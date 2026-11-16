import Coercions.Selective.Dot.Vanilla.Translate
import Coercions.Selective.Dot.Lift

/-!
# Selective DOT and DOT-MNF: elaboration of source derivations

A derivation of DOT-MNF is turned into a term of `SelDot` whose erasure is the
source term and which has the source type. The elaboration is a function on
derivations, by structural recursion.

* A subtyping derivation becomes a certificate. Transitivity becomes `seq`;
  the congruence rules become the lifts of `Lift.lean`; `Sel-<:` and `<:-Sel`
  become a step whose selection is taken on the path elaborated from the
  typing of the receiver.
* A typing derivation of a variable becomes a path rooted at the variable
  (`HasTy.toPath`). It extends a given path `p₀` by the casts of the
  subsumption steps. `Rec-I` and `Rec-E` add nothing. For `And-I` the second
  derivation extends the path of the first; `PathTy.keep` retains the view of
  the first.
* A typing derivation of any other term becomes a term whose receivers are such
  paths. The implicit comparison at an application argument is reflexivity;
  subsumption on a term that is not a path is a cast.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)
open SelDot.Lift (Ty.erase_embed')

mutual

/-- The certificate of a subtyping derivation. -/
def Sub.elab : {s : Sig} → {Γ : Ctx s} → {S T : Ty s} → Sub Γ S T → SelDot.Cert s
  | _, _, S, _, .top => SelDot.Cert.top (SelDot.Ty.ofDot S)
  | _, _, _, T, .bot => SelDot.Cert.bot (SelDot.Ty.ofDot T)
  | _, _, T, _, .refl => SelDot.Cert.refl (SelDot.Ty.ofDot T)
  | _, _, _, _, .trans d1 d2 => .seq d1.elab d2.elab
  | _, _, _, _, .and1 (S := S) (T := T) => SelDot.Cert.and1 (SelDot.Ty.ofDot S) (SelDot.Ty.ofDot T)
  | _, _, _, _, .and2 (S := S) (T := T) => SelDot.Cert.and2 (SelDot.Ty.ofDot S) (SelDot.Ty.ofDot T)
  | _, _, S, _, .and d1 d2 => SelDot.Cert.andI (SelDot.Ty.ofDot S) d1.elab d2.elab
  | _, _, _, _, .fld (a := a) d => d.elab.fld a
  | _, _, _, _, .typ (A := A) (S2 := S2) (T1 := T1) d1 d2 =>
      .seq (d1.elab.typLo A (SelDot.Ty.ofDot T1)) (d2.elab.typHi A (SelDot.Ty.ofDot S2))
  | _, _, _, T, .selUpper (x := x) (A := A) d =>
      .step (.sel (d.toPath (.var x)) A) (SelDot.Ty.ofDot T).embed
  | _, _, S, _, .selLower (x := x) (A := A) d =>
      .step (SelDot.Ty.ofDot S).embed (.sel (d.toPath (.var x)) A)
  | _, _, _, _, .all (S2 := S2) (T1 := T1) d1 d2 =>
      .seq (d1.elab.allDom (SelDot.Ty.ofDot T1)) (d2.elab.allBody (SelDot.Ty.ofDot S2))

/-- The path of a typing derivation of a variable, extending `p₀` by casts.
On a derivation of any other term it returns `p₀`. -/
def HasTy.toPath : {s : Sig} → {Γ : Ctx s} → {t : Tm s} → {T : Ty s} →
    HasTy Γ t T → SelDot.Path s → SelDot.Path s
  | _, _, _, _, .var, p₀ => p₀
  | _, _, _, _, .sub d e, p₀ => .cast (d.toPath p₀) e.elab
  | _, _, _, _, .recI d, p₀ => d.toPath p₀
  | _, _, _, _, .recE d, p₀ => d.toPath p₀
  | _, _, _, _, .andI d1 d2, p₀ => d2.toPath (d1.toPath p₀)
  | _, _, _, _, .lam _, p₀ => p₀
  | _, _, _, _, .app _ _, p₀ => p₀
  | _, _, _, _, .obj _ _, p₀ => p₀
  | _, _, _, _, .proj _, p₀ => p₀
  | _, _, _, _, .let _ _, p₀ => p₀

end

/-- The elaborated path keeps the root of the path it extends. -/
theorem HasTy.toPath_root : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (d : HasTy Γ t T) (p₀ : SelDot.Path s), (d.toPath p₀).root = p₀.root
  | _, _, _, _, .var, _ => rfl
  | _, _, _, _, .sub d _, p₀ => HasTy.toPath_root d p₀
  | _, _, _, _, .recI d, p₀ => HasTy.toPath_root d p₀
  | _, _, _, _, .recE d, p₀ => HasTy.toPath_root d p₀
  | _, _, _, _, .andI d1 d2, p₀ => (HasTy.toPath_root d2 _).trans (HasTy.toPath_root d1 p₀)
  | _, _, _, _, .lam _, _ => rfl
  | _, _, _, _, .app _ _, _ => rfl
  | _, _, _, _, .obj _ _, _ => rfl
  | _, _, _, _, .proj _, _ => rfl
  | _, _, _, _, .let _ _, _ => rfl

mutual

/-- The certificate of a subtyping derivation converts the source types. -/
theorem Sub.elab_typed : ∀ {s : Sig} {Γ : Ctx s} {S T : Ty s} (d : Sub Γ S T),
    SelDot.CertTy (SelDot.Ctx.ofDot Γ) d.elab (SelDot.Ty.ofDot S) (SelDot.Ty.ofDot T)
  | _, _, _, _, .top => SelDot.CertTy.top
  | _, _, _, _, .bot => SelDot.CertTy.bot
  | _, _, _, _, .refl => SelDot.CertTy.refl
  | _, _, _, _, .trans d1 d2 => .seq (Sub.elab_typed d1) (Sub.elab_typed d2)
  | _, _, _, _, .and1 => SelDot.CertTy.and1
  | _, _, _, _, .and2 => SelDot.CertTy.and2
  | _, _, _, _, .and d1 d2 => SelDot.CertTy.andI (Sub.elab_typed d1) (Sub.elab_typed d2)
  | _, _, _, _, .fld d => SelDot.CertTy.fld (Sub.elab_typed d)
  | _, _, _, _, .typ d1 d2 =>
      .seq (SelDot.CertTy.typLo (Sub.elab_typed d1)) (SelDot.CertTy.typHi (Sub.elab_typed d2))
  | _, _, _, T, .selUpper (x := x) (A := A) d => by
      have ih := HasTy.toPath_typed d x rfl (.var x) rfl (fun _ h => h)
      have hr := HasTy.toPath_root d (.var x)
      have c := SelDot.CertTy.step (SelDot.Prim.selU ih.1
        (SelDot.Wf.embed _ (SelDot.Ty.ofDot T)) (Ty.erase_embed' _).symm)
      simp only [SelDot.ATy.erase, Ty.erase_embed'] at c
      rw [hr] at c
      exact c
  | _, _, S, _, .selLower (x := x) (A := A) d => by
      have ih := HasTy.toPath_typed d x rfl (.var x) rfl (fun _ h => h)
      have hr := HasTy.toPath_root d (.var x)
      have c := SelDot.CertTy.step (SelDot.Prim.selL ih.1
        (SelDot.Wf.embed _ (SelDot.Ty.ofDot S)) (Ty.erase_embed' _).symm)
      simp only [SelDot.ATy.erase, Ty.erase_embed'] at c
      rw [hr] at c
      exact c
  | _, _, _, _, .all d1 d2 =>
      .seq (SelDot.CertTy.allDom (Sub.elab_typed d1)) (SelDot.CertTy.allBody (Sub.elab_typed d2))

/-- The path of a typing derivation of a variable `x`: given a path `p₀` rooted
at `x` that has every type of `x`, the extended path has the source type, and
it keeps every type of `p₀`. -/
theorem HasTy.toPath_typed : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (d : HasTy Γ t T) (x : BVar s .var), t = .path (.var x) →
    ∀ (p₀ : SelDot.Path s), p₀.root = x →
    (∀ U, SelDot.PathTy (SelDot.Ctx.ofDot Γ) (.var x) U →
      SelDot.PathTy (SelDot.Ctx.ofDot Γ) p₀ U) →
    SelDot.PathTy (SelDot.Ctx.ofDot Γ) (d.toPath p₀) (SelDot.Ty.ofDot T) ∧
      ∀ U, SelDot.PathTy (SelDot.Ctx.ofDot Γ) p₀ U →
        SelDot.PathTy (SelDot.Ctx.ofDot Γ) (d.toPath p₀) U
  | _, Γ, _, _, .var (x := x'), x, e, p₀, _, hp₀ => by
      cases e
      refine ⟨?_, fun _ h => h⟩
      have h := hp₀ _ (SelDot.PathTy.var (x := x'))
      rw [SelDot.Ctx.ofDot_lookup] at h
      exact h
  | _, _, _, _, .sub d e, x, ht, p₀, hr, hp₀ =>
      have ih := HasTy.toPath_typed d x ht p₀ hr hp₀
      have hc := Sub.elab_typed e
      ⟨.cast ih.1 hc, fun U h => .keep ih.1 hc (ih.2 U h)⟩
  | _, Γ, _, _, .recI (x := x') (T := T) d, x, ht, p₀, hr, hp₀ => by
      have ih := HasTy.toPath_typed d x ht p₀ hr hp₀
      have hroot := (HasTy.toPath_root d p₀).trans hr
      cases ht
      have h : SelDot.PathTy (SelDot.Ctx.ofDot Γ) (d.toPath p₀)
          ((SelDot.Ty.ofDot T).substVar (d.toPath p₀).root) := by
        rw [hroot, ← SelDot.Ty.ofDot_substVar]
        exact ih.1
      exact ⟨SelDot.PathTy.recI h, ih.2⟩
  | _, _, _, _, .recE (x := x') d, x, ht, p₀, hr, hp₀ => by
      have ih := HasTy.toPath_typed d x ht p₀ hr hp₀
      have hroot := (HasTy.toPath_root d p₀).trans hr
      cases ht
      have h := SelDot.PathTy.recE ih.1
      rw [hroot, ← SelDot.Ty.ofDot_substVar] at h
      exact ⟨h, ih.2⟩
  | _, _, _, _, .andI d1 d2, x, ht, p₀, hr, hp₀ =>
      have ih1 := HasTy.toPath_typed d1 x ht p₀ hr hp₀
      have ih2 := HasTy.toPath_typed d2 x ht (d1.toPath p₀)
        ((HasTy.toPath_root d1 p₀).trans hr) (fun U h => ih1.2 U (hp₀ U h))
      ⟨.andI (ih2.2 _ ih1.1) ih2.1, fun U h => ih2.2 U (ih1.2 U h)⟩
  | _, _, _, _, .lam _, _, ht, _, _, _ => by cases ht
  | _, _, _, _, .app _ _, _, ht, _, _, _ => by cases ht
  | _, _, _, _, .obj _ _, _, ht, _, _, _ => by cases ht
  | _, _, _, _, .proj _, _, ht, _, _, _ => by cases ht
  | _, _, _, _, .let _ _, _, ht, _, _, _ => by cases ht

end

/-- The path of a typing derivation of a variable, from the variable itself. -/
theorem HasTy.toPath_var {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (d : HasTy Γ (.path (.var x)) T) :
    SelDot.PathTy (SelDot.Ctx.ofDot Γ) (d.toPath (.var x)) (SelDot.Ty.ofDot T) ∧
      (d.toPath (.var x)).root = x :=
  ⟨(HasTy.toPath_typed d x rfl (.var x) rfl (fun _ h => h)).1, HasTy.toPath_root d _⟩

/-! ## Terms -/

/-- The elaboration of subsumption: on a variable, the elaborated path;
otherwise a cast. -/
def subElab (t : Tm s) (onPath : BVar s .var → SelDot.Tm s) (other : SelDot.Tm s) :
    SelDot.Tm s :=
  match t with
  | .path (.var x) => onPath x
  | _ => other

theorem subElab_cases (t : Tm s) (onPath : BVar s .var → SelDot.Tm s) (other : SelDot.Tm s) :
    (∃ x, t = .path (.var x) ∧ subElab t onPath other = onPath x) ∨
      subElab t onPath other = other := by
  match t with
  | .path (.var x) => exact .inl ⟨x, rfl, rfl⟩
  | .val _ | .app _ _ | .proj _ _ | .let _ _ => exact .inr rfl

mutual

/-- The elaboration of a typing derivation. -/
def HasTy.elab : {s : Sig} → {Γ : Ctx s} → {t : Tm s} → {T : Ty s} →
    HasTy Γ t T → SelDot.Tm s
  | _, _, _, _, .var (x := x) => .path (.var x)
  | _, _, _, _, .lam (S := S) d => .val (.lam (SelDot.Ty.ofDot S) d.elab)
  | _, _, _, _, .app (x := x) (y := y) d1 d2 => .app (d1.toPath (.var x)) (d2.toPath (.var y))
  | _, _, _, _, .obj D _ => .val (.obj D.elab)
  | _, _, _, _, .proj (x := x) (a := a) d => .proj (d.toPath (.var x)) a
  | _, _, _, _, .let d1 d2 => .let d1.elab d2.elab
  | _, _, _, _, .recI (x := x) d => .path ((HasTy.recI d).toPath (.var x))
  | _, _, _, _, .recE (x := x) d => .path ((HasTy.recE d).toPath (.var x))
  | _, _, _, _, .andI (x := x) d1 d2 => .path ((HasTy.andI d1 d2).toPath (.var x))
  | _, _, t, _, .sub d e =>
      subElab t (fun x => .path ((HasTy.sub d e).toPath (.var x))) (.cast d.elab e.elab)

/-- The elaboration of a definition typing derivation. -/
def DefsTy.elab : {s : Sig} → {Γ : Ctx s} → {d : Defs s} → {T : Ty s} →
    DefsTy Γ d T → SelDot.Defs s
  | _, _, _, _, .typ (A := A) (T := T) => .typ A (SelDot.Ty.ofDot T)
  | _, _, _, _, .trm (a := a) d => .trm a d.elab
  | _, _, _, _, .and D1 D2 => .and D1.elab D2.elab

end

mutual

/-- The elaboration erases to the source term. -/
theorem HasTy.elab_erase : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy Γ t T),
    d.elab.erase = SelDot.Tm.ofDot t
  | _, _, _, _, .var => rfl
  | _, _, _, _, .lam d => by
      have ih := HasTy.elab_erase d
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Value.erase, SelDot.Tm.ofDot,
        SelDot.Value.ofDot, ih]
  | _, _, _, _, .app (x := x) (y := y) d1 d2 => by
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root,
        SelDot.Path.root]
  | _, _, _, _, .obj D _ => by
      have ih := DefsTy.elab_erase D
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Value.erase, SelDot.Tm.ofDot,
        SelDot.Value.ofDot, ih]
  | _, _, _, _, .proj d => by
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root,
        SelDot.Path.root]
  | _, _, _, _, .let d1 d2 => by
      have ih1 := HasTy.elab_erase d1
      have ih2 := HasTy.elab_erase d2
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, ih1, ih2]
  | _, _, _, _, .recI d => by
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root,
        SelDot.Path.root]
  | _, _, _, _, .recE d => by
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root,
        SelDot.Path.root]
  | _, _, _, _, .andI d1 d2 => by
      simp only [HasTy.elab, SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root,
        SelDot.Path.root]
  | _, _, t, _, .sub d e => by
      have ih := HasTy.elab_erase d
      simp only [HasTy.elab]
      rcases subElab_cases t (fun x => .path ((HasTy.sub d e).toPath (.var x)))
        (.cast d.elab e.elab) with ⟨x, rfl, h⟩ | h
      · rw [h]
        simp only [SelDot.Tm.erase, SelDot.Tm.ofDot, HasTy.toPath_root, SelDot.Path.root]
      · rw [h]
        simp only [SelDot.Tm.erase, ih]

/-- The elaboration of definitions erases to the source definitions. -/
theorem DefsTy.elab_erase : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s} (D : DefsTy Γ d T),
    D.elab.erase = SelDot.Defs.ofDot d
  | _, _, _, _, .typ => rfl
  | _, _, _, _, .trm d => by
      have ih := HasTy.elab_erase d
      simp only [DefsTy.elab, SelDot.Defs.erase, SelDot.Defs.ofDot, ih]
  | _, _, _, _, .and D1 D2 => by
      have ih1 := DefsTy.elab_erase D1
      have ih2 := DefsTy.elab_erase D2
      simp only [DefsTy.elab, SelDot.Defs.erase, SelDot.Defs.ofDot, ih1, ih2]

end

mutual

/-- The elaboration has the source type. -/
theorem HasTy.elab_typed : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy Γ t T),
    SelDot.HasTy (SelDot.Ctx.ofDot Γ) d.elab (SelDot.Ty.ofDot T)
  | _, Γ, _, _, .var (x := x) => by
      have h := SelDot.PathTy.var (Γ := SelDot.Ctx.ofDot Γ) (x := x)
      rw [SelDot.Ctx.ofDot_lookup] at h
      exact .path h
  | _, _, _, _, .lam d => .lam (HasTy.elab_typed d)
  | _, Γ, _, _, .app (x := x) (y := y) (S := S) d1 d2 => by
      have h1 := (HasTy.toPath_var d1).1
      have h2 := HasTy.toPath_var d2
      have h := SelDot.HasTy.app h1 h2.1
        (.refl (SelDot.Wf.embed _ _) (SelDot.Wf.embed _ _) rfl)
      rw [h2.2, ← SelDot.Ty.ofDot_substVar] at h
      exact h
  | _, _, _, _, .obj D hd => by
      have ih := DefsTy.elab_typed D
      have hdist : D.elab.Distinct := by
        apply SelDot.Vanilla.distinct_of_erase
        rw [DefsTy.elab_erase]
        exact SelDot.Defs.Distinct.ofDot hd
      exact .obj ih hdist
  | _, _, _, _, .proj d => .proj (HasTy.toPath_var d).1
  | _, _, _, _, .let d1 d2 => by
      have ih1 := HasTy.elab_typed d1
      have ih2 := HasTy.elab_typed d2
      rw [SelDot.Ty.ofDot_weaken] at ih2
      exact .let ih1 ih2
  | _, _, _, _, .recI d => .path (HasTy.toPath_var (HasTy.recI d)).1
  | _, _, _, _, .recE d => .path (HasTy.toPath_var (HasTy.recE d)).1
  | _, _, _, _, .andI d1 d2 => .path (HasTy.toPath_var (HasTy.andI d1 d2)).1
  | _, _, t, _, .sub d e => by
      have ih := HasTy.elab_typed d
      have hc := Sub.elab_typed e
      simp only [HasTy.elab]
      rcases subElab_cases t (fun x => .path ((HasTy.sub d e).toPath (.var x)))
        (.cast d.elab e.elab) with ⟨x, rfl, h⟩ | h
      · rw [h]
        exact .path (HasTy.toPath_var (HasTy.sub d e)).1
      · rw [h]
        exact .cast ih hc

/-- The elaboration of definitions has the source type. -/
theorem DefsTy.elab_typed : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s} (D : DefsTy Γ d T),
    SelDot.DefsTy (SelDot.Ctx.ofDot Γ) D.elab (SelDot.Ty.ofDot T)
  | _, _, _, _, .typ => .typ
  | _, _, _, _, .trm d => .trm (HasTy.elab_typed d)
  | _, _, _, _, .and D1 D2 => .and (DefsTy.elab_typed D1) (DefsTy.elab_typed D2)

end

end DotMNF
