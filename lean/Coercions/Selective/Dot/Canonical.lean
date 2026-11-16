import Coercions.Selective.Dot.Tight
import Coercions.Selective.Dot.Subst
import Coercions.Selective.Dot.Lift
import Coercions.Selective.Dot.State

/-!
# Selective DOT: canonical forms

From the tight analysis of `Tight.lean` back to certificates, and the canonical
forms of stored values.

* A precise type of a variable is the type of a path with that root: the
  and-projections of a precise derivation are casts.
* Tight subtyping is general subtyping: every rule of `TSub` is a certificate.
* A chain of function-subtyping layers collapses to one comparison of the
  domains and one of the bodies.
* A typed store declares an inert context, and every stored value is the
  erasure of an annotated value of the declared type.
* Canonical forms: a path of function type is rooted at a stored closure, and a
  path of field type at a stored object with that field.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Precise typing gives a path -/

/-- A precise type of `x` is the type of a path rooted at `x`. -/
theorem Precise.path {Γ : Ctx s} {x : BVar s .var} {T : Ty s} (h : Precise Γ x T) :
    ∃ p : Path s, p.root = x ∧ PathTy Γ p T := by
  induction h with
  | var => exact ⟨.var x, rfl, .var⟩
  | recE _ ih =>
      obtain ⟨p, hr, hp⟩ := ih
      have h' := PathTy.recE hp
      rw [hr] at h'
      exact ⟨p, hr, h'⟩
  | and1 _ ih =>
      obtain ⟨p, hr, hp⟩ := ih
      have hc := PathTy.cast hp CertTy.and1
      refine ⟨_, ?_, hc⟩
      exact hr
  | and2 _ ih =>
      obtain ⟨p, hr, hp⟩ := ih
      have hc := PathTy.cast hp CertTy.and2
      refine ⟨_, ?_, hc⟩
      exact hr

/-! ## Tight subtyping is general subtyping -/

/-- Every tight subtyping has a certificate. -/
theorem TSub.cert {Γ : Ctx s} {S T : Ty s} (h : TSub Γ S T) : GSub Γ S T := by
  induction h with
  | top => exact ⟨_, CertTy.top⟩
  | bot => exact ⟨_, CertTy.bot⟩
  | refl => exact ⟨_, CertTy.refl⟩
  | trans _ _ ih1 ih2 =>
      obtain ⟨c1, h1⟩ := ih1
      obtain ⟨c2, h2⟩ := ih2
      exact ⟨_, .seq h1 h2⟩
  | and1 => exact ⟨_, CertTy.and1⟩
  | and2 => exact ⟨_, CertTy.and2⟩
  | and _ _ ih1 ih2 =>
      obtain ⟨c1, h1⟩ := ih1
      obtain ⟨c2, h2⟩ := ih2
      exact ⟨_, CertTy.andI h1 h2⟩
  | fld _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨_, CertTy.fld hc⟩
  | typ _ _ ih1 ih2 =>
      obtain ⟨c1, h1⟩ := ih1
      obtain ⟨c2, h2⟩ := ih2
      exact ⟨_, .seq (CertTy.typLo h1) (CertTy.typHi h2)⟩
  | all _ hb ih =>
      obtain ⟨c1, h1⟩ := ih
      obtain ⟨c2, h2⟩ := hb
      exact ⟨_, .seq (CertTy.allDom h1) (CertTy.allBody h2)⟩
  | @selU A T x hx =>
      obtain ⟨p, hr, hp⟩ := hx.path
      subst hr
      have h' := CertTy.step (Prim.selU (A := A) hp (Wf.embed Γ T) (Ty.erase_embed T).symm)
      rw [Ty.erase_embed] at h'
      exact ⟨_, h'⟩
  | @selL A T x hx =>
      obtain ⟨p, hr, hp⟩ := hx.path
      subst hr
      have h' := CertTy.step (Prim.selL (A := A) hp (Wf.embed Γ T) (Ty.erase_embed T).symm)
      rw [Ty.erase_embed] at h'
      exact ⟨_, h'⟩

/-! ## Function-subtyping chains -/

/-- A chain of function-subtyping layers is one comparison of the domains and
one of the bodies, the latter under the smaller domain. -/
theorem AllSub.collapse {Γ : Ctx s} {S0 S : Ty s} {T0 T : Ty (s,x)}
    (h : AllSub Γ S0 T0 S T) : GSub Γ S S0 ∧ GSub (Γ.cons S) T0 T := by
  induction h with
  | refl => exact ⟨⟨_, CertTy.refl⟩, ⟨_, CertTy.refl⟩⟩
  | step _ hS hT ih =>
      obtain ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := ih
      obtain ⟨c3, hc3⟩ := hS.cert
      obtain ⟨c4, hc4⟩ := hT
      obtain ⟨c2', hc2'⟩ := CertTy.narrow hc3 hc2
      exact ⟨⟨_, .seq hc3 hc1⟩, ⟨_, .seq hc2' hc4⟩⟩

/-! ## Definitions -/

/-- The labels of a typed definition list are the labels of its type. -/
theorem DefsTy.labels : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → T.labels = d.labels
  | _, _, _, _, .typ => rfl
  | _, _, _, _, .trm _ => rfl
  | _, _, _, _, .and h1 h2 => by
      simp only [Ty.labels, Defs.labels, DefsTy.labels h1, DefsTy.labels h2]

/-- Definitions with distinct labels have a record type. -/
theorem DefsTy.record : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → d.Distinct → T.Record
  | _, _, _, _, .typ, _ => .typ
  | _, _, _, _, .trm _, _ => .fld
  | _, _, _, _, .and h1 h2, hd => by
      have r1 := DefsTy.record h1
      have r2 := DefsTy.record h2
      cases hd with
      | and hd1 hd2 hdis =>
          refine .and (r1 hd1) (r2 hd2) ?_
          intro ℓ hl
          rw [DefsTy.labels h1] at hl
          rw [DefsTy.labels h2]
          exact hdis ℓ hl

/-- A label that is not defined has no term member. -/
theorem Defs.lookupTrm_none : ∀ {s : Sig} (d : Defs s) {a : Label},
    a ∉ d.labels → d.lookupTrm a = none
  | _, .typ _ _, _, _ => rfl
  | _, .trm b t, a, h => by
      simp only [Defs.labels, List.mem_singleton] at h
      simp [Defs.lookupTrm, h]
  | _, .and d1 d2, a, h => by
      simp only [Defs.labels, List.mem_append, not_or] at h
      simp only [Defs.lookupTrm, Defs.lookupTrm_none d1 h.1, Defs.lookupTrm_none d2 h.2]
      rfl

/-- A field declaration among the conjuncts of the type of distinct definitions
is defined by a term of the declared type. -/
theorem DefsTy.lookup_fld : ∀ {s : Sig} {Δ : Ctx s} {d : Defs s} {R : Ty s},
    DefsTy Δ d R → d.Distinct → ∀ {a : Label} {Tb : Ty s}, Ty.Conj (.fld a Tb) R →
      ∃ t', d.lookupTrm a = some t' ∧ HasTy Δ t' Tb
  | _, _, _, _, .typ, _, _, _, hc => by cases hc
  | _, _, _, _, .trm ht, _, _, _, hc => by
      cases hc
      exact ⟨_, by simp [Defs.lookupTrm], ht⟩
  | _, _, _, _, .and h1 h2, hd, a, Tb, hc => by
      have ih1 := DefsTy.lookup_fld h1
      have ih2 := DefsTy.lookup_fld h2
      cases hd with
      | and hd1 hd2 hdis =>
          cases hc with
          | left hc1 =>
              obtain ⟨t', e, ht⟩ := ih1 hd1 hc1
              have hl : a ∈ _ := hc1.labels (ℓ := a) (by simp [Ty.labels])
              rw [DefsTy.labels h1] at hl
              have hn := Defs.lookupTrm_none _ (hdis a hl)
              exact ⟨t', by simp only [Defs.lookupTrm, hn, e]; rfl, ht⟩
          | right hc2 =>
              obtain ⟨t', e, ht⟩ := ih2 hd2 hc2
              exact ⟨t', by simp only [Defs.lookupTrm, e]; rfl, ht⟩

/-- A field conjunct of a renamed type is the renaming of a field conjunct. -/
theorem Ty.Conj.fld_rename {a : Label} {T0 : Ty s2} :
    ∀ {R : Ty s1} {ρ : Rename s1 s2}, Ty.Conj (.fld a T0) (R.rename ρ) →
      ∃ Tb, Ty.Conj (.fld a Tb) R ∧ T0 = Tb.rename ρ
  | .top, _, h => by simp only [Ty.rename] at h; cases h
  | .bot, _, h => by simp only [Ty.rename] at h; cases h
  | .typ _ _ _, _, h => by simp only [Ty.rename] at h; cases h
  | .fld b Tb, ρ, h => by
      simp only [Ty.rename] at h
      cases h
      exact ⟨Tb, .refl, rfl⟩
  | .sel _ _, _, h => by simp only [Ty.rename] at h; cases h
  | .mu _, _, h => by simp only [Ty.rename] at h; cases h
  | .all _ _, _, h => by simp only [Ty.rename] at h; cases h
  | .and R1 R2, ρ, h => by
      simp only [Ty.rename] at h
      cases h with
      | left h1 =>
          obtain ⟨Tb, hc, e⟩ := Ty.Conj.fld_rename h1
          exact ⟨Tb, .left hc, e⟩
      | right h2 =>
          obtain ⟨Tb, hc, e⟩ := Ty.Conj.fld_rename h2
          exact ⟨Tb, .right hc, e⟩

/-! ## Stores -/

/-- Every stored value is the erasure of an annotated value of the declared
type of its variable. -/
theorem StoreTy.lookup {Γ : Ctx s} {σ : Store s} (h : StoreTy Γ σ) :
    ∀ x, ∃ v' : Value s, v'.erase = σ.lookup x ∧ HasTy Γ (.val v') (Γ.lookup x) := by
  induction h with
  | nil => intro x; cases x
  | cons _ hv ih =>
      intro x
      obtain ⟨v0, e0, h0⟩ := hv
      cases x with
      | here =>
          refine ⟨v0.weaken, ?_, h0.weaken _⟩
          subst e0
          exact Value.erase_rename _ _
      | there y =>
          obtain ⟨v1, e1, h1⟩ := ih y
          refine ⟨v1.weaken, ?_, h1.weaken _⟩
          show (v1.rename Rename.succ).erase = (_ : Value _).rename Rename.succ
          rw [Value.erase_rename, e1]

/-- The type of a value is inert. -/
theorem ValTy.inert {Γ : Ctx s} {v : Value s} {T : Ty s} (h : ValTy Γ v T) : T.Inert := by
  obtain ⟨v', _, hv⟩ := h
  cases v' with
  | lam S b => cases hv; exact .all
  | obj d => cases hv with | obj hd hdis => exact .obj (DefsTy.record hd hdis)

/-- A typed store declares an inert context. -/
theorem StoreTy.inert {Γ : Ctx s} {σ : Store s} (h : StoreTy Γ σ) : Γ.Inert := by
  induction h with
  | nil => exact .nil
  | cons _ hv ih => exact .cons ih hv.inert

/-! ## Canonical forms -/

/-- A path of function type is rooted at a stored closure whose annotated body
has a type below the body of the function type. -/
theorem canonical_fun {Γ : Ctx s} {σ : Store s} {p : Path s} {S : Ty s} {T : Ty (s,x)}
    (hσ : StoreTy Γ σ) (hp : PathTy Γ p (.all S T)) :
    ∃ (S0 : Ty s) (b : Tm (s,x)) (T0 : Ty (s,x)),
      σ.lookup p.root = .lam S0 b.erase ∧ HasTy (Γ.cons S0) b T0 ∧
      GSub Γ S S0 ∧ GSub (Γ.cons S) T0 T := by
  have hΓ := hσ.inert
  obtain ⟨S0, T0, hl, hsub⟩ := hp.fun_inv hΓ
  obtain ⟨v', ev, hv⟩ := hσ.lookup p.root
  rw [hl] at hv
  cases v' with
  | obj d => cases hv
  | lam S1 b =>
      cases hv with
      | lam hb =>
          obtain ⟨h1, h2⟩ := hsub.collapse
          exact ⟨S0, b, T0, ev.symm, hb, h1, h2⟩

/-- A path of field type is rooted at a stored object that defines the field;
the field's annotated body, instantiated at the root, has a type below the
field type. -/
theorem canonical_obj {Γ : Ctx s} {σ : Store s} {p : Path s} {a : Label} {T : Ty s}
    (hσ : StoreTy Γ σ) (hp : PathTy Γ p (.fld a T)) :
    ∃ (d : Defs (s,x)) (t : Tm (s,x)) (b : Tm s) (T0 : Ty s),
      σ.lookup p.root = .obj d ∧ d.lookupTrm a = some t ∧
      b.erase = t.substVar p.root ∧ HasTy Γ b T0 ∧ GSub Γ T0 T := by
  have hΓ := hσ.inert
  obtain ⟨T0, hpre, hsub⟩ := hp.fld_inv hΓ
  obtain ⟨R, hR, hc, _⟩ := hpre.record_part hΓ (fun h => by cases h)
  obtain ⟨Tb, hcb, rfl⟩ := Ty.Conj.fld_rename (ρ := Rename.subst p.root) hc
  obtain ⟨v', ev, hv⟩ := hσ.lookup p.root
  rw [hR] at hv
  cases v' with
  | lam S b => cases hv
  | obj d' =>
      cases hv with
      | obj hd hdis =>
          obtain ⟨t', hl, ht'⟩ := DefsTy.lookup_fld hd hdis hcb
          refine ⟨d'.erase, t'.erase, t'.substVar p.root, Tb.substVar p.root,
            ev.symm, ?_, ?_, HasTy.substVar_self hR ht', hsub.cert⟩
          · rw [Defs.lookupTrm_erase, hl]; rfl
          · exact Tm.erase_rename _ _

end SelDot
