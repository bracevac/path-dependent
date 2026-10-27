import Coercions.PDot.FCp.Machine
import Coercions.PDot.FCp.Model
import Coercions.PDot.FCp.Transparency
import Coercions.PDot.FCp.CheckerCompleteness

/-!
# FCp examples: the negative examples N1 to N3

The three negative examples of the plan's table (`plan-10-pdot.md:992-994`) at FCp.

- N2, `fact2_untyped`: a path field declared at a bounds type.  `DF-Path` declares a path field at
  its singleton only, so the inversion of `VA-Obj` and `DF-Path` meets a bounds type where it asks a
  singleton.
- N1, `badBounds_untyped`: pDOT's bad bounds.  `DF-Fun` declares a function field at a `Π` only, so
  the lambda field `b`, declared at an object type, has no derivation whatever `a` holds.
- N3, `dangling_untyped`: a field whose singleton names a path that no lookup reaches.  The
  inversion of `VA-Obj` and `DF-Path` leaves a typing of `P` with `P.path = x.zz` in the context
  `VA-Obj` builds, and `dangling_path_untyped` refutes it with a path model of that context
  (decision D11 of the groups file).

The model of the dangling context is in `namespace PDot.FCp.Dangling`.  `x` is the oldest variable
of every signature that extends `([],x)`.  Path equality relates `x.h.bs` to `x.zz.bs` and nothing
else, through a normal form that reads the first `h` after the oldest variable as `zz`.  Type
equality is equality of normal forms.  A type is read by closing its selves at paths.  The model
reaches `x` and `x.h` only, so no path evidence of the context has the path `x.zz`.

Two examples of the metatheory of typing follow (group g3).

- `namespace PDot.FCp.Binder`: the binder example of the d3 prototype over full FCp.  A literal
  `core` with a nested literal `core.types` and an alias field `core.m = core.types` is typed by all
  four `DF` rules and `VA-Obj`.  Under `y : core.types.type` the alias `y ≃ core.types` gives `y.f`
  and `y∙A ≡ core.types∙A`.  Closing `y := core.m` is the `substCo` lemmas, never a new derivation.
- `namespace PDot.FCp.Adjust`: the risk of the stage, `MS-LetVal`'s `adjust` with path evidence
  inside evidence.  A let body whose `PA-Alias` has `P₀ = var z` stays typed after the allocation
  of a cast literal, by `Tm.HasType.subst` at `CoSubst.Typed.selfCast`.

The checker of T.8 decides three programs by `decide +kernel` (group g5).

- `binderProg` binds `core` opaque by `TM-Let` and applies `λ(y : core.types.type). y.f (cast y to ⊤)`
  to `core.m`.  `Binder.Pyf` types from the type of `core` alone, so the program checks with no
  definition read.  `binderProg_typed` is its typing, read off by `checkTm_iff`.
- `fact2Prog` is the twin of `fact2_untyped`, the literal with the field body `x.a`.  The checker
  returns nothing, and `fact2Prog_untyped` is `checkTm_iff` with that verdict.
- `danglingProg` is the literal of N3 with the field body `x.zz`.  The checker returns nothing.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

abbrev la : Label := .trm 0
abbrev lb : Label := .trm 1
abbrev lh : Label := .trm 2
abbrev lzz : Label := .trm 3
abbrev lc : Label := .trm 4
abbrev tA : Label := .typ 0
abbrev tC : Label := .typ 1

/-- `{A : S..U}` at a self `w'`: `μ(w' : [S↑ ⊑ w'∙A, w'∙A ⊑ U↑])`. -/
def bnds (A : Label) (S U : Ty s) : Ty s := .mu (.cons (.cons .nil (.le S.weaken (.sel (.var .here) A))) (.le (.sel (.var .here) A) U.weaken))

/-- N2, `ν(x : {a : {A : ⊤..⊥}}) {a = P}` for any path evidence `P`. -/
def fact2Tel : Telescope ([],x) := .cons .nil (.fld la (bnds tA .top .bot))
def fact2Defs (P : PathCo ([],x)) : Defs ([],x) := .fld .nil la (.path P)
/-- N1, `ν(x : {a : {C : ∀(y : ⊤) ⊤ .. {c : ⊤}}} ∧ {b : {c : ⊤}}) {a = P} ∧ {b = fun v}`. -/
def badBoundsTel : Telescope ([],x) := .cons (.cons .nil (.fld la (bnds tC (.pi .top .top) (.mu (.cons .nil (.fld lc .top)))))) (.fld lb (.mu (.cons .nil (.fld lc .top))))
def badBoundsDefs (P : PathCo ([],x)) (v : Value ([],x)) : Defs ([],x) := .fld (.fld .nil la (.path P)) lb (.fn v)
/-- N3, `ν(x : {h : (x.zz).type}) {h = P}`. -/
def danglingTel : Telescope ([],x) := .cons .nil (.fld lh (Ty.sngl (.sel (.var .here) lzz)))
def danglingDefs (P : PathCo ([],x)) : Defs ([],x) := .fld .nil lh (.path P)
/-- The context `VA-Obj` builds for N3 once `DF-Path` has fixed `P.path = x.zz`. -/
def danglingCtx : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu danglingTel) (.node .nil (.cons .nil lh (.fwd (.sel (.var .here) lzz)))))

namespace Dangling

/-! ## The normal form of paths and types -/

def BVar.isOldest : {s : Sig} → BVar s k → Bool
  | _, @BVar.here [] _ => true
  | _, @BVar.here (_ :: _) _ => false
  | _, .there y => BVar.isOldest y
def Path.nfo : Path s → Path s
  | .var y => .var y
  | .sel (.var y) a => if BVar.isOldest y && a == lh then .sel (.var y) lzz else .sel (.var y) a
  | .sel p a => .sel (Path.nfo p) a
mutual
def Ty.nfo : Ty s → Ty s                                    -- Path.nfo at every path
  | .bot => .bot
  | .sel p A => .sel (Path.nfo p) A
  | .pi S T => .pi (Ty.nfo S) (Ty.nfo T)
  | .mu Tel => .mu (Telescope.nfo Tel)
def Pr.nfo : Pr s → Pr s
  | .le S T => .le (Ty.nfo S) (Ty.nfo T)
  | .fld a T => .fld a (Ty.nfo T)
  | .alias q => .alias (Path.nfo q)
  | .is T => .is (Ty.nfo T)
def Telescope.nfo : Telescope s → Telescope s
  | .nil => .nil
  | .cons Tel pr => .cons (Telescope.nfo Tel) (Pr.nfo pr)
end
def KeepsOldest (σ : PathSubst s₁ s₂) : Prop := ∀ y, BVar.isOldest y = true → ∃ y', σ.var y = .var y' ∧ BVar.isOldest y' = true
def danglingReach (p : Path ([],x)) : Prop := p = .var .here ∨ p = .sel (.var .here) lh

/-! ## The reading of types, with a closing substitution for the selves -/

mutual
def dsem : {s' : Sig} → PathSubst s' ([],x) → Ty s' → Path ([],x) → Prop
  | _, _, .bot, _ => False
  | _, _, .sel _ _, _ => False
  | _, _, .pi _ _, _ => False
  | _, τ, .mu Tel, p => danglingReach p ∧ dsemTel (τ.extend p) Tel p
def dsemTel : {s' : Sig} → PathSubst s' ([],x) → Telescope s' → Path ([],x) → Prop
  | _, _, .nil, _ => True
  | _, τ, .cons Tel pr, p => dsemTel τ Tel p ∧ dsemPr τ pr p
def dsemPr : {s' : Sig} → PathSubst s' ([],x) → Pr s' → Path ([],x) → Prop
  | _, τ, .le S T, _ => ∀ r, dsem τ S r → dsem τ T r
  | _, τ, .fld a T, p => dsem τ T (p.sel a)
  | _, τ, .alias q, p => Path.nfo p = Path.nfo (q.subst τ)
  | _, τ, .is T, p => dsem τ T p
end

/-! ## Laws of the normal form of paths -/

theorem BVar.isOldest_there (y : BVar s k) : BVar.isOldest (BVar.there (k0 := k0) y) = BVar.isOldest y := rfl

theorem Path.nfo_sel_var (y : BVar s .var) (a : Label) :
    Path.nfo (.sel (.var y) a) = if BVar.isOldest y && a == lh then .sel (.var y) lzz else .sel (.var y) a := rfl

theorem Path.nfo_sel_sel (p : Path s) (b a : Label) :
    Path.nfo (.sel (.sel p b) a) = .sel (Path.nfo (.sel p b)) a := rfl

/-- The normal form of a selection is a selection. -/
theorem Path.nfo_sel_ne_var (p : Path s) (a : Label) (y : BVar s .var) : Path.nfo (.sel p a) ≠ .var y := by
  cases p with
  | var y' =>
      rw [Path.nfo_sel_var]
      cases BVar.isOldest y' && a == lh <;> exact fun h => nomatch h
  | sel p b =>
      rw [Path.nfo_sel_sel]
      exact fun h => nomatch h

theorem Path.nfo_sel_congr {p q : Path s} (a : Label) : Path.nfo p = Path.nfo q → Path.nfo (p.sel a) = Path.nfo (q.sel a) := by
  intro h
  cases p with
  | var y =>
      cases q with
      | var y' =>
          cases h
          rfl
      | sel q c => exact absurd h.symm (Path.nfo_sel_ne_var q c y)
  | sel p b =>
      cases q with
      | var y' => exact absurd h (Path.nfo_sel_ne_var p b y')
      | sel q c =>
          rw [Path.nfo_sel_sel, Path.nfo_sel_sel, h]

theorem Path.nfo_rename_succ (p : Path s) : Path.nfo (p.rename (Rename.succ (k := .var))) = (Path.nfo p).rename (Rename.succ (k := .var)) := by
  induction p with
  | var y => rfl
  | sel p a ih =>
      cases p with
      | var y =>
          show Path.nfo (.sel (.var (.there y)) a) = (Path.nfo (.sel (.var y) a)).rename Rename.succ
          rw [Path.nfo_sel_var, Path.nfo_sel_var, BVar.isOldest_there]
          cases BVar.isOldest y && a == lh <;> rfl
      | sel p b =>
          show Path.nfo (.sel (.sel (p.rename Rename.succ) b) a) = (Path.nfo (.sel (.sel p b) a)).rename Rename.succ
          rw [Path.nfo_sel_sel, Path.nfo_sel_sel]
          show Path.sel (Path.nfo ((Path.sel p b).rename Rename.succ)) a = _
          rw [ih]
          rfl

theorem Path.nfo_subst_congr (p : Path s₁) {σ σ' : PathSubst s₁ s₂} (h : ∀ y, Path.nfo (σ.var y) = Path.nfo (σ'.var y)) : Path.nfo (p.subst σ) = Path.nfo (p.subst σ') := by
  induction p with
  | var y => exact h y
  | sel p a ih => exact Path.nfo_sel_congr a ih

theorem Path.nfo_subst_nfo (p : Path s₁) {σ : PathSubst s₁ s₂} (h : KeepsOldest σ) : Path.nfo ((Path.nfo p).subst σ) = Path.nfo (p.subst σ) := by
  induction p with
  | var y => rfl
  | sel p a ih =>
      cases p with
      | var y =>
          rw [Path.nfo_sel_var]
          cases hc : (BVar.isOldest y && a == lh)
          · rfl
          · obtain ⟨hy, ha⟩ := Bool.and_eq_true_iff.1 hc
            obtain ⟨y', e, hy'⟩ := h y hy
            have ha' : a = lh := eq_of_beq ha
            subst ha'
            show Path.nfo (.sel (σ.var y) lzz) = Path.nfo (.sel (σ.var y) lh)
            rw [e, Path.nfo_sel_var, Path.nfo_sel_var, hy']
            rfl
      | sel p b =>
          rw [Path.nfo_sel_sel]
          exact Path.nfo_sel_congr a ih

/-! ## Substitutions that keep the oldest variable -/

theorem KeepsOldest.lift {σ : PathSubst s₁ s₂} (hs : s₁ ≠ []) (h : KeepsOldest σ) : KeepsOldest σ.lift := by
  intro y hy
  cases y with
  | here =>
      cases s₁ with
      | nil => exact absurd rfl hs
      | cons _ _ => cases hy
  | there y =>
      obtain ⟨y', e, hy'⟩ := h y hy
      refine ⟨.there y', ?_, hy'⟩
      show (σ.var y).rename Rename.succ = _
      rw [e]
      rfl

theorem KeepsOldest.extend {τ : PathSubst s₁ s₂} (hs : s₁ ≠ []) (h : KeepsOldest τ) (p : Path s₂) : KeepsOldest (τ.extend p) := by
  intro y hy
  cases y with
  | here =>
      cases s₁ with
      | nil => exact absurd rfl hs
      | cons _ _ => cases hy
  | there y => exact h y hy

theorem KeepsOldest.ofRename_id : KeepsOldest (PathSubst.ofRename (Rename.id : Rename s s)) :=
  fun y hy => ⟨y, rfl, hy⟩

theorem KeepsOldest.one (hs : s ≠ []) (p : Path s) : KeepsOldest (PathSubst.one p : PathSubst (s,x) s) := by
  intro y hy
  cases y with
  | here =>
      cases s with
      | nil => exact absurd rfl hs
      | cons _ _ => cases hy
  | there y => exact ⟨y, rfl, hy⟩

/-! ## Laws of the normal form of types -/

theorem nfo_lift_congr {σ σ' : PathSubst s₁ s₂} (h : ∀ y, Path.nfo (σ.var y) = Path.nfo (σ'.var y)) :
    ∀ y, Path.nfo (σ.lift.var y) = Path.nfo (σ'.lift.var y)
  | .here => rfl
  | .there y => by
      show Path.nfo ((σ.var y).rename Rename.succ) = Path.nfo ((σ'.var y).rename Rename.succ)
      rw [Path.nfo_rename_succ, Path.nfo_rename_succ, h y]

mutual
theorem Ty.nfo_subst_congr (T : Ty s₁) {σ σ' : PathSubst s₁ s₂} (h : ∀ y, Path.nfo (σ.var y) = Path.nfo (σ'.var y)) : Ty.nfo (T.subst σ) = Ty.nfo (T.subst σ') :=
  match T with
  | .bot => rfl
  | .sel p A => by
      show Ty.sel (Path.nfo (p.subst _)) A = Ty.sel (Path.nfo (p.subst _)) A
      rw [Path.nfo_subst_congr p h]
  | .pi S T => by
      show Ty.pi (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _)) = Ty.pi (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_congr S h, Ty.nfo_subst_congr T (nfo_lift_congr h)]
  | .mu Tel => by
      show Ty.mu (Telescope.nfo (Tel.subst _)) = Ty.mu (Telescope.nfo (Tel.subst _))
      rw [Telescope.nfo_subst_congr Tel (nfo_lift_congr h)]
theorem Pr.nfo_subst_congr (pr : Pr s₁) {σ σ' : PathSubst s₁ s₂} (h : ∀ y, Path.nfo (σ.var y) = Path.nfo (σ'.var y)) : Pr.nfo (pr.subst σ) = Pr.nfo (pr.subst σ') :=
  match pr with
  | .le S T => by
      show Pr.le (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _)) = Pr.le (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_congr S h, Ty.nfo_subst_congr T h]
  | .fld a T => by
      show Pr.fld a (Ty.nfo (T.subst _)) = Pr.fld a (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_congr T h]
  | .alias q => by
      show Pr.alias (Path.nfo (q.subst _)) = Pr.alias (Path.nfo (q.subst _))
      rw [Path.nfo_subst_congr q h]
  | .is T => by
      show Pr.is (Ty.nfo (T.subst _)) = Pr.is (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_congr T h]
theorem Telescope.nfo_subst_congr (Tel : Telescope s₁) {σ σ' : PathSubst s₁ s₂} (h : ∀ y, Path.nfo (σ.var y) = Path.nfo (σ'.var y)) : Telescope.nfo (Tel.subst σ) = Telescope.nfo (Tel.subst σ') :=
  match Tel with
  | .nil => rfl
  | .cons Tel pr => by
      show Telescope.cons (Telescope.nfo (Tel.subst _)) (Pr.nfo (pr.subst _)) = Telescope.cons (Telescope.nfo (Tel.subst _)) (Pr.nfo (pr.subst _))
      rw [Telescope.nfo_subst_congr Tel h, Pr.nfo_subst_congr pr h]
end

mutual
theorem Ty.nfo_subst_nfo (T : Ty s₁) {σ : PathSubst s₁ s₂} (hs : s₁ ≠ []) (h : KeepsOldest σ) : Ty.nfo ((Ty.nfo T).subst σ) = Ty.nfo (T.subst σ) :=
  match T with
  | .bot => rfl
  | .sel p A => by
      show Ty.sel (Path.nfo ((Path.nfo p).subst _)) A = Ty.sel (Path.nfo (p.subst _)) A
      rw [Path.nfo_subst_nfo p h]
  | .pi S T => by
      show Ty.pi (Ty.nfo ((Ty.nfo S).subst _)) (Ty.nfo ((Ty.nfo T).subst _)) = Ty.pi (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_nfo S hs h, Ty.nfo_subst_nfo T (List.cons_ne_nil _ _) (KeepsOldest.lift hs h)]
  | .mu Tel => by
      show Ty.mu (Telescope.nfo ((Telescope.nfo Tel).subst _)) = Ty.mu (Telescope.nfo (Tel.subst _))
      rw [Telescope.nfo_subst_nfo Tel (List.cons_ne_nil _ _) (KeepsOldest.lift hs h)]
theorem Pr.nfo_subst_nfo (pr : Pr s₁) {σ : PathSubst s₁ s₂} (hs : s₁ ≠ []) (h : KeepsOldest σ) : Pr.nfo ((Pr.nfo pr).subst σ) = Pr.nfo (pr.subst σ) :=
  match pr with
  | .le S T => by
      show Pr.le (Ty.nfo ((Ty.nfo S).subst _)) (Ty.nfo ((Ty.nfo T).subst _)) = Pr.le (Ty.nfo (S.subst _)) (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_nfo S hs h, Ty.nfo_subst_nfo T hs h]
  | .fld a T => by
      show Pr.fld a (Ty.nfo ((Ty.nfo T).subst _)) = Pr.fld a (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_nfo T hs h]
  | .alias q => by
      show Pr.alias (Path.nfo ((Path.nfo q).subst _)) = Pr.alias (Path.nfo (q.subst _))
      rw [Path.nfo_subst_nfo q h]
  | .is T => by
      show Pr.is (Ty.nfo ((Ty.nfo T).subst _)) = Pr.is (Ty.nfo (T.subst _))
      rw [Ty.nfo_subst_nfo T hs h]
theorem Telescope.nfo_subst_nfo (Tel : Telescope s₁) {σ : PathSubst s₁ s₂} (hs : s₁ ≠ []) (h : KeepsOldest σ) : Telescope.nfo ((Telescope.nfo Tel).subst σ) = Telescope.nfo (Tel.subst σ) :=
  match Tel with
  | .nil => rfl
  | .cons Tel pr => by
      show Telescope.cons (Telescope.nfo ((Telescope.nfo Tel).subst _)) (Pr.nfo ((Pr.nfo pr).subst _)) = Telescope.cons (Telescope.nfo (Tel.subst _)) (Pr.nfo (pr.subst _))
      rw [Telescope.nfo_subst_nfo Tel hs h, Pr.nfo_subst_nfo pr hs h]
end

/-! ## Laws of the reading -/

theorem dsemTel_iff (τ : PathSubst s' ([],x)) (Tel : Telescope s') (p : Path ([],x)) : dsemTel τ Tel p ↔ ∀ i pr, Tel.At i pr → dsemPr τ pr p :=
  match Tel with
  | .nil => ⟨fun _ _ _ hi => (Telescope.At.nil_of_eq hi rfl).elim, fun _ => trivial⟩
  | .cons Tel pr => by
      show dsemTel τ Tel p ∧ dsemPr τ pr p ↔ _
      rw [dsemTel_iff τ Tel p]
      refine ⟨fun ⟨h₁, h₂⟩ i pr' hi => ?_, fun h => ⟨fun i pr' hi => h i pr' (.there hi), h _ _ .here⟩⟩
      rcases Telescope.At.cons_of_eq hi rfl with ⟨-, rfl⟩ | hi
      · exact h₂
      · exact h₁ i pr' hi

mutual
theorem dsem_subst (T : Ty s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) (p : Path ([],x)) : dsem τ (T.subst σ) p ↔ dsem (σ.comp τ) T p :=
  match T with
  | .bot => Iff.rfl
  | .sel _ _ => Iff.rfl
  | .pi _ _ => Iff.rfl
  | .mu Tel => by
      show danglingReach p ∧ dsemTel (τ.extend p) (Tel.subst σ.lift) p ↔ danglingReach p ∧ dsemTel ((σ.comp τ).extend p) Tel p
      rw [dsemTel_subst Tel σ.lift (τ.extend p) p, PDot.Source.PathSubst.lift_comp_extend]
theorem dsemTel_subst (Tel : Telescope s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) (p : Path ([],x)) : dsemTel τ (Tel.subst σ) p ↔ dsemTel (σ.comp τ) Tel p :=
  match Tel with
  | .nil => Iff.rfl
  | .cons Tel pr => by
      show dsemTel τ (Tel.subst σ) p ∧ dsemPr τ (pr.subst σ) p ↔ dsemTel (σ.comp τ) Tel p ∧ dsemPr (σ.comp τ) pr p
      rw [dsemTel_subst Tel σ τ p, dsemPr_subst pr σ τ p]
theorem dsemPr_subst (pr : Pr s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) (p : Path ([],x)) : dsemPr τ (pr.subst σ) p ↔ dsemPr (σ.comp τ) pr p :=
  match pr with
  | .le S T => by
      show (∀ r, dsem τ (S.subst σ) r → dsem τ (T.subst σ) r) ↔ (∀ r, dsem (σ.comp τ) S r → dsem (σ.comp τ) T r)
      exact forall_congr' fun r => imp_congr (dsem_subst S σ τ r) (dsem_subst T σ τ r)
  | .fld a T => dsem_subst T σ τ (p.sel a)
  | .alias q => by
      show Path.nfo p = Path.nfo ((q.subst σ).subst τ) ↔ Path.nfo p = Path.nfo (q.subst (σ.comp τ))
      rw [Path.subst_subst]
  | .is T => dsem_subst T σ τ p
end

mutual
theorem dsem_nfo (T : Ty s') (τ : PathSubst s' ([],x)) (hs : s' ≠ []) (h : KeepsOldest τ) (p : Path ([],x)) : dsem τ (Ty.nfo T) p ↔ dsem τ T p :=
  match T with
  | .bot => Iff.rfl
  | .sel _ _ => Iff.rfl
  | .pi _ _ => Iff.rfl
  | .mu Tel => by
      show danglingReach p ∧ dsemTel (τ.extend p) (Telescope.nfo Tel) p ↔ danglingReach p ∧ dsemTel (τ.extend p) Tel p
      rw [dsemTel_nfo Tel (τ.extend p) (List.cons_ne_nil _ _) (KeepsOldest.extend hs h p) p]
theorem dsemTel_nfo (Tel : Telescope s') (τ : PathSubst s' ([],x)) (hs : s' ≠ []) (h : KeepsOldest τ) (p : Path ([],x)) : dsemTel τ (Telescope.nfo Tel) p ↔ dsemTel τ Tel p :=
  match Tel with
  | .nil => Iff.rfl
  | .cons Tel pr => by
      show dsemTel τ (Telescope.nfo Tel) p ∧ dsemPr τ (Pr.nfo pr) p ↔ dsemTel τ Tel p ∧ dsemPr τ pr p
      rw [dsemTel_nfo Tel τ hs h p, dsemPr_nfo pr τ hs h p]
theorem dsemPr_nfo (pr : Pr s') (τ : PathSubst s' ([],x)) (hs : s' ≠ []) (h : KeepsOldest τ) (p : Path ([],x)) : dsemPr τ (Pr.nfo pr) p ↔ dsemPr τ pr p :=
  match pr with
  | .le S T => by
      show (∀ r, dsem τ (Ty.nfo S) r → dsem τ (Ty.nfo T) r) ↔ (∀ r, dsem τ S r → dsem τ T r)
      exact forall_congr' fun r => imp_congr (dsem_nfo S τ hs h r) (dsem_nfo T τ hs h r)
  | .fld a T => dsem_nfo T τ hs h (p.sel a)
  | .alias q => by
      show Path.nfo p = Path.nfo ((Path.nfo q).subst τ) ↔ Path.nfo p = Path.nfo (q.subst τ)
      rw [Path.nfo_subst_nfo q h]
  | .is T => dsem_nfo T τ hs h p
end

theorem dsem_reach {τ : PathSubst s' ([],x)} : ∀ {T : Ty s'} {p : Path ([],x)}, dsem τ T p → danglingReach p
  | .bot, _, h => h.elim
  | .sel _ _, _, h => h.elim
  | .pi _ _, _, h => h.elim
  | .mu _, _, h => h.1

/-- A proposition under the self, read with the self closed at `p`, is `semPrOf` of the reading at
the identity. -/
theorem dsemPr_open (pr : Pr (([],x),x)) (p : Path ([],x)) :
    dsemPr ((PathSubst.ofRename Rename.id).extend p) pr p ↔
      semPrOf (fun T r => dsem (PathSubst.ofRename Rename.id) T r) (fun r r' => Path.nfo r = Path.nfo r') pr p := by
  have e := PDot.Source.PathSubst.one_comp_ofRename_id p
  cases pr with
  | le S T =>
      show (∀ r, dsem _ S r → dsem _ T r) ↔ (∀ r, dsem _ (S.subst (PathSubst.one p)) r → dsem _ (T.subst (PathSubst.one p)) r)
      exact forall_congr' fun r => imp_congr (by rw [dsem_subst, e]) (by rw [dsem_subst, e])
  | fld a T =>
      show dsem _ T (p.sel a) ↔ dsem _ (T.subst (PathSubst.one p)) (p.sel a)
      rw [dsem_subst, e]
  | alias q =>
      show Path.nfo p = Path.nfo (q.subst _) ↔ Path.nfo p = Path.nfo (q.substPath p)
      rw [← Path.subst_one, ← e, ← Path.subst_subst, Path.subst_ofRename, Path.rename_id]
  | is T =>
      show dsem _ T p ↔ dsem _ (T.subst (PathSubst.one p)) p
      rw [dsem_subst, e]

/-! ## The dangling context defines no type -/

theorem danglingCtx_nodeAt : ∀ (p : Path ([],x)),
    danglingCtx.nodeAt p = none ∨ (∃ q, danglingCtx.nodeAt p = some (.fwd q)) ∨
      danglingCtx.nodeAt p = some (.node .nil (.cons .nil lh (.fwd (.sel (.var .here) lzz))))
  | .var .here => .inr (.inr rfl)
  | .sel p a => by
      rcases danglingCtx_nodeAt p with h | ⟨q, h⟩ | h
      · exact .inl (by simp [Ctx.nodeAt, h])
      · exact .inl (by simp [Ctx.nodeAt, h, Block.child])
      · by_cases ha : a = lh
        · subst ha; exact .inr (.inl ⟨.sel (.var .here) lzz, by simp [Ctx.nodeAt, h, Block.child, Kids.get]⟩)
        · exact .inl (by simp [Ctx.nodeAt, h, Block.child, Kids.get, ha])

theorem danglingCtx_defAt (p : Path ([],x)) (A : Label) : danglingCtx.defAt p A = none := by
  unfold Ctx.defAt
  rcases danglingCtx_nodeAt p with h | ⟨q, h⟩ | h <;> simp [h, Block.def, TyDefs.get]

/-! ## The model -/

def danglingModel : Model danglingCtx where
  sem T p := dsem (PathSubst.ofRename Rename.id) T p
  reach := danglingReach
  peq p q := Path.nfo p = Path.nfo q
  teq S T := Ty.nfo S = Ty.nfo T
  var x := by
    cases x with
    | here => exact And.intro (Or.inl rfl) (And.intro trivial (And.intro (Or.inr rfl) (And.intro trivial rfl)))
    | there y => nomatch y
  reach_sem _ _ h := dsem_reach h
  reach_sel p a h := by
    rcases h with h | h
    · cases h
    · cases h; exact .inl rfl
  mu Tel p := by
    show danglingReach p ∧ dsemTel _ Tel p ↔ _
    rw [dsemTel_iff]
    exact and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun pr => imp_congr_right fun _ => dsemPr_open pr p)
  bot _ h := h
  pi _ _ _ h := h
  alias S T p q hS hpq hT := by
    have hp := dsem_reach hS
    have hq := dsem_reach hT
    have e : p = q := by
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · rfl
      · exact absurd hpq (fun h => nomatch h)
      · exact absurd hpq.symm (fun h => nomatch h)
      · rfl
    subst e
    exact hT
  peq_refl _ := rfl
  peq_symm _ _ h := h.symm
  peq_trans _ _ _ h₁ h₂ := h₁.trans h₂
  peq_sel p q a h := Path.nfo_sel_congr a h
  teq_sem S T h p hS :=
    (dsem_nfo T _ (List.cons_ne_nil _ _) KeepsOldest.ofRename_id p).1
      (h ▸ (dsem_nfo S _ (List.cons_ne_nil _ _) KeepsOldest.ofRename_id p).2 hS)
  teq_refl _ := rfl
  teq_symm _ _ h := h.symm
  teq_trans _ _ _ h₁ h₂ := h₁.trans h₂
  teq_defP p A W h := by rw [danglingCtx_defAt] at h; cases h
  teq_lift T p q h := Ty.nfo_subst_congr T (σ := PathSubst.one p) (σ' := PathSubst.one q) (fun y => by
    cases y with
    | here => exact h
    | there y => rfl)
  teq_dom S₁ T₁ S₂ T₂ h := (Ty.pi.inj (h : Ty.pi (Ty.nfo S₁) (Ty.nfo T₁) = Ty.pi (Ty.nfo S₂) (Ty.nfo T₂))).1
  teq_cod S₁ T₁ S₂ T₂ p h := by
    have e := (Ty.pi.inj (h : Ty.pi (Ty.nfo S₁) (Ty.nfo T₁) = Ty.pi (Ty.nfo S₂) (Ty.nfo T₂))).2
    show Ty.nfo (T₁.subst (PathSubst.one p)) = Ty.nfo (T₂.subst (PathSubst.one p))
    rw [← Ty.nfo_subst_nfo T₁ (List.cons_ne_nil _ _) (KeepsOldest.one (List.cons_ne_nil _ _) p),
      ← Ty.nfo_subst_nfo T₂ (List.cons_ne_nil _ _) (KeepsOldest.one (List.cons_ne_nil _ _) p), e]

end Dangling

/-! ## The negative examples -/

theorem fact2_untyped (P : PathCo ([],x)) (U : Ty []) : ¬ Value.HasType .nil (.obj fact2Tel (fact2Defs P)) U := by
  intro h
  obtain ⟨_, hd⟩ := h.obj_inv
  obtain ⟨Tel, q, T, e, _, _, _⟩ := hd.path_inv
  simp [fact2Tel, Telescope.rename, Pr.rename, bnds, Ty.sngl, Ty.rename] at e

theorem badBounds_untyped (P : PathCo ([],x)) (v : Value ([],x)) (U : Ty []) : ¬ Value.HasType .nil (.obj badBoundsTel (badBoundsDefs P v)) U := by
  intro h
  obtain ⟨_, hd⟩ := h.obj_inv
  obtain ⟨Tel, S, T, e, _, _, _⟩ := hd.fn_inv
  simp [badBoundsTel, Telescope.rename, Pr.rename, Ty.rename] at e

theorem dangling_path_untyped {P : PathCo ([],x)} {T : Ty ([],x)} : PathCo.HasType danglingCtx P T → P.path ≠ .sel (.var .here) lzz := by
  intro h e
  have hr := Dangling.danglingModel.reach_path h
  rw [e] at hr
  rcases hr with hr | hr <;> cases hr

theorem dangling_untyped (P : PathCo ([],x)) (U : Ty []) : ¬ Value.HasType .nil (.obj danglingTel (danglingDefs P)) U := by
  intro h
  obtain ⟨_, hd⟩ := h.obj_inv
  obtain ⟨Tel, q, T, e, hq, _, hP⟩ := hd.path_inv
  have e₁ := (Pr.fld.inj (Telescope.cons.inj e).2).2
  rw [Ty.sngl_rename] at e₁
  have e₂ : (Path.sel (.var .here) lzz : Path (([],x),x)).weaken (k := .var) = q.weaken (k := .var) :=
    (Pr.alias.inj (Telescope.cons.inj (Ty.mu.inj e₁)).2)
  have e₃ : (Path.sel (.var .here) lzz : Path (([],x),x)) = q := by
    have := congrArg (fun r => Path.substPath r (.var .here)) e₂
    simpa only [Path.weaken_substPath] using this
  subst e₃
  have hpath : P.path = .sel (.var .here) lzz := hq
  have hctx : Ctx.nil.cons (.transparent (.mu danglingTel) (danglingDefs P).block) = danglingCtx := by
    show Ctx.nil.cons (.transparent _ (.node .nil (.cons .nil lh (.fwd P.path)))) = _
    rw [hpath]
    rfl
  rw [hctx] at hP
  exact dangling_path_untyped hP hpath

/-! ## The binder example over full FCp (`D3_Proto.lean:1422-1497`) -/

namespace Binder

abbrev types : Label := .trm 10
abbrev m : Label := .trm 11
abbrev f : Label := .trm 12
abbrev A : Label := .typ 10
/-- The nested annotation, under the outer self w and its own self v: [⊤ ⊑ v∙A, v∙A ⊑ ⊤, fld f Π(_ : ⊤) ⊤]. -/
def telTypes : Telescope (([],x),x) := .cons (.cons (.cons .nil (.le .top (.sel (.var .here) A))) (.le (.sel (.var .here) A) .top)) (.fld f (.pi .top .top))
/-- core's annotation: [fld types μ(v : telTypes), fld m (w.types).type]. -/
def telCore : Telescope ([],x) := .cons (.cons .nil (.fld types (.mu telTypes))) (.fld m (Ty.sngl (.sel (.var .here) types)))
/-- The nested definitions, addressed at z.types: {A = ⊤}, {f = fun λ(u : ⊤) u}. -/
def dsTypes : Defs ([],x) := .fld (.typ .nil A .top) f (.fn (.lam .top (.path (.var .here))))
/-- core's definitions: {types = nest (v : telTypes) dsTypes}, {m = path z.types}.  telTypes does not mention w, so
it is its own instance at z. -/
def dsCore : Defs ([],x) := .fld (.fld .nil types (.nest telTypes dsTypes)) m (.path (.sel (.var .here) types 0))
def coreVal : Value [] := .obj telCore dsCore
def σ0 : Store ([],x) := Store.nil.cons coreVal
def Γ0 : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telCore) dsCore.block)
def Γ1 : Ctx (([],x),x) := Γ0.cons (.opaque (Ty.sngl (.sel (.var .here) types)))        -- Γ0, y : core.types.type
abbrev y1 : Path (([],x),x) := .var .here
abbrev core1 : Path (([],x),x) := .var (.there .here)
def Py : PathCo (([],x),x) := .var .here
def πy : PEq (([],x),x) := .member Py (.refl (Ty.sngl (core1.sel types))) 0         -- y ≃ core.types
def Ptypes1 : PathCo (([],x),x) := .sel (.var (.there .here)) types 0
def PyAtTypes : PathCo (([],x),x) := .alias Py πy Ptypes1                              -- y at core.types' type
def Pyf : PathCo (([],x),x) := .sel PyAtTypes f 2                                      -- y.f
def φyA : EqCo (([],x),x) := .lift (.sel (.var .here) A) πy                            -- y∙A ≡ core.types∙A
def Pm : PathCo ([],x) := .sel (.var .here) m 1                                        -- core.m

/-- `DF-Typ` and `DF-Fun` at `core.types`, `DF-Nest` and `DF-Path` at `core`, then `VA-Obj`. -/
theorem coreVal_typed : Value.HasType .nil coreVal (.mu telCore) := by
  refine .obj ?_
  have hTypes : Defs.HasType Γ0 (.sel (.var .here) types) dsTypes
      ((telTypes.rename Rename.succ.lift.lift).subst (PathSubst.one (.var .here)).lift) := by
    have h₁ : Defs.HasType Γ0 (.sel (.var .here) types) (Defs.typ .nil A .top)
        (.cons (.cons .nil (.le .top (.sel (.var .here) A))) (.le (.sel (.var .here) A) .top)) :=
      .typ .nil (by decide) rfl
    exact Defs.HasType.fn (a := f) (S := .top) (T := .top) (v := .lam .top (.path (.var .here)))
      h₁ (by decide) rfl (.lam (.path (.var rfl)))
  have hNest := Defs.HasType.nest (a := types) (Defs.HasType.nil (Γ := Γ0) (p := .var .here)) (by decide) hTypes
  have hP : PathCo.HasType Γ0 (.sel (.var .here) types 0) _ := .sel (.var rfl) (.there .here)
  exact Defs.HasType.path (a := m) (q := .sel (.var .here) types) hNest (by decide) hP rfl
/-- `ST-Obj`: the store variable is the literal's own self. -/
theorem σ0_typed : Store.Typed σ0 Γ0 := .obj .nil coreVal_typed
/-- `Γ0.defAt` reads the nested node at `core.types` and nothing at the alias `core.m`. -/
theorem Γ0_defAt : Γ0.defAt (.sel (.var .here) types) A = some .top ∧ Γ0.defAt (.sel (.var .here) m) A = none :=
  ⟨rfl, rfl⟩
/-- `PE-Member` at the singleton of `y`. -/
theorem πy_ty : PEq.HasType Γ1 πy y1 (core1.sel types) := by
  have hy : PathCo.HasType Γ1 Py (Ty.sngl (core1.sel types)) := .var rfl
  exact .member hy .refl .here
/-- `y.f`, selected from `y` at `core.types`' type after the alias. -/
theorem Pyf_ty : PathCo.HasType Γ1 Pyf (.pi .top .top) := by
  have hTypes : PathCo.HasType Γ1 Ptypes1
      (((Ty.mu (telTypes.rename Rename.succ.lift.lift)).rename Rename.succ.lift).substPath core1) :=
    .sel (.var rfl) (.there .here)
  exact .sel (.alias (.var rfl) πy_ty hTypes) .here
/-- `EQ-Lift` of `y∙A` along the alias. -/
theorem φyA_ty : EqCo.HasType Γ1 φyA (.sel y1 A) (.sel (core1.sel types) A) := .lift πy_ty
theorem Pm_ty : PathCo.HasType Γ0 Pm (Ty.sngl (.sel (.var .here) types)) := by
  have h := PathCo.HasType.sel (Γ := Γ0) (P := .var .here) (.var rfl) .here
  exact h
/-- The binder closed by `y := core.m`. -/
theorem Pyf_closed : PathCo.HasType Γ0 (Pyf.substCo Pm) (.pi .top .top) := PathCo.HasType.substCo Pm_ty Pyf_ty
theorem Pyf_closed_path : (Pyf.substCo Pm).path = .sel (.sel (.var .here) m) f := rfl
theorem πy_closed : PEq.HasType Γ0 (πy.substCo Pm) (.sel (.var .here) m) (.sel (.var .here) types) :=
  PEq.HasType.substCo Pm_ty πy_ty
theorem φyA_closed : EqCo.HasType Γ0 (φyA.substCo Pm) (.sel (.sel (.var .here) m) A) (.sel (.sel (.var .here) types) A) :=
  EqCo.HasType.substCo Pm_ty φyA_ty

end Binder

/-! ## The risk of the stage: `adjust` with path evidence inside evidence -/

namespace Adjust

abbrev f : Label := .trm 20
def tel : Telescope ([],x) := .cons .nil (.fld f (.pi .top .top))
def ds : Defs ([],x) := .fld .nil f (.fn (.lam .top (.path (.var .here))))
def lit : Value [] := .obj tel ds
def E : LeCo [] := .top (.mu tel)
/-- A let body whose `PA-Alias` has `P₀ = var z`, typed with `z : opaque ⊤`. -/
def body : Tm ([],x) := .path (.alias (.var .here) (.refl (.var .here)) (.var .here))

theorem body_typed : Tm.HasType (Ctx.nil.cons (.opaque .top)) body .top :=
  .path (.alias (.var rfl) .refl (.var rfl))
theorem adjusted : body.adjust (.cast lit E) = .path (.alias (.cast (.var .here) (E.rename Rename.succ)) (.refl (.var .here)) (.cast (.var .here) (E.rename Rename.succ))) :=
  rfl
/-- After the allocation `P₀` is `cast (var z) E↑`: its type changed and its path did not, so
`PA-Alias` still holds.  The typing is `Tm.HasType.subst` at `CoSubst.Typed.selfCast`. -/
theorem adjusted_typed : Tm.HasType (Ctx.nil.cons (.transparent (.mu tel) ds.block)) (body.adjust (.cast lit E)) .top := by
  have hE : LeCo.HasType .nil E (.mu tel) .top := .top
  have h := Tm.HasType.subst (CoSubst.Typed.selfCast hE (.transparent (.mu tel) ds.block) rfl) body_typed
  rw [CoSubst.selfCast_paths] at h
  exact h

end Adjust

/-! ## The checker on the examples (group g5) -/

/-- let core = coreVal in let g = λ(y : core.types.type). y.f (cast y to ⊤) in g core.m -/
def binderProg : Tm [] :=
  .lett (.val Binder.coreVal)
    (.lett (.val (.lam (Ty.sngl (.sel (.var .here) Binder.types)) (.app Binder.Pyf (.cast Binder.Py (.top (Ty.sngl (Binder.core1.sel Binder.types)))))))
      (.app (.var .here) (.sel (.var (.there .here)) Binder.m 1)))
theorem binderProg_check : checkTm .nil binderProg .top = true := by decide +kernel
theorem binderProg_typed : Tm.HasType .nil binderProg .top := checkTm_iff.1 binderProg_check
theorem Binder.Pyf_check : checkPath Binder.Γ1 Binder.Pyf (.pi .top .top) = true := by decide +kernel
theorem Binder.coreVal_synth : synthValue .nil Binder.coreVal = some (.mu Binder.telCore) := by decide +kernel
/-- fact2_untyped's twin: the literal with the field body `x.a`. -/
def fact2Prog : Tm [] := .val (.obj fact2Tel (fact2Defs (.sel (.var .here) la 0)))
theorem fact2Prog_synth : synthTm .nil fact2Prog = none := by decide +kernel
theorem fact2Prog_untyped (T : Ty []) : ¬ Tm.HasType .nil fact2Prog T := fun h => by
  have h' := checkTm_iff.2 h
  rw [checkTm, fact2Prog_synth] at h'
  have e : (none : Option (Ty [])) = some T := of_decide_eq_true h'
  cases e
def danglingProg : Tm [] := .val (.obj danglingTel (danglingDefs (.sel (.var .here) lzz 0)))
theorem danglingProg_synth : synthTm .nil danglingProg = none := by decide +kernel

end PDot.FCp
