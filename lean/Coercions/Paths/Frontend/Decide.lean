import Coercions.Paths.DotMNF.Typing
import Coercions.Paths.FCdot.Checker

/-!
# The decided side conditions

Decision procedures for the side conditions of the typer.  `Ty.Decl` is
already decided in the version (`Ty.isDecl`).  This module decides three more.

- Well-formedness of a type, a premise of `HasTy.lam` and `HasTy.let`:
  `tyWf?`.
- Distinctness of the labels of a definition block, a premise of `HasTy.obj`
  and `DefsTy.trmObj`: `defsDistinct?`.
- Strengthening, the inverse of `Ty.weaken`: `tyStrengthen?`.  Avoidance at
  a `let` (`Avoid.lean`) uses it to take a body's type past the bound
  variable.

Strengthening also decides the one premise of `SelfFree` that is not a syntactic
match.  `SelfFree.closed` needs two types that do not mention the self binder
and a subtyping between their strengthened forms.  `selfFree?` strengthens both
sides and asks a subtyping search for the rest.  The search is an argument, so
this module can come before the search that calls it.

Strengthening reuses the partial renaming of the target
(`lean/Coercions/Paths/FCdot/Checker.lean`).  Only the traversal of `Path` and
`Ty` is written here.

Every recursive definition carries `termination_by structural`, so it reduces
in the kernel and `by decide` works on it.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open Paths.DotMNF (Path Ty Defs Ctx Sub SelfFree)

/-! ## Well-formedness of a type

`tyWf?` mirrors `Ty.Wf` clause for clause.  Like `Wf.typ`, it asks nothing of
the bounds, so `{A : S..T}` is well formed with bad bounds.  A selection and a
singleton are well formed whatever their path. -/

/-- The decision procedure for `Paths.DotMNF.Ty.Wf`. -/
def tyWf? : Ty s → Bool
  | .top | .bot | .sel _ _ | .sngl _ => true
  | .typ _ S T => tyWf? S && tyWf? T
  | .fld _ T => tyWf? T
  | .vfld _ T => tyWf? T
  | .mu T => tyWf? T && T.isDecl
  | .all S T => tyWf? S && tyWf? T
  | .and S T => tyWf? S && tyWf? T
termination_by structural T => T

theorem tyWf?_iff : ∀ {s : Sig} (T : Ty s), tyWf? T = true ↔ Ty.Wf T
  | _, .top => ⟨fun _ => .top, fun _ => rfl⟩
  | _, .bot => ⟨fun _ => .bot, fun _ => rfl⟩
  | _, .sel _ _ => ⟨fun _ => .sel, fun _ => rfl⟩
  | _, .sngl _ => ⟨fun _ => .sngl, fun _ => rfl⟩
  | _, .typ _ S T =>
      ⟨fun h => by
        rw [tyWf?, Bool.and_eq_true] at h
        exact .typ ((tyWf?_iff S).mp h.1) ((tyWf?_iff T).mp h.2),
       fun h => by
        cases h with
        | typ hS hT =>
            rw [tyWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff S).mpr hS, (tyWf?_iff T).mpr hT⟩⟩
  | _, .fld _ T =>
      ⟨fun h => by rw [tyWf?] at h; exact .fld ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | fld hT => rw [tyWf?]; exact (tyWf?_iff T).mpr hT⟩
  | _, .vfld _ T =>
      ⟨fun h => by rw [tyWf?] at h; exact .vfld ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | vfld hT => rw [tyWf?]; exact (tyWf?_iff T).mpr hT⟩
  | _, .mu T =>
      ⟨fun h => by
        rw [tyWf?, Bool.and_eq_true] at h
        exact .mu ((tyWf?_iff T).mp h.1) ((Ty.isDecl_iff T).mp h.2),
       fun h => by
        cases h with
        | mu hT hD =>
            rw [tyWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff T).mpr hT, (Ty.isDecl_iff T).mpr hD⟩⟩
  | _, .all S T =>
      ⟨fun h => by
        rw [tyWf?, Bool.and_eq_true] at h
        exact .all ((tyWf?_iff S).mp h.1) ((tyWf?_iff T).mp h.2),
       fun h => by
        cases h with
        | all hS hT =>
            rw [tyWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff S).mpr hS, (tyWf?_iff T).mpr hT⟩⟩
  | _, .and S T =>
      ⟨fun h => by
        rw [tyWf?, Bool.and_eq_true] at h
        exact .and ((tyWf?_iff S).mp h.1) ((tyWf?_iff T).mp h.2),
       fun h => by
        cases h with
        | and hS hT =>
            rw [tyWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff S).mpr hS, (tyWf?_iff T).mpr hT⟩⟩

instance instDecidableTyWf {s : Sig} (T : Ty s) : Decidable (Ty.Wf T) :=
  decidable_of_iff _ (tyWf?_iff T)

/-! ## Distinctness of the labels of a definition block

The test is list membership on `Defs.labels`. -/

/-- No label of the left block is a label of the right block. -/
def labelsDisjoint? (d e : Defs s) : Bool :=
  d.labels.all (fun l => ! e.labels.contains l)

theorem labelsDisjoint?_iff (d e : Defs s) :
    labelsDisjoint? d e = true ↔ ∀ l, l ∈ d.labels → l ∉ e.labels := by
  simp [labelsDisjoint?]

/-- The decision procedure for `Paths.DotMNF.Defs.Distinct`. -/
def defsDistinct? : Defs s → Bool
  | .typ _ _ => true
  | .trm _ _ => true
  | .and d e => defsDistinct? d && defsDistinct? e && labelsDisjoint? d e
termination_by structural d => d

theorem defsDistinct?_iff : ∀ {s : Sig} (d : Defs s), defsDistinct? d = true ↔ Defs.Distinct d
  | _, .typ _ _ => ⟨fun _ => .typ, fun _ => rfl⟩
  | _, .trm _ _ => ⟨fun _ => .trm, fun _ => rfl⟩
  | _, .and d e =>
      ⟨fun h => by
        rw [defsDistinct?, Bool.and_eq_true, Bool.and_eq_true] at h
        exact .and ((defsDistinct?_iff d).mp h.1.1) ((defsDistinct?_iff e).mp h.1.2)
          ((labelsDisjoint?_iff d e).mp h.2),
       fun h => by
        cases h with
        | and hd he hdis =>
            rw [defsDistinct?, Bool.and_eq_true, Bool.and_eq_true]
            exact ⟨⟨(defsDistinct?_iff d).mpr hd, (defsDistinct?_iff e).mpr he⟩,
              (labelsDisjoint?_iff d e).mpr hdis⟩⟩

instance instDecidableDefsDistinct {s : Sig} (d : Defs s) : Decidable (Defs.Distinct d) :=
  decidable_of_iff _ (defsDistinct?_iff d)

/-! ## Strengthening

The traversal of `Path` and `Ty` under a partial renaming, with soundness and
completeness against a total renaming it inverts.  Strengthening is the action
of `PartialRename.unshift`.  A path fails exactly when its root fails. -/

/-- A path under a partial renaming.  The root is renamed, the steps are kept. -/
def pathRename? : Path s1 → PartialRename s1 s2 → Option (Path s2)
  | .var x, rho => (rho.var x).map .var
  | .sel p a, rho => (pathRename? p rho).map (fun q => .sel q a)
termination_by structural p => p

/-- A type under a partial renaming.  It fails when a variable of the type is
outside the domain. -/
def tyRename? : Ty s1 → PartialRename s1 s2 → Option (Ty s2)
  | .top, _ => some .top
  | .bot, _ => some .bot
  | .typ A S T, rho =>
      match tyRename? S rho, tyRename? T rho with
      | some S', some T' => some (.typ A S' T')
      | _, _ => none
  | .fld a T, rho =>
      match tyRename? T rho with
      | some T' => some (.fld a T')
      | none => none
  | .vfld a T, rho =>
      match tyRename? T rho with
      | some T' => some (.vfld a T')
      | none => none
  | .sngl p, rho => (pathRename? p rho).map .sngl
  | .sel p A, rho => (pathRename? p rho).map (fun q => .sel q A)
  | .mu T, rho =>
      match tyRename? T rho.lift with
      | some T' => some (.mu T')
      | none => none
  | .all S T, rho =>
      match tyRename? S rho, tyRename? T rho.lift with
      | some S', some T' => some (.all S' T')
      | _, _ => none
  | .and S T, rho =>
      match tyRename? S rho, tyRename? T rho with
      | some S', some T' => some (.and S' T')
      | _, _ => none
termination_by structural T => T

theorem pathRename?_complete :
    ∀ {s1 s2 : Sig} (q : Path s2) (rho : PartialRename s1 s2) (sigma : Rename s2 s1),
      rho.Inverts sigma → pathRename? (q.rename sigma) rho = some q
  | _, _, .var x, rho, sigma, h => by
      simp only [Path.rename, pathRename?]
      rw [(h (sigma.var x) x).mpr rfl]
      rfl
  | _, _, .sel q a, rho, sigma, h => by
      simp only [Path.rename, pathRename?]
      rw [pathRename?_complete q rho sigma h]
      rfl

theorem pathRename?_sound :
    ∀ {s1 s2 : Sig} (p : Path s1) (q : Path s2) (rho : PartialRename s1 s2)
      (sigma : Rename s2 s1), rho.Inverts sigma → pathRename? p rho = some q →
      p = q.rename sigma
  | _, _, .var x, q, rho, sigma, h, hq => by
      simp only [pathRename?, Option.map_eq_some_iff] at hq
      obtain ⟨y, hy, hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [(h x y).mp hy]
  | _, _, .sel p a, q, rho, sigma, h, hq => by
      simp only [pathRename?, Option.map_eq_some_iff] at hq
      obtain ⟨q', hq', hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [← pathRename?_sound p q' rho sigma h hq']

theorem tyRename?_complete :
    ∀ {s1 s2 : Sig} (U : Ty s2) (rho : PartialRename s1 s2) (sigma : Rename s2 s1),
      rho.Inverts sigma → tyRename? (U.rename sigma) rho = some U
  | _, _, .top, _, _, _ => by simp [Ty.rename, tyRename?]
  | _, _, .bot, _, _, _ => by simp [Ty.rename, tyRename?]
  | _, _, .sngl p, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [pathRename?_complete p rho sigma h]
      rfl
  | _, _, .sel p A, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [pathRename?_complete p rho sigma h]
      rfl
  | _, _, .typ A S T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete S rho sigma h, tyRename?_complete T rho sigma h]
  | _, _, .fld a T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete T rho sigma h]
  | _, _, .vfld a T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete T rho sigma h]
  | _, _, .mu T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete T rho.lift sigma.lift h.lift]
  | _, _, .all S T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete S rho sigma h, tyRename?_complete T rho.lift sigma.lift h.lift]
  | _, _, .and S T, rho, sigma, h => by
      simp only [Ty.rename, tyRename?]
      rw [tyRename?_complete S rho sigma h, tyRename?_complete T rho sigma h]

theorem tyRename?_sound :
    ∀ {s1 s2 : Sig} (T : Ty s1) (U : Ty s2) (rho : PartialRename s1 s2) (sigma : Rename s2 s1),
      rho.Inverts sigma → tyRename? T rho = some U → T = U.rename sigma
  | _, _, .top, U, _, _, _, hU => by
      simp only [tyRename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .bot, U, _, _, _, hU => by
      simp only [tyRename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .sngl p, U, rho, sigma, h, hU => by
      simp only [tyRename?, Option.map_eq_some_iff] at hU
      obtain ⟨q, hq, hU⟩ := hU
      subst hU
      simp only [Ty.rename]
      rw [← pathRename?_sound p q rho sigma h hq]
  | _, _, .sel p A, U, rho, sigma, h, hU => by
      simp only [tyRename?, Option.map_eq_some_iff] at hU
      obtain ⟨q, hq, hU⟩ := hU
      subst hU
      simp only [Ty.rename]
      rw [← pathRename?_sound p q rho sigma h hq]
  | _, _, .typ A S T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hS : tyRename? S rho with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : tyRename? T rho with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← tyRename?_sound S S' rho sigma h hS, ← tyRename?_sound T T' rho sigma h hT]
  | _, _, .fld a T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hT : tyRename? T rho with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Ty.rename]
        rw [← tyRename?_sound T T' rho sigma h hT]
  | _, _, .vfld a T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hT : tyRename? T rho with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Ty.rename]
        rw [← tyRename?_sound T T' rho sigma h hT]
  | _, _, .mu T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hT : tyRename? T rho.lift with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Ty.rename]
        rw [← tyRename?_sound T T' rho.lift sigma.lift h.lift hT]
  | _, _, .all S T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hS : tyRename? S rho with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : tyRename? T rho.lift with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← tyRename?_sound S S' rho sigma h hS,
            ← tyRename?_sound T T' rho.lift sigma.lift h.lift hT]
  | _, _, .and S T, U, rho, sigma, h, hU => by
      simp only [tyRename?] at hU
      cases hS : tyRename? S rho with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : tyRename? T rho with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← tyRename?_sound S S' rho sigma h hS, ← tyRename?_sound T T' rho sigma h hT]

/-- Undo one weakening, if the innermost binder does not occur in the type. -/
def tyStrengthen? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option (Ty s) :=
  tyRename? T PartialRename.unshift

theorem tyStrengthen?_sound {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s}
    (h : tyStrengthen? T = some U) : T = U.weaken :=
  tyRename?_sound T U PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem tyStrengthen?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthen? (U.weaken (k := k)) = some U :=
  tyRename?_complete U PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Strengthening inverts weakening, on the nose. -/
theorem tyStrengthen?_iff {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s} :
    tyStrengthen? T = some U ↔ T = U.weaken := by
  constructor
  · exact tyStrengthen?_sound
  · intro h; subst h; exact tyStrengthen?_weaken U

/-- Strengthening, with the equation it establishes.  Avoidance at a `let`
rewrites the body's typing along that equation. -/
def tyStrengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U.weaken } :=
  match witness? (tyStrengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, tyStrengthen?_sound hU⟩
  | none => none

theorem tyStrengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [tyStrengthenW?, Paths.FCdot.witness?_eq_some (tyStrengthen?_weaken (k := k) U)]

/-- Strengthening fails exactly on a type that is no weakening. -/
theorem tyStrengthenW?_none {s : Sig} {k : Kind} {T : Ty (s,,k)}
    (h : tyStrengthenW? T = none) : ¬ ∃ U : Ty s, T = U.weaken := by
  rintro ⟨U, rfl⟩
  rw [tyStrengthenW?_weaken] at h
  cases h

/-- Being a weakening is decided by `tyStrengthen?`. -/
instance instDecidableIsWeakening {s : Sig} {k : Kind} (T : Ty (s,,k)) :
    Decidable (∃ U : Ty s, T = U.weaken) :=
  decidable_of_iff ((tyStrengthen? T).isSome = true)
    ⟨fun h => by
      cases hT : tyStrengthen? T with
      | none => rw [hT] at h; simp at h
      | some U => exact ⟨U, tyStrengthen?_sound hT⟩,
     fun h => by
      obtain ⟨U, hU⟩ := h
      subst hU
      rw [tyStrengthen?_weaken U]
      rfl⟩

/-! ## Self-free steps

`SelfFree Γ X Y` is the step a declared bound may take inside `Sub.mu`.  `X`
and `Y` live under the self binder.  Three rules are syntactic: `refl` at equal
sides, `bot` at a lower side `⊥`, `top` at an upper side `⊤`.  The fourth,
`closed`, needs both sides free of the self and their strengthened forms
related at the outer context `Γ`.

`selfFree?` tries the rules in that order.  The subtyping `sub` for `closed` is
passed in, and the subtyping search passes itself.  A failure means that no rule
applied with this `sub`. -/

/-- A self-free step from a closed subtyping, along the two equations that
strengthening returns. -/
def selfFreeClosedOf {s : Sig} {Γ : Ctx s} {X Y : Ty (s,x)} {X' Y' : Ty s}
    (hX : X = X'.weaken) (hY : Y = Y'.weaken) (e : Sub Γ X' Y') : SelfFree Γ X Y := by
  subst hX hY
  exact .closed e

/-- Search a self-free step from `X` to `Y`, with `sub` answering the subtyping
that `SelfFree.closed` needs. -/
def selfFree? {s : Sig} {Γ : Ctx s} (sub : (S T : Ty s) → Option (Sub Γ S T))
    (X Y : Ty (s,x)) : Option (SelfFree Γ X Y) :=
  if h : X = Y then some (h ▸ .refl)
  else if hb : X = .bot then some (hb ▸ .bot)
  else if ht : Y = .top then some (ht ▸ .top)
  else
    match tyStrengthenW? X, tyStrengthenW? Y with
    | some ⟨X', hX⟩, some ⟨Y', hY⟩ => (sub X' Y').map (selfFreeClosedOf hX hY)
    | _, _ => none

/-- `selfFree?` succeeds wherever the search it is handed is stronger.  The
monotonicity proof of the subtyping search uses this. -/
theorem selfFree?_isSome_of {s : Sig} {Γ : Ctx s} {sub sub' : (S T : Ty s) → Option (Sub Γ S T)}
    (hsub : ∀ S T, (sub S T).isSome → (sub' S T).isSome) (X Y : Ty (s,x))
    (h : (selfFree? sub X Y).isSome) : (selfFree? sub' X Y).isSome := by
  unfold selfFree? at h ⊢
  by_cases hXY : X = Y
  · rw [dif_pos hXY]; rfl
  · by_cases hb : X = .bot
    · rw [dif_neg hXY, dif_pos hb]; rfl
    · by_cases ht : Y = .top
      · rw [dif_neg hXY, dif_neg hb, dif_pos ht]; rfl
      · rw [dif_neg hXY, dif_neg hb, dif_neg ht] at h ⊢
        cases hX : tyStrengthenW? X with
        | none => rw [hX] at h; simp at h
        | some X' =>
          cases hY : tyStrengthenW? Y with
          | none => rw [hX, hY] at h; simp at h
          | some Y' =>
            obtain ⟨X', hX'⟩ := X'
            obtain ⟨Y', hY'⟩ := Y'
            rw [hX, hY] at h
            simp only [Option.isSome_map] at h ⊢
            exact hsub X' Y' h

/-! ## The variables of a context

The binder `consSelf` of an object literal is a variable like any other, so it
is in the list.  Example E6 of `lean/Coercions/Paths/DotMNF/Examples.lean`
needs it. -/

/-- Every variable of a context, newest binder first. -/
def ctxVars : Ctx s → List (BVar s .var)
  | .nil => []
  | .cons Gamma _ => .here :: (ctxVars Gamma).map .there
  | .consSelf Gamma _ _ => .here :: (ctxVars Gamma).map .there
termination_by structural Gamma => Gamma

/-! ## Tests

Every test is `by decide`. -/

section Tests

/-- A singleton and a stable field are well formed. -/
example : tyWf? (Ty.mu (Ty.and (Ty.vfld (Label.trm 0) Ty.top) (Ty.sngl (.var .here))) : Ty [])
    = true := by decide
example : tyWf? (Ty.mu (Ty.all Ty.top Ty.top) : Ty []) = false := by decide
/-- Below a stable field the check goes on. -/
example : tyWf? (Ty.vfld (Label.trm 0) (Ty.mu Ty.bot) : Ty []) = false := by decide
/-- Bad bounds are well formed. -/
example : Ty.Wf (Ty.typ (Label.typ 0) Ty.top Ty.bot : Ty []) := by decide
example : ¬ Ty.Wf (Ty.mu Ty.bot : Ty []) := by decide

example : Defs.Distinct
    (Defs.and (Defs.typ (Label.typ 0) Ty.top) (Defs.typ (Label.typ 1) Ty.top) : Defs []) := by
  decide
example : ¬ Defs.Distinct
    (Defs.and (Defs.typ (Label.typ 0) Ty.top) (Defs.typ (Label.typ 0) Ty.top) : Defs []) := by
  decide

example : tyStrengthen? (k := .var) ((Ty.fld (Label.trm 0) Ty.top : Ty []).weaken)
    = some (Ty.fld (Label.trm 0) Ty.top) := by decide
example : tyStrengthen? (s := []) (k := .var) (Ty.sel (.var .here) (Label.typ 0)) = none := by
  decide
/-- The traversal goes under `mu` and strips the outer binder. -/
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there (.there .here))) (Label.typ 0))))
    = some (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there .here)) (Label.typ 0)))) := by
  decide
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there .here)) (Label.typ 0)))) = none := by
  decide
/-- A path keeps its field steps and loses one binder at its root. -/
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.sngl (.sel (.sel (.var (.there .here)) (Label.trm 0)) (Label.trm 1)))
    = some (Ty.sngl (.sel (.sel (.var .here) (Label.trm 0)) (Label.trm 1))) := by
  decide
/-- A path rooted at the stripped binder does not strengthen. -/
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.vfld (Label.trm 0) (Ty.sel (.sel (.var .here) (Label.trm 0)) (Label.typ 0))) = none := by
  decide
example : (tyStrengthenW? (k := .var) ((Ty.sngl (.sel (.var .here) (Label.trm 0)) : Ty ([],x)).weaken)).isSome
    = true := by decide

/-! The four rules of `SelfFree`, through a search that knows one subtyping. -/

/-- A search that proves `{a : ⊥} <: {a : ⊤}` and nothing else. -/
def testSub {s : Sig} {Γ : Ctx s} : (S T : Ty s) → Option (Sub Γ S T)
  | .fld a .bot, .fld b .top =>
      if h : a = b then some (h ▸ Sub.fld Sub.bot) else none
  | _, _ => none

/-- `refl`: the self may occur on both sides. -/
example : (selfFree? (Γ := Ctx.nil) testSub
    (Ty.sel (.var .here) (Label.typ 0)) (Ty.sel (.var .here) (Label.typ 0))).isSome = true := by
  decide
/-- `bot` and `top`. -/
example : (selfFree? (Γ := Ctx.nil) testSub Ty.bot (Ty.sel (.var .here) (Label.typ 0))).isSome
    = true := by decide
example : (selfFree? (Γ := Ctx.nil) testSub (Ty.sel (.var .here) (Label.typ 0)) Ty.top).isSome
    = true := by decide
/-- `closed`: both sides strengthen and the search answers. -/
example : (selfFree? (Γ := Ctx.nil) testSub
    (Ty.fld (Label.trm 0) Ty.bot) (Ty.fld (Label.trm 0) Ty.top)).isSome = true := by decide
/-- No rule: the search has no answer. -/
example : (selfFree? (Γ := Ctx.nil) testSub
    (Ty.fld (Label.trm 0) Ty.top) (Ty.fld (Label.trm 0) Ty.bot)).isSome = false := by decide
/-- No rule: the lower side mentions the self, so `closed` does not apply. -/
example : (selfFree? (Γ := Ctx.cons Ctx.nil Ty.top) testSub
    (Ty.fld (Label.trm 0) (Ty.sel (.var .here) (Label.typ 0)))
    (Ty.fld (Label.trm 0) Ty.top)).isSome = false := by decide

/-- The self binder of an object literal is a variable of the context. -/
example : ctxVars (Ctx.consSelf (Ctx.cons Ctx.nil Ty.top) (Defs.typ (Label.typ 0) Ty.top) Ty.top)
    = [.here, .there .here] := by decide

end Tests

end PathsFrontend
