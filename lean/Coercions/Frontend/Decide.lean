import Coercions.DotMNF.Typing
import Coercions.FCdot.Checker

/-!
# The decided side conditions

The typer computes two side conditions.  Both are here.

* `defsDistinct?` decides `DotMNF.Defs.Distinct`, the distinctness of the
  labels of a definition block (`defsDistinct?_iff`).
* `tyStrengthen?` is the inverse of `DotMNF.Ty.weaken` (`tyStrengthen?_iff`).
  Avoidance at a `let` uses it when the type of the body does not mention the
  binder.  `tyStrengthenW?` also returns the equation, and
  `instDecidableIsWeakening` decides whether a type is a weakening.

Strengthening is `tyRename?` under the partial renaming `PartialRename.unshift`
of `lean/Coercions/FCdot/Checker.lean`.  That machinery is generic over `Sig`,
`Kind` and `BVar`.  Only the traversal of `DotMNF.Ty` is defined here, in the
shape of the target's `Ty.rename?`.

`DotMNF.Ty.Decl` needs no function here, since `Ty.isDecl` decides it.  All
definitions are structural, so `decide` evaluates them.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open DotMNF (Path Ty Defs Ctx)

/-! ## Distinctness of the labels of a definition block

`DotMNF.Defs.labels` lists the labels of a block, and `FCdot.Label` has
`DecidableEq`, so the test is list membership. -/

/-- No label of the left block is a label of the right block. -/
def labelsDisjoint? (d e : Defs s) : Bool :=
  d.labels.all (fun l => ! e.labels.contains l)

theorem labelsDisjoint?_iff (d e : Defs s) :
    labelsDisjoint? d e = true ↔ ∀ l, l ∈ d.labels → l ∉ e.labels := by
  simp [labelsDisjoint?]

/-- The decision procedure for `DotMNF.Defs.Distinct`. -/
def defsDistinct? : Defs s → Bool
  | .typ _ _ => true
  | .trm _ _ => true
  | .and d e => defsDistinct? d && defsDistinct? e && labelsDisjoint? d e

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

The traversal of `DotMNF.Path` and `DotMNF.Ty` under a partial renaming, with
soundness and completeness against a total renaming it inverts.  Strengthening
is the case `PartialRename.unshift`. -/

/-- A path under a partial renaming.  A path is a variable in this calculus. -/
def pathRename? : Path s1 → PartialRename s1 s2 → Option (Path s2)
  | .var x, rho => (rho.var x).map .var

/-- A type under a partial renaming.  It fails exactly when some variable of the
type is outside the domain of the renaming. -/
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

theorem pathRename?_complete {s1 s2 : Sig} (q : Path s2) (rho : PartialRename s1 s2)
    (sigma : Rename s2 s1) (h : rho.Inverts sigma) :
    pathRename? (q.rename sigma) rho = some q := by
  cases q with
  | var x =>
      simp only [Path.rename, pathRename?]
      rw [(h (sigma.var x) x).mpr rfl]
      rfl

theorem pathRename?_sound {s1 s2 : Sig} (p : Path s1) (q : Path s2)
    (rho : PartialRename s1 s2) (sigma : Rename s2 s1) (h : rho.Inverts sigma)
    (hq : pathRename? p rho = some q) : p = q.rename sigma := by
  cases p with
  | var x =>
      simp only [pathRename?, Option.map_eq_some_iff] at hq
      obtain ⟨y, hy, hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [(h x y).mp hy]

theorem tyRename?_complete :
    ∀ {s1 s2 : Sig} (U : Ty s2) (rho : PartialRename s1 s2) (sigma : Rename s2 s1),
      rho.Inverts sigma → tyRename? (U.rename sigma) rho = some U
  | _, _, .top, _, _, _ => by simp [Ty.rename, tyRename?]
  | _, _, .bot, _, _, _ => by simp [Ty.rename, tyRename?]
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

/-- Strengthening with the equation it establishes.  The typer rewrites the
typing of a `let` body along it. -/
def tyStrengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U.weaken } :=
  match witness? (tyStrengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, tyStrengthen?_sound hU⟩
  | none => none

theorem tyStrengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [tyStrengthenW?, FCdot.witness?_eq_some (tyStrengthen?_weaken (k := k) U)]

/-- Whether a type is a weakening, decided by `tyStrengthen?`. -/
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

/-! ## The variables of a context

The self binder `consSelf` of an object literal is a binder like any other for
`Ctx.lookup`, so its variable is in the list.  Example E6 of
`lean/Coercions/DotMNF/Examples.lean` needs it. -/

/-- Every variable of a context, newest binder first. -/
def ctxVars : Ctx s → List (BVar s .var)
  | .nil => []
  | .cons Gamma _ => .here :: (ctxVars Gamma).map .there
  | .consSelf Gamma _ _ => .here :: (ctxVars Gamma).map .there

/-! ## Tests

These are checked by `decide`. -/

section Tests

open FCdot (Label)

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
/-- The traversal goes under `mu`, and the binder it strips is the outer one. -/
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there (.there .here))) (Label.typ 0))))
    = some (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there .here)) (Label.typ 0)))) := by
  decide
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.mu (Ty.fld (Label.trm 0) (Ty.sel (.var (.there .here)) (Label.typ 0)))) = none := by
  decide

/-- The self binder of an object literal is a variable of the context. -/
example : ctxVars (Ctx.consSelf (Ctx.cons Ctx.nil Ty.top) (Defs.typ (Label.typ 0) Ty.top) Ty.top)
    = [.here, .there .here] := by decide

end Tests

end Frontend
