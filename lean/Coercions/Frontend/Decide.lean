import Coercions.DotMNF.Typing
import Coercions.FCdot.Checker

/-!
# The decided side conditions

Stage F1.1 of `plan-5e-frontend-stages.md`.  The typer of F1.4 discharges four
kinds of side condition.  `DotMNF.Ty.Decl` is already decided in the frozen tree
by `Ty.isDecl`, `Ty.isDecl_iff` and its instance
(`lean/Coercions/DotMNF/Syntax.lean`), so nothing is added for it.  The other
three are here: well-formedness of a type, distinctness of the labels of a
definition block, and strengthening, the inverse of `DotMNF.Ty.weaken`, which
the avoidance ladder of F1.4 climbs.

Strengthening reuses the target's partial renaming machinery verbatim rather
than rewriting it: `FCdot.PartialRename`, `PartialRename.lift`,
`PartialRename.unshift`, `Inverts`, `Inverts.lift`, `unshift_inverts` and
`witness?` (`lean/Coercions/FCdot/Checker.lean`).  That machinery is generic
over `Sig`, `Kind` and `BVar`, which the two calculi share.  Only the traversal
over `DotMNF.Ty` is new, and it copies the shape of the target's own
`Ty.rename?`, `Ty.strengthen?` and `Ty.strengthenW?`.

Every name here is a plain name in `namespace Frontend`, never a member of
`DotMNF.Ty`, `DotMNF.Defs` or `DotMNF.Ctx`, so the functions are written as
applications and not as dot notation (decision 14 of the plan).  Nothing of this
module is part of the metatheory and no definition lives in the `DotMNF` or
`FCdot` namespaces.

Everything here is structural.  No function of this module uses well-founded
recursion, so all of it reduces in the kernel and `by decide` works on it.  The
well-founded sites of the library are the two the plan names, `sub?` and the
typer's mutual block, both in later modules.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open DotMNF (Path Ty Defs Ctx)

/-! ## Well-formedness of a type

`tyWf?` mirrors `DotMNF.Ty.Wf` clause for clause, including the `Ty.Decl`
premise of `Wf.mu` and the absence of any relation between the bounds in
`Wf.typ`: `{A : S..T}` is well formed with bad bounds. -/

/-- The decision procedure for `DotMNF.Ty.Wf`. -/
def tyWf? : Ty s → Bool
  | .top | .bot | .sel _ _ => true
  | .typ _ S T => tyWf? S && tyWf? T
  | .fld _ T => tyWf? T
  | .mu T => tyWf? T && T.isDecl
  | .all S T => tyWf? S && tyWf? T
  | .and S T => tyWf? S && tyWf? T

theorem tyWf?_iff : ∀ {s : Sig} (T : Ty s), tyWf? T = true ↔ Ty.Wf T
  | _, .top => ⟨fun _ => .top, fun _ => rfl⟩
  | _, .bot => ⟨fun _ => .bot, fun _ => rfl⟩
  | _, .sel _ _ => ⟨fun _ => .sel, fun _ => rfl⟩
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

`DotMNF.Defs.labels` is frozen and `FCdot.Label` has `DecidableEq`, so the test
is a list membership test.  Today every example of
`lean/Coercions/DotMNF/Examples.lean` proves distinctness by hand. -/

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

The partial renaming and its inversion lemmas are the target's, reused as they
stand.  What follows is the traversal of `DotMNF.Path` and `DotMNF.Ty` under a
partial renaming, with soundness and completeness against a total renaming it
inverts, and then strengthening as the action of `PartialRename.unshift`. -/

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

/-- Strengthening, carrying the equation it establishes.  This is the form the
avoidance ladder of F1.4 needs: rung two rewrites the body's typing along the
equation, so the equation has to come back with the type. -/
def tyStrengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U.weaken } :=
  match witness? (tyStrengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, tyStrengthen?_sound hU⟩
  | none => none

theorem tyStrengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [tyStrengthenW?, FCdot.witness?_eq_some (tyStrengthen?_weaken (k := k) U)]

/-- A weakened type is one that strengthens.  The third instance: the
proposition the second rung of the avoidance ladder tests, decided by
`tyStrengthen?`. -/
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

`DotMNF.Ctx` has three constructors, and `consSelf`, the binder of an object
literal, is a binder like any other for `Ctx.lookup`, so its variable is in the
list.  Example E6 of `lean/Coercions/DotMNF/Examples.lean` needs it. -/

/-- Every variable of a context, newest binder first. -/
def ctxVars : Ctx s → List (BVar s .var)
  | .nil => []
  | .cons Gamma _ => .here :: (ctxVars Gamma).map .there
  | .consSelf Gamma _ _ => .here :: (ctxVars Gamma).map .there

/-! ## The module reduces in the kernel

Every test below is `by decide`, which is the repo's own idiom and which the
later modules cannot use: `sub?` and the typer are well founded, so they do not
reduce and their tests go through `Frontend.expect` instead (F1.7).  The line is
drawn here, at the last structural module. -/

section Tests

open FCdot (Label)

example : tyWf? (Ty.mu (Ty.fld (Label.trm 0) Ty.top) : Ty []) = true := by decide
example : tyWf? (Ty.mu (Ty.all Ty.top Ty.top) : Ty []) = false := by decide
/-- Bad bounds are well formed: `Wf.typ` relates the two sides not at all. -/
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
