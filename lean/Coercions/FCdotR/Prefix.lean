import Coercions.Oopsla16.Context

/-!
# The prefix at a variable of either zone

FCdotR's observation evidence — the target's image of `Oopsla16.Htp` — is
indexed by the prefix scope of its subject, exactly as `Htp` is.  But where
`Htp` observes an *abstract* variable only, and the reference handles a
concrete receiver through a separate pair of rules (`stp_strong_sel1/2`,
`dot.v:305-314`), the target has one observation judgment whose subject is a
two-zone `Vr σ s`.  This module is the prefix apparatus for that subject.

The definition that makes it work is

```text
scopeAt (abs x) = scopeUpTo x        scopeAt (conc ℓ) = []
```

`scopeAt (conc ℓ) = []` is not a convention.  The store scope `σ` is a separate
index and is never truncated, so a location is in scope in *every* prefix,
and the empty local scope is precisely where the reference checks a concrete
selection's premise: `stp [] G1 TX T2` (`dot.v:308`).  So one definition
subsumes `stp_sel1`/`stp_sel2`'s weakening by `renameUpTo x` and
`stp_strong_sel1`/`stp_strong_sel2`'s weakening by `renameNil`.

Lemmas `lookupAt_upTo` and `upTo_upTo` are what a locality result for the
observation judgment needs: they say that reading the context through a prefix
agrees with reading it directly.  They are stated with `HEq` because the two
sides live in scopes that are equal but not definitionally so —
`scopeUpTo_renameUpTo` supplies that equality.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Ctx scopeUpTo renameUpTo varUpTo tailBelow renameNil)

/-! ## Reading the context through a prefix -/

/-- The prefix scope of a variable of `x`'s prefix is its prefix scope in the
ambient scope: `renameUpTo` only ever prepends `.there`. -/
theorem tailBelow_renameUpTo : {s : Sig} → (x : BVar s .var) →
    (y : BVar (scopeUpTo x) .var) →
    tailBelow ((renameUpTo x).var y) = tailBelow y
  | _ :: _, .here, _ => rfl
  | _ :: _, .there x', y => tailBelow_renameUpTo x' y

/-- The same, at the level of scopes. -/
theorem scopeUpTo_renameUpTo {s : Sig} (x : BVar s .var)
    (y : BVar (scopeUpTo x) .var) :
    scopeUpTo ((renameUpTo x).var y) = scopeUpTo y :=
  congrArg Sig.extend_var (tailBelow_renameUpTo x y)

/-- Looking a variable up in a prefix agrees with looking it up directly. -/
theorem lookupAt_upTo : {σ s : Sig} → (Γ : Ctx σ s) → (x : BVar s .var) →
    (y : BVar (scopeUpTo x) .var) →
    HEq ((Γ.upTo x).lookupAt y) (Γ.lookupAt ((renameUpTo x).var y))
  | _, _, .cons _ _, .here, _ => HEq.rfl
  | _, _, .cons Γ _, .there x', y => lookupAt_upTo Γ x' y

/-- Truncating a prefix agrees with truncating directly. -/
theorem upTo_upTo : {σ s : Sig} → (Γ : Ctx σ s) → (x : BVar s .var) →
    (y : BVar (scopeUpTo x) .var) →
    HEq ((Γ.upTo x).upTo y) (Γ.upTo ((renameUpTo x).var y))
  | _, _, .cons _ _, .here, _ => HEq.rfl
  | _, _, .cons Γ _, .there x', y => upTo_upTo Γ x' y

/-! ## The prefix at a two-zone variable -/

/-- The prefix scope at a variable.  A location is in scope in every prefix,
so its prefix is the empty local scope. -/
abbrev scopeAt {σ s : Sig} : Vr σ s → Sig
  | .abs x => scopeUpTo x
  | .conc _ => []

/-- The prefix at a variable embeds into the ambient scope.  At an abstract
variable this is the reference's `GH = GU ++ GL`; at a location it is the
weakening out of `stp []`. -/
def renameAt {σ s : Sig} : (p : Vr σ s) → Rename (scopeAt p) s
  | .abs x => renameUpTo x
  | .conc _ => renameNil

/-- The variable itself, seen in its own prefix. -/
abbrev selfAt {σ s : Sig} : (p : Vr σ s) → Vr σ (scopeAt p)
  | .abs x => .abs (varUpTo x)
  | .conc l => .conc l

/-- The context truncated at a variable.  A location needs no hypothesis, so
its truncation is the empty context. -/
def ctxAt {σ s : Sig} : Ctx σ s → (p : Vr σ s) → Ctx σ (scopeAt p)
  | Γ, .abs x => Γ.upTo x
  | _, .conc _ => .nil

@[simp] theorem renameAt_selfAt {σ s : Sig} (p : Vr σ s) :
    (selfAt p).rename (renameAt p) = p := by
  cases p with
  | abs x => exact congrArg Vr.abs (Oopsla16.renameUpTo_varUpTo x)
  | conc l => rfl

@[simp] theorem scopeAt_selfAt {σ s : Sig} (p : Vr σ s) :
    scopeAt (selfAt p) = scopeAt p := by cases p <;> rfl

/-! ## Zones

No former of the observation judgment will change a subject's zone, and
substitution may send an abstract variable to either zone but a location only
to a location.  The zone is recorded here so that invariant is statable. -/

/-- The zone a variable lives in. -/
inductive Zone : Type where
  /-- A hypothesis or an enclosing binder. -/
  | abstract : Zone
  /-- A location of the runtime store. -/
  | concrete : Zone
deriving DecidableEq, Repr

/-- The zone of a variable. -/
def zone {σ s : Sig} : Vr σ s → Zone
  | .abs _ => .abstract
  | .conc _ => .concrete

@[simp] theorem zone_selfAt {σ s : Sig} (p : Vr σ s) : zone (selfAt p) = zone p := by
  cases p <;> rfl

/-- A location's prefix is the empty local scope: the acceptance criterion
that fixes the definition. -/
example {σ s : Sig} (l : BVar σ .var) : scopeAt (.conc l : Vr σ s) = [] := rfl

/-- An abstract variable's prefix is the reference's `GL`. -/
example {σ s : Sig} (x : BVar s .var) : scopeAt (.abs x : Vr σ s) = scopeUpTo x := rfl

end FCdotR
