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

/-- Reading a variable in its own prefix is reading it directly.  The `y`
instance of `lookupAt_upTo` that the locality lemma needs, stated without a
transport because `varUpTo x` is `.here` and `scopeUpTo (varUpTo x)` is
`scopeUpTo x` definitionally. -/
theorem lookupAt_upTo_self : {σ s : Sig} → (Γ : Ctx σ s) → (x : BVar s .var) →
    (Γ.upTo x).lookupAt (varUpTo x) = Γ.lookupAt x
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons Γ _, .there y => lookupAt_upTo_self Γ y

/-- Truncating a prefix at its own newest binder changes nothing. -/
theorem upTo_upTo_self : {σ s : Sig} → (Γ : Ctx σ s) → (x : BVar s .var) →
    (Γ.upTo x).upTo (varUpTo x) = Γ.upTo x
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons Γ _, .there y => upTo_upTo_self Γ y

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

/-! ## Iterating the prefix

Taking the prefix twice — first at `x`, then at a variable `y` of `x`'s prefix
— is taking it once, at the variable of the ambient scope that `y` names.  The
three laws below are that statement at the level of scopes, of renamings and of
variables.  They are `HEq`s because the two sides live in
`scopeUpTo ((renameUpTo x).var y)` and in `scopeUpTo y`, which agree only by
`scopeUpTo_renameUpTo` — a propositional equality of `Sig`s, not a definitional
one, since `renameUpTo x` does not reduce at a variable `x`.

`SubstTyping`'s Lemma R is exactly this coherence, carried through a
substitution; these are the transport-free half of it. -/

/-! ### Transport helpers

Each takes the scope equality *explicitly* rather than extracting it from an
`HEq`, so that `subst` applies and the heterogeneous statement collapses to a
homogeneous one in one step. -/

/-- Two renamings that agree heterogeneously agree on heterogeneously equal
variables. -/
theorem heq_rename_var {s A B : Sig} (hAB : A = B) {f : Rename A s}
    {g : Rename B s} (hf : HEq f g) {a : BVar A .var} {b : BVar B .var}
    (hab : HEq a b) : f.var a = g.var b := by
  subst hAB
  rw [eq_of_heq hf, eq_of_heq hab]

/-- Equal subjects have the same weakening out of their prefix.  Stated as an
`HEq` because `renameAt` is dependent in its subject. -/
theorem heq_renameAt {σ s : Sig} {p p' : Vr σ s} (h : p = p') :
    HEq (renameAt p) (renameAt p') := by subst h; rfl

/-- Post-composition preserves heterogeneous equality of renamings. -/
theorem heq_comp_right {s1 s2 A B : Sig} (hAB : A = B) {f : Rename A s1}
    {g : Rename B s1} (hf : HEq f g) (k : Rename s1 s2) :
    HEq (f.comp k) (g.comp k) := by
  subst hAB
  rw [eq_of_heq hf]

/-- Renaming a variable by a composite is renaming twice.  The `Vr` instance of
`Oopsla16.Vr.subst_comp`, stated on `rename` so that a rewrite finds it. -/
theorem Vr.rename_comp {σ s1 s2 s3 : Sig} (v : Vr σ s1) (ρ : Rename s1 s2)
    (ρ' : Rename s2 s3) : v.rename (ρ.comp ρ') = (v.rename ρ).rename ρ' := by
  cases v <;> rfl

/-- An injective renaming reflects heterogeneous equality of variables: if two
variables of scopes that agree have the same image, they agree. -/
theorem Vr.heq_of_rename {σ s A B : Sig} (hAB : A = B) {ρ : Rename A s}
    {ρ' : Rename B s} (hρ : HEq ρ ρ')
    (hinj : ∀ u w : Vr σ B, u.rename ρ' = w.rename ρ' → u = w)
    {v1 : Vr σ A} {v2 : Vr σ B} (h : v1.rename ρ = v2.rename ρ') : HEq v1 v2 := by
  subst hAB
  rw [eq_of_heq hρ] at h
  exact heq_of_eq (hinj v1 v2 h)

/-! ### The composition laws -/

/-- **Weakenings out of iterated prefixes compose.**  Weakening out of the
prefix at `y` and then out of the prefix at `x` is weakening out of the prefix
at the variable `y` names in the ambient scope.  This is the reference's
`GH = GU ++ GL` used twice, and it is where the recursion on `x` happens once
and for all. -/
theorem renameUpTo_comp : {s : Sig} → (x : BVar s .var) →
    (y : BVar (scopeUpTo x) .var) →
    HEq (renameUpTo ((renameUpTo x).var y)) ((renameUpTo y).comp (renameUpTo x))
  | _ :: _, .here, _ => heq_of_eq (Rename.comp_id _).symm
  | _ :: _, .there x', y =>
      (heq_comp_right (scopeUpTo_renameUpTo x' y) (renameUpTo_comp x' y)
          Rename.succ).trans
        (heq_of_eq (Rename.comp_assoc _ _ _))

/-- The scope level of the same law, at a subject of either zone.  At a
location both sides are the empty local scope. -/
theorem scopeAt_rename_renameAt {σ s : Sig} : (q : Vr σ s) →
    (u : Vr σ (scopeAt q)) → scopeAt (u.rename (renameAt q)) = scopeAt u
  | .abs x, .abs z => scopeUpTo_renameUpTo x z
  | .abs _, .conc _ => rfl
  | .conc _, .conc _ => rfl
  | .conc _, .abs u => nomatch u

/-- The renaming level, at a subject of either zone.  At a location both sides
are the unique map out of the empty local scope. -/
theorem renameAt_rename_renameAt {σ s : Sig} : (q : Vr σ s) →
    (u : Vr σ (scopeAt q)) →
    HEq (renameAt (u.rename (renameAt q))) ((renameAt u).comp (renameAt q))
  | .abs x, .abs z => renameUpTo_comp x z
  | .abs _, .conc _ => heq_of_eq (Rename.funext' (fun w => nomatch w))
  | .conc _, .conc _ => heq_of_eq (Rename.funext' (fun w => nomatch w))
  | .conc _, .abs u => nomatch u

end FCdotR
