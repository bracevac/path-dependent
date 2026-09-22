import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.FCdot.Preservation

namespace Paths

/-!
# Refutation of write-up A, scratch 2: section 6 brings Fact 4 back

Outside the import graph, against the g6 tree.

Write-up A section 6 changes the representation of blocks: a child is written
over the parent's self, the walk instantiates it at the parent path when it
descends (`b.substPath p`), and a definition is read at the *query* path
(`lookupDefP p ℓ = (W.get ℓ).substPath p`).  It claims that
`Ctx.blockFuel_budget` "is unchanged in argument, since the walk still spends
one unit per forwarding node and the targets are counted per node", and that
`defPairs` "enumerates the forest instantiating as it descends".

One literal refutes both claims: `ν(z. {A = z.a.A} ∧ {val a = z})`, whose field
`a` forwards to its own self.  Under section 6 the walk from `x.a^k` follows the
*one* forwarding node `k` times (it is instantiated at `x.a^(k-1)`, then at
`x.a^(k-2)`, and so on), so the budget `fwdCount + 1 = 2` answers `none` at
`x.a.a` while fuel `3` answers the node: the budget is not stable.  And the
definition read at `x.a^k` is `x.a^(k+1) ∙ A`, so the chain of definitions
from `x ∙ A` visits the keys `(x.a, A)`, `(x.a.a, A)`, `(x.a.a.a, A)`, ... which
are pairwise distinct and unbounded in depth: no finite enumeration of the
forest lists them, and the key pigeonhole of `Resolution.lean:8-27` (L2 to L4 of
P1.4) has nothing to count.  This is exactly Fact 4 of the plan, which decision
8 was made to avoid.

In the g6 tree the same literal is alias-tolerant: every `x.a^k` walks to one
node at the budget, and every `lookupDefP (x.a^k) A` is the one type
`x.a ∙ A`, a fixed point that resolution settles.

Section 6's lookup is modelled here on this one-node forest, with its two
clauses written out (`pass6`/`walk6` and `def6`).  The model is the write-up's
own code specialised to a forest with one object node, one child, and one
binder.
-/

namespace FCdot
namespace ScratchSnglSec6

def lA : Label := .typ 0
def la : Label := .trm 0

/-! ## The literal, typed in the g6 tree -/

/-- The self of the literal, in its own scope. -/
def selfS : Path ([],x) := .var .here

/-- `A ≐ self.a ∙ A`, and `a ≐ μ [≈ self↑]`. -/
def WS : Witnesses ([],x) :=
  (Witnesses.nil.cons lA (Ty.sel (.sel selfS la) lA)).cons la (Ty.obj (.nil ▹ .alias selfS.weaken))

/-- The body of `a`, the self, cast to `self ∙ a` through its singleton. -/
def eS : LeCo ([],x) :=
  .trans (.intoSngl (.var .here) selfS (.refl selfS)) (.eqToLe (.symm (.def .here la)))

def FS : Fields ([],x) := Fields.nil.cons la (.cast (.atom (.var .here)) eS)
def vS : Value [] := .obj WS FS
def TS : Ty [] := μ (Telescope.ofLiteral WS FS.labels FS.valLabels)

theorem vS_typed : Ctx.nil ⊢ᵥ vS : TS := by
  have h := checkTm_sound (Γ := Ctx.nil) (t := .val vS) (T := TS) (by decide +kernel)
  cases h with
  | val hv => exact hv

def σS : Store ([],x) := .cons .nil vS
def ΓS : Ctx ([],x) := Ctx.nil.cons (.transparent TS (vS.weaken.blocksAt (.var .here)))

theorem σS_typed : ⊢ σS : ΓS := Store.Typed.cons .nil trivial vS_typed

/-- `x.a^k`. -/
def xa : Nat → Path ([],x)
  | 0 => .var .here
  | k+1 => .sel (xa k) la

theorem xa_inj : ∀ k j, xa k = xa j → k = j
  | 0, 0, _ => rfl
  | 0, j+1, h => by simp [xa] at h
  | k+1, 0, h => by simp [xa] at h
  | k+1, j+1, h => by
      simp only [xa, Path.sel.injEq, and_true] at h
      rw [xa_inj k j h]

/-! ## The g6 tree: one node, one definition, a fixed point -/

/-- The budget of the g6 walk on this context: one forwarding node. -/
example : ΓS.aliasBudget = 2 := by decide +kernel

/-- Every `x.a^k` walks to the node of `x` at the budget. -/
example : ΓS.lookupBlock (xa 1) = ΓS.lookupBlock (xa 0) := by decide +kernel
example : ΓS.lookupBlock (xa 2) = ΓS.lookupBlock (xa 0) := by decide +kernel
example : ΓS.lookupBlock (xa 3) = ΓS.lookupBlock (xa 0) := by decide +kernel
example : (ΓS.lookupBlock (xa 3)).isSome := by decide +kernel

/-- The definition of `A` is written at `x` and is the same at every alias:
`x.a ∙ A`.  L1 of P1.4 (`Ctx.lookupDefP_fwd`). -/
example : ΓS.lookupDefP (xa 0) lA = some (Ty.sel (xa 1) lA) := by decide +kernel
example : ΓS.lookupDefP (xa 1) lA = some (Ty.sel (xa 1) lA) := by decide +kernel
example : ΓS.lookupDefP (xa 3) lA = some (Ty.sel (xa 1) lA) := by decide +kernel

/-- The chain from `x ∙ A` stands at the listed key `(x.a, A)` and stays there: a
self-alias, which resolution settles as `⊤`. -/
example : ΓS.resolve (Ty.sel (xa 0) lA) = ⊤ := by decide +kernel
example : ΓS.resolve (Ty.sel (xa 1) lA) = ⊤ := by decide +kernel

/-! ## Section 6, modelled on this forest

The one object node is the root, with the self-abstract witnesses of the stored
literal, `W6 : Witnesses (([],x),x)` (self `.here`, the store binder
`.there .here`).  Its one child, at `a`, is `fwd self` over the parent's self,
which section 6 instantiates at the parent path `p` as `fwd p` before following
it.  `pass6`/`walk6` are section 6's `blockPass`/`blockFuel` on this forest, and
`def6` is its `lookupDefP`: the witness read at the query path. -/

/-- The self-abstract witnesses of the stored literal. -/
def W6 : Witnesses (([],x),x) := (vS.weaken).witnesses

/-- One pass of section 6's walk: a variable is the root node; a field step
`p.a` reads the child at `a`, `fwd self`, instantiated at `p` as `fwd p`, and
follows it with one unit less. -/
def pass6 (k : Path ([],x) → Option (Witnesses (([],x),x))) :
    Path ([],x) → Option (Witnesses (([],x),x))
  | .var _ => some W6
  | .sel p a =>
      match pass6 k p with
      | some _ => if a = la then k p else none
      | none => none

def walk6 : Nat → Path ([],x) → Option (Witnesses (([],x),x))
  | 0, _ => none
  | n+1, p => pass6 (walk6 n) p

/-- Section 6's definition of `p ∙ ℓ`: the self-abstract witness instantiated
at the query path. -/
def def6 (n : Nat) (p : Path ([],x)) (ℓ : Label) : Option (Ty ([],x)) :=
  (walk6 n p).map fun W => (W.get ℓ).substPath p

/-- One forwarding node in the forest, so the budget of decision 9 is `2`. -/
def budget6 : Nat := 1 + 1

/-! ### The budget is not stable under section 6 -/

/-- At the budget, `x.a.a` is opaque. -/
theorem walk6_budget_none : walk6 budget6 (xa 2) = none := by decide

/-- With one more unit it is the root node. -/
theorem walk6_three_some : walk6 3 (xa 2) = some W6 := by decide

/-- In general: `x.a^k` needs fuel `k + 1`, one unit per field step, because
the one forwarding node is followed once per step. -/
theorem walk6_xa_some : ∀ k m, walk6 (k + 1 + m) (xa k) = some W6
  | 0, m => by rw [Nat.add_comm]; rfl
  | k+1, m => by
      have h1 := walk6_xa_some k (m + 1)
      have h2 := walk6_xa_some k m
      have e : k + 1 + 1 + m = (k + 1 + m) + 1 := by omega
      rw [e]
      show pass6 (walk6 (k + 1 + m)) (.sel (xa k) la) = some W6
      have e1 : pass6 (walk6 (k + 1 + m)) (xa k) = walk6 (k + 1 + (m + 1)) (xa k) := by
        rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega]; rfl
      simp only [pass6, e1, h1]
      simpa using h2

theorem walk6_xa_none : ∀ k, walk6 k (xa k) = none
  | 0 => rfl
  | k+1 => by
      show pass6 (walk6 k) (.sel (xa k) la) = none
      simp only [pass6]
      rw [show pass6 (walk6 k) (xa k) = walk6 (k + 1) (xa k) from rfl,
        walk6_xa_some k 0]
      simp [la, walk6_xa_none k]

/-- **The budget `fwdCount + 1` is not stable under section 6.**  The write-up's
claim that `Ctx.blockFuel_budget` is "unchanged in argument" is false: one
forwarding node is followed `k` times on `x.a^k`. -/
theorem budget6_not_stable :
    walk6 budget6 (xa 2) = none ∧ walk6 (budget6 + 1) (xa 2) = some W6 :=
  ⟨walk6_budget_none, walk6_three_some⟩

/-! ### The keys of the definition chain are unbounded under section 6 -/

/-- The definition of `x.a^k ∙ A` under section 6 is `x.a^(k+1) ∙ A`. -/
theorem def6_xa (k : Nat) : def6 (k + 1) (xa k) lA = some (Ty.sel (xa (k + 1)) lA) := by
  simp only [def6, walk6_xa_some k 0, Option.map_some]
  rfl

/-- So the chain from `x ∙ A` stands at `(x.a^k, A)` after `k` steps, and these
keys are pairwise distinct: the key pigeonhole of `Resolution.lean` (a chain
longer than `defPairs` repeats a key) counts nothing here.  Fact 4. -/
theorem keys6_distinct (k j : Nat) (h : k ≠ j) : (xa k, lA) ≠ (xa j, lA) := by
  intro he
  exact h (xa_inj k j (Prod.mk.inj he).1)

/-- L1 of P1.4 (`Ctx.lookupDefP_fwd`, `Context.lean:757`) is false under section
6: `x` and `x.a` walk to one node and read two definitions. -/
theorem l1_false_sec6 :
    walk6 3 (xa 0) = walk6 3 (xa 1) ∧ def6 3 (xa 0) lA ≠ def6 3 (xa 1) lA := by
  constructor
  · decide
  · decide

#print axioms vS_typed
#print axioms σS_typed
#print axioms budget6_not_stable
#print axioms walk6_xa_some
#print axioms walk6_xa_none
#print axioms def6_xa
#print axioms keys6_distinct
#print axioms l1_false_sec6

end ScratchSnglSec6
end FCdot

end Paths
