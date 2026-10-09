import Coercions.Frontend.Alg

/-!
# Goals at the recursion limit

Some goals have no finite derivation, and the search runs until the tank is
marked.  A marked tank is the verdict "recursion limit", not a rejection by the
rules.  The kernel checks each goal below at `defaultFuel`.

* `LP`: the loop through `∀` bodies of `Alg.lean`, `p.A` against `q.B`.  Each
  level reaches the same goal under one more binder, so the exact cut never
  fires.
* `PF`: Pierce's divergence of subtyping with bounded quantification, written
  with type members.  The goal comes back renamed under a new binder at every
  level.
* An alias chain whose every link is an intersection of two copies of one
  member.  Every goal along a branch is new, and `sSelHi` tries both members at
  every link, so the work doubles per link.  The goal is false at every fuel.
  The tank stays unmarked at eight links and is marked at ten and twelve.

The verdicts depend on `defaultFuel = 2 ^ 15`.  A fuel below `2 ^ 13` marks the
chain at eight links.  A fuel of `2 ^ 16` leaves it at ten links unmarked.
-/

namespace Frontend.Core

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Defs Ctx Sub HasTy)
open DotMNF.Examples

/-- The loop goal of `LPCtx`: `p.A <: q.B`. -/
def LPGoalLeft : Ty ([],x,x) := .sel (.var (.there .here)) lA

/-- `q.B`. -/
def LPGoalRight : Ty ([],x,x) := .sel (.var .here) lB

-- LP ends with the tank marked.
example : (sub? LPCtx LPGoalLeft LPGoalRight).2.out = true := by decide +kernel

/-- `∀(x : {A : ⊥..⊤}) ∀(z : {A : ⊥..∀(y : {A : ⊥..x.A}) ∀(w : {A : ⊥..y.A}) w.A}) z.A`,
the upper bound of the member in `PFCtx`. -/
def PFType : Ty [] :=
  .all (.typ lA .bot .top)
    (.all (.typ lA .bot (.all (.typ lA .bot (.sel (.var .here) lA))
                          (.all (.typ lA .bot (.sel (.var .here) lA)) (.sel (.var .here) lA))))
      (.sel (.var .here) lA))

/-- `x0 : {A : ⊥..PFType}`. -/
def PFCtx : Ctx ([],x) := Ctx.nil.cons (.typ lA .bot PFType)

/-- `x0.A`. -/
def PFLeft : Ty ([],x) := .sel (.var .here) lA

/-- `∀(x1 : {A : ⊥..x0.A}) ∀(z : {A : ⊥..x1.A}) z.A`. -/
def PFRight : Ty ([],x) :=
  .all (.typ lA .bot (.sel (.var .here) lA))
    (.all (.typ lA .bot (.sel (.var .here) lA)) (.sel (.var .here) lA))

-- PF ends with the tank marked.
example : (sub? PFCtx PFLeft PFRight).2.out = true := by decide +kernel

/-- `x0 : {A : ⊥..⊤}` and `xk : {A : x(k-1).A..x(k-1).A} ∧ {A : x(k-1).A..x(k-1).A}`
for `k = 1..n`. -/
def doubledCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => Ctx.nil.cons (.typ lA .bot .top)
  | n + 1 => (doubledCtx n).cons
      (.and (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA))
            (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA)))

-- `x8.A <: {a : ⊤}` is false at every fuel, and the search ends unmarked.
example : rejects (sub? (doubledCtx 8) (chainTop 8) (.fld la .top)) 8188 = true := by decide +kernel

-- At ten and twelve links the search exceeds `defaultFuel`.
example : (sub? (doubledCtx 10) (chainTop 10) (.fld la .top)).2.out = true := by decide +kernel
example : (sub? (doubledCtx 12) (chainTop 12) (.fld la .top)).2.out = true := by decide +kernel

-- `x12.A <: x0.A` is true, since the first member is enough.
example : answers (sub? (doubledCtx 12) (chainTop 12) (chainBot 12)) 163 = true := by decide +kernel

end Frontend.Core
