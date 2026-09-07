import Coercions.Captures.FCdot.Checker
import Coercions.Captures.FCdot.Erasure
import Coercions.Captures.FCdot.Consistency
import Coercions.Captures.DotMNF.Examples
import Coercions.Captures.DotMNF.Erasure

namespace Captures

/-!
# FCdot examples

The mandatory examples of Plan III §10 (E1 to E7) and the acceptance test for
self-bound propositions (E8), as `FCdot` terms accepted by the structural
checker of `Coercions.FCdot.Checker`.  Each example comes with

* the term and its type, built from the type translation of §5.1;
* the checker's verdict on it;
* a typing derivation `Eᵢ_typed : Ctx.nil ⊢ Eᵢ : EᵢTy`;
* the erasure equation against the source term of `Coercions.DotMNF.Examples`,
  which is pinned to that file's derivation by a type ascription.  Both
  calculi erase into `Coercions.Runtime`, so the equation is an equality of
  `Runtime.Tm` and holds by `rfl`.

## The verdicts are decided in the kernel

Every verdict is stated as `checkTm … = true := by decide +kernel`, and the
typing derivation is read off it with `checkTm_sound`, so the checker is run
by the kernel.  (Plain `decide` is not enough: `synthTmCore` is compiled by
well-founded recursion over `Nat`, which the elaborator will not unfold but
the kernel will.)  E2 and E5 contain object literals; their derivations are
also built by hand from the rules, as a second, independent witness, with
`E2Tel_eq`/`E5Tel_eq` identifying the literal's telescope with
`Telescope.ofLiteral`.

## The type translation, concretely

```text
{A : S..T}   ↦  Obj(y. [ S ≤ y.A , y.A ≤ T ])          `telTyp`
{a : T}      ↦  Obj(y. [ has a , y.a ≤ T ])            `telFld`
S ∧ T        ↦  Obj(y. Tel_S ++ Tel_T)                 `Telescope.append`
x.A ∧ T      ↦  Obj(y. [⊑ x.A] ++ Tel_T)               a self-bound (E8)
μ(x. T)      ↦  Obj(x. Tel_T)                          (the literal's own type)
```

Indices into a telescope count from the oldest proposition, so `telTyp` offers
the lower bound at `0` and the upper bound at `1`, and `telFld` offers the
field declaration at `0`.

## What replaces subsumption

There is no subsumption rule, so every source `Sub` step is an explicit
`LeCo`, and every source `{}-E` is a `proj` carrying its own field-presence
proof.  Three idioms recur:

* `LeCo.member (.var x) (.refl X) i` — the `i`-th proposition of `x`'s own
  object type `X`, opened at `x`.  This is the `Var`-instance of §5.4 and it
  covers both `Sel-<:` and `<:-Sel`.
* `LeCo.member a e i` with `a` a *cast* atom — the same at a type reached
  through a bound.  This is what E4 needs.
* `EqCo.def x ℓ` — the definition of a transparent binder's block name,
  available only inside an object literal (E2, E5).  A field of a literal has
  type `self.ℓ`, and this is the only way to give it a useful one.

The source calculus has no base types, so `Int` and `Nat` are the two
unrelated closed types `{a : ⊤}` and `{b : ⊤}`, exactly as in
`Coercions.DotMNF.Examples`.
-/

namespace FCdot
namespace Examples

/-! ## Labels

The same labels as the source examples; the `rfl`s below pin them. -/

/-- Type label `A`. -/
def lA : Label := .typ 0
/-- Type label `B`. -/
def lB : Label := .typ 1
/-- Term label `a`. -/
def la : Label := .trm 0
/-- Term label `b`. -/
def lb : Label := .trm 1

example : lA = DotMNF.Examples.lA := rfl
example : lB = DotMNF.Examples.lB := rfl
example : la = DotMNF.Examples.la := rfl
example : lb = DotMNF.Examples.lb := rfl

/-- Type label `T`. -/
def lT : Label := .typ 2
/-- Term label `v`. -/
def lv : Label := .trm 2

example : lT = DotMNF.Examples.lT := rfl
example : lv = DotMNF.Examples.lv := rfl

/-! ## Pure types and pure evidence

Every type in this stage carries the empty capture set, so a shape `S` is
used as the type `S ^ []` (`Ty.pure`), and a shape inclusion `e` is used as
the type inclusion `.capt e (.refl [])` (`co`). -/

/-- A shape inclusion as an inclusion of pure types. -/
def co (e : ShapeCo s) : LeCo s := .capt e (.refl [])

/-! ## Type shapes -/

/-- `{A : S..T}` as a telescope over the self block: `[S ≤ y.A, y.A ≤ T]`. -/
def telTyp (A : Label) (S T : Shape s) : Telescope (s,x) :=
  .cons (.cons .nil (.le S↑ (.sel .here A))) (.le (.sel .here A) T↑)

/-- `{A : S..T}`.  Lower bound at index `0`, upper bound at index `1`. -/
def tTyp (A : Label) (S T : Shape s) : Shape s := .obj (telTyp A S T)

/-- `{a : T}` as a telescope over the self block: `[has a, y.a ≤ T]`. -/
def telFld (a : Label) (T : Shape s) : Telescope (s,x) :=
  .cons (.cons .nil (.has a)) (.le (.sel .here a) T↑)

/-- `{a : T}`.  Field declaration at index `0`, upper bound at index `1`. -/
def tFld (a : Label) (T : Shape s) : Shape s := .obj (telFld a T)

/-- `∀(y : x.A) x.A`, the self-referential arrow of E2 and E4. -/
def piSel (A : Label) (x : BVar s .var) : Shape s :=
  .pi (Ty.pure (.sel x A)) (Ty.pure (.sel (.there x) A))

/-- `Int`, i.e. `{a : ⊤}`. -/
def tInt : Shape s := tFld la .top
/-- `Nat`, i.e. `{b : ⊤}`; unrelated to `tInt`. -/
def tNat : Shape s := tFld lb .top

/-! ## E1: bad bounds under a lambda

`λ(x : {A : ⊤..⊥}). let y = (x : {B : Int..Int}) in y`.  The retyping is the
composite `{A : ⊤..⊥} ≤ ⊤ ≤ x.A ≤ ⊥ ≤ {B : Int..Int}`, whose two middle steps
are eliminations at `x` of its own telescope.  No `absurd` rule is involved:
`member` through the two bounds of a single block name is all it takes. -/

/-- `{A : ⊤..⊥}`: bad bounds. -/
def E1Dom : Shape s := tTyp lA .top .bot
/-- `{B : Int..Int}`, unrelated to `E1Dom`. -/
def E1Res : Shape s := tTyp lB tInt tInt

/-- Under `x : {A : ⊤..⊥}` every type is below every other. -/
def badBounds (x : BVar s .var) (T : Shape s) : LeCo s :=
  co (.trans (.top E1Dom)
    (.trans (.member (.var x) (.refl E1Dom) 0)
      (.trans (.member (.var x) (.refl E1Dom) 1) (.bot T))))

def E1Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque (Ty.pure E1Dom))

/-- The retyping alone, in the context of the lambda. -/
example : checkLe E1Ctx (badBounds .here E1Res) (Ty.pure E1Dom) (Ty.pure E1Res) = true := by
  decide +kernel

def E1 : Tm [] :=
  .val (.lam (Ty.pure E1Dom)
    (.let (.atom (.cast (.var .here) (badBounds .here E1Res))) (.atom (.var .here))))

def E1Ty : Ty [] := Ty.pure (.pi (Ty.pure E1Dom) (Ty.pure E1Res))

example : checkTm Ctx.nil E1 E1Ty = true := by decide +kernel

theorem E1_typed : Ctx.nil ⊢ E1 : E1Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E1`. -/
def E1src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E1Dom (.let (.path (.var .here)) (.path (.var .here))))

example : DotMNF.HasTy .nil E1src (.all DotMNF.Examples.E1Dom DotMNF.Examples.E1Res) :=
  DotMNF.Examples.E1

theorem E1_erase : E1.erase = E1src.erase := rfl

/-! ## E2: recursive object with a self-referential member

`ν(x. {A = ∀(y : x.A) x.A} ∧ {id = λ(y : x.A). y})`, allocated by a `let`, its
field selected and applied to itself.

Two things are specific to the target.  First, a field's type is its block
name `x.a`, so the literal must *define* `a` in its witnesses; the definition
entry `x.a ≃ ∀(y : x.A) x.A` is what lets the projected field be applied at
all (Plan III §12, risk 4).  Second, no `Rec` block is needed: the witness
`∀(y : self.A) self.A` mentions the self binder directly, and the literal's
precise type `Telescope.ofLiteral` binds it.  `unfoldSelf` is likewise
unnecessary, because `member` already opens the telescope at the atom's
root.

`Telescope.ofLiteral` does not reduce in the kernel (see the header), so the
literal's telescope is also given explicitly as `E2Tel`, the two are identified
by `E2Tel_eq`, and the typing derivation is built by hand instead of being
extracted from the checker. -/

/-- The witness of both members: `∀(y : self.A) self.A`. -/
def E2W : Shape (s,x) := piSel lA .here

/-- The literal's witnesses: `A` and `a` are both defined as `E2W`. -/
def E2Wit : Witnesses (s,x) := .cons (.cons .nil lA E2W) la E2W

/-- The field body `λ(y : self.A). y`, cast from its own arrow type to the
block name `self.a` by the definition of `a`. -/
def E2Field : Tm (s,x) :=
  .cast (.val (.lam (Ty.pure (.sel .here lA)) (.atom (.var .here))))
    (co (.eqToLe (.symm (.def .here la))))

def E2Fields : Fields (s,x) := .cons .nil la E2Field

/-- The literal's precise telescope: `[self.A ≃ E2W, self.a ≃ E2W, has a]`. -/
def E2Tel : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel .here lA) E2W)) (.eq (.sel .here la) E2W)) (.has la)

/-- `E2Tel` is what the literal generates. -/
theorem E2Tel_eq : Telescope.ofLiteral (E2Wit (s := s)) .nil [la] = E2Tel := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E2Wit, E2Tel, lA, la]

/-- The literal's precise type. -/
def E2Ty : Shape s := .obj E2Tel

example : checkValue Ctx.nil (.obj E2Wit .nil E2Fields) (Ty.pure E2Ty) = true := by decide +kernel

theorem E2_value {s : Sig} {Γ : Ctx s} : Γ ⊢ᵥ .obj E2Wit .nil E2Fields : Ty.pure E2Ty := by
  have h : Γ ⊢ᵥ .obj E2Wit .nil E2Fields : Ty.pure (.obj (Telescope.ofLiteral E2Wit .nil [la])) :=
    .obj (.cons .nil
      (.cast (.val (.lam (.atom .var))) (.capt (.eqToLe (.symm (.def rfl))) .refl)))
  rw [E2Tel_eq] at h
  exact h

/-- `x.a`, opened at the let-bound `x`. -/
def E2Has (x : BVar s .var) : Has s := .member (.var x) (.refl E2Ty) 2
/-- `x.a ≤ ∀(y : x.A) x.A`, from the definition of `a`. -/
def E2aPi (x : BVar s .var) : LeCo s := co (.eqToLe (.member (.var x) (.refl E2Ty) 1))
/-- `∀(y : x.A) x.A ≤ x.A`, from the exact bounds of `A`. -/
def E2piA (x : BVar s .var) : LeCo s := co (.eqToLe (.symm (.member (.var x) (.refl E2Ty) 0)))

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : Tm [] :=
  .let (.val (.obj E2Wit .nil E2Fields))
    (.let (.proj (.var .here) la (E2Has .here))
      (.cast
        (.app (.cast (.var .here) (E2aPi (.there .here)))
          (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
        (co (.top (.sel (.there .here) lA)))))

def E2Ty' : Ty [] := Ty.pure .top

example : checkTm Ctx.nil E2 E2Ty' = true := by decide +kernel
example : checkTm Ctx.nil E2 (Ty.pure .bot) = false := by decide +kernel

/-- After the outer `let`: `x : E2Ty`. -/
def E2Ctx1 : Ctx ([],x) := Ctx.nil.cons (.opaque (Ty.pure E2Ty))
/-- After the inner `let`: `x : E2Ty, f : x.a`. -/
def E2Ctx2 : Ctx ([],x,x) := E2Ctx1.cons (.opaque (Ty.pure (.sel .here la)))

/-- `f : x.a ≤ ∀(y : x.A) x.A`. -/
theorem E2_fun : Atom.HasType E2Ctx2 (.cast (.var .here) (E2aPi (.there .here)))
    (Ty.pure (piSel lA (.there .here))) :=
  .cast .var (.capt (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here))) .refl)

/-- `f : x.a ≤ ∀(y : x.A) x.A ≤ x.A`, so `f` is its own argument. -/
theorem E2_arg : Atom.HasType E2Ctx2
    (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here))))
    (Ty.pure (.sel (.there .here) lA)) :=
  .cast .var
    (LeCo.HasType.trans
      (.capt (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here))) .refl)
      (.capt (.eqToLe (.symm (.member (Tel := E2Tel) .var .refl (.there (.there .here)))))
        .refl))

/-- `f f : x.A`. -/
theorem E2_app : Tm.HasType E2Ctx2
    (.app (.cast (.var .here) (E2aPi (.there .here)))
      (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
    (Ty.pure (.sel (.there .here) lA)) :=
  .app E2_fun E2_arg

theorem E2_typed : Ctx.nil ⊢ E2 : E2Ty' :=
  .let (.val E2_value)
    (.let (.proj .var (.member (Tel := E2Tel) .var .refl .here))
      (.cast E2_app (.capt .top .refl)))

/-- The source term of `DotMNF.Examples.E2`. -/
def E2src : DotMNF.Tm [] :=
  .let (.val (.obj DotMNF.Examples.E2Defs))
    (.let (.proj .here DotMNF.Examples.la) (.app .here .here))

example : DotMNF.HasTy .nil E2src .top := DotMNF.Examples.E2

theorem E2_erase : E2.erase = E2src.erase := rfl

/-! ## E3: intersection with a shared member

`x : {A : ⊥..Int} ∧ {A : Nat..⊤}`, used at both bounds.  The intersection is
the concatenation of the two telescopes, so the two declarations of `A` are
two propositions about the *same* block name `x.A`: index `2` gives
`Nat ≤ x.A` and index `1` gives `x.A ≤ Int`.  Nothing in the target has to
know that the source wrote `∧`. -/

/-- `{A : ⊥..Int} ∧ {A : Nat..⊤}`. -/
def E3Dom : Shape s := .obj ((telTyp lA .bot tInt).append (telTyp lA tNat .top))

/-- `Nat ≤ x.A ≤ Int`: the shared member, used at both bounds. -/
def E3sub (x : BVar s .var) : LeCo s :=
  co (.trans (.member (.var x) (.refl E3Dom) 2) (.member (.var x) (.refl E3Dom) 1))

/-- `λ(x : {A : ⊥..Int} ∧ {A : Nat..⊤}). λ(z : Nat). let y = (z : Int) in y`. -/
def E3 : Tm [] :=
  .val (.lam (Ty.pure E3Dom)
    (.val (.lam (Ty.pure tNat)
      (.let (.atom (.cast (.var .here) (E3sub (.there .here)))) (.atom (.var .here))))))

def E3Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E3Dom) (Ty.pure (.pi (Ty.pure tNat) (Ty.pure tInt))))

example : checkTm Ctx.nil E3 E3Ty = true := by decide +kernel

theorem E3_typed : Ctx.nil ⊢ E3 : E3Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E3`. -/
def E3src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E3Dom
    (.val (.lam DotMNF.Examples.E3T2 (.let (.path (.var .here)) (.path (.var .here))))))

example : DotMNF.HasTy .nil E3src
    (.all DotMNF.Examples.E3Dom (.all DotMNF.Examples.E3T2 DotMNF.Examples.E3T1)) :=
  DotMNF.Examples.E3

theorem E3_erase : E3.erase = E3src.erase := rfl

/-! ## E4: the counterexample of §1

`λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`, with
`S = {A : ⊥..⊤}` and `T = {A : Int..⊤}`.

This is the acceptance test.  The step `S ≤ x.B ≤ T` has no realizer, so `w`'s
view of its own member `A` is not the one its binding gives; the target reaches
`Int ≤ w.A` by eliminating at the *cast* atom `w ▹ (S ≤ T)`, which is the
general form of §5.4 and the reason `member` takes an arbitrary inclusion
rather than a context lookup. -/

/-- `S = {A : ⊥..⊤}`. -/
def E4S : Shape s := tTyp lA .bot .top
/-- `T = {A : Int..⊤}`. -/
def E4T : Shape s := tTyp lA tInt .top
/-- `{B : S..T}`. -/
def E4X : Shape s := tTyp lB E4S E4T

/-- `S ≤ x.B ≤ T`, the step with no realizer. -/
def E4ST (x : BVar s .var) : LeCo s :=
  co (.trans (.member (.var x) (.refl E4X) 0) (.member (.var x) (.refl E4X) 1))

/-- `w` at `T`: an atom, so that its members can be eliminated. -/
def E4wT (x w : BVar s .var) : Atom s := .cast (.var w) (E4ST x)

/-- `Int ≤ w.A`, by elimination at the cast atom. -/
def E4IntLe (x w : BVar s .var) : LeCo s := co (.member (E4wT x w) (.refl E4T) 0)

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : Tm [] :=
  .val (.lam (Ty.pure E4X) (.val (.lam (Ty.pure E4S) (.val (.lam (Ty.pure tInt)
    (.let (.val (.lam (Ty.pure (.sel (.there .here) lA)) (.atom (.var .here))))
      (.app (.var .here)
        (.cast (.var (.there .here))
          (E4IntLe (.there (.there (.there .here))) (.there (.there .here)))))))))))

def E4Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E4X) (Ty.pure (.pi (Ty.pure E4S)
    (Ty.pure (.pi (Ty.pure tInt) (Ty.pure (.sel (.there .here) lA)))))))

example : checkTm Ctx.nil E4 E4Ty = true := by decide +kernel

theorem E4_typed : Ctx.nil ⊢ E4 : E4Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E4`. -/
def E4src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E4X (.val (.lam DotMNF.Examples.E4S (.val (.lam DotMNF.Examples.E4Int
    (.let (.val (.lam (.sel (.var (.there .here)) DotMNF.Examples.lA) (.path (.var .here))))
      (.app .here (.there .here))))))))

example : DotMNF.HasTy .nil E4src
    (.all DotMNF.Examples.E4X (.all DotMNF.Examples.E4S (.all DotMNF.Examples.E4Int
      (.sel (.var (.there .here)) DotMNF.Examples.lA)))) :=
  DotMNF.Examples.E4

theorem E4_erase : E4.erase = E4src.erase := rfl

/-! ## E5: an object returned from a function and selected after a `let`

`λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z. {a = v}) in
 let o = f w in o.a`.

`App` renames the parameter's block to the argument's root, so `f w` has type
`Obj(z. [z.a ≃ w.A, has a])`; `proj` gives the abstract `o.a`, which the
definition entry of that telescope converts to `w.A` before the `let` closes
over `o`.  Both `Let`s therefore return a type mentioning neither binder.

As in E2, the literal's telescope is given explicitly (`E5Tel`) because
`Telescope.ofLiteral` does not reduce in the kernel (see the header). -/

/-- `{A : ⊤..⊤}`. -/
def E5AT : Shape s := tTyp lA .top .top

/-- Witnesses of `ν(z. {a = v})`: the single field is defined as `v.A`. -/
def E5Wit (v : BVar s .var) : Witnesses (s,x) := .cons .nil la (.sel (.there v) lA)

/-- `[z.a ≃ v.A, has a]`, the telescope of `ν(z. {a = v})`. -/
def E5Tel (v : BVar s .var) : Telescope (s,x) :=
  .cons (.cons .nil (.eq (.sel .here la) (.sel (.there v) lA))) (.has la)

theorem E5Tel_eq (v : BVar s .var) : Telescope.ofLiteral (E5Wit v) .nil [la] = E5Tel v := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E5Wit, E5Tel]

/-- `Obj(z. [z.a ≃ v.A, has a])`, the type of `ν(z. {a = v})`. -/
def E5ObjTy (v : BVar s .var) : Shape s := .obj (E5Tel v)

/-- The field body: `v : {A : ⊤..⊤} ≤ ⊤ ≤ v.A ≃ z.a`. -/
def E5Field : Tm (s,x,x) :=
  .atom (.cast (.var (.there .here))
    (co (.trans (.top E5AT)
      (.trans (.member (.var (.there .here)) (.refl E5AT) 0)
        (.eqToLe (.symm (.def .here la)))))))

def E5Fields : Fields (s,x,x) := .cons .nil la E5Field

/-- `λ(w : {A : ⊤..⊤}). let f = … in let o = f w in (o.a : w.A)`. -/
def E5 : Tm [] :=
  .val (.lam (Ty.pure E5AT)
    (.let (.val (.lam (Ty.pure E5AT) (.val (.obj (E5Wit .here) .nil E5Fields))))
      (.let (.app (.var .here) (.var (.there .here)))
        (.cast
          (.proj (.var .here) la
            (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))
          (co (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0)))))))

def E5Ty : Ty [] := Ty.pure (.pi (Ty.pure E5AT) (Ty.pure (.sel .here lA)))

example : checkTm Ctx.nil E5 E5Ty = true := by decide +kernel
example : checkTm Ctx.nil E5 (Ty.pure (.pi (Ty.pure E5AT) (Ty.pure .top))) = false := by
  decide +kernel

/-- `w : {A : ⊤..⊤}, v : {A : ⊤..⊤}`, the context of the object literal. -/
def E5Ctxv : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque (Ty.pure E5AT))).cons (.opaque (Ty.pure E5AT))

theorem E5_value : E5Ctxv ⊢ᵥ .obj (E5Wit .here) .nil E5Fields : Ty.pure (E5ObjTy .here) := by
  have h : Value.HasType E5Ctxv (.obj (E5Wit .here) .nil E5Fields)
      (Ty.pure (.obj (Telescope.ofLiteral (E5Wit .here) .nil [la]))) :=
    .obj
      (.cons .nil
        (.atom (.cast .var
          (.capt (.trans .top
            (.trans (.member (Tel := telTyp lA .top .top) .var .refl (.there .here))
              (.eqToLe (.symm (.def rfl))))) .refl))))
  rw [E5Tel_eq] at h
  exact h

/-- `w : {A : ⊤..⊤}, f : ∀(v : {A : ⊤..⊤}) Obj(z. [z.a ≃ v.A, has a])`. -/
def E5Ctxf : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque (Ty.pure E5AT))).cons
    (.opaque (Ty.pure (.pi (Ty.pure E5AT) (Ty.pure (E5ObjTy .here)))))

/-- `f`, at its declared type. -/
theorem E5_f : E5Ctxf ⊢ₐ .var .here :
    Ty.pure (.pi (Ty.pure E5AT) (Ty.pure (E5ObjTy .here))) := .var

/-- `f w : Obj(z. [z.a ≃ w.A, has a])`: the application renames `v`'s block. -/
theorem E5_app : Tm.HasType E5Ctxf (.app (.var .here) (.var (.there .here)))
    (Ty.pure (E5ObjTy (.there .here))) :=
  .app E5_f .var

/-- `w : …, f : …, o : Obj(z. [z.a ≃ w.A, has a])`. -/
def E5Ctxo : Ctx ([],x,x,x) := E5Ctxf.cons (.opaque (Ty.pure (E5ObjTy (.there .here))))

/-- `o.a`, then `o.a ≃ w.A`: the result mentions neither `let` binder. -/
theorem E5_proj : Tm.HasType E5Ctxo
    (.cast
      (.proj (.var .here) la (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))
      (co (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0))))
    (Ty.pure (.sel (.there (.there .here)) lA)) :=
  .cast (.proj .var (.member (Tel := E5Tel (.there (.there .here))) .var .refl .here))
    (.capt (.eqToLe (.member (Tel := E5Tel (.there (.there .here))) .var .refl (.there .here)))
      .refl)

theorem E5_typed : Ctx.nil ⊢ E5 : E5Ty :=
  .val (.lam (.let (.val (.lam (.val E5_value))) (.let E5_app E5_proj)))

/-- The source term of `DotMNF.Examples.E5`. -/
def E5src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E5AT
    (.let (.val (.lam DotMNF.Examples.E5AT DotMNF.Examples.E5Obj))
      (.let (.app .here (.there .here)) (.proj .here DotMNF.Examples.la))))

example : DotMNF.HasTy .nil E5src
    (.all DotMNF.Examples.E5AT (.sel (.var .here) DotMNF.Examples.lA)) :=
  DotMNF.Examples.E5

theorem E5_erase : E5.erase = E5src.erase := rfl

/-! ## E6: a field typed at its own literal's type member

`ν(x. {T = Int} ∧ {v = n})` with `n : Int` from the enclosing scope,
matching `DotMNF.Examples.E6`.  The field `v`'s witness is `self.T`, a bare
selection on the object's own self: previously forbidden by the self-alias
restriction on witnesses, now checked directly. -/

/-- The witnesses: `T ↦ Int`, `v ↦ self.T` (a same-block alias). -/
def E6Wit : Witnesses (s,x) := .cons (.cons .nil lT tInt) lv (.sel .here lT)

/-- The field body: `n` (from the enclosing scope), cast from `Int` to `self.T`
by the definition of `T`, then from `self.T` to the block name `self.v` by
the definition of `v`. -/
def E6Field : Tm (s,x,x) :=
  .atom (.cast
    (.cast (.var (.there .here)) (co (.eqToLe (.symm (.def .here lT)))))
    (co (.eqToLe (.symm (.def .here lv)))))

def E6Fields : Fields (s,x,x) := .cons .nil lv E6Field

/-- The literal's precise telescope: `[self.T ≃ Int, self.v ≃ self.T, has v]`. -/
def E6Tel : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel .here lT) tInt)) (.eq (.sel .here lv) (.sel .here lT)))
    (.has lv)

/-- `E6Tel` is what the literal generates. -/
theorem E6Tel_eq : Telescope.ofLiteral (E6Wit (s := s)) .nil [lv] = E6Tel := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E6Wit, E6Tel, lT, lv]

/-- The literal's precise type. -/
def E6Ty : Shape s := .obj E6Tel

/-- `n : Int` in scope. -/
def E6Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque (Ty.pure tInt))

example : checkValue E6Ctx (.obj E6Wit .nil E6Fields) (Ty.pure E6Ty) = true := by decide +kernel

theorem E6_value {s : Sig} {Γ : Ctx s} :
    (Γ.cons (.opaque (Ty.pure tInt))) ⊢ᵥ .obj E6Wit .nil E6Fields : Ty.pure E6Ty := by
  have h : (Γ.cons (.opaque (Ty.pure tInt))) ⊢ᵥ .obj E6Wit .nil E6Fields :
      Ty.pure (.obj (Telescope.ofLiteral E6Wit .nil [lv])) :=
    .obj (.cons .nil
      (.atom (.cast (.cast .var (.capt (.eqToLe (.symm (.def rfl))) .refl))
        (.capt (.eqToLe (.symm (.def rfl))) .refl))))
  rw [E6Tel_eq] at h
  exact h

/-! ## E7: a two-element alias cycle

`ν(x. {A = x.B} ∧ {B = x.A})`, matching `DotMNF.Examples.E7`.  Both
witnesses are bare selections on the object's own self, each other's alias:
a shape the self-alias restriction used to rule out entirely, admitted now
because alias-tolerant resolution follows a same-block alias to whatever it
names, cycles included (a cyclic alias resolves to `⊤`). -/

/-- The witnesses: `A ↦ self.B`, `B ↦ self.A`. -/
def E7Wit : Witnesses (s,x) := .cons (.cons .nil lA (.sel .here lB)) lB (.sel .here lA)

/-- The literal's precise telescope: `[self.A ≃ self.B, self.B ≃ self.A]`, no fields. -/
def E7Tel : Telescope (s,x) :=
  .cons (.cons .nil (.eq (.sel .here lA) (.sel .here lB))) (.eq (.sel .here lB) (.sel .here lA))

/-- `E7Tel` is what the literal generates. -/
theorem E7Tel_eq : Telescope.ofLiteral (E7Wit (s := s)) .nil [] = E7Tel := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E7Wit, E7Tel, lA, lB]

/-- The literal's precise type. -/
def E7Ty : Shape s := .obj E7Tel

example : checkValue Ctx.nil (.obj E7Wit .nil .nil) (Ty.pure E7Ty) = true := by decide +kernel

theorem E7_value {s : Sig} {Γ : Ctx s} : Γ ⊢ᵥ .obj E7Wit .nil .nil : Ty.pure E7Ty := by
  have h : Γ ⊢ᵥ .obj E7Wit .nil .nil :
      Ty.pure (.obj (Telescope.ofLiteral E7Wit .nil [])) := .obj .nil
  rw [E7Tel_eq] at h
  exact h

/-! ## E8: refining an abstract type

`λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`, matching
`DotMNF.Examples.E8`.  This is the acceptance test for self-bound
propositions: `x.A` is a type selection, not a declaration, so the
intersection `x.A ∧ {a : ⊤}` translates to the telescope

```text
[ ⊑ x.A , has a , y.a ≤ ⊤ ]
```

whose first proposition is the self-bound `⊑ x.A` -- "the object itself is
included in `x.A`".  The two source derivations of `y.a` translate to two
different pieces of evidence:

* `E8`: `And₂` first, an object coercion copying the two propositions of
  `{a : ⊤}` at offset `1`, then `{}-E`;
* `E8b`: `And₁` first -- the bound cast `LeCo.bound … 0` -- then `Sel-<:`,
  i.e. the upper bound of `x`'s member `A`, then `{}-E`.

`E8_both` is the `And-I` direction: from `y : x.A` and `y : {a : ⊤}` the
atom `Atom.both` recovers `y`'s own type, the non-declaration operand being
re-wrapped by `LeCo.intoBnd`. -/

/-- `{A : ⊥..{a : ⊤}}`, the bound of the abstract type. -/
def E8X : Shape s := tTyp lA .bot (tFld la .top)

/-- `x.A ∧ {a : ⊤}` as a telescope: a single self-bound, then `{a : ⊤}`. -/
def E8YTel (x : BVar s .var) : Telescope (s,x) :=
  (Telescope.nil.cons (⊑ (Shape.sel x lA)↑)).append (telFld la .top)

/-- `x.A ∧ {a : ⊤}`.  Self-bound at index `0`, field declaration at `1`,
field upper bound at `2`. -/
def E8Y (x : BVar s .var) : Shape s := .obj (E8YTel x)

/-- `And₂`: the identity morphism onto the second operand, at offset `1`. -/
def E8And2 (x : BVar s .var) : ShapeCo s :=
  .obj (E8YTel x) (.le (.has .nil 1) .none (.le 2) .none)

/-- `And₁` then `Sel-<:`: through the self-bound to `x.A`, then to `{a : ⊤}`
by the upper bound of `x`'s member `A`. -/
def E8Sel (x : BVar s .var) : ShapeCo s :=
  .trans (.bound (E8YTel x) 0) (.member (.var x) (.refl E8X) 1)

/-- `λ(x). λ(y). y.a`, the `And₂` derivation. -/
def E8 : Tm [] :=
  .val (.lam (Ty.pure E8X)
    (.val (.lam (Ty.pure (E8Y .here))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8And2 (.there .here)) 0))
        (co (.top (.sel .here la)))))))

/-- `λ(x). λ(y). y.a`, the `And₁`-then-`Sel-<:` derivation: the same term
after erasure. -/
def E8b : Tm [] :=
  .val (.lam (Ty.pure E8X)
    (.val (.lam (Ty.pure (E8Y .here))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8Sel (.there .here)) 0))
        (co (.top (.sel .here la)))))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) ⊤`. -/
def E8Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E8X) (Ty.pure (.pi (Ty.pure (E8Y .here)) (Ty.pure .top))))

example : checkTm Ctx.nil E8 E8Ty = true := by decide +kernel

theorem E8_typed : Ctx.nil ⊢ E8 : E8Ty := checkTm_sound (by decide +kernel)

example : checkTm Ctx.nil E8b E8Ty = true := by decide +kernel

theorem E8b_typed : Ctx.nil ⊢ E8b : E8Ty := checkTm_sound (by decide +kernel)

/-- The two derivations erase to the same runtime term. -/
theorem E8b_erase_E8 : E8b.erase = E8.erase := rfl

/-- `λ(x). λ(y). y.a` in the source calculus. -/
def E8src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E8Dom
    (.val (.lam (DotMNF.Examples.E8Ref .here) (.proj .here DotMNF.Examples.la))))

example : DotMNF.HasTy .nil E8src
    (.all DotMNF.Examples.E8Dom (.all (DotMNF.Examples.E8Ref .here) .top)) :=
  DotMNF.Examples.E8

example : DotMNF.HasTy .nil E8src
    (.all DotMNF.Examples.E8Dom (.all (DotMNF.Examples.E8Ref .here) .top)) :=
  DotMNF.Examples.E8b

theorem E8_erase : E8.erase = E8src.erase := rfl

theorem E8b_erase : E8b.erase = E8src.erase := rfl

/-! ### `And-I`

`y : x.A` and `y : {a : ⊤}` give back `y : x.A ∧ {a : ⊤}`: an atom, not a
closed program. -/

/-- `x : {A : ⊥..{a : ⊤}}, y : x.A ∧ {a : ⊤}`. -/
def E8Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque (Ty.pure E8X))).cons (.opaque (Ty.pure (E8Y .here)))

/-- `And-I`: the two views of `y` recombined.  The non-declaration operand
is re-wrapped by `intoBnd`, the declaration operand is used as it is. -/
theorem E8_both : E8Ctx ⊢ₐ
    (.both (Telescope.nil.cons (⊑ (Shape.sel (.there .here) lA)↑)) (telFld la .top)
      (.cast (.cast (.var .here) (co (.bound (E8YTel (.there .here)) 0)))
        (co (.intoBnd (.refl (.sel (.there .here) lA)))))
      (.cast (.var .here) (co (E8And2 (.there .here))))) :
    Ty.pure (E8Y (.there .here)) :=
  .both
    (.cast (.cast .var
        (.capt (.bound (Tel := E8YTel (.there .here)) (.there (.there .here))) .refl))
      (.capt (.intoBnd .refl) .refl))
    (.cast .var (.capt (.obj (.le (.has .nil (.there .here)) .here .none .none)) .refl))
    rfl

/-! ## C3: bad capture bounds under a lambda

`λ(x : μ(y. [{κ} ⊑ᶜ {}])). λ(z : □(⊤ ^ {κ})). unbox z ⦃member x⦄`, over the
platform prefix `κ ⊑ᶜ ∗`.  The domain of the outer lambda declares that the
platform capability is below the empty set -- inverted capture bounds, the
capture-sort twin of E1's `{A : ⊤..⊥}` -- and one `member` in the capture
sort turns that declaration into the evidence an `unbox` needs, stripping
`{κ}` off a boxed value.  The term is well typed, as E1's is; and, as in E1,
no store realises the binder: `Store.Typed.no_cap_star_le_nil` says that over
a typed store no closed capture evidence puts `{κ}` below the empty set. -/

/-- `μ(y. [{κ} ⊑ᶜ {}])`: inverted capture bounds. -/
def capBad (κ : BVar s .cap) : Shape s :=
  .obj (.cons .nil (.leC [CapAtom.cvar (.there κ)] []))

/-- `□(⊤ ^ {κ})`: a boxed value that captures the platform capability. -/
def boxCap (κ : BVar s .cap) : Shape s := .box ((⊤ : Shape s) ^ [CapAtom.cvar κ])

/-- Under `x : μ(y. [{κ} ⊑ᶜ {}])`, `{κ} ⊑ {}`: one `member` in the capture
sort, instantiated at the root `x`. -/
def badCapBounds (x : BVar s .var) (κ : BVar s .cap) : CapCo s :=
  .member (.var x) (.refl (capBad κ)) 0

/-- The platform prefix: one capture binder bounded by `∗`. -/
def C3Ctx0 : Ctx ([],c) := Ctx.nil.consC .star

/-- The context inside the two lambdas: `κ ⊑ᶜ ∗, x : μ(y. [{κ} ⊑ᶜ {}]),
z : □(⊤ ^ {κ})`. -/
def C3Ctx : Ctx ([],c,x,x) :=
  (C3Ctx0.cons (.opaque (Ty.pure (capBad .here)))).cons
    (.opaque (Ty.pure (boxCap (.there .here))))

/-- The bad capture bound, in the context of the two lambdas. -/
example :
    checkCap C3Ctx (badCapBounds (.there .here) (.there (.there .here)))
      [CapAtom.cvar (.there (.there .here))] [] = true := by
  decide +kernel

theorem C3_badBounds : C3Ctx ⊢ᶜ badCapBounds (.there .here) (.there (.there .here)) :
    [CapAtom.cvar (.there (.there .here))] ⊑ [] :=
  checkCap_sound (by decide +kernel)

def C3 : Tm ([],c) :=
  .val (.lam (Ty.pure (capBad .here))
    (.val (.lam (Ty.pure (boxCap (.there .here)))
      (.unbox (.var .here) (badCapBounds (.there .here) (.there (.there .here)))))))

def C3Ty : Ty ([],c) :=
  Ty.pure (.pi (Ty.pure (capBad .here))
    (Ty.pure (.pi (Ty.pure (boxCap (.there .here)))
      ((⊤ : Shape ([],c,x,x)) ^ [CapAtom.cvar (.there (.there .here))]))))

example : checkTm C3Ctx0 C3 C3Ty = true := by decide +kernel

theorem C3_typed : C3Ctx0 ⊢ C3 : C3Ty := checkTm_sound (by decide +kernel)

/-- The consistency corollary: over a typed store, a capture binder bounded
by `∗` never sinks to the empty set, so no store realises the domain of the
outer lambda. -/
theorem C3_no_store {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    {κ : BVar s .cap} (hκ : Γ.lookupCap κ = .star) :
    ¬ ∃ f : CapCo s, Γ ⊢ᶜ f : [CapAtom.cvar κ] ⊑ [] :=
  hσ.no_cap_star_le_nil hκ

/-! ## C4: `sc-var` at a cast atom

`capvar` reads the capture set of an atom's *type* and concludes about the
atom's *root*; `member` in the capture sort instantiates a telescope entry at
the same root.  Both fire at a wrapped atom -- a `recap` under a `cast` --
and they agree, because every wrapper keeps the root (plan-5a §2.3).  This is
the example the design correction of the stage makes true: with `box` and
`unbox` moved to the value and term sorts, no atom's capture set can disagree
with its root. -/

/-- `μ(y. [{y} ⊑ᶜ {κ}])`: the self's own capability is below `κ`. -/
def C4Dom (κ : BVar s .cap) : Shape s :=
  .obj (.cons .nil (.leC [CapAtom.var .here] [CapAtom.cvar (.there κ)]))

/-- `κ ⊑ᶜ ∗, x : μ(y. [{y} ⊑ᶜ {κ}]) ^ {κ}`. -/
def C4Ctx : Ctx ([],c,x) :=
  C3Ctx0.cons (.opaque (C4Dom .here ^ [CapAtom.cvar .here]))

/-- The atom: `x` recaptured at its own capability, then cast by the identity
inclusion.  Its root is still `x`. -/
def C4Atom : Atom ([],c,x) :=
  .cast (.recap (.var .here) (.refl [CapAtom.var .here]))
    (.capt (.refl (C4Dom (.there .here))) (.refl [CapAtom.var .here]))

/-- `sc-var` at the wrapped atom: its root is below the capture set of its
type. -/
example :
    checkCap C4Ctx (.capvar C4Atom) [CapAtom.var .here] [CapAtom.var .here] = true := by
  decide +kernel

theorem C4_capvar :
    C4Ctx ⊢ᶜ .capvar C4Atom : [CapAtom.var .here] ⊑ [CapAtom.var .here] :=
  checkCap_sound (by decide +kernel)

/-- `member` in the capture sort at the same atom, instantiated at the same
root: `{x} ⊑ {κ}`. -/
example :
    checkCap C4Ctx (.member C4Atom (.refl (C4Dom (.there .here))) 0)
      [CapAtom.var .here] [CapAtom.cvar (.there .here)] = true := by
  decide +kernel

theorem C4_member :
    C4Ctx ⊢ᶜ .member C4Atom (.refl (C4Dom (.there .here))) 0 :
      [CapAtom.var .here] ⊑ [CapAtom.cvar (.there .here)] :=
  checkCap_sound (by decide +kernel)

end Examples
end FCdot

end Captures
