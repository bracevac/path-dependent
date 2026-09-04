import Coercions.FCdot.Checker
import Coercions.FCdot.Erasure
import Coercions.DotMNF.Examples
import Coercions.DotMNF.Erasure

/-!
# FCdot examples

The five mandatory examples of Plan III §10, as `FCdot` terms accepted by the
structural checker of `Coercions.FCdot.Checker`.  Each example comes with

* the term and its type, built from the type translation of §5.1;
* the checker's verdict on it;
* a typing derivation `Eᵢ_typed : Tm.HasType Ctx.nil Eᵢ EᵢTy`;
* the erasure equation against the source term of `Coercions.DotMNF.Examples`,
  which is pinned to that file's derivation by a type ascription.  Both
  calculi erase into `Coercions.Runtime`, so the equation is an equality of
  `Runtime.Tm` and holds by `rfl`.

## `decide` and the two examples that use object literals

E1, E3 and E4 state the verdict as `checkTm … = true := by decide +kernel`
and read the derivation off it with `checkTm_sound`, so the checker is run by
the kernel.  (Plain `decide` is not enough: `synthTmCore` is compiled by
well-founded recursion and the *elaborator* will not unfold it, while the
kernel will.)

E2 and E5 contain object literals, and for those the kernel gets stuck, on a
definition rather than on the size of the computation: `Witnesses.eqEntriesOf`
(`Syntax.lean`) recurses on `Witnesses (s,x)`, whose family index is not a
variable, so Lean cannot compile it structurally and falls back to
`WellFounded.fix` over `sizeOfWFRel`, whose `Acc.rec` does not reduce.  (The
checker's own kernels are also well-founded, but over `Nat`, and
`WellFounded.Nat.fix` does reduce — which is why E1, E3 and E4 go through.)
Every literal's type goes through `Telescope.ofLiteral` and hence through
`eqEntriesOf`, so even `ν(z. ∅)` is out of reach of `decide`.  For those two examples the verdict is therefore a `#guard` (which
runs the compiled checker) and the typing derivation is built by hand from the
rules, with `E2Tel_eq`/`E5Tel_eq` — proved by `simp` from the equation lemmas —
supplying the one step the kernel cannot take.  Generalising
`Witnesses.eqEntriesOf` to `Witnesses s'` (as `Witnesses.all` already is) would
make it structural and put E2 and E5 within reach of `decide` too.

## The type translation, concretely

```text
{A : S..T}   ↦  Obj(y. [ S ≤ y.A , y.A ≤ T ])          `telTyp`
{a : T}      ↦  Obj(y. [ has a , y.a ≤ T ])            `telFld`
S ∧ T        ↦  Obj(y. Tel_S ++ Tel_T)                 `Telescope.append`
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

/-! ## Type shapes -/

/-- `{A : S..T}` as a telescope over the self block: `[S ≤ y.A, y.A ≤ T]`. -/
def telTyp (A : Label) (S T : Ty s) : Telescope (s,x) :=
  .cons (.cons .nil (.le S.weaken (.sel .here A))) (.le (.sel .here A) T.weaken)

/-- `{A : S..T}`.  Lower bound at index `0`, upper bound at index `1`. -/
def tTyp (A : Label) (S T : Ty s) : Ty s := .obj (telTyp A S T)

/-- `{a : T}` as a telescope over the self block: `[has a, y.a ≤ T]`. -/
def telFld (a : Label) (T : Ty s) : Telescope (s,x) :=
  .cons (.cons .nil (.has a)) (.le (.sel .here a) T.weaken)

/-- `{a : T}`.  Field declaration at index `0`, upper bound at index `1`. -/
def tFld (a : Label) (T : Ty s) : Ty s := .obj (telFld a T)

/-- `∀(y : x.A) x.A`, the self-referential arrow of E2 and E4. -/
def piSel (A : Label) (x : BVar s .var) : Ty s := .pi (.sel x A) (.sel (.there x) A)

/-- `Int`, i.e. `{a : ⊤}`. -/
def tInt : Ty s := tFld la .top
/-- `Nat`, i.e. `{b : ⊤}`; unrelated to `tInt`. -/
def tNat : Ty s := tFld lb .top

/-! ## E1: bad bounds under a lambda

`λ(x : {A : ⊤..⊥}). let y = (x : {B : Int..Int}) in y`.  The retyping is the
composite `{A : ⊤..⊥} ≤ ⊤ ≤ x.A ≤ ⊥ ≤ {B : Int..Int}`, whose two middle steps
are eliminations at `x` of its own telescope.  No `absurd` rule is involved:
`member` through the two bounds of a single block name is all it takes. -/

/-- `{A : ⊤..⊥}`: bad bounds. -/
def E1Dom : Ty s := tTyp lA .top .bot
/-- `{B : Int..Int}`, unrelated to `E1Dom`. -/
def E1Res : Ty s := tTyp lB tInt tInt

/-- Under `x : {A : ⊤..⊥}` every type is below every other. -/
def badBounds (x : BVar s .var) (T : Ty s) : LeCo s :=
  .trans (.top E1Dom)
    (.trans (.member (.var x) (.refl E1Dom) 0)
      (.trans (.member (.var x) (.refl E1Dom) 1) (.bot T)))

def E1Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque E1Dom)

/-- The retyping alone, in the context of the lambda. -/
example : checkLe E1Ctx (badBounds .here E1Res) E1Dom E1Res = true := by decide +kernel

def E1 : Tm [] :=
  .val (.lam E1Dom
    (.let (.atom (.cast (.var .here) (badBounds .here E1Res))) (.atom (.var .here))))

def E1Ty : Ty [] := .pi E1Dom E1Res

example : checkTm Ctx.nil E1 E1Ty = true := by decide +kernel

theorem E1_typed : Tm.HasType Ctx.nil E1 E1Ty := checkTm_sound (by decide +kernel)

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
def E2W : Ty (s,x) := piSel lA .here

/-- The literal's witnesses: `A` and `a` are both defined as `E2W`. -/
def E2Wit : Witnesses (s,x) := .cons (.cons .nil lA E2W) la E2W

/-- The field body `λ(y : self.A). y`, cast from its own arrow type to the
block name `self.a` by the definition of `a`. -/
def E2Field : Tm (s,x) :=
  .cast (.val (.lam (.sel .here lA) (.atom (.var .here))))
    (.eqToLe (.symm (.def .here la)))

def E2Fields : Fields (s,x) := .cons .nil la E2Field

/-- The literal's precise telescope: `[self.A ≃ E2W, self.a ≃ E2W, has a]`. -/
def E2Tel : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel .here lA) E2W)) (.eq (.sel .here la) E2W)) (.has la)

/-- `E2Tel` is what the literal generates. -/
theorem E2Tel_eq : Telescope.ofLiteral (E2Wit (s := s)) [la] = E2Tel := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E2Wit, E2Tel, lA, la]

/-- The literal's precise type. -/
def E2Ty : Ty s := .obj E2Tel

#guard checkValue Ctx.nil (.obj E2Wit E2Fields) E2Ty

theorem E2_value {s : Sig} {Γ : Ctx s} : Value.HasType Γ (.obj E2Wit E2Fields) E2Ty := by
  have h : Value.HasType Γ (.obj E2Wit E2Fields) (.obj (Telescope.ofLiteral E2Wit [la])) :=
    .obj rfl (.cons .nil (.cast (.val (.lam (.atom .var))) (.eqToLe (.symm (.def rfl)))))
  rw [E2Tel_eq] at h
  exact h

/-- `x.a`, opened at the let-bound `x`. -/
def E2Has (x : BVar s .var) : Has s := .member (.var x) (.refl E2Ty) 2
/-- `x.a ≤ ∀(y : x.A) x.A`, from the definition of `a`. -/
def E2aPi (x : BVar s .var) : LeCo s := .eqToLe (.member (.var x) (.refl E2Ty) 1)
/-- `∀(y : x.A) x.A ≤ x.A`, from the exact bounds of `A`. -/
def E2piA (x : BVar s .var) : LeCo s := .eqToLe (.symm (.member (.var x) (.refl E2Ty) 0))

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : Tm [] :=
  .let (.val (.obj E2Wit E2Fields))
    (.let (.proj (.var .here) la (E2Has .here))
      (.cast
        (.app (.cast (.var .here) (E2aPi (.there .here)))
          (.cast (.var .here) (.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
        (.top (.sel (.there .here) lA))))

def E2Ty' : Ty [] := .top

#guard checkTm Ctx.nil E2 E2Ty'
#guard !checkTm Ctx.nil E2 .bot

/-- After the outer `let`: `x : E2Ty`. -/
def E2Ctx1 : Ctx ([],x) := Ctx.nil.cons (.opaque E2Ty)
/-- After the inner `let`: `x : E2Ty, f : x.a`. -/
def E2Ctx2 : Ctx ([],x,x) := E2Ctx1.cons (.opaque (.sel .here la))

/-- `f : x.a ≤ ∀(y : x.A) x.A`. -/
theorem E2_fun : Atom.HasType E2Ctx2 (.cast (.var .here) (E2aPi (.there .here)))
    (piSel lA (.there .here)) :=
  .cast .var (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here)))

/-- `f : x.a ≤ ∀(y : x.A) x.A ≤ x.A`, so `f` is its own argument. -/
theorem E2_arg : Atom.HasType E2Ctx2
    (.cast (.var .here) (.trans (E2aPi (.there .here)) (E2piA (.there .here))))
    (.sel (.there .here) lA) :=
  .cast .var
    (.trans (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here)))
      (.eqToLe (.symm (.member (Tel := E2Tel) .var .refl (.there (.there .here))))))

/-- `f f : x.A`. -/
theorem E2_app : Tm.HasType E2Ctx2
    (.app (.cast (.var .here) (E2aPi (.there .here)))
      (.cast (.var .here) (.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
    (.sel (.there .here) lA) :=
  .app E2_fun E2_arg

theorem E2_typed : Tm.HasType Ctx.nil E2 E2Ty' :=
  .let (.val E2_value)
    (.let (.proj .var (.member (Tel := E2Tel) .var .refl .here)) (.cast E2_app .top))

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
def E3Dom : Ty s := .obj ((telTyp lA .bot tInt).append (telTyp lA tNat .top))

/-- `Nat ≤ x.A ≤ Int`: the shared member, used at both bounds. -/
def E3sub (x : BVar s .var) : LeCo s :=
  .trans (.member (.var x) (.refl E3Dom) 2) (.member (.var x) (.refl E3Dom) 1)

/-- `λ(x : {A : ⊥..Int} ∧ {A : Nat..⊤}). λ(z : Nat). let y = (z : Int) in y`. -/
def E3 : Tm [] :=
  .val (.lam E3Dom
    (.val (.lam tNat
      (.let (.atom (.cast (.var .here) (E3sub (.there .here)))) (.atom (.var .here))))))

def E3Ty : Ty [] := .pi E3Dom (.pi tNat tInt)

example : checkTm Ctx.nil E3 E3Ty = true := by decide +kernel

theorem E3_typed : Tm.HasType Ctx.nil E3 E3Ty := checkTm_sound (by decide +kernel)

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
def E4S : Ty s := tTyp lA .bot .top
/-- `T = {A : Int..⊤}`. -/
def E4T : Ty s := tTyp lA tInt .top
/-- `{B : S..T}`. -/
def E4X : Ty s := tTyp lB E4S E4T

/-- `S ≤ x.B ≤ T`, the step with no realizer. -/
def E4ST (x : BVar s .var) : LeCo s :=
  .trans (.member (.var x) (.refl E4X) 0) (.member (.var x) (.refl E4X) 1)

/-- `w` at `T`: an atom, so that its members can be eliminated. -/
def E4wT (x w : BVar s .var) : Atom s := .cast (.var w) (E4ST x)

/-- `Int ≤ w.A`, by elimination at the cast atom. -/
def E4IntLe (x w : BVar s .var) : LeCo s := .member (E4wT x w) (.refl E4T) 0

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : Tm [] :=
  .val (.lam E4X (.val (.lam E4S (.val (.lam tInt
    (.let (.val (.lam (.sel (.there .here) lA) (.atom (.var .here))))
      (.app (.var .here)
        (.cast (.var (.there .here))
          (E4IntLe (.there (.there (.there .here))) (.there (.there .here)))))))))))

def E4Ty : Ty [] := .pi E4X (.pi E4S (.pi tInt (.sel (.there .here) lA)))

example : checkTm Ctx.nil E4 E4Ty = true := by decide +kernel

theorem E4_typed : Tm.HasType Ctx.nil E4 E4Ty := checkTm_sound (by decide +kernel)

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
def E5AT : Ty s := tTyp lA .top .top

/-- Witnesses of `ν(z. {a = v})`: the single field is defined as `v.A`. -/
def E5Wit (v : BVar s .var) : Witnesses (s,x) := .cons .nil la (.sel (.there v) lA)

/-- `[z.a ≃ v.A, has a]`, the telescope of `ν(z. {a = v})`. -/
def E5Tel (v : BVar s .var) : Telescope (s,x) :=
  .cons (.cons .nil (.eq (.sel .here la) (.sel (.there v) lA))) (.has la)

theorem E5Tel_eq (v : BVar s .var) : Telescope.ofLiteral (E5Wit v) [la] = E5Tel v := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, E5Wit, E5Tel]

/-- `Obj(z. [z.a ≃ v.A, has a])`, the type of `ν(z. {a = v})`. -/
def E5ObjTy (v : BVar s .var) : Ty s := .obj (E5Tel v)

/-- The field body: `v : {A : ⊤..⊤} ≤ ⊤ ≤ v.A ≃ z.a`. -/
def E5Field : Tm (s,x,x) :=
  .atom (.cast (.var (.there .here))
    (.trans (.top E5AT)
      (.trans (.member (.var (.there .here)) (.refl E5AT) 0)
        (.eqToLe (.symm (.def .here la))))))

def E5Fields : Fields (s,x,x) := .cons .nil la E5Field

/-- `λ(w : {A : ⊤..⊤}). let f = … in let o = f w in (o.a : w.A)`. -/
def E5 : Tm [] :=
  .val (.lam E5AT
    (.let (.val (.lam E5AT (.val (.obj (E5Wit .here) E5Fields))))
      (.let (.app (.var .here) (.var (.there .here)))
        (.cast
          (.proj (.var .here) la
            (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))
          (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0))))))

def E5Ty : Ty [] := .pi E5AT (.sel .here lA)

#guard checkTm Ctx.nil E5 E5Ty
#guard !checkTm Ctx.nil E5 (.pi E5AT .top)

/-- `w : {A : ⊤..⊤}, v : {A : ⊤..⊤}`, the context of the object literal. -/
def E5Ctxv : Ctx ([],x,x) := (Ctx.nil.cons (.opaque E5AT)).cons (.opaque E5AT)

theorem E5_value : Value.HasType E5Ctxv (.obj (E5Wit .here) E5Fields) (E5ObjTy .here) := by
  have h : Value.HasType E5Ctxv (.obj (E5Wit .here) E5Fields)
      (.obj (Telescope.ofLiteral (E5Wit .here) [la])) :=
    .obj rfl
      (.cons .nil
        (.atom (.cast .var
          (.trans .top (.trans (.member (Tel := telTyp lA .top .top) .var .refl (.there .here))
            (.eqToLe (.symm (.def rfl))))))))
  rw [E5Tel_eq] at h
  exact h

/-- `w : {A : ⊤..⊤}, f : ∀(v : {A : ⊤..⊤}) Obj(z. [z.a ≃ v.A, has a])`. -/
def E5Ctxf : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque E5AT)).cons (.opaque (.pi E5AT (E5ObjTy .here)))

/-- `f`, at its declared type. -/
theorem E5_f : Atom.HasType E5Ctxf (.var .here) (.pi E5AT (E5ObjTy .here)) := .var

/-- `f w : Obj(z. [z.a ≃ w.A, has a])`: the application renames `v`'s block. -/
theorem E5_app : Tm.HasType E5Ctxf (.app (.var .here) (.var (.there .here)))
    (E5ObjTy (.there .here)) :=
  .app E5_f .var

/-- `w : …, f : …, o : Obj(z. [z.a ≃ w.A, has a])`. -/
def E5Ctxo : Ctx ([],x,x,x) := E5Ctxf.cons (.opaque (E5ObjTy (.there .here)))

/-- `o.a`, then `o.a ≃ w.A`: the result mentions neither `let` binder. -/
theorem E5_proj : Tm.HasType E5Ctxo
    (.cast
      (.proj (.var .here) la (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))
      (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0)))
    (.sel (.there (.there .here)) lA) :=
  .cast (.proj .var (.member (Tel := E5Tel (.there (.there .here))) .var .refl .here))
    (.eqToLe (.member (Tel := E5Tel (.there (.there .here))) .var .refl (.there .here)))

theorem E5_typed : Tm.HasType Ctx.nil E5 E5Ty :=
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

end Examples
end FCdot
