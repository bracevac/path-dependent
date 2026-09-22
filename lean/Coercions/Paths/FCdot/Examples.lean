import Coercions.Paths.FCdot.Checker
import Coercions.Paths.FCdot.Erasure
import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.FCdot.Consistency
import Coercions.Paths.FCdot.Progress
import Coercions.Paths.DotMNF.Examples
import Coercions.Paths.DotMNF.Erasure

namespace Paths

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

The examples of the path stage, Y1 to Y9 of P1.10, follow E8.  They are
about the block forest, the field coercion, and the stores the repairs of P1
reject or keep.

## The port to paths

E1 to E8 keep their names and statements.  Two forms change, each by a row
of table P1.9.  A block name `x ∙ ℓ` is written `.sel (.var x) ℓ`, since the
first argument of `Ty.sel` is a path and a binder is the path of depth zero.
`Telescope.ofLiteral` takes a third list, the stable field labels, and every
literal here passes `[]`: the fields of E2 are a lambda under a cast, those
of E5 and E6 are atoms, and E7 has none.  With `[]` the telescope is the
base's, so `E2Tel_eq`, `E5Tel_eq`, `E6Tel_eq` and `E7Tel_eq` equate the
base's telescopes, and their `simp` sets unfold `Telescope.hasValEntries` at
the empty list.

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

/-! ## Type shapes -/

/-- `{A : S..T}` as a telescope over the self block: `[S ≤ y.A, y.A ≤ T]`. -/
def telTyp (A : Label) (S T : Ty s) : Telescope (s,x) :=
  .cons (.cons .nil (.le S↑ (.sel (.var .here) A))) (.le (.sel (.var .here) A) T↑)

/-- `{A : S..T}`.  Lower bound at index `0`, upper bound at index `1`. -/
def tTyp (A : Label) (S T : Ty s) : Ty s := .obj (telTyp A S T)

/-- `{a : T}` as a telescope over the self block: `[has a, y.a ≤ T]`. -/
def telFld (a : Label) (T : Ty s) : Telescope (s,x) :=
  .cons (.cons .nil (.has a)) (.le (.sel (.var .here) a) T↑)

/-- `{a : T}`.  Field declaration at index `0`, upper bound at index `1`. -/
def tFld (a : Label) (T : Ty s) : Ty s := .obj (telFld a T)

/-- `∀(y : x.A) x.A`, the self-referential arrow of E2 and E4. -/
def piSel (A : Label) (x : BVar s .var) : Ty s := .pi (.sel (.var x) A) (.sel (.var (.there x)) A)

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

theorem E1_typed : Ctx.nil ⊢ E1 : E1Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E1`. -/
def E1src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E1Dom (.let (.path .here) (.path .here)))

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
  .cast (.val (.lam (.sel (.var .here) lA) (.atom (.var .here))))
    (.eqToLe (.symm (.def .here la)))

def E2Fields : Fields (s,x) := .cons .nil la E2Field

/-- The literal's precise telescope: `[self.A ≃ E2W, self.a ≃ E2W, has a]`. -/
def E2Tel : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel (.var .here) lA) E2W)) (.eq (.sel (.var .here) la) E2W)) (.has la)

/-- `E2Tel` is what the literal generates. -/
theorem E2Tel_eq : Telescope.ofLiteral (E2Wit (s := s)) [la] [] = E2Tel := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, Telescope.hasValEntries, E2Wit, E2Tel, lA, la]

/-- The literal's precise type. -/
def E2Ty : Ty s := .obj E2Tel

example : checkValue Ctx.nil (.obj E2Wit E2Fields) E2Ty = true := by decide +kernel

theorem E2_value {s : Sig} {Γ : Ctx s} : Γ ⊢ᵥ .obj E2Wit E2Fields : E2Ty := by
  have h : Γ ⊢ᵥ .obj E2Wit E2Fields : (.obj (Telescope.ofLiteral E2Wit [la] [])) :=
    .obj (.cons .nil (.cast (.val (.lam (.atom .var))) (.eqToLe (.symm (.def rfl)))))
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
        (.top (.sel (.var (.there .here)) lA))))

def E2Ty' : Ty [] := .top

example : checkTm Ctx.nil E2 E2Ty' = true := by decide +kernel
example : checkTm Ctx.nil E2 .bot = false := by decide +kernel

/-- After the outer `let`: `x : E2Ty`. -/
def E2Ctx1 : Ctx ([],x) := Ctx.nil.cons (.opaque E2Ty)
/-- After the inner `let`: `x : E2Ty, f : x.a`. -/
def E2Ctx2 : Ctx ([],x,x) := E2Ctx1.cons (.opaque (.sel (.var .here) la))

/-- `f : x.a ≤ ∀(y : x.A) x.A`. -/
theorem E2_fun : Atom.HasType E2Ctx2 (.cast (.var .here) (E2aPi (.there .here)))
    (piSel lA (.there .here)) :=
  .cast .var (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here)))

/-- `f : x.a ≤ ∀(y : x.A) x.A ≤ x.A`, so `f` is its own argument. -/
theorem E2_arg : Atom.HasType E2Ctx2
    (.cast (.var .here) (.trans (E2aPi (.there .here)) (E2piA (.there .here))))
    (.sel (.var (.there .here)) lA) :=
  .cast .var
    (.trans (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here)))
      (.eqToLe (.symm (.member (Tel := E2Tel) .var .refl (.there (.there .here))))))

/-- `f f : x.A`. -/
theorem E2_app : Tm.HasType E2Ctx2
    (.app (.cast (.var .here) (E2aPi (.there .here)))
      (.cast (.var .here) (.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
    (.sel (.var (.there .here)) lA) :=
  .app E2_fun E2_arg

theorem E2_typed : Ctx.nil ⊢ E2 : E2Ty' :=
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

theorem E3_typed : Ctx.nil ⊢ E3 : E3Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E3`. -/
def E3src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E3Dom
    (.val (.lam DotMNF.Examples.E3T2 (.let (.path .here) (.path .here)))))

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
    (.let (.val (.lam (.sel (.var (.there .here)) lA) (.atom (.var .here))))
      (.app (.var .here)
        (.cast (.var (.there .here))
          (E4IntLe (.there (.there (.there .here))) (.there (.there .here)))))))))))

def E4Ty : Ty [] := .pi E4X (.pi E4S (.pi tInt (.sel (.var (.there .here)) lA)))

example : checkTm Ctx.nil E4 E4Ty = true := by decide +kernel

theorem E4_typed : Ctx.nil ⊢ E4 : E4Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E4`. -/
def E4src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E4X (.val (.lam DotMNF.Examples.E4S (.val (.lam DotMNF.Examples.E4Int
    (.let (.val (.lam (.sel (.var (.there .here)) DotMNF.Examples.lA) (.path .here)))
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
def E5Wit (v : BVar s .var) : Witnesses (s,x) := .cons .nil la (.sel (.var (.there v)) lA)

/-- `[z.a ≃ v.A, has a]`, the telescope of `ν(z. {a = v})`. -/
def E5Tel (v : BVar s .var) : Telescope (s,x) :=
  .cons (.cons .nil (.eq (.sel (.var .here) la) (.sel (.var (.there v)) lA))) (.has la)

theorem E5Tel_eq (v : BVar s .var) : Telescope.ofLiteral (E5Wit v) [la] [] = E5Tel v := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, Telescope.hasValEntries, E5Wit, E5Tel]

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

def E5Ty : Ty [] := .pi E5AT (.sel (.var .here) lA)

example : checkTm Ctx.nil E5 E5Ty = true := by decide +kernel
example : checkTm Ctx.nil E5 (.pi E5AT .top) = false := by decide +kernel

/-- `w : {A : ⊤..⊤}, v : {A : ⊤..⊤}`, the context of the object literal. -/
def E5Ctxv : Ctx ([],x,x) := (Ctx.nil.cons (.opaque E5AT)).cons (.opaque E5AT)

theorem E5_value : E5Ctxv ⊢ᵥ .obj (E5Wit .here) E5Fields : E5ObjTy .here := by
  have h : Value.HasType E5Ctxv (.obj (E5Wit .here) E5Fields)
      (.obj (Telescope.ofLiteral (E5Wit .here) [la] [])) :=
    .obj
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
theorem E5_f : E5Ctxf ⊢ₐ .var .here : .pi E5AT (E5ObjTy .here) := .var

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
    (.sel (.var (.there (.there .here))) lA) :=
  .cast (.proj .var (.member (Tel := E5Tel (.there (.there .here))) .var .refl .here))
    (.eqToLe (.member (Tel := E5Tel (.there (.there .here))) .var .refl (.there .here)))

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
def E6Wit : Witnesses (s,x) := .cons (.cons .nil lT tInt) lv (.sel (.var .here) lT)

/-- The field body: `n` (from the enclosing scope), cast from `Int` to `self.T`
by the definition of `T`, then from `self.T` to the block name `self.v` by
the definition of `v`. -/
def E6Field : Tm (s,x,x) :=
  .atom (.cast
    (.cast (.var (.there .here)) (.eqToLe (.symm (.def .here lT))))
    (.eqToLe (.symm (.def .here lv))))

def E6Fields : Fields (s,x,x) := .cons .nil lv E6Field

/-- The literal's precise telescope: `[self.T ≃ Int, self.v ≃ self.T, has v]`. -/
def E6Tel : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel (.var .here) lT) tInt)) (.eq (.sel (.var .here) lv) (.sel (.var .here) lT)))
    (.has lv)

/-- `E6Tel` is what the literal generates. -/
theorem E6Tel_eq : Telescope.ofLiteral (E6Wit (s := s)) [lv] [] = E6Tel := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, Telescope.hasValEntries, E6Wit, E6Tel, lT, lv]

/-- The literal's precise type. -/
def E6Ty : Ty s := .obj E6Tel

/-- `n : Int` in scope. -/
def E6Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque tInt)

example : checkValue E6Ctx (.obj E6Wit E6Fields) E6Ty = true := by decide +kernel

theorem E6_value {s : Sig} {Γ : Ctx s} :
    (Γ.cons (.opaque tInt)) ⊢ᵥ .obj E6Wit E6Fields : E6Ty := by
  have h : (Γ.cons (.opaque tInt)) ⊢ᵥ .obj E6Wit E6Fields :
      (.obj (Telescope.ofLiteral E6Wit [lv] [])) :=
    .obj (.cons .nil
      (.atom (.cast (.cast .var (.eqToLe (.symm (.def rfl)))) (.eqToLe (.symm (.def rfl))))))
  rw [E6Tel_eq] at h
  exact h

/-! ## E7: a two-element alias cycle

`ν(x. {A = x.B} ∧ {B = x.A})`, matching `DotMNF.Examples.E7`.  Both
witnesses are bare selections on the object's own self, each other's alias:
a shape the self-alias restriction used to rule out entirely, admitted now
because alias-tolerant resolution follows a same-block alias to whatever it
names, cycles included (a cyclic alias resolves to `⊤`). -/

/-- The witnesses: `A ↦ self.B`, `B ↦ self.A`. -/
def E7Wit : Witnesses (s,x) := .cons (.cons .nil lA (.sel (.var .here) lB)) lB (.sel (.var .here) lA)

/-- The literal's precise telescope: `[self.A ≃ self.B, self.B ≃ self.A]`, no fields. -/
def E7Tel : Telescope (s,x) :=
  .cons (.cons .nil (.eq (.sel (.var .here) lA) (.sel (.var .here) lB))) (.eq (.sel (.var .here) lB) (.sel (.var .here) lA))

/-- `E7Tel` is what the literal generates. -/
theorem E7Tel_eq : Telescope.ofLiteral (E7Wit (s := s)) [] [] = E7Tel := by
  simp [Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, Telescope.hasValEntries, E7Wit, E7Tel, lA, lB]

/-- The literal's precise type. -/
def E7Ty : Ty s := .obj E7Tel

example : checkValue Ctx.nil (.obj E7Wit .nil) E7Ty = true := by decide +kernel

theorem E7_value {s : Sig} {Γ : Ctx s} : Γ ⊢ᵥ .obj E7Wit .nil : E7Ty := by
  have h : Γ ⊢ᵥ .obj E7Wit .nil : (.obj (Telescope.ofLiteral E7Wit [] [])) := .obj .nil
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
def E8X : Ty s := tTyp lA .bot (tFld la .top)

/-- `x.A ∧ {a : ⊤}` as a telescope: a single self-bound, then `{a : ⊤}`. -/
def E8YTel (x : BVar s .var) : Telescope (s,x) :=
  (Telescope.nil.cons (⊑ (Ty.sel (.var x) lA)↑)).append (telFld la .top)

/-- `x.A ∧ {a : ⊤}`.  Self-bound at index `0`, field declaration at `1`,
field upper bound at `2`. -/
def E8Y (x : BVar s .var) : Ty s := .obj (E8YTel x)

/-- `And₂`: the identity morphism onto the second operand, at offset `1`. -/
def E8And2 (x : BVar s .var) : LeCo s :=
  .obj (E8YTel x) (.le (.has .nil 1) .none (.le 2) .none)

/-- `And₁` then `Sel-<:`: through the self-bound to `x.A`, then to `{a : ⊤}`
by the upper bound of `x`'s member `A`. -/
def E8Sel (x : BVar s .var) : LeCo s :=
  .trans (.bound (E8YTel x) 0) (.member (.var x) (.refl E8X) 1)

/-- `λ(x). λ(y). y.a`, the `And₂` derivation. -/
def E8 : Tm [] :=
  .val (.lam E8X
    (.val (.lam (E8Y .here)
      (.cast (.proj (.var .here) la (.member (.var .here) (E8And2 (.there .here)) 0))
        (.top (.sel (.var .here) la))))))

/-- `λ(x). λ(y). y.a`, the `And₁`-then-`Sel-<:` derivation: the same term
after erasure. -/
def E8b : Tm [] :=
  .val (.lam E8X
    (.val (.lam (E8Y .here)
      (.cast (.proj (.var .here) la (.member (.var .here) (E8Sel (.there .here)) 0))
        (.top (.sel (.var .here) la))))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) ⊤`. -/
def E8Ty : Ty [] := .pi E8X (.pi (E8Y .here) .top)

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
def E8Ctx : Ctx ([],x,x) := (Ctx.nil.cons (.opaque E8X)).cons (.opaque (E8Y .here))

/-- `And-I`: the two views of `y` recombined.  The non-declaration operand
is re-wrapped by `intoBnd`, the declaration operand is used as it is. -/
theorem E8_both : E8Ctx ⊢ₐ
    (.both (Telescope.nil.cons (⊑ (Ty.sel (.var (.there .here)) lA)↑)) (telFld la .top)
      (.cast (.cast (.var .here) (.bound (E8YTel (.there .here)) 0))
        (.intoBnd (.refl (.sel (.var (.there .here)) lA))))
      (.cast (.var .here) (E8And2 (.there .here)))) :
    (E8Y (.there .here)) :=
  .both
    (.cast (.cast .var (.bound (Tel := E8YTel (.there .here)) (.there (.there .here))))
      (.intoBnd .refl))
    (.cast .var (.obj (.le (.has .nil (.there .here)) .here .none .none)))
    rfl

/-! ## The path examples Y1 to Y9

The examples of P1.10: the block forest, resolution through it, elimination
at a path, the field coercion, and the stores the repairs of P1 reject or
keep.  Each fact is closed by `decide +kernel`, by `checkTm` through
`checkTm_sound`, or by a theorem of the development applied to a store the
checker typed.

A field whose body is an object literal is stable only when its casts are
table-only (decision 26).  Every literal field of Y1, Y3, Y7 and Y8 is cast
by `eqToLe (symm (def z ℓ))`, sometimes after `top`, which is table-only, and
each keeps its `∋ᵛ` entry.  The one field of those four examples that is plain
is `b` of Y8's `x`, whose body is the atom `y`: it is meant to be plain,
since it is the forwarding child the example is about. -/

/-- Type label `C`. -/
def lC : Label := .typ 3
/-- Type label `E`. -/
def lE : Label := .typ 4
/-- Term label `c`. -/
def lc : Label := .trm 3
/-- Term label `f`. -/
def lf : Label := .trm 4

/-- Path synthesis is sound, read off `PathChecked`. -/
theorem synthPath_sound {s : Sig} {Γ : Ctx s} {P : PathCo s} {T : Ty s}
    (h : synthPath Γ P = some T) : Γ ⊢ᵖ P : T := by
  unfold synthPath at h
  cases hc : synthPathCore Γ P with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      have he := Option.some.inj h
      have hty := c.typing
      rw [he] at hty
      exact hty

/-- A value the checker accepts at a type has that type. -/
theorem value_of_check {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : checkTm Γ (.val v) T = true) : Γ ⊢ᵥ v : T := by
  have h' := checkTm_sound h
  cases h' with
  | val hv => exact hv

/-! ### Y1: a two-hop block name

`x = ν(z. {B = ⊤} ∧ {val a = ν(w. {A = z.B})})`.  The inner literal is the
child of `x` at `a`, and its witness is written at the outer self.  The
table substitutes the path each literal sits at, so the child reads
`x.a ∙ A = x ∙ B`, and resolution takes two hops to `⊤`. -/

/-- The witnesses of the inner literal: `A = z.B`, with `z` the outer self. -/
def Y1InWit : Witnesses (([],x),x) := Witnesses.nil.cons lA (Ty.sel (.var (.there .here)) lB)
/-- `ν(w. {A = z.B})`. -/
def Y1In : Value ([],x) := .obj Y1InWit .nil
/-- Its precise type. -/
def Y1InTy : Ty ([],x) := μ (Telescope.ofLiteral Y1InWit [] [])

def Y1Wit : Witnesses ([],x) := (Witnesses.nil.cons lB ⊤).cons la Y1InTy
/-- The field `a`, cast to `z ∙ a` by the definition of `a`: table-only. -/
def Y1Fields : Fields ([],x) :=
  Fields.nil.cons la (.cast (.val Y1In) (.eqToLe (.symm (.def .here la))))
def Y1Val : Value [] := .obj Y1Wit Y1Fields
def Y1Ty : Ty [] := μ (Telescope.ofLiteral Y1Wit Y1Fields.labels Y1Fields.valLabels)

def Y1σ : Store ([],x) := .cons .nil Y1Val
def Y1Ctx : Ctx ([],x) := Ctx.nil.cons (.transparent Y1Ty (Y1Val.weaken.blocksAt (.var .here)))

/-- `x.a`. -/
def Y1xa : Path ([],x) := .sel (.var .here) la

theorem Y1_stable : Y1Fields.valLabels = [la] := by decide +kernel

theorem Y1_typed : Ctx.nil ⊢ᵥ Y1Val : Y1Ty := value_of_check (by decide +kernel)

theorem Y1_store_typed : ⊢ Y1σ : Y1Ctx := Store.Typed.cons .nil trivial Y1_typed

/-- The first hop: the child at `x.a` defines `A` as `x ∙ B`. -/
theorem Y1_hop : Y1Ctx.lookupDefP Y1xa lA = some (Ty.sel (.var .here) lB) := by decide +kernel

/-- **Y1.**  `x.a ∙ A` resolves through the forest to `⊤`. -/
theorem Y1_resolve : Y1Ctx.resolve (Ty.sel Y1xa lA) = ⊤ := by decide +kernel

/-! ### Y2: the repaired counterexample

The literal `ν(x. {A = ⊥} ∧ {val b = x})` of `refute-paths.md` S1.  The field
`b` holds an atom, so it is plain and its child forwards to `x`: the names
`x.b ∙ A` and `x ∙ A` read one block, and `x.b` is no node.  The body is the
self at its singleton, cast to `z ∙ b` by the definition of `b`. -/

def Y2Wit : Witnesses ([],x) := (Witnesses.nil.cons lA ⊥).cons lb (Ty.snglOf (.var .here))
def Y2Body : Tm ([],x) :=
  .cast (.atom (.sngl (.var .here) (.var .here) (.refl (.var .here))))
    (.eqToLe (.symm (.def .here lb)))
def Y2Fields : Fields ([],x) := Fields.nil.cons lb Y2Body
def Y2Val : Value [] := .obj Y2Wit Y2Fields
def Y2Ty : Ty [] := μ (Telescope.ofLiteral Y2Wit Y2Fields.labels Y2Fields.valLabels)
def Y2Ctx : Ctx ([],x) := Ctx.nil.cons (.transparent Y2Ty (Y2Val.weaken.blocksAt (.var .here)))

/-- `x.b`. -/
def Y2xb : Path ([],x) := .sel (.var .here) lb

theorem Y2_plain : Y2Fields.valLabels = [] := by decide +kernel

theorem Y2_typed : Ctx.nil ⊢ᵥ Y2Val : Y2Ty := value_of_check (by decide +kernel)

/-- **Y2**, the table.  `x.b ∙ A` and `x ∙ A` read one block, which defines
`A` as `⊥`. -/
theorem Y2_one_block :
    Y2Ctx.lookupDefP Y2xb lA = Y2Ctx.lookupDefP (.var .here) lA ∧
      Y2Ctx.lookupDefP (.var .here) lA = some ⊥ := by decide +kernel

/-- `x.b` is no node: its walk meets the forwarding child. -/
theorem Y2_no_node : Y2Ctx.nodeBlock Y2xb = none := by decide +kernel

/-! The g6 store of `p1-g6-counterexample.lean`: `ν(z. {A = ⊥})` at the
outer binder `x`, `ν(z. {A = ⊤})` at the inner binder `y`.  An atom at `y`,
cast to `⊤`, was typed at the singleton of `x` through `LeCo.intoSngl`.  The
rule is gone, and `Atom.sngl` asks for an alias at the atom's root, so the
atom is typed at no singleton of `x`. -/

def Y2WBot : Witnesses (s,x) := .cons .nil lA .bot
def Y2WTop : Witnesses (s,x) := .cons .nil lA .top
def Y2vBot : Value s := .obj Y2WBot .nil
def Y2vTop : Value s := .obj Y2WTop .nil
def Y2TBot : Ty s := .obj (Telescope.ofLiteral (Y2WBot (s := s)) [] [])
def Y2TTop : Ty s := .obj (Telescope.ofLiteral (Y2WTop (s := s)) [] [])

def Y2Gamma : Ctx (([],x),x) :=
  (Ctx.nil.cons (.transparent (Y2TBot (s := [])) (Y2vBot.weaken.blocksAt (.var .here)))).cons
    (.transparent (Y2TTop (s := ([],x))) (Y2vTop.weaken.blocksAt (.var .here)))

/-- The outer binder, whose block defines `A` as `⊥`. -/
def Y2xVar : BVar (([],x),x) .var := .there .here
/-- The inner binder, whose block defines `A` as `⊤`. -/
def Y2yVar : BVar (([],x),x) .var := .here

/-- An atom at `⊤`, standing at the inner binder. -/
def Y2aTop : Atom (([],x),x) := .cast (.var Y2yVar) (.top (Y2TTop (s := ([],x))).weaken)

/-- The atom at `y` offered at the singleton of `x`, with the only alias its
root has. -/
def Y2aSngl : Atom (([],x),x) := .sngl Y2aTop (.var Y2xVar) (.refl (.var Y2yVar))

theorem Y2_aTop : synthAtom Y2Gamma Y2aTop = some ⊤ := by decide +kernel

/-- **Y2**, the g6 store.  The atom at `y` is not typed at the singleton of
`x`. -/
theorem Y2_sngl_rejected : synthAtom Y2Gamma Y2aSngl = none := by decide +kernel

theorem Y2_sngl_untyped (T : Ty (([],x),x)) : ¬ Y2Gamma ⊢ₐ Y2aSngl : T := fun h => by
  have := synthAtom_complete h
  rw [Y2_sngl_rejected] at this
  cases this

/-- The atom at `x` is typed at the singleton of `x`. -/
theorem Y2_sngl_x :
    synthAtom Y2Gamma (.sngl (.var Y2xVar) (.var Y2xVar) (.refl (.var Y2xVar))) =
      some (Ty.snglOf (.var Y2xVar)) := by decide +kernel

/-! ### Y3: E7p, a two-element alias cycle below a field

`ν(x. {val c = ν(z. {A = x.c.B} ∧ {B = x.c.A})})`.  The inner witnesses name
the path `x.c` through the outer self.  The two names are each other's alias,
and alias-tolerant resolution sends the cycle to `⊤`. -/

/-- `x.c`, written inside the inner literal, where the outer self is
`.there .here`. -/
def Y3xcIn : Path (([],x),x) := .sel (.var (.there .here)) lc
def Y3InWit : Witnesses (([],x),x) :=
  (Witnesses.nil.cons lA (Ty.sel Y3xcIn lB)).cons lB (Ty.sel Y3xcIn lA)
def Y3In : Value ([],x) := .obj Y3InWit .nil
def Y3InTy : Ty ([],x) := μ (Telescope.ofLiteral Y3InWit [] [])

def Y3Wit : Witnesses ([],x) := Witnesses.nil.cons lc Y3InTy
/-- The field `c`, cast to `z ∙ c` by the definition of `c`: table-only. -/
def Y3Fields : Fields ([],x) :=
  Fields.nil.cons lc (.cast (.val Y3In) (.eqToLe (.symm (.def .here lc))))
def Y3Val : Value [] := .obj Y3Wit Y3Fields
def Y3Ty : Ty [] := μ (Telescope.ofLiteral Y3Wit Y3Fields.labels Y3Fields.valLabels)
def Y3Ctx : Ctx ([],x) := Ctx.nil.cons (.transparent Y3Ty (Y3Val.weaken.blocksAt (.var .here)))

/-- `x.c`, at the store binder. -/
def Y3xc : Path ([],x) := .sel (.var .here) lc

theorem Y3_stable : Y3Fields.valLabels = [lc] := by decide +kernel

theorem Y3_typed : Ctx.nil ⊢ᵥ Y3Val : Y3Ty := value_of_check (by decide +kernel)

/-- The table reads the two witnesses at `x.c`. -/
theorem Y3_defs :
    Y3Ctx.lookupDefP Y3xc lA = some (Ty.sel Y3xc lB) ∧
      Y3Ctx.lookupDefP Y3xc lB = some (Ty.sel Y3xc lA) := by decide +kernel

/-- **Y3.**  Both names of the cycle resolve to `⊤`. -/
theorem Y3_resolve :
    Y3Ctx.resolve (Ty.sel Y3xc lA) = ⊤ ∧ Y3Ctx.resolve (Ty.sel Y3xc lB) = ⊤ := by
  decide +kernel

/-! ### Y4: forwarding

The literal `ν(x. {val a = x} ∧ {val b = x.a})` of P1.10.  A field body that
is a path is an atom rooted at `x`, and an atom's child forwards to its root
(`Tm.childAt`), so both bodies are written as the atom `x`.  Both children
forward to the binder itself, and the walk settles.  P1.10 said this walk runs
out of budget, which the forest cannot do here: following a child forwarding
lands on a binder, whose block is an object node (report of P1 g4).  A
forwarding cycle needs forwarding nodes that name each other, and the second
half of Y4 builds one by hand.  There the walk runs out of budget and the
name is opaque. -/

def Y4Fields : Fields ([],x) :=
  (Fields.nil.cons la (.atom (.var .here))).cons lb (.atom (.var .here))
def Y4Val : Value [] := .obj .nil Y4Fields
def Y4Ty : Ty [] := μ (Telescope.ofLiteral .nil Y4Fields.labels Y4Fields.valLabels)
def Y4Ctx : Ctx ([],x) := Ctx.nil.cons (.transparent Y4Ty (Y4Val.weaken.blocksAt (.var .here)))

theorem Y4_plain : Y4Fields.valLabels = [] := by decide +kernel

/-- Both children forward to `x`, and the walk settles on `x`'s block. -/
theorem Y4_settles :
    Y4Ctx.lookupBlock (.sel (.var .here) la) = Y4Ctx.lookupBlock (.var .here) ∧
      Y4Ctx.lookupBlock (.sel (.var .here) lb) = Y4Ctx.lookupBlock (.var .here) ∧
      (Y4Ctx.lookupBlock (.var .here)).isSome = true := by decide +kernel

theorem Y4_def : Y4Ctx.lookupDefP (.sel (.var .here) lb) lA = some ⊤ := by decide +kernel

/-- A block whose child `a` forwards to `x.b` and whose child `b` forwards to
`x.a`. -/
def Y4CycBlock : Block ([],x) :=
  .obj (Witnesses.nil.cons lA ⊤) [la, lb] []
    ((Children.nil.cons la (.fwd (.sel (.var .here) lb))).cons lb (.fwd (.sel (.var .here) la)))
def Y4CycCtx : Ctx ([],x) := Ctx.nil.cons (.transparent ⊤ Y4CycBlock)

theorem Y4_cycle_budget : Y4CycCtx.aliasBudget = 3 := by decide +kernel

/-- **Y4.**  On the cycle the walk runs out of budget. -/
theorem Y4_cycle_block :
    Y4CycCtx.lookupBlock (.sel (.var .here) la) = none ∧
      Y4CycCtx.lookupDefP (.sel (.var .here) la) lA = none := by decide +kernel

/-- So the name is opaque. -/
theorem Y4_cycle_opaque :
    Y4CycCtx.resolve (Ty.sel (.sel (.var .here) la) lA) = Ty.sel (.sel (.var .here) la) lA := by
  decide +kernel

/-! ### Y5: E1p's target, elimination at a path under a lambda

`λ(w : {val f : {A : ⊤..⊥}}). let y = (w : {B : Int..Int}) in y`.  The
parameter's declared type lists `∋ᵛ f`, so `w.f` is a stable path of type
`w ∙ f`, and the declared bound `w ∙ f ≤ {A : ⊤..⊥}` lets `memberP` eliminate
the two bounds of `w.f ∙ A`.  The store has no block for `w.f`: the binder is
opaque. -/

/-- `{val f : {A : ⊤..⊥}}`: presence at `0`, the bound at `1`, the stable
presence at `2`. -/
def Y5Dom : Ty s := .obj (((Telescope.nil ▹ ∋ lf) ▹ Ty.sel (.var .here) lf ⊑ E1Dom) ▹ ∋ᵛ lf)

/-- `w.f`, by the stable presence. -/
def Y5wf (w : BVar s .var) : PathCo s := .sel (.var w) lf 2

/-- `w ∙ f ≤ {A : ⊤..⊥}`, the declared bound. -/
def Y5wfDom (w : BVar s .var) : LeCo s := .member (.var w) (.refl Y5Dom) 1

/-- `{val f : …} ≤ ⊤ ≤ w.f ∙ A ≤ ⊥ ≤ T`, by elimination at the path `w.f`. -/
def Y5badBounds (w : BVar s .var) (T : Ty s) : LeCo s :=
  .trans (.top Y5Dom)
    (.trans (.memberP (Y5wf w) (Y5wfDom w) 0)
      (.trans (.memberP (Y5wf w) (Y5wfDom w) 1) (.bot T)))

def Y5 : Tm [] :=
  .val (.lam Y5Dom
    (.let (.atom (.cast (.var .here) (Y5badBounds .here E1Res))) (.atom (.var .here))))

def Y5Ty : Ty [] := .pi Y5Dom E1Res

def Y5Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque Y5Dom)

/-- The path `w.f` is typed at `w ∙ f`. -/
theorem Y5_path : synthPath Y5Ctx (Y5wf .here) = some (Ty.sel (.var .here) lf) := by
  decide +kernel

/-- No block for `w.f`. -/
theorem Y5_no_block : Y5Ctx.lookupBlock (.sel (.var .here) lf) = none := by decide +kernel

/-- **Y5.** -/
example : checkTm Ctx.nil Y5 Y5Ty = true := by decide +kernel

theorem Y5_typed : Ctx.nil ⊢ Y5 : Y5Ty := checkTm_sound (by decide +kernel)

/-! ### Y6: the pairs and the budget

`Ctx.defPairs` of Y3's context, which has a child, and the budget
`defPairs.length + 2` that `Ctx.resolve` runs at. -/

/-- The outer node lists its label `c`, and the child at `x.c` lists `A` and `B`
twice: once as its own labels and once as the head names of its two
witnesses. -/
theorem Y6_defPairs :
    Y3Ctx.defPairs = [(.var .here, lc), (Y3xc, lA), (Y3xc, lB), (Y3xc, lA), (Y3xc, lB)] := by
  decide +kernel

/-- The budget of `Ctx.resolve` is `5 + 2`.  The forest has no forwarding
node, so the walk's own budget is one unit. -/
theorem Y6_budget : Y3Ctx.defPairs.length + 2 = 7 ∧ Y3Ctx.aliasBudget = 1 := by decide +kernel

/-- **Y6.**  The resolution of Y3 at the computed budget. -/
theorem Y6_resolveFuel : Y3Ctx.resolveFuel 7 (Ty.sel Y3xc lA) = ⊤ := by decide +kernel

/-! ### Y7: the F1 store, the field coercion, and the view at `x.a.b`

`ν(x. {val a = ν(z. {B = ⊤} ∧ {val b = ν(w. {E = ⊤})})})`.  Both fields are
stable.  `Store.fieldCo` at `x.a` and `b` closes the coercion of `b` over
the store: `def z b` becomes `defP (x.a) b`.  The checker types it at
`x.a ∙ b`, and the view at `x.a.b` is the view of the declared `⊤`. -/

def Y7InWit : Witnesses ((([],x),x),x) := Witnesses.nil.cons lE ⊤
def Y7In : Value (([],x),x) := .obj Y7InWit .nil
def Y7InTy : Ty (([],x),x) := μ (Telescope.ofLiteral Y7InWit [] [])
def Y7MidWit : Witnesses (([],x),x) := (Witnesses.nil.cons lB ⊤).cons lb ⊤
/-- The field `b`: `top`, then the definition of `b`.  Table-only. -/
def Y7MidFields : Fields (([],x),x) :=
  Fields.nil.cons lb (.cast (.val Y7In) (.trans (.top Y7InTy) (.eqToLe (.symm (.def .here lb)))))
def Y7Mid : Value ([],x) := .obj Y7MidWit Y7MidFields
def Y7MidTy : Ty ([],x) := μ (Telescope.ofLiteral Y7MidWit Y7MidFields.labels Y7MidFields.valLabels)
def Y7Wit : Witnesses ([],x) := Witnesses.nil.cons la Y7MidTy
/-- The field `a`, cast by the definition of `a`.  Table-only. -/
def Y7Fields : Fields ([],x) :=
  Fields.nil.cons la (.cast (.val Y7Mid) (.eqToLe (.symm (.def .here la))))
def Y7Val : Value [] := .obj Y7Wit Y7Fields
def Y7Ty : Ty [] := μ (Telescope.ofLiteral Y7Wit Y7Fields.labels Y7Fields.valLabels)

def Y7σ : Store ([],x) := .cons .nil Y7Val
def Y7Ctx : Ctx ([],x) := Ctx.nil.cons (.transparent Y7Ty (Y7Val.weaken.blocksAt (.var .here)))

def Y7xa : Path ([],x) := .sel (.var .here) la

/-- The path `x.a.b`, through the cast of `x.a` to its definition. -/
def Y7Pab : PathCo ([],x) := .sel (.cast (.sel (.var .here) la 2) (.eqToLe (.defP (.var .here) la))) lb 3

/-- The coercion of `b` closed over the store. -/
def Y7Co : LeCo ([],x) :=
  .trans (.top (μ (Telescope.ofLiteral (Witnesses.nil.cons lE ⊤) [] []))) (.eqToLe (.symm (.defP Y7xa lb)))

theorem Y7_stable : Y7Fields.valLabels = [la] ∧ Y7MidFields.valLabels = [lb] := by decide +kernel

theorem Y7_typed : Ctx.nil ⊢ᵥ Y7Val : Y7Ty := value_of_check (by decide +kernel)

theorem Y7_store_typed : ⊢ Y7σ : Y7Ctx := Store.Typed.cons .nil trivial Y7_typed

/-- **Y7**, the field coercion at `x.a` and `b`, computed. -/
theorem Y7_fieldCo : Y7σ.fieldCo Y7xa lb = some Y7Co := by decide +kernel

/-- The checker types it at `x.a ∙ b`. -/
theorem Y7_fieldCo_synth :
    synthLe Y7Ctx Y7Co = some (μ (Telescope.ofLiteral (Witnesses.nil.cons lE ⊤) [] []), Ty.sel Y7xa lb) := by
  decide +kernel

theorem Y7_fieldCo_typed :
    Y7Ctx ⊢ Y7Co : μ (Telescope.ofLiteral (Witnesses.nil.cons lE ⊤) [] []) ≤ Ty.sel Y7xa lb :=
  synthLe_sound Y7_fieldCo_synth

/-- `Store.Typed.fieldCo` at the node `x.a` gives the same coercion. -/
theorem Y7_fieldCo_theorem : ∃ S, Y7Ctx ⊢ Y7Co : S ≤ Ty.sel Y7xa lb := by
  have hb : (match Y7Ctx.nodeBlock Y7xa with
      | some (.obj _ _ vls _) => vls.contains lb
      | _ => false) = true := by decide +kernel
  cases hn : Y7Ctx.nodeBlock Y7xa with
  | none => rw [hn] at hb; cases hb
  | some B =>
      rw [hn] at hb
      cases B with
      | fwd q => cases hb
      | obj W ls vls ch =>
          obtain ⟨E, S, hE, hty, -⟩ :=
            Store.Typed.fieldCo Y7_store_typed hn (by simpa using hb)
          rw [Y7_fieldCo] at hE
          obtain rfl := Option.some.inj hE
          exact ⟨S, hty⟩

theorem Y7_Pab_synth : synthPath Y7Ctx Y7Pab = some (Ty.sel Y7xa lb) := by decide +kernel

theorem Y7_Pab_typed : Y7Ctx ⊢ᵖ Y7Pab : Ty.sel Y7xa lb := synthPath_sound Y7_Pab_synth

/-- The declared type of `b` is `⊤`. -/
theorem Y7_resolve : Y7Ctx.resolve (Ty.sel Y7xa lb) = ⊤ := by decide +kernel

/-- **Y7**, the view at `x.a.b`: the view of `⊤`, which has no entry. -/
theorem Y7_pathView : pathView Y7σ 5 Y7Pab = some .nil := by decide +kernel

/-- T1 at `x.a.b`, by `Store.Typed.pathView`. -/
theorem Y7_t1 :
    ∃ (n : Nat) (V : View ([],x)), pathView Y7σ n Y7Pab = some V ∧
      (∀ Tel : Telescope (([],x),x), Y7Ctx.resolve (Ty.sel Y7xa lb) = μ Tel →
        Y7Ctx ⊨[Y7Pab.path, Y7σ] V : Tel) ∧ Y7Ctx.resolve (Ty.sel Y7xa lb) ≠ ⊥ :=
  Store.Typed.pathView Y7_store_typed Y7_Pab_typed

/-! ### Y8: a forwarding child is no node

The refutation's store of the T1 note: `y = ν(z. {val c = ν(w. {C = ⊤} ∧
{A = Π(w.C) ⊤})})` and `x = ν(u. {val b = y})`.  The field `b` of `x` holds
the atom `y`, so it is plain and its child forwards to `y`.  The name
`x.b ∙ c` resolves through that child to `y ∙ c`, and `x.b` is no node, so
the `node` rule types nothing at `x.b` (decision 24). -/

def Y8CWit : Witnesses (([],x),x) := (Witnesses.nil.cons lC ⊤).cons lA (.pi (Ty.sel (.var .here) lC) ⊤)
def Y8C : Value ([],x) := .obj Y8CWit .nil
def Y8CTy : Ty ([],x) := μ (Telescope.ofLiteral Y8CWit [] [])

def Y8yWit : Witnesses ([],x) := Witnesses.nil.cons lc Y8CTy
/-- The field `c` of `y`, cast by the definition of `c`.  Table-only. -/
def Y8yFields : Fields ([],x) :=
  Fields.nil.cons lc (.cast (.val Y8C) (.eqToLe (.symm (.def .here lc))))
def Y8y : Value [] := .obj Y8yWit Y8yFields
def Y8yTy : Ty [] := μ (Telescope.ofLiteral Y8yWit Y8yFields.labels Y8yFields.valLabels)
def Y8yCtx : Ctx ([],x) := Ctx.nil.cons (.transparent Y8yTy (Y8y.weaken.blocksAt (.var .here)))

def Y8xWit : Witnesses (([],x),x) := Witnesses.nil.cons lb ⊤
/-- The field `b` of `x`: the atom `y`, plain by design. -/
def Y8xFields : Fields (([],x),x) :=
  Fields.nil.cons lb
    (.cast (.atom (.var (.there .here)))
      (.trans (.top Y8yTy.weaken.weaken) (.eqToLe (.symm (.def .here lb)))))
def Y8x : Value ([],x) := .obj Y8xWit Y8xFields
def Y8xTy : Ty ([],x) := μ (Telescope.ofLiteral Y8xWit Y8xFields.labels Y8xFields.valLabels)

def Y8σ : Store (([],x),x) := .cons (.cons .nil Y8y) Y8x
def Y8Ctx : Ctx (([],x),x) := Y8yCtx.cons (.transparent Y8xTy (Y8x.weaken.blocksAt (.var .here)))

/-- `y`, and `x.b`. -/
def Y8yP : Path (([],x),x) := .var (.there .here)
def Y8xb : Path (([],x),x) := .sel (.var .here) lb

theorem Y8_stable : Y8yFields.valLabels = [lc] ∧ Y8xFields.valLabels = [] := by decide +kernel

theorem Y8_y_typed : Ctx.nil ⊢ᵥ Y8y : Y8yTy := value_of_check (by decide +kernel)

theorem Y8_x_typed : Y8yCtx ⊢ᵥ Y8x : Y8xTy := value_of_check (by decide +kernel)

theorem Y8_store_typed : ⊢ Y8σ : Y8Ctx :=
  Store.Typed.cons (Store.Typed.cons .nil trivial Y8_y_typed) trivial Y8_x_typed

/-- `x.b ∙ c` resolves through the forwarding child, to the name `y ∙ c`
reads. -/
theorem Y8_resolve :
    Y8Ctx.lookupDefP Y8xb lc = Y8Ctx.lookupDefP Y8yP lc ∧
      Y8Ctx.resolve (Ty.sel Y8xb lc) = Y8Ctx.resolve (Ty.sel Y8yP lc) ∧
      Y8Ctx.resolve (Ty.sel Y8xb lc) ≠ Ty.sel Y8xb lc := by decide +kernel

/-- The walk finds `y`'s block at `x.b`, with `c` stable. -/
theorem Y8_walk : Y8Ctx.lookupValFieldsP Y8xb = some [lc] := by decide +kernel

/-- `x.b` is no node. -/
theorem Y8_no_node : Y8Ctx.nodeBlock Y8xb = none := by decide +kernel

/-- The witnesses the walk finds at `x.b`, bound again at the self. -/
def Y8WalkW : Witnesses ((([],x),x),x) :=
  match Y8Ctx.lookupBlock Y8xb with
  | some (.obj W _ _ _) => W.rename Rename.succ
  | _ => .nil

/-- **Y8.**  The `node` rule does not type `x.b` at `y`'s literal. -/
theorem Y8_node_rejected : synthPath Y8Ctx (.node Y8xb Y8WalkW [lc] [lc]) = none := by
  decide +kernel

/-- Nor at any other literal. -/
theorem Y8_node_untyped (W : Witnesses ((([],x),x),x)) (ls vls : List Label)
    (T : Ty (([],x),x)) : ¬ Y8Ctx ⊢ᵖ .node Y8xb W ls vls : T := by
  intro h
  cases h with
  | node _ hn =>
      rw [Y8_no_node] at hn
      cases hn

/-! ### Y9: the store of g9b rejected, and the abstract witness kept

`x = ν(z. {a = ν(w. {C = ⊤}) ▷ E_a})`, `a` declared at `μ[self ∙ C ⊑ ⊥]`.
The cast `E_a` eliminates at `z.a` through the declared type of `a`, so the
field justified its own declaration, and over the store `⊤ ≤ ⊥` was
derivable (`p1-g9b-counterexample.lean`).  After decision 26 the field is not
stable, `a` gets no `∋ᵛ` entry, `z.a` is no stable path, and the checker
rejects the literal.  By completeness it types at no type. -/

def Y9Wi : Witnesses (([],x),x) := Witnesses.nil.cons lC .top
def Y9vi : Value ([],x) := .obj Y9Wi .nil
def Y9Tela : Telescope (([],x),x) := Telescope.nil ▹ Proposition.le (.sel (.var .here) lC) .bot
def Y9Wo : Witnesses ([],x) := Witnesses.nil.cons la (μ Y9Tela)
/-- `⊤ ≤ z.a ∙ C ≤ ⊥`, the second step by elimination at `z.a`. -/
def Y9ePost : LeCo ([],x) :=
  .trans (.eqToLe (.symm (.defP (.sel (.var .here) la) lC)))
    (.memberP (.sel (.var .here) la 2) (.eqToLe (.def .here la)) 0)
def Y9mA : Morphism ([],x) := .le .nil .none (.eq 0) (.some Y9ePost)
def Y9Ea : LeCo ([],x) :=
  .trans (.obj (Telescope.ofLiteral Y9Wi [] []) Y9mA) (.eqToLe (.symm (.def .here la)))
/-- The field `a`: a literal under a cast that eliminates.  Plain by
decision 26, which is the point of the example. -/
def Y9Fo : Fields ([],x) := Fields.nil.cons la (.cast (.val Y9vi) Y9Ea)
def Y9vo : Value [] := .obj Y9Wo Y9Fo

theorem Y9_not_tableOnly : Y9Ea.tableOnly = false := by decide +kernel

/-- `a` is not stable. -/
theorem Y9_plain : Y9Fo.valLabels = [] := by decide +kernel

/-- **Y9**, the rejection. -/
theorem Y9_synth_none : synthValue Ctx.nil Y9vo = none := by decide +kernel

/-- The literal types at no type, by completeness of the checker. -/
theorem Y9_untyped (T : Ty []) : ¬ Ctx.nil ⊢ᵥ Y9vo : T := fun h => by
  have := synthValue_complete h
  rw [Y9_synth_none] at this
  cases this

/-- So the store `x = Y9vo` is typed in no context. -/
theorem Y9_store_untyped (Γ : Ctx ([],x)) : ¬ ⊢ (Store.cons .nil Y9vo) : Γ := by
  intro h
  cases h with
  | cons h0 _ hv =>
      cases h0
      exact Y9_untyped _ hv

/-! The abstract witness kept (`Scratch_FF_Design.lean.txt:713-824`):
`x = ν(z. {a = ν(w. {C = ⊥}) ▷ E})` with `a` declared at `μ[self ∙ C ⊑ ⊤]`.
The cast `E` proves the declared bound from the literal's `C = ⊥` by the
constant side `top`, eliminates nowhere, and the field stays stable.  The
store is typed, and T1 at `x.a` and consistency hold by the base theorems. -/

def Y9Wi2 : Witnesses (([],x),x) := Witnesses.nil.cons lC .bot
def Y9vi2 : Value ([],x) := .obj Y9Wi2 .nil
def Y9Tela2 : Telescope (([],x),x) := Telescope.nil ▹ Proposition.le (.sel (.var .here) lC) ⊤
def Y9Wo2 : Witnesses ([],x) := Witnesses.nil.cons la (μ Y9Tela2)
def Y9mA2 : Morphism ([],x) := .le .nil .none (.eq 0) (.top .bot)
def Y9E2 : LeCo ([],x) :=
  .trans (.obj (Telescope.ofLiteral Y9Wi2 [] []) Y9mA2) (.eqToLe (.symm (.def .here la)))
def Y9Fo2 : Fields ([],x) := Fields.nil.cons la (.cast (.val Y9vi2) Y9E2)
def Y9vo2 : Value [] := .obj Y9Wo2 Y9Fo2
def Y9To2 : Ty [] := μ (Telescope.ofLiteral Y9Wo2 Y9Fo2.labels Y9Fo2.valLabels)
def Y9σ2 : Store ([],x) := .cons .nil Y9vo2
def Y9Γ2 : Ctx ([],x) := Ctx.nil.cons (.transparent Y9To2 (Y9vo2.weaken.blocksAt (.var .here)))

/-- `x.a`. -/
def Y9P2 : PathCo ([],x) := .sel (.var .here) la 2

theorem Y9_E2_tableOnly : Y9E2.tableOnly = true := by decide +kernel

/-- `a` is stable. -/
theorem Y9_stable : Y9Fo2.valLabels = [la] := by decide +kernel

theorem Y9_typed : Ctx.nil ⊢ᵥ Y9vo2 : Y9To2 := value_of_check (by decide +kernel)

theorem Y9_store_typed : ⊢ Y9σ2 : Y9Γ2 := Store.Typed.cons .nil trivial Y9_typed

theorem Y9_P2_synth : synthPath Y9Γ2 Y9P2 = some (Ty.sel (.var .here) la) := by decide +kernel

theorem Y9_P2_typed : Y9Γ2 ⊢ᵖ Y9P2 : Ty.sel (.var .here) la := synthPath_sound Y9_P2_synth

theorem Y9_pathView : (pathView Y9σ2 8 Y9P2).isSome = true := by decide +kernel

/-- **Y9**, T1 at `x.a`, by `Store.Typed.pathView`. -/
theorem Y9_t1 :
    ∃ (n : Nat) (V : View ([],x)), pathView Y9σ2 n Y9P2 = some V ∧
      (∀ Tel : Telescope (([],x),x), Y9Γ2.resolve (Ty.sel (.var .here) la) = μ Tel →
        Y9Γ2 ⊨[Y9P2.path, Y9σ2] V : Tel) ∧ Y9Γ2.resolve (Ty.sel (.var .here) la) ≠ ⊥ :=
  Store.Typed.pathView Y9_store_typed Y9_P2_typed

/-- Consistency over the store, by `Store.Typed.no_top_le_bot`. -/
theorem Y9_consistent : ¬ ∃ e : LeCo ([],x), Y9Γ2 ⊢ e : ⊤ ≤ ⊥ := Y9_store_typed.no_top_le_bot

end Examples
end FCdot

end Paths
