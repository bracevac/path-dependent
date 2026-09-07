import Coercions.Captures.FCdot.Checker
import Coercions.Captures.FCdot.Erasure
import Coercions.Captures.FCdot.Consistency
import Coercions.Captures.FCdot.Prediction
import Coercions.Captures.DotMNF.Examples
import Coercions.Captures.DotMNF.Erasure
import Coercions.Captures.DotToFCdot.Prediction

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

/-! ## Syntactic inclusions of capture sets

The three inclusions the hand-written derivations below need.  They are stated
as lemmas rather than decided, because the derivations are stated for an
arbitrary signature and `decide` needs a closed proposition. -/

/-- The empty capture set is included in every set. -/
theorem sub_nil {s : Sig} {C : CaptureSet s} : CaptureSet.Subset [] C := by
  intro a h; simp at h

/-- Every capture set is included in itself. -/
theorem sub_refl {s : Sig} {C : CaptureSet s} : CaptureSet.Subset C C := fun _ h => h

/-- A one-atom set is included in every set that begins with that atom. -/
theorem sub_head {s : Sig} {a : CapAtom s} {C : CaptureSet s} :
    CaptureSet.Subset [a] (a :: C) := by
  intro b h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  simp [h]

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
  .val (.lam [] (Ty.pure E1Dom)
    (.let (.atom (.cast (.var .here) (badBounds .here E1Res))) (.atom (.var .here))
      [] (.capvar (.var .here)))
    (.elem [CapAtom.var .here] [CapAtom.var .here]))

def E1Ty : Ty [] := Ty.pure (.pi (Ty.pure E1Dom) (Ty.pure E1Res))

example : checkTm Ctx.nil E1 E1Ty = true := by decide +kernel

theorem E1_typed : Ctx.nil ⊢ E1 : E1Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E1`. -/
def E1src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E1Dom (.let (.path (.var .here)) (.path (.var .here))))

example : DotMNF.HasTy [] .nil E1src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E1Dom DotMNF.Examples.E1Res)) :=
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

/-- The literal's capture witnesses: the field `a` holds a pure value, so its
capture name is declared empty.  This is the entry a `member` in the capture
sort reads to bound the capture name of a projection. -/
def E2CapWit : CapWitnesses (s,x) := .cons .nil la []

/-- The field body `λ(y : self.A). y`, cast from its own arrow type to the
block name `self.a` by the definition of `a`. -/
def E2Field : Tm (s,x) :=
  .cast
    (.val (.lam [] (Ty.pure (.sel .here lA)) (.atom (.var .here))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.capt (.eqToLe (.symm (.def .here la))) (.elem [] [CapAtom.name .here la]))

def E2Fields : Fields (s,x) :=
  .cons .nil la E2Field (.elem [] [CapAtom.var .here])

/-- The literal's precise telescope:
`[self.A ≃ E2W, self.a ≃ E2W, {self∙a} ≐ᶜ {}, has a]`. -/
def E2Tel : Telescope (s,x) :=
  .cons
    (.cons (.cons (.cons .nil (.eq (.sel .here lA) E2W)) (.eq (.sel .here la) E2W))
      (.eqC [CapAtom.name .here la] []))
    (.has la)

/-- `E2Tel` is what the literal generates. -/
theorem E2Tel_eq : Telescope.ofLiteral (E2Wit (s := s)) E2CapWit [la] = E2Tel := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, CapWitnesses.get, E2Wit, E2CapWit, E2Tel, lA, la]

/-- The literal's precise type. -/
def E2Ty : Shape s := .obj E2Tel

example : checkValue Ctx.nil (.obj [] E2Wit E2CapWit E2Fields) (Ty.pure E2Ty) = true := by
  decide +kernel

theorem E2_value {s : Sig} {Γ : Ctx s} :
    Γ ⊢ᵥ .obj [] E2Wit E2CapWit E2Fields : Ty.pure E2Ty := by
  have h : Γ ⊢ᵥ .obj [] E2Wit E2CapWit E2Fields :
      Ty.pure (.obj (Telescope.ofLiteral E2Wit E2CapWit [la])) :=
    .obj (.cons .nil
      (.cast (.val (.lam (.atom .var) (.elem sub_refl)))
        (.capt (.eqToLe (.symm (.def rfl))) (.elem sub_nil)))
      (.elem sub_nil))
  rw [E2Tel_eq] at h
  exact h

/-- `x.a`, opened at the let-bound `x`. -/
def E2Has (x : BVar s .var) : Has s := .member (.var x) (.refl E2Ty) 3
/-- `x.a ≤ ∀(y : x.A) x.A`, from the definition of `a`.  The capture name of
the projection is carried along unchanged. -/
def E2aPi (x : BVar s .var) : LeCo s :=
  .capt (.eqToLe (.member (.var x) (.refl E2Ty) 1)) (.refl [CapAtom.name x la])
/-- `∀(y : x.A) x.A ≤ x.A`, from the exact bounds of `A`, and the capture name
of the field down to the empty set, from its capture definition. -/
def E2piA (x : BVar s .var) : LeCo s :=
  .capt (.eqToLe (.symm (.member (.var x) (.refl E2Ty) 0)))
    (.eqToLe (.member (.var x) (.refl E2Ty) 2))

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : Tm [] :=
  .let (.val (.obj [] E2Wit E2CapWit E2Fields))
    (.let (.proj (.var .here) la (E2Has .here))
      (.cast
        (.app (.cast (.var .here) (E2aPi (.there .here)))
          (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
        (co (.top (.sel (.there .here) lA))))
      [CapAtom.name .here la]
      (.union (.capvar (.var .here)) (.capvar (.var .here))))
    []
    (.union (.capvar (.var .here)) (.eqToLe (.member (.var .here) (.refl E2Ty) 2)))

def E2Ty' : Ty [] := Ty.pure .top

example : checkTm Ctx.nil E2 E2Ty' = true := by decide +kernel
example : checkTm Ctx.nil E2 (Ty.pure .bot) = false := by decide +kernel

/-- After the outer `let`: `x : E2Ty`. -/
def E2Ctx1 : Ctx ([],x) := Ctx.nil.cons (.opaque (Ty.pure E2Ty))
/-- After the inner `let`: `x : x.a ^ {x∙a}`, the capture name of the field. -/
def E2Ctx2 : Ctx ([],x,x) :=
  E2Ctx1.cons (.opaque ((.sel .here la) ^ [CapAtom.name .here la]))

/-- `f : x.a ≤ ∀(y : x.A) x.A`, at the capture name of the field. -/
theorem E2_fun : Atom.HasType E2Ctx2 (.cast (.var .here) (E2aPi (.there .here)))
    ((piSel lA (.there .here)) ^ [CapAtom.name (.there .here) la]) :=
  .cast .var
    (.capt (.eqToLe (.member (Tel := E2Tel) .var .refl (.there (.there .here)))) .refl)

/-- `f : x.a ≤ ∀(y : x.A) x.A ≤ x.A`, so `f` is its own argument. -/
theorem E2_arg : Atom.HasType E2Ctx2
    (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here))))
    (Ty.pure (.sel (.there .here) lA)) :=
  .cast .var
    (LeCo.HasType.trans
      (.capt (.eqToLe (.member (Tel := E2Tel) .var .refl (.there (.there .here)))) .refl)
      (.capt (.eqToLe (.symm (.member (Tel := E2Tel) .var .refl (.there (.there (.there .here))))))
        (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here)))))

/-- `f f : x.A`. -/
theorem E2_app : Tm.HasType E2Ctx2
    (.app (.cast (.var .here) (E2aPi (.there .here)))
      (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
    (Ty.pure (.sel (.there .here) lA)) :=
  .app E2_fun E2_arg

theorem E2_typed : Ctx.nil ⊢ E2 : E2Ty' :=
  .let (.val E2_value)
    (.let (.proj .var (.member (Tel := E2Tel) .var .refl .here))
      (.cast E2_app (.capt .top .refl))
      (.union (.capvar .var) (.capvar .var)))
    (.union (.capvar .var) (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here))))

/-- The source term of `DotMNF.Examples.E2`. -/
def E2src : DotMNF.Tm [] :=
  .let (.val (.obj DotMNF.Examples.E2Defs))
    (.let (.proj .here DotMNF.Examples.la) (.app .here .here))

example : DotMNF.HasTy [] .nil E2src (DotMNF.Ty.capt [] .top) := DotMNF.Examples.E2

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
  .val (.lam [] (Ty.pure E3Dom)
    (.val (.lam [] (Ty.pure tNat)
      (.let (.atom (.cast (.var .here) (E3sub (.there .here)))) (.atom (.var .here))
        [] (.capvar (.var .here)))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

def E3Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E3Dom) (Ty.pure (.pi (Ty.pure tNat) (Ty.pure tInt))))

example : checkTm Ctx.nil E3 E3Ty = true := by decide +kernel

theorem E3_typed : Ctx.nil ⊢ E3 : E3Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E3`. -/
def E3src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E3Dom
    (.val (.lam DotMNF.Examples.E3T2 (.let (.path (.var .here)) (.path (.var .here))))))

example : DotMNF.HasTy [] .nil E3src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E3Dom
      (DotMNF.Ty.capt [] (.all DotMNF.Examples.E3T2 DotMNF.Examples.E3T1)))) :=
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
  .val (.lam [] (Ty.pure E4X)
    (.val (.lam [] (Ty.pure E4S)
      (.val (.lam [] (Ty.pure tInt)
        (.let
          (.val (.lam [] (Ty.pure (.sel (.there .here) lA)) (.atom (.var .here))
            (.elem [CapAtom.var .here] [CapAtom.var .here])))
          (.app (.var .here)
            (.cast (.var (.there .here))
              (E4IntLe (.there (.there (.there .here))) (.there (.there .here)))))
          [] (.union (.capvar (.var .here)) (.capvar (.var (.there .here)))))
        (.elem [] [CapAtom.var .here])))
      (.elem [] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

def E4Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E4X) (Ty.pure (.pi (Ty.pure E4S)
    (Ty.pure (.pi (Ty.pure tInt) (Ty.pure (.sel (.there .here) lA)))))))

example : checkTm Ctx.nil E4 E4Ty = true := by decide +kernel

theorem E4_typed : Ctx.nil ⊢ E4 : E4Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E4`. -/
def E4src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E4X (.val (.lam DotMNF.Examples.E4S (.val (.lam DotMNF.Examples.E4Int
    (.let (.val (.lam (DotMNF.Ty.capt [] (.sel (.var (.there .here)) DotMNF.Examples.lA))
      (.path (.var .here))))
      (.app .here (.there .here))))))))

example : DotMNF.HasTy [] .nil E4src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4X
      (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4S
        (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4Int
          (DotMNF.Ty.capt [] (.sel (.var (.there .here)) DotMNF.Examples.lA)))))))) :=
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

/-- Capture witnesses of `ν(z. {a = v})`: the field holds the pure `v`, so its
capture name is declared empty. -/
def E5CapWit : CapWitnesses (s,x) := .cons .nil la []

/-- `[z.a ≃ v.A, {z∙a} ≐ᶜ {}, has a]`, the telescope of `ν(z. {a = v})`. -/
def E5Tel (v : BVar s .var) : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.eq (.sel .here la) (.sel (.there v) lA)))
    (.eqC [CapAtom.name .here la] [])) (.has la)

theorem E5Tel_eq (v : BVar s .var) :
    Telescope.ofLiteral (E5Wit v) E5CapWit [la] = E5Tel v := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, CapWitnesses.get, E5Wit, E5CapWit, E5Tel]

/-- `Obj(z. [z.a ≃ v.A, has a])`, the type of `ν(z. {a = v})`. -/
def E5ObjTy (v : BVar s .var) : Shape s := .obj (E5Tel v)

/-- The field body: `v : {A : ⊤..⊤} ≤ ⊤ ≤ v.A ≃ z.a`. -/
def E5Field : Tm (s,x,x) :=
  .atom (.cast (.var (.there .here))
    (.capt (.trans (.top E5AT)
        (.trans (.member (.var (.there .here)) (.refl E5AT) 0)
          (.eqToLe (.symm (.def .here la)))))
      (.elem [] [CapAtom.name .here la])))

def E5Fields : Fields (s,x,x) :=
  .cons .nil la E5Field
    (.elem [CapAtom.var (.there .here)] [CapAtom.var (.there .here), CapAtom.var .here])

/-- `λ(w : {A : ⊤..⊤}). let f = … in let o = f w in (o.a : w.A)`.  The literal
captures the parameter `v` of the inner lambda, so it carries the assigned set
`{v}`, and the inner lambda's result type is the object type at `{v}`. -/
def E5 : Tm [] :=
  .val (.lam [] (Ty.pure E5AT)
    (.let
      (.val (.lam [] (Ty.pure E5AT)
        (.val (.obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields))
        (.elem [] [CapAtom.var .here])))
      (.let (.app (.var .here) (.var (.there .here)))
        (.cast
          (.proj (.var .here) la
            (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 2))
          (.capt (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0))
            (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))))
        [CapAtom.var (.there .here)] (.capvar (.var .here)))
      []
      (.union (.union (.capvar (.var .here)) (.capvar (.var (.there .here))))
        (.capvar (.var (.there .here)))))
    (.elem [] [CapAtom.var .here]))

def E5Ty : Ty [] := Ty.pure (.pi (Ty.pure E5AT) (Ty.pure (.sel .here lA)))

example : checkTm Ctx.nil E5 E5Ty = true := by decide +kernel
example : checkTm Ctx.nil E5 (Ty.pure (.pi (Ty.pure E5AT) (Ty.pure .top))) = false := by
  decide +kernel

/-- `w : {A : ⊤..⊤}, v : {A : ⊤..⊤}`, the context of the object literal. -/
def E5Ctxv : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque (Ty.pure E5AT))).cons (.opaque (Ty.pure E5AT))

theorem E5_value : E5Ctxv ⊢ᵥ .obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields :
    (E5ObjTy .here) ^ [CapAtom.var .here] := by
  have h : Value.HasType E5Ctxv (.obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields)
      ((.obj (Telescope.ofLiteral (E5Wit .here) E5CapWit [la])) ^ [CapAtom.var .here]) :=
    .obj
      (.cons .nil
        (.atom (.cast .var
          (.capt (.trans .top
            (.trans (.member (Tel := telTyp lA .top .top) .var .refl (.there .here))
              (.eqToLe (.symm (.def rfl))))) (.elem sub_nil))))
        (.elem sub_head))
  rw [E5Tel_eq] at h
  exact h

/-- `w : {A : ⊤..⊤}, f : ∀(v : {A : ⊤..⊤}) (Obj(z. [z.a ≃ v.A, …]) ^ {v})`. -/
def E5Ctxf : Ctx ([],x,x) :=
  (Ctx.nil.cons (.opaque (Ty.pure E5AT))).cons
    (.opaque (Ty.pure (.pi (Ty.pure E5AT) ((E5ObjTy .here) ^ [CapAtom.var .here]))))

/-- `f`, at its declared type. -/
theorem E5_f : E5Ctxf ⊢ₐ .var .here :
    Ty.pure (.pi (Ty.pure E5AT) ((E5ObjTy .here) ^ [CapAtom.var .here])) := .var

/-- `f w : Obj(z. [z.a ≃ w.A, …]) ^ {w}`: the application renames `v`'s block
and its capture set. -/
theorem E5_app : Tm.HasType E5Ctxf (.app (.var .here) (.var (.there .here)))
    ((E5ObjTy (.there .here)) ^ [CapAtom.var (.there .here)]) :=
  .app E5_f .var

/-- `w : …, f : …, o : Obj(z. [z.a ≃ w.A, …]) ^ {w}`. -/
def E5Ctxo : Ctx ([],x,x,x) :=
  E5Ctxf.cons (.opaque ((E5ObjTy (.there .here)) ^ [CapAtom.var (.there .here)]))

/-- `o.a`, then `o.a ≃ w.A`: the result mentions neither `let` binder, and its
capture name is discharged by the literal's capture definition. -/
theorem E5_proj : Tm.HasType E5Ctxo
    (.cast
      (.proj (.var .here) la (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 2))
      (.capt (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 0))
        (.eqToLe (.member (.var .here) (.refl (E5ObjTy (.there (.there .here)))) 1))))
    (Ty.pure (.sel (.there (.there .here)) lA)) :=
  .cast (.proj .var (.member (Tel := E5Tel (.there (.there .here))) .var .refl .here))
    (.capt
      (.eqToLe (.member (Tel := E5Tel (.there (.there .here))) .var .refl
        (.there (.there .here))))
      (.eqToLe (.member (Tel := E5Tel (.there (.there .here))) .var .refl (.there .here))))

theorem E5_typed : Ctx.nil ⊢ E5 : E5Ty :=
  .val (.lam
    (.let (.val (.lam (.val E5_value) (.elem sub_nil)))
      (.let E5_app E5_proj (.capvar .var))
      (.union (.union (.capvar .var) (.capvar .var)) (.capvar .var)))
    (.elem sub_nil))

/-- The source term of `DotMNF.Examples.E5`. -/
def E5src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E5AT
    (.let (.val (.lam DotMNF.Examples.E5AT DotMNF.Examples.E5Obj))
      (.let (.app .here (.there .here)) (.proj .here DotMNF.Examples.la))))

example : DotMNF.HasTy [] .nil E5src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E5AT
      (DotMNF.Ty.capt [] (.sel (.var .here) DotMNF.Examples.lA)))) :=
  DotMNF.Examples.E5

theorem E5_erase : E5.erase = E5src.erase := rfl

/-! ## E6: a field typed at its own literal's type member

`ν(x. {T = Int} ∧ {v = n})` with `n : Int` from the enclosing scope,
matching `DotMNF.Examples.E6`.  The field `v`'s witness is `self.T`, a bare
selection on the object's own self: previously forbidden by the self-alias
restriction on witnesses, now checked directly. -/

/-- The witnesses: `T ↦ Int`, `v ↦ self.T` (a same-block alias). -/
def E6Wit : Witnesses (s,x) := .cons (.cons .nil lT tInt) lv (.sel .here lT)

/-- Capture witnesses: the field `v` holds the pure `n`, so its capture name is
declared empty. -/
def E6CapWit : CapWitnesses (s,x) := .cons .nil lv []

/-- The field body: `n` (from the enclosing scope), cast from `Int` to `self.T`
by the definition of `T`, then from `self.T` to the block name `self.v` by
the definition of `v`. -/
def E6Field : Tm (s,x,x) :=
  .atom (.cast
    (.cast (.var (.there .here)) (co (.eqToLe (.symm (.def .here lT)))))
    (.capt (.eqToLe (.symm (.def .here lv))) (.elem [] [CapAtom.name .here lv])))

def E6Fields : Fields (s,x,x) :=
  .cons .nil lv E6Field
    (.elem [CapAtom.var (.there .here)] [CapAtom.var (.there .here), CapAtom.var .here])

/-- The literal's precise telescope:
`[self.T ≃ Int, self.v ≃ self.T, {self∙v} ≐ᶜ {}, has v]`. -/
def E6Tel : Telescope (s,x) :=
  .cons
    (.cons (.cons (.cons .nil (.eq (.sel .here lT) tInt))
      (.eq (.sel .here lv) (.sel .here lT))) (.eqC [CapAtom.name .here lv] []))
    (.has lv)

/-- `E6Tel` is what the literal generates. -/
theorem E6Tel_eq : Telescope.ofLiteral (E6Wit (s := s)) E6CapWit [lv] = E6Tel := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, CapWitnesses.get, E6Wit, E6CapWit, E6Tel, lT, lv]

/-- The literal's precise type. -/
def E6Ty : Shape s := .obj E6Tel

/-- `n : Int` in scope. -/
def E6Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque (Ty.pure tInt))

example :
    checkValue E6Ctx (.obj [CapAtom.var .here] E6Wit E6CapWit E6Fields)
      (E6Ty ^ [CapAtom.var .here]) = true := by decide +kernel

theorem E6_value {s : Sig} {Γ : Ctx s} :
    (Γ.cons (.opaque (Ty.pure tInt))) ⊢ᵥ .obj [CapAtom.var .here] E6Wit E6CapWit E6Fields :
      E6Ty ^ [CapAtom.var .here] := by
  have h : (Γ.cons (.opaque (Ty.pure tInt))) ⊢ᵥ
      .obj [CapAtom.var .here] E6Wit E6CapWit E6Fields :
      (.obj (Telescope.ofLiteral E6Wit E6CapWit [lv])) ^ [CapAtom.var .here] :=
    .obj (.cons .nil
      (.atom (.cast (.cast .var (.capt (.eqToLe (.symm (.def rfl))) .refl))
        (.capt (.eqToLe (.symm (.def rfl))) (.elem sub_nil))))
      (.elem sub_head))
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

example : checkValue Ctx.nil (.obj [] E7Wit .nil .nil) (Ty.pure E7Ty) = true := by decide +kernel

theorem E7_value {s : Sig} {Γ : Ctx s} : Γ ⊢ᵥ .obj [] E7Wit .nil .nil : Ty.pure E7Ty := by
  have h : Γ ⊢ᵥ .obj [] E7Wit .nil .nil :
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
  .val (.lam [] (Ty.pure E8X)
    (.val (.lam [] (Ty.pure (E8Y .here))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8And2 (.there .here)) 0))
        (.capt (.top (.sel .here la)) (.refl [CapAtom.name .here la])))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

/-- `λ(x). λ(y). y.a`, the `And₁`-then-`Sel-<:` derivation: the same term
after erasure. -/
def E8b : Tm [] :=
  .val (.lam [] (Ty.pure E8X)
    (.val (.lam [] (Ty.pure (E8Y .here))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8Sel (.there .here)) 0))
        (.capt (.top (.sel .here la)) (.refl [CapAtom.name .here la])))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) (⊤ ^ {y∙a})`.  The result is
the projection's own capture name: `y` is an opaque binder, and its declared
telescope has no capture proposition to read the name through. -/
def E8Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E8X)
    (Ty.pure (.pi (Ty.pure (E8Y .here))
      ((⊤ : Shape ([],x,x)) ^ [CapAtom.name .here la]))))

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

example : DotMNF.HasTy [] .nil E8src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E8Dom
      (DotMNF.Ty.capt [] (.all (DotMNF.Examples.E8Ref .here) (DotMNF.Ty.capt [] .top))))) :=
  DotMNF.Examples.E8

example : DotMNF.HasTy [] .nil E8src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E8Dom
      (DotMNF.Ty.capt [] (.all (DotMNF.Examples.E8Ref .here) (DotMNF.Ty.capt [] .top))))) :=
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
  .val (.lam [] (Ty.pure (capBad .here))
    (.val (.lam [] (Ty.pure (boxCap (.there .here)))
      (.unbox (.var .here) [] (badCapBounds (.there .here) (.there (.there .here))))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

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


/-! ## C1 and C6: the platform, use sets, and a run

The two examples of stage A2.6.  Both live over the platform prefix of two
rigid capture binders, `κ₁ ⊑ᶜ ∗` and `κ₂ ⊑ᶜ ∗`, with `Unit := ⊤` and two
closures standing for the capabilities: `log`, annotated `{κ₁}`, and
`console`, annotated `{κ₂}`.  A capability is the identity closure; what
matters is the set it carries.

C1 is the use-set example.  The closure

```text
c1 := λ^{log}(u : Unit). let _ = log u in λ^{console}(v : Unit). console v
```

is accepted at `(Π(Unit) ((Π(Unit) Unit) ^ {console})) ^ {log}` by the
checker, and the two programs that call it have the use sets the rule for
`let` predicts, computed by `decide`.

C6 is the prediction example.  The same closure with the inner annotation
`{}` is rejected by the checker.  The good program is run in the store `σ₀`,
by a `Steps` derivation written out step by step, and at the state that reads
`console` the conclusion of `inspects_covered` composed with
`capture_prediction` bounds what that state may read by the use set of the
initial state.  The second program, whose use set has no root `κ₂`, never
reads a root with root `κ₂`, by `effect_safety`. -/

/-! ### The platform and the capabilities -/

/-- The type of a capability: a closure from `Unit` to `Unit` capturing the
platform binder `κ`. -/
def capTy {s : Sig} (κ : BVar s .cap) : Ty s :=
  (.pi (Ty.pure .top) (Ty.pure .top)) ^ [CapAtom.cvar κ]

/-- A capability: the identity closure, annotated with its platform binder.
Its closing evidence is the syntactic inclusion of the body's use set in the
annotation united with the parameter. -/
def capVal {s : Sig} (κ : BVar s .cap) : Value s :=
  .lam [CapAtom.cvar κ] (Ty.pure .top) (.atom (.var .here))
    (.elem [CapAtom.var .here] [CapAtom.cvar (.there κ), CapAtom.var .here])

/-- `unit`, the only value of `Unit`: the empty object literal. -/
def unitVal {s : Sig} : Value s := .obj [] .nil .nil .nil

/-! ### C1: the closure and its use sets

The signature of the platform store is `κ₁, κ₂, log, console, unit`, and `c1`
is checked in it.  The binders, innermost first, are `unit`, `console`,
`log`, `κ₂`, `κ₁`. -/

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, log : capTy κ₁, console : capTy κ₂, unit : Unit`, all
opaque: the context in which `c1` is checked. -/
def C1Ctx : Ctx ([],c,c,x,x,x) :=
  ((((Ctx.nil.consC .star).consC .star).cons (.opaque (capTy (.there .here)))).cons
      (.opaque (capTy (.there .here)))).cons (.opaque (Ty.pure .top))

/-- `(Π(Unit) ((Π(Unit) Unit) ^ {console})) ^ {log}`. -/
def c1Ty : Ty ([],c,c,x,x,x) :=
  (.pi (Ty.pure .top)
      ((.pi (Ty.pure .top) (Ty.pure .top)) ^ [CapAtom.var (.there (.there .here))]))
    ^ [CapAtom.var (.there (.there .here))]

/-- `λ^{log}(u : Unit). let _ = log u in λ^{console}(v : Unit). console v`.
The inner closing evidence is the syntactic inclusion; so is the outer one,
because the outer annotation is the variable `log` itself. -/
def c1val : Value ([],c,c,x,x,x) :=
  .lam [CapAtom.var (.there (.there .here))] (Ty.pure .top)
    (.let (.app (.var (.there (.there (.there .here)))) (.var .here))
      (.val (.lam [CapAtom.var (.there (.there (.there .here)))] (Ty.pure .top)
        (.app (.var (.there (.there (.there (.there .here))))) (.var .here))
        (.elem [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here]
          [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here])))
      [] (.elem [] []))
    (.elem [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])

example : checkValue C1Ctx c1val c1Ty = true := by decide +kernel

/-- **C1**: the closure is accepted at the declared type. -/
theorem C1_typed : C1Ctx ⊢ᵥ c1val : c1Ty := checkValue_sound (by decide +kernel)

/-! The two programs.  Their signature adds `c1` to the platform, so the
binders, innermost first, are `c1`, `unit`, `console`, `log`, `κ₂`, `κ₁`. -/

/-- `let f = c1 unit in f unit ⦃{console, log}; f⦄`: the body still calls the
returned closure, so the let declares `{console, log}` and the avoidance
evidence is `capvar (var f)` for `{f} ⊑ {console}` composed with `elem`. -/
def C1prog1 : Tm ([],c,c,x,x,x,x) :=
  .let (.app (.var .here) (.var (.there .here)))
    (.app (.var .here) (.var (.there (.there .here))))
    [CapAtom.var (.there (.there .here)), CapAtom.var (.there (.there (.there .here)))]
    (.union
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.var (.there (.there (.there .here)))]
          [CapAtom.var (.there (.there (.there .here))),
            CapAtom.var (.there (.there (.there (.there .here))))]))
      (.trans (.capvar (.var (.there (.there .here))))
        (.elem []
          [CapAtom.var (.there (.there (.there .here))),
            CapAtom.var (.there (.there (.there (.there .here))))])))

/-- `let f = c1 unit in unit ⦃{}; f⦄`: the body drops the closure, so the let
declares nothing and the avoidance evidence is `capvar (var unit)`. -/
def C1prog2 : Tm ([],c,c,x,x,x,x) :=
  .let (.app (.var .here) (.var (.there .here)))
    (.atom (.var (.there (.there .here))))
    [] (.capvar (.var (.there (.there .here))))

/-- The use set of the first program: `{c1, unit, console, log}`. -/
theorem C1_uses_console :
    C1prog1.uses =
      [CapAtom.var .here, CapAtom.var (.there .here), CapAtom.var (.there (.there .here)),
        CapAtom.var (.there (.there (.there .here)))] := by decide

/-- The use set of the second program: `{c1, unit}`.  The returned closure is
avoided, so neither `console` nor `log` is in it. -/
theorem C1_uses_pure :
    C1prog2.uses = [CapAtom.var .here, CapAtom.var (.there .here)] := by decide

/-! ### C6: the rejected variant, the run, and the prediction -/

/-- `c1` with the inner annotation `{}` in place of `{console}`, the closing
evidence still the syntactic inclusion. -/
def c1bad : Value ([],c,c,x,x,x) :=
  .lam [CapAtom.var (.there (.there .here))] (Ty.pure .top)
    (.let (.app (.var (.there (.there (.there .here)))) (.var .here))
      (.val (.lam [] (Ty.pure .top)
        (.app (.var (.there (.there (.there (.there .here))))) (.var .here))
        (.elem [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here]
          [CapAtom.var .here])))
      [] (.elem [] []))
    (.elem [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])

/-- The type the bad closure claims: the inner arrow is pure. -/
def c1badTy : Ty ([],c,c,x,x,x) :=
  (.pi (Ty.pure .top) ((.pi (Ty.pure .top) (Ty.pure .top)) ^ []))
    ^ [CapAtom.var (.there (.there .here))]

/-- **C6, the rejected variant**: the checker refuses the bad closure, because
the body of the inner lambda uses `console`, which the empty annotation does
not cover. -/
theorem C6_rejected : checkValue C1Ctx c1bad c1badTy = false := by decide +kernel

/-- The platform store `σ₀ := κ₁, κ₂, log, console, unit, c1`. -/
def C6Store : Store ([],c,c,x,x,x,x) :=
  Store.cons (Store.cons (Store.cons (Store.cons
    (Store.consC (Store.consC Store.nil .star) .star)
      (capVal (.there .here)))
      (capVal (.there .here)))
      unitVal)
    c1val

/-- The context of `σ₀`: every entry is stored, so every term binder is
transparent. -/
def C6Ctx : Ctx ([],c,c,x,x,x,x) :=
  Ctx.cons (Ctx.cons (Ctx.cons (Ctx.cons
    (Ctx.consC (Ctx.consC Ctx.nil .star) .star)
      (.transparent (capTy (.there .here)) .nil .nil []))
      (.transparent (capTy (.there .here)) .nil .nil []))
      (.transparent (Ty.pure .top) .nil .nil []))
    (.transparent c1Ty .nil .nil [])

theorem C6_store : ⊢ C6Store : C6Ctx :=
  .cons (.cons (.cons (.cons (.consC (.consC .nil))
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel))

/-- The initial state of the good program. -/
def C6st0 : State ([],c,c,x,x,x,x) := ⟨C6Store, .nil, C1prog1⟩

theorem C6st0_typed : State.Typed C6st0 (Ty.pure .top) :=
  ⟨C6Ctx, Ty.pure .top, C6_store, checkTm_sound (by decide +kernel), .nil⟩

/-! The states of the run, written out.  `C6K0` is the continuation the first
`let` pushes, `C6inner0` the inner closure still under the let binder of
`c1`'s body, and `C6inner` the closure the run allocates. -/

/-- The body of the first `let`: `f unit`. -/
def C6body1 : Tm ([],c,c,x,x,x,x,x) :=
  .app (.var .here) (.var (.there (.there .here)))

/-- The declared use set of the first `let`: `{console, log}`. -/
def C6U1 : CaptureSet ([],c,c,x,x,x,x) :=
  [CapAtom.var (.there (.there .here)), CapAtom.var (.there (.there (.there .here)))]

/-- The avoidance evidence of the first `let`. -/
def C6f1 : CapCo ([],c,c,x,x,x,x,x) :=
  .union
    (.trans (.capvar (.var .here))
      (.elem [CapAtom.var (.there (.there (.there .here)))]
        [CapAtom.var (.there (.there (.there .here))),
          CapAtom.var (.there (.there (.there (.there .here))))]))
    (.trans (.capvar (.var (.there (.there .here))))
      (.elem []
        [CapAtom.var (.there (.there (.there .here))),
          CapAtom.var (.there (.there (.there (.there .here))))]))

/-- The continuation the first `let` pushes. -/
def C6K0 : Cont ([],c,c,x,x,x,x) := .nil ▹ .let C6body1 C6U1 C6f1

/-- The inner closure of `c1`, still under the let binder of `c1`'s body. -/
def C6inner0 : Tm ([],c,c,x,x,x,x,x) :=
  .val (.lam [CapAtom.var (.there (.there (.there .here)))] (Ty.pure .top)
    (.app (.var (.there (.there (.there (.there .here))))) (.var .here))
    (.elem [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here]
      [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here]))

/-- The inner closure once the let binder of `c1`'s body is gone: the value the
run allocates. -/
def C6inner : Value ([],c,c,x,x,x,x) :=
  .lam [CapAtom.var (.there (.there .here))] (Ty.pure .top)
    (.app (.var (.there (.there (.there .here)))) (.var .here))
    (.elem [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])

def C6st1 : State ([],c,c,x,x,x,x) :=
  ⟨C6Store, C6K0, .app (.var .here) (.var (.there .here))⟩

def C6st2 : State ([],c,c,x,x,x,x) :=
  ⟨C6Store, C6K0,
    .let (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
      C6inner0 [] (.elem [] [])⟩

def C6st3 : State ([],c,c,x,x,x,x) :=
  ⟨C6Store, C6K0 ▹ .let C6inner0 [] (.elem [] []),
    .app (.var (.there (.there (.there .here)))) (.var (.there .here))⟩

def C6st4 : State ([],c,c,x,x,x,x) :=
  ⟨C6Store, C6K0 ▹ .let C6inner0 [] (.elem [] []), .atom (.var (.there .here))⟩

def C6st5 : State ([],c,c,x,x,x,x) := ⟨C6Store, C6K0, .val C6inner⟩

/-- The store after the allocation. -/
def C6Store1 : Store ([],c,c,x,x,x,x,x) := C6Store.cons C6inner

def C6st6 : State ([],c,c,x,x,x,x,x) :=
  ⟨C6Store1, .nil, .app (.var .here) (.var (.there (.there .here)))⟩

/-- The state that reads `console`. -/
def C6st7 : State ([],c,c,x,x,x,x,x) :=
  ⟨C6Store1, .nil,
    .app (.var (.there (.there (.there .here)))) (.var (.there (.there .here)))⟩

theorem C6_step1 : C6st0 ⟶ C6st1 := .let

/-- The closure `c1` is read out of the store; the body it hands back is fixed
by the `rfl` side condition, so the resulting state is computed, not guessed. -/
theorem C6_step2 : C6st1 ⟶ C6st2 := by
  have h := Step.appVar (σ := C6Store) (x := .here) (K := C6K0)
    (b := .var (.there .here)) rfl
  exact h

theorem C6_step3 : C6st2 ⟶ C6st3 := .let

theorem C6_step4 : C6st3 ⟶ C6st4 := by
  have h := Step.appVar (σ := C6Store) (x := .there (.there (.there .here)))
    (K := C6K0 ▹ .let C6inner0 [] (.elem [] [])) (b := .var (.there .here)) rfl
  exact h

theorem C6_step5 : C6st4 ⟶ C6st5 := .rename
theorem C6_step6 : C6st5 ⟶ C6st6 := .alloc

theorem C6_step7 : C6st6 ⟶ C6st7 := by
  have h := Step.appVar (σ := C6Store1) (x := .here) (K := .nil)
    (b := .var (.there (.there .here))) rfl
  exact h

/-- **C6, the run**: `let f = c1 unit in f unit` steps by `let`, `appVar`,
`let`, `appVar`, `rename`, `alloc`, `appVar` to the state that reads
`console`. -/
theorem C6_run : C6st0 ⟶* C6st7 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail .refl
    C6_step1) C6_step2) C6_step3) C6_step4) C6_step5) C6_step6) C6_step7

/-- The context of the store after the allocation. -/
def C6Ctx1 : Ctx ([],c,c,x,x,x,x,x) :=
  C6Ctx.cons
    (.transparent
      ((.pi (Ty.pure .top) (Ty.pure .top)) ^ [CapAtom.var (.there (.there .here))])
      .nil .nil [])

theorem C6_store1 : ⊢ C6Store1 : C6Ctx1 :=
  .cons C6_store trivial (checkValue_sound (by decide +kernel))

/-- **C6, the prediction**: at the state that reads `console`, that root is
covered by the use set of the initial state, carried along the store extension
the run performed.  This is `inspects_covered` composed with
`capture_prediction`. -/
theorem C6_covered :
    ∃ ρ : Rename ([],c,c,x,x,x,x) ([],c,c,x,x,x,x,x),
      Store.Ext C6Store C6Store1 ρ ∧
        ∀ Γ' : Ctx ([],c,c,x,x,x,x,x), ⊢ C6Store1 : Γ' →
          CapLe Γ' [CapAtom.var (.there (.there (.there .here)))]
            (C6st0.uses.rename ρ) := by
  obtain ⟨ρ, hE, h⟩ := capture_prediction C6st0_typed C6_run
  exact ⟨ρ, hE, fun Γ' hΓ' => (inspects_covered (st := C6st7) rfl).trans (h Γ' hΓ')⟩

/-- The roots of `{console}` over the store's own context.  `Ctx.caps` is
compiled by well-founded recursion over a measure that mentions the context,
which neither the elaborator nor the kernel unfolds, so this computation runs
through the two clause lemmas `Ctx.capsAtom_var` and `Ctx.capsAtom_cvar`.  No
capture name is involved, so the fuel is `0`. -/
theorem C6_console_caps :
    C6Ctx1.caps 0 [CapAtom.var (.there (.there (.there .here)))]
      = [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] := by
  simp [C6Ctx1, C6Ctx, capTy, Ctx.capsAtom_var, Ctx.capsAtom_cvar, Ctx.capsBound,
    Binding.ty, CaptureSet.weaken, CaptureSet.rename,
    CapAtom.rename, CapBound.weaken, CapBound.rename]

/-- The membership the example instantiates: over the store's own context,
`κ₂` is a root of `{console}`. -/
theorem C6_console_root :
    C6Ctx1.Root (CapAtom.cvar (.there (.there (.there (.there (.there .here))))))
      [CapAtom.var (.there (.there (.there .here)))] :=
  Ctx.Root.of_mem_caps (n := 0) (by rw [C6_console_caps]; decide +kernel)

/-- `κ₂` is therefore a root of the use set of the initial state, as
transported by the run's store extension. -/
theorem C6_covered_root :
    ∃ ρ : Rename ([],c,c,x,x,x,x) ([],c,c,x,x,x,x,x),
      Store.Ext C6Store C6Store1 ρ ∧
        C6Ctx1.Root (CapAtom.cvar (.there (.there (.there (.there (.there .here))))))
          (C6st0.uses.rename ρ) := by
  obtain ⟨ρ, hE, h⟩ := C6_covered
  exact ⟨ρ, hE, h C6Ctx1 C6_store1 _ C6_console_root⟩

/-! ### The second run: no root `κ₂` in the use set, none read -/

/-- The initial state of the second program. -/
def C6st0' : State ([],c,c,x,x,x,x) := ⟨C6Store, .nil, C1prog2⟩

theorem C6st0'_typed : State.Typed C6st0' (Ty.pure .top) :=
  ⟨C6Ctx, Ty.pure .top, C6_store, checkTm_sound (by decide +kernel), .nil⟩

/-- The roots of the use set of the second program, at every fuel: `c1`
resolves to `log`, which resolves to `κ₁`, and `unit` resolves to nothing.  The
fuel plays no part, since no capture name is involved. -/
theorem C6_prog2_caps (n : Nat) :
    C6Ctx.caps n C6st0'.uses
      = [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] := by
  simp [C6st0', C1prog2, C6Ctx, capTy, c1Ty, Atom.root, Ctx.capsAtom_var, Ctx.capsAtom_cvar,
    Ctx.capsBound, Binding.ty, CaptureSet.weaken,
    CaptureSet.rename, CapAtom.rename, CapBound.weaken, CapBound.rename]

/-- The use set of the second program has no root `κ₂`. -/
theorem C6_no_kappa2 :
    ¬ C6Ctx.Root (CapAtom.cvar (.there (.there (.there (.there .here))))) C6st0'.uses := by
  rintro ⟨n, hn⟩
  rw [Ctx.roots_eq_caps, C6_prog2_caps] at hn
  revert hn
  decide +kernel

/-- **C6, effect safety**: no state reachable from the second program reads a
root whose root is `κ₂`. -/
theorem C6_safe {s' : Sig} {st' : State s'} {Γ' : Ctx s'} {x : BVar s' .var}
    (run : C6st0' ⟶* st') (hin : st'.inspects = some x) (hΓ' : ⊢ st'.σ : Γ') :
    ∃ ρ : Rename ([],c,c,x,x,x,x) s', Store.Ext C6Store st'.σ ρ ∧
      ¬ Γ'.Root
        (CapAtom.cvar (ρ.var (.there (.there (.there (.there .here))))))
        [CapAtom.var x] :=
  effect_safety C6st0'_typed C6_store run C6_no_kappa2 hin hΓ'


/-! ## S3, C2 and C7: the capture examples of stage A3a

The three source derivations of `DotMNF.Examples` over the platform prefix
of two rigid capture binders, on this side of the translation.  Each comes
in three parts.

* **The translation is typed.**  `Sᵢ_translated` is `HasTy.translate_typed`
  at the source derivation: the translated term has the translated type in
  the translated context.  It is not decided by the checker.  The type
  translation `Shape.translate` and the term translation `HasTy.translate`
  are compiled by well-founded recursion, so neither reduces in the kernel,
  and `decide +kernel` cannot be run on a goal that mentions them.
* **The erasure is the source term's.**  `Sᵢ_erase` is
  `HasTy.translate_erase` at the same derivation.
* **A target twin, decided by the checker.**  `Sᵢ_client` is the client half
  of the example written directly in the target, in the context the
  translation of the source types produce, and `checkTm … = true` is decided
  in the kernel there.  The negative half of C7 is `checkTm … = false` on
  the same twin with the empty use set and the syntactic capture evidence. -/

/-- `Unit → Unit` in the target. -/
def tArrow : Shape s := .pi (Ty.pure .top) (Ty.pure .top)

/-- The type of a capability in the target. -/
def tCapTy (κ : BVar s .cap) : Ty s := tArrow ^ [CapAtom.cvar κ]

/-- Type label `C`, a capture member. -/
def lC : Label := .typ 3
/-- Term label `elem`. -/
def lelem : Label := .trm 3
/-- Term label `run`. -/
def lrun : Label := .trm 4
/-- Term label `e₁`. -/
def lE1 : Label := .trm 5
/-- Term label `e₂`. -/
def lE2 : Label := .trm 6

example : lC = DotMNF.Examples.lC := rfl
example : lelem = DotMNF.Examples.lelem := rfl
example : lrun = DotMNF.Examples.lrun := rfl
example : lE1 = DotMNF.Examples.le1 := rfl
example : lE2 = DotMNF.Examples.le2 := rfl

/-- The platform context of the three examples is the context of the
platform prefix `Platform.cons (Platform.cons Platform.nil)`. -/
example : DotMNF.Examples.platCtx
    = (DotMNF.Platform.cons (DotMNF.Platform.cons DotMNF.Platform.nil)).ctx := rfl

/-- Its translation is the target platform prefix of two rigid binders. -/
example : DotMNF.Examples.platCtx.translate = (Ctx.nil.consC .star).consC .star := rfl

/-- The platform context is well formed, which is what
`HasTy.translate_typed` asks of it. -/
theorem platWf : DotMNF.Ctx.Wf DotMNF.Examples.platCtx := .consC (.consC .nil)

/-! ### S3 on the target side

`⟦μ(z. {A : □T..□T} ∧ {elem : z.A ^ {}})⟧` is the five-proposition object
type below: the two bounds of the member `A`, the presence of `elem`, the
declared shape of `elem`, and its declared capture set.  The client reads
the field at index `2`, brings it to `z.A` by index `3` and to `□T` by index
`1`, empties its capture set by index `4`, and unboxes at `{f}`. -/

/-- `□((Unit → Unit) ^ {f})` in the target. -/
def S3Box (f : BVar s .var) : Shape s := .box (tArrow ^ [CapAtom.var f])

/-- The telescope of `⟦μ(z. {A : □T..□T} ∧ {elem : z.A ^ {}})⟧`. -/
def S3Tel (f : BVar s .var) : Telescope (s,x) :=
  .cons (.cons (.cons (.cons (.cons .nil
    (.le (S3Box (.there f)) (.sel .here lA)))
    (.le (.sel .here lA) (S3Box (.there f))))
    (.has lelem))
    (.le (.sel .here lelem) (.sel .here lA)))
    (.leC [CapAtom.name .here lelem] [])

/-- The object type of S3. -/
def S3Obj (f : BVar s .var) : Shape s := .obj (S3Tel f)

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, f : (Unit → Unit) ^ {κ₁}, o : ⟦μ(z. …)⟧`. -/
def S3Ctx : Ctx ([],c,c,x,x) :=
  (((Ctx.nil.consC .star).consC .star).cons
    (.opaque (tCapTy (.there .here)))).cons (.opaque (Ty.pure (S3Obj .here)))

/-- The element, read off the object and brought to the boxed type. -/
def S3elem : Tm ([],c,c,x,x) :=
  .cast (.proj (.var .here) lelem (.member (.var .here) (.refl (S3Obj (.there .here))) 2))
    (.capt
      (.trans (.member (.var .here) (.refl (S3Obj (.there .here))) 3)
        (.member (.var .here) (.refl (S3Obj (.there .here))) 1))
      (.member (.var .here) (.refl (S3Obj (.there .here))) 4))

/-- The client of S3: read the element and unbox it at `{f}`. -/
def S3client : Tm ([],c,c,x,x) :=
  .let S3elem
    (.unbox (.var .here) [CapAtom.var (.there (.there .here))]
      (.refl [CapAtom.var (.there (.there .here))]))
    [CapAtom.var (.there .here)]
    (.union (.trans (.capvar (.var .here)) (.elem [] [CapAtom.var (.there (.there .here))]))
      (.refl [CapAtom.var (.there (.there .here))]))

/-- Its type: the unboxed capability, captured at `{f}`. -/
def S3clientTy : Ty ([],c,c,x,x) := tArrow ^ [CapAtom.var (.there .here)]

example : checkTm S3Ctx S3client S3clientTy = true := by decide +kernel

/-- **S3, the target twin.**  The client half of S3, checked by the
structural checker. -/
theorem S3_client : S3Ctx ⊢ S3client : S3clientTy := checkTm_sound (by decide +kernel)

/-- **S3, translated.**  The translation of the source derivation is typed
at the translated type in the translated context. -/
theorem S3_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.S3_typed.translate : DotMNF.Examples.S3Ty.translate :=
  DotMNF.Examples.S3_typed.translate_typed platWf

/-- **S3, erased.**  The translation erases to the source term. -/
theorem S3_erase :
    Tm.erase DotMNF.Examples.S3_typed.translate = DotMNF.Tm.erase DotMNF.Examples.S3tm :=
  DotMNF.HasTy.translate_erase _

/-! ### C7 on the target side

`⟦μ(z. {e₁ : □((Unit→Unit) ^ {κ₁}) ^ {}} ∧ {e₂ : □((Unit→Unit) ^ {κ₂}) ^ {}})⟧`
is six propositions, three per field.  Both capture entries declare the
empty set, which is what makes the container pure.  The client reads the
first field and unboxes it at `{κ₁}`. -/

/-- The telescope of C7's container. -/
def C7Tel (κ1 κ2 : BVar s .cap) : Telescope (s,x) :=
  .cons (.cons (.cons (.cons (.cons (.cons .nil
    (.has lE1))
    (.le (.sel .here lE1) (.box (tCapTy (.there κ1)))))
    (.leC [CapAtom.name .here lE1] []))
    (.has lE2))
    (.le (.sel .here lE2) (.box (tCapTy (.there κ2)))))
    (.leC [CapAtom.name .here lE2] [])

/-- The object type of C7. -/
def C7Obj (κ1 κ2 : BVar s .cap) : Shape s := .obj (C7Tel κ1 κ2)

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, o : ⟦μ(z. …)⟧`. -/
def C7Ctx : Ctx ([],c,c,x) :=
  ((Ctx.nil.consC .star).consC .star).cons
    (.opaque (Ty.pure (C7Obj (.there .here) .here)))

/-- The first element, read off the container and brought to the boxed
type. -/
def C7elem : Tm ([],c,c,x) :=
  .cast
    (.proj (.var .here) lE1
      (.member (.var .here) (.refl (C7Obj (.there (.there .here)) (.there .here))) 0))
    (.capt
      (.member (.var .here) (.refl (C7Obj (.there (.there .here)) (.there .here))) 1)
      (.member (.var .here) (.refl (C7Obj (.there (.there .here)) (.there .here))) 2))

/-- The client of C7: read the first element and unbox it at `{κ₁}`. -/
def C7client : Tm ([],c,c,x) :=
  .let C7elem
    (.unbox (.var .here) [CapAtom.cvar (.there (.there (.there .here)))]
      (.refl [CapAtom.cvar (.there (.there (.there .here)))]))
    [CapAtom.cvar (.there (.there .here))]
    (.union
      (.trans (.capvar (.var .here))
        (.elem [] [CapAtom.cvar (.there (.there (.there .here)))]))
      (.refl [CapAtom.cvar (.there (.there (.there .here)))]))

/-- Its type: the unboxed capability, captured at `{κ₁}`. -/
def C7clientTy : Ty ([],c,c,x) := tArrow ^ [CapAtom.cvar (.there (.there .here))]

example : checkTm C7Ctx C7client C7clientTy = true := by decide +kernel

/-- **C7, the target twin.**  The client half of C7, checked by the
structural checker: unboxing the first element charges `{κ₁}`. -/
theorem C7_client : C7Ctx ⊢ C7client : C7clientTy := checkTm_sound (by decide +kernel)

/-- The same client with the empty use set: the unboxing is annotated `{}`
and its capture evidence is the syntactic inclusion `{κ₁} ⊆ {}`. -/
def C7clientBad : Tm ([],c,c,x) :=
  .let C7elem
    (.unbox (.var .here) [] (.elem [CapAtom.cvar (.there (.there (.there .here)))] []))
    []
    (.union (.trans (.capvar (.var .here)) (.elem [] [])) (.refl []))

/-- **C7, rejected.**  The client does not type with use set `{}`: the
element's own set `{κ₁}` is not below the empty set, and there is no rule
that would put it there over a platform prefix. -/
theorem C7_rejected : checkTm C7Ctx C7clientBad C7clientTy = false := by decide +kernel

/-- **C7, translated.** -/
theorem C7_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.C7_typed.translate : DotMNF.Examples.C7Ty.translate :=
  DotMNF.Examples.C7_typed.translate_typed platWf

/-- **C7, erased.** -/
theorem C7_erase :
    Tm.erase DotMNF.Examples.C7_typed.translate = DotMNF.Tm.erase DotMNF.Examples.C7tm :=
  DotMNF.HasTy.translate_erase _

/-! ### C2 on the target side

`⟦μ(z. {C : {}..{κ₁,κ₂}} ∧ {run : (Unit → Unit) ^ {z.C}})⟧` is five
propositions: the two bounds of the capture member `C`, the presence of
`run`, its declared shape, and its declared capture set `{z.C}`.  The client
reads `run` at index `2`, and the call it makes is charged to `{κ₁,κ₂}` by
`capvar` composed with the upper bound of the capture member, index `1` --
the target's reading of `sc-var` followed by `sc-sel-upper`. -/

/-- The telescope of C2's abstract object type. -/
def C2Tel (κ1 κ2 : BVar s .cap) : Telescope (s,x) :=
  .cons (.cons (.cons (.cons (.cons .nil
    (.leC [] [CapAtom.name .here lC]))
    (.leC [CapAtom.name .here lC]
      [CapAtom.cvar (.there κ1), CapAtom.cvar (.there κ2)]))
    (.has lrun))
    (.le (.sel .here lrun) tArrow))
    (.leC [CapAtom.name .here lrun] [CapAtom.name .here lC])

/-- The abstract object type of C2. -/
def C2Obj (κ1 κ2 : BVar s .cap) : Shape s := .obj (C2Tel κ1 κ2)

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, x : ⟦μ(z. …)⟧ ^ {κ₁,κ₂}, u : Unit`. -/
def C2Ctx : Ctx ([],c,c,x,x) :=
  (((Ctx.nil.consC .star).consC .star).cons
    (.opaque (C2Obj (.there .here) .here
      ^ [CapAtom.cvar (.there .here), CapAtom.cvar .here]))).cons
    (.opaque (Ty.pure .top))

/-- The closure, read off the abstract member. -/
def C2run : Tm ([],c,c,x,x) :=
  .cast
    (.proj (.var (.there .here)) lrun
      (.member (.var (.there .here))
        (.refl (C2Obj (.there (.there (.there .here))) (.there (.there .here)))) 2))
    (.capt
      (.member (.var (.there .here))
        (.refl (C2Obj (.there (.there (.there .here))) (.there (.there .here)))) 3)
      (.member (.var (.there .here))
        (.refl (C2Obj (.there (.there (.there .here))) (.there (.there .here)))) 4))

/-- The client of C2: read the closure off the abstract member and call it.
Its use set is `{κ₁,κ₂}`, by `capvar` and the member's upper bound. -/
def C2client : Tm ([],c,c,x,x) :=
  .let C2run (.app (.var .here) (.var (.there .here)))
    [CapAtom.cvar (.there (.there (.there .here))),
      CapAtom.cvar (.there (.there .here))]
    (.union
      (.trans (.capvar (.var .here))
        (.member (.var (.there (.there .here)))
          (.refl (C2Obj (.there (.there (.there (.there .here))))
            (.there (.there (.there .here))))) 1))
      (.trans (.capvar (.var (.there .here)))
        (.elem [] [CapAtom.cvar (.there (.there (.there (.there .here)))),
          CapAtom.cvar (.there (.there (.there .here)))])))

example : checkTm C2Ctx C2client (Ty.pure .top) = true := by decide +kernel

/-- **C2, the target twin.**  The client half of C2, checked by the
structural checker. -/
theorem C2_client : C2Ctx ⊢ C2client : Ty.pure .top := checkTm_sound (by decide +kernel)

/-- **C2, translated.** -/
theorem C2_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.C2_typed.translate : DotMNF.Examples.C2Ty.translate :=
  DotMNF.Examples.C2_typed.translate_typed platWf

/-- **C2, erased.** -/
theorem C2_erase :
    Tm.erase DotMNF.Examples.C2_typed.translate = DotMNF.Tm.erase DotMNF.Examples.C2tm :=
  DotMNF.HasTy.translate_erase _


end Examples
end FCdot

end Captures
