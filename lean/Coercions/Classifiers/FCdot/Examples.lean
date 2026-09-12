import Coercions.Classifiers.FCdot.Checker
import Coercions.Classifiers.FCdot.LevelInversion
import Coercions.Classifiers.FCdot.Erasure
import Coercions.Classifiers.FCdot.Consistency
import Coercions.Classifiers.FCdot.Prediction
import Coercions.Classifiers.DotMNF.Examples
import Coercions.Classifiers.DotMNF.Erasure
import Coercions.Classifiers.DotToFCdot.Prediction

namespace Classifiers

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

/-! ### Reading an outer binder from inside a scope

A lambda body opens three binders, the body root, the arrow's capture binder
and the parameter, so an outer binder is three steps out.  A codomain and an
object body open two, so an outer binder is two steps out there, and a
domain opens one. -/

/-- An outer binder, read inside a lambda body. -/
abbrev up {s : Sig} {k : Kind} (y : BVar s k) : BVar (Sig.body s) k :=
  .there (.there (.there y))

/-- An outer binder, read inside a codomain or an object body. -/
abbrev up2 {s : Sig} {k : Kind} (y : BVar s k) : BVar ((s,c),x) k := .there (.there y)

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
  .pi (Ty.pure (.sel (.there x) A)) (.ty (Ty.pure (.sel (up2 x) A)))

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
    (.let (.atom (.plain (.cast (.var .here) (badBounds .here E1Res)))) (.atom (.plain (.var .here)))
      [] (.capvar (.var .here)))
    (.elem [CapAtom.var .here] [CapAtom.var .here]))

def E1Ty : Ty [] := Ty.pure (.pi (Ty.pure E1Dom) (.ty (Ty.pure E1Res)))

example : checkTm Ctx.nil E1 E1Ty = true := by decide +kernel

theorem E1_typed : Ctx.nil ⊢ E1 : E1Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E1`. -/
def E1src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E1Dom (.let (.path (.var .here)) (.path (.var .here))))

example : DotMNF.HasTyP [] .nil E1src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E1Dom (.ty DotMNF.Examples.E1Res))) :=
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
def E2Field : Tm ((s,c),x) :=
  .cast
    (.val (.lam [] (Ty.pure (.sel (.there .here) lA)) (.atom (.plain (.var .here)))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.capt (.eqToLe (.symm (.def .here la))) (.elem [] [CapAtom.name .here la]))

def E2Fields : Fields ((s,c),x) :=
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
      (.cast (.val (.plain (.lam (.atom (.plain .var)) (.elem sub_refl))))
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
theorem E2_app : Tm.HasTy E2Ctx2
    (.app (.cast (.var .here) (E2aPi (.there .here)))
      (.cast (.var .here) (LeCo.trans (E2aPi (.there .here)) (E2piA (.there .here)))))
    (Ty.pure (.sel (.there .here) lA)) :=
  .app E2_fun E2_arg

theorem E2_typed : Ctx.nil ⊢ E2 : E2Ty' :=
  .let (.val (.plain E2_value))
    (.let (.proj .var (.member (Tel := E2Tel) .var .refl .here))
      (.cast E2_app (.capt .top .refl))
      (.union (.capvar .var) (.capvar .var)))
    (.union (.capvar .var) (.eqToLe (.member (Tel := E2Tel) .var .refl (.there .here))))

/-- The source term of `DotMNF.Examples.E2`. -/
def E2src : DotMNF.Tm [] :=
  .let (.val (.obj DotMNF.Examples.E2Defs))
    (.let (.proj .here DotMNF.Examples.la) (.app .here .here))

example : DotMNF.HasTyP [] .nil E2src (DotMNF.Ty.capt [] .top) := DotMNF.Examples.E2

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
      (.let (.atom (.plain (.cast (.var .here) (E3sub (up .here))))) (.atom (.plain (.var .here)))
        [] (.capvar (.var .here)))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

def E3Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E3Dom) (.ty (Ty.pure (.pi (Ty.pure tNat) (.ty (Ty.pure tInt))))))

example : checkTm Ctx.nil E3 E3Ty = true := by decide +kernel

theorem E3_typed : Ctx.nil ⊢ E3 : E3Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E3`. -/
def E3src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E3Dom
    (.val (.lam DotMNF.Examples.E3T2 (.let (.path (.var .here)) (.path (.var .here))))))

example : DotMNF.HasTyP [] .nil E3src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E3Dom
      (.ty (DotMNF.Ty.capt [] (.all DotMNF.Examples.E3T2 (.ty DotMNF.Examples.E3T1)))))) :=
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
          (.val (.lam [] (Ty.pure (.sel (.there (up .here)) lA)) (.atom (.plain (.var .here)))
            (.elem [CapAtom.var .here] [CapAtom.var .here])))
          (.app (.var .here)
            (.cast (.var (.there .here))
              (E4IntLe (.there (up (up .here))) (.there (up .here)))))
          [] (.union (.capvar (.var .here)) (.capvar (.var (.there .here)))))
        (.elem [] [CapAtom.var .here])))
      (.elem [] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

def E4Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E4X) (.ty (Ty.pure (.pi (Ty.pure E4S)
    (.ty (Ty.pure (.pi (Ty.pure tInt) (.ty (Ty.pure (.sel (up2 .here) lA))))))))))

example : checkTm Ctx.nil E4 E4Ty = true := by decide +kernel

theorem E4_typed : Ctx.nil ⊢ E4 : E4Ty := checkTm_sound (by decide +kernel)

/-- The source term of `DotMNF.Examples.E4`. -/
def E4src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E4X (.val (.lam DotMNF.Examples.E4S (.val (.lam DotMNF.Examples.E4Int
    (.let (.val (.lam (DotMNF.Ty.capt [] (.sel (.var (.there (up .here))) DotMNF.Examples.lA))
      (.path (.var .here))))
      (.app .here (.there .here))))))))

example : DotMNF.HasTyP [] .nil E4src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4X
      (.ty (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4S
        (.ty (DotMNF.Ty.capt [] (.all DotMNF.Examples.E4Int
          (.ty (DotMNF.Ty.capt [] (.sel (.var (up2 .here)) DotMNF.Examples.lA))))))))))) :=
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
def E5Field : Tm ((s,x,c),x) :=
  .atom (.plain (.cast (.var (up2 .here))
    (.capt (.trans (.top E5AT)
        (.trans (.member (.var (up2 .here)) (.refl E5AT) 0)
          (.eqToLe (.symm (.def .here la)))))
      (.elem [] [CapAtom.name .here la]))))

def E5Fields : Fields ((s,x,c),x) :=
  .cons .nil la E5Field
    (.elem [CapAtom.var (up2 .here)] [CapAtom.var (up2 .here), CapAtom.var .here])

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

def E5Ty : Ty [] := Ty.pure (.pi (Ty.pure E5AT) (.ty (Ty.pure (.sel .here lA))))

example : checkTm Ctx.nil E5 E5Ty = true := by decide +kernel
example : checkTm Ctx.nil E5 (Ty.pure (.pi (Ty.pure E5AT) (.ty (Ty.pure .top)))) = false := by
  decide +kernel

/-- `w : {A : ⊤..⊤}`, the body of the outer lambda. -/
def E5Ctx1 : Ctx (Sig.body ([] : Sig)) := Ctx.body Ctx.nil (Ty.pure E5AT)

/-- `w : {A : ⊤..⊤}, v : {A : ⊤..⊤}`, the context of the object literal. -/
def E5Ctxv : Ctx (Sig.body (Sig.body ([] : Sig))) := Ctx.body E5Ctx1 (Ty.pure E5AT)

theorem E5_value : E5Ctxv ⊢ᵥ .obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields :
    (E5ObjTy .here) ^ [CapAtom.var .here] := by
  have h : Value.HasType E5Ctxv (.obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields)
      ((.obj (Telescope.ofLiteral (E5Wit .here) E5CapWit [la])) ^ [CapAtom.var .here]) :=
    .obj
      (.cons .nil
        (.atom (.plain (.cast .var
          (.capt (.trans .top
            (.trans (.member (Tel := telTyp lA .top .top) .var .refl (.there .here))
              (.eqToLe (.symm (.def rfl))))) (.elem sub_nil)))))
        (.elem sub_head))
  rw [E5Tel_eq] at h
  exact h

/-- `w : {A : ⊤..⊤}, f : ∀(v : {A : ⊤..⊤}) (Obj(z. [z.a ≃ v.A, …]) ^ {v})`. -/
def E5Ctxf : Ctx (Sig.body ([] : Sig),x) :=
  E5Ctx1.cons
    (.opaque (Ty.pure (.pi (Ty.pure E5AT) (.ty ((E5ObjTy .here) ^ [CapAtom.var .here])))))

/-- `f`, at its declared type. -/
theorem E5_f : E5Ctxf ⊢ₐ .var .here :
    Ty.pure (.pi (Ty.pure E5AT) (.ty ((E5ObjTy .here) ^ [CapAtom.var .here]))) := .var

/-- `f w : Obj(z. [z.a ≃ w.A, …]) ^ {w}`: the application renames `v`'s block
and its capture set. -/
theorem E5_app : Tm.HasTy E5Ctxf (.app (.var .here) (.var (.there .here)))
    ((E5ObjTy (.there .here)) ^ [CapAtom.var (.there .here)]) :=
  .app E5_f .var

/-- `w : …, f : …, o : Obj(z. [z.a ≃ w.A, …]) ^ {w}`. -/
def E5Ctxo : Ctx (Sig.body ([] : Sig),x,x) :=
  E5Ctxf.cons (.opaque ((E5ObjTy (.there .here)) ^ [CapAtom.var (.there .here)]))

/-- `o.a`, then `o.a ≃ w.A`: the result mentions neither `let` binder, and its
capture name is discharged by the literal's capture definition. -/
theorem E5_proj : Tm.HasTy E5Ctxo
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

/-- The codomain of `f`, named so that the `lam` rule below has its codomain
given rather than inferred from the body's type through `Cod.underRoot`. -/
def E5Cod : Cod (Sig.body ([] : Sig)) := .ty ((E5ObjTy .here) ^ [CapAtom.var .here])

/-- `f = λ(v : {A : ⊤..⊤}). ν(z. {a = v})`, in the body of the outer lambda. -/
theorem E5_fval : E5Ctx1 ⊢ᵥ
    .lam [] (Ty.pure E5AT) (.val (.obj [CapAtom.var .here] (E5Wit .here) E5CapWit E5Fields))
      (.elem [] [CapAtom.var .here]) :
    (Shape.pi (Ty.pure E5AT) E5Cod) ^ [] :=
  .lam (.val (.plain E5_value)) (.elem sub_nil)

theorem E5_typed : Ctx.nil ⊢ E5 : E5Ty :=
  .val (.plain (.lam
    (.let (.val (.plain E5_fval))
      (.let E5_app E5_proj (.capvar .var))
      (.union (.union (.capvar .var) (.capvar .var)) (.capvar .var)))
    (.elem sub_nil)))

/-- The source term of `DotMNF.Examples.E5`. -/
def E5src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E5AT
    (.let (.val (.lam DotMNF.Examples.E5AT DotMNF.Examples.E5Obj))
      (.let (.app .here (.there .here)) (.proj .here DotMNF.Examples.la))))

example : DotMNF.HasTyP [] .nil E5src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E5AT
      (.ty (DotMNF.Ty.capt [] (.sel (.var .here) DotMNF.Examples.lA))))) :=
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
def E6Field : Tm ((s,x,c),x) :=
  .atom (.plain (.cast
    (.cast (.var (up2 .here)) (co (.eqToLe (.symm (.def .here lT)))))
    (.capt (.eqToLe (.symm (.def .here lv))) (.elem [] [CapAtom.name .here lv]))))

def E6Fields : Fields ((s,x,c),x) :=
  .cons .nil lv E6Field
    (.elem [CapAtom.var (up2 .here)] [CapAtom.var (up2 .here), CapAtom.var .here])

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
      (.atom (.plain (.cast (.cast .var (.capt (.eqToLe (.symm (.def rfl))) .refl))
        (.capt (.eqToLe (.symm (.def rfl))) (.elem sub_nil)))))
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
    (.val (.lam [] (Ty.pure (E8Y (.there .here)))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8And2 (up .here)) 0))
        (.capt (.top (.sel .here la)) (.refl [CapAtom.name .here la])))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

/-- `λ(x). λ(y). y.a`, the `And₁`-then-`Sel-<:` derivation: the same term
after erasure. -/
def E8b : Tm [] :=
  .val (.lam [] (Ty.pure E8X)
    (.val (.lam [] (Ty.pure (E8Y (.there .here)))
      (.cast (.proj (.var .here) la (.member (.var .here) (E8Sel (up .here)) 0))
        (.capt (.top (.sel .here la)) (.refl [CapAtom.name .here la])))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) (⊤ ^ {y∙a})`.  The result is
the projection's own capture name: `y` is an opaque binder, and its declared
telescope has no capture proposition to read the name through. -/
def E8Ty : Ty [] :=
  Ty.pure (.pi (Ty.pure E8X)
    (.ty (Ty.pure (.pi (Ty.pure (E8Y (.there .here)))
      (.ty ((⊤ : Shape (Sig.cod (Sig.cod ([] : Sig)))) ^ [CapAtom.name .here la]))))))

example : checkTm Ctx.nil E8 E8Ty = true := by decide +kernel

theorem E8_typed : Ctx.nil ⊢ E8 : E8Ty := checkTm_sound (by decide +kernel)

example : checkTm Ctx.nil E8b E8Ty = true := by decide +kernel

theorem E8b_typed : Ctx.nil ⊢ E8b : E8Ty := checkTm_sound (by decide +kernel)

/-- The two derivations erase to the same runtime term. -/
theorem E8b_erase_E8 : E8b.erase = E8.erase := rfl

/-- `λ(x). λ(y). y.a` in the source calculus. -/
def E8src : DotMNF.Tm [] :=
  .val (.lam DotMNF.Examples.E8Dom
    (.val (.lam (DotMNF.Examples.E8Ref (.there .here)) (.proj .here DotMNF.Examples.la))))

example : DotMNF.HasTyP [] .nil E8src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E8Dom
      (.ty (DotMNF.Ty.capt [] (.all (DotMNF.Examples.E8Ref (.there .here))
        (.ty (DotMNF.Ty.capt [] .top))))))) :=
  DotMNF.Examples.E8

example : DotMNF.HasTyP [] .nil E8src
    (DotMNF.Ty.capt [] (.all DotMNF.Examples.E8Dom
      (.ty (DotMNF.Ty.capt [] (.all (DotMNF.Examples.E8Ref (.there .here))
        (.ty (DotMNF.Ty.capt [] .top))))))) :=
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
def C3Ctx : Ctx (Sig.body (Sig.body ([],c))) :=
  Ctx.body (Ctx.body C3Ctx0 (Ty.pure (capBad (.there .here))))
    (Ty.pure (boxCap (.there (up .here))))

/-- The bad capture bound, in the context of the two lambdas. -/
example :
    checkCap C3Ctx (badCapBounds (up .here) (up (up .here)))
      [CapAtom.cvar (up (up .here))] [] = true := by
  decide +kernel

theorem C3_badBounds : C3Ctx ⊢ᶜ badCapBounds (up .here) (up (up .here)) :
    [CapAtom.cvar (up (up .here))] ⊑ [] :=
  checkCap_sound (by decide +kernel)

def C3 : Tm ([],c) :=
  .val (.lam [] (Ty.pure (capBad (.there .here)))
    (.val (.lam [] (Ty.pure (boxCap (.there (up .here))))
      (.unbox (.var .here) [] (badCapBounds (up .here) (up (up .here))))
      (.elem [CapAtom.var .here] [CapAtom.var .here])))
    (.elem [] [CapAtom.var .here]))

def C3Ty : Ty ([],c) :=
  Ty.pure (.pi (Ty.pure (capBad (.there .here)))
    (.ty (Ty.pure (.pi (Ty.pure (boxCap (.there (up2 .here))))
      (.ty ((⊤ : Shape (Sig.cod (Sig.cod ([],c)))) ^ [CapAtom.cvar (up2 (up2 .here))]))))))

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
  (.pi (Ty.pure .top) (.ty (Ty.pure .top))) ^ [CapAtom.cvar κ]

/-- A capability: the identity closure, annotated with its platform binder.
Its closing evidence is the syntactic inclusion of the body's use set in the
annotation united with the parameter. -/
def capVal {s : Sig} (κ : BVar s .cap) : Value s :=
  .lam [CapAtom.cvar κ] (Ty.pure .top) (.atom (.plain (.var .here)))
    (.elem [CapAtom.var .here] [CapAtom.cvar (up κ), CapAtom.var .here])

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
      (.ty ((.pi (Ty.pure .top) (.ty (Ty.pure .top))) ^ [CapAtom.var (up2 (.there .here))])))
    ^ [CapAtom.var (.there (.there .here))]

/-- `λ^{log}(u : Unit). let _ = log u in λ^{console}(v : Unit). console v`.
The inner closing evidence is the syntactic inclusion; so is the outer one,
because the outer annotation is the variable `log` itself. -/
def c1val : Value ([],c,c,x,x,x) :=
  .lam [CapAtom.var (.there (.there .here))] (Ty.pure .top)
    (.let (.app (.var (up (.there (.there .here)))) (.var .here))
      (.val (.lam [CapAtom.var (.there (up (.there .here)))] (Ty.pure .top)
        (.app (.var (up (.there (up (.there .here))))) (.var .here))
        (.elem [CapAtom.var (up (.there (up (.there .here)))), CapAtom.var .here]
          [CapAtom.var (up (.there (up (.there .here)))), CapAtom.var .here])))
      [] (.elem [] []))
    (.elem [CapAtom.var (up (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (up (.there (.there .here))), CapAtom.var .here])

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
    (.atom (.plain (.var (.there (.there .here)))))
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
    (.let (.app (.var (up (.there (.there .here)))) (.var .here))
      (.val (.lam [] (Ty.pure .top)
        (.app (.var (up (.there (up (.there .here))))) (.var .here))
        (.elem [CapAtom.var (up (.there (up (.there .here)))), CapAtom.var .here]
          [CapAtom.var .here])))
      [] (.elem [] []))
    (.elem [CapAtom.var (up (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (up (.there (.there .here))), CapAtom.var .here])

/-- The type the bad closure claims: the inner arrow is pure. -/
def c1badTy : Ty ([],c,c,x,x,x) :=
  (.pi (Ty.pure .top) (.ty ((.pi (Ty.pure .top) (.ty (Ty.pure .top))) ^ [])))
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
  .cons (.cons (.cons (.cons (.consC (.consC .nil rfl) rfl)
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel)))
    trivial (checkValue_sound (by decide +kernel))

/-- The initial state of the good program. -/
def C6st0 : State ([],c,c,x,x,x,x) := ⟨C6Store, .nil, C1prog1⟩

theorem C6st0_typed : State.Typed C6st0 (Ty.pure .top) :=
  ⟨C6Ctx, .ty (Ty.pure .top), C6_store, checkTm_sound (by decide +kernel), .nil⟩

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
    (.app (.var (up (.there (.there (.there .here))))) (.var .here))
    (.elem [CapAtom.var (up (.there (.there (.there .here)))), CapAtom.var .here]
      [CapAtom.var (up (.there (.there (.there .here)))), CapAtom.var .here]))

/-- The inner closure once the let binder of `c1`'s body is gone: the value the
run allocates. -/
def C6inner : Value ([],c,c,x,x,x,x) :=
  .lam [CapAtom.var (.there (.there .here))] (Ty.pure .top)
    (.app (.var (up (.there (.there .here)))) (.var .here))
    (.elem [CapAtom.var (up (.there (.there .here))), CapAtom.var .here]
      [CapAtom.var (up (.there (.there .here))), CapAtom.var .here])

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
  ⟨C6Store, C6K0 ▹ .let C6inner0 [] (.elem [] []), .atom (.plain (.var (.there .here)))⟩

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
      ((.pi (Ty.pure .top) (.ty (Ty.pure .top))) ^ [CapAtom.var (.there (.there .here))])
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
  Ctx.Root.of_mem_caps (n := 0)
    (a := CapAtom.cvar (.there (.there (.there (.there (.there .here))))))
    (by rw [C6_console_caps]; decide +kernel) (Ctx.admitsB_top _ _)

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
  ⟨C6Ctx, .ty (Ty.pure .top), C6_store, checkTm_sound (by decide +kernel), .nil⟩

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
  -- `C6Ctx` is a store context: it has no scope root, so `roots` is `caps`
  have hroots : C6Ctx.roots n C6st0'.uses = C6Ctx.caps n C6st0'.uses := by
    rw [Ctx.roots_eq_caps_of_rootFree rfl (by rw [C6_prog2_caps]; decide)]
    exact Ctx.filter_map_base_eq_self (by rw [C6_prog2_caps]; decide)
  rw [hroots, C6_prog2_caps] at hn
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
def tArrow : Shape s := .pi (Ty.pure .top) (.ty (Ty.pure .top))

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
/-- Term label `read`. -/
def lread : Label := .trm 7
/-- Term label `next`. -/
def lnext : Label := .trm 8

example : lC = DotMNF.Examples.lC := rfl
example : lelem = DotMNF.Examples.lelem := rfl
example : lrun = DotMNF.Examples.lrun := rfl
example : lE1 = DotMNF.Examples.le1 := rfl
example : lE2 = DotMNF.Examples.le2 := rfl
example : lread = DotMNF.Examples.lread := rfl
example : lnext = DotMNF.Examples.lnext := rfl

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

/-! ## S1, S2 and C5: the examples of stage A3b

The two source derivations of `DotMNF.Examples` that are written with `any`
and typed at the expanded type, on this side of the translation, and the
packing of S2 seen from the target.

`any` never reaches the target: it is a source notation, expanded before the
program is typed, so the translated types below are the translations of the
expanded types.  The parts are the ones A3a used.  `Sᵢ_translated` is
`HasTy.translate_typed` at the source derivation and `Sᵢ_erase` is
`HasTy.translate_erase`; neither is decided, because `Shape.translate` and
`HasTy.translate` are compiled by well-founded recursion and do not reduce
in the kernel.  The twins that *are* decided are written directly in the
target. -/

/-- **S1, translated.**  The translation of the source derivation is typed
at the translated type in the translated context. -/
theorem S1_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.S1_typed.translate : DotMNF.Examples.S1ProgTy.translate :=
  DotMNF.Examples.S1_typed.translate_typed platWf

/-- **S1, erased.**  The translation erases to the source term. -/
theorem S1_erase :
    Tm.erase DotMNF.Examples.S1_typed.translate = DotMNF.Tm.erase DotMNF.Examples.S1tm :=
  DotMNF.HasTy.translate_erase _

/-- **S2, translated.** -/
theorem S2_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.S2_typed.translate : DotMNF.Examples.S2ProgTy.translate :=
  DotMNF.Examples.S2_typed.translate_typed platWf

/-- **S2, erased.** -/
theorem S2_erase :
    Tm.erase DotMNF.Examples.S2_typed.translate = DotMNF.Tm.erase DotMNF.Examples.S2tm :=
  DotMNF.HasTy.translate_erase _


/-! ### S1 on the target side: the argument at the capture parameter

The one step of S1 that the capture discipline turns on is the argument:
the operation is declared at `{fs}` and the parameter type asks for
`{cp.C}`, and the *lower* bound of the caller's precise capture member is
what puts one below the other.  In the target that bound is `member` at
index `0` of the capture parameter's telescope, and the argument is an atom
under one cast.  The shape of the operation plays no part, so the twin uses
`⊤ → ⊤` for it. -/

/-- `⟦μ(c. {C : {fs}..{fs}})⟧`: the lower bound at index `0`, the upper at
index `1`. -/
def S1CPTel (fs : BVar s .cap) : Telescope (s,x) :=
  .cons (.cons .nil (.leC [CapAtom.cvar (.there fs)] [CapAtom.name .here lC]))
    (.leC [CapAtom.name .here lC] [CapAtom.cvar (.there fs)])

/-- The capture parameter object in the target. -/
def S1CPObj (fs : BVar s .cap) : Shape s := .obj (S1CPTel fs)

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, cp : ⟦μ(c. {C : {fs}..{fs}})⟧, op : (⊤ → ⊤) ^ {κ₁}`. -/
def S1Ctx : Ctx ([],c,c,x,x) :=
  (((Ctx.nil.consC .star).consC .star).cons
    (.opaque (Ty.pure (S1CPObj (.there .here))))).cons
    (.opaque (tCapTy (.there (.there .here))))

/-- The argument, recaptured at the capture parameter's name. -/
def S1argTm : Tm ([],c,c,x,x) :=
  .atom (.plain (.cast (.var .here)
    (.capt (.refl tArrow)
      (.member (.var (.there .here)) (.refl (S1CPObj (.there (.there (.there .here))))) 0))))

/-- Its type: the operation at `{cp.C}`, which is what `withFile` asks
for. -/
def S1argTy : Ty ([],c,c,x,x) := tArrow ^ [CapAtom.name (.there .here) lC]

example : checkTm S1Ctx S1argTm S1argTy = true := by decide +kernel

/-- **S1, the target twin.**  The operation declared at `{fs}` is an
operation at `{cp.C}`, by the lower bound of the caller's precise capture
member. -/
theorem S1_client : S1Ctx ⊢ S1argTm : S1argTy := checkTm_sound (by decide +kernel)
/-! ### C5: the existential result, the packing seen from the target

The callee of S2 returns a literal that defines the capture member `C` as
`{fs}` and declares its field `next` at `{i.C}`.  Its translated capture
witnesses are therefore `Wᶜ = [C ↦ {fs}, next ↦ {self∙C}]`, and the
morphism of its `litCo` turns the single capture equality of the member into
the two inclusions the declared type asks for, the lower one through a
flipped hole.  Both facts are read off the translation itself below.

The packing is then one object coercion: from the literal's precise
telescope, whose capture block is two equalities, to the abstract iterator,
whose capture block is `{} ⊑ᶜ self∙C` and `self∙C ⊑ᶜ {fs}`.  The caller of
S2 never sees `{fs}` at the literal: it reads the member's upper bound
instead, which is `member` at index `1` of the declared telescope. -/

/-- `⟦(∀(v : ⊤) (⊤ ^ {i.C}))⟧`, the shape of `next`, under the self. -/
def C5NextShape : Shape (s,x) :=
  .pi (Ty.pure .top) (.ty (.top ^ [CapAtom.name (up2 .here) lC]))

/-- The capture witnesses of the callee's literal, read off the source
declaration shape by the translation: the member's definition and the
field's declared capture set.  This is the plan's
`Wᶜ = [C ↦ {fs}, next ↦ {self∙C}]`. -/
theorem C5_capWitnesses {s : Sig} (fs : BVar s .cap) :
    (DotMNF.Examples.S2PreAt (s := (s,x)) .here (.there fs)).capWitnesses
      = .cons (.cons .nil lC [CapAtom.cvar (.there fs)]) lnext
          [CapAtom.name .here lC] := by
  simp [DotMNF.Shape.capWitnesses, DotMNF.Examples.S2PreAt, CapWitnesses.append,
    DotMNF.CaptureSet.translate, DotMNF.CapAtom.translate?, DotMNF.Examples.unitTy, lC, lnext,
    DotMNF.Examples.lC, DotMNF.Examples.lnext]

/-- The block witnesses of the same literal: the translated shape of its one
field. -/
theorem C5_witnesses {s : Sig} (fs : BVar s .cap) :
    (DotMNF.Examples.S2PreAt (s := (s,x)) .here (.there fs)).witnesses
      = .cons .nil lnext C5NextShape := by
  simp [DotMNF.Shape.witnesses, DotMNF.Examples.S2PreAt, Witnesses.append,
    DotMNF.Shape.translate, DotMNF.CaptureSet.translate, DotMNF.CapAtom.translate?,
    DotMNF.Examples.unitTy, C5NextShape, lC, lnext, DotMNF.Examples.lC, DotMNF.Examples.lnext]

/-- The morphism of the literal's `litCo`, at the counters `litCo` starts it
with (`0` definition equalities, `1` capture equality below the block, `3`
presences below both).  The capture member's block is the pair
`eqSymC 1, eqC 1`: the one capture equality of the precise telescope, read
in both directions, is what the two declared inclusions are made of.  The
field's block is `has 3, eq 0, eqC 2`. -/
theorem C5_litMorphism {s : Sig} (fs : BVar s .cap) :
    (DotMNF.litMorphism (DotMNF.Examples.S2PreAt (s := (s,x)) .here (.there fs)) 0 1 3).1
      = Morphism.append
          (.leC (.leC .nil .nil (.eqSymC 1) .nil) .nil (.eqC 1) .nil)
          (.leC (.le (.has .nil 3) .none (.eq 0) .none) .nil (.eqC 2) .nil) := by
  simp [DotMNF.litMorphism, DotMNF.Examples.S2PreAt, DotMNF.Shape.fieldLabels]

/-! #### The twin -/

/-- The block witnesses of the twin. -/
def C5Wit : Witnesses (s,x) := .cons .nil lnext C5NextShape

/-- Its capture witnesses: `[C ↦ {fs}, next ↦ {self∙C}]`. -/
def C5CapWit (fs : BVar s .cap) : CapWitnesses (s,x) :=
  .cons (.cons .nil lC [CapAtom.cvar (.there fs)]) lnext [CapAtom.name .here lC]

/-- The literal's precise telescope: one definition equality, the two
capture equalities, and the presence of the field. -/
def C5PreTel (fs : BVar s .cap) : Telescope (s,x) :=
  .cons (.cons (.cons (.cons .nil
    (.eq (.sel .here lnext) C5NextShape))
    (.eqC [CapAtom.name .here lC] [CapAtom.cvar (.there fs)]))
    (.eqC [CapAtom.name .here lnext] [CapAtom.name .here lC]))
    (.has lnext)

theorem C5PreTel_eq (fs : BVar s .cap) :
    Telescope.ofLiteral C5Wit (C5CapWit fs) [lnext] = C5PreTel fs := by
  simp [Telescope.ofLiteral, CapWitnesses.eqEntries, CapWitnesses.eqEntriesOf,
    Witnesses.eqEntries, Witnesses.eqEntriesOf, Telescope.hasEntries,
    Witnesses.get, CapWitnesses.get, C5Wit, C5CapWit, C5PreTel, lC, lnext]

/-- The declared telescope of `⟦Iterator⟧`: the two bounds of the capture
member, the presence of `next`, its shape, and its declared capture set. -/
def C5Tel (fs : BVar s .cap) : Telescope (s,x) :=
  .cons (.cons (.cons (.cons (.cons .nil
    (.leC [] [CapAtom.name .here lC]))
    (.leC [CapAtom.name .here lC] [CapAtom.cvar (.there fs)]))
    (.has lnext))
    (.le (.sel .here lnext) C5NextShape))
    (.leC [CapAtom.name .here lnext] [CapAtom.name .here lC])

/-- The abstract iterator in the target. -/
def C5Obj (fs : BVar s .cap) : Shape s := .obj (C5Tel fs)

/-- The morphism of the packing: the member's lower bound comes from the
capture equality flipped and weakened by `{} ⊆ {fs}`, its upper bound from
the same equality read forwards, and the field's three propositions from the
literal's own presence, definition and capture equalities. -/
def C5packMorph (fs : BVar s .cap) : Morphism s :=
  .leC
    (.le
      (.has
        (.leC
          (.leC .nil (.cons (.closed (.elem [] [CapAtom.cvar fs])) .nil) (.eqSymC 1) .nil)
          .nil (.eqC 1) .nil)
        3)
      .none (.eq 0) .none)
    .nil (.eqC 2) .nil

/-- The packing coercion. -/
def C5packCo (fs : BVar s .cap) : ShapeCo s := .obj (C5PreTel fs) (C5packMorph fs)

/-- The field of the twin: the identity closure, cast to the field's own
name and capture name. -/
def C5FieldTm : Tm ((s,c),x) :=
  .cast
    (.val (.lam [] (Ty.pure .top)
      (.cast (.atom (.plain (.var .here)))
        (.capt (.refl .top) (.elem [] [CapAtom.name (up .here) lC])))
      (.refl [CapAtom.var .here])))
    (.capt (.eqToLe (.symm (.def .here lnext))) (.elem [] [CapAtom.name .here lnext]))

def C5Fields : Fields ((s,c),x) :=
  .cons .nil lnext C5FieldTm (.elem [] [CapAtom.var .here])

/-- The callee's literal in the target: pure, with the capture witnesses the
translation reads off the declaration shape. -/
def C5lit (fs : BVar s .cap) : Value s := .obj [] C5Wit (C5CapWit fs) C5Fields

/-- Its precise type. -/
def C5PreTy (fs : BVar s .cap) : Ty s := Ty.pure (.obj (C5PreTel fs))

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, u : ⊤`, the context of the callee's body. -/
def C5Ctx : Ctx ([],c,c,x) :=
  ((Ctx.nil.consC .star).consC .star).cons (.opaque (Ty.pure .top))

/-- `fs` is `κ₁` there. -/
def C5fs : BVar ([],c,c,x) .cap := .there (.there .here)

/-- The set the result is packed at: `{fs, u}`, the reading of the result
`any`. -/
def C5D : CaptureSet ([],c,c,x) := [CapAtom.cvar C5fs, CapAtom.var .here]

example : checkValue C5Ctx (C5lit C5fs) (C5PreTy C5fs) = true := by decide +kernel

/-- The literal is typed at its precise type. -/
theorem C5_literal : C5Ctx ⊢ᵥ C5lit C5fs : C5PreTy C5fs :=
  checkValue_sound (by decide +kernel)

example : checkLe C5Ctx (.capt (C5packCo C5fs) (.elem [] C5D))
    (C5PreTy C5fs) ((C5Obj C5fs) ^ C5D) = true := by decide +kernel

/-- **C5, the packing.**  The literal, cast by the packing coercion, is the
abstract iterator at `{fs, u}`: the member's `{fs}` is behind the two
inclusions of the declared capture block, and no capture variable of the
literal is left in the type. -/
theorem C5_packing : C5Ctx ⊢ᵥ .cast (C5lit C5fs) (.capt (C5packCo C5fs) (.elem [] C5D)) :
    (C5Obj C5fs) ^ C5D :=
  .cast C5_literal (checkLe_sound (by decide +kernel))

/-! #### The caller, from the target's side

The caller reads `next` off the abstract iterator and calls it.  Its capture
evidence is `capvar` at the closure it just read, composed with `member` at
index `1` of the declared telescope, which is the member's upper bound.  No
`capvar` at the literal's own variable appears, and `{fs}` is named only
where the declared bound names it. -/

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗, u : ⊤, it : ⟦Iterator⟧ ^ {κ₁, u}`. -/
def C5CCtx : Ctx ([],c,c,x,x) :=
  (((Ctx.nil.consC .star).consC .star).cons (.opaque (Ty.pure .top))).cons
    (.opaque ((C5Obj (.there (.there .here)))
      ^ [CapAtom.cvar (.there (.there .here)), CapAtom.var .here]))

/-- `it.next`, read off the abstract member. -/
def C5runTm : Tm ([],c,c,x,x) :=
  .cast
    (.proj (.var .here) lnext
      (.member (.var .here) (.refl (C5Obj (.there (.there (.there .here))))) 2))
    (.capt
      (.member (.var .here) (.refl (C5Obj (.there (.there (.there .here))))) 3)
      (.member (.var .here) (.refl (C5Obj (.there (.there (.there .here))))) 4))

/-- The caller: `let n = it.next in n u`, charged to `{κ₁}` by `capvar` and
the member's upper bound. -/
def C5clientTm : Tm ([],c,c,x,x) :=
  .let C5runTm (.app (.var .here) (.var (.there (.there .here))))
    [CapAtom.cvar (.there (.there (.there .here)))]
    (.union
      (.trans (.capvar (.var .here))
        (.member (.var (.there .here))
          (.refl (C5Obj (.there (.there (.there (.there .here)))))) 1))
      (.trans (.capvar (.var (.there (.there .here))))
        (.elem [] [CapAtom.cvar (.there (.there (.there (.there .here))))])))

/-- Its type: the answer, at the iterator's own capture name. -/
def C5clientTy : Ty ([],c,c,x,x) := .top ^ [CapAtom.name .here lC]

example : checkTm C5CCtx C5clientTm C5clientTy = true := by decide +kernel

/-- **C5, the caller as a target twin.**  Checked by the structural
checker. -/
theorem C5_client : C5CCtx ⊢ C5clientTm : C5clientTy := checkTm_sound (by decide +kernel)


/-! ## X1, X2 and X3: levels and the universal root

The three examples of stage B0.  They use no term former.  The level rule
reads only the shape of the context, so `Ctx.isRootB` and `Ctx.lvlLeB` decide
every side condition in the kernel, and every verdict below is a `decide`.

The universal root `⊤ᶜ` is the local root of the whole program.  A binder
that sits inside no scope is at the outermost level, so `⊤ᶜ` absorbs it (X1).
A binder introduced inside a scope is not at the outermost level, so `⊤ᶜ`
does not absorb it, while the scope's own root does (X2).  Nothing at all
puts such a binder below an enclosing root (X3). -/

/-! ### X1, inner absorbs outer

The context `κ₁ ⊑ᶜ ∗, x : ⊤ ^ {κ₁}` opens no scope, so every one of its
binders is at the outermost level and the universal root is above it.  This
is the shape of a platform prefix. -/

/-- The context of X1: one rigid capability and one program binder. -/
def X1Ctx : Ctx ([],c,x) :=
  Ctx.cons (Ctx.consC Ctx.nil .star) (.opaque (.top ^ [CapAtom.cvar .here]))

/-- The rigid capability of X1. -/
def X1κ₁ : BVar ([],c,x) .cap := .there .here

/-- The program binder of X1. -/
def X1x : BVar ([],c,x) .var := .here

/-- X1 opens no scope, so its innermost root is the universal one. -/
example : X1Ctx.root? = none := by decide

/-- The universal root is a root. -/
example : X1Ctx.isRootB ⊤ᶜ = true := by decide

/-- Both binders of X1 are at the outermost level. -/
example : X1Ctx.lvlLeB (CapAtom.cvar X1κ₁) ⊤ᶜ = true := by decide

example : X1Ctx.lvlLeB (CapAtom.var X1x) ⊤ᶜ = true := by decide

/-- **X1, inner absorbs outer.**  A platform capability, and a program binder
that captures it, are both at the outermost level, so the level rule puts
each below the universal root. -/
theorem X1_inner_absorbs_outer :
    (X1Ctx ⊢ᶜ .level (.cvar X1κ₁) ⊤ᶜ : [CapAtom.cvar X1κ₁] ⊑ [⊤ᶜ]) ∧
    (X1Ctx ⊢ᶜ .level (.var X1x) ⊤ᶜ : [CapAtom.var X1x] ⊑ [⊤ᶜ]) :=
  ⟨.level (by decide) (by decide), .level (by decide) (by decide)⟩

/-- The checker agrees, in the kernel. -/
example : checkCap X1Ctx (.level (.cvar X1κ₁) ⊤ᶜ) [CapAtom.cvar X1κ₁] [⊤ᶜ] = true := by
  decide +kernel

example : checkCap X1Ctx (.level (.var X1x) ⊤ᶜ) [CapAtom.var X1x] [⊤ᶜ] = true := by
  decide +kernel

/-! ### X2, outer does not absorb inner

The nested context `κ₁ ⊑ᶜ ∗, κ_S ⊚, κ₂ ⊑ᶜ ∗`: a rigid capability at the
outermost level, then a scope root, then a rigid capability introduced inside
that scope.  This is the nesting of `scoped-capabilities.md:93-106`, with
`⊤ᶜ` for the page's outermost `any`.

The scope root `κ_S` absorbs what is outside it, `κ₁` and `⊤ᶜ` alike, and the
universal root does not absorb what is inside it, neither `κ_S` itself nor
`κ₂`. -/

/-- The context of X2 and X3: rigid, root, rigid. -/
def X2Ctx : Ctx ([],c,c,c) :=
  Ctx.consC (Ctx.consC (Ctx.consC Ctx.nil .star) .root) .star

/-- The outer rigid capability of X2, outside the scope. -/
def X2κ₁ : BVar ([],c,c,c) .cap := .there (.there .here)

/-- The scope root of X2. -/
def X2κS : BVar ([],c,c,c) .cap := .there .here

/-- The rigid capability of X2, introduced inside the scope. -/
def X2κ₂ : BVar ([],c,c,c) .cap := .here

/-- `κ_S` is a root and the two rigid binders are not. -/
example : X2Ctx.isRootB (CapAtom.cvar X2κS) = true := by decide

example : X2Ctx.isRootB (CapAtom.cvar X2κ₁) = false := by decide

example : X2Ctx.isRootB (CapAtom.cvar X2κ₂) = false := by decide

/-- The innermost root of X2 is `κ_S`, and `κ₂` is at that level. -/
example : X2Ctx.root? = some X2κS := by decide

example : X2Ctx.lvl X2κ₂ = some X2κS := by decide

/-- **X2, outer does not absorb inner.**  Four parts.  What is outside the
scope is below the scope's root, the universal root included, and what is
inside the scope is not below the universal root, the scope's own root
included. -/
theorem X2_outer_not_inner :
    (X2Ctx ⊢ᶜ .level (.cvar X2κ₁) (.cvar X2κS) :
      [CapAtom.cvar X2κ₁] ⊑ [CapAtom.cvar X2κS]) ∧
    (X2Ctx ⊢ᶜ .level ⊤ᶜ (.cvar X2κS) : [⊤ᶜ] ⊑ [CapAtom.cvar X2κS]) ∧
    ¬ X2Ctx.LvlLe (CapAtom.cvar X2κS) ⊤ᶜ ∧
    ¬ X2Ctx.LvlLe (CapAtom.cvar X2κ₂) ⊤ᶜ :=
  ⟨.level (by decide) (by decide), .level (by decide) (by decide),
    by decide, by decide⟩

/-- The checker agrees on all four, in the kernel: it accepts the two that go
outward and rejects the two that go inward. -/
example : checkCap X2Ctx (.level (.cvar X2κ₁) (.cvar X2κS))
    [CapAtom.cvar X2κ₁] [CapAtom.cvar X2κS] = true := by decide +kernel

example : checkCap X2Ctx (.level ⊤ᶜ (.cvar X2κS)) [⊤ᶜ] [CapAtom.cvar X2κS] = true := by
  decide +kernel

example : checkCap X2Ctx (.level (.cvar X2κS) ⊤ᶜ) [CapAtom.cvar X2κS] [⊤ᶜ] = false := by
  decide +kernel

example : checkCap X2Ctx (.level (.cvar X2κ₂) ⊤ᶜ) [CapAtom.cvar X2κ₂] [⊤ᶜ] = false := by
  decide +kernel

/-! ### X3, nothing escapes a scope

`no_inner_escape` applied at `κ₂` and `⊤ᶜ` on the context of X2: no closed
evidence at all, and not only no `level` step, puts the binder introduced
inside the scope below the enclosing root.

The three level premises are decided.  The fourth premise is a typed store,
and at stage B0 no store types this context: a store binds capabilities and
never scopes, so a store context has no root binder
(`Store.Typed.rootFree`), and X2's context has one.  That is the second part
below, and it is why X3 holds vacuously here.  The escape gets its content in
stage B1, where a lambda body becomes a scope and a store slot can sit under
a root the run itself provides.  The argument run there is this one. -/

/-- **X3, nothing escapes a scope.**  Over any store that types the nested
context, no capture evidence puts the rigid binder introduced inside the
scope below the universal root. -/
theorem X3_no_escape {σ : Store ([],c,c,c)} (hσ : ⊢ σ : X2Ctx) :
    ¬ ∃ f : CapCo ([],c,c,c), X2Ctx ⊢ᶜ f : [CapAtom.cvar X2κ₂] ⊑ [⊤ᶜ] :=
  no_inner_escape hσ (by decide) (by decide) (by decide)

/-- **X3, the second part.**  At stage B0 the hypothesis of `X3_no_escape` is
unavailable for this context: a store context has no scope root, and X2's
context opens one. -/
theorem X3_no_store : ¬ ∃ σ : Store ([],c,c,c), ⊢ σ : X2Ctx := by
  rintro ⟨σ, hσ⟩
  have h : X2Ctx.root? = none := hσ.rootFree
  exact absurd h (by decide)



/-! ## B1: the arrow, the scope and the escape

The examples of stage B1.  A lambda body is a scope now: `Ctx.body Γ T`
binds the body root, then the arrow's capture binder, then the parameter,
so the parameter and the arrow binder are at one level and that level is
the body root.  Everything below reads off that one fact.

`C2_typed` is the regression test that the new binders are inert where
nothing names them.  `X4` rejects the `withFile` escape, and `X5` shows
that the rejection is the binder order and not an accident.  `S2_level`
and `C5a_level` are the two acceptance tests, the caller's side and the
callee's side, of the level step that puts a concrete assigned set below a
scope root. -/

/-- **T-B1.8, scope order.**  In `Γ.body T` the parameter is `.here`, the
arrow's capture binder is `.there .here` and the body root is
`.there (.there .here)`.  The parameter and the arrow binder are at one
level, and that level is the body root.  Both sides compute, so this is
`rfl`.  The four conjuncts are `Ctx.body_lvl_param`, `Ctx.body_lvl_arrow`,
`Ctx.body_lookupCap_arrow` and the bound of the root, collected here so
that the examples below can cite one name. -/
theorem scope_order {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .var) .here = some (.there (.there .here)) ∧
    (Γ.body T).lvl (k := .cap) (.there .here) = some (.there (.there .here)) ∧
    (Γ.body T).lookupCap (.there .here) = .star ∧
    (Γ.body T).lookupCap (.there (.there .here)) = .root :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### C2, the literal: the class root outside the self

The client half of C2 is above and is untouched by the arrow: it reads
`{x.C}`, a capture name.  The literal half is written here, because it is
where the new binders show.  `Ctx.objBody` binds the class root and then
the self, so the fields sit under both, and the witnesses, which generate
the literal's own type, sit under neither.

`Wᶜ` is `[C ↦ {κ₁}, run ↦ {self∙C}]` and the literal carries the assigned
set `{κ₁}`.  Nothing in the literal names the class root, which is the
point: the binder is inert. -/

/-- The block witnesses of C2's literal: the shape of `run`. -/
def C2Wit : Witnesses (s,x) := .cons .nil lrun tArrow

/-- Its capture witnesses, `[C ↦ {κ₁}, run ↦ {self∙C}]`. -/
def C2CapWit (κ1 : BVar s .cap) : CapWitnesses (s,x) :=
  .cons (.cons .nil lC [CapAtom.cvar (.there κ1)]) lrun [CapAtom.name .here lC]

/-- The one field of C2: the identity closure, cast to the field's own
block name and capture name.  It sits under the class root and the self. -/
def C2FieldTm : Tm ((s,c),x) :=
  .cast
    (.val (.lam [] (Ty.pure .top) (.atom (.plain (.var .here))) (.refl [CapAtom.var .here])))
    (.capt (.eqToLe (.symm (.def .here lrun))) (.elem [] [CapAtom.name .here lrun]))

def C2Fields (κ1 : BVar s .cap) : Fields ((s,c),x) :=
  .cons .nil lrun C2FieldTm
    (.elem [] [CapAtom.cvar (.there (.there κ1)), CapAtom.var .here])

/-- The literal `ν^{κ₁}(W ; Wᶜ ; F)`. -/
def C2lit (κ1 : BVar s .cap) : Value s :=
  .obj [CapAtom.cvar κ1] C2Wit (C2CapWit κ1) (C2Fields κ1)

/-- Its precise type, generated from the witnesses and the fields. -/
def C2LitTy (κ1 : BVar s .cap) : Ty s :=
  (Shape.obj (Telescope.ofLiteral C2Wit (C2CapWit κ1) [lrun])) ^ [CapAtom.cvar κ1]

/-- `κ₁ ⊑ᶜ ∗, κ₂ ⊑ᶜ ∗`, the context of the literal. -/
def C2LitCtx : Ctx ([],c,c) := (Ctx.nil.consC .star).consC .star

/-- `κ₁` there. -/
def C2κ₁ : BVar ([],c,c) .cap := .there .here

/-- The class root is outside the self: in the object body the innermost
root is `.there .here`, and the self, at `.here`, is at that level. -/
example : (C2LitCtx.objBody (C2LitTy C2κ₁) C2Wit (C2CapWit C2κ₁) [lrun]).root?
    = some (.there .here) := by decide

example : (C2LitCtx.objBody (C2LitTy C2κ₁) C2Wit (C2CapWit C2κ₁) [lrun]).lvl
    (k := .var) .here = some (.there .here) := by decide

example : checkValue C2LitCtx (C2lit C2κ₁) (C2LitTy C2κ₁) = true := by decide +kernel

/-- **C2, the literal.**  It is typed at its precise type in a context that
opens no scope.  The class root and the arrow's capture binder are both
inert here: no witness, no field and no type names either. -/
theorem C2_typed : C2LitCtx ⊢ᵥ C2lit C2κ₁ : C2LitTy C2κ₁ :=
  checkValue_sound (by decide +kernel)

/-! ### X4, the `withFile` escape, rejected

The page's program is `withFile[() => File^]("test.txt"): f => () => f`.
The outer lambda's body is typed in `Γ, κ_b ⊚, κ_f ⊑ᶜ ∗, f : File ^ {κ_f}`,
which is `Ctx.body Γ (File ^ {κ_f})`.  The inner lambda's closing evidence
forces its assigned set to hold `f`, so reaching the expected type needs
`{f} ⊑ᶜ {r}` for the root `r` of the scope outside the whole call, and that
root is `⊤ᶜ` when the call is at the top level.

Two theorems, both store free.  `X4_no_level` decides that the premise of
the level rule is false there, at `⊤ᶜ` and at an older root alike.
`X4_no_escape` is an instance of `level_inversion`: no member-free evidence
at all puts `{f}` below `{⊤ᶜ}`, because the binder set of `f` resolves to
the arrow binder `κ_f`, whose level is the body root.  The page's own
consequence for the program is `escaped().read()`, a use after close. -/

/-- `File ^ {κ_f}`, the domain of `withFile`'s callback: the file, captured
at the arrow's own capture binder. -/
def X4File : Dom [] := .top ^ [CapAtom.cvar .here]

/-- The body of the callback: `κ_b ⊚, κ_f ⊑ᶜ ∗, f : File ^ {κ_f}`. -/
def X4Ctx : Ctx (Sig.body []) := Ctx.body Ctx.nil X4File

/-- The parameter `f`. -/
def X4f : BVar (Sig.body []) .var := .here

/-- The arrow's capture binder `κ_f`. -/
def X4κf : BVar (Sig.body []) .cap := .there .here

/-- The body root `κ_b`. -/
def X4κb : BVar (Sig.body []) .cap := .there (.there .here)

/-- `f` and `κ_f` are at one level, and that level is the body root.  This
is `scope_order` at this context. -/
example : X4Ctx.lvl X4f = some X4κb ∧ X4Ctx.lvl X4κf = some X4κb := ⟨rfl, rfl⟩

/-- The same escape one scope further in: an outer scope root `κ_out`, then
the callback's body. -/
def X4OuterCtx : Ctx (Sig.body ([],c)) := Ctx.body (Ctx.nil.consC .root) X4File.weaken

/-- `κ_out`, the root of the scope outside the call. -/
def X4κout : BVar (Sig.body ([],c)) .cap := .there (.there (.there .here))

/-- **X4, no level step.**  The level rule does not fire on `f` at the root
outside the call.  It does not fire at the universal root, and it does not
fire at an older scope root either: the level of `f` is the body root, and
the body root is inside both. -/
theorem X4_no_level :
    ¬ X4Ctx.LvlLe (CapAtom.var X4f) ⊤ᶜ ∧
    ¬ X4Ctx.LvlLe (CapAtom.cvar X4κf) ⊤ᶜ ∧
    ¬ X4OuterCtx.LvlLe (CapAtom.var .here) (CapAtom.cvar X4κout) :=
  ⟨by decide, by decide, by decide⟩

/-- The checker agrees, in the kernel: the level step at `f` is rejected. -/
example : checkCap X4Ctx (.level (.var X4f) ⊤ᶜ) [CapAtom.var X4f] [⊤ᶜ] = false := by
  decide +kernel

/-- The binder set of `f` resolves to the arrow binder, at every fuel: the
parameter's declared type is `File ^ {κ_f}` and `κ_f` is rigid. -/
theorem X4_caps (n : Nat) : X4Ctx.caps n [CapAtom.var X4f] = [CapAtom.cvar X4κf] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show X4Ctx.caps n [CapAtom.cvar X4κf] = _
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

/-- **X4, nothing escapes the callback.**  No member-free capture evidence
puts `{f}` below the universal root.  An instance of `level_inversion`: the
binder set of `f` is `{κ_f}`, whose level is the body root, so it is not at
the outermost level, and member-free evidence never lowers a level. -/
theorem X4_no_escape :
    ¬ ∃ g : CapCo (Sig.body []),
        (X4Ctx ⊢ᶜ g : [CapAtom.var X4f] ⊑ [⊤ᶜ]) ∧ g.MemberFree := by
  rintro ⟨g, hg, hgf⟩
  have hD : ∀ m, X4Ctx.Confined (X4Ctx.caps m [(⊤ᶜ : CapAtom (Sig.body []))]) ⊤ᶜ := by
    intro m
    rw [Ctx.caps_cons, Ctx.capsAtom_top, Ctx.caps_nil]
    decide
  have hC := level_inversion hg hgf hD 0
  rw [X4_caps] at hC
  exact absurd hC (by decide)

/-! ### X5, the counterfactual order

Under the rejected order `κ_f, f, κ_b`, with the parameter bound before the
body root, the level of `f` is the nearest root older than `f`, which at the
top level is the outermost one.  So the level rule fires and the escape
types.  This is why B1.1 binds the body root first, and it is a checked
fact here rather than a claim. -/

/-- The rejected order: `κ_f ⊑ᶜ ∗, f : File ^ {κ_f}, κ_b ⊚`. -/
def X5Ctx : Ctx ([],c,x,c) :=
  ((Ctx.nil.consC .star).cons (.opaque (.top ^ [CapAtom.cvar .here]))).consC .root

/-- The parameter under the rejected order. -/
def X5f : BVar ([],c,x,c) .var := .there .here

/-- Its level is the outermost one, because no root is older than it. -/
example : X5Ctx.lvl X5f = none := by decide

/-- **X5, the counterfactual fires.**  Under the rejected binder order the
level rule puts the parameter below the universal root, which is the escape
X4 rejects. -/
theorem X5_fires : X5Ctx ⊢ᶜ .level (.var X5f) ⊤ᶜ : [CapAtom.var X5f] ⊑ [⊤ᶜ] :=
  .level (by decide) (by decide)

/-- The checker agrees, in the kernel, and this is the one verdict that
differs from X4's. -/
example : checkCap X5Ctx (.level (.var X5f) ⊤ᶜ) [CapAtom.var X5f] [⊤ᶜ] = true := by
  decide +kernel

/-! ### S2 and C5a: the concrete assigned set below a scope root

Both examples are written with the concrete assigned set `{fs, u}` in the
result type, which is what the source's result `any` expands to.  The step
that puts that set below a scope root `{κ_S}` is `level`, and B0 supplies
it: `fs` is bound outside the scope, so its level encloses `κ_S`, and `u`
is bound inside the scope, so its level is `κ_S` itself.  The `fresh`
halves of both are stage B2's.

The contexts below are the contexts of C5 with the second capture binder
read as a scope root instead of a rigid capability.  Nothing else moves. -/

/-- `κ₁ ⊑ᶜ ∗, κ_S ⊚, u : ⊤`, the callee's context with a scope. -/
def C5aCtx : Ctx ([],c,c,x) :=
  ((Ctx.nil.consC .star).consC .root).cons (.opaque (Ty.pure .top))

/-- The scope root there. -/
def C5aκS : BVar ([],c,c,x) .cap := .there .here

/-- `fs` is outside the scope and `u` is inside it, so both are below the
scope root. -/
example : C5aCtx.lvl C5fs = none := by decide

example : C5aCtx.lvl (k := .var) .here = some C5aκS := by decide

/-- The level step of C5a: the concrete assigned set `{fs, u}` below the
scope root, one `level` per atom. -/
def C5aLevelCo : CapCo ([],c,c,x) :=
  .union (.level (.cvar C5fs) (.cvar C5aκS)) (.level (.var .here) (.cvar C5aκS))

/-- **C5a, the level step.**  The result set of the callee is below the
scope root. -/
theorem C5a_level_step : C5aCtx ⊢ᶜ C5aLevelCo : C5D ⊑ [CapAtom.cvar C5aκS] :=
  .union (.level (by decide) (by decide)) (.level (by decide) (by decide))

/-- The literal, packed at `{fs, u}` and then read at `{κ_S}`. -/
def C5aVal : Value ([],c,c,x) :=
  .cast (.cast (C5lit C5fs) (.capt (C5packCo C5fs) (.elem [] C5D)))
    (.capt (.refl (C5Obj C5fs)) C5aLevelCo)

example : checkValue C5aCtx C5aVal ((C5Obj C5fs) ^ [CapAtom.cvar C5aκS]) = true := by
  decide +kernel

/-- **C5a, the callee's side.**  The abstract iterator, packed at the
concrete set `{fs, u}`, is an iterator at the scope root.  The step from
the one to the other is `level`, twice. -/
theorem C5a_level : C5aCtx ⊢ᵥ C5aVal : (C5Obj C5fs) ^ [CapAtom.cvar C5aκS] :=
  checkValue_sound (by decide +kernel)

/-- `κ₁ ⊑ᶜ ∗, κ_S ⊚, u : ⊤, it : ⟦Iterator⟧ ^ {κ₁, u}`, the caller's
context with a scope. -/
def S2aCtx : Ctx ([],c,c,x,x) :=
  (((Ctx.nil.consC .star).consC .root).cons (.opaque (Ty.pure .top))).cons
    (.opaque ((C5Obj (.there (.there .here)))
      ^ [CapAtom.cvar (.there (.there .here)), CapAtom.var .here]))

/-- `fs` in the caller's context. -/
def S2afs : BVar ([],c,c,x,x) .cap := .there (.there (.there .here))

/-- The scope root in the caller's context. -/
def S2aκS : BVar ([],c,c,x,x) .cap := .there (.there .here)

/-- The level step of S2, at the caller. -/
def S2aLevelCo : CapCo ([],c,c,x,x) :=
  .union (.level (.cvar S2afs) (.cvar S2aκS))
    (.level (.var (.there .here)) (.cvar S2aκS))

/-- The iterator read at the scope root. -/
def S2aTm : Tm ([],c,c,x,x) :=
  .atom (.plain (.cast (.var .here) (.capt (.refl (C5Obj S2afs)) S2aLevelCo)))

def S2aTy : Ty ([],c,c,x,x) := (C5Obj S2afs) ^ [CapAtom.cvar S2aκS]

example : checkTm S2aCtx S2aTm S2aTy = true := by decide +kernel

/-- **S2, the caller's side.**  The result of the call, whose type carries
the concrete set `{fs, u}`, is read at the enclosing scope's root.  The one
step that does it is `level`. -/
theorem S2_level : S2aCtx ⊢ S2aTm : S2aTy := checkTm_sound (by decide +kernel)

/-! ## Stage B2: `fresh` as an existential

The five examples Y1 to Y5 of B2.11.  They use the answer sort `ETy`, the
syntactic pack, the answer-cast coercion `ELeCo` and the `letex` former.

Y1 is `freshCell` and two calls whose opened binders are incomparable.  Y2 is
`makeLogger`, packed at the parameter.  Y3 is C5b, whose caller charges its
use to the instantiated bound and never learns the witness.  Y4 is the
`withFile` escape, rejected by isolation and by the level check.  Y5 is the
`fresh` half of C5a and S2.

Two of the theorems are negative, and both go through `cap_canon`, which
reads a typed store (decision 12).  So each of them is stated at the context
the `letex` rules build, transported into the transparent context a store
types by `Ctx.Refines`: a transparent context knows everything the opaque
one knows, so refusing the inclusion there refuses it in the opaque one, and
the store is exhibited rather than assumed. -/

/-- A binder of the ambient signature, read in a lambda body. -/
abbrev up3 {s : Sig} {k : Kind} (y : BVar s k) : BVar (Sig.body s) k :=
  .there (.there (.there y))
/-- The same, one term binder further in. -/
abbrev up4 {s : Sig} {k : Kind} (y : BVar s k) : BVar ((Sig.body s),x) k :=
  .there (up3 y)

/-- Term label `set`. -/
def lset : Label := .trm 9

/-! ### The unit of the capture examples -/

/-- The unit type: a pure closure.  It is a type a store can hold, which
`⊤` is not, and that is what lets Y1's context carry a typed store. -/
def YUnit : Ty s := Ty.pure tArrow

/-- Its one literal. -/
def YUnitVal : Value s :=
  .lam [] (Ty.pure .top) (.atom (.plain (.var .here))) (.refl [CapAtom.var .here])

/-! ### `Cell` -/

/-- The block witnesses of a cell literal: the shape of `set`. -/
def YCellWit : Witnesses (s,x) := .cons .nil lset tArrow

/-- Its capture witnesses: `[set ↦ {self}]`, the mutator captures the cell. -/
def YCellCapWit : CapWitnesses (s,x) := .cons .nil lset [CapAtom.var .here]

/-- The telescope of `Cell`. -/
def YCellTel : Telescope (s,x) := Telescope.ofLiteral YCellWit YCellCapWit [lset]

/-- `Cell = μ(c. {set : (Π(⊤) ⊤) ^ {c}})`, a closed shape. -/
def YCell : Shape s := .obj YCellTel

/-- The one field: the identity closure cast to the field's own name. -/
def YCellFieldTm : Tm ((s,c),x) :=
  .cast
    (.val (.lam [] (Ty.pure .top) (.atom (.plain (.var .here))) (.refl [CapAtom.var .here])))
    (.capt (.eqToLe (.symm (.def .here lset))) (.elem [] [CapAtom.name .here lset]))

def YCellFields (A : CaptureSet s) : Fields ((s,c),x) :=
  .cons .nil lset YCellFieldTm
    (.elem [] ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) A))
      ∪ [CapAtom.var .here]))

/-- The cell literal `ν^A(…)`. -/
def YCellLit (A : CaptureSet s) : Value s :=
  .obj A YCellWit YCellCapWit (YCellFields A)

def YCellLitTy (A : CaptureSet s) : Ty s := YCell ^ A

/-- A capability of the platform: a closure the prefix binder owns. -/
def YCapVal (κ : BVar s .cap) : Value s :=
  .lam [CapAtom.cvar κ] (Ty.pure .top) (.atom (.plain (.var .here)))
    (.elem [CapAtom.var .here] [CapAtom.cvar (up3 κ), CapAtom.var .here])

/-! ### `freshCell` -/

/-- The answer `∃ᶜ[{κ₁}] (Cell ^ {κ})`. -/
def YExTy (κ1 : BVar s .cap) : ETy s := ∃ᶜ[[CapAtom.cvar κ1]] (YCell ^ [CapAtom.cvar .here])

/-- The type of `freshCell`. -/
def YFreshCellTy (κ1 : BVar s .cap) : Ty s :=
  (Π(YUnit) (YExTy (up2 κ1))) ^ [CapAtom.cvar κ1]

/-- The residual inclusion of the pack: the shape is the same and the
capture half is the instance rule of B2.4, read backwards. -/
def YPackCo (C : CaptureSet s) (S : Shape (Sig.scope s)) : LeCo (Sig.scope s) :=
  .capt (.refl S)
    (.eqToLe (.symm (.instC (.cvar .here)
      (CaptureSet.weaken (k := .cap) (CaptureSet.weaken (k := .cap) C)))))

/-- Packing as an answer coercion, at a witness that is its own bound. -/
def YPackELe (C : CaptureSet s) (S : Shape (Sig.scope s)) : ELeCo s :=
  .pack C (.refl C) (YPackCo C S)

/-- The packed atom: the fresh cell, at the witness `{κ₁}`. -/
def YPacked (C : CaptureSet s) (S : Shape (Sig.scope s)) (a : Atom s) : PAtom s :=
  .pack C (.refl C) (YPackCo C S) a

/-- The body of `freshCell`: allocate, then pack. -/
def YFreshBody (κ1 : BVar s .cap) : Tm (Sig.body s) :=
  .let (.val (YCellLit [CapAtom.cvar (up3 κ1)])) (.atom (YPacked [CapAtom.cvar (up4 κ1)] YCell (.var .here)))
    [CapAtom.cvar (up3 κ1)] (.capvar (.var .here))

/-- `freshCell` itself. -/
def YFreshCell (κ1 : BVar s .cap) : Value s :=
  .lam [CapAtom.cvar κ1] YUnit (YFreshBody κ1)
    (.elem [CapAtom.cvar (up3 κ1)] [CapAtom.cvar (up3 κ1), CapAtom.var .here])

/-- `κ₁ ⊑ᶜ ∗`, the platform prefix. -/
def Y1Ctx : Ctx ([],c) := Ctx.nil.consC .star

def Y1κ₁ : BVar ([],c) .cap := .here

example : checkValue Y1Ctx YUnitVal YUnit = true := by decide +kernel

example : checkValue Y1Ctx (YCellLit [CapAtom.cvar Y1κ₁]) (YCellLitTy [CapAtom.cvar Y1κ₁]) = true := by decide +kernel

example : checkValue Y1Ctx (YFreshCell Y1κ₁) (YFreshCellTy Y1κ₁) = true := by decide +kernel

/-- **Y1, `freshCell`.**  The one example of the stage that needs the
instance rule of B2.4: the pack's residual reads the witness binder off its
own instance binding. -/
theorem Y1_freshCell : Y1Ctx ⊢ᵥ YFreshCell Y1κ₁ : YFreshCellTy Y1κ₁ :=
  checkValue_sound (by decide +kernel)

/-! ### The caller -/

/-- `κ₁ ⊑ᶜ ∗, u : Unit, fc : freshCell`. -/
def Y1CCtx : Ctx ([],c,x,x) :=
  ((Ctx.nil.consC .star).cons (.opaque YUnit)).cons
    (.opaque (YFreshCellTy (.there .here)))

/-- The call `fc u`, at the caller. -/
def Y1call : Tm ([],c,x,x) := .app (.var .here) (.var (.there .here))

/-- The call again, under one opened pair. -/
def Y1call' : Tm ([],c,x,x,c,x) :=
  .app (.var (.there (.there .here))) (.var (.there (.there (.there .here))))

/-- A pure closure, the answer both `letex`es hand back. -/
def Y1pure : Value ([],c,x,x,c,x,c,x,x) :=
  .lam [] (Ty.pure .top) (.atom (.plain (.var .here))) (.refl [CapAtom.var .here])

/-- The innermost body: it reads `x₂` and returns a pure closure. -/
def Y1inner : Tm ([],c,x,x,c,x,c,x) :=
  .let (.atom (.plain (.var .here))) (.val Y1pure) [CapAtom.var .here]
    (.elem [] [CapAtom.var (.there .here)])

/-- The charge of the inner `letex`: the body names the opened binder. -/
def Y1charge2 : CapCo ([],c,x,x,c,x,c,x) :=
  .union
    (.trans (.capvar (.var .here))
      (.elem [CapAtom.cvar (.there .here)]
        [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
          CapAtom.cvar (.there .here)]))
    (.trans (.capvar (.var .here))
      (.elem [CapAtom.cvar (.there .here)]
        [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
          CapAtom.cvar (.there .here)]))

/-- The second call, unpacked. -/
def Y1body2 : Tm ([],c,x,x,c,x) :=
  .letex Y1call' Y1inner [CapAtom.cvar (.there (.there (.there (.there .here))))]
    (.refl [CapAtom.cvar (.there (.there (.there (.there .here))))]) Y1charge2

/-- The charge of the outer `letex`. -/
def Y1charge1 : CapCo ([],c,x,x,c,x) :=
  .union
    (.union
      (.trans (.capvar (.var (.there (.there .here))))
        (.elem [CapAtom.cvar (.there (.there (.there (.there .here))))]
          [CapAtom.cvar (.there (.there (.there (.there .here)))), CapAtom.cvar (.there .here)]))
      (.trans (.capvar (.var (.there (.there (.there .here)))))
        (.elem []
          [CapAtom.cvar (.there (.there (.there (.there .here)))), CapAtom.cvar (.there .here)])))
    (.elem [CapAtom.cvar (.there (.there (.there (.there .here))))]
      [CapAtom.cvar (.there (.there (.there (.there .here)))), CapAtom.cvar (.there .here)])

/-- The caller: two calls, each unpacked at once. -/
def Y1caller : Tm ([],c,x,x) :=
  .letex Y1call Y1body2 [CapAtom.cvar (.there (.there .here))]
    (.refl [CapAtom.cvar (.there (.there .here))]) Y1charge1

example : checkTm Y1CCtx Y1caller (Ty.pure tArrow) = true := by decide +kernel

/-- **Y1, the caller.**  Each call is unpacked where it stands, since the
`letex` rule's head premise is on an arbitrary term. -/
theorem Y1_caller : Y1CCtx ⊢ Y1caller : Ty.pure tArrow :=
  checkTm_sound (by decide +kernel)


/-! ### Two calls are incomparable -/

/-- The context the `letex` rules build for the body: both opened capture
binders are rigid and both cells are opaque. -/
def Y1BodyCtxO : Ctx ([],c,x,x,c,x,c,x) :=
  (((Y1CCtx.consC .star).cons (.opaque (YCell ^ [CapAtom.cvar .here]))).consC .star).cons
    (.opaque (YCell ^ [CapAtom.cvar .here]))

/-- The same context as a store types it: the four term binders are
transparent. -/
def Y1BodyCtx : Ctx ([],c,x,x,c,x,c,x) :=
  (((((((Ctx.nil.consC .star).cons (.transparent YUnit .nil .nil [])).cons
    (.transparent (YFreshCellTy (.there .here)) .nil .nil [])).consC .star).cons
    (.transparent (YCell ^ [CapAtom.cvar .here]) YCellWit YCellCapWit [lset])).consC .star).cons
    (.transparent (YCell ^ [CapAtom.cvar .here]) YCellWit YCellCapWit [lset]))

/-- The store itself: the platform slot, the unit, `freshCell`, and the two
pairs the two `letex`es opened. -/
def Y1Store : Store ([],c,x,x,c,x,c,x) :=
  .cons (.consC (.cons (.consC (.cons (.cons (.consC .nil .star) YUnitVal)
    (YFreshCell (.there .here))) .star) (YCellLit [CapAtom.cvar .here])) .star) (YCellLit [CapAtom.cvar .here])

theorem Y1Store_typed : ⊢ Y1Store : Y1BodyCtx :=
  .cons (.consC (.cons (.consC (.cons (.cons (.consC .nil rfl)
      trivial (checkValue_sound (by decide +kernel)))
      trivial (checkValue_sound (by decide +kernel))) rfl)
      trivial (checkValue_sound (by decide +kernel))) rfl)
      trivial (checkValue_sound (by decide +kernel))

/-- The opaque context refines into the store's. -/
theorem Y1_refines : Ctx.Refines Y1BodyCtxO Y1BodyCtx :=
  ((((((Ctx.Refines.transparent.cons _).trans Ctx.Refines.transparent).consC _).cons
    _).trans Ctx.Refines.transparent).consC _).cons _ |>.trans Ctx.Refines.transparent

/-- The binder the first call opened. -/
def Y1κ₁' : BVar ([],c,x,x,c,x,c,x) .cap := .there (.there (.there .here))
/-- The binder the second call opened. -/
def Y1κ₂' : BVar ([],c,x,x,c,x,c,x) .cap := .there .here
/-- The first cell. -/
def Y1x₁ : BVar ([],c,x,x,c,x,c,x) .var := .there (.there .here)
/-- The second cell. -/
def Y1x₂ : BVar ([],c,x,x,c,x,c,x) .var := .here

theorem Y1_caps_κ₁' (n : Nat) :
    Y1BodyCtx.caps n [CapAtom.cvar Y1κ₁'] = [CapAtom.cvar Y1κ₁'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Y1_caps_κ₂' (n : Nat) :
    Y1BodyCtx.caps n [CapAtom.cvar Y1κ₂'] = [CapAtom.cvar Y1κ₂'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Y1_caps_x₁ (n : Nat) :
    Y1BodyCtx.caps n [CapAtom.var Y1x₁] = [CapAtom.cvar Y1κ₁'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show Y1BodyCtx.caps n [CapAtom.cvar Y1κ₁'] = _
  exact Y1_caps_κ₁' n

theorem Y1_caps_x₂ (n : Nat) :
    Y1BodyCtx.caps n [CapAtom.var Y1x₂] = [CapAtom.cvar Y1κ₂'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show Y1BodyCtx.caps n [CapAtom.cvar Y1κ₂'] = _
  exact Y1_caps_κ₂' n

theorem two_calls_incomparable :
    (¬ ∃ f, Y1BodyCtxO ⊢ᶜ f : [CapAtom.cvar Y1κ₁'] ⊑ [CapAtom.cvar Y1κ₂']) ∧
    (¬ ∃ f, Y1BodyCtxO ⊢ᶜ f : [CapAtom.var Y1x₁] ⊑ [CapAtom.var Y1x₂]) := by
  constructor
  · rintro ⟨f, hf⟩
    have hr : Y1BodyCtx.Root (CapAtom.cvar Y1κ₁') [CapAtom.cvar Y1κ₁'] :=
      ⟨0, by rw [Ctx.roots_eq_expand_caps, Y1_caps_κ₁']; decide⟩
    obtain ⟨m, hm⟩ := cap_canon Y1Store_typed (CapCo.HasType.refine Y1_refines hf) _ hr
    rw [Ctx.roots_eq_expand_caps, Y1_caps_κ₂'] at hm
    exact absurd hm (by decide)
  · rintro ⟨f, hf⟩
    have hr : Y1BodyCtx.Root (CapAtom.cvar Y1κ₁') [CapAtom.var Y1x₁] :=
      ⟨0, by rw [Ctx.roots_eq_expand_caps, Y1_caps_x₁]; decide⟩
    obtain ⟨m, hm⟩ := cap_canon Y1Store_typed (CapCo.HasType.refine Y1_refines hf) _ hr
    rw [Ctx.roots_eq_expand_caps, Y1_caps_x₂] at hm
    exact absurd hm (by decide)


/-! ## Y2: `makeLogger`, packed at the parameter -/

/-- `makeLogger : (Π[κ_p](FileSystem ^ {κ_p}) ∃ᶜ[{x}] (Logger ^ {κ})) ^ {}`.
The declared bound of the result is the parameter itself, which is the
page's "this `any` has to be defined in a scope in which `fs` is
visible". -/
def Y2MakeLoggerTy : Ty s :=
  (Π(tArrow ^ [CapAtom.cvar .here])
    (∃ᶜ[[CapAtom.var .here]] (tArrow ^ [CapAtom.cvar .here]))) ^ []

/-- The logger the callee builds: a closure that captures `fs`. -/
def Y2Logger : Value (Sig.body s) :=
  .lam [CapAtom.var .here] (Ty.pure .top) (.atom (.plain (.var .here)))
    (.elem [CapAtom.var .here]
      [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])

/-- The body of `makeLogger`: build the logger, then pack it at `{fs}`. -/
def Y2MakeLoggerBody : Tm (Sig.body s) :=
  .let (.val Y2Logger) (.atom (YPacked [CapAtom.var (.there .here)] tArrow (.var .here)))
    [CapAtom.var .here] (.capvar (.var .here))

/-- `makeLogger` itself: a pure function. -/
def Y2MakeLogger : Value s :=
  .lam [] (tArrow ^ [CapAtom.cvar .here]) Y2MakeLoggerBody (.refl [CapAtom.var .here])

example : checkValue Ctx.nil Y2MakeLogger Y2MakeLoggerTy = true := by decide +kernel

/-- **Y2, `makeLogger`.**  The witness is the parameter, not a platform
binder, which is the example's point. -/
theorem Y2_makeLogger : Ctx.nil ⊢ᵥ (Y2MakeLogger (s := [])) : Y2MakeLoggerTy :=
  checkValue_sound (by decide +kernel)

/-! ### The caller: the enclosing lambda closes -/

/-- `ml : makeLogger`. -/
def Y2Ctx : Ctx ([],x) := Ctx.nil.cons (.opaque Y2MakeLoggerTy)

/-- The innermost body: it reads the logger and returns a pure closure. -/
def Y2inner : Tm ([],x,c,c,x,c,x) :=
  .let (.atom (.plain (.var .here))) (.val YUnitVal) [CapAtom.var .here]
    (.elem [] [CapAtom.var (.there .here)])

/-- The caller's body: unpack the call and charge the use to `{fs}`. -/
def Y2ClientBody : Tm (Sig.body ([],x)) :=
  .letex
    (.app (.var (.there (.there (.there .here))))
      (.recap (.var .here) (.refl [CapAtom.var .here])))
    Y2inner [CapAtom.var .here] (.refl [CapAtom.var .here])
    (.union
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.cvar (.there .here)]
          [CapAtom.var (.there (.there .here)), CapAtom.cvar (.there .here)]))
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.cvar (.there .here)]
          [CapAtom.var (.there (.there .here)), CapAtom.cvar (.there .here)])))

/-- The caller, as a closure over `fs`: it closes, because everything it
charges is a capability it can name. -/
def Y2Client : Value ([],x) :=
  .lam [CapAtom.var .here] (tArrow ^ [CapAtom.cvar .here]) Y2ClientBody
    (.elem [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here, CapAtom.var .here]
      [CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])

def Y2ClientTy : Ty ([],x) :=
  (Π(tArrow ^ [CapAtom.cvar .here]) (.ty (Ty.pure tArrow))) ^ [CapAtom.var .here]

example : checkValue Y2Ctx Y2Client Y2ClientTy = true := by decide +kernel

/-- **Y2, the caller closes.**  Everything the body charges is a capability
the enclosing lambda can name, which is what the declared bound buys. -/
theorem Y2_client : Y2Ctx ⊢ᵥ Y2Client : Y2ClientTy :=
  checkValue_sound (by decide +kernel)


/-! ## Y3: C5b, the iterator returned `fresh` -/

/-- The callee of C5b: Y2's shape at the cell.  Its result is an existential
bounded by the parameter. -/
def Y3MkTy : Ty s :=
  (Π(tArrow ^ [CapAtom.cvar .here])
    (∃ᶜ[[CapAtom.var .here]] (YCell ^ [CapAtom.cvar .here]))) ^ []

/-- Its body: allocate at `{fs}`, then pack at `{fs}`. -/
def Y3MkBody : Tm (Sig.body s) :=
  .let (.val (YCellLit [CapAtom.var .here]))
    (.atom (YPacked [CapAtom.var (.there .here)] YCell (.var .here)))
    [CapAtom.var .here] (.capvar (.var .here))

def Y3Mk : Value s :=
  .lam [] (tArrow ^ [CapAtom.cvar .here]) Y3MkBody (.refl [CapAtom.var .here])

example : checkValue Ctx.nil (Y3Mk (s := [])) Y3MkTy = true := by decide +kernel

/-- **Y3, the callee of C5b.** -/
theorem Y3_mk : Ctx.nil ⊢ᵥ (Y3Mk (s := [])) : Y3MkTy :=
  checkValue_sound (by decide +kernel)

/-- `κ_fs ⊑ᶜ ∗, fs : FS ^ {κ_fs}, u : Unit, mk : Y3MkTy`, the caller's
context as the rules build it. -/
def Y3CtxO : Ctx ([],c,x,x,x) :=
  (((Ctx.nil.consC .star).cons (.opaque (tArrow ^ [CapAtom.cvar .here]))).cons
    (.opaque YUnit)).cons (.opaque Y3MkTy)

/-- The projection `c.set`, read through the declared telescope and cast to
the arrow and to `{c}`. -/
def Y3proj : Tm ([],c,x,x,x,c,x) :=
  .cast (.proj (.var .here) lset (.member (.var .here) (.refl YCell) 2))
    (.capt (.eqToLe (.member (.var .here) (.refl YCell) 0))
      (.eqToLe (.member (.var .here) (.refl YCell) 1)))

/-- The call `n u`, with the unit widened to the arrow's domain. -/
def Y3app : Tm ([],c,x,x,x,c,x,x) :=
  .app (.var .here)
    (.cast (.var (.there (.there (.there (.there .here))))) (.capt (.top tArrow) (.refl [])))

/-- The body of the `letex`: project, then apply. -/
def Y3letBody : Tm ([],c,x,x,x,c,x) :=
  .let Y3proj Y3app [CapAtom.var .here]
    (.union (.capvar (.var .here))
      (.trans (.capvar (.var (.there (.there (.there (.there .here))))))
        (.elem [] [CapAtom.var (.there .here)])))

/-- The caller: unpack the call, then use the cell through `{κ}`. -/
def Y3caller : Tm ([],c,x,x,x) :=
  .letex
    (.app (.var .here) (.recap (.var (.there (.there .here)))
      (.refl [CapAtom.var (.there (.there .here))])))
    Y3letBody [CapAtom.var (.there (.there .here))]
    (.refl [CapAtom.var (.there (.there .here))])
    (.union
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.cvar (.there .here)]
          [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.cvar (.there .here)]))
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.cvar (.there .here)]
          [CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.cvar (.there .here)])))

example : checkTm Y3CtxO Y3caller (Ty.pure .top) = true := by decide +kernel

/-- **Y3, the caller of C5b.**  It unpacks, projects and applies through the
opened binder. -/
theorem Y3_caller : Y3CtxO ⊢ Y3caller : Ty.pure .top :=
  checkTm_sound (by decide +kernel)


/-- `fs` at the caller. -/
def Y3fs : BVar ([],c,x,x,x) .var := .there (.there .here)

/-- The caller's own use set, charged to the argument it passed. -/
def Y3useCo : CapCo ([],c,x,x,x) :=
  .union
    (.union (.trans (.capvar (.var .here)) (.elem [] [CapAtom.var Y3fs]))
      (.refl [CapAtom.var Y3fs]))
    (.refl [CapAtom.var Y3fs])

/-- **Y3, the caller's use set.**  It is the argument it passed and nothing
more: the callee is pure and the declared set of the `letex` is `{fs}`. -/
theorem c5b_caller_uses : Y3CtxO ⊢ᶜ Y3useCo : Y3caller.uses ⊑ [CapAtom.var Y3fs] :=
  checkCap_sound (by decide +kernel)

/-! ### The caller never learns that the witness is the argument -/

/-- The body's context as the rules build it. -/
def Y3BodyCtxO : Ctx ([],c,x,x,x,c,x) :=
  (Y3CtxO.consC .star).cons (.opaque (YCell ^ [CapAtom.cvar .here]))

/-- The same as a store types it. -/
def Y3BodyCtx : Ctx ([],c,x,x,x,c,x) :=
  ((((((Ctx.nil.consC .star).cons
    (.transparent (tArrow ^ [CapAtom.cvar .here]) .nil .nil [])).cons
    (.transparent YUnit .nil .nil [])).cons
    (.transparent Y3MkTy .nil .nil [])).consC .star).cons
    (.transparent (YCell ^ [CapAtom.cvar .here]) YCellWit YCellCapWit [lset]))

def Y3Store : Store ([],c,x,x,x,c,x) :=
  .cons (.consC (.cons (.cons (.cons (.consC .nil .star) (YCapVal .here)) YUnitVal) Y3Mk) .star)
    (YCellLit [CapAtom.cvar .here])

theorem Y3Store_typed : ⊢ Y3Store : Y3BodyCtx :=
  .cons (.consC (.cons (.cons (.cons (.consC .nil rfl)
      trivial (checkValue_sound (by decide +kernel)))
      trivial (checkValue_sound (by decide +kernel)))
      trivial (checkValue_sound (by decide +kernel))) rfl)
      trivial (checkValue_sound (by decide +kernel))

theorem Y3_refines : Ctx.Refines Y3BodyCtxO Y3BodyCtx :=
  (((((Ctx.Refines.transparent.cons _).trans Ctx.Refines.transparent).cons _).trans
    Ctx.Refines.transparent).consC _).cons _ |>.trans Ctx.Refines.transparent

/-- The binder the call opened. -/
def Y3κ' : BVar ([],c,x,x,x,c,x) .cap := .there .here
/-- `fs` in the body. -/
def Y3fsB : BVar ([],c,x,x,x,c,x) .var := .there (.there (.there (.there .here)))
/-- `κ_fs` in the body. -/
def Y3κfs : BVar ([],c,x,x,x,c,x) .cap := .there (.there (.there (.there (.there .here))))

theorem Y3_caps_κ' (n : Nat) :
    Y3BodyCtx.caps n [CapAtom.cvar Y3κ'] = [CapAtom.cvar Y3κ'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Y3_caps_κfs (n : Nat) :
    Y3BodyCtx.caps n [CapAtom.cvar Y3κfs] = [CapAtom.cvar Y3κfs] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Y3_caps_fs (n : Nat) :
    Y3BodyCtx.caps n [CapAtom.var Y3fsB] = [CapAtom.cvar Y3κfs] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show Y3BodyCtx.caps n [CapAtom.cvar Y3κfs] = _
  exact Y3_caps_κfs n

/-- **Y3, the witness stays hidden.**  No evidence puts the opened binder
below the argument the caller passed: the caller knows the binder is below
the declared bound and nothing else. -/
theorem c5b_no_witness :
    ¬ ∃ f, Y3BodyCtxO ⊢ᶜ f : [CapAtom.cvar Y3κ'] ⊑ [CapAtom.var Y3fsB] := by
  rintro ⟨f, hf⟩
  have hr : Y3BodyCtx.Root (CapAtom.cvar Y3κ') [CapAtom.cvar Y3κ'] :=
    ⟨0, by rw [Ctx.roots_eq_expand_caps, Y3_caps_κ']; decide⟩
  obtain ⟨m, hm⟩ := cap_canon Y3Store_typed (CapCo.HasType.refine Y3_refines hf) _ hr
  rw [Ctx.roots_eq_expand_caps, Y3_caps_fs] at hm
  exact absurd hm (by decide)


/-! ## Y4: the `withFile` escape, rejected twice over -/

/-- **Y4, the third widening step of the page.**  A plain codomain is widened
to an existential under `ShapeCo.pi`, which is what `ELeCo.pack` being a
coercion buys (decision 19). -/
def Y4packUnderPi : LeCo ([],c) :=
  .capt (.pi (.capt (.refl tArrow) (.refl []))
    (YPackELe [CapAtom.cvar (up3 Y1κ₁)] YCell)) (.refl [CapAtom.cvar Y1κ₁])

example : checkLe Y1Ctx Y4packUnderPi
    ((Π(YUnit) (.ty (YCell ^ [CapAtom.cvar (up2 Y1κ₁)]))) ^ [CapAtom.cvar Y1κ₁])
    (YFreshCellTy Y1κ₁) = true := by decide +kernel

/-- **Y4, packing under an arrow.**  The page's third widening step. -/
theorem Y4_pack_under_pi : Y1Ctx ⊢ Y4packUnderPi :
    ((Π(YUnit) (.ty (YCell ^ [CapAtom.cvar (up2 Y1κ₁)]))) ^ [CapAtom.cvar Y1κ₁])
      ≤ YFreshCellTy Y1κ₁ :=
  checkLe_sound (by decide +kernel)

/-- **Y4, isolation.**  No coercion takes an existential answer back to a
plain one, so the existentially bound capability cannot flow into an outer
`any`.  This is `no_ex_le_ty`, T8's isolation half. -/
theorem Y4_isolation {C₀ : CaptureSet (Sig.body [])} {T : Ty ((Sig.body []),c)}
    {T' : Ty (Sig.body [])} :
    ¬ ∃ g, X4Ctx ⊢ᵉ g : (∃ᶜ[C₀] T) ≤ .ty T' := by
  rintro ⟨g, hg⟩
  exact no_ex_le_ty hg

/-- **Y4, the level check after a `letex`.**  B1's theorem, unchanged: even
if the caller unpacks, the unpacked binder's level is the caller's and the
level rule runs only inward. -/
theorem Y4_no_escape :
    ¬ ∃ g : CapCo (Sig.body []),
        (X4Ctx ⊢ᶜ g : [CapAtom.var X4f] ⊑ [⊤ᶜ]) ∧ g.MemberFree :=
  X4_no_escape

/-! ## Y5: the `fresh` halves of S2 and C5a -/

/-- **Y5a, C5a's `fresh` half.**  The packed literal, wrapped in an
existential bounded by the concrete assigned set `{fs, u}` instead of read at
the scope root `{κ_S}`. -/
def Y5ExVal : Value ([],c,c,x) :=
  .pack C5D (.refl C5D) (YPackCo C5D (C5Obj (.there (.there C5fs))))
    (.cast (C5lit C5fs) (.capt (C5packCo C5fs) (.elem [] C5D)))

def Y5ExTy : ETy ([],c,c,x) :=
  ∃ᶜ[C5D] ((C5Obj (.there C5fs)) ^ [CapAtom.cvar .here])

example : checkValueE C5Ctx Y5ExVal Y5ExTy = true := by decide +kernel

/-- **Y5a.**  C5a's literal at an existential answer. -/
theorem Y5_packed : C5Ctx ⊢ᵥᵉ Y5ExVal : Y5ExTy :=
  checkValueE_sound (by decide +kernel)

/-- `fs` in the body of the `letex`. -/
def Y5fs : BVar ([],c,c,x,c,x) .cap := .there (.there (.there (.there .here)))
/-- `fs` one term binder further in. -/
def Y5fs' : BVar ([],c,c,x,c,x,x) .cap := .there Y5fs

/-- `it.next`, read off the unpacked iterator. -/
def Y5run : Tm ([],c,c,x,c,x) :=
  .cast
    (.proj (.var .here) lnext (.member (.var .here) (.refl (C5Obj Y5fs)) 2))
    (.capt (.member (.var .here) (.refl (C5Obj Y5fs)) 3)
      (.member (.var .here) (.refl (C5Obj Y5fs)) 4))

/-- The call, charged through the member's upper bound. -/
def Y5client : Tm ([],c,c,x,c,x) :=
  .let Y5run (.app (.var .here) (.var (.there (.there (.there .here)))))
    [CapAtom.cvar Y5fs]
    (.union
      (.trans (.capvar (.var .here))
        (.member (.var (.there .here)) (.refl (C5Obj Y5fs')) 1))
      (.trans (.capvar (.var (.there (.there (.there .here)))))
        (.elem [] [CapAtom.cvar Y5fs'])))

/-- The body of the `letex`: use the iterator, then hand back a pure
closure, which is what lets the answer avoid both opened binders. -/
def Y5Body : Tm ([],c,c,x,c,x) :=
  .let Y5client (.val YUnitVal) [] (.elem [] [])

/-- **Y5b, S2's `fresh` half.**  The same program read through a `letex`
instead of through `{κ_S}`. -/
def Y5caller : Tm ([],c,c,x) :=
  .letex (.val Y5ExVal) Y5Body C5D (.refl C5D)
    (.union
      (.trans (.capvar (.var .here))
        (.elem [CapAtom.cvar (.there .here)]
          [CapAtom.cvar Y5fs, CapAtom.var (.there (.there .here)),
            CapAtom.cvar (.there .here)]))
      (.elem [CapAtom.cvar Y5fs]
        [CapAtom.cvar Y5fs, CapAtom.var (.there (.there .here)),
          CapAtom.cvar (.there .here)]))

example : checkTm C5Ctx Y5caller (Ty.pure tArrow) = true := by decide +kernel

/-- **Y5b.**  S2's program read through a `letex`. -/
theorem Y5_caller : C5Ctx ⊢ Y5caller : Ty.pure tArrow :=
  checkTm_sound (by decide +kernel)


/-! ### The source examples of B2.11 in the target

`Zᵢ_translated` is `HasTy.translate_typed` at the source derivation: the
translated term has the translated type in the translated context.  It is
not decided by the checker.  `Zᵢ_erase` is `HasTy.translate_erase` at the
same derivation, so the source program and its translation run the same
runtime term. -/

/-- The caller's context of Z1 is well formed. -/
theorem Z1CtxWf : DotMNF.Ctx.Wf DotMNF.Examples.Z1Ctx :=
  .cons (.cons (.consC (.consC .nil)))

/-- **Z1 translated.**  `freshCell`, at the type the result `fresh` expands
to. -/
theorem Z1_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.Z1_plat.translate :
    (DotMNF.Examples.Z1Ty DotMNF.Examples.k1).translate :=
  DotMNF.Examples.Z1_plat.translate_typed platWf

/-- **Z1 erased.** -/
theorem Z1_erase :
    Tm.erase DotMNF.Examples.Z1_plat.translate
      = DotMNF.Tm.erase (DotMNF.Examples.Z1Tm : DotMNF.Tm ([],c,c)) :=
  DotMNF.HasTy.translate_erase _

/-- **Z1's caller translated.**  A source `letex` becomes the target's
`letex`, with the declared set, the bound evidence and the body's own
use-set evidence. -/
theorem Z1_caller_translated : DotMNF.Examples.Z1Ctx.translate ⊢
    DotMNF.Examples.Z1_caller.translate :
    (DotMNF.Examples.unitTy : DotMNF.Ty ([],c,c,x,x)).translate :=
  DotMNF.Examples.Z1_caller.translate_typed Z1CtxWf

/-- **Z1's caller erased.** -/
theorem Z1_caller_erase :
    Tm.erase DotMNF.Examples.Z1_caller.translate
      = DotMNF.Tm.erase
          (DotMNF.Tm.letex (.app (.there .here) .here)
            (.let (.path (.var .here)) DotMNF.Examples.unitTm)) :=
  DotMNF.HasTy.translate_erase _

/-- **Z2 translated.**  `makeLogger`, whose bound is the parameter. -/
theorem Z2_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.Z2_plat.translate : DotMNF.Examples.Z2Ty.translate :=
  DotMNF.Examples.Z2_plat.translate_typed platWf

/-- **Z2 erased.** -/
theorem Z2_erase :
    Tm.erase DotMNF.Examples.Z2_plat.translate
      = DotMNF.Tm.erase (DotMNF.Examples.Z2Tm : DotMNF.Tm ([],c,c)) :=
  DotMNF.HasTy.translate_erase _

/-- **Z3 translated.**  C5b's callee: the capture member packs the literal's
`{fs}` and the existential packs the result. -/
theorem Z3_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.Z3_plat.translate :
    (DotMNF.Examples.Z3Ty DotMNF.Examples.k1).translate :=
  DotMNF.Examples.Z3_plat.translate_typed platWf

/-- **Z3 erased.** -/
theorem Z3_erase :
    Tm.erase DotMNF.Examples.Z3_plat.translate
      = DotMNF.Tm.erase (DotMNF.Examples.S2mkTm DotMNF.Examples.k1) :=
  DotMNF.HasTy.translate_erase _


/-! ### The source examples of B3.9 in the target

W2, W3 and W4 are source types read the compiler's way, so their target side
is the translation of the source derivation.  W5's second half is T17, which
lives on the target because it names `⊤ᶜ`, an atom the source cannot
write. -/

/-- The body context of W2 and W5 is well formed. -/
theorem W2BodyCtxWf : DotMNF.Ctx.Wf DotMNF.Examples.W2BodyCtx :=
  DotMNF.Ctx.Wf.body platWf _

/-- The calling context of W2 is well formed. -/
theorem W2CallCtxWf : DotMNF.Ctx.Wf DotMNF.Examples.W2CallCtx := .cons (.cons platWf)

/-- **W2 translated.**  A parameter `any` stays one arrow in the target: the
arrow binds the capture parameter, so no member encoding and no extra
application appear in the translated term. -/
theorem W2_translated : DotMNF.Examples.platCtx.translate ⊢
    (DotMNF.Examples.W2_typed (Γ := DotMNF.Examples.platCtx)).translate :
    (DotMNF.Examples.W2Ty : DotMNF.Ty ([],c,c)).translate :=
  DotMNF.Examples.W2_typed.translate_typed platWf

/-- **W2 erased.**  The source program and its translation run the same
runtime term, which is the erasure equality a member encoding would have
lost. -/
theorem W2_erase :
    Tm.erase (DotMNF.Examples.W2_typed (Γ := DotMNF.Examples.platCtx)).translate
      = DotMNF.Tm.erase (DotMNF.Examples.W2Tm : DotMNF.Tm ([],c,c)) :=
  DotMNF.HasTy.translate_erase _

/-- **W2's call translated.**  One application in the source is one
application in the target. -/
theorem W2_call_translated : DotMNF.Examples.W2CallCtx.translate ⊢
    DotMNF.Examples.W2_call.translate :
    (DotMNF.Examples.unitTy : DotMNF.Ty ([],c,c,x,x)).translate :=
  DotMNF.Examples.W2_call.translate_typed W2CallCtxWf

/-- **W3 translated.**  `makeLogger` with the parameter written `any` reads
as `Z2TyF`, so the target side is `Z2_translated`, byte for byte. -/
theorem W3_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.Z2_plat.translate : DotMNF.Examples.Z2Ty.translate :=
  Z2_translated

/-- **W4 translated.**  `freshCell` read the compiler's way is `freshCell`,
so the target side is `Z1_translated`. -/
theorem W4_translated : DotMNF.Examples.platCtx.translate ⊢
    DotMNF.Examples.Z1_plat.translate :
    (DotMNF.Examples.Z1Ty DotMNF.Examples.k1).translate :=
  Z1_translated

/-! ### W5, the second half: nothing escapes the callback

`W5_caps` is the source twin of `X4_caps`: the binder set of the callback's
parameter resolves to the arrow binder `κ_f`, whose level is the body root.
`W5_no_escape` is T17 at `r = ⊤ᶜ`: no member-free source subcapturing puts
`{f}` below the platform capability `κ₁`, which sits at the outermost level
because the platform prefix opens no scope.  The page's own consequence for
the program is `escaped().read()`, a use after close. -/

/-- The callback's parameter in the body context. -/
abbrev W5Tf : BVar (Sig.body ([],c,c)) .var := .here

/-- The callback's arrow binder there. -/
abbrev W5Tkf : BVar (Sig.body ([],c,c)) .cap := .there .here

/-- The outer platform capability, read inside the body. -/
abbrev W5Tk1 : BVar (Sig.body ([],c,c)) .cap :=
  .there (.there (.there (.there .here)))

/-- **W5, the resolution step.**  The binder set of `f` resolves to the
arrow binder, at every fuel: the parameter's declared type is `File ^ {κ_f}`
and `κ_f` is rigid in the translated context. -/
theorem W5_caps (n : Nat) :
    DotMNF.Examples.W2BodyCtx.translate.caps n [CapAtom.var W5Tf]
      = [CapAtom.cvar W5Tkf] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show DotMNF.Examples.W2BodyCtx.translate.caps n [CapAtom.cvar W5Tkf] = _
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

/-- **W5, nothing escapes the callback.**  No member-free source
subcapturing puts `{f}` below the platform capability.  An instance of T17:
the binder set of `f` is `{κ_f}`, whose level is the body root, so it is not
at the outermost level, and member-free evidence never lowers a level. -/
theorem W5_no_escape :
    ¬ ∃ d : DotMNF.Subcap DotMNF.Examples.W2BodyCtx [DotMNF.CapAtom.var W5Tf]
        [DotMNF.CapAtom.cvar W5Tk1], d.MemberFree := by
  rintro ⟨d, hd⟩
  have hD : ∀ m, DotMNF.Examples.W2BodyCtx.translate.Confined
      (DotMNF.Examples.W2BodyCtx.translate.caps m
        (DotMNF.CaptureSet.translate [DotMNF.CapAtom.cvar W5Tk1])) ⊤ᶜ := by
    intro m
    rw [show DotMNF.CaptureSet.translate [DotMNF.CapAtom.cvar W5Tk1]
          = [CapAtom.cvar W5Tk1] from rfl,
      Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
    show DotMNF.Examples.W2BodyCtx.translate.Confined [CapAtom.cvar W5Tk1] ⊤ᶜ
    decide
  have hC := DotMNF.source_lvl_safety W2BodyCtxWf hd hD 0
  rw [show DotMNF.CaptureSet.translate [DotMNF.CapAtom.var W5Tf]
        = [CapAtom.var W5Tf] from rfl, W5_caps] at hC
  exact absurd hC (by decide)


/-! ## Two calls of `freshCell`, on the source side

**B3.9 W4, the second half.**  `DotMNF.Examples.Z_two_calls_no_level` says
that the level order relates neither of the two opened binders to the other.
The full incomparability is a canonical-forms fact: no capture evidence at
all relates them.  It is `two_calls_incomparable` above, redone over a
translated source context, and it needs what that theorem needed, a typed
store, a refinement into the transparent context the store types, the
resolution of the two opened binders, and `cap_canon`.

The store is what decides which source context the statement can be made
over.  A store binds literals, a literal has its own precise type, and the
precise type of a target literal is `Telescope.ofLiteral`, a telescope of
definitions and presences.  The translation of a source object type is a
telescope of bounds, and its newest entry is a capture bound.  So no target
literal has the type `⟦File ^ C⟧`, and no store binds a variable at it.
That is `Z_no_literal_at_file`, and it is why the statement is made over the
translation of `DotMNF.Examples.Z1BodyCtxTop`, the same two calls with the
answer widened to `⊤` by `DotMNF.Examples.Z1_widen`, and not over the
translation of `Z1BodyCtxSrc`.

Nothing of the statement's content depends on the widening.  The two opened
capture binders are where they were, the two cells are declared at the sets
the two calls assigned them, and what is refuted is evidence between those
binders and between those cells. -/

/-! ### No literal has a translated object type -/

/-- Presence entries are appended last, so a telescope that ends in no
capture bound still ends in none after them. -/
theorem hasEntries_ne_leC {s' : Sig} :
    ∀ (ls : List Label) (T : Telescope s'),
      (∀ (Tel : Telescope s') (P Q : CaptureSet s'), T ≠ Tel.cons (.leC P Q)) →
      ∀ (Tel : Telescope s') (P Q : CaptureSet s'), T.hasEntries ls ≠ Tel.cons (.leC P Q)
  | [], T, h => h
  | l :: ls, T, _ => by
      refine hasEntries_ne_leC ls (T.cons (.has l)) ?_
      intro Tel P Q hEq
      simp only [Telescope.cons.injEq] at hEq
      exact absurd hEq.2 (by simp)

/-- A capture definition is not a capture bound, so the capture-definition
block of a literal ends in none either. -/
theorem capEqEntries_ne_leC {s' : Sig} (self : BVar s' .var) (W₀ : CapWitnesses s')
    (base : Telescope s')
    (hb : ∀ (Tel : Telescope s') (P Q : CaptureSet s'), base ≠ Tel.cons (.leC P Q)) :
    ∀ (Wc : CapWitnesses s') (Tel : Telescope s') (P Q : CaptureSet s'),
      W₀.eqEntriesOf self base Wc ≠ Tel.cons (.leC P Q)
  | .nil, Tel, P, Q => hb Tel P Q
  | .cons _ _ _, Tel, P, Q => by
      intro hEq
      rw [CapWitnesses.eqEntriesOf] at hEq
      simp only [Telescope.cons.injEq] at hEq
      exact absurd hEq.2 (by simp)

/-- And a definition is not a capture bound. -/
theorem eqEntries_ne_leC {s' : Sig} (self : BVar s' .var) (W₀ : Witnesses s') :
    ∀ (W : Witnesses s') (Tel : Telescope s') (P Q : CaptureSet s'),
      W₀.eqEntriesOf self W ≠ Tel.cons (.leC P Q)
  | .nil, Tel, P, Q => by intro hEq; rw [Witnesses.eqEntriesOf] at hEq; exact absurd hEq (by simp)
  | .cons _ _ _, Tel, P, Q => by
      intro hEq
      rw [Witnesses.eqEntriesOf] at hEq
      simp only [Telescope.cons.injEq] at hEq
      exact absurd hEq.2 (by simp)

/-- **The precise telescope of a literal never ends in a capture bound.** -/
theorem ofLiteral_ne_leC {s : Sig} (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
    (ls : List Label) (Tel : Telescope (s,x)) (P Q : CaptureSet (s,x)) :
    Telescope.ofLiteral W Wc ls ≠ Tel.cons (.leC P Q) :=
  hasEntries_ne_leC ls _
    (capEqEntries_ne_leC .here Wc _ (eqEntries_ne_leC .here W W) Wc) Tel P Q

/-- **No literal has an object type whose telescope ends in a capture
bound.**  A lambda has an arrow type, a box a box type, an object literal
its own precise type, and a cast is no literal. -/
theorem no_literal_at_leC {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (hlit : v.IsLiteral) (h : Γ ⊢ᵥ v : T) :
    ∀ (Tel : Telescope (s,x)) (P Q : CaptureSet (s,x)) (C : CaptureSet s),
      T ≠ (Shape.obj (Tel.cons (.leC P Q))) ^ C := by
  cases h with
  | lam => intro Tel P Q C hEq; simp at hEq
  | box => intro Tel P Q C hEq; simp at hEq
  | cast => exact hlit.elim
  | obj =>
      intro Tel P Q C hEq
      simp only [Ty.capt.injEq, Shape.obj.injEq] at hEq
      exact ofLiteral_ne_leC _ _ _ Tel P Q hEq.2

/-! ### The translated types of the two-call program -/

/-- `⟦⊤⟧`, the empty object shape.  The source's `⊤` is the empty telescope,
which is also the precise telescope of a literal with no witnesses and no
fields, so `⊤` is a source type a target store can hold. -/
def ZTopS : Shape s := .obj .nil

/-- `⟦⊤ ^ []⟧`. -/
def ZUnit : Ty s := ZTopS ^ []

/-- `⟦⊤ ^ C⟧ = ⟦⊤⟧ ^ ⟦C⟧`. -/
theorem ZTop_translate {s : Sig} (C : DotMNF.CaptureSet s) :
    DotMNF.Ty.translate (DotMNF.Ty.capt C .top) = Ty.capt C.translate ZTopS := by
  rw [DotMNF.Ty.translate, DotMNF.Shape.translate]; rfl

/-- `⟦⊤ ^ []⟧ = ZUnit`. -/
theorem ZUnit_translate {s : Sig} :
    DotMNF.Ty.translate (DotMNF.Examples.unitTy (s := s)) = ZUnit := by
  rw [DotMNF.Examples.unitTy, DotMNF.Ty.translate, DotMNF.Shape.translate]; rfl

/-- The telescope of `⟦File⟧`: a presence, a bound on the field's shape, and
a bound on the field's capture name.  Its newest entry is a capture bound,
which is what `no_literal_at_leC` reads. -/
def ZFileTel : Telescope (s,x) :=
  ((Telescope.nil.cons (.has DotMNF.Examples.lread)).cons
      (.le (.sel .here DotMNF.Examples.lread) (Shape.pi ZUnit (.ty ZUnit)))).cons
    (.leC [CapAtom.name .here DotMNF.Examples.lread] [CapAtom.var .here])

theorem ZFile_translate {s : Sig} (C : DotMNF.CaptureSet s) :
    DotMNF.Ty.translate (DotMNF.Ty.capt C DotMNF.Examples.fileS)
      = (Shape.obj ZFileTel) ^ C.translate := by
  rw [DotMNF.Ty.translate_capt, DotMNF.Examples.fileS, DotMNF.Shape.translate,
    DotMNF.Shape.telSelf, DotMNF.Examples.arrowS, DotMNF.Shape.translate_all_eq,
    ZUnit_translate, DotMNF.ETy.translate_ty, ZUnit_translate]
  rfl

/-- **No target literal has the translated type of the source's `File`.**  A
store binds literals, so no store binds a variable at `⟦File ^ C⟧`, and the
two-call statement below is made at the widened context for that reason. -/
theorem Z_no_literal_at_file {s : Sig} {Γ : Ctx s} {v : Value s} {C : DotMNF.CaptureSet s}
    (hlit : v.IsLiteral) :
    ¬ (Γ ⊢ᵥ v : DotMNF.Ty.translate (DotMNF.Ty.capt C DotMNF.Examples.fileS)) :=
  fun h => no_literal_at_leC hlit h _ _ _ _ (ZFile_translate C)

/-- `⟦Z1TyTop fs⟧`, the translated type of `freshCell` at the widened
answer. -/
def ZFreshTy (fs : BVar s .cap) : Ty s :=
  (Π(ZUnit) (∃ᶜ[[CapAtom.cvar (up2 fs), CapAtom.var .here]] (ZTopS ^ [CapAtom.cvar .here])))
    ^ [CapAtom.cvar fs]

theorem ZFreshTy_translate {s : Sig} (fs : BVar s .cap) :
    DotMNF.Ty.translate (DotMNF.Examples.Z1TyTop fs) = ZFreshTy fs := by
  rw [DotMNF.Examples.Z1TyTop, DotMNF.Ty.translate_capt, DotMNF.Shape.translate_all_eq,
    ZUnit_translate, DotMNF.ETy.translate_ex, ZTop_translate]
  rfl

/-! ### The store the argument needs -/

/-- The empty object literal at an assigned capture set. -/
def ZEmptyLit (A : CaptureSet s) : Value s := .obj A .nil .nil .nil

/-- The unit value: the empty object, pure. -/
def ZUnitVal : Value s := ZEmptyLit []

/-- The body of `freshCell` at the widened answer: allocate an empty object
at the arrow's own set, then pack it at the witness the answer declares. -/
def ZFreshBody (fs : BVar s .cap) : Tm (Sig.body s) :=
  .let (.val (ZEmptyLit [CapAtom.cvar (up3 fs)]))
    (.atom (.pack [CapAtom.cvar (up4 fs)]
        (.elem [CapAtom.cvar (up4 fs)] [CapAtom.cvar (up4 fs), CapAtom.var (.there .here)])
        (YPackCo [CapAtom.cvar (up4 fs)] ZTopS) (.var .here)))
    [CapAtom.cvar (up3 fs)] (.capvar (.var .here))

/-- `freshCell` itself, at the widened answer. -/
def ZFreshCell (fs : BVar s .cap) : Value s :=
  .lam [CapAtom.cvar fs] ZUnit (ZFreshBody fs)
    (.elem [CapAtom.cvar (up3 fs)] [CapAtom.cvar (up3 fs), CapAtom.var .here])

/-- The platform prefix of the source examples, translated. -/
def ZPlat : Ctx ([],c,c) := (Ctx.nil.consC .star).consC .star

example : DotMNF.Examples.platCtx.translate = ZPlat := rfl

/-- `fs` is the source's `κ₁`. -/
def Zfs : BVar ([],c,c) .cap := .there .here

example : checkValue ZPlat ZUnitVal ZUnit = true := by decide +kernel

example : checkValue ZPlat (ZEmptyLit [CapAtom.cvar Zfs]) (ZTopS ^ [CapAtom.cvar Zfs]) = true := by
  decide +kernel

example : checkValue ZPlat (ZFreshCell Zfs) (ZFreshTy Zfs) = true := by decide +kernel

/-- The translated two-call context, spelled out.  Every term binder is
opaque, as the `letex` rule leaves it. -/
def ZBodyCtxO : Ctx ([],c,c,x,x,c,x,c,x) :=
  (((((((Ctx.nil.consC .star).consC .star).cons
    (.opaque (ZFreshTy (.there .here)))).cons (.opaque ZUnit)).consC .star).cons
    (.opaque (ZTopS ^ [CapAtom.cvar .here]))).consC .star).cons
    (.opaque (ZTopS ^ [CapAtom.cvar .here]))

theorem ZBodyCtxO_eq : DotMNF.Ctx.translate DotMNF.Examples.Z1BodyCtxTop = ZBodyCtxO := by
  rw [DotMNF.Examples.Z1BodyCtxTop, DotMNF.Ctx.translate, DotMNF.Ctx.translate,
    DotMNF.Ctx.translate, DotMNF.Ctx.translate, DotMNF.Examples.Z1CtxTop,
    DotMNF.Ctx.translate, DotMNF.Ctx.translate, DotMNF.Examples.platCtx,
    DotMNF.Ctx.translate, DotMNF.Ctx.translate, DotMNF.Ctx.translate,
    ZTop_translate, ZTop_translate, ZUnit_translate, ZFreshTy_translate]
  rfl

/-- The same context as a store types it: the four term binders are
transparent, and none of the four values has a witness or a field. -/
def ZBodyCtx : Ctx ([],c,c,x,x,c,x,c,x) :=
  (((((((Ctx.nil.consC .star).consC .star).cons
    (.transparent (ZFreshTy (.there .here)) .nil .nil [])).cons
    (.transparent ZUnit .nil .nil [])).consC .star).cons
    (.transparent (ZTopS ^ [CapAtom.cvar .here]) .nil .nil [])).consC .star).cons
    (.transparent (ZTopS ^ [CapAtom.cvar .here]) .nil .nil [])

/-- The store itself: the two platform slots, `freshCell`, the unit, and the
two pairs the two `letex`es opened. -/
def ZStore : Store ([],c,c,x,x,c,x,c,x) :=
  .cons (.consC (.cons (.consC (.cons (.cons (.consC (.consC .nil .star) .star)
    (ZFreshCell (.there .here))) ZUnitVal) .star) (ZEmptyLit [CapAtom.cvar .here])) .star)
    (ZEmptyLit [CapAtom.cvar .here])

theorem ZStore_typed : ⊢ ZStore : ZBodyCtx :=
  .cons (.consC (.cons (.consC (.cons (.cons (.consC (.consC .nil rfl) rfl)
      trivial (checkValue_sound (by decide +kernel)))
      trivial (checkValue_sound (by decide +kernel))) rfl)
      trivial (checkValue_sound (by decide +kernel))) rfl)
      trivial (checkValue_sound (by decide +kernel))

/-- The translated context refines into the store's. -/
theorem Z_refines : Ctx.Refines ZBodyCtxO ZBodyCtx :=
  ((((((Ctx.Refines.transparent.cons _).trans Ctx.Refines.transparent).consC _).cons
    _).trans Ctx.Refines.transparent).consC _).cons _ |>.trans Ctx.Refines.transparent

/-! ### The two opened binders resolve to themselves -/

theorem Z_caps_k1 (n : Nat) :
    ZBodyCtx.caps n [CapAtom.cvar DotMNF.Examples.Zk1'] = [CapAtom.cvar DotMNF.Examples.Zk1'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Z_caps_k2 (n : Nat) :
    ZBodyCtx.caps n [CapAtom.cvar DotMNF.Examples.Zk2'] = [CapAtom.cvar DotMNF.Examples.Zk2'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_cvar, Ctx.caps_nil, List.append_nil]
  rfl

theorem Z_caps_x1 (n : Nat) :
    ZBodyCtx.caps n [CapAtom.var DotMNF.Examples.Zx1'] = [CapAtom.cvar DotMNF.Examples.Zk1'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show ZBodyCtx.caps n [CapAtom.cvar DotMNF.Examples.Zk1'] = _
  exact Z_caps_k1 n

theorem Z_caps_x2 (n : Nat) :
    ZBodyCtx.caps n [CapAtom.var DotMNF.Examples.Zx2'] = [CapAtom.cvar DotMNF.Examples.Zk2'] := by
  rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil]
  show ZBodyCtx.caps n [CapAtom.cvar DotMNF.Examples.Zk2'] = _
  exact Z_caps_k2 n

/-- **B3.9 W4, two calls are incomparable on the source side.**  Over the
translation of the source's own two-call context, no capture evidence puts
the binder the first call opened below the binder the second call opened,
and none puts the first cell below the second.  The argument is the
target's: the two binders resolve to themselves, so each is a root of its
own set and of neither the other's, and `cap_canon` reads any evidence as an
inclusion of roots.

What is not claimed is what B2.11 records: at run time both opened binders
carry `.inst C`, so in the store's own context each is below the other. -/
theorem Z_two_calls_incomparable :
    (¬ ∃ f, DotMNF.Ctx.translate DotMNF.Examples.Z1BodyCtxTop ⊢ᶜ f :
      [CapAtom.cvar DotMNF.Examples.Zk1'] ⊑ [CapAtom.cvar DotMNF.Examples.Zk2']) ∧
    (¬ ∃ f, DotMNF.Ctx.translate DotMNF.Examples.Z1BodyCtxTop ⊢ᶜ f :
      [CapAtom.var DotMNF.Examples.Zx1'] ⊑ [CapAtom.var DotMNF.Examples.Zx2']) := by
  rw [ZBodyCtxO_eq]
  constructor
  · rintro ⟨f, hf⟩
    have hr : ZBodyCtx.Root (CapAtom.cvar DotMNF.Examples.Zk1')
        [CapAtom.cvar DotMNF.Examples.Zk1'] :=
      ⟨0, by rw [Ctx.roots_eq_expand_caps, Z_caps_k1]; decide⟩
    obtain ⟨m, hm⟩ := cap_canon ZStore_typed (CapCo.HasType.refine Z_refines hf) _ hr
    rw [Ctx.roots_eq_expand_caps, Z_caps_k2] at hm
    exact absurd hm (by decide)
  · rintro ⟨f, hf⟩
    have hr : ZBodyCtx.Root (CapAtom.cvar DotMNF.Examples.Zk1')
        [CapAtom.var DotMNF.Examples.Zx1'] :=
      ⟨0, by rw [Ctx.roots_eq_expand_caps, Z_caps_x1]; decide⟩
    obtain ⟨m, hm⟩ := cap_canon ZStore_typed (CapCo.HasType.refine Z_refines hf) _ hr
    rw [Ctx.roots_eq_expand_caps, Z_caps_x2] at hm
    exact absurd hm (by decide)


/-! ## K0.9: the three classifier examples

Three contexts of classified capabilities, and what a projected capture atom
resolves to over each.  Every verdict is read off an equation for `Ctx.caps`,
proved by `simp` over the clause lemmas, and an expansion decided in the
kernel.  `Ctx.caps` is a well-founded recursion, so it is never handed to
`decide`. -/

/-! ### K1x, a platform filter

Two classified capabilities and no scope root.  A projection by `only
Control` keeps the `Control` capability and drops the `IO` one.  This is the
whole of the atom case. -/

/-- `κ_ctl ⊑ᶜ cls Control, κ_io ⊑ᶜ cls IO`. -/
def K1Ctx : Ctx ([],c,c) :=
  Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.Control)) (.cls Cls.IO)

/-- The `Control` capability of K1x. -/
abbrev K1ctl : BVar ([],c,c) .cap := .there .here

/-- The `IO` capability of K1x. -/
abbrev K1io : BVar ([],c,c) .cap := .here

theorem K1x_caps_ctl (n : Nat) :
    K1Ctx.caps n [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control]
      = [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control] := by
  simp [K1Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    Ctx.lookupCap, CapBound.weaken, CapBound.rename]

theorem K1x_caps_io (n : Nat) :
    K1Ctx.caps n [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control]
      = [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control] := by
  simp [K1Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    Ctx.lookupCap, CapBound.weaken, CapBound.rename]

/-- The `Control` capability survives its own filter. -/
theorem K1x_roots_ctl :
    K1Ctx.roots 0 [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control] = [CapAtom.cvar K1ctl] := by
  rw [Ctx.roots_eq_expand_caps, K1x_caps_ctl]
  decide

/-- The `IO` capability does not. -/
theorem K1x_roots_io :
    K1Ctx.roots 0 [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control] = [] := by
  rw [Ctx.roots_eq_expand_caps, K1x_caps_io]
  decide

/-! ### K2x, a root filter

The shape the adversarial check broke.  The universal root projected at
`except ThreadLocal` has the single root `⊤ᶜ`: `Control` lies below
`ThreadLocal`, so both classified binders are excluded, while `⊤ᶜ` itself is
admitted.  The refuted design derived the same kinding and kept the
`ThreadLocal` binder among the roots. -/

/-- `κ_tl ⊑ᶜ cls ThreadLocal, κ_ctl ⊑ᶜ cls Control`, with no scope root. -/
def K2Ctx : Ctx ([],c,c) :=
  Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.ThreadLocal)) (.cls Cls.Control)

theorem K2x_caps (n : Nat) :
    K2Ctx.caps n [⊤ᶜ ↾ Cls.except Cls.ThreadLocal]
      = [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] := by
  simp [K2Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_top]

/-- The universal root survives, and nothing else does. -/
theorem K2x_roots : K2Ctx.roots 0 [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] = [⊤ᶜ] := by
  rw [Ctx.roots_eq_expand_caps, K2x_caps]
  decide

/-- And the projected set is kinded by construction, which is T2.  This is
what the refuted design could not have. -/
theorem K2x_kindLe :
    K2Ctx.KindLe [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] (Cls.except Cls.ThreadLocal) :=
  Ctx.kindLe_proj K2Ctx [⊤ᶜ] (Cls.except Cls.ThreadLocal)

/-! ### K3x, a scope root filter

A scope root between two classified capabilities.  The root opens into `⊤ᶜ`
and every opaque binder at its level or outside it, and the filter then keeps
only what the kind admits.  The `Control` capability is inside the scope and
is excluded by the kind, so it is not below the projected root: that is the
sentence E2 will make about a program. -/

/-- `κ_tl ⊑ᶜ cls ThreadLocal, κ_S ⊚, κ_ctl ⊑ᶜ cls Control`. -/
def K3Ctx : Ctx ([],c,c,c) :=
  Ctx.consC (Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.ThreadLocal)) .root) (.cls Cls.Control)

/-- The scope root of K3x. -/
abbrev K3S : BVar ([],c,c,c) .cap := .there .here

/-- The `Control` capability of K3x, opened inside the scope. -/
abbrev K3ctl : BVar ([],c,c,c) .cap := .here

theorem K3x_caps (n : Nat) :
    K3Ctx.caps n [(CapAtom.cvar K3S) ↾ Cls.except Cls.ThreadLocal]
      = [(CapAtom.cvar K3S) ↾ Cls.except Cls.ThreadLocal] := by
  simp [K3Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    Ctx.lookupCap, CapBound.weaken, CapBound.rename]

theorem K3x_caps_ctl (n : Nat) :
    K3Ctx.caps n [CapAtom.cvar K3ctl] = [CapAtom.cvar K3ctl] := by
  simp [K3Ctx, Ctx.capsAtom_cvar, Ctx.capsBound,
    Ctx.lookupCap, CapBound.weaken, CapBound.rename]

/-- The projected scope root keeps `⊤ᶜ` and itself and neither classified
binder. -/
theorem K3x_roots :
    K3Ctx.roots 0 [(CapAtom.cvar K3S) ↾ Cls.except Cls.ThreadLocal]
      = [⊤ᶜ, CapAtom.cvar K3S] := by
  rw [Ctx.roots_eq_expand_caps, K3x_caps]
  decide

/-- So the inner `Control` capability is not below the projected root. -/
theorem K3x_not_capLe :
    ¬ CapLe K3Ctx [CapAtom.cvar K3ctl] [(CapAtom.cvar K3S) ↾ Cls.except Cls.ThreadLocal] := by
  intro h
  obtain ⟨m, hm⟩ := h (CapAtom.cvar K3ctl)
    ⟨0, by rw [Ctx.roots_eq_expand_caps, K3x_caps_ctl]; decide⟩
  rw [Ctx.roots_eq_expand_caps, K3x_caps] at hm
  exact absurd hm (by decide)

/-! ## K1: kinding evidence and subcapturing through a projection

Two examples of stage K1, both decided through the checker, in the manner of
X1 to X5.  Every premise of every kinding rule is a `Bool` function, so
`checkKindCo` and `checkCap` run in the kernel and `decide` closes each
verdict. -/

/-! ### K4x, the platform capability

`kcls` is Capless(K)'s `k-label` and `k-label-absurd` in one rule.  Over the
context of K1x, the `Control` capability projected at `only Control` is
kinded at `only Control` and not at `only ThreadLocal`, and the `IO`
capability projected at `only Control` is kinded at *every* kind, because its
own projection already excludes its classifier.  That vacuous branch is
`k-label-absurd`. -/

/-- The `Control` capability, projected at its own kind. -/
abbrev K4ctl : CapAtom ([],c,c) := (CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control

/-- The `IO` capability, projected at a kind that excludes it. -/
abbrev K4io : CapAtom ([],c,c) := (CapAtom.cvar K1io) ↾ Cls.only Cls.Control

/-- `k-label`: the declared classifier is admitted by the target. -/
theorem K4x_ctl_accept :
    checkKindCo K1Ctx (.kcls K4ctl) [K4ctl] (Cls.only Cls.Control) = true := by decide

/-- And the same evidence is rejected at a kind the classifier is outside.
`only ThreadLocal` would accept it, because `Control` lies below
`ThreadLocal`, so the rejecting kind is `only IO`. -/
theorem K4x_ctl_reject :
    checkKindCo K1Ctx (.kcls K4ctl) [K4ctl] (Cls.only Cls.IO) = false := by decide

/-- `k-label-absurd`: the projection already excludes the classifier, so the
atom is kinded at every kind.  Two witnesses. -/
theorem K4x_io_absurd_control :
    checkKindCo K1Ctx (.kcls K4io) [K4io] (Cls.only Cls.Control) = true := by decide

theorem K4x_io_absurd_threadLocal :
    checkKindCo K1Ctx (.kcls K4io) [K4io] (Cls.only Cls.ThreadLocal) = true := by decide

/-- The kinding judgment behind the first verdict, through `checkKindCo_iff_hasType`. -/
theorem K4x_ctl_hasType :
    K1Ctx ⊢ᵏ (KindCo.kcls K4ctl) : [K4ctl] ⊑ᵏ (Cls.only Cls.Control) :=
  checkKindCo_iff_hasType.mp K4x_ctl_accept

/-! ### K5x, subcapturing through a projection

`CapCo.projC` puts a kinded set below its own projection and `CapCo.unprojC`
puts a projection below the set it projects, so over K1x's context the
`Control` capability and its projection at `only Control` have the same
roots. -/

/-- The kinding evidence `projC` premises: the singleton is kinded at
`only Control` by `k-label`. -/
abbrev K5kind : KindCo ([],c,c) := .cons (.kcls (CapAtom.cvar K1ctl)) .nil

/-- The projected set, as `CaptureSet.proj` builds it. -/
abbrev K5proj : CaptureSet ([],c,c) :=
  CaptureSet.proj [CapAtom.cvar K1ctl] (Cls.only Cls.Control)

theorem K5x_kind :
    checkKindCo K1Ctx K5kind [CapAtom.cvar K1ctl] (Cls.only Cls.Control) = true := by decide

/-- `sc-proj`: the set goes below its own projection. -/
theorem K5x_projC :
    checkCap K1Ctx (.projC K5kind [CapAtom.cvar K1ctl] (Cls.only Cls.Control))
      [CapAtom.cvar K1ctl] K5proj = true := by decide

/-- And a projection goes below the set it projects. -/
theorem K5x_unprojC :
    checkCap K1Ctx (.unprojC [CapAtom.cvar K1ctl] (Cls.only Cls.Control))
      K5proj [CapAtom.cvar K1ctl] = true := by decide

theorem K5x_caps_bare (n : Nat) :
    K1Ctx.caps n [CapAtom.cvar K1ctl] = [CapAtom.cvar K1ctl] := by
  simp [K1Ctx, Ctx.capsAtom_cvar, Ctx.capsBound,
    Ctx.lookupCap, CapBound.weaken, CapBound.rename]

/-- So the two sets have the same roots. -/
theorem K5x_roots : K1Ctx.roots 0 K5proj = K1Ctx.roots 0 [CapAtom.cvar K1ctl] := by
  show K1Ctx.roots 0 [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control]
    = K1Ctx.roots 0 [CapAtom.cvar K1ctl]
  rw [Ctx.roots_eq_expand_caps, Ctx.roots_eq_expand_caps, K1x_caps_ctl, K5x_caps_bare]
  decide

/-! ### K6x, the rigid binder with no declared classifier

The example K1.2 asks for, and the boundary the evidence family cannot
cross.  A rigid binder that declares no classifier carries the root
classifier as its own.  `except ThreadLocal` contains the root classifier
and `only Control` does not, so the canonical form kinds such a binder at
the first kind and not at the second.  That is decision 9 read on the
semantics: an unwritten classifier is the root one, and the strict reading
keeps it out of `only Control`.

No evidence term of K1 derives the first fact, and the gap is forced.
`kcls` reads a classifier a binder *declares*, and this binder declares
none.  `kproj` asks that the target kind admit every classifier, which
`except ThreadLocal` does not.  A rule that read the root classifier off a
binder with no declaration would not survive `Ctx.Ren.instC`, the
instantiation lemma T-B2.1, which reads such a binder as an instance of an
arbitrary set: the fact below is true here and false in the image of that
map, so the kinding family would lose its renaming lemma.  The two halves
are machine checked in the K1 g6 counterexample. -/

/-- `κ_tl ⊑ᶜ cls ThreadLocal, κ_p ⊚`: a classified capability, then a rigid
binder with no declared classifier. -/
def K6Ctx : Ctx ([],c,c) :=
  Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.ThreadLocal)) .star

/-- The rigid binder of K6x. -/
abbrev K6p : CapAtom ([],c,c) := CapAtom.cvar BVar.here

theorem K6x_caps (n : Nat) : K6Ctx.caps n [K6p] = [K6p] := by
  simp [K6Ctx, Ctx.capsAtom_cvar, Ctx.capsBound, Ctx.lookupCap, CapBound.weaken,
    CapBound.rename]

theorem K6x_roots (n : Nat) : K6Ctx.roots n [K6p] = [K6p] := by
  rw [Ctx.roots_eq_expand_caps, K6x_caps]
  decide

/-- Kinded at `except ThreadLocal`: the one root carries the root
classifier, which the kind admits. -/
theorem K6x_kindLe : K6Ctx.KindLe [K6p] (Cls.except Cls.ThreadLocal) := by
  intro r hr
  obtain ⟨n, hn⟩ := hr
  rw [K6x_roots] at hn
  have hr' : r = K6p := by simpa using hn
  subst hr'
  decide

/-- And not kinded at `only Control`. -/
theorem K6x_not_kindLe : ¬ K6Ctx.KindLe [K6p] (Cls.only Cls.Control) := by
  intro h
  have hc := h K6p ⟨0, by rw [K6x_roots]; exact List.mem_cons_self ..⟩
  revert hc
  decide

/-- The evidence family stops short of the first fact: the classifier rule
rejects the binder, because it declares nothing. -/
theorem K6x_kcls_reject :
    checkKindCo K6Ctx (.kcls K6p) [K6p] (Cls.except Cls.ThreadLocal) = false := by decide

/-- And the kind rule rejects it, because `except ThreadLocal` does not
admit every classifier. -/
theorem K6x_kproj_reject :
    checkKindCo K6Ctx (.kproj K6p) [K6p] (Cls.except Cls.ThreadLocal) = false := by decide

/-! ## E1, only-control

The target side of `DotMNF.Examples`' E1 (`exceptions.tex:60-66`).  The source
program is `Try.apply` applied to a body the program allocates, and its declared
use set is the platform set filtered at `only[Control]`.  Here: the platform
context as the translation builds it, the resolution of the two platform
capabilities through the filter, the kinding of the filtered sets by T2, the
translation of the source evidence, and effect safety at `only[Control]` on both
sides.

The platform context is K1x's context on the nose, so the two resolution facts
are K1x over a real program. -/

/-- The platform context of E1, as `Platform.ctx` builds it. -/
theorem E1_platCtx : DotMNF.Examples.E1Plat.ctx = DotMNF.Examples.E1PlatCtx := rfl

/-- Its translation is K1x's context: `κ_ctl ⊑ᶜ cls Control, κ_io ⊑ᶜ cls IO`. -/
theorem E1_ctx_translate : DotMNF.Examples.E1Plat.ctx.translate = K1Ctx := rfl

/-- The platform context is well formed. -/
theorem E1_ctx_wf : DotMNF.Ctx.Wf DotMNF.Examples.E1Plat.ctx :=
  DotMNF.Platform.ctx_wf _

/-- The body of `Try.apply` is read in a well-formed context. -/
theorem E1_bodyCtx_wf : DotMNF.Ctx.Wf DotMNF.Examples.E1BodyCtx :=
  .cons (.consC (.consRoot E1_ctx_wf))

/-! ### The platform verdicts

`Platform.admits_iff` turns the admission test at a platform capability into the
containment test of the classifier the platform declares, and the kernel decides
that. -/

/-- The control capability is admitted by `only[Control]`. -/
theorem E1_admits_ctl :
    DotMNF.Examples.E1Plat.ctx.translate.admitsB (CapAtom.cvar K1ctl)
      (Cls.only Cls.Control) = true := by
  rw [DotMNF.Platform.admits_iff DotMNF.Examples.E1Plat K1ctl]
  decide

/-- The input-output capability is not. -/
theorem E1_admits_io :
    DotMNF.Examples.E1Plat.ctx.translate.admitsB (CapAtom.cvar K1io)
      (Cls.only Cls.Control) = false := by
  rw [DotMNF.Platform.admits_iff DotMNF.Examples.E1Plat K1io]
  decide

/-! ### Resolution through the filter -/

theorem E1_caps_ctl (n : Nat) :
    DotMNF.Examples.E1Plat.ctx.translate.caps n
        [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control]
      = [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control] := by
  rw [E1_ctx_translate]
  simp [K1Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

theorem E1_caps_io (n : Nat) :
    DotMNF.Examples.E1Plat.ctx.translate.caps n
        [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control]
      = [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control] := by
  rw [E1_ctx_translate]
  simp [K1Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

/-- The control capability survives the filter. -/
theorem E1_roots_ctl :
    DotMNF.Examples.E1Plat.ctx.translate.roots 0
        [(CapAtom.cvar K1ctl) ↾ Cls.only Cls.Control] = [CapAtom.cvar K1ctl] := by
  rw [Ctx.roots_eq_expand_caps, E1_caps_ctl, E1_ctx_translate]
  decide

/-- The input-output capability does not: this is the sentence E1 makes. -/
theorem E1_roots_io :
    DotMNF.Examples.E1Plat.ctx.translate.roots 0
        [(CapAtom.cvar K1io) ↾ Cls.only Cls.Control] = [] := by
  rw [Ctx.roots_eq_expand_caps, E1_caps_io, E1_ctx_translate]
  decide

/-! ### The filtered sets are kinded, by T2

`Ctx.kindLe_proj` kinds a projected set by construction, and the translation of
a projected source set is the projection of its translation. -/

/-- The program's declared use set is kinded at `only[Control]`. -/
theorem E1_kindLe_uses :
    DotMNF.Examples.E1Plat.ctx.translate.KindLe
      DotMNF.Examples.E1Filt.translate (Cls.only Cls.Control) := by
  simp only [DotMNF.Examples.E1Filt, DotMNF.CaptureSet.translate_proj]
  exact Ctx.kindLe_proj _ _ _

/-- And so is the field's set `{x ↾ only[Control]}`, in the body of
`Try.apply`. -/
theorem E1_kindLe_field :
    DotMNF.Examples.E1BodyCtx.translate.KindLe
      DotMNF.Examples.E1FieldSet.translate (Cls.only Cls.Control) := by
  simp only [DotMNF.Examples.E1FieldSet, DotMNF.CaptureSet.translate_proj]
  exact Ctx.kindLe_proj _ _ _

/-! ### The source evidence, through the translation -/

/-- The program's translation is typed at the translated type. -/
theorem E1_translate_typed :
    Tm.HasType DotMNF.Examples.E1Plat.ctx.translate DotMNF.Examples.E1_typed.translate
      (DotMNF.ETy.translate (.ty DotMNF.Examples.E1Ty)) :=
  DotMNF.HasTy.translate_typed _ E1_ctx_wf

/-- The kinding of the use set translates to target kinding evidence. -/
theorem E1_kind_translate_typed :
    DotMNF.Examples.E1Plat.ctx.translate ⊢ᵏ DotMNF.Examples.E1_kind.translate :
      DotMNF.Examples.E1Filt.translate ⊑ᵏ (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ E1_ctx_wf

/-- And so does the kinding of the field's set, the `kvar` derivation. -/
theorem E1_field_kind_translate_typed :
    DotMNF.Examples.E1BodyCtx.translate ⊢ᵏ DotMNF.Examples.E1_field_kind.translate :
      DotMNF.Examples.E1FieldSet.translate ⊑ᵏ (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ E1_bodyCtx_wf

/-! ### Why the filter is needed

The unfiltered platform set is not kinded at `only[Control]`: the
input-output capability is one of its roots, and `only[Control]` excludes `IO`.
That is why `Try.apply` returns its object at the filtered set and not at the
parameter's own set. -/

theorem E1_caps_platSet (n : Nat) :
    DotMNF.Examples.E1Plat.ctx.translate.caps n
        [CapAtom.cvar K1ctl, CapAtom.cvar K1io]
      = [CapAtom.cvar K1ctl, CapAtom.cvar K1io] := by
  rw [E1_ctx_translate]
  simp [K1Ctx, Ctx.capsAtom_cvar, Ctx.capsBound, CapBound.weaken, CapBound.rename]

theorem E1_platSet_not_kindLe :
    ¬ DotMNF.Examples.E1Plat.ctx.translate.KindLe
      [CapAtom.cvar K1ctl, CapAtom.cvar K1io] (Cls.only Cls.Control) := by
  intro h
  have hc := h (CapAtom.cvar K1io)
    ⟨0, by rw [Ctx.roots_eq_expand_caps, E1_caps_platSet, E1_ctx_translate]; decide⟩
  rw [E1_ctx_translate] at hc
  revert hc
  decide

/-! ### The checker on the translated evidence

The translation of a source kinding derivation is a well-founded recursion, so
the kernel does not unfold it and `decide` says nothing about it.  The checker's
completeness closes the gap: the translation is typed, so the checker accepts
it.  The decided half is `E1_kcls_ctl` and `E1_kcls_io_absurd`, which are K4x's
two verdicts at E1's own platform context. -/

/-- `k-label` at the control capability, decided. -/
theorem E1_kcls_ctl :
    checkKindCo DotMNF.Examples.E1Plat.ctx.translate (.kcls K4ctl) [K4ctl]
      (Cls.only Cls.Control) = true := by
  rw [E1_ctx_translate]
  decide

/-- `k-label-absurd` at the input-output capability, decided: its own
projection already excludes its classifier. -/
theorem E1_kcls_io_absurd :
    checkKindCo DotMNF.Examples.E1Plat.ctx.translate (.kcls K4io) [K4io]
      (Cls.only Cls.Control) = true := by
  rw [E1_ctx_translate]
  decide

/-- The checker accepts the translation of the field's kinding derivation. -/
theorem E1_field_kind_checked :
    checkKindCo DotMNF.Examples.E1BodyCtx.translate
      DotMNF.Examples.E1_field_kind.translate DotMNF.Examples.E1FieldSet.translate
      (Cls.only Cls.Control) = true :=
  checkKindCo_iff_hasType.mpr E1_field_kind_translate_typed

/-- And the translation of the use set's kinding derivation. -/
theorem E1_kind_checked :
    checkKindCo DotMNF.Examples.E1Plat.ctx.translate
      DotMNF.Examples.E1_kind.translate DotMNF.Examples.E1Filt.translate
      (Cls.only Cls.Control) = true :=
  checkKindCo_iff_hasType.mpr E1_kind_translate_typed

/-! ### Effect safety at `only[Control]` -/

/-- The initial target state of E1's program. -/
def E1TgtInit : State ([],c,c) :=
  ⟨DotMNF.Examples.E1Plat.targetStore, .nil, DotMNF.Examples.E1_typed.translate⟩

/-- Its use set is kinded at `only[Control]`: the declared use set bounds it by
`cap_canon`, and the declared use set is the filtered platform set. -/
theorem E1_initial_kindLe :
    DotMNF.Examples.E1Plat.ctx.translate.KindLe E1TgtInit.uses (Cls.only Cls.Control) := by
  have hbase : CapLe DotMNF.Examples.E1Plat.ctx.translate E1TgtInit.uses
      DotMNF.Examples.E1Filt.translate := by
    simp only [E1TgtInit, State.uses_mk, usesK_nil, CaptureSet.union_def, List.append_nil]
    exact cap_canon DotMNF.Examples.E1Plat.targetStore_typed
      (DotMNF.HasTy.translate_uses _ E1_ctx_wf)
  exact Ctx.KindLe.mono hbase E1_kindLe_uses

/-- **E1 on the target.**  Along any run of the translated program, every root
of a variable the machine reads carries a classifier `only[Control]` admits.
This is `classified_effect_safety` at `only Control`. -/
theorem E1_target_effect_safety {s' : Sig} {st' : State s'} {Γ' : Ctx s'}
    {x : BVar s' .var} (run : E1TgtInit ⟶* st') (hin : st'.inspects = some x)
    (hσ' : Store.Typed st'.σ Γ') :
    ∀ a : CapAtom s', Γ'.Root a [CapAtom.var x] →
      (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  classified_effect_safety
    (DotMNF.Platform.initial_typed DotMNF.Examples.E1Plat DotMNF.Examples.E1_typed)
    DotMNF.Examples.E1Plat.targetStore_typed E1_initial_kindLe run hin hσ'

/-- **The run never reads `κ_io`.**  `only[Control]` does not contain `IO`, so
no root of a read variable is classified `IO`. -/
theorem E1_never_io {s' : Sig} {st' : State s'} {Γ' : Ctx s'} {x : BVar s' .var}
    (run : E1TgtInit ⟶* st') (hin : st'.inspects = some x)
    (hσ' : Store.Typed st'.σ Γ') (a : CapAtom s') (ha : Γ'.Root a [CapAtom.var x]) :
    Γ'.classOf a ≠ Cls.IO := by
  intro h
  have hc := E1_target_effect_safety run hin hσ' a ha
  rw [h] at hc
  exact absurd hc (by decide)

/-- **E1 at the source**, through T9': the source program, its own kinding
evidence, and any source run.  The matched target state reads only capabilities
`only[Control]` admits. -/
theorem E1_effect_safety {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps
      (⟨DotMNF.Examples.E1Plat.store, .nil, DotMNF.Examples.E1tm⟩ : DotMNF.State ([],c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : State s) (Γ' : Ctx s) (ρ : Rename ([],c,c) s),
      State.erase stt = st.erase ∧ Store.Typed stt.σ Γ' ∧
        Store.Ext DotMNF.Examples.E1Plat.targetStore stt.σ ρ ∧
          ∀ a : CapAtom s, Γ'.Root a [CapAtom.var x] →
            (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  DotMNF.dot_classified_effect_safety' DotMNF.Examples.E1Plat DotMNF.Examples.E1_typed
    DotMNF.Examples.E1_kind run hin

/-! ## E2, except-thread-local

The target side of `DotMNF.Examples`' E2 (`exceptions.tex:74-92`).  The source
program is `Future.apply` applied to a body the program allocates, and its
declared use set is the platform set filtered at `except[ThreadLocal]`.  Here:
the platform context as the translation builds it, the two resolution shapes of
the example, the refutation of a thread-local argument, the verdicts of the
checker, the kinding of the filtered set by T2, and effect safety at
`except[ThreadLocal]` on both sides.

The resolution shapes are read over the classified platform of the paper, the
two capabilities `except[ThreadLocal]` excludes.  Its translation is K2x's
context on the nose, so the first shape is K2x over a real program, and the
second is K3x with the body root of `Future.apply` as the scope root.  The
companions over the program's platform show the input-output capability
surviving the filter, which is what makes the legal argument legal. -/

section E2

open DotMNF.Examples (E2Plat E2PlatCtx E2PlatIO E2PlatIOCtx E2Dom E2Filt E2ClsBodyCtx
  E2TlDescent E2tl E2ctl E2io)

/-- The platform context of E2, as `Platform.ctx` builds it. -/
theorem E2_platCtx : E2Plat.ctx = E2PlatCtx := rfl

/-- And the same for the platform the program runs on. -/
theorem E2_platIOCtx : E2PlatIO.ctx = E2PlatIOCtx := rfl

/-- The classified platform translates to K2x's context: `κ_tl ⊑ᶜ cls
ThreadLocal, κ_ctl ⊑ᶜ cls Control`. -/
theorem E2_ctx_translate : E2Plat.ctx.translate = K2Ctx := rfl

/-- The program's platform on the target. -/
def E2TCtx : Ctx ([],c,c,c) :=
  Ctx.consC (Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.ThreadLocal)) (.cls Cls.Control))
    (.cls Cls.IO)

/-- `κ_tl` on the target. -/
abbrev E2Ttl : BVar ([],c,c,c) .cap := .there (.there .here)
/-- `κ_ctl` on the target. -/
abbrev E2Tctl : BVar ([],c,c,c) .cap := .there .here
/-- `κ_io` on the target. -/
abbrev E2Tio : BVar ([],c,c,c) .cap := .here

theorem E2_ctxIO_translate : E2PlatIO.ctx.translate = E2TCtx := rfl

/-- The platform context is well formed. -/
theorem E2_ctx_wf : DotMNF.Ctx.Wf E2PlatIO.ctx := DotMNF.Platform.ctx_wf _

/-- And so is the context the call is read in. -/
theorem E2_callCtx_wf : DotMNF.Ctx.Wf DotMNF.Examples.E2CtxF := .cons (.cons E2_ctx_wf)

/-! ### The platform verdicts

`Platform.admits_iff` turns the admission test at a platform capability into the
containment test of the classifier the platform declares, and the kernel decides
that. -/

/-- `except[ThreadLocal]` does not admit the thread-local capability. -/
theorem E2_admits_tl :
    E2PlatIO.ctx.translate.admitsB (CapAtom.cvar E2Ttl) (Cls.except Cls.ThreadLocal) = false := by
  rw [DotMNF.Platform.admits_iff E2PlatIO E2Ttl]
  decide

/-- Nor the control capability, because `Control` lies below `ThreadLocal`. -/
theorem E2_admits_ctl :
    E2PlatIO.ctx.translate.admitsB (CapAtom.cvar E2Tctl) (Cls.except Cls.ThreadLocal) = false := by
  rw [DotMNF.Platform.admits_iff E2PlatIO E2Tctl]
  decide

/-- And it does admit the input-output capability. -/
theorem E2_admits_io :
    E2PlatIO.ctx.translate.admitsB (CapAtom.cvar E2Tio) (Cls.except Cls.ThreadLocal) = true := by
  rw [DotMNF.Platform.admits_iff E2PlatIO E2Tio]
  decide

/-! ### The universal root through the filter

`⊤ᶜ` opens into itself and every opaque binder of the context, and the filter
then keeps only what the kind admits.  Over the classified platform both
capabilities are excluded, so the universal root projected at
`except[ThreadLocal]` has itself as its only root. -/

/-- **The roots of the projected universal root**, over the classified
platform. -/
theorem E2_roots_top :
    E2Plat.ctx.translate.roots 0 [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] = [⊤ᶜ] := by
  rw [E2_ctx_translate]
  exact K2x_roots

theorem E2_caps_top_io (n : Nat) :
    E2PlatIO.ctx.translate.caps n [⊤ᶜ ↾ Cls.except Cls.ThreadLocal]
      = [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] := by
  rw [E2_ctxIO_translate]
  simp [E2TCtx, Ctx.capsAtom_proj, Ctx.capsAtom_top]

/-- Over the program's platform the input-output capability survives, and the
two excluded capabilities still do not.  This is the positive half of the same
filter. -/
theorem E2_roots_top_io :
    E2PlatIO.ctx.translate.roots 0 [⊤ᶜ ↾ Cls.except Cls.ThreadLocal]
      = [⊤ᶜ, CapAtom.cvar E2Tio] := by
  rw [Ctx.roots_eq_expand_caps, E2_caps_top_io, E2_ctxIO_translate]
  decide

/-! ### The scope root of `Future.apply` through the filter

The body of `Future.apply` opens a scope root, and the parameter's declared set
is the arrow's own capture binder projected at `except[ThreadLocal]`.  The
projected body root opens into `⊤ᶜ`, the arrow's own capture binder and itself,
and into neither classified capability.  The arrow's binder survives because it
declares no classifier and reads as the root classifier, which
`except[ThreadLocal]` admits.  The two classified capabilities do not survive,
which is the sentence E2 makes about a program. -/

/-- The body context of `Future.apply` on the target, over the classified
platform. -/
def E2TBody : Ctx (Sig.body ([],c,c)) :=
  Ctx.cons (Ctx.consC (Ctx.consC K2Ctx .root) .star)
    (.opaque ((E2Dom : DotMNF.Dom ([],c,c)).underRoot.translate))

theorem E2_bodyCtx_translate : E2ClsBodyCtx.translate = E2TBody := rfl

/-- The arrow's own capture binder. -/
abbrev E2Karrow : BVar (Sig.body ([],c,c)) .cap := .there .here
/-- The body root of `Future.apply`. -/
abbrev E2Kroot : BVar (Sig.body ([],c,c)) .cap := .there (.there .here)
/-- The control capability, read inside the body. -/
abbrev E2Kctl : BVar (Sig.body ([],c,c)) .cap := .there (.there (.there .here))
/-- The thread-local capability, read inside the body. -/
abbrev E2Ktl : BVar (Sig.body ([],c,c)) .cap := .there (.there (.there (.there .here)))

theorem E2_caps_bodyRoot (n : Nat) :
    E2ClsBodyCtx.translate.caps n [(CapAtom.cvar E2Kroot) ↾ Cls.except Cls.ThreadLocal]
      = [(CapAtom.cvar E2Kroot) ↾ Cls.except Cls.ThreadLocal] := by
  rw [E2_bodyCtx_translate]
  simp [E2TBody, K2Ctx, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

theorem E2_caps_ctl (n : Nat) :
    E2ClsBodyCtx.translate.caps n [CapAtom.cvar E2Kctl] = [CapAtom.cvar E2Kctl] := by
  rw [E2_bodyCtx_translate]
  simp [E2TBody, K2Ctx, Ctx.capsAtom_cvar, Ctx.capsBound, CapBound.weaken, CapBound.rename]

/-- **The roots of the projected scope root**: the universal root, the arrow's
own capture binder, the root itself, and neither classified capability. -/
theorem E2_roots_bodyRoot :
    E2ClsBodyCtx.translate.roots 0 [(CapAtom.cvar E2Kroot) ↾ Cls.except Cls.ThreadLocal]
      = [⊤ᶜ, CapAtom.cvar E2Karrow, CapAtom.cvar E2Kroot] := by
  rw [Ctx.roots_eq_expand_caps, E2_caps_bodyRoot, E2_bodyCtx_translate]
  decide

/-- **So the control capability is not below the projected scope root.**  A
`Future` body written `cap.except[ThreadLocal]` does not reach it. -/
theorem E2_not_capLe :
    ¬ CapLe E2ClsBodyCtx.translate [CapAtom.cvar E2Kctl]
      [(CapAtom.cvar E2Kroot) ↾ Cls.except Cls.ThreadLocal] := by
  intro h
  obtain ⟨m, hm⟩ := h (CapAtom.cvar E2Kctl)
    ⟨0, by rw [Ctx.roots_eq_expand_caps, E2_caps_ctl, E2_bodyCtx_translate]; decide⟩
  rw [Ctx.roots_eq_expand_caps, E2_caps_bodyRoot, E2_bodyCtx_translate] at hm
  exact absurd hm (by decide)

/-! ### A bare root is kinded only at a kind that admits every classifier

`kproj` at an atom that is its own base asks that `Kind.top` be a subkind of the
target kind, and `Kind.top` is not a subkind of `except[ThreadLocal]`, even
though `except[ThreadLocal]` contains the root classifier.  The kinding of
`cap.except[ThreadLocal]` therefore rides on the projected atom, whose own kind
is the filter.  Both verdicts are decided. -/

/-- The bare universal root is rejected at `except[ThreadLocal]`. -/
theorem E2_kproj_root_reject :
    checkKindCo E2PlatIO.ctx.translate (.kproj ⊤ᶜ) [⊤ᶜ] (Cls.except Cls.ThreadLocal) = false := by
  rw [E2_ctxIO_translate]
  decide

/-- And the projected one is accepted. -/
theorem E2_kproj_projRoot_accept :
    checkKindCo E2PlatIO.ctx.translate (.kproj (⊤ᶜ ↾ Cls.except Cls.ThreadLocal))
      [⊤ᶜ ↾ Cls.except Cls.ThreadLocal] (Cls.except Cls.ThreadLocal) = true := by
  rw [E2_ctxIO_translate]
  decide

/-! ### The thread-local argument is refused

A body charged to the thread-local capability cannot be passed: the kinding
premise of `sc-proj` fails.  The checker rejects both rules that could conclude
it, and no source derivation exists at all, because the semantics of kinding
refutes it and every source derivation translates into semantics through T5. -/

theorem E2_caps_tl (n : Nat) :
    E2PlatIO.ctx.translate.caps n [CapAtom.cvar E2Ttl] = [CapAtom.cvar E2Ttl] := by
  rw [E2_ctxIO_translate]
  simp [E2TCtx, Ctx.capsAtom_cvar, Ctx.capsBound, CapBound.weaken, CapBound.rename]

/-- The thread-local capability is not kinded at `except[ThreadLocal]`. -/
theorem E2_tl_not_kindLe :
    ¬ E2PlatIO.ctx.translate.KindLe [CapAtom.cvar E2Ttl] (Cls.except Cls.ThreadLocal) := by
  intro h
  have hc := h (CapAtom.cvar E2Ttl)
    ⟨0, by rw [Ctx.roots_eq_expand_caps, E2_caps_tl, E2_ctxIO_translate]; decide⟩
  rw [E2_ctxIO_translate] at hc
  revert hc
  decide

/-- **No source derivation kinds it either.**  T5 reads a translated derivation
as the semantics, and the semantics is refuted. -/
theorem E2_tl_not_capKind
    (g : DotMNF.CapKind E2PlatIO.ctx [DotMNF.CapAtom.cvar E2tl] (Cls.except Cls.ThreadLocal)) :
    False :=
  E2_tl_not_kindLe (kind_canon E2PlatIO.targetStore_typed (g.translate_typed E2_ctx_wf))

theorem E2_caps_tlDescent (n : Nat) :
    E2PlatIO.ctx.translate.caps n E2TlDescent.translate = E2TlDescent.translate := by
  rw [E2_ctxIO_translate]
  simp [E2TCtx, DotMNF.Examples.E2TlDescent, DotMNF.CaptureSet.translate_proj, CaptureSet.proj,
    CapAtom.projBy, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

theorem E2_tlDescent_not_kindLe :
    ¬ E2PlatIO.ctx.translate.KindLe E2TlDescent.translate (Cls.except Cls.ThreadLocal) := by
  intro h
  have hc := h (CapAtom.cvar E2Ttl)
    ⟨0, by rw [Ctx.roots_eq_expand_caps, E2_caps_tlDescent, E2_ctxIO_translate]; decide⟩
  rw [E2_ctxIO_translate] at hc
  revert hc
  decide

/-- **And the premise `kvar` hands down is refused too**: the set an argument
declared at the thread-local capability descends to is not kinded at
`except[ThreadLocal]`, so the one rule that could have reached it fails at its
own premise. -/
theorem E2_tl_descent_not_capKind
    (g : DotMNF.CapKind E2PlatIO.ctx E2TlDescent (Cls.except Cls.ThreadLocal)) : False :=
  E2_tlDescent_not_kindLe (kind_canon E2PlatIO.targetStore_typed (g.translate_typed E2_ctx_wf))

/-- `k-label` at the thread-local capability, rejected by the checker. -/
theorem E2_kcls_tl_reject :
    checkKindCo E2PlatIO.ctx.translate (.kcls (CapAtom.cvar E2Ttl)) [CapAtom.cvar E2Ttl]
      (Cls.except Cls.ThreadLocal) = false := by
  rw [E2_ctxIO_translate]
  decide

/-- And `k-cbound` at it, likewise. -/
theorem E2_kproj_tl_reject :
    checkKindCo E2PlatIO.ctx.translate (.kproj (CapAtom.cvar E2Ttl)) [CapAtom.cvar E2Ttl]
      (Cls.except Cls.ThreadLocal) = false := by
  rw [E2_ctxIO_translate]
  decide

/-- The control capability is rejected the same way. -/
theorem E2_kcls_ctl_reject :
    checkKindCo E2PlatIO.ctx.translate (.kcls (CapAtom.cvar E2Tctl)) [CapAtom.cvar E2Tctl]
      (Cls.except Cls.ThreadLocal) = false := by
  rw [E2_ctxIO_translate]
  decide

/-! ### The input-output argument goes through -/

/-- `k-label` at the input-output capability, accepted. -/
theorem E2_kcls_io :
    checkKindCo E2PlatIO.ctx.translate (.kcls (CapAtom.cvar E2Tio)) [CapAtom.cvar E2Tio]
      (Cls.except Cls.ThreadLocal) = true := by
  rw [E2_ctxIO_translate]
  decide

theorem E2_caps_io (n : Nat) :
    E2PlatIO.ctx.translate.caps n [CapAtom.cvar E2Tio] = [CapAtom.cvar E2Tio] := by
  rw [E2_ctxIO_translate]
  simp [E2TCtx, Ctx.capsAtom_cvar, Ctx.capsBound, CapBound.weaken, CapBound.rename]

theorem E2_roots_io (n : Nat) :
    E2PlatIO.ctx.translate.roots n [CapAtom.cvar E2Tio] = [CapAtom.cvar E2Tio] := by
  rw [Ctx.roots_eq_expand_caps, E2_caps_io, E2_ctxIO_translate]
  decide

/-- And the input-output capability does carry a classifier the kind admits. -/
theorem E2_kindLe_io :
    E2PlatIO.ctx.translate.KindLe [CapAtom.cvar E2Tio] (Cls.except Cls.ThreadLocal) := by
  intro r hr
  obtain ⟨n, hn⟩ := hr
  rw [E2_roots_io] at hn
  have hr' : r = CapAtom.cvar E2Tio := by simpa using hn
  subst hr'
  rw [E2_ctxIO_translate]
  decide

/-! ### The filtered set is kinded, by T2

`Ctx.kindLe_proj` kinds a projected set by construction, and the translation of
a projected source set is the projection of its translation. -/

/-- The program's declared use set is kinded at `except[ThreadLocal]`. -/
theorem E2_kindLe_uses :
    E2PlatIO.ctx.translate.KindLe E2Filt.translate (Cls.except Cls.ThreadLocal) := by
  simp only [DotMNF.Examples.E2Filt, DotMNF.CaptureSet.translate_proj]
  exact Ctx.kindLe_proj _ _ _

theorem E2_caps_filt (n : Nat) :
    E2PlatIO.ctx.translate.caps n E2Filt.translate = E2Filt.translate := by
  rw [E2_ctxIO_translate]
  simp [E2TCtx, DotMNF.Examples.E2Filt, DotMNF.CaptureSet.translate_proj, CaptureSet.proj,
    CapAtom.projBy, Ctx.capsAtom_proj, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

/-- **And what it resolves to**: the input-output capability alone.  The program
reaches no thread-local capability and no control capability. -/
theorem E2_roots_filt :
    E2PlatIO.ctx.translate.roots 0 E2Filt.translate = [CapAtom.cvar E2Tio] := by
  rw [Ctx.roots_eq_expand_caps, E2_caps_filt, E2_ctxIO_translate]
  decide

/-! ### The source evidence, through the translation -/

/-- The program's translation is typed at the translated type. -/
theorem E2_translate_typed :
    Tm.HasType E2PlatIO.ctx.translate DotMNF.Examples.E2_typed.translate
      (DotMNF.ETy.translate (.ty DotMNF.Examples.E2Ty)) :=
  DotMNF.HasTy.translate_typed _ E2_ctx_wf

/-- The kinding of the use set translates to target kinding evidence. -/
theorem E2_kind_translate_typed :
    E2PlatIO.ctx.translate ⊢ᵏ DotMNF.Examples.E2_kind.translate :
      E2Filt.translate ⊑ᵏ (Cls.except Cls.ThreadLocal) :=
  DotMNF.CapKind.translate_typed _ E2_ctx_wf

/-- The translation of a source kinding derivation is a well-founded recursion,
so the kernel does not unfold it and `decide` says nothing about it.  The
checker's completeness closes the gap. -/
theorem E2_kind_checked :
    checkKindCo E2PlatIO.ctx.translate DotMNF.Examples.E2_kind.translate
      E2Filt.translate (Cls.except Cls.ThreadLocal) = true :=
  checkKindCo_iff_hasType.mpr E2_kind_translate_typed

/-- The local premise of the paper's sentence, through the translation: the
argument the call passes is kinded at `except[ThreadLocal]`. -/
theorem E2_arg_kind_translate_typed :
    DotMNF.Examples.E2CtxF.translate ⊢ᵏ DotMNF.Examples.E2_arg_kind.translate :
      (DotMNF.CaptureSet.translate [DotMNF.CapAtom.var (.there .here)]) ⊑ᵏ
        (Cls.except Cls.ThreadLocal) :=
  DotMNF.CapKind.translate_typed _ E2_callCtx_wf

/-- And the checker accepts it. -/
theorem E2_arg_kind_checked :
    checkKindCo DotMNF.Examples.E2CtxF.translate DotMNF.Examples.E2_arg_kind.translate
      (DotMNF.CaptureSet.translate [DotMNF.CapAtom.var (.there .here)])
      (Cls.except Cls.ThreadLocal) = true :=
  checkKindCo_iff_hasType.mpr E2_arg_kind_translate_typed

/-! ### Effect safety at `except[ThreadLocal]` -/

/-- The initial target state of E2's program. -/
def E2TgtInit : State ([],c,c,c) :=
  ⟨E2PlatIO.targetStore, .nil, DotMNF.Examples.E2_typed.translate⟩

/-- Its use set is kinded at `except[ThreadLocal]`: the declared use set bounds
it by `cap_canon`, and the declared use set is the filtered platform set. -/
theorem E2_initial_kindLe :
    E2PlatIO.ctx.translate.KindLe E2TgtInit.uses (Cls.except Cls.ThreadLocal) := by
  have hbase : CapLe E2PlatIO.ctx.translate E2TgtInit.uses E2Filt.translate := by
    simp only [E2TgtInit, State.uses_mk, usesK_nil, CaptureSet.union_def, List.append_nil]
    exact cap_canon E2PlatIO.targetStore_typed (DotMNF.HasTy.translate_uses _ E2_ctx_wf)
  exact Ctx.KindLe.mono hbase E2_kindLe_uses

/-- **E2 on the target.**  Along any run of the translated program, every root
of a variable the machine reads carries a classifier `except[ThreadLocal]`
admits.  This is `classified_effect_safety` at `except ThreadLocal`. -/
theorem E2_target_effect_safety {s' : Sig} {st' : State s'} {Γ' : Ctx s'}
    {x : BVar s' .var} (run : E2TgtInit ⟶* st') (hin : st'.inspects = some x)
    (hσ' : Store.Typed st'.σ Γ') :
    ∀ a : CapAtom s', Γ'.Root a [CapAtom.var x] →
      (Cls.except Cls.ThreadLocal).Contains (Γ'.classOf a) :=
  classified_effect_safety
    (DotMNF.Platform.initial_typed E2PlatIO DotMNF.Examples.E2_typed)
    E2PlatIO.targetStore_typed E2_initial_kindLe run hin hσ'

/-- **The run never reads a thread-local capability.** -/
theorem E2_never_tl {s' : Sig} {st' : State s'} {Γ' : Ctx s'} {x : BVar s' .var}
    (run : E2TgtInit ⟶* st') (hin : st'.inspects = some x)
    (hσ' : Store.Typed st'.σ Γ') (a : CapAtom s') (ha : Γ'.Root a [CapAtom.var x]) :
    Γ'.classOf a ≠ Cls.ThreadLocal := by
  intro h
  have hc := E2_target_effect_safety run hin hσ' a ha
  rw [h] at hc
  exact absurd hc (by decide)

/-- And never a control capability, because `Control` lies below
`ThreadLocal`. -/
theorem E2_never_ctl {s' : Sig} {st' : State s'} {Γ' : Ctx s'} {x : BVar s' .var}
    (run : E2TgtInit ⟶* st') (hin : st'.inspects = some x)
    (hσ' : Store.Typed st'.σ Γ') (a : CapAtom s') (ha : Γ'.Root a [CapAtom.var x]) :
    Γ'.classOf a ≠ Cls.Control := by
  intro h
  have hc := E2_target_effect_safety run hin hσ' a ha
  rw [h] at hc
  exact absurd hc (by decide)

/-- **E2 at the source**, through T9': the source program, its own kinding
evidence, and any source run.  The matched target state reads only capabilities
`except[ThreadLocal]` admits. -/
theorem E2_effect_safety {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps
      (⟨E2PlatIO.store, .nil, DotMNF.Examples.E2tm⟩ : DotMNF.State ([],c,c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : State s) (Γ' : Ctx s) (ρ : Rename ([],c,c,c) s),
      State.erase stt = st.erase ∧ Store.Typed stt.σ Γ' ∧
        Store.Ext E2PlatIO.targetStore stt.σ ρ ∧
          ∀ a : CapAtom s, Γ'.Root a [CapAtom.var x] →
            (Cls.except Cls.ThreadLocal).Contains (Γ'.classOf a) :=
  DotMNF.dot_classified_effect_safety' E2PlatIO DotMNF.Examples.E2_typed
    DotMNF.Examples.E2_kind run hin

end E2

/-! ## E3, C2 with a kind bound

The target side of `DotMNF.Examples`' E3.  The source is C2 with the capture
member's set bound `{}..{κ₁,κ₂}` replaced by the kind bound `only[Control]`,
over a platform whose two capabilities are both classified `Control`.  Here:
the platform context as the translation builds it, the decided verdicts of the
checker at both binders, the morphism the `capkI` step compiles to and its
canonical form, the client's `kmember`, capture prediction at `only[Control]`,
and the same verdicts again over a platform with a third `Control` capability.

Two things on this page carry the example.  The `capkI` morphism is a
`Morphism.kindCle` whose hole is the member's own upper bound and whose closed
kinding is the translation of the source `kcls`, and `mor_canon` reads it as a
normalized entry list typed at the one-entry telescope a kind-bounded member
compiles to.  And the client's charge is `KindCo.kmember` at index `0`, the
target's reading of the source's `ksel`: the closure's set `{x.C}` is kinded by
the member and is not widened to anything, because a kind bound offers no set to
widen to. -/

section E3cls

open DotMNF.Examples (E3Plat E3PlatCtx E3Plat3 E3Plat3Ctx E3k1 E3k2 E3k1' E3k2' E3k3
  E3Uses E3ClientCtx E3ClosureSet E3CtxB E3aSet lC)

/-- The platform context of E3, as `Platform.ctx` builds it. -/
theorem E3_platCtx : E3Plat.ctx = E3PlatCtx := rfl

/-- And the extended platform's. -/
theorem E3_plat3Ctx : E3Plat3.ctx = E3Plat3Ctx := rfl

/-- E3's platform on the target: two capture binders, both `cls Control`. -/
def E3TCtx : Ctx ([],c,c) :=
  Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.Control)) (.cls Cls.Control)

/-- `κ₁` on the target. -/
abbrev E3Tk1 : BVar ([],c,c) .cap := .there .here
/-- `κ₂` on the target. -/
abbrev E3Tk2 : BVar ([],c,c) .cap := .here

theorem E3_ctx_translate : E3Plat.ctx.translate = E3TCtx := rfl

/-- The extended platform on the target: one more `cls Control` binder. -/
def E3TCtx3 : Ctx ([],c,c,c) :=
  Ctx.consC (Ctx.consC (Ctx.consC Ctx.nil (.cls Cls.Control)) (.cls Cls.Control))
    (.cls Cls.Control)

/-- `κ₁` on the extended target platform. -/
abbrev E3Tk1' : BVar ([],c,c,c) .cap := .there (.there .here)
/-- `κ₂` on the extended target platform. -/
abbrev E3Tk2' : BVar ([],c,c,c) .cap := .there .here
/-- `κ₃`, the third `Control` capability, on the target. -/
abbrev E3Tk3 : BVar ([],c,c,c) .cap := .here

theorem E3_ctx3_translate : E3Plat3.ctx.translate = E3TCtx3 := rfl

/-- The platform context is well formed. -/
theorem E3_ctx_wf : DotMNF.Ctx.Wf E3Plat.ctx := DotMNF.Platform.ctx_wf _

/-- And so is the context the two literals are retyped in. -/
theorem E3_absCtx_wf : DotMNF.Ctx.Wf E3CtxB := .cons (.cons (.cons E3_ctx_wf))

/-- And so is the client's own context, two lambda bodies and the closure
binder above the platform. -/
theorem E3_clientCtx_wf : DotMNF.Ctx.Wf E3ClientCtx :=
  .cons (.cons (.consC (.consRoot (.cons (.consC (.consRoot E3_ctx_wf))))))

/-! ### The platform verdicts

`Platform.admits_iff` turns the admission test at a platform capability into the
containment test of the classifier the platform declares, and the kernel decides
that.  Both binders of E3 are `Control`, so both are admitted. -/

theorem E3_admits_k1 :
    E3Plat.ctx.translate.admitsB (CapAtom.cvar E3Tk1) (Cls.only Cls.Control) = true := by
  rw [DotMNF.Platform.admits_iff E3Plat E3Tk1]
  decide

theorem E3_admits_k2 :
    E3Plat.ctx.translate.admitsB (CapAtom.cvar E3Tk2) (Cls.only Cls.Control) = true := by
  rw [DotMNF.Platform.admits_iff E3Plat E3Tk2]
  decide

/-! ### The checker at the platform binders

`k-label` at each binder, decided in the kernel.  These are the two verdicts the
literals' `capkI` premises rest on. -/

theorem E3_kcls_k1 :
    checkKindCo E3Plat.ctx.translate (.kcls (CapAtom.cvar E3Tk1)) [CapAtom.cvar E3Tk1]
      (Cls.only Cls.Control) = true := by
  rw [E3_ctx_translate]
  decide

theorem E3_kcls_k2 :
    checkKindCo E3Plat.ctx.translate (.kcls (CapAtom.cvar E3Tk2)) [CapAtom.cvar E3Tk2]
      (Cls.only Cls.Control) = true := by
  rw [E3_ctx_translate]
  decide

/-! ### The resolution of the platform set

Both binders survive `only[Control]`, because both are `Control`.  The equation
for `Ctx.caps` is proved by `simp` over the clause lemmas and the expansion is
decided, in the manner of K1x. -/

theorem E3_caps_uses (n : Nat) :
    E3Plat.ctx.translate.caps n [CapAtom.cvar E3Tk1, CapAtom.cvar E3Tk2]
      = [CapAtom.cvar E3Tk1, CapAtom.cvar E3Tk2] := by
  rw [E3_ctx_translate]
  simp [E3TCtx, Ctx.capsAtom_cvar, Ctx.capsBound,
    CapBound.weaken, CapBound.rename]

theorem E3_roots_uses :
    E3Plat.ctx.translate.roots 0 [CapAtom.cvar E3Tk1, CapAtom.cvar E3Tk2]
      = [CapAtom.cvar E3Tk1, CapAtom.cvar E3Tk2] := by
  rw [Ctx.roots_eq_expand_caps, E3_caps_uses, E3_ctx_translate]
  decide

/-! ### The source evidence, through the translation -/

/-- The kinding of the program's use set translates to target kinding
evidence. -/
theorem E3_kind_translate_typed :
    E3Plat.ctx.translate ⊢ᵏ DotMNF.Examples.E3_kind.translate :
      E3Uses.translate ⊑ᵏ (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ E3_ctx_wf

/-- And the checker accepts it. -/
theorem E3_kind_checked :
    checkKindCo E3Plat.ctx.translate DotMNF.Examples.E3_kind.translate
      E3Uses.translate (Cls.only Cls.Control) = true :=
  checkKindCo_iff_hasType.mpr E3_kind_translate_typed

/-- The `kcls` the first literal's `capkI` premises, translated. -/
theorem E3_kind_a_translate_typed :
    E3CtxB.translate ⊢ᵏ DotMNF.Examples.E3_kind_a.translate :
      E3aSet.translate ⊑ᵏ (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ E3_absCtx_wf

/-- And the checker accepts it. -/
theorem E3_kind_a_checked :
    checkKindCo E3CtxB.translate DotMNF.Examples.E3_kind_a.translate
      E3aSet.translate (Cls.only Cls.Control) = true :=
  checkKindCo_iff_hasType.mpr E3_kind_a_translate_typed

/-- The whole program's translation is typed at the translated type. -/
theorem E3_translate_typed :
    Tm.HasType E3Plat.ctx.translate DotMNF.Examples.E3_typed.translate
      (DotMNF.ETy.translate (.ty DotMNF.Examples.E3Ty)) :=
  DotMNF.HasTy.translate_typed _ E3_ctx_wf

/-! ### The `capkI` morphism and its kinding entry

`SubShape.capkI` compiles to an object coercion whose morphism is one
`Morphism.kindCle`: a chain into the member's own upper bound, the capture hole
of the two-entry telescope a set-bounded member compiles to, a chain out of it,
and the closed kinding of the bound.  Its target is the one-entry telescope of a
kind-bounded member, `[name .here C] ⊑ᵏ only[Control]`.

`mor_canon` is what reads that entry: its `kindCle` case normalizes the two
chains with `sideC_canon` and the closed kinding with `kind_canon`, and the
semantic step behind the entry is `kindCle_semantic`. -/

/-- The morphism the first literal's `capkI` step compiles to. -/
def E3capkIMor : Morphism ([],c,c,x,x,x) :=
  .kindCle .nil .nil (.leC 1) .nil DotMNF.Examples.E3_kind_a.translate
    (Cls.only Cls.Control)

/-- **The `capkI` morphism is typed**, from the two-entry telescope of
`{C : {κ₁}..{κ₁}}` to the one-entry telescope of `{C : only[Control]}`. -/
theorem E3_capkI_mor :
    E3CtxB.translate ⊢ E3capkIMor :
      (DotMNF.Shape.cap lC E3aSet E3aSet).tel ⇒
        (DotMNF.Shape.capk lC (Cls.only Cls.Control)).tel := by
  rw [DotMNF.Shape.tel_capk]
  refine .kindCle .nil ?_ .nil .nil (DotMNF.CapKind.translate_typed _ E3_absCtx_wf)
  rw [DotMNF.Shape.tel_cap]
  exact .leC (Telescope.At.one_two _ _)

/-- **The kinding entry, canonically.**  `mor_canon` normalizes the morphism to
an entry list typed between the two telescopes.  The `kindCle` case is the one
that runs here, and the semantic step it carries is `kindCle_semantic`. -/
theorem E3_capkI_mor_canon {σ : Store ([],c,c,x,x,x)}
    (hσ : Store.Typed σ E3CtxB.translate) :
    MorConcl σ E3CtxB.translate (DotMNF.Shape.cap lC E3aSet E3aSet).tel E3capkIMor
      (DotMNF.Shape.capk lC (Cls.only Cls.Control)).tel :=
  mor_canon hσ E3_capkI_mor

/-! ### The client, charged by `kmember`

The source's `ksel` translates to `KindCo.kmember` at the member's own telescope
and index `0`, since a kind-bounded member compiles to a one-entry telescope.
That is the whole of the client's charge: the closure's set `{x.C}` is kinded,
and no subcapturing step widens it. -/

/-- The translation of the client's kinding is a `kmember`. -/
theorem E3_client_kind_kmember :
    DotMNF.Examples.E3_client_kind_plat.translate
      = KindCo.kmember DotMNF.Examples.E3xCapPlat.translateAtom
          (.refl (DotMNF.Shape.capk lC (Cls.only Cls.Control)).translate) 0 := by
  rw [DotMNF.Examples.E3_client_kind_plat, DotMNF.Examples.E3_client_kind,
    DotMNF.CapKind.translate.eq_def]
  rfl

/-- And it is typed at the translated set. -/
theorem E3_client_kind_translate_typed :
    E3ClientCtx.translate ⊢ᵏ DotMNF.Examples.E3_client_kind_plat.translate :
      E3ClosureSet.translate ⊑ᵏ (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ E3_clientCtx_wf

/-- And the checker accepts it. -/
theorem E3_client_kind_checked :
    checkKindCo E3ClientCtx.translate DotMNF.Examples.E3_client_kind_plat.translate
      E3ClosureSet.translate (Cls.only Cls.Control) = true :=
  checkKindCo_iff_hasType.mpr E3_client_kind_translate_typed

/-! ### Capture prediction at `only[Control]` -/

/-- The initial target state of E3's program. -/
def E3TgtInit : State ([],c,c) :=
  ⟨E3Plat.targetStore, .nil, DotMNF.Examples.E3_typed.translate⟩

/-- The program's declared use set is kinded at `only[Control]`, semantically:
`kind_canon` of the translated source evidence. -/
theorem E3_kindLe_uses :
    E3Plat.ctx.translate.KindLe E3Uses.translate (Cls.only Cls.Control) :=
  kind_canon E3Plat.targetStore_typed E3_kind_translate_typed

/-- **E3, capture prediction at `only[Control]`.**  `dot_classified_prediction`
at E3's platform, its program and its use set: along any source run the matched
target state's use set is below the declared one and is kinded at
`only[Control]`. -/
theorem E3_prediction {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps
      (⟨E3Plat.store, .nil, DotMNF.Examples.E3tm⟩ : DotMNF.State ([],c,c)) st) :
    ∃ (stt : State s) (Γ' : Ctx s) (ρ : Rename ([],c,c) s),
      State.erase stt = st.erase ∧ Store.Typed stt.σ Γ' ∧
        Store.Ext E3Plat.targetStore stt.σ ρ ∧
          CapLe Γ' stt.uses (E3Uses.translate.rename ρ) ∧
            Γ'.KindLe stt.uses (Cls.only Cls.Control) :=
  DotMNF.dot_classified_prediction E3Plat DotMNF.Examples.E3_typed E3_kindLe_uses run

/-- The same from the source's own kinding evidence, through T8'. -/
theorem E3_prediction' {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps
      (⟨E3Plat.store, .nil, DotMNF.Examples.E3tm⟩ : DotMNF.State ([],c,c)) st) :
    ∃ (stt : State s) (Γ' : Ctx s) (ρ : Rename ([],c,c) s),
      State.erase stt = st.erase ∧ Store.Typed stt.σ Γ' ∧
        Store.Ext E3Plat.targetStore stt.σ ρ ∧
          CapLe Γ' stt.uses (E3Uses.translate.rename ρ) ∧
            Γ'.KindLe stt.uses (Cls.only Cls.Control) :=
  DotMNF.dot_classified_prediction' E3Plat DotMNF.Examples.E3_typed
    DotMNF.Examples.E3_kind run

/-! ### Stability over the extended platform

One more `Platform.consCls`, one more `Control` capability, and every decided
verdict of the page above still holds.  The two platforms are stated side by
side so that the reader can see that no statement of the left one is rewritten
for the right one.  A set bound `{}..{κ₁,κ₂}` would have to become
`{}..{κ₁,κ₂,κ₃}`, and so would every derivation that reads it. -/

/-- **The checker's verdicts stand over both platforms.**  `k-label` at every
binder of E3's platform, and at every binder of the extended one. -/
theorem E3_stable_kcls :
    (checkKindCo E3TCtx (.kcls (CapAtom.cvar E3Tk1)) [CapAtom.cvar E3Tk1]
        (Cls.only Cls.Control) = true ∧
      checkKindCo E3TCtx (.kcls (CapAtom.cvar E3Tk2)) [CapAtom.cvar E3Tk2]
        (Cls.only Cls.Control) = true) ∧
    (checkKindCo E3TCtx3 (.kcls (CapAtom.cvar E3Tk1')) [CapAtom.cvar E3Tk1']
        (Cls.only Cls.Control) = true ∧
      checkKindCo E3TCtx3 (.kcls (CapAtom.cvar E3Tk2')) [CapAtom.cvar E3Tk2']
        (Cls.only Cls.Control) = true ∧
      checkKindCo E3TCtx3 (.kcls (CapAtom.cvar E3Tk3)) [CapAtom.cvar E3Tk3]
        (Cls.only Cls.Control) = true) := by decide

/-- **The admission verdicts stand over both platforms.** -/
theorem E3_stable_admits :
    (E3TCtx.admitsB (CapAtom.cvar E3Tk1) (Cls.only Cls.Control) = true ∧
      E3TCtx.admitsB (CapAtom.cvar E3Tk2) (Cls.only Cls.Control) = true) ∧
    (E3TCtx3.admitsB (CapAtom.cvar E3Tk1') (Cls.only Cls.Control) = true ∧
      E3TCtx3.admitsB (CapAtom.cvar E3Tk2') (Cls.only Cls.Control) = true ∧
      E3TCtx3.admitsB (CapAtom.cvar E3Tk3) (Cls.only Cls.Control) = true) := by decide

/-- The extended platform's set is kinded too, by the same rule one more
time. -/
theorem E3_kind3_translate_typed :
    E3Plat3.ctx.translate ⊢ᵏ DotMNF.Examples.E3_kind3.translate :
      DotMNF.CaptureSet.translate
        [DotMNF.CapAtom.cvar E3k1', DotMNF.CapAtom.cvar E3k2', DotMNF.CapAtom.cvar E3k3] ⊑ᵏ
        (Cls.only Cls.Control) :=
  DotMNF.CapKind.translate_typed _ (DotMNF.Platform.ctx_wf E3Plat3)

/-- And the third literal's retyping is typed at the target, with no change to
the member and no change to the client. -/
theorem E3_third_translate_typed :
    Tm.HasType DotMNF.Examples.E3CtxD.translate
      DotMNF.Examples.E3_abstract_c.translate
      (DotMNF.ETy.translate (.ty (DotMNF.Examples.E3AbsTyAt
        [DotMNF.CapAtom.cvar (.there (.there (.there .here))),
          DotMNF.CapAtom.cvar (.there (.there .here)),
          DotMNF.CapAtom.cvar (.there .here)]))) :=
  DotMNF.HasTy.translate_typed _ (.cons (DotMNF.Platform.ctx_wf E3Plat3))

end E3cls

end Examples
end FCdot

end Classifiers
