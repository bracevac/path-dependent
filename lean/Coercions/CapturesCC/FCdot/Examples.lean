import Coercions.CapturesCC.FCdot.Checker
import Coercions.CapturesCC.FCdot.LevelInversion
import Coercions.CapturesCC.FCdot.Erasure
import Coercions.CapturesCC.FCdot.Consistency
import Coercions.CapturesCC.FCdot.Prediction
import Coercions.CapturesCC.DotMNF.Examples
import Coercions.CapturesCC.DotMNF.Erasure
import Coercions.CapturesCC.DotToFCdot.Prediction

namespace CapturesCC

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
  have hroots : C6Ctx.roots n C6st0'.uses = C6Ctx.caps n C6st0'.uses :=
    Ctx.roots_eq_caps_of_rootFree rfl (by rw [C6_prog2_caps]; decide)
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

end Examples
end FCdot

end CapturesCC
