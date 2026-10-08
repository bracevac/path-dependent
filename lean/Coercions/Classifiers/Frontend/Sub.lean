import Coercions.Classifiers.Frontend.Look
import Coercions.Classifiers.Frontend.Search

/-!
# Subtyping, subcapturing, kinding and answers in the compiler's case order

The algorithm decides five goals.  `shp S T` asks for `S <: T` on shapes and
is answered by a `SubShape` derivation.  `cap C D` asks for `C <: D` on
capture sets and is answered by a `Subcap` derivation.  `kind C φ` asks that
every capability the set `C` reaches carry a classifier the kind `φ` admits,
and is answered by a `CapKind` derivation.  `esub E F` asks for `E <: F` on
answers and is answered by an `ESub` derivation.  An answer is a type, or a
type under a capture binder for `fresh`, `∃ᶜ[C₀] T`.  `var x V T` asks that
the variable `x`, already typed at the type `V`, have the type `T`.  It is
answered by a map from a derivation of `x` at `V` to one at `T`, at every use
set.  This is the compiler's singleton on the left: it keeps `x` while it
widens, so a recursive shape is opened at `x` (`TypeComparer.scala:742-744`,
`fixRecs` at `:1990-2005`).  The rules `Rec-I`, `Rec-E`, `And-I` and `sub`
with `Subcap.refl` on the use set keep the use set.

A type is a shape with a capture set, and `Sub` has the one rule `capt`.  So
two types compare by a set goal and a shape goal side by side, the set goal
first, as the compiler compares a capturing type: `compareCaptures` before the
parents (`TypeComparer.scala:548-566` on the left, `:876-907` on the right).

Each goal tries its alternatives in the compiler's order: identity
(`TypeComparer.scala:1626`), then `firstTry` on the right (`:300`), then
`secondTry` on the left (`:434`), then `thirdTry` on the right (`:652`), then
`fourthTry` on the left (`:981`).  An intersection on the right is final, as
in `firstTry` (`:401-402`).  A set includes its elements one by one
(`subCaptures`, `cc/CaptureSet.scala:307-320`).  An element is included by
identity, by a scope root at or inside its level, by a projected element of
the right set, by the bounds of a capture member, by an instance binder whose
witness holds it, or by its underlying set (`subsumes`,
`cc/Capability.scala:809-937`, and `accountsFor`,
`cc/CaptureSet.scala:251-267`).  A kind is the compiler's `transClassifiers`
(`cc/Capability.scala:684-710`) joined over a set
(`cc/CaptureSet.scala:460-462`) and tested by `isKnownClassifiedAs`
(`cc/Capability.scala:740-742`).  Each alternative is a function of its own
and emits the version's own derivation.  The middle of every transitivity
step is a bound of a member, an operand of an intersection, the declared set
of a variable, the witness of an instance binder, or a projection of a set
the goal names, read off what the algorithm already holds.  No middle is
chosen from the context.  Where the compiler tries two alternatives with
`either` (`TypeComparer.scala:2016`), each is tried in turn.

The forms the version forces to differ from the compiler are these.

1. The compiler compares `μ <: μ` through the parents
   (`TypeComparer.scala:738-740`) and a `μ` on the left by its parent
   (`:1063-1064`).  The version has no `μ` rule in `SubShape`, so a `μ` is
   opened only at a variable.
2. The compiler merges two members of one name (`Types.scala:5759`, and
   `hasMatchingMember` at `TypeComparer.scala:2235`).  The version has no rule
   for the merge, so each member is tried.
3. The compiler lets a boxed type pass where an unboxed one is expected when
   either capture set is empty (`isBoxCompatibleWith`,
   `cc/CaptureOps.scala:299-302`), and heals a box difference
   (`healBoxDifference`, `TypeComparer.scala:2971`).  `SubShape.box` relates
   boxes to boxes only.  The typer boxes and unboxes at a variable instead, by
   the box status of the two types (`cc/CheckCaptures.scala:1973-2006`).
4. The compiler compares a dependent function type through its
   non-dependent approximation, with each parameter replaced by its bound.
   `SubShape.all` reads the codomains under the second domain, which is full
   F<:.  So a goal can come back renamed under a new binder.  No cut catches
   that, and the tank ends it.
5. `Any` on the right ignores the left capture set in the compiler
   (`TypeComparer.scala:550`).  `Sub.capt` always asks the set goal.
6. The root `any` subsumes every capability in the compiler
   (`cc/Capability.scala:827`).  The version's `any` and `fresh` are inert.
   Only `Subcap.elem` mentions them.
7. A capture member on the left goes to its upper bound, which is then split
   element by element.  That is the fallback of `addNewElem` to the
   underlying set (`cc/CaptureSet.scala:216-225`).  `subsumes` takes another
   route to the same verdict: one element of the right set must subsume every
   element of the bound (`cc/Capability.scala:859`).
8. An atom below a capture member on the right is compared with the whole
   lower bound.  The compiler asks one element of the lower bound to subsume
   it (`cc/Capability.scala:874-881`).  This is a different route to the same
   verdict.
9. The level rule is directional.  The compiler compares owners by
   containment (`acceptsLevelOf`, `cc/Capability.scala:230-236`).
   `Subcap.level` asks for a scope root on the right.
10. The compiler's local root subsumes its hidden set
    (`cc/Capability.scala:918`).  The version's instance binder stands for the
    witness of a pack, and `Subcap.inst` puts the witness below it.
11. The version packs a plain answer at a witness (`ESub.pack`).  No case of
    the compiler packs.  Its nearest form is a local root that hides what
    flows into it, under a level test and a classifier test
    (`cc/Capability.scala:903-924`).  The witness is the answer's own capture
    set, then the bound: a choice the version forces.
12. The compiler keeps a singleton's capture set apart from its underlying
    type's (`TypeComparer.scala:892-895`), and widens a singleton to its
    whole underlying type at the set `{x}` (`:1050-1058`).  The version has no
    singleton types.  The `var` goal plays that part, from the view of the
    variable: its declared type at `{}` for a variable declared at `{}`, its
    declared shape at `{x}` for any other.  After the decompositions, the
    view that is left is compared with the goal whatever its shape, a
    selection included, as `tp1widened` is.  The compiler narrows to `{x}`
    only under a condition (`improveCaptures`, `cc/CheckCaptures.scala:2035`).
    The version's `Var` rule narrows always.
13. The compiler's classified capability carries an `only` class and a list
    of exclusions in a normal form, and a capability may be read-only or
    maybe (`cc/Capability.scala:85-155`).  The version's projected atom
    carries one kind, and has no read-only or maybe atom.  So a projected
    atom is kinded by the decided `subkindB`, where the compiler decides
    `isSubClass`.
14. The compiler strips the restriction of a right element when the left
    restriction is below it (`cc/Capability.scala:453-456`).
    `Subcap.projMono` asks for equal kinds.  So `{b ↾ ψ} <: {d ↾ φ}` with
    `ψ` below `φ` goes through the kinding of `{b ↾ ψ}` at `φ` and
    `Subcap.proj`, with the middle `{b ↾ ψ} ↾ φ`.
15. The compiler reads a capture member bounded by a kind, `{C : φ}`, as one
    whose upper bound is `{any.only[φ]}`, and widens through it.  The version
    gives such a member no upper set.  So `{x.C}` under a kind bound is
    reached only by kinding, never through a set.

A selection on the right skips a member whose lower bound is `⊥`, as
`isSubApproxHi` fails at once there (`TypeComparer.scala:1606-1607`).  A left
side that is `⊥` has already succeeded by the rule for `⊥`.

Member lookups go through `typs`, `caps` and `capks` of `Look.lean`.  Their
structural index is the fuel left in the tank.  Each lookup level draws at
least one unit, so the index never runs out before the tank does.

The run is the generic one of `Fuel.lean`, at the cost `cost`: one tank for
the whole run, the goals pending along the branch, and a goal that repeats
exactly fails.  A goal holds its context, so a goal under a new binder is
never cut by a goal outside it.  A kinding goal is a goal of the same run, so
kinding draws on the same tank and the same pending list.  `shp?`, `cap?`,
`kind?`, `sub?`, `esub?` and `var?` start a run from a full tank and return
the answer with the tank left.  `shpF`, `capF`, `kindF`, `varTyF`, `esubF`,
`subF` and `varF` run on a tank they are handed, for a caller that threads
one tank through many goals.

The step is framed and dominated (`step_frame`, `step_dom`), so the facts of
`Fuel.lean` hold for the run.  The functions on a handed tank are framed,
and the entry points keep an answer at any larger fuel (`shp?_mono`,
`cap?_mono`, `kind?_mono`, `esub?_mono`, `sub?_mono`, `var?_mono`).  A
kinding that ends with the tank unmarked has the same verdict at every larger
fuel (`kind?_stable`), so kinding needs no fuel of its own.

Every definition is structural, so the kernel evaluates the algorithm.  The
checks at the end of the module run it on the examples by `decide +kernel`.
-/

namespace ClassifiersFrontend.Core

open Frontend.Fuel
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy CapKind)
open Classifiers
open scoped Classifiers.DotMNF

deriving instance DecidableEq for Classifiers.DotMNF.Ctx

/-! ## Goals and answers -/

/-- The five goals of the algorithm. -/
inductive Q (s : Sig) where
  /-- `S <: T` on shapes. -/
  | shp (S T : Shape s)
  /-- `C <: D` on capture sets. -/
  | cap (C D : CaptureSet s)
  /-- Every capability `C` reaches carries a classifier `φ` admits. -/
  | kind (C : CaptureSet s) (φ : Cls.Kind)
  /-- `E <: F` on answers. -/
  | esub (E F : ETy s)
  /-- The variable `x`, typed at `V`, has the type `T`. -/
  | var (x : BVar s .var) (V T : Ty s)
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx s
  q : Q s
deriving DecidableEq

/-- A map from the variable `x` at the type `V` to `x` at the type `T`, at
every use set. -/
abbrev VarTy {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Ty s) : Type :=
  (U : CaptureSet s) → HasTy U Γ (.path (.var x)) (.ty V) → HasTy U Γ (.path (.var x)) (.ty T)

/-- The answer to a goal: a `SubShape`, `Subcap`, `CapKind` or `ESub`
derivation, or a map from the variable at one type to the variable at
another. -/
def RQ {s : Sig} (Γ : Ctx s) : Q s → Type
  | .shp S T => SubShape Γ S T
  | .cap C D => Subcap Γ C D
  | .kind C φ => CapKind Γ C φ
  | .esub E F => ESub Γ E F
  | .var x V T => VarTy Γ x V T

/-- The answer to a goal in its context. -/
def R (g : G) : Type := RQ g.Γ g.q

/-- The oracle an alternative asks: goals in the same context. -/
abbrev Rec {s : Sig} (Γ : Ctx s) := (q : Q s) → Fu (Option (RQ Γ q))

/-- The oracle for the codomains of two function shapes: goals in the body
of the second function, whose parameter is at its domain. -/
abbrev RecBody {s : Sig} (Γ : Ctx s) := (T2 : Dom s) → Rec (Γ.body T2)

/-- The oracle for the residual of a pack: goals in the scope whose instance
binder stands for the witness `W`. -/
abbrev RecInst {s : Sig} (Γ : Ctx s) := (W : CaptureSet s) → Rec (Γ.scopeInst W)

/-! ## Combinators on optional answers -/

/-- Run `c`, and map an answer through `f`. -/
def mapO {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (Option β) :=
  Fu.bind c fun o => Fu.ret (o.map f)

/-- Run `c`, and on an answer run `f` on it.  No answer stops here. -/
def bindO {α β : Type} (c : Fu (Option α)) (f : α → Fu (Option β)) : Fu (Option β) :=
  Fu.bind c fun
    | some a => f a
    | none => Fu.ret none

/-- The type members of `p` at `A`, looked up on the tank.  The index of the
lookup is the fuel left. -/
def typsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (TMem Γ p A)) :=
  fun t => typs Γ t.left p A t

/-- The capture members of `p` at `A` bounded by sets, looked up on the tank.
The index of the lookup is the fuel left. -/
def capsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (CMem Γ p A)) :=
  fun t => caps Γ t.left p A t

/-- The capture members of `p` at `A` bounded by a kind, looked up on the
tank.  The index of the lookup is the fuel left. -/
def capksAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (KMem Γ p A)) :=
  fun t => capks Γ t.left p A t

/-- The shape is an intersection. -/
def isAnd {s : Sig} : Shape s → Bool
  | .and _ _ => true
  | _ => false

/-! ## Derivations across a decided equation -/

/-- `SubShape.fld` across a decided label equality. -/
def subFld {s : Sig} {Γ : Ctx s} {a b : Label} {T U : Ty s} (h : a = b) (e : Sub Γ T U) :
    SubShape Γ (.fld a T) (.fld b U) := by
  cases h
  exact SubShape.fld e

/-- `SubShape.typ` across a decided label equality. -/
def subTyp {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Shape s} (h : A = B)
    (e1 : SubShape Γ S2 S1) (e2 : SubShape Γ T1 T2) : SubShape Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h
  exact SubShape.typ e1 e2

/-- `SubShape.cap` across a decided label equality. -/
def subCapM {s : Sig} {Γ : Ctx s} {A B : Label} {c1 c2 c1' c2' : CaptureSet s} (h : A = B)
    (e1 : Subcap Γ c1' c1) (e2 : Subcap Γ c2 c2') : SubShape Γ (.cap A c1 c2) (.cap B c1' c2') := by
  cases h
  exact SubShape.cap e1 e2

/-- `SubShape.capkI` across a decided label equality. -/
def subCapkI {s : Sig} {Γ : Ctx s} {A B : Label} {c1 c2 : CaptureSet s} {φ : Cls.Kind} (h : A = B)
    (g : CapKind Γ c2 φ) : SubShape Γ (.cap A c1 c2) (.capk B φ) := by
  cases h
  exact SubShape.capkI g

/-- `SubShape.capk` across a decided label equality. -/
def subCapk {s : Sig} {Γ : Ctx s} {A B : Label} {φ1 φ2 : Cls.Kind} (h : A = B)
    (hs : φ1.subkindB φ2 = true) : SubShape Γ (.capk A φ1) (.capk B φ2) := by
  cases h
  exact SubShape.capk hs

/-- `C₀ ↾ φ <: C₀ <: D`, for a set `L` decided equal to `C₀ ↾ φ`. -/
def unprojTo {s : Sig} {Γ : Ctx s} {C₀ L D : CaptureSet s} {φ : Cls.Kind}
    (h : CaptureSet.proj C₀ φ = L) (e : Subcap Γ C₀ D) : Subcap Γ L D := by
  cases h
  exact Subcap.trans Subcap.unproj e

/-- `C ↾ φ <: D ↾ φ` from `C <: D`, for sets decided equal to both sides. -/
def projMonoTo {s : Sig} {Γ : Ctx s} {C D L L' : CaptureSet s} {φ ψ : Cls.Kind}
    (h1 : CaptureSet.proj C φ = L) (h2 : CaptureSet.proj D ψ = L') (hk : φ = ψ)
    (e : Subcap Γ C D) : Subcap Γ L L' := by
  cases h1
  cases h2
  cases hk
  exact Subcap.projMono e

/-- `{a} <: {a} ↾ φ <: X ↾ φ`, from a kinding of `{a}` at `φ` and `{a} <: X`,
for a set decided equal to `X ↾ φ`. -/
def projThrough {s : Sig} {Γ : Ctx s} {a : CapAtom s} {X L : CaptureSet s} {φ : Cls.Kind}
    (hx : CaptureSet.proj X φ = L) (g : CapKind Γ [a] φ) (e : Subcap Γ [a] X) :
    Subcap Γ [a] L := by
  cases hx
  exact Subcap.trans (Subcap.proj g) (Subcap.projMono e)

/-- `CapKind.kprojS` across a decided equation of a projected set. -/
def kprojSTo {s : Sig} {Γ : Ctx s} {C₀ L : CaptureSet s} {ψ φ : Cls.Kind}
    (h : CaptureSet.proj C₀ ψ = L) (g : CapKind Γ C₀ φ) : CapKind Γ L φ := by
  cases h
  exact CapKind.kprojS g

/-- Two types by `Sub.capt`: the set goal, then the shape goal, as the
compiler compares a capturing type (`TypeComparer.scala:548-566` on the left,
`:876-907` on the right). -/
def tySub {s : Sig} {Γ : Ctx s} (r : Rec Γ) : (T U : Ty s) → Fu (Option (Sub Γ T U))
  | .capt C S, .capt C' S' =>
      bindO (r (.cap C C')) fun e2 =>
        mapO (r (.shp S S')) fun e1 => Sub.capt e1 e2

/-! ## The `shp` goal, one alternative per compiler case -/

section ShapeAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, `TypeComparer.scala:1626`. -/
def sRefl (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : S = T then some (h ▸ SubShape.refl) else none

/-- `Any` on the right, `thirdTryNamed`, `TypeComparer.scala:616`. -/
def sTop (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : T = .top then some (h ▸ SubShape.top) else none

/-- `Nothing` on the left, `secondTry`, `TypeComparer.scala:444-445`. -/
def sBot (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : S = .bot then some (h ▸ SubShape.bot) else none

/-- An intersection on the right, `firstTry`, `TypeComparer.scala:401-402`.
Both operands must hold. -/
def sAndR (r : Rec Γ) (S : Shape s) : (T : Shape s) → Fu (Option (SubShape Γ S T))
  | .and T1 T2 =>
      bindO (r (.shp S T1)) fun e1 =>
        mapO (r (.shp S T2)) fun e2 => SubShape.and e1 e2
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member,
`thirdTryNamed`, `TypeComparer.scala:601`.  Each member is tried.  A member
whose lower bound is `⊥` is skipped, as `isSubApproxHi` fails at once there
(`TypeComparer.scala:1606-1607`). -/
def sSelLo (r : Rec Γ) (S : Shape s) : (T : Shape s) → Fu (Option (SubShape Γ S T))
  | .sel (.var p) A =>
      Fu.bind (typsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.shp S d.1)) fun e => SubShape.trans e (SubShape.selLower d.2.2)) ds
  | _ => Fu.ret none

/-- Two fields, two type members, two capture members, two boxes or two
function shapes of one form, `thirdTry`.  Refinements go by
`compareRefinedSlow` and `hasMatchingMember` (`TypeComparer.scala:659-663,2235`).
Bounds go by `compareTypeBounds` (`:864-868`).  A capture member's bounds are
capture set types, so its bounds go to two set goals.  A capture member
bounded by sets is below one bounded by a kind when its upper bound is
classified by the kind, the restricted case of `subsumes`
(`cc/Capability.scala:868-871`), and two kind bounds compare by their kinds
(`:851-852`).  Two boxed capturing types compare by their types
(`TypeComparer.scala:555-564`).  Functions have contravariant parameters, by
`isSubInfo` (`:675-708`).  The domains are compared in a scope of their own,
and the codomains as answers in the body of the second function. -/
def sStruct (r : Rec Γ) (rS : Rec Γ.scope) (rB : RecBody Γ) :
    (S T : Shape s) → Fu (Option (SubShape Γ S T))
  | .fld a T1, .fld b T2 =>
      if h : a = b then mapO (tySub r T1 T2) (subFld h) else Fu.ret none
  | .typ A S1 T1, .typ B S2 T2 =>
      if h : A = B then
        bindO (r (.shp S2 S1)) fun e1 =>
          mapO (r (.shp T1 T2)) fun e2 => subTyp h e1 e2
      else Fu.ret none
  | .cap A c1 c2, .cap B c1' c2' =>
      if h : A = B then
        bindO (r (.cap c1' c1)) fun e1 =>
          mapO (r (.cap c2 c2')) fun e2 => subCapM h e1 e2
      else Fu.ret none
  | .cap A _ c2, .capk B φ =>
      if h : A = B then mapO (r (.kind c2 φ)) (subCapkI h) else Fu.ret none
  | .capk A φ1, .capk B φ2 =>
      if h : A = B then
        if hs : φ1.subkindB φ2 = true then Fu.ret (some (subCapk h hs)) else Fu.ret none
      else Fu.ret none
  | .box T1, .box T2 => mapO (tySub r T1 T2) SubShape.box
  | .all T1 U1, .all T2 U2 =>
      bindO (tySub rS (Dom.underRoot T2) (Dom.underRoot T1)) fun e1 =>
        mapO (rB T2 (.esub (Cod.underRoot U1) (Cod.underRoot U2))) fun e2 => SubShape.all e1 e2
  | _, _ => Fu.ret none

/-- A selection on the left, through the upper bound of a member, `fourthTry`,
`TypeComparer.scala:982-992`.  Each member is tried. -/
def sSelHi (r : Rec Γ) (T : Shape s) : (S : Shape s) → Fu (Option (SubShape Γ S T))
  | .sel (.var q) B =>
      Fu.bind (typsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TMem Γ q B =>
          mapO (r (.shp d.2.1 T)) fun e => SubShape.trans (SubShape.selUpper d.2.2) e) ds
  | _ => Fu.ret none

/-- An intersection on the left, `fourthTry`, `TypeComparer.scala:1077-1099`.
The left operand first, then the right one, as `either` does (`:2016`). -/
def sAndL (r : Rec Γ) (T : Shape s) : (S : Shape s) → Fu (Option (SubShape Γ S T))
  | .and S1 S2 =>
      Fu.orElse (mapO (r (.shp S1 T)) fun e => SubShape.trans SubShape.and1 e) fun _ =>
        mapO (r (.shp S2 T)) fun e => SubShape.trans SubShape.and2 e
  | _ => Fu.ret none

end ShapeAlts

/-- The `shp` goal: the alternatives in the compiler's order.  An
intersection on the right is final: when `T` is one, nothing after `sAndR` is
tried. -/
def shpStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rS : Rec Γ.scope) (rB : RecBody Γ)
    (S T : Shape s) : Fu (Option (SubShape Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>
  Fu.orElse (Fu.ret (sBot S T)) fun _ =>
  if isAnd T then sAndR r S T else
  Fu.orElse (sSelLo r S T) fun _ =>
  Fu.orElse (sStruct r rS rB S T) fun _ =>
  Fu.orElse (sSelHi r T S) fun _ =>
  sAndL r T S

/-! ## The `cap` goal, one alternative per compiler case -/

/-- The capture binders a set names, `κ` for each atom `{κ}`. -/
def capVars {s : Sig} (D : CaptureSet s) : List (BVar s .cap) :=
  D.filterMap fun
    | .cvar κ => some κ
    | _ => none

/-- The capture members a set names, `y.A` for each atom `{y.A}`. -/
def selAtoms {s : Sig} (D : CaptureSet s) : List (BVar s .var × Label) :=
  D.filterMap fun
    | .sel y A => some (y, A)
    | _ => none

section CapAlts

variable {s : Sig} {Γ : Ctx s}

/-- An inclusion, `accountsFor` by `subsumes` (`cc/CaptureSet.scala:251-259`)
at `this eq y` (`cc/Capability.scala:826`). -/
def cElem (C D : CaptureSet s) : Option (Subcap Γ C D) :=
  if h : CaptureSet.Subset C D then some (Subcap.elem h) else none

/-- A set of two or more atoms, atom by atom: `tryInclude` with `forall`
(`cc/CaptureSet.scala:201-204`), called from `subCaptures` (`:307-320`). -/
def cUnion (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | a :: b :: C, D =>
      bindO (r (.cap [a] D)) fun e1 =>
        mapO (r (.cap (b :: C) D)) fun e2 => Subcap.union (C1 := [a]) (C2 := b :: C) e1 e2
  | _, _ => Fu.ret none

/-- One atom below a scope root that the right set names, when the atom is at
or outside the root's level: a local root subsumes what its level accepts
(`maxSubsumes` and `acceptsLevelOf`, `cc/Capability.scala:920,230-236`).
Each binder of the right set is tried. -/
def cLevel : (C D : CaptureSet s) → Option (Subcap Γ C D)
  | [a], D =>
      (capVars D).findSome? fun κ =>
        if h1 : Γ.IsRoot (.cvar κ) then
          if h2 : Γ.LvlLe a (.cvar κ) then
            if hm : CaptureSet.Subset [CapAtom.cvar κ] D then
              some (Subcap.trans (Subcap.level h1 h2) (Subcap.elem hm))
            else none
          else none
        else none
  | _, _ => none

/-- One projected atom below a projected atom of the right set at the same
kind: the restriction of the right element is stripped
(`cc/Capability.scala:851-852`, `stripRestricted` at `:453-456`), and the
atoms under the projections compare, by `Subcap.projMono`.  Each atom of the
right set is tried. -/
def cProjMono (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      match unprojSetW? [a] with
      | some ⟨p, h1⟩ =>
          Fu.firstSome (fun x : CapAtom s =>
            match unprojSetW? [x] with
            | some ⟨q, h2⟩ =>
                if hk : p.2 = q.2 then
                  if hm : CaptureSet.Subset [x] D then
                    mapO (r (.cap p.1 q.1)) fun e =>
                      Subcap.trans (projMonoTo h1 h2 hk e) (Subcap.elem hm)
                  else Fu.ret none
                else Fu.ret none
            | none => Fu.ret none) D
      | none => Fu.ret none
  | _, _ => Fu.ret none

/-- One projected atom, its restriction dropped: a restricted element is
below its base (`cc/Capability.scala:851-852`), by `Subcap.unproj`. -/
def cProjL (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      match unprojSetW? [a] with
      | some ⟨p, h⟩ => mapO (r (.cap p.1 D)) fun e => unprojTo h e
      | none => Fu.ret none
  | _, _ => Fu.ret none

/-- A capture member on the left, through its upper bound: the fallback of
`addNewElem` to the underlying set (`cc/CaptureSet.scala:216-225`).  Each
member is tried. -/
def cSelHi (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [.sel y A], D =>
      Fu.bind (capsAt Γ y A) fun ds =>
        Fu.firstSome (fun d : CMem Γ y A =>
          mapO (r (.cap d.2.1 D)) fun e => Subcap.trans (Subcap.selUpper d.2.2) e) ds
  | _, _ => Fu.ret none

/-- One atom below a projected atom `X ↾ φ` of the right set: the atom is
classified as `φ` and below `X`, the restricted case of `subsumes`
(`cc/Capability.scala:868-871`, `isKnownClassifiedAs` at `:740-742`), by
`Subcap.proj` and `Subcap.projMono`.  Each atom of the right set is tried. -/
def cProjR (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      Fu.firstSome (fun x : CapAtom s =>
        match unprojSetW? [x] with
        | some ⟨p, hx⟩ =>
            if hm : CaptureSet.Subset [x] D then
              bindO (r (.kind [a] p.2)) fun g =>
                mapO (r (.cap [a] p.1)) fun e =>
                  Subcap.trans (projThrough hx g e) (Subcap.elem hm)
            else Fu.ret none
        | none => Fu.ret none) D
  | _, _ => Fu.ret none

/-- One atom below a capture member that the right set names, through the
member's lower bound: `subsumes` with `this` a `CapSet` type reference
(`cc/Capability.scala:874-881`).  Each selection of the right set and each
member is tried. -/
def cSelLo (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      Fu.firstSome (fun p : BVar s .var × Label =>
        if h : CaptureSet.Subset [CapAtom.sel p.1 p.2] D then
          Fu.bind (capsAt Γ p.1 p.2) fun ds =>
            Fu.firstSome (fun d : CMem Γ p.1 p.2 =>
              mapO (r (.cap [a] d.1)) fun e =>
                Subcap.trans e (Subcap.trans (Subcap.selLower d.2.2) (Subcap.elem h))) ds
        else Fu.ret none) (selAtoms D)
  | _, _ => Fu.ret none

/-- One atom below an instance binder that the right set names, when the
binder's witness holds the atom: a local root subsumes its hidden set
(`cc/Capability.scala:918`).  Each binder of the right set is tried. -/
def cInst (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      Fu.firstSome (fun κ : BVar s .cap =>
        match h : Γ.instSet? κ with
        | some W =>
            if hm : CaptureSet.Subset [CapAtom.cvar κ] D then
              mapO (r (.cap [a] W)) fun e =>
                Subcap.trans e (Subcap.trans (Subcap.inst h) (Subcap.elem hm))
            else Fu.ret none
        | none => Fu.ret none) (capVars D)
  | _, _ => Fu.ret none

/-- A term variable on the left, widened to the capture set it is declared
at: `accountsFor` through `captureSetOfInfo` (`cc/CaptureSet.scala:262-267`,
`cc/Capability.scala:639-658`). -/
def cVar (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [.var x], D => mapO (r (.cap (Γ.lookup x).captureSet D)) fun e => Subcap.trans Subcap.var e
  | _, _ => Fu.ret none

/-- A restricted term variable or capture member on the left, widened to its
underlying set under the same restriction: `accountsFor` through
`captureSetOfInfo` (`cc/CaptureSet.scala:259-267`), which restricts the
underlying set of a classified capability (`:1755-1761`).  `{y ↾ φ}` goes to
`y`'s declared set restricted to `φ`, by `Subcap.projMono` of `Subcap.var`.
`{y.C ↾ φ}` goes to the upper bound of a member restricted to `φ`, by
`Subcap.projMono` of `Subcap.selUpper`.  Each member is tried. -/
def cProjVar (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [.proj (.var y) φ], D =>
      mapO (r (.cap (CaptureSet.proj (Γ.lookup y).captureSet φ) D)) fun e =>
        Subcap.trans (Subcap.projMono (C := [.var y]) (ψ := φ) Subcap.var) e
  | [.proj (.sel y A) φ], D =>
      Fu.bind (capsAt Γ y A) fun ds =>
        Fu.firstSome (fun d : CMem Γ y A =>
          mapO (r (.cap (CaptureSet.proj d.2.1 φ) D)) fun e =>
            Subcap.trans (Subcap.projMono (C := [.sel y A]) (ψ := φ) (Subcap.selUpper d.2.2)) e) ds
  | _, _ => Fu.ret none

end CapAlts

/-- The `cap` goal: the alternatives in the compiler's order.  A whole
inclusion first, then the split into atoms, then a root on the right, then a
projected atom against a projected atom or without its restriction, then the
upper bound of a capture member, then a projected atom on the right, then the
lower bound of a capture member, then an instance binder on the right, then
the declared set of a variable, restricted or not. -/
def capStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (C D : CaptureSet s) : Fu (Option (Subcap Γ C D)) :=
  Fu.orElse (Fu.ret (cElem C D)) fun _ =>
  Fu.orElse (cUnion r C D) fun _ =>
  Fu.orElse (Fu.ret (cLevel C D)) fun _ =>
  Fu.orElse (cProjMono r C D) fun _ =>
  Fu.orElse (cProjL r C D) fun _ =>
  Fu.orElse (cSelHi r C D) fun _ =>
  Fu.orElse (cProjR r C D) fun _ =>
  Fu.orElse (cSelLo r C D) fun _ =>
  Fu.orElse (cInst r C D) fun _ =>
  Fu.orElse (cVar r C D) fun _ =>
  cProjVar r C D

/-! ## The `kind` goal, one alternative per compiler case -/

section KindAlts

variable {s : Sig} {Γ : Ctx s}

/-- The empty set, the empty join (`cc/CaptureSet.scala:462`). -/
def kNil (φ : Cls.Kind) : (C : CaptureSet s) → Option (CapKind Γ C φ)
  | [] => some CapKind.nil
  | _ => none

/-- A set of two or more atoms, the join over its atoms
(`cc/CaptureSet.scala:460-462`). -/
def kCons (r : Rec Γ) (φ : Cls.Kind) : (C : CaptureSet s) → Fu (Option (CapKind Γ C φ))
  | a :: b :: C =>
      bindO (r (.kind [a] φ)) fun g =>
        mapO (r (.kind (b :: C) φ)) fun h => CapKind.cons g h
  | _ => Fu.ret none

/-- An atom whose restriction is a subkind of `φ`: a restriction classifies
the capability as its `only` class (`cc/Capability.scala:698-699`). -/
def kProj (φ : Cls.Kind) : (C : CaptureSet s) → Option (CapKind Γ C φ)
  | [a] => if h : a.kindOf.subkindB φ = true then some (CapKind.kproj h) else none
  | _ => none

/-- An atom whose binder declares a classifier that `φ` admits whenever the
atom's restriction does: the inherited classifier
(`cc/Capability.scala:705`). -/
def kCls (φ : Cls.Kind) : (C : CaptureSet s) → Option (CapKind Γ C φ)
  | [a] =>
      match hc : Γ.clsOf? a.base with
      | some c =>
          if h2 : (a.kindOf.containsB c = true → φ.containsB c = true) then
            some (CapKind.kcls hc h2)
          else none
      | none => none
  | _ => none

/-- A member bounded by the kind `ψ` at `φ`: `CapKind.ksel` when the kinds are
equal, else `CapKind.ksub` behind it when `ψ` is a subkind of `φ`. -/
def kselOf {x : BVar s .var} {A : Label} (φ : Cls.Kind) (d : KMem Γ x A) :
    Option (CapKind Γ [.sel x A] φ) :=
  if h : d.1 = φ then some (h ▸ CapKind.ksel d.2)
  else if hs : d.1.subkindB φ = true then some (CapKind.ksub (CapKind.ksel d.2) hs)
  else none

/-- A capture member bounded by a kind: the upper bound `any.only[ψ]` of a
capture parameter (`cc/Capability.scala:706`).  Each member is tried. -/
def kSel (φ : Cls.Kind) : (C : CaptureSet s) → Fu (Option (CapKind Γ C φ))
  | [.sel x A] =>
      Fu.bind (capksAt Γ x A) fun ds =>
        Fu.firstSome (fun d : KMem Γ x A => Fu.ret (kselOf φ d)) ds
  | _ => Fu.ret none

/-- An atom whose base is a term variable or an instance binder: the
underlying set under the atom's restriction (`cc/Capability.scala:706`,
`cc/CaptureSet.scala:1755-1761`), by `CapKind.kvar` or `CapKind.kcvar`. -/
def kVar (r : Rec Γ) (φ : Cls.Kind) : (C : CaptureSet s) → Fu (Option (CapKind Γ C φ))
  | [a] =>
      match hb : a.base with
      | .var x =>
          mapO (r (.kind (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ)) (CapKind.kvar hb)
      | .cvar κ =>
          match hi : Γ.instSet? κ with
          | some C => mapO (r (.kind (CaptureSet.proj C a.kindOf) φ)) (CapKind.kcvar hb hi)
          | none => Fu.ret none
      | _ => Fu.ret none
  | _ => Fu.ret none

/-- A capture member bounded by sets: the underlying set of a capture
parameter, its upper bound (`cc/Capability.scala:706`), by `CapKind.kle`
along `Subcap.selUpper`.  Each member is tried. -/
def kSelUp (r : Rec Γ) (φ : Cls.Kind) : (C : CaptureSet s) → Fu (Option (CapKind Γ C φ))
  | [.sel x A] =>
      Fu.bind (capsAt Γ x A) fun ds =>
        Fu.firstSome (fun d : CMem Γ x A =>
          mapO (r (.kind d.2.1 φ)) fun g => CapKind.kle (Subcap.selUpper d.2.2) g) ds
  | _ => Fu.ret none

/-- A projected atom under a restriction it does not need: the classifiers
of the base (`cc/Capability.scala:697`), by `CapKind.kprojS`. -/
def kProjS (r : Rec Γ) (φ : Cls.Kind) : (C : CaptureSet s) → Fu (Option (CapKind Γ C φ))
  | [a] =>
      match unprojSetW? [a] with
      | some ⟨p, h⟩ => mapO (r (.kind p.1 φ)) fun g => kprojSTo h g
      | none => Fu.ret none
  | _ => Fu.ret none

end KindAlts

/-- The `kind` goal: the empty set, the join, the restriction, the declared
classifier, a kind bound, the underlying set of a variable or an instance
binder, the upper bound of a set-bounded member, then the base of a
projected atom. -/
def kindStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (C : CaptureSet s) (φ : Cls.Kind) :
    Fu (Option (CapKind Γ C φ)) :=
  Fu.orElse (Fu.ret (kNil φ C)) fun _ =>
  Fu.orElse (kCons r φ C) fun _ =>
  Fu.orElse (Fu.ret (kProj φ C)) fun _ =>
  Fu.orElse (Fu.ret (kCls φ C)) fun _ =>
  Fu.orElse (kSel φ C) fun _ =>
  Fu.orElse (kVar r φ C) fun _ =>
  Fu.orElse (kSelUp r φ C) fun _ =>
  kProjS r φ C

/-! ## The `var` goal, one alternative per compiler case -/

section VarAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, `TypeComparer.scala:1626`. -/
def vRefl (x : BVar s .var) (V T : Ty s) : Option (VarTy Γ x V T) :=
  if h : V = T then some (fun _ d => h ▸ d) else none

/-- An intersection on the right under a capture set, `firstTry`, which
splits `(p1 & p2) ^ C` into `p1 ^ C` and `p2 ^ C`
(`TypeComparer.scala:883-884`), by `HasTy.andI`. -/
def vAndR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.and T1 T2) =>
      bindO (r (.var x V (T1 ^ C))) fun f1 =>
        mapO (r (.var x V (T2 ^ C))) fun f2 U d => HasTy.andI (f1 U d) (f2 U d)
  | _ => Fu.ret none

/-- A recursive shape on the right with a singleton on the left, `thirdTry`,
`TypeComparer.scala:742-744`.  `fixRecs` (`:1990-2005`) opens the body at the
variable, and so does `HasTy.recI`, for a body that is a declaration. -/
def vMuR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.mu B) =>
      if hB : Shape.Decl B then
        mapO (r (.var x V ((B.substVar x) ^ C))) fun f U d => HasTy.recI (f U d) hB
      else Fu.ret none
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, the
variable kept, `thirdTryNamed`, `TypeComparer.scala:601`.  Each member is
tried.  A member whose lower bound is `⊥` is skipped
(`TypeComparer.scala:1606-1607`). -/
def vSelLo (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.sel (.var p) A) =>
      Fu.bind (typsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.var x V (d.1 ^ C))) fun f U e =>
            HasTy.sub (f U e) (ESub.ty (Sub.capt (SubShape.selLower d.2.2) Subcap.refl))
              Subcap.refl) ds
  | _ => Fu.ret none

/-- A recursive shape in the view, opened at the variable, `fourthTry`: the
singleton widened (`TypeComparer.scala:1036-1058`), then the recursive shape
as `findMember`'s `goRec` opens it (`Types.scala:875-896`), by `HasTy.recE`,
for a body that is a declaration. -/
def vMuL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.mu B) =>
      if hB : Shape.Decl B then
        mapO (r (.var x ((B.substVar x) ^ C) T)) fun f U d => f U (HasTy.recE d hB)
      else Fu.ret none
  | _ => Fu.ret none

/-- An intersection in the view, `fourthTry`, `TypeComparer.scala:1077-1099`.
The left operand first, then the right one, as `either` does (`:2016`). -/
def vAndL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.and V1 V2) =>
      Fu.orElse (mapO (r (.var x (V1 ^ C) T)) fun f U d =>
          f U (HasTy.sub d (ESub.ty (Sub.capt SubShape.and1 Subcap.refl)) Subcap.refl)) fun _ =>
        mapO (r (.var x (V2 ^ C) T)) fun f U d =>
          f U (HasTy.sub d (ESub.ty (Sub.capt SubShape.and2 Subcap.refl)) Subcap.refl)
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member, `fourthTry`,
`TypeComparer.scala:982-992`.  Each member is tried. -/
def vSelHi (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarTy Γ x V T))
  | .capt C (.sel (.var q) B) =>
      Fu.bind (typsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TMem Γ q B =>
          mapO (r (.var x (d.2.1 ^ C) T)) fun f U e =>
            f U (HasTy.sub e (ESub.ty (Sub.capt (SubShape.selUpper d.2.2) Subcap.refl))
              Subcap.refl)) ds
  | _ => Fu.ret none

/-- The view against the goal, `fourthTry`: the singleton widened to its
whole underlying type at its own set, a selection included, as `tp1widened`
is (`TypeComparer.scala:1050-1058`), then compared as a capturing type, by
subsumption. -/
def vWiden (r : Rec Γ) (x : BVar s .var) (V T : Ty s) : Fu (Option (VarTy Γ x V T)) :=
  mapO (tySub r V T) fun e _ d => HasTy.sub d (ESub.ty e) Subcap.refl

end VarAlts

/-- The `var` goal: the variable `x`, typed at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  An intersection on the right is final. -/
def varStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (x : BVar s .var) (V T : Ty s) :
    Fu (Option (VarTy Γ x V T)) :=
  Fu.orElse (Fu.ret (vRefl x V T)) fun _ =>
  if isAnd T.shape then vAndR r x V T else
  Fu.orElse (vMuR r x V T) fun _ =>
  Fu.orElse (vSelLo r x V T) fun _ =>
  Fu.orElse (vMuL r x T V) fun _ =>
  Fu.orElse (vAndL r x T V) fun _ =>
  Fu.orElse (vSelHi r x T V) fun _ =>
  vWiden r x V T

/-! ## The `esub` goal, one alternative per form of answer -/

section ESubAlts

variable {s : Sig} {Γ : Ctx s}

/-- Two plain answers, two result types compared (`isSubInfo`,
`TypeComparer.scala:682`), by `ESub.ty`. -/
def eTy (r : Rec Γ) : (E F : ETy s) → Fu (Option (ESub Γ E F))
  | .ty T, .ty T' => mapO (tySub r T T') ESub.ty
  | _, _ => Fu.ret none

/-- A plain answer below an existential, by `ESub.pack`.  The witness is
below the bound, and the answer is below the body in the scope whose instance
binder stands for the witness.  The witness is the answer's own capture set,
then the bound: a finite `either` over two sets the goal names. -/
def ePack (r : Rec Γ) (rI : RecInst Γ) : (E F : ETy s) → Fu (Option (ESub Γ E F))
  | .ty T', .ex C₀ T =>
      Fu.firstSome (fun W =>
        bindO (r (.cap W C₀)) fun e1 =>
          mapO (tySub (rI W) ((T'.weaken (k := .cap)).weaken (k := .cap))
              (Dom.underRoot (s := s) T)) fun e2 => ESub.pack e1 e2) [T'.captureSet, C₀]
  | _, _ => Fu.ret none

/-- Two existentials, two result capabilities unified
(`cc/Capability.scala:927`), by `ESub.exist`: the bounds, then the bodies in
a scope of their own. -/
def eExist (r : Rec Γ) (rS : Rec Γ.scope) : (E F : ETy s) → Fu (Option (ESub Γ E F))
  | .ex C₀ T, .ex C₀' T' =>
      bindO (r (.cap C₀ C₀')) fun e1 =>
        mapO (tySub rS (Dom.underRoot (s := s) T) (Dom.underRoot (s := s) T')) fun e2 =>
          ESub.exist e1 e2
  | _, _ => Fu.ret none

end ESubAlts

/-- The `esub` goal: two plain answers, a plain answer packed, two
existentials. -/
def esubStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rS : Rec Γ.scope) (rI : RecInst Γ)
    (E F : ETy s) : Fu (Option (ESub Γ E F)) :=
  Fu.orElse (eTy r E F) fun _ =>
  Fu.orElse (ePack r rI E F) fun _ =>
  eExist r rS E F

/-! ## The step and the entry points -/

/-- One step of the algorithm.  A goal in `Γ` asks goals in `Γ`.  The
domains of two function shapes and the bodies of two existentials are asked
in `Γ.scope`, the codomains in `Γ.body T2`, and the residual of a pack in
`Γ.scopeInst W`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .shp S T⟩ =>
      shpStep Γ (fun q => o ⟨s, Γ, q⟩) (fun q => o ⟨_, Γ.scope, q⟩)
        (fun T2 q => o ⟨_, Γ.body T2, q⟩) S T
  | ⟨s, Γ, .cap C D⟩ => capStep Γ (fun q => o ⟨s, Γ, q⟩) C D
  | ⟨s, Γ, .kind C φ⟩ => kindStep Γ (fun q => o ⟨s, Γ, q⟩) C φ
  | ⟨s, Γ, .esub E F⟩ =>
      esubStep Γ (fun q => o ⟨s, Γ, q⟩) (fun q => o ⟨_, Γ.scope, q⟩)
        (fun W q => o ⟨_, Γ.scopeInst W, q⟩) E F
  | ⟨s, Γ, .var x V T⟩ => varStep Γ (fun q => o ⟨s, Γ, q⟩) x V T

/-- `S <: T` on shapes, on the tank it is handed.  The run's index is the
fuel left. -/
def shpF {s : Sig} (Γ : Ctx s) (S T : Shape s) : Fu (Option (SubShape Γ S T)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .shp S T⟩ t

/-- `C <: D` on capture sets, on the tank it is handed. -/
def capF {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Fu (Option (Subcap Γ C D)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .cap C D⟩ t

/-- `C` at the kind `φ`, on the tank it is handed. -/
def kindF {s : Sig} (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) : Fu (Option (CapKind Γ C φ)) :=
  fun t => run cost step t.left [] ⟨s, Γ, .kind C φ⟩ t

/-- The variable `x`, typed at `V`, at the type `T`, on the tank it is
handed. -/
def varTyF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Ty s) : Fu (Option (VarTy Γ x V T)) :=
  fun t => run cost step t.left [] ⟨s, Γ, .var x V T⟩ t

/-- `E <: F` on answers, on the tank it is handed. -/
def esubF {s : Sig} (Γ : Ctx s) (E F : ETy s) : Fu (Option (ESub Γ E F)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .esub E F⟩ t

/-- `T <: U` on types, on the tank it is handed: the set goal, then the shape
goal. -/
def subF {s : Sig} (Γ : Ctx s) : (T U : Ty s) → Fu (Option (Sub Γ T U))
  | .capt C S, .capt C' S' =>
      bindO (capF Γ C C') fun e2 =>
        mapO (shpF Γ S S') fun e1 => Sub.capt e1 e2

/-- The variable `x`, typed at `V` with the use set `U`, at the type `T`: the
`var` goal from `V`. -/
def varFrom {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s) (V : Ty s)
    (d : HasTy U Γ (.path (.var x)) (.ty V)) (T : Ty s) :
    Fu (Option ((U' : CaptureSet s) × HasTy U' Γ (.path (.var x)) (.ty T))) :=
  mapO (varTyF Γ x V T) fun f => ⟨U, f U d⟩

/-- `x : T` on the tank it is handed, from the first view of `x`
(`varView`): a variable declared at `{}` is used at `{}` at its declared
type, any other at `{x}` at its declared shape. -/
def varF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    Fu (Option ((U : CaptureSet s) × HasTy U Γ (.path (.var x)) (.ty T))) :=
  varFrom Γ x (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv T

/-- `S <: T` on shapes from a full tank of `n` units, with the tank left. -/
def shp? {s : Sig} (Γ : Ctx s) (S T : Shape s) (n : Nat := defaultFuel) :
    Option (SubShape Γ S T) × Tank :=
  shpF Γ S T ⟨n, false⟩

/-- `C <: D` on capture sets from a full tank of `n` units, with the tank
left. -/
def cap? {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) (n : Nat := defaultFuel) :
    Option (Subcap Γ C D) × Tank :=
  capF Γ C D ⟨n, false⟩

/-- `C` at the kind `φ` from a full tank of `n` units, with the tank left. -/
def kind? {s : Sig} (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) (n : Nat := defaultFuel) :
    Option (CapKind Γ C φ) × Tank :=
  kindF Γ C φ ⟨n, false⟩

/-- `T <: U` on types from a full tank of `n` units, with the tank left. -/
def sub? {s : Sig} (Γ : Ctx s) (T U : Ty s) (n : Nat := defaultFuel) : Option (Sub Γ T U) × Tank :=
  subF Γ T U ⟨n, false⟩

/-- `E <: F` on answers from a full tank of `n` units, with the tank left. -/
def esub? {s : Sig} (Γ : Ctx s) (E F : ETy s) (n : Nat := defaultFuel) :
    Option (ESub Γ E F) × Tank :=
  esubF Γ E F ⟨n, false⟩

/-- `x : T` from a full tank of `n` units, with its use set and the tank
left. -/
def var? {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) (n : Nat := defaultFuel) :
    Option ((U : CaptureSet s) × HasTy U Γ (.path (.var x)) (.ty T)) × Tank :=
  varF Γ x T ⟨n, false⟩

/-! ## The lookups at the tank's own index

`typsAt`, `capsAt` and `capksAt` run a lookup whose index is the fuel left.
With more fuel the index is larger.  A lookup that ends unmarked never
reached index zero, so it gives the same answers at any larger index.  So
all three are framed, as every computation of a step must be. -/

/-- Either branch of a test agrees with its partner, so the tests agree. -/
theorem ite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' b b' : Fu α} (ha : Agree a a')
    (hb : Agree b b') : Agree (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- A test whose branches read its proof agrees with its partner when the
branches do. -/
theorem dite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Agree (a h) (a' h)) (hb : ∀ h, Agree (b h) (b' h)) :
    Agree (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-- A lookup at a larger index does what the lookup at a smaller one does. -/
theorem look_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ (P : List (LKey s)) (x : BVar s .var) (V : Shape s) (k : Key),
      Agree (look Γ d P x V k) (look Γ d' P x V k)
  | 0, d', _, P, x, V, k => by
    refine ⟨look_framed Γ 0 P x V k, look_framed Γ d' P x V k, ?_⟩
    intro t r t' h ho _
    simp only [look, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, x, V, k => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := look_agree Γ d e (by omega)
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply ite_agree (ret_agree _)
      cases V with
      | mu B =>
        exact dite_agree (fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _)
          (fun _ => ret_agree _)
      | and V1 V2 =>
        exact bind_agree (ih _ _ _ _) fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _
      | sel p B =>
        cases p with
        | var q =>
          refine bind_agree (ih _ _ _ _) fun es => flatMapL_agree ?_ es
          intro e
          split
          · exact bind_agree (ih _ _ _ _) fun _ => ret_agree _
          · exact ret_agree _
      | top => exact ret_agree _
      | bot => exact ret_agree _
      | typ _ _ _ => exact ret_agree _
      | fld _ _ => exact ret_agree _
      | cap _ _ _ => exact ret_agree _
      | capk _ _ => exact ret_agree _
      | all _ _ => exact ret_agree _
      | box _ => exact ret_agree _

/-- A member lookup that ends unmarked gives the same answers at a larger
index, for every reader. -/
theorem members_index {s : Sig} {β : Type} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {k : Key}
    {pick : Found Γ p (Γ.lookup p).shape → Option β} {t : Tank}
    (h : (members Γ d p k pick t).2.out = false) (hd : d ≤ d') :
    members Γ d' p k pick t = members Γ d p k pick t := by
  have hag : Agree (members Γ d p k pick) (members Γ d' p k pick) :=
    bind_agree (look_agree Γ d d' hd _ _ _ _) fun _ => ret_agree _
  have := hag.sim t _ _ rfl h 0
  simpa using this

/-- A type member lookup that ends unmarked gives the same answers at a
larger index. -/
theorem typs_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (typs Γ d p A t).2.out = false) (hd : d ≤ d') : typs Γ d' p A t = typs Γ d p A t :=
  members_index h hd

/-- A capture member lookup that ends unmarked gives the same answers at a
larger index. -/
theorem caps_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (caps Γ d p A t).2.out = false) (hd : d ≤ d') : caps Γ d' p A t = caps Γ d p A t :=
  members_index h hd

/-- A lookup of capture members bounded by a kind that ends unmarked gives
the same answers at a larger index. -/
theorem capks_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (capks Γ d p A t).2.out = false) (hd : d ≤ d') : capks Γ d' p A t = capks Γ d p A t :=
  members_index h hd

/-- A member lookup at the tank's own index is framed, for every reader. -/
theorem membersAt_framed {s : Sig} {β : Type} (Γ : Ctx s) (p : BVar s .var) (k : Key)
    (pick : Found Γ p (Γ.lookup p).shape → Option β) :
    Framed (fun t => members Γ t.left p k pick t) where
  absorbs t ht := (members_framed Γ t.left p k pick).absorbs t ht
  spends t := (members_framed Γ t.left p k pick).spends t
  shift := by
    intro t r t' h ho k'
    have h1 := members_frame h ho k'
    have h2 : (members Γ t.left p k pick (t.add k')).2.out = false := by
      rw [h1]
      exact ho
    change members Γ (t.left + k') p k pick (t.add k') = _
    rw [members_index h2 (Nat.le_add_right _ _), h1]

/-- The type member lookup at the tank's own index is framed. -/
theorem typsAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (typsAt Γ p A) :=
  membersAt_framed Γ p _ _

/-- The capture member lookup at the tank's own index is framed. -/
theorem capsAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (capsAt Γ p A) :=
  membersAt_framed Γ p _ _

/-- The lookup of capture members bounded by a kind at the tank's own index
is framed. -/
theorem capksAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (capksAt Γ p A) :=
  membersAt_framed Γ p _ _

/-! ## The step is framed and dominated

`FrameF step` says that oracles which agree give answers which agree.
`DomF step` says that an oracle which dominates another gives answers which
dominate.  `run_frame`, `run_index` and `cut_complete` of `Fuel.lean` ask for
both.  Each alternative is built from `Fu.ret`, `Fu.bind`, `Fu.orElse`,
`Fu.firstSome`, `mapO`, `bindO`, `typsAt`, `capsAt`, `capksAt`, tests and
matches on decided values.  So each has an agreement lemma and a dominance
lemma, each a composition of the combinator lemmas.  An alternative at one
oracle agrees with itself, so it is framed.  The two facts of the step follow
by cases on the five goals. -/

section Tests

variable {α : Type}

/-- Either branch of a test dominates its partner, so the tests do. -/
theorem ite_dom {p : Prop} [hp : Decidable p] {m : Nat} {a a' b b' : Fu α} (ha : Dom m a a')
    (hb : Dom m b b') : Dom m (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- A test whose branches read its proof dominates its partner when the
branches do. -/
theorem dite_dom {p : Prop} [hp : Decidable p] {m : Nat} {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Dom m (a h) (a' h)) (hb : ∀ h, Dom m (b h) (b' h)) :
    Dom m (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

end Tests

section OptionFrames

variable {α β : Type} {m : Nat}

/-- Mapping an answer keeps a computation framed. -/
theorem mapO_framed {c : Fu (Option α)} (f : α → β) (hc : Framed c) : Framed (mapO c f) :=
  bind_framed hc fun _ => ret_framed _

/-- Mapping an answer keeps two computations in agreement. -/
theorem mapO_agree {c c' : Fu (Option α)} (f : α → β) (hc : Agree c c') :
    Agree (mapO c f) (mapO c' f) :=
  bind_agree hc fun _ => ret_agree _

/-- Mapping an answer keeps a dominance. -/
theorem mapO_dom {c c' : Fu (Option α)} (f : α → β) (hc : Framed c) (hd : Dom m c c') :
    Dom m (mapO c f) (mapO c' f) :=
  bind_dom hc (fun _ => ret_framed _) hd fun _ => ret_dom _ m

/-- A framed computation, then a framed one on its answer, is framed. -/
theorem bindO_framed {c : Fu (Option α)} {f : α → Fu (Option β)} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) : Framed (bindO c f) :=
  bind_framed hc fun
    | some a => hf a
    | none => ret_framed _

/-- Two computations that agree, each followed by continuations that agree,
agree. -/
theorem bindO_agree {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Agree c c')
    (hf : ∀ a, Agree (f a) (f' a)) : Agree (bindO c f) (bindO c' f') :=
  bind_agree hc fun
    | some a => hf a
    | none => ret_agree _

/-- A dominance followed by a dominance on every answer is a dominance. -/
theorem bindO_dom {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) (hd : Dom m c c') (hfd : ∀ a, Dom m (f a) (f' a)) :
    Dom m (bindO c f) (bindO c' f') :=
  bind_dom hc (fun | some a => hf a | none => ret_framed _) hd fun
    | some a => hfd a
    | none => ret_dom _ m

end OptionFrames

/-! ### Two types

The agreement lemmas take oracles `r` and `r'` that agree on every goal.  The
dominance lemmas take a framed `r` that dominates `r'` below `m`. -/

section TyFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem tySub_agree (hr : ∀ q, Agree (r q) (r' q)) (T U : Ty s) :
    Agree (tySub r T U) (tySub r' T U) := by
  cases T
  cases U
  exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)

theorem tySub_framed (hF : ∀ q, Framed (r q)) (T U : Ty s) : Framed (tySub r T U) :=
  (tySub_agree (fun q => Agree.refl (hF q)) T U).left

theorem tySub_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T U : Ty s) :
    Dom m (tySub r T U) (tySub r' T U) := by
  cases T
  cases U
  exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)

end TyFrames

/-! ### The alternatives of the `shp` goal

The lemmas of `sStruct` and `shpStep` also take the hypotheses of the
oracle for the domains of two functions, `hS`, `hSF` and `hSd`, and of the
oracle for their codomains, `hB`, `hBF` and `hBd`, at every second domain. -/

section ShapeFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rS rS' : Rec Γ.scope} {rB rB' : RecBody Γ}
  {m : Nat}

theorem sAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Shape s) :
    Agree (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Shape s) :
    Dom m (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Shape s) :
    Agree (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      exact bind_agree (Agree.refl (typsAt_framed Γ p A)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
  | _ => exact ret_agree _

theorem sSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Shape s) :
    Dom m (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      have hf : ∀ d : TMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
          else mapO (r (.shp S d.1)) fun e => SubShape.trans e (SubShape.selLower d.2.2)) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (typsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
        ((typsAt_framed Γ p A).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
  | _ => exact ret_dom _ m

theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q)) (hS : ∀ q, Agree (rS q) (rS' q))
    (hB : ∀ T2 q, Agree (rB T2 q) (rB' T2 q)) (S T : Shape s) :
    Agree (sStruct r rS rB S T) (sStruct r' rS' rB' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact dite_agree (fun _ => mapO_agree _ (tySub_agree hr _ _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => dite_agree (fun _ => ret_agree _) fun _ => ret_agree _)
        fun _ => ret_agree _
    | exact mapO_agree _ (tySub_agree hr _ _)
    | exact bindO_agree (tySub_agree hS _ _) fun _ => mapO_agree _ (hB _ _)

theorem sStruct_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hSF : ∀ q, Framed (rS q)) (hSd : ∀ q, Dom m (rS q) (rS' q))
    (hBF : ∀ T2 q, Framed (rB T2 q)) (hBd : ∀ T2 q, Dom m (rB T2 q) (rB' T2 q))
    (S T : Shape s) : Dom m (sStruct r rS rB S T) (sStruct r' rS' rB' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact dite_dom (fun _ => mapO_dom _ (tySub_framed hF _ _) (tySub_dom hF hd _ _))
        fun _ => ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact dite_dom (fun _ => dite_dom (fun _ => ret_dom _ m) fun _ => ret_dom _ m)
        fun _ => ret_dom _ m
    | exact mapO_dom _ (tySub_framed hF _ _) (tySub_dom hF hd _ _)
    | exact bindO_dom (tySub_framed hSF _ _) (fun _ => mapO_framed _ (hBF _ _))
        (tySub_dom hSF hSd _ _) fun _ => mapO_dom _ (hBF _ _) (hBd _ _)

theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Shape s) :
    Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_agree (Agree.refl (typsAt_framed Γ q B)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | _ => exact ret_agree _

theorem sSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Shape s) :
    Dom m (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_dom (typsAt_framed Γ q B)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((typsAt_framed Γ q B).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | _ => exact ret_dom _ m

theorem sAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Shape s) :
    Agree (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Shape s) :
    Dom m (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem shpStep_agree (hr : ∀ q, Agree (r q) (r' q)) (hS : ∀ q, Agree (rS q) (rS' q))
    (hB : ∀ T2 q, Agree (rB T2 q) (rB' T2 q)) (S T : Shape s) :
    Agree (shpStep Γ r rS rB S T) (shpStep Γ r' rS' rB' S T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (sAndR_agree hr S T) <|
    orElse_agree (sSelLo_agree hr S T) <| orElse_agree (sStruct_agree hr hS hB S T) <|
    orElse_agree (sSelHi_agree hr T S) (sAndL_agree hr T S)

theorem shpStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hSF : ∀ q, Framed (rS q)) (hSd : ∀ q, Dom m (rS q) (rS' q))
    (hBF : ∀ T2 q, Framed (rB T2 q)) (hBd : ∀ T2 q, Dom m (rB T2 q) (rB' T2 q))
    (S T : Shape s) : Dom m (shpStep Γ r rS rB S T) (shpStep Γ r' rS' rB' S T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hS : ∀ q, Agree (rS q) (rS q) := fun q => Agree.refl (hSF q)
  have hB : ∀ T2 q, Agree (rB T2 q) (rB T2 q) := fun _ _ => Agree.refl (hBF _ _)
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    ite_dom (sAndR_dom hF hd S T) <|
    orElse_dom (sSelLo_agree hr S T).left (sSelLo_dom hF hd S T) <|
    orElse_dom (sStruct_agree hr hS hB S T).left (sStruct_dom hF hd hSF hSd hBF hBd S T) <|
    orElse_dom (sSelHi_agree hr T S).left (sSelHi_dom hF hd T S) (sAndL_dom hF hd T S)

end ShapeFrames

/-! ### The alternatives of the `cap` goal

`cElem` and `cLevel` ask no goal.  Each is `Fu.ret` of an answer, covered by
`ret_agree` and `ret_dom` inside `capStep`. -/

section CapFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem cUnion_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cUnion r C D) (cUnion r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [_] => exact ret_agree _
  | _ :: _ :: _ => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)

theorem cUnion_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cUnion r C D) (cUnion r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [_] => exact ret_dom _ m
  | _ :: _ :: _ =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)

theorem cInst_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cInst r C D) (cInst r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [_] =>
    refine firstSome_agree (fun κ => ?_) _
    split
    · exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem cInst_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cInst r C D) (cInst r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [_] =>
    refine firstSome_dom (fun κ => ?_) (fun κ => ?_) _
    · split
      · exact dite_framed (fun _ => mapO_framed _ (hF _)) fun _ => ret_framed _
      · exact ret_framed _
    · split
      · exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
      · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem cSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cSelHi r C D) (cSelHi r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [.sel y A] =>
    exact bind_agree (Agree.refl (capsAt_framed Γ y A)) fun ds =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | [.var _] => exact ret_agree _
  | [.cvar _] => exact ret_agree _
  | [.any] => exact ret_agree _
  | [.fresh] => exact ret_agree _
  | [.proj _ _] => exact ret_agree _
  | a :: _ :: _ => cases a <;> exact ret_agree _

theorem cSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cSelHi r C D) (cSelHi r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [.sel y A] =>
    exact bind_dom (capsAt_framed Γ y A)
      (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
      ((capsAt_framed Γ y A).dom m) fun ds =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | [.var _] => exact ret_dom _ m
  | [.cvar _] => exact ret_dom _ m
  | [.any] => exact ret_dom _ m
  | [.fresh] => exact ret_dom _ m
  | [.proj _ _] => exact ret_dom _ m
  | a :: _ :: _ => cases a <;> exact ret_dom _ m

theorem cSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cSelLo r C D) (cSelLo r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [_] =>
    exact firstSome_agree (fun p => dite_agree (fun _ =>
      bind_agree (Agree.refl (capsAt_framed Γ p.1 p.2)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds) fun _ => ret_agree _) _
  | _ :: _ :: _ => exact ret_agree _

theorem cSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cSelLo r C D) (cSelLo r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [_] =>
    exact firstSome_dom
      (fun p => dite_framed (fun _ => bind_framed (capsAt_framed Γ p.1 p.2) fun ds =>
        firstSome_framed (fun _ => mapO_framed _ (hF _)) ds) fun _ => ret_framed _)
      (fun p => dite_dom (fun _ => bind_dom (capsAt_framed Γ p.1 p.2)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((capsAt_framed Γ p.1 p.2).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds)
        fun _ => ret_dom _ m) _
  | _ :: _ :: _ => exact ret_dom _ m

theorem cVar_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cVar r C D) (cVar r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [.var _] => exact mapO_agree _ (hr _)
  | [.sel _ _] => exact ret_agree _
  | [.cvar _] => exact ret_agree _
  | [.any] => exact ret_agree _
  | [.fresh] => exact ret_agree _
  | [.proj _ _] => exact ret_agree _
  | a :: _ :: _ => cases a <;> exact ret_agree _

theorem cVar_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cVar r C D) (cVar r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [.var _] => exact mapO_dom _ (hF _) (hd _)
  | [.sel _ _] => exact ret_dom _ m
  | [.cvar _] => exact ret_dom _ m
  | [.any] => exact ret_dom _ m
  | [.fresh] => exact ret_dom _ m
  | [.proj _ _] => exact ret_dom _ m
  | a :: _ :: _ => cases a <;> exact ret_dom _ m

theorem cProjMono_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cProjMono r C D) (cProjMono r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [a] =>
    dsimp only [cProjMono]
    split
    · refine firstSome_agree (fun x => ?_) _
      split
      · exact dite_agree (fun _ => dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _)
          fun _ => ret_agree _
      · exact ret_agree _
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem cProjMono_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (C D : CaptureSet s) : Dom m (cProjMono r C D) (cProjMono r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [a] =>
    dsimp only [cProjMono]
    split
    · refine firstSome_dom (fun x => ?_) (fun x => ?_) _
      · split
        · exact dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (hF _))
            fun _ => ret_framed _) fun _ => ret_framed _
        · exact ret_framed _
      · split
        · exact dite_dom (fun _ => dite_dom (fun _ => mapO_dom _ (hF _) (hd _))
            fun _ => ret_dom _ m) fun _ => ret_dom _ m
        · exact ret_dom _ m
    · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem cProjL_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cProjL r C D) (cProjL r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [a] =>
    dsimp only [cProjL]
    split
    · exact mapO_agree _ (hr _)
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem cProjL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cProjL r C D) (cProjL r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [a] =>
    dsimp only [cProjL]
    split
    · exact mapO_dom _ (hF _) (hd _)
    · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem cProjR_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cProjR r C D) (cProjR r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [a] =>
    refine firstSome_agree (fun x => ?_) _
    split
    · exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _))
        fun _ => ret_agree _
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem cProjR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cProjR r C D) (cProjR r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [a] =>
    refine firstSome_dom (fun x => ?_) (fun x => ?_) _
    · split
      · exact dite_framed (fun _ => bindO_framed (hF _) fun _ => mapO_framed _ (hF _))
          fun _ => ret_framed _
      · exact ret_framed _
    · split
      · exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
          fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
      · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem cProjVar_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cProjVar r C D) (cProjVar r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [.proj (.var _) _] => exact mapO_agree _ (hr _)
  | [.proj (.sel y A) _] =>
    exact bind_agree (Agree.refl (capsAt_framed Γ y A)) fun ds =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | [.proj (.cvar _) _] => exact ret_agree _
  | [.proj .any _] => exact ret_agree _
  | [.proj .fresh _] => exact ret_agree _
  | [.proj (.proj _ _) _] => exact ret_agree _
  | [.var _] => exact ret_agree _
  | [.sel _ _] => exact ret_agree _
  | [.cvar _] => exact ret_agree _
  | [.any] => exact ret_agree _
  | [.fresh] => exact ret_agree _
  | a :: _ :: _ =>
    cases a with
    | proj b _ => cases b <;> exact ret_agree _
    | _ => exact ret_agree _

theorem cProjVar_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (C D : CaptureSet s) : Dom m (cProjVar r C D) (cProjVar r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [.proj (.var _) _] => exact mapO_dom _ (hF _) (hd _)
  | [.proj (.sel y A) _] =>
    exact bind_dom (capsAt_framed Γ y A)
      (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
      ((capsAt_framed Γ y A).dom m) fun ds =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | [.proj (.cvar _) _] => exact ret_dom _ m
  | [.proj .any _] => exact ret_dom _ m
  | [.proj .fresh _] => exact ret_dom _ m
  | [.proj (.proj _ _) _] => exact ret_dom _ m
  | [.var _] => exact ret_dom _ m
  | [.sel _ _] => exact ret_dom _ m
  | [.cvar _] => exact ret_dom _ m
  | [.any] => exact ret_dom _ m
  | [.fresh] => exact ret_dom _ m
  | a :: _ :: _ =>
    cases a with
    | proj b _ => cases b <;> exact ret_dom _ m
    | _ => exact ret_dom _ m

theorem capStep_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (capStep Γ r C D) (capStep Γ r' C D) :=
  orElse_agree (ret_agree _) <| orElse_agree (cUnion_agree hr C D) <|
    orElse_agree (ret_agree _) <| orElse_agree (cProjMono_agree hr C D) <|
    orElse_agree (cProjL_agree hr C D) <| orElse_agree (cSelHi_agree hr C D) <|
    orElse_agree (cProjR_agree hr C D) <| orElse_agree (cSelLo_agree hr C D) <|
    orElse_agree (cInst_agree hr C D) <| orElse_agree (cVar_agree hr C D) (cProjVar_agree hr C D)

theorem capStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (capStep Γ r C D) (capStep Γ r' C D) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (cUnion_agree hr C D).left (cUnion_dom hF hd C D) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (cProjMono_agree hr C D).left (cProjMono_dom hF hd C D) <|
    orElse_dom (cProjL_agree hr C D).left (cProjL_dom hF hd C D) <|
    orElse_dom (cSelHi_agree hr C D).left (cSelHi_dom hF hd C D) <|
    orElse_dom (cProjR_agree hr C D).left (cProjR_dom hF hd C D) <|
    orElse_dom (cSelLo_agree hr C D).left (cSelLo_dom hF hd C D) <|
    orElse_dom (cInst_agree hr C D).left (cInst_dom hF hd C D) <|
    orElse_dom (cVar_agree hr C D).left (cVar_dom hF hd C D) (cProjVar_dom hF hd C D)

end CapFrames

/-! ### The alternatives of the `kind` goal

`kNil`, `kProj` and `kCls` ask no goal.  Each is `Fu.ret` of an answer,
covered by `ret_agree` and `ret_dom` inside `kindStep`.  `kSel` asks no goal
either, but it reads the tank through `capksAt`. -/

section KindFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem kCons_agree (hr : ∀ q, Agree (r q) (r' q)) (φ : Cls.Kind) (C : CaptureSet s) :
    Agree (kCons r φ C) (kCons r' φ C) := by
  match C with
  | [] => exact ret_agree _
  | [_] => exact ret_agree _
  | _ :: _ :: _ => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)

theorem kCons_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (φ : Cls.Kind)
    (C : CaptureSet s) : Dom m (kCons r φ C) (kCons r' φ C) := by
  match C with
  | [] => exact ret_dom _ m
  | [_] => exact ret_dom _ m
  | _ :: _ :: _ =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)

/-- `kSel` asks no goal, so it is framed whatever the oracle. -/
theorem kSel_framed (φ : Cls.Kind) (C : CaptureSet s) : Framed (kSel (Γ := Γ) φ C) := by
  match C with
  | [] => exact ret_framed _
  | [.sel x A] =>
    exact bind_framed (capksAt_framed Γ x A) fun ds =>
      firstSome_framed (fun _ => ret_framed _) ds
  | [.var _] => exact ret_framed _
  | [.cvar _] => exact ret_framed _
  | [.any] => exact ret_framed _
  | [.fresh] => exact ret_framed _
  | [.proj _ _] => exact ret_framed _
  | a :: _ :: _ => cases a <;> exact ret_framed _

theorem kVar_agree (hr : ∀ q, Agree (r q) (r' q)) (φ : Cls.Kind) (C : CaptureSet s) :
    Agree (kVar r φ C) (kVar r' φ C) := by
  match C with
  | [] => exact ret_agree _
  | [a] =>
    dsimp only [kVar]
    split
    · exact mapO_agree _ (hr _)
    · split
      · exact mapO_agree _ (hr _)
      · exact ret_agree _
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem kVar_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (φ : Cls.Kind)
    (C : CaptureSet s) : Dom m (kVar r φ C) (kVar r' φ C) := by
  match C with
  | [] => exact ret_dom _ m
  | [a] =>
    dsimp only [kVar]
    split
    · exact mapO_dom _ (hF _) (hd _)
    · split
      · exact mapO_dom _ (hF _) (hd _)
      · exact ret_dom _ m
    · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem kSelUp_agree (hr : ∀ q, Agree (r q) (r' q)) (φ : Cls.Kind) (C : CaptureSet s) :
    Agree (kSelUp r φ C) (kSelUp r' φ C) := by
  match C with
  | [] => exact ret_agree _
  | [.sel x A] =>
    exact bind_agree (Agree.refl (capsAt_framed Γ x A)) fun ds =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | [.var _] => exact ret_agree _
  | [.cvar _] => exact ret_agree _
  | [.any] => exact ret_agree _
  | [.fresh] => exact ret_agree _
  | [.proj _ _] => exact ret_agree _
  | a :: _ :: _ => cases a <;> exact ret_agree _

theorem kSelUp_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (φ : Cls.Kind)
    (C : CaptureSet s) : Dom m (kSelUp r φ C) (kSelUp r' φ C) := by
  match C with
  | [] => exact ret_dom _ m
  | [.sel x A] =>
    exact bind_dom (capsAt_framed Γ x A)
      (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
      ((capsAt_framed Γ x A).dom m) fun ds =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | [.var _] => exact ret_dom _ m
  | [.cvar _] => exact ret_dom _ m
  | [.any] => exact ret_dom _ m
  | [.fresh] => exact ret_dom _ m
  | [.proj _ _] => exact ret_dom _ m
  | a :: _ :: _ => cases a <;> exact ret_dom _ m

theorem kProjS_agree (hr : ∀ q, Agree (r q) (r' q)) (φ : Cls.Kind) (C : CaptureSet s) :
    Agree (kProjS r φ C) (kProjS r' φ C) := by
  match C with
  | [] => exact ret_agree _
  | [a] =>
    dsimp only [kProjS]
    split
    · exact mapO_agree _ (hr _)
    · exact ret_agree _
  | _ :: _ :: _ => exact ret_agree _

theorem kProjS_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (φ : Cls.Kind)
    (C : CaptureSet s) : Dom m (kProjS r φ C) (kProjS r' φ C) := by
  match C with
  | [] => exact ret_dom _ m
  | [a] =>
    dsimp only [kProjS]
    split
    · exact mapO_dom _ (hF _) (hd _)
    · exact ret_dom _ m
  | _ :: _ :: _ => exact ret_dom _ m

theorem kindStep_agree (hr : ∀ q, Agree (r q) (r' q)) (C : CaptureSet s) (φ : Cls.Kind) :
    Agree (kindStep Γ r C φ) (kindStep Γ r' C φ) :=
  orElse_agree (ret_agree _) <| orElse_agree (kCons_agree hr φ C) <|
    orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    orElse_agree (Agree.refl (kSel_framed φ C)) <| orElse_agree (kVar_agree hr φ C) <|
    orElse_agree (kSelUp_agree hr φ C) (kProjS_agree hr φ C)

theorem kindStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C : CaptureSet s)
    (φ : Cls.Kind) : Dom m (kindStep Γ r C φ) (kindStep Γ r' C φ) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (kCons_agree hr φ C).left (kCons_dom hF hd φ C) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (kSel_framed φ C) ((kSel_framed φ C).dom m) <|
    orElse_dom (kVar_agree hr φ C).left (kVar_dom hF hd φ C) <|
    orElse_dom (kSelUp_agree hr φ C).left (kSelUp_dom hF hd φ C) (kProjS_dom hF hd φ C)

end KindFrames

/-! ### The alternatives of the `var` goal

Each alternative but `vWiden` reads the shape of one of the two types and
keeps its set, so its lemmas take the type apart. -/

section VarFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem vAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
    | _ => exact ret_agree _

theorem vAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | and T1 T2 =>
      exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ =>
        mapO_dom _ (hF _) (hd _)
    | _ => exact ret_dom _ m

theorem vMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | _ => exact ret_agree _

theorem vMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | _ => exact ret_dom _ m

theorem vSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | sel p A =>
      cases p with
      | var p =>
        exact bind_agree (Agree.refl (typsAt_framed Γ p A)) fun ds =>
          firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
    | _ => exact ret_agree _

theorem vSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | capt C T =>
    cases T with
    | sel p A =>
      cases p with
      | var p =>
        have hf : ∀ d : TMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
            else mapO (r (.var x V (d.1 ^ C))) fun f U e =>
              HasTy.sub (f U e) (ESub.ty (Sub.capt (SubShape.selLower d.2.2) Subcap.refl))
                Subcap.refl) :=
          fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
        exact bind_dom (typsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
          ((typsAt_framed Γ p A).dom m) fun ds =>
            firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
    | _ => exact ret_dom _ m

theorem vMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | _ => exact ret_agree _

theorem vMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | _ => exact ret_dom _ m

theorem vAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | and V1 V2 =>
      dsimp only [vAndL]
      refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
    | _ => exact ret_agree _

theorem vAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | and V1 V2 =>
      dsimp only [vAndL]
      refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
    | _ => exact ret_dom _ m

theorem vSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | sel p B =>
      cases p with
      | var q =>
        exact bind_agree (Agree.refl (typsAt_framed Γ q B)) fun ds =>
          firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
    | _ => exact ret_agree _

theorem vSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | capt C V =>
    cases V with
    | sel p B =>
      cases p with
      | var q =>
        exact bind_dom (typsAt_framed Γ q B)
          (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
          ((typsAt_framed Γ q B).dom m) fun ds =>
            firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
    | _ => exact ret_dom _ m

theorem vWiden_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vWiden r x V T) (vWiden r' x V T) :=
  mapO_agree _ (tySub_agree hr V T)

theorem vWiden_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vWiden r x V T) (vWiden r' x V T) :=
  mapO_dom _ (tySub_framed hF V T) (tySub_dom hF hd V T)

theorem varStep_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (varStep Γ r x V T) (varStep Γ r' x V T) :=
  orElse_agree (ret_agree _) <| ite_agree (vAndR_agree hr x V T) <|
    orElse_agree (vMuR_agree hr x V T) <| orElse_agree (vSelLo_agree hr x V T) <|
    orElse_agree (vMuL_agree hr x T V) <| orElse_agree (vAndL_agree hr x T V) <|
    orElse_agree (vSelHi_agree hr x T V) (vWiden_agree hr x V T)

theorem varStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (varStep Γ r x V T) (varStep Γ r' x V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <| ite_dom (vAndR_dom hF hd x V T) <|
    orElse_dom (vMuR_agree hr x V T).left (vMuR_dom hF hd x V T) <|
    orElse_dom (vSelLo_agree hr x V T).left (vSelLo_dom hF hd x V T) <|
    orElse_dom (vMuL_agree hr x T V).left (vMuL_dom hF hd x T V) <|
    orElse_dom (vAndL_agree hr x T V).left (vAndL_dom hF hd x T V) <|
    orElse_dom (vSelHi_agree hr x T V).left (vSelHi_dom hF hd x T V) (vWiden_dom hF hd x V T)

end VarFrames

/-! ### The alternatives of the `esub` goal

The lemmas of `ePack` take the hypotheses of the oracle for the residual of a
pack, `hI`, `hIF` and `hId`, at every witness.  The lemmas of `eExist` take
those of the oracle for the bodies, `hS`, `hSF` and `hSd`. -/

section ESubFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rS rS' : Rec Γ.scope} {rI rI' : RecInst Γ}
  {m : Nat}

theorem eTy_agree (hr : ∀ q, Agree (r q) (r' q)) (E F : ETy s) :
    Agree (eTy r E F) (eTy r' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_agree _
    | exact mapO_agree _ (tySub_agree hr _ _)

theorem eTy_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (E F : ETy s) :
    Dom m (eTy r E F) (eTy r' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_dom _ m
    | exact mapO_dom _ (tySub_framed hF _ _) (tySub_dom hF hd _ _)

theorem ePack_agree (hr : ∀ q, Agree (r q) (r' q)) (hI : ∀ W q, Agree (rI W q) (rI' W q))
    (E F : ETy s) : Agree (ePack r rI E F) (ePack r' rI' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_agree _
    | exact firstSome_agree (fun W => bindO_agree (hr _) fun _ =>
        mapO_agree _ (tySub_agree (hI W) _ _)) _

theorem ePack_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hIF : ∀ W q, Framed (rI W q)) (hId : ∀ W q, Dom m (rI W q) (rI' W q)) (E F : ETy s) :
    Dom m (ePack r rI E F) (ePack r' rI' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_dom _ m
    | exact firstSome_dom
        (fun W => bindO_framed (hF _) fun _ => mapO_framed _ (tySub_framed (hIF W) _ _))
        (fun W => bindO_dom (hF _) (fun _ => mapO_framed _ (tySub_framed (hIF W) _ _)) (hd _)
          fun _ => mapO_dom _ (tySub_framed (hIF W) _ _) (tySub_dom (hIF W) (hId W) _ _)) _

theorem eExist_agree (hr : ∀ q, Agree (r q) (r' q)) (hS : ∀ q, Agree (rS q) (rS' q))
    (E F : ETy s) : Agree (eExist r rS E F) (eExist r' rS' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_agree _
    | exact bindO_agree (hr _) fun _ => mapO_agree _ (tySub_agree hS _ _)

theorem eExist_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hSF : ∀ q, Framed (rS q)) (hSd : ∀ q, Dom m (rS q) (rS' q)) (E F : ETy s) :
    Dom m (eExist r rS E F) (eExist r' rS' E F) := by
  cases E <;> cases F
  all_goals first
    | exact ret_dom _ m
    | exact bindO_dom (hF _) (fun _ => mapO_framed _ (tySub_framed hSF _ _)) (hd _) fun _ =>
        mapO_dom _ (tySub_framed hSF _ _) (tySub_dom hSF hSd _ _)

theorem esubStep_agree (hr : ∀ q, Agree (r q) (r' q)) (hS : ∀ q, Agree (rS q) (rS' q))
    (hI : ∀ W q, Agree (rI W q) (rI' W q)) (E F : ETy s) :
    Agree (esubStep Γ r rS rI E F) (esubStep Γ r' rS' rI' E F) :=
  orElse_agree (eTy_agree hr E F) <| orElse_agree (ePack_agree hr hI E F) (eExist_agree hr hS E F)

theorem esubStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hSF : ∀ q, Framed (rS q)) (hSd : ∀ q, Dom m (rS q) (rS' q))
    (hIF : ∀ W q, Framed (rI W q)) (hId : ∀ W q, Dom m (rI W q) (rI' W q)) (E F : ETy s) :
    Dom m (esubStep Γ r rS rI E F) (esubStep Γ r' rS' rI' E F) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hI : ∀ W q, Agree (rI W q) (rI W q) := fun _ _ => Agree.refl (hIF _ _)
  orElse_dom (eTy_agree hr E F).left (eTy_dom hF hd E F) <|
    orElse_dom (ePack_agree hr hI E F).left (ePack_dom hF hd hIF hId E F)
      (eExist_dom hF hd hSF hSd E F)

end ESubFrames

/-! ### The step -/

theorem step_frame : FrameF step := by
  intro o o' ho g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | shp S T =>
    exact shpStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rS := fun q => o ⟨_, Γ.scope, q⟩) (rS' := fun q => o' ⟨_, Γ.scope, q⟩)
      (rB := fun T2 q => o ⟨_, Γ.body T2, q⟩) (rB' := fun T2 q => o' ⟨_, Γ.body T2, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun q => ho ⟨_, Γ.scope, q⟩) (fun T2 q => ho ⟨_, Γ.body T2, q⟩) S T
  | cap C D =>
    exact capStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) C D
  | kind C φ =>
    exact kindStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) C φ
  | var x V T =>
    exact varStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) x V T
  | esub E F =>
    exact esubStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rS := fun q => o ⟨_, Γ.scope, q⟩) (rS' := fun q => o' ⟨_, Γ.scope, q⟩)
      (rI := fun W q => o ⟨_, Γ.scopeInst W, q⟩) (rI' := fun W q => o' ⟨_, Γ.scopeInst W, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun q => ho ⟨_, Γ.scope, q⟩)
      (fun W q => ho ⟨_, Γ.scopeInst W, q⟩) E F

theorem step_dom : DomF step := by
  intro m o o' hF _ hd g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | shp S T =>
    exact shpStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rS := fun q => o ⟨_, Γ.scope, q⟩) (rS' := fun q => o' ⟨_, Γ.scope, q⟩)
      (rB := fun T2 q => o ⟨_, Γ.body T2, q⟩) (rB' := fun T2 q => o' ⟨_, Γ.body T2, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun q => hF ⟨_, Γ.scope, q⟩) (fun q => hd ⟨_, Γ.scope, q⟩)
      (fun T2 q => hF ⟨_, Γ.body T2, q⟩) (fun T2 q => hd ⟨_, Γ.body T2, q⟩) S T
  | cap C D =>
    exact capStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) C D
  | kind C φ =>
    exact kindStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) C φ
  | var x V T =>
    exact varStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) x V T
  | esub E F =>
    exact esubStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rS := fun q => o ⟨_, Γ.scope, q⟩) (rS' := fun q => o' ⟨_, Γ.scope, q⟩)
      (rI := fun W q => o ⟨_, Γ.scopeInst W, q⟩) (rI' := fun W q => o' ⟨_, Γ.scopeInst W, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun q => hF ⟨_, Γ.scope, q⟩) (fun q => hd ⟨_, Γ.scope, q⟩)
      (fun W q => hF ⟨_, Γ.scopeInst W, q⟩) (fun W q => hd ⟨_, Γ.scopeInst W, q⟩) E F

/-! ## The entry points keep an answer with more fuel

A run whose index is the fuel left is framed, as `typsAt` is.  A run that
ends unmarked never reached index zero, so it does the same at any larger
index.  An answer of the run leaves the tank unmarked.  `subF` joins two runs
by `bindO` and `mapO`, and `varFrom` maps the answer of one run, which keeps
both facts.  So the entry points keep an answer at any larger fuel. -/

section RunLeft

variable {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat} {F : Step G R}

/-- An answer of the run leaves the tank unmarked. -/
theorem run_some {d : Nat} {P : List G} {g : G} {t : Tank} {x : R g}
    (h : (run cost F d P g t).1 = some x) : (run cost F d P g t).2.out = false := by
  cases d with
  | zero => simp [run] at h
  | succ d =>
    rw [run_succ] at h ⊢
    exact node_some (k := F (run cost F d (g :: P)) g) (Prod.ext h rfl)

/-- The run at the index of the fuel left is framed. -/
theorem runLeft_framed (hF : FrameF F) (P : List G) (g : G) :
    Framed (fun t => run cost F t.left P g t) where
  absorbs t ht := (run_framed hF t.left P g).absorbs t ht
  spends t := (run_framed hF t.left P g).spends t
  shift := by
    intro t r t' h ho k
    have h1 := run_frame hF h ho k
    have h2 : (run cost F t.left P g (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change run cost F (t.left + k) P g (t.add k) = _
    rw [run_index hF h2 (Nat.le_add_right _ _), h1]

end RunLeft

/-- A computation whose every answer leaves the tank unmarked. -/
def SomeUnmarked {α : Type} (c : Fu (Option α)) : Prop :=
  ∀ t x, (c t).1 = some x → (c t).2.out = false

section Unmarked

variable {α β : Type}

/-- An answer of the run leaves the tank unmarked. -/
theorem runLeft_someUnmarked {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat}
    {F : Step G R} (P : List G) (g : G) : SomeUnmarked (fun t => run cost F t.left P g t) :=
  fun _ _ h => run_some h

/-- Mapping an answer keeps its tank. -/
theorem mapO_someUnmarked {c : Fu (Option α)} (f : α → β) (hc : SomeUnmarked c) :
    SomeUnmarked (mapO c f) := by
  intro t x h
  simp only [mapO, Fu.bind, Fu.ret] at h ⊢
  cases hct : c t with
  | mk o t1 =>
    rw [hct] at h
    cases o with
    | none => simp at h
    | some a =>
      have := hc t a (by rw [hct])
      rw [hct] at this
      exact this

/-- An answer of `bindO` is an answer of its continuation. -/
theorem bindO_someUnmarked {c : Fu (Option α)} {f : α → Fu (Option β)}
    (hf : ∀ a, SomeUnmarked (f a)) : SomeUnmarked (bindO c f) := by
  intro t x h
  simp only [bindO, Fu.bind] at h ⊢
  cases hct : c t with
  | mk o t1 =>
    rw [hct] at h
    cases o with
    | none => simp [Fu.ret] at h
    | some a => exact hf a t1 x h

/-- A framed computation whose answers leave the tank unmarked keeps an
answer from a full tank at any larger full tank. -/
theorem full_mono {c : Fu (Option α)} (hc : Framed c) (hu : SomeUnmarked c) {n m : Nat} {e : α}
    (h : (c ⟨n, false⟩).1 = some e) (hnm : n ≤ m) : (c ⟨m, false⟩).1 = some e := by
  have ho := hu _ _ h
  have := hc.shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  have hadd : (⟨n, false⟩ : Tank).add (m - n) = ⟨m, false⟩ := by
    simp only [Tank.add, Tank.mk.injEq, and_true]
    omega
  rw [hadd] at this
  rw [this]

/-- A framed computation that ends unmarked from a full tank gives the same
answer, a rejection included, from any larger full tank. -/
theorem full_stable {c : Fu α} (hc : Framed c) {n k : Nat} {r : α}
    (h : c ⟨n, false⟩ = (r, ⟨k, false⟩)) (m : Nat) : (c ⟨n + m, false⟩).1 = r :=
  congrArg Prod.fst (hc.shift ⟨n, false⟩ r _ h rfl m)

end Unmarked

theorem shpF_framed {s : Sig} (Γ : Ctx s) (S T : Shape s) : Framed (shpF Γ S T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .shp S T⟩

theorem capF_framed {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Framed (capF Γ C D) :=
  runLeft_framed step_frame [] ⟨s, Γ, .cap C D⟩

theorem kindF_framed {s : Sig} (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) :
    Framed (kindF Γ C φ) :=
  runLeft_framed step_frame [] ⟨s, Γ, .kind C φ⟩

theorem varTyF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Ty s) :
    Framed (varTyF Γ x V T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .var x V T⟩

theorem esubF_framed {s : Sig} (Γ : Ctx s) (E F : ETy s) : Framed (esubF Γ E F) :=
  runLeft_framed step_frame [] ⟨s, Γ, .esub E F⟩

theorem subF_framed {s : Sig} (Γ : Ctx s) (T U : Ty s) : Framed (subF Γ T U) := by
  cases T
  cases U
  exact bindO_framed (capF_framed _ _ _) fun _ => mapO_framed _ (shpF_framed _ _ _)

theorem varFrom_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s) (V : Ty s)
    (d : HasTy U Γ (.path (.var x)) (.ty V)) (T : Ty s) : Framed (varFrom Γ x U V d T) :=
  mapO_framed _ (varTyF_framed _ _ _ _)

theorem varF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Framed (varF Γ x T) :=
  varFrom_framed _ _ _ _ _ _

theorem subF_someUnmarked {s : Sig} (Γ : Ctx s) (T U : Ty s) : SomeUnmarked (subF Γ T U) := by
  cases T
  cases U
  exact bindO_someUnmarked fun _ => mapO_someUnmarked _ (runLeft_someUnmarked _ _)

theorem varFrom_someUnmarked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s)
    (V : Ty s) (d : HasTy U Γ (.path (.var x)) (.ty V)) (T : Ty s) :
    SomeUnmarked (varFrom Γ x U V d T) :=
  mapO_someUnmarked _ (runLeft_someUnmarked _ _)

theorem varF_someUnmarked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    SomeUnmarked (varF Γ x T) :=
  varFrom_someUnmarked _ _ _ _ _ _

theorem shp?_mono {s : Sig} {Γ : Ctx s} {S T : Shape s} {n m : Nat} {e : SubShape Γ S T}
    (h : (shp? Γ S T n).1 = some e) (hnm : n ≤ m) : (shp? Γ S T m).1 = some e :=
  full_mono (shpF_framed Γ S T) (runLeft_someUnmarked _ _) h hnm

theorem cap?_mono {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {n m : Nat} {e : Subcap Γ C D}
    (h : (cap? Γ C D n).1 = some e) (hnm : n ≤ m) : (cap? Γ C D m).1 = some e :=
  full_mono (capF_framed Γ C D) (runLeft_someUnmarked _ _) h hnm

theorem kind?_mono {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} {n m : Nat}
    {e : CapKind Γ C φ} (h : (kind? Γ C φ n).1 = some e) (hnm : n ≤ m) :
    (kind? Γ C φ m).1 = some e :=
  full_mono (kindF_framed Γ C φ) (runLeft_someUnmarked _ _) h hnm

/-- A kinding that ends with the tank unmarked, an answer or a rejection,
is the same at every larger fuel.  The verdict of a kinding goal does not
depend on the fuel once the fuel suffices. -/
theorem kind?_stable {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} {n k : Nat}
    {r : Option (CapKind Γ C φ)} (h : kind? Γ C φ n = (r, ⟨k, false⟩)) (m : Nat) :
    (kind? Γ C φ (n + m)).1 = r :=
  full_stable (kindF_framed Γ C φ) h m

theorem esub?_mono {s : Sig} {Γ : Ctx s} {E F : ETy s} {n m : Nat} {e : ESub Γ E F}
    (h : (esub? Γ E F n).1 = some e) (hnm : n ≤ m) : (esub? Γ E F m).1 = some e :=
  full_mono (esubF_framed Γ E F) (runLeft_someUnmarked _ _) h hnm

theorem sub?_mono {s : Sig} {Γ : Ctx s} {T U : Ty s} {n m : Nat} {e : Sub Γ T U}
    (h : (sub? Γ T U n).1 = some e) (hnm : n ≤ m) : (sub? Γ T U m).1 = some e :=
  full_mono (subF_framed Γ T U) (subF_someUnmarked Γ T U) h hnm

theorem var?_mono {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n m : Nat}
    {e : (U : CaptureSet s) × HasTy U Γ (.path (.var x)) (.ty T)}
    (h : (var? Γ x T n).1 = some e) (hnm : n ≤ m) : (var? Γ x T m).1 = some e :=
  full_mono (varF_framed Γ x T) (varF_someUnmarked Γ x T) h hnm

/-! ## Reading a run

`answers` and `rejects` read the result of a run from a full tank.  Each
says whether the run answered, that it ended with the tank unmarked, and how
many units it used.  So one kernel check evaluates the run once.  A run that
ends unmarked uses the same units at every larger fuel. -/

/-- The run from a full tank of `n` units answered, ended unmarked and used
`k` units. -/
def answers {α : Type} (r : Option α × Tank) (k : Nat) (n : Nat := defaultFuel) : Bool :=
  match r with
  | (some _, t) => !t.out && n - t.left == k
  | (none, _) => false

/-- The run from a full tank of `n` units gave no answer, ended unmarked and
used `k` units. -/
def rejects {α : Type} (r : Option α × Tank) (k : Nat) (n : Nat := defaultFuel) : Bool :=
  match r with
  | (none, t) => !t.out && n - t.left == k
  | (some _, _) => false

/-- An answer read off a run is a run that answers with the tank unmarked. -/
theorem answers_isSome {α : Type} {r : Option α × Tank} {k n : Nat} (h : answers r k n = true) :
    r.1.isSome = true ∧ r.2.out = false := by
  obtain ⟨o, t⟩ := r
  cases o with
  | none => simp [answers] at h
  | some _ =>
    simp only [answers, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨rfl, h.1⟩

/-- A rejection read off a run is a run that ends with no answer and the tank
unmarked. -/
theorem rejects_eq {α : Type} {r : Option α × Tank} {k n : Nat} (h : rejects r k n = true) :
    r = (none, ⟨r.2.left, false⟩) := by
  obtain ⟨o, t⟩ := r
  cases o with
  | some _ => simp [rejects] at h
  | none =>
    simp only [rejects, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨left, out⟩ := t
    simp only at h
    rw [h.1]

/-! ## Checks

Each check runs in the kernel at the default fuel. -/

section SubChecks

open Classifiers.DotMNF.Examples

/-- `μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥..{a : ⊤}}))`. -/
def P1M {s : Sig} : Shape s :=
  .mu (.and (.fld lb (.top ^ [])) (.and (.fld lv (.top ^ [])) (.typ lA .bot (.fld la (.top ^ [])))))

/-- `∀(y : P1M) y.A`. -/
def P1S : Shape ([] : Sig) := .all (P1M ^ []) (.ty ((Shape.sel (.var .here) lA) ^ []))

/-- `∀(y : P1M) {a : ⊤}`. -/
def P1T : Shape ([] : Sig) := .all (P1M ^ []) (.ty ((Shape.fld la (.top ^ [])) ^ []))

/-- C2's literal `x` at its precise type, on the platform. -/
def C2LitCtx : Ctx ([],c,c,x) := platCtx.cons (C2PreTy k1)

/-- E1 with the middle written: `t : ⊤` in the body of E1's lambda. -/
def E1sCtx1 : Ctx (Sig.body ([] : Sig),x) := E1Ctx.cons (.top ^ [])

/-- E1 with the middle written: then `u : x.A`. -/
def E1sCtx2 : Ctx (Sig.body ([] : Sig),x,x) :=
  E1sCtx1.cons ((Shape.sel (.var (.there .here)) lA) ^ [])

/-- `z : μ(z. {C : {}..{z.C}})` on the platform: a capture member bounded by
itself. -/
def CycCtx : Ctx ([],c,c,x) := platCtx.cons ((Shape.mu (.cap lC [] [CapAtom.sel .here lC])) ^ [])

/-- `n` variables. -/
def chainBase : Nat → Sig
  | 0 => []
  | n + 1 => Sig.extend (chainBase n) .var

/-- The signature of a chain of `n` links: `n + 1` variables. -/
def chainSig (n : Nat) : Sig := Sig.extend (chainBase n) .var

/-- An alias chain: `x0 : {A : ⊥..⊤}` and `xk : {A : x(k-1).A..x(k-1).A}` for
`k = 1..n`. -/
def chainCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])
  | n + 1 => (chainCtx n).cons ((Shape.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA)) ^ [])

/-- The chain with every link doubled: two equal members per link. -/
def dchainCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])
  | n + 1 => (dchainCtx n).cons ((Shape.and (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA))
      (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA))) ^ [])

/-- The first variable of a chain, `x0`. -/
def chainFirst : (n : Nat) → BVar (chainSig n) .var
  | 0 => .here
  | n + 1 => .there (chainFirst n)

/-- `xn.A`, the last link. -/
def chainTop (n : Nat) : Shape (chainSig n) := .sel (.var .here) lA

/-- `x0.A`, the first link. -/
def chainBot (n : Nat) : Shape (chainSig n) := .sel (.var (chainFirst n)) lA

/-- `q : {A : ⊥..⊤}`, `x : q.A ^ {}`: a variable at its own abstract shape,
declared at the empty set. -/
def XCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `q.A ^ {}`, seen from `XCtx`. -/
def XT : Ty ([],x,x) := (Shape.sel (.var (.there .here)) lA) ^ []

/-- `q : {A : ⊥..⊤}`, `x : q.A ^ {κ₁}`, on the platform: a variable at its
own abstract shape, declared at a set that is not empty. -/
def XkCtx : Ctx ([],c,c,x,x) :=
  (platCtx.cons ((Shape.typ lA .bot .top) ^ [])).cons
    ((Shape.sel (.var .here) lA) ^ [CapAtom.cvar (.there k1)])

/-- `q.A ^ {κ₁}`, seen from `XkCtx`. -/
def XkT : Ty ([],c,c,x,x) :=
  (Shape.sel (.var (.there .here)) lA) ^ [CapAtom.cvar (.there (.there k1))]

/-- `q : {A : ⊥..⊤}`, `p : {A : ⊥..q.A}`, `x : p.A ^ {}`. -/
def X2Ctx : Ctx ([],x,x,x) :=
  ((Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])).cons
    ((Shape.typ lA .bot (.sel (.var .here) lA)) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `q.A ^ {}`, seen from `X2Ctx`. -/
def X2T : Ty ([],x,x,x) := (Shape.sel (.var (.there (.there .here))) lA) ^ []

/-- `only[Control]`. -/
def ctlK : Cls.Kind := Cls.only Cls.Control

/-- `ctl : Control`, `io : IO`, `f : (Unit → Unit) ^ {ctl, io}`. -/
def WCtx1 : Ctx ([],c,c,x) := E1PlatCtx.cons (arrowS ^ [CapAtom.cvar E1ctl, CapAtom.cvar E1io])

/-- `{f ↾ only[Control]}`. -/
def WL : CaptureSet ([],c,c,x) := CaptureSet.proj [CapAtom.var .here] ctlK

/-- `{ctl ↾ only[Control], io ↾ only[Control]}`, `f`'s declared set restricted. -/
def WR : CaptureSet ([],c,c,x) := CaptureSet.proj (WCtx1.lookup .here).captureSet ctlK

/-- Then `g : (Unit → Unit) ^ {f ↾ only[Control]}`. -/
def WCtx2 : Ctx ([],c,c,x,x) := WCtx1.cons (arrowS ^ WL)

/-- `(Unit → Unit) ^ {ctl ↾ only[Control], io ↾ only[Control]}`, seen from
`WCtx2`. -/
def WT2 : Ty ([],c,c,x,x) :=
  arrowS ^ CaptureSet.proj (WCtx2.lookup (.there .here)).captureSet ctlK

/-- CE5's platform with an argument `y` at the thread-local capability. -/
def E2TlCtx : Ctx ([],c,c,c,x) := E2PlatIOCtx.cons (arrowS ^ [CapAtom.cvar E2tl])

/-- `p : μ(s. {A : ⊥..∀(y : ⊤) s.A})`, `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`,
`x : p.A`.  `x : q.B` has no finite derivation.  Each level reaches the goal
again under a new binder. -/
def LPCtx : Ctx ([],x,x,x) :=
  ((Ctx.nil.cons ((Shape.mu (.typ lA .bot
        (.all (.top ^ []) (.ty ((Shape.sel (.var (.there (.there .here))) lA) ^ []))))) ^ [])).cons
    ((Shape.mu (.typ lB
        (.all (.top ^ []) (.ty ((Shape.sel (.var (.there (.there .here))) lB) ^ [])))
        .top)) ^ [])).cons
    ((Shape.sel (.var (.there .here)) lA) ^ [])

/-- The label `T` of LQ2. -/
def lYT : Label := .typ 10

/-- The label `B` of LQ2. -/
def lYB : Label := .typ 11

/-- The label `D` of LQ2. -/
def lYD : Label := .typ 12

/-- `∀(z : r.T) z.L` inside the body of `μ r`. -/
def freshArrow {s : Sig} (L : Label) : Shape (s,x) :=
  .all (Ty.capt [] (.sel (.var (.there .here)) lYT)) (.ty (Ty.capt [] (.sel (.var .here) L)))

/-- `M(r) = {B : ⊥..∀(z : r.T) z.B} ∧ {D : ∀(w : r.T) w.D..⊤}`. -/
def MBD {s : Sig} : Shape (s,x) :=
  .and (.typ lYB .bot (freshArrow lYB)) (.typ lYD (freshArrow lYD) .top)

/-- `μ(r. {T : ⊥..s.T} ∧ M(r))`'s body, under the outer self `s`. -/
def innerBody {s : Sig} : Shape ((s,x),x) :=
  .and (.typ lYT .bot (.sel (.var (.there .here)) lYT)) MBD

/-- `{T : ⊥..μ(r. {T : ⊥..s.T} ∧ M(r))} ∧ M(s)`. -/
def outerBody {s : Sig} : Shape (s,x) := .and (.typ lYT .bot (.mu innerBody)) MBD

/-- LQ2: `y : μ(s. {T : ⊥..μ(r. {T : ⊥..s.T} ∧ M(r))} ∧ M(s))`.  The goal
`y.B <: y.D` compares two arrows whose codomain goal mentions the fresh
parameter, at every level. -/
def LQ2Ctx : Ctx ([],x) := Ctx.nil.cons ((Shape.mu outerBody) ^ [])

-- E6: `Int <: z.T` at the self binder's own member, as a shape and at the
-- outer variable.
example : answers (shp? E6Ctxz E6IntS (.sel (.var .here) lT)) 12 = true := by decide +kernel
example : answers (var? E6Ctxz (up2 .here) ((Shape.sel (.var .here) lT) ^ [])) 12 = true := by
  decide +kernel

-- E8: `x.A <: {a : ⊤}` through the upper bound, and the field of
-- `y : x.A ∧ {a : ⊤}`.
example : answers (shp? E8Ctx2 (.sel (.var (up .here)) lA) (.fld la (.top ^ []))) 4 = true := by
  decide +kernel
example : answers (var? E8Ctx2 .here ((Shape.fld la (.top ^ [])) ^ [CapAtom.var .here])) 15
    = true := by decide +kernel
-- The converse of E8 fails: the lower bound of `x.A` is `⊥`.
example : rejects (shp? E8Ctx2 (.fld la (.top ^ [])) (.sel (.var (up .here)) lA)) 2 = true := by
  decide +kernel

-- CE4: the closure's set at `only[Control]`, by `ksel` at the member read on
-- demand, and the call's goal `{g} <: {g ↾ only[Control]}` by `proj`.
example : answers (kind? E3ClientCtx E3ClosureSet (Cls.only Cls.Control)) 10 = true := by
  decide +kernel
example : answers (cap? E3ClientCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.Control))) 21 = true := by decide +kernel
-- The same at the unrelated classifier `IO` is refused.
example : rejects (kind? E3ClientCtx E3ClosureSet (Cls.only Cls.IO)) 19 = true := by
  decide +kernel
example : rejects (cap? E3ClientCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.IO))) 60 = true := by decide +kernel

-- CE2: `{y} <: {y ↾ except[ThreadLocal]}` at an input-output argument.
example : answers (cap? E2IoCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))) 8 = true := by
  decide +kernel
-- CE5: the thread-local argument is refused.
example : rejects (cap? E2TlCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))) 15 = true := by
  decide +kernel

-- CE3: the literal retyped at the abstract type whose capture member is
-- bounded by a kind: `Rec-E`, `Rec-I`, `capkI` and the declared classifiers.
example : answers (var? E3CtxB (.there .here)
    (E3AbsTy (.there (.there (.there (.there .here)))) (.there (.there (.there .here))))) 75
    = true := by decide +kernel

-- E1s, the middle written: `t : ⊤` at `x.A` by the lower bound, then
-- `u : x.A` at E1's result.
example : answers (var? E1sCtx1 .here ((Shape.sel (.var (.there .here)) lA) ^ [])) 4 = true := by
  decide +kernel
example : answers (var? E1sCtx2 .here E1Res) 10 = true := by decide +kernel

-- E3s: `{b : ⊤} <: x.A` through the second member's lower bound, and
-- `x.A <: {a : ⊤}` through the first member's upper bound.
example : answers (shp? E3Ctx2 E3T2S (.sel (.var (up .here)) lA)) 8 = true := by
  decide +kernel
example : answers (shp? E3Ctx2 (.sel (.var (up .here)) lA) E3T1S) 8 = true := by
  decide +kernel

-- M1: a mixed set on the left, `{b ↾ only[Control], f}` below the filtered
-- platform set.
example : answers (cap? E1Ctx2
    [CapAtom.proj (.var (.there .here)) (Cls.only Cls.Control), CapAtom.var .here]
    (CaptureSet.weaken (CaptureSet.weaken E1Filt))) 172 = true := by decide +kernel
-- M2: a mixed set on the right, `{y} <: {κ_ctl, y ↾ except[ThreadLocal]}`.
example : answers (cap? E2IoCtx [CapAtom.var .here]
    [CapAtom.cvar (.there (.there .here)),
      CapAtom.proj (.var .here) (Cls.except Cls.ThreadLocal)]) 8 = true := by decide +kernel
-- M5: `{κ_ctl}` below the filtered platform set.
example : answers (cap? E1PlatCtx [CapAtom.cvar E1ctl] E1Filt) 5 = true := by decide +kernel
-- R2: a selection off a member bounded by sets, kinded through its upper
-- bound.
example : answers (kind? (C2CtxG E3PlatCtx E3k1 E3k2) [CapAtom.sel (.there (up .here)) lC]
    (Cls.only Cls.Control)) 27 = true := by decide +kernel

-- C2: `{g} <: {κ₁, κ₂}`, the declared set of `g`, then the upper bound of a
-- capture member, found on demand.
example : answers (cap? (C2CtxG platCtx k1 k2) [CapAtom.var .here]
    [CapAtom.cvar (.there (up (up k1))), CapAtom.cvar (.there (up (up k2)))]) 15 = true := by
  decide +kernel
-- The upper bound is `{κ₁, κ₂}`, so `{g}` is not below `{κ₁}`.
example : rejects (cap? (C2CtxG platCtx k1 k2) [CapAtom.var .here]
    [CapAtom.cvar (.there (up (up k1)))]) 23 = true := by decide +kernel

-- S1: `{fs} <: {cp.C}` through the lower bound of `cp`'s capture member.
example : answers (cap? S1Ctx2 [CapAtom.cvar fs2] [CapAtom.sel .here lC]) 6 = true := by
  decide +kernel

-- C5: `{n} <: {fs}`, the declared set `{it.C}`, then the member's upper bound.
example : answers (cap? S2Ctx4 [CapAtom.var .here] [CapAtom.cvar fs4]) 15 = true := by
  decide +kernel

-- C2's literal at its precise type, retyped at the abstract type: `Rec-E`,
-- the capture member, `Rec-I` and the declared set.
example : answers (var? C2LitCtx .here (C2AbsTy (.there k1) (.there k2))) 82 = true := by
  decide +kernel

-- P1: a type member three levels down a recursive binder, under a `∀`.
example : answers (shp? .nil P1S P1T) 34 = true := by decide +kernel
-- The converse fails: `{a : ⊤}` is not below `y.A`, whose lower bound is `⊥`.
example : rejects (shp? .nil P1T P1S) 30 = true := by decide +kernel

-- E7: the alias cycle ends.  `x.A` has no field, and `x.A <: x.B` holds.
example : rejects (shp? E7Ctx (.sel (.var .here) lA) (.fld la (.top ^ []))) 24 = true := by
  decide +kernel
example : answers (shp? E7Ctx (.sel (.var .here) lA) (.sel (.var .here) lB)) 12 = true := by
  decide +kernel

-- A capture member bounded by itself: the goal repeats and fails, as a set
-- goal and as a kinding goal.
example : rejects (cap? CycCtx [CapAtom.sel .here lC] [CapAtom.cvar (.there k1)]) 6 = true := by
  decide +kernel
example : rejects (kind? CycCtx [CapAtom.sel .here lC] ctlK) 9 = true := by decide +kernel

-- W5: `f` below the root of its own scope, by its level, and not below the
-- outer one.
example : answers (cap? W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kb]) 1 = true := by
  decide +kernel
example : rejects (cap? W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout]) 3 = true := by
  decide +kernel

-- W1: the outer root is below the inner one, not the other way.  Both
-- parameters are below the inner root.
example : answers (cap? W1Ctx2 [CapAtom.cvar W1outRoot] [CapAtom.cvar W1inRoot]) 1 = true := by
  decide +kernel
example : rejects (cap? W1Ctx2 [CapAtom.cvar W1inRoot] [CapAtom.cvar W1outRoot]) 1 = true := by
  decide +kernel
example : answers (cap? W1Ctx2 [CapAtom.var W1outParam] [CapAtom.cvar W1inRoot]) 1 = true := by
  decide +kernel
example : answers (cap? W1Ctx2 [CapAtom.var W1inParam] [CapAtom.cvar W1inRoot]) 1 = true := by
  decide +kernel

-- The binders two unpacked calls open are unrelated, in both directions.
example : rejects (cap? Z1BodyCtxSrc [CapAtom.cvar Zk1'] [CapAtom.cvar Zk2']) 1 = true := by
  decide +kernel
example : rejects (cap? Z1BodyCtxSrc [CapAtom.cvar Zk2'] [CapAtom.cvar Zk1']) 1 = true := by
  decide +kernel

-- Z1: the body's answer packs, the witness its own set, the residual by the
-- instance rule.  The arrow rule opens its scopes and compares the answers as
-- two existentials.
example : answers (esub? (platCtx.body unitTy) (.ty (fileS ^ [CapAtom.var .here]))
    (∃ᶜ[[CapAtom.cvar (up k1), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))) 10 = true := by
  decide +kernel
example : answers (sub? platCtx (Z1Ty k1) (Z1TyTop k1)) 17 = true := by decide +kernel
-- An existential is below no plain answer.
example : rejects (esub? platCtx (∃ᶜ[[CapAtom.cvar k1]] (Shape.top ^ [CapAtom.cvar .here]))
    (.ty (Shape.top ^ []))) 1 = true := by decide +kernel

-- Alias chains of 16 and 32 links, and a doubled chain of 6.
example : answers (shp? (chainCtx 16) (chainTop 16) (chainBot 16)) 185 = true := by
  decide +kernel
example : answers (shp? (chainCtx 32) (chainTop 32) (chainBot 32)) 625 = true := by
  decide +kernel
example : answers (shp? (dchainCtx 6) (chainTop 6) (chainBot 6)) 64 = true := by
  decide +kernel

-- A variable at its own abstract shape.  Declared at `{}`, its view is its
-- declared type, and identity holds.  From the view at `{x}`, and for a
-- variable declared at `{κ₁}`, the view is widened whole, the selection
-- included: `{x}` goes to its declared set, and `q.A <: q.A` by identity.
example : answers (var? XCtx .here XT) 1 = true := by decide +kernel
example : answers (varTyF XCtx .here ((Shape.sel (.var (.there .here)) lA) ^ [CapAtom.var .here])
    XT ⟨defaultFuel, false⟩) 24 = true := by decide +kernel
example : answers (var? XkCtx .here XkT) 24 = true := by decide +kernel
-- The same through an upper bound: `x : p.A ^ {}` at `q.A ^ {}`.
example : answers (var? X2Ctx .here X2T) 5 = true := by decide +kernel

-- W: `{f ↾ only[Control]}` below `f`'s declared set restricted, by
-- `projMono` of `f`'s declared set, and the same at a variable whose set is
-- `{f ↾ only[Control]}`.  `io` is not of kind `only[Control]`, so no route
-- through the atoms of the right set holds.
example : answers (cap? WCtx1 WL WR) 174 = true := by decide +kernel
example : answers (var? WCtx2 .here WT2) 391 = true := by decide +kernel
example : rejects (kind? WCtx1 [CapAtom.cvar (.there E1io)] ctlK) 1 = true := by decide +kernel

-- B1: `n : {a : ⊤}` is not shown at `{b : ⊤}`.  No lookup widens through
-- `x.A`'s lower bound.
example : rejects (var? B1Ctx .here ((Shape.fld lb (.top ^ [])) ^ [CapAtom.var .here])) 5
    = true := by decide +kernel

-- E1, E3 and E4 as written are rejected with the tank unmarked, as scalac
-- rejects them.
example : rejects (sub? E1Ctx E1Dom E1Res) 2 = true := by decide +kernel
example : rejects (var? E1Ctx .here E1Res) 5 = true := by decide +kernel
example : rejects (shp? E3Ctx2 E3T2S E3T1S) 1 = true := by decide +kernel
example : rejects (sub? E3Ctx2 E3T2 E3T1) 2 = true := by decide +kernel
example : rejects (sub? E4Ctx4 E4Int ((Shape.sel (.var (.there (up .here))) lA) ^ [])) 3
    = true := by decide +kernel
example : rejects (var? E4Ctx4 (.there .here) ((Shape.sel (.var (.there (up .here))) lA) ^ [])) 7
    = true := by decide +kernel

-- The loops LP and LQ2 exhaust the tank: the recursion limit.
example : (var? LPCtx .here ((Shape.sel (.var (.there .here)) lB) ^ [])).2.out = true := by
  decide +kernel
example : (shp? LPCtx (.sel (.var (.there (.there .here))) lA)
    (.sel (.var (.there .here)) lB)).2.out = true := by decide +kernel
example : (shp? LQ2Ctx (.sel (.var .here) lYB) (.sel (.var .here) lYD)).2.out = true := by
  decide +kernel

end SubChecks

end ClassifiersFrontend.Core
