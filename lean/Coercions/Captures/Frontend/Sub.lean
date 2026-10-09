import Coercions.Captures.Frontend.Look
import Coercions.Captures.Frontend.Search

/-!
# Subtyping and subcapturing in the compiler's case order

The algorithm decides three goals.

- `shape S T` asks for `S <: T` on shapes.  The answer is a `SubShape`
  derivation.
- `cap C D` asks for `C <: D` on capture sets.  The answer is a `Subcap`
  derivation.
- `var x V T` asks that the variable `x`, already seen at the shape `V`, have
  the shape `T`.  The answer is a map from the variable at `V` to the variable
  at `T`, at every use set and capture set.

The `var` goal is the compiler's singleton on the left.  It keeps `x` while it
widens, so a recursive shape is opened at `x` (`TypeComparer.thirdTry` for
`RecType`, `TypeComparer.fixRecs`).  The rules `Rec-I`, `Rec-E`, `And-I` and
`sub` with `Subcap.refl` keep both sets, so the walk over the shape never
touches them.

A type is a shape with a capture set, and `Sub` has the one rule `capt`.  Two
types compare by a set goal and a shape goal, the set goal first, as the
compiler compares a capturing type in `secondTry` and `thirdTry`.

## Order of the alternatives

Each goal tries its alternatives in the compiler's order: identity in
`TypeComparer.recur`, then `firstTry` on the right, `secondTry` on the left,
`thirdTry` on the right and `fourthTry` on the left.  An intersection on
the right is final, as in `firstTry`.  Each alternative is a function of its
own and emits its own derivation.  The middle of every transitivity step is a
bound of a member, an operand of an intersection or the declared set of a
variable, read off what the algorithm already holds.  Where the compiler tries
two alternatives with `TypeComparer.either`, each is tried in turn.

A selection on the right skips a member whose lower bound is `⊥`, as
`TypeComparer.isSubApproxHi` fails at once there.  A left side that is `⊥` has
already succeeded by the rule for `⊥`.

A set includes its elements one by one (`CaptureSet.subCaptures`).  An element
is included by identity, by a capture member's bounds, or by its underlying
set (`Capability.subsumes` and `CaptureSet.accountsFor`).

## Differences from the compiler

1. The compiler compares `μ <: μ` through the parents (`thirdTry`) and a `μ`
   on the left by its parent (`fourthTry`).  `SubShape` has no `μ` rule, so a
   `μ` is opened only at a variable.
2. The compiler merges two members of one name (`TypeBounds.&` in
   `core/Types.scala`, and `TypeComparer.hasMatchingMember`).  There is no
   rule for the merge, so each member is tried.
3. The compiler lets a boxed type pass where an unboxed one is expected when
   either capture set is empty (`isBoxCompatibleWith` in `cc/CaptureOps.scala`),
   and heals a box difference (`TypeComparer.healBoxDifference`).
   `SubShape.box` relates boxes to boxes only.  The typer inserts boxes
   instead.
4. The root `any` subsumes every capability in the compiler
   (`Capability.subsumes`).  Here only `Subcap.elem` does.
5. A capture member on the left goes to its upper bound, which is then split
   element by element.  The compiler reaches the same verdict through the
   fallback of `CaptureSet.addNewElem` in an open state, the one typing uses.
   In a closed state it asks one element of the right set to subsume the whole
   bound (`Capability.subsumes`).
6. An atom below a capture member on the right is compared with the whole
   lower bound.  The compiler asks one element of the lower bound to subsume
   it (`Capability.subsumes`).  The verdict is the same.
7. The compiler keeps a singleton's capture set apart from its underlying
   type's (the capturing case of `thirdTry`) and widens a singleton to its
   underlying type at the set `{x}` (`fourthTry`).  There are no singleton
   types here.  The `var` goal plays that part from
   the view of the variable: `{}` for a variable declared at `{}`, `{x}` for
   any other.  The compiler narrows to `{x}` only under a condition
   (`CheckCaptures.improveCaptures`).  The `Var` rule narrows always.

## Fuel

Member lookups go through `decls` and `capDecls` of `Look.lean`.  Their
structural index is the fuel left in the tank.  Each lookup level draws at
least one unit, so the index never runs out before the tank does.

The run is the generic one of `Fuel.lean`, at the cost `cost`.  It uses one
tank for the whole run and the goals pending along the branch, and a goal that
repeats exactly fails.  A goal holds its context, so a goal under a new binder
is never cut by a goal outside it.  `shape?`, `subcap?`, `sub?` and `var?`
start a run from a full tank and return the answer with the tank left.
`shapeF`, `subcapF`, `subF` and `varF` run on a tank they are handed, for a
caller that threads one tank through many goals.

The step is framed and dominated (`step_frame`, `step_dom`), so the facts of
`Fuel.lean` hold for the run.  The four entry points keep an answer at any
larger fuel (`shape?_mono`, `subcap?_mono`, `sub?_mono`, `var?_mono`).

The definitions are structural, so the kernel evaluates the algorithm.  The
checks at the end run it on the examples by `decide +kernel`.
-/

namespace CapturesFrontend.Core

open Frontend.Fuel
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open scoped Captures.DotMNF

deriving instance DecidableEq for Captures.DotMNF.Ctx

/-! ## Goals and answers -/

/-- The three goals of the algorithm. -/
inductive Q (s : Sig) where
  /-- `S <: T` on shapes. -/
  | shape (S T : Shape s)
  /-- `C <: D` on capture sets. -/
  | cap (C D : CaptureSet s)
  /-- The variable `x`, seen at the shape `V`, has the shape `T`. -/
  | var (x : BVar s .var) (V T : Shape s)
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx s
  q : Q s
deriving DecidableEq

/-- The answer to a goal: a `SubShape` derivation, a `Subcap` derivation, or
a map from the variable at one shape to the variable at another. -/
def RQ {s : Sig} (Γ : Ctx s) : Q s → Type
  | .shape S T => SubShape Γ S T
  | .cap C D => Subcap Γ C D
  | .var x V T => VarFn Γ x V T

/-- The answer to a goal in its context. -/
def R (g : G) : Type := RQ g.Γ g.q

/-- The oracle an alternative asks: goals in the same context. -/
abbrev Rec {s : Sig} (Γ : Ctx s) := (q : Q s) → Fu (Option (RQ Γ q))

/-- The oracle for the codomains of two function shapes: goals under the new
binder at the second domain. -/
abbrev RecAll {s : Sig} (Γ : Ctx s) := (T2 : Ty s) → Rec (Γ.cons T2)

/-- A type member of `p` at `A`: its bounds, and the premise of
`SubShape.selUpper` and `SubShape.selLower`. -/
abbrev TyMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (lo : Shape s) × (hi : Shape s) × Var Γ p [.var p] [.var p] (.typ A lo hi)

/-- A capture member of `p` at `A`: its bounds, and the premise of
`Subcap.selUpper` and `Subcap.selLower`. -/
abbrev CapMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (c1 : CaptureSet s) × (c2 : CaptureSet s) × Var Γ p [.var p] [.var p] (.cap A c1 c2)

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
def declsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (TyMem Γ p A)) :=
  fun t => decls Γ t.left p A t

/-- The capture members of `p` at `A`, looked up on the tank.  The index of
the lookup is the fuel left. -/
def capsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (CapMem Γ p A)) :=
  fun t => capDecls Γ t.left p A t

/-- The shape is an intersection. -/
def isAnd {s : Sig} : Shape s → Bool
  | .and _ _ => true
  | _ => false

/-- The shape is an atom of a widening: not `μ`, `∧` or a selection. -/
def isAtom {s : Sig} : Shape s → Bool
  | .mu _ => false
  | .and _ _ => false
  | .sel _ _ => false
  | _ => true

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

/-- Two types by `Sub.capt`: the set goal, then the shape goal, as the
compiler compares a capturing type in `secondTry` and `thirdTry`. -/
def tySub {s : Sig} {Γ : Ctx s} (r : Rec Γ) : (T U : Ty s) → Fu (Option (Sub Γ T U))
  | .capt C S, .capt C' S' =>
      bindO (r (.cap C C')) fun e2 =>
        mapO (r (.shape S S')) fun e1 => Sub.capt e1 e2

/-! ## The `shape` goal, one alternative per compiler case -/

section ShapeAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, as in `TypeComparer.recur`. -/
def sRefl (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : S = T then some (h ▸ SubShape.refl) else none

/-- `Any` on the right, `thirdTryNamed`. -/
def sTop (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : T = .top then some (h ▸ SubShape.top) else none

/-- `Nothing` on the left, `secondTry`. -/
def sBot (S T : Shape s) : Option (SubShape Γ S T) :=
  if h : S = .bot then some (h ▸ SubShape.bot) else none

/-- An intersection on the right, `firstTry`.  Both operands must hold. -/
def sAndR (r : Rec Γ) (S : Shape s) : (T : Shape s) → Fu (Option (SubShape Γ S T))
  | .and T1 T2 =>
      bindO (r (.shape S T1)) fun e1 =>
        mapO (r (.shape S T2)) fun e2 => SubShape.and e1 e2
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member,
`thirdTryNamed`.  Each member is tried.  A member whose lower bound is `⊥` is
skipped, as `isSubApproxHi` fails at once there. -/
def sSelLo (r : Rec Γ) (S : Shape s) : (T : Shape s) → Fu (Option (SubShape Γ S T))
  | .sel (.var p) A =>
      Fu.bind (declsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TyMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.shape S d.1)) fun e => SubShape.trans e (SubShape.selLower d.2.2)) ds
  | _ => Fu.ret none

/-- Two fields, two type members, two capture members, two boxes or two
function shapes of one form, `thirdTry`.  Refinements go by
`compareRefinedSlow` and `hasMatchingMember`.  Bounds go by
`compareTypeBounds`.  A capture member's bounds are capture set types, so its
bounds go to two set goals.  Two boxed capturing types compare by their
types.  Functions have contravariant parameters, as in `isSubInfo`.  The
codomains are compared under the new binder at the second domain. -/
def sStruct (r : Rec Γ) (rAll : RecAll Γ) : (S T : Shape s) → Fu (Option (SubShape Γ S T))
  | .fld a T1, .fld b T2 =>
      if h : a = b then mapO (tySub r T1 T2) (subFld h) else Fu.ret none
  | .typ A S1 T1, .typ B S2 T2 =>
      if h : A = B then
        bindO (r (.shape S2 S1)) fun e1 =>
          mapO (r (.shape T1 T2)) fun e2 => subTyp h e1 e2
      else Fu.ret none
  | .cap A c1 c2, .cap B c1' c2' =>
      if h : A = B then
        bindO (r (.cap c1' c1)) fun e1 =>
          mapO (r (.cap c2 c2')) fun e2 => subCapM h e1 e2
      else Fu.ret none
  | .box T1, .box T2 => mapO (tySub r T1 T2) SubShape.box
  | .all T1 U1, .all T2 U2 =>
      bindO (tySub r T2 T1) fun e1 =>
        mapO (tySub (rAll T2) U1 U2) fun e2 => SubShape.all e1 e2
  | _, _ => Fu.ret none

/-- A selection on the left, through the upper bound of a member, `fourthTry`.
Each member is tried. -/
def sSelHi (r : Rec Γ) (T : Shape s) : (S : Shape s) → Fu (Option (SubShape Γ S T))
  | .sel (.var q) B =>
      Fu.bind (declsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TyMem Γ q B =>
          mapO (r (.shape d.2.1 T)) fun e => SubShape.trans (SubShape.selUpper d.2.2) e) ds
  | _ => Fu.ret none

/-- An intersection on the left, `fourthTry`.  The left operand first, then the
right one, as `either` does. -/
def sAndL (r : Rec Γ) (T : Shape s) : (S : Shape s) → Fu (Option (SubShape Γ S T))
  | .and S1 S2 =>
      Fu.orElse (mapO (r (.shape S1 T)) fun e => SubShape.trans SubShape.and1 e) fun _ =>
        mapO (r (.shape S2 T)) fun e => SubShape.trans SubShape.and2 e
  | _ => Fu.ret none

end ShapeAlts

/-- The `shape` goal: the alternatives in the compiler's order.  An
intersection on the right is final: when `T` is one, nothing after `sAndR` is
tried. -/
def shapeStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rAll : RecAll Γ) (S T : Shape s) :
    Fu (Option (SubShape Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>
  Fu.orElse (Fu.ret (sBot S T)) fun _ =>
  if isAnd T then sAndR r S T else
  Fu.orElse (sSelLo r S T) fun _ =>
  Fu.orElse (sStruct r rAll S T) fun _ =>
  Fu.orElse (sSelHi r T S) fun _ =>
  sAndL r T S

/-! ## The `cap` goal, one alternative per compiler case -/

/-- The capture members a set names, `y.A` for each atom `{y.A}`. -/
def selAtoms {s : Sig} (D : CaptureSet s) : List (BVar s .var × Label) :=
  D.filterMap fun
    | .sel y A => some (y, A)
    | _ => none

section CapAlts

variable {s : Sig} {Γ : Ctx s}

/-- An inclusion, `CaptureSet.accountsFor` by `Capability.subsumes` at
`this eq y`. -/
def cElem (C D : CaptureSet s) : Option (Subcap Γ C D) :=
  if h : CaptureSet.Subset C D then some (Subcap.elem h) else none

/-- A set of two or more atoms, atom by atom: `CaptureSet.tryInclude` with
`forall`, called from `CaptureSet.subCaptures`. -/
def cUnion (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | a :: b :: C, D =>
      bindO (r (.cap [a] D)) fun e1 =>
        mapO (r (.cap (b :: C) D)) fun e2 => Subcap.union (C1 := [a]) (C2 := b :: C) e1 e2
  | _, _ => Fu.ret none

/-- One atom below a capture member that the right set names, through the
member's lower bound: `Capability.subsumes` with `this` a `CapSet` type
reference.  Each selection of the right set and each member is tried. -/
def cSelLo (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [a], D =>
      Fu.firstSome (fun p : BVar s .var × Label =>
        if h : CaptureSet.Subset [CapAtom.sel p.1 p.2] D then
          Fu.bind (capsAt Γ p.1 p.2) fun ds =>
            Fu.firstSome (fun d : CapMem Γ p.1 p.2 =>
              mapO (r (.cap [a] d.1)) fun e =>
                Subcap.trans e (Subcap.trans (Subcap.selLower d.2.2) (Subcap.elem h))) ds
        else Fu.ret none) (selAtoms D)
  | _, _ => Fu.ret none

/-- A capture member on the left, through its upper bound: `Capability.subsumes`
with `y` a `CapSet` type reference, and the fallback of `CaptureSet.addNewElem`
to the underlying set.  Each member is tried. -/
def cSelHi (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [.sel y A], D =>
      Fu.bind (capsAt Γ y A) fun ds =>
        Fu.firstSome (fun d : CapMem Γ y A =>
          mapO (r (.cap d.2.1 D)) fun e => Subcap.trans (Subcap.selUpper d.2.2) e) ds
  | _, _ => Fu.ret none

/-- A term variable on the left, widened to the capture set it is declared
at: `CaptureSet.accountsFor` through `captureSetOfInfo`. -/
def cVar (r : Rec Γ) : (C D : CaptureSet s) → Fu (Option (Subcap Γ C D))
  | [.var x], D => mapO (r (.cap (Γ.lookup x).captureSet D)) fun e => Subcap.trans Subcap.var e
  | _, _ => Fu.ret none

end CapAlts

/-- The `cap` goal: the alternatives in the compiler's order.  A whole
inclusion first, then the split into atoms, then the bounds of a capture
member on either side, then the declared set of a variable. -/
def capStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (C D : CaptureSet s) : Fu (Option (Subcap Γ C D)) :=
  Fu.orElse (Fu.ret (cElem C D)) fun _ =>
  Fu.orElse (cUnion r C D) fun _ =>
  Fu.orElse (cSelLo r C D) fun _ =>
  Fu.orElse (cSelHi r C D) fun _ =>
  cVar r C D

/-! ## The `var` goal, one alternative per compiler case -/

section VarAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, as in `TypeComparer.recur`. -/
def vRefl (x : BVar s .var) (V T : Shape s) : Option (VarFn Γ x V T) :=
  if h : V = T then some (fun _ _ d => h ▸ d) else none

/-- An intersection on the right, `firstTry`, by `HasTy.andI`. -/
def vAndR (r : Rec Γ) (x : BVar s .var) (V : Shape s) : (T : Shape s) → Fu (Option (VarFn Γ x V T))
  | .and T1 T2 =>
      bindO (r (.var x V T1)) fun f1 =>
        mapO (r (.var x V T2)) fun f2 U C d => HasTy.andI (f1 U C d) (f2 U C d)
  | _ => Fu.ret none

/-- A recursive shape on the right with a singleton on the left, `thirdTry`.
`fixRecs` opens the body at the variable, and so does `HasTy.recI`, for a body
that is a declaration. -/
def vMuR (r : Rec Γ) (x : BVar s .var) (V : Shape s) : (T : Shape s) → Fu (Option (VarFn Γ x V T))
  | .mu B =>
      if hB : Shape.Decl B then
        mapO (r (.var x V (B.substVar x))) fun f U C d => HasTy.recI (f U C d) hB
      else Fu.ret none
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, the
variable kept, `thirdTryNamed`.  Each member is tried.  A member whose lower
bound is `⊥` is skipped. -/
def vSelLo (r : Rec Γ) (x : BVar s .var) (V : Shape s) : (T : Shape s) → Fu (Option (VarFn Γ x V T))
  | .sel (.var p) A =>
      Fu.bind (declsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TyMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.var x V d.1)) fun f U C e =>
            HasTy.sub (f U C e) (Sub.capt (SubShape.selLower d.2.2) Subcap.refl) Subcap.refl) ds
  | _ => Fu.ret none

/-- A recursive shape in the view, opened at the variable, `fourthTry`: the
singleton widened, then the recursive shape as `findMember`'s `goRec` opens
it, by `HasTy.recE`, for a body that is a declaration. -/
def vMuL (r : Rec Γ) (x : BVar s .var) (T : Shape s) : (V : Shape s) → Fu (Option (VarFn Γ x V T))
  | .mu B =>
      if hB : Shape.Decl B then
        mapO (r (.var x (B.substVar x) T)) fun f U C d => f U C (HasTy.recE d hB)
      else Fu.ret none
  | _ => Fu.ret none

/-- An intersection in the view, `fourthTry`.  The left operand first, then the
right one, as `either` does. -/
def vAndL (r : Rec Γ) (x : BVar s .var) (T : Shape s) : (V : Shape s) → Fu (Option (VarFn Γ x V T))
  | .and V1 V2 =>
      Fu.orElse (mapO (r (.var x V1 T)) fun f U C d =>
          f U C (HasTy.sub d (Sub.capt SubShape.and1 Subcap.refl) Subcap.refl)) fun _ =>
        mapO (r (.var x V2 T)) fun f U C d =>
          f U C (HasTy.sub d (Sub.capt SubShape.and2 Subcap.refl) Subcap.refl)
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member, `fourthTry`.
Each member is tried. -/
def vSelHi (r : Rec Γ) (x : BVar s .var) (T : Shape s) : (V : Shape s) → Fu (Option (VarFn Γ x V T))
  | .sel (.var q) B =>
      Fu.bind (declsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TyMem Γ q B =>
          mapO (r (.var x d.2.1 T)) fun f U C e =>
            f U C (HasTy.sub e (Sub.capt (SubShape.selUpper d.2.2) Subcap.refl) Subcap.refl)) ds
  | _ => Fu.ret none

/-- An atom of the view against the goal, `fourthTry`: the widened singleton
compared as a shape, by subsumption. -/
def vAtom (r : Rec Γ) (x : BVar s .var) (V T : Shape s) : Fu (Option (VarFn Γ x V T)) :=
  if isAtom V then
    mapO (r (.shape V T)) fun e _ _ d => HasTy.sub d (Sub.capt e Subcap.refl) Subcap.refl
  else Fu.ret none

end VarAlts

/-- The `var` goal: the variable `x`, seen at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  An intersection on the right is final. -/
def varStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (x : BVar s .var) (V T : Shape s) :
    Fu (Option (VarFn Γ x V T)) :=
  Fu.orElse (Fu.ret (vRefl x V T)) fun _ =>
  if isAnd T then vAndR r x V T else
  Fu.orElse (vMuR r x V T) fun _ =>
  Fu.orElse (vSelLo r x V T) fun _ =>
  Fu.orElse (vMuL r x T V) fun _ =>
  Fu.orElse (vAndL r x T V) fun _ =>
  Fu.orElse (vSelHi r x T V) fun _ =>
  vAtom r x V T

/-! ## The step and the entry points -/

/-- One step of the algorithm.  A goal in `Γ` asks goals in `Γ`, and the
codomains of two function shapes are asked in `Γ.cons T2`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .shape S T⟩ =>
      shapeStep Γ (fun q => o ⟨s, Γ, q⟩) (fun T2 q => o ⟨_, Γ.cons T2, q⟩) S T
  | ⟨s, Γ, .cap C D⟩ => capStep Γ (fun q => o ⟨s, Γ, q⟩) C D
  | ⟨s, Γ, .var x V T⟩ => varStep Γ (fun q => o ⟨s, Γ, q⟩) x V T

/-- `S <: T` on shapes, on the tank it is handed.  The run's index is the
fuel left. -/
def shapeF {s : Sig} (Γ : Ctx s) (S T : Shape s) : Fu (Option (SubShape Γ S T)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .shape S T⟩ t

/-- `C <: D` on capture sets, on the tank it is handed. -/
def subcapF {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Fu (Option (Subcap Γ C D)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .cap C D⟩ t

/-- The variable `x`, seen at the shape `V`, at the shape `T`, on the tank it
is handed. -/
def varShapeF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Shape s) :
    Fu (Option (VarFn Γ x V T)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .var x V T⟩ t

/-- `T <: U` on types, on the tank it is handed: the set goal, then the shape
goal. -/
def subF {s : Sig} (Γ : Ctx s) : (T U : Ty s) → Fu (Option (Sub Γ T U))
  | .capt C S, .capt C' S' =>
      bindO (subcapF Γ C C') fun e2 =>
        mapO (shapeF Γ S S') fun e1 => Sub.capt e1 e2

/-- The variable `x`, typed at `V` with the use set `U`, at the type `T`: the
set goal from the set of `V`, then the `var` goal from the shape of `V`. -/
def varFrom {s : Sig} (Γ : Ctx s) (x : BVar s .var) :
    (U : CaptureSet s) → (V : Ty s) → HasTy U Γ (.path (.var x)) V → (T : Ty s) →
    Fu (Option ((U' : CaptureSet s) × HasTy U' Γ (.path (.var x)) T))
  | U, .capt Cv Sv, d, .capt C' S' =>
      bindO (subcapF Γ Cv C') fun e =>
        mapO (varShapeF Γ x Sv S') fun f =>
          ⟨U, HasTy.sub (f U Cv d) (Sub.capt SubShape.refl e) Subcap.refl⟩

/-- `x : T` on the tank it is handed, from the first view of `x`
(`varView`): a variable declared at `{}` is used at `{}`, any other at `{x}`. -/
def varF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    Fu (Option ((U : CaptureSet s) × HasTy U Γ (.path (.var x)) T)) :=
  varFrom Γ x (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv T

/-- `S <: T` on shapes from a full tank of `n` units, with the tank left. -/
def shape? {s : Sig} (Γ : Ctx s) (S T : Shape s) (n : Nat := defaultFuel) :
    Option (SubShape Γ S T) × Tank :=
  shapeF Γ S T ⟨n, false⟩

/-- `C <: D` on capture sets from a full tank of `n` units, with the tank
left. -/
def subcap? {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) (n : Nat := defaultFuel) :
    Option (Subcap Γ C D) × Tank :=
  subcapF Γ C D ⟨n, false⟩

/-- `T <: U` on types from a full tank of `n` units, with the tank left. -/
def sub? {s : Sig} (Γ : Ctx s) (T U : Ty s) (n : Nat := defaultFuel) : Option (Sub Γ T U) × Tank :=
  subF Γ T U ⟨n, false⟩

/-- `x : T` from a full tank of `n` units, with its use set and the tank
left. -/
def var? {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) (n : Nat := defaultFuel) :
    Option ((U : CaptureSet s) × HasTy U Γ (.path (.var x)) T) × Tank :=
  varF Γ x T ⟨n, false⟩

/-! ## The lookups at the tank's own index

`declsAt` and `capsAt` run a lookup whose index is the fuel left.  With more
fuel the index is larger.  A lookup that ends unmarked never reached index
zero, so it gives the same answers at any larger index.  So both are framed,
as every computation of a step must be. -/

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
        exact dite_agree (fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _) (fun _ => ret_agree _)
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
      | all _ _ => exact ret_agree _
      | box _ => exact ret_agree _

/-- A type member lookup that ends unmarked gives the same answers at a
larger index. -/
theorem decls_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (decls Γ d p A t).2.out = false) (hd : d ≤ d') : decls Γ d' p A t = decls Γ d p A t := by
  have hag : Agree (decls Γ d p A) (decls Γ d' p A) :=
    bind_agree (look_agree Γ d d' hd _ _ _ _) fun _ => ret_agree _
  have := hag.sim t _ _ rfl h 0
  simpa using this

/-- A capture member lookup that ends unmarked gives the same answers at a
larger index. -/
theorem capDecls_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (capDecls Γ d p A t).2.out = false) (hd : d ≤ d') :
    capDecls Γ d' p A t = capDecls Γ d p A t := by
  have hag : Agree (capDecls Γ d p A) (capDecls Γ d' p A) :=
    bind_agree (look_agree Γ d d' hd _ _ _ _) fun _ => ret_agree _
  have := hag.sim t _ _ rfl h 0
  simpa using this

/-- The type member lookup at the tank's own index is framed. -/
theorem declsAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (declsAt Γ p A) where
  absorbs t ht := (decls_framed Γ t.left p A).absorbs t ht
  spends t := (decls_framed Γ t.left p A).spends t
  shift := by
    intro t r t' h ho k
    have h1 := decls_frame h ho k
    have h2 : (decls Γ t.left p A (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change decls Γ (t.left + k) p A (t.add k) = _
    rw [decls_index h2 (Nat.le_add_right _ _), h1]

/-- The capture member lookup at the tank's own index is framed. -/
theorem capsAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (capsAt Γ p A) where
  absorbs t ht := (capDecls_framed Γ t.left p A).absorbs t ht
  spends t := (capDecls_framed Γ t.left p A).spends t
  shift := by
    intro t r t' h ho k
    have h1 := capDecls_frame h ho k
    have h2 : (capDecls Γ t.left p A (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change capDecls Γ (t.left + k) p A (t.add k) = _
    rw [capDecls_index h2 (Nat.le_add_right _ _), h1]

/-! ## The step is framed and dominated

`FrameF step` says that oracles which agree give answers which agree.
`DomF step` says that an oracle which dominates another gives answers which
dominate.  `run_frame`, `run_index` and `cut_complete` of `Fuel.lean` ask for
both.  Each alternative is built from `Fu.ret`, `Fu.bind`, `Fu.orElse`,
`Fu.firstSome`, `mapO`, `bindO`, `declsAt`, `capsAt` and tests.  So each has
an agreement lemma and a dominance lemma, each a composition of the
combinator lemmas.  An alternative at one oracle agrees with itself, so it is
framed.  The two facts of the step follow by cases on the goal. -/

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

/-! ### The alternatives of the `shape` goal

The lemmas of `sStruct` and `shapeStep` take the same hypotheses of the
oracles for codomains, `hA`, `hAF` and `hAd`, at every second domain. -/

section ShapeFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rAll rAll' : RecAll Γ} {m : Nat}

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
      exact bind_agree (Agree.refl (declsAt_framed Γ p A)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
  | _ => exact ret_agree _

theorem sSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Shape s) :
    Dom m (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      have hf : ∀ d : TyMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
          else mapO (r (.shape S d.1)) fun e => SubShape.trans e (SubShape.selLower d.2.2)) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (declsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
        ((declsAt_framed Γ p A).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
  | _ => exact ret_dom _ m

theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ T2 q, Agree (rAll T2 q) (rAll' T2 q)) (S T : Shape s) :
    Agree (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact dite_agree (fun _ => mapO_agree _ (tySub_agree hr _ _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact mapO_agree _ (tySub_agree hr _ _)
    | exact bindO_agree (tySub_agree hr _ _) fun _ => mapO_agree _ (tySub_agree (hA _) _ _)

theorem sStruct_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ T2 q, Framed (rAll T2 q)) (hAd : ∀ T2 q, Dom m (rAll T2 q) (rAll' T2 q))
    (S T : Shape s) : Dom m (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact dite_dom (fun _ => mapO_dom _ (tySub_framed hF _ _) (tySub_dom hF hd _ _))
        fun _ => ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact mapO_dom _ (tySub_framed hF _ _) (tySub_dom hF hd _ _)
    | exact bindO_dom (tySub_framed hF _ _) (fun _ => mapO_framed _ (tySub_framed (hAF _) _ _))
        (tySub_dom hF hd _ _) fun _ => mapO_dom _ (tySub_framed (hAF _) _ _)
          (tySub_dom (hAF _) (hAd _) _ _)

theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Shape s) :
    Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_agree (Agree.refl (declsAt_framed Γ q B)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | _ => exact ret_agree _

theorem sSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Shape s) :
    Dom m (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_dom (declsAt_framed Γ q B)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((declsAt_framed Γ q B).dom m) fun ds =>
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

theorem shapeStep_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ T2 q, Agree (rAll T2 q) (rAll' T2 q)) (S T : Shape s) :
    Agree (shapeStep Γ r rAll S T) (shapeStep Γ r' rAll' S T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (sAndR_agree hr S T) <|
    orElse_agree (sSelLo_agree hr S T) <| orElse_agree (sStruct_agree hr hA S T) <|
    orElse_agree (sSelHi_agree hr T S) (sAndL_agree hr T S)

theorem shapeStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ T2 q, Framed (rAll T2 q)) (hAd : ∀ T2 q, Dom m (rAll T2 q) (rAll' T2 q))
    (S T : Shape s) : Dom m (shapeStep Γ r rAll S T) (shapeStep Γ r' rAll' S T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hA : ∀ T2 q, Agree (rAll T2 q) (rAll T2 q) := fun _ _ => Agree.refl (hAF _ _)
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    ite_dom (sAndR_dom hF hd S T) <|
    orElse_dom (sSelLo_agree hr S T).left (sSelLo_dom hF hd S T) <|
    orElse_dom (sStruct_agree hr hA S T).left (sStruct_dom hF hd hAF hAd S T) <|
    orElse_dom (sSelHi_agree hr T S).left (sSelHi_dom hF hd T S) (sAndL_dom hF hd T S)

end ShapeFrames

/-! ### The alternatives of the `cap` goal -/

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
  | a :: _ :: _ => cases a <;> exact ret_dom _ m

theorem cVar_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (cVar r C D) (cVar r' C D) := by
  match C with
  | [] => exact ret_agree _
  | [.var _] => exact mapO_agree _ (hr _)
  | [.sel _ _] => exact ret_agree _
  | [.cvar _] => exact ret_agree _
  | [.any] => exact ret_agree _
  | a :: _ :: _ => cases a <;> exact ret_agree _

theorem cVar_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (cVar r C D) (cVar r' C D) := by
  match C with
  | [] => exact ret_dom _ m
  | [.var _] => exact mapO_dom _ (hF _) (hd _)
  | [.sel _ _] => exact ret_dom _ m
  | [.cvar _] => exact ret_dom _ m
  | [.any] => exact ret_dom _ m
  | a :: _ :: _ => cases a <;> exact ret_dom _ m

theorem capStep_agree (hr : ∀ q, Agree (r q) (r' q)) (C D : CaptureSet s) :
    Agree (capStep Γ r C D) (capStep Γ r' C D) :=
  orElse_agree (ret_agree _) <| orElse_agree (cUnion_agree hr C D) <|
    orElse_agree (cSelLo_agree hr C D) <| orElse_agree (cSelHi_agree hr C D) (cVar_agree hr C D)

theorem capStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (C D : CaptureSet s) :
    Dom m (capStep Γ r C D) (capStep Γ r' C D) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (cUnion_agree hr C D).left (cUnion_dom hF hd C D) <|
    orElse_dom (cSelLo_agree hr C D).left (cSelLo_dom hF hd C D) <|
    orElse_dom (cSelHi_agree hr C D).left (cSelHi_dom hF hd C D) (cVar_dom hF hd C D)

end CapFrames

/-! ### The alternatives of the `var` goal -/

section VarFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem vAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Shape s) :
    Agree (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Shape s) : Dom m (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Shape s) :
    Agree (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem vMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Shape s) : Dom m (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem vSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Shape s) :
    Agree (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      exact bind_agree (Agree.refl (declsAt_framed Γ p A)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
  | _ => exact ret_agree _

theorem vSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Shape s) : Dom m (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      have hf : ∀ d : TyMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
          else mapO (r (.var x V d.1)) fun f U C e =>
            HasTy.sub (f U C e) (Sub.capt (SubShape.selLower d.2.2) Subcap.refl) Subcap.refl) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (declsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
        ((declsAt_framed Γ p A).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
  | _ => exact ret_dom _ m

theorem vMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Shape s) :
    Agree (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem vMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Shape s) : Dom m (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem vAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Shape s) :
    Agree (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Shape s) : Dom m (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Shape s) :
    Agree (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_agree (Agree.refl (declsAt_framed Γ q B)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | _ => exact ret_agree _

theorem vSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Shape s) : Dom m (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_dom (declsAt_framed Γ q B)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((declsAt_framed Γ q B).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | _ => exact ret_dom _ m

theorem vAtom_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Shape s) :
    Agree (vAtom r x V T) (vAtom r' x V T) :=
  ite_agree (mapO_agree _ (hr _)) (ret_agree _)

theorem vAtom_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Shape s) : Dom m (vAtom r x V T) (vAtom r' x V T) :=
  ite_dom (mapO_dom _ (hF _) (hd _)) (ret_dom _ m)

theorem varStep_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Shape s) :
    Agree (varStep Γ r x V T) (varStep Γ r' x V T) :=
  orElse_agree (ret_agree _) <| ite_agree (vAndR_agree hr x V T) <|
    orElse_agree (vMuR_agree hr x V T) <| orElse_agree (vSelLo_agree hr x V T) <|
    orElse_agree (vMuL_agree hr x T V) <| orElse_agree (vAndL_agree hr x T V) <|
    orElse_agree (vSelHi_agree hr x T V) (vAtom_agree hr x V T)

theorem varStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Shape s) : Dom m (varStep Γ r x V T) (varStep Γ r' x V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <| ite_dom (vAndR_dom hF hd x V T) <|
    orElse_dom (vMuR_agree hr x V T).left (vMuR_dom hF hd x V T) <|
    orElse_dom (vSelLo_agree hr x V T).left (vSelLo_dom hF hd x V T) <|
    orElse_dom (vMuL_agree hr x T V).left (vMuL_dom hF hd x T V) <|
    orElse_dom (vAndL_agree hr x T V).left (vAndL_dom hF hd x T V) <|
    orElse_dom (vSelHi_agree hr x T V).left (vSelHi_dom hF hd x T V) (vAtom_dom hF hd x V T)

end VarFrames

/-! ### The step -/

theorem step_frame : FrameF step := by
  intro o o' ho g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | shape S T =>
    exact shapeStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun T2 q => o ⟨_, Γ.cons T2, q⟩) (rAll' := fun T2 q => o' ⟨_, Γ.cons T2, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun T2 q => ho ⟨_, Γ.cons T2, q⟩) S T
  | cap C D =>
    exact capStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) C D
  | var x V T =>
    exact varStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) x V T

theorem step_dom : DomF step := by
  intro m o o' hF _ hd g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | shape S T =>
    exact shapeStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun T2 q => o ⟨_, Γ.cons T2, q⟩) (rAll' := fun T2 q => o' ⟨_, Γ.cons T2, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun T2 q => hF ⟨_, Γ.cons T2, q⟩) (fun T2 q => hd ⟨_, Γ.cons T2, q⟩) S T
  | cap C D =>
    exact capStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) C D
  | var x V T =>
    exact varStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) x V T

/-! ## The entry points keep an answer with more fuel

A run whose index is the fuel left is framed, as `declsAt` is.  A run that
ends unmarked never reached index zero, so it does the same at any larger
index.  An answer of the run leaves the tank unmarked.  `subF` and `varFrom`
join two runs by `bindO` and `mapO`, which keep both facts.  So the four
entry points keep an answer at any larger fuel. -/

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

end Unmarked

theorem shapeF_framed {s : Sig} (Γ : Ctx s) (S T : Shape s) : Framed (shapeF Γ S T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .shape S T⟩

theorem subcapF_framed {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Framed (subcapF Γ C D) :=
  runLeft_framed step_frame [] ⟨s, Γ, .cap C D⟩

theorem varShapeF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Shape s) :
    Framed (varShapeF Γ x V T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .var x V T⟩

theorem subF_framed {s : Sig} (Γ : Ctx s) (T U : Ty s) : Framed (subF Γ T U) := by
  cases T
  cases U
  exact bindO_framed (subcapF_framed _ _ _) fun _ => mapO_framed _ (shapeF_framed _ _ _)

theorem varFrom_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s) (V : Ty s)
    (d : HasTy U Γ (.path (.var x)) V) (T : Ty s) : Framed (varFrom Γ x U V d T) := by
  cases V
  cases T
  exact bindO_framed (subcapF_framed _ _ _) fun _ => mapO_framed _ (varShapeF_framed _ _ _ _)

theorem varF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Framed (varF Γ x T) :=
  varFrom_framed _ _ _ _ _ _

theorem subF_someUnmarked {s : Sig} (Γ : Ctx s) (T U : Ty s) : SomeUnmarked (subF Γ T U) := by
  cases T
  cases U
  exact bindO_someUnmarked fun _ => mapO_someUnmarked _ (runLeft_someUnmarked _ _)

theorem varFrom_someUnmarked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s)
    (V : Ty s) (d : HasTy U Γ (.path (.var x)) V) (T : Ty s) :
    SomeUnmarked (varFrom Γ x U V d T) := by
  cases V
  cases T
  exact bindO_someUnmarked fun _ => mapO_someUnmarked _ (runLeft_someUnmarked _ _)

theorem varF_someUnmarked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    SomeUnmarked (varF Γ x T) :=
  varFrom_someUnmarked _ _ _ _ _ _

theorem shape?_mono {s : Sig} {Γ : Ctx s} {S T : Shape s} {n m : Nat} {e : SubShape Γ S T}
    (h : (shape? Γ S T n).1 = some e) (hnm : n ≤ m) : (shape? Γ S T m).1 = some e :=
  full_mono (shapeF_framed Γ S T) (runLeft_someUnmarked _ _) h hnm

theorem subcap?_mono {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {n m : Nat} {e : Subcap Γ C D}
    (h : (subcap? Γ C D n).1 = some e) (hnm : n ≤ m) : (subcap? Γ C D m).1 = some e :=
  full_mono (subcapF_framed Γ C D) (runLeft_someUnmarked _ _) h hnm

theorem sub?_mono {s : Sig} {Γ : Ctx s} {T U : Ty s} {n m : Nat} {e : Sub Γ T U}
    (h : (sub? Γ T U n).1 = some e) (hnm : n ≤ m) : (sub? Γ T U m).1 = some e :=
  full_mono (subF_framed Γ T U) (subF_someUnmarked Γ T U) h hnm

theorem var?_mono {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n m : Nat}
    {e : (U : CaptureSet s) × HasTy U Γ (.path (.var x)) T}
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

open Captures.DotMNF.Examples

/-- `μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C : {}..{κ₁}}))`, at the platform. -/
def P1M : Shape ([],c,c) :=
  .mu (.and (.fld lb (.top ^ [])) (.and (.fld lv (.top ^ []))
    (.cap lC [] [CapAtom.cvar (.there k1)])))

/-- `∀(y : P1M) ⊤ ^ {y.C}`. -/
def P1S : Shape ([],c,c) := .all (P1M ^ []) (.top ^ [CapAtom.sel .here lC])

/-- `∀(y : P1M) ⊤ ^ {κ₁}`. -/
def P1T : Shape ([],c,c) := .all (P1M ^ []) (.top ^ [CapAtom.cvar (.there k1)])

/-- The two platform capabilities and `n` variables. -/
def chainBase : Nat → Sig
  | 0 => ([],c,c)
  | n + 1 => Sig.extend (chainBase n) .var

/-- The signature of a chain of `n` links: the platform and `n + 1`
variables. -/
def chainSig (n : Nat) : Sig := Sig.extend (chainBase n) .var

/-- `κ₁` under the variables of a chain. -/
def k1At : (n : Nat) → BVar (chainBase n) .cap
  | 0 => k1
  | n + 1 => .there (k1At n)

/-- `κ₂` under the variables of a chain. -/
def k2At : (n : Nat) → BVar (chainBase n) .cap
  | 0 => k2
  | n + 1 => .there (k2At n)

/-- An alias chain of capture members: `x0 : {C : {κ₁}..{κ₁}}` and
`xk : {C : {x(k-1).C}..{x(k-1).C}}` for `k = 1..n`. -/
def chainCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => platCtx.cons ((Shape.cap lC [CapAtom.cvar k1] [CapAtom.cvar k1]) ^ [])
  | n + 1 => (chainCtx n).cons ((Shape.cap lC [CapAtom.sel .here lC] [CapAtom.sel .here lC]) ^ [])

/-- A link with two equal capture members, so each step through an upper
bound tries both. -/
def dLink {s : Sig} : Shape (s,x) :=
  .and (.cap lC [CapAtom.sel .here lC] [CapAtom.sel .here lC])
    (.cap lC [CapAtom.sel .here lC] [CapAtom.sel .here lC])

/-- The chain of `chainCtx` with every link doubled. -/
def dchainCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => platCtx.cons ((Shape.cap lC [CapAtom.cvar k1] [CapAtom.cvar k1]) ^ [])
  | n + 1 => (dchainCtx n).cons (dLink ^ [])

/-- R3's context at the projection: `x : {A : ⊥..{a : {b : ⊤}}}`,
`y : x.A ∧ {a : {b : {v : ⊤}}}`. -/
def R3Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot (.fld la ((Shape.fld lb (.top ^ [])) ^ []))) ^ [])).cons
    ((Shape.and (.sel (.var .here) lA)
      (.fld la ((Shape.fld lb ((Shape.fld lv (.top ^ [])) ^ [])) ^ []))) ^ [])

/-- `q : {A : ⊥..⊤}`, `x : q.A ^ {}`: a variable at its own abstract shape,
declared at the empty set. -/
def XCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `q.A ^ {}`, seen from `XCtx`. -/
def XT : Ty ([],x,x) := (Shape.sel (.var (.there .here)) lA) ^ []

/-- `q : {A : ⊥..⊤}`, `p : {A : ⊥..q.A}`, `x : p.A ^ {}`. -/
def X2Ctx : Ctx ([],x,x,x) :=
  ((Ctx.nil.cons ((Shape.typ lA .bot .top) ^ [])).cons
    ((Shape.typ lA .bot (.sel (.var .here) lA)) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `q.A ^ {}`, seen from `X2Ctx`. -/
def X2T : Ty ([],x,x,x) := (Shape.sel (.var (.there (.there .here))) lA) ^ []

/-- `p : μ(s. {A : ⊥..∀(y : ⊤) s.A})`, `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`.
`p.A <: q.B` has no finite derivation.  Each level reaches the goal again
under a new binder. -/
def LPCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.mu (.typ lA .bot
      (.all (.top ^ []) ((Shape.sel (.var (.there .here)) lA) ^ [])))) ^ [])).cons
    ((Shape.mu (.typ lB (.all (.top ^ []) ((Shape.sel (.var (.there .here)) lB) ^ [])) .top)) ^ [])

/-- `μ(t. {C : s.A..s.A} ∧ {B : ⊥..∀(w : t.C) w.B} ∧ {T : ∀(w : t.C) w.T..⊤})`. -/
def LPw2Body : Shape ([],x,x) :=
  .and (.typ lC (.sel (.var (.there .here)) lA) (.sel (.var (.there .here)) lA))
    (.and (.typ lB .bot (.all ((Shape.sel (.var .here) lC) ^ []) ((Shape.sel (.var .here) lB) ^ [])))
      (.typ lT (.all ((Shape.sel (.var .here) lC) ^ []) ((Shape.sel (.var .here) lT) ^ [])) .top))

/-- `p : μ(s. {A : ⊥..μ(t. …)})`, then `y : p.A`.  The domain of each
function is the variable's own member, so every goal of the loop mentions
the newest binder. -/
def LPw2Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.mu (.typ lA .bot (.mu LPw2Body))) ^ [])).cons
    ((Shape.sel (.var .here) lA) ^ [])

-- C2: `{g} <: {κ₁, κ₂}`, the declared set of `g`, then the upper bound of a
-- capture member, found on demand.
example : answers (subcap? (C2CtxG platCtx k1 k2) [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1))), CapAtom.cvar (.there (.there (.there k2)))]) 15
    = true := by decide +kernel
-- The upper bound is `{κ₁, κ₂}`, so `{g}` is not below `{κ₁}`.
example : rejects (subcap? (C2CtxG platCtx k1 k2) [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1)))]) 23 = true := by decide +kernel

-- S1: `{fs} <: {cp.C}` through the lower bound of `cp`'s capture member.
example : answers (subcap? S1Ctx2 [CapAtom.cvar fs2] [CapAtom.sel .here lC]) 6 = true := by
  decide +kernel

-- C5: `{n} <: {fs}`, the declared set `{it.C}`, then the member's upper bound.
example : answers (subcap? S2Ctx4 [CapAtom.var .here] [CapAtom.cvar fs4]) 15 = true := by
  decide +kernel

-- E6: `Int <: z.T` at the self binder's own member.
example : answers (shape? E6Ctxz E6IntS (.sel (.var .here) lT)) 12 = true := by decide +kernel
example : answers (var? E6Ctxz (.there .here) ((Shape.sel (.var .here) lT) ^ [])) 13 = true := by
  decide +kernel

-- E8: `x.A <: {a : ⊤}` through the upper bound.
example : answers (shape? E8Ctx2 (.sel (.var (.there .here)) lA) (.fld la (.top ^ []))) 4 = true := by
  decide +kernel
-- The converse of E8 fails: the lower bound of `x.A` is `⊥`.
example : rejects (shape? E8Ctx2 (.fld la (.top ^ [])) (.sel (.var (.there .here)) lA)) 2 = true := by
  decide +kernel

-- E3s: `{b : ⊤} <: x.A` through the second member's lower bound.
example : answers (shape? E3Ctx2 E3T2S (.sel (.var (.there .here)) lA)) 8 = true := by
  decide +kernel
-- E3s: `x.A <: {a : ⊤}` through the first member's upper bound.
example : answers (shape? E3Ctx2 (.sel (.var (.there .here)) lA) E3T1S) 8 = true := by
  decide +kernel

-- C2's literal `a`, at its precise type, retyped at the abstract type: `Rec-I`,
-- `And-I`, `Rec-E`, the capture member, and `{} <: {κ₁, κ₂}`.
example : answers (var? C2Ctx2 .here
    (C2AbsTy (.there (.there (.there .here))) (.there (.there .here)))) 59 = true := by
  decide +kernel

-- P1cc: a capture member three levels down a recursive binder, under a `∀`.
example : answers (shape? platCtx P1S P1T) 29 = true := by decide +kernel
-- The converse fails: `{κ₁}` is not below `{y.C}`, whose lower bound is `{}`.
example : rejects (shape? platCtx P1T P1S) 27 = true := by decide +kernel

-- An alias chain of capture members at 8 and 16 links, both ways.
example : answers (subcap? (chainCtx 8) [CapAtom.sel .here lC] [CapAtom.cvar (.there (k1At 8))]) 64
    = true := by decide +kernel
example : answers (subcap? (chainCtx 8) [CapAtom.cvar (.there (k1At 8))] [CapAtom.sel .here lC]) 64
    = true := by decide +kernel
example : answers (subcap? (chainCtx 16) [CapAtom.sel .here lC] [CapAtom.cvar (.there (k1At 16))])
    188 = true := by decide +kernel
example : answers (subcap? (chainCtx 16) [CapAtom.cvar (.there (k1At 16))] [CapAtom.sel .here lC])
    188 = true := by decide +kernel

-- R3: `y : x.A ∧ {a : {b : {v : ⊤}}}` has the field `{a : {b : {v : ⊤}}}`, by
-- the right operand.
example : answers (var? R3Ctx .here
    ((Shape.fld la ((Shape.fld lb ((Shape.fld lv (.top ^ [])) ^ [])) ^ [])) ^ [.var .here])) 36
    = true := by decide +kernel

-- A variable at its own abstract shape, at the empty set: the set goal and the
-- shape goal are separate, so `x : q.A ^ {}` holds by identity on the shape.
example : answers (var? XCtx .here XT) 2 = true := by decide +kernel
-- The same through an upper bound: `x : p.A ^ {}` at `q.A ^ {}`.
example : answers (var? X2Ctx .here X2T) 6 = true := by decide +kernel

-- E1, E3 and E4 as written are rejected with the tank unmarked, as scalac
-- rejects them.
example : rejects (sub? E1Ctx E1Dom E1Res) 2 = true := by decide +kernel
example : rejects (var? E1Ctx .here E1Res) 4 = true := by decide +kernel
example : rejects (sub? E3Ctx2 E3T2 E3T1) 2 = true := by decide +kernel
example : rejects (sub? E4Ctx4 E4Int ((Shape.sel (.var (.there (.there .here))) lA) ^ [])) 3
    = true := by decide +kernel
example : rejects (var? E4Ctx4 (.there .here) ((Shape.sel (.var (.there (.there .here))) lA) ^ []))
    6 = true := by decide +kernel

-- LPw2: the lookup opens both binders, `y.B <: ∀(w : y.C) w.B`.
example : answers (shape? LPw2Ctx (.sel (.var .here) lB)
    (.all ((Shape.sel (.var .here) lC) ^ []) ((Shape.sel (.var .here) lB) ^ []))) 32 = true := by
  decide +kernel

-- The loops LP and LPw2 exhaust the tank: the recursion limit.
example : (shape? LPCtx (.sel (.var (.there .here)) lA) (.sel (.var .here) lB)).2.out = true := by
  decide +kernel
example : (shape? LPw2Ctx (.sel (.var .here) lB) (.sel (.var .here) lT)).2.out = true := by
  decide +kernel

-- The doubled chain at 12 links.  The goal that fails, `{x12.C} <: {κ₂}`, tries
-- both members at every link and exhausts the tank: the recursion limit.
example : answers (subcap? (dchainCtx 12) [CapAtom.sel .here lC] [CapAtom.cvar (.there (k1At 12))])
    166 = true := by decide +kernel
example : (subcap? (dchainCtx 12) [CapAtom.sel .here lC] [CapAtom.cvar (.there (k2At 12))]).2.out
    = true := by decide +kernel

end SubChecks

end CapturesFrontend.Core
