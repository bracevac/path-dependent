import Coercions.Paths.Frontend.Look

/-!
# Subtyping on paths

The algorithm decides three goals.

- `sub S T` asks for `S <: T`, answered by a `Sub` derivation.
- `path p V T` asks that the path `p`, already seen at the type `V`, have the
  type `T`.  It is the compiler's `p.type <: T` with `p.type` widened to `V`.
  It is answered by a map from a derivation of `p : V` to one of `p : T`.
- `var x V T` asks the same of the variable `x` as a term.  It is answered by
  a map between `HasTy` derivations.

The calculus has three judgments where the compiler has one.  `Sub` has no rule
for a singleton.  Every singleton rule is a rule of `PathTy`, and `HasTy`
reads `PathTy` only at a singleton goal (`HasTy.sngl`).  So a singleton on the
left is widened in a `path` goal only, never in a `sub` or `var` goal.

Each goal tries its alternatives in the order of `TypeComparer.recur`.  First
comes identity, then `firstTry` on the right, `secondTry` on the left,
`thirdTry` on the right and `fourthTry` on the left.  An intersection on the
right is final, as in `firstTry`.  Each alternative is a function of its own
and emits the calculus's own derivation.  The middle of every transitivity
step is read off a type the algorithm already holds: a bound of a member, an
operand of an intersection or a declared type of a path.  No middle is chosen
from the context.  Where the compiler tries two alternatives with `either`,
each is tried in turn.

A singleton `q.type` in the view of a path `p` is widened to each declared
type of `q`, and the path `p` is kept, by `PathTy.snglTrans`.  So a recursive
type reached through the singleton is opened at `p`, as `fixRecs` opens it at
the anchor and as `goRec` of `Types.findMember` opens it at the prefix of the
lookup.

The calculus differs from the compiler in these places.

- The compiler widens a singleton on the left in any goal (`fourthTry`, case
  `SingletonType`).  Here only a `path` goal widens it.
- The compiler relates `p.A` and `q.A` through `isSubPrefix` for an abstract
  `A` (`firstTry`, `compareNamed`).  The calculus has no rule for it.
- The compiler compares two recursive types through their parents (`thirdTry`,
  `compareRec`).  It compares a recursive type on the left by its parent
  (`fourthTry`).  The calculus relates two recursive types through the abstract
  view `Sub.mu`.  It opens a recursive type on one side only at a path.
- The compiler merges two members of one name (`TypeBounds.&`,
  `hasMatchingMember`).  The calculus has no rule for that, so each member is
  tried.
- `matchAbstractTypeMember` has no rule in the calculus and is left out.
- The compiler gives up after a failed alias (`firstTry`, `canDropAlias`).
  Here every alternative is tried, which only adds successes.

A selection on the right skips a member whose lower bound is `⊥`, as
`isSubApproxHi` fails at once there.  A left side that is `⊥` has already
succeeded by the rule for `⊥`.

Member lookups go through `lookP`, `startP` and `declsP` of `Look.lean`.  Their
structural index is the fuel left in the tank.  Each lookup level draws at
least one unit, so the index never runs out before the tank does.  A lookup at
a larger index does the same, so the lookups at the tank's own index are framed
(`lookF_framed`, `startF_framed`, `declsF_framed`).

The run is the generic one of `Fuel.lean`, at the cost `cost`.  There is one
tank for the whole run and one list of the goals pending along the branch.  A
goal that repeats exactly fails.  A goal holds its context, so a goal under a
new binder is never cut by a goal outside it.  `sub?`, `path?` and `var?`
start a run from a full tank and return the answer with the tank left.  `subF`,
`pathF` and `varF` run on a tank they are handed, for a caller that threads one
tank through many goals.

Every definition is structural, so the kernel evaluates the algorithm.  The
checks at the end of the module run it on the examples by `decide +kernel`.
-/

namespace PathsFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Ctx Sub PathTy HasTy)

deriving instance DecidableEq for Paths.DotMNF.Ctx

/-! ## Goals and answers -/

/-- The three goals of the algorithm. -/
inductive Q (s : Sig) where
  /-- `S <: T`. -/
  | sub (S T : Ty s)
  /-- The path `p`, seen at `V`, has the type `T`. -/
  | path (p : Path s) (V T : Ty s)
  /-- The variable `x` as a term, seen at `V`, has the type `T`. -/
  | var (x : BVar s .var) (V T : Ty s)
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx s
  q : Q s
deriving DecidableEq

/-- A term typing of the variable `x`. -/
abbrev Var {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Type :=
  HasTy Γ (.path x) T

/-- The answer to a goal: a derivation of `S <: T`, or a map from a
derivation at the view to one at the goal. -/
def RQ {s : Sig} (Γ : Ctx s) : Q s → Type
  | .sub S T => Sub Γ S T
  | .path p V T => PathTy Γ p V → PathTy Γ p T
  | .var x V T => Var Γ x V → Var Γ x T

/-- The answer to a goal in its context. -/
def R (g : G) : Type := RQ g.Γ g.q

/-- The oracle an alternative asks: goals in the same context. -/
abbrev Rec {s : Sig} (Γ : Ctx s) := (q : Q s) → Fu (Option (RQ Γ q))

/-- The oracle for the codomains of two function types, under the new
binder at the second domain. -/
abbrev RecAll {s : Sig} (Γ : Ctx s) :=
  (S2 : Ty s) → (T1 T2 : Ty (s,x)) → Fu (Option (Sub (Γ.cons S2) T1 T2))

/-! ## Combinators and tests -/

/-- Run `c`, and map an answer through `f`. -/
def mapO {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (Option β) :=
  Fu.bind c fun o => Fu.ret (o.map f)

/-- The type is an intersection. -/
def isAnd {s : Sig} : Ty s → Bool
  | .and _ _ => true
  | _ => false

/-- The type is an atom of a path's widening: not `μ`, `∧`, a selection or a
singleton. -/
def isAtom {s : Sig} : Ty s → Bool
  | .mu _ => false
  | .and _ _ => false
  | .sel _ _ => false
  | .sngl _ => false
  | _ => true

/-- The type is an atom of a variable's widening as a term.  A singleton is
one, since `HasTy` has no rule that widens it. -/
def isVAtom {s : Sig} : Ty s → Bool
  | .mu _ => false
  | .and _ _ => false
  | .sel _ _ => false
  | _ => true

/-- `Sub.fld` across a decided label equality. -/
def subFld {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b) (e : Sub Γ S T) :
    Sub Γ (.fld a S) (.fld b T) := by
  cases h
  exact Sub.fld e

/-- `Sub.vfld` across a decided label equality. -/
def subVfld {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b) (e : Sub Γ S T) :
    Sub Γ (.vfld a S) (.vfld b T) := by
  cases h
  exact Sub.vfld e

/-- A stable field below a field, `Sub.vfldToFld` then `Sub.fld`, across a
decided label equality. -/
def subVfldFld {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b) (e : Sub Γ S T) :
    Sub Γ (.vfld a S) (.fld b T) := by
  cases h
  exact Sub.trans Sub.vfldToFld (Sub.fld e)

/-- `Sub.typ` across a decided label equality. -/
def subTyp {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Ty s} (h : A = B)
    (e1 : Sub Γ S2 S1) (e2 : Sub Γ T1 T2) : Sub Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h
  exact Sub.typ e1 e2

/-- `PathTy.snglSel` across a decided label equality. -/
def snglSelAt {s : Sig} {Γ : Ctx s} {p q : Path s} {a b : Label} {T : Ty s} (h : a = b)
    (d1 : PathTy Γ p (.sngl q)) (d2 : PathTy Γ p (.vfld a T)) :
    PathTy Γ (.sel p b) (.sngl (.sel q a)) := by
  cases h
  exact PathTy.snglSel d1 d2

/-! ## Lookups at the tank's own index

A step receives only its oracle, not the run's index.  The lookups need a
structural index, and they take the fuel left.  Each lookup level draws at
least one unit, so the index reaches zero only when the tank is empty. -/

/-- The types of `p`, seen at `V`, that fit the key `k`, looked up on the tank. -/
def lookF {s : Sig} (Γ : Ctx s) (p : Path s) (V : Ty s) (k : Key) : Fu (List (FoundP Γ p V)) :=
  fun t => lookP Γ t.left [] p V k t

/-- The declared types of `q`, looked up on the tank. -/
def startF {s : Sig} (Γ : Ctx s) (q : Path s) : Fu (List (PV Γ q)) :=
  fun t => startP Γ t.left q t

/-- The type members of `q` at `A`, looked up on the tank. -/
def declsF {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) : Fu (List (Mem Γ q A)) :=
  fun t => declsP Γ t.left q A t

/-! ## The `sub` goal, one alternative per compiler case -/

section SubAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, `TypeComparer.recur`. -/
def sRefl (S T : Ty s) : Option (Sub Γ S T) :=
  if h : S = T then some (h ▸ Sub.refl) else none

/-- `Any` on the right, `thirdTryNamed`. -/
def sTop (S T : Ty s) : Option (Sub Γ S T) :=
  if h : T = .top then some (h ▸ Sub.top) else none

/-- `Nothing` on the left, `secondTry`. -/
def sBot (S T : Ty s) : Option (Sub Γ S T) :=
  if h : S = .bot then some (h ▸ Sub.bot) else none

/-- An intersection on the right, `firstTry`.  Both operands must hold. -/
def sAndR (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))
  | .and T1 T2 =>
      bindO (r (.sub S T1)) fun e1 =>
        mapO (r (.sub S T2)) fun e2 => Sub.and e1 e2
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member,
`thirdTryNamed`.  Each member is tried.  A member whose lower bound is `⊥` is
skipped, as `isSubApproxHi` fails at once there. -/
def sSelLo (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))
  | .sel q A =>
      Fu.bind (declsF Γ q A) fun ms =>
        Fu.firstSome (fun m : Mem Γ q A =>
          if m.lo = .bot then Fu.ret none
          else mapO (r (.sub S m.lo)) fun e => Sub.trans e (Sub.selLower m.d)) ms
  | _ => Fu.ret none

/-- Two members of one shape, `thirdTry`.  Fields and type members are
refinements, compared by `compareRefinedSlow` and `hasMatchingMember`.  A stable
field below a field is a `val` below a `def`, as in `hasMatchingMember`.  Bounds
go by `compareTypeBounds`.  Function types have contravariant parameters, by
`isSubInfo`, and the codomains are compared under the new binder at the second
domain.  Two recursive types go through the abstract view `Sub.mu`, where the
compiler compares the parents (`compareRec`).  The walker `subDecl?` asks this
oracle at each self-free step. -/
def sStruct (r : Rec Γ) (rAll : RecAll Γ) : (S T : Ty s) → Fu (Option (Sub Γ S T))
  | .fld a S', .fld b T' =>
      if h : a = b then mapO (r (.sub S' T')) (subFld h) else Fu.ret none
  | .vfld a S', .vfld b T' =>
      if h : a = b then mapO (r (.sub S' T')) (subVfld h) else Fu.ret none
  | .vfld a S', .fld b T' =>
      if h : a = b then mapO (r (.sub S' T')) (subVfldFld h) else Fu.ret none
  | .typ A S1 T1, .typ B S2 T2 =>
      if h : A = B then
        bindO (r (.sub S2 S1)) fun e1 =>
          mapO (r (.sub T1 T2)) fun e2 => subTyp h e1 e2
      else Fu.ret none
  | .all S1 T1, .all S2 T2 =>
      bindO (r (.sub S2 S1)) fun e1 =>
        mapO (rAll S2 T1 T2) fun e2 => Sub.all e1 e2
  | .mu D1, .mu D2 =>
      if h1 : Ty.Decl D1 then
        if h2 : Ty.Decl D2 then
          mapO (subDecl? (fun S T => r (.sub S T)) D1 D2) fun e => Sub.mu e h1 h2
        else Fu.ret none
      else Fu.ret none
  | _, _ => Fu.ret none

/-- A selection on the left, through the upper bound of a member,
`fourthTry`.  Each member is tried. -/
def sSelHi (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))
  | .sel q B =>
      Fu.bind (declsF Γ q B) fun ms =>
        Fu.firstSome (fun m : Mem Γ q B =>
          mapO (r (.sub m.hi T)) fun e => Sub.trans (Sub.selUpper m.d) e) ms
  | _ => Fu.ret none

/-- An intersection on the left, `fourthTry`.  The left operand first,
then the right one, as `either` does. -/
def sAndL (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))
  | .and S1 S2 =>
      Fu.orElse (mapO (r (.sub S1 T)) fun e => Sub.trans Sub.and1 e) fun _ =>
        mapO (r (.sub S2 T)) fun e => Sub.trans Sub.and2 e
  | _ => Fu.ret none

end SubAlts

/-- The `sub` goal: the alternatives in the compiler's order.  An
intersection on the right is final: when `T` is one, nothing after `sAndR` is
tried. -/
def subStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rAll : RecAll Γ) (S T : Ty s) :
    Fu (Option (Sub Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>
  Fu.orElse (Fu.ret (sBot S T)) fun _ =>
  if isAnd T then sAndR r S T else
  Fu.orElse (sSelLo r S T) fun _ =>
  Fu.orElse (sStruct r rAll S T) fun _ =>
  Fu.orElse (sSelHi r T S) fun _ =>
  sAndL r T S

/-! ## The `path` goal, one alternative per compiler case -/

/-- A map from a derivation of `p : V` to one of `p : T`. -/
abbrev PathFn {s : Sig} (Γ : Ctx s) (p : Path s) (V T : Ty s) : Type :=
  PathTy Γ p V → PathTy Γ p T

section PathAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, `TypeComparer.recur`. -/
def pRefl (p : Path s) (V T : Ty s) : Option (PathFn Γ p V T) :=
  if h : V = T then some (fun d => h ▸ d) else none

/-- The path's own singleton, identity on `p.type`, by
`PathTy.snglRefl`. -/
def pSelf (p : Path s) (V T : Ty s) : Option (PathFn Γ p V T) :=
  if h : T = .sngl p then some (fun d => h ▸ PathTy.snglRefl d) else none

/-- An intersection on the right, `firstTry`, by `PathTy.andI`. -/
def pAndR (r : Rec Γ) (p : Path s) (V : Ty s) : (T : Ty s) → Fu (Option (PathFn Γ p V T))
  | .and T1 T2 =>
      bindO (r (.path p V T1)) fun f1 =>
        mapO (r (.path p V T2)) fun f2 d => PathTy.andI (f1 d) (f2 d)
  | _ => Fu.ret none

/-- Two singletons of one stable field, `firstTry`.  `compareNamed` compares
the prefixes (`isSubPrefix`).  By `PathTy.snglSel`, `p'.a` has `(q'.a).type`
when `p'` has `q'.type` and a stable field `a`.  The prefix is checked from each
of its declared types. -/
def pPre (r : Rec Γ) : (p : Path s) → (V T : Ty s) → Fu (Option (PathFn Γ p V T))
  | .sel p' b, _, .sngl (.sel q' a) =>
      if h : a = b then
        Fu.bind (startF Γ p') (Fu.firstSome fun w =>
          bindO (r (.path p' w.ty (.sngl q'))) fun f =>
            Fu.bind (lookF Γ p' w.ty (.vfld a)) fun es =>
              Fu.ret (es.findSome? fun e => (e.vfld? a).map fun g _ =>
                snglSelAt h (f w.d) (g.2 w.d)))
      else Fu.ret none
  | _, _, _ => Fu.ret none

/-- A singleton on the right whose path is itself declared at a singleton,
`fourthTry`, `comparePaths`.  If `q` has `q'.type`, then `p.type <: q.type`
follows from `p.type <: q'.type`.  `PathTy.snglSym` and `PathTy.snglInv` turn
`q : q'.type` into `q' : q.type`, and `PathTy.snglTrans` composes. -/
def pAlias (r : Rec Γ) (p : Path s) (V : Ty s) : (T : Ty s) → Fu (Option (PathFn Γ p V T))
  | .sngl q =>
      Fu.bind (startF Γ q) (Fu.firstSome fun w =>
        Fu.bind (lookF Γ q w.ty .sngl) (Fu.firstSome fun e =>
          match e.sngl? with
          | some g =>
              mapO (r (.path p V (.sngl g.1))) fun f d =>
                PathTy.snglTrans (f d) (PathTy.snglSym (g.2 w.d) (PathTy.snglInv (g.2 w.d)))
          | none => Fu.ret none))
  | _ => Fu.ret none

/-- A recursive type on the right, `thirdTry`.  `fixRecs` opens the body at the
anchor, the path, and so does `PathTy.recI`. -/
def pMuR (r : Rec Γ) (p : Path s) (V : Ty s) : (T : Ty s) → Fu (Option (PathFn Γ p V T))
  | .mu B =>
      if hd : Ty.Decl B then mapO (r (.path p V (B.substPath p))) fun f d => PathTy.recI (f d) hd
      else Fu.ret none
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, the path
kept, `thirdTryNamed`.  Each member is tried.  A member whose lower bound is `⊥`
is skipped, as `isSubApproxHi` fails at once there. -/
def pSelLo (r : Rec Γ) (p : Path s) (V : Ty s) : (T : Ty s) → Fu (Option (PathFn Γ p V T))
  | .sel q A =>
      Fu.bind (declsF Γ q A) fun ms =>
        Fu.firstSome (fun m : Mem Γ q A =>
          if m.lo = .bot then Fu.ret none
          else mapO (r (.path p V m.lo)) fun f d => PathTy.sub (f d) (Sub.selLower m.d)) ms
  | _ => Fu.ret none

/-- A recursive type in the view, opened at the path, as `goRec` of
`Types.findMember` opens it at the prefix, by `PathTy.recE`. -/
def pMuL (r : Rec Γ) (p : Path s) (T : Ty s) : (V : Ty s) → Fu (Option (PathFn Γ p V T))
  | .mu B =>
      if hd : Ty.Decl B then mapO (r (.path p (B.substPath p) T)) fun f d => f (PathTy.recE d hd)
      else Fu.ret none
  | _ => Fu.ret none

/-- An intersection in the view, `fourthTry`.  The left operand first, then
the right one, as `either` does. -/
def pAndL (r : Rec Γ) (p : Path s) (T : Ty s) : (V : Ty s) → Fu (Option (PathFn Γ p V T))
  | .and V1 V2 =>
      Fu.orElse (mapO (r (.path p V1 T)) fun f d => f (PathTy.sub d Sub.and1)) fun _ =>
        mapO (r (.path p V2 T)) fun f d => f (PathTy.sub d Sub.and2)
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member,
`fourthTry`.  Each member is tried. -/
def pSelHi (r : Rec Γ) (p : Path s) (T : Ty s) : (V : Ty s) → Fu (Option (PathFn Γ p V T))
  | .sel q B =>
      Fu.bind (declsF Γ q B) fun ms =>
        Fu.firstSome (fun m : Mem Γ q B =>
          mapO (r (.path p m.hi T)) fun f d => f (PathTy.sub d (Sub.selUpper m.d))) ms
  | _ => Fu.ret none

/-- A singleton `q.type` in the view, `fourthTry`: the singleton widened to its
underlying type (`tp1widened`).  Each declared type of `q` is tried, and the
path `p` is kept, by `PathTy.snglTrans`.  So a recursive type found there is
opened at `p`, as `fixRecs` opens it at the anchor. -/
def pSnglL (r : Rec Γ) (p : Path s) (T : Ty s) : (V : Ty s) → Fu (Option (PathFn Γ p V T))
  | .sngl q =>
      Fu.bind (startF Γ q) (Fu.firstSome fun w =>
        mapO (r (.path p w.ty T)) fun f d => f (PathTy.snglTrans d w.d))
  | _ => Fu.ret none

/-- An atom of the view against the goal, `fourthTry`: the widened singleton
compared as a type (`tp1widened`), by `PathTy.sub`. -/
def pAtom (r : Rec Γ) (p : Path s) (V T : Ty s) : Fu (Option (PathFn Γ p V T)) :=
  if isAtom V then mapO (r (.sub V T)) fun e d => PathTy.sub d e else Fu.ret none

end PathAlts

/-- The `path` goal: the path `p`, seen at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  An intersection on the right is final. -/
def pathStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (p : Path s) (V T : Ty s) :
    Fu (Option (PathFn Γ p V T)) :=
  Fu.orElse (Fu.ret (pRefl p V T)) fun _ =>
  Fu.orElse (Fu.ret (pSelf p V T)) fun _ =>
  if isAnd T then pAndR r p V T else
  Fu.orElse (pPre r p V T) fun _ =>
  Fu.orElse (pAlias r p V T) fun _ =>
  Fu.orElse (pMuR r p V T) fun _ =>
  Fu.orElse (pSelLo r p V T) fun _ =>
  Fu.orElse (pMuL r p T V) fun _ =>
  Fu.orElse (pAndL r p T V) fun _ =>
  Fu.orElse (pSelHi r p T V) fun _ =>
  Fu.orElse (pSnglL r p T V) fun _ =>
  pAtom r p V T

/-! ## The `var` goal, one alternative per compiler case -/

/-- A map from a derivation of `x : V` to one of `x : T`. -/
abbrev VarFn {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Ty s) : Type :=
  Var Γ x V → Var Γ x T

section VarAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, `TypeComparer.recur`. -/
def vRefl (x : BVar s .var) (V T : Ty s) : Option (VarFn Γ x V T) :=
  if h : V = T then some (fun d => h ▸ d) else none

/-- A singleton on the right is a `path` goal at the variable, through
`HasTy.toPathTy` and back through `HasTy.sngl`. -/
def vSngl (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .sngl q => mapO (r (.path (.var x) V (.sngl q))) fun f d => HasTy.sngl (f d.toPathTy)
  | _ => Fu.ret none

/-- An intersection on the right, `firstTry`, by `HasTy.andI`. -/
def vAndR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .and T1 T2 =>
      bindO (r (.var x V T1)) fun f1 =>
        mapO (r (.var x V T2)) fun f2 d => HasTy.andI (f1 d) (f2 d)
  | _ => Fu.ret none

/-- A recursive type on the right, `thirdTry`.  `fixRecs` opens the body at the
variable, and so does `HasTy.recI`. -/
def vMuR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .mu B =>
      if hd : Ty.Decl B then mapO (r (.var x V (B.substVar x))) fun f d => HasTy.recI (f d) hd
      else Fu.ret none
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, the
variable kept, `thirdTryNamed`.  Each member is tried.  A member whose lower
bound is `⊥` is skipped, as `isSubApproxHi` fails at once there. -/
def vSelLo (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .sel q A =>
      Fu.bind (declsF Γ q A) fun ms =>
        Fu.firstSome (fun m : Mem Γ q A =>
          if m.lo = .bot then Fu.ret none
          else mapO (r (.var x V m.lo)) fun f d => HasTy.sub (f d) (Sub.selLower m.d)) ms
  | _ => Fu.ret none

/-- A recursive type in the view, opened at the variable, as `goRec` of
`Types.findMember` opens it, by `HasTy.recE`. -/
def vMuL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .mu B =>
      if hd : Ty.Decl B then mapO (r (.var x (B.substVar x) T)) fun f d => f (HasTy.recE d hd)
      else Fu.ret none
  | _ => Fu.ret none

/-- An intersection in the view, `fourthTry`.  The left operand first, then
the right one, as `either` does. -/
def vAndL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .and V1 V2 =>
      Fu.orElse (mapO (r (.var x V1 T)) fun f d => f (HasTy.sub d Sub.and1)) fun _ =>
        mapO (r (.var x V2 T)) fun f d => f (HasTy.sub d Sub.and2)
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member,
`fourthTry`.  Each member is tried. -/
def vSelHi (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .sel q B =>
      Fu.bind (declsF Γ q B) fun ms =>
        Fu.firstSome (fun m : Mem Γ q B =>
          mapO (r (.var x m.hi T)) fun f d => f (HasTy.sub d (Sub.selUpper m.d))) ms
  | _ => Fu.ret none

/-- An atom of the view against the goal, `fourthTry`, by subsumption.  A
singleton is an atom here, so the term is never widened through it. -/
def vAtom (r : Rec Γ) (x : BVar s .var) (V T : Ty s) : Fu (Option (VarFn Γ x V T)) :=
  if isVAtom V then mapO (r (.sub V T)) fun e d => HasTy.sub d e else Fu.ret none

end VarAlts

/-- The `var` goal: the variable `x`, seen at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  An intersection on the right is final. -/
def varStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (x : BVar s .var) (V T : Ty s) :
    Fu (Option (VarFn Γ x V T)) :=
  Fu.orElse (Fu.ret (vRefl x V T)) fun _ =>
  Fu.orElse (vSngl r x V T) fun _ =>
  if isAnd T then vAndR r x V T else
  Fu.orElse (vMuR r x V T) fun _ =>
  Fu.orElse (vSelLo r x V T) fun _ =>
  Fu.orElse (vMuL r x T V) fun _ =>
  Fu.orElse (vAndL r x T V) fun _ =>
  Fu.orElse (vSelHi r x T V) fun _ =>
  vAtom r x V T

/-! ## The step and the entry points -/

/-- One step of the algorithm.  A goal in `Γ` asks goals in `Γ`, and the
codomains of two function types are asked in `Γ.cons S2`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .sub S T⟩ =>
      subStep Γ (fun q => o ⟨s, Γ, q⟩) (fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | ⟨s, Γ, .path p V T⟩ => pathStep Γ (fun q => o ⟨s, Γ, q⟩) p V T
  | ⟨s, Γ, .var x V T⟩ => varStep Γ (fun q => o ⟨s, Γ, q⟩) x V T

/-- The run from an empty list of pending goals, at the index of the fuel
left. -/
def runF (g : G) : Fu (Option (R g)) := fun t => run cost step t.left [] g t

/-- `S <: T` on the tank it is handed. -/
def subF {s : Sig} (Γ : Ctx s) (S T : Ty s) : Fu (Option (Sub Γ S T)) :=
  runF ⟨s, Γ, .sub S T⟩

/-- `p : T` on the tank it is handed, from each declared type of `p`. -/
def pathF {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Fu (Option (PathTy Γ p T)) :=
  Fu.bind (startF Γ p) (Fu.firstSome fun w =>
    mapO (runF ⟨s, Γ, .path p w.ty T⟩) fun f => f w.d)

/-- `x : T` on the tank it is handed, from the type `x` is declared at. -/
def varF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Fu (Option (Var Γ x T)) :=
  mapO (runF ⟨s, Γ, .var x (Γ.lookup x) T⟩) fun f => f .var

/-- `S <: T` from a full tank of `n` units, with the tank left. -/
def sub? {s : Sig} (Γ : Ctx s) (S T : Ty s) (n : Nat := defaultFuel) : Option (Sub Γ S T) × Tank :=
  subF Γ S T ⟨n, false⟩

/-- `p : T` from a full tank of `n` units, with the tank left. -/
def path? {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) (n : Nat := defaultFuel) :
    Option (PathTy Γ p T) × Tank :=
  pathF Γ p T ⟨n, false⟩

/-- `x : T` from a full tank of `n` units, with the tank left. -/
def var? {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) (n : Nat := defaultFuel) :
    Option (Var Γ x T) × Tank :=
  varF Γ x T ⟨n, false⟩

/-! ## The lookups at the tank's own index are framed

A lookup that ends unmarked never reached index zero, so it gives the same
answers at any larger index (`lookP_agree`).  With more fuel the index is
larger.  So a lookup at the index of the fuel left is framed, as every
computation of a step must be. -/

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

/-- A family of computations indexed by `d`, each doing what the one at a
smaller index does, is framed at the index of the fuel left. -/
theorem atLeft_framed {α : Type} {c : Nat → Fu α} (hc : ∀ d d', d ≤ d' → Agree (c d) (c d')) :
    Framed (fun t => c t.left t) where
  absorbs t ht := (hc t.left t.left (Nat.le_refl _)).left.absorbs t ht
  spends t := (hc t.left t.left (Nat.le_refl _)).left.spends t
  shift := by
    intro t r t' h ho j
    exact (hc t.left (t.left + j) (Nat.le_add_right _ _)).sim t r t' h ho j

/-- The declared types of a path agree when the lookups they call agree. -/
theorem startOf_agree {s : Sig} {Γ : Ctx s} {lk lk' : Lk Γ}
    (hlk : ∀ p V k, Agree (lk p V k) (lk' p V k)) : ∀ q, Agree (startOf lk q) (startOf lk' q)
  | .var _ => ret_agree _
  | .sel r _ =>
    bind_agree (startOf_agree hlk r) (flatMapL_agree fun _ =>
      bind_agree (hlk _ _ _) fun _ => ret_agree _)

/-- The members of a path agree when the lookups they call agree. -/
theorem declsAt_agree {s : Sig} {Γ : Ctx s} {lk lk' : Lk Γ}
    (hlk : ∀ p V k, Agree (lk p V k) (lk' p V k)) (q : Path s) (A : Label) :
    Agree (declsAt lk q A) (declsAt lk' q A) :=
  bind_agree (startOf_agree hlk q) (flatMapL_agree fun _ =>
    bind_agree (hlk _ _ _) fun _ => ret_agree _)

/-- A path lookup at a larger index does what the lookup at a smaller one
does. -/
theorem lookP_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ (P : List (LKey s)) (p : Path s) (V : Ty s) (k : Key),
      Agree (lookP Γ d P p V k) (lookP Γ d' P p V k)
  | 0, d', _, P, p, V, k => by
    refine ⟨lookP_framed Γ 0 P p V k, lookP_framed Γ d' P p V k, ?_⟩
    intro t r t' h ho _
    simp only [lookP, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, p, V, k => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := lookP_agree Γ d e (by omega)
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
      | sel q B =>
        exact bind_agree (declsAt_agree (ih _) _ _) (flatMapL_agree fun _ =>
          bind_agree (ih _ _ _ _) fun _ => ret_agree _)
      | sngl q =>
        exact bind_agree (startOf_agree (ih _) _) (flatMapL_agree fun _ =>
          bind_agree (ih _ _ _ _) fun _ => ret_agree _)
      | top => exact ret_agree _
      | bot => exact ret_agree _
      | typ _ _ _ => exact ret_agree _
      | fld _ _ => exact ret_agree _
      | vfld _ _ => exact ret_agree _
      | all _ _ => exact ret_agree _

theorem lookF_framed {s : Sig} (Γ : Ctx s) (p : Path s) (V : Ty s) (k : Key) :
    Framed (lookF Γ p V k) :=
  atLeft_framed fun d d' hd => lookP_agree Γ d d' hd [] p V k

theorem startF_framed {s : Sig} (Γ : Ctx s) (q : Path s) : Framed (startF Γ q) :=
  atLeft_framed fun d d' hd => startOf_agree (lookP_agree Γ d d' hd []) q

theorem declsF_framed {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) : Framed (declsF Γ q A) :=
  atLeft_framed fun d d' hd => declsAt_agree (lookP_agree Γ d d' hd []) q A

/-! ## The step is framed and dominated

`FrameF step` says that oracles which agree give answers which agree.
`DomF step` says that an oracle which dominates another gives answers which
dominate.  `run_frame`, `run_index` and `cut_complete` of `Fuel.lean` ask for
both.  Each alternative is built from `Fu.ret`, `Fu.bind`, `Fu.orElse`,
`Fu.firstSome`, `mapO`, `bindO`, the lookups `lookF`, `startF` and `declsF`,
the walker `subDecl?` and tests.  So each has an agreement lemma and a
dominance lemma, composed from the combinator lemmas.  A lookup asks no oracle,
so it agrees with itself and dominates itself.  An alternative that agrees with
itself is framed.  The two facts of the step follow by cases on the goal. -/

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

theorem mapO_framed {c : Fu (Option α)} (f : α → β) (hc : Framed c) : Framed (mapO c f) :=
  bind_framed hc fun _ => ret_framed _

theorem mapO_agree {c c' : Fu (Option α)} (f : α → β) (hc : Agree c c') :
    Agree (mapO c f) (mapO c' f) :=
  bind_agree hc fun _ => ret_agree _

theorem mapO_dom {c c' : Fu (Option α)} (f : α → β) (hc : Framed c) (hd : Dom m c c') :
    Dom m (mapO c f) (mapO c' f) :=
  bind_dom hc (fun _ => ret_framed _) hd fun _ => ret_dom _ m

end OptionFrames

/-! ### The alternatives of the `sub` goal

The agreement lemmas take oracles `r` and `r'` that agree on every goal.  The
dominance lemmas take a framed `r` that dominates `r'` below `m`.  The lemmas
of `sStruct` and `subStep` take the same of the oracles for codomains. -/

section SubFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rAll rAll' : RecAll Γ} {m : Nat}

theorem sAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty s) :
    Dom m (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel q A =>
    exact bind_agree (Agree.refl (declsF_framed Γ q A)) fun ms =>
      firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ms
  | _ => exact ret_agree _

theorem sSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty s) :
    Dom m (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel q A =>
    have hf : ∀ n : Mem Γ q A, Framed (if n.lo = .bot then Fu.ret none
        else mapO (r (.sub S n.lo)) fun e => Sub.trans e (Sub.selLower n.d)) :=
      fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
    exact bind_dom (declsF_framed Γ q A) (fun ms => firstSome_framed hf ms)
      ((declsF_framed Γ q A).dom m) fun ms =>
        firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ms
  | _ => exact ret_dom _ m

theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Agree (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact bindO_agree (hr _) fun _ => mapO_agree _ (hA _ _ _)
    | exact dite_agree (fun _ => dite_agree
        (fun _ => mapO_agree _ (subDecl?_agree (fun _ _ => hr _) _ _)) fun _ => ret_agree _)
        fun _ => ret_agree _

theorem sStruct_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ S2 T1 T2, Framed (rAll S2 T1 T2))
    (hAd : ∀ S2 T1 T2, Dom m (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Dom m (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact bindO_dom (hF _) (fun _ => mapO_framed _ (hAF _ _ _)) (hd _)
        fun _ => mapO_dom _ (hAF _ _ _) (hAd _ _ _)
    | exact dite_dom (fun _ => dite_dom
        (fun _ => mapO_dom _ (subDecl?_framed (fun _ _ => hF _) _ _)
          (subDecl?_dom (fun _ _ => hF _) (fun _ _ => hd _) _ _)) fun _ => ret_dom _ m)
        fun _ => ret_dom _ m

theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) :
    Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel q B =>
    exact bind_agree (Agree.refl (declsF_framed Γ q B)) fun ms =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ms
  | _ => exact ret_agree _

theorem sSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty s) :
    Dom m (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel q B =>
    exact bind_dom (declsF_framed Γ q B)
      (fun ms => firstSome_framed (fun _ => mapO_framed _ (hF _)) ms)
      ((declsF_framed Γ q B).dom m) fun ms =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ms
  | _ => exact ret_dom _ m

theorem sAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) :
    Agree (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty s) :
    Dom m (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem subStep_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Agree (subStep Γ r rAll S T) (subStep Γ r' rAll' S T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (sAndR_agree hr S T) <|
    orElse_agree (sSelLo_agree hr S T) <| orElse_agree (sStruct_agree hr hA S T) <|
    orElse_agree (sSelHi_agree hr T S) (sAndL_agree hr T S)

theorem subStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ S2 T1 T2, Framed (rAll S2 T1 T2))
    (hAd : ∀ S2 T1 T2, Dom m (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Dom m (subStep Γ r rAll S T) (subStep Γ r' rAll' S T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll S2 T1 T2) := fun _ _ _ => Agree.refl (hAF _ _ _)
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    ite_dom (sAndR_dom hF hd S T) <|
    orElse_dom (sSelLo_agree hr S T).left (sSelLo_dom hF hd S T) <|
    orElse_dom (sStruct_agree hr hA S T).left (sStruct_dom hF hd hAF hAd S T) <|
    orElse_dom (sSelHi_agree hr T S).left (sSelHi_dom hF hd T S) (sAndL_dom hF hd T S)

end SubFrames

/-! ### The alternatives of the `path` goal -/

section PathFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem pAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pAndR r p V T) (pAndR r' p V T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem pAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pAndR r p V T) (pAndR r' p V T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem pPre_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pPre r p V T) (pPre r' p V T) := by
  cases p with
  | var x => exact ret_agree _
  | sel p' b =>
    cases T with
    | sngl q =>
      cases q with
      | var y => exact ret_agree _
      | sel q' a =>
        exact dite_agree (fun _ => bind_agree (Agree.refl (startF_framed Γ p')) fun ws =>
          firstSome_agree (fun _ => bindO_agree (hr _) fun _ =>
            bind_agree (Agree.refl (lookF_framed _ _ _ _)) fun _ => ret_agree _) ws)
          fun _ => ret_agree _
    | _ => exact ret_agree _

theorem pPre_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pPre r p V T) (pPre r' p V T) := by
  cases p with
  | var x => exact ret_dom _ m
  | sel p' b =>
    cases T with
    | sngl q =>
      cases q with
      | var y => exact ret_dom _ m
      | sel q' a =>
        refine dite_dom (fun _ => ?_) fun _ => ret_dom _ m
        refine bind_dom (startF_framed Γ p') (fun ws => firstSome_framed (fun w => ?_) ws)
          ((startF_framed Γ p').dom m) fun ws => firstSome_dom (fun w => ?_) (fun w => ?_) ws
        · exact bindO_framed (hF _) fun _ => bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _
        · exact bindO_framed (hF _) fun _ => bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _
        · exact bindO_dom (hF _) (fun _ => bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _)
            (hd _) fun _ => (bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _).dom m
    | _ => exact ret_dom _ m

theorem pAlias_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pAlias r p V T) (pAlias r' p V T) := by
  cases T with
  | sngl q =>
    refine bind_agree (Agree.refl (startF_framed Γ q)) fun ws => firstSome_agree (fun w => ?_) ws
    refine bind_agree (Agree.refl (lookF_framed Γ q w.ty .sngl)) fun es =>
      firstSome_agree (fun e => ?_) es
    dsimp only
    split
    · exact mapO_agree _ (hr _)
    · exact ret_agree _
  | _ => exact ret_agree _

theorem pAlias_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pAlias r p V T) (pAlias r' p V T) := by
  cases T with
  | sngl q =>
    refine bind_dom (startF_framed Γ q) (fun ws => firstSome_framed (fun w => ?_) ws)
      ((startF_framed Γ q).dom m) fun ws => firstSome_dom (fun w => ?_) (fun w => ?_) ws
    · refine bind_framed (lookF_framed Γ q w.ty .sngl) fun es =>
        firstSome_framed (fun e => ?_) es
      dsimp only
      split
      · exact mapO_framed _ (hF _)
      · exact ret_framed _
    · refine bind_framed (lookF_framed Γ q w.ty .sngl) fun es =>
        firstSome_framed (fun e => ?_) es
      dsimp only
      split
      · exact mapO_framed _ (hF _)
      · exact ret_framed _
    · refine bind_dom (lookF_framed Γ q w.ty .sngl) (fun es => firstSome_framed (fun e => ?_) es)
        ((lookF_framed Γ q w.ty .sngl).dom m) fun es =>
          firstSome_dom (fun e => ?_) (fun e => ?_) es
      all_goals dsimp only
      all_goals split
      all_goals first
        | exact mapO_framed _ (hF _)
        | exact ret_framed _
        | exact mapO_dom _ (hF _) (hd _)
        | exact ret_dom _ m
  | _ => exact ret_dom _ m

theorem pMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pMuR r p V T) (pMuR r' p V T) := by
  cases T with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem pMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pMuR r p V T) (pMuR r' p V T) := by
  cases T with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem pSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pSelLo r p V T) (pSelLo r' p V T) := by
  cases T with
  | sel q A =>
    exact bind_agree (Agree.refl (declsF_framed Γ q A)) fun ms =>
      firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ms
  | _ => exact ret_agree _

theorem pSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pSelLo r p V T) (pSelLo r' p V T) := by
  cases T with
  | sel q A =>
    have hf : ∀ n : Mem Γ q A, Framed (if n.lo = .bot then Fu.ret none
        else mapO (r (.path p V n.lo)) fun f d => PathTy.sub (f d) (Sub.selLower n.d)) :=
      fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
    exact bind_dom (declsF_framed Γ q A) (fun ms => firstSome_framed hf ms)
      ((declsF_framed Γ q A).dom m) fun ms =>
        firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ms
  | _ => exact ret_dom _ m

theorem pMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T V : Ty s) :
    Agree (pMuL r p T V) (pMuL r' p T V) := by
  cases V with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem pMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (T V : Ty s) : Dom m (pMuL r p T V) (pMuL r' p T V) := by
  cases V with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem pAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T V : Ty s) :
    Agree (pAndL r p T V) (pAndL r' p T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [pAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem pAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (T V : Ty s) : Dom m (pAndL r p T V) (pAndL r' p T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [pAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem pSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T V : Ty s) :
    Agree (pSelHi r p T V) (pSelHi r' p T V) := by
  cases V with
  | sel q B =>
    exact bind_agree (Agree.refl (declsF_framed Γ q B)) fun ms =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ms
  | _ => exact ret_agree _

theorem pSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (T V : Ty s) : Dom m (pSelHi r p T V) (pSelHi r' p T V) := by
  cases V with
  | sel q B =>
    exact bind_dom (declsF_framed Γ q B)
      (fun ms => firstSome_framed (fun _ => mapO_framed _ (hF _)) ms)
      ((declsF_framed Γ q B).dom m) fun ms =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ms
  | _ => exact ret_dom _ m

theorem pSnglL_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T V : Ty s) :
    Agree (pSnglL r p T V) (pSnglL r' p T V) := by
  cases V with
  | sngl q =>
    exact bind_agree (Agree.refl (startF_framed Γ q)) fun ws =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ws
  | _ => exact ret_agree _

theorem pSnglL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (T V : Ty s) : Dom m (pSnglL r p T V) (pSnglL r' p T V) := by
  cases V with
  | sngl q =>
    exact bind_dom (startF_framed Γ q)
      (fun ws => firstSome_framed (fun _ => mapO_framed _ (hF _)) ws)
      ((startF_framed Γ q).dom m) fun ws =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ws
  | _ => exact ret_dom _ m

theorem pAtom_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pAtom r p V T) (pAtom r' p V T) :=
  ite_agree (mapO_agree _ (hr _)) (ret_agree _)

theorem pAtom_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pAtom r p V T) (pAtom r' p V T) :=
  ite_dom (mapO_dom _ (hF _) (hd _)) (ret_dom _ m)

theorem pathStep_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (V T : Ty s) :
    Agree (pathStep Γ r p V T) (pathStep Γ r' p V T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (pAndR_agree hr p V T) <|
    orElse_agree (pPre_agree hr p V T) <| orElse_agree (pAlias_agree hr p V T) <|
    orElse_agree (pMuR_agree hr p V T) <| orElse_agree (pSelLo_agree hr p V T) <|
    orElse_agree (pMuL_agree hr p T V) <| orElse_agree (pAndL_agree hr p T V) <|
    orElse_agree (pSelHi_agree hr p T V) <| orElse_agree (pSnglL_agree hr p T V) <|
    pAtom_agree hr p V T

theorem pathStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (p : Path s)
    (V T : Ty s) : Dom m (pathStep Γ r p V T) (pathStep Γ r' p V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    ite_dom (pAndR_dom hF hd p V T) <|
    orElse_dom (pPre_agree hr p V T).left (pPre_dom hF hd p V T) <|
    orElse_dom (pAlias_agree hr p V T).left (pAlias_dom hF hd p V T) <|
    orElse_dom (pMuR_agree hr p V T).left (pMuR_dom hF hd p V T) <|
    orElse_dom (pSelLo_agree hr p V T).left (pSelLo_dom hF hd p V T) <|
    orElse_dom (pMuL_agree hr p T V).left (pMuL_dom hF hd p T V) <|
    orElse_dom (pAndL_agree hr p T V).left (pAndL_dom hF hd p T V) <|
    orElse_dom (pSelHi_agree hr p T V).left (pSelHi_dom hF hd p T V) <|
    orElse_dom (pSnglL_agree hr p T V).left (pSnglL_dom hF hd p T V) <|
    pAtom_dom hF hd p V T

end PathFrames

/-! ### The alternatives of the `var` goal -/

section VarFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem vSngl_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vSngl r x V T) (vSngl r' x V T) := by
  cases T with
  | sngl q => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vSngl_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vSngl r x V T) (vSngl r' x V T) := by
  cases T with
  | sngl q => exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem vMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem vSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel q A =>
    exact bind_agree (Agree.refl (declsF_framed Γ q A)) fun ms =>
      firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ms
  | _ => exact ret_agree _

theorem vSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel q A =>
    have hf : ∀ n : Mem Γ q A, Framed (if n.lo = .bot then Fu.ret none
        else mapO (r (.var x V n.lo)) fun f d => HasTy.sub (f d) (Sub.selLower n.d)) :=
      fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
    exact bind_dom (declsF_framed Γ q A) (fun ms => firstSome_framed hf ms)
      ((declsF_framed Γ q A).dom m) fun ms =>
        firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ms
  | _ => exact ret_dom _ m

theorem vMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
  | _ => exact ret_agree _

theorem vMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
  | _ => exact ret_dom _ m

theorem vAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel q B =>
    exact bind_agree (Agree.refl (declsF_framed Γ q B)) fun ms =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) ms
  | _ => exact ret_agree _

theorem vSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel q B =>
    exact bind_dom (declsF_framed Γ q B)
      (fun ms => firstSome_framed (fun _ => mapO_framed _ (hF _)) ms)
      ((declsF_framed Γ q B).dom m) fun ms =>
        firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ms
  | _ => exact ret_dom _ m

theorem vAtom_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vAtom r x V T) (vAtom r' x V T) :=
  ite_agree (mapO_agree _ (hr _)) (ret_agree _)

theorem vAtom_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vAtom r x V T) (vAtom r' x V T) :=
  ite_dom (mapO_dom _ (hF _) (hd _)) (ret_dom _ m)

theorem varStep_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (varStep Γ r x V T) (varStep Γ r' x V T) :=
  orElse_agree (ret_agree _) <| orElse_agree (vSngl_agree hr x V T) <|
    ite_agree (vAndR_agree hr x V T) <|
    orElse_agree (vMuR_agree hr x V T) <| orElse_agree (vSelLo_agree hr x V T) <|
    orElse_agree (vMuL_agree hr x T V) <| orElse_agree (vAndL_agree hr x T V) <|
    orElse_agree (vSelHi_agree hr x T V) (vAtom_agree hr x V T)

theorem varStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (varStep Γ r x V T) (varStep Γ r' x V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (vSngl_agree hr x V T).left (vSngl_dom hF hd x V T) <|
    ite_dom (vAndR_dom hF hd x V T) <|
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
  | sub S T =>
    exact subStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (rAll' := fun S2 T1 T2 => o' ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun S2 T1 T2 => ho ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | path p V T =>
    exact pathStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) p V T
  | var x V T =>
    exact varStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) x V T

theorem step_dom : DomF step := by
  intro m o o' hF _ hd g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (rAll' := fun S2 T1 T2 => o' ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun S2 T1 T2 => hF ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun S2 T1 T2 => hd ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | path p V T =>
    exact pathStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) p V T
  | var x V T =>
    exact varStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) x V T

/-! ## The entry points keep an answer with more fuel

A run whose index is the fuel left is framed, as the lookups are.  A run that
ends unmarked never reached index zero, so it does the same at any larger
index.  So `subF`, `pathF` and `varF` are framed.  An answer of each leaves the
tank unmarked, so the frame lemma carries it to any larger fuel. -/

/-- An answer of `c` leaves the tank unmarked. -/
def Unmarked {α : Type} (c : Fu (Option α)) : Prop :=
  ∀ t, (c t).1.isSome = true → (c t).2.out = false

section Unmarked

variable {α β : Type}

theorem bind_unmarked {γ : Type} {c : Fu γ} {f : γ → Fu (Option β)} (hf : ∀ a, Unmarked (f a)) :
    Unmarked (Fu.bind c f) := by
  intro t h
  simp only [Fu.bind] at h ⊢
  exact hf _ _ h

theorem mapO_unmarked {c : Fu (Option α)} (f : α → β) (hc : Unmarked c) : Unmarked (mapO c f) := by
  intro t h
  simp only [mapO, Fu.bind, Fu.ret] at h ⊢
  rw [Option.isSome_map] at h
  exact hc t h

theorem firstSome_unmarked {f : α → Fu (Option β)} (hf : ∀ a, Unmarked (f a)) :
    ∀ l, Unmarked (Fu.firstSome f l)
  | [] => by
    intro t h
    simp [Fu.firstSome, Fu.ret] at h
  | a :: l => by
    intro t h
    simp only [Fu.firstSome, Fu.orElse] at h ⊢
    have ha := hf a t
    revert h ha
    cases f a t with
    | mk o t1 =>
      cases o with
      | some _ => exact fun _ ha => ha rfl
      | none =>
        cases ht : t1.out
        · simp only [ht, Bool.false_eq_true, if_false]
          exact fun h _ => firstSome_unmarked hf l t1 h
        · simp [ht]

end Unmarked

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

theorem run_unmarked (d : Nat) (P : List G) (g : G) : Unmarked (run cost F d P g) := by
  intro t h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  exact run_some hx

end RunLeft

theorem runF_framed (g : G) : Framed (runF g) :=
  atLeft_framed fun d d' hd => run_agree step_frame d d' hd [] g

theorem runF_unmarked (g : G) : Unmarked (runF g) := fun t => run_unmarked t.left [] g t

theorem subF_framed {s : Sig} (Γ : Ctx s) (S T : Ty s) : Framed (subF Γ S T) :=
  runF_framed _

theorem pathF_framed {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Framed (pathF Γ p T) :=
  bind_framed (startF_framed Γ p) fun ws =>
    firstSome_framed (fun _ => mapO_framed _ (runF_framed _)) ws

theorem varF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Framed (varF Γ x T) :=
  mapO_framed _ (runF_framed _)

theorem subF_unmarked {s : Sig} (Γ : Ctx s) (S T : Ty s) : Unmarked (subF Γ S T) :=
  runF_unmarked _

theorem pathF_unmarked {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Unmarked (pathF Γ p T) :=
  bind_unmarked fun ws => firstSome_unmarked (fun _ => mapO_unmarked _ (runF_unmarked _)) ws

theorem varF_unmarked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Unmarked (varF Γ x T) :=
  mapO_unmarked _ (runF_unmarked _)

/-- A full tank of `n` units with `m - n` more is a full tank of `m` units. -/
theorem full_add {n m : Nat} (h : n ≤ m) : (⟨n, false⟩ : Tank).add (m - n) = ⟨m, false⟩ := by
  simp only [Tank.add, Tank.mk.injEq, and_true]
  omega

/-- A framed computation whose answers leave the tank unmarked keeps an answer
from a full tank at any larger full tank. -/
theorem full_mono {α : Type} {c : Fu (Option α)} (hF : Framed c) (hU : Unmarked c) {n m : Nat}
    {e : α} (h : (c ⟨n, false⟩).1 = some e) (hnm : n ≤ m) : (c ⟨m, false⟩).1 = some e := by
  have ho : (c ⟨n, false⟩).2.out = false := hU _ (by simp [h])
  have := hF.shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  rw [this]

theorem sub?_mono {s : Sig} {Γ : Ctx s} {S T : Ty s} {n m : Nat} {e : Sub Γ S T}
    (h : (sub? Γ S T n).1 = some e) (hnm : n ≤ m) : (sub? Γ S T m).1 = some e :=
  full_mono (subF_framed Γ S T) (subF_unmarked Γ S T) h hnm

theorem path?_mono {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} {n m : Nat} {e : PathTy Γ p T}
    (h : (path? Γ p T n).1 = some e) (hnm : n ≤ m) : (path? Γ p T m).1 = some e :=
  full_mono (pathF_framed Γ p T) (pathF_unmarked Γ p T) h hnm

theorem var?_mono {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n m : Nat} {e : Var Γ x T}
    (h : (var? Γ x T n).1 = some e) (hnm : n ≤ m) : (var? Γ x T m).1 = some e :=
  full_mono (varF_framed Γ x T) (varF_unmarked Γ x T) h hnm

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

Each check runs in the kernel at the default fuel.  It states the verdict,
that the tank ends unmarked, and the units used, so it holds at every fuel
that covers those units.  The two loops at the end are the exception: they
end with the tank marked, the recursion limit. -/

section SubChecks

open Paths.DotMNF.Examples

/-- `x : {val a : ⊤}`, `y : x.type`. -/
def SgCtx : Ctx ([],x,x) := (Ctx.nil.cons (.vfld la .top)).cons (.sngl (.var .here))

/-- `x0 : {A : ⊥..⊤}` and `xk : {A : x(k-1).A .. x(k-1).A}` for `k = 1..n`. -/
def chainCtx : (n : Nat) → Ctx (sigN (n + 1))
  | 0 => Ctx.nil.cons (.typ lA .bot .top)
  | n + 1 => (chainCtx n).cons (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA))

/-- `x0`, seen from the end of a chain of `n` links. -/
def chainFirst : (n : Nat) → BVar (sigN (n + 1)) .var
  | 0 => .here
  | n + 1 => .there (chainFirst n)

/-- `xn.A`, the last selection of the chain. -/
def chainTop (n : Nat) : Ty (sigN (n + 1)) := .sel (.var .here) lA

/-- `x0.A`, the first selection of the chain. -/
def chainBot (n : Nat) : Ty (sigN (n + 1)) := .sel (.var (chainFirst n)) lA

/-- `μ(s. {A : ⊥..⊤} ∧ {a : {b : ⊤} ∧ {v : ⊤}})`. -/
def MuWide : Ty [] := .mu (.and (.typ lA .bot .top) (.fld la (.and (.fld lb .top) (.fld lv .top))))

/-- `μ(s. {a : {b : ⊤}})`. -/
def MuNarrow : Ty [] := .mu (.fld la (.fld lb .top))

/-- `∀(y : {A : ⊥..{a : ⊤}}) y.A`. -/
def AllSel : Ty [] := .all (.typ lA .bot (.fld la .top)) (.sel (.var .here) lA)

/-- `∀(y : {A : ⊥..{a : ⊤}}) {a : ⊤}`. -/
def AllFld : Ty [] := .all (.typ lA .bot (.fld la .top)) (.fld la .top)

/-- `p : μ(s. {A : ⊥..∀(y : ⊤) s.A})`, `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`.  No
derivation of `p.A <: q.B` exists. -/
def LPCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.mu (.typ lA .bot (.all .top (.sel (.var (.there .here)) lA))))).cons
    (.mu (.typ lB (.all .top (.sel (.var (.there .here)) lB)) .top))

/-- `p.A`. -/
def LPLeft : Ty ([],x,x) := .sel (.var (.there .here)) lA

/-- `q.B`. -/
def LPRight : Ty ([],x,x) := .sel (.var .here) lB

/-- The members of `y : k.D`, under the outer self `s` and the inner self `t`:
`{C : s.D .. s.D} ∧ {B : ⊥ .. ∀(y : t.C) y.B} ∧ {T : ∀(y : t.C) y.T .. ⊤}`. -/
def LPdBody : Ty ([],x,x) :=
  .and (.typ lC (.sel (.var (.there .here)) lA) (.sel (.var (.there .here)) lA))
    (.and (.typ lB .bot (.all (.sel (.var .here) lC) (.sel (.var .here) lB)))
          (.typ lT (.all (.sel (.var .here) lC) (.sel (.var .here) lT)) .top))

/-- `k : μ(s. {A : ⊥ .. μ(t. LPdBody)})`. -/
def LPdCtx : Ctx ([],x) := Ctx.nil.cons (.mu (.typ lA .bot (.mu LPdBody)))

/-- `∀(y : k.A) y.B`. -/
def LPdLeft : Ty ([],x) := .all (.sel (.var .here) lA) (.sel (.var .here) lB)

/-- `∀(y : k.A) y.T`. -/
def LPdRight : Ty ([],x) := .all (.sel (.var .here) lA) (.sel (.var .here) lT)

-- E6: `Int <: x.T` at the self binder, the member read through `μ`.
example : answers (sub? E6Ctxz E6Int (.sel (.var .here) lT)) 12 = true := by decide +kernel
-- E8: `x.A <: {a : ⊤}` through the upper bound.  The converse fails, the lower bound is `⊥`.
example : answers (sub? E8Ctx2 (.sel (.var (.there .here)) lA) (.fld la .top)) 4 = true := by
  decide +kernel
example : rejects (sub? E8Ctx2 (.fld la .top) (.sel (.var (.there .here)) lA)) 2 = true := by
  decide +kernel
-- E9: `y.B <: N` under `y : q.type`, the member of `q` read through the singleton.
example : answers (sub? E9_Γ4 (.sel (.var (.there .here)) lB) E9_N) 9 = true := by decide +kernel
-- X1: `x.c.A <: x.B` and back, at a path of length two.
example : answers (sub? X1_Ctx (.sel (.sel (.var .here) X1_lc) lA) (.sel (.var .here) lB)) 12 =
    true := by decide +kernel
example : answers (sub? X1_Ctx (.sel (.var .here) lB) (.sel (.sel (.var .here) X1_lc) lA)) 15 =
    true := by decide +kernel
-- E2p: the argument of `f f`, `f`'s type below `x.c.A`.
example : answers (sub? E2p_Γ3 (E2p_Γ3.lookup .here) (E2p_xcA (.there (.there .here)))) 15 =
    true := by decide +kernel
-- X3: path goals under `x : {val a : {val b : ⊤}}`, `y : (x.a).type`.
example : answers (path? X3_CtxY (.var .here) (.sngl (.var .here))) 1 = true := by decide +kernel
example : answers (path? X3_CtxY (.var .here) (.sngl (.sel (.var (.there .here)) la))) 1 = true := by
  decide +kernel
example : answers (path? X3_CtxY (.sel (.var (.there .here)) la) (.fld lb .top)) 7 = true := by
  decide +kernel
example : answers (path? X3_CtxY (.var .here) (.vfld lb .top)) 4 = true := by decide +kernel
example : answers (path? X3_CtxY (.sel (.var .here) lb) .top) 6 = true := by decide +kernel

-- E3s: `{b : ⊤} <: x.A` and `x.A <: {a : ⊤}`, each through one of the two members.
example : answers (sub? E3Ctx2 E3T2 (.sel (.var (.there .here)) lA)) 8 = true := by decide +kernel
example : answers (sub? E3Ctx2 (.sel (.var (.there .here)) lA) E3T1) 8 = true := by decide +kernel

-- Two recursive types through the abstract view, and a stable field below a field.
example : answers (sub? .nil MuWide MuNarrow) 6 = true := by decide +kernel
example : answers (sub? .nil (Ty.mu (.vfld la .top)) (.mu (.fld la .top))) 1 = true := by
  decide +kernel
example : rejects (sub? .nil (Ty.mu (.fld la .top)) (.mu (.vfld la .top))) 1 = true := by
  decide +kernel
-- Two function types, the codomain compared under the new binder.
example : answers (sub? .nil AllSel AllFld) 9 = true := by decide +kernel

-- The singleton alternatives in `x : {val a : ⊤}`, `y : x.type`.  `y.a : (x.a).type` by the
-- prefix, `x : y.type` by symmetry, `y : {a : ⊤}` by widening `y`'s singleton.
example : answers (path? SgCtx (.sel (.var .here) la) (.sngl (.sel (.var (.there .here)) la))) 9 =
    true := by decide +kernel
example : answers (path? SgCtx (.var (.there .here)) (.sngl (.var .here))) 4 = true := by
  decide +kernel
example : answers (path? SgCtx (.var .here) (.fld la .top)) 10 = true := by decide +kernel
-- The term `x` at `y.type`, through `HasTy.sngl`.  The term `y` is not widened through its
-- singleton, since `HasTy` has no rule for it.
example : answers (var? SgCtx (.there .here) (.sngl (.var .here))) 7 = true := by decide +kernel
example : rejects (var? SgCtx .here (.vfld la .top)) 3 = true := by decide +kernel

-- A member read through 6, 12, 16 and 32 singletons.
example : answers (sub? (aliasCtx 6) (.sel (.var .here) lA) (.fld la .top)) 31 = true := by
  decide +kernel
example : answers (sub? (aliasCtx 12) (.sel (.var .here) lA) (.fld la .top)) 94 = true := by
  decide +kernel
example : answers (sub? (aliasCtx 16) (.sel (.var .here) lA) (.fld la .top)) 156 = true := by
  decide +kernel
example : answers (sub? (aliasCtx 32) (.sel (.var .here) lA) (.fld la .top)) 564 = true := by
  decide +kernel
-- A member 6 and 12 stable fields down, and 3 down under a `∀`.
example : answers (sub? (Ctx.nil.cons (deepTy 6)) (.sel (deepPath .here 6) lA) (.fld la .top)) 10 =
    true := by decide +kernel
example : answers (sub? (Ctx.nil.cons (deepTy 12)) (.sel (deepPath .here 12) lA) (.fld la .top))
    16 = true := by decide +kernel
example : answers (sub? .nil (.all (deepTy 3) (.sel (deepPath .here 3) lA))
    (.all (deepTy 3) (.fld la .top))) 12 = true := by decide +kernel
-- Selection chains of 16 and 32 links.
example : answers (sub? (chainCtx 16) (chainTop 16) (chainBot 16)) 185 = true := by decide +kernel
example : answers (sub? (chainCtx 32) (chainTop 32) (chainBot 32)) 625 = true := by decide +kernel

-- MuS: `p.A <: {B : p.C .. p.C}` under `p : q.type`, with `q`'s self type opened at `p`.
example : answers (sub? MuSCtx (.sel (.var .here) lA)
    (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))) 17 = true := by decide +kernel
-- MuP: `p : {a : p.A}` under `p : q.type`, opened at `p` as well.
example : answers (path? MuPCtx (.var .here) (.fld la (.sel (.var .here) lA))) 19 = true := by
  decide +kernel

-- E1, E1p, E3 and E4 as written are rejected with the tank unmarked, as scalac rejects them.
example : rejects (sub? E1Ctx E1Dom E1Res) 1 = true := by decide +kernel
example : rejects (var? E1Ctx .here E1Res) 3 = true := by decide +kernel
example : rejects (sub? E1p_Ctx1 E1p_Dom E1p_Res) 1 = true := by decide +kernel
example : rejects (sub? E3Ctx2 E3T2 E3T1) 1 = true := by decide +kernel
example : rejects (sub? E4Ctx4 E4Int (.sel (.var (.there (.there .here))) lA)) 2 = true := by
  decide +kernel
example : rejects (var? E4Ctx4 (.there .here) (.sel (.var (.there (.there .here))) lA)) 5 = true := by
  decide +kernel

-- LP reaches its goal again under each new binder of a `∀` body.  LPd does the same with goals
-- that mention the newest binder.  Both end with the tank marked.
example : (sub? LPCtx LPLeft LPRight).2.out = true := by decide +kernel
example : (sub? LPdCtx LPdLeft LPdRight).2.out = true := by decide +kernel

end SubChecks

end PathsFrontend.Core
