import Coercions.Oopsla16.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# Inference of self types

The typer of `Typer.lean` takes a literal without a written self type only when
every method of the literal is annotated, since it reads the self type off the
members (`selfOf?`).  This module writes a self type into every other literal
(`fillF`) and hands the filled term to the typer, on the same tank.  The fill
changes no other part of the term, so the filled term erases to the input
(`fills_erase` of `Ann.lean`).  The derivation is the typer's on the filled
term, with `T_Obj` at every literal.

## The rule of empty slots

`fillF` first asks `ATm.landed`.  A term the typer takes as it is comes back
unchanged and draws nothing.  So a program the typer types elaborates as the
typer types it, with the same derivations and the same tank (`elabF_landed`,
`elabChkF_landed`).  A term the typer does not take as it is gets no candidate
from the typer at all (`synthF_unlanded`, `checkF_unlanded`), so no program
the typer accepts changes its verdict.

## Where a goal reaches a literal

- An ascription `(t : T)` gives `T` to `t`, as `Typer.typedTyped` does.
- A call argument `t.l(u)` gives `u` the dominant formal: the parameter type of
  one of the method types the lookup finds at `l` for the receiver, with every
  other one below it by the subtyping goal.  Several method types at one label
  come from an intersection, and the compiler types the argument against the
  union of their formals.  The dominant formal is that union when the formals
  are ordered.  No dominant formal leaves the argument without a goal.
- A method body gets the method's declared result, as `Typer.typedDefDef`
  types the right side against the result type.
- A receiver gets no goal, as `SelectionProto` is no type.

A goal site first fills its term at the goal and checks the filled term
against it.  If that fails with the tank unmarked, it fills the term with no
goal, and the typer then synthesizes and subsumes.  So a goal never loses a
program that types without it.

## The members a goal declares

A goal is the parent of the literal, as `Typer.typedNew` takes `pt` as the
parent of an anonymous class.  It is first dealiased: a selection whose member
has equal bounds is replaced by the bound, to a fixpoint, and each side of an
intersection is dealiased, as `strippedDealias` follows every alias.  A goal
`μ(z. B)` is opened at the literal's own self, any other goal is weakened past
it (`openGoal`).  Its declarations at a label meet, as `Type.findFunctionType`
meets two function types.  Two domains that the subtyping goal orders give the
larger one, two that it does not give their union, and the results meet.  An
abstract selection whose upper bound declares the method is a type mismatch.

## The heads of the members

A literal without a self type gets one from its members (`headsOf`).  A type
member is known at its right side.  A method takes its written parameter type,
else the goal's.  A method with neither is the compiler's missing parameter
type.  A method takes its written result type, else the goal's when the goal
declares the method at the same parameter type, compared both ways by the
subtyping goal, as `Namer.inferredResultType` takes `inherited`.  The self type
is the member list read in lockstep (`fullSelf`), the shape `D_Nil`, `D_Typ`
and `D_Fun` conclude.

## Results on demand

A method whose result is neither written nor inherited is a job (`jobsF`), as
`Namer.inferredResultType` types the right side of such a method ahead.  The
jobs are typed in rounds (`roundsF`).  A round takes a snapshot of the self
type known so far (`probeSelf`) and types every ready job once, its body filled
with no goal and synthesized by the typer, with the self bound at the snapshot
and the parameter at its type.  A job is ready when none of the methods it
calls on the self is pending.  A job that uses the self any other way is typed
in the first round in which no ready job lacks such a use, so such jobs do not
see one another.  A body's result is its least candidate (`leastCandF`), and
candidates with no least one are ambiguous.  A round that types nothing stops
with the cyclic reference `cycleAt` names, the member the walk of first pending
calls reaches again, as `SymDenotation.completeFrom` does.  `formSelfF` runs
the rounds and reads the self type in lockstep.

The literal clause of `fillF` runs the rounds on a literal whose self type
`selfOf?` does not compute.  It then fills the members against the formed self
type.  A method typed in a round takes the body its round filled.  Any other
method body is filled at its declared result.  The typer then checks the filled
literal in the real context, with the self at the formed type, so the
derivation is the typer's, with `T_Obj` at the literal.  Each body is filled
once and checked once more by the typer, so nested literals cost fuel that
grows with the square of their depth.

## Reasons

A rejection reports the recursion limit when the tank ended marked, else the
reason the fill gave, else a mismatch (`elabTopF`).

## The theorems

`fillF_landed`, `elabF_landed`, `elabChkF_landed` and `elabF_landed_tank` say
that a term the typer takes as it is elaborates as the typer types it, at the
same fuel.  `synthF_unlanded`, `checkF_unlanded` and `checkDmsF_unlanded` say
that the typer gives no answer to any other term, and `synthF_cons_landed`
that a term with a candidate is one it takes.  So inference changes no verdict
of the typer.  `dealiasF_framed`, `dealiasAt_framed` and `argGoalF_framed` say
that dealiasing and the goal of a call argument keep a marked tank, never add
fuel, and do the same with more fuel.  `argGoal_dominant` says that the goal
of a call argument is one of the formals and that every formal is below it.

`headsOf_param`, `headsOf_written` and `headsOf_typ` say what the head at each
label is.  A method without a parameter type takes the one the goal gives.
`missingParam_iff` says that the fill reports a missing parameter type at a
label exactly when the method there has none, the goal declares no method
there, and every member below it has a head.  `fullSelf_lockstep` says that
the self type formed from the heads is in lockstep with the members, in the
shape `D_Nil`, `D_Typ` and `D_Fun` conclude.  `fullSelf_selfOf` says that for
a literal whose methods are all annotated it is the self type `selfOf?`
computes, so inference extends the typer's own reading.

`leastCand_least` says that the least candidate is a candidate whose type is
below the type of every candidate, and `runJobF_least` that a typed job's
result is that type for its filled body.  `roundsF_framed` and
`formSelfF_framed` say that the rounds keep a marked tank, never add fuel, and
do the same with more fuel, when every job does.  `picks_plain`, `picks_bare`
and `picks_nil_iff` state the order of the rounds.  `cycleAt_onCycle` says that
the cyclic reference names a pending method whose walk comes back to it, and
`stallReason_cyclic` that a round that types nothing always reports one.
`jobsF_member`, `jobsF_lbls` and `jobsF_written` say that the jobs are the
methods whose result is pending, each with its body and its head, and that a
literal with every result written has none.  `formSelfF_jobs` says that rounds
that end on these jobs form a self type in lockstep with the members, and
`formSelfF_nil` that with no job the rounds draw nothing.

`fillF_framed`, `elabF_framed` and `elabChkF_framed` say that the fill and the
elaborator keep a marked tank, never add fuel, and do the same with more fuel.
`fillF_fills` says that a term the fill returns fills its input, so it erases
to it (`fills_erase`), and that the typer takes it as it is.  `elabF_fills` and
`elabChkF_fills` add that the answer is the typer's on that term.
`synthF_obj_head` says that every candidate the typer gives a literal ends in
`T_Obj`, and `obj_none_landed` that a literal without a self type elaborates
to a literal the typer takes, so its derivation ends there.
-/

namespace Oopsla16Frontend

open Frontend.Fuel Frontend.Reason Oopsla16Frontend.Core
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Tm Dm Dms Ctx Store Stp HasType DmsHasType EqSome renameUpTo)

/-- Why a program is rejected.  Oopsla16 names a method by its label, and its
typer has no reasons of its own. -/
abbrev EReason := Reason Lb Empty

/-- An answer of the fill: the filled term, or the reason it stopped. -/
abbrev FillR (α : Type) := Except EReason α

/-- The value at a label in an association list. -/
def lookupL {β : Type} : List (Lb × β) → Lb → Option β
  | [], _ => none
  | (b, v) :: l, a => if a = b then some v else lookupL l a

/-! ## Combinators -/

/-- The answer `a` with the tank marked: the recursion limit. -/
def markAs {α : Type} (a : α) : Fu α := fun t => (a, { t with out := true })

/-- Run the fallback `b` unless the tank is marked.  A fallback that fails
keeps the answer of the attempt, the first in search order. -/
def retryF {α : Type} (first : FillR α) (b : Fu (FillR α)) : Fu (FillR α) := fun t =>
  if t.out then (first, t)
  else
    match b t with
    | (.ok a, t') => (.ok a, t')
    | (.error _, t') =>
        match first with
        | .ok a => (.ok a, t')
        | .error e0 => (.error e0, t')

/-! ## Dealiasing a goal -/

/-- The upper bound of the first member with equal bounds, an alias. -/
def aliasOf {s : Sig} {Γ : Ctx [] s} {y : BVar s .var} {L : Lb} :
    List (TyMem Γ y L) → Option (Ty [] s)
  | [] => none
  | m :: ms => if m.1 = m.2.1 then some (m.2.1.rename (renameUpTo y)) else aliasOf ms

/-- A goal with its aliases followed, at the head and in each side of an
intersection, with `rec` for the type an alias stands for. -/
def dealiasTy {s : Sig} (Γ : Ctx [] s) (rec : Ty [] s → Fu (Ty [] s)) : Ty [] s → Fu (Ty [] s)
  | .TSel (.abs y) L =>
      Fu.bind (members Γ y L) fun ms =>
        match aliasOf ms with
        | some T => rec T
        | none => Fu.ret (.TSel (.abs y) L)
  | .TAnd A B =>
      Fu.bind (dealiasTy Γ rec A) fun A' => Fu.bind (dealiasTy Γ rec B) fun B' => Fu.ret (.TAnd A' B')
  | .TSel (.conc c) L => Fu.ret (.TSel (.conc c) L)
  | .TBot => Fu.ret .TBot
  | .TTop => Fu.ret .TTop
  | .TFun l S U => Fu.ret (.TFun l S U)
  | .TTyp l S U => Fu.ret (.TTyp l S U)
  | .TBind B => Fu.ret (.TBind B)
  | .TOr A B => Fu.ret (.TOr A B)

/-- A goal with at most `d` aliases followed along each path.  One more marks
the tank. -/
def dealiasF {s : Sig} (Γ : Ctx [] s) : Nat → Ty [] s → Fu (Ty [] s)
  | 0, G => dealiasTy Γ markAs G
  | d + 1, G => dealiasTy Γ (dealiasF Γ d) G

/-- A goal dealiased from the fuel left.  Every alias followed draws at least
one unit, so the index never runs out first. -/
def dealiasAt {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) : Fu (Ty [] s) := fun t =>
  dealiasF Γ t.left G t

/-! ## The members a goal declares -/

/-- A goal seen from the literal's self.  The body of a recursive goal is
opened at the self, any other goal is weakened past it, and the sides of an
intersection are read alike. -/
def openGoal {s : Sig} : Ty [] s → Ty [] (s,x)
  | .TBind B => B
  | .TAnd A B => .TAnd (openGoal A) (openGoal B)
  | G => G.weaken

/-- The method types a type declares at the label `l`, in its intersection
spine, left to right. -/
def declsIn {s : Sig} (l : Lb) : Ty [] s → List (Ty [] s × Ty [] (s,x))
  | .TFun l' S U => if l' = l then [(S, U)] else []
  | .TAnd A B => declsIn l A ++ declsIn l B
  | _ => []

/-- Whether an abstract selection of the goal has an upper bound that declares
a method at `l`.  The compiler reports a type mismatch there. -/
def abstractDeclF {s : Sig} (Γ : Ctx [] s) (l : Lb) : Ty [] s → Fu Bool
  | .TSel (.abs y) L =>
      Fu.bind (members Γ y L) fun ms =>
        Fu.ret (ms.any fun m => !(declsIn l (openGoal (m.2.1.rename (renameUpTo y)))).isEmpty)
  | .TAnd A B =>
      Fu.bind (abstractDeclF Γ l A) fun b => if b then Fu.ret true else abstractDeclF Γ l B
  | _ => Fu.ret false

/-- What a goal says of the method at a label. -/
inductive MPart (s : Sig) where
  /-- No declaration. -/
  | none
  /-- The parameter type `S` and the result type `U`. -/
  | one (S : Ty [] s) (U : Ty [] (s,x))
  /-- A declaration the version cannot give, a type mismatch. -/
  | bad
deriving DecidableEq

/-- The meet of two results: one of them when they are equal. -/
def meetRes {s : Sig} (U1 U2 : Ty [] (s,x)) : Ty [] (s,x) :=
  if U1 = U2 then U1 else .TAnd U1 U2

/-- One more declaration `(S, U)` met with the part read so far.  Two domains
the subtyping goal orders give the larger, two it does not order give their
union.  The results meet. -/
def meetOneF {s : Sig} (Γ : Ctx [] s) (S : Ty [] s) (U : Ty [] (s,x)) : MPart s → Fu (MPart s)
  | .none => Fu.ret (.one S U)
  | .bad => Fu.ret .bad
  | .one S2 U2 =>
      if S = S2 then Fu.ret (.one S (meetRes U U2))
      else
        Fu.bind (subF Γ S2 S) fun o =>
          match o with
          | some _ => Fu.ret (.one S (meetRes U U2))
          | none =>
              Fu.bind (subF Γ S S2) fun o' =>
                match o' with
                | some _ => Fu.ret (.one S2 (meetRes U U2))
                | none => Fu.ret (.one (.TOr S S2) (meetRes U U2))

/-- The meet of a list of declarations. -/
def meetAllF {s : Sig} (Γ : Ctx [] s) : List (Ty [] s × Ty [] (s,x)) → Fu (MPart s)
  | [] => Fu.ret .none
  | (S, U) :: rest => Fu.bind (meetAllF Γ rest) fun p => meetOneF Γ S U p

/-- What the dealiased goal `G` declares at `l`, seen from the literal's self.
The domains are compared with the self at the opened goal. -/
def partF {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (l : Lb) : Fu (MPart (s,x)) :=
  Fu.bind (abstractDeclF Γ l G) fun b =>
    if b then Fu.ret .bad else meetAllF (Γ.cons (openGoal G)) (declsIn l (openGoal G))

/-- What a goal says of one method: its part, and whether the method's written
parameter type is the part's domain both ways. -/
structure Inherit (s : Sig) where
  /-- The goal's declaration at the method's label. -/
  part : MPart s
  /-- The written parameter type and the goal's domain are below each other. -/
  same : Bool

/-- Whether a written parameter type is the domain of the part, both ways by
the subtyping goal. -/
def sameDomF {s : Sig} (Γ : Ctx [] s) : Option (Ty [] s) → MPart s → Fu Bool
  | some S, .one S' _ =>
      if S = S' then Fu.ret true
      else
        Fu.bind (subF Γ S S') fun o =>
          match o with
          | some _ => Fu.bind (subF Γ S' S) fun o' => Fu.ret o'.isSome
          | none => Fu.ret false
  | _, _ => Fu.ret false

/-- What a goal says of each method of a member list that lacks an
annotation, by label.  `part` reads the goal at a label, and `Γ` binds the self
at the opened goal. -/
def inheritF {s : Sig} (Γ : Ctx [] s) (part : Lb → Fu (MPart s)) :
    ADms s → Fu (List (Lb × Inherit s))
  | .dnil => Fu.ret []
  | .dcons (.dty _) ds => inheritF Γ part ds
  | .dcons (.dfun o1 o2 _) ds =>
      Fu.bind (inheritF Γ part ds) fun rest =>
        if o1.isSome && o2.isSome then Fu.ret rest
        else
          Fu.bind (part ds.length) fun p =>
            Fu.bind (sameDomF Γ o1 p) fun b =>
              Fu.ret ((ds.length, ⟨p, b⟩) :: rest)

/-- What the goal of a literal says of its methods: nothing without a goal,
else the reading of the dealiased goal. -/
def readGoalF {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) (ds : ADms (s,x)) :
    Fu (List (Lb × Inherit (s,x))) :=
  match g with
  | none => Fu.ret []
  | some G => Fu.bind (dealiasAt Γ G) fun G' => inheritF (Γ.cons (openGoal G')) (partF Γ G') ds

/-- The parameter type the goal gives the method at `l`: the domain of its
declaration there.  An abstract declaration is a mismatch. -/
def paramFrom {s : Sig} (rd : List (Lb × Inherit s)) (l : Lb) : FillR (Option (Ty [] s)) :=
  match lookupL rd l with
  | some ⟨.one S _, _⟩ => .ok (some S)
  | some ⟨.bad, _⟩ => .error .mismatch
  | _ => .ok none

/-- The result type the goal gives the method at `l` with parameter type `S`:
the result of its declaration there, when the declaration's domain is `S`, or
when the written parameter type is that domain both ways. -/
def resultFrom {s : Sig} (rd : List (Lb × Inherit s)) (l : Lb) (S : Ty [] s) :
    Option (Ty [] (s,x)) :=
  match lookupL rd l with
  | some ⟨.one S' U, b⟩ => if b || decide (S' = S) then some U else none
  | _ => none

/-! ## The heads of the members -/

/-- A member's head: a type member's alias, or a method's parameter type with
its result type when it is known. -/
inductive Head (s : Sig) where
  /-- `type = T`. -/
  | typ (T : Ty [] s)
  /-- A method with its parameter type, and its result type if it is known. -/
  | fn (S : Ty [] s) (U : Option (Ty [] (s,x)))
deriving DecidableEq

/-- The heads of a member list, newest member first, each at its label.  A
type member is known at its right side (`TypeDefCompleter.typeSig`).  A method
takes its written types (`valOrDefDefSig`), else the goal's.  A parameter with
neither is the compiler's missing parameter type. -/
def headsOf {s : Sig} (pf : Lb → FillR (Option (Ty [] s)))
    (rf : Lb → Ty [] s → Option (Ty [] (s,x))) : ADms s → FillR (List (Lb × Head s))
  | .dnil => .ok []
  | .dcons (.dty T) ds =>
      match headsOf pf rf ds with
      | .ok hs => .ok ((ds.length, .typ T) :: hs)
      | .error r => .error r
  | .dcons (.dfun o1 o2 _) ds =>
      match headsOf pf rf ds with
      | .error r => .error r
      | .ok hs =>
          match o1 with
          | some S => .ok ((ds.length, .fn S (o2.or (rf ds.length S))) :: hs)
          | none =>
              match pf ds.length with
              | .error r => .error r
              | .ok none => .error (.missingParamType (some ds.length))
              | .ok (some S) => .ok ((ds.length, .fn S (o2.or (rf ds.length S))) :: hs)

/-- The self type the members have so far: every member whose type is known.
A method whose result is pending is left out. -/
def probeSelf {s : Sig} (hs : List (Lb × Head s)) (known : List (Lb × Ty [] (s,x))) : Ty [] s :=
  match hs with
  | [] => .TTop
  | (l, .typ T) :: hs' => .TAnd (.TTyp l T T) (probeSelf hs' known)
  | (l, .fn S (some U)) :: hs' => .TAnd (.TFun l S U) (probeSelf hs' known)
  | (l, .fn S none) :: hs' =>
      match lookupL known l with
      | some U => .TAnd (.TFun l S U) (probeSelf hs' known)
      | none => probeSelf hs' known

/-- The self type in lockstep with the members, once every result is known:
the shape `D_Nil`, `D_Typ` and `D_Fun` conclude and `checkDmsF` reads.
`known` holds the results found by typing bodies. -/
def fullSelf {s : Sig} (hs : List (Lb × Head s)) (known : List (Lb × Ty [] (s,x))) :
    Option (Ty [] s) :=
  match hs with
  | [] => some .TTop
  | (l, .typ T) :: hs' => (fullSelf hs' known).map (.TAnd (.TTyp l T T))
  | (l, .fn S (some U)) :: hs' => (fullSelf hs' known).map (.TAnd (.TFun l S U))
  | (l, .fn S none) :: hs' =>
      match lookupL known l with
      | some U => (fullSelf hs' known).map (.TAnd (.TFun l S U))
      | none => none

/-! ## The goal of a call argument -/

/-- The parameter types of the method types at `l` that the lookup finds for
each candidate of the receiver `t`. -/
def formalsF {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) : Fu (List (Ty [] s)) :=
  Fu.bind (synthF Γ t) fun cts =>
    Fu.flatMapL (fun ct => Fu.bind (cands Γ l t ct) fun cs => Fu.ret (cs.map (·.dom))) cts

/-- Every type of the list is `F` or below it by the subtyping goal. -/
def allBelowF {s : Sig} (Γ : Ctx [] s) (F : Ty [] s) : List (Ty [] s) → Fu Bool
  | [] => Fu.ret true
  | F' :: Fs =>
      if F' = F then allBelowF Γ F Fs
      else
        Fu.bind (subF Γ F' F) fun o =>
          match o with
          | some _ => allBelowF Γ F Fs
          | none => Fu.ret false

/-- The first type of `cands` that every type of `Fs` is below. -/
def dominantF {s : Sig} (Γ : Ctx [] s) (Fs : List (Ty [] s)) : List (Ty [] s) → Fu (Option (Ty [] s))
  | [] => Fu.ret none
  | F :: rest =>
      Fu.bind (allBelowF Γ F Fs) fun b => if b then Fu.ret (some F) else dominantF Γ Fs rest

/-- The goal of the argument of a call `t.l(·)`: the dominant formal.  `none`
when the receiver has no method type at `l` or no formal is dominant. -/
def argGoalF {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) : Fu (Option (Ty [] s)) :=
  Fu.bind (formalsF Γ t l) fun Fs => dominantF Γ Fs Fs

/-! ## Results on demand

A method whose result is neither written nor inherited gets the type of its
body, as `Namer.inferredResultType` types the right side ahead.  Such a method
is a job.  The jobs are typed in rounds against a snapshot of the self type,
and a round that types nothing stops at the compiler's cyclic reference. -/

/-- A filled term with the typer's candidates for it. -/
abbrev Filled {s : Sig} (Γ : Ctx [] s) : Type := (a : ATm s) × List (Cand Γ a.erase)

/-- A method whose result is typed from its body.  `s` is the scope of the
members, with the self innermost. -/
structure Job (s : Sig) where
  /-- The method's label. -/
  lbl : Lb
  /-- Its parameter type, written or taken from the goal. -/
  par : Ty [] s
  /-- Its body, under the parameter. -/
  tm : ATm (s,x)
  /-- The body filled with no goal and synthesized by the typer, in a context
  that binds the parameter. -/
  run : (Γ : Ctx [] (s,x)) → Fu (FillR (Filled Γ))

/-- The dependencies of a job's body on the self, the variable just outside
the parameter: the labels it calls on the self, and whether it uses the self
any other way. -/
def Job.deps {s : Sig} (j : Job (s,x)) : List Lb × Bool := j.tm.deps (.there .here)

/-- A typed job: its label, its body, the filled body, and the result type the
rounds chose. -/
structure Done (s : Sig) where
  /-- The method's label. -/
  lbl : Lb
  /-- The body. -/
  tm : ATm (s,x)
  /-- The filled body. -/
  a : ATm (s,x)
  /-- The result type, the least candidate of the filled body. -/
  ty : Ty [] (s,x)

/-- The first typed job at a label, the entry whose result `Done.known` gives
there. -/
def lookupDone {s : Sig} : List (Done s) → Lb → Option (Done s)
  | [], _ => none
  | e :: es, l => if e.lbl = l then some e else lookupDone es l

/-- The results typed so far, by label. -/
def Done.known {s : Sig} (ds : List (Done s)) : List (Lb × Ty [] (s,x)) :=
  ds.map fun e => (e.lbl, e.ty)

/-! ### The least candidate

A body's result is the least type of its candidates: the type of the first
candidate that is below every other one by the subtyping goal.  Every candidate
is a type of the body, so a use that needs another one reaches it by
subsumption, and the choice does not depend on the order of an intersection.
The compiler meets the candidates with `Denotation.meet`, which the version
cannot derive for a term that is not a variable.  So candidates with no least
one are rejected as ambiguous. -/

/-- `T` is below every type of the list, or equal to it. -/
def belowAllF {s : Sig} (Γ : Ctx [] s) (T : Ty [] s) : List (Ty [] s) → Fu Bool
  | [] => Fu.ret true
  | U :: Us =>
      if T = U then belowAllF Γ T Us
      else
        Fu.bind (subF Γ T U) fun o =>
          match o with
          | some _ => belowAllF Γ T Us
          | none => Fu.ret false

/-- The first candidate of the list whose type is below every type of `Ts`. -/
def leastFromF {s : Sig} (Γ : Ctx [] s) {t : Tm [] s} (Ts : List (Ty [] s)) :
    List (Cand Γ t) → Fu (Option (Cand Γ t))
  | [] => Fu.ret none
  | c :: rest =>
      Fu.bind (belowAllF Γ c.ty Ts) fun b => if b then Fu.ret (some c) else leastFromF Γ Ts rest

/-- The least candidate: the first one whose type is below the type of every
candidate. -/
def leastCandF {s : Sig} (Γ : Ctx [] s) {t : Tm [] s} (cs : List (Cand Γ t)) :
    Fu (Option (Cand Γ t)) :=
  leastFromF Γ (cs.map (·.ty)) cs

/-! ### Rounds

A round takes a snapshot of the self type known so far (`probeSelf`) and types
every ready job once, with the self bound at the snapshot.  A job is ready
when none of the methods it calls on the self is pending.  A job that uses the
self any other way waits for the first round in which no ready job lacks such
a use.  So a method that returns the self is typed before the methods that call
it, two such methods do not see each other, and a pending method is missing
from the snapshot its own body sees.  The number of rounds is an index, so the
rounds are structural. -/

/-- A job is ready when none of the methods it calls on the self is
pending. -/
def readyIn {s : Sig} (pend : List Lb) (j : Job (s,x)) : Bool :=
  j.deps.1.all fun l => !pend.contains l

/-- Whether a round types the jobs that use the self bare: when no ready job
lacks such a use. -/
def bareRound {s : Sig} (js : List (Job (s,x))) : Bool :=
  !(js.any fun j => readyIn (js.map (·.lbl)) j && !j.deps.2)

/-- Whether a round over the pending jobs `js` types `j`: it is ready, and it
uses the self bare exactly when the round types such jobs. -/
def picks {s : Sig} (js : List (Job (s,x))) (j : Job (s,x)) : Bool :=
  readyIn (js.map (·.lbl)) j && decide (j.deps.2 = bareRound js)

/-- A job typed against the snapshot `P`: its body filled and synthesized with
the self at `P` and the parameter at the job's parameter type, and its result
the least candidate.  No candidate is a mismatch, and candidates with no least
one are ambiguous. -/
def runJobF {s : Sig} (Γ : Ctx [] s) (P : Ty [] (s,x)) (j : Job (s,x)) :
    Fu (FillR (Done (s,x))) :=
  Fu.bind (j.run ((Γ.cons P).cons j.par.weaken)) fun r =>
    match r with
    | .error e => Fu.ret (.error e)
    | .ok ⟨_, []⟩ => Fu.ret (.error .mismatch)
    | .ok ⟨a, c :: cs⟩ =>
        Fu.bind (leastCandF ((Γ.cons P).cons j.par.weaken) (c :: cs)) fun o =>
          match o with
          | some e => Fu.ret (.ok ⟨j.lbl, j.tm, a, e.ty⟩)
          | none => Fu.ret (.error (.ambiguous j.lbl))

/-- One round: the jobs typed against the snapshot `P`, in source order.  The
first failure stops it. -/
def roundF {s : Sig} (Γ : Ctx [] s) (P : Ty [] (s,x)) :
    List (Job (s,x)) → Fu (FillR (List (Done (s,x))))
  | [] => Fu.ret (.ok [])
  | j :: js =>
      Fu.bind (runJobF Γ P j) fun r =>
        match r with
        | .ok e =>
            Fu.bind (roundF Γ P js) fun r' =>
              match r' with
              | .ok es => Fu.ret (.ok (e :: es))
              | .error e' => Fu.ret (.error e')
        | .error e' => Fu.ret (.error e')

/-! ### The cyclic reference

A round that types nothing has every pending job waiting for a pending method.
The walk starts at the first pending job in source order and follows the
first pending method it calls on the self, until a label repeats.  That label
is the cyclic reference, the member `SymDenotation.completeFrom` reaches again
while its completion is under way. -/

/-- The pending labels a job calls on the self, in body order. -/
def waitsFor {s : Sig} (js : List (Job (s,x))) (j : Job (s,x)) : List Lb :=
  j.deps.1.filter fun l => (js.map (·.lbl)).contains l

/-- The label the walk visits after `l`: the first pending label that the
first job at `l` waits for. -/
def nextL {s : Sig} (js : List (Job (s,x))) (l : Lb) : Option Lb :=
  match js.find? (fun j => decide (j.lbl = l)) with
  | some j => (waitsFor js j).head?
  | none => none

/-- The walk from `l`, with the labels `seen` before it, for at most `n`
steps: the first label it visits twice. -/
def cycleFrom {s : Sig} (js : List (Job (s,x))) : Nat → List Lb → Lb → Option Lb
  | 0, _, _ => none
  | n + 1, seen, l =>
      if seen.contains l then some l
      else
        match nextL js l with
        | some l' => cycleFrom js n (l :: seen) l'
        | none => none

/-- The cyclic reference among the pending jobs: the first label the walk
from the first job visits twice, within `n` steps. -/
def cycleAt {s : Sig} (js : List (Job (s,x))) (n : Nat) : Option Lb :=
  match js with
  | [] => none
  | j :: _ => cycleFrom js n [] j.lbl

/-- The label the walk reaches from `l` in `k` steps. -/
def walkL {s : Sig} (js : List (Job (s,x))) : Nat → Lb → Option Lb
  | 0, l => some l
  | k + 1, l => (nextL js l).bind (walkL js k)

/-- The walk from a job comes back to its label. -/
def OnCycle {s : Sig} (js : List (Job (s,x))) (j : Job (s,x)) : Prop :=
  ∃ k, walkL js (k + 1) j.lbl = some j.lbl

/-- The reason of a round that types nothing.  The walk visits at most one
label per job before one repeats. -/
def stallReason {s : Sig} (js : List (Job (s,x))) : EReason :=
  match cycleAt js (js.length + 1) with
  | some l => .cyclicRef l
  | none => .mismatch

/-- Rounds until every job is typed, at most `n` of them.  `hs` are the heads
of the members, which give the snapshot together with the results typed so
far, and `done` lists those results.  A round that types nothing stops with
the cyclic reference. -/
def roundsF {s : Sig} (Γ : Ctx [] s) (hs : List (Lb × Head (s,x))) :
    Nat → List (Job (s,x)) → List (Done (s,x)) → Fu (FillR (List (Done (s,x))))
  | _, [], done => Fu.ret (.ok done)
  | 0, j :: js, _ => Fu.ret (.error (stallReason (j :: js)))
  | n + 1, j :: js, done =>
      if ((j :: js).filter (picks (j :: js))).isEmpty then
        Fu.ret (.error (stallReason (j :: js)))
      else
        Fu.bind (roundF Γ (probeSelf hs (Done.known done)) ((j :: js).filter (picks (j :: js))))
          fun r =>
            match r with
            | .ok typed =>
                roundsF Γ hs n ((j :: js).filter fun k => !picks (j :: js) k) (done ++ typed)
            | .error e => Fu.ret (.error e)

/-- The self type of a literal in `Γ` formed from the heads `hs` of its
members and the jobs `js`: the rounds, then the self type in lockstep, with
the typed jobs.  A round that does not stop types at least one job, so one
round per job suffices. -/
def formSelfF {s : Sig} (Γ : Ctx [] s) (hs : List (Lb × Head (s,x))) (js : List (Job (s,x))) :
    Fu (FillR (Ty [] (s,x) × List (Done (s,x)))) :=
  Fu.bind (roundsF Γ hs (js.length + 1) js []) fun r =>
    match r with
    | .ok done =>
        Fu.ret (match fullSelf hs (Done.known done) with
          | some T => .ok (T, done)
          | none => .error .mismatch)
    | .error e => Fu.ret (.error e)

/-! ## The fill -/

/-- A goal site.  The term `a` is filled at the goal `G` by `fill (some G)`
and the filled term is checked against `G`.  If that fails with the tank
unmarked, `a` is filled with no goal.  A term the typer takes as it is comes
back unchanged. -/
def fillAtF {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (a : ATm s)
    (fill : Option (Ty [] s) → Fu (FillR (ATm s))) : Fu (FillR (ATm s)) :=
  if a.landed then Fu.ret (.ok a)
  else
    Fu.bind (fill (some G)) fun r =>
      match r with
      | .ok a' =>
          Fu.bind (checkF Γ a' G) fun o =>
            match o with
            | some _ => Fu.ret (.ok a')
            | none => retryF (.ok a') (fill none)
      | .error e => retryF (.error e) (fill none)

mutual

/-- Write a self type into every literal that lacks one and that the typer
cannot take as it is.  `g` is the goal of the term, which a literal reads as
its parent.  The self type comes from the heads of the members, and the rounds
type the methods whose result neither the program nor the goal gives. -/
def fillF {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) (a : ATm s) : Fu (FillR (ATm s)) :=
  if a.landed then Fu.ret (.ok a)
  else
    match a with
    | .var x => Fu.ret (.ok (.var x))
    | .asc t T =>
        Fu.bind (fillAtF Γ T t (fun g' => fillF Γ g' t)) fun r => Fu.ret (r.map (.asc · T))
    | .app t l u =>
        Fu.bind (fillF Γ none t) fun r =>
          match r with
          | .error e => Fu.ret (.error e)
          | .ok t' =>
              if u.landed then Fu.ret (.ok (.app t' l u))
              else
                Fu.bind (argGoalF Γ t' l) fun o =>
                  Fu.bind (match o with
                      | some F => fillAtF Γ F u (fun g' => fillF Γ g' u)
                      | none => fillF Γ none u) fun r' =>
                    Fu.ret (r'.map (.app t' l ·))
    | .obj o ds =>
        match o <|> selfOf? ds.erase with
        | some T => Fu.bind (fillDmsF (Γ.cons T) [] ds T) fun r => Fu.ret (r.map (.obj (some T) ·))
        | none =>
            Fu.bind (readGoalF Γ g ds) fun rd =>
              match headsOf (paramFrom rd) (resultFrom rd) ds with
              | .error e => Fu.ret (.error e)
              | .ok hs =>
                  Fu.bind (formSelfF Γ hs (jobsF hs ds)) fun r =>
                    match r with
                    | .error e => Fu.ret (.error e)
                    | .ok (T, done) =>
                        Fu.bind (fillDmsF (Γ.cons T) done ds T) fun r' =>
                          Fu.ret (r'.map (.obj (some T) ·))
termination_by structural a

/-- Fill the members of a literal against its self type, in lockstep.  A method
typed in a round takes the body the round filled, the entry of `done` at its
label.  That body is taken when it fills the method's body and the typer takes
it as it is.  The round's fill ensures both, and deciding them here keeps
`fillF_fills` free of any fact about the rounds.  Any other method body is
filled with the method's declared result as its goal. -/
def fillDmsF {s : Sig} (Γ : Ctx [] s) (done : List (Done s)) (ds : ADms s) (T : Ty [] s) :
    Fu (FillR (ADms s)) :=
  match ds, T with
  | .dnil, _ => Fu.ret (.ok .dnil)
  | .dcons (.dty T') ds', .TAnd _ TS =>
      Fu.bind (fillDmsF Γ done ds' TS) fun r => Fu.ret (r.map (.dcons (.dty T')))
  | .dcons (.dfun o1 o2 t) ds', .TAnd (.TFun _ T11 T12) TS =>
      Fu.bind (fillDmsF Γ done ds' TS) fun r =>
        match r with
        | .error e => Fu.ret (.error e)
        | .ok ds'' =>
            match lookupDone done ds'.length with
            | some e =>
                Fu.ret (if t.fills e.a && e.a.landed then .ok (.dcons (.dfun o1 o2 e.a) ds'')
                  else .error .mismatch)
            | none =>
                Fu.bind
                    (fillAtF (Γ.cons T11.weaken) T12 t (fun g' => fillF (Γ.cons T11.weaken) g' t))
                  fun r' => Fu.ret (r'.map fun t' => .dcons (.dfun o1 o2 t') ds'')
  | _, _ => Fu.ret (.error .mismatch)
termination_by structural ds

/-- The jobs of a member list, read in lockstep with its heads `hs`: every
method whose head has no result, in source order.  A job's body is filled with
no goal and synthesized by the typer. -/
def jobsF {s : Sig} (hs : List (Lb × Head s)) (ds : ADms s) : List (Job s) :=
  match hs, ds with
  | (l, .fn S none) :: hs', .dcons (.dfun _ _ t) ds' =>
      ⟨l, S, t, fun Γ =>
        Fu.bind (fillF Γ none t) fun r =>
          match r with
          | .ok t' => Fu.bind (synthF Γ t') fun cs => Fu.ret (.ok ⟨t', cs⟩)
          | .error e => Fu.ret (.error e)⟩ :: jobsF hs' ds'
  | _ :: hs', .dcons _ ds' => jobsF hs' ds'
  | _, _ => []
termination_by structural ds

end

/-! ## The elaborator: fill, then the typer -/

/-- A filled term with the typer's check of it at `G`. -/
abbrev FilledChk {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) : Type :=
  (a : ATm s) × Option (HasType Store.nil Γ a.erase G)

/-- Fill with no goal, then synthesize the filled term with the typer. -/
def elabF {s : Sig} (Γ : Ctx [] s) (a : ATm s) : Fu (FillR (Filled Γ)) :=
  Fu.bind (fillF Γ none a) fun r =>
    match r with
    | .ok a' => Fu.bind (synthF Γ a') fun cs => Fu.ret (.ok ⟨a', cs⟩)
    | .error e => Fu.ret (.error e)

/-- Fill at the goal `G`, then check the filled term with the typer. -/
def elabChkF {s : Sig} (Γ : Ctx [] s) (a : ATm s) (G : Ty [] s) : Fu (FillR (FilledChk Γ G)) :=
  Fu.bind (fillAtF Γ G a (fun g => fillF Γ g a)) fun r =>
    match r with
    | .ok a' => Fu.bind (checkF Γ a' G) fun o => Fu.ret (.ok ⟨a', o⟩)
    | .error e => Fu.ret (.error e)

/-- A closed program elaborated from a full tank of `n` units: the filled term
with its first candidate, or the reason.  A marked tank is the recursion
limit. -/
def elabTopF (n : Nat) (a : ATm []) : FillR ((a' : ATm []) × Cand Ctx.nil a'.erase) × Tank :=
  match elabF Ctx.nil a ⟨n, false⟩ with
  | (.ok ⟨a', c :: _⟩, t) => (if t.out then .error .limit else .ok ⟨a', c⟩, t)
  | (.ok ⟨_, []⟩, t) => (.error (Reason.top t.out []), t)
  | (.error e, t) => (.error (Reason.top t.out [e]), t)

/-! ## A term the typer takes is elaborated as the typer types it -/

/-- The fill returns a term the typer takes as it is, and draws nothing. -/
theorem fillF_landed {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) (a : ATm s)
    (h : a.landed = true) : fillF Γ g a = Fu.ret (.ok a) := by
  rw [fillF.eq_def]
  simp only [h, if_true]

/-- A goal site returns a term the typer takes as it is, and draws nothing. -/
theorem fillAtF_landed {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (a : ATm s)
    (fill : Option (Ty [] s) → Fu (FillR (ATm s))) (h : a.landed = true) :
    fillAtF Γ G a fill = Fu.ret (.ok a) := by
  unfold fillAtF
  simp only [h, if_true]

/-- The elaborator gives a term the typer takes as it is the typer's candidates,
on the same tank. -/
theorem elabF_landed {s : Sig} (Γ : Ctx [] s) (a : ATm s) (h : a.landed = true) :
    elabF Γ a = Fu.bind (synthF Γ a) fun cs => Fu.ret (.ok ⟨a, cs⟩) := by
  unfold elabF
  rw [fillF_landed Γ none a h]
  rfl

/-- The elaborator checks a term the typer takes as it is by the typer's check,
on the same tank. -/
theorem elabChkF_landed {s : Sig} (Γ : Ctx [] s) (a : ATm s) (G : Ty [] s) (h : a.landed = true) :
    elabChkF Γ a G = Fu.bind (checkF Γ a G) fun o => Fu.ret (.ok ⟨a, o⟩) := by
  unfold elabChkF
  rw [fillAtF_landed Γ G a _ h]
  rfl

/-- The tank after the elaboration of a term the typer takes as it is, is the
typer's tank. -/
theorem elabF_landed_tank {s : Sig} (Γ : Ctx [] s) (a : ATm s) (h : a.landed = true) (t : Tank) :
    (elabF Γ a t).2 = (synthF Γ a t).2 := by
  rw [elabF_landed Γ a h]
  rfl

/-! ## The typer rejects every term it cannot take as it is

Every clause of the typer passes an empty answer of a subterm on.  So a term
with a literal that has no self type and that `selfOf?` does not type gets no
candidate and no check, whatever the tank. -/

theorem flatMapL_nil_fst {α β : Type} (f : α → Fu (List β)) (hf : ∀ x t, (f x t).1 = [])
    (xs : List α) (t : Tank) : (Fu.flatMapL f xs t).1 = [] := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
      simp only [Fu.flatMapL, Fu.bind, Fu.ret]
      rw [hf x t, ih]
      rfl

theorem firstSome_none_fst {α β : Type} (f : α → Fu (Option β)) (hf : ∀ x t, (f x t).1 = none)
    (xs : List α) (t : Tank) : (Fu.firstSome f xs t).1 = none := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
      simp only [Fu.firstSome, Fu.orElse]
      have hx := hf x t
      revert hx
      cases f x t with
      | mk o t1 =>
        intro hx
        simp only at hx
        subst hx
        simp only
        split
        · rfl
        · exact ih t1

theorem bindO_none_fst {α β : Type} {c : Fu (Option α)} {f : α → Fu (Option β)} {t : Tank}
    (h : (c t).1 = none) : (bindO c f t).1 = none := by
  simp only [bindO, Fu.bind]
  revert h
  cases c t with
  | mk o t1 => intro h; simp only at h; subst h; rfl

theorem bindO_right_fst {α β : Type} {c : Fu (Option α)} {f : α → Fu (Option β)}
    (hf : ∀ a t, (f a t).1 = none) (t : Tank) : (bindO c f t).1 = none := by
  simp only [bindO, Fu.bind]
  cases c t with
  | mk o t1 => cases o with
    | none => rfl
    | some a => exact hf a t1

theorem mapO_none_fst {α β : Type} {c : Fu (Option α)} {f : α → β} {t : Tank}
    (h : (c t).1 = none) : (mapO c f t).1 = none := by
  simp only [mapO, Fu.bind]
  revert h
  cases c t with
  | mk o t1 => intro h; simp only at h; subst h; rfl

/-- A literal the typer cannot take, but whose self type it finds, has a member
list the typer cannot take. -/
theorem obj_unlanded {s : Sig} {o : Option (Ty [] (s,x))} {ds : ADms (s,x)}
    (h : (ATm.obj o ds).landed = false) {T : Ty [] (s,x)} (hT : (o <|> selfOf? ds.erase) = some T) :
    ds.landed = false := by
  simp only [ATm.landed, Bool.and_eq_false_iff] at h
  rcases h with h | h
  · exfalso
    cases o with
    | some _ => simp at h
    | none =>
        simp only [Option.isSome_none, Bool.false_or] at h
        have : selfOf? ds.erase = some T := by simpa using hT
        rw [this] at h
        simp at h
  · exact h

mutual

/-- Synthesis gives no candidate to a term it cannot take as it is. -/
theorem synthF_unlanded {s : Sig} (Γ : Ctx [] s) :
    (a : ATm s) → a.landed = false → ∀ t, (synthF Γ a t).1 = []
  | .var _, h, _ => by simp [ATm.landed] at h
  | .obj o ds, h, t => by
      rw [synthF]
      cases hT : (o <|> selfOf? ds.erase) with
      | none => rfl
      | some T =>
          simp only [Fu.bind, Fu.ret]
          have hds := obj_unlanded h hT
          have := checkDmsF_unlanded (Γ.cons T) ds hds T t
          revert this
          cases checkDmsF (Γ.cons T) ds T t with
          | mk o' t1 => intro h'; simp only at h'; subst h'; rfl
  | .app u l v, h, t => by
      rw [synthF]
      simp only [ATm.landed, Bool.and_eq_false_iff] at h
      simp only [Fu.bind, Fu.ret]
      rcases h with h | h
      · have := synthF_unlanded Γ u h t
        revert this
        cases synthF Γ u t with
        | mk cts t1 =>
          intro h'; simp only at h'; subst h'
          simp only [Fu.flatMapL, Fu.ret]
          cases synthF Γ v t1 with
          | mk _ _ => rfl
      · cases synthF Γ u t with
        | mk cts t1 =>
          simp only
          have := synthF_unlanded Γ v h t1
          revert this
          cases synthF Γ v t1 with
          | mk cus t2 =>
            intro h'; simp only at h'; subst h'
            have hz := flatMapL_nil_fst (fun ct => Fu.bind (cands Γ l u ct) fun cs =>
                Fu.flatMapL (fun c => Fu.bind (argSynth Γ v [] c) fun o => Fu.ret (listO o)) cs)
              (by
                intro ct t'
                simp only [Fu.bind]
                cases cands Γ l u ct t' with
                | mk cs t'' =>
                  apply flatMapL_nil_fst
                  intro c t3
                  simp only [Fu.bind, Fu.ret]
                  cases v with
                  | var _ => simp [ATm.landed] at h
                  | obj _ _ => rfl
                  | app _ _ _ => rfl
                  | asc _ _ => rfl) cts t2
            revert hz
            cases Fu.flatMapL _ cts t2 with
            | mk rs t3 => intro hz; simp only at hz; subst hz; rfl
  | .asc a T, h, t => by
      rw [synthF]
      simp only [ATm.landed] at h
      simp only [Fu.bind, Fu.ret]
      have := checkF_unlanded Γ a T h t
      revert this
      cases checkF Γ a T t with
      | mk o t1 => intro h'; simp only at h'; subst h'; rfl

/-- Checking gives no derivation to a term it cannot take as it is. -/
theorem checkF_unlanded {s : Sig} (Γ : Ctx [] s) :
    (a : ATm s) → (T : Ty [] s) → a.landed = false → ∀ t, (checkF Γ a T t).1 = none
  | .var _, _, h, _ => by simp [ATm.landed] at h
  | .obj o ds, T, h, t => by
      rw [checkF]
      cases hT : (o <|> selfOf? ds.erase) with
      | none => rfl
      | some S =>
          exact bindO_none_fst (checkDmsF_unlanded (Γ.cons S) ds (obj_unlanded h hT) S t)
  | .app u l v, T, h, t => by
      rw [checkF]
      simp only [ATm.landed, Bool.and_eq_false_iff] at h
      simp only [Fu.bind]
      rcases h with h | h
      · have := synthF_unlanded Γ u h t
        revert this
        cases synthF Γ u t with
        | mk cts t1 =>
          intro h'; simp only at h'; subst h'
          cases synthF Γ v t1 with
          | mk _ _ => rfl
      · cases synthF Γ u t with
        | mk cts t1 =>
          simp only
          have := synthF_unlanded Γ v h t1
          revert this
          cases synthF Γ v t1 with
          | mk cus t2 =>
            intro h'; simp only at h'; subst h'
            apply firstSome_none_fst
            intro ct t3
            simp only [Fu.bind]
            cases cands Γ l u ct t3 with
            | mk cs t4 =>
              apply firstSome_none_fst
              intro c t5
              cases v with
              | var _ => simp [ATm.landed] at h
              | obj _ _ => rfl
              | app _ _ _ => rfl
              | asc _ _ => rfl
  | .asc a T', T, h, t => by
      rw [checkF]
      simp only [ATm.landed] at h
      exact bindO_none_fst (checkF_unlanded Γ a T' h t)

/-- The member check gives no derivation to a member list it cannot take as
it is. -/
theorem checkDmsF_unlanded {s : Sig} (Γ : Ctx [] s) :
    (ds : ADms s) → ds.landed = false → ∀ (T : Ty [] s) t, (checkDmsF Γ ds T t).1 = none
  | .dnil, h, _, _ => by simp [ADms.landed] at h
  | .dcons (.dty T') ds', h, T, t => by
      have h' : ds'.landed = false := by simpa [ADms.landed, ADm.landed] using h
      cases T with
      | TAnd A TS =>
        cases A with
        | TTyp l T1 T2 =>
          rw [checkDmsF]
          by_cases hc : l = ds'.erase.length ∧ T1 = T' ∧ T2 = T'
          · rw [dif_pos hc]
            exact mapO_none_fst (checkDmsF_unlanded Γ ds' h' TS t)
          · rw [dif_neg hc]; rfl
        | _ => rw [checkDmsF] <;> first | rfl | (intros; simp_all)
      | _ => rw [checkDmsF] <;> first | rfl | (intros; simp_all)
  | .dcons (.dfun o1 o2 b) ds', h, T, t => by
      simp only [ADms.landed, ADm.landed, Bool.and_eq_false_iff] at h
      cases T with
      | TAnd A TS =>
        cases A with
        | TFun l T11 T12 =>
          rw [checkDmsF]
          by_cases hc : l = ds'.erase.length ∧ EqSome o1 T11 ∧ EqSome o2 T12
          · rw [dif_pos hc]
            rcases h with h | h
            · exact bindO_right_fst (fun _ t' => mapO_none_fst (checkF_unlanded _ b T12 h t')) t
            · exact bindO_none_fst (checkDmsF_unlanded Γ ds' h TS t)
          · rw [dif_neg hc]; rfl
        | _ => rw [checkDmsF] <;> first | rfl | (intros; simp_all)
      | _ => rw [checkDmsF] <;> first | rfl | (intros; simp_all)

end

/-- A term with a candidate is one the typer takes as it is.  So a program the
typer types is elaborated as the typer types it (`elabF_landed`). -/
theorem synthF_cons_landed {s : Sig} {Γ : Ctx [] s} {a : ATm s} {t : Tank} {c : Cand Γ a.erase}
    {cs : List (Cand Γ a.erase)} (h : (synthF Γ a t).1 = c :: cs) : a.landed = true := by
  cases hl : a.landed with
  | true => rfl
  | false => rw [synthF_unlanded Γ a hl t] at h; cases h

/-! ## The frame lemmas of the goal reading

Dealiasing and the goal of a call argument are built from the combinators of
`Fuel.lean` and from framed computations of the typer, so each keeps a marked
tank, never adds fuel, and does the same with more fuel. -/

section Frames
variable {α : Type}

theorem markAs_framed (a : α) : Framed (markAs a) where
  absorbs t ht := by cases t; simp_all [markAs]
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [markAs, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

/-- A computation that marks the tank agrees with any framed one, since it
never ends unmarked. -/
theorem markAs_agree (a : α) {c : Fu α} (hc : Framed c) : Agree (markAs a) c := by
  refine ⟨markAs_framed a, hc, ?_⟩
  intro t r t' h ho _
  simp only [markAs, Prod.mk.injEq] at h
  rw [← h.2] at ho
  simp at ho

end Frames

theorem dealiasTy_agree {s : Sig} (Γ : Ctx [] s) {rec rec' : Ty [] s → Fu (Ty [] s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ G, Agree (dealiasTy Γ rec G) (dealiasTy Γ rec' G)
  | .TSel (.abs y) L => by
    simp only [dealiasTy]
    refine bind_agree (Agree.refl (members_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact ret_agree _
  | .TAnd A B => by
    simp only [dealiasTy]
    exact bind_agree (dealiasTy_agree Γ hr A) fun _ =>
      bind_agree (dealiasTy_agree Γ hr B) fun _ => ret_agree _
  | .TSel (.conc _) _ => ret_agree _
  | .TBot => ret_agree _
  | .TTop => ret_agree _
  | .TFun _ _ _ => ret_agree _
  | .TTyp _ _ _ => ret_agree _
  | .TBind _ => ret_agree _
  | .TOr _ _ => ret_agree _

/-- Dealiasing is framed at every index. -/
theorem dealiasF_framed {s : Sig} (Γ : Ctx [] s) : ∀ d G, Framed (dealiasF Γ d G)
  | 0, G => (dealiasTy_agree Γ (fun T => Agree.refl (markAs_framed T)) G).left
  | d + 1, G => (dealiasTy_agree Γ (fun T => Agree.refl (dealiasF_framed Γ d T)) G).left

/-- Dealiasing at a larger index agrees with the smaller one. -/
theorem dealiasF_agree {s : Sig} (Γ : Ctx [] s) :
    ∀ d d', d ≤ d' → ∀ G, Agree (dealiasF Γ d G) (dealiasF Γ d' G)
  | 0, d', _, G => by
    cases d' with
    | zero => exact Agree.refl (dealiasF_framed Γ 0 G)
    | succ e => exact dealiasTy_agree Γ (fun T => markAs_agree T (dealiasF_framed Γ e T)) G
  | d + 1, d', hd, G => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact dealiasTy_agree Γ (fun T => dealiasF_agree Γ d e (by omega) T) G

/-- Dealiasing from the fuel left is framed. -/
theorem dealiasAt_framed {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) : Framed (dealiasAt Γ G) where
  absorbs t ht := (dealiasF_framed Γ t.left G).absorbs t ht
  spends t := (dealiasF_framed Γ t.left G).spends t
  shift := by
    intro t r t' h ho k
    exact (dealiasF_agree Γ t.left (t.left + k) (Nat.le_add_right _ _) G).sim t r t' h ho k

theorem formalsF_framed {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) : Framed (formalsF Γ t l) :=
  bind_framed (synthF_framed Γ t) fun cts =>
    flatMapL_framed (fun ct => bind_framed (cands_framed Γ l t ct) fun _ => ret_framed _) cts

theorem allBelowF_framed {s : Sig} (Γ : Ctx [] s) (F : Ty [] s) : ∀ Fs, Framed (allBelowF Γ F Fs)
  | [] => ret_framed _
  | F' :: Fs => by
    unfold allBelowF
    split
    · exact allBelowF_framed Γ F Fs
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact allBelowF_framed Γ F Fs
      | none => exact ret_framed _

theorem dominantF_framed {s : Sig} (Γ : Ctx [] s) (Fs : List (Ty [] s)) :
    ∀ cands, Framed (dominantF Γ Fs cands)
  | [] => ret_framed _
  | F :: rest => by
    refine bind_framed (allBelowF_framed Γ F Fs) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact dominantF_framed Γ Fs rest

/-- The goal of a call argument is framed. -/
theorem argGoalF_framed {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) : Framed (argGoalF Γ t l) :=
  bind_framed (formalsF_framed Γ t l) fun Fs => dominantF_framed Γ Fs Fs

/-! ## The goal of a call argument is dominant -/

theorem allBelowF_sub {s : Sig} {Γ : Ctx [] s} {F : Ty [] s} :
    ∀ {Fs : List (Ty [] s)} {t t' : Tank}, allBelowF Γ F Fs t = (true, t') →
      ∀ F' ∈ Fs, Nonempty (SStp Γ F' F)
  | [], _, _, _, F', hF' => absurd hF' List.not_mem_nil
  | F'' :: Fs, t, t', h, F', hF' => by
    unfold allBelowF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hF' with rfl | hm
      · exact ⟨heq ▸ refl _⟩
      · exact allBelowF_sub h F' hm
    · cases hs : subF Γ F'' F t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some d =>
          rcases List.mem_cons.mp hF' with rfl | hm
          · exact ⟨d⟩
          · exact allBelowF_sub h F' hm
        | none => simp [Fu.ret] at h

theorem dominantF_sub {s : Sig} {Γ : Ctx [] s} {Fs : List (Ty [] s)} :
    ∀ {cands : List (Ty [] s)} {t : Tank} {F : Ty [] s} {t' : Tank},
      dominantF Γ Fs cands t = (some F, t') → F ∈ cands ∧ ∀ F' ∈ Fs, Nonempty (SStp Γ F' F)
  | [], _, _, _, h => by simp [dominantF, Fu.ret] at h
  | F0 :: rest, t, F, t', h => by
    unfold dominantF at h
    cases hb : allBelowF Γ F0 Fs t with
    | mk b t1 =>
      simp only [Fu.bind, hb] at h
      cases b with
      | true =>
        simp only [if_true, Fu.ret, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self .., allBelowF_sub hb⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨hm, hs⟩ := dominantF_sub h
        exact ⟨List.mem_cons_of_mem _ hm, hs⟩

/-- The goal of the argument of a call `t.l(·)` is one of the formals the
lookup finds, and every formal is below it. -/
theorem argGoal_dominant {s : Sig} {Γ : Ctx [] s} {t : ATm s} {l : Lb} {tk : Tank} {F : Ty [] s}
    (h : (argGoalF Γ t l tk).1 = some F) :
    ∃ Fs tk', formalsF Γ t l tk = (Fs, tk') ∧ F ∈ Fs ∧ ∀ F' ∈ Fs, Nonempty (SStp Γ F' F) := by
  cases hf : formalsF Γ t l tk with
  | mk Fs t1 =>
    unfold argGoalF at h
    simp only [Fu.bind, hf] at h
    cases hd : dominantF Γ Fs Fs t1 with
    | mk o t2 =>
      rw [hd] at h
      simp only at h
      subst h
      exact ⟨Fs, t1, rfl, dominantF_sub hd⟩

/-! ## Heads and self types in lockstep with the members

A member's label is the number of members below it.  `ADms.memberAt` finds
the member at a label and `ADms.suffixAt` the list from it down.  `Lockstep`
is the shape of a self type the rules `D_Nil`, `D_Typ` and `D_Fun` conclude,
with every written annotation kept.  The theorems say what each head is, when
the heads stop at a missing parameter type, and that the self type formed from
the heads is in lockstep with the members and is the one `selfOf?` computes
when every method is annotated. -/

/-- The member at the label `l`: the one with `l` members below it. -/
def ADms.memberAt {s : Sig} (ds : ADms s) (l : Lb) : Option (ADm s) :=
  match ds with
  | .dnil => none
  | .dcons d ds' => if l = ds'.length then some d else ds'.memberAt l
termination_by structural ds

/-- The member list from the member at the label `l` down. -/
def ADms.suffixAt {s : Sig} (ds : ADms s) (l : Lb) : Option (ADms s) :=
  match ds with
  | .dnil => none
  | .dcons d ds' => if l = ds'.length then some (.dcons d ds') else ds'.suffixAt l
termination_by structural ds

/-- Every method of the member list has a written parameter type and a written
result type.  Bodies are not read. -/
def ADms.AllAnnotated {s : Sig} (ds : ADms s) : Prop :=
  match ds with
  | .dnil => True
  | .dcons (.dty _) ds' => ds'.AllAnnotated
  | .dcons (.dfun o1 o2 _) ds' => o1.isSome = true ∧ o2.isSome = true ∧ ds'.AllAnnotated
termination_by structural ds

/-- `T` is a self type of the members in lockstep: the right nested
intersection `D_Nil`, `D_Typ` and `D_Fun` conclude, at the positions as labels,
with every written annotation kept.  Bodies are not read. -/
inductive Lockstep {s : Sig} : ADms s → Ty [] s → Prop where
  /-- No member, at `⊤`. -/
  | nil : Lockstep .dnil .TTop
  /-- `type = T` at `{L_l : T .. T}`. -/
  | typ {ds : ADms s} {TS : Ty [] s} (T : Ty [] s) :
      Lockstep ds TS → Lockstep (.dcons (.dty T) ds) (.TAnd (.TTyp ds.length T T) TS)
  /-- `def (x [: S]) [: U] = t` at `{def m_l(x : S) : U}`. -/
  | fn {ds : ADms s} {TS : Ty [] s} {o1 : Option (Ty [] s)} {o2 : Option (Ty [] (s,x))}
      {t : ATm (s,x)} (S : Ty [] s) (U : Ty [] (s,x)) :
      Lockstep ds TS → EqSome o1 S → EqSome o2 U →
      Lockstep (.dcons (.dfun o1 o2 t) ds) (.TAnd (.TFun ds.length S U) TS)

section HeadsOf
variable {s : Sig} {pf : Lb → FillR (Option (Ty [] s))} {rf : Lb → Ty [] s → Option (Ty [] (s,x))}

/-- The heads of a type member and the list below it. -/
theorem headsOf_dty {T : Ty [] s} {ds : ADms s} {hs : List (Lb × Head s)}
    (h : headsOf pf rf (.dcons (.dty T) ds) = .ok hs) :
    ∃ hs', headsOf pf rf ds = .ok hs' ∧ hs = (ds.length, .typ T) :: hs' := by
  simp only [headsOf] at h
  cases h' : headsOf pf rf ds with
  | error r => rw [h'] at h; cases h
  | ok hs' =>
    rw [h'] at h
    cases h
    exact ⟨hs', rfl, rfl⟩

/-- The heads of a method and the list below it.  The parameter type is the
written one, else the one `pf` gives, and the result is the written one, else
the one `rf` gives. -/
theorem headsOf_dfun {o1 : Option (Ty [] s)} {o2 : Option (Ty [] (s,x))} {t : ATm (s,x)}
    {ds : ADms s} {hs : List (Lb × Head s)}
    (h : headsOf pf rf (.dcons (.dfun o1 o2 t) ds) = .ok hs) :
    ∃ hs' S, headsOf pf rf ds = .ok hs' ∧
      hs = (ds.length, .fn S (o2.or (rf ds.length S))) :: hs' ∧
      (o1 = some S ∨ (o1 = none ∧ pf ds.length = .ok (some S))) := by
  simp only [headsOf] at h
  cases h' : headsOf pf rf ds with
  | error r => rw [h'] at h; cases h
  | ok hs' =>
    rw [h'] at h
    cases o1 with
    | some S =>
      cases h
      exact ⟨hs', S, rfl, rfl, .inl rfl⟩
    | none =>
      simp only at h
      cases hp : pf ds.length with
      | error r => rw [hp] at h; cases h
      | ok o =>
        rw [hp] at h
        cases o with
        | none => cases h
        | some S =>
          cases h
          exact ⟨hs', S, rfl, rfl, .inr ⟨rfl, rfl⟩⟩

/-- The heads of a member and the list below it: the head of the member at its
label, consed onto the heads below. -/
theorem headsOf_cons {d : ADm s} {ds : ADms s} {hs : List (Lb × Head s)}
    (h : headsOf pf rf (.dcons d ds) = .ok hs) :
    ∃ hs' H, headsOf pf rf ds = .ok hs' ∧ hs = (ds.length, H) :: hs' := by
  cases d with
  | dty T =>
    obtain ⟨hs', h1, h2⟩ := headsOf_dty h
    exact ⟨hs', _, h1, h2⟩
  | dfun o1 o2 t =>
    obtain ⟨hs', S, h1, h2, -⟩ := headsOf_dfun h
    exact ⟨hs', _, h1, h2⟩

/-- A method without a parameter type has the head the goal gives it: the
parameter type `pf` gives at its label, and its written result, else the one
`rf` gives. -/
theorem headsOf_param {l : Lb} {o2 : Option (Ty [] (s,x))} {t : ATm (s,x)} :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      ds.memberAt l = some (.dfun none o2 t) →
      ∃ S, lookupL hs l = some (.fn S (o2.or (rf l S))) ∧ pf l = .ok (some S)
  | .dnil, _, _, hm => by simp [ADms.memberAt] at hm
  | .dcons d ds, hs, h, hm => by
    by_cases hl : l = ds.length
    · subst hl
      simp only [ADms.memberAt, if_true, Option.some.injEq] at hm
      subst hm
      obtain ⟨hs', S, -, rfl, hS⟩ := headsOf_dfun h
      refine ⟨S, by simp [lookupL], ?_⟩
      rcases hS with h1 | ⟨-, h2⟩
      · cases h1
      · exact h2
    · simp only [ADms.memberAt, hl, if_false] at hm
      obtain ⟨hs', H, h1, rfl⟩ := headsOf_cons h
      simp only [lookupL, hl, if_false]
      exact headsOf_param h1 hm

/-- A method with a written parameter type keeps it in its head. -/
theorem headsOf_written {l : Lb} {S : Ty [] s} {o2 : Option (Ty [] (s,x))} {t : ATm (s,x)} :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      ds.memberAt l = some (.dfun (some S) o2 t) →
      lookupL hs l = some (.fn S (o2.or (rf l S)))
  | .dnil, _, _, hm => by simp [ADms.memberAt] at hm
  | .dcons d ds, hs, h, hm => by
    by_cases hl : l = ds.length
    · subst hl
      simp only [ADms.memberAt, if_true, Option.some.injEq] at hm
      subst hm
      obtain ⟨hs', S', -, rfl, hS⟩ := headsOf_dfun h
      rcases hS with h1 | ⟨h1, -⟩
      · cases h1
        simp [lookupL]
      · cases h1
    · simp only [ADms.memberAt, hl, if_false] at hm
      obtain ⟨hs', H, h1, rfl⟩ := headsOf_cons h
      simp only [lookupL, hl, if_false]
      exact headsOf_written h1 hm

/-- A type member is known at its right side. -/
theorem headsOf_typ {l : Lb} {T : Ty [] s} :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      ds.memberAt l = some (.dty T) → lookupL hs l = some (.typ T)
  | .dnil, _, _, hm => by simp [ADms.memberAt] at hm
  | .dcons d ds, hs, h, hm => by
    by_cases hl : l = ds.length
    · subst hl
      simp only [ADms.memberAt, if_true, Option.some.injEq] at hm
      subst hm
      obtain ⟨hs', -, rfl⟩ := headsOf_dty h
      simp [lookupL]
    · simp only [ADms.memberAt, hl, if_false] at hm
      obtain ⟨hs', H, h1, rfl⟩ := headsOf_cons h
      simp only [lookupL, hl, if_false]
      exact headsOf_typ h1 hm

/-- A suffix starts at a label below the length of the list. -/
theorem suffixAt_lt {l : Lb} : ∀ {ds e : ADms s}, ds.suffixAt l = some e → l < ds.length
  | .dnil, _, h => by simp [ADms.suffixAt] at h
  | .dcons d ds, e, h => by
    show l < ds.length + 1
    by_cases hl : l = ds.length
    · subst hl
      exact Nat.lt_succ_self _
    · simp only [ADms.suffixAt, hl, if_false] at h
      exact Nat.lt_succ_of_lt (suffixAt_lt h)

/-- The suffix at a label starts with the member at that label. -/
theorem memberAt_of_suffixAt {l : Lb} {d : ADm s} {ds' : ADms s} :
    ∀ {ds : ADms s}, ds.suffixAt l = some (.dcons d ds') → ds.memberAt l = some d
  | .dnil, h => by simp [ADms.suffixAt] at h
  | .dcons d0 ds, h => by
    by_cases hl : l = ds.length
    · subst hl
      simp only [ADms.suffixAt, if_true, Option.some.injEq, ADms.dcons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ADms.memberAt]
    · simp only [ADms.suffixAt, hl, if_false] at h
      simp only [ADms.memberAt, hl, if_false]
      exact memberAt_of_suffixAt h

/-- The heads stop at a missing parameter type at `l` exactly when the method
at `l` has no parameter type, `pf` gives none, and every member below it has a
head.  `pf` itself never reports that reason. -/
theorem headsOf_missing_iff {l : Lb}
    (hpf : ∀ l', pf l' ≠ .error (.missingParamType (some l))) :
    ∀ {ds : ADms s}, headsOf pf rf ds = .error (.missingParamType (some l)) ↔
      ∃ o2 t ds', ds.suffixAt l = some (.dcons (.dfun none o2 t) ds') ∧ pf l = .ok none ∧
        ∃ hs, headsOf pf rf ds' = .ok hs
  | .dnil => by simp [headsOf, ADms.suffixAt]
  | .dcons d ds => by
    constructor
    · intro h
      cases h' : headsOf pf rf ds with
      | error r =>
        have hr : r = .missingParamType (some l) := by
          cases d with
          | dty T => simp only [headsOf, h'] at h; cases h; rfl
          | dfun o1 o2 t => simp only [headsOf, h'] at h; cases h; rfl
        subst hr
        obtain ⟨o2, t, ds', hs, hp, hk⟩ := (headsOf_missing_iff hpf).mp h'
        have hl : l ≠ ds.length := Nat.ne_of_lt (suffixAt_lt hs)
        refine ⟨o2, t, ds', ?_, hp, hk⟩
        simp only [ADms.suffixAt, hl, if_false]
        exact hs
      | ok hs0 =>
        cases d with
        | dty T => simp only [headsOf, h'] at h; cases h
        | dfun o1 o2 t =>
          cases o1 with
          | some S => simp only [headsOf, h'] at h; cases h
          | none =>
            cases hp : pf ds.length with
            | error r =>
              simp only [headsOf, h', hp] at h
              cases h
              exact absurd hp (hpf _)
            | ok o =>
              cases o with
              | some S => simp only [headsOf, h', hp] at h; cases h
              | none =>
                simp only [headsOf, h', hp] at h
                cases h
                exact ⟨o2, t, ds, by simp [ADms.suffixAt], hp, hs0, h'⟩
    · rintro ⟨o2, t, ds', hs, hp, hs0, hk⟩
      by_cases hl : l = ds.length
      · subst hl
        simp only [ADms.suffixAt, if_true, Option.some.injEq, ADms.dcons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [headsOf, hk, hp]
      · simp only [ADms.suffixAt, hl, if_false] at hs
        have h' := (headsOf_missing_iff hpf).mpr ⟨o2, t, ds', hs, hp, hs0, hk⟩
        cases d with
        | dty T => simp only [headsOf, h']
        | dfun o1 o2 t => simp only [headsOf, h']

end HeadsOf

/-- The goal reading reports only a mismatch. -/
theorem paramFrom_error {s : Sig} {rd : List (Lb × Inherit s)} {l : Lb} {r : EReason}
    (h : paramFrom rd l = .error r) : r = .mismatch := by
  unfold paramFrom at h
  split at h <;> cases h
  rfl

/-- The goal gives a parameter type exactly when it declares the method. -/
theorem paramFrom_some {s : Sig} {rd : List (Lb × Inherit s)} {l : Lb} {S : Ty [] s} :
    paramFrom rd l = .ok (some S) ↔ ∃ U b, lookupL rd l = some ⟨.one S U, b⟩ := by
  unfold paramFrom
  constructor
  · intro h
    split at h
    · cases h
      exact ⟨_, _, by assumption⟩
    · cases h
    · cases h
  · rintro ⟨U, b, h⟩
    rw [h]

/-- The goal gives no parameter type exactly when it declares no method at the
label. -/
theorem paramFrom_none {s : Sig} {rd : List (Lb × Inherit s)} {l : Lb} :
    paramFrom rd l = .ok none ↔ ∀ i, lookupL rd l = some i → i.part = .none := by
  unfold paramFrom
  constructor
  · intro h i hi
    rw [hi] at h
    obtain ⟨p, b⟩ := i
    cases p with
    | none => rfl
    | one S U => cases h
    | bad => cases h
  · intro h
    cases hl : lookupL rd l with
    | none => rfl
    | some i =>
      have := h i hl
      obtain ⟨p, b⟩ := i
      cases this
      rfl

/-- The fill reports a missing parameter type at `l` exactly when the method at
`l` has no parameter type, the goal declares no method there, and every member
below it has a head. -/
theorem missingParam_iff {s : Sig} {rd : List (Lb × Inherit s)}
    {rf : Lb → Ty [] s → Option (Ty [] (s,x))} {ds : ADms s} {l : Lb} :
    headsOf (paramFrom rd) rf ds = .error (.missingParamType (some l)) ↔
      ∃ o2 t ds', ds.suffixAt l = some (.dcons (.dfun none o2 t) ds') ∧
        paramFrom rd l = .ok none ∧ ∃ hs, headsOf (paramFrom rd) rf ds' = .ok hs :=
  headsOf_missing_iff fun _ h => by cases paramFrom_error h

/-- A missing parameter type at `l` is a method at `l` with no parameter type,
for which the goal gives none. -/
theorem missingParam_member {s : Sig} {rd : List (Lb × Inherit s)}
    {rf : Lb → Ty [] s → Option (Ty [] (s,x))} {ds : ADms s} {l : Lb}
    (h : headsOf (paramFrom rd) rf ds = .error (.missingParamType (some l))) :
    ∃ o2 t, ds.memberAt l = some (.dfun none o2 t) ∧ paramFrom rd l = .ok none := by
  obtain ⟨o2, t, ds', hs, hp, -⟩ := missingParam_iff.mp h
  exact ⟨o2, t, memberAt_of_suffixAt hs, hp⟩

section FullSelf
variable {s : Sig} {pf : Lb → FillR (Option (Ty [] s))} {rf : Lb → Ty [] s → Option (Ty [] (s,x))}

/-- The self type formed from the heads is in lockstep with the members. -/
theorem fullSelf_lockstep {known : List (Lb × Ty [] (s,x))} :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)} {T : Ty [] s},
      headsOf pf rf ds = .ok hs → fullSelf hs known = some T → Lockstep ds T
  | .dnil, hs, T, hh, h => by
    simp only [headsOf, Except.ok.injEq] at hh
    subst hh
    simp only [fullSelf, Option.some.injEq] at h
    subst h
    exact .nil
  | .dcons (.dty T') ds, hs, T, hh, h => by
    obtain ⟨hs', h1, rfl⟩ := headsOf_dty hh
    simp only [fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨T0, h0, rfl⟩ := h
    exact .typ T' (fullSelf_lockstep h1 h0)
  | .dcons (.dfun o1 o2 t) ds, hs, T, hh, h => by
    obtain ⟨hs', S, h1, rfl, hS⟩ := headsOf_dfun hh
    have e1 : EqSome o1 S := by
      rcases hS with h' | ⟨h', -⟩
      · exact .inr h'
      · exact .inl h'
    cases hU : o2.or (rf ds.length S) with
    | some U =>
      rw [hU] at h
      simp only [fullSelf, Option.map_eq_some_iff] at h
      obtain ⟨T0, h0, rfl⟩ := h
      have e2 : EqSome o2 U := by
        cases o2 with
        | none => exact .inl rfl
        | some U' =>
          have hU' : some U' = some U := hU
          exact .inr hU'
      exact .fn S U (fullSelf_lockstep h1 h0) e1 e2
    | none =>
      rw [hU] at h
      have e2 : o2 = none := by
        cases o2 with
        | none => rfl
        | some _ => simp at hU
      simp only [fullSelf] at h
      cases hk : lookupL known ds.length with
      | none => rw [hk] at h; cases h
      | some U =>
        rw [hk] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨T0, h0, rfl⟩ := h
        exact .fn S U (fullSelf_lockstep h1 h0) e1 (.inl e2)

/-- A member list whose methods are all annotated is one `selfOf?` types. -/
theorem allAnnotated_iff : ∀ {ds : ADms s}, ds.AllAnnotated ↔ (selfOf? ds.erase).isSome = true
  | .dnil => by simp [ADms.AllAnnotated, ADms.erase, selfOf?]
  | .dcons (.dty T) ds => by
    simp only [ADms.AllAnnotated, ADms.erase, ADm.erase, selfOf?, Option.isSome_map]
    exact allAnnotated_iff
  | .dcons (.dfun o1 o2 t) ds => by
    simp only [ADms.AllAnnotated, ADms.erase, ADm.erase]
    cases o1 with
    | none => simp [selfOf?]
    | some S =>
      cases o2 with
      | none => simp [selfOf?]
      | some U =>
        simp only [selfOf?, Option.isSome_map, Option.isSome_some, true_and]
        exact allAnnotated_iff

/-- The heads of a member list whose methods are all annotated never stop. -/
theorem headsOf_annotated :
    ∀ {ds : ADms s}, ds.AllAnnotated → ∃ hs, headsOf pf rf ds = .ok hs
  | .dnil, _ => ⟨[], rfl⟩
  | .dcons (.dty T) ds, hw => by
    obtain ⟨hs, h⟩ := headsOf_annotated (ds := ds) hw
    exact ⟨(ds.length, .typ T) :: hs, by simp only [headsOf, h]⟩
  | .dcons (.dfun o1 o2 t) ds, hw => by
    simp only [ADms.AllAnnotated] at hw
    obtain ⟨h1, -, hw⟩ := hw
    obtain ⟨S, rfl⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨hs, h⟩ := headsOf_annotated (ds := ds) hw
    exact ⟨(ds.length, .fn S (o2.or (rf ds.length S))) :: hs, by simp only [headsOf, h]⟩

/-- For a member list whose methods are all annotated, the self type formed
from the heads is the one `selfOf?` computes, the one the typer reads. -/
theorem fullSelf_selfOf {known : List (Lb × Ty [] (s,x))} :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, ds.AllAnnotated →
      headsOf pf rf ds = .ok hs → fullSelf hs known = selfOf? ds.erase
  | .dnil, hs, _, hh => by
    simp only [headsOf, Except.ok.injEq] at hh
    subst hh
    rfl
  | .dcons (.dty T) ds, hs, hw, hh => by
    obtain ⟨hs', h1, rfl⟩ := headsOf_dty hh
    simp only [ADms.AllAnnotated] at hw
    simp only [fullSelf, ADms.erase, ADm.erase, selfOf?, ADms.length_erase,
      fullSelf_selfOf hw h1]
  | .dcons (.dfun o1 o2 t) ds, hs, hw, hh => by
    simp only [ADms.AllAnnotated] at hw
    obtain ⟨h1, h2, hw⟩ := hw
    obtain ⟨S1, rfl⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨U, rfl⟩ := Option.isSome_iff_exists.mp h2
    obtain ⟨hs', S, h1', rfl, hS⟩ := headsOf_dfun hh
    have hS1 : S = S1 := by
      rcases hS with h' | ⟨h', -⟩
      · exact (Option.some.inj h').symm
      · cases h'
    subst hS1
    have hU : (some U).or (rf ds.length S) = some U := rfl
    rw [hU]
    simp only [fullSelf, ADms.erase, ADm.erase, selfOf?, ADms.length_erase,
      fullSelf_selfOf hw h1']

/-- Inference extends `selfOf?`: a literal the typer gives a self type from its
members gets that self type from its heads, whatever the goal says. -/
theorem fullSelf_of_selfOf {known : List (Lb × Ty [] (s,x))} {ds : ADms s} {T : Ty [] s}
    (h : selfOf? ds.erase = some T) :
    ∃ hs, headsOf pf rf ds = .ok hs ∧ fullSelf hs known = some T := by
  have hw : ds.AllAnnotated := allAnnotated_iff.mpr (by rw [h]; rfl)
  obtain ⟨hs, hh⟩ := headsOf_annotated (pf := pf) (rf := rf) hw
  exact ⟨hs, hh, (fullSelf_selfOf hw hh).trans h⟩

end FullSelf

/-! ## The rounds

The least candidate is a candidate below every other one.  The rounds keep a
marked tank, never add fuel, and do the same with more fuel, when every job
does.  A round types every ready job that does not use the self bare, and a
job that does only once no such job is ready.  The cyclic reference names a
pending method whose walk comes back to it, and a round that types nothing
always has one.  The jobs of a literal are its methods whose result is
pending, and rounds that end type every one of them. -/

/-! ### The frame lemmas of the rounds -/

theorem belowAllF_framed {s : Sig} (Γ : Ctx [] s) (T : Ty [] s) :
    ∀ Us, Framed (belowAllF Γ T Us)
  | [] => ret_framed _
  | U :: Us => by
    unfold belowAllF
    split
    · exact belowAllF_framed Γ T Us
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact belowAllF_framed Γ T Us
      | none => exact ret_framed _

theorem leastFromF_framed {s : Sig} (Γ : Ctx [] s) {t0 : Tm [] s} (Ts : List (Ty [] s)) :
    ∀ cs : List (Cand Γ t0), Framed (leastFromF Γ Ts cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed Γ c.ty Ts) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromF_framed Γ Ts rest

theorem leastCandF_framed {s : Sig} (Γ : Ctx [] s) {t0 : Tm [] s} (cs : List (Cand Γ t0)) :
    Framed (leastCandF Γ cs) :=
  leastFromF_framed Γ _ cs

theorem runJobF_framed {s : Sig} (Γ : Ctx [] s) (P : Ty [] (s,x)) {j : Job (s,x)}
    (hj : ∀ Γ', Framed (j.run Γ')) : Framed (runJobF Γ P j) := by
  refine bind_framed (hj _) fun r => ?_
  split
  · exact ret_framed _
  · exact ret_framed _
  · refine bind_framed (leastCandF_framed _ _) fun o => ?_
    cases o with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

theorem roundF_framed {s : Sig} (Γ : Ctx [] s) (P : Ty [] (s,x)) :
    ∀ (js : List (Job (s,x))), (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundF Γ P js)
  | [], _ => ret_framed _
  | j :: js, hj => by
    refine bind_framed (runJobF_framed Γ P (hj j (List.mem_cons_self ..))) fun r => ?_
    cases r with
    | ok e =>
      refine bind_framed (roundF_framed Γ P js fun j' h' => hj j' (List.mem_cons_of_mem _ h'))
        fun r' => ?_
      cases r' with
      | ok _ => exact ret_framed _
      | error _ => exact ret_framed _
    | error _ => exact ret_framed _

/-- The rounds are framed when every job's run is. -/
theorem roundsF_framed {s : Sig} (Γ : Ctx [] s) (hs : List (Lb × Head (s,x))) :
    ∀ (n : Nat) (js : List (Job (s,x))) (done : List (Done (s,x))),
      (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundsF Γ hs n js done)
  | _, [], _, _ => by
    unfold roundsF
    exact ret_framed _
  | 0, j :: js, _, _ => by
    unfold roundsF
    exact ret_framed _
  | n + 1, j :: js, done, hj => by
    unfold roundsF
    split
    · exact ret_framed _
    · refine bind_framed (roundF_framed Γ _ _ fun j' h' => hj j' (List.mem_filter.mp h').1)
        fun r => ?_
      cases r with
      | ok typed =>
        exact roundsF_framed Γ hs n _ _ fun j' h' => hj j' (List.mem_filter.mp h').1
      | error _ => exact ret_framed _

/-- Forming a self type is framed when every job's run is. -/
theorem formSelfF_framed {s : Sig} (Γ : Ctx [] s) (hs : List (Lb × Head (s,x)))
    {js : List (Job (s,x))} (hj : ∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) :
    Framed (formSelfF Γ hs js) := by
  refine bind_framed (roundsF_framed Γ hs _ js [] hj) fun r => ?_
  cases r with
  | ok _ => exact ret_framed _
  | error _ => exact ret_framed _

/-! ### The least candidate is least -/

theorem belowAllF_sub {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} :
    ∀ {Us : List (Ty [] s)} {t t' : Tank}, belowAllF Γ T Us t = (true, t') →
      ∀ U ∈ Us, Nonempty (SStp Γ T U)
  | [], _, _, _, U, hU => absurd hU List.not_mem_nil
  | U' :: Us, t, t', h, U, hU => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hU with rfl | hm
      · exact ⟨heq ▸ refl _⟩
      · exact belowAllF_sub h U hm
    · cases hs : subF Γ T U' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some d =>
          rcases List.mem_cons.mp hU with rfl | hm
          · exact ⟨d⟩
          · exact belowAllF_sub h U hm
        | none => simp [Fu.ret] at h

theorem leastFromF_sub {s : Sig} {Γ : Ctx [] s} {t0 : Tm [] s} {Ts : List (Ty [] s)} :
    ∀ {cs : List (Cand Γ t0)} {t : Tank} {c : Cand Γ t0} {t' : Tank},
      leastFromF Γ Ts cs t = (some c, t') → c ∈ cs ∧ ∀ T ∈ Ts, Nonempty (SStp Γ c.ty T)
  | [], _, _, _, h => by simp [leastFromF, Fu.ret] at h
  | c0 :: rest, t, c, t', h => by
    unfold leastFromF at h
    cases hb : belowAllF Γ c0.ty Ts t with
    | mk b t1 =>
      simp only [Fu.bind, hb] at h
      cases b with
      | true =>
        simp only [if_true, Fu.ret, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self .., belowAllF_sub hb⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨hm, hs⟩ := leastFromF_sub h
        exact ⟨List.mem_cons_of_mem _ hm, hs⟩

/-- The least candidate is a candidate, and its type is below the type of
every candidate. -/
theorem leastCand_least {s : Sig} {Γ : Ctx [] s} {t0 : Tm [] s} {cs : List (Cand Γ t0)}
    {tk : Tank} {c : Cand Γ t0} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) :
    c ∈ cs ∧ ∀ c' ∈ cs, Nonempty (SStp Γ c.ty c'.ty) := by
  obtain ⟨hm, hs⟩ := leastFromF_sub h
  exact ⟨hm, fun c' hc' => hs c'.ty (List.mem_map_of_mem hc')⟩

theorem belowAllF_sub? {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} :
    ∀ {Us : List (Ty [] s)} {t t' : Tank}, belowAllF Γ T Us t = (true, t') → t'.out = false →
      ∀ U ∈ Us, U = T ∨ ∃ n, (sub? Γ T U n).1.isSome = true
  | [], _, _, _, _, U, hU => absurd hU List.not_mem_nil
  | U' :: Us, t, t', h, ho, U, hU => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hU with rfl | hm
      · exact .inl heq.symm
      · exact belowAllF_sub? h ho U hm
    · cases hs : subF Γ T U' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some e =>
          rcases List.mem_cons.mp hU with rfl | hm
          · have h1 : t1.out = false := (belowAllF_framed Γ T Us).start h ho
            have h0 : t.out = false := (subF_framed Γ T U).start hs h1
            refine .inr ⟨t.left, ?_⟩
            have ht : t = ⟨t.left, false⟩ := by
              cases t
              simp_all
            show (subF Γ T U ⟨t.left, false⟩).1.isSome = true
            rw [← ht, hs]
            rfl
          · exact belowAllF_sub? h ho U hm
        | none => simp [Fu.ret] at h

theorem leastFromF_sub? {s : Sig} {Γ : Ctx [] s} {t0 : Tm [] s} {Ts : List (Ty [] s)} :
    ∀ {cs : List (Cand Γ t0)} {t : Tank} {c : Cand Γ t0} {t' : Tank},
      leastFromF Γ Ts cs t = (some c, t') → t'.out = false →
        ∀ T ∈ Ts, T = c.ty ∨ ∃ n, (sub? Γ c.ty T n).1.isSome = true
  | [], _, _, _, h, _ => by simp [leastFromF, Fu.ret] at h
  | c0 :: rest, t, c, t', h, ho => by
    unfold leastFromF at h
    cases hb : belowAllF Γ c0.ty Ts t with
    | mk b t1 =>
      simp only [Fu.bind, hb] at h
      cases b with
      | true =>
        simp only [if_true, Fu.ret, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact belowAllF_sub? hb ho
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact leastFromF_sub? h ho

/-- The same with the subtyping goal from a full tank: on a tank that ends
unmarked, the type of the least candidate is the type of every other candidate
or below it at some fuel. -/
theorem leastCand_sub? {s : Sig} {Γ : Ctx [] s} {t0 : Tm [] s} {cs : List (Cand Γ t0)}
    {tk : Tank} {c : Cand Γ t0} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk'))
    (ho : tk'.out = false) :
    ∀ c' ∈ cs, c'.ty = c.ty ∨ ∃ n, (sub? Γ c.ty c'.ty n).1.isSome = true :=
  fun c' hc' => leastFromF_sub? h ho c'.ty (List.mem_map_of_mem hc')

/-- A typed job keeps its label and body.  Its filled body is the one its run
returns, in the context that binds the self at the snapshot and the parameter
at its type.  Its result is the type of the least candidate of that body. -/
theorem runJobF_least {s : Sig} {Γ : Ctx [] s} {P : Ty [] (s,x)} {j : Job (s,x)} {t t' : Tank}
    {e : Done (s,x)} (h : runJobF Γ P j t = (.ok e, t')) :
    e.lbl = j.lbl ∧ e.tm = j.tm ∧
      ∃ cs t1 c, j.run ((Γ.cons P).cons j.par.weaken) t = (.ok ⟨e.a, cs⟩, t1) ∧ c ∈ cs ∧
        e.ty = c.ty ∧ ∀ c' ∈ cs, Nonempty (SStp ((Γ.cons P).cons j.par.weaken) c.ty c'.ty) := by
  unfold runJobF at h
  cases hr : j.run ((Γ.cons P).cons j.par.weaken) t with
  | mk r t1 =>
    simp only [Fu.bind, hr] at h
    cases r with
    | error _ => simp [Fu.ret] at h
    | ok p =>
      obtain ⟨a, cs⟩ := p
      cases cs with
      | nil => simp [Fu.ret] at h
      | cons c0 cs' =>
        simp only at h
        cases hl : leastCandF ((Γ.cons P).cons j.par.weaken) (c0 :: cs') t1 with
        | mk o t2 =>
          simp only [Fu.bind, hl] at h
          cases o with
          | none => simp [Fu.ret] at h
          | some c =>
            simp only [Fu.ret, Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨hm, hs⟩ := leastCand_least hl
            exact ⟨rfl, rfl, c0 :: cs', t1, c, rfl, hm, rfl, hs⟩

/-! ### Lists

Facts about lists, proved by induction so that they need no choice. -/

/-- A filter is empty exactly when the test fails on every entry. -/
theorem filterL_nil_iff {α : Type} (p : α → Bool) :
    ∀ l : List α, l.filter p = [] ↔ ∀ a ∈ l, p a = false
  | [] => by simp
  | a :: l => by
    cases hp : p a with
    | true => simp [List.filter, hp]
    | false =>
      simp only [List.filter, hp, List.mem_cons, forall_eq_or_imp, true_and]
      exact filterL_nil_iff p l

/-- A list on which `all` fails has an entry the test fails on. -/
theorem allL_false {α : Type} (f : α → Bool) :
    ∀ l : List α, l.all f = false → ∃ a ∈ l, f a = false
  | [], h => by simp at h
  | a :: l, h => by
    cases hf : f a with
    | false => exact ⟨a, List.mem_cons_self .., hf⟩
    | true =>
      simp only [List.all_cons, hf, Bool.true_and] at h
      obtain ⟨b, hb, hfb⟩ := allL_false f l h
      exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩

/-- The list without the first occurrence of `m`. -/
def dropL (m : Lb) : List Lb → List Lb
  | [] => []
  | b :: l => if b = m then l else b :: dropL m l

theorem dropL_length {m : Lb} : ∀ {l : List Lb}, m ∈ l → (dropL m l).length + 1 = l.length
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    simp only [dropL]
    by_cases hb : b = m
    · simp only [hb, if_true, List.length_cons]
    · simp only [hb, if_false, List.length_cons]
      rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hb
      · rw [dropL_length h]

theorem mem_dropL {m y : Lb} (hy : y ≠ m) : ∀ {l : List Lb}, y ∈ l → y ∈ dropL m l
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    simp only [dropL]
    by_cases hb : b = m
    · simp only [hb, if_true]
      rcases List.mem_cons.mp h with h | h
      · exact absurd (h.trans hb) hy
      · exact h
    · simp only [hb, if_false]
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_dropL hy h)

/-! ### The bare rule

A round over the pending jobs types each ready job that does not use the self
bare.  A job that uses the self bare is typed only in a round in which every
ready job uses it bare too.  A round types nothing exactly when no pending job
is ready. -/

section Bare
variable {s : Sig} {js : List (Job (s,x))} {j : Job (s,x)}

/-- A job a round types is ready. -/
theorem picks_ready (h : picks js j = true) : readyIn (js.map (·.lbl)) j = true := by
  simp only [picks, Bool.and_eq_true] at h
  exact h.1

/-- A ready job that does not use the self bare is typed in the round. -/
theorem picks_plain (hj : j ∈ js) (hr : readyIn (js.map (·.lbl)) j = true)
    (hb : j.deps.2 = false) : picks js j = true := by
  have hbr : bareRound js = false := by
    simp only [bareRound, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true,
      Bool.not_eq_true']
    exact ⟨j, hj, hr, hb⟩
  simp only [picks, hr, hb, hbr, decide_true, Bool.and_self]

/-- A job that uses the self bare is typed only in a round in which every
ready job uses the self bare. -/
theorem picks_bare (h : picks js j = true) (hb : j.deps.2 = true) :
    ∀ k ∈ js, readyIn (js.map (·.lbl)) k = true → k.deps.2 = true := by
  intro k hk hr
  simp only [picks, Bool.and_eq_true, decide_eq_true_eq] at h
  have hbr : bareRound js = true := h.2 ▸ hb
  cases hkb : k.deps.2 with
  | true => rfl
  | false =>
    have : bareRound js = false := by
      simp only [bareRound, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true,
        Bool.not_eq_true']
      exact ⟨k, hk, hr, hkb⟩
    rw [hbr] at this
    cases this

/-- A round types nothing exactly when no pending job is ready. -/
theorem picks_nil_iff :
    js.filter (picks js) = [] ↔ ∀ j ∈ js, readyIn (js.map (·.lbl)) j = false := by
  rw [filterL_nil_iff]
  constructor
  · intro h j hj
    have hn : ∀ k ∈ js, picks js k = true → False := fun k hk hp => by
      rw [h k hk] at hp
      cases hp
    cases hr : readyIn (js.map (·.lbl)) j with
    | false => rfl
    | true =>
      exfalso
      cases hb : j.deps.2 with
      | false => exact hn j hj (picks_plain hj hr hb)
      | true =>
        cases hbr : bareRound js with
        | true =>
          refine hn j hj ?_
          simp only [picks, hr, hb, hbr, decide_true, Bool.and_self]
        | false =>
          simp only [bareRound, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true,
            Bool.not_eq_true'] at hbr
          obtain ⟨k, hk, hkr, hkb⟩ := hbr
          exact hn k hk (picks_plain hk hkr hkb)
  · intro h j hj
    cases hp : picks js j with
    | false => rfl
    | true =>
      have h1 := picks_ready hp
      rw [h j hj] at h1
      cases h1

end Bare

/-! ### The cyclic reference is on a cycle -/

theorem walkL_snoc {s : Sig} {js : List (Job (s,x))} {l l' : Lb} (hn : nextL js l = some l') :
    ∀ {k : Nat} {m : Lb}, walkL js k m = some l → walkL js (k + 1) m = some l'
  | 0, m, h => by
    simp only [walkL, Option.some.injEq] at h
    subst h
    simp only [walkL, hn, Option.bind_some]
  | k + 1, m, h => by
    simp only [walkL] at h ⊢
    cases hm : nextL js m with
    | none => simp [hm] at h
    | some m1 =>
      simp only [hm, Option.bind_some] at h ⊢
      exact walkL_snoc hn h

theorem nextL_mem {s : Sig} {js : List (Job (s,x))} {l l' : Lb} (h : nextL js l = some l') :
    l' ∈ js.map (·.lbl) := by
  unfold nextL at h
  split at h
  · rename_i j _
    have hm : l' ∈ waitsFor js j := List.mem_of_mem_head? h
    simp only [waitsFor, List.mem_filter] at hm
    exact List.contains_iff_mem.mp hm.2
  · cases h

theorem cycleFrom_onCycle {s : Sig} {js : List (Job (s,x))} :
    ∀ {n : Nat} {seen : List Lb} {l r : Lb},
      (∀ m ∈ seen, ∃ k, walkL js (k + 1) m = some l) → l ∈ js.map (·.lbl) →
      cycleFrom js n seen l = some r → ∃ j ∈ js, j.lbl = r ∧ OnCycle js j
  | 0, _, _, _, _, _, h => by simp [cycleFrom] at h
  | n + 1, seen, l, r, hs, hl, h => by
    unfold cycleFrom at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨k, hk⟩ := hs l (List.contains_iff_mem.mp hc)
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
      exact ⟨j, hj, rfl, k, hk⟩
    · cases hn : nextL js l with
      | none => simp [hn] at h
      | some l' =>
        simp only [hn] at h
        refine cycleFrom_onCycle (fun m hm => ?_) (nextL_mem hn) h
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨0, by simp only [walkL, hn, Option.bind_some]⟩
        · obtain ⟨k, hk⟩ := hs m hm
          exact ⟨k + 1, walkL_snoc hn hk⟩

/-- The label `cycleAt` reports is the label of a pending job whose walk comes
back to it. -/
theorem cycleAt_onCycle {s : Sig} {js : List (Job (s,x))} {n : Nat} {l : Lb}
    (h : cycleAt js n = some l) : ∃ j ∈ js, j.lbl = l ∧ OnCycle js j := by
  unfold cycleAt at h
  split at h
  · cases h
  · rename_i j js'
    exact cycleFrom_onCycle (by simp) (List.mem_map_of_mem (List.mem_cons_self ..)) h

/-- A list without repeats whose entries are all in `b` is no longer than
`b`. -/
theorem nodup_length_le {a b : List Lb} (ha : a.Nodup) (hs : ∀ m ∈ a, m ∈ b) :
    a.length ≤ b.length := by
  induction a generalizing b with
  | nil => exact Nat.zero_le _
  | cons m a ih =>
    obtain ⟨hm, ha'⟩ := List.nodup_cons.mp ha
    have hb : m ∈ b := hs m (List.mem_cons_self ..)
    have hs' : ∀ m' ∈ a, m' ∈ dropL m b := fun m' h' =>
      mem_dropL (fun e : m' = m => hm (e ▸ h')) (hs m' (List.mem_cons_of_mem _ h'))
    have h1 := ih ha' hs'
    have h2 := dropL_length hb
    show a.length + 1 ≤ b.length
    omega

/-- When every pending job waits for a pending method, the walk from a pending
label repeats one within the steps the labels allow. -/
theorem cycleFrom_isSome {s : Sig} {js : List (Job (s,x))}
    (hn : ∀ l ∈ js.map (·.lbl), (nextL js l).isSome = true) :
    ∀ {n : Nat} {seen : List Lb} {l : Lb}, seen.Nodup → (∀ m ∈ seen, m ∈ js.map (·.lbl)) →
      l ∈ js.map (·.lbl) → (js.map (·.lbl)).length + 1 ≤ n + seen.length →
      (cycleFrom js n seen l).isSome = true
  | 0, seen, l, hd, hs, hl, hlen => by
    have := nodup_length_le hd hs
    omega
  | n + 1, seen, l, hd, hs, hl, hlen => by
    unfold cycleFrom
    split
    · rfl
    · rename_i hc
      obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp (hn l hl)
      simp only [hl']
      have hc' : l ∉ seen := fun h => hc (List.contains_iff_mem.mpr h)
      refine cycleFrom_isSome hn (List.nodup_cons.mpr ⟨hc', hd⟩) (fun m hm => ?_)
        (nextL_mem hl') (by simp only [List.length_cons]; omega)
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hl
      · exact hs m hm

/-- A pending job that is not ready waits for a pending label, so the walk
goes on from the label of every pending job. -/
theorem nextL_isSome {s : Sig} {js : List (Job (s,x))}
    (hw : ∀ j ∈ js, readyIn (js.map (·.lbl)) j = false) :
    ∀ l ∈ js.map (·.lbl), (nextL js l).isSome = true := by
  intro l hl
  unfold nextL
  split
  · rename_i j hf
    have hj : j ∈ js := List.mem_of_find?_eq_some hf
    obtain ⟨l', hl', hc⟩ := allL_false _ _ (hw j hj)
    have hm : l' ∈ waitsFor js j := by
      simp only [waitsFor, List.mem_filter]
      refine ⟨hl', ?_⟩
      cases hc' : (js.map (·.lbl)).contains l' with
      | true => rfl
      | false => rw [hc'] at hc; cases hc
    cases hwf : waitsFor js j with
    | nil => rw [hwf] at hm; cases hm
    | cons _ _ => rfl
  · rename_i hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true rfl) (hf j hj)

/-- A round that types nothing reports a cyclic reference, at the label of a
pending job whose walk comes back to it. -/
theorem stallReason_cyclic {s : Sig} {js : List (Job (s,x))} (hne : js ≠ [])
    (hw : ∀ j ∈ js, readyIn (js.map (·.lbl)) j = false) :
    ∃ j ∈ js, stallReason js = .cyclicRef j.lbl ∧ OnCycle js j := by
  cases js with
  | nil => exact absurd rfl hne
  | cons j0 js' =>
    have hs : (cycleAt (j0 :: js') ((j0 :: js').length + 1)).isSome = true := by
      unfold cycleAt
      exact cycleFrom_isSome (nextL_isSome hw) List.nodup_nil (by simp)
        (List.mem_map_of_mem (List.mem_cons_self ..)) (by simp)
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨j, hj, rfl, hc⟩ := cycleAt_onCycle hl
    exact ⟨j, hj, by simp only [stallReason, hl], hc⟩

/-! ### The jobs of a literal -/

/-- The labels of the heads with no result, in list order. -/
def pendingL {s : Sig} : List (Lb × Head s) → List Lb
  | [] => []
  | (l, .fn _ none) :: hs => l :: pendingL hs
  | _ :: hs => pendingL hs

/-- Every method of the member list has a written result type. -/
def ADms.AllResultsWritten {s : Sig} (ds : ADms s) : Prop :=
  match ds with
  | .dnil => True
  | .dcons (.dty _) ds' => ds'.AllResultsWritten
  | .dcons (.dfun _ o2 _) ds' => o2.isSome = true ∧ ds'.AllResultsWritten
termination_by structural ds

section Jobs
variable {s : Sig} {pf : Lb → FillR (Option (Ty [] s))} {rf : Lb → Ty [] s → Option (Ty [] (s,x))}

/-- A job is the method of the literal at its label.  The method has no result
written or inherited, the job has the parameter type of its head, and its run
is the elaborator on the method's body. -/
theorem jobsF_member :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      ∀ j ∈ jobsF hs ds, j.lbl < ds.length ∧
        (∃ o1, ds.memberAt j.lbl = some (.dfun o1 none j.tm)) ∧
        lookupL hs j.lbl = some (.fn j.par none) ∧ ∀ Γ, j.run Γ = elabF Γ j.tm
  | .dnil, hs, hh, j, hj => by
    simp only [headsOf, Except.ok.injEq] at hh
    subst hh
    simp [jobsF] at hj
  | .dcons (.dty T) ds, hs, hh, j, hj => by
    obtain ⟨hs', h1, rfl⟩ := headsOf_dty hh
    simp only [jobsF] at hj
    obtain ⟨hlt, ⟨o1, hm⟩, hl, hr⟩ := jobsF_member h1 j hj
    have hne : j.lbl ≠ ds.length := Nat.ne_of_lt hlt
    refine ⟨Nat.lt_succ_of_lt hlt, ⟨o1, ?_⟩, ?_, hr⟩
    · simp only [ADms.memberAt, hne, if_false]
      exact hm
    · simp only [lookupL, hne, if_false]
      exact hl
  | .dcons (.dfun o1 o2 t) ds, hs, hh, j, hj => by
    obtain ⟨hs', S, h1, rfl, -⟩ := headsOf_dfun hh
    have tail : j ∈ jobsF hs' ds → j.lbl < (ADms.dcons (.dfun o1 o2 t) ds).length ∧
        (∃ o1', (ADms.dcons (.dfun o1 o2 t) ds).memberAt j.lbl = some (.dfun o1' none j.tm)) ∧
        lookupL ((ds.length, .fn S (o2.or (rf ds.length S))) :: hs') j.lbl =
          some (.fn j.par none) ∧ ∀ Γ, j.run Γ = elabF Γ j.tm := by
      intro hj'
      obtain ⟨hlt, ⟨o1', hm⟩, hl, hr⟩ := jobsF_member h1 j hj'
      have hne : j.lbl ≠ ds.length := Nat.ne_of_lt hlt
      refine ⟨Nat.lt_succ_of_lt hlt, ⟨o1', ?_⟩, ?_, hr⟩
      · simp only [ADms.memberAt, hne, if_false]
        exact hm
      · simp only [lookupL, hne, if_false]
        exact hl
    cases hU : o2.or (rf ds.length S) with
    | none =>
      have ho2 : o2 = none := by
        cases o2 with
        | none => rfl
        | some _ => simp at hU
      subst ho2
      rw [hU] at hj tail
      simp only [jobsF, List.mem_cons] at hj
      rcases hj with rfl | hj
      · refine ⟨Nat.lt_succ_self _, ⟨o1, by simp [ADms.memberAt]⟩, by simp [lookupL],
          fun Γ => ?_⟩
        dsimp only
        unfold elabF
        apply congrArg
        funext r
        cases r <;> rfl
      · exact tail hj
    | some U =>
      rw [hU] at hj tail
      simp only [jobsF] at hj
      exact tail hj

/-- The labels of the jobs are the labels of the heads with no result, in
list order. -/
theorem jobsF_lbls :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      (jobsF hs ds).map (·.lbl) = pendingL hs
  | .dnil, hs, hh => by
    simp only [headsOf, Except.ok.injEq] at hh
    subst hh
    simp [jobsF, pendingL]
  | .dcons (.dty T) ds, hs, hh => by
    obtain ⟨hs', h1, rfl⟩ := headsOf_dty hh
    simp only [jobsF, pendingL]
    exact jobsF_lbls h1
  | .dcons (.dfun o1 o2 t) ds, hs, hh => by
    obtain ⟨hs', S, h1, rfl, -⟩ := headsOf_dfun hh
    cases hU : o2.or (rf ds.length S) with
    | none =>
      simp only [jobsF, pendingL, List.map_cons, jobsF_lbls h1]
    | some U =>
      simp only [jobsF, pendingL]
      exact jobsF_lbls h1

/-- A member list whose results are all written has no job, so a literal with
every result written needs no round. -/
theorem jobsF_written :
    ∀ {ds : ADms s} {hs : List (Lb × Head s)}, headsOf pf rf ds = .ok hs →
      ds.AllResultsWritten → jobsF hs ds = []
  | .dnil, hs, hh, _ => by
    simp only [headsOf, Except.ok.injEq] at hh
    subst hh
    simp [jobsF]
  | .dcons (.dty T) ds, hs, hh, hw => by
    obtain ⟨hs', h1, rfl⟩ := headsOf_dty hh
    simp only [ADms.AllResultsWritten] at hw
    simp only [jobsF]
    exact jobsF_written h1 hw
  | .dcons (.dfun o1 o2 t) ds, hs, hh, hw => by
    obtain ⟨hs', S, h1, rfl, -⟩ := headsOf_dfun hh
    simp only [ADms.AllResultsWritten] at hw
    obtain ⟨h2, hw⟩ := hw
    obtain ⟨U, rfl⟩ := Option.isSome_iff_exists.mp h2
    have hU : (some U).or (rf ds.length S) = some U := rfl
    rw [hU]
    simp only [jobsF]
    exact jobsF_written h1 hw

end Jobs

/-- The self type is formed once every head with no result has one in
`known`. -/
theorem fullSelf_isSome {s : Sig} {known : List (Lb × Ty [] (s,x))} :
    ∀ {hs : List (Lb × Head s)}, (∀ l ∈ pendingL hs, (lookupL known l).isSome = true) →
      (fullSelf hs known).isSome = true
  | [], _ => rfl
  | (l, .typ T) :: hs, h => by
    simp only [pendingL] at h
    simp only [fullSelf, Option.isSome_map]
    exact fullSelf_isSome h
  | (l, .fn S (some U)) :: hs, h => by
    simp only [pendingL] at h
    simp only [fullSelf, Option.isSome_map]
    exact fullSelf_isSome h
  | (l, .fn S none) :: hs, h => by
    simp only [pendingL, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hl, h⟩ := h
    simp only [fullSelf]
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp hl
    simp only [hU, Option.isSome_map]
    exact fullSelf_isSome h

/-- A label of a typed job has a result in the table of typed jobs. -/
theorem lookupL_known {s : Sig} {l : Lb} :
    ∀ {out : List (Done s)}, l ∈ out.map (·.lbl) → (lookupL (Done.known out) l).isSome = true
  | [], h => by simp at h
  | e :: out, h => by
    simp only [Done.known, List.map_cons, lookupL]
    split
    · rfl
    · rename_i hne
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hne
      · exact lookupL_known h

/-- With no job, forming a self type draws nothing and gives the self type of
the heads. -/
theorem formSelfF_nil {s : Sig} (Γ : Ctx [] s) (hs : List (Lb × Head (s,x))) :
    formSelfF Γ hs [] = Fu.ret (match fullSelf hs [] with
      | some T => .ok (T, [])
      | none => .error .mismatch) := by
  funext t
  rfl

/-- A round that ends types each of its jobs once, in order. -/
theorem roundF_lbls {s : Sig} {Γ : Ctx [] s} {P : Ty [] (s,x)} :
    ∀ {js : List (Job (s,x))} {t : Tank} {es : List (Done (s,x))} {t' : Tank},
      roundF Γ P js t = (.ok es, t') → es.map (·.lbl) = js.map (·.lbl)
  | [], t, es, t', h => by
    simp only [roundF, Fu.ret, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | j :: js, t, es, t', h => by
    unfold roundF at h
    cases hr : runJobF Γ P j t with
    | mk r t1 =>
      simp only [Fu.bind, hr] at h
      cases r with
      | error _ => simp [Fu.ret] at h
      | ok e =>
        cases hr' : roundF Γ P js t1 with
        | mk r' t2 =>
          simp only [Fu.bind, hr'] at h
          cases r' with
          | error _ => simp [Fu.ret] at h
          | ok es' =>
            simp only [Fu.ret, Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [List.map_cons, (runJobF_least hr).1, roundF_lbls hr']

/-- A list split by a test, read back by labels. -/
theorem mem_split {s : Sig} (p : Job s → Bool) (js : List (Job s)) (l : Lb) :
    (l ∈ (js.filter p).map (·.lbl) ∨ l ∈ (js.filter fun k => !p k).map (·.lbl)) ↔
      l ∈ js.map (·.lbl) := by
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro (⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩) <;> exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    cases hp : p k with
    | true => exact .inl ⟨k, ⟨hk, hp⟩, rfl⟩
    | false => exact .inr ⟨k, ⟨hk, by simp [hp]⟩, rfl⟩

/-- Rounds that end have typed every job they were given. -/
theorem roundsF_lbls {s : Sig} {Γ : Ctx [] s} {hs : List (Lb × Head (s,x))} :
    ∀ {n : Nat} {js : List (Job (s,x))} {done : List (Done (s,x))} {t : Tank}
      {out : List (Done (s,x))} {t' : Tank},
      roundsF Γ hs n js done t = (.ok out, t') →
        ∀ l, l ∈ out.map (·.lbl) ↔ l ∈ done.map (·.lbl) ∨ l ∈ js.map (·.lbl)
  | _, [], done, t, out, t', h => by
    unfold roundsF at h
    simp only [Fu.ret, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro l
    simp
  | 0, j :: js, _, t, _, _, h => by
    unfold roundsF at h
    simp [Fu.ret] at h
  | n + 1, j :: js, done, t, out, t', h => by
    unfold roundsF at h
    split at h
    · simp [Fu.ret] at h
    · cases hr : roundF Γ (probeSelf hs (Done.known done))
          ((j :: js).filter (picks (j :: js))) t with
      | mk r t1 =>
        simp only [Fu.bind, hr] at h
        cases r with
        | error _ => simp [Fu.ret] at h
        | ok typed =>
          simp only at h
          intro l
          rw [roundsF_lbls h l, List.map_append, List.mem_append, roundF_lbls hr,
            ← mem_split (picks (j :: js)) (j :: js) l, or_assoc]

/-- Rounds that end on the jobs of a literal form its self type, and that
self type is in lockstep with the members.  So forming a self type is a
mismatch only through a job. -/
theorem formSelfF_jobs {s : Sig} {Γ : Ctx [] s} {pf : Lb → FillR (Option (Ty [] (s,x)))}
    {rf : Lb → Ty [] (s,x) → Option (Ty [] ((s,x),x))} {ds : ADms (s,x)}
    {hs : List (Lb × Head (s,x))} {t : Tank} {out : List (Done (s,x))} {t' : Tank}
    (hh : headsOf pf rf ds = .ok hs)
    (h : roundsF Γ hs ((jobsF hs ds).length + 1) (jobsF hs ds) [] t = (.ok out, t')) :
    ∃ T, formSelfF Γ hs (jobsF hs ds) t = (.ok (T, out), t') ∧
      fullSelf hs (Done.known out) = some T ∧ Lockstep ds T := by
  have hk : ∀ l ∈ pendingL hs, (lookupL (Done.known out) l).isSome = true := by
    intro l hl
    rw [← jobsF_lbls hh] at hl
    exact lookupL_known ((roundsF_lbls h l).mpr (.inr hl))
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (fullSelf_isSome hk)
  refine ⟨T, ?_, hT, fullSelf_lockstep hh hT⟩
  unfold formSelfF
  simp only [Fu.bind, h, hT, Fu.ret]

/-- The self type a formation gives is the one the heads give with the results
of the rounds, so it is in lockstep with the members. -/
theorem formSelfF_lockstep {s : Sig} {Γ : Ctx [] s} {pf : Lb → FillR (Option (Ty [] (s,x)))}
    {rf : Lb → Ty [] (s,x) → Option (Ty [] ((s,x),x))} {ds : ADms (s,x)}
    {hs : List (Lb × Head (s,x))} {js : List (Job (s,x))} {t : Tank} {T : Ty [] (s,x)}
    {done : List (Done (s,x))} (hh : headsOf pf rf ds = .ok hs)
    (h : (formSelfF Γ hs js t).1 = .ok (T, done)) :
    fullSelf hs (Done.known done) = some T ∧ Lockstep ds T := by
  unfold formSelfF at h
  cases hr : roundsF Γ hs (js.length + 1) js [] t with
  | mk r t1 =>
    simp only [Fu.bind, hr] at h
    cases r with
    | error _ => simp [Fu.ret] at h
    | ok out =>
      simp only [Fu.ret] at h
      cases hf : fullSelf hs (Done.known out) with
      | none => simp [hf] at h
      | some T' =>
        simp only [hf, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hf, fullSelf_lockstep hh hf⟩

/-! ## The fill is framed

The goal reading, the rounds and the fill are built from the combinators of
`Fuel.lean` and from framed computations of the typer, so each keeps a marked
tank, never adds fuel, and does the same with more fuel. -/

/-- The fallback is framed when the computation it runs is. -/
theorem retryF_framed {α : Type} (first : FillR α) {b : Fu (FillR α)} (hb : Framed b) :
    Framed (retryF first b) where
  absorbs t ht := by simp [retryF, ht]
  spends t := by
    unfold retryF
    cases ht : t.out
    · have hs := hb.spends t
      cases hbt : b t with
      | mk r t' =>
        rw [hbt] at hs
        cases r with
        | ok _ => exact hs
        | error _ => cases first <;> exact hs
    · simp
  shift := by
    intro t r t' h ho k
    unfold retryF at h ⊢
    cases ht : t.out
    · have htk : (t.add k).out = false := by simp [ht]
      simp only [ht, htk, Bool.false_eq_true, if_false] at h ⊢
      cases hbt : b t with
      | mk r0 t0 =>
        rw [hbt] at h
        have ho0 : t0.out = false := by
          cases r0 <;> (try cases first) <;> simp only [Prod.mk.injEq] at h <;> rw [h.2] <;>
            exact ho
        rw [hb.shift t r0 t0 hbt ho0 k]
        cases r0 <;> (try cases first) <;> simp only [Prod.mk.injEq] at h ⊢ <;>
          exact ⟨h.1, by rw [h.2]⟩
    · simp only [ht, if_true, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [ht] at ho

/-- A goal site is framed when the fill it runs is, at every goal. -/
theorem fillAtF_framed {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (a : ATm s)
    {fill : Option (Ty [] s) → Fu (FillR (ATm s))} (hf : ∀ g, Framed (fill g)) :
    Framed (fillAtF Γ G a fill) := by
  unfold fillAtF
  split
  · exact ret_framed _
  · refine bind_framed (hf _) fun r => ?_
    cases r with
    | ok a' =>
      refine bind_framed (checkF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact ret_framed _
      | none => exact retryF_framed _ (hf none)
    | error e => exact retryF_framed _ (hf none)

theorem abstractDeclF_framed {s : Sig} (Γ : Ctx [] s) (l : Lb) :
    ∀ G, Framed (abstractDeclF Γ l G)
  | .TSel (.abs y) L => bind_framed (members_framed _ _ _) fun _ => ret_framed _
  | .TAnd A B => by
    refine bind_framed (abstractDeclF_framed Γ l A) fun b => ?_
    cases b
    · exact abstractDeclF_framed Γ l B
    · exact ret_framed _
  | .TSel (.conc _) _ => ret_framed _
  | .TBot => ret_framed _
  | .TTop => ret_framed _
  | .TFun _ _ _ => ret_framed _
  | .TTyp _ _ _ => ret_framed _
  | .TBind _ => ret_framed _
  | .TOr _ _ => ret_framed _

theorem meetOneF_framed {s : Sig} (Γ : Ctx [] s) (S : Ty [] s) (U : Ty [] (s,x)) :
    ∀ p, Framed (meetOneF Γ S U p)
  | .none => ret_framed _
  | .bad => ret_framed _
  | .one S2 U2 => by
    rw [meetOneF]
    split
    · exact ret_framed _
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact ret_framed _
      | none =>
        refine bind_framed (subF_framed _ _ _) fun o' => ?_
        cases o' with
        | some _ => exact ret_framed _
        | none => exact ret_framed _

theorem meetAllF_framed {s : Sig} (Γ : Ctx [] s) :
    ∀ ds : List (Ty [] s × Ty [] (s,x)), Framed (meetAllF Γ ds)
  | [] => ret_framed _
  | (S, U) :: rest => bind_framed (meetAllF_framed Γ rest) fun p => meetOneF_framed Γ S U p

theorem partF_framed {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (l : Lb) : Framed (partF Γ G l) := by
  refine bind_framed (abstractDeclF_framed _ _ _) fun b => ?_
  cases b
  · exact meetAllF_framed _ _
  · exact ret_framed _

theorem sameDomF_framed {s : Sig} (Γ : Ctx [] s) : ∀ o p, Framed (sameDomF Γ o p)
  | some S, .one S' _ => by
    rw [sameDomF]
    split
    · exact ret_framed _
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact bind_framed (subF_framed _ _ _) fun _ => ret_framed _
      | none => exact ret_framed _
  | some _, .none => ret_framed _
  | some _, .bad => ret_framed _
  | none, _ => ret_framed _

theorem inheritF_framed {s : Sig} (Γ : Ctx [] s) {part : Lb → Fu (MPart s)}
    (hp : ∀ l, Framed (part l)) : ∀ ds, Framed (inheritF Γ part ds)
  | .dnil => ret_framed _
  | .dcons (.dty _) ds => inheritF_framed Γ hp ds
  | .dcons (.dfun o1 o2 _) ds => by
    refine bind_framed (inheritF_framed Γ hp ds) fun rest => ?_
    dsimp only
    split
    · exact ret_framed _
    · exact bind_framed (hp _) fun p => bind_framed (sameDomF_framed _ _ _) fun _ => ret_framed _

/-- Reading the goal of a literal is framed. -/
theorem readGoalF_framed {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) (ds : ADms (s,x)) :
    Framed (readGoalF Γ g ds) := by
  unfold readGoalF
  cases g with
  | none => exact ret_framed _
  | some G =>
    exact bind_framed (dealiasAt_framed _ _) fun G' =>
      inheritF_framed _ (fun l => partF_framed _ _ l) ds

mutual

/-- The fill is framed. -/
theorem fillF_framed {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) :
    (a : ATm s) → Framed (fillF Γ g a)
  | .var x => by
    rw [fillF]
    split
    · exact ret_framed _
    · exact ret_framed _
  | .asc t T => by
    rw [fillF]
    split
    · exact ret_framed _
    · exact bind_framed (fillAtF_framed _ _ _ fun g' => fillF_framed Γ g' t) fun _ => ret_framed _
  | .app t l u => by
    rw [fillF]
    split
    · exact ret_framed _
    · refine bind_framed (fillF_framed Γ none t) fun r => ?_
      cases r with
      | error _ => exact ret_framed _
      | ok t' =>
        dsimp only
        split
        · exact ret_framed _
        · refine bind_framed (argGoalF_framed _ _ _) fun o => ?_
          refine bind_framed ?_ fun _ => ret_framed _
          cases o with
          | some F => exact fillAtF_framed _ _ _ fun g' => fillF_framed Γ g' u
          | none => exact fillF_framed Γ none u
  | .obj o ds => by
    rw [fillF]
    split
    · exact ret_framed _
    · split
      · exact bind_framed (fillDmsF_framed _ [] ds _) fun _ => ret_framed _
      · refine bind_framed (readGoalF_framed _ _ _) fun rd => ?_
        split
        · exact ret_framed _
        · rename_i hs _
          refine bind_framed (formSelfF_framed _ hs (jobsF_framed ds hs)) fun r => ?_
          cases r with
          | error _ => exact ret_framed _
          | ok p =>
            obtain ⟨T, done⟩ := p
            exact bind_framed (fillDmsF_framed _ done ds T) fun _ => ret_framed _

/-- Filling the members of a literal is framed. -/
theorem fillDmsF_framed {s : Sig} (Γ : Ctx [] s) (done : List (Done s)) :
    (ds : ADms s) → (T : Ty [] s) → Framed (fillDmsF Γ done ds T)
  | .dnil, T => by
    rw [fillDmsF]
    exact ret_framed _
  | .dcons (.dty T') ds', T => by
    cases T with
    | TAnd _ TS => exact bind_framed (fillDmsF_framed Γ done ds' TS) fun _ => ret_framed _
    | _ => exact ret_framed _
  | .dcons (.dfun o1 o2 t) ds', T => by
    cases T with
    | TAnd A TS =>
      cases A with
      | TFun _ T11 T12 =>
        refine bind_framed (fillDmsF_framed Γ done ds' TS) fun r => ?_
        cases r with
        | error _ => exact ret_framed _
        | ok ds'' =>
          dsimp only
          split
          · exact ret_framed _
          · exact bind_framed (fillAtF_framed _ _ _ fun g' => fillF_framed _ g' t)
              fun _ => ret_framed _
      | _ => exact ret_framed _
    | _ => exact ret_framed _

/-- The jobs of a member list run framed computations. -/
theorem jobsF_framed {s : Sig} :
    (ds : ADms s) → ∀ hs : List (Lb × Head s), ∀ j ∈ jobsF hs ds, ∀ Γ, Framed (j.run Γ)
  | .dnil, hs => by
    intro j hj
    rcases hs with _ | ⟨⟨l, _ | ⟨S, _ | U⟩⟩, hs'⟩ <;> simp [jobsF] at hj
  | .dcons (.dty T) ds', hs => by
    intro j hj
    rcases hs with _ | ⟨⟨l, h⟩, hs'⟩
    · simp [jobsF] at hj
    · rcases h with _ | ⟨S, _ | U⟩ <;> simp only [jobsF] at hj <;> exact jobsF_framed ds' hs' j hj
  | .dcons (.dfun o1 o2 t) ds', hs => by
    intro j hj
    rcases hs with _ | ⟨⟨l, h⟩, hs'⟩
    · simp [jobsF] at hj
    · rcases h with _ | ⟨S, _ | U⟩
      · simp only [jobsF] at hj
        exact jobsF_framed ds' hs' j hj
      · simp only [jobsF, List.mem_cons] at hj
        rcases hj with rfl | hj
        · intro Γ
          dsimp only
          refine bind_framed (fillF_framed Γ none t) fun r => ?_
          cases r with
          | ok t' => exact bind_framed (synthF_framed _ _) fun _ => ret_framed _
          | error _ => exact ret_framed _
        · exact jobsF_framed ds' hs' j hj
      · simp only [jobsF] at hj
        exact jobsF_framed ds' hs' j hj

end

/-- Elaboration with no goal is framed. -/
theorem elabF_framed {s : Sig} (Γ : Ctx [] s) (a : ATm s) : Framed (elabF Γ a) := by
  refine bind_framed (fillF_framed Γ none a) fun r => ?_
  cases r with
  | ok a' => exact bind_framed (synthF_framed _ _) fun _ => ret_framed _
  | error _ => exact ret_framed _

/-- Elaboration at a goal is framed. -/
theorem elabChkF_framed {s : Sig} (Γ : Ctx [] s) (a : ATm s) (G : Ty [] s) :
    Framed (elabChkF Γ a G) := by
  refine bind_framed (fillAtF_framed _ _ _ fun g => fillF_framed Γ g a) fun r => ?_
  cases r with
  | ok a' => exact bind_framed (checkF_framed _ _ _) fun _ => ret_framed _
  | error _ => exact ret_framed _

/-! ## The fill fills

The fill rebuilds the term it is given and writes a self type into a literal
that lacks one.  A method body typed in a round comes from the rounds, and the
fill decides that it fills the method's body.  So every term the fill returns
fills its input and is one the typer takes as it is. -/

/-- Every answer of `c`, from any tank, has the property `P`. -/
def Always {α : Type} (P : α → Prop) (c : Fu α) : Prop := ∀ t, P (c t).1

theorem always_ret {α : Type} {P : α → Prop} {a : α} (h : P a) : Always P (Fu.ret a) :=
  fun _ => h

theorem always_bind {α β : Type} {P : β → Prop} {Q : α → Prop} {c : Fu α} {f : α → Fu β}
    (hc : Always Q c) (hf : ∀ a, Q a → Always P (f a)) : Always P (Fu.bind c f) := by
  intro t
  have h := hc t
  simp only [Fu.bind]
  cases hct : c t with
  | mk a t1 =>
    rw [hct] at h
    exact hf a h t1

theorem always_true {α : Type} (c : Fu α) : Always (fun _ => True) c := fun _ => trivial

theorem always_retry {α : Type} {P : FillR α → Prop} {first : FillR α} {b : Fu (FillR α)}
    (h1 : P first) (hb : Always P b) : Always P (retryF first b) := by
  intro t
  unfold retryF
  cases ht : t.out
  · have h := hb t
    simp only [Bool.false_eq_true, if_false]
    cases hbt : b t with
    | mk r t' =>
      rw [hbt] at h
      cases r with
      | ok _ => exact h
      | error _ => cases first <;> exact h1
  · simpa using h1

/-- A filled term fills `a` and the typer takes it as it is. -/
def FillOk {s : Sig} (a : ATm s) : FillR (ATm s) → Prop
  | .ok a' => a.fills a' = true ∧ a'.landed = true
  | .error _ => True

/-- Filled members fill `ds` and the typer takes them as they are. -/
def DmsFillOk {s : Sig} (ds : ADms s) : FillR (ADms s) → Prop
  | .ok ds' => ds.fills ds' = true ∧ ds'.landed = true
  | .error _ => True

/-- A goal site returns a term that fills `a` when the fill it runs does. -/
theorem fillAtF_fills {s : Sig} (Γ : Ctx [] s) (G : Ty [] s) (a : ATm s)
    {fill : Option (Ty [] s) → Fu (FillR (ATm s))} (hf : ∀ g, Always (FillOk a) (fill g)) :
    Always (FillOk a) (fillAtF Γ G a fill) := by
  unfold fillAtF
  split
  · rename_i h
    exact always_ret ⟨fills_refl a, h⟩
  · refine always_bind (hf _) fun r hr => ?_
    cases r with
    | ok a' =>
      refine always_bind (always_true _) fun o _ => ?_
      cases o with
      | some _ => exact always_ret hr
      | none => exact always_retry hr (hf none)
    | error e => exact always_retry trivial (hf none)

mutual

/-- Every answer of the fill fills the term. -/
theorem fillF_always {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) :
    (a : ATm s) → Always (FillOk a) (fillF Γ g a)
  | .var x => by
    rw [fillF]
    split
    · rename_i h
      exact always_ret ⟨fills_refl _, h⟩
    · exact always_ret ⟨fills_refl _, rfl⟩
  | .asc t T => by
    rw [fillF]
    split
    · rename_i h
      exact always_ret ⟨fills_refl _, h⟩
    · refine always_bind (fillAtF_fills _ _ _ fun g' => fillF_always Γ g' t) fun r hr => ?_
      apply always_ret
      cases r with
      | error _ => trivial
      | ok t' =>
        simp only [FillOk, Except.map, ATm.fills, ATm.landed, decide_true, Bool.and_true] at hr ⊢
        exact hr
  | .app t l u => by
    rw [fillF]
    split
    · rename_i h
      exact always_ret ⟨fills_refl _, h⟩
    · refine always_bind (fillF_always Γ none t) fun r hr => ?_
      cases r with
      | error _ => exact always_ret trivial
      | ok t' =>
        dsimp only
        split
        · rename_i hu
          apply always_ret
          simp only [FillOk, ATm.fills, ATm.landed, decide_true, Bool.and_true, Bool.and_eq_true]
            at hr ⊢
          exact ⟨⟨hr.1, fills_refl u⟩, hr.2, hu⟩
        · have hu : ∀ o : Option (Ty [] s), Always (FillOk u)
              (match o with
                | some F => fillAtF Γ F u (fun g' => fillF Γ g' u)
                | none => fillF Γ none u) := by
            intro o
            cases o with
            | some F => exact fillAtF_fills _ _ _ fun g' => fillF_always Γ g' u
            | none => exact fillF_always Γ none u
          refine always_bind (always_true _) fun o _ => ?_
          refine always_bind (hu o) fun r' hr' => ?_
          apply always_ret
          cases r' with
          | error _ => trivial
          | ok u' =>
            simp only [FillOk, Except.map, ATm.fills, ATm.landed, decide_true, Bool.and_true,
              Bool.and_eq_true] at hr hr' ⊢
            exact ⟨⟨hr.1, hr'.1⟩, hr.2, hr'.2⟩
  | .obj o ds => by
    rw [fillF]
    split
    · rename_i h
      exact always_ret ⟨fills_refl _, h⟩
    · split
      · rename_i T hT
        refine always_bind (fillDmsF_always _ [] ds _) fun r hr => ?_
        apply always_ret
        cases r with
        | error _ => trivial
        | ok ds' =>
          have hs : slotAgrees o (some T) = true := by
            cases o with
            | none => rfl
            | some T0 =>
              simp only [Option.orElse, HOrElse.hOrElse, OrElse.orElse, Option.some.injEq] at hT
              subst hT
              exact slotAgrees_refl _
          simp only [DmsFillOk] at hr
          simp only [FillOk, Except.map, ATm.fills, ATm.landed, hs, hr.1, hr.2, Option.isSome_some,
            Bool.true_or, Bool.and_self, and_self]
      · rename_i hT
        have ho : o = none := by
          cases o with
          | none => rfl
          | some _ => simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hT
        subst ho
        refine always_bind (always_true _) fun rd _ => ?_
        split
        · exact always_ret trivial
        · refine always_bind (always_true _) fun r _ => ?_
          cases r with
          | error _ => exact always_ret trivial
          | ok p =>
            obtain ⟨T, done⟩ := p
            refine always_bind (fillDmsF_always _ done ds T) fun r' hr' => ?_
            apply always_ret
            cases r' with
            | error _ => trivial
            | ok ds' =>
              simp only [DmsFillOk] at hr'
              simp only [FillOk, Except.map, ATm.fills, ATm.landed, slotAgrees, hr'.1, hr'.2,
                Option.isSome_some, Bool.true_or, Bool.and_self, and_self]

/-- Every answer of the fill of members fills them. -/
theorem fillDmsF_always {s : Sig} (Γ : Ctx [] s) (done : List (Done s)) :
    (ds : ADms s) → (T : Ty [] s) → Always (DmsFillOk ds) (fillDmsF Γ done ds T)
  | .dnil, T => by
    rw [fillDmsF]
    exact always_ret ⟨fillsDms_refl _, rfl⟩
  | .dcons (.dty T') ds', T => by
    cases T with
    | TAnd _ TS =>
      refine always_bind (fillDmsF_always Γ done ds' TS) fun r hr => ?_
      apply always_ret
      cases r with
      | error _ => trivial
      | ok ds'' =>
        simp only [DmsFillOk, Except.map, ADms.fills, ADm.fills, ADms.landed, ADm.landed,
          decide_true, Bool.true_and] at hr ⊢
        exact hr
    | _ => exact always_ret trivial
  | .dcons (.dfun o1 o2 t) ds', T => by
    cases T with
    | TAnd A TS =>
      cases A with
      | TFun _ T11 T12 =>
        refine always_bind (fillDmsF_always Γ done ds' TS) fun r hr => ?_
        cases r with
        | error _ => exact always_ret trivial
        | ok ds'' =>
          dsimp only
          simp only [DmsFillOk] at hr
          split
          · rename_i e _
            apply always_ret
            split
            · rename_i hd
              simp only [Bool.and_eq_true] at hd
              simp only [DmsFillOk, ADms.fills, ADm.fills, ADms.landed, ADm.landed, decide_true,
                Bool.true_and, hd.1, hd.2, hr.1, hr.2, and_self]
            · trivial
          · refine always_bind (fillAtF_fills _ _ _ fun g' => fillF_always _ g' t) fun r' hr' => ?_
            apply always_ret
            cases r' with
            | error _ => trivial
            | ok t' =>
              simp only [FillOk] at hr'
              simp only [DmsFillOk, Except.map, ADms.fills, ADm.fills, ADms.landed, ADm.landed,
                decide_true, Bool.true_and, hr'.1, hr'.2, hr.1, hr.2, and_self]
      | _ => exact always_ret trivial
    | _ => exact always_ret trivial

end

/-- A term the fill returns fills its input, so it differs from it only in
self types written where the input has none, and the typer takes it as it
is. -/
theorem fillF_fills {s : Sig} {Γ : Ctx [] s} {g : Option (Ty [] s)} {a a' : ATm s} {t : Tank}
    (h : (fillF Γ g a t).1 = .ok a') : a.fills a' = true ∧ a'.landed = true := by
  have hf := fillF_always Γ g a t
  rw [h] at hf
  exact hf

/-- The term the elaborator types fills its input, and the candidates are the
typer's on it. -/
theorem elabF_fills {s : Sig} {Γ : Ctx [] s} {a : ATm s} {t : Tank} {f : Filled Γ}
    (h : (elabF Γ a t).1 = .ok f) :
    a.fills f.1 = true ∧ f.1.landed = true ∧ ∃ t1, (synthF Γ f.1 t1).1 = f.2 := by
  unfold elabF at h
  cases hf : fillF Γ none a t with
  | mk r t1 =>
    simp only [Fu.bind, hf] at h
    cases r with
    | error _ => simp [Fu.ret] at h
    | ok a' =>
      have hfill := fillF_fills (Γ := Γ) (g := none) (t := t) (by rw [hf])
      cases h
      exact ⟨hfill.1, hfill.2, t1, rfl⟩

/-- The term the elaborator checks at a goal fills its input, and the check
is the typer's on it. -/
theorem elabChkF_fills {s : Sig} {Γ : Ctx [] s} {a : ATm s} {G : Ty [] s} {t : Tank}
    {f : FilledChk Γ G} (h : (elabChkF Γ a G t).1 = .ok f) :
    a.fills f.1 = true ∧ f.1.landed = true ∧ ∃ t1, (checkF Γ f.1 G t1).1 = f.2 := by
  unfold elabChkF at h
  have hall := fillAtF_fills Γ G a (fun g => fillF_always Γ g a) t
  cases hf : fillAtF Γ G a (fun g => fillF Γ g a) t with
  | mk r t1 =>
    rw [hf] at hall
    simp only [Fu.bind, hf] at h
    cases r with
    | error _ => simp [Fu.ret] at h
    | ok a' =>
      cases h
      exact ⟨hall.1, hall.2, t1, rfl⟩

/-- Every candidate the typer gives a literal ends in `T_Obj`, at the self
type the literal has or `selfOf?` computes. -/
theorem synthF_obj_head {s : Sig} {Γ : Ctx [] s} {o : Option (Ty [] (s,x))} {ds : ADms (s,x)}
    {t : Tank} : ∀ c ∈ (synthF Γ (.obj o ds) t).1,
      ∃ T d, (o <|> selfOf? ds.erase) = some T ∧ c = ⟨.TBind T, .T_Obj d⟩ := by
  intro c hc
  rw [synthF] at hc
  cases hT : (o <|> selfOf? ds.erase) with
  | none => simp [hT, Fu.ret] at hc
  | some T =>
    simp only [hT, Fu.bind] at hc
    cases hd : checkDmsF (Γ.cons T) ds T t with
    | mk od t1 =>
      rw [hd] at hc
      cases od with
      | none => simp [Fu.ret, listO] at hc
      | some d =>
        simp only [Fu.ret, Option.map, listO, List.mem_singleton] at hc
        exact ⟨T, d, rfl, hc⟩

/-- A literal without a self type is elaborated as a literal the typer takes as
it is: the filled term is a literal, and the candidates are the typer's on
it.  So each one ends in `T_Obj` (`synthF_obj_head`). -/
theorem obj_none_landed {s : Sig} {Γ : Ctx [] s} {ds : ADms (s,x)} {t : Tank} {f : Filled Γ}
    (h : (elabF Γ (.obj none ds) t).1 = .ok f) :
    ∃ o' ds' t1, f.1 = .obj o' ds' ∧ f.1.landed = true ∧ (synthF Γ f.1 t1).1 = f.2 := by
  obtain ⟨hfill, hl, t1, hs⟩ := elabF_fills h
  obtain ⟨a', cs⟩ := f
  cases a' with
  | obj o' ds' => exact ⟨o', ds', t1, rfl, hl, hs⟩
  | var _ => simp [ATm.fills] at hfill
  | app _ _ _ => simp [ATm.fills] at hfill
  | asc _ _ => simp [ATm.fills] at hfill

/-! ## Checks

Each check elaborates a surface program at `defaultFuel` in the kernel.  It
states the type and the tank left, or the reason and the tank left.  Every
tank below ends unmarked, so the fuel did not limit the verdict. -/

namespace InferChecks

open TyperChecks

/-- The verdict of a closed elaboration. -/
inductive Outcome where
  /-- The filled program has this type. -/
  | typed (T : Ty [] [])
  /-- The program is rejected for this reason. -/
  | rejected (r : EReason)
  /-- The program does not resolve. -/
  | unresolved
deriving DecidableEq

/-- Whether the program is typed. -/
def Outcome.isTyped : Outcome → Bool
  | .typed _ => true
  | _ => false

/-- The verdict of a closed program after resolution, from a full tank of `n`
units, and the tank left. -/
def inferAt (Λ : LabelTable) (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  match resolve Λ e with
  | some a =>
      match elabTopF n a with
      | (.ok ⟨_, c⟩, t) => (.typed c.ty, t)
      | (.error r, t) => (.rejected r, t)
  | none => (.unresolved, ⟨n, false⟩)

/-- The filled program, when elaboration succeeds. -/
def filledAt (Λ : LabelTable) (e : STm) (n : Nat := defaultFuel) : Option (ATm []) :=
  match resolve Λ e with
  | some a =>
      match elabTopF n a with
      | (.ok ⟨a', _⟩, _) => some a'
      | (.error _, _) => none
  | none => none

/-! ### Programs the typer takes as they are

The elaborator gives them the typer's type at the typer's fuel. -/

example : inferAt recArgTable recArgSrc = (.typed .TTop, ⟨defaultFuel - 117, false⟩) := by
  decide +kernel

example : inferAt paperLstTable paperLstSrc
    = (.typed (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody), ⟨defaultFuel - 1229, false⟩) := by
  decide +kernel

/-- `paper_lst` with every self type erased is still a program the typer takes
as it is, since every method is annotated. -/
example : inferAt paperLstTable paperLstSrc.eraseSelf
    = (.typed (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody), ⟨defaultFuel - 1229, false⟩) := by
  decide +kernel

/-! ### A call argument

`recArg` with the self type of its argument erased.  The argument's goal is
the domain `μ(z. {def f(y : ⊤) : z.B})` of `apply`.  The method `f` takes the
parameter type `⊤` and the result `z.B` from it, as `Namer.inferredResultType`
takes `inherited`.  The written self type declared `f` at `z.A`. -/

/-- The self type the argument takes: its own type members `A` and `B`, and `f`
at the domain's declaration. -/
def recArgArgSelf : Ty [] ([],x) :=
  .TAnd (.TTyp 2 (.TSel (.abs .here) 1) (.TSel (.abs .here) 1))
    (.TAnd (.TTyp 1 .TTop .TTop) (.TAnd (.TFun 0 .TTop (.TSel (.abs (.there .here)) 1)) .TTop))

/-- `recArg` with that self type written into its argument. -/
def recArgFilled : ATm [] :=
  match resolve recArgTable recArgSrc with
  | some (.app t l (.obj _ ds)) => .app t l (.obj (some recArgArgSelf) ds)
  | _ => .obj none .dnil

example : inferAt recArgTable recArgSrcA = (.typed .TTop, ⟨defaultFuel - 113, false⟩) := by
  decide +kernel

example : filledAt recArgTable recArgSrcA = some recArgFilled := by decide +kernel

/-- The fill agrees with every slot the program writes, and the typer takes it
as it is. -/
example : (resolve recArgTable recArgSrcA).map (·.fills recArgFilled) = some true ∧
    recArgFilled.landed = true := by
  decide +kernel

/-- With no self type at all, the receiver gets no goal, and `apply` has no
parameter type. -/
example : inferAt recArgTable recArgSrcS
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- `curryCall`'s argument has the domain `⊤`, which declares no method. -/
example : inferAt curryCallTable curryCallSrcA
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

/-! ### Two method types at the callee's label

`y` has two method types at `g`, an intersection.  The argument's goal is the
formal every other formal is below. -/

/-- Two formals whose domains declare `f` at `⊤` with different results. -/
def twoFormalsSrc : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : ⊤) : { type A : ⊥ .. ⊤ } }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q) = q }) }

/-- Two formals whose domains declare `f` at `⊤` and at `{A : ⊥..⊤}`.  The
second formal is the larger. -/
def twoDomainsSrc : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : { type A : ⊥ .. ⊤ }) : ⊤ }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q) = q }) }

/-- Two formals whose domains declare `f` at `{A : ⊥..⊤}` and at
`{B : ⊥..⊤}`, which the subtyping goal does not order. -/
def twoDomainsIncSrc : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : { type A : ⊥ .. ⊤ }) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : { type B : ⊥ .. ⊤ }) : ⊤ }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q) = q }) }

/-- Two formals whose domains declare `f` at `⊤` and at `⊤ ∧ ⊤`. -/
def eqvArgSrc : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : ⊤ ∧ ⊤) : ⊤ }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q) = q }) }

/-- The table of the first three. -/
def formalsTable : LabelTable := [("g", 0), ("f", 0), ("A", 0), ("B", 1), ("m", 0)]

example : labelsOfProgram [("g", 0), ("f", 0), ("A", 0), ("B", 1)] twoDomainsIncSrc
    = some formalsTable := by decide

/-- The type of the literal `c` in the first program. -/
abbrev twoFormalsSelf : Ty [] ([],x) :=
  .TAnd (.TFun 0 (.TAnd (.TFun 0 (.TFun 0 .TTop .TTop) .TTop)
    (.TFun 0 (.TFun 0 .TTop (.TTyp 0 .TBot .TTop)) .TTop)) .TTop) .TTop

example : inferAt formalsTable twoFormalsSrc
    = (.typed (.TBind twoFormalsSelf), ⟨defaultFuel - 43, false⟩) := by
  decide +kernel

example : (inferAt formalsTable twoDomainsSrc).1.isTyped = true ∧
    (inferAt formalsTable twoDomainsSrc).2 = ⟨defaultFuel - 78, false⟩ := by
  decide +kernel

example : inferAt formalsTable twoDomainsIncSrc
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel - 22, false⟩) := by
  decide +kernel

example : (inferAt formalsTable eqvArgSrc).1.isTyped = true ∧
    (inferAt formalsTable eqvArgSrc).2 = ⟨defaultFuel - 49, false⟩ := by
  decide +kernel

/-! ### An ascription

The ascribed type is the literal's parent.  Its declarations at a label meet. -/

/-- The self type of a literal under an ascription. -/
def ascSelf? : Option (ATm []) → Option (Ty [] ([],x))
  | some (.asc (.obj o _) _) => o
  | _ => none

/-- A method with neither a parameter type nor a goal. -/
def noParamSrc : STm := o16% new { o ⇒ def f(x) = x }

/-- The same literal ascribed: the goal gives the parameter and the result. -/
def ascParamSrc : STm := o16% (new { o ⇒ def f(x) = x } : μ(z. { def f(y : ⊤) : ⊤ }))

/-- Two declarations of `f` at one domain: the results meet. -/
def ascSameSrc : STm :=
  o16% (new { o ⇒ def f(x) = x } : { def f(y : ⊤) : ⊤ } ∧ { def f(y : ⊤) : ⊤ ∧ ⊤ })

/-- A literal whose written self type the goal gives back. -/
def ascWSrc : STm :=
  o16% (new { o : { def f(y : ⊤) : ⊤ } ∧ ⊤ ⇒ def f(y) = y } : { def f(y : ⊤) : ⊤ })

/-- The same with the self type erased. -/
def ascWSrcS : STm := o16% (new { o ⇒ def f(y) = y } : { def f(y : ⊤) : ⊤ })

/-- Two declarations of `f` at domains of `⊤` and below it: the larger domain. -/
def ascTwoSrc : STm :=
  o16% (new { o ⇒ def f(x) = x } : { def f(y : ⊤) : ⊤ } ∧ { def f(y : { type A : ⊥ .. ⊤ }) : ⊤ })

/-- Two declarations of `f` at domains that are not ordered: their union. -/
def twoDomSrc : STm :=
  o16% (new { o ⇒ def f(x) = x } :
          { def f(y : { type A : ⊥ .. ⊤ }) : ⊤ } ∧ { def f(y : { type B : ⊥ .. ⊤ }) : ⊤ })

/-- The same domains with results the body does not meet: the parameter at
the union is below neither result. -/
def ascIncSrc : STm :=
  o16% (new { o ⇒ def f(x) = x } :
          { def f(y : { type A : ⊥ .. ⊤ }) : { type A : ⊥ .. ⊤ } }
            ∧ { def f(y : { type B : ⊥ .. ⊤ }) : { type B : ⊥ .. ⊤ } })

/-- Two declarations of `f` at `⊤` and at `⊤ ∧ ⊤`, compared by the subtyping
goal. -/
def eqvAscSrc : STm :=
  o16% (new { o ⇒ def f(x) = x } : { def f(y : ⊤) : ⊤ } ∧ { def f(y : ⊤ ∧ ⊤) : ⊤ })

/-- The table of the programs of this section. -/
def fTable : LabelTable := [("A", 0), ("B", 1), ("f", 0)]

example : labelsOfProgram [("A", 0), ("B", 1)] ascIncSrc = some fTable := by decide

example : inferAt fTable noParamSrc
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

example : inferAt fTable ascParamSrc
    = (.typed (.TBind (.TFun 0 .TTop .TTop)), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- The result of `f` is the meet of the two results. -/
example : ascSelf? (filledAt fTable ascSameSrc)
    = some (.TAnd (.TFun 0 .TTop (.TAnd .TTop (.TAnd .TTop .TTop))) .TTop) ∧
    (inferAt fTable ascSameSrc).1.isTyped = true ∧
    (inferAt fTable ascSameSrc).2 = ⟨defaultFuel - 140, false⟩ := by
  decide +kernel

/-- The fill is the written program, typed as the typer types it. -/
example : filledAt fTable ascWSrcS = resolve fTable ascWSrc ∧
    inferAt fTable ascWSrcS = (.typed (.TFun 0 .TTop .TTop), ⟨defaultFuel - 14, false⟩) ∧
    inferAt fTable ascWSrc = (.typed (.TFun 0 .TTop .TTop), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- The larger domain `⊤`. -/
example : ascSelf? (filledAt fTable ascTwoSrc) = some (.TAnd (.TFun 0 .TTop .TTop) .TTop) ∧
    (inferAt fTable ascTwoSrc).1.isTyped = true ∧
    (inferAt fTable ascTwoSrc).2 = ⟨defaultFuel - 61, false⟩ := by
  decide +kernel

/-- The union domain `{A : ⊥..⊤} ∨ {B : ⊥..⊤}`. -/
example : ascSelf? (filledAt fTable twoDomSrc)
    = some (.TAnd (.TFun 0 (.TOr (.TTyp 0 .TBot .TTop) (.TTyp 1 .TBot .TTop)) .TTop) .TTop) ∧
    (inferAt fTable twoDomSrc).1.isTyped = true ∧
    (inferAt fTable twoDomSrc).2 = ⟨defaultFuel - 122, false⟩ := by
  decide +kernel

example : inferAt fTable ascIncSrc = (.rejected .mismatch, ⟨defaultFuel - 74, false⟩) := by
  decide +kernel

example : ascSelf? (filledAt fTable eqvAscSrc) = some (.TAnd (.TFun 0 .TTop .TTop) .TTop) ∧
    (inferAt fTable eqvAscSrc).1.isTyped = true ∧
    (inferAt fTable eqvAscSrc).2 = ⟨defaultFuel - 61, false⟩ := by
  decide +kernel

/-! ### Goals that are selections -/

/-- An alias of an alias of a method type. -/
def alias2Src : STm :=
  o16% new { y ⇒ type L = y.M
                  type M = { def f(p : ⊤) : ⊤ }
                  def g(x : ⊤) : ⊤ = (new { o ⇒ def f(q) = q } : y.L) }

/-- Its table. -/
def alias2Table : LabelTable := [("L", 2), ("M", 1), ("g", 0), ("f", 0)]

example : labelsOfProgram [] alias2Src = some alias2Table := by decide

example : (inferAt alias2Table alias2Src).1.isTyped = true ∧
    (inferAt alias2Table alias2Src).2 = ⟨defaultFuel - 202, false⟩ := by
  decide +kernel

/-- An abstract goal whose upper bound declares the method. -/
def upperSrc : STm :=
  o16% new { c ⇒ def g(z : { type L : ⊥ .. { def f(p : ⊤) : ⊤ } }) : ⊤
                   = (new { o ⇒ def f(q) = q } : z.L) }

/-- An abstract goal whose lower bound declares the method. -/
def lowerSrc : STm :=
  o16% new { c ⇒ def g(z : { type L : { def f(p : ⊤) : ⊤ } .. ⊤ }) : ⊤
                   = (new { o ⇒ def f(q) = q } : z.L) }

/-- Their table. -/
def boundTable : LabelTable := [("L", 0), ("g", 0), ("f", 0)]

example : labelsOfProgram [("L", 0)] upperSrc = some boundTable := by decide

example : inferAt boundTable upperSrc = (.rejected .mismatch, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

example : inferAt boundTable lowerSrc
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

/-! ### `paper_lst` with every parameter type erased

The ascription is the module's parent, so `nil` and `cons` take their
parameter types from it.  Each nested literal takes its methods' parameter
types from the declared result of the method whose body it is, through the
alias `m.List`. -/

example : inferAt paperLstTable paperLstSrc.eraseParam
    = (.typed (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody), ⟨defaultFuel - 4468, false⟩) := by
  decide +kernel

/-! ### Heads

The heads of a literal at its labels, read off the resolved program. -/

/-- The members of a closed program that is a literal. -/
def membersOf? : Option (ATm []) → Option (ADms ([],x))
  | some (.obj _ ds) => some ds
  | _ => none

/-- With no goal, the heads of noParam stop at `f`, the method at label `0`,
which has no parameter type. -/
example : (membersOf? (resolve fTable noParamSrc)).map (fun ds =>
      (match headsOf (paramFrom []) (resultFrom []) ds with
          | .error r => decide (r = .missingParamType (some 0))
          | .ok _ => false,
        (ds.memberAt 0).map fun d => match d with
          | .dfun none _ _ => true
          | _ => false))
    = some (true, some true) := by
  decide +kernel

/-- A literal with a type member and a method annotated at both. -/
def annSrc : STm := o16% new { z ⇒ type A = ⊤ def f(y : z.A) : ⊤ = y }

/-- The table of `annSrc`. -/
def annTable : LabelTable := [("A", 1), ("f", 0)]

example : labelsOfProgram [] annSrc = some annTable := by decide

/-- Its heads give the self type `selfOf?` computes. -/
example : (membersOf? (resolve annTable annSrc)).map (fun ds =>
      (decide ((match headsOf (paramFrom []) (resultFrom []) ds with
          | .ok hs => fullSelf hs []
          | .error _ => none) = selfOf? ds.erase),
        (selfOf? ds.erase).isSome))
    = some (true, true) := by
  decide +kernel

/-! ### Results on demand

The rounds alone, on a literal without a self type: the heads, the jobs, the
rounds, then the self type in lockstep.  Each check compares the self type the
rounds form with the one a written form of the program states, or gives the
reason the rounds stop.  The next subsection runs the whole elaborator. -/

/-- The self type the rounds form for a literal in `Γ` at the goal `g`. -/
def formLitF {s : Sig} (Γ : Ctx [] s) (g : Option (Ty [] s)) (ds : ADms (s,x)) :
    Fu (FillR (Ty [] (s,x))) :=
  Fu.bind (readGoalF Γ g ds) fun rd =>
    match headsOf (paramFrom rd) (resultFrom rd) ds with
    | .error e => Fu.ret (.error e)
    | .ok hs => Fu.bind (formSelfF Γ hs (jobsF hs ds)) fun r => Fu.ret (r.map (·.1))

/-- What the rounds give the first literal without a self type of a
program. -/
inductive Formed where
  /-- A self type formed, and whether it is the one the written form states. -/
  | self (written : Bool)
  /-- The reason the rounds stop. -/
  | no (r : EReason)
  /-- No such literal, or the written form is not the same program there. -/
  | shape
deriving DecidableEq

/-- The rounds on the first literal without a self type, found under
ascriptions and at the receivers of calls, against the same place of the
written form.  An ascription is the literal's goal.  The written self type is
the one the written form states, else the one `selfOf?` reads off its
members. -/
def formGo {s : Sig} (Γ : Ctx [] s) (n : Nat) (g : Option (Ty [] s)) (a w : ATm s) :
    Formed × Tank :=
  match a, w with
  | .obj none ds, .obj o ds' =>
      match formLitF Γ g ds ⟨n, false⟩ with
      | (.ok T, tk) => (.self (decide ((o <|> selfOf? ds'.erase) = some T)), tk)
      | (.error r, tk) => (.no (Reason.top tk.out [r]), tk)
  | .asc t T, .asc t' T' => if T = T' then formGo Γ n (some T) t t' else (.shape, ⟨n, true⟩)
  | .app t _ _, .app t' _ _ => formGo Γ n none t t'
  | _, _ => (.shape, ⟨n, true⟩)
termination_by structural a

/-- The rounds on a surface program, against its written form, with the tank
left. -/
def formAt (Λ : LabelTable) (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolve Λ e, resolve Λ w with
  | some a, some b => formGo Ctx.nil n none a b
  | _, _ => (.shape, ⟨n, true⟩)

/-- The jobs of a closed literal without a goal: each label with what the body
calls on the self and whether it uses the self bare. -/
def jobsAt (Λ : LabelTable) (e : STm) : List (Lb × (List Lb × Bool)) :=
  match resolve Λ e with
  | some (.obj _ ds) =>
      match headsOf (paramFrom []) (resultFrom []) ds with
      | .ok hs => (jobsF hs ds).map fun j => (j.lbl, j.deps)
      | .error _ => []
  | _ => []

/-- A method that calls a later one. -/
def fwdSrc : STm := o16% new { o ⇒ def g(x : ⊤) = o.f(x)   def f(x : ⊤) = x }

/-- The same with the results written. -/
def fwdSrcW : STm := o16% new { o ⇒ def g(x : ⊤) : ⊤ = o.f(x)   def f(x : ⊤) : ⊤ = x }

/-- Its table. -/
def fwdTable : LabelTable := [("g", 1), ("f", 0)]

example : labelsOfProgram [] fwdSrc = some fwdTable := by decide

/-- A recursive method without a result type. -/
def recUSrc : STm := o16% new { o ⇒ def f(x : ⊤) = o.f(x) }

/-- The same with the result written. -/
def recWSrc : STm := o16% new { o ⇒ def f(x : ⊤) : ⊤ = o.f(x) }

/-- A recursive method that calls itself through an ascription of the self. -/
def ascRecSrc : STm := o16% new { o ⇒ def f(x : ⊤) = (o : { def f(y : ⊤) : ⊤ }).f(x) }

/-- Their table. -/
def recTable : LabelTable := [("f", 0)]

example : labelsOfProgram [] ascRecSrc = some recTable := by decide

/-- A method that calls a cycle between two later ones. -/
def cycSrc : STm :=
  o16% new { o ⇒ def a(x : ⊤) = o.b(x)   def b(x : ⊤) = o.c(x)   def c(x : ⊤) = o.b(x) }

/-- Its table. -/
def cycTable : LabelTable := [("a", 2), ("b", 1), ("c", 0)]

example : labelsOfProgram [] cycSrc = some cycTable := by decide

/-- A recursive call from a nested literal. -/
def nestRecSrc : STm := o16% new { o ⇒ def f(x : ⊤) = new { p ⇒ def g(y : ⊤) = o.f(y) } }

/-- A nested literal whose method has neither a parameter type nor a goal. -/
def nestNoParamSrc : STm := o16% new { o ⇒ def f(x : ⊤) = new { p ⇒ def g(y) = y } }

/-- Their table. -/
def nestTable : LabelTable := [("f", 0), ("g", 0)]

example : labelsOfProgram [] nestRecSrc = some nestTable := by decide

/-- A method that returns the self, and one that does not. -/
def bareSrc : STm := o16% new { o ⇒ def c(x : ⊤) = o   def d(x : ⊤) = x }

/-- The same with the results written at the snapshot `c` is typed at. -/
def bareSrcW : STm :=
  o16% new { o ⇒ def c(x : ⊤) : { def d(y : ⊤) : ⊤ } ∧ ⊤ = o   def d(x : ⊤) : ⊤ = x }

/-- Its table. -/
def bareTable : LabelTable := [("c", 1), ("d", 0)]

example : labelsOfProgram [] bareSrc = some bareTable := by decide

/-- A method that returns the self, and one that calls it. -/
def fluentSrc : STm := o16% new { o ⇒ def c(x : ⊤) = o   def g(x : ⊤) = o.c(x) }

/-- The same with the results written at the snapshots. -/
def fluentSrcW : STm := o16% new { o ⇒ def c(x : ⊤) : ⊤ = o   def g(x : ⊤) : ⊤ = o.c(x) }

/-- Its table. -/
def fluentTable : LabelTable := [("c", 1), ("g", 0)]

example : labelsOfProgram [] fluentSrc = some fluentTable := by decide

/-- A method that calls a later one that returns the self. -/
def bareLateSrc : STm := o16% new { o ⇒ def c(x : ⊤) = o.e(x)   def e(x : ⊤) = o }

/-- The same with the results written at the snapshots. -/
def bareLateSrcW : STm := o16% new { o ⇒ def c(x : ⊤) : ⊤ = o.e(x)   def e(x : ⊤) : ⊤ = o }

/-- Its table. -/
def bareLateTable : LabelTable := [("c", 1), ("e", 0)]

example : labelsOfProgram [] bareLateSrc = some bareLateTable := by decide

/-- A method that returns the self, alone. -/
def chainSrc : STm := o16% new { o ⇒ def c(x : ⊤) = o }

/-- The same with the result written at the snapshot, which lacks `c`. -/
def chainSrcW : STm := o16% new { o ⇒ def c(x : ⊤) : ⊤ = o }

/-- Its table. -/
def chainTable : LabelTable := [("c", 0)]

/-- `twoCand` with the two method types of `x` in the other order. -/
def twoCandSwapSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : { type A : ⊥ .. ⊤ } }
                         ∧ { def f(y : ⊤ ∧ ⊤ ∧ ⊤ ∧ ⊤) : ⊤ }) : { type A : ⊥ .. ⊤ } = x.f(x) }

/-- A body with two candidates whose types are not ordered. -/
def ambSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : { type A : ⊥ .. ⊤ } }
                         ∧ { def f(y : ⊤) : { type B : ⊥ .. ⊤ } }) = x.f(x) }

/-- Its table. -/
def ambTable : LabelTable := [("f", 0), ("A", 0), ("B", 1), ("g", 0)]

example : labelsOfProgram [("f", 0), ("A", 0), ("B", 1)] ambSrc = some ambTable := by decide

/-- P1 with its results erased: `h` calls itself and `g` calls `h`. -/
def P1RSrc : STm :=
  o16% new { c ⇒ type L = μ(w. { type B : ⊥ .. w.B })
    def h(q : ⊤) = c.h(q)
    def g(p : ⊤) = c.h(p) }

/-- Its table. -/
def P1RTable : LabelTable := [("B", 0), ("L", 2), ("h", 1), ("g", 0)]

example : labelsOfProgram [("B", 0)] P1RSrc = some P1RTable := by decide

-- The jobs, in source order, with their dependencies.  A method with its
-- result written is no job.  A call through an ascription of the self is a
-- call and a bare use.
example : jobsAt fwdTable fwdSrc = [(1, ([0], false)), (0, ([], false))] := by decide +kernel
example : jobsAt recTable recWSrc = [] := by decide +kernel
example : jobsAt recTable ascRecSrc = [(0, ([0], true))] := by decide +kernel
example : jobsAt fluentTable fluentSrc = [(1, ([], true)), (0, ([1], false))] := by
  decide +kernel

-- A method that calls a later one waits a round.  A method with its result
-- written is known at once, so its recursion is no cycle.
example : formAt fwdTable fwdSrc fwdSrcW = (.self true, ⟨defaultFuel - 6, false⟩) := by
  decide +kernel
example : formAt recTable recWSrc recWSrc = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel

-- The result of `selCall` and of `twoCand` is the least candidate of the
-- body, the written one, in either order of the intersection.
example : formAt selCallTable selCallSrc.eraseRes selCallSrc
    = (.self true, ⟨defaultFuel - 19, false⟩) := by
  decide +kernel
example : formAt twoCandTable twoCandSrc.eraseRes twoCandSrc
    = (.self true, ⟨defaultFuel - 49, false⟩) := by
  decide +kernel
example : formAt twoCandTable twoCandSwapSrc.eraseRes twoCandSwapSrc
    = (.self true, ⟨defaultFuel - 48, false⟩) := by
  decide +kernel

-- Cyclic references, at the method the walk reaches again: a recursion, a
-- recursion through an ascription of the self, a cycle that a method before
-- it calls, a recursive call from a nested literal, and P1.
example : formAt recTable recUSrc recUSrc = (.no (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt recTable ascRecSrc ascRecSrc = (.no (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt cycTable cycSrc cycSrc = (.no (.cyclicRef 1), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt nestTable nestRecSrc nestRecSrc = (.no (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt P1RTable P1RSrc P1RSrc = (.no (.cyclicRef 1), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Bare uses of the self, typed at the snapshot after every ready method that
-- does not use the self bare.  A method that calls one of them waits for it.
example : formAt bareTable bareSrc bareSrcW = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt fluentTable fluentSrc fluentSrcW = (.self true, ⟨defaultFuel - 6, false⟩) := by
  decide +kernel
example : formAt bareLateTable bareLateSrc bareLateSrcW
    = (.self true, ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- The snapshot a method that returns the self is typed at lacks the method
itself, since it is pending.  No type of the version names the whole self
type of a literal without a type member. -/
example : formAt chainTable chainSrc chainSrcW = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- Two candidates whose types are not ordered have no least one.  The
compiler meets them, which the version cannot derive for a call. -/
example : formAt ambTable ambSrc ambSrc = (.no (.ambiguous 0), ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- A job's own reason stops the rounds. -/
example : formAt nestTable nestNoParamSrc nestNoParamSrc
    = (.no (.missingParamType (some 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Literals without a self type, through the elaborator

The whole elaborator on programs whose literals need rounds: the goal reading,
the heads, the rounds, the fill of the members, then the typer on the filled
program.  A program that compiles is compared with a written form that states
the results the rounds find.  Its type is the written form's type. -/

/-- Whether a derivation ends in `T_Obj`, at its head or under one
subsumption. -/
def objHead {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Tm σ s} {T : Ty σ s} :
    HasType G Γ t T → Bool
  | .T_Obj _ => true
  | .T_Sub (.T_Obj _) _ => true
  | _ => false

/-- Whether the derivation the elaborator returns for a closed program ends in
`T_Obj`. -/
def objAt (Λ : LabelTable) (e : STm) (n : Nat := defaultFuel) : Bool :=
  match resolve Λ e with
  | some a =>
      match elabTopF n a with
      | (.ok ⟨_, c⟩, _) => objHead c.deriv
      | (.error _, _) => false
  | none => false

-- Cyclic references, at the method the walk reaches again.  A recursion, a
-- recursion through an ascription of the self, a cycle that a method before it
-- calls, a recursive call from a nested literal.
example : inferAt recTable recUSrc = (.rejected (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : inferAt recTable ascRecSrc = (.rejected (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : inferAt cycTable cycSrc = (.rejected (.cyclicRef 1), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : inferAt nestTable nestRecSrc = (.rejected (.cyclicRef 0), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P1 with its results erased is a cyclic reference at `h`. -/
example : inferAt P1RTable P1RSrc = (.rejected (.cyclicRef 1), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P3 with its results erased: `apply` calls itself and `g` calls `apply`. -/
def P3RSrc : STm :=
  o16% new { c ⇒
    def apply(t : { type T : ⊥ .. ⊤ }) = c.apply(t)
    def g(q : ⊤) =
      c.apply(new { o ⇒ type T = ⊤  type U = ⊤ }).m(new { o2 ⇒ type T = ⊤  type U = ⊤ }) }

/-- Its table. -/
def P3RTable : LabelTable := [("T", 1), ("U", 0), ("m", 0), ("apply", 1), ("g", 0)]

example : labelsOfProgram [("T", 1), ("U", 0), ("m", 0)] P3RSrc = some P3RTable := by decide

/-- P3 with its results erased is a cyclic reference at `apply`. -/
example : inferAt P3RTable P3RSrc = (.rejected (.cyclicRef 1), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- A method that calls a later one waits a round.  A method with its result
-- written is known at once, so its recursion is no cycle.
example : inferAt fwdTable fwdSrc = ((inferAt fwdTable fwdSrcW).1, ⟨defaultFuel - 20, false⟩) := by
  decide +kernel
example : inferAt recTable recWSrc = ((inferAt recTable recWSrc).1, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : (inferAt fwdTable fwdSrcW).1.isTyped = true := by decide +kernel

-- Bare uses of the self.  A method that calls one of them waits for it.
example : inferAt bareTable bareSrc
    = ((inferAt bareTable bareSrcW).1, ⟨defaultFuel - 26, false⟩) := by
  decide +kernel
example : inferAt fluentTable fluentSrc
    = ((inferAt fluentTable fluentSrcW).1, ⟨defaultFuel - 25, false⟩) := by
  decide +kernel
example : inferAt bareLateTable bareLateSrc
    = ((inferAt bareLateTable bareLateSrcW).1, ⟨defaultFuel - 25, false⟩) := by
  decide +kernel
example : (inferAt bareTable bareSrcW).1.isTyped && (inferAt fluentTable fluentSrcW).1.isTyped &&
    (inferAt bareLateTable bareLateSrcW).1.isTyped = true := by
  decide +kernel

/-- `bare` used: `c` returns the self at the type it was typed at, which
declares `d`, so the call of `d` on its result types. -/
def bareUseSrc : STm :=
  o16% (new { o ⇒ def c(x : ⊤) = o   def d(x : ⊤) = x }).c(new { z ⇒ }).d(new { z ⇒ })

example : labelsOfProgram [] bareUseSrc = some bareTable := by decide

example : inferAt bareTable bareUseSrc = (.typed .TTop, ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

/-- `fluent` used: `g` calls `c` on the self. -/
def fluentUseSrc : STm :=
  o16% (new { o ⇒ def c(x : ⊤) = o   def g(x : ⊤) = o.c(x) }).g(new { z ⇒ })

example : labelsOfProgram [] fluentUseSrc = some fluentTable := by decide

example : inferAt fluentTable fluentUseSrc = (.typed .TTop, ⟨defaultFuel - 39, false⟩) := by
  decide +kernel

/-- The chain `c` then `c` again.  The snapshot `c` is typed at lacks `c`, so
the second call finds no method.  The compiler gives `c` the class type and
accepts the chain.  No type of the version names the whole self type here. -/
def chainUseSrc : STm := o16% (new { o ⇒ def c(x : ⊤) = o }).c(new { z ⇒ }).c(new { z ⇒ })

example : labelsOfProgram [] chainUseSrc = some chainTable := by decide

example : inferAt chainTable chainUseSrc = (.rejected .mismatch, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

-- The result of `selCall` and of `twoCand` is the least candidate of the body,
-- the written one, in either order of the intersection.
example : inferAt selCallTable selCallSrc.eraseRes
    = ((inferAt selCallTable selCallSrc).1, ⟨defaultFuel - 51, false⟩) := by
  decide +kernel
example : inferAt twoCandTable twoCandSrc.eraseRes
    = ((inferAt twoCandTable twoCandSrc).1, ⟨defaultFuel - 98, false⟩) := by
  decide +kernel
example : inferAt twoCandTable twoCandSwapSrc.eraseRes
    = ((inferAt twoCandTable twoCandSwapSrc).1, ⟨defaultFuel - 60, false⟩) := by
  decide +kernel

/-- Two candidates whose types are not ordered have no least one. -/
example : inferAt ambTable ambSrc = (.rejected (.ambiguous 0), ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- A nested literal whose method has no parameter type stops the rounds of
the outer one with its own reason. -/
example : inferAt nestTable nestNoParamSrc
    = (.rejected (.missingParamType (some 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- `ex1` with its results written as the rounds find them: the outer method
returns the self type of the inner literal. -/
def ex1RW : STm :=
  o16% new { o ⇒ def apply(t : { type T : ⊥ .. ⊤ }) : μ(q. { def apply(x : t.T) : t.T } ∧ ⊤) =
                  new { p ⇒ def apply(x : t.T) : t.T = x } }

example : labelsOfProgram [("T", 0)] ex1RW = some ex1Table := by decide

/-- `ex1` with its results erased.  The inner literal's method is typed in a
round of the inner literal, inside the outer one's round. -/
example : inferAt ex1Table ex1src.eraseRes
    = ((inferAt ex1Table ex1RW).1, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- `selfCall` with its results erased.  The receiver literal is formed from
its members, and the typer takes the argument literal as it is. -/
example : inferAt selfCallTable selfCallSrc.eraseRes
    = ((inferAt selfCallTable selfCallSrc).1, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

/-- `packSel` with its results written as the rounds find them: the body's
type, the parameter type. -/
def packSelRW : STm :=
  o16% new { m ⇒ type L = μ(w. { type A : ⊤ .. ⊤ })
    def g(x : { type A : ⊤ .. ⊤ }) : { type A : ⊤ .. ⊤ } = x }

example : labelsOfProgram [("A", 0)] packSelRW = some packSelTable := by decide

example : inferAt packSelTable packSelSrc.eraseRes
    = ((inferAt packSelTable packSelRW).1, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- `paper_lst` with every result erased.  The ascription is the module's
parent, so `nil` and `cons` inherit their results, and each nested literal
inherits from the declared result of its method through the alias `m.List`.
The recursive `head` and `tail` of `nil`'s list then inherit, and are no
cycle. -/
example : inferAt paperLstTable paperLstSrc.eraseRes
    = (.typed (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody), ⟨defaultFuel - 29926, false⟩) := by
  decide +kernel

-- The derivation the elaborator returns ends in `T_Obj` at the literal, under
-- the subsumption to the ascription for `paper_lst`.
example : objAt fwdTable fwdSrc && objAt recTable recWSrc && objAt bareTable bareSrc &&
    objAt selCallTable selCallSrc.eraseRes && objAt ex1Table ex1src.eraseRes = true := by
  decide +kernel
example : objAt paperLstTable paperLstSrc.eraseRes = true := by
  decide +kernel

/-- Literals without a self type nested `d` deep, each with one method with a
written parameter type and no result, the innermost body the parameter. -/
def nestObj : Nat → {s : Sig} → ATm (s,x)
  | 0, _ => .var .here
  | d + 1, _ => .obj none (.dcons (.dfun (some .TTop) none (nestObj d)) .dnil)

/-- The nesting at depth `d + 1`, closed. -/
def nestTop (d : Nat) : ATm [] := .obj none (.dcons (.dfun (some .TTop) none (nestObj d)) .dnil)

/-- The fuel the elaborator draws on `nestTop d`, and the fuel the typer draws
on the filled term, when both type it with the tank unmarked. -/
def nestFuel (d : Nat) : Option (Nat × Nat) :=
  match elabTopF defaultFuel (nestTop d) with
  | (.ok ⟨a', _⟩, t) =>
      match t.out, synthTopF defaultFuel a' with
      | false, (some _, t') =>
          if t'.out then none else some (defaultFuel - t.left, defaultFuel - t'.left)
      | _, _ => none
  | (.error _, _) => none

-- Each body is typed once in a round and once more by the typer on the
-- filled literal, so the fuel grows with the square of the depth.
example : nestFuel 4 = some (15, 5) := by decide +kernel
example : nestFuel 8 = some (45, 9) := by decide +kernel
example : nestFuel 12 = some (91, 13) := by decide +kernel

end InferChecks

end Oopsla16Frontend
