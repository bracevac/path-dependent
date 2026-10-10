import Coercions.Captures.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# The elaborator

The elaborator fills the empty slots of a partial term (`PTm`, `Ann.lean`) and
types the result with the typer of `Typer.lean`, on the same tank.

## One function with an optional goal

The typer's `inferF` synthesizes and checks in one function, with an optional
goal.  `elabF` has the same form.  Its candidates are the typer's own `Elab`:
an elaborated term, its use set, its type, and the `HasTy` derivation of its
erasure.  So every result is a judgment of the version.  Beside the candidates
`elabF` returns the reasons of its failed branches, in search order.

## The rule of empty slots

`elabF` first asks `PTm.full?`.  A term with no empty slot goes to `inferF` as
it is, with its goal (`fullInfer`).  So a program with every slot written
elaborates as the typer types it, at the same fuel (`elabF_toI`).  Below an
empty slot each clause is the typer's clause of the same form, with the
reasons added.  A clause that checks against a goal first and then falls back
to synthesis and the subtyping goal keeps doing so, so a goal site whose
attempt fails runs the typer's own route on the filled term.

## Where a goal reaches a term

- A written `let` type is the goal of the body, under the binder.
- A `let` checked at a goal passes the goal to its body.
- An ascription `(t : T)` checks `t` against `T`.
- A lambda's body gets the result part of the goal.
- A field of a literal with a written self shape gets the field's type in it.
- A call argument gets the dominant formal of its callee.

## Lambdas

A lambda without a domain takes it from the function part of its goal
(`funPartOf`), as `Typer.typedFunctionValue` does through
`Typer.decomposeProtoFunction` and `Type.findFunctionType`.  The capture set of
the goal is dropped and a box is looked through, as `strippedDealias` drops
annotations.  A function type at the top of the goal gives its domain and its
codomain.  A selection whose member has equal bounds is replaced by the bound,
to a fixpoint, as `strippedDealias` follows aliases.  The sides of an
intersection meet.  One function side gives that side.  Two sides whose
domains are comparable give the larger domain and the intersection of the
results.  Two sides with incomparable domains are a mismatch, since the
compiler forms their union, which the version lacks.  A selection with
different bounds whose upper bound has a function part is a mismatch, as for an
abstract type with a function upper bound in the compiler.  Any other goal has
no function part.  There, and with no goal at all, a body `g x` that calls a
variable `g` bound outside on the parameter gives the domain: the dominant
formal of `g`, as `Typer.typedFunctionValue` reads the parameter type of the
callee (`inferredFromTarget`).  Any other lambda there is the compiler's
"Missing parameter type".

A lambda whose body has no empty slot is filled with the domain and handed to
`inferF` with the goal.  So its candidates and its tank are the typer's on the
filled lambda.  Otherwise the lambda takes the typer's clause with that
domain: at a function type the body is checked against the codomain, and the
lambda gets the goal's set when its body's set fits.  Through an intersection,
a selection or a box, the body is checked against the result part and the
lambda, at its least set, is moved to the goal by the subtyping goal.  If that
gives nothing, the body is synthesized and the lambda moved to the goal.  A
lambda with a written domain whose body has an empty slot reads the result
part of its goal the same way.

## Call arguments

The resolver binds the operand of an application with a `let` tagged `arg`,
`let z = t in g z`.  When `t` has an empty slot, its goal is a formal of the
callee `g`: the domain of a function type the lookup finds for `g`, or of a
function type `g` boxes.  An intersection callee has several formals, and the
compiler types the argument against their least upper bound
(`TypeComparer.distributeAnd`).  The version has no union, so the goal is the
dominant formal, the one every other formal is below.  The whole formal is
the goal, so a curried lambda takes its inner domains from the formal's
result.  A box on the formal is stripped, since the compiler's typer sees no
boxes and box inference boxes the argument afterwards.  The goal only fills
the argument.  The `let` with the filled argument then goes to `inferF`, so
the typer binds `z` at the type it gives the filled argument, and a closure
keeps its least set, as `CheckCaptures.recheckClosure` types a closure at its
own use set.  With no dominant formal, or when the filled `let` does not type
on an unmarked tank, the `let` is typed as any other.  So a lambda without a
domain there is the compiler's "Missing parameter type".  A `let` the
programmer writes is never a call argument, as Scala's `val i = x => x`.

## Object literals

A literal with a written self shape whose definitions have an empty slot has
its definitions filled against the shape in lockstep (`elabDefsF`).  A field
with no empty slot stays as written.  Any other field is elaborated against
its type in the shape, so its lambdas take their domains from it.  The fields
are elaborated with the self bound at `μ` of the shape, at the written set or
at every atom of the context (`probeCtx`).  The filled literal then goes to
`inferF` in the real context, so its derivation is the typer's `HasTy.obj` and
its set the least one the typer finds.  A literal without a self shape at a
goal that dealiases to a `μ` takes the body of that `μ` as its self shape
(`selfGoalF`).  Scala makes a class `pt` the parent of `new { … }`
(`Typer.typedNew`), and every type of the version is structural, so a `μ` goal
plays the class.  When that gives nothing on an unmarked tank, and for any
other literal without a self shape, the self shape is formed from the
definitions, as the next section says.  The literal is then filled at the
formed shape (`fillDefsF`) and goes to `inferF` with the goal, which
synthesizes it and moves it to the goal.  A field without a written type holds
the term the rounds elaborated for it, so no field is elaborated twice, and
nested literals cost fuel quadratic in their depth.

## Self shapes formed from definitions

`formSelfF` forms the self shape of a literal from its definitions, as the
completers of `Namer` type the members of a class.  Type members, capture
members and fields with a written type are known at once.  Every other field
is a job (`jobsF`), typed in rounds (`roundsF`).  A round takes a snapshot of
the self shape known so far and types every ready job once, with no goal, in
the probe context: the self at `μ` of the snapshot, at the written set or at
every atom of the context.  A job is ready when none of the fields it projects
off the self is pending (`PTm.deps`).  A job that uses the self any other way
is typed in the first round in which no ready job lacks such a use.  A
field's type is its least candidate (`leastCandF`), capture sets included, and
candidates with no least one are ambiguous.  A round that types nothing stops
with the cyclic reference `cycleAt` names.  The self shape is the definition
list read in lockstep (`PDefs.fullSelf`).

## Reasons

Each clause returns the reasons of its failed branches in search order, and a
branch that succeeds drops them.  `elabTopF` reports the recursion limit when
the tank ended marked, else the first reason, else a mismatch (`Reason.top`).
`EReason` is the reason type of `Coercions.Frontend.Reason` at the labels of
this version, with no reason of the typer's own, since the typer rejects with
no reason.

## The theorems

`elabF_toI` says that a term with every slot written is the typer's,
candidates, derivations and tank, and `elabF_full` says the same of any term
with no empty slot.  `elabF_lam_none` unfolds the clause of a lambda without a
domain, and `elabF_arg` the clause of a call argument.  `argGoal_dominant`
says that the goal of a call argument is a formal of the callee and that
every formal is below it.  `lam_callee_full` says that a lambda without a
domain whose body is `g x`, at no function part, is the typer's on the lambda
filled with the dominant formal of `g`, candidates and tank.

`elabF_framed` and `elabDefsF_framed` say that the elaborator is framed, as
the typer is (`inferF_framed`): it keeps a marked tank, never adds fuel, and
does the same with more fuel.  The index of the function part and of the self
shape a goal gives starts at the fuel left, so their frame lemmas rest on the
agreement of a smaller index with a larger one, as the lookup's do.

`lam_direct_full`, `lam_side_full` and `asc_direct_full` say that a lambda
whose domain is empty and whose body has none elaborates as the typer types
the lambda with the domain the goal gives written, with the same candidates
and the same tank.  At a function type and at an ascription to one this holds
from every tank.  Through an intersection, an alias or a box it holds from
the tank the function part leaves.  `letAnn_direct_full` says the same of a
lambda that is the body of a `let` with a written function type.

`fullSelf_lockstep` says that the formed self shape is the definition list
read in lockstep, and `jobsF_written` that a literal with a written type on
every field has no job.  `leastCand_least` says that the least candidate is a
candidate whose type is below every candidate's, and `cycleAt_onCycle` that the
cyclic reference names a pending field whose walk comes back to it.
`roundsF_framed` says that the rounds are framed when every job is, and
`jobsF_framed` that every job is.  `formSelfF_noAny` says that the formed self
shape and the typed fields hold no `any` when the context, the definitions and
every job hold none, and `jobsF_noAny` that every job holds none.
`obj_none_landed` says that a candidate of a literal without a self shape is
a candidate the typer gives the literal with its self shape and its
definitions filled, at the same set and goal, so its derivation is the
typer's.  `obj_none_formed` adds that with no goal the self shape is the one
the rounds form.

`elab_noAny` says that no candidate holds `any` in an annotation, a set or a
type definition when the partial term, the goal and the types of the context
hold none.  The proof follows every set and type the typer forms through the
lookup, box inference and avoidance (`inferF_noAny`).  `elabTop_noAny` is its
form for a closed program.
-/

namespace CapturesFrontend

open Frontend.Fuel CapturesFrontend.Core Frontend.Reason
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Ctx Sub SubShape Subcap
  HasTy DefsTy Platform)
open scoped Captures.DotMNF

/-- The reasons of this front end: its labels, and no reason of the typer's
own. -/
abbrev EReason := Reason Label Empty

/-- The candidates of an elaboration, with the reasons of its failed
branches. -/
abbrev Out {s : Sig} (Γ : Ctx s) := List (Elab Γ) × List EReason

/-! ## Combinators with reasons -/

/-- A slot agrees with a value when it is empty or holds that value. -/
def optAgree {α : Type} [DecidableEq α] : Option α → α → Bool
  | some x, y => decide (x = y)
  | none, _ => true

/-- A list computation, with a mismatch when it has no candidate. -/
def withR {α : Type} (c : Fu (List α)) : Fu (List α × List EReason) :=
  Fu.bind c fun l => Fu.ret (l, if l.isEmpty then [.mismatch] else [])

/-- The typer on a term with no empty slot, at an optional goal. -/
def fullInfer {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Option (Ty s)) : Fu (Out Γ) :=
  withR (inferF Γ a G)

/-- The candidates of `a`, or those of `b` when `a` has none, with the
reasons of both.  This is `orElseL` of the typer with reasons. -/
def orElseO {s : Sig} {Γ : Ctx s} (a b : Fu (Out Γ)) : Fu (Out Γ) :=
  Fu.bind a fun r =>
    match r with
    | ([], rs) => Fu.bind b fun r' => Fu.ret (r'.1, rs ++ r'.2)
    | r => Fu.ret r

/-- The candidates of an elaboration continued by a list step of the typer.
No candidate after the step keeps the reasons of the elaboration, or adds a
mismatch when the step dropped candidates. -/
def thenL {s s' : Sig} {Γ : Ctx s} {Δ : Ctx s'} (a : Fu (Out Δ))
    (f : List (Elab Δ) → Fu (List (Elab Γ))) : Fu (Out Γ) :=
  Fu.bind a fun r => Fu.bind (f r.1) fun cs =>
    Fu.ret (cs, if cs.isEmpty then (if r.1.isEmpty then r.2 else r.2 ++ [.mismatch]) else [])

/-- The answer `a` when `stop` holds or the tank is marked, else `c`. -/
def stopOr {β : Type} (stop : Bool) (a : β) (c : Fu β) : Fu β := fun t =>
  if stop || t.out then (a, t) else c t

/-- Run `a`.  On an answer `ok` accepts, or on a marked tank, stop.  Otherwise
run `b` from the tank `a` left and keep the reasons of both. -/
def orElseW {α ρ : Type} (ok : α → Bool) (a : Fu (α × List ρ)) (b : Unit → Fu (α × List ρ)) :
    Fu (α × List ρ) :=
  Fu.bind a fun r => stopOr (ok r.1) r (Fu.bind (b ()) fun r' => Fu.ret (r'.1, r.2 ++ r'.2))

/-- The first answer over a list, in order, with the reasons of the failed
tries.  A marked tank stops, as `Fu.firstSome` does. -/
def firstSomeR {α β ρ : Type} (f : α → Fu (Option β × List ρ)) : List α → Fu (Option β × List ρ)
  | [] => Fu.ret (none, [])
  | x :: xs => orElseW Option.isSome (f x) (fun _ => firstSomeR f xs)

/-- Every answer over a list, in order, with every reason. -/
def flatMapR {α β ρ : Type} (f : α → Fu (List β × List ρ)) : List α → Fu (List β × List ρ)
  | [] => Fu.ret ([], [])
  | x :: xs =>
      Fu.bind (f x) fun r1 => Fu.bind (flatMapR f xs) fun r2 => Fu.ret (r1.1 ++ r2.1, r1.2 ++ r2.2)

/-- The answer `a` with the tank marked: the recursion limit. -/
def markAs {α : Type} (a : α) : Fu α := fun t => (a, { t with out := true })

/-! ## The function part of a goal

`Type.findFunctionType` on the shapes of the version, after
`strippedDealias`.  The lookups and the subtyping goals of a meet draw on the
tank.  The index of `funPartF` bounds the number of aliases followed.
`funPartOf` starts it at the fuel left, as `declsAt` starts a lookup, and every
alias followed draws at least one unit, so the index never runs out first. -/

/-- The function part of a goal. -/
inductive FunPart (s : Sig) where
  /-- No function part, the compiler's missing parameter type. -/
  | none
  /-- The goal is the function type `(∀(x : T1) T2) ^ C` itself. -/
  | direct (C : CaptureSet s) (T1 : Ty s) (T2 : Ty (s,x))
  /-- A function part with the domain `T1` and the result part `V`, reached
  through an intersection, an alias or a box. -/
  | side (T1 : Ty s) (V : Ty (s,x))
  /-- A function part the version cannot give, a type mismatch. -/
  | bad

/-- The bound of the first member with equal bounds, an alias. -/
def aliasOf {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} :
    List (TyMem Γ y A) → Option (Shape s)
  | [] => none
  | m :: ms => if m.1 = m.2.1 then some m.2.1 else aliasOf ms

/-- `bad` when one of the upper bounds has a function part, `none`
otherwise. -/
def uppersPart {s : Sig} (rec : Shape s → Fu (FunPart s)) : List (Shape s) → Fu (FunPart s)
  | [] => Fu.ret .none
  | S :: Ss =>
      Fu.bind (rec S) fun f =>
        match f with
        | .none => uppersPart rec Ss
        | _ => Fu.ret .bad

/-- The intersection of two result parts.  The shapes meet, and the set is the
atoms the two sets share, so the intersection is below both. -/
def meetRes {s : Sig} (V1 V2 : Ty s) : Ty s :=
  if V1 = V2 then V1
  else
    match V1, V2 with
    | .capt C1 S1, .capt C2 S2 => .capt (C1.filter fun a => CaptureSet.elem C2 a) (.and S1 S2)

/-- The meet of the function parts of two sides of an intersection, as
`findFunctionType` meets them with `&`.  Comparable domains give the larger
one and the intersection of the results. -/
def meetPart {s : Sig} (Γ : Ctx s) : FunPart s → FunPart s → Fu (FunPart s)
  | .bad, _ => Fu.ret .bad
  | _, .bad => Fu.ret .bad
  | .none, f => Fu.ret f
  | f, .none => Fu.ret f
  | .side S1 V1, .side S2 V2 =>
      if S1 = S2 then Fu.ret (.side S1 (meetRes V1 V2))
      else
        Fu.bind (subF Γ S2 S1) fun o2 =>
          match o2 with
          | some _ => Fu.ret (.side S1 (meetRes V1 V2))
          | none =>
              Fu.bind (subF Γ S1 S2) fun o1 =>
                match o1 with
                | some _ => Fu.ret (.side S2 (meetRes V1 V2))
                | none => Fu.ret .bad
  | _, _ => Fu.ret .bad

mutual
/-- The function part of a shape, with `rec` for the shape an alias stands for
and for an upper bound. -/
def funPartS {s : Sig} (Γ : Ctx s) (rec : Shape s → Fu (FunPart s)) : Shape s → Fu (FunPart s)
  | .all T1 T2 => Fu.ret (.side T1 T2)
  | .and S1 S2 =>
      Fu.bind (funPartS Γ rec S1) fun f1 =>
        Fu.bind (funPartS Γ rec S2) fun f2 => meetPart Γ f1 f2
  | .box T => funPartT Γ rec T
  | .sel (.var y) A =>
      Fu.bind (declsAt Γ y A) fun ms =>
        match aliasOf ms with
        | some S => rec S
        | none => uppersPart rec (ms.map fun m => m.2.1)
  | .top => Fu.ret .none
  | .bot => Fu.ret .none
  | .typ _ _ _ => Fu.ret .none
  | .fld _ _ => Fu.ret .none
  | .cap _ _ _ => Fu.ret .none
  | .mu _ => Fu.ret .none
/-- The function part of a type: its set dropped. -/
def funPartT {s : Sig} (Γ : Ctx s) (rec : Shape s → Fu (FunPart s)) : Ty s → Fu (FunPart s)
  | .capt _ S => funPartS Γ rec S
end

/-- The function part of a shape, following at most `d` aliases.  One more
marks the tank.  `seen` holds the shapes reached so far, and a shape reached
again has no function part, as the subtyping goal of the typer fails on a
goal it is already pursuing.  So a cycle of aliases stops at once. -/
def funPartF {s : Sig} (Γ : Ctx s) : Nat → List (Shape s) → Shape s → Fu (FunPart s)
  | 0, _, S => funPartS Γ (fun _ => markAs .none) S
  | d + 1, seen, S =>
      funPartS Γ (fun S' => if S' ∈ seen then Fu.ret .none else funPartF Γ d (S' :: seen) S') S

/-- The function part of an optional goal.  A function type at the top is
`direct` and draws nothing.  Any other goal is read from the fuel left. -/
def funPartOf {s : Sig} (Γ : Ctx s) : Option (Ty s) → Fu (FunPart s)
  | none => Fu.ret .none
  | some (.capt C (.all T1 T2)) => Fu.ret (.direct C T1 T2)
  | some (.capt _ S) => fun t => funPartF Γ t.left [S] S t

/-! ## The self shape a goal gives a literal -/

/-- A shape with its head alias followed, with `rec` for the next step. -/
def dealiasS {s : Sig} (Γ : Ctx s) (rec : Shape s → Fu (Shape s)) (S : Shape s) : Fu (Shape s) :=
  match S with
  | .sel (.var y) A =>
      Fu.bind (declsAt Γ y A) fun ms =>
        match aliasOf ms with
        | some S' => rec S'
        | none => Fu.ret S
  | _ => Fu.ret S

/-- A shape with at most `d` head aliases followed.  One more marks the
tank.  A shape reached again, held in `seen`, is where the walk stops. -/
def dealiasF {s : Sig} (Γ : Ctx s) : Nat → List (Shape s) → Shape s → Fu (Shape s)
  | 0, _, S => dealiasS Γ markAs S
  | d + 1, seen, S =>
      dealiasS Γ (fun S' => if S' ∈ seen then Fu.ret S' else dealiasF Γ d (S' :: seen) S') S

/-- A shape with its head aliases followed, from the fuel left. -/
def dealiasAt {s : Sig} (Γ : Ctx s) (S : Shape s) : Fu (Shape s) :=
  fun t => dealiasF Γ t.left [S] S t

/-- The self shape a goal gives a literal: the body of the `μ` its shape
dealiases to.  The goal's set is no part of the self shape. -/
def selfGoalF {s : Sig} (Γ : Ctx s) : Ty s → Fu (Option (Shape (s,x)))
  | .capt _ S =>
      Fu.bind (dealiasAt Γ S) fun S' =>
        match S' with
        | .mu B => Fu.ret (some B)
        | _ => Fu.ret none

/-! ## The goal of a call argument

The formals of a callee are the domains of the function types the lookup
finds for it.  A callee with no function type but a box gives the domains of
the function types it boxes, since the typer's application clause unboxes
such a callee first.  Several formals come from an intersection.  The
argument of an intersection callee is typed against the least upper bound of
the formals (`TypeComparer.distributeAnd`).  The version has no union, so the
goal is the dominant formal, the one every other formal is below. -/

/-- The domain of a boxed function type. -/
def boxDom? {s : Sig} {Γ : Ctx s} {g : BVar s .var} (b : BoxView Γ g) : Option (Ty s) :=
  match b.bsh with
  | .all T1 _ => some T1
  | _ => none

/-- The parameter types of the function types the lookup finds for `g`, or
of the function types it boxes when it has none. -/
def formalsF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (List (Ty s)) :=
  Fu.bind (fnViewsF Γ g) fun fs =>
    match fs with
    | [] => Fu.bind (boxViewsF Γ g) fun bs => Fu.ret (bs.filterMap boxDom?)
    | fs => Fu.ret (fs.map (·.dom))

/-- Every type of the list is `F` or below it by the subtyping goal. -/
def allBelowF {s : Sig} (Γ : Ctx s) (F : Ty s) : List (Ty s) → Fu Bool
  | [] => Fu.ret true
  | F' :: Fs =>
      if F' = F then allBelowF Γ F Fs
      else
        Fu.bind (subF Γ F' F) fun o =>
          match o with
          | some _ => allBelowF Γ F Fs
          | none => Fu.ret false

/-- The first type of `cands` that every type of `Fs` is below. -/
def dominantF {s : Sig} (Γ : Ctx s) (Fs : List (Ty s)) : List (Ty s) → Fu (Option (Ty s))
  | [] => Fu.ret none
  | F :: rest =>
      Fu.bind (allBelowF Γ F Fs) fun b => if b then Fu.ret (some F) else dominantF Γ Fs rest

/-- The dominant formal of `g`, the whole parameter type with its result.
`none` when `g` has no function type or no formal is dominant. -/
def argGoalF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (Option (Ty s)) :=
  Fu.bind (formalsF Γ g) fun Fs => dominantF Γ Fs Fs

/-- A formal as the compiler's typer sees it, with a box stripped.  The typer
of the compiler sees no boxes, and box inference boxes the argument when the
application is typed. -/
def stripBox {s : Sig} : Ty s → Ty s
  | .capt _ (.box T) => T
  | T => T

/-- A variable under one more binder, as a variable outside it: `none` for the
innermost binder. -/
def BVar.outer? {s : Sig} {k0 k : Kind} : BVar (s,,k0) k → Option (BVar s k)
  | .here => none
  | .there y => some y

/-- The callee of a body `g x`: `g`, when `x` is the innermost binder and `g`
a variable bound outside it. -/
def calleeOf? {s : Sig} : PTm (s,x) → Option (BVar s .var)
  | .app f y => if y = .here then BVar.outer? f else none
  | _ => none

/-- The callee of a call argument: `g` when the `let` is the binding the
resolver inserts at an operand, `let z = t in g z`. -/
def argCallee? {s : Sig} : LetTag → Option (Ty s) → PTm (s,x) → Option (BVar s .var)
  | .arg, none, u => calleeOf? u
  | _, _, _ => none

/-! ## Lambdas -/

/-- The typer's synthesis route for `λ(x : T). t`: the lambda at its least set
from the candidates of its body, moved to the goal. -/
def lamGenFin {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T) (G : Option (Ty s))
    (rs : List (Elab (Γ.cons T))) : Fu (List (Elab Γ)) :=
  Fu.bind (lamGenF Γ T hwf rs) (finishF Γ G)

/-- `λ(x : T). t`, whose body has an empty slot, at a goal with the function
part `fp`.  At a function type the body is checked against its codomain, as
the typer's clause does.  At a side the body is checked against the result
part, and the lambda moved to the goal.  If that gives nothing, the body is
synthesized and the lambda moved to the goal. -/
def lamAtF {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s)) (fp : FunPart s)
    (body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))) : Fu (Out Γ) :=
  if hwf : Ty.Wf T then
    orElseO
      (match fp with
        | .direct C T1' T2 => thenL (body (some T2)) (lamCheckF Γ T hwf C T1' T2)
        | .side _ V => thenL (body (some V)) (lamGenFin Γ T hwf G)
        | _ => Fu.ret ([], []))
      (thenL (body none) (lamGenFin Γ T hwf G))
  else Fu.ret ([], [.mismatch])

/-- A lambda with a written domain whose body has an empty slot. -/
def lamSomeF {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s))
    (body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))) : Fu (Out Γ) :=
  Fu.bind (funPartOf Γ G) fun fp => lamAtF Γ T G fp body

/-- A lambda without a domain whose goal has no function part, or with no
goal.  A body `g x` gives the domain: the dominant formal of `g`, as
`Typer.typedFunctionValue` reads the parameter type of the callee
(`calleeType`, `inferredFromTarget`).  The filled lambda goes to `inferF` with
the goal.  Any other body, or a callee with no dominant formal, is the
compiler's missing parameter type. -/
def lamCalleeF {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (t : PTm (s,x)) : Fu (Out Γ) :=
  match calleeOf? t with
  | some g =>
      Fu.bind (argGoalF Γ g) fun oS =>
        match oS, t.full? with
        | some S, some b => fullInfer Γ (.lam S b) G
        | _, _ => Fu.ret ([], [.missingParamType none])
  | none => Fu.ret ([], [.missingParamType none])

/-- A lambda without a domain.  The domain is the domain of the goal's
function part.  With a body that has no empty slot, the lambda filled with it
goes to `inferF` with the goal.  Otherwise `lamAtF`.  With no function part a
body `g x` gives the domain (`lamCalleeF`), and any other body is the
compiler's missing parameter type.  A function part the version cannot give
is a mismatch. -/
def lamNoneF {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (t : PTm (s,x))
    (body : (T1 : Ty s) → Option (Ty (s,x)) → Fu (Out (Γ.cons T1))) : Fu (Out Γ) :=
  Fu.bind (funPartOf Γ G) fun fp =>
    match fp with
    | .direct _ T1 _ =>
        match t.full? with
        | some b => fullInfer Γ (.lam T1 b) G
        | none => lamAtF Γ T1 G fp (body T1)
    | .side T1 _ =>
        match t.full? with
        | some b => fullInfer Γ (.lam T1 b) G
        | none => lamAtF Γ T1 G fp (body T1)
    | .none => lamCalleeF Γ G t
    | .bad => Fu.ret ([], [.mismatch])

/-! ## `let`

The typer's `let` clause with reasons: `letCheckF`, `letSpecialF` and
`letGenF` of `Typer.lean`, with the body an elaboration. -/

/-- The first candidate of the bound term whose body checks against `A` under
its binder, at the type `A`. -/
def letCheckO {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s) (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))) : Fu (Out Γ) :=
  Fu.bind (firstSomeR (fun r1 =>
      Fu.bind (body r1 (some A.weaken)) fun r2 =>
        match firstChecked r2.1 A.weaken with
        | some c => Fu.bind (letAtF Γ ann A r1 c) fun o =>
            Fu.ret (o, if o.isSome then ([] : List EReason) else [.mismatch])
        | none => Fu.ret (none, if r2.1.isEmpty then r2.2 else [.mismatch])) r1s) fun r =>
    Fu.ret (listO r.1, r.2)

/-- A `let` without annotation checked against a goal: its body checked
against the goal under the binder. -/
def letSpecialO {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s))
    (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))) : Fu (Out Γ) :=
  match ann, G with
  | none, some T => if tyWf? T then letCheckO Γ none T r1s body else Fu.ret ([], [])
  | _, _ => Fu.ret ([], [])

/-- A `let` synthesized: at its annotation, or every pair of candidates with
the body's type avoided. -/
def letGenO {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))) : Fu (Out Γ) :=
  match ann with
  | some A => letCheckO Γ (some A) A r1s body
  | none =>
      Fu.bind (flatMapR (fun r1 =>
          Fu.bind (body r1 none) fun r2 =>
            Fu.bind (Fu.flatMapL (fun r2' => mapL (letFinishF Γ r1 r2') id) r2.1) fun cs =>
              Fu.ret (cs, if cs.isEmpty then (if r2.1.isEmpty then r2.2 else [.mismatch])
                else ([] : List EReason)))
          r1s) fun r =>
        Fu.ret (dedupE r.1, r.2)

/-- A `let` from the candidates of its bound term: the body checked against
the goal first, as the typer's clause does, then synthesized and moved to the
goal.  No candidate of the bound term keeps its reasons. -/
def letO {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s)) (bound : Fu (Out Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))) : Fu (Out Γ) :=
  Fu.bind bound fun r1 =>
    if r1.1.isEmpty then Fu.ret ([], r1.2)
    else
      orElseO (letSpecialO Γ ann G r1.1 body)
        (thenL (letGenO Γ ann r1.1 body) (finishF Γ G))

/-! ## Call arguments -/

/-- A call argument `let z = t in g z`, whose bound term `t` has an empty
slot.  `arg F` elaborates `t` against the formal `F`, and only fills it.  The
`let` with the first candidate's term in place of `t` then goes to `inferF`
with the goal, so the typer binds `z` at the type it gives the filled
argument, and a closure keeps its least set, as
`CheckCaptures.recheckClosure` types a closure at its own use set.  With no
dominant formal, or when this gives nothing on an unmarked tank, `gen` types
the `let` as any other. -/
def argLetF {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (g : BVar s .var) (b : ATm (s,x))
    (arg : Ty s → Fu (Out Γ)) (gen : Unit → Fu (Out Γ)) : Fu (Out Γ) :=
  Fu.bind (argGoalF Γ g) fun oF =>
    match oF with
    | some F =>
        orElseW (fun cs => !cs.isEmpty)
          (Fu.bind (arg (stripBox F)) fun r =>
            match r.1 with
            | c :: _ => fullInfer Γ (.let none c.tm b) G
            | [] => Fu.ret ([], r.2))
          gen
    | none => gen ()

/-- A `let` whose body has no empty slot: a call argument when the resolver
inserted it at an operand, any other `let` otherwise. -/
def letF {s : Sig} (Γ : Ctx s) (tag : LetTag) (ann : Option (Ty s)) (u : PTm (s,x))
    (G : Option (Ty s)) (arg : Ty s → Fu (Out Γ)) (gen : Unit → Fu (Out Γ)) : Fu (Out Γ) :=
  match argCallee? tag ann u, u.full? with
  | some g, some b => argLetF Γ G g b arg gen
  | _, _ => gen ()

/-! ## Ascriptions -/

/-- `(t : T)` from the candidates of `t` checked against `T`, moved to the
goal, as the typer's clause. -/
def ascO {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s)) (r : Fu (Out Γ)) : Fu (Out Γ) :=
  thenL r fun rs =>
    finishF Γ G (listO ((firstChecked rs T).map fun c =>
      (⟨.asc c.tm T, c.uses, T, c.deriv⟩ : Elab Γ)))

/-! ## Object literals -/

/-- Every atom of a context: its term variables and capture binders. -/
def allAtoms {s : Sig} (Γ : Ctx s) : CaptureSet s :=
  (ctxVars Γ).map CapAtom.var ++ (ctxCaps Γ).map CapAtom.cvar

/-- The context in which the fields of a literal are elaborated: the self at
`μ` of the self shape, at the written set or at every atom of the context.  A
use of the self is then charged whenever the literal's set can be nonempty,
and the final check in the real context finds the least set. -/
def probeCtx {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (U0 : Option (CaptureSet s)) : Ctx (s,x) :=
  Γ.cons ((Shape.mu S) ^ (U0.getD (allAtoms Γ)))

/-- A literal with self shape `S` and set `U0`, its definitions filled by
`defs`, then typed by `inferF` with the goal. -/
def objSelfF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (U0 : Option (CaptureSet s))
    (G : Option (Ty s)) (defs : Fu (Option (ADefs (s,x)) × List EReason)) : Fu (Out Γ) :=
  Fu.bind defs fun r =>
    match r.1 with
    | some d' => fullInfer Γ (.obj S U0 d') G
    | none => Fu.ret ([], r.2)

/-! ## Self shapes formed from definitions

A literal without a self shape has it formed from its definitions, as the
completers of `Namer` type the members of a class.  A type member is known at
once at its right-hand side on both bounds, and a capture member at its set on
both bounds (`Namer.TypeDefCompleter.typeSig`).  A field with a written type is
known at once at it (`Namer.valOrDefDefSig`).  Every other field is typed on
demand (`Namer.inferredResultType`), in rounds.  `known` lists the fields typed
so far, by label. -/

/-- The first entry at a label. -/
def lookupL {β : Type} : List (Label × β) → Label → Option β
  | [], _ => none
  | (b, v) :: l, a => if a = b then some v else lookupL l a

/-- The self shape the definitions have so far.  A field not yet typed is
left out, and `none` means that nothing is known. -/
def PDefs.partialSelf {s : Sig} : PDefs s → List (Label × Ty s) → Option (Shape s)
  | .typ A S, _ => some (.typ A S S)
  | .cap C c, _ => some (.cap C c c)
  | .trm a (some T) _, _ => some (.fld a T)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.partialSelf known, e.partialSelf known with
      | some S1, some S2 => some (.and S1 S2)
      | some S1, none => some S1
      | none, o => o

/-- The snapshot a round types its jobs against: the self shape known so
far, or `⊤` when nothing is. -/
def PDefs.probeSelf {s : Sig} (d : PDefs s) (known : List (Label × Ty s)) : Shape s :=
  (d.partialSelf known).getD .top

/-- The self shape in lockstep with the definitions, once every field is
typed: the shape `DefsTy` concludes and `checkDefsF` reads. -/
def PDefs.fullSelf {s : Sig} : PDefs s → List (Label × Ty s) → Option (Shape s)
  | .typ A S, _ => some (.typ A S S)
  | .cap C c, _ => some (.cap C c c)
  | .trm a (some T) _, _ => some (.fld a T)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.fullSelf known, e.fullSelf known with
      | some S1, some S2 => some (.and S1 S2)
      | _, _ => none

/-- `S` is the self shape of `d` in lockstep.  A type member gives its
right-hand side on both bounds, a capture member its set on both bounds, a
field with a written type that type, any other field the first type `known`
gives its label, and an intersection of definitions the intersection of their
self shapes. -/
inductive Lockstep {s : Sig} (known : List (Label × Ty s)) : PDefs s → Shape s → Prop where
  /-- `{type A = S}` at `{A : S .. S}`. -/
  | typ (A : Label) (S : Shape s) : Lockstep known (.typ A S) (.typ A S S)
  /-- `{C^ = c}` at `{C^ : c .. c}`. -/
  | cap (C : Label) (c : CaptureSet s) : Lockstep known (.cap C c) (.cap C c c)
  /-- `{a : T = t}` at `{a : T}`. -/
  | written (a : Label) (T : Ty s) (t : PTm s) : Lockstep known (.trm a (some T) t) (.fld a T)
  /-- `{a = t}` at `{a : T}`, with `T` the type known at `a`. -/
  | inferred (a : Label) (T : Ty s) (t : PTm s) (h : lookupL known a = some T) :
      Lockstep known (.trm a none t) (.fld a T)
  /-- `d1 ∧ d2` at `S1 ∧ S2`. -/
  | and {d1 d2 : PDefs s} {S1 S2 : Shape s} :
      Lockstep known d1 S1 → Lockstep known d2 S2 → Lockstep known (.and d1 d2) (.and S1 S2)

/-- Every field of the definitions has a written type. -/
def PDefs.AllFieldsWritten {s : Sig} : PDefs s → Prop
  | .typ _ _ => True
  | .cap _ _ => True
  | .trm _ o _ => o.isSome = true
  | .and d e => d.AllFieldsWritten ∧ e.AllFieldsWritten

/-! ## Jobs

A job is a field without a written type.  It carries its elaboration as a
function of the context, so that a round can run it with the self bound at the
snapshot.  `jobsF` makes the jobs of a definition list inside the elaborator's
mutual block, where the elaboration of a field is a call on a subterm. -/

/-- A field without a written type: its label, its right-hand side, and its
elaboration with no goal in a context. -/
structure Job (s : Sig) where
  /-- The field's label. -/
  lbl : Label
  /-- The right-hand side. -/
  tm : PTm s
  /-- The elaboration of the right-hand side with no goal. -/
  run : (Γ : Ctx s) → Fu (Out Γ)

/-- The dependencies of a job on the self, the innermost variable. -/
def Job.deps {s : Sig} (j : Job (s,x)) : List Label × Bool := j.tm.deps [.here]

/-- A typed job: its label and right-hand side, the term elaborated from it,
and the type the rounds chose. -/
structure Done (s : Sig) where
  /-- The field's label. -/
  lbl : Label
  /-- The right-hand side. -/
  tm : PTm s
  /-- The elaborated right-hand side. -/
  a : ATm s
  /-- Its type, the least candidate's. -/
  ty : Ty s

/-- The fields typed so far, by label. -/
def Done.known {s : Sig} (ds : List (Done s)) : List (Label × Ty s) :=
  ds.map fun e => (e.lbl, e.ty)

/-! ## The least candidate

A field's type is the least type of its candidates: the type of the first
candidate that is below every other one by the subtyping goal, capture sets
included.  Every candidate is a type of the right-hand side, so a use that
needs another one reaches it by subsumption.  The choice does not depend on
the order of an intersection.  The compiler meets the candidates with
`Denotation.meet`, which the version cannot derive for a term that is not a
variable, so candidates with no least one are rejected as ambiguous. -/

/-- `T` is below every type of the list, or equal to it. -/
def belowAllF {s : Sig} (Γ : Ctx s) (T : Ty s) : List (Ty s) → Fu Bool
  | [] => Fu.ret true
  | U :: Us =>
      if T = U then belowAllF Γ T Us
      else
        Fu.bind (subF Γ T U) fun o =>
          match o with
          | some _ => belowAllF Γ T Us
          | none => Fu.ret false

/-- The first candidate of the list whose type is below every type of
`Ts`. -/
def leastFromF {s : Sig} (Γ : Ctx s) (Ts : List (Ty s)) : List (Elab Γ) → Fu (Option (Elab Γ))
  | [] => Fu.ret none
  | c :: rest =>
      Fu.bind (belowAllF Γ c.ty Ts) fun b => if b then Fu.ret (some c) else leastFromF Γ Ts rest

/-- The least candidate: the first one whose type is below the type of every
candidate. -/
def leastCandF {s : Sig} (Γ : Ctx s) (cs : List (Elab Γ)) : Fu (Option (Elab Γ)) :=
  leastFromF Γ (cs.map (·.ty)) cs

/-! ## Rounds

A round takes a snapshot of the self shape known so far and types every ready
job once, with no goal, in the probe context: the self at `μ` of the
snapshot, at the written set or at every atom of the context (`probeCtx`).  A
job is ready when none of the labels it projects off the self is pending.  A
job that uses the self any other way waits for the first round in which no
ready job lacks such a use.  So two such jobs do not see each other, and a job
that projects the field of one sees it.  The number of rounds is an index, so
the rounds are structural. -/

/-- A job is ready when none of the labels it projects off the self is
pending. -/
def readyIn {s : Sig} (pend : List Label) (j : Job (s,x)) : Bool :=
  j.deps.1.all fun a => !pend.contains a

/-- Whether a round types the jobs that use the self bare: when no ready job
lacks such a use. -/
def bareRound {s : Sig} (js : List (Job (s,x))) : Bool :=
  !(js.any fun j => readyIn (js.map (·.lbl)) j && !j.deps.2)

/-- Whether a round over the pending jobs `js` types `j`: it is ready, and it
uses the self bare exactly when the round types such jobs. -/
def picks {s : Sig} (js : List (Job (s,x))) (j : Job (s,x)) : Bool :=
  readyIn (js.map (·.lbl)) j && decide (j.deps.2 = bareRound js)

/-- A job typed against the snapshot `P`: its elaboration in the probe
context, and its type the least candidate.  No candidate gives the reasons of
the elaboration, and candidates with no least one give `ambiguous`. -/
def runJobF {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (P : Shape (s,x))
    (j : Job (s,x)) : Fu (Except (List EReason) (Done (s,x))) :=
  Fu.bind (j.run (probeCtx Γ P U0)) fun r =>
    match r.1 with
    | [] => Fu.ret (.error r.2)
    | c :: cs =>
        Fu.bind (leastCandF (probeCtx Γ P U0) (c :: cs)) fun o =>
          match o with
          | some e => Fu.ret (.ok ⟨j.lbl, j.tm, e.tm, e.ty⟩)
          | none => Fu.ret (.error [.ambiguous j.lbl])

/-- One round: the jobs typed against the snapshot `P`, in source order.  The
first failure stops it. -/
def roundF {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (P : Shape (s,x)) :
    List (Job (s,x)) → Fu (Except (List EReason) (List (Done (s,x))))
  | [] => Fu.ret (.ok [])
  | j :: js =>
      Fu.bind (runJobF Γ U0 P j) fun r =>
        match r with
        | .ok e =>
            Fu.bind (roundF Γ U0 P js) fun r' =>
              match r' with
              | .ok es => Fu.ret (.ok (e :: es))
              | .error rs => Fu.ret (.error rs)
        | .error rs => Fu.ret (.error rs)

/-! ## The cyclic reference

A round that types nothing has every pending job waiting for a pending label.
The walk starts at the first pending job in source order and follows the
first pending label it waits for, until a label repeats.  That label is the
cyclic reference, the member `SymDenotation.completeFrom` reaches again while
its completion is under way. -/

/-- The pending labels a job projects off the self, in term order. -/
def waitsFor {s : Sig} (js : List (Job (s,x))) (j : Job (s,x)) : List Label :=
  j.deps.1.filter fun a => (js.map (·.lbl)).contains a

/-- The label the walk visits after `l`: the first pending label that the
first job at `l` waits for. -/
def nextL {s : Sig} (js : List (Job (s,x))) (l : Label) : Option Label :=
  match js.find? (fun j => decide (j.lbl = l)) with
  | some j => (waitsFor js j).head?
  | none => none

/-- The walk from `l`, with the labels `seen` before it, for at most `n`
steps: the first label it visits twice. -/
def cycleFrom {s : Sig} (js : List (Job (s,x))) : Nat → List Label → Label → Option Label
  | 0, _, _ => none
  | n + 1, seen, l =>
      if seen.contains l then some l
      else
        match nextL js l with
        | some l' => cycleFrom js n (l :: seen) l'
        | none => none

/-- The cyclic reference among the pending jobs: the first label the walk
from the first job visits twice, within `n` steps. -/
def cycleAt {s : Sig} (js : List (Job (s,x))) (n : Nat) : Option Label :=
  match js with
  | [] => none
  | j :: _ => cycleFrom js n [] j.lbl

/-- The label the walk reaches from `l` in `k` steps. -/
def walkL {s : Sig} (js : List (Job (s,x))) : Nat → Label → Option Label
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

/-- Rounds until every job is typed, at most `n` of them.  `probe` gives the
snapshot from the fields typed so far, and `done` lists them.  A round that
types nothing stops with the cyclic reference. -/
def roundsF {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s))
    (probe : List (Label × Ty (s,x)) → Shape (s,x)) :
    Nat → List (Job (s,x)) → List (Done (s,x)) → Fu (Except (List EReason) (List (Done (s,x))))
  | _, [], done => Fu.ret (.ok done)
  | 0, j :: js, _ => Fu.ret (.error [stallReason (j :: js)])
  | n + 1, j :: js, done =>
      if ((j :: js).filter (picks (j :: js))).isEmpty then Fu.ret (.error [stallReason (j :: js)])
      else
        Fu.bind (roundF Γ U0 (probe (Done.known done)) ((j :: js).filter (picks (j :: js))))
          fun r =>
            match r with
            | .ok new =>
                roundsF Γ U0 probe n ((j :: js).filter fun k => !picks (j :: js) k) (done ++ new)
            | .error rs => Fu.ret (.error rs)

/-- The self shape of a literal with set `U0` formed from its definitions `d`
in `Γ`, with their jobs `js`: the rounds, then the self shape in lockstep,
with the typed jobs.  One round per job suffices, and one more stops. -/
def formSelfF {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (d : PDefs (s,x))
    (js : List (Job (s,x))) : Fu (Except (List EReason) (Shape (s,x) × List (Done (s,x)))) :=
  Fu.bind (roundsF Γ U0 d.probeSelf (js.length + 1) js []) fun r =>
    match r with
    | .ok done =>
        Fu.ret (match d.fullSelf (Done.known done) with
          | some S => .ok (S, done)
          | none => .error [.mismatch])
    | .error rs => Fu.ret (.error rs)

/-! ## The filled literal

Once the self shape is formed, the literal is filled and handed to `inferF`
in the real context, with the goal.  A field without a written type holds the
term the rounds elaborated for it, so no field is elaborated twice.  A field
with a written type and an empty slot is elaborated against that type, with
the self at the formed shape (`probeCtx`).  The typer then checks every field
once more, finds the least set and moves the literal to the goal. -/

/-- The first typed job at a label. -/
def lookupDone {s : Sig} : List (Done s) → Label → Option (Done s)
  | [], _ => none
  | e :: es, a => if e.lbl = a then some e else lookupDone es a

/-- A literal without a self shape, with set `U0`, at the goal `G`: the self
shape formed by `form`, the definitions filled at it by `fill`, then the
filled literal typed by `inferF` with the goal (`objSelfF`).  The reasons of
the rounds or of the filling reject it. -/
def objNoneF {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (G : Option (Ty s))
    (form : Fu (Except (List EReason) (Shape (s,x) × List (Done (s,x)))))
    (fill : Shape (s,x) → List (Done (s,x)) → Fu (Option (ADefs (s,x)) × List EReason)) :
    Fu (Out Γ) :=
  Fu.bind form fun r =>
    match r with
    | .ok (S, done) => objSelfF Γ S U0 G (fill S done)
    | .error rs => Fu.ret ([], rs)

/-! ## The elaborator -/

mutual

/-- The candidates of a partial term at an optional goal.  A term with no
empty slot goes to `inferF`. -/
def elabF {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Option (Ty s)) : Fu (Out Γ) :=
  match p.full? with
  | some a => fullInfer Γ a G
  | none =>
      match p with
      | .lam (some T) t => lamSomeF Γ T G (fun o => elabF (Γ.cons T) t o)
      | .lam none t => lamNoneF Γ G t (fun T1 o => elabF (Γ.cons T1) t o)
      | .obj (some S) U0 d => objSelfF Γ S U0 G (elabDefsF (probeCtx Γ S U0) d S)
      | .obj none U0 d =>
          match G with
          | some T =>
              Fu.bind (selfGoalF Γ T) fun oS =>
                match oS with
                | some S =>
                    orElseW (fun cs => !cs.isEmpty)
                      (objSelfF Γ S U0 G (elabDefsF (probeCtx Γ S U0) d S))
                      (fun _ => objNoneF Γ U0 G (formSelfF Γ U0 d (jobsF d))
                        fun S' done => fillDefsF (probeCtx Γ S' U0) done d S')
                | none =>
                    objNoneF Γ U0 G (formSelfF Γ U0 d (jobsF d))
                      fun S' done => fillDefsF (probeCtx Γ S' U0) done d S'
          | none =>
              objNoneF Γ U0 none (formSelfF Γ U0 d (jobsF d))
                fun S done => fillDefsF (probeCtx Γ S U0) done d S
      | .let tag ann t u =>
          letF Γ tag ann u G (fun F => elabF Γ t (some F))
            (fun _ => letO Γ ann G (elabF Γ t none) (fun r1 o => elabF (Γ.cons r1.ty) u o))
      | .asc t T => ascO Γ T G (elabF Γ t (some T))
      | .path _ => Fu.ret ([], [.mismatch])
      | .app _ _ => Fu.ret ([], [.mismatch])
      | .proj _ _ => Fu.ret ([], [.mismatch])
      | .box _ => Fu.ret ([], [.mismatch])
      | .unbox _ _ => Fu.ret ([], [.mismatch])
termination_by structural p

/-- The definitions of a literal filled against its self shape, in lockstep.
A type or capture member stays.  A field with no empty slot stays as written.
Any other field is elaborated against its type in the shape and holds the
first candidate.  A written field type must be the shape's.  No derivation is
kept: the typer checks the filled literal. -/
def elabDefsF {s : Sig} (Γ : Ctx s) (d : PDefs s) (S : Shape s) :
    Fu (Option (ADefs s) × List EReason) :=
  match d, S with
  | .typ A S0, _ => Fu.ret (some (.typ A S0), [])
  | .cap C c, _ => Fu.ret (some (.cap C c), [])
  | .trm a o t, .fld _ T =>
      if optAgree o T then
        match t.full? with
        | some b => Fu.ret (some (.trm a b), [])
        | none => Fu.bind (elabF Γ t (some T)) fun r =>
            Fu.ret (r.1.head?.map fun c => ADefs.trm a c.tm, r.2)
      else Fu.ret (none, [.mismatch])
  | .and d1 d2, .and S1 S2 =>
      Fu.bind (elabDefsF Γ d1 S1) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (elabDefsF Γ d2 S2) fun r2 =>
              Fu.ret (r2.1.map (ADefs.and e1), r2.2)
        | none => Fu.ret (none, r1.2)
  | _, _ => Fu.ret (none, [.mismatch])
termination_by structural d

/-- The jobs of a definition list: every field without a written type, in
source order, with its elaboration by `elabF` with no goal. -/
def jobsF {s : Sig} : PDefs s → List (Job s)
  | .typ _ _ => []
  | .cap _ _ => []
  | .trm _ (some _) _ => []
  | .trm a none t => [⟨a, t, fun Γ => elabF Γ t none⟩]
  | .and d1 d2 => jobsF d1 ++ jobsF d2
termination_by structural d => d

/-- The definitions of a literal filled at its formed self shape, in
lockstep.  A type or capture member stays.  A field without a written type
holds the first typed job at its label.  A field with a written type holds its
right-hand side when that has no empty slot, and else the first candidate of
its elaboration against the type.  No derivation is kept: the typer checks the
filled literal. -/
def fillDefsF {s : Sig} (Γ : Ctx s) (done : List (Done s)) (d : PDefs s) (S : Shape s) :
    Fu (Option (ADefs s) × List EReason) :=
  match d, S with
  | .typ A S0, _ => Fu.ret (some (.typ A S0), [])
  | .cap C c, _ => Fu.ret (some (.cap C c), [])
  | .trm a none _, _ =>
      match lookupDone done a with
      | some e => Fu.ret (some (.trm a e.a), [])
      | none => Fu.ret (none, [.mismatch])
  | .trm a (some T) t, .fld _ W =>
      if T = W then
        match t.full? with
        | some b => Fu.ret (some (.trm a b), [])
        | none => Fu.bind (elabF Γ t (some W)) fun r =>
            Fu.ret (r.1.head?.map fun c => ADefs.trm a c.tm, r.2)
      else Fu.ret (none, [.mismatch])
  | .and d1 d2, .and S1 S2 =>
      Fu.bind (fillDefsF Γ done d1 S1) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (fillDefsF Γ done d2 S2) fun r2 =>
              Fu.ret (r2.1.map (ADefs.and e1), r2.2)
        | none => Fu.ret (none, r1.2)
  | _, _ => Fu.ret (none, [.mismatch])
termination_by structural d

end

/-! ## The entry point -/

/-- The first candidate of a closed partial term over a platform, from a full
tank of `n` units, or the reason it is rejected, with the tank left. -/
def elabTopF (n : Nat) (π : PlatformNames) (p : PTm π.sig) :
    Except EReason (Elab (platformCtx π.plat)) × Tank :=
  match elabF (platformCtx π.plat) p none ⟨n, false⟩ with
  | ((c :: _, _), t) => (if t.out then .error .limit else .ok c, t)
  | (([], rs), t) => (.error (Reason.top t.out rs), t)

/-! ## Every slot written

A term with no empty slot is the typer's: candidates, derivations and tank. -/

theorem elabF_full {s : Sig} (Γ : Ctx s) {p : PTm s} {a : ATm s} (h : p.full? = some a)
    (G : Option (Ty s)) : elabF Γ p G = fullInfer Γ a G := by
  unfold elabF
  rw [h]

theorem elabF_toI {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Option (Ty s)) :
    elabF Γ a.toI G = fullInfer Γ a G :=
  elabF_full Γ (ATm.full?_toI a) G

/-! ## A lambda without a domain -/

theorem elabF_lam_none {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (G : Option (Ty s)) :
    elabF Γ (.lam none t) G = lamNoneF Γ G t (fun T1 o => elabF (Γ.cons T1) t o) := by
  rw [elabF]
  rfl

/-! ## The goal of a call argument

The goal is one of the formals, and every formal is below it.  So the domain
a call argument or a callee's body takes is the least upper bound of the
formals, the compiler's choice, whenever that bound is a formal. -/

theorem allBelowF_sub {s : Sig} {Γ : Ctx s} {F : Ty s} :
    ∀ {Fs : List (Ty s)} {t t' : Tank}, allBelowF Γ F Fs t = (true, t') →
      ∀ F' ∈ Fs, Nonempty (Sub Γ F' F)
  | [], _, _, _, F', hF' => absurd hF' List.not_mem_nil
  | F'' :: Fs, t, t', h, F', hF' => by
    unfold allBelowF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hF' with rfl | hm
      · exact ⟨heq ▸ Sub.refl _⟩
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

theorem dominantF_sub {s : Sig} {Γ : Ctx s} {Fs : List (Ty s)} :
    ∀ {cands : List (Ty s)} {t : Tank} {F : Ty s} {t' : Tank},
      dominantF Γ Fs cands t = (some F, t') → F ∈ cands ∧ ∀ F' ∈ Fs, Nonempty (Sub Γ F' F)
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

/-- The goal of an argument of `g` is one of its formals, and every formal is
below it. -/
theorem argGoal_dominant {s : Sig} {Γ : Ctx s} {g : BVar s .var} {tk : Tank} {F : Ty s}
    (h : (argGoalF Γ g tk).1 = some F) :
    ∃ Fs tk', formalsF Γ g tk = (Fs, tk') ∧ F ∈ Fs ∧ ∀ F' ∈ Fs, Nonempty (Sub Γ F' F) := by
  cases hf : formalsF Γ g tk with
  | mk Fs t1 =>
    unfold argGoalF at h
    simp only [Fu.bind, hf] at h
    cases hd : dominantF Γ Fs Fs t1 with
    | mk o t2 =>
      rw [hd] at h
      simp only at h
      subst h
      exact ⟨Fs, t1, rfl, dominantF_sub hd⟩

/-! ## A call argument -/

/-- A call argument whose bound term has an empty slot takes the clause of
call arguments, with the bound term elaborated against the formal and, as
the fallback, the clause of any other `let`. -/
theorem elabF_arg {s : Sig} (Γ : Ctx s) {t : PTm s} (ht : t.full? = none) (g : BVar s .var)
    (G : Option (Ty s)) :
    elabF Γ (.let .arg none t (.app (.there g) .here)) G =
      argLetF Γ G g (.app (.there g) .here) (fun F => elabF Γ t (some F))
        (fun _ => letO Γ none G (elabF Γ t none)
          (fun r1 o => elabF (Γ.cons r1.ty) (.app (.there g) .here) o)) := by
  rw [elabF]
  simp only [PTm.full?, ht]
  rfl

/-! ## The callee's body -/

/-- A body whose callee is `g` is `g x`. -/
theorem calleeOf?_eq {s : Sig} {t : PTm (s,x)} {g : BVar s .var} (h : calleeOf? t = some g) :
    t = .app (.there g) .here := by
  cases t with
  | app f y =>
    by_cases hy : y = .here
    · subst hy
      have h' : BVar.outer? f = some g := by
        rw [← h]
        show _ = (if (BVar.here : BVar (s,x) .var) = .here then BVar.outer? f else none)
        exact (if_pos rfl).symm
      cases f with
      | here => cases h'
      | there f' =>
        cases h'
        rfl
    · have h' : (none : Option (BVar s .var)) = some g := by
        rw [← h]
        show _ = (if y = .here then BVar.outer? f else none)
        exact (if_neg hy).symm
      cases h'
  | _ => cases h

theorem calleeOf?_app {s : Sig} (g : BVar s .var) :
    calleeOf? (.app (.there g) .here : PTm (s,x)) = some g := rfl

/-- A body `g x` at a goal with no function part, or at no goal: the
elaborator is the typer on the lambda filled with the dominant formal of `g`,
candidates and tank. -/
theorem lam_callee_full {s : Sig} {Γ : Ctx s} {g : BVar s .var} {G : Option (Ty s)}
    {tk tk1 tk2 : Tank} {S : Ty s} (hf : funPartOf Γ G tk = (.none, tk1))
    (h : argGoalF Γ g tk1 = (some S, tk2)) :
    elabF Γ (.lam none (.app (.there g) .here)) G tk =
      fullInfer Γ (.lam S (.app (.there g) .here)) G tk2 := by
  rw [elabF_lam_none]
  unfold lamNoneF
  simp only [Fu.bind, hf]
  unfold lamCalleeF
  rw [calleeOf?_app]
  simp only [Fu.bind, h, PTm.full?]

/-! ## The frame lemmas of the combinators -/

section CombinatorFrames

variable {α β ρ : Type}

theorem stopOr_framed {stop : Bool} {a : β} {c : Fu β} (hc : Framed c) :
    Framed (stopOr stop a c) where
  absorbs t ht := by simp [stopOr, ht]
  spends t := by
    unfold stopOr
    split
    · exact Nat.le_refl _
    · exact hc.spends t
  shift := by
    intro t r t' h ho k
    unfold stopOr at h ⊢
    by_cases hs : (stop || t.out) = true
    · rw [if_pos hs] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (by simpa using hs)]
    · rw [if_neg hs] at h
      rw [if_neg (by simpa using hs)]
      exact hc.shift t r t' h ho k

theorem orElseW_framed {ok : α → Bool} {a : Fu (α × List ρ)} {b : Unit → Fu (α × List ρ)}
    (ha : Framed a) (hb : Framed (b ())) : Framed (orElseW ok a b) :=
  bind_framed ha fun _ => stopOr_framed (bind_framed hb fun _ => ret_framed _)

theorem firstSomeR_framed {f : α → Fu (Option β × List ρ)} (hf : ∀ x, Framed (f x)) :
    ∀ l, Framed (firstSomeR f l)
  | [] => ret_framed _
  | x :: xs => orElseW_framed (hf x) (firstSomeR_framed hf xs)

theorem flatMapR_framed {f : α → Fu (List β × List ρ)} (hf : ∀ x, Framed (f x)) :
    ∀ l, Framed (flatMapR f l)
  | [] => ret_framed _
  | x :: xs => bind_framed (hf x) fun _ => bind_framed (flatMapR_framed hf xs) fun _ => ret_framed _

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

theorem withR_framed {c : Fu (List α)} (hc : Framed c) : Framed (withR c) :=
  bind_framed hc fun _ => ret_framed _

end CombinatorFrames

theorem fullInfer_framed {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Option (Ty s)) :
    Framed (fullInfer Γ a G) :=
  withR_framed (inferF_framed Γ a G)

theorem orElseO_framed {s : Sig} {Γ : Ctx s} {a b : Fu (Out Γ)} (ha : Framed a) (hb : Framed b) :
    Framed (orElseO a b) := by
  refine bind_framed ha fun r => ?_
  obtain ⟨l, rs⟩ := r
  cases l with
  | nil => exact bind_framed hb fun _ => ret_framed _
  | cons _ _ => exact ret_framed _

theorem thenL_framed {s s' : Sig} {Γ : Ctx s} {Δ : Ctx s'} {a : Fu (Out Δ)}
    {f : List (Elab Δ) → Fu (List (Elab Γ))} (ha : Framed a) (hf : ∀ l, Framed (f l)) :
    Framed (thenL a f) :=
  bind_framed ha fun r => bind_framed (hf r.1) fun _ => ret_framed _

/-! ## The frame lemmas of the goal readers

`funPartF` and `dealiasF` at an index agree with themselves at any larger
index, as the lookup does (`look_agree`).  So the forms that start the index
at the fuel left are framed. -/

theorem uppersPart_agree {s : Sig} {rec rec' : Shape s → Fu (FunPart s)}
    (hr : ∀ S, Agree (rec S) (rec' S)) : ∀ Ss, Agree (uppersPart rec Ss) (uppersPart rec' Ss)
  | [] => ret_agree _
  | S :: Ss => by
    refine bind_agree (hr S) fun f => ?_
    cases f with
    | none => exact uppersPart_agree hr Ss
    | direct _ _ _ => exact ret_agree _
    | side _ _ => exact ret_agree _
    | bad => exact ret_agree _

theorem meetPart_framed {s : Sig} (Γ : Ctx s) (f1 f2 : FunPart s) :
    Framed (meetPart Γ f1 f2) := by
  cases f1 <;> cases f2 <;> simp only [meetPart] <;> try exact ret_framed _
  refine ite_framed (ret_framed _) (bind_framed (subF_framed _ _ _) fun o2 => ?_)
  cases o2 with
  | some _ => exact ret_framed _
  | none =>
    refine bind_framed (subF_framed _ _ _) fun o1 => ?_
    cases o1 with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

mutual

theorem funPartS_agree {s : Sig} (Γ : Ctx s) {rec rec' : Shape s → Fu (FunPart s)}
    (hr : ∀ S, Agree (rec S) (rec' S)) : ∀ S, Agree (funPartS Γ rec S) (funPartS Γ rec' S)
  | .all _ _ => ret_agree _
  | .and S1 S2 =>
    bind_agree (funPartS_agree Γ hr S1) fun _ =>
      bind_agree (funPartS_agree Γ hr S2) fun _ => Agree.refl (meetPart_framed _ _ _)
  | .box T => funPartT_agree Γ hr T
  | .sel (.var y) A => by
    refine bind_agree (Agree.refl (declsAt_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact uppersPart_agree hr _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .typ _ _ _ => ret_agree _
  | .fld _ _ => ret_agree _
  | .cap _ _ _ => ret_agree _
  | .mu _ => ret_agree _

theorem funPartT_agree {s : Sig} (Γ : Ctx s) {rec rec' : Shape s → Fu (FunPart s)}
    (hr : ∀ S, Agree (rec S) (rec' S)) : ∀ T, Agree (funPartT Γ rec T) (funPartT Γ rec' T)
  | .capt _ S => funPartS_agree Γ hr S

end

theorem funPartF_framed {s : Sig} (Γ : Ctx s) : ∀ d seen S, Framed (funPartF Γ d seen S)
  | 0, _, S => (funPartS_agree Γ (fun _ => Agree.refl (markAs_framed _)) S).left
  | d + 1, seen, S =>
    (funPartS_agree Γ (fun S' => Agree.refl
      (ite_framed (ret_framed _) (funPartF_framed Γ d (S' :: seen) S'))) S).left

theorem funPartF_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ seen S, Agree (funPartF Γ d seen S) (funPartF Γ d' seen S)
  | 0, d', _, seen, S => by
    cases d' with
    | zero => exact Agree.refl (funPartF_framed Γ 0 seen S)
    | succ e =>
      exact funPartS_agree Γ (fun S' => markAs_agree _
        (ite_framed (ret_framed _) (funPartF_framed Γ e (S' :: seen) S'))) S
  | d + 1, d', hd, seen, S => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact funPartS_agree Γ (fun S' => ite_agree (ret_agree _)
      (funPartF_agree Γ d e (by omega) (S' :: seen) S')) S

/-- The function part of a shape from the fuel left is framed. -/
theorem funPartAt_framed {s : Sig} (Γ : Ctx s) (S : Shape s) :
    Framed (fun t => funPartF Γ t.left [S] S t) where
  absorbs t ht := (funPartF_framed Γ t.left [S] S).absorbs t ht
  spends t := (funPartF_framed Γ t.left [S] S).spends t
  shift := by
    intro t r t' h ho k
    exact (funPartF_agree Γ t.left (t.left + k) (Nat.le_add_right _ _) [S] S).sim t r t' h ho k

theorem funPartOf_framed {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) : Framed (funPartOf Γ G) := by
  cases G with
  | none => exact ret_framed _
  | some T =>
    obtain ⟨C, S⟩ := T
    cases S <;> first | exact ret_framed _ | exact funPartAt_framed Γ _

theorem dealiasS_agree {s : Sig} (Γ : Ctx s) {rec rec' : Shape s → Fu (Shape s)}
    (hr : ∀ S, Agree (rec S) (rec' S)) (S : Shape s) :
    Agree (dealiasS Γ rec S) (dealiasS Γ rec' S) := by
  unfold dealiasS
  split
  · refine bind_agree (Agree.refl (declsAt_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact ret_agree _
  · exact ret_agree _

theorem dealiasF_framed {s : Sig} (Γ : Ctx s) : ∀ d seen S, Framed (dealiasF Γ d seen S)
  | 0, _, S => (dealiasS_agree Γ (fun S' => Agree.refl (markAs_framed S')) S).left
  | d + 1, seen, S =>
    (dealiasS_agree Γ (fun S' => Agree.refl
      (ite_framed (ret_framed _) (dealiasF_framed Γ d (S' :: seen) S'))) S).left

theorem dealiasF_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ seen S, Agree (dealiasF Γ d seen S) (dealiasF Γ d' seen S)
  | 0, d', _, seen, S => by
    cases d' with
    | zero => exact Agree.refl (dealiasF_framed Γ 0 seen S)
    | succ e =>
      exact dealiasS_agree Γ (fun S' => markAs_agree S'
        (ite_framed (ret_framed _) (dealiasF_framed Γ e (S' :: seen) S'))) S
  | d + 1, d', hd, seen, S => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact dealiasS_agree Γ (fun S' => ite_agree (ret_agree _)
      (dealiasF_agree Γ d e (by omega) (S' :: seen) S')) S

theorem dealiasAt_framed {s : Sig} (Γ : Ctx s) (S : Shape s) : Framed (dealiasAt Γ S) where
  absorbs t ht := (dealiasF_framed Γ t.left [S] S).absorbs t ht
  spends t := (dealiasF_framed Γ t.left [S] S).spends t
  shift := by
    intro t r t' h ho k
    exact (dealiasF_agree Γ t.left (t.left + k) (Nat.le_add_right _ _) [S] S).sim t r t' h ho k

theorem selfGoalF_framed {s : Sig} (Γ : Ctx s) (G : Ty s) : Framed (selfGoalF Γ G) := by
  obtain ⟨C, S⟩ := G
  unfold selfGoalF
  refine bind_framed (dealiasAt_framed Γ S) fun S' => ?_
  cases S' <;> exact ret_framed _

theorem formalsF_framed {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Framed (formalsF Γ g) := by
  refine bind_framed (fnViewsF_framed _ _) fun fs => ?_
  cases fs with
  | nil => exact bind_framed (boxViewsF_framed _ _) fun _ => ret_framed _
  | cons _ _ => exact ret_framed _

theorem allBelowF_framed {s : Sig} (Γ : Ctx s) (F : Ty s) : ∀ Fs, Framed (allBelowF Γ F Fs)
  | [] => ret_framed _
  | F' :: Fs => by
    unfold allBelowF
    split
    · exact allBelowF_framed Γ F Fs
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact allBelowF_framed Γ F Fs
      | none => exact ret_framed _

theorem dominantF_framed {s : Sig} (Γ : Ctx s) (Fs : List (Ty s)) :
    ∀ cands, Framed (dominantF Γ Fs cands)
  | [] => ret_framed _
  | F :: rest => by
    refine bind_framed (allBelowF_framed Γ F Fs) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact dominantF_framed Γ Fs rest

theorem argGoalF_framed {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Framed (argGoalF Γ g) :=
  bind_framed (formalsF_framed Γ g) fun Fs => dominantF_framed Γ Fs Fs

/-! ## The frame lemmas of the clauses -/

theorem lamGenFin_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T) (G : Option (Ty s))
    (rs : List (Elab (Γ.cons T))) : Framed (lamGenFin Γ T hwf G rs) :=
  bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _

theorem lamAtF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s)) (fp : FunPart s)
    {body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))} (hb : ∀ o, Framed (body o)) :
    Framed (lamAtF Γ T G fp body) := by
  unfold lamAtF
  refine dite_framed (fun hwf => orElseO_framed ?_ ?_) (fun _ => ret_framed _)
  · cases fp with
    | direct C T1' T2 => exact thenL_framed (hb _) fun _ => lamCheckF_framed _ _ _ _ _ _ _
    | side _ V => exact thenL_framed (hb _) fun _ => lamGenFin_framed _ _ _ _ _
    | none => exact ret_framed _
    | bad => exact ret_framed _
  · exact thenL_framed (hb _) fun _ => lamGenFin_framed _ _ _ _ _

theorem lamSomeF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s))
    {body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))} (hb : ∀ o, Framed (body o)) :
    Framed (lamSomeF Γ T G body) :=
  bind_framed (funPartOf_framed _ _) fun fp => lamAtF_framed _ _ _ fp hb

theorem lamCalleeF_framed {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (t : PTm (s,x)) :
    Framed (lamCalleeF Γ G t) := by
  unfold lamCalleeF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oS => ?_
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  · exact ret_framed _

theorem lamNoneF_framed {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (t : PTm (s,x))
    {body : (T1 : Ty s) → Option (Ty (s,x)) → Fu (Out (Γ.cons T1))}
    (hb : ∀ T1 o, Framed (body T1 o)) : Framed (lamNoneF Γ G t body) := by
  refine bind_framed (funPartOf_framed _ _) fun fp => ?_
  cases fp with
  | direct C T1 T2 =>
    show Framed (match t.full? with
      | some b => fullInfer Γ (.lam T1 b) G
      | none => lamAtF Γ T1 G (.direct C T1 T2) (body T1))
    split
    · exact fullInfer_framed _ _ _
    · exact lamAtF_framed _ _ _ _ (hb T1)
  | side T1 V =>
    show Framed (match t.full? with
      | some b => fullInfer Γ (.lam T1 b) G
      | none => lamAtF Γ T1 G (.side T1 V) (body T1))
    split
    · exact fullInfer_framed _ _ _
    · exact lamAtF_framed _ _ _ _ (hb T1)
  | none => exact lamCalleeF_framed _ _ _
  | bad => exact ret_framed _

theorem letCheckO_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s)
    (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letCheckO Γ ann A r1s body) := by
  refine bind_framed (firstSomeR_framed (fun r1 => bind_framed (hb _ _) fun r2 => ?_) r1s)
    fun _ => ret_framed _
  dsimp only
  split
  · exact bind_framed (letAtF_framed _ _ _ _ _) fun _ => ret_framed _
  · exact ret_framed _

theorem letSpecialO_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s))
    (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letSpecialO Γ ann G r1s body) := by
  unfold letSpecialO
  split
  · exact ite_framed (letCheckO_framed _ _ _ _ hb) (ret_framed _)
  · exact ret_framed _

theorem letGenO_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letGenO Γ ann r1s body) := by
  unfold letGenO
  cases ann with
  | some A => exact letCheckO_framed _ _ _ _ hb
  | none =>
    exact bind_framed (flatMapR_framed (fun _ => bind_framed (hb _ _) fun _ =>
      bind_framed (flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _)) _)
        fun _ => ret_framed _) _) fun _ => ret_framed _

theorem letO_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s))
    {bound : Fu (Out Γ)}
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hbound : Framed bound) (hb : ∀ r1 o, Framed (body r1 o)) :
    Framed (letO Γ ann G bound body) :=
  bind_framed hbound fun _ => ite_framed (ret_framed _)
    (orElseO_framed (letSpecialO_framed _ _ _ _ hb)
      (thenL_framed (letGenO_framed _ _ _ hb) fun _ => finishF_framed _ _ _))

theorem argLetF_framed {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (g : BVar s .var)
    (b : ATm (s,x)) {arg : Ty s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ F, Framed (arg F)) (hgen : Framed (gen ())) : Framed (argLetF Γ G g b arg gen) := by
  refine bind_framed (argGoalF_framed _ _) fun oF => ?_
  cases oF with
  | none => exact hgen
  | some F =>
    refine orElseW_framed (bind_framed (harg _) fun r => ?_) hgen
    dsimp only
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _

theorem letF_framed {s : Sig} (Γ : Ctx s) (tag : LetTag) (ann : Option (Ty s)) (u : PTm (s,x))
    (G : Option (Ty s)) {arg : Ty s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ F, Framed (arg F)) (hgen : Framed (gen ())) :
    Framed (letF Γ tag ann u G arg gen) := by
  unfold letF
  split
  · exact argLetF_framed _ _ _ _ harg hgen
  · exact hgen

theorem ascO_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (G : Option (Ty s)) {r : Fu (Out Γ)}
    (hr : Framed r) : Framed (ascO Γ T G r) :=
  thenL_framed hr fun _ => finishF_framed _ _ _

theorem objSelfF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (U0 : Option (CaptureSet s))
    (G : Option (Ty s)) {defs : Fu (Option (ADefs (s,x)) × List EReason)} (hd : Framed defs) :
    Framed (objSelfF Γ S U0 G defs) := by
  refine bind_framed hd fun r => ?_
  dsimp only
  split
  · exact fullInfer_framed _ _ _
  · exact ret_framed _

/-! ## The frame lemmas of the rounds

The rounds keep a marked tank, never add fuel, and do the same with more fuel,
when every job's elaboration does. -/

theorem belowAllF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) : ∀ Us, Framed (belowAllF Γ T Us)
  | [] => ret_framed _
  | U :: Us => by
    unfold belowAllF
    split
    · exact belowAllF_framed Γ T Us
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact belowAllF_framed Γ T Us
      | none => exact ret_framed _

theorem leastFromF_framed {s : Sig} (Γ : Ctx s) (Ts : List (Ty s)) :
    ∀ cs : List (Elab Γ), Framed (leastFromF Γ Ts cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed Γ c.ty Ts) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromF_framed Γ Ts rest

theorem leastCandF_framed {s : Sig} (Γ : Ctx s) (cs : List (Elab Γ)) :
    Framed (leastCandF Γ cs) :=
  leastFromF_framed Γ _ cs

theorem runJobF_framed {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (P : Shape (s,x))
    {j : Job (s,x)} (hj : ∀ Γ', Framed (j.run Γ')) : Framed (runJobF Γ U0 P j) := by
  refine bind_framed (hj _) fun r => ?_
  split
  · exact ret_framed _
  · refine bind_framed (leastCandF_framed _ _) fun o => ?_
    cases o with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

theorem roundF_framed {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (P : Shape (s,x)) :
    ∀ (js : List (Job (s,x))), (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundF Γ U0 P js)
  | [], _ => ret_framed _
  | j :: js, hj => by
    refine bind_framed (runJobF_framed Γ U0 P (hj j (List.mem_cons_self ..))) fun r => ?_
    cases r with
    | ok e =>
      refine bind_framed (roundF_framed Γ U0 P js fun j' h' => hj j' (List.mem_cons_of_mem _ h'))
        fun r' => ?_
      cases r' with
      | ok _ => exact ret_framed _
      | error _ => exact ret_framed _
    | error _ => exact ret_framed _

/-- The rounds are framed when every job's elaboration is. -/
theorem roundsF_framed {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s))
    (probe : List (Label × Ty (s,x)) → Shape (s,x)) :
    ∀ (n : Nat) (js : List (Job (s,x))) (known : List (Done (s,x))),
      (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundsF Γ U0 probe n js known)
  | _, [], _, _ => by
    unfold roundsF
    exact ret_framed _
  | 0, j :: js, _, _ => by
    unfold roundsF
    exact ret_framed _
  | n + 1, j :: js, known, hj => by
    unfold roundsF
    split
    · exact ret_framed _
    · refine bind_framed (roundF_framed Γ U0 _ _ fun j' h' => hj j' (List.mem_filter.mp h').1)
        fun r => ?_
      cases r with
      | ok new =>
        exact roundsF_framed Γ U0 probe n _ _ fun j' h' => hj j' (List.mem_filter.mp h').1
      | error _ => exact ret_framed _

theorem formSelfF_framed {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (d : PDefs (s,x))
    {js : List (Job (s,x))} (hj : ∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) :
    Framed (formSelfF Γ U0 d js) := by
  refine bind_framed (roundsF_framed Γ U0 _ _ js [] hj) fun r => ?_
  cases r with
  | ok _ => exact ret_framed _
  | error _ => exact ret_framed _

theorem objNoneF_framed {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (G : Option (Ty s))
    {form : Fu (Except (List EReason) (Shape (s,x) × List (Done (s,x))))}
    {fill : Shape (s,x) → List (Done (s,x)) → Fu (Option (ADefs (s,x)) × List EReason)}
    (hf : Framed form) (hl : ∀ S done, Framed (fill S done)) :
    Framed (objNoneF Γ U0 G form fill) := by
  refine bind_framed hf fun r => ?_
  cases r with
  | ok p =>
    obtain ⟨S, done⟩ := p
    exact objSelfF_framed _ _ _ _ (hl S done)
  | error _ => exact ret_framed _

/-! ## The frame lemmas of the elaborator -/

mutual

theorem elabF_framed {s : Sig} (Γ : Ctx s) : (p : PTm s) → (G : Option (Ty s)) →
    Framed (elabF Γ p G)
  | .path q, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  | .app x y, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  | .proj x a, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  | .box x, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  | .unbox C x, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ret_framed _
  | .lam (some T) t, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact lamSomeF_framed _ _ _ fun o => elabF_framed _ t o
  | .lam none t, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact lamNoneF_framed _ _ _ fun T1 o => elabF_framed _ t o
  | .obj (some S) U0 d, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact objSelfF_framed _ _ _ _ (elabDefsF_framed _ d S)
  | .obj none U0 d, G => by
    rw [elabF.eq_def]
    split
    · exact fullInfer_framed _ _ _
    · dsimp only
      have hn : ∀ G', Framed (objNoneF Γ U0 G' (formSelfF Γ U0 d (jobsF d))
          fun S' done => fillDefsF (probeCtx Γ S' U0) done d S') := fun G' =>
        objNoneF_framed _ _ _ (formSelfF_framed _ _ d (jobsF_framed d))
          fun S' done => fillDefsF_framed _ done d S'
      cases G with
      | none => exact hn none
      | some T =>
        refine bind_framed (selfGoalF_framed _ _) fun oS => ?_
        cases oS with
        | some S => exact orElseW_framed (objSelfF_framed _ _ _ _ (elabDefsF_framed _ d S)) (hn _)
        | none => exact hn _
  | .let tag ann t u, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact letF_framed _ _ _ _ _ (fun F => elabF_framed _ t _)
        (letO_framed _ _ _ (elabF_framed _ t _) fun r1 o => elabF_framed _ u o)
  | .asc t T, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _
    · exact ascO_framed _ _ _ (elabF_framed _ t _)

theorem elabDefsF_framed {s : Sig} (Γ : Ctx s) : (d : PDefs s) → (S : Shape s) →
    Framed (elabDefsF Γ d S)
  | .typ A S0, S => by
    rw [elabDefsF]
    exact ret_framed _
  | .cap C c, S => by
    rw [elabDefsF]
    exact ret_framed _
  | .trm a o t, S => by
    cases S with
    | fld c T =>
      rw [elabDefsF]
      refine ite_framed ?_ (ret_framed _)
      split
      · exact ret_framed _
      · exact bind_framed (elabF_framed _ t _) fun _ => ret_framed _
    | _ => simp only [elabDefsF]; exact ret_framed _
  | .and d1 d2, S => by
    cases S with
    | and S1 S2 =>
      rw [elabDefsF]
      refine bind_framed (elabDefsF_framed _ d1 S1) fun r1 => ?_
      split
      · exact bind_framed (elabDefsF_framed _ d2 S2) fun _ => ret_framed _
      · exact ret_framed _
    | _ => simp only [elabDefsF]; exact ret_framed _

/-- The jobs of a definition list run framed elaborations. -/
theorem jobsF_framed {s : Sig} : (d : PDefs s) → ∀ j ∈ jobsF d, ∀ Γ, Framed (j.run Γ)
  | .typ _ _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .cap _ _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm _ (some _) _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm a none t => by
    intro j hj Γ
    simp only [jobsF, List.mem_singleton] at hj
    subst hj
    exact elabF_framed Γ t none
  | .and d1 d2 => by
    intro j hj Γ
    simp only [jobsF, List.mem_append] at hj
    rcases hj with h | h
    · exact jobsF_framed d1 j h Γ
    · exact jobsF_framed d2 j h Γ

theorem fillDefsF_framed {s : Sig} (Γ : Ctx s) (done : List (Done s)) :
    (d : PDefs s) → (S : Shape s) → Framed (fillDefsF Γ done d S)
  | .typ A S0, S => by
    rw [fillDefsF]
    exact ret_framed _
  | .cap C c, S => by
    rw [fillDefsF]
    exact ret_framed _
  | .trm a none t, S => by
    rw [fillDefsF]
    split
    · exact ret_framed _
    · exact ret_framed _
  | .trm a (some T) t, S => by
    cases S with
    | fld c W =>
      rw [fillDefsF]
      refine ite_framed ?_ (ret_framed _)
      split
      · exact ret_framed _
      · exact bind_framed (elabF_framed _ t _) fun _ => ret_framed _
    | _ => simp only [fillDefsF]; exact ret_framed _
  | .and d1 d2, S => by
    cases S with
    | and S1 S2 =>
      rw [fillDefsF]
      refine bind_framed (fillDefsF_framed Γ done d1 S1) fun r1 => ?_
      split
      · exact bind_framed (fillDefsF_framed Γ done d2 S2) fun _ => ret_framed _
      · exact ret_framed _
    | _ => simp only [fillDefsF]; exact ret_framed _

end

/-! ## Completeness of a filled domain -/

/-- An elaboration agrees with a computation of the typer when, from every
tank, it gives the same answer and leaves the same tank.  Only the reasons
are new. -/
def Agrees {α ρ : Type} (a' : Fu (α × List ρ)) (a : Fu α) : Prop :=
  ∀ t, (a' t).1.1 = (a t).1 ∧ (a' t).2 = (a t).2

theorem withR_agrees {α : Type} (c : Fu (List α)) : Agrees (withR c) c := by
  intro t
  exact ⟨rfl, rfl⟩

theorem fullInfer_agrees {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Option (Ty s)) :
    Agrees (fullInfer Γ a G) (inferF Γ a G) :=
  withR_agrees _

theorem thenL_agrees {s s' : Sig} {Γ : Ctx s} {Δ : Ctx s'} {a1 : Fu (Out Δ)}
    {a : Fu (List (Elab Δ))} (ha : Agrees a1 a) (f : List (Elab Δ) → Fu (List (Elab Γ))) :
    Agrees (thenL a1 f) (Fu.bind a f) := by
  intro t
  obtain ⟨h1, h2⟩ := ha t
  simp only [thenL, Fu.bind]
  generalize a1 t = r1 at h1 h2 ⊢
  generalize a t = r at h1 h2 ⊢
  obtain ⟨⟨l, rs⟩, t1⟩ := r1
  obtain ⟨l2, t2⟩ := r
  simp only at h1 h2
  subst h1
  subst h2
  exact ⟨rfl, rfl⟩

/-- A lambda without a domain whose body has no empty slot, checked against a
function type: the elaborator is the typer on the lambda with the goal's
domain written, candidates and tank. -/
theorem lam_direct_eq {s : Sig} (Γ : Ctx s) (a : ATm (s,x)) (C : CaptureSet s) (T1 : Ty s)
    (T2 : Ty (s,x)) :
    elabF Γ (.lam none a.toI) (some ((Shape.all T1 T2) ^ C)) =
      fullInfer Γ (.lam T1 a) (some ((Shape.all T1 T2) ^ C)) := by
  rw [elabF_lam_none]
  funext t
  simp only [lamNoneF, funPartOf, Fu.bind, Fu.ret, ATm.full?_toI]

theorem lam_direct_full {s : Sig} (Γ : Ctx s) (a : ATm (s,x)) (C : CaptureSet s) (T1 : Ty s)
    (T2 : Ty (s,x)) :
    Agrees (elabF Γ (.lam none a.toI) (some ((Shape.all T1 T2) ^ C)))
      (inferF Γ (.lam T1 a) (some ((Shape.all T1 T2) ^ C))) := by
  rw [lam_direct_eq]
  exact fullInfer_agrees _ _ _

/-- A lambda without a domain whose body has no empty slot, at a goal whose
function part is reached through an intersection, an alias or a box: the
elaborator is the typer on the lambda with the domain written, from the tank
the function part left. -/
theorem lam_side_full {s : Sig} {Γ : Ctx s} (a : ATm (s,x)) {G : Option (Ty s)} {tk tk' : Tank}
    {T1 : Ty s} {V : Ty (s,x)} (hf : funPartOf Γ G tk = (.side T1 V, tk')) :
    elabF Γ (.lam none a.toI) G tk = fullInfer Γ (.lam T1 a) G tk' := by
  rw [elabF_lam_none]
  simp only [lamNoneF, Fu.bind, hf, ATm.full?_toI]

/-- The same, as an agreement with the typer: the same candidates and the
same tank. -/
theorem lam_side_agrees {s : Sig} {Γ : Ctx s} (a : ATm (s,x)) {G : Option (Ty s)} {tk tk' : Tank}
    {T1 : Ty s} {V : Ty (s,x)} (hf : funPartOf Γ G tk = (.side T1 V, tk')) :
    (elabF Γ (.lam none a.toI) G tk).1.1 = (inferF Γ (.lam T1 a) G tk').1 ∧
      (elabF Γ (.lam none a.toI) G tk).2 = (inferF Γ (.lam T1 a) G tk').2 := by
  rw [lam_side_full a hf]
  exact fullInfer_agrees _ _ _ tk'

/-- An ascription whose term has an empty slot: the term checked against the
ascribed type, as the typer's clause. -/
theorem elabF_asc {s : Sig} (Γ : Ctx s) {t : PTm s} (ht : t.full? = none) (T : Ty s)
    (G : Option (Ty s)) : elabF Γ (.asc t T) G = ascO Γ T G (elabF Γ t (some T)) := by
  rw [elabF]
  simp only [PTm.full?, ht, Option.map_none]

/-- A lambda without a domain whose body has no empty slot, ascribed a
function type: the elaborator is the typer on the ascription of the lambda
with the domain written, candidates and tank. -/
theorem asc_direct_full {s : Sig} (Γ : Ctx s) (a : ATm (s,x)) (C : CaptureSet s) (T1 : Ty s)
    (T2 : Ty (s,x)) (G : Option (Ty s)) :
    Agrees (elabF Γ (.asc (.lam none a.toI) ((Shape.all T1 T2) ^ C)) G)
      (inferF Γ (.asc (.lam T1 a) ((Shape.all T1 T2) ^ C)) G) := by
  rw [elabF_asc _ rfl, lam_direct_eq, inferF]
  exact thenL_agrees (fullInfer_agrees _ _ _) _

theorem firstSomeR_agrees {α β ρ : Type} {f : α → Fu (Option β × List ρ)}
    {g : α → Fu (Option β)} (hf : ∀ x, Agrees (f x) (g x)) :
    ∀ l, Agrees (firstSomeR f l) (Fu.firstSome g l)
  | [] => fun _ => ⟨rfl, rfl⟩
  | x :: xs => by
    intro t
    rw [firstSomeR, Fu.firstSome]
    obtain ⟨h1, h2⟩ := hf x t
    simp only [orElseW, Fu.bind, Fu.orElse]
    generalize f x t = r1 at h1 h2 ⊢
    generalize g x t = r at h1 h2 ⊢
    obtain ⟨⟨o, rs⟩, t1⟩ := r1
    obtain ⟨o', t1'⟩ := r
    simp only at h1 h2
    subst h1
    subst h2
    cases o with
    | some b => simp [stopOr]
    | none =>
      cases hout : t1.out with
      | true => simp [stopOr, hout]
      | false =>
        simp only [stopOr, Option.isSome_none, hout, Bool.false_or, Bool.false_eq_true, if_false,
          Fu.bind, Fu.ret]
        obtain ⟨h3, h4⟩ := firstSomeR_agrees hf xs t1
        generalize firstSomeR f xs t1 = r2 at h3 h4 ⊢
        generalize Fu.firstSome g xs t1 = r2' at h3 h4 ⊢
        obtain ⟨⟨o2, rs2⟩, t2⟩ := r2
        obtain ⟨o2', t2'⟩ := r2'
        simp only at h3 h4 ⊢
        exact ⟨h3, h4⟩

theorem bind_agrees {α β ρ ρ' : Type} {a' : Fu (α × List ρ)} {a : Fu α}
    {f' : α × List ρ → Fu (β × List ρ')} {f : α → Fu β} (ha : Agrees a' a)
    (hf : ∀ x rs, Agrees (f' (x, rs)) (f x)) : Agrees (Fu.bind a' f') (Fu.bind a f) := by
  intro t
  obtain ⟨h1, h2⟩ := ha t
  simp only [Fu.bind]
  generalize a' t = r1 at h1 h2 ⊢
  generalize a t = r at h1 h2 ⊢
  obtain ⟨⟨x, rs⟩, t1⟩ := r1
  obtain ⟨x', t1'⟩ := r
  simp only at h1 h2
  subst h1
  subst h2
  exact hf x rs t1

theorem ret_agrees {α ρ : Type} (x : α) (rs : List ρ) : Agrees (Fu.ret (x, rs)) (Fu.ret x) := by
  intro t
  exact ⟨rfl, rfl⟩

theorem bind_ret_agrees {α ρ : Type} (c : Fu α) (g : α → List ρ) :
    Agrees (Fu.bind c fun o => Fu.ret (o, g o)) c := by
  intro t
  unfold Fu.bind Fu.ret
  generalize c t = r
  obtain ⟨o, t1⟩ := r
  exact ⟨rfl, rfl⟩

/-- The `let` clause at a written type, with the body of the elaborator and
the body of the typer agreeing at that type, agrees with the typer's. -/
theorem letCheckO_agrees {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s)
    (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    {body' : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : ∀ r1, Agrees (body r1 (some A.weaken)) (body' r1 (some A.weaken))) :
    Agrees (letCheckO Γ ann A r1s body) (mapL (letCheckF Γ ann A r1s body') id) := by
  unfold letCheckO mapL letCheckF
  refine bind_agrees (firstSomeR_agrees (fun r1 => bind_agrees (hb r1) fun l rs => ?_) r1s)
    fun o rs => ?_
  · dsimp only
    cases firstChecked l A.weaken with
    | some c => exact bind_ret_agrees _ _
    | none => exact ret_agrees _ _
  · cases o with
    | some _ => exact ret_agrees _ _
    | none => exact ret_agrees _ _

/-- A `let` with a written function type whose body is a lambda without a
domain with no empty slot: the elaborator is the typer on the program with the
domain written, candidates and tank.  The written type is the goal of the
body, so the body's lambda takes its domain from it. -/
theorem letAnn_direct_full {s : Sig} (Γ : Ctx s) (tag : LetTag) (t : ATm s) (a : ATm (s,x,x))
    (C : CaptureSet s) (T1 : Ty s) (T2 : Ty (s,x)) (G : Option (Ty s)) :
    Agrees (elabF Γ (.let tag (some ((Shape.all T1 T2) ^ C)) t.toI (.lam none a.toI)) G)
      (inferF Γ (.let (some ((Shape.all T1 T2) ^ C)) t (.lam T1.weaken a)) G) := by
  have he : elabF Γ (.let tag (some ((Shape.all T1 T2) ^ C)) t.toI (.lam none a.toI)) G =
      letO Γ (some ((Shape.all T1 T2) ^ C)) G (fullInfer Γ t none)
        (fun r1 o => elabF (Γ.cons r1.ty) (.lam none a.toI) o) := by
    rw [elabF]
    simp only [PTm.full?, ATm.full?_toI]
    cases tag <;> simp only [letF, argCallee?, elabF_toI]
  have hw : ((Shape.all T1 T2) ^ C).weaken (k := .var) =
      (Shape.all T1.weaken (T2.rename Rename.succ.lift)) ^ (CaptureSet.weaken C) := rfl
  rw [he, inferF]
  intro tk
  simp only [letO, fullInfer, withR, Fu.bind, Fu.ret]
  generalize inferF Γ t none tk = r at ⊢
  obtain ⟨r1s, t1⟩ := r
  cases r1s with
  | nil =>
    cases G <;> simp [orElseL, letSpecialF, letGenF, mapL, letCheckF, Fu.firstSome, finishF,
      Fu.flatMapL, Fu.bind, Fu.ret, listO]
  | cons r r1s' =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
    have hc := thenL_agrees (letCheckO_agrees Γ (some ((Shape.all T1 T2) ^ C))
      ((Shape.all T1 T2) ^ C) (r :: r1s')
      (body := fun r1 o => elabF (Γ.cons r1.ty) (.lam none a.toI) o)
      (body' := fun r1 o => inferF (Γ.cons r1.ty) (.lam T1.weaken a) o)
      (fun r1 => by
        dsimp only
        rw [hw]
        exact lam_direct_full _ a _ _ _)) (finishF Γ G) t1
    simp only [orElseO, orElseL, letSpecialO, letSpecialF, letGenO, letGenF, Fu.bind, Fu.ret]
    generalize thenL (letCheckO Γ (some ((Shape.all T1 T2) ^ C)) ((Shape.all T1 T2) ^ C)
      (r :: r1s') fun r1 o => elabF (Γ.cons r1.ty) (.lam none a.toI) o) (finishF Γ G) t1 = q at hc
    simpa only [Fu.bind] using hc

/-! ## Self shapes formed from definitions -/

/-- The self shape formed from the definitions is in lockstep with them. -/
theorem fullSelf_lockstep {s : Sig} {known : List (Label × Ty s)} :
    ∀ {d : PDefs s} {S : Shape s}, d.fullSelf known = some S → Lockstep known d S
  | .typ A S, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .typ A S
  | .cap C c, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .cap C c
  | .trm a (some T) t, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .written a T t
  | .trm a none t, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    exact .inferred a T t hT
  | .and d e, _, h => by
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf known with
    | none => simp only [h1, reduceCtorEq] at h
    | some S1 =>
      cases h2 : e.fullSelf known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some S2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact .and (fullSelf_lockstep h1) (fullSelf_lockstep h2)

/-- A definition list whose fields all have a written type has no job, so a
literal with a written type on every field needs no round. -/
theorem jobsF_written {s : Sig} : ∀ {d : PDefs s}, d.AllFieldsWritten → jobsF d = []
  | .typ _ _, _ => by simp only [jobsF]
  | .cap _ _, _ => by simp only [jobsF]
  | .trm _ (some _) _, _ => by simp only [jobsF]
  | .trm _ none _, hw => by simp [PDefs.AllFieldsWritten] at hw
  | .and d e, hw => by
    simp only [PDefs.AllFieldsWritten] at hw
    simp only [jobsF, jobsF_written hw.1, jobsF_written hw.2, List.append_nil]

/-! ## The least candidate is least -/

theorem belowAllF_sub {s : Sig} {Γ : Ctx s} {T : Ty s} :
    ∀ {Us : List (Ty s)} {t t' : Tank}, belowAllF Γ T Us t = (true, t') →
      ∀ U ∈ Us, Nonempty (Sub Γ T U)
  | [], _, _, _, U, hU => absurd hU List.not_mem_nil
  | U' :: Us, t, t', h, U, hU => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hU with rfl | hm
      · exact ⟨heq ▸ Sub.refl _⟩
      · exact belowAllF_sub h U hm
    · cases hs : subF Γ T U' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some e =>
          rcases List.mem_cons.mp hU with rfl | hm
          · exact ⟨e⟩
          · exact belowAllF_sub h U hm
        | none => simp [Fu.ret] at h

theorem leastFromF_sub {s : Sig} {Γ : Ctx s} {Ts : List (Ty s)} :
    ∀ {cs : List (Elab Γ)} {t : Tank} {c : Elab Γ} {t' : Tank},
      leastFromF Γ Ts cs t = (some c, t') → c ∈ cs ∧ ∀ T ∈ Ts, Nonempty (Sub Γ c.ty T)
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
theorem leastCand_least {s : Sig} {Γ : Ctx s} {cs : List (Elab Γ)} {tk : Tank}
    {c : Elab Γ} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) :
    c ∈ cs ∧ ∀ c' ∈ cs, Nonempty (Sub Γ c.ty c'.ty) := by
  obtain ⟨hm, hs⟩ := leastFromF_sub h
  exact ⟨hm, fun c' hc' => hs c'.ty (List.mem_map_of_mem hc')⟩

theorem belowAllF_sub? {s : Sig} {Γ : Ctx s} {T : Ty s} :
    ∀ {Us : List (Ty s)} {t t' : Tank}, belowAllF Γ T Us t = (true, t') → t'.out = false →
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

theorem leastFromF_sub? {s : Sig} {Γ : Ctx s} {Ts : List (Ty s)} :
    ∀ {cs : List (Elab Γ)} {t : Tank} {c : Elab Γ} {t' : Tank},
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

/-- The same with the typer's subtyping from a full tank: on a tank that ends
unmarked, the type of the least candidate is the type of every other candidate
or below it at some fuel. -/
theorem leastCand_sub? {s : Sig} {Γ : Ctx s} {cs : List (Elab Γ)} {tk : Tank}
    {c : Elab Γ} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) (ho : tk'.out = false) :
    ∀ c' ∈ cs, c'.ty = c.ty ∨ ∃ n, (sub? Γ c.ty c'.ty n).1.isSome = true :=
  fun c' hc' => leastFromF_sub? h ho c'.ty (List.mem_map_of_mem hc')

/-! ## The cyclic reference is on a cycle -/

theorem walkL_snoc {s : Sig} {js : List (Job (s,x))} {l l' : Label} (hn : nextL js l = some l') :
    ∀ {k : Nat} {m : Label}, walkL js k m = some l → walkL js (k + 1) m = some l'
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

theorem nextL_mem {s : Sig} {js : List (Job (s,x))} {l l' : Label} (h : nextL js l = some l') :
    l' ∈ js.map (·.lbl) := by
  unfold nextL at h
  split at h
  · rename_i j _
    have hm : l' ∈ waitsFor js j := List.mem_of_mem_head? h
    simp only [waitsFor, List.mem_filter] at hm
    exact List.contains_iff_mem.mp hm.2
  · cases h

theorem cycleFrom_onCycle {s : Sig} {js : List (Job (s,x))} :
    ∀ {n : Nat} {seen : List Label} {l r : Label},
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
theorem cycleAt_onCycle {s : Sig} {js : List (Job (s,x))} {n : Nat} {l : Label}
    (h : cycleAt js n = some l) : ∃ j ∈ js, j.lbl = l ∧ OnCycle js j := by
  unfold cycleAt at h
  split at h
  · cases h
  · rename_i j js'
    exact cycleFrom_onCycle (by simp) (List.mem_map_of_mem (List.mem_cons_self ..)) h

/-! ## No `any` in an elaborated term

The resolver writes no `any` (`resolve_noAny`).  The typer and the
elaborator write none either: every annotation, set and type they produce
comes from the program, from the goal, or from a type of the context, through
renaming, lookup, avoidance and joins of sets, none of which introduces
`any`. -/

section NoAnyBasics

theorem CaptureSet.noAny_rename_eq {s1 s2 : Sig} (C : CaptureSet s1) (ρ : Rename s1 s2) :
    CaptureSet.noAny (C.rename ρ) = CaptureSet.noAny C := by
  induction C with
  | nil => rfl
  | cons a C ih =>
    cases a <;> simp only [CaptureSet.rename, List.map_cons, CapAtom.rename,
      CaptureSet.noAny] at ih ⊢ <;> exact ih

mutual

theorem Shape.noAny_rename_eq : ∀ {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2),
    (S.rename ρ).noAny = S.noAny
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .sel _ _, _ => rfl
  | _, _, .typ _ S T, ρ => by
    simp only [Shape.rename, Shape.noAny, Shape.noAny_rename_eq S ρ, Shape.noAny_rename_eq T ρ]
  | _, _, .fld _ T, ρ => by
    simp only [Shape.rename, Shape.noAny, Ty.noAny_rename_eq T ρ]
  | _, _, .cap _ c1 c2, ρ => by
    simp only [Shape.rename, Shape.noAny, CaptureSet.noAny_rename_eq]
  | _, _, .mu S, ρ => by
    simp only [Shape.rename, Shape.noAny, Shape.noAny_rename_eq S ρ.lift]
  | _, _, .all T1 T2, ρ => by
    simp only [Shape.rename, Shape.noAny, Ty.noAny_rename_eq T1 ρ, Ty.noAny_rename_eq T2 ρ.lift]
  | _, _, .and S T, ρ => by
    simp only [Shape.rename, Shape.noAny, Shape.noAny_rename_eq S ρ, Shape.noAny_rename_eq T ρ]
  | _, _, .box T, ρ => by
    simp only [Shape.rename, Shape.noAny, Ty.noAny_rename_eq T ρ]

theorem Ty.noAny_rename_eq : ∀ {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2),
    (T.rename ρ).noAny = T.noAny
  | _, _, .capt C S, ρ => by
    simp only [Ty.rename, Ty.noAny, CaptureSet.noAny_rename_eq, Shape.noAny_rename_eq S ρ]

end

theorem Ty.noAny_weaken_eq {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).noAny = T.noAny :=
  Ty.noAny_rename_eq T _

theorem Shape.noAny_substVar_eq {s : Sig} {k : Kind} (S : Shape (s,,k)) (y : BVar s k) :
    (S.substVar y).noAny = S.noAny :=
  Shape.noAny_rename_eq S _

theorem Ty.noAny_substVar_eq {s : Sig} {k : Kind} (T : Ty (s,,k)) (y : BVar s k) :
    (T.substVar y).noAny = T.noAny :=
  Ty.noAny_rename_eq T _

theorem CaptureSet.noAny_weaken_eq {s : Sig} {k : Kind} (C : CaptureSet s) :
    CaptureSet.noAny (CaptureSet.weaken C (k := k)) = CaptureSet.noAny C :=
  CaptureSet.noAny_rename_eq C _

theorem CaptureSet.noAny_iff {s : Sig} (C : CaptureSet s) :
    CaptureSet.noAny C = true ↔ ∀ a ∈ C, a ≠ .any := by
  induction C with
  | nil => simp [CaptureSet.noAny]
  | cons a C ih =>
    cases a <;> simp [CaptureSet.noAny, ih]

theorem CaptureSet.noAny_of_subset {s : Sig} {C D : CaptureSet s} (h : ∀ a ∈ C, a ∈ D)
    (hD : CaptureSet.noAny D = true) : CaptureSet.noAny C = true :=
  (CaptureSet.noAny_iff C).mpr fun a ha => (CaptureSet.noAny_iff D).mp hD a (h a ha)

theorem CaptureSet.noAny_append' {s : Sig} {C D : CaptureSet s} (hC : CaptureSet.noAny C = true)
    (hD : CaptureSet.noAny D = true) : CaptureSet.noAny (C ++ D) = true := by
  rw [CaptureSet.noAny_iff] at *
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hC a h
  · exact hD a h

theorem capJoin_noAny {s : Sig} {C D : CaptureSet s} (hC : CaptureSet.noAny C = true)
    (hD : CaptureSet.noAny D = true) : CaptureSet.noAny (capJoin C D) = true :=
  CaptureSet.noAny_append' hC (CaptureSet.noAny_of_subset (fun _ h => (List.mem_filter.mp h).1) hD)

theorem Ty.noAny_capt_iff {s : Sig} (C : CaptureSet s) (S : Shape s) :
    (S ^ C).noAny = true ↔ CaptureSet.noAny C = true ∧ S.noAny = true := by
  simp [Ty.noAny]

/-- Every type a context declares holds no `any`. -/
def CtxNoAny {s : Sig} (Γ : Ctx s) : Prop := ∀ x : BVar s .var, (Γ.lookup x).noAny = true

theorem CtxNoAny.cons {s : Sig} {Γ : Ctx s} (h : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true) :
    CtxNoAny (Γ.cons T) := by
  intro y
  cases y with
  | here => simp only [Ctx.lookup, Ty.noAny_weaken_eq, hT]
  | there y => simp only [Ctx.lookup, Ty.noAny_weaken_eq, h y]

theorem CtxNoAny.consSelf {s : Sig} {Γ : Ctx s} (h : CtxNoAny Γ) (e : Defs (s,x)) {S : Shape (s,x)}
    {U : CaptureSet s} (hS : S.noAny = true) (hU : CaptureSet.noAny U = true) :
    CtxNoAny (Γ.consSelf e S U) := by
  intro y
  cases y with
  | here => simp only [Ctx.lookup, Ty.noAny_weaken_eq, Ty.noAny, Shape.noAny, hS, hU, Bool.and_self]
  | there y => simp only [Ctx.lookup, Ty.noAny_weaken_eq, h y]

theorem CtxNoAny.consC {s : Sig} {Γ : Ctx s} (h : CtxNoAny Γ) : CtxNoAny (Γ.consC) := by
  intro y
  cases y with
  | there y => simp only [Ctx.lookup, Ty.noAny_weaken_eq, h y]

theorem CtxNoAny.platform {s : Sig} : ∀ (P : Platform s), CtxNoAny (platformCtx P)
  | .nil => fun y => nomatch y
  | .cons P => by
    rw [platformCtx]
    exact (CtxNoAny.platform P).consC

theorem CtxNoAny.shape {s : Sig} {Γ : Ctx s} (h : CtxNoAny Γ) (y : BVar s .var) :
    (Γ.lookup y).shape.noAny = true := by
  have := h y
  revert this
  cases Γ.lookup y with
  | capt C S =>
    simp only [Ty.noAny, Ty.shape, Bool.and_eq_true]
    exact fun h => h.2

theorem CtxNoAny.captureSet {s : Sig} {Γ : Ctx s} (h : CtxNoAny Γ) (y : BVar s .var) :
    CaptureSet.noAny (Γ.lookup y).captureSet = true := by
  have := h y
  revert this
  cases Γ.lookup y with
  | capt C S =>
    simp only [Ty.noAny, Ty.captureSet, Bool.and_eq_true]
    exact fun h => h.1

end NoAnyBasics

/-! ### Answers that always have a property -/

section Always

variable {α β : Type}

/-- Every answer of `c`, from every tank, has `P`. -/
def Always (P : α → Prop) (c : Fu α) : Prop := ∀ t, P (c t).1

/-- Every element of the list has `P`. -/
def AllL (P : α → Prop) (l : List α) : Prop := ∀ a ∈ l, P a

/-- An answer, if there is one, has `P`. -/
def OptP (P : α → Prop) (o : Option α) : Prop := ∀ a, o = some a → P a

theorem always_ret {P : α → Prop} {a : α} (h : P a) : Always P (Fu.ret a) := fun _ => h

theorem always_true (c : Fu α) : Always (fun _ => True) c := fun _ => trivial

theorem always_bind {Q : α → Prop} {P : β → Prop} {c : Fu α} {f : α → Fu β}
    (hc : Always Q c) (hf : ∀ a, Q a → Always P (f a)) : Always P (Fu.bind c f) := by
  intro t
  simp only [Fu.bind]
  cases hct : c t with
  | mk a t1 =>
    have := hc t
    rw [hct] at this
    exact hf a this t1

theorem allL_nil (P : α → Prop) : AllL P [] := fun _ h => nomatch h

theorem allL_append {P : α → Prop} {l1 l2 : List α} (h1 : AllL P l1) (h2 : AllL P l2) :
    AllL P (l1 ++ l2) := fun a ha => (List.mem_append.mp ha).elim (h1 a) (h2 a)

theorem allL_map {P : β → Prop} {f : α → β} {l : List α} (h : ∀ a ∈ l, P (f a)) :
    AllL P (l.map f) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact h a ha

theorem allL_filter {P : α → Prop} {l : List α} (p : α → Bool) (h : AllL P l) :
    AllL P (l.filter p) := fun a ha => h a (List.mem_filter.mp ha).1

theorem allL_filterMap {P : β → Prop} {f : α → Option β} {l : List α}
    (h : ∀ a ∈ l, OptP P (f a)) : AllL P (l.filterMap f) := by
  intro b hb
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hb
  exact h a ha b hfa

theorem allL_listO {P : α → Prop} {o : Option α} (h : OptP P o) : AllL P (listO o) := by
  cases o with
  | none => exact allL_nil P
  | some a =>
    intro b hb
    simp only [listO, List.mem_singleton] at hb
    subst hb
    exact h _ rfl

theorem optP_none (P : α → Prop) : OptP P none := fun _ h => nomatch h

theorem optP_true (o : Option α) : OptP (fun _ => True) o := fun _ _ => trivial

theorem optP_some {P : α → Prop} {a : α} (h : P a) : OptP P (some a) := by
  intro b hb
  cases hb
  exact h

theorem optP_map {P : β → Prop} {Q : α → Prop} {f : α → β} {o : Option α} (h : OptP Q o)
    (hf : ∀ a, Q a → P (f a)) : OptP P (o.map f) := by
  cases o with
  | none => exact optP_none P
  | some a => exact optP_some (hf a (h a rfl))

theorem always_flatMapL {P : β → Prop} {f : α → Fu (List β)} :
    ∀ {l : List α}, (∀ a ∈ l, Always (AllL P) (f a)) → Always (AllL P) (Fu.flatMapL f l)
  | [], _ => always_ret (allL_nil P)
  | a :: l, h => by
    rw [Fu.flatMapL]
    exact always_bind (h a (List.mem_cons_self ..)) fun _ h1 =>
      always_bind (always_flatMapL fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ h2 =>
        always_ret (allL_append h1 h2)

theorem always_orElse {P : α → Prop} {a : Fu (Option α)} {b : Unit → Fu (Option α)}
    (ha : Always (OptP P) a) (hb : Always (OptP P) (b ())) : Always (OptP P) (Fu.orElse a b) := by
  intro t
  simp only [Fu.orElse]
  have h1 := ha t
  cases hat : a t with
  | mk o t1 =>
    rw [hat] at h1
    cases o with
    | some x => exact h1
    | none =>
      dsimp only
      split
      · exact optP_none P
      · exact hb t1

theorem always_firstSome {P : β → Prop} {f : α → Fu (Option β)} :
    ∀ {l : List α}, (∀ a ∈ l, Always (OptP P) (f a)) → Always (OptP P) (Fu.firstSome f l)
  | [], _ => always_ret (optP_none P)
  | a :: l, h => by
    rw [Fu.firstSome]
    exact always_orElse (h a (List.mem_cons_self ..))
      (always_firstSome fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem always_mapL {Q : α → Prop} {P : β → Prop} {c : Fu (Option α)} {f : α → β}
    (hc : Always (OptP Q) c) (hf : ∀ a, Q a → P (f a)) : Always (AllL P) (mapL c f) :=
  always_bind hc fun _ h => always_ret (allL_listO (optP_map h hf))

theorem always_mapO {Q : α → Prop} {P : β → Prop} {c : Fu (Option α)} {f : α → β}
    (hc : Always (OptP Q) c) (hf : ∀ a, Q a → P (f a)) : Always (OptP P) (mapO c f) :=
  always_bind hc fun _ h => always_ret (optP_map h hf)

theorem always_bindO {Q : α → Prop} {P : β → Prop} {c : Fu (Option α)} {f : α → Fu (Option β)}
    (hc : Always (OptP Q) c) (hf : ∀ a, Q a → Always (OptP P) (f a)) :
    Always (OptP P) (bindO c f) := by
  refine always_bind hc fun o h => ?_
  cases o with
  | some a => exact hf a (h a rfl)
  | none => exact always_ret (optP_none P)

theorem always_orElseL {P : α → Prop} {a b : Fu (List α)} (ha : Always (AllL P) a)
    (hb : Always (AllL P) b) : Always (AllL P) (orElseL a b) := by
  refine always_bind ha fun l h => ?_
  cases l with
  | nil => exact hb
  | cons _ _ => exact always_ret h

theorem always_ite {P : α → Prop} {p : Prop} [hp : Decidable p] {a b : Fu α} (ha : Always P a)
    (hb : Always P b) : Always P (if p then a else b) := by
  cases hp
  · exact hb
  · exact ha

theorem always_dite {P : α → Prop} {p : Prop} [hp : Decidable p] {a : p → Fu α} {b : ¬p → Fu α}
    (ha : ∀ h, Always P (a h)) (hb : ∀ h, Always P (b h)) :
    Always P (if h : p then a h else b h) := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

end Always

/-! ### The lookup -/

section LookNoAny

theorem Found.typ?_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} {A : Label}
    {e : Found Γ x V} {r : (lo : Shape s) × (hi : Shape s) × VarFn Γ x V (.typ A lo hi)}
    (h : e.typ? A = some r) (he : e.ty.noAny = true) : r.1.noAny = true ∧ r.2.1.noAny = true := by
  unfold Found.typ? at h
  split at h
  · rename_i B lo hi heq
    split at h
    · cases h
      rw [heq] at he
      simp only [Shape.noAny, Bool.and_eq_true] at he
      exact he
    · cases h
  · cases h

theorem Found.cap?_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} {A : Label}
    {e : Found Γ x V}
    {r : (c1 : CaptureSet s) × (c2 : CaptureSet s) × VarFn Γ x V (.cap A c1 c2)}
    (h : e.cap? A = some r) (he : e.ty.noAny = true) :
    CaptureSet.noAny r.1 = true ∧ CaptureSet.noAny r.2.1 = true := by
  unfold Found.cap? at h
  split at h
  · rename_i B c1 c2 heq
    split at h
    · cases h
      rw [heq] at he
      simp only [Shape.noAny, Bool.and_eq_true] at he
      exact he
    · cases h
  · cases h

/-- Every shape the lookup finds holds no `any`, when the shape it searches
and the context hold none. -/
theorem look_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    ∀ (d : Nat) (P : List (LKey s)) (x : BVar s .var) (V : Shape s) (k : Key),
      V.noAny = true → Always (AllL fun e : Found Γ x V => e.ty.noAny = true) (look Γ d P x V k)
  | 0, _, _, _, _, _ => fun _ => allL_nil _
  | d + 1, P, x, V, k, hV => by
    unfold look
    refine always_bind (always_true _) fun b _ => ?_
    cases b with
    | false => exact always_ret (allL_nil _)
    | true =>
      dsimp only
      split
      · exact always_ret (allL_nil _)
      split
      · intro t e he
        simp only [Fu.ret, List.mem_singleton] at he
        subst he
        exact hV
      split
      · rename_i B _ _
        refine always_dite (fun hB => ?_) (fun _ => always_ret (allL_nil _))
        have hB' : (B.substVar x).noAny = true := by
          rw [Shape.noAny_substVar_eq]
          simpa [Shape.noAny] using hV
        exact always_bind (look_noAny hΓ d _ x _ k hB') fun es hes =>
          always_ret (allL_map fun e he => hes e he)
      · rename_i V1 V2 _ _
        simp only [Shape.noAny, Bool.and_eq_true] at hV
        exact always_bind (look_noAny hΓ d _ x V1 k hV.1) fun es1 h1 =>
          always_bind (look_noAny hΓ d _ x V2 k hV.2) fun es2 h2 =>
            always_ret (allL_append (allL_map fun e he => h1 e he)
              (allL_map fun e he => h2 e he))
      · rename_i q B _ _
        refine always_bind (look_noAny hΓ d _ q _ _ (hΓ.shape q)) fun es hes => ?_
        refine always_flatMapL fun e he => ?_
        split
        · rename_i lo hi g heq
          have hhi := (Found.typ?_noAny heq (hes e he)).2
          exact always_bind (look_noAny hΓ d _ x hi k hhi) fun es2 h2 =>
            always_ret (allL_map fun e2 he2 => h2 e2 he2)
        · exact always_ret (allL_nil _)
      · exact always_ret (allL_nil _)

theorem decls_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (d : Nat) (p : BVar s .var)
    (A : Label) :
    Always (AllL fun m : TyMem Γ p A => m.1.noAny = true ∧ m.2.1.noAny = true) (decls Γ d p A) := by
  refine always_bind (look_noAny hΓ d [] p _ _ (hΓ.shape p)) fun es hes => ?_
  refine always_ret (allL_filterMap fun e he => ?_)
  intro m hm
  cases hr : e.typ? A with
  | none => rw [hr] at hm; cases hm
  | some r =>
    rw [hr] at hm
    cases hm
    exact Found.typ?_noAny hr (hes e he)

theorem capDecls_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (d : Nat) (p : BVar s .var)
    (A : Label) :
    Always (AllL fun m : CapMem Γ p A =>
      CaptureSet.noAny m.1 = true ∧ CaptureSet.noAny m.2.1 = true) (capDecls Γ d p A) := by
  refine always_bind (look_noAny hΓ d [] p _ _ (hΓ.shape p)) fun es hes => ?_
  refine always_ret (allL_filterMap fun e he => ?_)
  intro m hm
  cases hr : e.cap? A with
  | none => rw [hr] at hm; cases hm
  | some r =>
    rw [hr] at hm
    cases hm
    exact Found.cap?_noAny hr (hes e he)

theorem declsAt_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (p : BVar s .var) (A : Label) :
    Always (AllL fun m : TyMem Γ p A => m.1.noAny = true ∧ m.2.1.noAny = true) (declsAt Γ p A) :=
  fun t => decls_noAny hΓ t.left p A t

theorem capsAt_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (p : BVar s .var) (A : Label) :
    Always (AllL fun m : CapMem Γ p A =>
      CaptureSet.noAny m.1 = true ∧ CaptureSet.noAny m.2.1 = true) (capsAt Γ p A) :=
  fun t => capDecls_noAny hΓ t.left p A t

end LookNoAny

/-! ### Views, box inference and avoidance -/

section AdaptNoAny

/-- A typing holds no `any`: not in its term's annotations, its use set or
its type. -/
def Elab.NoAny {s : Sig} {Γ : Ctx s} (c : Elab Γ) : Prop :=
  c.tm.NoAnyAnn = true ∧ CaptureSet.noAny c.uses = true ∧ c.ty.noAny = true

/-- A typing at a given type holds no `any` in its term or its use set. -/
def Checked.NoAny {s : Sig} {Γ : Ctx s} {T : Ty s} (c : Checked Γ T) : Prop :=
  c.tm.NoAnyAnn = true ∧ CaptureSet.noAny c.uses = true

theorem Checked.toElab_noAny {s : Sig} {Γ : Ctx s} {T : Ty s} {c : Checked Γ T} (h : c.NoAny)
    (hT : T.noAny = true) : c.toElab.NoAny :=
  ⟨h.1, h.2, hT⟩

/-- A function view holds no `any`. -/
def FnView.NoAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} (f : FnView Γ x) : Prop :=
  CaptureSet.noAny f.uses = true ∧ CaptureSet.noAny f.cs = true ∧ f.dom.noAny = true ∧
    f.cod.noAny = true

/-- A field view holds no `any`. -/
def FldView.NoAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} (f : FldView Γ x a) :
    Prop :=
  CaptureSet.noAny f.uses = true ∧ CaptureSet.noAny f.cs = true ∧ f.ty.noAny = true

/-- A box view holds no `any`. -/
def BoxView.NoAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} (b : BoxView Γ x) : Prop :=
  CaptureSet.noAny b.uses = true ∧ CaptureSet.noAny b.cs = true ∧
    CaptureSet.noAny b.bcs = true ∧ b.bsh.noAny = true

theorem varView_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    CaptureSet.noAny (varView Γ x).uses = true ∧ (varView Γ x).ty.noAny = true := by
  unfold varView
  split
  · exact ⟨rfl, hΓ x⟩
  · exact ⟨rfl, by simp only [Ty.noAny, CaptureSet.noAny, hΓ.shape x, Bool.and_self]⟩

theorem viewOf_parts {s : Sig} {Γ : Ctx s} {x : BVar s .var} (U : CaptureSet s) (T : Ty s)
    (d : HasTy U Γ (.path (.var x)) T) :
    (viewOf U T d).uses = U ∧ (viewOf U T d).cs = T.captureSet ∧ (viewOf U T d).sh = T.shape := by
  cases T
  exact ⟨rfl, rfl, rfl⟩

theorem vview_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    CaptureSet.noAny (vview Γ x).uses = true ∧ CaptureSet.noAny (vview Γ x).cs = true ∧
      (vview Γ x).sh.noAny = true := by
  obtain ⟨h1, h2, h3⟩ := viewOf_parts (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv
  obtain ⟨hu, ht⟩ := varView_noAny hΓ x
  unfold vview
  rw [h1, h2, h3]
  revert ht
  cases (varView Γ x).ty with
  | capt C S =>
    simp only [Ty.noAny, Ty.captureSet, Ty.shape, Bool.and_eq_true]
    exact fun h => ⟨hu, h.1, h.2⟩

theorem lookVar_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (k : Key) :
    Always (AllL fun e : Found Γ x (vview Γ x).sh => e.ty.noAny = true) (lookVar Γ x k) :=
  fun t => look_noAny hΓ t.left [] x _ k (vview_noAny hΓ x).2.2 t

theorem Found.fn?_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} {e : Found Γ x V}
    {r : (T1 : Ty s) × (T2 : Ty (s,x)) × VarFn Γ x V (.all T1 T2)}
    (h : e.fn? = some r) (he : e.ty.noAny = true) : r.1.noAny = true ∧ r.2.1.noAny = true := by
  unfold Found.fn? at h
  split at h
  · rename_i T1 T2 heq
    cases h
    rw [heq] at he
    simp only [Shape.noAny, Bool.and_eq_true] at he
    exact he
  · cases h

theorem Found.fld?_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} {a : Label}
    {e : Found Γ x V} {r : (T : Ty s) × VarFn Γ x V (.fld a T)}
    (h : e.fld? a = some r) (he : e.ty.noAny = true) : r.1.noAny = true := by
  unfold Found.fld? at h
  split at h
  · rename_i b T heq
    split at h
    · cases h
      rw [heq] at he
      simpa only [Shape.noAny] using he
    · cases h
  · cases h

theorem Found.box?_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} {e : Found Γ x V}
    {r : (C : CaptureSet s) × (S : Shape s) × VarFn Γ x V (.box (S ^ C))}
    (h : e.box? = some r) (he : e.ty.noAny = true) :
    CaptureSet.noAny r.1 = true ∧ r.2.1.noAny = true := by
  unfold Found.box? at h
  split at h
  · rename_i C S heq
    cases h
    rw [heq] at he
    simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at he
    exact he
  · cases h

theorem fnViewsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    Always (AllL FnView.NoAny) (fnViewsF Γ x) := by
  refine always_bind (lookVar_noAny hΓ x .fn) fun es hes => always_ret ?_
  refine allL_filterMap fun e he => ?_
  intro f hf
  cases hr : e.fn? with
  | none => rw [hr] at hf; cases hf
  | some r =>
    rw [hr] at hf
    cases hf
    obtain ⟨h1, h2⟩ := Found.fn?_noAny hr (hes e he)
    exact ⟨(vview_noAny hΓ x).1, (vview_noAny hΓ x).2.1, h1, h2⟩

theorem fldViewsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (a : Label) :
    Always (AllL FldView.NoAny) (fldViewsF Γ x a) := by
  refine always_bind (lookVar_noAny hΓ x (.fld a)) fun es hes => always_ret ?_
  refine allL_filterMap fun e he => ?_
  intro f hf
  cases hr : e.fld? a with
  | none => rw [hr] at hf; cases hf
  | some r =>
    rw [hr] at hf
    cases hf
    exact ⟨(vview_noAny hΓ x).1, (vview_noAny hΓ x).2.1, Found.fld?_noAny hr (hes e he)⟩

theorem boxViewsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    Always (AllL BoxView.NoAny) (boxViewsF Γ x) := by
  refine always_bind (lookVar_noAny hΓ x .box) fun es hes => always_ret ?_
  refine allL_filterMap fun e he => ?_
  intro b hb
  cases hr : e.box? with
  | none => rw [hr] at hb; cases hb
  | some r =>
    rw [hr] at hb
    cases hb
    obtain ⟨h1, h2⟩ := Found.box?_noAny hr (hes e he)
    exact ⟨(vview_noAny hΓ x).1, (vview_noAny hΓ x).2.1, h1, h2⟩

theorem varSynth_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    (varSynth Γ x).NoAny :=
  ⟨rfl, (varView_noAny hΓ x).1, (varView_noAny hΓ x).2⟩

theorem varFrom_uses {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U : CaptureSet s) (V : Ty s)
    (d : HasTy U Γ (.path (.var x)) V) (T : Ty s) :
    Always (OptP fun p : (U' : CaptureSet s) × HasTy U' Γ (.path (.var x)) T => p.1 = U)
      (varFrom Γ x U V d T) := by
  cases V with
  | capt Cv Sv =>
    cases T with
    | capt C' S' =>
      exact always_bindO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ =>
        always_mapO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ => rfl

theorem varF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (T : Ty s) :
    Always (OptP fun p : (U : CaptureSet s) × HasTy U Γ (.path (.var x)) T =>
      CaptureSet.noAny p.1 = true) (varF Γ x T) := by
  intro t p hp
  have := varFrom_uses Γ x (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv T t p hp
  rw [this]
  exact (varView_noAny hΓ x).1

theorem checkVarF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (T : Ty s) :
    Always (OptP fun r : VarChecked Γ x T => CaptureSet.noAny r.uses = true) (checkVarF Γ x T) :=
  always_mapO (varF_noAny hΓ x T) fun _ h => h

theorem subsumeF_noAny {s : Sig} (Γ : Ctx s) {r : Elab Γ} (hr : r.NoAny) (T : Ty s) :
    Always (OptP Checked.NoAny) (subsumeF Γ r T) := by
  unfold subsumeF
  refine always_dite (fun _ => always_ret (optP_some ⟨hr.1, hr.2.1⟩)) (fun _ => ?_)
  exact always_mapO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ => ⟨hr.1, hr.2.1⟩

theorem boxValue_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) :
    (boxValue Γ x).NoAny := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [boxValue, Ty.noAny, Shape.noAny, CaptureSet.noAny, (varView_noAny hΓ x).2,
    Bool.and_self]

theorem unboxOf_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s)
    {b : BoxView Γ x} (hb : b.NoAny) : OptP Elab.NoAny (unboxOf C b) := by
  unfold unboxOf
  split
  · rename_i hc
    subst hc
    refine optP_some ⟨hb.2.2.1, capJoin_noAny hb.2.2.1 hb.1, ?_⟩
    simp only [Ty.noAny, hb.2.2.1, hb.2.2.2, Bool.and_self]
  · exact optP_none _

theorem unboxAll_noAny {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s)
    {bs : List (BoxView Γ x)} (hbs : AllL BoxView.NoAny bs) : AllL Elab.NoAny (unboxAll C bs) :=
  allL_filterMap fun b hb => unboxOf_noAny C (hbs b hb)

theorem adaptInsertF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (G : Ty s) :
    Always (OptP Checked.NoAny) (adaptInsertF Γ x G) := by
  refine always_bind (boxViewsF_noAny hΓ x) fun bs hbs => ?_
  dsimp only
  split
  · exact always_orElse (always_mapO (Q := fun _ => True) (fun _ => optP_true _)
      fun _ _ => ⟨rfl, rfl⟩) (subsumeF_noAny Γ (boxValue_noAny hΓ x) G)
  · exact always_firstSome fun r hr => subsumeF_noAny Γ (unboxAll_noAny _ hbs r hr) G

theorem adaptVarF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (G : Ty s) :
    Always (OptP Checked.NoAny) (adaptVarF Γ x G) :=
  always_orElse (always_mapO (checkVarF_noAny hΓ x G) fun _ h => ⟨rfl, h⟩)
    (adaptInsertF_noAny hΓ x G)

end AdaptNoAny

section AvoidNoAny

theorem capMapUp_noAny {s : Sig} {Γ : Ctx s} {f : (a : CapAtom s) → Fu (CapAbove Γ [a])} :
    ∀ {C : CaptureSet s},
      (∀ a ∈ C, Always (fun r : CapAbove Γ [a] => CaptureSet.noAny r.1 = true) (f a)) →
      Always (fun r : CapAbove Γ C => CaptureSet.noAny r.1 = true) (capMapUp f C)
  | [], _ => always_ret rfl
  | a :: C, h => by
    rw [capMapUp]
    exact always_bind (h a (List.mem_cons_self ..)) fun _ h1 =>
      always_bind (capMapUp_noAny fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ h2 =>
        always_ret (capJoin_noAny h1 h2)

theorem capMapDown_noAny {s : Sig} {Γ : Ctx s} {f : (a : CapAtom s) → Fu (CapBelow Γ [a])} :
    ∀ {C : CaptureSet s},
      (∀ a ∈ C, Always (fun r : CapBelow Γ [a] => CaptureSet.noAny r.1 = true) (f a)) →
      Always (fun r : CapBelow Γ C => CaptureSet.noAny r.1 = true) (capMapDown f C)
  | [], _ => always_ret rfl
  | a :: C, h => by
    rw [capMapDown]
    exact always_bind (h a (List.mem_cons_self ..)) fun _ h1 =>
      always_bind (capMapDown_noAny fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ h2 =>
        always_ret (capJoin_noAny h1 h2)

theorem meetAll_noAny {s : Sig} {Γ : Ctx s} {S : Shape s} :
    ∀ {rs : List (Above Γ S)}, AllL (fun r : Above Γ S => r.1.noAny = true) rs →
      (meetAll rs).1.noAny = true
  | [], _ => rfl
  | [a], h => h a (List.mem_singleton_self _)
  | a :: b :: rest, h => by
    rw [meetAll]
    simp only [Shape.noAny, Bool.and_eq_true]
    exact ⟨h a (List.mem_cons_self ..),
      meetAll_noAny fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- Avoidance writes no `any`: every shape and set it gives is built from the
shape or set it approximates and from the bounds and declared sets of the
context. -/
theorem avoid_noAny : ∀ (d : Nat) {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List AKey)
    (S : Shape s) (C : CaptureSet s), CtxNoAny Γ → S.noAny = true → CaptureSet.noAny C = true →
    Always (fun r : Above Γ S => r.1.noAny = true) (up Γ z d P S) ∧
      Always (fun r : Below Γ S => r.1.noAny = true) (down Γ z d P S) ∧
      Always (fun r : CapAbove Γ C => CaptureSet.noAny r.1 = true) (capUp Γ z d P C) ∧
      Always (fun r : CapBelow Γ C => CaptureSet.noAny r.1 = true) (capDown Γ z d P C)
  | 0, _, _, _, _, _, _, _, hS, hC =>
    ⟨fun _ => rfl, fun _ => rfl, always_ite (always_ret hC) (fun _ => hC),
      always_ite (always_ret hC) (fun _ => rfl)⟩
  | d + 1, s, Γ, z, P, S, C, hΓ, hS, hC => by
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List AKey) (S : Shape s)
        (C : CaptureSet s), CtxNoAny Γ → S.noAny = true → CaptureSet.noAny C = true →
        Always (fun r : Above Γ S => r.1.noAny = true) (up Γ z d P S) ∧
          Always (fun r : Below Γ S => r.1.noAny = true) (down Γ z d P S) ∧
          Always (fun r : CapAbove Γ C => CaptureSet.noAny r.1 = true) (capUp Γ z d P C) ∧
          Always (fun r : CapBelow Γ C => CaptureSet.noAny r.1 = true) (capDown Γ z d P C) :=
      fun Γ z P S C => avoid_noAny d Γ z P S C
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine always_bind (always_true _) fun ok _ => ?_
      cases ok
      · exact always_ret rfl
      · refine always_ite (always_ret hS) ?_
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            refine always_ite (always_ret rfl) ?_
            refine always_bind (declsAt_noAny hΓ q A) fun ms hms => ?_
            refine always_bind (always_flatMapL (P := fun r : Above Γ (.sel (.var q) A) =>
              r.1.noAny = true) fun m hm => ?_) fun rs hrs => always_ret (meetAll_noAny hrs)
            exact always_bind (ih Γ z _ _ C hΓ (hms m hm).2 hC).1 fun r hr =>
              always_ret fun r' hr' => by
                simp only [List.mem_singleton] at hr'
                subst hr'
                exact hr
        | fld a T =>
          cases T with
          | capt C' S' =>
            simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
            exact always_bind (ih Γ z P S' C hΓ hS.2 hC).1 fun r hr =>
              always_bind (ih Γ z P S' C' hΓ hS.2 hS.1).2.2.1 fun c hc =>
                always_ret (by simp only [Shape.noAny, Ty.noAny, hr, hc, Bool.and_self])
        | typ A L H =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P L C hΓ hS.1 hC).2.1 fun l hl =>
            always_bind (ih Γ z P H C hΓ hS.2 hC).1 fun h hh =>
              always_ret (by simp only [Shape.noAny, hl, hh, Bool.and_self])
        | cap A c1 c2 =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P .top c1 hΓ rfl hS.1).2.2.2 fun l hl =>
            always_bind (ih Γ z P .top c2 hΓ rfl hS.2).2.2.1 fun h hh =>
              always_ret (by simp only [Shape.noAny, hl, hh, Bool.and_self])
        | and S1 S2 =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P S1 C hΓ hS.1 hC).1 fun r1 h1 =>
            always_bind (ih Γ z P S2 C hΓ hS.2 hC).1 fun r2 h2 =>
              always_ret (by simp only [Shape.noAny, h1, h2, Bool.and_self])
        | box T =>
          cases T with
          | capt C' S' =>
            simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
            exact always_bind (ih Γ z P S' C hΓ hS.2 hC).1 fun r hr =>
              always_bind (ih Γ z P S' C' hΓ hS.2 hS.1).2.2.1 fun c hc =>
                always_ret (by simp only [Shape.noAny, Ty.noAny, hr, hc, Bool.and_self])
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
              refine always_bind (ih Γ z P S1 C1 hΓ hS.1.2 hS.1.1).2.1 fun l hl => ?_
              refine always_bind (ih Γ z P S1 C1 hΓ hS.1.2 hS.1.1).2.2.2 fun lc hlc => ?_
              have hΓ' : CtxNoAny (Γ.cons (l.1 ^ lc.1)) :=
                hΓ.cons (by simp only [Ty.noAny, hl, hlc, Bool.and_self])
              exact always_bind (ih _ (.there z) P S2 C2 hΓ' hS.2.2 hS.2.1).1 fun r hr =>
                always_bind (ih _ (.there z) P S2 C2 hΓ' hS.2.2 hS.2.1).2.2.1 fun rc hrc =>
                  always_ret (by simp only [Shape.noAny, Ty.noAny, hl, hlc, hr, hrc,
                    Bool.and_self])
        | mu _ => exact always_ret rfl
        | top => exact always_ret rfl
        | bot => exact always_ret rfl
    · refine always_bind (always_true _) fun ok _ => ?_
      cases ok
      · exact always_ret rfl
      · refine always_ite (always_ret hS) ?_
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            refine always_ite (always_ret rfl) ?_
            refine always_bind (declsAt_noAny hΓ q A) fun ms hms => ?_
            cases ms with
            | nil => exact always_ret rfl
            | cons m _ =>
              exact always_bind (ih Γ z _ _ C hΓ (hms m (List.mem_cons_self ..)).1 hC).2.1
                fun r hr => always_ret hr
        | fld a T =>
          cases T with
          | capt C' S' =>
            simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
            exact always_bind (ih Γ z P S' C hΓ hS.2 hC).2.1 fun r hr =>
              always_bind (ih Γ z P S' C' hΓ hS.2 hS.1).2.2.2 fun c hc =>
                always_ret (by simp only [Shape.noAny, Ty.noAny, hr, hc, Bool.and_self])
        | typ A L H =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P L C hΓ hS.1 hC).1 fun l hl =>
            always_bind (ih Γ z P H C hΓ hS.2 hC).2.1 fun h hh =>
              always_ret (by simp only [Shape.noAny, hl, hh, Bool.and_self])
        | cap A c1 c2 =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P .top c1 hΓ rfl hS.1).2.2.1 fun l hl =>
            always_bind (ih Γ z P .top c2 hΓ rfl hS.2).2.2.2 fun h hh =>
              always_ret (by simp only [Shape.noAny, hl, hh, Bool.and_self])
        | and S1 S2 =>
          simp only [Shape.noAny, Bool.and_eq_true] at hS
          exact always_bind (ih Γ z P S1 C hΓ hS.1 hC).2.1 fun r1 h1 =>
            always_bind (ih Γ z P S2 C hΓ hS.2 hC).2.1 fun r2 h2 =>
              always_ret (by simp only [Shape.noAny, h1, h2, Bool.and_self])
        | box T =>
          cases T with
          | capt C' S' =>
            simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
            exact always_bind (ih Γ z P S' C hΓ hS.2 hC).2.1 fun r hr =>
              always_bind (ih Γ z P S' C' hΓ hS.2 hS.1).2.2.2 fun c hc =>
                always_ret (by simp only [Shape.noAny, Ty.noAny, hr, hc, Bool.and_self])
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              simp only [Shape.noAny, Ty.noAny, Bool.and_eq_true] at hS
              have hΓ' : CtxNoAny (Γ.cons (S1 ^ C1)) :=
                hΓ.cons (by simp only [Ty.noAny, hS.1.1, hS.1.2, Bool.and_self])
              exact always_bind (ih Γ z P S1 C1 hΓ hS.1.2 hS.1.1).1 fun l hl =>
                always_bind (ih Γ z P S1 C1 hΓ hS.1.2 hS.1.1).2.2.1 fun lc hlc =>
                  always_bind (ih _ (.there z) P S2 C2 hΓ' hS.2.2 hS.2.1).2.1 fun r hr =>
                    always_bind (ih _ (.there z) P S2 C2 hΓ' hS.2.2 hS.2.1).2.2.2 fun rc hrc =>
                      always_ret (by simp only [Shape.noAny, Ty.noAny, hl, hlc, hr, hrc,
                        Bool.and_self])
        | mu _ => exact always_ret rfl
        | top => exact always_ret rfl
        | bot => exact always_ret rfl
    · refine always_ite (always_ret hC) ?_
      refine always_bind (always_true _) fun ok _ => ?_
      cases ok
      · exact always_ret hC
      · refine capMapUp_noAny fun a ha => ?_
        have ha' := (CaptureSet.noAny_iff C).mp hC a ha
        cases a with
        | var y =>
          exact always_ite (always_bind (ih Γ z P S _ hΓ hS (hΓ.captureSet y)).2.2.1 fun r hr =>
            always_ret hr) (always_ret rfl)
        | sel y A =>
          refine always_ite (always_bind (capsAt_noAny hΓ y A) fun ms hms => ?_) (always_ret rfl)
          cases ms with
          | nil => exact always_ret rfl
          | cons m _ =>
            exact always_bind (ih Γ z _ S _ hΓ hS (hms m (List.mem_cons_self ..)).2).2.2.1
              fun r hr => always_ret hr
        | cvar _ => exact always_ret rfl
        | any => exact absurd rfl ha'
    · refine always_ite (always_ret hC) ?_
      refine always_bind (always_true _) fun ok _ => ?_
      cases ok
      · exact always_ret rfl
      · refine capMapDown_noAny fun a ha => ?_
        have ha' := (CaptureSet.noAny_iff C).mp hC a ha
        cases a with
        | var y => exact always_ite (always_ret rfl) (always_ret rfl)
        | sel y A =>
          refine always_ite (always_ite (always_ret rfl)
            (always_bind (capsAt_noAny hΓ y A) fun ms hms => ?_)) (always_ret rfl)
          cases ms with
          | nil => exact always_ret rfl
          | cons m _ =>
            exact always_bind (ih Γ z _ S _ hΓ hS (hms m (List.mem_cons_self ..)).1).2.2.2
              fun r hr => always_ret hr
        | cvar _ => exact always_ret rfl
        | any => exact absurd rfl ha'

theorem tyUpAt_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (z : BVar s .var) {T : Ty s}
    (hT : T.noAny = true) :
    Always (fun r : TyAbove Γ T => r.1.noAny = true) (tyUpAt Γ z T) := by
  intro t
  obtain ⟨C, S⟩ := T
  simp only [Ty.noAny, Bool.and_eq_true] at hT
  have h : Always (fun r : TyAbove Γ (S ^ C) => r.1.noAny = true)
      (tyUp Γ z t.left [] (S ^ C)) := by
    unfold tyUp
    refine always_bind (avoid_noAny t.left Γ z [] S C hΓ hT.2 hT.1).1 fun r hr =>
      always_bind (avoid_noAny t.left Γ z [] S C hΓ hT.2 hT.1).2.2.1 fun c hc => always_ret ?_
    simp only [Ty.noAny, hr, hc, Bool.and_self]
  exact h t

theorem capUpAt_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (z : BVar s .var) {C : CaptureSet s}
    (hC : CaptureSet.noAny C = true) :
    Always (fun r : CapAbove Γ C => CaptureSet.noAny r.1 = true) (capUpAt Γ z C) :=
  fun t => (avoid_noAny t.left Γ z [] .top C hΓ rfl hC).2.2.1 t

theorem unlessOut_always {α : Type} {P : α → Prop} {o : Option α} (h : OptP P o) :
    Always (OptP P) (unlessOut o) := by
  intro t
  unfold unlessOut
  split
  · exact optP_none P
  · exact h

theorem avoidLet_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T0 : Ty s} (h0 : T0.noAny = true)
    {V : Ty (s,x)} (hV : V.noAny = true) :
    Always (OptP fun r : LetTy Γ T0 V => r.1.noAny = true) (avoidLet Γ T0 V) := by
  refine always_bind (tyUpAt_noAny (hΓ.cons h0) .here hV) fun r hr => unlessOut_always ?_
  intro p hp
  unfold strengthenTy at hp
  split at hp
  · rename_i w _
    cases hp
    have hw := w.property
    rw [hw, Ty.noAny_weaken_eq] at hr
    exact hr
  · cases hp

theorem avoidUses_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T0 : Ty s} (h0 : T0.noAny = true)
    {V : CaptureSet (s,x)} (hV : CaptureSet.noAny V = true) :
    Always (OptP fun r : LetUses Γ T0 V => CaptureSet.noAny r.1 = true) (avoidUses Γ T0 V) := by
  refine always_bind (capUpAt_noAny (hΓ.cons h0) .here hV) fun r hr => unlessOut_always ?_
  intro p hp
  unfold strengthenSet at hp
  split at hp
  · rename_i w _
    cases hp
    have hw := w.property
    rw [hw, CaptureSet.noAny_weaken_eq] at hr
    exact hr
  · cases hp

end AvoidNoAny

/-! ### The typer -/

section TyperNoAny

/-- A goal holds no `any`. -/
def GoalNoAny {s : Sig} (G : Option (Ty s)) : Prop := ∀ T, G = some T → T.noAny = true

theorem goalNoAny_none {s : Sig} : GoalNoAny (none : Option (Ty s)) := fun _ h => nomatch h

theorem goalNoAny_some {s : Sig} {T : Ty s} (h : T.noAny = true) : GoalNoAny (some T) := by
  intro T' hT
  cases hT
  exact h

/-- Definitions typed against a shape hold no `any`. -/
def DefsElab.NoAny {s : Sig} {Γ : Ctx s} {S : Shape s} (r : DefsElab Γ S) : Prop :=
  r.tm.NoAnyAnn = true ∧ CaptureSet.noAny r.uses = true

theorem allL_dedupE {s : Sig} {Γ : Ctx s} {P : Elab Γ → Prop} :
    ∀ {l : List (Elab Γ)}, AllL P l → AllL P (dedupE l)
  | [], h => h
  | r :: rs, h => by
    rw [dedupE]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h _ (List.mem_cons_self ..)
    · exact allL_dedupE (fun c hc => h c (List.mem_cons_of_mem _ hc)) c
        (List.mem_filter.mp hc).1

theorem firstChecked_noAny {s : Sig} {Γ : Ctx s} {T : Ty s} :
    ∀ {rs : List (Elab Γ)}, AllL Elab.NoAny rs → OptP Checked.NoAny (firstChecked rs T)
  | [], _ => by
    intro c hc
    simp [firstChecked] at hc
  | r :: rs, h => by
    intro c hc
    simp only [firstChecked, List.findSome?_cons] at hc
    split at hc
    · rename_i c' hc'
      cases hc
      unfold toChecked at hc'
      split at hc'
      · cases hc'
        exact ⟨(h r (List.mem_cons_self ..)).1, (h r (List.mem_cons_self ..)).2.1⟩
      · cases hc'
    · exact firstChecked_noAny (fun c hc => h c (List.mem_cons_of_mem _ hc)) c hc

theorem finishF_noAny {s : Sig} (Γ : Ctx s) {G : Option (Ty s)} (hG : GoalNoAny G)
    {rs : List (Elab Γ)} (hrs : AllL Elab.NoAny rs) : Always (AllL Elab.NoAny) (finishF Γ G rs) := by
  cases G with
  | none => exact always_ret hrs
  | some T =>
    exact always_flatMapL fun r hr => always_mapL (subsumeF_noAny Γ (hrs r hr) T)
      fun c hc => Checked.toElab_noAny hc (hG T rfl)

theorem hereBoundsF_noAny {s : Sig} {Γ : Ctx (s,x)} (hΓ : CtxNoAny Γ) (V : CaptureSet (s,x)) :
    Always (AllL fun p : Label × CaptureSet (s,x) => CaptureSet.noAny p.2 = true)
      (hereBoundsF Γ V) := by
  refine always_flatMapL fun a _ => ?_
  dsimp only
  split
  · rename_i C _
    refine always_bind (capsAt_noAny hΓ .here C) fun ds hds => always_ret (allL_listO ?_)
    cases ds with
    | nil => exact optP_none _
    | cons d _ => exact optP_some (hds d (List.mem_cons_self ..)).2
  · exact always_ret (allL_nil _)

theorem selOf_noAny {s : Sig} {bs : List (Label × CaptureSet s)}
    (h : AllL (fun p : Label × CaptureSet s => CaptureSet.noAny p.2 = true) bs) (C : Label) :
    OptP (fun D : CaptureSet s => CaptureSet.noAny D = true) (selOf bs C) := by
  unfold selOf
  cases hf : bs.find? (fun p => decide (p.1 = C)) with
  | none => exact optP_none _
  | some p => exact optP_some (h p (List.mem_of_find?_eq_some hf))

theorem capReplaceHere_noAny {s : Sig} {R : CaptureSet (s,x)}
    {sel : Label → Option (CaptureSet (s,x))} (hR : CaptureSet.noAny R = true)
    (hsel : ∀ C, OptP (fun D : CaptureSet (s,x) => CaptureSet.noAny D = true) (sel C)) :
    ∀ {V : CaptureSet (s,x)}, CaptureSet.noAny V = true →
      CaptureSet.noAny (capReplaceHere R sel V) = true
  | [], _ => rfl
  | a :: V, hV => by
    rw [capReplaceHere]
    have ha := (CaptureSet.noAny_iff _).mp hV a (List.mem_cons_self ..)
    have hV' : CaptureSet.noAny V = true :=
      CaptureSet.noAny_of_subset (fun b hb => List.mem_cons_of_mem _ hb) hV
    refine capJoin_noAny ?_ (capReplaceHere_noAny hR hsel hV')
    unfold hereImage
    split
    · exact hR
    · rename_i C
      cases hs : sel C with
      | none => rfl
      | some D => exact hsel C D hs
    · rename_i a' _ _
      exact (CaptureSet.noAny_iff _).mpr fun b hb => by
        simp only [List.mem_singleton] at hb
        subst hb
        exact ha

theorem capDropHere_noAny {s : Sig} {sel : Label → Option (CaptureSet (s,x))}
    (hsel : ∀ C, OptP (fun D : CaptureSet (s,x) => CaptureSet.noAny D = true) (sel C))
    {V : CaptureSet (s,x)} (hV : CaptureSet.noAny V = true) :
    OptP (fun U : CaptureSet s => CaptureSet.noAny U = true) (capDropHere? sel V) := by
  intro U hU
  unfold capDropHere? capAvoid? at hU
  have h := capStrengthen?_sound hU
  have h2 := capReplaceHere_noAny (R := []) rfl hsel hV
  rw [h, CaptureSet.noAny_weaken_eq] at h2
  exact h2

theorem lamUsesF_noAny {s : Sig} {Γ : Ctx s} {T : Ty s} (hΓ : CtxNoAny (Γ.cons T))
    {V : CaptureSet (s,x)} (hV : CaptureSet.noAny V = true) :
    Always (OptP fun p : (U : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken U ∪ [.var .here]) =>
      CaptureSet.noAny p.1 = true) (lamUsesF Γ T V) := by
  refine always_bind (hereBoundsF_noAny hΓ V) fun bs hbs => ?_
  dsimp only
  split
  · rename_i U hU
    exact always_mapO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ =>
      capDropHere_noAny (selOf_noAny hbs) hV U hU
  · exact always_ret (optP_none _)

theorem letAtF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {A : Ty s} (hA : A.noAny = true) {r1 : Elab Γ} (h1 : r1.NoAny)
    {r2 : Checked (Γ.cons r1.ty) A.weaken} (h2 : r2.NoAny) :
    Always (OptP Elab.NoAny) (letAtF Γ ann A r1 r2) := by
  unfold letAtF
  refine always_dite (fun _ => ?_) (fun _ => always_ret (optP_none _))
  refine always_mapO (avoidUses_noAny hΓ h1.2.2 h2.2) fun p hp => ⟨?_, ?_, hA⟩
  · cases ann with
    | none => simp only [ATm.NoAnyAnn, h1.1, h2.1, Bool.and_self]
    | some U => simp only [ATm.NoAnyAnn, hann U rfl, h1.1, h2.1, Bool.and_self]
  · exact capJoin_noAny h1.2.1 hp

theorem letFinishF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {r1 : Elab Γ} (h1 : r1.NoAny)
    {r2 : Elab (Γ.cons r1.ty)} (h2 : r2.NoAny) :
    Always (OptP Elab.NoAny) (letFinishF Γ r1 r2) :=
  always_bindO (avoidLet_noAny hΓ h1.2.2 h2.2.2) fun _ ha =>
    letAtF_noAny hΓ goalNoAny_none ha h1 ⟨h2.1, h2.2.1⟩

theorem letPairsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {r1 : Elab Γ} (h1 : r1.NoAny)
    {body : Fu (List (Elab (Γ.cons r1.ty)))} (hb : Always (AllL Elab.NoAny) body) :
    Always (AllL Elab.NoAny) (letPairsF Γ r1 body) :=
  always_bind hb fun _ h2s => always_flatMapL fun r2 hr2 =>
    always_mapL (letFinishF_noAny hΓ h1 (h2s r2 hr2)) fun _ h => h

/-- The body of a `let` keeps no `any` at any goal that holds none. -/
def BodyNoAny {s : Sig} {Γ : Ctx s}
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))) : Prop :=
  ∀ r1, r1.NoAny → ∀ o, GoalNoAny o → Always (AllL Elab.NoAny) (body r1 o)

theorem letCheckF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {A : Ty s} (hA : A.noAny = true) {r1s : List (Elab Γ)}
    (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : BodyNoAny body) : Always (OptP Elab.NoAny) (letCheckF Γ ann A r1s body) := by
  refine always_firstSome fun r1 hr1 => ?_
  refine always_bind (hb r1 (hr1s r1 hr1) _ (goalNoAny_some (by rw [Ty.noAny_weaken_eq]; exact hA)))
    fun r2s h2s => ?_
  dsimp only
  split
  · rename_i c hc
    exact letAtF_noAny hΓ hann hA (hr1s r1 hr1) (firstChecked_noAny h2s c hc)
  · exact always_ret (optP_none _)

theorem letSpecialF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (ann : Option (Ty s))
    {G : Option (Ty s)} (hG : GoalNoAny G) {r1s : List (Elab Γ)} (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : BodyNoAny body) : Always (AllL Elab.NoAny) (letSpecialF Γ ann G r1s body) := by
  unfold letSpecialF
  split
  · rename_i T
    exact always_ite (always_mapL (letCheckF_noAny hΓ goalNoAny_none (hG T rfl) hr1s hb)
      fun _ h => h) (always_ret (allL_nil _))
  · exact always_ret (allL_nil _)

theorem letGenF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {r1s : List (Elab Γ)} (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : BodyNoAny body) : Always (AllL Elab.NoAny) (letGenF Γ ann r1s body) := by
  unfold letGenF
  cases ann with
  | some A =>
    exact always_mapL (letCheckF_noAny hΓ hann (hann A rfl) hr1s hb) fun _ h => h
  | none =>
    exact always_bind (always_flatMapL fun r1 hr1 =>
      letPairsF_noAny hΓ (hr1s r1 hr1) (hb r1 (hr1s r1 hr1) none goalNoAny_none))
      fun _ h => always_ret (allL_dedupE h)

theorem appWithF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {x : BVar s .var}
    {fs : List (FnView Γ x)} (hfs : AllL FnView.NoAny fs) (y : BVar s .var) :
    Always (AllL Elab.NoAny) (appWithF Γ fs y) :=
  always_flatMapL fun f hf => always_mapL (checkVarF_noAny hΓ y f.dom) fun r hr =>
    ⟨rfl, capJoin_noAny (hfs f hf).1 hr, by rw [Ty.noAny_substVar_eq]; exact (hfs f hf).2.2.2⟩

theorem appCoreF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x y : BVar s .var) :
    Always (AllL Elab.NoAny) (appCoreF Γ x y) :=
  always_bind (fnViewsF_noAny hΓ x) fun _ hfs => appWithF_noAny hΓ hfs y

theorem appStepWithF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x y : BVar s .var)
    {fs : List (FnView Γ x)} (hfs : AllL FnView.NoAny fs) :
    Always (AllL Elab.NoAny) (appStepWithF Γ x y fs) := by
  refine always_orElseL (appWithF_noAny hΓ hfs y) (always_flatMapL fun f hf => ?_)
  refine always_bind (adaptInsertF_noAny hΓ y f.dom) fun o ho => ?_
  cases o with
  | some r =>
    have hr : r.toElab.NoAny := Checked.toElab_noAny (ho r rfl) (hfs f hf).2.2.1
    exact letPairsF_noAny hΓ hr (appCoreF_noAny (hΓ.cons hr.2.2) _ _)
  | none => exact always_ret (allL_nil _)

theorem appStepF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x y : BVar s .var) :
    Always (AllL Elab.NoAny) (appStepF Γ x y) :=
  always_bind (fnViewsF_noAny hΓ x) fun _ hfs => appStepWithF_noAny hΓ x y hfs

theorem appAllF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x y : BVar s .var) :
    Always (AllL Elab.NoAny) (appAllF Γ x y) := by
  refine always_bind (fnViewsF_noAny hΓ x) fun fs hfs => ?_
  refine always_bind (P := AllL Elab.NoAny) ?_ fun _ h => always_ret (allL_dedupE h)
  cases fs with
  | nil =>
    refine always_bind (boxViewsF_noAny hΓ x) fun bs hbs => ?_
    dsimp only
    split
    · exact always_flatMapL fun r1 hr1 =>
        letPairsF_noAny hΓ (unboxAll_noAny _ hbs r1 hr1)
          (appStepF_noAny (hΓ.cons (unboxAll_noAny _ hbs r1 hr1).2.2) _ _)
    · exact always_ret (allL_nil _)
  | cons f fs => exact appStepWithF_noAny hΓ x y hfs

theorem projAllF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (x : BVar s .var) (a : Label) :
    Always (AllL Elab.NoAny) (projAllF Γ x a) := by
  refine always_bind (fldViewsF_noAny hΓ x a) fun fs hfs => ?_
  refine always_bind (P := AllL Elab.NoAny) ?_ fun _ h => always_ret (allL_dedupE h)
  cases fs with
  | nil =>
    refine always_bind (boxViewsF_noAny hΓ x) fun bs hbs => ?_
    dsimp only
    split
    · refine always_flatMapL fun r1 hr1 => letPairsF_noAny hΓ (unboxAll_noAny _ hbs r1 hr1) ?_
      exact always_bind (fldViewsF_noAny (hΓ.cons (unboxAll_noAny _ hbs r1 hr1).2.2) _ a)
        fun gs hgs => always_ret (allL_map fun g hg => ⟨rfl, (hgs g hg).1, (hgs g hg).2.2⟩)
    · exact always_ret (allL_nil _)
  | cons f fs =>
    exact always_ret (allL_map fun g hg => ⟨rfl, (hfs g hg).1, (hfs g hg).2.2⟩)

theorem lamGenF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true)
    (hwf : Ty.Wf T) {rs : List (Elab (Γ.cons T))} (hrs : AllL Elab.NoAny rs) :
    Always (AllL Elab.NoAny) (lamGenF Γ T hwf rs) :=
  always_flatMapL fun r hr => always_mapL (lamUsesF_noAny (hΓ.cons hT) (hrs r hr).2.1)
    fun p hp => ⟨by simp only [ATm.NoAnyAnn, hT, (hrs r hr).1, Bool.and_self], rfl,
      by simp only [Ty.noAny, Shape.noAny, hp, hT, (hrs r hr).2.2, Bool.and_self]⟩

theorem lamCheckF_noAny {s : Sig} {Γ : Ctx s} {T : Ty s} (hT : T.noAny = true) (hwf : Ty.Wf T)
    {C : CaptureSet s} {T1' : Ty s} {T2 : Ty (s,x)}
    (hG : ((Shape.all T1' T2) ^ C).noAny = true) {rs : List (Elab (Γ.cons T))}
    (hrs : AllL Elab.NoAny rs) : Always (AllL Elab.NoAny) (lamCheckF Γ T hwf C T1' T2 rs) := by
  unfold lamCheckF
  split
  · rename_i r hr
    have hr' := firstChecked_noAny hrs r hr
    refine always_mapL (Q := Elab.NoAny) ?_ fun _ h => h
    refine always_bindO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ => ?_
    refine always_mapO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ => ?_
    exact ⟨by simp only [ATm.NoAnyAnn, hT, hr'.1, Bool.and_self], rfl, hG⟩
  · exact always_ret (allL_nil _)

theorem funGoal?_eq {s : Sig} {G : Option (Ty s)} {C : CaptureSet s} {T1' : Ty s}
    {T2 : Ty (s,x)} (h : funGoal? G = some (C, T1', T2)) : G = some ((Shape.all T1' T2) ^ C) := by
  unfold funGoal? at h
  split at h
  · cases h
    rfl
  · cases h

theorem objDoneF_noAny {s : Sig} {Γ : Ctx s} {S : Shape (s,x)} (hS : S.noAny = true)
    (e : Defs (s,x)) {U : CaptureSet s} (hU : CaptureSet.noAny U = true)
    {r : DefsElab (Γ.consSelf e S U) S} (hr : r.NoAny) :
    Always (OptP Elab.NoAny) (objDoneF Γ S e U r) := by
  unfold objDoneF
  refine always_dite (fun _ => always_dite (fun _ => ?_) (fun _ => always_ret (optP_none _)))
    (fun _ => always_ret (optP_none _))
  exact always_mapO (Q := fun _ => True) (fun _ => optP_true _) fun _ _ =>
    ⟨by simp only [ATm.NoAnyAnn, hS, hU, hr.1, Bool.and_self], rfl,
      by simp only [Ty.noAny, Shape.noAny, hS, hU, Bool.and_self]⟩

theorem newAtomsF_noAny {s : Sig} (Γ : Ctx s) (U : CaptureSet s) {D : CaptureSet s}
    (hD : CaptureSet.noAny D = true) :
    Always (fun N : CaptureSet s => CaptureSet.noAny N = true) (newAtomsF Γ U D) := by
  have h : Always (AllL fun a : CapAtom s => a ≠ .any) (newAtomsF Γ U D) := by
    refine always_flatMapL fun a ha => ?_
    have ha' := (CaptureSet.noAny_iff D).mp hD a ha
    unfold newAtomF
    refine always_ite (always_ret (allL_nil _)) (always_bind (always_true _) fun o _ => ?_)
    cases o with
    | some _ => exact always_ret (allL_nil _)
    | none =>
      refine always_ret fun b hb => ?_
      simp only [List.mem_singleton] at hb
      subst hb
      exact ha'
  exact fun t => (CaptureSet.noAny_iff _).mpr (h t)

theorem objNextF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {S : Shape (s,x)}
    (hS : S.noAny = true) (fix : Bool) (e : Defs (s,x)) {U : CaptureSet s}
    (hU : CaptureSet.noAny U = true) {r : DefsElab (Γ.consSelf e S U) S} (hr : r.NoAny) :
    Always (fun U' : CaptureSet s => CaptureSet.noAny U' = true) (objNextF Γ S fix e U r) := by
  unfold objNextF
  refine always_ite (always_ret hU) ?_
  refine always_bind (hereBoundsF_noAny (hΓ.consSelf e hS hU) r.uses) fun bs hbs => ?_
  have hD : CaptureSet.noAny ((capDropHere? (selOf bs) r.uses).getD []) = true := by
    cases hd : capDropHere? (selOf bs) r.uses with
    | none => rfl
    | some D => exact capDropHere_noAny (selOf_noAny hbs) hr.2 D hd
  exact always_bind (newAtomsF_noAny Γ U hD) fun N hN => always_ret (capJoin_noAny hU hN)

theorem objFixF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {S : Shape (s,x)}
    (hS : S.noAny = true) (fix : Bool)
    {chk : (e : Defs (s,x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.consSelf e S U) S))}
    (hchk : ∀ e U, CaptureSet.noAny U = true → Always (OptP DefsElab.NoAny) (chk e U)) :
    ∀ k e U, CaptureSet.noAny U = true → Always (OptP Elab.NoAny) (objFixF Γ S fix chk k e U)
  | 0, e, U, _ => by
    rw [objFixF]
    exact fun _ => optP_none _
  | k + 1, e, U, hU => by
    rw [objFixF]
    refine always_bindO (hchk e U hU) fun r hr => ?_
    refine always_orElse (objDoneF_noAny hS e hU hr) ?_
    refine always_bind (objNextF_noAny hΓ hS fix e hU hr) fun U' hU' => ?_
    exact always_ite (always_ret (optP_none _)) (objFixF_noAny hΓ hS fix hchk k _ U' hU')

mutual

/-- The typer writes no `any`, from a context, a term and a goal that hold
none. -/
theorem inferF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    (a : ATm s) → a.NoAnyAnn = true → (G : Option (Ty s)) → GoalNoAny G →
      Always (AllL Elab.NoAny) (inferF Γ a G)
  | .path (.var x), _, G, hG => by
    cases G with
    | none =>
      rw [inferF]
      exact always_ret fun c hc => by
        simp only [List.mem_singleton] at hc
        subst hc
        exact varSynth_noAny hΓ x
    | some T =>
      rw [inferF]
      exact always_mapL (adaptVarF_noAny hΓ x T) fun c hc => Checked.toElab_noAny hc (hG T rfl)
  | .lam T t, ha, G, hG => by
    simp only [ATm.NoAnyAnn, Bool.and_eq_true] at ha
    rw [inferF]
    refine always_dite (fun hwf => always_orElseL ?_ ?_) (fun _ => always_ret (allL_nil _))
    · split
      · rename_i C T1' T2 hfg
        have hG' : ((Shape.all T1' T2) ^ C).noAny = true := hG _ (funGoal?_eq hfg)
        have hT2 : T2.noAny = true := by
          simp only [Ty.noAny, Shape.noAny, Bool.and_eq_true] at hG'
          exact hG'.2.2
        exact always_bind (inferF_noAny (hΓ.cons ha.1) t ha.2 _ (goalNoAny_some hT2))
          fun rs hrs => lamCheckF_noAny ha.1 hwf hG' hrs
      · exact always_ret (allL_nil _)
    · exact always_bind (inferF_noAny (hΓ.cons ha.1) t ha.2 none goalNoAny_none) fun rs hrs =>
        always_bind (lamGenF_noAny hΓ ha.1 hwf hrs) fun _ h => finishF_noAny Γ hG h
  | .obj S U0 d, ha, G, hG => by
    simp only [ATm.NoAnyAnn, Bool.and_eq_true] at ha
    obtain ⟨⟨hS, hU0⟩, hd⟩ := ha
    rw [inferF]
    have hU0' : CaptureSet.noAny (U0.getD []) = true := by
      cases U0 with
      | none => rfl
      | some C => exact hU0
    exact always_bind (objFixF_noAny hΓ hS _
      (fun e U hU => checkDefsF_noAny (hΓ.consSelf e hS hU) d hd S hS) _ _ _ hU0')
      fun o ho => finishF_noAny Γ hG (allL_listO ho)
  | .app x y, _, G, hG => by
    rw [inferF]
    exact always_bind (appAllF_noAny hΓ x y) fun _ h => finishF_noAny Γ hG h
  | .proj x a, _, G, hG => by
    rw [inferF]
    exact always_bind (projAllF_noAny hΓ x a) fun _ h => finishF_noAny Γ hG h
  | .let ann t u, ha, G, hG => by
    simp only [ATm.NoAnyAnn, Bool.and_eq_true] at ha
    obtain ⟨⟨hann, ht⟩, hu⟩ := ha
    have hann' : GoalNoAny ann := by
      intro A hA
      subst hA
      exact hann
    rw [inferF]
    refine always_bind (inferF_noAny hΓ t ht none goalNoAny_none) fun r1s hr1s => ?_
    have hb : BodyNoAny (fun r1 o => inferF (Γ.cons r1.ty) u o) :=
      fun r1 h1 o ho => inferF_noAny (hΓ.cons h1.2.2) u hu o ho
    exact always_orElseL (letSpecialF_noAny hΓ ann hG hr1s hb)
      (always_bind (letGenF_noAny hΓ hann' hr1s hb) fun _ h => finishF_noAny Γ hG h)
  | .box x, _, G, hG => by
    cases G with
    | some T =>
      rw [inferF]
      exact always_orElseL (always_mapL (Q := fun _ => True) (fun _ => optP_true _)
        fun _ _ => ⟨rfl, rfl, hG T rfl⟩)
        (finishF_noAny Γ hG fun c hc => by
          simp only [List.mem_singleton] at hc
          subst hc
          exact boxValue_noAny hΓ x)
    | none =>
      rw [inferF]
      exact always_orElseL (always_ret (allL_nil _))
        (finishF_noAny Γ hG fun c hc => by
          simp only [List.mem_singleton] at hc
          subst hc
          exact boxValue_noAny hΓ x)
  | .unbox C x, _, G, hG => by
    rw [inferF]
    exact always_bind (boxViewsF_noAny hΓ x) fun _ hbs =>
      finishF_noAny Γ hG (unboxAll_noAny C hbs)
  | .asc t T, ha, G, hG => by
    simp only [ATm.NoAnyAnn, Bool.and_eq_true] at ha
    rw [inferF]
    refine always_bind (inferF_noAny hΓ t ha.1 _ (goalNoAny_some ha.2)) fun rs hrs => ?_
    refine finishF_noAny Γ hG (allL_listO (optP_map (firstChecked_noAny hrs) fun c hc => ?_))
    exact ⟨by simp only [ATm.NoAnyAnn, hc.1, ha.2, Bool.and_self], hc.2, ha.2⟩

/-- Definitions checked against a shape that holds no `any` hold none. -/
theorem checkDefsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    (d : ADefs s) → d.NoAnyAnn = true → (S : Shape s) → S.noAny = true →
      Always (OptP DefsElab.NoAny) (checkDefsF Γ d S)
  | .typ A S0, hd, S, _ => by
    cases S with
    | typ B L U =>
      rw [checkDefsF]
      refine always_ret ?_
      split
      · split
        · split
          · exact optP_some ⟨hd, rfl⟩
          · exact optP_none _
        · exact optP_none _
      · exact optP_none _
    | _ => exact always_ret (optP_none _)
  | .cap A c, hd, S, _ => by
    cases S with
    | cap B c1 c2 =>
      rw [checkDefsF]
      refine always_ret ?_
      split
      · split
        · split
          · exact optP_some ⟨hd, rfl⟩
          · exact optP_none _
        · exact optP_none _
      · exact optP_none _
    | _ => exact always_ret (optP_none _)
  | .trm a t, hd, S, hS => by
    cases S with
    | fld c T =>
      rw [checkDefsF]
      refine always_dite (fun _ => ?_) (fun _ => always_ret (optP_none _))
      refine always_bind (inferF_noAny hΓ t hd _ (goalNoAny_some hS)) fun rs hrs => ?_
      exact always_ret (optP_map (firstChecked_noAny hrs) fun r hr => ⟨hr.1, hr.2⟩)
    | _ => exact always_ret (optP_none _)
  | .and d1 d2, hd, S, hS => by
    simp only [ADefs.NoAnyAnn, Bool.and_eq_true] at hd
    cases S with
    | and S1 S2 =>
      simp only [Shape.noAny, Bool.and_eq_true] at hS
      rw [checkDefsF]
      exact always_bindO (checkDefsF_noAny hΓ d1 hd.1 S1 hS.1) fun r1 h1 =>
        always_mapO (checkDefsF_noAny hΓ d2 hd.2 S2 hS.2) fun r2 h2 =>
          ⟨by simp only [ADefs.NoAnyAnn, h1.1, h2.1, Bool.and_self], capJoin_noAny h1.2 h2.2⟩
    | _ => exact always_ret (optP_none _)

end

end TyperNoAny

/-! ### The elaborator -/

section ElabNoAny

/-- A function part holds no `any`. -/
def FunPart.NoAny {s : Sig} : FunPart s → Prop
  | .none => True
  | .direct C T1 T2 => CaptureSet.noAny C = true ∧ T1.noAny = true ∧ T2.noAny = true
  | .side T1 V => T1.noAny = true ∧ V.noAny = true
  | .bad => True

theorem aliasOf_noAny {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} :
    ∀ {ms : List (TyMem Γ y A)}, AllL (fun m : TyMem Γ y A => m.1.noAny = true ∧ m.2.1.noAny = true) ms →
      OptP (fun S : Shape s => S.noAny = true) (aliasOf ms)
  | [], _ => optP_none _
  | m :: ms, h => by
    rw [aliasOf]
    split
    · exact optP_some (h m (List.mem_cons_self ..)).2
    · exact aliasOf_noAny fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

theorem uppersPart_noAny {s : Sig} {rec : Shape s → Fu (FunPart s)}
    (hr : ∀ S, S.noAny = true → Always FunPart.NoAny (rec S)) :
    ∀ {Ss : List (Shape s)}, AllL (fun S : Shape s => S.noAny = true) Ss →
      Always FunPart.NoAny (uppersPart rec Ss)
  | [], _ => always_ret trivial
  | S :: Ss, h => by
    rw [uppersPart]
    refine always_bind (hr S (h S (List.mem_cons_self ..))) fun f _ => ?_
    cases f with
    | none => exact uppersPart_noAny hr fun S' hS' => h S' (List.mem_cons_of_mem _ hS')
    | direct _ _ _ => exact always_ret trivial
    | side _ _ => exact always_ret trivial
    | bad => exact always_ret trivial

theorem meetRes_noAny {s : Sig} {V1 V2 : Ty s} (h1 : V1.noAny = true) (h2 : V2.noAny = true) :
    (meetRes V1 V2).noAny = true := by
  unfold meetRes
  split
  · exact h1
  · obtain ⟨C1, S1⟩ := V1
    obtain ⟨C2, S2⟩ := V2
    simp only [Ty.noAny, Bool.and_eq_true] at h1 h2
    simp only [Ty.noAny, Shape.noAny, h1.2, h2.2, Bool.and_true]
    exact CaptureSet.noAny_of_subset (fun a ha => (List.mem_filter.mp ha).1) h1.1

theorem meetPart_noAny {s : Sig} (Γ : Ctx s) {f1 f2 : FunPart s} (h1 : f1.NoAny) (h2 : f2.NoAny) :
    Always FunPart.NoAny (meetPart Γ f1 f2) := by
  cases f1 <;> cases f2 <;> simp only [meetPart] <;>
    first | exact always_ret trivial | exact always_ret h1 | exact always_ret h2 | skip
  rename_i S1 V1 S2 V2
  have hm := meetRes_noAny h1.2 h2.2
  refine always_ite (always_ret ⟨h1.1, hm⟩) (always_bind (always_true _) fun o2 _ => ?_)
  cases o2 with
  | some _ => exact always_ret ⟨h1.1, hm⟩
  | none =>
    refine always_bind (always_true _) fun o1 _ => ?_
    cases o1 with
    | some _ => exact always_ret ⟨h2.1, hm⟩
    | none => exact always_ret trivial

mutual

theorem funPartS_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {rec : Shape s → Fu (FunPart s)}
    (hr : ∀ S, S.noAny = true → Always FunPart.NoAny (rec S)) :
    ∀ S : Shape s, S.noAny = true → Always FunPart.NoAny (funPartS Γ rec S)
  | .all T1 T2, h => by
    simp only [Shape.noAny, Bool.and_eq_true] at h
    exact always_ret h
  | .and S1 S2, h => by
    simp only [Shape.noAny, Bool.and_eq_true] at h
    exact always_bind (funPartS_noAny hΓ hr S1 h.1) fun _ h1 =>
      always_bind (funPartS_noAny hΓ hr S2 h.2) fun _ h2 => meetPart_noAny Γ h1 h2
  | .box T, h => funPartT_noAny hΓ hr T (by simpa only [Shape.noAny] using h)
  | .sel (.var y) A, _ => by
    refine always_bind (declsAt_noAny hΓ y A) fun ms hms => ?_
    dsimp only
    split
    · rename_i S hS
      exact hr S (aliasOf_noAny hms S hS)
    · exact uppersPart_noAny hr (allL_map fun m hm => (hms m hm).2)
  | .top, _ => always_ret trivial
  | .bot, _ => always_ret trivial
  | .typ _ _ _, _ => always_ret trivial
  | .fld _ _, _ => always_ret trivial
  | .cap _ _ _, _ => always_ret trivial
  | .mu _, _ => always_ret trivial

theorem funPartT_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {rec : Shape s → Fu (FunPart s)}
    (hr : ∀ S, S.noAny = true → Always FunPart.NoAny (rec S)) :
    ∀ T : Ty s, T.noAny = true → Always FunPart.NoAny (funPartT Γ rec T)
  | .capt _ S, h => by
    simp only [Ty.noAny, Bool.and_eq_true] at h
    exact funPartS_noAny hΓ hr S h.2

end

theorem funPartF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    ∀ d seen (S : Shape s), S.noAny = true → Always FunPart.NoAny (funPartF Γ d seen S)
  | 0, _, S, h => funPartS_noAny hΓ (rec := fun _ => markAs .none) (fun _ _ _ => trivial) S h
  | d + 1, seen, S, h =>
    funPartS_noAny hΓ
      (rec := fun S' => if S' ∈ seen then Fu.ret .none else funPartF Γ d (S' :: seen) S')
      (fun S' hS' => always_ite (always_ret trivial)
        (funPartF_noAny hΓ d (S' :: seen) S' hS')) S h

theorem funPartOf_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {G : Option (Ty s)}
    (hG : GoalNoAny G) : Always FunPart.NoAny (funPartOf Γ G) := by
  cases G with
  | none => exact always_ret trivial
  | some T =>
    have hT := hG T rfl
    obtain ⟨C, S⟩ := T
    simp only [Ty.noAny, Bool.and_eq_true] at hT
    cases S <;> first
      | (simp only [Shape.noAny, Bool.and_eq_true] at hT
         exact always_ret ⟨hT.1, hT.2⟩)
      | exact fun t => funPartF_noAny hΓ t.left _ _ hT.2 t

theorem dealiasS_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {rec : Shape s → Fu (Shape s)}
    (hr : ∀ S, S.noAny = true → Always (fun S' : Shape s => S'.noAny = true) (rec S))
    {S : Shape s} (h : S.noAny = true) :
    Always (fun S' : Shape s => S'.noAny = true) (dealiasS Γ rec S) := by
  unfold dealiasS
  split
  · rename_i y A
    refine always_bind (declsAt_noAny hΓ y A) fun ms hms => ?_
    dsimp only
    split
    · rename_i S' hS'
      exact hr S' (aliasOf_noAny hms S' hS')
    · exact always_ret h
  · exact always_ret h

theorem dealiasF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    ∀ d seen (S : Shape s), S.noAny = true →
      Always (fun S' : Shape s => S'.noAny = true) (dealiasF Γ d seen S)
  | 0, _, _, h => dealiasS_noAny hΓ (fun _ hS' _ => hS') h
  | d + 1, seen, _, h =>
    dealiasS_noAny hΓ (fun S' hS' => always_ite (always_ret hS')
      (dealiasF_noAny hΓ d (S' :: seen) S' hS')) h

theorem selfGoalF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true) :
    Always (OptP fun B : Shape (s,x) => B.noAny = true) (selfGoalF Γ T) := by
  obtain ⟨C, S⟩ := T
  simp only [Ty.noAny, Bool.and_eq_true] at hT
  unfold selfGoalF
  have hd : Always (fun S' : Shape s => S'.noAny = true) (dealiasAt Γ S) :=
    fun t => dealiasF_noAny hΓ t.left [S] S hT.2 t
  refine always_bind hd fun S' hS' => ?_
  cases S' with
  | mu B => exact always_ret (optP_some (by simpa only [Shape.noAny] using hS'))
  | _ => exact always_ret (optP_none _)

theorem formalsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (g : BVar s .var) :
    Always (AllL fun F : Ty s => F.noAny = true) (formalsF Γ g) := by
  refine always_bind (fnViewsF_noAny hΓ g) fun fs hfs => ?_
  cases fs with
  | nil =>
    refine always_bind (boxViewsF_noAny hΓ g) fun bs hbs => always_ret ?_
    refine allL_filterMap fun b hb => ?_
    intro T hT
    unfold boxDom? at hT
    split at hT
    · rename_i T1 T2 heq
      cases hT
      have h := (hbs b hb).2.2.2
      rw [heq] at h
      simp only [Shape.noAny, Bool.and_eq_true] at h
      exact h.1
    · cases hT
  | cons f fs => exact always_ret (allL_map fun f hf => (hfs f hf).2.2.1)

theorem dominantF_mem {s : Sig} (Γ : Ctx s) (Fs : List (Ty s)) :
    ∀ cands : List (Ty s), Always (OptP fun F => F ∈ cands) (dominantF Γ Fs cands)
  | [] => always_ret (optP_none _)
  | F :: rest => by
    rw [dominantF]
    refine always_bind (always_true _) fun b _ => ?_
    cases b with
    | true => exact always_ret (optP_some (List.mem_cons_self ..))
    | false =>
      exact fun t F' hF' => List.mem_cons_of_mem _ (dominantF_mem Γ Fs rest t F' hF')

theorem argGoalF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (g : BVar s .var) :
    Always (OptP fun F : Ty s => F.noAny = true) (argGoalF Γ g) :=
  always_bind (formalsF_noAny hΓ g) fun Fs hFs t F hF => hFs F (dominantF_mem Γ Fs Fs t F hF)

theorem stripBox_noAny {s : Sig} {T : Ty s} (h : T.noAny = true) : (stripBox T).noAny = true := by
  unfold stripBox
  split
  · simp only [Ty.noAny, Shape.noAny, Bool.and_eq_true] at h
    exact h.2
  · exact h

/-- The candidates of an elaboration hold no `any`. -/
def OutNoAny {s : Sig} {Γ : Ctx s} (r : Out Γ) : Prop := AllL Elab.NoAny r.1

theorem withR_noAny {s : Sig} {Γ : Ctx s} {c : Fu (List (Elab Γ))}
    (hc : Always (AllL Elab.NoAny) c) : Always OutNoAny (withR c) :=
  always_bind hc fun _ h => always_ret h

theorem fullInfer_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {a : ATm s}
    (ha : a.NoAnyAnn = true) {G : Option (Ty s)} (hG : GoalNoAny G) :
    Always OutNoAny (fullInfer Γ a G) :=
  withR_noAny (inferF_noAny hΓ a ha G hG)

theorem orElseO_noAny {s : Sig} {Γ : Ctx s} {a b : Fu (Out Γ)} (ha : Always OutNoAny a)
    (hb : Always OutNoAny b) : Always OutNoAny (orElseO a b) := by
  refine always_bind ha fun r hr => ?_
  obtain ⟨l, rs⟩ := r
  cases l with
  | nil => exact always_bind hb fun _ h => always_ret h
  | cons _ _ => exact always_ret hr

theorem thenL_noAny {s s' : Sig} {Γ : Ctx s} {Δ : Ctx s'} {a : Fu (Out Δ)}
    {f : List (Elab Δ) → Fu (List (Elab Γ))} (ha : Always OutNoAny a)
    (hf : ∀ l, AllL Elab.NoAny l → Always (AllL Elab.NoAny) (f l)) : Always OutNoAny (thenL a f) :=
  always_bind ha fun r hr => always_bind (hf r.1 hr) fun _ h => always_ret h

theorem stopOr_always {β : Type} {P : β → Prop} {stop : Bool} {a : β} {c : Fu β} (ha : P a)
    (hc : Always P c) : Always P (stopOr stop a c) := by
  intro t
  unfold stopOr
  split
  · exact ha
  · exact hc t

theorem orElseW_always {α ρ : Type} {P : α → Prop} {ok : α → Bool} {a : Fu (α × List ρ)}
    {b : Unit → Fu (α × List ρ)} (ha : Always (fun r => P r.1) a)
    (hb : Always (fun r => P r.1) (b ())) : Always (fun r => P r.1) (orElseW ok a b) :=
  always_bind ha fun _ h => stopOr_always h (always_bind hb fun _ h' => always_ret h')

theorem firstSomeR_always {α β ρ : Type} {P : β → Prop} {f : α → Fu (Option β × List ρ)} :
    ∀ {l : List α}, (∀ x ∈ l, Always (fun r : Option β × List ρ => OptP P r.1) (f x)) →
      Always (fun r : Option β × List ρ => OptP P r.1) (firstSomeR f l)
  | [], _ => always_ret (optP_none P)
  | x :: xs, h => by
    rw [firstSomeR]
    exact orElseW_always (h x (List.mem_cons_self ..))
      (firstSomeR_always fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem flatMapR_always {α β ρ : Type} {P : β → Prop} {f : α → Fu (List β × List ρ)} :
    ∀ {l : List α}, (∀ x ∈ l, Always (fun r : List β × List ρ => AllL P r.1) (f x)) →
      Always (fun r : List β × List ρ => AllL P r.1) (flatMapR f l)
  | [], _ => always_ret (allL_nil P)
  | x :: xs, h => by
    rw [flatMapR]
    exact always_bind (h x (List.mem_cons_self ..)) fun _ h1 =>
      always_bind (flatMapR_always fun y hy => h y (List.mem_cons_of_mem _ hy)) fun _ h2 =>
        always_ret (allL_append h1 h2)

theorem lamGenFin_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true)
    (hwf : Ty.Wf T) {G : Option (Ty s)} (hG : GoalNoAny G) {rs : List (Elab (Γ.cons T))}
    (hrs : AllL Elab.NoAny rs) : Always (AllL Elab.NoAny) (lamGenFin Γ T hwf G rs) :=
  always_bind (lamGenF_noAny hΓ hT hwf hrs) fun _ h => finishF_noAny Γ hG h

theorem lamAtF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true)
    {G : Option (Ty s)} (hG : GoalNoAny G) {fp : FunPart s} (hfp : fp.NoAny)
    {body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))}
    (hb : ∀ o, GoalNoAny o → Always OutNoAny (body o)) : Always OutNoAny (lamAtF Γ T G fp body) := by
  unfold lamAtF
  refine always_dite (fun hwf => orElseO_noAny ?_ ?_) (fun _ => always_ret (allL_nil _))
  · cases fp with
    | direct C T1' T2 =>
      have hG' : ((Shape.all T1' T2) ^ C).noAny = true := by
        simp only [Ty.noAny, Shape.noAny, hfp.1, hfp.2.1, hfp.2.2, Bool.and_self]
      exact thenL_noAny (hb _ (goalNoAny_some hfp.2.2)) fun _ h => lamCheckF_noAny hT hwf hG' h
    | side _ V =>
      exact thenL_noAny (hb _ (goalNoAny_some hfp.2)) fun _ h => lamGenFin_noAny hΓ hT hwf hG h
    | none => exact always_ret (allL_nil _)
    | bad => exact always_ret (allL_nil _)
  · exact thenL_noAny (hb _ goalNoAny_none) fun _ h => lamGenFin_noAny hΓ hT hwf hG h

theorem lamSomeF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {T : Ty s} (hT : T.noAny = true)
    {G : Option (Ty s)} (hG : GoalNoAny G) {body : Option (Ty (s,x)) → Fu (Out (Γ.cons T))}
    (hb : ∀ o, GoalNoAny o → Always OutNoAny (body o)) : Always OutNoAny (lamSomeF Γ T G body) :=
  always_bind (funPartOf_noAny hΓ hG) fun _ hfp => lamAtF_noAny hΓ hT hG hfp hb

theorem lamCalleeF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {G : Option (Ty s)}
    (hG : GoalNoAny G) {t : PTm (s,x)} (ht : t.NoAnyAnn = true) :
    Always OutNoAny (lamCalleeF Γ G t) := by
  unfold lamCalleeF
  split
  · rename_i g _
    refine always_bind (argGoalF_noAny hΓ g) fun oS hoS => ?_
    cases oS with
    | none => exact always_ret (allL_nil _)
    | some S =>
      cases hb : t.full? with
      | none => exact always_ret (allL_nil _)
      | some b =>
        exact fullInfer_noAny hΓ (by simp only [ATm.NoAnyAnn, hoS S rfl,
          PTm.NoAnyAnn_of_full? hb ht, Bool.and_self]) hG
  · exact always_ret (allL_nil _)

theorem lamNoneF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {G : Option (Ty s)}
    (hG : GoalNoAny G) {t : PTm (s,x)} (ht : t.NoAnyAnn = true)
    {body : (T1 : Ty s) → Option (Ty (s,x)) → Fu (Out (Γ.cons T1))}
    (hb : ∀ T1, T1.noAny = true → ∀ o, GoalNoAny o → Always OutNoAny (body T1 o)) :
    Always OutNoAny (lamNoneF Γ G t body) := by
  refine always_bind (funPartOf_noAny hΓ hG) fun fp hfp => ?_
  cases fp with
  | direct C T1 T2 =>
    show Always OutNoAny (match t.full? with
      | some b => fullInfer Γ (.lam T1 b) G
      | none => lamAtF Γ T1 G (.direct C T1 T2) (body T1))
    split
    · rename_i b hb'
      exact fullInfer_noAny hΓ (by simp only [ATm.NoAnyAnn, hfp.2.1,
        PTm.NoAnyAnn_of_full? hb' ht, Bool.and_self]) hG
    · exact lamAtF_noAny hΓ hfp.2.1 hG hfp (hb T1 hfp.2.1)
  | side T1 V =>
    show Always OutNoAny (match t.full? with
      | some b => fullInfer Γ (.lam T1 b) G
      | none => lamAtF Γ T1 G (.side T1 V) (body T1))
    split
    · rename_i b hb'
      exact fullInfer_noAny hΓ (by simp only [ATm.NoAnyAnn, hfp.1,
        PTm.NoAnyAnn_of_full? hb' ht, Bool.and_self]) hG
    · exact lamAtF_noAny hΓ hfp.1 hG hfp (hb T1 hfp.1)
  | none => exact lamCalleeF_noAny hΓ hG ht
  | bad => exact always_ret (allL_nil _)

/-- The body of a `let` elaborates with no `any` at any goal that holds
none. -/
def BodyNoAnyO {s : Sig} {Γ : Ctx s}
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))) : Prop :=
  ∀ r1, r1.NoAny → ∀ o, GoalNoAny o → Always OutNoAny (body r1 o)

theorem letCheckO_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {A : Ty s} (hA : A.noAny = true) {r1s : List (Elab Γ)}
    (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : BodyNoAnyO body) : Always OutNoAny (letCheckO Γ ann A r1s body) := by
  unfold letCheckO
  refine always_bind (firstSomeR_always (P := Elab.NoAny) fun r1 hr1 => ?_) fun r hr =>
    always_ret (allL_listO hr)
  refine always_bind (hb r1 (hr1s r1 hr1) _
    (goalNoAny_some (by rw [Ty.noAny_weaken_eq]; exact hA))) fun r2 h2 => ?_
  dsimp only
  split
  · rename_i c hc
    exact always_bind (letAtF_noAny hΓ hann hA (hr1s r1 hr1) (firstChecked_noAny h2 c hc))
      fun _ h => always_ret h
  · exact always_ret (optP_none _)

theorem letSpecialO_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (ann : Option (Ty s))
    {G : Option (Ty s)} (hG : GoalNoAny G) {r1s : List (Elab Γ)} (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : BodyNoAnyO body) : Always OutNoAny (letSpecialO Γ ann G r1s body) := by
  unfold letSpecialO
  split
  · rename_i T
    exact always_ite (letCheckO_noAny hΓ goalNoAny_none (hG T rfl) hr1s hb)
      (always_ret (allL_nil _))
  · exact always_ret (allL_nil _)

theorem letGenO_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {r1s : List (Elab Γ)} (hr1s : AllL Elab.NoAny r1s)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : BodyNoAnyO body) : Always OutNoAny (letGenO Γ ann r1s body) := by
  unfold letGenO
  cases ann with
  | some A => exact letCheckO_noAny hΓ hann (hann A rfl) hr1s hb
  | none =>
    refine always_bind (flatMapR_always (P := Elab.NoAny) fun r1 hr1 => ?_) fun r hr =>
      always_ret (allL_dedupE hr)
    refine always_bind (hb r1 (hr1s r1 hr1) none goalNoAny_none) fun r2 h2 => ?_
    refine always_bind (always_flatMapL fun r2' hr2' =>
      always_mapL (letFinishF_noAny hΓ (hr1s r1 hr1) (h2 r2' hr2')) fun _ h => h) fun _ h =>
        always_ret h

theorem letO_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {ann : Option (Ty s)}
    (hann : GoalNoAny ann) {G : Option (Ty s)} (hG : GoalNoAny G) {bound : Fu (Out Γ)}
    (hbound : Always OutNoAny bound)
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    (hb : BodyNoAnyO body) : Always OutNoAny (letO Γ ann G bound body) :=
  always_bind hbound fun _ h1 => always_ite (always_ret (allL_nil _))
    (orElseO_noAny (letSpecialO_noAny hΓ ann hG h1 hb)
      (thenL_noAny (letGenO_noAny hΓ hann h1 hb) fun _ h => finishF_noAny Γ hG h))

theorem argLetF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {G : Option (Ty s)}
    (hG : GoalNoAny G) (g : BVar s .var) {b : ATm (s,x)} (hb : b.NoAnyAnn = true)
    {arg : Ty s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ F, F.noAny = true → Always OutNoAny (arg F)) (hgen : Always OutNoAny (gen ())) :
    Always OutNoAny (argLetF Γ G g b arg gen) := by
  refine always_bind (argGoalF_noAny hΓ g) fun oF hoF => ?_
  cases oF with
  | none => exact hgen
  | some F =>
    refine orElseW_always (P := AllL Elab.NoAny) ?_ hgen
    refine always_bind (harg _ (stripBox_noAny (hoF F rfl))) fun r hr => ?_
    dsimp only
    split
    · rename_i c _ heq
      have hc : c.NoAny := hr c (by rw [heq]; exact List.mem_cons_self ..)
      exact fullInfer_noAny hΓ (by simp only [ATm.NoAnyAnn, hc.1, hb, Bool.and_self]) hG
    · exact always_ret (allL_nil _)

theorem letF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (tag : LetTag) (ann : Option (Ty s))
    {u : PTm (s,x)} (hu : u.NoAnyAnn = true) {G : Option (Ty s)} (hG : GoalNoAny G)
    {arg : Ty s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ F, F.noAny = true → Always OutNoAny (arg F)) (hgen : Always OutNoAny (gen ())) :
    Always OutNoAny (letF Γ tag ann u G arg gen) := by
  unfold letF
  split
  · rename_i g b _ hb
    exact argLetF_noAny hΓ hG g (PTm.NoAnyAnn_of_full? hb hu) harg hgen
  · exact hgen

theorem ascO_noAny {s : Sig} {Γ : Ctx s} {T : Ty s} (hT : T.noAny = true) {G : Option (Ty s)}
    (hG : GoalNoAny G) {r : Fu (Out Γ)} (hr : Always OutNoAny r) :
    Always OutNoAny (ascO Γ T G r) :=
  thenL_noAny hr fun rs hrs => finishF_noAny Γ hG (allL_listO (optP_map
    (firstChecked_noAny hrs) fun c hc =>
      ⟨by simp only [ATm.NoAnyAnn, hc.1, hT, Bool.and_self], hc.2, hT⟩))

theorem allAtoms_noAny {s : Sig} (Γ : Ctx s) : CaptureSet.noAny (allAtoms Γ) = true := by
  refine (CaptureSet.noAny_iff _).mpr fun a ha => ?_
  unfold allAtoms at ha
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨y, _, rfl⟩ := List.mem_map.mp h
    exact fun h => nomatch h
  · obtain ⟨y, _, rfl⟩ := List.mem_map.mp h
    exact fun h => nomatch h

theorem probeCtx_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {S : Shape (s,x)}
    (hS : S.noAny = true) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true) :
    CtxNoAny (probeCtx Γ S U0) := by
  refine hΓ.cons ?_
  have hU : CaptureSet.noAny (U0.getD (allAtoms Γ)) = true := by
    cases U0 with
    | none => exact allAtoms_noAny Γ
    | some C => exact hU0 C rfl
  simp only [Ty.noAny, Shape.noAny, hS, hU, Bool.and_self]

theorem objSelfF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {S : Shape (s,x)}
    (hS : S.noAny = true) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true)
    {G : Option (Ty s)} (hG : GoalNoAny G) {defs : Fu (Option (ADefs (s,x)) × List EReason)}
    (hd : Always (fun r : Option (ADefs (s,x)) × List EReason =>
      OptP (fun d : ADefs (s,x) => d.NoAnyAnn = true) r.1) defs) :
    Always OutNoAny (objSelfF Γ S U0 G defs) := by
  refine always_bind hd fun r hr => ?_
  dsimp only
  split
  · rename_i d' heq
    have hd' := hr d' heq
    refine fullInfer_noAny hΓ ?_ hG
    cases U0 with
    | none => simp only [ATm.NoAnyAnn, hS, hd', Bool.and_self]
    | some C => simp only [ATm.NoAnyAnn, hS, hU0 C rfl, hd', Bool.and_self]
  · exact always_ret (allL_nil _)

/-- A job's elaboration writes no `any` in a context that holds none. -/
def Job.NoAny {s : Sig} (j : Job s) : Prop := ∀ Δ, CtxNoAny Δ → Always OutNoAny (j.run Δ)

/-- A typed job holds no `any` in its elaborated term or its type. -/
def Done.NoAny {s : Sig} (e : Done s) : Prop := e.a.NoAnyAnn = true ∧ e.ty.noAny = true

/-- Every type a list gives a label holds no `any`. -/
def KnownNoAny {s : Sig} (known : List (Label × Ty s)) : Prop := ∀ p ∈ known, p.2.noAny = true

theorem lookupL_noAny {s : Sig} :
    ∀ {known : List (Label × Ty s)}, KnownNoAny known → ∀ {a : Label} {T : Ty s},
      lookupL known a = some T → T.noAny = true
  | [], _, _, _, h => by simp [lookupL] at h
  | (b, U) :: l, hk, a, T, h => by
    unfold lookupL at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hk _ (List.mem_cons_self ..)
    · exact lookupL_noAny (fun p hp => hk p (List.mem_cons_of_mem _ hp)) h

theorem known_noAny {s : Sig} {ds : List (Done s)} (h : AllL Done.NoAny ds) :
    KnownNoAny (Done.known ds) := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact (h e he).2

theorem partialSelf_noAny {s : Sig} {known : List (Label × Ty s)} (hk : KnownNoAny known) :
    ∀ {d : PDefs s}, d.NoAnyAnn = true → ∀ {S : Shape s}, d.partialSelf known = some S →
      S.noAny = true
  | .typ A S0, hd, S, h => by
    simp only [PDefs.partialSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn] at hd
    simp only [Shape.noAny, hd, Bool.and_self]
  | .cap C c, hd, S, h => by
    simp only [PDefs.partialSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn] at hd
    simp only [Shape.noAny, hd, Bool.and_self]
  | .trm a (some T) t, hd, S, h => by
    simp only [PDefs.partialSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    simpa only [Shape.noAny] using hd.1
  | .trm a none t, _, S, h => by
    simp only [PDefs.partialSelf, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    simpa only [Shape.noAny] using lookupL_noAny hk hT
  | .and d e, hd, S, h => by
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    simp only [PDefs.partialSelf] at h
    cases h1 : d.partialSelf known with
    | none =>
      simp only [h1] at h
      exact partialSelf_noAny hk hd.2 h
    | some S1 =>
      cases h2 : e.partialSelf known with
      | none =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact partialSelf_noAny hk hd.1 h1
      | some S2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        simp only [Shape.noAny, partialSelf_noAny hk hd.1 h1, partialSelf_noAny hk hd.2 h2,
          Bool.and_self]

/-- The snapshot holds no `any` when the definitions and the known field types
hold none. -/
theorem probeSelf_noAny {s : Sig} {d : PDefs s} (hd : d.NoAnyAnn = true)
    {known : List (Label × Ty s)} (hk : KnownNoAny known) : (d.probeSelf known).noAny = true := by
  unfold PDefs.probeSelf
  cases h : d.partialSelf known with
  | none => rfl
  | some S => exact partialSelf_noAny hk hd h

/-- The formed self shape holds no `any` when the definitions and the known
field types hold none. -/
theorem fullSelf_noAny {s : Sig} {known : List (Label × Ty s)} (hk : KnownNoAny known) :
    ∀ {d : PDefs s}, d.NoAnyAnn = true → ∀ {S : Shape s}, d.fullSelf known = some S →
      S.noAny = true
  | .typ A S0, hd, S, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn] at hd
    simp only [Shape.noAny, hd, Bool.and_self]
  | .cap C c, hd, S, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn] at hd
    simp only [Shape.noAny, hd, Bool.and_self]
  | .trm a (some T) t, hd, S, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    simpa only [Shape.noAny] using hd.1
  | .trm a none t, _, S, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    simpa only [Shape.noAny] using lookupL_noAny hk hT
  | .and d e, hd, S, h => by
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf known with
    | none => simp only [h1, reduceCtorEq] at h
    | some S1 =>
      cases h2 : e.fullSelf known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some S2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        simp only [Shape.noAny, fullSelf_noAny hk hd.1 h1, fullSelf_noAny hk hd.2 h2,
          Bool.and_self]

/-- The least candidate is one of the candidates. -/
theorem leastCandF_mem {s : Sig} {Γ : Ctx s} (cs : List (Elab Γ)) :
    Always (OptP fun c => c ∈ cs) (leastCandF Γ cs) := by
  intro t
  cases h : leastCandF Γ cs t with
  | mk o t' =>
    cases o with
    | none => exact optP_none _
    | some c => exact optP_some (leastCand_least h).1

theorem runJobF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true) {P : Shape (s,x)}
    (hP : P.noAny = true) {j : Job (s,x)} (hj : j.NoAny) :
    Always (fun r : Except (List EReason) (Done (s,x)) => ∀ e, r = .ok e → e.NoAny)
      (runJobF Γ U0 P j) := by
  refine always_bind (hj _ (probeCtx_noAny hΓ hP hU0)) fun r hr => ?_
  dsimp only
  split
  · exact always_ret fun e h => nomatch h
  · rename_i c cs hcs
    refine always_bind (leastCandF_mem _) fun o ho => ?_
    cases o with
    | some e =>
      have he : e ∈ r.1 := by
        rw [hcs]
        exact ho e rfl
      have hne := hr e he
      refine always_ret fun e' h => ?_
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨hne.1, hne.2.2⟩
    | none => exact always_ret fun e h => nomatch h

theorem roundF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true) {P : Shape (s,x)}
    (hP : P.noAny = true) :
    ∀ (js : List (Job (s,x))), (∀ j ∈ js, j.NoAny) →
      Always (fun r : Except (List EReason) (List (Done (s,x))) =>
        ∀ es, r = .ok es → AllL Done.NoAny es) (roundF Γ U0 P js)
  | [], _ => by
    unfold roundF
    exact always_ret fun es h => by
      simp only [Except.ok.injEq] at h
      subst h
      exact allL_nil _
  | j :: js, hj => by
    unfold roundF
    refine always_bind (runJobF_noAny hΓ hU0 hP (hj j (List.mem_cons_self ..))) fun r hr => ?_
    cases r with
    | ok e =>
      refine always_bind (roundF_noAny hΓ hU0 hP js fun j' h' => hj j' (List.mem_cons_of_mem _ h'))
        fun r' hr' => ?_
      cases r' with
      | ok es =>
        refine always_ret fun es' h => ?_
        simp only [Except.ok.injEq] at h
        subst h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr a rfl
        · exact hr' es rfl a ha
      | error _ => exact always_ret fun es h => nomatch h
    | error _ => exact always_ret fun es h => nomatch h

/-- The rounds write no `any` when the context, the set, the snapshots and
every job's elaboration hold none. -/
theorem roundsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true)
    {probe : List (Label × Ty (s,x)) → Shape (s,x)}
    (hp : ∀ known, KnownNoAny known → (probe known).noAny = true) :
    ∀ (n : Nat) (js : List (Job (s,x))) (done : List (Done (s,x))), (∀ j ∈ js, j.NoAny) →
      AllL Done.NoAny done →
      Always (fun r : Except (List EReason) (List (Done (s,x))) =>
        ∀ es, r = .ok es → AllL Done.NoAny es) (roundsF Γ U0 probe n js done)
  | _, [], done, _, hd => by
    unfold roundsF
    exact always_ret fun es h => by
      simp only [Except.ok.injEq] at h
      subst h
      exact hd
  | 0, j :: js, _, _, _ => by
    unfold roundsF
    exact always_ret fun es h => nomatch h
  | n + 1, j :: js, done, hj, hd => by
    unfold roundsF
    split
    · exact always_ret fun es h => nomatch h
    · refine always_bind (roundF_noAny hΓ hU0 (hp _ (known_noAny hd)) _
        fun j' h' => hj j' (List.mem_filter.mp h').1) fun r hr => ?_
      cases r with
      | ok new =>
        exact roundsF_noAny hΓ hU0 hp n _ _ (fun j' h' => hj j' (List.mem_filter.mp h').1)
          (allL_append hd (hr new rfl))
      | error _ => exact always_ret fun es h => nomatch h

/-- The formed self shape and the typed jobs hold no `any` when the context,
the set, the definitions and every job's elaboration hold none. -/
theorem formSelfF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true) {d : PDefs (s,x)}
    (hd : d.NoAnyAnn = true) {js : List (Job (s,x))} (hj : ∀ j ∈ js, j.NoAny) :
    Always (fun r : Except (List EReason) (Shape (s,x) × List (Done (s,x))) =>
      ∀ S done, r = .ok (S, done) → S.noAny = true ∧ AllL Done.NoAny done)
      (formSelfF Γ U0 d js) := by
  refine always_bind (roundsF_noAny hΓ hU0 (fun known hk => probeSelf_noAny hd hk) _ js [] hj
    (allL_nil _)) fun r hr => ?_
  cases r with
  | ok done =>
    have hdn := hr done rfl
    refine always_ret ?_
    intro S done' h
    cases hf : d.fullSelf (Done.known done) with
    | none => simp only [hf, reduceCtorEq] at h
    | some S' =>
      simp only [hf, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fullSelf_noAny (known_noAny hdn) hd hf, hdn⟩
  | error _ => exact always_ret fun _ _ h => nomatch h

theorem lookupDone_mem {s : Sig} {a : Label} :
    ∀ {done : List (Done s)} {e : Done s}, lookupDone done a = some e → e ∈ done
  | [], _, h => nomatch h
  | e' :: es, e, h => by
    unfold lookupDone at h
    split at h
    · cases h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookupDone_mem h)

theorem objNoneF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) {U0 : Option (CaptureSet s)}
    (hU0 : ∀ C, U0 = some C → CaptureSet.noAny C = true) {G : Option (Ty s)} (hG : GoalNoAny G)
    {form : Fu (Except (List EReason) (Shape (s,x) × List (Done (s,x))))}
    {fill : Shape (s,x) → List (Done (s,x)) → Fu (Option (ADefs (s,x)) × List EReason)}
    (hf : Always (fun r : Except (List EReason) (Shape (s,x) × List (Done (s,x))) =>
      ∀ S done, r = .ok (S, done) → S.noAny = true ∧ AllL Done.NoAny done) form)
    (hl : ∀ S done, S.noAny = true → AllL Done.NoAny done →
      Always (fun r : Option (ADefs (s,x)) × List EReason =>
        OptP (fun e : ADefs (s,x) => e.NoAnyAnn = true) r.1) (fill S done)) :
    Always OutNoAny (objNoneF Γ U0 G form fill) := by
  refine always_bind hf fun r hr => ?_
  cases r with
  | ok p =>
    obtain ⟨S, done⟩ := p
    have h := hr S done rfl
    exact objSelfF_noAny hΓ h.1 hU0 hG (hl S done h.1 h.2)
  | error _ => exact always_ret (allL_nil _)

mutual

/-- The elaborator writes no `any`, from a context, a partial term and a goal
that hold none. -/
theorem elabF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    (p : PTm s) → p.NoAnyAnn = true → (G : Option (Ty s)) → GoalNoAny G →
      Always OutNoAny (elabF Γ p G)
  | .path q, hp, G, hG => by
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact always_ret (allL_nil _)
  | .app x y, hp, G, hG => by
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact always_ret (allL_nil _)
  | .proj x l, hp, G, hG => by
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact always_ret (allL_nil _)
  | .box x, hp, G, hG => by
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact always_ret (allL_nil _)
  | .unbox C x, hp, G, hG => by
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact always_ret (allL_nil _)
  | .lam (some T) t, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hp'
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact lamSomeF_noAny hΓ hp'.1 hG fun o ho => elabF_noAny (hΓ.cons hp'.1) t hp'.2 o ho
  | .lam none t, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.true_and] at hp'
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact lamNoneF_noAny hΓ hG hp' fun T1 hT1 o ho => elabF_noAny (hΓ.cons hT1) t hp' o ho
  | .obj (some S) U0 d, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hp'
    obtain ⟨⟨hS, hU0⟩, hd⟩ := hp'
    have hU0' : ∀ C, U0 = some C → CaptureSet.noAny C = true := by
      intro C hC
      subst hC
      exact hU0
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact objSelfF_noAny hΓ hS hU0' hG
        (elabDefsF_noAny (probeCtx_noAny hΓ hS hU0') d hd S hS)
  | .obj none U0 d, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.true_and, Bool.and_eq_true] at hp'
    obtain ⟨hU0, hd⟩ := hp'
    have hU0' : ∀ C, U0 = some C → CaptureSet.noAny C = true := by
      intro C hC
      subst hC
      exact hU0
    rw [elabF.eq_def]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · dsimp only
      have hn : ∀ G', GoalNoAny G' →
          Always OutNoAny (objNoneF Γ U0 G' (formSelfF Γ U0 d (jobsF d))
            fun S' done => fillDefsF (probeCtx Γ S' U0) done d S') := fun G' hG' =>
        objNoneF_noAny hΓ hU0' hG' (formSelfF_noAny hΓ hU0' hd (jobsF_noAny d hd))
          fun S' done hS' hdone =>
            fillDefsF_noAny (probeCtx_noAny hΓ hS' hU0') done hdone d hd S' hS'
      cases G with
      | none => exact hn none hG
      | some T =>
        refine always_bind (selfGoalF_noAny hΓ (hG T rfl)) fun oS hoS => ?_
        cases oS with
        | some S =>
          have hS := hoS S rfl
          exact orElseW_always (objSelfF_noAny hΓ hS hU0' hG
            (elabDefsF_noAny (probeCtx_noAny hΓ hS hU0') d hd S hS)) (hn _ hG)
        | none => exact hn _ hG
  | .let tag ann t u, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hp'
    obtain ⟨⟨hann, ht⟩, hu⟩ := hp'
    have hann' : GoalNoAny ann := by
      intro A hA
      subst hA
      exact hann
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact letF_noAny hΓ tag ann hu hG (fun F hF => elabF_noAny hΓ t ht _ (goalNoAny_some hF))
        (letO_noAny hΓ hann' hG (elabF_noAny hΓ t ht none goalNoAny_none)
          fun r1 h1 o ho => elabF_noAny (hΓ.cons h1.2.2) u hu o ho)
  | .asc t T, hp, G, hG => by
    have hp' := hp
    simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hp'
    rw [elabF]
    split
    · rename_i a ha
      exact fullInfer_noAny hΓ (PTm.NoAnyAnn_of_full? ha hp) hG
    · exact ascO_noAny hp'.2 hG (elabF_noAny hΓ t hp'.1 _ (goalNoAny_some hp'.2))

/-- The definitions the elaborator fills against a shape that holds no `any`
hold none. -/
theorem elabDefsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) :
    (d : PDefs s) → d.NoAnyAnn = true → (S : Shape s) → S.noAny = true →
      Always (fun r : Option (ADefs s) × List EReason =>
        OptP (fun e : ADefs s => e.NoAnyAnn = true) r.1) (elabDefsF Γ d S)
  | .typ A S0, hd, S, _ => by
    rw [elabDefsF]
    exact always_ret (optP_some hd)
  | .cap C c, hd, S, _ => by
    rw [elabDefsF]
    exact always_ret (optP_some hd)
  | .trm a o t, hd, S, hS => by
    have ht : t.NoAnyAnn = true := by
      simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
      exact hd.2
    cases S with
    | fld c T =>
      have hT : T.noAny = true := by simpa only [Shape.noAny] using hS
      rw [elabDefsF]
      refine always_ite ?_ (always_ret (optP_none _))
      split
      · rename_i b hb
        exact always_ret (optP_some (PTm.NoAnyAnn_of_full? hb ht))
      · refine always_bind (elabF_noAny hΓ t ht _ (goalNoAny_some hT)) fun r hr => ?_
        refine always_ret (optP_map (Q := Elab.NoAny) ?_ fun c hc => hc.1)
        intro c hc
        cases hl : r.1 with
        | nil => rw [hl] at hc; cases hc
        | cons c' _ =>
          rw [hl] at hc
          cases hc
          exact hr _ (by rw [hl]; exact List.mem_cons_self ..)
    | _ => simp only [elabDefsF]; exact always_ret (optP_none _)
  | .and d1 d2, hd, S, hS => by
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    cases S with
    | and S1 S2 =>
      simp only [Shape.noAny, Bool.and_eq_true] at hS
      rw [elabDefsF]
      refine always_bind (elabDefsF_noAny hΓ d1 hd.1 S1 hS.1) fun r1 h1 => ?_
      split
      · rename_i e1 he1
        refine always_bind (elabDefsF_noAny hΓ d2 hd.2 S2 hS.2) fun r2 h2 => ?_
        refine always_ret (optP_map h2 fun e2 he2 => ?_)
        simp only [ADefs.NoAnyAnn, h1 e1 he1, he2, Bool.and_self]
      · exact always_ret (optP_none _)
    | _ => simp only [elabDefsF]; exact always_ret (optP_none _)

/-- The jobs of a definition list that holds no `any` write none. -/
theorem jobsF_noAny {s : Sig} : (d : PDefs s) → d.NoAnyAnn = true → ∀ j ∈ jobsF d, j.NoAny
  | .typ _ _, _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .cap _ _, _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm _ (some _) _, _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm a none t, hd => by
    intro j hj Δ hΔ
    simp only [jobsF, List.mem_singleton] at hj
    subst hj
    have ht : t.NoAnyAnn = true := by simpa only [PDefs.NoAnyAnn, Bool.true_and] using hd
    exact elabF_noAny hΔ t ht none goalNoAny_none
  | .and d1 d2, hd => by
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    intro j hj
    simp only [jobsF, List.mem_append] at hj
    rcases hj with h | h
    · exact jobsF_noAny d1 hd.1 j h
    · exact jobsF_noAny d2 hd.2 j h

/-- The definitions filled at a formed self shape that holds no `any`, from
typed jobs that hold none, hold none. -/
theorem fillDefsF_noAny {s : Sig} {Γ : Ctx s} (hΓ : CtxNoAny Γ) (done : List (Done s))
    (hdone : AllL Done.NoAny done) :
    (d : PDefs s) → d.NoAnyAnn = true → (S : Shape s) → S.noAny = true →
      Always (fun r : Option (ADefs s) × List EReason =>
        OptP (fun e : ADefs s => e.NoAnyAnn = true) r.1) (fillDefsF Γ done d S)
  | .typ A S0, hd, S, _ => by
    rw [fillDefsF]
    exact always_ret (optP_some hd)
  | .cap C c, hd, S, _ => by
    rw [fillDefsF]
    exact always_ret (optP_some hd)
  | .trm a none t, _, S, _ => by
    rw [fillDefsF]
    split
    · rename_i e he
      exact always_ret (optP_some (hdone e (lookupDone_mem he)).1)
    · exact always_ret (optP_none _)
  | .trm a (some T) t, hd, S, hS => by
    have ht : t.NoAnyAnn = true := by
      simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
      exact hd.2
    cases S with
    | fld c W =>
      have hW : W.noAny = true := by simpa only [Shape.noAny] using hS
      rw [fillDefsF]
      refine always_ite ?_ (always_ret (optP_none _))
      split
      · rename_i b hb
        exact always_ret (optP_some (PTm.NoAnyAnn_of_full? hb ht))
      · refine always_bind (elabF_noAny hΓ t ht _ (goalNoAny_some hW)) fun r hr => ?_
        refine always_ret (optP_map (Q := Elab.NoAny) ?_ fun c hc => hc.1)
        intro c hc
        cases hl : r.1 with
        | nil => rw [hl] at hc; cases hc
        | cons c' _ =>
          rw [hl] at hc
          cases hc
          exact hr _ (by rw [hl]; exact List.mem_cons_self ..)
    | _ => simp only [fillDefsF]; exact always_ret (optP_none _)
  | .and d1 d2, hd, S, hS => by
    simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hd
    cases S with
    | and S1 S2 =>
      simp only [Shape.noAny, Bool.and_eq_true] at hS
      rw [fillDefsF]
      refine always_bind (fillDefsF_noAny hΓ done hdone d1 hd.1 S1 hS.1) fun r1 h1 => ?_
      split
      · rename_i e1 he1
        refine always_bind (fillDefsF_noAny hΓ done hdone d2 hd.2 S2 hS.2) fun r2 h2 => ?_
        refine always_ret (optP_map h2 fun e2 he2 => ?_)
        simp only [ADefs.NoAnyAnn, h1 e1 he1, he2, Bool.and_self]
      · exact always_ret (optP_none _)
    | _ => simp only [fillDefsF]; exact always_ret (optP_none _)

end

/-- No candidate of the elaborator holds `any` in an annotation, a set or a
type definition, when the partial term, the goal and the context hold none. -/
theorem elab_noAny {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Option (Ty s)} {t : Tank}
    {c : Elab Γ} {cs : List (Elab Γ)} (h : (elabF Γ p G t).1.1 = c :: cs)
    (hp : p.NoAnyAnn = true) (hΓ : CtxNoAny Γ) (hG : GoalNoAny G) : c.tm.NoAnyAnn = true :=
  (elabF_noAny hΓ p hp G hG t c (by rw [h]; exact List.mem_cons_self ..)).1

/-- The elaborated program holds no `any` when the resolved program holds
none. -/
theorem elabTop_noAny {n : Nat} {π : PlatformNames} {p : PTm π.sig}
    {c : Elab (platformCtx π.plat)} (h : (elabTopF n π p).1 = .ok c) (hp : p.NoAnyAnn = true) :
    c.tm.NoAnyAnn = true := by
  unfold elabTopF at h
  have hall := elabF_noAny (CtxNoAny.platform π.plat) p hp none goalNoAny_none ⟨n, false⟩
  revert hall h
  cases elabF (platformCtx π.plat) p none ⟨n, false⟩ with
  | mk r t =>
    obtain ⟨l, rs⟩ := r
    cases l with
    | nil => intro h; cases h
    | cons c' cs =>
      intro h hall
      dsimp only at h
      split at h
      · cases h
      · cases h
        exact (hall c (List.mem_cons_self ..)).1

end ElabNoAny

/-! ## A literal without a self shape is the typer's literal

Every candidate of a literal without a self shape is a candidate the typer
gives a literal with every slot filled, with the same set and goal.  So its
derivation is the one the typer's object clause gives, which ends in
`HasTy.obj` before the subtyping goal moves it to the goal. -/

/-- Every candidate of a list is a candidate `inferF` gives a literal with set
`U0` at the goal `G`, its self shape and definitions filled, from some
tank. -/
def InferObj {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (G : Option (Ty s))
    (cs : List (Elab Γ)) : Prop :=
  ∀ c ∈ cs, ∃ S d' tk', c ∈ (inferF Γ (.obj S U0 d') G tk').1

theorem objSelfF_inferF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (U0 : Option (CaptureSet s))
    (G : Option (Ty s)) (defs : Fu (Option (ADefs (s,x)) × List EReason)) :
    Always (fun r : Out Γ => ∀ c ∈ r.1, ∃ d' tk', c ∈ (inferF Γ (.obj S U0 d') G tk').1)
      (objSelfF Γ S U0 G defs) := by
  refine always_bind (always_true defs) fun r _ => ?_
  dsimp only
  split
  · rename_i d' _
    intro t c hc
    simp only [fullInfer, withR, Fu.bind, Fu.ret] at hc
    exact ⟨d', t, hc⟩
  · exact always_ret fun c hc => nomatch hc

theorem objSelfF_inferObj {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (U0 : Option (CaptureSet s))
    (G : Option (Ty s)) (defs : Fu (Option (ADefs (s,x)) × List EReason)) :
    Always (fun r : Out Γ => InferObj Γ U0 G r.1) (objSelfF Γ S U0 G defs) := fun t c hc =>
  let ⟨d', tk', h⟩ := objSelfF_inferF Γ S U0 G defs t c hc
  ⟨S, d', tk', h⟩

theorem objNoneF_inferObj {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (G : Option (Ty s))
    (form : Fu (Except (List EReason) (Shape (s,x) × List (Done (s,x)))))
    (fill : Shape (s,x) → List (Done (s,x)) → Fu (Option (ADefs (s,x)) × List EReason)) :
    Always (fun r : Out Γ => InferObj Γ U0 G r.1) (objNoneF Γ U0 G form fill) := by
  refine always_bind (always_true form) fun r _ => ?_
  cases r with
  | ok p => exact objSelfF_inferObj _ _ _ _ _
  | error _ => exact always_ret fun c hc => nomatch hc

/-- The elaboration of a literal without a self shape, unfolded. -/
theorem elabF_obj_none {s : Sig} (Γ : Ctx s) (U0 : Option (CaptureSet s)) (d : PDefs (s,x))
    (G : Option (Ty s)) :
    elabF Γ (.obj none U0 d) G =
      match G with
      | some T =>
          Fu.bind (selfGoalF Γ T) fun oS =>
            match oS with
            | some S =>
                orElseW (fun cs => !cs.isEmpty)
                  (objSelfF Γ S U0 G (elabDefsF (probeCtx Γ S U0) d S))
                  (fun _ => objNoneF Γ U0 G (formSelfF Γ U0 d (jobsF d))
                    fun S' done => fillDefsF (probeCtx Γ S' U0) done d S')
            | none =>
                objNoneF Γ U0 G (formSelfF Γ U0 d (jobsF d))
                  fun S' done => fillDefsF (probeCtx Γ S' U0) done d S'
      | none =>
          objNoneF Γ U0 none (formSelfF Γ U0 d (jobsF d))
            fun S done => fillDefsF (probeCtx Γ S U0) done d S := by
  rw [elabF.eq_def]
  rfl

/-- A candidate of a literal without a self shape is a candidate of the typer
on a literal with every slot filled, with the same set and the same goal:
the literal at the self shape its `μ` goal gives, or at the one the rounds
form. -/
theorem obj_none_landed {s : Sig} {Γ : Ctx s} {U0 : Option (CaptureSet s)} {d : PDefs (s,x)}
    {G : Option (Ty s)} {tk : Tank} {c : Elab Γ} {cs : List (Elab Γ)}
    (h : (elabF Γ (.obj none U0 d) G tk).1.1 = c :: cs) :
    ∃ S d' tk', c ∈ (inferF Γ (.obj S U0 d') G tk').1 := by
  have hall : Always (fun r : Out Γ => InferObj Γ U0 G r.1) (elabF Γ (.obj none U0 d) G) := by
    rw [elabF_obj_none]
    cases G with
    | none => exact objNoneF_inferObj _ _ _ _ _
    | some T =>
      refine always_bind (always_true _) fun oS _ => ?_
      cases oS with
      | some S =>
        exact orElseW_always (objSelfF_inferObj _ _ _ _ _) (objNoneF_inferObj _ _ _ _ _)
      | none => exact objNoneF_inferObj _ _ _ _ _
  exact hall tk c (by rw [h]; exact List.mem_cons_self ..)

/-- With no goal, the self shape is the one the rounds form from the tank the
elaboration starts with, and a candidate is a candidate of the typer on the
literal at that shape, its definitions filled. -/
theorem obj_none_formed {s : Sig} {Γ : Ctx s} {U0 : Option (CaptureSet s)} {d : PDefs (s,x)}
    {tk : Tank} {c : Elab Γ} {cs : List (Elab Γ)}
    (h : (elabF Γ (.obj none U0 d) none tk).1.1 = c :: cs) :
    ∃ S done d' tk', (formSelfF Γ U0 d (jobsF d) tk).1 = .ok (S, done) ∧
      c ∈ (inferF Γ (.obj S U0 d') none tk').1 := by
  rw [elabF_obj_none] at h
  dsimp only [objNoneF, Fu.bind] at h
  cases hf : formSelfF Γ U0 d (jobsF d) tk with
  | mk r tk1 =>
    rw [hf] at h
    cases r with
    | error rs => simp [Fu.ret] at h
    | ok p =>
      obtain ⟨S, done⟩ := p
      obtain ⟨d', tk', hc⟩ :=
        objSelfF_inferF Γ S U0 none (fillDefsF (probeCtx Γ S U0) done d S) tk1 c
          (by dsimp only at h; rw [h]; exact List.mem_cons_self ..)
      exact ⟨S, done, d', tk', rfl, hc⟩

/-! ## Checks

Each check elaborates a surface program at `defaultFuel` in the kernel, over
the empty platform or over `πc`.  It states the elaborated term, its use set
and its type, or the reason, and the tank left.  A program with an empty slot
that compiles is compared with the program that writes the slot: the
elaborated term, use set and type are the ones the typer gives that program.
An unmarked tank means the fuel played no part in the verdict. -/

section ElabChecks

/-- The outcome of a closed elaboration: the elaborated term, its use set and
its type, or the reason. -/
inductive Outcome (s : Sig) where
  /-- The elaborated term, its use set and its type. -/
  | ok (a : ATm s) (U : CaptureSet s) (T : Ty s)
  /-- The reason the program is rejected. -/
  | no (r : EReason)
deriving DecidableEq

/-- The outcome has a type. -/
def Outcome.isOk {s : Sig} : Outcome s → Bool
  | .ok _ _ _ => true
  | .no _ => false

/-- The outcome of a surface program over a platform, resolved and
elaborated, with the tank left. -/
def elabOut (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolvePTop Λc π e with
  | some p =>
      match elabTopF n π p with
      | (.ok c, t) => (.ok c.tm c.uses c.ty, t)
      | (.error r, t) => (.no r, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- What the typer gives a surface program with every slot written: its
first candidate's term, use set and type. -/
def writtenOut (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolveTop Λc π e with
  | some a =>
      match synthTopF n π a with
      | (some c, t) => (.ok c.tm c.uses c.ty, t)
      | (none, t) => (.no .mismatch, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- C2 with the client ascribed, every lambda domain erased.  The ascription
gives the client's domains, and the self shapes give the fields theirs. -/
def C2ascSrcD : STm :=
  cap% let c = (λx. λu. x.run u
                : ∀(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2})
                    (∀(u : ⊤) ⊤) ^ {k1, k2}) in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λu. u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λu. u}) in
      let ga = c a in let gb = c b in gb

/-- An ascription at two function sides of one domain. -/
def X2cSrc : STm := cap% (λ(x : {a : ⊤}). x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤))

/-- The same with the domain erased.  The sides meet at the domain `{a : ⊤}`. -/
def X2cSrcD : STm := cap% (λx. x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤))

/-- An ascription whose second side is a selection with a function lower
bound.  The written lambda is below it through the lower bound. -/
def X3cSrc : STm :=
  cap% λ(y : {A : (∀(x : {a : ⊤}) {a : ⊤}) .. ⊤}). (λ(x : {a : ⊤}). x : (∀(x : {a : ⊤}) ⊤) ∧ y.A)

/-- The same with the inner domain erased.  The selection's upper bound has
no function part, so the domain is the first side's. -/
def X3cSrcD : STm :=
  cap% λ(y : {A : (∀(x : {a : ⊤}) {a : ⊤}) .. ⊤}). (λx. x : (∀(x : {a : ⊤}) ⊤) ∧ y.A)

/-- Two function sides with comparable domains, the larger one written. -/
def AndTwoSrc : STm := cap% (λ(y : ⊤). y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤))

/-- The same with the domain erased.  The domain is the larger one, `⊤`. -/
def AndTwoSrcD : STm := cap% (λy. y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤))

/-- Two function sides with comparable domains, whose first result the
identity at the larger domain does not meet. -/
def AndResSrc : STm := cap% (λ(x : ⊤). x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : ⊤) ⊤))

/-- The same with the domain erased. -/
def AndResSrcD : STm := cap% (λx. x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : ⊤) ⊤))

/-- Two function sides with incomparable domains. -/
def AndIncSrcD : STm := cap% (λy. y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤))

/-- One function side and a field the lambda does not have. -/
def AndOneSrcD : STm := cap% (λy. y : (∀(x : ⊤) ⊤) ∧ {a : ⊤})

/-- One function side and `⊤`. -/
def AndTopSrc : STm := cap% (λ(y : ⊤). y : (∀(x : ⊤) ⊤) ∧ ⊤)

/-- The same with the domain erased. -/
def AndTopSrcD : STm := cap% (λy. y : (∀(x : ⊤) ⊤) ∧ ⊤)

/-- The ascription `(λ(x : ⊤). x : ∀(x : ⊤) ⊤)`. -/
def AscSrc : STm := cap% (λ(x : ⊤). x : ∀(x : ⊤) ⊤)

/-- The same with the domain erased. -/
def AscSrcD : STm := cap% (λx. x : ∀(x : ⊤) ⊤)

/-- An alias of a function type as the goal. -/
def AliasSrc : STm := cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). (λ(x : ⊤). x : y.A)

/-- The same with the domain erased.  The alias is followed. -/
def AliasSrcD : STm := cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). (λx. x : y.A)

/-- An alias of an alias of a function type as the goal. -/
def Alias2Src : STm :=
  cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(z : {B : y.A .. y.A}). (λ(x : ⊤). x : z.B)

/-- The same with the domain erased.  Both aliases are followed. -/
def Alias2SrcD : STm :=
  cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(z : {B : y.A .. y.A}). (λx. x : z.B)

/-- An abstract type with a function upper bound as the goal. -/
def UpperSrcD : STm := cap% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). (λx. x : y.A)

/-- An abstract type with a function lower bound only. -/
def LowerSrcD : STm := cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). (λx. x : y.A)

/-- A type member whose bounds are itself, reached through the self of its
binder.  Following it comes back to the same selection. -/
def LoopSrc : STm := cap% λ(y : μ(w. {A : w.A .. w.A})). (λ(x : ⊤). x : y.A)

/-- The same with the domain erased. -/
def LoopSrcD : STm := cap% λ(y : μ(w. {A : w.A .. w.A})). (λx. x : y.A)

/-- A lambda bound with no type. -/
def Id0SrcD : STm := cap% let i = λx. x in i

/-- A lambda ascribed at `⊤`. -/
def IdTopSrcD : STm := cap% (λx. x : ⊤)

/-- E11 with every domain erased. -/
def E11srcD : STm := cap% let i = λx. x in (λf. λg. f (g f)) i i

/-- A lambda bound by a written `let` and then passed: no call argument. -/
def LetArgSrcD : STm := cap% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λx. x in g i

/-- A curried lambda ascribed at a curried function type. -/
def CurrySrc : STm := cap% (λ(x : ⊤). λ(y : ⊤). x : ∀(x : ⊤) ∀(y : ⊤) ⊤)

/-- The same with both domains erased.  The inner lambda takes its domain
from the codomain of the outer goal. -/
def CurrySrcD : STm := cap% (λx. λy. x : ∀(x : ⊤) ∀(y : ⊤) ⊤)

/-- A curried lambda ascribed at an intersection with a curried side. -/
def SideCurrySrc : STm := cap% (λ(x : ⊤). λ(y : ⊤). y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- The same with both domains erased.  The inner lambda takes its domain
from the result part of the side. -/
def SideCurrySrcD : STm := cap% (λx. λy. y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- The same with the outer domain written and the inner one erased. -/
def SideCurrySrcW : STm := cap% (λ(x : ⊤). λy. y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- A lambda as the body of a `let` with a written type. -/
def LetBodySrc : STm := cap% λ(w : ⊤). let k : ∀(x : ⊤) ⊤ = w in λ(x : ⊤). x

/-- The same with the inner domain erased.  The written type is the goal of
the body. -/
def LetBodySrcD : STm := cap% λ(w : ⊤). let k : ∀(x : ⊤) ⊤ = w in λx. x

/-- A block ascribed at a function type. -/
def BlockSrc : STm := cap% (let k = λ(y : ⊤). y in λ(x : ⊤). x : ∀(x : ⊤) ⊤)

/-- The same with the domain of the block's result erased.  The block passes
its goal to its body. -/
def BlockSrcD : STm := cap% (let k = λ(y : ⊤). y in λx. x : ∀(x : ⊤) ⊤)

/-- A closure over a capability ascribed at a function type that captures it. -/
def CapSrc : STm := cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λ(x : ⊤). f x : (∀(x : ⊤) ⊤) ^ {f})

/-- The same with the domain erased. -/
def CapSrcD : STm := cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λx. f x : (∀(x : ⊤) ⊤) ^ {f})

/-- The closure ascribed at a pure function type, which does not admit it. -/
def CapPureSrc : STm := cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λ(x : ⊤). f x : ∀(x : ⊤) ⊤)

/-- The same with the domain erased. -/
def CapPureSrcD : STm := cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λx. f x : ∀(x : ⊤) ⊤)

/-- A field closure of a literal with a written self shape. -/
def FldSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = λ(u : ⊤). f u})

/-- The same with the domain erased.  The self shape gives it. -/
def FldSrcD : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = λu. f u})

/-- A literal with a written self shape and a field without its type. -/
def FldTySrc : STm := cap% ν(z : {a : ∀(u : ⊤) ⊤}. {a = λ(u : ⊤). u})

/-- A field type written under a written self shape, equal to the shape's. -/
def FldTySrcD : STm := cap% ν(z : {a : ∀(u : ⊤) ⊤}. {a : ∀(u : ⊤) ⊤ = λu. u})

/-- A field type written under a written self shape, other than the shape's. -/
def FldTyBadSrc : STm := cap% ν(z : {a : ∀(u : ⊤) ⊤}. {a : ⊤ = λu. u})

/-- A literal ascribed at a `μ`, its self shape written. -/
def AscObjSrc : STm := cap% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self shape erased.  The `μ` goal gives it. -/
def AscObjSrcS : STm := cap% λ(n : {b : ⊤}). (ν(z. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- A literal whose field is below the goal's field, its self shape written. -/
def AscWideSrc : STm :=
  cap% λ(y : {b : ⊤} ∧ {elem : ⊤}). (ν(z : {a : {b : ⊤}}. {a = y}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self shape erased.  The `μ` goal gives the goal's field
type, not the field's own. -/
def AscWideSrcS : STm :=
  cap% λ(y : {b : ⊤} ∧ {elem : ⊤}). (ν(z. {a = y}) : μ(z. {a : {b : ⊤}}))

/-- A literal nested in a field of a written self shape. -/
def NestSrc : STm :=
  cap% λ(y : {b : ⊤} ∧ {elem : ⊤}).
        ν(o : {a : μ(z. {b : {b : ⊤}})}. {a = ν(z : {b : {b : ⊤}}. {b = y})})

/-- The same with the inner self shape erased.  The field's type is a `μ`
goal. -/
def NestSrcS : STm :=
  cap% λ(y : {b : ⊤} ∧ {elem : ⊤}). ν(o : {a : μ(z. {b : {b : ⊤}})}. {a = ν(z. {b = y})})

/-- A literal without a self shape and with no goal. -/
def NoShapeSrcS : STm := cap% ν(z. {a = λ(u : ⊤). u})

-- The erased programs are the written ones with those slots erased.
example : (resolvePTop Λc πc C2ascSrc).map PTm.eraseDoms = resolvePTop Λc πc C2ascSrcD := by
  decide
example : (resolvePTop Λc .empty X2cSrc).map PTm.eraseAsc = resolvePTop Λc .empty X2cSrcD := by
  decide
example : (resolvePTop Λc .empty X3cSrc).map PTm.eraseAsc = resolvePTop Λc .empty X3cSrcD := by
  decide
example : (resolvePTop Λc .empty AndTwoSrc).map PTm.eraseAsc =
    resolvePTop Λc .empty AndTwoSrcD := by
  decide
example : (resolvePTop Λc .empty AliasSrc).map PTm.eraseAsc = resolvePTop Λc .empty AliasSrcD := by
  decide
example : (resolvePTop Λc .empty CurrySrc).map PTm.eraseDoms = resolvePTop Λc .empty CurrySrcD := by
  decide
example : (resolvePTop Λc .empty E11src).map PTm.eraseDoms = resolvePTop Λc .empty E11srcD := by
  decide
example : (resolvePTop Λc .empty AscObjSrc).map PTm.eraseSelf =
    resolvePTop Λc .empty AscObjSrcS := by
  decide

-- Every slot written: the typer's verdict, term, use set, type and tank.
example : elabOut .empty E2src = writtenOut .empty E2src := by decide +kernel
example : elabOut .empty E11src = writtenOut .empty E11src := by decide +kernel
example : elabOut πc C2ascSrc = writtenOut πc C2ascSrc := by decide +kernel

-- Domains of fields from written self shapes.
example : elabOut .empty E2srcD = ((writtenOut .empty E2src).1, ⟨defaultFuel - 69, false⟩) ∧
    writtenOut .empty E2src = ((writtenOut .empty E2src).1, ⟨defaultFuel - 64, false⟩) ∧
    (writtenOut .empty E2src).1.isOk = true := by
  decide +kernel
example : elabOut πc C2ascSrcD = ((writtenOut πc C2ascSrc).1, ⟨defaultFuel - 187, false⟩) ∧
    writtenOut πc C2ascSrc = ((writtenOut πc C2ascSrc).1, ⟨defaultFuel - 177, false⟩) ∧
    (writtenOut πc C2ascSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc FldSrcD = ((writtenOut πc FldSrc).1, ⟨defaultFuel - 14, false⟩) ∧
    (writtenOut πc FldSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty FldTySrcD = ((writtenOut .empty FldTySrc).1, ⟨defaultFuel - 11, false⟩) ∧
    (writtenOut .empty FldTySrc).1.isOk = true := by
  decide +kernel

-- Domains from ascriptions, written `let` types and blocks.
example : elabOut .empty X2cSrcD = ((writtenOut .empty X2cSrc).1, ⟨defaultFuel - 19, false⟩) ∧
    (writtenOut .empty X2cSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty X3cSrcD = ((writtenOut .empty X3cSrc).1, ⟨defaultFuel - 25, false⟩) ∧
    (writtenOut .empty X3cSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AndTwoSrcD =
      ((writtenOut .empty AndTwoSrc).1, ⟨defaultFuel - 23, false⟩) ∧
    (writtenOut .empty AndTwoSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AndTopSrcD = ((writtenOut .empty AndTopSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenOut .empty AndTopSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AscSrcD = ((writtenOut .empty AscSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut .empty AscSrc).1 =
      .ok (.asc (.lam (.top ^ []) (.path (.var .here))) ((Shape.all (.top ^ []) (.top ^ [])) ^ []))
        [] ((Shape.all (.top ^ []) (.top ^ [])) ^ []) := by
  decide +kernel
example : elabOut .empty AliasSrcD = ((writtenOut .empty AliasSrc).1, ⟨defaultFuel - 8, false⟩) ∧
    (writtenOut .empty AliasSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty Alias2SrcD =
      ((writtenOut .empty Alias2Src).1, ⟨defaultFuel - 14, false⟩) ∧
    (writtenOut .empty Alias2Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty CurrySrcD = ((writtenOut .empty CurrySrc).1, ⟨defaultFuel - 8, false⟩) ∧
    (writtenOut .empty CurrySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty SideCurrySrcD =
      ((writtenOut .empty SideCurrySrc).1, ⟨defaultFuel - 12, false⟩) ∧
    elabOut .empty SideCurrySrcW =
      ((writtenOut .empty SideCurrySrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty SideCurrySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty LetBodySrcD =
      ((writtenOut .empty LetBodySrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty LetBodySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BlockSrcD = ((writtenOut .empty BlockSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty BlockSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc CapSrcD = ((writtenOut πc CapSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenOut πc CapSrc).1.isOk = true := by
  decide +kernel

-- Literals without a self shape at a `μ` goal.
example : elabOut .empty AscObjSrcS =
      ((writtenOut .empty AscObjSrc).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut .empty AscObjSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AscWideSrcS =
      ((writtenOut .empty AscWideSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty AscWideSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty NestSrcS = ((writtenOut .empty NestSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty NestSrc).1.isOk = true := by
  decide +kernel

-- Missing parameter type: no goal, a goal with no function part, a lambda
-- bound by a written `let`, an alias that comes back to itself.
example : elabOut .empty Id0SrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty IdTopSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty E11srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty E8srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty LetArgSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty LowerSrcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabOut .empty LoopSrcD = (.no (.missingParamType none), ⟨defaultFuel - 3, false⟩) ∧
    writtenOut .empty LoopSrc = (.no .mismatch, ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

-- Mismatch: incomparable domains, one function side the lambda does not meet,
-- a result the lambda does not meet, an abstract type with a function upper
-- bound, a closure too large for its goal, a written field type other than
-- the self shape's.
example : elabOut .empty AndIncSrcD = (.no .mismatch, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel
example : elabOut .empty AndOneSrcD = (.no .mismatch, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabOut .empty AndResSrcD = (.no .mismatch, ⟨defaultFuel - 21, false⟩) ∧
    writtenOut .empty AndResSrc = (.no .mismatch, ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : elabOut .empty UpperSrcD = (.no .mismatch, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabOut πc CapPureSrcD = (.no .mismatch, ⟨defaultFuel - 13, false⟩) ∧
    writtenOut πc CapPureSrc = (.no .mismatch, ⟨defaultFuel - 13, false⟩) := by
  decide +kernel
example : elabOut .empty FldTyBadSrc = (.no .mismatch, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Call arguments and callee bodies -/

/-- E11 with the identity passed directly, twice. -/
def E11aSrc : STm :=
  cap% (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) (λ(x : ⊤). x) (λ(x : ⊤). x)

/-- The same with both argument domains erased.  Each takes the formal of its
callee. -/
def E11aSrcA : STm := cap% (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) (λx. x) (λx. x)

/-- A callee whose formal has a capturing domain, applied to a lambda. -/
def Run1Src : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let run = λ(op : ∀(g : (∀(u : ⊤) ⊤) ^ {k1}) ⊤ ^ {g}). op f1 in
        run (λ(g : (∀(u : ⊤) ⊤) ^ {k1}). g)

/-- The same with the argument's domain erased.  It takes the formal's domain
with its set `{k1}`. -/
def Run1SrcA : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let run = λ(op : ∀(g : (∀(u : ⊤) ⊤) ^ {k1}) ⊤ ^ {g}). op f1 in
        run (λg. g)

/-- A callee whose formal is pure, applied to a closure over `f1`. -/
def TooBigSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). let k = λ(h : ∀(u : ⊤) ⊤). h in k (λ(u : ⊤). f1 u)

/-- The same with the argument's domain erased. -/
def TooBigSrcA : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). let k = λ(h : ∀(u : ⊤) ⊤). h in k (λu. f1 u)

/-- The same callee at the set `{k1}`, which admits the closure. -/
def FitsSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let k = λ(h : (∀(u : ⊤) ⊤) ^ {k1}). h in k (λ(u : ⊤). f1 u)

/-- The same with the argument's domain erased.  The closure keeps its own
set `{f1}`. -/
def FitsSrcA : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). let k = λ(h : (∀(u : ⊤) ⊤) ^ {k1}). h in k (λu. f1 u)

/-- A callee at two function types whose formals have one domain. -/
def SameDomSrc : STm :=
  cap% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λ(x : ⊤). x)

/-- The same with the argument's domain erased.  The first formal is the
dominant one. -/
def SameDomSrcA : STm :=
  cap% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λx. x)

/-- A callee at two function types whose formals have comparable domains. -/
def DomSrc : STm :=
  cap% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) ⊤) ⊤)). g (λ(x : {a : ⊤}). x)

/-- The same with the argument's domain erased.  The formal with the smaller
domain is the dominant one. -/
def DomSrcA : STm :=
  cap% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) ⊤) ⊤)). g (λx. x)

/-- The callee of `DomSrc` with its sides swapped. -/
def DomRevSrc : STm :=
  cap% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤)). g (λ(x : {a : ⊤}). x)

/-- The same with the argument's domain erased.  The dominant formal does not
depend on the order of the sides. -/
def DomRevSrcA : STm :=
  cap% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤)). g (λx. x)

/-- A callee whose formals have incomparable domains. -/
def IncSrcA : STm :=
  cap% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λx. x)

/-- A curried lambda argument. -/
def C13Src : STm := cap% λ(k : ∀(h : ∀(p : ⊤) ∀(q : ⊤) ⊤) ⊤). k (λ(p : ⊤). λ(q : ⊤). p)

/-- The same with both domains erased.  The whole formal is the goal, so the
inner lambda takes its domain from the formal's result. -/
def C13SrcA : STm := cap% λ(k : ∀(h : ∀(p : ⊤) ∀(q : ⊤) ⊤) ⊤). k (λp. λq. p)

/-- A callee reached through a box. -/
def C14Src : STm := cap% λ(g : □(∀(h : ∀(y : ⊤) ⊤) ⊤)). g (λ(y : ⊤). y)

/-- The same with the argument's domain erased.  The formal is the domain of
the boxed function type. -/
def C14SrcA : STm := cap% λ(g : □(∀(h : ∀(y : ⊤) ⊤) ⊤)). g (λy. y)

/-- A callee whose formal is boxed. -/
def BoxFSrc : STm := cap% λ(g : ∀(h : □(∀(y : ⊤) ⊤)) ⊤). g (λ(y : ⊤). y)

/-- The same with the argument's domain erased.  The goal is the formal with
its box stripped, and box inference boxes the argument. -/
def BoxFSrcA : STm := cap% λ(g : ∀(h : □(∀(y : ⊤) ⊤)) ⊤). g (λy. y)

/-- A formal that is an alias of a function type. -/
def AliasArgSrc : STm :=
  cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(g : ∀(h : y.A) ⊤). g (λ(x : ⊤). x)

/-- The same with the argument's domain erased.  The alias is followed. -/
def AliasArgSrcA : STm :=
  cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(g : ∀(h : y.A) ⊤). g (λx. x)

/-- A formal that is an abstract type with a function upper bound. -/
def UpperArgSrcA : STm := cap% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). λ(g : ∀(h : y.A) ⊤). g (λx. x)

/-- A formal that is an abstract type with a function lower bound only. -/
def LowerArgSrcA : STm := cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). λ(g : ∀(h : y.A) ⊤). g (λx. x)

/-- A callee with no function type. -/
def NoFnSrcA : STm := cap% λ(g : ⊤). g (λx. x)

/-- A block as a call argument. -/
def BlockArgSrc : STm := cap% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). g (let w = g in λ(x : ⊤). x)

/-- The same with the domain of the block's result erased.  The block passes
the formal to its body. -/
def BlockArgSrcA : STm := cap% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). g (let w = g in λx. x)

/-- A lambda that calls `g` on its parameter, bound by `let`. -/
def CalleeSrc : STm := cap% λ(g : ∀(x : ⊤) ⊤). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The callee gives it. -/
def CalleeSrcD : STm := cap% λ(g : ∀(x : ⊤) ⊤). let h = λx. g x in h

/-- A callee at two function types with comparable domains. -/
def CalleeAndSrc : STm :=
  cap% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The larger domain is the dominant
formal. -/
def CalleeAndSrcD : STm :=
  cap% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λx. g x in h

/-- A callee at two function types with incomparable domains. -/
def CalleeIncSrcD : STm :=
  cap% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤)). let h = λx. g x in h

/-- A callee with no function type. -/
def CalleeTopSrcD : STm := cap% λ(g : ⊤). let h = λx. g x in h

/-- A body that applies `g` to a variable other than the parameter. -/
def CalleeOtherSrcD : STm := cap% λ(g : ∀(x : ⊤) ⊤). λ(y : ⊤). let h = λx. g y in h

/-- A callee's body ascribed at a goal with no function part. -/
def CalleeTopGoalSrc : STm := cap% λ(g : ∀(x : {a : ⊤}) ⊤). (λ(x : {a : ⊤}). g x : ⊤)

/-- The same with the domain erased.  The goal has no function part, so the
callee gives the domain. -/
def CalleeTopGoalSrcD : STm := cap% λ(g : ∀(x : {a : ⊤}) ⊤). (λx. g x : ⊤)

/-- A callee's body as a call argument whose formal has no function part. -/
def CalleeArgSrc : STm := cap% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(y : ⊤) ⊤). f (λ(x : ⊤). g x)

/-- The same with the domain erased. -/
def CalleeArgSrcA : STm := cap% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(y : ⊤) ⊤). f (λx. g x)

/-- A callee's body whose callee is boxed. -/
def CalleeBoxSrc : STm := cap% λ(g : □(∀(x : ⊤) ⊤)). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased. -/
def CalleeBoxSrcD : STm := cap% λ(g : □(∀(x : ⊤) ⊤)). let h = λx. g x in h

/-- A callee's body over a capability. -/
def CalleeCapSrc : STm := cap% λ(g : (∀(x : ⊤) ⊤) ^ {k1}). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The closure keeps its least set `{g}`. -/
def CalleeCapSrcD : STm := cap% λ(g : (∀(x : ⊤) ⊤) ^ {k1}). let h = λx. g x in h

-- The erased call arguments are the written ones with the argument domains
-- erased.
example : (resolvePTop Λc .empty E11aSrc).map PTm.eraseArgs = resolvePTop Λc .empty E11aSrcA := by
  decide +kernel
example : (resolvePTop Λc πc Run1Src).map PTm.eraseArgs = resolvePTop Λc πc Run1SrcA := by
  decide +kernel
example : (resolvePTop Λc πc TooBigSrc).map PTm.eraseArgs = resolvePTop Λc πc TooBigSrcA := by
  decide +kernel
example : (resolvePTop Λc πc FitsSrc).map PTm.eraseArgs = resolvePTop Λc πc FitsSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty SameDomSrc).map PTm.eraseArgs =
    resolvePTop Λc .empty SameDomSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty DomSrc).map PTm.eraseArgs = resolvePTop Λc .empty DomSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty C14Src).map PTm.eraseArgs = resolvePTop Λc .empty C14SrcA := by
  decide +kernel
example : (resolvePTop Λc .empty AliasArgSrc).map PTm.eraseArgs =
    resolvePTop Λc .empty AliasArgSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty CalleeArgSrc).map PTm.eraseArgs =
    resolvePTop Λc .empty CalleeArgSrcA := by
  decide +kernel
-- A curried argument has its inner domain erased as well.
example : (resolvePTop Λc .empty C13Src).map PTm.eraseDoms =
    (resolvePTop Λc .empty C13SrcA).map PTm.eraseDoms := by
  decide +kernel

-- Call arguments that compile at the written term, use set and type.
example : elabOut .empty E11aSrcA = ((writtenOut .empty E11aSrc).1, ⟨defaultFuel - 35, false⟩) ∧
    writtenOut .empty E11aSrc = ((writtenOut .empty E11aSrc).1, ⟨defaultFuel - 23, false⟩) ∧
    (writtenOut .empty E11aSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc Run1SrcA = ((writtenOut πc Run1Src).1, ⟨defaultFuel - 36, false⟩) ∧
    writtenOut πc Run1Src = ((writtenOut πc Run1Src).1, ⟨defaultFuel - 28, false⟩) ∧
    (writtenOut πc Run1Src).1.isOk = true := by
  decide +kernel
example : elabOut πc FitsSrcA = ((writtenOut πc FitsSrc).1, ⟨defaultFuel - 27, false⟩) ∧
    writtenOut πc FitsSrc = ((writtenOut πc FitsSrc).1, ⟨defaultFuel - 18, false⟩) ∧
    (writtenOut πc FitsSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty SameDomSrcA =
      ((writtenOut .empty SameDomSrc).1, ⟨defaultFuel - 46, false⟩) ∧
    writtenOut .empty SameDomSrc = ((writtenOut .empty SameDomSrc).1, ⟨defaultFuel - 26, false⟩) ∧
    (writtenOut .empty SameDomSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty DomSrcA = ((writtenOut .empty DomSrc).1, ⟨defaultFuel - 56, false⟩) ∧
    (writtenOut .empty DomSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty DomRevSrcA =
      ((writtenOut .empty DomRevSrc).1, ⟨defaultFuel - 62, false⟩) ∧
    (writtenOut .empty DomRevSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty C13SrcA = ((writtenOut .empty C13Src).1, ⟨defaultFuel - 16, false⟩) ∧
    writtenOut .empty C13Src = ((writtenOut .empty C13Src).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenOut .empty C13Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty C14SrcA = ((writtenOut .empty C14Src).1, ⟨defaultFuel - 16, false⟩) ∧
    writtenOut .empty C14Src = ((writtenOut .empty C14Src).1, ⟨defaultFuel - 9, false⟩) ∧
    (writtenOut .empty C14Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty BoxFSrcA = ((writtenOut .empty BoxFSrc).1, ⟨defaultFuel - 21, false⟩) ∧
    (writtenOut .empty BoxFSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AliasArgSrcA =
      ((writtenOut .empty AliasArgSrc).1, ⟨defaultFuel - 18, false⟩) ∧
    (writtenOut .empty AliasArgSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BlockArgSrcA =
      ((writtenOut .empty BlockArgSrc).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenOut .empty BlockArgSrc).1.isOk = true := by
  decide +kernel

-- Callee bodies that compile at the written term, use set and type.
example : elabOut .empty CalleeSrcD = ((writtenOut .empty CalleeSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    writtenOut .empty CalleeSrc = ((writtenOut .empty CalleeSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty CalleeSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeAndSrcD =
      ((writtenOut .empty CalleeAndSrc).1, ⟨defaultFuel - 23, false⟩) ∧
    (writtenOut .empty CalleeAndSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeTopGoalSrcD =
      ((writtenOut .empty CalleeTopGoalSrc).1, ⟨defaultFuel - 8, false⟩) ∧
    (writtenOut .empty CalleeTopGoalSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeArgSrcA =
      ((writtenOut .empty CalleeArgSrc).1, ⟨defaultFuel - 20, false⟩) ∧
    (writtenOut .empty CalleeArgSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeBoxSrcD =
      ((writtenOut .empty CalleeBoxSrc).1, ⟨defaultFuel - 11, false⟩) ∧
    (writtenOut .empty CalleeBoxSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc CalleeCapSrcD = ((writtenOut πc CalleeCapSrc).1, ⟨defaultFuel - 9, false⟩) ∧
    (writtenOut πc CalleeCapSrc).1.isOk = true := by
  decide +kernel

-- Missing parameter type: incomparable formals, a formal with only a lower
-- bound, a callee with no function type, a body that is no call of the
-- parameter.
example : elabOut .empty IncSrcA = (.no (.missingParamType none), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : elabOut .empty LowerArgSrcA =
    (.no (.missingParamType none), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : elabOut .empty NoFnSrcA = (.no (.missingParamType none), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : elabOut .empty CalleeIncSrcD =
    (.no (.missingParamType none), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel
example : elabOut .empty CalleeTopSrcD =
    (.no (.missingParamType none), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : elabOut .empty CalleeOtherSrcD =
    (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Mismatch: a closure too large for a pure formal, written or erased, and a
-- formal that is an abstract type with a function upper bound.
example : elabOut πc TooBigSrcA = (.no .mismatch, ⟨defaultFuel - 30, false⟩) ∧
    writtenOut πc TooBigSrc = (.no .mismatch, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel
example : elabOut .empty UpperArgSrcA = (.no .mismatch, ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-! ### Self shapes formed from definitions

The rounds alone, on a literal without a self shape, then the self shape in
lockstep.  Each check compares the self shape `formSelfF` forms with the self
shape the written form of the program states, or gives the reason the rounds
stop. -/

/-- What `formSelfF` gives the first literal without a self shape of a
program. -/
inductive Formed where
  /-- A self shape formed, and whether it is the one the written form
  states. -/
  | self (written : Bool)
  /-- The reason the rounds stop. -/
  | no (r : EReason)
  /-- No such literal, or the written form is not the same program there. -/
  | shape
deriving DecidableEq

/-- The type the typer gives a bound term with no empty slot, on a tank of its
own: the type at which a `let` binds its variable. -/
def boundTy? {s : Sig} (Γ : Ctx s) (t : PTm s) : Option (Ty s) :=
  match t.full? with
  | some a => (inferF Γ a none ⟨defaultFuel, false⟩).1.head?.map (·.ty)
  | none => none

/-- `formSelfF` on the first literal without a self shape, found under written
lambdas, under ascriptions, and in `let`s, against the same place of the
written form.  A `let` whose bound term holds no such literal binds its
variable at the type the typer gives the written bound term. -/
def formGo {s : Sig} (Γ : Ctx s) (n : Nat) : PTm s → PTm s → Formed × Tank
  | .lam (some T) t, .lam (some T') t' =>
      if T = T' then formGo (Γ.cons T) n t t' else (.shape, ⟨n, true⟩)
  | .asc t _, .asc t' _ => formGo Γ n t t'
  | .let _ _ t u, .let _ _ t' u' =>
      match formGo Γ n t t' with
      | (.shape, _) =>
          match boundTy? Γ t' with
          | some T => formGo (Γ.cons T) n u u'
          | none => (.shape, ⟨n, true⟩)
      | r => r
  | .obj none U0 d, .obj o _ _ =>
      match formSelfF Γ U0 d (jobsF d) ⟨n, false⟩ with
      | (.ok (S, _), tk) => (.self (decide (o = some S)), tk)
      | (.error rs, tk) => (.no (Reason.top tk.out rs), tk)
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a surface program over a platform, against a written form,
with the tank left. -/
def formAt (π : PlatformNames) (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolvePTop Λc π e, resolvePTop Λc π w with
  | some p, some q => formGo (platformCtx π.plat) n p q
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a written program `e` with every self shape erased, against
a written form `w`. -/
def formSAt (π : PlatformNames) (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolvePTop Λc π e, resolvePTop Λc π w with
  | some p, some q => formGo (platformCtx π.plat) n p.eraseSelf q
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a written program with every self shape erased, against
the program itself. -/
def formS (π : PlatformNames) (w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  formSAt π w w n

/-- The jobs of a program that is a literal, or a literal under written
lambdas, with its self shape erased. -/
def jobsAt (π : PlatformNames) (e : STm) : List (Label × (List Label × Bool)) :=
  let rec go {s : Sig} : PTm s → List (Label × (List Label × Bool))
    | .lam _ t => go t
    | .obj none _ d => (jobsF d).map fun j => (j.lbl, j.deps)
    | _ => []
  match resolvePTop Λc π e with
  | some p => go p.eraseSelf
  | none => []

/-- A literal that holds `f` in a field that reads a later one. -/
def FwdSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : (∀(u : ⊤) ⊤) ^ {f}}. {a = z.b} ∧ {b = f})

/-- A field closure that projects another field off the self. -/
def SelfProjSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {b : (∀(u : ⊤) ⊤) ^ {f}} ∧ {a : (∀(u : ⊤) ⊤) ^ {z, f}}.
           {b = f} ∧ {a = λ(u : ⊤). let w = z.b in w u})

/-- E2's object alone. -/
def E2oSrc : STm :=
  cap% ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
          {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- A recursive field with its type written. -/
def RecSrc : STm := cap% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = z.a in w y})

/-- The same without a self shape and with the field type written. -/
def RecWSrcS : STm := cap% ν(z. {a : ∀(y : ⊤) ⊤ = λy. let w = z.a in w y})

/-- E5 with the self shape written at the type of the field's right-hand
side. -/
def E5srcW : STm :=
  cap% λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : {A : ⊤..⊤}}. {a = v}) in
         let o = f w in o.a

/-- E6 with the self shape written at the type of the field's right-hand
side. -/
def E6srcW : STm :=
  cap% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : {a : ⊤}}. {type T = {a : ⊤}} ∧ {v = n})

/-- Two fields that read each other. -/
def CycSrcS : STm := cap% ν(z. {a = z.b} ∧ {b = z.a})

/-- A recursive field without a written type. -/
def RecUSrcS : STm := cap% ν(z. {a = λ(y : ⊤). let w = z.a in w y})

/-- A field that reads a cycle between two later fields. -/
def Cyc3SrcS : STm := cap% ν(z. {a = z.b} ∧ {b = z.v} ∧ {v = z.b})

/-- A recursive field that reads itself through an alias of the self. -/
def AliasRecSrcS : STm := cap% ν(z. {a = λ(y : ⊤). let w = z in let u = w.a in u y})

/-- A field that is the self. -/
def SelfSrcS : STm := cap% ν(z. {a = z})

/-- The same with the self shape written at the snapshot the field is typed
at. -/
def SelfSrc : STm := cap% ν(z : {a : μ(y. ⊤)}. {a = z})

/-- A field that reads a later field that is the self. -/
def FwdSelfSrcS : STm := cap% ν(z. {a = z.b} ∧ {b = z})

/-- The same with the self shape written. -/
def FwdSelfSrc : STm := cap% ν(z : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = z.b} ∧ {b = z})

/-- A field that is the self, and a later one that reads it. -/
def BareProjSrcS : STm := cap% ν(z. {a = z} ∧ {b = z.a})

/-- The same with the self shape written. -/
def BareProjSrc : STm := cap% ν(z : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = z} ∧ {b = z.a})

/-- A field whose right-hand side has two incomparable types. -/
def AmbSrcS : STm := cap% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s. {a = y.a})

/-- A field whose right-hand side has two types, one below the other, and a
use of the field that needs the smaller one. -/
def AmbUseSrcS : STm :=
  cap% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let o = ν(s. {v = y.a}) in let w = o.v in w.b

/-- The same with the self shape written. -/
def AmbUseSrc : STm :=
  cap% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}).
        let o = ν(s : {v : {b : ⊤}}. {v = y.a}) in let w = o.v in w.b

/-- The same two types in the other order. -/
def AmbUse2SrcS : STm :=
  cap% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}). let o = ν(s. {v = y.a}) in let w = o.v in w.b

/-- The same with the self shape written. -/
def AmbUse2Src : STm :=
  cap% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}).
        let o = ν(s : {v : {b : ⊤}}. {v = y.a}) in let w = o.v in w.b

/-- A field that is a lambda without a domain and without a goal. -/
def NoDomSrcS : STm := cap% ν(z. {a = λy. y})


/-- impureIns with its self shape written at the types of the right-hand
sides: both fields hold `f` unboxed. -/
def impureInsSrcW : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : (∀(u : ⊤) ⊤) ^ {f}}. {a = f} ∧ {b = f})

/-- C7 with its self shape written at the types of the right-hand sides: each
box at the set of its capability. -/
def C7srcW : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {f1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {f2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

/-- C7nb with its self shape written at the types of the right-hand sides:
the capabilities unboxed. -/
def C7nbSrcW : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : (∀(u : ⊤) ⊤) ^ {f1}} ∧ {e2 : (∀(u : ⊤) ⊤) ^ {f2}}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- C7scala with its self shape written at the types of the right-hand
sides: the capabilities unboxed. -/
def C7scalaSrcW : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : (∀(u : ⊤) ⊤) ^ {f1}} ∧ {e2 : (∀(u : ⊤) ⊤) ^ {f2}}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u

/-- argUnbox with its self shape written at the type of the right-hand
side. -/
def argUnboxSrcW : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {e1 : (∀(u : ⊤) ⊤) ^ {f1}}. {e1 = f1}) in
        let e = o.e1 in
        let h = λ(k : (∀(u : ⊤) ⊤) ^ {k1}). k in h e

/-- recv with its self shape written at the type of the right-hand side. -/
def recvSrcW : STm :=
  cap% λ(p : {a : ⊤} ^ {k1}).
        let o = ν(z : {e1 : {a : ⊤} ^ {p}}. {e1 = p}) in
        let e = o.e1 in e.a

/-- S3nb with its self shape written at the types of the right-hand sides:
the field at the capability's type, where the written shape names the
member. -/
def S3nbSrcW : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : (∀(u : ⊤) ⊤) ^ {f} .. (∀(u : ⊤) ⊤) ^ {f}} ∧
                      {elem : (∀(u : ⊤) ⊤) ^ {f}}.
                   {type A = (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem = f})
        in let e = o.elem in (e : (∀(u : ⊤) ⊤) ^ {f})

/-- C2 with the self shape of its first literal written at the types of the
right-hand sides: the closure is pure, where the written shape gives it the
member's set. -/
def C2srcW : STm :=
  cap% let c = λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : ∀(u : ⊤) ⊤}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

-- The jobs of a field list: the fields without a written type, in source
-- order, with their dependencies.  A field with a written type is no job.  A
-- projection through an alias of the self depends on its label.  A bare use
-- sets the flag.
example : jobsAt πc FwdSrc = [(.trm 0, ([.trm 1], false)), (.trm 1, ([], false))] := by
  decide +kernel
example : jobsAt .empty RecWSrcS = [] := by decide +kernel
example : jobsAt .empty AliasRecSrcS = [(.trm 0, ([.trm 0], false))] := by decide +kernel
example : jobsAt .empty FwdSelfSrcS = [(.trm 0, ([.trm 1], false)), (.trm 1, ([], true))] := by
  decide +kernel

-- The written self shapes, formed: impure, accounted, a field that reads a
-- later one, E2 and its object, E7 with no job, S1 with and without its
-- ascription, a closure that projects another field off the self, and a
-- recursive field with its type written.
example : formS πc impureSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc accountedSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc FwdSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : formS .empty E2src = (.self true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS .empty E2oSrc = (.self true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS .empty E7src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc S1bareSrc = (.self true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πc S1src = (.self true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πc SelfProjSrc = (.self true, ⟨defaultFuel - 9, false⟩) := by decide +kernel
example : formAt .empty RecWSrcS RecSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- The types of the right-hand sides, with their capture sets: E5 and E6, a
-- capability in a field unboxed where the written shape asks for a box, a box
-- at the capability's own set, a field where the written shape names a member
-- or its set.
example : formAt .empty E5srcS E5srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt .empty E6srcS E6srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formSAt πc impureInsSrc impureInsSrcW = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formSAt πc C7src C7srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formSAt πc C7nbSrc C7nbSrcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formSAt πc C7scalaSrc C7scalaSrcW = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formSAt πc argUnboxSrc argUnboxSrcW = (.self true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formSAt πc recvSrc recvSrcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formSAt πc S3nbSrc S3nbSrcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formSAt πc C2src C2srcW = (.self true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πc S3src = (.self false, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc C2ascSrc = (.self false, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πc S2src = (.self false, ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- Cyclic references: two fields that read each other, a recursive field, a
-- cycle that a field before it reads, a recursion through an alias.
example : formAt .empty CycSrcS CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty RecUSrcS RecUSrcS =
    (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty Cyc3SrcS Cyc3SrcS =
    (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty AliasRecSrcS AliasRecSrcS =
    (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Bare uses of the self, typed at the snapshot.
example : formAt .empty SelfSrcS SelfSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt .empty FwdSelfSrcS FwdSelfSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : formAt .empty BareProjSrcS BareProjSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

-- The least candidate, in both orders of the intersection, and candidates
-- with no least one.
example : formAt .empty AmbUseSrcS AmbUseSrc = (.self true, ⟨defaultFuel - 9, false⟩) := by
  decide +kernel
example : formAt .empty AmbUse2SrcS AmbUse2Src = (.self true, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : formAt .empty AmbSrcS AmbSrcS =
    (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

-- A job whose lambda has no domain and no goal.
example : formAt .empty NoDomSrcS NoDomSrcS =
    (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Literals without a self shape

Each program is a written program with every self shape erased, elaborated
whole.  A program that compiles is compared with a written form: the program
itself when the formed self shape is the written one, and else the program
with its self shape written at the types of the right-hand sides. -/

/-- The outcome of a written program with every self shape erased, with the
tank left. -/
def elabSOut (π : PlatformNames) (w : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolvePTop Λc π w with
  | some p =>
      match elabTopF n π p.eraseSelf with
      | (.ok c, t) => (.ok c.tm c.uses c.ty, t)
      | (.error r, t) => (.no r, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- The type of an outcome, if it has one. -/
def Outcome.ty? {s : Sig} : Outcome s → Option (Ty s)
  | .ok _ _ T => some T
  | .no _ => none

/-- The head rule of a derivation is the object rule. -/
def derivIsObj {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {T : Ty s} :
    HasTy U Γ t T → Bool
  | .obj _ _ => true
  | _ => false

/-- The first candidate of the literal a program is, under its written
lambdas, elaborated with no goal on a tank of its own: whether its derivation
ends in the object rule, on an unmarked tank. -/
def objUnder {s : Sig} (Γ : Ctx s) : PTm s → Bool
  | .lam (some T) t => objUnder (Γ.cons T) t
  | .obj o U d =>
      match elabF Γ (.obj o U d) none ⟨defaultFuel, false⟩ with
      | ((c :: _, _), t) => !t.out && derivIsObj c.deriv
      | _ => false
  | _ => false

/-- `objUnder` on a written program with every self shape erased. -/
def objS (π : PlatformNames) (w : STm) : Bool :=
  match resolvePTop Λc π w with
  | some p => objUnder (platformCtx π.plat) p.eraseSelf
  | none => false

/-- A field whose right-hand side has two types, one below the other, and a
written self shape that gives the field the larger one. -/
def AmbSubSrc : STm := cap% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). ν(s : {v : ⊤}. {v = y.a})

/-- The same with its self shape written at the smaller type. -/
def AmbSubSrcW : STm :=
  cap% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). ν(s : {v : {b : ⊤}}. {v = y.a})

/-- A literal without a self shape at a goal that is no `μ`, its self shape
erased. -/
def AscTopSrcS : STm := cap% λ(n : {b : ⊤}). (ν(z. {a = n}) : ⊤)

/-- The same with its self shape written. -/
def AscTopSrc : STm := cap% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : ⊤)

/-- A literal without a self shape and with no goal, its self shape written
at the type of the right-hand side. -/
def NoShapeSrc : STm := cap% ν(z : {a : ∀(u : ⊤) ⊤}. {a = λ(u : ⊤). u})

/-- Literals without a self shape nested `k` deep, the innermost field the
variable `n`. -/
def nestP : Nat → {s : Sig} → BVar s .var → PTm s
  | 0, _, n => .path (.var n)
  | k + 1, _, n => .obj none none (.trm (.trm 0) none (nestP k n.there))

/-- `λ(n : {b : ⊤}). ν(x1. {a = … ν(xk. {a = n}) …})`. -/
def X6P (k : Nat) : PTm PlatformNames.empty.sig :=
  .lam (some ((Shape.fld (.trm 1) ((Shape.top) ^ [])) ^ [])) (nestP k .here)

/-- The fuel of the nested literals `k` deep: the elaboration's, and the
typer's on the elaborated program, when both end on an unmarked tank. -/
def x6At (k : Nat) : Option (Nat × Nat) :=
  match elabTopF defaultFuel .empty (X6P k) with
  | (.ok c, t) =>
      match synthTopF defaultFuel .empty c.tm with
      | (some c', t') =>
          if !t.out && !t'.out && c'.ty = c.ty then
            some (defaultFuel - t.left, defaultFuel - t'.left)
          else none
      | (none, _) => none
  | (.error _, _) => none

-- The erased programs are the written ones with their self shapes erased.
example : (resolvePTop Λc .empty RecSrc).map PTm.eraseSelf = resolvePTop Λc .empty RecUSrcS := by
  decide
example : (resolvePTop Λc .empty AscTopSrc).map PTm.eraseSelf =
    resolvePTop Λc .empty AscTopSrcS := by
  decide
example : (resolvePTop Λc .empty NoShapeSrc).map PTm.eraseSelf =
    resolvePTop Λc .empty NoShapeSrcS := by
  decide

-- The written self shapes, formed: the program elaborates to the written
-- term, use set and type.  impure, accounted, a field that reads a later one,
-- E2's object, E2, E7, S1 with and without its ascription, a closure that
-- projects another field off the self, and a recursive field with its type
-- written.
example : elabSOut πc impureSrc = ((writtenOut πc impureSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    writtenOut πc impureSrc = ((writtenOut πc impureSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut πc impureSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc accountedSrc =
      ((writtenOut πc accountedSrc).1, ⟨defaultFuel - 40, false⟩) ∧
    (writtenOut πc accountedSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc FwdSrc = ((writtenOut πc FwdSrc).1, ⟨defaultFuel - 33, false⟩) ∧
    writtenOut πc FwdSrc = ((writtenOut πc FwdSrc).1, ⟨defaultFuel - 30, false⟩) ∧
    (writtenOut πc FwdSrc).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E2oSrc = ((writtenOut .empty E2oSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    writtenOut .empty E2oSrc = ((writtenOut .empty E2oSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty E2oSrc).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E2src = ((writtenOut .empty E2src).1, ⟨defaultFuel - 65, false⟩) ∧
    (writtenOut .empty E2src).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E7src = ((writtenOut .empty E7src).1, ⟨defaultFuel - 1, false⟩) ∧
    writtenOut .empty E7src = ((writtenOut .empty E7src).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenOut .empty E7src).1.isOk = true := by
  decide +kernel
example : elabSOut πc S1src = ((writtenOut πc S1src).1, ⟨defaultFuel - 92, false⟩) ∧
    writtenOut πc S1src = ((writtenOut πc S1src).1, ⟨defaultFuel - 91, false⟩) ∧
    (writtenOut πc S1src).1.isOk = true := by
  decide +kernel
example : elabSOut πc S1bareSrc = ((writtenOut πc S1bareSrc).1, ⟨defaultFuel - 79, false⟩) ∧
    writtenOut πc S1bareSrc = ((writtenOut πc S1bareSrc).1, ⟨defaultFuel - 78, false⟩) ∧
    (writtenOut πc S1bareSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc SelfProjSrc =
      ((writtenOut πc SelfProjSrc).1, ⟨defaultFuel - 53, false⟩) ∧
    writtenOut πc SelfProjSrc = ((writtenOut πc SelfProjSrc).1, ⟨defaultFuel - 44, false⟩) ∧
    (writtenOut πc SelfProjSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty RecWSrcS = ((writtenOut .empty RecSrc).1, ⟨defaultFuel - 19, false⟩) ∧
    writtenOut .empty RecSrc = ((writtenOut .empty RecSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenOut .empty RecSrc).1.isOk = true := by
  decide +kernel

-- The derivation of the filled literal ends in the object rule: impure, a
-- field that reads a later one, E2's object, a recursive field with its type
-- written.
example : objS πc impureSrc = true := by decide +kernel
example : objS πc FwdSrc = true := by decide +kernel
example : objS .empty E2oSrc = true := by decide +kernel
example : objS .empty RecWSrcS = true := by decide +kernel

-- The types of the right-hand sides, with their capture sets: the program
-- elaborates as the one that writes the self shape at those types.  E5 and
-- E6, a capability in a field unboxed where the written shape asks for a box,
-- the capabilities unboxed by box inference, an unboxing at an argument, a
-- receiver, a field at the capability's type where the written shape names
-- the member.
example : elabOut .empty E5srcS = ((writtenOut .empty E5srcW).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenOut .empty E5srcW).1.isOk = true := by
  decide +kernel
example : elabOut .empty E6srcS = ((writtenOut .empty E6srcW).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut .empty E6srcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc impureInsSrc =
      ((writtenOut πc impureInsSrcW).1, ⟨defaultFuel - 16, false⟩) ∧
    (writtenOut πc impureInsSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc C7nbSrc = ((writtenOut πc C7nbSrcW).1, ⟨defaultFuel - 43, false⟩) ∧
    (writtenOut πc C7nbSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc C7scalaSrc =
      ((writtenOut πc C7scalaSrcW).1, ⟨defaultFuel - 40, false⟩) ∧
    (writtenOut πc C7scalaSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc argUnboxSrc =
      ((writtenOut πc argUnboxSrcW).1, ⟨defaultFuel - 30, false⟩) ∧
    (writtenOut πc argUnboxSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc recvSrc = ((writtenOut πc recvSrcW).1, ⟨defaultFuel - 20, false⟩) ∧
    (writtenOut πc recvSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc S3nbSrc = ((writtenOut πc S3nbSrcW).1, ⟨defaultFuel - 29, false⟩) ∧
    (writtenOut πc S3nbSrcW).1.isOk = true := by
  decide +kernel

-- The program's type, where the written self shapes name members or their
-- sets: S3, S3nb, C2, C2 with the client ascribed, S2.
example : (elabSOut πc S3src).1.ty? = (writtenOut πc S3src).1.ty? ∧
    (elabSOut πc S3src).2 = ⟨defaultFuel - 16, false⟩ ∧ (writtenOut πc S3src).1.isOk = true := by
  decide +kernel
example : (elabSOut πc S3nbSrc).1.ty? = (writtenOut πc S3nbSrc).1.ty? ∧
    (writtenOut πc S3nbSrc).1.isOk = true := by
  decide +kernel
example : (elabSOut πc C2src).1.ty? = (writtenOut πc C2src).1.ty? ∧
    (elabSOut πc C2src).2 = ⟨defaultFuel - 217, false⟩ ∧ (writtenOut πc C2src).1.isOk = true := by
  decide +kernel
example : (elabSOut πc C2ascSrc).1.ty? = (writtenOut πc C2ascSrc).1.ty? ∧
    (elabSOut πc C2ascSrc).2 = ⟨defaultFuel - 219, false⟩ ∧
    (writtenOut πc C2ascSrc).1.isOk = true := by
  decide +kernel
example : (elabSOut πc S2src).1.ty? = (writtenOut πc S2src).1.ty? ∧
    (elabSOut πc S2src).2 = ⟨defaultFuel - 169, false⟩ ∧ (writtenOut πc S2src).1.isOk = true := by
  decide +kernel

-- C7 boxes each capability at its own set, where the written unboxing names
-- `{k1}`: a mismatch, as for the program that writes the self shape at those
-- boxes.
example : elabSOut πc C7src = (.no .mismatch, ⟨defaultFuel - 15, false⟩) ∧
    writtenOut πc C7srcW = (.no .mismatch, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

-- Cyclic references: a recursive field, two fields that read each other, a
-- cycle that a field before it reads, a recursion through an alias.
example : elabSOut .empty RecSrc = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty Cyc3SrcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty AliasRecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Bare uses of the self, typed at the snapshot: the typer accepts the self at
-- `μ(y. ⊤)` in the real context.
example : elabOut .empty SelfSrcS = ((writtenOut .empty SelfSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty SelfSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty FwdSelfSrcS =
      ((writtenOut .empty FwdSelfSrc).1, ⟨defaultFuel - 29, false⟩) ∧
    writtenOut .empty FwdSelfSrc = ((writtenOut .empty FwdSelfSrc).1, ⟨defaultFuel - 26, false⟩) ∧
    (writtenOut .empty FwdSelfSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BareProjSrcS =
      ((writtenOut .empty BareProjSrc).1, ⟨defaultFuel - 29, false⟩) ∧
    writtenOut .empty BareProjSrc =
      ((writtenOut .empty BareProjSrc).1, ⟨defaultFuel - 26, false⟩) ∧
    (writtenOut .empty BareProjSrc).1.isOk = true := by
  decide +kernel

-- The least candidate: a field at the smaller of two types, AmbUse in both
-- orders of the intersection, and candidates with no least one.
example : elabSOut .empty AmbSubSrc =
      ((writtenOut .empty AmbSubSrcW).1, ⟨defaultFuel - 18, false⟩) ∧
    writtenOut .empty AmbSubSrc = ((writtenOut .empty AmbSubSrc).1, ⟨defaultFuel - 9, false⟩) ∧
    (writtenOut .empty AmbSubSrc).1.isOk = true ∧
    (writtenOut .empty AmbSubSrcW).1.isOk = true := by
  decide +kernel
example : elabOut .empty AmbUseSrcS =
      ((writtenOut .empty AmbUseSrc).1, ⟨defaultFuel - 24, false⟩) ∧
    writtenOut .empty AmbUseSrc = ((writtenOut .empty AmbUseSrc).1, ⟨defaultFuel - 15, false⟩) ∧
    (writtenOut .empty AmbUseSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AmbUse2SrcS =
      ((writtenOut .empty AmbUse2Src).1, ⟨defaultFuel - 22, false⟩) ∧
    (writtenOut .empty AmbUse2Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty AmbSrcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

-- A field that is a lambda without a domain and without a goal.
example : elabOut .empty NoDomSrcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- A literal with no goal, and one at a goal that is no `μ`: formed, then moved
-- to the goal.
example : elabOut .empty NoShapeSrcS =
      ((writtenOut .empty NoShapeSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    writtenOut .empty NoShapeSrc = ((writtenOut .empty NoShapeSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty NoShapeSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AscTopSrcS =
      ((writtenOut .empty AscTopSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    writtenOut .empty AscTopSrc = ((writtenOut .empty AscTopSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty AscTopSrc).1.isOk = true := by
  decide +kernel

-- Nested literals without a self shape: the elaboration's fuel against the
-- typer's on the elaborated program, quadratic against linear.
example : x6At 2 = some (8, 5) := by decide +kernel
example : x6At 4 = some (19, 7) := by decide +kernel
example : x6At 8 = some (53, 11) := by decide +kernel
example : x6At 12 = some (103, 15) := by decide +kernel
example : x6At 16 = some (169, 19) := by decide +kernel
example : x6At 17 = some (188, 20) := by decide +kernel

end ElabChecks

end CapturesFrontend
