import Coercions.CapturesCC.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# The elaborator

The elaborator fills the empty slots of a partial term (`PTm`, `Ann.lean`) and
types the result with the typer of `Typer.lean`, on the same tank.

## One function with an optional goal

The typer's `inferF` synthesizes and checks in one function, with an optional
goal, structural on an index that starts at the size of the term.  `elabF`
has the same form.  Each candidate (`ECand`) is a fill beside a result of the
typer.  The fill is the term with the empty slots below it filled.  The result
is the typer's own `Elab`: an elaborated term, its use set, its answer, and
the `HasTy` derivation of its erasure.  So every result is a judgment of the
version.  Beside the candidates `elabF` returns the reasons of its failed
branches, in search order.

## The rule of empty slots

`elabF` first asks `PTm.full?`.  A term with no empty slot goes to `inferF` as
it is, with its goal, from the index `synthF` and `checkF` start at
(`fullInfer`).  So a program with every slot written elaborates as the typer
types it, at the same fuel (`elabF_toI`, `elabInF_toI`).  Below an empty slot
each clause is the typer's clause of the same form, with the fills and the
reasons added.  A clause that checks against a goal first and then falls back
to synthesis and the answer goal keeps doing so, so a goal site whose attempt
fails runs the typer's own route on the filled term.

## Where a goal reaches a term

- A `let` with a written answer passes it to its body, under the binder.
- A `let` checked at a goal passes the goal to its body.
- An ascription `(t : T)` checks `t` against `T` read at the context.
- A lambda's body gets the result part of the goal.
- A field of a literal with a written self shape gets the field's type in the
  shape, read under the class root.
- A call argument, the binding the resolver inserts at an operand, gets the
  dominant formal of its callee, whole, its result included.
- The bound term of `let x : A = t in x`, the version's `val x : A = t`, gets
  `A` read at the context.

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
results, where the version has one.  Two sides with incomparable domains are a
mismatch, since the compiler forms their union, which the version lacks.  A
selection with different bounds whose upper bound has a function part is a
mismatch, as for an abstract type with a function upper bound in the compiler.
An existential answer and any other goal have no function part.  There, as
with no goal at all, a lambda without a domain is the compiler's "Missing
parameter type", unless its body is `g x` on its own parameter.  Then the
domain is the dominant formal of `g`, as `Typer.typedFunctionValue` reads the
parameter type of the callee (`inferredFromTarget`).

The domain lives under the arrow's own capture binder, where the goal's domain
lives, so it is copied as it is.  The typer reads a domain with `readDom`,
which reads `any` as the arrow's own binder.  The goal's domain was read so
when the goal was read, so it holds no `any`, and `readDom` leaves it as it is
(`Ty.expand_noAny`).  This is the compiler's `globalCapToLocal` on an inferred
parameter type.

A lambda whose body has no empty slot is filled with the domain and handed to
`inferF` with the goal.  So its candidates and its tank are the typer's on the
filled lambda.  Otherwise the lambda takes the typer's clause with that
domain: at a function type the body is checked against its codomain, and the
lambda gets the goal's set when its body's set fits.  Through an intersection,
a selection or a box, the body is checked against the result part and the
lambda, at its least set, is moved to the goal by the answer goal.  If that
gives nothing, the body is synthesized and the lambda moved to the goal.  A
lambda with a written domain whose body has an empty slot reads the result
part of its goal the same way.

## Call arguments and `val` definitions

`atomize` binds an operand that is no variable by a `let` tagged `arg`, so
`g t` is `let z = t in g z`.  The formals of `g` are the domains of the
function types the lookup finds for it, or of the function types it boxes.
The goal is the dominant formal, the one every formal is below, as the
argument of an intersection callee is typed against the least upper bound of
the formals (`TypeComparer.distributeAnd`).  The formal lives under the
callee's arrow binder, which the application instantiates with `z`.  So the
goal is the formal moved out from under that binder, with a box stripped,
and a set that names the binder is read as every atom of the context.  The
bound term is elaborated against the goal only to fill it.  The filled `let`
goes to `inferF` with the goal, so `z` is bound at the type the typer gives
the filled term and a closure keeps its least set.  With no dominant formal,
or when this gives nothing on an unmarked tank, the `let` is typed as any
other.  `let x : A = t in x` is filled the same way against `A`, as
`typedValDef` types a right-hand side against its written type.

## `let` and unpackings

A `let` whose bound term has an existential answer is an unpacking, and its
body is typed under the witness and the payload, renamed past the witness
binder, as the typer does.  The fill of such a body may name the witness, so
the fill of the `let` is then the unpacking `letex`, unless the body has no
empty slot, in which case the `let` keeps its form.

## Object literals

A literal with a written self shape whose definitions have an empty slot has
its definitions filled against the shape in lockstep (`elabDefsF`).  A field
with no empty slot stays as written.  Any other field is elaborated against
its type in the shape read under the class root, so its lambdas take their
domains from it.  A written field type must be the shape's.  The fields are
elaborated in a probe context (`probeCtx`): the class root, then the self at
the shape read at the context, holding a placeholder for the definitions and
the set of every atom of the context.  No function of the typer reads the
definitions of a self binder.  The filled literal then goes to `inferF` in the
real context, so its derivation is the typer's `HasTy.obj` and its set the
least one the typer finds.  A literal without a self shape at a goal that
dealiases to a `μ` takes the body of that `μ` as its self shape
(`selfGoalF`).  Scala makes a class `pt` the parent of `new { … }`
(`Typer.typedNew`), and every type of the version is structural, so a `μ` goal
plays the class.  When that gives nothing on an unmarked tank, and for any
other literal without a self shape, the self shape is formed from the
definitions, as the next section says.  The literal is then filled at the
formed shape (`fillDefsF`) and goes to `inferF` with the goal, which
synthesizes it and moves it to the goal.  A field without a written type
holds the fill the rounds chose for it, so no such field is elaborated twice,
and nested literals cost fuel quadratic in their depth.

## Self shapes formed from definitions

`formSelfF` forms the self shape of a literal from its definitions, as the
completers of `Namer` type the members of a class.  Type members, capture
members and fields with a written type are known at once.  Every other field
is a job (`jobsOf`, `jobsF`), typed in rounds (`roundsF`).  A round takes a
snapshot of the self shape known so far and types every ready job once, with
no goal, in the probe context: the class root, then the self at the snapshot
read at the context, at the set of every atom of the context.  A job is ready
when none of the fields it projects off the self is pending (`PTm.deps`).  A
job that uses the self any other way is typed in the first round in which no
ready job lacks such a use.  A field's type is the answer of its least
candidate (`leastCandF`), capture sets included, moved out from under the
class root.  Candidates with no least one are ambiguous.  An existential
answer, or one that names the class root, holds a root capability the self
shape cannot state, and the field needs a written type, as
`CheckCaptures.checkInferredResult` asks.  A round that types nothing stops
with the cyclic reference `cycleAt` names.  The self shape is the definition
list read in lockstep (`PDefs.fullSelf`), each member moved out from under the
class root.

## Reasons

Each clause returns the reasons of its failed branches in search order, and a
branch that succeeds drops them.  A written type outside the notation of the
version is the typer's own reason (`writtenWhy`), with its proof.  `elabTopF`
reports the recursion limit when the tank ended marked, else the first
reason, else a mismatch (`Reason.top`).  `EReason` is the reason type of
`Coercions.Frontend.Reason` at the labels of this version, with the typer's
`Reason` as its own.

## The theorems

`elabF_toI` says that a term with every slot written is the typer's,
candidates, derivations and tank, with the term itself as the fill, and
`elabF_full` says the same of any term with no empty slot.  `elabInF_toI` is
the same from the index the elaborator starts at, against `synthF`.
`elabF_lam_none` unfolds the clause of a lambda without a domain.
`elabF_lam_formal` says that every candidate of such a lambda fills it with
the domain of its goal's function part, or, at a goal with none, with the
dominant formal of the callee of a body `g x`.  `readDom` leaves that domain
as it is when it holds no `any` (`Ty.expand_noAny`).  `argGoal_dominant` says
that the goal of a call argument is a formal that every formal is below.
`elabF_arg` and `elabF_val` unfold the two clauses that fill a bound term,
and `lam_callee_full` says that a callee's body is the typer on the lambda
filled with the formal, candidates and tank.  `inferF_index` says that the typer
gives the same answer at every index from the size of the term up, so the
elaborator, which calls it at the size of a subterm, and the typer, which
calls it at the index left, agree.

`elabF_framed` and `elabDefsF_framed` say that the elaborator is framed, as
the typer is (`inferF_framed`).  It leaves a marked tank as it is, it only
spends fuel, and a run that ends unmarked runs the same from a fuller tank.
The goal readers follow aliases on an index that starts at the fuel left, so
their frame lemmas rest on the agreement of that index with any larger one,
as the lookup's do.

`lam_fill_full` is the completeness of a filled domain.  At a goal whose
function part gives a domain, a lambda without one whose body has no empty
slot is the typer on the lambda filled with that domain, candidates and tank.
`lam_direct_full`, `lam_side_full` and `asc_direct_full` state it at a
function type, at a side and under an ascription, as an agreement with
`inferF` (`Agrees`).  `arg_fill_full` and `val_fill_full` state it at a call
argument and at a `val` definition.  When the typer types the lambda filled
with the formal and then the filled `let`, the elaborator is the typer on the
filled program.

`fullSelf_lockstep` says that the formed self shape is the definition list
read in lockstep, and `jobsF_written` that a literal with a written type on
every field has no job.  `leastCand_least` says that the least candidate is a
candidate whose answer is below every candidate's, and `cycleAt_onCycle` that
the cyclic reference names a pending field whose walk comes back to it.
`roundF_explicit` says that a round that asks for a written type names one of
its jobs, whose least answer the self shape cannot hold or whose own
elaboration asked for it.  `roundsF_framed` says that the rounds are framed
when every job is, and `jobsF_framed` that every job is.  `probeCtx_lookup`
says that the probe context types every variable as the object body of the
literal does, whatever its definitions.  `obj_none_landed` says that a
candidate of a literal without a self shape is a candidate the typer gives the
literal with its self shape and its definitions filled, at the same goal, with
that literal as its fill, so its derivation is the typer's.
`obj_none_formed` adds that with no goal the self shape is the one the rounds
form.
-/

namespace CapturesCCFrontend

open Frontend.Fuel CapturesCCFrontend.Core
open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub
  SubShape Subcap ESub HasTy DefsTy Platform)
open scoped CapturesCC.DotMNF

/-- The reasons of this front end: its labels, and the typer's reasons as its
own. -/
abbrev EReason := Frontend.Reason.Reason Label Reason

/-- A candidate: the fill of the partial term, and the typer's result on
it. -/
structure ECand {s : Sig} (Γ : Ctx s) where
  /-- The partial term with the empty slots below it filled. -/
  fill : ATm s
  /-- The typer's elaborated term, use set, answer and derivation. -/
  e : Elab Γ

/-- The candidates of an elaboration, with the reasons of its failed
branches. -/
abbrev Out {s : Sig} (Γ : Ctx s) := List (ECand Γ) × List EReason

/-! ## Renaming partial terms

The typer types the body of a `let` whose bound term has an existential
answer renamed past the witness binder.  The elaborator does the same with a
body that has an empty slot. -/

mutual
/-- Rename the free variables of a partial term, with each written slot
renamed at the signature it lives in. -/
def PTm.rename {s1 s2 : Sig} (p : PTm s1) (ρ : Rename s1 s2) : PTm s2 :=
  match p with
  | .path q => .path (q.rename ρ)
  | .lam T t => .lam (T.map fun T => T.rename ρ.lift) (t.rename ρ.lift.lift.lift)
  | .obj S d => .obj (S.map fun S => S.rename ρ.lift) (d.rename ρ.lift.lift)
  | .app x y => .app (ρ.var x) (ρ.var y)
  | .proj x a => .proj (ρ.var x) a
  | .let g ann t u => .let g (ann.map fun E => E.rename ρ) (t.rename ρ) (u.rename ρ.lift)
  | .letex t u => .letex (t.rename ρ) (u.rename ρ.lift.lift)
  | .box x => .box (ρ.var x)
  | .unbox C x => .unbox (C.map fun C => CaptureSet.rename C ρ) (ρ.var x)
  | .asc t T => .asc (t.rename ρ) (T.rename ρ)
termination_by structural p
/-- Rename the free variables of the definitions of a partial term. -/
def PDefs.rename {s1 s2 : Sig} (d : PDefs s1) (ρ : Rename s1 s2) : PDefs s2 :=
  match d with
  | .typ A S => .typ A (S.rename ρ)
  | .cap C c => .cap C (CaptureSet.rename c ρ)
  | .trm a T t => .trm a (T.map fun T => T.rename ρ) (t.rename ρ)
  | .and d e => .and (d.rename ρ) (e.rename ρ)
termination_by structural d
end

mutual
/-- Renaming keeps the node count of a term. -/
theorem sizeATm_rename : ∀ {s1 s2 : Sig} (a : ATm s1) (ρ : Rename s1 s2),
    sizeATm (a.rename ρ) = sizeATm a
  | _, _, .path _, _ => by simp only [ATm.rename, sizeATm]
  | _, _, .lam _ t, ρ => by simp only [ATm.rename, sizeATm, sizeATm_rename t]
  | _, _, .obj _ d, ρ => by simp only [ATm.rename, sizeATm, sizeADefs_rename d]
  | _, _, .app _ _, _ => by simp only [ATm.rename, sizeATm]
  | _, _, .proj _ _, _ => by simp only [ATm.rename, sizeATm]
  | _, _, .let _ t u, ρ => by simp only [ATm.rename, sizeATm, sizeATm_rename t, sizeATm_rename u]
  | _, _, .letex t u, ρ => by
      simp only [ATm.rename, sizeATm, sizeATm_rename t, sizeATm_rename u]
  | _, _, .box _, _ => by simp only [ATm.rename, sizeATm]
  | _, _, .unbox _ _, _ => by simp only [ATm.rename, sizeATm]
  | _, _, .asc t _, ρ => by simp only [ATm.rename, sizeATm, sizeATm_rename t]
/-- Renaming keeps the node count of definitions. -/
theorem sizeADefs_rename : ∀ {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2),
    sizeADefs (d.rename ρ) = sizeADefs d
  | _, _, .typ _ _, _ => by simp only [ADefs.rename, sizeADefs]
  | _, _, .cap _ _, _ => by simp only [ADefs.rename, sizeADefs]
  | _, _, .trm _ t, ρ => by simp only [ADefs.rename, sizeADefs, sizeATm_rename t]
  | _, _, .and d e, ρ => by
      simp only [ADefs.rename, sizeADefs, sizeADefs_rename d, sizeADefs_rename e]
end

/-! ## Combinators with reasons -/

/-- A slot agrees with a value when it is empty or holds that value. -/
def optAgree {α : Type} [DecidableEq α] : Option α → α → Bool
  | some x, y => decide (x = y)
  | none, _ => true

/-- The typer on a term with no empty slot, at an optional goal, from the
index `synthF` and `checkF` start at.  The term is its own fill.  No
candidate is a mismatch. -/
def fullInfer {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (G : Option (ETy s)) :
    Fu (Out Γ) :=
  Fu.bind (inferF Γ ps (sizeATm a) a G) fun cs =>
    Fu.ret (cs.map fun e => (⟨a, e⟩ : ECand Γ), if cs.isEmpty then [.mismatch] else [])

/-- The candidates of `a`, or those of `b` when `a` has none, with the
reasons of both.  This is `orElseL` of the typer with reasons. -/
def orElseO {s : Sig} {Γ : Ctx s} (a b : Fu (Out Γ)) : Fu (Out Γ) :=
  Fu.bind a fun r =>
    match r with
    | ([], rs) => Fu.bind b fun r' => Fu.ret (r'.1, rs ++ r'.2)
    | r => Fu.ret r

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

/-- The reasons a step that dropped every candidate leaves: those of the
candidates it started from when there were none, and a mismatch otherwise. -/
def dropReasons {α : Type} (before : List α) (rs : List EReason) : List EReason :=
  if before.isEmpty then rs else [.mismatch]

/-- Keep the first candidate of each use set and answer, as `dedupE`. -/
def dedupEC {s : Sig} {Γ : Ctx s} : List (ECand Γ) → List (ECand Γ)
  | [] => []
  | c :: cs => c :: (dedupEC cs).filter fun c' => !decide (c'.e.uses = c.e.uses ∧ c'.e.ans = c.e.ans)

/-- The first candidate at exactly the answer asked for, with its fill, as
`firstChecked`. -/
def firstCheckedE {s : Sig} {Γ : Ctx s} (cs : List (ECand Γ)) (E : ETy s) :
    Option (ATm s × Checked Γ E) :=
  cs.findSome? fun c => (toChecked c.e E).map fun r => (c.fill, r)

/-- The candidates moved to a goal, each keeping its fill, as `finishF`.  A
goal that drops every candidate is a mismatch. -/
def finishE {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (cs : List (ECand Γ)) : Fu (Out Γ) :=
  match G with
  | none => Fu.ret (cs, [])
  | some E =>
      Fu.bind (Fu.flatMapL (fun c => mapL (subsumeF Γ c.e E) fun r =>
          (⟨c.fill, r.toElab⟩ : ECand Γ)) cs) fun l =>
        Fu.ret (l, if l.isEmpty && !cs.isEmpty then [.mismatch] else [])

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
  | direct (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s)
  /-- A function part with the domain `T1` and the result part `V`, reached
  through an intersection, an alias or a box.  `V` is empty when two results
  have no intersection in the version. -/
  | side (T1 : Dom s) (V : Option (Cod s))
  /-- A function part the version cannot give, a type mismatch. -/
  | bad

/-- The domain a function part gives a lambda. -/
def FunPart.dom? {s : Sig} : FunPart s → Option (Dom s)
  | .direct _ T1 _ => some T1
  | .side T1 _ => some T1
  | _ => Option.none

/-- The bound of the first member with equal bounds, an alias. -/
def aliasOf {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} :
    List (TMem Γ y A) → Option (Shape s)
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

/-- The intersection of two result parts.  Two plain types meet: the shapes
by `∧`, the sets at the atoms they share, so the intersection is below both.
Equal results are their own intersection.  Any other pair has none in the
version. -/
def meetRes {s : Sig} (V1 V2 : Cod s) : Option (Cod s) :=
  if V1 = V2 then some V1
  else
    match V1, V2 with
    | .ty (.capt C1 S1), .ty (.capt C2 S2) =>
        some (.ty (.capt (C1.filter fun a => CaptureSet.elem C2 a) (.and S1 S2)))
    | _, _ => none

/-- The intersection of two optional result parts. -/
def meetOpt {s : Sig} : Option (Cod s) → Option (Cod s) → Option (Cod s)
  | some V1, some V2 => meetRes V1 V2
  | _, _ => none

/-- The meet of the function parts of two sides of an intersection, as
`findFunctionType` meets them with `&`.  Comparable domains give the larger
one and the intersection of the results.  Domains are compared as
`SubShape.all` compares them, under the scope root (`domSubF`). -/
def meetPart {s : Sig} (Γ : Ctx s) : FunPart s → FunPart s → Fu (FunPart s)
  | .bad, _ => Fu.ret .bad
  | _, .bad => Fu.ret .bad
  | .none, f => Fu.ret f
  | f, .none => Fu.ret f
  | .side S1 V1, .side S2 V2 =>
      Fu.bind (domSubF Γ S2 S1) fun o2 =>
        match o2 with
        | some _ => Fu.ret (.side S1 (meetOpt V1 V2))
        | none =>
            Fu.bind (domSubF Γ S1 S2) fun o1 =>
              match o1 with
              | some _ => Fu.ret (.side S2 (meetOpt V1 V2))
              | none => Fu.ret .bad
  | _, _ => Fu.ret .bad

mutual
/-- The function part of a shape, with `rec` for the shape an alias stands for
and for an upper bound. -/
def funPartS {s : Sig} (Γ : Ctx s) (rec : Shape s → Fu (FunPart s)) : Shape s → Fu (FunPart s)
  | .all T1 T2 => Fu.ret (.side T1 (some T2))
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
goal it is still pursuing.  So a cycle of aliases stops at once. -/
def funPartF {s : Sig} (Γ : Ctx s) : Nat → List (Shape s) → Shape s → Fu (FunPart s)
  | 0, _, S => funPartS Γ (fun _ => markAs .none) S
  | d + 1, seen, S =>
      funPartS Γ (fun S' => if S' ∈ seen then Fu.ret .none else funPartF Γ d (S' :: seen) S') S

/-- The function part of an optional goal.  A function type at the top is
`direct` and draws nothing.  An existential answer has none.  Any other goal
is read from the fuel left. -/
def funPartOf {s : Sig} (Γ : Ctx s) : Option (ETy s) → Fu (FunPart s)
  | none => Fu.ret .none
  | some (.ex _ _) => Fu.ret .none
  | some (.ty (.capt C (.all T1 T2))) => Fu.ret (.direct C T1 T2)
  | some (.ty (.capt _ S)) => fun t => funPartF Γ t.left [S] S t

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
dealiases to.  The goal's set is no part of the self shape, and an
existential answer gives none. -/
def selfGoalF {s : Sig} (Γ : Ctx s) : ETy s → Fu (Option (Shape (s,x)))
  | .ty (.capt _ S) =>
      Fu.bind (dealiasAt Γ S) fun S' =>
        match S' with
        | .mu B => Fu.ret (some B)
        | _ => Fu.ret none
  | .ex _ _ => Fu.ret none

/-! ## The goal of a call argument

The formals of a callee are the domains of the function types the lookup
finds for it.  A callee with no function type but a box gives the domains of
the function types it boxes, since the typer's application clause unboxes
such a callee first.  Several formals come from an intersection.  The
argument of an intersection callee is typed against the least upper bound of
the formals (`TypeComparer.distributeAnd`).  The version has no union, so the
goal is the dominant formal, the one every other formal is below.  A formal
is a domain, under the callee's arrow binder, so formals are compared as
`SubShape.all` compares domains, under the scope root (`domSubF`). -/

/-- Every atom of a context: its term variables and capture binders. -/
def allAtoms {s : Sig} (Γ : Ctx s) : CaptureSet s :=
  (ctxVars Γ).map CapAtom.var ++ (ctxCaps Γ).map CapAtom.cvar

/-- The domain of a boxed function type. -/
def boxDom? {s : Sig} {Γ : Ctx s} {g : BVar s .var} (b : BoxView Γ g) : Option (Dom s) :=
  match b.bsh with
  | .all T1 _ => some T1
  | _ => none

/-- The domains of the function types the lookup finds for `g`, or of the
function types it boxes when it has none. -/
def formalsF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (List (Dom s)) :=
  Fu.bind (fnViewsF Γ g) fun fs =>
    match fs with
    | [] => Fu.bind (boxViewsF Γ g) fun bs => Fu.ret (bs.filterMap boxDom?)
    | fs => Fu.ret (fs.map (·.dom))

/-- Every domain of the list is below `F` under the scope root.  An equal
domain costs nothing (`domSubF`). -/
def allBelowF {s : Sig} (Γ : Ctx s) (F : Dom s) : List (Dom s) → Fu Bool
  | [] => Fu.ret true
  | F' :: Fs =>
      Fu.bind (domSubF Γ F' F) fun o =>
        match o with
        | some _ => allBelowF Γ F Fs
        | none => Fu.ret false

/-- The first domain of `cands` that every domain of `Fs` is below. -/
def dominantF {s : Sig} (Γ : Ctx s) (Fs : List (Dom s)) : List (Dom s) → Fu (Option (Dom s))
  | [] => Fu.ret none
  | F :: rest =>
      Fu.bind (allBelowF Γ F Fs) fun b => if b then Fu.ret (some F) else dominantF Γ Fs rest

/-- The dominant formal of `g`, the whole parameter type with its result.
`none` when `g` has no function type or no formal is dominant. -/
def argGoalF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (Option (Dom s)) :=
  Fu.bind (formalsF Γ g) fun Fs => dominantF Γ Fs Fs

/-- A formal as the compiler's typer sees it, with a box stripped.  The typer
of the compiler sees no boxes, and box inference boxes the argument when the
application is typed. -/
def stripBox {s : Sig} : Ty s → Ty s
  | .capt _ (.box T) => T
  | T => T

/-- The goal a formal gives the bound term of a call argument, outside the
callee's arrow binder, with a box stripped.  The binder stands for the
argument's own set, which the application instantiates with the argument
variable, bound only after the term.  So a set that names the binder is read
as every atom of the context, the largest set a term there can capture.  A
shape that names the binder gives no goal. -/
def formalGoal {s : Sig} (Γ : Ctx s) (F : Dom s) : Option (Ty s) :=
  match stripBox F with
  | .capt C S =>
      (shapeStrengthen? S).map fun S' => .capt ((capStrengthen? C).getD (allAtoms Γ)) S'

/-- A variable under one more binder, as a variable outside it: `none` for the
innermost binder. -/
def BVar.outer? {s : Sig} {k0 k : Kind} : BVar (s,,k0) k → Option (BVar s k)
  | .here => none
  | .there y => some y

/-- `g` when a term is `g x`, with `x` the innermost binder and `g` a variable
bound outside it. -/
def appHere? {s : Sig} : PTm (s,x) → Option (BVar s .var)
  | .app f y => if y = .here then BVar.outer? f else none
  | _ => none

/-- The callee of a lambda body `g x`: `g`, when `x` is the parameter and `g` a
variable bound outside the lambda, past its arrow binder and its root. -/
def calleeOf? {s : Sig} (t : PTm (Sig.body s)) : Option (BVar s .var) :=
  (appHere? t).bind fun g => (BVar.outer? g).bind BVar.outer?

/-- The callee of a call argument: `g` when the `let` is the binding the
resolver inserts at an operand, `let z = t in g z`. -/
def argCallee? {s : Sig} : LetTag → Option (ETy s) → PTm (s,x) → Option (BVar s .var)
  | .arg, none, u => appHere? u
  | _, _, _ => none

/-! ## Lambdas -/

/-- The typer's checking route for `λ(x : Tw). t` at `(∀(x : T1') T2) ^ C`,
read at `T`: the first candidate of the body at the codomain, and
`lamCheckF` on it.  The fill is the lambda with the body's fill. -/
def lamCheckE {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s) (C : CaptureSet s)
    (T1' : Dom s) (T2 : Cod s) (r : Out (Γ.body T)) : Fu (Out Γ) :=
  match r.1.find? (fun c => decide (c.e.ans = Cod.underRoot T2)) with
  | some c =>
      Fu.bind (lamCheckF Γ T hwf C T1' T2 [c.e]) fun es =>
        Fu.ret (es.map fun e => (⟨.lam Tw c.fill, e⟩ : ECand Γ),
          if es.isEmpty then [.mismatch] else [])
  | none => Fu.ret ([], dropReasons r.1 r.2)

/-- The typer's synthesis route for `λ(x : Tw). t`, read at `T`: each
candidate of the body closed by `lamGenF` at its least set and moved to the
goal.  The fill is the lambda with the body's fill. -/
def lamGenE {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s) (G : Option (ETy s))
    (r : Out (Γ.body T)) : Fu (Out Γ) :=
  Fu.bind (flatMapR (fun (c : ECand (Γ.body T)) =>
      Fu.bind (lamGenF Γ T hwf [c.e]) fun es =>
        Fu.bind (finishF Γ G es) fun es' =>
          Fu.ret (es'.map fun e => (⟨.lam Tw c.fill, e⟩ : ECand Γ), ([] : List EReason))) r.1)
    fun l => Fu.ret (l.1, if l.1.isEmpty then dropReasons r.1 r.2 else [])

/-- `λ(x : Tw). t`, whose body has an empty slot, at a goal with the function
part `fp`.  The typer reads the domain as `readDom Tw`.  At a function type
the body is checked against its codomain, as the typer's clause does.  At a
side the body is checked against the result part, and the lambda moved to
the goal.  If that gives nothing, the body is synthesized and the lambda
moved to the goal.  A domain outside the notation is the typer's reason. -/
def lamAtF {s : Sig} (Γ : Ctx s) (Tw : Dom s) (G : Option (ETy s)) (fp : FunPart s)
    (body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))) : Fu (Out Γ) :=
  match writtenWhy (domArrow Tw) with
  | some r => Fu.ret ([], [.landed r])
  | none =>
      if hwf : Ty.Wf (readDom Tw) then
        orElseO
          (match fp with
            | .direct C T1' T2 =>
                Fu.bind (body (some (Cod.underRoot T2))) (lamCheckE Γ (readDom Tw) hwf Tw C T1' T2)
            | .side _ (some V) =>
                Fu.bind (body (some (Cod.underRoot V))) (lamGenE Γ (readDom Tw) hwf Tw G)
            | _ => Fu.ret ([], []))
          (Fu.bind (body none) (lamGenE Γ (readDom Tw) hwf Tw G))
      else Fu.ret ([], [.mismatch])

/-- A lambda with a written domain whose body has an empty slot. -/
def lamSomeF {s : Sig} (Γ : Ctx s) (Tw : Dom s) (G : Option (ETy s))
    (body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))) : Fu (Out Γ) :=
  Fu.bind (funPartOf Γ G) fun fp => lamAtF Γ Tw G fp body

/-- A lambda without a domain whose goal has no function part, or with no
goal.  A body `g x` gives the domain: the dominant formal of `g`, as
`Typer.typedFunctionValue` reads the parameter type of the callee
(`calleeType`, `inferredFromTarget`).  The formal is a domain under the
callee's arrow binder, and it becomes the lambda's domain under the lambda's
own binder.  The filled lambda goes to `inferF` with the goal.  Any other
body, or a callee with no dominant formal, is the compiler's missing parameter
type. -/
def lamCalleeF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (t : PTm (Sig.body s)) : Fu (Out Γ) :=
  match calleeOf? t with
  | some g =>
      Fu.bind (argGoalF Γ g) fun oD =>
        match oD, t.full? with
        | some D, some b => fullInfer Γ ps (.lam D b) G
        | _, _ => Fu.ret ([], [.missingParamType none])
  | none => Fu.ret ([], [.missingParamType none])

/-- A lambda without a domain.  The domain is the domain of the goal's
function part.  With a body that has no empty slot, the lambda filled with it
goes to `inferF` with the goal.  Otherwise `lamAtF`.  With no function part a
body `g x` gives the domain (`lamCalleeF`), and any other body is the
compiler's missing parameter type.  A function part the version cannot give
is a mismatch. -/
def lamNoneF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (t : PTm (Sig.body s))
    (body : (D : Dom s) → Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom D)))) :
    Fu (Out Γ) :=
  Fu.bind (funPartOf Γ G) fun fp =>
    match fp.dom? with
    | some D =>
        match t.full? with
        | some b => fullInfer Γ ps (.lam D b) G
        | none => lamAtF Γ D G fp (body D)
    | none =>
        match fp with
        | .bad => Fu.ret ([], [.mismatch])
        | _ => lamCalleeF Γ ps G t

/-! ## `let`

The typer's `let` clause with fills and reasons: `letOneF`, `letBoundF`,
`letPairsF` and `letexPairsF` of `Typer.lean`, with the body an elaboration.
`mk` builds the fill of a plain `let` from the fills of its bound term and
its body, and `mkX` the fill of an unpacking. -/

/-- The candidates of a body under the binder of a plain bound term. -/
abbrev BodyPE {s : Sig} (Γ : Ctx s) : Type :=
  (p : PElab Γ) → Option (ETy (s,x)) → Fu (Out (Γ.cons p.ty))

/-- The candidates of a body under the witness and the payload of an
existential bound term. -/
abbrev BodyXE {s : Sig} (Γ : Ctx s) : Type :=
  (q : XElab Γ) → Option (ETy ((s,c),x)) → Fu (Out ((Γ.consC).cons q.body))

/-- Every candidate of a body under the binder of `p`, each closed by
`letFinishF`, as `letPairsF`. -/
def letPairsE {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    (mk : ATm (s,x) → ATm s) (body : Fu (Out (Γ.cons p.ty))) : Fu (Out Γ) :=
  Fu.bind body fun r2 =>
    Fu.bind (Fu.flatMapL (fun (c2 : ECand (Γ.cons p.ty)) =>
        mapL (letFinishF Γ ann p c2.e) fun e => (⟨mk c2.fill, e⟩ : ECand Γ)) r2.1) fun cs =>
      Fu.ret (cs, if cs.isEmpty then dropReasons r2.1 r2.2 else [])

/-- Every candidate of an unpacking's body, each closed by `letexFinishF`, as
`letexPairsF`. -/
def letexPairsE {s : Sig} (Γ : Ctx s) (q : XElab Γ) (mkX : ATm ((s,c),x) → ATm s)
    (body : Fu (Out ((Γ.consC).cons q.body))) : Fu (Out Γ) :=
  Fu.bind body fun r2 =>
    Fu.bind (Fu.flatMapL (fun (c2 : ECand ((Γ.consC).cons q.body)) =>
        mapL (letexFinishF Γ q c2.e) fun e => (⟨mkX c2.fill, e⟩ : ECand Γ)) r2.1) fun cs =>
      Fu.ret (cs, if cs.isEmpty then dropReasons r2.1 r2.2 else [])

/-- A `let` without annotation, at one candidate of the bound term, as
`letBoundF`. -/
def letBoundE {s : Sig} (Γ : Ctx s) (c1 : ECand Γ) (bp : BodyPE Γ) (bx : BodyXE Γ)
    (mk : ATm s → ATm (s,x) → ATm s) (mkX : ATm s → ATm ((s,c),x) → ATm s) : Fu (Out Γ) :=
  match c1.e.split with
  | .inl p => letPairsE Γ none p (mk c1.fill) (bp p none)
  | .inr q => letexPairsE Γ q (mkX c1.fill) (bx q none)

/-- A `let` at the answer `E`, at one candidate of the bound term, as
`letOneF`. -/
def letOneE {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (E : ETy s) (c1 : ECand Γ)
    (bp : BodyPE Γ) (bx : BodyXE Γ) (mk : ATm s → ATm (s,x) → ATm s)
    (mkX : ATm s → ATm ((s,c),x) → ATm s) : Fu (Option (ECand Γ) × List EReason) :=
  match c1.e.split, E with
  | .inl p, .ty G =>
      if tyWf? G then
        Fu.bind (bp p (some (.ty G.weaken))) fun r2 =>
          match firstCheckedE r2.1 (.ty G.weaken) with
          | some (f2, c2) =>
              Fu.bind (letAtF Γ ann G p c2) fun o =>
                Fu.ret (o.map fun e => (⟨mk c1.fill f2, e⟩ : ECand Γ),
                  if o.isSome then [] else [.mismatch])
          | none => Fu.ret (none, dropReasons r2.1 r2.2)
      else Fu.ret (none, [.mismatch])
  | .inl p, .ex _ _ =>
      match ann with
      | some _ =>
          Fu.bind (letPairsE Γ ann p (mk c1.fill) (bp p none)) fun r =>
            Fu.bind (Fu.firstSome (fun (c : ECand Γ) =>
                mapO (subsumeF Γ c.e E) fun r' => (⟨c.fill, r'.toElab⟩ : ECand Γ)) r.1) fun o =>
              Fu.ret (o, if o.isSome then [] else dropReasons r.1 r.2)
      | none => Fu.ret (none, [])
  | .inr q, E =>
      Fu.bind (bx q (some (ETy.weaken (ETy.weaken (k := .cap) E)))) fun r2 =>
        match firstCheckedE r2.1 (ETy.weaken (ETy.weaken (k := .cap) E)) with
        | some (f2, c2) =>
            Fu.bind (letexOfF Γ q E c2) fun o =>
              Fu.ret (o.map fun e => (⟨mkX c1.fill f2, e⟩ : ECand Γ),
                if o.isSome then [] else [.mismatch])
        | none => Fu.ret (none, dropReasons r2.1 r2.2)

/-- The list of at most one candidate a `let` at a goal gives. -/
def listR {s : Sig} {Γ : Ctx s} (r : Option (ECand Γ) × List EReason) : Out Γ :=
  (listO r.1, r.2)

/-- A `let` from the candidates of its bound term, as the typer's clause.
Without annotation the body is checked against the goal first, then every
pair is synthesized, avoided and moved to the goal.  With an annotation the
body is checked against it, read at the context.  An annotation outside the
notation is the typer's reason.  No candidate of the bound term keeps its
reasons. -/
def letE {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (ann : Option (ETy s)) (G : Option (ETy s))
    (bound : Fu (Out Γ)) (bp : BodyPE Γ) (bx : BodyXE Γ) (mk : ATm s → ATm (s,x) → ATm s)
    (mkX : ATm s → ATm ((s,c),x) → ATm s) : Fu (Out Γ) :=
  Fu.bind bound fun r1 =>
    if r1.1.isEmpty then Fu.ret ([], r1.2)
    else
      match ann with
      | none =>
          orElseO
            (match G with
              | some E =>
                  Fu.bind (firstSomeR (fun c1 => letOneE Γ none E c1 bp bx mk mkX) r1.1) fun r =>
                    Fu.ret (listR r)
              | none => Fu.ret ([], []))
            (Fu.bind (flatMapR (fun c1 => letBoundE Γ c1 bp bx mk mkX) r1.1) fun r =>
              Fu.bind (finishE Γ G (dedupEC r.1)) fun r' =>
                Fu.ret (r'.1, if r'.1.isEmpty then r.2 ++ r'.2 else []))
      | some A =>
          match writtenAnsWhy A with
          | some rr => Fu.ret ([], [.landed rr])
          | none =>
              Fu.bind (firstSomeR (fun c1 => letOneE Γ (some (readAns Γ ps A)) (readAns Γ ps A) c1
                  bp bx mk mkX) r1.1) fun r =>
                Fu.bind (finishE Γ G (listO r.1)) fun r' =>
                  Fu.ret (r'.1, if r'.1.isEmpty then r.2 ++ r'.2 else [])

/-- An unpacking from the candidates of its bound term, as the typer's
clause. -/
def letexE {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (bound : Fu (Out Γ)) (bx : BodyXE Γ) :
    Fu (Out Γ) :=
  Fu.bind bound fun r1 =>
    if r1.1.isEmpty then Fu.ret ([], r1.2)
    else
      Fu.bind (flatMapR (fun (c1 : ECand Γ) =>
          match c1.e.split with
          | .inr q => letexPairsE Γ q (fun f2 => .letex c1.fill f2) (bx q none)
          | .inl _ => Fu.ret ([], [.mismatch])) r1.1) fun r =>
        Fu.bind (finishE Γ G (dedupEC r.1)) fun r' =>
          Fu.ret (r'.1, if r'.1.isEmpty then r.2 ++ r'.2 else [])

/-- The fill of an unpacking that types a `let` whose bound term has an
existential answer: the `let` itself when its body has no empty slot, the
unpacking otherwise, since the filled body may name the witness. -/
def letXFill {s : Sig} (ann : Option (ETy s)) (u : PTm (s,x)) (f1 : ATm s)
    (f2 : ATm ((s,c),x)) : ATm s :=
  match u.full? with
  | some b => .let ann f1 b
  | none => .letex f1 f2

/-! ## Ascriptions -/

/-- `(t : T)` from the candidates of `t` checked against `T` read at the
context, moved to the goal, as the typer's clause.  The fill keeps the written
`T`. -/
def ascE {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (T : Ty s) (G : Option (ETy s))
    (r : Fu (Out Γ)) : Fu (Out Γ) :=
  Fu.bind r fun r =>
    match firstCheckedE r.1 (.ty (readAt Γ ps T)) with
    | some (f, c) =>
        finishE Γ G [⟨.asc f T, ⟨.asc c.tm (readAt Γ ps T), c.uses, .ty (readAt Γ ps T), c.deriv⟩⟩]
    | none => Fu.ret ([], dropReasons r.1 r.2)

/-! ## Call arguments and `val` definitions

Two sites fill a bound term against a goal the typer does not pass it, and
then retype the filled `let` with the typer.  The typer synthesizes the bound
term of every `let`, so the variable is bound at the type the typer gives the
filled term, and a closure keeps its least set, as
`CheckCaptures.recheckClosure` types a closure at its own use set. -/

/-- Run `r`, the bound term elaborated against a goal, and hand the `let`
built by `mk` from the first candidate's fill to `inferF` with the goal `G`.
When this gives nothing on an unmarked tank, `gen` types the `let` as any
other, and the reasons of both are kept. -/
def fillThenF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s)) (r : Fu (Out Γ))
    (mk : ATm s → ATm s) (gen : Unit → Fu (Out Γ)) : Fu (Out Γ) :=
  orElseW (fun cs => !cs.isEmpty)
    (Fu.bind r fun r =>
      match r.1 with
      | c :: _ => fullInfer Γ ps (mk c.fill) G
      | [] => Fu.ret ([], r.2))
    gen

/-- A call argument `let z = t in g z`, whose bound term `t` has an empty
slot.  `arg E` elaborates `t` against the goal of the dominant formal of `g`
(`formalGoal`), as `FunProto.typedArg` types an argument against its formal.
The application clause of the typer then checks `z` against the formal, with
the callee's binder at `z`, and adapts a box.  With no dominant formal or no
goal, `gen` types the `let` as any other. -/
def argLetF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s)) (g : BVar s .var)
    (b : ATm (s,x)) (arg : ETy s → Fu (Out Γ)) (gen : Unit → Fu (Out Γ)) : Fu (Out Γ) :=
  Fu.bind (argGoalF Γ g) fun oF =>
    match oF.bind (formalGoal Γ) with
    | some T => fillThenF Γ ps G (arg (.ty T)) (fun f => .let none f b) gen
    | none => gen ()

/-- `let x : A = t in x`, the version's `val x : A = t`, whose bound term has
an empty slot.  `arg E` elaborates `t` against `A` read at the context, as
`typedValDef` types a right-hand side against the written type.  The typer
then checks `x` against `A`, as on the filled program.  An existential `A`
gives no goal, and `gen` types the `let` as any other. -/
def valLetF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (A : ETy s) (G : Option (ETy s))
    (u : ATm (s,x)) (arg : ETy s → Fu (Out Γ)) (gen : Unit → Fu (Out Γ)) : Fu (Out Γ) :=
  match readAns Γ ps A with
  | .ty T => fillThenF Γ ps G (arg (.ty T)) (fun f => .let (some A) f u) gen
  | .ex _ _ => gen ()

/-- A `let` whose body has no empty slot: a call argument when the resolver
inserted it at an operand, a `val` definition when it is written
`let x : A = t in x` with `A` in the notation, any other `let` otherwise. -/
def letF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (tag : LetTag) (ann : Option (ETy s))
    (u : PTm (s,x)) (G : Option (ETy s)) (arg : ETy s → Fu (Out Γ)) (gen : Unit → Fu (Out Γ)) :
    Fu (Out Γ) :=
  match argCallee? tag ann u, u.full? with
  | some g, some b => argLetF Γ ps G g b arg gen
  | none, some b =>
      match ann with
      | some A =>
          if u.isHere && (writtenAnsWhy A).isNone then valLetF Γ ps A G b arg gen else gen ()
      | none => gen ()
  | _, none => gen ()

/-! ## Object literals -/

/-- The definitions a probe binder holds.  No function of the typer reads the
definitions of a self binder, so any will do. -/
def probeDefs {s : Sig} : Defs s := .typ (.typ 0) .top

/-- The context in which the fields of a literal are elaborated: the class
root, then the self at the self shape read at the context, at the set of
every atom of the context.  A use of the self is then charged whenever the
literal's set can be nonempty, and the final check in the real context finds
the least set. -/
def probeCtx {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x)) : Ctx ((s,c),x) :=
  Γ.objBody probeDefs (readSelf Γ ps S) (allAtoms Γ)

/-- A literal with self shape `S`, its definitions filled by `defs`, then
typed by `inferF` with the goal.  A shape outside the notation is the typer's
reason. -/
def objSelfF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x)) (G : Option (ETy s))
    (defs : Fu (Option (ADefs ((s,c),x)) × List EReason)) : Fu (Out Γ) :=
  match writtenWhy ((Shape.mu S) ^ []) with
  | some r => Fu.ret ([], [.landed r])
  | none =>
      Fu.bind defs fun r =>
        match r.1 with
        | some d' => fullInfer Γ ps (.obj S d') G
        | none => Fu.ret ([], r.2)

/-! ## Self shapes formed from definitions

A literal without a self shape has it formed from its definitions, as the
completers of `Namer` type the members of a class.  A type member is known at
once at its right-hand side on both bounds, and a capture member at its set on
both bounds (`Namer.TypeDefCompleter.typeSig`).  A field with a written type is
known at once at it (`Namer.valOrDefDefSig`).  Every other field is typed on
demand (`Namer.inferredResultType`), in rounds.  `known` lists the fields typed
so far, by label.

The definitions live under the class root and the self, and the self shape
under the self alone.  So each member is moved out from under the class root
by a partial renaming `ρ`, the inverse of `Shape.underRoot` (`outOfRoot`).  A
member that names the class root cannot be moved.  No written member names it,
since no program writes its name. -/

/-- The first entry at a label. -/
def lookupL {β : Type} : List (Label × β) → Label → Option β
  | [], _ => none
  | (b, v) :: l, a => if a = b then some v else lookupL l a

/-- The partial renaming that moves a member of a literal out from under its
class root, the inverse of `Shape.underRoot`. -/
abbrev outOfRoot {s : Sig} : PartialRename ((s,c),x) (s,x) := PartialRename.unshift.lift

/-- The self shape the definitions have so far, each member moved by `ρ`.  A
field not yet typed, and a member that cannot be moved, are left out.  `none`
means that nothing is known. -/
def PDefs.partialSelf {s t : Sig} (ρ : PartialRename s t) :
    PDefs s → List (Label × Ty t) → Option (Shape t)
  | .typ A S, _ => (shapeRename? S ρ).map fun S' => .typ A S' S'
  | .cap C c, _ => (capRename? c ρ).map fun c' => .cap C c' c'
  | .trm a (some T) _, _ => (tyRename? T ρ).map (.fld a)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.partialSelf ρ known, e.partialSelf ρ known with
      | some S1, some S2 => some (.and S1 S2)
      | some S1, none => some S1
      | none, o => o

/-- The snapshot a round types its jobs against: the self shape known so
far, or `⊤` when nothing is. -/
def PDefs.probeSelf {s t : Sig} (ρ : PartialRename s t) (d : PDefs s)
    (known : List (Label × Ty t)) : Shape t :=
  (d.partialSelf ρ known).getD .top

/-- The self shape in lockstep with the definitions, each member moved by
`ρ`, once every field is typed: the shape `DefsTy` concludes and `checkDefsF`
reads, under the class root. -/
def PDefs.fullSelf {s t : Sig} (ρ : PartialRename s t) :
    PDefs s → List (Label × Ty t) → Option (Shape t)
  | .typ A S, _ => (shapeRename? S ρ).map fun S' => .typ A S' S'
  | .cap C c, _ => (capRename? c ρ).map fun c' => .cap C c' c'
  | .trm a (some T) _, _ => (tyRename? T ρ).map (.fld a)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.fullSelf ρ known, e.fullSelf ρ known with
      | some S1, some S2 => some (.and S1 S2)
      | _, _ => none

/-- `S` is the self shape of `d` in lockstep, each member moved by `ρ`.  A type
member gives its right-hand side on both bounds, a capture member its set on
both bounds, a field with a written type that type, any other field the first
type `known` gives its label, and an intersection of definitions the
intersection of their self shapes. -/
inductive Lockstep {s t : Sig} (ρ : PartialRename s t) (known : List (Label × Ty t)) :
    PDefs s → Shape t → Prop where
  /-- `{type A = S}` at `{A : S' .. S'}`, with `S'` the shape `S` moved. -/
  | typ (A : Label) (S : Shape s) (S' : Shape t) (h : shapeRename? S ρ = some S') :
      Lockstep ρ known (.typ A S) (.typ A S' S')
  /-- `{C^ = c}` at `{C^ : c' .. c'}`, with `c'` the set `c` moved. -/
  | cap (C : Label) (c : CaptureSet s) (c' : CaptureSet t) (h : capRename? c ρ = some c') :
      Lockstep ρ known (.cap C c) (.cap C c' c')
  /-- `{a : T = u}` at `{a : T'}`, with `T'` the type `T` moved. -/
  | written (a : Label) (T : Ty s) (T' : Ty t) (u : PTm s) (h : tyRename? T ρ = some T') :
      Lockstep ρ known (.trm a (some T) u) (.fld a T')
  /-- `{a = u}` at `{a : T}`, with `T` the type known at `a`. -/
  | inferred (a : Label) (T : Ty t) (u : PTm s) (h : lookupL known a = some T) :
      Lockstep ρ known (.trm a none u) (.fld a T)
  /-- `d1 ∧ d2` at `S1 ∧ S2`. -/
  | and {d1 d2 : PDefs s} {S1 S2 : Shape t} :
      Lockstep ρ known d1 S1 → Lockstep ρ known d2 S2 → Lockstep ρ known (.and d1 d2) (.and S1 S2)

/-- Every field of the definitions has a written type. -/
def PDefs.AllFieldsWritten {s : Sig} : PDefs s → Prop
  | .typ _ _ => True
  | .cap _ _ => True
  | .trm _ o _ => o.isSome = true
  | .and d e => d.AllFieldsWritten ∧ e.AllFieldsWritten

/-! ## Jobs

A job is a field without a written type.  It carries its elaboration as a
function of the context, so that a round can run it with the self bound at the
snapshot.  `jobsOf` takes the elaboration of a right-hand side as an argument,
so that the elaborator can make the jobs of a literal at the index it is
called at (`jobsF`). -/

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

/-- The jobs of a definition list: every field without a written type, in
source order, with its elaboration by `el`. -/
def jobsOf {s : Sig} (el : PTm s → (Γ : Ctx s) → Fu (Out Γ)) : PDefs s → List (Job s)
  | .typ _ _ => []
  | .cap _ _ => []
  | .trm _ (some _) _ => []
  | .trm a none t => [⟨a, t, el t⟩]
  | .and d1 d2 => jobsOf el d1 ++ jobsOf el d2

/-- A typed job of a literal in `s`: its label and right-hand side under the
class root and the self, the fill of its least candidate, and the type the
rounds chose, moved out from under the class root. -/
structure Done (s : Sig) where
  /-- The field's label. -/
  lbl : Label
  /-- The right-hand side. -/
  tm : PTm ((s,c),x)
  /-- The right-hand side with its empty slots filled. -/
  a : ATm ((s,c),x)
  /-- Its type in the self shape. -/
  ty : Ty (s,x)

/-- The fields typed so far, by label. -/
def Done.known {s : Sig} (ds : List (Done s)) : List (Label × Ty (s,x)) :=
  ds.map fun e => (e.lbl, e.ty)

/-! ## The least candidate

A field's type is the least answer of its candidates: the answer of the first
candidate that is below every other one by the answer goal, capture sets
included.  Every candidate is an answer of the right-hand side, so a use that
needs another one reaches it by subsumption.  The choice does not depend on
the order of an intersection.  The compiler meets the candidates with
`Denotation.meet`, which the version cannot derive for a term that is not a
variable, so candidates with no least one are rejected as ambiguous. -/

/-- `E` is below every answer of the list, or equal to it. -/
def belowAllF {s : Sig} (Γ : Ctx s) (E : ETy s) : List (ETy s) → Fu Bool
  | [] => Fu.ret true
  | F :: Fs =>
      if E = F then belowAllF Γ E Fs
      else
        Fu.bind (esubF Γ E F) fun o =>
          match o with
          | some _ => belowAllF Γ E Fs
          | none => Fu.ret false

/-- The first candidate of the list whose answer is below every answer of
`Es`. -/
def leastFromF {s : Sig} (Γ : Ctx s) (Es : List (ETy s)) :
    List (ECand Γ) → Fu (Option (ECand Γ))
  | [] => Fu.ret none
  | c :: rest =>
      Fu.bind (belowAllF Γ c.e.ans Es) fun b =>
        if b then Fu.ret (some c) else leastFromF Γ Es rest

/-- The least candidate: the first one whose answer is below the answer of
every candidate. -/
def leastCandF {s : Sig} (Γ : Ctx s) (cs : List (ECand Γ)) : Fu (Option (ECand Γ)) :=
  leastFromF Γ (cs.map (·.e.ans)) cs

/-- The type a field's answer gives the self shape: the answer moved out from
under the class root.  An existential answer, and a type that names the class
root, give none.  Both are a root capability in the field's type, which
`CheckCaptures.checkInferredResult` asks to be written, point (2). -/
def fieldTy? {s : Sig} : ETy ((s,c),x) → Option (Ty (s,x))
  | .ty T => tyRename? T outOfRoot
  | .ex _ _ => none

/-! ## Rounds

A round takes a snapshot of the self shape known so far and types every ready
job once, with no goal, in the probe context: the class root, then the self at
the snapshot read at the context, at the set of every atom of the context
(`probeCtx`).  A job is ready when none of the labels it projects off the self
is pending.  A job that uses the self any other way waits for the first round
in which no ready job lacks such a use.  So two such jobs do not see each
other, and a job that projects the field of one sees it.  The number of rounds
is an index, so the rounds are structural. -/

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

/-- A job of a literal in `Γ` typed against the snapshot `P`: its elaboration
in the probe context, and its type the least candidate's answer, moved out
from under the class root.  No candidate gives the reasons of the
elaboration, candidates with no least one give `ambiguous`, and a least
answer the self shape cannot hold gives `needsExplicitType`. -/
def runJobF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (P : Shape (s,x)) (j : Job ((s,c),x)) :
    Fu (Except (List EReason) (Done s)) :=
  Fu.bind (j.run (probeCtx Γ ps P)) fun r =>
    match r.1 with
    | [] => Fu.ret (.error r.2)
    | c :: cs =>
        Fu.bind (leastCandF (probeCtx Γ ps P) (c :: cs)) fun o =>
          match o with
          | some e =>
              match fieldTy? e.e.ans with
              | some T => Fu.ret (.ok ⟨j.lbl, j.tm, e.fill, T⟩)
              | none => Fu.ret (.error [.needsExplicitType j.lbl])
          | none => Fu.ret (.error [.ambiguous j.lbl])

/-- One round: the jobs typed against the snapshot `P`, in source order.  The
first failure stops it. -/
def roundF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (P : Shape (s,x)) :
    List (Job ((s,c),x)) → Fu (Except (List EReason) (List (Done s)))
  | [] => Fu.ret (.ok [])
  | j :: js =>
      Fu.bind (runJobF Γ ps P j) fun r =>
        match r with
        | .ok e =>
            Fu.bind (roundF Γ ps P js) fun r' =>
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
def roundsF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s)
    (probe : List (Label × Ty (s,x)) → Shape (s,x)) :
    Nat → List (Job ((s,c),x)) → List (Done s) → Fu (Except (List EReason) (List (Done s)))
  | _, [], done => Fu.ret (.ok done)
  | 0, j :: js, _ => Fu.ret (.error [stallReason (j :: js)])
  | n + 1, j :: js, done =>
      if ((j :: js).filter (picks (j :: js))).isEmpty then Fu.ret (.error [stallReason (j :: js)])
      else
        Fu.bind (roundF Γ ps (probe (Done.known done)) ((j :: js).filter (picks (j :: js))))
          fun r =>
            match r with
            | .ok new =>
                roundsF Γ ps probe n ((j :: js).filter fun k => !picks (j :: js) k) (done ++ new)
            | .error rs => Fu.ret (.error rs)

/-- The self shape of a literal in `Γ` formed from its definitions `d`, with
their jobs `js`: the rounds, then the self shape in lockstep, with the typed
jobs.  One round per job suffices, and one more stops. -/
def formSelfF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (d : PDefs ((s,c),x))
    (js : List (Job ((s,c),x))) : Fu (Except (List EReason) (Shape (s,x) × List (Done s))) :=
  Fu.bind (roundsF Γ ps (d.probeSelf outOfRoot) (js.length + 1) js []) fun r =>
    match r with
    | .ok done =>
        Fu.ret (match d.fullSelf outOfRoot (Done.known done) with
          | some S => .ok (S, done)
          | none => .error [.mismatch])
    | .error rs => Fu.ret (.error rs)

/-! ## The filled literal

Once the self shape is formed, the literal is filled and handed to `inferF`
in the real context, with the goal.  A field without a written type holds the
fill the rounds chose for it, so no such field is elaborated twice.  A field
with a written type and an empty slot is elaborated against that type, with
the self at the formed shape (`probeCtx`).  The typer then checks every field
once more, finds the least set and moves the literal to the goal. -/

/-- The fill the rounds chose for a label: that of the first typed job
there. -/
def doneAt {s : Sig} (done : List (Done s)) (a : Label) : Option (ATm ((s,c),x)) :=
  (done.find? fun e => decide (e.lbl = a)).map (·.a)

/-- A literal without a self shape at the goal `G`: the self shape formed by
`form`, the definitions filled at it by `fill`, then the filled literal typed
by `inferF` with the goal (`objSelfF`).  The reasons of the rounds or of the
filling reject it. -/
def objNoneF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (form : Fu (Except (List EReason) (Shape (s,x) × List (Done s))))
    (fill : Shape (s,x) → List (Done s) → Fu (Option (ADefs ((s,c),x)) × List EReason)) :
    Fu (Out Γ) :=
  Fu.bind form fun r =>
    match r with
    | .ok (S, done) => objSelfF Γ ps S G (fill S done)
    | .error rs => Fu.ret ([], rs)

/-! ## The elaborator -/

mutual

/-- The candidates of a partial term at an optional goal, structural on an
index that starts at the size of the term.  A term with no empty slot goes
to `inferF`.  At index zero the tank is marked. -/
def elabF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Nat → PTm s → Option (ETy s) → Fu (Out Γ)
  | 0, _, _ => markAs ([], [])
  | k + 1, p, G =>
      match p.full? with
      | some a => fullInfer Γ ps a G
      | none =>
          match p with
          | .lam (some T) t =>
              lamSomeF Γ T G (fun o => elabF (Γ.body (readDom T)) (psBody ps) k t o)
          | .lam none t =>
              lamNoneF Γ ps G t (fun D o => elabF (Γ.body (readDom D)) (psBody ps) k t o)
          | .obj (some S) d =>
              objSelfF Γ ps S G (elabDefsF (probeCtx Γ ps S) (psObj ps) k d (Shape.underRoot S)
                (Shape.underRoot (readSelf Γ ps S)))
          | .obj none d =>
              match G with
              | some E =>
                  Fu.bind (selfGoalF Γ E) fun oS =>
                    match oS with
                    | some S =>
                        orElseW (fun cs => !cs.isEmpty)
                          (objSelfF Γ ps S G (elabDefsF (probeCtx Γ ps S) (psObj ps) k d
                            (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S))))
                          (fun _ => objNoneF Γ ps G
                            (formSelfF Γ ps d (jobsOf (fun t Γ' => elabF Γ' (psObj ps) k t none) d))
                            fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
                              (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S')))
                    | none =>
                        objNoneF Γ ps G
                          (formSelfF Γ ps d (jobsOf (fun t Γ' => elabF Γ' (psObj ps) k t none) d))
                          fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
                            (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S'))
              | none =>
                  objNoneF Γ ps none
                    (formSelfF Γ ps d (jobsOf (fun t Γ' => elabF Γ' (psObj ps) k t none) d))
                    fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
                      (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S'))
          | .let tag ann t u =>
              letF Γ ps tag ann u G (fun E => elabF Γ ps k t (some E))
                (fun _ => letE Γ ps ann G (elabF Γ ps k t none)
                  (fun pe o => elabF (Γ.cons pe.ty) (psVar ps) k u o)
                  (fun q o => elabF ((Γ.consC).cons q.body) (psObj ps) k
                    (u.rename (Rename.succ (k := .cap)).lift) o)
                  (fun f1 f2 => .let ann f1 f2) (letXFill ann u))
          | .letex t u =>
              letexE Γ G (elabF Γ ps k t none)
                (fun q o => elabF ((Γ.consC).cons q.body) (psObj ps) k u o)
          | .asc t T =>
              match writtenWhy T with
              | some r => Fu.ret ([], [.landed r])
              | none => ascE Γ ps T G (elabF Γ ps k t (some (.ty (readAt Γ ps T))))
          | .path _ => Fu.ret ([], [.mismatch])
          | .app _ _ => Fu.ret ([], [.mismatch])
          | .proj _ _ => Fu.ret ([], [.mismatch])
          | .box _ => Fu.ret ([], [.mismatch])
          | .unbox _ _ => Fu.ret ([], [.mismatch])
termination_by structural k _ _ => k

/-- The definitions of a literal filled against its self shape under the
class root, in lockstep: `Sw` as written, for a written field type to agree
with, and `Sr` read at the context, for the goals.  A type or capture member
stays.  A field with no empty slot stays as written.  Any other field is
elaborated against its type in `Sr` and holds the first candidate's fill.  A
written field type must be the shape's.  No derivation is kept: the typer
checks the filled literal. -/
def elabDefsF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Nat → PDefs s → Shape s → Shape s → Fu (Option (ADefs s) × List EReason)
  | 0, _, _, _ => markAs (none, [])
  | _ + 1, .typ A S0, _, _ => Fu.ret (some (.typ A S0), [])
  | _ + 1, .cap C c, _, _ => Fu.ret (some (.cap C c), [])
  | k + 1, .trm a o t, .fld _ Tw, .fld _ Tr =>
      if optAgree o Tw then
        match t.full? with
        | some b => Fu.ret (some (.trm a b), [])
        | none =>
            Fu.bind (elabF Γ ps k t (some (.ty Tr))) fun r =>
              Fu.ret (r.1.head?.map fun c => ADefs.trm a c.fill, r.2)
      else Fu.ret (none, [.mismatch])
  | k + 1, .and d1 d2, .and S1 S2, .and R1 R2 =>
      Fu.bind (elabDefsF Γ ps k d1 S1 R1) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (elabDefsF Γ ps k d2 S2 R2) fun r2 =>
              Fu.ret (r2.1.map (ADefs.and e1), r2.2)
        | none => Fu.ret (none, r1.2)
  | _ + 1, _, _, _ => Fu.ret (none, [.mismatch])
termination_by structural k _ _ _ => k

/-- The definitions of a literal filled at its formed self shape under the
class root, in lockstep: `Sw` as formed, for a written field type to agree
with, and `Sr` read at the context, for the goals.  A type or capture member
stays.  A field without a written type holds the fill `look` gives its label.
A field with a written type holds its right-hand side when that has no empty
slot, and else the first candidate's fill of its elaboration against the
type.  No derivation is kept: the typer checks the filled literal. -/
def fillDefsF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (look : Label → Option (ATm s)) :
    Nat → PDefs s → Shape s → Shape s → Fu (Option (ADefs s) × List EReason)
  | 0, _, _, _ => markAs (none, [])
  | _ + 1, .typ A S0, _, _ => Fu.ret (some (.typ A S0), [])
  | _ + 1, .cap C c, _, _ => Fu.ret (some (.cap C c), [])
  | _ + 1, .trm a none _, _, _ =>
      match look a with
      | some b => Fu.ret (some (.trm a b), [])
      | none => Fu.ret (none, [.mismatch])
  | k + 1, .trm a (some T) t, .fld _ Tw, .fld _ Tr =>
      if T = Tw then
        match t.full? with
        | some b => Fu.ret (some (.trm a b), [])
        | none =>
            Fu.bind (elabF Γ ps k t (some (.ty Tr))) fun r =>
              Fu.ret (r.1.head?.map fun c => ADefs.trm a c.fill, r.2)
      else Fu.ret (none, [.mismatch])
  | k + 1, .and d1 d2, .and S1 S2, .and R1 R2 =>
      Fu.bind (fillDefsF Γ ps look k d1 S1 R1) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (fillDefsF Γ ps look k d2 S2 R2) fun r2 =>
              Fu.ret (r2.1.map (ADefs.and e1), r2.2)
        | none => Fu.ret (none, r1.2)
  | _ + 1, _, _, _ => Fu.ret (none, [.mismatch])
termination_by structural k _ _ _ => k

end

/-! ## The entry points -/

/-- The candidates of a partial term in `Γ` with no goal, from the index of
its size and a full tank of `n` units. -/
def elabInF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (p : PTm s) (n : Nat) : Out Γ × Tank :=
  elabF Γ ps (sizePTm p) p none ⟨n, false⟩

/-- The first candidate of a closed partial term over a platform, from a full
tank of `n` units, or the reason it is rejected, with the tank left. -/
def elabTopF (n : Nat) (π : PlatformNames) (p : PTm π.sig) :
    Except EReason (ECand π.plat.ctx) × Tank :=
  match elabInF π.plat.ctx π.set p n with
  | ((c :: _, _), t) => (if t.out then .error .limit else .ok c, t)
  | (([], rs), t) => (.error (Frontend.Reason.Reason.top t.out rs), t)

/-- The jobs of the definitions of a literal, each elaborated by `elabF` at
the index `k` with the platform set `ps` under the class root and the
self. -/
def jobsF {s : Sig} (ps : CaptureSet s) (k : Nat) (d : PDefs s) : List (Job s) :=
  jobsOf (fun t Γ => elabF Γ ps k t none) d

end CapturesCCFrontend

namespace CapturesCCFrontend

open Frontend.Fuel CapturesCCFrontend.Core
open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub
  SubShape Subcap ESub HasTy DefsTy Platform)
open scoped CapturesCC.DotMNF

/-! ## Every slot written

A term with no empty slot is the typer's: candidates, derivations and tank,
with the term itself as the fill. -/

theorem elabF_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) {p : PTm s} {a : ATm s}
    (h : p.full? = some a) (k : Nat) (G : Option (ETy s)) :
    elabF Γ ps (k + 1) p G = fullInfer Γ ps a G := by
  unfold elabF
  simp only [h]

theorem elabF_toI {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) (a : ATm s)
    (G : Option (ETy s)) : elabF Γ ps (k + 1) a.toI G = fullInfer Γ ps a G :=
  elabF_full Γ ps (ATm.full?_toI a) k G

/-- From the index the elaborator starts at, a term with every slot written
has the candidates of `synthF`, in its order, and leaves the same tank. -/
theorem elabInF_toI {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (n : Nat) :
    ((elabInF Γ ps a.toI n).1.1.map (·.e), (elabInF Γ ps a.toI n).2) =
      synthF Γ ps a ⟨n, false⟩ := by
  have hs : sizePTm a.toI = (sizeATm a - 1) + 1 := by
    rw [sizePTm_toI]
    have := sizeATm_pos a
    omega
  unfold elabInF
  rw [hs, elabF_toI]
  unfold fullInfer synthF
  simp only [Fu.bind, Fu.ret]
  cases inferF Γ ps (sizeATm a) a none ⟨n, false⟩ with
  | mk cs t =>
    simp only [List.map_map]
    exact Prod.ext (List.map_id' cs) rfl

/-! ## A lambda without a domain -/

theorem elabF_lam_none {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) (t : PTm (Sig.body s))
    (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.lam none t) G =
      lamNoneF Γ ps G t (fun D o => elabF (Γ.body (readDom D)) (psBody ps) k t o) := by
  rw [elabF]
  rfl

/-- Expansion leaves a type with no `any` as it is.  So `readDom` leaves a
domain copied from a read goal as it is. -/
theorem Ty.expand_noAny {s : Sig} (T : Ty s) (D : CaptureSet s) (h : T.noAny = true) :
    T.expand D = T :=
  CapturesCC.DotMNF.Ty.expand_of_noAny T h D

theorem readDom_noAny {s : Sig} {D : Dom s} (h : D.noAny = true) : readDom D = D :=
  Ty.expand_noAny D _ h

/-! ### The fills of a clause

`AllFills P x` says that every candidate `x` returns, from any tank, has a fill
`P` holds of. -/

/-- Every candidate of `x`, from any tank, has a fill `P` holds of. -/
def AllFills {s : Sig} {Γ : Ctx s} (P : ATm s → Prop) (x : Fu (Out Γ)) : Prop :=
  ∀ t, ∀ c ∈ (x t).1.1, P c.fill

section Fills

variable {s : Sig} {Γ : Ctx s} {P : ATm s → Prop}

theorem allFills_ret {l : List (ECand Γ)} {rs : List EReason} (h : ∀ c ∈ l, P c.fill) :
    AllFills P (Fu.ret (l, rs)) := fun _ c hc => h c hc

theorem allFills_bind' {α : Type} {x : Fu α} {f : α → Fu (Out Γ)}
    (h : ∀ t, AllFills P (f (x t).1)) : AllFills P (Fu.bind x f) := by
  intro t c hc
  simp only [Fu.bind] at hc
  have ht := h t
  cases hx : x t with
  | mk a t1 =>
    rw [hx] at hc ht
    exact ht t1 c hc

theorem allFills_bind {α : Type} {x : Fu α} {f : α → Fu (Out Γ)} (h : ∀ a, AllFills P (f a)) :
    AllFills P (Fu.bind x f) :=
  allFills_bind' fun t => h (x t).1

theorem allFills_orElseO {a b : Fu (Out Γ)} (ha : AllFills P a) (hb : AllFills P b) :
    AllFills P (orElseO a b) := by
  intro t c hc
  unfold orElseO at hc
  simp only [Fu.bind] at hc
  cases hA : a t with
  | mk r t1 =>
    rw [hA] at hc
    obtain ⟨l, rs⟩ := r
    cases l with
    | nil =>
      simp only at hc
      simp only [Fu.bind] at hc
      cases hB : b t1 with
      | mk r' t2 =>
        rw [hB] at hc
        have := hb t1 c
        rw [hB] at this
        exact this hc
    | cons c0 cs =>
      have := ha t c
      rw [hA] at this
      exact this hc

theorem allFills_flatMapR {α : Type} {f : α → Fu (Out Γ)} (h : ∀ x, AllFills P (f x)) :
    ∀ l : List α, AllFills P (flatMapR f l)
  | [] => allFills_ret fun _ hc => absurd hc List.not_mem_nil
  | x :: xs => by
    unfold flatMapR
    refine allFills_bind' fun t => allFills_bind' fun t' => ?_
    refine allFills_ret fun c hc => ?_
    rcases List.mem_append.mp hc with h1 | h2
    · exact h x t c h1
    · exact allFills_flatMapR h xs _ c h2

end Fills

/-- Every candidate of the checking route of a lambda is the lambda. -/
theorem lamCheckE_fills {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s)
    (C : CaptureSet s) (T1' : Dom s) (T2 : Cod s) (r : Out (Γ.body T)) :
    AllFills (fun f => ∃ b, f = .lam Tw b) (lamCheckE Γ T hwf Tw C T1' T2 r) := by
  unfold lamCheckE
  split
  · refine allFills_bind fun es => allFills_ret fun c hc => ?_
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
    exact ⟨_, rfl⟩
  · exact allFills_ret fun _ hc => absurd hc List.not_mem_nil

/-- Every candidate of the synthesis route of a lambda is the lambda. -/
theorem lamGenE_fills {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s)
    (G : Option (ETy s)) (r : Out (Γ.body T)) :
    AllFills (fun f => ∃ b, f = .lam Tw b) (lamGenE Γ T hwf Tw G r) := by
  unfold lamGenE
  refine allFills_bind' fun t => allFills_ret fun c hc => ?_
  refine allFills_flatMapR (P := fun f => ∃ b, f = .lam Tw b) (fun c0 => ?_) r.1 t c hc
  refine allFills_bind fun es => allFills_bind fun es' => allFills_ret fun c hc => ?_
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨_, rfl⟩

/-- Every candidate of a lambda whose body has an empty slot is the lambda at
its domain. -/
theorem lamAtF_fills {s : Sig} (Γ : Ctx s) (Tw : Dom s) (G : Option (ETy s)) (fp : FunPart s)
    (body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))) :
    AllFills (fun f => ∃ b, f = .lam Tw b) (lamAtF Γ Tw G fp body) := by
  unfold lamAtF
  split
  · exact allFills_ret fun _ hc => absurd hc List.not_mem_nil
  · split
    · refine allFills_orElseO ?_ (allFills_bind fun r => lamGenE_fills _ _ _ _ _ r)
      split
      · exact allFills_bind fun r => lamCheckE_fills _ _ _ _ _ _ _ r
      · exact allFills_bind fun r => lamGenE_fills _ _ _ _ _ r
      · exact allFills_ret fun _ hc => absurd hc List.not_mem_nil
    · exact allFills_ret fun _ hc => absurd hc List.not_mem_nil

/-! ## The goal of a call argument

The goal is one of the formals, and every formal is below it.  So the domain
a call argument or a callee's body takes is the least upper bound of the
formals, the compiler's choice, whenever that bound is a formal. -/

theorem allBelowF_sub {s : Sig} {Γ : Ctx s} {F : Dom s} :
    ∀ {Fs : List (Dom s)} {t t' : Tank}, allBelowF Γ F Fs t = (true, t') →
      ∀ F' ∈ Fs, Nonempty (Sub Γ.scope (Dom.underRoot F') (Dom.underRoot F))
  | [], _, _, _, F', hF' => absurd hF' List.not_mem_nil
  | F'' :: Fs, t, t', h, F', hF' => by
    unfold allBelowF at h
    cases hs : domSubF Γ F'' F t with
    | mk o t1 =>
      simp only [Fu.bind, hs] at h
      cases o with
      | some d =>
        rcases List.mem_cons.mp hF' with rfl | hm
        · exact ⟨d⟩
        · exact allBelowF_sub h F' hm
      | none => simp [Fu.ret] at h

theorem dominantF_sub {s : Sig} {Γ : Ctx s} {Fs : List (Dom s)} :
    ∀ {cands : List (Dom s)} {t : Tank} {F : Dom s} {t' : Tank},
      dominantF Γ Fs cands t = (some F, t') →
        F ∈ cands ∧ ∀ F' ∈ Fs, Nonempty (Sub Γ.scope (Dom.underRoot F') (Dom.underRoot F))
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
below it, as `SubShape.all` compares domains. -/
theorem argGoal_dominant {s : Sig} {Γ : Ctx s} {g : BVar s .var} {tk : Tank} {F : Dom s}
    (h : (argGoalF Γ g tk).1 = some F) :
    ∃ Fs tk', formalsF Γ g tk = (Fs, tk') ∧ F ∈ Fs ∧
      ∀ F' ∈ Fs, Nonempty (Sub Γ.scope (Dom.underRoot F') (Dom.underRoot F)) := by
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

/-- The goal a formal gives is the formal with its box stripped and its shape
moved out from under the callee's binder.  Its set is the formal's, moved out
the same way, when the formal's set does not name the binder. -/
theorem formalGoal_shape {s : Sig} {Γ : Ctx s} {F : Dom s} {T : Ty s}
    (h : formalGoal Γ F = some T) :
    ∃ C S C0, stripBox F = .capt C S.weaken ∧ T = .capt C0 S ∧
      ∀ C', capStrengthen? C = some C' → C0 = C' := by
  unfold formalGoal at h
  cases hF : stripBox F with
  | capt C S0 =>
    rw [hF] at h
    cases hS : shapeStrengthen? S0 with
    | none => simp [hS] at h
    | some S =>
      simp only [hS, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨C, S, _, by rw [shapeStrengthen?_sound hS], rfl, fun C' hC => ?_⟩
      simp [hC]

/-! ## A call argument and a `val` definition -/

/-- A call argument whose bound term has an empty slot takes the clause of
call arguments, with the bound term elaborated against the goal of the
dominant formal and, as the fallback, the clause of any other `let`. -/
theorem elabF_arg {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) {t : PTm s}
    (ht : t.full? = none) (g : BVar s .var) (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.let .arg none t (.app (.there g) .here)) G =
      argLetF Γ ps G g (.app (.there g) .here) (fun E => elabF Γ ps k t (some E))
        (fun _ => letE Γ ps none G (elabF Γ ps k t none)
          (fun pe o => elabF (Γ.cons pe.ty) (psVar ps) k (.app (.there g) .here) o)
          (fun q o => elabF ((Γ.consC).cons q.body) (psObj ps) k
            ((PTm.app (.there g) .here : PTm (s,x)).rename (Rename.succ (k := .cap)).lift) o)
          (fun f1 f2 => .let none f1 f2) (letXFill none (.app (.there g) .here))) := by
  rw [elabF]
  simp only [PTm.full?, ht]
  rfl

/-- `let x : A = t in x` with `A` in the notation and an empty slot in `t`
takes the clause of `val` definitions, with `t` elaborated against `A` and,
as the fallback, the clause of any other `let`. -/
theorem elabF_val {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) (tag : LetTag)
    {A : ETy s} (hA : writtenAnsWhy A = none) {t : PTm s} (ht : t.full? = none)
    (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.let tag (some A) t (.path (.var .here))) G =
      valLetF Γ ps A G (.path (.var .here)) (fun E => elabF Γ ps k t (some E))
        (fun _ => letE Γ ps (some A) G (elabF Γ ps k t none)
          (fun pe o => elabF (Γ.cons pe.ty) (psVar ps) k (.path (.var .here)) o)
          (fun q o => elabF ((Γ.consC).cons q.body) (psObj ps) k
            ((PTm.path (.var .here) : PTm (s,x)).rename (Rename.succ (k := .cap)).lift) o)
          (fun f1 f2 => .let (some A) f1 f2) (letXFill (some A) (.path (.var .here)))) := by
  rw [elabF]
  simp only [PTm.full?, ht]
  cases tag <;> simp [letF, argCallee?, PTm.isHere, hA, PTm.full?]

/-! ## The callee's body -/

theorem appHere?_eq {s : Sig} {t : PTm (s,x)} {g : BVar s .var} (h : appHere? t = some g) :
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

theorem appHere?_app {s : Sig} (g : BVar s .var) :
    appHere? (.app (.there g) .here : PTm (s,x)) = some g := rfl

theorem BVar.outer?_eq {s : Sig} {k0 k : Kind} {y : BVar (s,,k0) k} {z : BVar s k}
    (h : BVar.outer? y = some z) : y = .there z := by
  cases y with
  | here => cases h
  | there y' =>
    cases h
    rfl

/-- A body whose callee is `g` is `g x`, with `g` seen past the parameter,
the arrow binder and the root. -/
theorem calleeOf?_eq {s : Sig} {t : PTm (Sig.body s)} {g : BVar s .var}
    (h : calleeOf? t = some g) : t = .app (.there (.there (.there g))) .here := by
  unfold calleeOf? at h
  cases h1 : appHere? t with
  | none => simp [h1] at h
  | some g1 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    cases h2 : BVar.outer? g1 with
    | none => simp [h2] at h
    | some g2 =>
      rw [h2] at h
      simp only [Option.bind_some] at h
      rw [appHere?_eq h1, BVar.outer?_eq h2, BVar.outer?_eq h]

theorem calleeOf?_app {s : Sig} (g : BVar s .var) :
    calleeOf? (.app (.there (.there (.there g))) .here : PTm (Sig.body s)) = some g := rfl

/-- A body `g x` at a goal with no function part, or at no goal: the
elaborator is the typer on the lambda filled with the dominant formal of `g`,
candidates and tank. -/
theorem lam_callee_full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat} {g : BVar s .var}
    {G : Option (ETy s)} {tk tk1 tk2 : Tank} {D : Dom s} (hf : funPartOf Γ G tk = (.none, tk1))
    (h : argGoalF Γ g tk1 = (some D, tk2)) :
    elabF Γ ps (k + 1) (.lam none (.app (.there (.there (.there g))) .here)) G tk =
      fullInfer Γ ps (.lam D (.app (.there (.there (.there g))) .here)) G tk2 := by
  rw [elabF_lam_none]
  unfold lamNoneF
  simp only [Fu.bind, hf, FunPart.dom?]
  unfold lamCalleeF
  rw [calleeOf?_app]
  simp only [Fu.bind, h, PTm.full?]

/-- Every candidate of a lambda without a domain at no function part fills
it with the dominant formal of its body's callee. -/
theorem lamCalleeF_fills {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (t : PTm (Sig.body s)) (tk : Tank) :
    ∀ c ∈ (lamCalleeF Γ ps G t tk).1.1, ∃ g D f tk', calleeOf? t = some g ∧
      argGoalF Γ g tk = (some D, tk') ∧ c.fill = .lam D f := by
  intro c hc
  unfold lamCalleeF at hc
  cases hg : calleeOf? t with
  | none => simp [hg, Fu.ret] at hc
  | some g =>
    simp only [hg, Fu.bind] at hc
    cases hA : argGoalF Γ g tk with
    | mk o tk' =>
      rw [hA] at hc
      cases o with
      | none => simp [Fu.ret] at hc
      | some D =>
        cases hb : t.full? with
        | none => simp [hb, Fu.ret] at hc
        | some b =>
          simp only [hb, fullInfer, Fu.bind, Fu.ret] at hc
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
          exact ⟨g, D, b, tk', rfl, hA, rfl⟩

/-- A filled domain is the domain of the goal's function part, or, where the
goal has none, the dominant formal of the callee of a body `g x`: every
candidate of a lambda without a domain fills it with that domain, which
`readDom` leaves as it is when it holds no `any`. -/
theorem elabF_lam_formal {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    {t : PTm (Sig.body s)} {G : Option (ETy s)} {tk : Tank} {c : ECand Γ}
    (h : c ∈ (elabF Γ ps (k + 1) (.lam none t) G tk).1.1) :
    ∃ fp tk' D f, funPartOf Γ G tk = (fp, tk') ∧ c.fill = .lam D f ∧
      (fp.dom? = some D ∨
        ∃ g tk'', fp = .none ∧ calleeOf? t = some g ∧ argGoalF Γ g tk' = (some D, tk'')) ∧
      (D.noAny = true → readDom D = D) := by
  rw [elabF_lam_none] at h
  unfold lamNoneF at h
  simp only [Fu.bind] at h
  cases hf : funPartOf Γ G tk with
  | mk fp tk' =>
    rw [hf] at h
    cases hd : fp.dom? with
    | none =>
      rw [hd] at h
      cases fp with
      | none =>
        obtain ⟨g, D, f, tk'', hg, hA, hfill⟩ := lamCalleeF_fills Γ ps G t tk' c h
        exact ⟨.none, tk', D, f, rfl, hfill, .inr ⟨g, tk'', rfl, hg, hA⟩, readDom_noAny⟩
      | bad => simp [Fu.ret] at h
      | direct _ _ _ => simp [FunPart.dom?] at hd
      | side _ _ => simp [FunPart.dom?] at hd
    | some D =>
      rw [hd] at h
      simp only at h
      refine ⟨fp, tk', D, ?_⟩
      cases hb : t.full? with
      | some b =>
        rw [hb] at h
        simp only [fullInfer, Fu.bind, Fu.ret] at h
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp h
        exact ⟨b, rfl, rfl, .inl hd, readDom_noAny⟩
      | none =>
        rw [hb] at h
        obtain ⟨b, hb⟩ := lamAtF_fills Γ D G fp _ tk' c h
        exact ⟨b, rfl, hb, .inl hd, readDom_noAny⟩

/-! ## The index of the typer

`inferF` answers the same at every index from the size of the term up: every
recursive call is at a subterm, or at the body of a `let` renamed past the
witness binder, which has the same size. -/

theorem inferF_index_both : ∀ (n : Nat),
    (∀ {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (G : Option (ETy s)) (m : Nat),
      sizeATm a ≤ n → sizeATm a ≤ m → inferF Γ ps n a G = inferF Γ ps m a G) ∧
    (∀ {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (d : ADefs s) (S : Shape s) (m : Nat),
      sizeADefs d ≤ n → sizeADefs d ≤ m → checkDefsF Γ ps n d S = checkDefsF Γ ps m d S)
  | 0 =>
    ⟨fun _ _ a _ _ h _ => absurd h (Nat.not_le.mpr (sizeATm_pos a)),
     fun _ _ d _ _ h _ => absurd h (Nat.not_le.mpr (sizeADefs_pos d))⟩
  | n + 1 => by
    have ih := inferF_index_both n
    refine ⟨?_, ?_⟩
    · intro s Γ ps a G m hn hm
      cases m with
      | zero => exact absurd hm (Nat.not_le.mpr (sizeATm_pos a))
      | succ m =>
        cases a with
        | path p => cases p; simp only [inferF]
        | lam T t =>
          simp only [sizeATm] at hn hm
          have ht : ∀ (Γ' : Ctx (Sig.body s)) ps' G',
              inferF Γ' ps' n t G' = inferF Γ' ps' m t G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' t G' m (by omega) (by omega)
          simp only [inferF, ht]
        | obj S d =>
          simp only [sizeATm] at hn hm
          have hd : ∀ (Γ' : Ctx ((s,c),x)) ps' S',
              checkDefsF Γ' ps' n d S' = checkDefsF Γ' ps' m d S' :=
            fun Γ' ps' S' => ih.2 Γ' ps' d S' m (by omega) (by omega)
          simp only [inferF, hd]
        | app x y => simp only [inferF]
        | proj x a => simp only [inferF]
        | «let» ann t u =>
          simp only [sizeATm] at hn hm
          have ht : ∀ (Γ' : Ctx s) ps' G', inferF Γ' ps' n t G' = inferF Γ' ps' m t G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' t G' m (by omega) (by omega)
          have hu : ∀ (Γ' : Ctx (s,x)) ps' G', inferF Γ' ps' n u G' = inferF Γ' ps' m u G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' u G' m (by omega) (by omega)
          have hu' : ∀ (Γ' : Ctx ((s,c),x)) ps' G',
              inferF Γ' ps' n (u.rename (Rename.succ (k := .cap)).lift) G' =
                inferF Γ' ps' m (u.rename (Rename.succ (k := .cap)).lift) G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' _ G' m (by rw [sizeATm_rename]; omega)
              (by rw [sizeATm_rename]; omega)
          simp only [inferF, ht, hu, hu']
        | letex t u =>
          simp only [sizeATm] at hn hm
          have ht : ∀ (Γ' : Ctx s) ps' G', inferF Γ' ps' n t G' = inferF Γ' ps' m t G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' t G' m (by omega) (by omega)
          have hu : ∀ (Γ' : Ctx ((s,c),x)) ps' G', inferF Γ' ps' n u G' = inferF Γ' ps' m u G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' u G' m (by omega) (by omega)
          simp only [inferF, ht, hu]
        | box x => simp only [inferF]
        | unbox C x => simp only [inferF]
        | asc t T =>
          simp only [sizeATm] at hn hm
          have ht : ∀ (Γ' : Ctx s) ps' G', inferF Γ' ps' n t G' = inferF Γ' ps' m t G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' t G' m (by omega) (by omega)
          simp only [inferF, ht]
    · intro s Γ ps d S m hn hm
      cases m with
      | zero => exact absurd hm (Nat.not_le.mpr (sizeADefs_pos d))
      | succ m =>
        cases d with
        | typ A S0 => cases S <;> simp only [checkDefsF]
        | cap C c => cases S <;> simp only [checkDefsF]
        | trm a t =>
          simp only [sizeADefs] at hn hm
          have ht : ∀ (Γ' : Ctx s) ps' G', inferF Γ' ps' n t G' = inferF Γ' ps' m t G' :=
            fun Γ' ps' G' => ih.1 Γ' ps' t G' m (by omega) (by omega)
          cases S <;> simp only [checkDefsF, ht]
        | and d1 d2 =>
          simp only [sizeADefs] at hn hm
          have h1 : ∀ (Γ' : Ctx s) ps' S',
              checkDefsF Γ' ps' n d1 S' = checkDefsF Γ' ps' m d1 S' :=
            fun Γ' ps' S' => ih.2 Γ' ps' d1 S' m (by omega) (by omega)
          have h2 : ∀ (Γ' : Ctx s) ps' S',
              checkDefsF Γ' ps' n d2 S' = checkDefsF Γ' ps' m d2 S' :=
            fun Γ' ps' S' => ih.2 Γ' ps' d2 S' m (by omega) (by omega)
          cases S <;> simp only [checkDefsF, h1, h2]

/-- The typer answers at every index from the size of the term as at the
size: candidates and tank. -/
theorem inferF_index {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s} {G : Option (ETy s)}
    {k : Nat} (h : sizeATm a ≤ k) : inferF Γ ps k a G = inferF Γ ps (sizeATm a) a G :=
  (inferF_index_both k).1 Γ ps a G (sizeATm a) h (Nat.le_refl _)

/-- The same for definitions checked against a declaration shape. -/
theorem checkDefsF_index {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {d : ADefs s} {S : Shape s}
    {k : Nat} (h : sizeADefs d ≤ k) :
    checkDefsF Γ ps k d S = checkDefsF Γ ps (sizeADefs d) d S :=
  (inferF_index_both k).2 Γ ps d S (sizeADefs d) h (Nat.le_refl _)

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

end CombinatorFrames

theorem fullInfer_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (G : Option (ETy s)) : Framed (fullInfer Γ ps a G) :=
  bind_framed (inferF_framed Γ ps _ a G) fun _ => ret_framed _

theorem orElseO_framed {s : Sig} {Γ : Ctx s} {a b : Fu (Out Γ)} (ha : Framed a) (hb : Framed b) :
    Framed (orElseO a b) := by
  refine bind_framed ha fun r => ?_
  obtain ⟨l, rs⟩ := r
  cases l with
  | nil => exact bind_framed hb fun _ => ret_framed _
  | cons _ _ => exact ret_framed _

theorem finishE_framed {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (cs : List (ECand Γ)) :
    Framed (finishE Γ G cs) := by
  cases G with
  | none => exact ret_framed _
  | some E =>
    unfold finishE
    exact bind_framed (flatMapL_framed (fun _ => mapL_framed _ (subsumeF_framed _ _ _)) _)
      fun _ => ret_framed _

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
  refine bind_framed (domSubF_framed _ _ _) fun o2 => ?_
  cases o2 with
  | some _ => exact ret_framed _
  | none =>
    refine bind_framed (domSubF_framed _ _ _) fun o1 => ?_
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

theorem funPartOf_framed {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) :
    Framed (funPartOf Γ G) := by
  rcases G with _ | (⟨C, S⟩ | ⟨C, T⟩)
  · exact ret_framed _
  · cases S <;> first | exact ret_framed _ | exact funPartAt_framed Γ _
  · exact ret_framed _

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

theorem selfGoalF_framed {s : Sig} (Γ : Ctx s) (E : ETy s) : Framed (selfGoalF Γ E) := by
  rcases E with ⟨C, S⟩ | ⟨C, T⟩
  · unfold selfGoalF
    refine bind_framed (dealiasAt_framed Γ S) fun S' => ?_
    cases S' <;> exact ret_framed _
  · exact ret_framed _

theorem formalsF_framed {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Framed (formalsF Γ g) := by
  refine bind_framed (fnViewsF_framed _ _) fun fs => ?_
  cases fs with
  | nil => exact bind_framed (boxViewsF_framed _ _) fun _ => ret_framed _
  | cons _ _ => exact ret_framed _

theorem allBelowF_framed {s : Sig} (Γ : Ctx s) (F : Dom s) : ∀ Fs, Framed (allBelowF Γ F Fs)
  | [] => ret_framed _
  | F' :: Fs => by
    refine bind_framed (domSubF_framed _ _ _) fun o => ?_
    cases o with
    | some _ => exact allBelowF_framed Γ F Fs
    | none => exact ret_framed _

theorem dominantF_framed {s : Sig} (Γ : Ctx s) (Fs : List (Dom s)) :
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

theorem lamCheckE_framed {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s)
    (C : CaptureSet s) (T1' : Dom s) (T2 : Cod s) (r : Out (Γ.body T)) :
    Framed (lamCheckE Γ T hwf Tw C T1' T2 r) := by
  unfold lamCheckE
  split
  · exact bind_framed (lamCheckF_framed _ _ _ _ _ _ _) fun _ => ret_framed _
  · exact ret_framed _

theorem lamGenE_framed {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s)
    (G : Option (ETy s)) (r : Out (Γ.body T)) : Framed (lamGenE Γ T hwf Tw G r) :=
  bind_framed (flatMapR_framed (fun _ => bind_framed (lamGenF_framed _ _ _ _) fun _ =>
    bind_framed (finishF_framed _ _ _) fun _ => ret_framed _) _) fun _ => ret_framed _

theorem lamAtF_framed {s : Sig} (Γ : Ctx s) (Tw : Dom s) (G : Option (ETy s)) (fp : FunPart s)
    {body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))}
    (hb : ∀ o, Framed (body o)) : Framed (lamAtF Γ Tw G fp body) := by
  unfold lamAtF
  split
  · exact ret_framed _
  · refine dite_framed (fun hwf => orElseO_framed ?_ ?_) (fun _ => ret_framed _)
    · split
      · exact bind_framed (hb _) fun r => lamCheckE_framed _ _ _ _ _ _ _ r
      · exact bind_framed (hb _) fun r => lamGenE_framed _ _ _ _ _ r
      · exact ret_framed _
    · exact bind_framed (hb _) fun r => lamGenE_framed _ _ _ _ _ r

theorem lamSomeF_framed {s : Sig} (Γ : Ctx s) (Tw : Dom s) (G : Option (ETy s))
    {body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))}
    (hb : ∀ o, Framed (body o)) : Framed (lamSomeF Γ Tw G body) :=
  bind_framed (funPartOf_framed _ _) fun fp => lamAtF_framed _ _ _ fp hb

theorem lamCalleeF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (t : PTm (Sig.body s)) : Framed (lamCalleeF Γ ps G t) := by
  unfold lamCalleeF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oD => ?_
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  · exact ret_framed _

theorem lamNoneF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (t : PTm (Sig.body s))
    {body : (D : Dom s) → Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom D)))}
    (hb : ∀ D o, Framed (body D o)) : Framed (lamNoneF Γ ps G t body) := by
  refine bind_framed (funPartOf_framed _ _) fun fp => ?_
  dsimp only
  split
  · split
    · exact fullInfer_framed _ _ _ _
    · exact lamAtF_framed _ _ _ _ (hb _)
  · split
    · exact ret_framed _
    · exact lamCalleeF_framed _ _ _ _

theorem letPairsE_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    (mk : ATm (s,x) → ATm s) {body : Fu (Out (Γ.cons p.ty))} (hb : Framed body) :
    Framed (letPairsE Γ ann p mk body) :=
  bind_framed hb fun _ => bind_framed (flatMapL_framed (fun _ =>
    mapL_framed _ (letFinishF_framed _ _ _ _)) _) fun _ => ret_framed _

theorem letexPairsE_framed {s : Sig} (Γ : Ctx s) (q : XElab Γ) (mkX : ATm ((s,c),x) → ATm s)
    {body : Fu (Out ((Γ.consC).cons q.body))} (hb : Framed body) :
    Framed (letexPairsE Γ q mkX body) :=
  bind_framed hb fun _ => bind_framed (flatMapL_framed (fun _ =>
    mapL_framed _ (letexFinishF_framed _ _ _)) _) fun _ => ret_framed _

theorem letBoundE_framed {s : Sig} (Γ : Ctx s) (c1 : ECand Γ) {bp : BodyPE Γ} {bx : BodyXE Γ}
    (hp : ∀ p o, Framed (bp p o)) (hx : ∀ q o, Framed (bx q o))
    (mk : ATm s → ATm (s,x) → ATm s) (mkX : ATm s → ATm ((s,c),x) → ATm s) :
    Framed (letBoundE Γ c1 bp bx mk mkX) := by
  unfold letBoundE
  split
  · exact letPairsE_framed _ _ _ _ (hp _ _)
  · exact letexPairsE_framed _ _ _ (hx _ _)

theorem letOneE_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (E : ETy s) (c1 : ECand Γ)
    {bp : BodyPE Γ} {bx : BodyXE Γ} (hp : ∀ p o, Framed (bp p o)) (hx : ∀ q o, Framed (bx q o))
    (mk : ATm s → ATm (s,x) → ATm s) (mkX : ATm s → ATm ((s,c),x) → ATm s) :
    Framed (letOneE Γ ann E c1 bp bx mk mkX) := by
  unfold letOneE
  split
  · refine ite_framed (bind_framed (hp _ _) fun r2 => ?_) (ret_framed _)
    dsimp only
    split
    · exact bind_framed (letAtF_framed _ _ _ _ _) fun _ => ret_framed _
    · exact ret_framed _
  · split
    · exact bind_framed (letPairsE_framed _ _ _ _ (hp _ _)) fun _ =>
        bind_framed (firstSome_framed (fun _ => mapO_framed _ (subsumeF_framed _ _ _)) _)
          fun _ => ret_framed _
    · exact ret_framed _
  · refine bind_framed (hx _ _) fun r2 => ?_
    dsimp only
    split
    · exact bind_framed (letexOfF_framed _ _ _ _) fun _ => ret_framed _
    · exact ret_framed _

theorem letE_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (ann : Option (ETy s))
    (G : Option (ETy s)) {bound : Fu (Out Γ)} {bp : BodyPE Γ} {bx : BodyXE Γ}
    (hbound : Framed bound) (hp : ∀ p o, Framed (bp p o)) (hx : ∀ q o, Framed (bx q o))
    (mk : ATm s → ATm (s,x) → ATm s) (mkX : ATm s → ATm ((s,c),x) → ATm s) :
    Framed (letE Γ ps ann G bound bp bx mk mkX) := by
  refine bind_framed hbound fun r1 => ite_framed (ret_framed _) ?_
  cases ann with
  | none =>
    refine orElseO_framed ?_ ?_
    · cases G with
      | some E =>
        exact bind_framed (firstSomeR_framed (fun _ => letOneE_framed _ _ _ _ hp hx _ _) _)
          fun _ => ret_framed _
      | none => exact ret_framed _
    · exact bind_framed (flatMapR_framed (fun _ => letBoundE_framed _ _ hp hx _ _) _) fun _ =>
        bind_framed (finishE_framed _ _ _) fun _ => ret_framed _
  | some A =>
    dsimp only
    split
    · exact ret_framed _
    · exact bind_framed (firstSomeR_framed (fun _ => letOneE_framed _ _ _ _ hp hx _ _) _)
        fun _ => bind_framed (finishE_framed _ _ _) fun _ => ret_framed _

theorem letexE_framed {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) {bound : Fu (Out Γ)}
    {bx : BodyXE Γ} (hbound : Framed bound) (hx : ∀ q o, Framed (bx q o)) :
    Framed (letexE Γ G bound bx) := by
  refine bind_framed hbound fun r1 => ite_framed (ret_framed _)
    (bind_framed (flatMapR_framed (fun c1 => ?_) _) fun _ =>
      bind_framed (finishE_framed _ _ _) fun _ => ret_framed _)
  dsimp only
  split
  · exact letexPairsE_framed _ _ _ (hx _ _)
  · exact ret_framed _

theorem ascE_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (T : Ty s) (G : Option (ETy s))
    {r : Fu (Out Γ)} (hr : Framed r) : Framed (ascE Γ ps T G r) := by
  refine bind_framed hr fun r => ?_
  dsimp only
  split
  · exact finishE_framed _ _ _
  · exact ret_framed _

theorem fillThenF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    {r : Fu (Out Γ)} (mk : ATm s → ATm s) {gen : Unit → Fu (Out Γ)} (hr : Framed r)
    (hgen : Framed (gen ())) : Framed (fillThenF Γ ps G r mk gen) := by
  refine orElseW_framed (bind_framed hr fun r => ?_) hgen
  dsimp only
  split
  · exact fullInfer_framed _ _ _ _
  · exact ret_framed _

theorem argLetF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (g : BVar s .var) (b : ATm (s,x)) {arg : ETy s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ E, Framed (arg E)) (hgen : Framed (gen ())) :
    Framed (argLetF Γ ps G g b arg gen) := by
  refine bind_framed (argGoalF_framed _ _) fun oF => ?_
  dsimp only
  split
  · exact fillThenF_framed _ _ _ _ (harg _) hgen
  · exact hgen

theorem valLetF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (A : ETy s) (G : Option (ETy s))
    (u : ATm (s,x)) {arg : ETy s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (harg : ∀ E, Framed (arg E)) (hgen : Framed (gen ())) :
    Framed (valLetF Γ ps A G u arg gen) := by
  unfold valLetF
  split
  · exact fillThenF_framed _ _ _ _ (harg _) hgen
  · exact hgen

theorem letF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (tag : LetTag)
    (ann : Option (ETy s)) (u : PTm (s,x)) (G : Option (ETy s)) {arg : ETy s → Fu (Out Γ)}
    {gen : Unit → Fu (Out Γ)} (harg : ∀ E, Framed (arg E)) (hgen : Framed (gen ())) :
    Framed (letF Γ ps tag ann u G arg gen) := by
  unfold letF
  split
  · exact argLetF_framed _ _ _ _ _ harg hgen
  · split
    · exact ite_framed (valLetF_framed _ _ _ _ _ harg hgen) hgen
    · exact hgen
  · exact hgen

theorem objSelfF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (G : Option (ETy s)) {defs : Fu (Option (ADefs ((s,c),x)) × List EReason)}
    (hd : Framed defs) : Framed (objSelfF Γ ps S G defs) := by
  unfold objSelfF
  split
  · exact ret_framed _
  · refine bind_framed hd fun r => ?_
    dsimp only
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _

/-! ## The frame lemmas of the rounds

The rounds keep a marked tank, never add fuel, and do the same with more fuel,
when every job's elaboration does. -/

theorem belowAllF_framed {s : Sig} (Γ : Ctx s) (E : ETy s) : ∀ Fs, Framed (belowAllF Γ E Fs)
  | [] => ret_framed _
  | F :: Fs => by
    unfold belowAllF
    split
    · exact belowAllF_framed Γ E Fs
    · refine bind_framed (esubF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact belowAllF_framed Γ E Fs
      | none => exact ret_framed _

theorem leastFromF_framed {s : Sig} (Γ : Ctx s) (Es : List (ETy s)) :
    ∀ cs : List (ECand Γ), Framed (leastFromF Γ Es cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed Γ c.e.ans Es) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromF_framed Γ Es rest

theorem leastCandF_framed {s : Sig} (Γ : Ctx s) (cs : List (ECand Γ)) :
    Framed (leastCandF Γ cs) :=
  leastFromF_framed Γ _ cs

theorem runJobF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (P : Shape (s,x))
    {j : Job ((s,c),x)} (hj : ∀ Γ', Framed (j.run Γ')) : Framed (runJobF Γ ps P j) := by
  refine bind_framed (hj _) fun r => ?_
  split
  · exact ret_framed _
  · refine bind_framed (leastCandF_framed _ _) fun o => ?_
    cases o with
    | some e =>
      dsimp only
      split
      · exact ret_framed _
      · exact ret_framed _
    | none => exact ret_framed _

theorem roundF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (P : Shape (s,x)) :
    ∀ (js : List (Job ((s,c),x))), (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) →
      Framed (roundF Γ ps P js)
  | [], _ => ret_framed _
  | j :: js, hj => by
    refine bind_framed (runJobF_framed Γ ps P (hj j (List.mem_cons_self ..))) fun r => ?_
    cases r with
    | ok e =>
      refine bind_framed (roundF_framed Γ ps P js fun j' h' => hj j' (List.mem_cons_of_mem _ h'))
        fun r' => ?_
      cases r' with
      | ok _ => exact ret_framed _
      | error _ => exact ret_framed _
    | error _ => exact ret_framed _

/-- The rounds are framed when every job's elaboration is. -/
theorem roundsF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s)
    (probe : List (Label × Ty (s,x)) → Shape (s,x)) :
    ∀ (n : Nat) (js : List (Job ((s,c),x))) (known : List (Done s)),
      (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundsF Γ ps probe n js known)
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
    · refine bind_framed (roundF_framed Γ ps _ _ fun j' h' => hj j' (List.mem_filter.mp h').1)
        fun r => ?_
      cases r with
      | ok new =>
        exact roundsF_framed Γ ps probe n _ _ fun j' h' => hj j' (List.mem_filter.mp h').1
      | error _ => exact ret_framed _

theorem formSelfF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (d : PDefs ((s,c),x))
    {js : List (Job ((s,c),x))} (hj : ∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) :
    Framed (formSelfF Γ ps d js) := by
  refine bind_framed (roundsF_framed Γ ps _ _ js [] hj) fun r => ?_
  cases r with
  | ok _ => exact ret_framed _
  | error _ => exact ret_framed _

/-- The jobs of a definition list are framed when the elaboration they carry
is. -/
theorem jobsOf_framed {s : Sig} {el : PTm s → (Γ : Ctx s) → Fu (Out Γ)}
    (hel : ∀ t Γ, Framed (el t Γ)) : (d : PDefs s) → ∀ j ∈ jobsOf el d, ∀ Γ, Framed (j.run Γ)
  | .typ _ _ => by
    intro j hj
    simp only [jobsOf, List.not_mem_nil] at hj
  | .cap _ _ => by
    intro j hj
    simp only [jobsOf, List.not_mem_nil] at hj
  | .trm _ (some _) _ => by
    intro j hj
    simp only [jobsOf, List.not_mem_nil] at hj
  | .trm a none t => by
    intro j hj Γ
    simp only [jobsOf, List.mem_singleton] at hj
    subst hj
    exact hel t Γ
  | .and d1 d2 => by
    intro j hj Γ
    simp only [jobsOf, List.mem_append] at hj
    rcases hj with h | h
    · exact jobsOf_framed hel d1 j h Γ
    · exact jobsOf_framed hel d2 j h Γ

theorem objNoneF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    {form : Fu (Except (List EReason) (Shape (s,x) × List (Done s)))}
    {fill : Shape (s,x) → List (Done s) → Fu (Option (ADefs ((s,c),x)) × List EReason)}
    (hf : Framed form) (hl : ∀ S done, Framed (fill S done)) :
    Framed (objNoneF Γ ps G form fill) := by
  refine bind_framed hf fun r => ?_
  cases r with
  | ok p =>
    obtain ⟨S, done⟩ := p
    exact objSelfF_framed _ _ _ _ (hl S done)
  | error _ => exact ret_framed _

/-! ## The frame lemmas of the elaborator -/

mutual

theorem elabF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    (k : Nat) → (p : PTm s) → (G : Option (ETy s)) → Framed (elabF Γ ps k p G)
  | 0, p, G => by
    rw [elabF.eq_1]
    exact markAs_framed _
  | k + 1, .path q, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  | k + 1, .app x y, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  | k + 1, .proj x a, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  | k + 1, .box x, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  | k + 1, .unbox C x, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact ret_framed _
  | k + 1, .lam (some T) t, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact lamSomeF_framed _ _ _ fun o => elabF_framed _ _ k t o
  | k + 1, .lam none t, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact lamNoneF_framed _ _ _ _ fun D o => elabF_framed _ _ k t o
  | k + 1, .obj (some S) d, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact objSelfF_framed _ _ _ _ (elabDefsF_framed _ _ k d _ _)
  | k + 1, .obj none d, G => by
    rw [elabF.eq_def]
    dsimp only
    split
    · exact fullInfer_framed _ _ _ _
    · have hn : ∀ G', Framed (objNoneF Γ ps G'
          (formSelfF Γ ps d (jobsOf (fun t Γ' => elabF Γ' (psObj ps) k t none) d))
          fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
            (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S'))) := fun G' =>
        objNoneF_framed _ _ _
          (formSelfF_framed _ _ d (jobsOf_framed (fun t Γ' => elabF_framed Γ' _ k t none) d))
          fun S' done => fillDefsF_framed _ _ _ k d _ _
      cases G with
      | none => exact hn none
      | some E =>
        refine bind_framed (selfGoalF_framed _ _) fun oS => ?_
        cases oS with
        | some S =>
          exact orElseW_framed (objSelfF_framed _ _ _ _ (elabDefsF_framed _ _ k d _ _)) (hn _)
        | none => exact hn _
  | k + 1, .let tag ann t u, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact letF_framed _ _ _ _ _ _ (fun _ => elabF_framed _ _ k t _)
        (letE_framed _ _ _ _ (elabF_framed _ _ k t _) (fun _ _ => elabF_framed _ _ k u _)
          (fun _ _ => elabF_framed _ _ k _ _) _ _)
  | k + 1, .letex t u, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · exact letexE_framed _ _ (elabF_framed _ _ k t _) fun _ _ => elabF_framed _ _ k u _
  | k + 1, .asc t T, G => by
    rw [elabF]
    split
    · exact fullInfer_framed _ _ _ _
    · split
      · exact ret_framed _
      · exact ascE_framed _ _ _ _ (elabF_framed _ _ k t _)

theorem elabDefsF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    (k : Nat) → (d : PDefs s) → (Sw Sr : Shape s) → Framed (elabDefsF Γ ps k d Sw Sr)
  | 0, d, Sw, Sr => by
    rw [elabDefsF]
    exact markAs_framed _
  | k + 1, .typ A S0, Sw, Sr => by
    rw [elabDefsF]
    exact ret_framed _
  | k + 1, .cap C c, Sw, Sr => by
    rw [elabDefsF]
    exact ret_framed _
  | k + 1, .trm a o t, Sw, Sr => by
    cases Sw with
    | fld b Tw =>
      cases Sr with
      | fld c Tr =>
        rw [elabDefsF]
        refine ite_framed ?_ (ret_framed _)
        split
        · exact ret_framed _
        · exact bind_framed (elabF_framed _ _ k t _) fun _ => ret_framed _
      | _ => simp only [elabDefsF]; exact ret_framed _
    | _ => simp only [elabDefsF]; exact ret_framed _
  | k + 1, .and d1 d2, Sw, Sr => by
    cases Sw with
    | and S1 S2 =>
      cases Sr with
      | and R1 R2 =>
        rw [elabDefsF]
        refine bind_framed (elabDefsF_framed _ _ k d1 S1 R1) fun r1 => ?_
        split
        · exact bind_framed (elabDefsF_framed _ _ k d2 S2 R2) fun _ => ret_framed _
        · exact ret_framed _
      | _ => simp only [elabDefsF]; exact ret_framed _
    | _ => simp only [elabDefsF]; exact ret_framed _

theorem fillDefsF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (look : Label → Option (ATm s)) :
    (k : Nat) → (d : PDefs s) → (Sw Sr : Shape s) → Framed (fillDefsF Γ ps look k d Sw Sr)
  | 0, d, Sw, Sr => by
    rw [fillDefsF]
    exact markAs_framed _
  | k + 1, .typ A S0, Sw, Sr => by
    rw [fillDefsF]
    exact ret_framed _
  | k + 1, .cap C c, Sw, Sr => by
    rw [fillDefsF]
    exact ret_framed _
  | k + 1, .trm a none t, Sw, Sr => by
    rw [fillDefsF]
    split
    · exact ret_framed _
    · exact ret_framed _
  | k + 1, .trm a (some T) t, Sw, Sr => by
    cases Sw with
    | fld b Tw =>
      cases Sr with
      | fld c Tr =>
        rw [fillDefsF]
        refine ite_framed ?_ (ret_framed _)
        split
        · exact ret_framed _
        · exact bind_framed (elabF_framed _ _ k t _) fun _ => ret_framed _
      | _ => simp only [fillDefsF]; exact ret_framed _
    | _ => simp only [fillDefsF]; exact ret_framed _
  | k + 1, .and d1 d2, Sw, Sr => by
    cases Sw with
    | and S1 S2 =>
      cases Sr with
      | and R1 R2 =>
        rw [fillDefsF]
        refine bind_framed (fillDefsF_framed _ _ look k d1 S1 R1) fun r1 => ?_
        split
        · exact bind_framed (fillDefsF_framed _ _ look k d2 S2 R2) fun _ => ret_framed _
        · exact ret_framed _
      | _ => simp only [fillDefsF]; exact ret_framed _
    | _ => simp only [fillDefsF]; exact ret_framed _

end

/-! ## Completeness of a filled domain -/

/-- An elaboration agrees with a computation of the typer when, from every
tank, its candidates are the typer's results in the typer's order and it
leaves the same tank.  Only the fills and the reasons are new. -/
def Agrees {s : Sig} {Γ : Ctx s} (a' : Fu (Out Γ)) (a : Fu (List (Elab Γ))) : Prop :=
  ∀ t, (a' t).1.1.map (·.e) = (a t).1 ∧ (a' t).2 = (a t).2

theorem fullInfer_agrees {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (G : Option (ETy s)) : Agrees (fullInfer Γ ps a G) (inferF Γ ps (sizeATm a) a G) := by
  intro t
  refine ⟨?_, rfl⟩
  simp only [fullInfer, Fu.bind, Fu.ret, List.map_map]
  exact List.map_id' _

/-- Every candidate of the typer on a term with no empty slot has the term
as its fill. -/
theorem fullInfer_fill {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s}
    {G : Option (ETy s)} {t : Tank} {c : ECand Γ} (h : c ∈ (fullInfer Γ ps a G t).1.1) :
    c.fill = a := by
  simp only [fullInfer, Fu.bind, Fu.ret] at h
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp h
  rfl

/-- At a goal whose function part gives the domain `D`, a lambda without a
domain whose body has no empty slot is the typer on the lambda filled with
`D`, from the tank the function part left: candidates and tank. -/
theorem lam_fill_full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    (a : ATm (Sig.body s)) {G : Option (ETy s)} {tk tk' : Tank} {fp : FunPart s} {D : Dom s}
    (hf : funPartOf Γ G tk = (fp, tk')) (hd : fp.dom? = some D) :
    elabF Γ ps (k + 1) (.lam none a.toI) G tk = fullInfer Γ ps (.lam D a) G tk' := by
  rw [elabF_lam_none]
  simp only [lamNoneF, Fu.bind, hf, hd, ATm.full?_toI]

/-- A lambda without a domain whose body has no empty slot, checked against a
function type: the elaborator is the typer on the lambda with the goal's
domain written, candidates and tank. -/
theorem lam_direct_eq {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) (a : ATm (Sig.body s))
    (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s) :
    elabF Γ ps (k + 1) (.lam none a.toI) (some (.ty ((Shape.all T1 T2) ^ C))) =
      fullInfer Γ ps (.lam T1 a) (some (.ty ((Shape.all T1 T2) ^ C))) := by
  funext tk
  exact lam_fill_full (fp := .direct C T1 T2) a rfl rfl

theorem lam_direct_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat)
    (a : ATm (Sig.body s)) (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s) :
    Agrees (elabF Γ ps (k + 1) (.lam none a.toI) (some (.ty ((Shape.all T1 T2) ^ C))))
      (inferF Γ ps (sizeATm (.lam T1 a)) (.lam T1 a) (some (.ty ((Shape.all T1 T2) ^ C)))) := by
  rw [lam_direct_eq]
  exact fullInfer_agrees _ _ _ _

/-- A lambda without a domain whose body has no empty slot, at a goal whose
function part is reached through an intersection, an alias or a box: the
elaborator is the typer on the lambda with the domain written, from the tank
the function part left. -/
theorem lam_side_full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat} (a : ATm (Sig.body s))
    {G : Option (ETy s)} {tk tk' : Tank} {T1 : Dom s} {V : Option (Cod s)}
    (hf : funPartOf Γ G tk = (.side T1 V, tk')) :
    elabF Γ ps (k + 1) (.lam none a.toI) G tk = fullInfer Γ ps (.lam T1 a) G tk' :=
  lam_fill_full a hf rfl

/-- The same, as an agreement with the typer: the same candidates and the
same tank. -/
theorem lam_side_agrees {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    (a : ATm (Sig.body s)) {G : Option (ETy s)} {tk tk' : Tank} {T1 : Dom s}
    {V : Option (Cod s)} (hf : funPartOf Γ G tk = (.side T1 V, tk')) :
    (elabF Γ ps (k + 1) (.lam none a.toI) G tk).1.1.map (·.e) =
        (inferF Γ ps (sizeATm (.lam T1 a)) (.lam T1 a) G tk').1 ∧
      (elabF Γ ps (k + 1) (.lam none a.toI) G tk).2 =
        (inferF Γ ps (sizeATm (.lam T1 a)) (.lam T1 a) G tk').2 := by
  rw [lam_side_full a hf]
  exact fullInfer_agrees _ _ _ _ tk'

/-- An ascription in the notation whose term has an empty slot: the term
checked against the ascribed type read at the context, as the typer's
clause. -/
theorem elabF_asc {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) {t : PTm s}
    (ht : t.full? = none) {T : Ty s} (hT : writtenWhy T = none) (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.asc t T) G =
      ascE Γ ps T G (elabF Γ ps k t (some (.ty (readAt Γ ps T)))) := by
  rw [elabF]
  simp only [PTm.full?, ht, Option.map_none, hT]

theorem firstCheckedE_snd {s : Sig} {Γ : Ctx s} (E : ETy s) :
    ∀ cs : List (ECand Γ), (firstCheckedE cs E).map Prod.snd = firstChecked (cs.map (·.e)) E
  | [] => rfl
  | c :: cs => by
    simp only [firstCheckedE, firstChecked, List.findSome?_cons, List.map_cons]
    cases h : toChecked c.e E with
    | some r => rfl
    | none =>
      have := firstCheckedE_snd E cs
      simp only [firstCheckedE, firstChecked] at this
      simpa using this

theorem flatMapL_agrees {α γ β δ : Type} {f : α → Fu (List β)} {g : γ → Fu (List δ)}
    {p : α → γ} {h : β → δ} (hf : ∀ x t, ((f x t).1.map h, (f x t).2) = g (p x) t) :
    ∀ (l : List α) t, ((Fu.flatMapL f l t).1.map h, (Fu.flatMapL f l t).2) =
      Fu.flatMapL g (l.map p) t
  | [] => fun _ => rfl
  | x :: xs => by
    intro t
    simp only [Fu.flatMapL, Fu.bind, Fu.ret, List.map_cons]
    have h1 := hf x t
    generalize f x t = r1 at h1 ⊢
    obtain ⟨l1, t1⟩ := r1
    rw [← h1]
    simp only
    have h2 := flatMapL_agrees hf xs t1
    generalize Fu.flatMapL f xs t1 = r2 at h2 ⊢
    obtain ⟨l2, t2⟩ := r2
    rw [← h2]
    simp only [List.map_append]

/-- The candidates moved to a goal are the typer's results moved there, each
with its fill. -/
theorem finishE_agrees {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (cs : List (ECand Γ)) :
    Agrees (finishE Γ G cs) (finishF Γ G (cs.map (·.e))) := by
  intro t
  cases G with
  | none => exact ⟨rfl, rfl⟩
  | some E =>
    simp only [finishE, finishF, Fu.bind, Fu.ret]
    have := flatMapL_agrees (f := fun c => mapL (subsumeF Γ c.e E) fun r =>
        (⟨c.fill, r.toElab⟩ : ECand Γ)) (g := fun r => mapL (subsumeF Γ r E) Checked.toElab)
      (p := (·.e)) (h := (·.e)) (fun c t => by
        simp only [mapL, Fu.bind, Fu.ret]
        generalize subsumeF Γ c.e E t = r
        obtain ⟨o, t1⟩ := r
        cases o <;> rfl) cs t
    generalize Fu.flatMapL (fun c => mapL (subsumeF Γ c.e E) fun r =>
        (⟨c.fill, r.toElab⟩ : ECand Γ)) cs t = r at this ⊢
    obtain ⟨l, t1⟩ := r
    rw [← this]
    exact ⟨rfl, rfl⟩

/-- A lambda without a domain whose body has no empty slot, ascribed a type
that reads as a function type: the elaborator is the typer on the
ascription of the lambda with the read domain written, candidates and
tank. -/
theorem asc_direct_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat)
    (a : ATm (Sig.body s)) {T : Ty s} {C : CaptureSet s} {T1 : Dom s} {T2 : Cod s}
    (hT : writtenWhy T = none) (hR : readAt Γ ps T = (Shape.all T1 T2) ^ C)
    (G : Option (ETy s)) :
    Agrees (elabF Γ ps (k + 2) (.asc (.lam none a.toI) T) G)
      (inferF Γ ps (sizeATm (.asc (.lam T1 a) T)) (.asc (.lam T1 a) T) G) := by
  rw [elabF_asc _ _ _ rfl hT]
  have hl : elabF Γ ps (k + 1) (.lam none a.toI) (some (.ty (readAt Γ ps T))) =
      fullInfer Γ ps (.lam T1 a) (some (.ty (readAt Γ ps T))) := by
    rw [hR]
    exact lam_direct_eq _ _ _ _ _ _ _
  rw [hl]
  show Agrees _ (inferF Γ ps (sizeATm (.lam T1 a) + 1) _ G)
  rw [inferF]
  simp only [hT, Option.isNone_none, if_true]
  intro tk
  have h1 := fullInfer_agrees Γ ps (.lam T1 a) (some (.ty (readAt Γ ps T))) tk
  simp only [ascE, Fu.bind]
  generalize fullInfer Γ ps (.lam T1 a) (some (.ty (readAt Γ ps T))) tk = r at h1 ⊢
  generalize inferF Γ ps (sizeATm (.lam T1 a)) (.lam T1 a)
    (some (.ty (readAt Γ ps T))) tk = r' at h1 ⊢
  obtain ⟨⟨cs, rs⟩, t1⟩ := r
  obtain ⟨es, t1'⟩ := r'
  obtain ⟨h1, h2⟩ := h1
  simp only at h1 h2
  subst h1
  subst h2
  have hc := firstCheckedE_snd (.ty (readAt Γ ps T)) cs
  cases hf : firstCheckedE cs (.ty (readAt Γ ps T)) with
  | some fc =>
    rw [hf] at hc
    obtain ⟨f, c⟩ := fc
    simp only [Option.map_some] at hc
    rw [← hc]
    exact finishE_agrees Γ G _ t1
  | none =>
    rw [hf] at hc
    simp only [Option.map_none] at hc
    rw [← hc]
    cases G <;> exact ⟨rfl, rfl⟩

/-- A call argument `g (λx. a)` whose lambda has no domain and whose body has
no empty slot.  When the goal of the dominant formal gives the domain `D`,
and the typer finds a candidate for the lambda filled with `D` at that goal
and then for the filled `let`, the elaborator is the typer on the filled
program, candidates and tank. -/
theorem arg_fill_full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    (a : ATm (Sig.body s)) {g : BVar s .var} {G : Option (ETy s)} {tk tk1 tk2 tk3 : Tank}
    {F D : Dom s} {T : Ty s} {fp : FunPart s} {e : Elab Γ} {es : List (Elab Γ)}
    (hA : argGoalF Γ g tk = (some F, tk1)) (hF : formalGoal Γ F = some T)
    (hf : funPartOf Γ (some (.ty T)) tk1 = (fp, tk2)) (hd : fp.dom? = some D)
    (hc : inferF Γ ps (sizeATm (.lam D a)) (.lam D a) (some (.ty T)) tk2 = (e :: es, tk3))
    (hr : (inferF Γ ps (sizeATm (.let none (.lam D a) (.app (.there g) .here)))
      (.let none (.lam D a) (.app (.there g) .here)) G tk3).1 ≠ []) :
    elabF Γ ps (k + 2) (.let .arg none (.lam none a.toI) (.app (.there g) .here)) G tk =
      fullInfer Γ ps (.let none (.lam D a) (.app (.there g) .here)) G tk3 := by
  rw [elabF_arg _ _ _ rfl]
  simp only [argLetF, fillThenF, orElseW, Fu.bind, hA, Option.bind_some, hF]
  rw [lam_fill_full a hf hd]
  simp only [fullInfer, Fu.bind, Fu.ret, hc, List.map_cons]
  generalize hL : inferF Γ ps (sizeATm (.let none (.lam D a) (.app (.there g) .here)))
    (.let none (.lam D a) (.app (.there g) .here)) G tk3 = r at hr ⊢
  obtain ⟨l, t4⟩ := r
  cases l with
  | nil => exact absurd rfl hr
  | cons _ _ => simp [stopOr]

/-- `let x : A = λy. a in x`, the version's `val x : A = …`, whose lambda has
no domain and whose body has no empty slot.  When `A` reads as a plain type
that gives the domain `D`, and the typer finds a candidate for the lambda
filled with `D` at `A` and then for the filled `let`, the elaborator is the
typer on the filled program, candidates and tank. -/
theorem val_fill_full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat} (tag : LetTag)
    (a : ATm (Sig.body s)) {A : ETy s} {G : Option (ETy s)} {tk tk2 tk3 : Tank}
    {D : Dom s} {T : Ty s} {fp : FunPart s} {e : Elab Γ} {es : List (Elab Γ)}
    (hw : writtenAnsWhy A = none) (hR : readAns Γ ps A = .ty T)
    (hf : funPartOf Γ (some (.ty T)) tk = (fp, tk2)) (hd : fp.dom? = some D)
    (hc : inferF Γ ps (sizeATm (.lam D a)) (.lam D a) (some (.ty T)) tk2 = (e :: es, tk3))
    (hr : (inferF Γ ps (sizeATm (.let (some A) (.lam D a) (.path (.var .here))))
      (.let (some A) (.lam D a) (.path (.var .here))) G tk3).1 ≠ []) :
    elabF Γ ps (k + 2) (.let tag (some A) (.lam none a.toI) (.path (.var .here))) G tk =
      fullInfer Γ ps (.let (some A) (.lam D a) (.path (.var .here))) G tk3 := by
  rw [elabF_val _ _ _ _ hw rfl]
  simp only [valLetF, hR, fillThenF, orElseW, Fu.bind]
  rw [lam_fill_full a hf hd]
  simp only [fullInfer, Fu.bind, Fu.ret, hc, List.map_cons]
  generalize hL : inferF Γ ps (sizeATm (.let (some A) (.lam D a) (.path (.var .here))))
    (.let (some A) (.lam D a) (.path (.var .here))) G tk3 = r at hr ⊢
  obtain ⟨l, t4⟩ := r
  cases l with
  | nil => exact absurd rfl hr
  | cons _ _ => simp [stopOr]

/-- Every job the elaborator makes is framed. -/
theorem jobsF_framed {s : Sig} (ps : CaptureSet s) (k : Nat) (d : PDefs s) :
    ∀ j ∈ jobsF ps k d, ∀ Γ, Framed (j.run Γ) :=
  jobsOf_framed (fun t Γ => elabF_framed Γ ps k t none) d

/-! ## Self shapes formed from definitions -/

/-- The self shape formed from the definitions is in lockstep with them. -/
theorem fullSelf_lockstep {s t : Sig} {ρ : PartialRename s t} {known : List (Label × Ty t)} :
    ∀ {d : PDefs s} {S : Shape t}, d.fullSelf ρ known = some S → Lockstep ρ known d S
  | .typ A S, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨S', hS, rfl⟩ := h
    exact .typ A S S' hS
  | .cap C c, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨c', hc, rfl⟩ := h
    exact .cap C c c' hc
  | .trm a (some T) u, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨T', hT, rfl⟩ := h
    exact .written a T T' u hT
  | .trm a none u, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    exact .inferred a T u hT
  | .and d e, _, h => by
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf ρ known with
    | none => simp only [h1, reduceCtorEq] at h
    | some S1 =>
      cases h2 : e.fullSelf ρ known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some S2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact .and (fullSelf_lockstep h1) (fullSelf_lockstep h2)

/-- A member moved out from under the class root is the member read back
under it: the self shape a literal's members give, read under the class root
by `Shape.underRoot`, holds the members as written. -/
theorem outOfRoot_shape {s : Sig} {S : Shape ((s,c),x)} {S' : Shape (s,x)}
    (h : shapeRename? S outOfRoot = some S') : S = Shape.underRoot S' :=
  shapeRename?_sound S S' _ _ (PartialRename.Inverts.lift PartialRename.unshift_inverts) h

theorem outOfRoot_ty {s : Sig} {T : Ty ((s,c),x)} {T' : Ty (s,x)}
    (h : tyRename? T outOfRoot = some T') : T = T'.rename Rename.succ.lift :=
  tyRename?_sound T T' _ _ (PartialRename.Inverts.lift PartialRename.unshift_inverts) h

theorem outOfRoot_cap {s : Sig} {C : CaptureSet ((s,c),x)} {C' : CaptureSet (s,x)}
    (h : capRename? C outOfRoot = some C') : C = CaptureSet.rename C' Rename.succ.lift :=
  capRename?_sound C C' _ _ (PartialRename.Inverts.lift PartialRename.unshift_inverts) h

/-- A definition list whose fields all have a written type has no job, so a
literal with a written type on every field needs no round. -/
theorem jobsOf_written {s : Sig} {el : PTm s → (Γ : Ctx s) → Fu (Out Γ)} :
    ∀ {d : PDefs s}, d.AllFieldsWritten → jobsOf el d = []
  | .typ _ _, _ => by simp only [jobsOf]
  | .cap _ _, _ => by simp only [jobsOf]
  | .trm _ (some _) _, _ => by simp only [jobsOf]
  | .trm _ none _, hw => by simp [PDefs.AllFieldsWritten] at hw
  | .and d e, hw => by
    simp only [PDefs.AllFieldsWritten] at hw
    simp only [jobsOf, jobsOf_written hw.1, jobsOf_written hw.2, List.append_nil]

/-- The elaborator makes no job for a literal with a written type on every
field. -/
theorem jobsF_written {s : Sig} {ps : CaptureSet s} {k : Nat} {d : PDefs s}
    (hw : d.AllFieldsWritten) : jobsF ps k d = [] :=
  jobsOf_written hw

/-! ## The least candidate is least -/

theorem belowAllF_sub {s : Sig} {Γ : Ctx s} {E : ETy s} :
    ∀ {Fs : List (ETy s)} {t t' : Tank}, belowAllF Γ E Fs t = (true, t') →
      ∀ F ∈ Fs, Nonempty (ESub Γ E F)
  | [], _, _, _, F, hF => absurd hF List.not_mem_nil
  | F' :: Fs, t, t', h, F, hF => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hF with rfl | hm
      · exact ⟨heq ▸ ESub.refl _⟩
      · exact belowAllF_sub h F hm
    · cases hs : esubF Γ E F' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some e =>
          rcases List.mem_cons.mp hF with rfl | hm
          · exact ⟨e⟩
          · exact belowAllF_sub h F hm
        | none => simp [Fu.ret] at h

theorem leastFromF_sub {s : Sig} {Γ : Ctx s} {Es : List (ETy s)} :
    ∀ {cs : List (ECand Γ)} {t : Tank} {c : ECand Γ} {t' : Tank},
      leastFromF Γ Es cs t = (some c, t') → c ∈ cs ∧ ∀ F ∈ Es, Nonempty (ESub Γ c.e.ans F)
  | [], _, _, _, h => by simp [leastFromF, Fu.ret] at h
  | c0 :: rest, t, c, t', h => by
    unfold leastFromF at h
    cases hb : belowAllF Γ c0.e.ans Es t with
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

/-- The least candidate is a candidate, and its answer is below the answer of
every candidate. -/
theorem leastCand_least {s : Sig} {Γ : Ctx s} {cs : List (ECand Γ)} {tk : Tank}
    {c : ECand Γ} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) :
    c ∈ cs ∧ ∀ c' ∈ cs, Nonempty (ESub Γ c.e.ans c'.e.ans) := by
  obtain ⟨hm, hs⟩ := leastFromF_sub h
  exact ⟨hm, fun c' hc' => hs c'.e.ans (List.mem_map_of_mem hc')⟩

theorem belowAllF_esub? {s : Sig} {Γ : Ctx s} {E : ETy s} :
    ∀ {Fs : List (ETy s)} {t t' : Tank}, belowAllF Γ E Fs t = (true, t') → t'.out = false →
      ∀ F ∈ Fs, F = E ∨ ∃ n, (esub? Γ E F n).1.isSome = true
  | [], _, _, _, _, F, hF => absurd hF List.not_mem_nil
  | F' :: Fs, t, t', h, ho, F, hF => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hF with rfl | hm
      · exact .inl heq.symm
      · exact belowAllF_esub? h ho F hm
    · cases hs : esubF Γ E F' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some e =>
          rcases List.mem_cons.mp hF with rfl | hm
          · have h1 : t1.out = false := (belowAllF_framed Γ E Fs).start h ho
            have h0 : t.out = false := (esubF_framed Γ E F).start hs h1
            refine .inr ⟨t.left, ?_⟩
            have ht : t = ⟨t.left, false⟩ := by
              cases t
              simp_all
            show (esubF Γ E F ⟨t.left, false⟩).1.isSome = true
            rw [← ht, hs]
            rfl
          · exact belowAllF_esub? h ho F hm
        | none => simp [Fu.ret] at h

theorem leastFromF_esub? {s : Sig} {Γ : Ctx s} {Es : List (ETy s)} :
    ∀ {cs : List (ECand Γ)} {t : Tank} {c : ECand Γ} {t' : Tank},
      leastFromF Γ Es cs t = (some c, t') → t'.out = false →
        ∀ F ∈ Es, F = c.e.ans ∨ ∃ n, (esub? Γ c.e.ans F n).1.isSome = true
  | [], _, _, _, h, _ => by simp [leastFromF, Fu.ret] at h
  | c0 :: rest, t, c, t', h, ho => by
    unfold leastFromF at h
    cases hb : belowAllF Γ c0.e.ans Es t with
    | mk b t1 =>
      simp only [Fu.bind, hb] at h
      cases b with
      | true =>
        simp only [if_true, Fu.ret, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact belowAllF_esub? hb ho
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact leastFromF_esub? h ho

/-- The same with the typer's answer goal from a full tank: on a tank that ends
unmarked, the answer of the least candidate is the answer of every other
candidate or below it at some fuel. -/
theorem leastCand_esub? {s : Sig} {Γ : Ctx s} {cs : List (ECand Γ)} {tk : Tank}
    {c : ECand Γ} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) (ho : tk'.out = false) :
    ∀ c' ∈ cs, c'.e.ans = c.e.ans ∨ ∃ n, (esub? Γ c.e.ans c'.e.ans n).1.isSome = true :=
  fun c' hc' => leastFromF_esub? h ho c'.e.ans (List.mem_map_of_mem hc')

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

/-! ## A field that needs a written type -/

/-- The self shape cannot hold an answer exactly when it is no type read back
under the class root: an existential, or a type that names the class root. -/
theorem fieldTy?_eq_none {s : Sig} {E : ETy ((s,c),x)} :
    fieldTy? E = none ↔ ∀ T : Ty (s,x), E ≠ .ty (T.rename Rename.succ.lift) := by
  constructor
  · intro h T hE
    subst hE
    simp only [fieldTy?] at h
    rw [tyRename?_complete T _ _ (PartialRename.Inverts.lift PartialRename.unshift_inverts)] at h
    cases h
  · intro h
    cases E with
    | ty T =>
      simp only [fieldTy?]
      cases hT : tyRename? T outOfRoot with
      | none => rfl
      | some T' => exact absurd (congrArg ETy.ty (outOfRoot_ty hT)) (h T')
    | ex _ _ => rfl

/-- A field's type is its answer read back under the class root. -/
theorem fieldTy?_some {s : Sig} {E : ETy ((s,c),x)} {T : Ty (s,x)} (h : fieldTy? E = some T) :
    E = .ty (T.rename Rename.succ.lift) := by
  cases E with
  | ty T0 =>
    simp only [fieldTy?] at h
    rw [outOfRoot_ty h]
  | ex _ _ => cases h

/-- The least candidate of the job `j` in the probe context at the snapshot
`P`, from some tank, has an answer the self shape cannot hold: an existential,
or a type that names the class root. -/
def NamesRootOrEx {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (P : Shape (s,x))
    (j : Job ((s,c),x)) : Prop :=
  ∃ (t : Tank) (e : ECand (probeCtx Γ ps P)), e ∈ (j.run (probeCtx Γ ps P) t).1.1 ∧
    (∀ c' ∈ (j.run (probeCtx Γ ps P) t).1.1,
      Nonempty (ESub (probeCtx Γ ps P) e.e.ans c'.e.ans)) ∧
    fieldTy? e.e.ans = none

theorem runJobF_explicit {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {P : Shape (s,x)}
    {j : Job ((s,c),x)} {t : Tank} {l : Label}
    (h : (runJobF Γ ps P j t).1 = .error [.needsExplicitType l]) :
    (j.lbl = l ∧ NamesRootOrEx Γ ps P j) ∨
      ∃ t', (j.run (probeCtx Γ ps P) t').1 = ([], [.needsExplicitType l]) := by
  unfold runJobF at h
  rcases hr : j.run (probeCtx Γ ps P) t with ⟨⟨cs, rs⟩, t1⟩
  cases cs with
  | nil =>
    simp only [Fu.bind, hr, Fu.ret, Except.error.injEq] at h
    subst h
    exact .inr ⟨t, by rw [hr]⟩
  | cons c cs =>
    rcases hl : leastCandF (probeCtx Γ ps P) (c :: cs) t1 with ⟨o, t2⟩
    cases o with
    | none => simp [Fu.bind, hr, hl, Fu.ret] at h
    | some e =>
      cases hf : fieldTy? e.e.ans with
      | some T => simp [Fu.bind, hr, hl, hf, Fu.ret] at h
      | none =>
        simp only [Fu.bind, hr, hl, hf, Fu.ret, Except.error.injEq, List.cons.injEq, and_true,
          Frontend.Reason.Reason.needsExplicitType.injEq] at h
        obtain ⟨hm, hs⟩ := leastCand_least hl
        refine .inl ⟨h, t, e, ?_, ?_, hf⟩
        · rw [hr]
          exact hm
        · rw [hr]
          exact hs

/-- A round that asks for a written type names a job of the round.  Either
the least candidate of that job has an answer the self shape cannot hold, an
existential or a type that names the class root, or the job's own
elaboration asked for it, as a literal nested in the right-hand side does. -/
theorem roundF_explicit {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {P : Shape (s,x)} :
    ∀ {js : List (Job ((s,c),x))} {t : Tank} {l : Label},
      (roundF Γ ps P js t).1 = .error [.needsExplicitType l] →
      ∃ j ∈ js, (j.lbl = l ∧ NamesRootOrEx Γ ps P j) ∨
        ∃ t', (j.run (probeCtx Γ ps P) t').1 = ([], [.needsExplicitType l])
  | [], _, _, h => by simp [roundF, Fu.ret] at h
  | j :: js, t, l, h => by
    unfold roundF at h
    rcases hr : runJobF Γ ps P j t with ⟨r, t1⟩
    cases r with
    | error rs =>
      simp only [Fu.bind, hr, Fu.ret, Except.error.injEq] at h
      subst h
      exact ⟨j, List.mem_cons_self .., runJobF_explicit (by rw [hr])⟩
    | ok e =>
      rcases hr' : roundF Γ ps P js t1 with ⟨r', t2⟩
      cases r' with
      | ok _ => simp [Fu.bind, hr, hr', Fu.ret] at h
      | error rs =>
        simp only [Fu.bind, hr, hr', Fu.ret, Except.error.injEq] at h
        subst h
        obtain ⟨j', hj', hc⟩ := roundF_explicit (by rw [hr'])
        exact ⟨j', List.mem_cons_of_mem _ hj', hc⟩

/-! ## The probe context

The probe context binds the self at the snapshot read at the context, at the
set of every atom of the context.  It holds a placeholder for the
definitions.  No function of the context that the typer reads looks at the
definitions of a self binder, so the probe context is, for the typer, the
object body of the literal with any definitions at that set. -/

/-- The probe context types every variable as the object body of the literal
does, whatever its definitions, at the set of every atom of the context. -/
theorem probeCtx_lookup {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (d : Defs ((s,c),x)) :
    ∀ y, (probeCtx Γ ps S).lookup y = (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)).lookup y
  | .here => rfl
  | .there _ => rfl

/-- The probe context has the roots, levels, instance binders, variables and
capture binders of the object body, whatever its definitions. -/
theorem probeCtx_agree {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (d : Defs ((s,c),x)) :
    (probeCtx Γ ps S).root? = (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)).root? ∧
    (∀ κ, (probeCtx Γ ps S).instSet? κ =
      (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)).instSet? κ) ∧
    (∀ κ, (probeCtx Γ ps S).rootB κ = (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)).rootB κ) ∧
    (∀ {k : Kind} (y : BVar ((s,c),x) k),
      (probeCtx Γ ps S).lvl y = (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)).lvl y) ∧
    ctxVars (probeCtx Γ ps S) = ctxVars (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)) ∧
    ctxCaps (probeCtx Γ ps S) = ctxCaps (Γ.objBody d (readSelf Γ ps S) (allAtoms Γ)) := by
  refine ⟨rfl, fun κ => ?_, fun κ => ?_, fun y => ?_, rfl, rfl⟩
  · cases κ <;> rfl
  · cases κ <;> rfl
  · cases y <;> rfl

/-! ## A literal without a self shape is the typer's literal

Every candidate of a literal without a self shape is a candidate the typer
gives a literal with every slot filled, at the same goal, and its fill is that
literal.  So its derivation is the one the typer's object clause gives, which
ends in `HasTy.obj` before the subtyping goal moves it to the goal. -/

/-- Every candidate of `x`, from any tank, satisfies `Q`. -/
def AllCands {s : Sig} {Γ : Ctx s} (Q : ECand Γ → Prop) (x : Fu (Out Γ)) : Prop :=
  ∀ t, ∀ c ∈ (x t).1.1, Q c

section Cands

variable {s : Sig} {Γ : Ctx s} {Q : ECand Γ → Prop}

theorem allCands_nil (rs : List EReason) : AllCands Q (Fu.ret ([], rs)) :=
  fun _ _ hc => absurd hc List.not_mem_nil

theorem allCands_bind {α : Type} {x : Fu α} {f : α → Fu (Out Γ)} (h : ∀ a, AllCands Q (f a)) :
    AllCands Q (Fu.bind x f) := by
  intro t c hc
  simp only [Fu.bind] at hc
  exact h _ _ c hc

theorem allCands_orElseW {ok : List (ECand Γ) → Bool} {a : Fu (Out Γ)} {b : Unit → Fu (Out Γ)}
    (ha : AllCands Q a) (hb : AllCands Q (b ())) : AllCands Q (orElseW ok a b) := by
  intro t c hc
  simp only [orElseW, Fu.bind, stopOr] at hc
  cases hA : a t with
  | mk r t1 =>
    rw [hA] at hc
    have ha' := ha t c
    rw [hA] at ha'
    dsimp only at hc ha'
    split at hc
    · exact ha' hc
    · cases hB : b () t1 with
      | mk r' t2 =>
        rw [hB] at hc
        have hb' := hb t1 c
        rw [hB] at hb'
        exact hb' hc

end Cands

/-- A candidate the typer gives a literal with every slot filled, at the goal
`G`, from some tank, beside that literal as its fill. -/
def InferObj {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s)) (c : ECand Γ) :
    Prop :=
  ∃ S d' tk', c.fill = .obj S d' ∧ c.e ∈ (inferF Γ ps (sizeATm (.obj S d')) (.obj S d') G tk').1

theorem objSelfF_inferF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (G : Option (ETy s)) (defs : Fu (Option (ADefs ((s,c),x)) × List EReason)) :
    AllCands (fun c => ∃ d' tk', c.fill = .obj S d' ∧
      c.e ∈ (inferF Γ ps (sizeATm (.obj S d')) (.obj S d') G tk').1) (objSelfF Γ ps S G defs) := by
  unfold objSelfF
  split
  · exact allCands_nil _
  · refine allCands_bind fun r => ?_
    split
    · rename_i d' _
      intro t c hc
      simp only [fullInfer, Fu.bind, Fu.ret, List.mem_map] at hc
      obtain ⟨e, he, rfl⟩ := hc
      exact ⟨d', t, rfl, he⟩
    · exact allCands_nil _

theorem objSelfF_inferObj {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (G : Option (ETy s)) (defs : Fu (Option (ADefs ((s,c),x)) × List EReason)) :
    AllCands (InferObj Γ ps G) (objSelfF Γ ps S G defs) := fun t c hc =>
  let ⟨d', tk', hf, he⟩ := objSelfF_inferF Γ ps S G defs t c hc
  ⟨S, d', tk', hf, he⟩

theorem objNoneF_inferObj {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (G : Option (ETy s))
    (form : Fu (Except (List EReason) (Shape (s,x) × List (Done s))))
    (fill : Shape (s,x) → List (Done s) → Fu (Option (ADefs ((s,c),x)) × List EReason)) :
    AllCands (InferObj Γ ps G) (objNoneF Γ ps G form fill) := by
  refine allCands_bind fun r => ?_
  cases r with
  | ok p => exact objSelfF_inferObj _ _ _ _ _
  | error _ => exact allCands_nil _

/-- The elaboration of a literal without a self shape, unfolded.  The jobs
are those of `jobsF` at the index left. -/
theorem elabF_obj_none {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (k : Nat) (d : PDefs ((s,c),x))
    (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.obj none d) G =
      match G with
      | some E =>
          Fu.bind (selfGoalF Γ E) fun oS =>
            match oS with
            | some S =>
                orElseW (fun cs => !cs.isEmpty)
                  (objSelfF Γ ps S G (elabDefsF (probeCtx Γ ps S) (psObj ps) k d
                    (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S))))
                  (fun _ => objNoneF Γ ps G (formSelfF Γ ps d (jobsF (psObj ps) k d))
                    fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
                      (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S')))
            | none =>
                objNoneF Γ ps G (formSelfF Γ ps d (jobsF (psObj ps) k d))
                  fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
                    (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S'))
      | none =>
          objNoneF Γ ps none (formSelfF Γ ps d (jobsF (psObj ps) k d))
            fun S' done => fillDefsF (probeCtx Γ ps S') (psObj ps) (doneAt done) k d
              (Shape.underRoot S') (Shape.underRoot (readSelf Γ ps S')) := by
  rw [elabF.eq_def]
  rfl

/-- A candidate of a literal without a self shape is a candidate of the typer
on a literal with every slot filled, at the same goal, and that literal is
its fill: the literal at the self shape its `μ` goal gives, or at the one the
rounds form. -/
theorem obj_none_landed {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    {d : PDefs ((s,c),x)} {G : Option (ETy s)} {tk : Tank} {c : ECand Γ} {cs : List (ECand Γ)}
    (h : (elabF Γ ps k (.obj none d) G tk).1.1 = c :: cs) :
    ∃ S d' tk', c.fill = .obj S d' ∧
      c.e ∈ (inferF Γ ps (sizeATm (.obj S d')) (.obj S d') G tk').1 := by
  cases k with
  | zero =>
    rw [elabF.eq_1] at h
    simp [markAs] at h
  | succ k =>
    have hall : AllCands (InferObj Γ ps G) (elabF Γ ps (k + 1) (.obj none d) G) := by
      rw [elabF_obj_none]
      cases G with
      | none => exact objNoneF_inferObj _ _ _ _ _
      | some E =>
        refine allCands_bind fun oS => ?_
        cases oS with
        | some S =>
          exact allCands_orElseW (objSelfF_inferObj _ _ _ _ _) (objNoneF_inferObj _ _ _ _ _)
        | none => exact objNoneF_inferObj _ _ _ _ _
    exact hall tk c (by rw [h]; exact List.mem_cons_self ..)

/-- With no goal, the self shape is the one the rounds form from the tank the
elaboration starts with, and a candidate is a candidate of the typer on the
literal at that shape, its definitions filled, with that literal as its
fill. -/
theorem obj_none_formed {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {k : Nat}
    {d : PDefs ((s,c),x)} {tk : Tank} {c : ECand Γ} {cs : List (ECand Γ)}
    (h : (elabF Γ ps (k + 1) (.obj none d) none tk).1.1 = c :: cs) :
    ∃ S done d' tk', (formSelfF Γ ps d (jobsF (psObj ps) k d) tk).1 = .ok (S, done) ∧
      c.fill = .obj S d' ∧ c.e ∈ (inferF Γ ps (sizeATm (.obj S d')) (.obj S d') none tk').1 := by
  rw [elabF_obj_none] at h
  dsimp only [objNoneF, Fu.bind] at h
  cases hf : formSelfF Γ ps d (jobsF (psObj ps) k d) tk with
  | mk r tk1 =>
    rw [hf] at h
    cases r with
    | error rs => simp [Fu.ret] at h
    | ok p =>
      obtain ⟨S, done⟩ := p
      obtain ⟨d', tk', hfill, hc⟩ :=
        objSelfF_inferF Γ ps S none _ tk1 c (by dsimp only at h; rw [h]; exact List.mem_cons_self ..)
      exact ⟨S, done, d', tk', rfl, hfill, hc⟩

end CapturesCCFrontend


namespace CapturesCCFrontend

open Frontend.Fuel CapturesCCFrontend.Core
open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub
  SubShape Subcap ESub HasTy DefsTy Platform)
open scoped CapturesCC.DotMNF

/-! ## Checks

Each check elaborates a surface program at `defaultFuel` in the kernel, over
the empty platform or over `πc` or `πz`.  It states the fill, the elaborated
term, its use set and its answer, or the reason, and the tank left.  A program
with an empty slot that compiles is compared with the program that writes the
slot: the fill is that program, and the elaborated term, use set and answer
are the ones the typer gives it.  Where the fill differs from the written
program, the check compares the judgment alone and says why.  An unmarked
tank means the fuel played no part in the verdict. -/

section ElabChecks

/-- A reason with the typer's own reason replaced by its name, so that
outcomes can be compared. -/
def EReason.view : EReason → Frontend.Reason.Reason Label String
  | .missingParamType l => .missingParamType l
  | .cyclicRef l => .cyclicRef l
  | .needsExplicitType l => .needsExplicitType l
  | .ambiguous l => .ambiguous l
  | .landed r => .landed r.name
  | .mismatch => .mismatch
  | .limit => .limit

/-- The outcome of a closed elaboration: the fill, the elaborated term, its
use set and its answer, or the reason. -/
inductive Outcome (s : Sig) where
  /-- The fill, the elaborated term, its use set and its answer. -/
  | ok (f a : ATm s) (U : CaptureSet s) (E : ETy s)
  /-- The reason the program is rejected. -/
  | no (r : Frontend.Reason.Reason Label String)
deriving DecidableEq

/-- The outcome has a typing. -/
def Outcome.isOk {s : Sig} : Outcome s → Bool
  | .ok _ _ _ _ => true
  | .no _ => false

/-- The elaborated term, use set and answer of an outcome, without the
fill. -/
def Outcome.judg {s : Sig} : Outcome s → Option (ATm s × CaptureSet s × ETy s)
  | .ok _ a U E => some (a, U, E)
  | .no _ => none

/-- The outcome of a surface program over a platform, resolved and
elaborated, with the tank left. -/
def elabOut (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolvePTop Λc π e with
  | some p =>
      match elabTopF n π p with
      | (.ok c, t) => (.ok c.fill c.e.tm c.e.uses c.e.ans, t)
      | (.error r, t) => (.no r.view, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- What the typer gives a surface program with every slot written: the
program, its first candidate's term, use set and answer. -/
def writtenOut (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolveTop Λc π e with
  | some a =>
      match synthTopF n π a with
      | (some c, t) => (.ok a c.tm c.uses c.ans, t)
      | (none, t) => (.no .mismatch, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- E2 of `Examples.lean`: a literal whose field's lambda is applied to
itself through a type member. -/
def E2SrcW : STm :=
  cc% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

/-- The same with the domain erased.  The written self shape gives it. -/
def E2SrcD : STm :=
  cc% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λy. y})
       in let f = x.a in f f

/-- `process` ascribed at its own type, its parameter written at `any`. -/
def W2ascSrc : STm :=
  cc% (λ(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). u
        : ∀(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ∀(u : ⊤) ⊤)

/-- The same with both domains erased.  The domain is the goal's, whose `any`
was read as the arrow's own binder when the ascription was read. -/
def W2ascSrcD : STm :=
  cc% (λx. λu. u : ∀(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ∀(u : ⊤) ⊤)

/-- An ascription at two function sides of one domain. -/
def AndSameSrc : STm := cc% (λ(x : {a : ⊤}). x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤))

/-- The same with the domain erased.  The sides meet at the domain
`{a : ⊤}`. -/
def AndSameSrcD : STm := cc% (λx. x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤))

/-- An ascription whose second side is a selection with a function lower
bound.  The written lambda is below it through the lower bound. -/
def X3Src : STm :=
  cc% λ(y : {A : (∀(x : {a : ⊤}) {a : ⊤}) .. ⊤}). (λ(x : {a : ⊤}). x : (∀(x : {a : ⊤}) ⊤) ∧ y.A)

/-- The same with the inner domain erased.  The selection's upper bound has
no function part, so the domain is the first side's. -/
def X3SrcD : STm :=
  cc% λ(y : {A : (∀(x : {a : ⊤}) {a : ⊤}) .. ⊤}). (λx. x : (∀(x : {a : ⊤}) ⊤) ∧ y.A)

/-- Two function sides with comparable domains, the larger one written. -/
def AndTwoSrc : STm := cc% (λ(y : ⊤). y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤))

/-- The same with the domain erased.  The domain is the larger one, `⊤`. -/
def AndTwoSrcD : STm := cc% (λy. y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤))

/-- Two function sides with comparable domains, whose first result the
identity at the larger domain does not meet. -/
def AndResSrc : STm := cc% (λ(x : ⊤). x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : ⊤) ⊤))

/-- The same with the domain erased. -/
def AndResSrcD : STm := cc% (λx. x : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : ⊤) ⊤))

/-- Two function sides with incomparable domains. -/
def AndIncSrcD : STm := cc% (λy. y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤))

/-- One function side and a field the lambda does not have. -/
def AndOneSrcD : STm := cc% (λy. y : (∀(x : ⊤) ⊤) ∧ {a : ⊤})

/-- One function side and `⊤`. -/
def AndTopSrc : STm := cc% (λ(y : ⊤). y : (∀(x : ⊤) ⊤) ∧ ⊤)

/-- The same with the domain erased. -/
def AndTopSrcD : STm := cc% (λy. y : (∀(x : ⊤) ⊤) ∧ ⊤)

/-- The ascription `(λ(x : ⊤). x : ∀(x : ⊤) ⊤)`. -/
def AscSrc : STm := cc% (λ(x : ⊤). x : ∀(x : ⊤) ⊤)

/-- The same with the domain erased. -/
def AscSrcD : STm := cc% (λx. x : ∀(x : ⊤) ⊤)

/-- An alias of a function type as the goal. -/
def AliasSrc : STm := cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). (λ(x : ⊤). x : y.A)

/-- The same with the domain erased.  The alias is followed. -/
def AliasSrcD : STm := cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). (λx. x : y.A)

/-- An alias of an alias of a function type as the goal. -/
def Alias2Src : STm :=
  cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(z : {B : y.A .. y.A}). (λ(x : ⊤). x : z.B)

/-- The same with the domain erased.  Both aliases are followed. -/
def Alias2SrcD : STm :=
  cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). λ(z : {B : y.A .. y.A}). (λx. x : z.B)

/-- An abstract type with a function upper bound as the goal. -/
def UpperSrcD : STm := cc% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). (λx. x : y.A)

/-- An abstract type with a function lower bound only. -/
def LowerSrcD : STm := cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). (λx. x : y.A)

/-- A type member whose bounds are itself, reached through the self of its
binder.  Following it comes back to the same selection. -/
def LoopSrc : STm := cc% λ(y : μ(w. {A : w.A .. w.A})). (λ(x : ⊤). x : y.A)

/-- The same with the domain erased. -/
def LoopSrcD : STm := cc% λ(y : μ(w. {A : w.A .. w.A})). (λx. x : y.A)

/-- A lambda bound with no type. -/
def Id0SrcD : STm := cc% let i = λx. x in i

/-- A lambda ascribed at `⊤`. -/
def IdTopSrcD : STm := cc% (λx. x : ⊤)

/-- E8 of `Examples.lean` with its outer domain erased. -/
def E8SrcD : STm := cc% λx. λ(y : x.A ∧ {a : ⊤}). y.a

/-- A lambda bound by a written `let` and then passed: no call argument. -/
def LetArgSrcD : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λx. x in g i

/-- A curried lambda ascribed at a curried function type. -/
def CurrySrc : STm := cc% (λ(x : ⊤). λ(y : ⊤). x : ∀(x : ⊤) ∀(y : ⊤) ⊤)

/-- The same with both domains erased.  The inner lambda takes its domain
from the codomain of the outer goal. -/
def CurrySrcD : STm := cc% (λx. λy. x : ∀(x : ⊤) ∀(y : ⊤) ⊤)

/-- A curried lambda ascribed at an intersection with a curried side. -/
def SideCurrySrc : STm := cc% (λ(x : ⊤). λ(y : ⊤). y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- The same with both domains erased.  The inner lambda takes its domain
from the result part of the side. -/
def SideCurrySrcD : STm := cc% (λx. λy. y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- The same with the outer domain written and the inner one erased. -/
def SideCurrySrcW : STm := cc% (λ(x : ⊤). λy. y : (∀(x : ⊤) ∀(y : ⊤) ⊤) ∧ ⊤)

/-- A lambda as the body of a `let` with a written type. -/
def LetBodySrc : STm := cc% λ(w : ⊤). let k : ∀(x : ⊤) ⊤ = w in λ(x : ⊤). x

/-- The same with the inner domain erased.  The written type is the goal of
the body. -/
def LetBodySrcD : STm := cc% λ(w : ⊤). let k : ∀(x : ⊤) ⊤ = w in λx. x

/-- A block ascribed at a function type. -/
def BlockSrc : STm := cc% (let k = λ(y : ⊤). y in λ(x : ⊤). x : ∀(x : ⊤) ⊤)

/-- The same with the domain of the block's result erased.  The block passes
its goal to its body. -/
def BlockSrcD : STm := cc% (let k = λ(y : ⊤). y in λx. x : ∀(x : ⊤) ⊤)

/-- A closure over a capability ascribed at a function type that captures
it. -/
def CapSrc : STm := cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λ(x : ⊤). f x : (∀(x : ⊤) ⊤) ^ {f})

/-- The same with the domain erased. -/
def CapSrcD : STm := cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λx. f x : (∀(x : ⊤) ⊤) ^ {f})

/-- The closure ascribed at a pure function type, which does not admit it. -/
def CapPureSrc : STm := cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λ(x : ⊤). f x : ∀(x : ⊤) ⊤)

/-- The same with the domain erased. -/
def CapPureSrcD : STm := cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). (λx. f x : ∀(x : ⊤) ⊤)

/-- A field closure of a literal with a written self shape. -/
def FldSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = λ(u : ⊤). f u})

/-- The same with the domain erased.  The self shape gives it. -/
def FldSrcD : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = λu. f u})

/-- A literal with a written self shape and a field without its type. -/
def FldTySrc : STm := cc% ν(z : {a : ∀(u : ⊤) ⊤}. {a = λ(u : ⊤). u})

/-- A field type written under a written self shape, equal to the shape's. -/
def FldTySrcD : STm := cc% ν(z : {a : ∀(u : ⊤) ⊤}. {a : ∀(u : ⊤) ⊤ = λu. u})

/-- A field type written under a written self shape, other than the shape's. -/
def FldTyBadSrc : STm := cc% ν(z : {a : ∀(u : ⊤) ⊤}. {a : ⊤ = λu. u})

/-- A literal ascribed at a `μ`, its self shape written. -/
def AscObjSrc : STm := cc% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self shape erased.  The `μ` goal gives it. -/
def AscObjSrcS : STm := cc% λ(n : {b : ⊤}). (ν(z. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- A literal whose field is below the goal's field, its self shape written. -/
def AscWideSrc : STm :=
  cc% λ(y : {b : ⊤} ∧ {elem : ⊤}). (ν(z : {a : {b : ⊤}}. {a = y}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self shape erased.  The `μ` goal gives the goal's field
type, not the field's own. -/
def AscWideSrcS : STm :=
  cc% λ(y : {b : ⊤} ∧ {elem : ⊤}). (ν(z. {a = y}) : μ(z. {a : {b : ⊤}}))

/-- A literal nested in a field of a written self shape. -/
def NestSrc : STm :=
  cc% λ(y : {b : ⊤} ∧ {elem : ⊤}).
        ν(o : {a : μ(z. {b : {b : ⊤}})}. {a = ν(z : {b : {b : ⊤}}. {b = y})})

/-- The same with the inner self shape erased.  The field's type is a `μ`
goal. -/
def NestSrcS : STm :=
  cc% λ(y : {b : ⊤} ∧ {elem : ⊤}). ν(o : {a : μ(z. {b : {b : ⊤}})}. {a = ν(z. {b = y})})

/-- A literal without a self shape and with no goal. -/
def NoShapeSrcS : STm := cc% ν(z. {a = λ(u : ⊤). u})

/-- A `let` whose bound term has an existential answer, a call of a function
that returns a fresh cell, with a body that ascribes a lambda. -/
def LetExSrc : STm :=
  cc% λ(g : ⊤).
        let fc = ((λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
        let r = fc g in (λ(x : ⊤). x : ∀(y : ⊤) ⊤)

/-- The same with the domain of the body's lambda erased.  The body is typed
under the witness and the payload, renamed past the witness binder. -/
def LetExSrcD : STm :=
  cc% λ(g : ⊤).
        let fc = ((λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
        let r = fc g in (λx. x : ∀(y : ⊤) ⊤)

/-- The escape written as an ascription, `AscEscSrc` of `Typer.lean`, with
the domains of the callback erased where an expected type reaches. -/
def AscEscSrcG : STm :=
  cc% λ(g : ⊤).
        ((λf. λu. f) :
          (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
            (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {})

/-- A lambda ascribed at a type that puts `any` where the version reads
none. -/
def DeepSrcD : STm := cc% (λx. x : ∀(x : {read : ⊤ ^ {any}}) ⊤)

-- The erased programs are the written ones with those slots erased.
example : (resolvePTop Λc .empty E2SrcW).map PTm.eraseDoms = resolvePTop Λc .empty E2SrcD := by
  decide
example : (resolvePTop Λc πc W2ascSrc).map PTm.eraseDoms = resolvePTop Λc πc W2ascSrcD := by
  decide
example : (resolvePTop Λc .empty AndSameSrc).map PTm.eraseAsc =
    resolvePTop Λc .empty AndSameSrcD := by
  decide
example : (resolvePTop Λc .empty X3Src).map PTm.eraseAsc = resolvePTop Λc .empty X3SrcD := by
  decide
example : (resolvePTop Λc .empty AndTwoSrc).map PTm.eraseAsc =
    resolvePTop Λc .empty AndTwoSrcD := by
  decide
example : (resolvePTop Λc .empty AliasSrc).map PTm.eraseAsc = resolvePTop Λc .empty AliasSrcD := by
  decide
example : (resolvePTop Λc .empty CurrySrc).map PTm.eraseDoms = resolvePTop Λc .empty CurrySrcD := by
  decide
example : (resolvePTop Λc .empty AscObjSrc).map PTm.eraseSelf =
    resolvePTop Λc .empty AscObjSrcS := by
  decide
example : (resolvePTop Λc πc AscEscSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πc AscEscSrcG := by
  decide

-- Every slot written: the typer's verdict, term, use set, answer and tank,
-- with the program as its own fill.
example : elabOut .empty E2SrcW = writtenOut .empty E2SrcW := by decide +kernel
example : elabOut πc W2ascSrc = writtenOut πc W2ascSrc := by decide +kernel
example : elabOut πz Z1defSrc = writtenOut πz Z1defSrc := by decide +kernel
example : elabOut πc C7src = writtenOut πc C7src := by decide +kernel
example : elabOut πz LetExSrc = writtenOut πz LetExSrc := by decide +kernel
example : elabOut πc AscEscSrc = writtenOut πc AscEscSrc := by decide +kernel

-- Domains of fields from written self shapes.
example : elabOut .empty E2SrcD = ((writtenOut .empty E2SrcW).1, ⟨defaultFuel - 62, false⟩) ∧
    writtenOut .empty E2SrcW = ((writtenOut .empty E2SrcW).1, ⟨defaultFuel - 60, false⟩) ∧
    (writtenOut .empty E2SrcW).1.isOk = true := by
  decide +kernel
example : elabOut πc FldSrcD = ((writtenOut πc FldSrc).1, ⟨defaultFuel - 8, false⟩) ∧
    writtenOut πc FldSrc = ((writtenOut πc FldSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut πc FldSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty FldTySrcD = ((writtenOut .empty FldTySrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut .empty FldTySrc).1.isOk = true := by
  decide +kernel

-- Domains from ascriptions, written `let` types and blocks.
example : elabOut .empty AndSameSrcD =
      ((writtenOut .empty AndSameSrc).1, ⟨defaultFuel - 34, false⟩) ∧
    writtenOut .empty AndSameSrc = ((writtenOut .empty AndSameSrc).1, ⟨defaultFuel - 34, false⟩) ∧
    (writtenOut .empty AndSameSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty X3SrcD = ((writtenOut .empty X3Src).1, ⟨defaultFuel - 41, false⟩) ∧
    writtenOut .empty X3Src = ((writtenOut .empty X3Src).1, ⟨defaultFuel - 40, false⟩) ∧
    (writtenOut .empty X3Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty AndTwoSrcD =
      ((writtenOut .empty AndTwoSrc).1, ⟨defaultFuel - 38, false⟩) ∧
    (writtenOut .empty AndTwoSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AndTopSrcD =
      ((writtenOut .empty AndTopSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty AndTopSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AscSrcD = ((writtenOut .empty AscSrc).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenOut .empty AscSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AliasSrcD = ((writtenOut .empty AliasSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty AliasSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty Alias2SrcD =
      ((writtenOut .empty Alias2Src).1, ⟨defaultFuel - 19, false⟩) ∧
    (writtenOut .empty Alias2Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty CurrySrcD = ((writtenOut .empty CurrySrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenOut .empty CurrySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty SideCurrySrcD =
      ((writtenOut .empty SideCurrySrc).1, ⟨defaultFuel - 14, false⟩) ∧
    elabOut .empty SideCurrySrcW =
      ((writtenOut .empty SideCurrySrc).1, ⟨defaultFuel - 14, false⟩) ∧
    (writtenOut .empty SideCurrySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty LetBodySrcD =
      ((writtenOut .empty LetBodySrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenOut .empty LetBodySrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BlockSrcD = ((writtenOut .empty BlockSrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenOut .empty BlockSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc CapSrcD = ((writtenOut πc CapSrc).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut πc CapSrc).1.isOk = true := by
  decide +kernel

-- A domain read at the arrow's own binder.  The fill holds the goal's domain,
-- read, where the written program holds `any`.  The elaborated term, use set
-- and answer are the written program's.
example : (elabOut πc W2ascSrcD).1.judg = (writtenOut πc W2ascSrc).1.judg ∧
    (elabOut πc W2ascSrcD).2 = ⟨defaultFuel - 3, false⟩ ∧
    (writtenOut πc W2ascSrc).1.isOk = true ∧
    (elabOut πc W2ascSrcD).1 ≠ (writtenOut πc W2ascSrc).1 := by
  decide +kernel

-- A body with an empty slot under an unpacking.  The fill is the unpacking,
-- and the elaborated term, use set and answer are the written program's.
example : (elabOut πz LetExSrcD).1.judg = (writtenOut πz LetExSrc).1.judg ∧
    (elabOut πz LetExSrcD).2 = ⟨defaultFuel - 20, false⟩ ∧
    (writtenOut πz LetExSrc).1.isOk = true := by
  decide +kernel

-- Literals without a self shape at a `μ` goal.
example : elabOut .empty AscObjSrcS =
      ((writtenOut .empty AscObjSrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenOut .empty AscObjSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AscWideSrcS =
      ((writtenOut .empty AscWideSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut .empty AscWideSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty NestSrcS = ((writtenOut .empty NestSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    writtenOut .empty NestSrc = ((writtenOut .empty NestSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenOut .empty NestSrc).1.isOk = true := by
  decide +kernel

-- Missing parameter type: no goal, a goal with no function part, a lambda
-- bound by a written `let`, an alias that comes back to itself.
example : elabOut .empty Id0SrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty IdTopSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty E8SrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty LetArgSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty LowerSrcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabOut .empty LoopSrcD = (.no (.missingParamType none), ⟨defaultFuel - 3, false⟩) ∧
    writtenOut .empty LoopSrc = (.no .mismatch, ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

-- Mismatch: incomparable domains, one function side the lambda does not meet,
-- a result the lambda does not meet, an abstract type with a function upper
-- bound, a closure too large for its goal, a written field type other than
-- the self shape's.
example : elabOut .empty AndIncSrcD = (.no .mismatch, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel
example : elabOut .empty AndOneSrcD = (.no .mismatch, ⟨defaultFuel - 12, false⟩) := by
  decide +kernel
example : elabOut .empty AndResSrcD = (.no .mismatch, ⟨defaultFuel - 35, false⟩) ∧
    writtenOut .empty AndResSrc = (.no .mismatch, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel
example : elabOut .empty UpperSrcD = (.no .mismatch, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabOut πc CapPureSrcD = (.no .mismatch, ⟨defaultFuel - 14, false⟩) ∧
    writtenOut πc CapPureSrc = (.no .mismatch, ⟨defaultFuel - 14, false⟩) := by
  decide +kernel
example : elabOut .empty FldTyBadSrc = (.no .mismatch, ⟨defaultFuel, false⟩) := by
  decide +kernel

-- The escape with the callback's domains erased: no candidate, as the typer
-- finds none on the written program, whose verdict names the escape.
example : elabOut πc AscEscSrcG = (.no .mismatch, ⟨defaultFuel - 63, false⟩) ∧
    writtenOut πc AscEscSrc = (.no .mismatch, ⟨defaultFuel - 88, false⟩) := by
  decide +kernel

-- A goal outside the notation of the version: the typer's own reason.
example : elabOut .empty DeepSrcD = (.no (.landed "anyNotOk"), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Call arguments, callee bodies and `val` definitions -/

/-- `withFile` applied to its callback, as Scala writes
`withFile(cp)(f => (u: Unit) => u)`. -/
def S1callSrc : STm :=
  cc% let withFile =
        (λ(cp : μ(c. {C^ : {}..{fs}}) ^ {}).
           λ(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}).
             let fl = ν(f : {read : (∀(u : ⊤) ⊤) ^ {f}}. {read = λ(u : ⊤). u}) in op fl
         : (∀(cp : μ(c. {C^ : {}..{fs}}))
              (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
                ^ {fs, cp}) ^ {fs}) in
      let cp = ν(c : {C^ : {fs}..{fs}}. {C^ = {fs}}) in
      let g = withFile cp in
      g (λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}). λ(u : ⊤). u)

/-- The same with the callback's domain erased.  The formal of `g` gives it. -/
def S1callSrcA : STm :=
  cc% let withFile =
        (λ(cp : μ(c. {C^ : {}..{fs}}) ^ {}).
           λ(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}).
             let fl = ν(f : {read : (∀(u : ⊤) ⊤) ^ {f}}. {read = λ(u : ⊤). u}) in op fl
         : (∀(cp : μ(c. {C^ : {}..{fs}}))
              (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
                ^ {fs, cp}) ^ {fs}) in
      let cp = ν(c : {C^ : {fs}..{fs}}. {C^ = {fs}}) in
      let g = withFile cp in
      g (λf. λ(u : ⊤). u)

/-- The same with every domain in a checked position erased.  The callback's
inner lambda has the goal `⊤`, which has no function part. -/
def S1callSrcG : STm :=
  cc% let withFile =
        (λcp. λop.
             let fl = ν(f : {read : (∀(u : ⊤) ⊤) ^ {f}}. {read = λu. u}) in op fl
         : (∀(cp : μ(c. {C^ : {}..{fs}}))
              (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
                ^ {fs, cp}) ^ {fs}) in
      let cp = ν(c : {C^ : {fs}..{fs}}. {C^ = {fs}}) in
      let g = withFile cp in
      g (λf. λu. u)

/-- The same with the inner lambda's domain written. -/
def S1callSrcGu : STm :=
  cc% let withFile =
        (λcp. λop.
             let fl = ν(f : {read : (∀(u : ⊤) ⊤) ^ {f}}. {read = λu. u}) in op fl
         : (∀(cp : μ(c. {C^ : {}..{fs}}))
              (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
                ^ {fs, cp}) ^ {fs}) in
      let cp = ν(c : {C^ : {fs}..{fs}}. {C^ = {fs}}) in
      let g = withFile cp in
      g (λf. λ(u : ⊤). u)

/-- A callback whose parameter captures a platform capability. -/
def KcapSrc : STm :=
  cc% λ(k : ∀(h : (∀(x : (∀(u : ⊤) ⊤) ^ {k1}) ⊤ ^ {k1}) ^ {k1}) ⊤).
        k (λ(y : (∀(u : ⊤) ⊤) ^ {k1}). y)

/-- The same with the callback's domain erased. -/
def KcapSrcA : STm :=
  cc% λ(k : ∀(h : (∀(x : (∀(u : ⊤) ⊤) ^ {k1}) ⊤ ^ {k1}) ^ {k1}) ⊤). k (λy. y)

/-- An intersection callee whose formals agree on their domain and differ in
their result. -/
def X1Src : STm :=
  cc% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λ(x : ⊤). x)

/-- The same with the argument's domain erased.  The dominant formal is
`∀(x : ⊤) ⊤`. -/
def X1SrcA : STm := cc% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λx. x)

/-- An intersection callee whose formals have comparable domains. -/
def DomSrc : STm :=
  cc% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) ⊤) ⊤)). g (λ(x : {a : ⊤}). x)

/-- The same with the argument's domain erased.  The dominant formal is
`∀(x : {a : ⊤}) ⊤`, which the other formal is below. -/
def DomSrcA : STm := cc% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) ⊤) ⊤)). g (λx. x)

/-- An intersection callee whose formals are incomparable, with the
argument's domain erased. -/
def IncSrcA : STm :=
  cc% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λx. x)

/-- A block as a call argument whose result is a lambda. -/
def BlockArgSrc : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). λ(a : ⊤). g (let y = a in λ(x : ⊤). x)

/-- The same with the lambda's domain erased.  The block passes the formal to
its result. -/
def BlockArgSrcG : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). λ(a : ⊤). g (let y = a in λx. x)

/-- A curried callback. -/
def CurriedSrc : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ∀(y : ⊤) ⊤) ⊤). g (λ(x : ⊤). λ(y : ⊤). y)

/-- The same with both domains erased.  The whole formal is the goal, so the
inner lambda takes its domain from the formal's result. -/
def CurriedSrcG : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ∀(y : ⊤) ⊤) ⊤). g (λx. λy. y)

/-- A boxed callee. -/
def BoxCalleeSrc : STm := cc% λ(g : □(∀(h : ∀(y : ⊤) ⊤) ⊤)). g (λ(y : ⊤). y)

/-- The same with the argument's domain erased.  The formal is read off the
box. -/
def BoxCalleeSrcA : STm := cc% λ(g : □(∀(h : ∀(y : ⊤) ⊤) ⊤)). g (λy. y)

/-- A boxed formal. -/
def BoxFSrc : STm := cc% λ(g : ∀(h : □(∀(y : ⊤) ⊤)) ⊤). g (λ(y : ⊤). y)

/-- The same with the argument's domain erased.  The box is stripped for the
goal, and the typer boxes the argument. -/
def BoxFSrcA : STm := cc% λ(g : ∀(h : □(∀(y : ⊤) ⊤)) ⊤). g (λy. y)

/-- A callee whose formal captures anything, `{any}` read as the callee's
binder, and a closure over `f` as its argument. -/
def AnyAscSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let g = (λ(h : (∀(x : ⊤) ⊤) ^ {any}). h : ∀(h : (∀(x : ⊤) ⊤) ^ {any}) ⊤) in
        g (λ(x : ⊤). f x)

/-- The same with the argument's domain erased.  The formal's set names the
callee's binder and is read as every atom of the context. -/
def AnyAscSrcA : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let g = (λ(h : (∀(x : ⊤) ⊤) ^ {any}). h : ∀(h : (∀(x : ⊤) ⊤) ^ {any}) ⊤) in
        g (λx. f x)

/-- A closure over `f` at a formal that captures `f`. -/
def FitsSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(g : ∀(h : (∀(x : ⊤) ⊤) ^ {f}) ⊤). g (λ(x : ⊤). f x)

/-- The same with the argument's domain erased. -/
def FitsSrcA : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(g : ∀(h : (∀(x : ⊤) ⊤) ^ {f}) ⊤). g (λx. f x)

/-- A closure over `f` at a pure formal. -/
def TooBigSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). g (λ(x : ⊤). f x)

/-- The same with the argument's domain erased. -/
def TooBigSrcA : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). g (λx. f x)

/-- A callee with no function type, with the argument's domain erased. -/
def NoFnSrcA : STm := cc% λ(g : ⊤). g (λx. x)

/-- A lambda whose body calls `g` on its parameter. -/
def CalleeSrc : STm := cc% λ(g : ∀(y : ⊤) ⊤). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The callee's formal gives it. -/
def CalleeSrcD : STm := cc% λ(g : ∀(y : ⊤) ⊤). let h = λx. g x in h

/-- A callee whose parameter is written at `{any}`, the binder of its arrow. -/
def CalleeAnySrc : STm :=
  cc% let g = (λ(y : (∀(u : ⊤) ⊤) ^ {any}). y : ∀(y : (∀(u : ⊤) ⊤) ^ {any}) ⊤) in
      let h = λ(x : (∀(u : ⊤) ⊤) ^ {any}). g x in h

/-- The same with the domain of `h` erased.  The formal, read, becomes the
lambda's domain under its own binder. -/
def CalleeAnySrcD : STm :=
  cc% let g = (λ(y : (∀(u : ⊤) ⊤) ^ {any}). y : ∀(y : (∀(u : ⊤) ⊤) ^ {any}) ⊤) in
      let h = λx. g x in h

/-- A callee body ascribed at `⊤`. -/
def CalleeTopSrc : STm := cc% λ(g : ∀(y : ⊤) ⊤). (λ(x : ⊤). g x : ⊤)

/-- The same with the domain erased. -/
def CalleeTopSrcD : STm := cc% λ(g : ∀(y : ⊤) ⊤). (λx. g x : ⊤)

/-- A body that calls `g` on another variable, with the domain erased. -/
def CalleeOtherSrcD : STm := cc% λ(g : ∀(y : ⊤) ⊤). λ(z : ⊤). let h = λx. g z in h

/-- A callee at incomparable domains, with the domain erased. -/
def CalleeIncSrcD : STm :=
  cc% λ(g : (∀(y : {a : ⊤}) ⊤) ∧ (∀(y : {b : ⊤}) ⊤)). let h = λx. g x in h

/-- A callee body as a call argument at a formal with no function part. -/
def CalleeArgSrc : STm := cc% λ(g : ∀(y : ⊤) ⊤). λ(f : ∀(h : ⊤) ⊤). f (λ(x : ⊤). g x)

/-- The same with the domain erased. -/
def CalleeArgSrcA : STm := cc% λ(g : ∀(y : ⊤) ⊤). λ(f : ∀(h : ⊤) ⊤). f (λx. g x)

/-- `val i : ∀(x : ⊤) ⊤ = (x : ⊤) => x`. -/
def ValSrc : STm := cc% let i : ∀(x : ⊤) ⊤ = λ(x : ⊤). x in i

/-- The same with the domain erased.  The written type gives it. -/
def ValSrcD : STm := cc% let i : ∀(x : ⊤) ⊤ = λx. x in i

/-- `freshCell` bound by a `val` with both domains erased. -/
def Z1defSrcD : STm :=
  cc% let fc : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs} =
        λu. let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λv. v}) in r
      in fc

/-- `EscOkSrc` of `Typer.lean` with its callback's domains erased. -/
def EscOkSrcG : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {f}) ^ {f}) ^ {}
      = λf. λu. f
    in cb

/-- `TopEscSrc` of `Typer.lean` with its callback's domains erased. -/
def TopEscSrcG : STm :=
  cc% let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                  (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
        = λf. λu. f
      in cb

-- The erased programs are the written ones with those slots erased.
example : (resolvePTop Λc πz S1callSrc).map PTm.eraseArgs = resolvePTop Λc πz S1callSrcA := by
  decide +kernel
example : (resolvePTop Λc πz S1callSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz S1callSrcG := by
  decide +kernel
example : (resolvePTop Λc πc KcapSrc).map PTm.eraseArgs = resolvePTop Λc πc KcapSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty X1Src).map PTm.eraseArgs = resolvePTop Λc .empty X1SrcA := by
  decide +kernel
example : (resolvePTop Λc .empty DomSrc).map PTm.eraseArgs = resolvePTop Λc .empty DomSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty BlockArgSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc .empty BlockArgSrcG := by
  decide +kernel
example : (resolvePTop Λc .empty CurriedSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc .empty CurriedSrcG := by
  decide +kernel
example : (resolvePTop Λc .empty BoxCalleeSrc).map PTm.eraseArgs =
    resolvePTop Λc .empty BoxCalleeSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty BoxFSrc).map PTm.eraseArgs = resolvePTop Λc .empty BoxFSrcA := by
  decide +kernel
example : (resolvePTop Λc πc AnyAscSrc).map PTm.eraseArgs = resolvePTop Λc πc AnyAscSrcA := by
  decide +kernel
example : (resolvePTop Λc πc FitsSrc).map PTm.eraseArgs = resolvePTop Λc πc FitsSrcA := by
  decide +kernel
example : (resolvePTop Λc πc TooBigSrc).map PTm.eraseArgs = resolvePTop Λc πc TooBigSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty CalleeArgSrc).map PTm.eraseArgs =
    resolvePTop Λc .empty CalleeArgSrcA := by
  decide +kernel
example : (resolvePTop Λc .empty ValSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc .empty ValSrcD := by
  decide +kernel
example : (resolvePTop Λc πz Z1defSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz Z1defSrcD := by
  decide +kernel
example : (resolvePTop Λc πc EscOkSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πc EscOkSrcG := by
  decide +kernel
example : (resolvePTop Λc πc TopEscSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πc TopEscSrcG := by
  decide +kernel

-- Call arguments: the dominant formal, whole, is the goal of the argument.
example : elabOut πz S1callSrcA = ((writtenOut πz S1callSrc).1, ⟨defaultFuel - 91, false⟩) ∧
    writtenOut πz S1callSrc = ((writtenOut πz S1callSrc).1, ⟨defaultFuel - 83, false⟩) ∧
    (writtenOut πz S1callSrc).1.isOk = true := by
  decide +kernel
example : elabOut πz S1callSrcGu = ((writtenOut πz S1callSrc).1, ⟨defaultFuel - 93, false⟩) := by
  decide +kernel
example : elabOut .empty K1srcA = ((writtenOut .empty K1src).1, ⟨defaultFuel - 33, false⟩) ∧
    writtenOut .empty K1src = ((writtenOut .empty K1src).1, ⟨defaultFuel - 26, false⟩) ∧
    (writtenOut .empty K1src).1.isOk = true := by
  decide +kernel
example : elabOut πc KcapSrcA = ((writtenOut πc KcapSrc).1, ⟨defaultFuel - 41, false⟩) ∧
    writtenOut πc KcapSrc = ((writtenOut πc KcapSrc).1, ⟨defaultFuel - 31, false⟩) ∧
    (writtenOut πc KcapSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty X1SrcA = ((writtenOut .empty X1Src).1, ⟨defaultFuel - 52, false⟩) ∧
    writtenOut .empty X1Src = ((writtenOut .empty X1Src).1, ⟨defaultFuel - 31, false⟩) ∧
    (writtenOut .empty X1Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty DomSrcA = ((writtenOut .empty DomSrc).1, ⟨defaultFuel - 66, false⟩) ∧
    (writtenOut .empty DomSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BlockArgSrcG =
      ((writtenOut .empty BlockArgSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenOut .empty BlockArgSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CurriedSrcG = ((writtenOut .empty CurriedSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenOut .empty CurriedSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BoxCalleeSrcA =
      ((writtenOut .empty BoxCalleeSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty BoxCalleeSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BoxFSrcA = ((writtenOut .empty BoxFSrc).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenOut .empty BoxFSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc AnyAscSrcA = ((writtenOut πc AnyAscSrc).1, ⟨defaultFuel - 26, false⟩) ∧
    (writtenOut πc AnyAscSrc).1.isOk = true := by
  decide +kernel
example : elabOut πc FitsSrcA = ((writtenOut πc FitsSrc).1, ⟨defaultFuel - 20, false⟩) ∧
    (writtenOut πc FitsSrc).1.isOk = true := by
  decide +kernel

-- The callee's body `λx. g x` takes the dominant formal of `g`.
example : elabOut .empty CalleeSrcD = ((writtenOut .empty CalleeSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    writtenOut .empty CalleeSrc = ((writtenOut .empty CalleeSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut .empty CalleeSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeTopSrcD =
      ((writtenOut .empty CalleeTopSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenOut .empty CalleeTopSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty CalleeArgSrcA =
      ((writtenOut .empty CalleeArgSrc).1, ⟨defaultFuel - 22, false⟩) ∧
    (writtenOut .empty CalleeArgSrc).1.isOk = true := by
  decide +kernel

-- A formal at the callee's binder.  The fill holds the formal, read, where
-- the written program holds `any`.  The elaborated term, use set and answer
-- are the written program's.
example : (elabOut .empty CalleeAnySrcD).1.judg = (writtenOut .empty CalleeAnySrc).1.judg ∧
    (elabOut .empty CalleeAnySrcD).2 = ⟨defaultFuel - 19, false⟩ ∧
    (writtenOut .empty CalleeAnySrc).1.isOk = true ∧
    (elabOut .empty CalleeAnySrcD).1 ≠ (writtenOut .empty CalleeAnySrc).1 := by
  decide +kernel

-- `val` definitions: the written type is the goal of the right-hand side.
example : elabOut .empty ValSrcD = ((writtenOut .empty ValSrc).1, ⟨defaultFuel - 4, false⟩) ∧
    writtenOut .empty ValSrc = ((writtenOut .empty ValSrc).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenOut .empty ValSrc).1.isOk = true := by
  decide +kernel
example : elabOut πz Z1defSrcD = ((writtenOut πz Z1defSrc).1, ⟨defaultFuel - 45, false⟩) ∧
    writtenOut πz Z1defSrc = ((writtenOut πz Z1defSrc).1, ⟨defaultFuel - 31, false⟩) ∧
    (writtenOut πz Z1defSrc).1.isOk = true := by
  decide +kernel
example : (elabOut πc EscOkSrcG).1.judg = (writtenOut πc EscOkSrc).1.judg ∧
    (elabOut πc EscOkSrcG).2 = ⟨defaultFuel - 7, false⟩ ∧
    (writtenOut πc EscOkSrc).1.isOk = true ∧
    (elabOut πc EscOkSrcG).1 ≠ (writtenOut πc EscOkSrc).1 := by
  decide +kernel

-- Missing parameter type: incomparable formals, a callee with no function
-- type, a callee body at incomparable domains, a body that is no call of the
-- parameter, and a lambda at a goal `⊤` inside a callback.
example : elabOut .empty IncSrcA = (.no (.missingParamType none), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : elabOut .empty NoFnSrcA = (.no (.missingParamType none), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : elabOut .empty CalleeIncSrcD =
    (.no (.missingParamType none), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel
example : elabOut .empty CalleeOtherSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut πz S1callSrcG = (.no (.missingParamType none), ⟨defaultFuel - 54, false⟩) := by
  decide +kernel

-- Mismatch: a closure too large for its formal, as for the written program,
-- and the escape at the top with its callback's domains erased, where the
-- typer finds no candidate on the written program either.
example : elabOut πc TooBigSrcA = (.no .mismatch, ⟨defaultFuel - 36, false⟩) ∧
    writtenOut πc TooBigSrc = (.no .mismatch, ⟨defaultFuel - 20, false⟩) := by
  decide +kernel
example : elabOut πc TopEscSrcG = (.no .mismatch, ⟨defaultFuel - 63, false⟩) ∧
    writtenOut πc TopEscSrc = (.no .mismatch, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-! ### More programs whose lambdas take their domains from a goal -/

/-- `makeLogger` of `Examples.lean`, bound by an ascription, its parameter
written at `{any}`. -/
def Z2srcW : STm :=
  cc% (λ(l : (∀(u : ⊤) ⊤) ^ {any}).
          let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {})

/-- The same with every lambda domain erased.  The ascription gives the outer
one, read at the arrow's binder, and the self shape the inner one. -/
def Z2srcD : STm :=
  cc% (λl. let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λv. v}) in r
        : (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {})

/-- Z3 of `Examples.lean` with every lambda domain erased. -/
def Z3srcD : STm :=
  cc% (λu. let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                       {C^ = {fs}} ∧ {next = λv. v}) in
                 (it : μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fs})
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fresh})
             ^ {fs})

/-- S2 of `Examples.lean` with the domain of every lambda in a checked
position erased.  `un` is the identity ascribed at `⊤`, which has no function
part. -/
def S2srcChecked : STm :=
  cc% let mk =
        (λu. let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                          {C^ = {fs}} ∧ {next = λv. v}) in it
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {any}) ^ {fs}) in
      let un = (λy. y : ⊤) in
      let it = mk un in let n = it.next in let r = n un in r

/-- `exTopSrc` of `Typer.lean` with the domain of every lambda in a checked
position erased.  `un` is bound by a written `let`, which is no checked
position. -/
def exTopSrcG : STm :=
  cc% let fc = ((λu. let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λv. v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
      let un = λ(v : ⊤). v in fc un

/-- The same with every lambda domain erased. -/
def exTopSrcD : STm :=
  cc% let fc = ((λu. let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λv. v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
      let un = λv. v in fc un

/-- `process` of `Typer.lean` with both domains erased. -/
def W2defSrcD : STm := cc% λx. λu. u

/-- `C7src` of `Typer.lean` with both domains erased. -/
def C7srcD : STm :=
  cc% λf1. λf2.
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

-- The erased programs are the written ones with those slots erased.  For Z1,
-- Z3, X3, TopEsc and Esc the domains in checked positions are all the
-- domains, so the D and G erasures agree.
example : (resolvePTop Λc πz Z2srcW).map PTm.eraseDoms = resolvePTop Λc πz Z2srcD := by
  decide +kernel
example : (resolvePTop Λc πz Z2srcW).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz Z2srcD := by
  decide +kernel
example : (resolvePTop Λc πz Z3srcW).map PTm.eraseDoms = resolvePTop Λc πz Z3srcD := by
  decide +kernel
example : (resolvePTop Λc πz Z3srcW).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz Z3srcD := by
  decide +kernel
example : (resolvePTop Λc .empty X3Src).map (PTm.eraseChecked false false) =
    resolvePTop Λc .empty X3SrcD := by
  decide +kernel
example : (resolvePTop Λc πz S2srcW).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz S2srcChecked := by
  decide +kernel
example : (resolvePTop Λc πz exTopSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πz exTopSrcG := by
  decide +kernel
example : (resolvePTop Λc πz exTopSrc).map PTm.eraseDoms = resolvePTop Λc πz exTopSrcD := by
  decide +kernel
example : (resolvePTop Λc πc TopEscSrc).map PTm.eraseDoms = resolvePTop Λc πc TopEscSrcG := by
  decide +kernel
example : (resolvePTop Λc πc EscSrc).map (PTm.eraseChecked false false) =
    resolvePTop Λc πc EscSrcG := by
  decide +kernel
example : (resolvePTop Λc πc W2defSrc).map PTm.eraseDoms = resolvePTop Λc πc W2defSrcD := by
  decide +kernel
example : (resolvePTop Λc πc C7src).map PTm.eraseDoms = resolvePTop Λc πc C7srcD := by
  decide +kernel

-- Domains from an ascription and from written self shapes: `freshCell` and
-- `mk` compile to the written program.
example : elabOut πz Z1srcD = ((writtenOut πz Z1srcW).1, ⟨defaultFuel - 14, false⟩) ∧
    writtenOut πz Z1srcW = ((writtenOut πz Z1srcW).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut πz Z1srcW).1.isOk = true := by
  decide +kernel
example : elabOut πz Z3srcD = ((writtenOut πz Z3srcW).1, ⟨defaultFuel - 107, false⟩) ∧
    writtenOut πz Z3srcW = ((writtenOut πz Z3srcW).1, ⟨defaultFuel - 101, false⟩) ∧
    (writtenOut πz Z3srcW).1.isOk = true := by
  decide +kernel

-- A parameter written at `{any}`.  The fill holds the goal's domain, read,
-- where the written program holds `any`.  The elaborated term, use set and
-- answer are the written program's.
example : (elabOut πz Z2srcD).1.judg = (writtenOut πz Z2srcW).1.judg ∧
    (elabOut πz Z2srcD).2 = ⟨defaultFuel - 14, false⟩ ∧
    writtenOut πz Z2srcW = ((writtenOut πz Z2srcW).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut πz Z2srcW).1.isOk = true ∧
    (elabOut πz Z2srcD).1 ≠ (writtenOut πz Z2srcW).1 := by
  decide +kernel

-- Missing parameter type: a lambda ascribed at `⊤` in S2, a lambda bound by a
-- written `let`, and programs whose outermost term is a lambda.
example : elabOut πz S2srcChecked = (.no (.missingParamType none), ⟨defaultFuel - 96, false⟩) := by
  decide +kernel
example : elabOut πz exTopSrcD = (.no (.missingParamType none), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel
example : elabOut πc W2defSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut πc C7srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- No candidate where the typer finds none on the written program: the
-- existential at the top of `exTop`, and the escape of `Esc`.  The typer's
-- verdicts on the written programs name `existentialAtTop` and `levelEscape`.
example : elabOut πz exTopSrcG = (.no .mismatch, ⟨defaultFuel - 21, false⟩) ∧
    writtenOut πz exTopSrc = (.no .mismatch, ⟨defaultFuel - 19, false⟩) := by
  decide +kernel
example : elabOut πc EscSrcG = (.no .mismatch, ⟨defaultFuel - 63, false⟩) ∧
    writtenOut πc EscSrc = (.no .mismatch, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-! ### Self shapes formed from definitions

The rounds alone, on a literal without a self shape, then the self shape in
lockstep.  Each check compares the self shape `formSelfF` forms with the self
shape the written form of the program states, or gives the reason the rounds
stop.  It also fills the literal at the formed shape by hand, each field
without a written type holding the term the rounds elaborated for it, and asks
the typer whether the filled literal types in the real context. -/

/-- What `formSelfF` gives the first literal without a self shape of a
program. -/
inductive Formed where
  /-- A self shape formed, whether it is the one the written form states, and
  whether the typer types the literal filled at it. -/
  | self (written typed : Bool)
  /-- The reason the rounds stop. -/
  | no (r : Frontend.Reason.Reason Label String)
  /-- No such literal, or the written form is not the same program there. -/
  | shape
deriving DecidableEq

/-- The definitions of a literal filled by hand: a field without a written
type holds the term `look` gives its label, a field with a written type its
right-hand side when that has no empty slot. -/
def fillByHand {s : Sig} (look : Label → Option (ATm s)) : PDefs s → Option (ADefs s)
  | .typ A S => some (.typ A S)
  | .cap C c => some (.cap C c)
  | .trm a none _ => (look a).map (.trm a)
  | .trm a (some _) t => t.full?.map (.trm a)
  | .and d e =>
      match fillByHand look d, fillByHand look e with
      | some d', some e' => some (.and d' e')
      | _, _ => none

/-- The typer gives the literal with self shape `S` and definitions `d` a
candidate in `Γ`, on a tank of its own. -/
def typesLit {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x))
    (d : ADefs ((s,c),x)) : Bool :=
  !(inferF Γ ps (sizeATm (.obj S d)) (.obj S d) none ⟨defaultFuel, false⟩).1.isEmpty

/-- The type the typer gives a bound term with no empty slot, on a tank of its
own: the type at which a `let` binds its variable. -/
def boundTy? {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (t : PTm s) : Option (Ty s) :=
  match t.full? with
  | some a =>
      match (inferF Γ ps (sizeATm a) a none ⟨defaultFuel, false⟩).1.head? with
      | some r =>
          match r.ans with
          | .ty T => some T
          | .ex _ _ => none
      | none => none
  | none => none

/-- `formSelfF` on the first literal without a self shape, found under written
lambdas, under ascriptions, and in `let`s, against the same place of the
written form.  A `let` whose bound term holds no such literal binds its
variable at the type the typer gives the written bound term.  The jobs are
elaborated at an index that is the size of the definitions. -/
def formGo {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (n : Nat) : PTm s → PTm s → Formed × Tank
  | .lam (some T) t, .lam (some T') t' =>
      if T = T' then formGo (Γ.body (readDom T)) (psBody ps) n t t' else (.shape, ⟨n, true⟩)
  | .asc t _, .asc t' _ => formGo Γ ps n t t'
  | .let _ _ t u, .let _ _ t' u' =>
      match formGo Γ ps n t t' with
      | (.shape, _) =>
          match boundTy? Γ ps t' with
          | some T => formGo (Γ.cons T) (psVar ps) n u u'
          | none => (.shape, ⟨n, true⟩)
      | r => r
  | .obj none d, .obj o _ =>
      match formSelfF Γ ps d (jobsF (psObj ps) (sizePDefs d) d) ⟨n, false⟩ with
      | (.ok (S, done), tk) =>
          (.self (decide (o = some S))
            (match fillByHand (doneAt done) d with
              | some d' => typesLit Γ ps S d'
              | none => false), tk)
      | (.error rs, tk) => (.no (EReason.view (Frontend.Reason.Reason.top tk.out rs)), tk)
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a surface program over a platform, against a written form,
with the tank left. -/
def formAt (π : PlatformNames) (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolvePTop Λc π e, resolvePTop Λc π w with
  | some p, some q => formGo π.plat.ctx π.set n p q
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a written program `e` with every self shape erased, against
a written form `w`. -/
def formSAt (π : PlatformNames) (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolvePTop Λc π e, resolvePTop Λc π w with
  | some p, some q => formGo π.plat.ctx π.set n p.eraseSelf q
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a written program with every self shape erased, against
the program itself. -/
def formS (π : PlatformNames) (w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  formSAt π w w n

/-- The jobs of a program that is a literal, or a literal under written
lambdas, with its self shape erased: the label and the dependencies of each. -/
def jobsAt (π : PlatformNames) (e : STm) : List (Label × (List Label × Bool)) :=
  let rec go {s : Sig} : PTm s → List (Label × (List Label × Bool))
    | .lam _ t => go t
    | .obj none d => (jobsOf (fun _ _ => Fu.ret ([], [])) d).map fun j => (j.lbl, j.deps)
    | _ => []
  match resolvePTop Λc π e with
  | some p => go p.eraseSelf
  | none => []

/-- A literal whose first field reads the second. -/
def FwdObjSrc : STm :=
  cc% ν(z : {a : ∀(y : ⊤) ⊤} ∧ {b : ∀(y : ⊤) ⊤}. {a = z.b} ∧ {b = λ(y : ⊤). y})

/-- A field that holds a capability of the context. -/
def Cap1Src : STm := cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = f})

/-- A field closure that projects another field off the self. -/
def SelfProjSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {b : (∀(u : ⊤) ⊤) ^ {f}} ∧ {a : (∀(u : ⊤) ⊤) ^ {z}}.
           {b = f} ∧ {a = λ(u : ⊤). let w = z.b in w u})

/-- A recursive field with its type written in the self shape. -/
def RecObjSrc : STm := cc% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = z.a in w y})

/-- The same without a self shape and with the field type written. -/
def RecWSrcS : STm := cc% ν(z. {a : ∀(y : ⊤) ⊤ = λy. let w = z.a in w y})

/-- E5 with the self shape written at the type of the field's right-hand
side. -/
def E5srcR : STm :=
  cc% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : {A : ⊤..⊤}}. {a = v})
         in let o = f w in o.a

/-- E6 of `Examples.lean`, closed over its parameter, with the self shape
written at the type of the field's right-hand side. -/
def E6srcR : STm :=
  cc% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : {a : ⊤}}. {type T = {a : ⊤}} ∧ {v = n})

/-- The same with the self shape erased. -/
def E6srcS : STm := cc% λ(n : {a : ⊤}). ν(x. {type T = {a : ⊤}} ∧ {v = n})

/-- Two fields that read each other. -/
def CycSrcS : STm := cc% ν(z. {a = z.b} ∧ {b = z.a})

/-- A recursive field without a written type. -/
def RecSrcS : STm := cc% ν(z. {a = λ(y : ⊤). let w = z.a in w y})

/-- A field that reads a cycle between two later fields. -/
def Cyc3SrcS : STm := cc% ν(z. {a = z.b} ∧ {b = z.v} ∧ {v = z.b})

/-- A recursive field that reads itself through an alias of the self. -/
def AliasRecSrcS : STm := cc% ν(z. {a = λ(y : ⊤). let w = z in let u = w.a in u y})

/-- A field that is the self. -/
def BareSrcS : STm := cc% ν(z. {a = z})

/-- The same with the self shape written at the snapshot the field is typed
at. -/
def BareSrc : STm := cc% ν(z : {a : μ(y. ⊤)}. {a = z})

/-- A field that is the self, beside a field that holds a capability, with
the self shape a programmer writes. -/
def BareCapSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : ⊤ ^ {z}}. {a = f} ∧ {b = z})

/-- A closure that reads a sibling through the self, beside a field that
holds a capability, with the self shape a programmer writes. -/
def LamCapSrc : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {v : ∀(u : ⊤) ⊤} ∧ {b : (∀(y : ⊤) ⊤) ^ {z}}.
           {a = f} ∧ {v = λ(u : ⊤). u} ∧ {b = λ(y : ⊤). let w = z.v in w y})

/-- A field that reads a later field that is the self. -/
def FwdSelfSrcS : STm := cc% ν(z. {a = z.b} ∧ {b = z})

/-- The same with the self shape written. -/
def FwdSelfSrc : STm := cc% ν(z : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = z.b} ∧ {b = z})

/-- A field that is the self, and a later one that reads it. -/
def BareProjSrcS : STm := cc% ν(z. {a = z} ∧ {b = z.a})

/-- The same with the self shape written. -/
def BareProjSrc : STm := cc% ν(z : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = z} ∧ {b = z.a})

/-- A field whose type names the class root, read off a written `any`. -/
def NESrcS : STm := cc% ν(z. {a = (λ(u : ⊤). u : (∀(u : ⊤) ⊤) ^ {any})})

/-- A field whose right-hand side unpacks a `fresh` result, over `πz`. -/
def NEfreshSrcS : STm :=
  cc% let fc = (λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
                 : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
      let un = λ(v : ⊤). v in
      ν(z. {a = let x = fc un in x})

/-- A field whose right-hand side has two incomparable types. -/
def AmbSrcS : STm := cc% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s. {a = y.a})

/-- A field whose right-hand side has two types, one below the other, and a
use of the field that needs the smaller one. -/
def AmbUseSrcS : STm :=
  cc% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let o = ν(s. {v = y.a}) in let w = o.v in w.b

/-- The same with the self shape written. -/
def AmbUseSrc : STm :=
  cc% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}).
        let o = ν(s : {v : {b : ⊤}}. {v = y.a}) in let w = o.v in w.b

/-- The same two types in the other order. -/
def AmbUse2SrcS : STm :=
  cc% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}). let o = ν(s. {v = y.a}) in let w = o.v in w.b

/-- The same with the self shape written. -/
def AmbUse2Src : STm :=
  cc% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}).
        let o = ν(s : {v : {b : ⊤}}. {v = y.a}) in let w = o.v in w.b

/-- A field that is a lambda without a domain and without a goal. -/
def NoDomSrcS : STm := cc% ν(z. {a = λy. y})

/-- RecW with the domain of its lambda written as well. -/
def RecWdSrcS : STm := cc% ν(z. {a : ∀(y : ⊤) ⊤ = λ(y : ⊤). let w = z.a in w y})

/-- S3 with the self shape the definitions form: the field at the boxed
capability, not at `z.A`. -/
def S3srcF : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : □((∀(u : ⊤) ⊤) ^ {f}) .. □((∀(u : ⊤) ⊤) ^ {f})} ∧
                      {elem : □((∀(u : ⊤) ⊤) ^ {f})}.
                   {type A = □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem = □ f})
        in let e = o.elem in {f} ⊸ e

/-- C2 with the self shapes the definitions form: `run` pure, not at
`{z.C}`. -/
def C2srcF : STm :=
  cc% let c = λ(x : μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : ∀(u : ⊤) ⊤}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : ∀(u : ⊤) ⊤}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

/-- The literal of `freshCell` with the self shape its definitions form:
`read` pure, not at `{f}`.  Z1, Z1def, Z2 and exTop hold this literal. -/
def Z1litF : STm := cc% ν(f : {read : ∀(v : ⊤) ⊤}. {read = λ(v : ⊤). v})

/-- The same with the self shape erased. -/
def Z1litS : STm := cc% ν(f. {read = λ(v : ⊤). v})

/-- C7 with the self shape the definitions form: the fields at the
capabilities they hold, unboxed, where the written shape boxes them at
`{k1}` and `{k2}`. -/
def C7srcF : STm :=
  cc% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : (∀(u : ⊤) ⊤) ^ {f1}} ∧ {e2 : (∀(u : ⊤) ⊤) ^ {f2}}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- SelfProj with the self shape the definitions form: `a` at `{z, f}`, since
the probe charges the self and the closure reads `f` through it. -/
def SelfProjSrcF : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {b : (∀(u : ⊤) ⊤) ^ {f}} ∧ {a : (∀(u : ⊤) ⊤) ^ {z, f}}.
           {b = f} ∧ {a = λ(u : ⊤). let w = z.b in w u})

/-- BareCap with the self shape the definitions form: `b` at the snapshot
that knows `a`, at `{z}`. -/
def BareCapSrcF : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : μ(y. {a : (∀(u : ⊤) ⊤) ^ {f}}) ^ {z}}.
           {a = f} ∧ {b = z})

/-! #### The jobs and their dependencies

Fwd has two jobs, `a` waiting for `b`.  RecW has none, since its one field
has a written type.  AliasRec's job depends on its own label through the
alias `w` of the self.  FwdSelf's second job and BareProj's first use the
self bare. -/

example : jobsAt .empty FwdObjSrc = [(.trm 0, ([.trm 1], false)), (.trm 1, ([], false))] := by
  decide +kernel
example : jobsAt .empty RecWSrcS = [] := by decide +kernel
example : jobsAt .empty AliasRecSrcS = [(.trm 0, ([.trm 0], false))] := by decide +kernel
example : jobsAt .empty FwdSelfSrcS = [(.trm 0, ([.trm 1], false)), (.trm 1, ([], true))] := by
  decide +kernel
example : jobsAt .empty BareProjSrcS = [(.trm 0, ([], true)), (.trm 1, ([.trm 0], false))] := by
  decide +kernel

/-! #### The written self shape formed

Each program forms the self shape it writes, and the typer types the literal
filled at it in the real context.  RecW forms its
written shape with no job.  Its field's lambda has no domain, which the hand
filling leaves empty, so the typer is asked only of RecW with the domain
written. -/

example : formS .empty E2srcW = (.self true true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS .empty E7srcW = (.self true true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc accountedSrc = (.self true true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS .empty FwdObjSrc = (.self true true, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel
example : formS πc Cap1Src = (.self true true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt .empty RecWSrcS RecObjSrc = (.self true false, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty RecWdSrcS RecObjSrc = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty E5srcS E5srcR = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty E6srcS E6srcR = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! #### Another self shape formed

These programs form a self shape other than the written one, stated by a
written form at it, and the typer types the literal filled at it.  The
literal of `freshCell` forms `read` pure, so Z1, Z1def, Z2 and exTop form
that shape.  C7 forms unboxed fields. -/

example : formSAt πc S3srcW S3srcF = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formSAt πc C2srcW C2srcF = (.self true true, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : formAt πz Z1litS Z1litF = (.self true true, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : formS πz Z1srcW = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz Z1defSrc = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz Z2srcW = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz exTopSrc = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz S1srcW = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz S2srcW = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formS πz Z3srcW = (.self false true, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : formSAt πc C7src C7srcF = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formSAt πc SelfProjSrc SelfProjSrcF = (.self true true, ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

/-! #### The self bare

The probe binds the self at the set of every atom of the context, so a bare
use is charged.  Bare, FwdSelf and BareProj form `μ(y. ⊤)` for the bare field
in the empty platform.  BareCap forms `b` at the snapshot that knows `a`, and
LamCap forms the shape a programmer writes.  The typer types every one of
them filled at the formed shape. -/

example : formAt .empty BareSrcS BareSrc = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty FwdSelfSrcS FwdSelfSrc = (.self true true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : formAt .empty BareProjSrcS BareProjSrc =
    (.self true true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : formSAt πc BareCapSrc BareCapSrcF = (.self true true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formS πc BareCapSrc = (.self false true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formS πc LamCapSrc = (.self true true, ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-! #### The least candidate

X5a and X5b form `{v : {b : ⊤}}` in both orders of `y`'s intersection.  Amb
has two incomparable candidates and is ambiguous. -/

example : formAt .empty AmbUseSrcS AmbUseSrc = (.self true true, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel
example : formAt .empty AmbUse2SrcS AmbUse2Src =
    (.self true true, ⟨defaultFuel - 10, false⟩) := by
  decide +kernel
example : formAt .empty AmbSrcS AmbSrcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

/-! #### Rejections

Cyc, Rec and AliasRec are cyclic at `a`, and Cyc3 at `b`, the member the walk
from `a` reaches twice.  NE's field holds a root capability and NEfresh's an
existential, so both need a written type.  A field that is a lambda without a
domain has no goal and is a missing parameter type. -/

example : formAt .empty CycSrcS CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty RecSrcS RecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt πc Cyc3SrcS Cyc3SrcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty AliasRecSrcS AliasRecSrcS =
    (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt .empty NESrcS NESrcS =
    (.no (.needsExplicitType (.trm 0)), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : formAt πz NEfreshSrcS NEfreshSrcS =
    (.no (.needsExplicitType (.trm 0)), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : formAt .empty NoDomSrcS NoDomSrcS =
    (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Literals without a self shape, elaborated whole

Each program is a written program with every self shape erased, elaborated
whole, so each literal without a self shape is formed, filled and handed to
the typer.  A program that compiles is compared with a written form: the
program itself when the formed self shape is the written one, and else the
program with its self shape written at the formed shape.  Where the formed
shape differs from the written one, the erased term, use set and answer are
those of the written program. -/

/-- The outcome of a written program with every self shape erased, with the
tank left. -/
def elabSOut (π : PlatformNames) (w : STm) (n : Nat := defaultFuel) : Outcome π.sig × Tank :=
  match resolvePTop Λc π w with
  | some p =>
      match elabTopF n π p.eraseSelf with
      | (.ok c, t) => (.ok c.fill c.e.tm c.e.uses c.e.ans, t)
      | (.error r, t) => (.no r.view, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- The erased term, use set and answer of an outcome.  Erasure drops the self
shapes and every other annotation. -/
def Outcome.erased {s : Sig} : Outcome s → Option (Tm s × CaptureSet s × ETy s)
  | .ok _ a U E => some (a.erase, U, E)
  | .no _ => none

/-- The head rule of a derivation is the object rule. -/
def derivIsObj {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {E : ETy s} :
    HasTy U Γ t E → Bool
  | .obj .. => true
  | _ => false

/-- The first candidate of the literal a program is, under its written
lambdas, elaborated with no goal on a tank of its own: whether its derivation
ends in the object rule, on an unmarked tank. -/
def objUnder {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) : PTm s → Bool
  | .lam (some T) t => objUnder (Γ.body (readDom T)) (psBody ps) t
  | .obj o d =>
      match elabF Γ ps (sizePTm (.obj o d)) (.obj o d) none ⟨defaultFuel, false⟩ with
      | ((c :: _, _), t) => !t.out && derivIsObj c.e.deriv
      | _ => false
  | _ => false

/-- `objUnder` on a written program with every self shape erased. -/
def objS (π : PlatformNames) (w : STm) : Bool :=
  match resolvePTop Λc π w with
  | some p => objUnder π.plat.ctx π.set p.eraseSelf
  | none => false

/-- The literal of E2 on its own. -/
def E2objSrc : STm :=
  cc% ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
          {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- C7 with its boxes and its unboxing written, as in `Examples.lean`. -/
def C7boxSrcW : STm :=
  cc% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

/-- The self shape of the literals nested `k` deep: each field holds the next
literal, the innermost the parameter `n : {b : ⊤}`. -/
def nestShape : Nat → SShape
  | 0 => .fld "a" (.capt (.fld "b" (.capt .top [])) [])
  | k + 1 => .fld "a" (.capt (.mu "y" (nestShape k)) [])

/-- Literals nested `k + 1` deep, with their self shapes written when `w`
holds. -/
def nestTm (w : Bool) : Nat → STm
  | 0 => .obj "x" (if w then some (nestShape 0) else none) (.trm "a" none (.var "n"))
  | k + 1 => .obj "x" (if w then some (nestShape (k + 1)) else none) (.trm "a" none (nestTm w k))

/-- `λ(n : {b : ⊤}). ν(x. {a = ν(x. … ν(x. {a = n}) …)})`, the literals nested
`k + 1` deep. -/
def NestKSrc (w : Bool) (k : Nat) : STm :=
  .lam none "n" (SDom.capt (.fld "b" (.capt .top [])) []) (nestTm w k)

-- The erased programs are the written ones with their self shapes erased.
example : (resolvePTop Λc .empty E2objSrc).map PTm.eraseSelf =
    resolvePTop Λc .empty (cc% ν(s. {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})) := by
  decide
example : (resolvePTop Λc .empty E5srcW).map PTm.eraseSelf = resolvePTop Λc .empty E5srcS := by
  decide
example : (resolvePTop Λc .empty (NestKSrc true 2)).map PTm.eraseSelf =
    resolvePTop Λc .empty (NestKSrc false 2) := by
  decide

/-! #### The written self shape formed

Each program elaborates to its written form: the fill, the elaborated term,
the use set and the answer the typer gives that form.  RecW's lambda takes its
domain from the field's written type.  NoShape is a literal with no goal.  E5
and E6 compile at the type of the right-hand side, where the written shapes
name a type member. -/

example : elabSOut .empty E2srcW = ((writtenOut .empty E2srcW).1, ⟨defaultFuel - 61, false⟩) ∧
    writtenOut .empty E2srcW = ((writtenOut .empty E2srcW).1, ⟨defaultFuel - 60, false⟩) ∧
    (writtenOut .empty E2srcW).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E2objSrc = ((writtenOut .empty E2objSrc).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut .empty E2objSrc).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E7srcW = ((writtenOut .empty E7srcW).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenOut .empty E7srcW).1.isOk = true := by
  decide +kernel
example : elabSOut πc accountedSrc =
      ((writtenOut πc accountedSrc).1, ⟨defaultFuel - 36, false⟩) ∧
    (writtenOut πc accountedSrc).1.isOk = true := by
  decide +kernel
example : elabSOut .empty FwdObjSrc = ((writtenOut .empty FwdObjSrc).1, ⟨defaultFuel - 16, false⟩) ∧
    writtenOut .empty FwdObjSrc = ((writtenOut .empty FwdObjSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenOut .empty FwdObjSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc Cap1Src = ((writtenOut πc Cap1Src).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenOut πc Cap1Src).1.isOk = true := by
  decide +kernel
example : elabOut .empty RecWSrcS = ((writtenOut .empty RecObjSrc).1, ⟨defaultFuel - 13, false⟩) ∧
    writtenOut .empty RecObjSrc = ((writtenOut .empty RecObjSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenOut .empty RecObjSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty RecWdSrcS = ((writtenOut .empty RecObjSrc).1, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabOut .empty NoShapeSrcS = ((writtenOut .empty FldTySrc).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut .empty FldTySrc).1.isOk = true := by
  decide +kernel
example : elabSOut .empty E5srcW = ((writtenOut .empty E5srcR).1, ⟨defaultFuel - 11, false⟩) ∧
    writtenOut .empty E5srcW = ((writtenOut .empty E5srcW).1, ⟨defaultFuel - 20, false⟩) ∧
    (writtenOut .empty E5srcR).1.isOk = true := by
  decide +kernel
example : elabOut .empty E6srcS = ((writtenOut .empty E6srcR).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenOut .empty E6srcR).1.isOk = true := by
  decide +kernel
example : elabOut πz Z1litS = ((writtenOut πz Z1litF).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenOut πz Z1litF).1.isOk = true := by
  decide +kernel

/-! #### Another self shape formed

S3, C2, S1, S2, Z3 and BareCap form self shapes other than the written ones,
so their elaborated terms differ from the written terms in the self shapes.
The erased term and the use set are the written program's, and so is the
answer for all but BareCap, whose answer holds the formed shape.  S3, C2 and
BareCap are also compared whole with their forms written at the formed
shapes, and so are SelfProj and C7.  SelfProj's written shape charges `a` at
`{z}`, which the typer rejects, while the formed `{z, f}` compiles. -/

example : (elabSOut πc S3srcW).1.erased = (writtenOut πc S3srcW).1.erased ∧
    elabSOut πc S3srcW = ((writtenOut πc S3srcF).1, ⟨defaultFuel - 15, false⟩) ∧
    writtenOut πc S3srcW = ((writtenOut πc S3srcW).1, ⟨defaultFuel - 46, false⟩) ∧
    (writtenOut πc S3srcW).1.isOk = true := by
  decide +kernel
example : (elabSOut πc C2srcW).1.erased = (writtenOut πc C2srcW).1.erased ∧
    elabSOut πc C2srcW = ((writtenOut πc C2srcF).1, ⟨defaultFuel - 244, false⟩) ∧
    writtenOut πc C2srcW = ((writtenOut πc C2srcW).1, ⟨defaultFuel - 214, false⟩) ∧
    (writtenOut πc C2srcW).1.isOk = true := by
  decide +kernel
example : (elabSOut πz S1srcW).1.erased = (writtenOut πz S1srcW).1.erased ∧
    (elabSOut πz S1srcW).2 = ⟨defaultFuel - 97, false⟩ ∧
    (writtenOut πz S1srcW).1.isOk = true := by
  decide +kernel
example : (elabSOut πz S2srcW).1.erased = (writtenOut πz S2srcW).1.erased ∧
    (elabSOut πz S2srcW).2 = ⟨defaultFuel - 191, false⟩ ∧
    (writtenOut πz S2srcW).1.isOk = true := by
  decide +kernel
example : (elabSOut πz Z3srcW).1.erased = (writtenOut πz Z3srcW).1.erased ∧
    (elabSOut πz Z3srcW).2 = ⟨defaultFuel - 154, false⟩ ∧
    (writtenOut πz Z3srcW).1.isOk = true := by
  decide +kernel
example : ((elabSOut πc BareCapSrc).1.erased.map fun r => (r.1, r.2.1)) =
      ((writtenOut πc BareCapSrc).1.erased.map fun r => (r.1, r.2.1)) ∧
    elabSOut πc BareCapSrc = ((writtenOut πc BareCapSrcF).1, ⟨defaultFuel - 40, false⟩) ∧
    (writtenOut πc BareCapSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc SelfProjSrc = ((writtenOut πc SelfProjSrcF).1, ⟨defaultFuel - 44, false⟩) ∧
    (writtenOut πc SelfProjSrcF).1.isOk = true ∧
    writtenOut πc SelfProjSrc = (.no .mismatch, ⟨defaultFuel - 36, false⟩) := by
  decide +kernel
example : elabSOut πc C7src = ((writtenOut πc C7srcF).1, ⟨defaultFuel - 44, false⟩) ∧
    (writtenOut πc C7srcF).1.isOk = true := by
  decide +kernel

/-! #### The self bare and the least candidate

Bare, FwdSelf and BareProj form `μ(y. ⊤)` for the bare field in the empty
platform.  LamCap forms the shape a programmer writes.  X5a and X5b form
`{v : {b : ⊤}}` in both orders of `y`'s intersection. -/

example : elabOut .empty BareSrcS = ((writtenOut .empty BareSrc).1, ⟨defaultFuel - 15, false⟩) ∧
    (writtenOut .empty BareSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty FwdSelfSrcS =
      ((writtenOut .empty FwdSelfSrc).1, ⟨defaultFuel - 33, false⟩) ∧
    (writtenOut .empty FwdSelfSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty BareProjSrcS =
      ((writtenOut .empty BareProjSrc).1, ⟨defaultFuel - 33, false⟩) ∧
    (writtenOut .empty BareProjSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πc LamCapSrc = ((writtenOut πc LamCapSrc).1, ⟨defaultFuel - 68, false⟩) ∧
    writtenOut πc LamCapSrc = ((writtenOut πc LamCapSrc).1, ⟨defaultFuel - 54, false⟩) ∧
    (writtenOut πc LamCapSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AmbUseSrcS =
      ((writtenOut .empty AmbUseSrc).1, ⟨defaultFuel - 33, false⟩) ∧
    (writtenOut .empty AmbUseSrc).1.isOk = true := by
  decide +kernel
example : elabOut .empty AmbUse2SrcS =
      ((writtenOut .empty AmbUse2Src).1, ⟨defaultFuel - 28, false⟩) ∧
    (writtenOut .empty AmbUse2Src).1.isOk = true := by
  decide +kernel

/-! #### The object rule at the head

The derivation of a literal without a self shape is the typer's on the filled
literal, so with no goal it ends in `HasTy.obj`. -/

example : objS .empty FwdObjSrc = true ∧ objS .empty E2objSrc = true ∧
    objS .empty RecWSrcS = true ∧ objS πc Cap1Src = true ∧ objS .empty BareSrcS = true ∧
    objS πc LamCapSrc = true ∧ objS πc accountedSrc = true := by
  decide +kernel

/-! #### Rejections

Cyc, Rec and AliasRec are cyclic references at `a`, and Cyc3 at `b`.  NE and
NEfresh need an explicit type, Amb is ambiguous, and NoDom's lambda has no
parameter type.  C7box's written unboxing names `{k1}` where the formed box
holds `{f1}`.  Z1, Z1def, Z2 and exTop form `read` pure, and the version has no
subtyping between two `μ` shapes, so the literal does not meet the written
`μ(f. {read : … ^ {f}})`. -/

example : elabOut .empty CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty RecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty AliasRecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut πc Cyc3SrcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabOut .empty NESrcS = (.no (.needsExplicitType (.trm 0)), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel
example : elabOut πz NEfreshSrcS =
    (.no (.needsExplicitType (.trm 0)), ⟨defaultFuel - 24, false⟩) := by
  decide +kernel
example : elabOut .empty AmbSrcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 15, false⟩) := by
  decide +kernel
example : elabOut .empty NoDomSrcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabSOut πc C7boxSrcW = (.no .mismatch, ⟨defaultFuel - 13, false⟩) ∧
    writtenOut πc C7boxSrcW = ((writtenOut πc C7boxSrcW).1, ⟨defaultFuel - 31, false⟩) ∧
    (writtenOut πc C7boxSrcW).1.isOk = true := by
  decide +kernel
example : elabSOut πz Z1srcW = (.no .mismatch, ⟨defaultFuel - 62, false⟩) ∧
    (writtenOut πz Z1srcW).1.isOk = true := by
  decide +kernel
example : elabSOut πz Z1defSrc = (.no .mismatch, ⟨defaultFuel - 112, false⟩) ∧
    (writtenOut πz Z1defSrc).1.isOk = true := by
  decide +kernel
example : elabSOut πz Z2srcW = (.no .mismatch, ⟨defaultFuel - 62, false⟩) ∧
    (writtenOut πz Z2srcW).1.isOk = true := by
  decide +kernel
example : elabSOut πz exTopSrc = (.no .mismatch, ⟨defaultFuel - 62, false⟩) := by
  decide +kernel

/-! #### Nested literals

`NestKSrc false k` nests `k + 1` literals without a self shape.  Each field is
elaborated once and checked once more by the typer at each enclosing literal,
so the fuel is `(k + 1) (k + 2) / 2`, against `k + 3` for the written form. -/

example : elabOut .empty (NestKSrc false 2) =
      ((writtenOut .empty (NestKSrc true 2)).1, ⟨defaultFuel - 10, false⟩) ∧
    writtenOut .empty (NestKSrc true 2) =
      ((writtenOut .empty (NestKSrc true 2)).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenOut .empty (NestKSrc true 2)).1.isOk = true := by
  decide +kernel
example : elabOut .empty (NestKSrc false 4) =
      ((writtenOut .empty (NestKSrc true 4)).1, ⟨defaultFuel - 21, false⟩) ∧
    writtenOut .empty (NestKSrc true 4) =
      ((writtenOut .empty (NestKSrc true 4)).1, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabOut .empty (NestKSrc false 8) =
      ((writtenOut .empty (NestKSrc true 8)).1, ⟨defaultFuel - 55, false⟩) ∧
    writtenOut .empty (NestKSrc true 8) =
      ((writtenOut .empty (NestKSrc true 8)).1, ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : elabOut .empty (NestKSrc false 12) =
      ((writtenOut .empty (NestKSrc true 12)).1, ⟨defaultFuel - 105, false⟩) ∧
    writtenOut .empty (NestKSrc true 12) =
      ((writtenOut .empty (NestKSrc true 12)).1, ⟨defaultFuel - 15, false⟩) := by
  decide +kernel
example : elabOut .empty (NestKSrc false 16) =
      ((writtenOut .empty (NestKSrc true 16)).1, ⟨defaultFuel - 171, false⟩) ∧
    writtenOut .empty (NestKSrc true 16) =
      ((writtenOut .empty (NestKSrc true 16)).1, ⟨defaultFuel - 19, false⟩) ∧
    (writtenOut .empty (NestKSrc true 16)).1.isOk = true := by
  decide +kernel

end ElabChecks

end CapturesCCFrontend
