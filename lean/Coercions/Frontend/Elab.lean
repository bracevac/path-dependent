import Coercions.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# The elaborator

The elaborator fills the empty slots of a partial term (`PTm`, `Ann.lean`) and
types the result with the typer of `Typer.lean`, on the same tank.

## The rule of empty slots

Each function first asks `PTm.full?`.  A term with no empty slot goes to the
typer as it is: `elabF` calls `synthF`, and `elabChkF` calls `checkOf`.  So a
program with every slot written elaborates as the typer types it, at the same
fuel (`elabF_toI`, `elabChkF_toI`).  Only a term with an empty slot below it
takes the clauses of this module.

## Two modes

`elabF` synthesizes.  It returns candidates, each an elaborated term, its type
and the `DotMNF.HasTy` derivation of its erasure, as `synthF` does.
`elabChkF` checks against a goal and returns the elaborated term with a
derivation at the goal.  `elabDefsF` checks definitions against a self type in
lockstep.  Every result carries `p.fills a = true`: the elaborated term agrees
with every slot the program writes.

## Where a goal reaches a term

- A written `let` type is the goal of the body, under the binder.
- An ascription `let y : U = t in y` gives `U` to `t`.  The resolver writes
  `(t : U)` so.
- A call argument `let z = t in g z`, the binding the resolver inserts at an
  operand, gives `t` the dominant formal of `g`: the parameter type of one of
  the function types the lookup finds for `g`, with every other one below it.
  An intersection of function types gives several, and the compiler types the
  argument against their least upper bound (`TypeComparer.distributeAnd`).  The
  version has no union, so the dominant formal is that bound when it exists.
  The argument is filled at that goal, and the filled `let` goes to the typer,
  as `Applications.typedApply` types an argument against its formal.
- A field of a literal with a self type gets the field's declaration.
- A lambda's body gets the result part of the goal.
- A block `let x = t in u` passes its goal to `u`, as `Typer.typedBlock` does.

## Lambdas

A lambda without a domain takes it from the function part of its goal
(`funPartF`), as `Typer.typedFunctionValue` does through
`Typer.decomposeProtoFunction` and `Type.findFunctionType`.  A selection whose
member has equal bounds is replaced by the bound, to a fixpoint, as
`strippedDealias` follows aliases.  `∀(x : S) V` gives `S` and `V`.  The sides
of an intersection meet.  One function side gives that side.  Two sides whose
domains are comparable give the larger domain and the intersection of the
results.  Two sides with incomparable domains are a mismatch, since the
compiler forms their union, which the version lacks.  A selection with
different bounds whose upper bound has a function part is a mismatch, as for an
abstract type with a function upper bound in the compiler.  Any other goal has
no function part, and the lambda is the compiler's "Missing parameter type".
So is a lambda with no goal.

The one exception is a body `g x` that applies a variable `g` bound outside
the lambda to the parameter.  With no goal, or a goal with no function part,
such a lambda takes the dominant formal of `g` as its domain, as
`Typer.inferredFromTarget` takes the parameter type of the callee it finds in
the body (`calleeType`).  The compiler types the argument of an intersection of
function types against the union of their formals, and the version has no
union, so the dominant formal stands for it, as at a call argument.  A callee
with no dominant formal leaves the parameter type missing.  The filled lambda
goes to the typer.

A lambda whose body has no empty slot is filled with the domain and handed to
the typer at the goal (`lam_fill_full`).  Otherwise the body is checked against
the result part, and the lambda is moved to the goal by the subtyping goal.  A
lambda with a written domain whose body has an empty slot passes the result
part to its body in the same way.

## The fallback

A goal site whose attempt fails with the tank unmarked runs the typer's own
route on the term: synthesis, then subsumption to the goal.  So erasing a slot
at a goal site never loses a program whose filled form types by that route.

## Object literals

A literal with a self type has its definitions elaborated against it, with the
self bound at its `μ`.  The literal with its slots filled then goes to
`synthF`, whose object clause gives `HasTy.obj` in the real context.  A literal
without a self type, checked at a goal that dealiases to a `μ`, takes the body
of that `μ` as its self type (`selfGoalF`).  If that attempt fails with the
tank unmarked, or the goal gives no self type, or there is no goal, the self
type is formed from the definitions (`formSelfF`, below).  The literal is then
filled at it (`fillDefsF`): a field without a written type holds the term the
rounds elaborated for it, and a field with a written type is elaborated
against that type with the self at the formed type.  The filled literal goes
to `synthF` in the real context, so its derivation is `HasTy.obj`, and each
field is elaborated once and checked once more.  At a goal the candidate is
then subsumed.

## Self types formed from definitions

`formSelfF` forms the self type of a literal from its definitions, as the
completers of `Namer` type the members of a class.  Type members and fields
with a written type are known at once.  Every other field is a job
(`jobsF`), typed in rounds (`roundsF`).  A round takes a snapshot of the self
type known so far and types every ready job once, by synthesis, with the self
bound at the snapshot.  A job is ready when none of the fields it projects off
the self is pending (`PTm.deps`).  A job that uses the self any other way is
typed in the first round in which no ready job lacks such a use.  A field's
type is its least candidate (`leastCandF`), and candidates with no least one
are ambiguous.  A round that types nothing stops with the cyclic reference
`cycleAt` names.  The self type is the definition list read in lockstep
(`PDefs.fullSelf`).

## Reasons

Each function returns the reasons of its failed branches in search order.
`elabTopF` reports the recursion limit when the tank ended marked, else the
first reason, else a mismatch (`Reason.top`).

## The theorems

`elabF_toI` and `elabChkF_toI` say that a term with every slot written is the
typer's, at the same fuel.  `elabF_framed`, `elabChkF_framed`,
`elabDefsF_framed` and `funPartAt_framed` say that each computation keeps a
marked tank, never adds fuel, and does the same with more fuel.
`elabChkF_lam_formal` says that a filled domain is the domain of the goal's
function part, or, at a goal with no function part, the dominant formal of the
callee of the body `g x`.  `elabF_lam_formal` says the second for a lambda
with no goal.  `argGoal_dominant` says that every formal of a callee is below
the goal of its argument.  `lam_fill_full` says that a lambda whose body has no
empty slot is the typer's check of the filled lambda, on the tank the function
part left.  `lam_callee_full` and `lam_callee_chk_full` say the same of a body
`g x` filled with the dominant formal of `g`.

`fullSelf_lockstep` says that a formed self type is in lockstep with the
definitions.  `jobsF_written` says that definitions whose fields all have a
written type make no job.  `leastCand_least` says that the type of the least
candidate is below the type of every candidate, and `leastCand_sub?` says so
with the typer's subtyping at some fuel.  `cycleAt_onCycle` says that the
cyclic reference is the label of a pending job whose walk comes back to it.
`roundsF_framed` and `jobsF_framed` say that the rounds are framed.
`obj_none_landed` says that a candidate of a literal without a self type is a
candidate of `synthF` on the filled literal, at the self type the rounds
formed.
-/

namespace Frontend

open Frontend.Fuel Frontend.Core Frontend.Reason
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Value Defs Ctx Sub HasTy DefsTy)

/-- The reasons of this front end: its labels, and no reason of the typer's
own. -/
abbrev EReason := Reason Label Empty

/-! ## Agreement with a written slot -/

/-- A slot agrees with a value when it is empty or holds that value. -/
def optAgree {α : Type} [DecidableEq α] : Option α → α → Bool
  | some x, y => decide (x = y)
  | none, _ => true

theorem optAgree_some {α : Type} [DecidableEq α] (x : α) : optAgree (some x) x = true := by
  simp [optAgree]

theorem PTm.fills_lam {s : Sig} {o : Option (Ty s)} {t : PTm (s,x)} {S : Ty s} {a : ATm (s,x)}
    (ho : optAgree o S = true) (h : t.fills a = true) : (PTm.lam o t).fills (.lam S a) = true := by
  cases o <;> simp_all [PTm.fills, optAgree]

theorem PTm.fills_obj {s : Sig} {o : Option (Ty (s,x))} {d : PDefs (s,x)} {T : Ty (s,x)}
    {e : ADefs (s,x)} (ho : optAgree o T = true) (h : d.fills T e = true) :
    (PTm.obj o d).fills (.obj T e) = true := by
  cases o <;> simp_all [PTm.fills, optAgree]

theorem PTm.fills_let {s : Sig} {g : LetTag} {o : Option (Ty s)} {t : PTm s} {u : PTm (s,x)}
    {a : ATm s} {b : ATm (s,x)} (ht : t.fills a = true) (hu : u.fills b = true) :
    (PTm.let g o t u).fills (.let o a b) = true := by
  simp [PTm.fills, ht, hu]

theorem PTm.fills_app {s : Sig} (x y : BVar s .var) : (PTm.app x y).fills (.app x y) = true := by
  simp [PTm.fills]

theorem PDefs.fills_typ {s : Sig} (A : Label) (S U : Ty s) :
    (PDefs.typ A S).fills U (.typ A S) = true := by
  simp [PDefs.fills]

theorem PDefs.fills_trm {s : Sig} {a c : Label} {o : Option (Ty s)} {t : PTm s} {U : Ty s}
    {b : ATm s} (ho : optAgree o U = true) (h : t.fills b = true) :
    (PDefs.trm a o t).fills (.fld c U) (.trm a b) = true := by
  cases o <;> simp_all [PDefs.fills, optAgree]

theorem PDefs.fills_and {s : Sig} {d1 d2 : PDefs s} {T1 T2 : Ty s} {e1 e2 : ADefs s}
    (h1 : d1.fills T1 e1 = true) (h2 : d2.fills T2 e2 = true) :
    (PDefs.and d1 d2).fills (.and T1 T2) (.and e1 e2) = true := by
  simp [PDefs.fills, andLeft, andRight, h1, h2]

/-! ## Results -/

/-- A synthesized candidate: the elaborated term, its type, the derivation of
its erasure, and its agreement with the written slots. -/
structure ECand {s : Sig} (Γ : Ctx s) (p : PTm s) where
  /-- The elaborated term. -/
  a : ATm s
  /-- Its type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ a.erase ty
  /-- The term agrees with every written slot of `p`. -/
  fills : p.fills a = true

/-- A term checked at `G`: the elaborated term, the derivation at `G`, and its
agreement with the written slots. -/
structure EChk {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s) where
  /-- The elaborated term. -/
  a : ATm s
  /-- The derivation at the goal. -/
  deriv : HasTy Γ a.erase G
  /-- The term agrees with every written slot of `p`. -/
  fills : p.fills a = true

/-- Definitions checked against a self type `T` in lockstep. -/
structure EDefs {s : Sig} (Γ : Ctx s) (d : PDefs s) (T : Ty s) where
  /-- The elaborated definitions. -/
  ds : ADefs s
  /-- The derivation against `T`. -/
  deriv : DefsTy Γ ds.erase T
  /-- The definitions agree with every written slot of `d`, at `T`. -/
  fills : d.fills T ds = true

/-- The candidates of a synthesis, with the reasons of its failed branches. -/
abbrev ESynth {s : Sig} (Γ : Ctx s) (p : PTm s) := List (ECand Γ p) × List EReason

/-- The answer of a check, with the reasons of its failed branches. -/
abbrev ECheck {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s) := Option (EChk Γ p G) × List EReason

/-- The answer of a definition check, with the reasons of its failed branches. -/
abbrev EDefsR {s : Sig} (Γ : Ctx s) (d : PDefs s) (T : Ty s) :=
  Option (EDefs Γ d T) × List EReason

/-! ## Combinators with reasons -/

/-- The answer `a` when `stop` holds or the tank is marked, else `c`. -/
def stopOr {β : Type} (stop : Bool) (a : β) (c : Fu β) : Fu β := fun t =>
  if stop || t.out then (a, t) else c t

/-- Run `a`.  On an answer `ok` accepts, or on a marked tank, stop.  Otherwise
run `b` from the tank `a` left and keep the reasons of both. -/
def orElseW {α ρ : Type} (ok : α → Bool) (a : Fu (α × List ρ)) (b : Unit → Fu (α × List ρ)) :
    Fu (α × List ρ) :=
  Fu.bind a fun r => stopOr (ok r.1) r (Fu.bind (b ()) fun r' => Fu.ret (r'.1, r.2 ++ r'.2))

/-- The first answer over a list, in order, with the reasons of the failed
tries. -/
def firstSomeR {α β ρ : Type} (f : α → Fu (Option β × List ρ)) : List α → Fu (Option β × List ρ)
  | [] => Fu.ret (none, [])
  | x :: xs => orElseW Option.isSome (f x) (fun _ => firstSomeR f xs)

/-- Every answer over a list, in order, with every reason. -/
def flatMapR {α β ρ : Type} (f : α → Fu (List β × List ρ)) : List α → Fu (List β × List ρ)
  | [] => Fu.ret ([], [])
  | x :: xs =>
      Fu.bind (f x) fun r1 => Fu.bind (flatMapR f xs) fun r2 => Fu.ret (r1.1 ++ r2.1, r1.2 ++ r2.2)

/-- Keep the first candidate of each type. -/
def dedupE {s : Sig} {Γ : Ctx s} {p : PTm s} : List (ECand Γ p) → List (ECand Γ p)
  | [] => []
  | c :: cs => c :: (dedupE cs).filter fun c' => !decide (c'.ty = c.ty)

/-- A candidate moved to the goal: as it is when its type is the goal, by the
subtyping goal otherwise. -/
def toGoal {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (c : ECand Γ p) : Fu (ECheck Γ p G) :=
  if h : c.ty = G then Fu.ret (some ⟨c.a, h ▸ c.deriv, c.fills⟩, [])
  else
    Fu.bind (subF Γ c.ty G) fun o =>
      Fu.ret (o.map (fun e => ⟨c.a, .sub c.deriv e, c.fills⟩), if o.isSome then [] else [.mismatch])

/-- The first candidate the subtyping goal moves to `G`. -/
def subsume {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) : Fu (ECheck Γ p G) :=
  Fu.bind (firstSomeR (toGoal Γ G) r.1) fun r' => Fu.ret (r'.1, r.2 ++ r'.2)

/-- The answer `a` with the tank marked: the recursion limit. -/
def markAs {α : Type} (a : α) : Fu α := fun t => (a, { t with out := true })

/-! ## The typer on a filled term -/

/-- The candidates `synthF` gives a filled term `a`, as candidates of the partial
term `p` it fills. -/
def fullSynthAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) :
    Fu (ESynth Γ p) :=
  Fu.bind (synthF Γ a) fun cs =>
    Fu.ret (cs.map fun c => ⟨a, c.ty, c.deriv, h⟩, if cs.isEmpty then [.mismatch] else [])

/-- The check `checkOf` gives a filled term `a` at `G`, as a check of the partial
term `p` it fills. -/
def fullCheckAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) (G : Ty s) :
    Fu (ECheck Γ p G) :=
  Fu.bind (checkOf Γ a G (synthF Γ a)) fun o =>
    Fu.ret (o.map fun hd => ⟨a, hd, h⟩, if o.isSome then [] else [.mismatch])

/-- The typer's synthesis of a term with every slot written. -/
def fullSynth {s : Sig} (Γ : Ctx s) (a : ATm s) : Fu (ESynth Γ a.toI) :=
  fullSynthAt Γ a.toI a (ATm.fills_toI a)

/-- The typer's check of a term with every slot written. -/
def fullCheck {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Ty s) : Fu (ECheck Γ a.toI G) :=
  fullCheckAt Γ a.toI a (ATm.fills_toI a) G

/-! ## The function part of a goal

`Type.findFunctionType` on the types of the version, after `strippedDealias`.
The lookups draw on the tank.  The index of `funPartF` bounds the number of
aliases followed.  `funPartAt` starts it at the fuel left, as `declsAt` starts
a lookup, and every alias followed draws at least one unit, so the index never
runs out first. -/

/-- The function part of a goal: none, a domain and a result, or a mismatch. -/
inductive FunPart (s : Sig) where
  /-- No function part, the compiler's missing parameter type. -/
  | none
  /-- The domain `S` and the result part `V`. -/
  | one (S : Ty s) (V : Ty (s,x))
  /-- A function part the version cannot give, a type mismatch. -/
  | bad

/-- The upper bound of the first member with equal bounds, an alias. -/
def aliasOf {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} : List (TyMem Γ y A) → Option (Ty s)
  | [] => none
  | m :: ms => if m.1 = m.2.1 then some m.2.1 else aliasOf ms

/-- `bad` when one of the upper bounds has a function part, `none` otherwise. -/
def uppersPart {s : Sig} (rec : Ty s → Fu (FunPart s)) : List (Ty s) → Fu (FunPart s)
  | [] => Fu.ret .none
  | T :: Ts =>
      Fu.bind (rec T) fun f =>
        match f with
        | .none => uppersPart rec Ts
        | _ => Fu.ret .bad

/-- The meet of the function parts of two sides of an intersection, as
`findFunctionType` meets them with `&`.  Comparable domains give the larger
one and the intersection of the results. -/
def meetPart {s : Sig} (Γ : Ctx s) : FunPart s → FunPart s → Fu (FunPart s)
  | .bad, _ => Fu.ret .bad
  | _, .bad => Fu.ret .bad
  | .none, f => Fu.ret f
  | f, .none => Fu.ret f
  | .one S1 V1, .one S2 V2 =>
      Fu.bind (subF Γ S2 S1) fun o2 =>
        match o2 with
        | some _ => Fu.ret (.one S1 (.and V1 V2))
        | none =>
            Fu.bind (subF Γ S1 S2) fun o1 =>
              match o1 with
              | some _ => Fu.ret (.one S2 (.and V1 V2))
              | none => Fu.ret .bad

/-- The function part of a type, with `rec` for the type an alias stands for
and for an upper bound. -/
def funPartTy {s : Sig} (Γ : Ctx s) (rec : Ty s → Fu (FunPart s)) : Ty s → Fu (FunPart s)
  | .all S V => Fu.ret (.one S V)
  | .and G1 G2 =>
      Fu.bind (funPartTy Γ rec G1) fun f1 => Fu.bind (funPartTy Γ rec G2) fun f2 => meetPart Γ f1 f2
  | .sel (.var y) A =>
      Fu.bind (declsAt Γ y A) fun ms =>
        match aliasOf ms with
        | some T => rec T
        | none => uppersPart rec (ms.map fun m => m.2.1)
  | .top => Fu.ret .none
  | .bot => Fu.ret .none
  | .typ _ _ _ => Fu.ret .none
  | .fld _ _ => Fu.ret .none
  | .mu _ => Fu.ret .none

/-- The function part of a goal, following at most `d` aliases.  One more
marks the tank. -/
def funPartF {s : Sig} (Γ : Ctx s) : Nat → Ty s → Fu (FunPart s)
  | 0, G => funPartTy Γ (fun _ => markAs .none) G
  | d + 1, G => funPartTy Γ (funPartF Γ d) G

/-- The function part of a goal, from the fuel left. -/
def funPartAt {s : Sig} (Γ : Ctx s) (G : Ty s) : Fu (FunPart s) := fun t => funPartF Γ t.left G t

/-! ## The self type a goal gives a literal -/

/-- A type with its head aliases followed, with `rec` for the next step. -/
def dealiasTy {s : Sig} (Γ : Ctx s) (rec : Ty s → Fu (Ty s)) : Ty s → Fu (Ty s)
  | .sel (.var y) A =>
      Fu.bind (declsAt Γ y A) fun ms =>
        match aliasOf ms with
        | some T => rec T
        | none => Fu.ret (.sel (.var y) A)
  | .top => Fu.ret .top
  | .bot => Fu.ret .bot
  | .typ A S T => Fu.ret (.typ A S T)
  | .fld a T => Fu.ret (.fld a T)
  | .mu T => Fu.ret (.mu T)
  | .all S T => Fu.ret (.all S T)
  | .and S T => Fu.ret (.and S T)

/-- A type with at most `d` head aliases followed.  One more marks the tank. -/
def dealiasF {s : Sig} (Γ : Ctx s) : Nat → Ty s → Fu (Ty s)
  | 0, G => dealiasTy Γ markAs G
  | d + 1, G => dealiasTy Γ (dealiasF Γ d) G

/-- A type with its head aliases followed, from the fuel left. -/
def dealiasAt {s : Sig} (Γ : Ctx s) (G : Ty s) : Fu (Ty s) := fun t => dealiasF Γ t.left G t

/-- The self type a goal gives a literal: the body of the `μ` it dealiases
to.  Scala makes a class `pt` the parent of `new { … }` (`Typer.typedNew`),
and every type of the version is structural, so a `μ` goal plays the class. -/
def selfGoalF {s : Sig} (Γ : Ctx s) (G : Ty s) : Fu (Option (Ty (s,x))) :=
  Fu.bind (dealiasAt Γ G) fun G' =>
    match G' with
    | .mu T => Fu.ret (some T)
    | _ => Fu.ret none

/-! ## The goal of a call argument -/

/-- The parameter types of the function types the lookup finds for `g`. -/
def formalsF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (List (Ty s)) :=
  Fu.bind (lookVar Γ g .fn) fun es => Fu.ret (es.filterMap fun e => e.all?.map (·.1))

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

/-- The goal of an argument of `g`: its dominant formal, the whole parameter
type with its result.  `none` when `g` has no function type or no formal is
dominant. -/
def argGoalF {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Fu (Option (Ty s)) :=
  Fu.bind (formalsF Γ g) fun Fs => dominantF Γ Fs Fs

/-! ## Lambdas -/

/-- The candidates of a lambda with domain `S`, from those of its body. -/
def lamCands {s : Sig} {Γ : Ctx s} {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (ho : optAgree o S = true) (r : ESynth (Γ.cons S) t) : ESynth Γ (.lam o t) :=
  (r.1.map fun c => ⟨.lam S c.a, .all S c.ty, .lam c.deriv, PTm.fills_lam ho c.fills⟩, r.2)

/-- A lambda with domain `S`, whose body has an empty slot, checked at `G`
whose result part is `V`.  The body is checked against `V`, and the lambda is
moved to `G`.  On an unmarked failure the body is synthesized under `S` and the
lambda subsumed. -/
def lamGoalF {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s) (V : Ty (s,x))
    (G : Ty s) (ho : optAgree o S = true) (chk : Fu (ECheck (Γ.cons S) t V))
    (syn : Unit → Fu (ESynth (Γ.cons S) t)) : Fu (ECheck Γ (.lam o t) G) :=
  orElseW Option.isSome
    (Fu.bind chk fun r =>
      match r.1 with
      | some e => toGoal Γ G ⟨.lam S e.a, .all S V, .lam e.deriv, PTm.fills_lam ho e.fills⟩
      | none => Fu.ret (none, r.2))
    (fun _ => Fu.bind (syn ()) fun r => subsume Γ G (lamCands S ho r))

/-- A lambda without a domain at a goal whose function part has the domain `S`
and the result part `V`.  With a body that has no empty slot, the lambda
filled with `S` goes to `checkOf`.  Otherwise `lamGoalF`. -/
def lamOneChkF {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (S : Ty s) (V : Ty (s,x)) (G : Ty s)
    (chk : Fu (ECheck (Γ.cons S) t V)) (syn : Unit → Fu (ESynth (Γ.cons S) t)) :
    Fu (ECheck Γ (.lam none t) G) :=
  match ht : t.full? with
  | some b => fullCheckAt Γ (.lam none t) (.lam S b) (PTm.fills_lam rfl (PTm.fills_of_full? ht)) G
  | none => lamGoalF Γ S V G rfl chk syn

/-- A variable under one more binder, as a variable outside it: `none` for the
innermost binder. -/
def BVar.outer? {s : Sig} {k0 k : Kind} : BVar (s,,k0) k → Option (BVar s k)
  | .here => none
  | .there y => some y

/-- The callee of a lambda's body `g x`: `g`, when `x` is the lambda's
parameter and `g` a variable bound outside the lambda.  This is the body whose
callee `Typer.typedFunctionValue` types to find a parameter type
(`calleeType`). -/
def calleeOf? {s : Sig} : PTm (s,x) → Option (BVar s .var)
  | .app f y => if y = .here then BVar.outer? f else none
  | _ => none

/-- A lambda without a domain and without a goal.  A body `g x` gives the
domain: the dominant formal of `g`, the goal `g` gives its argument.  The
filled lambda goes to `synthF`.  Any other body, or a callee with no dominant
formal, is the compiler's missing parameter type. -/
def lamCalleeSynF {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) : Fu (ESynth Γ (.lam none t)) :=
  match calleeOf? t with
  | some g =>
      Fu.bind (argGoalF Γ g) fun oS =>
        match oS with
        | some S =>
            match ht : t.full? with
            | some b => fullSynthAt Γ _ (.lam S b) (PTm.fills_lam rfl (PTm.fills_of_full? ht))
            | none => Fu.ret ([], [.missingParamType none])
        | none => Fu.ret ([], [.missingParamType none])
  | none => Fu.ret ([], [.missingParamType none])

/-- A lambda without a domain at a goal with no function part, as
`lamCalleeSynF`, with `checkOf` on the filled lambda at `G`. -/
def lamCalleeChkF {s : Sig} (Γ : Ctx s) (G : Ty s) (t : PTm (s,x)) : Fu (ECheck Γ (.lam none t) G) :=
  match calleeOf? t with
  | some g =>
      Fu.bind (argGoalF Γ g) fun oS =>
        match oS with
        | some S =>
            match ht : t.full? with
            | some b => fullCheckAt Γ _ (.lam S b) (PTm.fills_lam rfl (PTm.fills_of_full? ht)) G
            | none => Fu.ret (none, [.missingParamType none])
        | none => Fu.ret (none, [.missingParamType none])
  | none => Fu.ret (none, [.missingParamType none])

/-- A lambda without a domain checked at `G`.  The domain is the domain of the
function part of `G`.  With no function part, a body `g x` gives the domain
(`lamCalleeChkF`), and any other body is the compiler's missing parameter type.
A function part the version cannot give is a mismatch. -/
def lamNoneChkF {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (G : Ty s)
    (chk : (S : Ty s) → (V : Ty (s,x)) → Fu (ECheck (Γ.cons S) t V))
    (syn : (S : Ty s) → Fu (ESynth (Γ.cons S) t)) : Fu (ECheck Γ (.lam none t) G) :=
  Fu.bind (funPartAt Γ G) fun fp =>
    match fp with
    | .one S V => lamOneChkF Γ t S V G (chk S V) (fun _ => syn S)
    | .none => lamCalleeChkF Γ G t
    | .bad => Fu.ret (none, [.mismatch])

/-! ## Object literals -/

/-- A literal with self type `T`: its definitions elaborated against `T` with
the self at `μ` of it, then the filled literal typed by `synthF`. -/
def objSelfF {s : Sig} (Γ : Ctx s) {o : Option (Ty (s,x))} {d : PDefs (s,x)} (T : Ty (s,x))
    (ho : optAgree o T = true) (defs : Fu (EDefsR (Γ.cons (.mu T)) d T)) :
    Fu (ESynth Γ (.obj o d)) :=
  Fu.bind defs fun r =>
    match r.1 with
    | some e => fullSynthAt Γ (.obj o d) (.obj T e.ds) (PTm.fills_obj ho e.fills)
    | none => Fu.ret ([], r.2)

/-! ## Self types formed from definitions

A literal without a self type has it formed from its definitions, as the
completers of `Namer` type the members of a class.  A type member is known at
once at its right-hand side on both bounds (`Namer.TypeDefCompleter.typeSig`).
A field with a written type is known at once at it (`Namer.valOrDefDefSig`).
Every other field is typed on demand (`Namer.inferredResultType`), in rounds.
`known` lists the fields typed so far, by label. -/

/-- The first entry at a label. -/
def lookupL {β : Type} : List (Label × β) → Label → Option β
  | [], _ => none
  | (b, v) :: l, a => if a = b then some v else lookupL l a

/-- The self type the definitions have so far.  A field not yet typed is left
out, and `none` means that nothing is known. -/
def PDefs.partialSelf {s : Sig} : PDefs s → List (Label × Ty s) → Option (Ty s)
  | .typ A T, _ => some (.typ A T T)
  | .trm a (some U) _, _ => some (.fld a U)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.partialSelf known, e.partialSelf known with
      | some T1, some T2 => some (.and T1 T2)
      | some T1, none => some T1
      | none, o => o

/-- The snapshot a round types its jobs against: the self type known so far,
or `⊤` when nothing is. -/
def PDefs.probeSelf {s : Sig} (d : PDefs s) (known : List (Label × Ty s)) : Ty s :=
  (d.partialSelf known).getD .top

/-- The self type in lockstep with the definitions, once every field is typed:
the shape `DefsTy` concludes and `checkDefsF` reads. -/
def PDefs.fullSelf {s : Sig} : PDefs s → List (Label × Ty s) → Option (Ty s)
  | .typ A T, _ => some (.typ A T T)
  | .trm a (some U) _, _ => some (.fld a U)
  | .trm a none _, known => (lookupL known a).map (.fld a)
  | .and d e, known =>
      match d.fullSelf known, e.fullSelf known with
      | some T1, some T2 => some (.and T1 T2)
      | _, _ => none

/-- `T` is the self type of `d` in lockstep.  A type member gives its
right-hand side on both bounds, a field with a written type that type, any
other field the first type `known` gives its label, and an intersection of
definitions the intersection of their self types. -/
inductive Lockstep {s : Sig} (known : List (Label × Ty s)) : PDefs s → Ty s → Prop where
  /-- `{type A = T}` at `{A : T .. T}`. -/
  | typ (A : Label) (T : Ty s) : Lockstep known (.typ A T) (.typ A T T)
  /-- `{a : U = t}` at `{a : U}`. -/
  | written (a : Label) (U : Ty s) (t : PTm s) : Lockstep known (.trm a (some U) t) (.fld a U)
  /-- `{a = t}` at `{a : U}`, with `U` the type known at `a`. -/
  | inferred (a : Label) (U : Ty s) (t : PTm s) (h : lookupL known a = some U) :
      Lockstep known (.trm a none t) (.fld a U)
  /-- `d1 ∧ d2` at `T1 ∧ T2`. -/
  | and {d1 d2 : PDefs s} {T1 T2 : Ty s} :
      Lockstep known d1 T1 → Lockstep known d2 T2 → Lockstep known (.and d1 d2) (.and T1 T2)

/-- Every field of the definitions has a written type. -/
def PDefs.AllFieldsWritten {s : Sig} : PDefs s → Prop
  | .typ _ _ => True
  | .trm _ o _ => o.isSome = true
  | .and d e => d.AllFieldsWritten ∧ e.AllFieldsWritten

/-! ## Jobs

A job is a field without a written type.  It carries its synthesis as a
function of the context, so that a round can run it with the self bound at the
snapshot.  `jobsF` makes the jobs of a definition list inside the elaborator's
mutual block, where the synthesis of a field is a call on a subterm. -/

/-- A field without a written type: its label, its right-hand side, and its
synthesis in a context. -/
structure Job (s : Sig) where
  /-- The field's label. -/
  lbl : Label
  /-- The right-hand side. -/
  tm : PTm s
  /-- The synthesis of the right-hand side. -/
  run : (Γ : Ctx s) → Fu (ESynth Γ tm)

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
  /-- Its type, the least candidate. -/
  ty : Ty s
  /-- The elaborated term agrees with every written slot. -/
  fills : tm.fills a = true

/-- The fields typed so far, by label. -/
def Done.known {s : Sig} (ds : List (Done s)) : List (Label × Ty s) :=
  ds.map fun e => (e.lbl, e.ty)

/-! ## The least candidate

A field's type is the least type of its candidates: the type of the first
candidate that is below every other one by the subtyping goal.  Every candidate
is a type of the right-hand side, so a use that needs another one reaches it by
subsumption.  The choice does not depend on the order of an intersection.  The
compiler meets the candidates with `Denotation.meet`, which the version cannot
derive for a term that is not a variable, so candidates with no least one are
rejected as ambiguous. -/

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

/-- The first candidate of the list whose type is below every type of `Ts`. -/
def leastFromF {s : Sig} (Γ : Ctx s) {p : PTm s} (Ts : List (Ty s)) :
    List (ECand Γ p) → Fu (Option (ECand Γ p))
  | [] => Fu.ret none
  | c :: rest =>
      Fu.bind (belowAllF Γ c.ty Ts) fun b => if b then Fu.ret (some c) else leastFromF Γ Ts rest

/-- The least candidate: the first one whose type is below the type of every
candidate. -/
def leastCandF {s : Sig} (Γ : Ctx s) {p : PTm s} (cs : List (ECand Γ p)) :
    Fu (Option (ECand Γ p)) :=
  leastFromF Γ (cs.map (·.ty)) cs

/-! ## Rounds

A round takes a snapshot of the self type known so far and types every ready
job once, by synthesis, with the self bound at the snapshot.  A job is ready
when none of the labels it projects off the self is pending.  A job that uses
the self any other way waits for the first round in which no ready job lacks
such a use.  So two such jobs do not see each other, and a job that projects
the field of one sees it.  The number of rounds is an index, so the rounds are
structural. -/

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

/-- A job typed against the snapshot `P`: its synthesis with the self at
`μ(x. P)`, and its type the least candidate.  No candidate gives the reasons
of the synthesis, and candidates with no least one give `ambiguous`. -/
def runJobF {s : Sig} (Γ : Ctx s) (P : Ty (s,x)) (j : Job (s,x)) :
    Fu (Except (List EReason) (Done (s,x))) :=
  Fu.bind (j.run (Γ.cons (.mu P))) fun r =>
    match r.1 with
    | [] => Fu.ret (.error r.2)
    | c :: cs =>
        Fu.bind (leastCandF (Γ.cons (.mu P)) (c :: cs)) fun o =>
          match o with
          | some e => Fu.ret (.ok ⟨j.lbl, j.tm, e.a, e.ty, e.fills⟩)
          | none => Fu.ret (.error [.ambiguous j.lbl])

/-- One round: the jobs typed against the snapshot `P`, in source order.  The
first failure stops it. -/
def roundF {s : Sig} (Γ : Ctx s) (P : Ty (s,x)) :
    List (Job (s,x)) → Fu (Except (List EReason) (List (Done (s,x))))
  | [] => Fu.ret (.ok [])
  | j :: js =>
      Fu.bind (runJobF Γ P j) fun r =>
        match r with
        | .ok e =>
            Fu.bind (roundF Γ P js) fun r' =>
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
def roundsF {s : Sig} (Γ : Ctx s) (probe : List (Label × Ty (s,x)) → Ty (s,x)) :
    Nat → List (Job (s,x)) → List (Done (s,x)) → Fu (Except (List EReason) (List (Done (s,x))))
  | _, [], done => Fu.ret (.ok done)
  | 0, j :: js, _ => Fu.ret (.error [stallReason (j :: js)])
  | n + 1, j :: js, done =>
      if ((j :: js).filter (picks (j :: js))).isEmpty then Fu.ret (.error [stallReason (j :: js)])
      else
        Fu.bind (roundF Γ (probe (Done.known done)) ((j :: js).filter (picks (j :: js)))) fun r =>
          match r with
          | .ok new => roundsF Γ probe n ((j :: js).filter fun k => !picks (j :: js) k) (done ++ new)
          | .error rs => Fu.ret (.error rs)

/-- The self type of a literal formed from its definitions `d` in `Γ`, with
their jobs `js`: the rounds, then the self type in lockstep, with the typed
jobs.  One round
per job suffices, and one more stops. -/
def formSelfF {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) (js : List (Job (s,x))) :
    Fu (Except (List EReason) (Ty (s,x) × List (Done (s,x)))) :=
  Fu.bind (roundsF Γ d.probeSelf (js.length + 1) js []) fun r =>
    match r with
    | .ok done =>
        Fu.ret (match d.fullSelf (Done.known done) with
          | some T => .ok (T, done)
          | none => .error [.mismatch])
    | .error rs => Fu.ret (.error rs)

/-! ## The filled literal

Once the self type is formed, the literal is filled and handed to the object
clause of `synthF` in the real context, with the self at the formed type.  A
field without a written type holds the term the rounds elaborated for it, so
no field is elaborated twice.  A field with a written type is elaborated
against that type here, with the self at the formed type, unless its
right-hand side has no empty slot.  The object clause then checks every field
once more. -/

/-- Definitions filled at the self type `T`: the elaborated definitions and
their agreement with the written slots. -/
structure EFill {s : Sig} (d : PDefs s) (T : Ty s) where
  /-- The filled definitions. -/
  ds : ADefs s
  /-- They agree with every written slot of `d`, at `T`. -/
  fills : d.fills T ds = true

/-- The answer of a filling, with the reasons of its failed branches. -/
abbrev EFillR {s : Sig} (d : PDefs s) (T : Ty s) := Option (EFill d T) × List EReason

/-- The first typed job at a label. -/
def lookupDone {s : Sig} : List (Done s) → Label → Option (Done s)
  | [], _ => none
  | e :: es, a => if e.lbl = a then some e else lookupDone es a

theorem PDefs.fills_trm_none {s : Sig} {a : Label} {t : PTm s} {U : Ty s} {b : ATm s}
    (h : t.fills b = true) : (PDefs.trm a none t).fills U (.trm a b) = true := by
  simp [PDefs.fills, h]

theorem PDefs.fills_and' {s : Sig} {d1 d2 : PDefs s} {T : Ty s} {e1 e2 : ADefs s}
    (h1 : d1.fills (andLeft T) e1 = true) (h2 : d2.fills (andRight T) e2 = true) :
    (PDefs.and d1 d2).fills T (.and e1 e2) = true := by
  simp [PDefs.fills, h1, h2]

/-- A literal without a self type: the self type formed by `form`, the
definitions filled at it by `fill`, then the filled literal typed by
`synthF`.  The reasons of the rounds or of the filling reject it. -/
def objNoneF {s : Sig} (Γ : Ctx s) (d : PDefs (s,x))
    (form : Fu (Except (List EReason) (Ty (s,x) × List (Done (s,x)))))
    (fill : (T : Ty (s,x)) → List (Done (s,x)) → Fu (EFillR d T)) :
    Fu (ESynth Γ (.obj none d)) :=
  Fu.bind form fun r =>
    match r with
    | .ok (T, done) =>
        Fu.bind (fill T done) fun r' =>
          match r'.1 with
          | some e => fullSynthAt Γ (.obj none d) (.obj T e.ds) (PTm.fills_obj rfl e.fills)
          | none => Fu.ret ([], r'.2)
    | .error rs => Fu.ret ([], rs)

/-! ## `let` -/

/-- The candidates of a bound term.  With no empty slot, `synthF`.  At an
ascription `let y : U = t in y`, `t` checked against `U`.  Otherwise its
synthesis. -/
def boundF {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (syn : Fu (ESynth Γ t)) (chk : (G : Ty s) → Fu (ECheck Γ t G)) : Fu (ESynth Γ t) :=
  match ht : t.full? with
  | some a => fullSynthAt Γ t a (PTm.fills_of_full? ht)
  | none =>
      match ann, u with
      | some U, .path (.var .here) =>
          Fu.bind (chk U) fun r => Fu.ret (listO (r.1.map fun e => ⟨e.a, U, e.deriv, e.fills⟩), r.2)
      | _, _ => syn

/-- A `let` with the written type `U`: the body checked against `U` under the
binder, for the first candidate of the bound term that allows it. -/
def letAnnR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (U : Ty s)
    (r1 : ESynth Γ t) (chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u U.weaken)) :
    Fu (ESynth Γ (.let g (some U) t u)) :=
  Fu.bind (firstSomeR (fun (c1 : ECand Γ t) => Fu.bind (chk c1) fun r =>
      Fu.ret (r.1.map (fun (e : EChk (Γ.cons c1.ty) u U.weaken) => (⟨.let (some U) c1.a e.a, U,
        (HasTy.let c1.deriv e.deriv : HasTy Γ (.let c1.a.erase e.a.erase) U),
        PTm.fills_let c1.fills e.fills⟩ : ECand Γ (.let g (some U) t u))), r.2)) r1.1) fun r =>
    Fu.ret (listO r.1, r1.2 ++ r.2)

/-- A `let` without a type: every candidate of the body under every candidate
of the bound term, its type avoided, as the `let` clause of `synthF`. -/
def letNoneR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (r1 : ESynth Γ t)
    (syn : (c1 : ECand Γ t) → Fu (ESynth (Γ.cons c1.ty) u)) : Fu (ESynth Γ (.let g none t u)) :=
  Fu.bind (flatMapR (fun (c1 : ECand Γ t) => Fu.bind (syn c1) fun r2 =>
      Fu.bind (flatMapR (fun (c2 : ECand (Γ.cons c1.ty) u) => Fu.bind (avoidLet Γ c1.ty c2.ty) fun o =>
          Fu.ret (listO (o.map fun (lt : LetTy Γ c1.ty c2.ty) => (⟨.let none c1.a c2.a, lt.1,
            (HasTy.let c1.deriv (.sub c2.deriv lt.2) : HasTy Γ (.let c1.a.erase c2.a.erase) lt.1),
            PTm.fills_let c1.fills c2.fills⟩ : ECand Γ (.let g none t u))), ([] : List EReason)))
        r2.1) fun r3 => Fu.ret (r3.1, r2.2 ++ r3.2)) r1.1) fun r =>
    Fu.ret (dedupE r.1, r1.2 ++ r.2)

/-- A block checked at `G`: the body checked against `G` under the binder, for
the first candidate of the bound term that allows it. -/
def blockR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (G : Ty s)
    (r1 : ESynth Γ t) (chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u G.weaken)) :
    Fu (ECheck Γ (.let g none t u) G) :=
  Fu.bind (firstSomeR (fun (c1 : ECand Γ t) => Fu.bind (chk c1) fun r =>
      Fu.ret (r.1.map (fun (e : EChk (Γ.cons c1.ty) u G.weaken) => (⟨.let none c1.a e.a,
        (HasTy.let c1.deriv e.deriv : HasTy Γ (.let c1.a.erase e.a.erase) G),
        PTm.fills_let c1.fills e.fills⟩ : EChk Γ (.let g none t u) G)), r.2)) r1.1) fun r =>
    Fu.ret (r.1, r1.2 ++ r.2)

/-- A `let` synthesized, from the candidates of its bound term. -/
def letSynF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (c1s : Fu (ESynth Γ t)) (synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u))
    (chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)) :
    Fu (ESynth Γ (.let g ann t u)) :=
  match ann with
  | some U => Fu.bind c1s fun r1 => letAnnR Γ U r1 (fun c1 => chkU c1.ty U.weaken)
  | none => Fu.bind c1s fun r1 => letNoneR Γ r1 (fun c1 => synU c1.ty)

/-- A `let` checked at `G`, from the candidates of its bound term.  A written
type is the `let`'s type, subsumed to `G`.  A block passes `G` to its body, and
on an unmarked failure is synthesized and subsumed. -/
def letChkGenF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (G : Ty s) (c1s : Fu (ESynth Γ t))
    (synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u))
    (chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)) :
    Fu (ECheck Γ (.let g ann t u) G) :=
  match ann with
  | some U =>
      Fu.bind c1s fun r1 => Fu.bind (letAnnR Γ U r1 (fun c1 => chkU c1.ty U.weaken)) (subsume Γ G)
  | none =>
      Fu.bind c1s fun r1 =>
        orElseW Option.isSome (blockR Γ G r1 (fun c1 => chkU c1.ty G.weaken))
          (fun _ => Fu.bind (letNoneR Γ r1 (fun c1 => synU c1.ty)) (subsume Γ G))

/-- The callee of a call argument: `f` when the `let` is the binding the
resolver inserts at an operand, `let z = t in f z`. -/
def argCallee? {s : Sig} : LetTag → Option (Ty s) → PTm (s,x) → Option (BVar s .var)
  | .arg, none, .app (.there f) .here => some f
  | _, _, _ => none

/-- A call argument synthesized.  `t` is filled at the dominant formal of the
callee `f`, and the filled `let` goes to `synthF`.  With no dominant formal, or
on an unmarked failure, `gen` types it as any `let`. -/
def argSynF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (f : BVar s .var) (b : ATm (s,x)) (hb : u.fills b = true)
    (chkT : (G : Ty s) → Fu (ECheck Γ t G)) (gen : Unit → Fu (ESynth Γ (.let g ann t u))) :
    Fu (ESynth Γ (.let g ann t u)) :=
  Fu.bind (argGoalF Γ f) fun oF =>
    match oF with
    | some F =>
        orElseW (fun r => !r.isEmpty)
          (Fu.bind (chkT F) fun r =>
            match r.1 with
            | some e => fullSynthAt Γ (.let g ann t u) (.let ann e.a b) (PTm.fills_let e.fills hb)
            | none => Fu.ret ([], r.2))
          gen
    | none => gen ()

/-- A call argument checked at `G`, as `argSynF` with `checkOf` on the filled
`let`. -/
def argChkF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (G : Ty s) (f : BVar s .var) (b : ATm (s,x)) (hb : u.fills b = true)
    (chkT : (G : Ty s) → Fu (ECheck Γ t G)) (gen : Unit → Fu (ECheck Γ (.let g ann t u) G)) :
    Fu (ECheck Γ (.let g ann t u) G) :=
  Fu.bind (argGoalF Γ f) fun oF =>
    match oF with
    | some F =>
        orElseW Option.isSome
          (Fu.bind (chkT F) fun r =>
            match r.1 with
            | some e => fullCheckAt Γ (.let g ann t u) (.let ann e.a b) (PTm.fills_let e.fills hb) G
            | none => Fu.ret (none, r.2))
          gen
    | none => gen ()

/-- A `let` synthesized: a call argument, or any other `let`. -/
def letF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (synT : Fu (ESynth Γ t)) (chkT : (G : Ty s) → Fu (ECheck Γ t G))
    (synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u))
    (chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)) :
    Fu (ESynth Γ (.let g ann t u)) :=
  match argCallee? g ann u, hu : u.full? with
  | some f, some b =>
      argSynF Γ g ann t u f b (PTm.fills_of_full? hu) chkT fun _ =>
        letSynF Γ g ann t u (boundF Γ ann t u synT chkT) synU chkU
  | _, _ => letSynF Γ g ann t u (boundF Γ ann t u synT chkT) synU chkU

/-- A `let` checked at `G`: a call argument, or any other `let`. -/
def letChkF {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    (G : Ty s) (synT : Fu (ESynth Γ t)) (chkT : (G : Ty s) → Fu (ECheck Γ t G))
    (synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u))
    (chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)) :
    Fu (ECheck Γ (.let g ann t u) G) :=
  match argCallee? g ann u, hu : u.full? with
  | some f, some b =>
      argChkF Γ g ann t u G f b (PTm.fills_of_full? hu) chkT fun _ =>
        letChkGenF Γ g ann t u G (boundF Γ ann t u synT chkT) synU chkU
  | _, _ => letChkGenF Γ g ann t u G (boundF Γ ann t u synT chkT) synU chkU

/-! ## The elaborator -/

mutual

/-- Synthesis.  A term with no empty slot goes to `synthF`.  A lambda without
a domain has no goal here.  It takes its domain from the callee of a body
`g x`, and is the compiler's missing parameter type otherwise. -/
def elabF {s : Sig} (Γ : Ctx s) (p : PTm s) : Fu (ESynth Γ p) :=
  match hp : p.full? with
  | some a => fullSynthAt Γ p a (PTm.fills_of_full? hp)
  | none =>
      match p with
      | .lam (some S) t =>
          Fu.bind (elabF (Γ.cons S) t) fun r => Fu.ret (lamCands S (optAgree_some S) r)
      | .lam none t => lamCalleeSynF Γ t
      | .obj (some T) d => objSelfF Γ T (optAgree_some T) (elabDefsF (Γ.cons (.mu T)) d T)
      | .obj none d =>
          objNoneF Γ d (formSelfF Γ d (jobsF d)) fun T done => fillDefsF (Γ.cons (.mu T)) done d T
      | .let g ann t u =>
          letF Γ g ann t u (elabF Γ t) (fun G => elabChkF Γ t G)
            (fun T0 => elabF (Γ.cons T0) u) (fun T0 G => elabChkF (Γ.cons T0) u G)
      | .path _ => Fu.ret ([], [.mismatch])
      | .app _ _ => Fu.ret ([], [.mismatch])
      | .proj _ _ => Fu.ret ([], [.mismatch])
termination_by structural p

/-- Checking against a goal.  A term with no empty slot goes to `checkOf`.  A
lambda without a domain takes it from the goal's function part, or from the
callee of a body `g x` when the goal has none. -/
def elabChkF {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s) : Fu (ECheck Γ p G) :=
  match hp : p.full? with
  | some a => fullCheckAt Γ p a (PTm.fills_of_full? hp) G
  | none =>
      match p with
      | .lam none t =>
          lamNoneChkF Γ t G (fun S V => elabChkF (Γ.cons S) t V) (fun S => elabF (Γ.cons S) t)
      | .lam (some S) t =>
          Fu.bind (funPartAt Γ G) fun fp =>
            match fp with
            | .one _ V =>
                lamGoalF Γ S V G (optAgree_some S) (elabChkF (Γ.cons S) t V)
                  (fun _ => elabF (Γ.cons S) t)
            | _ => Fu.bind (elabF (Γ.cons S) t) fun r => subsume Γ G (lamCands S (optAgree_some S) r)
      | .obj (some T) d =>
          Fu.bind (objSelfF Γ T (optAgree_some T) (elabDefsF (Γ.cons (.mu T)) d T)) (subsume Γ G)
      | .obj none d =>
          Fu.bind (selfGoalF Γ G) fun oT =>
            match oT with
            | some T =>
                orElseW Option.isSome
                  (Fu.bind (objSelfF Γ T rfl (elabDefsF (Γ.cons (.mu T)) d T)) (subsume Γ G))
                  (fun _ => Fu.bind (objNoneF Γ d (formSelfF Γ d (jobsF d))
                    fun T' done => fillDefsF (Γ.cons (.mu T')) done d T') (subsume Γ G))
            | none =>
                Fu.bind (objNoneF Γ d (formSelfF Γ d (jobsF d))
                  fun T done => fillDefsF (Γ.cons (.mu T)) done d T) (subsume Γ G)
      | .let g ann t u =>
          letChkF Γ g ann t u G (elabF Γ t) (fun G' => elabChkF Γ t G')
            (fun T0 => elabF (Γ.cons T0) u) (fun T0 G' => elabChkF (Γ.cons T0) u G')
      | .path _ => Fu.ret (none, [.mismatch])
      | .app _ _ => Fu.ret (none, [.mismatch])
      | .proj _ _ => Fu.ret (none, [.mismatch])
termination_by structural p

/-- Definitions against a self type in lockstep.  A field is checked against
its declaration, so its lambdas take their domains from it.  A written field
type must be the declaration's type. -/
def elabDefsF {s : Sig} (Γ : Ctx s) (d : PDefs s) (T : Ty s) : Fu (EDefsR Γ d T) :=
  match d, T with
  | .typ A S, .typ B L U =>
      Fu.ret (if hA : A = B then
        if hL : S = L then
          if hU : S = U then (some ⟨.typ A S, defsTypAt hA hL hU, PDefs.fills_typ A S _⟩, [])
          else (none, [.mismatch])
        else (none, [.mismatch])
      else (none, [.mismatch]))
  | .trm a o t, .fld c U =>
      if h : a = c then
        if ho : optAgree o U = true then
          Fu.bind (elabChkF Γ t U) fun r =>
            Fu.ret (r.1.map fun e => ⟨.trm a e.a, defsTrmAt h e.deriv, PDefs.fills_trm ho e.fills⟩, r.2)
        else Fu.ret (none, [.mismatch])
      else Fu.ret (none, [.mismatch])
  | .and d1 d2, .and T1 T2 =>
      Fu.bind (elabDefsF Γ d1 T1) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (elabDefsF Γ d2 T2) fun r2 =>
              Fu.ret (r2.1.map fun (e2 : EDefs Γ d2 T2) =>
                ⟨.and e1.ds e2.ds, .and e1.deriv e2.deriv, PDefs.fills_and e1.fills e2.fills⟩, r2.2)
        | none => Fu.ret (none, r1.2)
  | _, _ => Fu.ret (none, [.mismatch])
termination_by structural d

/-- The jobs of a definition list: every field without a written type, in
source order, with its synthesis by `elabF`. -/
def jobsF {s : Sig} : PDefs s → List (Job s)
  | .typ _ _ => []
  | .trm _ (some _) _ => []
  | .trm a none t => [⟨a, t, fun Γ => elabF Γ t⟩]
  | .and d1 d2 => jobsF d1 ++ jobsF d2
termination_by structural d => d

/-- The definitions of a literal filled at its formed self type `T`.  A field
without a written type holds the first typed job at its label, a field with a
written type its right-hand side elaborated against that type, and a type
member stays as it is. -/
def fillDefsF {s : Sig} (Γ : Ctx s) (done : List (Done s)) (d : PDefs s) (T : Ty s) :
    Fu (EFillR d T) :=
  match d with
  | .typ A S => Fu.ret (some ⟨.typ A S, PDefs.fills_typ A S T⟩, [])
  | .trm a none t =>
      match lookupDone done a with
      | some e =>
          if h : t.fills e.a = true then Fu.ret (some ⟨.trm a e.a, PDefs.fills_trm_none h⟩, [])
          else Fu.ret (none, [.mismatch])
      | none => Fu.ret (none, [.mismatch])
  | .trm a (some V) t =>
      match T with
      | .fld c W =>
          if hV : optAgree (some V) W = true then
            match ht : t.full? with
            | some b =>
                Fu.ret (some ⟨.trm a b, PDefs.fills_trm (c := c) hV (PTm.fills_of_full? ht)⟩, [])
            | none =>
                Fu.bind (elabChkF Γ t W) fun r =>
                  Fu.ret (r.1.map fun e => ⟨.trm a e.a, PDefs.fills_trm (c := c) hV e.fills⟩, r.2)
          else Fu.ret (none, [.mismatch])
      | _ => Fu.ret (none, [.mismatch])
  | .and d1 d2 =>
      Fu.bind (fillDefsF Γ done d1 (andLeft T)) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (fillDefsF Γ done d2 (andRight T)) fun r2 =>
              Fu.ret (r2.1.map fun (e2 : EFill d2 (andRight T)) =>
                ⟨.and e1.ds e2.ds, PDefs.fills_and' e1.fills e2.fills⟩, r2.2)
        | none => Fu.ret (none, r1.2)
termination_by structural d

end

/-! ## The entry point -/

/-- The first candidate of a closed partial term, from a full tank of `n`
units, or the reason it is rejected, with the tank left. -/
def elabTopF (n : Nat) (p : PTm []) : Except EReason (ECand Ctx.nil p) × Tank :=
  match elabF Ctx.nil p ⟨n, false⟩ with
  | ((c :: _, _), t) => (if t.out then .error .limit else .ok c, t)
  | (([], rs), t) => (.error (Reason.top t.out rs), t)

/-! ## Every slot written

A term with no empty slot is the typer's, candidates, derivations and tank. -/

theorem elabF_toI {s : Sig} (Γ : Ctx s) (a : ATm s) : elabF Γ a.toI = fullSynth Γ a := by
  rw [elabF]
  split
  · rename_i a' h
    rw [ATm.full?_toI, Option.some.injEq] at h
    subst h
    rfl
  · rename_i h
    rw [ATm.full?_toI] at h
    cases h

theorem elabChkF_toI {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Ty s) :
    elabChkF Γ a.toI G = fullCheck Γ a G := by
  rw [elabChkF]
  split
  · rename_i a' h
    rw [ATm.full?_toI, Option.some.injEq] at h
    subst h
    rfl
  · rename_i h
    rw [ATm.full?_toI] at h
    cases h

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

theorem toGoal_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (c : ECand Γ p) :
    Framed (toGoal Γ G c) := by
  unfold toGoal
  split
  · exact ret_framed _
  · exact bind_framed (subF_framed _ _ _) fun _ => ret_framed _

theorem subsume_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) :
    Framed (subsume Γ G r) :=
  bind_framed (firstSomeR_framed (toGoal_framed Γ G) r.1) fun _ => ret_framed _

theorem fullSynthAt_framed {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) :
    Framed (fullSynthAt Γ p a h) :=
  bind_framed (synthF_framed Γ a) fun _ => ret_framed _

theorem fullCheckAt_framed {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true)
    (G : Ty s) : Framed (fullCheckAt Γ p a h G) :=
  bind_framed (checkF_framed Γ a G) fun _ => ret_framed _

/-! ## The frame lemmas of the goal readers

`funPartF` and `dealiasF` at an index agree with themselves at any larger
index, as the lookup does (`look_agree`).  So the forms that start the index
at the fuel left are framed. -/

theorem uppersPart_agree {s : Sig} {rec rec' : Ty s → Fu (FunPart s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ Ts, Agree (uppersPart rec Ts) (uppersPart rec' Ts)
  | [] => ret_agree _
  | T :: Ts => by
    refine bind_agree (hr T) fun f => ?_
    cases f with
    | none => exact uppersPart_agree hr Ts
    | one _ _ => exact ret_agree _
    | bad => exact ret_agree _

theorem meetPart_framed {s : Sig} (Γ : Ctx s) (f1 f2 : FunPart s) : Framed (meetPart Γ f1 f2) := by
  cases f1 <;> cases f2 <;> simp only [meetPart] <;> try exact ret_framed _
  refine bind_framed (subF_framed _ _ _) fun o2 => ?_
  cases o2 with
  | some _ => exact ret_framed _
  | none =>
    refine bind_framed (subF_framed _ _ _) fun o1 => ?_
    cases o1 with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

theorem funPartTy_agree {s : Sig} (Γ : Ctx s) {rec rec' : Ty s → Fu (FunPart s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ G, Agree (funPartTy Γ rec G) (funPartTy Γ rec' G)
  | .all _ _ => ret_agree _
  | .and G1 G2 =>
    bind_agree (funPartTy_agree Γ hr G1) fun _ =>
      bind_agree (funPartTy_agree Γ hr G2) fun _ => Agree.refl (meetPart_framed _ _ _)
  | .sel (.var y) A => by
    refine bind_agree (Agree.refl (declsAt_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact uppersPart_agree hr _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .typ _ _ _ => ret_agree _
  | .fld _ _ => ret_agree _
  | .mu _ => ret_agree _

theorem funPartF_framed {s : Sig} (Γ : Ctx s) : ∀ d G, Framed (funPartF Γ d G)
  | 0, G => (funPartTy_agree Γ (fun _ => Agree.refl (markAs_framed _)) G).left
  | d + 1, G => (funPartTy_agree Γ (fun T => Agree.refl (funPartF_framed Γ d T)) G).left

theorem funPartF_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ G, Agree (funPartF Γ d G) (funPartF Γ d' G)
  | 0, d', _, G => by
    cases d' with
    | zero => exact Agree.refl (funPartF_framed Γ 0 G)
    | succ e => exact funPartTy_agree Γ (fun T => markAs_agree _ (funPartF_framed Γ e T)) G
  | d + 1, d', hd, G => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact funPartTy_agree Γ (fun T => funPartF_agree Γ d e (by omega) T) G

/-- The function part of a goal is framed. -/
theorem funPartAt_framed {s : Sig} (Γ : Ctx s) (G : Ty s) : Framed (funPartAt Γ G) where
  absorbs t ht := (funPartF_framed Γ t.left G).absorbs t ht
  spends t := (funPartF_framed Γ t.left G).spends t
  shift := by
    intro t r t' h ho k
    exact (funPartF_agree Γ t.left (t.left + k) (Nat.le_add_right _ _) G).sim t r t' h ho k

theorem dealiasTy_agree {s : Sig} (Γ : Ctx s) {rec rec' : Ty s → Fu (Ty s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ G, Agree (dealiasTy Γ rec G) (dealiasTy Γ rec' G)
  | .sel (.var y) A => by
    simp only [dealiasTy]
    refine bind_agree (Agree.refl (declsAt_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact ret_agree _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .typ _ _ _ => ret_agree _
  | .fld _ _ => ret_agree _
  | .mu _ => ret_agree _
  | .all _ _ => ret_agree _
  | .and _ _ => ret_agree _

theorem dealiasF_framed {s : Sig} (Γ : Ctx s) : ∀ d G, Framed (dealiasF Γ d G)
  | 0, G => (dealiasTy_agree Γ (fun T => Agree.refl (markAs_framed T)) G).left
  | d + 1, G => (dealiasTy_agree Γ (fun T => Agree.refl (dealiasF_framed Γ d T)) G).left

theorem dealiasF_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ G, Agree (dealiasF Γ d G) (dealiasF Γ d' G)
  | 0, d', _, G => by
    cases d' with
    | zero => exact Agree.refl (dealiasF_framed Γ 0 G)
    | succ e => exact dealiasTy_agree Γ (fun T => markAs_agree T (dealiasF_framed Γ e T)) G
  | d + 1, d', hd, G => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact dealiasTy_agree Γ (fun T => dealiasF_agree Γ d e (by omega) T) G

theorem dealiasAt_framed {s : Sig} (Γ : Ctx s) (G : Ty s) : Framed (dealiasAt Γ G) where
  absorbs t ht := (dealiasF_framed Γ t.left G).absorbs t ht
  spends t := (dealiasF_framed Γ t.left G).spends t
  shift := by
    intro t r t' h ho k
    exact (dealiasF_agree Γ t.left (t.left + k) (Nat.le_add_right _ _) G).sim t r t' h ho k

theorem selfGoalF_framed {s : Sig} (Γ : Ctx s) (G : Ty s) : Framed (selfGoalF Γ G) := by
  refine bind_framed (dealiasAt_framed Γ G) fun G' => ?_
  cases G' <;> exact ret_framed _

theorem formalsF_framed {s : Sig} (Γ : Ctx s) (g : BVar s .var) : Framed (formalsF Γ g) :=
  bind_framed (lookVar_framed _ _ _) fun _ => ret_framed _

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

theorem lamGoalF_framed {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (V : Ty (s,x)) (G : Ty s) (ho : optAgree o S = true) {chk : Fu (ECheck (Γ.cons S) t V)}
    {syn : Unit → Fu (ESynth (Γ.cons S) t)} (hchk : Framed chk) (hsyn : Framed (syn ())) :
    Framed (lamGoalF Γ S V G ho chk syn) := by
  refine orElseW_framed (bind_framed hchk fun r => ?_)
    (bind_framed hsyn fun _ => subsume_framed _ _ _)
  split
  · exact toGoal_framed _ _ _
  · exact ret_framed _

theorem lamOneChkF_framed {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (S : Ty s) (V : Ty (s,x)) (G : Ty s)
    {chk : Fu (ECheck (Γ.cons S) t V)} {syn : Unit → Fu (ESynth (Γ.cons S) t)} (hchk : Framed chk)
    (hsyn : Framed (syn ())) : Framed (lamOneChkF Γ t S V G chk syn) := by
  unfold lamOneChkF
  split
  · exact fullCheckAt_framed _ _ _ _ _
  · exact lamGoalF_framed _ _ _ _ _ hchk hsyn

theorem lamCalleeSynF_framed {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) :
    Framed (lamCalleeSynF Γ t) := by
  unfold lamCalleeSynF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oS => ?_
    split
    · split
      · exact fullSynthAt_framed _ _ _ _
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem lamCalleeChkF_framed {s : Sig} (Γ : Ctx s) (G : Ty s) (t : PTm (s,x)) :
    Framed (lamCalleeChkF Γ G t) := by
  unfold lamCalleeChkF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oS => ?_
    split
    · split
      · exact fullCheckAt_framed _ _ _ _ _
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem lamNoneChkF_framed {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (G : Ty s)
    {chk : (S : Ty s) → (V : Ty (s,x)) → Fu (ECheck (Γ.cons S) t V)}
    {syn : (S : Ty s) → Fu (ESynth (Γ.cons S) t)} (hchk : ∀ S V, Framed (chk S V))
    (hsyn : ∀ S, Framed (syn S)) : Framed (lamNoneChkF Γ t G chk syn) := by
  refine bind_framed (funPartAt_framed _ _) fun fp => ?_
  cases fp with
  | one S V => exact lamOneChkF_framed _ _ _ _ _ (hchk S V) (hsyn S)
  | none => exact lamCalleeChkF_framed _ _ _
  | bad => exact ret_framed _

theorem objSelfF_framed {s : Sig} (Γ : Ctx s) {o : Option (Ty (s,x))} {d : PDefs (s,x)}
    (T : Ty (s,x)) (ho : optAgree o T = true) {defs : Fu (EDefsR (Γ.cons (.mu T)) d T)}
    (hd : Framed defs) : Framed (objSelfF Γ T ho defs) := by
  refine bind_framed hd fun r => ?_
  split
  · exact fullSynthAt_framed _ _ _ _
  · exact ret_framed _

theorem boundF_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (t : PTm s) (u : PTm (s,x))
    {syn : Fu (ESynth Γ t)} {chk : (G : Ty s) → Fu (ECheck Γ t G)} (hsyn : Framed syn)
    (hchk : ∀ G, Framed (chk G)) : Framed (boundF Γ ann t u syn chk) := by
  unfold boundF
  split
  · exact fullSynthAt_framed _ _ _ _
  · split
    · exact bind_framed (hchk _) fun _ => ret_framed _
    · exact hsyn

theorem letAnnR_framed {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (U : Ty s)
    (r1 : ESynth Γ t) {chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u U.weaken)}
    (hchk : ∀ c1, Framed (chk c1)) : Framed (letAnnR (g := g) Γ U r1 chk) :=
  bind_framed (firstSomeR_framed (fun c1 => bind_framed (hchk c1) fun _ => ret_framed _) _)
    fun _ => ret_framed _

theorem letNoneR_framed {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)}
    (r1 : ESynth Γ t) {syn : (c1 : ECand Γ t) → Fu (ESynth (Γ.cons c1.ty) u)}
    (hsyn : ∀ c1, Framed (syn c1)) : Framed (letNoneR (g := g) Γ r1 syn) :=
  bind_framed (flatMapR_framed (fun c1 => bind_framed (hsyn c1) fun _ =>
      bind_framed (flatMapR_framed (fun _ => bind_framed (avoidLet_framed _ _ _) fun _ =>
        ret_framed _) _) fun _ => ret_framed _) _) fun _ => ret_framed _

theorem blockR_framed {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (G : Ty s)
    (r1 : ESynth Γ t) {chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u G.weaken)}
    (hchk : ∀ c1, Framed (chk c1)) : Framed (blockR (g := g) Γ G r1 chk) :=
  bind_framed (firstSomeR_framed (fun c1 => bind_framed (hchk c1) fun _ => ret_framed _) _)
    fun _ => ret_framed _

theorem letSynF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) {c1s : Fu (ESynth Γ t)} {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u)}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)} (hc1s : Framed c1s)
    (hsynU : ∀ T0, Framed (synU T0)) (hchkU : ∀ T0 G, Framed (chkU T0 G)) :
    Framed (letSynF Γ g ann t u c1s synU chkU) := by
  cases ann with
  | some U =>
    simp only [letSynF]
    exact bind_framed hc1s fun r1 => letAnnR_framed Γ U r1 fun _ => hchkU _ _
  | none =>
    simp only [letSynF]
    exact bind_framed hc1s fun r1 => letNoneR_framed Γ r1 fun _ => hsynU _

theorem letChkGenF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (G : Ty s) {c1s : Fu (ESynth Γ t)}
    {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u)}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)} (hc1s : Framed c1s)
    (hsynU : ∀ T0, Framed (synU T0)) (hchkU : ∀ T0 G, Framed (chkU T0 G)) :
    Framed (letChkGenF Γ g ann t u G c1s synU chkU) := by
  cases ann with
  | some U =>
    simp only [letChkGenF]
    exact bind_framed hc1s fun r1 =>
      bind_framed (letAnnR_framed Γ U r1 fun _ => hchkU _ _) fun _ => subsume_framed Γ G _
  | none =>
    simp only [letChkGenF]
    exact bind_framed hc1s fun r1 =>
      orElseW_framed (blockR_framed Γ G r1 fun _ => hchkU _ _)
        (bind_framed (letNoneR_framed Γ r1 fun _ => hsynU _) fun _ => subsume_framed Γ G _)

theorem argSynF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (f : BVar s .var) (b : ATm (s,x)) (hb : u.fills b = true)
    {chkT : (G : Ty s) → Fu (ECheck Γ t G)} {gen : Unit → Fu (ESynth Γ (.let g ann t u))}
    (hchkT : ∀ G, Framed (chkT G)) (hgen : Framed (gen ())) :
    Framed (argSynF Γ g ann t u f b hb chkT gen) := by
  refine bind_framed (argGoalF_framed Γ f) fun oF => ?_
  cases oF with
  | some F =>
    refine orElseW_framed (bind_framed (hchkT F) fun r => ?_) hgen
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact ret_framed _
  | none => exact hgen

theorem argChkF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (G : Ty s) (f : BVar s .var) (b : ATm (s,x)) (hb : u.fills b = true)
    {chkT : (G : Ty s) → Fu (ECheck Γ t G)} {gen : Unit → Fu (ECheck Γ (.let g ann t u) G)}
    (hchkT : ∀ G, Framed (chkT G)) (hgen : Framed (gen ())) :
    Framed (argChkF Γ g ann t u G f b hb chkT gen) := by
  refine bind_framed (argGoalF_framed Γ f) fun oF => ?_
  cases oF with
  | some F =>
    refine orElseW_framed (bind_framed (hchkT F) fun r => ?_) hgen
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact ret_framed _
  | none => exact hgen

theorem letF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) {synT : Fu (ESynth Γ t)} {chkT : (G : Ty s) → Fu (ECheck Γ t G)}
    {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u)}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)}
    (hsynT : Framed synT) (hchkT : ∀ G, Framed (chkT G)) (hsynU : ∀ T0, Framed (synU T0))
    (hchkU : ∀ T0 G, Framed (chkU T0 G)) : Framed (letF Γ g ann t u synT chkT synU chkU) := by
  unfold letF
  split
  · exact argSynF_framed _ _ _ _ _ _ _ _ hchkT
      (letSynF_framed _ _ _ _ _ (boundF_framed _ _ _ _ hsynT hchkT) hsynU hchkU)
  · exact letSynF_framed _ _ _ _ _ (boundF_framed _ _ _ _ hsynT hchkT) hsynU hchkU

theorem letChkF_framed {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (G : Ty s) {synT : Fu (ESynth Γ t)} {chkT : (G : Ty s) → Fu (ECheck Γ t G)}
    {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u)}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)}
    (hsynT : Framed synT) (hchkT : ∀ G, Framed (chkT G)) (hsynU : ∀ T0, Framed (synU T0))
    (hchkU : ∀ T0 G, Framed (chkU T0 G)) : Framed (letChkF Γ g ann t u G synT chkT synU chkU) := by
  unfold letChkF
  split
  · exact argChkF_framed _ _ _ _ _ _ _ _ _ hchkT
      (letChkGenF_framed _ _ _ _ _ _ (boundF_framed _ _ _ _ hsynT hchkT) hsynU hchkU)
  · exact letChkGenF_framed _ _ _ _ _ _ (boundF_framed _ _ _ _ hsynT hchkT) hsynU hchkU

/-! ## The frame lemmas of the rounds

The rounds keep a marked tank, never add fuel, and do the same with more fuel,
when every job's synthesis does. -/

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

theorem leastFromF_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (Ts : List (Ty s)) :
    ∀ cs : List (ECand Γ p), Framed (leastFromF Γ Ts cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed Γ c.ty Ts) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromF_framed Γ Ts rest

theorem leastCandF_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (cs : List (ECand Γ p)) :
    Framed (leastCandF Γ cs) :=
  leastFromF_framed Γ _ cs

theorem runJobF_framed {s : Sig} (Γ : Ctx s) (P : Ty (s,x)) {j : Job (s,x)}
    (hj : ∀ Γ', Framed (j.run Γ')) : Framed (runJobF Γ P j) := by
  refine bind_framed (hj _) fun r => ?_
  split
  · exact ret_framed _
  · refine bind_framed (leastCandF_framed _ _) fun o => ?_
    cases o with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

theorem roundF_framed {s : Sig} (Γ : Ctx s) (P : Ty (s,x)) :
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

/-- The rounds are framed when every job's synthesis is. -/
theorem roundsF_framed {s : Sig} (Γ : Ctx s) (probe : List (Label × Ty (s,x)) → Ty (s,x)) :
    ∀ (n : Nat) (js : List (Job (s,x))) (known : List (Done (s,x))),
      (∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) → Framed (roundsF Γ probe n js known)
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
    · refine bind_framed (roundF_framed Γ _ _ fun j' h' => hj j' (List.mem_filter.mp h').1)
        fun r => ?_
      cases r with
      | ok new =>
        exact roundsF_framed Γ probe n _ _ fun j' h' => hj j' (List.mem_filter.mp h').1
      | error _ => exact ret_framed _

theorem formSelfF_framed {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) {js : List (Job (s,x))}
    (hj : ∀ j ∈ js, ∀ Γ', Framed (j.run Γ')) : Framed (formSelfF Γ d js) := by
  refine bind_framed (roundsF_framed Γ _ _ js [] hj) fun r => ?_
  cases r with
  | ok _ => exact ret_framed _
  | error _ => exact ret_framed _

theorem objNoneF_framed {s : Sig} (Γ : Ctx s) (d : PDefs (s,x))
    {form : Fu (Except (List EReason) (Ty (s,x) × List (Done (s,x))))}
    {fill : (T : Ty (s,x)) → List (Done (s,x)) → Fu (EFillR d T)}
    (hf : Framed form) (hl : ∀ T done, Framed (fill T done)) : Framed (objNoneF Γ d form fill) := by
  refine bind_framed hf fun r => ?_
  cases r with
  | ok p =>
    obtain ⟨T, done⟩ := p
    refine bind_framed (hl T done) fun r' => ?_
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact ret_framed _
  | error _ => exact ret_framed _

/-! ## The frame lemmas of the elaborator

By induction on the term, from the frame lemmas of the clauses. -/

mutual

/-- Synthesis is framed. -/
theorem elabF_framed {s : Sig} (Γ : Ctx s) : (p : PTm s) → Framed (elabF Γ p)
  | .path q => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact ret_framed _
  | .app x y => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact ret_framed _
  | .proj x a => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact ret_framed _
  | .lam (some S) t => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact bind_framed (elabF_framed _ t) fun _ => ret_framed _
  | .lam none t => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact lamCalleeSynF_framed _ t
  | .obj (some T) d => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact objSelfF_framed _ _ _ (elabDefsF_framed _ d T)
  | .obj none d => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed d))
        fun T done => fillDefsF_framed _ done d T
  | .let g ann t u => by
    rw [elabF]
    split
    · exact fullSynthAt_framed _ _ _ _
    · exact letF_framed _ _ _ _ _ (elabF_framed _ t) (fun G => elabChkF_framed _ t G)
        (fun T0 => elabF_framed _ u) (fun T0 G => elabChkF_framed _ u G)

/-- Checking is framed. -/
theorem elabChkF_framed {s : Sig} (Γ : Ctx s) : (p : PTm s) → (G : Ty s) → Framed (elabChkF Γ p G)
  | .path q, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact ret_framed _
  | .app x y, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact ret_framed _
  | .proj x a, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact ret_framed _
  | .lam none t, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact lamNoneChkF_framed _ _ _ (fun _ V => elabChkF_framed _ t V) (fun _ => elabF_framed _ t)
  | .lam (some S) t, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · refine bind_framed (funPartAt_framed _ _) fun fp => ?_
      split
      · exact lamGoalF_framed _ _ _ _ _ (elabChkF_framed _ t _) (elabF_framed _ t)
      · exact bind_framed (elabF_framed _ t) fun _ => subsume_framed _ _ _
  | .obj (some T) d, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact bind_framed (objSelfF_framed _ _ _ (elabDefsF_framed _ d T)) fun _ => subsume_framed _ _ _
  | .obj none d, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · refine bind_framed (selfGoalF_framed _ _) fun oT => ?_
      split
      · exact orElseW_framed
          (bind_framed (objSelfF_framed _ _ _ (elabDefsF_framed _ d _)) fun _ => subsume_framed _ _ _)
          (bind_framed (objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed d))
            fun T' done => fillDefsF_framed _ done d T') fun _ => subsume_framed _ _ _)
      · exact bind_framed (objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed d))
          fun T done => fillDefsF_framed _ done d T) fun _ => subsume_framed _ _ _
  | .let g ann t u, G => by
    rw [elabChkF]
    split
    · exact fullCheckAt_framed _ _ _ _ _
    · exact letChkF_framed _ _ _ _ _ _ (elabF_framed _ t) (fun G => elabChkF_framed _ t G)
        (fun T0 => elabF_framed _ u) (fun T0 G => elabChkF_framed _ u G)

/-- Checking definitions is framed. -/
theorem elabDefsF_framed {s : Sig} (Γ : Ctx s) : (d : PDefs s) → (T : Ty s) →
    Framed (elabDefsF Γ d T)
  | .typ A S, T => by
    cases T with
    | typ B L U => rw [elabDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | .trm a o t, T => by
    cases T with
    | fld c U =>
      rw [elabDefsF]
      split
      · split
        · exact bind_framed (elabChkF_framed _ t U) fun _ => ret_framed _
        · exact ret_framed _
      · exact ret_framed _
    | _ => exact ret_framed _
  | .and d1 d2, T => by
    cases T with
    | and T1 T2 =>
      rw [elabDefsF]
      refine bind_framed (elabDefsF_framed _ d1 T1) fun r1 => ?_
      split
      · exact bind_framed (elabDefsF_framed _ d2 T2) fun _ => ret_framed _
      · exact ret_framed _
    | _ => exact ret_framed _

/-- The jobs of a definition list run framed syntheses. -/
theorem jobsF_framed {s : Sig} : (d : PDefs s) → ∀ j ∈ jobsF d, ∀ Γ, Framed (j.run Γ)
  | .typ _ _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm _ (some _) _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm a none t => by
    intro j hj Γ
    simp only [jobsF, List.mem_singleton] at hj
    subst hj
    exact elabF_framed Γ t
  | .and d1 d2 => by
    intro j hj Γ
    simp only [jobsF, List.mem_append] at hj
    rcases hj with h | h
    · exact jobsF_framed d1 j h Γ
    · exact jobsF_framed d2 j h Γ

/-- Filling definitions is framed. -/
theorem fillDefsF_framed {s : Sig} (Γ : Ctx s) (done : List (Done s)) :
    (d : PDefs s) → (T : Ty s) → Framed (fillDefsF Γ done d T)
  | .typ A S, T => by
    rw [fillDefsF]
    exact ret_framed _
  | .trm a none t, T => by
    rw [fillDefsF]
    split
    · split
      · exact ret_framed _
      · exact ret_framed _
    · exact ret_framed _
  | .trm a (some V) t, T => by
    cases T with
    | fld c W =>
      rw [fillDefsF]
      split
      · split
        · exact ret_framed _
        · exact bind_framed (elabChkF_framed _ t _) fun _ => ret_framed _
      · exact ret_framed _
    | _ =>
      rw [fillDefsF]
      · exact ret_framed _
      · intro _ _ h
        cases h
  | .and d1 d2, T => by
    rw [fillDefsF]
    refine bind_framed (fillDefsF_framed Γ done d1 _) fun r1 => ?_
    split
    · exact bind_framed (fillDefsF_framed Γ done d2 _) fun _ => ret_framed _
    · exact ret_framed _

end

/-! ## What a filled slot is

`Yields P c` says that every answer of `c`, from any tank, satisfies `P`.  The
combinators keep it, so a filled domain can be read off the clause that fills
it. -/

/-- Every answer of `c`, from any tank, satisfies `P`. -/
def Yields {α ρ : Type} (P : α → Prop) (c : Fu (Option α × List ρ)) : Prop :=
  ∀ t x, (c t).1.1 = some x → P x

section YieldsLemmas

variable {α β ρ : Type} {P : α → Prop}

theorem yields_ret_none (rs : List ρ) : Yields P (Fu.ret ((none : Option α), rs)) := by
  intro t x h
  simp [Fu.ret] at h

theorem yields_bind {c : Fu β} {f : β → Fu (Option α × List ρ)} (hf : ∀ b, Yields P (f b)) :
    Yields P (Fu.bind c f) := by
  intro t x h
  cases hc : c t with
  | mk b t1 =>
    simp only [Fu.bind, hc] at h
    exact hf b t1 x h

/-- Keeping the answer and changing the reasons keeps `Yields`. -/
theorem yields_reasons {c : Fu (Option α × List ρ)} (g : Option α × List ρ → List ρ)
    (hc : Yields P c) : Yields P (Fu.bind c fun r => Fu.ret (r.1, g r)) := by
  intro t x h
  cases hct : c t with
  | mk r t1 =>
    simp only [Fu.bind, Fu.ret, hct] at h
    exact hc t x (by rw [hct]; exact h)

theorem yields_orElseW {a : Fu (Option α × List ρ)} {b : Unit → Fu (Option α × List ρ)}
    (ha : Yields P a) (hb : Yields P (b ())) : Yields P (orElseW Option.isSome a b) := by
  intro t x h
  cases hat : a t with
  | mk r t1 =>
    simp only [orElseW, Fu.bind, hat, stopOr] at h
    split at h
    · exact ha t x (by rw [hat]; exact h)
    · cases hbt : b () t1 with
      | mk r' t2 =>
        simp only [hbt, Fu.ret] at h
        exact hb t1 x (by rw [hbt]; exact h)

theorem yields_firstSomeR {f : β → Fu (Option α × List ρ)} :
    ∀ (l : List β), (∀ y ∈ l, Yields P (f y)) → Yields P (firstSomeR f l)
  | [], _ => yields_ret_none _
  | y :: ys, hl =>
    yields_orElseW (hl y (List.mem_cons_self ..))
      (yields_firstSomeR ys fun y' hy' => hl y' (List.mem_cons_of_mem _ hy'))

end YieldsLemmas

theorem yields_toGoal {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (c : ECand Γ p)
    {Q : ATm s → Prop} (hq : Q c.a) : Yields (fun e : EChk Γ p G => Q e.a) (toGoal Γ G c) := by
  unfold toGoal
  split
  · intro t x h
    simp only [Fu.ret, Option.some.injEq] at h
    subst h
    exact hq
  · refine yields_bind fun o => ?_
    intro t x h
    simp only [Fu.ret, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact hq

theorem yields_subsume {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p)
    {Q : ATm s → Prop} (hq : ∀ c ∈ r.1, Q c.a) : Yields (fun e : EChk Γ p G => Q e.a) (subsume Γ G r) :=
  yields_reasons _ (yields_firstSomeR _ fun c hc => yields_toGoal Γ G c (hq c hc))

theorem yields_fullCheckAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true)
    (G : Ty s) : Yields (fun e : EChk Γ p G => e.a = a) (fullCheckAt Γ p a h G) := by
  refine yields_bind fun o => ?_
  intro t x hx
  simp only [Fu.ret, Option.map_eq_some_iff] at hx
  obtain ⟨_, _, rfl⟩ := hx
  rfl

/-- Every answer of `lamGoalF` is a lambda with the domain it was given. -/
theorem yields_lamGoalF {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (V : Ty (s,x)) (G : Ty s) (ho : optAgree o S = true) (chk : Fu (ECheck (Γ.cons S) t V))
    (syn : Unit → Fu (ESynth (Γ.cons S) t)) :
    Yields (fun e : EChk Γ (.lam o t) G => ∃ b, e.a = .lam S b) (lamGoalF Γ S V G ho chk syn) := by
  refine yields_orElseW (yields_bind fun r => ?_) (yields_bind fun r => ?_)
  · split
    · exact yields_toGoal (Q := fun a => ∃ b, a = .lam S b) _ _ _ ⟨_, rfl⟩
    · exact yields_ret_none _
  · refine yields_subsume (Q := fun a => ∃ b, a = .lam S b) _ _ _ fun c hc => ?_
    simp only [lamCands, List.mem_map] at hc
    obtain ⟨c', _, rfl⟩ := hc
    exact ⟨_, rfl⟩

/-- The check of a lambda without a domain, unfolded. -/
theorem elabChkF_lam_none {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (G : Ty s) :
    elabChkF Γ (.lam none t) G =
      lamNoneChkF Γ t G (fun S V => elabChkF (Γ.cons S) t V) (fun S => elabF (Γ.cons S) t) := by
  rw [elabChkF]
  split
  · rename_i hp
    simp [PTm.full?] at hp
  · rfl

theorem yields_lamOneChkF {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) (S : Ty s) (V : Ty (s,x))
    (G : Ty s) (chk : Fu (ECheck (Γ.cons S) t V)) (syn : Unit → Fu (ESynth (Γ.cons S) t)) :
    Yields (fun e : EChk Γ (.lam none t) G => ∃ b, e.a = .lam S b) (lamOneChkF Γ t S V G chk syn) := by
  unfold lamOneChkF
  split
  · intro tk e h
    exact ⟨_, yields_fullCheckAt _ _ _ _ _ tk e h⟩
  · exact yields_lamGoalF _ _ _ _ _ _ _

/-- Every candidate of `fullSynthAt` is the filled term it was given. -/
theorem fullSynthAt_a {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} {h : p.fills a = true}
    {tk : Tank} {c : ECand Γ p} (hc : c ∈ (fullSynthAt Γ p a h tk).1.1) : c.a = a := by
  unfold fullSynthAt at hc
  cases hs : synthF Γ a tk with
  | mk cs t1 =>
    simp only [Fu.bind, Fu.ret, hs, List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    rfl

/-- A body with a callee is `g x`. -/
theorem calleeOf?_eq {s : Sig} {t : PTm (s,x)} {g : BVar s .var} (hg : calleeOf? t = some g) :
    t = .app (.there g) .here := by
  cases t with
  | app f y =>
    simp only [calleeOf?] at hg
    split at hg
    · rename_i hy
      subst hy
      cases f with
      | here => cases hg
      | there f' =>
        cases hg
        rfl
    · cases hg
  | _ => simp [calleeOf?] at hg

/-- The callee of the body `g x` is `g`. -/
theorem calleeOf?_app {s : Sig} (g : BVar s .var) : calleeOf? (.app (.there g) .here) = some g := rfl

/-- An answer of `lamCalleeChkF` is the body `g x` filled with the dominant
formal of `g`, read on the tank the check starts from. -/
theorem lamCalleeChkF_formal {s : Sig} {Γ : Ctx s} {G : Ty s} {t : PTm (s,x)} {tk : Tank}
    {e : EChk Γ (.lam none t) G} (h : (lamCalleeChkF Γ G t tk).1.1 = some e) :
    ∃ g S tk', t = .app (.there g) .here ∧ argGoalF Γ g tk = (some S, tk') ∧
      e.a = .lam S (.app (.there g) .here) := by
  unfold lamCalleeChkF at h
  cases hc : calleeOf? t with
  | none => simp [hc, Fu.ret] at h
  | some g =>
    simp only [hc] at h
    obtain rfl := calleeOf?_eq hc
    cases ha : argGoalF Γ g tk with
    | mk oS t1 =>
      simp only [Fu.bind, ha] at h
      cases oS with
      | some S =>
        exact ⟨g, S, t1, rfl, ha,
          yields_fullCheckAt Γ _ (.lam S (.app (.there g) .here)) _ G t1 e h⟩
      | none => simp [Fu.ret] at h

/-- A candidate of `lamCalleeSynF` is the body `g x` filled with the dominant
formal of `g`, read on the tank the synthesis starts from. -/
theorem lamCalleeSynF_formal {s : Sig} {Γ : Ctx s} {t : PTm (s,x)} {tk : Tank}
    {c : ECand Γ (.lam none t)} (h : c ∈ (lamCalleeSynF Γ t tk).1.1) :
    ∃ g S tk', t = .app (.there g) .here ∧ argGoalF Γ g tk = (some S, tk') ∧
      c.a = .lam S (.app (.there g) .here) := by
  unfold lamCalleeSynF at h
  cases hc : calleeOf? t with
  | none => simp [hc, Fu.ret] at h
  | some g =>
    simp only [hc] at h
    obtain rfl := calleeOf?_eq hc
    cases ha : argGoalF Γ g tk with
    | mk oS t1 =>
      simp only [Fu.bind, ha] at h
      cases oS with
      | some S =>
        exact ⟨g, S, t1, rfl, ha,
          fullSynthAt_a (a := .lam S (.app (.there g) .here)) (tk := t1) h⟩
      | none => simp [Fu.ret] at h

/-- A filled domain is the domain of the goal's function part, read on the tank
the check starts from.  At a goal with no function part it is the dominant
formal of the callee `g` of the body `g x`, read on the tank the function part
left. -/
theorem elabChkF_lam_formal {s : Sig} {Γ : Ctx s} {t : PTm (s,x)} {G : Ty s} {tk : Tank}
    {e : EChk Γ (.lam none t) G} (h : (elabChkF Γ (.lam none t) G tk).1.1 = some e) :
    (∃ S V b tk', funPartF Γ tk.left G tk = (.one S V, tk') ∧ e.a = .lam S b) ∨
    (∃ g S tk' tk'', funPartF Γ tk.left G tk = (.none, tk') ∧ t = .app (.there g) .here ∧
      argGoalF Γ g tk' = (some S, tk'') ∧ e.a = .lam S (.app (.there g) .here)) := by
  rw [elabChkF_lam_none] at h
  unfold lamNoneChkF at h
  cases hf : funPartAt Γ G tk with
  | mk fp t1 =>
    have hf' : funPartF Γ tk.left G tk = (fp, t1) := hf
    simp only [Fu.bind, hf] at h
    cases fp with
    | one S V =>
      obtain ⟨b, hb⟩ := yields_lamOneChkF _ _ _ _ _ _ _ t1 e h
      exact .inl ⟨S, V, b, t1, hf', hb⟩
    | none =>
      obtain ⟨g, S, t2, ht, ha, he⟩ := lamCalleeChkF_formal h
      exact .inr ⟨g, S, t1, t2, hf', ht, ha, he⟩
    | bad => simp [Fu.ret] at h

/-- The synthesis of a lambda without a domain, unfolded. -/
theorem elabF_lam_none {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) :
    elabF Γ (.lam none t) = lamCalleeSynF Γ t := by
  rw [elabF]
  split
  · rename_i hp
    simp [PTm.full?] at hp
  · rfl

/-- A lambda without a domain synthesizes only with a body `g x`, and its
domain is the dominant formal of `g`, read on the tank the synthesis starts
from. -/
theorem elabF_lam_formal {s : Sig} {Γ : Ctx s} {t : PTm (s,x)} {tk : Tank}
    {c : ECand Γ (.lam none t)} (h : c ∈ (elabF Γ (.lam none t) tk).1.1) :
    ∃ g S tk', t = .app (.there g) .here ∧ argGoalF Γ g tk = (some S, tk') ∧
      c.a = .lam S (.app (.there g) .here) := by
  rw [elabF_lam_none] at h
  exact lamCalleeSynF_formal h

/-- A lambda without a domain and with the body `g x` is the typer's synthesis
of the lambda filled with the dominant formal of `g`, from the tank that
formal's lookup left. -/
theorem lam_callee_full {s : Sig} {Γ : Ctx s} {g : BVar s .var} {tk tk' : Tank} {S : Ty s}
    (h : argGoalF Γ g tk = (some S, tk')) :
    elabF Γ (.lam none (.app (.there g) .here)) tk =
      fullSynthAt Γ (.lam none (.app (.there g) .here)) (.lam S (.app (.there g) .here))
        (PTm.fills_lam rfl (PTm.fills_app _ _)) tk' := by
  rw [elabF_lam_none]
  unfold lamCalleeSynF
  simp only [calleeOf?_app, Fu.bind, h]
  rfl

/-- The same at a goal with no function part: the typer's check of the filled
lambda at the goal. -/
theorem lam_callee_chk_full {s : Sig} {Γ : Ctx s} {g : BVar s .var} {G : Ty s}
    {tk tk' tk'' : Tank} {S : Ty s} (hf : funPartF Γ tk.left G tk = (.none, tk'))
    (h : argGoalF Γ g tk' = (some S, tk'')) :
    elabChkF Γ (.lam none (.app (.there g) .here)) G tk =
      fullCheckAt Γ (.lam none (.app (.there g) .here)) (.lam S (.app (.there g) .here))
        (PTm.fills_lam rfl (PTm.fills_app _ _)) G tk'' := by
  rw [elabChkF_lam_none]
  have hf' : funPartAt Γ G tk = (.none, tk') := hf
  simp only [lamNoneChkF, Fu.bind, hf']
  unfold lamCalleeChkF
  simp only [calleeOf?_app, Fu.bind, h]
  rfl

/-- A lambda whose body has no empty slot, at a goal with a function part, is
`checkOf` on the lambda filled with the part's domain. -/
theorem lamOneChkF_toI {s : Sig} (Γ : Ctx s) (a : ATm (s,x)) (S : Ty s) (V : Ty (s,x)) (G : Ty s)
    (chk : Fu (ECheck (Γ.cons S) a.toI V)) (syn : Unit → Fu (ESynth (Γ.cons S) a.toI)) :
    lamOneChkF Γ a.toI S V G chk syn =
      fullCheckAt Γ (.lam none a.toI) (.lam S a) (PTm.fills_lam rfl (ATm.fills_toI a)) G := by
  unfold lamOneChkF
  split
  · rename_i b hb
    rw [ATm.full?_toI, Option.some.injEq] at hb
    subst hb
    rfl
  · rename_i hb
    rw [ATm.full?_toI] at hb
    cases hb

/-- A lambda whose body has no empty slot, checked at a goal with a function
part, is the typer's check of the lambda filled with the part's domain, from
the tank the function part left. -/
theorem lam_fill_full {s : Sig} {Γ : Ctx s} {G : Ty s} {tk tk' : Tank} {S : Ty s} {V : Ty (s,x)}
    (a : ATm (s,x)) (h : funPartF Γ tk.left G tk = (.one S V, tk')) :
    elabChkF Γ (.lam none a.toI) G tk =
      fullCheckAt Γ (.lam none a.toI) (.lam S a) (PTm.fills_lam rfl (ATm.fills_toI a)) G tk' := by
  rw [elabChkF_lam_none]
  have hf : funPartAt Γ G tk = (.one S V, tk') := h
  simp only [lamNoneChkF, Fu.bind, hf]
  rw [lamOneChkF_toI]

/-! ## The goal of a call argument is dominant -/

theorem allBelowF_sub {s : Sig} {Γ : Ctx s} {F : Ty s} :
    ∀ {Fs : List (Ty s)} {t t' : Tank}, allBelowF Γ F Fs t = (true, t') →
      ∀ F' ∈ Fs, Nonempty (Sub Γ F' F)
  | [], _, _, _, F', hF' => absurd hF' List.not_mem_nil
  | F'' :: Fs, t, t', h, F', hF' => by
    unfold allBelowF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hF' with rfl | hm
      · exact ⟨heq ▸ Sub.refl⟩
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

/-! ## Self types formed from definitions -/

/-- The self type formed from the definitions is in lockstep with them. -/
theorem fullSelf_lockstep {s : Sig} {known : List (Label × Ty s)} :
    ∀ {d : PDefs s} {T : Ty s}, d.fullSelf known = some T → Lockstep known d T
  | .typ A S, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .typ A S
  | .trm a (some U) t, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .written a U t
  | .trm a none t, _, h => by
    simp only [PDefs.fullSelf, Option.map_eq_some_iff] at h
    obtain ⟨U, hU, rfl⟩ := h
    exact .inferred a U t hU
  | .and d e, _, h => by
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf known with
    | none => simp only [h1, reduceCtorEq] at h
    | some T1 =>
      cases h2 : e.fullSelf known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some T2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact .and (fullSelf_lockstep h1) (fullSelf_lockstep h2)

/-- A definition list whose fields all have a written type has no job, so a
literal with a written type on every field needs no round. -/
theorem jobsF_written {s : Sig} : ∀ {d : PDefs s}, d.AllFieldsWritten → jobsF d = []
  | .typ _ _, _ => by simp only [jobsF]
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
      · exact ⟨heq ▸ Sub.refl⟩
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

theorem leastFromF_sub {s : Sig} {Γ : Ctx s} {p : PTm s} {Ts : List (Ty s)} :
    ∀ {cs : List (ECand Γ p)} {t : Tank} {c : ECand Γ p} {t' : Tank},
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
theorem leastCand_least {s : Sig} {Γ : Ctx s} {p : PTm s} {cs : List (ECand Γ p)} {tk : Tank}
    {c : ECand Γ p} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) :
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

theorem leastFromF_sub? {s : Sig} {Γ : Ctx s} {p : PTm s} {Ts : List (Ty s)} :
    ∀ {cs : List (ECand Γ p)} {t : Tank} {c : ECand Γ p} {t' : Tank},
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
theorem leastCand_sub? {s : Sig} {Γ : Ctx s} {p : PTm s} {cs : List (ECand Γ p)} {tk : Tank}
    {c : ECand Γ p} {tk' : Tank} (h : leastCandF Γ cs tk = (some c, tk')) (ho : tk'.out = false) :
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

/-! ## A literal without a self type is the typer's literal -/

/-- The synthesis of a literal without a self type, unfolded. -/
theorem elabF_obj_none {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) :
    elabF Γ (.obj none d) =
      objNoneF Γ d (formSelfF Γ d (jobsF d)) fun T done => fillDefsF (Γ.cons (.mu T)) done d T := by
  rw [elabF]
  split
  · rename_i hp
    simp [PTm.full?] at hp
  · rfl

/-- A candidate of a literal without a self type is a candidate of the typer
on the filled literal.  Its self type is the one the rounds formed, from the
tank the synthesis starts with, and the derivation is the one the object
clause of `synthF` gives, `HasTy.obj`. -/
theorem obj_none_landed {s : Sig} {Γ : Ctx s} {d : PDefs (s,x)} {tk : Tank}
    {c : ECand Γ (.obj none d)} {cs : List (ECand Γ (.obj none d))}
    (h : (elabF Γ (.obj none d) tk).1.1 = c :: cs) :
    ∃ T done d' tk', (formSelfF Γ d (jobsF d) tk).1 = .ok (T, done) ∧
      ∃ hc : c.a = .obj T d',
        (⟨c.ty, hc ▸ c.deriv⟩ : Cand Γ (ATm.obj T d').erase) ∈ (synthF Γ (.obj T d') tk').1 := by
  rw [elabF_obj_none] at h
  unfold objNoneF at h
  cases hf : formSelfF Γ d (jobsF d) tk with
  | mk r tk1 =>
    simp only [Fu.bind, hf] at h
    cases r with
    | error rs => simp [Fu.ret] at h
    | ok p =>
      obtain ⟨T, done⟩ := p
      cases hl : fillDefsF (Γ.cons (.mu T)) done d T tk1 with
      | mk r' tk2 =>
        dsimp only [Fu.bind] at h
        rw [hl] at h
        cases r' with
        | mk o rs =>
          cases o with
          | none => simp [Fu.ret] at h
          | some e =>
            dsimp only at h
            unfold fullSynthAt at h
            cases hs : synthF Γ (.obj T e.ds) tk2 with
            | mk l tk3 =>
              simp only [Fu.bind, Fu.ret, hs] at h
              cases l with
              | nil => simp at h
              | cons c0 l' =>
                simp only [List.map_cons, List.cons.injEq] at h
                obtain ⟨rfl, _⟩ := h
                exact ⟨T, done, e.ds, tk2, rfl, rfl, by rw [hs]; exact List.mem_cons_self ..⟩

/-! ## Checks

Each check elaborates a surface program at `defaultFuel` in the kernel.  It
states the elaborated term and its type, or the reason, and the tank left.  A
program with an empty slot that compiles is compared with the program that
writes the slot: the elaborated term is the term that program resolves to, and
the type is the one `synthF` gives it.  An unmarked tank means the fuel played
no part in the verdict. -/

section ElabChecks

/-- The outcome of a closed elaboration: the elaborated term and its type, or
the reason. -/
inductive Outcome where
  /-- The elaborated term and its type. -/
  | ok (a : ATm []) (T : Ty [])
  /-- The reason the program is rejected. -/
  | no (r : EReason)
deriving DecidableEq

/-- The type of an outcome, if it has one. -/
def Outcome.ty? : Outcome → Option (Ty [])
  | .ok _ T => some T
  | .no _ => none

/-- The outcome of a surface program, resolved and elaborated, with the tank
left. -/
def elabAt (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  match resolveP exampleTable e with
  | some p =>
      match elabTopF n p with
      | (.ok c, t) => (.ok c.a c.ty, t)
      | (.error r, t) => (.no r, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- What `synthF` gives a surface program with every slot written: the term it
resolves to and its first type. -/
def writtenAt (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  match resolve exampleTable e with
  | some a =>
      match synthTopF n a with
      | (some c, t) => (.ok a c.ty, t)
      | (none, t) => (.no .mismatch, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- E11 with the identity passed directly, twice, the domains written. -/
def E11asrc : STm :=
  dot% (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) (λ(x : ⊤). x) (λ(x : ⊤). x)

/-- The same with the domains of the two arguments erased. -/
def E11asrcA : STm := dot% (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) (λx. x) (λx. x)

/-- E11 with every domain erased. -/
def E11srcD : STm := dot% let i = λx. x in (λf. λg. f (g f)) i i

/-- A callee at an intersection of two function types whose formals are
comparable, applied to the identity with its domain written. -/
def X1src : STm :=
  dot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λ(x : ⊤). x)

/-- The same with the domain erased.  The dominant formal is `∀(x : ⊤) ⊤`. -/
def X1srcA : STm := dot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λx. x)

/-- A written type with two function sides of one domain. -/
def X2src : STm :=
  dot% let f : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) = λ(x : {a : ⊤}). x in f

/-- The same with the domain erased.  The sides meet at the domain `{a : ⊤}`. -/
def X2srcD : STm := dot% let f : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) = λx. x in f

/-- A written type whose second side is a selection with a function lower
bound.  The written lambda is below it through the lower bound. -/
def X3src : STm :=
  dot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}).
         let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A = λ(x : {a : ⊤}). x in f

/-- The same with the inner domain erased.  The body has no empty slot, so the
lambda filled with `{a : ⊤}` goes to the typer at the written type. -/
def X3srcD : STm :=
  dot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}). let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A = λx. x in f

/-- `let i : ∀(x : ⊤) ⊤ = λ(x : ⊤). x in i`. -/
def IdAscSrc : STm := dot% let i : ∀(x : ⊤) ⊤ = λ(x : ⊤). x in i

/-- The same with the domain erased. -/
def IdAscSrcD : STm := dot% let i : ∀(x : ⊤) ⊤ = λx. x in i

/-- The ascription `(λx. x : ∀(x : ⊤) ⊤)`. -/
def AscSrcD : STm := dot% (λx. x : ∀(x : ⊤) ⊤)

/-- The ascription with the domain written. -/
def AscSrc : STm := dot% (λ(x : ⊤). x : ∀(x : ⊤) ⊤)

/-- One function side and `⊤`. -/
def AndTopSrc : STm := dot% let f : (∀(x : ⊤) ⊤) ∧ ⊤ = λ(y : ⊤). y in f

/-- The same with the domain erased. -/
def AndTopSrcD : STm := dot% let f : (∀(x : ⊤) ⊤) ∧ ⊤ = λy. y in f

/-- Two function sides with comparable domains, the larger one written. -/
def AndTwoSrc : STm := dot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤) = λ(y : ⊤). y in f

/-- The same with the domain erased.  The domain is the larger one, `⊤`. -/
def AndTwoSrcD : STm := dot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤) = λy. y in f

/-- Two function sides with incomparable domains. -/
def AndIncSrcD : STm := dot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤) = λy. y in f

/-- One function side and a field the lambda does not have. -/
def AndOneSrcD : STm := dot% let f : (∀(x : ⊤) ⊤) ∧ {a : ⊤} = λy. y in f

/-- A lambda bound with no type. -/
def Id0SrcD : STm := dot% let i = λx. x in i

/-- A lambda bound at `⊤`. -/
def IdTopSrcD : STm := dot% let i : ⊤ = λx. x in i

/-- An alias of a function type as the written type. -/
def AliasSrc : STm :=
  dot% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). let f : y.A = λ(x : ⊤). x in f

/-- The same with the domain erased.  The alias is followed. -/
def AliasSrcD : STm := dot% λ(y : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}). let f : y.A = λx. x in f

/-- An abstract type with a function upper bound as the written type. -/
def UpperSrcD : STm := dot% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). let f : y.A = λx. x in f

/-- An abstract type with a function lower bound only. -/
def LowerSrcD : STm := dot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). let f : y.A = λx. x in f

/-- A callee whose two formals are incomparable. -/
def IncSrcD : STm :=
  dot% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λx. x)

/-- A callee whose two formals are one type, the domain written. -/
def DomSrc : STm :=
  dot% λ(g : (∀(h : ∀(x : {a : ⊤}) {a : ⊤}) {a : ⊤}) ∧ (∀(h : ∀(x : {a : ⊤}) {a : ⊤}) ⊤)).
         g (λ(x : {a : ⊤}). x)

/-- The same with the domain erased. -/
def DomSrcD : STm :=
  dot% λ(g : (∀(h : ∀(x : {a : ⊤}) {a : ⊤}) {a : ⊤}) ∧ (∀(h : ∀(x : {a : ⊤}) {a : ⊤}) ⊤)). g (λx. x)

/-- A lambda bound by a written `let` and then passed: no call argument. -/
def LetArgSrcD : STm := dot% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λx. x in g i

/-- A literal ascribed at a `μ`, its self type written. -/
def AscObjSrc : STm := dot% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self type erased.  The `μ` goal gives it. -/
def AscObjSrcS : STm := dot% λ(n : {b : ⊤}). (ν(z. {a = n}) : μ(z. {a : {b : ⊤}}))

-- The erased programs are the written ones with those slots erased.
example : (resolveP exampleTable E11src).map PTm.eraseDoms = resolveP exampleTable E11srcD := rfl
example : (resolveP exampleTable E11asrc).map PTm.eraseArgs = resolveP exampleTable E11asrcA := rfl
example : (resolveP exampleTable X1src).map PTm.eraseArgs = resolveP exampleTable X1srcA := rfl
example : (resolveP exampleTable DomSrc).map PTm.eraseArgs = resolveP exampleTable DomSrcD := rfl
example : (resolveP exampleTable X2src).map PTm.eraseDoms = resolveP exampleTable X2srcD := rfl
example : (resolveP exampleTable AndTwoSrc).map PTm.eraseDoms = resolveP exampleTable AndTwoSrcD := rfl
example : (resolveP exampleTable AscObjSrc).map PTm.eraseSelf = resolveP exampleTable AscObjSrcS := rfl

-- Every slot written: the typer's verdict, term, type and tank.
example : elabAt E2src = writtenAt E2src := by decide +kernel
example : elabAt E11src = writtenAt E11src := by decide +kernel

-- The domains of call arguments erased: the written terms, at more fuel.
example : elabAt E11asrcA = ((writtenAt E11asrc).1, ⟨defaultFuel - 19, false⟩) ∧
    writtenAt E11asrc = ((writtenAt E11asrc).1, ⟨defaultFuel - 15, false⟩) ∧
    (writtenAt E11asrc).1.ty? = some .top := by
  decide +kernel
example : elabAt K1srcA = ((writtenAt K1src).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt K1src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt X1srcA = ((writtenAt X1src).1, ⟨defaultFuel - 27, false⟩) ∧
    (writtenAt X1src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt DomSrcD = ((writtenAt DomSrc).1, ⟨defaultFuel - 15, false⟩) ∧
    (writtenAt DomSrc).1.ty?.isSome = true := by
  decide +kernel

-- E2 with every domain erased: its only lambda is a field of a literal with a
-- written self type.
example : elabAt E2srcD = ((writtenAt E2src).1, ⟨defaultFuel - 59, false⟩) ∧
    (writtenAt E2src).1.ty? = some (.all (.all .top .bot) .top) := by
  decide +kernel

-- Domains from written types and ascriptions.
example : elabAt X2srcD = ((writtenAt X2src).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenAt X2src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt X3srcD = ((writtenAt X3src).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt X3src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt IdAscSrcD = ((writtenAt IdAscSrc).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenAt IdAscSrc).1.ty? = some (.all .top .top) := by
  decide +kernel
example : elabAt AscSrcD = ((writtenAt AscSrc).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenAt AscSrc).1.ty? = some (.all .top .top) := by
  decide +kernel
example : elabAt AndTopSrcD = ((writtenAt AndTopSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenAt AndTopSrc).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AndTwoSrcD = ((writtenAt AndTwoSrc).1, ⟨defaultFuel - 14, false⟩) ∧
    (writtenAt AndTwoSrc).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AliasSrcD = ((writtenAt AliasSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenAt AliasSrc).1.ty?.isSome = true := by
  decide +kernel

-- A literal without a self type at a `μ` goal.
example : elabAt AscObjSrcS = ((writtenAt AscObjSrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenAt AscObjSrc).1.ty?.isSome = true := by
  decide +kernel

-- Missing parameter type: no goal, a goal with no function part, a callee with
-- no dominant formal, a lambda bound by a written `let`.
example : elabAt Id0SrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt IdTopSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt E11srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt LowerSrcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabAt IncSrcD = (.no (.missingParamType none), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : elabAt LetArgSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Mismatch: incomparable domains, one function side the lambda does not meet,
-- an abstract type with a function upper bound.
example : elabAt AndIncSrcD = (.no .mismatch, ⟨defaultFuel - 2, false⟩) := by decide +kernel
example : elabAt AndOneSrcD = (.no .mismatch, ⟨defaultFuel - 5, false⟩) := by decide +kernel
example : elabAt UpperSrcD = (.no .mismatch, ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-! ### The callee's body

A lambda `λx. g x` with no goal, or with a goal that has no function part,
takes the dominant formal of `g`.  Scala compiles each program below that
compiles here, with `g` a method or a function value. -/

/-- A lambda bound with no type whose body applies `g` to the parameter, the
domain written. -/
def CalleeSrc : STm := dot% λ(g : ∀(x : ⊤) ⊤). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  It is the domain of `g`. -/
def CalleeSrcD : STm := dot% λ(g : ∀(x : ⊤) ⊤). let h = λx. g x in h

/-- The same with `g` bound by a `let`, so the program is closed. -/
def CalleeLetSrc : STm := dot% let g = λ(y : ⊤). y in let h = λ(x : ⊤). g x in h

/-- The same with the domain of `h` erased. -/
def CalleeLetSrcD : STm := dot% let g = λ(y : ⊤). y in let h = λx. g x in h

/-- A callee at an intersection of two function types with comparable domains,
the larger domain written. -/
def CalleeAndSrc : STm :=
  dot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The dominant formal is `⊤`. -/
def CalleeAndSrcD : STm := dot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λx. g x in h

/-- A callee at an intersection of two function types with incomparable
domains.  Scala takes their union, which the version lacks. -/
def CalleeIncSrcD : STm :=
  dot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤)). let h = λx. g x in h

/-- A callee with no function type. -/
def CalleeTopSrcD : STm := dot% λ(g : ⊤). let h = λx. g x in h

/-- A body whose argument is not the parameter. -/
def CalleeOtherSrcD : STm := dot% λ(g : ∀(x : ⊤) ⊤). λ(y : ⊤). let h = λx. g y in h

/-- A body that applies the parameter to itself. -/
def CalleeSelfSrcD : STm := dot% let h = λx. x x in h

/-- A body that applies a projection to the parameter.  The resolver binds the
projection first, so the body is a `let` and not `g x`. -/
def CalleeProjSrcD : STm := dot% λ(o : {a : ∀(x : ⊤) ⊤}). let h = λx. o.a x in h

/-- A block body. -/
def CalleeBlockSrcD : STm := dot% λ(g : ∀(x : ⊤) ⊤). let h = λx. (let z = g x in z) in h

/-- A goal with no function part, the domain written. -/
def CalleeTopGoalSrc : STm :=
  dot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ⊤ = λ(x : {a : ⊤}). g x in h

/-- The same with the domain erased.  It is the domain of `g`. -/
def CalleeTopGoalSrcD : STm := dot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ⊤ = λx. g x in h

/-- A goal with a function part whose domain is below the domain of `g`, the
domain written. -/
def CalleeFunGoalSrc : STm :=
  dot% λ(g : ∀(x : {a : ⊤}) ⊤).
         let h : ∀(x : {a : ⊤} ∧ {b : ⊤}) ⊤ = λ(x : {a : ⊤} ∧ {b : ⊤}). g x in h

/-- The same with the domain erased.  The goal gives it, not the callee. -/
def CalleeFunGoalSrcD : STm :=
  dot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ∀(x : {a : ⊤} ∧ {b : ⊤}) ⊤ = λx. g x in h

/-- A call argument whose formal is `⊤`, the domain written. -/
def CalleeArgSrc : STm := dot% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (λ(x : ⊤). g x)

/-- The same with the domain erased.  The formal has no function part, so the
callee gives it. -/
def CalleeArgSrcD : STm := dot% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (λx. g x)

-- The erased call argument is the written one with the argument's domain erased.
example : (resolveP exampleTable CalleeArgSrc).map PTm.eraseArgs = resolveP exampleTable CalleeArgSrcD :=
  rfl

-- The domain of the callee: the written terms, at more fuel.
example : elabAt CalleeSrcD = ((writtenAt CalleeSrc).1, ⟨defaultFuel - 4, false⟩) ∧
    writtenAt CalleeSrc = ((writtenAt CalleeSrc).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenAt CalleeSrc).1.ty? = some (.all (.all .top .top) (.all .top .top)) := by
  decide +kernel
example : elabAt CalleeLetSrcD = ((writtenAt CalleeLetSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenAt CalleeLetSrc).1.ty? = some (.all .top .top) := by
  decide +kernel
example : elabAt CalleeAndSrcD = ((writtenAt CalleeAndSrc).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt CalleeAndSrc).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeTopGoalSrcD = ((writtenAt CalleeTopGoalSrc).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenAt CalleeTopGoalSrc).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeFunGoalSrcD = ((writtenAt CalleeFunGoalSrc).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenAt CalleeFunGoalSrc).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeArgSrcD = ((writtenAt CalleeArgSrc).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenAt CalleeArgSrc).1.ty?.isSome = true := by
  decide +kernel

-- Missing parameter type: no dominant formal, no function type, a body that is
-- not `g x` with `x` the parameter.
example : elabAt CalleeIncSrcD = (.no (.missingParamType none), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabAt CalleeTopSrcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabAt CalleeOtherSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeSelfSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeProjSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeBlockSrcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Self types formed from definitions

The rounds alone, on a literal without a self type, then the self type in
lockstep.  Each check compares the self type `formSelfF` forms with the self
type a written form of the program states, or gives the reason the rounds
stop. -/

/-- What `formSelfF` gives the first literal without a self type of a
program. -/
inductive Formed where
  /-- A self type formed, and whether it is the one the written form states. -/
  | self (written : Bool)
  /-- The reason the rounds stop. -/
  | no (r : EReason)
  /-- No such literal, or the written form is not the same program there. -/
  | shape
deriving DecidableEq

/-- `formSelfF` on the first literal without a self type, found under written
lambdas and in the bound terms of `let`s, against the same place of the
written form. -/
def formGo {s : Sig} (Γ : Ctx s) (n : Nat) : PTm s → PTm s → Formed × Tank
  | .lam (some S) t, .lam (some S') t' =>
      if S = S' then formGo (Γ.cons S) n t t' else (.shape, ⟨n, true⟩)
  | .let _ _ t _, .let _ _ t' _ => formGo Γ n t t'
  | .obj none d, .obj o _ =>
      match formSelfF Γ d (jobsF d) ⟨n, false⟩ with
      | (.ok (T, _), tk) => (.self (decide (o = some T)), tk)
      | (.error rs, tk) => (.no (Reason.top tk.out rs), tk)
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a surface program, against its written form, with the tank
left. -/
def formAt (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolveP exampleTable e, resolveP exampleTable w with
  | some p, some q => formGo Ctx.nil n p q
  | _, _ => (.shape, ⟨n, true⟩)

/-- E5 with the self type of its literal written at the type of the field's
right-hand side. -/
def E5srcW : STm :=
  dot% λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : {A : ⊤..⊤}}. {a = v}) in
         let o = f w in o.a

/-- E6 with the self type of its literal written at the type of the field's
right-hand side. -/
def E6srcW : STm :=
  dot% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : {a : ⊤}}. {type T = {a : ⊤}} ∧ {v = n})

/-- A field that reads a later field. -/
def FwdSrcS : STm := dot% ν(x. {a = x.b} ∧ {b = λ(y : ⊤). y})

/-- The same with the self type written. -/
def FwdSrc : STm :=
  dot% ν(x : {a : ∀(y : ⊤) ⊤} ∧ {b : ∀(y : ⊤) ⊤}. {a = x.b} ∧ {b = λ(y : ⊤). y})

/-- A recursive field with a written type. -/
def RecWSrcS : STm := dot% ν(x. {a : ∀(y : ⊤) ⊤ = λy. let z = x.a in z y})

/-- The same with the self type written. -/
def RecWSrc : STm := dot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let z = x.a in z y})

/-- Two fields that read each other. -/
def CycSrcS : STm := dot% ν(x. {a = x.b} ∧ {b = x.a})

/-- A recursive field without a written type. -/
def RecUSrcS : STm := dot% ν(x. {a = λ(y : ⊤). let z = x.a in z y})

/-- A field that reads a cycle between two later fields. -/
def Cyc3SrcS : STm := dot% ν(x. {a = x.b} ∧ {b = x.v} ∧ {v = x.b})

/-- A recursive field that reads itself through an alias of the self. -/
def AliasRecSrcS : STm := dot% ν(x. {a = λ(y : ⊤). let w = x in let u = w.a in u y})

/-- A field that is the self. -/
def BareSrcS : STm := dot% ν(x. {a = x})

/-- The same with the self type written at the snapshot the field is typed at. -/
def BareSrc : STm := dot% ν(x : {a : μ(y. ⊤)}. {a = x})

/-- A field that reads a later field that is the self. -/
def FwdSelfSrcS : STm := dot% ν(x. {a = x.b} ∧ {b = x})

/-- The same with the self type written. -/
def FwdSelfSrc : STm := dot% ν(x : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = x.b} ∧ {b = x})

/-- A field that is the self, and a later one that reads it. -/
def BareProjSrcS : STm := dot% ν(x. {a = x} ∧ {b = x.a})

/-- The same with the self type written. -/
def BareProjSrc : STm := dot% ν(x : {a : μ(y. ⊤)} ∧ {b : μ(y. ⊤)}. {a = x} ∧ {b = x.a})

/-- A field whose right-hand side has two types, `⊤` first. -/
def X5SrcS1 : STm :=
  dot% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). ν(s. {a = y.a} ∧ {v = let z = s.a in z.b})

/-- The same with the self type written. -/
def X5Src1 : STm :=
  dot% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}).
         ν(s : {a : {b : ⊤}} ∧ {v : ⊤}. {a = y.a} ∧ {v = let z = s.a in z.b})

/-- The same two types in the other order. -/
def X5SrcS2 : STm :=
  dot% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}). ν(s. {a = y.a} ∧ {v = let z = s.a in z.b})

/-- The same with the self type written. -/
def X5Src2 : STm :=
  dot% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}).
         ν(s : {a : {b : ⊤}} ∧ {v : ⊤}. {a = y.a} ∧ {v = let z = s.a in z.b})

/-- A field whose right-hand side has two incomparable types. -/
def AmbSrcS : STm := dot% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s. {a = y.a})

/-- A field that is a lambda without a domain and without a goal. -/
def NoDomSrcS : STm := dot% ν(x. {a = λy. y})

-- The jobs of a field list: the fields without a written type, in source order.
example : (match resolveP exampleTable FwdSrcS with
    | some (.obj none d) => (jobsF d).map (·.lbl)
    | _ => []) = [.trm 0, .trm 1] := by decide +kernel
example : (match resolveP exampleTable RecWSrcS with
    | some (.obj none d) => (jobsF d).length
    | _ => 1) = 0 := by decide +kernel

-- Dependencies: a projection through an alias of the self, a bare use.
example : (match resolveP exampleTable AliasRecSrcS with
    | some (.obj none d) => (jobsF d).map (·.deps)
    | _ => []) = [([.trm 0], false)] := by decide +kernel
example : (match resolveP exampleTable FwdSelfSrcS with
    | some (.obj none d) => (jobsF d).map (·.deps)
    | _ => []) = [([.trm 1], false), ([], true)] := by decide +kernel

-- E2 and E7 form their written self types.  E7 has no job.
example : formAt E2srcS E2src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt E7srcS E7src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- E5 and E6 form the types of the right-hand sides.
example : formAt E5srcS E5srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt E6srcS E6srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- A field that reads a later one waits a round.  A field with a written type
-- is no job.
example : formAt FwdSrcS FwdSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : formAt RecWSrcS RecWSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- Cyclic references: two fields that read each other, a recursive field, a
-- cycle that a field before it reads, a recursion through an alias.
example : formAt CycSrcS CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt RecUSrcS RecUSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt Cyc3SrcS Cyc3SrcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt AliasRecSrcS AliasRecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Bare uses of the self, typed at the snapshot.
example : formAt BareSrcS BareSrc = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt FwdSelfSrcS FwdSelfSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : formAt BareProjSrcS BareProjSrc = (.self true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

-- The least candidate, in both orders of the intersection.
example : formAt X5SrcS1 X5Src1 = (.self true, ⟨defaultFuel - 12, false⟩) := by decide +kernel
example : formAt X5SrcS2 X5Src2 = (.self true, ⟨defaultFuel - 11, false⟩) := by decide +kernel

-- No least candidate, and a job whose lambda has no domain.
example : formAt AmbSrcS AmbSrcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : formAt NoDomSrcS NoDomSrcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Literals without a self type

The literal clause on its own: the self type formed from the definitions, the
literal filled with the terms the rounds elaborated, and the filled literal
typed by the object clause of `synthF` in the real context.  A program that
compiles elaborates to its written form, at the type `synthF` gives that
form.  A literal at the top of a program, or under its lambdas, has a
derivation that ends in `HasTy.obj`. -/

/-- The derivation ends in the object rule, under the lambdas of the term. -/
def objBelow {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} : HasTy Γ t T → Bool
  | .obj _ _ => true
  | .lam h => objBelow h
  | _ => false

/-- Whether the derivation of the first candidate of a surface program ends in
the object rule, under its lambdas. -/
def objAt (e : STm) (n : Nat := defaultFuel) : Bool :=
  match resolveP exampleTable e with
  | some p =>
      match elabTopF n p with
      | (.ok c, _) => objBelow c.deriv
      | (.error _, _) => false
  | none => false

/-- The literal of E2 with its self type erased. -/
def E2objSrcS : STm := dot% ν(s. {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- The literal of E2 with its self type written. -/
def E2objSrc : STm :=
  dot% ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
         {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- A literal without a self type ascribed at `⊤`.  The goal is no `μ`, so the
self type is formed and the literal subsumed. -/
def AscTopSrcS : STm := dot% λ(n : {b : ⊤}). (ν(z. {a = n}) : ⊤)

/-- The same with the self type written. -/
def AscTopSrc : STm := dot% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : ⊤)

/-- `ν(x1. {a = ν(x2. {a = … ν(xd. {a = n}) …})})` with `d` literals: each
field holds the next literal, the innermost the variable `v`.  The label is
`a` of the example table. -/
def nestP : Nat → {s : Sig} → BVar s .var → PTm s
  | 0, _, v => .path (.var v)
  | d + 1, _, v => .obj none (.trm (.trm 0) none (nestP d v.there))

/-- The nesting under `λ(n : {b : ⊤})`. -/
def X6P (d : Nat) : PTm [] := .lam (some (.fld (.trm 1) .top)) (nestP d .here)

/-- The fuel of the nesting with every self type erased, and the fuel of the
typer on the term it elaborates to, when both end unmarked. -/
def x6At (d : Nat) : Option (Nat × Nat) :=
  match elabTopF defaultFuel (X6P d) with
  | (.ok c, t) =>
      match synthTopF defaultFuel c.a with
      | (some _, w) =>
          if t.out || w.out then none else some (defaultFuel - t.left, defaultFuel - w.left)
      | (none, _) => none
  | (.error _, _) => none

-- The literal of E2, E2 and E7 compile at their written terms.  The literals
-- have `HasTy.obj` at the head.
example : elabAt E2objSrcS = ((writtenAt E2objSrc).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenAt E2objSrc).1.ty?.isSome = true ∧ objAt E2objSrcS = true := by
  decide +kernel
example : elabAt E2srcS = ((writtenAt E2src).1, ⟨defaultFuel - 58, false⟩) ∧
    (writtenAt E2src).1.ty? = some (.all (.all .top .bot) .top) := by
  decide +kernel
example : elabAt E7srcS = ((writtenAt E7src).1, ⟨defaultFuel, false⟩) ∧
    (writtenAt E7src).1.ty?.isSome = true ∧ objAt E7srcS = true := by
  decide +kernel

-- E5 and E6 compile at the types of their right-hand sides.
example : elabAt E5srcS = ((writtenAt E5srcW).1, ⟨defaultFuel - 8, false⟩) ∧
    (writtenAt E5srcW).1.ty?.isSome = true := by
  decide +kernel
example : elabAt E6srcS = ((writtenAt E6srcW).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenAt E6srcW).1.ty?.isSome = true ∧ objAt E6srcS = true := by
  decide +kernel

-- A field that reads a later one, and a recursive field with a written type.
example : elabAt FwdSrcS = ((writtenAt FwdSrc).1, ⟨defaultFuel - 14, false⟩) ∧
    writtenAt FwdSrc = ((writtenAt FwdSrc).1, ⟨defaultFuel - 11, false⟩) ∧
    (writtenAt FwdSrc).1.ty?.isSome = true ∧ objAt FwdSrcS = true := by
  decide +kernel
example : elabAt RecWSrcS = ((writtenAt RecWSrc).1, ⟨defaultFuel - 14, false⟩) ∧
    writtenAt RecWSrc = ((writtenAt RecWSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenAt RecWSrc).1.ty?.isSome = true ∧ objAt RecWSrcS = true := by
  decide +kernel

-- Cyclic references.
example : elabAt CycSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt RecUSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt Cyc3SrcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt AliasRecSrcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Bare uses of the self: pass 2 checks the self against the snapshot type
-- `μ(y. ⊤)` in the real context.
example : elabAt BareSrcS = ((writtenAt BareSrc).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenAt BareSrc).1.ty?.isSome = true ∧ objAt BareSrcS = true := by
  decide +kernel
example : elabAt FwdSelfSrcS = ((writtenAt FwdSelfSrc).1, ⟨defaultFuel - 28, false⟩) ∧
    writtenAt FwdSelfSrc = ((writtenAt FwdSelfSrc).1, ⟨defaultFuel - 25, false⟩) ∧
    (writtenAt FwdSelfSrc).1.ty?.isSome = true ∧ objAt FwdSelfSrcS = true := by
  decide +kernel
example : elabAt BareProjSrcS = ((writtenAt BareProjSrc).1, ⟨defaultFuel - 28, false⟩) ∧
    writtenAt BareProjSrc = ((writtenAt BareProjSrc).1, ⟨defaultFuel - 25, false⟩) ∧
    (writtenAt BareProjSrc).1.ty?.isSome = true ∧ objAt BareProjSrcS = true := by
  decide +kernel

-- The least candidate, in both orders of the intersection.
example : elabAt X5SrcS1 = ((writtenAt X5Src1).1, ⟨defaultFuel - 31, false⟩) ∧
    writtenAt X5Src1 = ((writtenAt X5Src1).1, ⟨defaultFuel - 19, false⟩) ∧
    (writtenAt X5Src1).1.ty?.isSome = true ∧ objAt X5SrcS1 = true := by
  decide +kernel
example : elabAt X5SrcS2 = ((writtenAt X5Src2).1, ⟨defaultFuel - 29, false⟩) ∧
    writtenAt X5Src2 = ((writtenAt X5Src2).1, ⟨defaultFuel - 18, false⟩) ∧
    (writtenAt X5Src2).1.ty?.isSome = true ∧ objAt X5SrcS2 = true := by
  decide +kernel

-- No least candidate, and a job whose lambda has no domain.
example : elabAt AmbSrcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabAt NoDomSrcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- A goal that is no `μ`: the self type formed, then subsumption.
example : elabAt AscTopSrcS = ((writtenAt AscTopSrc).1, ⟨defaultFuel - 3, false⟩) ∧
    writtenAt AscTopSrc = ((writtenAt AscTopSrc).1, ⟨defaultFuel - 7, false⟩) ∧
    (writtenAt AscTopSrc).1.ty?.isSome = true := by
  decide +kernel

-- Nested literals: the fuel grows with the square of the depth, since each
-- field is elaborated once and checked once more by the object clause.
example : x6At 4 = some (10, 4) := by decide +kernel
example : x6At 8 = some (36, 8) := by decide +kernel
example : x6At 12 = some (78, 12) := by decide +kernel
example : x6At 17 = some (153, 17) := by decide +kernel

end ElabChecks

end Frontend
