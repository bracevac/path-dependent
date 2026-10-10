import Coercions.Paths.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# The elaborator

The elaborator fills the empty slots of a partial term (`PTm`, `Ann.lean`) and
types the result with the typer of `Typer.lean`, on the same tank.

## The rule of empty slots

Each function first asks `PTm.full?`.  A term with no empty slot goes to the
typer as it is: `elabF` calls `synthF`, and `elabChkF` calls `checkF`.  So a
program with every slot written elaborates as the typer types it, at the same
fuel (`elabF_toI`, `elabChkF_toI`).  Only a term with an empty slot below it
takes the clauses of this module.

## Two modes

`elabF` synthesizes.  It returns candidates, each an elaborated term, its type
and the `Paths.DotMNF.HasTy` derivation of its erasure, as `synthF` does.
`elabChkF` checks against a goal and returns the elaborated term with a
derivation at the goal.  `elabDefsF` elaborates definitions against a self type
in lockstep and returns them with their slots filled, without a derivation.
Every result carries `p.fills a = true`: the elaborated term agrees with every
slot the program writes.

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
- A field of a literal with a self type gets the field's declaration.  A field
  declared stable, `{val a : μ(x. U)}`, holds a literal, and that literal takes
  `U` as its self type.
- A lambda's body gets the result part of the goal.
- A block `let x = t in u` passes its goal to `u`, as `Typer.typedBlock` does.

## Lambdas

A lambda without a domain takes it from the function part of its goal
(`funPartF`), as `Typer.typedFunctionValue` does through
`Typer.decomposeProtoFunction` and `Type.findFunctionType`.  A selection `p.A`
whose member, found by the path lookup of `Look.lean`, has equal bounds is
replaced by the bound, to a fixpoint, as `strippedDealias` follows aliases.
The lookup follows stable fields and singletons along `p`.  `∀(x : S) V` gives
`S` and `V`.  The sides of an intersection meet.  One function side gives that
side.  Two sides whose domains are comparable give the larger domain and the
intersection of the results.  Two sides with incomparable domains are a
mismatch, since the compiler forms their union, which the version lacks.  A
selection with different bounds whose upper bound has a function part is a
mismatch, as for an abstract type with a function upper bound in the compiler.
Any other goal has no function part, a singleton `p.type` among them.

A lambda with no goal, or with a goal that has no function part, takes its
domain from the callee of a body `g x`, where `x` is the parameter and `g` a
variable bound outside the lambda, as `Typer.inferredFromTarget` does.  The
domain is the dominant formal of `g`, the goal `g` gives its argument.  The
lambda filled with it goes to the typer: `synthF` with no goal, `checkF` at the
goal.  Any other body, or a callee with no dominant formal, is the compiler's
"Missing parameter type".

A lambda whose body has no empty slot is filled with the domain and handed to
the typer at the goal (`lam_fill_full`).  Otherwise the body is checked against
the result part, and the lambda is moved to the goal by the subtyping goal.  A
lambda with a written domain whose body has an empty slot passes the result
part to its body in the same way.  `HasTy.lam` asks the domain to be well
formed, so a domain that is not is a mismatch.

## The fallback

A goal site whose attempt fails with the tank unmarked runs the typer's own
route on the term: synthesis, then subsumption to the goal.  So erasing a slot
at a goal site never loses a program whose filled form types by that route.

## Object literals

A literal with a self type has its definitions elaborated against it, with the
self bound at its `μ`.  The literal with its slots filled then goes to
`synthF`, whose object clause gives `HasTy.obj` in the real context, the self
bound with its definitions.  So the elaborated literal is typed once more, and
its derivation is the typer's.  A field declared stable holds a literal whose
self type the declaration gives, and its definitions are elaborated in the same
way, one level down.  A literal without a self type, checked at a goal
that dealiases to a `μ`, takes the body of that `μ` as its self type
(`selfGoalF`).  If that attempt fails with the tank unmarked, or the goal
gives no self type, or there is no goal, the self type is formed from the
definitions (`formSelfF`, below).  The literal is then filled at it
(`fillDefsF`): a field the rounds typed holds the term they elaborated for it,
a literal with a written self type has its definitions elaborated against that
type, and a field with a written type is elaborated against that type with the
self at the formed type.  The filled literal goes to `synthF` in the real
context, so its derivation is `HasTy.obj`, and each field is elaborated once
and checked once more.  At a goal the candidate is then subsumed.

## Self types formed from definitions

`formSelfF` forms the self type of a literal from its definitions, as the
completers of `Namer` type the members of a class.  Type members, fields with
a written type, the self as a whole right-hand side and literals with a
written self type are known at once.  Every other field is a job (`jobsF`),
typed in rounds (`roundsF`).  A round takes a snapshot of the self type known
so far and types every ready job once, by synthesis, with the self bound at
the snapshot.  A job is ready when none of the fields it depends on is pending
(`PTm.deps`): the fields it projects off the self, and the first fields of
the paths at the self in the types it writes, through the self's type
members.  A job that uses the self any other way is typed in the first round
in which no ready job lacks such a use.  A field's type is its least candidate
(`leastCandF`), and candidates with no least one are ambiguous.  A round that
types nothing stops with the cyclic reference `cycleAt` names.  The self type
is the definition list read in lockstep (`PDefs.fullSelf`), with a field that
holds a literal at a stable field.  The checks at the end run it on its own.

## Reasons

A rejected program gets a `Reason`, the type that `Coercions.Frontend.Reason`
shares among the front ends.  Here it is `EReason`: its labels are the member
labels of this version, and its reasons of the typer are `Empty`, since the
typer of this front end gives none of its own.  A rejection by the typer is
`mismatch`.  A marked tank is `limit`, the recursion limit.

Four reasons name an empty slot: `missingParamType`, `cyclicRef`,
`needsExplicitType` and `ambiguous`.  This version has no capture sets, so
`needsExplicitType`, which the capture checker gives for an inferred result
type, has no use here.  Each function returns the reasons of its failed
branches in search order.  A rejection reports `limit` when the tank ended
marked, else the first reason in search order, else `mismatch`
(`Reason.top`).

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
definitions.  `fullSelf_vfld` says that a stable field of a formed self type
holds a literal at a `μ` type, as `DefsTy.trmObj` asks.  `jobsF_written` says
that definitions whose fields all have a written type make no job.
`leastCand_least` says that the type of the least candidate is below the type
of every candidate, and `leastCand_sub?` says so with the typer's subtyping at
some fuel.  `cycleAt_onCycle` says that the cyclic reference is the label of a
pending job whose walk comes back to it.  `roundsF_framed` and `jobsF_framed`
say that the rounds are framed.  `obj_none_landed` says that a candidate of
a literal without a self type is a candidate of `synthF` on the filled
literal, at the self type the rounds formed.
-/

namespace PathsFrontend

open Frontend.Fuel PathsFrontend.Core Frontend.Reason
open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Tm Defs Ctx Sub HasTy DefsTy)

/-- The reasons of this front end: its labels, and no reason of the typer's
own. -/
abbrev EReason := Reason Label Empty

namespace ReasonChecks

/-- A marked tank reports the recursion limit. -/
example : Reason.top true [(.cyclicRef (.trm 0) : EReason)] = .limit := by
  decide +kernel

/-- An unmarked tank reports the first reason in search order. -/
example : Reason.top false [(.missingParamType none : EReason), .cyclicRef (.trm 0)]
    = .missingParamType none := by
  decide +kernel

/-- An unmarked tank with no reason is a mismatch. -/
example : Reason.top false ([] : List EReason) = .mismatch := by
  decide +kernel

/-- The reasons of the slots are told apart from the typer's rejection and
from the recursion limit. -/
example : (.cyclicRef (.trm 1) : EReason).isSlotReason = true
    ∧ (.ambiguous (.trm 1) : EReason).isSlotReason = true
    ∧ (.missingParamType none : EReason).isSlotReason = true
    ∧ (.mismatch : EReason).isSlotReason = false
    ∧ (.limit : EReason).isSlotReason = false := by
  decide +kernel

/-- Reasons at two labels differ. -/
example : (.cyclicRef (.trm 0) : EReason) ≠ .cyclicRef (.trm 1) := by
  decide +kernel

end ReasonChecks

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

theorem PDefs.fills_trm {s : Sig} {a c : Label} {o : Option (Ty s)} {t : PTm s} {U : Ty s}
    {b : ATm s} (ho : optAgree o U = true) (h : t.fills b = true) :
    (PDefs.trm a o t).fills (.fld c U) (.trm a b) = true := by
  cases o <;> simp_all [PDefs.fills, optAgree]

/-- A field with no written type agrees with any declaration. -/
theorem PDefs.fills_trm_none {s : Sig} {a : Label} {t : PTm s} {U : Ty s} {b : ATm s}
    (h : t.fills b = true) : (PDefs.trm a none t).fills U (.trm a b) = true := by
  simp [PDefs.fills, h]

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

/-- Definitions elaborated against a self type `T` in `Γ`, with their slots
filled.  There is no derivation: the literal they belong to is typed again by
`synthF` once they are filled, and that typing is the derivation.  A stable
field `{val a : μ(x. U)}` is typed by `DefsTy.trmObj` in a context that binds
the literal's self to its own definitions, which exist only once the
definitions are filled. -/
structure EDefs {s : Sig} (Γ : Ctx s) (d : PDefs s) (T : Ty s) where
  /-- The elaborated definitions. -/
  ds : ADefs s
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

/-- The check `checkF` gives a filled term `a` at `G`, as a check of the partial
term `p` it fills. -/
def fullCheckAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) (G : Ty s) :
    Fu (ECheck Γ p G) :=
  Fu.bind (checkF Γ a G) fun o =>
    Fu.ret (o.map fun hd => ⟨a, hd, h⟩, if o.isSome then [] else [.mismatch])

/-- The typer's synthesis of a term with every slot written. -/
def fullSynth {s : Sig} (Γ : Ctx s) (a : ATm s) : Fu (ESynth Γ a.toI) :=
  fullSynthAt Γ a.toI a (ATm.fills_toI a)

/-- The typer's check of a term with every slot written. -/
def fullCheck {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Ty s) : Fu (ECheck Γ a.toI G) :=
  fullCheckAt Γ a.toI a (ATm.fills_toI a) G

/-! ## The function part of a goal

`Type.findFunctionType` on the types of the version, after `strippedDealias`.
A selection `p.A` is read through `declsF`, the type members the path lookup
finds at `p`.  The lookups draw on the tank.  The index of `funPartF` bounds
the number of aliases followed.  `funPartAt` starts it at the fuel left, as
`declsF` starts a lookup, and every alias followed draws at least one unit, so
the index never runs out first. -/

/-- The function part of a goal: none, a domain and a result, or a mismatch. -/
inductive FunPart (s : Sig) where
  /-- No function part, the compiler's missing parameter type. -/
  | none
  /-- The domain `S` and the result part `V`. -/
  | one (S : Ty s) (V : Ty (s,x))
  /-- A function part the version cannot give, a type mismatch. -/
  | bad

/-- The upper bound of the first member with equal bounds, an alias. -/
def aliasOf {s : Sig} {Γ : Ctx s} {q : Path s} {A : Label} : List (Mem Γ q A) → Option (Ty s)
  | [] => none
  | m :: ms => if m.lo = m.hi then some m.hi else aliasOf ms

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
  | .sel q A =>
      Fu.bind (declsF Γ q A) fun ms =>
        match aliasOf ms with
        | some T => rec T
        | none => uppersPart rec (ms.map fun m => m.hi)
  | .top => Fu.ret .none
  | .bot => Fu.ret .none
  | .typ _ _ _ => Fu.ret .none
  | .fld _ _ => Fu.ret .none
  | .vfld _ _ => Fu.ret .none
  | .sngl _ => Fu.ret .none
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
  | .sel q A =>
      Fu.bind (declsF Γ q A) fun ms =>
        match aliasOf ms with
        | some T => rec T
        | none => Fu.ret (.sel q A)
  | .top => Fu.ret .top
  | .bot => Fu.ret .bot
  | .typ A S T => Fu.ret (.typ A S T)
  | .fld a T => Fu.ret (.fld a T)
  | .vfld a T => Fu.ret (.vfld a T)
  | .sngl q => Fu.ret (.sngl q)
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

/-- The candidates of a lambda with the well formed domain `S`, from those of
its body. -/
def lamCands {s : Sig} {Γ : Ctx s} {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s) (hwf : Ty.Wf S)
    (ho : optAgree o S = true) (r : ESynth (Γ.cons S) t) : ESynth Γ (.lam o t) :=
  (r.1.map fun c => ⟨.lam S c.a, .all S c.ty, .lam c.deriv hwf, PTm.fills_lam ho c.fills⟩, r.2)

/-- A lambda with domain `S` synthesized from the synthesis of its body.  A
domain that is not well formed is a mismatch, as `HasTy.lam` asks it to be. -/
def lamSynF {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (ho : optAgree o S = true) (syn : Fu (ESynth (Γ.cons S) t)) : Fu (ESynth Γ (.lam o t)) :=
  if hwf : Ty.Wf S then Fu.bind syn fun r => Fu.ret (lamCands S hwf ho r)
  else Fu.ret ([], [.mismatch])

/-- A lambda with domain `S`, whose body has an empty slot, checked at `G`
whose result part is `V`.  The body is checked against `V`, and the lambda is
moved to `G`.  On an unmarked failure the body is synthesized under `S` and the
lambda subsumed.  A domain that is not well formed is a mismatch. -/
def lamGoalF {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s) (V : Ty (s,x))
    (G : Ty s) (ho : optAgree o S = true) (chk : Fu (ECheck (Γ.cons S) t V))
    (syn : Unit → Fu (ESynth (Γ.cons S) t)) : Fu (ECheck Γ (.lam o t) G) :=
  if hwf : Ty.Wf S then
    orElseW Option.isSome
      (Fu.bind chk fun r =>
        match r.1 with
        | some e => toGoal Γ G ⟨.lam S e.a, .all S V, .lam e.deriv hwf, PTm.fills_lam ho e.fills⟩
        | none => Fu.ret (none, r.2))
      (fun _ => Fu.bind (syn ()) fun r => subsume Γ G (lamCands S hwf ho r))
  else Fu.ret (none, [.mismatch])

/-- A lambda without a domain at a goal whose function part has the domain `S`
and the result part `V`.  With a body that has no empty slot, the lambda
filled with `S` goes to `checkF`.  Otherwise `lamGoalF`. -/
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
filled lambda goes to `synthF`, which asks the domain to be well formed.  Any
other body, or a callee with no dominant formal, is the compiler's missing
parameter type. -/
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
`lamCalleeSynF`, with `checkF` on the filled lambda at `G`. -/
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
the self at `μ` of it, then the filled literal typed by `synthF`, which binds
the self with its definitions. -/
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
It is a plain field, since a field with a written type is no stable member.
Two more fields are known at once.  The self as the whole right-hand side is
at its singleton `x.type`, the type the compiler keeps for `val c = this`.  A
literal with a written self type `T` is at the stable field `{val a : μ(T)}`,
since the version types such a literal at that type and at no other.  Every
other field is typed on demand (`Namer.inferredResultType`), in rounds.  A
field the rounds typed at a literal's type is a stable field, as
`DefsTy.trmObj` declares it, and any other at a plain field.  `known` lists
the fields typed so far, by label.  `v` is the self. -/

/-- The declaration a field without a written type has at once: the self `v`
as the whole right-hand side at `v.type`, a literal with a written self type
`T` at `{val a : μ(T)}`.  Any other right-hand side has none. -/
def PTm.atOnce {s : Sig} (v : BVar s .var) (a : Label) : PTm s → Option (Ty s)
  | .path y => if y = v then some (.fld a (.sngl (.var y))) else none
  | .obj (some T) _ => some (.vfld a (.mu T))
  | _ => none

/-- The declaration of a field the rounds typed at `U`: a literal at its `μ`
type is a stable field, anything else a plain field. -/
def declOf {s : Sig} (a : Label) : PTm s → Ty s → Ty s
  | .obj _ _, .mu T => .vfld a (.mu T)
  | _, U => .fld a U

/-- The self type the definitions have so far.  A field not yet typed is left
out, and `none` means that nothing is known. -/
def PDefs.partialSelf {s : Sig} (v : BVar s .var) : PDefs s → List (Label × Ty s) → Option (Ty s)
  | .typ A T, _ => some (.typ A T T)
  | .trm a (some U) _, _ => some (.fld a U)
  | .trm a none t, known =>
      match t.atOnce v a with
      | some D => some D
      | none => (lookupL known a).map (declOf a t)
  | .and d e, known =>
      match d.partialSelf v known, e.partialSelf v known with
      | some T1, some T2 => some (.and T1 T2)
      | some T1, none => some T1
      | none, o => o

/-- The snapshot a round types its jobs against: the self type known so far,
or `⊤` when nothing is. -/
def PDefs.probeSelf {s : Sig} (d : PDefs s) (v : BVar s .var) (known : List (Label × Ty s)) :
    Ty s :=
  (d.partialSelf v known).getD .top

/-- The self type in lockstep with the definitions, once every field is typed:
the shape `DefsTy` concludes and `checkDefsF` reads. -/
def PDefs.fullSelf {s : Sig} (v : BVar s .var) : PDefs s → List (Label × Ty s) → Option (Ty s)
  | .typ A T, _ => some (.typ A T T)
  | .trm a (some U) _, _ => some (.fld a U)
  | .trm a none t, known =>
      match t.atOnce v a with
      | some D => some D
      | none => (lookupL known a).map (declOf a t)
  | .and d e, known =>
      match d.fullSelf v known, e.fullSelf v known with
      | some T1, some T2 => some (.and T1 T2)
      | _, _ => none

/-- `T` is the self type of `d` in lockstep, with the self `v`.  A type member
gives its right-hand side on both bounds, a field with a written type that
type, a field known at once its declaration, any other field the declaration
of the first type `known` gives its label, and an intersection of definitions
the intersection of their self types. -/
inductive Lockstep {s : Sig} (v : BVar s .var) (known : List (Label × Ty s)) :
    PDefs s → Ty s → Prop where
  /-- `{type A = T}` at `{A : T .. T}`. -/
  | typ (A : Label) (T : Ty s) : Lockstep v known (.typ A T) (.typ A T T)
  /-- `{a : U = t}` at `{a : U}`. -/
  | written (a : Label) (U : Ty s) (t : PTm s) : Lockstep v known (.trm a (some U) t) (.fld a U)
  /-- `{a = t}` at the declaration it has at once. -/
  | atOnce (a : Label) (t : PTm s) (D : Ty s) (h : t.atOnce v a = some D) :
      Lockstep v known (.trm a none t) D
  /-- `{a = t}` at the declaration of `U`, the type known at `a`. -/
  | inferred (a : Label) (U : Ty s) (t : PTm s) (hn : t.atOnce v a = none)
      (h : lookupL known a = some U) : Lockstep v known (.trm a none t) (declOf a t U)
  /-- `d1 ∧ d2` at `T1 ∧ T2`. -/
  | and {d1 d2 : PDefs s} {T1 T2 : Ty s} :
      Lockstep v known d1 T1 → Lockstep v known d2 T2 → Lockstep v known (.and d1 d2) (.and T1 T2)

/-- Every field of the definitions has a written type. -/
def PDefs.AllFieldsWritten {s : Sig} : PDefs s → Prop
  | .typ _ _ => True
  | .trm _ o _ => o.isSome = true
  | .and d e => d.AllFieldsWritten ∧ e.AllFieldsWritten

/-- The labels of a definition list, in source order. -/
def PDefs.labels {s : Sig} : PDefs s → List Label
  | .typ A _ => [A]
  | .trm a _ _ => [a]
  | .and d e => d.labels ++ e.labels

/-- The labels of a definition list are pairwise distinct, as
`Paths.DotMNF.Defs.Distinct` says of the version's definitions. -/
inductive PDefs.Distinct : {s : Sig} → PDefs s → Prop where
  | typ {s : Sig} {A : Label} {T : Ty s} : PDefs.Distinct (.typ A T)
  | trm {s : Sig} {a : Label} {o : Option (Ty s)} {t : PTm s} : PDefs.Distinct (.trm a o t)
  | and {s : Sig} {d1 d2 : PDefs s} :
      PDefs.Distinct d1 → PDefs.Distinct d2 → (∀ l, l ∈ d1.labels → l ∉ d2.labels) →
      PDefs.Distinct (.and d1 d2)

/-- The right-hand side of the field at a label.  The right conjunct shadows,
as in `Paths.DotMNF.Defs.lookupTrm`. -/
def PDefs.lookupTrm {s : Sig} : PDefs s → Label → Option (PTm s)
  | .typ _ _, _ => none
  | .trm a _ t, l => if l = a then some t else none
  | .and d e, l => (e.lookupTrm l).or (d.lookupTrm l)

/-! ## Jobs

A job is a field without a written type that is not known at once.  It
carries its dependencies, read off the right-hand side by `PTm.deps`, and its
synthesis as a function of the context, so that a round can run it with the
self bound at the snapshot.  `jobsF` makes the jobs of a definition list inside
the elaborator's mutual block, where the synthesis of a field is a call on a
subterm. -/

/-- A field without a written type: its label, its right-hand side, the
fields it depends on with the flag of any other use of the self, and its
synthesis in a context. -/
structure Job (s : Sig) where
  /-- The field's label. -/
  lbl : Label
  /-- The right-hand side. -/
  tm : PTm s
  /-- The fields the right-hand side depends on, and the flag. -/
  deps : List Label × Bool
  /-- The synthesis of the right-hand side. -/
  run : (Γ : Ctx s) → Fu (ESynth Γ tm)

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
when none of the fields it depends on is pending.  A job that uses the self
any other way waits for the first round in which no ready job lacks such a
use.  So two such jobs do not see each other, and a job that projects the
field of one sees it.  The number of rounds is an index, so the rounds are
structural. -/

/-- A job is ready when none of the fields it depends on is pending. -/
def readyIn {s : Sig} (pend : List Label) (j : Job s) : Bool :=
  j.deps.1.all fun a => !pend.contains a

/-- Whether a round types the jobs that use the self any other way: when no
ready job lacks such a use. -/
def bareRound {s : Sig} (js : List (Job s)) : Bool :=
  !(js.any fun j => readyIn (js.map (·.lbl)) j && !j.deps.2)

/-- Whether a round over the pending jobs `js` types `j`: it is ready, and it
uses the self any other way exactly when the round types such jobs. -/
def picks {s : Sig} (js : List (Job s)) (j : Job s) : Bool :=
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

A round that types nothing has every pending job waiting for a pending field.
The walk starts at the first pending job in source order and follows the
first pending field it waits for, until a label repeats.  That label is the
cyclic reference, the member `SymDenotation.completeFrom` reaches again while
its completion is under way. -/

/-- The pending fields a job depends on, in term order. -/
def waitsFor {s : Sig} (js : List (Job s)) (j : Job s) : List Label :=
  j.deps.1.filter fun a => (js.map (·.lbl)).contains a

/-- The label the walk visits after `l`: the first pending field that the
first job at `l` waits for. -/
def nextL {s : Sig} (js : List (Job s)) (l : Label) : Option Label :=
  match js.find? (fun j => decide (j.lbl = l)) with
  | some j => (waitsFor js j).head?
  | none => none

/-- The walk from `l`, with the labels `seen` before it, for at most `n`
steps: the first label it visits twice. -/
def cycleFrom {s : Sig} (js : List (Job s)) : Nat → List Label → Label → Option Label
  | 0, _, _ => none
  | n + 1, seen, l =>
      if seen.contains l then some l
      else
        match nextL js l with
        | some l' => cycleFrom js n (l :: seen) l'
        | none => none

/-- The cyclic reference among the pending jobs: the first label the walk
from the first job visits twice, within `n` steps. -/
def cycleAt {s : Sig} (js : List (Job s)) (n : Nat) : Option Label :=
  match js with
  | [] => none
  | j :: _ => cycleFrom js n [] j.lbl

/-- The label the walk reaches from `l` in `k` steps. -/
def walkL {s : Sig} (js : List (Job s)) : Nat → Label → Option Label
  | 0, l => some l
  | k + 1, l => (nextL js l).bind (walkL js k)

/-- The walk from a job comes back to its label. -/
def OnCycle {s : Sig} (js : List (Job s)) (j : Job s) : Prop :=
  ∃ k, walkL js (k + 1) j.lbl = some j.lbl

/-- The reason of a round that types nothing.  The walk visits at most one
label per job before one repeats. -/
def stallReason {s : Sig} (js : List (Job s)) : EReason :=
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
jobs.  The self is the innermost variable.  One round per job suffices, and
one more stops. -/
def formSelfF {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) (js : List (Job (s,x))) :
    Fu (Except (List EReason) (Ty (s,x) × List (Done (s,x)))) :=
  Fu.bind (roundsF Γ (d.probeSelf .here) (js.length + 1) js []) fun r =>
    match r with
    | .ok done =>
        Fu.ret (match d.fullSelf .here (Done.known done) with
          | some T => .ok (T, done)
          | none => .error [.mismatch])
    | .error rs => Fu.ret (.error rs)

/-! ## The filled literal

Once the self type is formed, the literal is filled and handed to the object
clause of `synthF` in the real context, where the self is bound with its
definitions.  A field the rounds typed holds the term they elaborated for it,
so no such field is elaborated twice.  When that term is a literal, the formed
self type declares the field stable at the literal's `μ` type, and the object
clause checks it by `DefsTy.trmObj`.  The self as a whole right-hand side has
no empty slot and stays as it is.  A literal with a written self type has its
definitions elaborated against that type, with its own self at the `μ` of it.
A field with a written type is elaborated against that type with the outer
self at the formed type, unless its right-hand side has no empty slot.  The
object clause then checks every field once more. -/

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

theorem PDefs.fills_and' {s : Sig} {d1 d2 : PDefs s} {T : Ty s} {e1 e2 : ADefs s}
    (h1 : d1.fills (andLeft T) e1 = true) (h2 : d2.fills (andRight T) e2 = true) :
    (PDefs.and d1 d2).fills T (.and e1 e2) = true := by
  simp [PDefs.fills, h1, h2]

theorem PDefs.fills_typ {s : Sig} (A : Label) (S T : Ty s) :
    (PDefs.typ A S).fills T (.typ A S) = true := by
  simp [PDefs.fills]

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
      | some U, .path .here =>
          Fu.bind (chk U) fun r => Fu.ret (listO (r.1.map fun e => ⟨e.a, U, e.deriv, e.fills⟩), r.2)
      | _, _ => syn

/-- A `let` with the written type `U`: the body checked against `U` under the
binder, for the first candidate of the bound term that allows it.  `U` must be
well formed, as `HasTy.let` asks. -/
def letAnnR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (U : Ty s)
    (r1 : ESynth Γ t) (chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u U.weaken)) :
    Fu (ESynth Γ (.let g (some U) t u)) :=
  if hwf : Ty.Wf U then
    Fu.bind (firstSomeR (fun (c1 : ECand Γ t) => Fu.bind (chk c1) fun r =>
        Fu.ret (r.1.map (fun (e : EChk (Γ.cons c1.ty) u U.weaken) => (⟨.let (some U) c1.a e.a, U,
          (HasTy.let c1.deriv e.deriv hwf : HasTy Γ (.let c1.a.erase e.a.erase) U),
          PTm.fills_let c1.fills e.fills⟩ : ECand Γ (.let g (some U) t u))), r.2)) r1.1) fun r =>
      Fu.ret (listO r.1, r1.2 ++ r.2)
  else Fu.ret ([], r1.2 ++ [.mismatch])

/-- A `let` without a type: every candidate of the body under every candidate
of the bound term, its type avoided by `letAvoidC`, as the `let` clause of
`synthF`. -/
def letNoneR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (r1 : ESynth Γ t)
    (syn : (c1 : ECand Γ t) → Fu (ESynth (Γ.cons c1.ty) u)) : Fu (ESynth Γ (.let g none t u)) :=
  Fu.bind (flatMapR (fun (c1 : ECand Γ t) => Fu.bind (syn c1) fun r2 =>
      Fu.bind (flatMapR (fun (c2 : ECand (Γ.cons c1.ty) u) =>
          Fu.bind (letAvoidC (t := c1.a.erase) (u := c2.a.erase) ⟨c1.ty, c1.deriv⟩ ⟨c2.ty, c2.deriv⟩)
            fun cs => Fu.ret (cs.map fun (c : Cand Γ (.let c1.a.erase c2.a.erase)) =>
              (⟨.let none c1.a c2.a, c.ty, c.deriv, PTm.fills_let c1.fills c2.fills⟩ :
                ECand Γ (.let g none t u)), ([] : List EReason)))
        r2.1) fun r3 => Fu.ret (r3.1, r2.2 ++ r3.2)) r1.1) fun r =>
    Fu.ret (dedupE r.1, r1.2 ++ r.2)

/-- A block checked at `G`: the body checked against `G` under the binder, for
the first candidate of the bound term that allows it.  `G` must be well formed,
as `HasTy.let` asks. -/
def blockR {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (G : Ty s)
    (r1 : ESynth Γ t) (chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u G.weaken)) :
    Fu (ECheck Γ (.let g none t u) G) :=
  if hwf : Ty.Wf G then
    Fu.bind (firstSomeR (fun (c1 : ECand Γ t) => Fu.bind (chk c1) fun r =>
        Fu.ret (r.1.map (fun (e : EChk (Γ.cons c1.ty) u G.weaken) => (⟨.let none c1.a e.a,
          (HasTy.let c1.deriv e.deriv hwf : HasTy Γ (.let c1.a.erase e.a.erase) G),
          PTm.fills_let c1.fills e.fills⟩ : EChk Γ (.let g none t u) G)), r.2)) r1.1) fun r =>
      Fu.ret (r.1, r1.2 ++ r.2)
  else Fu.ret (none, r1.2)

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

/-- A call argument checked at `G`, as `argSynF` with `checkF` on the filled
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
a domain has no goal here.  It takes the dominant formal of the callee of a
body `g x`, and any other body is the compiler's missing parameter type. -/
def elabF {s : Sig} (Γ : Ctx s) (p : PTm s) : Fu (ESynth Γ p) :=
  match hp : p.full? with
  | some a => fullSynthAt Γ p a (PTm.fills_of_full? hp)
  | none =>
      match p with
      | .lam (some S) t => lamSynF Γ S (optAgree_some S) (elabF (Γ.cons S) t)
      | .lam none t => lamCalleeSynF Γ t
      | .obj (some T) d => objSelfF Γ T (optAgree_some T) (elabDefsF (Γ.cons (.mu T)) d T)
      | .obj none d =>
          objNoneF Γ d (formSelfF Γ d (jobsF .here (d.memberHeads .here) d))
            fun T done => fillDefsF (Γ.cons (.mu T)) done d T
      | .let g ann t u =>
          letF Γ g ann t u (elabF Γ t) (fun G => elabChkF Γ t G)
            (fun T0 => elabF (Γ.cons T0) u) (fun T0 G => elabChkF (Γ.cons T0) u G)
      | .path _ => Fu.ret ([], [.mismatch])
      | .app _ _ => Fu.ret ([], [.mismatch])
      | .proj _ _ => Fu.ret ([], [.mismatch])
termination_by structural p

/-- Checking against a goal.  A term with no empty slot goes to `checkF`.  A
lambda without a domain takes it from the goal's function part. -/
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
            | _ => Fu.bind (lamSynF Γ S (optAgree_some S) (elabF (Γ.cons S) t)) (subsume Γ G)
      | .obj (some T) d =>
          Fu.bind (objSelfF Γ T (optAgree_some T) (elabDefsF (Γ.cons (.mu T)) d T)) (subsume Γ G)
      | .obj none d =>
          Fu.bind (selfGoalF Γ G) fun oT =>
            match oT with
            | some T =>
                orElseW Option.isSome
                  (Fu.bind (objSelfF Γ T rfl (elabDefsF (Γ.cons (.mu T)) d T)) (subsume Γ G))
                  (fun _ => Fu.bind (objNoneF Γ d (formSelfF Γ d (jobsF .here (d.memberHeads .here) d))
                    fun T' done => fillDefsF (Γ.cons (.mu T')) done d T') (subsume Γ G))
            | none =>
                Fu.bind (objNoneF Γ d (formSelfF Γ d (jobsF .here (d.memberHeads .here) d))
                  fun T done => fillDefsF (Γ.cons (.mu T)) done d T) (subsume Γ G)
      | .let g ann t u =>
          letChkF Γ g ann t u G (elabF Γ t) (fun G' => elabChkF Γ t G')
            (fun T0 => elabF (Γ.cons T0) u) (fun T0 G' => elabChkF (Γ.cons T0) u G')
      | .path _ => Fu.ret (none, [.mismatch])
      | .app _ _ => Fu.ret (none, [.mismatch])
      | .proj _ _ => Fu.ret (none, [.mismatch])
termination_by structural p

/-- Definitions against a self type in lockstep, elaborated in the context of
the self.  Definitions with no empty slot are returned as they are, and the
typing of the literal checks them.  A field is checked against its
declaration, so its lambdas take their domains from it.  A written field type
must be the declaration's type.  A field declared stable at `μ(x. U)` holds a
literal with no written field type, and that literal's definitions are
elaborated against `U` with its self at `μ(x. U)`.  A type member has no slot,
so it never reaches the clauses. -/
def elabDefsF {s : Sig} (Γ : Ctx s) (d : PDefs s) (T : Ty s) : Fu (EDefsR Γ d T) :=
  match hd : d.full? with
  | some ad => Fu.ret (some ⟨ad, PDefs.fills_of_full? T hd⟩, [])
  | none =>
      match d, T with
      | .trm a o t, .fld c U =>
          if a = c then
            if ho : optAgree o U = true then
              Fu.bind (elabChkF Γ t U) fun r =>
                Fu.ret (r.1.map fun e => ⟨.trm a e.a, PDefs.fills_trm ho e.fills⟩, r.2)
            else Fu.ret (none, [.mismatch])
          else Fu.ret (none, [.mismatch])
      | .trm a none (.obj oT d'), .vfld c (.mu U) =>
          if a = c then
            if hT : optAgree oT U = true then
              Fu.bind (elabDefsF (Γ.cons (.mu U)) d' U) fun r =>
                Fu.ret (r.1.map fun e =>
                  ⟨.trm a (.obj U e.ds), PDefs.fills_trm_none (PTm.fills_obj hT e.fills)⟩, r.2)
            else Fu.ret (none, [.mismatch])
          else Fu.ret (none, [.mismatch])
      | .and d1 d2, .and T1 T2 =>
          Fu.bind (elabDefsF Γ d1 T1) fun r1 =>
            match r1.1 with
            | some e1 =>
                Fu.bind (elabDefsF Γ d2 T2) fun r2 =>
                  Fu.ret (r2.1.map fun (e2 : EDefs Γ d2 T2) =>
                    ⟨.and e1.ds e2.ds, PDefs.fills_and e1.fills e2.fills⟩, r2.2)
            | none => Fu.ret (none, r1.2)
      | _, _ => Fu.ret (none, [.mismatch])
termination_by structural d

/-- The jobs of a definition list with the self `v`: every field without a
written type and not known at once, in source order.  Each carries its
dependencies, read with the heads `ms` of the type members of the literal, and
its synthesis by `elabF`. -/
def jobsF {s : Sig} (v : BVar s .var) (ms : List (Label × List Label)) : PDefs s → List (Job s)
  | .typ _ _ => []
  | .trm _ (some _) _ => []
  | .trm a none t =>
      match t.atOnce v a with
      | some _ => []
      | none => [⟨a, t, t.deps ms [v], fun Γ => elabF Γ t⟩]
  | .and d1 d2 => jobsF v ms d1 ++ jobsF v ms d2
termination_by structural d => d

/-- The definitions of a literal filled at its formed self type `T`, in the
context that binds the self at `μ(x. T)`.  A field the rounds typed holds the
first typed job at its label.  The self as a whole right-hand side, or any
other right-hand side with no empty slot, stays as it is.  A literal with a
written self type `T'` has its definitions elaborated against `T'`.  A field
with a written type has its right-hand side elaborated against that type.  A
type member stays as it is. -/
def fillDefsF {s : Sig} (Γ : Ctx s) (done : List (Done s)) (d : PDefs s) (T : Ty s) :
    Fu (EFillR d T) :=
  match d with
  | .typ A S => Fu.ret (some ⟨.typ A S, PDefs.fills_typ A S T⟩, [])
  | .trm a none (.obj (some T') d') =>
      Fu.bind (elabDefsF (Γ.cons (.mu T')) d' T') fun r =>
        Fu.ret (r.1.map fun e =>
          ⟨.trm a (.obj T' e.ds), PDefs.fills_trm_none (PTm.fills_obj (optAgree_some T') e.fills)⟩,
          r.2)
  | .trm a none t =>
      match lookupDone done a with
      | some e =>
          if h : t.fills e.a = true then Fu.ret (some ⟨.trm a e.a, PDefs.fills_trm_none h⟩, [])
          else Fu.ret (none, [.mismatch])
      | none =>
          match ht : t.full? with
          | some b => Fu.ret (some ⟨.trm a b, PDefs.fills_trm_none (PTm.fills_of_full? ht)⟩, [])
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
index, as the lookup does (`lookV_agree`).  So the forms that start the index
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
  | .sel q A => by
    refine bind_agree (Agree.refl (declsF_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact uppersPart_agree hr _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .typ _ _ _ => ret_agree _
  | .fld _ _ => ret_agree _
  | .vfld _ _ => ret_agree _
  | .sngl _ => ret_agree _
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
  | .sel q A => by
    simp only [dealiasTy]
    refine bind_agree (Agree.refl (declsF_framed _ _ _)) fun ms => ?_
    split
    · exact hr _
    · exact ret_agree _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .typ _ _ _ => ret_agree _
  | .fld _ _ => ret_agree _
  | .vfld _ _ => ret_agree _
  | .sngl _ => ret_agree _
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

theorem lamSynF_framed {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (ho : optAgree o S = true) {syn : Fu (ESynth (Γ.cons S) t)} (hsyn : Framed syn) :
    Framed (lamSynF Γ S ho syn) :=
  dite_framed (fun _ => bind_framed hsyn fun _ => ret_framed _) (fun _ => ret_framed _)

theorem lamGoalF_framed {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (V : Ty (s,x)) (G : Ty s) (ho : optAgree o S = true) {chk : Fu (ECheck (Γ.cons S) t V)}
    {syn : Unit → Fu (ESynth (Γ.cons S) t)} (hchk : Framed chk) (hsyn : Framed (syn ())) :
    Framed (lamGoalF Γ S V G ho chk syn) := by
  refine dite_framed (fun hwf => ?_) (fun _ => ret_framed _)
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
  dite_framed (fun _ => bind_framed (firstSomeR_framed (fun c1 => bind_framed (hchk c1) fun _ =>
    ret_framed _) _) fun _ => ret_framed _) (fun _ => ret_framed _)

theorem letNoneR_framed {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)}
    (r1 : ESynth Γ t) {syn : (c1 : ECand Γ t) → Fu (ESynth (Γ.cons c1.ty) u)}
    (hsyn : ∀ c1, Framed (syn c1)) : Framed (letNoneR (g := g) Γ r1 syn) :=
  bind_framed (flatMapR_framed (fun c1 => bind_framed (hsyn c1) fun _ =>
      bind_framed (flatMapR_framed (fun _ => bind_framed (letAvoidC_framed _ _) fun _ =>
        ret_framed _) _) fun _ => ret_framed _) _) fun _ => ret_framed _

theorem blockR_framed {s : Sig} (Γ : Ctx s) {g : LetTag} {t : PTm s} {u : PTm (s,x)} (G : Ty s)
    (r1 : ESynth Γ t) {chk : (c1 : ECand Γ t) → Fu (ECheck (Γ.cons c1.ty) u G.weaken)}
    (hchk : ∀ c1, Framed (chk c1)) : Framed (blockR (g := g) Γ G r1 chk) :=
  dite_framed (fun _ => bind_framed (firstSomeR_framed (fun c1 => bind_framed (hchk c1) fun _ =>
    ret_framed _) _) fun _ => ret_framed _) (fun _ => ret_framed _)

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

/-- A field without a written type whose right-hand side is no literal with a
written self type fills without a call. -/
theorem fillDefsF_trm_framed {s : Sig} (Γ : Ctx s) (done : List (Done s)) {a : Label}
    {t : PTm s} {T : Ty s} (ht : ∀ T' d', t = .obj (some T') d' → False) :
    Framed (fillDefsF Γ done (.trm a none t) T) := by
  rw [fillDefsF]
  · repeat' (first | exact ret_framed _ | split)
  · exact ht

/-- A field definition is framed when the check of its right-hand side is,
and, for a literal, the elaboration of the literal's definitions. -/
theorem elabDefsF_trm_framed {s : Sig} (Γ : Ctx s) {a : Label} {o : Option (Ty s)} {t : PTm s}
    {T : Ty s} (hc : ∀ U, Framed (elabChkF Γ t U))
    (hd : ∀ oT d', t = .obj oT d' → ∀ U, Framed (elabDefsF (Γ.cons (.mu U)) d' U)) :
    Framed (elabDefsF Γ (.trm a o t) T) := by
  rw [elabDefsF]
  split
  · exact ret_framed _
  · cases T with
    | fld c U =>
      refine ite_framed (dite_framed (fun _ => ?_) (fun _ => ret_framed _)) (ret_framed _)
      exact bind_framed (hc U) fun _ => ret_framed _
    | vfld c V =>
      cases o with
      | none =>
        cases t <;> cases V <;> first
          | exact ret_framed _
          | exact ite_framed (dite_framed (fun _ => bind_framed (hd _ _ rfl _) fun _ =>
              ret_framed _) (fun _ => ret_framed _)) (ret_framed _)
      | some _ => cases t <;> cases V <;> exact ret_framed _
    | _ => exact ret_framed _

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
    · exact lamSynF_framed _ _ _ (elabF_framed _ t)
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
    · exact objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed _ _ d))
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
      · exact bind_framed (lamSynF_framed _ _ _ (elabF_framed _ t)) fun _ => subsume_framed _ _ _
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
      cases oT with
      | some T =>
        exact orElseW_framed
          (bind_framed (objSelfF_framed _ _ _ (elabDefsF_framed _ d T)) fun _ => subsume_framed _ _ _)
          (bind_framed (objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed _ _ d))
            fun T' done => fillDefsF_framed _ done d T') fun _ => subsume_framed _ _ _)
      | none =>
        exact bind_framed (objNoneF_framed _ _ (formSelfF_framed _ _ (jobsF_framed _ _ d))
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
    rw [elabDefsF]
    split
    · exact ret_framed _
    · exact ret_framed _
  | .trm a o (.obj oT d'), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.obj oT d') U)
      fun _ _ h U => (PTm.obj.inj h).2 ▸ elabDefsF_framed _ d' U
  | .trm a o (.path y), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.path y) U) fun _ _ h => by cases h
  | .trm a o (.lam o' t), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.lam o' t) U) fun _ _ h => by cases h
  | .trm a o (.app y z), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.app y z) U) fun _ _ h => by cases h
  | .trm a o (.proj y b), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.proj y b) U) fun _ _ h => by cases h
  | .trm a o (.let g o' t u), T =>
    elabDefsF_trm_framed Γ (fun U => elabChkF_framed _ (.let g o' t u) U) fun _ _ h => by cases h
  | .and d1 d2, T => by
    rw [elabDefsF]
    split
    · exact ret_framed _
    · cases T with
      | and T1 T2 =>
        refine bind_framed (elabDefsF_framed _ d1 T1) fun r1 => ?_
        split
        · exact bind_framed (elabDefsF_framed _ d2 T2) fun _ => ret_framed _
        · exact ret_framed _
      | _ => exact ret_framed _

/-- The jobs of a definition list run framed syntheses. -/
theorem jobsF_framed {s : Sig} (v : BVar s .var) (ms : List (Label × List Label)) :
    (d : PDefs s) → ∀ j ∈ jobsF v ms d, ∀ Γ, Framed (j.run Γ)
  | .typ _ _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm _ (some _) _ => by
    intro j hj
    simp only [jobsF, List.not_mem_nil] at hj
  | .trm a none t => by
    intro j hj Γ
    rw [jobsF] at hj
    split at hj
    · simp only [List.not_mem_nil] at hj
    · simp only [List.mem_singleton] at hj
      subst hj
      exact elabF_framed Γ t
  | .and d1 d2 => by
    intro j hj Γ
    simp only [jobsF, List.mem_append] at hj
    rcases hj with h | h
    · exact jobsF_framed v ms d1 j h Γ
    · exact jobsF_framed v ms d2 j h Γ

/-- Filling definitions is framed. -/
theorem fillDefsF_framed {s : Sig} (Γ : Ctx s) (done : List (Done s)) :
    (d : PDefs s) → (T : Ty s) → Framed (fillDefsF Γ done d T)
  | .typ A S, T => by
    rw [fillDefsF]
    exact ret_framed _
  | .trm a none (.obj (some T') d'), T => by
    rw [fillDefsF]
    exact bind_framed (elabDefsF_framed _ d' T') fun _ => ret_framed _
  | .trm a none (.obj none d'), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
  | .trm a none (.path y), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
  | .trm a none (.lam o t), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
  | .trm a none (.app y z), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
  | .trm a none (.proj y b), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
  | .trm a none (.let g o t u), T => fillDefsF_trm_framed Γ done (by intro _ _ h; cases h)
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
  unfold lamGoalF
  split
  · refine yields_orElseW (yields_bind fun r => ?_) (yields_bind fun r => ?_)
    · split
      · exact yields_toGoal (Q := fun a => ∃ b, a = .lam S b) _ _ _ ⟨_, rfl⟩
      · exact yields_ret_none _
    · refine yields_subsume (Q := fun a => ∃ b, a = .lam S b) _ _ _ fun c hc => ?_
      simp only [lamCands, List.mem_map] at hc
      obtain ⟨c', _, rfl⟩ := hc
      exact ⟨_, rfl⟩
  · exact yields_ret_none _

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
`checkF` on the lambda filled with the part's domain. -/
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
theorem fullSelf_lockstep {s : Sig} {v : BVar s .var} {known : List (Label × Ty s)} :
    ∀ {d : PDefs s} {T : Ty s}, d.fullSelf v known = some T → Lockstep v known d T
  | .typ A S, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .typ A S
  | .trm a (some U) t, _, h => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    exact .written a U t
  | .trm a none t, _, h => by
    simp only [PDefs.fullSelf] at h
    cases ho : t.atOnce v a with
    | some D =>
      simp only [ho, Option.some.injEq] at h
      subst h
      exact .atOnce a t D ho
    | none =>
      simp only [ho, Option.map_eq_some_iff] at h
      obtain ⟨U, hU, rfl⟩ := h
      exact .inferred a U t ho hU
  | .and d e, _, h => by
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf v known with
    | none => simp only [h1, reduceCtorEq] at h
    | some T1 =>
      cases h2 : e.fullSelf v known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some T2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact .and (fullSelf_lockstep h1) (fullSelf_lockstep h2)

/-- A definition list whose fields all have a written type has no job, so a
literal with a written type on every field needs no round. -/
theorem jobsF_written {s : Sig} {v : BVar s .var} {ms : List (Label × List Label)} :
    ∀ {d : PDefs s}, d.AllFieldsWritten → jobsF v ms d = []
  | .typ _ _, _ => by simp only [jobsF]
  | .trm _ (some _) _, _ => by simp only [jobsF]
  | .trm _ none _, hw => by simp [PDefs.AllFieldsWritten] at hw
  | .and d e, hw => by
    simp only [PDefs.AllFieldsWritten] at hw
    simp only [jobsF, jobsF_written hw.1, jobsF_written hw.2, List.append_nil]

/-- A field found at a label is among the labels. -/
theorem PDefs.mem_labels_of_lookupTrm {s : Sig} {a : Label} :
    ∀ {d : PDefs s} {t : PTm s}, d.lookupTrm a = some t → a ∈ d.labels
  | .typ _ _, _, h => by simp [PDefs.lookupTrm] at h
  | .trm b _ _, _, h => by
    simp only [PDefs.lookupTrm] at h
    split at h
    · rename_i hab
      simp [PDefs.labels, hab]
    · cases h
  | .and d e, _, h => by
    simp only [PDefs.lookupTrm] at h
    cases he : e.lookupTrm a with
    | some t' => exact List.mem_append_right _ (PDefs.mem_labels_of_lookupTrm he)
    | none =>
      simp only [he, Option.none_or] at h
      exact List.mem_append_left _ (PDefs.mem_labels_of_lookupTrm h)

/-- No field is found at a label that is not among the labels. -/
theorem PDefs.lookupTrm_none {s : Sig} {d : PDefs s} {a : Label} (h : a ∉ d.labels) :
    d.lookupTrm a = none := by
  cases ht : d.lookupTrm a with
  | none => rfl
  | some t => exact absurd (PDefs.mem_labels_of_lookupTrm ht) h

/-- A declaration known at once is a field at the singleton of the self, or a
stable field at the `μ` of the written self type of the literal the field
holds. -/
theorem atOnce_shape {s : Sig} {v : BVar s .var} {b : Label} {t : PTm s} {D : Ty s}
    (h : t.atOnce v b = some D) :
    D = .fld b (.sngl (.var v)) ∨ ∃ T' d', t = .obj (some T') d' ∧ D = .vfld b (.mu T') := by
  cases t with
  | path y =>
    simp only [PTm.atOnce] at h
    split at h
    · rename_i hy
      subst hy
      simp only [Option.some.injEq] at h
      exact .inl h.symm
    · cases h
  | obj o d' =>
    cases o with
    | some T' =>
      simp only [PTm.atOnce, Option.some.injEq] at h
      exact .inr ⟨T', d', rfl, h.symm⟩
    | none => simp [PTm.atOnce] at h
  | lam _ _ => simp [PTm.atOnce] at h
  | app _ _ => simp [PTm.atOnce] at h
  | proj _ _ => simp [PTm.atOnce] at h
  | «let» _ _ _ _ => simp [PTm.atOnce] at h

/-- The declaration of a typed field is a plain field at its type, or a stable
field at the `μ` type of the literal the field holds. -/
theorem declOf_shape {s : Sig} (b : Label) (t : PTm s) (U : Ty s) :
    declOf b t U = .fld b U ∨
      ∃ o d' T', t = .obj o d' ∧ U = .mu T' ∧ declOf b t U = .vfld b (.mu T') := by
  cases t with
  | obj o d' =>
    cases U with
    | mu T' => exact .inr ⟨o, d', T', rfl, rfl, rfl⟩
    | _ => exact .inl rfl
  | _ => exact .inl rfl

/-- A field without a written type that the formed self type declares stable
holds a literal, and its declaration is a `μ`. -/
theorem trmSelf_vfld {s : Sig} {v : BVar s .var} {known : List (Label × Ty s)} {b : Label}
    {t : PTm s} {T : Ty s} (h : (PDefs.trm b none t).fullSelf v known = some T) {a : Label}
    {U : Ty s} (hl : T.lookupVfldDecl a = some U) :
    ∃ o d' T', (PDefs.trm b none t).lookupTrm a = some (.obj o d') ∧ U = .mu T' := by
  simp only [PDefs.fullSelf] at h
  cases ho : t.atOnce v b with
  | some D =>
    simp only [ho, Option.some.injEq] at h
    subst h
    rcases atOnce_shape ho with rfl | ⟨T', d', rfl, rfl⟩
    · simp [Ty.lookupVfldDecl] at hl
    · simp only [Ty.lookupVfldDecl] at hl
      split at hl
      · rename_i hab
        simp only [Option.some.injEq] at hl
        exact ⟨some T', d', T', by simp [PDefs.lookupTrm, hab], hl.symm⟩
      · cases hl
  | none =>
    simp only [ho, Option.map_eq_some_iff] at h
    obtain ⟨U0, _, rfl⟩ := h
    rcases declOf_shape b t U0 with hd | ⟨o, d', T', rfl, rfl, hd⟩
    · rw [hd] at hl
      simp [Ty.lookupVfldDecl] at hl
    · rw [hd] at hl
      simp only [Ty.lookupVfldDecl] at hl
      split at hl
      · rename_i hab
        simp only [Option.some.injEq] at hl
        exact ⟨o, d', T', by simp [PDefs.lookupTrm, hab], hl.symm⟩
      · cases hl

/-- A stable field of the formed self type holds a literal in the definitions,
the field the version's `DefsTy.trmObj` asks for, and its declaration is a
`μ`.  The labels must be distinct, as `HasTy.obj` asks, since a later field of
the same label would shadow the literal. -/
theorem fullSelf_vfld {s : Sig} {v : BVar s .var} {known : List (Label × Ty s)} :
    ∀ {d : PDefs s} {T : Ty s}, d.fullSelf v known = some T → d.Distinct →
      ∀ {a : Label} {U : Ty s}, T.lookupVfldDecl a = some U →
        ∃ o d' T', d.lookupTrm a = some (.obj o d') ∧ U = .mu T'
  | .typ A S, _, h, _, a, U, hl => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    simp [Ty.lookupVfldDecl] at hl
  | .trm b (some W) t, _, h, _, a, U, hl => by
    simp only [PDefs.fullSelf, Option.some.injEq] at h
    subst h
    simp [Ty.lookupVfldDecl] at hl
  | .trm b none t, _, h, _, a, U, hl => trmSelf_vfld h hl
  | .and d e, _, h, hd, a, U, hl => by
    simp only [PDefs.fullSelf] at h
    cases h1 : d.fullSelf v known with
    | none => simp only [h1, reduceCtorEq] at h
    | some T1 =>
      cases h2 : e.fullSelf v known with
      | none => simp only [h1, h2, reduceCtorEq] at h
      | some T2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        cases hd with
        | and hd1 hd2 hdis =>
          simp only [Ty.lookupVfldDecl] at hl
          cases hl2 : T2.lookupVfldDecl a with
          | some U2 =>
            simp only [hl2, Option.some_or, Option.some.injEq] at hl
            subst hl
            obtain ⟨o, d', T', he, hU⟩ := fullSelf_vfld h2 hd2 hl2
            exact ⟨o, d', T', by simp [PDefs.lookupTrm, he], hU⟩
          | none =>
            simp only [hl2, Option.none_or] at hl
            obtain ⟨o, d', T', hdl, hU⟩ := fullSelf_vfld h1 hd1 hl
            have hne : e.lookupTrm a = none :=
              PDefs.lookupTrm_none (hdis a (PDefs.mem_labels_of_lookupTrm hdl))
            exact ⟨o, d', T', by simp [PDefs.lookupTrm, hne, hdl], hU⟩

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

theorem walkL_snoc {s : Sig} {js : List (Job s)} {l l' : Label} (hn : nextL js l = some l') :
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

theorem nextL_mem {s : Sig} {js : List (Job s)} {l l' : Label} (h : nextL js l = some l') :
    l' ∈ js.map (·.lbl) := by
  unfold nextL at h
  split at h
  · rename_i j _
    have hm : l' ∈ waitsFor js j := List.mem_of_mem_head? h
    simp only [waitsFor, List.mem_filter] at hm
    exact List.contains_iff_mem.mp hm.2
  · cases h

theorem cycleFrom_onCycle {s : Sig} {js : List (Job s)} :
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
theorem cycleAt_onCycle {s : Sig} {js : List (Job s)} {n : Nat} {l : Label}
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
      objNoneF Γ d (formSelfF Γ d (jobsF .here (d.memberHeads .here) d))
        fun T done => fillDefsF (Γ.cons (.mu T)) done d T := by
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
    ∃ T done d' tk', (formSelfF Γ d (jobsF .here (d.memberHeads .here) d) tk).1 = .ok (T, done) ∧
      ∃ hc : c.a = .obj T d',
        (⟨c.ty, hc ▸ c.deriv⟩ : Cand Γ (ATm.obj T d').erase) ∈ (synthF Γ (.obj T d') tk').1 := by
  rw [elabF_obj_none] at h
  unfold objNoneF at h
  cases hf : formSelfF Γ d (jobsF .here (d.memberHeads .here) d) tk with
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

Each check elaborates a program at `defaultFuel` in the kernel.  It states the
elaborated term and its type, or the reason, and the tank left.  A program with
an empty slot that compiles is compared with the program that writes the slot:
the elaborated term is the term that program resolves to, and the type is the
one `synthF` gives it.  An unmarked tank means the fuel played no part in the
verdict. -/

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

/-- The outcome of a resolved program, elaborated, with the tank left. -/
def elabOf (o : Option (PTm [])) (n : Nat := defaultFuel) : Outcome × Tank :=
  match o with
  | some p =>
      match elabTopF n p with
      | (.ok c, t) => (.ok c.a c.ty, t)
      | (.error r, t) => (.no r, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- The outcome of a surface program, resolved and elaborated, with the tank
left. -/
def elabAt (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  elabOf (resolveP pathsTable e) n

/-- The outcome of a surface program with every lambda domain erased. -/
def elabAtD (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  elabOf ((resolveP pathsTable e).map PTm.eraseDoms) n

/-- What `synthF` gives a surface program with every slot written: the term it
resolves to and its first type. -/
def writtenAt (e : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  match resolve pathsTable e with
  | some a =>
      match synthTopF n a with
      | (some c, t) => (.ok a c.ty, t)
      | (none, t) => (.no .mismatch, t)
  | none => (.no .mismatch, ⟨n, true⟩)

/-- K3 with the domain its dominant formal gives, `{a : ⊤}`.  Scala infers
that domain for K3. -/
def K3d_src : STm :=
  pdot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤)). g (λ(x : {a : ⊤}). x)

/-- A written type that is an alias reached through a stable field. -/
def AL_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}). let f : m.c.A = λ(x : ⊤). x in f

/-- The same with the inner domain erased.  The alias is followed. -/
def AL_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}). let f : m.c.A = λx. x in f

/-- An alias of an alias: `m.c.B` stands for `z.A` of the same literal. -/
def AA_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤} ∧ {B : z.A .. z.A})}).
    let f : m.c.B = λ(x : ⊤). x in f

/-- The same with the inner domain erased.  Both aliases are followed. -/
def AA_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤} ∧ {B : z.A .. z.A})}).
    let f : m.c.B = λx. x in f

/-- An intersection of two aliases of one function type. -/
def AI_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤} ∧ {B : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}).
    let f : m.c.A ∧ m.c.B = λ(x : ⊤). x in f

/-- The same with the inner domain erased.  Each side is dealiased. -/
def AI_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤} ∧ {B : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}).
    let f : m.c.A ∧ m.c.B = λx. x in f

/-- A function side beside an alias of a function type with a larger domain. -/
def AIm_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}).
    let f : (∀(x : {a : ⊤}) ⊤) ∧ m.c.A = λ(x : ⊤). x in f

/-- The same with the inner domain erased.  The domains meet at `⊤`. -/
def AIm_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤})}).
    let f : (∀(x : {a : ⊤}) ⊤) ∧ m.c.A = λx. x in f

/-- Two function sides of one domain. -/
def AS_src : STm :=
  pdot% let f : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) = λ(x : {a : ⊤}). x in f

/-- The same with the domain erased. -/
def AS_srcD : STm :=
  pdot% let f : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) = λx. x in f

/-- A written type whose second side is a selection with a function lower
bound.  The written lambda is below it through the lower bound. -/
def X3p_src : STm :=
  pdot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}).
    let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A = λ(x : {a : ⊤}). x in f

/-- The same with the inner domain erased.  The body has no empty slot, so the
lambda filled with `{a : ⊤}` goes to the typer at the written type. -/
def X3p_srcD : STm :=
  pdot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}). let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A = λx. x in f

/-- The ascription `(λ(x : ⊤). x : ∀(z : ⊤) ⊤)`. -/
def Asc_src : STm := pdot% (λ(x : ⊤). x : ∀(z : ⊤) ⊤)

/-- The same with the domain erased. -/
def Asc_srcD : STm := pdot% (λx. x : ∀(z : ⊤) ⊤)

/-- A literal ascribed at a `μ`, its self type written. -/
def AscObj_src : STm := pdot% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- The same with the self type erased.  The `μ` goal gives it. -/
def AscObj_srcS : STm := pdot% λ(n : {b : ⊤}). (ν(z. {a = n}) : μ(z. {a : {b : ⊤}}))

/-- A stable field whose literal has its self type and its lambda's domain
written. -/
def StD_src : STm :=
  pdot% ν(x : {val c : μ(y. {A : ⊤ .. ⊤} ∧ {f : ∀(z : y.A) y.A})}.
          {c = ν(y : {A : ⊤ .. ⊤} ∧ {f : ∀(z : y.A) y.A}. {type A = ⊤} ∧ {f = λ(z : y.A). z})})

/-- The same with the inner self type and the domain erased.  The stable field's
declaration gives the self type, and the self type gives the domain. -/
def StD_srcD : STm :=
  pdot% ν(x : {val c : μ(y. {A : ⊤ .. ⊤} ∧ {f : ∀(z : y.A) y.A})}. {c = ν(y. {type A = ⊤} ∧ {f = λz. z})})

/-- E11 with the self type of its stable field's literal erased. -/
def E11_srcI : STm :=
  pdot% let z = ν(z : {C : ⊤..⊤}. {type C = ⊤}) in
        ν(x : {val a : μ(w. {A : ⊤..⊤})} ∧ {b : z.type}. {a = ν(w. {type A = ⊤})} ∧ {b = z})

/-- A lambda bound with no type. -/
def Id0_srcD : STm := pdot% let i = λx. x in i

/-- A lambda bound at `⊤`. -/
def IdTop_srcD : STm := pdot% let i : ⊤ = λx. x in i

/-- A lambda bound by a written `let` and then passed: no call argument. -/
def LetArg_srcD : STm := pdot% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λx. x in g i

/-- A singleton as the written type. -/
def SG_srcD : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let f : g.type = λx. x in f

/-- An abstract type with a function lower bound only. -/
def Lower_srcD : STm := pdot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). let f : y.A = λx. x in f

/-- A callee whose two formals are incomparable. -/
def Inc_srcA : STm :=
  pdot% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λx. x)

/-- An abstract member with a function upper bound, through a stable field. -/
def AB_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊥ .. ∀(x : ⊤) ⊤})}). let f : m.c.A = λx. x in f

/-- Two function sides with incomparable domains. -/
def AndInc_srcD : STm := pdot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤) = λy. y in f

-- The erased programs are the written ones with those slots erased.
example : (resolveP pathsTable K3d_src).map PTm.eraseArgs = resolveP pathsTable K3_srcA := rfl
example : (resolveP pathsTable AS_src).map PTm.eraseDoms = resolveP pathsTable AS_srcD := rfl
example : (resolveP pathsTable Asc_src).map PTm.eraseDoms = resolveP pathsTable Asc_srcD := rfl
example : (resolveP pathsTable AscObj_src).map PTm.eraseSelf = resolveP pathsTable AscObj_srcS := rfl
example : (resolveP pathsTable StD_src).map (fun p => p.eraseSelf.eraseDoms) =
    (resolveP pathsTable StD_srcD).map (fun p => p.eraseSelf.eraseDoms) := rfl
-- The programs with an inner domain erased differ from the written ones in
-- their domains only.
example : (resolveP pathsTable AL_src).map PTm.eraseDoms =
    (resolveP pathsTable AL_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable AA_src).map PTm.eraseDoms =
    (resolveP pathsTable AA_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable AI_src).map PTm.eraseDoms =
    (resolveP pathsTable AI_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable AIm_src).map PTm.eraseDoms =
    (resolveP pathsTable AIm_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable X3p_src).map PTm.eraseDoms =
    (resolveP pathsTable X3p_srcD).map PTm.eraseDoms := rfl

-- Every slot written: the typer's verdict, term, type and tank.
example : elabAt E2_src = writtenAt E2_src := by decide +kernel
example : elabAt Fig1_src = writtenAt Fig1_src := by decide +kernel

-- The domains of call arguments erased: the written terms, at more fuel.  K1s
-- fills a singleton, K1p a selection through a stable field, K2 the one
-- formal of two equal ones.
example : elabAt K1s_srcA = ((writtenAt K1s_src).1, ⟨defaultFuel - 15, false⟩) ∧
    writtenAt K1s_src = ((writtenAt K1s_src).1, ⟨defaultFuel - 11, false⟩) ∧
    (writtenAt K1s_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt K1p_srcA = ((writtenAt K1p_src).1, ⟨defaultFuel - 19, false⟩) ∧
    (writtenAt K1p_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt K2_srcA = ((writtenAt K2_src).1, ⟨defaultFuel - 27, false⟩) ∧
    (writtenAt K2_src).1.ty?.isSome = true := by
  decide +kernel

-- K3: the formal `∀(x : {a : ⊤}) ⊤` is dominant, so the domain is `{a : ⊤}`
--.
example : elabAt K3_srcA = ((writtenAt K3d_src).1, ⟨defaultFuel - 37, false⟩) ∧
    (writtenAt K3d_src).1.ty?.isSome = true := by
  decide +kernel

-- Domains from written types and ascriptions: aliases through stable fields,
-- followed to a fixpoint and inside each side of an intersection, comparable
-- and equal domains meeting.
example : elabAt AL_srcD = ((writtenAt AL_src).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenAt AL_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AA_srcD = ((writtenAt AA_src).1, ⟨defaultFuel - 47, false⟩) ∧
    (writtenAt AA_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AI_srcD = ((writtenAt AI_src).1, ⟨defaultFuel - 53, false⟩) ∧
    (writtenAt AI_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AIm_srcD = ((writtenAt AIm_src).1, ⟨defaultFuel - 25, false⟩) ∧
    (writtenAt AIm_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt AS_srcD = ((writtenAt AS_src).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenAt AS_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt X3p_srcD = ((writtenAt X3p_src).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt X3p_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt Asc_srcD = ((writtenAt Asc_src).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenAt Asc_src).1.ty? = some (.all .top .top) := by
  decide +kernel

-- Every domain erased in programs whose lambdas are fields of literals with
-- written self types: the written terms and types.
example : elabAtD E2_src = ((writtenAt E2_src).1, ⟨defaultFuel - 59, false⟩) ∧
    (writtenAt E2_src).1.ty? = some E2_avoided := by
  decide +kernel
example : elabAtD E2p_src = ((writtenAt E2p_src).1, ⟨defaultFuel - 72, false⟩) ∧
    (writtenAt E2p_src).1.ty? = some E2_avoided := by
  decide +kernel
example : elabAtD Fig1_src = ((writtenAt Fig1_src).1, ⟨defaultFuel - 482, false⟩) ∧
    (writtenAt Fig1_src).1.ty? = some Fig1_ty := by
  decide +kernel
example : elabAtD Fig2_src = ((writtenAt Fig2_src).1, ⟨defaultFuel - 482, false⟩) ∧
    (writtenAt Fig2_src).1.ty? = some Fig2_avoided := by
  decide +kernel

-- Literals without a self type at a goal that gives one: a `μ` ascription, and
-- the declaration of a stable field.
example : elabAt AscObj_srcS = ((writtenAt AscObj_src).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenAt AscObj_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt StD_srcD = ((writtenAt StD_src).1, ⟨defaultFuel - 2, false⟩) ∧
    (writtenAt StD_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt E11_srcI = ((writtenAt E11_src).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenAt E11_src).1.ty? = some E11_avoided := by
  decide +kernel

-- Missing parameter type: no goal, a goal with no function part, a singleton
-- goal, a callee with no dominant formal, a lambda bound by a written `let`.
example : elabAt Id0_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt IdTop_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt SG_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt Lower_srcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabAt Inc_srcA = (.no (.missingParamType none), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : elabAt LetArg_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Mismatch: an abstract member with a function upper bound, incomparable
-- domains.
example : elabAt AB_srcD = (.no .mismatch, ⟨defaultFuel - 4, false⟩) := by decide +kernel
example : elabAt AndInc_srcD = (.no .mismatch, ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-! ### The callee's body

A lambda `λx. g x` with no goal, or with a goal that has no function part,
takes the dominant formal of `g`.  The lookup finds the function types of `g`
through aliases, upper bounds and stable fields.  Scala compiles each program
below that compiles here, with `g` a function value. -/

/-- A lambda bound with no type whose body applies `g` to the parameter, the
domain written. -/
def Callee_src : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  It is the domain of `g`. -/
def Callee_srcD : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let h = λx. g x in h

/-- The same with `g` bound by a `let`, so the program is closed. -/
def CalleeLet_src : STm := pdot% let g = λ(y : ⊤). y in let h = λ(x : ⊤). g x in h

/-- The same with the domain of `h` erased. -/
def CalleeLet_srcD : STm := pdot% let g = λ(y : ⊤). y in let h = λx. g x in h

/-- A callee at an intersection of two function types with comparable domains,
the larger domain written. -/
def CalleeAnd_src : STm :=
  pdot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The dominant formal is `⊤`. -/
def CalleeAnd_srcD : STm := pdot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). let h = λx. g x in h

/-- A callee at an alias reached through a stable field, the domain written. -/
def CalleeAlias_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : {a : ⊤}) ⊤ .. ∀(x : {a : ⊤}) ⊤})}). λ(g : m.c.A).
    let h = λ(x : {a : ⊤}). g x in h

/-- The same with the domain erased.  The lookup follows the alias. -/
def CalleeAlias_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ∀(x : {a : ⊤}) ⊤ .. ∀(x : {a : ⊤}) ⊤})}). λ(g : m.c.A).
    let h = λx. g x in h

/-- A callee at an abstract member with a function upper bound, the domain
written. -/
def CalleeAbs_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊥ .. ∀(x : ⊤) ⊤})}). λ(g : m.c.A). let h = λ(x : ⊤). g x in h

/-- The same with the domain erased.  The lookup reads the upper bound. -/
def CalleeAbs_srcD : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊥ .. ∀(x : ⊤) ⊤})}). λ(g : m.c.A). let h = λx. g x in h

/-- A callee whose formal is a singleton, the domain written. -/
def CalleeDep_src : STm := pdot% λ(y : ⊤). λ(g : ∀(x : y.type) ⊤). let h = λ(x : y.type). g x in h

/-- The same with the domain erased.  It is the singleton `y.type`. -/
def CalleeDep_srcD : STm := pdot% λ(y : ⊤). λ(g : ∀(x : y.type) ⊤). let h = λx. g x in h

/-- A callee read off the self of a literal with a written self type, the
domain written. -/
def CalleeField_src : STm :=
  pdot% ν(o : {f : ∀(x : ⊤) ⊤} ∧ {b : ∀(x : ⊤) ⊤}.
    {f = λ(x : ⊤). x} ∧ {b = λ(x : ⊤). let k = o.f in let h = λ(y : ⊤). k y in h x})

/-- The same with the domain of `h` erased. -/
def CalleeField_srcD : STm :=
  pdot% ν(o : {f : ∀(x : ⊤) ⊤} ∧ {b : ∀(x : ⊤) ⊤}.
    {f = λ(x : ⊤). x} ∧ {b = λ(x : ⊤). let k = o.f in let h = λy. k y in h x})

/-- A goal with no function part, the domain written. -/
def CalleeTopGoal_src : STm :=
  pdot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ⊤ = λ(x : {a : ⊤}). g x in h

/-- The same with the domain erased.  It is the domain of `g`. -/
def CalleeTopGoal_srcD : STm := pdot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ⊤ = λx. g x in h

/-- An abstract goal with a function lower bound only, the domain written. -/
def CalleeLower_src : STm :=
  pdot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). λ(g : ∀(x : ⊤) ⊤). let f : y.A = λ(x : ⊤). g x in f

/-- The same with the domain erased.  The goal has no function part, so the
callee gives the domain, and the lambda is below the goal by its lower
bound. -/
def CalleeLower_srcD : STm :=
  pdot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). λ(g : ∀(x : ⊤) ⊤). let f : y.A = λx. g x in f

/-- A goal with a function part whose domain is below the domain of `g`, the
domain written. -/
def CalleeFunGoal_src : STm :=
  pdot% λ(g : ∀(x : {a : ⊤}) ⊤).
    let h : ∀(x : {a : ⊤} ∧ {b : ⊤}) ⊤ = λ(x : {a : ⊤} ∧ {b : ⊤}). g x in h

/-- The same with the domain erased.  The goal gives it, not the callee. -/
def CalleeFunGoal_srcD : STm :=
  pdot% λ(g : ∀(x : {a : ⊤}) ⊤). let h : ∀(x : {a : ⊤} ∧ {b : ⊤}) ⊤ = λx. g x in h

/-- A call argument whose formal is `⊤`, the domain written. -/
def CalleeArg_src : STm := pdot% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (λ(x : ⊤). g x)

/-- The same with the domain erased.  The formal has no function part, so the
callee gives it. -/
def CalleeArg_srcA : STm := pdot% λ(f : ∀(h : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (λx. g x)

/-- A callee at an intersection of two function types with incomparable
domains.  Scala takes their union, which the version lacks. -/
def CalleeInc_srcD : STm :=
  pdot% λ(g : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤)). let h = λx. g x in h

/-- A callee with no function type. -/
def CalleeTop_srcD : STm := pdot% λ(g : ⊤). let h = λx. g x in h

/-- A callee at the singleton of a function, the domain written.  The typer
finds no function type for `g` and rejects it. -/
def CalleeSngl_src : STm :=
  pdot% λ(f : ∀(x : {a : ⊤}) ⊤). λ(g : f.type). let h = λ(x : {a : ⊤}). g x in h

/-- The same with the domain erased.  The lookup finds no formal either. -/
def CalleeSngl_srcD : STm :=
  pdot% λ(f : ∀(x : {a : ⊤}) ⊤). λ(g : f.type). let h = λx. g x in h

/-- A body whose argument is not the parameter. -/
def CalleeOther_srcD : STm := pdot% λ(g : ∀(x : ⊤) ⊤). λ(y : ⊤). let h = λx. g y in h

/-- A body that applies the parameter to itself. -/
def CalleeSelf_srcD : STm := pdot% let h = λx. x x in h

/-- A body that applies a projection to the parameter.  The resolver binds the
projection first, so the body is a `let` and not `g x`. -/
def CalleeProj_srcD : STm := pdot% λ(o : {a : ∀(x : ⊤) ⊤}). let h = λx. o.a x in h

/-- A block body. -/
def CalleeBlock_srcD : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let h = λx. (let z = g x in z) in h

/-- A singleton goal.  The callee gives the domain, and the lambda is not of
the singleton type. -/
def CalleeSnglGoal_srcD : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let f : g.type = λx. g x in f

-- The erased programs differ from the written ones in their domains only, and
-- the erased call argument is the written one with the argument's domain erased.
example : (resolveP pathsTable Callee_src).map PTm.eraseDoms =
    (resolveP pathsTable Callee_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable CalleeAlias_src).map PTm.eraseDoms =
    (resolveP pathsTable CalleeAlias_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable CalleeField_src).map PTm.eraseDoms =
    (resolveP pathsTable CalleeField_srcD).map PTm.eraseDoms := rfl
example : (resolveP pathsTable CalleeArg_src).map PTm.eraseArgs = resolveP pathsTable CalleeArg_srcA :=
  rfl

-- The domain of the callee: the written terms, at more fuel.
example : elabAt Callee_srcD = ((writtenAt Callee_src).1, ⟨defaultFuel - 4, false⟩) ∧
    writtenAt Callee_src = ((writtenAt Callee_src).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenAt Callee_src).1.ty? = some (.all (.all .top .top) (.all .top .top)) := by
  decide +kernel
example : elabAt CalleeLet_srcD = ((writtenAt CalleeLet_src).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenAt CalleeLet_src).1.ty? = some (.all .top .top) := by
  decide +kernel
example : elabAt CalleeAnd_srcD = ((writtenAt CalleeAnd_src).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt CalleeAnd_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeAlias_srcD = ((writtenAt CalleeAlias_src).1, ⟨defaultFuel - 22, false⟩) ∧
    (writtenAt CalleeAlias_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeAbs_srcD = ((writtenAt CalleeAbs_src).1, ⟨defaultFuel - 22, false⟩) ∧
    (writtenAt CalleeAbs_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeDep_srcD = ((writtenAt CalleeDep_src).1, ⟨defaultFuel - 4, false⟩) ∧
    (writtenAt CalleeDep_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeField_srcD = ((writtenAt CalleeField_src).1, ⟨defaultFuel - 30, false⟩) ∧
    (writtenAt CalleeField_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeTopGoal_srcD = ((writtenAt CalleeTopGoal_src).1, ⟨defaultFuel - 5, false⟩) ∧
    (writtenAt CalleeTopGoal_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeLower_srcD = ((writtenAt CalleeLower_src).1, ⟨defaultFuel - 9, false⟩) ∧
    (writtenAt CalleeLower_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeFunGoal_srcD = ((writtenAt CalleeFunGoal_src).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenAt CalleeFunGoal_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAt CalleeArg_srcA = ((writtenAt CalleeArg_src).1, ⟨defaultFuel - 12, false⟩) ∧
    (writtenAt CalleeArg_src).1.ty?.isSome = true := by
  decide +kernel

-- Missing parameter type: no dominant formal, no function type found, a body
-- that is not `g x` with `x` the parameter.
example : elabAt CalleeInc_srcD = (.no (.missingParamType none), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabAt CalleeTop_srcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabAt CalleeSngl_srcD = (.no (.missingParamType none), ⟨defaultFuel - 1, false⟩) ∧
    writtenAt CalleeSngl_src = (.no .mismatch, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : elabAt CalleeOther_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeSelf_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeProj_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : elabAt CalleeBlock_srcD = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Mismatch: the lambda the callee fills is not of the singleton goal.
example : elabAt CalleeSnglGoal_srcD = (.no .mismatch, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

/-! ### Self types formed from definitions

The rounds alone, on a literal without a self type, then the self type in
lockstep.  Each check compares the self type `formSelfF` forms with the self
type a written form of the program states, or gives the reason the rounds
stop.  A literal without a self type nested in another one is a job whose
synthesis forms its own self type.  The checks of the literal clause follow in
the next subsection. -/

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

/-- The rounds on a literal without a self type, with its jobs. -/
def formOf {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) :
    Fu (Except (List EReason) (Ty (s,x) × List (Done (s,x)))) :=
  formSelfF Γ d (jobsF .here (d.memberHeads .here) d)

/-- `formSelfF` on the last literal without a self type of a chain of `let`s,
found under written lambdas.  The body of a `let` is searched first, with the
bound variable at `⊤`, and the bound term when the body holds no such literal.
So the checks below put a literal in a body only where its jobs never read the
bound variable.  It is compared with the same place of the written form. -/
def formGo {s : Sig} (Γ : Ctx s) (n : Nat) : PTm s → PTm s → Formed × Tank
  | .lam (some S) t, .lam (some S') t' =>
      if S = S' then formGo (Γ.cons S) n t t' else (.shape, ⟨n, true⟩)
  | .let _ _ t u, .let _ _ t' u' =>
      match formGo (Γ.cons .top) n u u' with
      | (.shape, _) => formGo Γ n t t'
      | r => r
  | .obj none d, .obj o _ =>
      match formOf Γ d ⟨n, false⟩ with
      | (.ok (T, _), tk) => (.self (decide (o = some T)), tk)
      | (.error rs, tk) => (.no (Reason.top tk.out rs), tk)
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a surface program, against its written form, with the tank
left. -/
def formAt (e w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolveP pathsTable e, resolveP pathsTable w with
  | some p, some q => formGo Ctx.nil n p q
  | _, _ => (.shape, ⟨n, true⟩)

/-- `formSelfF` on a written program with every self type erased, against
the program itself. -/
def formAtS (w : STm) (n : Nat := defaultFuel) : Formed × Tank :=
  match resolveP pathsTable w with
  | some q => formGo Ctx.nil n q.eraseSelf q
  | none => (.shape, ⟨n, true⟩)

/-- The jobs of a literal without a self type, with their dependencies. -/
def jobDeps (e : STm) : List (Label × List Label × Bool) :=
  match resolveP pathsTable e with
  | some (.obj none d) => (jobsF .here (d.memberHeads .here) d).map fun j => (j.lbl, j.deps)
  | _ => []

/-- The same, with every self type of a written program erased. -/
def jobDepsS (w : STm) : List (Label × List Label × Bool) :=
  match (resolveP pathsTable w).map PTm.eraseSelf with
  | some (.obj none d) => (jobsF .here (d.memberHeads .here) d).map fun j => (j.lbl, j.deps)
  | _ => []

/-- E5 with the self type of its literal written at the type of the field's
right-hand side. -/
def E5_srcW : STm :=
  pdot% λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : {A : ⊤..⊤}}. {a = v}) in
         let o = f w in o.a

/-- E6 with the self type of its literal written at the type of the field's
right-hand side. -/
def E6_srcW : STm :=
  pdot% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : {a : ⊤}}. {type T = {a : ⊤}} ∧ {v = n})

/-- The bare self at a field, written.  The compiler gives `c` the self's
singleton. -/
def BS_src : STm := pdot% ν(x : {c : x.type}. {c = x})

/-- A forward path to a later stable field, written. -/
def FwP_src : STm :=
  pdot% ν(x : {f : ∀(z : x.c.A) x.c.A} ∧ {val c : μ(w. {A : ⊤ .. ⊤})}.
          {f = λ(z : x.c.A). z} ∧ {c = ν(w : {A : ⊤ .. ⊤}. {type A = ⊤})})

/-- The same with the outer self type erased.  The literal at `c` keeps its
written self type, so `c` is known at once. -/
def FwP_srcO : STm :=
  pdot% ν(x. {f = λ(z : x.c.A). z} ∧ {c = ν(w : {A : ⊤ .. ⊤}. {type A = ⊤})})

/-- A field that reaches a later stable field `c` through the type member `B`,
written. -/
def TMf_src : STm :=
  pdot% ν(x : {B : x.c.A .. x.c.A} ∧ {f : ∀(z : x.B) ⊤} ∧ {val c : μ(y. {A : {a : ⊤} .. {a : ⊤}})}.
          {type B = x.c.A} ∧ {f = λ(z : x.B). z.a} ∧
          {c = ν(y : {A : {a : ⊤} .. {a : ⊤}}. {type A = {a : ⊤}})})

/-- The same definitions with `c` first, written. -/
def TMb_src : STm :=
  pdot% ν(x : {val c : μ(y. {A : {a : ⊤} .. {a : ⊤}})} ∧ {B : x.c.A .. x.c.A} ∧ {f : ∀(z : x.B) ⊤}.
          {c = ν(y : {A : {a : ⊤} .. {a : ⊤}}. {type A = {a : ⊤}})} ∧
          {type B = x.c.A} ∧ {f = λ(z : x.B). z.a})

/-- TMf with the outer self type erased. -/
def TMf_srcO : STm :=
  pdot% ν(x. {type B = x.c.A} ∧ {f = λ(z : x.B). z.a} ∧
          {c = ν(y : {A : {a : ⊤} .. {a : ⊤}}. {type A = {a : ⊤}})})

/-- A stable field whose own right-hand side names a path through it,
written. -/
def OwnP_src : STm :=
  pdot% ν(x : {val a : μ(y. {T : ⊤ .. ⊤} ∧ {f : ∀(z : x.a.T) x.a.T})}.
          {a = ν(y : {T : ⊤ .. ⊤} ∧ {f : ∀(z : x.a.T) x.a.T}. {type T = ⊤} ∧ {f = λ(z : x.a.T). z})})

/-- Two stable fields whose type members name each other, written. -/
def MutP_src : STm :=
  pdot% ν(x : {val types : μ(t. {T : ⊤ .. ⊤} ∧ {A : x.symbols.B .. x.symbols.B})}
             ∧ {val symbols : μ(y. {B : x.types.T .. x.types.T})}.
          {types = ν(t : {T : ⊤ .. ⊤} ∧ {A : x.symbols.B .. x.symbols.B}.
                       {type T = ⊤} ∧ {type A = x.symbols.B})}
          ∧ {symbols = ν(y : {B : x.types.T .. x.types.T}. {type B = x.types.T})})

/-- The self passed as an argument by two fields, written. -/
def BA_src : STm :=
  pdot% λ(g : ∀(y : ⊤) ⊤). ν(x : {c : ⊤} ∧ {v : ⊤}. {c = g x} ∧ {v = g x})

/-- A field whose right-hand side has two comparable types, `⊤` first.  The
self type is written at the least one. -/
def AM1_srcW : STm :=
  pdot% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). ν(s : {c : {b : ⊤}} ∧ {v : {b : ⊤}}. {c = y.a} ∧ {v = s.c})

/-- The same two types in the other order. -/
def AM2_srcW : STm :=
  pdot% λ(y : {a : {b : ⊤}} ∧ {a : ⊤}). ν(s : {c : {b : ⊤}} ∧ {v : {b : ⊤}}. {c = y.a} ∧ {v = s.c})

/-- A field whose right-hand side has two incomparable types. -/
def Amb_srcS : STm := pdot% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s. {a = y.a})

/-- A field that reads a later field, written. -/
def Fwd_src : STm :=
  pdot% ν(x : {a : ∀(y : ⊤) ⊤} ∧ {b : ∀(y : ⊤) ⊤}. {a = x.b} ∧ {b = λ(y : ⊤). y})

/-- A recursive field with a written type, its lambda's domain empty. -/
def RecW_srcS : STm := pdot% ν(x. {a : ∀(y : ⊤) ⊤ = λy. let z = x.a in z y})

/-- The same with the self type written. -/
def RecW_src : STm := pdot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let z = x.a in z y})

/-- Two fields that read each other. -/
def Cyc_srcS : STm := pdot% ν(x. {a = x.b} ∧ {b = x.a})

/-- A recursive field without a written type. -/
def RecU_srcS : STm := pdot% ν(x. {a = λ(y : ⊤). let z = x.a in z y})

/-- A field that reads a cycle between two later fields. -/
def Cyc3_srcS : STm := pdot% ν(x. {a = x.b} ∧ {b = x.v} ∧ {v = x.b})

/-- A recursive field that reads itself through an alias of the self. -/
def AliasRec_srcS : STm := pdot% ν(x. {a = λ(y : ⊤). let w = x in let u = w.a in u y})

/-- A field that reads a later field that is the self, written at the
singleton. -/
def FwdSelf_src : STm := pdot% ν(x : {a : x.type} ∧ {b : x.type}. {a = x.b} ∧ {b = x})

/-- A field that is the self, and a later one that reads it, written. -/
def BareProj_src : STm := pdot% ν(x : {a : x.type} ∧ {b : x.type}. {a = x} ∧ {b = x.a})

/-- The self inside a closure, typed at the snapshot, written. -/
def SL_src : STm := pdot% ν(x : {c : ∀(z : ⊤) μ(y. ⊤)}. {c = λ(z : ⊤). x})

/-- A field that is a lambda without a domain and without a goal. -/
def NoDom_srcS : STm := pdot% ν(x. {a = λy. y})

-- The labels `a`, `b`, `c`, `f` and `types` are `.trm 0`, `.trm 1`, `.trm 3`,
-- `.trm 4` and `.trm 8` of `pathsTable`.

-- The jobs of a field list: the fields without a written type that are not
-- known at once, in source order, with their dependencies.  A field with a
-- written type is no job.
example : jobDeps RecW_srcS = [] := by decide +kernel
example : jobDeps AliasRec_srcS = [(.trm 0, [.trm 0], false)] := by decide +kernel

-- The bare self is known at once, so a field that reads it waits for nothing.
example : jobDepsS FwdSelf_src = [(.trm 0, [.trm 1], false)] := by decide +kernel

-- A selection of a type member of the self depends on the fields its body
-- reaches, in both orders of the definitions.
example : jobDepsS TMf_src = [(.trm 4, [.trm 3], false), (.trm 3, [], false)] := by
  decide +kernel
example : jobDepsS TMb_src = [(.trm 3, [], false), (.trm 4, [.trm 3], false)] := by
  decide +kernel

-- The body of a type member of a nested literal adds no field through a
-- selection, so X1's literal field does not wait for itself.
example : jobDepsS X1_src = [(.trm 3, [], false)] := by decide +kernel

-- Paths through a field inside its own right-hand side, and through two
-- fields that name each other.
example : jobDepsS OwnP_src = [(.trm 0, [.trm 0], false)] := by decide +kernel
example : jobDepsS MutP_src = [(.trm 8, [.trm 6], false), (.trm 6, [.trm 8], false)] := by
  decide +kernel

-- E2 and E7 form their written self types.  E7 has no job.
example : formAt E2_srcS E2_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt E7_srcS E7_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- E5 and E6 form the types of the right-hand sides.
example : formAt E5_srcS E5_srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt E6_srcS E6_srcW = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- Known at once: the bare self at its singleton, a literal with a written self
-- type at a stable field.  FwP's field `f` names a path through `c`.
example : formAtS BS_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAt FwP_srcO FwP_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- TMf with its literal field written: `f` reads `z.a` through `x.B`, which
-- the snapshot dealiases to `x.c.A`.
example : formAt TMf_srcO TMf_src = (.self true, ⟨defaultFuel - 43, false⟩) := by decide +kernel

-- A field that reads a later one waits a round.  A field with a written type
-- is no job.
example : formAtS Fwd_src = (.self true, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : formAt RecW_srcS RecW_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel

-- Cyclic references: two fields that read each other, a recursive field, a
-- cycle that a field before it reads, a recursion through an alias.
example : formAt Cyc_srcS Cyc_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt RecU_srcS RecU_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt Cyc3_srcS Cyc3_srcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : formAt AliasRec_srcS AliasRec_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) :=
  by decide +kernel

-- Cyclic references through paths, with every self type erased: a field that
-- projects itself (X2, P3e), paths through a field inside its own right-hand
-- side (OwnP, E2p, E7p), and two literal fields whose members name each other
-- (MutP, gDOT Fig. 1 and Fig. 2).
example : formAtS X2_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS P3e_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS OwnP_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS E2p_src = (.no (.cyclicRef (.trm 3)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS E7p_src = (.no (.cyclicRef (.trm 3)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS MutP_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS Fig1_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS Fig2_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel

-- Uses of the self other than a projection, typed at the snapshot: a field
-- that reads the bare self, a field read by a later one, the self in a
-- closure, the self passed to a function by two fields.
example : formAtS FwdSelf_src = (.self true, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : formAtS BareProj_src = (.self true, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : formAtS SL_src = (.self true, ⟨defaultFuel, false⟩) := by decide +kernel
example : formAtS BA_src = (.self true, ⟨defaultFuel - 8, false⟩) := by decide +kernel

-- The least candidate, in both orders of the intersection.
example : formAtS AM1_srcW = (.self true, ⟨defaultFuel - 10, false⟩) := by decide +kernel
example : formAtS AM2_srcW = (.self true, ⟨defaultFuel - 9, false⟩) := by decide +kernel

-- No least candidate, and a job whose lambda has no domain.
example : formAt Amb_srcS Amb_srcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : formAt NoDom_srcS NoDom_srcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
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
  | .lam h _ => objBelow h
  | _ => false

/-- Whether the derivation of the first candidate of a resolved program ends
in the object rule, under its lambdas. -/
def objOf (o : Option (PTm [])) (n : Nat := defaultFuel) : Bool :=
  match o with
  | some p =>
      match elabTopF n p with
      | (.ok c, _) => objBelow c.deriv
      | (.error _, _) => false
  | none => false

/-- The same for a surface program. -/
def objAt (e : STm) (n : Nat := defaultFuel) : Bool := objOf (resolveP pathsTable e) n

/-- The self types of the outermost literals erased, those of the literals
they hold kept. -/
def PTm.eraseOuterSelf : {s : Sig} → PTm s → PTm s
  | _, .lam o t => .lam o t.eraseOuterSelf
  | _, .obj _ d => .obj none d
  | _, .let g o t u => .let g o t.eraseOuterSelf u.eraseOuterSelf
  | _, .path y => .path y
  | _, .app y z => .app y z
  | _, .proj y a => .proj y a

/-- A written program with every self type erased, elaborated. -/
def elabAtS (w : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  elabOf ((resolveP pathsTable w).map PTm.eraseSelf) n

/-- A written program with the self types of its outermost literals erased,
elaborated. -/
def elabAtO (w : STm) (n : Nat := defaultFuel) : Outcome × Tank :=
  elabOf ((resolveP pathsTable w).map PTm.eraseOuterSelf) n

/-- `objOf` on a written program with every self type erased. -/
def objAtS (w : STm) (n : Nat := defaultFuel) : Bool :=
  objOf ((resolveP pathsTable w).map PTm.eraseSelf) n

/-- The literal of E2 with its self type erased. -/
def E2obj_srcS : STm := pdot% ν(s. {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- The literal of E2 with its self type written. -/
def E2obj_src : STm :=
  pdot% ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
          {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})

/-- A literal without a self type ascribed at `⊤`.  The goal is no `μ`, so the
self type is formed and the literal subsumed. -/
def AscTop_srcS : STm := pdot% λ(n : {b : ⊤}). (ν(z. {a = n}) : ⊤)

/-- The same with the self type written. -/
def AscTop_src : STm := pdot% λ(n : {b : ⊤}). (ν(z : {a : {b : ⊤}}. {a = n}) : ⊤)

/-- `ν(x1. {a = ν(x2. {a = … ν(xd. {a = n}) …})})` with `d` literals: each
field holds the next literal, the innermost the variable `v`.  The label is
`a` of `pathsTable`. -/
def nestP : Nat → {s : Sig} → BVar s .var → PTm s
  | 0, _, v => .path v
  | d + 1, _, v => .obj none (.trm (.trm 0) none (nestP d (.there v)))

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

-- The erased programs are the written ones with those self types erased.
example : (resolveP pathsTable E2obj_src).map PTm.eraseSelf = resolveP pathsTable E2obj_srcS := rfl
example : (resolveP pathsTable AscTop_src).map PTm.eraseSelf = resolveP pathsTable AscTop_srcS := rfl
example : (resolveP pathsTable X1_src).map PTm.eraseSelf = resolveP pathsTable X1_srcS := rfl
example : (resolveP pathsTable E11_src).map PTm.eraseSelf = resolveP pathsTable E11_srcS := rfl
example : (resolveP pathsTable FwP_src).map PTm.eraseOuterSelf = resolveP pathsTable FwP_srcO := rfl
example : (resolveP pathsTable TMf_src).map PTm.eraseOuterSelf = resolveP pathsTable TMf_srcO := rfl

-- The literal of E2, E2 and E7 compile at their written terms.  The literals
-- have `HasTy.obj` at the head.
example : elabAt E2obj_srcS = ((writtenAt E2obj_src).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenAt E2obj_src).1.ty?.isSome = true ∧ objAt E2obj_srcS = true := by
  decide +kernel
example : elabAt E2_srcS = ((writtenAt E2_src).1, ⟨defaultFuel - 58, false⟩) ∧
    (writtenAt E2_src).1.ty? = some E2_avoided := by
  decide +kernel
example : elabAt E7_srcS = ((writtenAt E7_src).1, ⟨defaultFuel, false⟩) ∧
    (writtenAt E7_src).1.ty?.isSome = true ∧ objAt E7_srcS = true := by
  decide +kernel

-- E5 and E6 compile at the types of their right-hand sides, and so do E5p and
-- E6p, whose fields hold literals.
example : elabAt E5_srcS = ((writtenAt E5_srcW).1, ⟨defaultFuel - 8, false⟩) ∧
    (writtenAt E5_srcW).1.ty?.isSome = true := by
  decide +kernel
example : elabAt E6_srcS = ((writtenAt E6_srcW).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenAt E6_srcW).1.ty?.isSome = true ∧ objAt E6_srcS = true := by
  decide +kernel
example : (elabAtS E5p_src).2 = ⟨defaultFuel - 13, false⟩ ∧ (elabAtS E5p_src).1.ty?.isSome = true := by
  decide +kernel
example : (elabAtS E6p_src).2 = ⟨defaultFuel - 1, false⟩ ∧ (elabAtS E6p_src).1.ty?.isSome = true ∧
    objAtS E6p_src = true := by
  decide +kernel

-- A field that reads a later one, and a recursive field with a written type.
example : elabAtS Fwd_src = ((writtenAt Fwd_src).1, ⟨defaultFuel - 14, false⟩) ∧
    writtenAt Fwd_src = ((writtenAt Fwd_src).1, ⟨defaultFuel - 11, false⟩) ∧
    (writtenAt Fwd_src).1.ty?.isSome = true ∧ objAtS Fwd_src = true := by
  decide +kernel
example : elabAt RecW_srcS = ((writtenAt RecW_src).1, ⟨defaultFuel - 12, false⟩) ∧
    writtenAt RecW_src = ((writtenAt RecW_src).1, ⟨defaultFuel - 6, false⟩) ∧
    (writtenAt RecW_src).1.ty?.isSome = true ∧ objAt RecW_srcS = true := by
  decide +kernel

-- Cyclic references.
example : elabAt Cyc_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt RecU_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt Cyc3_srcS = (.no (.cyclicRef (.trm 1)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAt AliasRec_srcS = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Cyclic references through paths, with every self type erased.
example : elabAtS X2_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS P3e_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS OwnP_src = (.no (.cyclicRef (.trm 0)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS E2p_src = (.no (.cyclicRef (.trm 3)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS E7p_src = (.no (.cyclicRef (.trm 3)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS MutP_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS Fig1_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel
example : elabAtS Fig2_src = (.no (.cyclicRef (.trm 8)), ⟨defaultFuel, false⟩) := by decide +kernel

-- The same programs with only their outermost self types erased compile at
-- their written terms, since the literals they hold keep their self types and
-- are known at once.
example : elabAtO OwnP_src = ((writtenAt OwnP_src).1, ⟨defaultFuel - 1, false⟩) ∧
    (writtenAt OwnP_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAtO E2p_src = ((writtenAt E2p_src).1, ⟨defaultFuel - 71, false⟩) ∧
    (writtenAt E2p_src).1.ty? = some E2_avoided := by
  decide +kernel
example : elabAtO E7p_src = ((writtenAt E7p_src).1, ⟨defaultFuel, false⟩) ∧
    (writtenAt E7p_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAtO MutP_src = ((writtenAt MutP_src).1, ⟨defaultFuel, false⟩) ∧
    (writtenAt MutP_src).1.ty?.isSome = true := by
  decide +kernel
example : elabAtO Fig1_src = ((writtenAt Fig1_src).1, ⟨defaultFuel - 242, false⟩) ∧
    (writtenAt Fig1_src).1.ty? = some Fig1_ty := by
  decide +kernel
example : elabAtO Fig2_src = ((writtenAt Fig2_src).1, ⟨defaultFuel - 242, false⟩) ∧
    (writtenAt Fig2_src).1.ty? = some Fig2_avoided := by
  decide +kernel

-- Literals that hold literals.  X1's field `c` is a job whose literal forms
-- its own self type, at a stable field.  FwP's literal keeps its self type.
-- TMf and TMb wait for `c` through the type member `B`, in both orders.
-- E11's field `b` is at the type of `z`.
example : elabAt X1_srcS = ((writtenAt X1_src).1, ⟨defaultFuel, false⟩) ∧
    (writtenAt X1_src).1.ty?.isSome = true ∧ objAt X1_srcS = true := by
  decide +kernel
example : elabAt FwP_srcO = ((writtenAt FwP_src).1, ⟨defaultFuel - 1, false⟩) ∧
    elabAtS FwP_src = elabAt FwP_srcO ∧ (writtenAt FwP_src).1.ty?.isSome = true ∧
    objAt FwP_srcO = true := by
  decide +kernel
example : elabAtS TMf_src = ((writtenAt TMf_src).1, ⟨defaultFuel - 109, false⟩) ∧
    elabAt TMf_srcO = elabAtS TMf_src ∧
    writtenAt TMf_src = ((writtenAt TMf_src).1, ⟨defaultFuel - 66, false⟩) ∧
    (writtenAt TMf_src).1.ty?.isSome = true ∧ objAtS TMf_src = true := by
  decide +kernel
example : elabAtS TMb_src = ((writtenAt TMb_src).1, ⟨defaultFuel - 109, false⟩) ∧
    (writtenAt TMb_src).1.ty?.isSome = true ∧ objAtS TMb_src = true := by
  decide +kernel
example : (elabAt E11_srcS).2 = ⟨defaultFuel - 2, false⟩ ∧
    (elabAt E11_srcS).1.ty? =
      some (.mu (.and (.vfld (.trm 0) (.mu (.typ (.typ 0) .top .top)))
        (.fld (.trm 1) (.mu (.typ (.typ 3) .top .top))))) := by
  decide +kernel

-- Bare uses of the self: the self as a whole right-hand side at its
-- singleton, a field that reads it, the self in a closure, the self passed to
-- a function by two fields.
example : elabAtS BS_src = ((writtenAt BS_src).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenAt BS_src).1.ty?.isSome = true ∧ objAtS BS_src = true := by
  decide +kernel
example : elabAtS FwdSelf_src = ((writtenAt FwdSelf_src).1, ⟨defaultFuel - 16, false⟩) ∧
    writtenAt FwdSelf_src = ((writtenAt FwdSelf_src).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenAt FwdSelf_src).1.ty?.isSome = true ∧ objAtS FwdSelf_src = true := by
  decide +kernel
example : elabAtS BareProj_src = ((writtenAt BareProj_src).1, ⟨defaultFuel - 16, false⟩) ∧
    writtenAt BareProj_src = ((writtenAt BareProj_src).1, ⟨defaultFuel - 13, false⟩) ∧
    (writtenAt BareProj_src).1.ty?.isSome = true ∧ objAtS BareProj_src = true := by
  decide +kernel
example : elabAtS SL_src = ((writtenAt SL_src).1, ⟨defaultFuel - 10, false⟩) ∧
    (writtenAt SL_src).1.ty?.isSome = true ∧ objAtS SL_src = true := by
  decide +kernel
example : elabAtS BA_src = ((writtenAt BA_src).1, ⟨defaultFuel - 32, false⟩) ∧
    writtenAt BA_src = ((writtenAt BA_src).1, ⟨defaultFuel - 24, false⟩) ∧
    (writtenAt BA_src).1.ty?.isSome = true ∧ objAtS BA_src = true := by
  decide +kernel

-- The least candidate, in both orders of the intersection.
example : elabAtS AM1_srcW = ((writtenAt AM1_srcW).1, ⟨defaultFuel - 27, false⟩) ∧
    writtenAt AM1_srcW = ((writtenAt AM1_srcW).1, ⟨defaultFuel - 17, false⟩) ∧
    (writtenAt AM1_srcW).1.ty?.isSome = true ∧ objAtS AM1_srcW = true := by
  decide +kernel
example : elabAtS AM2_srcW = ((writtenAt AM2_srcW).1, ⟨defaultFuel - 25, false⟩) ∧
    writtenAt AM2_srcW = ((writtenAt AM2_srcW).1, ⟨defaultFuel - 16, false⟩) ∧
    (writtenAt AM2_srcW).1.ty?.isSome = true ∧ objAtS AM2_srcW = true := by
  decide +kernel

-- No least candidate, and a job whose lambda has no domain.
example : elabAt Amb_srcS = (.no (.ambiguous (.trm 0)), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : elabAt NoDom_srcS = (.no (.missingParamType none), ⟨defaultFuel, false⟩) := by
  decide +kernel

-- Fields at the types of their right-hand sides: X4's methods, and the
-- written types of E9 and AVp, at less fuel than the written programs.
example : (elabAtS X4_src).2 = ⟨defaultFuel - 5, false⟩ ∧ (elabAtS X4_src).1.ty?.isSome = true ∧
    objAtS X4_src = true := by
  decide +kernel
example : (elabAtS E9_src).2 = ⟨defaultFuel - 20, false⟩ ∧
    (elabAtS E9_src).1.ty? = (writtenAt E9_src).1.ty? ∧ (writtenAt E9_src).1.ty?.isSome = true := by
  decide +kernel
example : (elabAtS AVp_src).2 = ⟨defaultFuel - 14, false⟩ ∧
    (elabAtS AVp_src).1.ty? = (writtenAt AVp_src).1.ty? ∧ (writtenAt AVp_src).1.ty?.isSome = true := by
  decide +kernel

-- A goal that is no `μ`: the self type formed, then subsumption.
example : elabAt AscTop_srcS = ((writtenAt AscTop_src).1, ⟨defaultFuel - 3, false⟩) ∧
    (writtenAt AscTop_src).1.ty?.isSome = true := by
  decide +kernel

-- Nested literals: one unit per level.  Each field is elaborated once, and
-- the object clause checks a stable field that holds a literal without
-- drawing, so the typer spends one unit on the whole term.
example : x6At 4 = some (4, 1) := by decide +kernel
example : x6At 8 = some (8, 1) := by decide +kernel
example : x6At 12 = some (12, 1) := by decide +kernel
example : x6At 17 = some (17, 1) := by decide +kernel

end ElabChecks

end PathsFrontend
