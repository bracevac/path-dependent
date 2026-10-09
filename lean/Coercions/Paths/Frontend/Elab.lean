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
(`selfGoalF`).  A literal without a self type and without such a goal is
rejected with a mismatch: this module does not form a self type from the
definitions.

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

/-- A literal without a self type and without a goal that gives one.  No self
type is formed from the definitions here, so it is a mismatch. -/
def objFormF {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) : Fu (ESynth Γ (.obj none d)) :=
  Fu.ret ([], [.mismatch])

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
      | .obj none d => objFormF Γ d
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
                  (fun _ => Fu.bind (objFormF Γ d) (subsume Γ G))
            | none => Fu.bind (objFormF Γ d) (subsume Γ G)
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

theorem objFormF_framed {s : Sig} (Γ : Ctx s) (d : PDefs (s,x)) : Framed (objFormF Γ d) :=
  ret_framed _

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
    · exact objFormF_framed _ _
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
      split
      · exact orElseW_framed
          (bind_framed (objSelfF_framed _ _ _ (elabDefsF_framed _ d _)) fun _ => subsume_framed _ _ _)
          (bind_framed (objFormF_framed _ _) fun _ => subsume_framed _ _ _)
      · exact bind_framed (objFormF_framed _ _) fun _ => subsume_framed _ _ _
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
  | .trm a o t, T => by
    rw [elabDefsF]
    split
    · exact ret_framed _
    · cases T with
      | fld c U =>
        refine ite_framed (dite_framed (fun _ => ?_) (fun _ => ret_framed _)) (ret_framed _)
        exact bind_framed (elabChkF_framed _ t U) fun _ => ret_framed _
      | vfld c V =>
        cases o with
        | none =>
          cases t <;> cases V <;> first
            | exact ret_framed _
            | exact ite_framed (dite_framed (fun _ => bind_framed (elabDefsF_framed _ _ _) fun _ =>
                ret_framed _) (fun _ => ret_framed _)) (ret_framed _)
        | some _ => cases t <;> cases V <;> exact ret_framed _
      | _ => exact ret_framed _
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

end ElabChecks

end PathsFrontend
