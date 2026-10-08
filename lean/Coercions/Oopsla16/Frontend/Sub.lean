import Coercions.Oopsla16.Frontend.Look

/-!
# Subtyping in the compiler's case order

The algorithm decides two goals.  `sub S T` asks for `S <: T` and is
answered by an `Oopsla16.Stp` derivation.  `var x V T` asks that the variable
`x`, already seen at the type `V`, have the type `T`.  It is answered by a
map from a `HasType` derivation of `x : V` to one of `x : T`.  This is the
compiler's singleton on the left: it keeps `x` while it widens, so a
recursive type is opened or packed at `x` (`TypeComparer.scala:742-744`,
`fixRecs` at `:1990-2005`).  Oopsla16 packs and unpacks only at a variable,
so the second goal is needed.

Each goal tries its alternatives in the compiler's order: identity
(`TypeComparer.scala:1626`), then `firstTry` on the right (`:300`), then
`secondTry` on the left (`:434`), then `thirdTry` on the right (`:652`), then
`fourthTry` on the left (`:981`).  Three cases of the compiler are final.  An
intersection on the right splits (`:401-402`).  A union on the left splits
(`:501-523`).  Two recursive types compare their bodies (`:738-740`).  At two
recursive types the algorithm tries `stp_bindx`, then `stp_bind1`.  The
compiler never builds a recursive type whose self is unused
(`RecType.closeOver`, `Types.scala:3464-3466`), and Oopsla16 does, so such a
left side needs `stp_bind1` (`Typing.lean:149`).  Each alternative is a
function of its own and emits the version's own derivation.  The middle of
every transitivity step is a bound of a member found by lookup.  No middle is
chosen from the context.  Where the compiler tries two alternatives with
`either` (`:2016`), each is tried in turn.

The forms Oopsla16 forces to differ from the compiler are these.  `⊤` on
the right and `⊥` on the left are tried before the final cases.  `S <: μ B`
with `S` not recursive is final in the compiler (`:741-744`), and `Stp` has no
rule for it, so the later alternatives go on.  The compiler meets the members
of both operands of an intersection (`:714,724,729`, `hasMatchingMember` at
`:2235`, `goAnd` at `Types.scala:994-995`) and keeps one merged denotation per
name.  Oopsla16 has no rule that merges two members, so each member is tried.
Distribution over a union (`:813-818`, `:1083-1092`) and the union
alternatives `widenOK` and `joinOK` (`:506-530`) have no rule and are left
out.  The early `return false` after a failed alias (`:318-319`) is not
copied, which only adds successes.  The compiler compares two codomains under
the left method's parameter (`:2298`), and `stp_fun` under the right one.
`HasType` has no intersection introduction on a variable.  So at an
intersection on the right of a `var` goal the variable is shown at one part of
it, then the part is compared with the whole (`vAndPart`), or the variable is
packed at the recursive type of both bodies (`vAndPack`).  Neither is final.

A selection on the right skips a member whose lower bound is `⊥`, as
`isSubApproxHi` fails at once there (`TypeComparer.scala:1606-1607`).  A left
side that is `⊥` has already succeeded by the rule for `⊥`.

Member lookups go through `hdecls` of `Look.lean`, at the prefix of the
variable.  Its structural index is the fuel left in the tank.  Each lookup
level draws at least one unit, so the index never runs out before the tank
does.

The run is the generic one of `Fuel.lean`, at the cost `cost`: one tank for
the whole run, the goals pending along the branch, and a goal that repeats
exactly fails.  A goal holds its context, so a goal under a new binder is
never cut by a goal outside it.  `sub?` and `var?` start a run from a full
tank and return the answer with the tank left.  `subF` and `varF` run on a
tank they are handed, for a caller that threads one tank through many goals.

The step is framed and dominated (`step_frame`, `step_dom`), so the facts of
`Fuel.lean` hold for the run.  `subF` and `varF` are framed, and `sub?` and
`var?` keep an answer at any larger fuel (`sub?_mono`, `var?_mono`).

Every definition is structural, so the kernel evaluates the algorithm.  The
checks at the end of the module run it on the examples by `decide +kernel`.
-/

namespace Oopsla16Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Ctx Store Stp Htp HasType scopeUpTo renameUpTo varUpTo)

/-! ## Goals and answers -/

/-- A variable at a type, at the empty store. -/
abbrev Var {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) : Type :=
  HasType Store.nil Γ (.tvar (.abs x)) T

/-- The two goals of the algorithm. -/
inductive Q (s : Sig) where
  /-- `S <: T`. -/
  | sub (S T : Ty [] s)
  /-- The variable `x`, seen at `V`, has the type `T`. -/
  | var (x : BVar s .var) (V T : Ty [] s)
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx [] s
  q : Q s
deriving DecidableEq

/-- The answer to a goal: a derivation of `S <: T`, or a map from a
derivation of `x : V` to one of `x : T`. -/
def RQ {s : Sig} (Γ : Ctx [] s) : Q s → Type
  | .sub S T => SStp Γ S T
  | .var x V T => Var Γ x V → Var Γ x T

/-- The answer to a goal in its context. -/
def R (g : G) : Type := RQ g.Γ g.q

/-- The oracle an alternative asks: goals in the same context. -/
abbrev Rec {s : Sig} (Γ : Ctx [] s) := (q : Q s) → Fu (Option (RQ Γ q))

/-- The oracle for a `sub` goal under one more hypothesis `T0`: the parameter
of `stp_fun`, or the self of `stp_bindx` and `stp_bind1`. -/
abbrev RecC {s : Sig} (Γ : Ctx [] s) :=
  (T0 : Ty [] (s,x)) → (S T : Ty [] (s,x)) → Fu (Option (SStp (Γ.cons T0) S T))

/-- A type member of `x` at `L`: its bounds in the prefix of `x`, and the
`Htp` premise of `stp_sel1` and `stp_sel2`. -/
abbrev TyMem {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (L : Lb) : Type :=
  (lo : Ty [] (scopeUpTo x)) × (hi : Ty [] (scopeUpTo x)) × SHtp Γ x (.TTyp L lo hi)

/-! ## Combinators on optional answers -/

/-- Run `c`, and map an answer through `f`. -/
def mapO {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (Option β) :=
  Fu.bind c fun o => Fu.ret (o.map f)

/-- Run `c`, and on an answer run `f` on it.  No answer stops here. -/
def bindO {α β : Type} (c : Fu (Option α)) (f : α → Fu (Option β)) : Fu (Option β) :=
  Fu.bind c fun
    | some a => f a
    | none => Fu.ret none

/-- The type members of `x` at `L`, looked up on the tank.  The index of the
lookup is the fuel left. -/
def members {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (L : Lb) : Fu (List (TyMem Γ x L)) :=
  fun t => hdecls Γ t.left x L t

/-! ## Tests on the form of a type -/

/-- The type is an intersection. -/
def isAnd {s : Sig} : Ty [] s → Bool
  | .TAnd _ _ => true
  | _ => false

/-- The type is a union. -/
def isOr {s : Sig} : Ty [] s → Bool
  | .TOr _ _ => true
  | _ => false

/-- The type is recursive. -/
def isMu {s : Sig} : Ty [] s → Bool
  | .TBind _ => true
  | _ => false

/-- The type is a selection. -/
def isSel {s : Sig} : Ty [] s → Bool
  | .TSel _ _ => true
  | _ => false

/-- The pairs at which the compiler stops at its first case: an intersection
on the right (`TypeComparer.scala:401-402`), a union on the left (`:523`), two
recursive types (`:738-740`). -/
def Final {s : Sig} (S T : Ty [] s) : Bool := isAnd T || isOr S || (isMu S && isMu T)

/-- `stp_fun` across a decided label equality. -/
def stpFun {s : Sig} {Γ : Ctx [] s} {l1 l2 : Lb} {T1 T3 : Ty [] s} {T2 T4 : Ty [] (s,x)}
    (h : l1 = l2) (e1 : SStp Γ T3 T1) (e2 : SStp (Γ.cons T3.weaken) T2 T4) :
    SStp Γ (.TFun l1 T1 T2) (.TFun l2 T3 T4) := by
  cases h
  exact .stp_fun e1 e2

/-- `stp_typ` across a decided label equality. -/
def stpTyp {s : Sig} {Γ : Ctx [] s} {l1 l2 : Lb} {T1 T2 T3 T4 : Ty [] s} (h : l1 = l2)
    (e1 : SStp Γ T3 T1) (e2 : SStp Γ T2 T4) : SStp Γ (.TTyp l1 T1 T2) (.TTyp l2 T3 T4) := by
  cases h
  exact .stp_typ e1 e2

/-! ## The `sub` goal, one alternative per compiler case -/

section SubAlts

variable {s : Sig} {Γ : Ctx [] s}

/-- Identity, `TypeComparer.scala:1626`.  `Stp.refl` is a derived rule. -/
def sRefl (S T : Ty [] s) : Option (SStp Γ S T) :=
  if h : S = T then some (h ▸ refl S) else none

/-- `Any` on the right, `thirdTryNamed`, `TypeComparer.scala:616`. -/
def sTop (S : Ty [] s) : (T : Ty [] s) → Option (SStp Γ S T)
  | .TTop => some .stp_top
  | _ => none

/-- `Nothing` on the left, `secondTry`, `TypeComparer.scala:444-445`. -/
def sBot (T : Ty [] s) : (S : Ty [] s) → Option (SStp Γ S T)
  | .TBot => some .stp_bot
  | _ => none

/-- An intersection on the right, `firstTry`, `TypeComparer.scala:401-402`,
by `stp_and2`.  Both operands must hold. -/
def sAndR (r : Rec Γ) (S : Ty [] s) : (T : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TAnd T1 T2 =>
      bindO (r (.sub S T1)) fun e1 =>
        mapO (r (.sub S T2)) fun e2 => .stp_and2 e1 e2
  | _ => Fu.ret none

/-- A union on the left, `secondTry`, `TypeComparer.scala:501-523`, by
`stp_or1`.  Both operands must hold. -/
def sOrL (r : Rec Γ) (T : Ty [] s) : (S : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TOr S1 S2 =>
      bindO (r (.sub S1 T)) fun e1 =>
        mapO (r (.sub S2 T)) fun e2 => .stp_or1 e1 e2
  | _ => Fu.ret none

/-- Two recursive types, `thirdTry`, `TypeComparer.scala:736-740`, by
`stp_bindx`: the bodies under the left self. -/
def sBindx (rC : RecC Γ) : (S T : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TBind T1, .TBind T2 => mapO (rC T1 T1 T2) .stp_bindx
  | _, _ => Fu.ret none

/-- A union on the right, `thirdTry`, `TypeComparer.scala:823`, the left
operand first, as `either` does (`:2016`), by `stp_or21` and `stp_or22`. -/
def sOrR (r : Rec Γ) (S : Ty [] s) : (T : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TOr T1 T2 =>
      Fu.orElse (mapO (r (.sub S T1)) .stp_or21) fun _ => mapO (r (.sub S T2)) .stp_or22
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member,
`thirdTryNamed`, `TypeComparer.scala:601`, by `stp_sel2` after `stp_trans`.
Each member is tried.  A member whose lower bound is `⊥` is skipped, as
`isSubApproxHi` fails at once there (`TypeComparer.scala:1606-1607`). -/
def sSelLo (r : Rec Γ) (S : Ty [] s) : (T : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TSel (.abs x) L =>
      Fu.bind (members Γ x L) fun ds =>
        Fu.firstSome (fun d : TyMem Γ x L =>
          if d.1 = .TBot then Fu.ret none
          else mapO (r (.sub S (d.1.rename (renameUpTo x)))) fun e =>
            .stp_trans e (.stp_sel2 (upperTop d.2.2))) ds
  | _ => Fu.ret none

/-- Two methods or two type members of one label, `thirdTry`: refinements by
`compareRefinedSlow` and `hasMatchingMember` (`TypeComparer.scala:659-663,2235`),
bounds by `compareTypeBounds` (`:864-868`), and methods with contravariant
parameters by `isSubInfo` (`:2291-2301`).  `stp_fun` compares the codomains
under the right domain. -/
def sStruct (r : Rec Γ) (rC : RecC Γ) : (S T : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TFun l1 T1 T2, .TFun l2 T3 T4 =>
      if h : l1 = l2 then
        bindO (r (.sub T3 T1)) fun e1 =>
          mapO (rC T3.weaken T2 T4) fun e2 => stpFun h e1 e2
      else Fu.ret none
  | .TTyp l1 T1 T2, .TTyp l2 T3 T4 =>
      if h : l1 = l2 then
        bindO (r (.sub T3 T1)) fun e1 =>
          mapO (r (.sub T2 T4)) fun e2 => stpTyp h e1 e2
      else Fu.ret none
  | _, _ => Fu.ret none

/-- A selection on the left, through the upper bound of a member, `fourthTry`,
`TypeComparer.scala:982-992`, by `stp_sel1` before `stp_trans`.  Each member
is tried. -/
def sSelHi (r : Rec Γ) (T : Ty [] s) : (S : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TSel (.abs x) L =>
      Fu.bind (members Γ x L) fun ds =>
        Fu.firstSome (fun d : TyMem Γ x L =>
          mapO (r (.sub (d.2.1.rename (renameUpTo x)) T)) fun e =>
            .stp_trans (.stp_sel1 (lowerBot d.2.2)) e) ds
  | _ => Fu.ret none

/-- An intersection on the left, `fourthTry`, `TypeComparer.scala:1077-1099`,
by `stp_and11` and `stp_and12`.  The left operand first, then the right one,
as `either` does (`:2016`). -/
def sAndL (r : Rec Γ) (T : Ty [] s) : (S : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TAnd S1 S2 =>
      Fu.orElse (mapO (r (.sub S1 T)) .stp_and11) fun _ => mapO (r (.sub S2 T)) .stp_and12
  | _ => Fu.ret none

/-- A recursive type on the left, `fourthTry`, `TypeComparer.scala:1063-1064`,
by `stp_bind1`: the body under its self against the right side, which must not
mention the self. -/
def sBind1 (rC : RecC Γ) (T : Ty [] s) : (S : Ty [] s) → Fu (Option (SStp Γ S T))
  | .TBind T1 => mapO (rC T1 T1 T.weaken) .stp_bind1
  | _ => Fu.ret none

end SubAlts

/-- The alternatives after the final cases, in the compiler's order: the right
type (`thirdTry`), then the left type (`fourthTry`). -/
def subRest {s : Sig} {Γ : Ctx [] s} (r : Rec Γ) (rC : RecC Γ) (S T : Ty [] s) :
    Fu (Option (SStp Γ S T)) :=
  Fu.orElse (sOrR r S T) fun _ =>
  Fu.orElse (sSelLo r S T) fun _ =>
  Fu.orElse (sStruct r rC S T) fun _ =>
  Fu.orElse (sSelHi r T S) fun _ =>
  Fu.orElse (sAndL r T S) fun _ =>
  sBind1 rC T S

/-- The final cases, then the rest.  At two recursive types `stp_bindx` is
tried, then `stp_bind1`, for a left self that the body does not use. -/
def subMain {s : Sig} {Γ : Ctx [] s} (r : Rec Γ) (rC : RecC Γ) (S T : Ty [] s) :
    Fu (Option (SStp Γ S T)) :=
  if isAnd T then sAndR r S T
  else if isOr S then sOrL r T S
  else if isMu S && isMu T then Fu.orElse (sBindx rC S T) fun _ => sBind1 rC T S
  else subRest r rC S T

/-- The `sub` goal: identity, `⊤` and `⊥`, then the final cases and the
rest. -/
def subStep {s : Sig} (Γ : Ctx [] s) (r : Rec Γ) (rC : RecC Γ) (S T : Ty [] s) :
    Fu (Option (SStp Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>
  Fu.orElse (Fu.ret (sBot T S)) fun _ =>
  subMain r rC S T

/-! ## The `var` goal, one alternative per compiler case -/

/-- A map from a derivation of `x : V` to one of `x : T`. -/
abbrev VarFn {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (V T : Ty [] s) : Type :=
  Var Γ x V → Var Γ x T

/-- The operands of an intersection, left to right, each not an
intersection. -/
def andParts {s : Sig} : Ty [] s → List (Ty [] s)
  | .TAnd A B => andParts A ++ andParts B
  | T => [T]

section VarAlts

variable {s : Sig} {Γ : Ctx [] s}

/-- Identity, `TypeComparer.scala:1626`. -/
def vRefl (x : BVar s .var) (V T : Ty [] s) : Option (VarFn Γ x V T) :=
  if h : V = T then some (fun d => h ▸ d) else none

/-- An intersection on the right, `firstTry`, `TypeComparer.scala:401-402`.
`HasType` has no intersection introduction on a variable.  So the variable is
shown at one operand `W`, with the variable kept, and `W` is compared with the
whole by `T_Sub`.  Each operand is tried. -/
def vAndPart (r : Rec Γ) (x : BVar s .var) (V : Ty [] s) : (T : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TAnd T1 T2 =>
      Fu.firstSome (fun W =>
        bindO (r (.var x V W)) fun f =>
          mapO (r (.sub W (.TAnd T1 T2))) fun e d => .T_Sub (f d) e)
        (andParts (.TAnd T1 T2))
  | _ => Fu.ret none

/-- An intersection of two recursive types on the right.  The variable is
shown at the opened body of `μ(A ∧ B)` and packed there by `T_VarPack`.  Then
`μ(A ∧ B) <: μA ∧ μB` by `stp_and2` over two `stp_bindx`. -/
def vAndPack (r : Rec Γ) (x : BVar s .var) (V : Ty [] s) : (T : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TAnd (.TBind A) (.TBind B) =>
      mapO (r (.var x V ((Ty.TAnd A B).substVr (.abs x)))) fun f d =>
        .T_Sub (.T_VarPack (f d)) (.stp_and2 (.stp_bindx (.stp_and11 (refl A)))
          (.stp_bindx (.stp_and12 (refl B))))
  | _ => Fu.ret none

/-- A recursive type on the right with a singleton on the left, `thirdTry`,
`TypeComparer.scala:742-744`.  `fixRecs` (`:1990-2005`) opens the body at the
variable, and `T_VarPack` packs it there. -/
def vMuR (r : Rec Γ) (x : BVar s .var) (V : Ty [] s) : (T : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TBind B => mapO (r (.var x V (B.substVr (.abs x)))) fun f d => .T_VarPack (f d)
  | _ => Fu.ret none

/-- A union on the right, `thirdTry`, `TypeComparer.scala:823`, the variable
kept, the left operand first (`either`, `:2016`). -/
def vOrR (r : Rec Γ) (x : BVar s .var) (V : Ty [] s) : (T : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TOr T1 T2 =>
      Fu.orElse (mapO (r (.var x V T1)) fun f d => .T_Sub (f d) (.stp_or21 (refl T1))) fun _ =>
        mapO (r (.var x V T2)) fun f d => .T_Sub (f d) (.stp_or22 (refl T2))
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, the
variable kept, `thirdTryNamed`, `TypeComparer.scala:601`.  Each member is
tried.  A member whose lower bound is `⊥` is skipped
(`TypeComparer.scala:1606-1607`). -/
def vSelLo (r : Rec Γ) (x : BVar s .var) (V : Ty [] s) : (T : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TSel (.abs p) L =>
      Fu.bind (members Γ p L) fun ds =>
        Fu.firstSome (fun d : TyMem Γ p L =>
          if d.1 = .TBot then Fu.ret none
          else mapO (r (.var x V (d.1.rename (renameUpTo p)))) fun f e =>
            .T_Sub (f e) (.stp_sel2 (upperTop d.2.2))) ds
  | _ => Fu.ret none

/-- A recursive type in the view, opened at the variable, as `findMember`'s
`goRec` opens it with the variable as prefix (`Types.scala:875-896`), by
`T_VarUnpack`. -/
def vMuL (r : Rec Γ) (x : BVar s .var) (T : Ty [] s) : (V : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TBind B => mapO (r (.var x (B.substVr (.abs x)) T)) fun f d => f (.T_VarUnpack d)
  | _ => Fu.ret none

/-- An intersection in the view, `fourthTry`, `TypeComparer.scala:1077-1099`.
The left operand first, then the right one, as `either` does (`:2016`). -/
def vAndL (r : Rec Γ) (x : BVar s .var) (T : Ty [] s) : (V : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TAnd V1 V2 =>
      Fu.orElse (mapO (r (.var x V1 T)) fun f d => f (.T_Sub d (.stp_and11 (refl V1)))) fun _ =>
        mapO (r (.var x V2 T)) fun f d => f (.T_Sub d (.stp_and12 (refl V2)))
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member, `fourthTry`,
`TypeComparer.scala:982-992`.  Each member is tried. -/
def vSelHi (r : Rec Γ) (x : BVar s .var) (T : Ty [] s) : (V : Ty [] s) → Fu (Option (VarFn Γ x V T))
  | .TSel (.abs q) L =>
      Fu.bind (members Γ q L) fun ds =>
        Fu.firstSome (fun d : TyMem Γ q L =>
          mapO (r (.var x (d.2.1.rename (renameUpTo q)) T)) fun f e =>
            f (.T_Sub e (.stp_sel1 (lowerBot d.2.2)))) ds
  | _ => Fu.ret none

/-- The singleton widened to its view, `fourthTry`,
`TypeComparer.scala:1036-1058`: the view against the goal, by `T_Sub`.  Not at
a recursive type or a selection, where the variable is kept. -/
def vSub (r : Rec Γ) (x : BVar s .var) (V T : Ty [] s) : Fu (Option (VarFn Γ x V T)) :=
  if !isMu V && !isSel V then mapO (r (.sub V T)) fun e d => .T_Sub d e else Fu.ret none

end VarAlts

/-- The `var` goal: the variable `x`, seen at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  None is final, since an intersection
on the right cannot be split at a variable. -/
def varStep {s : Sig} (Γ : Ctx [] s) (r : Rec Γ) (x : BVar s .var) (V T : Ty [] s) :
    Fu (Option (VarFn Γ x V T)) :=
  Fu.orElse (Fu.ret (vRefl x V T)) fun _ =>
  Fu.orElse (vAndPart r x V T) fun _ =>
  Fu.orElse (vAndPack r x V T) fun _ =>
  Fu.orElse (vMuR r x V T) fun _ =>
  Fu.orElse (vOrR r x V T) fun _ =>
  Fu.orElse (vSelLo r x V T) fun _ =>
  Fu.orElse (vMuL r x T V) fun _ =>
  Fu.orElse (vAndL r x T V) fun _ =>
  Fu.orElse (vSelHi r x T V) fun _ =>
  vSub r x V T

/-! ## The step and the entry points -/

/-- One step of the algorithm.  A goal in `Γ` asks goals in `Γ`, and a goal
under a new hypothesis `T0` is asked in `Γ.cons T0`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .sub S T⟩ =>
      subStep Γ (fun q => o ⟨s, Γ, q⟩) (fun T0 S' T' => o ⟨_, Γ.cons T0, .sub S' T'⟩) S T
  | ⟨s, Γ, .var x V T⟩ => varStep Γ (fun q => o ⟨s, Γ, q⟩) x V T

/-- `S <: T` on the tank it is handed.  The run's index is the fuel left. -/
def subF {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Fu (Option (SStp Γ S T)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .sub S T⟩ t

/-- `x : T` on the tank it is handed, from the type `x` is declared at, by
`T_Varz`. -/
def varF {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) : Fu (Option (Var Γ x T)) :=
  mapO (fun t => run cost step t.left [] ⟨s, Γ, .var x (Γ.lookup x) T⟩ t) fun f => f .T_Varz

/-- `S <: T` from a full tank of `n` units, with the tank left. -/
def sub? {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) (n : Nat := defaultFuel) :
    Option (SStp Γ S T) × Tank :=
  subF Γ S T ⟨n, false⟩

/-- `x : T` from a full tank of `n` units, with the tank left. -/
def var? {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) (n : Nat := defaultFuel) :
    Option (Var Γ x T) × Tank :=
  varF Γ x T ⟨n, false⟩

/-! ## The lookup at the tank's own index

`members` runs a lookup whose index is the fuel left.  With more fuel the
index is larger.  A lookup that ends unmarked never reached index zero, so it
gives the same answers at any larger index.  So `members` is framed, as every
computation of a step must be. -/

/-- Either branch of a test agrees with its partner, so the tests agree. -/
theorem ite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' b b' : Fu α} (ha : Agree a a')
    (hb : Agree b b') : Agree (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- One level of the lookup agrees with its partner when the levels below
agree. -/
theorem lookBody_agree {rec rec' : (q : LQ) → Fu (List q.R)} (hr : ∀ q, Agree (rec q) (rec' q)) :
    ∀ q, Agree (lookBody rec q) (lookBody rec' q) := by
  intro q
  cases q with
  | h s Γ x V k =>
    apply ite_agree (ret_agree _)
    cases V with
    | TBind X => exact bind_agree (hr _) fun _ => ret_agree _
    | TAnd A B => exact bind_agree (hr _) fun _ => bind_agree (hr _) fun _ => ret_agree _
    | TSel p L =>
      cases p with
      | abs y =>
        refine bind_agree (hr _) fun es => flatMapL_agree ?_ es
        intro e
        split
        · exact bind_agree (hr _) fun _ => ret_agree _
        · exact ret_agree _
      | conc _ => exact ret_agree _
    | TBot => exact ret_agree _
    | TTop => exact ret_agree _
    | TFun _ _ _ => exact ret_agree _
    | TTyp _ _ _ => exact ret_agree _
    | TOr _ _ => exact ret_agree _
  | st s Γ V k =>
    apply ite_agree (ret_agree _)
    cases V with
    | TAnd A B => exact bind_agree (hr _) fun _ => bind_agree (hr _) fun _ => ret_agree _
    | TSel p L =>
      cases p with
      | abs y =>
        refine bind_agree (hr _) fun es => flatMapL_agree ?_ es
        intro e
        split
        · exact bind_agree (hr _) fun _ => ret_agree _
        · exact ret_agree _
      | conc _ => exact ret_agree _
    | TBot => exact ret_agree _
    | TTop => exact ret_agree _
    | TFun _ _ _ => exact ret_agree _
    | TTyp _ _ _ => exact ret_agree _
    | TBind _ => exact ret_agree _
    | TOr _ _ => exact ret_agree _

/-- A lookup at a larger index does what the lookup at a smaller one does. -/
theorem look_agree : ∀ d d', d ≤ d' → ∀ (P : List LKey) (q : LQ), Agree (look d P q) (look d' P q)
  | 0, d', _, P, q => by
    refine ⟨look_framed 0 P q, look_framed d' P q, ?_⟩
    intro t r t' h ho _
    simp only [look, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, q => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := look_agree d e (by omega)
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · exact ite_agree (ret_agree _) (lookBody_agree (ih _) q)

/-- A member lookup that ends unmarked gives the same answers at a larger
index. -/
theorem hdecls_index {s : Sig} {Γ : Ctx [] s} {d d' : Nat} {x : BVar s .var} {L : Lb} {t : Tank}
    (h : (hdecls Γ d x L t).2.out = false) (hd : d ≤ d') : hdecls Γ d' x L t = hdecls Γ d x L t := by
  have hag : Agree (hdecls Γ d x L) (hdecls Γ d' x L) :=
    bind_agree (look_agree d d' hd _ _) fun _ => ret_agree _
  have := hag.sim t _ _ rfl h 0
  simpa using this

/-- The lookup at the fuel left is framed: more fuel gives the same members
and leaves the extra fuel over. -/
theorem members_framed {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (L : Lb) :
    Framed (members Γ x L) where
  absorbs t ht := (hdecls_framed Γ t.left x L).absorbs t ht
  spends t := (hdecls_framed Γ t.left x L).spends t
  shift := by
    intro t r t' h ho k
    have h1 := hdecls_frame h ho k
    have h2 : (hdecls Γ t.left x L (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change hdecls Γ (t.left + k) x L (t.add k) = _
    rw [hdecls_index h2 (Nat.le_add_right _ _), h1]

/-! ## The step is framed and dominated

`FrameF step` says that oracles which agree give answers which agree.
`DomF step` says that an oracle which dominates another gives answers which
dominate.  `run_frame`, `run_index` and `cut_complete` of `Fuel.lean` ask for
both.  Each alternative is built from `Fu.ret`, `Fu.bind`, `Fu.orElse`,
`Fu.firstSome`, `mapO`, `bindO`, `members` and tests.  So each has an
agreement lemma and a dominance lemma, each a composition of the combinator
lemmas.  An alternative at one oracle agrees with itself, so it is framed.
The two facts of the step follow by cases on the goal. -/

section Tests

variable {α : Type}

/-- Either branch of a test dominates its partner, so the tests do. -/
theorem ite_dom {p : Prop} [hp : Decidable p] {m : Nat} {a a' b b' : Fu α} (ha : Dom m a a')
    (hb : Dom m b b') : Dom m (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- A test whose branches read its proof agrees with its partner when the
branches do. -/
theorem dite_agree {p : Prop} [hp : Decidable p] {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Agree (a h) (a' h)) (hb : ∀ h, Agree (b h) (b' h)) :
    Agree (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

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

theorem bindO_agree {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Agree c c')
    (hf : ∀ a, Agree (f a) (f' a)) : Agree (bindO c f) (bindO c' f') :=
  bind_agree hc fun
    | some a => hf a
    | none => ret_agree _

theorem bindO_framed {c : Fu (Option α)} {f : α → Fu (Option β)} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) : Framed (bindO c f) :=
  bind_framed hc fun
    | some a => hf a
    | none => ret_framed _

theorem bindO_dom {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) (hd : Dom m c c') (hfd : ∀ a, Dom m (f a) (f' a)) :
    Dom m (bindO c f) (bindO c' f') :=
  bind_dom hc (fun | some a => hf a | none => ret_framed _) hd fun
    | some a => hfd a
    | none => ret_dom _ m

end OptionFrames

/-! ### The alternatives of the `sub` goal

The agreement lemmas take oracles `r` and `r'` that agree on every goal, and
oracles `rC` and `rC'` under one more hypothesis that agree on every goal.
The dominance lemmas take framed `r` and `rC` that dominate `r'` and `rC'`
below `m`.  The lookup is the same on both sides, so `members` enters by its
frame alone. -/

section SubFrames

variable {s : Sig} {Γ : Ctx [] s} {r r' : Rec Γ} {rC rC' : RecC Γ} {m : Nat}

theorem sAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty [] s) :
    Agree (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | TAnd T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty [] s) :
    Dom m (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | TAnd T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sOrL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty [] s) :
    Agree (sOrL r T S) (sOrL r' T S) := by
  cases S with
  | TOr S1 S2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sOrL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty [] s) :
    Dom m (sOrL r T S) (sOrL r' T S) := by
  cases S with
  | TOr S1 S2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sBindx_agree (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Agree (sBindx rC S T) (sBindx rC' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact mapO_agree _ (hC _ _ _)

theorem sBindx_dom (hCF : ∀ T0 S T, Framed (rC T0 S T))
    (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Dom m (sBindx rC S T) (sBindx rC' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact mapO_dom _ (hCF _ _ _) (hCd _ _ _)

theorem sOrR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty [] s) :
    Agree (sOrR r S T) (sOrR r' S T) := by
  cases T with
  | TOr T1 T2 =>
    dsimp only [sOrR]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sOrR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty [] s) :
    Dom m (sOrR r S T) (sOrR r' S T) := by
  cases T with
  | TOr T1 T2 =>
    dsimp only [sOrR]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty [] s) :
    Agree (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | TSel p L =>
    cases p with
    | abs x =>
      exact bind_agree (Agree.refl (members_framed Γ x L)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
    | _ => exact ret_agree _
  | _ => exact ret_agree _

theorem sSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty [] s) :
    Dom m (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | TSel p L =>
    cases p with
    | abs x =>
      have hf : ∀ d : TyMem Γ x L, Framed (if d.1 = .TBot then Fu.ret none
          else mapO (r (.sub S (d.1.rename (renameUpTo x)))) fun e =>
            Stp.stp_trans e (.stp_sel2 (upperTop d.2.2))) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (members_framed Γ x L) (fun ds => firstSome_framed hf ds)
        ((members_framed Γ x L).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
    | _ => exact ret_dom _ m
  | _ => exact ret_dom _ m

theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q))
    (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Agree (sStruct r rC S T) (sStruct r' rC' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hC _ _ _))
        fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _

theorem sStruct_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hCF : ∀ T0 S T, Framed (rC T0 S T)) (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T))
    (S T : Ty [] s) : Dom m (sStruct r rC S T) (sStruct r' rC' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hCF _ _ _)) (hd _)
        fun _ => mapO_dom _ (hCF _ _ _) (hCd _ _ _)) fun _ => ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m

theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty [] s) :
    Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | TSel p L =>
    cases p with
    | abs x =>
      exact bind_agree (Agree.refl (members_framed Γ x L)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
    | _ => exact ret_agree _
  | _ => exact ret_agree _

theorem sSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty [] s) :
    Dom m (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | TSel p L =>
    cases p with
    | abs x =>
      exact bind_dom (members_framed Γ x L)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((members_framed Γ x L).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
    | _ => exact ret_dom _ m
  | _ => exact ret_dom _ m

theorem sAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty [] s) :
    Agree (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | TAnd S1 S2 =>
    dsimp only [sAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty [] s) :
    Dom m (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | TAnd S1 S2 =>
    dsimp only [sAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sBind1_agree (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (T S : Ty [] s) :
    Agree (sBind1 rC T S) (sBind1 rC' T S) := by
  cases S with
  | TBind T1 => exact mapO_agree _ (hC _ _ _)
  | _ => exact ret_agree _

theorem sBind1_dom (hCF : ∀ T0 S T, Framed (rC T0 S T))
    (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T)) (T S : Ty [] s) :
    Dom m (sBind1 rC T S) (sBind1 rC' T S) := by
  cases S with
  | TBind T1 => exact mapO_dom _ (hCF _ _ _) (hCd _ _ _)
  | _ => exact ret_dom _ m

theorem subRest_agree (hr : ∀ q, Agree (r q) (r' q))
    (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Agree (subRest r rC S T) (subRest r' rC' S T) :=
  orElse_agree (sOrR_agree hr S T) <| orElse_agree (sSelLo_agree hr S T) <|
    orElse_agree (sStruct_agree hr hC S T) <| orElse_agree (sSelHi_agree hr T S) <|
    orElse_agree (sAndL_agree hr T S) (sBind1_agree hC T S)

theorem subRest_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hCF : ∀ T0 S T, Framed (rC T0 S T)) (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T))
    (S T : Ty [] s) : Dom m (subRest r rC S T) (subRest r' rC' S T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hC : ∀ T0 S T, Agree (rC T0 S T) (rC T0 S T) := fun _ _ _ => Agree.refl (hCF _ _ _)
  orElse_dom (sOrR_agree hr S T).left (sOrR_dom hF hd S T) <|
    orElse_dom (sSelLo_agree hr S T).left (sSelLo_dom hF hd S T) <|
    orElse_dom (sStruct_agree hr hC S T).left (sStruct_dom hF hd hCF hCd S T) <|
    orElse_dom (sSelHi_agree hr T S).left (sSelHi_dom hF hd T S) <|
    orElse_dom (sAndL_agree hr T S).left (sAndL_dom hF hd T S) (sBind1_dom hCF hCd T S)

theorem subMain_agree (hr : ∀ q, Agree (r q) (r' q))
    (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Agree (subMain r rC S T) (subMain r' rC' S T) :=
  ite_agree (sAndR_agree hr S T) <| ite_agree (sOrL_agree hr T S) <|
    ite_agree (orElse_agree (sBindx_agree hC S T) (sBind1_agree hC T S)) (subRest_agree hr hC S T)

theorem subMain_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hCF : ∀ T0 S T, Framed (rC T0 S T)) (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T))
    (S T : Ty [] s) : Dom m (subMain r rC S T) (subMain r' rC' S T) :=
  have hC : ∀ T0 S T, Agree (rC T0 S T) (rC T0 S T) := fun _ _ _ => Agree.refl (hCF _ _ _)
  ite_dom (sAndR_dom hF hd S T) <| ite_dom (sOrL_dom hF hd T S) <|
    ite_dom (orElse_dom (sBindx_agree hC S T).left (sBindx_dom hCF hCd S T)
      (sBind1_dom hCF hCd T S)) (subRest_dom hF hd hCF hCd S T)

theorem subStep_agree (hr : ∀ q, Agree (r q) (r' q))
    (hC : ∀ T0 S T, Agree (rC T0 S T) (rC' T0 S T)) (S T : Ty [] s) :
    Agree (subStep Γ r rC S T) (subStep Γ r' rC' S T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    subMain_agree hr hC S T

theorem subStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hCF : ∀ T0 S T, Framed (rC T0 S T)) (hCd : ∀ T0 S T, Dom m (rC T0 S T) (rC' T0 S T))
    (S T : Ty [] s) : Dom m (subStep Γ r rC S T) (subStep Γ r' rC' S T) :=
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <| subMain_dom hF hd hCF hCd S T

end SubFrames

/-! ### The alternatives of the `var` goal -/

section VarFrames

variable {s : Sig} {Γ : Ctx [] s} {r r' : Rec Γ} {m : Nat}

theorem vAndPart_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vAndPart r x V T) (vAndPart r' x V T) := by
  cases T with
  | TAnd T1 T2 =>
    exact firstSome_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) _
  | _ => exact ret_agree _

theorem vAndPart_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vAndPart r x V T) (vAndPart r' x V T) := by
  cases T with
  | TAnd T1 T2 =>
    exact firstSome_dom (fun _ => bindO_framed (hF _) fun _ => mapO_framed _ (hF _))
      (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) _
  | _ => exact ret_dom _ m

theorem vAndPack_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vAndPack r x V T) (vAndPack r' x V T) := by
  unfold vAndPack
  split
  · exact mapO_agree _ (hr _)
  · exact ret_agree _

theorem vAndPack_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vAndPack r x V T) (vAndPack r' x V T) := by
  unfold vAndPack
  split
  · exact mapO_dom _ (hF _) (hd _)
  · exact ret_dom _ m

theorem vMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | TBind B => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | TBind B => exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vOrR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vOrR r x V T) (vOrR r' x V T) := by
  cases T with
  | TOr T1 T2 =>
    dsimp only [vOrR]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vOrR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vOrR r x V T) (vOrR r' x V T) := by
  cases T with
  | TOr T1 T2 =>
    dsimp only [vOrR]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | TSel p L =>
    cases p with
    | abs p =>
      exact bind_agree (Agree.refl (members_framed Γ p L)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
    | _ => exact ret_agree _
  | _ => exact ret_agree _

theorem vSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | TSel p L =>
    cases p with
    | abs p =>
      have hf : ∀ d : TyMem Γ p L, Framed (if d.1 = .TBot then Fu.ret none
          else mapO (r (.var x V (d.1.rename (renameUpTo p)))) fun f e =>
            HasType.T_Sub (f e) (.stp_sel2 (upperTop d.2.2))) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (members_framed Γ p L) (fun ds => firstSome_framed hf ds)
        ((members_framed Γ p L).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
    | _ => exact ret_dom _ m
  | _ => exact ret_dom _ m

theorem vMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty [] s) :
    Agree (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | TBind B => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty [] s) : Dom m (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | TBind B => exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty [] s) :
    Agree (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | TAnd V1 V2 =>
    dsimp only [vAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty [] s) : Dom m (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | TAnd V1 V2 =>
    dsimp only [vAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty [] s) :
    Agree (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | TSel p L =>
    cases p with
    | abs q =>
      exact bind_agree (Agree.refl (members_framed Γ q L)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
    | _ => exact ret_agree _
  | _ => exact ret_agree _

theorem vSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty [] s) : Dom m (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | TSel p L =>
    cases p with
    | abs q =>
      exact bind_dom (members_framed Γ q L)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((members_framed Γ q L).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
    | _ => exact ret_dom _ m
  | _ => exact ret_dom _ m

theorem vSub_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (vSub r x V T) (vSub r' x V T) :=
  ite_agree (mapO_agree _ (hr _)) (ret_agree _)

theorem vSub_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (vSub r x V T) (vSub r' x V T) :=
  ite_dom (mapO_dom _ (hF _) (hd _)) (ret_dom _ m)

theorem varStep_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty [] s) :
    Agree (varStep Γ r x V T) (varStep Γ r' x V T) :=
  orElse_agree (ret_agree _) <| orElse_agree (vAndPart_agree hr x V T) <|
    orElse_agree (vAndPack_agree hr x V T) <| orElse_agree (vMuR_agree hr x V T) <|
    orElse_agree (vOrR_agree hr x V T) <| orElse_agree (vSelLo_agree hr x V T) <|
    orElse_agree (vMuL_agree hr x T V) <| orElse_agree (vAndL_agree hr x T V) <|
    orElse_agree (vSelHi_agree hr x T V) (vSub_agree hr x V T)

theorem varStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty [] s) : Dom m (varStep Γ r x V T) (varStep Γ r' x V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (vAndPart_agree hr x V T).left (vAndPart_dom hF hd x V T) <|
    orElse_dom (vAndPack_agree hr x V T).left (vAndPack_dom hF hd x V T) <|
    orElse_dom (vMuR_agree hr x V T).left (vMuR_dom hF hd x V T) <|
    orElse_dom (vOrR_agree hr x V T).left (vOrR_dom hF hd x V T) <|
    orElse_dom (vSelLo_agree hr x V T).left (vSelLo_dom hF hd x V T) <|
    orElse_dom (vMuL_agree hr x T V).left (vMuL_dom hF hd x T V) <|
    orElse_dom (vAndL_agree hr x T V).left (vAndL_dom hF hd x T V) <|
    orElse_dom (vSelHi_agree hr x T V).left (vSelHi_dom hF hd x T V) (vSub_dom hF hd x V T)

end VarFrames

/-! ### The step -/

theorem step_frame : FrameF step := by
  intro o o' ho g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rC := fun T0 S' T' => o ⟨_, Γ.cons T0, .sub S' T'⟩)
      (rC' := fun T0 S' T' => o' ⟨_, Γ.cons T0, .sub S' T'⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun T0 S' T' => ho ⟨_, Γ.cons T0, .sub S' T'⟩) S T
  | var x V T =>
    exact varStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) x V T

theorem step_dom : DomF step := by
  intro m o o' hF _ hd g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rC := fun T0 S' T' => o ⟨_, Γ.cons T0, .sub S' T'⟩)
      (rC' := fun T0 S' T' => o' ⟨_, Γ.cons T0, .sub S' T'⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun T0 S' T' => hF ⟨_, Γ.cons T0, .sub S' T'⟩)
      (fun T0 S' T' => hd ⟨_, Γ.cons T0, .sub S' T'⟩) S T
  | var x V T =>
    exact varStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) x V T

/-! ## The entry points keep an answer with more fuel

A run whose index is the fuel left is framed, as `members` is.  A run that
ends unmarked never reached index zero, so it does the same at any larger
index.  So `subF` and `varF` are framed, and `sub?` and `var?` keep an answer
at any larger fuel. -/

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

theorem subF_framed {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Framed (subF Γ S T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .sub S T⟩

theorem varF_framed {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) :
    Framed (varF Γ x T) :=
  mapO_framed _ (runLeft_framed step_frame [] ⟨s, Γ, .var x (Γ.lookup x) T⟩)

/-- A full tank of `n` units with `m - n` more is a full tank of `m` units. -/
theorem full_add {n m : Nat} (h : n ≤ m) : (⟨n, false⟩ : Tank).add (m - n) = ⟨m, false⟩ := by
  simp only [Tank.add, Tank.mk.injEq, and_true]
  omega

theorem sub?_mono {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} {n m : Nat} {e : SStp Γ S T}
    (h : (sub? Γ S T n).1 = some e) (hnm : n ≤ m) : (sub? Γ S T m).1 = some e := by
  have ho : (sub? Γ S T n).2.out = false := run_some (cost := cost) (P := []) h
  have := (subF_framed Γ S T).shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  change (subF Γ S T ⟨m, false⟩).1 = some e
  rw [this]

theorem var?_mono {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {n m : Nat}
    {e : Var Γ x T} (h : (var? Γ x T n).1 = some e) (hnm : n ≤ m) :
    (var? Γ x T m).1 = some e := by
  have ho : (var? Γ x T n).2.out = false := by
    simp only [var?, varF, mapO, Fu.bind, Fu.ret] at h ⊢
    cases hr : run cost step n [] ⟨s, Γ, .var x (Γ.lookup x) T⟩ ⟨n, false⟩ with
    | mk o t1 =>
      rw [hr] at h
      cases o with
      | none => simp at h
      | some f =>
        have := run_some (cost := cost) (F := step) (d := n) (P := [])
          (g := ⟨s, Γ, .var x (Γ.lookup x) T⟩) (t := ⟨n, false⟩) (x := f) (by rw [hr])
        rw [hr] at this
        exact this
  have := (varF_framed Γ x T).shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  change (varF Γ x T ⟨m, false⟩).1 = some e
  rw [this]

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

Each check runs in the kernel at the default fuel.  `answers` and `rejects`
state the units used.  `fnTop 9` is the method type `{def 9(y : ⊤) : ⊤}`. -/

section SubChecks

/-- `z.A`, at the self of a method's parameter. -/
abbrev zA : Ty [] ([],x) := .TSel (.abs .here) 1

/-- `{C : ⊥..⊤} ∨ ⊤`. -/
abbrev Cod {s : Sig} : Ty [] s := .TOr (.TTyp 0 .TBot .TTop) .TTop

/-- A self whose member is an intersection of two copies of itself:
`z : {A : z.A ∧ z.A..z.A ∧ z.A} ∧ {def 0(x : z.A) : Cod} ∧ ⊤`. -/
abbrev selfZ : Ty [] ([],x) :=
  .TAnd (.TTyp 1 (.TAnd zA zA) (.TAnd zA zA)) (.TAnd (.TFun 0 zA Cod) .TTop)

/-- The method's parameter `x : z.A`, under the self `z`. -/
abbrev Γz2 : Ctx [] ([],x,x) := (Ctx.nil.cons selfZ).cons zA.weaken

/-- `m : {L : μ(w. {A : ⊤..⊤})..μ(w. {A : ⊤..⊤})} ∧ {def 0(x : {A : ⊤..⊤}) : m.L} ∧ ⊤`. -/
abbrev selfP : Ty [] ([],x) :=
  .TAnd (.TTyp 1 (.TBind (.TTyp 0 .TTop .TTop)) (.TBind (.TTyp 0 .TTop .TTop)))
    (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TSel (.abs (.there .here)) 1)) .TTop)

/-- The method's parameter `x : {A : ⊤..⊤}`, under the self `m`. -/
abbrev Γp : Ctx [] ([],x,x) := (Ctx.nil.cons selfP).cons (Ty.TTyp 0 .TTop .TTop).weaken

/-- `x : {0 : ⊥..⊤} ∧ {1 : ⊥..x.0}`, a type that mentions its own variable. -/
def packTwoCtx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TAnd (.TTyp 0 .TBot .TTop) (.TTyp 1 .TBot (.TSel (.abs .here) 0)))

/-- `μ(w. {0 : ⊥..⊤}) ∧ μ(w. {1 : ⊥..w.0})`.  Neither part is above the
other, so the variable is packed at the recursive type of both bodies. -/
def packTwoT : Ty [] ([],x) :=
  .TAnd (.TBind (.TTyp 0 .TBot .TTop)) (.TBind (.TTyp 1 .TBot (.TSel (.abs .here) 0)))

/-- The chain of `n` aliases ends at `xn.0`. -/
def chainLast (n : Nat) : Ty [] (chainSig n) := .TSel (.abs .here) 0

/-- A loop through method binders: `p : {1 : ⊥..{def 0(y : ⊤) : p.1}}` and
`q : {1 : {def 0(y : ⊤) : q.1}..⊤}`.  `p.1 <: q.1` meets itself under the
parameter of the method at every level. -/
def lpCtx : Ctx [] ([],x,x) :=
  (Ctx.nil.cons (.TTyp 1 .TBot (.TFun 0 .TTop (.TSel (.abs (.there .here)) 1)))).cons
    (.TTyp 1 (.TFun 0 .TTop (.TSel (.abs (.there .here)) 1)) .TTop)

/-- `p.1`. -/
def lpP : Ty [] ([],x,x) := .TSel (.abs (.there .here)) 1

/-- `q.1`. -/
def lpQ : Ty [] ([],x,x) := .TSel (.abs .here) 1

/-- `r : {1 : {def 0(y : ⊤) : r.1}..⊤}`. -/
def r2R : Ty [] ([],x) := .TTyp 1 (.TFun 0 .TTop (.TSel (.abs (.there .here)) 1)) .TTop

/-- `r.1`, below `x`. -/
def r2K : Ty [] ([],x,x) := .TSel (.abs (.there .here)) 1

/-- `x : {0 : ⊥..{0 : ⊥..r.1}} ∧ {0 : ⊥..{def 0(y : ⊤) : x.0}} ∧ x.0`. -/
def r2X : Ty [] ([],x,x) :=
  .TAnd (.TTyp 0 .TBot (.TTyp 0 .TBot r2K))
    (.TAnd (.TTyp 0 .TBot (.TFun 0 .TTop (.TSel (.abs (.there .here)) 0))) (.TSel (.abs .here) 0))

/-- The context of `x.0 <: r.1`.  The only derivation goes under the
method's parameter to the same goal, where the lookup of `x` finds the member
`{0 : ⊥..r.1}`. -/
def r2Ctx : Ctx [] ([],x,x) := (Ctx.nil.cons r2R).cons r2X

/-- `y : {0 : ⊥..μ(z. {1 : ⊥..z.1})}`. -/
def r3Ctx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TTyp 0 .TBot (.TBind (.TTyp 1 .TBot (.TSel (.abs .here) 1))))

/-- `μ(z. y.0)`, a recursive type whose self is unused. -/
def r3S : Ty [] ([],x) := .TBind (.TSel (.abs (.there .here)) 0)

/-- `μ(z. {1 : ⊥..z.1})`. -/
def r3T : Ty [] ([],x) := .TBind (.TTyp 1 .TBot (.TSel (.abs .here) 1))

section

open Oopsla16.Examples.FunctionField (Sbody Tbody Γz A B)

-- `recursive`: `μz. S(z) <: μz. T(z)` by `stp_bindx`.  The converse is rejected.
example : answers (sub? Ctx.nil (.TBind Sbody) (.TBind Tbody)) 55 = true := by decide +kernel
example : rejects (sub? Ctx.nil (.TBind Tbody) (.TBind Sbody)) 8 = true := by decide +kernel
-- `selUnder`: `z.A <: z.B` under the method's parameter.
example : answers (sub? (Γz.cons .TTop) (.TSel (.abs (.there .here)) A)
    (.TSel (.abs (.there .here)) B)) 25 = true := by decide +kernel

end

-- `RecursiveArg`: `⊤ <: z.A`, by `stp_sel2` twice.
example : answers (sub? FCdotR.SourceSafety.RecursiveArg.Γf .TTop
    FCdotR.SourceSafety.RecursiveArg.zA) 44 = true := by decide +kernel

section

open FCdotR.CheckerExamples.PaperLst (Γn PNil Γ2t P3)

-- The `nil` cell of the paper's list below `m.List`.
example : answers (sub? Γn (.TBind PNil) (.TSel (.abs (.there .here)) 0)) 147 = true := by
  decide +kernel
-- The `cons` cell below `m.List`.
example : answers (sub? Γ2t (.TBind P3)
    (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)) 497 = true := by
  decide +kernel

end

-- A repeated selection: `stp_or21` fails on `z.A`, then `stp_or22` closes by `⊤`.
example : answers (sub? Γz2 (Γz2.lookup .here) Cod) 27 = true := by decide +kernel

-- D1: the method type of a self with six members, through six intersections.
example : answers (sub? deepCtx (.TSel (.abs .here) 0) (fnTop 9)) 58 = true := by decide +kernel

-- D2: chains of 10, 16 and 32 aliases.
example : answers (sub? (chainCtx 10) (chainLast 10) (fnTop 9)) 89 = true := by decide +kernel
example : answers (sub? (chainCtx 16) (chainLast 16) (fnTop 9)) 188 = true := by decide +kernel
example : answers (sub? (chainCtx 32) (chainLast 32) (fnTop 9)) 628 = true := by decide +kernel

-- `packSel`: the parameter below a selection whose lower bound is recursive.
example : answers (var? Γp .here (.TSel (.abs (.there .here)) 1)) 17 = true := by decide +kernel
-- `packAnd`: the parameter below an intersection with a recursive part.
example : answers (var? Γp .here (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop)) 14 = true := by
  decide +kernel
-- Packing at the recursive type of both bodies, by `vAndPack`.
example : answers (var? packTwoCtx .here packTwoT) 59 = true := by decide +kernel

-- R3: two recursive types, the left self unused, by `stp_bind1`, also as codomains.
example : answers (sub? r3Ctx r3S r3T) 42 = true := by decide +kernel
example : answers (sub? r3Ctx (.TFun 0 .TTop r3S.weaken) (.TFun 0 .TTop r3T.weaken)) 54 = true := by
  decide +kernel

-- The alias cycle: no method type, with the tank unmarked.  The two aliases are related.
example : rejects (sub? cycCtx (.TSel (.abs .here) 1) (fnTop 9)) 28 = true := by decide +kernel
example : answers (sub? cycCtx (.TSel (.abs .here) 1) (.TSel (.abs .here) 0)) 14 = true := by
  decide +kernel

-- LP: the loop through method binders ends with the tank marked.
example : (sub? lpCtx lpP lpQ).2.out = true := by decide +kernel

-- R2: the member `{0 : ⊥..r.1}` lies behind `x.0` in the type of `x` itself, so
-- the lookup of `x` cuts it at every depth.  The search goes under the
-- method's parameter at every level and ends with the tank marked.
example : (sub? r2Ctx (.TSel (.abs .here) 0) r2K).2.out = true := by decide +kernel

end SubChecks

end Oopsla16Frontend.Core
