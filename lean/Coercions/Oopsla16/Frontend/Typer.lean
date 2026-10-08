import Coercions.Oopsla16.Frontend.Search
import Coercions.Oopsla16.Frontend.Resolve

/-!
# The typer

A bidirectional typer for annotated terms.  It returns derivations of
`Oopsla16.HasType` and `Oopsla16.DmsHasType`, so it is sound by its result
type.  Typing in this calculus is undecidable, and the typer is incomplete.

* `synth? b n Γ a` synthesizes a type of `a`.
* `check? b n Γ a T` checks `a` at `T`.
* `checkDms? b n Γ ds T` checks a member list against a self type.
* `checkVar? b k Γ x T` checks a variable with `k` levels of packing.

The typer fuel `n` drops by one at every subterm.  The subtyping search runs
at fuel `b.sub`, and the view closures at `b.views` rounds.

## Variables

The views of a variable are the types the typer derives for it without a goal.
They start with its recorded type (`T_Varz`).  Each round applies
`T_VarUnpack` at a recursive type, `stp_and11` and `stp_and12` at an
intersection, and `stp_sel1` at a selection `y.L`, whose upper bound comes
from a view of `y` (`Search.lean`).  So a recursive type is opened wherever it
appears, also below an intersection or behind a selection.

`checkVar?` first looks for a view equal to the goal or below it.  Then it
packs: for a recursive type `μ U` in the goal, in either side of an
intersection or union, or as the lower bound of a selection `y.L`, it checks
the variable at `U` opened at the variable, and `T_VarPack` closes it.  The
search then relates the packed type to the goal.

## Calls

`t.l(u)` synthesizes `t` at `V` and `u` at `A`, then looks for a method type
`{def l(x : S) : U}` of the receiver.  The candidates are its method members at
`l`, those of either side of an intersection or union, and those of the body of
a recursive type that do not mention its self.  A variable receiver offers the
candidates of each of its views.  The widening candidate `{def l(x : A) : ⊤}`
comes last.  The search decides each candidate, using `stp_or1` for a union,
`stp_bot` for `⊥`, `stp_sel1` for a selection and `stp_bind1` for a recursive
type.

A candidate gives the call a result type by the first rung that applies.

1. The argument is a variable `y`: `T_AppVar`, result `U` opened at `y`.
2. `U` does not mention the parameter: `T_App`, result `U` strengthened.
3. Narrowing.  Expose the argument's type `A`: its body when `A = μ X` and `X`
   does not mention the self, else `A`.  Replace each selection `x.L` on the
   parameter in `U` by the bound of `L` in the exposed type `A'`, the upper
   bound at a covariant position and the lower one at a contravariant one.
   If the result no longer mentions the parameter, ask the search for the
   candidate below `{def l(x : A') : U₁}` and apply `T_App`.
4. `T_App` at `⊤`, through `stp_fun` with `stp_top`.

The replacement in rung 3 is a guess that the search checks, so it adds no
proof obligation.  In checking mode there is one more rung between 3 and 4,
with the goal as the codomain.  Each rung's result is checked against the goal,
and a failure moves on to the next rung and candidate.  After the widening
candidate, a last candidate takes the goal as its codomain.

## Fuel monotonicity

Candidates, rungs and `checkVar?` call the search and the view closures, never
the typer.  A call depends on the typer only through the types of receiver and
argument, and a synthesized type does not change with more fuel
(`synth?_le_ty`).  So more fuel never loses an answer.  One induction over the
three typer functions proves it (`TyperLe`, `typerStep_le`).

Nothing here is part of the metatheory.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Tm Dm Dms Ctx Store Stp Htp HasType DmsHasType EqSome
  scopeUpTo renameUpTo varUpTo)

/-! ## Closing a typing at a goal -/

/-- A typing at `S` becomes one at `T` when they are equal, or by `T_Sub` when
the search relates them. -/
def closeTo (b : Budget) {s : Sig} (Γ : Ctx [] s) (t : Tm [] s) (S T : Ty [] s) :
    Option (HasType Store.nil Γ t S → HasType Store.nil Γ t T) :=
  if h : S = T then some fun d => h ▸ d
  else (sub? b b.sub Γ S T).map fun e d => .T_Sub d e

/-! ## The views of a variable -/

/-- A type of a variable, with its derivation. -/
structure TView {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) where
  /-- The type. -/
  ty : Ty [] s
  /-- The derivation. -/
  deriv : HasType Store.nil Γ (.tvar (.abs x)) ty

/-- Drop views whose type is in `seen` or earlier in the list. -/
def dedupTViewsFrom {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (seen : List (Ty [] s))
    (l : List (TView Γ x)) : List (TView Γ x) :=
  match l with
  | [] => []
  | v :: vs =>
      if tyMem? v.ty seen then dedupTViewsFrom seen vs
      else v :: dedupTViewsFrom (v.ty :: seen) vs
termination_by structural l

/-- The selection step: a view `y.L` of `x` and a view of `y` with a member `L`
give `x` the member's upper bound. -/
def tselAt {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {y : BVar s .var} {l : Lb}
    (d : HasType Store.nil Γ (.tvar (.abs x)) (.TSel (.abs y) l)) (w : HView Γ y) :
    Option (TView Γ x) :=
  match w with
  | ⟨.TTyp l' lo hi, e⟩ =>
      if hl : l' = l then
        some ⟨hi.rename (renameUpTo y), .T_Sub d (.stp_sel1 (hl ▸ lowerBot (lo := lo) e))⟩
      else none
  | _ => none

/-- The views one step from a view.  `k` is the number of closure rounds used
at a selection. -/
def tstep (k : Nat) {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (v : TView Γ x) :
    List (TView Γ x) :=
  match v with
  | ⟨.TBind _, d⟩ => [⟨_, .T_VarUnpack d⟩]
  | ⟨.TAnd A B, d⟩ =>
      [⟨A, .T_Sub d (.stp_and11 (Oopsla16.Stp.refl A))⟩,
       ⟨B, .T_Sub d (.stp_and12 (Oopsla16.Stp.refl B))⟩]
  | ⟨.TSel (.abs y) _, d⟩ => (hviews k Γ y).filterMap (tselAt d)
  | _ => []

/-- The views of `x` after `r` rounds, without duplicate types. -/
def tviews (k r : Nat) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) : List (TView Γ x) :=
  match r with
  | 0 => [⟨Γ.lookup x, .T_Varz⟩]
  | r + 1 => tround k (tviews k r Γ x)
termination_by structural r
where
  /-- One round: every view, one step from each, without duplicates. -/
  tround (k : Nat) {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (vs : List (TView Γ x)) :
      List (TView Γ x) :=
    dedupTViewsFrom [] (vs ++ vs.flatMap (tstep k))

/-! ## Checking a variable -/

/-- The bodies a variable can be packed at for a goal: a recursive type in the
goal, in either side of an intersection or union, or as the lower bound of a
selection in a view of its receiver. -/
def packTargets (b : Budget) {s : Sig} (Γ : Ctx [] s) (T : Ty [] s) : List (Ty [] (s,x)) :=
  match T with
  | .TBind U => [U]
  | .TAnd A B => packTargets b Γ A ++ packTargets b Γ B
  | .TOr A B => packTargets b Γ A ++ packTargets b Γ B
  | .TSel (.abs y) l => (hviews b.views Γ y).flatMap fun w =>
      match w.ty with
      | .TTyp l' lo _ =>
          if l' = l then
            match lo.rename (renameUpTo y) with
            | .TBind U => [U]
            | _ => []
          else []
      | _ => []
  | _ => []
termination_by structural T

/-- A view of the variable that equals the goal or is below it. -/
def checkVarViews (b : Budget) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) :
    Option (HasType Store.nil Γ (.tvar (.abs x)) T) :=
  firstSome (fun v => (closeTo b Γ _ v.ty T).map fun f => f v.deriv) (tviews b.views b.views Γ x)

/-- Check a variable at a goal: its views first, then packing, with `k` levels
of packing. -/
def checkVar? (b : Budget) (k : Nat) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] s) :
    Option (HasType Store.nil Γ (.tvar (.abs x)) T) :=
  match k with
  | 0 => checkVarViews b Γ x T
  | k + 1 =>
      checkVarViews b Γ x T <|>
        firstSome (fun U => (checkVar? b k Γ x (U.substVr (.abs x))).bind fun h =>
            (closeTo b Γ _ (.TBind U) T).map fun f => f (.T_VarPack h))
          (packTargets b Γ T)
termination_by structural k

/-! ## Method candidates -/

/-- The components of an intersection, left to right. -/
def andParts {s : Sig} (T : Ty [] s) : List (Ty [] s) :=
  match T with
  | .TAnd A B => andParts A ++ andParts B
  | T => [T]
termination_by structural T

/-- The method types at `l` read off a type: a method member, those of either
side of an intersection or union, and those of the body of a recursive type
that do not mention its self. -/
def methodCands (l : Lb) {s : Sig} (V : Ty [] s) : List (Ty [] s × Ty [] (s,x)) :=
  match V with
  | .TFun l' S U => if l' = l then [(S, U)] else []
  | .TAnd A B => methodCands l A ++ methodCands l B
  | .TOr A B => methodCands l A ++ methodCands l B
  | .TBind X => (andParts X).flatMap fun P =>
      match FCdotR.Ty.strengthen? P with
      | some (.TFun l' S U) => if l' = l then [(S, U)] else []
      | _ => []
  | _ => []
termination_by structural V

/-! ## Narrowing a codomain to the argument -/

/-- The body of a recursive type that does not mention its self, else the
type itself. -/
def expose {s : Sig} (A : Ty [] s) : Ty [] s :=
  match A with
  | .TBind X =>
      match FCdotR.Ty.strengthen? X with
      | some X0 => X0
      | none => .TBind X
  | _ => A

/-- The bound of the type member `L` among the components of an intersection,
the upper one when `upper` holds. -/
def boundOf? {s : Sig} (A : Ty [] s) (L : Lb) (upper : Bool) : Option (Ty [] s) :=
  firstSome (fun P => match P with
    | .TTyp L' lo hi => if L' = L then some (if upper then hi else lo) else none
    | _ => none) (andParts A)

/-- The replacement under one more binder: weakened, and none for the new
binder. -/
def liftBnd {s : Sig} (bnd : BVar s .var → Lb → Bool → Option (Ty [] s)) :
    BVar (s,x) .var → Lb → Bool → Option (Ty [] (s,x)) :=
  fun v L p =>
    match v with
    | .here => none
    | .there y => (bnd y L p).map Ty.weaken

/-- Replace each selection `y.L` that `bnd` names by its bound.  `pos` holds at
a covariant position and selects the upper bound.  Polarity flips at a method's
domain and at a type member's lower bound. -/
def narrowTy {s : Sig} (bnd : BVar s .var → Lb → Bool → Option (Ty [] s)) (pos : Bool)
    (T : Ty [] s) : Ty [] s :=
  match T with
  | .TBot => .TBot
  | .TTop => .TTop
  | .TFun l S U => .TFun l (narrowTy bnd (!pos) S) (narrowTy (liftBnd bnd) pos U)
  | .TTyp l lo hi => .TTyp l (narrowTy bnd (!pos) lo) (narrowTy bnd pos hi)
  | .TSel (.abs y) L =>
      match bnd y L pos with
      | some B => B
      | none => .TSel (.abs y) L
  | .TSel p L => .TSel p L
  | .TBind X => .TBind (narrowTy (liftBnd bnd) pos X)
  | .TAnd A B => .TAnd (narrowTy bnd pos A) (narrowTy bnd pos B)
  | .TOr A B => .TOr (narrowTy bnd pos A) (narrowTy bnd pos B)
termination_by structural T

/-- Replace a selection on a method's parameter by the bound in the exposed
argument type `A'`. -/
def paramBnd {s : Sig} (A' : Ty [] s) : BVar (s,x) .var → Lb → Bool → Option (Ty [] (s,x)) :=
  fun v L p =>
    match v with
    | .here => (boundOf? A' L p).map Ty.weaken
    | .there _ => none

/-! ## Calls -/

/-- A call typed at `R`, from typings of receiver at `V` and argument at `A`. -/
abbrev CallFin {s : Sig} (Γ : Ctx [] s) (te ue : Tm [] s) (l : Lb) (V A R : Ty [] s) : Type :=
  HasType Store.nil Γ te V → HasType Store.nil Γ ue A → HasType Store.nil Γ (.tapp te l ue) R

/-- A typing of the receiver at another type. -/
structure RView {s : Sig} (Γ : Ctx [] s) (te : Tm [] s) (V : Ty [] s) where
  /-- The other type. -/
  ty : Ty [] s
  /-- The typing at it. -/
  recv : HasType Store.nil Γ te V → HasType Store.nil Γ te ty

/-- The typings candidates are read off: the views of a variable, or the
synthesized type of any other term. -/
def recvViews (b : Budget) {s : Sig} (Γ : Ctx [] s) (t : ATm s) (V : Ty [] s) :
    List (RView Γ t.erase V) :=
  match t with
  | .var x => (tviews b.views b.views Γ x).map fun v => ⟨v.ty, fun _ => v.deriv⟩
  | _ => [⟨V, id⟩]

/-- A method type of the receiver at `l`, validated by the search. -/
structure Cand {s : Sig} (Γ : Ctx [] s) (te : Tm [] s) (l : Lb) (V : Ty [] s) where
  /-- The domain. -/
  dom : Ty [] s
  /-- The codomain, under the parameter. -/
  cod : Ty [] (s,x)
  /-- The receiver at the method type. -/
  recv : HasType Store.nil Γ te V → HasType Store.nil Γ te (.TFun l dom cod)

/-- Validate a method type for a typing of the receiver. -/
def withCand (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} {l : Lb} {V : Ty [] s}
    (rv : RView Γ te V) (S : Ty [] s) (U : Ty [] (s,x)) : Option (Cand Γ te l V) :=
  (closeTo b Γ te rv.ty (.TFun l S U)).map fun f => ⟨S, U, fun ht => f (rv.recv ht)⟩

/-- Rung 1, `T_AppVar` at a variable argument. -/
def rungVar (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (u : ATm s) {l : Lb}
    {V A : Ty [] s} (c : Cand Γ te l V) : Option ((R : Ty [] s) × CallFin Γ te u.erase l V A R) :=
  match u with
  | .var y => (checkVar? b b.views Γ y c.dom).map fun hy =>
      ⟨c.cod.substVr (.abs y), fun ht _ => .T_AppVar (c.recv ht) hy⟩
  | _ => none

/-- Rung 2, `T_App` at a codomain that does not mention the parameter. -/
def rungWeak (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (ue : Tm [] s) {l : Lb}
    {V : Ty [] s} (A : Ty [] s) (c : Cand Γ te l V) :
    Option ((R : Ty [] s) × CallFin Γ te ue l V A R) :=
  match FCdotR.Ty.strengthenW? c.cod with
  | some ⟨U0, hU⟩ => (closeTo b Γ ue A c.dom).map fun g =>
      ⟨U0, fun ht hu => .T_App (T1 := c.dom) (T2 := U0) (hU ▸ c.recv ht) (g hu)⟩
  | none => none

/-- Rung 3, `T_App` at the codomain narrowed to the exposed argument type. -/
def rungNarrow (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (ue : Tm [] s) {l : Lb}
    {V : Ty [] s} (A : Ty [] s) (c : Cand Γ te l V) :
    Option ((R : Ty [] s) × CallFin Γ te ue l V A R) :=
  (closeTo b Γ ue A (expose A)).bind fun gA =>
    match FCdotR.Ty.strengthen? (narrowTy (paramBnd (expose A)) true c.cod) with
    | some U0 =>
        (closeTo b Γ te (.TFun l c.dom c.cod) (.TFun l (expose A) U0.weaken)).map fun e =>
          ⟨U0, fun ht hu => .T_App (e (c.recv ht)) (gA hu)⟩
    | none => none

/-- The checking rung, `T_App` with the goal as the codomain. -/
def rungGoal (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (ue : Tm [] s) {l : Lb}
    {V : Ty [] s} (A G : Ty [] s) (c : Cand Γ te l V) :
    Option ((R : Ty [] s) × CallFin Γ te ue l V A R) :=
  (closeTo b Γ ue A (expose A)).bind fun gA =>
    (closeTo b Γ te (.TFun l c.dom c.cod) (.TFun l (expose A) G.weaken)).map fun e =>
      ⟨G, fun ht hu => .T_App (e (c.recv ht)) (gA hu)⟩

/-- Rung 4, `T_App` at `⊤`. -/
def rungTop (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (ue : Tm [] s) {l : Lb}
    {V : Ty [] s} (A : Ty [] s) (c : Cand Γ te l V) :
    Option ((R : Ty [] s) × CallFin Γ te ue l V A R) :=
  (closeTo b Γ ue A c.dom).map fun g =>
    ⟨.TTop, fun ht hu => .T_App (T1 := c.dom) (T2 := .TTop)
      (.T_Sub (c.recv ht) (.stp_fun (Oopsla16.Stp.refl c.dom) .stp_top)) (g hu)⟩

/-- The rungs of a candidate in synthesis, in order. -/
def rungsSynth (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (u : ATm s) {l : Lb}
    {V : Ty [] s} (A : Ty [] s) (c : Cand Γ te l V) :
    Option ((R : Ty [] s) × CallFin Γ te u.erase l V A R) :=
  rungVar b Γ u c <|> rungWeak b Γ u.erase A c <|> rungNarrow b Γ u.erase A c
    <|> rungTop b Γ u.erase A c

/-- A call gets the result type of the first candidate with a rung that
applies. -/
def callSynth (b : Budget) {s : Sig} (Γ : Ctx [] s) (t u : ATm s) (l : Lb) (V A : Ty [] s) :
    Option ((R : Ty [] s) × CallFin Γ t.erase u.erase l V A R) :=
  firstSome (fun rv => firstSome (fun (p : Ty [] s × Ty [] (s,x)) =>
      (withCand b Γ rv p.1 p.2).bind (rungsSynth b Γ u A)) (methodCands l rv.ty))
    (recvViews b Γ t V)
  <|> (withCand b Γ ⟨V, id⟩ A .TTop).bind (rungsSynth b Γ u A)

/-- A rung followed by a check of its result against the goal. -/
def closeCall (b : Budget) {s : Sig} (Γ : Ctx [] s) {te ue : Tm [] s} {l : Lb} {V A : Ty [] s}
    (G : Ty [] s) (o : Option ((R : Ty [] s) × CallFin Γ te ue l V A R)) :
    Option (CallFin Γ te ue l V A G) :=
  o.bind fun p => (closeTo b Γ (.tapp te l ue) p.1 G).map fun k ht hu => k (p.2 ht hu)

/-- The rungs of a candidate in checking, each closed at the goal. -/
def rungsCheck (b : Budget) {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (u : ATm s) {l : Lb}
    {V : Ty [] s} (A G : Ty [] s) (c : Cand Γ te l V) : Option (CallFin Γ te u.erase l V A G) :=
  closeCall b Γ G (rungVar b Γ u c) <|> closeCall b Γ G (rungWeak b Γ u.erase A c)
    <|> closeCall b Γ G (rungNarrow b Γ u.erase A c) <|> closeCall b Γ G (rungGoal b Γ u.erase A G c)
    <|> closeCall b Γ G (rungTop b Γ u.erase A c)

/-- A call checked at a goal tries the candidates and their rungs until one
result meets the goal, then the widening candidate, then the candidate with
the goal as its codomain. -/
def callCheck (b : Budget) {s : Sig} (Γ : Ctx [] s) (t u : ATm s) (l : Lb) (V A G : Ty [] s) :
    Option (CallFin Γ t.erase u.erase l V A G) :=
  firstSome (fun rv => firstSome (fun (p : Ty [] s × Ty [] (s,x)) =>
      (withCand b Γ rv p.1 p.2).bind (rungsCheck b Γ u A G)) (methodCands l rv.ty))
    (recvViews b Γ t V)
  <|> (withCand b Γ ⟨V, id⟩ A .TTop).bind (rungsCheck b Γ u A G)
  <|> (withCand b Γ ⟨V, id⟩ (expose A) G.weaken).bind (rungsCheck b Γ u A G)

/-! ## The typer -/

/-- The three typer functions at one fuel, the form in which the rules receive
their recursive calls. -/
structure Typer where
  /-- Synthesis. -/
  synth : ∀ {s : Sig} (Γ : Ctx [] s) (a : ATm s),
    Option ((T : Ty [] s) × HasType Store.nil Γ a.erase T)
  /-- Checking. -/
  check : ∀ {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s),
    Option (HasType Store.nil Γ a.erase T)
  /-- Checking a member list against a self type. -/
  checkDms : ∀ {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s),
    Option (DmsHasType Store.nil Γ ds.erase T)

/-- The typer at fuel `0`, which finds nothing. -/
def typerNone : Typer where
  synth _ _ := none
  check _ _ _ := none
  checkDms _ _ _ := none

/-- `T_Obj` at the written self type, or else at the one `selfOf?` computes. -/
def synthObj (r : Typer) {s : Sig} (Γ : Ctx [] s) (o : Option (Ty [] (s,x))) (ds : ADms (s,x)) :
    Option ((T : Ty [] s) × HasType Store.nil Γ (ATm.obj o ds).erase T) :=
  match o <|> selfOf? ds.erase with
  | some T => (r.checkDms (Γ.cons T) ds T).map fun d => ⟨.TBind T, .T_Obj d⟩
  | none => none

/-- A call in synthesis. -/
def synthApp (b : Budget) (r : Typer) {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) (u : ATm s) :
    Option ((T : Ty [] s) × HasType Store.nil Γ (ATm.app t l u).erase T) :=
  (r.synth Γ t).bind fun p => (r.synth Γ u).bind fun q =>
    (callSynth b Γ t u l p.1 q.1).map fun c => ⟨c.1, c.2 p.2 q.2⟩

/-- Synthesis, one clause per term former. -/
def synthRules (b : Budget) (r : Typer) {s : Sig} (Γ : Ctx [] s) (a : ATm s) :
    Option ((T : Ty [] s) × HasType Store.nil Γ a.erase T) :=
  match a with
  | .var x => some ⟨Γ.lookup x, .T_Varz⟩
  | .obj o ds => synthObj r Γ o ds
  | .app t l u => synthApp b r Γ t l u
  | .asc a' T => (r.check Γ a' T).map fun h => ⟨T, h⟩

/-- Checking a literal: synthesis, then the goal. -/
def checkObj (b : Budget) (r : Typer) {s : Sig} (Γ : Ctx [] s) (o : Option (Ty [] (s,x)))
    (ds : ADms (s,x)) (T : Ty [] s) : Option (HasType Store.nil Γ (ATm.obj o ds).erase T) :=
  (synthObj r Γ o ds).bind fun p => (closeTo b Γ _ p.1 T).map fun f => f p.2

/-- A call in checking. -/
def checkApp (b : Budget) (r : Typer) {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) (u : ATm s)
    (T : Ty [] s) : Option (HasType Store.nil Γ (ATm.app t l u).erase T) :=
  (r.synth Γ t).bind fun p => (r.synth Γ u).bind fun q =>
    (callCheck b Γ t u l p.1 q.1 T).map fun f => f p.2 q.2

/-- Checking, one clause per term former. -/
def checkRules (b : Budget) (r : Typer) {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) :
    Option (HasType Store.nil Γ a.erase T) :=
  match a with
  | .var x => checkVar? b b.views Γ x T
  | .obj o ds => checkObj b r Γ o ds T
  | .app t l u => checkApp b r Γ t l u T
  | .asc a' T' => (r.check Γ a' T').bind fun h => (closeTo b Γ _ T' T).map fun f => f h

/-- The member list against the self type, in lockstep: `D_Nil`, `D_Typ` and
`D_Fun`.  A method's types come from the self type, so a Curry style method
checks. -/
def checkDmsRules (r : Typer) {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s) :
    Option (DmsHasType Store.nil Γ ds.erase T) :=
  match ds, T with
  | .dnil, .TTop => some .D_Nil
  | .dcons (.dty T') ds', .TAnd (.TTyp l T1 T2) TS => checkTyp r Γ T' ds' l T1 T2 TS
  | .dcons (.dfun o1 o2 t) ds', .TAnd (.TFun l T11 T12) TS => checkFun r Γ o1 o2 t ds' l T11 T12 TS
  | _, _ => none
where
  /-- `D_Typ`: the label is the position and both bounds are the member. -/
  checkTyp (r : Typer) {s : Sig} (Γ : Ctx [] s) (T' : Ty [] s) (ds' : ADms s) (l : Lb)
      (T1 T2 TS : Ty [] s) :
      Option (DmsHasType Store.nil Γ (ADms.dcons (.dty T') ds').erase (.TAnd (.TTyp l T1 T2) TS)) :=
    if h : l = ds'.erase.length ∧ T1 = T' ∧ T2 = T' then
      (r.checkDms Γ ds' TS).map fun d => by
        obtain ⟨h1, h2, h3⟩ := h
        subst h1 h2 h3
        exact .D_Typ d
    else none
  /-- `D_Fun`: the label is the position, the annotations agree with the self
  type, and the body checks at the codomain under the parameter. -/
  checkFun (r : Typer) {s : Sig} (Γ : Ctx [] s) (o1 : Option (Ty [] s)) (o2 : Option (Ty [] (s,x)))
      (t : ATm (s,x)) (ds' : ADms s) (l : Lb) (T11 : Ty [] s) (T12 : Ty [] (s,x)) (TS : Ty [] s) :
      Option (DmsHasType Store.nil Γ (ADms.dcons (.dfun o1 o2 t) ds').erase
        (.TAnd (.TFun l T11 T12) TS)) :=
    if h : l = ds'.erase.length ∧ EqSome o1 T11 ∧ EqSome o2 T12 then
      (r.checkDms Γ ds' TS).bind fun d => (r.check (Γ.cons T11.weaken) t T12).map fun hb => by
        obtain ⟨h1, e1, e2⟩ := h
        subst h1
        exact .D_Fun d hb e1 e2
    else none

/-- One more unit of fuel: the rules over the typer one fuel lower. -/
def typerStep (b : Budget) (r : Typer) : Typer where
  synth Γ a := synthRules b r Γ a
  check Γ a T := checkRules b r Γ a T
  checkDms Γ ds T := checkDmsRules r Γ ds T

/-- The typer at fuel `n`. -/
def typerAt (b : Budget) (n : Nat) : Typer :=
  match n with
  | 0 => typerNone
  | n + 1 => typerStep b (typerAt b n)
termination_by structural n

/-- Synthesis at fuel `n`. -/
def synth? (b : Budget) (n : Nat) {s : Sig} (Γ : Ctx [] s) (a : ATm s) :
    Option ((T : Ty [] s) × HasType Store.nil Γ a.erase T) :=
  (typerAt b n).synth Γ a

/-- Checking at fuel `n`. -/
def check? (b : Budget) (n : Nat) {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) :
    Option (HasType Store.nil Γ a.erase T) :=
  (typerAt b n).check Γ a T

/-- Checking a member list at fuel `n`. -/
def checkDms? (b : Budget) (n : Nat) {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s) :
    Option (DmsHasType Store.nil Γ ds.erase T) :=
  (typerAt b n).checkDms Γ ds T

/-! ## Fuel monotonicity

`TyperLe r r'` says that `r'` keeps every answer of `r`.  A synthesized type
stays the same, and a successful check still succeeds. -/

/-- `r'` finds every answer of `r`, and synthesizes the same types. -/
def TyperLe (r r' : Typer) : Prop :=
  (∀ {s : Sig} (Γ : Ctx [] s) (a : ATm s), (r.synth Γ a).isSome = true →
      (r'.synth Γ a).map Sigma.fst = (r.synth Γ a).map Sigma.fst) ∧
  (∀ {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s),
      (r.check Γ a T).isSome = true → (r'.check Γ a T).isSome = true) ∧
  (∀ {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s),
      (r.checkDms Γ ds T).isSome = true → (r'.checkDms Γ ds T).isSome = true)

theorem TyperLe.refl (r : Typer) : TyperLe r r :=
  ⟨fun _ _ _ => rfl, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem TyperLe.trans {r₁ r₂ r₃ : Typer} (h₁ : TyperLe r₁ r₂) (h₂ : TyperLe r₂ r₃) :
    TyperLe r₁ r₃ := by
  refine ⟨fun Γ a h => ?_, fun Γ a T h => h₂.2.1 Γ a T (h₁.2.1 Γ a T h),
    fun Γ ds T h => h₂.2.2 Γ ds T (h₁.2.2 Γ ds T h)⟩
  have e₁ := h₁.1 Γ a h
  have h' : (r₂.synth Γ a).isSome = true := by
    rw [← Option.isSome_map (f := Sigma.fst), e₁, Option.isSome_map]; exact h
  rw [h₂.1 Γ a h', e₁]

/-- A dependent pair whose first component is known. -/
theorem map_fst_eq_some {α : Type} {β : α → Type} {o : Option ((a : α) × β a)} {a : α}
    (h : o.map Sigma.fst = some a) : ∃ b, o = some ⟨a, b⟩ := by
  cases o with
  | none => cases h
  | some p =>
      obtain ⟨a', b⟩ := p
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨b, rfl⟩

/-- A synthesis that succeeds at `r` gives the same type at `r'`, with some
derivation. -/
theorem synth_same {r r' : Typer} (hr : TyperLe r r') {s : Sig} {Γ : Ctx [] s} {a : ATm s}
    {T : Ty [] s} {h : HasType Store.nil Γ a.erase T} (e : r.synth Γ a = some ⟨T, h⟩) :
    ∃ h', r'.synth Γ a = some ⟨T, h'⟩ := by
  have := hr.1 Γ a (by rw [e]; rfl)
  rw [e] at this
  exact map_fst_eq_some this

section StepMono
variable {r r' : Typer} (hr : TyperLe r r')
include hr

theorem synthObj_le {s : Sig} (Γ : Ctx [] s) (o : Option (Ty [] (s,x)))
    (ds : ADms (s,x)) : (synthObj r Γ o ds).isSome = true →
      (synthObj r' Γ o ds).map Sigma.fst = (synthObj r Γ o ds).map Sigma.fst := by
  intro h
  unfold synthObj at h ⊢
  cases hT : (o <|> selfOf? ds.erase) with
  | none => rfl
  | some T =>
    simp only [hT] at h ⊢
    cases e : r.checkDms (Γ.cons T) ds T with
    | none => rw [e] at h; cases h
    | some d =>
        have e' := hr.2.2 (Γ.cons T) ds T (by rw [e]; rfl)
        cases e'' : r'.checkDms (Γ.cons T) ds T with
        | none => rw [e''] at e'; cases e'
        | some d' => rfl

theorem synthApp_le (b : Budget) {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) (u : ATm s) :
    (synthApp b r Γ t l u).isSome = true →
      (synthApp b r' Γ t l u).map Sigma.fst = (synthApp b r Γ t l u).map Sigma.fst := by
  intro h
  unfold synthApp at h ⊢
  cases e1 : r.synth Γ t with
  | none => rw [e1] at h; cases h
  | some p =>
      cases e2 : r.synth Γ u with
      | none => rw [e1, e2] at h; cases h
      | some q =>
          obtain ⟨V, ht⟩ := p
          obtain ⟨A, hu⟩ := q
          obtain ⟨ht', e1'⟩ := synth_same hr e1
          obtain ⟨hu', e2'⟩ := synth_same hr e2
          simp [e1', e2', Option.map_map, Function.comp_def]

theorem checkObj_le (b : Budget) {s : Sig} (Γ : Ctx [] s) (o : Option (Ty [] (s,x)))
    (ds : ADms (s,x)) (T : Ty [] s) :
    (checkObj b r Γ o ds T).isSome = true → (checkObj b r' Γ o ds T).isSome = true := by
  intro h
  unfold checkObj at h ⊢
  cases e : synthObj r Γ o ds with
  | none => rw [e] at h; cases h
  | some p =>
      obtain ⟨V, hv⟩ := p
      have e' := synthObj_le hr Γ o ds (by rw [e]; rfl)
      rw [e] at e'
      obtain ⟨hv', e''⟩ := map_fst_eq_some e'
      rw [e] at h
      rw [e'']
      simpa using h

theorem checkApp_le (b : Budget) {s : Sig} (Γ : Ctx [] s) (t : ATm s) (l : Lb) (u : ATm s)
    (T : Ty [] s) :
    (checkApp b r Γ t l u T).isSome = true → (checkApp b r' Γ t l u T).isSome = true := by
  intro h
  unfold checkApp at h ⊢
  cases e1 : r.synth Γ t with
  | none => rw [e1] at h; cases h
  | some p =>
      cases e2 : r.synth Γ u with
      | none => rw [e1, e2] at h; cases h
      | some q =>
          obtain ⟨V, ht⟩ := p
          obtain ⟨A, hu⟩ := q
          obtain ⟨ht', e1'⟩ := synth_same hr e1
          obtain ⟨hu', e2'⟩ := synth_same hr e2
          rw [e1, e2] at h
          rw [e1', e2']
          simpa using h

theorem synthRules_le (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) :
    (synthRules b r Γ a).isSome = true →
      (synthRules b r' Γ a).map Sigma.fst = (synthRules b r Γ a).map Sigma.fst := by
  intro h
  cases a with
  | var x => rfl
  | obj o ds => exact synthObj_le hr Γ o ds h
  | app t l u => exact synthApp_le hr b Γ t l u h
  | asc a' T =>
      simp only [synthRules] at h ⊢
      cases e : r.check Γ a' T with
      | none => rw [e] at h; cases h
      | some d =>
          have e' := hr.2.1 Γ a' T (by rw [e]; rfl)
          cases e'' : r'.check Γ a' T with
          | none => rw [e''] at e'; cases e'
          | some d' => rfl

theorem checkRules_le (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) :
    (checkRules b r Γ a T).isSome = true → (checkRules b r' Γ a T).isSome = true := by
  intro h
  cases a with
  | var x => exact h
  | obj o ds => exact checkObj_le hr b Γ o ds T h
  | app t l u => exact checkApp_le hr b Γ t l u T h
  | asc a' T' =>
      simp only [checkRules] at h ⊢
      exact bindMap_mono (hr.2.1 Γ a' T') id h

theorem checkDmsRules_le {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s) :
    (checkDmsRules r Γ ds T).isSome = true → (checkDmsRules r' Γ ds T).isSome = true := by
  have hTyp : ∀ (T' : Ty [] s) (ds' : ADms s) (l : Lb) (T1 T2 TS : Ty [] s),
      (checkDmsRules.checkTyp r Γ T' ds' l T1 T2 TS).isSome = true →
        (checkDmsRules.checkTyp r' Γ T' ds' l T1 T2 TS).isSome = true := by
    intro T' ds' l T1 T2 TS h
    unfold checkDmsRules.checkTyp at h ⊢
    by_cases hc : l = ds'.erase.length ∧ T1 = T' ∧ T2 = T'
    · rw [dif_pos hc] at h ⊢
      exact map_mono (hr.2.2 Γ ds' TS) h
    · rw [dif_neg hc] at h
      cases h
  have hFun : ∀ (o1 : Option (Ty [] s)) (o2 : Option (Ty [] (s,x))) (t : ATm (s,x)) (ds' : ADms s)
      (l : Lb) (T11 : Ty [] s) (T12 : Ty [] (s,x)) (TS : Ty [] s),
      (checkDmsRules.checkFun r Γ o1 o2 t ds' l T11 T12 TS).isSome = true →
        (checkDmsRules.checkFun r' Γ o1 o2 t ds' l T11 T12 TS).isSome = true := by
    intro o1 o2 t ds' l T11 T12 TS h
    unfold checkDmsRules.checkFun at h ⊢
    by_cases hc : l = ds'.erase.length ∧ EqSome o1 T11 ∧ EqSome o2 T12
    · rw [dif_pos hc] at h ⊢
      exact bindMap_mono (hr.2.2 Γ ds' TS) (hr.2.1 (Γ.cons T11.weaken) t T12) h
    · rw [dif_neg hc] at h
      cases h
  intro h
  cases ds with
  | dnil => cases T <;> exact h
  | dcons d ds' =>
      cases d with
      | dty T' =>
          cases T with
          | TAnd A B =>
              cases A with
              | TTyp l T1 T2 => exact hTyp T' ds' l T1 T2 B h
              | _ => exact h
          | _ => exact h
      | dfun o1 o2 t =>
          cases T with
          | TAnd A B =>
              cases A with
              | TFun l T11 T12 => exact hFun o1 o2 t ds' l T11 T12 B h
              | _ => exact h
          | _ => exact h

end StepMono

/-- The rules preserve `TyperLe`. -/
theorem typerStep_le (b : Budget) {r r' : Typer} (hr : TyperLe r r') :
    TyperLe (typerStep b r) (typerStep b r') :=
  ⟨fun Γ a h => synthRules_le hr b Γ a h, fun Γ a T h => checkRules_le hr b Γ a T h,
    fun Γ ds T h => checkDmsRules_le hr Γ ds T h⟩

/-- Every fuel is below the next. -/
theorem typerAt_succ (b : Budget) : ∀ n, TyperLe (typerAt b n) (typerAt b (n + 1))
  | 0 => by
      refine ⟨fun _ _ h => ?_, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩ <;>
        simp [typerAt, typerNone] at h
  | n + 1 => typerStep_le b (typerAt_succ b n)

/-- Every fuel is below a larger one. -/
theorem typerAt_le (b : Budget) {n n' : Nat} (h : n ≤ n') :
    TyperLe (typerAt b n) (typerAt b n') := by
  induction n' with
  | zero =>
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn
      exact TyperLe.refl _
  | succ m ih =>
      cases Nat.lt_or_ge n (m + 1) with
      | inl hlt => exact (ih (Nat.lt_succ_iff.mp hlt)).trans (typerAt_succ b m)
      | inr hge =>
          have hn : n = m + 1 := Nat.le_antisymm h hge
          subst hn
          exact TyperLe.refl _

/-- **More fuel never loses a synthesized type.** -/
theorem synth?_le {b : Budget} {n n' : Nat} (h : n ≤ n') {s : Sig} {Γ : Ctx [] s}
    {a : ATm s} : (synth? b n Γ a).isSome = true → (synth? b n' Γ a).isSome = true := by
  intro hs
  have e := (typerAt_le b h).1 Γ a hs
  unfold synth? at hs ⊢
  rw [← Option.isSome_map (f := Sigma.fst), e, Option.isSome_map]
  exact hs

/-- A synthesized type is the same at every larger fuel. -/
theorem synth?_le_ty {b : Budget} {n n' : Nat} (h : n ≤ n') {s : Sig} {Γ : Ctx [] s}
    {a : ATm s} : (synth? b n Γ a).isSome = true →
      (synth? b n' Γ a).map Sigma.fst = (synth? b n Γ a).map Sigma.fst :=
  (typerAt_le b h).1 Γ a

/-- More fuel never loses a successful check. -/
theorem check?_le {b : Budget} {n n' : Nat} (h : n ≤ n') {s : Sig} {Γ : Ctx [] s}
    {a : ATm s} {T : Ty [] s} :
    (check? b n Γ a T).isSome = true → (check? b n' Γ a T).isSome = true :=
  (typerAt_le b h).2.1 Γ a T

/-- More fuel never loses a successful check of a member list. -/
theorem checkDms?_le {b : Budget} {n n' : Nat} (h : n ≤ n') {s : Sig} {Γ : Ctx [] s}
    {ds : ADms s} {T : Ty [] s} :
    (checkDms? b n Γ ds T).isSome = true → (checkDms? b n' Γ ds T).isSome = true :=
  (typerAt_le b h).2.2 Γ ds T

/-! ## Entry points -/

/-- Synthesis in a given context at the budget's typer fuel. -/
def synthIn? (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) :
    Option ((T : Ty [] s) × HasType Store.nil Γ a.erase T) :=
  synth? b b.typer Γ a

/-- Checking in a given context at the budget's typer fuel. -/
def checkIn? (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) :
    Option (HasType Store.nil Γ a.erase T) :=
  check? b b.typer Γ a T

/-- Synthesis of a closed program. -/
def synthTop? (b : Budget) (a : ATm []) :
    Option ((T : Ty [] []) × HasType Store.nil Ctx.nil a.erase T) :=
  synthIn? b Ctx.nil a

/-- The synthesized type alone. -/
def typeIn? (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) : Option (Ty [] s) :=
  (synthIn? b Γ a).map (·.1)

/-- Whether checking succeeds. -/
def checksIn (b : Budget) {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) : Bool :=
  (checkIn? b Γ a T).isSome

/-! ## Checks

Every check runs in the kernel.  A budget is `{ views := k, sub := m, typer := n }`,
written `(k, m, n)` below.  A positive check states a budget where the answer
is found.  A negative check says nothing about other budgets.  Programs are
written in surface notation, and the synthesized type is compared with the
type the calculus's own derivation concludes. -/

namespace TyperChecks

/-- The synthesized type of a closed surface program under a label table. -/
def typeOfSrc (b : Budget) (Λ : LabelTable) (e : STm) : Option (Ty [] []) :=
  (resolve Λ e).bind (typeIn? b Ctx.nil)

/-! ### The calculus's programs -/

/-- `ex0` at `μ(z. ⊤)`, the type of `Oopsla16.Examples.ex0_precise`, at
`(0, 0, 2)`. -/
example : typeOfSrc { views := 0, sub := 0, typer := 2 } [] ex0src = some (.TBind .TTop) := by
  decide +kernel

/-- `ex0` ascribed, at `⊤`, the type of `Oopsla16.Examples.ex0`, at
`(0, 1, 3)`. -/
example : typeOfSrc { views := 0, sub := 1, typer := 3 } [] ex0AscSrc = some .TTop := by
  decide +kernel

/-- `RecursiveArg.prog` at `⊤`, the type of
`FCdotR.SourceSafety.RecursiveArg.progTy`, at `(2, 6, 6)`.  The argument goes
in by `T_App` at the strengthened codomain, and its type is below the domain
by `stp_bindx` with two `stp_sel2`. -/
example : typeOfSrc { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc = some .TTop := by
  decide +kernel

/-- `CurryCall.prog` at `⊤`, the type of `FCdotR.CurryCall.progTy`, at
`(0, 3, 7)`. -/
example : typeOfSrc { views := 0, sub := 3, typer := 7 } curryCallTable curryCallSrc
    = some .TTop := by
  decide +kernel

/-- `ex1` synthesizes the self type `selfOf?` computes, at `(0, 3, 5)`. -/
example : typeOfSrc { views := 0, sub := 3, typer := 5 } ex1Table ex1src
    = some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf) := by
  decide +kernel

/-- `ex1` checks at `polyId`, the type of `FCdotR.CheckerExamples.DotExs.ex1`,
at `(0, 3, 5)`. -/
example : ((resolve ex1Table ex1src).map fun a =>
    checksIn { views := 0, sub := 3, typer := 5 } Ctx.nil a FCdotR.CheckerExamples.DotExs.polyId)
    = some true := by
  decide +kernel

/-- `ex2`, open in `y : polyId`, synthesizes `{def apply(x : ⊤) : ⊤}`, the type
of `FCdotR.CheckerExamples.DotExs.ex2`, at `(1, 4, 4)`.  This is rung 3:
narrowing the codomain of `polyId` to the argument's exposed type
`{T : ⊤..⊤} ∧ ⊤` replaces `t.T` by `⊤`. -/
example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).bind
    (typeIn? { views := 1, sub := 4, typer := 4 } FCdotR.CheckerExamples.DotExs.Γy)
    = some (.TFun 0 .TTop .TTop) := by
  decide +kernel

/-- With no view rounds the narrowed method type is not validated, and the call
falls to rung 4 at `⊤`. -/
example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).bind
    (typeIn? { views := 0, sub := 4, typer := 4 } FCdotR.CheckerExamples.DotExs.Γy)
    = some .TTop := by
  decide +kernel

/-- `paper_lst` at its module type, the type of
`FCdotR.CheckerExamples.PaperLst.paper_lst`, at `(3, 12, 13)`. -/
example : typeOfSrc { views := 3, sub := 12, typer := 13 } paperLstTable paperLstSrc
    = some (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody) := by
  decide +kernel

/-- Not found at the default budget `(4, 8, 12)`. -/
example : typeOfSrc {} paperLstTable paperLstSrc = none := by
  decide +kernel

/-! ### Open examples

The context `Γz` of `Oopsla16.Examples.FunctionField` holds the self
`z : S(z)`. -/

section FunctionField
open Oopsla16.Examples.FunctionField (Γz A B f)

/-- `z` synthesizes its recorded type. -/
example : typeIn? {} Γz (.var .here) = some Oopsla16.Examples.FunctionField.Sbody := by
  decide +kernel

/-- `sBound`: `z` checks at `{A : ⊥..z.B}`, at `(0, 3, 1)`. -/
example : checksIn { views := 0, sub := 3, typer := 1 } Γz (.var .here)
    (.TTyp A .TBot (.TSel (.abs .here) B)) = true := by
  decide +kernel

/-- `premise`: `z` checks at `T(z)`, at `(1, 5, 1)`. -/
example : checksIn { views := 1, sub := 5, typer := 1 } Γz (.var .here)
    Oopsla16.Examples.FunctionField.Tbody = true := by
  decide +kernel

/-- `selMember`: under the parameter, the self has `{A : ⊥..z.B}` after one
round. -/
example : ((tviews 1 1 (Γz.cons .TTop) (.there .here)).any
    fun v => decide (v.ty = .TTyp A .TBot (.TSel (.abs (.there .here)) B))) = true := by
  decide +kernel

/-- A call on the self under the parameter: `z.f(x)` with `x : ⊤` has the result
`z.A`, by `T_AppVar`. -/
example : typeIn? { views := 1 } (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    = some (.TSel (.abs (.there .here)) A) := by
  decide +kernel

/-- `methodCovariant`: `z.f(x)` checks at `z.B`, by `selUnder` from the result
`z.A`. -/
example : checksIn { views := 1 } (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    (.TSel (.abs (.there .here)) B) = true := by
  decide +kernel

end FunctionField

/-! ### Unpacking below an intersection and a selection

In `paper_lst`, the innermost parameter of `cons` is
`tl : m.List ∧ {Elem : ⊥..t.T}`.  Its views split the intersection, widen
`m.List` to the list type, unpack it and split again.  So `tl.head(tl)` finds
the method `head` and answers `tl.Elem`. -/

section PaperLst
open FCdotR.CheckerExamples.PaperLst (Γ2t)

/-- `tl` has a view with the method `head` after four rounds. -/
example : ((tviews 4 4 Γ2t .here).any fun v => match v.ty with
    | .TFun 2 _ _ => true
    | _ => false) = true := by
  decide +kernel

/-- `tl.head(tl)` synthesizes `tl.Elem`, at four rounds. -/
example : typeIn? { views := 4 } Γ2t (.app (.var .here) 2 (.var .here))
    = some (.TSel (.abs .here) 0) := by
  decide +kernel

end PaperLst

/-! ### A call on a literal whose method type mentions its self

`f`'s codomain `z.A` mentions the receiver's self, so no candidate reads off
the receiver's type.  The widening candidate `{def f(x : μ(w. ⊤)) : ⊤}` is
below the receiver by `stp_bind1`, so the call types at `⊤`. -/

/-- The program. -/
def selfCallSrc : STm := o16% (new { z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤ }).f(new { w ⇒ })

/-- Its label table. -/
def selfCallTable : LabelTable := [("f", 1), ("A", 0)]

example : labelsOfProgram [] selfCallSrc = some selfCallTable := by decide

/-- At `(2, 4, 5)`. -/
example : typeOfSrc { views := 2, sub := 4, typer := 5 } selfCallTable selfCallSrc = some .TTop := by
  decide +kernel

/-- The derivation found at the default budget. -/
def selfCallFound : HasType Store.nil Ctx.nil ((resolve selfCallTable selfCallSrc).get (by decide)).erase .TTop :=
  (checkIn? {} Ctx.nil ((resolve selfCallTable selfCallSrc).get (by decide)) .TTop).get (by decide +kernel)

/-- The target checker accepts its elaboration. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabTm FCdotR.emptyStoreTy selfCallFound).tm .TTop = true := by
  decide +kernel

/-! ### A call on a variable whose type is a selection

`x : c.L` widens to `c.L`'s upper bound `{def f(y : ⊤) : ⊤}` by the selection
step of its views. -/

/-- The program.  `f` names a method of a type, so its label is an explicit
entry. -/
def selCallSrc : STm := o16% new { c ⇒ type L = { def f(y : ⊤) : ⊤ }   def g(x : c.L) : ⊤ = x.f(x) }

/-- Its label table. -/
def selCallTable : LabelTable := [("f", 0), ("L", 1), ("g", 0)]

example : labelsOfProgram [("f", 0)] selCallSrc = some selCallTable := by decide

/-- At `(1, 1, 5)`, the self type `selfC` of `Search.lean`. -/
example : typeOfSrc { views := 1, sub := 1, typer := 5 } selCallTable selCallSrc
    = some (.TBind SearchChecks.selfC) := by
  decide +kernel

/-! ### The first candidate's answer fails the goal

`x` has two method types at `f`.  The first answers `⊤`, which is not below
the goal `{A : ⊥..⊤}`, so checking moves on to the second.  The program types
whether or not the search proves the first candidate's domain. -/

/-- The program. -/
def twoCandSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤ ∧ ⊤ ∧ ⊤ ∧ ⊤) : ⊤ } ∧ { def f(y : ⊤) : { type A : ⊥ .. ⊤ } })
                   : { type A : ⊥ .. ⊤ } = x.f(x) }

/-- Its label table. -/
def twoCandTable : LabelTable := [("f", 0), ("A", 0), ("g", 0)]

example : labelsOfProgram [("f", 0), ("A", 0)] twoCandSrc = some twoCandTable := by decide

/-- `{A : ⊥..⊤}`. -/
abbrev memberA {s : Sig} : Ty [] s := .TTyp 0 .TBot .TTop
/-- `x`'s type. -/
abbrev twoMethods {s : Sig} : Ty [] s :=
  .TAnd (.TFun 0 (.TAnd .TTop (.TAnd .TTop (.TAnd .TTop .TTop))) .TTop) (.TFun 0 .TTop memberA)
/-- The literal's self type. -/
abbrev twoCandSelf : Ty [] ([],x) := .TAnd (.TFun 0 twoMethods memberA) .TTop

/-- At `(0, 2, 4)`, where the search does not prove `x`'s type below the first
domain. -/
example : typeOfSrc { views := 0, sub := 2, typer := 4 } twoCandTable twoCandSrc = some (.TBind twoCandSelf) := by
  decide +kernel

/-- At `(0, 6, 4)`, where it does. -/
example : typeOfSrc { views := 0, sub := 6, typer := 4 } twoCandTable twoCandSrc = some (.TBind twoCandSelf) := by
  decide +kernel

/-- And at `(4, 12, 20)`. -/
example : typeOfSrc { views := 4, sub := 12, typer := 20 } twoCandTable twoCandSrc
    = some (.TBind twoCandSelf) := by
  decide +kernel

/-! ### A receiver at a union and a receiver at `⊥` -/

/-- A union receiver. -/
def unionCallSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : ⊤ } ∨ { def f(y : ⊤) : ⊤ }) : ⊤ = x.f(x) }

/-- A receiver at `⊥`. -/
def botCallSrc : STm := o16% new { c ⇒ def g(x : ⊥) : ⊤ = x.f(x) }

/-- The label table of both. -/
def unionCallTable : LabelTable := [("f", 0), ("g", 0)]

example : labelsOfProgram [("f", 0)] unionCallSrc = some unionCallTable := by decide
example : labelsOfProgram [("f", 0)] botCallSrc = some unionCallTable := by decide

/-- The union receiver, through `stp_or1`, at `(0, 2, 4)`. -/
example : typeOfSrc { views := 0, sub := 2, typer := 4 } unionCallTable unionCallSrc
    = some (.TBind (.TAnd (.TFun 0 (.TOr SearchChecks.F SearchChecks.F) .TTop) .TTop)) := by
  decide +kernel

/-- The receiver at `⊥`, through `stp_bot`, at `(0, 1, 4)`. -/
example : typeOfSrc { views := 0, sub := 1, typer := 4 } unionCallTable botCallSrc
    = some (.TBind (.TAnd (.TFun 0 .TBot .TTop) .TTop)) := by
  decide +kernel

/-! ### Packing below a selection and below an intersection -/

/-- The goal is the selection `m.L`, whose lower bound is a recursive type. -/
def packSelSrc : STm :=
  o16% new { m ⇒ type L = μ(w. { type A : ⊤ .. ⊤ })   def g(x : { type A : ⊤ .. ⊤ }) : m.L = x }

/-- The goal is an intersection with a recursive type on its left. -/
def packAndSrc : STm :=
  o16% new { m ⇒ def g(x : { type A : ⊤ .. ⊤ }) : μ(w. { type A : ⊤ .. ⊤ }) ∧ ⊤ = x }

/-- The label table of the first. -/
def packSelTable : LabelTable := [("A", 0), ("L", 1), ("g", 0)]

example : labelsOfProgram [("A", 0)] packSelSrc = some packSelTable := by decide

/-- Below a selection, at `(1, 1, 4)`, the self type `selfP` of `Search.lean`. -/
example : typeOfSrc { views := 1, sub := 1, typer := 4 } packSelTable packSelSrc
    = some (.TBind SearchChecks.selfP) := by
  decide +kernel

/-- Below an intersection, at `(1, 2, 3)`. -/
example : typeOfSrc { views := 1, sub := 2, typer := 3 } [("A", 0), ("g", 0)] packAndSrc
    = some (.TBind (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop))
        .TTop)) := by
  decide +kernel

/-- `checkVar?` alone, in the method body of the first: one level of packing
reaches `m.L`. -/
example : (checkVar? { views := 1 } 1 SearchChecks.Γp .here (.TSel (.abs (.there .here)) 1)).isSome
    = true := by
  decide +kernel

/-- With no level of packing it does not. -/
example : (checkVar? { views := 4 } 0 SearchChecks.Γp .here (.TSel (.abs (.there .here)) 1)).isSome
    = false := by
  decide +kernel

/-- `checkVar?` through `∧`: one level of packing reaches `μ(w. {A : ⊤..⊤}) ∧ ⊤`. -/
example : (checkVar? { views := 1 } 1 SearchChecks.Γp .here
    (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop)).isSome = true := by
  decide +kernel

/-- The derivation found for the first, at the default budget. -/
def packSelFound : HasType Store.nil Ctx.nil ((resolve packSelTable packSelSrc).get (by decide)).erase
    (.TBind SearchChecks.selfP) :=
  (checkIn? {} Ctx.nil ((resolve packSelTable packSelSrc).get (by decide)) (.TBind SearchChecks.selfP)).get
    (by decide +kernel)

/-- The target checker accepts its elaboration. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabTm FCdotR.emptyStoreTy packSelFound).tm (.TBind SearchChecks.selfP) = true := by
  decide +kernel

end TyperChecks

end Oopsla16Frontend
