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
and `D_Fun` conclude.  A method whose result is neither written nor inherited
is not typed here, and the literal is a mismatch.

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
its parent. -/
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
        | some T => Fu.bind (fillDmsF (Γ.cons T) ds T) fun r => Fu.ret (r.map (.obj (some T) ·))
        | none =>
            Fu.bind (readGoalF Γ g ds) fun rd =>
              match headsOf (paramFrom rd) (resultFrom rd) ds with
              | .error e => Fu.ret (.error e)
              | .ok hs =>
                  match fullSelf hs [] with
                  | none => Fu.ret (.error .mismatch)
                  | some T =>
                      Fu.bind (fillDmsF (Γ.cons T) ds T) fun r => Fu.ret (r.map (.obj (some T) ·))
termination_by structural a

/-- Fill the members of a literal against its self type, in lockstep.  A method
body is filled with the method's declared result as its goal. -/
def fillDmsF {s : Sig} (Γ : Ctx [] s) (ds : ADms s) (T : Ty [] s) : Fu (FillR (ADms s)) :=
  match ds, T with
  | .dnil, _ => Fu.ret (.ok .dnil)
  | .dcons (.dty T') ds', .TAnd _ TS =>
      Fu.bind (fillDmsF Γ ds' TS) fun r => Fu.ret (r.map (.dcons (.dty T')))
  | .dcons (.dfun o1 o2 t) ds', .TAnd (.TFun _ T11 T12) TS =>
      Fu.bind (fillDmsF Γ ds' TS) fun r =>
        match r with
        | .error e => Fu.ret (.error e)
        | .ok ds'' =>
            Fu.bind (fillAtF (Γ.cons T11.weaken) T12 t (fun g' => fillF (Γ.cons T11.weaken) g' t))
              fun r' => Fu.ret (r'.map fun t' => .dcons (.dfun o1 o2 t') ds'')
  | _, _ => Fu.ret (.error .mismatch)
termination_by structural ds

end

/-! ## The elaborator: fill, then the typer -/

/-- A filled term with the typer's candidates for it. -/
abbrev Filled {s : Sig} (Γ : Ctx [] s) : Type := (a : ATm s) × List (Cand Γ a.erase)

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

end InferChecks

end Oopsla16Frontend
