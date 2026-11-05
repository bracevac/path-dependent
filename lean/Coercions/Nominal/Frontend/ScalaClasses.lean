import Coercions.Nominal.Frontend.ScalaRead.Scope

/-!
# The classes of a Scala file: implementers, effective members, names, the checks

Plan XII, "Linearization, effective members, and the checks", for the Scala mapping of
`Frontend/Scala.lean`.  The linearization `L(K)` is the reader's (`Scope.lin`, `Scope.linOf`, Martres
p.73).  This module adds Martres' implementer `mimpl` (p.74), the class of the effective member `eff`,
the members of an instance in order (`names`), and the superclass of a class.

The checks are decided over the tree and give scalac's text.  `outcome` answers `rejected` with them
(`Outcome.checked`).  At a class, in text order: the shape of the parents (the arity of the first
parent of a class, E171, arguments to a trait parent, a class after `with`, E104, a trait after `with`
whose superclass the class's superclass does not derive from, the arguments of a superclass reached
through a first parent that is a trait, E171), OV-Accidental (Martres' `noAccidentalOverride`, Figure
5.8, p.75, E164), OV-Abstract ("needs to be abstract"), then at each own member OV-Need (E164, at a
concrete member only) and OV-Nothing (E037), then OV-Private at the first member whose type signature
names a plain parameter of the class, unless OV-Private's second walk at an alias removes the report, as
scalac's does (`checkNoPrivateLeaks`, no code).  Where OV-Private makes no second walk, it reports.  At
each `new p.K(ē)`, in text order after the classes: the arity of `new` (E171) and OV-New (E042).  A class
context whose linearization does not exist is skipped, since R-CI refuses it first.

Every function is structural, or fuelled by the number of classes of the file plus one.  The second walks
of OV-Private are fuelled by the size of the file's members plus one.  No function reads the characters
of a name.
-/

namespace NominalFrontend.Scala.Classes

open ScalaSyntax (Pos Err)
open NominalFrontend.ScalaRead (File Mems Stats Tm Args Parents CMems ClsDecl ClsKind CParam ClassRef Param)
open NominalFrontend.ScalaRead.Scope (Entry clsOf? clsKey memCls linOf parentEnvs refEnv? clsKind
  stemMems stemEnv headEnv lookup thisOf lookupTyp headTmpl? kindPath declTrm?)

/-! ## Members of a class -/

/-- Whether a class body defines the term member `a` concretely: a `val` with a right side or a `def`
with a body. -/
def bodyDefines (a : String) : CMems → Bool
  | .nil => false
  | .val _ _ b _ _ r | .defn _ _ b _ _ _ r => decide (a = b) || bodyDefines a r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .defDecl _ _ _ _ _ r => bodyDefines a r

/-- Whether a class defines the term member `a` concretely: a `val` parameter, a `val` with a right
side, a `def` with a body (Martres p.74). -/
def clsDefines (d : ClsDecl) (a : String) : Bool :=
  d.params.any (fun x => x.isVal && decide (x.name = a)) || bodyDefines a d.body

/-- Whether the class of a context declares the term member `a`: a `val` parameter or a body member. -/
def declaresAt (a : String) (e : List Entry) : Bool := ((clsOf? e).map fun d => (d.findMem a).isSome).getD false

/-- Whether the class of a context defines the term member `a` concretely. -/
def definesAt (a : String) (e : List Entry) : Bool := ((clsOf? e).map (clsDefines · a)).getD false

/-- Whether the class of a context declares the type member `A`. -/
def declaresTypAt (A : String) (e : List Entry) : Bool := ((clsOf? e).map (·.body.declaresTyp A)).getD false

/-- `L(K)` of a class context, `[K]` when the linearization does not exist (a cycle, refused by R-CI). -/
def linD (e : List Entry) : List (List Entry) := (linOf e).getD [e]

/-- `mimpl'(a, Ls)`: the first class of `Ls` that defines `a` concretely (Martres p.74). -/
def mimpl (a : String) : List (List Entry) → Option (List Entry)
  | [] => none
  | e :: es => if definesAt a e then some e else mimpl a es

/-- The class whose declaration is `eff(a, K)`, for `L = L(K)`: `mimpl`'s, else the first class that
declares `a`. -/
def effCls (a : String) (L : List (List Entry)) : Option (List Entry) :=
  match mimpl a L with
  | some e => some e
  | none => L.find? (declaresAt a)

/-! ## The members of an instance -/

/-- A member of an instance: a type member, a term member, or the hidden field `ℓx$D` of the plain
parameter `x` of the class `D` (D-11). -/
inductive IName where
  | typ (A : String)
  | trm (a : String)
  | hid (x D : String)
deriving DecidableEq, Repr

/-- The members a class body declares, in text order. -/
def bodyNames : CMems → List IName
  | .nil => []
  | .typ _ _ A _ _ r | .alias _ _ A _ r => .typ A :: bodyNames r
  | .valDecl _ _ a _ r | .val _ _ a _ _ r | .defDecl _ _ a _ _ r | .defn _ _ a _ _ _ r => .trm a :: bodyNames r

/-- The members of a class in the order of `decls(K)`: the hidden fields of its plain parameters, its
`val` parameters, its body. -/
def clsNames (d : ClsDecl) : List IName :=
  d.params.filterMap (fun x => if x.isVal then none else some (.hid x.name d.name)) ++
    d.params.filterMap (fun x => if x.isVal then some (.trm x.name) else none) ++ bodyNames d.body

/-- The names of a list, each at its first appearance. -/
def nubI : List IName → List IName → List IName
  | _, [] => []
  | seen, x :: xs => if seen.contains x then nubI seen xs else x :: nubI (x :: seen) xs

/-- `names(K)` for `L = L(K)`: the members of the classes of `L`, from `K` on, each at its first
appearance. -/
def names (L : List (List Entry)) : List IName :=
  nubI [] (L.flatMap fun e => ((clsOf? e).map clsNames).getD [])

/-- The term members of `names(K)`. -/
def termNames (L : List (List Entry)) : List String :=
  (names L).filterMap fun | .trm a => some a | _ => none

/-- The superclass of a class context: its first parent when that is a class, else the superclass of
its first parent, a trait, and `none` without a parent or at the end of the fuel (scalac, probes P03,
P04, P19). -/
def superCls : Nat → List Entry → Option (List Entry)
  | 0, _ => none
  | n + 1, e =>
    match parentEnvs e with
    | P :: _ =>
      match clsOf? P with
      | some d => if d.kind = .trait then superCls n P else some P
      | none => none
    | [] => none

/-- The superclass of a class context, fuelled by the number of classes of the file plus one. -/
def superOf (e : List Entry) : Option (List Entry) := superCls ((stemMems e).classes.length + 1) e

/-- The superclass a parent contributes: the parent itself when it is a class, else its superclass. -/
def parentSuper (eP : List Entry) : Option (List Entry) :=
  match clsOf? eP with
  | some d => if d.kind = .trait then superOf eP else some eP
  | none => none

/-- The superclass of a class context as scalac's `ensureFirstIsClass` computes it: the first parent when it
is a class, else the fold over the parents that moves to a parent's superclass when that derives from the
candidate (probes Q06, P03, P04, P19). -/
def superFold (eK : List Entry) : Option (List Entry) :=
  match parentEnvs eK with
  | [] => none
  | P :: Ps =>
    if (clsOf? P).any (·.kind ≠ .trait) then some P
    else (P :: Ps).foldl (fun cand eP =>
      match parentSuper eP, cand with
      | some B, none => some B
      | some B, some C => if memCls C (linD B) then some B else cand
      | none, _ => cand) none

/-! ## Messages -/

/-- The noun of a class. -/
def noun (d : ClsDecl) : String := if d.kind = .trait then "trait" else "class"

/-- The name of the class of a context. -/
def nameAt (e : List Entry) : String := ((clsOf? e).map (·.name)).getD "?"

/-- The noun and name of the class of a context, `trait T` or `class C`. -/
def nounAt (e : List Entry) : String := ((clsOf? e).map fun d => noun d ++ " " ++ d.name).getD "?"

/-- OV-Need (scalac E164). -/
def msgNeedsOverride (what a : String) (D : List Entry) : String :=
  "error overriding " ++ what ++ " " ++ a ++ " in " ++ nounAt D ++ ": " ++ what ++ " " ++ a ++
    " needs `override` modifier (scalac E164)"
/-- OV-Nothing (scalac E037). -/
def msgOverridesNothing (what a : String) : String := what ++ " " ++ a ++ " overrides nothing (scalac E037)"
/-- OV-Accidental when the implementer's member is not written with `override` (scalac E164). -/
def msgConflict (d : ClsDecl) (a : String) (P Q : List Entry) : String :=
  noun d ++ " " ++ d.name ++ " inherits conflicting members: " ++ a ++ " in " ++ nounAt P ++ " and " ++ a ++
    " in " ++ nounAt Q ++ " (scalac E164)"
/-- OV-Accidental when the implementer's member is written with `override`, the thesis's example
(scalac E164). -/
def msgAccidental (what a : String) (P Q : List Entry) : String :=
  "error overriding " ++ what ++ " " ++ a ++ " in " ++ nounAt P ++ ": " ++ what ++ " " ++ a ++ " in " ++
    nounAt Q ++ " cannot override a concrete member without a third member that's overridden by both (scalac E164)"
/-- OV-Abstract (scalac, no code). -/
def msgNeedsAbstract (d : ClsDecl) (a : String) (D : List Entry) : String :=
  "class " ++ d.name ++ " needs to be abstract, since " ++ a ++ " in " ++ nounAt D ++ " is not defined"
/-- OV-New at a trait (scalac E042). -/
def msgNewTrait (K : String) : String := K ++ " is a trait; it cannot be instantiated (scalac E042)"
/-- OV-New at an abstract class (scalac E042). -/
def msgNewAbstract (K : String) : String := K ++ " is abstract; it cannot be instantiated (scalac E042)"
/-- A missing argument of a constructor (scalac E171). -/
def msgMissingArg (x : String) (d : ClsDecl) : String :=
  "missing argument for parameter " ++ x ++ " of constructor " ++ d.name ++ " in " ++ noun d ++ " " ++ d.name ++
    " (scalac E171)"
/-- More arguments than a constructor without parameters or with two or more takes (scalac, no code). -/
def msgTooMany (d : ClsDecl) : String :=
  "too many arguments for constructor " ++ d.name ++ " in " ++ noun d ++ " " ++ d.name
/-- A class after `with` (scalac E104). -/
def msgNotTrait (B : String) : String := "class " ++ B ++ " is not a trait (scalac E104)"
/-- A trait after `with` whose superclass the class's superclass does not derive from (scalac, no code). -/
def msgIllegalTrait (A T B : String) : String :=
  "illegal trait inheritance: superclass " ++ A ++ " does not derive from trait " ++ T ++ "'s superclass " ++ B

/-- OV-Private at the member `m` of `d`, its word `what`, whose signature names the plain parameter `x`
(scalac, no code). -/
def msgPrivateEscape (what m : String) (d : ClsDecl) (x : String) : String :=
  "non-private " ++ what ++ " " ++ m ++ " in " ++ noun d ++ " " ++ d.name ++ " refers to private value " ++ x ++
    " in its type signature"

/-! ## The checks at a class -/

/-- The first parameter that has no argument. -/
def missingArg : List CParam → Args → Option String
  | [], _ => none
  | x :: _, .nil => some x.name
  | _ :: xs, .cons _ r => missingArg xs r

/-- The number of arguments. -/
def argsLen : Args → Nat
  | .nil => 0
  | .cons _ r => argsLen r + 1

/-- The arguments after the first `n`. -/
def argsDrop : Nat → Args → Args
  | 0, as => as
  | _, .nil => .nil
  | n + 1, .cons _ r => argsDrop n r

/-- Whether there is no argument. -/
def argsNil : Args → Bool
  | .nil => true
  | .cons .. => false

/-- Where scalac reports an argument too many, given the arguments from the first one too many on: the root
of that argument when it is a path, else the class reference. -/
def argPos (P : Pos) : Args → Pos
  | .cons (.path q) _ => q.root.pos
  | _ => P

/-- The shape of the parents of the class at the head of `eK` (N5 departure 1): the arity of the first
parent of a class (S31, E171, too many arguments unless the parent has one parameter, which the mapping
refuses first), arguments to a trait parent (S32), a class after `with` (S33, E104), a trait after `with`
whose superclass the class's superclass does not derive from (S34).  The first parent of a trait is not
checked, since the reader refuses its arguments (probe Q12). -/
def checkParents (eK : List Entry) (first : Bool) : Parents → Except Err Unit
  | .nil => .ok ()
  | .cons P as r => do
    match refEnv? eK.tail P with
    | some eP =>
      match clsOf? eP with
      | some D =>
        if first then
          if (clsOf? eK).any (·.kind = .trait) then pure ()
          else if D.kind = .trait then
            if !argsNil as then throw ⟨argPos P.pos as, msgTooMany D⟩
          else
            match missingArg D.params as with
            | some x => throw ⟨P.pos, msgMissingArg x D⟩
            | none =>
              if D.params.length ≠ 1 && D.params.length < argsLen as then
                throw ⟨argPos P.pos (argsDrop D.params.length as), msgTooMany D⟩
        else if D.kind ≠ .trait then throw ⟨P.pos, msgNotTrait D.name⟩
        else
          match superOf eP, superFold eK with
          | some B, some A => if !memCls B (linD A) then throw ⟨P.pos, msgIllegalTrait (nameAt A) D.name (nameAt B)⟩
          | _, _ => pure ()
      | none => pure ()
    | none => pure ()
    checkParents eK false r

/-- An own member of a class: its position, whether written with `override`, its name, its word, `method`,
`value` or `type`, and whether it is abstract (a `val` or `def` without a right side). -/
structure Own where
  pos : Pos
  ov : Bool
  name : String
  what : String
  abs : Bool

/-- The own members of a class body, in text order. -/
def bodyOwns : CMems → List Own
  | .nil => []
  | .typ p o A _ _ r | .alias p o A _ r => ⟨p, o, A, "type", false⟩ :: bodyOwns r
  | .valDecl p o a _ r => ⟨p, o, a, "value", true⟩ :: bodyOwns r
  | .val p o a _ _ r => ⟨p, o, a, "value", false⟩ :: bodyOwns r
  | .defDecl p o f _ _ r => ⟨p, o, f, "method", true⟩ :: bodyOwns r
  | .defn p o f _ _ _ r => ⟨p, o, f, "method", false⟩ :: bodyOwns r

/-- The own members of a class: its `val` parameters, then its body. -/
def clsOwns (d : ClsDecl) : List Own :=
  d.params.filterMap (fun x => if x.isVal then some ⟨x.pos, false, x.name, "value", false⟩ else none) ++ bodyOwns d.body

/-- OV-Accidental at `a`: `mimpl(a, K) = P`, some `Q` of `L(K)` with `mimpl(a, Q) = P'`, and no class of
both `L(P)` and `L(Q)` declares `a`.  The answer is `(P', P)`, in scalac's order. -/
def accidental (L : List (List Entry)) (a : String) : Option (List Entry × List Entry) :=
  match mimpl a L with
  | some P =>
    L.findSome? fun Q =>
      match mimpl a (linD Q) with
      | some P' => if (linD P).all (fun R => !memCls R (linD Q) || !declaresAt a R) then some (P', P) else none
      | none => none
  | none => none

/-- The own member `a` of the class of a context. -/
def ownAt (a : String) (e : List Entry) : Option Own :=
  (clsOf? e).bind fun d => (clsOwns d).find? fun m => decide (m.name = a)

/-- OV-Need and OV-Nothing at an own member of the class whose linearization without itself is `Ls`.
OV-Need asks `override` of a concrete member only (probes Q21, Q30). -/
def checkOwn (Ls : List (List Entry)) (m : Own) : Except Err Unit := do
  if m.what ≠ "type" && !m.ov && !m.abs then
    match Ls.find? (definesAt m.name) with
    | some D => throw ⟨m.pos, msgNeedsOverride m.what m.name D⟩
    | none => pure ()
  if m.ov then
    let declared := if m.what = "type" then Ls.any (declaresTypAt m.name) else Ls.any (declaresAt m.name)
    if !declared then throw ⟨m.pos, msgOverridesNothing m.what m.name⟩

/-! ## OV-Private: a plain parameter in a signature

scalac 3.8.4 checks that the type signature of a member that is not private names no private value whose
owner does not contain the member's access boundary (`checkNoPrivateLeaks`).  In the subset every member is
public, and the only private values are the plain parameters of a class, owned by the class.  The signatures
are the type of a `val` parameter, read in the class head (G-1), and in the body the bounds or the alias of a
type member, the type of a `val`, and the parameter types and the result type of a `def`.  A right side is no
signature, so a plain parameter stays usable in a body (pos/PlainParamBodyUse).

scalac walks the signature and reports each path that starts at a private value.  At a type selection `q.A`
whose walk reported one, scalac tries again when `A` is an alias in the type of `q`.  It walks the alias, as
seen from `q`, in place of `q.A`.  It keeps the alias when that walk reports nothing (pos/PlainParamAlias).

OV-Private does the same at a type selection on a path through a plain parameter `z` of `K`.  The selection
is `z.w.A`, or `this.A` and a bare `A` where `this` stands for a path through `z`.  OV-Private reads the
declared type of `z`, then the declared type of each step the path selects, then looks up `A` in it.  A step
on a class instance selects a member of `L(K)`, a `val` parameter or a `val` of a body
(neg/PrivateParentValEscape).  It selects a plain parameter only where the body of that parameter's class
names it (pos/PlainParamParentAlias).  The walk follows a refinement, `&`, a class through its
linearization, an object behind `o.type`, and an alias of an object that names one of these.  At `&`, an
alias on one side wins over a side that does not declare `A` or declares it with no bounds.  scalac's meet
of the two does the same.  In a class, an inherited alias wins in the same way over the other declarations of
`L(K)` (neg/PrivateInheritedBoundEscape).  A class of `L(K)` that derives from the class of the alias and
declares `A` again overrides the alias (neg/PrivateOverriddenAliasEscape).  The right side of the alias is
read where it is written.  There the refinement or the class body that holds it stands for the path.  So
`this.S` and a bare `S` in it select on the path again (neg/PrivateAliasAbstract).  An object is static, so
nothing in it stands for `z`.  When the second walk reports a plain parameter, OV-Private reports `z`, as
scalac does.

The second walk is not made in the cases below.  There OV-Private refuses where scalac may accept.
- At `&` when both sides declare `A` otherwise (disagree/PlainParamAliasMeet).
- At a class when another class of `L(K)` declares `A` as an alias or with bounds that are not open, outside
  the base classes of the class whose alias is found (disagree/PlainParamInheritedAliases).
- At a parameter typed by a singleton other than an object's (disagree/PlainParamAliasSingleton).
- At a type that the declared type names through a path that is not an object.
- At a type member of a class that is the declared type of a `val` (disagree/PlainParamAliasValAlias).
- At a `val` selected on `&` or on a refinement (disagree/PlainParamAliasRefinementVal).
- When its fuel runs out.

The type of a parameter that a path selects on an instance is read in the head of its class, as scalac reads
it (`headSite`).  There a name that the body declares or inherits does not hide a name outside the class
(neg/PrivateOuterObjectEscape, pos/PlainParamAliasHeadName).  A parameter of the class named there continues
the path (neg/PrivateEarlierParamEscape).  The type of a `val` of a body is read in the body.  A second walk
only removes a report of the first.  So OV-Private refuses only where the first walk alone reports a plain
parameter.  That the second walk removes a report only where scalac's does is tested on the corpus and on the
review probes, not proved.

A name is read with the reader's `lookup`.  Refinements and binders are pushed as the reader pushes them.  So
a member or binder of the same name hides the parameter (pos/PlainParamShadowed).  An alias of an alias
written in the body names no parameter.  So scalac and the check report the first alias only
(neg/PrivateAliasChainEscape).  An inherited member is checked in the class that declares it
(neg/PrivateParentEscape).  The files are in scala/nominal.  Like the other checks of `checkClass`,
OV-Private runs at the classes that `Mems.clsEnvs` reaches: those of the wrapper and of its objects.
`checkClass` does not run at a class in an object inside a literal.  In the probes tried, the typer rejects
each such class that has a plain parameter.  That is tested, not proved. -/

/-- The names a path selects after its root, in order. -/
def steps : ScalaRead.Path → List String
  | .this _ | .var _ _ => []
  | .sel q _ a => steps q ++ [a]

/-- A step of a path after its root: the name, and the key of the class whose plain parameter it selects.  A
step selects a plain parameter only where the body of that class writes it, as `this.a` or a bare `a`.
Selected on an instance from outside, a name is a member: a `val` parameter or a member of a body
(neg/PrivateParentValEscape). -/
abbrev Step := String × Option Pos

/-- Steps that select members. -/
def mems (ns : List String) : List Step := ns.map fun a => (a, none)

/-- The step `a` written in the template `t`: the plain parameter `a` of `t` when `t` is a class that has
one, as `ClsDecl.findTrm` finds parameters first. -/
def stepIn (t : NominalFrontend.ScalaRead.Scope.Tmpl) (a : String) : Step :=
  match t with
  | .cls d' => if d'.plain a then (a, some d'.pos) else (a, none)
  | _ => (a, none)

/-- The steps of `this.a.ns` written in the template `t`. -/
def stepsIn (t : NominalFrontend.ScalaRead.Scope.Tmpl) : List String → List Step
  | [] => []
  | a :: ns => stepIn t a :: mems ns

/-- A path through a plain parameter: the parameter, then the steps after it. -/
abbrev Via := String × List Step

/-- The path that the template at `k` stands for, by the list of a site. -/
def selfOf (k : Pos) : List (Pos × Via) → Option Via
  | [] => none
  | (k', v) :: r => if decide (k' = k) then some v else selfOf k r

/-- Where a type that OV-Private reads is written. -/
inductive Mode where
  /-- In a body, a refinement or an object. -/
  | body
  /-- In the head of the class `E.d` that OV-Private checks, at the type of a parameter.  `n` is the length
  of the context at the start of that type. -/
  | head (n : Nat)
  /-- In the head of the class `d'`, at the type of one of its parameters, seen from the path `v`.  `b` is the
  length of the context outside `d'`.  A parameter of `d'` named there is a step on `v`. -/
  | inst (d' : ClsDecl) (b : Nat) (v : Via)

/-- A type that OV-Private reads: `ty` in `env`, written at `mode`, and the templates `sfs` whose `this`
stands for a path through a plain parameter. -/
structure Site where
  env : List Entry
  mode : Mode
  sfs : List (Pos × Via)
  ty : ScalaRead.Ty

/-- What OV-Private reads with at a class `d`: `b` the length of the context outside the class, and `ok v A`,
whether the second walk at the selection `A` on the path `v` reports nothing. -/
structure Esc where
  d : ClsDecl
  b : Nat
  ok : Via → String → Bool

/-- The path through a plain parameter of `E.d` that `q`, read in `env`, is.  A template of `sfs` stands for its
path: `this` there, or a bare member of it, continues that path.  Else, in a body (`.body`): a name that
`lookup` finds as a member of the body of `d`, or `this.x` where `this` is the body of `d`.  In the head of `d`
(`.head n`): a name that `lookup` finds as a binder whose outside has a length from `E.b` to below `n`, a
parameter of `d`.  In the head of another class `d'` seen from `v` (`.inst d' b v`): a name that `lookup` finds
as a binder whose outside has a length from `b` to below `b` plus the number of parameters of `d'`.  That
binder is a parameter of `d'`, so the name continues `v`.  In a head, `this` is the object around the class,
and nothing in an object stands for a path through `z`. -/
def rootOf (E : Esc) (mode : Mode) (sfs : List (Pos × Via)) (env : List Entry) (q : ScalaRead.Path) :
    Option Via :=
  match q.root with
  | .var _ w =>
    match lookup w env with
    | .member (.tmpl t :: _) =>
      match selfOf t.pos sfs, mode, t with
      | some (z, s), _, _ => some (z, s ++ stepIn t w :: mems (steps q))
      | none, .body, .cls d' => if E.d.plain w && decide (d'.pos = E.d.pos) then some (w, mems (steps q)) else none
      | _, _, _ => none
    | .param _ _ env' =>
      match mode with
      | .head n =>
        if E.d.plain w && decide (E.b ≤ env'.length) && decide (env'.length < n) then some (w, mems (steps q))
        else none
      | .inst d' b (z, s) =>
        if decide (b ≤ env'.length) && decide (env'.length < b + d'.params.length) then
          some (z, s ++ stepIn (.cls d') w :: mems (steps q))
        else none
      | .body => none
    | _ => none
  | .this _ =>
    match thisOf env with
    | some (.tmpl t :: _) =>
      match selfOf t.pos sfs, mode, t, steps q with
      | some (z, s), _, _, ns => some (z, s ++ stepsIn t ns)
      | none, .body, .cls d', x :: ns => if E.d.plain x && decide (d'.pos = E.d.pos) then some (x, mems ns) else none
      | _, _, _, _ => none
    | _ => none
  | .sel .. => none

mutual
/-- The first plain parameter of `E.d` that `T`, read in `env`, names after the second walks.  A refinement
and the binder of a function type are pushed as the reader's `checkTy` pushes them. -/
def tyEsc (E : Esc) (mode : Mode) (sfs : List (Pos × Via)) (env : List Entry) (T : ScalaRead.Ty) :
    Option String :=
  match T with
  | .any _ | .nothing _ => none
  | .name _ A =>
    match lookupTyp A env with
    | some (.tmpl t :: _) =>
      match selfOf t.pos sfs with
      | some v => if E.ok v A then none else some v.1
      | none => none
    | _ => none
  | .sel _ q A =>
    match rootOf E mode sfs env q with
    | some v => if E.ok v A then none else some v.1
    | none => none
  | .sngl _ q => (rootOf E mode sfs env q).map (·.1)
  | .refine p ds => declsEsc E mode sfs (.tmpl (.ref p ds) :: env) ds
  | .and S U => (tyEsc E mode sfs env S).or (tyEsc E mode sfs env U)
  | .fn _ (some x) S U => (tyEsc E mode sfs env S).or (tyEsc E mode sfs (.param x (some S) false :: env) U)
  | .fn _ none S U => (tyEsc E mode sfs env S).or (tyEsc E mode sfs env U)
/-- The first plain parameter of `E.d` that a bound names. -/
def boundEsc (E : Esc) (mode : Mode) (sfs : List (Pos × Via)) (env : List Entry) (b : ScalaRead.Bound) :
    Option String :=
  match b with
  | .absent => none
  | .given T => tyEsc E mode sfs env T
/-- The first plain parameter of `E.d` that declarations name. -/
def declsEsc (E : Esc) (mode : Mode) (sfs : List (Pos × Via)) (env : List Entry) (ds : ScalaRead.Decls) :
    Option String :=
  match ds with
  | .nil => none
  | .typ _ _ lo hi r =>
    ((boundEsc E mode sfs env lo).or (boundEsc E mode sfs env hi)).or (declsEsc E mode sfs env r)
  | .alias _ _ T r | .val _ _ T r => (tyEsc E mode sfs env T).or (declsEsc E mode sfs env r)
end

/-- The type member `A` of a path, as the second walk finds it. -/
inductive Mem where
  /-- No member `A`. -/
  | absent
  /-- `A` with no bounds, or `>: Nothing <: Any`. -/
  | open
  /-- `A` with other bounds, or declared in a way the second walk does not follow. -/
  | other
  /-- `A` an alias, whose right side is at the site. -/
  | alias (s : Site)

/-- The member `A` of `S & U` from those of `S` and `U`: an alias meets no member or one with no bounds into
the alias. -/
def Mem.meet : Mem → Mem → Mem
  | .absent, m => m
  | m, .absent => m
  | .open, .open => .open
  | .open, .alias s => .alias s
  | .alias s, .open => .alias s
  | _, _ => .other

/-- Whether bounds are absent, `Nothing` below and `Any` above. -/
def openBounds (lo hi : ScalaRead.Bound) : Bool :=
  (match lo with
   | .absent | .given (.nothing _) => true
   | _ => false) &&
  (match hi with
   | .absent | .given (.any _) => true
   | _ => false)

/-- The member that a declaration found by name gives: `Al` makes the site of an alias's right side, `Bd`
judges bounds, and no declaration is `absent`. -/
def memOf (Al : ScalaRead.Ty → Site) (Bd : ScalaRead.Bound → ScalaRead.Bound → Mem) :
    Option ScalaRead.DTyp → Mem
  | some (.alias U) => .alias (Al U)
  | some (.bounds lo hi) => Bd lo hi
  | none => .absent

/-- The alias `A` of an object or of the stem at the head of `e`. -/
def objTyp? (e : List Entry) (A : String) : Option ScalaRead.Ty :=
  match headTmpl? e with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) => ms.findTyp A
  | _ => none

/-- The member `A` that the class at the head of `e` declares in its own body, on the path `v`.  The body
stands for `v`. -/
def ownTyp (v : Via) (e : List Entry) (A : String) : Mem :=
  memOf (fun U => ⟨e, .body, [(clsKey e, v)], U⟩) (fun lo hi => if openBounds lo hi then .open else .other)
    ((clsOf? e).bind (·.body.findTyp A))

/-- Whether the class of a context declares the type member `A` as an alias or with bounds that are not open. -/
def closedTypAt (A : String) (e : List Entry) : Bool :=
  match (clsOf? e).bind (·.body.findTyp A) with
  | some (.alias _) => true
  | some (.bounds lo hi) => !openBounds lo hi
  | none => false

/-- Whether the class of `e''` derives from the class of `e'` and is another class. -/
def derivesFrom (e' e'' : List Entry) : Bool :=
  !decide (clsKey e'' = clsKey e') && (linD e'').any fun b => decide (clsKey b = clsKey e')

/-- The member `A` of an instance of the class at the head of `e`, on the path `v`.

It is the class's own declaration, if there is one.  Else it is the alias of the first class `E` of `L(K)`
that aliases `A`, as `Scope.clsTyp?` resolves it (G-6).  scalac's member is then the meet of the members of
the parents, where a member overrides those of its base classes.  So the alias is kept only when no class of
`L(K)` outside `L(E)` declares `A` as an alias or with bounds that are not open, and no class of `L(K)` that
derives from `E` declares `A` at all.  Else the member is `other` (neg/PrivateInheritedBoundEscape,
neg/PrivateOverriddenAliasEscape).  A subclass of `E` that declares `A` with open bounds overrides the alias
with an abstract type.  scalac refuses such a class alone (E164), and reports the leak first where a
signature selects `A` through a plain parameter.  Two equal aliases are `other` too, as at `&`, where scalac
keeps the alias (disagree/PlainParamInheritedAliases).  With no alias in `L(K)`, the member is `other` when a
class of `L(K)` declares `A`. -/
def instTyp (v : Via) (e : List Entry) (A : String) : Mem :=
  match ownTyp v e A with
  | .absent =>
    match (linD e).tail.find? fun e' => ((clsOf? e').map (·.body.aliases A)).getD false with
    | some e' =>
      if (linD e).tail.any fun e'' =>
          (!(linD e').any (fun b => decide (clsKey b = clsKey e'')) && closedTypAt A e'') ||
          (derivesFrom e' e'' && declaresTypAt A e'')
      then .other
      else ownTyp v e' A
    | none => if (linD e).tail.any (declaresTypAt A) then .other else .absent
  | m => m

/-- The member `A` of a path `v` whose declared type is at the site `s`.  Fuelled, `other` when the fuel runs
out. -/
def memTyp : Nat → Via → Site → String → Mem
  | 0, _, _, _ => .other
  | n + 1, v, ⟨env, mode, sfs, T⟩, A =>
    match T with
    | .refine p ds =>
      memOf (fun U => ⟨.tmpl (.ref p ds) :: env, mode, (p, v) :: sfs, U⟩)
        (fun lo hi => if openBounds lo hi then .open else .other) (ds.findTyp A)
    | .and S U => (memTyp n v ⟨env, mode, sfs, S⟩ A).meet (memTyp n v ⟨env, mode, sfs, U⟩ A)
    | .name p C =>
      match clsKind n env ⟨p, none, C⟩ with
      | .inst e => instTyp v e A
      | _ =>
        match (lookupTyp C env).bind fun e => (objTyp? e C).map (e, ·) with
        | some (e, U) => memTyp n v ⟨e, .body, [], U⟩ A
        | none => .other
    | .sel p q C =>
      match clsKind n env ⟨p, some q, C⟩, kindPath n env none q with
      | .inst e, _ => instTyp v e A
      | _, .obj e =>
        match objTyp? e C with
        | some U => memTyp n v ⟨e, .body, [], U⟩ A
        | none => .other
      | _, _ => .other
    | .sngl _ q =>
      match kindPath n env none q with
      | .obj e => memOf (fun U => ⟨e, .body, [], U⟩) (fun _ _ => .other) ((objTyp? e A).map .alias)
      | _ => .other
    | .any _ | .fn .. => .absent
    | .nothing _ => .other

/-- The class of `Ls` whose key is `k`, with the type of its plain parameter `a`. -/
def plainAt (k : Pos) (a : String) : List (List Entry) → Option (List Entry × ScalaRead.Ty)
  | [] => none
  | e' :: es =>
    if decide (clsKey e' = k) then
      ((clsOf? e').bind fun d => d.params.find? fun x => !x.isVal && decide (x.name = a)).map fun x => (e', x.ty)
    else plainAt k a es

/-- Whether `a` is a `val` parameter of the class at the head of `e`. -/
def valParamAt (a : String) (e : List Entry) : Bool :=
  ((clsOf? e).map fun d => d.params.any fun x => x.isVal && decide (x.name = a)).getD false

/-- The site of the type `Ta` of a parameter of the class at the head of `e`, seen from the path `v`.  It is
the class head, as scalac, the mapping and `Scope.kindPath` read it (`Scope.headEnv`, G-1).  There the
parameters are pushed over the context outside the class, and a name that the body declares or inherits is
not in scope (neg/PrivateOuterObjectEscape). -/
def headSite (v : Via) (e : List Entry) (Ta : ScalaRead.Ty) : Option Site :=
  match e with
  | .tmpl (.cls d') :: out => some ⟨headEnv e, .inst d' out.length v, [], Ta⟩
  | _ => none

/-- The declared type of the step `a` on an instance of the class at the head of `e`, on the path `v`.

A step that selects a plain parameter of a class of `L(K)` takes that parameter.  The body of that class
names it.  A plain parameter is private to its class, but scalac makes the second walk on it as on any path
(pos/PlainParamAliasClass, pos/PlainParamParentAlias).

Any other step takes the member `a` of `L(K)`, as `declTrm?` finds it.  That is a `val` parameter or a `val`
of a body, never a plain parameter (G-3).  So a plain parameter of a subclass does not hide the `val` of a
parent that the parent's alias names (neg/PrivateParentValEscape).

The type of a parameter is read in the head of its class (`headSite`).  A parameter named there is a step on
`v` (`rootOf` at `.inst`), so an earlier parameter named in the type of a later one is selected on `v`
(neg/PrivateEarlierParamEscape, pos/PlainParamAliasHeadName).  A name that the body declares or inherits
does not hide one outside the class (neg/PrivateOuterObjectEscape, neg/PrivateParentOuterObjectEscape).
The type of a `val` of a body is read in the body, which stands for `v`. -/
def instVal (v : Via) (e : List Entry) : Step → Option Site
  | (a, some k) => (plainAt k a (linD e)).bind fun (e', Ta) => headSite v e' Ta
  | (a, none) =>
    match declTrm? a (linD e) with
    | some (e', .val Ta) =>
      if valParamAt a e' then headSite v e' Ta else some ⟨e', .body, [(clsKey e', v)], Ta⟩
    | _ => none

/-- The declared type of the member `a` of the object or stem at the head of `e`: an object is its singleton
read where it is declared, a `val` its written type. -/
def objVal (e : List Entry) (a : String) : Option Site :=
  match headTmpl? e with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) =>
    match ms.findTrm a with
    | some (.obj p ..) => some ⟨e, .body, [], .sngl p (.var p a)⟩
    | some (.val (some Ta) _) => some ⟨e, .body, [], Ta⟩
    | _ => none
  | _ => none

/-- The declared type of the `val` member `a` of a path `v` whose declared type is at the site `s`: in a class
through `L(K)`, in an object.  None at `&`, at a refinement and when the fuel runs out.  scalac's second walk
does select the `val` of a refinement (disagree/PlainParamAliasRefinementVal), so there OV-Private is stricter.
E083 refuses a `val` of a refinement as a type prefix only where the source writes the path. -/
def memVal : Nat → Via → Site → Step → Option Site
  | 0, _, _, _ => none
  | n + 1, v, ⟨env, _, _, T⟩, a =>
    match T with
    | .name p C =>
      match clsKind n env ⟨p, none, C⟩ with
      | .inst e => instVal v e a
      | _ =>
        match (lookupTyp C env).bind fun e => (objTyp? e C).map (e, ·) with
        | some (e, U) => memVal n v ⟨e, .body, [], U⟩ a
        | none => none
    | .sel p q C =>
      match clsKind n env ⟨p, some q, C⟩, kindPath n env none q with
      | .inst e, _ => instVal v e a
      | _, .obj e => (objTyp? e C).bind fun U => memVal n v ⟨e, .body, [], U⟩ a
      | _, _ => none
    | .sngl _ q =>
      match kindPath n env none q with
      | .obj e => objVal e a.1
      | _ => none
    | _ => none

/-- The declared type of the path `(z, pre ++ ns)`, from that of `(z, pre)` at `s`. -/
def walkVals (n : Nat) (z : String) : List Step → List Step → Site → Option Site
  | _, [], s => some s
  | pre, a :: ns, s => (memVal n (z, pre) s a).bind (walkVals n z (pre ++ [a]) ns)

/-- The context and the type of the parameter `z` of a class, `env` the context outside the class: the
earlier parameters are pushed, as the head reads them (G-1). -/
def paramAt (z : String) : List Entry → List CParam → Option (List Entry × ScalaRead.Ty)
  | _, [] => none
  | env, x :: xs =>
    if decide (x.name = z) then some (env, x.ty) else paramAt z (.param x.name (some x.ty) false :: env) xs

/-- The second walk at the selection `A` on the path `v` through a plain parameter of `d`, `out` the context
outside `d`: whether `A` is an alias in the declared type of `v` whose right side names no plain parameter of
`d`.  Fuelled, false when the fuel runs out. -/
def okSel (d : ClsDecl) (out : List Entry) : Nat → Via → String → Bool
  | 0, _, _ => false
  | n + 1, (z, ns), A =>
    match (paramAt z out d.params).bind fun (envZ, Tz) => walkVals n z [] ns ⟨envZ, .head envZ.length, [], Tz⟩ with
    | some s =>
      match memTyp n (z, ns) s A with
      | .alias s' => (tyEsc ⟨d, out.length, fun v' A' => okSel d out n v' A'⟩ s'.mode s'.sfs s'.env s'.ty).isNone
      | _ => false
    | none => false

/-- The first plain parameter that the signature of a `def` of the body names: the parameter types, each with
the earlier parameters in scope, as `pushParams` pushes them, then the result type. -/
def paramsEsc (E : Esc) (env : List Entry) : List Param → ScalaRead.Ty → Option String
  | [], R => tyEsc E .body [] env R
  | x :: xs, R => (tyEsc E .body [] env x.ty).or (paramsEsc E (.param x.name (some x.ty) false :: env) xs R)

/-- OV-Private at the member `m` of `d` at `p`, its word `what`, when its signature names a plain parameter. -/
def escErr (d : ClsDecl) (p : Pos) (what m : String) : Option String → Option Err
  | some x => some ⟨p, msgPrivateEscape what m d x⟩
  | none => none

/-- OV-Private at the `val` parameters of `E.d`, in text order.  The type of each is read in the class head
with the earlier parameters in scope (G-1): `env` is the context outside the class with them pushed. -/
def headEsc (E : Esc) (env : List Entry) : List CParam → Option Err
  | [] => none
  | x :: xs =>
    (if x.isVal then escErr E.d x.pos "value" x.name (tyEsc E (.head env.length) [] env x.ty) else none).or
      (headEsc E (.param x.name (some x.ty) false :: env) xs)

/-- OV-Private at the members of the body of `E.d`, whose context is `eK`, in text order. -/
def bodyEsc (E : Esc) (eK : List Entry) : CMems → Option Err
  | .nil => none
  | .typ p _ A lo hi r =>
    (escErr E.d p "type" A ((boundEsc E .body [] eK lo).or (boundEsc E .body [] eK hi))).or (bodyEsc E eK r)
  | .alias p _ A T r => (escErr E.d p "type" A (tyEsc E .body [] eK T)).or (bodyEsc E eK r)
  | .valDecl p _ a T r | .val p _ a T _ r => (escErr E.d p "value" a (tyEsc E .body [] eK T)).or (bodyEsc E eK r)
  | .defDecl p _ f ps R r | .defn p _ f ps R _ r =>
    (escErr E.d p "method" f (paramsEsc E eK ps R)).or (bodyEsc E eK r)

/-- OV-Private at the class whose context is `eK`: the `val` parameters, then the body.  The second walks are
fuelled by the size of the file's members plus one. -/
def checkEscape (eK : List Entry) : Except Err Unit :=
  match eK with
  | .tmpl (.cls d) :: out =>
    let E : Esc := ⟨d, out.length, okSel d out ((stemMems eK).size + 1)⟩
    match (headEsc E out d.params).or (bodyEsc E eK d.body) with
    | some err => .error err
    | none => .ok ()
  | _ => .ok ()

/-- The checks at the class whose context is `eK`.  A class that is no trait and whose first parent is a
trait passes its superclass no argument, so a superclass with parameters is a missing argument at the
class's name (probes Q10, Q13, Q32). -/
def checkClass (eK : List Entry) : Except Err Unit :=
  match clsOf? eK, linOf eK with
  | some d, some L => do
    checkParents eK true d.parents
    if d.kind ≠ .trait && (parentEnvs eK).head?.any (fun P => (clsOf? P).any (·.kind = .trait)) then
      match (superFold eK).bind clsOf? with
      | some dS =>
        match dS.params with
        | x :: _ => throw ⟨d.pos, msgMissingArg x.name dS⟩
        | [] => pure ()
      | none => pure ()
    match (termNames L).findSome? fun a => (accidental L a).map (a, ·) with
    | some (a, P', P) =>
      match ownAt a P with
      | some m => if m.ov then throw ⟨d.pos, msgAccidental m.what a P' P⟩ else throw ⟨d.pos, msgConflict d a P' P⟩
      | none => throw ⟨d.pos, msgConflict d a P' P⟩
    | none => pure ()
    if d.kind = .concrete then
      match (termNames L).find? fun a => (mimpl a L).isNone with
      | some a => throw ⟨d.pos, msgNeedsAbstract d a ((L.find? (declaresAt a)).getD eK)⟩
      | none => pure ()
    (clsOwns d).forM (checkOwn L.tail)
    checkEscape eK
  | _, _ => .ok ()

/-- Whether every argument is a path. -/
def argsPaths : Args → Bool
  | .nil => true
  | .cons (.path _) r => argsPaths r
  | .cons _ _ => false

/-! ## The checks at `new` -/

/-- The arity of `new p.K(ē)` (S30, E171, and too many arguments unless `K` has one parameter, which the
mapping refuses first), then OV-New (E042). -/
def checkNew (n : Nat) (env : List Entry) (p : Pos) (K : ClassRef) (as : Args) : Except Err Unit :=
  match clsKind n env K with
  | .inst e =>
    match clsOf? e with
    | some d =>
      match missingArg d.params as with
      | some x => throw ⟨p, msgMissingArg x d⟩
      | none =>
        if d.params.length ≠ 1 && d.params.length < argsLen as then
          throw ⟨argPos K.pos (argsDrop d.params.length as), msgTooMany d⟩
        else if d.kind = .trait then throw ⟨K.pos, msgNewTrait d.name⟩
        else if d.kind = .abstract then throw ⟨K.pos, msgNewAbstract d.name⟩
        else .ok ()
    | none => .ok ()
  | _ => .ok ()

/-- The context after the parameters of a `def`, as the mapping pushes them. -/
def pushParams (env : List Entry) (ps : List Param) : List Entry :=
  ps.foldl (fun env x => .param x.name (some x.ty) false :: env) env

mutual
/-- The checks at each `new` of a term, in text order, in the context the mapping gives it. -/
def newsTm (n : Nat) (env : List Entry) (t : Tm) : Except Err Unit :=
  match t with
  | .path _ => .ok ()
  | .sel u _ _ => newsTm n env u
  | .app f u => do
    newsTm n env f
    newsTm n env u
  | .lam _ x T b => newsTm n (.param x T false :: env) b
  | .asc _ e _ => newsTm n env e
  | .block _ ss => newsStats n env ss
  | .lit p s ms => newsMems n (.tmpl (.lit p s ms) :: env) ms
  | .new p K as => do
    checkNew n env p K as
    newsArgs n env as
termination_by structural t
/-- The checks at each `new` of the arguments. -/
def newsArgs (n : Nat) (env : List Entry) (as : Args) : Except Err Unit :=
  match as with
  | .nil => .ok ()
  | .cons t r => do
    newsTm n env t
    newsArgs n env r
termination_by structural as
/-- The checks at each `new` of the arguments of parents. -/
def newsParents (n : Nat) (env : List Entry) (Ps : Parents) : Except Err Unit :=
  match Ps with
  | .nil => .ok ()
  | .cons _ as r => do
    newsArgs n env as
    newsParents n env r
termination_by structural Ps
/-- The checks at each `new` of a class body. -/
def newsCMems (n : Nat) (env : List Entry) (ms : CMems) : Except Err Unit :=
  match ms with
  | .nil => .ok ()
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .defDecl _ _ _ _ _ r => newsCMems n env r
  | .val _ _ _ _ e r => do
    newsTm n env e
    newsCMems n env r
  | .defn _ _ _ ps _ e r => do
    newsTm n (pushParams env ps) e
    newsCMems n env r
termination_by structural ms
/-- The checks at each `new` of a block. -/
def newsStats (n : Nat) (env : List Entry) (ss : Stats) : Except Err Unit :=
  match ss with
  | .last t => newsTm n env t
  | .val _ x T e r => do
    newsTm n env e
    newsStats n (.val x T e :: env) r
termination_by structural ss
/-- The checks at each `new` of template members. -/
def newsMems (n : Nat) (env : List Entry) (ms : Mems) : Except Err Unit :=
  match ms with
  | .nil => .ok ()
  | .obj p o s b r => do
    newsMems n (.tmpl (.obj p o s b) :: env) b
    newsMems n env r
  | .typ _ _ _ r => newsMems n env r
  | .val _ _ _ e r => do
    newsTm n env e
    newsMems n env r
  | .defn _ _ ps _ e r => do
    newsTm n (pushParams env ps) e
    newsMems n env r
  | .cls p k C ps Ps b r => do
    let eK : List Entry := .tmpl (.cls ⟨p, k, C, ps, Ps, b⟩) :: env
    newsParents n (headEnv eK) Ps
    newsCMems n eK b
    newsMems n env r
termination_by structural ms
end

/-! ## The entry point -/

/-- The checks of a file that the reader takes: each class in text order, then each `new` in text
order. -/
def check (F : File) : Except Err Unit := do
  (F.mems.clsEnvs (stemEnv F)).forM checkClass
  newsMems (F.size + 1) (stemEnv F) F.mems
  newsTm (F.size + 1) (stemEnv F) F.body

end NominalFrontend.Scala.Classes
