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
concrete member only) and OV-Nothing (E037).  At each `new p.K(ē)`, in text order after the classes: the arity of `new`
(E171) and OV-New (E042).  A class context whose linearization does not exist is skipped, since R-CI
refuses it first.

Every function is structural, or fuelled by the number of classes of the file plus one.  No function
reads the characters of a name.
-/

namespace NominalFrontend.Scala.Classes

open ScalaSyntax (Pos Err)
open NominalFrontend.ScalaRead (File Mems Stats Tm Args Parents CMems ClsDecl ClsKind CParam ClassRef Param)
open NominalFrontend.ScalaRead.Scope (Entry clsOf? clsKey memCls linOf parentEnvs refEnv? clsKind
  stemMems stemEnv headEnv)

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
