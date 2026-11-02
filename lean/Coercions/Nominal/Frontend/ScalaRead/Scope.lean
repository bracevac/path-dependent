import Coercions.Nominal.Frontend.ScalaRead.Ast
import Coercions.ScalaSyntax.Scope
import Coercions.Nominal.Frontend.Surface

/-!
# Scopes and the kind table of the pDOT Scala reader

The context of a name in a parsed file, and the kind of a path (plan XI, D-10,
D-11, D-13, "The kind table").

On the tree: the members a template declares (`Mems.findTrm`, `Mems.findTyp`,
`Decls.findVal`, `Decls.findTyp`), the size of a file, which is the fuel of
the kind table, and the module chains (`modules`), the object names from the
stem through objects.  An object inside a literal is no module.

In `Scope`: a template (`Tmpl`) is the stem, an object, a literal or a
refinement, identified by the position of its node.  A context is a list of
entries, innermost first.  `lookup` is D-11: the innermost binder or template
member wins, and a template member hides a name bound further out.

The kind table (`kindPath`, `kindVar`, `kindSel`) answers in `PathKind`, whose
environments let a selection continue in the template it lands in.  The rows
are tried in order, with two changes against the plan: a block alias outranks
the `val` row (change 11), and an untyped lambda parameter has the kind `val`
(change 12).  The three functions are structural on the fuel, and the fuel run
out answers `unstable`, which refuses.  `unstablePrefix?` gives the shortest
prefix of length two or more whose kind is a method or unstable.

The refusals R-L to R-Y (plan XI, "The refusals"), after those of the parser:
the shapes of member names (R-D, R-U), the cycles of type members (R-Y, with
scalac's reason by `e140`, change 17) and of path vals (R-C), and the walk
`checkTy`, `checkTm`, `checkMems` with plan IX's rules as D-22 keeps them.  The
walk refuses at the position of its node, the first in text order.  `check` is
its entry point.  `labels` is the label table of a file, each name at the sort
its position gives (D-3), with `ℓself` last.
-/

/-!
Classes and traits (plan XII, stage N5).  A class or trait body is the template `Tmpl.cls`.  It declares its
parameters and members, and it inherits the members of its linearization `L(K)` (`lin`, Martres p.73,
fuelled by the number of classes of the file plus one, a cycle answering `none`).  A subclass inherits the
`val` parameters and the body members of `L(K)`, not the parameters written without `val`.  A parameter's
type and a parent's arguments are read outside the body (`headEnv`), as scalac reads them.  A parent is
reached through objects (`refEnv?`).  An instance of a class has the kind `inst`.  The walk adds R-CN, R-PP,
R-CI, R-LB, R-VT, R-PA, R-BN on term and type names, R-D on overloading, and plan XI's R-Y and R-C in class
bodies, and `labels` adds the hidden labels of each class (`hiddenNames`): `new$K`, `m$K`, `ℓx$K` and the
override witnesses.
-/

namespace NominalFrontend.ScalaRead

open ScalaSyntax (Pos Err)
open Paths.FCdot (Label)

/-! ## Members of templates -/

/-- A term member of an object, a literal or the stem. -/
inductive TMem where
  /-- `object o { s => ms }`. -/
  | obj (p : Pos) (o : String) (self : Option String) (ms : Mems)
  /-- `val a [: T] = rhs`. -/
  | val (T : Option Ty) (rhs : Tm)
  /-- `def a` of `n` lists. -/
  | defn (n : Nat)

/-- A type member of a refinement. -/
inductive DTyp where
  /-- `type A = T`. -/
  | alias (T : Ty)
  /-- `type A >: lo <: hi`. -/
  | bounds (lo hi : Bound)

/-- The first object, val or def named `x`. -/
def Mems.findTrm (x : String) : Mems → Option TMem
  | .nil => none
  | .obj p o s b r => if decide (x = o) then some (.obj p o s b) else Mems.findTrm x r
  | .typ _ _ _ r => Mems.findTrm x r
  | .val _ a T e r => if decide (x = a) then some (.val T e) else Mems.findTrm x r
  | .defn _ f ps _ _ r => if decide (x = f) then some (.defn ps.length) else Mems.findTrm x r
  | .cls _ _ _ _ _ _ r => Mems.findTrm x r

/-- The first `type A = T`. -/
def Mems.findTyp (A : String) : Mems → Option Ty
  | .nil => none
  | .typ _ B T r => if decide (A = B) then some T else Mems.findTyp A r
  | .obj _ _ _ _ r | .val _ _ _ _ r | .defn _ _ _ _ _ r | .cls _ _ _ _ _ _ r => Mems.findTyp A r

/-- The first `val a: T`. -/
def Decls.findVal (a : String) : Decls → Option Ty
  | .nil => none
  | .val _ b T r => if decide (a = b) then some T else Decls.findVal a r
  | .typ _ _ _ _ r | .alias _ _ _ r => Decls.findVal a r

/-- The first type member `A`: its alias, or its bounds. -/
def Decls.findTyp (A : String) : Decls → Option DTyp
  | .nil => none
  | .typ _ B lo hi r => if decide (A = B) then some (.bounds lo hi) else Decls.findTyp A r
  | .alias _ B T r => if decide (A = B) then some (.alias T) else Decls.findTyp A r
  | .val _ _ _ r => Decls.findTyp A r

/-- A class or trait definition, the fields of `Mems.cls`. -/
structure ClsDecl where
  /-- At the name. -/
  pos : Pos
  kind : ClsKind
  name : String
  params : List CParam
  parents : Parents
  body : CMems

/-- The first class or trait `C` among members. -/
def Mems.findCls (C : String) : Mems → Option ClsDecl
  | .nil => none
  | .cls p k D ps Ps b r => if decide (C = D) then some ⟨p, k, D, ps, Ps, b⟩ else Mems.findCls C r
  | .obj _ _ _ _ r | .typ _ _ _ r | .val _ _ _ _ r | .defn _ _ _ _ _ r => Mems.findCls C r

/-- Every class and trait of members, through objects, in text order. -/
def Mems.classes : Mems → List ClsDecl
  | .nil => []
  | .cls p k C ps Ps b r => ⟨p, k, C, ps, Ps, b⟩ :: Mems.classes r
  | .obj _ _ _ b r => Mems.classes b ++ Mems.classes r
  | .typ _ _ _ r | .val _ _ _ _ r | .defn _ _ _ _ _ r => Mems.classes r

/-- The class references of parents, in text order. -/
def Parents.refs : Parents → List ClassRef
  | .nil => []
  | .cons P _ r => P :: Parents.refs r

/-- A term member of a class or trait: a parameter or a `val` at its type, or a `def` of `n` lists. -/
inductive CTrm where
  | val (T : Ty)
  | defn (n : Nat)

/-- The first `val` or `def` named `a` of a class body. -/
def CMems.findTrm (a : String) : CMems → Option CTrm
  | .nil => none
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r => CMems.findTrm a r
  | .valDecl _ _ b T r | .val _ _ b T _ r => if decide (a = b) then some (.val T) else CMems.findTrm a r
  | .defDecl _ _ f ps _ r | .defn _ _ f ps _ _ r =>
    if decide (a = f) then some (.defn ps.length) else CMems.findTrm a r

/-- Whether a class body declares the type member `A`. -/
def CMems.declaresTyp (A : String) : CMems → Bool
  | .nil => false
  | .typ _ _ B _ _ r | .alias _ _ B _ r => decide (A = B) || CMems.declaresTyp A r
  | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r => CMems.declaresTyp A r

/-- The parameter or own member `a` of a class: a parameter first, then the body. -/
def ClsDecl.findTrm (d : ClsDecl) (a : String) : Option CTrm :=
  match d.params.find? (fun x => decide (x.name = a)) with
  | some x => some (.val x.ty)
  | none => d.body.findTrm a

/-- The member `a` of a class as a subclass inherits it: a `val` parameter first, then the body.  A parameter
written without `val` is no member (G-3). -/
def ClsDecl.findMem (d : ClsDecl) (a : String) : Option CTrm :=
  match d.params.find? (fun x => x.isVal && decide (x.name = a)) with
  | some x => some (.val x.ty)
  | none => d.body.findTrm a

/-- Whether `a` is a parameter of the class written without `val`. -/
def ClsDecl.plain (d : ClsDecl) (a : String) : Bool := d.params.any fun x => !x.isVal && decide (x.name = a)

/-- Whether a class body aliases `A`. -/
def CMems.aliases (A : String) : CMems → Bool
  | .nil => false
  | .alias _ _ B _ r => decide (A = B) || CMems.aliases A r
  | .typ _ _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r =>
    CMems.aliases A r

/-- The lower bound written for `A` in a class body, erased, unless it is absent or `Nothing`. -/
def CMems.lowerOf (A : String) : CMems → Option Ty
  | .nil => none
  | .typ _ _ B lo _ r =>
    if decide (A = B) then
      match lo with
      | .given (.nothing _) | .absent => none
      | .given T => some T.erase
    else CMems.lowerOf A r
  | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r =>
    CMems.lowerOf A r

/-- Whether a class body defines `f` concretely with parameter types other than `Ts`, as written. -/
def CMems.otherDef (f : String) (Ts : List Ty) : CMems → Bool
  | .nil => false
  | .defn _ _ g qs _ _ r => (decide (f = g) && !decide (qs.map (·.ty.erase) = Ts)) || CMems.otherDef f Ts r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r =>
    CMems.otherDef f Ts r

/-- Whether a class body declares `f` without a body with parameter types other than `Ts`, as written. -/
def CMems.otherDecl (f : String) (Ts : List Ty) : CMems → Bool
  | .nil => false
  | .defDecl _ _ g qs _ r => (decide (f = g) && !decide (qs.map (·.ty.erase) = Ts)) || CMems.otherDecl f Ts r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defn _ _ _ _ _ _ r =>
    CMems.otherDecl f Ts r

/-- Whether a class body declares `f`, with a body or without, with the parameter types `Ts`, as written. -/
def CMems.sameDecl (f : String) (Ts : List Ty) : CMems → Bool
  | .nil => false
  | .defDecl _ _ g qs _ r => (decide (f = g) && decide (qs.map (·.ty.erase) = Ts)) || CMems.sameDecl f Ts r
  | .defn _ _ g qs _ _ r => (decide (f = g) && decide (qs.map (·.ty.erase) = Ts)) || CMems.sameDecl f Ts r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r => CMems.sameDecl f Ts r

/-- The name and the erased parameter types of each `def` of a class body with a body, and, when `abs`, of
each `def` without one, in text order. -/
def CMems.defSigs (abs : Bool) : CMems → List (String × List Ty)
  | .nil => []
  | .defn _ _ f ps _ _ r => (f, ps.map (·.ty.erase)) :: CMems.defSigs abs r
  | .defDecl _ _ f ps _ r => (if abs then [(f, ps.map (·.ty.erase))] else []) ++ CMems.defSigs abs r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .val _ _ _ _ _ r => CMems.defSigs abs r

/-- The first type member `A` of a class body: its alias, or its bounds. -/
def CMems.findTyp (A : String) : CMems → Option DTyp
  | .nil => none
  | .typ _ _ B lo hi r => if decide (A = B) then some (.bounds lo hi) else CMems.findTyp A r
  | .alias _ _ B T r => if decide (A = B) then some (.alias T) else CMems.findTyp A r
  | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r => CMems.findTyp A r

/-- The right side of the first `val a` of a class body, none when it is declared without one. -/
def CMems.valRhs? (a : String) : CMems → Option Tm
  | .nil => none
  | .val _ _ b _ e r => if decide (a = b) then some e else CMems.valRhs? a r
  | .valDecl _ _ b _ r => if decide (a = b) then none else CMems.valRhs? a r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r => CMems.valRhs? a r

/-! ## Size, the fuel of the kind table -/

mutual
/-- The size of a type, one per node. -/
def Ty.size (T : Ty) : Nat :=
  match T with
  | .any _ | .nothing _ | .name .. => 1
  | .sel .. | .sngl .. => 2
  | .refine _ ds => Decls.size ds + 1
  | .and S U | .fn _ _ S U => Ty.size S + Ty.size U + 1
termination_by structural T
/-- The size of a bound. -/
def Bound.size (b : Bound) : Nat :=
  match b with
  | .absent => 0
  | .given T => Ty.size T
termination_by structural b
/-- The size of declarations. -/
def Decls.size (ds : Decls) : Nat :=
  match ds with
  | .nil => 1
  | .typ _ _ lo hi r => Bound.size lo + Bound.size hi + Decls.size r + 1
  | .alias _ _ T r | .val _ _ T r => Ty.size T + Decls.size r + 1
termination_by structural ds
end

/-- The size of a path, one per step. -/
def Path.size : Path → Nat
  | .this _ | .var _ _ => 1
  | .sel q _ _ => q.size + 1

/-- The size of a type that may be absent. -/
def Ty.sizeOpt : Option Ty → Nat
  | some T => T.size
  | none => 0

mutual
/-- The size of a term. -/
def Tm.size (t : Tm) : Nat :=
  match t with
  | .path q => q.size
  | .sel u _ _ => Tm.size u + 1
  | .app u v => Tm.size u + Tm.size v + 1
  | .lam _ _ T b => Ty.sizeOpt T + Tm.size b + 1
  | .asc _ u T => Tm.size u + T.size + 1
  | .block _ ss => Stats.size ss + 1
  | .lit _ _ ms => Mems.size ms + 1
  | .new _ K as => (K.pre.map Path.size).getD 0 + Args.size as + 1
termination_by structural t
/-- The size of arguments. -/
def Args.size (as : Args) : Nat :=
  match as with
  | .nil => 1
  | .cons t r => Tm.size t + Args.size r + 1
termination_by structural as
/-- The size of parents. -/
def Parents.size (Ps : Parents) : Nat :=
  match Ps with
  | .nil => 1
  | .cons P as r => (P.pre.map Path.size).getD 0 + Args.size as + Parents.size r + 1
termination_by structural Ps
/-- The size of class members. -/
def CMems.size (ms : CMems) : Nat :=
  match ms with
  | .nil => 1
  | .typ _ _ _ lo hi r => Bound.size lo + Bound.size hi + CMems.size r + 1
  | .alias _ _ _ T r | .valDecl _ _ _ T r => T.size + CMems.size r + 1
  | .val _ _ _ T e r => T.size + Tm.size e + CMems.size r + 1
  | .defDecl _ _ _ ps R r => (ps.map (·.ty.size)).sum + R.size + CMems.size r + 1
  | .defn _ _ _ ps R e r => (ps.map (·.ty.size)).sum + R.size + Tm.size e + CMems.size r + 1
termination_by structural ms
/-- The size of statements. -/
def Stats.size (ss : Stats) : Nat :=
  match ss with
  | .last t => Tm.size t + 1
  | .val _ _ T e r => Ty.sizeOpt T + Tm.size e + Stats.size r + 1
termination_by structural ss
/-- The size of members. -/
def Mems.size (ms : Mems) : Nat :=
  match ms with
  | .nil => 1
  | .obj _ _ _ b r => Mems.size b + Mems.size r + 1
  | .typ _ _ T r => T.size + Mems.size r + 1
  | .val _ _ T e r => Ty.sizeOpt T + Tm.size e + Mems.size r + 1
  | .defn _ _ ps R e r => (ps.map (·.ty.size)).sum + Ty.sizeOpt R + Tm.size e + Mems.size r + 1
  | .cls _ _ _ ps Ps b r => (ps.map (·.ty.size)).sum + Parents.size Ps + CMems.size b + Mems.size r + 1
termination_by structural ms
end

/-- The size of a file, the fuel of the kind table and of the cycle checks less one. -/
def File.size (F : File) : Nat := F.mems.size + Ty.sizeOpt F.ty + F.body.size + 1

/-! ## Modules -/

/-- The chains of object names from the stem through objects, outer before inner, in text order. -/
def Mems.modules (pre : List String) : Mems → List (List String)
  | .nil => []
  | .obj _ o _ b r => (pre ++ [o]) :: Mems.modules (pre ++ [o]) b ++ Mems.modules pre r
  | .typ _ _ _ r | .val _ _ _ _ r | .defn _ _ _ _ _ r | .cls _ _ _ _ _ _ r => Mems.modules pre r

/-- The module chains of a file.  A `val`'s literal is not entered. -/
def modules (F : File) : List (List String) := F.mems.modules []

namespace Scope

/-! ## Templates -/

/-- A template: the stem, an object, a literal or a refinement. -/
inductive Tmpl where
  /-- The wrapper's members, the stem σ. -/
  | stem (p : Pos) (W : String) (ms : Mems)
  /-- `object o { s => ms }`. -/
  | obj (p : Pos) (o : String) (self : Option String) (ms : Mems)
  /-- `new Object { s => ms }`. -/
  | lit (p : Pos) (self : Option String) (ms : Mems)
  /-- A refinement `{ ds }`. -/
  | ref (p : Pos) (ds : Decls)
  /-- The body of a class or trait, with its parameters. -/
  | cls (d : ClsDecl)

/-- The position of a template's node, its identity (fix 6). -/
def Tmpl.pos : Tmpl → Pos
  | .stem p .. | .obj p .. | .lit p .. | .ref p .. => p
  | .cls d => d.pos

/-- Whether the template declares the term member `x`: `findTrm`, or `findVal` for a refinement. -/
def Tmpl.declaresTrm (t : Tmpl) (x : String) : Bool :=
  match t with
  | .stem _ _ ms | .obj _ _ _ ms | .lit _ _ ms => (ms.findTrm x).isSome
  | .ref _ ds => (ds.findVal x).isSome
  | .cls d => (d.findTrm x).isSome

/-- Whether the template declares the type member `A`, or the class or trait `A`. -/
def Tmpl.declaresTyp (t : Tmpl) (A : String) : Bool :=
  match t with
  | .stem _ _ ms | .obj _ _ _ ms => (ms.findTyp A).isSome || (ms.findCls A).isSome
  | .lit _ _ ms => (ms.findTyp A).isSome
  | .ref _ ds => (ds.findTyp A).isSome
  | .cls d => d.body.declaresTyp A

/-- Whether the template binds the name `x` to itself: the wrapper's name, an object's own name or self
name, a literal's self name. -/
def Tmpl.binds (t : Tmpl) (x : String) : Bool :=
  match t with
  | .stem _ W _ => decide (x = W)
  | .obj _ o s _ => decide (x = o) || decide (s = some x)
  | .lit _ s _ => decide (s = some x)
  | .ref .. | .cls _ => false

/-- The noun of a template, for messages. -/
def Tmpl.noun : Tmpl → String
  | .stem .. | .obj .. => "object"
  | .lit .. => "object literal"
  | .ref .. => "refinement"
  | .cls d => match d.kind with
    | .trait => "trait"
    | _ => "class"

/-! ## The context -/

/-- An entry of a context. -/
inductive Entry where
  /-- A lambda or def parameter, a function type's binder.  `mod`: written at a module singleton, in a
  lambda or a function type (R-K). -/
  | param (x : String) (T : Option Ty) (mod : Bool)
  /-- A block val seen so far. -/
  | val (x : String) (T : Option Ty) (rhs : Tm)
  /-- The block val whose type or right side the walk is in. -/
  | defining (x : String) (typed : Bool)
  /-- A later val of the same block. -/
  | later (x : String)
  /-- A template. -/
  | tmpl (t : Tmpl)

/-- What a name refers to in a context. -/
inductive Ref where
  /-- A parameter.  `env`: the entries outside the binder. -/
  | param (T : Option Ty) (mod : Bool) (env : List Entry)
  /-- A block val seen so far.  `env`: the entries outside it. -/
  | val (T : Option Ty) (rhs : Tm) (env : List Entry)
  /-- The block val being defined. -/
  | defining (typed : Bool)
  /-- A later val of the same block. -/
  | later
  /-- The template at the head of `env`, by its binder's name. -/
  | self (env : List Entry)
  /-- A member of the template at the head of `env`. -/
  | member (env : List Entry)
  /-- Nothing. -/
  | none

/-- The referent of `x` by own declarations only, as `lookup` reads the context outside every class body. -/
def lookupOwn (x : String) : List Entry → Ref
  | [] => .none
  | .param y T m :: env => if decide (x = y) then .param T m env else lookupOwn x env
  | .val y T e :: env => if decide (x = y) then .val T e env else lookupOwn x env
  | .defining y typed :: env => if decide (x = y) then .defining typed else lookupOwn x env
  | .later y :: env => if decide (x = y) then .later else lookupOwn x env
  | .tmpl t :: env =>
    if t.declaresTrm x then .member (.tmpl t :: env)
    else if t.binds x then .self (.tmpl t :: env)
    else lookupOwn x env

/-- The innermost template, with the entries outside it. -/
def thisOf : List Entry → Option (List Entry)
  | [] => none
  | .tmpl t :: env => some (.tmpl t :: env)
  | _ :: env => thisOf env

/-- The template at the head of a context. -/
def headTmpl? : List Entry → Option Tmpl
  | .tmpl t :: _ => some t
  | _ => none

/-! ## Classes: references, parents, linearization -/

/-- The context of the object `a` that the stem or object at the head of `env` declares. -/
def objStep? (env : List Entry) (a : String) : Option (List Entry) :=
  match headTmpl? env with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) =>
    match ms.findTrm a with
    | some (.obj p o s b) => some (.tmpl (.obj p o s b) :: env)
    | _ => none
  | _ => none

/-- Whether the head of `env` is the stem or an object. -/
def isModule (env : List Entry) : Bool :=
  match headTmpl? env with
  | some (.stem ..) | some (.obj ..) => true
  | _ => false

/-- The context of the object a path names through objects only: `this`, the wrapper's or an object's name,
a bare member object, then object members.  An alias, a parameter or a `val` names none (R-PP). -/
def objChain? (env : List Entry) : Path → Option (List Entry)
  | .this _ =>
    match thisOf env with
    | some e => if isModule e then some e else none
    | none => none
  | .var _ x =>
    match lookupOwn x env with
    | .self e => if isModule e then some e else none
    | .member e => objStep? e x
    | _ => none
  | .sel q _ a => (objChain? env q).bind fun e => objStep? e a

/-- The class or trait `C` that the stem or object at the head of `env` declares, as the context of its body. -/
def clsIn? (env : List Entry) (C : String) : Option (List Entry) :=
  match headTmpl? env with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) =>
    match ms.findCls C with
    | some d => some (.tmpl (.cls d) :: env)
    | none => none
  | _ => none

/-- The class or trait a bare name `C` names: the innermost template declaring the type `C`, when it
declares a class or trait. -/
def lookupCls (C : String) : List Entry → Option (List Entry)
  | [] => none
  | .tmpl t :: env => if t.declaresTyp C then clsIn? (.tmpl t :: env) C else lookupCls C env
  | _ :: env => lookupCls C env

/-- The class or trait a parent reference names, reached through objects (R-PP). -/
def refEnv? (env : List Entry) (P : ClassRef) : Option (List Entry) :=
  match P.pre with
  | none => lookupCls P.name env
  | some q => (objChain? env q).bind fun e => clsIn? e P.name

/-- The class of a context whose head is a class or trait body. -/
def clsOf? : List Entry → Option ClsDecl
  | .tmpl (.cls d) :: _ => some d
  | _ => none

/-- The key of a class context: the position of its definition. -/
def clsKey (e : List Entry) : Pos :=
  match headTmpl? e with
  | some t => t.pos
  | none => ScalaSyntax.Pos.zero

/-- The parents of the class at the head of `e` that resolve, in text order. -/
def parentEnvs : List Entry → List (List Entry)
  | .tmpl (.cls d) :: env => d.parents.refs.filterMap (refEnv? env)
  | _ => []

/-- Whether a class context is in a list, by key. -/
def memCls (e : List Entry) : List (List Entry) → Bool
  | [] => false
  | e' :: es => decide (clsKey e = clsKey e') || memCls e es

/-- `Ls ⊕ R`: the classes of `Ls` not in `R`, then `R` (Martres p.73). -/
def addAll : List (List Entry) → List (List Entry) → List (List Entry)
  | [], R => R
  | N :: Ls, R => if memCls N R then addAll Ls R else N :: addAll Ls R

/-- `L(K)` on a fuel: `K`, then `L(P) ⊕ …` from the last parent to the first.  `none` when the fuel runs out,
which a cycle does. -/
def lin : Nat → List Entry → Option (List (List Entry))
  | 0, _ => none
  | n + 1, e => do
    let Ls ← (parentEnvs e).mapM (lin n)
    pure (e :: Ls.foldl (fun acc LP => addAll LP acc) [])

/-- The members of the stem at the bottom of a context. -/
def stemMems : List Entry → Mems
  | [] => .nil
  | [.tmpl (.stem _ _ ms)] => ms
  | _ :: env => stemMems env

/-- `L(K)` for the class at the head of `e`, fuelled by the number of classes of the file plus one. -/
def linOf (e : List Entry) : Option (List (List Entry)) := lin ((stemMems e).classes.length + 1) e

/-- The first class of `Ls` that has the term member `a`, with the member.  A parameter written without `val`
is no member (G-3). -/
def declTrm? (a : String) : List (List Entry) → Option (List Entry × CTrm)
  | [] => none
  | e :: es =>
    match (clsOf? e).bind (·.findMem a) with
    | some m => some (e, m)
    | none => declTrm? a es

/-- The first class of `Ls` that declares the type member `A`. -/
def declTyp? (A : String) : List (List Entry) → Option (List Entry)
  | [] => none
  | e :: es => if ((clsOf? e).map (·.body.declaresTyp A)).getD false then some e else declTyp? A es

/-- The term member `a` of the class at the head of `e`: its own, else the first of `L(K)`. -/
def instTrm? (e : List Entry) (a : String) : Option (List Entry × CTrm) :=
  match (clsOf? e).bind (·.findTrm a) with
  | some m => some (e, m)
  | none =>
    match linOf e with
    | some (_ :: L) => declTrm? a L
    | _ => none

/-- The context of a class head: the entries outside the class, then its parameters, the last innermost.  The
type of a parameter is read there, as scalac reads it (G-1). -/
def headEnv : List Entry → List Entry
  | .tmpl (.cls d) :: env => d.params.foldl (fun env x => .param x.name (some x.ty) false :: env) env
  | env => env

/-- Whether `a` is a parameter of the class at the head of `e`. -/
def isParamOf (e : List Entry) (a : String) : Bool :=
  ((clsOf? e).map fun d => d.params.any fun x => decide (x.name = a)).getD false

/-- The type member `A` of the class at the head of `e`: its own declaration, else the alias of the first class
of `L(K)` that aliases it, as the instance defines it (plan, `inst(A)`), else the bounds of the first class
that declares it (G-6). -/
def clsTyp? (e : List Entry) (A : String) : Option DTyp :=
  match (clsOf? e).bind (·.body.findTyp A) with
  | some t => some t
  | none =>
    match linOf e with
    | some (_ :: L) =>
      match L.findSome? fun e' => (clsOf? e').bind fun d => if d.body.aliases A then d.body.findTyp A else none with
      | some t => some t
      | none => L.findSome? fun e' => (clsOf? e').bind (·.body.findTyp A)
    | _ => none

/-- The right side of the `val a` of the class at the head of `e`: its own, else that of the first class of
`L(K)` that has the member `a` (G-6). -/
def clsVal? (e : List Entry) (a : String) : Option Tm :=
  match (clsOf? e).bind (·.findTrm a) with
  | some _ => (clsOf? e).bind (·.body.valRhs? a)
  | none =>
    match linOf e with
    | some (_ :: L) => (declTrm? a L).bind fun (e', _) => (clsOf? e').bind (·.body.valRhs? a)
    | _ => none

/-- Whether the class at the head of `e` inherits the term member `a` from a class of `L(K)` other than itself. -/
def inheritsTrm (e : List Entry) (a : String) : Bool :=
  match linOf e with
  | some (_ :: L) => (declTrm? a L).isSome
  | _ => false

/-- Whether the class at the head of `e` inherits the type member `A`. -/
def inheritsTyp (e : List Entry) (A : String) : Bool :=
  match linOf e with
  | some (_ :: L) => (declTyp? A L).isSome
  | _ => false

/-- Whether the template at the head of `e` is a class body that inherits `x` (`typ`: a type member). -/
def inherits (typ : Bool) (e : List Entry) (x : String) : Bool :=
  match clsOf? e with
  | some _ => if typ then inheritsTyp e x else inheritsTrm e x
  | none => false

/-- The referent of `x`: the innermost binder or template member wins (D-11).  A class body declares its
parameters, its members and the members it inherits. -/
def lookup (x : String) : List Entry → Ref
  | [] => .none
  | .param y T m :: env => if decide (x = y) then .param T m env else lookup x env
  | .val y T e :: env => if decide (x = y) then .val T e env else lookup x env
  | .defining y typed :: env => if decide (x = y) then .defining typed else lookup x env
  | .later y :: env => if decide (x = y) then .later else lookup x env
  | .tmpl t :: env =>
    if t.declaresTrm x || inherits false (.tmpl t :: env) x then .member (.tmpl t :: env)
    else if t.binds x then .self (.tmpl t :: env)
    else lookup x env

/-- The innermost template declaring type `A`, inherited members of a class body included, with the entries
outside it. -/
def lookupTyp (A : String) : List Entry → Option (List Entry)
  | [] => none
  | .tmpl t :: env =>
    if t.declaresTyp A || inherits true (.tmpl t :: env) A then some (.tmpl t :: env) else lookupTyp A env
  | _ :: env => lookupTyp A env

/-- The context of the stem: the wrapper's template. -/
def stemEnv (F : File) : List Entry := [.tmpl (.stem F.pos F.name F.mems)]

/-! ## The kind table -/

/-- The kind of a path. -/
inductive PathKind where
  /-- An object or the stem, `env` from its template on. -/
  | obj (env : List Entry)
  /-- A literal, `env` from its template on. -/
  | lit (env : List Entry)
  /-- `this` of a refinement, `env` from its template on. -/
  | ref (env : List Entry)
  /-- A binder written at a refinement in place, `env` from that refinement on. -/
  | str (env : List Entry)
  /-- A binder written at a type that is no refinement and no singleton. -/
  | strOther
  /-- A block val, no written type, no alias, or an untyped lambda parameter. -/
  | val
  /-- A val holding a lambda. -/
  | fun
  /-- A def of `n` lists. -/
  | meth (n : Nat)
  /-- `this.a` with `val a: U`, `U` no singleton. -/
  | refval
  /-- No kind: the path is not stable. -/
  | unstable
  /-- An instance of the class or trait whose body is at the head of `env`. -/
  | inst (env : List Entry)

/-- The comparable summary of a kind. -/
inductive KindWord where
  | obj | lit | ref | str | val | fun | meth (n : Nat) | refval | unstable | inst
deriving DecidableEq, Repr

/-- The word of a kind: `str` and `strOther` both give `.str`. -/
def PathKind.word : PathKind → KindWord
  | .obj _ => .obj
  | .lit _ => .lit
  | .ref _ => .ref
  | .str _ | .strOther => .str
  | .val => .val
  | .fun => .fun
  | .meth n => .meth n
  | .refval => .refval
  | .unstable => .unstable
  | .inst _ => .inst

/-- The kind of the template at the head of `env`: stem, obj give `obj`, lit `lit`, ref `ref`. -/
def tmplKind (env : List Entry) : PathKind :=
  match env with
  | .tmpl (.stem ..) :: _ | .tmpl (.obj ..) :: _ => .obj env
  | .tmpl (.lit ..) :: _ => .lit env
  | .tmpl (.ref ..) :: _ => .ref env
  | .tmpl (.cls _) :: _ => .inst env
  | _ => .unstable

/-- The kind of a binder written at `T`, whose scope is `env`. -/
def writtenKind (T : Ty) (env : List Entry) : PathKind :=
  match T with
  | .refine p ds => .str (.tmpl (.ref p ds) :: env)
  | _ => .strOther

mutual
/-- The kind of a path.  `sk` is the kind that `this` and the bare members of the refinement at the head
of `env` read as (the plan's `q'`). -/
def kindPath : Nat → List Entry → Option PathKind → Path → PathKind
  | 0, _, _, _ => .unstable
  | _ + 1, env, sk, .this _ =>
    match sk with
    | some k => k
    | none =>
      match thisOf env with
      | some env' => tmplKind env'
      | none => .unstable
  | n + 1, env, sk, .var _ x =>
    match sk, headTmpl? env with
    | some k, some t =>
      if t.declaresTrm x then kindSel n k x else kindVar n env x
    | _, _ => kindVar n env x
  | n + 1, env, sk, .sel q _ a => kindSel n (kindPath n env sk q) a
/-- The kind of a variable, by its referent. -/
def kindVar : Nat → List Entry → String → PathKind
  | 0, _, _ => .unstable
  | n + 1, env, x =>
    match lookup x env with
    | .param (some T) _ envT => tyKind n envT T
    | .param none _ _ => .val
    | .val (some T) _ envT => tyKind n envT T
    | .val none (.path q) envT =>
      match kindPath n envT none q with
      | .obj e => .obj e
      | _ => .val
    | .val none (.new _ K _) envT =>
      match clsKind n envT K with
      | .inst e => .inst e
      | _ => .val
    | .val none _ _ => .val
    | .self env' => tmplKind env'
    | .member env' => kindSel n (tmplKind env') x
    | _ => .unstable
/-- The kind of a selection `a` on a path of kind `k`. -/
def kindSel : Nat → PathKind → String → PathKind
  | 0, _, _ => .unstable
  | n + 1, k, a =>
    match k with
    | .obj env | .lit env =>
      match headTmpl? env with
      | some (.stem _ _ ms) | some (.obj _ _ _ ms) | some (.lit _ _ ms) =>
        match ms.findTrm a with
        | some (.obj p o s b) => .obj (.tmpl (.obj p o s b) :: env)
        | some (.val (some (.sngl _ q)) (.path q')) =>
          if decide (q.erase = q'.erase) then kindPath n env none q else .unstable
        | some (.val none (.path q)) =>
          match kindPath n env none q with
          | .obj e => .obj e
          | _ => .unstable
        | some (.val _ (.lam ..)) => .fun
        | some (.defn m) => .meth m
        | _ => .unstable
      | _ => .unstable
    | .ref env | .str env =>
      match headTmpl? env with
      | some (.ref _ ds) =>
        match ds.findVal a with
        | some (.sngl _ q) => kindPath n env (some k) q
        | some _ => match k with
          | .ref _ => .refval
          | _ => .unstable
        | none => .unstable
      | _ => .unstable
    | .inst env =>
      match instTrm? env a with
      | some (e, .val T) => tyKind n (if isParamOf e a then headEnv e else e) T
      | some (_, .defn m) => .meth m
      | none => .unstable
    | _ => .unstable
/-- The kind of a binder written at `T` in `env`: a singleton's path, an instance of a class or trait, else
`writtenKind`. -/
def tyKind : Nat → List Entry → Ty → PathKind
  | 0, _, _ => .unstable
  | n + 1, env, T =>
    match T with
    | .sngl _ q => kindPath n env none q
    | .name p C =>
      match clsKind n env ⟨p, none, C⟩ with
      | .inst e => .inst e
      | _ => writtenKind T env
    | .sel p q C =>
      match clsKind n env ⟨p, some q, C⟩ with
      | .inst e => .inst e
      | _ => writtenKind T env
    | _ => writtenKind T env
/-- The kind of an instance of the class or trait a reference names: a bare name by its scope, `q.C` by the
kind of `q`. -/
def clsKind : Nat → List Entry → ClassRef → PathKind
  | 0, _, _ => .unstable
  | n + 1, env, K =>
    match K.pre with
    | none =>
      match lookupCls K.name env with
      | some e => .inst e
      | none => .unstable
    | some q =>
      match kindPath n env none q with
      | .obj e =>
        match clsIn? e K.name with
        | some e' => .inst e'
        | none => .unstable
      | _ => .unstable
end

/-- The shortest prefix of length two or more whose kind is a method or unstable. -/
def unstablePrefix? (n : Nat) (env : List Entry) : Path → Option Path
  | .this _ | .var _ _ => none
  | .sel q p a =>
    match unstablePrefix? n env q with
    | some r => some r
    | none =>
      match kindPath n env none (.sel q p a) with
      | .meth _ | .unstable => some (.sel q p a)
      | _ => none

end Scope

/-! ## Shapes of member names (R-D, R-U) -/

/-- The shape of a member declaration. -/
inductive Shape where
  /-- An object, a template val, a refinement val. -/
  | value
  /-- A def of `n` lists. -/
  | meth (n : Nat)
deriving DecidableEq, Repr

mutual
/-- Every member declaration of a type, in text order, with its position, name and shape. -/
def Ty.shapes (T : Ty) : List (Pos × String × Shape) :=
  match T with
  | .any _ | .nothing _ | .sel .. | .sngl .. | .name .. => []
  | .refine _ ds => Decls.shapes ds
  | .and S U | .fn _ _ S U => Ty.shapes S ++ Ty.shapes U
termination_by structural T
/-- The member declarations of a bound. -/
def Bound.shapes (b : Bound) : List (Pos × String × Shape) :=
  match b with
  | .absent => []
  | .given T => Ty.shapes T
termination_by structural b
/-- The member declarations of declarations: `val a` is a value. -/
def Decls.shapes (ds : Decls) : List (Pos × String × Shape) :=
  match ds with
  | .nil => []
  | .typ _ _ lo hi r => Bound.shapes lo ++ Bound.shapes hi ++ Decls.shapes r
  | .alias _ _ T r => Ty.shapes T ++ Decls.shapes r
  | .val p a T r => (p, a, .value) :: Ty.shapes T ++ Decls.shapes r
termination_by structural ds
end

/-- The member declarations of a type that may be absent. -/
def Ty.shapesOpt : Option Ty → List (Pos × String × Shape)
  | some T => T.shapes
  | none => []

/-- The member declarations in the types of parameters. -/
def Param.shapesL : List Param → List (Pos × String × Shape)
  | [] => []
  | x :: xs => x.ty.shapes ++ Param.shapesL xs

/-- The member declarations of constructor parameters: a `val` parameter is a value. -/
def CParam.shapesL : List CParam → List (Pos × String × Shape)
  | [] => []
  | x :: xs => (if x.isVal then [(x.pos, x.name, Shape.value)] else []) ++ x.ty.shapes ++ CParam.shapesL xs

mutual
/-- Every member declaration of a term, in text order. -/
def Tm.shapes (t : Tm) : List (Pos × String × Shape) :=
  match t with
  | .path _ => []
  | .sel u _ _ => Tm.shapes u
  | .app u v => Tm.shapes u ++ Tm.shapes v
  | .lam _ _ T b => Ty.shapesOpt T ++ Tm.shapes b
  | .asc _ u T => Tm.shapes u ++ T.shapes
  | .block _ ss => Stats.shapes ss
  | .lit _ _ ms => Mems.shapes ms
  | .new _ _ as => Args.shapes as
termination_by structural t
/-- The member declarations of arguments. -/
def Args.shapes (as : Args) : List (Pos × String × Shape) :=
  match as with
  | .nil => []
  | .cons t r => Tm.shapes t ++ Args.shapes r
termination_by structural as
/-- The member declarations of the arguments of parents. -/
def Parents.shapes (Ps : Parents) : List (Pos × String × Shape) :=
  match Ps with
  | .nil => []
  | .cons _ as r => Args.shapes as ++ Parents.shapes r
termination_by structural Ps
/-- The member declarations of class members: `val a` is a value, `def f` has its lists. -/
def CMems.shapes (ms : CMems) : List (Pos × String × Shape) :=
  match ms with
  | .nil => []
  | .typ _ _ _ lo hi r => Bound.shapes lo ++ Bound.shapes hi ++ CMems.shapes r
  | .alias _ _ _ T r => T.shapes ++ CMems.shapes r
  | .valDecl p _ a T r => (p, a, .value) :: T.shapes ++ CMems.shapes r
  | .val p _ a T e r => (p, a, .value) :: T.shapes ++ Tm.shapes e ++ CMems.shapes r
  | .defDecl p _ f ps R r => (p, f, .meth ps.length) :: Param.shapesL ps ++ R.shapes ++ CMems.shapes r
  | .defn p _ f ps R e r =>
    (p, f, .meth ps.length) :: Param.shapesL ps ++ R.shapes ++ Tm.shapes e ++ CMems.shapes r
termination_by structural ms
/-- The member declarations of statements. -/
def Stats.shapes (ss : Stats) : List (Pos × String × Shape) :=
  match ss with
  | .last t => Tm.shapes t
  | .val _ _ T e r => Ty.shapesOpt T ++ Tm.shapes e ++ Stats.shapes r
termination_by structural ss
/-- The member declarations of members: `object o` and `val a` are values, `def f` has its lists. -/
def Mems.shapes (ms : Mems) : List (Pos × String × Shape) :=
  match ms with
  | .nil => []
  | .obj p o _ b r => (p, o, .value) :: Mems.shapes b ++ Mems.shapes r
  | .typ _ _ T r => T.shapes ++ Mems.shapes r
  | .val p a T e r => (p, a, .value) :: Ty.shapesOpt T ++ Tm.shapes e ++ Mems.shapes r
  | .defn p f ps R e r =>
    (p, f, .meth ps.length) :: Param.shapesL ps ++ Ty.shapesOpt R ++ Tm.shapes e ++ Mems.shapes r
  | .cls _ _ _ ps Ps b r => CParam.shapesL ps ++ Parents.shapes Ps ++ CMems.shapes b ++ Mems.shapes r
termination_by structural ms
end

/-- Every member declaration of a file, in text order. -/
def File.shapes (F : File) : List (Pos × String × Shape) :=
  F.mems.shapes ++ Ty.shapesOpt F.ty ++ F.body.shapes

/-! ## Labels -/

/-- The label names of a path: its steps, each a term name. -/
def Path.labelNames : Path → List (String × Bool)
  | .this _ | .var _ _ => []
  | .sel q _ a => q.labelNames ++ [(a, false)]

mutual
/-- The label names of a type, in text order, `true` for a type name. -/
def Ty.labelNames (T : Ty) : List (String × Bool) :=
  match T with
  | .any _ | .nothing _ => []
  | .sel _ q A => q.labelNames ++ [(A, true)]
  | .sngl _ q => q.labelNames
  | .name _ A => [(A, true)]
  | .refine _ ds => Decls.labelNames ds
  | .and S U | .fn _ _ S U => Ty.labelNames S ++ Ty.labelNames U
termination_by structural T
/-- The label names of a bound. -/
def Bound.labelNames (b : Bound) : List (String × Bool) :=
  match b with
  | .absent => []
  | .given T => Ty.labelNames T
termination_by structural b
/-- The label names of declarations, each declaration's name first. -/
def Decls.labelNames (ds : Decls) : List (String × Bool) :=
  match ds with
  | .nil => []
  | .typ _ A lo hi r => (A, true) :: (Bound.labelNames lo ++ Bound.labelNames hi ++ Decls.labelNames r)
  | .alias _ A T r => (A, true) :: (Ty.labelNames T ++ Decls.labelNames r)
  | .val _ a T r => (a, false) :: (Ty.labelNames T ++ Decls.labelNames r)
termination_by structural ds
end

/-- The label names of a type that may be absent. -/
def Ty.labelNamesOpt : Option Ty → List (String × Bool)
  | some T => T.labelNames
  | none => []

/-- The label names in the types of parameters. -/
def Param.labelNamesL : List Param → List (String × Bool)
  | [] => []
  | x :: xs => x.ty.labelNames ++ Param.labelNamesL xs

/-- The label names of constructor parameters: a `val` parameter's name, then its type's. -/
def CParam.labelNamesL : List CParam → List (String × Bool)
  | [] => []
  | x :: xs => (if x.isVal then [(x.name, false)] else []) ++ x.ty.labelNames ++ CParam.labelNamesL xs

/-- The label names of a class reference: its path's steps, then the class, a type name. -/
def ClassRef.labelNames (K : ClassRef) : List (String × Bool) :=
  (K.pre.map Path.labelNames).getD [] ++ [(K.name, true)]

mutual
/-- The label names of a term, in text order. -/
def Tm.labelNames (t : Tm) : List (String × Bool) :=
  match t with
  | .path q => q.labelNames
  | .sel u _ a => Tm.labelNames u ++ [(a, false)]
  | .app u v => Tm.labelNames u ++ Tm.labelNames v
  | .lam _ _ T b => Ty.labelNamesOpt T ++ Tm.labelNames b
  | .asc _ u T => Tm.labelNames u ++ T.labelNames
  | .block _ ss => Stats.labelNames ss
  | .lit _ _ ms => Mems.labelNames ms
  | .new _ K as => K.labelNames ++ Args.labelNames as
termination_by structural t
/-- The label names of arguments. -/
def Args.labelNames (as : Args) : List (String × Bool) :=
  match as with
  | .nil => []
  | .cons t r => Tm.labelNames t ++ Args.labelNames r
termination_by structural as
/-- The label names of parents. -/
def Parents.labelNames (Ps : Parents) : List (String × Bool) :=
  match Ps with
  | .nil => []
  | .cons P as r => P.labelNames ++ Args.labelNames as ++ Parents.labelNames r
termination_by structural Ps
/-- The label names of class members, each member's name first. -/
def CMems.labelNames (ms : CMems) : List (String × Bool) :=
  match ms with
  | .nil => []
  | .typ _ _ A lo hi r => (A, true) :: (Bound.labelNames lo ++ Bound.labelNames hi ++ CMems.labelNames r)
  | .alias _ _ A T r => (A, true) :: (T.labelNames ++ CMems.labelNames r)
  | .valDecl _ _ a T r => (a, false) :: (T.labelNames ++ CMems.labelNames r)
  | .val _ _ a T e r => (a, false) :: (T.labelNames ++ Tm.labelNames e ++ CMems.labelNames r)
  | .defDecl _ _ f ps R r => (f, false) :: (Param.labelNamesL ps ++ R.labelNames ++ CMems.labelNames r)
  | .defn _ _ f ps R e r =>
    (f, false) :: (Param.labelNamesL ps ++ R.labelNames ++ Tm.labelNames e ++ CMems.labelNames r)
termination_by structural ms
/-- The label names of statements.  A block val's name is no label. -/
def Stats.labelNames (ss : Stats) : List (String × Bool) :=
  match ss with
  | .last t => Tm.labelNames t
  | .val _ _ T e r => Ty.labelNamesOpt T ++ Tm.labelNames e ++ Stats.labelNames r
termination_by structural ss
/-- The label names of members, each member's name first. -/
def Mems.labelNames (ms : Mems) : List (String × Bool) :=
  match ms with
  | .nil => []
  | .obj _ o _ b r => (o, false) :: (Mems.labelNames b ++ Mems.labelNames r)
  | .typ _ A T r => (A, true) :: (T.labelNames ++ Mems.labelNames r)
  | .val _ a T e r => (a, false) :: (Ty.labelNamesOpt T ++ Tm.labelNames e ++ Mems.labelNames r)
  | .defn _ f ps R e r =>
    (f, false) :: (Param.labelNamesL ps ++ Ty.labelNamesOpt R ++ Tm.labelNames e ++ Mems.labelNames r)
  | .cls _ _ C ps Ps b r =>
    (C, true) :: (CParam.labelNamesL ps ++ Parents.labelNames Ps ++ CMems.labelNames b ++ Mems.labelNames r)
termination_by structural ms
end

/-- The label names of a file, in text order. -/
def File.labelNames (F : File) : List (String × Bool) :=
  F.mems.labelNames ++ Ty.labelNamesOpt F.ty ++ F.body.labelNames

/-- The name of the self label, which no Scala text has (D-7). -/
def selfLabelName : String := "ℓself"

/-- The number of term labels of a table. -/
def countTrm : LabelTable → Nat
  | [] => 0
  | (_, .trm _) :: Λ => countTrm Λ + 1
  | (_, .typ _) :: Λ => countTrm Λ

/-- The class contexts of members, through objects, in text order: each class or trait body pushed on the
context of the template that declares it. -/
def Mems.clsEnvs (env : List Scope.Entry) : Mems → List (List Scope.Entry)
  | .nil => []
  | .cls p k C ps Ps b r => (.tmpl (.cls ⟨p, k, C, ps, Ps, b⟩) :: env) :: Mems.clsEnvs env r
  | .obj p o s b r => Mems.clsEnvs (.tmpl (.obj p o s b) :: env) b ++ Mems.clsEnvs env r
  | .typ _ _ _ r | .val _ _ _ _ r | .defn _ _ _ _ _ r => Mems.clsEnvs env r

/-- The term members a class declares, in text order, `true` for a `def`: its `val` parameters, then its
body's `val`s and `def`s. -/
def ClsDecl.trmDecls (d : ClsDecl) : List (String × Bool) :=
  d.params.filterMap (fun x => if x.isVal then some (x.name, false) else none) ++ go d.body
where go : CMems → List (String × Bool)
  | .nil => []
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r => go r
  | .valDecl _ _ a _ r | .val _ _ a _ _ r => (a, false) :: go r
  | .defDecl _ _ f _ _ r | .defn _ _ f _ _ _ r => (f, true) :: go r

/-- The type members a class body declares, in text order. -/
def CMems.typNames : CMems → List String
  | .nil => []
  | .typ _ _ A _ _ r | .alias _ _ A _ r => A :: CMems.typNames r
  | .valDecl _ _ _ _ r | .val _ _ _ _ _ r | .defDecl _ _ _ _ _ r | .defn _ _ _ _ _ _ r => CMems.typNames r

/-- The members of a class body with a right side, `val`s and `def`s, in text order. -/
def CMems.bodied : CMems → List String
  | .nil => []
  | .val _ _ a _ _ r | .defn _ _ a _ _ _ r => a :: CMems.bodied r
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .defDecl _ _ _ _ _ r => CMems.bodied r

/-- `new$C`, the constructor of `C` (D-8). -/
def newName (C : String) : String := "new$" ++ C
/-- `f$C`, the module function or the witness of the member `f` of `C` (D-9, D-10). -/
def modName (f C : String) : String := f ++ "$" ++ C
/-- `ℓx$C`, the hidden field of the plain parameter `x` of `C` (D-11). -/
def hidName (x C : String) : String := "ℓ" ++ x ++ "$" ++ C
/-- `w$K$m$D`, the override witness `w` of `K` for the member `m` declared in `D` (D-13). -/
def witName (w K m D : String) : String := w ++ "$" ++ K ++ "$" ++ m ++ "$" ++ D

/-- Whether a class of `L` other than the one at key `k` declares the term member `m`. -/
def otherDeclares (L : List (List Scope.Entry)) (k : Pos) (m : String) : Bool :=
  L.any fun e => !decide (Scope.clsKey e = k) && ((Scope.clsOf? e).map fun d => (d.findMem m).isSome).getD false

/-- The witness labels of `K` for the class `D` of `L(K)`: for each term member of `D` that another class
of `L(K)` declares, `ov` and `ovp` for a `def`, `ovv` for a `val`. -/
def witTrm (K : String) (L : List (List Scope.Entry)) (eD : List Scope.Entry) : List (String × Bool) :=
  match Scope.clsOf? eD with
  | some D =>
    D.trmDecls.flatMap fun (m, isDef) =>
      if otherDeclares L (Scope.clsKey eD) m then
        (if isDef then [(witName "ov" K m D.name, false), (witName "ovp" K m D.name, false)]
         else [(witName "ovv" K m D.name, false)])
      else []
  | none => []

/-- The witness labels `ovl` and `ovu` of `K` for each type member of `K` that a class `D` of `L(K)` other
than `K` declares. -/
def witTyp (K : String) (As : List String) (L : List (List Scope.Entry)) : List (String × Bool) :=
  As.flatMap fun A => L.flatMap fun eD =>
    match Scope.clsOf? eD with
    | some D => if D.body.declaresTyp A then [(witName "ovl" K A D.name, false), (witName "ovu" K A D.name, false)]
      else []
    | none => []

/-- The hidden labels of the class at the head of `e`: `new$C` for a concrete class, `m$C` for each member
with a right side, `ℓx$C` for each plain parameter, then the witness labels along `L(C)`. -/
def clsHidden (e : List Scope.Entry) : List (String × Bool) :=
  match Scope.clsOf? e with
  | some d =>
    let L := (Scope.linOf e).getD [e]
    (if d.kind = .concrete then [(newName d.name, false)] else []) ++
      d.body.bodied.map (fun m => (modName m d.name, false)) ++
      d.params.filterMap (fun x => if x.isVal then none else some (hidName x.name d.name, false)) ++
      L.flatMap (witTrm d.name L) ++ witTyp d.name d.body.typNames L.tail
  | none => []

/-- The hidden labels of a file, class by class in text order. -/
def hiddenNames (F : File) : List (String × Bool) := (F.mems.clsEnvs (Scope.stemEnv F)).flatMap clsHidden

/-- The label table of a file: every name at the sort its position gives, in order of first
appearance, then the hidden labels of its classes, then `ℓself` as the next term label. -/
def labels (F : File) : LabelTable :=
  let Λ := intern [] 0 0 (F.labelNames ++ hiddenNames F)
  Λ ++ [(selfLabelName, .trm (countTrm Λ))]

namespace Scope

open ScalaSyntax.Scope (mem quote checkName checkMember Under litUnder)

/-- The shape of the first declaration of `x`. -/
def firstShape? (S : List (Pos × String × Shape)) (x : String) : Option Shape :=
  match S with
  | [] => none
  | (_, y, s) :: S' => if decide (x = y) then some s else firstShape? S' x

/-- The number of lists when the first declaration of `x` is a def. -/
def defLists? (S : List (Pos × String × Shape)) (x : String) : Option Nat :=
  match firstShape? S x with
  | some (.meth n) => some n
  | _ => none

/-! ## Cycles (R-Y, R-C) -/

/-- A member, with the context of its template. -/
structure NodeE where
  /-- The context from the template on. -/
  env : List Entry
  /-- The member's name. -/
  name : String

/-- The key of a member: its template's position and its name (fix 6). -/
def NodeE.key (e : NodeE) : Pos × String :=
  match headTmpl? e.env with
  | some t => (t.pos, e.name)
  | none => (ScalaSyntax.Pos.zero, e.name)

/-- Whether a key is in a list. -/
def memKey (k : Pos × String) : List (Pos × String) → Bool
  | [] => false
  | k' :: ks => decide (k = k') || memKey k ks

/-- The type member `A` that a selection names, as a node, when its prefix's template declares it. -/
def selNode (n : Nat) (env : List Entry) (q : Path) (A : String) : List NodeE :=
  match kindPath n env none q with
  | .obj e | .lit e | .ref e | .str e =>
    match headTmpl? e with
    | some t => if t.declaresTyp A then [⟨e, A⟩] else []
    | none => []
  | .inst e =>
    match q, headTmpl? e with
    | .this _, some t => if t.declaresTyp A || inherits true e A then [⟨e, A⟩] else []
    | _, _ => []
  | _ => []

mutual
/-- The type members that `T` selects.  With `direct`, only those outside every function type and every
nested refinement. -/
def tyEdges (n : Nat) (env : List Entry) (direct : Bool) (T : Ty) : List NodeE :=
  match T with
  | .any _ | .nothing _ | .sngl .. => []
  | .sel _ q A => selNode n env q A
  | .name _ A =>
    match lookupTyp A env with
    | some e => [⟨e, A⟩]
    | none => []
  | .refine p ds => if direct then [] else declsEdges n (.tmpl (.ref p ds) :: env) ds
  | .and S U => tyEdges n env direct S ++ tyEdges n env direct U
  | .fn _ x S U =>
    if direct then [] else tyEdges n env false S ++ tyEdges n (.param (x.getD "") (some S) false :: env) false U
termination_by structural T
/-- The type members that a bound selects. -/
def boundEdges (n : Nat) (env : List Entry) (direct : Bool) (b : Bound) : List NodeE :=
  match b with
  | .absent => []
  | .given T => tyEdges n env direct T
termination_by structural b
/-- The type members that declarations select. -/
def declsEdges (n : Nat) (env : List Entry) (ds : Decls) : List NodeE :=
  match ds with
  | .nil => []
  | .typ _ _ lo hi r => boundEdges n env false lo ++ boundEdges n env false hi ++ declsEdges n env r
  | .alias _ _ T r | .val _ _ T r => tyEdges n env false T ++ declsEdges n env r
termination_by structural ds
end

/-- The successors of a type member: all edges, or the plain ones of an upper bound (`plain`). -/
def typSuccs (n : Nat) (plain : Bool) (e : NodeE) : List NodeE :=
  match headTmpl? e.env with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) | some (.lit _ _ ms) =>
    match ms.findTyp e.name with
    | some T => tyEdges n e.env false T
    | none => []
  | some (.ref _ ds) =>
    match ds.findTyp e.name with
    | some (.alias T) => tyEdges n e.env false T
    | some (.bounds lo hi) => boundEdges n e.env false lo ++ boundEdges n e.env plain hi
    | none => []
  | some (.cls _) =>
    match clsTyp? e.env e.name with
    | some (.alias T) => tyEdges n e.env false T
    | some (.bounds lo hi) => boundEdges n e.env false lo ++ boundEdges n e.env plain hi
    | none => []
  | none => []

/-- The keys reached from `todo` along `succ`, in at most the given number of steps. -/
def reachBy (succ : NodeE → List NodeE) : Nat → List NodeE → List (Pos × String) → List (Pos × String)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, e :: todo, seen =>
    if memKey e.key seen then reachBy succ k todo seen else reachBy succ k (todo ++ succ e) (e.key :: seen)

/-- Whether a type member is on a cycle: a plain edge to itself, or a path back through another member. -/
def onCycleY (n : Nat) (e : NodeE) : Bool :=
  memKey e.key ((typSuccs n true e).map NodeE.key) ||
    memKey e.key (reachBy (typSuccs n false) n ((typSuccs n false e).filter fun s => !decide (s.key = e.key)) [])

/-- The edges of a type outside the result of every function type at its top: a function type gives the
edges of its parameter type, an intersection those of both sides, any other type all its edges. -/
def tyLead (n : Nat) (env : List Entry) (T : Ty) : List NodeE :=
  match T with
  | .fn _ _ S _ => tyEdges n env false S
  | .and S U => tyLead n env S ++ tyLead n env U
  | _ => tyEdges n env false T
termination_by structural T

/-- The lead edges of a bound. -/
def boundLead (n : Nat) (env : List Entry) : Bound → List NodeE
  | .absent => []
  | .given T => tyLead n env T

/-- The successors of a type member along its lead edges. -/
def leadSuccs (n : Nat) (e : NodeE) : List NodeE :=
  match headTmpl? e.env with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) | some (.lit _ _ ms) =>
    match ms.findTyp e.name with
    | some T => tyLead n e.env T
    | none => []
  | some (.ref _ ds) =>
    match ds.findTyp e.name with
    | some (.alias T) => tyLead n e.env T
    | some (.bounds lo hi) => boundLead n e.env lo ++ boundLead n e.env hi
    | none => []
  | some (.cls _) =>
    match clsTyp? e.env e.name with
    | some (.alias T) => tyLead n e.env T
    | some (.bounds lo hi) => boundLead n e.env lo ++ boundLead n e.env hi
    | none => []
  | none => []

/-- scalac's code for a member on a cycle: E140 for a plain edge to itself, or a lead edge into the cycle
(change 17). -/
def e140 (n : Nat) (e : NodeE) : Bool :=
  memKey e.key ((typSuccs n true e).map NodeE.key) ||
    memKey e.key (reachBy (typSuccs n false) n ((leadSuccs n e).filter fun s => !decide (s.key = e.key)) [])

/-- The right side of the val `b` of the template at the head of `env`: of the stem, an object, a literal, or
a class body through its own and inherited members (G-6). -/
def tmplValRhs? (env : List Entry) (b : String) : Option Tm :=
  match headTmpl? env with
  | some (.stem _ _ ms) | some (.obj _ _ _ ms) | some (.lit _ _ ms) =>
    match ms.findTrm b with
    | some (.val _ rhs) => some rhs
    | _ => none
  | some (.cls _) => clsVal? env b
  | _ => none

/-- The path val that a template val's right side names: for `q.b`, the val `b` of the template of `q`, and
for a bare member `x`, the val `x`, each when it holds a path. -/
def valSucc (n : Nat) (e : NodeE) : List NodeE :=
  let target (env : List Entry) (b : String) : List NodeE :=
    match tmplValRhs? env b with
    | some (.path _) => [⟨env, b⟩]
    | _ => []
  match tmplValRhs? e.env e.name with
  | some (.path (.sel q _ b)) =>
    match kindPath n e.env none q with
    | .obj env' | .lit env' => target env' b
    | _ => []
  | some (.path (.var _ x)) =>
    match lookup x e.env with
    | .member env' => target env' x
    | _ => []
  | _ => []

/-- Whether a template val is on a cycle of path vals. -/
def onCycleC (n : Nat) (e : NodeE) : Bool :=
  memKey e.key (reachBy (valSucc n) n (valSucc n e) [])

/-! ## The messages -/

/-- R-L. -/
def msgRL : String := "a member that holds an object literal is a nested `object`"
/-- R-V. -/
def msgRV : String := "a field that holds a path is an alias in pDOT: write `val a: p.type = p`"
/-- R-R. -/
def msgRR : String := "a field holds a path or a value in pDOT: move the computation into `program`"
/-- R-D. -/
def msgRD : String := "a name is a method everywhere or a value everywhere"
/-- R-U. -/
def msgRU : String := "a method is called with all its parameter lists"
/-- R-K. -/
def msgRK : String := "scalac 3.8.4 crashes in the pickler on this shape (orphan parameter reference)"
/-- R-S, at the unstable prefix `q`. -/
def msgRS (q : Path) : String :=
  "`" ++ q.text ++ "` is not a valid type prefix, since it is not an immutable path (scalac E083)"
/-- R-Y, on the alias or bound `what` of `A`, with scalac's code when `code` (change 17). -/
def msgRY (code : Bool) (what A : String) : String :=
  "illegal cyclic type reference: the " ++ what ++ " of `" ++ A ++ "` refers back to `" ++ A ++ "`" ++
    (if code then " (scalac E140)" else " (scalac exceeds its recursion limit)")
/-- R-C, at the val `a`. -/
def msgRC (a : String) : String := "cyclic reference involving val " ++ a ++ " (scalac E046)"

/-- R-PP, at the parent. -/
def msgRPP : String := "a parent is a class or trait of this file reached through objects"
/-- R-CN, at a type member whose name a class or trait of the file has. -/
def msgRCN : String := "a class or trait name is not a type member name anywhere in the file"
/-- R-CN, at the second class or trait of one name. -/
def msgRCN2 : String := "a class or trait name is declared once in the file"
/-- R-VT, at the `val`. -/
def msgRVT : String := "a `val` of a class or trait does not read `this`"
/-- R-PA, at the selection of the plain parameter `x`. -/
def msgRPA (x : String) : String :=
  "`" ++ x ++ "` is a constructor parameter, not a member: write `val " ++ x ++ "` (scalac E173)"
/-- R-BN, at the bare name `x`. -/
def msgRBN (x : String) : String :=
  "Reference to `" ++ x ++ "` is ambiguous: it is both defined in an enclosing object and inherited (scalac E049)"
/-- R-CI, at the parent of the class or trait `C` (its noun `what`) through which `C` reaches itself. -/
def msgRCI (what C : String) : String := "Cyclic inheritance: " ++ what ++ " " ++ C ++ " extends itself (scalac E110)"
/-- R-LB, at the class.  The condition compares lower bounds as written (G-9). -/
def msgRLB (A : String) : String := "the inherited lower bounds of `" ++ A ++ "` differ as written"
/-- R-D, overloading, at the `def`. -/
def msgROL (f : String) : String :=
  "`" ++ f ++ "` has other parameter types than an inherited `" ++ f ++ "`: overloading is outside the subset"
/-- R-D, overloading, at a class that inherits `f` with other parameter types from two classes (G-5). -/
def msgROL2 (f : String) : String :=
  "`" ++ f ++ "` is inherited with other parameter types from two classes: overloading is outside the subset"
/-- `new` of a name that is no class or trait in scope. -/
def msgNoCls (C : String) : String := "`" ++ C ++ "` is not a class or trait in scope"

/-- Rule 5: `x` is no member of the template `t`. -/
def notMember (p : Pos) (t : Tmpl) (typ : Bool) (x : String) : Err :=
  ⟨p, (if typ then "type " else "value ") ++ x ++ " is not a member of the " ++ t.noun ++ " (scalac E008)"⟩

/-- Rule 8: a second type member `A` of a refinement. -/
def dupType (p : Pos) (A : String) : Err := ⟨p, quote A ++ " is already defined in this refinement (scalac E161)"⟩

/-- Rule 8: a second field `a` of a refinement. -/
def dupField (p : Pos) (a : String) : Err :=
  ⟨p, "conflicting definitions of " ++ quote a ++ " in one refinement (scalac E120)"⟩

/-- Rule 8: a second member `x` of a template with the noun `noun`, or a member named as the self name. -/
def dupMem (noun : String) (p : Pos) (self : Bool) (x : String) : Err :=
  if self then ⟨p, "conflicting definitions of the self name and the member " ++ quote x ++ " (scalac E120)"⟩
  else ⟨p, "conflicting definitions of " ++ quote x ++ " in one " ++ noun ++ " (scalac E120)"⟩

/-! ## The walk -/

/-- The context of the walk. -/
structure Ctx where
  /-- The entries, innermost first. -/
  env : List Entry
  /-- Inside a dependent function type (rule 4). -/
  dep : Bool
  /-- The fuel of the kind table and the cycle checks, `F.size + 1`. -/
  fuel : Nat
  /-- The member declarations of the file, `F.shapes`. -/
  shapes : List (Pos × String × Shape)
  /-- The classes and traits of the file in text order, `F.mems.classes`. -/
  classes : List ClsDecl

/-- The context with one more entry. -/
def Ctx.push (c : Ctx) (e : Entry) : Ctx := { c with env := e :: c.env }

/-- The context of the template a root names when it is `this`, a self name, an object's own name or the
wrapper's name. -/
def binderOf (c : Ctx) : Path → Option (List Entry)
  | .this _ => thisOf c.env
  | .var _ x =>
    match lookup x c.env with
    | .self env' => some env'
    | _ => none
  | .sel .. => none

/-- Whether the template at the head of `e` declares `x`, a type member when `typ`, inherited members of a
class body included. -/
def declaresIn (typ : Bool) (e : List Entry) (x : String) : Bool :=
  match headTmpl? e with
  | some t => (if typ then t.declaresTyp x else t.declaresTrm x) || inherits typ e x
  | none => true

/-- R-BN: the class body at the head of `e` inherits `x` and does not declare it, and a template outside the
class declares or binds `x`. -/
def ambiguous (e : List Entry) (x : String) : Bool :=
  match e with
  | .tmpl (.cls d) :: env =>
    (d.findTrm x).isNone &&
      (match lookup x env with
       | .member _ | .self _ => true
       | _ => false)
  | _ => false

/-- R-PA: `a` is a plain parameter of the class whose instance `k` is. -/
def plainOf (k : PathKind) (a : String) : Bool :=
  match k with
  | .inst e => ((clsOf? e).map (·.plain a)).getD false
  | _ => false

/-- Whether the key `k` is in a list. -/
def memPos (k : Pos) : List Pos → Bool
  | [] => false
  | k' :: ks => decide (k = k') || memPos k ks

/-- The keys of the classes reached from `todo` along parents, in at most the given number of steps. -/
def reachCls : Nat → List (List Entry) → List Pos → List Pos
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, e :: todo, seen =>
    if memPos (clsKey e) seen then reachCls k todo seen else reachCls k (todo ++ parentEnvs e) (clsKey e :: seen)

/-- R-CI: the first parent, in text order, from which the class at the key `k` is reached. -/
def firstCyclic (n : Nat) (k : Pos) (env : List Entry) : List ClassRef → Option Pos
  | [] => none
  | P :: Ps =>
    match refEnv? env P with
    | some eP => if memPos k (reachCls n [eP] []) then some P.pos else firstCyclic n k env Ps
    | none => firstCyclic n k env Ps

/-- R-PP: the first parent, in text order, that names no class or trait through objects. -/
def firstLost (env : List Entry) : List ClassRef → Option Pos
  | [] => none
  | P :: Ps => if (refEnv? env P).isSome then firstLost env Ps else some P.pos

/-- The types of a list without repeats, first occurrences kept. -/
def nubTy : List Ty → List Ty
  | [] => []
  | T :: Ts => if Ts.contains T then nubTy Ts else T :: nubTy Ts

/-- R-LB: the first type member of the classes `L`, in their order, that no class of `L` aliases and that
two classes of `L` bound below by different types, as written. -/
def lbConflict (L : List (List Entry)) : List String → Option String
  | [] => none
  | A :: As =>
    let ds := L.filterMap clsOf?
    if !(ds.any fun d => d.body.aliases A) && decide (2 ≤ (nubTy (ds.filterMap fun d => d.body.lowerOf A)).length)
    then some A else lbConflict L As

/-- R-D, overloading, at a `def f(ps)` of the class `K` at the head of `e`, `o` when it is marked `override`,
`abs` when `K` is a trait or an abstract class: a class of `L(K)` other than `K` defines `f` with a body and
with parameter types other than those of `ps`, or, when `abs`, declares it so without a body, as written.  An
`override` counts only when a class of `L(K)` other than `K` declares `f` with the parameter types of `ps`
(G-5). -/
def overloads (o abs : Bool) (e : List Entry) (f : String) (ps : List Param) : Bool :=
  let Ts := ps.map (·.ty.erase)
  match linOf e with
  | some (_ :: L) =>
    let ds := L.filterMap clsOf?
    (!o || ds.any fun d => d.body.sameDecl f Ts) &&
      ds.any fun d => d.body.otherDef f Ts || (abs && d.body.otherDecl f Ts)
  | _ => false

/-- R-D, overloading, at the class `K` whose `L(K)` without `K` is `L`, `abs` when `K` is a trait or an
abstract class: the first `def` name, in the order of the bodies of `L`, that two classes of `L` define with
a body and with other parameter types, or, when `abs`, declare so with or without a body, as written (G-5). -/
def inheritedOverload (abs : Bool) (L : List (List Entry)) : Option String :=
  let ss := (L.filterMap clsOf?).flatMap (·.body.defSigs abs)
  (ss.find? fun (f, Ts) => ss.any fun (g, Us) => decide (f = g) && !decide (Ts = Us)).map (·.1)

/-- Whether the class at `p` is a second class or trait named `C` in text order. -/
def secondCls (p : Pos) (C : String) : List ClsDecl → Bool
  | [] => false
  | d :: ds => if decide (d.pos = p) then false else decide (d.name = C) || secondCls p C ds

/-- R-PP, R-CI, R-LB and R-D on inherited overloads at the class or trait `d`, which the template at the head
of `c.env` declares. -/
def checkClsHead (c : Ctx) (d : ClsDecl) : Except Err Unit := do
  match firstLost c.env d.parents.refs with
  | some q => throw ⟨q, msgRPP⟩
  | none => pure ()
  match firstCyclic c.fuel d.pos c.env d.parents.refs with
  | some q => throw ⟨q, msgRCI (Tmpl.cls d).noun d.name⟩
  | none => pure ()
  if d.kind = .concrete then
    match linOf (.tmpl (.cls d) :: c.env) with
    | some L =>
      match lbConflict L (L.flatMap fun e => ((clsOf? e).map (·.body.typNames)).getD []) with
      | some A => throw ⟨d.pos, msgRLB A⟩
      | none => pure ()
    | none => pure ()
  match linOf (.tmpl (.cls d) :: c.env) with
  | some (_ :: L) =>
    match inheritedOverload (decide (d.kind ≠ .concrete)) L with
    | some f => throw ⟨d.pos, msgROL2 f⟩
    | none => pure ()
  | _ => pure ()

/-- R-Y and R-C at the class or trait `d`, whose body is at the head of `c.env`, on the members it inherits
and does not declare: the first type member on a cycle, then the first `val` on a cycle, each in the order of
the bodies of `L(K)`.  It runs after the body, so that an own member on a cycle is named first (G-6). -/
def checkInherited (c : Ctx) (d : ClsDecl) : Except Err Unit :=
  match linOf c.env with
  | some (_ :: L) =>
    let ds := L.filterMap clsOf?
    match (ds.flatMap (·.body.typNames)).find? fun A => !d.body.declaresTyp A && onCycleY c.fuel ⟨c.env, A⟩ with
    | some A => .error ⟨d.pos, msgRY false "inherited alias or bound" A⟩
    | none =>
      match (ds.flatMap (·.body.bodied)).find? fun a => (d.findTrm a).isNone && onCycleC c.fuel ⟨c.env, a⟩ with
      | some a => .error ⟨d.pos, msgRC a⟩
      | none => .ok ()
  | _ => .ok ()

/-- R-VT and R-R at a `val` of a class or trait: a path that does not start at `this`, or a lambda. -/
def checkClsField (p : Pos) (e : Tm) : Except Err Unit :=
  match e with
  | .path q =>
    match q.root with
    | .this _ => .error ⟨p, msgRVT⟩
    | _ => .ok ()
  | .lam .. => .ok ()
  | _ => .error ⟨p, msgRR⟩

/-- R-D at a declaration of `x` with shape `s`: the first declaration of `x` has the same shape. -/
def checkShape (c : Ctx) (p : Pos) (x : String) (s : Shape) : Except Err Unit :=
  match firstShape? c.shapes x with
  | some s' => if decide (s = s') then .ok () else .error ⟨p, msgRD⟩
  | none => .ok ()

/-- R-U at a use of the member `x` at `p`: a def of `m` lists used as a prefix (`last` false) or under
`k < m` argument lists. -/
def checkUse (c : Ctx) (p : Pos) (x : String) (last : Bool) (k : Nat) : Except Err Unit :=
  match defLists? c.shapes x with
  | some m => if !last || decide (k < m) then .error ⟨p, msgRU⟩ else .ok ()
  | none => .ok ()

/-- The checks of a path's root: rule 4 on `this` in a dependent function type, rule 1 and rule 9 on a
name, R-U on a bare member def. -/
def checkRoot (c : Ctx) (last : Bool) (k : Nat) : Path → Except Err Unit
  | .this p =>
    if c.dep then .error ⟨p, "inside `(x: S) => T` scalac reads `this` as the enclosing object"⟩ else .ok ()
  | .var p x =>
    match lookup x c.env with
    | .none => .error ⟨p, quote x ++ " is not in scope"⟩
    | .defining false =>
      .error ⟨p, "recursive value " ++ quote x ++ " needs a type: its right side names it (scalac E045)"⟩
    | .defining true => .error ⟨p, "forward reference: the right side of " ++ quote x ++ " names it (scalac E039)"⟩
    | .later => .error ⟨p, "forward reference: " ++ quote x ++ " is defined later in this block (scalac E039)"⟩
    | .member e => if ambiguous e x then .error ⟨p, msgRBN x⟩ else checkUse c p x last k
    | _ => .ok ()
  | .sel .. => .ok ()

/-- The checks of a path's steps, `last` when the path is the whole path, applied to `k` lists: rule 7,
rule 5 on the first step after a binder, R-U. -/
def checkSteps (c : Ctx) (last : Bool) (k : Nat) : Path → Except Err Unit
  | .sel q p a => do
    checkSteps c false 0 q
    checkMember [] p a false
    if q.isRoot then
      match binderOf c q with
      | some e =>
        match headTmpl? e with
        | some t => if declaresIn false e a then pure () else throw (notMember p t false a)
        | none => pure ()
      | none => pure ()
    match q with
    | .this _ => pure ()
    | _ => if plainOf (kindPath c.fuel c.env none q) a then throw ⟨p, msgRPA a⟩
    checkUse c p a last k
  | q => checkRoot c last k q

/-- A path in a term (`inType` false) or in a written type, applied to `k` lists.  In a type, R-K and R-S
follow the checks of the steps. -/
def checkPath (c : Ctx) (inType : Bool) (k : Nat) (q : Path) : Except Err Unit := do
  checkSteps c true k q
  if inType then
    match q.root with
    | .var _ x =>
      match lookup x c.env, q.firstStep? with
      | .param _ true _, some p => throw ⟨p, msgRK⟩
      | _, _ => pure ()
    | _ => pure ()
    match unstablePrefix? c.fuel c.env q with
    | some r => throw ⟨r.pos, msgRS r⟩
    | none => pure ()

/-- Whether `S` is the singleton of a module path. -/
def isModSngl (c : Ctx) (S : Ty) : Bool :=
  match S with
  | .sngl _ q =>
    match kindPath c.fuel c.env none q with
    | .obj _ => true
    | _ => false
  | _ => false

mutual
/-- Whether the name `x` roots a path of the type `T` (rule 6). -/
def tyMentions (x : String) (T : Ty) : Bool :=
  match T with
  | .any _ | .nothing _ | .name .. => false
  | .sel _ q _ | .sngl _ q =>
    match q.root with
    | .var _ y => decide (x = y)
    | _ => false
  | .refine _ ds => declsMention x ds
  | .and S U => tyMentions x S || tyMentions x U
  | .fn _ y S U => tyMentions x S || (!decide (y = some x) && tyMentions x U)
termination_by structural T
/-- Whether `x` roots a path of a bound. -/
def boundMentions (x : String) (b : Bound) : Bool :=
  match b with
  | .absent => false
  | .given T => tyMentions x T
termination_by structural b
/-- Whether `x` roots a path of declarations. -/
def declsMention (x : String) (ds : Decls) : Bool :=
  match ds with
  | .nil => false
  | .typ _ _ lo hi r => boundMentions x lo || boundMentions x hi || declsMention x r
  | .alias _ _ T r | .val _ _ T r => tyMentions x T || declsMention x r
termination_by structural ds
end

mutual
/-- Refuse a written type that breaks a rule. -/
def checkTy (c : Ctx) (T : Ty) : Except Err Unit :=
  match T with
  | .any _ | .nothing _ => .ok ()
  | .sel p q A => do
    checkPath c true 0 q
    checkMember [] p A true
    if q.isRoot then
      match binderOf c q with
      | some e =>
        match headTmpl? e with
        | some t => if declaresIn true e A then pure () else throw (notMember p t true A)
        | none => pure ()
      | none => pure ()
  | .sngl _ q => checkPath c true 0 q
  | .name p A =>
    match lookupTyp A c.env with
    | some (.tmpl (.cls d) :: env) =>
      if !d.body.declaresTyp A && (lookupTyp A env).isSome then .error ⟨p, msgRBN A⟩ else .ok ()
    | some _ => .ok ()
    | none => .error ⟨p, "the type " ++ quote A ++ " is outside the subset"⟩
  | .refine p ds => checkDecls (c.push (.tmpl (.ref p ds))) [] ds
  | .and S U => do
    checkTy c S
    checkTy c U
  | .fn p (some x) S U => do
    checkName [] p x
    let c' := { c with dep := true }
    checkTy c' S
    checkTy (c'.push (.param x (some S) (isModSngl c S))) U
    if !tyMentions x U then
      throw ⟨p, "the parameter " ++ quote x ++ " does not occur in the result: write `S => T`"⟩
  | .fn _ none S U => do
    checkTy c S
    checkTy c U
termination_by structural T
/-- Refuse a bound that breaks a rule. -/
def checkBound (c : Ctx) (b : Bound) : Except Err Unit :=
  match b with
  | .absent => .ok ()
  | .given T => checkTy c T
termination_by structural b
/-- Refuse a refinement's declarations: rule 7, rule 8, R-Y, R-D, then their types.  `seen` holds the
names declared so far. -/
def checkDecls (c : Ctx) (seen : List String) (ds : Decls) : Except Err Unit :=
  match ds with
  | .nil => .ok ()
  | .typ p A lo hi r => do
    checkMember [] p A true
    if mem A seen then throw (dupType p A)
    if mem A (c.classes.map (·.name)) then throw ⟨p, msgRCN⟩
    if onCycleY c.fuel ⟨c.env, A⟩ then
      let e : NodeE := ⟨c.env, A⟩
      let lower := memKey e.key (reachBy (typSuccs c.fuel false) c.fuel (boundEdges c.fuel c.env false lo) [])
      throw ⟨p, msgRY (e140 c.fuel ⟨c.env, A⟩) (if lower then "lower bound" else "upper bound") A⟩
    checkBound c lo
    checkBound c hi
    checkDecls c (A :: seen) r
  | .alias p A T r => do
    checkMember [] p A true
    if mem A seen then throw (dupType p A)
    if mem A (c.classes.map (·.name)) then throw ⟨p, msgRCN⟩
    if onCycleY c.fuel ⟨c.env, A⟩ then throw ⟨p, msgRY (e140 c.fuel ⟨c.env, A⟩) "alias" A⟩
    checkTy c T
    checkDecls c (A :: seen) r
  | .val p a T r => do
    checkMember [] p a false
    if mem a seen then throw (dupField p a)
    checkShape c p a .value
    checkTy c T
    checkDecls c (a :: seen) r
termination_by structural ds
end

/-- Refuse a type that may be absent. -/
def checkTyOpt (c : Ctx) : Option Ty → Except Err Unit
  | some T => checkTy c T
  | none => .ok ()

/-- The constructor parameters of `C`: rule 7, a second parameter of one name, then their types.  A type is
read outside the class body, with the earlier parameters in scope, and the parameter itself and the later ones
as forward references, as scalac reads it (G-1). -/
def checkCParams (c : Ctx) (C : String) (seen : List String) : List CParam → Except Err Unit
  | [] => .ok ()
  | x :: xs => do
    if x.isVal then checkMember [] x.pos x.name false else checkName [] x.pos x.name
    if mem x.name seen then throw ⟨x.pos, quote x.name ++ " is already a parameter of " ++ quote C⟩
    checkTy { c with env := (x :: xs).map (fun y => Entry.later y.name) ++ c.env } x.ty
    checkCParams (c.push (.param x.name (some x.ty) false)) C (x.name :: seen) xs

/-- Where the right side of a definition with the optional type `T` stands: written when `T` is some,
else inferred. -/
def underOf (T : Option Ty) : Under := if T.isSome then .written else .inferred

/-- The parameters of a def, each in scope of the later ones and of the result and body.  Rule 7, and a
second parameter of one name. -/
def checkParams (c : Ctx) (f : String) (seen : List String) : List Param → Except Err Ctx
  | [] => .ok c
  | x :: xs => do
    checkName [] x.pos x.name
    if mem x.name seen then throw ⟨x.pos, quote x.name ++ " is already a parameter of " ++ quote f⟩
    checkTy c x.ty
    checkParams (c.push (.param x.name (some x.ty) false)) f (x.name :: seen) xs

/-- The names of a block's vals. -/
def statsNames : Stats → List String
  | .last _ => []
  | .val _ x _ _ r => x :: statsNames r

/-- R-L, R-V and R-R on a template val: a literal, a path at a type other than its own singleton or
untyped and no module path, anything but a path or a lambda. -/
def checkField (c : Ctx) (p : Pos) (T : Option Ty) (e : Tm) : Except Err Unit :=
  match e, T with
  | .lit .., _ => .error ⟨p, msgRL⟩
  | .lam .., _ => .ok ()
  | .path q, some (.sngl _ q') => if decide (q.erase = q'.erase) then .ok () else .error ⟨p, msgRV⟩
  | .path _, some _ => .error ⟨p, msgRV⟩
  | .path q, none =>
    match kindPath c.fuel c.env none q with
    | .obj _ => .ok ()
    | _ => .error ⟨p, msgRV⟩
  | _, _ => .error ⟨p, msgRR⟩

mutual
/-- Refuse a term that breaks a rule.  It stands at `u` and is applied to `k` argument lists. -/
def checkTm (c : Ctx) (u : Under) (k : Nat) (t : Tm) : Except Err Unit :=
  match t with
  | .path q => checkPath c false k q
  | .sel s p a => do
    checkTm c .other 0 s
    checkMember [] p a false
    match s with
    | .new _ K _ => if plainOf (clsKind c.fuel c.env K) a then throw ⟨p, msgRPA a⟩
    | _ => pure ()
    checkUse c p a true k
  | .app f e => do
    checkTm c .other (k + 1) f
    checkTm c .other 0 e
  | .lam p x T b => do
    checkName [] p x
    checkTyOpt c T
    let m := match T with
      | some S => isModSngl c S
      | none => false
    checkTm (c.push (.param x T m)) .other 0 b
  | .asc _ e T => do
    checkTm c .written 0 e
    checkTy c T
  | .block _ ss => checkStats c [] ss
  | .lit p s ms => do
    litUnder p u
    match s with
    | some x => checkName [] p x
    | none => pure ()
    checkMems (c.push (.tmpl (.lit p s ms))) "object literal" [] s ms
  | .new _ K as => do
    match K.pre with
    | some q => checkPath c false 0 q
    | none => pure ()
    checkMember [] K.pos K.name true
    match clsKind c.fuel c.env K with
    | .inst _ => pure ()
    | _ => throw ⟨K.pos, msgNoCls K.name⟩
    checkArgs c as
termination_by structural t
/-- Refuse arguments, each at `other`. -/
def checkArgs (c : Ctx) (as : Args) : Except Err Unit :=
  match as with
  | .nil => .ok ()
  | .cons t r => do
    checkTm c .other 0 t
    checkArgs c r
termination_by structural as
/-- Refuse the arguments of parents, outside the class body with the class's parameters in scope (G-1). -/
def checkParentArgs (c : Ctx) (Ps : Parents) : Except Err Unit :=
  match Ps with
  | .nil => .ok ()
  | .cons _ as r => do
    checkArgs c as
    checkParentArgs c r
termination_by structural Ps
/-- Refuse the members of a class or trait body, the class at the head of `c.env`, with the noun `noun`:
rule 7, rule 8, R-CN, R-Y, R-D, R-VT, R-R, R-C, then the parts.  `seen` holds the parameters and the names declared so
far. -/
def checkCMems (c : Ctx) (noun : String) (seen : List String) (ms : CMems) : Except Err Unit :=
  match ms with
  | .nil => .ok ()
  | .typ p _ A lo hi r => do
    checkMember [] p A true
    if mem A seen then throw (dupMem noun p false A)
    if mem A (c.classes.map (·.name)) then throw ⟨p, msgRCN⟩
    if onCycleY c.fuel ⟨c.env, A⟩ then
      let e : NodeE := ⟨c.env, A⟩
      let lower := memKey e.key (reachBy (typSuccs c.fuel false) c.fuel (boundEdges c.fuel c.env false lo) [])
      throw ⟨p, msgRY (e140 c.fuel e) (if lower then "lower bound" else "upper bound") A⟩
    checkBound c lo
    checkBound c hi
    checkCMems c noun (A :: seen) r
  | .alias p _ A T r => do
    checkMember [] p A true
    if mem A seen then throw (dupMem noun p false A)
    if mem A (c.classes.map (·.name)) then throw ⟨p, msgRCN⟩
    if onCycleY c.fuel ⟨c.env, A⟩ then throw ⟨p, msgRY (e140 c.fuel ⟨c.env, A⟩) "alias" A⟩
    checkTy c T
    checkCMems c noun (A :: seen) r
  | .valDecl p _ a T r => do
    checkMember [] p a false
    if mem a seen then throw (dupMem noun p false a)
    checkShape c p a .value
    checkTy c T
    checkCMems c noun (a :: seen) r
  | .val p _ a T e r => do
    checkMember [] p a false
    if mem a seen then throw (dupMem noun p false a)
    checkShape c p a .value
    checkClsField p e
    if onCycleC c.fuel ⟨c.env, a⟩ then throw ⟨p, msgRC a⟩
    checkTy c T
    checkTm c .written 0 e
    checkCMems c noun (a :: seen) r
  | .defDecl p o f ps R r => do
    checkMember [] p f false
    if mem f seen then throw (dupMem noun p false f)
    checkShape c p f (.meth ps.length)
    if overloads o (((clsOf? c.env).map fun d => decide (d.kind ≠ .concrete)).getD false) c.env f ps then
      throw ⟨p, msgROL f⟩
    let c' ← checkParams c f [] ps
    checkTy c' R
    checkCMems c noun (f :: seen) r
  | .defn p o f ps R e r => do
    checkMember [] p f false
    if mem f seen then throw (dupMem noun p false f)
    checkShape c p f (.meth ps.length)
    if overloads o (((clsOf? c.env).map fun d => decide (d.kind ≠ .concrete)).getD false) c.env f ps then
      throw ⟨p, msgROL f⟩
    let c' ← checkParams c f [] ps
    checkTy c' R
    checkTm c' .written 0 e
    checkCMems c noun (f :: seen) r
termination_by structural ms
/-- Refuse a block's statements: rule 7, rule 8, and rule 9 through the `defining` and `later` entries.
`seen` holds the names defined so far. -/
def checkStats (c : Ctx) (seen : List String) (ss : Stats) : Except Err Unit :=
  match ss with
  | .last t => checkTm c .other 0 t
  | .val p x T e r => do
    checkName [] p x
    if mem x seen then throw ⟨p, quote x ++ " is already defined in this block (scalac E161)"⟩
    let c' := { c with env := .defining x T.isSome :: (statsNames r).map .later ++ c.env }
    checkTyOpt c' T
    checkTm c' (underOf T) 0 e
    checkStats (c.push (.val x T e)) (x :: seen) r
termination_by structural ss
/-- Refuse the members of a template with the noun `noun` and the self name `self`: rule 7, rule 8, R-D,
R-Y, R-L, R-R, R-V, R-C, then the parts.  `seen` holds the names declared so far. -/
def checkMems (c : Ctx) (noun : String) (seen : List String) (self : Option String) (ms : Mems) :
    Except Err Unit :=
  match ms with
  | .nil => .ok ()
  | .obj p o s b r => do
    checkMember [] p o false
    if mem o seen then throw (dupMem noun p false o)
    if decide (self = some o) then throw (dupMem noun p true o)
    checkShape c p o .value
    match s with
    | some x => checkName [] p x
    | none => pure ()
    checkMems (c.push (.tmpl (.obj p o s b))) "object" [] s b
    checkMems c noun (o :: seen) self r
  | .typ p A T r => do
    checkMember [] p A true
    if mem A seen then throw (dupMem noun p false A)
    if decide (self = some A) then throw (dupMem noun p true A)
    if mem A (c.classes.map (·.name)) then throw ⟨p, msgRCN⟩
    if onCycleY c.fuel ⟨c.env, A⟩ then throw ⟨p, msgRY (e140 c.fuel ⟨c.env, A⟩) "alias" A⟩
    checkTy c T
    checkMems c noun (A :: seen) self r
  | .val p a T e r => do
    checkMember [] p a false
    if mem a seen then throw (dupMem noun p false a)
    if decide (self = some a) then throw (dupMem noun p true a)
    checkShape c p a .value
    checkField c p T e
    if onCycleC c.fuel ⟨c.env, a⟩ then throw ⟨p, msgRC a⟩
    checkTyOpt c T
    checkTm c (underOf T) 0 e
    checkMems c noun (a :: seen) self r
  | .defn p f ps R e r => do
    checkMember [] p f false
    if mem f seen then throw (dupMem noun p false f)
    if decide (self = some f) then throw (dupMem noun p true f)
    checkShape c p f (.meth ps.length)
    let c' ← checkParams c f [] ps
    checkTyOpt c' R
    checkTm c' (underOf R) 0 e
    checkMems c noun (f :: seen) self r
  | .cls p k C ps Ps b r => do
    let d : ClsDecl := ⟨p, k, C, ps, Ps, b⟩
    checkMember [] p C true
    if mem C seen then throw (dupMem noun p false C)
    if secondCls p C c.classes then throw ⟨p, msgRCN2⟩
    checkClsHead c d
    checkCParams c C [] ps
    checkParentArgs (ps.foldl (fun c' x => c'.push (.param x.name (some x.ty) false)) c) Ps
    let cK := c.push (.tmpl (.cls d))
    checkCMems cK (Tmpl.cls d).noun (ps.map (·.name)) b
    checkInherited cK d
    checkMems c noun (C :: seen) self r
termination_by structural ms
end

end Scope

/-! ## The entry point -/

/-- Refuse a parsed file that breaks a rule, at the first node in text order. -/
def check (F : File) : Except Err Unit := do
  let c : Scope.Ctx := ⟨Scope.stemEnv F, false, F.size + 1, F.shapes, F.mems.classes⟩
  Scope.checkMems c "object" [] none F.mems
  Scope.checkTyOpt c F.ty
  Scope.checkTm c (Scope.underOf F.ty) 0 F.body

end NominalFrontend.ScalaRead
