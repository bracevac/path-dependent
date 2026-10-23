import Coercions.ScalaSyntax.Ast

/-!
# Scopes, checks and the label table

The third stage of the Scala reader.  `check` walks a parsed `Program` and
refuses, at the position of the node, every name that Scala would read
differently from the subset (plan IX, S-13), every cycle of type members that
scalac refuses (S-16), and every object literal that is not under a written
type (S-12).
`labels` lists the member names of a program in order of first appearance,
each with its sort, for the label table of a front end (S-8).

Both are front-end neutral.  Whether a capture form belongs to a front end is
the question of that front end's translation.

The walk carries a context, innermost first: the lambda parameters and the
binders of dependent function types, the block `val`s seen so far, the `val`
whose right side the walk is in and the later `val`s of its block, and the
templates around the node (a refinement or an object literal, with the names
it declares and its self name).  It also records whether the walk is inside a
dependent function type, the platform names of `def program`, and the names
of the prelude.

The tree holds names as `String`s, and `String.toList` depends on
`Classical.choice` in Lean v4.29.1.  So the characters of a name are read off
its UTF-8 bytes (`String.toByteArray`, which depends on no axiom).  The parser
makes ASCII names only, one byte per character.  Every function is
structural, and the reachability of a cycle runs on a fuel.

This module imports Lean core only, through `Ast`.
-/

namespace ScalaSyntax

namespace Scope

/-! ## Names -/

/-- The characters of a name, one per byte of its UTF-8 encoding.  For an
ASCII name these are its characters. -/
def nameChars (x : String) : List Char :=
  x.toByteArray.data.toList.map fun b => Char.ofNat b.toNat

/-- Whether a name starts with an upper case letter, the sort of a member
name: a type member, capture members included, or a field. -/
def isUpperName (x : String) : Bool :=
  match nameChars x with
  | c :: _ => c.isUpper
  | [] => false

/-- Whether `x` is in the list. -/
def mem (x : String) : List String → Bool
  | [] => false
  | y :: ys => decide (x = y) || mem x ys

/-- A name in backquotes, for a message. -/
def quote (x : String) : String := "`" ++ x ++ "`"

/-- Whether the characters form a name of the subset: a letter, then
letters, digits and `_`. -/
def nameShape : List Char → Bool
  | c :: cs => c.isAlpha && cs.all fun d => d.isAlphanum || d == '_'
  | [] => false

/-- The members of `Any`, `AnyRef` and `Function1` (plan S-13).  Every
template inherits them, so inside one such a name means the member. -/
def anyMember : List Char → Bool
  | ['t','o','S','t','r','i','n','g'] | ['h','a','s','h','C','o','d','e'] | ['e','q','u','a','l','s']
  | ['g','e','t','C','l','a','s','s'] | ['w','a','i','t'] | ['n','o','t','i','f','y']
  | ['n','o','t','i','f','y','A','l','l'] | ['c','l','o','n','e'] | ['f','i','n','a','l','i','z','e']
  | ['e','q'] | ['n','e'] | ['s','y','n','c','h','r','o','n','i','z','e','d']
  | ['i','s','I','n','s','t','a','n','c','e','O','f']
  | ['a','s','I','n','s','t','a','n','c','e','O','f'] | ['a','p','p','l','y']
  | ['a','n','d','T','h','e','n'] | ['c','o','m','p','o','s','e'] => true
  | _ => false

/-- The types of the subset's text that a member of the same name would
hide: `Any`, `Nothing`, `Object`. -/
def topType : List Char → Bool
  | ['A','n','y'] | ['N','o','t','h','i','n','g'] | ['O','b','j','e','c','t'] => true
  | _ => false

/-- Refuse a binder or member name `x` at `p`, whose characters are `cs`,
that the subset cannot write or that Scala reads as something else: not a name
of the subset, a keyword, a member of `Any`, `AnyRef` or `Function1`, `caps`,
or a name of the prelude `prel` (plan S-13).  A binder named `caps` would turn
`caps.any` into a selection on it (probe `CapsVar`). -/
def checkChars (prel : List String) (p : Pos) (x : String) (cs : List Char) : Except Err Unit :=
  if !nameShape cs then
    .error ⟨p, quote x ++ " is not a name of the subset: a letter, then letters, digits and `_`"⟩
  else
    match wordOf cs with
    | .kw | .reserved => .error ⟨p, quote x ++ " is a keyword of Scala"⟩
    | .name =>
      if anyMember cs then .error ⟨p, quote x ++ " is a member of every Scala object: rename it"⟩
      else if cs == ['c','a','p','s'] then
        .error ⟨p, "`caps` names the package of `caps.any` in Scala: rename it"⟩
      else if mem x prel then .error ⟨p, quote x ++ " is a class or trait of the prelude: rename it"⟩
      else .ok ()

/-- Refuse a binder name `x` at `p`, as `checkChars` does. -/
def checkName (prel : List String) (p : Pos) (x : String) : Except Err Unit :=
  checkChars prel p x (nameChars x)

/-- Refuse a member name `x` at `p`, declared or selected, as `checkName`
does, and also a member named `Any`, `Nothing` or `Object`, a type member
(`typ`) that starts lower case, and a field that starts upper case. -/
def checkMember (prel : List String) (p : Pos) (x : String) (typ : Bool) : Except Err Unit := do
  let cs := nameChars x
  checkChars prel p x cs
  if topType cs then
    throw ⟨p, "a member named " ++ quote x ++ " hides the type " ++ quote x ++ " in Scala: rename it"⟩
  let up := match cs with
    | c :: _ => c.isUpper
    | [] => false
  if typ && !up then
    throw ⟨p, "the type member " ++ quote x ++ " starts lower case: type members start upper case"⟩
  if !typ && up then
    throw ⟨p, "the field " ++ quote x ++ " starts upper case: fields start lower case"⟩

/-! ## Templates and the context -/

/-- A refinement or an object literal around the node, with the names it
declares. -/
structure Template where
  /-- Whether it is an object literal. -/
  lit : Bool
  /-- The self name of a literal, if one is written. -/
  self : Option String
  /-- The type members, capture members included. -/
  types : List String
  /-- The fields. -/
  fields : List String

/-- Whether the template declares a member named `x`. -/
def Template.declares (t : Template) (x : String) : Bool := mem x t.types || mem x t.fields

/-- How a message names a template. -/
def Template.noun (t : Template) : String := if t.lit then "object literal" else "refinement"

/-- The type members of a refinement, capture members included. -/
def declsTypes : Decls → List String
  | .nil => []
  | .typ _ A _ _ r | .alias _ A _ r | .cap _ A _ _ r | .capAlias _ A _ r => A :: declsTypes r
  | .val _ _ _ r => declsTypes r

/-- The fields of a refinement. -/
def declsFields : Decls → List String
  | .nil => []
  | .typ _ _ _ _ r | .alias _ _ _ r | .cap _ _ _ _ r | .capAlias _ _ _ r => declsFields r
  | .val _ a _ r => a :: declsFields r

/-- The type members of a literal, capture members included. -/
def defsTypes : Defs → List String
  | .nil => []
  | .typ _ A _ r | .cap _ A _ r => A :: defsTypes r
  | .val _ _ _ _ r => defsTypes r

/-- The fields of a literal. -/
def defsFields : Defs → List String
  | .nil => []
  | .typ _ _ _ r | .cap _ _ _ r => defsFields r
  | .val _ a _ _ r => a :: defsFields r

/-- The `val` names of the statements of a block, in order. -/
def statsNames : Stats → List String
  | .last _ => []
  | .val _ x _ _ r => x :: statsNames r

/-- What the walk has passed on its way to a node, innermost first. -/
inductive Entry where
  /-- A lambda parameter or the binder of a dependent function type. -/
  | param (x : String)
  /-- A block `val` seen so far. -/
  | val (x : String)
  /-- The block `val` whose type or right side the walk is in, with whether
  its type is written. -/
  | defining (x : String) (typed : Bool)
  /-- A later `val` of the same block. -/
  | later (x : String)
  /-- A template. -/
  | tmpl (t : Template)

/-- The context of the walk. -/
structure Ctx where
  /-- The binders and templates around the node, innermost first. -/
  env : List Entry
  /-- Whether the walk is inside a dependent function type `(x: S) => T`. -/
  dep : Bool
  /-- The platform names, the parameters of `def program`. -/
  plat : List String
  /-- The names of the prelude's classes and traits. -/
  prel : List String
  /-- The names of the prelude's classifier traits. -/
  cls : List String

/-- The innermost template, which `this` names. -/
def innermost : List Entry → Option Template
  | [] => none
  | .tmpl t :: _ => some t
  | _ :: env => innermost env

/-- What a bare name refers to. -/
inductive Ref where
  /-- A lambda parameter, the binder of a dependent function type, or an
  earlier block `val`. -/
  | bound
  /-- The self name of the literal `t`. -/
  | self (t : Template)
  /-- The block `val` whose right side holds the name, with whether its type
  is written. -/
  | defining (typed : Bool)
  /-- A later `val` of the same block. -/
  | later
  /-- A platform name. -/
  | plat
  /-- A member of the template `t`.  `inner` when `t` is the innermost
  template, and `hidden` when a binder of the name lies further out. -/
  | member (t : Template) (inner hidden : Bool)
  /-- Nothing in scope. -/
  | none

/-- Whether `env` or the platform names `plat` bind `x`. -/
def bindsOuter (x : String) (plat : List String) : List Entry → Bool
  | [] => mem x plat
  | .param y :: env | .val y :: env | .defining y _ :: env | .later y :: env =>
    decide (x = y) || bindsOuter x plat env
  | .tmpl t :: env => decide (t.self = some x) || bindsOuter x plat env

/-- What the bare name `x` refers to, innermost first.  A template that
declares a member `x` takes the name, as in Scala.  `inner` holds until the
walk passes a template. -/
def lookup (x : String) (plat : List String) (inner : Bool) : List Entry → Ref
  | [] => if mem x plat then .plat else .none
  | .param y :: env | .val y :: env =>
    if decide (x = y) then .bound else lookup x plat inner env
  | .defining y typed :: env => if decide (x = y) then .defining typed else lookup x plat inner env
  | .later y :: env => if decide (x = y) then .later else lookup x plat inner env
  | .tmpl t :: env =>
    if t.declares x then .member t inner (bindsOuter x plat env)
    else if decide (t.self = some x) then .self t
    else lookup x plat false env

/-- Refuse the bare name `x` at `p`, in a term or at the head of a path, or in
a capture set when `inCaps`, unless it is in scope as Scala reads it.  The
result is the literal whose self name `x` is, if it is one. -/
def checkVar (c : Ctx) (p : Pos) (x : String) (inCaps : Bool) : Except Err (Option Template) :=
  match lookup x c.plat true c.env with
  | .bound => .ok none
  | .self t => .ok (some t)
  | .defining false =>
    .error ⟨p, "recursive value " ++ quote x ++ " needs a type: its right side names it (scalac E045)"⟩
  | .defining true =>
    .error ⟨p, "forward reference: the right side of " ++ quote x ++ " names it (scalac E039)"⟩
  | .later =>
    .error ⟨p, "forward reference: " ++ quote x ++ " is defined later in this block (scalac E039)"⟩
  | .plat =>
    if inCaps then .ok none
    else .error ⟨p, quote x ++ " is a platform name: it stands only in capture sets"⟩
  | .member t inner hidden =>
    if hidden then
      .error ⟨p, quote x ++ " names the member of the enclosing " ++
        (if t.lit then "object" else "refinement") ++ " here, as in Scala: rename the variable"⟩
    else if t.lit && inner then
      .error ⟨p, quote x ++ " is a member: members are named through a path, write " ++
        quote ("this." ++ x)⟩
    else
      match t.lit, t.self with
      | true, some s =>
        .error ⟨p, quote x ++ " is a member: members are named through a path, write " ++
          quote (s ++ "." ++ x)⟩
      | _, _ =>
        .error ⟨p, quote x ++ " is a member of " ++ (if inner then "the" else "an") ++ " enclosing " ++
          t.noun ++ ": members are named through a path"⟩
  | .none =>
    if mem x c.prel then .error ⟨p, quote x ++ " is a class or trait of the prelude, not a value"⟩
    else .error ⟨p, quote x ++ " is not in scope"⟩

/-- Refuse a classifier name `k` at `p` that the prelude does not declare. -/
def checkClassifier (c : Ctx) (p : Pos) (k : String) : Except Err Unit :=
  if mem k c.cls then .ok ()
  else .error ⟨p, quote k ++ " is not in scope: the prelude declares no classifier " ++ quote k⟩

/-- Refuse a capture set whose names are not in scope. -/
def checkCaps (c : Ctx) : CapSet → Except Err Unit
  | [] => .ok ()
  | .var p x :: cs => do
    discard (checkVar c p x true)
    checkCaps c cs
  | .any _ :: cs => checkCaps c cs
  | .only p x k :: cs => do
    match x with
    | some y => discard (checkVar c p y true)
    | Option.none => pure ()
    checkClassifier c p k
    checkCaps c cs

/-- Refuse an optional capture set whose names are not in scope. -/
def checkCapsOpt (c : Ctx) : Option CapSet → Except Err Unit
  | some cs => checkCaps c cs
  | Option.none => .ok ()

/-- Refuse the arrow of a function type whose capture set names are not in
scope. -/
def checkArrow (c : Ctx) : Arrow → Except Err Unit
  | .fat => .ok ()
  | .thin cs => checkCapsOpt c cs

/-- The refusal of a selection of `x` on a template that does not declare it
(scalac E008). -/
def notMember (p : Pos) (t : Template) (typ : Bool) (x : String) : Err :=
  ⟨p, (if typ then "type " else "value ") ++ x ++ " is not a member of the " ++ t.noun ++
    " (scalac E008)"⟩

/-- The refusal at `p` of a second type member `A` in one refinement (scalac
E161). -/
def dupType (p : Pos) (A : String) : Err :=
  ⟨p, quote A ++ " is already defined in this refinement (scalac E161)"⟩

/-- The refusal at `p` of a second field `a` in one refinement (scalac E120). -/
def dupField (p : Pos) (a : String) : Err :=
  ⟨p, "conflicting definitions of " ++ quote a ++ " in one refinement (scalac E120)"⟩

/-- The refusal at `p` of a second member `x` in one literal, or of a member
named as the literal's self name (scalac E120). -/
def dupLit (p : Pos) (self : Bool) (x : String) : Err :=
  if self then
    ⟨p, "conflicting definitions of the self name and the member " ++ quote x ++ " (scalac E120)"⟩
  else ⟨p, "conflicting definitions of " ++ quote x ++ " in one object literal (scalac E120)"⟩

/-! ## Free names and cycles -/

/-- Whether a capture set names `x`. -/
def capsMention (x : String) : CapSet → Bool
  | [] => false
  | .var _ y :: cs => decide (x = y) || capsMention x cs
  | .only _ (some y) _ :: cs => decide (x = y) || capsMention x cs
  | _ :: cs => capsMention x cs

/-- Whether an optional capture set names `x`. -/
def capsMentionOpt (x : String) : Option CapSet → Bool
  | some cs => capsMention x cs
  | Option.none => false

/-- Whether the capture set of an arrow names `x`. -/
def arrowMentions (x : String) : Arrow → Bool
  | .fat => false
  | .thin cs => capsMentionOpt x cs

mutual
/-- Whether `x` occurs free in a type: at the head of a path or in a capture
set, outside the binders of dependent function types that rebind it. -/
def tyMentions (x : String) (T : Ty) : Bool :=
  match T with
  | .any _ | .nothing _ | .sel _ (.this _) _ => false
  | .sel _ (.var _ y) _ => decide (x = y)
  | .refine _ ds => declsMention x ds
  | .and S U => tyMentions x S || tyMentions x U
  | .fn _ y S a U =>
    tyMentions x S || arrowMentions x a || (!decide (y = some x) && tyMentions x U)
  | .capt _ S cs => tyMentions x S || capsMentionOpt x cs
termination_by structural T
/-- Whether `x` occurs free in an optional type. -/
def tyMentionsOpt (x : String) (T : Option Ty) : Bool :=
  match T with
  | some U => tyMentions x U
  | Option.none => false
termination_by structural T
/-- Whether `x` occurs free in the declarations of a refinement. -/
def declsMention (x : String) (ds : Decls) : Bool :=
  match ds with
  | .nil => false
  | .typ _ _ lo hi r => tyMentionsOpt x lo || tyMentionsOpt x hi || declsMention x r
  | .alias _ _ T r | .val _ _ T r => tyMentions x T || declsMention x r
  | .cap _ _ lo hi r => capsMentionOpt x lo || capsMentionOpt x hi || declsMention x r
  | .capAlias _ _ cs r => capsMention x cs || declsMention x r
termination_by structural ds
end

mutual
/-- The members that a type selects on a template's own binder: `this.B`
when `top` (the template's own level, outside nested refinements, where
`this` names the nested one), and `s.B` for its self name `self`, which no
nested refinement rebinds. -/
def tySelects (top : Bool) (self : Option String) (T : Ty) : List String :=
  match T with
  | .any _ | .nothing _ => []
  | .sel _ (.this _) B => if top then [B] else []
  | .sel _ (.var _ y) B => if decide (self = some y) then [B] else []
  | .refine _ ds => declsSelects self ds
  | .and S U => tySelects top self S ++ tySelects top self U
  | .fn _ y S _ U =>
    tySelects top self S ++ tySelects top (if decide (self = y) then Option.none else self) U
  | .capt _ S _ => tySelects top self S
termination_by structural T
/-- The members that an optional type selects on a template's own binder. -/
def tySelectsOpt (top : Bool) (self : Option String) (T : Option Ty) : List String :=
  match T with
  | some U => tySelects top self U
  | Option.none => []
termination_by structural T
/-- The members that the declarations of a nested refinement select on the
outer template's self name. -/
def declsSelects (self : Option String) (ds : Decls) : List String :=
  match ds with
  | .nil => []
  | .typ _ _ lo hi r =>
    tySelectsOpt false self lo ++ tySelectsOpt false self hi ++ declsSelects self r
  | .alias _ _ T r | .val _ _ T r => tySelects false self T ++ declsSelects self r
  | .cap _ _ _ _ r | .capAlias _ _ _ r => declsSelects self r
termination_by structural ds
end

/-- The members that a type selects on a template's own binder outside every
function type and nested refinement, on `this` or on the self name `self`.
Under a function type scalac admits a selection of the member itself in an
upper bound as an F-bound (LP's `p`), and inside a nested refinement `this`
names that refinement. -/
def tyDirect (self : Option String) (T : Ty) : List String :=
  match T with
  | .sel _ (.this _) B => [B]
  | .sel _ (.var _ y) B => if decide (self = some y) then [B] else []
  | .and S U => tyDirect self S ++ tyDirect self U
  | .capt _ S _ => tyDirect self S
  | _ => []
termination_by structural T

/-- The members that an optional type selects outside function types. -/
def tyDirectOpt (self : Option String) : Option Ty → List String
  | some T => tyDirect self T
  | Option.none => []

/-- The edges of the cycle check of a refinement: each type member, and the
members that its alias or bounds select on `this`. -/
def declsEdges : Decls → List (String × List String)
  | .nil => []
  | .typ _ A lo hi r =>
    (A, tySelectsOpt true Option.none lo ++ tySelectsOpt true Option.none hi) :: declsEdges r
  | .alias _ A T r => (A, tySelects true Option.none T) :: declsEdges r
  | .val _ _ _ r | .cap _ _ _ _ r | .capAlias _ _ _ r => declsEdges r

/-- The plain edges among them, which scalac never admits on a cycle: from an
alias, a lower bound, or an upper bound outside its function types. -/
def declsPlain : Decls → List (String × List String)
  | .nil => []
  | .typ _ A lo hi r =>
    (A, tySelectsOpt true Option.none lo ++ tyDirectOpt Option.none hi) :: declsPlain r
  | .alias _ A T r => (A, tySelects true Option.none T) :: declsPlain r
  | .val _ _ _ r | .cap _ _ _ _ r | .capAlias _ _ _ r => declsPlain r

/-- The direct edges among them, outside every function type.  scalac reports
a cycle of several members along them as E140, and any other cycle of several
members by exceeding its recursion limit (probes `CycUpper`, `UpFun2`). -/
def declsDirect : Decls → List (String × List String)
  | .nil => []
  | .typ _ A lo hi r => (A, tyDirectOpt Option.none lo ++ tyDirectOpt Option.none hi) :: declsDirect r
  | .alias _ A T r => (A, tyDirect Option.none T) :: declsDirect r
  | .val _ _ _ r | .cap _ _ _ _ r | .capAlias _ _ _ r => declsDirect r

/-- The edges of the cycle check of a literal with the self name `self`.  A
literal's type members are aliases, so every edge is plain. -/
def defsEdges (self : Option String) : Defs → List (String × List String)
  | .nil => []
  | .typ _ A T r => (A, tySelects true self T) :: defsEdges self r
  | .val _ _ _ _ r | .cap _ _ _ r => defsEdges self r

/-- The direct edges of a literal, outside every function type. -/
def defsDirect (self : Option String) : Defs → List (String × List String)
  | .nil => []
  | .typ _ A T r => (A, tyDirect self T) :: defsDirect self r
  | .val _ _ _ _ r | .cap _ _ _ r => defsDirect self r

/-- The members that the edges `E` lead to from `x`. -/
def succs (x : String) : List (String × List String) → List String
  | [] => []
  | (y, bs) :: E => (if decide (x = y) then bs else []) ++ succs x E

/-- The number of names in the edges, which bounds the steps of `reach`. -/
def edgesSize : List (String × List String) → Nat
  | [] => 0
  | (_, bs) :: E => bs.length + 1 + edgesSize E

/-- The members reachable from `todo` along the edges `E`, added to `seen`.
Each step takes one name off `todo`, and a name pushes its successors only the
first time it is seen, so the fuel `edgesSize E + todo.length + 1` suffices. -/
def reach (E : List (String × List String)) : Nat → List String → List String → List String
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, x :: todo, seen =>
    if mem x seen then reach E n todo seen
    else reach E n (todo ++ succs x E) (x :: seen)

/-- Whether the members `start` lead to `A` along the edges `E`. -/
def leadsTo (E : List (String × List String)) (A : String) (start : List String) : Bool :=
  mem A (reach E (edgesSize E + start.length + 1) start [])

/-- Whether the type member `A` lies on a cycle that scalac refuses, along
the edges `E` with the plain edges `P` among them.  A cycle through another
member is refused whatever its edges (probes `CycUpper`, `UpFun2`), and so is
a plain edge from `A` to itself (`LPsrc`).  Only an upper bound that selects
`A` under a function type stays, an F-bound (LP's `p`). -/
def onCycle (E P : List (String × List String)) (A : String) : Bool :=
  mem A (succs A P) || leadsTo E A ((succs A E).filter fun B => !decide (B = A))

/-- The refusal at `p` of the cyclic alias or bound `what` of `A`, with
scalac's reason: E140 for a plain edge from `A` to itself or a cycle of
direct edges `D`, and its recursion limit for any other cycle. -/
def cyclic (P D : List (String × List String)) (p : Pos) (what A : String) : Err :=
  ⟨p, "illegal cyclic type reference: the " ++ what ++ " of " ++ quote A ++ " refers back to " ++
    quote A ++
    (if mem A (succs A P) || leadsTo D A ((succs A D).filter fun B => !decide (B = A))
     then " (scalac E140)" else " (scalac exceeds its recursion limit)")⟩

/-! ## The walk of types -/

/-- Refuse the path of a type selection, and give the template that it names
when it is `this` or a self name, for the member check. -/
def checkPath (c : Ctx) : Path → Except Err (Option Template)
  | .this p =>
    if c.dep then .error ⟨p, "inside `(x: S) => T` scalac reads `this` as the enclosing object"⟩
    else
      match innermost c.env with
      | some t => .ok (some t)
      | Option.none =>
        .error ⟨p, "`this` outside every refinement and object literal names the wrapper object in Scala"⟩
  | .var p x => checkVar c p x false

mutual
/-- Refuse a type that breaks a rule of the subset. -/
def checkTy (c : Ctx) (T : Ty) : Except Err Unit :=
  match T with
  | .any _ | .nothing _ => .ok ()
  | .sel p q A => do
    let t ← checkPath c q
    checkMember c.prel p A true
    match t with
    | some t => if mem A t.types then pure () else throw (notMember p t true A)
    | Option.none => pure ()
  | .refine _ ds =>
    let t : Template := ⟨false, Option.none, declsTypes ds, declsFields ds⟩
    checkDecls { c with env := .tmpl t :: c.env } (declsEdges ds) (declsPlain ds) (declsDirect ds) [] ds
  | .and S U => do
    checkTy c S
    checkTy c U
  | .fn p (some x) S a U => do
    checkName c.prel p x
    let c' := { c with dep := true }
    checkTy c' S
    checkArrow c' a
    checkTy { c' with env := .param x :: c.env } U
    if !tyMentions x U then
      throw ⟨p, "the parameter " ++ quote x ++ " does not occur in the result: write `S => T`"⟩
  | .fn _ Option.none S a U => do
    checkTy c S
    checkArrow c a
    checkTy c U
  | .capt _ S cs => do
    checkTy c S
    checkCapsOpt c cs
termination_by structural T
/-- Refuse an optional type that breaks a rule of the subset. -/
def checkTyOpt (c : Ctx) (T : Option Ty) : Except Err Unit :=
  match T with
  | some U => checkTy c U
  | Option.none => .ok ()
termination_by structural T
/-- Refuse the declarations of a refinement, whose template is the innermost
of `c`.  `E` holds the edges of its cycle check, `P` and `D` the plain and the
direct ones among them, and `seen` the names declared before. -/
def checkDecls (c : Ctx) (E P D : List (String × List String)) (seen : List String) (ds : Decls) :
    Except Err Unit :=
  match ds with
  | .nil => .ok ()
  | .typ p A lo hi r => do
    checkMember c.prel p A true
    if mem A seen then throw (dupType p A)
    if onCycle E P A then
      throw (cyclic P D p (if leadsTo E A (tySelectsOpt true Option.none lo) then "lower bound"
        else "upper bound") A)
    checkTyOpt c lo
    checkTyOpt c hi
    checkDecls c E P D (A :: seen) r
  | .alias p A T r => do
    checkMember c.prel p A true
    if mem A seen then throw (dupType p A)
    if onCycle E P A then throw (cyclic P D p "alias" A)
    checkTy c T
    checkDecls c E P D (A :: seen) r
  | .val p a T r => do
    checkMember c.prel p a false
    if mem a seen then throw (dupField p a)
    checkTy c T
    checkDecls c E P D (a :: seen) r
  | .cap p C lo hi r => do
    checkMember c.prel p C true
    if mem C seen then throw (dupType p C)
    checkCapsOpt c lo
    checkCapsOpt c hi
    checkDecls c E P D (C :: seen) r
  | .capAlias p C cs r => do
    checkMember c.prel p C true
    if mem C seen then throw (dupType p C)
    checkCaps c cs
    checkDecls c E P D (C :: seen) r
termination_by structural ds
end

/-! ## The walk of terms -/

/-- Where a term stands, for the rule that a literal stands only under a
written type (plan S-12). -/
inductive Under where
  /-- The term of an ascription, or the right side of a typed `val`, typed
  literal member or typed program. -/
  | written
  /-- The right side of an untyped `val`, literal member or program, which
  scalac types from the right side. -/
  | inferred
  /-- Anywhere else: an argument, a function, a lambda body, the receiver of a
  selection, the result of a block. -/
  | other

/-- Where the right side of a definition with the optional type `T` stands. -/
def underOf (T : Option Ty) : Under := if T.isSome then .written else .inferred

/-- The template whose members a selection on the term `t` names, when `t` is
`this` or a self name. -/
def selfOf (c : Ctx) : Tm → Option Template
  | .this _ => innermost c.env
  | .var _ x =>
    match lookup x c.plat true c.env with
    | .self t => some t
    | _ => Option.none
  | _ => Option.none

/-- The refusal of a literal at `p` that is not under a written type. -/
def litUnder (p : Pos) : Under → Except Err Unit
  | .written => .ok ()
  | .inferred => .error ⟨p, "an object literal needs a written type: scalac types it as Object"⟩
  | .other => .error ⟨p, "an object literal needs a written type: write `(new Object { … }: T)`"⟩

mutual
/-- Refuse a term that breaks a rule of the subset.  `u` says where it
stands. -/
def checkTm (c : Ctx) (u : Under) (t : Tm) : Except Err Unit :=
  match t with
  | .var p x => discard (checkVar c p x false)
  | .this p =>
    match innermost c.env with
    | some _ => .ok ()
    | Option.none =>
      .error ⟨p, "`this` outside every refinement and object literal names the wrapper object in Scala"⟩
  | .sel s p a => do
    checkTm c .other s
    checkMember c.prel p a false
    match selfOf c s with
    | some t => if mem a t.fields then pure () else throw (notMember p t false a)
    | Option.none => pure ()
  | .app f e => do
    checkTm c .other f
    checkTm c .other e
  | .lam p x T b => do
    checkName c.prel p x
    checkTyOpt c T
    checkTm { c with env := .param x :: c.env } .other b
  | .asc _ e T => do
    checkTm c .written e
    checkTy c T
  | .block _ ss => checkStats c [] ss
  | .lit p s ds => do
    litUnder p u
    match s with
    | some x => checkName c.prel p x
    | Option.none => pure ()
    let tp : Template := ⟨true, s, defsTypes ds, defsFields ds⟩
    checkDefs { c with env := .tmpl tp :: c.env } (defsEdges s ds) (defsDirect s ds) [] s ds
termination_by structural t
/-- Refuse the statements of a block.  `seen` holds the `val`s of the block
before them. -/
def checkStats (c : Ctx) (seen : List String) (ss : Stats) : Except Err Unit :=
  match ss with
  | .last t => checkTm c .other t
  | .val p x T e r => do
    checkName c.prel p x
    if mem x seen then throw ⟨p, quote x ++ " is already defined in this block (scalac E161)"⟩
    let c' := { c with env := .defining x T.isSome :: (statsNames r).map .later ++ c.env }
    checkTyOpt c' T
    checkTm c' (underOf T) e
    checkStats { c with env := .val x :: c.env } (x :: seen) r
termination_by structural ss
/-- Refuse the members of a literal, whose template is the innermost of `c`.
`E` holds the edges of its cycle check, all plain, `D` the direct ones among
them, `seen` the names defined before, and `self` its self name. -/
def checkDefs (c : Ctx) (E D : List (String × List String)) (seen : List String)
    (self : Option String) (ds : Defs) : Except Err Unit :=
  match ds with
  | .nil => .ok ()
  | .typ p A T r => do
    checkMember c.prel p A true
    if mem A seen then throw (dupLit p false A)
    if decide (self = some A) then throw (dupLit p true A)
    if onCycle E E A then throw (cyclic E D p "alias" A)
    checkTy c T
    checkDefs c E D (A :: seen) self r
  | .val p a T e r => do
    checkMember c.prel p a false
    if mem a seen then throw (dupLit p false a)
    if decide (self = some a) then throw (dupLit p true a)
    checkTyOpt c T
    checkTm c (underOf T) e
    checkDefs c E D (a :: seen) self r
  | .cap p C cs r => do
    checkMember c.prel p C true
    if mem C seen then throw (dupLit p false C)
    if decide (self = some C) then throw (dupLit p true C)
    checkCaps c cs
    checkDefs c E D (C :: seen) self r
termination_by structural ds
end

/-! ## The prelude and the platform -/

/-- The name and the position of a prelude line. -/
def itemName : PreludeItem → Pos × String
  | .capClass p C | .classifier p C _ | .platClass p C _ => (p, C)

/-- The classifier trait of a prelude line, if it declares one. -/
def itemClassifier : PreludeItem → Option String
  | .classifier _ K _ => some K
  | _ => Option.none

/-- Refuse two prelude lines of one name (scalac E161), and a classifier
that the prelude does not declare as the parent of a classifier trait or of a
platform class.  `seen` holds the names before. -/
def checkPrelude (cls seen : List String) : List PreludeItem → Except Err Unit
  | [] => .ok ()
  | i :: is => do
    let (p, x) := itemName i
    if mem x seen then throw ⟨p, quote x ++ " is already defined in the prelude (scalac E161)"⟩
    match i with
    | .classifier _ _ (some k) | .platClass _ _ k =>
      if !mem k cls then
        throw ⟨p, quote k ++ " is not in scope: the prelude declares no classifier " ++ quote k⟩
    | _ => pure ()
    checkPrelude cls (x :: seen) is

/-- Refuse a platform parameter whose name breaks a rule of the subset, a
second parameter of one name (scalac E161), or a class that the prelude does
not declare (scalac E006).  `seen` holds the names before. -/
def checkParams (prel seen : List String) : List (Pos × String × String) → Except Err Unit
  | [] => .ok ()
  | (p, x, C) :: ps => do
    checkName prel p x
    if mem x seen then
      throw ⟨p, quote x ++ " is already defined as a parameter of `program` (scalac E161)"⟩
    if !mem C prel then
      throw ⟨p, quote C ++ " is not in scope: the prelude declares no class " ++ quote C ++
        " (scalac E006)"⟩
    checkParams prel (x :: seen) ps

/-! ## The label table -/

mutual
/-- The member names of a type, with repetitions, in the order of the text. -/
def tyLabels (T : Ty) : List String :=
  match T with
  | .any _ | .nothing _ => []
  | .sel _ _ A => [A]
  | .refine _ ds => declsLabels ds
  | .and S U | .fn _ _ S _ U => tyLabels S ++ tyLabels U
  | .capt _ S _ => tyLabels S
termination_by structural T
/-- The member names of an optional type. -/
def tyLabelsOpt (T : Option Ty) : List String :=
  match T with
  | some U => tyLabels U
  | Option.none => []
termination_by structural T
/-- The member names of the declarations of a refinement. -/
def declsLabels (ds : Decls) : List String :=
  match ds with
  | .nil => []
  | .typ _ A lo hi r => A :: (tyLabelsOpt lo ++ tyLabelsOpt hi ++ declsLabels r)
  | .alias _ A T r | .val _ A T r => A :: (tyLabels T ++ declsLabels r)
  | .cap _ C _ _ r | .capAlias _ C _ r => C :: declsLabels r
termination_by structural ds
end

mutual
/-- The member names of a term, with repetitions, in the order of the text. -/
def tmLabels (t : Tm) : List String :=
  match t with
  | .var .. | .this _ => []
  | .sel s _ a => tmLabels s ++ [a]
  | .app f e => tmLabels f ++ tmLabels e
  | .lam _ _ T b => tyLabelsOpt T ++ tmLabels b
  | .asc _ e T => tmLabels e ++ tyLabels T
  | .block _ ss => statsLabels ss
  | .lit _ _ ds => defsLabels ds
termination_by structural t
/-- The member names of the statements of a block. -/
def statsLabels (ss : Stats) : List String :=
  match ss with
  | .last t => tmLabels t
  | .val _ _ T e r => tyLabelsOpt T ++ (tmLabels e ++ statsLabels r)
termination_by structural ss
/-- The member names of the members of a literal. -/
def defsLabels (ds : Defs) : List String :=
  match ds with
  | .nil => []
  | .typ _ A T r => A :: (tyLabels T ++ defsLabels r)
  | .val _ a T e r => a :: (tyLabelsOpt T ++ (tmLabels e ++ defsLabels r))
  | .cap _ C _ r => C :: defsLabels r
termination_by structural ds
end

/-- The names in their first occurrences, after the names `seen`, which are
kept in reverse. -/
def firstOccurrences (seen : List String) : List String → List String
  | [] => seen.reverse
  | x :: xs => if mem x seen then firstOccurrences seen xs else firstOccurrences (x :: seen) xs

end Scope

open Scope in
/-- The checks of plan IX on a parsed program (S-12, S-13, the syntactic
half of S-16): names in scope as Scala reads them, `this` where it names a
template, selections on `this` and on self names that the template declares,
dependent function types whose binder occurs, names that Scala reads as
something else, duplicate definitions, forward and recursive references in a
block, literals under no written type, cycles of type members other than an
upper F-bound, and the platform and prelude names where they belong.  The first refusal, at the
position of its node, or `()`. -/
def check (P : Program) : Except Err Unit := do
  let prel := P.prelude.map fun i => (itemName i).2
  let cls := P.prelude.filterMap itemClassifier
  checkPrelude cls [] P.prelude
  let ps := P.params.getD []
  checkParams prel [] ps
  let c : Ctx := { env := [], dep := false, plat := ps.map (·.2.1), prel, cls }
  checkTyOpt c P.ty
  checkTm c (underOf P.ty) P.body

open Scope in
/-- The label table of a program (plan S-8): every member name of every
refinement, literal and selection, in order of first appearance in the file,
with `true` for a type member (upper case, capture members included) and
`false` for a field. -/
def labels (P : Program) : List (String × Bool) :=
  (firstOccurrences [] (tyLabelsOpt P.ty ++ tmLabels P.body)).map fun x => (x, isUpperName x)

end ScalaSyntax
