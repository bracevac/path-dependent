import Coercions.ScalaSyntax.Parse
import Coercions.ScalaSyntax.Scope
import Coercions.ScalaSyntax.Print
import Coercions.Frontend.Pipeline
import Coercions.Frontend.Pretty

/-!
# Scala programs in the vanilla front end

The shared reader of `lean/Coercions/ScalaSyntax/` turns the characters of a
`.scala` file into a `ScalaSyntax.Program` and checks its names and scopes.
This module maps that tree to the surface syntax of the vanilla front end, an
`STm`, and runs the existing pipeline on it (plan IX, S-7).

The mapping follows the table of the plan's vanilla subset.  `Any` and
`Nothing` are `⊤` and `⊥`.  A refinement is a right-nested `∧` of its
declarations, under `μ` exactly when `this` occurs at its own level.  A
template without a self name binds the name `this`, so an inner template hides
the outer one as in Scala.  `S => T` is `∀(_ : S) T`.  A block `val x: T = e`
annotates `x`, so it reads as `let x = (e : T) in r`, and as `let x : T = e in x`
when the block returns `x` (S-11).  An object literal stands only under a
written type `T` and reads as `let ℓ = ν(s. ds) in (ℓ : T)` (S-12).  The name
`ℓ` is one Scala cannot write.

The translation refuses what the vanilla front end lacks: a header other than
the one import, a prelude, `def program`, `->`, `^` and capture members.  It
also refuses the cases `check` has already refused, so that it is total.  The
first refusal in the order of the text wins, at the position of its node.

The label table numbers the member names of the Scala tree in order of first
appearance, each within its sort (S-8).  `outcome` parses, checks, translates,
numbers and compiles at the default budget, and answers one of five kinds.
An outcome carries values, and its text is a separate function, so the kernel
decides a kind without building a string.

The member check of S-17 runs after compilation.  Each selection `x.A` in a
written type must name a member that the type of `x` declares, by the front
end's own lookup.  Otherwise the program is outside, with scalac's reason
(E008), at the first such selection in the text.

The printers run the translation backwards (S-27).  `toScala` writes a
surface term as a Scala program, the inverse of `ofScala` on its image, and
refuses any other term with the reason it has no Scala form.  `fillToScala`
writes the elaborated term of a compiled program, every slot written.
`roundTrip` prints a term, reads the text back and compares the two terms
after resolution.

Every function here is structural, and none calls `String.toList`.  So the
kernel runs `outcome` on the characters of a file, and `roundTrip` on a term.
-/

namespace Frontend.Scala

/-! ## Names -/

/-- The one import of a vanilla file, character by character. -/
def vanillaImport : List Char :=
  ['s', 'c', 'a', 'l', 'a', '.', 'r', 'e', 'f', 'l', 'e', 'c', 't', '.',
   'S', 'e', 'l', 'e', 'c', 't', 'a', 'b', 'l', 'e', '.',
   'r', 'e', 'f', 'l', 'e', 'c', 't', 'i', 'v', 'e', 'S', 'e', 'l', 'e', 'c', 't', 'a', 'b', 'l', 'e']

/-- The one import of a vanilla file, as the parser names it. -/
def vanillaImportName : String := String.ofList vanillaImport

/-- The name of the let-bound literal of S-12.  No Scala name has it. -/
def litName : String := "ℓ"

/-- The binder of a template without a self name.  No Scala name is `this`. -/
def selfName : String := "this"

/-- The binder of `S => T`. -/
def anonName : String := "_"

/-! ## The label table -/

/-- Number the names, each within its sort, in the order given.  `true` is a
type label. -/
def tableOf : Nat → Nat → List (String × Bool) → LabelTable
  | _, _, [] => []
  | i, j, (x, true) :: xs => (x, .typ i) :: tableOf (i + 1) j xs
  | i, j, (x, false) :: xs => (x, .trm j) :: tableOf i (j + 1) xs

/-- The label table of a program: its member names in order of first
appearance in the text, as `ScalaSyntax.labels` lists them. -/
def table (P : ScalaSyntax.Program) : LabelTable := tableOf 0 0 (ScalaSyntax.labels P)

/-! ## Refusals -/

/-- The refusal of a header other than the one import. -/
def msgHeader : String :=
  "the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`"

/-- The refusal of a prelude line. -/
def msgPrelude : String := "a prelude is outside the vanilla subset"

/-- The refusal of `def program`. -/
def msgDefProgram : String := "`def program` is outside the vanilla subset: write `val program`"

/-- The refusal of `->`. -/
def msgThinArrow : String := "`->` is capture syntax, outside the vanilla subset: write `=>`"

/-- The refusal of `^`. -/
def msgHat : String := "`^` is capture syntax, outside the vanilla subset"

/-- The refusal of the capture member `C^`. -/
def msgCapMember (C : String) : String :=
  "the capture member `" ++ C ++ "^` is outside the vanilla subset"

/-- A literal under no written type.  `check` refuses it first. -/
def msgLitNoType : String := "an object literal needs a written type: scalac types it as Object"

/-- `this` outside every template.  `check` refuses it first. -/
def msgThisOutside : String :=
  "`this` outside every refinement and object literal names the wrapper object in Scala"

/-- An empty refinement.  The parser refuses it first. -/
def msgEmptyRefinement : String := "an empty refinement is outside the subset"

/-- An empty literal.  The parser refuses it first. -/
def msgEmptyLiteral : String := "an empty object literal is outside the subset"

/-! ## Helpers -/

/-- Whether a term is an object literal. -/
def isLit : ScalaSyntax.Tm → Bool
  | .lit .. => true
  | _ => false

/-- Whether the declarations end here. -/
def declsEnd : ScalaSyntax.Decls → Bool
  | .nil => true
  | _ => false

/-- Whether the members end here. -/
def defsEnd : ScalaSyntax.Defs → Bool
  | .nil => true
  | _ => false

/-- Whether the rest of a block is exactly the variable `x`. -/
def returns (x : String) : ScalaSyntax.Stats → Bool
  | .last (.var _ y) => decide (y = x)
  | _ => false

mutual
/-- Whether `this` occurs in a type at the level of the template it stands in.
A nested refinement is a template of its own and is not entered. -/
def usesThis (T : ScalaSyntax.Ty) : Bool :=
  match T with
  | .sel _ (.this _) _ => true
  | .sel _ (.var ..) _ | .any _ | .nothing _ | .refine .. => false
  | .and S U | .fn _ _ S _ U => usesThis S || usesThis U
  | .capt _ S _ => usesThis S
termination_by structural T
/-- Whether `this` occurs in an optional type at its template's level. -/
def usesThisOpt (T : Option ScalaSyntax.Ty) : Bool :=
  match T with
  | none => false
  | some U => usesThis U
/-- Whether `this` occurs in the declarations of a refinement at its level. -/
def usesThisDecls (ds : ScalaSyntax.Decls) : Bool :=
  match ds with
  | .nil => false
  | .typ _ _ lo hi r => usesThisOpt lo || usesThisOpt hi || usesThisDecls r
  | .alias _ _ T r | .val _ _ T r => usesThis T || usesThisDecls r
  | .cap _ _ _ _ r | .capAlias _ _ _ r => usesThisDecls r
termination_by structural ds
end

/-! ## Types

`self` is the binder of the innermost template, `none` outside every
template.  A refinement binds `this`. -/

mutual
/-- A Scala type as a surface type. -/
def ofTy (self : Option String) (T : ScalaSyntax.Ty) : Except ScalaSyntax.Err SType :=
  match T with
  | .any _ => pure .top
  | .nothing _ => pure .bot
  | .sel _ (.var _ x) A => pure (.sel x A)
  | .sel _ (.this p) A =>
    match self with
    | some b => pure (.sel b A)
    | none => throw ⟨p, msgThisOutside⟩
  | .refine p ds => do
    let body ← ofDecls (some selfName) p ds
    pure (if usesThisDecls ds then .mu selfName body else body)
  | .and S U => do
    let S' ← ofTy self S
    let U' ← ofTy self U
    pure (.and S' U')
  | .fn p x S a U => do
    let S' ← ofTy self S
    match a with
    | .thin _ => throw ⟨p, msgThinArrow⟩
    | .fat => pure ()
    let U' ← ofTy self U
    pure (.all (x.getD anonName) S' U')
  | .capt p S _ => do
    let _ ← ofTy self S
    throw ⟨p, msgHat⟩
termination_by structural T
/-- An optional bound, `dflt` when it is missing. -/
def ofTyOpt (self : Option String) (dflt : SType) (T : Option ScalaSyntax.Ty) :
    Except ScalaSyntax.Err SType :=
  match T with
  | none => pure dflt
  | some U => ofTy self U
termination_by structural T
/-- The declarations of a refinement at `p`, joined by a right-nested `∧`. -/
def ofDecls (self : Option String) (p : ScalaSyntax.Pos) (ds : ScalaSyntax.Decls) :
    Except ScalaSyntax.Err SType :=
  match ds with
  | .nil => throw ⟨p, msgEmptyRefinement⟩
  | .typ _ A lo hi r => do
    let S ← ofTyOpt self .bot lo
    let U ← ofTyOpt self .top hi
    if declsEnd r then pure (.typ A S U) else
      let rest ← ofDecls self p r
      pure (.and (.typ A S U) rest)
  | .alias _ A T r => do
    let T' ← ofTy self T
    if declsEnd r then pure (.typ A T' T') else
      let rest ← ofDecls self p r
      pure (.and (.typ A T' T') rest)
  | .val _ a T r => do
    let T' ← ofTy self T
    if declsEnd r then pure (.fld a T') else
      let rest ← ofDecls self p r
      pure (.and (.fld a T') rest)
  | .cap q C _ _ _ | .capAlias q C _ _ => throw ⟨q, msgCapMember C⟩
termination_by structural ds
end

/-- An optional type, as the optional slot of a lambda. -/
def ofTySlot (self : Option String) : Option ScalaSyntax.Ty → Except ScalaSyntax.Err (Option SType)
  | none => pure none
  | some T => some <$> ofTy self T

/-! ## Terms

`under` is the written type a term stands under, set only where a literal may
stand (D-4 of the groups file): the term of an ascription, the right side of a
typed `val`, of a typed literal member and of the typed program.  Every other
node passes `none` to its parts. -/

mutual
/-- A Scala term as a surface term. -/
def ofTm (self : Option String) (under : Option ScalaSyntax.Ty) (t : ScalaSyntax.Tm) :
    Except ScalaSyntax.Err STm :=
  match t with
  | .var _ x => pure (.var x)
  | .this p =>
    match self with
    | some b => pure (.var b)
    | none => throw ⟨p, msgThisOutside⟩
  | .sel s _ a => do
    let s' ← ofTm self none s
    pure (.proj s' a)
  | .app f u => do
    let f' ← ofTm self none f
    let u' ← ofTm self none u
    pure (.app f' u')
  | .lam _ x T b => do
    let T' ← ofTySlot self T
    let b' ← ofTm self none b
    pure (.lam x T' b')
  | .asc _ e T =>
    if isLit e then ofTm self (some T) e else do
      let e' ← ofTm self none e
      let T' ← ofTy self T
      pure (.asc e' T')
  | .block _ ss => ofStats self ss
  | .lit p s ds =>
    match under with
    | none => throw ⟨p, msgLitNoType⟩
    | some T => do
      let b := s.getD selfName
      let ds' ← ofDefs (some b) p ds
      let T' ← ofTy self T
      pure (.«let» litName none (.obj b none ds') (.asc (.var litName) T'))
termination_by structural t
/-- The statements of a block, as nested `let`s. -/
def ofStats (self : Option String) (ss : ScalaSyntax.Stats) : Except ScalaSyntax.Err STm :=
  match ss with
  | .last t => ofTm self none t
  | .val _ x none e r => do
    let e' ← ofTm self none e
    let r' ← ofStats self r
    pure (.«let» x none e' r')
  | .val _ x (some T) e r => do
    let T' ← ofTy self T
    if returns x r then
      let e' ← ofTm self (some T) e
      pure (.«let» x (some T') e' (.var x))
    else
      let e' ← if isLit e then ofTm self (some T) e else do
        let e₀ ← ofTm self none e
        pure (.asc e₀ T')
      let r' ← ofStats self r
      pure (.«let» x none e' r')
termination_by structural ss
/-- The members of a literal at `p`, joined by a right-nested `∧`. -/
def ofDefs (self : Option String) (p : ScalaSyntax.Pos) (ds : ScalaSyntax.Defs) :
    Except ScalaSyntax.Err SDefs :=
  match ds with
  | .nil => throw ⟨p, msgEmptyLiteral⟩
  | .typ _ A T r => do
    let T' ← ofTy self T
    if defsEnd r then pure (.typ A T') else
      let rest ← ofDefs self p r
      pure (.and (.typ A T') rest)
  | .val _ a T e r => do
    let T' ← ofTySlot self T
    let e' ← ofTm self T e
    if defsEnd r then pure (.trm a T' e') else
      let rest ← ofDefs self p r
      pure (.and (.trm a T' e') rest)
  | .cap q C _ _ => throw ⟨q, msgCapMember C⟩
termination_by structural ds
end

/-! ## Programs -/

/-- Refuse a header other than the one import: at the first import that is
not the vanilla one, at a second import, or at `1:1` when there is none. -/
def ofImports : List (ScalaSyntax.Pos × String) → Except ScalaSyntax.Err Unit
  | [] => throw ⟨⟨1, 1⟩, msgHeader⟩
  | (p, i) :: rest =>
    if decide (i = vanillaImportName) then
      match rest with
      | [] => pure ()
      | (q, _) :: _ => throw ⟨q, msgHeader⟩
    else throw ⟨p, msgHeader⟩

/-- A program as a surface term: the header, the prelude and `def program`
refused, then the right side, ascribed when the program has a written type.
It does not call `check`. -/
def ofScala (P : ScalaSyntax.Program) : Except ScalaSyntax.Err STm := do
  ofImports P.imports
  match P.prelude with
  | [] => pure ()
  | i :: _ => throw ⟨(ScalaSyntax.Scope.itemName i).1, msgPrelude⟩
  match P.params with
  | none => pure ()
  | some [] => throw ⟨⟨1, 1⟩, msgDefProgram⟩
  | some ((q, _) :: _) => throw ⟨q, msgDefProgram⟩
  match P.ty with
  | none => ofTm none none P.body
  | some T => do
    let T' ← ofTy none T
    if isLit P.body then ofTm none (some T) P.body else
      let e ← ofTm none none P.body
      pure (.asc e T')

/-- Parse, check and translate the characters of a file, and number its
labels. -/
def readProgram (cs : List Char) :
    Except ScalaSyntax.Err (ScalaSyntax.Program × STm × LabelTable) := do
  let P ← ScalaSyntax.parseFile cs
  ScalaSyntax.check P
  let e ← ofScala P
  pure (P, e, table P)

/-- The surface term and the label table of the characters of a file (S-2). -/
def readVanilla (cs : List Char) : Except ScalaSyntax.Err (STm × LabelTable) :=
  (readProgram cs).map fun (_, e, Λ) => (e, Λ)

/-! ## The member check (S-17)

scalac refuses a selection `x.A` in a written type when the type of `x` has no
member `A` (E008).  The front end does not check written types for that, so
it may type such a program.  The check walks the partial term of `resolveP`
and the elaborated term of `compileE` together.  The written types are the
filled slots of the partial term: lambda domains, `let` types (an ascription
is a `let` at its type), self types, field types and the right sides of type
members.  Each is checked in the context the elaborated term gives it.  A
lambda binds its domain, a literal its self type under `μ`, and a `let` the
type of its elaborated right side.  Inferred slots are not checked.

A selection is declared when `Core.decls` finds the member on a fresh tank.
So the walk does not draw on one tank, and every lookup has the full fuel.
The first answer other than `ok`, in the order of the walk, wins. -/

/-- The answer of the member check. -/
inductive MemberCheck where
  /-- Every selection names a declared member. -/
  | ok
  /-- A selection names the member `A`, and the type of its variable lacks it. -/
  | undeclared (A : FCdot.Label)
  /-- The right side of a `let` has no type, so its body has no context. -/
  | unknown
  /-- A lookup ended with the tank marked. -/
  | limit
deriving DecidableEq, Repr

/-- The first answer other than `ok`. -/
def MemberCheck.andThen : MemberCheck → MemberCheck → MemberCheck
  | .ok, m => m
  | m, _ => m

/-- Whether the type of `x` declares the type member `A`, by the lookup of the
front end on a fresh tank. -/
def declaredIn {s : FCdot.Sig} (Γ : DotMNF.Ctx s) (x : FCdot.BVar s .var) (A : FCdot.Label) :
    MemberCheck :=
  let r := Core.decls Γ Core.defaultFuel x A ⟨Core.defaultFuel, false⟩
  if r.2.out then .limit else if r.1.isEmpty then .undeclared A else .ok

/-- Every selection in `T` names a declared member.  A `μ` binds its body's
variable, and `∀(x : S) U` binds `x` at `S` in `U`. -/
def memberTy {s : FCdot.Sig} (Γ : DotMNF.Ctx s) (T : DotMNF.Ty s) : MemberCheck :=
  match T with
  | .top | .bot => .ok
  | .typ _ S U => (memberTy Γ S).andThen (memberTy Γ U)
  | .fld _ U => memberTy Γ U
  | .sel (.var x) A => declaredIn Γ x A
  | .mu U => memberTy (Γ.cons (.mu U)) U
  | .all S U => (memberTy Γ S).andThen (memberTy (Γ.cons S) U)
  | .and S U => (memberTy Γ S).andThen (memberTy Γ U)
termination_by structural T

/-- A written slot, `ok` when it is empty. -/
def memberOpt {s : FCdot.Sig} (Γ : DotMNF.Ctx s) : Option (DotMNF.Ty s) → MemberCheck
  | none => .ok
  | some T => memberTy Γ T

mutual
/-- The written types of the partial term `p`, each in the context that the
elaborated term `a` gives it. -/
def memberTm {s : FCdot.Sig} (Γ : DotMNF.Ctx s) (p : PTm s) (a : ATm s) : MemberCheck :=
  match p, a with
  | .lam o t, .lam S t' => (memberOpt Γ o).andThen (memberTm (Γ.cons S) t t')
  | .obj o d, .obj T d' =>
    let Γ' := Γ.cons (.mu T)
    (memberOpt Γ' o).andThen (memberDefs Γ' d d')
  | .«let» _ o t u, .«let» _ t' u' =>
    (memberOpt Γ o).andThen ((memberTm Γ t t').andThen
      (match synthIn? {} Γ t' with
       | some c => memberTm (Γ.cons c.ty) u u'
       | none => .unknown))
  | _, _ => .ok
termination_by structural p
/-- The written types of the members `d` of a literal, in the literal's context. -/
def memberDefs {s : FCdot.Sig} (Γ : DotMNF.Ctx s) (d : PDefs s) (e : ADefs s) : MemberCheck :=
  match d, e with
  | .typ _ T, .typ _ _ => memberTy Γ T
  | .trm _ o t, .trm _ t' => (memberOpt Γ o).andThen (memberTm Γ t t')
  | .and d₁ d₂, .and e₁ e₂ => (memberDefs Γ d₁ e₁).andThen (memberDefs Γ d₂ e₂)
  | _, _ => .ok
termination_by structural d
end

/-- The member check of a program `e` that compiled to `a` with the table `Λ`.
It is `ok` when `e` does not resolve, which `compileE` has already refused. -/
def members (Λ : LabelTable) (e : STm) (a : ATm []) : MemberCheck :=
  match resolveP Λ e with
  | some p => memberTm .nil p a
  | none => .ok

/-! ### Where the refusal sits

The walk knows the label and a de Bruijn variable, not the text.  So the
refusal sits at the first selection `x.A` on a variable, in a written type, in
the order of the text, whose member name is the label's name (D-8 of the
groups file).  Two selections of one name on different variables can put it
at the wrong one. -/

mutual
/-- The first selection of the member `A` on a variable in a type, at the
member's name, with the variable. -/
def firstSelTy (A : String) (T : ScalaSyntax.Ty) : Option (ScalaSyntax.Pos × String) :=
  match T with
  | .sel p (.var _ x) A' => if decide (A' = A) then some (p, x) else none
  | .sel _ (.this _) _ | .any _ | .nothing _ => none
  | .refine _ ds => firstSelDecls A ds
  | .and S U | .fn _ _ S _ U => (firstSelTy A S).or (firstSelTy A U)
  | .capt _ S _ => firstSelTy A S
termination_by structural T
/-- The same in an optional type. -/
def firstSelTyOpt (A : String) (T : Option ScalaSyntax.Ty) : Option (ScalaSyntax.Pos × String) :=
  match T with
  | none => none
  | some U => firstSelTy A U
termination_by structural T
/-- The same in the declarations of a refinement, the lower bound first. -/
def firstSelDecls (A : String) (ds : ScalaSyntax.Decls) : Option (ScalaSyntax.Pos × String) :=
  match ds with
  | .nil => none
  | .typ _ _ lo hi r => (firstSelTyOpt A lo).or ((firstSelTyOpt A hi).or (firstSelDecls A r))
  | .alias _ _ T r | .val _ _ T r => (firstSelTy A T).or (firstSelDecls A r)
  | .cap _ _ _ _ r | .capAlias _ _ _ r => firstSelDecls A r
termination_by structural ds
end

mutual
/-- The first selection of the member `A` on a variable in the written types of
a term, in the order of the text. -/
def firstSelTm (A : String) (t : ScalaSyntax.Tm) : Option (ScalaSyntax.Pos × String) :=
  match t with
  | .var .. | .this _ => none
  | .sel s _ _ => firstSelTm A s
  | .app f u => (firstSelTm A f).or (firstSelTm A u)
  | .lam _ _ T b => (firstSelTyOpt A T).or (firstSelTm A b)
  | .asc _ e T => (firstSelTm A e).or (firstSelTy A T)
  | .block _ ss => firstSelStats A ss
  | .lit _ _ ds => firstSelDefs A ds
termination_by structural t
/-- The same in a block: a `val`'s type, its right side, then the rest. -/
def firstSelStats (A : String) (ss : ScalaSyntax.Stats) : Option (ScalaSyntax.Pos × String) :=
  match ss with
  | .last t => firstSelTm A t
  | .val _ _ T e r => (firstSelTyOpt A T).or ((firstSelTm A e).or (firstSelStats A r))
termination_by structural ss
/-- The same in the members of a literal, each in order. -/
def firstSelDefs (A : String) (ds : ScalaSyntax.Defs) : Option (ScalaSyntax.Pos × String) :=
  match ds with
  | .nil => none
  | .typ _ _ T r => (firstSelTy A T).or (firstSelDefs A r)
  | .val _ _ T e r => (firstSelTyOpt A T).or ((firstSelTm A e).or (firstSelDefs A r))
  | .cap _ _ _ r => firstSelDefs A r
termination_by structural ds
end

/-- The first selection of the member `A` on a variable in a program: its
written type, then its right side. -/
def firstSel (A : String) (P : ScalaSyntax.Program) : Option (ScalaSyntax.Pos × String) :=
  (firstSelTyOpt A P.ty).or (firstSelTm A P.body)

/-- The refusal of an undeclared member `A`, naming the variable when the
selection is found. -/
def msgUndeclared (A : String) : Option String → String
  | some x => "type " ++ A ++ " is not a member of the type of " ++ x ++ " (scalac E008)"
  | none => "type " ++ A ++ " is not a member (scalac E008)"

/-- The refusal of an undeclared member `A` of the program `P`: at its first
selection, or at `1:1` when there is none. -/
def undeclaredErr (P : ScalaSyntax.Program) (A : String) : ScalaSyntax.Err :=
  match firstSel A P with
  | some (p, x) => ⟨p, msgUndeclared A (some x)⟩
  | none => ⟨⟨1, 1⟩, msgUndeclared A none⟩

/-! ## Outcomes -/

/-- The five kinds of an outcome (S-7). -/
inductive Kind where
  /-- The front end types the program. -/
  | ok
  /-- The front end rejects the program, by a reason of its rules. -/
  | rejected
  /-- The front end cannot tell. -/
  | unknown
  /-- The tank ended marked, the compiler's recursion limit. -/
  | limit
  /-- The program is outside the subset. -/
  | outside
deriving DecidableEq, Repr

/-- What the front end makes of a file.  `ok` carries the fill and its type,
`rejected` the reason (never the recursion limit), `unknown` a sentence, and
`outside` the refusal of the reader or the translation. -/
inductive Outcome where
  /-- The fill and its type. -/
  | ok (table : LabelTable) (a : ATm []) (ty : DotMNF.Ty [])
  /-- The reason of the rejection. -/
  | rejected (table : LabelTable) (r : EReason)
  /-- Why the front end cannot tell. -/
  | unknown (table : LabelTable) (why : String)
  /-- The recursion limit. -/
  | limit (table : LabelTable)
  /-- The refusal, with its position. -/
  | outside (err : ScalaSyntax.Err)
deriving DecidableEq

/-- The kind of an outcome. -/
def Outcome.kind : Outcome → Kind
  | .ok .. => .ok
  | .rejected .. => .rejected
  | .unknown .. => .unknown
  | .limit _ => .limit
  | .outside _ => .outside

/-- An outcome as text, with labels by name. -/
def Outcome.text : Outcome → String
  | .ok Λ _ T => "ok : " ++ ppTyWith Λ .nil T
  | .rejected Λ r => "rejected: " ++ ppReasonWith Λ r
  | .unknown _ why => "unknown: " ++ why
  | .limit _ => "limit: Recursion limit exceeded"
  | .outside e => "outside " ++ toString e.pos.line ++ ":" ++ toString e.pos.col ++ ": " ++ e.msg

/-- The outcome of the characters of a file: read, compile at the default
budget, then check the members of the written types (S-17). -/
def outcome (cs : List Char) : Outcome :=
  match readProgram cs with
  | .error err => .outside err
  | .ok (P, e, Λ) =>
    match compileE {} Λ e with
    | .error .limit => .limit Λ
    | .error r => .rejected Λ r
    | .ok ⟨a, c⟩ =>
      match members Λ e a with
      | .ok => .ok Λ a c.ty
      | .undeclared A => .outside (undeclaredErr P ((labelName? Λ A).getD (defaultLabelName A)))
      | .unknown => .unknown Λ "the member check of plan S-17 found no type for a right side"
      | .limit => .limit Λ

/-! ## The printers (S-27)

`toScala` writes a surface term as a Scala program.  On the image of
`ofScala` it is the inverse: the text it prints reads back to a term that
resolves as the original does.  A term outside that image is refused with the
reason it has no Scala form (the plan's Gaps list).  `fillToScala` writes the
elaborated term of a compiled program, with every slot written, and relaxes
three of the reasons.

The printer builds the tree of the shared reader, then runs `check` on it,
since `print` reads back only trees in the parser's image.  A refusal of
`check` comes back as `reader: ` and its message.  Names are used as written,
so `check` refuses a name the subset does not have. -/

/-! ### Why a term has no Scala form -/

/-- A literal with a written self type. -/
def gapSelfType : String :=
  "a written self type has no Scala form: scalac never writes one (plan S-12)"

/-- A literal outside the literal form. -/
def gapUntypedLiteral : String :=
  "an object literal needs a written type: scalac types it as Object (plan S-12)"

/-- A `μ` whose body is not a chain of declarations with distinct names. -/
def gapMuBody : String :=
  "a μ whose body is not one refinement has no Scala form (plan S-15)"

/-- A `μ` or a literal named from inside an inner template. -/
def gapMuOuter : String :=
  "a μ or a literal named from inside an inner template has no Scala form: the inner `this` hides it (plan S-13)"

/-- A `μ` whose binder does not occur. -/
def gapMuUnused : String :=
  "a μ whose binder does not occur has no Scala form: it would print as its body (plan S-15)"

/-- A typed `let` whose body is not its binder. -/
def gapLetType : String :=
  "`let x : U = t in u` with `u` not `x` has no Scala form: it would print as `({ val x = t; u }: U)` (plan S-11)"

/-- `this` inside a dependent function type. -/
def gapThisDep : String :=
  "`this` inside a dependent function type has no Scala form (plan S-13)"

/-- Definitions joined by a left-nested `∧`. -/
def gapDefsLeft : String :=
  "definitions joined by a left-nested ∧ have no Scala form: a literal lists its members"

/-- A literal ascribed directly, outside the literal form. -/
def gapAscLiteral : String :=
  "a literal ascribed directly reads back as `let ℓ = ν(s. d) in (ℓ : T)` (plan S-12)"

/-- The nine reasons. -/
def gapReasons : List String :=
  [gapSelfType, gapUntypedLiteral, gapMuBody, gapMuOuter, gapMuUnused, gapLetType, gapThisDep,
   gapDefsLeft, gapAscLiteral]

/-! ### Free names -/

/-- The list without the name `x`. -/
def dropName (x : String) (l : List String) : List String := l.filter fun y => !decide (y = x)

/-- The free names of a type.  A binder removes its own name from its scope. -/
def fvTy : SType → List String
  | .top | .bot => []
  | .typ _ S U => fvTy S ++ fvTy U
  | .fld _ U => fvTy U
  | .sel x _ => [x]
  | .mu x U => dropName x (fvTy U)
  | .all x S U => fvTy S ++ dropName x (fvTy U)
  | .and S U => fvTy S ++ fvTy U

/-- The free names of an optional type. -/
def fvTyOpt : Option SType → List String
  | none => []
  | some T => fvTy T

mutual
/-- The free names of a term.  The self binder of a literal scopes over its
self type, and the binder of a `let` does not scope over its type. -/
def fvTm (e : STm) : List String :=
  match e with
  | .var x => [x]
  | .lam x T t => fvTyOpt T ++ dropName x (fvTm t)
  | .obj x T d => dropName x (fvTyOpt T ++ fvDefs d)
  | .app t u => fvTm t ++ fvTm u
  | .proj t _ => fvTm t
  | .«let» x T t u => fvTyOpt T ++ fvTm t ++ dropName x (fvTm u)
  | .asc t T => fvTm t ++ fvTy T
termination_by structural e
/-- The free names of the members of a literal. -/
def fvDefs (d : SDefs) : List String :=
  match d with
  | .typ _ T => fvTy T
  | .trm _ T t => fvTyOpt T ++ fvTm t
  | .and d e => fvDefs d ++ fvDefs e
termination_by structural d
end

/-! ### The context of the printer

In Scala every refinement and every literal is a template, and `this` names
the innermost one.  `thisName` is the binder that prints as `this`.  `hidden`
holds the binders that an inner template hides, so they cannot be printed.
`dep` holds inside a dependent function type, where `this` is refused.
`body` holds in the body of the `μ` being printed, whose declarations are
that `μ`'s refinement.  `fill` relaxes three reasons. -/

/-- The context of the printer (D-11 of the groups file). -/
structure PCtx where
  /-- The binder that prints as `this`. -/
  thisName : Option String
  /-- The binders that an inner template hides. -/
  hidden : List String
  /-- Inside a dependent function type. -/
  dep : Bool
  /-- In the body of the `μ` being printed. -/
  body : Bool
  /-- Printing a fill. -/
  fill : Bool

/-- A binder of `y`: below it, `y` is neither `this` nor hidden. -/
def PCtx.bind (c : PCtx) (y : String) : PCtx :=
  { c with
    thisName := match c.thisName with
      | some t => if decide (t = y) then none else some t
      | none => none
    hidden := dropName y c.hidden }

/-- Open a template whose `this` is `t`: the binder that printed as `this`
before is hidden from now on. -/
def PCtx.enter (c : PCtx) (t : Option String) (body : Bool) : PCtx :=
  { c with
    thisName := t
    hidden := match c.thisName with
      | some s => s :: c.hidden
      | none => c.hidden
    body }

/-- The context of the parts of a declaration.  In the body of the `μ` being
printed the declaration belongs to that `μ`'s refinement.  Elsewhere it is a
refinement of its own, a template without a self name. -/
def PCtx.member (c : PCtx) : PCtx :=
  if c.body then { c with body := false } else c.enter none false

/-- The context of the members of a literal bound to `x`.  A literal bound to
`this` prints without a self name, and `this` names it.  Any other binder
prints as the self name `x =>`. -/
def PCtx.lit (c : PCtx) (x : String) : PCtx :=
  (c.bind x).enter (if decide (x = selfName) then some selfName else none) false

/-! ### Types -/

/-- The declarations `ds`, then `es`. -/
def appendDecls (ds es : ScalaSyntax.Decls) : ScalaSyntax.Decls :=
  match ds with
  | .nil => es
  | .typ p A lo hi r => .typ p A lo hi (appendDecls r es)
  | .alias p A T r => .alias p A T (appendDecls r es)
  | .val p a T r => .val p a T (appendDecls r es)
  | .cap p C lo hi r => .cap p C lo hi (appendDecls r es)
  | .capAlias p C cs r => .capAlias p C cs (appendDecls r es)
termination_by structural ds

/-- A surface type as a Scala type and, when the type is a chain of
declarations with distinct names, that chain with its names (D-11).  The chain
prints as one refinement.  A `μ` is never a chain. -/
def tyToScala (c : PCtx) (T : SType) :
    Except String (ScalaSyntax.Ty × Option (ScalaSyntax.Decls × List String)) :=
  match T with
  | .top => pure (.any .zero, none)
  | .bot => pure (.nothing .zero, none)
  | .typ A S U => do
    let (S', _) ← tyToScala c.member S
    let (U', _) ← tyToScala c.member U
    let d : ScalaSyntax.Decls :=
      if decide (S = U) then .alias .zero A S' .nil
      else .typ .zero A (if decide (S = .bot) then none else some S')
        (if decide (U = .top) then none else some U') .nil
    pure (.refine .zero d, some (d, [A]))
  | .fld a U => do
    let (U', _) ← tyToScala c.member U
    let d : ScalaSyntax.Decls := .val .zero a U' .nil
    pure (.refine .zero d, some (d, [a]))
  | .sel y A =>
    if decide (c.thisName = some y) then
      if c.dep then throw gapThisDep else pure (.sel .zero (.this .zero) A, none)
    else if ScalaSyntax.Scope.mem y c.hidden then throw gapMuOuter
    else pure (.sel .zero (.var .zero y) A, none)
  | .mu x U => do
    let (U', ch) ← tyToScala ((c.bind x).enter (some x) true) U
    match ch with
    | none => throw gapMuBody
    | some _ =>
      if ScalaSyntax.Scope.mem x (fvTy U) || c.fill then pure (U', none) else throw gapMuUnused
  | .all x S U => do
    let used := ScalaSyntax.Scope.mem x (fvTy U)
    let c' := { c with dep := c.dep || used, body := false }
    let (S', _) ← tyToScala c' S
    let (U', _) ← tyToScala (c'.bind x) U
    pure (.fn .zero (if used then some x else none) S' .fat U', none)
  | .and S U => do
    let (S', cs) ← tyToScala c S
    let (U', cu) ← tyToScala c U
    match cs, cu with
    | some (d, [A]), some (ds, ns) =>
      if ScalaSyntax.Scope.mem A ns then pure (.and S' U', none)
      else
        let ds' := appendDecls d ds
        pure (.refine .zero ds', some (ds', A :: ns))
    | _, _ => pure (.and S' U', none)
termination_by structural T

/-- An optional type, as the optional type of a lambda. -/
def tyOptToScala (c : PCtx) : Option SType → Except String (Option ScalaSyntax.Ty)
  | none => pure none
  | some T => do
    let (T', _) ← tyToScala c T
    pure (some T')

/-! ### Terms

A `let` prints as a block.  `tmToScala c block e` returns the statements of
`e`, and `block` holds the names that a later `val` of the current block may
not take: the names of the `val`s so far and the free names of their right
sides and written types (D-10).  `check` refuses such a `val`, so it starts a
nested block instead.  A term is read off statements by `toTm`. -/

/-- A term from statements: the result alone, or a block. -/
def toTm : ScalaSyntax.Stats → ScalaSyntax.Tm
  | .last t => t
  | ss => .block .zero ss

/-- An ascription taken apart into its type and its term. -/
def splitAsc : ScalaSyntax.Tm → Option ScalaSyntax.Ty × ScalaSyntax.Tm
  | .asc _ t T => (some T, t)
  | t => (none, t)

/-- The written type of the literal form `let y = ν(x. d) in (y : T)`, with `y`
not free in `T`, the reading of a literal under `T` (D-4). -/
def litFormType : STm → Option SType
  | .«let» y none (.obj _ none _) (.asc (.var w) T) =>
    if decide (w = y) && !ScalaSyntax.Scope.mem y (fvTy T) then some T else none
  | _ => none

/-- Whether a term is an object literal. -/
def isObj : STm → Bool
  | .obj .. => true
  | _ => false

/-- Whether a term is an ascription of a term that is not an object literal. -/
def isAscNonObj : STm → Bool
  | .asc t _ => !isObj t
  | _ => false

/-- Whether a term is the variable `x`. -/
def isVar (x : String) : STm → Bool
  | .var y => decide (y = x)
  | _ => false

/-- A literal with the members `ds`, bound to `x`. -/
def litOf (x : String) (ds : ScalaSyntax.Defs) : ScalaSyntax.Tm :=
  .lit .zero (if decide (x = selfName) then none else some x) ds

/-- The statement `val x: T = rhs` before the statements `r`, or, when `nested`
holds, in a block of its own that ends the current one. -/
def joinVal (nested : Bool) (x : String) (T : Option ScalaSyntax.Ty) (rhs : ScalaSyntax.Tm)
    (r : ScalaSyntax.Stats) : ScalaSyntax.Stats :=
  if nested then .last (.block .zero (.val .zero x T rhs r)) else .val .zero x T rhs r

/-- The members `ds`, then `es`. -/
def appendDefs (ds es : ScalaSyntax.Defs) : ScalaSyntax.Defs :=
  match ds with
  | .nil => es
  | .typ p A T r => .typ p A T (appendDefs r es)
  | .val p a T t r => .val p a T t (appendDefs r es)
  | .cap p C cs r => .cap p C cs (appendDefs r es)
termination_by structural ds

/-- Whether definitions are joined by `∧` at the top. -/
def isAndDefs : SDefs → Bool
  | .and .. => true
  | _ => false

mutual
/-- The statements of a surface term (D-10).  The cases, first match wins: the
literal form, a `val` with a written type before more, a typed `let` that
returns its binder, a typed `let` that does not, any other `let`, and any
other term as the result. -/
def tmToScala (c : PCtx) (block : List String) (e : STm) : Except String ScalaSyntax.Stats :=
  match e with
  | .var y =>
    if decide (c.thisName = some y) then pure (.last (.this .zero))
    else if ScalaSyntax.Scope.mem y c.hidden then throw gapMuOuter
    else pure (.last (.var .zero y))
  | .lam x T t => do
    let T' ← tyOptToScala c T
    let t' ← tmToScala (c.bind x) [] t
    pure (.last (.lam .zero x T' (toTm t')))
  | .obj x T d =>
    match T with
    | none => throw gapUntypedLiteral
    | some S =>
      if c.fill then do
        let ds ← defsToScala (c.lit x) d
        let (S', _) ← tyToScala c (.mu x S)
        pure (.last (.asc .zero (litOf x ds) S'))
      else throw gapSelfType
  | .app t u => do
    let t' ← tmToScala c [] t
    let u' ← tmToScala c [] u
    pure (.last (.app (toTm t') (toTm u')))
  | .proj t a => do
    let t' ← tmToScala c [] t
    pure (.last (.sel (toTm t') .zero a))
  | .asc t T =>
    if isObj t then throw gapAscLiteral
    else do
      let t' ← tmToScala c [] t
      let (T', _) ← tyToScala c T
      pure (.last (.asc .zero (toTm t') T'))
  | .«let» y none (.obj x none d) (.asc (.var w) T) =>
    -- the literal form, else a `val` whose right side is a literal outside it
    if decide (w = y) && !ScalaSyntax.Scope.mem y (fvTy T) then do
      let ds ← defsToScala (c.lit x) d
      let (T', _) ← tyToScala c T
      pure (.last (.asc .zero (litOf x ds) T'))
    else throw gapUntypedLiteral
  | .«let» x none t u => do
    -- `val x: T = …` when `t` is the literal form or an ascription and `u` is not `x`
    let t' ← tmToScala c [] t
    let typed := ((litFormType t).isSome || isAscNonObj t) && !isVar x u
    let (T', rhs) := if typed then splitAsc (toTm t') else (none, toTm t')
    let N := x :: fvTm t
    let nested := ScalaSyntax.Scope.mem x block
    let r ← tmToScala (c.bind x) (if nested then N else N ++ block) u
    pure (joinVal nested x T' rhs r)
  | .«let» x (some U) t u =>
    if !isVar x u && !c.fill then throw gapLetType
    else do
      let t' ← tmToScala c [] t
      let (U', _) ← tyToScala c U
      if isVar x u then
        -- `val x: U = …` then `x`, the literal bare when its written type is `U`
        let rhs := match litFormType t with
          | some T => if decide (T = U) then (splitAsc (toTm t')).2 else toTm t'
          | none => toTm t'
        let N := x :: (fvTm t ++ fvTy U)
        let nested := ScalaSyntax.Scope.mem x block
        let r ← tmToScala (c.bind x) (if nested then N else N ++ block) u
        pure (joinVal nested x (some U') rhs r)
      else do
        -- fill mode: `({ val x = t; u }: U)`
        let r ← tmToScala (c.bind x) (x :: fvTm t) u
        pure (.last (.asc .zero (.block .zero (.val .zero x none (toTm t') r)) U'))
termination_by structural e
/-- The members of a literal, in order.  A member with a written type `T` whose
right side is the literal form under `T` prints the literal bare (D-4 read
backwards). -/
def defsToScala (c : PCtx) (d : SDefs) : Except String ScalaSyntax.Defs :=
  match d with
  | .typ A T => do
    let (T', _) ← tyToScala c T
    pure (.typ .zero A T' .nil)
  | .trm a T t => do
    let T' ← tyOptToScala c T
    let t' ← tmToScala c [] t
    let rhs := match litFormType t, T with
      | some T₀, some U => if decide (T₀ = U) then (splitAsc (toTm t')).2 else toTm t'
      | _, _ => toTm t'
    pure (.val .zero a T' rhs .nil)
  | .and d₁ d₂ =>
    if isAndDefs d₁ then throw gapDefsLeft
    else do
      let r₁ ← defsToScala c d₁
      let r₂ ← defsToScala c d₂
      pure (appendDefs r₁ r₂)
termination_by structural d
end

/-! ### Programs -/

/-- Whether a term is an ascription. -/
def isAsc : STm → Bool
  | .asc .. => true
  | _ => false

/-- A surface term as a vanilla program named `Main`, checked by the reader.
The literal form under `T` gives `val program: T = new Object { … }`, an
ascription `(t : T)` gives `val program: T = t`, and any other term `val
program = t`.  With `fill`, three reasons are relaxed (D-12). -/
def toScalaWith (fill : Bool) (e : STm) : Except String ScalaSyntax.Program := do
  let c : PCtx := { thisName := none, hidden := [], dep := false, body := false, fill }
  let r ← tmToScala c [] e
  let (ty, body) := if (litFormType e).isSome || isAsc e then splitAsc (toTm r) else (none, toTm r)
  let P : ScalaSyntax.Program :=
    { imports := [(.zero, vanillaImportName)], name := "Main", prelude := [], params := none, ty, body }
  match ScalaSyntax.check P with
  | .ok _ => pure P
  | .error err => throw ("reader: " ++ err.msg)

/-- A surface term as a vanilla program, or the reason it has none (S-27). -/
def toScala (e : STm) : Except String ScalaSyntax.Program := toScalaWith false e

/-! ### Fills

The elaborated term of a compiled program has every slot written.  `fillTm`
turns it back into a surface term: a binder under the signature `s` is named
`x` and the length of `s`, as `Pretty.defaultNames` names them, a variable by
its binder, a label by the table.  A literal keeps its self type, a `let` its
type, and a member has no written type. -/

/-- The name of a binder introduced under the signature `s`. -/
def binderName (s : FCdot.Sig) : String := "x" ++ toString s.length

/-- A type of the target as a surface type (D-12). -/
def sTyOf (Λ : LabelTable) {s : FCdot.Sig} (nv : NameEnv s) (T : DotMNF.Ty s) : SType :=
  match T with
  | .top => .top
  | .bot => .bot
  | .typ A S U => .typ (ppLabel Λ A) (sTyOf Λ nv S) (sTyOf Λ nv U)
  | .fld a U => .fld (ppLabel Λ a) (sTyOf Λ nv U)
  | .sel (.var x) A => .sel (NameEnv.nameAt nv x) (ppLabel Λ A)
  | .mu U => .mu (binderName s) (sTyOf Λ (nv.cons (binderName s)) U)
  | .all S U => .all (binderName s) (sTyOf Λ nv S) (sTyOf Λ (nv.cons (binderName s)) U)
  | .and S U => .and (sTyOf Λ nv S) (sTyOf Λ nv U)
termination_by structural T

/-- An optional type of the target as an optional surface type. -/
def sTyOptOf (Λ : LabelTable) {s : FCdot.Sig} (nv : NameEnv s) : Option (DotMNF.Ty s) → Option SType
  | none => none
  | some T => some (sTyOf Λ nv T)

mutual
/-- An elaborated term as a surface term with every slot written. -/
def fillTm (Λ : LabelTable) {s : FCdot.Sig} (nv : NameEnv s) (a : ATm s) : STm :=
  match a with
  | .path (.var x) => .var (NameEnv.nameAt nv x)
  | .lam T t => .lam (binderName s) (some (sTyOf Λ nv T)) (fillTm Λ (nv.cons (binderName s)) t)
  | .obj T d =>
    .obj (binderName s) (some (sTyOf Λ (nv.cons (binderName s)) T))
      (fillDefs Λ (nv.cons (binderName s)) d)
  | .app x y => .app (.var (NameEnv.nameAt nv x)) (.var (NameEnv.nameAt nv y))
  | .proj x l => .proj (.var (NameEnv.nameAt nv x)) (ppLabel Λ l)
  | .«let» o t u =>
    .«let» (binderName s) (sTyOptOf Λ nv o) (fillTm Λ nv t) (fillTm Λ (nv.cons (binderName s)) u)
termination_by structural a
/-- Elaborated members as surface members, each field without a written type. -/
def fillDefs (Λ : LabelTable) {s : FCdot.Sig} (nv : NameEnv s) (d : ADefs s) : SDefs :=
  match d with
  | .typ A T => .typ (ppLabel Λ A) (sTyOf Λ nv T)
  | .trm l t => .trm (ppLabel Λ l) none (fillTm Λ nv t)
  | .and d₁ d₂ => .and (fillDefs Λ nv d₁) (fillDefs Λ nv d₂)
termination_by structural d
end

/-- A closed elaborated term as a surface term. -/
def fillSTm (Λ : LabelTable) (a : ATm []) : STm := fillTm Λ .nil a

/-- The fill of a compiled program as a vanilla program (S-27).  A written self
type prints as `(new Object { x => ds }: μ(x. T))`, a typed `let` whose body is
not its binder as `({ val x = t; u }: U)`, and a `μ` whose binder does not
occur as its body. -/
def fillToScala (Λ : LabelTable) (a : ATm []) : Except String ScalaSyntax.Program :=
  toScalaWith true (fillSTm Λ a)

/-! ### Round trips -/

/-- The answer of a round trip. -/
inductive Trip where
  /-- The text reads back to a term that resolves as the original does. -/
  | same
  /-- The term has no Scala form, for this reason. -/
  | gap (why : String)
  /-- The reader refuses the printed text. -/
  | unreadable (err : ScalaSyntax.Err)
  /-- The text reads back to a term that resolves otherwise. -/
  | differs
  /-- The term does not resolve with the table. -/
  | unresolved
deriving DecidableEq, Repr

/-- Print a term, read the text back, and compare the resolved terms (the
round trip (R) of S-27). -/
def roundTrip (Λ : LabelTable) (e : STm) : Trip :=
  match resolveP Λ e with
  | none => .unresolved
  | some p =>
    match toScala e with
    | .error why => .gap why
    | .ok P =>
      match readVanilla (ScalaSyntax.print P) with
      | .error err => .unreadable err
      | .ok (e', _) => if decide (resolveP Λ e' = some p) then .same else .differs

end Frontend.Scala
