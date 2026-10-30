import Coercions.Nominal.Frontend.Pipeline

/-!
# The printers

Printers from the term syntaxes of the front end back into the notation of
`pdc%`, so that a fill, a derivation's type or a run can be read as text.  The
surface tree prints with its names.  A partial term prints its empty slots as
the surface leaves them out.  An annotated term prints every self type and every
written `let` type.  A term of `Nominal.Source` prints as the annotated term with
no `let` type.  A configuration of the source machine and one of the runtime
print their store, then their term.  The FCn machine is printed through its
erasure, which is a runtime configuration (`ppRunFC`).  `ppReasonWith` prints
why a program is rejected, in the compiler's words where the compiler has them.
The module has no theorems.  The checks at the end are decided in the kernel.

A label is a sort and a number, so a name comes back only through a
`LabelTable`.  Without a table a label prints as its sort and number, `A0` for
the first type label and `a0` for the first term label.  A bound variable is an
index, so a name comes back through a `NameEnv`.  An alias of the environment
binds no variable and is skipped.  Under a binder the printer invents a name
with `freshName`, the first of eight short names not yet in the environment.
Two binders can get the same name, as the self binder of a literal bound by a
`let`, which is printed before the `let` binder is in scope.  The output is
alpha equivalent and shadows.  A store has no names, so its binders print as
`x0`, `x1` and so on, outermost first.

The output is meant to be read, not parsed back through `pdc%`.  Binder names
are invented, and a label that is a keyword, such as `Type`, prints without the
guillemets the notation needs.  Three forms have no notation and print so:
`alias x = p in u` and `bind widen x = t in u` for the two forms only the Scala
reader makes, and `a = ν{d₁, …}` for a nested literal of the runtime, which has
no binder.  A literal of the runtime and its lambdas have no types.

This is the model's printer (`Paths/Frontend/Pretty.lean`) for the syntax of
pDOT.  A literal is `ν(x : T) {d₁, …, dₙ}`, a type member `{A : S..U}`, and a
`let` the resolver made for an ascription prints as the ascription.
-/

namespace NominalFrontend

open Paths.FCdot (Sig BVar Kind Label Path)
open Nominal.Source (Ty Dec Tm Val Def Defs Rhs)

/-! ## Parentheses

Each printer takes the precedence of its position and parenthesizes a form that
binds more loosely.  The numbers are those of `Notation.lean`. -/

/-- Wrap in parentheses when `b`. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-- The entries of a definition list between braces, separated by commas. -/
def braces (es : List String) : String := "{" ++ String.intercalate ", " es ++ "}"

/-! ## Labels -/

/-- The first name the table interns at this label. -/
def labelName? (Λ : LabelTable) (l : Label) : Option String :=
  match Λ with
  | [] => none
  | (x, l') :: Λ' => if l' = l then some x else labelName? Λ' l
termination_by structural Λ

/-- The name of a label no table holds: the sort and the number. -/
def defaultLabelName : Label → String
  | .typ n => "A" ++ toString n
  | .trm n => "a" ++ toString n

/-- The name of a label, through the table where the table has one. -/
def ppLabel (Λ : LabelTable) (l : Label) : String :=
  (labelName? Λ l).getD (defaultLabelName l)

/-! ## Names for binders -/

/-- The short names a binder is given, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The first short name the environment does not hold. -/
def freshName (used : List String) : String :=
  match binderNames.find? (fun c => !used.contains c) with
  | some c => c
  | none => "x" ++ toString used.length

/-- The name of a bound variable.  An alias binds no variable and is skipped. -/
def NameEnv.nameAt : {s : Sig} → NameEnv s → BVar s .var → String
  | _, .cons _ y, .here => y
  | _, .cons nv _, .there i => NameEnv.nameAt nv i
  | _, .alias nv _ _, i => NameEnv.nameAt nv i
termination_by structural _ nv => nv

/-- Names for a signature that never had any, outermost binder `x0`. -/
def defaultNames (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (defaultNames s') ("x" ++ toString s'.length)
termination_by structural s

/-- The name `freshName` gives the next binder under `nv`. -/
def NameEnv.fresh {s : Sig} (nv : NameEnv s) : String := freshName nv.names

/-! ## Paths and types of `Nominal.Source` -/

/-- A path in the paper's notation, with a label table. -/
def ppPathWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (p : Path s) : String :=
  match p with
  | .var x => nv.nameAt x
  | .sel p' a => ppPathWith Λ nv p' ++ "." ++ ppLabel Λ a
termination_by structural p

mutual
/-- A type in the paper's notation, at the precedence of its position. -/
def ppTyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .rcd D => ppDecWith Λ nv D
  | .and S U => parenIf (p > 65) (ppTyAt Λ 66 nv S ++ " ∧ " ++ ppTyAt Λ 65 nv U)
  | .sel q A => ppPathWith Λ nv q ++ "." ++ ppLabel Λ A
  | .mu U =>
      let y := nv.fresh
      "μ(" ++ y ++ ". " ++ ppTyAt Λ 0 (nv.cons y) U ++ ")"
  | .all S U =>
      let y := nv.fresh
      parenIf (p > 60) ("∀(" ++ y ++ " : " ++ ppTyAt Λ 0 nv S ++ ") " ++ ppTyAt Λ 0 (nv.cons y) U)
  | .sngl q => ppPathWith Λ nv q ++ ".type"
termination_by structural T
/-- A declaration in the paper's notation. -/
def ppDecWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (D : Dec s) : String :=
  match D with
  | .typ A S U => "{" ++ ppLabel Λ A ++ " : " ++ ppTyAt Λ 0 nv S ++ ".." ++ ppTyAt Λ 0 nv U ++ "}"
  | .trm a U => "{" ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ 0 nv U ++ "}"
termination_by structural D
end

/-- A type in the paper's notation, with a label table. -/
def ppTyWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (T : Ty s) : String := ppTyAt Λ 0 nv T

/-- A closed type in the paper's notation. -/
def ppTy (Λ : LabelTable) (T : Ty []) : String := ppTyWith Λ .nil T

/-! ## Terms of `Nominal.Source`

A literal prints its self type, as the syntax holds it.  Only a lambda and a
`let` can need parentheses. -/

mutual
/-- A term in the paper's notation, at the precedence of its position. -/
def ppTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : Tm s) : String :=
  match t with
  | .val v => ppValAt Λ p nv v
  | .app q r => ppPathWith Λ nv q ++ " " ++ ppPathWith Λ nv r
  | .lett t' u =>
      let y := nv.fresh
      parenIf (p > 0) ("let " ++ y ++ " = " ++ ppTmAt Λ 1 nv t' ++ " in " ++ ppTmAt Λ 0 (nv.cons y) u)
  | .path q => ppPathWith Λ nv q
termination_by structural t
/-- A value in the paper's notation. -/
def ppValAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (v : Val s) : String :=
  match v with
  | .new T ds =>
      let y := nv.fresh
      "ν(" ++ y ++ " : " ++ ppTyWith Λ (nv.cons y) T ++ ") " ++ braces (ppDefsList Λ (nv.cons y) ds)
  | .lam S t =>
      let y := nv.fresh
      parenIf (p > 1) ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). " ++ ppTmAt Λ 0 (nv.cons y) t)
termination_by structural v
/-- One definition in the paper's notation. -/
def ppDefWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : Def s) : String :=
  match d with
  | .typ A T => "type " ++ ppLabel Λ A ++ " = " ++ ppTyWith Λ nv T
  | .trm a r => ppLabel Λ a ++ " = " ++ ppRhsWith Λ nv r
  | .cls C T => "class " ++ ppLabel Λ C ++ " = " ++ ppTyWith Λ nv T      -- N4 owns the class printer (plan XII D-16)
termination_by structural d
/-- The definitions of a literal, first definition first. -/
def ppDefsList (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (ds : Defs s) : List String :=
  match ds with
  | .nil => []
  | .cons ds' d => ppDefsList Λ nv ds' ++ [ppDefWith Λ nv d]
termination_by structural ds
/-- The right side of a field. -/
def ppRhsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (r : Rhs s) : String :=
  match r with
  | .defp q => ppPathWith Λ nv q
  | .defv v => ppValAt Λ 0 nv v
termination_by structural r
end

/-- A term in the paper's notation, with a label table. -/
def ppTmWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (t : Tm s) : String := ppTmAt Λ 0 nv t

/-- A closed term in the paper's notation. -/
def ppTm (Λ : LabelTable) (t : Tm []) : String := ppTmWith Λ .nil t

/-- A value in the paper's notation, with a label table. -/
def ppValWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (v : Val s) : String := ppValAt Λ 0 nv v

/-! ## Annotated terms

These are the terms a compilation returns.  They print the self type of a
literal and the written type of a `let`.  The `let` the resolver made for an
ascription, `let z : U = t in z` tagged `asc`, prints as `(t : U)`. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its position. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) : String :=
  match t with
  | .path q => ppPathWith Λ nv q
  | .app q r => ppPathWith Λ nv q ++ " " ++ ppPathWith Λ nv r
  | .lam S t' =>
      let y := nv.fresh
      parenIf (p > 1) ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). " ++ ppATmAt Λ 0 (nv.cons y) t')
  | .new T ds =>
      let y := nv.fresh
      "ν(" ++ y ++ " : " ++ ppTyWith Λ (nv.cons y) T ++ ") " ++ braces (ppADefsList Λ (nv.cons y) ds)
  | .«let» .asc (some U) t' (.path (.var .here)) =>
      "(" ++ ppATmAt Λ 0 nv t' ++ " : " ++ ppTyWith Λ nv U ++ ")"
  | .«let» _ ann t' u =>
      let y := nv.fresh
      let ann? :=
        match ann with
        | none => ""
        | some W => " : " ++ ppTyWith Λ nv W
      parenIf (p > 0)
        ("let " ++ y ++ ann? ++ " = " ++ ppATmAt Λ 1 nv t' ++ " in " ++ ppATmAt Λ 0 (nv.cons y) u)
termination_by structural t
/-- One annotated definition in the paper's notation. -/
def ppADefWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : ADef s) : String :=
  match d with
  | .typ A T => "type " ++ ppLabel Λ A ++ " = " ++ ppTyWith Λ nv T
  | .path a q => ppLabel Λ a ++ " = " ++ ppPathWith Λ nv q
  | .lam a S t =>
      let y := nv.fresh
      ppLabel Λ a ++ " = λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). " ++ ppATmAt Λ 0 (nv.cons y) t
  | .new a T ds =>
      let y := nv.fresh
      ppLabel Λ a ++ " = ν(" ++ y ++ " : " ++ ppTyWith Λ (nv.cons y) T ++ ") "
        ++ braces (ppADefsList Λ (nv.cons y) ds)
termination_by structural d
/-- The annotated definitions of a literal, first definition first. -/
def ppADefsList (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (ds : ADefs s) : List String :=
  match ds with
  | .nil => []
  | .cons ds' d => ppADefsList Λ nv ds' ++ [ppADefWith Λ nv d]
termination_by structural ds
end

/-- An annotated term in the paper's notation, with a label table. -/
def ppATmWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (t : ATm s) : String := ppATmAt Λ 0 nv t

/-- A closed annotated term in the paper's notation. -/
def ppATm (Λ : LabelTable) (t : ATm []) : String := ppATmWith Λ .nil t

/-! ## Partial terms

The syntax `resolveP` returns, whose slots may be empty.  An empty domain
prints as `λx. t`, an empty self type as `ν(x) {…}`, and a written declared type
of a lambda field as `a : U = λ…`.  The binding of an ascription prints as the
ascription.  Every other `let` prints as a `let`, whatever its tag. -/

mutual
/-- A partial term in the paper's notation, at the precedence of its position. -/
def ppPTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : PTm s) : String :=
  match t with
  | .path q => ppPathWith Λ nv q
  | .app q r => ppPathWith Λ nv q ++ " " ++ ppPathWith Λ nv r
  | .lam (some S) t' =>
      let y := nv.fresh
      parenIf (p > 1) ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). " ++ ppPTmAt Λ 0 (nv.cons y) t')
  | .lam none t' =>
      let y := nv.fresh
      parenIf (p > 1) ("λ" ++ y ++ ". " ++ ppPTmAt Λ 0 (nv.cons y) t')
  | .new (some T) ds =>
      let y := nv.fresh
      "ν(" ++ y ++ " : " ++ ppTyWith Λ (nv.cons y) T ++ ") " ++ braces (ppPDefsList Λ (nv.cons y) ds)
  | .new none ds =>
      let y := nv.fresh
      "ν(" ++ y ++ ") " ++ braces (ppPDefsList Λ (nv.cons y) ds)
  | .«let» .asc (some U) t' (.path (.var .here)) =>
      "(" ++ ppPTmAt Λ 0 nv t' ++ " : " ++ ppTyWith Λ nv U ++ ")"
  | .«let» _ ann t' u =>
      let y := nv.fresh
      let ann? :=
        match ann with
        | none => ""
        | some W => " : " ++ ppTyWith Λ nv W
      parenIf (p > 0)
        ("let " ++ y ++ ann? ++ " = " ++ ppPTmAt Λ 1 nv t' ++ " in " ++ ppPTmAt Λ 0 (nv.cons y) u)
termination_by structural t
/-- One definition of a partial literal in the paper's notation. -/
def ppPDefWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : PDef s) : String :=
  match d with
  | .typ A T => "type " ++ ppLabel Λ A ++ " = " ++ ppTyWith Λ nv T
  | .path a q => ppLabel Λ a ++ " = " ++ ppPathWith Λ nv q
  | .lam a decl dom t =>
      let y := nv.fresh
      let decl? :=
        match decl with
        | none => ""
        | some U => " : " ++ ppTyWith Λ nv U
      let dom? :=
        match dom with
        | none => "λ" ++ y ++ ". "
        | some S => "λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). "
      ppLabel Λ a ++ decl? ++ " = " ++ dom? ++ ppPTmAt Λ 0 (nv.cons y) t
  | .new a (some T) ds =>
      let y := nv.fresh
      ppLabel Λ a ++ " = ν(" ++ y ++ " : " ++ ppTyWith Λ (nv.cons y) T ++ ") "
        ++ braces (ppPDefsList Λ (nv.cons y) ds)
  | .new a none ds =>
      let y := nv.fresh
      ppLabel Λ a ++ " = ν(" ++ y ++ ") " ++ braces (ppPDefsList Λ (nv.cons y) ds)
termination_by structural d
/-- The definitions of a partial literal, first definition first. -/
def ppPDefsList (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (ds : PDefs s) : List String :=
  match ds with
  | .nil => []
  | .cons ds' d => ppPDefsList Λ nv ds' ++ [ppPDefWith Λ nv d]
termination_by structural ds
end

/-- A partial term in the paper's notation, with a label table. -/
def ppPTmWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (t : PTm s) : String := ppPTmAt Λ 0 nv t

/-- A closed partial term in the paper's notation. -/
def ppPTm (Λ : LabelTable) (t : PTm []) : String := ppPTmWith Λ .nil t

/-! ## Surface phrases

Surface syntax carries its names, so these need no table or environment.  The
operator of an application is printed at 70, the operand at 71 and the
receiver of a projection at 80. -/

/-- A surface path, root first. -/
def ppSPath (p : SPath) : String :=
  match p with
  | .var x => x
  | .sel p' a => ppSPath p' ++ "." ++ a
termination_by structural p

/-- A surface type in the paper's notation, at the precedence of its position. -/
def ppSTyAt (p : Nat) (T : SType) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U => "{" ++ A ++ " : " ++ ppSTyAt 0 S ++ ".." ++ ppSTyAt 0 U ++ "}"
  | .fld a U => "{" ++ a ++ " : " ++ ppSTyAt 0 U ++ "}"
  | .sngl q => ppSPath q ++ ".type"
  | .sel q A => ppSPath q ++ "." ++ A
  | .mu x U => "μ(" ++ x ++ ". " ++ ppSTyAt 0 U ++ ")"
  | .all x S U => parenIf (p > 60) ("∀(" ++ x ++ " : " ++ ppSTyAt 0 S ++ ") " ++ ppSTyAt 0 U)
  | .and S U => parenIf (p > 65) (ppSTyAt 66 S ++ " ∧ " ++ ppSTyAt 65 U)
termination_by structural T

/-- A surface type in the paper's notation. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

/-- The word for the kind of a binding the Scala reader inserts. -/
def SBind.word : SBind → String
  | .widen => "widen"
  | .unstable => "unstable"

mutual
/-- A surface term in the paper's notation, at the precedence of its position.
A path in term position is nested `proj`. -/
def ppSTmAt (p : Nat) (e : STm) : String :=
  match e with
  | .var x => x
  | .lam x (some T) t => parenIf (p > 1) ("λ(" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). " ++ ppSTmAt 0 t)
  | .lam x none t => parenIf (p > 1) ("λ" ++ x ++ ". " ++ ppSTmAt 0 t)
  | .obj x (some T) d => "ν(" ++ x ++ " : " ++ ppSTyAt 0 T ++ ") " ++ braces (ppSDefsList d)
  | .obj x none d => "ν(" ++ x ++ ") " ++ braces (ppSDefsList d)
  | .app t u => parenIf (p > 70) (ppSTmAt 70 t ++ " " ++ ppSTmAt 71 u)
  | .proj t a => ppSTmAt 80 t ++ "." ++ a
  | .«let» x ann t u =>
      let ann? :=
        match ann with
        | none => ""
        | some U => " : " ++ ppSTyAt 0 U
      parenIf (p > 0) ("let " ++ x ++ ann? ++ " = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
  | .asc t T => "(" ++ ppSTmAt 0 t ++ " : " ++ ppSTyAt 0 T ++ ")"
  | .alias x q u => parenIf (p > 0) ("alias " ++ x ++ " = " ++ ppSPath q ++ " in " ++ ppSTmAt 0 u)
  | .bind k x t u =>
      parenIf (p > 0) ("bind " ++ k.word ++ " " ++ x ++ " = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
termination_by structural e
/-- The surface definitions of a literal, first definition first. -/
def ppSDefsList (d : SDefs) : List String :=
  match d with
  | .nil => []
  | .typ ds A T => ppSDefsList ds ++ ["type " ++ A ++ " = " ++ ppSTyAt 0 T]
  | .trm ds a none t => ppSDefsList ds ++ [a ++ " = " ++ ppSTmAt 0 t]
  | .trm ds a (some T) t => ppSDefsList ds ++ [a ++ " : " ++ ppSTyAt 0 T ++ " = " ++ ppSTmAt 0 t]
termination_by structural d
end

/-- A surface term in the paper's notation. -/
def ppSTm (e : STm) : String := ppSTmAt 0 e

/-- Surface definitions in the paper's notation, between braces. -/
def ppSDefs (d : SDefs) : String := braces (ppSDefsList d)

/-! ## Reasons

A rejection prints as the compiler's message where the compiler has one:
"Missing parameter type" for `AnonymousFunctionMissingParamType`, and
"Recursive value a needs type" for a cyclic reference.  A label prints through
the table.  A reason of the typer (`TReason`) prints as the side condition or
rule it names.  `selfSingleton` holds the field labels of the path after its
root, so the root prints as `_`.  `noField`, `notFunction` and `argMismatch`
have a message, and the elaborator of XF3a reports none of them. -/

/-- A reason of the typer as a message, with a label table. -/
def ppTReasonWith (Λ : LabelTable) : TReason → String
  | .selfSingleton bs =>
      "The path _" ++ String.join (bs.map fun b => "." ++ ppLabel Λ b)
        ++ " is checked at its own singleton type, which no pDOT rule derives"
  | .notTight b => "The literal at " ++ ppLabel Λ b ++ " has a type member with two different bounds"
  | .dupLabel l => "Two definitions of " ++ ppLabel Λ l
  | .fieldNotFun l => "The lambda field " ++ ppLabel Λ l ++ " is declared at a type that is no function type"
  | .noField a => "No member " ++ ppLabel Λ a
  | .notFunction => "The callee has no function type"
  | .argMismatch => "The argument does not meet the domain of the callee"
  | .literalGoal => "An object literal is checked against a goal, which pDOT meets only through a let"

/-- A reason of the front end as a message, with a label table. -/
def ppReasonWith (Λ : LabelTable) : PReason → String
  | .missingParamType none => "Missing parameter type"
  | .missingParamType (some l) => "Missing parameter type in " ++ ppLabel Λ l
  | .cyclicRef l => "Recursive value " ++ ppLabel Λ l ++ " needs type"
  | .needsExplicitType l => "Value " ++ ppLabel Λ l ++ " needs a written type"
  | .ambiguous l => "The types of " ++ ppLabel Λ l ++ " have no least one"
  | .landed r => ppTReasonWith Λ r
  | .mismatch => "Type mismatch"
  | .limit => "Recursion limit exceeded"

/-- A reason of the front end as a message, with no label table. -/
def ppReason (r : PReason) : String := ppReasonWith [] r

/-- The answer of `compileE`: the fill and its type, or the reason. -/
def ppCompileE (Λ : LabelTable) : Except PReason ((a : ATm []) × Compiled a) → String
  | .ok r => "ok: " ++ ppATm Λ r.1 ++ " : " ++ ppTy Λ r.2.ty
  | .error r => "rejected: " ++ ppReasonWith Λ r

/-! ## Configurations

A store prints one entry per binder, outermost first, `·` when empty.  A
configuration prints as `⟨store | term⟩`. -/

/-- The store of the source machine, one entry per binder, outermost first. -/
def storeEntries (Λ : LabelTable) : {s : Sig} → Nominal.Source.Store s → List String
  | _, .nil => []
  | _, .cons (s := s) σ v =>
      storeEntries Λ σ ++ [("x" ++ toString s.length) ++ " = " ++ ppValWith Λ (defaultNames s) v]

/-- A store in the paper's notation. -/
def ppStoreList (es : List String) : String :=
  match es with
  | [] => "·"
  | _ => String.intercalate ", " es

/-- A configuration of the source machine. -/
def ppConfWith (Λ : LabelTable) (c : Nominal.Source.Conf) : String :=
  "⟨" ++ ppStoreList (storeEntries Λ c.store) ++ " | " ++ ppTmWith Λ (defaultNames c.s) c.tm ++ "⟩"

/-! ### The runtime

The erasure of both machines.  No types.  A nested literal has no binder, its
self is named by its path, and it prints as `ν{…}`. -/

mutual
/-- A runtime term, at the precedence of its position. -/
def ppRTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : PDot.Runtime.Tm s) : String :=
  match t with
  | .path q => ppPathWith Λ nv q
  | .val v => ppRValAt Λ p nv v
  | .app q r => ppPathWith Λ nv q ++ " " ++ ppPathWith Λ nv r
  | .lett t' u =>
      let y := nv.fresh
      parenIf (p > 0) ("let " ++ y ++ " = " ++ ppRTmAt Λ 1 nv t' ++ " in " ++ ppRTmAt Λ 0 (nv.cons y) u)
termination_by structural t
/-- A runtime value. -/
def ppRValAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (v : PDot.Runtime.Val s) : String :=
  match v with
  | .new ds =>
      let y := nv.fresh
      "ν(" ++ y ++ ") " ++ braces (ppRDefsList Λ (nv.cons y) ds)
  | .lam t =>
      let y := nv.fresh
      parenIf (p > 1) ("λ" ++ y ++ ". " ++ ppRTmAt Λ 0 (nv.cons y) t)
termination_by structural v
/-- The fields of a runtime literal, first field first. -/
def ppRDefsList (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (ds : PDot.Runtime.Defs s) : List String :=
  match ds with
  | .nil => []
  | .cons ds' a r => ppRDefsList Λ nv ds' ++ [ppLabel Λ a ++ " = " ++ ppRRhsWith Λ nv r]
termination_by structural ds
/-- The right side of a runtime field. -/
def ppRRhsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (r : PDot.Runtime.Rhs s) : String :=
  match r with
  | .defp q => ppPathWith Λ nv q
  | .defv v => ppRValAt Λ 0 nv v
  | .nest ds => "ν" ++ braces (ppRDefsList Λ nv ds)
termination_by structural r
end

/-- The store of the runtime, one entry per binder, outermost first. -/
def rstoreEntries (Λ : LabelTable) : {s : Sig} → PDot.Runtime.Store s → List String
  | _, .nil => []
  | _, .cons (s := s) σ v =>
      rstoreEntries Λ σ ++ [("x" ++ toString s.length) ++ " = " ++ ppRValAt Λ 0 (defaultNames s) v]

/-- A configuration of the runtime. -/
def ppRConfWith (Λ : LabelTable) (c : PDot.Runtime.Conf) : String :=
  "⟨" ++ ppStoreList (rstoreEntries Λ c.store) ++ " | " ++ ppRTmAt Λ 0 (defaultNames c.s) c.tm ++ "⟩"

/-- The answer of `compileAndRun`, in full. -/
def ppRun (Λ : LabelTable) : Option Nominal.Source.Conf → String
  | none => "did not compile"
  | some c => ppConfWith Λ c

/-- The answer of `compileAndRun`, erased to the runtime. -/
def ppRunErased (Λ : LabelTable) : Option Nominal.Source.Conf → String
  | none => "did not compile"
  | some c => ppRConfWith Λ c.erase

/-- The answer of `compileAndRunFC`, erased to the runtime. -/
def ppRunFC (Λ : LabelTable) : Option ((s : Sig) × Nominal.FCn.State s) → String
  | none => "did not compile"
  | some ⟨_, st⟩ => ppRConfWith Λ st.erase

/-! ## Checks

Each check is decided in the kernel.  The programs are those of `Sources.lean`
and the namespace `ElabChecks` of `Pipeline.lean`, and the three programs of
the checks sit in the namespace `PrettyChecks`. -/

namespace PrettyChecks

open NominalFrontend.Sources NominalFrontend.ElabChecks Frontend.Reason

/-- The surface program E7, back in the notation it was written in. -/
example : ppSTm E7_src =
    "let core = ν(c : {types : μ(t. {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤})} ∧ {m : c.types.type}) "
      ++ "{types = ν(t : {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}) {type A = ⊤, f = λ(u : ⊤). u}, m = c.types} "
      ++ "in core.m.f core" := by
  decide +kernel

/-- E7 resolved.  Binder names are invented, and the self binder and the `let`
binder both get the name `x`, since the literal is printed before the `let`
binder is in scope. -/
example : (resolve Λ7 E7_src).map (ppATm Λ7) = some
    ("let x = ν(x : {types : μ(y. {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤})} ∧ {m : x.types.type}) "
      ++ "{types = ν(y : {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤}) {type A = ⊤, f = λ(z : ⊤). z}, m = x.types} "
      ++ "in x.m.f x") := by
  decide +kernel

/-- The same term with no table: a label is its sort and its number. -/
example : (resolve Λ7 E7_src).map (ppATm []) = some
    ("let x = ν(x : {a0 : μ(y. {A0 : ⊤..⊤} ∧ {a1 : ∀(z : ⊤) ⊤})} ∧ {a2 : x.a0.type}) "
      ++ "{a0 = ν(y : {A0 : ⊤..⊤} ∧ {a1 : ∀(z : ⊤) ⊤}) {type A0 = ⊤, a1 = λ(z : ⊤). z}, a2 = x.a0} "
      ++ "in x.a2.a1 x") := by
  decide +kernel

/-- The erasure prints as the annotated term when no `let` has a type. -/
example : (resolve Λ7 E7_src).map (fun a => ppTm Λ7 a.erase) = (resolve Λ7 E7_src).map (ppATm Λ7) := by
  decide +kernel

/-- The source term of `Nominal.Source` prints the same text. -/
example : some (ppTm Λ7 Nominal.Source.E7_prog) = (resolve Λ7 E7_src).map (ppATm Λ7) := by
  decide +kernel

/-- A partial term prints its empty self types as the surface leaves them out. -/
example : (resolveP Λ7 E7_srcI).map (ppPTm Λ7) =
    some "let x = ν(x) {types = ν(y) {type A = ⊤, f = λ(z : ⊤). z}, m = x.types} in x.m.f x" := by
  decide +kernel

/-- The labels of the two programs below. -/
def ΛF : LabelTable := [("f", .trm 0), ("g", .trm 1)]

/-- A written declared type on a lambda field, and two empty domains. -/
def Fld_src : STm := pdc% ν(x) {f : ∀(u : ⊤) ⊤ = λu. u, g = λu. x.f u}

/-- An ascription of a lambda with an empty domain. -/
def Asc_src : STm := pdc% (λx. x : ∀(z : ⊤) ⊤)

example : ppSTm Fld_src = "ν(x) {f : ∀(u : ⊤) ⊤ = λu. u, g = λu. x.f u}" := by decide +kernel

example : (resolveP ΛF Fld_src).map (ppPTm ΛF) = some "ν(x) {f : ∀(y : ⊤) ⊤ = λy. y, g = λy. x.f y}" := by
  decide +kernel

/-- The fill with its formed self type, and the type of the program. -/
example : ppCompileE ΛF (compileE {} ΛF Fld_src) =
    "ok: ν(x : {f : ∀(y : ⊤) ⊤} ∧ {g : ∀(y : ⊤) ⊤}) {f = λ(y : ⊤). y, g = λ(y : ⊤). x.f y} "
      ++ ": μ(x. {f : ∀(y : ⊤) ⊤} ∧ {g : ∀(y : ⊤) ⊤})" := by
  decide +kernel

example : ppSTm Asc_src = "(λx. x : ∀(z : ⊤) ⊤)" := by decide +kernel

/-- The binding of an ascription prints as the ascription. -/
example : (resolveP [] Asc_src).map (ppPTm []) = some "(λx. x : ∀(x : ⊤) ⊤)" := by decide +kernel

example : ppCompileE [] (compileE {} [] Asc_src) = "ok: (λ(x : ⊤). x : ∀(x : ⊤) ⊤) : ∀(x : ⊤) ⊤" := by
  decide +kernel

/-- Only the left operand of `∧` needs parentheses. -/
example : ppTy [] (.and (.and .top .bot) (.and .bot .top)) = "(⊤ ∧ ⊥) ∧ ⊥ ∧ ⊤" := by decide +kernel

/-- So does a function type there. -/
example : ppTy [] (.and (.all .top .top) .bot) = "(∀(x : ⊤) ⊤) ∧ ⊥" := by decide +kernel

/-- A binder takes the first short name not in the environment. -/
example : ppTy [] (.mu (.rcd (.trm (.trm 0) (.mu (.sel (.var (.there .here)) (.typ 0)))))) =
    "μ(x. {a0 : μ(y. x.A0)})" := by
  decide +kernel

/-- The two forms only the Scala reader makes. -/
example : ppSTm (.alias "c" (.var "core") (.var "c")) = "alias c = core in c" := by decide +kernel

example : ppSTm (.bind .widen "y" (.var "x") (.var "y")) = "bind widen y = x in y" := by decide +kernel

/-- Every reason, with its labels through the table. -/
example : [Reason.missingParamType none, .missingParamType (some (.trm 2)), .cyclicRef (.trm 0),
      .needsExplicitType (.trm 1), .ambiguous (.trm 1), .landed (.selfSingleton [.trm 0, .trm 1]),
      .landed (.notTight (.trm 3)), .landed (.dupLabel (.trm 0)), .landed (.fieldNotFun (.trm 2)),
      .landed (.noField (.trm 1)), .landed .notFunction, .landed .argMismatch, .landed .literalGoal,
      .mismatch, .limit].map (ppReasonWith ΛS) =
    ["Missing parameter type", "Missing parameter type in f", "Recursive value a needs type",
      "Value b needs a written type", "The types of b have no least one",
      "The path _.a.b is checked at its own singleton type, which no pDOT rule derives",
      "The literal at m has a type member with two different bounds", "Two definitions of a",
      "The lambda field f is declared at a type that is no function type", "No member b",
      "The callee has no function type", "The argument does not meet the domain of the callee",
      "An object literal is checked against a goal, which pDOT meets only through a let",
      "Type mismatch", "Recursion limit exceeded"] := by
  decide +kernel

/-- Without a table a label is its sort and its number. -/
example : ppReason (.cyclicRef (.trm 0)) = "Recursive value a0 needs type" := by decide +kernel

/-- N4 is rejected at its own singleton.  The path is the variable, so no label follows `_`. -/
example : ppCompileE ΛN4 (compileE {} ΛN4 N4_src) =
    "rejected: The path _ is checked at its own singleton type, which no pDOT rule derives" := by
  decide +kernel

/-- Two lambda fields that read each other with no written type. -/
example : ppCompileE ΛS (compileE {} ΛS Cyc_src) = "rejected: Recursive value a needs type" := by
  decide +kernel

/-- E13 with its self type formed. -/
example : ppCompileE Λ13 (compileE {} Λ13 E13_srcI) =
    "ok: ν(x : {a : x.a.type}) {a = x.a} : μ(x. {a : x.a.type})" := by
  decide +kernel

/-- The end of E7's source run, with the store's binder `x0`. -/
example : ppRun Λ7 (compileAndRun {} 4 2 Λ7 E7_srcI) =
    "⟨x0 = ν(x : {types : μ(y. {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤})} ∧ {m : x.types.type}) "
      ++ "{types = ν(y : {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤}) {type A = ⊤, f = λ(z : ⊤). z}, m = x.types} | x0⟩" := by
  decide +kernel

/-- Its erasure.  The runtime drops types and type members, and a nested literal
has no binder. -/
example : ppRunErased Λ7 (compileAndRun {} 4 2 Λ7 E7_srcI) =
    "⟨x0 = ν(x) {types = ν{f = λy. y}, m = x.types} | x0⟩" := by
  decide +kernel

/-- Nothing to print. -/
example : ppRun [] none = "did not compile" ∧ ppRunErased [] none = "did not compile" ∧
    ppRunFC [] none = "did not compile" := by
  decide +kernel

end PrettyChecks

end NominalFrontend
