import Coercions.ScalaSyntax.Read
import Coercions.Paths.FCdot.Debruijn

/-!
# The surface syntax of the pDOT front end

The notation (`Notation.lean`) and the Scala reader produce a value of the
inductives below and nothing else.  All the work on the indexed calculus
happens later, in the ordinary functions of `Resolve.lean`.

The tree is the one of the paths front end (`Paths/Frontend/Surface.lean`)
with four changes (plan XI, "The surface tree").  There is no stable field
declaration.  Definitions are a spine that grows on the right from `nil`, as
pDOT's `Defs` do.  Two term forms have no notation: `alias` and `bind`, which
only the Scala reader makes (plan XI D-10, D-12).

Labels are strings.  A `LabelTable` interns them.  The sort of a name is its
position, never its case (plan XI D-3).  So one name may have a type label and
a term label at once, and a capitalized name in a field position is a term
label.

A lambda's domain and a literal's self type are `Option`s.  `none` is a slot
the programmer left empty, for the elaborator to fill.

The four side conditions are `Bool` functions, one per family.  `Scoped` asks
that every free name is bound.  `LabelsIn` asks that every label is in the
table at its sort.  `FieldsOk` asks that a field holds a path, a lambda or a
literal, and that a written field type sits on a lambda field, or on a path
field `p` as exactly `p.type`.  `PathOperands` asks that every operand of an
application and every receiver of a projection is a path, and that no `bind`
occurs.

Every recursive definition is structural, so it reduces in the kernel and
`by decide` works on it.  No function here reads the characters of a name.
Names are compared by `decide (x = y)` and `List.contains`.

Nothing here belongs to the metatheory.
-/

namespace PDotFrontend

open Paths.FCdot (Label)

/-! ## The named abstract syntax -/

/-- A surface path: a variable and a chain of field steps, by name. -/
inductive SPath : Type where
  /-- `x`, a variable by name. -/
  | var (x : String)
  /-- `p.a`, one more field step. -/
  | sel (p : SPath) (a : String)
deriving DecidableEq, Repr, Inhabited

/-- Surface types, with binders and labels as strings. -/
inductive SType : Type where
  /-- `⊤`. -/
  | top
  /-- `⊥`. -/
  | bot
  /-- `{A : S..T}`, a type member declaration. -/
  | typ (A : String) (S T : SType)
  /-- `{a : T}`, a term member declaration. -/
  | fld (a : String) (T : SType)
  /-- `p.type`, the singleton of a path. -/
  | sngl (p : SPath)
  /-- `p.A`, a type selection at a path. -/
  | sel (p : SPath) (A : String)
  /-- `μ(x. T)`, a recursive self type. -/
  | mu (x : String) (T : SType)
  /-- `∀(x : S) T`, a dependent function type. -/
  | all (x : String) (S T : SType)
  /-- `S ∧ T`, an intersection. -/
  | and (S T : SType)
deriving DecidableEq, Repr, Inhabited

/-- The two kinds of binding that the Scala reader inserts. -/
inductive SBind : Type where
  /-- scalac's widening at a `val` with no written type. -/
  | widen
  /-- An unstable prefix, bound first (plan XI D-10). -/
  | unstable
deriving DecidableEq, Repr, Inhabited

mutual
/-- Surface terms.  Application and selection take arbitrary terms.
`Resolve.lean` inserts lets to restore monadic normal form.  A path `x.a.b` in
term position is nested `proj`, not a new form. -/
inductive STm : Type where
  /-- `x`, a variable by name. -/
  | var (x : String)
  /-- `λ(x : T). t`, or `λx. t` with the domain left to inference. -/
  | lam (x : String) (T : Option SType) (t : STm)
  /-- `ν(x : T) {d}`, or `ν(x) {d}` with the self type left to inference. -/
  | obj (x : String) (T : Option SType) (d : SDefs)
  /-- `t u`, direct style. -/
  | app (t u : STm)
  /-- `t.a`, direct style. -/
  | proj (t : STm) (a : String)
  /-- `let x = t in u`, or `let x : T = t in u` with a written type. -/
  | «let» (x : String) (ann : Option SType) (t u : STm)
  /-- `(t : T)`, an ascription. -/
  | asc (t : STm) (T : SType)
  /-- No notation, made by `ofScala` (plan XI D-10, D-12).  The body `u` with
  the name `x` standing for the path `p`. -/
  | alias (x : String) (p : SPath) (u : STm)
  /-- No notation, made by `ofScala` (plan XI D-10, D-12).  A binding of `x`
  to `t` in `u` that the reader inserted, of kind `k`. -/
  | bind (k : SBind) (x : String) (t u : STm)
/-- Surface definitions, a spine that grows on the right. -/
inductive SDefs : Type where
  /-- No definition yet, the start of `{d₁, …, dₙ}`. -/
  | nil
  /-- `ds, type A = T`. -/
  | typ (ds : SDefs) (A : String) (T : SType)
  /-- `ds, a = t`, or `ds, a : T = t` with a written type. -/
  | trm (ds : SDefs) (a : String) (T : Option SType) (t : STm)
end

deriving instance DecidableEq, Repr for STm, SDefs

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDefs := ⟨.nil⟩

/-! ## Paths in term position -/

/-- A variable is a path, and `t.a` is a path when `t` is.  Nothing else is. -/
def STm.isPath : STm → Bool
  | .var _ => true
  | .proj t _ => t.isPath
  | _ => false

/-- The surface path of a term that is a path, and `none` otherwise. -/
def STm.toPath? : STm → Option SPath
  | .var x => some (.var x)
  | .proj t a => t.toPath?.map (·.sel a)
  | _ => none

/-! ## The label table

Type labels and term labels are disjoint in the target, so a lookup names its
sort.  An entry of the other sort with the same name is skipped, so one name
may have a label at each sort. -/

/-- A label table maps surface names to target labels, first entry first. -/
abbrev LabelTable := List (String × Label)

/-- The label of the first entry `(A, .typ n)`. -/
def labelTyp? (Λ : LabelTable) (A : String) : Option Label :=
  match Λ with
  | [] => none
  | (y, .typ n) :: Λ' => if A = y then some (.typ n) else labelTyp? Λ' A
  | (_, .trm _) :: Λ' => labelTyp? Λ' A

/-- The label of the first entry `(a, .trm n)`. -/
def labelTrm? (Λ : LabelTable) (a : String) : Option Label :=
  match Λ with
  | [] => none
  | (y, .trm n) :: Λ' => if a = y then some (.trm n) else labelTrm? Λ' a
  | (_, .typ _) :: Λ' => labelTrm? Λ' a

/-! ### The default table of a program

The names in label position, in text order, each with its sort: `true` for a
type position, `false` for a term position. -/

/-- The field steps of a surface path, root first.  Each is a term name. -/
def SPath.labelNames : SPath → List (String × Bool)
  | .var _ => []
  | .sel p a => p.labelNames ++ [(a, false)]

/-- The names in label position of a surface type, in text order. -/
def SType.labelNames : SType → List (String × Bool)
  | .top => []
  | .bot => []
  | .typ A S T => (A, true) :: (S.labelNames ++ T.labelNames)
  | .fld a T => (a, false) :: T.labelNames
  | .sngl p => p.labelNames
  | .sel p A => p.labelNames ++ [(A, true)]
  | .mu _ T => T.labelNames
  | .all _ S T => S.labelNames ++ T.labelNames
  | .and S T => S.labelNames ++ T.labelNames

/-- The names in label position of an optional type.  An empty slot has none. -/
def SType.labelNamesOpt : Option SType → List (String × Bool)
  | none => []
  | some T => T.labelNames

mutual
/-- The names in label position of a surface term, in text order. -/
def STm.labelNames (e : STm) : List (String × Bool) :=
  match e with
  | .var _ => []
  | .lam _ T t => SType.labelNamesOpt T ++ STm.labelNames t
  | .obj _ T d => SType.labelNamesOpt T ++ SDefs.labelNames d
  | .app t u => STm.labelNames t ++ STm.labelNames u
  | .proj t a => STm.labelNames t ++ [(a, false)]
  | .«let» _ ann t u => SType.labelNamesOpt ann ++ STm.labelNames t ++ STm.labelNames u
  | .asc t T => STm.labelNames t ++ T.labelNames
  | .alias _ p u => p.labelNames ++ STm.labelNames u
  | .bind _ _ t u => STm.labelNames t ++ STm.labelNames u
termination_by structural e
/-- The names in label position of surface definitions, in text order: the
earlier definitions, then the defined name, then its type and right side. -/
def SDefs.labelNames (d : SDefs) : List (String × Bool) :=
  match d with
  | .nil => []
  | .typ ds A T => SDefs.labelNames ds ++ (A, true) :: T.labelNames
  | .trm ds a T t =>
      SDefs.labelNames ds ++ (a, false) :: (SType.labelNamesOpt T ++ STm.labelNames t)
termination_by structural d
end

/-- Number type names and term names separately, in order of first appearance.
The first argument is the table built so far, the two counters are the next
type index and the next term index.  A name already in the table at its sort
is skipped. -/
def intern : LabelTable → Nat → Nat → List (String × Bool) → LabelTable
  | acc, _, _, [] => acc
  | acc, i, j, (x, true) :: xs =>
      if (labelTyp? acc x).isSome then intern acc i j xs
      else intern (acc ++ [(x, .typ i)]) (i + 1) j xs
  | acc, i, j, (x, false) :: xs =>
      if (labelTrm? acc x).isSome then intern acc i j xs
      else intern (acc ++ [(x, .trm j)]) i (j + 1) xs

/-- The default label table of a program: every name in label position, once
per sort, in order of first appearance, at the sort its position names. -/
def labelsOfProgram (e : STm) : LabelTable := intern [] 0 0 e.labelNames

/-! ## Scoping

`Scoped Γ` holds when every free name of the phrase is in `Γ`, innermost binder
first.  The self binder of `ν(x : T) {d}` scopes over its own annotation.  The
binder of a `let` scopes over the body only. -/

/-- The root of the path is in the list.  Field steps add no names. -/
def SPath.Scoped : List String → SPath → Bool
  | Γ, .var x => Γ.contains x
  | Γ, .sel p _ => SPath.Scoped Γ p

/-- Every free name of a surface type is in the list. -/
def SType.Scoped : List String → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Γ, .typ _ S T => SType.Scoped Γ S && SType.Scoped Γ T
  | Γ, .fld _ T => SType.Scoped Γ T
  | Γ, .sngl p => SPath.Scoped Γ p
  | Γ, .sel p _ => SPath.Scoped Γ p
  | Γ, .mu x T => SType.Scoped (x :: Γ) T
  | Γ, .all x S T => SType.Scoped Γ S && SType.Scoped (x :: Γ) T
  | Γ, .and S T => SType.Scoped Γ S && SType.Scoped Γ T

/-- Every free name of an optional type is in the list.  An empty slot has
none. -/
def SType.ScopedOpt (Γ : List String) : Option SType → Bool
  | none => true
  | some T => SType.Scoped Γ T

mutual
/-- Every free name of a surface term is in the list. -/
def STm.Scoped (Γ : List String) (e : STm) : Bool :=
  match e with
  | .var x => Γ.contains x
  | .lam x T t => SType.ScopedOpt Γ T && STm.Scoped (x :: Γ) t
  | .obj x T d => SType.ScopedOpt (x :: Γ) T && SDefs.Scoped (x :: Γ) d
  | .app t u => STm.Scoped Γ t && STm.Scoped Γ u
  | .proj t _ => STm.Scoped Γ t
  | .«let» x ann t u => SType.ScopedOpt Γ ann && STm.Scoped Γ t && STm.Scoped (x :: Γ) u
  | .asc t T => STm.Scoped Γ t && SType.Scoped Γ T
  | .alias x p u => SPath.Scoped Γ p && STm.Scoped (x :: Γ) u
  | .bind _ x t u => STm.Scoped Γ t && STm.Scoped (x :: Γ) u
termination_by structural e
/-- Every free name of surface definitions is in the list. -/
def SDefs.Scoped (Γ : List String) (d : SDefs) : Bool :=
  match d with
  | .nil => true
  | .typ ds _ T => SDefs.Scoped Γ ds && SType.Scoped Γ T
  | .trm ds _ T t => SDefs.Scoped Γ ds && SType.ScopedOpt Γ T && STm.Scoped Γ t
termination_by structural d
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table at the
sort its position demands.  The positions are those of `labelNames`. -/

/-- Every field step of a surface path is a term label of the table. -/
def SPath.LabelsIn : LabelTable → SPath → Bool
  | _, .var _ => true
  | Λ, .sel p a => SPath.LabelsIn Λ p && (labelTrm? Λ a).isSome

/-- Every label of a surface type is in the table at the right sort. -/
def SType.LabelsIn : LabelTable → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Λ, .typ A S T => (labelTyp? Λ A).isSome && SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .fld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | Λ, .sngl p => SPath.LabelsIn Λ p
  | Λ, .sel p A => SPath.LabelsIn Λ p && (labelTyp? Λ A).isSome
  | Λ, .mu _ T => SType.LabelsIn Λ T
  | Λ, .all _ S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .and S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T

/-- Every label of an optional type is in the table.  An empty slot has
none. -/
def SType.LabelsInOpt (Λ : LabelTable) : Option SType → Bool
  | none => true
  | some T => SType.LabelsIn Λ T

mutual
/-- Every label of a surface term is in the table at the right sort. -/
def STm.LabelsIn (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ T t => SType.LabelsInOpt Λ T && STm.LabelsIn Λ t
  | .obj _ T d => SType.LabelsInOpt Λ T && SDefs.LabelsIn Λ d
  | .app t u => STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .proj t a => STm.LabelsIn Λ t && (labelTrm? Λ a).isSome
  | .«let» _ ann t u => SType.LabelsInOpt Λ ann && STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .asc t T => STm.LabelsIn Λ t && SType.LabelsIn Λ T
  | .alias _ p u => SPath.LabelsIn Λ p && STm.LabelsIn Λ u
  | .bind _ _ t u => STm.LabelsIn Λ t && STm.LabelsIn Λ u
termination_by structural e
/-- Every label of surface definitions is in the table at the right sort. -/
def SDefs.LabelsIn (Λ : LabelTable) (d : SDefs) : Bool :=
  match d with
  | .nil => true
  | .typ ds A T => SDefs.LabelsIn Λ ds && (labelTyp? Λ A).isSome && SType.LabelsIn Λ T
  | .trm ds a T t =>
      SDefs.LabelsIn Λ ds && (labelTrm? Λ a).isSome && SType.LabelsInOpt Λ T && STm.LabelsIn Λ t
termination_by structural d
end

/-! ## Fields

pDOT's right side of a field is a path or a value (`PDot/Source/Syntax.lean:61-62`),
and `ty_def_path` declares a path field at its singleton only
(`PDot/Source/Typing.lean:69`).  So a field holds a path, a lambda or a
literal.  A written type sits on a lambda field, or on a path field `p` as
exactly `p.type`.  A written type on a literal field is refused. -/

/-- The shape of one field with written type `T` and right side `t`. -/
def fieldShape (T : Option SType) (t : STm) : Bool :=
  match T, t with
  | none, .lam .. => true
  | none, .obj .. => true
  | none, t => t.isPath
  | some _, .lam .. => true
  | some U, t =>
      match t.toPath? with
      | some p => decide (U = .sngl p)
      | none => false

mutual
/-- Every field of every literal of a surface term has a right shape. -/
def STm.FieldsOk (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ t => STm.FieldsOk t
  | .obj _ _ d => SDefs.FieldsOk d
  | .app t u => STm.FieldsOk t && STm.FieldsOk u
  | .proj t _ => STm.FieldsOk t
  | .«let» _ _ t u => STm.FieldsOk t && STm.FieldsOk u
  | .asc t _ => STm.FieldsOk t
  | .alias _ _ u => STm.FieldsOk u
  | .bind _ _ t u => STm.FieldsOk t && STm.FieldsOk u
termination_by structural e
/-- Every field of surface definitions, and of the literals inside them, has a
right shape. -/
def SDefs.FieldsOk (d : SDefs) : Bool :=
  match d with
  | .nil => true
  | .typ ds _ _ => SDefs.FieldsOk ds
  | .trm ds _ T t => SDefs.FieldsOk ds && STm.FieldsOk t && fieldShape T t
termination_by structural d
end

/-! ## Path operands

Under this side condition resolution inserts no `let`. -/

mutual
/-- Every operand of an application and every receiver of a projection is a
path, and no `bind` occurs. -/
def STm.PathOperands (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ t => STm.PathOperands t
  | .obj _ _ d => SDefs.PathOperands d
  | .app t u => t.isPath && u.isPath && STm.PathOperands t && STm.PathOperands u
  | .proj t _ => t.isPath && STm.PathOperands t
  | .«let» _ _ t u => STm.PathOperands t && STm.PathOperands u
  | .asc t _ => STm.PathOperands t
  | .alias _ _ u => STm.PathOperands u
  | .bind .. => false
termination_by structural e
/-- Every operand and receiver in surface definitions is a path, and no `bind`
occurs. -/
def SDefs.PathOperands (d : SDefs) : Bool :=
  match d with
  | .nil => true
  | .typ ds _ _ => SDefs.PathOperands ds
  | .trm ds _ _ t => SDefs.PathOperands ds && STm.PathOperands t
termination_by structural d
end

/-! ## The test helper

`#eval expect ...` fails the build on a false check.  It is for checks too slow
for the kernel.  The tests in this module are `by decide`. -/

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## Tests -/

/-- `ν(x : {A : ⊤..⊤} ∧ {a : x.A}) {type A = ⊤, a = x}`. -/
example : labelsOfProgram (.obj "x" (some (.and (.typ "A" .top .top) (.fld "a" (.sel (.var "x") "A"))))
    (.trm (.typ .nil "A" .top) "a" none (.var "x"))) = [("A", .typ 0), ("a", .trm 0)] := by decide

/-- A name at both sorts: `λ(y : {A : ⊤..⊤} ∧ {A : ⊤}). y`. -/
example : labelsOfProgram (.lam "y" (some (.and (.typ "A" .top .top) (.fld "A" .top))) (.var "y")) =
    [("A", .typ 0), ("A", .trm 0)] := by decide

example : labelTyp? (labelsOfProgram (.lam "y" (some (.and (.typ "A" .top .top) (.fld "A" .top)))
    (.var "y"))) "A" = some (.typ 0) := by decide

example : labelTrm? (labelsOfProgram (.lam "y" (some (.and (.typ "A" .top .top) (.fld "A" .top)))
    (.var "y"))) "A" = some (.trm 0) := by decide

/-- A capitalized term label: `ν(s) {Nil = λ(x : ⊤). x}`. -/
example : labelsOfProgram (.obj "s" none (.trm .nil "Nil" none (.lam "x" (some .top) (.var "x")))) =
    [("Nil", .trm 0)] := by decide

/-- Scoping, with `alias` binding its name in the body. -/
example : STm.Scoped [] (.var "y") = false := by decide

example : STm.Scoped [] (.lam "y" none (.var "y")) = true := by decide

example : STm.Scoped ["x"] (.alias "y" (.sel (.var "x") "a") (.var "y")) = true := by decide

example : STm.Scoped [] (.alias "y" (.var "x") (.var "y")) = false := by decide

/-- `ν(s) {a = x.b}`. -/
example : STm.FieldsOk (.obj "s" none (.trm .nil "a" none (.proj (.var "x") "b"))) = true := by decide

/-- `ν(s) {a : x.b.type = x.b}`. -/
example : STm.FieldsOk (.obj "s" none
    (.trm .nil "a" (some (.sngl (.sel (.var "x") "b"))) (.proj (.var "x") "b"))) = true := by decide

/-- `ν(s) {f : ⊤ = λ(y : ⊤). y}`. -/
example : STm.FieldsOk (.obj "s" none
    (.trm .nil "f" (some .top) (.lam "y" (some .top) (.var "y")))) = true := by decide

/-- `ν(s) {a = f x}`, an application in a field. -/
example : STm.FieldsOk (.obj "s" none (.trm .nil "a" none (.app (.var "f") (.var "x")))) = false := by
  decide

/-- `ν(s) {a : ⊤ = x.b}`, a path field at a type that is not its singleton. -/
example : STm.FieldsOk (.obj "s" none (.trm .nil "a" (some .top) (.proj (.var "x") "b"))) = false := by
  decide

/-- `ν(s) {a : μ(z. ⊤) = ν(z) {type A = ⊤}}`, a written type on a literal field. -/
example : STm.FieldsOk (.obj "s" none
    (.trm .nil "a" (some (.mu "z" .top)) (.obj "z" none (.typ .nil "A" .top)))) = false := by decide

/-- `f x.a`. -/
example : STm.PathOperands (.app (.var "f") (.proj (.var "x") "a")) = true := by decide

/-- `f (g x)`. -/
example : STm.PathOperands (.app (.var "f") (.app (.var "g") (.var "x"))) = false := by decide

/-- Any `bind`. -/
example : STm.PathOperands (.bind .widen "u" (.var "x") (.var "u")) = false := by decide

example : STm.PathOperands (.bind .unstable "u" (.var "x") (.var "u")) = false := by decide

end PDotFrontend
