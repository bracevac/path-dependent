import Lean

/-!
# The surface syntax of the Oopsla16 front end

A first order, unindexed rendering of the paper's source language: types,
terms and member lists written with string names instead of de Bruijn
indices.  The notation layer turns concrete syntax into a value of one of
these inductives and nothing else, and every indexed construction happens
afterwards, as an ordinary Lean function over this syntax.

There is no `let`.  A call takes an arbitrary term on both sides, matching
the target calculus, and an ascription is the only purely front end
construct: it carries no counterpart in the version and erases away.

Labels are strings here and share one namespace, following the version's own
convention that a member's label is its position in the enclosing list,
counted from the end.  A `LabelTable` assigns a number to a name.  Building
one from a program, and deciding what every member of a literal needs to
satisfy against it, lives beyond this module.

`Scoped` and `LabelsIn` are the two decidable conditions that keep resolution
total, the counterpart of the vanilla front end's same named predicates.
`Positioned` is new: it holds when every member of every literal carries the
label of its own position, which a `LabelTable` built from the program
guarantees but an explicit table need not.

Every recursive definition here says `termination_by structural`, so the
kernel can reduce all of them and later facts about resolution become
`decide` or `rfl`.  A command checks that this held, rather than trusting it:
a definition of the namespace it is given compiled by well founded
recursion fails the build.

Nothing in this module is part of the metatheory.  No definition here lives
in the `Oopsla16` namespace.
-/

namespace Oopsla16Frontend

/-! ## The named abstract syntax -/

/-- Surface types. -/
inductive SType : Type where
  /-- `⊤`. -/
  | top
  /-- `⊥`. -/
  | bot
  /-- `{type L : S..U}`, a type member declaration. -/
  | typ (L : String) (S U : SType)
  /-- `{def m(x : S) : U}`, a method member declaration.  `U` may mention
  `x`. -/
  | fn (m : String) (x : String) (S U : SType)
  /-- `x.L`, a type selection on a variable. -/
  | sel (x : String) (L : String)
  /-- `μ(z. T)`, a recursive self type. -/
  | mu (z : String) (T : SType)
  /-- `S ∧ T`, an intersection. -/
  | and (S T : SType)
  /-- `S ∨ T`, a union. -/
  | or (S T : SType)
deriving DecidableEq, Repr, Inhabited

mutual
/-- Surface terms.  A call takes an arbitrary term as its receiver and its
argument, so elaboration into the target's monadic normal form happens
afterwards, not here. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `new {z ⇒ ds}` or `new {z : T ⇒ ds}`.  The self type is written only
  when the literal needs it to type its own members. -/
  | obj (z : String) (self : Option SType) (ds : SDms)
  /-- `t.m(u)`. -/
  | call (t : STm) (m : String) (u : STm)
  /-- `(t : T)`, front end only.  It erases to `t`. -/
  | asc (t : STm) (T : SType)
/-- A single member of a literal. -/
inductive SDm : Type where
  /-- `type L = T`. -/
  | typ (L : String) (T : SType)
  /-- `def m(x [: S]) [: U] = t`.  Both annotations are optional, Church and
  Curry style alike. -/
  | fn (m : String) (x : String) (S U : Option SType) (t : STm)
/-- A member list, newest member first. -/
inductive SDms : Type where
  | nil
  | cons (d : SDm) (ds : SDms)
end

deriving instance DecidableEq, Repr for STm, SDm, SDms

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDm := ⟨.typ "" .top⟩
instance : Inhabited SDms := ⟨.nil⟩

/-- The number of members, the label that would attach to one more member
consed onto the front. -/
def SDms.length (ds : SDms) : Nat :=
  match ds with
  | .nil => 0
  | .cons _ ds' => ds'.length + 1
termination_by structural ds

/-! ## The label table

One namespace, following the version: a member's label is the length of the
list of members below it.  Building a table from a program, and checking
that every member of the program agrees with it, is the resolver's job. -/

/-- A label table maps surface names to the version's positional labels,
first entry first. -/
abbrev LabelTable := List (String × Nat)

/-- The first entry for a name. -/
def labelOf? (Λ : LabelTable) (x : String) : Option Nat :=
  match Λ with
  | [] => none
  | (y, l) :: Λ' => if x = y then some l else labelOf? Λ' x
termination_by structural Λ

/-! ## Scoping

`Scoped Γ` holds when every free name of the phrase is in `Γ`, innermost
binder first.  The self binder of a literal scopes over its own written self
type, since the self type is checked against the very members it governs.  A
method's parameter scopes over its result type and its body, not over its
domain. -/

/-- Every free name of a surface type is in the list. -/
def SType.Scoped (Γ : List String) (T : SType) : Bool :=
  match T with
  | .top => true
  | .bot => true
  | .typ _ S U => SType.Scoped Γ S && SType.Scoped Γ U
  | .fn _ x S U => SType.Scoped Γ S && SType.Scoped (x :: Γ) U
  | .sel x _ => Γ.contains x
  | .mu z T' => SType.Scoped (z :: Γ) T'
  | .and S T' => SType.Scoped Γ S && SType.Scoped Γ T'
  | .or S T' => SType.Scoped Γ S && SType.Scoped Γ T'
termination_by structural T

mutual
/-- Every free name of a surface term is in the list. -/
def STm.Scoped (Γ : List String) (e : STm) : Bool :=
  match e with
  | .var x => Γ.contains x
  | .obj z self ds =>
      (match self with
        | none => true
        | some T => SType.Scoped (z :: Γ) T)
        && SDms.Scoped (z :: Γ) ds
  | .call t _ u => STm.Scoped Γ t && STm.Scoped Γ u
  | .asc t T => STm.Scoped Γ t && SType.Scoped Γ T
termination_by structural e
/-- Every free name of a surface member is in the list. -/
def SDm.Scoped (Γ : List String) (d : SDm) : Bool :=
  match d with
  | .typ _ T => SType.Scoped Γ T
  | .fn _ x S U t =>
      (match S with
        | none => true
        | some S' => SType.Scoped Γ S')
        && (match U with
          | none => true
          | some U' => SType.Scoped (x :: Γ) U')
        && STm.Scoped (x :: Γ) t
termination_by structural d
/-- Every free name of a surface member list is in the list. -/
def SDms.Scoped (Γ : List String) (ds : SDms) : Bool :=
  match ds with
  | .nil => true
  | .cons d ds' => SDm.Scoped Γ d && SDms.Scoped Γ ds'
termination_by structural ds
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table, at
some label.  The version has a single sort of label, so there is no further
test on which sort it is. -/

/-- Every label of a surface type is in the table. -/
def SType.LabelsIn (Λ : LabelTable) (T : SType) : Bool :=
  match T with
  | .top => true
  | .bot => true
  | .typ L S U => (labelOf? Λ L).isSome && SType.LabelsIn Λ S && SType.LabelsIn Λ U
  | .fn m _ S U => (labelOf? Λ m).isSome && SType.LabelsIn Λ S && SType.LabelsIn Λ U
  | .sel _ L => (labelOf? Λ L).isSome
  | .mu _ T' => SType.LabelsIn Λ T'
  | .and S T' => SType.LabelsIn Λ S && SType.LabelsIn Λ T'
  | .or S T' => SType.LabelsIn Λ S && SType.LabelsIn Λ T'
termination_by structural T

mutual
/-- Every label of a surface term is in the table. -/
def STm.LabelsIn (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .obj _ self ds =>
      (match self with
        | none => true
        | some T => SType.LabelsIn Λ T)
        && SDms.LabelsIn Λ ds
  | .call t m u => STm.LabelsIn Λ t && (labelOf? Λ m).isSome && STm.LabelsIn Λ u
  | .asc t T => STm.LabelsIn Λ t && SType.LabelsIn Λ T
termination_by structural e
/-- Every label of a surface member is in the table. -/
def SDm.LabelsIn (Λ : LabelTable) (d : SDm) : Bool :=
  match d with
  | .typ L T => (labelOf? Λ L).isSome && SType.LabelsIn Λ T
  | .fn m _ S U t =>
      (labelOf? Λ m).isSome
        && (match S with
          | none => true
          | some S' => SType.LabelsIn Λ S')
        && (match U with
          | none => true
          | some U' => SType.LabelsIn Λ U')
        && STm.LabelsIn Λ t
termination_by structural d
/-- Every label of a surface member list is in the table. -/
def SDms.LabelsIn (Λ : LabelTable) (ds : SDms) : Bool :=
  match ds with
  | .nil => true
  | .cons d ds' => SDm.LabelsIn Λ d && SDms.LabelsIn Λ ds'
termination_by structural ds
end

/-! ## Positions

A literal's members are consed newest first, and the version reads the label
of a member off the length of the list below it (`SDms.length` of its own
tail).  `Positioned Λ` holds when every member of every literal of the
phrase carries exactly that label in `Λ`.  A table built from the program
guarantees this by construction, but nothing stops an explicit table from
getting a position wrong, and resolution must reject that program rather
than silently mislabel a member. -/

mutual
/-- Every literal of a surface term has its members positioned. -/
def STm.Positioned (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .obj _ _ ds => SDms.Positioned Λ ds
  | .call t _ u => STm.Positioned Λ t && STm.Positioned Λ u
  | .asc t _ => STm.Positioned Λ t
termination_by structural e
/-- The body of a surface member, if any, has its own literals positioned.
A member's own label is checked where it is consed, in `SDms.Positioned`. -/
def SDm.Positioned (Λ : LabelTable) (d : SDm) : Bool :=
  match d with
  | .typ _ _ => true
  | .fn _ _ _ _ t => STm.Positioned Λ t
termination_by structural d
/-- Every member of the list carries the label of its position, and every
literal reachable from a member body is positioned in turn. -/
def SDms.Positioned (Λ : LabelTable) (ds : SDms) : Bool :=
  match ds with
  | .nil => true
  | .cons d ds' =>
      (match d with
        | .typ L _ => labelOf? Λ L == some ds'.length
        | .fn m _ _ _ _ => labelOf? Λ m == some ds'.length)
        && SDm.Positioned Λ d && SDms.Positioned Λ ds'
termination_by structural ds
end

/-! ## The test helper

The typer's search is not structural over the whole derivation, so tests
that touch it run compiled code through `#eval expect ...`, where a false
result throws and so fails the build.  The tests of this module reduce in
the kernel and stay `by rfl` and `by decide`. -/

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## The well foundedness check

A definition of a front end that falls back to well founded recursion
reduces in the elaborator but not in the kernel, which turns a `by decide`
into a compiled test without anyone asking for that.  This command catches
the fall back instead of letting it pass silently: it looks at every
definition whose name starts with the given namespace and fails when one of
them used a well foundedness combinator, of which Lean has more than one
depending on the recursion's shape. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by well
founded recursion, of any shape. -/
elab "#assert_no_wf " ns:ident : command => do
  let env ← getEnv
  let bad := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
        if ns.getId.isPrefixOf n && d.value.getUsedConstants.any (·.getRoot == `WellFounded) then
          acc.push n
        else acc
    | _ => acc
  unless bad.isEmpty do throwError "well-founded definitions: {bad}"

/-! ## Sanity

A small literal with a self type, checked structurally.  It is
`new {z : {type A : ⊥..⊤} ∧ {def f(x : ⊤) : z.A} ⇒ type A = ⊤  def f(x) = x}`,
with `A` at position 1 and `f` at position 0, the length of the tail below
each in the member list. -/

/-- The sample program's self type. -/
private def sampleSelf : SType :=
  .and (.typ "A" .bot .top) (.fn "f" "x" .top (.sel "z" "A"))

/-- The sample program's members, `A` then `f`. -/
private def sampleMembers : SDms :=
  .cons (.typ "A" .top) (.cons (.fn "f" "x" none none (.var "x")) .nil)

/-- The sample program. -/
private def sampleProgram : STm :=
  .obj "z" (some sampleSelf) sampleMembers

/-- The table the sample program needs: `A` at the length of its tail (one
member below it), `f` at the length of its own tail (none below it). -/
private def sampleLabels : LabelTable := [("A", 1), ("f", 0)]

example : labelOf? sampleLabels "A" = some 1 := by decide
example : labelOf? sampleLabels "f" = some 0 := by decide
example : labelOf? sampleLabels "g" = none := by decide

/-- The sample program is closed. -/
example : STm.Scoped [] sampleProgram = true := by decide

/-- A free name is out of scope. -/
example : STm.Scoped [] (.var "x") = false := by decide

/-- The self binder of a literal scopes over its own self type. -/
example : STm.Scoped [] (.obj "z" (some (.sel "z" "A")) (.cons (.typ "A" .top) .nil))
    = true := by decide

/-- A method's domain does not scope over its own parameter. -/
example : SDm.Scoped [] (.fn "f" "x" (some (.sel "x" "A")) none (.var "x")) = false := by decide

/-- The sample program's labels are all in its own table. -/
example : STm.LabelsIn sampleLabels sampleProgram = true := by decide

/-- An empty table labels nothing. -/
example : STm.LabelsIn [] sampleProgram = false := by decide

/-- The sample program's members carry the labels of their positions. -/
example : STm.Positioned sampleLabels sampleProgram = true := by decide

/-- Swapping the two labels breaks the positions. -/
example : STm.Positioned [("A", 0), ("f", 1)] sampleProgram = false := by decide

/-- A one member literal needs its member at position `0`. -/
example : SDms.Positioned [("f", 0)] (.cons (.fn "f" "x" none none (.var "x")) .nil)
    = true := by decide

end Oopsla16Frontend
