import Lean

/-!
# The surface syntax

Types, terms and member lists of the source language, written with string
names instead of de Bruijn indices.  The notation layer turns concrete syntax
into these inductives, and the resolver (`Resolve.lean`) turns them into
indexed syntax.

There is no `let`.  A call takes an arbitrary term on both sides.  An
ascription `(t : T)` has no counterpart in the calculus and erases away.

Labels are strings in one namespace.  A member's label is its position in the
enclosing list, counted from the end.  A `LabelTable` assigns a number to each
name.

Three decidable predicates say when resolution succeeds.  `Scoped` holds when
every free name is bound.  `LabelsIn` holds when every label name is in the
table.  `Positioned` holds when every member of every literal carries the label
of its own position, which a table built from the program guarantees and an
explicit table may not.

Five erasures drop written annotations from a surface program, as their
namesakes in `Ann.lean` drop them from a resolved one.  When the written
program resolves, each erasure of it resolves to the erasure of its resolution
(`Resolve.lean`).  So an erased source written in the notation stands for the
erased program.

Every recursive definition is structural, so the kernel reduces it.
`#assert_no_wf` checks this for a namespace.  Nothing here is part of the
metatheory.
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
/-- Surface terms.  A call takes arbitrary terms as receiver and argument. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `new {z ⇒ ds}` or `new {z : T ⇒ ds}`.  The self type is optional.
  Without one, a literal with a Curry style method is not one the typer takes
  as it is (`ATm.landed`), and a fill writes the self type in (`ATm.fills`). -/
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

/-- The number of members, the label of a member consed onto the front. -/
def SDms.length (ds : SDms) : Nat :=
  match ds with
  | .nil => 0
  | .cons _ ds' => ds'.length + 1
termination_by structural ds

/-! ## The label table

A member's label is the length of the list of members below it.  Building a
table from a program is the resolver's job. -/

/-- A label table maps surface names to positional labels. -/
abbrev LabelTable := List (String × Nat)

/-- The first entry for a name. -/
def labelOf? (Λ : LabelTable) (x : String) : Option Nat :=
  match Λ with
  | [] => none
  | (y, l) :: Λ' => if x = y then some l else labelOf? Λ' x
termination_by structural Λ

/-! ## Scoping

`Scoped Γ` holds when every free name of the phrase is in `Γ`, innermost
binder first.  A literal's self binder scopes over its written self type and
its members.  A method's parameter scopes over its result type and body, not
over its domain. -/

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

`LabelsIn Λ` holds when every name in label position is in the table. -/

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

`Positioned Λ` holds when every member of every literal carries in `Λ` the
length of the list below it (`SDms.length` of its tail).  Resolution rejects a
program that fails it, and never mislabels a member. -/

mutual
/-- Every literal of a surface term has its members positioned. -/
def STm.Positioned (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .obj _ _ ds => SDms.Positioned Λ ds
  | .call t _ u => STm.Positioned Λ t && STm.Positioned Λ u
  | .asc t _ => STm.Positioned Λ t
termination_by structural e
/-- The literals in a member's body are positioned.  The member's own label is
checked in `SDms.Positioned`. -/
def SDm.Positioned (Λ : LabelTable) (d : SDm) : Bool :=
  match d with
  | .typ _ _ => true
  | .fn _ _ _ _ t => STm.Positioned Λ t
termination_by structural d
/-- Every member carries the label of its position, and so does every literal
in a member body. -/
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

/-! ## Erasures

`eraseSelf` drops every self type, `eraseRes` every method result type,
`eraseParam` every method parameter type, and `eraseArgSelf` the self type of
every literal that is a call argument.  `scalaForm` is the program a Scala
programmer writes: no self type, no result type, and every parameter type
written.  A parameter that the program left to the written self type takes the
domain that self type declares at the member's position.  The self type is
read in lockstep with the members, one conjunct of a right nested
intersection per member, as `selfOf?` builds it. -/

mutual
/-- Drop every self type of a surface term. -/
def STm.eraseSelf (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .obj z _ ds => .obj z none ds.eraseSelf
  | .call t m u => .call t.eraseSelf m u.eraseSelf
  | .asc t T => .asc t.eraseSelf T
termination_by structural e
/-- Drop every self type inside a surface member. -/
def SDm.eraseSelf (d : SDm) : SDm :=
  match d with
  | .typ L T => .typ L T
  | .fn m x S U t => .fn m x S U t.eraseSelf
termination_by structural d
/-- Drop every self type inside a surface member list. -/
def SDms.eraseSelf (ds : SDms) : SDms :=
  match ds with
  | .nil => .nil
  | .cons d ds' => .cons d.eraseSelf ds'.eraseSelf
termination_by structural ds
end

mutual
/-- Drop every method result type of a surface term. -/
def STm.eraseRes (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .obj z self ds => .obj z self ds.eraseRes
  | .call t m u => .call t.eraseRes m u.eraseRes
  | .asc t T => .asc t.eraseRes T
termination_by structural e
/-- Drop the result type of a surface method, and every one in its body. -/
def SDm.eraseRes (d : SDm) : SDm :=
  match d with
  | .typ L T => .typ L T
  | .fn m x S _ t => .fn m x S none t.eraseRes
termination_by structural d
/-- Drop every method result type inside a surface member list. -/
def SDms.eraseRes (ds : SDms) : SDms :=
  match ds with
  | .nil => .nil
  | .cons d ds' => .cons d.eraseRes ds'.eraseRes
termination_by structural ds
end

mutual
/-- Drop every method parameter type of a surface term. -/
def STm.eraseParam (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .obj z self ds => .obj z self ds.eraseParam
  | .call t m u => .call t.eraseParam m u.eraseParam
  | .asc t T => .asc t.eraseParam T
termination_by structural e
/-- Drop the parameter type of a surface method, and every one in its body. -/
def SDm.eraseParam (d : SDm) : SDm :=
  match d with
  | .typ L T => .typ L T
  | .fn m x _ U t => .fn m x none U t.eraseParam
termination_by structural d
/-- Drop every method parameter type inside a surface member list. -/
def SDms.eraseParam (ds : SDms) : SDms :=
  match ds with
  | .nil => .nil
  | .cons d ds' => .cons d.eraseParam ds'.eraseParam
termination_by structural ds
end

mutual
/-- Drop the self type of every literal that is a call argument.  `arg` says
whether `e` itself is the argument of a call. -/
def STm.eraseArgSelfAt (arg : Bool) (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .obj z self ds => .obj z (if arg then none else self) ds.eraseArgSelf
  | .call t m u => .call (t.eraseArgSelfAt false) m (u.eraseArgSelfAt true)
  | .asc t T => .asc (t.eraseArgSelfAt false) T
termination_by structural e
/-- Drop the self type of every literal that is a call argument inside a
surface member. -/
def SDm.eraseArgSelf (d : SDm) : SDm :=
  match d with
  | .typ L T => .typ L T
  | .fn m x S U t => .fn m x S U (t.eraseArgSelfAt false)
termination_by structural d
/-- Drop the self type of every literal that is a call argument inside a
surface member list. -/
def SDms.eraseArgSelf (ds : SDms) : SDms :=
  match ds with
  | .nil => .nil
  | .cons d ds' => .cons d.eraseArgSelf ds'.eraseArgSelf
termination_by structural ds
end

/-- Drop the self type of every literal that is a call argument. -/
def STm.eraseArgSelf (e : STm) : STm := e.eraseArgSelfAt false

mutual
/-- The surface program a Scala programmer writes. -/
def STm.scalaForm (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .obj z self ds => .obj z none (ds.scalaForm self)
  | .call t m u => .call t.scalaForm m u.scalaForm
  | .asc t T => .asc t.scalaForm T
termination_by structural e
/-- A surface member in the Scala form, given the conjunct the written self
type has at its position. -/
def SDm.scalaForm (d : SDm) (H : Option SType) : SDm :=
  match d, H with
  | .fn m x S _ t, some (.fn _ _ S' _) => .fn m x (S.or (some S')) none t.scalaForm
  | .fn m x S _ t, _ => .fn m x S none t.scalaForm
  | .typ L T, _ => .typ L T
termination_by structural d
/-- A surface member list in the Scala form, read in lockstep with the written
self type. -/
def SDms.scalaForm (ds : SDms) (T : Option SType) : SDms :=
  match ds, T with
  | .nil, _ => .nil
  | .cons d ds', some (.and H TS) => .cons (d.scalaForm (some H)) (ds'.scalaForm (some TS))
  | .cons d ds', _ => .cons (d.scalaForm none) (ds'.scalaForm none)
termination_by structural ds
end

/-! ## The test helper

The typer's search is not structural, so tests that use it run compiled code
through `#eval expect ...`. -/

/-- Throw, so that an `#eval` fails the build, when a check is false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## The well foundedness check

A definition compiled by well founded recursion does not reduce in the
kernel, so `by decide` on it would fail. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` uses well founded
recursion. -/
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

A literal with a self type:
`new {z : {type A : ⊥..⊤} ∧ {def f(x : ⊤) : z.A} ⇒ type A = ⊤  def f(x) = x}`,
with `A` at position 1 and `f` at position 0. -/

/-- The sample program's self type. -/
private def sampleSelf : SType :=
  .and (.typ "A" .bot .top) (.fn "f" "x" .top (.sel "z" "A"))

/-- The sample program's members, `A` then `f`. -/
private def sampleMembers : SDms :=
  .cons (.typ "A" .top) (.cons (.fn "f" "x" none none (.var "x")) .nil)

/-- The sample program. -/
private def sampleProgram : STm :=
  .obj "z" (some sampleSelf) sampleMembers

/-- The table the sample program needs. -/
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

/-! ### Erasures

`new {z : {def f(x : ⊤) : ⊤} ∧ ⊤ ⇒ def f(x) = x}`, a Curry style method under
a written self type. -/

/-- The Curry style literal. -/
private def curryLiteral : STm :=
  .obj "z" (some (.and (.fn "f" "x" .top .top) .top)) (.cons (.fn "f" "x" none none (.var "x")) .nil)

/-- The `S` erasure leaves the method with no annotation at all. -/
example : curryLiteral.eraseSelf = .obj "z" none (.cons (.fn "f" "x" none none (.var "x")) .nil) := by
  decide

/-- The Scala form takes the parameter type from the self type. -/
example : curryLiteral.scalaForm
    = .obj "z" none (.cons (.fn "f" "x" (some .top) none (.var "x")) .nil) := by
  decide

/-- A written parameter type stays, and the result type goes. -/
example : (STm.obj "z" (some (.and (.fn "f" "x" .top .top) .top))
      (.cons (.fn "f" "x" (some .bot) (some .top) (.var "x")) .nil)).scalaForm
    = .obj "z" none (.cons (.fn "f" "x" (some .bot) none (.var "x")) .nil) := by
  decide

/-- The sample self type ends in a method, not in `⊤`, so the lockstep reading
reaches `f` at no conjunct and gives it no parameter type. -/
example : sampleProgram.scalaForm = .obj "z" none sampleMembers := by decide

/-- Only the literal that is the argument of a call loses its self type. -/
example : (STm.call curryLiteral "f" curryLiteral).eraseArgSelf
    = .call curryLiteral "f" curryLiteral.eraseSelf := by
  decide

/-- An ascribed argument is not itself the argument, so it keeps its self
type. -/
example : (STm.call (.var "y") "f" (.asc curryLiteral .top)).eraseArgSelf
    = .call (.var "y") "f" (.asc curryLiteral .top) := by
  decide

/-- `R` and `P` drop the two annotations of a method one at a time. -/
example : (SDm.fn "f" "x" (some .bot) (some .top) (.var "x")).eraseRes
      = .fn "f" "x" (some .bot) none (.var "x") ∧
    (SDm.fn "f" "x" (some .bot) (some .top) (.var "x")).eraseParam
      = .fn "f" "x" none (some .top) (.var "x") := by
  decide

end Oopsla16Frontend
