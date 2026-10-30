import Coercions.Nominal.Source.Syntax

/-!
# Annotated and partial pDOT terms

`ATm` is the term of `Nominal.Source` with two things added.  A literal carries
its self type, and a `let` carries an optional type and a tag that says where
the `let` came from.  The typer reads an `ATm`.  `ATm.erase` drops the tags and
the `let` types and gives back a `Nominal.Source.Tm`.

The terms keep pDOT's shape (plan XI D-4).  A path is a term, an application
takes two paths, and a field of a literal holds a path, a lambda or a literal.
Definitions are a spine that grows on the right from `nil`, as pDOT's `Defs`.

`PTm` is an `ATm` whose slots may be empty: a lambda's domain, a literal's self
type, and the declared type of a lambda field.  Resolution returns a `PTm`, and
the elaborator fills its slots.  `PTm.full?` gives the `ATm` of a partial term
with every slot written.  `PTm.fills` says that an annotated term agrees with
every written slot of a partial term.

The tag is kept in `ATm`, unlike the paths front end
(`Paths/Frontend/Ann.lean:45-57`), since the Scala mode of the typer widens a
`let` by its origin (plan XI D-13).

Nothing here is part of the metatheory.  Every recursive definition is
structural.
-/

namespace NominalFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path)
open Nominal.Source (Ty Dec Tm Val Def Defs Rhs)

/-! ## Where a `let` comes from -/

/-- The origin of a `let`. -/
inductive LetTag where
  /-- A `let` the programmer wrote. -/
  | written
  /-- Inserted at the operand of an application that is not a path. -/
  | arg
  /-- Inserted at an operator or the receiver of a selection that is not a
  path, or made for an unstable prefix (`bind .unstable`). -/
  | recv
  /-- An ascription `(t : T)`, which is `let % : T = t in %`. -/
  | asc
  /-- A `val` whose type scalac widens (`bind .widen`). -/
  | widen
deriving DecidableEq, Repr

/-! ## The annotated terms -/

mutual
/-- Terms of pDOT with the self type of every literal and the origin of every
`let`. -/
inductive ATm : Sig → Type where
  /-- A path `p`. -/
  | path : Path s → ATm s
  /-- `p q`. -/
  | app : Path s → Path s → ATm s
  /-- `λ(z : S) t`. -/
  | lam : Ty s → ATm (s,x) → ATm s
  /-- `ν(z : T) ds`. -/
  | new : Ty (s,x) → ADefs (s,x) → ATm s
  /-- `let z (: W)? = t in u`, with its origin. -/
  | «let» : LetTag → Option (Ty s) → ATm s → ATm (s,x) → ATm s
/-- One definition of an annotated literal. -/
inductive ADef : Sig → Type where
  /-- `{A = T}`. -/
  | typ : Label → Ty s → ADef s
  /-- `{a = p}`. -/
  | path : Label → Path s → ADef s
  /-- `{a = λ(z : S) t}`. -/
  | lam : Label → Ty s → ATm (s,x) → ADef s
  /-- `{a = ν(z : T) ds}`. -/
  | new : Label → Ty (s,x) → ADefs (s,x) → ADef s
/-- The definitions of an annotated literal, a spine from `nil`. -/
inductive ADefs : Sig → Type where
  /-- No definition. -/
  | nil : ADefs s
  /-- The definitions so far, then one more. -/
  | cons : ADefs s → ADef s → ADefs s
end

deriving instance DecidableEq for ATm, ADef, ADefs

/-! ## Erasure

Erasure drops the tags and the `let` types and changes nothing else. -/

mutual
/-- The pDOT term of an annotated term. -/
def ATm.erase : {s : Sig} → ATm s → Tm s
  | _, .path p => .path p
  | _, .app p q => .app p q
  | _, .lam S t => .val (.lam S t.erase)
  | _, .new T ds => .val (.new T ds.erase)
  | _, .«let» _ _ t u => .lett t.erase u.erase
termination_by structural _ t => t
/-- The pDOT definition of an annotated definition. -/
def ADef.erase : {s : Sig} → ADef s → Def s
  | _, .typ A T => .typ A T
  | _, .path a p => .trm a (.defp p)
  | _, .lam a S t => .trm a (.defv (.lam S t.erase))
  | _, .new a T ds => .trm a (.defv (.new T ds.erase))
termination_by structural _ d => d
/-- The pDOT definitions of annotated definitions. -/
def ADefs.erase : {s : Sig} → ADefs s → Defs s
  | _, .nil => .nil
  | _, .cons ds d => .cons ds.erase d.erase
termination_by structural _ ds => ds
end

/-! ## The partial terms -/

mutual
/-- An `ATm` whose lambda domains and self types may be empty. -/
inductive PTm : Sig → Type where
  /-- A path `p`. -/
  | path : Path s → PTm s
  /-- `p q`. -/
  | app : Path s → Path s → PTm s
  /-- `λ(z : S) t` or `λz. t`. -/
  | lam : Option (Ty s) → PTm (s,x) → PTm s
  /-- `ν(z : T) ds` or `ν(z) ds`. -/
  | new : Option (Ty (s,x)) → PDefs (s,x) → PTm s
  /-- `let z (: W)? = t in u`, with its origin. -/
  | «let» : LetTag → Option (Ty s) → PTm s → PTm (s,x) → PTm s
/-- One definition of a partial literal. -/
inductive PDef : Sig → Type where
  /-- `{A = T}`. -/
  | typ : Label → Ty s → PDef s
  /-- `{a = p}`.  A written type on a path field is checked by `FieldsOk` and
  then dropped. -/
  | path : Label → Path s → PDef s
  /-- `{a (: U)? = λ(z (: S)?) t}`: the declared type, then the domain. -/
  | lam : Label → Option (Ty s) → Option (Ty s) → PTm (s,x) → PDef s
  /-- `{a = ν(z (: T)?) ds}`. -/
  | new : Label → Option (Ty (s,x)) → PDefs (s,x) → PDef s
/-- The definitions of a partial literal, a spine from `nil`. -/
inductive PDefs : Sig → Type where
  /-- No definition. -/
  | nil : PDefs s
  /-- The definitions so far, then one more. -/
  | cons : PDefs s → PDef s → PDefs s
end

deriving instance DecidableEq for PTm, PDef, PDefs

/-! ## The bridges to `ATm` -/

mutual
/-- The `ATm` a partial term stands for, when no slot is empty.  A written
declared type of a lambda field has no place in `ATm`, so it makes the term
partial.  The tag is kept. -/
def PTm.full? : {s : Sig} → PTm s → Option (ATm s)
  | _, .path p => some (.path p)
  | _, .app p q => some (.app p q)
  | _, .lam (some S) t => t.full?.map (.lam S)
  | _, .lam none _ => none
  | _, .new (some T) ds => ds.full?.map (.new T)
  | _, .new none _ => none
  | _, .«let» g ann t u =>
      match t.full?, u.full? with
      | some a, some b => some (.«let» g ann a b)
      | _, _ => none
termination_by structural _ t => t
/-- The `ADef` of one definition of a partial literal, when no slot is empty and no declared
type is written. -/
def PDef.full? : {s : Sig} → PDef s → Option (ADef s)
  | _, .typ A T => some (.typ A T)
  | _, .path a p => some (.path a p)
  | _, .lam a none (some S) t => t.full?.map (.lam a S)
  | _, .lam _ none none _ => none
  | _, .lam _ (some _) _ _ => none
  | _, .new a (some T) ds => ds.full?.map (.new a T)
  | _, .new _ none _ => none
termination_by structural _ d => d
/-- The `ADefs` of the definitions of a partial literal, when every one is full. -/
def PDefs.full? : {s : Sig} → PDefs s → Option (ADefs s)
  | _, .nil => some .nil
  | _, .cons ds d =>
      match ds.full?, d.full? with
      | some a, some b => some (.cons a b)
      | _, _ => none
termination_by structural _ ds => ds
end

mutual
/-- Every slot written, no declared field type, the tag kept. -/
def ATm.toI : {s : Sig} → ATm s → PTm s
  | _, .path p => .path p
  | _, .app p q => .app p q
  | _, .lam S t => .lam (some S) t.toI
  | _, .new T ds => .new (some T) ds.toI
  | _, .«let» g ann t u => .«let» g ann t.toI u.toI
termination_by structural _ t => t
/-- Every slot written, no declared field type. -/
def ADef.toI : {s : Sig} → ADef s → PDef s
  | _, .typ A T => .typ A T
  | _, .path a p => .path a p
  | _, .lam a S t => .lam a none (some S) t.toI
  | _, .new a T ds => .new a (some T) ds.toI
termination_by structural _ d => d
/-- Every slot written in every definition. -/
def ADefs.toI : {s : Sig} → ADefs s → PDefs s
  | _, .nil => .nil
  | _, .cons ds d => .cons ds.toI d.toI
termination_by structural _ ds => ds
end

/-! ## Inserted bindings -/

/-- One for a tag that resolution inserts, `arg` or `recv`, and zero for the
others. -/
def LetTag.counts : LetTag → Nat
  | .arg => 1
  | .recv => 1
  | .written => 0
  | .asc => 0
  | .widen => 0

mutual
/-- The number of `let`s tagged `arg` or `recv`, through every subterm. -/
def PTm.inserted : {s : Sig} → PTm s → Nat
  | _, .path _ => 0
  | _, .app _ _ => 0
  | _, .lam _ t => t.inserted
  | _, .new _ ds => ds.inserted
  | _, .«let» g _ t u => g.counts + t.inserted + u.inserted
termination_by structural _ t => t
/-- The number of inserted `let`s in a definition. -/
def PDef.inserted : {s : Sig} → PDef s → Nat
  | _, .typ _ _ => 0
  | _, .path _ _ => 0
  | _, .lam _ _ _ t => t.inserted
  | _, .new _ _ ds => ds.inserted
termination_by structural _ d => d
/-- The number of inserted `let`s in definitions. -/
def PDefs.inserted : {s : Sig} → PDefs s → Nat
  | _, .nil => 0
  | _, .cons ds d => ds.inserted + d.inserted
termination_by structural _ ds => ds
end

/-! ## Agreement with the written slots

The definitions of a literal are a spine from `nil`.  The self type of a
literal with one definition is the declaration of that definition, and a longer
spine `ds ▹ d` is declared by `T ∧ U`, with `T` for `ds` and `U` for `d`
(`e1_dottyDefs` with `e1_Td`, `PDot/Source/Programs.lean:122,134`).  So
`PDefs.fills` reads the self type from the right and has a base case for a
spine of one definition. -/

/-- The left part of an intersection.  Any other type gives `⊤`, which declares
nothing, so a declared type checked against it does not agree. -/
def andLeft {s : Sig} : Ty s → Ty s
  | .and T _ => T
  | _ => .top

/-- The right part of an intersection, and `⊤` for any other type. -/
def andRight {s : Sig} : Ty s → Ty s
  | .and _ T => T
  | _ => .top

/-- An optional slot agrees with a value: an empty slot always, a written one
when it is equal. -/
def slotAgrees {α : Type} [DecidableEq α] : Option α → α → Bool
  | none, _ => true
  | some a, b => decide (a = b)

/-- A written declared type of the field `a` agrees with the declaration
`{a : W}` at its place in the self type, and with nothing else.  An empty one
agrees with anything. -/
def declAgrees {s : Sig} (a : Label) : Option (Ty s) → Ty s → Bool
  | none, _ => true
  | some V, .rcd (.trm b W) => decide (a = b) && decide (V = W)
  | some _, _ => false

mutual
/-- The annotated term agrees with every written slot of the partial term, in
lockstep.  An empty slot agrees with anything.  The tags are equal. -/
def PTm.fills : {s : Sig} → PTm s → ATm s → Bool
  | _, .path p, .path q => decide (p = q)
  | _, .app p q, .app p' q' => decide (p = p') && decide (q = q')
  | _, .lam o t, .lam S a => slotAgrees o S && t.fills a
  | _, .new o ds, .new T ds' => slotAgrees o T && ds.fills T ds'
  | _, .«let» g o t u, .«let» g' o' a b =>
      decide (g = g') && decide (o = o') && t.fills a && u.fills b
  | _, _, _ => false
termination_by structural _ t => t
/-- One definition against the declaration at its place in the self type. -/
def PDef.fills : {s : Sig} → PDef s → Ty s → ADef s → Bool
  | _, .typ A T, _, .typ A' T' => decide (A = A') && decide (T = T')
  | _, .path a p, _, .path a' p' => decide (a = a') && decide (p = p')
  | _, .lam a o D t, U, .lam a' S b =>
      decide (a = a') && declAgrees a o U && slotAgrees D S && t.fills b
  | _, .new a o ds, _, .new a' T ds' =>
      decide (a = a') && slotAgrees o T && ds.fills T ds'
  | _, _, _, _ => false
termination_by structural _ d => d
/-- Definitions against the self type they were typed at, read from the right.
A spine of one definition is declared by the whole self type. -/
def PDefs.fills : {s : Sig} → PDefs s → Ty s → ADefs s → Bool
  | _, .nil, _, .nil => true
  | _, .cons .nil d, U, .cons .nil d' => d.fills U d'
  | _, .cons ds d, U, .cons ds' d' => ds.fills (andLeft U) ds' && d.fills (andRight U) d'
  | _, _, _, _ => false
termination_by structural _ ds => ds
end

/-! ## Tests -/

section Tests

private abbrev l0 : Label := .trm 0
private abbrev l1 : Label := .trm 1
private abbrev lA : Label := .typ 0

/-- The literal `ν(z : {a : z.type}) {a = z}`. -/
private def selfLit : ATm [] :=
  .new (.rcd (.trm l0 (.sngl (.var .here)))) (.cons .nil (.path l0 (.var .here)))

example : selfLit.erase =
    .val (.new (.rcd (.trm l0 (.sngl (.var .here)))) (.cons .nil (.trm l0 (.defp (.var .here))))) := by
  decide

example : selfLit.toI.full? = some selfLit := by decide

example : selfLit.toI.fills selfLit = true := by decide

/-- An empty self type makes the term partial, and agrees. -/
example : (PTm.new none (.cons .nil (.path l0 (.var .here))) : PTm []).full? = none := by decide

example : (PTm.new none (.cons .nil (.path l0 (.var .here))) : PTm []).fills selfLit = true := by
  decide

/-- An empty lambda domain makes the term partial. -/
example : (PTm.lam none (.path (.var .here)) : PTm []).full? = none := by decide

/-- A written declared type of a lambda field makes the term partial. -/
example : (PDef.lam l0 (some .top) (some .top) (.path (.var .here)) : PDef []).full? = none := by
  decide

/-- The tag is kept by `full?` and `toI`, and counted by `inserted`. -/
example : (PTm.«let» .arg none (.path (.var .here)) (.path (.var .here)) : PTm ([],x)).full? =
    some (.«let» .arg none (.path (.var .here)) (.path (.var .here))) := by decide

example : (PTm.«let» .recv none (.«let» .arg none (.path (.var .here)) (.path (.var .here)))
    (.«let» .written none (.path (.var .here)) (.path (.var .here))) : PTm ([],x)).inserted = 2 := by
  decide

/-- Different tags do not agree. -/
example : (PTm.«let» .arg none (.path (.var .here)) (.path (.var .here)) : PTm ([],x)).fills
    (.«let» .written none (.path (.var .here)) (.path (.var .here))) = false := by decide

/-- A one-definition spine: the declared type of the lambda field agrees with
the whole self type `{a : ∀(y : ⊤) ⊤}`. -/
example :
    let U : Ty ([],x) := .rcd (.trm l0 (.all .top .top))
    (PDefs.cons .nil (.lam l0 (some (.all .top .top)) (some .top) (.path (.var .here)))).fills U
      (.cons .nil (.lam l0 .top (.path (.var .here)))) = true := by
  decide

/-- A two-definition spine reads the self type from the right. -/
example :
    let U : Ty ([],x) := .and (.rcd (.typ lA .top .top)) (.rcd (.trm l1 (.all .top .top)))
    (PDefs.cons (.cons .nil (.typ lA .top))
        (.lam l1 (some (.all .top .top)) none (.path (.var .here)))).fills U
      (.cons (.cons .nil (.typ lA .top)) (.lam l1 .top (.path (.var .here)))) = true := by
  decide

/-- A declared type against a declaration at another label does not agree. -/
example :
    let U : Ty ([],x) := .rcd (.trm l1 (.all .top .top))
    (PDefs.cons .nil (.lam l0 (some (.all .top .top)) none (.path (.var .here)))).fills U
      (.cons .nil (.lam l0 .top (.path (.var .here)))) = false := by
  decide

end Tests

end NominalFrontend
