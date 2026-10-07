import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Frontend.Notation
import Coercions.Oopsla16.Examples
import Coercions.FCdotR.CheckerExamples

/-!
# Name resolution and label tables

Three structural functions take a surface phrase to the annotated de Bruijn
syntax of `Ann.lean`, and they are the only place where a surface name
becomes an index or a label becomes a position.

Name environments are innermost binder first, one name per binder of the
signature, so shadowing is innermost wins by construction.  User names are
data in a `NameEnv`, never Lean identifiers, so Lean's macro hygiene never
touches them.

The resolver inserts no binder.  A call of the version takes arbitrary terms
on both sides, so a surface call resolves to a call, and the target's own
elaboration does the normalisation it needs.

Scopes.  A literal `new {z ⇒ ds}` resolves its members, and its written self
type, under `z`.  A method `def m(x : S) : U = t` resolves `S` at the member's
scope and `U` and `t` under `x`.  A method type `{def m(x : S) : U}` resolves
`U` under `x`, and `μ(z. T)` resolves `T` under `z`.

Labels.  The version's label of a member is the length of the list below it.
So a member list resolves only when every member's name has that position in
the table, and a mismatch is a resolution failure rather than a silently
renumbered member.  `labelsOfProgram` builds a table from a program: the
explicit entries first, then the position of every member name of every
literal, in program order.  It fails when one name is forced to two
positions.  A name that labels no literal member, for instance a type member
of a parameter's type, needs an explicit entry.

What is stated below is totality on scoped, labelled, positioned phrases, and
that a table built by `labelsOfProgram` positions its program.  The examples
at the end resolve the version's own programs and compare their erasures with
the version's terms.

This module imports `Notation.lean` for the examples, and Lean's token table
is global.  So `type`, `def`, `new` and `μ` are keywords here and none of them
can be a local name.

Nothing in this module is part of the metatheory.  No definition here lives
in the `Oopsla16` or `FCdot` namespaces.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Lb Ty Tm Dm Dms)

/-! ## Name environments -/

/-- One surface name per binder of the signature, innermost binder first. -/
inductive NameEnv : Sig → Type where
  /-- The empty environment. -/
  | nil : NameEnv []
  /-- One more binder, with its surface name. -/
  | cons : NameEnv s → String → NameEnv (s,x)

/-- The index of a name, innermost binder wins. -/
def NameEnv.find? {s : Sig} (ν : NameEnv s) (z : String) : Option (BVar s .var) :=
  match ν with
  | .nil => none
  | .cons ν' y => if z = y then some .here else (ν'.find? z).map .there
termination_by structural ν

/-- The names of the environment, innermost binder first. -/
def NameEnv.names {s : Sig} (ν : NameEnv s) : List String :=
  match ν with
  | .nil => []
  | .cons ν' y => y :: ν'.names
termination_by structural ν

/-- A name in the environment has an index. -/
theorem NameEnv.find?_isSome : ∀ {s : Sig} (ν : NameEnv s) (z : String),
    ν.names.contains z = true → (ν.find? z).isSome = true
  | _, .nil, _, h => by simp [NameEnv.names] at h
  | _, .cons ν' y, z, h => by
      by_cases hzy : z = y
      · simp [NameEnv.find?, hzy]
      · have hy : (z == y) = false := by simp [hzy]
        have h' : ν'.names.contains z = true := by
          simp only [NameEnv.names, List.contains_cons, hy, Bool.false_or] at h
          exact h
        obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.find?_isSome ν' z h')
        simp [NameEnv.find?, hzy, hi]

/-! ## The resolvers

Each is structural on the surface phrase.  The order in which a clause asks
for its parts matches the order of the conjuncts of `Scoped`, `LabelsIn` and
`Positioned`, so the totality proofs take the conjunctions apart in the order
the `Option`s are produced. -/

/-- Resolve a surface type. -/
def resolveTy {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (T : SType) : Option (Ty [] s) :=
  match T with
  | .top => some .TTop
  | .bot => some .TBot
  | .typ L S U => do
      let l ← labelOf? Λ L
      let S' ← resolveTy Λ ν S
      let U' ← resolveTy Λ ν U
      pure (.TTyp l S' U')
  | .fn m x S U => do
      let l ← labelOf? Λ m
      let S' ← resolveTy Λ ν S
      let U' ← resolveTy Λ (ν.cons x) U
      pure (.TFun l S' U')
  | .sel x L => do
      let i ← ν.find? x
      let l ← labelOf? Λ L
      pure (.TSel (.abs i) l)
  | .mu z T' => do
      let T'' ← resolveTy Λ (ν.cons z) T'
      pure (.TBind T'')
  | .and S T' => do
      let S' ← resolveTy Λ ν S
      let T'' ← resolveTy Λ ν T'
      pure (.TAnd S' T'')
  | .or S T' => do
      let S' ← resolveTy Λ ν S
      let T'' ← resolveTy Λ ν T'
      pure (.TOr S' T'')
termination_by structural T

/-- Resolve an optional annotation.  A missing one stays missing. -/
def resolveTyOpt {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (T : Option SType) :
    Option (Option (Ty [] s)) :=
  match T with
  | none => some none
  | some T' => (resolveTy Λ ν T').map some

/-- The name a member defines. -/
def SDm.name (d : SDm) : String :=
  match d with
  | .typ L _ => L
  | .fn m _ _ _ _ => m

mutual
/-- Resolve a surface term. -/
def resolveTm {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (e : STm) : Option (ATm s) :=
  match e with
  | .var x => do
      let i ← ν.find? x
      pure (.var i)
  | .obj z self ds => do
      let self' ← resolveTyOpt Λ (ν.cons z) self
      let ds' ← resolveDms Λ (ν.cons z) ds
      pure (.obj self' ds')
  | .call t m u => do
      let t' ← resolveTm Λ ν t
      let l ← labelOf? Λ m
      let u' ← resolveTm Λ ν u
      pure (.app t' l u')
  | .asc t T => do
      let t' ← resolveTm Λ ν t
      let T' ← resolveTy Λ ν T
      pure (.asc t' T')
termination_by structural e
/-- Resolve a surface member.  Its label is checked by the list that holds
it, where the position is known. -/
def resolveDm {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (d : SDm) : Option (ADm s) :=
  match d with
  | .typ _ T => do
      let T' ← resolveTy Λ ν T
      pure (.dty T')
  | .fn _ x S U t => do
      let S' ← resolveTyOpt Λ ν S
      let U' ← resolveTyOpt Λ (ν.cons x) U
      let t' ← resolveTm Λ (ν.cons x) t
      pure (.dfun S' U' t')
termination_by structural d
/-- Resolve a surface member list.  Every member's name must have, in the
table, the label of its position, the length of the list below it. -/
def resolveDms {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (ds : SDms) : Option (ADms s) :=
  match ds with
  | .nil => some .dnil
  | .cons d ds' =>
      if labelOf? Λ d.name == some ds'.length then do
        let d' ← resolveDm Λ ν d
        let ds'' ← resolveDms Λ ν ds'
        pure (.dcons d' ds'')
      else none
termination_by structural ds
end

/-- Resolve a surface term in a given environment, for a program that is
open in the variables the environment names. -/
def resolveIn {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (e : STm) : Option (ATm s) :=
  resolveTm Λ ν e

/-- Resolve a closed surface program. -/
def resolve (Λ : LabelTable) (e : STm) : Option (ATm []) := resolveIn Λ .nil e

/-! ## Totality

Resolution succeeds on a phrase whose free names are all in the environment,
whose labels are all in the table, and whose literals' members are all
positioned.  The proofs follow the resolvers clause by clause. -/

/-- A `some` from an `isSome`, the step every clause below takes. -/
private theorem some_of_isSome {α : Type} {o : Option α} (h : o.isSome = true) :
    ∃ a, o = some a :=
  Option.isSome_iff_exists.mp h

/-- A label in the table has a value. -/
private theorem label_of_isSome {Λ : LabelTable} {L : String}
    (h : (labelOf? Λ L).isSome = true) : ∃ l, labelOf? Λ L = some l :=
  some_of_isSome h

/-- A scoped, labelled surface type resolves. -/
theorem resolveTy_isSome : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (ν : NameEnv s),
    SType.Scoped ν.names T = true → SType.LabelsIn Λ T = true →
    (resolveTy Λ ν T).isSome = true
  | .top, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _ => rfl
  | .typ L S U, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hL⟩ := label_of_isSome hl.1.1
      obtain ⟨S', hS⟩ := some_of_isSome (resolveTy_isSome S Λ ν hs.1 hl.1.2)
      obtain ⟨U', hU⟩ := some_of_isSome (resolveTy_isSome U Λ ν hs.2 hl.2)
      simp [resolveTy, hL, hS, hU]
  | .fn m x S U, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hm⟩ := label_of_isSome hl.1.1
      obtain ⟨S', hS⟩ := some_of_isSome (resolveTy_isSome S Λ ν hs.1 hl.1.2)
      obtain ⟨U', hU⟩ := some_of_isSome (resolveTy_isSome U Λ (ν.cons x) hs.2 hl.2)
      simp [resolveTy, hm, hS, hU]
  | .sel x L, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      obtain ⟨i, hx⟩ := some_of_isSome (NameEnv.find?_isSome ν x hs)
      obtain ⟨l, hL⟩ := label_of_isSome hl
      simp [resolveTy, hx, hL]
  | .mu z T, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ (ν.cons z) hs hl)
      simp [resolveTy, hT]
  | .and S T, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨S', hS⟩ := some_of_isSome (resolveTy_isSome S Λ ν hs.1 hl.1)
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ ν hs.2 hl.2)
      simp [resolveTy, hS, hT]
  | .or S T, _, Λ, ν, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨S', hS⟩ := some_of_isSome (resolveTy_isSome S Λ ν hs.1 hl.1)
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ ν hs.2 hl.2)
      simp [resolveTy, hS, hT]

/-- An optional annotation resolves when it is absent, or present and
resolvable. -/
theorem resolveTyOpt_isSome {s : Sig} (Λ : LabelTable) (ν : NameEnv s) :
    ∀ (T : Option SType),
    (match T with | none => true | some T' => SType.Scoped ν.names T') = true →
    (match T with | none => true | some T' => SType.LabelsIn Λ T') = true →
    (resolveTyOpt Λ ν T).isSome = true
  | none, _, _ => rfl
  | some T, hs, hl => by
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ ν hs hl)
      simp [resolveTyOpt, hT]

mutual
/-- A scoped, labelled, positioned surface term resolves. -/
theorem resolveTm_isSome : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s),
    STm.Scoped ν.names e = true → STm.LabelsIn Λ e = true → STm.Positioned Λ e = true →
    (resolveTm Λ ν e).isSome = true
  | .var x, _, Λ, ν, hs, _, _ => by
      simp only [STm.Scoped] at hs
      obtain ⟨i, hx⟩ := some_of_isSome (NameEnv.find?_isSome ν x hs)
      simp [resolveTm, hx]
  | .obj z self ds, _, Λ, ν, hs, hl, hp => by
      simp only [STm.Scoped, STm.LabelsIn, STm.Positioned, Bool.and_eq_true] at hs hl hp
      obtain ⟨self', hT⟩ := some_of_isSome (resolveTyOpt_isSome Λ (ν.cons z) self hs.1 hl.1)
      obtain ⟨ds', hd⟩ := some_of_isSome (resolveDms_isSome ds Λ (ν.cons z) hs.2 hl.2 hp)
      simp [resolveTm, hT, hd]
  | .call t m u, _, Λ, ν, hs, hl, hp => by
      simp only [STm.Scoped, STm.LabelsIn, STm.Positioned, Bool.and_eq_true] at hs hl hp
      obtain ⟨t', ht⟩ := some_of_isSome (resolveTm_isSome t Λ ν hs.1 hl.1.1 hp.1)
      obtain ⟨l, hm⟩ := label_of_isSome hl.1.2
      obtain ⟨u', hu⟩ := some_of_isSome (resolveTm_isSome u Λ ν hs.2 hl.2 hp.2)
      simp [resolveTm, ht, hm, hu]
  | .asc t T, _, Λ, ν, hs, hl, hp => by
      simp only [STm.Scoped, STm.LabelsIn, STm.Positioned, Bool.and_eq_true] at hs hl hp
      obtain ⟨t', ht⟩ := some_of_isSome (resolveTm_isSome t Λ ν hs.1 hl.1 hp)
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ ν hs.2 hl.2)
      simp [resolveTm, ht, hT]
/-- A scoped, labelled surface member resolves, whatever its position. -/
theorem resolveDm_isSome : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s),
    SDm.Scoped ν.names d = true → SDm.LabelsIn Λ d = true → SDm.Positioned Λ d = true →
    (resolveDm Λ ν d).isSome = true
  | .typ L T, _, Λ, ν, hs, hl, _ => by
      simp only [SDm.Scoped, SDm.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨T', hT⟩ := some_of_isSome (resolveTy_isSome T Λ ν hs hl.2)
      simp [resolveDm, hT]
  | .fn m x S U t, _, Λ, ν, hs, hl, hp => by
      simp only [SDm.Scoped, SDm.LabelsIn, SDm.Positioned, Bool.and_eq_true] at hs hl hp
      obtain ⟨S', hS⟩ := some_of_isSome (resolveTyOpt_isSome Λ ν S hs.1.1 hl.1.1.2)
      obtain ⟨U', hU⟩ := some_of_isSome (resolveTyOpt_isSome Λ (ν.cons x) U hs.1.2 hl.1.2)
      obtain ⟨t', ht⟩ := some_of_isSome (resolveTm_isSome t Λ (ν.cons x) hs.2 hl.2 hp)
      simp [resolveDm, hS, hU, ht]
/-- A scoped, labelled, positioned member list resolves. -/
theorem resolveDms_isSome : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s),
    SDms.Scoped ν.names ds = true → SDms.LabelsIn Λ ds = true → SDms.Positioned Λ ds = true →
    (resolveDms Λ ν ds).isSome = true
  | .nil, _, _, _, _, _, _ => rfl
  | .cons d ds', _, Λ, ν, hs, hl, hp => by
      simp only [SDms.Scoped, SDms.LabelsIn, SDms.Positioned, Bool.and_eq_true] at hs hl hp
      have hpos : (labelOf? Λ d.name == some ds'.length) = true := by
        cases d <;> exact hp.1.1
      obtain ⟨d', hd⟩ := some_of_isSome (resolveDm_isSome d Λ ν hs.1 hl.1 hp.1.2)
      obtain ⟨ds'', hds⟩ := some_of_isSome (resolveDms_isSome ds' Λ ν hs.2 hl.2 hp.2)
      simp [resolveDms, hpos, hd, hds]
end

/-! ## Label tables from a program

`collectLabels` walks every literal of a phrase in program order and gives
each member name not yet in the table the position it has where it first
occurs.  `labelsOfProgram` starts from the explicit entries, collects, and
accepts the table when it positions every literal of the program.  A name
that two literals put at two positions keeps the first and then fails the
check at the second, so the program has no table. -/

/-- Add a name at a position, unless the table already has the name. -/
def addLabel (Λ : LabelTable) (x : String) (p : Nat) : LabelTable :=
  match labelOf? Λ x with
  | some _ => Λ
  | none => Λ ++ [(x, p)]

mutual
/-- The member names of every literal of a term, at their positions. -/
def STm.collectLabels (Λ : LabelTable) (e : STm) : LabelTable :=
  match e with
  | .var _ => Λ
  | .obj _ _ ds => SDms.collectLabels Λ ds
  | .call t _ u => STm.collectLabels (STm.collectLabels Λ t) u
  | .asc t _ => STm.collectLabels Λ t
termination_by structural e
/-- The member names of every literal in a member's body. -/
def SDm.collectLabels (Λ : LabelTable) (d : SDm) : LabelTable :=
  match d with
  | .typ _ _ => Λ
  | .fn _ _ _ _ t => STm.collectLabels Λ t
termination_by structural d
/-- The member names of a list, each at its position, then those of every
literal below. -/
def SDms.collectLabels (Λ : LabelTable) (ds : SDms) : LabelTable :=
  match ds with
  | .nil => Λ
  | .cons d ds' => SDms.collectLabels (SDm.collectLabels (addLabel Λ d.name ds'.length) d) ds'
termination_by structural ds
end

/-- The label table of a program: the explicit entries first, then every
member name at its position.  `none` when a name is forced to two positions,
or an explicit entry contradicts a position. -/
def labelsOfProgram (explicit : LabelTable) (e : STm) : Option LabelTable :=
  let Λ := STm.collectLabels explicit e
  if STm.Positioned Λ e then some Λ else none

/-- A table built from a program positions that program, so the program meets
the third premise of `resolveTm_isSome`. -/
theorem labelsOfProgram_positioned {Λ₀ Λ : LabelTable} {e : STm}
    (h : labelsOfProgram Λ₀ e = some Λ) : STm.Positioned Λ e = true := by
  dsimp only [labelsOfProgram] at h
  split at h
  · cases h; assumption
  · cases h

/-! ### The explicit entries win

The table only grows at its end, so an entry is never overwritten.  In
particular an explicit entry is the entry of the result. -/

/-- One table extends another when every name of the first keeps its label. -/
def Extends (Λ Λ' : LabelTable) : Prop :=
  ∀ x l, labelOf? Λ x = some l → labelOf? Λ' x = some l

theorem Extends.refl (Λ : LabelTable) : Extends Λ Λ := fun _ _ h => h

theorem Extends.trans {Λ₁ Λ₂ Λ₃ : LabelTable} (h₁ : Extends Λ₁ Λ₂) (h₂ : Extends Λ₂ Λ₃) :
    Extends Λ₁ Λ₃ := fun x l h => h₂ x l (h₁ x l h)

/-- Appending keeps every entry already found. -/
theorem labelOf?_append_of_some : ∀ (Λ Λ' : LabelTable) (x : String) (l : Nat),
    labelOf? Λ x = some l → labelOf? (Λ ++ Λ') x = some l
  | [], _, _, _, h => by simp [labelOf?] at h
  | (y, k) :: Λ, Λ', x, l, h => by
      by_cases hxy : x = y
      · simp only [labelOf?, List.cons_append, hxy, if_true] at h ⊢
        exact h
      · simp only [labelOf?, List.cons_append, hxy, if_false] at h ⊢
        exact labelOf?_append_of_some Λ Λ' x l h

/-- Adding a name keeps every entry. -/
theorem addLabel_extends (Λ : LabelTable) (x : String) (p : Nat) :
    Extends Λ (addLabel Λ x p) := by
  intro y l h
  unfold addLabel
  split
  · exact h
  · exact labelOf?_append_of_some Λ _ y l h

mutual
/-- Collecting the labels of a term keeps every entry. -/
theorem STm.collectLabels_extends : ∀ (e : STm) (Λ : LabelTable),
    Extends Λ (STm.collectLabels Λ e)
  | .var _, Λ => Extends.refl Λ
  | .obj _ _ ds, Λ => SDms.collectLabels_extends ds Λ
  | .call t _ u, Λ =>
      (STm.collectLabels_extends t Λ).trans (STm.collectLabels_extends u _)
  | .asc t _, Λ => STm.collectLabels_extends t Λ
/-- Collecting the labels of a member keeps every entry. -/
theorem SDm.collectLabels_extends : ∀ (d : SDm) (Λ : LabelTable),
    Extends Λ (SDm.collectLabels Λ d)
  | .typ _ _, Λ => Extends.refl Λ
  | .fn _ _ _ _ t, Λ => STm.collectLabels_extends t Λ
/-- Collecting the labels of a member list keeps every entry. -/
theorem SDms.collectLabels_extends : ∀ (ds : SDms) (Λ : LabelTable),
    Extends Λ (SDms.collectLabels Λ ds)
  | .nil, Λ => Extends.refl Λ
  | .cons d ds', Λ =>
      ((addLabel_extends Λ d.name ds'.length).trans (SDm.collectLabels_extends d _)).trans
        (SDms.collectLabels_extends ds' _)
end

/-- Every explicit entry is the entry of the table `labelsOfProgram` builds. -/
theorem labelsOfProgram_explicit {Λ₀ Λ : LabelTable} {e : STm}
    (h : labelsOfProgram Λ₀ e = some Λ) : Extends Λ₀ Λ := by
  dsimp only [labelsOfProgram] at h
  split at h
  · cases h; exact STm.collectLabels_extends e Λ₀
  · cases h

/-! ## The version's programs

Each program of `Notation.lean` gets its label table from `labelsOfProgram`,
compared by `decide` with the table written out, and resolves under it.  The
erasure of the resolved term is compared by `rfl` with the version's term,
since the version's terms derive no equality.  Each closed program also meets
the three premises of `resolveTm_isSome`, decided. -/

/-! ### `ex0` -/

/-- `ex0` needs no label. -/
example : labelsOfProgram [] ex0src = some [] := by decide

/-- `ex0` resolves to the subject of `Oopsla16.Examples.ex0`. -/
example : (resolve [] ex0src).map ATm.erase = some (.tobj .dnil) := rfl

/-- Ascribed, it resolves to the same term. -/
example : (resolve [] ex0AscSrc).map ATm.erase = some (.tobj .dnil) := rfl

/-! ### `RecursiveArg.prog` -/

/-- The table of `RecursiveArg.prog`: the caller's method, then the argument's
three members. -/
def recArgTable : LabelTable := [("apply", 0), ("A", 2), ("B", 1), ("f", 0)]

example : labelsOfProgram [] recArgSrc = some recArgTable := by decide

example : STm.Scoped [] recArgSrc = true ∧ STm.LabelsIn recArgTable recArgSrc = true ∧
    STm.Positioned recArgTable recArgSrc = true := by decide

example : (resolve recArgTable recArgSrc).map ATm.erase
    = some FCdotR.SourceSafety.RecursiveArg.prog := rfl

/-! ### `CurryCall.prog` -/

/-- The table of `CurryCall.prog`: every literal has the one method. -/
def curryCallTable : LabelTable := [("apply", 0)]

example : labelsOfProgram [] curryCallSrc = some curryCallTable := by decide

example : STm.Scoped [] curryCallSrc = true ∧ STm.LabelsIn curryCallTable curryCallSrc = true ∧
    STm.Positioned curryCallTable curryCallSrc = true := by decide

example : (resolve curryCallTable curryCallSrc).map ATm.erase
    = some FCdotR.CurryCall.prog := rfl

/-! ### `ex1`

`T` is the type member of the parameter's type and labels no literal member,
so it is an explicit entry. -/

/-- The table of `ex1`. -/
def ex1Table : LabelTable := [("T", 0), ("apply", 0)]

example : labelsOfProgram [("T", 0)] ex1src = some ex1Table := by decide

example : STm.Scoped [] ex1src = true ∧ STm.LabelsIn ex1Table ex1src = true ∧
    STm.Positioned ex1Table ex1src = true := by decide

example : (resolve ex1Table ex1src).map ATm.erase
    = some FCdotR.CheckerExamples.DotExs.ex1Tm := rfl

/-! ### `ex2`, open in `y`

`apply` is the method of `y`'s type and labels no literal member of the
program, so it is an explicit entry. -/

/-- The table of `ex2`. -/
def ex2Table : LabelTable := [("apply", 0), ("T", 0)]

example : labelsOfProgram [("apply", 0)] ex2src = some ex2Table := by decide

example : STm.Scoped ["y"] ex2src = true ∧ STm.LabelsIn ex2Table ex2src = true ∧
    STm.Positioned ex2Table ex2src = true := by decide

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map ATm.erase
    = some FCdotR.CheckerExamples.DotExs.ex2Tm := rfl

/-- `polyId`, the type of `y`, resolves to the version's `polyId`. -/
example : resolveTy ex2Table .nil polyId = some FCdotR.CheckerExamples.DotExs.polyId := by
  decide

/-! ### `paper_lst`

`T` is the type member of `cons`'s parameter type and labels no literal
member, so it is the one explicit entry.  Every other name gets the position
the version's derivation uses: `nil = 2`, `cons = 1`, `List = 0` in the module,
`head = 2`, `tail = 1`, `Elem = 0` in a list cell, `apply = 0` in the curried
layers of `cons`. -/

/-- The table of `paper_lst`. -/
def paperLstTable : LabelTable :=
  [("T", 0), ("nil", 2), ("head", 2), ("tail", 1), ("Elem", 0), ("cons", 1), ("apply", 0),
    ("List", 0)]

example : labelsOfProgram [("T", 0)] paperLstSrc = some paperLstTable := by decide

/-- The positions of the version's derivation, name by name. -/
example : ["nil", "cons", "List", "head", "tail", "Elem", "apply", "T"].map (labelOf? paperLstTable)
    = [some 2, some 1, some 0, some 2, some 1, some 0, some 0, some 0] := by decide

example : STm.Scoped [] paperLstSrc = true ∧ STm.LabelsIn paperLstTable paperLstSrc = true ∧
    STm.Positioned paperLstTable paperLstSrc = true := by decide

example : (resolve paperLstTable paperLstSrc).map ATm.erase
    = some FCdotR.CheckerExamples.PaperLst.lstTm := rfl

/-- The totality theorem applies to `paper_lst`, with the positions taken from
the table `labelsOfProgram` built. -/
example : (resolve paperLstTable paperLstSrc).isSome = true :=
  resolveTm_isSome paperLstSrc paperLstTable .nil (by decide) (by decide)
    (labelsOfProgram_positioned (Λ₀ := [("T", 0)]) (by decide))

/-! ### `FunctionField`, two types under the self `z` -/

/-- The labels of `FunctionField`: `A = 2`, `B = 1`, `f = 0`. -/
def functionFieldTable : LabelTable := [("A", 2), ("B", 1), ("f", 0)]

example : resolveTy functionFieldTable (NameEnv.nil.cons "z") Sbody
    = some Oopsla16.Examples.FunctionField.Sbody := by decide

example : resolveTy functionFieldTable (NameEnv.nil.cons "z") Tbody
    = some Oopsla16.Examples.FunctionField.Tbody := by decide

/-! ### `forgetSelf`, two closed types

`μ(z. ⊤ ∧ {type B : ⊥ .. ⊤})` and its body, with `B = 1`, the two sides of
`Oopsla16.Examples.forgetSelf`. -/

example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
    = some (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop))) := by decide

example : resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
    = some (.TAnd .TTop (.TTyp 1 .TBot .TTop)) := by decide

/-! ### A program with no table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  The first puts
`a` at `1` and `b` at `0`, the second needs `b` at `1`, so no table positions
all three. -/

/-- The cyclic names program. -/
def cyclicSrc : STm :=
  o16% (new { p ⇒ type a = ⊤ type b = ⊤ }).a(
         (new { q ⇒ type b = ⊤ type c = ⊤ }).b(new { r ⇒ type c = ⊤ type a = ⊤ }))

example : cyclicSrc =
    .call (.obj "p" none (.cons (.typ "a" .top) (.cons (.typ "b" .top) .nil))) "a"
      (.call (.obj "q" none (.cons (.typ "b" .top) (.cons (.typ "c" .top) .nil))) "b"
        (.obj "r" none (.cons (.typ "c" .top) (.cons (.typ "a" .top) .nil)))) := by
  decide

example : labelsOfProgram [] cyclicSrc = none := by decide

/-- Under the table the first literal suggests, resolution fails at the second
literal rather than renumbering its members. -/
example : (resolve [("a", 1), ("b", 0), ("c", 0)] cyclicSrc).isSome = false := by decide

end Oopsla16Frontend
