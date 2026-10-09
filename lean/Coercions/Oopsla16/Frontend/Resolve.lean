import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Frontend.Notation
import Coercions.Oopsla16.Examples
import Coercions.FCdotR.CheckerExamples

/-!
# Name resolution and label tables

The resolvers take a surface phrase to the annotated de Bruijn syntax of
`Ann.lean`.  They are where a name becomes an index and a label becomes a
position.

A `NameEnv` holds one name per binder, innermost first, so the innermost
binder wins.  A literal `new {z ⇒ ds}` resolves its members and written self
type under `z`.  A method `def m(x : S) : U = t` resolves `S` outside `x` and
`U` and `t` under `x`.  The resolver inserts no binder.

A member list resolves only when each member's name has its position as label
in the table.  A mismatch fails, and no member is renumbered.
`labelsOfProgram` builds a table from explicit entries and the member names
of every literal, in program order.  It fails when a name is forced to two
positions.  A name that labels no literal member, such as a type member of a
parameter's type, needs an explicit entry.

The theorems are totality on scoped, labelled, positioned phrases
(`resolveTm_isSome`), `labelsOfProgram_positioned`, and that resolution
commutes with the erasures of `Surface.lean` on a program that resolves
(`resolve_eraseSelf` and its four siblings).  The examples at the end
resolve the calculus's own programs and compare their erasures with its terms.

Importing `Notation.lean` makes `type`, `def`, `new` and `μ` keywords, so none
can be a local name.  Nothing here is part of the metatheory.
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

/-! ## The resolvers -/

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
/-- Resolve a surface member.  The list that holds it checks its label. -/
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
/-- Resolve a surface member list.  Every member's name must have in the table
the label of its position. -/
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

/-- Resolve a surface term that is open in the variables of `ν`. -/
def resolveIn {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (e : STm) : Option (ATm s) :=
  resolveTm Λ ν e

/-- Resolve a closed surface program. -/
def resolve (Λ : LabelTable) (e : STm) : Option (ATm []) := resolveIn Λ .nil e

/-! ## Totality

Resolution succeeds on a phrase that is scoped, labelled and positioned.  The
proofs follow the resolvers clause by clause. -/

/-- A `some` from an `isSome`. -/
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

/-! ## Erasures commute with resolution

A written program that resolves has each of its five surface erasures
(`Surface.lean`) resolve, to the erasure of the resolved program
(`Ann.lean`).  An erased source written in the notation therefore stands for
the erased program.  The converse fails: an erasure may drop the one
annotation that does not resolve.  The Scala form copies a parameter type from
the written self type, and the two resolve in the same scope, the literal's
self binder. -/

/-- A missing annotation resolves to a missing one. -/
@[simp] theorem resolveTyOpt_none {s : Sig} (Λ : LabelTable) (ν : NameEnv s) :
    resolveTyOpt Λ ν none = some none := rfl

/-- Dropping every self type keeps a member's name. -/
theorem SDm.name_eraseSelf (d : SDm) : d.eraseSelf.name = d.name := by
  cases d <;> rfl
/-- Dropping every self type keeps the number of members. -/
theorem SDms.length_eraseSelf : (ds : SDms) → ds.eraseSelf.length = ds.length
  | .nil => rfl
  | .cons _ ds' => by simp [SDms.eraseSelf, SDms.length, SDms.length_eraseSelf ds']

mutual
/-- A term that resolves has its `S` erasure resolve to the `S` erasure of the result. -/
theorem resolveTm_eraseSelf : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ATm s),
    resolveTm Λ ν e = some a → resolveTm Λ ν e.eraseSelf = some a.eraseSelf
  | .var x, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp [STm.eraseSelf, resolveTm, hi, ATm.eraseSelf]
  | .obj z self ds, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨o, ho, ds', hds, rfl⟩ := h
      simp [STm.eraseSelf, resolveTm, resolveDms_eraseSelf ds Λ _ ds' hds,
        ATm.eraseSelf]
  | .call t m u, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, l, hl, u', hu, rfl⟩ := h
      simp [STm.eraseSelf, resolveTm, resolveTm_eraseSelf t Λ ν t' ht, hl,
        resolveTm_eraseSelf u Λ ν u' hu, ATm.eraseSelf]
  | .asc t T, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [STm.eraseSelf, resolveTm, resolveTm_eraseSelf t Λ ν t' ht, hT, ATm.eraseSelf]
/-- The member case of `resolveTm_eraseSelf`. -/
theorem resolveDm_eraseSelf : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ADm s),
    resolveDm Λ ν d = some a → resolveDm Λ ν d.eraseSelf = some a.eraseSelf
  | .typ L T, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, rfl⟩ := h
      simp [SDm.eraseSelf, resolveDm, hT, ADm.eraseSelf]
  | .fn m x S U t, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, U', hU, t', ht, rfl⟩ := h
      simp [SDm.eraseSelf, resolveDm, hS, hU, resolveTm_eraseSelf t Λ _ t' ht, ADm.eraseSelf]
/-- The member list case of `resolveTm_eraseSelf`. -/
theorem resolveDms_eraseSelf : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADms s), resolveDms Λ ν ds = some a → resolveDms Λ ν ds.eraseSelf = some a.eraseSelf
  | .nil, _, Λ, ν, a, h => by
      simp only [resolveDms, Option.some.injEq] at h
      subst h
      rfl
  | .cons d ds', _, Λ, ν, a, h => by
      simp only [resolveDms] at h
      split at h
      · rename_i hpos
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, ds'', hds, rfl⟩ := h
        have hpos' : (labelOf? Λ d.eraseSelf.name == some ds'.eraseSelf.length) = true := by
          rw [SDm.name_eraseSelf, SDms.length_eraseSelf]
          exact hpos
        simp [SDms.eraseSelf, resolveDms, hpos', resolveDm_eraseSelf d Λ ν d' hd,
          resolveDms_eraseSelf ds' Λ ν ds'' hds, ADms.eraseSelf]
      · cases h
end


/-- Dropping every result type keeps a member's name. -/
theorem SDm.name_eraseRes (d : SDm) : d.eraseRes.name = d.name := by
  cases d <;> rfl
/-- Dropping every result type keeps the number of members. -/
theorem SDms.length_eraseRes : (ds : SDms) → ds.eraseRes.length = ds.length
  | .nil => rfl
  | .cons _ ds' => by simp [SDms.eraseRes, SDms.length, SDms.length_eraseRes ds']

mutual
/-- A term that resolves has its `R` erasure resolve to the `R` erasure of the result. -/
theorem resolveTm_eraseRes : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ATm s),
    resolveTm Λ ν e = some a → resolveTm Λ ν e.eraseRes = some a.eraseRes
  | .var x, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp [STm.eraseRes, resolveTm, hi, ATm.eraseRes]
  | .obj z self ds, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨o, ho, ds', hds, rfl⟩ := h
      simp [STm.eraseRes, resolveTm, ho, resolveDms_eraseRes ds Λ _ ds' hds,
        ATm.eraseRes]
  | .call t m u, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, l, hl, u', hu, rfl⟩ := h
      simp [STm.eraseRes, resolveTm, resolveTm_eraseRes t Λ ν t' ht, hl,
        resolveTm_eraseRes u Λ ν u' hu, ATm.eraseRes]
  | .asc t T, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [STm.eraseRes, resolveTm, resolveTm_eraseRes t Λ ν t' ht, hT, ATm.eraseRes]
/-- The member case of `resolveTm_eraseRes`. -/
theorem resolveDm_eraseRes : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ADm s),
    resolveDm Λ ν d = some a → resolveDm Λ ν d.eraseRes = some a.eraseRes
  | .typ L T, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, rfl⟩ := h
      simp [SDm.eraseRes, resolveDm, hT, ADm.eraseRes]
  | .fn m x S U t, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, U', hU, t', ht, rfl⟩ := h
      simp [SDm.eraseRes, resolveDm, hS, resolveTm_eraseRes t Λ _ t' ht, ADm.eraseRes]
/-- The member list case of `resolveTm_eraseRes`. -/
theorem resolveDms_eraseRes : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADms s), resolveDms Λ ν ds = some a → resolveDms Λ ν ds.eraseRes = some a.eraseRes
  | .nil, _, Λ, ν, a, h => by
      simp only [resolveDms, Option.some.injEq] at h
      subst h
      rfl
  | .cons d ds', _, Λ, ν, a, h => by
      simp only [resolveDms] at h
      split at h
      · rename_i hpos
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, ds'', hds, rfl⟩ := h
        have hpos' : (labelOf? Λ d.eraseRes.name == some ds'.eraseRes.length) = true := by
          rw [SDm.name_eraseRes, SDms.length_eraseRes]
          exact hpos
        simp [SDms.eraseRes, resolveDms, hpos', resolveDm_eraseRes d Λ ν d' hd,
          resolveDms_eraseRes ds' Λ ν ds'' hds, ADms.eraseRes]
      · cases h
end


/-- Dropping every parameter type keeps a member's name. -/
theorem SDm.name_eraseParam (d : SDm) : d.eraseParam.name = d.name := by
  cases d <;> rfl
/-- Dropping every parameter type keeps the number of members. -/
theorem SDms.length_eraseParam : (ds : SDms) → ds.eraseParam.length = ds.length
  | .nil => rfl
  | .cons _ ds' => by simp [SDms.eraseParam, SDms.length, SDms.length_eraseParam ds']

mutual
/-- A term that resolves has its `P` erasure resolve to the `P` erasure of the result. -/
theorem resolveTm_eraseParam : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ATm s),
    resolveTm Λ ν e = some a → resolveTm Λ ν e.eraseParam = some a.eraseParam
  | .var x, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp [STm.eraseParam, resolveTm, hi, ATm.eraseParam]
  | .obj z self ds, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨o, ho, ds', hds, rfl⟩ := h
      simp [STm.eraseParam, resolveTm, ho, resolveDms_eraseParam ds Λ _ ds' hds,
        ATm.eraseParam]
  | .call t m u, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, l, hl, u', hu, rfl⟩ := h
      simp [STm.eraseParam, resolveTm, resolveTm_eraseParam t Λ ν t' ht, hl,
        resolveTm_eraseParam u Λ ν u' hu, ATm.eraseParam]
  | .asc t T, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [STm.eraseParam, resolveTm, resolveTm_eraseParam t Λ ν t' ht, hT, ATm.eraseParam]
/-- The member case of `resolveTm_eraseParam`. -/
theorem resolveDm_eraseParam : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ADm s),
    resolveDm Λ ν d = some a → resolveDm Λ ν d.eraseParam = some a.eraseParam
  | .typ L T, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, rfl⟩ := h
      simp [SDm.eraseParam, resolveDm, hT, ADm.eraseParam]
  | .fn m x S U t, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, U', hU, t', ht, rfl⟩ := h
      simp [SDm.eraseParam, resolveDm, hU, resolveTm_eraseParam t Λ _ t' ht, ADm.eraseParam]
/-- The member list case of `resolveTm_eraseParam`. -/
theorem resolveDms_eraseParam : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADms s), resolveDms Λ ν ds = some a → resolveDms Λ ν ds.eraseParam = some a.eraseParam
  | .nil, _, Λ, ν, a, h => by
      simp only [resolveDms, Option.some.injEq] at h
      subst h
      rfl
  | .cons d ds', _, Λ, ν, a, h => by
      simp only [resolveDms] at h
      split at h
      · rename_i hpos
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, ds'', hds, rfl⟩ := h
        have hpos' : (labelOf? Λ d.eraseParam.name == some ds'.eraseParam.length) = true := by
          rw [SDm.name_eraseParam, SDms.length_eraseParam]
          exact hpos
        simp [SDms.eraseParam, resolveDms, hpos', resolveDm_eraseParam d Λ ν d' hd,
          resolveDms_eraseParam ds' Λ ν ds'' hds, ADms.eraseParam]
      · cases h
end


/-- Dropping the self type of every call argument keeps a member's name. -/
theorem SDm.name_eraseArgSelf (d : SDm) : d.eraseArgSelf.name = d.name := by
  cases d <;> rfl
/-- Dropping the self type of every call argument keeps the number of members. -/
theorem SDms.length_eraseArgSelf : (ds : SDms) → ds.eraseArgSelf.length = ds.length
  | .nil => rfl
  | .cons _ ds' => by simp [SDms.eraseArgSelf, SDms.length, SDms.length_eraseArgSelf ds']

mutual
/-- A term that resolves has its `A` erasure resolve to the `A` erasure of the
result, in argument position or not. -/
theorem resolveTm_eraseArgSelfAt : ∀ (arg : Bool) (e : STm) {s : Sig} (Λ : LabelTable)
    (ν : NameEnv s) (a : ATm s),
    resolveTm Λ ν e = some a → resolveTm Λ ν (e.eraseArgSelfAt arg) = some (a.eraseArgSelfAt arg)
  | _, .var x, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp [STm.eraseArgSelfAt, resolveTm, hi, ATm.eraseArgSelfAt]
  | arg, .obj z self ds, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨o, ho, ds', hds, rfl⟩ := h
      cases arg <;>
        simp [STm.eraseArgSelfAt, resolveTm, ho, resolveDms_eraseArgSelf ds Λ _ ds' hds,
          ATm.eraseArgSelfAt]
  | _, .call t m u, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, l, hl, u', hu, rfl⟩ := h
      simp [STm.eraseArgSelfAt, resolveTm, resolveTm_eraseArgSelfAt false t Λ ν t' ht, hl,
        resolveTm_eraseArgSelfAt true u Λ ν u' hu, ATm.eraseArgSelfAt]
  | _, .asc t T, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [STm.eraseArgSelfAt, resolveTm, resolveTm_eraseArgSelfAt false t Λ ν t' ht, hT,
        ATm.eraseArgSelfAt]
/-- The member case of `resolveTm_eraseArgSelfAt`. -/
theorem resolveDm_eraseArgSelf : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADm s), resolveDm Λ ν d = some a → resolveDm Λ ν d.eraseArgSelf = some a.eraseArgSelf
  | .typ L T, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, rfl⟩ := h
      simp [SDm.eraseArgSelf, resolveDm, hT, ADm.eraseArgSelf]
  | .fn m x S U t, _, Λ, ν, a, h => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, U', hU, t', ht, rfl⟩ := h
      simp [SDm.eraseArgSelf, resolveDm, hS, hU, resolveTm_eraseArgSelfAt false t Λ _ t' ht,
        ADm.eraseArgSelf]
/-- The member list case of `resolveTm_eraseArgSelfAt`. -/
theorem resolveDms_eraseArgSelf : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADms s), resolveDms Λ ν ds = some a → resolveDms Λ ν ds.eraseArgSelf = some a.eraseArgSelf
  | .nil, _, Λ, ν, a, h => by
      simp only [resolveDms, Option.some.injEq] at h
      subst h
      rfl
  | .cons d ds', _, Λ, ν, a, h => by
      simp only [resolveDms] at h
      split at h
      · rename_i hpos
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, ds'', hds, rfl⟩ := h
        have hpos' : (labelOf? Λ d.eraseArgSelf.name == some ds'.eraseArgSelf.length) = true := by
          rw [SDm.name_eraseArgSelf, SDms.length_eraseArgSelf]
          exact hpos
        simp [SDms.eraseArgSelf, resolveDms, hpos', resolveDm_eraseArgSelf d Λ ν d' hd,
          resolveDms_eraseArgSelf ds' Λ ν ds'' hds, ADms.eraseArgSelf]
      · cases h
end

/-- The Scala form keeps a member's name. -/
theorem SDm.name_scalaForm (d : SDm) (H : Option SType) : (d.scalaForm H).name = d.name := by
  cases d <;> cases H <;> try rfl
  all_goals (rename_i T; cases T <;> rfl)
/-- The Scala form keeps the number of members. -/
theorem SDms.length_scalaForm : (ds : SDms) → (T : Option SType) →
    (ds.scalaForm T).length = ds.length
  | .nil, _ => rfl
  | .cons _ ds', none => by simp [SDms.scalaForm, SDms.length, SDms.length_scalaForm ds']
  | .cons _ ds', some T => by
      cases T <;> simp [SDms.scalaForm, SDms.length, SDms.length_scalaForm ds']


mutual
/-- A term that resolves has its Scala form resolve to the Scala form of the
result. -/
theorem resolveTm_scalaForm : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s) (a : ATm s),
    resolveTm Λ ν e = some a → resolveTm Λ ν e.scalaForm = some a.scalaForm
  | .var x, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp [STm.scalaForm, resolveTm, hi, ATm.scalaForm]
  | .obj z self ds, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨o, ho, ds', hds, rfl⟩ := h
      simp [STm.scalaForm, resolveTm, resolveDms_scalaForm ds Λ _ ds' self o hds ho,
        ATm.scalaForm]
  | .call t m u, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, l, hl, u', hu, rfl⟩ := h
      simp [STm.scalaForm, resolveTm, resolveTm_scalaForm t Λ ν t' ht, hl,
        resolveTm_scalaForm u Λ ν u' hu, ATm.scalaForm]
  | .asc t T, _, Λ, ν, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [STm.scalaForm, resolveTm, resolveTm_scalaForm t Λ ν t' ht, hT, ATm.scalaForm]
/-- The member case of `resolveTm_scalaForm`.  The conjunct of the self type
resolves in the member's own scope, as a written self type does. -/
theorem resolveDm_scalaForm : ∀ (d : SDm) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADm s) (H : Option SType) (H' : Option (Ty [] s)),
    resolveDm Λ ν d = some a → resolveTyOpt Λ ν H = some H' →
    resolveDm Λ ν (d.scalaForm H) = some (a.scalaForm H')
  | .typ L T, _, Λ, ν, a, _, _, h, _ => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, rfl⟩ := h
      simp [SDm.scalaForm, resolveDm, hT, ADm.scalaForm]
  | .fn m x S U t, _, Λ, ν, a, H, H', h, hH => by
      simp only [resolveDm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, U', _, t', ht, rfl⟩ := h
      have htt := resolveTm_scalaForm t Λ (ν.cons x) t' ht
      cases H with
      | none =>
          simp only [resolveTyOpt_none, Option.some.injEq] at hH
          subst hH
          simp [SDm.scalaForm, resolveDm, hS, htt, ADm.scalaForm]
      | some T =>
          cases T
          case fn m0 x0 S0 U0 =>
            simp only [resolveTyOpt, resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.pure_def, Option.map_eq_some_iff, Option.some.injEq] at hH
            obtain ⟨_, ⟨l, _, S0', hS0, U0', _, rfl⟩, rfl⟩ := hH
            cases S with
            | none =>
                simp only [resolveTyOpt_none, Option.some.injEq] at hS
                subst hS
                simp [SDm.scalaForm, resolveDm, resolveTyOpt, hS0, htt, ADm.scalaForm]
            | some S1 =>
                simp only [resolveTyOpt, Option.map_eq_some_iff] at hS
                obtain ⟨S1', hS1, rfl⟩ := hS
                simp [SDm.scalaForm, resolveDm, resolveTyOpt, hS1, htt, ADm.scalaForm]
          all_goals
            simp only [resolveTyOpt, resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.pure_def, Option.map_eq_some_iff, Option.some.injEq] at hH
            obtain ⟨_, hH0, rfl⟩ := hH
            repeat' obtain ⟨_, _, hH0⟩ := hH0
            simp [SDm.scalaForm, resolveDm, hS, htt, ADm.scalaForm]
/-- The member list case of `resolveTm_scalaForm`, in lockstep with a self type
that resolves. -/
theorem resolveDms_scalaForm : ∀ (ds : SDms) {s : Sig} (Λ : LabelTable) (ν : NameEnv s)
    (a : ADms s) (T : Option SType) (T' : Option (Ty [] s)),
    resolveDms Λ ν ds = some a → resolveTyOpt Λ ν T = some T' →
    resolveDms Λ ν (ds.scalaForm T) = some (a.scalaForm T')
  | .nil, _, Λ, ν, a, T, _, h, _ => by
      simp only [resolveDms, Option.some.injEq] at h
      subst h
      cases T <;> rfl
  | .cons d ds', _, Λ, ν, a, T, T', h, hT => by
      simp only [resolveDms] at h
      split at h
      · rename_i hpos
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, ds'', hds, rfl⟩ := h
        have hpos' (H : Option SType) (TS : Option SType) :
            (labelOf? Λ (d.scalaForm H).name == some (ds'.scalaForm TS).length) = true := by
          rw [SDm.name_scalaForm, SDms.length_scalaForm]
          exact hpos
        cases T with
        | none =>
            simp only [resolveTyOpt_none, Option.some.injEq] at hT
            subst hT
            simp [SDms.scalaForm, resolveDms, hpos', resolveDm_scalaForm d Λ ν d' none none hd rfl,
              resolveDms_scalaForm ds' Λ ν ds'' none none hds rfl, ADms.scalaForm]
        | some T0 =>
            cases T0
            case and H TS =>
              simp only [resolveTyOpt, resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.pure_def, Option.map_eq_some_iff, Option.some.injEq] at hT
              obtain ⟨_, ⟨H', hH, TS', hTS, rfl⟩, rfl⟩ := hT
              simp [SDms.scalaForm, resolveDms, hpos',
                resolveDm_scalaForm d Λ ν d' (some H) (some H') hd (by simp [resolveTyOpt, hH]),
                resolveDms_scalaForm ds' Λ ν ds'' (some TS) (some TS') hds
                  (by simp [resolveTyOpt, hTS]), ADms.scalaForm]
            all_goals
              simp only [resolveTyOpt, resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.pure_def, Option.map_eq_some_iff, Option.some.injEq] at hT
              obtain ⟨_, hT0, rfl⟩ := hT
              repeat' obtain ⟨_, _, hT0⟩ := hT0
              simp [SDms.scalaForm, resolveDms, hpos',
                resolveDm_scalaForm d Λ ν d' none none hd rfl,
                resolveDms_scalaForm ds' Λ ν ds'' none none hds rfl, ADms.scalaForm]
      · cases h
end

/-- A program that resolves has its `S` erasure resolve to the `S` erasure. -/
theorem resolve_eraseSelf {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    resolve Λ e.eraseSelf = some a.eraseSelf :=
  resolveTm_eraseSelf e Λ .nil a h

/-- A program that resolves has its `R` erasure resolve to the `R` erasure. -/
theorem resolve_eraseRes {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    resolve Λ e.eraseRes = some a.eraseRes :=
  resolveTm_eraseRes e Λ .nil a h

/-- A program that resolves has its `P` erasure resolve to the `P` erasure. -/
theorem resolve_eraseParam {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    resolve Λ e.eraseParam = some a.eraseParam :=
  resolveTm_eraseParam e Λ .nil a h

/-- A program that resolves has its `A` erasure resolve to the `A` erasure. -/
theorem resolve_eraseArgSelf {Λ : LabelTable} {e : STm} {a : ATm []}
    (h : resolve Λ e = some a) : resolve Λ e.eraseArgSelf = some a.eraseArgSelf :=
  resolveTm_eraseArgSelfAt false e Λ .nil a h

/-- A program that resolves has its Scala form resolve to the Scala form. -/
theorem resolve_scalaForm {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    resolve Λ e.scalaForm = some a.scalaForm :=
  resolveTm_scalaForm e Λ .nil a h

/-! ## Label tables from a program

`collectLabels` walks the literals in program order and gives each member name
not yet in the table the position of its first occurrence.  `labelsOfProgram`
starts from the explicit entries and accepts the result when it positions the
program.  A name at two positions keeps the first and fails the check at the
second. -/

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

/-- The label table of a program: the explicit entries, then every member name
at its position.  `none` when a name is forced to two positions or an explicit
entry contradicts a position. -/
def labelsOfProgram (explicit : LabelTable) (e : STm) : Option LabelTable :=
  let Λ := STm.collectLabels explicit e
  if STm.Positioned Λ e then some Λ else none

/-- A table built from a program positions it, the third premise of
`resolveTm_isSome`. -/
theorem labelsOfProgram_positioned {Λ₀ Λ : LabelTable} {e : STm}
    (h : labelsOfProgram Λ₀ e = some Λ) : STm.Positioned Λ e = true := by
  dsimp only [labelsOfProgram] at h
  split at h
  · cases h; assumption
  · cases h

/-! ### The explicit entries win

The table only grows at its end, so an explicit entry is never overwritten. -/

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

/-! ## The calculus's programs

For each program of `Notation.lean`, `labelsOfProgram` gives the table written
out, and the erasure of the resolved term is the calculus's own term. -/

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

`T` labels no literal member, so it is an explicit entry. -/

/-- The table of `ex1`. -/
def ex1Table : LabelTable := [("T", 0), ("apply", 0)]

example : labelsOfProgram [("T", 0)] ex1src = some ex1Table := by decide

example : STm.Scoped [] ex1src = true ∧ STm.LabelsIn ex1Table ex1src = true ∧
    STm.Positioned ex1Table ex1src = true := by decide

example : (resolve ex1Table ex1src).map ATm.erase
    = some FCdotR.CheckerExamples.DotExs.ex1Tm := rfl

/-! ### `ex2`, open in `y`

`apply` labels no literal member, so it is an explicit entry. -/

/-- The table of `ex2`. -/
def ex2Table : LabelTable := [("apply", 0), ("T", 0)]

example : labelsOfProgram [("apply", 0)] ex2src = some ex2Table := by decide

example : STm.Scoped ["y"] ex2src = true ∧ STm.LabelsIn ex2Table ex2src = true ∧
    STm.Positioned ex2Table ex2src = true := by decide

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map ATm.erase
    = some FCdotR.CheckerExamples.DotExs.ex2Tm := rfl

/-- `polyId`, the type of `y`, resolves to the calculus's `polyId`. -/
example : resolveTy ex2Table .nil polyId = some FCdotR.CheckerExamples.DotExs.polyId := by
  decide

/-! ### `paper_lst`

`T` labels no literal member, so it is the one explicit entry.  The other
names get the positions of the calculus's derivation: `nil = 2`, `cons = 1`,
`List = 0` in the module, `head = 2`, `tail = 1`, `Elem = 0` in a list cell,
and `apply = 0` in the curried layers of `cons`. -/

/-- The table of `paper_lst`. -/
def paperLstTable : LabelTable :=
  [("T", 0), ("nil", 2), ("head", 2), ("tail", 1), ("Elem", 0), ("cons", 1), ("apply", 0),
    ("List", 0)]

example : labelsOfProgram [("T", 0)] paperLstSrc = some paperLstTable := by decide

/-- The positions of the calculus's derivation, name by name. -/
example : ["nil", "cons", "List", "head", "tail", "Elem", "apply", "T"].map (labelOf? paperLstTable)
    = [some 2, some 1, some 0, some 2, some 1, some 0, some 0, some 0] := by decide

example : STm.Scoped [] paperLstSrc = true ∧ STm.LabelsIn paperLstTable paperLstSrc = true ∧
    STm.Positioned paperLstTable paperLstSrc = true := by decide

example : (resolve paperLstTable paperLstSrc).map ATm.erase
    = some FCdotR.CheckerExamples.PaperLst.lstTm := rfl

/-- Totality applies to `paper_lst`. -/
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

`μ(z. ⊤ ∧ {type B : ⊥ .. ⊤})` and its body, with `B = 1`: the two sides of
`Oopsla16.Examples.forgetSelf`. -/

example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
    = some (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop))) := by decide

example : resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
    = some (.TAnd .TTop (.TTyp 1 .TBot .TTop)) := by decide

/-! ### A program with no table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  The first puts
`a` at `1` and `b` at `0`, the second needs `b` at `1`, so no table fits. -/

/-- Three literals whose member names form a cycle. -/
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
literal. -/
example : (resolve [("a", 1), ("b", 0), ("c", 0)] cyclicSrc).isSome = false := by decide

/-! ## Erased sources

The programs above with some annotations left out, written in the notation.
Each is the surface erasure of the written program, and resolves under the
written program's table to the erasure of its resolution.  The checks run the
resolver, so they hold apart from `resolve_eraseSelf` and its siblings. -/

/-! ### `RecursiveArg.prog` -/

/-- `RecursiveArg.prog` with no self type. -/
def recArgSrcS : STm :=
  o16% (new { c ⇒ def apply(y) = y }).apply(
         new { z ⇒ type A = z.B
                   type B = ⊤
                   def f(y) = y })

/-- `RecursiveArg.prog` with no self type on the argument. -/
def recArgSrcA : STm :=
  o16% (new { c : { def apply(x : μ(z. { def f(y : ⊤) : z.B })) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = y }).apply(
         new { z ⇒ type A = z.B
                   type B = ⊤
                   def f(y) = y })

/-- `RecursiveArg.prog` as a Scala programmer writes it: each parameter type
taken from the written self type, no self type and no result type. -/
def recArgSrcSR : STm :=
  o16% (new { c ⇒ def apply(y : μ(z. { def f(y : ⊤) : z.B })) = y }).apply(
         new { z ⇒ type A = z.B
                   type B = ⊤
                   def f(y : ⊤) = y })

example : recArgSrc.eraseSelf = recArgSrcS := by decide
example : recArgSrc.eraseArgSelf = recArgSrcA := by decide
example : recArgSrc.scalaForm = recArgSrcSR := by decide

example : resolve recArgTable recArgSrcS
    = (resolve recArgTable recArgSrc).map ATm.eraseSelf := rfl
example : resolve recArgTable recArgSrcA
    = (resolve recArgTable recArgSrc).map ATm.eraseArgSelf := rfl
example : resolve recArgTable recArgSrcSR
    = (resolve recArgTable recArgSrc).map ATm.scalaForm := rfl

/-- The typer takes the written program as it is (`ATm.landed`), and none of
its three erasures. -/
example : (resolve recArgTable recArgSrc).map ATm.landed = some true ∧
    (resolve recArgTable recArgSrcS).map ATm.landed = some false ∧
    (resolve recArgTable recArgSrcA).map ATm.landed = some false ∧
    (resolve recArgTable recArgSrcSR).map ATm.landed = some false := by
  decide

/-! ### `CurryCall.prog` -/

/-- `CurryCall.prog` with no self type on the argument.  The inner literal is
a receiver, so it keeps its self type. -/
def curryCallSrcA : STm :=
  o16% (new { c : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = (new { i : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒ def apply(y) = y }).apply(y) }).apply(
         new { i ⇒ def apply(y) = y })

/-- `CurryCall.prog` as a Scala programmer writes it. -/
def curryCallSrcSR : STm :=
  o16% (new { c ⇒ def apply(y : ⊤) = (new { i ⇒ def apply(y : ⊤) = y }).apply(y) }).apply(
         new { i ⇒ def apply(y : ⊤) = y })

example : curryCallSrc.eraseArgSelf = curryCallSrcA := by decide
example : curryCallSrc.scalaForm = curryCallSrcSR := by decide

example : resolve curryCallTable curryCallSrcA
    = (resolve curryCallTable curryCallSrc).map ATm.eraseArgSelf := rfl
example : resolve curryCallTable curryCallSrcSR
    = (resolve curryCallTable curryCallSrc).map ATm.scalaForm := rfl

/-! ### `ex1`

`ex1` has no self type, so its `S` and `A` erasures are the program itself.
Its Scala form is its `R` erasure. -/

/-- `ex1` with no result type. -/
def ex1SrcR : STm :=
  o16% new { o ⇒ def apply(t : { type T : ⊥ .. ⊤ }) =
                  new { p ⇒ def apply(x : t.T) = x } }

/-- `ex1` with no parameter type. -/
def ex1SrcP : STm :=
  o16% new { o ⇒ def apply(t) : { def apply(x : t.T) : t.T } =
                  new { p ⇒ def apply(x) : t.T = x } }

example : ex1src.eraseSelf = ex1src ∧ ex1src.eraseArgSelf = ex1src := by decide
example : ex1src.eraseRes = ex1SrcR ∧ ex1src.scalaForm = ex1SrcR := by decide
example : ex1src.eraseParam = ex1SrcP := by decide

example : resolve ex1Table ex1SrcR = (resolve ex1Table ex1src).map ATm.eraseRes := rfl
example : resolve ex1Table ex1SrcP = (resolve ex1Table ex1src).map ATm.eraseParam := rfl

/-! ### `paper_lst`

The module is long, so its erasures are the functions applied to it. -/

example : resolve paperLstTable paperLstSrc.eraseRes
    = (resolve paperLstTable paperLstSrc).map ATm.eraseRes := rfl
example : resolve paperLstTable paperLstSrc.eraseParam
    = (resolve paperLstTable paperLstSrc).map ATm.eraseParam := rfl

/-- The theorem gives the same for every erasure, with no run of the
resolver on the erased source. -/
example : ∃ a, resolve paperLstTable paperLstSrc = some a ∧
    resolve paperLstTable paperLstSrc.scalaForm = some a.scalaForm :=
  match h : resolve paperLstTable paperLstSrc with
  | some a => ⟨a, rfl, resolve_scalaForm h⟩
  | none => absurd h (by decide)

end Oopsla16Frontend
