import FCsub

/-!
# Finite generative alias scopes

This module is a target-side administrative layer for finite signatures of
type aliases.  It deliberately adds no path or member syntax to `FCsub`.
Instead, a signature of `count` aliases is represented by `count` nested
uses of the existing `FCsub.NewtypeScope`: every layer allocates one fresh
type name followed by equality evidence relating that name to an ambient
anchor type.

Finite indices are newest-first, consistently with `FCsub.BVar.bound` and
`FCsub.TypeArgs.get`.  Thus index zero denotes the innermost (last allocated)
alias.  The explicit `name` and `equality` maps below make the two-binder
stride part of the intrinsic interface rather than a convention left to
clients.
-/

namespace DotToFCsub.M6.AliasScope

open FCsub

/-- Add one private name/equality pair per alias. -/
@[reducible]
def Scope (scope : Sig) : Nat → Sig
  | 0 => scope
  | count + 1 => NewtypeScope (Scope scope count)

/-- Ambient weakening through one private name/equality pair. -/
def weakenOne {scope : Sig} : Rename scope (NewtypeScope scope) :=
  (Rename.succ (kind := .type)).comp
    (Rename.succ (kind := .evidence .equality))

/-- Ambient weakening through every alias pair. -/
def weaken {scope : Sig} : (count : Nat) → Rename scope (Scope scope count)
  | 0 => Rename.id
  | count + 1 => (weaken count).comp weakenOne

/-- The fresh type-name variable for an alias. -/
def name {scope : Sig} : (count : Nat) → Fin count →
    BVar (Scope scope count) .type
  | 0, index => Fin.elim0 index
  | _count + 1, ⟨0, _⟩ => .there .here
  | count + 1, ⟨index + 1, smaller⟩ =>
      .there (.there
        (name count ⟨index, Nat.lt_of_succ_lt_succ smaller⟩))

/-- The equality-evidence variable paired with an alias name. -/
def equality {scope : Sig} : (count : Nat) → Fin count →
    BVar (Scope scope count) (.evidence .equality)
  | 0, index => Fin.elim0 index
  | _count + 1, ⟨0, _⟩ => .here
  | count + 1, ⟨index + 1, smaller⟩ =>
      .there (.there
        (equality count ⟨index, Nat.lt_of_succ_lt_succ smaller⟩))

/-- The target type selected by a fresh alias name. -/
def aliasTy {scope : Sig} (count : Nat) (index : Fin count) :
    Ty (Scope scope count) :=
  .tvar (name count index)

/-- An ambient anchor type weakened below the complete alias scope. -/
def anchorTy {scope : Sig} {count : Nat}
    (anchors : Fin count → Ty scope) (index : Fin count) :
    Ty (Scope scope count) :=
  (anchors index).rename (weaken count)

/-- Extend a context with a finite signature of aliases.

The tail is allocated first, so `anchors 0` becomes the newest alias and the
resulting context agrees definitionally with the newest-first `Fin` layout.
-/
def extend {scope : Sig} (context : Ctx scope) :
    {count : Nat} → (Fin count → Ty scope) → Ctx (Scope scope count)
  | 0, _ => context
  | count + 1, anchors =>
      let previous := extend context (fun index => anchors index.succ)
      previous.extendNewtype
        ((anchors ⟨0, Nat.zero_lt_succ count⟩).rename (weaken count))

/-! ## Exact intrinsic layout -/

@[simp]
theorem name_zero {scope : Sig} {count : Nat} :
    name (scope := scope) (count + 1) ⟨0, Nat.zero_lt_succ count⟩ =
      (.there .here : BVar (Scope scope (count + 1)) .type) := rfl

@[simp]
theorem equality_zero {scope : Sig} {count : Nat} :
    equality (scope := scope) (count + 1) ⟨0, Nat.zero_lt_succ count⟩ =
      (.here : BVar (Scope scope (count + 1)) (.evidence .equality)) := rfl

@[simp]
theorem name_succ {scope : Sig} {count : Nat} (index : Fin count) :
    name (scope := scope) (count + 1) index.succ =
      .there (.there (name count index)) := by
  cases index
  rfl

@[simp]
theorem equality_succ {scope : Sig} {count : Nat} (index : Fin count) :
    equality (scope := scope) (count + 1) index.succ =
      .there (.there (equality count index)) := by
  cases index
  rfl

/-- The exact heterogeneous de Bruijn depth of a variable. -/
def depth {scope : Sig} {kind : BinderKind} : BVar scope kind → Nat
  | .here => 0
  | .there older => depth older + 1

@[simp]
theorem depth_name {scope : Sig} {count : Nat} (index : Fin count) :
    depth (name (scope := scope) count index) = 2 * index.val + 1 := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index with
      | mk value smaller =>
          cases value with
          | zero => rfl
          | succ value =>
              change depth (name count
                ⟨value, Nat.lt_of_succ_lt_succ smaller⟩) + 1 + 1 =
                  2 * (value + 1) + 1
              rw [induction]
              change 2 * value + 1 + 1 + 1 = 2 * (value + 1) + 1
              omega

@[simp]
theorem depth_equality {scope : Sig} {count : Nat} (index : Fin count) :
    depth (equality (scope := scope) count index) = 2 * index.val := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index with
      | mk value smaller =>
          cases value with
          | zero => rfl
          | succ value =>
              change depth (equality count
                ⟨value, Nat.lt_of_succ_lt_succ smaller⟩) + 1 + 1 =
                  2 * (value + 1)
              rw [induction]
              change 2 * value + 1 + 1 = 2 * (value + 1)
              omega

/-- Different signature slots allocate different target type names. -/
theorem name_injective {scope : Sig} {count : Nat} :
    Function.Injective (name (scope := scope) count) := by
  intro first second same
  have sameDepth := congrArg depth same
  simp only [depth_name] at sameDepth
  apply Fin.ext
  omega

/-- Different signature slots allocate different equality assumptions. -/
theorem equality_injective {scope : Sig} {count : Nat} :
    Function.Injective (equality (scope := scope) count) := by
  intro first second same
  have sameDepth := congrArg depth same
  simp only [depth_equality] at sameDepth
  apply Fin.ext
  omega

theorem name_ne {scope : Sig} {count : Nat} {first second : Fin count}
    (different : first ≠ second) :
    name (scope := scope) count first ≠ name count second :=
  fun same => different (name_injective same)

theorem equality_ne {scope : Sig} {count : Nat} {first second : Fin count}
    (different : first ≠ second) :
    equality (scope := scope) count first ≠ equality count second :=
  fun same => different (equality_injective same)

@[simp]
theorem depth_weaken {scope : Sig} {kind : BinderKind}
    (indexVar : BVar scope kind) (count : Nat) :
    depth ((weaken count).var indexVar) = depth indexVar + 2 * count := by
  induction count with
  | zero => simp [weaken]
  | succ count induction =>
      simp only [weaken, Rename.comp_var, weakenOne, Rename.succ_var, depth]
      rw [induction]
      omega

/-- Every generated name is strictly newer than every ambient type name. -/
theorem name_ne_ambient {scope : Sig} {count : Nat} (index : Fin count)
    (ambient : BVar scope .type) :
    name (scope := scope) count index ≠ (weaken count).var ambient := by
  intro same
  have sameDepth := congrArg depth same
  rw [depth_name, depth_weaken] at sameDepth
  have smaller := index.isLt
  omega

/-- Every generated equality is strictly newer than every ambient equality. -/
theorem equality_ne_ambient {scope : Sig} {count : Nat} (index : Fin count)
    (ambient : BVar scope (.evidence .equality)) :
    equality (scope := scope) count index ≠ (weaken count).var ambient := by
  intro same
  have sameDepth := congrArg depth same
  rw [depth_equality, depth_weaken] at sameDepth
  have smaller := index.isLt
  omega

/-! ## Context lookup and equality transport -/

/-- Every generated equality variable has exactly its advertised endpoints. -/
@[simp]
theorem lookup_equality {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    (extend context anchors).lookup (equality count index) =
      .equality (aliasTy count index) (anchorTy anchors index) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index with
      | mk value smaller =>
          cases value with
          | zero =>
              change Binding.equality
                  (.tvar (.there .here))
                  ((anchors ⟨0, smaller⟩).rename (weaken count) |>.weaken
                    |>.weaken) =
                Binding.equality
                  (aliasTy (count + 1) ⟨0, smaller⟩)
                  (anchorTy anchors ⟨0, smaller⟩)
              congr 1
              unfold anchorTy Ty.weaken
              rw [Ty.rename_comp, Ty.rename_comp]
              change (anchors ⟨0, smaller⟩).rename
                  (((weaken count).comp Rename.succ).comp Rename.succ) =
                (anchors ⟨0, smaller⟩).rename
                  ((weaken count).comp weakenOne)
              unfold weakenOne
              rw [Rename.comp_assoc]
          | succ value =>
              let older : Fin count :=
                ⟨value, Nat.lt_of_succ_lt_succ smaller⟩
              change
                ((extend context (fun i => anchors i.succ)).lookup
                    (equality count older)).weaken.weaken =
                  .equality (aliasTy (count + 1) older.succ)
                    (anchorTy anchors older.succ)
              rw [induction (fun i => anchors i.succ) older]
              simp only [Binding.weaken, Binding.rename, aliasTy, name_succ,
                anchorTy, Ty.rename, Ty.rename_comp, weaken, weakenOne,
                Rename.succ_var, Rename.comp_assoc]

/-- Canonical equality evidence from a fresh alias to its anchor. -/
def toAnchor {scope : Sig} (count : Nat) (index : Fin count) :
    EqCo (Scope scope count) :=
  .var (equality count index)

/-- Canonical equality evidence from an anchor back to its fresh alias. -/
def fromAnchor {scope : Sig} (count : Nat) (index : Fin count) :
    EqCo (Scope scope count) :=
  .symm (toAnchor count index)

/-- Compose alias-to-anchor, an equality between anchors, and
anchor-to-alias. -/
def between {scope : Sig} (count : Nat) (first second : Fin count)
    (anchorsEqual : EqCo (Scope scope count)) : EqCo (Scope scope count) :=
  .trans (toAnchor count first)
    (.trans anchorsEqual (fromAnchor count second))

noncomputable def toAnchor_hasType {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    EqCo.HasType (extend context anchors) (toAnchor count index)
      (aliasTy count index) (anchorTy anchors index) :=
  .var (lookup_equality context anchors index)

noncomputable def fromAnchor_hasType {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    EqCo.HasType (extend context anchors) (fromAnchor count index)
      (anchorTy anchors index) (aliasTy count index) :=
  .symm (toAnchor_hasType context anchors index)

noncomputable def between_hasType {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope)
    (first second : Fin count) {anchorsEqual : EqCo (Scope scope count)}
    (anchorsTyping : EqCo.HasType (extend context anchors) anchorsEqual
      (anchorTy anchors first) (anchorTy anchors second)) :
    EqCo.HasType (extend context anchors)
      (between count first second anchorsEqual)
      (aliasTy count first) (aliasTy count second) :=
  .trans (toAnchor_hasType context anchors first)
    (.trans anchorsTyping (fromAnchor_hasType context anchors second))

/-- Lower-bound transport is directed from anchor to alias, matching the
`lower ≤ fresh-name` proposition of a member telescope. -/
def lower {scope : Sig} (count : Nat) (index : Fin count) :
    LeCo (Scope scope count) :=
  .eqToLe (fromAnchor count index)

/-- Upper-bound transport is directed from alias to anchor, matching the
`fresh-name ≤ upper` proposition of a member telescope. -/
def upper {scope : Sig} (count : Nat) (index : Fin count) :
    LeCo (Scope scope count) :=
  .eqToLe (toAnchor count index)

noncomputable def lower_hasType {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    LeCo.HasType (extend context anchors) (lower count index)
      (anchorTy anchors index) (aliasTy count index) :=
  .eqToLe (fromAnchor_hasType context anchors index)

noncomputable def upper_hasType {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    LeCo.HasType (extend context anchors) (upper count index)
      (aliasTy count index) (anchorTy anchors index) :=
  .eqToLe (toAnchor_hasType context anchors index)

/-! ## Checker-facing certificates -/

theorem synthEq_toAnchor {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    synthEq (extend context anchors) (toAnchor count index) =
      some (aliasTy count index, anchorTy anchors index) :=
  synthEq_complete (toAnchor_hasType context anchors index)

theorem synthEq_fromAnchor {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    synthEq (extend context anchors) (fromAnchor count index) =
      some (anchorTy anchors index, aliasTy count index) :=
  synthEq_complete (fromAnchor_hasType context anchors index)

theorem synthLe_lower {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    synthLe (extend context anchors) (lower count index) =
      some (anchorTy anchors index, aliasTy count index) :=
  synthLe_complete (lower_hasType context anchors index)

theorem synthLe_upper {scope : Sig} (context : Ctx scope)
    {count : Nat} (anchors : Fin count → Ty scope) (index : Fin count) :
    synthLe (extend context anchors) (upper count index) =
      some (aliasTy count index, anchorTy anchors index) :=
  synthLe_complete (upper_hasType context anchors index)

/-! ## Renaming and substitution administration -/

/-- Lift an ambient renaming while preserving every generated alias pair. -/
def liftRename {source target : Sig} (rho : Rename source target) :
    (count : Nat) → Rename (Scope source count) (Scope target count)
  | 0 => rho
  | count + 1 => (liftRename rho count).liftNewtype

/-- One-pair weakening is natural in an ambient renaming. -/
theorem weakenOne_natural {source target : Sig} (rho : Rename source target) :
    (weakenOne (scope := source)).comp rho.liftNewtype =
      rho.comp (weakenOne (scope := target)) := by
  apply Rename.ext
  intro kind indexVar
  rfl

/-- Complete alias weakening is natural in an ambient renaming. -/
theorem weaken_natural {source target : Sig} (rho : Rename source target)
    (count : Nat) :
    (weaken (scope := source) count).comp (liftRename rho count) =
      rho.comp (weaken (scope := target) count) := by
  induction count with
  | zero => simp [weaken, liftRename]
  | succ count induction =>
      simp only [weaken, liftRename, Rename.comp_assoc]
      rw [weakenOne_natural]
      rw [← Rename.comp_assoc, induction, Rename.comp_assoc]

@[simp]
theorem liftRename_name {source target : Sig} (rho : Rename source target)
    {count : Nat} (index : Fin count) :
    (liftRename rho count).var (name (scope := source) count index) =
      name (scope := target) count index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          change BVar.there (BVar.there
              ((liftRename rho count).var
                (name (scope := source) count index))) =
            BVar.there (BVar.there (name (scope := target) count index))
          rw [induction]

@[simp]
theorem liftRename_equality {source target : Sig}
    (rho : Rename source target) {count : Nat} (index : Fin count) :
    (liftRename rho count).var (equality (scope := source) count index) =
      equality (scope := target) count index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          change BVar.there (BVar.there
              ((liftRename rho count).var
                (equality (scope := source) count index))) =
            BVar.there (BVar.there
              (equality (scope := target) count index))
          rw [induction]

@[simp]
theorem aliasTy_rename {source target : Sig} (rho : Rename source target)
    {count : Nat} (index : Fin count) :
    (aliasTy (scope := source) count index).rename (liftRename rho count) =
      aliasTy (scope := target) count index := by
  simp [aliasTy, Ty.rename]

@[simp]
theorem anchorTy_rename {source target : Sig} (rho : Rename source target)
    {count : Nat} (anchors : Fin count → Ty source) (index : Fin count) :
    (anchorTy anchors index).rename (liftRename rho count) =
      anchorTy (fun slot => (anchors slot).rename rho) index := by
  simp only [anchorTy, Ty.rename_comp, weaken_natural]

/-- Lift a four-sort substitution while preserving every generated pair. -/
def liftSubst {source target : Sig} (substitution : Subst source target) :
    (count : Nat) → Subst (Scope source count) (Scope target count)
  | 0 => substitution
  | count + 1 => (liftSubst substitution count).liftNewtype

@[simp]
theorem aliasTy_substitute {source target : Sig}
    (substitution : Subst source target) {count : Nat} (index : Fin count) :
    (aliasTy (scope := source) count index).substitute
        (liftSubst substitution count) =
      aliasTy (scope := target) count index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          change ((liftSubst substitution count).typeVar
              (name (scope := source) count index)).weaken.weaken =
            (aliasTy (scope := target) count index).weaken.weaken
          have inner := induction index
          change (liftSubst substitution count).typeVar
              (name (scope := source) count index) =
            aliasTy (scope := target) count index at inner
          rw [inner]

/-- Substitution commutes with weakening below a complete alias scope. -/
@[simp]
theorem substitute_weaken {source target : Sig} (type : Ty source)
    (substitution : Subst source target) (count : Nat) :
    (type.rename (weaken count)).substitute (liftSubst substitution count) =
      (type.substitute substitution).rename (weaken count) := by
  induction count with
  | zero => simp [weaken, liftSubst]
  | succ count induction =>
      simp only [weaken, liftSubst, weakenOne, ← Ty.rename_comp]
      change (((type.rename (weaken count)).weaken).weaken).substitute
          ((liftSubst substitution count).liftType.liftEquality) =
        (((type.substitute substitution).rename (weaken count)).weaken).weaken
      rw [Ty.substitute_weakenEquality, Ty.substitute_weakenType, induction]

@[simp]
theorem anchorTy_substitute {source target : Sig}
    (substitution : Subst source target) {count : Nat}
    (anchors : Fin count → Ty source) (index : Fin count) :
    (anchorTy anchors index).substitute (liftSubst substitution count) =
      anchorTy (fun slot => (anchors slot).substitute substitution) index :=
  substitute_weaken (anchors index) substitution count

/-! ## Repeated nonescape and `newtype` closure -/

private def newtypeSection {scope : Sig} :
    PartialTypeRename.Square PartialTypeRename.id
      (weakenOne (scope := scope)) Rename.id
      (PartialTypeRename.dropNewtype scope) where
  typeVar := fun _ => by rfl

/-- Weakening an ambient result through one alias pair is a section of
`strengthenNewtype`. -/
@[simp]
theorem strengthenNewtype_weakenOne {scope : Sig} (type : Ty scope) :
    (type.rename weakenOne).strengthenNewtype = some type := by
  simpa only [Ty.strengthenNewtype, Ty.rename?_id, Option.map_some,
    Ty.rename_id] using
    (Ty.rename?_square type PartialTypeRename.id weakenOne Rename.id
      (PartialTypeRename.dropNewtype scope)
      (newtypeSection (scope := scope))).symm

/-- Remove all generated aliases, rejecting a type if any fresh name escapes. -/
def strengthen {scope : Sig} : {count : Nat} →
    Ty (Scope scope count) → Option (Ty scope)
  | 0, type => some type
  | count + 1, type =>
      type.strengthenNewtype >>= strengthen (count := count)

@[simp]
theorem strengthen_weaken {scope : Sig} (type : Ty scope) (count : Nat) :
    strengthen (type.rename (weaken count)) = some type := by
  induction count with
  | zero => simp [strengthen, weaken]
  | succ count induction =>
      change (type.rename (weaken (count + 1))).strengthenNewtype >>=
          strengthen (count := count) = some type
      rw [show type.rename (weaken (count + 1)) =
          (type.rename (weaken count)).rename weakenOne by
        rw [Ty.rename_comp]
        rfl]
      rw [strengthenNewtype_weakenOne]
      exact induction

/-- Close a body by emitting one nested `FCsub.newtype` per alias. -/
def close {scope : Sig} : {count : Nat} →
    (anchors : Fin count → Ty scope) → Tm (Scope scope count) → Tm scope
  | 0, _anchors, body => body
  | count + 1, anchors, body =>
      close (fun index => anchors index.succ)
        (.newtype
          ((anchors ⟨0, Nat.zero_lt_succ count⟩).rename (weaken count)) body)

/-- Nested alias closure preserves every ambient result type. -/
noncomputable def close_hasType {scope : Sig} (context : Ctx scope) :
    {count : Nat} → (anchors : Fin count → Ty scope) →
    {body : Tm (Scope scope count)} → {result : Ty scope} →
    Tm.HasType (extend context anchors) body (result.rename (weaken count)) →
    Tm.HasType context (close anchors body) result
  | 0, _anchors, _body, _result, typing => by
      simpa [close, extend, weaken] using typing
  | count + 1, anchors, body, result, typing => by
      let older := fun index : Fin count => anchors index.succ
      let witness :=
        (anchors ⟨0, Nat.zero_lt_succ count⟩).rename (weaken count)
      have bodyTyping : Tm.HasType
          ((extend context older).extendNewtype witness) body
          ((result.rename (weaken count)).rename weakenOne) := by
        simpa [older, witness, extend, weaken, ← Ty.rename_comp] using typing
      have oneClosed : Tm.HasType (extend context older)
          (.newtype witness body) (result.rename (weaken count)) :=
        .newtype bodyTyping (strengthenNewtype_weakenOne _)
      exact close_hasType context older oneClosed

/-! ## Erasure administration -/

/-- Drop all statically generated alias pairs from an erased body. -/
def eraseAliases {scope : Sig} : {count : Nat} →
    Runtime.Tm (Scope scope count) → Runtime.Tm scope
  | 0, body => body
  | count + 1, body =>
      eraseAliases (count := count)
        (body.subst Runtime.Subst.dropNewtype)

@[simp]
theorem erase_close {scope : Sig} {count : Nat}
    (anchors : Fin count → Ty scope) (body : Tm (Scope scope count)) :
    (close anchors body).erase = eraseAliases body.erase := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [close, eraseAliases]
      exact induction (fun index => anchors index.succ)
        (.newtype
          ((anchors ⟨0, Nat.zero_lt_succ count⟩).rename (weaken count)) body)

end DotToFCsub.M6.AliasScope
