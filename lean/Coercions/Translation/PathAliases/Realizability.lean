import Coercions.Translation.PathAliases.Translation
import Coercions.Translation.PathAliases.CoResolvedEquality
import Coercions.DOT.TraceablePaths.Source.Runtime
import Coercions.FCsub.CheckerCompleteness

/-!
# Realizability for traceable path aliases

Given a finite layout certificate, the path-alias realization theorem combines
three independently checkable pieces:

* source paths carry finite transparent-resolution certificates;
* syntactic `(path, label)` keys receive distinct `newtype` names;
* co-resolution produces explicit equality between those names.

No theorem in this module derives such a layout from arbitrary source typing,
quotients paths, guesses a missing trace, or assigns an identity to a dynamic
receiver.
-/

namespace DotToFCsub.PathAliases

open DotFCRP.Source

/-! ## Ambient weakening through a finite alias scope -/

namespace AliasScope

/-- The generated name/equality pairs extend, but never alter, the ambient
context.  This certificate lets arbitrary ambient typing derivations be
renamed below the complete finite alias scope. -/
noncomputable def extensionRenames {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) : {count : Nat} ->
    (anchors : Fin count -> FCsub.Ty scope) ->
    FCsub.Ctx.Renames context (extend context anchors) (weaken count)
  | 0, _anchors => by
      simpa [extend, weaken] using FCsub.Ctx.Renames.id context
  | count + 1, anchors => by
      let older : Fin count -> FCsub.Ty scope :=
        fun index => anchors index.succ
      let previous := extend context older
      let witness :=
        (anchors ⟨0, Nat.zero_lt_succ count⟩).rename (weaken count)
      have ambient := extensionRenames context older
      have underType := FCsub.Ctx.Renames.weaken previous
        (FCsub.Binding.typeVar)
      have underEquality := FCsub.Ctx.Renames.weaken previous.extendType
        (FCsub.Binding.equality
          (.tvar (.here : FCsub.BVar
            (AliasScope.Scope scope count ▹ .type) .type))
          witness.weaken)
      have underPair := underType.comp underEquality
      have complete := ambient.comp underPair
      simpa [extend, weaken, weakenOne, FCsub.Ctx.extendNewtype,
        older, previous, witness, FCsub.Rename.comp_assoc] using complete

end AliasScope

/-! ## Conditional finite-layout realization -/

/-- The canonical image owned by one exact allocation position. -/
def PathLayout.ownedImage {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target) (index : Fin layout.count) :
    MemberImage layout (layout.keyAt index) where
  index := index
  compiled := layout.owns index

/-- Every allocated source member is tied to one exact recursive-member interface.
Together with `PathLayout.traceAt`, this connects the syntactic path, its
resolved variable anchor, its private name, and its recursive target witness. -/
structure RecursiveLayoutRealization {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target)
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    (encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions) :
    Type where
  memberAt : forall index,
    RecursiveMemberAt encoding (layout.ownedImage index)

/-! ## Coherence of alternative realizations -/

/-- Two realization witnesses for one syntactic key choose the same recursive
member position.  This is endpoint coherence; it does not assert equality of
the proof-relevant trace or realization records. -/
theorem RecursiveMemberAt.memberIndex_eq {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (first second : RecursiveMemberAt encoding image) :
    first.memberIndex = second.memberIndex :=
  encoding.labels.index_eq_of_label_eq first.memberIndex second.memberIndex
    (first.label_eq.trans second.label_eq.symm)

/-- Consequently, alternative realization proofs expose the same exact
target witness endpoint. -/
theorem RecursiveMemberAt.exact_endpoint_eq {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (first second : RecursiveMemberAt encoding image) :
    recursiveExact encoding first.memberIndex =
      recursiveExact encoding second.memberIndex := by
  rw [first.memberIndex_eq second]

/-- Co-resolved paths selecting the same label also agree on the exact recursive
member position, even though their private alias names remain distinct. -/
theorem RecursiveMemberAt.memberIndex_eq_of_pathEq
    {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (leftRealization : RecursiveMemberAt encoding left)
    (rightRealization : RecursiveMemberAt encoding right)
    (equality : MemberPathEq left right) :
    leftRealization.memberIndex = rightRealization.memberIndex :=
  encoding.labels.index_eq_of_label_eq leftRealization.memberIndex
    rightRealization.memberIndex
    (leftRealization.label_eq.trans
      (equality.label_eq.trans rightRealization.label_eq.symm))

/-! ## Singleton/path-equality realization -/

/-- Singleton view of one certified co-resolution member equality.  The
lower and upper fields show both directed uses of the equality on the exact
recursive witness, with the orientations checked by FCsub.  This structure does not
turn an arbitrary singleton hypothesis into a trace certificate. -/
structure SingletonMemberRealization {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (leftRealization : RecursiveMemberAt encoding left)
    (rightRealization : RecursiveMemberAt encoding right)
    (equality : MemberPathEq left right)
    (context : FCsub.Ctx target) : Type where
  sameMember : leftRealization.memberIndex = rightRealization.memberIndex
  targetEquality : FCsub.EqCo.HasType
    (AliasScope.extend context layout.anchorType)
    equality.evidence left.aliasType right.aliasType
  transportedLower : FCsub.LeCo.HasType
    (AliasScope.extend context layout.anchorType)
    (equality.transportLower leftRealization.lower)
    ((recursiveExact encoding leftRealization.memberIndex).rename
      (AliasScope.weaken layout.count)) right.aliasType
  transportedUpper : FCsub.LeCo.HasType
    (AliasScope.extend context layout.anchorType)
    (equality.transportUpper leftRealization.upper)
    right.aliasType
    ((recursiveExact encoding leftRealization.memberIndex).rename
      (AliasScope.weaken layout.count))

/-- Construct the singleton view from a proof-relevant source co-resolution
certificate. -/
noncomputable def realizeSingletonMember {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (leftRealization : RecursiveMemberAt encoding left)
    (rightRealization : RecursiveMemberAt encoding right)
    (equality : MemberPathEq left right)
    (context : FCsub.Ctx target) :
    SingletonMemberRealization leftRealization rightRealization equality
      context where
  sameMember := leftRealization.memberIndex_eq_of_pathEq
    rightRealization equality
  targetEquality := equality.evidence_hasType context
  transportedLower := equality.transportLower_hasType context
    (leftRealization.lower_hasType context)
  transportedUpper := equality.transportUpper_hasType context
    (leftRealization.upper_hasType context)

/-! ## Closing the recursive object below all generated aliases -/

/-- Wrap the recursive package in one existing FCsub `newtype` per
syntactic member key.  The object itself is only weakened; all wrappers are
static and are eliminated again by `AliasScope.close`. -/
def aliasedRecursiveObject {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target)
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    (encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions) :
    FCsub.Tm target :=
  AliasScope.close layout.anchorType
    (encoding.object.rename (AliasScope.weaken layout.count))

/-- The complete alias allocation preserves the recursive package type. -/
noncomputable def aliasedRecursiveObject_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target) (context : FCsub.Ctx target)
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    (encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions) :
    FCsub.Tm.HasType context (aliasedRecursiveObject layout encoding)
      encoding.objectType := by
  apply AliasScope.close_hasType context layout.anchorType
  exact (encoding.object_typed (context := context)).rename
    (AliasScope.extensionRenames context layout.anchorType)

namespace AliasScope

/-- Erasing any number of generated alias pairs from runtime unit is unit. -/
@[simp]
theorem eraseAliases_unit {scope : FCsub.Sig} (count : Nat) :
    eraseAliases (count := count)
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm (Scope scope count)) =
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm scope) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change eraseAliases (count := count)
        ((FCsub.Runtime.Tm.unit :
          FCsub.Runtime.Tm (Scope scope (count + 1))).subst
            FCsub.Runtime.Subst.dropNewtype) = .unit
      exact induction

end AliasScope

/-- All newly generated names, equality fields, and recursive interface
annotations erase; the resulting runtime program is unit. -/
@[simp]
theorem erase_aliasedRecursiveObject {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target)
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    (encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions) :
    (aliasedRecursiveObject layout encoding).erase =
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm target) := by
  rw [aliasedRecursiveObject, AliasScope.erase_close,
    FCsub.Tm.erase_rename]
  change AliasScope.eraseAliases
    ((FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm target).rename
      (AliasScope.weaken layout.count)) = .unit
  simpa only [FCsub.Runtime.Tm.rename] using
    (AliasScope.eraseAliases_unit (scope := target) layout.count)

/-- Full realization of a supplied finite path layout over a recursive-object
interface. -/
structure AliasedRecursiveObjectRealization {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    (layout : PathLayout store target)
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    (encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions)
    (context : FCsub.Ctx target) : Type where
  pathMembers : RecursiveLayoutRealization layout encoding
  targetTyping : FCsub.Tm.HasType context
    (aliasedRecursiveObject layout encoding) encoding.objectType
  checkerAccepts : FCsub.checkTerm context
    (aliasedRecursiveObject layout encoding) encoding.objectType = true
  erasesToUnit : (aliasedRecursiveObject layout encoding).erase =
    (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm target)
  reachesUnit : FCsub.Runtime.Steps
    (aliasedRecursiveObject layout encoding).erase
    (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm target)

/-- Construct the complete typed, checker-accepted, runtime-reachable
path-aliased object from the finite trace/member realization. -/
noncomputable def realizeAliasedRecursiveObject {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)}
    {encoding : DotToFCsub.RecursiveObjects.Encoding (target := target) definitions}
    (pathMembers : RecursiveLayoutRealization layout encoding)
    (context : FCsub.Ctx target) :
    AliasedRecursiveObjectRealization layout encoding context := by
  have typing := aliasedRecursiveObject_hasType layout context encoding
  refine
    { pathMembers := pathMembers
      targetTyping := typing
      checkerAccepts := FCsub.checkTerm_iff.mpr ⟨typing⟩
      erasesToUnit := erase_aliasedRecursiveObject layout encoding
      reachesUnit := ?_ }
  rw [erase_aliasedRecursiveObject]
  exact .refl

/-! ## Honest unsupported boundary -/

/-- A key absent from the finite allocation has no certified member image. -/
theorem unallocated_not_translatable {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (missing : translateMember? layout key = none) :
    MemberImage layout key -> False := by
  intro image
  rw [translateMember_image image] at missing
  contradiction

/-- A path for which no trace can be supplied cannot form a `PathImage`. -/
theorem unresolved_not_pathImage {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {path : Path source}
    (unresolved : forall anchor, Traceable store path anchor -> False) :
    PathImage layout path -> False := by
  intro image
  exact unresolved image.anchor image.trace

/-- Dynamic receivers are outside the traceable path-alias translation boundary. -/
theorem dynamic_receiver_untranslatable {scope : DotFC.Sig}
    (store : AliasStore scope) (term : DotFCRP.Source.Runtime.Tm scope) :
    DotFCRP.Source.Runtime.TraceableReceiver store (.dynamic term) -> False :=
  DotFCRP.Source.Runtime.dynamic_not_traceable store term

/-- Weakening an ambient certified path below a term binder never aliases it
with the fresh variable. -/
theorem weakened_path_not_fresh {scope : DotFC.Sig}
    {store : AliasStore scope} {path : Path scope}
    {anchor : DotFC.BVar scope .term}
    (trace : Traceable store path anchor) :
    CoResolved (store.weaken (kind := .term)) path.weaken (.var .here) ->
      False :=
  weakened_not_coResolved_fresh trace

end DotToFCsub.PathAliases
