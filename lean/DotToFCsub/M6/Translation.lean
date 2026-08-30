import DotToFCsub.M6.PathLayout
import DotToFCsub.M5.Realizability

/-!
# Translation of traceable path members

M6 deliberately allocates by the syntactic key `(path, label)`.  Successful
lookup therefore produces a fresh target name even when another path is
known to resolve to the same source object.  Equality between such names is
an explicit coercion, developed separately in `PathEquality`; it never
changes this allocation table.

This module also connects a finite path layout to the exact recursive-member
interface constructed in M5.  Each source slot retains its transparent trace
and identifies its ambient target anchor with one M5 recursive projection.
-/

namespace DotToFCsub.M6

open DotFCRP.Source

/-! ## Executable member translation -/

/-- Translate one allocated `(path, label)` key to its private target name.
Failure is honest: an absent key has no target approximation. -/
def translateMember? {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} (layout : PathLayout store target)
    (key : MemberKey source) :
    Option (FCsub.Ty (AliasScope.Scope target layout.count)) :=
  (layout.index? key).map fun index =>
    AliasScope.aliasTy layout.count index

@[simp]
theorem translateMember_image {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (image : MemberImage layout key) :
    translateMember? layout key = some image.aliasType := by
  unfold translateMember?
  rw [image.compiled]
  rfl

/-- Translation of an exact syntactic key is functional. -/
theorem translated_member_functional {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (first second : MemberImage layout key) :
    first.aliasType = second.aliasType :=
  MemberImage.aliasType_eq first second

/-- Distinct syntactic keys retain distinct generated target identities.
This remains true even if their paths later receive singleton equality. -/
theorem translated_member_distinct {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {firstKey secondKey : MemberKey source}
    (first : MemberImage layout firstKey)
    (second : MemberImage layout secondKey)
    (different : firstKey ≠ secondKey) :
    first.aliasType ≠ second.aliasType := by
  intro equalTypes
  have equalNames :
      AliasScope.name (scope := target) layout.count first.index =
        AliasScope.name layout.count second.index := by
    simpa [MemberImage.aliasType, AliasScope.aliasTy] using equalTypes
  exact (first.index_ne_of_key_ne second different)
    (AliasScope.name_injective equalNames)

/-! ## Directed bound transport -/

/-- If a lower bound reaches the ambient anchor, continue through equality
from that anchor to the freshly allocated alias. -/
def transportLower {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key)
    (lower : FCsub.LeCo (AliasScope.Scope target layout.count)) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  .trans lower (AliasScope.lower layout.count image.index)

/-- To expose an upper bound, first move from the fresh alias to its ambient
anchor and then follow the original upper certificate. -/
def transportUpper {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key)
    (upper : FCsub.LeCo (AliasScope.Scope target layout.count)) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  .trans (AliasScope.upper layout.count image.index) upper

noncomputable def transportLower_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (image : MemberImage layout key) (context : FCsub.Ctx target)
    {lower : FCsub.LeCo (AliasScope.Scope target layout.count)}
    {lowerType : FCsub.Ty (AliasScope.Scope target layout.count)}
    (lowerTyping : FCsub.LeCo.HasType
      (AliasScope.extend context layout.anchorType) lower lowerType
      image.anchorType) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      (transportLower image lower) lowerType image.aliasType :=
  .trans lowerTyping
    (AliasScope.lower_hasType context layout.anchorType image.index)

noncomputable def transportUpper_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (image : MemberImage layout key) (context : FCsub.Ctx target)
    {upper : FCsub.LeCo (AliasScope.Scope target layout.count)}
    {upperType : FCsub.Ty (AliasScope.Scope target layout.count)}
    (upperTyping : FCsub.LeCo.HasType
      (AliasScope.extend context layout.anchorType) upper image.anchorType
      upperType) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      (transportUpper image upper) image.aliasType upperType :=
  .trans (AliasScope.upper_hasType context layout.anchorType image.index)
    upperTyping

/-! ## Specialization to the M5 recursive interface -/

/-- Ambient identity of one exact M5 recursive member. -/
def recursiveAnchor {target : FCsub.Sig}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    (encoding : DotToFCsub.M5.Encoding (target := target) definitions)
    (index : Fin definitions.length) : FCsub.Ty target :=
  .recProj encoding.block (DotToFCsub.M5.memberIndex index)

/-- The corresponding instantiated exact M5 witness. -/
def recursiveExact {target : FCsub.Sig}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    (encoding : DotToFCsub.M5.Encoding (target := target) definitions)
    (index : Fin definitions.length) : FCsub.Ty target :=
  (encoding.translation.witness index).instantiateNames encoding.witnesses

/-- One allocated path member is realized by a public member of an M5
recursive interface.  The source trace is retained by `image.trace`; the
fields below align its label and target anchor with the exact M5 slot. -/
structure RecursiveMemberAt {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    (encoding : DotToFCsub.M5.Encoding (target := target) definitions)
    (image : MemberImage layout key) : Type where
  memberIndex : Fin definitions.length
  label_eq : (definitions.get memberIndex).label = key.label
  anchorType_eq : image.ambientAnchorType =
    recursiveAnchor encoding memberIndex

namespace RecursiveMemberAt

/-- The source half of a recursive-member realization is a complete trace
from the syntactic path to the layout's retained variable anchor. -/
def trace {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (_realization : RecursiveMemberAt encoding image) :
    Traceable store key.path image.anchor :=
  image.trace

/-- Canonical M5 unfolding equality, renamed below all generated aliases. -/
def equality {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image) :
    FCsub.EqCo (AliasScope.Scope target layout.count) :=
  (FCsub.EqCo.unfoldRec encoding.block
    (DotToFCsub.M5.memberIndex realization.memberIndex)).rename
      (AliasScope.weaken layout.count)

noncomputable def equality_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image)
    (context : FCsub.Ctx target) :
    FCsub.EqCo.HasType (AliasScope.extend context layout.anchorType)
      realization.equality image.anchorType
      ((recursiveExact encoding realization.memberIndex).rename
        (AliasScope.weaken layout.count)) := by
  have guarded :
      (encoding.block.rename (AliasScope.weaken layout.count)).headGuarded =
        true := by
    simpa only [FCsub.RecBodies.headGuarded_rename] using encoding.guarded
  have typing := FCsub.EqCo.HasType.unfoldRec
    (context := AliasScope.extend context layout.anchorType)
    (index := DotToFCsub.M5.memberIndex realization.memberIndex) guarded
  have anchorEqual : image.anchorType =
      (recursiveAnchor encoding realization.memberIndex).rename
        (AliasScope.weaken layout.count) := by
    change (layout.anchorType image.index).rename
      (AliasScope.weaken layout.count) = _
    have ambientEqual : layout.anchorType image.index =
        recursiveAnchor encoding realization.memberIndex :=
      realization.anchorType_eq
    rw [ambientEqual]
  have unfoldEqual :
      (encoding.block.rename (AliasScope.weaken layout.count)).unfoldAt
          (DotToFCsub.M5.memberIndex realization.memberIndex) =
        (recursiveExact encoding realization.memberIndex).rename
          (AliasScope.weaken layout.count) := by
    rw [← FCsub.RecBodies.unfoldAt_rename]
    simpa [recursiveExact, DotToFCsub.M5.Encoding.block,
      DotToFCsub.M5.Encoding.witnesses] using
        congrArg
          (fun type => type.rename (AliasScope.weaken layout.count))
          (encoding.unfolds realization.memberIndex)
  rw [anchorEqual]
  rw [unfoldEqual] at typing
  simpa only [equality, FCsub.EqCo.rename, recursiveAnchor,
    FCsub.Ty.rename] using typing

/-- Exact lower transport: witness to M5 anchor, then anchor to alias. -/
def lower {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  transportLower image (.eqToLe (.symm realization.equality))

/-- Exact upper transport: alias to M5 anchor, then anchor to witness. -/
def upper {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  transportUpper image (.eqToLe realization.equality)

noncomputable def lower_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image)
    (context : FCsub.Ctx target) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      realization.lower
      ((recursiveExact encoding realization.memberIndex).rename
        (AliasScope.weaken layout.count)) image.aliasType :=
  transportLower_hasType image context
    (.eqToLe (.symm (realization.equality_hasType context)))

noncomputable def upper_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    {definitions : List (DotFCR.Source.TypeDef DotToFCsub.M5.ClosedSelfScope)}
    {encoding : DotToFCsub.M5.Encoding (target := target) definitions}
    {image : MemberImage layout key}
    (realization : RecursiveMemberAt encoding image)
    (context : FCsub.Ctx target) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      realization.upper image.aliasType
      ((recursiveExact encoding realization.memberIndex).rename
        (AliasScope.weaken layout.count)) :=
  transportUpper_hasType image context
    (.eqToLe (realization.equality_hasType context))

end RecursiveMemberAt

end DotToFCsub.M6
