import Coercions.Translation.PathAliases.PathLayout
import Coercions.DOT.TraceablePaths.Source.Typing

/-!
# Explicit equality for co-resolved path members

Two syntactically different keys keep different generated FCsub names.  When
their paths co-resolve and their labels agree, this module composes each
fresh name's equality-to-anchor through the common anchor.  No allocation is
identified or quotiented.
-/

namespace DotToFCsub.PathAliases

open DotFCRP.Source

/-- The exact source premises for transporting one selected member identity. -/
structure MemberPathEq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    (left : MemberImage layout leftKey)
    (right : MemberImage layout rightKey) where
  paths : CoResolved store leftKey.path rightKey.path
  label_eq : leftKey.label = rightKey.label

namespace MemberPathEq

/-- Certified transparent co-resolution supplies the source singleton view
that the path-alias translation supports.  This is intentionally one-way: arbitrary singleton
hypotheses are not resolved outside the finite alias store. -/
def singletonSub {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (context : DotFCRP.Source.Ctx source) :
    DotFCRP.Source.Sub store context
      (.singleton leftKey.path) (.singleton rightKey.path) :=
  .singletonEq equality.paths

theorem left_anchor_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    left.anchor = equality.paths.anchor :=
  Traceable.deterministic left.trace equality.paths.leftTrace

theorem right_anchor_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    right.anchor = equality.paths.anchor :=
  Traceable.deterministic right.trace equality.paths.rightTrace

/-- Co-resolved member images have the same retained variable anchor. -/
theorem anchors_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    left.anchor = right.anchor :=
  equality.left_anchor_eq.trans equality.right_anchor_eq.symm

private theorem allocated_labels_eq {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    (layout.keyAt left.index).label =
      (layout.keyAt right.index).label := by
  rw [left.key_eq, right.key_eq]
  exact equality.label_eq

/-- Anchor identity is coherent for the common source anchor and label. -/
theorem ambientAnchorType_eq {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    left.ambientAnchorType = right.ambientAnchorType :=
  layout.anchorType_coherent left.index right.index
    equality.anchors_eq (allocated_labels_eq equality)

/-- The same anchor equality after weakening through all fresh alias pairs. -/
theorem anchorType_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) :
    left.anchorType = right.anchorType := by
  change
    (layout.anchorType left.index).rename
        (AliasScope.weaken layout.count) =
      (layout.anchorType right.index).rename
        (AliasScope.weaken layout.count)
  exact congrArg
    (fun type => type.rename (AliasScope.weaken layout.count))
    equality.ambientAnchorType_eq

/-- Explicit target equality: left alias to anchor, reflexive equality at the
common anchor, then anchor to right alias. -/
def evidence {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (_equality : MemberPathEq left right) :
    FCsub.EqCo (AliasScope.Scope target layout.count) :=
  AliasScope.between layout.count left.index right.index
    (.refl left.anchorType)

/-- The co-resolution certificate compiles to independently checked FCsub
equality evidence with the two separately allocated names as endpoints. -/
noncomputable def evidence_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target) :
    FCsub.EqCo.HasType (AliasScope.extend context layout.anchorType)
      equality.evidence left.aliasType right.aliasType := by
  have anchorsTyping : FCsub.EqCo.HasType
      (AliasScope.extend context layout.anchorType)
      (.refl left.anchorType) left.anchorType right.anchorType := by
    exact Eq.rec (motive := fun targetType _equal =>
        FCsub.EqCo.HasType
          (AliasScope.extend context layout.anchorType)
          (.refl left.anchorType) left.anchorType targetType)
      (.refl left.anchorType) equality.anchorType_eq
  apply AliasScope.between_hasType context layout.anchorType
    left.index right.index
  exact anchorsTyping

/-- Alternative trace or co-resolution proof trees compile to the same
certificate syntax; proof relevance changes neither target endpoints nor
allocation. -/
theorem evidence_coherent {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (first second : MemberPathEq left right) :
    first.evidence = second.evidence := rfl

/-- Same-label evidence is deliberately unavailable for different labels. -/
theorem different_label_rejected {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (different : leftKey.label ≠ rightKey.label) :
    MemberPathEq left right -> False := by
  intro equality
  exact different equality.label_eq

/-! ## Directed bound transport -/

/-- Transport a lower-bound certificate `L <= left.A` to `L <= right.A`. -/
def transportLower {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (lower : FCsub.LeCo (AliasScope.Scope target layout.count)) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  .trans lower (.eqToLe equality.evidence)

noncomputable def transportLower_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target)
    {lower : FCsub.LeCo (AliasScope.Scope target layout.count)}
    {bound : FCsub.Ty (AliasScope.Scope target layout.count)}
    (lowerTyping : FCsub.LeCo.HasType
      (AliasScope.extend context layout.anchorType)
      lower bound left.aliasType) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      (equality.transportLower lower) bound right.aliasType :=
  .trans lowerTyping (.eqToLe (equality.evidence_hasType context))

/-- Transport an upper-bound certificate `left.A <= U` to `right.A <= U`. -/
def transportUpper {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (upper : FCsub.LeCo (AliasScope.Scope target layout.count)) :
    FCsub.LeCo (AliasScope.Scope target layout.count) :=
  .trans (.eqToLe (.symm equality.evidence)) upper

noncomputable def transportUpper_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target)
    {upper : FCsub.LeCo (AliasScope.Scope target layout.count)}
    {bound : FCsub.Ty (AliasScope.Scope target layout.count)}
    (upperTyping : FCsub.LeCo.HasType
      (AliasScope.extend context layout.anchorType)
      upper left.aliasType bound) :
    FCsub.LeCo.HasType (AliasScope.extend context layout.anchorType)
      (equality.transportUpper upper) right.aliasType bound :=
  .trans (.eqToLe (.symm (equality.evidence_hasType context))) upperTyping

end MemberPathEq

/-! ## Finite path-image alignment -/

/-- Aligned positions of two path images yield same-label member equality. -/
def PathImage.alignedMemberEq {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {leftPath rightPath : Path source}
    (left : PathImage layout leftPath) (right : PathImage layout rightPath)
    (alignment : LabelAlignment left.labelLayout right.labelLayout)
    (paths : CoResolved store leftPath rightPath)
    (index : Fin left.labels.length) :
    MemberPathEq (left.member index)
      (right.member (alignment.forward index)) where
  paths := paths
  label_eq := (alignment.forward_label index).symm

/-! ## Allocation remains unquotiented -/

/-- Distinct keys retain distinct alias types even when path equality later
relates those types by an explicit certificate. -/
theorem MemberImage.aliasType_ne_of_key_ne {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    (left : MemberImage layout leftKey)
    (right : MemberImage layout rightKey)
    (different : leftKey ≠ rightKey) :
    left.aliasType ≠ right.aliasType := by
  intro same
  simp only [MemberImage.aliasType, AliasScope.aliasTy] at same
  have namesEqual : AliasScope.name (scope := target) layout.count left.index =
      AliasScope.name (scope := target) layout.count right.index := by
    injection same
  exact left.index_ne_of_key_ne right different
    (AliasScope.name_injective namesEqual)

end DotToFCsub.PathAliases
