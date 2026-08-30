import Coercions.DOT.TraceablePaths.Source.Trace
import Coercions.Translation.PathAliases.AliasScope

/-!
# Finite layouts for traceable path members

The path-alias translation keeps allocation keyed by the syntactic pair
`(path, label)`.  Path
equality never changes this table: every key owns a distinct private FCsub
name, while `CoResolvedEquality` constructs explicit equality evidence between
names whose paths co-resolve.
-/

namespace DotToFCsub.PathAliases

open DotFCRP.Source

/-- The unquotiented source key used by path-member allocation. -/
structure MemberKey (scope : DotFC.Sig) where
  path : Path scope
  label : Name
deriving DecidableEq

/-- A finite, executable label order with proof-relevant lookup. -/
structure LabelLayout (labels : List Name) where
  index? : Name -> Option (Fin labels.length)
  owns : forall index, index? (labels.get index) = some index
  sound : forall label index, index? label = some index ->
    labels.get index = label

/-- Successful lookup in a finite label order. -/
structure LabelAt {labels : List Name} (layout : LabelLayout labels)
    (label : Name) where
  index : Fin labels.length
  compiled : layout.index? label = some index

namespace LabelAt

theorem label_eq {labels : List Name} {layout : LabelLayout labels}
    {label : Name} (found : LabelAt layout label) :
    labels.get found.index = label :=
  layout.sound label found.index found.compiled

theorem functional {labels : List Name} {layout : LabelLayout labels}
    {label : Name} (first second : LabelAt layout label) :
    first.index = second.index := by
  have same := second.compiled
  rw [first.compiled] at same
  exact Option.some.inj same

end LabelAt

/-- A bijective alignment between two finite label orders.  The orders may
differ, but corresponding positions carry exactly the same source label. -/
structure LabelAlignment {left right : List Name}
    (leftLayout : LabelLayout left) (rightLayout : LabelLayout right) where
  forward : Fin left.length -> Fin right.length
  backward : Fin right.length -> Fin left.length
  forward_label : forall index,
    right.get (forward index) = left.get index
  backward_label : forall index,
    left.get (backward index) = right.get index
  left_inverse : forall index, backward (forward index) = index
  right_inverse : forall index, forward (backward index) = index

namespace LabelAlignment

def refl {labels : List Name} (layout : LabelLayout labels) :
    LabelAlignment layout layout where
  forward := id
  backward := id
  forward_label := fun _ => rfl
  backward_label := fun _ => rfl
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl

theorem forward_injective {left right : List Name}
    {leftLayout : LabelLayout left} {rightLayout : LabelLayout right}
    (alignment : LabelAlignment leftLayout rightLayout) :
    Function.Injective alignment.forward := by
  intro first second same
  have := congrArg alignment.backward same
  simpa [alignment.left_inverse] using this

end LabelAlignment

/-- One finite allocation table for all member keys currently in scope.

`anchorAt` and `traceAt` retain the source path's canonical variable.  The
ambient `anchorType` is the target member identity at that variable.  The
last field states the only semantic coherence needed by path equality: the
same source anchor and label have the same ambient target type.
-/
structure PathLayout {source : DotFC.Sig} (store : AliasStore source)
    (target : FCsub.Sig) where
  count : Nat
  keyAt : Fin count -> MemberKey source
  anchorAt : Fin count -> DotFC.BVar source .term
  traceAt : forall index,
    Traceable store (keyAt index).path (anchorAt index)
  anchorType : Fin count -> FCsub.Ty target
  index? : MemberKey source -> Option (Fin count)
  owns : forall index, index? (keyAt index) = some index
  sound : forall key index, index? key = some index -> keyAt index = key
  anchorType_coherent : forall first second,
    anchorAt first = anchorAt second ->
    (keyAt first).label = (keyAt second).label ->
    anchorType first = anchorType second

/-- Proof-relevant successful allocation of one syntactic member key. -/
structure MemberImage {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} (layout : PathLayout store target)
    (key : MemberKey source) where
  index : Fin layout.count
  compiled : layout.index? key = some index

namespace MemberImage

theorem key_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    layout.keyAt image.index = key :=
  layout.sound key image.index image.compiled

/-- The source anchor retained by this exact allocation slot. -/
def anchor {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    DotFC.BVar source .term :=
  layout.anchorAt image.index

/-- The allocation slot carries a complete transparent trace to its anchor. -/
def trace {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    Traceable store key.path image.anchor := by
  simpa only [image.key_eq] using layout.traceAt image.index

/-- Ambient target identity of the member at the resolved anchor. -/
def ambientAnchorType {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    FCsub.Ty target :=
  layout.anchorType image.index

/-- Fresh, separately allocated target identity of this syntactic key. -/
def aliasType {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    FCsub.Ty (AliasScope.Scope target layout.count) :=
  AliasScope.aliasTy layout.count image.index

/-- The anchor identity weakened below every fresh alias pair. -/
def anchorType {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    FCsub.Ty (AliasScope.Scope target layout.count) :=
  AliasScope.anchorTy layout.anchorType image.index

/-- Canonical explicit equality from this fresh name to its anchor name. -/
def toAnchor {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    FCsub.EqCo (AliasScope.Scope target layout.count) :=
  AliasScope.toAnchor layout.count image.index

/-- Canonical explicit equality from the anchor name back to this fresh name. -/
def fromAnchor {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (image : MemberImage layout key) :
    FCsub.EqCo (AliasScope.Scope target layout.count) :=
  AliasScope.fromAnchor layout.count image.index

/-- Executable allocation lookup is functional for an exact syntactic key. -/
theorem functional {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (first second : MemberImage layout key) :
    first.index = second.index := by
  have same := second.compiled
  rw [first.compiled] at same
  exact Option.some.inj same

theorem aliasType_eq {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {key : MemberKey source} (first second : MemberImage layout key) :
    first.aliasType = second.aliasType := by
  simp only [aliasType]
  rw [functional first second]

/-- Distinct syntactic keys necessarily occupy distinct allocation slots. -/
theorem index_ne_of_key_ne {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {firstKey secondKey : MemberKey source}
    (first : MemberImage layout firstKey)
    (second : MemberImage layout secondKey)
    (different : firstKey ≠ secondKey) : first.index ≠ second.index := by
  intro same
  apply different
  calc
    firstKey = layout.keyAt first.index := first.key_eq.symm
    _ = layout.keyAt second.index := congrArg layout.keyAt same
    _ = secondKey := second.key_eq

noncomputable def toAnchor_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (image : MemberImage layout key) (context : FCsub.Ctx target) :
    FCsub.EqCo.HasType (AliasScope.extend context layout.anchorType)
      image.toAnchor image.aliasType image.anchorType :=
  AliasScope.toAnchor_hasType context layout.anchorType image.index

noncomputable def fromAnchor_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target} {key : MemberKey source}
    (image : MemberImage layout key) (context : FCsub.Ctx target) :
    FCsub.EqCo.HasType (AliasScope.extend context layout.anchorType)
      image.fromAnchor image.anchorType image.aliasType :=
  AliasScope.fromAnchor_hasType context layout.anchorType image.index

end MemberImage

namespace PathLayout

/-- Compile an executable key lookup to its proof-relevant member image. -/
def image? {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} (layout : PathLayout store target)
    (key : MemberKey source) : Option (MemberImage layout key) :=
  match found : layout.index? key with
  | none => none
  | some index => some { index := index, compiled := found }

end PathLayout

/-- One traceable path together with its complete finite member image. -/
structure PathImage {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} (layout : PathLayout store target)
    (path : Path source) where
  anchor : DotFC.BVar source .term
  trace : Traceable store path anchor
  labels : List Name
  labelLayout : LabelLayout labels
  member : forall index,
    MemberImage layout { path := path, label := labels.get index }

namespace PathImage

/-- Every member slot of a path resolves to the path image's one anchor. -/
theorem member_anchor {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {path : Path source} (image : PathImage layout path)
    (index : Fin image.labels.length) :
    (image.member index).anchor = image.anchor :=
  Traceable.deterministic (image.member index).trace image.trace

/-- Select a member image through proof-relevant finite label lookup. -/
def memberAt {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {path : Path source} (image : PathImage layout path) {label : Name}
    (found : LabelAt image.labelLayout label) :
    MemberImage layout { path := path, label := label } := by
  simpa only [← found.label_eq] using image.member found.index

end PathImage

end DotToFCsub.PathAliases
