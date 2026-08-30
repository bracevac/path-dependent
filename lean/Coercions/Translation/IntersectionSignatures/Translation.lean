import Coercions.Translation.IntersectionSignatures.SourceFragment
import Coercions.Translation.Acyclic.MemberEncoding

/-!
# Total intersection-signature type and context translation

The translation consumes the explicit stable certificate.  Consequently it
has no option-valued branches: every collectible declaration already owns a
scope-polymorphic signature telescope, and every selection already owns its
successful key lookup.
-/

namespace DotToFCsub.IntersectionSignatures

open DotFCI.Source
open Encoding

namespace SourceFragment

namespace StableType

/-- Total type translation for the certified fragment.  A collectible value
is an existential unit package.  A function over such a value abstracts the
same full telescope and then accepts the one shared unit payload. -/
def translate {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {type : Ty sourceScope} (stable : StableType layout type) :
    FCsub.Ty targetScope :=
  match stable with
  | .top => .top
  | .bot => .bot
  | .signature binding =>
      (binding.encoding targetScope).existsType
  | .sel selection =>
      .tvar selection.lookup.slot.name
  | .allPlain domainStable _ codomainStable =>
      .arr domainStable.translate codomainStable.translate
  | .allSignature binding codomainStable =>
      let encoding := binding.encoding targetScope
      .forallT encoding.telescope (.arr .one codomainStable.translate)

@[simp]
theorem translate_top {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope} :
    translate (StableType.top (layout := layout)) = .top := rfl

@[simp]
theorem translate_bot {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope} :
    translate (StableType.bot (layout := layout)) = .bot := rfl

@[simp]
theorem translate_signature {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {type : Ty sourceScope} (binding : ClosedBinding sourceContext type) :
    translate (StableType.signature (layout := layout) binding) =
      (binding.encoding targetScope).existsType := rfl

@[simp]
theorem translate_selection {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (selection : StableSelection layout path label) :
    translate (StableType.sel selection) =
      .tvar selection.lookup.slot.name := rfl

end StableType

/-! ## Whole-context translation -/

/-- Constructive output of translating a certified source context.  The
target scope is definitionally the exact scope indexed by its layout. -/
structure ContextTranslation {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (layout : ContextLayout.Context sourceContext targetScope) : Type where
  target : FCsub.Ctx targetScope

namespace StableContext

/-- Translate every declaration according to its recorded layout choice.
Each signature case calls `extendPayload` once with the complete telescope. -/
def translate {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    (stable : StableContext layout) : ContextTranslation layout :=
  match stable with
  | .nil => ⟨.nil⟩
  | .plain outerStable typeStable _ =>
      let outerTranslation := translate outerStable
      ⟨outerTranslation.target.extendTerm typeStable.translate⟩
  | .signature outerStable binding =>
      let outerTranslation := translate outerStable
      let encoding := binding.encoding _
      ⟨outerTranslation.target.extendPayload encoding.telescope .one⟩

end StableContext

/-! ## Stable identity and lookup theorems -/

namespace StableSelection

/-- Two occurrence proofs for one key compile to the exact same complete
slot, even if their lower/upper intervals came from different intersections. -/
theorem shared_slot {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (first second : StableSelection layout path label) :
    first.lookup.slot = second.lookup.slot :=
  ContextLayout.MemberLookup.functional first.lookup second.lookup

/-- Projection of overlapping views cannot manufacture a fresh static name. -/
theorem shared_name {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (first second : StableSelection layout path label) :
    first.lookup.slot.name = second.lookup.slot.name :=
  congrArg ContextLayout.MemberSlot.name (shared_slot first second)

/-- All accumulated lower/upper evidence positions are shared with the name. -/
theorem shared_bounds {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (first second : StableSelection layout path label) :
    first.lookup.slot.bounds = second.lookup.slot.bounds :=
  congrArg ContextLayout.MemberSlot.bounds (shared_slot first second)

/-- The runtime representative is likewise one shared payload binder. -/
theorem shared_payload {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : ContextLayout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (first second : StableSelection layout path label) :
    first.lookup.slot.payload = second.lookup.slot.payload :=
  congrArg ContextLayout.MemberSlot.payload (shared_slot first second)

end StableSelection

/-! ## Legacy singleton-layout compatibility -/

namespace LegacySingleton

/-- Canonical metadata for the only entry of a singleton signature. -/
def index (label : Name) : EntryIndex 1 2 where
  label := label
  name := ⟨0, by omega⟩
  bounds :=
    [{ lower := ⟨0, by omega⟩, upper := ⟨1, by omega⟩ }]

@[simp]
theorem singleton_names (label : Name) (lower upper : Ty sourceScope) :
    (Signature.singleton label lower upper).entries.length = 1 := rfl

@[simp]
theorem singleton_constraints (label : Name) (lower upper : Ty sourceScope) :
    signatureConstraintCount
      (Signature.singleton label lower upper).entries = 2 := rfl

/-- The generic allocation pass chooses the canonical singleton metadata. -/
theorem allocation_eq (label : Name) (lower upper : Ty sourceScope) :
    allocation? (Signature.singleton label lower upper) label =
      some (index label) := by
  simp [allocation?, allocations, intervalIndices, index,
    intervalConstraintCount, signatureConstraintCount]

/-- The intersection-signature singleton package has the same exact scope as
the acyclic member convention: one name, two inclusions, then one payload. -/
theorem payload_scope_eq (targetScope : FCsub.Sig) :
    FCsub.PayloadScope targetScope 1 2 =
      DotToFCsub.MemberEncoding.Payload targetScope := rfl

/-- The static name binder is byte-for-byte the legacy singleton name. -/
theorem name_eq (targetScope : FCsub.Sig) (label : Name) :
    (ContextLayout.MemberSlot.ofIndex targetScope label (index label)).name =
      (DotToFCsub.MemberEncoding.name :
        FCsub.BVar (DotToFCsub.MemberEncoding.Payload targetScope) .type) :=
  rfl

/-- The singleton package retains the exact legacy shared payload binder. -/
theorem payload_eq (targetScope : FCsub.Sig) (label : Name) :
    (ContextLayout.MemberSlot.ofIndex targetScope label (index label)).payload =
      (DotToFCsub.MemberEncoding.payload :
        FCsub.BVar (DotToFCsub.MemberEncoding.Payload targetScope) .term) :=
  rfl

/-- The intersection-signature translation uses newest-first finite indices.
Thus the semantic lower position is the legacy upper binder position; this is
only an administrative evidence permutation and does not affect the shared
static name or payload. -/
theorem lower_position_eq_legacy_upper (targetScope : FCsub.Sig)
    (label : Name) :
    ((ContextLayout.MemberSlot.ofIndex targetScope label (index label)).bounds.get
      ⟨0, by simp [ContextLayout.MemberSlot.ofIndex, index]⟩).lower =
      (DotToFCsub.MemberEncoding.upper :
        FCsub.BVar (DotToFCsub.MemberEncoding.Payload targetScope)
          (.evidence .inclusion)) := rfl

/-- The companion upper position is the legacy lower binder position. -/
theorem upper_position_eq_legacy_lower (targetScope : FCsub.Sig)
    (label : Name) :
    ((ContextLayout.MemberSlot.ofIndex targetScope label (index label)).bounds.get
      ⟨0, by simp [ContextLayout.MemberSlot.ofIndex, index]⟩).upper =
      (DotToFCsub.MemberEncoding.lower :
        FCsub.BVar (DotToFCsub.MemberEncoding.Payload targetScope)
          (.evidence .inclusion)) := rfl

end LegacySingleton

end SourceFragment

end DotToFCsub.IntersectionSignatures
