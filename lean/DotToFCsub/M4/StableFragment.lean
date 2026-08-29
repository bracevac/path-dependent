import DotToFCsub.M4.Layout

/-!
# The explicit stable M4 source fragment

This certificate is deliberately narrower than full `DotFCI`.  A declaration
is either represented by one ordinary target term binder, or it is a
collectible member/intersection tree whose bounds have a total closed
top/bottom signature encoding.  Selections additionally carry the successful
layout lookup for their stable `(path,label)` identity.
-/

namespace DotToFCsub.M4.StableFragment

open DotFCI.Source
open SignatureEncoding

/-- A collectible declaration together with the total, scope-polymorphic
encoding of its already-normalized signature. -/
structure ClosedBinding {sourceScope : DotFC.Sig}
    (sourceContext : Ctx sourceScope) (type : Ty sourceScope) : Type where
  signature : Signature sourceScope
  collectible : Collectible sourceContext type signature
  closed : ClosedSignature signature

namespace ClosedBinding

/-- Extend a layout by opening this binding's complete package exactly once. -/
def layout {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {type : Ty sourceScope} {targetScope : FCsub.Sig}
    (binding : ClosedBinding sourceContext type)
    (outer : Layout.Context sourceContext targetScope) :
    Layout.Context (sourceContext.snoc type)
      (FCsub.PayloadScope targetScope binding.signature.entries.length
        (signatureConstraintCount binding.signature.entries)) :=
  .signature binding.signature outer binding.collectible binding.closed

/-- The exact telescope selected by a closed binding at an ambient scope. -/
def encoding {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {type : Ty sourceScope} (binding : ClosedBinding sourceContext type)
    (targetScope : FCsub.Sig) : EncodingAt targetScope binding.signature :=
  binding.closed.encoding targetScope

theorem collected {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {type : Ty sourceScope}
    (binding : ClosedBinding sourceContext type) :
    collect? type = some binding.signature :=
  binding.collectible.collected

end ClosedBinding

/-- Formation of a selection plus its constructive compilation to the unique
target slot for the stable key.  The lower/upper witnesses retain the exact
source occurrence, while lookup depends only on `(path,label)`. -/
structure StableSelection {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (layout : Layout.Context sourceContext targetScope)
    (path : DotFC.BVar sourceScope .term) (label : Name) : Type where
  lower : Ty sourceScope
  upper : Ty sourceScope
  occurrence : MemberOccurrence sourceContext path label lower upper
  allocated : Layout.MemberAllocated layout path label

namespace StableSelection

/-- The structurally derived target lookup for this selection. -/
def lookup {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig}
    {layout : Layout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (selection : StableSelection layout path label) :
    Layout.MemberLookup layout ⟨path, label⟩ :=
  selection.allocated.compile

/-- The stored member occurrence discharges source selection formation. -/
def wf {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig}
    {layout : Layout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (selection : StableSelection layout path label) :
    Wf sourceContext (.sel path label) :=
  .sel selection.occurrence.handle

/-- The selection certificate exposes the executable context lookup equation. -/
theorem compiles {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Layout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (selection : StableSelection layout path label) :
    layout.lookup? ⟨path, label⟩ = some selection.lookup.slot :=
  selection.allocated.compiles

end StableSelection

/-- Types for which M4 layout translation is total.  The two function cases
make the binder representation explicit: a plain domain opens one term,
whereas a collectible domain opens its full names/evidence/payload package. -/
inductive StableType : {sourceScope : DotFC.Sig} →
    {sourceContext : Ctx sourceScope} → {targetScope : FCsub.Sig} →
    (layout : Layout.Context sourceContext targetScope) →
    Ty sourceScope → Type where
  | top {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope} :
      StableType layout .top
  | bot {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope} :
      StableType layout .bot
  | signature {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope}
      {type : Ty sourceScope}
      (binding : ClosedBinding sourceContext type) :
      StableType layout type
  | sel {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term} {label : Name}
      (selection : StableSelection layout path label) :
      StableType layout (.sel path label)
  | allPlain {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope}
      {domain : Ty sourceScope}
      {codomain : Ty (sourceScope ▹ .term)}
      (domainStable : StableType layout domain)
      (shape : Layout.PlainShape domain)
      (codomainStable :
        StableType (Layout.Context.plain layout shape) codomain) :
      StableType layout (.all domain codomain)
  | allSignature {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {layout : Layout.Context sourceContext targetScope}
      {domain : Ty sourceScope}
      {codomain : Ty (sourceScope ▹ .term)}
      (binding : ClosedBinding sourceContext domain)
      (codomainStable : StableType (binding.layout layout) codomain) :
      StableType layout (.all domain codomain)

namespace StableType

/-- Stable translation certificates are, in particular, source formation
derivations. -/
def wf {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig}
    {layout : Layout.Context sourceContext targetScope}
    {type : Ty sourceScope} (stable : StableType layout type) :
    Wf sourceContext type :=
  match stable with
  | .top => .top
  | .bot => .bot
  | .signature binding => binding.collectible.wf
  | .sel selection => selection.wf
  | .allPlain domainStable _ codomainStable =>
      .all domainStable.wf codomainStable.wf
  | .allSignature binding codomainStable =>
      .all binding.collectible.wf codomainStable.wf

end StableType

/-- An entire context whose layout choices and stable type certificates agree
at every declaration. -/
inductive StableContext : {sourceScope : DotFC.Sig} →
    {sourceContext : Ctx sourceScope} → {targetScope : FCsub.Sig} →
    (layout : Layout.Context sourceContext targetScope) → Type where
  | nil : StableContext Layout.Context.nil
  | plain {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {outer : Layout.Context sourceContext targetScope}
      {type : Ty sourceScope}
      (outerStable : StableContext outer)
      (typeStable : StableType outer type)
      (shape : Layout.PlainShape type) :
      StableContext (Layout.Context.plain outer shape)
  | signature {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {outer : Layout.Context sourceContext targetScope}
      {type : Ty sourceScope}
      (outerStable : StableContext outer)
      (binding : ClosedBinding sourceContext type) :
      StableContext (binding.layout outer)

namespace StableContext

/-- Every stable context certificate discharges source context validity. -/
def valid {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig}
    {layout : Layout.Context sourceContext targetScope}
    (stable : StableContext layout) : Ctx.Valid sourceContext :=
  match stable with
  | .nil => .nil
  | .plain outerStable typeStable _ =>
      .snoc outerStable.valid typeStable.wf
  | .signature outerStable binding =>
      .snoc outerStable.valid binding.collectible.wf

end StableContext

end DotToFCsub.M4.StableFragment
