import FCsub.ClosedArtifact
import DotFCR
import DotFCRP

/-!
# Executable syntax and generation metrics

Every counter in this module is structural: one is charged for the outer
constructor and then the counters of all syntax stored by that constructor
are added.  Variables, finite indices, and numeric labels are payloads rather
than syntax nodes.  Lists of source definitions charge one node per
`TypeDef`, but do not separately charge list constructors.

The module has no dependency on the M7 compiler.  A compiler supplies its own
source-node count and generation counts to `Metrics.ofArtifact`; the target
and erased counts and checker result are then obtained independently from the
proof-free closed FCsub artifact.
-/

namespace DotToFCsub.M7

namespace NodeCount

/-! ## Standalone FCsub -/

mutual

/-- Nodes in an FCsub type, including embedded telescope and recursive-block
syntax. -/
def fcTy {scope : FCsub.Sig} : FCsub.Ty scope -> Nat
  | .top => 1
  | .bot => 1
  | .one => 1
  | .tvar _ => 1
  | .arr domain codomain => 1 + fcTy domain + fcTy codomain
  | .existsT telescope payload =>
      1 + fcTelescope telescope + fcTy payload
  | .forallT telescope body =>
      1 + fcTelescope telescope + fcTy body
  | .recProj bodies _ => 1 + fcRecBodies bodies

/-- Nodes in a simultaneous FCsub recursive body vector. -/
def fcRecBodies {scope : FCsub.Sig} {bound count : Nat} :
    FCsub.RecBodies scope bound count -> Nat
  | .nil => 1
  | .snoc initial body => 1 + fcRecBodies initial + fcTy body

/-- Nodes in one FCsub telescope proposition. -/
def fcProposition {scope : FCsub.Sig} : FCsub.Proposition scope -> Nat
  | .inclusion source target => 1 + fcTy source + fcTy target

/-- Nodes in an FCsub telescope, including its proposition types. -/
def fcTelescope {scope : FCsub.Sig} {names constraints : Nat} :
    FCsub.Telescope scope names constraints -> Nat
  | .nil => 1
  | .snoc initial proposition =>
      1 + fcTelescope initial + fcProposition proposition

end

/-- Nodes in simultaneous FCsub type witnesses. -/
def fcTypeArgs {scope : FCsub.Sig} {count : Nat} :
    FCsub.TypeArgs scope count -> Nat
  | .nil => 1
  | .snoc initial type => 1 + fcTypeArgs initial + fcTy type

/-- Nodes in symmetric FCsub equality evidence. -/
def fcEqCo {scope : FCsub.Sig} : FCsub.EqCo scope -> Nat
  | .var _ => 1
  | .refl type => 1 + fcTy type
  | .symm evidence => 1 + fcEqCo evidence
  | .trans first second => 1 + fcEqCo first + fcEqCo second
  | .unfoldRec bodies _ => 1 + fcRecBodies bodies

mutual

/-- Nodes in directed FCsub inclusion evidence. -/
def fcLeCo {scope : FCsub.Sig} : FCsub.LeCo scope -> Nat
  | .var _ => 1
  | .refl type => 1 + fcTy type
  | .trans first second => 1 + fcLeCo first + fcLeCo second
  | .top source => 1 + fcTy source
  | .bot target => 1 + fcTy target
  | .eqToLe evidence => 1 + fcEqCo evidence
  | .arr domain codomain => 1 + fcLeCo domain + fcLeCo codomain
  | .existsT adaptation sourcePayload targetPayload payload =>
      1 + fcTelMor adaptation + fcTy sourcePayload + fcTy targetPayload +
        fcLeCo payload
  | .forallT adaptation sourceBody targetBody body =>
      1 + fcTelMor adaptation + fcTy sourceBody + fcTy targetBody +
        fcLeCo body

/-- Nodes in a vector of FCsub inclusion arguments. -/
def fcLeArgs {scope : FCsub.Sig} {count : Nat} :
    FCsub.LeArgs scope count -> Nat
  | .nil => 1
  | .snoc initial evidence => 1 + fcLeArgs initial + fcLeCo evidence

/-- Nodes in an FCsub telescope morphism. -/
def fcTelMor {scope : FCsub.Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat} :
    FCsub.TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints -> Nat
  | .refl telescope => 1 + fcTelescope telescope
  | .map source target names evidence =>
      1 + fcTelescope source + fcTelescope target + fcTypeArgs names +
        fcLeArgs evidence
  | .trans first second => 1 + fcTelMor first + fcTelMor second

end

/-- Nodes in a fully annotated FCsub term, including all stored types,
telescopes, and certificates. -/
def fcTm {scope : FCsub.Sig} : FCsub.Tm scope -> Nat
  | .unit => 1
  | .var _ => 1
  | .lam domain body => 1 + fcTy domain + fcTm body
  | .app function argument => 1 + fcTm function + fcTm argument
  | .let' rhs body => 1 + fcTm rhs + fcTm body
  | .cast term evidence => 1 + fcTm term + fcLeCo evidence
  | .pack telescope payloadType witnesses evidence payload =>
      1 + fcTelescope telescope + fcTy payloadType + fcTypeArgs witnesses +
        fcLeArgs evidence + fcTm payload
  | .open telescope payloadType scrutinee body =>
      1 + fcTelescope telescope + fcTy payloadType + fcTm scrutinee +
        fcTm body
  | .slam telescope body => 1 + fcTelescope telescope + fcTm body
  | .sapp telescope function witnesses evidence =>
      1 + fcTelescope telescope + fcTm function + fcTypeArgs witnesses +
        fcLeArgs evidence
  | .newtype witness body => 1 + fcTy witness + fcTm body
  | .foldRec bodies _ term => 1 + fcRecBodies bodies + fcTm term
  | .unfoldRec bodies _ term => 1 + fcRecBodies bodies + fcTm term

/-- Nodes in the erased standalone FCsub runtime. -/
def fcRuntimeTm {scope : FCsub.Sig} : FCsub.Runtime.Tm scope -> Nat
  | .var _ => 1
  | .lam body => 1 + fcRuntimeTm body
  | .unit => 1
  | .app function argument => 1 + fcRuntimeTm function + fcRuntimeTm argument
  | .let' rhs body => 1 + fcRuntimeTm rhs + fcRuntimeTm body

/-! ## Recursive DOT (`DotFCR`) -/

/-- Nodes in a recursive-DOT source type. -/
def dotFCRTy {scope : DotFC.Sig} : DotFCR.Source.Ty scope -> Nat
  | .top => 1
  | .bot => 1
  | .all domain codomain => 1 + dotFCRTy domain + dotFCRTy codomain
  | .member _ lower upper => 1 + dotFCRTy lower + dotFCRTy upper
  | .sel _ _ => 1
  | .inter left right => 1 + dotFCRTy left + dotFCRTy right
  | .mu body => 1 + dotFCRTy body

/-- Nodes in one recursive-DOT type definition. -/
def dotFCRTypeDef {scope : DotFC.Sig}
    (definition : DotFCR.Source.TypeDef scope) : Nat :=
  1 + dotFCRTy definition.witness

/-- Nodes in a finite recursive-DOT definition block. -/
def dotFCRTypeDefs {scope : DotFC.Sig}
    (definitions : List (DotFCR.Source.TypeDef scope)) : Nat :=
  definitions.foldl (fun total definition => total + dotFCRTypeDef definition) 0

/-- Nodes in a recursive-DOT source term, including static definitions and
their witness types. -/
def dotFCRTm {scope : DotFC.Sig} : DotFCR.Source.Tm scope -> Nat
  | .var _ => 1
  | .lam domain body => 1 + dotFCRTy domain + dotFCRTm body
  | .obj definitions => 1 + dotFCRTypeDefs definitions
  | .recObj definitions => 1 + dotFCRTypeDefs definitions
  | .app _ _ => 1
  | .let' rhs body => 1 + dotFCRTm rhs + dotFCRTm body

/-- Nodes in the erased recursive-DOT runtime. -/
def dotFCRRuntimeTm {scope : DotFC.Sig} :
    DotFCR.Source.Runtime.Tm scope -> Nat
  | .var _ => 1
  | .lam body => 1 + dotFCRRuntimeTm body
  | .unit => 1
  | .app function argument =>
      1 + dotFCRRuntimeTm function + dotFCRRuntimeTm argument
  | .let' rhs body => 1 + dotFCRRuntimeTm rhs + dotFCRRuntimeTm body

/-! ## Traceable-path recursive DOT (`DotFCRP`) -/

/-- Nodes in a stable traceable path. -/
def dotFCRPPath {scope : DotFC.Sig} : DotFCRP.Source.Path scope -> Nat
  | .var _ => 1
  | .select receiver _ => 1 + dotFCRPPath receiver

/-- Nodes in a traceable-path DOT source type. -/
def dotFCRPTy {scope : DotFC.Sig} : DotFCRP.Source.Ty scope -> Nat
  | .top => 1
  | .bot => 1
  | .all domain codomain => 1 + dotFCRPTy domain + dotFCRPTy codomain
  | .member _ lower upper => 1 + dotFCRPTy lower + dotFCRPTy upper
  | .sel path _ => 1 + dotFCRPPath path
  | .singleton path => 1 + dotFCRPPath path
  | .inter left right => 1 + dotFCRPTy left + dotFCRPTy right
  | .mu body => 1 + dotFCRPTy body

/-- Nodes in one traceable-path DOT type definition. -/
def dotFCRPTypeDef {scope : DotFC.Sig}
    (definition : DotFCRP.Source.TypeDef scope) : Nat :=
  1 + dotFCRPTy definition.witness

/-- Nodes in a finite traceable-path DOT definition block. -/
def dotFCRPTypeDefs {scope : DotFC.Sig}
    (definitions : List (DotFCRP.Source.TypeDef scope)) : Nat :=
  definitions.foldl
    (fun total definition => total + dotFCRPTypeDef definition) 0

/-- Nodes in a traceable-path DOT source term. -/
def dotFCRPTm {scope : DotFC.Sig} : DotFCRP.Source.Tm scope -> Nat
  | .ref path => 1 + dotFCRPPath path
  | .lam domain body => 1 + dotFCRPTy domain + dotFCRPTm body
  | .obj definitions => 1 + dotFCRPTypeDefs definitions
  | .recObj definitions => 1 + dotFCRPTypeDefs definitions
  | .app function argument =>
      1 + dotFCRPPath function + dotFCRPPath argument
  | .let' rhs body => 1 + dotFCRPTm rhs + dotFCRPTm body

/-- Nodes in one finite transparent alias-store entry. -/
def dotFCRPAliasField {scope : DotFC.Sig}
    (field : DotFCRP.Source.AliasField scope) : Nat :=
  1 + dotFCRPPath field.target

/-- Nodes in a transparent alias store. -/
def dotFCRPAliasStore {scope : DotFC.Sig}
    (store : DotFCRP.Source.AliasStore scope) : Nat :=
  store.foldl (fun total field => total + dotFCRPAliasField field) 0

/-- Nodes in the traceable-path DOT runtime. -/
def dotFCRPRuntimeTm {scope : DotFC.Sig} :
    DotFCRP.Source.Runtime.Tm scope -> Nat
  | .var _ => 1
  | .select receiver _ => 1 + dotFCRPRuntimeTm receiver
  | .lam body => 1 + dotFCRPRuntimeTm body
  | .unit => 1
  | .app function argument =>
      1 + dotFCRPRuntimeTm function + dotFCRPRuntimeTm argument
  | .let' rhs body => 1 + dotFCRPRuntimeTm rhs + dotFCRPRuntimeTm body

end NodeCount

/-! ## Generation accounting -/

/-- Compiler-generated static resources, separated from structural syntax
size so the M5/M6 formulas remain visible in reports. -/
structure GenerationCounts where
  generatedNames : Nat
  generatedConstraints : Nat
  aliasPairs : Nat
deriving DecidableEq, Repr

namespace GenerationCounts

/-- No generated static resources. -/
def zero : GenerationCounts :=
  { generatedNames := 0
    generatedConstraints := 0
    aliasPairs := 0 }

/-- Add resource counts from independent translation layers. -/
def add (first second : GenerationCounts) : GenerationCounts :=
  { generatedNames := first.generatedNames + second.generatedNames
    generatedConstraints :=
      first.generatedConstraints + second.generatedConstraints
    aliasPairs := first.aliasPairs + second.aliasPairs }

/-- M5 allocates one public name and two directed constraints per recursive
source member. -/
def m5 (members : Nat) : GenerationCounts :=
  { generatedNames := members
    generatedConstraints := 2 * members
    aliasPairs := 0 }

/-- M6 allocates one fresh name/equality pair per syntactic path-member key.
The equality is recorded as an alias pair, not as a directed M5 constraint. -/
def m6 (aliases : Nat) : GenerationCounts :=
  { generatedNames := aliases
    generatedConstraints := 0
    aliasPairs := aliases }

/-- Combined M5 recursive-member and M6 traceable-alias accounting. -/
def m5m6 (members aliases : Nat) : GenerationCounts :=
  (m5 members).add (m6 aliases)

@[simp]
theorem m5_generatedNames (members : Nat) :
    (m5 members).generatedNames = members := rfl

@[simp]
theorem m5_generatedConstraints (members : Nat) :
    (m5 members).generatedConstraints = 2 * members := rfl

@[simp]
theorem m6_generatedNames (aliases : Nat) :
    (m6 aliases).generatedNames = aliases := rfl

@[simp]
theorem m6_aliasPairs (aliases : Nat) :
    (m6 aliases).aliasPairs = aliases := rfl

end GenerationCounts

/-- Number of projections in the exact M5 recursive block: one erased object
payload projection followed by one projection per public member. -/
def m5RecursiveSlots (members : Nat) : Nat := members + 1

/-- Number of heterogeneous target binders introduced by M6 nested
`newtype`: one type name and one equality assumption per alias. -/
def m6AliasScopeBinders (aliases : Nat) : Nat := 2 * aliases

/-! ## End-to-end report -/

/-- Executable report for one generated closed artifact. -/
structure Metrics where
  sourceNodes : Nat
  targetTermNodes : Nat
  targetTypeNodes : Nat
  erasedTermNodes : Nat
  generatedNames : Nat
  generatedConstraints : Nat
  aliasPairs : Nat
  checkerAccepted : Bool
deriving DecidableEq, Repr

namespace Metrics

/-- Measure a proof-free artifact and independently run the FCsub checker.
The source count is supplied by the caller so this hook also works for a
forthcoming compiler-specific surface language. -/
def ofArtifact (sourceNodes : Nat) (generation : GenerationCounts)
    (artifact : FCsub.ClosedArtifact) : Metrics :=
  { sourceNodes := sourceNodes
    targetTermNodes := NodeCount.fcTm artifact.term
    targetTypeNodes := NodeCount.fcTy artifact.type
    erasedTermNodes := NodeCount.fcRuntimeTm artifact.erase
    generatedNames := generation.generatedNames
    generatedConstraints := generation.generatedConstraints
    aliasPairs := generation.aliasPairs
    checkerAccepted := artifact.check }

/-- Measure an artifact emitted directly from a recursive-DOT term. -/
def ofDotFCR {scope : DotFC.Sig} (source : DotFCR.Source.Tm scope)
    (generation : GenerationCounts) (artifact : FCsub.ClosedArtifact) :
    Metrics :=
  ofArtifact (NodeCount.dotFCRTm source) generation artifact

/-- Measure an artifact emitted directly from a traceable-path DOT term. -/
def ofDotFCRP {scope : DotFC.Sig} (source : DotFCRP.Source.Tm scope)
    (generation : GenerationCounts) (artifact : FCsub.ClosedArtifact) :
    Metrics :=
  ofArtifact (NodeCount.dotFCRPTm source) generation artifact

/-- Attach the generic M5/M6 resource formulas to a closed artifact. -/
def forM5M6 (sourceNodes members aliases : Nat)
    (artifact : FCsub.ClosedArtifact) : Metrics :=
  ofArtifact sourceNodes (GenerationCounts.m5m6 members aliases) artifact

@[simp]
theorem ofArtifact_checkerAccepted (sourceNodes : Nat)
    (generation : GenerationCounts) (artifact : FCsub.ClosedArtifact) :
    (ofArtifact sourceNodes generation artifact).checkerAccepted =
      artifact.check := rfl

end Metrics

end DotToFCsub.M7
