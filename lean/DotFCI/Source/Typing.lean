import DotFCI.Source.SignatureMetatheory

/-!
# Static semantics for acyclic DOT with signature intersections

The judgments remain proof-relevant, as in the conservative `DotFC` source
fragment.  Intersections are genuine meets at the type level.  Object syntax,
however, carries a list of exact definitions and object typing requires an
explicit no-duplicate-label certificate.  Repeated labels are therefore
available only by intersecting independently checked type views; they cannot
be smuggled into one object-definition list.
-/

namespace DotFCI.Source

open DotFC

/-! ## Acyclic contexts and lookup -/

/-- An intrinsically scoped telescope of term declarations. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | snoc {scope : Sig} (context : Ctx scope) (type : Ty scope) :
      Ctx (scope ▹ .term)

namespace Ctx

def length {scope : Sig} : Ctx scope → Nat
  | .nil => 0
  | .snoc context _ => context.length + 1

end Ctx

/-- Proof-relevant lookup weakens an older declaration across every newer
term binder. -/
inductive Lookup : {scope : Sig} → Ctx scope →
    BVar scope .term → Ty scope → Type where
  | here {scope : Sig} {context : Ctx scope} {type : Ty scope} :
      Lookup (.snoc context type) .here type.weaken
  | there {scope : Sig} {context : Ctx scope} {bound type : Ty scope}
      {path : BVar scope .term} (lookup : Lookup context path type) :
      Lookup (.snoc context bound) (.there path) type.weaken

namespace Lookup

def weaken {scope : Sig} {context : Ctx scope}
    {path : BVar scope .term} {type bound : Ty scope}
    (lookup : Lookup context path type) :
    Lookup (context.snoc bound) (.there path) type.weaken :=
  .there lookup

def newest {scope : Sig} {context : Ctx scope} {type : Ty scope} :
    Lookup (context.snoc type) .here type.weaken :=
  .here

end Lookup

/-! ## Formation, subtyping, adjustments, and member exposure -/

mutual

/-- Well-formed source types.  Intersections impose no label-disjointness:
they are conjunctions of views and may intentionally repeat one label. -/
inductive Wf : {scope : Sig} → Ctx scope → Ty scope → Type where
  | top {scope : Sig} {context : Ctx scope} : Wf context .top
  | bot {scope : Sig} {context : Ctx scope} : Wf context .bot
  | all {scope : Sig} {context : Ctx scope} {domain : Ty scope}
      {codomain : Ty (scope ▹ .term)}
      (domainWf : Wf context domain)
      (codomainWf : Wf (context.snoc domain) codomain) :
      Wf context (.all domain codomain)
  | member {scope : Sig} {context : Ctx scope} {label : Name}
      {lower upper : Ty scope}
      (lowerWf : Wf context lower) (upperWf : Wf context upper) :
      Wf context (.member label lower upper)
  | sel {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
      (exposure : Handle context path label lower upper) :
      Wf context (.sel path label)
  | inter {scope : Sig} {context : Ctx scope} {left right : Ty scope}
      (leftWf : Wf context left) (rightWf : Wf context right) :
      Wf context (.inter left right)

/-- Directed declarative subtyping.  `inter` is meet introduction;
`interLeft` and `interRight` are its two projections. -/
inductive Sub : {scope : Sig} → Ctx scope → Ty scope → Ty scope → Type where
  | refl {scope : Sig} {context : Ctx scope} {type : Ty scope}
      (typeWf : Wf context type) : Sub context type type
  | trans {scope : Sig} {context : Ctx scope} {source middle target : Ty scope}
      (first : Sub context source middle)
      (second : Sub context middle target) : Sub context source target
  | bot {scope : Sig} {context : Ctx scope} {type : Ty scope}
      (typeWf : Wf context type) : Sub context .bot type
  | top {scope : Sig} {context : Ctx scope} {type : Ty scope}
      (typeWf : Wf context type) : Sub context type .top
  | member {scope : Sig} {context : Ctx scope} {label : Name}
      {lower₁ upper₁ lower₂ upper₂ : Ty scope}
      (lower : Sub context lower₂ lower₁)
      (upper : Sub context upper₁ upper₂) :
      Sub context (.member label lower₁ upper₁)
        (.member label lower₂ upper₂)
  | lower {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
      (exposure : Handle context path label lower upper) :
      Sub context lower (.sel path label)
  | upper {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
      (exposure : Handle context path label lower upper) :
      Sub context (.sel path label) upper
  | all {scope : Sig} {context : Ctx scope} {domain₁ domain₂ : Ty scope}
      {codomain₁ codomain₂ : Ty (scope ▹ .term)}
      (domain : Sub context domain₂ domain₁)
      (adjustment : CtxMor (context.snoc domain₂) (context.snoc domain₁))
      (codomain : Sub (context.snoc domain₂) codomain₁ codomain₂)
      (sourceWf : Wf context (.all domain₁ codomain₁))
      (targetWf : Wf context (.all domain₂ codomain₂)) :
      Sub context (.all domain₁ codomain₁)
        (.all domain₂ codomain₂)
  | inter {scope : Sig} {context : Ctx scope} {source left right : Ty scope}
      (leftSub : Sub context source left)
      (rightSub : Sub context source right) :
      Sub context source (.inter left right)
  | interLeft {scope : Sig} {context : Ctx scope} {left right : Ty scope} :
      Sub context (.inter left right) left
  | interRight {scope : Sig} {context : Ctx scope} {left right : Ty scope} :
      Sub context (.inter left right) right

/-- Pointwise adjustment between dependent contexts. -/
inductive CtxMor : {scope : Sig} → Ctx scope → Ctx scope → Type where
  | id {scope : Sig} {context : Ctx scope} : CtxMor context context
  | snoc {scope : Sig} {actual view : Ctx scope}
      {actualType viewType : Ty scope}
      (tail : CtxMor actual view)
      (head : Sub actual actualType viewType) :
      CtxMor (actual.snoc actualType) (view.snoc viewType)

/-- A reusable exposure of one stable `(path,label)` member identity. -/
inductive Handle : {scope : Sig} → Ctx scope → BVar scope .term → Name →
    Ty scope → Ty scope → Type where
  | direct {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
      (binding : Lookup context path (.member label lower upper)) :
      Handle context path label lower upper
  | adjust {scope : Sig} {actual view : Ctx scope}
      {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
      (adjustment : CtxMor actual view)
      (binding : Lookup view path (.member label lower upper)) :
      Handle actual path label lower upper
  | expose {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {label : Name}
      {declared lower upper : Ty scope}
      (binding : Lookup context path declared)
      (view : Sub context declared (.member label lower upper)) :
      Handle context path label lower upper

end

namespace Ctx

/-- Formation of an acyclic source context. -/
inductive Valid : {scope : Sig} → Ctx scope → Type where
  | nil : Valid .nil
  | snoc {scope : Sig} {context : Ctx scope} {type : Ty scope}
      (contextValid : Valid context) (typeWf : Wf context type) :
      Valid (context.snoc type)

end Ctx

/-! ## Multi-definition object certificates -/

namespace TypeDefs

/-- Definition labels in source order. -/
def labels {scope : Sig} (definitions : List (TypeDef scope)) : List Name :=
  definitions.map TypeDef.label

/-- Every exact witness in an object definition list is well formed. -/
inductive AllWf {scope : Sig} (context : Ctx scope) :
    List (TypeDef scope) → Type where
  | nil : AllWf context []
  | cons {definition : TypeDef scope} {remaining : List (TypeDef scope)}
      (witnessWf : Wf context definition.witness)
      (remainingWf : AllWf context remaining) :
      AllWf context (definition :: remaining)

/-- Object-definition validity makes label uniqueness explicit. -/
structure Valid {scope : Sig} (context : Ctx scope)
    (definitions : List (TypeDef scope)) : Type where
  witnesses : AllWf context definitions
  labelsNoDup : (labels definitions).Nodup

namespace AllWf

/-- Exact member intersections formed from checked definitions are well
formed. -/
def exactWf {scope : Sig} {context : Ctx scope} :
    (definitions : List (TypeDef scope)) → AllWf context definitions →
      Wf context (TypeDefs.exact definitions)
  | [], .nil => .top
  | [_], .cons witnessWf .nil => .member witnessWf witnessWf
  | _ :: next :: remaining, .cons witnessWf remainingWf =>
      .inter (.member witnessWf witnessWf)
        (exactWf (next :: remaining) remainingWf)

end AllWf

namespace Valid

def nil {scope : Sig} {context : Ctx scope} :
    Valid context [] where
  witnesses := .nil
  labelsNoDup := .nil

def cons {scope : Sig} {context : Ctx scope}
    (definition : TypeDef scope) {remaining : List (TypeDef scope)}
    (witnessWf : Wf context definition.witness)
    (remainingValid : Valid context remaining)
    (fresh : definition.label ∉ labels remaining) :
    Valid context (definition :: remaining) where
  witnesses := .cons witnessWf remainingValid.witnesses
  labelsNoDup := by
    rw [labels, List.map_cons, List.nodup_cons]
    exact ⟨fresh, remainingValid.labelsNoDup⟩

def exactWf {scope : Sig} {context : Ctx scope}
    {definitions : List (TypeDef scope)}
    (valid : Valid context definitions) :
    Wf context (TypeDefs.exact definitions) :=
  valid.witnesses.exactWf definitions

def singleton {scope : Sig} {context : Ctx scope}
    (label : Name) (witness : Ty scope) (witnessWf : Wf context witness) :
    Valid context [⟨label, witness⟩] where
  witnesses := .cons witnessWf .nil
  labelsNoDup := by simp [labels]

def pair {scope : Sig} {context : Ctx scope}
    (firstLabel secondLabel : Name) (firstWitness secondWitness : Ty scope)
    (firstWf : Wf context firstWitness)
    (secondWf : Wf context secondWitness)
    (different : firstLabel ≠ secondLabel) :
    Valid context
      [⟨firstLabel, firstWitness⟩, ⟨secondLabel, secondWitness⟩] :=
  cons ⟨firstLabel, firstWitness⟩ firstWf
    (singleton secondLabel secondWitness secondWf) (by
      simpa [labels] using different)

/-- Two definitions with the same label can never satisfy object validity. -/
theorem no_duplicate_pair {scope : Sig} {context : Ctx scope}
    (label : Name) (first second : Ty scope) :
    Valid context [⟨label, first⟩, ⟨label, second⟩] → False := by
  intro valid
  simpa [labels] using valid.labelsNoDup

end Valid

end TypeDefs

/-! ## Term typing -/

/-- Proof-relevant declarative typing. -/
inductive HasTy : {scope : Sig} → Ctx scope → Tm scope → Ty scope → Type where
  | var {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {type : Ty scope}
      (binding : Lookup context path type) : HasTy context (.var path) type
  | lam {scope : Sig} {context : Ctx scope} {domain : Ty scope}
      {body : Tm (scope ▹ .term)} {codomain : Ty (scope ▹ .term)}
      (domainWf : Wf context domain)
      (bodyTyping : HasTy (context.snoc domain) body codomain) :
      HasTy context (.lam domain body) (.all domain codomain)
  | obj {scope : Sig} {context : Ctx scope}
      {definitions : List (TypeDef scope)}
      (definitionsValid : TypeDefs.Valid context definitions) :
      HasTy context (.obj definitions) (TypeDefs.exact definitions)
  | app {scope : Sig} {context : Ctx scope}
      {function argument : BVar scope .term}
      {domain : Ty scope} {codomain : Ty (scope ▹ .term)}
      (functionTyping : HasTy context (.var function) (.all domain codomain))
      (argumentTyping : HasTy context (.var argument) domain)
      (resultWf : Wf context (codomain.open argument)) :
      HasTy context (.app function argument) (codomain.open argument)
  | let' {scope : Sig} {context : Ctx scope} {rhs : Tm scope}
      {body : Tm (scope ▹ .term)} {bound result : Ty scope}
      (rhsTyping : HasTy context rhs bound)
      (bodyTyping : HasTy (context.snoc bound) body result.weaken)
      (resultWf : Wf context result) :
      HasTy context (.let' rhs body) result
  | sub {scope : Sig} {context : Ctx scope} {term : Tm scope}
      {source target : Ty scope}
      (termTyping : HasTy context term source)
      (subtyping : Sub context source target)
      (targetWf : Wf context target) :
      HasTy context term target

/-! ## Proof-relevant signature roots and member occurrences -/

/-- A member/intersection tree whose bounds are well formed and whose result
signature is fixed in the type of the certificate. -/
inductive Collectible : {scope : Sig} → Ctx scope → Ty scope →
    Signature scope → Type where
  | member {scope : Sig} {context : Ctx scope} {label : Name}
      {lower upper : Ty scope}
      (lowerWf : Wf context lower) (upperWf : Wf context upper) :
      Collectible context (.member label lower upper)
        (.singleton label lower upper)
  | inter {scope : Sig} {context : Ctx scope}
      {left right : Ty scope} {leftSignature rightSignature : Signature scope}
      (leftCollectible : Collectible context left leftSignature)
      (rightCollectible : Collectible context right rightSignature) :
      Collectible context (.inter left right)
        (leftSignature.merge rightSignature)

namespace Collectible

def wf {scope : Sig} {context : Ctx scope} {type : Ty scope}
    {signature : Signature scope}
    (certificate : Collectible context type signature) : Wf context type :=
  match certificate with
  | .member lowerWf upperWf => .member lowerWf upperWf
  | .inter left right => .inter left.wf right.wf

def normalized {scope : Sig} {context : Ctx scope} {type : Ty scope}
    {signature : Signature scope}
    (certificate : Collectible context type signature) :
    signature.Normalized :=
  match certificate with
  | .member (label := label) (lower := lower) (upper := upper) _ _ =>
      Signature.singleton_normalized label lower upper
  | .inter left right =>
      Signature.merge_normalized _ _ left.normalized right.normalized

theorem collected {scope : Sig} {context : Ctx scope} {type : Ty scope}
    {signature : Signature scope}
    (certificate : Collectible context type signature) :
    collect? type = some signature := by
  induction certificate with
  | member => rfl
  | inter left right leftInduction rightInduction =>
      simp [collect?, leftInduction, rightInduction]

end Collectible

/-- A structural occurrence, retaining whether it came from the left or
right branch even when both branches use the same label. -/
inductive MemberAt : {scope : Sig} → Ty scope → Name →
    Ty scope → Ty scope → Type where
  | here {scope : Sig} {label : Name} {lower upper : Ty scope} :
      MemberAt (.member label lower upper) label lower upper
  | left {scope : Sig} {left right : Ty scope} {label : Name}
      {lower upper : Ty scope}
      (occurrence : MemberAt left label lower upper) :
      MemberAt (.inter left right) label lower upper
  | right {scope : Sig} {left right : Ty scope} {label : Name}
      {lower upper : Ty scope}
      (occurrence : MemberAt right label lower upper) :
      MemberAt (.inter left right) label lower upper

namespace Collectible

/-- Structural intersection projection exposes an occurrence without
searching or manufacturing a second member identity. -/
def memberSub {scope : Sig} {context : Ctx scope} {root : Ty scope}
    {signature : Signature scope} {label : Name} {lower upper : Ty scope}
    (certificate : Collectible context root signature)
    (occurrence : MemberAt root label lower upper) :
    Sub context root (.member label lower upper) :=
  match certificate, occurrence with
  | .member lowerWf upperWf, .here => .refl (.member lowerWf upperWf)
  | .inter left _, .left occurrence =>
      .trans .interLeft (left.memberSub occurrence)
  | .inter _ right, .right occurrence =>
      .trans .interRight (right.memberSub occurrence)

/-- Every structural occurrence contributes its exact interval to the
normalized signature, including repeated-label occurrences. -/
def memberInterval_mem {scope : Sig} {context : Ctx scope}
    {root : Ty scope} {signature : Signature scope}
    {label : Name} {lower upper : Ty scope}
    (certificate : Collectible context root signature)
    (occurrence : MemberAt root label lower upper) :
    (⟨lower, upper⟩ : Interval scope) ∈ signature.constraintsAt label :=
  match certificate, occurrence with
  | .member _ _, .here => by simp
  | @Collectible.inter _ _ left right leftSignature rightSignature
      leftCertificate rightCertificate, .left occurrence => by
      rw [Signature.constraintsAt_merge leftSignature rightSignature
        leftCertificate.normalized rightCertificate.normalized]
      exact List.mem_append_left _
        (leftCertificate.memberInterval_mem occurrence)
  | @Collectible.inter _ _ left right leftSignature rightSignature
      leftCertificate rightCertificate, .right occurrence => by
      rw [Signature.constraintsAt_merge leftSignature rightSignature
        leftCertificate.normalized rightCertificate.normalized]
      exact List.mem_append_right _
        (rightCertificate.memberInterval_mem occurrence)

end Collectible

/-- One checked collectible interface rooted at one stable path binding. -/
structure SignatureRoot {scope : Sig} (context : Ctx scope)
    (path : BVar scope .term) (signature : Signature scope) : Type where
  declared : Ty scope
  binding : Lookup context path declared
  collectible : Collectible context declared signature

namespace SignatureRoot

def wf {scope : Sig} {context : Ctx scope} {path : BVar scope .term}
    {signature : Signature scope}
    (root : SignatureRoot context path signature) : Wf context root.declared :=
  root.collectible.wf

def normalized {scope : Sig} {context : Ctx scope}
    {path : BVar scope .term} {signature : Signature scope}
    (root : SignatureRoot context path signature) : signature.Normalized :=
  root.collectible.normalized

theorem collected {scope : Sig} {context : Ctx scope}
    {path : BVar scope .term} {signature : Signature scope}
    (root : SignatureRoot context path signature) :
    collect? root.declared = some signature :=
  root.collectible.collected

end SignatureRoot

/-- Stable identity key used by M4 allocation. -/
structure MemberKey (scope : Sig) where
  path : BVar scope .term
  label : Name
deriving DecidableEq

/-- A proof-relevant occurrence under one shared signature root.  Multiple
occurrences may have the same key and different intervals, but all retain the
same root certificate and hence the same future target identity. -/
structure MemberOccurrence {scope : Sig} (context : Ctx scope)
    (path : BVar scope .term) (label : Name)
    (lower upper : Ty scope) : Type where
  signature : Signature scope
  root : SignatureRoot context path signature
  member : MemberAt root.declared label lower upper

namespace MemberOccurrence

def key {scope : Sig} {context : Ctx scope} {path : BVar scope .term}
    {label : Name} {lower upper : Ty scope}
    (_ : MemberOccurrence context path label lower upper) : MemberKey scope :=
  ⟨path, label⟩

def handle {scope : Sig} {context : Ctx scope} {path : BVar scope .term}
    {label : Name} {lower upper : Ty scope}
    (occurrence : MemberOccurrence context path label lower upper) :
    Handle context path label lower upper :=
  .expose occurrence.root.binding
    (occurrence.root.collectible.memberSub occurrence.member)

theorem interval_mem {scope : Sig} {context : Ctx scope}
    {path : BVar scope .term} {label : Name} {lower upper : Ty scope}
    (occurrence : MemberOccurrence context path label lower upper) :
    (⟨lower, upper⟩ : Interval scope) ∈
      occurrence.signature.constraintsAt label :=
  occurrence.root.collectible.memberInterval_mem occurrence.member

end MemberOccurrence

/-- Repeating a label across two intersected views is well formed and
collectible; object-definition uniqueness is intentionally unrelated. -/
def Collectible.overlappingMembers {scope : Sig} {context : Ctx scope}
    (label : Name) {lower₁ upper₁ lower₂ upper₂ : Ty scope}
    (lower₁Wf : Wf context lower₁) (upper₁Wf : Wf context upper₁)
    (lower₂Wf : Wf context lower₂) (upper₂Wf : Wf context upper₂) :
    Collectible context
      (.inter (.member label lower₁ upper₁)
        (.member label lower₂ upper₂))
      ((Signature.singleton label lower₁ upper₁).merge
        (Signature.singleton label lower₂ upper₂)) :=
  .inter (.member lower₁Wf upper₁Wf) (.member lower₂Wf upper₂Wf)

end DotFCI.Source
