import Coercions.DOT.TraceablePaths.Source.Trace

/-!
# Static semantics for traceable-path DOT

The new rules consume `Traceable` evidence at every path-sensitive boundary.
The final section gives an explicit, one-way derivation-preserving inclusion
of arbitrary recursive-object `DotFCR` judgments.  Thus recursive type-member
objects are retained even though traceable paths add no new recursive
principle.  No reflection or conservative-extension theorem is claimed for
the larger native judgment.
-/

namespace DotFCRP.Source

open DotFC

/-! ## Contexts and resolved path bindings -/

inductive Ctx : Sig → Type where
  | nil : Ctx []
  | snoc {scope : Sig} (context : Ctx scope) (type : Ty scope) :
      Ctx (scope ▹ .term)

namespace Legacy

/-- Constructor-for-constructor embedding of a recursive-object context. -/
def context : {scope : Sig} → DotFCR.Source.Ctx scope → Ctx scope
  | _, .nil => .nil
  | _, .snoc outer type => .snoc (context outer) (ty type)

end Legacy

inductive Lookup : {scope : Sig} → Ctx scope →
    BVar scope .term → Ty scope → Type where
  | here {scope : Sig} {context : Ctx scope} {type : Ty scope} :
      Lookup (.snoc context type) .here type.weaken
  | there {scope : Sig} {context : Ctx scope} {bound type : Ty scope}
      {root : BVar scope .term} (lookup : Lookup context root type) :
      Lookup (.snoc context bound) (.there root) type.weaken

namespace Lookup

def weaken {scope : Sig} {context : Ctx scope}
    {root : BVar scope .term} {type bound : Ty scope}
    (lookup : Lookup context root type) :
    Lookup (context.snoc bound) (.there root) type.weaken :=
  .there lookup

end Lookup

/-- A path resolves to a context variable with the displayed type. -/
structure PathBinding {scope : Sig} (store : AliasStore scope)
    (context : Ctx scope) (path : Path scope) (type : Ty scope) : Type where
  anchor : BVar scope .term
  trace : Traceable store path anchor
  lookup : Lookup context anchor type

namespace PathBinding

/-- Co-resolved paths inherit the same anchor binding. -/
def transport {scope : Sig} {store : AliasStore scope}
    {context : Ctx scope} {left right : Path scope} {type : Ty scope}
    (binding : PathBinding store context left type)
    (equality : CoResolved store left right) :
    PathBinding store context right type := by
  have anchorEqual : binding.anchor = equality.anchor :=
    Traceable.deterministic binding.trace equality.leftTrace
  exact ⟨binding.anchor, anchorEqual.symm ▸ equality.rightTrace,
    binding.lookup⟩

end PathBinding

/-! ## Member structure and well-formedness -/

inductive MemberAt : {scope : Sig} → Ty scope → Name →
    Ty scope → Ty scope → Type where
  | here {scope : Sig} {label : Name} {lower upper : Ty scope} :
      MemberAt (.member label lower upper) label lower upper
  | left {scope : Sig} {left right : Ty scope} {label : Name}
      {lower upper : Ty scope}
      (member : MemberAt left label lower upper) :
      MemberAt (.inter left right) label lower upper
  | right {scope : Sig} {left right : Ty scope} {label : Name}
      {lower upper : Ty scope}
      (member : MemberAt right label lower upper) :
      MemberAt (.inter left right) label lower upper

/-- A recursive body has a proper member/intersection head. -/
inductive HeadGuarded : {scope : Sig} → Ty scope → Type where
  | member {scope : Sig} {label : Name} {lower upper : Ty scope} :
      HeadGuarded (.member label lower upper)
  | inter {scope : Sig} {left right : Ty scope}
      (leftGuarded : HeadGuarded left)
      (rightGuarded : HeadGuarded right) :
      HeadGuarded (.inter left right)

/-- Exposure of a member through a traceable path. -/
inductive Handle {scope : Sig} (store : AliasStore scope)
    (context : Ctx scope) : Path scope → Name →
      Ty scope → Ty scope → Type where
  | direct {path : Path scope} {rootType : Ty scope} {label : Name}
      {lower upper : Ty scope}
      (binding : PathBinding store context path rootType)
      (member : MemberAt rootType label lower upper) :
      Handle store context path label lower upper
  | recursive {path : Path scope} {body : Ty (scope ▹ .term)}
      {label : Name} {lower upper : Ty scope}
      (binding : PathBinding store context path (.mu body))
      (guarded : HeadGuarded body)
      (member : MemberAt (body.open path) label lower upper) :
      Handle store context path label lower upper

/-- Well-formed types.  Alias stores weaken under binders and are immutable. -/
inductive Wf : {scope : Sig} → AliasStore scope →
    Ctx scope → Ty scope → Type where
  | top {scope : Sig} {store : AliasStore scope} {context : Ctx scope} :
      Wf store context .top
  | bot {scope : Sig} {store : AliasStore scope} {context : Ctx scope} :
      Wf store context .bot
  | all {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {domain : Ty scope} {codomain : Ty (scope ▹ .term)}
      (domainWf : Wf store context domain)
      (codomainWf : Wf (store.weaken (kind := .term))
        (context.snoc domain) codomain) :
      Wf store context (.all domain codomain)
  | member {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {label : Name} {lower upper : Ty scope}
      (lowerWf : Wf store context lower) (upperWf : Wf store context upper) :
      Wf store context (.member label lower upper)
  | sel {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {path : Path scope} {label : Name} {lower upper : Ty scope}
      (handle : Handle store context path label lower upper) :
      Wf store context (.sel path label)
  | singleton {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {path : Path scope} {type : Ty scope}
      (binding : PathBinding store context path type) :
      Wf store context (.singleton path)
  | inter {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {left right : Ty scope}
      (leftWf : Wf store context left) (rightWf : Wf store context right) :
      Wf store context (.inter left right)
  | mu {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {body : Ty (scope ▹ .term)}
      (guarded : HeadGuarded body)
      (bodyWf : Wf (store.weaken (kind := .term))
        (context.snoc (.mu body)) body) :
      Wf store context (.mu body)
  | legacy {scope : Sig} {store : AliasStore scope}
      {legacyContext : DotFCR.Source.Ctx scope}
      {legacyType : DotFCR.Source.Ty scope}
      (derivation : DotFCR.Source.Wf legacyContext legacyType) :
      Wf store (Legacy.context legacyContext) (Legacy.ty legacyType)

/-! ## Subtyping -/

inductive Sub : {scope : Sig} → AliasStore scope → Ctx scope →
    Ty scope → Ty scope → Type where
  | refl {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {type : Ty scope} (typeWf : Wf store context type) :
      Sub store context type type
  | trans {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {source middle target : Ty scope}
      (first : Sub store context source middle)
      (second : Sub store context middle target) :
      Sub store context source target
  | bot {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {type : Ty scope} (typeWf : Wf store context type) :
      Sub store context .bot type
  | top {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {type : Ty scope} (typeWf : Wf store context type) :
      Sub store context type .top
  | member {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {label : Name} {lower₁ upper₁ lower₂ upper₂ : Ty scope}
      (lower : Sub store context lower₂ lower₁)
      (upper : Sub store context upper₁ upper₂) :
      Sub store context (.member label lower₁ upper₁)
        (.member label lower₂ upper₂)
  | lower {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {path : Path scope} {label : Name} {lower upper : Ty scope}
      (handle : Handle store context path label lower upper) :
      Sub store context lower (.sel path label)
  | upper {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {path : Path scope} {label : Name} {lower upper : Ty scope}
      (handle : Handle store context path label lower upper) :
      Sub store context (.sel path label) upper
  | inter {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {source left right : Ty scope}
      (leftSub : Sub store context source left)
      (rightSub : Sub store context source right) :
      Sub store context source (.inter left right)
  | interLeft {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {left right : Ty scope} : Sub store context (.inter left right) left
  | interRight {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {left right : Ty scope} : Sub store context (.inter left right) right
  | singletonEq {scope : Sig} {store : AliasStore scope}
      {context : Ctx scope} {left right : Path scope}
      (equality : CoResolved store left right) :
      Sub store context (.singleton left) (.singleton right)
  | legacy {scope : Sig} {store : AliasStore scope}
      {legacyContext : DotFCR.Source.Ctx scope}
      {source target : DotFCR.Source.Ty scope}
      (derivation : DotFCR.Source.Sub legacyContext source target) :
      Sub store (Legacy.context legacyContext) (Legacy.ty source)
        (Legacy.ty target)

/-! ## Object validity and term typing -/

namespace TypeDefs

def labels {scope : Sig} (definitions : List (TypeDef scope)) : List Name :=
  definitions.map TypeDef.label

inductive AllWf {scope : Sig} (store : AliasStore scope)
    (context : Ctx scope) : List (TypeDef scope) → Type where
  | nil : AllWf store context []
  | cons {definition : TypeDef scope} {remaining : List (TypeDef scope)}
      (witnessWf : Wf store context definition.witness)
      (remainingWf : AllWf store context remaining) :
      AllWf store context (definition :: remaining)

namespace AllWf

def exactWf {scope : Sig} {store : AliasStore scope} {context : Ctx scope} :
    (definitions : List (TypeDef scope)) → AllWf store context definitions →
      Wf store context (exact definitions)
  | [], .nil => .top
  | [_], .cons witnessWf .nil => .member witnessWf witnessWf
  | _ :: next :: remaining, .cons witnessWf remainingWf =>
      .inter (.member witnessWf witnessWf)
        (exactWf (next :: remaining) remainingWf)

end AllWf

structure Valid {scope : Sig} (store : AliasStore scope)
    (context : Ctx scope) (definitions : List (TypeDef scope)) : Type where
  witnesses : AllWf store context definitions
  labelsNoDup : (labels definitions).Nodup

/-- Proper-head witnesses relative to the newest recursive self binder. -/
inductive WitnessGuarded {scope : Sig} : Ty (scope ▹ .term) → Type where
  | top : WitnessGuarded .top
  | bot : WitnessGuarded .bot
  | all {domain : Ty (scope ▹ .term)}
      {codomain : Ty ((scope ▹ .term) ▹ .term)} :
      WitnessGuarded (.all domain codomain)
  | member {label : Name} {lower upper : Ty (scope ▹ .term)} :
      WitnessGuarded (.member label lower upper)
  | inter {left right : Ty (scope ▹ .term)} :
      WitnessGuarded (.inter left right)
  | mu {body : Ty ((scope ▹ .term) ▹ .term)} :
      WitnessGuarded (.mu body)
  | ambientSel {path : Path scope} {label : Name} :
      WitnessGuarded (.sel path.weaken label)
  | ambientSingleton {path : Path scope} :
      WitnessGuarded (.singleton path.weaken)

inductive AllGuarded {scope : Sig} :
    List (TypeDef (scope ▹ .term)) → Type where
  | nil : AllGuarded []
  | cons {definition : TypeDef (scope ▹ .term)}
      {remaining : List (TypeDef (scope ▹ .term))}
      (head : WitnessGuarded definition.witness)
      (tail : AllGuarded remaining) :
      AllGuarded (definition :: remaining)

def exactHeadGuarded {scope : Sig} :
    (definitions : List (TypeDef scope)) → definitions ≠ [] →
      HeadGuarded (exact definitions)
  | [], nonempty => False.elim (nonempty rfl)
  | [_], _ => .member
  | _ :: _ :: _, _ => .inter .member (exactHeadGuarded _ (by simp))

structure RecValid {scope : Sig} (store : AliasStore scope)
    (context : Ctx scope)
    (definitions : List (TypeDef (scope ▹ .term))) : Type where
  nonempty : definitions ≠ []
  witnessGuards : AllGuarded definitions
  witnesses : AllWf (store.weaken (kind := .term))
    (context.snoc (.mu (exact definitions))) definitions
  labelsNoDup : (labels definitions).Nodup

namespace RecValid

def headGuarded {scope : Sig} {store : AliasStore scope}
    {context : Ctx scope}
    {definitions : List (TypeDef (scope ▹ .term))}
    (valid : RecValid store context definitions) :
    HeadGuarded (exact definitions) :=
  exactHeadGuarded definitions valid.nonempty

def selfTypeWf {scope : Sig} {store : AliasStore scope}
    {context : Ctx scope}
    {definitions : List (TypeDef (scope ▹ .term))}
    (valid : RecValid store context definitions) :
    Wf store context (.mu (exact definitions)) :=
  .mu valid.headGuarded (valid.witnesses.exactWf definitions)

end RecValid

end TypeDefs

inductive HasTy : {scope : Sig} → AliasStore scope → Ctx scope →
    Tm scope → Ty scope → Type where
  | path {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {path : Path scope} {type : Ty scope}
      (binding : PathBinding store context path type) :
      HasTy store context (.ref path) type
  | pathEq {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {left right : Path scope} {type : Ty scope}
      (binding : PathBinding store context left type)
      (equality : CoResolved store left right) :
      HasTy store context (.ref right) type
  | lam {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {domain : Ty scope} {body : Tm (scope ▹ .term)}
      {codomain : Ty (scope ▹ .term)}
      (domainWf : Wf store context domain)
      (bodyTyping : HasTy (store.weaken (kind := .term))
        (context.snoc domain) body codomain) :
      HasTy store context (.lam domain body) (.all domain codomain)
  | obj {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {definitions : List (TypeDef scope)}
      (valid : TypeDefs.Valid store context definitions) :
      HasTy store context (.obj definitions) (TypeDefs.exact definitions)
  | recObj {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {definitions : List (TypeDef (scope ▹ .term))}
      (valid : TypeDefs.RecValid store context definitions) :
      HasTy store context (.recObj definitions)
        (.mu (TypeDefs.exact definitions))
  | app {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {function argument : Path scope} {domain : Ty scope}
      {codomain : Ty (scope ▹ .term)}
      (functionBinding : PathBinding store context function
        (.all domain codomain))
      (argumentBinding : PathBinding store context argument domain)
      (resultWf : Wf store context (codomain.open argument)) :
      HasTy store context (.app function argument) (codomain.open argument)
  | let' {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {rhs : Tm scope} {body : Tm (scope ▹ .term)}
      {bound result : Ty scope}
      (rhsTyping : HasTy store context rhs bound)
      (bodyTyping : HasTy (store.weaken (kind := .term))
        (context.snoc bound) body result.weaken)
      (resultWf : Wf store context result) :
      HasTy store context (.let' rhs body) result
  | sub {scope : Sig} {store : AliasStore scope} {context : Ctx scope}
      {term : Tm scope} {source target : Ty scope}
      (termTyping : HasTy store context term source)
      (subtyping : Sub store context source target)
      (targetWf : Wf store context target) :
      HasTy store context term target
  | legacy {scope : Sig} {store : AliasStore scope}
      {legacyContext : DotFCR.Source.Ctx scope}
      {legacyTerm : DotFCR.Source.Tm scope}
      {legacyType : DotFCR.Source.Ty scope}
      (derivation : DotFCR.Source.HasTy legacyContext legacyTerm legacyType) :
      HasTy store (Legacy.context legacyContext) (Legacy.tm legacyTerm)
        (Legacy.ty legacyType)

/-! ## Complete recursive-object derivation embedding -/

namespace Legacy

def wf {scope : Sig} {store : AliasStore scope}
    {context : DotFCR.Source.Ctx scope} {type : DotFCR.Source.Ty scope}
    (derivation : DotFCR.Source.Wf context type) :
    Wf store (Legacy.context context) (Legacy.ty type) :=
  .legacy derivation

def sub {scope : Sig} {store : AliasStore scope}
    {context : DotFCR.Source.Ctx scope}
    {source target : DotFCR.Source.Ty scope}
    (derivation : DotFCR.Source.Sub context source target) :
    Sub store (Legacy.context context) (Legacy.ty source) (Legacy.ty target) :=
  .legacy derivation

def hasTy {scope : Sig} {store : AliasStore scope}
    {context : DotFCR.Source.Ctx scope} {term : DotFCR.Source.Tm scope}
    {type : DotFCR.Source.Ty scope}
    (derivation : DotFCR.Source.HasTy context term type) :
    HasTy store (Legacy.context context) (Legacy.tm term) (Legacy.ty type) :=
  .legacy derivation

/-- The mutually recursive object remains typable without aliases. -/
def mutualObjectTyping :
    HasTy ([] : AliasStore []) (context DotFCR.Source.Ctx.nil)
      (tm DotFCR.Source.MutualExample.object)
      (ty DotFCR.Source.MutualExample.objectType) :=
  hasTy DotFCR.Source.MutualExample.objectTyping

end Legacy

end DotFCRP.Source
