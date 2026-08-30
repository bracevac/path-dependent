import Coercions.DOT.Acyclic.Source.Context

/-!
# Proof-relevant source static semantics

All judgments are `Type`-valued certificates.  In particular, source
subtyping derivations are data that Stage A can elaborate to explicit directed
coercions.

Member declarations deliberately have no bound-consistency premise.  Thus an
open context may contain bad bounds, while the only object introduction rule
constructs an exact member.
-/

namespace DotFC.Source

mutual

/-- Well-formed source types. -/
inductive Wf : {s : Sig} → Ctx s → Ty s → Type where
  | top {s : Sig} {context : Ctx s} : Wf context .top
  | bot {s : Sig} {context : Ctx s} : Wf context .bot
  | all {s : Sig} {context : Ctx s} {domain : Ty s}
      {codomain : Ty (s ▹ .term)}
      (domainWf : Wf context domain)
      (codomainWf : Wf (context.snoc domain) codomain) :
      Wf context (.all domain codomain)
  | member {s : Sig} {context : Ctx s} {label : Name} {lower upper : Ty s}
      (lowerWf : Wf context lower) (upperWf : Wf context upper) :
      Wf context (.member label lower upper)
  | sel {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Ty s} (exposure : Handle context path label lower upper) :
      Wf context (.sel path label)

/-- Declarative, directed source subtyping.  Constructors retain the complete
proof, including transitivity and member-bound provenance. -/
inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | refl {s : Sig} {context : Ctx s} {type : Ty s}
      (typeWf : Wf context type) : Sub context type type
  | trans {s : Sig} {context : Ctx s} {source middle target : Ty s}
      (first : Sub context source middle) (second : Sub context middle target) :
      Sub context source target
  | bot {s : Sig} {context : Ctx s} {type : Ty s}
      (typeWf : Wf context type) : Sub context .bot type
  | top {s : Sig} {context : Ctx s} {type : Ty s}
      (typeWf : Wf context type) : Sub context type .top
  | member {s : Sig} {context : Ctx s} {label : Name}
      {lower₁ upper₁ lower₂ upper₂ : Ty s}
      (lower : Sub context lower₂ lower₁)
      (upper : Sub context upper₁ upper₂) :
      Sub context (.member label lower₁ upper₁)
        (.member label lower₂ upper₂)
  | lower {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Ty s} (exposure : Handle context path label lower upper) :
      Sub context lower (.sel path label)
  | upper {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Ty s} (exposure : Handle context path label lower upper) :
      Sub context (.sel path label) upper
  | all {s : Sig} {context : Ctx s} {domain₁ domain₂ : Ty s}
      {codomain₁ codomain₂ : Ty (s ▹ .term)}
      (domain : Sub context domain₂ domain₁)
      (adjustment : CtxMor (context.snoc domain₂) (context.snoc domain₁))
      (codomain : Sub (context.snoc domain₂) codomain₁ codomain₂)
      (sourceWf : Wf context (.all domain₁ codomain₁))
      (targetWf : Wf context (.all domain₂ codomain₂)) :
      Sub context (.all domain₁ codomain₁) (.all domain₂ codomain₂)

/-- An explicit pointwise adjustment from an actual context to a context under
whose views a dependent type was originally checked. -/
inductive CtxMor : {s : Sig} → Ctx s → Ctx s → Type where
  | id {s : Sig} {context : Ctx s} : CtxMor context context
  | snoc {s : Sig} {actual view : Ctx s} {actualType viewType : Ty s}
      (tail : CtxMor actual view)
      (head : Sub actual actualType viewType) :
      CtxMor (actual.snoc actualType) (view.snoc viewType)

/-- A reusable certificate exposing the sole member selected by `(path,label)`.
Handles can expose a declaration directly, through an adjusted dependent
context, or through an explicitly proved object view. -/
inductive Handle : {s : Sig} → Ctx s → BVar s .term → Name →
    Ty s → Ty s → Type where
  | direct {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Ty s}
      (binding : Lookup context path (.member label lower upper)) :
      Handle context path label lower upper
  | adjust {s : Sig} {actual view : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Ty s}
      (adjustment : CtxMor actual view)
      (binding : Lookup view path (.member label lower upper)) :
      Handle actual path label lower upper
  | expose {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {declared lower upper : Ty s}
      (binding : Lookup context path declared)
      (view : Sub context declared (.member label lower upper)) :
      Handle context path label lower upper

end

namespace Ctx

/-- Formation of an acyclic source context. -/
inductive Valid : {s : Sig} → Ctx s → Type where
  | nil : Valid .nil
  | snoc {s : Sig} {context : Ctx s} {type : Ty s}
      (contextValid : Valid context) (typeWf : Wf context type) :
      Valid (context.snoc type)

end Ctx

/-- Proof-relevant declarative typing.  Subsumption remains implicit in the
source and will elaborate to an explicit cast in Stage A. -/
inductive HasTy : {s : Sig} → Ctx s → Tm s → Ty s → Type where
  | var {s : Sig} {context : Ctx s} {path : BVar s .term} {type : Ty s}
      (binding : Lookup context path type) : HasTy context (.var path) type
  | lam {s : Sig} {context : Ctx s} {domain : Ty s}
      {body : Tm (s ▹ .term)} {codomain : Ty (s ▹ .term)}
      (domainWf : Wf context domain)
      (bodyTyping : HasTy (context.snoc domain) body codomain) :
      HasTy context (.lam domain body) (.all domain codomain)
  | obj {s : Sig} {context : Ctx s} {label : Name} {witness : Ty s}
      (witnessWf : Wf context witness) :
      HasTy context (.obj label witness) (.member label witness witness)
  | app {s : Sig} {context : Ctx s} {function argument : BVar s .term}
      {domain : Ty s} {codomain : Ty (s ▹ .term)}
      (functionTyping : HasTy context (.var function) (.all domain codomain))
      (argumentTyping : HasTy context (.var argument) domain)
      (resultWf : Wf context (codomain.open argument)) :
      HasTy context (.app function argument) (codomain.open argument)
  | let' {s : Sig} {context : Ctx s} {rhs : Tm s}
      {body : Tm (s ▹ .term)} {bound result : Ty s}
      (rhsTyping : HasTy context rhs bound)
      (bodyTyping : HasTy (context.snoc bound) body result.weaken)
      (resultWf : Wf context result) :
      HasTy context (.let' rhs body) result
  | sub {s : Sig} {context : Ctx s} {term : Tm s} {source target : Ty s}
      (termTyping : HasTy context term source)
      (subtyping : Sub context source target)
      (targetWf : Wf context target) :
      HasTy context term target

end DotFC.Source
