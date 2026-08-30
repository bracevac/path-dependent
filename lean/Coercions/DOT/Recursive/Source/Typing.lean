import Coercions.DOT.Recursive.Source.Syntax

/-!
# Static semantics for recursive type-member objects

The calculus keeps proof-relevant contexts, lookup, subtyping, and member
exposure.  A recursive object is checked under one self assumption containing
its complete member/intersection body.  `HeadGuarded` is carried explicitly at
every fold/unfold boundary; no positivity condition is imposed on bounds.
-/

namespace DotFCR.Source

open DotFC

/-! ## Contexts and stable lookup -/

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

/-- Lookup weakens an older declaration across every newer term binder. -/
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

/-! ## Structural member occurrences -/

/-- A member occurrence retains its exact branch in an intersection tree. -/
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

namespace MemberAt

/-- Member occurrence is natural under stable-path renaming. -/
def rename {source target : Sig} {root : Ty source} {label : Name}
    {lower upper : Ty source}
    (occurrence : MemberAt root label lower upper) (rho : Rename source target) :
    MemberAt (root.rename rho) label (lower.rename rho) (upper.rename rho) :=
  match occurrence with
  | .here => .here
  | .left inner => .left (inner.rename rho)
  | .right inner => .right (inner.rename rho)

end MemberAt

/-! ## Formation, subtyping, context adjustment, and member exposure -/

mutual

/-- Well-formed types.  A recursive body is checked with its own folded type
as the newest assumption. -/
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
  | mu {scope : Sig} {context : Ctx scope}
      {body : Ty (scope ▹ .term)}
      (guarded : HeadGuarded body)
      (bodyWf : Wf (context.snoc (.mu body)) body) :
      Wf context (.mu body)

/-- Directed declarative subtyping.  Recursive fold and unfold rules are
path-indexed: only a stable variable whose lookup has the folded type can
instantiate the self binder. -/
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
  | unfold {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {body : Ty (scope ▹ .term)}
      (binding : Lookup context path (.mu body))
      (guarded : HeadGuarded body) :
      Sub context (.mu body) (body.open path)
  | fold {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {body : Ty (scope ▹ .term)}
      (binding : Lookup context path (.mu body))
      (guarded : HeadGuarded body) :
      Sub context (body.open path) (.mu body)

/-- Pointwise adjustment between dependent contexts. -/
inductive CtxMor : {scope : Sig} → Ctx scope → Ctx scope → Type where
  | id {scope : Sig} {context : Ctx scope} : CtxMor context context
  | snoc {scope : Sig} {actual view : Ctx scope}
      {actualType viewType : Ty scope}
      (tail : CtxMor actual view)
      (head : Sub actual actualType viewType) :
      CtxMor (actual.snoc actualType) (view.snoc viewType)

/-- Reusable exposure of one stable `(path,label)` identity.  `self` is the
primitive guarded knot used while checking a recursive object's definitions;
`recursive` is its opened form for an arbitrary stable path. -/
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
  | recursive {scope : Sig} {context : Ctx scope}
      {path : BVar scope .term} {body : Ty (scope ▹ .term)}
      {label : Name} {lower upper : Ty scope}
      (binding : Lookup context path (.mu body))
      (guarded : HeadGuarded body)
      (member : MemberAt (body.open path) label lower upper) :
      Handle context path label lower upper
  | self {scope : Sig} {context : Ctx scope}
      {body : Ty (scope ▹ .term)} {label : Name}
      {lower upper : Ty (scope ▹ .term)}
      (guarded : HeadGuarded body)
      (member : MemberAt body label lower upper) :
      Handle (context.snoc (.mu body)) .here label lower upper
  | selfWeaken {scope : Sig} {context : Ctx scope}
      {body : Ty (scope ▹ .term)} {bound : Ty (scope ▹ .term)}
      {label : Name} {lower upper : Ty (scope ▹ .term)}
      (guarded : HeadGuarded body)
      (member : MemberAt body label lower upper) :
      Handle ((context.snoc (.mu body)).snoc bound) (.there .here) label
        lower.weaken upper.weaken

end

namespace Ctx

/-- Formation of recursive source contexts. -/
inductive Valid : {scope : Sig} → Ctx scope → Type where
  | nil : Valid .nil
  | snoc {scope : Sig} {context : Ctx scope} {type : Ty scope}
      (contextValid : Valid context) (typeWf : Wf context type) :
      Valid (context.snoc type)

end Ctx

/-! ## Plain and recursive definition certificates -/

namespace TypeDefs

/-- Definition labels in source order. -/
def labels {scope : Sig} (definitions : List (TypeDef scope)) : List Name :=
  definitions.map TypeDef.label

/-- Every witness in a definition list is well formed. -/
inductive AllWf {scope : Sig} (context : Ctx scope) :
    List (TypeDef scope) → Type where
  | nil : AllWf context []
  | cons {definition : TypeDef scope} {remaining : List (TypeDef scope)}
      (witnessWf : Wf context definition.witness)
      (remainingWf : AllWf context remaining) :
      AllWf context (definition :: remaining)

/-- Nonrecursive object validity. -/
structure Valid {scope : Sig} (context : Ctx scope)
    (definitions : List (TypeDef scope)) : Type where
  witnesses : AllWf context definitions
  labelsNoDup : (labels definitions).Nodup

namespace AllWf

/-- Exact intersections formed from checked definitions are well formed. -/
def exactWf {scope : Sig} {context : Ctx scope} :
    (definitions : List (TypeDef scope)) → AllWf context definitions →
      Wf context (exact definitions)
  | [], .nil => .top
  | [_], .cons witnessWf .nil => .member witnessWf witnessWf
  | _ :: next :: remaining, .cons witnessWf remainingWf =>
      .inter (.member witnessWf witnessWf)
        (exactWf (next :: remaining) remainingWf)

end AllWf

namespace Valid

def nil {scope : Sig} {context : Ctx scope} : Valid context [] where
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
    {definitions : List (TypeDef scope)} (valid : Valid context definitions) :
    Wf context (exact definitions) :=
  valid.witnesses.exactWf definitions

def singleton {scope : Sig} {context : Ctx scope}
    (label : Name) (witness : Ty scope) (witnessWf : Wf context witness) :
    Valid context [⟨label, witness⟩] where
  witnesses := .cons witnessWf .nil
  labelsNoDup := by simp [labels]

end Valid

/-- Validity of a recursive object.  All definitions are checked under one
shared folded self type; nonemptiness and guardedness are explicit fields. -/
structure RecValid {scope : Sig} (context : Ctx scope)
    (definitions : List (TypeDef (scope ▹ .term))) : Type where
  nonempty : definitions ≠ []
  guarded : HeadGuarded (exact definitions)
  witnessGuards : AllGuarded definitions
  witnesses :
    AllWf (context.snoc (.mu (exact definitions))) definitions
  labelsNoDup : (labels definitions).Nodup

namespace RecValid

/-- Construct recursive validity while deriving the head guard from a
nonempty definition list. -/
def checked {scope : Sig} {context : Ctx scope}
    {definitions : List (TypeDef (scope ▹ .term))}
    (nonempty : definitions ≠ [])
    (witnessGuards : AllGuarded definitions)
    (witnesses :
      AllWf (context.snoc (.mu (exact definitions))) definitions)
    (labelsNoDup : (labels definitions).Nodup) :
    RecValid context definitions where
  nonempty := nonempty
  guarded := exactHeadGuarded definitions nonempty
  witnessGuards := witnessGuards
  witnesses := witnesses
  labelsNoDup := labelsNoDup

/-- The recursive body is well formed under its folded self assumption. -/
def bodyWf {scope : Sig} {context : Ctx scope}
    {definitions : List (TypeDef (scope ▹ .term))}
    (valid : RecValid context definitions) :
    Wf (context.snoc (.mu (exact definitions))) (exact definitions) :=
  valid.witnesses.exactWf definitions

/-- A checked recursive definition block forms a well-formed recursive type. -/
def selfTypeWf {scope : Sig} {context : Ctx scope}
    {definitions : List (TypeDef (scope ▹ .term))}
    (valid : RecValid context definitions) :
    Wf context (.mu (exact definitions)) :=
  .mu valid.guarded valid.bodyWf

end RecValid

/-- Duplicate labels cannot be hidden inside a recursive object. -/
theorem RecValid.no_duplicate_pair {scope : Sig} {context : Ctx scope}
    (label : Name) (first second : Ty (scope ▹ .term)) :
    RecValid context [⟨label, first⟩, ⟨label, second⟩] → False := by
  intro valid
  simpa [labels] using valid.labelsNoDup

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
  | recObj {scope : Sig} {context : Ctx scope}
      {definitions : List (TypeDef (scope ▹ .term))}
      (definitionsValid : TypeDefs.RecValid context definitions) :
      HasTy context (.recObj definitions) (.mu (TypeDefs.exact definitions))
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

/-! ## Two-member mutual-recursion regression -/

namespace MutualExample

def firstLabel : Name := 0
def secondLabel : Name := 1

/-- The recursive references themselves. -/
def firstReference : Ty ([] ▹ .term) := .sel .here secondLabel
def secondReference : Ty ([] ▹ .term) := .sel .here firstLabel

/-- Each mutual reference occurs beneath a proper arrow head. -/
def firstWitness : Ty ([] ▹ .term) :=
  .all .top firstReference.weaken

def secondWitness : Ty ([] ▹ .term) :=
  .all .top secondReference.weaken

def definitions : List (TypeDef ([] ▹ .term)) :=
  [⟨firstLabel, firstWitness⟩, ⟨secondLabel, secondWitness⟩]

def body : Ty ([] ▹ .term) := TypeDefs.exact definitions
def objectType : Ty [] := .mu body
def object : Tm [] := .recObj definitions

def bodyGuarded : HeadGuarded body := .inter .member .member

def firstMember : MemberAt body firstLabel firstWitness firstWitness :=
  .left .here

def secondMember : MemberAt body secondLabel secondWitness secondWitness :=
  .right .here

def firstReferenceWf :
    Wf ((Ctx.nil.snoc objectType).snoc .top) firstReference.weaken :=
  .sel (.selfWeaken bodyGuarded secondMember)

def secondReferenceWf :
    Wf ((Ctx.nil.snoc objectType).snoc .top) secondReference.weaken :=
  .sel (.selfWeaken bodyGuarded firstMember)

def firstWitnessWf : Wf (Ctx.nil.snoc objectType) firstWitness :=
  .all .top firstReferenceWf

def secondWitnessWf : Wf (Ctx.nil.snoc objectType) secondWitness :=
  .all .top secondReferenceWf

def witnessesGuarded : TypeDefs.AllGuarded definitions :=
  .cons .all (.cons .all .nil)

def definitionsValid : TypeDefs.RecValid Ctx.nil definitions where
  nonempty := by simp [definitions]
  guarded := bodyGuarded
  witnessGuards := witnessesGuarded
  witnesses := .cons firstWitnessWf (.cons secondWitnessWf .nil)
  labelsNoDup := by decide

/-- Both cross-referencing members are checked under the same self identity. -/
def objectTyping : HasTy Ctx.nil object objectType :=
  .recObj definitionsValid

/-- The whole mutually recursive object type is well formed. -/
def objectTypeWf : Wf Ctx.nil objectType :=
  definitionsValid.selfTypeWf

theorem labels_are_distinct : (TypeDefs.labels definitions).Nodup :=
  definitionsValid.labelsNoDup

/-! A direct alias cycle has the same outer exact-member body shape, but its
definition witnesses have no proper guard and are rejected. -/

def directAliasDefinitions : List (TypeDef ([] ▹ .term)) :=
  [⟨firstLabel, firstReference⟩, ⟨secondLabel, secondReference⟩]

theorem directAlias_not_guarded :
    TypeDefs.AllGuarded directAliasDefinitions → False := by
  intro guarded
  cases guarded with
  | cons firstGuarded _ => cases firstGuarded

theorem directAlias_not_valid :
    TypeDefs.RecValid Ctx.nil directAliasDefinitions → False := by
  intro valid
  exact directAlias_not_guarded valid.witnessGuards

end MutualExample

/-- A naked self selection cannot serve as a recursive body head. -/
theorem selection_not_headGuarded {scope : Sig}
    (path : BVar scope .term) (label : Name) :
    HeadGuarded (.sel path label) → False := by
  intro guarded
  cases guarded

end DotFCR.Source
