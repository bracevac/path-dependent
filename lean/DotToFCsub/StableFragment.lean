import DotToFCsub.Layout
import DotFC.Explicit.SourceContext
import DotFC.Source.Structural

/-!
# Stable-root source fragment for the DOT-to-FCsub bridge

The Milestone-3 layout allocates an FCsub name only for a source path whose
actual declaration is a member with the selected label.  This file makes that
boundary explicit without mentioning the target checker.

Adjusted and exposed views remain available, but they are admitted only when
the same path has a syntactic member root and the requested view is connected
to that root by stable, member-preserving evidence.  Member arguments use the
same discipline: subsumption may change bounds, but may not manufacture a
member identity from a plain declaration.
-/

namespace DotToFCsub.StableFragment

open DotFC
open DotFC.Source

/-- The actual source declaration that owns the stable identity `(path,label)`.
The stored bounds are root bounds, not bounds obtained only from a view. -/
structure StableRoot {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) : Type where
  lower : DotFC.Source.Ty source
  upper : DotFC.Source.Ty source
  lookup : DotFC.Source.Lookup context path (.member label lower upper)

namespace StableRoot

/-- A direct member lookup is the canonical stable root. -/
def ofLookup {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    StableRoot context path label :=
  ⟨lower, upper, lookup⟩

/-- A stable root cannot simultaneously be declared bottom. -/
theorem notBottom {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label)
    (bottom : DotFC.Source.Lookup context path .bot) : False := by
  have equality := DotFC.Source.Lookup.functional root.lookup bottom
  cases equality

/-- The executable layout allocates a complete canonical FCsub slot for every
stable root.  This is the lookup fact needed by lower/upper and member-argument
compilation. -/
theorem fullSlot_exists {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) :
    ∃ slot, DotToFCsub.Layout.fullSlot?
      (DotFC.Explicit.Ctx.ofSource context) path label = some slot := by
  cases root with
  | mk rootLower rootUpper lookup =>
      generalize typeEq :
        (DotFC.Source.Ty.member label rootLower rootUpper) = type at lookup
      induction lookup with
      | @here source context bound =>
          cases bound <;>
            simp_all [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename]
      | @there source context bound type path lookup induction =>
          cases type with
          | top => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
          | bot => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
          | all domain codomain =>
              simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
          | sel selected selectedLabel =>
              simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
          | member rootLabel lower upper =>
              simp only [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
              injection typeEq with labelEq lowerEq upperEq
              subst rootLabel
              obtain ⟨slot, slotLookup⟩ := induction lower upper rfl
              refine ⟨slot.rename
                (DotToFCsub.Layout.extendRename
                  (DotFC.Explicit.Ctx.ofSource context) (.term bound)), ?_⟩
              cases bound <;>
                simp [DotFC.Explicit.Ctx.extendTerm,
                  DotToFCsub.Layout.fullSlot?, slotLookup]

end StableRoot

/-- Source subtyping shapes that expose pointwise variance between two member
interfaces.  These are precisely the shapes from which a telescope morphism
can be compiled without running source subtyping in the target checker. -/
inductive MemberPreserving :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {left right : DotFC.Source.Ty source} →
    DotFC.Source.Sub context left right → Type where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      (formation : DotFC.Source.Wf context (.member label lower upper)) :
      MemberPreserving (.refl formation)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      (lower : DotFC.Source.Sub context lower₂ lower₁)
      (upper : DotFC.Source.Sub context upper₁ upper₂) :
      MemberPreserving (.member (label := label) lower upper)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ lower₃ upper₃ :
        DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context
        (.member label lower₁ upper₁) (.member label lower₂ upper₂)}
      {second : DotFC.Source.Sub context
        (.member label lower₂ upper₂) (.member label lower₃ upper₃)}
      (firstPreserving : MemberPreserving first)
      (secondPreserving : MemberPreserving second) :
      MemberPreserving (.trans first second)

mutual

/-- Formation admissibility.  Every selection is justified by a stable-root
handle, recursively through all type components. -/
inductive StableWf : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} →
    (valid : context.Valid) →
    {type : DotFC.Source.Ty source} →
    DotFC.Source.Wf context type → Type where
  | top {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} : StableWf valid DotFC.Source.Wf.top
  | bot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} : StableWf valid DotFC.Source.Wf.bot
  | all {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {domain : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context domain}
      {codomainWf : DotFC.Source.Wf (context.snoc domain) codomain}
      (domainStable : StableWf valid domainWf)
      (codomainStable : StableWf (.snoc valid domainWf) codomainWf) :
      StableWf valid (.all domainWf codomainWf)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {lowerWf : DotFC.Source.Wf context lower}
      {upperWf : DotFC.Source.Wf context upper}
      (lowerStable : StableWf valid lowerWf)
      (upperStable : StableWf valid upperWf) :
      StableWf valid (.member (label := label) lowerWf upperWf)
  | sel {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      (stable : StableHandle valid handle) : StableWf valid (.sel handle)

/-- Stable subtyping admissibility.  It combines recursive formation, stable
selection roots, and the plain/member interface split needed by FCsub function
coercions. -/
inductive StableSub : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} →
    (valid : context.Valid) →
    {left right : DotFC.Source.Ty source} →
    DotFC.Source.Sub context left right → Type where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {type : DotFC.Source.Ty source}
      {formation : DotFC.Source.Wf context type}
      (stable : StableWf valid formation) : StableSub valid (.refl formation)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {left middle right : DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context left middle}
      {second : DotFC.Source.Sub context middle right}
      (firstStable : StableSub valid first)
      (secondStable : StableSub valid second) :
      StableSub valid (.trans first second)
  | bot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {type : DotFC.Source.Ty source}
      {formation : DotFC.Source.Wf context type}
      (stable : StableWf valid formation) : StableSub valid (.bot formation)
  | top {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {type : DotFC.Source.Ty source}
      {formation : DotFC.Source.Wf context type}
      (stable : StableWf valid formation) : StableSub valid (.top formation)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {lower : DotFC.Source.Sub context lower₂ lower₁}
      {upper : DotFC.Source.Sub context upper₁ upper₂}
      (lowerStable : StableSub valid lower)
      (upperStable : StableSub valid upper) :
      StableSub valid (.member (label := label) lower upper)
  | lower {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      (stable : StableHandle valid handle) : StableSub valid (.lower handle)
  | upper {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      (stable : StableHandle valid handle) : StableSub valid (.upper handle)
  | allPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {domain₁ domain₂ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context domain₂ domain₁}
      {adjustment : DotFC.Source.CtxMor (context.snoc domain₂)
        (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc domain₂)
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context (.all domain₂ codomain₂)}
      (domainStable : StableSub valid domain)
      (codomainStable : StableSub
        (.snoc valid (DotFC.Source.Sub.sourceWf valid domain)) codomain)
      (sourceStable : StableWf valid sourceWf)
      (targetStable : StableWf valid targetWf)
      (sourcePlain : ∀ label lower upper,
        domain₁ ≠ .member label lower upper)
      (targetPlain : ∀ label lower upper,
        domain₂ ≠ .member label lower upper) :
      StableSub valid
        (.all domain adjustment codomain sourceWf targetWf)
  | allMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context
        (.member label lower₂ upper₂) (.member label lower₁ upper₁)}
      {adjustment : DotFC.Source.CtxMor
        (context.snoc (.member label lower₂ upper₂))
        (context.snoc (.member label lower₁ upper₁))}
      {codomain : DotFC.Source.Sub
        (context.snoc (.member label lower₂ upper₂))
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context
        (.all (.member label lower₁ upper₁) codomain₁)}
      {targetWf : DotFC.Source.Wf context
        (.all (.member label lower₂ upper₂) codomain₂)}
      (domainStable : StableSub valid domain)
      (domainPreserving : MemberPreserving domain)
      (codomainStable : StableSub
        (.snoc valid (DotFC.Source.Sub.sourceWf valid domain)) codomain)
      (sourceStable : StableWf valid sourceWf)
      (targetStable : StableWf valid targetWf) :
      StableSub valid
        (.all domain adjustment codomain sourceWf targetWf)

/-- Stable-root admissibility for reusable handles. -/
inductive StableHandle : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} →
    (valid : context.Valid) →
    {path : DotFC.BVar source .term} → {label : DotFC.Source.Name} →
    {lower upper : DotFC.Source.Ty source} →
    DotFC.Source.Handle context path label lower upper → Type where
  | direct {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
      StableHandle valid (.direct lookup)
  | expose {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name}
      {rootLower rootUpper lower upper : DotFC.Source.Ty source}
      (lookup : DotFC.Source.Lookup context path
        (.member label rootLower rootUpper))
      {view : DotFC.Source.Sub context
        (.member label rootLower rootUpper) (.member label lower upper)}
      (viewStable : StableSub valid view)
      (viewPreserving : MemberPreserving view) :
      StableHandle valid (.expose lookup view)
  | adjust {source : DotFC.Sig}
      {actual viewed : DotFC.Source.Ctx source}
      {valid : actual.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name}
      {rootLower rootUpper lower upper : DotFC.Source.Ty source}
      {adjustment : DotFC.Source.CtxMor actual viewed}
      (adjustmentStable : StableCtxMor valid adjustment)
      (lookup : DotFC.Source.Lookup viewed path (.member label lower upper))
      (root : DotFC.Source.Lookup actual path
        (.member label rootLower rootUpper)) :
      StableHandle valid (.adjust adjustment lookup)

/-- Recursive admissibility for the source context morphism followed by an
adjusted handle.  Each head subtyping derivation is stable, and the head keeps
the plain/member representation split.  Consequently a selected member head
also carries the `MemberPreserving` evidence needed by
`adjustedResultDirect?`. -/
inductive StableCtxMor : {source : DotFC.Sig} →
    {actual viewed : DotFC.Source.Ctx source} →
    (valid : actual.Valid) → DotFC.Source.CtxMor actual viewed → Type where
  | id {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} : StableCtxMor valid .id
  | snocPlain {source : DotFC.Sig}
      {actual viewed : DotFC.Source.Ctx source}
      {valid : actual.Valid} {actualType viewType : DotFC.Source.Ty source}
      {tail : DotFC.Source.CtxMor actual viewed}
      {head : DotFC.Source.Sub actual actualType viewType}
      (tailStable : StableCtxMor valid tail)
      (headStable : StableSub valid head)
      (actualTypeWf : DotFC.Source.Wf actual actualType)
      (actualPlain : ∀ label lower upper,
        actualType ≠ .member label lower upper)
      (viewPlain : ∀ label lower upper,
        viewType ≠ .member label lower upper) :
      StableCtxMor (.snoc valid actualTypeWf) (.snoc tail head)
  | snocMember {source : DotFC.Sig}
      {actual viewed : DotFC.Source.Ctx source}
      {valid : actual.Valid} {label : DotFC.Source.Name}
      {actualLower actualUpper viewLower viewUpper : DotFC.Source.Ty source}
      {tail : DotFC.Source.CtxMor actual viewed}
      {head : DotFC.Source.Sub actual
        (.member label actualLower actualUpper)
        (.member label viewLower viewUpper)}
      (tailStable : StableCtxMor valid tail)
      (headStable : StableSub valid head)
      (headPreserving : MemberPreserving head)
      (actualTypeWf : DotFC.Source.Wf actual
        (.member label actualLower actualUpper)) :
      StableCtxMor (.snoc valid actualTypeWf) (.snoc tail head)

end

namespace StableHandle

/-- Extract the actual member declaration owned by a stable handle. -/
def root {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {valid : context.Valid} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {handle : DotFC.Source.Handle context path label lower upper}
    (stable : StableHandle valid handle) : StableRoot context path label :=
  match stable with
  | .direct lookup => StableRoot.ofLookup lookup
  | .expose lookup _ _ => StableRoot.ofLookup lookup
  | .adjust _ _ root => StableRoot.ofLookup root

/-- Attach independently checked root-to-view evidence to an adjusted handle. -/
def adjusted {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source}
    {valid : actual.Valid} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    (adjustmentStable : StableCtxMor valid adjustment)
    (lookup : DotFC.Source.Lookup viewed path (.member label lower upper))
    (root : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)) :
    StableHandle valid (.adjust adjustment lookup) :=
  .adjust adjustmentStable lookup root

end StableHandle

/-- Stable-root admissibility of the member-typed variable premise of an ANF
application.  It permits bound-changing subsumption, but only along a chain of
member-preserving views rooted at the variable's declaration. -/
inductive StableMemberArgument : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} →
    (valid : context.Valid) →
    {path : DotFC.BVar source .term} → {label : DotFC.Source.Name} →
    {lower upper : DotFC.Source.Ty source} →
    DotFC.Source.HasTy context (.var path) (.member label lower upper) →
    Type where
  | var {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
      StableMemberArgument valid (.var lookup)
  | sub {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name}
      {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
      {typing : DotFC.Source.HasTy context (.var path)
        (.member label sourceLower sourceUpper)}
      (typingStable : StableMemberArgument valid typing)
      {view : DotFC.Source.Sub context
        (.member label sourceLower sourceUpper)
        (.member label targetLower targetUpper)}
      (viewStable : StableSub valid view)
      (viewPreserving : MemberPreserving view)
      {targetWf : DotFC.Source.Wf context
        (.member label targetLower targetUpper)}
      (targetStable : StableWf valid targetWf) :
      StableMemberArgument valid (.sub typing view targetWf)

namespace StableMemberArgument

/-- Extract the root shared by every member-preserving argument view. -/
def root {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {valid : context.Valid} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context (.var path)
      (.member label lower upper)}
    (stable : StableMemberArgument valid typing) :
    StableRoot context path label :=
  match stable with
  | .var lookup => StableRoot.ofLookup lookup
  | .sub inner _ _ _ => root inner

/-- Named smart constructor for member-preserving argument subsumption. -/
def subsume {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {valid : context.Valid} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name}
    {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context (.var path)
      (.member label sourceLower sourceUpper)}
    (typingStable : StableMemberArgument valid typing)
    {view : DotFC.Source.Sub context
      (.member label sourceLower sourceUpper)
      (.member label targetLower targetUpper)}
    (viewStable : StableSub valid view)
    (viewPreserving : MemberPreserving view)
    {targetWf : DotFC.Source.Wf context
      (.member label targetLower targetUpper)}
    (targetStable : StableWf valid targetWf) :
    StableMemberArgument valid (.sub typing view targetWf) :=
  .sub typingStable viewStable viewPreserving targetStable

end StableMemberArgument

/-- Context validity plus stable formation of every stored declaration. -/
inductive StableContext : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} → context.Valid → Type where
  | nil : StableContext DotFC.Source.Ctx.Valid.nil
  | snoc {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      {valid : context.Valid} {typeWf : DotFC.Source.Wf context type}
      (contextStable : StableContext valid)
      (typeStable : StableWf valid typeWf) :
      StableContext (.snoc valid typeWf)

/-- Term-typing admissibility used by a total stable-fragment compiler. -/
inductive StableHasTy : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} →
    (valid : context.Valid) →
    {term : DotFC.Source.Tm source} → {type : DotFC.Source.Ty source} →
    DotFC.Source.HasTy context term type → Type where
  | var {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {path : DotFC.BVar source .term}
      {type : DotFC.Source.Ty source}
      {lookup : DotFC.Source.Lookup context path type}
      (typeStable : StableWf valid (DotFC.Source.Lookup.wf valid lookup)) :
      StableHasTy valid (.var lookup)
  | lam {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {domain : DotFC.Source.Ty source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context domain}
      {bodyTyping : DotFC.Source.HasTy (context.snoc domain) body codomain}
      (domainStable : StableWf valid domainWf)
      (bodyStable : StableHasTy (.snoc valid domainWf) bodyTyping) :
      StableHasTy valid (.lam domainWf bodyTyping)
  | obj {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {label : DotFC.Source.Name}
      {witness : DotFC.Source.Ty source}
      {witnessWf : DotFC.Source.Wf context witness}
      (witnessStable : StableWf valid witnessWf) :
      StableHasTy valid (.obj (label := label) witnessWf)
  | appPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {function argument : DotFC.BVar source .term}
      {domain : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all domain codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument) domain}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      (functionStable : StableHasTy valid functionTyping)
      (argumentStable : StableHasTy valid argumentTyping)
      (resultStable : StableWf valid resultWf)
      (plain : ∀ label lower upper, domain ≠ .member label lower upper) :
      StableHasTy valid (.app functionTyping argumentTyping resultWf)
  | appMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {function argument : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all (.member label lower upper) codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument)
        (.member label lower upper)}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      (functionStable : StableHasTy valid functionTyping)
      (argumentStable : StableHasTy valid argumentTyping)
      (memberArgument : StableMemberArgument valid argumentTyping)
      (resultStable : StableWf valid resultWf) :
      StableHasTy valid (.app functionTyping argumentTyping resultWf)
  | let' {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {rhs : DotFC.Source.Tm source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {bound result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs bound}
      {bodyTyping : DotFC.Source.HasTy (context.snoc bound) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      (rhsStable : StableHasTy valid rhsTyping)
      (bodyStable : StableHasTy
        (.snoc valid (DotFC.Source.HasTy.typeWf valid rhsTyping)) bodyTyping)
      (resultStable : StableWf valid resultWf) :
      StableHasTy valid (.let' rhsTyping bodyTyping resultWf)
  | sub {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid} {term : DotFC.Source.Tm source}
      {sourceType targetType : DotFC.Source.Ty source}
      {termTyping : DotFC.Source.HasTy context term sourceType}
      {subtyping : DotFC.Source.Sub context sourceType targetType}
      {targetWf : DotFC.Source.Wf context targetType}
      (termStable : StableHasTy valid termTyping)
      (subStable : StableSub valid subtyping)
      (targetStable : StableWf valid targetWf) :
      StableHasTy valid (.sub termTyping subtyping targetWf)

/-! Prop wrappers are useful at public theorem boundaries; the Type-valued
certificates above remain directly consumable by a proof-producing compiler. -/

def HasStableRoot {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) : Prop :=
  Nonempty (StableRoot context path label)

def HandleAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (handle : DotFC.Source.Handle context path label lower upper) : Prop :=
  Nonempty (StableHandle valid handle)

def MemberArgumentAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (typing : DotFC.Source.HasTy context (.var path)
      (.member label lower upper)) : Prop :=
  Nonempty (StableMemberArgument valid typing)

def WfAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {type : DotFC.Source.Ty source}
    (formation : DotFC.Source.Wf context type) : Prop :=
  Nonempty (StableWf valid formation)

def ContextAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid) : Prop :=
  Nonempty (StableContext valid)

def CtxMorAdmissible {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} (valid : actual.Valid)
    (adjustment : DotFC.Source.CtxMor actual viewed) : Prop :=
  Nonempty (StableCtxMor valid adjustment)

def SubAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {left right : DotFC.Source.Ty source}
    (subtyping : DotFC.Source.Sub context left right) : Prop :=
  Nonempty (StableSub valid subtyping)

def TermAdmissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (typing : DotFC.Source.HasTy context term type) : Prop :=
  Nonempty (StableHasTy valid typing)

/-- A bottom-derived exposure has no stable member root, despite being legal in
the unrestricted source calculus. -/
theorem bottomDerivedHandle_not_admissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (bottom : DotFC.Source.Lookup context path .bot)
    (view : DotFC.Source.Sub context .bot (.member label lower upper)) :
    ¬ HandleAdmissible valid (DotFC.Source.Handle.expose bottom view) := by
  intro admissible
  obtain ⟨stable⟩ := admissible
  exact stable.root.notBottom bottom

/-- A member argument obtained solely by subsuming a bottom-typed path is
excluded for the same reason. -/
theorem bottomDerivedArgument_not_admissible {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (bottom : DotFC.Source.Lookup context path .bot)
    (view : DotFC.Source.Sub context .bot (.member label lower upper))
    (targetWf : DotFC.Source.Wf context (.member label lower upper)) :
    ¬ MemberArgumentAdmissible valid
      (DotFC.Source.HasTy.sub (DotFC.Source.HasTy.var bottom) view targetWf) := by
  intro admissible
  obtain ⟨stable⟩ := admissible
  exact stable.root.notBottom bottom

end DotToFCsub.StableFragment
