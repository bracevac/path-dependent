import DotFC.Source.Typing

/-!
# Structural lemmas for the source calculus

The strengthened weakening relation below inserts one well-formed binding at
an arbitrary depth in an acyclic context.  Its `lift` constructor is what is
needed below dependent function binders; plain top-level weakening is the
special case `Weakening.insert`.
-/

namespace DotFC.Source

noncomputable section

namespace Lookup

/-- A context assigns at most one type to a variable. -/
theorem functional {s : Sig} {context : Ctx s} {path : BVar s .term}
    {first second : Ty s} (left : Lookup context path first)
    (right : Lookup context path second) : first = second := by
  induction left with
  | here =>
      cases right
      rfl
  | there lookup ih =>
      cases right with
      | there lookup' => exact congrArg Ty.weaken (ih lookup')

end Lookup

/-- Insertion of one well-formed binding, possibly below a suffix of dependent
term bindings.  The stored renaming describes the corresponding scope map. -/
inductive Weakening : {s₁ s₂ : Sig} → Ctx s₁ → Ctx s₂ →
    Rename s₁ s₂ → Type where
  | insert {s : Sig} {context : Ctx s} {bound : Ty s}
      (boundWf : Wf context bound) :
      Weakening context (context.snoc bound) Rename.succ
  | lift {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
      {ρ : Rename s₁ s₂} {bound : Ty s₁}
      (weakening : Weakening source target ρ) :
      Weakening (source.snoc bound) (target.snoc (bound.rename ρ)) ρ.lift

namespace Rename

/-- Opening a dependent type commutes with renaming its free context. -/
theorem openAt_comp {s₁ s₂ : Sig} (ρ : Rename s₁ s₂)
    (path : BVar s₁ .term) :
    (openAt path).comp ρ = ρ.lift.comp (openAt (ρ.var path)) := by
  apply Rename.ext
  intro k x
  cases x <;> rfl

end Rename

namespace Ty

/-- Type opening commutes with a renaming of the surrounding context. -/
theorem open_rename {s₁ s₂ : Sig} (type : Ty (s₁ ▹ .term))
    (path : BVar s₁ .term) (ρ : Rename s₁ s₂) :
    (type.open path).rename ρ =
      (type.rename ρ.lift).open (ρ.var path) := by
  simp only [Ty.open, Ty.rename_comp, Rename.openAt_comp]

/-- Weakening below a binder commutes with renaming the surrounding scope. -/
theorem weaken_rename {s₁ s₂ : Sig} (type : Ty s₁) (ρ : Rename s₁ s₂) :
    (Ty.weaken (kind := .term) type).rename (ρ.lift (k := .term)) =
      Ty.weaken (kind := .term) (type.rename ρ) := by
  simp only [Ty.weaken, Ty.rename_comp, Rename.succ_lift_comm]

end Ty

/-! A common rank makes termination across the mutually inductive static
certificates explicit. -/

mutual

def Wf.rank {s : Sig} {context : Ctx s} {type : Ty s} :
    Wf context type → Nat
  | .top => 1
  | .bot => 1
  | .all domain codomain => domain.rank + codomain.rank + 1
  | .member lower upper => lower.rank + upper.rank + 1
  | .sel exposure => exposure.rank + 1

def Sub.rank {s : Sig} {context : Ctx s} {left right : Ty s} :
    Sub context left right → Nat
  | .refl typeWf => typeWf.rank + 1
  | .trans first second => first.rank + second.rank + 1
  | .bot typeWf => typeWf.rank + 1
  | .top typeWf => typeWf.rank + 1
  | .member lower upper => lower.rank + upper.rank + 1
  | .lower exposure => exposure.rank + 1
  | .upper exposure => exposure.rank + 1
  | .all domain adjustment codomain sourceWf targetWf =>
      domain.rank + adjustment.rank + codomain.rank +
        sourceWf.rank + targetWf.rank + 1

def CtxMor.rank {s : Sig} {actual view : Ctx s} : CtxMor actual view → Nat
  | .id => 1
  | .snoc tail head => tail.rank + head.rank + 1

def Handle.rank {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {lower upper : Ty s} :
    Handle context path label lower upper → Nat
  | .direct _ => 1
  | .adjust adjustment _ => adjustment.rank + 1
  | .expose _ view => view.rank + 1

end

@[simp]
theorem Wf.rank_all {s : Sig} {context : Ctx s} {domain : Ty s}
    {codomain : Ty (s ▹ .term)} (domainWf : Wf context domain)
    (codomainWf : Wf (context.snoc domain) codomain) :
    Wf.rank (.all domainWf codomainWf) =
      domainWf.rank + codomainWf.rank + 1 := rfl

@[simp]
theorem Wf.rank_top {s : Sig} {context : Ctx s} :
    Wf.rank (.top : Wf context .top) = 1 := rfl

@[simp]
theorem Wf.rank_bot {s : Sig} {context : Ctx s} :
    Wf.rank (.bot : Wf context .bot) = 1 := rfl

@[simp]
theorem Wf.rank_member {s : Sig} {context : Ctx s} {label : Name}
    {lower upper : Ty s} (lowerWf : Wf context lower)
    (upperWf : Wf context upper) :
    Wf.rank (.member lowerWf upperWf : Wf context (.member label lower upper)) =
      lowerWf.rank + upperWf.rank + 1 := rfl

@[simp]
theorem Wf.rank_sel {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {lower upper : Ty s}
    (exposure : Handle context path label lower upper) :
    Wf.rank (.sel exposure) = exposure.rank + 1 := rfl

@[simp]
theorem Sub.rank_refl {s : Sig} {context : Ctx s} {type : Ty s}
    (typeWf : Wf context type) :
    Sub.rank (.refl typeWf) = typeWf.rank + 1 := rfl

@[simp]
theorem Sub.rank_trans {s : Sig} {context : Ctx s} {source middle target : Ty s}
    (first : Sub context source middle) (second : Sub context middle target) :
    Sub.rank (.trans first second) = first.rank + second.rank + 1 := rfl

@[simp]
theorem Sub.rank_bot {s : Sig} {context : Ctx s} {type : Ty s}
    (typeWf : Wf context type) :
    Sub.rank (.bot typeWf) = typeWf.rank + 1 := rfl

@[simp]
theorem Sub.rank_top {s : Sig} {context : Ctx s} {type : Ty s}
    (typeWf : Wf context type) :
    Sub.rank (.top typeWf) = typeWf.rank + 1 := rfl

@[simp]
theorem Sub.rank_member {s : Sig} {context : Ctx s} {label : Name}
    {lower₁ upper₁ lower₂ upper₂ : Ty s}
    (lower : Sub context lower₂ lower₁) (upper : Sub context upper₁ upper₂) :
    Sub.rank (.member lower upper :
      Sub context (.member label lower₁ upper₁) (.member label lower₂ upper₂)) =
      lower.rank + upper.rank + 1 := rfl

@[simp]
theorem Sub.rank_lower {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {lower upper : Ty s}
    (exposure : Handle context path label lower upper) :
    Sub.rank (.lower exposure) = exposure.rank + 1 := rfl

@[simp]
theorem Sub.rank_upper {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {lower upper : Ty s}
    (exposure : Handle context path label lower upper) :
    Sub.rank (.upper exposure) = exposure.rank + 1 := rfl

@[simp]
theorem Sub.rank_all {s : Sig} {context : Ctx s} {domain₁ domain₂ : Ty s}
    {codomain₁ codomain₂ : Ty (s ▹ .term)}
    (domain : Sub context domain₂ domain₁)
    (adjustment : CtxMor (context.snoc domain₂) (context.snoc domain₁))
    (codomain : Sub (context.snoc domain₂) codomain₁ codomain₂)
    (sourceWf : Wf context (.all domain₁ codomain₁))
    (targetWf : Wf context (.all domain₂ codomain₂)) :
    Sub.rank (.all domain adjustment codomain sourceWf targetWf) =
      domain.rank + adjustment.rank + codomain.rank +
        sourceWf.rank + targetWf.rank + 1 := rfl

@[simp]
theorem CtxMor.rank_id {s : Sig} {context : Ctx s} :
    CtxMor.rank (.id : CtxMor context context) = 1 := rfl

@[simp]
theorem CtxMor.rank_snoc {s : Sig} {actual view : Ctx s}
    {actualType viewType : Ty s} (tail : CtxMor actual view)
    (head : Sub actual actualType viewType) :
    CtxMor.rank (.snoc tail head) = tail.rank + head.rank + 1 := rfl

@[simp]
theorem Handle.rank_direct {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {lower upper : Ty s}
    (binding : Lookup context path (.member label lower upper)) :
    Handle.rank (.direct binding) = 1 := rfl

@[simp]
theorem Handle.rank_adjust {s : Sig} {actual view : Ctx s}
    {path : BVar s .term} {label : Name} {lower upper : Ty s}
    (adjustment : CtxMor actual view)
    (binding : Lookup view path (.member label lower upper)) :
    Handle.rank (.adjust adjustment binding) = adjustment.rank + 1 := rfl

@[simp]
theorem Handle.rank_expose {s : Sig} {context : Ctx s} {path : BVar s .term}
    {label : Name} {declared lower upper : Ty s}
    (binding : Lookup context path declared)
    (view : Sub context declared (.member label lower upper)) :
    Handle.rank (.expose binding view) = view.rank + 1 := rfl

namespace Lookup

/-- Transport lookup through an insertion at any depth. -/
def weakenAlong {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {ρ : Rename s₁ s₂} (weakening : Weakening source target ρ)
    {path : BVar s₁ .term} {type : Ty s₁}
    (lookup : Lookup source path type) :
    Lookup target (ρ.var path) (type.rename ρ) := by
  induction weakening with
  | insert boundWf =>
      exact .there lookup
  | @lift s₁ s₂ source target ρ bound weakening ih =>
      cases lookup with
      | here =>
          simpa only [Ty.weaken, Ty.rename_comp, Rename.succ_lift_comm] using
            (Lookup.here :
              Lookup (target.snoc (bound.rename ρ)) .here
                (bound.rename ρ).weaken)
      | @there _ _ _ type path lookup =>
          simpa only [Ty.weaken, Ty.rename_comp, Rename.succ_lift_comm] using
            Lookup.there (ih lookup)

end Lookup

mutual

/-- Well-formedness is stable under insertion of a well-formed binding at any
depth. -/
def Wf.weakenAlong {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {ρ : Rename s₁ s₂} (weakening : Weakening source target ρ)
    {type : Ty s₁} (derivation : Wf source type) :
    Wf target (type.rename ρ) :=
  match derivation with
  | .top => .top
  | .bot => .bot
  | .all domain codomain =>
      .all (Wf.weakenAlong weakening domain)
        (Wf.weakenAlong (.lift weakening) codomain)
  | .member lower upper =>
      .member (Wf.weakenAlong weakening lower) (Wf.weakenAlong weakening upper)
  | .sel exposure => .sel (Handle.weakenAlong weakening exposure)
termination_by derivation.rank

/-- Subtyping is stable under insertion at any depth. -/
def Sub.weakenAlong {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {ρ : Rename s₁ s₂} (weakening : Weakening source target ρ)
    {left right : Ty s₁} (derivation : Sub source left right) :
    Sub target (left.rename ρ) (right.rename ρ) :=
  match derivation with
  | .refl typeWf => .refl (Wf.weakenAlong weakening typeWf)
  | .trans first second =>
      .trans (Sub.weakenAlong weakening first) (Sub.weakenAlong weakening second)
  | .bot typeWf => .bot (Wf.weakenAlong weakening typeWf)
  | .top typeWf => .top (Wf.weakenAlong weakening typeWf)
  | .member lower upper =>
      .member (Sub.weakenAlong weakening lower) (Sub.weakenAlong weakening upper)
  | .lower exposure => .lower (Handle.weakenAlong weakening exposure)
  | .upper exposure => .upper (Handle.weakenAlong weakening exposure)
  | .all domain _ codomain sourceWf targetWf =>
      let domain' := Sub.weakenAlong weakening domain
      .all domain' (.snoc .id domain')
        (Sub.weakenAlong (.lift weakening) codomain)
        (Wf.weakenAlong weakening sourceWf)
        (Wf.weakenAlong weakening targetWf)
termination_by derivation.rank

/-- Transport a context morphism through the same insertion operation on its
actual context.  At the insertion point the view receives `⊤`; this is always
well formed, and the actual inserted type is related to it by `Sub.top`. -/
def Weakening.transportMor {s₁ s₂ : Sig} {actual : Ctx s₁}
    {actual' : Ctx s₂} {ρ : Rename s₁ s₂}
    (weakening : Weakening actual actual' ρ) {view : Ctx s₁}
    (adjustment : CtxMor actual view) (budget : Nat)
    (rankEq : adjustment.rank = budget) :
    Σ view' : Ctx s₂, Weakening view view' ρ × CtxMor actual' view' := by
  cases adjustment with
  | id => exact ⟨actual', weakening, .id⟩
  | @snoc s actualBase viewBase actualType viewType tail head =>
      cases weakening with
      | insert boundWf =>
          exact ⟨(viewBase.snoc viewType).snoc .top, .insert .top,
            .snoc (CtxMor.snoc tail head) (.top boundWf)⟩
      | lift weakening =>
          have rankEquation : tail.rank + head.rank + 1 = budget := by
            simpa using rankEq
          let ⟨view', viewWeakening, tail'⟩ :=
            Weakening.transportMor weakening tail tail.rank rfl
          exact ⟨view'.snoc _, .lift viewWeakening,
            .snoc tail' (Sub.weakenAlong weakening head)⟩
termination_by budget

/-- Reusable member exposure is stable under insertion. -/
def Handle.weakenAlong {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {ρ : Rename s₁ s₂} (weakening : Weakening source target ρ)
    {path : BVar s₁ .term} {label : Name} {lower upper : Ty s₁}
    (exposure : Handle source path label lower upper) :
    Handle target (ρ.var path) label (lower.rename ρ) (upper.rename ρ) :=
  match exposure with
  | .direct binding => .direct (Lookup.weakenAlong weakening binding)
  | .expose binding view =>
      .expose (Lookup.weakenAlong weakening binding)
        (Sub.weakenAlong weakening view)
  | .adjust adjustment binding =>
      let ⟨_, viewWeakening, adjustment'⟩ :=
        Weakening.transportMor weakening adjustment adjustment.rank rfl
      .adjust adjustment' (Lookup.weakenAlong viewWeakening binding)
termination_by exposure.rank

decreasing_by
  all_goals repeat first | cases ‹_ ≍ _›
  all_goals subst_vars
  all_goals simp_all [Handle.rank]
  all_goals try rw [CtxMor.rank_snoc] at rankEq
  all_goals simp [Wf.rank, Sub.rank, CtxMor.rank, Handle.rank] <;> omega

end

namespace Wf

/-- Ordinary one-binding weakening. -/
def weaken {s : Sig} {context : Ctx s} {bound type : Ty s}
    (boundWf : Wf context bound) (derivation : Wf context type) :
    Wf (context.snoc bound) type.weaken :=
  Wf.weakenAlong (.insert boundWf) derivation

end Wf

namespace Sub

/-- Ordinary one-binding weakening. -/
def weaken {s : Sig} {context : Ctx s} {bound left right : Ty s}
    (boundWf : Wf context bound) (derivation : Sub context left right) :
    Sub (context.snoc bound) left.weaken right.weaken :=
  Sub.weakenAlong (.insert boundWf) derivation

end Sub

namespace Handle

/-- Ordinary one-binding weakening. -/
def weaken {s : Sig} {context : Ctx s} {bound lower upper : Ty s}
    {path : BVar s .term} {label : Name} (boundWf : Wf context bound)
    (exposure : Handle context path label lower upper) :
    Handle (context.snoc bound) (.there path) label lower.weaken upper.weaken :=
  Handle.weakenAlong (.insert boundWf) exposure

end Handle

namespace Lookup

/-- Every declaration retrieved from a valid context is well formed in the
full current context. -/
def wf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {path : BVar s .term} {type : Ty s} (lookup : Lookup context path type) :
    Wf context type := by
  induction lookup with
  | here =>
      cases contextValid with
      | snoc _ typeWf => exact Wf.weaken typeWf typeWf
  | there lookup ih =>
      cases contextValid with
      | snoc tailValid boundWf => exact Wf.weaken boundWf (ih tailValid)

end Lookup

namespace CtxMor

/-- Extract the pointwise content of a context morphism.  A lookup in the view
produces an actual declaration and directed evidence from that declaration to
the viewed type, all in the full current scope. -/
def lookupTransport {s : Sig} {actual view : Ctx s}
    (adjustment : CtxMor actual view) (actualValid : actual.Valid)
    {path : BVar s .term} {viewType : Ty s}
    (binding : Lookup view path viewType) :
    Σ actualType : Ty s,
      Lookup actual path actualType × Sub actual actualType viewType := by
  cases adjustment with
  | id =>
      exact ⟨viewType, binding, .refl (Lookup.wf actualValid binding)⟩
  | @snoc s actual view actualType viewType tail head =>
      cases actualValid with
      | snoc tailValid actualTypeWf =>
          cases binding with
          | here =>
              exact ⟨actualType.weaken, .here, Sub.weaken actualTypeWf head⟩
          | there binding =>
              let ⟨found, foundBinding, foundSub⟩ :=
                lookupTransport tail tailValid binding
              exact ⟨found.weaken, .there foundBinding,
                Sub.weaken actualTypeWf foundSub⟩

end CtxMor

/-! ## Endpoint formation

The explicit endpoint premises on dependent-function subtyping make formation
structural.  Selection endpoints use context validity to recover the bounds of
their reusable exposure handle. -/

mutual

/-- The source endpoint of a subtyping certificate is well formed. -/
def Sub.sourceWf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {source target : Ty s} (derivation : Sub context source target) :
    Wf context source :=
  match derivation with
  | .refl typeWf => typeWf
  | .trans first _ => Sub.sourceWf contextValid first
  | .bot _ => .bot
  | .top typeWf => typeWf
  | .member lower upper =>
      .member (Sub.targetWf contextValid lower) (Sub.sourceWf contextValid upper)
  | .lower exposure => Handle.lowerWf contextValid exposure
  | .upper exposure => .sel exposure
  | .all _ _ _ sourceWf _ => sourceWf
termination_by derivation.rank

/-- The target endpoint of a subtyping certificate is well formed. -/
def Sub.targetWf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {source target : Ty s} (derivation : Sub context source target) :
    Wf context target :=
  match derivation with
  | .refl typeWf => typeWf
  | .trans _ second => Sub.targetWf contextValid second
  | .bot typeWf => typeWf
  | .top _ => .top
  | .member lower upper =>
      .member (Sub.sourceWf contextValid lower) (Sub.targetWf contextValid upper)
  | .lower exposure => .sel exposure
  | .upper exposure => Handle.upperWf contextValid exposure
  | .all _ _ _ _ targetWf => targetWf
termination_by derivation.rank

/-- The lower bound exposed by a reusable handle is well formed. -/
def Handle.lowerWf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {path : BVar s .term} {label : Name} {lower upper : Ty s}
    (exposure : Handle context path label lower upper) : Wf context lower := by
  cases exposure with
  | direct binding =>
      have memberWf := Lookup.wf contextValid binding
      cases memberWf with
      | member lowerWf _ => exact lowerWf
  | expose _ view =>
      have memberWf := Sub.targetWf contextValid view
      cases memberWf with
      | member lowerWf _ => exact lowerWf
  | adjust adjustment binding =>
      have memberWf := CtxMor.lookupWfBudget adjustment contextValid binding
        adjustment.rank rfl
      cases memberWf with
      | member lowerWf _ => exact lowerWf
termination_by exposure.rank

/-- The upper bound exposed by a reusable handle is well formed. -/
def Handle.upperWf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {path : BVar s .term} {label : Name} {lower upper : Ty s}
    (exposure : Handle context path label lower upper) : Wf context upper := by
  cases exposure with
  | direct binding =>
      have memberWf := Lookup.wf contextValid binding
      cases memberWf with
      | member _ upperWf => exact upperWf
  | expose _ view =>
      have memberWf := Sub.targetWf contextValid view
      cases memberWf with
      | member _ upperWf => exact upperWf
  | adjust adjustment binding =>
      have memberWf := CtxMor.lookupWfBudget adjustment contextValid binding
        adjustment.rank rfl
      cases memberWf with
      | member _ upperWf => exact upperWf
termination_by exposure.rank

/-- A viewed lookup transported along a context morphism is well formed in the
actual context.  `budget` exposes a plain natural termination measure for the
mutually inductive context-morphism proof. -/
def CtxMor.lookupWfBudget {s : Sig} {actual view : Ctx s}
    (adjustment : CtxMor actual view) (actualValid : actual.Valid)
    {path : BVar s .term} {viewType : Ty s}
    (binding : Lookup view path viewType) (budget : Nat)
    (rankEq : adjustment.rank = budget) : Wf actual viewType := by
  cases adjustment with
  | id => exact Lookup.wf actualValid binding
  | @snoc s actual view actualType viewType tail head =>
      have rankEquation : tail.rank + head.rank + 1 = budget := by
        simpa using rankEq
      cases actualValid with
      | snoc tailValid actualTypeWf =>
          cases binding with
          | here =>
              exact Wf.weaken actualTypeWf (Sub.targetWf tailValid head)
          | there binding =>
              exact Wf.weaken actualTypeWf
                (CtxMor.lookupWfBudget tail tailValid binding tail.rank rfl)
termination_by budget

decreasing_by
  all_goals subst_vars
  all_goals simp_all
  all_goals omega

end


namespace CtxMor

/-- Public formation corollary for a lookup through an adjusted view. -/
def lookupWf {s : Sig} {actual view : Ctx s}
    (adjustment : CtxMor actual view) (actualValid : actual.Valid)
    {path : BVar s .term} {viewType : Ty s}
    (binding : Lookup view path viewType) : Wf actual viewType :=
  lookupWfBudget adjustment actualValid binding adjustment.rank rfl

end CtxMor

namespace HasTy

/-- Typing is stable under insertion at any depth. -/
def weakenAlong {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {ρ : Rename s₁ s₂} (weakening : Weakening source target ρ)
    {term : Tm s₁} {type : Ty s₁} (derivation : HasTy source term type) :
    HasTy target (term.rename ρ) (type.rename ρ) :=
  match derivation with
  | .var binding => .var (Lookup.weakenAlong weakening binding)
  | .lam domainWf bodyTyping =>
      .lam (Wf.weakenAlong weakening domainWf)
        (HasTy.weakenAlong (.lift weakening) bodyTyping)
  | .obj witnessWf => .obj (Wf.weakenAlong weakening witnessWf)
  | .app functionTyping argumentTyping resultWf => by
      have resultWf' := Wf.weakenAlong weakening resultWf
      rw [Ty.open_rename] at resultWf'
      simpa only [Tm.rename, Ty.open_rename] using
        HasTy.app (HasTy.weakenAlong weakening functionTyping)
          (HasTy.weakenAlong weakening argumentTyping) resultWf'
  | .let' rhsTyping bodyTyping resultWf => by
      have bodyTyping' := HasTy.weakenAlong (.lift weakening) bodyTyping
      rw [Ty.weaken_rename] at bodyTyping'
      exact HasTy.let' (HasTy.weakenAlong weakening rhsTyping) bodyTyping'
        (Wf.weakenAlong weakening resultWf)
  | .sub termTyping subtyping targetWf =>
      .sub (HasTy.weakenAlong weakening termTyping)
        (Sub.weakenAlong weakening subtyping)
        (Wf.weakenAlong weakening targetWf)

/-- Ordinary one-binding weakening for term typing. -/
def weaken {s : Sig} {context : Ctx s} {bound type : Ty s} {term : Tm s}
    (boundWf : Wf context bound) (derivation : HasTy context term type) :
    HasTy (context.snoc bound) term.weaken type.weaken :=
  weakenAlong (.insert boundWf) derivation

/-- The result type of a typing certificate is well formed in a valid
context. -/
def typeWf {s : Sig} {context : Ctx s} (contextValid : context.Valid)
    {term : Tm s} {type : Ty s} (derivation : HasTy context term type) :
    Wf context type :=
  match derivation with
  | .var binding => Lookup.wf contextValid binding
  | .lam domainWf bodyTyping =>
      .all domainWf (HasTy.typeWf (.snoc contextValid domainWf) bodyTyping)
  | .obj witnessWf => .member witnessWf witnessWf
  | .app _ _ resultWf => resultWf
  | .let' _ _ resultWf => resultWf
  | .sub _ _ targetWf => targetWf

end HasTy

end

end DotFC.Source
