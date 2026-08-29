import DotFC.Explicit.Typing

/-!
# Executable structural checker

This module depends only on the explicit syntax, context, and endpoint
judgments.  In particular it does not import declarative source typing or
source subtyping.  The internal checked-result structures retain a
`Type`-valued derivation; the public `synth*` functions erase that derivation
and return only structurally synthesized endpoints.

The checker accepts already intrinsically scoped syntax.  It does not claim
declarative `Source.Wf` for retained type annotations: selections are opaque
at formation time.  A selection can affect evidence only when an explicit
`Exposure` checks and binds a reusable `.member` handle, since `lower` and
`upper` have no path-based constructors.  The public scope-checking API below
states this deliberately narrow formation contract without importing source
typing or source subtyping.
-/

namespace DotFC.Explicit

open DotFC

abbrev Endpoints (s : Sig) := Source.Ty s × Source.Ty s

private structure EqChecked {s : Sig} (context : Ctx s) (evidence : EqCo s) where
  source : Source.Ty s
  target : Source.Ty s
  typing : EqCo.HasType context evidence source target

private structure LeChecked {s : Sig} (context : Ctx s) (evidence : LeCo s) where
  source : Source.Ty s
  target : Source.Ty s
  typing : LeCo.HasType context evidence source target

private structure ExposureChecked {s : Sig} (context : Ctx s)
    (exposure : Exposure s) where
  member : MemberSpec s
  typing : Exposure.HasType context exposure member

private structure MorChecked {s : Sig} (actual : Ctx s) (morphism : CtxMor s) where
  view : Ctx s
  typing : CtxMor.HasType actual view morphism

private structure TmChecked {s : Sig} (context : Ctx s) (term : Tm s) where
  type : Source.Ty s
  typing : Tm.HasType context term type

/-! ## Internal proof-producing checkers -/

private def checkEqCore {s : Sig} (context : Ctx s) (evidence : EqCo s) :
    Option (EqChecked context evidence) :=
  match evidence with
  | .var index =>
      let endpoints := (context.lookup index).equalityEndpoints
      some ⟨endpoints.1, endpoints.2, EqCo.HasType.var index⟩
  | .refl type => some ⟨type, type, .refl type⟩
  | .symm inner => do
      let checked ← checkEqCore context inner
      pure ⟨checked.target, checked.source, .symm checked.typing⟩
  | .trans first second => do
      let firstChecked ← checkEqCore context first
      let secondChecked ← checkEqCore context second
      if middle : firstChecked.target = secondChecked.source then
        let secondTyping : EqCo.HasType context second firstChecked.target
            secondChecked.target := by
          simpa [middle] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .trans firstChecked.typing secondTyping⟩
      else
        none

mutual

private def checkLeCore {s : Sig} (context : Ctx s) (evidence : LeCo s) :
    Option (LeChecked context evidence) :=
  match evidence with
  | .var index =>
      let endpoints := (context.lookup index).inclusionEndpoints
      some ⟨endpoints.1, endpoints.2, LeCo.HasType.var index⟩
  | .refl type => some ⟨type, type, .refl type⟩
  | .trans first second => do
      let firstChecked ← checkLeCore context first
      let secondChecked ← checkLeCore context second
      if middle : firstChecked.target = secondChecked.source then
        let secondTyping : LeCo.HasType context second firstChecked.target
            secondChecked.target := by
          simpa [middle] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .trans firstChecked.typing secondTyping⟩
      else
        none
  | .top source => some ⟨source, .top, .top source⟩
  | .bot target => some ⟨.bot, target, .bot target⟩
  | .eqToLe equality => do
      let checked ← checkEqCore context equality
      pure ⟨checked.source, checked.target, .eqToLe checked.typing⟩
  | .member label lower upper => do
      let lowerChecked ← checkLeCore context lower
      let upperChecked ← checkLeCore context upper
      pure ⟨.member label lowerChecked.target upperChecked.source,
        .member label lowerChecked.source upperChecked.target,
        .member lowerChecked.typing upperChecked.typing⟩
  | .all domain view codomain => do
      let domainChecked ← checkLeCore context domain
      let actualContext := context.extendTerm domainChecked.source
      let expectedView := context.extendTerm domainChecked.target
      let viewChecked ← checkMorCore actualContext view
      if sameView : viewChecked.view = expectedView then
        let viewTyping : CtxMor.HasType actualContext expectedView view := by
          simpa [sameView] using viewChecked.typing
        let codomainChecked ← checkLeCore actualContext codomain
        pure ⟨.all domainChecked.target codomainChecked.source,
          .all domainChecked.source codomainChecked.target,
          .all domainChecked.typing viewTyping codomainChecked.typing⟩
      else
        none
  | .lower handle =>
      let member := (context.lookup handle).memberSpec
      some ⟨member.lower, .sel member.path member.label,
        LeCo.HasType.lower⟩
  | .upper handle =>
      let member := (context.lookup handle).memberSpec
      some ⟨.sel member.path member.label, member.upper,
        LeCo.HasType.upper⟩
  | .letHandle exposure body => do
      let exposureChecked ← checkExposureCore context exposure
      let bodyChecked ←
        checkLeCore (context.extendMember exposureChecked.member) body
      pure ⟨ScopedTy.dropMember bodyChecked.source,
        ScopedTy.dropMember bodyChecked.target,
        .letHandle exposureChecked.typing bodyChecked.typing⟩

private def checkExposureCore {s : Sig} (context : Ctx s)
    (exposure : Exposure s) : Option (ExposureChecked context exposure) :=
  match exposure with
  | .view path label lower upper inclusion =>
      let actual := (context.lookup path).termType
      do
        let inclusionChecked ← checkLeCore context inclusion
        if sameSource : inclusionChecked.source = actual then
          if sameTarget : inclusionChecked.target = .member label lower upper then
            let inclusionTyping : LeCo.HasType context inclusion actual
                (.member label lower upper) := by
              simpa [sameSource, sameTarget] using inclusionChecked.typing
            pure ⟨⟨path, label, lower, upper⟩,
              Exposure.HasType.view inclusionTyping⟩
          else
            none
        else
          none

private def checkMorCore {s : Sig} (actual : Ctx s) (morphism : CtxMor s) :
    Option (MorChecked actual morphism) :=
  match morphism, actual with
  | .refl, actual => some ⟨actual, .refl⟩
  | .function domain, .extend outer (.term actualDomain) => do
      let domainChecked ← checkLeCore outer domain
      if sameDomain : domainChecked.source = actualDomain then
        let domainTyping : LeCo.HasType outer domain actualDomain
            domainChecked.target := by
          simpa [sameDomain] using domainChecked.typing
        pure ⟨outer.extendTerm domainChecked.target,
          CtxMor.HasType.function domainTyping⟩
      else
        none

end

private theorem checkMorCore_refl_complete {s : Sig} (actual : Ctx s) :
    ∃ result, checkMorCore actual (.refl : CtxMor s) = some result ∧
      result.view = actual := by
  rw [checkMorCore.eq_1]
  simp

private theorem checkMorCore_function_complete {s : Sig} (context : Ctx s)
    (domain : LeCo s) (actual : Source.Ty s)
    (checked : LeChecked context domain)
    (equation : checkLeCore context domain = some checked)
    (sourceEq : checked.source = actual) :
    ∃ result,
      checkMorCore (context.extendTerm actual) (.function domain) = some result ∧
        result.view = context.extendTerm checked.target := by
  cases sourceEq
  unfold Ctx.extendTerm
  rw [checkMorCore.eq_2, equation]
  simp [Ctx.extendTerm]

private def checkTmCore {s : Sig} (context : Ctx s) (term : Tm s) :
    Option (TmChecked context term) :=
  match term with
  | .var path =>
      some ⟨(context.lookup path).termType, Tm.HasType.var path⟩
  | .lam domain body => do
      let bodyChecked ← checkTmCore (context.extendTerm domain) body
      pure ⟨.all domain bodyChecked.type, .lam bodyChecked.typing⟩
  | .obj label witness =>
      some ⟨.member label witness witness, .obj label witness⟩
  | .app function argument functionView argumentView => do
      let functionChecked ← checkLeCore context functionView
      let argumentChecked ← checkLeCore context argumentView
      if functionSource : functionChecked.source =
          (context.lookup function).termType then
        match functionTarget : functionChecked.target with
        | .all domain codomain =>
            if argumentSource : argumentChecked.source =
                (context.lookup argument).termType then
              if argumentTarget : argumentChecked.target = domain then
                let functionTyping : LeCo.HasType context functionView
                    (context.lookup function).termType (.all domain codomain) := by
                  simpa [← functionSource, ← functionTarget] using
                    functionChecked.typing
                let argumentTyping : LeCo.HasType context argumentView
                    (context.lookup argument).termType domain := by
                  simpa [← argumentSource, ← argumentTarget] using
                    argumentChecked.typing
                some ⟨codomain.open argument,
                  Tm.HasType.app functionTyping argumentTyping⟩
              else
                none
            else
              none
        | _ => none
      else
        none
  | .let' rhs body => do
      let rhsChecked ← checkTmCore context rhs
      let bodyChecked ← checkTmCore (context.extendTerm rhsChecked.type) body
      match nonescape : ScopedTy.strengthenTerm bodyChecked.type with
      | some result =>
          pure ⟨result,
            .let' rhsChecked.typing bodyChecked.typing nonescape⟩
      | none => none
  | .cast inner inclusion => do
      let termChecked ← checkTmCore context inner
      let inclusionChecked ← checkLeCore context inclusion
      if sameSource : termChecked.type = inclusionChecked.source then
        let inclusionTyping : LeCo.HasType context inclusion termChecked.type
            inclusionChecked.target := by
          simpa [sameSource] using inclusionChecked.typing
        pure ⟨inclusionChecked.target,
          .cast termChecked.typing inclusionTyping⟩
      else
        none
  | .letHandle exposure body => do
      let exposureChecked ← checkExposureCore context exposure
      let bodyChecked ←
        checkTmCore (context.extendMember exposureChecked.member) body
      pure ⟨ScopedTy.dropMember bodyChecked.type,
        .letHandle exposureChecked.typing bodyChecked.typing⟩
  | .letExact label witness body => do
      let bodyChecked ← checkTmCore (context.extendExact label witness) body
      match nonescape : ScopedTy.strengthenExact bodyChecked.type with
      | some result =>
          pure ⟨result, .letExact bodyChecked.typing nonescape⟩
      | none => none

/-! ## Public executable interface -/

/-! ### Intrinsic scope formation

These Boolean traversals are useful at a serialization/parser boundary.  For
values already inhabiting the indexed Lean datatypes they necessarily return
`true`; the accompanying soundness functions expose the exact scope-only
formation judgment. -/

/-- Check the recursive shape of an intrinsically scoped target type.
Selections are accepted as opaque `(path,label)` atoms. -/
def checkTyScope {s : Sig} : Source.Ty s → Bool
  | .top => true
  | .bot => true
  | .all domain codomain => checkTyScope domain && checkTyScope codomain
  | .member _ lower upper => checkTyScope lower && checkTyScope upper
  | .sel _ _ => true

/-- Check the scoped bounds stored by a reusable member fact. -/
def checkMemberScope {s : Sig} (member : MemberSpec s) : Bool :=
  checkTyScope member.lower && checkTyScope member.upper

/-- Check every type payload in one heterogeneous binding. -/
def checkBindingScope {s : Sig} {kind : BinderKind} : Binding s kind → Bool
  | .term type => checkTyScope type
  | .typeVar => true
  | .equality left right => checkTyScope left && checkTyScope right
  | .inclusion source target => checkTyScope source && checkTyScope target
  | .member member => checkMemberScope member

/-- Check every payload in a heterogeneous target telescope. -/
def checkContextScope {s : Sig} : Ctx s → Bool
  | .nil => true
  | .extend outer binding => checkContextScope outer && checkBindingScope binding

@[simp]
theorem checkTyScope_eq_true {s : Sig} (type : Source.Ty s) :
    checkTyScope type = true := by
  induction type with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [checkTyScope, domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp [checkTyScope, lowerInduction, upperInduction]
  | sel path label => rfl

@[simp]
theorem checkMemberScope_eq_true {s : Sig} (member : MemberSpec s) :
    checkMemberScope member = true := by
  simp [checkMemberScope]

@[simp]
theorem checkBindingScope_eq_true {s : Sig} {kind : BinderKind}
    (binding : Binding s kind) : checkBindingScope binding = true := by
  cases binding <;> simp [checkBindingScope, checkMemberScope]

@[simp]
theorem checkContextScope_eq_true {s : Sig} (context : Ctx s) :
    checkContextScope context = true := by
  induction context with
  | nil => rfl
  | extend outer binding induction =>
      simp [checkContextScope, induction]

def checkTyScope_sound {s : Sig} {type : Source.Ty s}
    (_checked : checkTyScope type = true) : Formation.TyScoped type :=
  Formation.TyScoped.total type

def checkMemberScope_sound {s : Sig} {member : MemberSpec s}
    (_checked : checkMemberScope member = true) : Formation.MemberScoped member :=
  Formation.MemberScoped.total member

def checkBindingScope_sound {s : Sig} {kind : BinderKind}
    {binding : Binding s kind} (_checked : checkBindingScope binding = true) :
    Formation.BindingScoped binding :=
  Formation.BindingScoped.total binding

def checkContextScope_sound {s : Sig} {context : Ctx s}
    (_checked : checkContextScope context = true) :
    Formation.ContextScoped context :=
  Formation.ContextScoped.total context

/-- Synthesize the structural endpoints of equality evidence.  Successful
synthesis does not assert declarative DOT well-formedness of those endpoints. -/
def synthEq {s : Sig} (context : Ctx s) (evidence : EqCo s) :
    Option (Endpoints s) :=
  (checkEqCore context evidence).map fun checked => (checked.source, checked.target)

/-- Synthesize the structural endpoints of directed inclusion evidence.
Selection annotations are opaque unless an explicit exposure binds a handle. -/
def synthLe {s : Sig} (context : Ctx s) (evidence : LeCo s) :
    Option (Endpoints s) :=
  (checkLeCore context evidence).map fun checked => (checked.source, checked.target)

/-- Synthesize the member fact produced by an explicitly checked exposure
recipe.  This is the only path from a term view to reusable lower/upper rules. -/
def synthExposure {s : Sig} (context : Ctx s) (exposure : Exposure s) :
    Option (MemberSpec s) :=
  (checkExposureCore context exposure).map ExposureChecked.member

/-- Starting from an actual context, synthesize the context produced by an
explicit context morphism. -/
def synthMor {s : Sig} (actual : Ctx s) (morphism : CtxMor s) : Option (Ctx s) :=
  (checkMorCore actual morphism).map MorChecked.view

/-- Check a context morphism against both expected endpoint contexts. -/
def checkMor {s : Sig} (actual view : Ctx s) (morphism : CtxMor s) : Bool :=
  match synthMor actual morphism with
  | some synthesized => decide (synthesized = view)
  | none => false

/-- Synthesize the unique type assigned by syntax-directed target typing.
Annotations receive intrinsic scope checking, not declarative source `Wf`. -/
def synthTm {s : Sig} (context : Ctx s) (term : Tm s) : Option (Source.Ty s) :=
  match term with
  | .var path => some (context.lookup path).termType
  | .lam domain body => do
      let codomain ← synthTm (context.extendTerm domain) body
      pure (.all domain codomain)
  | .obj label witness => some (.member label witness witness)
  | .app function argument functionView argumentView => do
      let functionEndpoints ← synthLe context functionView
      let argumentEndpoints ← synthLe context argumentView
      if functionEndpoints.1 = (context.lookup function).termType then
        match functionEndpoints.2 with
        | .all domain codomain =>
            if argumentEndpoints.1 = (context.lookup argument).termType then
              if argumentEndpoints.2 = domain then
                some (codomain.open argument)
              else
                none
            else
              none
        | _ => none
      else
        none
  | .let' rhs body => do
      let bound ← synthTm context rhs
      let bodyType ← synthTm (context.extendTerm bound) body
      ScopedTy.strengthenTerm bodyType
  | .cast inner inclusion => do
      let innerType ← synthTm context inner
      let endpoints ← synthLe context inclusion
      if innerType = endpoints.1 then some endpoints.2 else none
  | .letHandle exposure body => do
      let member ← synthExposure context exposure
      let bodyType ← synthTm (context.extendMember member) body
      pure (ScopedTy.dropMember bodyType)
  | .letExact label witness body => do
      let bodyType ← synthTm (context.extendExact label witness) body
      ScopedTy.strengthenExact bodyType

/-! ## Soundness -/

def synthEq_sound {s : Sig} {context : Ctx s} {evidence : EqCo s}
    {source target : Source.Ty s}
    (checked : synthEq context evidence = some (source, target)) :
    EqCo.HasType context evidence source target := by
  unfold synthEq at checked
  cases equation : checkEqCore context evidence with
  | none => simp [equation] at checked
  | some result =>
    simp [equation] at checked
    obtain ⟨rfl, rfl⟩ := checked
    exact result.typing

def synthLe_sound {s : Sig} {context : Ctx s} {evidence : LeCo s}
    {source target : Source.Ty s}
    (checked : synthLe context evidence = some (source, target)) :
    LeCo.HasType context evidence source target := by
  unfold synthLe at checked
  cases equation : checkLeCore context evidence with
  | none => simp [equation] at checked
  | some result =>
    simp [equation] at checked
    obtain ⟨rfl, rfl⟩ := checked
    exact result.typing

def synthExposure_sound {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (checked : synthExposure context exposure = some member) :
    Exposure.HasType context exposure member := by
  unfold synthExposure at checked
  cases equation : checkExposureCore context exposure with
  | none => simp [equation] at checked
  | some result =>
    simp [equation] at checked
    subst member
    exact result.typing

def synthMor_sound {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s}
    (checked : synthMor actual morphism = some view) :
    CtxMor.HasType actual view morphism := by
  unfold synthMor at checked
  cases equation : checkMorCore actual morphism with
  | none => simp [equation] at checked
  | some result =>
    simp [equation] at checked
    subst view
    exact result.typing

def checkMor_sound {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s} (checked : checkMor actual view morphism = true) :
    CtxMor.HasType actual view morphism := by
  unfold checkMor at checked
  cases equation : synthMor actual morphism with
  | none => simp [equation] at checked
  | some synthesized =>
    simp only [equation, decide_eq_true_eq] at checked
    subst view
    exact synthMor_sound equation

def synthTm_sound {s : Sig} {context : Ctx s} {term : Tm s}
    {type : Source.Ty s} (checked : synthTm context term = some type) :
    Tm.HasType context term type :=
  match term with
  | .var path => by
      simp [synthTm] at checked
      subst type
      exact .var path
  | .lam domain body => by
      cases bodyEquation : synthTm (context.extendTerm domain) body with
      | none => simp [synthTm, bodyEquation] at checked
      | some codomain =>
          simp [synthTm, bodyEquation] at checked
          subst type
          exact .lam (synthTm_sound bodyEquation)
  | .obj label witness => by
      simp [synthTm] at checked
      subst type
      exact .obj label witness
  | .app function argument functionView argumentView => by
      cases functionEquation : synthLe context functionView with
      | none => simp [synthTm, functionEquation] at checked
      | some functionEndpoints =>
          cases argumentEquation : synthLe context argumentView with
          | none => simp [synthTm, functionEquation, argumentEquation] at checked
          | some argumentEndpoints =>
              rcases functionEndpoints with ⟨functionSource, functionTarget⟩
              rcases argumentEndpoints with ⟨argumentSource, argumentTarget⟩
              by_cases functionSourceEq :
                  functionSource = (context.lookup function).termType
              · cases functionTargetEq : functionTarget with
                | top =>
                    simp [synthTm, functionEquation, argumentEquation,
                      functionSourceEq, functionTargetEq] at checked
                | bot =>
                    simp [synthTm, functionEquation, argumentEquation,
                      functionSourceEq, functionTargetEq] at checked
                | member label lower upper =>
                    simp [synthTm, functionEquation, argumentEquation,
                      functionSourceEq, functionTargetEq] at checked
                | sel path label =>
                    simp [synthTm, functionEquation, argumentEquation,
                      functionSourceEq, functionTargetEq] at checked
                | all domain codomain =>
                    by_cases argumentSourceEq :
                        argumentSource = (context.lookup argument).termType
                    · by_cases argumentTargetEq : argumentTarget = domain
                      · simp [synthTm, functionEquation, argumentEquation,
                          functionSourceEq, functionTargetEq, argumentSourceEq,
                          argumentTargetEq] at checked
                        subst type
                        have functionTyping : LeCo.HasType context functionView
                            (context.lookup function).termType
                            (.all domain codomain) := by
                          simpa [functionSourceEq, functionTargetEq] using
                            synthLe_sound functionEquation
                        have argumentTyping : LeCo.HasType context argumentView
                            (context.lookup argument).termType domain := by
                          simpa [argumentSourceEq, argumentTargetEq] using
                            synthLe_sound argumentEquation
                        exact .app functionTyping argumentTyping
                      · simp [synthTm, functionEquation, argumentEquation,
                          functionSourceEq, functionTargetEq, argumentSourceEq,
                          argumentTargetEq] at checked
                    · simp [synthTm, functionEquation, argumentEquation,
                        functionSourceEq, functionTargetEq, argumentSourceEq]
                        at checked
              · simp [synthTm, functionEquation, argumentEquation,
                  functionSourceEq] at checked
  | .let' rhs body => by
      cases rhsEquation : synthTm context rhs with
      | none => simp [synthTm, rhsEquation] at checked
      | some bound =>
          cases bodyEquation : synthTm (context.extendTerm bound) body with
          | none => simp [synthTm, rhsEquation, bodyEquation] at checked
          | some bodyType =>
              cases nonescape : ScopedTy.strengthenTerm bodyType with
              | none =>
                  simp [synthTm, rhsEquation, bodyEquation, nonescape] at checked
              | some result =>
                  simp [synthTm, rhsEquation, bodyEquation, nonescape] at checked
                  subst type
                  exact .let' (synthTm_sound rhsEquation)
                    (synthTm_sound bodyEquation) nonescape
  | .cast inner inclusion => by
      cases termEquation : synthTm context inner with
      | none => simp [synthTm, termEquation] at checked
      | some source =>
          cases inclusionEquation : synthLe context inclusion with
          | none => simp [synthTm, termEquation, inclusionEquation] at checked
          | some endpoints =>
              by_cases sourceEquation : source = endpoints.1
              · simp [synthTm, termEquation, inclusionEquation,
                    sourceEquation] at checked
                subst type
                let inclusionTyping : LeCo.HasType context inclusion source
                    endpoints.2 := by
                  simpa [sourceEquation] using synthLe_sound inclusionEquation
                exact .cast (synthTm_sound termEquation)
                  inclusionTyping
              · simp [synthTm, termEquation, inclusionEquation,
                    sourceEquation] at checked
  | .letHandle exposure body => by
      cases exposureEquation : synthExposure context exposure with
      | none => simp [synthTm, exposureEquation] at checked
      | some member =>
          cases bodyEquation : synthTm (context.extendMember member) body with
          | none => simp [synthTm, exposureEquation, bodyEquation] at checked
          | some bodyType =>
              simp [synthTm, exposureEquation, bodyEquation] at checked
              subst type
              exact .letHandle (synthExposure_sound exposureEquation)
                (synthTm_sound bodyEquation)
  | .letExact label witness body => by
      cases bodyEquation : synthTm (context.extendExact label witness) body with
      | none => simp [synthTm, bodyEquation] at checked
      | some bodyType =>
          cases nonescape : ScopedTy.strengthenExact bodyType with
          | none => simp [synthTm, bodyEquation, nonescape] at checked
          | some result =>
              simp [synthTm, bodyEquation, nonescape] at checked
              subst type
              exact .letExact (synthTm_sound bodyEquation) nonescape

/-! ## Exact formation corollaries

The following functions intentionally conclude only intrinsic scope
formation.  Stronger `Source.Wf` provenance is supplied by source elaboration,
not reconstructed or searched for by this checker. -/

def synthEq_scope_sound {s : Sig} {context : Ctx s} {evidence : EqCo s}
    {source target : Source.Ty s}
    (_checked : synthEq context evidence = some (source, target)) :
    Formation.TyScoped source × Formation.TyScoped target :=
  ⟨Formation.TyScoped.total source, Formation.TyScoped.total target⟩

def synthLe_scope_sound {s : Sig} {context : Ctx s} {evidence : LeCo s}
    {source target : Source.Ty s}
    (_checked : synthLe context evidence = some (source, target)) :
    Formation.TyScoped source × Formation.TyScoped target :=
  ⟨Formation.TyScoped.total source, Formation.TyScoped.total target⟩

def synthExposure_scope_sound {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (_checked : synthExposure context exposure = some member) :
    Formation.MemberScoped member :=
  Formation.MemberScoped.total member

def synthMor_scope_sound {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s}
    (_checked : synthMor actual morphism = some view) :
    Formation.ContextScoped view :=
  Formation.ContextScoped.total view

def synthTm_scope_sound {s : Sig} {context : Ctx s} {term : Tm s}
    {type : Source.Ty s} (_checked : synthTm context term = some type) :
    Formation.TyScoped type :=
  Formation.TyScoped.total type

/-! ## Completeness -/

private theorem checkEqCore_complete {s : Sig} {context : Ctx s}
    {evidence : EqCo s} {source target : Source.Ty s}
    (typing : EqCo.HasType context evidence source target) :
    ∃ result, checkEqCore context evidence = some result ∧
      result.source = source ∧ result.target = target := by
  induction typing with
  | var index =>
      simp [checkEqCore]
  | refl type =>
      simp [checkEqCore]
  | symm typing induction =>
      obtain ⟨result, equation, sourceEq, targetEq⟩ := induction
      simp [checkEqCore, equation, sourceEq, targetEq]
  | trans firstTyping secondTyping firstInduction secondInduction =>
      obtain ⟨first, firstEquation, firstSource, firstTarget⟩ := firstInduction
      obtain ⟨second, secondEquation, secondSource, secondTarget⟩ := secondInduction
      simp [checkEqCore, firstEquation, secondEquation, firstSource,
        firstTarget, secondSource, secondTarget]

theorem synthEq_complete {s : Sig} {context : Ctx s} {evidence : EqCo s}
    {source target : Source.Ty s}
    (typing : EqCo.HasType context evidence source target) :
    synthEq context evidence = some (source, target) := by
  obtain ⟨result, equation, sourceEq, targetEq⟩ :=
    checkEqCore_complete typing
  unfold synthEq
  rw [equation]
  simp [sourceEq, targetEq]

mutual

private theorem checkLeCore_complete {s : Sig} {context : Ctx s}
    {evidence : LeCo s} {source target : Source.Ty s}
    (typing : LeCo.HasType context evidence source target) :
    ∃ result, checkLeCore context evidence = some result ∧
      result.source = source ∧ result.target = target :=
  match typing with
  | .var index => by
      simp [checkLeCore]
  | .refl type => by
      simp [checkLeCore]
  | .trans firstTyping secondTyping => by
      obtain ⟨first, firstEquation, firstSource, firstTarget⟩ :=
        checkLeCore_complete firstTyping
      obtain ⟨second, secondEquation, secondSource, secondTarget⟩ :=
        checkLeCore_complete secondTyping
      simp [checkLeCore, firstEquation, secondEquation, firstSource,
        firstTarget, secondSource, secondTarget]
  | .top source => by
      simp [checkLeCore]
  | .bot target => by
      simp [checkLeCore]
  | .eqToLe equalityTyping => by
      obtain ⟨equality, equation, sourceEq, targetEq⟩ :=
        checkEqCore_complete equalityTyping
      simp [checkLeCore, equation, sourceEq, targetEq]
  | .member lowerTyping upperTyping => by
      obtain ⟨lower, lowerEquation, lowerSource, lowerTarget⟩ :=
        checkLeCore_complete lowerTyping
      obtain ⟨upper, upperEquation, upperSource, upperTarget⟩ :=
        checkLeCore_complete upperTyping
      simp [checkLeCore, lowerEquation, upperEquation, lowerSource,
        lowerTarget, upperSource, upperTarget]
  | .all domainTyping viewTyping codomainTyping => by
      obtain ⟨domain, domainEquation, domainSource, domainTarget⟩ :=
        checkLeCore_complete domainTyping
      obtain ⟨view, viewEquation, viewTarget⟩ :=
        checkMorCore_complete viewTyping
      obtain ⟨codomain, codomainEquation, codomainSource, codomainTarget⟩ :=
        checkLeCore_complete codomainTyping
      cases domainSource
      cases domainTarget
      cases codomainSource
      cases codomainTarget
      simp [checkLeCore, domainEquation, viewEquation, viewTarget,
        codomainEquation]
  | .lower => by
      simp [checkLeCore]
  | .upper => by
      simp [checkLeCore]
  | .letHandle exposureTyping bodyTyping => by
      obtain ⟨exposure, exposureEquation, exposureMember⟩ :=
        checkExposureCore_complete exposureTyping
      obtain ⟨body, bodyEquation, bodySource, bodyTarget⟩ :=
        checkLeCore_complete bodyTyping
      cases exposureMember
      cases bodySource
      cases bodyTarget
      simp [checkLeCore, exposureEquation, bodyEquation]

private theorem checkExposureCore_complete {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (typing : Exposure.HasType context exposure member) :
    ∃ result, checkExposureCore context exposure = some result ∧
      result.member = member :=
  match typing with
  | .view inclusionTyping => by
      obtain ⟨inclusion, equation, sourceEq, targetEq⟩ :=
        checkLeCore_complete inclusionTyping
      simp [checkExposureCore, equation, sourceEq, targetEq]

private theorem checkMorCore_complete {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s}
    (typing : CtxMor.HasType actual view morphism) :
    ∃ result, checkMorCore actual morphism = some result ∧ result.view = view :=
  match typing with
  | .refl => by
      exact checkMorCore_refl_complete _
  | .function domainTyping => by
      obtain ⟨domain, equation, sourceEq, targetEq⟩ :=
        checkLeCore_complete domainTyping
      cases sourceEq
      cases targetEq
      exact checkMorCore_function_complete _ _ _ domain equation rfl

end

theorem synthLe_complete {s : Sig} {context : Ctx s} {evidence : LeCo s}
    {source target : Source.Ty s}
    (typing : LeCo.HasType context evidence source target) :
    synthLe context evidence = some (source, target) := by
  obtain ⟨result, equation, sourceEq, targetEq⟩ :=
    checkLeCore_complete typing
  unfold synthLe
  rw [equation]
  simp [sourceEq, targetEq]

theorem synthExposure_complete {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (typing : Exposure.HasType context exposure member) :
    synthExposure context exposure = some member := by
  obtain ⟨result, equation, memberEq⟩ :=
    checkExposureCore_complete typing
  unfold synthExposure
  rw [equation]
  simp [memberEq]

theorem synthMor_complete {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s} (typing : CtxMor.HasType actual view morphism) :
    synthMor actual morphism = some view := by
  obtain ⟨result, equation, viewEq⟩ := checkMorCore_complete typing
  unfold synthMor
  rw [equation]
  simp [viewEq]

theorem checkMor_complete {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s} (typing : CtxMor.HasType actual view morphism) :
    checkMor actual view morphism = true := by
  unfold checkMor
  rw [synthMor_complete typing]
  simp

theorem synthTm_complete {s : Sig} {context : Ctx s} {term : Tm s}
    {type : Source.Ty s} (typing : Tm.HasType context term type) :
    synthTm context term = some type := by
  induction typing with
  | var path =>
      simp [synthTm]
  | lam bodyTyping induction =>
      simp [synthTm, induction]
  | obj label witness =>
      simp [synthTm]
  | app functionTyping argumentTyping =>
      simp [synthTm, synthLe_complete functionTyping,
        synthLe_complete argumentTyping]
  | let' rhsTyping bodyTyping nonescape rhsInduction bodyInduction =>
      simp [synthTm, rhsInduction, bodyInduction, nonescape]
  | cast termTyping inclusionTyping termInduction =>
      simp [synthTm, termInduction, synthLe_complete inclusionTyping]
  | letHandle exposureTyping bodyTyping bodyInduction =>
      simp [synthTm, synthExposure_complete exposureTyping, bodyInduction]
  | letExact bodyTyping nonescape bodyInduction =>
      simp [synthTm, bodyInduction, nonescape]

end DotFC.Explicit
