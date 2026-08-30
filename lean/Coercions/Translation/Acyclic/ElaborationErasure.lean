import Coercions.Translation.Acyclic.Elaboration
import Coercions.FCsub.Erasure

/-!
# Erasure of DOT-to-FCsub elaboration

The source and target use different heterogeneous signatures: one source
member binder expands to a generic FCsub telescope with one abstract name,
two constraints, and a separate runtime payload.  `sourceRuntime` embeds a
source typing derivation directly in that target layout while deleting the
three static telescope entries.
-/

namespace DotToFCsub.Elaboration

open FCsub

/-- Lifting static erasure beneath the payload term binder is exactly payload
erasure for the client-level member telescope. -/
theorem dropStatic_lift_eq_dropPayload {scope : FCsub.Sig} :
    (FCsub.Runtime.Subst.dropStatic (scope := scope)
      MemberEncoding.names MemberEncoding.constraints).lift =
    FCsub.Runtime.Subst.dropPayload
      MemberEncoding.names MemberEncoding.constraints := by
  apply FCsub.Runtime.Subst.ext
  intro index
  cases index <;> rfl

/-- Source runtime erasure embedded in the standalone FCsub layout selected by
a typing derivation.  Member binders retain only their ordinary payload term
binder, source objects become runtime unit, and subsumption is erased. -/
def sourceRuntime {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) :
    FCsub.Runtime.Tm (TargetSig context) :=
  match derivation with
  | .var (path := path) _ =>
      .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path)
  | .lam (domain := domain) _ bodyTyping =>
      match domain with
      | .member _ _ _ =>
          .lam ((sourceRuntime bodyTyping).subst
            (FCsub.Runtime.Subst.dropPayload
              MemberEncoding.names MemberEncoding.constraints))
      | .top => .lam (sourceRuntime bodyTyping)
      | .bot => .lam (sourceRuntime bodyTyping)
      | .all _ _ => .lam (sourceRuntime bodyTyping)
      | .sel _ _ => .lam (sourceRuntime bodyTyping)
  | .obj _ => .unit
  | .app (argument := argument) functionTyping _ _ =>
      .app (sourceRuntime functionTyping)
        (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) argument))
  | .let' (bound := bound) rhsTyping bodyTyping _ =>
      match bound with
      | .member _ _ _ =>
          .let' (sourceRuntime rhsTyping)
            ((sourceRuntime bodyTyping).subst
              (FCsub.Runtime.Subst.dropPayload
                MemberEncoding.names MemberEncoding.constraints))
      | .top => .let' (sourceRuntime rhsTyping) (sourceRuntime bodyTyping)
      | .bot => .let' (sourceRuntime rhsTyping) (sourceRuntime bodyTyping)
      | .all _ _ => .let' (sourceRuntime rhsTyping) (sourceRuntime bodyTyping)
      | .sel _ _ => .let' (sourceRuntime rhsTyping) (sourceRuntime bodyTyping)
  | .sub termTyping _ _ => sourceRuntime termTyping

/-- Every source derivation of a variable has the same runtime image,
independently of surrounding source subsumption nodes. -/
theorem sourceRuntime_variable {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context (.var path) type) :
    sourceRuntime derivation =
      .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path) :=
  match derivation with
  | .var _ => rfl
  | .sub termTyping _ _ => sourceRuntime_variable termTyping

/-- Successful bridge compilation inserts only static FCsub syntax and
administrative packaging.  Its standalone FCsub erasure is exactly the source
runtime embedded in the generated target layout. -/
theorem term_erasure {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {sourceTerm : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context sourceTerm type)
    {target : FCsub.Tm (TargetSig context)}
    (compiled : term? derivation = some target) :
    target.erase = sourceRuntime derivation := by
  induction derivation with
  | @var source context path declared binding =>
      cases declared with
      | top =>
          simp only [term?] at compiled
          simp at compiled
          rw [← compiled]
          rfl
      | bot =>
          simp only [term?] at compiled
          simp at compiled
          rw [← compiled]
          rfl
      | all domain codomain =>
          simp only [term?] at compiled
          simp at compiled
          rw [← compiled]
          rfl
      | sel path label =>
          simp only [term?] at compiled
          simp at compiled
          rw [← compiled]
          rfl
      | member label lower upper =>
          simp only [term?] at compiled
          obtain ⟨lowerTarget, lowerCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨upperTarget, upperCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨slot, lookup, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [MemberEncoding.pack, FCsub.Tm.erase, sourceRuntime]
          exact congrArg FCsub.Runtime.Tm.var
            (Layout.fullSlot_payload lookup)
  | @lam source context domain body codomain domainWf bodyTyping induction =>
      cases domain with
      | top =>
          simp only [term?] at compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          exact congrArg FCsub.Runtime.Tm.lam (induction bodyCompiled)
      | bot =>
          simp only [term?] at compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          exact congrArg FCsub.Runtime.Tm.lam (induction bodyCompiled)
      | all nested result =>
          simp only [term?] at compiled
          obtain ⟨domainTarget, domainCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          exact congrArg FCsub.Runtime.Tm.lam (induction bodyCompiled)
      | sel path label =>
          simp only [term?] at compiled
          obtain ⟨domainTarget, domainCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          exact congrArg FCsub.Runtime.Tm.lam (induction bodyCompiled)
      | member label lower upper =>
          simp only [term?] at compiled
          obtain ⟨lowerTarget, lowerCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨upperTarget, upperCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [MemberEncoding.lam, FCsub.Tm.erase,
            FCsub.Runtime.Tm.subst, sourceRuntime]
          rw [dropStatic_lift_eq_dropPayload]
          exact congrArg FCsub.Runtime.Tm.lam
            (congrArg
              (fun runtime => runtime.subst
                (FCsub.Runtime.Subst.dropPayload MemberEncoding.names
                  MemberEncoding.constraints))
              (induction bodyCompiled))
  | @obj source context label witness witnessWf =>
      simp only [term?] at compiled
      obtain ⟨witnessTarget, witnessCompiled, compiled⟩ :=
        Option.bind_eq_some_iff.mp compiled
      simp at compiled
      rw [← compiled]
      rfl
  | @app source context function argument domain codomain functionTyping
      argumentTyping resultWf functionInduction argumentInduction =>
      cases domain with
      | top =>
          simp only [term?] at compiled
          obtain ⟨functionTarget, functionCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨argumentTarget, argumentCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [functionInduction functionCompiled,
            argumentInduction argumentCompiled,
            sourceRuntime_variable argumentTyping]
      | bot =>
          simp only [term?] at compiled
          obtain ⟨functionTarget, functionCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨argumentTarget, argumentCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [functionInduction functionCompiled,
            argumentInduction argumentCompiled,
            sourceRuntime_variable argumentTyping]
      | all nested result =>
          simp only [term?] at compiled
          obtain ⟨functionTarget, functionCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨argumentTarget, argumentCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [functionInduction functionCompiled,
            argumentInduction argumentCompiled,
            sourceRuntime_variable argumentTyping]
      | sel path label =>
          simp only [term?] at compiled
          obtain ⟨functionTarget, functionCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨argumentTarget, argumentCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [functionInduction functionCompiled,
            argumentInduction argumentCompiled,
            sourceRuntime_variable argumentTyping]
      | member label lower upper =>
          simp only [term?] at compiled
          obtain ⟨functionTarget, functionCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨lowerTarget, lowerCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨upperTarget, upperCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨use, useCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [MemberEncoding.app, FCsub.Tm.erase, sourceRuntime]
          rw [functionInduction functionCompiled]
  | @let' source context rhs body bound result rhsTyping bodyTyping resultWf
      rhsInduction bodyInduction =>
      cases bound with
      | top =>
          simp only [term?] at compiled
          obtain ⟨rhsTarget, rhsCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [rhsInduction rhsCompiled]
          exact congrArg
            (FCsub.Runtime.Tm.let' (sourceRuntime rhsTyping))
            (bodyInduction bodyCompiled)
      | bot =>
          simp only [term?] at compiled
          obtain ⟨rhsTarget, rhsCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [rhsInduction rhsCompiled]
          exact congrArg
            (FCsub.Runtime.Tm.let' (sourceRuntime rhsTyping))
            (bodyInduction bodyCompiled)
      | all domain codomain =>
          simp only [term?] at compiled
          obtain ⟨rhsTarget, rhsCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [rhsInduction rhsCompiled]
          exact congrArg
            (FCsub.Runtime.Tm.let' (sourceRuntime rhsTyping))
            (bodyInduction bodyCompiled)
      | sel path label =>
          simp only [term?] at compiled
          obtain ⟨rhsTarget, rhsCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [FCsub.Tm.erase, sourceRuntime]
          rw [rhsInduction rhsCompiled]
          exact congrArg
            (FCsub.Runtime.Tm.let' (sourceRuntime rhsTyping))
            (bodyInduction bodyCompiled)
      | member label lower upper =>
          simp only [term?] at compiled
          obtain ⟨lowerTarget, lowerCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨upperTarget, upperCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨rhsTarget, rhsCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          obtain ⟨bodyTarget, bodyCompiled, compiled⟩ :=
            Option.bind_eq_some_iff.mp compiled
          simp at compiled
          rw [← compiled]
          simp only [MemberEncoding.open, FCsub.Tm.erase, sourceRuntime]
          rw [rhsInduction rhsCompiled]
          exact congrArg
            (FCsub.Runtime.Tm.let' (sourceRuntime rhsTyping))
            (congrArg
              (fun runtime => runtime.subst
                (FCsub.Runtime.Subst.dropPayload MemberEncoding.names
                  MemberEncoding.constraints))
              (bodyInduction bodyCompiled))
  | @sub source context sourceTerm sourceType targetType termTyping subtyping
      targetWf induction =>
      simp only [term?] at compiled
      obtain ⟨termTarget, termCompiled, compiled⟩ :=
        Option.bind_eq_some_iff.mp compiled
      obtain ⟨evidenceTarget, evidenceCompiled, compiled⟩ :=
        Option.bind_eq_some_iff.mp compiled
      simp at compiled
      rw [← compiled]
      simp only [FCsub.Tm.erase, sourceRuntime]
      exact induction termCompiled

/-- Checked readiness packages the deterministic elaborated term together with
the DOT-to-FCsub commuting erasure equation. -/
theorem BReady.erasure {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {sourceTerm : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context sourceTerm type}
    (ready : BReady derivation) :
    ∃ target : FCsub.Tm (TargetSig context),
      TermTranslates derivation target ∧
      target.erase = sourceRuntime derivation := by
  obtain ⟨_, _, target, _, _, compiled, _⟩ := ready
  exact ⟨target, compiled, term_erasure derivation compiled⟩

/-- The complete checked bridge package combines context/type translation,
standalone FCsub typing, and exact commuting erasure. -/
theorem BReady.sound {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {sourceTerm : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context sourceTerm type}
    (ready : BReady derivation) :
    ∃ (targetContext : FCsub.Ctx (TargetSig context))
        (type' : FCsub.Ty (TargetSig context))
        (target : FCsub.Tm (TargetSig context)),
      SourceContext.Translates context targetContext ∧
      Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type type' ∧
      TermTranslates derivation target ∧
      Nonempty (FCsub.Tm.HasType targetContext target type') ∧
      target.erase = sourceRuntime derivation := by
  obtain ⟨targetContext, type', target, contextTranslation, typeTranslation,
    compiled, checked⟩ := ready
  exact ⟨targetContext, type', target, contextTranslation, typeTranslation,
    compiled, FCsub.synthTm_sound checked,
    term_erasure derivation compiled⟩

end DotToFCsub.Elaboration
