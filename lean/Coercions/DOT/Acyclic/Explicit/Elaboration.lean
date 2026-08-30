import Coercions.DOT.Acyclic.Source.Structural
import Coercions.DOT.Acyclic.Explicit.SourceContext
import Coercions.DOT.Acyclic.Explicit.Structural
import Coercions.DOT.Acyclic.Explicit.Erasure

/-!
# Derivation-directed Stage A elaboration

The functions in this file consume source certificates; they perform no DOT
subtyping or member-exposure search.  Every source transitivity node becomes
`LeCo.trans`, and every selection rule binds one reusable structural exposure
before referring to its lower or upper endpoint.
-/

namespace DotFC.Explicit.Elaboration

open DotFC

mutual

/-- Compile a declarative source subtyping derivation to directed evidence. -/
def sub {s : Sig} {context : Source.Ctx s} {source target : Source.Ty s}
    (derivation : Source.Sub context source target) : LeCo s :=
  match derivation with
  | .refl _ => .refl source
  | .trans first second => .trans (sub first) (sub second)
  | .bot _ => .bot target
  | .top _ => .top source
  | .member (label := label) lower upper =>
      .member label (sub lower) (sub upper)
  | .lower exposure => .letHandle (handle exposure) (.lower .here)
  | .upper exposure => .letHandle (handle exposure) (.upper .here)
  | .all domain _ codomain _ _ =>
      let domainEvidence := sub domain
      .all domainEvidence (.function domainEvidence) (sub codomain)
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.Sub.rank]
  all_goals omega

/-- Compile a reusable source exposure to a structural target recipe. -/
def handle {s : Sig} {context : Source.Ctx s} {path : BVar s .term}
    {label : Source.Name} {lower upper : Source.Ty s}
    (exposure : Source.Handle context path label lower upper) : Exposure s :=
  match exposure with
  | .direct _ =>
      .view path label lower upper (.refl (.member label lower upper))
  | .expose _ view => .view path label lower upper (sub view)
  | .adjust adjustment binding =>
      .view path label lower upper (adjusted adjustment binding)
termination_by exposure.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.Handle.rank]
  all_goals omega

/-- Compile the pointwise action of a source context adjustment on one
lookup.  This is the certificate-producing counterpart of
`Source.CtxMor.lookupTransport`: it follows the supplied morphism and never
searches for a subtype path. -/
def adjusted {s : Sig} {actual view : Source.Ctx s}
    (adjustment : Source.CtxMor actual view)
    {path : BVar s .term} {viewType : Source.Ty s}
    (binding : Source.Lookup view path viewType) : LeCo s :=
  match adjustment, binding with
  | .id, _ => .refl viewType
  | .snoc _ head, .here => (sub head).weaken
  | .snoc tail _, .there older => (adjusted tail older).weaken
termination_by adjustment.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.CtxMor.rank]
  all_goals omega

end

/-! ## Certificate preservation -/

mutual

/-- Compiled source subtyping is well typed at exactly the source endpoints. -/
def subTyping {s : Sig} {context : Source.Ctx s}
    {source target : Source.Ty s}
    (derivation : Source.Sub context source target) :
    LeCo.HasType (Ctx.ofSource context) (sub derivation) source target :=
  match derivation with
  | .refl _ => by
      simpa [sub] using
        (LeCo.HasType.refl (context := Ctx.ofSource context) source)
  | .trans first second => by
      simpa [sub] using LeCo.HasType.trans (subTyping first) (subTyping second)
  | .bot _ => by
      simpa [sub] using
        (LeCo.HasType.bot (context := Ctx.ofSource context) target)
  | .top _ => by
      simpa [sub] using
        (LeCo.HasType.top (context := Ctx.ofSource context) source)
  | .member (label := label) lower upper => by
      simpa [sub] using
        (LeCo.HasType.member (label := label)
          (subTyping lower) (subTyping upper))
  | .lower (path := path) (label := label) (lower := lower) (upper := upper)
      exposure => by
      let member : MemberSpec s := ⟨path, label, lower, upper⟩
      have compiledExposure :
          Exposure.HasType (Ctx.ofSource context) (handle exposure) member :=
        handleTyping exposure
      have boundTyping :=
        (LeCo.HasType.lower
          (context := (Ctx.ofSource context).extendMember member)
          (handle := (.here : BVar (s ▹ .member) .member)))
      have lowerDrop :
          ScopedTy.dropMember (lower.rename (Rename.succ (k := .member))) =
            lower := by
        exact ScopedTy.dropMember_weaken lower
      have selectionDrop :
          ScopedTy.dropMember
            (.sel (.there path : BVar (s ▹ .member) .term) label) =
            .sel path label := rfl
      simpa [sub, member, Binding.weaken, Binding.rename, Binding.memberSpec,
        MemberSpec.weaken, MemberSpec.rename, lowerDrop, selectionDrop] using
        LeCo.HasType.letHandle compiledExposure boundTyping
  | .upper (path := path) (label := label) (lower := lower) (upper := upper)
      exposure => by
      let member : MemberSpec s := ⟨path, label, lower, upper⟩
      have compiledExposure :
          Exposure.HasType (Ctx.ofSource context) (handle exposure) member :=
        handleTyping exposure
      have boundTyping :=
        (LeCo.HasType.upper
          (context := (Ctx.ofSource context).extendMember member)
          (handle := (.here : BVar (s ▹ .member) .member)))
      have upperDrop :
          ScopedTy.dropMember (upper.rename (Rename.succ (k := .member))) =
            upper := by
        exact ScopedTy.dropMember_weaken upper
      have selectionDrop :
          ScopedTy.dropMember
            (.sel (.there path : BVar (s ▹ .member) .term) label) =
            .sel path label := rfl
      simpa [sub, member, Binding.weaken, Binding.rename, Binding.memberSpec,
        MemberSpec.weaken, MemberSpec.rename, upperDrop, selectionDrop] using
        LeCo.HasType.letHandle compiledExposure boundTyping
  | .all domain _ codomain _ _ => by
      have domainTyping := subTyping domain
      have viewTyping := CtxMor.HasType.function domainTyping
      have codomainTyping := subTyping codomain
      simpa [sub] using
        LeCo.HasType.all domainTyping viewTyping codomainTyping
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.Sub.rank]
  all_goals omega

/-- Compiling a source handle produces the reusable member fact it claims. -/
def handleTyping {s : Sig} {context : Source.Ctx s}
    {path : BVar s .term} {label : Source.Name}
    {lower upper : Source.Ty s}
    (exposure : Source.Handle context path label lower upper) :
    Exposure.HasType (Ctx.ofSource context) (handle exposure)
      ⟨path, label, lower, upper⟩ :=
  match exposure with
  | .direct binding => by
      have inclusionTyping : LeCo.HasType (Ctx.ofSource context)
          (.refl (.member label lower upper))
          ((Ctx.ofSource context).lookup path).termType
          (.member label lower upper) := by
        rw [Ctx.lookup_ofSource binding]
        exact .refl _
      simpa [handle] using Exposure.HasType.view inclusionTyping
  | .expose binding view => by
      have inclusionTyping : LeCo.HasType (Ctx.ofSource context) (sub view)
          ((Ctx.ofSource context).lookup path).termType
          (.member label lower upper) := by
        rw [Ctx.lookup_ofSource binding]
        exact subTyping view
      simpa [handle] using Exposure.HasType.view inclusionTyping
  | .adjust adjustment binding => by
      let ⟨actualType, actualBinding, inclusionTyping⟩ :=
        adjustedTyping adjustment binding
      have endpointTyping : LeCo.HasType (Ctx.ofSource context)
          (adjusted adjustment binding)
          ((Ctx.ofSource context).lookup path).termType
          (.member label lower upper) := by
        rw [Ctx.lookup_ofSource actualBinding]
        exact inclusionTyping
      simpa [handle] using Exposure.HasType.view endpointTyping
termination_by exposure.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.Handle.rank]
  all_goals omega

/-- Pointwise compilation of a source context adjustment returns the actual
declaration, its lookup proof, and a checked explicit coercion to the viewed
declaration. -/
def adjustedTyping {s : Sig} {actual view : Source.Ctx s}
    (adjustment : Source.CtxMor actual view)
    {path : BVar s .term} {viewType : Source.Ty s}
    (binding : Source.Lookup view path viewType) :
    Σ actualType : Source.Ty s,
      Source.Lookup actual path actualType ×
        LeCo.HasType (Ctx.ofSource actual) (adjusted adjustment binding)
          actualType viewType :=
  match adjustment, binding with
  | .id, binding => by
      exact ⟨viewType, binding, by
        simpa [adjusted] using
          (LeCo.HasType.refl (context := Ctx.ofSource actual) viewType)⟩
  | @Source.CtxMor.snoc base actualBase viewBase actualType viewedType tail head,
      .here => by
      have typing := (subTyping head).weakenTerm actualType
      exact ⟨actualType.weaken, .here, by
        simpa [adjusted] using typing⟩
  | @Source.CtxMor.snoc base actualBase viewBase actualType viewedType tail head,
      .there older => by
      let ⟨found, foundBinding, foundTyping⟩ := adjustedTyping tail older
      have typing := foundTyping.weakenTerm actualType
      exact ⟨found.weaken, .there foundBinding, by
        simpa [adjusted] using typing⟩
termination_by adjustment.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Source.CtxMor.rank]
  all_goals omega

end

/-- Extract the explicit view coercion from a typing derivation of a stable
variable.  The only possible source rules are direct lookup and repeated
subsumption. -/
def variableView {s : Sig} {context : Source.Ctx s}
    {path : BVar s .term} {type : Source.Ty s}
    (derivation : Source.HasTy context (.var path) type) : LeCo s :=
  match derivation with
  | .var (type := declared) _ => .refl declared
  | .sub inner inclusion _ => .trans (variableView inner) (sub inclusion)

/-- A compiled variable view starts at the variable's actual declaration in
the translated context and ends at the type assigned by source typing. -/
def variableViewTyping {s : Sig} {context : Source.Ctx s}
    {path : BVar s .term} {type : Source.Ty s}
    (derivation : Source.HasTy context (.var path) type) :
    LeCo.HasType (Ctx.ofSource context) (variableView derivation)
      ((Ctx.ofSource context).lookup path).termType type :=
  match derivation with
  | .var binding => by
      rw [Ctx.lookup_ofSource binding]
      simpa [variableView] using
        (LeCo.HasType.refl (context := Ctx.ofSource context) type)
  | .sub inner inclusion _ => by
      simpa [variableView] using
        LeCo.HasType.trans (variableViewTyping inner) (subTyping inclusion)

/-- Compile source term typing.  Source subsumption becomes `cast`; the two
possibly subsumed variable premises of an ANF application become its explicit
function and argument view coercions. -/
def term {s : Sig} {context : Source.Ctx s} {sourceTerm : Source.Tm s}
    {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type) : Tm s :=
  match derivation with
  | .var (path := path) _ => .var path
  | .lam (domain := domain) _ bodyTyping => .lam domain (term bodyTyping)
  | .obj (label := label) (witness := witness) _ => .obj label witness
  | .app (function := function) (argument := argument)
      functionTyping argumentTyping _ =>
      .app function argument (variableView functionTyping)
        (variableView argumentTyping)
  | .let' rhsTyping bodyTyping _ => .let' (term rhsTyping) (term bodyTyping)
  | .sub termTyping inclusion _ => .cast (term termTyping) (sub inclusion)

/-- Derivation-directed term compilation preserves the assigned type exactly;
all source subsumption is represented by explicit target evidence. -/
def termTyping {s : Sig} {context : Source.Ctx s}
    {sourceTerm : Source.Tm s} {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type) :
    Tm.HasType (Ctx.ofSource context) (term derivation) type :=
  match derivation with
  | .var (path := path) binding => by
      simpa [term, Ctx.lookup_ofSource binding] using
        (Tm.HasType.var (context := Ctx.ofSource context) path)
  | .lam _ bodyTyping => by
      simpa [term] using Tm.HasType.lam (termTyping bodyTyping)
  | .obj (label := label) (witness := witness) _ => by
      simpa [term] using
        (Tm.HasType.obj (context := Ctx.ofSource context) label witness)
  | .app functionTyping argumentTyping _ => by
      simpa [term] using
        Tm.HasType.app (variableViewTyping functionTyping)
          (variableViewTyping argumentTyping)
  | .let' rhsTyping bodyTyping _ => by
      simpa [term, ScopedTy.strengthenTerm_weaken] using
        Tm.HasType.let' (termTyping rhsTyping) (termTyping bodyTyping)
          (ScopedTy.strengthenTerm_weaken _)
  | .sub innerTyping inclusion _ => by
      simpa [term] using
        Tm.HasType.cast (termTyping innerTyping) (subTyping inclusion)

/-! ## Stronger source-formation provenance

The independent target checker intentionally concludes only
`Formation.TyScoped`.  A certificate-producing source front end has stronger
information: in a valid source context its derivations also supply the
declarative source well-formedness proofs below.  These proofs are retained as
compiler provenance and are not re-discovered by the target checker. -/

/-- Both endpoints of compiled source subtyping are source-well-formed when
the source context is valid. -/
noncomputable def subEndpointWf {s : Sig} {context : Source.Ctx s}
    (contextValid : context.Valid) {source target : Source.Ty s}
    (derivation : Source.Sub context source target) :
    Source.Wf context source × Source.Wf context target :=
  ⟨Source.Sub.sourceWf contextValid derivation,
    Source.Sub.targetWf contextValid derivation⟩

/-- A source handle itself forms the selected type it exposes. -/
noncomputable def handleSelectionWf {s : Sig} {context : Source.Ctx s}
    {path : BVar s .term} {label : Source.Name}
    {lower upper : Source.Ty s}
    (exposure : Source.Handle context path label lower upper) :
    Source.Wf context (.sel path label) :=
  .sel exposure

/-- In a valid source context, a handle also supplies formation of the member
declaration exported by its compiled exposure recipe. -/
noncomputable def handleMemberWf {s : Sig} {context : Source.Ctx s}
    (contextValid : context.Valid) {path : BVar s .term}
    {label : Source.Name} {lower upper : Source.Ty s}
    (exposure : Source.Handle context path label lower upper) :
    Source.Wf context (.member label lower upper) :=
  .member (Source.Handle.lowerWf contextValid exposure)
    (Source.Handle.upperWf contextValid exposure)

/-- The type preserved by term compilation is source-well-formed whenever
the input typing context is valid. -/
noncomputable def termResultWf {s : Sig} {context : Source.Ctx s}
    (contextValid : context.Valid) {sourceTerm : Source.Tm s}
    {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type) :
    Source.Wf context type :=
  Source.HasTy.typeWf contextValid derivation

/-! ## Erasure coherence -/

/-- Stage A inserts only proof-erased constructs, so elaboration has exactly
the source runtime program as its erasure. -/
theorem term_erase {s : Sig} {context : Source.Ctx s}
    {sourceTerm : Source.Tm s} {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type) :
    (term derivation).erase = sourceTerm.erase := by
  induction derivation with
  | var binding => rfl
  | lam domainWf bodyTyping induction =>
      simp [term, induction, Source.Tm.erase]
  | obj witnessWf => rfl
  | app functionTyping argumentTyping resultWf => rfl
  | let' rhsTyping bodyTyping resultWf rhsIH bodyIH =>
      simp [term, rhsIH, bodyIH, Source.Tm.erase]
  | sub termTyping inclusion targetWf induction =>
      simpa [term, Explicit.Tm.erase] using induction

end DotFC.Explicit.Elaboration
