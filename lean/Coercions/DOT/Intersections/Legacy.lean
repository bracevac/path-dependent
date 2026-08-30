import Coercions.DOT.Acyclic.Source.Structural
import Coercions.DOT.Acyclic.Source.Runtime
import Coercions.DOT.Intersections.Source.Runtime

/-!
# Conservative embedding of the singleton DotFC fragment

`DotFCI` is a genuine extension rather than a replacement namespace.  This
module records the exact conservative boundary: every acyclic type, singleton
object, context, lookup, formation/subtyping/exposure derivation, term typing
derivation, erased term, value, and CBV step embeds into `DotFCI`.

The theorem is intentionally scoped to the old singleton language.  There is
no reverse derivation embedding for intersections or multi-definition objects,
because those constructs have no legacy syntax or rules.
-/

namespace DotFCI.Legacy

open DotFC

/-! ## Syntax and contexts -/

/-- Embed a legacy source type without introducing intersections. -/
def ty {scope : Sig} : DotFC.Source.Ty scope → DotFCI.Source.Ty scope
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (ty domain) (ty codomain)
  | .member label lower upper => .member label (ty lower) (ty upper)
  | .sel path label => .sel path label

/-- Embed a singleton object as a one-element definition list. -/
def tm {scope : Sig} : DotFC.Source.Tm scope → DotFCI.Source.Tm scope
  | .var path => .var path
  | .lam domain body => .lam (ty domain) (tm body)
  | .obj label witness => .obj [⟨label, ty witness⟩]
  | .app function argument => .app function argument
  | .let' rhs body => .let' (tm rhs) (tm body)

@[simp]
theorem ty_rename {source target : Sig} (type : DotFC.Source.Ty source)
    (rho : Rename source target) :
    ty (type.rename rho) = (ty type).rename rho := by
  induction type generalizing target with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp only [DotFC.Source.Ty.rename, ty, DotFCI.Source.Ty.rename]
      rw [domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp only [DotFC.Source.Ty.rename, ty, DotFCI.Source.Ty.rename]
      rw [lowerInduction, upperInduction]
  | sel => rfl

@[simp]
theorem ty_weaken {scope : Sig} {kind : BinderKind}
    (type : DotFC.Source.Ty scope) :
    ty (type.weaken (kind := kind)) = (ty type).weaken := by
  simp [DotFC.Source.Ty.weaken, DotFCI.Source.Ty.weaken]

theorem openAt_eq {scope : Sig} (path : BVar scope .term) :
    DotFC.Source.Rename.openAt path = DotFCI.Source.Rename.openAt path := by
  apply Rename.ext
  intro k x
  cases x <;> rfl

@[simp]
theorem ty_open {scope : Sig} (type : DotFC.Source.Ty (scope ▹ .term))
    (path : BVar scope .term) :
    ty (type.open path) = (ty type).open path := by
  unfold DotFC.Source.Ty.open DotFCI.Source.Ty.open
  rw [ty_rename, openAt_eq]

@[simp]
theorem tm_rename {source target : Sig} (term : DotFC.Source.Tm source)
    (rho : Rename source target) :
    tm (term.rename rho) = (tm term).rename rho := by
  induction term generalizing target with
  | var => rfl
  | lam domain body induction =>
      simp only [DotFC.Source.Tm.rename, tm, DotFCI.Source.Tm.rename]
      rw [ty_rename, induction]
  | obj label witness =>
      simp only [DotFC.Source.Tm.rename, tm, DotFCI.Source.Tm.rename,
        DotFCI.Source.TypeDefs.rename]
      rw [ty_rename]
      rfl
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFC.Source.Tm.rename, tm, DotFCI.Source.Tm.rename]
      rw [rhsInduction, bodyInduction]

/-- Pointwise embedding of legacy source contexts. -/
def context : {scope : Sig} → DotFC.Source.Ctx scope →
    DotFCI.Source.Ctx scope
  | _, .nil => .nil
  | _, .snoc outer type => .snoc (context outer) (ty type)

@[simp]
theorem context_nil : context DotFC.Source.Ctx.nil = DotFCI.Source.Ctx.nil :=
  rfl

@[simp]
theorem context_snoc {scope : Sig} (outer : DotFC.Source.Ctx scope)
    (type : DotFC.Source.Ty scope) :
    context (outer.snoc type) = (context outer).snoc (ty type) := rfl

/-- Legacy lookup is preserved at the exact translated declaration. -/
def lookup {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    {path : BVar scope .term} {type : DotFC.Source.Ty scope}
    (binding : DotFC.Source.Lookup legacyContext path type) :
    DotFCI.Source.Lookup (context legacyContext) path (ty type) :=
  match binding with
  | @DotFC.Source.Lookup.here scope outer bound => by
      rw [ty_weaken]
      exact DotFCI.Source.Lookup.here
  | @DotFC.Source.Lookup.there scope outer bound found path older => by
      rw [ty_weaken]
      exact DotFCI.Source.Lookup.there (lookup older)

/-! ## Full legacy static-derivation embedding -/

mutual

def wf {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    {type : DotFC.Source.Ty scope}
    (derivation : DotFC.Source.Wf legacyContext type) :
    DotFCI.Source.Wf (context legacyContext) (ty type) :=
  match derivation with
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (wf domain) (wf codomain)
  | .member lower upper => .member (wf lower) (wf upper)
  | .sel exposure => .sel (handle exposure)
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Wf.rank]
  all_goals omega

def sub {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    {source target : DotFC.Source.Ty scope}
    (derivation : DotFC.Source.Sub legacyContext source target) :
    DotFCI.Source.Sub (context legacyContext) (ty source) (ty target) :=
  match derivation with
  | .refl typeWf => .refl (wf typeWf)
  | .trans first second => .trans (sub first) (sub second)
  | .bot typeWf => .bot (wf typeWf)
  | .top typeWf => .top (wf typeWf)
  | .member lower upper => .member (sub lower) (sub upper)
  | .lower exposure => .lower (handle exposure)
  | .upper exposure => .upper (handle exposure)
  | .all domain adjustment codomain sourceWf targetWf =>
      .all (sub domain) (ctxMor adjustment) (sub codomain)
        (wf sourceWf) (wf targetWf)
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Sub.rank]
  all_goals omega

def ctxMor {scope : Sig} {actual view : DotFC.Source.Ctx scope}
    (adjustment : DotFC.Source.CtxMor actual view) :
    DotFCI.Source.CtxMor (context actual) (context view) :=
  match adjustment with
  | .id => .id
  | .snoc tail head => .snoc (ctxMor tail) (sub head)
termination_by adjustment.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.CtxMor.rank]
  all_goals omega

def handle {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    {path : BVar scope .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty scope}
    (exposure : DotFC.Source.Handle legacyContext path label lower upper) :
    DotFCI.Source.Handle (context legacyContext) path label
      (ty lower) (ty upper) :=
  match exposure with
  | .direct binding => .direct (lookup binding)
  | .adjust adjustment binding =>
      .adjust (ctxMor adjustment) (lookup binding)
  | .expose binding view => .expose (lookup binding) (sub view)
termination_by exposure.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Handle.rank]
  all_goals omega

end

/-- Every valid legacy context remains valid after translation. -/
def valid {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    (derivation : DotFC.Source.Ctx.Valid legacyContext) :
    DotFCI.Source.Ctx.Valid (context legacyContext) :=
  match derivation with
  | .nil => .nil
  | .snoc outer typeWf => .snoc (valid outer) (wf typeWf)

/-- Full embedding of legacy term-typing derivations.  The only object case
uses `TypeDefs.Valid.singleton`, so its no-duplicate-label obligation is
constructive and immediate. -/
def hasTy {scope : Sig} {legacyContext : DotFC.Source.Ctx scope}
    {term : DotFC.Source.Tm scope} {type : DotFC.Source.Ty scope}
    (derivation : DotFC.Source.HasTy legacyContext term type) :
    DotFCI.Source.HasTy (context legacyContext) (tm term) (ty type) :=
  match derivation with
  | .var binding => .var (lookup binding)
  | .lam domainWf bodyTyping => .lam (wf domainWf) (hasTy bodyTyping)
  | .obj (label := label) (witness := witness) witnessWf =>
      .obj (DotFCI.Source.TypeDefs.Valid.singleton label (ty witness)
        (wf witnessWf))
  | .app functionTyping argumentTyping resultWf => by
      have translatedResult := wf resultWf
      rw [ty_open] at translatedResult
      simpa only [tm, ty_open] using
        DotFCI.Source.HasTy.app (hasTy functionTyping)
          (hasTy argumentTyping) translatedResult
  | .let' rhsTyping bodyTyping resultWf => by
      have translatedBody := hasTy bodyTyping
      rw [ty_weaken] at translatedBody
      exact DotFCI.Source.HasTy.let' (hasTy rhsTyping) translatedBody
        (wf resultWf)
  | .sub termTyping subtyping targetWf =>
      .sub (hasTy termTyping) (sub subtyping) (wf targetWf)

/-! ## Runtime embedding and operational correspondence -/

/-- Legacy unit-like objects become the explicit DotFCI runtime unit. -/
def runtimeTm {scope : Sig} : DotFC.Source.Runtime.Tm scope →
    DotFCI.Source.Runtime.Tm scope
  | .var path => .var path
  | .lam body => .lam (runtimeTm body)
  | .obj => .unit
  | .app function argument => .app (runtimeTm function) (runtimeTm argument)
  | .let' rhs body => .let' (runtimeTm rhs) (runtimeTm body)

@[simp]
theorem runtimeTm_rename {source target : Sig}
    (term : DotFC.Source.Runtime.Tm source) (rho : Rename source target) :
    runtimeTm (term.rename rho) = (runtimeTm term).rename rho := by
  induction term generalizing target with
  | var => rfl
  | lam body induction =>
      simp only [DotFC.Source.Runtime.Tm.rename, runtimeTm,
        DotFCI.Source.Runtime.Tm.rename]
      rw [induction]
  | obj => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFC.Source.Runtime.Tm.rename, runtimeTm,
        DotFCI.Source.Runtime.Tm.rename]
      rw [functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFC.Source.Runtime.Tm.rename, runtimeTm,
        DotFCI.Source.Runtime.Tm.rename]
      rw [rhsInduction, bodyInduction]

@[simp]
theorem runtimeTm_weaken {scope : Sig} {kind : BinderKind}
    (term : DotFC.Source.Runtime.Tm scope) :
    runtimeTm (term.weaken (kind := kind)) = (runtimeTm term).weaken := by
  simp [DotFC.Source.Runtime.Tm.weaken,
    DotFCI.Source.Runtime.Tm.weaken]

/-- Pointwise map of legacy runtime substitutions. -/
def runtimeSubst {source target : Sig}
    (substitution : DotFC.Source.Runtime.Subst source target) :
    DotFCI.Source.Runtime.Subst source target where
  var := fun path => runtimeTm (substitution.var path)

@[simp]
theorem runtimeSubst_lift {source target : Sig}
    (substitution : DotFC.Source.Runtime.Subst source target) :
    runtimeSubst substitution.lift = (runtimeSubst substitution).lift := by
  ext path
  cases path with
  | here => rfl
  | there path => simp [runtimeSubst]

@[simp]
theorem runtimeTm_subst {source target : Sig}
    (term : DotFC.Source.Runtime.Tm source)
    (substitution : DotFC.Source.Runtime.Subst source target) :
    runtimeTm (term.subst substitution) =
      (runtimeTm term).subst (runtimeSubst substitution) := by
  induction term generalizing target with
  | var => rfl
  | lam body induction =>
      simp only [DotFC.Source.Runtime.Tm.subst, runtimeTm,
        DotFCI.Source.Runtime.Tm.subst]
      rw [induction, runtimeSubst_lift]
  | obj => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFC.Source.Runtime.Tm.subst, runtimeTm,
        DotFCI.Source.Runtime.Tm.subst]
      rw [functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFC.Source.Runtime.Tm.subst, runtimeTm,
        DotFCI.Source.Runtime.Tm.subst]
      rw [rhsInduction, bodyInduction, runtimeSubst_lift]

@[simp]
theorem runtimeSubst_openAt {scope : Sig}
    (replacement : DotFC.Source.Runtime.Tm scope) :
    runtimeSubst (DotFC.Source.Runtime.Subst.openAt replacement) =
      DotFCI.Source.Runtime.Subst.openAt (runtimeTm replacement) := by
  ext path
  cases path <;> rfl

@[simp]
theorem runtimeTm_open {scope : Sig}
    (body : DotFC.Source.Runtime.Tm (scope ▹ .term))
    (replacement : DotFC.Source.Runtime.Tm scope) :
    runtimeTm (body.open replacement) =
      (runtimeTm body).open (runtimeTm replacement) := by
  unfold DotFC.Source.Runtime.Tm.open DotFCI.Source.Runtime.Tm.open
  rw [runtimeTm_subst, runtimeSubst_openAt]

/-- Legacy values remain values. -/
def runtimeValue {scope : Sig} {term : DotFC.Source.Runtime.Tm scope}
    (value : DotFC.Source.Runtime.IsValue term) :
    DotFCI.Source.Runtime.IsValue (runtimeTm term) :=
  match value with
  | .lam => .lam
  | .obj => .unit

/-- Every legacy CBV step is simulated by one DotFCI CBV step. -/
def runtimeStep {scope : Sig} {first second : DotFC.Source.Runtime.Tm scope}
    (step : DotFC.Source.Runtime.Step first second) :
    DotFCI.Source.Runtime.Step (runtimeTm first) (runtimeTm second) :=
  match step with
  | .appFunction inner => .appFunction (runtimeStep inner)
  | .appArgument functionValue inner =>
      .appArgument (runtimeValue functionValue) (runtimeStep inner)
  | .beta argumentValue => by
      simpa only [runtimeTm, runtimeTm_open] using
        DotFCI.Source.Runtime.Step.beta (runtimeValue argumentValue)
  | .letRhs inner => .letRhs (runtimeStep inner)
  | .zeta rhsValue => by
      simpa only [runtimeTm, runtimeTm_open] using
        DotFCI.Source.Runtime.Step.zeta (runtimeValue rhsValue)

/-- Legacy multi-step reduction is preserved pointwise. -/
def runtimeSteps {scope : Sig} {first second : DotFC.Source.Runtime.Tm scope}
    (steps : DotFC.Source.Runtime.Steps first second) :
    DotFCI.Source.Runtime.Steps (runtimeTm first) (runtimeTm second) :=
  match steps with
  | .refl => .refl
  | .tail initial final => .tail (runtimeSteps initial) (runtimeStep final)

/-- Source erasure commutes exactly with the conservative embedding. -/
theorem erase_commutes {scope : Sig} (term : DotFC.Source.Tm scope) :
    runtimeTm term.erase = (tm term).erase := by
  induction term with
  | var => rfl
  | lam domain body induction => simp [tm, runtimeTm, induction]
  | obj => rfl
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp [tm, runtimeTm, rhsInduction, bodyInduction]

end DotFCI.Legacy
