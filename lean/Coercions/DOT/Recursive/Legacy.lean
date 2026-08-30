import Coercions.DOT.Intersections.Source.Runtime
import Coercions.DOT.Recursive.Source.Runtime

/-!
# Conservative embedding of nonrecursive DotFCI

Every intersection-signature source derivation embeds without introducing
`mu` or `recObj`.
The runtime map is exact, and source erasure commutes with the embedding.
-/

namespace DotFCR.Legacy

open DotFC

/-! ## Syntax -/

/-- Embed a nonrecursive DotFCI type constructor-for-constructor. -/
def ty {scope : Sig} : DotFCI.Source.Ty scope → DotFCR.Source.Ty scope
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (ty domain) (ty codomain)
  | .member label lower upper => .member label (ty lower) (ty upper)
  | .sel path label => .sel path label
  | .inter left right => .inter (ty left) (ty right)

def typeDef {scope : Sig} (definition : DotFCI.Source.TypeDef scope) :
    DotFCR.Source.TypeDef scope where
  label := definition.label
  witness := ty definition.witness

def typeDefs {scope : Sig} (definitions : List (DotFCI.Source.TypeDef scope)) :
    List (DotFCR.Source.TypeDef scope) :=
  definitions.map typeDef

/-- Plain objects remain plain; the embedding introduces no recursion. -/
def tm {scope : Sig} : DotFCI.Source.Tm scope → DotFCR.Source.Tm scope
  | .var path => .var path
  | .lam domain body => .lam (ty domain) (tm body)
  | .obj definitions => .obj (typeDefs definitions)
  | .app function argument => .app function argument
  | .let' rhs body => .let' (tm rhs) (tm body)

@[simp]
theorem ty_rename {source target : Sig} (type : DotFCI.Source.Ty source)
    (rho : Rename source target) :
    ty (type.rename rho) = (ty type).rename rho := by
  induction type generalizing target with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp only [DotFCI.Source.Ty.rename, ty, DotFCR.Source.Ty.rename]
      rw [domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp only [DotFCI.Source.Ty.rename, ty, DotFCR.Source.Ty.rename]
      rw [lowerInduction, upperInduction]
  | sel => rfl
  | inter left right leftInduction rightInduction =>
      simp only [DotFCI.Source.Ty.rename, ty, DotFCR.Source.Ty.rename]
      rw [leftInduction, rightInduction]

@[simp]
theorem ty_weaken {scope : Sig} {kind : BinderKind}
    (type : DotFCI.Source.Ty scope) :
    ty (type.weaken (kind := kind)) = (ty type).weaken := by
  simp [DotFCI.Source.Ty.weaken, DotFCR.Source.Ty.weaken]

theorem openAt_eq {scope : Sig} (path : BVar scope .term) :
    DotFCI.Source.Rename.openAt path = DotFCR.Source.Rename.openAt path := by
  apply Rename.ext
  intro k x
  cases x <;> rfl

@[simp]
theorem ty_open {scope : Sig} (type : DotFCI.Source.Ty (scope ▹ .term))
    (path : BVar scope .term) :
    ty (type.open path) = (ty type).open path := by
  unfold DotFCI.Source.Ty.open DotFCR.Source.Ty.open
  rw [ty_rename, openAt_eq]

@[simp]
theorem typeDef_rename {source target : Sig}
    (definition : DotFCI.Source.TypeDef source) (rho : Rename source target) :
    typeDef (definition.rename rho) = (typeDef definition).rename rho := by
  cases definition
  simp [typeDef, DotFCI.Source.TypeDef.rename,
    DotFCR.Source.TypeDef.rename]

@[simp]
theorem typeDefs_rename {source target : Sig}
    (definitions : List (DotFCI.Source.TypeDef source))
    (rho : Rename source target) :
    typeDefs (DotFCI.Source.TypeDefs.rename definitions rho) =
      DotFCR.Source.TypeDefs.rename (typeDefs definitions) rho := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      simp [typeDefs, DotFCI.Source.TypeDefs.rename,
        DotFCR.Source.TypeDefs.rename]

@[simp]
theorem ty_exact {scope : Sig}
    (definitions : List (DotFCI.Source.TypeDef scope)) :
    ty (DotFCI.Source.TypeDefs.exact definitions) =
      DotFCR.Source.TypeDefs.exact (typeDefs definitions) := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      cases remaining with
      | nil => rfl
      | cons next rest =>
          simp only [DotFCI.Source.TypeDefs.exact,
            DotFCR.Source.TypeDefs.exact, ty, typeDefs, List.map_cons]
          exact congrArg (DotFCR.Source.Ty.inter
            (typeDef definition).exactTy) induction

@[simp]
theorem tm_rename {source target : Sig} (term : DotFCI.Source.Tm source)
    (rho : Rename source target) :
    tm (term.rename rho) = (tm term).rename rho := by
  induction term generalizing target with
  | var => rfl
  | lam domain body induction =>
      simp only [DotFCI.Source.Tm.rename, tm, DotFCR.Source.Tm.rename]
      rw [ty_rename, induction]
  | obj definitions =>
      simp only [DotFCI.Source.Tm.rename, tm, DotFCR.Source.Tm.rename]
      rw [typeDefs_rename]
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFCI.Source.Tm.rename, tm, DotFCR.Source.Tm.rename]
      rw [rhsInduction, bodyInduction]

/-! ## Contexts and static derivations -/

def context : {scope : Sig} → DotFCI.Source.Ctx scope →
    DotFCR.Source.Ctx scope
  | _, .nil => .nil
  | _, .snoc outer type => .snoc (context outer) (ty type)

@[simp]
theorem context_nil :
    context DotFCI.Source.Ctx.nil = DotFCR.Source.Ctx.nil := rfl

@[simp]
theorem context_snoc {scope : Sig} (outer : DotFCI.Source.Ctx scope)
    (type : DotFCI.Source.Ty scope) :
    context (outer.snoc type) = (context outer).snoc (ty type) := rfl

def lookup {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {path : BVar scope .term} {type : DotFCI.Source.Ty scope}
    (binding : DotFCI.Source.Lookup legacyContext path type) :
    DotFCR.Source.Lookup (context legacyContext) path (ty type) :=
  match binding with
  | @DotFCI.Source.Lookup.here scope outer bound => by
      rw [ty_weaken]
      exact DotFCR.Source.Lookup.here
  | @DotFCI.Source.Lookup.there scope outer bound found path older => by
      rw [ty_weaken]
      exact DotFCR.Source.Lookup.there (lookup older)

mutual

def wf {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {type : DotFCI.Source.Ty scope}
    (derivation : DotFCI.Source.Wf legacyContext type) :
    DotFCR.Source.Wf (context legacyContext) (ty type) :=
  match derivation with
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (wf domain) (wf codomain)
  | .member lower upper => .member (wf lower) (wf upper)
  | .sel exposure => .sel (handle exposure)
  | .inter left right => .inter (wf left) (wf right)
termination_by sizeOf derivation
decreasing_by
  all_goals simp_wf
  all_goals omega

def sub {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {source target : DotFCI.Source.Ty scope}
    (derivation : DotFCI.Source.Sub legacyContext source target) :
    DotFCR.Source.Sub (context legacyContext) (ty source) (ty target) :=
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
  | .inter left right => .inter (sub left) (sub right)
  | .interLeft => .interLeft
  | .interRight => .interRight
termination_by sizeOf derivation
decreasing_by
  all_goals simp_wf
  all_goals omega

def ctxMor {scope : Sig} {actual view : DotFCI.Source.Ctx scope}
    (adjustment : DotFCI.Source.CtxMor actual view) :
    DotFCR.Source.CtxMor (context actual) (context view) :=
  match adjustment with
  | .id => .id
  | .snoc tail head => .snoc (ctxMor tail) (sub head)
termination_by sizeOf adjustment
decreasing_by
  all_goals simp_wf
  all_goals omega

def handle {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {path : BVar scope .term} {label : DotFCI.Source.Name}
    {lower upper : DotFCI.Source.Ty scope}
    (exposure : DotFCI.Source.Handle legacyContext path label lower upper) :
    DotFCR.Source.Handle (context legacyContext) path label
      (ty lower) (ty upper) :=
  match exposure with
  | .direct binding => .direct (lookup binding)
  | .adjust adjustment binding =>
      .adjust (ctxMor adjustment) (lookup binding)
  | .expose binding view => .expose (lookup binding) (sub view)
termination_by sizeOf exposure
decreasing_by
  all_goals simp_wf
  all_goals omega

end

def valid {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    (derivation : DotFCI.Source.Ctx.Valid legacyContext) :
    DotFCR.Source.Ctx.Valid (context legacyContext) :=
  match derivation with
  | .nil => .nil
  | .snoc outer typeWf => .snoc (valid outer) (wf typeWf)

def allWf {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {definitions : List (DotFCI.Source.TypeDef scope)}
    (derivation : DotFCI.Source.TypeDefs.AllWf legacyContext definitions) :
    DotFCR.Source.TypeDefs.AllWf (context legacyContext)
      (typeDefs definitions) :=
  match derivation with
  | .nil => .nil
  | .cons witnessWf remainingWf => .cons (wf witnessWf) (allWf remainingWf)

@[simp]
theorem labels_typeDefs {scope : Sig}
    (definitions : List (DotFCI.Source.TypeDef scope)) :
    DotFCR.Source.TypeDefs.labels (typeDefs definitions) =
      DotFCI.Source.TypeDefs.labels definitions := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      simp [DotFCR.Source.TypeDefs.labels, DotFCI.Source.TypeDefs.labels,
        typeDefs, typeDef]

def typeDefsValid {scope : Sig}
    {legacyContext : DotFCI.Source.Ctx scope}
    {definitions : List (DotFCI.Source.TypeDef scope)}
    (derivation : DotFCI.Source.TypeDefs.Valid legacyContext definitions) :
    DotFCR.Source.TypeDefs.Valid (context legacyContext)
      (typeDefs definitions) where
  witnesses := allWf derivation.witnesses
  labelsNoDup := by
    rw [labels_typeDefs]
    exact derivation.labelsNoDup

def hasTy {scope : Sig} {legacyContext : DotFCI.Source.Ctx scope}
    {term : DotFCI.Source.Tm scope} {type : DotFCI.Source.Ty scope}
    (derivation : DotFCI.Source.HasTy legacyContext term type) :
    DotFCR.Source.HasTy (context legacyContext) (tm term) (ty type) :=
  match derivation with
  | .var binding => .var (lookup binding)
  | .lam domainWf bodyTyping => .lam (wf domainWf) (hasTy bodyTyping)
  | .obj definitionsValid => by
      rw [ty_exact]
      exact .obj (typeDefsValid definitionsValid)
  | .app functionTyping argumentTyping resultWf => by
      have translatedResult := wf resultWf
      rw [ty_open] at translatedResult
      simpa only [tm, ty_open] using
        DotFCR.Source.HasTy.app (hasTy functionTyping)
          (hasTy argumentTyping) translatedResult
  | .let' rhsTyping bodyTyping resultWf => by
      have translatedBody := hasTy bodyTyping
      rw [ty_weaken] at translatedBody
      exact DotFCR.Source.HasTy.let' (hasTy rhsTyping) translatedBody
        (wf resultWf)
  | .sub termTyping subtyping targetWf =>
      .sub (hasTy termTyping) (sub subtyping) (wf targetWf)

/-! ## Runtime embedding -/

def runtimeTm {scope : Sig} : DotFCI.Source.Runtime.Tm scope →
    DotFCR.Source.Runtime.Tm scope
  | .var path => .var path
  | .lam body => .lam (runtimeTm body)
  | .unit => .unit
  | .app function argument => .app (runtimeTm function) (runtimeTm argument)
  | .let' rhs body => .let' (runtimeTm rhs) (runtimeTm body)

@[simp]
theorem runtimeTm_rename {source target : Sig}
    (term : DotFCI.Source.Runtime.Tm source) (rho : Rename source target) :
    runtimeTm (term.rename rho) = (runtimeTm term).rename rho := by
  induction term generalizing target with
  | var => rfl
  | lam body induction =>
      simp only [DotFCI.Source.Runtime.Tm.rename, runtimeTm,
        DotFCR.Source.Runtime.Tm.rename]
      rw [induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFCI.Source.Runtime.Tm.rename, runtimeTm,
        DotFCR.Source.Runtime.Tm.rename]
      rw [functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFCI.Source.Runtime.Tm.rename, runtimeTm,
        DotFCR.Source.Runtime.Tm.rename]
      rw [rhsInduction, bodyInduction]

@[simp]
theorem runtimeTm_weaken {scope : Sig} {kind : BinderKind}
    (term : DotFCI.Source.Runtime.Tm scope) :
    runtimeTm (term.weaken (kind := kind)) = (runtimeTm term).weaken := by
  simp [DotFCI.Source.Runtime.Tm.weaken,
    DotFCR.Source.Runtime.Tm.weaken]

def runtimeSubst {source target : Sig}
    (substitution : DotFCI.Source.Runtime.Subst source target) :
    DotFCR.Source.Runtime.Subst source target where
  var := fun path => runtimeTm (substitution.var path)

@[simp]
theorem runtimeSubst_lift {source target : Sig}
    (substitution : DotFCI.Source.Runtime.Subst source target) :
    runtimeSubst substitution.lift = (runtimeSubst substitution).lift := by
  ext path
  cases path with
  | here => rfl
  | there path => simp [runtimeSubst]

@[simp]
theorem runtimeTm_subst {source target : Sig}
    (term : DotFCI.Source.Runtime.Tm source)
    (substitution : DotFCI.Source.Runtime.Subst source target) :
    runtimeTm (term.subst substitution) =
      (runtimeTm term).subst (runtimeSubst substitution) := by
  induction term generalizing target with
  | var => rfl
  | lam body induction =>
      simp only [DotFCI.Source.Runtime.Tm.subst, runtimeTm,
        DotFCR.Source.Runtime.Tm.subst]
      rw [induction, runtimeSubst_lift]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFCI.Source.Runtime.Tm.subst, runtimeTm,
        DotFCR.Source.Runtime.Tm.subst]
      rw [functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFCI.Source.Runtime.Tm.subst, runtimeTm,
        DotFCR.Source.Runtime.Tm.subst]
      rw [rhsInduction, bodyInduction, runtimeSubst_lift]

@[simp]
theorem runtimeSubst_openAt {scope : Sig}
    (replacement : DotFCI.Source.Runtime.Tm scope) :
    runtimeSubst (DotFCI.Source.Runtime.Subst.openAt replacement) =
      DotFCR.Source.Runtime.Subst.openAt (runtimeTm replacement) := by
  ext path
  cases path <;> rfl

@[simp]
theorem runtimeTm_open {scope : Sig}
    (body : DotFCI.Source.Runtime.Tm (scope ▹ .term))
    (replacement : DotFCI.Source.Runtime.Tm scope) :
    runtimeTm (body.open replacement) =
      (runtimeTm body).open (runtimeTm replacement) := by
  unfold DotFCI.Source.Runtime.Tm.open DotFCR.Source.Runtime.Tm.open
  rw [runtimeTm_subst, runtimeSubst_openAt]

def runtimeValue {scope : Sig} {term : DotFCI.Source.Runtime.Tm scope}
    (value : DotFCI.Source.Runtime.IsValue term) :
    DotFCR.Source.Runtime.IsValue (runtimeTm term) :=
  match value with
  | .lam => .lam
  | .unit => .unit

def runtimeStep {scope : Sig}
    {first second : DotFCI.Source.Runtime.Tm scope}
    (step : DotFCI.Source.Runtime.Step first second) :
    DotFCR.Source.Runtime.Step (runtimeTm first) (runtimeTm second) :=
  match step with
  | .appFunction inner => .appFunction (runtimeStep inner)
  | .appArgument functionValue inner =>
      .appArgument (runtimeValue functionValue) (runtimeStep inner)
  | .beta argumentValue => by
      simpa only [runtimeTm, runtimeTm_open] using
        DotFCR.Source.Runtime.Step.beta (runtimeValue argumentValue)
  | .letRhs inner => .letRhs (runtimeStep inner)
  | .zeta rhsValue => by
      simpa only [runtimeTm, runtimeTm_open] using
        DotFCR.Source.Runtime.Step.zeta (runtimeValue rhsValue)

def runtimeSteps {scope : Sig}
    {first second : DotFCI.Source.Runtime.Tm scope}
    (steps : DotFCI.Source.Runtime.Steps first second) :
    DotFCR.Source.Runtime.Steps (runtimeTm first) (runtimeTm second) :=
  match steps with
  | .refl => .refl
  | .tail initial final => .tail (runtimeSteps initial) (runtimeStep final)

/-- Source erasure commutes exactly with the conservative embedding. -/
theorem erase_commutes {scope : Sig} (term : DotFCI.Source.Tm scope) :
    runtimeTm term.erase = (tm term).erase := by
  induction term with
  | var => rfl
  | lam domain body induction => simp [tm, runtimeTm, induction]
  | obj => rfl
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp [tm, runtimeTm, rhsInduction, bodyInduction]

end DotFCR.Legacy
