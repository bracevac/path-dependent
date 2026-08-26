import LambdaPToFCo.Full.ContextWellFormed

/-!
# Ill-formed internal endpoints in full LambdaPFC typing

These source-only regressions show why a full compiler cannot recursively
request `Tau.Wf` for every endpoint appearing inside a typing or subtyping
derivation, even when the ambient context and public endpoints are well
formed.
-/

namespace LambdaPToFCo.Full.IllWfSubtypingRegression

open LambdaPFC

def label : Name := 0

def sourceDomain : Ty n :=
  .Pair .Top label (Tau.intv .Bot .Top).weaken

def sourceResult : Ty (n + 1) :=
  .TSel (.var 0) label

def sourceFunctionType : Ty n :=
  .Fun sourceDomain sourceResult

def targetFunctionType : Ty n :=
  .Fun .Bot .Top

def sourceDomainWf {context : Ctx n} : Tau.Wf context (.ty sourceDomain) :=
  .pair .top (.bounds_wf .bot .top .bot)

def sourceResultWf {context : Ctx n} :
    Tau.Wf (context.snoc sourceDomain) (.ty sourceResult) := by
  apply Tau.Wf.sel
  · have receiver :
        Path.Ty (context.snoc sourceDomain) (.var 0)
          (.ty sourceDomain.weaken) := .var
    simpa only [sourceDomain, Tau.weaken_open] using receiver.sel_r
  · exact .bot

def sourceFunctionWf {context : Ctx n} :
    Tau.Wf context (.ty sourceFunctionType) :=
  .fun sourceDomainWf sourceResultWf

def targetFunctionWf {context : Ctx n} :
    Tau.Wf context (.ty targetFunctionType) :=
  .fun .bot .top

def selectionPrefix
    {context : Ctx n} {path : Path n} {selectedLabel : Name}
    {result : Tau n kind} :
    Path.Ty context (path.sel selectedLabel) result ->
      Sigma fun first : Ty n =>
      Sigma fun storedLabel : Name =>
      Sigma fun memberKind : Kind =>
      Sigma fun member : Tau (n + 1) memberKind =>
        Path.Ty context path (.ty (.Pair first storedLabel member)) := by
  intro typing
  cases typing with
  | sel_r receiver => exact ⟨_, _, _, _, receiver⟩
  | sel_l receiver _ _ => exact ⟨_, _, _, _, receiver⟩

def botVar_not_pair
    {context : Ctx n} {first : Ty (n + 1)} {storedLabel : Name}
    {member : Tau (n + 2) kind} :
    Path.Ty (context.snoc .Bot) (.var 0)
      (.ty (.Pair first storedLabel member)) -> Empty := by
  intro typing
  cases typing

def botSelection_not_interval
    {context : Ctx n} {selectedLabel : Name}
    {lower upper : Ty (n + 1)} :
    Path.Ty (context.snoc .Bot) ((Path.var 0).sel selectedLabel)
      (.intv lower upper) -> Empty := by
  intro typing
  rcases selectionPrefix typing with ⟨_, _, _, _, receiver⟩
  exact botVar_not_pair receiver

/-- `x.A` is not well formed when the newest variable precisely has `Bot`. -/
def sourceResult_not_wf_under_bot
    {context : Ctx n} :
    Tau.Wf (context.snoc .Bot) (.ty sourceResult) -> Empty := by
  intro wf
  cases wf with
  | sel selection _ => exact botSelection_not_interval selection

/-- Both function endpoints are well formed, but this direct function
subtyping rule checks its source codomain in the target-domain context, where
that codomain is not well formed. -/
def dependentFunctionSubtype :
    Tau.Sub Ctx.nil (.ty sourceFunctionType) (.ty targetFunctionType) :=
  .fun .bot .top

example : Tau.Wf Ctx.nil (.ty sourceFunctionType) := sourceFunctionWf
example : Tau.Wf Ctx.nil (.ty targetFunctionType) := targetFunctionWf
example :
    Tau.Wf (Ctx.nil.snoc .Bot) (.ty sourceResult) -> Empty :=
  sourceResult_not_wf_under_bot

/-! ## A typed application with a non-well-formed result -/

/-- The function is stored first; the newest path has precise type `Bot`. -/
def applicationContext : Ctx 2 :=
  (Ctx.nil.snoc sourceFunctionType).snoc .Bot

def applicationContextWf : ContextWellFormed applicationContext := by
  exact .snoc (.snoc .nil sourceFunctionWf) .bot

def functionPath : Path 2 := .var 1
def argumentPath : Path 2 := .var 0

def functionPrecise :
    Path.Ty applicationContext functionPath (.ty sourceFunctionType) := by
  simpa only [applicationContext, functionPath, Ctx.lookup,
    sourceFunctionType, sourceDomain, sourceResult, Ty.weaken, Ty.rename,
    Tau.rename, Path.rename] using
    (Path.Ty.var : Path.Ty applicationContext functionPath
      (.ty (applicationContext.lookup 1)))

def argumentPrecise :
    Path.Ty applicationContext argumentPath (.ty .Bot) := by
  simpa only [applicationContext, argumentPath, Ctx.lookup, Ty.weaken,
    Ty.rename] using
    (Path.Ty.var : Path.Ty applicationContext argumentPath
      (.ty (applicationContext.lookup 0)))

def functionTyping :
    Tm.Ty applicationContext (.path functionPath) sourceFunctionType :=
  .sub (.path functionPrecise) (.widen functionPrecise) sourceFunctionWf

/-- Subsumption types the `Bot` path at the package domain. -/
def argumentTyping :
    Tm.Ty applicationContext (.path argumentPath) sourceDomain :=
  .sub (.path argumentPrecise)
    (.trans (.widen argumentPrecise) .bot) sourceDomainWf

/-- `Tm.Ty.app` advertises `q.A`; unlike `Tm.Ty.sub` and `Tm.Ty.let`, it has
no result-well-formedness premise. -/
def applicationTyping :
    Tm.Ty applicationContext (.app functionPath argumentPath)
      (sourceResult.open argumentPath) :=
  .app functionTyping argumentTyping

theorem applicationResult_eq :
    sourceResult.open argumentPath = .TSel argumentPath label := rfl

/-- The advertised application result is not well formed despite the
well-formed context and complete typing derivation. -/
def applicationResult_not_wf :
    Tau.Wf applicationContext
      (.ty (sourceResult.open argumentPath)) -> Empty := by
  simpa only [applicationResult_eq] using
    (sourceResult_not_wf_under_bot
      (context := Ctx.nil.snoc sourceFunctionType))

end LambdaPToFCo.Full.IllWfSubtypingRegression
