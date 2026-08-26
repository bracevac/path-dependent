import LambdaPToFCo.Direct.Application
import LambdaPToFCo.Direct.Adaptation
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
# Direct dependent-application regression

This checks a variable function applied to a variable argument.  Both source
path terms are compiled as singleton introductions followed by their literal
singleton-widening derivations.  The argument compiler is demanded at the
exact Top domain exposed by the function representation, after which the
application leaf invokes the retained ordinary code and returns the opened
Top codomain slot under CPS.
-/

namespace LambdaPToFCo.Direct.ApplicationRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.TermIntroduction
open LambdaPToFCo.Direct.Internal.Application

abbrev TargetContext : Ctx [] := Ctx.empty

abbrev DomainSource : LambdaPFC.Ty 2 := .Top
abbrev CodomainSource : LambdaPFC.Ty 3 := .Top
abbrev FunctionSource : LambdaPFC.Ty 2 :=
  .Fun DomainSource CodomainSource

/-- The older variable is the Top argument; the newer variable is the
Top-to-Top function. -/
abbrev SourceContext : LambdaPFC.Ctx 2 :=
  LambdaPFC.Ctx.snoc
    (LambdaPFC.Ctx.snoc LambdaPFC.Ctx.nil (.Top : LambdaPFC.Ty 0))
    (.Fun (.Top : LambdaPFC.Ty 1) (.Top : LambdaPFC.Ty 2))

abbrev functionPath : LambdaPFC.Path 2 := .var 0
abbrev argumentPath : LambdaPFC.Path 2 := .var 1

def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

noncomputable def topSlot (base : Ctx sig) :
    Slot base (.Top : LambdaPFC.Ty n) where
  shape := .stable (Top.plan sig)
  interface := {
    arguments := Top.arguments .top topPayload (topPayload_hasType base) }
  rep := .top base

noncomputable def domain :
    LambdaPToFCo.Direct.Internal.Wf.Proper TargetContext DomainSource :=
  .top TargetContext

noncomputable def body :
    Slot (domain.shape.context TargetContext) CodomainSource :=
  topSlot (domain.shape.context TargetContext)

noncomputable def functionSlot : Slot TargetContext FunctionSource :=
  abstractSlot domain body

noncomputable def argumentSlot : Slot TargetContext DomainSource :=
  topSlot TargetContext

noncomputable def environment : Env SourceContext TargetContext where
  lookup := Fin.cases functionSlot (fun older =>
    Fin.cases argumentSlot (fun impossible => Fin.elim0 impossible) older)

def functionPathTyping : LambdaPFC.Path.Ty SourceContext functionPath
    (.ty FunctionSource) := by
  exact .var

def argumentPathTyping : LambdaPFC.Path.Ty SourceContext argumentPath
    (.ty DomainSource) := by
  exact .var

def functionDerivation : LambdaPFC.Tm.Ty SourceContext
    (.path functionPath) FunctionSource :=
  .sub (.path functionPathTyping) (.widen functionPathTyping)
    (.fun .top .top)

def argumentDerivation : LambdaPFC.Tm.Ty SourceContext
    (.path argumentPath) DomainSource :=
  .sub (.path argumentPathTyping) (.widen argumentPathTyping) .top

/-- The literal source `Tm.Ty.app` derivation exercised below. -/
def derivation : LambdaPFC.Tm.Ty SourceContext
    (.app functionPath argumentPath)
    (CodomainSource.open argumentPath) :=
  .app functionDerivation argumentDerivation

/-! ## Exact compilation of the two full path-term premises -/

/-- Compile a path term followed by its literal singleton widening.  This
small regression helper uses the same `Path.compile` and `adaptSlot` junctions
as the recursive dispatcher. -/
noncomputable def compileWidenedPath
    {path : LambdaPFC.Path 2} {sourceType : LambdaPFC.Ty 2}
    (typing : LambdaPFC.Path.Ty SourceContext path (.ty sourceType)) :
    ValueComputation SourceContext TargetContext sourceType :=
  fun answer consumer =>
    Path.compile typing environment answer
      (fun mapping typed nextEnvironment view => by
        cases view with
        | proper referent =>
            let singleton := singletonSlot path referent
            let widening :=
              AtomicSubtyping.widenAt path referent
            let adapted := TermAdaptation.adaptSlot nextEnvironment singleton
              widening.relation
            let localConsumer : ValueConsumer SourceContext _
                (answer.rename mapping) sourceType :=
              fun next nextTyped finalEnvironment result => by
                let combined := mapping.comp next
                let combinedTyped := TypedRename.comp typed nextTyped
                simpa only [Ty.rename_comp] using
                  consumer combined combinedTyped finalEnvironment result
            exact adapted (answer.rename mapping) localConsumer)

noncomputable def functionCompilation :
    FunctionComputation functionDerivation TargetContext :=
  compileWidenedPath functionPathTyping

/-- The exact application kernel instantiated with the already compiled
function and argument interfaces.  The derivation-directed outer dispatcher
will supply the same two interfaces after its recursive cuts. -/
noncomputable def compiledExact : ValueComputation SourceContext TargetContext
    (CodomainSource.open argumentPath) :=
  applyExact environment argumentPath functionSlot.interface domain.rep
    body.rep argumentSlot.interface

/-- The closed CPS program produced by the rule is typed in unchanged
System FCo. -/
noncomputable def compiledAtTop : Path.Body TargetContext
    (Top.plan []).inputTy :=
  compiledExact (Top.plan []).inputTy
    (fun {current} {currentContext} mapping _typed _environment _result => by
      let canonical := topSlot (n := 2) currentContext
      exact {
        expression := canonical.interface.package
        typing := by
          simpa only [Shape.inputTy_rename, Shape.rename,
            Top.plan_rename] using canonical.interface.package_hasType
      })

example : Exp.HasType TargetContext compiledAtTop.expression
    (Top.plan []).inputTy :=
  compiledAtTop.typing

end

end LambdaPToFCo.Direct.ApplicationRegression
