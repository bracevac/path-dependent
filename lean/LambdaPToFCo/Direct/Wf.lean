import LambdaPToFCo.Direct.Path

/-!
# Direct well-formed type representations

Well-formed proper types are represented by one existential target `Shape`
and the exact source-indexed `Representation.Rep` for that shape.  A
well-formed interval retains only its two endpoint shapes and endpoint
representations; formation does not choose a selected type or fabricate a
stable plan for one.

The atomic path-dependent constructors are compiled with `Path.compile`.
Their result is exposed only to a scope-natural consumer, so a hidden type
opened while following a path never escapes its System FCo elimination body.
The structural constructors below combine already-materialized children in
their exact binder scopes.  This is enough for structural recursion that does
not open an additional existential while computing a dependent child, and it
keeps the remaining scope problem explicit instead of silently duplicating or
canonicalizing a parent interface.
-/

namespace LambdaPToFCo.Direct.Internal.Wf

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

/-- Exact material representation of one well-formed proper source type. -/
structure Proper {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig)
    (sourceType : LambdaPFC.Ty n) : Type where
  shape : Shape sig
  rep : Rep targetContext sourceType shape

/-- Exact material endpoint representations of one well-formed interval.

The source nonemptiness derivation belongs to subtyping compilation.  Wf
formation itself needs no selected target type and no endpoint functions. -/
structure Interval {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig)
    (lowerSource upperSource : LambdaPFC.Ty n) : Type where
  lower : Shape sig
  upper : Shape sig
  lowerRep : Rep targetContext lowerSource lower
  upperRep : Rep targetContext upperSource upper

/-- Kind-complete material result exposed by Wf compilation. -/
inductive View {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper (result : Proper targetContext sourceType) :
    View targetContext (.ty sourceType)
| interval (result : Interval targetContext lowerSource upperSource) :
    View targetContext (.intv lowerSource upperSource)

namespace Proper

/-- Canonical bottom representation. -/
def bottom {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig) :
    Proper (n := n) targetContext .Bot where
  shape := .stable (Bot.plan sig)
  rep := .bottom targetContext

/-- Canonical top representation. -/
def top {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig) :
    Proper (n := n) targetContext .Top where
  shape := .stable (Top.plan sig)
  rep := .top targetContext

/-- Complete target package type of an already-resolved path referent. -/
def referentType
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) : SystemFCo.Ty sig :=
  slot.shape.inputTy

/-- Form a singleton from the exact already-open referent slot.

The singleton bridges its own hidden identity to the referent's complete
package type.  Widening can consequently recover that package and then open
it through the exact retained `Rep`; it never needs to reify or guess the
referent's hidden identity. -/
noncomputable def singletonFromSlot
    {targetContext : SystemFCo.Ctx sig}
    {referent : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n)
    (slot : Slot targetContext referent) :
    Proper targetContext (.Single path) where
  shape := .stable (Single.plan (referentType slot))
  rep := .singleton targetContext path (referentType slot)

/-- Variable paths need no target elimination: their exact interface is
already present in the environment. -/
noncomputable def singletonVariable
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) :
    Proper targetContext (.Single (.var index)) :=
  singletonFromSlot (.var index) (environment.lookup index)

/-- Form a selected proper type from the exact opened interval view.  The
selected shape stays opaque. -/
noncomputable def selection
    {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (path : LambdaPFC.Path n) (label : LambdaPFC.Name)
    (interval : IntervalRep (targetContext := targetContext)
      lowerSource upperSource lower selectedType upper) :
    Proper targetContext (.TSel path label) where
  shape := .opaque selectedType
  rep := interval.selection path label

/-- Assemble a function from children already materialized in the domain's
exact opened scope. -/
def function
    {targetContext : SystemFCo.Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Proper targetContext domainSource)
    (codomain : Proper (domain.shape.context targetContext) codomainSource) :
    Proper targetContext (.Fun domainSource codomainSource) where
  shape := .stable (Function.plan domain.shape codomain.shape)
  rep := .function domain.rep codomain.rep

/-- Assemble a proper-member pair from children in the exact first-component
scope. -/
def properPair
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Proper targetContext firstSource)
    (member : Proper (first.shape.context targetContext) memberSource) :
    Proper targetContext (.Pair firstSource label (.ty memberSource)) where
  shape := .stable (Pair.Proper.plan first.shape member.shape)
  rep := .properPair first.rep member.rep

/-- Assemble an interval-member pair from the exact endpoint representations
under the first-component scope. -/
def intervalPair
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Proper targetContext firstSource)
    (member : Interval (first.shape.context targetContext)
      lowerSource upperSource) :
    Proper targetContext
      (.Pair firstSource label (.intv lowerSource upperSource)) where
  shape := .stable
    (Pair.Interval.plan first.shape member.lower member.upper)
  rep := .intervalPair first.rep member.lowerRep member.upperRep

/-- Reindex a material proper result through a typed target renaming. -/
noncomputable def targetRename
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {sourceType : LambdaPFC.Ty n}
    (result : Proper sourceContext sourceType)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Proper targetContext sourceType where
  shape := result.shape.rename mapping
  rep := result.rep.targetRename mapping typed

end Proper

namespace Interval

/-- Interval formation retains exactly the two proper endpoint
representations.  Its source nonemptiness premise is deliberately not turned
into target syntax here. -/
def bounds
    {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (lower : Proper targetContext lowerSource)
    (upper : Proper targetContext upperSource) :
    Interval targetContext lowerSource upperSource where
  lower := lower.shape
  upper := upper.shape
  lowerRep := lower.rep
  upperRep := upper.rep

/-- Reindex material interval endpoints through a typed target renaming. -/
noncomputable def targetRename
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (result : Interval sourceContext lowerSource upperSource)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Interval targetContext lowerSource upperSource where
  lower := result.lower.rename mapping
  upper := result.upper.rename mapping
  lowerRep := result.lowerRep.targetRename mapping typed
  upperRep := result.upperRep.targetRename mapping typed

end Interval

/-- A Wf consumer natural in every target scope opened by focused path
compilation.  The environment remains separate from the representation
result; endpoint results never carry invented interfaces. -/
abbrev Consumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    {kind : LambdaPFC.Kind} (source : LambdaPFC.Tau n kind) : Type :=
  forall {current : Sig} {currentContext : SystemFCo.Ctx current},
    (mapping : SystemFCo.Rename root current) ->
    SystemFCo.Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    View currentContext source ->
    Path.Body currentContext (answer.rename mapping)

/-- Invoke a natural Wf consumer in its root scope. -/
private noncomputable def consumeHere
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {answer : SystemFCo.Ty sig}
    {kind : LambdaPFC.Kind} {source : LambdaPFC.Tau n kind}
    (environment : Env sourceContext targetContext)
    (view : View targetContext source)
    (consumer : Consumer sourceContext targetContext answer source) :
    Path.Body targetContext answer := by
  simpa only [SystemFCo.Ty.rename_id] using
    consumer SystemFCo.Rename.id (TypedRename.id targetContext)
      environment view

/-- Compile the `Wf.bot` constructor. -/
noncomputable def compileBottom
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer
      (.ty (.Bot : LambdaPFC.Ty n))) :
    Path.Body targetContext answer :=
  consumeHere environment (.proper (.bottom targetContext)) consumer

/-- Compile the `Wf.top` constructor. -/
noncomputable def compileTop
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer
      (.ty (.Top : LambdaPFC.Ty n))) :
    Path.Body targetContext answer :=
  consumeHere environment (.proper (.top targetContext)) consumer

/-- Compile the `Wf.path` constructor against the exact focused proper slot. -/
noncomputable def compilePath
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer
      (.ty (.Single path))) :
    Path.Body targetContext answer :=
  Path.compile typing environment answer (fun mapping typed nextEnvironment
      view => by
    cases view with
    | proper slot =>
        exact consumer mapping typed nextEnvironment
          (.proper (Proper.singletonFromSlot path slot)))

/-- Compile the `Wf.sel` constructor against the exact focused interval.
The source nonemptiness premise does not select or repackage the hidden target
type; its computational use belongs to subtyping. -/
noncomputable def compileSelection
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (_nonempty : LambdaPFC.Tau.Sub sourceContext
      (.ty lowerSource) (.ty upperSource))
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer
      (.ty (.TSel path label))) :
    Path.Body targetContext answer :=
  Path.compile typing environment answer (fun mapping typed nextEnvironment
      view => by
    cases view with
    | interval interval =>
        exact consumer mapping typed nextEnvironment
          (.proper (Proper.selection path label interval)))

/-- Expose an already-materialized proper result to a natural consumer.  This
is the structural handoff used after `function`, `properPair`, or
`intervalPair` has assembled children in the exact required scopes. -/
noncomputable def compileProper
    {sourceContext : LambdaPFC.Ctx n}
    {sourceType : LambdaPFC.Ty n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (result : Proper targetContext sourceType)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer (.ty sourceType)) :
    Path.Body targetContext answer :=
  consumeHere environment (.proper result) consumer

/-- Expose materialized Wf interval endpoints to a natural consumer. -/
noncomputable def compileInterval
    {sourceContext : LambdaPFC.Ctx n}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (result : Interval targetContext lowerSource upperSource)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer
      (.intv lowerSource upperSource)) :
    Path.Body targetContext answer :=
  consumeHere environment (.interval result) consumer

end LambdaPToFCo.Direct.Internal.Wf
