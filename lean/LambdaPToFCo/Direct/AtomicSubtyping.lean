import LambdaPToFCo.Direct.Relation
import LambdaPToFCo.Direct.Wf

/-!
# Direct atomic subtyping rules

These constructors consume the literal atomic `LambdaPFC.Tau.Sub` premises
and build ordinary `SystemFCo` conversions plus identity-preserving
`InterfaceMap`s.  Path-driven rules stay under `Path.compile`: a hidden shape
is returned only to a scope-natural consumer and never escapes its package
elimination scope.

`Result` is the single existential boundary for proper endpoint shapes.  The
outer rule compiler must either use those computed shapes or continue in its
consumer; this module deliberately provides no equality certificate for
matching an independently chosen demand.  The interval nonemptiness premises
are computationally erased because an opened interval already carries its
two exact typed endpoint functions.
-/

namespace LambdaPToFCo.Direct.Internal.AtomicSubtyping

open SystemFCo
open Representation

/-- Exact proper endpoint shapes and their direct subtyping relation. -/
structure Result (base : Ctx sig)
    (sourceType targetType : LambdaPFC.Ty n) : Type where
  source : Shape sig
  target : Shape sig
  relation : Relation base sourceType targetType source target

namespace Result

noncomputable def targetRename
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourceType targetType : LambdaPFC.Ty n}
    (result : Result sourceContext sourceType targetType)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Result targetContext sourceType targetType where
  source := result.source.rename mapping
  target := result.target.rename mapping
  relation := result.relation.targetRename mapping typed

end Result

/-- A proper-rule consumer natural in every target scope opened by a path. -/
abbrev Consumer
    {n : Nat} {root : Sig}
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (rootContext : Ctx root) (answer : Ty root)
    (sourceType targetType : LambdaPFC.Ty n) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    Rename.Typed rootContext currentContext mapping ->
    EndpointEnvs sourceContext targetContext currentContext ->
    Result currentContext sourceType targetType ->
    Path.Body currentContext (answer.rename mapping)

private noncomputable def focusedEnvironments
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin} {currentContext : Ctx current}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide)
    (mapping : Rename origin current)
    (typed : Rename.Typed base currentContext mapping)
    (focused : Env (environments.proofContext side) currentContext) :
    EndpointEnvs sourceContext targetContext currentContext := by
  cases side with
  | source =>
      exact {
        source := focused
        target := environments.target.targetRename mapping typed
      }
  | target =>
      exact {
        source := environments.source.targetRename mapping typed
        target := focused
      }

/-- Proper reflexivity preserves the exact supplied representation. -/
noncomputable def refl
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (source : Wf.Proper base sourceType) :
    Result base sourceType sourceType where
  source := source.shape
  target := source.shape
  relation := Relation.refl source.rep

private noncomputable def bottomConversion
    {base : Ctx sig} {targetType : LambdaPFC.Ty n}
    {target : Shape sig} (targetRep : Rep base targetType target) :
    Conversion base (Bot.plan sig).inputTy target.inputTy := by
  cases target with
  | stable plan =>
      exact Conversion.stableBottom base plan targetRep.termOnly
  | «opaque» type =>
      exact (Conversion.stableBottom base (Single.plan type)
        (Single.termOnly type)).compose
          (Conversion.Singleton.unwrap base type)

/-- Bottom elimination into any represented stable or opaque target. -/
noncomputable def bot
    {base : Ctx sig} {targetType : LambdaPFC.Ty n}
    (target : Wf.Proper base targetType) :
    Result base .Bot targetType where
  source := .stable (Bot.plan sig)
  target := target.shape
  relation := Relation.ofConversion (.bottom base) target.rep
    (bottomConversion target.rep)

private noncomputable def topConversion
    (base : Ctx sig) (source : Shape sig) :
    Conversion base source.inputTy (Top.plan sig).inputTy := by
  cases source with
  | stable plan =>
      exact Conversion.stableTop base plan
  | «opaque» type =>
      exact (Conversion.Singleton.wrap base type).compose
        (Conversion.stableTop base (Single.plan type))

/-- Erase all observations into canonical Top. -/
noncomputable def top
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (source : Wf.Proper base sourceType) :
    Result base sourceType .Top where
  source := source.shape
  target := .stable (Top.plan sig)
  relation := Relation.ofConversion source.rep (.top base)
    (topConversion base source.shape)

/-- Exact widening result at a resolved proper path slot. -/
noncomputable def widenAt
    {base : Ctx sig} {targetType : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n) (slot : Slot base targetType) :
    Result base (.Single path) targetType where
  source := .stable (Single.plan slot.shape.inputTy)
  target := slot.shape
  relation := Relation.ofConversion
    (.singleton base path slot.shape.inputTy) slot.rep
    (Conversion.Singleton.unwrap base slot.shape.inputTy)

/-- Compile singleton widening under the literal path derivation. -/
noncomputable def widen
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide)
    {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty (environments.proofContext side) path
      (.ty targetType))
    (answer : Ty sig)
    (consumer : Consumer sourceContext targetContext base answer
      (.Single path) targetType) : Path.Body base answer :=
  Path.compile typing (environments.environment side) answer
    (fun mapping typed focused view => by
      cases view with
      | proper slot =>
          exact consumer mapping typed
            (focusedEnvironments environments side mapping typed focused)
            (widenAt path slot))

/-- Exact singleton-symmetry result after faithful closure exposure has
reached the literal singleton representation. -/
private noncomputable def symmResult
    {base : Ctx sig} {sourcePath : LambdaPFC.Path n}
    (targetPath : LambdaPFC.Path n)
    (referent : Ty sig) :
    Result base (.Single sourcePath) (.Single targetPath) :=
  let targetRep : Rep base (.Single targetPath)
      (.stable (Single.plan (Single.plan referent).inputTy)) :=
    .singleton base targetPath (Single.plan referent).inputTy
  let bridge := Conversion.Singleton.selfBridge base referent
  let conversion := Conversion.Singleton.retarget base referent
    (Single.plan referent).inputTy bridge
  {
    source := .stable (Single.plan referent)
    target := .stable (Single.plan (Single.plan referent).inputTy)
    relation := Relation.ofConversion
      (.singleton base sourcePath referent) targetRep conversion
  }

/-- Singleton symmetry of an unreachable value changes only the source path
index.  The same retained Bottom represents both endpoints, and the target
conversion is ordinary identity at `forall X. X`. -/
private noncomputable def symmAbsurdResult
    {base : Ctx sig} {sourcePath : LambdaPFC.Path n}
    (targetPath : LambdaPFC.Path n)
    (bottomValue : Exp sig)
    (bottomTyping : Exp.HasType base bottomValue Adapter.bottomTy) :
    Result base (.Single sourcePath) (.Single targetPath) where
  source := .opaque Adapter.bottomTy
  target := .opaque Adapter.bottomTy
  relation := Relation.ofConversion
    (.absurd bottomValue bottomTyping)
    (.absurd bottomValue bottomTyping)
    (Conversion.refl base Adapter.bottomTy)

/-- Expose a possibly closed singleton slot and consume its exact symmetry
result under every carrier elimination scope. -/
noncomputable def symmAt
    {base : Ctx sig} {sourcePath : LambdaPFC.Path n}
    (targetPath : LambdaPFC.Path n)
    (slot : Slot base (.Single sourcePath))
    (answer : Ty sig)
    (consumer : forall {current : Sig} {currentContext : Ctx current},
      (mapping : Rename sig current) ->
      Rename.Typed base currentContext mapping ->
      Result currentContext (.Single sourcePath) (.Single targetPath) ->
      Path.Body currentContext (answer.rename mapping)) :
    Path.Body base answer := by
  cases slot with
  | mk shape interface rep =>
      let exposed := rep.expose interface answer
        (fun mapping typed _ exposedRep => by
          cases exposedRep with
          | absurd bottomValue bottomTyping =>
              let body := consumer mapping typed
                (symmAbsurdResult targetPath bottomValue bottomTyping)
              exact {
                expression := body.expression
                typing := body.typing
              }
          | singleton _ _ referent =>
              let body := consumer mapping typed
                (symmResult targetPath referent)
              exact {
                expression := body.expression
                typing := body.typing
              })
      exact {
        expression := exposed.expression
        typing := exposed.typing
      }

/-- Compile singleton symmetry under the literal path derivation. -/
noncomputable def symm
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide)
    {path sourcePath : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty (environments.proofContext side) path
      (.ty (.Single sourcePath)))
    (answer : Ty sig)
    (consumer : Consumer sourceContext targetContext base answer
      (.Single sourcePath) (.Single path)) : Path.Body base answer :=
  Path.compile typing (environments.environment side) answer
    (fun mapping typed focused view => by
      cases view with
      | proper slot =>
          exact symmAt path slot (answer.rename mapping)
            (fun next nextTyped result => by
              let combined := mapping.comp next
              let combinedTyped := TypedRename.comp typed nextTyped
              let focusedAt := focused.targetRename next nextTyped
              let environmentsAt := focusedEnvironments environments side
                combined combinedTyped focusedAt
              simpa only [Ty.rename_comp] using
                consumer combined combinedTyped environmentsAt result))

/-- The ordinary runtime witness retained by one opened interval. -/
def intervalWitness
    {base : Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (interval : IntervalRep (targetContext := base)
      lowerSource upperSource lower selectedType upper) :
    Conversion.Interval.Witness base lower upper where
  selected := .opaque selectedType
  lowerFunction := interval.lowerFunction
  lowerTyping := interval.lowerTyping
  upperFunction := interval.upperFunction
  upperTyping := interval.upperTyping

noncomputable def selHiAt
    {base : Ctx sig} {path : LambdaPFC.Path n}
    {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (interval : IntervalRep (targetContext := base)
      lowerSource upperSource lower selectedType upper) :
    Result base (.TSel path label) upperSource :=
  let witness := intervalWitness interval
  {
    source := .opaque selectedType
    target := upper
    relation := Relation.ofConversion (interval.selection path label)
      interval.upperRep (Conversion.Interval.upper witness)
  }

/-- Compile selected-type widening through the stored upper function. -/
noncomputable def sel_hi
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty (environments.proofContext side)
      (.sel path label) (.intv lowerSource upperSource))
    (_nonempty : LambdaPFC.Tau.Sub (environments.proofContext side)
      (.ty lowerSource) (.ty upperSource))
    (answer : Ty sig)
    (consumer : Consumer sourceContext targetContext base answer
      (.TSel path label) upperSource) : Path.Body base answer :=
  Path.compile typing (environments.environment side) answer
    (fun mapping typed focused view => by
      cases view with
      | interval interval =>
          exact consumer mapping typed
            (focusedEnvironments environments side mapping typed focused)
            (selHiAt interval))

noncomputable def selLoAt
    {base : Ctx sig} {path : LambdaPFC.Path n}
    {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (interval : IntervalRep (targetContext := base)
      lowerSource upperSource lower selectedType upper) :
    Result base lowerSource (.TSel path label) :=
  let witness := intervalWitness interval
  {
    source := lower
    target := .opaque selectedType
    relation := Relation.ofConversion interval.lowerRep
      (interval.selection path label) (Conversion.Interval.lower witness)
  }

/-- Compile selected-type introduction through the stored lower function. -/
noncomputable def sel_lo
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty (environments.proofContext side)
      (.sel path label) (.intv lowerSource upperSource))
    (_nonempty : LambdaPFC.Tau.Sub (environments.proofContext side)
      (.ty lowerSource) (.ty upperSource))
    (answer : Ty sig)
    (consumer : Consumer sourceContext targetContext base answer
      lowerSource (.TSel path label)) : Path.Body base answer :=
  Path.compile typing (environments.environment side) answer
    (fun mapping typed focused view => by
      cases view with
      | interval interval =>
          exact consumer mapping typed
            (focusedEnvironments environments side mapping typed focused)
            (selLoAt interval))

/-- Exact contravariant-lower/covariant-upper interval relation. -/
structure IntervalRelation
    {base : Ctx sig}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (source : Wf.Interval base sourceLower sourceUpper)
    (target : Wf.Interval base targetLower targetUpper) : Type where
  lower : Relation base targetLower sourceLower target.lower source.lower
  upper : Relation base sourceUpper targetUpper source.upper target.upper

namespace IntervalRelation

noncomputable def refl
    {base : Ctx sig} {lower upper : LambdaPFC.Ty n}
    (interval : Wf.Interval base lower upper) :
    IntervalRelation interval interval where
  lower := Relation.refl interval.lowerRep
  upper := Relation.refl interval.upperRep

noncomputable def mapWitness
    {base : Ctx sig}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {source : Wf.Interval base sourceLower sourceUpper}
    {target : Wf.Interval base targetLower targetUpper}
    (relation : IntervalRelation source target)
    (witness : Conversion.Interval.Witness base source.lower source.upper) :
    Conversion.Interval.Witness base target.lower target.upper :=
  Conversion.Interval.map witness relation.lower.conversion
    relation.upper.conversion

noncomputable def targetRename
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {source : Wf.Interval sourceContext sourceLower sourceUpper}
    {target : Wf.Interval sourceContext targetLower targetUpper}
    (relation : IntervalRelation source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    IntervalRelation (source.targetRename mapping typed)
      (target.targetRename mapping typed) where
  lower := relation.lower.targetRename mapping typed
  upper := relation.upper.targetRename mapping typed

noncomputable def trans
    {base : Ctx sig}
    {sourceLower sourceUpper middleLower middleUpper targetLower targetUpper :
      LambdaPFC.Ty n}
    {source : Wf.Interval base sourceLower sourceUpper}
    {middle : Wf.Interval base middleLower middleUpper}
    {target : Wf.Interval base targetLower targetUpper}
    (first : IntervalRelation source middle)
    (second : IntervalRelation middle target) :
    IntervalRelation source target where
  lower := second.lower.trans first.lower
  upper := first.upper.trans second.upper

end IntervalRelation

/-- Existential endpoint shapes computed by one interval derivation. -/
structure IntervalResult (base : Ctx sig)
    (sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n) :
    Type where
  source : Wf.Interval base sourceLower sourceUpper
  target : Wf.Interval base targetLower targetUpper
  relation : IntervalRelation source target

namespace IntervalResult

noncomputable def refl
    {base : Ctx sig} {lower upper : LambdaPFC.Ty n}
    (interval : Wf.Interval base lower upper) :
    IntervalResult base lower upper lower upper where
  source := interval
  target := interval
  relation := IntervalRelation.refl interval

noncomputable def bounds
    {base : Ctx sig}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {sourceLowerShape sourceUpperShape targetLowerShape targetUpperShape :
      Shape sig}
    (lower : Relation base targetLower sourceLower targetLowerShape
      sourceLowerShape)
    (upper : Relation base sourceUpper targetUpper sourceUpperShape
      targetUpperShape) :
    IntervalResult base sourceLower sourceUpper targetLower targetUpper :=
  let source : Wf.Interval base sourceLower sourceUpper := {
    lower := sourceLowerShape
    upper := sourceUpperShape
    lowerRep := lower.targetRep
    upperRep := upper.sourceRep
  }
  let target : Wf.Interval base targetLower targetUpper := {
    lower := targetLowerShape
    upper := targetUpperShape
    lowerRep := lower.sourceRep
    upperRep := upper.targetRep
  }
  {
    source := source
    target := target
    relation := { lower := lower, upper := upper }
  }

noncomputable def targetRename
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (result : IntervalResult sourceContext sourceLower sourceUpper
      targetLower targetUpper)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    IntervalResult targetContext sourceLower sourceUpper
      targetLower targetUpper where
  source := result.source.targetRename mapping typed
  target := result.target.targetRename mapping typed
  relation := result.relation.targetRename mapping typed

end IntervalResult

end LambdaPToFCo.Direct.Internal.AtomicSubtyping
