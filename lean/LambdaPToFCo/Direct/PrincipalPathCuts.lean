import LambdaPToFCo.Direct.AtomicSubtyping
import LambdaPToFCo.Direct.ContextRelation

/-!
# Direct principal path cuts

Two atomic transitivity patterns used by dependent records must be compiled
before either path rule exports an existential endpoint Shape.

For `widen ; sel_lo`, the lower endpoint exposed by the second rule fixes the
representation demanded of the first rule.  The resulting ordinary target
function opens that exact singleton and immediately invokes the interval's
stored lower function.  It never constructs an independently shaped middle.

For `sel_hi ; sel_lo` on the same equal-bounds path, the interval is followed
once and its exact selected representation is retained by reflexivity.

These functions are internal seams for the demand-directed term cut.  In
particular, `widenSelectionLow` does not adapt an arbitrary synthesized
singleton Slot: the future term checker must compile the literal source
premise against the exact `relation.sourceRep` while the continuation is
live.  Distinct source paths that merely alias require a structural paired
path fusion; they cannot be reconstructed from two raw selection Reps.
-/

namespace LambdaPToFCo.Direct.Internal.PrincipalPathCuts

noncomputable section

open SystemFCo
open Representation
open ContextRelation

/-- Direct target relation at one already-open lower-selection interval. -/
private noncomputable def widenSelectionLowAt
    {base : Ctx sig}
    {path receiver : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {middle upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (interval : IntervalRep (targetContext := base)
      middle upperSource lower selectedType upper) :
    Relation base (.Single path) (.TSel receiver label)
      (.stable (Single.plan lower.inputTy)) (.opaque selectedType) :=
  let witness := AtomicSubtyping.intervalWitness interval
  Relation.ofConversion
    (.singleton base path lower.inputTy)
    (interval.selection receiver label)
    ((Conversion.Singleton.unwrap base lower.inputTy).compose
      (Conversion.Interval.lower witness))

/-- Fuse the literal principal cut `widen ; sel_lo`.

Only the selection path is followed here.  Its exact lower representation
determines the source singleton demand; source-term checking happens later,
inside the supplied natural continuation. -/
noncomputable def widenSelectionLow
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    {path receiver : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {middle upperSource : LambdaPFC.Ty n}
    (_widenTyping : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) path (.ty middle))
    (selectionTyping : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) (.sel receiver label)
      (.intv middle upperSource))
    (_nonempty : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty middle) (.ty upperSource))
    (answer : Ty sig)
    (consumer : forall {current : Sig} {currentContext : Ctx current},
      (mapping : Rename sig current) ->
      Rename.Typed base currentContext mapping ->
      {source target : Shape current} ->
      Relation currentContext (.Single path) (.TSel receiver label)
        source target ->
      Path.Body currentContext (answer.rename mapping)) :
    Path.Body base answer :=
  Path.compile selectionTyping (scope.endpointEnvs.environment side) answer
    (fun mapping typed _focused view => by
      cases view with
      | interval interval =>
          exact consumer mapping typed
            (widenSelectionLowAt
              (path := path) (receiver := receiver) (label := label)
              interval))

/-- Fuse `sel_hi h ; sel_lo h` for one literal equal-bounds interval focus.

The selected hidden type is opened once.  Since the overall source and target
types are the same selection, the exact selected representation is preserved
by the ordinary reflexive relation. -/
noncomputable def selectionHighLowSame
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    {receiver : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {middle : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) (.sel receiver label)
      (.intv middle middle))
    (_firstNonempty _secondNonempty : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty middle) (.ty middle))
    (answer : Ty sig)
    (consumer : forall {current : Sig} {currentContext : Ctx current},
      (mapping : Rename sig current) ->
      Rename.Typed base currentContext mapping ->
      {source target : Shape current} ->
      Relation currentContext (.TSel receiver label)
        (.TSel receiver label) source target ->
      Path.Body currentContext (answer.rename mapping)) :
    Path.Body base answer :=
  Path.compile typing (scope.endpointEnvs.environment side) answer
    (fun mapping typed _focused view => by
      cases view with
      | interval interval =>
          exact consumer mapping typed
            (Relation.refl (interval.selection receiver label)))

end

end LambdaPToFCo.Direct.Internal.PrincipalPathCuts
