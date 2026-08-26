import LambdaPToFCo.OperationalReturnPathCapability

/-!
# Automatic existing-location return

This high-level wrapper combines the source-only result capability retained
by the execution zipper with the resolved path's source/store head theorems.
All target behavior, suffix reduction, and resume construction remain owned
by `ReturnExecution.ofImage`.
-/

namespace LambdaPToFCo
namespace OperationalAutomaticReturn

open SystemFCo
open OperationalApplicationSpine
open OperationalExpectedResult
open OperationalMachineImage
open OperationalStateImage
open OperationalStateImage.StateImage
open OperationalReturnPathCapability

/-- A same-closure return uses the let's retained bound policy.  Abstracting
both source closures before eliminating equality avoids dependent equations
involving the concrete captured frame. -/
private noncomputable def returnBoundShape_of_policy
    {current : Nat}
    {left right : SourceClosure current}
    {path : LambdaPFC.Path left.original.arity}
    (term_eq : left.original.term = .path path)
    (policy : OperationalAdmissibility.LetBoundPolicy right.original.typing)
    (closure_eq : left = right) :
    NonCanonicalResultShape right.original.resultType := by
  cases closure_eq
  cases policy with
  | directValue evidence =>
      have pathValue : LambdaPFC.Tm.IsValue (.path path) :=
        term_eq ▸ evidence.isValue
      have impossible : False := by cases pathValue
      exact impossible.elim
  | nonCanonical shape => exact shape

private noncomputable def returnPathCapability_of_policy
    {current : Nat}
    {left right : SourceClosure current}
    {path : LambdaPFC.Path left.original.arity}
    {typing : Fragment.HasType left.original.context (.path path)
      left.original.resultType}
    (term_eq : left.original.term = .path path)
    (policy : OperationalAdmissibility.LetBoundPolicy right.original.typing)
    (closure_eq : left = right) :
    ReturnPathCapability typing right.original.resultType :=
  .nonCanonical
    (returnBoundShape_of_policy term_eq policy closure_eq)

namespace ActiveResultCapability

/-- Every reachable existing-location return binds a noncanonical source
type.  A same-closure frame obtains this from its retained let-bound policy;
the other active-head case stores it directly. -/
noncomputable def returnBoundShape
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentOrigin : Exp []} {parentBoundary : ResultBoundary.{0}}
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary}
    {origin : CurrentOrigin sourceStore}
    (active : OperationalStateImage.ActiveResultCapability origin
      (.cons frame saved tail))
    {path : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    (resolved : ResolvedPathView origin path location) :
    NonCanonicalResultShape frame.image.holeType := by
  rcases active with ⟨parentSourceOrigin, parent, parent_eq, head⟩
  cases head with
  | same closure_eq =>
      exact returnBoundShape_of_policy resolved.term_eq frame.boundPolicy
        closure_eq
  | nonCanonical shape => exact shape

/-- Select the source-head capability required by the active saved frame.
An exact source-closure match reuses the resolved path's repaired
admissibility evidence; a noncanonical frame hole has no physical-head
demand. -/
noncomputable def returnPathCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentOrigin : Exp []} {parentBoundary : ResultBoundary.{0}}
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary}
    {origin : CurrentOrigin sourceStore}
    (active : OperationalStateImage.ActiveResultCapability origin
      (.cons frame saved tail))
    {path : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    (resolved : ResolvedPathView origin path location) :
    ReturnPathCapability resolved.typing frame.image.holeType := by
  rcases active with ⟨parentSourceOrigin, parent, parent_eq, head⟩
  cases head with
  | same closure_eq =>
      exact returnPathCapability_of_policy resolved.term_eq
        frame.boundPolicy closure_eq
  | nonCanonical shape =>
      exact .nonCanonical shape

end ActiveResultCapability

namespace ReturnExecution

/-- Construct complete return execution from the source capability already
indexed by the current execution zipper.  No target or store premise remains
beyond the fields of the existing machine image. -/
noncomputable def automatic
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {parentOrigin : Exp []} {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    {tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary}
    {origin : CurrentOrigin sourceStore}
    {sourcePath : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    {resolved : ResolvedPathView origin sourcePath location}
    {running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (active : OperationalStateImage.ActiveResultCapability origin
      (.cons frame saved tail)) :
    OperationalStateImage.StateImage.ReturnExecution frame origin sourcePath
      location resolved running :=
  let capability :=
    OperationalAutomaticReturn.ActiveResultCapability.returnPathCapability
      active resolved
  OperationalStateImage.StateImage.ReturnExecution.ofImage saved
    (OperationalAutomaticReturn.ActiveResultCapability.returnBoundShape
      active resolved)
    (OperationalReturnPathCapability.ResolvedPathView.frameMemberCell
      frame resolved capability)
    (OperationalReturnPathCapability.ResolvedPathView.frameFunctionCell
      frame resolved capability)

end ReturnExecution

end OperationalAutomaticReturn
end LambdaPToFCo
