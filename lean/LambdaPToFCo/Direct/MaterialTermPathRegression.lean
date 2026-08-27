import LambdaPToFCo.Direct.MaterialTermPath
import LambdaPToFCo.Direct.CompilerWf

/-!
# Package-aware raw path regressions

The receiver below is a proper pair assembled from explicit Top payloads,
not from an interface canonicalized in an elimination scope.  Its member
projection must carry that actual nested pair package through singleton
introduction and back to the root.
-/

namespace LambdaPToFCo.Direct.MaterialTermPathRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf
open LambdaPToFCo.Direct.Internal.MaterialTermPath

private abbrev Label : LambdaPFC.Name := 0

private abbrev PairSource : LambdaPFC.Ty 0 :=
  .Pair .Top Label (.ty .Top)

private abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc PairSource

private abbrev ReceiverPath : LambdaPFC.Path 1 := .var 0

private abbrev MemberPath : LambdaPFC.Path 1 := .sel ReceiverPath Label

private abbrev TargetContext : Ctx [] := Ctx.empty

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType
    (context : Ctx sig) :
    Exp.HasType context (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface
    (context : Ctx sig) :
    Shape.Interface context (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType context)

private def first : Shape [] := .stable (Top.plan [])

private def member : Shape first.scope :=
  .stable (Top.plan first.scope)

private noncomputable def memberArguments :
    Telescope.Args TargetContext
      (member.binders.subst
        (topInterface TargetContext).substitution) := by
  have equal :
      member.binders.subst (topInterface TargetContext).substitution =
        (.stable (Top.plan []) : Shape []).binders := by
    change ((Top.plan first.scope).subst
      (topInterface TargetContext).substitution).telescope =
        (Top.plan []).telescope
    exact congrArg Package.Plan.telescope
      (Top.plan_subst (topInterface TargetContext).substitution)
  exact equal.symm ▸ (topInterface TargetContext).arguments

/-- The receiver contains two caller-supplied Top packages inside the
dependent pair representation package. -/
private noncomputable def receiverInterface :
    Shape.Interface TargetContext
      (.stable (Pair.Proper.plan first member)) where
  arguments := Pair.Proper.exactArguments first member
    (topInterface TargetContext).arguments memberArguments

private def receiverRep :
    Rep TargetContext PairSource
      (.stable (Pair.Proper.plan first member)) :=
  .properPair (.top _) (.top _)

private noncomputable def receiver :
    Slot TargetContext (SourceContext.lookup 0) where
  shape := .stable (Pair.Proper.plan first member)
  interface := receiverInterface
  rep := receiverRep.sourceRename LambdaPFC.FinFun.weaken

private noncomputable def environment :
    Env SourceContext TargetContext where
  lookup index := Fin.cases receiver (fun older => Fin.elim0 older) index

private def receiverTyping :
    LambdaPFC.Path.Ty SourceContext ReceiverPath
      (.ty (SourceContext.lookup 0)) :=
  .var

private def memberTyping :
    LambdaPFC.Path.Ty SourceContext MemberPath (.ty .Top) := by
  simpa only [LambdaPFC.Tau.open] using receiverTyping.sel_r

/-- The concrete receiver package is definitionally the exact proper-pair
package built from the two explicit payload interfaces. -/
theorem receiver_uses_explicit_payloads :
    receiver.interface.package =
      Pair.Proper.exactPackage first member
        (topInterface TargetContext).arguments memberArguments :=
  rfl

/-- The selected member is reclosed at the root as a raw exact Slot. -/
noncomputable def projectedMember :
    Slot TargetContext (.Top : LambdaPFC.Ty 1) :=
  materialize memberTyping environment

/-- The member projection traversed the pair representation and therefore
returns through a faithful opaque carrier rather than leaking its scope. -/
theorem projectedMember_isClosed :
    match projectedMember.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

/-- Singleton introduction consumes the selected member's actual package
before the same focus history recloses it at the root. -/
noncomputable def projectedMemberSingleton :
    Slot TargetContext (.Single MemberPath) :=
  materializeSingleton memberTyping environment

private noncomputable def singletonFromActualSelection :
    Slot TargetContext (.Single MemberPath) :=
  compileWith memberTyping environment (fun focus _ view => by
    cases view with
    | proper selected =>
        let singleton : Slot _ (.Single MemberPath) := {
          shape := .stable (Single.plan selected.shape.inputTy)
          interface := {
            arguments := Single.exactArguments selected.shape.inputTy
              selected.interface.package
              selected.interface.package_hasType
          }
          rep := .singleton _ MemberPath
            selected.shape.inputTy
        }
        exact focus.closeSlot singleton)

/-- This equation pins the runtime payload origin: no canonical receiver or
selected package can be substituted for the precise package returned by the
path view. -/
theorem singleton_preserves_actual_selected_package :
    projectedMemberSingleton = singletonFromActualSelection :=
  rfl

noncomputable def projectedMemberSingleton_hasType :
    Exp.HasType TargetContext
      projectedMemberSingleton.interface.package
      projectedMemberSingleton.shape.inputTy :=
  projectedMemberSingleton.interface.package_hasType

/-! ## Generic material exposure -/

/-- The generic exposure runner opens the closed projected Top and then
recloses the exact closure-free Slot through the retained actual packages. -/
noncomputable def exposedRoundTrip :
    Slot TargetContext (.Top : LambdaPFC.Ty 1) :=
  exposeSlot projectedMember (fun focus interface exposed =>
    focus.closeSlot {
      shape := _
      interface := interface
      rep := exposed.toRep
    })

noncomputable def exposedRoundTrip_hasType :
    Exp.HasType TargetContext exposedRoundTrip.interface.package
      exposedRoundTrip.shape.inputTy :=
  exposedRoundTrip.interface.package_hasType

/-! ## Wf/term path coherence -/

private def singletonWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.Single MemberPath)) :=
  .path memberTyping

noncomputable def compiledWfSingleton :
    Proper TargetContext (.Single MemberPath) := by
  cases LambdaPToFCo.Direct.Internal.CompilerWf.compile
      singletonWf environment with
  | proper result => exact result

/-- Type-side Wf compilation and runtime singleton materialization close the
same precise path focus to exactly the same root Shape. -/
theorem path_shape_coherent :
    compiledWfSingleton.shape = projectedMemberSingleton.shape :=
  rfl

end LambdaPToFCo.Direct.MaterialTermPathRegression
