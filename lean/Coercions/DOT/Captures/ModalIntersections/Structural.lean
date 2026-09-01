import Coercions.DOT.Captures.ModalIntersections.Syntax

/-!
# Structural laws for modal captured intersections
-/

namespace DOTCapture.ModalIntersections

namespace Path

@[simp]
theorem rename_id {scope : Sig} (path : Path scope) :
    path.rename DOTCapture.BinderOnly.Rename.id = path := by
  cases path
  rfl

@[simp]
theorem rename_comp {first second third : Sig} (path : Path first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (path.rename rho₁).rename rho₂ = path.rename (rho₁.comp rho₂) := by
  cases path
  rfl

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (path : Path source) (rho : Rename source target) :
    (path.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (path.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Path

namespace ClassifierRef

@[simp]
theorem rename_id {scope : Sig} (reference : ClassifierRef scope) :
    reference.rename DOTCapture.BinderOnly.Rename.id = reference := by
  cases reference <;> simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (reference : ClassifierRef first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (reference.rename rho₁).rename rho₂ =
      reference.rename (rho₁.comp rho₂) := by
  cases reference <;> simp [rename]

end ClassifierRef

namespace ClassifierExpr

@[simp]
theorem rename_id {scope : Sig} (classifier : ClassifierExpr scope) :
    classifier.rename DOTCapture.BinderOnly.Rename.id = classifier := by
  cases classifier <;> simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (classifier : ClassifierExpr first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (classifier.rename rho₁).rename rho₂ =
      classifier.rename (rho₁.comp rho₂) := by
  cases classifier <;> simp [rename]

end ClassifierExpr

namespace StaticRef

@[simp]
theorem rename_id {sort : StaticSort} {scope : Sig}
  (reference : StaticRef sort scope) :
    reference.rename DOTCapture.BinderOnly.Rename.id = reference := by
  cases reference <;> simp only [rename, Path.rename_id,
    DOTCapture.BinderOnly.Rename.id_var]

@[simp]
theorem rename_comp {sort : StaticSort} {first second third : Sig}
    (reference : StaticRef sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (reference.rename rho₁).rename rho₂ =
      reference.rename (rho₁.comp rho₂) := by
  cases reference <;> simp only [rename, Path.rename_comp,
    DOTCapture.BinderOnly.Rename.comp_var]

@[simp]
theorem weaken_rename {sort : StaticSort} {source target : Sig}
    {kind : BinderKind} (reference : StaticRef sort source)
    (rho : Rename source target) :
    (reference.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (reference.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end StaticRef

mutual

@[simp]
def Capture.rename_id {scope : Sig} (capture : Capture scope) :
    capture.rename DOTCapture.BinderOnly.Rename.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_id left,
        Capture.rename_id right]
  | .project capture classifier => by
      simp only [Capture.rename, Capture.rename_id capture,
        ClassifierExpr.rename_id classifier]
  | .readOnly captures => by
      simp only [Capture.rename, Capture.rename_id captures]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_id path]
  | .ref reference => by
      simp only [Capture.rename, StaticRef.rename_id reference]

@[simp]
def SeparationContext.rename_id {scope : Sig} {count : Nat}
    (context : SeparationContext count scope) :
    context.rename DOTCapture.BinderOnly.Rename.id = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.rename,
        SeparationContext.rename_id rest, Capture.rename_id capture]

@[simp]
def ModeContext.rename_id {scope : Sig} {modes : List CaptureMode}
    (context : ModeContext modes scope) :
    context.rename DOTCapture.BinderOnly.Rename.id = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.rename, ModeContext.rename_id rest,
        Capture.rename_id capture]

@[simp]
def ModalRequirements.rename_id {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope) :
    requirements.rename DOTCapture.BinderOnly.Rename.id = requirements :=
  match requirements with
  | .mk separation mode => by
      simp only [ModalRequirements.rename,
        SeparationContext.rename_id separation, ModeContext.rename_id mode]

@[simp]
def Ty.rename_id {scope : Sig} (type : Ty scope) :
    type.rename DOTCapture.BinderOnly.Rename.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [Ty.rename, StaticRef.rename_id reference]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_id domain, Ty.rename_id codomain]
  | .objectArrow parameter resultTemplate => by
      simp only [Ty.rename, ObjectType.rename_id parameter,
        Ty.rename_id resultTemplate]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_id captures, Ty.rename_id shape]
  | .forallI interval body => by
      simp only [Ty.rename, Interval.rename_id interval,
        DOTCapture.BinderOnly.Rename.lift_id, Ty.rename_id body]
  | .existsI interval body => by
      simp only [Ty.rename, Interval.rename_id interval,
        DOTCapture.BinderOnly.Rename.lift_id, Ty.rename_id body]
  | .modal requirements body => by
      simp only [Ty.rename, ModalRequirements.rename_id requirements,
        Ty.rename_id body]
  | .object object => by
      simp only [Ty.rename, ObjectType.rename_id object]

@[simp]
def StaticExpr.rename_id {sort : StaticSort} {scope : Sig}
    (expression : StaticExpr sort scope) :
    expression.rename DOTCapture.BinderOnly.Rename.id = expression :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_id type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_id capture]

@[simp]
def Endpoint.rename_id {sort : StaticSort} {scope : Sig}
    (endpoint : Endpoint sort scope) :
    endpoint.rename DOTCapture.BinderOnly.Rename.id = endpoint :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.rename, StaticExpr.rename_id expression]

@[simp]
def Interval.rename_id {sort : StaticSort} {scope : Sig}
    (interval : Interval sort scope) :
    interval.rename DOTCapture.BinderOnly.Rename.id = interval :=
  match interval with
  | .bounds lower upper => by
      simp only [Interval.rename, Endpoint.rename_id lower,
        Endpoint.rename_id upper]

@[simp]
def Interface.rename_id {scope : Sig} (interface : Interface scope) :
    interface.rename DOTCapture.BinderOnly.Rename.id = interface :=
  match interface with
  | .empty => rfl
  | .typeMember _ lower upper => by
      simp only [Interface.rename, Ty.rename_id lower, Ty.rename_id upper]
  | .captureMember _ lower upper => by
      simp only [Interface.rename, Capture.rename_id lower,
        Capture.rename_id upper]
  | .classifierMember _ lower upper => by
      simp only [Interface.rename, ClassifierExpr.rename_id lower,
        ClassifierExpr.rename_id upper]
  | .classifierDisjoint left right => by
      simp only [Interface.rename, ClassifierExpr.rename_id left,
        ClassifierExpr.rename_id right]
  | .captureHasKind capture classifier => by
      simp only [Interface.rename, Capture.rename_id capture,
        ClassifierExpr.rename_id classifier]
  | .inter left right => by
      simp only [Interface.rename, Interface.rename_id left,
        Interface.rename_id right]

@[simp]
def ObjectType.rename_id {scope : Sig} (object : ObjectType scope) :
    object.rename DOTCapture.BinderOnly.Rename.id = object :=
  match object with
  | .mk interface representation outerCapture => by
      simp only [ObjectType.rename, Interface.rename_id interface,
        Ty.rename_id representation, Capture.rename_id outerCapture]
  | .mkContracted interface representation outerCapture packageCapture => by
      simp only [ObjectType.rename, Interface.rename_id interface,
        Ty.rename_id representation, Capture.rename_id outerCapture,
        Capture.rename_id packageCapture]

end

mutual

@[simp]
def Capture.rename_comp {first second third : Sig}
    (capture : Capture first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (capture.rename rho₁).rename rho₂ =
      capture.rename (rho₁.comp rho₂) :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_comp left,
        Capture.rename_comp right]
  | .project capture classifier => by
      simp only [Capture.rename, Capture.rename_comp capture,
        ClassifierExpr.rename_comp classifier]
  | .readOnly captures => by
      simp only [Capture.rename, Capture.rename_comp captures]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_comp path]
  | .ref reference => by
      simp only [Capture.rename, StaticRef.rename_comp reference]

@[simp]
def SeparationContext.rename_comp {count : Nat}
    {first second third : Sig} (context : SeparationContext count first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (context.rename rho₁).rename rho₂ =
      context.rename (rho₁.comp rho₂) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.rename,
        SeparationContext.rename_comp rest, Capture.rename_comp capture]

@[simp]
def ModeContext.rename_comp {modes : List CaptureMode}
    {first second third : Sig} (context : ModeContext modes first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (context.rename rho₁).rename rho₂ =
      context.rename (rho₁.comp rho₂) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.rename, ModeContext.rename_comp rest,
        Capture.rename_comp capture]

@[simp]
def ModalRequirements.rename_comp {separationCount : Nat}
    {modes : List CaptureMode} {first second third : Sig}
    (requirements : ModalRequirements separationCount modes first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (requirements.rename rho₁).rename rho₂ =
      requirements.rename (rho₁.comp rho₂) :=
  match requirements with
  | .mk separation mode => by
      simp only [ModalRequirements.rename,
        SeparationContext.rename_comp separation,
        ModeContext.rename_comp mode]

@[simp]
def Ty.rename_comp {first second third : Sig} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ = type.rename (rho₁.comp rho₂) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [Ty.rename, StaticRef.rename_comp reference]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_comp domain, Ty.rename_comp codomain]
  | .objectArrow parameter resultTemplate => by
      simp only [Ty.rename, ObjectType.rename_comp parameter,
        Ty.rename_comp resultTemplate]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_comp captures,
        Ty.rename_comp shape]
  | .forallI interval body => by
      simp only [Ty.rename, Interval.rename_comp interval,
        Ty.rename_comp body, DOTCapture.BinderOnly.Rename.lift_comp]
  | .existsI interval body => by
      simp only [Ty.rename, Interval.rename_comp interval,
        Ty.rename_comp body, DOTCapture.BinderOnly.Rename.lift_comp]
  | .modal requirements body => by
      simp only [Ty.rename, ModalRequirements.rename_comp requirements,
        Ty.rename_comp body]
  | .object object => by
      simp only [Ty.rename, ObjectType.rename_comp object]

@[simp]
def StaticExpr.rename_comp {sort : StaticSort} {first second third : Sig}
    (expression : StaticExpr sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (expression.rename rho₁).rename rho₂ =
      expression.rename (rho₁.comp rho₂) :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_comp type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_comp capture]

@[simp]
def Endpoint.rename_comp {sort : StaticSort} {first second third : Sig}
    (endpoint : Endpoint sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (endpoint.rename rho₁).rename rho₂ =
      endpoint.rename (rho₁.comp rho₂) :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.rename, StaticExpr.rename_comp expression]

@[simp]
def Interval.rename_comp {sort : StaticSort} {first second third : Sig}
    (interval : Interval sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (interval.rename rho₁).rename rho₂ =
      interval.rename (rho₁.comp rho₂) :=
  match interval with
  | .bounds lower upper => by
      simp only [Interval.rename, Endpoint.rename_comp lower,
        Endpoint.rename_comp upper]

@[simp]
def Interface.rename_comp {first second third : Sig}
    (interface : Interface first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (interface.rename rho₁).rename rho₂ =
      interface.rename (rho₁.comp rho₂) :=
  match interface with
  | .empty => rfl
  | .typeMember _ lower upper => by
      simp only [Interface.rename, Ty.rename_comp lower,
        Ty.rename_comp upper]
  | .captureMember _ lower upper => by
      simp only [Interface.rename, Capture.rename_comp lower,
        Capture.rename_comp upper]
  | .classifierMember _ lower upper => by
      simp only [Interface.rename, ClassifierExpr.rename_comp lower,
        ClassifierExpr.rename_comp upper]
  | .classifierDisjoint left right => by
      simp only [Interface.rename, ClassifierExpr.rename_comp left,
        ClassifierExpr.rename_comp right]
  | .captureHasKind capture classifier => by
      simp only [Interface.rename, Capture.rename_comp capture,
        ClassifierExpr.rename_comp classifier]
  | .inter left right => by
      simp only [Interface.rename, Interface.rename_comp left,
        Interface.rename_comp right]

@[simp]
def ObjectType.rename_comp {first second third : Sig}
    (object : ObjectType first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (object.rename rho₁).rename rho₂ =
      object.rename (rho₁.comp rho₂) :=
  match object with
  | .mk interface representation outerCapture => by
      simp only [ObjectType.rename, Interface.rename_comp interface,
        Ty.rename_comp representation, Capture.rename_comp outerCapture]
  | .mkContracted interface representation outerCapture packageCapture => by
      simp only [ObjectType.rename, Interface.rename_comp interface,
        Ty.rename_comp representation, Capture.rename_comp outerCapture,
        Capture.rename_comp packageCapture]

end

namespace Capture

@[simp]
theorem seq_rename {source target : Sig}
    (immediate continuation : Capture source) (rho : Rename source target) :
    (immediate.seq continuation).rename rho =
      (immediate.rename rho).seq (continuation.rename rho) := by
  cases immediate <;> rfl

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (capture : Capture source) (rho : Rename source target) :
    (capture.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (capture.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Capture

namespace SeparationContext

@[simp]
theorem weaken_rename {source target : Sig} {count : Nat}
    {kind : BinderKind} (context : SeparationContext count source)
    (rho : Rename source target) :
    (context.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (context.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end SeparationContext

namespace ModeContext

@[simp]
theorem weaken_rename {source target : Sig} {modes : List CaptureMode}
    {kind : BinderKind} (context : ModeContext modes source)
    (rho : Rename source target) :
    (context.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (context.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end ModeContext

namespace ModalRequirements

@[simp]
theorem weaken_rename {source target : Sig} {separationCount : Nat}
    {modes : List CaptureMode} {kind : BinderKind}
    (requirements : ModalRequirements separationCount modes source)
    (rho : Rename source target) :
    (requirements.weaken (kind := kind)).rename
        (rho.lift (kind := kind)) =
      (requirements.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end ModalRequirements

namespace Ty

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (type : Ty source) (rho : Rename source target) :
    (type.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (type.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

@[simp]
theorem outerCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).outerCapture = type.outerCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem stripCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).stripCapture = type.stripCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem precise_rename {source target : Sig} (type : Ty source)
    (path : Path source) (rho : Rename source target) :
    (type.precise path).rename rho =
      (type.rename rho).precise (path.rename rho) := by
  cases type <;> rfl

end Ty

namespace StaticExpr

@[simp]
theorem weaken_rename {sort : StaticSort} {source target : Sig}
    {kind : BinderKind} (expression : StaticExpr sort source)
    (rho : Rename source target) :
    (expression.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (expression.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end StaticExpr

namespace Endpoint

@[simp]
theorem weaken_rename {sort : StaticSort} {source target : Sig}
    {kind : BinderKind} (endpoint : Endpoint sort source)
    (rho : Rename source target) :
    (endpoint.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (endpoint.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Endpoint

namespace Interval

@[simp]
theorem weaken_rename {sort : StaticSort} {source target : Sig}
    {kind : BinderKind} (interval : Interval sort source)
    (rho : Rename source target) :
    (interval.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (interval.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Interval

namespace Interface

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (interface : Interface source) (rho : Rename source target) :
    (interface.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (interface.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Interface

namespace ObjectType

@[simp]
theorem formedType_rename {source target : Sig} (object : ObjectType source)
    (rho : Rename source target) :
    (object.rename rho).formedType = object.formedType.rename rho := by
  cases object <;> rfl

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (object : ObjectType source) (rho : Rename source target) :
    (object.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (object.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end ObjectType

end DOTCapture.ModalIntersections
