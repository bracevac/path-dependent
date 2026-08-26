import LambdaPToFCo.StaticScope

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

structure PathTranslation {sig : Sig} (context : Ctx sig) where
  targetType : Ty sig
  expression : Exp sig
  typing : Exp.HasType context expression targetType

namespace TypedInterfaceSlot

def path {context : Ctx sig} :
    TypedInterfaceSlot context -> PathTranslation context
| .ordinary slot =>
    { targetType := slot.targetType
      expression := slot.interface.value
      typing := slot.typing }
| .exact slot =>
    { targetType := slot.rawType
      expression := slot.interface.raw
      typing := slot.rawTyping }

end TypedInterfaceSlot

namespace TypedExactSlot

def payloadPath {context : Ctx sig}
    (slot : TypedExactSlot context) : PathTranslation context where
  targetType := slot.payloadType
  expression := slot.interface.payload
  typing := slot.payloadTyping

end TypedExactSlot

/-- Derivation-directed translation of a precise source path. -/
noncomputable def translatePath
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (typing : Fragment.PathTy sourceContext path sourceType) :
    PathTranslation targetContext :=
  match typing with
  | @Fragment.PathTy.var _ _ x => (scope.lookup x).path
  | .exactFst member => (scope.lookupMember member).payloadPath

/-- Derivation-directed translation of a supported source type. -/
noncomputable def translateType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (wf : Fragment.Wf sourceContext sourceType) : Ty sig :=
  match wf with
  | .top => .top
  | .singleton pathTyping => (translatePath scope pathTyping).targetType
  | .selection member _ => (scope.lookupMember member).interface.witness
  | @Fragment.Wf.memberPackage _ _ first _ _ _ lowerWf upperWf _ =>
      Ty.member (translateType scope lowerWf) (translateType scope upperWf)
        (payloadFamily (scope.lookup first).path.targetType)
  | .arrow domainWf codomainWf =>
      .arrow (translateType scope domainWf) (translateType scope codomainWf)

end StaticTranslation
end LambdaPToFCo
