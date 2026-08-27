import LambdaPToFCo.Direct.Relation

/-!
# Ordinary conversions for unreachable raw representations

An unreachable representation retains one actual term of impredicative
Bottom.  These target-only helpers are the two ways a subtyping checker can
cross that boundary: eliminate a source Bottom to the demanded target input,
or ignore an arbitrary source input and return the exact Bottom retained by
an unreachable target.  Both are ordinary `SystemFCo.Exp` lambdas packaged in
the existing sealed `Conversion`; no result hierarchy or target extension is
introduced.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open Representation

namespace Conversion

private noncomputable def constant
    {base : Ctx sig}
    (source target : Ty sig)
    (value : Exp sig)
    (typing : Exp.HasType base value target) :
    Conversion base source target :=
  Conversion.ofFunction
    (Adapter.ofBody source (value.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken] using typing.weaken (.var source)))

/-- Eliminate one retained Bottom term to an arbitrary represented target
input type. -/
noncomputable def fromAbsurd
    {base : Ctx sig}
    (bottomValue : Exp sig)
    (bottomTyping : Exp.HasType base bottomValue Adapter.bottomTy)
    (target : Shape sig) :
    Conversion base Adapter.bottomTy target.inputTy :=
  constant Adapter.bottomTy target.inputTy
    (Adapter.eliminateBottom bottomValue target.inputTy)
    (Adapter.eliminateBottom_hasType bottomTyping)

/-- Ignore an arbitrary represented source input and return the exact Bottom
term retained by an unreachable target. -/
noncomputable def toAbsurd
    {base : Ctx sig}
    (source : Shape sig)
    (bottomValue : Exp sig)
    (bottomTyping : Exp.HasType base bottomValue Adapter.bottomTy) :
    Conversion base source.inputTy Adapter.bottomTy :=
  constant source.inputTy Adapter.bottomTy bottomValue bottomTyping

end Conversion

namespace Relation

/-- A source-unreachable relation to any exact represented target. -/
noncomputable def fromAbsurd
    {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    {target : Shape sig}
    (bottomValue : Exp sig)
    (bottomTyping : Exp.HasType base bottomValue Adapter.bottomTy)
    (targetRep : Rep base targetType target) :
    Relation base sourceType targetType
      (.opaque Adapter.bottomTy) target :=
  Relation.ofConversion
    (.absurd bottomValue bottomTyping) targetRep
    (Conversion.fromAbsurd bottomValue bottomTyping target)

/-- A relation from any exact represented source to an unreachable target. -/
noncomputable def toAbsurd
    {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    {source : Shape sig}
    (sourceRep : Rep base sourceType source)
    (bottomValue : Exp sig)
    (bottomTyping : Exp.HasType base bottomValue Adapter.bottomTy) :
    Relation base sourceType targetType source
      (.opaque Adapter.bottomTy) :=
  Relation.ofConversion sourceRep
    (.absurd bottomValue bottomTyping)
    (Conversion.toAbsurd source bottomValue bottomTyping)

end Relation

end LambdaPToFCo.Direct.Internal
