import Coercions.DOT.TraceablePaths.Source.Typing
import Coercions.Translation.RecursiveObjects.MemberLayout

/-!
# Shallow Scala-like surface for the compiler case study

The compiler case study does not introduce another source calculus or another
source type checker.  The declarations below are only names and smart
constructors for the existing `DotFCR` recursive-object syntax and `DotFCRP`
traceable-path syntax.

A case-study program consists of one closed recursive type-member object and
two stable paths selecting the same public member through a finite transparent
alias store.  The proof-directed front end in `Certificate` supplies the
existing source validity, path-resolution, and bridge certificates.
-/

namespace DotToFCsub.CompilerCaseStudy.Surface

open DotFC

abbrev Name := DotFCRP.Source.Name
abbrev Path := DotFCRP.Source.Path
abbrev AliasStore := DotFCRP.Source.AliasStore
abbrev PathTy := DotFCRP.Source.Ty
abbrev PathTm := DotFCRP.Source.Tm
abbrev RecursiveTy := DotFCR.Source.Ty
abbrev RecursiveTm := DotFCR.Source.Tm
abbrev TypeDef := DotFCR.Source.TypeDef

/-! ## Scala-like smart constructors -/

/-- An abstract type-member refinement `{ type A >: lower <: upper }`. -/
def abstractMember {scope : Sig} (label : Name)
    (lower upper : PathTy scope) : PathTy scope :=
  .member label lower upper

/-- An exact type-member refinement `{ type A = witness }`. -/
def exactMember {scope : Sig} (label : Name)
    (witness : PathTy scope) : PathTy scope :=
  .exact label witness

/-- Intersection of two object refinements. -/
def intersection {scope : Sig} (left right : PathTy scope) : PathTy scope :=
  .inter left right

/-- A dependent method type `(x : domain) => codomain`. -/
def dependentMethod {scope : Sig} (domain : PathTy scope)
    (codomain : PathTy (scope ▹ .term)) : PathTy scope :=
  .all domain codomain

/-- A stable member selection `path.A`. -/
def selection {scope : Sig} (path : Path scope) (label : Name) : PathTy scope :=
  .sel path label

/-- A singleton path type `path.type`. -/
def singleton {scope : Sig} (path : Path scope) : PathTy scope :=
  .singleton path

/-- Recursive self type `mu(self => body)`. -/
def recursive {scope : Sig} (body : PathTy (scope ▹ .term)) : PathTy scope :=
  .mu body

/-- One exact recursive type-member definition. -/
def recursiveTypeMember (label : Name)
    (witness : RecursiveTy DotToFCsub.RecursiveObjects.ClosedSelfScope) :
    TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope :=
  ⟨label, witness⟩

/-! ## Proof-free surface program data -/

/-- The deliberately small compiler case-study compilation unit.

`definitions` is the closed recursive object from RecursiveObjects.  `aliases`, `leftPath`,
and `rightPath` are ordinary path-alias data.  No typing or translation proof
is stored here. -/
structure Program where
  definitions : List (TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope)
  pathScope : Sig
  aliases : AliasStore pathScope
  leftPath : Path pathScope
  rightPath : Path pathScope
  selectedLabel : Name

namespace Program

/-- The existing recursive-object source term represented by a surface program. -/
def object (program : Program) : RecursiveTm [] :=
  .recObj program.definitions

/-- Its exact recursive self type.  `TypeDefs.exact` forms the intersection
of all exact member refinements without adding a new surface type language. -/
def objectType (program : Program) : RecursiveTy [] :=
  .mu (DotFCR.Source.TypeDefs.exact program.definitions)

/-- The same recursive object embedded constructor-for-constructor in the
traceable-path source syntax. -/
def pathObject (program : Program) : PathTm [] :=
  DotFCRP.Source.Legacy.tm program.object

/-- The corresponding embedded recursive self type. -/
def pathObjectType (program : Program) : PathTy [] :=
  DotFCRP.Source.Legacy.ty program.objectType

/-- Surface type of the generated rekey method's argument. -/
def leftSelection (program : Program) : PathTy program.pathScope :=
  selection program.leftPath program.selectedLabel

/-- Surface type of the generated rekey method's result. -/
def rightSelection (program : Program) : PathTy program.pathScope :=
  selection program.rightPath program.selectedLabel

/-- Scala-like signature of the generated method:
`(x : leftPath.A) => rightPath.A`.

The result is weakened below the argument binder using the existing scoped
`DotFCRP` syntax.  This case-study signature does not mention `x`, so it is the
non-dependent fragment of the existing dependent-method constructor. -/
def rekeySignature (program : Program) : PathTy program.pathScope :=
  dependentMethod program.leftSelection program.rightSelection.weaken

end Program

end DotToFCsub.CompilerCaseStudy.Surface
