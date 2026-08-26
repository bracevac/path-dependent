import LambdaPToFCo.TermTranslation

/-!
# Closed regression for the term compiler

The source program is `fun f => fun x => let p = { x, A = Top } in f x`.
Its typing derivation deliberately routes `x` through both exact-member
bounds (`Top <: p.A <: Top`) before the application. Thus elaboration must
produce a Church package, unpack that binding once, use both lexical coercion
variables, and compile the source application.
-/

namespace LambdaPToFCo
namespace TermTranslationRegression

open LambdaPFC
open Fragment

def label : Name := 0

def functionType (n : Nat) : Ty n :=
  .Fun .Top .Top

def functionWf : Wf (.nil : Ctx 0) (functionType 0) :=
  .arrow .top .top

def functionContext : Ctx 1 :=
  Ctx.snoc .nil (functionType 0)

def argumentContext : Ctx 2 :=
  functionContext.snoc .Top

def packageType : Ty 2 :=
  exactPackageTy 0 label .Top

def packageTerm : Tm 2 :=
  .pair 0 label (.type .Top)

def packageTyping : HasType argumentContext packageTerm packageType :=
  .typePackage .top

def bodyContext : Ctx 3 :=
  argumentContext.snoc packageType

def member : BoundExactMember bodyContext 0 label .Top 1 :=
  .here

def functionPathTyping :
    PathTy bodyContext (.var 2) (functionType 3) := by
  change PathTy bodyContext (.var 2) (bodyContext.lookup 2)
  exact .var

def functionTyping :
    HasType bodyContext (.path (.var 2)) (functionType 3) :=
  .sub (.path functionPathTyping)
    (.widen functionPathTyping (.arrow .top .top))

def argumentPathTyping :
    PathTy bodyContext (.var 1) .Top := by
  change PathTy bodyContext (.var 1) (bodyContext.lookup 1)
  exact .var

def throughMember : Sub bodyContext (.Single (.var 1)) .Top :=
  .trans
    (.widen argumentPathTyping .top)
    (.trans (Sub.selectExactLower member .top)
      (Sub.selectExactUpper member .top))

def argumentTyping :
    HasType bodyContext (.path (.var 1)) .Top :=
  .sub (.path argumentPathTyping) throughMember

def applicationTerm : Tm 3 :=
  .app (.var 2) (.var 1)

def applicationTyping :
    HasType bodyContext applicationTerm .Top :=
  .app functionTyping argumentTyping .top

def packageBody : Tm 2 :=
  .let packageTerm applicationTerm

def packageBodyTyping :
    HasType argumentContext packageBody .Top :=
  .let packageTyping .top applicationTyping

def innerBody : Tm 1 :=
  .abs .Top packageBody

def innerBodyTyping :
    HasType functionContext innerBody (functionType 1) := by
  exact HasType.abs (domain := .Top) (codomain := .Top)
    (by simpa only [argumentContext, Ty.weaken] using packageBodyTyping)
    .top .top

def program : Tm 0 :=
  .abs (functionType 0) innerBody

def programType : Ty 0 :=
  .Fun (functionType 0) (functionType 0).weaken

def programTyping : HasType .nil program programType := by
  exact HasType.abs (domain := functionType 0)
    (codomain := functionType 0)
    (by simpa only [functionContext, functionType, Ty.weaken] using
      innerBodyTyping)
    functionWf functionWf

end TermTranslationRegression
end LambdaPToFCo
