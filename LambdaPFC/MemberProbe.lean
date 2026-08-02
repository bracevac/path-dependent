import LambdaPFC.Member

/-!
An inhabited one-hop probe for an abstract type member.  The package selects
`Top` as its witness, with the singleton of a separate runtime location as its
lower bound.  Introduction and elimination both preserve that location.
-/

namespace LambdaPFC.MemberProbe

open LambdaP LambdaPFC

def label : Name := 0

def packageLocation : Fin 3 := 0
def firstLocation : Fin 3 := 1
def valueLocation : Fin 3 := 2

def model : Model 3 := fun x =>
  if x = packageLocation then
    .pair firstLocation label (.type .Top)
  else
    .atom

def valuation : Valuation 2 3 :=
  Fin.cases packageLocation (fun _ => valueLocation)

def packagePath : Path 2 := .var 0
def valuePath : Path 2 := .var 1

def lower : Ty 2 := .Single valuePath
def upper : Ty 2 := .Top

def package : MemberPackage model valuation packagePath label lower upper where
  witness := .Top
  resolves := by
    apply Resolve.sel Resolve.var
    apply Select.hit (y := firstLocation)
    simp [model, packageLocation, valuation, instantiateTy, Ty.subst]
  lower := .top
  upper := .refl

def lowerValue : Typed model valuation lower where
  raw := valueLocation
  realizes := .single .var

def selectedValue : Selected package :=
  package.intro lowerValue

def upperValue : Typed model valuation upper :=
  package.elim selectedValue

theorem introduction_preserves_runtime :
    selectedValue.erase = lowerValue.erase := rfl

theorem elimination_preserves_runtime :
    upperValue.erase = selectedValue.erase := rfl

theorem complete_pass_preserves_runtime :
    upperValue.erase = lowerValue.erase := rfl

end LambdaPFC.MemberProbe
