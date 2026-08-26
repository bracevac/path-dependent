import LambdaPToFCo.Source
import SystemFCo.ChurchPackage

/-!
# Exact LambdaP packages as explicit SystemFCo packages

This is the first deliberately small bridge from the LambdaP source layer to
the explicit-coercion target.  It covers only `Source.HasType.typePackage`:
an exact type definition is represented by a Church package that hides its
witness and passes two object-language reflexivity coercions to its consumer.

The source package's first component becomes the Church payload.  Its target
type is constant in the hidden witness; the source rule imposes no relation
between the first component's type and the stored type definition.

There is no claim of a whole-language translation or operational
correspondence in this module.
-/

namespace LambdaPToFCo
namespace ExactPackage

/-- The first-component payload does not depend on the hidden type witness. -/
def payloadFamily (firstType : SystemFCo.Ty sig) :
    SystemFCo.Ty (sig ,, .tvar) :=
  firstType.weaken .tvar

/-- Compile an exact package after the source witness type and first component
have been translated to target syntax.

Both bounds equal `witness`, so the two pieces of evidence stored in the
target term are literal `Co.refl witness` nodes. -/
def compile (witness firstType : SystemFCo.Ty sig)
    (first : SystemFCo.Exp sig) : SystemFCo.Exp sig :=
  SystemFCo.Exp.packMember
    witness witness witness (payloadFamily firstType)
    (.refl witness) (.refl witness) first

/-- Target typing for the compiled exact package.  This proof uses the public
Church-package introduction rule; it does not inspect its encoding. -/
noncomputable def compile_hasType
    {context : SystemFCo.Ctx sig}
    {witness firstType : SystemFCo.Ty sig}
    {first : SystemFCo.Exp sig}
    (firstTyping : SystemFCo.Exp.HasType context first firstType) :
    SystemFCo.Exp.HasType context
      (compile witness firstType first)
      (SystemFCo.Ty.member witness witness (payloadFamily firstType)) := by
  apply SystemFCo.Exp.HasType.packMember
  · exact .refl
  · exact .refl
  · simpa only [payloadFamily, SystemFCo.Ty.weaken_openTVar]
      using firstTyping

/-- Constructor-level bridge from the exact source package rule.

Since a general translation of LambdaPFC types and contexts has intentionally
not been defined yet, the target images of the witness and first component
remain explicit parameters. -/
def compileTypePackage
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirst : Fin n} {sourceLabel : LambdaPFC.Name}
    {sourceWitness : LambdaPFC.Ty n}
    (_sourceTyping :
      Source.HasType sourceContext
        (.pair sourceFirst sourceLabel (.type sourceWitness))
        (Source.exactPackageTy sourceFirst sourceLabel sourceWitness))
    (targetWitness firstType : SystemFCo.Ty sig)
    (first : SystemFCo.Exp sig) : SystemFCo.Exp sig :=
  compile targetWitness firstType first

/-- Typing theorem for the constructor-level bridge.  Target typing depends
on the supplied target images and their typing proof; the source derivation
records that the input really is the exact package constructor in scope. -/
noncomputable def compileTypePackage_hasType
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirst : Fin n} {sourceLabel : LambdaPFC.Name}
    {sourceWitness : LambdaPFC.Ty n}
    {targetContext : SystemFCo.Ctx sig}
    {targetWitness firstType : SystemFCo.Ty sig}
    {first : SystemFCo.Exp sig}
    (sourceTyping :
      Source.HasType sourceContext
        (.pair sourceFirst sourceLabel (.type sourceWitness))
        (Source.exactPackageTy sourceFirst sourceLabel sourceWitness))
    (firstTyping :
      SystemFCo.Exp.HasType targetContext first firstType) :
    SystemFCo.Exp.HasType targetContext
      (compileTypePackage sourceTyping targetWitness firstType first)
      (SystemFCo.Ty.member targetWitness targetWitness
        (payloadFamily firstType)) :=
  compile_hasType firstTyping

/-! ## The existing exact-package regression, translated

The source context contains `y : Top`; its target image is a one-variable
mixed telescope containing `y : top`.  The source term `<y; A = Top>` becomes
a package hiding target `top`, carrying `y`, and storing explicit
`refl top` evidence in both directions.
-/

namespace Regression

abbrev targetSig : SystemFCo.Sig :=
  [] ,, .var

def targetContext : SystemFCo.Ctx targetSig :=
  SystemFCo.Ctx.empty.bindVar .top

def targetFirst : SystemFCo.Exp targetSig :=
  .var .here

def targetFirstTyping :
    SystemFCo.Exp.HasType targetContext targetFirst .top :=
  .var .here

/-- The source constructor being compiled. -/
def sourceTyping :=
  Source.Regression.packageConstruction

/-- The actual target syntax for the source regression package. -/
def compiled : SystemFCo.Exp targetSig :=
  compileTypePackage sourceTyping .top .top targetFirst

noncomputable def compiledTyping :
    SystemFCo.Exp.HasType targetContext compiled
      (SystemFCo.Ty.member .top .top (payloadFamily .top)) :=
  compileTypePackage_hasType sourceTyping targetFirstTyping

/-! ### The interface visible while unpacking

The handler binders are, from oldest to newest:

1. the hidden witness type `X`;
2. a coercion variable `lower : top => X`;
3. a coercion variable `upper : X => top`;
4. the first-component payload.

The definitions `selectedLower` and `selectedUpper` below are therefore real
`Co.cvar` syntax.  Their typing derivations are ordinary target lookup proofs,
not LambdaPFC realization evidence.
-/

abbrev interfaceSig : SystemFCo.Sig :=
  ((((targetSig ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)

def interfaceContext : SystemFCo.Ctx interfaceSig :=
  (((targetContext.bindTVar
      |>.bindCVar
        ((.top : SystemFCo.Ty targetSig).weaken .tvar)
        (.tvar .here))
      |>.bindCVar
        ((.tvar .here : SystemFCo.Ty (targetSig ,, .tvar)).weaken .cvar)
        (((.top : SystemFCo.Ty targetSig).weaken .tvar).weaken .cvar))
      |>.bindVar
        (((payloadFamily (.top : SystemFCo.Ty targetSig)).weaken .cvar)
          |>.weaken .cvar))

/-- `top`, transported underneath all four handler binders. -/
def interfaceLower : SystemFCo.Ty interfaceSig :=
  (((((.top : SystemFCo.Ty targetSig).weaken .tvar).weaken .cvar)
    |>.weaken .cvar) |>.weaken .var)

/-- The hidden witness `X`, transported underneath the two coercion binders
and the payload binder. -/
def interfaceWitness : SystemFCo.Ty interfaceSig :=
  (((.tvar .here : SystemFCo.Ty (targetSig ,, .tvar)).weaken .cvar
    |>.weaken .cvar) |>.weaken .var)

/-- The lower bound selected from the unpacked member interface. -/
def selectedLower : SystemFCo.Co interfaceSig :=
  .cvar (.there (.there .here))

/-- The upper bound selected from the unpacked member interface. -/
def selectedUpper : SystemFCo.Co interfaceSig :=
  .cvar (.there .here)

def selectedLowerTyping :
    SystemFCo.Co.HasType interfaceContext selectedLower
      interfaceLower interfaceWitness :=
  .cvar (.there (.there .here))

def selectedUpperTyping :
    SystemFCo.Co.HasType interfaceContext selectedUpper
      interfaceWitness interfaceLower :=
  .cvar (.there .here)

/-- A target coercion term that explicitly composes the selected bounds. -/
def selectedRoundTrip : SystemFCo.Co interfaceSig :=
  .trans selectedLower selectedUpper

def selectedRoundTripTyping :
    SystemFCo.Co.HasType interfaceContext selectedRoundTrip
      interfaceLower interfaceLower :=
  .trans selectedLowerTyping selectedUpperTyping

/-- The inline consumer uses both selected coercion variables. -/
def interfaceBody : SystemFCo.Exp interfaceSig :=
  .cast (.var .here) selectedRoundTrip

def interfaceBodyTyping :
    SystemFCo.Exp.HasType interfaceContext interfaceBody interfaceLower :=
  .cast (.var .here) selectedRoundTripTyping

/-- Eliminate the compiled source package through the explicit member
interface. -/
def unpacked : SystemFCo.Exp targetSig :=
  SystemFCo.Exp.unpackMemberBody compiled .top .top .top
    (payloadFamily .top) interfaceBody

noncomputable def unpackedTyping :
    SystemFCo.Exp.HasType targetContext unpacked .top :=
  SystemFCo.Exp.HasType.unpackMemberBody compiledTyping interfaceBodyTyping

end Regression

end ExactPackage
end LambdaPToFCo
