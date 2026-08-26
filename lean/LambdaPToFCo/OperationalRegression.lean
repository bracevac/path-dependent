import LambdaPToFCo.OperationalAdmissibility
import LambdaPToFCo.TermTranslationSoundness
import SystemFCo.Safety

/-!
# Closed operational regression for the exact-member core

This program is intentionally a computation rather than a closed value:

```text
let seed = (fun x : Top => x) in
let p    = { seed; A = Top } in
let f    = (fun x : Top => x) in
f p.fst
```

The CK machine must allocate all three values, resolve `p.fst` to the older
`seed` cell, and apply `f` to that location.  The proof below establishes the
restricted fragment typing and the source-only operational-admissibility
evidence.  `OperationalOneStepPreservation.regression_not_goesWrong` applies
the completed generic image-preservation theorem to this program.
-/

namespace LambdaPToFCo
namespace OperationalRegression

open LambdaPFC
open Fragment
open OperationalAdmissibility
open OperationalValueEvidence
open OperationalApplicationSpine
open OperationalFunctionPathSpine

def label : Name := 0

def identityType (n : Nat) : Ty n :=
  .Fun .Top .Top

def identityBody (n : Nat) : Tm (n + 1) :=
  .path (.var 0)

def identityTerm (n : Nat) : Tm n :=
  .abs .Top (identityBody n)

def identityBodyTyping (context : Ctx n) :
    HasType (context.snoc .Top) (identityBody n) .Top :=
  let pathTyping : PathTy (context.snoc .Top) (.var 0) .Top := .var
  .sub (.path pathTyping) (.widen pathTyping .top)

def identityTyping (context : Ctx n) :
    HasType context (identityTerm n) (identityType n) :=
  .abs (identityBodyTyping context) .top .top

def identityApplicationSpine (context : Ctx n) :
    ApplicationSpine
      (HasType.abs (identityBodyTyping context) .top .top) :=
  .abs (identityBodyTyping context) .top .top .top

def identityAdmissible (context : Ctx n) :
    OperationallyAdmissible (identityTyping context) := by
  unfold identityTyping
  let pathTyping : PathTy (context.snoc .Top) (.var 0) .Top := .var
  let inner : HasType (context.snoc .Top) (.path (.var 0))
      (.Single (.var 0)) := .path pathTyping
  let subtype : Sub (context.snoc .Top) (.Single (.var 0)) .Top :=
    .widen pathTyping .top
  let bodyAdmissible : OperationallyAdmissible
      (HasType.sub inner subtype) :=
    .neutralSub .path (.path pathTyping) subtype .top
  let spine := identityApplicationSpine context
  exact .function spine bodyAdmissible

def seedContext : Ctx 1 :=
  .snoc .nil (identityType 0)

def packageType : Ty 1 :=
  exactPackageTy 0 label .Top

def packageTerm : Tm 1 :=
  .pair 0 label (.type .Top)

def packageTyping : HasType seedContext packageTerm packageType :=
  .typePackage .top

def packageAdmissible : OperationallyAdmissible packageTyping :=
  .package (.package .top)

def packageContext : Ctx 2 :=
  seedContext.snoc packageType

def functionTypeInPackageContext : Ty 2 :=
  identityType 2

def functionTyping :
    HasType packageContext (identityTerm 2) functionTypeInPackageContext :=
  identityTyping packageContext

def functionAdmissible : OperationallyAdmissible functionTyping :=
  identityAdmissible packageContext

def applicationContext : Ctx 3 :=
  packageContext.snoc functionTypeInPackageContext

def packageMemberInApplication :
    BoundExactMember applicationContext 1 label .Top 2 :=
  BoundExactMember.there (BoundExactMember.here
    (Γ := seedContext) (first := (0 : Fin 1))
    (label := label) (witness := .Top))

def functionPathTyping :
    PathTy applicationContext (.var 0) (identityType 3) :=
  .var

def functionPathHasType :
    HasType applicationContext (.path (.var 0)) (identityType 3) :=
  .sub (.path functionPathTyping)
    (.widen functionPathTyping (.arrow .top .top))

def argumentPathTyping :
    PathTy applicationContext (.fst (.var 1)) (.Single (.var 2)) :=
  .exactFst packageMemberInApplication

def seedPathTyping :
    PathTy applicationContext (.var 2) (identityType 3) :=
  .var

def argumentSubtype :
    Sub applicationContext (.Single (.fst (.var 1))) .Top :=
  .trans
    (.widen argumentPathTyping (.singleton seedPathTyping))
    (Sub.trans
      (Sub.widen seedPathTyping (.arrow .top .top))
      (Sub.top (.arrow .top .top)))

def argumentPathHasType :
    HasType applicationContext (.path (.fst (.var 1))) .Top :=
  .sub (.path argumentPathTyping) argumentSubtype

def applicationTerm : Tm 3 :=
  .app (.var 0) (.fst (.var 1))

def applicationTyping :
    HasType applicationContext applicationTerm .Top :=
  .app functionPathHasType argumentPathHasType .top

def functionPathSpine :
    FunctionPathSpine (domain := .Top) (codomain := .Top)
      functionPathHasType := by
  unfold functionPathHasType identityType
  exact .widen functionPathTyping .top .top .top

def functionPathAdmissible :
    OperationallyAdmissible functionPathHasType :=
  .functionPath functionPathSpine

def argumentPathAdmissible :
    OperationallyAdmissible argumentPathHasType :=
  .neutralSub .path (.path argumentPathTyping) argumentSubtype .top

def applicationAdmissible : OperationallyAdmissible applicationTyping :=
  .app (resultType := (.Top : Ty 3)) functionPathAdmissible functionPathSpine
    argumentPathAdmissible .top

def functionLetBody : Tm 2 :=
  .let (identityTerm 2) applicationTerm

def functionLetTyping :
    HasType packageContext functionLetBody .Top :=
  .let functionTyping .top applicationTyping

def functionLetAdmissible : OperationallyAdmissible functionLetTyping :=
  .let (resultType := (.Top : Ty 2)) functionAdmissible
    (.directValue (.function (identityApplicationSpine packageContext)))
    applicationAdmissible .top

def packageLetBody : Tm 1 :=
  .let packageTerm functionLetBody

def packageLetTyping : HasType seedContext packageLetBody .Top :=
  .let packageTyping .top functionLetTyping

def packageLetAdmissible : OperationallyAdmissible packageLetTyping :=
  .let (resultType := (.Top : Ty 1)) packageAdmissible
    (.directValue (.package (.package .top))) functionLetAdmissible .top

def program : Tm 0 :=
  .let (identityTerm 0) packageLetBody

def programTyping : HasType .nil program .Top :=
  .let (identityTyping .nil) .top packageLetTyping

def programAdmissible : OperationallyAdmissible programTyping :=
  .let (resultType := (.Top : Ty 0)) (identityAdmissible .nil)
    (.directValue (.function (identityApplicationSpine .nil)))
    packageLetAdmissible .top

/-! ## Compiled target endpoint -/

noncomputable def compiledProgram : SystemFCo.Exp [] :=
  TermTranslation.elaborate StaticTranslation.Scope.empty programTyping

noncomputable def compiledProgramTyping :
    SystemFCo.Exp.HasType .empty compiledProgram
      (StaticTranslation.translateType StaticTranslation.Scope.empty
        programTyping.typeWf) :=
  TermTranslation.elaborate_hasType
    StaticTranslation.Scope.Coherent.empty programTyping

/-- The nontrivial compiled computation is already covered by the target's
standalone safety theorem.  The operational image theorem separately relates
the CK execution below to target reduction and proves source non-stuckness. -/
noncomputable def compiledProgramSoundness :
    Not (SystemFCo.Exp.GoesWrong compiledProgram) :=
  SystemFCo.Exp.soundness compiledProgramTyping

/-! ## Concrete source execution -/

def seedStore : Store 1 :=
  .val .empty (identityTerm 0) .abs

def packageStore : Store 2 :=
  .val seedStore packageTerm .pair

def functionStore : Store 3 :=
  .val packageStore (identityTerm 2) .abs

def packageBinds :
    Store.Binds functionStore 1 (.pair 2 label (.type .Top)) := by
  exact .there (.here (sigma := seedStore) (v := packageTerm) (vv := .pair))

def argumentResolves :
    Path.Resolve (.fst (.var 1)) functionStore (.loc 2) :=
  .fst .var packageBinds

def functionBinds :
    Store.Binds functionStore 0 (identityTerm 3) :=
  .here

/-- The source CK machine performs three allocations, resolves the dependent
first projection to `seed`, applies the stored closure, and finishes at that
location. -/
def sourceExecution :
    State.Steps (State.initial program)
      (State.mk functionStore [] (.path (.var 2))) :=
  .tail .let_push <|
  .tail (.allocate (.abs : (identityTerm 0).IsValue)) <|
  .tail .let_push <|
  .tail (.allocate (.pair : packageTerm.IsValue)) <|
  .tail .let_push <|
  .tail (.allocate (.abs : (identityTerm 2).IsValue)) <|
  .tail (.app .var argumentResolves functionBinds) <|
  .refl

end OperationalRegression
end LambdaPToFCo
