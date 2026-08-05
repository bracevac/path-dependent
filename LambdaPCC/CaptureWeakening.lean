import LambdaPCC.CaptureEvidence

/-!
Allocation weakening for qualifier-aware semantic evidence.  A fresh store
cell extends the semantic world with the introduction qualifier of the allocated
value; all earlier locations and all evidence about them are shifted by the
same intrinsic renaming.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Exact allocation summaries -/

noncomputable def ExactBody.weaken
    {n : Nat} {sigma : Store n} {S : Ty n} {body : Tm (n + 1)}
    {T : Ty (n + 1)} {C : CaptureSet (n + 1)}
    (closure : ExactBody sigma S body T C)
    (v : Tm n) (vv : v.IsValue) :
    ExactBody (Store.val sigma v vv) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext)
      (C.rename FinFun.weaken.ext) := by
  cases closure with
  | source code =>
      simpa only [Ty.weaken, Valuation.weaken, Tm.rename_rename,
        Ty.rename_rename, CaptureSet.rename_rename, FinFun.ext_comp] using
        ExactBody.source (sigma := Store.val sigma v vv) code

noncomputable def ExactValue.weaken
    {n : Nat} {sigma : Store n} {term : Tm n} {Q : CaptureSet n}
    (value : ExactValue sigma term Q)
    (v : Tm n) (vv : v.IsValue) :
    ExactValue (Store.val sigma v vv) term.weaken Q.weaken := by
  cases value with
  | abs closure =>
      apply ExactValue.abs
      simpa only [CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using closure.weaken v vv
  | pair => exact .pair
  | typePair => exact .typePair
  | capturePair => exact .capturePair

def Lookup.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {term : Tm n} {Q : CaptureSet n}
    (lookup : Lookup world x term Q)
    {v : Tm n} {R : CaptureSet n}
    (exact : ExactValue sigma v R) (vv : v.IsValue) :
    Lookup (World.val world exact (vv := vv)) x.succ
      term.weaken Q.weaken :=
  .there lookup

/-! ## Allocation motives for the mutual semantic families -/

private abbrev EnvironmentAllocation
    {n m : Nat} {sigma : Store m} (world : World sigma)
    (Gamma : Ctx n) (rho : Valuation n m)
    (_ : Environment world Gamma rho) : Type 1 :=
  forall {v : Tm m} {Q : CaptureSet m}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    Environment (World.val world exact (vv := vv)) Gamma rho.weaken

private abbrev LocationEvidenceAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (x : Fin n) (T : Ty n) (_ : LocationEvidence world x T) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    LocationEvidence (World.val world exact (vv := vv)) x.succ T.weaken

private abbrev RealizesAllocation
    {n : Nat} {k : Kind} {sigma : Store n} (world : World sigma)
    (referent : Path.Referent n) (d : Tau n k)
    (_ : Realizes world referent d) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    Realizes (World.val world exact (vv := vv)) referent.weaken d.weaken

private abbrev RelationAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (C D : CaptureSet n) (_ : Relation world C D) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    Relation (World.val world exact (vv := vv)) C.weaken D.weaken

private abbrev TyAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (T U : Ty n) (_ : TyCoercion world T U) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    TyCoercion (World.val world exact (vv := vv)) T.weaken U.weaken

private abbrev ShapeAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (S T : Shape n) (_ : ShapeCoercion world S T) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    ShapeCoercion (World.val world exact (vv := vv)) S.weaken T.weaken

private abbrev CoercionAllocation
    {n : Nat} {k : Kind} {sigma : Store n} (world : World sigma)
    (d e : Tau n k) (_ : Coercion world d e) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    Coercion (World.val world exact (vv := vv)) d.weaken e.weaken

private abbrev DeferredAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (S : Ty n) (T U : Ty (n + 1))
    (_ : DeferredCoercion world S T U) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    DeferredCoercion (World.val world exact (vv := vv)) S.weaken
      (T.rename FinFun.weaken.ext) (U.rename FinFun.weaken.ext)

private abbrev MemberAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (S : Ty n) {k : Kind} (d e : Tau (n + 1) k)
    (_ : MemberClosure world S d e) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    MemberClosure (World.val world exact (vv := vv)) S.weaken
      (d.rename FinFun.weaken.ext) (e.rename FinFun.weaken.ext)

private abbrev BodyAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (S : Ty n) (body : Tm (n + 1)) (T : Ty (n + 1))
    (C : CaptureSet (n + 1)) (_ : Body world S body T C) : Type 1 :=
  forall {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue),
    Body (World.val world exact (vv := vv)) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext)
      (C.rename FinFun.weaken.ext)

private abbrev ValueAllocation
    {n : Nat} {sigma : Store n} (world : World sigma)
    (term : Tm n) (T : Ty n) (Q : CaptureSet n)
    (_ : Value world term T Q) : Type 1 :=
  forall {v : Tm n} {R : CaptureSet n}
    (exact : ExactValue sigma v R) (vv : v.IsValue),
    Value (World.val world exact (vv := vv)) term.weaken T.weaken Q.weaken

/-! ## Constructor actions -/

private noncomputable def allocateEnvironmentIntro
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m}
    (lookup : forall x : Fin n,
      LocationEvidence world (rho x) ((Gamma.lookup x).rename rho))
    (ih : forall x, LocationEvidenceAllocation world (rho x)
      ((Gamma.lookup x).rename rho) (lookup x)) :
    EnvironmentAllocation world Gamma rho
      (@Environment.intro n m sigma world Gamma rho lookup) :=
  fun exact vv => by
    apply Environment.intro
    intro x
    simpa only [Valuation.weaken, Valuation.comp, Ty.weaken,
      Ty.rename_rename] using ih x exact vv

private noncomputable def allocateLocationTop
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n}
    (lookup : Lookup world x v Q)
    (coverage : Relation world Q C)
    (coverageIH : RelationAllocation world Q C coverage) :
    LocationEvidenceAllocation world x (.capt C .Top)
      (@LocationEvidence.top _ _ world x v Q C lookup coverage) :=
  fun exact vv => .top (lookup.weaken exact vv) (coverageIH exact vv)

private noncomputable def allocateLocationFun
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {Q C : CaptureSet n} {A S : Ty n}
    {body : Tm (n + 1)} {B U : Ty (n + 1)}
    (lookup : Lookup world x (.abs A body) Q)
    (closure : Body world A body B
      (.union Q.weaken (.singleton (.var 0))))
    (input : TyCoercion world S A)
    (output : DeferredCoercion world S B U)
    (coverage : Relation world Q C)
    (closureIH : BodyAllocation world A body B
      (.union Q.weaken (.singleton (.var 0))) closure)
    (inputIH : TyAllocation world S A input)
    (outputIH : DeferredAllocation world S B U output)
    (coverageIH : RelationAllocation world Q C coverage) :
    LocationEvidenceAllocation world x (.capt C (.Fun S U))
      (@LocationEvidence.fun _ sigma world x Q C A S body B U lookup
        closure input output coverage) :=
  fun exact vv => by
    apply LocationEvidence.fun (lookup.weaken exact vv)
    · simpa only [CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using closureIH exact vv
    · exact inputIH exact vv
    · exact outputIH exact vv
    · exact coverageIH exact vv

private noncomputable def allocateLocationPair
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {x y : Fin n} {Q C : CaptureSet n} {a : Name}
    {delta : Def n k} {S : Ty n} {d : Tau (n + 1) k}
    (lookup : Lookup world x (.pair y a delta) Q)
    (first : LocationEvidence world y S)
    (member : Realizes world delta.referent (d.open (.var y)))
    (coverage : Relation world Q C)
    (firstIH : LocationEvidenceAllocation world y S first)
    (memberIH : RealizesAllocation world delta.referent
      (d.open (.var y)) member)
    (coverageIH : RelationAllocation world Q C coverage) :
    LocationEvidenceAllocation world x (.capt C (.Pair S a d))
      (@LocationEvidence.pair _ _ sigma world x y Q C a delta S d lookup
        first member coverage) :=
  fun exact vv => by
    apply LocationEvidence.pair (lookup.weaken exact vv) (firstIH exact vv)
    · rw [Def.referent_weaken]
      simpa only [Tau.weaken, Tau.open_rename, Path.weaken,
        Path.rename] using memberIH exact vv
    · exact coverageIH exact vv

private noncomputable def allocateLocationSingle
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n} {p : Path n}
    (lookup : Lookup world x v Q)
    (resolution : Path.Resolve p sigma (.loc x))
    (coverage : Relation world Q C)
    (coverageIH : RelationAllocation world Q C coverage) :
    LocationEvidenceAllocation world x (.capt C (.Single p))
      (@LocationEvidence.single _ sigma world x v Q C p lookup resolution coverage) :=
  fun exact vv => .single (lookup.weaken exact vv)
    (resolution.weaken _ vv) (coverageIH exact vv)

private noncomputable def allocateLocationSelection
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {v : Tm n} {Q C E : CaptureSet n}
    {p : Path n} {a : Name} {W : Shape n}
    (lookup : Lookup world x v Q)
    (resolution : Path.Resolve (p.sel a) sigma (.type W))
    (witness : LocationEvidence world x (.capt E W))
    (coverage : Relation world Q C)
    (witnessIH : LocationEvidenceAllocation world x (.capt E W) witness)
    (coverageIH : RelationAllocation world Q C coverage) :
    LocationEvidenceAllocation world x (.capt C (.TSel p a))
      (@LocationEvidence.selection _ sigma world x v Q C E p a W lookup resolution
        witness coverage) :=
  fun exact vv => .selection (lookup.weaken exact vv)
    (resolution.weaken _ vv) (witnessIH exact vv) (coverageIH exact vv)

private noncomputable def allocateRealizesLoc
    (possible : LocationEvidence world x T)
    (possibleIH : LocationEvidenceAllocation world x T possible) :
    RealizesAllocation world (.loc x) (.term T) (.loc possible) :=
  fun exact vv => .loc (possibleIH exact vv)

private noncomputable def allocateRealizesType
    (lower : ShapeCoercion world L W) (upper : ShapeCoercion world W U)
    (lowerIH : ShapeAllocation world L W lower)
    (upperIH : ShapeAllocation world W U upper) :
    RealizesAllocation world (.type W) (.type L U) (.type lower upper) :=
  fun exact vv => .type (lowerIH exact vv) (upperIH exact vv)

private noncomputable def allocateRealizesCapture
    (lower : Relation world L W) (upper : Relation world W U)
    (lowerIH : RelationAllocation world L W lower)
    (upperIH : RelationAllocation world W U upper) :
    RealizesAllocation world (.capture W) (.capture L U)
      (.capture lower upper) :=
  fun exact vv => .capture (lowerIH exact vv) (upperIH exact vv)

private noncomputable def allocateRelationSource
    (environment : Environment world Gamma rho)
    (code : CaptureSet.Sub Gamma C D)
    (environmentIH : EnvironmentAllocation world Gamma rho environment) :
    RelationAllocation world (C.rename rho) (D.rename rho)
      (.source environment code) :=
  fun exact vv => by
    simpa only [Valuation.weaken, CaptureSet.weaken,
      CaptureSet.rename_rename] using
      Relation.source (environmentIH exact vv) code

private noncomputable def allocateRelationRefl :
    RelationAllocation world C C .refl := fun _ _ => .refl

private noncomputable def allocateRelationTrans
    (first : Relation world C D) (second : Relation world D E)
    (firstIH : RelationAllocation world C D first)
    (secondIH : RelationAllocation world D E second) :
    RelationAllocation world C E (.trans first second) :=
  fun exact vv => .trans (firstIH exact vv) (secondIH exact vv)

private noncomputable def allocateRelationRuntime
    (conversion : CaptureSet.RuntimeConv (Path.RuntimeEq sigma) C D) :
    RelationAllocation world C D (.runtime conversion) :=
  fun _ vv => .runtime (conversion.weaken _ vv)

private noncomputable def allocateRelationEmpty :
    RelationAllocation world .empty C .empty := fun _ _ => .empty

private noncomputable def allocateRelationUnionLeft :
    RelationAllocation world C (.union C D) .unionLeft :=
  fun _ _ => .unionLeft

private noncomputable def allocateRelationUnionRight :
    RelationAllocation world D (.union C D) .unionRight :=
  fun _ _ => .unionRight

private noncomputable def allocateRelationUnionElim
    (left : Relation world C E) (right : Relation world D E)
    (leftIH : RelationAllocation world C E left)
    (rightIH : RelationAllocation world D E right) :
    RelationAllocation world (.union C D) E (.unionElim left right) :=
  fun exact vv => .unionElim (leftIH exact vv) (rightIH exact vv)

private noncomputable def allocateRelationAlias
    (left : Path.Resolve p sigma (.loc x))
    (right : Path.Resolve q sigma (.loc x)) :
    RelationAllocation world (.singleton q) (.singleton p)
      (.alias left right) :=
  fun _ vv => .alias (left.weaken _ vv) (right.weaken _ vv)

private noncomputable def allocateRelationFold
    (resolution : Path.Resolve p sigma (.loc x))
    (lookup : Lookup world x term Q) :
    RelationAllocation world Q (.singleton p)
      (.fold resolution lookup) :=
  fun exact vv =>
    .fold (resolution.weaken _ vv) (lookup.weaken exact vv)

private noncomputable def allocateRelationFstRoot
    (resolution : Path.Resolve p.fst sigma (.loc x)) :
    RelationAllocation world (.singleton p.fst) (.singleton p)
      (.fstRoot resolution) :=
  fun _ vv => .fstRoot (resolution.weaken _ vv)

private noncomputable def allocateRelationSelRoot
    (resolution : Path.Resolve (p.sel a) sigma (.loc x)) :
    RelationAllocation world (.singleton (p.sel a)) (.singleton p)
      (.selRoot resolution) :=
  fun _ vv => .selRoot (resolution.weaken _ vv)

private noncomputable def allocateRelationSelectLower
    (resolution : Path.Resolve (p.sel a) sigma (.capture W))
    (lower : Relation world L W)
    (lowerIH : RelationAllocation world L W lower) :
    RelationAllocation world L (.select p a) (.selectLower resolution lower) :=
  fun exact vv => .selectLower (resolution.weaken _ vv) (lowerIH exact vv)

private noncomputable def allocateRelationSelectUpper
    (resolution : Path.Resolve (p.sel a) sigma (.capture W))
    (upper : Relation world W U)
    (upperIH : RelationAllocation world W U upper) :
    RelationAllocation world (.select p a) U (.selectUpper resolution upper) :=
  fun exact vv => .selectUpper (resolution.weaken _ vv) (upperIH exact vv)

private noncomputable def allocateTyRefl :
    TyAllocation world T T .refl := fun _ _ => .refl

private noncomputable def allocateTyTrans
    (first : TyCoercion world T U) (second : TyCoercion world U V)
    (firstIH : TyAllocation world T U first)
    (secondIH : TyAllocation world U V second) :
    TyAllocation world T V (.trans first second) :=
  fun exact vv => .trans (firstIH exact vv) (secondIH exact vv)

private noncomputable def allocateTyRuntime
    (conversion : Ty.RuntimeConv (Path.RuntimeEq sigma) T U) :
    TyAllocation world T U (.runtime conversion) :=
  fun _ vv => .runtime (conversion.weaken _ vv)

private noncomputable def allocateTyCapt
    (captures : Relation world C D) (shape : ShapeCoercion world S T)
    (capturesIH : RelationAllocation world C D captures)
    (shapeIH : ShapeAllocation world S T shape) :
    TyAllocation world (.capt C S) (.capt D T) (.capt captures shape) :=
  fun exact vv => .capt (capturesIH exact vv) (shapeIH exact vv)

private noncomputable def allocateShapeRefl :
    ShapeAllocation world S S .refl := fun _ _ => .refl

private noncomputable def allocateShapeTrans
    (first : ShapeCoercion world S T) (second : ShapeCoercion world T U)
    (firstIH : ShapeAllocation world S T first)
    (secondIH : ShapeAllocation world T U second) :
    ShapeAllocation world S U (.trans first second) :=
  fun exact vv => .trans (firstIH exact vv) (secondIH exact vv)

private noncomputable def allocateShapeRuntime
    (conversion : Shape.RuntimeConv (Path.RuntimeEq sigma) S T) :
    ShapeAllocation world S T (.runtime conversion) :=
  fun _ vv => .runtime (conversion.weaken _ vv)

private noncomputable def allocateShapeBot :
    ShapeAllocation world .Bot S .bot := fun _ _ => .bot

private noncomputable def allocateShapeTop :
    ShapeAllocation world S .Top .top := fun _ _ => .top

private noncomputable def allocateShapeWiden
    (resolution : Path.Resolve p sigma (.loc x))
    (possible : LocationEvidence world x (.capt C S))
    (possibleIH : LocationEvidenceAllocation world x (.capt C S) possible) :
    ShapeAllocation world (.Single p) S (.widen resolution possible) :=
  fun exact vv => .widen (resolution.weaken _ vv) (possibleIH exact vv)

private noncomputable def allocateShapeAlias
    (left : Path.Resolve p sigma (.loc x))
    (right : Path.Resolve q sigma (.loc x)) :
    ShapeAllocation world (.Single q) (.Single p) (.alias left right) :=
  fun _ vv => .alias (left.weaken _ vv) (right.weaken _ vv)

private noncomputable def allocateShapeSelectLower
    (resolution : Path.Resolve (p.sel a) sigma (.type W))
    (lower : ShapeCoercion world L W)
    (lowerIH : ShapeAllocation world L W lower) :
    ShapeAllocation world L (.TSel p a) (.selectLower resolution lower) :=
  fun exact vv => .selectLower (resolution.weaken _ vv) (lowerIH exact vv)

private noncomputable def allocateShapeSelectUpper
    (resolution : Path.Resolve (p.sel a) sigma (.type W))
    (upper : ShapeCoercion world W U)
    (upperIH : ShapeAllocation world W U upper) :
    ShapeAllocation world (.TSel p a) U (.selectUpper resolution upper) :=
  fun exact vv => .selectUpper (resolution.weaken _ vv) (upperIH exact vv)

private noncomputable def allocateShapeFun
    (domain : TyCoercion world S' S)
    (codomain : DeferredCoercion world S' T T')
    (domainIH : TyAllocation world S' S domain)
    (codomainIH : DeferredAllocation world S' T T' codomain) :
    ShapeAllocation world (.Fun S T) (.Fun S' T')
      (.fun domain codomain) :=
  fun exact vv => .fun (domainIH exact vv) (codomainIH exact vv)

private noncomputable def allocateShapePair
    (first : TyCoercion world S S')
    (member : MemberClosure world S d d')
    (firstIH : TyAllocation world S S' first)
    (memberIH : MemberAllocation world S d d' member) :
    ShapeAllocation world (.Pair S a d) (.Pair S' a d')
      (.pair first member) :=
  fun exact vv => .pair (firstIH exact vv) (memberIH exact vv)

private noncomputable def allocateCoercionRefl :
    CoercionAllocation world d d .refl := fun _ _ => .refl

private noncomputable def allocateCoercionTrans
    (first : Coercion world d e) (second : Coercion world e f)
    (firstIH : CoercionAllocation world d e first)
    (secondIH : CoercionAllocation world e f second) :
    CoercionAllocation world d f (.trans first second) :=
  fun exact vv => .trans (firstIH exact vv) (secondIH exact vv)

private noncomputable def allocateCoercionRuntime
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma) d e) :
    CoercionAllocation world d e (.runtime conversion) :=
  fun _ vv => .runtime (conversion.weaken _ vv)

private noncomputable def allocateCoercionTerm
    (types : TyCoercion world T U)
    (typesIH : TyAllocation world T U types) :
    CoercionAllocation world (.term T) (.term U) (.term types) :=
  fun exact vv => .term (typesIH exact vv)

private noncomputable def allocateCoercionType
    (lower : ShapeCoercion world L' L) (upper : ShapeCoercion world U U')
    (lowerIH : ShapeAllocation world L' L lower)
    (upperIH : ShapeAllocation world U U' upper) :
    CoercionAllocation world (.type L U) (.type L' U')
      (.type lower upper) :=
  fun exact vv => .type (lowerIH exact vv) (upperIH exact vv)

private noncomputable def allocateCoercionCapture
    (lower : Relation world L' L) (upper : Relation world U U')
    (lowerIH : RelationAllocation world L' L lower)
    (upperIH : RelationAllocation world U U' upper) :
    CoercionAllocation world (.capture L U) (.capture L' U')
      (.capture lower upper) :=
  fun exact vv => .capture (lowerIH exact vv) (upperIH exact vv)

private noncomputable def allocateDeferredRefl :
    DeferredAllocation world S T T .refl := fun _ _ => .refl

private noncomputable def allocateDeferredTrans
    (first : DeferredCoercion world S T U)
    (second : DeferredCoercion world S U V)
    (firstIH : DeferredAllocation world S T U first)
    (secondIH : DeferredAllocation world S U V second) :
    DeferredAllocation world S T V (.trans first second) :=
  fun exact vv => .trans (firstIH exact vv) (secondIH exact vv)

private noncomputable def allocateDeferredRuntime
    (conversion : Ty.RuntimeConv
      (Path.ScopedLift (Path.RuntimeEq sigma)) T U) :
    DeferredAllocation world S T U (.runtime conversion) :=
  fun _ vv => .runtime (conversion.weakenScoped _ vv)

private noncomputable def allocateDeferredNarrow
    (domain : TyCoercion world S' S)
    (codomain : DeferredCoercion world S T U)
    (domainIH : TyAllocation world S' S domain)
    (codomainIH : DeferredAllocation world S T U codomain) :
    DeferredAllocation world S' T U (.narrow domain codomain) :=
  fun exact vv => .narrow (domainIH exact vv) (codomainIH exact vv)

private noncomputable def allocateDeferredSource
    (environment : Environment world Gamma rho)
    (code : Ty.Sub (Gamma.snoc S) T U)
    (environmentIH : EnvironmentAllocation world Gamma rho environment) :
    DeferredAllocation world (S.rename rho)
      (T.rename rho.ext) (U.rename rho.ext) (.source environment code) :=
  fun exact vv => by
    simpa only [Valuation.weaken, Valuation.comp, Ty.weaken,
      Ty.rename_rename, FinFun.ext_comp] using
      DeferredCoercion.source (environmentIH exact vv) code

private noncomputable def allocateMemberSource
    (environment : Environment world Gamma rho)
    (code : Tau.Sub (Gamma.snoc S) d e)
    (environmentIH : EnvironmentAllocation world Gamma rho environment) :
    MemberAllocation world (S.rename rho)
      (d.rename rho.ext) (e.rename rho.ext) (.source environment code) :=
  fun exact vv => by
    simpa only [Valuation.weaken, Valuation.comp, Ty.weaken,
      Ty.rename_rename, Tau.rename_rename, FinFun.ext_comp] using
      MemberClosure.source (environmentIH exact vv) code

private noncomputable def allocateBodySource
    (environment : Environment world Gamma rho)
    (code : Tm.Ty (Gamma.snoc S) body T C)
    (environmentIH : EnvironmentAllocation world Gamma rho environment) :
    BodyAllocation world (S.rename rho) (body.rename rho.ext)
      (T.rename rho.ext) (C.rename rho.ext) (.source environment code) :=
  fun exact vv => by
    simpa only [Valuation.weaken, Valuation.comp, Ty.weaken,
      Ty.rename_rename, Tm.rename_rename, CaptureSet.rename_rename,
      FinFun.ext_comp] using Body.source (environmentIH exact vv) code

private noncomputable def allocateValueAbs
    (closure : Body world A body B
      (.union Q.weaken (.singleton (.var 0))))
    (suffix : TyCoercion world (.capt Q (.Fun A B)) T)
    (closureIH : BodyAllocation world A body B
      (.union Q.weaken (.singleton (.var 0))) closure)
    (suffixIH : TyAllocation world (.capt Q (.Fun A B)) T suffix) :
    ValueAllocation world (.abs A body) T Q (.abs closure suffix) :=
  fun exact vv => by
    apply Value.abs
    · simpa only [CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using closureIH exact vv
    · exact suffixIH exact vv

private noncomputable def allocateValuePair
    (qualifier : Q =
      .union (.singleton (.var y)) (.singleton (.var z)))
    (suffix : TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.term
            (.capt (.singleton (Path.var z).weaken)
              (.Single (Path.var z).weaken))))) T)
    (suffixIH : TyAllocation world _ T suffix) :
    ValueAllocation world (.pair y a (.val z)) T Q
      (.pair qualifier suffix) :=
  fun exact vv => by
    apply Value.pair
    · simpa [CaptureSet.weaken, CaptureSet.rename, Path.rename] using
        congrArg (fun C => C.rename FinFun.weaken) qualifier
    · simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Path.weaken_rename] using
        suffixIH exact vv

private noncomputable def allocateValueTypePair
    (qualifier : Q = .singleton (.var y))
    (suffix : TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.type W.weaken W.weaken))) T)
    (suffixIH : TyAllocation world _ T suffix) :
    ValueAllocation world (.pair y a (.type W)) T Q
      (.typePair qualifier suffix) :=
  fun exact vv => by
    apply Value.typePair
    · simpa [CaptureSet.weaken, CaptureSet.rename, Path.rename] using
        congrArg (fun C => C.rename FinFun.weaken) qualifier
    · simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Shape.weaken_rename] using
        suffixIH exact vv

private noncomputable def allocateValueCapturePair
    (qualifier : Q = .singleton (.var y))
    (suffix : TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.capture W.weaken W.weaken))) T)
    (suffixIH : TyAllocation world _ T suffix) :
    ValueAllocation world (.pair y a (.capture W)) T Q
      (.capturePair qualifier suffix) :=
  fun exact vv => by
    apply Value.capturePair
    · simpa [CaptureSet.weaken, CaptureSet.rename, Path.rename] using
        congrArg (fun C => C.rename FinFun.weaken) qualifier
    · simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using suffixIH exact vv

local macro "allocationRec(" recursor:term ")" : term =>
  `($recursor
      (motive_1 := EnvironmentAllocation)
      (motive_2 := LocationEvidenceAllocation)
      (motive_3 := RealizesAllocation)
      (motive_4 := RelationAllocation)
      (motive_5 := TyAllocation)
      (motive_6 := ShapeAllocation)
      (motive_7 := CoercionAllocation)
      (motive_8 := DeferredAllocation)
      (motive_9 := MemberAllocation)
      (motive_10 := BodyAllocation)
      (motive_11 := ValueAllocation)
      allocateEnvironmentIntro
      allocateLocationTop allocateLocationFun allocateLocationPair
      allocateLocationSingle allocateLocationSelection
      allocateRealizesLoc allocateRealizesType allocateRealizesCapture
      allocateRelationSource allocateRelationRefl allocateRelationTrans
      allocateRelationRuntime allocateRelationEmpty
      allocateRelationUnionLeft allocateRelationUnionRight
      allocateRelationUnionElim allocateRelationAlias
      allocateRelationFold
      allocateRelationFstRoot allocateRelationSelRoot
      allocateRelationSelectLower allocateRelationSelectUpper
      allocateTyRefl allocateTyTrans allocateTyRuntime allocateTyCapt
      allocateShapeRefl allocateShapeTrans allocateShapeRuntime
      allocateShapeBot allocateShapeTop allocateShapeWiden allocateShapeAlias
      allocateShapeSelectLower allocateShapeSelectUpper
      allocateShapeFun allocateShapePair
      allocateCoercionRefl allocateCoercionTrans allocateCoercionRuntime
      allocateCoercionTerm allocateCoercionType allocateCoercionCapture
      allocateDeferredRefl allocateDeferredTrans allocateDeferredRuntime
      allocateDeferredNarrow allocateDeferredSource
      allocateMemberSource allocateBodySource
      allocateValueAbs allocateValuePair
      allocateValueTypePair allocateValueCapturePair)

/-! ## Public weakening operations -/

noncomputable def Environment.weaken
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m}
    (evidence : Environment world Gamma rho)
    {v : Tm m} {Q : CaptureSet m}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Environment (World.val world exact (vv := vv)) Gamma rho.weaken :=
  allocationRec(Environment.rec) evidence exact vv

noncomputable def LocationEvidence.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {T : Ty n} (evidence : LocationEvidence world x T)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    LocationEvidence (World.val world exact (vv := vv)) x.succ T.weaken :=
  allocationRec(LocationEvidence.rec) evidence exact vv

noncomputable def Realizes.weaken
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {referent : Path.Referent n} {d : Tau n k}
    (evidence : Realizes world referent d)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Realizes (World.val world exact (vv := vv)) referent.weaken d.weaken :=
  allocationRec(Realizes.rec) evidence exact vv

noncomputable def Relation.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {C D : CaptureSet n} (evidence : Relation world C D)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Relation (World.val world exact (vv := vv)) C.weaken D.weaken :=
  allocationRec(Relation.rec) evidence exact vv

noncomputable def TyCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {T U : Ty n} (evidence : TyCoercion world T U)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    TyCoercion (World.val world exact (vv := vv)) T.weaken U.weaken :=
  allocationRec(TyCoercion.rec) evidence exact vv

noncomputable def ShapeCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S T : Shape n} (evidence : ShapeCoercion world S T)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    ShapeCoercion (World.val world exact (vv := vv)) S.weaken T.weaken :=
  allocationRec(ShapeCoercion.rec) evidence exact vv

noncomputable def Coercion.weaken
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {d e : Tau n k} (evidence : Coercion world d e)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Coercion (World.val world exact (vv := vv)) d.weaken e.weaken :=
  allocationRec(Coercion.rec) evidence exact vv

noncomputable def DeferredCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {T U : Ty (n + 1)}
    (evidence : DeferredCoercion world S T U)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    DeferredCoercion (World.val world exact (vv := vv)) S.weaken
      (T.rename FinFun.weaken.ext) (U.rename FinFun.weaken.ext) :=
  allocationRec(DeferredCoercion.rec) evidence exact vv

noncomputable def MemberClosure.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {k : Kind} {d e : Tau (n + 1) k}
    (evidence : MemberClosure world S d e)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    MemberClosure (World.val world exact (vv := vv)) S.weaken
      (d.rename FinFun.weaken.ext) (e.rename FinFun.weaken.ext) :=
  allocationRec(MemberClosure.rec) evidence exact vv

noncomputable def Body.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {body : Tm (n + 1)} {T : Ty (n + 1)}
    {C : CaptureSet (n + 1)} (evidence : Body world S body T C)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Body (World.val world exact (vv := vv)) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext)
      (C.rename FinFun.weaken.ext) :=
  allocationRec(Body.rec) evidence exact vv

noncomputable def Value.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {term : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : Value world term T Q)
    {v : Tm n} {R : CaptureSet n}
    (exact : ExactValue sigma v R) (vv : v.IsValue) :
    Value (World.val world exact (vv := vv)) term.weaken T.weaken Q.weaken :=
  allocationRec(Value.rec) value exact vv

/-! ## Extending a valid world -/

def World.Valid.extend
    {n : Nat} {sigma : Store n} {world : World sigma}
    {v : Tm n} {vv : v.IsValue} {T : Ty n} {Q : CaptureSet n}
    {exact : ExactValue sigma v Q}
    (valid : World.Valid world) (value : Value world v T Q) :
    World.Valid (World.val world exact (vv := vv)) :=
  .val valid value

end
end Cap
end LambdaPCC
