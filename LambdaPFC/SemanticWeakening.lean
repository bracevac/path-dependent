import LambdaPFC.SemanticEvidence

/-!
Allocation weakening for semantic evidence.  Allocating a fresh value shifts
all existing store locations.  Evidence below a source binder is renamed by
the lifted weakening, which leaves the bound variable fixed while shifting
the locations supplied by the enclosing environment.
-/

namespace LambdaPFC

noncomputable section

/-! ## Runtime conversion below a binder -/

/-- Scoped runtime equality is stable under allocation in the ambient store. -/
noncomputable def Path.ScopedLift.weakenRuntime
    {n : Nat} {sigma : Store n} {p q : Path (n + 1)}
    (evidence : Path.ScopedLift (Path.RuntimeEq sigma) p q)
    (v : Tm n) (vv : v.IsValue) :
    Path.ScopedLift (Path.RuntimeEq (Store.val sigma v vv))
      (p.rename FinFun.weaken.ext) (q.rename FinFun.weaken.ext) := by
  induction evidence with
  | bound => exact .bound
  | old evidence =>
      simpa only [Path.weaken, Path.rename_rename, FinFun.comp_weaken] using
        Path.ScopedLift.old (evidence.weaken v vv)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | fst _ ih => exact .fst ih
  | sel _ ih => exact .sel ih

/-- Runtime conversion below a binder is stable under allocation in the
ambient store. -/
noncomputable def Tau.RuntimeConv.weakenScoped
    {n : Nat} {sigma : Store n} {d1 d2 : Tau (n + 1) k}
    (conversion :
      Tau.RuntimeConv (Path.ScopedLift (Path.RuntimeEq sigma)) d1 d2)
    (v : Tm n) (vv : v.IsValue) :
    Tau.RuntimeConv
      (Path.ScopedLift (Path.RuntimeEq (Store.val sigma v vv)))
      (d1.rename FinFun.weaken.ext) (d2.rename FinFun.weaken.ext) :=
  conversion.rename FinFun.weaken.ext
    (fun evidence => evidence.weakenRuntime v vv)

/-! ## Allocation weakening -/

private abbrev EnvironmentAllocation
    {n m : Nat} (Gamma : Ctx n) (rho : Valuation n m)
    (sigma : Store m) (_ : Environment Gamma rho sigma) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    Environment Gamma rho.weaken (Store.val sigma v vv)

private abbrev PossibleAllocation
    {m : Nat} (sigma : Store m) (x : Fin m) (T : Ty m)
    (_ : Store.Possible sigma x T) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    Store.Possible (Store.val sigma v vv) x.succ T.weaken

private abbrev RealizesAllocation
    {m : Nat} {k : Kind} (sigma : Store m)
    (referent : Path.Referent m) (d : Tau m k)
    (_ : Path.Referent.Realizes sigma referent d) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    Path.Referent.Realizes (Store.val sigma v vv)
      referent.weaken d.weaken

private abbrev CoercionAllocation
    {m : Nat} {k : Kind} (sigma : Store m) (d1 d2 : Tau m k)
    (_ : Coercion sigma d1 d2) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    Coercion (Store.val sigma v vv) d1.weaken d2.weaken

private abbrev DeferredAllocation
    {m : Nat} (sigma : Store m) (S : Ty m) (T U : Ty (m + 1))
    (_ : DeferredCoercion sigma S T U) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    DeferredCoercion (Store.val sigma v vv) S.weaken
      (T.rename FinFun.weaken.ext) (U.rename FinFun.weaken.ext)

private abbrev MemberAllocation
    {m : Nat} (sigma : Store m) (S : Ty m) {k : Kind}
    (d d' : Tau (m + 1) k)
    (_ : MemberClosure sigma S d d') : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    MemberClosure (Store.val sigma v vv) S.weaken
      (d.rename FinFun.weaken.ext) (d'.rename FinFun.weaken.ext)

private abbrev BodyAllocation
    {m : Nat} (sigma : Store m) (S : Ty m)
    (body : Tm (m + 1)) (T : Ty (m + 1))
    (_ : BodyClosure sigma S body T) : Type 1 :=
  forall (v : Tm m) (vv : v.IsValue),
    BodyClosure (Store.val sigma v vv) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext)

/-! The constructor clauses below instantiate the mutual induction principle
generated for the seven semantic evidence families. -/

private noncomputable def allocateEnvironmentIntro
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m}
    (lookup : forall x : Fin n,
      Store.Possible sigma (rho x) ((Gamma.lookup x).rename rho))
    (ih : forall x, PossibleAllocation sigma (rho x)
      ((Gamma.lookup x).rename rho) (lookup x)) :
    EnvironmentAllocation Gamma rho sigma (.intro lookup) :=
  fun v vv => by
    apply Environment.intro
    intro x
    simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
      Ty.rename_rename] using ih x v vv

private noncomputable def allocatePossibleTop :
    PossibleAllocation sigma x .Top .top :=
  fun _ _ => .top

private noncomputable def allocatePossibleFun
    (binding : Store.Binds sigma x (.abs A body))
    (closure : BodyClosure sigma A body B)
    (domain : Coercion sigma (.ty S) (.ty A))
    (codomain : DeferredCoercion sigma S B U)
    (closureIH : BodyAllocation sigma A body B closure)
    (domainIH : CoercionAllocation sigma (.ty S) (.ty A) domain)
    (codomainIH : DeferredAllocation sigma S B U codomain) :
    PossibleAllocation sigma x (.Fun S U)
      (.fun binding closure domain codomain) :=
  fun v vv => .fun (.there binding) (closureIH v vv)
    (domainIH v vv) (codomainIH v vv)

private noncomputable def allocatePossiblePair
    (binding : Store.Binds sigma x (.pair y a delta))
    (first : Store.Possible sigma y S)
    (member : Path.Referent.Realizes sigma delta.referent
      (d.open (.var y)))
    (firstIH : PossibleAllocation sigma y S first)
    (memberIH : RealizesAllocation sigma delta.referent
      (d.open (.var y)) member) :
    PossibleAllocation sigma x (.Pair S a d)
      (.pair binding first member) :=
  fun v vv => by
    refine .pair (.there binding) (firstIH v vv) ?_
    rw [Def.referent_weaken]
    simpa only [Tm.weaken, Tm.rename,
      Tau.weaken, Tau.open_rename, Path.weaken, Path.rename] using
      memberIH v vv

private noncomputable def allocatePossibleSingle
    (resolution : Path.Resolve p sigma (.loc x)) :
    PossibleAllocation sigma x (.Single p) (.single resolution) :=
  fun v vv => .single (resolution.weaken v vv)

private noncomputable def allocatePossibleSelection
    (resolution : Path.Resolve (p.sel A) sigma (.type W))
    (witness : Store.Possible sigma x W)
    (witnessIH : PossibleAllocation sigma x W witness) :
    PossibleAllocation sigma x (.TSel p A)
      (.selection resolution witness) :=
  fun v vv => .selection (resolution.weaken v vv) (witnessIH v vv)

private noncomputable def allocateRealizesLoc
    (possible : Store.Possible sigma x T)
    (possibleIH : PossibleAllocation sigma x T possible) :
    RealizesAllocation sigma (.loc x) (.ty T) (.loc possible) :=
  fun v vv => .loc (possibleIH v vv)

private noncomputable def allocateRealizesType
    (lower : Coercion sigma (.ty L) (.ty W))
    (upper : Coercion sigma (.ty W) (.ty U))
    (lowerIH : CoercionAllocation sigma (.ty L) (.ty W) lower)
    (upperIH : CoercionAllocation sigma (.ty W) (.ty U) upper) :
    RealizesAllocation sigma (.type W) (.intv L U)
      (.type lower upper) :=
  fun v vv => .type (lowerIH v vv) (upperIH v vv)

private noncomputable def allocateCoercionRefl :
    CoercionAllocation sigma d d .refl :=
  fun _ _ => .refl

private noncomputable def allocateCoercionTrans
    (first : Coercion sigma d1 d2) (second : Coercion sigma d2 d3)
    (firstIH : CoercionAllocation sigma d1 d2 first)
    (secondIH : CoercionAllocation sigma d2 d3 second) :
    CoercionAllocation sigma d1 d3 (.trans first second) :=
  fun v vv => .trans (firstIH v vv) (secondIH v vv)

private noncomputable def allocateCoercionRuntime
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma) d1 d2) :
    CoercionAllocation sigma d1 d2 (.runtime conversion) :=
  fun v vv => .runtime (conversion.weaken v vv)

private noncomputable def allocateCoercionBot :
    CoercionAllocation sigma (.ty .Bot) (.ty T) .bot :=
  fun _ _ => .bot

private noncomputable def allocateCoercionTop :
    CoercionAllocation sigma (.ty T) (.ty .Top) .top :=
  fun _ _ => .top

private noncomputable def allocateCoercionWiden
    (resolution : Path.Resolve p sigma (.loc x))
    (possible : Store.Possible sigma x T)
    (possibleIH : PossibleAllocation sigma x T possible) :
    CoercionAllocation sigma (.ty (.Single p)) (.ty T)
      (.widen resolution possible) :=
  fun v vv => .widen (resolution.weaken v vv) (possibleIH v vv)

private noncomputable def allocateCoercionAlias
    (left : Path.Resolve p sigma (.loc x))
    (right : Path.Resolve q sigma (.loc x)) :
    CoercionAllocation sigma (.ty (.Single q)) (.ty (.Single p))
      (.alias left right) :=
  fun v vv => .alias (left.weaken v vv) (right.weaken v vv)

private noncomputable def allocateCoercionSelLo
    (resolution : Path.Resolve (p.sel A) sigma (.type W))
    (lower : Coercion sigma (.ty L) (.ty W))
    (lowerIH : CoercionAllocation sigma (.ty L) (.ty W) lower) :
    CoercionAllocation sigma (.ty L) (.ty (.TSel p A))
      (.selLo resolution lower) :=
  fun v vv => .selLo (resolution.weaken v vv) (lowerIH v vv)

private noncomputable def allocateCoercionSelHi
    (resolution : Path.Resolve (p.sel A) sigma (.type W))
    (upper : Coercion sigma (.ty W) (.ty U))
    (upperIH : CoercionAllocation sigma (.ty W) (.ty U) upper) :
    CoercionAllocation sigma (.ty (.TSel p A)) (.ty U)
      (.selHi resolution upper) :=
  fun v vv => .selHi (resolution.weaken v vv) (upperIH v vv)

private noncomputable def allocateCoercionFun
    (domain : Coercion sigma (.ty S') (.ty S))
    (codomain : DeferredCoercion sigma S' T T')
    (domainIH : CoercionAllocation sigma (.ty S') (.ty S) domain)
    (codomainIH : DeferredAllocation sigma S' T T' codomain) :
    CoercionAllocation sigma (.ty (.Fun S T)) (.ty (.Fun S' T'))
      (.fun domain codomain) :=
  fun v vv => .fun (domainIH v vv) (codomainIH v vv)

private noncomputable def allocateCoercionPair
    (first : Coercion sigma (.ty S) (.ty S'))
    (member : MemberClosure sigma S d d')
    (firstIH : CoercionAllocation sigma (.ty S) (.ty S') first)
    (memberIH : MemberAllocation sigma S d d' member) :
    CoercionAllocation sigma
      (.ty (.Pair S a d)) (.ty (.Pair S' a d'))
      (.pair first member) :=
  fun v vv => .pair (firstIH v vv) (memberIH v vv)

private noncomputable def allocateCoercionBounds
    (lower : Coercion sigma (.ty S') (.ty S))
    (upper : Coercion sigma (.ty T) (.ty T'))
    (lowerIH : CoercionAllocation sigma (.ty S') (.ty S) lower)
    (upperIH : CoercionAllocation sigma (.ty T) (.ty T') upper) :
    CoercionAllocation sigma (.intv S T) (.intv S' T')
      (.bounds lower upper) :=
  fun v vv => .bounds (lowerIH v vv) (upperIH v vv)

private noncomputable def allocateDeferredRefl :
    DeferredAllocation sigma S T T .refl :=
  fun _ _ => .refl

private noncomputable def allocateDeferredTrans
    (first : DeferredCoercion sigma S T U)
    (second : DeferredCoercion sigma S U V)
    (firstIH : DeferredAllocation sigma S T U first)
    (secondIH : DeferredAllocation sigma S U V second) :
    DeferredAllocation sigma S T V (.trans first second) :=
  fun v vv => .trans (firstIH v vv) (secondIH v vv)

private noncomputable def allocateDeferredRuntime
    (conversion : Tau.RuntimeConv
      (Path.ScopedLift (Path.RuntimeEq sigma)) (.ty T) (.ty U)) :
    DeferredAllocation sigma S T U (.runtime conversion) :=
  fun v vv => .runtime (conversion.weakenScoped v vv)

private noncomputable def allocateDeferredNarrow
    (domain : Coercion sigma (.ty S') (.ty S))
    (codomain : DeferredCoercion sigma S T U)
    (domainIH : CoercionAllocation sigma (.ty S') (.ty S) domain)
    (codomainIH : DeferredAllocation sigma S T U codomain) :
    DeferredAllocation sigma S' T U (.narrow domain codomain) :=
  fun v vv => .narrow (domainIH v vv) (codomainIH v vv)

private noncomputable def allocateDeferredSource
    (environment : Environment Gamma rho sigma)
    (code : Tau.Sub (Gamma.snoc S) (.ty T) (.ty U))
    (environmentIH : EnvironmentAllocation Gamma rho sigma environment) :
    DeferredAllocation sigma (S.rename rho)
      (T.rename rho.ext) (U.rename rho.ext)
      (.source environment code) :=
  fun v vv => by
    simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
      Ty.rename_rename, FinFun.ext_comp] using
      DeferredCoercion.source (environmentIH v vv) code

private noncomputable def allocateMemberSource
    (environment : Environment Gamma rho sigma)
    (code : Tau.Sub (Gamma.snoc S) d d')
    (environmentIH : EnvironmentAllocation Gamma rho sigma environment) :
    MemberAllocation sigma (S.rename rho)
      (d.rename rho.ext) (d'.rename rho.ext)
      (.source environment code) :=
  fun v vv => by
    simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
      Ty.rename_rename, Tau.rename_rename, FinFun.ext_comp] using
      MemberClosure.source (environmentIH v vv) code

private noncomputable def allocateBodySource
    (environment : Environment Gamma rho sigma)
    (code : Tm.Ty (Gamma.snoc S) body T)
    (environmentIH : EnvironmentAllocation Gamma rho sigma environment) :
    BodyAllocation sigma (S.rename rho)
      (body.rename rho.ext) (T.rename rho.ext)
      (.source environment code) :=
  fun v vv => by
    simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
      Ty.rename_rename, Tm.rename_rename, FinFun.ext_comp] using
      BodyClosure.source (environmentIH v vv) code

local macro "allocationRec(" recursor:term ")" : term =>
  `($recursor
      (motive_1 := EnvironmentAllocation)
      (motive_2 := PossibleAllocation)
      (motive_3 := RealizesAllocation)
      (motive_4 := CoercionAllocation)
      (motive_5 := DeferredAllocation)
      (motive_6 := MemberAllocation)
      (motive_7 := BodyAllocation)
      allocateEnvironmentIntro
      allocatePossibleTop allocatePossibleFun allocatePossiblePair
      allocatePossibleSingle allocatePossibleSelection
      allocateRealizesLoc allocateRealizesType
      allocateCoercionRefl allocateCoercionTrans allocateCoercionRuntime
      allocateCoercionBot allocateCoercionTop allocateCoercionWiden
      allocateCoercionAlias allocateCoercionSelLo allocateCoercionSelHi
      allocateCoercionFun allocateCoercionPair allocateCoercionBounds
      allocateDeferredRefl allocateDeferredTrans allocateDeferredRuntime
      allocateDeferredNarrow allocateDeferredSource
      allocateMemberSource allocateBodySource)

/-- An executable coercion between old types survives allocation. -/
noncomputable def Coercion.weaken
    {m : Nat} {k : Kind} {sigma : Store m} {d1 d2 : Tau m k}
    (evidence : Coercion sigma d1 d2)
    (v : Tm m) (vv : v.IsValue) :
    Coercion (Store.val sigma v vv) d1.weaken d2.weaken :=
  allocationRec(Coercion.rec) evidence v vv

/-- A source body closure survives allocation in its ambient store. -/
noncomputable def BodyClosure.weaken
    {m : Nat} {sigma : Store m} {S : Ty m}
    {body : Tm (m + 1)} {T : Ty (m + 1)}
    (evidence : BodyClosure sigma S body T)
    (v : Tm m) (vv : v.IsValue) :
    BodyClosure (Store.val sigma v vv) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext) :=
  allocationRec(BodyClosure.rec) evidence v vv

end
end LambdaPFC
