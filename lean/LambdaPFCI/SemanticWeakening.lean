import LambdaPFCI.SemanticEvidence

/-!
Allocation weakening for semantic evidence.  Allocating a fresh value shifts
all existing store locations.  Evidence below a source binder is renamed by
the lifted weakening, which leaves the bound variable fixed while shifting
the locations supplied by the enclosing environment.
-/

namespace LambdaPFCI

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

/-! ## Allocation weakening

All seven semantic evidence families survive allocation, by one structural
mutual recursion over the evidence. -/

mutual

/-- A semantic environment survives allocation in its ambient store. -/
noncomputable def Environment.weaken
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m} {sigma : Store m}
    (environment : Environment Gamma rho sigma)
    (v : Tm m) (vv : v.IsValue) :
    Environment Gamma rho.weaken (Store.val sigma v vv) :=
  match environment with
  | .intro lookup =>
      .intro fun x => by
        simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
          Ty.rename_rename] using (lookup x).weaken v vv

/-- A store observation survives allocation. -/
noncomputable def Store.Possible.weaken
    {m : Nat} {sigma : Store m} {x : Fin m} {T : Ty m}
    (possible : Store.Possible sigma x T)
    (v : Tm m) (vv : v.IsValue) :
    Store.Possible (Store.val sigma v vv) x.succ T.weaken :=
  match possible with
  | .top => .top
  | .inter left right =>
      .inter (left.weaken v vv) (right.weaken v vv)
  | .fun binding closure domain codomain =>
      .fun (.there binding) (closure.weaken v vv)
        (domain.weaken v vv) (codomain.weaken v vv)
  | .pair binding first member => by
      refine .pair (.there binding) (first.weaken v vv) ?_
      rw [Def.referent_weaken]
      simpa only [Tm.weaken, Tm.rename, Tau.weaken, Tau.open_rename,
        Path.weaken, Path.rename] using member.weaken v vv
  | .single resolution => .single (resolution.weaken v vv)
  | .selection resolution witness =>
      .selection (resolution.weaken v vv) (witness.weaken v vv)

/-- A referent realization survives allocation. -/
noncomputable def Path.Referent.Realizes.weaken
    {m : Nat} {k : Kind} {sigma : Store m}
    {referent : Path.Referent m} {d : Tau m k}
    (realizes : Path.Referent.Realizes sigma referent d)
    (v : Tm m) (vv : v.IsValue) :
    Path.Referent.Realizes (Store.val sigma v vv)
      referent.weaken d.weaken :=
  match realizes with
  | .loc possible => .loc (possible.weaken v vv)
  | .type lower upper => .type (lower.weaken v vv) (upper.weaken v vv)

/-- An executable coercion between old types survives allocation. -/
noncomputable def Coercion.weaken
    {m : Nat} {k : Kind} {sigma : Store m} {d1 d2 : Tau m k}
    (evidence : Coercion sigma d1 d2)
    (v : Tm m) (vv : v.IsValue) :
    Coercion (Store.val sigma v vv) d1.weaken d2.weaken :=
  match evidence with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken v vv) (second.weaken v vv)
  | .runtime conversion => .runtime (conversion.weaken v vv)
  | .bot => .bot
  | .top => .top
  | .inter left right =>
      .inter (left.weaken v vv) (right.weaken v vv)
  | .interLeft => .interLeft
  | .interRight => .interRight
  | .pairInter => .pairInter
  | .widen resolution possible =>
      .widen (resolution.weaken v vv) (possible.weaken v vv)
  | .alias left right =>
      .alias (left.weaken v vv) (right.weaken v vv)
  | .selLo resolution lower =>
      .selLo (resolution.weaken v vv) (lower.weaken v vv)
  | .selHi resolution upper =>
      .selHi (resolution.weaken v vv) (upper.weaken v vv)
  | .fun domain codomain =>
      .fun (domain.weaken v vv) (codomain.weaken v vv)
  | .pair first member =>
      .pair (first.weaken v vv) (member.weaken v vv)
  | .bounds lower upper =>
      .bounds (lower.weaken v vv) (upper.weaken v vv)

/-- An open codomain coercion survives allocation. -/
noncomputable def DeferredCoercion.weaken
    {m : Nat} {sigma : Store m} {S : Ty m} {T U : Ty (m + 1)}
    (deferred : DeferredCoercion sigma S T U)
    (v : Tm m) (vv : v.IsValue) :
    DeferredCoercion (Store.val sigma v vv) S.weaken
      (T.rename FinFun.weaken.ext) (U.rename FinFun.weaken.ext) :=
  match deferred with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken v vv) (second.weaken v vv)
  | .runtime conversion => .runtime (conversion.weakenScoped v vv)
  | .narrow domain rest =>
      .narrow (domain.weaken v vv) (rest.weaken v vv)
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, FinFun.ext_comp] using
        DeferredCoercion.source (environment.weaken v vv) code

/-- A suspended member comparison survives allocation. -/
noncomputable def MemberClosure.weaken
    {m : Nat} {sigma : Store m} {S : Ty m} {k : Kind}
    {d d' : Tau (m + 1) k}
    (member : MemberClosure sigma S d d')
    (v : Tm m) (vv : v.IsValue) :
    MemberClosure (Store.val sigma v vv) S.weaken
      (d.rename FinFun.weaken.ext) (d'.rename FinFun.weaken.ext) :=
  match member with
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, Tau.rename_rename, FinFun.ext_comp] using
        MemberClosure.source (environment.weaken v vv) code

/-- A source body closure survives allocation in its ambient store. -/
noncomputable def BodyClosure.weaken
    {m : Nat} {sigma : Store m} {S : Ty m}
    {body : Tm (m + 1)} {T : Ty (m + 1)}
    (closure : BodyClosure sigma S body T)
    (v : Tm m) (vv : v.IsValue) :
    BodyClosure (Store.val sigma v vv) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext) :=
  match closure with
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, Tm.rename_rename, FinFun.ext_comp] using
        BodyClosure.source (environment.weaken v vv) code

end

end

end LambdaPFCI
