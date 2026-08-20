import LambdaPCCI.CaptureEvidence

/-!
Allocation weakening for capture-aware semantic evidence. A fresh store cell
extends the semantic world with the assigned capture set of the allocated
value; all earlier locations and all evidence about them are shifted by the
same intrinsic renaming.
-/

namespace LambdaPCCI
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

/-! ## Allocation weakening

All eleven semantic evidence families survive allocation by one structural
mutual recursion over the evidence. -/

mutual

/-- A semantic environment survives allocation in its ambient world. -/
noncomputable def Environment.weaken
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m}
    (evidence : Environment world Gamma rho)
    {v : Tm m} {Q : CaptureSet m}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Environment (World.val world exact (vv := vv)) Gamma rho.weaken :=
  match evidence with
  | .intro lookup =>
      .intro fun x => by
        simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
          Ty.rename_rename] using (lookup x).weaken exact vv

/-- Evidence for an existing location survives allocation. -/
noncomputable def LocationEvidence.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {T : Ty n} (evidence : LocationEvidence world x T)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    LocationEvidence (World.val world exact (vv := vv)) x.succ T.weaken :=
  match evidence with
  | .top lookup coverage =>
      .top (lookup.weaken exact vv) (coverage.weaken exact vv)
  | .inter left right =>
      .inter (left.weaken exact vv) (right.weaken exact vv)
  | .fun lookup closure input output coverage => by
      apply LocationEvidence.fun (lookup.weaken exact vv)
      · simpa only [CaptureSet.rename, Path.rename,
          ← CaptureSet.weaken_rename] using closure.weaken exact vv
      · exact input.weaken exact vv
      · exact output.weaken exact vv
      · exact coverage.weaken exact vv
  | .pair lookup first member coverage => by
      apply LocationEvidence.pair (lookup.weaken exact vv)
        (first.weaken exact vv)
      · rw [Def.referent_weaken]
        simpa only [Tau.weaken, Tau.open_rename, Path.weaken,
          Path.rename] using member.weaken exact vv
      · exact coverage.weaken exact vv
  | .single lookup resolution coverage =>
      .single (lookup.weaken exact vv) (resolution.weaken _ vv)
        (coverage.weaken exact vv)
  | .selection lookup resolution witness coverage =>
      .selection (lookup.weaken exact vv) (resolution.weaken _ vv)
        (witness.weaken exact vv) (coverage.weaken exact vv)

/-- Realization evidence for an existing referent survives allocation. -/
noncomputable def Realizes.weaken
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {referent : Path.Referent n} {d : Tau n k}
    (evidence : Realizes world referent d)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Realizes (World.val world exact (vv := vv)) referent.weaken d.weaken :=
  match evidence with
  | .loc possible => .loc (possible.weaken exact vv)
  | .type lower upper =>
      .type (lower.weaken exact vv) (upper.weaken exact vv)
  | .capture lower upper =>
      .capture (lower.weaken exact vv) (upper.weaken exact vv)

/-- Subcapturing evidence survives allocation. -/
noncomputable def Relation.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {C D : CaptureSet n} (evidence : Relation world C D)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Relation (World.val world exact (vv := vv)) C.weaken D.weaken :=
  match evidence with
  | .source environment code => by
      simpa only [Valuation.weaken, CaptureSet.weaken,
        CaptureSet.rename_rename] using
        Relation.source (environment.weaken exact vv) code
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken exact vv) (second.weaken exact vv)
  | .runtime conversion => .runtime (conversion.weaken _ vv)
  | .empty => .empty
  | .unionLeft => .unionLeft
  | .unionRight => .unionRight
  | .unionElim left right =>
      .unionElim (left.weaken exact vv) (right.weaken exact vv)
  | .alias left right =>
      .alias (left.weaken _ vv) (right.weaken _ vv)
  | .fold resolution lookup =>
      .fold (resolution.weaken _ vv) (lookup.weaken exact vv)
  | .fstRoot resolution => .fstRoot (resolution.weaken _ vv)
  | .selRoot resolution => .selRoot (resolution.weaken _ vv)
  | .selectLower resolution lower =>
      .selectLower (resolution.weaken _ vv) (lower.weaken exact vv)
  | .selectUpper resolution upper =>
      .selectUpper (resolution.weaken _ vv) (upper.weaken exact vv)

/-- A coercion between capturing types survives allocation. -/
noncomputable def TyCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {T U : Ty n} (evidence : TyCoercion world T U)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    TyCoercion (World.val world exact (vv := vv)) T.weaken U.weaken :=
  match evidence with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken exact vv) (second.weaken exact vv)
  | .runtime conversion => .runtime (conversion.weaken _ vv)
  | .capt captures shape =>
      .capt (captures.weaken exact vv) (shape.weaken exact vv)

/-- A shape coercion survives allocation. -/
noncomputable def ShapeCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S T : Shape n} (evidence : ShapeCoercion world S T)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    ShapeCoercion (World.val world exact (vv := vv)) S.weaken T.weaken :=
  match evidence with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken exact vv) (second.weaken exact vv)
  | .runtime conversion => .runtime (conversion.weaken _ vv)
  | .bot => .bot
  | .top => .top
  | .inter left right =>
      .inter (left.weaken exact vv) (right.weaken exact vv)
  | .interLeft => .interLeft
  | .interRight => .interRight
  | .pairInter => .pairInter
  | .widen resolution possible =>
      .widen (resolution.weaken _ vv) (possible.weaken exact vv)
  | .alias left right =>
      .alias (left.weaken _ vv) (right.weaken _ vv)
  | .selectLower resolution lower =>
      .selectLower (resolution.weaken _ vv) (lower.weaken exact vv)
  | .selectUpper resolution upper =>
      .selectUpper (resolution.weaken _ vv) (upper.weaken exact vv)
  | .fun domain codomain =>
      .fun (domain.weaken exact vv) (codomain.weaken exact vv)
  | .pair first member =>
      .pair (first.weaken exact vv) (member.weaken exact vv)

/-- A generalized member coercion survives allocation. -/
noncomputable def Coercion.weaken
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {d e : Tau n k} (evidence : Coercion world d e)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Coercion (World.val world exact (vv := vv)) d.weaken e.weaken :=
  match evidence with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken exact vv) (second.weaken exact vv)
  | .runtime conversion => .runtime (conversion.weaken _ vv)
  | .term types => .term (types.weaken exact vv)
  | .type lower upper =>
      .type (lower.weaken exact vv) (upper.weaken exact vv)
  | .capture lower upper =>
      .capture (lower.weaken exact vv) (upper.weaken exact vv)

/-- A suspended result coercion survives allocation. -/
noncomputable def DeferredCoercion.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {T U : Ty (n + 1)}
    (evidence : DeferredCoercion world S T U)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    DeferredCoercion (World.val world exact (vv := vv)) S.weaken
      (T.rename FinFun.weaken.ext) (U.rename FinFun.weaken.ext) :=
  match evidence with
  | .refl => .refl
  | .trans first second =>
      .trans (first.weaken exact vv) (second.weaken exact vv)
  | .runtime conversion => .runtime (conversion.weakenScoped _ vv)
  | .narrow domain codomain =>
      .narrow (domain.weaken exact vv) (codomain.weaken exact vv)
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, FinFun.ext_comp] using
        DeferredCoercion.source (environment.weaken exact vv) code

/-- A suspended member comparison survives allocation. -/
noncomputable def MemberClosure.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {k : Kind} {d e : Tau (n + 1) k}
    (evidence : MemberClosure world S d e)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    MemberClosure (World.val world exact (vv := vv)) S.weaken
      (d.rename FinFun.weaken.ext) (e.rename FinFun.weaken.ext) :=
  match evidence with
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, Tau.rename_rename, FinFun.ext_comp] using
        MemberClosure.source (environment.weaken exact vv) code

/-- A source body survives allocation in its ambient world. -/
noncomputable def Body.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {body : Tm (n + 1)} {T : Ty (n + 1)}
    {C : CaptureSet (n + 1)} (evidence : Body world S body T C)
    {v : Tm n} {Q : CaptureSet n}
    (exact : ExactValue sigma v Q) (vv : v.IsValue) :
    Body (World.val world exact (vv := vv)) S.weaken
      (body.rename FinFun.weaken.ext) (T.rename FinFun.weaken.ext)
      (C.rename FinFun.weaken.ext) :=
  match evidence with
  | .source environment code => by
      simpa only [Valuation.weaken, FinFun.comp, Ty.weaken,
        Ty.rename_rename, Tm.rename_rename, CaptureSet.rename_rename,
        FinFun.ext_comp] using Body.source (environment.weaken exact vv) code

/-- Value evidence survives allocation. -/
noncomputable def Value.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {term : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : Value world term T Q)
    {v : Tm n} {R : CaptureSet n}
    (exact : ExactValue sigma v R) (vv : v.IsValue) :
    Value (World.val world exact (vv := vv)) term.weaken T.weaken Q.weaken :=
  match value with
  | .abs closure suffix => by
      apply Value.abs
      · simpa only [CaptureSet.rename, Path.rename,
          ← CaptureSet.weaken_rename] using closure.weaken exact vv
      · exact suffix.weaken exact vv
  | .pair suffix => by
      apply Value.pair
      simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Path.weaken_rename] using
        suffix.weaken exact vv
  | .typePair suffix => by
      apply Value.typePair
      simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Shape.weaken_rename] using
        suffix.weaken exact vv
  | .capturePair suffix => by
      apply Value.capturePair
      simpa [Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using suffix.weaken exact vv

end

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
end LambdaPCCI
