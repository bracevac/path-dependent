import LambdaPCC.CaptureTyping

/-!
Interpretation of source typing in the capture-aware runtime invariant.
Result types and use sets are interpreted together; source subsumption becomes
an explicit type coercion and a runtime subcapturing edge.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-- Interpret a source typing derivation in a valid capture-aware world. -/
noncomputable def Tm.Ty.interpret
    {n m : Nat} {Gamma : Ctx n} {term : Tm n}
    {T : LambdaPCC.Ty n} {C : CaptureSet n}
    {rho : Valuation n m} {sigma : Store m} {world : World sigma}
    (code : LambdaPCC.Tm.Ty Gamma term T C)
    (environment : Environment world Gamma rho)
    (valid : World.Valid world) :
    TermEvidence valid (term.rename rho) (T.rename rho) (C.rename rho) := by
  induction code with
  | path pathCode =>
      obtain ⟨referent, resolution, realizes⟩ :=
        Cap.Path.Ty.resolve environment pathCode
      cases realizes with
      | loc possible =>
          simpa [Tm.rename, LambdaPCC.Ty.rename, Shape.rename,
            CaptureSet.rename, Path.rename] using
            TermEvidence.path (valid := valid) resolution
              (TyCoercion.refl (world := world))
              (Relation.refl (world := world))
  | abs body domain captures ihBody =>
      simpa [Tm.rename, LambdaPCC.Ty.rename, Shape.rename,
        CaptureSet.rename] using
        TermEvidence.value (valid := valid)
          (Value.abs (by
              simpa only [CaptureSet.rename, Path.rename,
                ← CaptureSet.weaken_rename] using
                Body.source environment body)
            (TyCoercion.refl (world := world)))
          (Relation.refl (world := world))
  | app function argument ihFunction ihArgument =>
      simpa only [Tm.rename, LambdaPCC.Ty.rename, Shape.rename,
        CaptureSet.rename, Ty.open_rename] using
        TermEvidence.app (ihFunction environment)
          (ihArgument environment)
          (TyCoercion.refl (world := world))
          (Relation.refl (world := world))
  | pair =>
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename,
        Tau.rename, CaptureSet.rename, Path.rename,
        ← Path.weaken_rename] using
        TermEvidence.value (valid := valid)
          (Value.pair (world := world) rfl
            (TyCoercion.refl (world := world)))
          (Relation.refl (world := world))
  | type_pair member =>
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename,
        Tau.rename, CaptureSet.rename, Path.rename,
        ← Shape.weaken_rename] using
        TermEvidence.value (valid := valid)
          (Value.typePair (world := world) rfl
            (TyCoercion.refl (world := world)))
          (Relation.refl (world := world))
  | capture_pair captures =>
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename,
        Tau.rename, CaptureSet.rename, Path.rename,
        ← CaptureSet.weaken_rename] using
        TermEvidence.value (valid := valid)
          (Value.capturePair (world := world) rfl
            (TyCoercion.refl (world := world)))
          (Relation.refl (world := world))
  | «let» bound body result captures ihBound ihBody =>
      apply TermEvidence.let (ihBound environment)
      · simpa only [← Ty.weaken_rename,
          ← CaptureSet.weaken_rename] using
          Body.source environment body
      · exact TyCoercion.refl (world := world)
      · exact Relation.refl (world := world)
  | sub term subtype subcapture wfType wfCapture ihTerm =>
      exact ((ihTerm environment).castType
        (Cap.Ty.Sub.compile environment subtype)).castUse
          (Cap.CaptureSet.Sub.compile environment subcapture)

/-- Instantiate a suspended source body with a realized runtime location. -/
noncomputable def Body.apply
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S : Ty n} {body : Tm (n + 1)}
    {T : Ty (n + 1)} {C : CaptureSet (n + 1)}
    (closure : Body world S body T C)
    {x : Fin n} (argument : LocationEvidence world x S) :
    TermEvidence valid (body.open x) (T.open (.var x))
      (C.open (.var x)) := by
  cases closure with
  | source environment code =>
      have interpreted := Cap.Tm.Ty.interpret code
        (environment.snoc argument) valid
      simpa only [Tm.open, Tm.rename_ext_openAt,
        ← Ty.rename_openAt_eq_open_var, Ty.rename_ext_openAt,
        ← CaptureSet.rename_openAt_eq_open_var,
        CaptureSet.rename_ext_openAt] using interpreted

end
end Cap
end LambdaPCC
