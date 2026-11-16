import Coercions.Selective.Bridge.Encode

/-!
# Forward preservation

Every F-sub primitive step is one primitive step of `H` (`prim_preserved`): the
bound step `X ≤₀ Γ(X)` becomes `P-SelU` through the declared type
`{A : ⊥ .. ⟦Γ(X)⟧}`; arrows and universals become `P-All`, the universal's bound
comparison through `P-Typ` with the lower bound `⊥` compared by reflexivity.
Hence a typed F-sub certificate encodes to a typed `H` certificate with the
encoded endpoints (`cert_preserved`), built from `step` and `;` only
(`encCert_stepOnly`). The corollaries are the forward agreement of the two
checkers (`synthC_preserved`) and the passage from declarative F-sub to
DOT-MNF subtyping (`sub_preserved`), through `SelFsub.coercion_iff` and
`Selective.coercion_sound`.

The last section transports the F-sub nontransitivity witness
`Y <: Top → Top, X <: Y`.
-/

namespace Bridge

open FCdot (Kind Sig BVar Rename Label)

theorem prim_preserved {n : Nat} {Γ : SelFsub.Ctx n} {S T : SelFsub.Ty n}
    (h : SelFsub.Prim Γ S T) : Selective.Prim (encCtx Γ) (enc S) (enc T) := by
  induction h with
  | refl => exact .refl
  | top => exact .top
  | bound x =>
    exact .selU (x := bv x) (L := .bot) (by rw [encCtx_lookup]; exact .typ)
  | arr _ _ i₁ i₂ => exact .all i₁ (i₂.weaken _)
  | all _ _ i₁ i₂ => exact .all (.typ .refl i₁) i₂

theorem cert_preserved {n : Nat} {Γ : SelFsub.Ctx n} {c : SelFsub.Cert n} {S T : SelFsub.Ty n}
    (h : SelFsub.CTy Γ c S T) : Selective.CTy (encCtx Γ) (encCert c) (enc S) (enc T) := by
  induction h with
  | step h => exact .step (prim_preserved h)
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

/-- An encoded certificate has no positioned step and therefore no atom. -/
theorem encCert_stepOnly {n : Nat} (c : SelFsub.Cert n) : (encCert c).StepOnly := by
  induction c with
  | step => exact .step
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

/-- Checker agreement, forward: what the F-sub checker accepts, `H`'s checker
accepts after encoding, with the encoded endpoints. -/
theorem synthC_preserved {n : Nat} {Γ : SelFsub.Ctx n} {c : SelFsub.Cert n}
    {S T : SelFsub.Ty n} (h : SelFsub.synthC Γ c = some (S, T)) :
    Selective.synthC (encCtx Γ) (encCert c) = some (enc S, enc T) :=
  Selective.synthC_iff.mpr (cert_preserved (SelFsub.synthC_iff.mp h))

/-- Coercion existence, forward, with a step/seq-only witness. -/
theorem coercion_preserved {n : Nat} {Γ : SelFsub.Ctx n} {S T : SelFsub.Ty n}
    (h : ∃ c, SelFsub.CTy Γ c S T) :
    ∃ c : Selective.Cert (sig n), c.StepOnly ∧ Selective.CTy (encCtx Γ) c (enc S) (enc T) :=
  let ⟨c, hc⟩ := h
  ⟨encCert c, encCert_stepOnly c, cert_preserved hc⟩

/-- Declarative F-sub subtyping gives DOT-MNF subtyping of the encodings. -/
theorem sub_preserved {n : Nat} {Γ : SelFsub.Ctx n} {S T : SelFsub.Ty n}
    (h : SelFsub.Sub Γ S T) : Nonempty (DotMNF.Sub (encCtx Γ) (enc S) (enc T)) := by
  obtain ⟨c, hc⟩ := SelFsub.coercion_iff.mpr ⟨h⟩
  exact Selective.coercion_sound (cert_preserved hc)

/-! ## The nontransitivity witness, transported

`Y <: Top → Top, X <: Y` encodes to `y : {A : ⊥ .. ∀(_ : ⊤) ⊤}, x : {A : ⊥ .. y.A}`. -/

theorem encCtx_YX :
    encCtx SelFsub.ctxYX =
      .cons (.cons .nil (.typ Selective.lA .bot (.all .top .top)))
        (.typ Selective.lA .bot (.sel (.var .here) Selective.lA)) := rfl

theorem enc_YX_types :
    enc (.var 0 : SelFsub.Ty 2) = .sel (.var .here) Selective.lA ∧
    enc (.var 1 : SelFsub.Ty 2) = .sel (.var (.there .here)) Selective.lA ∧
    enc (.arr .top .top : SelFsub.Ty 2) = .all .top .top := ⟨rfl, rfl, rfl⟩

/-- `x.A ≤₀ y.A`. -/
theorem YX_XY : Selective.Prim (encCtx SelFsub.ctxYX) (enc (.var 0)) (enc (.var 1)) :=
  prim_preserved SelFsub.ctxYX_XY

/-- `y.A ≤₀ ∀(_ : ⊤) ⊤`. -/
theorem YX_Y : Selective.Prim (encCtx SelFsub.ctxYX) (enc (.var 1)) (enc (.arr .top .top)) :=
  prim_preserved SelFsub.ctxYX_Y

/-- The composite `x.A ≤₀ ∀(_ : ⊤) ⊤` fails, decided by `Selective.prim?`. -/
theorem YX_checker :
    Selective.prim? (encCtx SelFsub.ctxYX) (enc (.var 0)) (enc (.arr .top .top)) = false := by
  decide

theorem YX_not : ¬ Selective.Prim (encCtx SelFsub.ctxYX) (enc (.var 0)) (enc (.arr .top .top)) :=
  Selective.not_prim_of YX_checker

/-- The two-step F-sub certificate `step[X, Y] ; step[Y, Top → Top]`. -/
def certYX : SelFsub.Cert 2 := .seq (.step (.var 0) (.var 1)) (.step (.var 1) (.arr .top .top))

theorem certYX_fsub :
    SelFsub.synthC SelFsub.ctxYX certYX = some (.var 0, .arr .top .top) := by decide

/-- Its encoding checks in `H`, decided by `Selective.synthC`. -/
theorem certYX_H :
    Selective.synthC (encCtx SelFsub.ctxYX) (encCert certYX) =
      some (enc (.var 0), enc (.arr .top .top)) := by decide

/-- The same fact, obtained from `synthC_preserved`. -/
theorem certYX_H' :
    Selective.synthC (encCtx SelFsub.ctxYX) (encCert certYX) =
      some (enc (.var 0), enc (.arr .top .top)) := synthC_preserved certYX_fsub

end Bridge
