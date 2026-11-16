import Coercions.Selective.Fsub.Exact
/-!
# A computable elaborator

`FDer` is the type of derivations of `FTy`, with the subsumption and bound premises
given by `Sub` derivations. `FDer.elab` is a function on derivations that returns an
annotated term: subsumption becomes a cast by `Sub.toCert`, and the bound of a type
application becomes a cast of the callee by the bound lift. Its erasure is the source
term and it is typed by `HTy`.
-/
namespace SelFsub

/-- Typing derivations of `FTy` as data. -/
inductive FDer : Ctx n → List (Ty n) → Tm n → Ty n → Type where
  | var : Δ[x]? = some T → FDer Γ Δ (.var x) T
  | lam : FDer Γ (S :: Δ) e T → FDer Γ Δ (.lam S e) (.arr S T)
  | app : FDer Γ Δ e (.arr S T) → FDer Γ Δ u S → FDer Γ Δ (.app e u) T
  | tlam : FDer (Γ.snoc S) (Δ.map Ty.weaken) e T → FDer Γ Δ (.tlam S e) (.all S T)
  | tapp : FDer Γ Δ e (.all S T) → Sub Γ U S → FDer Γ Δ (.tapp e U) (T.subst (sub0 U))
  | sub : FDer Γ Δ e S → Sub Γ S T → FDer Γ Δ e T

/-- A derivation gives a typing. -/
theorem FDer.toFTy : FDer Γ Δ e T → FTy Γ Δ e T
  | .var h => .var h
  | .lam d => .lam d.toFTy
  | .app d₁ d₂ => .app d₁.toFTy d₂.toFTy
  | .tlam d => .tlam d.toFTy
  | .tapp d s => .tapp d.toFTy s
  | .sub d s => .sub d.toFTy s

/-- A typing has a derivation. -/
theorem FTy.toFDer : FTy Γ Δ e T → Nonempty (FDer Γ Δ e T)
  | .var h => ⟨.var h⟩
  | .lam h => let ⟨d⟩ := h.toFDer; ⟨.lam d⟩
  | .app h₁ h₂ => let ⟨d₁⟩ := h₁.toFDer; let ⟨d₂⟩ := h₂.toFDer; ⟨.app d₁ d₂⟩
  | .tlam h => let ⟨d⟩ := h.toFDer; ⟨.tlam d⟩
  | .tapp h s => let ⟨d⟩ := h.toFDer; ⟨.tapp d s⟩
  | .sub h s => let ⟨d⟩ := h.toFDer; ⟨.sub d s⟩

/-- The elaborated annotated term of a derivation. -/
def FDer.elab {Γ : Ctx n} {Δ : List (Ty n)} {e : Tm n} {T : Ty n} : FDer Γ Δ e T → Tm n
  | .var (x := x) _ => .var x
  | .lam (S := S) d => .lam S d.elab
  | .app d₁ d₂ => .app d₁.elab d₂.elab
  | .tlam (S := S) d => .tlam S d.elab
  | .tapp (T := T) (U := U) d s => .tapp (.cast d.elab (s.toCert.allBound T)) U
  | .sub d s => .cast d.elab s.toCert

/-- The elaborated term erases to the source term. -/
theorem FDer.elab_erase : (d : FDer Γ Δ e T) → d.elab.erase = e
  | .var _ => rfl
  | .lam d => by simp only [FDer.elab, Tm.erase, d.elab_erase]
  | .app d₁ d₂ => by simp only [FDer.elab, Tm.erase, d₁.elab_erase, d₂.elab_erase]
  | .tlam d => by simp only [FDer.elab, Tm.erase, d.elab_erase]
  | .tapp d _ => by simp only [FDer.elab, Tm.erase, d.elab_erase]
  | .sub d _ => by simp only [FDer.elab, Tm.erase, d.elab_erase]

/-- The elaborated term is typed by `HTy`. -/
theorem FDer.elab_typed : (d : FDer Γ Δ e T) → HTy Γ Δ d.elab T
  | .var h => .var h
  | .lam d => .lam d.elab_typed
  | .app d₁ d₂ => .app d₁.elab_typed d₂.elab_typed .refl
  | .tlam d => .tlam d.elab_typed
  | .tapp d s => .tapp (.cast d.elab_typed (s.toCert_typed.allBound _)) .refl
  | .sub d s => .cast d.elab_typed s.toCert_typed

end SelFsub
