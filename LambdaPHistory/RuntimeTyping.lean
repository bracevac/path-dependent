import LambdaPHistory.RuntimeConversion
import LambdaPHistory.PathPreservation
import LambdaPHistory.TypingInversion

/-!
Typing modulo equations justified by the current store.

`Tm.RuntimeTy` is a proof invariant, not a source typing rule.  It retains an
ordinary source typing witness and permits only a top-level chain of source
subtyping and store-indexed runtime conversion.  This is already sufficient
to state and prove the historically missing preservation lemma for the
standalone path-normalization transition.
-/

namespace LambdaPHistory

/-- A term has source type `U`, and `U` is below the observed type `T` after
closing source subtyping under equations witnessed by the current store. -/
def Tm.RuntimeTy (Γ : Ctx n) (σ : Store n)
    (t : Tm n) (T : LambdaPHistory.Ty n) : Prop :=
  ∃ U, Tm.Ty Γ t U ∧
    Tau.RuntimeSub Γ σ (Tau.ty U) (Tau.ty T)

/-- Ordinary source typing embeds into runtime typing. -/
theorem Tm.RuntimeTy.of_source (h : Tm.Ty Γ t T) :
    Tm.RuntimeTy Γ σ t T :=
  ⟨T, h, .refl⟩

/-- Runtime typing composes with mixed runtime subtyping. -/
theorem Tm.RuntimeTy.sub
    (h : Tm.RuntimeTy Γ σ t S)
    (hs : Tau.RuntimeSub Γ σ (Tau.ty S) (Tau.ty T)) :
    Tm.RuntimeTy Γ σ t T := by
  obtain ⟨U, ht, hUS⟩ := h
  exact ⟨U, ht, .trans hUS hs⟩

/-- Runtime-equal paths have mutually convertible singleton types. -/
theorem Tau.RuntimeSub.single
    {n : Nat} {Γ : Ctx n} {σ : Store n} {p q : Path n}
    (h : Path.RuntimeEq σ p q) :
    Tau.RuntimeSub Γ σ
      (Tau.ty (Ty.Single p)) (Tau.ty (Ty.Single q)) := by
  have hr := Tau.RuntimeSub.replace (Gamma := Γ)
    (d := Tau.ty (Ty.Single (Path.var (0 : Fin (n + 1))))) h
  simpa [Tau.open, Tau.subst, Ty.open, Ty.subst, Path.open,
    Path.subst] using hr

/-- Source path typing followed by ordinary subsumption can be replayed as a
mixed runtime-subtyping chain from the path singleton. -/
theorem Tm.RuntimeTy.path_source
    (h : Tm.Ty Γ (Tm.path p) T) :
    Tau.RuntimeSub Γ σ
      (Tau.ty (Ty.Single p)) (Tau.ty T) :=
  .source (Tm.Ty.path_subtyping h)

/-- **Big-step path-lookup preservation.**  Replacing a path term by the
location to which it resolves preserves its runtime type.  This is the
runtime-aware form of the first missing 2024 preservation case. -/
theorem Tm.RuntimeTy.reduce_path
    (hr : Path.reduce p σ x)
    (h : Tm.RuntimeTy Γ σ (Tm.path p) T) :
    Tm.RuntimeTy Γ σ (Tm.path (Path.var x)) T := by
  obtain ⟨U, hp, hUT⟩ := h
  obtain ⟨X, hx⟩ := Ctx.Binds.exists Γ x
  refine ⟨Ty.Single (Path.var x), Tm.Ty.path (Path.Ty.var hx), ?_⟩
  have heq : Path.RuntimeEq σ (Path.var x) p :=
    (Path.RuntimeEq.of_reduce hr).symm
  exact .trans (Tau.RuntimeSub.single heq)
    (.trans (.source (Tm.Ty.path_subtyping hp)) hUT)

/-- Runtime typing weakens across store allocation. -/
theorem Tm.RuntimeTy.weaken
    {n : Nat} {Γ : Ctx n} {σ : Store n} {t : Tm n}
    {T : LambdaPHistory.Ty n}
    (h : Tm.RuntimeTy Γ σ t T)
    (S : LambdaPHistory.Ty n) (v : Tm n) (hv : v.IsValue) :
    Tm.RuntimeTy (Γ.snoc S) (Store.val σ v hv) t.weaken T.weaken := by
  obtain ⟨U, ht, hsub⟩ := h
  exact ⟨U.weaken, ht.weaken, hsub.weaken S v hv⟩

end LambdaPHistory
