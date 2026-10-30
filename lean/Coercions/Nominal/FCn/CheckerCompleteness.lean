import Coercions.Nominal.FCn.Checker

/-!
# FCn checker completeness (plan T.8)

Completeness of the checker of `Checker.lean`, then the two equivalences of T.8, `checkTm_iff` and
`checkPath_iff`.  Completeness is one structural recursion on each typing block.  Each rule fixes
the output of its subject from the outputs of its premises, so every case reads the recursive
results, meets its side conditions by `rfl` or by its premises, and returns the conclusion of the
rule.

`LE-Bound` and `TM-Let` read `T` from `T↑` by `Ty.unweaken_iff`, and `DF-Path` reads `q` from the
singleton of `q` by `Path.unweaken_iff`.  Every position of a telescope is read by
`Telescope.get?_iff`.  The pre and post sides are functional in the direction the checker reads
them, so their completeness needs no search.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Evidence -/

mutual
theorem synthPEq_complete {Γ : Ctx s} {π : PEq s} {p q : Path s} : PEq.HasType Γ π p q → synthPEq Γ π = some (p, q)
  | .refl => by simp only [synthPEq]
  | .symm h => by simp only [synthPEq, synthPEq_complete h]
  | .trans h₁ h₂ => by
      simp only [synthPEq, synthPEq_complete h₁, synthPEq_complete h₂, ↓reduceIte]
  | .sel h => by simp only [synthPEq, synthPEq_complete h]
  | .member hP he hi => by
      simp only [synthPEq, synthPath_complete hP, synthLe_complete he, Telescope.get?_iff.2 hi,
        ↓reduceIte]
theorem synthPath_complete {Γ : Ctx s} {P : PathCo s} {T : Ty s} : PathCo.HasType Γ P T → synthPath Γ P = some T
  | .var h => by simp only [synthPath, h]
  | .sel hP hi => by
      simp only [synthPath, synthPath_complete hP, Telescope.get?_iff.2 hi, ↓reduceIte]
  | .cast hP he => by
      simp only [synthPath, synthPath_complete hP, synthLe_complete he, ↓reduceIte]
  | .alias h₀ hπ hQ => by
      simp only [synthPath, synthPath_complete h₀, synthPEq_complete hπ, synthPath_complete hQ,
        and_self, ↓reduceIte]
  | .sngl hP hπ => by
      simp only [synthPath, synthPath_complete hP, synthPEq_complete hπ, and_self,
        ↓reduceIte]
  | .fldI hQ e => by simp only [synthPath, synthPath_complete hQ, e, ↓reduceIte]
  | .unfold hP => by simp only [synthPath, synthPath_complete hP]
  | .fold hP => by simp only [synthPath, synthPath_complete hP, ↓reduceIte]
  | .both hP hQ e => by
      simp only [synthPath, synthPath_complete hP, synthPath_complete hQ, e, and_self, ↓reduceIte]
theorem synthLe_complete {Γ : Ctx s} {e : LeCo s} {S T : Ty s} : LeCo.HasType Γ e S T → synthLe Γ e = some (S, T)
  | .refl => by simp only [synthLe]
  | .trans h₁ h₂ => by
      simp only [synthLe, synthLe_complete h₁, synthLe_complete h₂, ↓reduceIte]
  | .top => by simp only [synthLe]
  | .bot => by simp only [synthLe]
  | .eqToLe h => by simp only [synthLe, synthEq_complete h]
  | .pi he hf => by simp only [synthLe, synthLe_complete he, synthLe_complete hf]
  | .obj hm => by simp only [synthLe, synthMor_complete hm]
  | .pair he hf => by
      simp only [synthLe, synthLe_complete he, synthLe_complete hf, and_self, ↓reduceIte]
  | .bound hi => by simp only [synthLe, Telescope.get?_iff.2 hi, Ty.unweaken_iff.2 rfl]
  | .intoBnd he => by simp only [synthLe, synthLe_complete he]
  | .member hP he hi => by
      simp only [synthLe, synthPath_complete hP, synthLe_complete he, Telescope.get?_iff.2 hi,
        ↓reduceIte]
  | .seal h => by simp only [synthLe, h, Option.map_some]
theorem synthEq_complete {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} : EqCo.HasType Γ φ S T → synthEq Γ φ = some (S, T)
  | .refl => by simp only [synthEq]
  | .symm h => by simp only [synthEq, synthEq_complete h]
  | .trans h₁ h₂ => by
      simp only [synthEq, synthEq_complete h₁, synthEq_complete h₂, ↓reduceIte]
  | .defP h => by simp only [synthEq, h]
  | .lift h => by simp only [synthEq, synthPEq_complete h]
  | .dom h => by simp only [synthEq, synthEq_complete h]
  | .cod h => by simp only [synthEq, synthEq_complete h]
theorem synthMor_complete {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s} : Morphism.HasType Γ src m Tel → synthMor Γ src m = some Tel
  | .nil => by simp only [synthMor]
  | .le hm hj hpre hpost => by
      simp only [synthMor, synthMor_complete hm, Telescope.get?_iff.2 hj, synthPre_complete hpre,
        synthPost_complete hpost]
  | .fld hm hj hsd => by
      simp only [synthMor, synthMor_complete hm, Telescope.get?_iff.2 hj, synthPost_complete hsd]
  | .alias hm hj => by simp only [synthMor, synthMor_complete hm, Telescope.get?_iff.2 hj]
  | .is hm he => by
      simp only [synthMor, synthMor_complete hm, synthLe_complete he, ↓reduceIte]
theorem synthPre_complete {Γ : Ctx s} {sd : Side s} {S X : Ty (s,x)} : Side.HasType Γ sd S X → synthPre Γ sd X = some S
  | .none => by simp only [synthPre]
  | .some he => by simp only [synthPre, synthLe_complete he, ↓reduceIte]
  | .bot => by simp only [synthPre, ↓reduceIte]
  | .top => by simp only [synthPre, ↓reduceIte]
theorem synthPost_complete {Γ : Ctx s} {sd : Side s} {Y T : Ty (s,x)} : Side.HasType Γ sd Y T → synthPost Γ sd Y = some T
  | .none => by simp only [synthPost]
  | .some he => by simp only [synthPost, synthLe_complete he, ↓reduceIte]
  | .bot => by simp only [synthPost, ↓reduceIte]
  | .top => by simp only [synthPost, ↓reduceIte]
end

/-! ## Terms, values, definitions -/

mutual
theorem synthTm_complete {Γ : Ctx s} {t : Tm s} {T : Ty s} : Tm.HasType Γ t T → synthTm Γ t = some T
  | .path h => by simp only [synthTm, synthPath_complete h]
  | .val h => by simp only [synthTm, synthValue_complete h]
  | .app hP hQ => by
      simp only [synthTm, synthPath_complete hP, synthPath_complete hQ, ↓reduceIte]
  | .lett ht hu => by
      simp only [synthTm, synthTm_complete ht, synthTm_complete hu]
      exact Ty.unweaken_iff.2 rfl
  | .cast ht he => by
      simp only [synthTm, synthTm_complete ht, synthLe_complete he, ↓reduceIte]
theorem synthValue_complete {Γ : Ctx s} {v : Value s} {T : Ty s} : Value.HasType Γ v T → synthValue Γ v = some T
  | .lam h => by simp only [synthValue, synthTm_complete h]
  | .obj h => by simp only [synthValue, checkDefs_complete h, ↓reduceIte]
  | .cast hv he => by
      simp only [synthValue, synthValue_complete hv, synthLe_complete he, ↓reduceIte]
theorem checkDefs_complete {Γ : Ctx s} {p : Path s} {ds : Defs s} {Tel : Telescope (s,x)} : Defs.HasType Γ p ds Tel → checkDefs Γ p ds Tel = true
  | .nil => by simp only [checkDefs]
  | .typ hds hA hU => by
      simp only [checkDefs, checkDefs_complete hds, Bool.and_true]
      exact decide_eq_true ⟨trivial, trivial, trivial, hA, hU⟩
  | .cls hds hC hU => by
      simp only [checkDefs, checkDefs_complete hds, Bool.and_true]
      exact decide_eq_true ⟨trivial, trivial, trivial, hC, hU⟩
  | .path hds ha hP hq => by
      simp only [checkDefs, Ty.sngl, Path.unweaken_iff.2 rfl, synthPath_complete hP,
        checkDefs_complete hds, Bool.and_true]
      exact decide_eq_true ⟨trivial, ha, hq⟩
  | .fn hds ha hl hv => by
      simp only [checkDefs, synthValue_complete hv, checkDefs_complete hds, Bool.and_true]
      exact Bool.and_eq_true_iff.2 ⟨decide_eq_true ⟨trivial, ha, hl⟩, decide_eq_true trivial⟩
  | .nest hds ha hds' => by
      simp only [checkDefs, checkDefs_complete hds, checkDefs_complete hds', Bool.and_true]
      exact decide_eq_true ⟨trivial, ha, trivial⟩
end

/-! ## The equivalences of T.8 -/

theorem synthPath_iff {Γ : Ctx s} {P : PathCo s} {T : Ty s} : synthPath Γ P = some T ↔ PathCo.HasType Γ P T :=
  ⟨synthPath_sound, synthPath_complete⟩
theorem synthTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} : synthTm Γ t = some T ↔ Tm.HasType Γ t T :=
  ⟨synthTm_sound, synthTm_complete⟩
theorem checkPath_iff {Γ : Ctx s} {P : PathCo s} {T : Ty s} : checkPath Γ P T = true ↔ PathCo.HasType Γ P T :=
  decide_eq_true_iff.trans synthPath_iff
theorem checkTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} : checkTm Γ t T = true ↔ Tm.HasType Γ t T :=
  decide_eq_true_iff.trans synthTm_iff

end Nominal.FCn
