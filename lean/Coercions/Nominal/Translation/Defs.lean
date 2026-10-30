import Coercions.Nominal.Translation.EvidenceTyped

/-!
# Definitions: the helpers outside the recursion (plan X, Part TR.5, stage X6 group g3)

The term translation and the definition translation are one mutual block, in `Terms` (decision D1 of
the groups file).  This module holds what that block and its typedness read from outside it.

`Translation.toValue` reads the value under the casts of a term.  The image of a lambda at
`ty_def_all` is the lambda under the casts of the `ty_sub` steps that end its derivation (TR.5), and
`toValue` takes it out (decision D8).  `Defs.labels` lists the labels of source definitions, which
`DefsTy.translate_labels` compares with the labels of the image.  `Defs.not_mem_labels_of_hasnt`
carries `ty_defs_cons`'s `ds.hasnt d.label` to the target's `a ∉ ds.labels`.

The opening inversions read an un-opened annotation off an opened one.  Each is a `cases` on the
annotation, which is syntax, and an annotation opened at `r` keeps its head constructor.  So
`T₀⟨r⟩ = T ∧ U` gives `T₀ = T₀' ∧ U₀`, and so on for a record, a type or a field declaration, a
function type, a recursive type and a singleton.  `Translation.nil_append` and `Ty.tight_rename` are
the two small laws the typedness of definitions reads.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The value under the casts of a term: `val v` gives `v`, `cast t e` the value of `t` under the
cast by `e`, and any other term none. -/
def _root_.Nominal.Translation.toValue : FCn.Tm s → Option (FCn.Value s)   -- the value under the casts of a term
  | .val v => some v                                          -- val v ↦ v
  | .cast t e => (Translation.toValue t).map (FCn.Value.cast · e)        -- cast t e ↦ cast v e
  | .path _ => none                                           -- path P: not a value
  | .app _ _ => none                                          -- app P Q: not a value
  | .lett _ _ => none                                         -- let z = t in u: not a value

/-- The labels of source definitions, the newest first. -/
def Defs.labels : Defs s → List Label                         -- the labels of source definitions
  | .nil => []                                                -- [] ↦ []
  | .cons ds d => d.label :: ds.labels                        -- ds ▹ d ↦ d's label, then the labels of ds

/-- A label no definition of `ds` has is not among `ds.labels`. -/
theorem Defs.not_mem_labels_of_hasnt : ∀ {ds : Defs s} {l : Label}, ds.hasnt l → l ∉ ds.labels
  | .nil, _, _ => List.not_mem_nil
  | .cons ds d, l, h => by
      unfold Defs.hasnt Defs.get at h
      split at h
      · exact absurd h (by simp)
      · next hne =>
          intro hm
          rcases List.mem_cons.mp hm with e | hm
          · exact hne e.symm
          · exact Defs.not_mem_labels_of_hasnt h hm

/-- An opened annotation that is an intersection was one before opening. -/
theorem Ty.substPath_eq_and {T₀ : Ty (s,x)} {r : Path s} {T U : Ty s} (h : T₀.substPath r = .and T U) :
    ∃ T₀' U₀, T₀ = .and T₀' U₀ ∧ T₀'.substPath r = T ∧ U₀.substPath r = U := by
  cases T₀ <;> try (simp [Ty.substPath, Ty.subst] at h)
  next T' U' => exact ⟨T', U', rfl, h.1, h.2⟩

/-- An opened annotation that is a record was one before opening. -/
theorem Ty.substPath_eq_rcd {T₀ : Ty (s,x)} {r : Path s} {D : Dec s} (h : T₀.substPath r = .rcd D) :
    ∃ D₀, T₀ = .rcd D₀ ∧ D₀.substPath r = D := by
  cases T₀ <;> try (simp [Ty.substPath, Ty.subst] at h)
  next D' => exact ⟨D', rfl, h⟩

/-- An opened type member declaration was one before opening, at the same label. -/
theorem Dec.substPath_eq_typ {D₀ : Dec (s,x)} {r : Path s} {A : Label} {S U : Ty s} (h : D₀.substPath r = .typ A S U) :
    ∃ S₀ U₀, D₀ = .typ A S₀ U₀ ∧ S₀.substPath r = S ∧ U₀.substPath r = U := by
  cases D₀ with
  | typ A' S' U' =>
      simp only [Dec.substPath, Dec.subst, Dec.typ.injEq] at h
      obtain ⟨rfl, h₁, h₂⟩ := h
      exact ⟨S', U', rfl, h₁, h₂⟩
  | trm _ _ => simp [Dec.substPath, Dec.subst] at h

/-- An opened field declaration was one before opening, at the same label. -/
theorem Dec.substPath_eq_trm {D₀ : Dec (s,x)} {r : Path s} {a : Label} {T : Ty s} (h : D₀.substPath r = .trm a T) :
    ∃ T₀, D₀ = .trm a T₀ ∧ T₀.substPath r = T := by
  cases D₀ with
  | typ _ _ _ => simp [Dec.substPath, Dec.subst] at h
  | trm a' T' =>
      simp only [Dec.substPath, Dec.subst, Dec.trm.injEq] at h
      obtain ⟨rfl, h₁⟩ := h
      exact ⟨T', rfl, h₁⟩

/-- An opened function type was one before opening. -/
theorem Ty.substPath_eq_all {T₀ : Ty (s,x)} {r : Path s} {U : Ty s} {V : Ty (s,x)} (h : T₀.substPath r = .all U V) :
    ∃ U₀ V₀, T₀ = .all U₀ V₀ := by
  cases T₀ <;> try (simp [Ty.substPath, Ty.subst] at h)
  next U' V' => exact ⟨U', V', rfl⟩

/-- An opened recursive type was one before opening, its body substituted under the binder. -/
theorem Ty.substPath_eq_mu {T₀ : Ty (s,x)} {r : Path s} {T : Ty (s,x)} (h : T₀.substPath r = .mu T) :
    ∃ T₁, T₀ = .mu T₁ ∧ T₁.subst (PathSubst.one r).lift = T := by
  cases T₀ <;> try (simp [Ty.substPath, Ty.subst] at h)
  next T' => exact ⟨T', rfl, h⟩

/-- An opened singleton was one before opening. -/
theorem Ty.substPath_eq_sngl {T₀ : Ty (s,x)} {r : Path s} {q : Path s} (h : T₀.substPath r = .sngl q) :
    ∃ q₀, T₀ = .sngl q₀ ∧ q₀.substPath r = q := by
  cases T₀ <;> try (simp [Ty.substPath, Ty.subst] at h)
  next q' => exact ⟨q', rfl, h⟩

/-- The empty telescope is a left unit of `++`. -/
theorem _root_.Nominal.Translation.nil_append : ∀ (Tel : FCn.Telescope s), (FCn.Telescope.nil ++ Tel) = Tel
  | .nil => rfl
  | .cons Tel pr => by rw [FCn.Telescope.append_cons, Translation.nil_append Tel]

/-- A renaming keeps a tight type tight. -/
theorem Ty.tight_rename (T : Ty s₁) (ρ : Rename s₁ s₂) (h : T.tight = true) : (T.rename ρ).tight = true := by
  rw [Ty.rename_eq_subst]; exact Ty.tight_subst T _ h

end Nominal.Source
