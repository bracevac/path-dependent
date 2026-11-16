import Coercions.Selective.Dot.Vanilla.Sound
import Coercions.Selective.Dot.Vanilla.Elab

/-!
# Selective DOT and DOT-MNF: the exact correspondence

A source term is typable in DOT-MNF exactly when some term of `SelDot` that
erases to it has the same type; a source subtyping holds exactly when some
certificate converts the two types. Transitivity of the source is the
composition `seq` of certificates.

A typed `SelDot` term erases to a source derivation in the context
`(Ctx.ofDot Γ).toDot`, which differs from `Γ` only in the definitions recorded
at self binders. Lookup is the same, so the derivation transfers by renaming
along the identity.
-/

namespace SelDot.Vanilla

open FCdot (Kind Sig BVar Rename Label)

/-- Typability in DOT-MNF is typability of an elaboration in `SelDot`. -/
theorem typability_iff {Γ : DotMNF.Ctx s} {t : DotMNF.Tm s} {T : DotMNF.Ty s} :
    Nonempty (DotMNF.HasTy Γ t T) ↔
      ∃ h : SelDot.Tm s, h.erase = Tm.ofDot t ∧ SelDot.HasTy (Ctx.ofDot Γ) h (Ty.ofDot T) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.elab, d.elab_erase, d.elab_typed⟩
  · rintro ⟨h, he, ht⟩
    obtain ⟨d⟩ := hasTy_sound ht
    rw [← Tm.toDot_erase, he, Tm.toDot_ofDot, Ty.toDot_ofDot] at d
    exact ⟨hasTyTransfer (fun x => (Ctx.toDot_ofDot_lookup Γ x).symm) d⟩

/-- Subtyping in DOT-MNF is the existence of a certificate. -/
theorem coercion_iff {Γ : DotMNF.Ctx s} {S T : DotMNF.Ty s} :
    Nonempty (DotMNF.Sub Γ S T) ↔ ∃ c, CertTy (Ctx.ofDot Γ) c (Ty.ofDot S) (Ty.ofDot T) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.elab, d.elab_typed⟩
  · rintro ⟨c, hc⟩
    obtain ⟨d⟩ := certTy_sound hc
    rw [Ty.toDot_ofDot, Ty.toDot_ofDot] at d
    exact ⟨subTransfer (fun x => (Ctx.toDot_ofDot_lookup Γ x).symm) d⟩

/-- Transitivity is elaborated to composition. -/
theorem trans_is_seq {Γ : DotMNF.Ctx s} {S M T : DotMNF.Ty s}
    (d1 : DotMNF.Sub Γ S M) (d2 : DotMNF.Sub Γ M T) :
    (DotMNF.Sub.trans d1 d2).elab = .seq d1.elab d2.elab := rfl

end SelDot.Vanilla
