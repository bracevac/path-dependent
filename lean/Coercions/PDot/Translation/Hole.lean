import Coercions.PDot.Translation.TypesLemmas

/-!
# The translated hole of a replacement (plan X, Part TR.4, stage X6 group g2)

A replacement `r : p ↦ q ⊢ T ⇝ T'` has a hole `r.hole`, a type with one new innermost variable `h`
(`Source/Repl.lean:68-90`).  Opened at `p` the hole is `T`, opened at `q` it is `T'`
(`Repl.hole_spec`, `Source/Repl.lean:203`).  The images of `subtyp_sngl_pq` and `subtyp_sngl_qp`
lift a path equality through the translated hole, `lift (h. ⟦hole r⟧) π`.  `EQ-Lift` types it at the
translated hole opened at each end.  `Repl.translate_hole` says these are `⟦T⟧` and `⟦T'⟧`.

`Repl.hole_spec` has one case per replacement constructor, so the eleven constructors are covered
for every `r`.  The proof moves the opening through the translation by `Ty.translate_substPath`.
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The translated hole opened at `p` is `⟦T⟧`, opened at `q` it is `⟦T'⟧`. -/
theorem Repl.translate_hole {p q : Path s} {T T' : Ty s} (r : Repl p q T T') :
    r.hole.translate.substPath p = T.translate ∧ r.hole.translate.substPath q = T'.translate := by
  rw [← Ty.translate_substPath, ← Ty.translate_substPath, r.hole_spec.1, r.hole_spec.2]
  exact ⟨rfl, rfl⟩

end PDot.Source
