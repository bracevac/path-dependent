import Coercions.PDot.Translation.Types
import Coercions.PDot.Translation.TypesLemmas
import Coercions.PDot.Translation.Hole
import Coercions.PDot.Translation.Rel
import Coercions.PDot.Translation.Evidence
import Coercions.PDot.Translation.EvidenceTyped
import Coercions.PDot.Translation.Defs
import Coercions.PDot.Translation.Terms
import Coercions.PDot.Translation.DefsTyped
import Coercions.PDot.Translation.TermsTyped
import Coercions.PDot.Translation.Erasure
import Coercions.PDot.Translation.Safety
import Coercions.PDot.Translation.Examples
import Coercions.PDot.Translation.Pages

/-!
Import root for the translation of PDot: the pDOT source `PDot.Source` into the coercion calculus
FCp `PDot.FCp`, plan X, Part TR, in `PDot/Translation/`.  Every function is structural recursion on
its source object.  A function or theorem whose subject is a source object is declared in
`PDot.Source`, and a helper whose subject is a target object in `PDot.Translation`.

The parts, in the order they land.  `Types` holds the type translation `⟦·⟧` of TR.2 with the
telescopes `tel⁺` and `tel`.  `TypesLemmas` holds its laws under renaming and path substitution,
the fold `Ty.tel_fold`, the refutation `tel_open_ne` of the open equation, and the kernel checks on
E3's types.  `Hole` holds the translated hole of a replacement, `Repl.translate_hole`.  `Rel` holds
the related contexts `G ≈ Δ` of TR.1 and `Ctx.translate`.  `Evidence` holds the images of path
typings (TR.3) and of subtyping (TR.4), one structural recursion, with the paths of the images.
`EvidenceTyped` shows the images typed in related contexts, `HasTy.translatePath_typed` and
`Sub.translate_typed`, with the examples E9 to E11.  `Defs` holds the helpers of the definition
translation and the opening inversions.  `Terms` holds the images of terms (TR.6) and of definitions
(TR.5), one structural recursion.  `DefsTyped` holds the label lemmas and the inversions of FCp's
typing the next part reads.  `TermsTyped` shows the images typed in related contexts,
`HasTy.translate_typed` and `DefsTy.translate_typed`, with the examples E3, E8, E13 and N5.
`Erasure` shows that the image of a derivation erases to the source's erasure of its term,
`HasTy.translate_erase`.
-/
