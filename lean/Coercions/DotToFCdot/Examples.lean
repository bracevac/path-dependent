import Coercions.DotMNF.Examples
import Coercions.DotToFCdot.TermsTyped
import Coercions.DotToFCdot.Erasure

/-!
# Translation regressions for unrestricted recursive types

These closed source derivations exercise recursive function types across a
let boundary, self-dependent intersections, nested recursive binders, and
recursive bodies consisting of a bare selection. Each translation has the
advertised target type and the same untyped erasure as the source. `E9_runs` in
`DotMNF.Examples` also checks the source program's execution.
-/

namespace DotMNF.Examples

theorem E9_translate_typed :
    FCdot.Tm.HasType Ctx.nil.translate E9.translate Ty.top.translate :=
  E9.translate_typed .nil

theorem E9_translate_erase : E9.translate.erase = E9Term.erase :=
  E9.translate_erase

theorem E10_translate_typed : FCdot.Tm.HasType Ctx.nil.translate E10.translate
    (Ty.all E10Rec (.sel (.var .here) lB)).translate :=
  E10.translate_typed .nil

theorem E10_translate_erase : E10.translate.erase = E10Term.erase :=
  E10.translate_erase

theorem E11_translate_typed : FCdot.Tm.HasType Ctx.nil.translate E11.translate
    (Ty.all E11Rec (.sel (.var .here) lA)).translate :=
  E11.translate_typed .nil

theorem E11_translate_erase : E11.translate.erase = E11Term.erase :=
  E11.translate_erase

theorem E12_translate_typed : FCdot.Tm.HasType Ctx.nil.translate E12.translate
    (Ty.all E12Rec (.sel (.var .here) lA)).translate :=
  E12.translate_typed .nil

theorem E12_translate_erase : E12.translate.erase = E12Term.erase :=
  E12.translate_erase

end DotMNF.Examples
