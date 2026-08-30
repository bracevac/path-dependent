import Coercions.Translation.ManySorted.Acyclic.ObjectEncoding
import Coercions.Translation.ManySorted.Acyclic.ObjectEncodingMetatheory
import Coercions.Translation.ManySorted.Acyclic.Layout
import Coercions.Translation.ManySorted.Acyclic.StaticTranslation
import Coercions.Translation.ManySorted.Acyclic.StaticTranslationMetatheory
import Coercions.Translation.ManySorted.Acyclic.ExposureTranslation
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation
import Coercions.Translation.ManySorted.Acyclic.RuntimeContext
import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.Translation.ManySorted.Acyclic.SelectionUseTranslation

/-!
# Acyclic DOT with captures to many-sorted FC

This root collects the target representation and shared context layout for
the first DOT layer with genuine type selections `x.A`, capture selections
`x.C`, and value selections `x.v : (x.A)^{x.C}`.
-/
