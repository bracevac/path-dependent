import Coercions.Nominal.Source
import Coercions.PDot.Runtime
import Coercions.Nominal.FCn
import Coercions.Nominal.Translation

/-!
# PDot: full pDOT by coercions

The library has four parts.

* The source, `Nominal.Source` in `PDot/Source/`.  pDOT as its Coq formalization states it, in the
  de Bruijn signatures of the Paths target.
* The runtime, `PDot.Runtime` in `PDot/PDot.Runtime.lean`.  Untyped pDOT, which substitutes paths and
  never copies an object, with nested literals addressed by their path.  The erasure of the source
  into it is `PDot/Source/Erasure.lean`.
* The target, `Nominal.FCn` in `PDot/FCp/`.  The coercion calculus FCn: syntax, typing, store and
  machine, erasure into the runtime, and the checker with its completeness.  Its canonical forms
  and metatheory are later stages.
* The translation, `Nominal.Translation` in `PDot/Translation/`.  The source into the target, and the
  transport of the target's theorems.  A later stage.
-/
