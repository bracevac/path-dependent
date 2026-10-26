import Coercions.PDot.Source
import Coercions.PDot.Runtime

/-!
# PDot: full pDOT by coercions

The library has four parts.

* The source, `PDot.Source` in `PDot/Source/`.  pDOT as its Coq formalization states it, in the
  de Bruijn signatures of the Paths target.
* The runtime, `PDot.Runtime` in `PDot/Runtime.lean`.  Untyped pDOT, which substitutes paths and
  never copies an object, with nested literals addressed by their path.  The erasure of the source
  into it is `PDot/Source/Erasure.lean`.
* The target, `PDot.FCp` in `PDot/FCp/`.  The coercion calculus FCp and its machine.  A later stage.
* The translation, `PDot.Translation` in `PDot/Translation/`.  The source into the target, and the
  transport of the target's theorems.  A later stage.
-/
