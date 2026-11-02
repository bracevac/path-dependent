import Coercions.Nominal.Source
import Coercions.PDot.Runtime
import Coercions.Nominal.FCn
import Coercions.Nominal.Translation

/-!
# Nominal: classes and traits over pDOT by coercions

The library has four parts.

* The source, `Nominal.Source` in `Nominal/Source/`.  pDOT-C: pDOT as its Coq formalization states
  it, with plan XII's class definition and seal, in the de Bruijn signatures of the Paths target.
* The runtime, `PDot.Runtime` in `PDot/Runtime.lean`.  The PDot tree holds it, and this tree imports
  it unchanged and shares it.  Untyped pDOT, which substitutes paths and never copies an object,
  with nested literals addressed by their path.  The erasure of the source into it is
  `Nominal/Source/Erasure.lean`.
* The target, `Nominal.FCn` in `Nominal/FCn/`.  The coercion calculus FCn, plan X's FCp with a class
  entry and a seal: syntax, typing, store and machine, erasure into the runtime, the checker with
  its completeness, the canonical forms and the metatheory.
* The translation, `Nominal.Translation` in `Nominal/Translation/`.  The source into the target, and
  the transport of the target's theorems.
-/
