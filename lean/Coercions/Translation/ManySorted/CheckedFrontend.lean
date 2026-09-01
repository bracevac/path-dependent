import Coercions.Translation.ManySorted.CheckedFrontend.Source
import Coercions.Translation.ManySorted.CheckedFrontend.Evidence
import Coercions.Translation.ManySorted.CheckedFrontend.Checker
import Coercions.Translation.ManySorted.CheckedFrontend.Compiler
import Coercions.Translation.ManySorted.CheckedFrontend.Examples

/-!
# Stage 8 checked front end

This aggregate exposes an executable, intrinsically scoped, annotated source
fragment in front of the cumulative captured-DOT compiler.  Its proof
certificates are first-order syntax checked structurally; accepted terms
produce existing source typing derivations and then independently accepted
ManySortedFC artifacts.

Supported computation forms are return, general application, plain let,
static application, existential opening, modal unlocking, and explicit use
widening.  Supported values are variables, unit, runtime lambdas, static
lambdas, packages, modal locks, and the non-modal value-adapter fragment.
Modal requirements use recursive finite coverage syntax: one certificate per
mode entry and both orientations of every distinct separation pair.  The
structural checker covers empty, union, subcapture, writable/read-only mode,
symmetry, disjointness injection, and explicitly named lexical interval
bounds; evidence obtained by consulting an enclosing lock frame is deferred.
Member selection and object/recursive-object forms are outside the raw
language.  Unsupported sentinels cover only their boundary diagnostics.

Global runtime correctness is `AdministrativeEq`, matching the cumulative
compiler's function and modal adapter semantics.
-/
