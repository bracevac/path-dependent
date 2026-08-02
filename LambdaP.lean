import LambdaP.Debruijn
import LambdaP.Original
import LambdaP.Repaired
import LambdaP.Syntax
import LambdaP.Substitution
import LambdaP.Context
import LambdaP.Typing
import LambdaP.Semantics
import LambdaP.Lemmas.Renaming
import LambdaP.Lemmas.Subst
import LambdaP.Lemmas.StoWeaken
import LambdaP.Lemmas.Locs
import LambdaP.Soundness.Store
import LambdaP.Soundness.Pushback
import LambdaP.Soundness.Embedding
import LambdaP.Soundness.RealizedSubst
import LambdaP.Soundness.Progress
import LambdaP.Soundness.PreservationPrep
import LambdaP.Soundness.EmbedGap
import LambdaP.Soundness.SubstGap
import LambdaP.Soundness.GSub
import LambdaP.Soundness.Preservation
import LambdaP.Soundness.Safety
import LambdaP.Examples

/-! Pushback campaign (deviation 9). IN the build as of V14: the
syntactic pipeline `Store → Pushback → Embedding → {Progress,
RealizedSubst} → PreservationPrep → Preservation → Safety`, i.e. progress,
preservation and TYPE SAFETY, plus the two gap files (`EmbedGap`,
`SubstGap`) and the sized scope-generic table (`GSub`).

OUT of the build (superseded): the semantic tower `Den`/`DenLemmas`/
`PathLemmas`/`Transfer`/`Closure` — it existed only to build the `Ξ` that
the old `SemStoExists` fed to canonical forms, and `Sub.canonical_arrow`
retired that obligation; and the possible-types chain `Precise`/`Tight`/
`Invertible`/`PT`/`Bridge`/`PTTransfer`, subsumed by `SSub`/`SOut`.
`Functionality` is imported by `Preservation`. -/

/-! ### Axiom audit (V14). `type_safety` is unconditional except for the
single remaining leaf `Sto.ResidueCollapse` (see `Soundness/Embedding.lean`
and NOTES.md, "V14 EXECUTION REPORT"): no `sorryAx` anywhere. -/
section
open LambdaP
#print axioms LambdaP.type_safety
#print axioms LambdaP.type_safety_init
#print axioms LambdaP.preservation
#print axioms LambdaP.progress
#print axioms LambdaP.Sub.to_ssub
#print axioms LambdaP.Sub.subst
#print axioms LambdaP.GSub.subst
#print axioms LambdaP.GSub.subst_loc
#print axioms LambdaP.Sub.to_gsub
#print axioms LambdaP.GSub.to_sub
#print axioms LambdaP.gsubstLift
#print axioms LambdaP.Sub.canonical_arrow
#print axioms LambdaP.Sub.consistency_empty
#print axioms LambdaP.EmbedGap.substPower
#print axioms LambdaP.EmbedGap.embPower_of_residueCollapse
#print axioms LambdaP.EmbedGap.residueCollapse_of_embPower
end
