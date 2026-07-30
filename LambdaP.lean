import LambdaP.Debruijn
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
import LambdaP.Examples
import LambdaP.Soundness.PreservationPrep
import LambdaP.Soundness.DOut
import LambdaP.Soundness.Compose

/-! Pushback campaign (deviation 9): the semantic chain
(Den/Closure/Progress/Preservation/Safety), the possible-types chain
(Precise/Tight/Invertible/PT/Bridge/PTTransfer), Functionality, and
Examples are temporarily out of the build while the store-anchored
selection rules propagate; they are superseded or restored by the
trans-free runtime subtyping pipeline (see Soundness/Pushback.lean). -/
