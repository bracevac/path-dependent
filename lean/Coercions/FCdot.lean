import Coercions.FCdot.Debruijn
import Coercions.FCdot.Syntax
import Coercions.FCdot.RenameLemmas
import Coercions.FCdot.Context
import Coercions.FCdot.Typing
import Coercions.FCdot.Store
import Coercions.FCdot.Machine
import Coercions.FCdot.Erasure
import Coercions.FCdot.TypingRename
import Coercions.FCdot.Transparency
import Coercions.FCdot.TypingSubst
import Coercions.FCdot.Preservation
import Coercions.FCdot.ErasureMetatheory
import Coercions.FCdot.Checker
import Coercions.FCdot.CheckerCompleteness
import Coercions.FCdot.Canonical
import Coercions.FCdot.Resolution
import Coercions.FCdot.CanonicalTyped
import Coercions.FCdot.CanonicalViews
import Coercions.FCdot.CanonicalCombine
import Coercions.FCdot.CanonicalMono
import Coercions.FCdot.CanonicalMetatheory
import Coercions.FCdot.CanonicalChain
import Coercions.FCdot.Progress
/-!
Import root for FCdot, the explicit-evidence coercion target of Plan III.
-/
