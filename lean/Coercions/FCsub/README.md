# FCsub

System F-sub with explicit coercions, telescope-constrained quantifiers, and head-guarded recursive projections.  Standalone.

| module | contents |
|---|---|
| `Scope` | intrinsically scoped heterogeneous variables |
| `Syntax` | syntax |
| `Telescope`, `TelescopeMetatheory` | telescope operations and morphism metatheory |
| `Recursion` | simultaneous guarded recursive types |
| `Context` | contexts and telescope opening |
| `Typing` | declarative typing |
| `Substitution`, `SubstitutionMetatheory` | four-sort substitution and its typing metatheory |
| `Structural` | structural metatheory |
| `Normalization` | coercion normalization |
| `Dynamics` | annotated call-by-value dynamics |
| `Preservation`, `Progress` | preservation; closed-program progress |
| `Runtime`, `RuntimeSubstitution`, `RuntimeMetatheory` | erased runtime and its metatheory |
| `Erasure`, `ErasureMetatheory`, `Simulation` | erasure and erasure simulation |
| `Checker`, `CheckerCompleteness` | executable checker, `checkTerm_iff` |
| `ClosedArtifact` | proof-free closed artifacts |
| `Examples` | kernel examples (`native_decide`) |
