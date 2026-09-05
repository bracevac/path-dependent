# ManySortedFC

The static layer of a two-sorted (type and capture) coercion target.  Standalone; no operational semantics.

| module | contents |
|---|---|
| `Scope`, `Syntax`, `Context`, `Substitution`, `Adapter` | syntax and scoping |
| `Evidence`, `EvidenceChecker`, `EvidenceCheckerCompleteness`, `EvidenceNormalization` | logical evidence, its checker, normalization |
| `Term`, `TermTyping`, `TermChecker`, `TermCheckerCompleteness`, `TermProjection`, `Erasure`, `Runtime` | annotated terms, capture-predictive typing, checker, erasure |
| `Recursion` | guarded recursive type members |
| `Intervals`, `IntervalElaboration` | interval theories |
| `TheoryModel`, `TheoryModelChecker`, `TheoryMorphism`, `TheoryMorphismChecker` | local theories, models, morphisms |
| `TheoryMap`, `TheoryMapChecker`, `TheoryMapCheckerCompleteness`, `TheoryMapComposition`, `TheoryMapMetatheory`, `TheoryMapValidity` | cross-shape theory maps |
| `Consistency`, `ModelConsistency`, `SeparationConsistency` | consistency models |
| `DisjointCaptureTheory` | pairwise-disjoint capture theories |
| `ModalContext`, `ModalConfinement`, `ModalTheoryMap` | modal contexts |
| `Classifier`, `StaticDomain`, `StaticDomainClassifier`, `StaticInstantiation` | classifier kinds, static domains |
| `*Examples` | regressions (`native_decide`) |
