# Coercions

Root modules: `DotMNF.lean`, `FCdot.lean`, `DotToFCdot.lean`, `Runtime.lean`,
`FCsub.lean`, `ManySortedFC.lean`, `All.lean` (= FCsub + ManySortedFC).

## Runtime.lean
The untyped runtime both DotMNF and FCdot erase into: `var`, `lam`, `obj` with
fields, `app`, `proj`, `let`; store machine; `Final`, `Stuck`.

## DotMNF/ — source: WadlerFest DOT in monadic normal form
| module | contents |
|---|---|
| `Syntax` | paths, types (`⊤ ⊥ {A:S..T} {a:T} p.A μ ∀ ∧`), terms, values, definitions; `Decl`, `Wf`, `Distinct`, `Guarded` |
| `Typing` | contexts (`cons`, `consSelf`); `Sub`, `HasTy`, `DefsTy` (Type-valued) |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Erasure` | erasure to `Runtime`; `erase_step`, `erase_reflect`, `final_erase`, `final_reflect` |
| `Examples` | E1–E5 as `HasTy` derivations |

## FCdot/ — target: explicit-evidence coercion calculus
| module | contents |
|---|---|
| `Debruijn` | signatures, `BVar`, renamings |
| `Syntax` | types (`⊤ = μ []`, `⊥`, `x ∙ ℓ`, `Π`, `μ Tel`), propositions, telescopes; evidence `LeCo` (`refl trans top bot eqToLe pi obj pair member`), `EqCo`, `Has`, template morphisms (`Hole`, `Side`, `Morphism`); atoms (`var cast foldSelf unfoldSelf both`); terms, values, witnesses, fields; renaming, substitution; notation |
| `Context` | bindings (opaque / transparent with witnesses), contexts, lookups, guardedness |
| `Typing` | `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ`, `Γ ⊢ m : Tel ⇒ Tel'`, `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ F` |
| `Store` | stores, literals, `⊢ σ : Γ` |
| `Normalizer` | `Ctx.resolve`; forms, entries, views; `combine`, `pair`, `entriesAt`; fuel-indexed `hnf`, `entries`, `view`, `viewThrough`, `hasView`, `closedAtomForm` |
| `Machine` | continuations `Γ ⊢ₖ K : T ⇒ U`, states, `st ⟶ st'`, `st ⟶* st'` |
| `Erasure` | `⌊·⌋` to `Runtime`; `CastRedex` |
| `RenameLemmas` | `rename_id`, `rename_comp`, subst/rename algebra, injectivity, weakening lemmas |
| `TypingRename` | typing under renaming and weakening |
| `Transparency` | context refinement (transparent ⇒ opaque) preserves typing |
| `TypingSubst` | typing under atom substitution |
| `Preservation` | inversion lemmas, store-typing lemmas, `preservation` (modulo `FormsTyped`) |
| `ErasureMetatheory` | `erase_step`, cast-frame normalization, `erase_reflect` (modulo canonical forms), `final_erase`, `final_reflect` |
| `Checker` | executable checker: `synthLe`, `checkTm`, … with soundness |
| `CheckerCompleteness` | `checkTm_iff` and friends; type uniqueness |
| `Resolution` | `Ctx.resolve` lemmas; fuel bound; well-defined contexts |
| `FormTyping` | `Γ ⊨ F : S ≤ T`, `SideTyped`, `Γ ⊨ Es : Tel₁ ⇒ Tel₂`, `Γ ⊨[r] F : S ≤ T` (chains), `Γ ⊨[r, σ] V : Tel` (views) |
| `FormAlgebra` | `combine_typed`, `pair_typed`, `entriesAt_typed`, `viewThrough_typed`, `atRoot`; fuel monotonicity and determinism |
| `CanonicalForms` | `le_canon`, `eq_canon`, `has_canon`, `mor_canon`, `atom_canon`; `closedAtomForm_typed`; `formsTyped`; `preservation'`, `erase_reflect'` |
| `Progress` | `closed_pi_inversion`, `closed_has_field`, `progress`, `not_stuck` |
| `Consistency` | `closed_le_shapes`, `no_top_le_bot`, `realized`, `Steps.typed`, `reachable_consistent` |
| `Examples` | E1–E5 checked in the kernel, erasure equal to DotMNF's |

## DotToFCdot/ — the translation
| module | contents |
|---|---|
| `Types` | `Ty.translate`, `Ty.tel`, `Ty.telSelf`, `Ty.witnesses`, `Ty.fieldLabels`, `Ty.literalTy`, `Ctx.translate` |
| `TypesLemmas` | translation commutes with renaming and instantiation; `translate_decl`, `tel_substVar` |
| `Evidence` | `Sub.translate`, `HasTy.translateAtom`, `litCo`, `identityMorphism`, `Ctx.varAtom` |
| `EvidenceTyped` | `Sub.translate_typed`, `translateAtom_typed`, `translateAtom_root`, `litCo_typed`, `varAtom_typed`; `Ctx.Wf` |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields` |
| `TermsTyped` | `HasTy.translate_typed`, `translateFields_typed` |
| `Erasure` | `translate_erase`, `coherence` |
| `Safety` | `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for translated programs |

## FCsub/ — System F-sub with explicit coercions (standalone)
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

## ManySortedFC/ — static layer of a two-sorted (type and capture) target (standalone, no dynamics)
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
