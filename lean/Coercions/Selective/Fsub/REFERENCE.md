# Plain full F-sub with selective explicit transitivity: reference

The introduction is [README.md](README.md). This file is the detailed account: the module list, the
theorem inventory, the four claims and the limits.

The library `SelectiveFsub` (modules `Coercions.Selective.Fsub.*`, namespace `SelFsub`) is
self-contained: its modules import nothing outside their own directory (no Mathlib, no
other library of the repository, no DOT). It develops plain full F-sub in which ordinary
subtyping is restricted to a primitive relation `≤₀` without transitivity, and every
further transitive step is written as a stored certificate

```text
c, d ::= step[S, T] | c ; d
Γ ⊢ step[S,T] : S ⇒ T   if  Γ ⊢ S ≤₀ T
Γ ⊢ c ; d : S ⇒ T       if  Γ ⊢ c : S ⇒ M  and  Γ ⊢ d : M ⇒ T   (the same M, syntactically)
```

Types are `Top | X | S → T | ∀(X <: S). T`, intrinsically scoped (`Ty n`, de Bruijn
indices in `Fin n`); contexts are ordered lists of upper bounds, each scoped before
its binder. The universal rule is the full one: bounds contravariant, bodies compared
under the target bound.

"Every further transitive step is written" is a statement about typing derivations:
each boundary does exactly one primitive check between uniquely determined types. It
does not hold along reduction. Programs typable without casts can reach reducts that
need written steps (`gProg`, `hProg` in
`Probes/P2_Chains.lean`), so preservation generates certificates, while
syntactic cast-freeness is itself preserved by reduction (`Steps.castfree` in
`Probes/P1_Reduction.lean`). No lower bound is claimed on the number of
written steps a reduct needs: that check rejects one displayed one-step candidate and
accepts a displayed two-step candidate.

Certificates need no constructor beyond `step`
and `;`: the lifts, the converse translation, narrowing, type substitution and the
inversion lemmas are all functions on certificates built from these two.

## Replay

From the repository root:

```sh
lake build SelectiveFsub
lake env lean lean/Coercions/Selective/Fsub/Axioms.lean     # 159 lines
lake env lean lean/Coercions/Selective/Fsub/Probes/P1_Reduction.lean   # likewise P2_Chains and P3_Size
```

The audit has 159 lines; each reads `[propext]`, `[propext, Quot.sound]` or "does not
depend on any axioms" (`Quot.sound` enters through `funext` in the de Bruijn lemmas and
through `simp` in the checker proofs, for example `boundIs_true`).
The sources contain no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`,
`set_option`, `Classical` or Mathlib import. Every function is structural recursion;
nothing uses fuel or well-founded recursion, so the kernel evaluates the checker and
the certificate operations (`decide` and `rfl` in `Witness.lean`). The term checker
`synthTm` is structural recursion on the term as well, and the term examples are
checked by plain `decide` (`Examples.lean`).

## Modules

| file | lines | content |
| --- | --- | --- |
| `Syntax.lean` | 140 | `Ty`, `rename`, `weaken`, `liftS`, `subst`, `sub0`, `liftN`, `Ctx`, `lookup`, `Tele`, `append`, `Tele.subst`; lines 70-140 are de Bruijn lemmas |
| `Prim.lean` | 157 | `Prim` (five rules), `PrimAt`, `primDir`, `prim?`, `prim?_iff`, decidability, `Prim.inv`; `TyRen`, `Prim.rename`, `Prim.weaken` (26 lines); the nontransitivity witnesses and `primitive_nontrans` |
| `Cert.lean` | 88 | `Cert`, `src`, `tgt`, `CTy`, endpoints; `Cert.valid`, `synthC`, `checkC` with their `_iff`; `Cert.rename`, `CTy.rename`, `CTy.weaken` (17 lines) |
| `Sub.lean` | 42 | declarative full F-sub `Sub` (`Type`-valued), `primitive_sound`, `coercion_sound`, `coercion_transitive`, `coercion_exists_transitive` |
| `Lift.lean` | 71 | `Cert.arrDom`, `arrCod`, `allBound`, `allBody`, `Cert.arr`, `Cert.all` and their typing lemmas |
| `Complete.lean` | 31 | `Sub.toCert`, `Sub.toCert_typed`, `coercion_iff` |
| `Subst.lean` | 153 | certified substitutions `CSub` with entries, `liftT`, `liftNT`, `CSub.lift`, `CSub.liftTele` (25 lines of lifting); `Cert.ofPrim`, `Cert.subst`, `CTy.subst`; narrowing and type substitution under a telescope |
| `Invert.lean` | 72 | `CTy.top_inv`; `Cert.arrInv`, `CTy.arr_inv`; `Cert.allInv`, `CTy.all_inv` |
| `Witness.lean` | 138 | the examples listed below |
| `Term.lean` | 118 | terms `Tm n` with casts, `erase`; type renaming `renTy`, type substitution of erased terms `substTy`, term substitution `subst`, their commutation with `erase`, and the type lemmas `Ty.subst_subst`, `Ty.subst_sub0`, `Ty.rename_sub0` (lines 39-117 are bookkeeping) |
| `Typing.lean` | 98 | `HTy` (no subsumption; `≤₀` at the application argument and the type-application bound), `HTy.unique`, `synthTm`, `synthTm_iff` |
| `Safety.lean` | 251 | `Value`, `Step`, `Steps`; `HTy.renTy`, `HTy.append` (29 lines of typed renaming); `HTy.subst`, `HTy.substTy`, canonical forms, `preservation`, `progress`, `safety`; determinism `Value.no_step`, `Step.det` (27 lines) |
| `Exact.lean` | 64 | declarative F-sub term typing `FTy`, `elaboration_typed`, `elaboration_complete`, `typability_iff`, the corollary `fsub_safety` |
| `Examples.lean` | 145 | the term examples listed below |
| `Axioms.lean` | 177 | `#print axioms` for every theorem and the main functions (not imported by the root) |
| `../Fsub.lean` | 14 | the import root: all modules except `Axioms` |

The eight core modules have 754 lines. About 140 of them are syntactic bookkeeping:
the de Bruijn lemmas of `Syntax` (71), typed renaming of `Prim` (26) and `CTy` (17),
and lifting certified substitutions under binders and telescopes (25). The rest is the
calculus, its checker and the metatheory proper.

The term layer (`Term`, `Typing`, `Safety`, `Exact`) has 531 lines: syntax and erasure
38, syntactic bookkeeping 108 (term renaming and substitution with their commutation
lemmas, 79; typed renaming and weakening of term contexts, 29), typing and checker 98,
exactness against `FTy` 64, the safety module proper 195 (of which 41 are its
docstring and the reduction relation), and determinism of `Step` 27. `Safety` imports
neither `Sub` nor `Complete`. These are file lines;
the matched comparison with a declarative proof, in declaration lines, is in
[`../FsubDeclarative/REFERENCE.md`](../FsubDeclarative/REFERENCE.md) (459 lines for the safety argument
proper of this route against 199 there).

Related libraries: [`../FsubDeclarative`](../FsubDeclarative/README.md) (the matched declarative control:
the same safety theorem proved directly on `FTy`); [`../FsubCompare`](../FsubCompare/README.md) (data on the
plain-F-sub fragment of the repository's FCsub); [`../Bridge`](../Bridge/README.md) (a forward,
evidence-preserving translation into the DOT-MNF calculus). [`Probes/`](Probes) holds three probes from an
independent check of this development. They are not part of the library and are replayed one file at a time.

## Theorem inventory

All names are in namespace `SelFsub` (examples in `SelFsub.Witness`).

Primitive relation (`Prim.lean`):

- `primDir_sound`, `primDir_complete`: the polarity checker is sound and complete for `PrimAt`.
- `prim?_iff : prim? Γ S T = true ↔ Prim Γ S T`.
- `Prim.inv`: a primitive step is reflexivity, `Top`, an exact bound lookup, or structural.
- `Prim.rename : TyRen Γ Δ ρ → Prim Γ S T → Prim Δ (S.rename ρ) (T.rename ρ)`; `Prim.weaken`.
- `ctxYX_XY`, `ctxYX_Y`, `ctxYX_not`, `ctxYX_checker`: in `Y <: Top → Top, X <: Y`, `X ≤₀ Y` and `Y ≤₀ Top → Top` but not `X ≤₀ Top → Top`, and `prim?` returns `false`.
- `ctxZYX_XY`, `ctxZYX_YZ`, `ctxZYX_not`: the same in `Z <: Top, Y <: Z, X <: Y` for `X`, `Y`, `Z`.
- `primitive_nontrans : ¬ ∀ {n} (Γ : Ctx n) S M T, Prim Γ S M → Prim Γ M T → Prim Γ S T`.

Certificates and checker (`Cert.lean`):

- `CTy.endpoints : CTy Γ c S T → c.src = S ∧ c.tgt = T`; `CTy.endpoints_unique`.
- `Cert.valid_iff : c.valid Γ = true ↔ CTy Γ c c.src c.tgt`.
- `synthC_iff : synthC Γ c = some (S, T) ↔ CTy Γ c S T`; `checkC_iff : checkC Γ c S T = true ↔ CTy Γ c S T`.
- `CTy.rename : TyRen Γ Δ ρ → CTy Γ c S T → CTy Δ (c.rename ρ) (S.rename ρ) (T.rename ρ)`; `CTy.weaken`.

Soundness and transitivity (`Sub.lean`):

- `primitive_sound : Prim Γ S T → Nonempty (Sub Γ S T)`.
- `coercion_sound : CTy Γ c S T → Nonempty (Sub Γ S T)`.
- `coercion_transitive : CTy Γ c S M → CTy Γ d M T → CTy Γ (.seq c d) S T`.
- `coercion_exists_transitive : (∃ c, CTy Γ c S M) → (∃ d, CTy Γ d M T) → ∃ e, CTy Γ e S T`.

Lifts (`Lift.lean`), each for a function on certificates:

- `CTy.arrDom : CTy Γ c B A → CTy Γ (c.arrDom C) (A → C) (B → C)` (reverses `;`).
- `CTy.arrCod : CTy Γ c A B → CTy Γ (c.arrCod C) (C → A) (C → B)`.
- `CTy.allBound : CTy Γ c B A → CTy Γ (c.allBound C) (∀(X <: A). C) (∀(X <: B). C)` (reverses `;`).
- `CTy.allBody : CTy (Γ, X <: A) c B C → CTy Γ (c.allBody A) (∀(X <: A). B) (∀(X <: A). C)`.
- `CTy.arr : CTy Γ dom B₁ A₁ → CTy Γ cod A₂ B₂ → CTy Γ (Cert.arr dom cod) (A₁ → A₂) (B₁ → B₂)`.
- `CTy.all : CTy Γ bound B₁ A₁ → CTy (Γ, X <: B₁) body A₂ B₂ → CTy Γ (Cert.all bound body) (∀(X <: A₁). A₂) (∀(X <: B₁). B₂)`.

Completeness (`Complete.lean`):

- `Sub.toCert_typed : (h : Sub Γ S T) → CTy Γ h.toCert S T`, for the function `Sub.toCert`.
- `coercion_iff : (∃ c, CTy Γ c S T) ↔ Nonempty (Sub Γ S T)`.

Certified substitution (`Subst.lean`). `CSub Γ Δ σ τ` says: for each `x`, the entry
`τ x` is `some c` with `CTy Δ c (σ x) (Γ(x)[σ])`, or `none` with `Prim Δ (σ x) (Γ(x)[σ])`.

- `EntryTy.cert`: an entry yields a certificate.
- `CSub.lift : CSub Γ Δ σ τ → CSub (Γ, X <: B) (Δ, X <: B[σ]) (liftS σ) (liftT τ)`; `CSub.liftTele` for a telescope.
- `Cert.ofPrim_typed`: a primitive step `S ≤₀ T` (in either polarity) becomes the certificate `Cert.ofPrim p σ τ S T : S[σ] ⇒ T[σ]`.
- `CTy.subst : CSub Γ Δ σ τ → CTy Γ c S T → CTy Δ (c.subst σ τ) S[σ] T[σ]`.
- `CSub.narrow`, `CTy.narrow : CTy (Γ, X <: U, Θ) c S T → CTy Γ d U' U → CTy (Γ, X <: U', Θ) (c.narrow k d) S T`.
- `CSub.inst`, `CTy.inst : CTy (Γ, X <: U, Θ) c S T → CTy Γ d V U → CTy (Γ, Θ[V/X]) (c.inst k V d) S[V/X] T[V/X]` (with `[V/X]` the `k`-fold lift of `sub0 V`).

Inversion (`Invert.lean`), in every context:

- `CTy.top_inv : CTy Γ c S T → S = Top → T = Top`.
- `CTy.arr_inv : CTy Γ c (A₁ → A₂) T → T = Top ∨ ∃ B₁ B₂, T = B₁ → B₂ ∧ CTy Γ c.arrInv.1 B₁ A₁ ∧ CTy Γ c.arrInv.2 A₂ B₂`.
- `CTy.all_inv : CTy Γ c (∀(X <: A₁). A₂) T → T = Top ∨ ∃ B₁ B₂, T = ∀(X <: B₁). B₂ ∧ CTy Γ c.allInv.1 B₁ A₁ ∧ CTy (Γ, X <: B₁) c.allInv.2 A₂ B₂`.

Examples (`Witness.lean`):

- `chainL_typed`, `chainR_typed`, `chain_not_prim`, `chain_step_rejected`, `chain_middle_not_prim`: three bound steps `X ⇒ Y ⇒ Z ⇒ Top → Top` in both associations, none of the composites primitive, and the single step rejected by the checker.
- `arr_typed`, `arr_not_prim`: chains in an arrow domain and result. `all_typed`, `all_not_prim`: chains in a universal bound and body.
- `bad_parts`, `bad_rejected`, `bad_untyped`, `good_typed`: `step[X,Y] ; step[Top→Top, Top→Top]` is rejected though both parts check and `step[X,Y] ; step[Y, Top→Top]` checks for the same outer endpoints.
- `nb_narrow`, `nb_narrow_typed`, `nb_not_prim`: narrowing `X <: Z` to `X <: Y` turns the bound step `step[X,Z]` into `step[X,Y] ; step[Y,Z]`, and `X ≤₀ Z` no longer holds.
- `na_narrow`, `na_narrow_typed`, `na_not_prim`: the same under an inner binder, inside an arrow result. `nu_narrow_typed`, `nu_not_prim`: inside a universal body.
- `sb_inst`, `sb_inst_typed`: substituting `W` for `X <: Z` turns `step[X,Z]` into the supplied composite `d : W ⇒ Y ⇒ Z`. `sa_inst`, `sa_inst_typed`, `sa_not_prim`: the same under an inner binder at a contravariant position, where `d` appears reversed.
- `arr_inv_components`, `all_inv_components`: the inversion functions on the lifted chains.

Terms (`Term.lean`):

- `Tm.erase_erase : t.erase.erase = t.erase` (erased terms are cast-free).
- `Tm.erase_renTy : (t.renTy ρ).erase = t.erase.renTy ρ`; `Tm.erase_subst : (t.subst k w).erase = t.erase.subst k w.erase`.
- `Ty.rename_sub0`, `Ty.subst_subst`, `Ty.subst_sub0 : (T[U/X])[σ] = (T[liftS σ])[U[σ]/X]`.

Typing and checker (`Typing.lean`):

- `HTy.unique : HTy Γ Δ t T → HTy Γ Δ t T' → T = T'`.
- `synthTm_iff : synthTm Γ Δ t = some T ↔ HTy Γ Δ t T`; decidability of `HTy`.

Direct safety (`Safety.lean`), for term-closed terms in every type context `Γ`. `Step`
uses a substitution that does not shift the substituted term. On terms closed in term
variables it coincides with standard capture-avoiding call-by-value (`step_iff_std`,
`safety_std` in `Probes/P1_Reduction.lean`), and terms typed in the
empty term context are closed. On open terms `Step` captures and preservation fails
(`open_capture`, `open_preservation_fails`, same file). No theorem uses `Step` on
annotated terms, where `Tm.substTy` would drop casts.

- `HTy.renTy : TyRen Γ Γ' ρ → HTy Γ Δ t T → HTy Γ' (Δ.map (rename ρ)) (t.renTy ρ) (T.rename ρ)`; `HTy.append : HTy Γ Δ t T → ∀ Δ', HTy Γ (Δ ++ Δ') t T`.
- `HTy.subst : HTy Γ (Δ ++ [S]) t T → HTy Γ [] w S → HTy Γ Δ (t.subst Δ.length w) T`.
- `HTy.substTy : CSub Γ Γ' σ τ → HTy Γ Δ t T → ∃ t', t'.erase = t.erase.substTy σ ∧ HTy Γ' (Δ.map (subst σ)) t' (T.subst σ)`.
- `HTy.canon_lam : HTy Γ Δ t T → t.erase = λ(x : S). e₀ → ∃ b T₀ c, b.erase = e₀ ∧ HTy Γ (S :: Δ) b T₀ ∧ CTy Γ c (S → T₀) T`; `HTy.canon_tlam` likewise for `Λ`, with the body under `Γ, X <: S`; both are typing inversions through casts.
- `preservation : HTy Γ [] t T → Step t.erase e' → ∃ t', t'.erase = e' ∧ HTy Γ [] t' T`.
- `progress : HTy Γ [] t T → Value t.erase ∨ ∃ e', Step t.erase e'`.
- `safety : HTy Γ [] t T → Steps t.erase e → Value e ∨ ∃ e', Step e e'`.
- `Value.no_step : Value v → ¬ Step v e`; `Step.det : Step e e₁ → Step e e₂ → e₁ = e₂`.

Exactness (`Exact.lean`):

- `FTy.erase_eq : FTy Γ Δ e T → e.erase = e`.
- `elaboration_typed : HTy Γ Δ t T → FTy Γ Δ t.erase T`.
- `elaboration_complete : FTy Γ Δ e T → ∃ t, t.erase = e ∧ HTy Γ Δ t T`.
- `typability_iff : (∃ t, t.erase = e ∧ HTy Γ Δ t T) ↔ FTy Γ Δ e T`.
- `fsub_safety : FTy Γ [] e T → Steps e e' → Value e' ∨ ∃ e'', Step e' e''` (from `elaboration_complete` and `safety`).

Term examples (`Examples.lean`, namespace `SelFsub.Examples`), all by `decide` or `rfl`:

- `arg_bare_rejected`, `arg_one_step_rejected`, `arg_cast_typed`: `Λ(Y <: Top → Top). Λ(X <: Y). λ(x : X). (λ(g : Top → Top). g) x` is rejected bare and with the single cast `step[X, Top → Top]`, and accepted with `x ▷ (step[X,Y] ; step[Y, Top → Top])`; this written chain is not minimal (`x ▷ step[X, Y]` with the implicit check also suffices, the reviewer's `arg_one_written_step`). `argRun_typed`, `argRun_steps`, `argRun_value`: applied, it runs to `λ(z : Top). z`.
- `nest_typed`, `nest_subject_rejected`, `nest_mismatch_rejected`: nested casts compose through their written endpoints only; a cast subject gets no implicit step.
- `calleeF_typed`, `callee_bare_rejected`, `calleeApp_typed`: a type application two bound steps below the bound, accepted with a cast on the callee by `Cert.allBound` (one written step under the lift also suffices, `calleeApp1_typed`). A boundary adds at most one implicit step after the last written cast; no example claims minimality.
- `tb_step`, `tb_bare_rejected`, `tbReduct_erase`, `tbReduct_typed`, `tbEntry_eq`, `tb_arg_cast`, `tb_arg_cast_typed`: after type-β the erased reduct is untypable bare; an annotation with the chain on the argument is typed, and the cast the proof inserts is computed by `Cert.subst`.
- `bRedex_typed`, `b_step`, `b_bare_rejected`, `b_min_typed`, `bReduct_erase`, `bReduct_typed`: a β-step after which two implicit steps meet at one argument; the bare reduct is rejected, and `bReduct`, a hand-written annotation transcribed from the construction in the proof of preservation, is typed by `synthTm`. The witness of `preservation` is an existential in `Prop` and is not extracted, so annotation growth along `safety` is not observed.

## The four claims

1. `≤₀` has no transitivity constructor: `Prim` has the five rules `refl`, `top`,
   `bound`, `arr`, `all` (by definition, `Prim.lean`), and `bound` returns the declared
   bound only.
2. Transitivity is not admissible for `≤₀`: `primitive_nontrans`, from `ctxYX_XY`,
   `ctxYX_Y`, `ctxYX_not`; also `ctxZYX_not`, `chain_not_prim`, `chain_middle_not_prim`.
3. The checker decides exactly `≤₀`, does not close it under transitivity, and
   searches for no middle type: `prim?_iff`, `synthC_iff`, `checkC_iff`; on the
   witnesses `ctxYX_checker` and `chain_step_rejected`; the mismatch regression
   `bad_rejected`. Some composite endpoints are still primitive by another rule
   (`X ≤₀ Y`, `Y ≤₀ Top` and `X ≤₀ Top` by the top rule); nontransitivity is claim 2.
4. Coercion existence is transitive and coincides with declarative full F-sub:
   `coercion_exists_transitive`, `coercion_iff` (via `coercion_sound` and
   `Sub.toCert_typed`).

## Consequence for inference

Subtyping in full F-sub is undecidable (Pierce, "Bounded quantification is
undecidable", POPL 1992). By `coercion_iff`, coercion existence coincides with it, so
no sound, complete and always-terminating procedure can decide whether some
certificate exists between two types in a given context. Certificates are finite and
each candidate is decided by the checker, so enumerating them is a complete
semi-decision procedure for the positive instances; it need not terminate on the
negative ones. This rests on the cited result, which is not formalized here. The
calculus decides `≤₀` and checks written evidence; nothing here claims annotation
inference.

## What is not claimed

Safety is stated for terms closed in term variables (any type context), with `Step`
on erased terms; `Tm.subst` does not shift the substituted term, which is capture-free
only for term-closed terms, the only case the theorems use. `HTy.substTy`,
`preservation` and `elaboration_complete` are existence statements, not functions on
terms; no bound is claimed on the size of the annotations they produce, and the
annotation of a reduct need not be minimal. There is
no annotation-inference claim and no bound on the size of the certificates produced by
the lifts, `Sub.toCert`, narrowing or substitution. This library contains no
comparison with or embedding into the repository's FCsub; the comparison is `../FsubCompare` and the
translation into the DOT calculus is `../Bridge`. Soundness gives `Nonempty (Sub Γ S T)`, not a
function from typed certificates to derivations. Renaming is proved directly on
certificates (`CTy.rename`, which keeps their shape) and is not derived from `CTy.subst`.

## Known limits of this implementation

The probe `P3_Size.lean` named below is in `Probes/`.

- `Cert.ofPrim` expands steps the substitution does not touch: under the identity
  substitution one step between types with `m` arrows becomes `m+1` steps, quadratic in
  the stored type nodes (`P3_Size.lean`). A repair, not implemented, is to return a step
  unchanged when no free variable of its types has an entry.
- The output of `Cert.allInv` depends on the association of the chain: quadratic for a
  left-nested chain, linear for a right-nested one (`P3_Size.lean`).
- Compiled evaluation of the checker scales badly with de Bruijn depth, because
  `Ctx.lookup` goes through `Fin.cases`. The kernel is unaffected, and a pattern-matching
  lookup proved equal (`lk_eq` in `P3_Size.lean`) removes the cost. The verified checker
  is correct; it needs this routine lookup correction before any practical performance
  claim.
