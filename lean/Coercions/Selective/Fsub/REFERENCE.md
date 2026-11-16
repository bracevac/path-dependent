# Selective transitivity for full F-sub: reference

The introduction is [README.md](README.md). This file lists the modules and the theorems.

The library `SelectiveFsub` (modules `Coercions.Selective.Fsub.*`, namespace `SelFsub`) imports
nothing outside its directory. Types are `Top | X | S → T | ∀(X <: S). T`, intrinsically scoped
(`Ty n`, de Bruijn indices in `Fin n`). Contexts are ordered lists of upper bounds, each scoped
before its binder. The rule for universals is the full one: bounds are contravariant and bodies
are compared under the target bound. Certificates are

```text
c, d ::= step[S, T] | c ; d
Γ ⊢ step[S,T] : S ⇒ T   if  Γ ⊢ S ≤₀ T
Γ ⊢ c ; d : S ⇒ T       if  Γ ⊢ c : S ⇒ M  and  Γ ⊢ d : M ⇒ T   (the same M, syntactically)
```

From the repository root:

```sh
lake build SelectiveFsub
lake env lean lean/Coercions/Selective/Fsub/Axioms.lean
```

Each line of the audit reads `[propext]`, `[propext, Quot.sound]` or "does not depend on any
axioms". Every function is structural recursion, so the kernel evaluates the checkers and the
operations on certificates; the examples are checked by `decide` and `rfl`.

## Modules

| file | content |
| --- | --- |
| `Syntax.lean` | `Ty`, renaming, substitution, `Ctx`, `lookup`, telescopes; de Bruijn lemmas |
| `Prim.lean` | `Prim` (five rules), the checker `prim?`, `prim?_iff`, `Prim.inv`, renaming; the nontransitivity witnesses and `primitive_nontrans` |
| `Cert.lean` | `Cert`, `CTy`, endpoints; the checkers `synthC`, `checkC` with their `_iff`; renaming |
| `Sub.lean` | declarative full F-sub `Sub` (`Type`-valued), `primitive_sound`, `coercion_sound`, `coercion_transitive` |
| `Lift.lean` | certificates under an arrow and under a universal |
| `Complete.lean` | `Sub.toCert`, `Sub.toCert_typed`, `coercion_iff` |
| `Subst.lean` | certified substitutions `CSub`; `Cert.subst`, `CTy.subst`; narrowing and type substitution under a telescope |
| `Invert.lean` | `CTy.top_inv`; `Cert.arrInv`, `CTy.arr_inv`; `Cert.allInv`, `CTy.all_inv` |
| `Witness.lean` | examples for certificates |
| `Term.lean` | terms with casts, `erase`, renaming and substitution with their commutation lemmas |
| `Typing.lean` | `HTy`, `HTy.unique`, the checker `synthTm`, `synthTm_iff` |
| `Safety.lean` | `Value`, `Step`, `Steps`; substitution lemmas, canonical forms, `preservation`, `progress`, `safety`; determinism |
| `Exact.lean` | declarative F-sub term typing `FTy`, `typability_iff`, `fsub_preservation`, `fsub_safety` |
| `Elab.lean` | derivations of `FTy` as data (`FDer`), the elaborator `FDer.elab`, `FDer.elab_erase`, `FDer.elab_typed` |
| `Reduction.lean` | closed terms, the standard substitution and call-by-value relation, `step_iff_std`, `safety_std`; cast-freeness along reduction; the counterexample for open terms |
| `Examples.lean` | examples for terms |
| `Axioms.lean` | `#print axioms` for every theorem and the main functions (not imported by the root) |
| `../Fsub.lean` | the import root: all modules except `Axioms` |

## Theorems

All names are in namespace `SelFsub`; the examples are in `SelFsub.Witness` and
`SelFsub.Examples`.

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

Examples for certificates (`Witness.lean`):

- `chainL_typed`, `chainR_typed`, `chain_not_prim`, `chain_step_rejected`, `chain_middle_not_prim`: three bound steps `X ⇒ Y ⇒ Z ⇒ Top → Top` in both associations, none of the composites primitive, and the single step rejected by the checker.
- `arr_typed`, `arr_not_prim`: chains in an arrow domain and result. `all_typed`, `all_not_prim`: chains in a universal bound and body.
- `bad_parts`, `bad_rejected`, `bad_untyped`, `good_typed`: `step[X,Y] ; step[Top→Top, Top→Top]` is rejected though both parts check, and `step[X,Y] ; step[Y, Top→Top]` checks for the same outer endpoints.
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

Safety (`Safety.lean`), for terms closed in term variables, in every type context `Γ`:

- `HTy.renTy : TyRen Γ Γ' ρ → HTy Γ Δ t T → HTy Γ' (Δ.map (rename ρ)) (t.renTy ρ) (T.rename ρ)`; `HTy.append : HTy Γ Δ t T → ∀ Δ', HTy Γ (Δ ++ Δ') t T`.
- `HTy.subst : HTy Γ (Δ ++ [S]) t T → HTy Γ [] w S → HTy Γ Δ (t.subst Δ.length w) T`.
- `HTy.substTy : CSub Γ Γ' σ τ → HTy Γ Δ t T → ∃ t', t'.erase = t.erase.substTy σ ∧ HTy Γ' (Δ.map (subst σ)) t' (T.subst σ)`.
- `HTy.canon_lam : HTy Γ Δ t T → t.erase = λ(x : S). e₀ → ∃ b T₀ c, b.erase = e₀ ∧ HTy Γ (S :: Δ) b T₀ ∧ CTy Γ c (S → T₀) T`; `HTy.canon_tlam` likewise for `Λ`, with the body under `Γ, X <: S`.
- `preservation : HTy Γ [] t T → Step t.erase e' → ∃ t', t'.erase = e' ∧ HTy Γ [] t' T`.
- `progress : HTy Γ [] t T → Value t.erase ∨ ∃ e', Step t.erase e'`.
- `safety : HTy Γ [] t T → Steps t.erase e → Value e ∨ ∃ e', Step e e'`.
- `Value.no_step : Value v → ¬ Step v e`; `Step.det : Step e e₁ → Step e e₂ → e₁ = e₂`.

Correspondence with declarative F-sub (`Exact.lean`):

- `FTy.erase_eq : FTy Γ Δ e T → e.erase = e`.
- `elaboration_typed : HTy Γ Δ t T → FTy Γ Δ t.erase T`.
- `elaboration_complete : FTy Γ Δ e T → ∃ t, t.erase = e ∧ HTy Γ Δ t T`.
- `typability_iff : (∃ t, t.erase = e ∧ HTy Γ Δ t T) ↔ FTy Γ Δ e T`.
- `fsub_preservation : FTy Γ [] e T → Step e e' → FTy Γ [] e' T`.
- `fsub_safety : FTy Γ [] e T → Steps e e' → Value e' ∨ ∃ e'', Step e' e''`.

The elaborator as a function (`Elab.lean`):

- `FDer Γ Δ e T : Type` has the rules of `FTy`; `FDer.toFTy : FDer Γ Δ e T → FTy Γ Δ e T`, `FTy.toFDer : FTy Γ Δ e T → Nonempty (FDer Γ Δ e T)`.
- `FDer.elab : FDer Γ Δ e T → Tm n`: subsumption becomes a cast by `Sub.toCert`, and a type application casts its callee along the lifted bound.
- `FDer.elab_erase : (d : FDer Γ Δ e T) → d.elab.erase = e`; `FDer.elab_typed : (d : FDer Γ Δ e T) → HTy Γ Δ d.elab T`.

Reduction (`Reduction.lean`). `Tm.cl k t` says that the free term variables of `t` are below `k`;
`Tm.substStd` is the standard substitution, which shifts the substituted term under term binders,
and `StepStd` is call-by-value reduction with it.

- `HTy.cl : HTy Γ Δ t T → Tm.cl Δ.length t`; `Step.cl : Step e e' → Tm.cl 0 e → Tm.cl 0 e'`.
- `Tm.substStd_eq : Tm.cl 0 w → Tm.substStd t k w = t.subst k w`.
- `step_iff_std : Tm.cl 0 e → (Step e e' ↔ StepStd e e')`; `steps_iff_std` for sequences.
- `safety_std : HTy Γ [] t T → StepsStd t.erase e → Value e ∨ ∃ e', StepStd e e'`.
- `Steps.castfree : Steps t.erase e → CastFree e`; `Tm.substTy_erase : t.substTy σ = t.erase.substTy σ`.
- `open_step`, `open_capture`, `open_typed`, `open_preservation_fails`: in the term context `[Top → Top]` a typed redex steps by `Step` to a term in which a free variable is captured, and no annotation of that term has the type of the redex.

Examples for terms (`Examples.lean`), all by `decide` or `rfl`:

- `arg_bare_rejected`, `arg_one_step_rejected`, `arg_cast_typed`, `arg_one_written_typed`: `Λ(Y <: Top → Top). Λ(X <: Y). λ(x : X). (λ(g : Top → Top). g) x` is rejected bare and with the single cast `step[X, Top → Top]`. It is accepted with `x ▷ (step[X,Y] ; step[Y, Top → Top])` and with `x ▷ step[X, Y]`, where the argument check supplies the second step. `argRun_typed`, `argRun_steps`, `argRun_value`: applied, it runs to `λ(z : Top). z`.
- `nest_typed`, `nest_subject_rejected`, `nest_mismatch_rejected`: nested casts compose through their written endpoints only; the subject of a cast gets no implicit step.
- `calleeF_typed`, `callee_bare_rejected`, `calleeApp_typed`: a type application two bound steps below the bound, accepted with a cast on the callee by `Cert.allBound`.
- `tb_step`, `tb_bare_rejected`, `tbReduct_erase`, `tbReduct_typed`, `tbEntry_eq`, `tb_arg_cast`, `tb_arg_cast_typed`: after type-β the erased reduct is rejected bare; an annotation with the chain on the argument is typed, and the cast that the proof of preservation inserts is computed by `Cert.subst`.
- `bRedex_typed`, `b_step`, `b_bare_rejected`, `b_min_typed`, `bReduct_erase`, `bReduct_typed`: a β-step after which two implicit steps meet at one argument. The bare reduct is rejected; annotations with one written step and with the casts that the proof of preservation constructs are typed.
- `gProg_typed`, `g_step`, `g_bare_rejected`, `gReduct_typed`: a program without casts whose β-reduct is rejected bare and typed with a cast on the callee of a type application.
- `hProg_typed`, `h_steps`, `h_bare_rejected`, `h_one_step_rejected`, `h_two_steps_typed`: a program without casts whose reduct after two β-steps is rejected bare and with the displayed single step, and typed with the displayed composition of two.
- `cap_step`, `cap_std`, `cap_typed`: β under a type binder shifts the type variables of the substituted value.

## Scope

Safety is stated for terms closed in term variables (any type context), with `Step`
on erased terms; `Tm.subst` does not shift the substituted term, which is capture-free
only for term-closed terms, the only case the theorems use. On such terms `Step` is standard
call-by-value (`step_iff_std`); on open terms it captures and preservation fails
(`open_capture`, `open_preservation_fails`).

`HTy.substTy`, `preservation` and `elaboration_complete` are existence statements, not functions
on terms. A program typed without casts can reach a reduct whose annotation has casts (`gProg`,
`hProg`), while every term on a reduction sequence from an erased term is cast-free
(`Steps.castfree`). No bound is claimed on the number of written steps a reduct needs or on the
size of the certificates produced by the lifts, `Sub.toCert`, narrowing or substitution.
Soundness gives `Nonempty (Sub Γ S T)`, not a function from typed certificates to derivations.

The checkers decide `≤₀` and check written certificates and annotated terms. Nothing here infers
annotations. Subtyping in full F-sub is undecidable (Pierce, "Bounded quantification is
undecidable", POPL 1992; not formalized here), and by `coercion_iff` the existence of a
certificate coincides with it, so no terminating procedure decides whether a certificate exists.
