# Selective subtyping for DOT-MNF: reference

The module list and the theorem inventory of the library `Selective`. The introduction is
[README.md](README.md); [`Hybrid.lean`](Hybrid.lean) collects the main statements and two examples.
The calculus is called `H` below. Its types and contexts are `DotMNF.Ty` and `DotMNF.Ctx`. `H` is an
explored design and not the DOT calculus aimed at; the README says what separates the two.

## Replay

From the repository root:

```sh
lake build Selective
lake env lean lean/Coercions/Selective/Hybrid.lean     # the entry point alone; no output means accepted
lake env lean lean/Coercions/Selective/Axioms.lean     # one line per audited declaration
```

Every line of the audit reads `[propext, Quot.sound]`, `[propext]` or "does not depend on any axioms".
The sources contain no `sorry`, no `native_decide`, no `partial` or `unsafe` definition, no `axiom`
declaration, no `set_option` and no Mathlib import. `Axioms.lean` is not imported by the library root.

## Modules

| module | content |
| --- | --- |
| `Prim.lean` | `Exp`, `memR`, `members`, `exp_iff_members`, `Exp.rename`; `Prim` (eleven rules, no transitivity), `Prim.rename`, `Prim.weaken`; `sz`, `primN`, `prim?`, `prim?_sound`, `primN_complete`, `prim?_iff`, `not_prim_of`, `Prim.decidable`; `sz_rename`, `sz_substVar`; `Chain` with `append`, `snoc`, `rename` and the lifts `fld`, `typU`, `typL`, `typ`, `allCod`, `allDom`, `all`, `andCongL`, `andCongR`, `and` |
| `Syntax.lean` | `Atom`, `Cert`, `Pos` (mutual), `Atom.root`, `HTm`, `HVal`, `HDefs`, `erase`; `rename` on all six, `Atom.root_rename`, `HTm.erase_rename`; derived `DecidableEq` (hence `BEq`); `Atom.size`, `Cert.size`, `Pos.size` |
| `Typing.lean` | `FExp`; `ATy`, `CTy`, `PTy` (mutual); `HTy`, `HDefsTy` (mutual); `HTy.atom_iff` and one inversion lemma per term and definition former |
| `Check.lean` | `memU`, `memL` with `_iff`; `synthA`, `synthC`, `synthP`; completeness, soundness, `_iff`; `checkC`, `checkC_iff`; `CTy.endpoints_unique`, `ATy.unique` |
| `Sound.lean` | `Exp.toHasTy`, `FExp.toHasTy`, `primitive_sound`; `ATy/CTy/PTy.sound`, `coercion_sound`; `elaboration_typed`, `defs_typed`, `elaboration_erases`, `compiled_safety`, `compiled_not_stuck`; `coercion_transitive`, `coercion_exists_transitive` |
| `Lift.lean` | `Cert.liftFld`, `liftTypU`, `liftTypL`, `liftAllD`, `liftAllC` (with `AllCGoal`), `liftAndL`, `liftAndR` and their `CTy` lemmas |
| `Complete.lean` | `cert_complete`, `atom_complete`, `elaboration_complete`, `defs_complete`, `typability_iff`, `coercion_iff`, `atom_iff` |
| `Annotate.lean` | the converse translation as computable functions: `DotMNF.Sub.toCert`, `DotMNF.HasTy.toAtom?` (and the wrapper `toAtom`), `DotMNF.HasTy.toH`, `DotMNF.DefsTy.toH` (structural recursion); `Sub.toCert_typed`, `HasTy.toAtom?_typed`, `HasTy.toAtom_typed`, `HasTy.toH_typed`, `DefsTy.toH_typed`; smoke checks `E3sub_toCert_checks`, `E3_toH_checks` |
| `Rename.lean` | `FExp.rename`; `ATy/CTy/PTy.rename` (mutual), `HTy/HDefsTy.rename` (mutual); `ATy.weaken`, `CTy.weaken`, `HTy.weaken` |
| `Typer.lean` | `PRename`, `DotMNF.Ty.unrename` with spec, `DotMNF.Ty.unweaken?` with `unweaken?_spec`; `DotMNF.Defs.distinct?` with `distinct?_iff`; `fexpN`, `fexps`, `fexps_iff`; `synthTm`, `synthVal`, `synthDefs` (mutual, structural, list-valued); soundness, completeness, `synthTm_iff`, `synthDefs_iff`, `HTy.decidable`, `untypable_of_synthTm` |
| `Witness.lean` | matrix rows 1-8 and 12-14, with their contexts and programs |
| `Matrix.lean` | rows 9-11 and the extra rows, the μ-bridge |
| `Negative.lean` | step-only certificates are chains (`stepOnly_iff_chain`); `R1.rebind_loses_root`; `K_receiver_free_chain`; the invariant behind `Y_no_receiver_free_chain`, `Y_no_receiver_free_coercion` |
| `Subst.lean` | re-annotation under substitution: `DotMNF.Ctx.Retypes`, `DotMNF.Sub/HasTy/DefsTy.retype`, `HTy.retype`, `HTy.subst_atom`, `Prim.subst_atom`, `CTy.subst_atom` |
| `Hybrid.lean` | the entry point: the main statements under fixed names (`prim_decided`, `prim_not_transitive`, `var_exact`, `step_rule`, `seq_rule`, `cast_rule`, `app_rule`, `cast_seq`, `cast_erases`, `atom_type_unique`, `cert_checker`, `term_checker`, `coercion_exact`, `typability_exact`, `annotation`, `annotation_checks`, `trans_is_seq`, `safety`, `not_stuck`); example 1 (`ex1_*`, `gapNeededTm`); example 2 (`ex2_*`, `recv`, `receiverProgram`, and `Reach`, `reach_step`, `reach_chain` behind `ex2_no_step_only`); `receiver_evidence_needed`, `views_typed` |
| `Axioms.lean` | `#print axioms` for every theorem, the functions of `Annotate.lean` and the three `retype` functions |
| `../Selective.lean` | the import root: every module except `Axioms.lean` |

Imports from the rest of the repository: `Coercions.DotMNF.Structural` (Prim), `Coercions.DotToFCdot`
(Sound), `Coercions.Frontend.Alg` (Witness, for `LPCtx`), `Coercions.DotMNF.Examples` (Annotate, Matrix)
and `Coercions.Frontend.Examples` (Matrix).

## Theorem inventory

All names are in namespace `Selective` unless they are written with `DotMNF.` or `R1.`.
Binders `{s} {Γ}` are implicit.

### Entry point (`Hybrid.lean`, namespace `Selective.Hybrid`)

Twelve of its nineteen main statements are references to theorems listed below. The others, and the
facts about the two examples:

| theorem | statement |
| --- | --- |
| `var_exact` | `HTy Γ (.atom (.var x)) T ↔ T = Γ.lookup x` |
| `step_rule` | `CTy Γ (.step A B) S T ↔ A = S ∧ B = T ∧ Prim Γ S T` |
| `seq_rule` | `CTy Γ (.seq c d) S T ↔ ∃ M, CTy Γ c S M ∧ CTy Γ d M T` |
| `cast_seq`, `cast_erases` | a term cast by a written composite has the composed endpoint; `(t ▷ c).erase = t.erase` |
| `annotation_checks` | `T ∈ synthTm Γ d.toH` for every `d : DotMNF.HasTy Γ t T` |
| `trans_is_seq` | `(Sub.trans d1 d2).toCert = .seq d1.toCert d2.toCert`, by `rfl` |
| `ex1_gap`, `ex1_one_step_rejected`, `ex1_term_cast`, `ex1_closed_erases` | example 1: the halves are primitive and the composite is not; `k (z ▷ step[b.B, c.C])` has no type; the composite as a term cast; the erased closed program written out |
| `ex1_nested_casts`, `ex1_one_written_step`, `ex1_term_cast_one_step` | example 1 has shorter accepted annotations: nested casts; one written step `k (z ▷ step[b.B, x.A])`, the application supplying `x.A ≤₀ c.C`; `z ▷ step[x.A, c.C] : c.C`, the cast subject supplying `b.B ≤₀ x.A` |
| `ex2_bare_rejected`, `ex2_not_primitive`, `ex2_bare_receiver_rejected`, `ex2_no_step_only`, `ex2_closed_typed` | example 2: `u.a` has no type; `y.A ≤₀ {a:⊤}` fails; the member step with the bare receiver is not a certificate; no step-only certificate relates `y.A` to `{a:⊤}` in `ΓR2` (over this `Prim`); the closed form is typed |

### Soundness, safety and composition

| theorem | statement |
| --- | --- |
| `primitive_sound` | `Prim Γ S T → Nonempty (DotMNF.Sub Γ S T)` |
| `ATy.sound` | an atom's typing gives a DOT-MNF typing of its root, `HasTy Γ (.path (.var a.root)) T` |
| `coercion_sound` | `CTy Γ c S T → Nonempty (DotMNF.Sub Γ S T)` (the mutual `CTy.sound`) |
| `PTy.sound` | `PTy Γ k S T → Nonempty (DotMNF.Sub Γ S T)` |
| `elaboration_typed` | `HTy Γ t T → Nonempty (DotMNF.HasTy Γ t.erase T)` |
| `elaboration_erases` | some DOT-MNF derivation of `t.erase` has an FCdot translation with the same runtime erasure |
| `compiled_safety` | every state that DOT-MNF's machine reaches from `⌊t⌋` of a closed typed `t` is final or steps |
| `compiled_not_stuck` | no such state is `Stuck` (via `DotMNF.dot_not_stuck`) |
| `primitive_nontrans` | `≤₀` is not transitive (witness `Γr`) |
| `realizable_nontrans` | in `Γr`: `b.B ≤₀ x.A`, `x.A ≤₀ c.C`, `¬ b.B ≤₀ c.C`, and `wit` is a certificate `b.B ⇒ c.C` |
| `coercion_transitive` | `CTy Γ c S M → CTy Γ d M T → CTy Γ (c ; d) S T` |
| `coercion_exists_transitive` | coercion existence is transitive |

### Checkers

The certificate checker is sound and complete. It has no budget of its own and
searches for no middle types in subtyping. The only fuel in it is inside `prim?`,
`sz S + sz T + 1`, fixed by the goal and proved sufficient (`prim?_iff`), so no run
ends in exhaustion. The term checker is also sound and complete. Its only fuel is in
the field lookup `fexps`, `sz V`, again fixed by the input and proved sufficient. It
still enumerates the finitely many typing alternatives (the fields of one label) and
does not deduplicate them.

| theorem | statement |
| --- | --- |
| `prim?_iff` | `prim? Γ S T = true ↔ Prim Γ S T` (fuel `sz S + sz T + 1`, fixed by the goal) |
| `synthA_iff` | `synthA Γ a = some T ↔ ATy Γ a T` |
| `synthC_iff` | `synthC Γ c = some (S, T) ↔ CTy Γ c S T` |
| `synthP_iff` | `synthP Γ k = some (S, T) ↔ PTy Γ k S T` |
| `checkC_iff` | `checkC Γ c S T = true ↔ CTy Γ c S T` |
| `CTy.endpoints_unique` | a certificate determines its endpoints |
| `ATy.unique` | an atom determines its type |
| `synthTm_iff` | `T ∈ synthTm Γ t ↔ HTy Γ t T`, the **complete** term checker |
| `synthDefs_iff` | `T ∈ synthDefs Γ d ↔ HDefsTy Γ d T` |
| `DotMNF.Ty.unweaken?_spec` | `U'.unweaken? = some U ↔ U.weaken = U'` |
| `DotMNF.Defs.distinct?_iff` | `d.distinct? = true ↔ d.Distinct` |
| `fexps_iff` | `T ∈ fexps x V a ↔ FExp x V a T` |
| `HTy.atom_iff` | an atom used as a term has exactly its atom type (no subsumption) |

### Converse translation

| theorem | statement |
| --- | --- |
| `cert_complete` | `DotMNF.Sub Γ S T → ∃ c, CTy Γ c S T` |
| `atom_complete` | `DotMNF.HasTy Γ (.path (.var x)) T → ∃ a, a.root = x ∧ ATy Γ a T` |
| `elaboration_complete` | `DotMNF.HasTy Γ t T → ∃ h, h.erase = t ∧ HTy Γ h T` |
| `defs_complete` | the same for definitions |
| `typability_iff` | `(∃ h, h.erase = t ∧ HTy Γ h T) ↔ Nonempty (DotMNF.HasTy Γ t T)` |
| `coercion_iff` | `(∃ c, CTy Γ c S T) ↔ Nonempty (DotMNF.Sub Γ S T)` |
| `atom_iff` | `(∃ a, a.root = x ∧ ATy Γ a T) ↔ Nonempty (DotMNF.HasTy Γ (.path (.var x)) T)` |
| `CTy.liftFld`, `liftTypU`, `liftTypL`, `liftAllD`, `liftAllC`, `liftAndL`, `liftAndR` | the structural rules of `Sub` are admissible for certificates |
| `DotMNF.Sub.toCert_typed` | `CTy Γ d.toCert S T` for every `d : Sub Γ S T` (the function form of `cert_complete`) |
| `DotMNF.HasTy.toAtom_typed` | `h.toAtom.root = x ∧ ATy Γ h.toAtom T` for `h : HasTy Γ (.path (.var x)) T` |
| `DotMNF.HasTy.toH_typed` | `h.toH.erase = t ∧ HTy Γ h.toH T` for `h : HasTy Γ t T` |
| `DotMNF.DefsTy.toH_typed` | `h.toH.erase = d ∧ HDefsTy Γ h.toH T` |

The functions `toCert`, `toAtom?`, `toH` are computable and reduce in the kernel
(structural recursion): `E3sub_toCert_checks` and `E3_toH_checks` check DOT-MNF's E3
by `decide`. One DOT-MNF derivation `d` thus gives both `d.toH` and `d.translate`.

### Renaming

| theorem | statement |
| --- | --- |
| `Atom.root_rename` | `(a.rename ρ).root = ρ.var a.root` |
| `ATy.rename`, `CTy.rename`, `PTy.rename` | the evidence judgments are preserved by a lookup-preserving renaming |
| `HTy.rename`, `HDefsTy.rename` | the same for annotated terms and definitions |
| `CTy.weaken`, `ATy.weaken`, `HTy.weaken` | weakening by `Rename.succ` |
| `HTm.erase_rename` | erasure commutes with renaming |

### Negative theorems

| # | theorem | location | statement |
| --- | --- | --- | --- |
| N1 | `realizable_gap`, `primitive_nontrans` | Witness | `¬ Prim Γr b.B c.C`, by inversion; `≤₀` is not transitive |
| N2 | `E3_not_prim`, `E3_rejected` | Witness | `{b:⊤} ≤₀ {a:⊤}` fails in every context; `z : {b:⊤}` has no atom type one `≤₀` step below `{a:⊤}` |
| N3 | `R1.rebind_loses_root` | Negative | `let y2 = yArg in let h = g y2 in h u` has no type in `G6` |
| N4 | `reductNaive_untypable` | Matrix | the renamed annotation of the SR reduct has no type in `Δy` |
| N5 | `Y_no_receiver_free_chain`, `Y_no_receiver_free_coercion` | Negative | no `≤₀` chain, and no step-only certificate, relates `certY`'s endpoints in `y : ⊤`: step and seq alone cannot relate them; `certY` supplies a solution with a scoped receiver |
| N6 | `K_receiver_free_chain` | Negative | the non-`⊤` example under two binders has a three-step chain without receivers |
| N8 | `fun_invertible_H` | Matrix | the function chain in `ΓW` decomposes: a domain step, and a codomain positioned step under `x : w.B` |

N7 (the programs that a calculus with casts on terms only loses) was shown in an exploratory design that
is not part of this repository, and is not proved here. N9, that the root-identity example
`g y u` needs `fold`, is a conjecture and is not proved.

### Matrix

The row theorems carry the row numbers of the example matrix that the design was checked against. Rows 1-8 and
12-14 are in `Witness.lean`. Rows 9-11 and the extra rows are in `Matrix.lean`.
There are three exceptions. The row-13 theorems (`goodK_*`, `badK_*`,
`K_not_primitive`) are in `Witness.lean`, and an extra row cites them from
there. `loop_decided` (rows 9 and 14) is in `Witness.lean`. `K_receiver_free_chain`
and the `Y_no_*` theorems are in `Negative.lean`. The R1 row is in namespace
`Selective.R1`. The μ-bridge `x : {A : μS..μT} ⊢ μS ⇒ x.A ⇒ μT` is
`muBridge_checks` and `distinct_mu_inclusion`, with `muBridge_not_primitive` and
`muBridge_different`.

### Substitution

| theorem | statement |
| --- | --- |
| `HTy.subst_atom` | `HTy (Γ.cons S) t T → ATy Γ b V → Prim Γ V S → ∃ t', t'.erase = t.erase.rename (Rename.subst b.root) ∧ HTy Γ t' (T.substVar b.root)` |
| `HTy.retype` | the inner-binder generalization: a typed renaming (`DotMNF.Ctx.Retypes`) preserves `H` typability, with re-annotation |
| `Prim.subst_atom`, `CTy.subst_atom` | a primitive step or a certificate under `z : S` becomes a certificate after `z := root b` |
| `DotMNF.HasTy.retype` (def) | DOT-MNF typing is preserved by a typed renaming (variable substitution) |

## Restrictions of `H` relative to `DotMNF.HasTy`

No erased program is lost (`typability_iff`). Each restriction costs annotations.

- R1: there is no subsumption rule. An implicit `≤₀` step happens only at an application argument and at a cast subject.
- R2: `≤₀` takes one step per position. A bound step followed by structure needs a written middle.
- R3: exposure reads the receiver's declared type. It does not read through a selection-typed receiver or from `⊥`, and it does not merge members.
- R4: there is no `μ` subtyping rule. Recursion is opened by `unfold`, `Exp` or `FExp` at a root and closed by `fold`.
- R5: implicit Rec-E happens only inside lookups (`Exp`, `FExp`). Elsewhere `unfold a` is written.
- R6: the callee gets no implicit step. A callee that needs retyping carries a cast atom.
- R7: `let` has no avoidance. The body's type must be a weakening.
- R8: object literals carry their self-type body `ν(x : T) d`, which is erased.
- R9: endpoints agree by syntactic equality of `DotMNF.Ty`. Nothing is normalized.
- R10: positioned steps navigate `fld`, both bounds of `typ`, the domain and codomain of `∀`, and both operands of `∧`. They do not go under `μ` or inside a selection.
- R11: paths are variables and terms are in MNF only.

## What is not claimed

- No direct safety proof. There is no preservation or progress theorem for `H` and no
  state typing. Safety holds only through `compiled_safety` and `compiled_not_stuck`,
  which reuse DOT-MNF and FCdot entirely.
- `HTy.subst_atom` is proved by translation. It runs `elaboration_typed`, then a
  DOT-MNF variable-substitution lemma (`DotMNF.HasTy.retype`), then
  `elaboration_complete`. The new annotation is therefore the fully explicit one that the
  converse translation builds, with no minimality guarantee. This closes re-annotation under substitution by
  translation; it does not establish local evidence repair or a smaller independent
  safety proof. Status: re-annotation under substitution: proved (`HTy.subst_atom`);
  local repair of the original evidence, direct machine preservation and progress for `H`: open.
- The term checker is complete (`synthTm_iff`), so term typing is decided. The checker
  implementation has a known limitation that the calculus does not have. `fexpN`
  concatenates the alternatives of an intersection without deduplication, and
  `synthTm` checks a `let` body once for every entry of the bound term's type list.
  Duplicate field declarations therefore produce exponentially many duplicate types in
  the output list, even when there is one distinct type. An independent check found
  `x : {a:⊤} ∧ {a:⊤}` with `n` nested `let _ = x.a` giving a list of length
  `2^(n+1)`. The correctness theorems are unaffected.
- `synthTm` and the certificate checker discover no evidence. Annotation inference,
  minimal annotations and bounds on annotation size are not addressed.
- That the root-identity example `g y u` needs `fold` (N9) is a conjecture; it is not proved.
- Coverage is for the whole of DOT-MNF, the repository's WadlerFest DOT in monadic normal form
  (`DotMNF.Ty`, `DotMNF.HasTy`, `DotMNF.Sub`). Only features outside that grammar are outside this
  result: paths longer than a variable (pDOT), nominal types, unions.
