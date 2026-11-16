# Type safety of declarative full F-sub, proved directly: reference

The introduction is [README.md](README.md).

The library `SelectiveFsubDeclarative` (modules `Coercions.Selective.FsubDeclarative.*`, namespace
`SelFsub`) proves type safety of plain full F-sub for the syntax, the reduction relation and the
declarative typing of [`../Fsub`](../Fsub/README.md), directly on the declarative
system: `FTy` with its ordinary subsumption rule over `Sub`, and `Sub` with its `trans`
constructor. There are no certificates, no primitive relation and no annotated terms. It
is the matched control for the certificate route of `../Fsub/Safety.lean`: the
same theorem, the same `Value`, `Step`, `Steps`, `FTy`, `Sub`, `Ty`, `Tm` (imported, not
copied), in the same proof style.

## Replay

From the repository root:

```sh
lake build SelectiveFsubDeclarative
lake env lean lean/Coercions/Selective/FsubDeclarative/Axioms.lean     # 18 lines
lake env lean lean/Coercions/Selective/FsubDeclarative/Deps.lean       # dependency check, 92 lines
```

Every line of the audit reads `[propext]` or `[propext, Quot.sound]`. The sources
contain no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom` declaration,
`set_option`, `Classical` or Mathlib import. `Deps.lean` imports `Lean` for its
metaprogram; the library modules import only `Coercions.Selective.Fsub.Exact` and each other.
Neither `Axioms.lean` nor `Deps.lean` is imported by the library root.

## Theorems

All in namespace `SelFsub` (`Safety.lean`), for terms closed in term variables
in an arbitrary type context `Γ`, the statement shape of `SelFsub.fsub_safety`:

```text
fsub_progress      : FTy Γ [] e T → Value e ∨ ∃ e', Step e e'
fsub_preservation  : FTy Γ [] e T → Step e e' → FTy Γ [] e' T
fsub_safety_direct : FTy Γ [] e T → Steps e e' → Value e' ∨ ∃ e'', Step e' e''
```

`FTy` is a `Prop` with `Sub` derivations (a `Type`) as fields, so the headline statements
need no `Nonempty`. The lemmas on `Sub` are functions on derivations (`def`); the
inversion lemmas return their component derivations under `Nonempty`, and `TySub` (for
each variable, a derivation that its image lies below its substituted bound) is a
`Type`.

## Modules and lemmas

Lines are declaration blocks: the declaration with its docstring, without the blank lines
around it. Module docstrings, imports, `namespace`/`end` and section headers are counted
only in the file totals.

| file | lines | declarations |
| --- | --- | --- |
| `Sub.lean` | 112 | 76 lines of declarations: group (i) |
| `Typing.lean` | 94 | 69 lines of declarations: group (ii) |
| `Safety.lean` | 76 | 54 lines of declarations: group (iii) |
| `../FsubDeclarative.lean` | 3 | the import root |
| `Axioms.lean` | 25 | `#print axioms` for all 18 declarations |
| `Deps.lean` | 80 | the dependency check below |

| group | lemma | lines | content |
| --- | --- | --- | --- |
| (i) renaming | `Sub.rename`, `Sub.weaken` | 8 + 2 | along `TyRen`; the bound axiom is rewritten by `TyRen` |
| (i) substitution | `TySub`, `TySub.lift` | 3 + 7 | the evidence of a substitution, lifted under a binder |
| (i) substitution | `Sub.subst` | 8 | bound axiom ↦ the supplied derivation, `trans` ↦ `trans`, arrow and universal recurse |
| (i) substitution | `TySub.inst` | 5 | instantiating `X <: U` by `V` with `V <: U` |
| (i) narrowing | `Sub.narrow` | 8 | instance of `Sub.subst` at `σ = var`, the bound axiom on `X` becoming `X <: U' <: U` |
| (i) inversion | `Sub.top_inv` | 5 | out of `Top` |
| (i) inversion | `Sub.arr_inv` | 14 | out of an arrow: `Top` or an arrow with the components; `trans` composes |
| (i) inversion | `Sub.all_inv` | 16 | out of a universal; `trans` composes, the first body narrowed to the second bound |
| (ii) renaming | `FTy.renTy`, `FTy.append` | 13 + 12 | type renaming; term variables added on the outside |
| (ii) term substitution | `FTy.subst` | 19 | a term-closed `w` of exactly the variable's type |
| (ii) type substitution | `FTy.substTy` | 13 | along a `TySub`; each `Sub` premise mapped by `Sub.subst` |
| (ii) canonical forms | `FTy.canon_lam`, `FTy.canon_tlam` | 6 + 6 | an abstraction's own typing and a `Sub` to the given type, subsumptions composed by `trans` |
| (iii) | `fsub_preservation` | 24 | β by `arr_inv` and `FTy.subst`; type-β by `all_inv`, `FTy.substTy` and `Sub.subst` along `TySub.inst` |
| (iii) | `fsub_progress` | 25 | a `Λ` at an arrow type and a `λ` at a universal type are excluded by `all_inv`, `arr_inv` |
| (iii) | `fsub_safety_direct` | 5 | induction on `Steps` |

Totals: (i) 76 (renaming 10, substitution and narrowing 31, inversion 35), (ii) 69
(renaming 25, term substitution 19, type substitution 13, canonical forms 12), (iii) 54;
199 lines of declarations in 282 file lines.

Reused, not restated. From `SelFsub.Syntax`: `Ty`, `rename`, `weaken`, `liftRen`, `liftS`,
`subst`, `sub0`, `Ctx`, `lookup`, and the lemmas `Ty.rename_weaken`, `Ty.weaken_subst`,
`Ty.weaken_sub0`, `Ty.subst_var` (directly) and `Ty.rename_rename`, `Ty.subst_rename`,
`Ty.rename_subst`, `liftRen_comp`, `liftS_var` (through them). From `SelFsub.Term`: `Tm`,
`Tm.renTy`, `Tm.substTy`, `Tm.subst`, `Ty.rename_sub0`, `Ty.subst_sub0` (and through them
`Ty.subst_subst`, `liftS_comp`). From `SelFsub.Prim`: the context-level renaming predicate
`TyRen` with `TyRen.lift`, `TyRen.weaken` (they mention no `Prim`). From `SelFsub.Sub`:
`Sub`; from `SelFsub.Safety`: `Value`, `Step`, `Steps`; from `SelFsub.Exact`: `FTy`.
Not used: telescopes (`Tele`, `Ctx.append`, `Tele.subst`, `liftN`, `liftN_var`,
`Tele.subst_var`), `Tm.erase` and its lemmas. Added syntactic lemmas: none.

## Dependency check

`Deps.lean` computes, for each headline theorem, the transitive closure of the constants
mentioned by types and values (with the constructors of every inductive reached), lists
the constants of namespace `SelFsub` in it by declaring module, and intersects it with 31
constants of the certificate layer: `Prim`, `PrimAt`, `prim?`, `CTy`, `Cert.subst`,
`Cert.ofPrim`, `Cert.narrow`, `Cert.inst`, `Cert.arrInv`, `Cert.allInv`, `Cert.allBound`,
`CSub`, `CTy.subst`, `CTy.narrow`, `CTy.inst`, `CTy.arr_inv`, `CTy.all_inv`, `HTy`,
`synthC`, `synthTm`, `preservation`, `progress`, `safety`, `Sub.toCert`, `Sub.toCert_typed`,
`primitive_sound`, `coercion_sound`, `elaboration_typed`, `elaboration_complete`,
`typability_iff`, `fsub_safety`. Result, as `Deps.lean` prints it:

- `fsub_progress`, `fsub_preservation`, `fsub_safety_direct`: forbidden constants reached:
  `[]`. As a control, the same test on `SelFsub.fsub_safety` and `SelFsub.safety` lists
  the certificate constants.
- The constants of the certificate modules that the closure does reach are `Cert`,
  `Cert.step`, `Cert.seq`, `Cert.rename` (module `Coercions.Selective.Fsub.Cert`) and `TyRen`,
  `TyRen.lift`, `TyRen.weaken` (module `Coercions.Selective.Fsub.Prim`). The first four come from the
  shared term syntax: `Tm.cast` stores a `Cert`, and `Tm.renTy` renames it with
  `Cert.rename`. No certificate typing, no operation on certificates beyond that renaming
  and no lemma about certificates is reached, and no proof here builds a cast. Removing
  `Cert` from the closure would require a different, cast-free term syntax, and with it a
  different `Step`.
- The full list of `SelFsub` constants reached is printed by `Deps.lean`: from `Syntax`, `Term`,
  `Sub` (the inductive only), `Safety` (`Value`, `Step`, `Steps`), `Exact` (`FTy` only),
  and the two items above.

## Matched comparison with the certificate route

The certificate route's `SelFsub.safety` imports `Typing → Term → Invert → Subst → Lift
→ Cert → Prim → Syntax`; it does not import `Sub`, `Complete` or `Exact`. Running the same
closure on `SelFsub.safety` (the last block that `Deps.lean` prints) determines which declarations it
reaches; the lines below are declaration blocks counted the same way as above.

Not counted on either side:

- shared definitions and bookkeeping used by both: `Syntax` (except the telescope items),
  `Tm`, `Tm.renTy`, `Tm.substTy`, `Tm.subst`, the four type lemmas of `Term`, `TyRen` and
  its two lemmas, `Value`, `Step`, `Steps`;
- the definitions of the systems themselves: `Prim` 6, `Cert` 4, `CTy` 3, `HTy` 7,
  `Tm.erase` 8 (28 lines) against `Sub` 7, `FTy` 7 (14 lines);
- the certificate system's interface, which `safety` does not reach and the declarative
  route does not need at all (177 lines): `PrimAt`, `boundIs`, `primDir`, `prim?` with
  `primDir_base`/`_sound`/`_complete`, `prim?_iff` and decidability (65), the
  nontransitivity witnesses and `primitive_nontrans` (17), `Cert.valid`, `synthC`,
  `checkC`, their `_iff` lemmas, decidability and `CTy.endpoints_unique` (27),
  `HTy.unique`, `synthTm`, `synthTm_sound`/`_complete`/`_iff` and decidability (63),
  `Tm.erase_erase` (5);
- module docstrings, imports, section headers and blank lines.

The safety argument proper, everything else that the respective safety theorem reaches:

| part | certificate route | lines | declarative route | lines |
| --- | --- | --- | --- | --- |
| (i) renaming | `Prim.rename`, `Prim.weaken`, `Cert.weaken`, `CTy.rename`, `CTy.weaken` (`Cert.rename`, 3 lines, is shared: see below) | 18 | `Sub.rename`, `Sub.weaken` | 10 |
| (i) substitution, narrowing, instantiation | `Subst` (115: entries and `CSub` with lifts 32, `Cert.ofPrim` with its typing 33, `Cert.subst`/`CTy.subst` 9, narrowing 22, instantiation 19), `Lift` (47), `Prim.inv` (11), `Cert.src`/`tgt`/`CTy.endpoints` (10), telescopes in `Syntax` (20) | 203 | `TySub`, `TySub.lift`, `Sub.subst`, `TySub.inst`, `Sub.narrow` | 31 |
| (i) inversion | `Invert`: `CTy.top_inv`, `Cert.arrInv`, `CTy.arr_inv`, `Cert.allInv`, `CTy.all_inv` | 54 | `Sub.top_inv`, `Sub.arr_inv`, `Sub.all_inv` | 35 |
| (ii) renaming, weakening | `HTy.renTy`, `HTy.append` | 25 | `FTy.renTy`, `FTy.append` | 25 |
| (ii) term substitution | `HTy.subst` | 19 | `FTy.subst` | 19 |
| (ii) type substitution | `HTy.substTy` (existential, re-annotation) | 31 | `FTy.substTy` | 13 |
| (ii) canonical forms | `HTy.canon_lam`, `HTy.canon_tlam` | 15 | `FTy.canon_lam`, `FTy.canon_tlam` | 12 |
| (ii) erasure | `Tm.erase_renTy`, `Tm.erase_subst` | 19 | none | 0 |
| (iii) preservation | `preservation` | 40 | `fsub_preservation` | 24 |
| (iii) progress | `progress` | 29 | `fsub_progress` | 25 |
| (iii) safety | `safety` | 6 | `fsub_safety_direct` | 5 |
| total | | 459 | | 199 |

By group: (i) 275 against 76, (ii) 109 against 69, (iii) 75 against 54. The declarative
route is shorter for the safety argument proper by 260 lines: 199 against 459, that is
43% of the certificate route's length, or 57% fewer lines.

Two accounting notes. `Cert.rename` (3 lines) is reached on both sides, since the shared
`Tm.renTy` renames casts; the table counts it on neither side, as shared bookkeeping
(counted on both, the totals would be 462 against 202). The table compares `safety` (about `HTy`) with `fsub_safety_direct` (about
`FTy`). To state the same source-level theorem, the certificate route also needs its
exactness bridge from `FTy` (`elaboration_complete` and what it reaches, `Sub.toCert`
with the lifts; not counted here), so the omission favours the certificate route. The
certificate route uses narrowing and instantiation only at depth 0 (`CTy.narrow .nil`,
`CSub.inst … .nil`); its telescope generality (the 20 lines in `Syntax`, `liftNT` 3,
`CSub.liftTele` 4, and two lines of `CSub.narrow`) is reached but
not needed at greater depth. Without it the certificate route would be about 433 lines,
which does not change the comparison.

Where the difference comes from, in these two proofs:

- Substitution, 172 of the 260 lines. `Sub.subst` maps a derivation structurally: the
  bound axiom on `x` becomes the derivation that `TySub` supplies for `x`, `trans`
  becomes `trans`, arrows and universals recurse (lifting the evidence under the
  universal body). A certificate stores the endpoint types of each step and no
  derivation, so `Cert.subst` rebuilds every primitive step from its two stored types
  (`Cert.ofPrim` and its typing lemma, by `Prim.inv`), recombining structural steps
  through the lifts of `Lift` and the endpoint functions `Cert.src`/`tgt`; the entries
  of a certified substitution are options so that unchanged variables keep a primitive
  bound step. Narrowing and instantiation are instances on both sides.
- Inversion, 19 lines. Both are inductions with a composition case (`trans` here, `;`
  there) and narrowing in the universal case. The certificate side also defines the
  component functions `Cert.arrInv`/`allInv` (12 lines) and handles the step case through
  `Prim.inv` rather than by constructor cases. On this route the canonical forms need
  inversion only with an arrow or a universal on the left, which is a direct induction on
  the declarative derivation; no algorithmic subtyping relation and no transitivity
  elimination occur in this proof.
- Type substitution on typings, 18 lines. `FTy.substTy` maps each `Sub` premise and the
  subsumption case by `Sub.subst`; `HTy.substTy` is an existence statement that inserts a
  cast at every application argument and type-application callee.
- Erasure and preservation, 35 lines. On the certificate route `Step` acts on erased
  terms and the invariant is "the erased term has a typed annotation": preservation
  exposes the erased subterms before case analysis, returns a new annotated term with an
  erasure equation, and needs `Tm.erase_renTy`, `Tm.erase_subst`. Here the invariant is
  the typing itself and the subsumption case is one line.
- Renaming, 8 lines: two relations (`Prim`, `CTy`) and certificate weakening against one.
- Equal or nearly equal: renaming and weakening of typings and term substitution are the
  same proofs line for line (`sub` in place of `cast`); canonical forms are 12 against 15
  (`trans` in place of `;`); progress 25 against 29.

These numbers compare the two proofs in front of us and nothing else.

## Not proved

Nothing stated is admitted. As on the certificate route, preservation, progress and
safety are stated for terms closed in term variables (empty term context, any type
context); `Tm.subst` does not shift the substituted term, which is capture-free for
term-closed terms only. Not claimed: anything for open terms, determinism of `Step`, a
function from the inversion lemmas' `Nonempty` components to derivations.
