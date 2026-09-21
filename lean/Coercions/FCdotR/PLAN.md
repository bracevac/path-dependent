# THE PLAN — FCdotR

## A. DECISION

Build **Design 2 with the observation sort's subject generalised from `BVar s .var` to Oopsla16's two-zone `Vr σ s`** (proposal *within-2*), because it is the only one of the three whose substitution lemma has a true statement, and because generalising the subject is exactly the unification of the reference's own case split (`subst_aux` sends `htp` at the substituted head to `htpy`, at every other head to `htp`). Grafted in: from *FCdotR-Z*, the zone lattice `abs x ⊑ conc ℓ` proved first, the closure list of constructible substitutions with its deliberately excluded case, and the typed-restriction shape (F1) in place of within-2's false context-equality (M); from *FCdotR-B*, the union formers `orI`/`orE` with their `combine` matrix. Rejected: *FCdotR-B* outright — `Γ.upTo (root a) ⊢ e : S ≤ T` does not typecheck under intrinsic scoping, and its `BIND` at `S := (p.B)^` reproduces the packing counterexample through the context entry; *FCdotR-Z* outright — its `O-Base` substitution clause is false, and repairing it reintroduces within-2's witness field, at which point it *is* within-2 with the subject erased.

Three defects the attacks found are fixed below and are the plan's own content: **(i)** `Subst.Typed` keeps FCdot's atom field and *adds* the `Vc` field, in two layers; **(ii)** the typedness of the restricted substitution is a **derived lemma**, not a field, so the circularity at `.here` does not arise; **(iii)** the derivation it needs is supplied by a new **locality lemma for `Vc`**, which is the target's own reading of `GH = GU ++ GL`.

## B. THE SUBSTITUTION LEMMA

### B.0 The prefix apparatus at `Vr`

Extend `Oopsla16/Context.lean` from `BVar s .var` to `Vr σ s`:

```
scopeUpTo   (abs x) = scopeUpTo x      scopeUpTo   (conc ℓ) = []
renameUpTo  (abs x) = renameUpTo x     renameUpTo  (conc ℓ) = renameNil
Γ.upTo      (abs x) = Γ.upTo x         Γ.upTo      (conc ℓ) = .nil
selfOf      (abs x) = abs (varUpTo x)  selfOf      (conc ℓ) = conc ℓ
Vc : Store σ σ → Ctx σ s → (p : Vr σ s) → Ty σ (scopeUpTo p) → Type
```

`scopeUpTo (conc ℓ) = []` is not a convention: the store scope `σ` is never truncated, so a location is in scope in every prefix. This single definition unifies `stp_sel1/2`'s `renameUpTo x` with `stp_strong_sel1/2`'s `renameNil`.

**Lemma Z (zone monotonicity).** No `Vc` or `LeCo` former changes the zone of an index; substitution maps `abs x` to either zone and `conc ℓ` only to `conc (θ.loc ℓ)`. Three-line induction; prove it first (§H, M1).

### B.1 Lemma 0 — locality of `Vc` (new; the load-bearing device)

> **Lemma 0.** `Vc G Γ (abs x) T  ≃  Vc G (Γ.upTo x) (abs (varUpTo x)) T`, transported along `scopeUpTo (varUpTo x) = scopeUpTo x`; and `Vc G Γ (conc ℓ) T ≃ Vc G .nil (conc ℓ) T`.

Proof: one induction over `Vc`. Every former at index `p` consults only `Γ.upTo p` — `vcVar` reads `Γ.lookupAt x`, and `(Γ.upTo x).lookupAt (varUpTo x) = Γ.lookupAt x`; `vcSub` reads `Γ.upTo x`, and `(Γ.upTo x).upTo (varUpTo x) = Γ.upTo x`; `vcUnfold`, `vcLoc`, `vcPack` read no context. Auxiliaries (both true, both missing from every proposal): `(Γ.upTo x).lookupAt y = Γ.lookupAt ((renameUpTo x).var y)` and `(Γ.upTo x).upTo y = Γ.upTo ((renameUpTo x).var y)`, with `scopeUpTo ((renameUpTo x).var y) = scopeUpTo y`.

Lemma 0 *is* `GH = GU ++ GL`: a variable's observation evidence is determined by its own prefix. The reference states it as an appendix side condition; here it is a strengthening/weakening isomorphism, and it is what makes B.4 non-circular.

### B.2 Restriction families (replacing within-2's (M))

`Subst.Mono σ Γ θ Γ'` is **data**: for each `x : BVar s₁ .var` a substitution `θ↾x : Subst σ (scopeUpTo x) σ' (scopeUpTo (θ.vr x))`, subject to

* **(★)** `(T.rename (renameUpTo x))[θ] = (T[θ↾x]).rename (renameUpTo (θ.vr x))` for all `T : Ty σ (scopeUpTo x)`;
* **(coh)** `(θ↾x)↾y = θ↾((renameUpTo x).var y)`.

There is **no** requirement `(Γ.upTo x)[θ↾x] = Γ'.upTo (θ.vr x)`; that equality is what `Subst.selfCast` violates (`FormAlgebra.lean:642` composes `pi`/`dfun` forms through it), and it is not needed.

Closure (proved once, ~150 lines): `ofRename ρ` for monotone `ρ` (weaken, lift, succ) with `(ofRename ρ)↾x = ofRename (ρ↾x)`, free because `scopeUpTo (.there y) = scopeUpTo y` and `Ctx.upTo (.cons Γ _) (.there y) = Γ.upTo y` are *definitional*; `selfCast E` with `↾x = id`; `single a` (B.5); composition; `lift`, monotone because `θ.lift↾(.there y) = θ↾y` on the nose.

### B.3 The two layers

```
structure Subst.Ev G (Γ : Ctx σ s₁) (θ : Subst.Mono …) (Γ' : Ctx σ' s₂) : Prop where
  vc : ∀ x, Vc G Γ' (θ.vr x) ((Γ.lookupAt x)[θ↾x])

structure Subst.Typed … extends Subst.Ev where
  var : ∀ x, Γ' ⊢ₐ θ.var x : (Γ.lookup x).rename θ.root
```

`Subst.Ev` is what evidence substitution consumes; `Subst.Typed` adds FCdot's atom field, which **is not deleted** — `Tm.substAtom` replaces a variable by an atom carrying its cast wrappers (`Machine.lean:126,133,142`), and `vcToAtom` produces *some* atom of the right root, not the one the reduct contains. The layering is justified by the structural fact that carries the whole design: **FCdotR's inclusion and observation evidence contain no atoms** (`defL` carries a store index, `selL` carries a `Vc`, `Vc` has no atom premise), so the dependency runs Atom → LeCo/Vc and never back. The `Vc` field is the reference's `Definition Subst` (`dot_soundness.v:262`), whose hypothesis is `htpy m1 G x (substt x TX)` and not a `has_type`.

### B.4 Lemma R — the restriction is typed (derived, not assumed)

> **Lemma R.** `Subst.Ev G Γ θ Γ'` implies `Subst.Ev G (Γ.upTo x) (θ↾x) (Γ'.upTo (θ.vr x))` for every `x`.

Proof. Fix `y : BVar (scopeUpTo x) .var`, let `z = (renameUpTo x).var y`. The outer field gives `Vc G Γ' (θ.vr z) ((Γ.lookupAt z)[θ↾z])`. By Lemma 0 (strengthen), that is a `Vc` over `Γ'.upTo (θ.vr z)`; by Lemma 0 (weaken) and `(Γ'.upTo (θ.vr x)).upTo (…) = Γ'.upTo (θ.vr z)` it re-enters `Γ'.upTo (θ.vr x)`. The type matches by (coh) and the B.1 auxiliaries. ∎

This is the fix for the circularity both cost attacks found: at `x = .here` the statement instantiates to `Subst.Ev G Γ θ Γ'` — harmless as a *theorem instance*, fatal only as a structure *field*.

### B.5 The lemmas

> **Lemma 1 (Vc).** `Subst.Ev G Γ θ Γ'` and `Vc G Γ p T` imply `Vc G Γ' (θ.vr p) (T[θ↾p])`.
> **Lemma 2 (inclusion).** `Subst.Ev G Γ θ Γ'` and `Γ ⊢ e : S ≤ T` imply `Γ' ⊢ e[θ] : S[θ] ≤ T[θ]`.
> **Lemma 3 (atoms/terms/defs).** `Subst.Typed` transports `⊢ₐ`, `⊢`, `⊢d`; statements unchanged from FCdot.
> **Lemma 4 (embeddings).** (a) `vcToAtom : Vc G Γ p T → Γ ⊢ₐ a : T.rename (renameUpTo p)` with `root a = p`. (b) `atomToVc : Γ ⊢ₐ a : T → Vc G Γ (root a) T`, **statable only at `s = []`**, where `BVar [] .var` is uninhabited so `root a` is necessarily a location. (b) is `hastp_to_htpy` (`dot_soundness.v:249`) and its `[]` is the O3 firewall.

Lemmas 1 and 2 are **one mutual induction on derivation size**, one clause per former, structure-preserving: `vcVar x ↦ the field`; `vcLoc ℓ ↦ vcLoc`; `vcUnfold T v ↦ vcUnfold (T[(θ↾p).lift]) IH`; `vcSub T₁ e v ↦ vcSub _ (Lemma 2 at θ↾p, by **Lemma R**) IH`; `selL v ↦ selL (Lemma 1 v)`, typed by **(★)**; `defL ℓ l e ↦ defL (θ.loc ℓ) l e` (already local-closed); `bindx`/`dfun` under `θ.lift`. No canonical forms, no narrowing, no pushback, no pack count occurs inside any of them, and `CanonicalForms` stays *below* `TypingSubst` — the four-module import cycle `CanonicalForms ← FormAlgebra ← Preservation ← TypingSubst` is avoided.

**Constructible instances (the audit, performed).** `Subst.one` is statable only where its root's prefix can receive the entry:

* `root a = conc ℓ`, `s₁ = ([],x)`, `s₂ = []` — then `θ↾.here = θ : Subst ([],x) []`, `Γ.upTo .here = Γ`, `Γ'.upTo (conc ℓ) = .nil`. **This is the runtime case**: `ST_Obj` and `ST_AppAbs` substitute `Vr.conc` and `Step` runs terms of local scope `[]`.
* `root a = .here` (`selfCast`) — `scopeUpTo .here = s`, `Γ.upTo .here = Γ`, so the field is `vcSub S₀ E (vcVar .here)`. Prefix indexing subsumes narrowing at the newest binder.

*Not* constructible, deliberately: `single a` at an older abstract root, where `T : Ty σ s` cannot be transported to `Ty σ (scopeUpTo (root a))`. The audit comes out clean **by construction**: MNF makes `app a l b` take atoms and instantiates the codomain by `U{root b}`, a *type-level* root renaming; no elaboration, checker or normalizer step performs a derivation-level `single` at an old variable. If a future extension needs one, it costs the two-case (minidot) lemma and the module reordering above.

**Corollary (preservation's instance).** With `Γ = .nil.cons TX`, `Γ' = .nil`, `θ = Subst.one a`, `root a = conc ℓ`: from `Vc G .nil (conc ℓ) (TX{conc ℓ})` every `Vc G Γ (abs .here) T` yields `Vc G .nil (conc ℓ) (T{conc ℓ})` at `Ty σ []`, and every `Γ ⊢ e : S ≤ T` yields a **closed** `.nil ⊢ e[θ] : S{ℓ} ≤ T{ℓ}` — the closed world `defL`, `hnf` and `atom_canon` already inhabit.

**Obligations, in full:** (★) and (coh) for the five constructors; the B.1 auxiliaries; Lemma 0; Lemma R; the open/subst commutation family `(T.substVr v)[θ] = (T[θ.lift]).substVr (v[θ])` (already the shape of `Oopsla16/Structural.lean`); one mutual induction for Lemmas 1–2; two small inductions for Lemma 4.

## C. GRAMMARS

Types are **Oopsla16's verbatim** (identity translation, `Oopsla16/Syntax.lean`): `Bot | Top | p.l | {l:S..U} | {l:Pi(S)U} | mu T | S∧T | S∨T`, `p ::= conc ℓ | abs x`. Contexts are `Oopsla16/Context.lean` verbatim (`cons : Ctx σ s → Ty σ (s,x)`). Store typing carries a **record** `Γ_G : (ℓ : BVar σ .var) → Ty σ ([],x)` naming each literal's typing type; `tyOf_G ℓ := (Γ_G ℓ).substVr (conc ℓ)` is then a function of data, not of a derivation, and its stability under `Grows` is `Γ_G`'s extension (this closes within-2's `tyOf_G` open item).

```
e,f ::= refl T | trans M e f | top T | bot T
      | dtyp l e f | dfun l e f
      | andI T₁ T₂ e f | andE1 T₂ e | andE2 T₁ e
      | orI1 T₂ e | orI2 T₁ e | orE S₁ S₂ e f
      | defL ℓ l e | defR ℓ l e            -- exact, reads the stored dty
      | selL p v | selR p v                -- p : Vr, EITHER zone
      | bindx S T e | muDrop T
v   ::= vcVar x | vcLoc ℓ | vcPack T v | vcUnfold T v | vcSub T₁ e v
a,b ::= var p | a |> e | pack T a | unpack T a          root : Atom → Vr
t   ::= atom a | new T ds | app a l b | let t u | cast t e
ds  ::= dnil | dcons (dty T) ds | dcons (dfun S U t) ds
```

## D. TYPING RULES

`T^` = weaken, `T{p}` = substVr, `T|p` = `rename (renameUpTo p)`.

**Inclusion** `Γ ⊢ e : S ≤ T` — (1) `refl`, (2) `trans`, (3) `top`, (4) `bot`: FCdot verbatim. (5) `dtyp l e f : {l:S₁..U₁} ≤ {l:S₂..U₂}` from `e:S₂≤S₁`, `f:U₁≤U₂` (= `stp_typ`). (6) `dfun l e f` likewise with `f` under `Γ, y:S₂^` (= `stp_fun`; replaces FCdot's `Form.pi`, same contravariance). (7–9) `andI/andE1/andE2`. (10–12) `orI1/orI2/orE` — **new**, from FCdotR-B. (13) `defL ℓ l e : (conc ℓ).l ≤ T₂|nil` given `(G.lookup ℓ).get? l = some (dty TX)` and `.nil ⊢ e : TX ≤ T₂` (= `stp_strong_sel1`); (14) `defR` dually. (15) `selL p v : p.l ≤ U|p` from `Vc G Γ p {l:Bot..U}`; (16) `selR` dually — **differs from within-2's ancestors**: `p` ranges over both zones, which is what makes Lemma 2 structure-preserving. (17) `bindx S T e : mu S ≤ mu T` from `Γ, z:S ⊢ e : S ≤ T` — the entry is the **opened body**, never `mu S`; this is the single correction to `FCdot/RecursiveEvidence.lean:106`. (18) `muDrop T : mu (T^) ≤ T` — target is a **weakening**; `mu T ≤ T{x}` is an unsoundness, not an optimisation. Derived: `bind1 S U e := trans _ (bindx S U^ e) (muDrop U)`; `selx p l := refl (p.l)`.

**Observation** `Γ ⊢ v :: p : T`, `T : Ty σ (scopeUpTo p)` — (19) `vcVar x :: abs x : Γ.lookupAt x` (= `htp_var`). (20) `vcLoc ℓ :: conc ℓ : tyOf_G ℓ` (= `TY_Vary`). (21) `vcUnfold T v :: p : T{selfOf p}` from `v :: p : mu T` (= `htp_unpack`). (22) `vcSub T₁ e v :: p : T₂` with `Γ.upTo p ⊢ e : T₁ ≤ T₂` (= `htp_sub`; at `conc ℓ` the context is `.nil`, i.e. `htpy`'s `stp [] G1`). (23) `vcPack T v :: conc ℓ : mu T` from `v :: conc ℓ : T{conc ℓ}` — **the index is a constructor index, so packing at an abstract variable is unwritable, not merely absent.** `vcPack` is not decoration: it is what makes `Subst.Ev`'s field constructible for an argument atom whose typing ends in `Atom.pack`, which is precisely the case on which FCdotR-Z's lemma dies.

**Atoms/terms/defs**: `absVar`, `concVar` (at `tyOf_G`), `cast`, `pack`, `unpack`; `atom`, `app` (`U{root b}`), `new`, `let`, `cast`; `dnil`, `dty`, `dfun`. As Design 2; `Binding`, transparency, `Ctx.lookupDef/lookupFields` all disappear (there are no transparent binders in FCdotR), which removes the `ty/transparent/def_/fields` fields of `Subst.Typed`.

## E. ELABORATION (32 source rules)

| source | target | note |
|---|---|---|
| `T_Vary` | `atom (var (conc ℓ))` at `tyOf_G ℓ` | needs `Γ_G` agreement lemma |
| `T_Varz` | `atom (var (abs x))` | |
| `T_VarPack` / `T_VarUnpack` | `pack T a` / `unpack T a` | |
| `T_Obj` | `new T ds` | |
| `T_App` | `app a l b`, `U` a weakening | **MNF lemma**: `tapp t₁ l t₂` → `let`-bound atoms + operational correspondence |
| `T_AppVar` | `app a l b : U{root b}` | MNF as above |
| `T_Sub` | `cast t e` / `a |> e` | |
| `D_Nil/D_Typ/D_Fun` | `dnil` / `dty` / `dfun` | |
| `stp_bot/top/typ/fun` | `bot/top/dtyp/dfun` | |
| `stp_and11/12/2`, `or1/21/22` | `andE1/andE2/andI`, `orE/orI1/orI2` | |
| `stp_trans` | `trans` | |
| `stp_selx` | `refl (p.l)` | derived |
| `stp_strong_sel1/2` | `defL/defR` | exact; no `obs_conc_admissible` needed for R1 |
| `stp_sel1/2` | `selL (abs x) ⟦h⟧` / `selR` | |
| `stp_bindx` | `bindx T₁ T₂ ⟦d⟧` | |
| `stp_bind1` | `trans _ (bindx T₁ T₂^ ⟦d⟧) (muDrop T₂)` | derived |
| `htp_var/unpack/sub` | `vcVar/vcUnfold/vcSub` | truncation is the index |

**Nothing fails.** Two auxiliary lemmas: MNF normalisation of general `tapp` with operational correspondence (the branch has this pattern in `DotMNF/WadlerFest`), and `Γ_G`-agreement for `T_Vary`. Recommendation carried from Design 2: elaborate the **union-free fragment first** and state R1 for it; `stp_or*` are unexercised even in `dot_exs.v`.

## F. O1, O2, PACKING — BLOCKED BY TYPING

**O1** (`FCdot/ReceiverCounterexample.lean`). Steps 1–5 still go through: under a hypothesis at `D(p)` one derives `D(p) ≤ E`. But in FCdotR the only former that creates a hypothesis and exports a first-class inclusion is `bindx`, whose conclusion is `mu (D(p)^) ≤ mu (E^)`. **The step that fails to typecheck is step 8**: it needs `p.D ≤ mu (D(p)^)`, an inclusion with `mu` on the right and a non-`mu` left. No former has that shape — the source has no `stp_bind2`, and FCdotR adds nothing. `pack` at the atom level gives `mu ((q's type)^)`, and closing the gap needs `bindx` with premise `dtyp A refl (p.D ≤ E)`, i.e. the sought inclusion. Circular, hence dead.

**O2** has no statement: the type translation is the identity, so `Ty.telSelf` and the `isDecl` clause of `DotToFCdot/Types.lean:102` have no counterpart, and `mu (D(p)^) ≠ D(p)` is `Ty.mu_ne_obj`/`mu_weaken_ne_self` (`FCdot/RecursiveTypes.lean:177-205`), already proved.

**Packing counterexample** (`Oopsla16/PackingCounterexample.lean`). Its single new step is `zPacked : HtpP G Γ z D` — `htp_pack` at the **abstract** self of `stp_bindx`. `vcPack`'s index is literally `conc ℓ`, so that instance is *unwritable*. Rebuilding it concretely re-converges on needing a closed `D ≤ D'` (`D = μ_.p.B`, `D' = μ_.p.C`), hence `bindx` with an abstract self, hence `p.B ≤ p.C` under `z`, hence `Vc (abs z) : p.C`: from `vcVar z : p.B`, `defL p B` gives `{A:D..D'}` and `selL/selR` give facts about `z.A`, never about `z`. Reaching `p.C` needs `vcPack` at `abs` (unwritable) or a `mu` on the right from a non-`mu` left (no former). Two further guards, both **negative regression tests on day one**: `atomToVc` is statable only at `s = []` (any generalisation to `s ≠ []` is O3 restored); `muDrop`'s target must stay a weakening.

## G. METATHEORY PLAN

**Reused verbatim:** `Debruijn`, the `Oopsla16` scoping layer, `Resolution`'s pigeonhole (now context-free), `Consistency`'s endpoint arguments, `Erasure`'s shape. **New structural cases:** `Form.combine` gains `rec` (chain append, `O(1)`), `meet` (conjunct-index substitution, the analogue of `Entries.through`), and `inj`/`cases`; `FormTyped` loses the `ρ` mode and gains `rec`/`meet`/`inj`/`cases` plus one clause for concrete `selL`. **Genuinely new, in dependency order:** Lemma Z → the prefix apparatus at `Vr` + (★) → Lemma 0 → Lemma R → Lemmas 1–4 → `Store.Typed` with `Γ_G` → `combine_typed` → `le_canon`/`vc_canon`/`atom_canon` (one mutual induction, `Vc` as a third sort) → consistency (endpoints only, no chain interpreted) → preservation/progress → checker + completeness.

## H. MILESTONES

1. **`FCdotR/Prefix.lean`** — `scopeUpTo`/`renameUpTo`/`Ctx.upTo`/`selfOf` at `Vr`; the B.1 auxiliaries; Lemma Z. *Accept:* `scopeUpTo_varUpTo`, `lookupAt_upTo`, `upTo_upTo` compile; `example : scopeUpTo (Vr.conc ℓ) = [] := rfl`. One sitting, no open question.
2. **`FCdotR/Syntax.lean` + `Typing.lean`** — grammars C, rules D, union-free. *Accept:* `Oopsla16.Examples.FunctionField.recursive` elaborates to closed `bindx S T (andE2 _ (andE2 _ (dfun f (top _) (selL _ (vcSub _ sBound (vcVar z))))))` and typechecks — the judgment `RecursiveSubtypingSeparation.no_coercion` proves current FCdot cannot express.
3. **`FCdotR/Structural.lean`** — `Subst.Mono`, (★), (coh), closure under the five constructors. *Accept:* `Subst.Mono.lift`, `.comp`, `.selfCast` compile.
4. **`FCdotR/Locality.lean`** — Lemma 0. *Accept:* both directions, both zones.
5. **`FCdotR/TypingSubst.lean`** — `Subst.Ev`/`Subst.Typed`, Lemma R, Lemmas 1–4. *Accept:* the B.5 corollary; `Subst.Typed.selfCast`; a `#print axioms`-clean negative test that `Subst.one` at an old abstract root does not elaborate.
6. **`FCdotR/Normalizer.lean` + `FormAlgebra.lean`** — `hnf` (fuel), `rec`/`meet`, `combine`, `combine_typed`. *Accept:* `combine` totality/determinism; the `dfun` composition case via `Subst.Typed.selfCast`.
7. **`FCdotR/CanonicalForms.lean`** — `le_canon`/`vc_canon`/`atom_canon`. *Accept:* `no_top_le_bot` over a store with bad bounds.
8. **`FCdotR/Preservation.lean` + `Progress.lean`**, then **`Elaboration.lean`** (R1), then **unions**, then **`Checker`**.

## I. OPEN, HONESTLY

* **The one measure that does not go away.** `vc_canon` must invert a closed `Vc` at `conc ℓ` through `vcPack`/`vcUnfold`/`vcSub` alternation, and at a `vcUnfold` whose subject was widened by a `bindx`-derived inclusion it must instantiate the chain at `ℓ` — evidence that is *not* a subderivation. Substitution is structure-preserving, so the growth is `+|H_ℓ|` per `vcVar` leaf with `H_ℓ` fixed per location, but nested `rec`s compose and I have no proof the lexicographic pair terminates. This is the reference's `canon_typ`/pack count `m`. **Cost if it cannot be closed:** re-import the count as a nat parameter of `vc_canon` *alone* (~1 lemma), not as an index on a judgment — still inside R4, since it adds no typing relation and no narrowing or pushback. Prototype on a two-location mutually recursive store before writing Lean.
* **Concrete `selL`/`selR` are more permissive than `stp_strong_sel1/2`,** which read the stored `dty` exactly. R1 does not depend on this (`defL`/`defR` stay primitive), but soundness owes `obs_conc_admissible`: any closed `v :: conc ℓ : {l:Bot..U}` forces `TX ≤ U` for the stored `TX`. Expected to follow from `Store.resolve` + `le_canon` (the reference's `canon_typ` + `stp_strong_sel1/2`); if false, retreat to abstract-only `selL` and pay the two-case substitution lemma.
* **Dependent-index ergonomics.** `Vc : (p : Vr σ s) → Ty σ (scopeUpTo p) → Type` has a motive over a computed `Sig` inside a mutual block with `LeCo` and `Atom`. Prototype that block in milestone 2; fallback is two constructors discriminated on the zone.
* **Store typing.** `Store σ σ'` is deliberately double-indexed, so stored objects may reference each other; `tyOf_G` and `vcLoc` read a possibly cyclic store. Decide explicitly: prefix-orderable stores (an R1 concession relative to `dot_soundness.v:1131`) or the reference's unconstrained store.
* **Inherited and untouched:** union `combine` doubling and disjunctive `AtomConcl` (claimed unreachable from `Progress` — a lemma about resolution, not an inspection); `meets`/`joins` flattening termination; `decide +kernel` slowdown from retained `mu` layers; FCdotR is a **second target**, and the WadlerFest→FCdot chain is not reused.