# Bridge: selective F-sub into the DOT calculus

The library `SelectiveBridge` (modules `Coercions.Selective.Bridge.*`, namespace `Bridge`) maps plain
full F-sub with selective subtyping ([`../Fsub`](../Fsub/README.md), namespace `SelFsub`) into the
calculus `H` over WadlerFest DOT-MNF ([the parent directory](../README.md), namespace `Selective`) at
the level of evidence. A type variable `X` becomes `x_X.A`, a binding `X <: U` becomes
`x_X : {A : ⊥ .. ⟦U⟧}`, `∀(X <: U). T` becomes `∀(x : {A : ⊥ .. ⟦U⟧}) ⟦T⟧`,
`S → T` becomes `∀(_ : ⟦S⟧) ⟦T⟧↑` and `Top` becomes `⊤`, with the one type label
`Selective.lA = .typ 0`. Certificates are mapped homomorphically.

## Replay

From the repository root:

```sh
lake build SelectiveBridge
lake env lean lean/Coercions/Selective/Bridge/Axioms.lean     # 48 lines
```

The audit has 48 lines: 20 read
`[propext, Quot.sound]`, 27 read `[propext]`, one ("`Bridge.sig`") depends on no
axioms. The sources contain no `sorry`, no `native_decide`, no `partial` or
`unsafe` definition, no `axiom` declaration, no `set_option` and no Mathlib
import. Every negative fact is decided by `decide` or proved by inversion.

## Modules

| file | lines | content |
| --- | --- | --- |
| `Encode.lean` | 142 | `sig`, `bv`, `toFin`, `renF`; `enc`, `encCtx`, `encCert`; `enc_rename`, `enc_weaken`, `encCtx_lookup` |
| `Preserve.lean` | 113 | `prim_preserved`, `cert_preserved`, `encCert_stepOnly`, the corollaries, the transported witness |
| `Reflect.lean` | 153 | the counterexample to reflection, injectivity, `separator_outside_image` |
| `Axioms.lean` | 52 | `#print axioms` for every definition and theorem |
| `../Bridge.lean` | 3 | the import root: the three modules, without `Axioms` |

## Theorems

All names are in namespace `Bridge`.

- `enc_rename`: `enc (A.rename ρ) = (enc A).rename (renF ρ)`; `enc_weaken` is the instance `ρ = Fin.succ`.
- `encCtx_lookup`: `(encCtx Γ).lookup (bv x) = {A : ⊥ .. enc (Γ.lookup x)}`.
- `prim_preserved`: `SelFsub.Prim Γ S T → Selective.Prim (encCtx Γ) (enc S) (enc T)`; one primitive step goes to one primitive step (bound to `P-SelU`, arrow and universal to `P-All`, the universal's bound through `P-Typ`).
- `cert_preserved`: `SelFsub.CTy Γ c S T → Selective.CTy (encCtx Γ) (encCert c) (enc S) (enc T)`.
- `encCert_stepOnly`: `(encCert c).StepOnly`, the predicate `Selective.Cert.StepOnly` of `../Negative.lean` (no `pos`, hence no atom).
- `synthC_preserved`: `SelFsub.synthC Γ c = some (S, T) → Selective.synthC (encCtx Γ) (encCert c) = some (enc S, enc T)`.
- `coercion_preserved`: an F-sub certificate gives a step/seq-only `H` certificate between the encodings.
- `sub_preserved`: `SelFsub.Sub Γ S T → Nonempty (DotMNF.Sub (encCtx Γ) (enc S) (enc T))`, through `SelFsub.coercion_iff` and `Selective.coercion_sound`.
- `encCtx_YX`, `enc_YX_types`: `Y <: Top → Top, X <: Y` encodes to `y : {A : ⊥ .. ∀(_ : ⊤) ⊤}, x : {A : ⊥ .. y.A}`, with `⟦X⟧ = x.A`, `⟦Y⟧ = y.A`, `⟦Top → Top⟧ = ∀(_ : ⊤) ⊤`.
- `YX_XY`, `YX_Y`: `x.A ≤₀ y.A` and `y.A ≤₀ ∀(_ : ⊤) ⊤` in `H`.
- `YX_checker`, `YX_not`: `Selective.prim?` returns `false` on the composite, so `¬ x.A ≤₀ ∀(_ : ⊤) ⊤`.
- `certYX_fsub`, `certYX_H`, `certYX_H'`: the certificate `step[X, Y] ; step[Y, Top → Top]` checks in F-sub, its encoding checks in `H` by `decide`, and again by `synthC_preserved`.
- `counter_H`, `counter_H_checker`: `⟦Top → Top⟧ ≤₀ ⟦∀(X <: Top). Top⟧` in the empty context (`P-All` with `P-Top` on the domain).
- `counter_fsub`, `counter_fsub_checker`: `¬ SelFsub.Prim .nil (Top → Top) (∀(X <: Top). Top)`.
- `prim_not_reflects`: `≤₀` on encodings does not imply F-sub's `≤₀`.
- `sub_not_reflects`: the encodings are DOT-MNF subtypes, and `¬ Nonempty (SelFsub.Sub .nil (Top → Top) (∀(X <: Top). Top))` (through `ArrOrTop.cert`: certificates out of an arrow or `Top` end at an arrow or `Top`).
- `enc_injective`, `encCtx_injective`, `encCert_injective`: the encoding is injective on types, contexts and certificates (`enc_ne_typ`: an encoded type is never a declaration `{A : L .. U}`; `weaken_injective` comes from `DotMNF.Ty.unweaken?_spec`).
- `separator_outside_image`: `encCtx Γ ≠ Selective.ΓR` for every `Γ : SelFsub.Ctx 2`.

## Reflection

Reflection fails. Arrows and universals both become dependent functions, and a
universal's domain `{A : ⊥ .. ⟦U⟧}` is below the arrow domain `⊤` by `P-Top`, so
`⟦Top → S⟧ ≤₀ ⟦∀(X <: U). S↑⟧` holds in one step although F-sub relates no arrow to
a universal, neither primitively nor declaratively (`prim_not_reflects`,
`sub_not_reflects`). A conservative encoding would have to make the two function
forms incomparable, for instance by tagging codomains with distinct field labels
(`∀(_ : ⟦S⟧) {r₁ : ⟦T⟧↑}` against `∀(x : {A : ⊥ .. ⟦U⟧}) {r₂ : ⟦T⟧}`); it is not
built here, and reflection for it is not proved. The encoding is injective.

## The first obstruction, side by side

The image of the encoding contains only contexts whose entries are declarations
`{A : ⊥ .. U}` (`encCtx_lookup`). The DOT-MNF separator lies outside it
(`separator_outside_image`): in `w : {B : ⊥ .. R}, y : w.B` with
`R = {A : ⊥ .. {a : ⊤}}`, DOT-MNF derives `y.A <: {a : ⊤}` by retyping the
receiver `y` at `R`, and no step/seq certificate relates these endpoints with the
declared-exposure primitive relation (`Selective.Hybrid.ex2_no_step_only`, stated in the context
extended by `u : y.A`). `H` repairs it with
the positioned step whose receiver atom is `y ▷ step[w.B, R]`
(`Selective.openC`, checked by `Selective.open_H` in
`../Matrix.lean`).

## What the bridge shows and what it does not

It shows forward preservation for types and contexts: every F-sub primitive step
is one primitive step of `H`, and every F-sub certificate maps to a step/seq-only
`H` certificate between the encoded endpoints, so the F-sub evidence discipline is
literally a fragment of `H`'s. It gives no term-level embedding (DOT-MNF is in
monadic normal form), makes no claim about safety, does not claim that every
two-constructor evidence language fails for DOT (a stronger primitive relation
could absorb receiver retyping), and does not claim that `H`'s constructor
inventory is minimal.
