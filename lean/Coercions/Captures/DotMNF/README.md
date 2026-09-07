# DotMNF, at stage A1 of captures

WadlerFest DOT in monadic normal form, the source of the translation in `../DotToFCdot`.

| module | contents |
|---|---|
| `Syntax` | paths, types (`⊤ ⊥ {A:S..T} {a:T} p.A μ ∀ ∧`), terms, values, definitions; `Decl` and its decision procedure `isDecl`, `Wf`, `Distinct` |
| `Typing` | contexts (`cons`, `consSelf`); `Sub`, `HasTy`, `DefsTy` (Type-valued); intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise); `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`); `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Erasure` | erasure to `Runtime`; `erase_step`, `erase_reflect`, `final_erase`, `final_reflect` |
| `Examples` | E1 to E8 as `HasTy` derivations; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation |

Unchanged in stages A0 and A1.  The capturing source calculus is stage A3.
