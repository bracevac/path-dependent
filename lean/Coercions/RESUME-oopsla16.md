# Resume state

Branch `fcdot-recursive-subtyping`, commits `f24cc45`, `66acc08`, `8bc4322`.
Build: `lake -d <tmp> build FCdot DotMNF DotToFCdot Oopsla16` — 89 jobs, green.
Temp lake project: `<scratchpad>/build` (lakefile with absolute `srcDir`).
Builds need `dangerouslyDisableSandbox`: `~/.elan` is outside the sandbox.

## Done

`Oopsla16/` — the Rompf–Amin OOPSLA'16 source, intrinsically scoped. 265 code
lines of spec against `dot.v:17-399`'s 309. `Htp` is indexed at
`Ty σ (scopeUpTo x)` so the artifact's `length GL = S x ∧ GH = GU ++ GL`
truncation is the judgment's type. `Stp.refl` is 8 lines against 55.
`PackingCounterexample` adds the mirror of `T_VarPack` to `Htp`, keeps every
other restriction, and produces a well-typed stuck program.

## Settled

**The packing result stands.** Six independent attacks failed
(`<scratchpad>/VERIFY-verdict.md`, run `wf_7ac7e30a-406`). It is mechanized in
Coq at `coq/oopsla16-packing/`: `dot_spec.v` byte-identical to `dot.v:14-399`,
the extended judgment block one character from `dot.v:219-393`, `htp_sub`
unweakened, `htp_pack` used once, `Print Assumptions` closed. No `closed`
premise obstructs it, so the intrinsic port hid nothing.

Corrections applied: `dSubPlain` isolates what the rule adds (one step); the
extension is a subsystem, not a conservative extension; the second restriction
is kept and satisfied, not stressed; the culprit is the interaction with
`stp_bindx`, not packing alone (WadlerFest and pDOT allow packing in `Sel` and
are sound); 39 of 90 `dot.v` citations were wrong and are now all verified.

Still optional, not needed for the claim: reachability of the store from a
closed source program, and a Lean embedding of the subsystem into the full
extended calculus (Coq's `extend_all` already does the latter).

## In flight

2. **FCdotR target design** — workflow `wf_85586d5e-49d`. Recovered to
   `<scratchpad>/DESIGN-scout.md`, `DESIGN-1-*.md`, `DESIGN-2-*.md`,
   `DESIGN-judge-{1,2,3}.md`. Two of four designs blew the 64k output cap and
   the final synthesis hit the session limit; no plan was produced.

   Design 1 — delete the receiver binder from object telescopes so `mu` is the
   only self binder; `mu` rigid with congruence-only `BIND`/`BIND1`, no
   `S ≤ mu S`; fold/unfold on subjects only; a fold-free `Path` sort for
   observations inside inclusions. Scores 6/6/6. Its consistency story survived
   every attack, but it drops both of the source's soundness carriers and the
   three union rules of `Stp` do not elaborate.

   Design 2 — keep Oopsla16's type language verbatim; three evidence sorts
   `LeCo`/`Vc`/`Atom`; `bindx` over the opened body; `Vc` indexed at
   `scopeUpTo x`. Scores 9 (soundness), 9 (translatability, all 32 rules
   elaborate), 5 (proof cost).

   **The shared blocker, found independently by all three judges: substitution.**
   `FCdot/TypingSubst.lean:35` is
   `Subst.Typed.var : ∀ x, Γ' ⊢ₐ σ.var x : (Γ.lookupTy x).rename σ.root` — every
   substituted variable is supplied by an ATOM. Both designs add a second
   subject sort for observations inside inclusions and neither says what
   substitution does to it. Design 1 declares the lemma unnecessary; it is not.
   Design 2 makes it harder, because `Vc Γ x T` is indexed at `scopeUpTo x` and
   preservation must replace an abstract variable by a store location.
   Design 2's own stated crux is separate: `interp`/`apply` over the view
   environment has no termination measure.

   Next design round must answer: what does substitution do to prefix-scoped
   observation evidence? Everything else is downstream of that.

## Built so far

| module | state |
|---|---|
| `Oopsla16/{Syntax,Structural,SubstLemmas,Context,Semantics,Typing,Lemmas,Examples}` | done |
| `Oopsla16/PackingCounterexample` + `coq/oopsla16-packing/` | done, verified, mechanized |
| `FCdotR/Prefix` | milestone 1 done |
| `FCdotR/{Syntax,Typing,Examples}` | milestone 2 done — `recursive_typed` is closed evidence for the coercion the old target cannot express |
| `FCdotR/Structural` | milestone 3 partial: `Mono`, `star_ty`, `Mono.id` |

Build: 97 jobs green. `PLAN.md` in `FCdotR/` has the design and milestones 4-8.

## The current obstruction

`Mono.lift`. Pushing a prefix-respecting substitution under a binder must
supply, at `.there y`, a substitution at `scopeAt ((θ.abs y).weaken)`.
`scopeAt_weaken` says that is `scopeAt (θ.abs y)`, so `m.res y` is the witness
— but only after a transport, and `star` for the lifted substitution then has
to be proved underneath it.

Per constructor the equation is definitional (`(.abs x).weaken` is
`.abs (.there x)` and `tailBelow (.there x)` reduces to `tailBelow x`;
`(.conc l).weaken` is `.conc l`). It is opaque only because `θ.abs y` is a
neutral term. So the fix is to case on `θ.abs y` where the restriction is
*built*, not transport after the fact: index `res` by a `Vr` rather than a
`BVar`, and split `Mono` so the two zones are separate fields. That also
matches Lemma 1, whose subject is a `Vr` and at `conc l` has `[]` on both
sides.

## Next

- Finish (1), then state the counterexample's scope in `Oopsla16/README.md`.
- Finish (2), then write `FCdotR/Syntax.lean` as milestone 1.
- Open: no correspondence between `Oopsla16` and `DotMNF`; no soundness proof
  ported; `dot_exs.v`'s `ex1`/`ex2`/`paper_lst` not ported.
