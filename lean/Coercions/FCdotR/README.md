# FCdotR

An explicit-evidence coercion calculus for
[`../Oopsla16`](../Oopsla16/README.md). Subtyping, and the variable typings
that type selections go through, become evidence terms; applications take
atoms. Types, contexts and stores are
`Oopsla16`'s own.

## Main results

* `Oopsla16.oopsla16_safety`, `oopsla16_not_stuck` (`SourceSafety`): a closed
  `Oopsla16` program typed over the empty store never gets stuck on
  `Oopsla16`'s own machine. The proof elaborates the program into FCdotR, uses
  FCdotR's safety, and relates the two machines.
* `safety'`, `preservation'`, `progress'` (`MethodInversion`): FCdotR type
  safety. Preservation holds up to evidence.
* `consistency_honest` (`Inversion`): no closed `⊤ ≤ ⊥` over an honest store.
* `elabSpec`, `elabSpecGen` (`ElaborationFull`): every `Oopsla16` typing
  elaborates to a typed FCdotR term, over a store whose methods are annotated.
* `checkTm_iff` and its siblings (`Checker`, `CheckerCompleteness`): an
  executable checker decides every FCdotR judgment. `CheckerExamples` runs it
  in the kernel, including on the reference's `ex1`, `ex2` and `paper_lst`.
* `Store.Honest.varConcAny_admissible`, `Store.Honest.vcLocAny_admissible`
  (`Admissibility`): over an honest store the location rules derive nothing
  the source cannot.

## Where FCdotR is not a rule-for-rule image of `Oopsla16`

* **A different calculus by design.** Explicit evidence, casts as syntax,
  `let`, application on atoms only, methods always annotated, and a
  store-and-continuation machine. Source-to-target typing is proved (the
  elaboration); the converse is not.
* **The location rules are not `T_Vary`.** They observe a location at any type
  that matches its stored object member by member and do not re-type method
  bodies. Over an honest store they derive nothing the source cannot. Over a
  dishonest store they trust the stored annotations: over
  `{def 0(y:⊤):⊥ = y}` they type `l.0(l)` at `⊥` (`Coverage.UncheckedBody`).
  Machine stores are always honest, so safety is unaffected.
* **Elaborating `T_Vary` needs annotated stored methods**, so `ElabSpecGen`
  assumes `Store.Annotated G`. The headline safety theorems do not change.
* **Other target-only power.** `selL`/`selR` on locations and `vcLoc`, which
  reads the store typing (a lying store typing proves `⊤ ≤ ⊥`).

## Checks

No `sorry`; the only axioms are `propext` and `Quot.sound`
(`audit/AxiomAudit.lean`). `audit/Oopsla16Fingerprint.lean` fingerprints every
`Oopsla16` definition, so a change to the source calculus is visible.
