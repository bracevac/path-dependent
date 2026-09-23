# FCdotR — status

State of the `Coercions.FCdotR` library as integrated on branch
`fcdot-recursive-subtyping`.  FCdotR is the explicit-evidence **target** for
the `Coercions.Oopsla16` source (Rompf–Amin OOPSLA'16 DOT, which has
recursive subtyping).  It is a *second* target: the WadlerFest→FCdot chain in
`DotMNF`/`DotToFCdot`/`FCdot` is not reused, only imitated.

`lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR` completes in **118 jobs**.
Its only warning is the pre-existing unused `termination_by` at
`FCdot/Syntax.lean:221`, outside this library.  There is no `sorry`, `admit`,
`axiom`, `native_decide` or `partial` anywhere in `FCdotR/` or `Oopsla16/`
outside comments.  An environment-wide audit of every constant defined in
`Coercions.FCdotR.*` and `Coercions.Oopsla16.*` reports `checked 6258
constants; offending: 0`: nothing uses an axiom beyond `propext` and
`Quot.sound`.

**Type safety of `Oopsla16`'s own substitution machine is proved with no
hypothesis**, for every closed term typed over the empty store: arbitrary
operands at every application, Curry-style methods allowed.  The typing work
is all the target's.  The source is elaborated into FCdotR, the two machines
are related by an operational correspondence, and `MethodInversion.safety'`
refutes a stuck state.  This is the shape of the WadlerFest line
(`DotToFCdot/Safety.lean`, `DotMNF.dot_safety`).

## The headline

In `SourceSafety.lean`, namespace `Oopsla16`:

```lean
theorem oopsla16_safety {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') : ¬ FCdotR.SrcStuck G' t'

theorem oopsla16_not_stuck {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') :
    t'.IsAnswer ∨ ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Tm σ' []),
      Step g' G' t' G'' t''
```

`FCdotR.SrcStuck G t` is `¬ t.IsAnswer ∧ ¬ ∃ σ' g G' t', Oopsla16.Step g G t G' t'`.
Both statements mention only `Oopsla16`'s `HasType`, `Steps`, `Step` and
`IsAnswer`; no FCdotR notion appears in them, so their meaning does not
depend on the correspondence or on the target.  The positive form is proved
constructively from the `Simulated` invariant, not derived from the negative
one (that would need classical logic).  Naming follows the brief: here
`…_safety` is the negative form and `…_not_stuck` the positive one, the reverse
of `DotMNF.dot_safety`/`dot_not_stuck`.

**Checked not vacuous at integration** (scratch file, not in the library).
Typed closed programs exist: `Oopsla16.Examples.ex0` and
`SourceSafety.RecursiveArg.progTy` (the latter outside `TmFrag`, and needing
`stp_bindx`).  `SrcStuck` is inhabited: `PackingCounterexample.badTerm_not_answer`
and `badTerm_stuck` give `SrcStuck PackingCounterexample.G badTerm`.  The
ill-typed `tapp (tobj dnil) 0 (tobj dnil)` reaches a stuck configuration from
the empty store in two source steps, so `oopsla16_safety` refutes every
typing of it; and `oopsla16_safety_honest` over `TwoObjectStore.honest`
refutes every `Oopsla16` typing of `badTerm`, which only the `htp_pack`
extension types.

The honest-store versions `Oopsla16.oopsla16_safety_honest` and
`oopsla16_not_stuck_honest` start from a term typed over an honest source
store (`Store.Honest G W`).  The term is arbitrary; the literal each location
was typed from must lie in `DmsFrag` (see *Restrictions*).

`ElaborationFull.oopsla16_safety'`/`oopsla16Safety_holds` and
`ElaborationFull.oopsla16_progress` are the same two statements, proved in that
module; `SourceSafety` restates them in the source's namespace.

## Hypotheses

Every hypothesis structure still in the code is **inhabited**.  Each is kept as
an explicit argument only in the modules that sit below its proof in the import
order; the doc comment of every theorem that takes one names where it is
discharged.

| Hypothesis | Taken by | What it says | Discharged by |
| --- | --- | --- | --- |
| `Contract G W` | `Normalizer`: `VcTy.unfoldStep`, `VcTy.canon` | an unfolding-over-packing redex can be contracted without growing the spine pack count | `Inversion.Store.Honest.contract` (any honest store); `Store.Honest.canon` is `canon` without it |
| `BoundsVacuous G W` | `CanonicalForms`: `consistency`, `no_loc_le_bot` | the bounds a closed observation of a location reports are sound for `Vacuous` | `Inversion.Store.Honest.boundsVacuous`; `consistency_honest`, `Store.Honest.no_loc_le_bot` are the theorems without it |
| `AppInversion` | `Preservation`: `StateTy.app`, `preservation`, `preservation_steps`, `preservation_init`; `Progress`: `progress_app`, `progress`, `not_stuck`, `safety`, `safety_of_source` | canonical forms for methods: a closed atom at `{l : S0 → U0}` over an honest machine store is rooted at a location storing a method at `l` | `MethodInversion.appInversion`; the primed theorems in `MethodInversion` are the unprimed ones without it |
| `ObsFunInversion` | `Preservation`: `AppInversion.ofObs` | the evidence-level content of `AppInversion`: a closed observation at a method type inverts to a method conjunct of a location node's type | `MethodInversion.obsFunInversion`, from `Inversion.RecordedLit.obsFun` |
| `ElabSpec` | `Correspondence`: `transport`, `oopsla16_safety`; `Simulation`: `Simulated.of_elab`, `elab_adequacy` | every closed source typing elaborates to a typed FCdotR term whose initial state is related (`Rel`) to the source term | `ElaborationFull.elabSpec` (via `elabSpecGen`); `SourceSafety`'s `Simulated.init`, `elab_adequacy'`, `Oopsla16.oopsla16_safety` are the theorems without it |
| `SimSpec` (`SimStepSpec ∧ SimStuckSpec`) | `Correspondence`: `transport`, `transport_from`; `SimStepSpec` alone: `Rel.steps` | a source step from a related pair is matched by a target run; a stuck source makes a related target run into a stuck state | `Correspondence.sim_spec` (`sim_step`, `sim_stuck`), in the same module; `Simulation.Rel.steps'` is `Rel.steps` without it |

`ObsConcAdmissible` (`CanonicalForms`) is a named statement rather than a
hypothesis — nothing takes it as an argument — and `Inversion.obs_conc_admissible`
proves it over every honest store.  `VaryEv` and `LemmaR`, hypotheses of
earlier rounds, are gone: `VaryEv` was false and was removed when the target
acquired `T_Vary` verbatim (`VcTy.vcLocAny`, `AtomTy.varConcAny`); `LemmaR` is
inhabited by `SubstTyping.lemmaR`.

## Restrictions that are not hypotheses

* `Store.Honest` (source store) and `MachineStore.Honest` (machine store) are
  real store invariants; `CanonicalForms.DishonestStore` shows that `LeTy`
  alone is inconsistent, so they cannot be dropped.
* Preservation types a state **up to evidence** (`Preservation.StateTy`: some
  typed term and continuation with the state's skeleton).  On-the-nose typing
  is false for this machine (`Preservation.OnTheNose`).  The correspondence is
  a property of skeletons (`Corr.skel_iff`), so this costs the transport
  nothing (`StateTy.corr_witness`).
* **Honest initial stores need fragment witnesses.**  `oopsla16_safety_honest`
  and `oopsla16_not_stuck_honest` ask that every stored witness
  `(h.at' l).defs` be in `DmsFrag`.  `MachineStore.Honest` types stored target
  literals over the machine store's *erasure*; a fragment witness elaborates
  with no `let`, so that erasure is the source store (`toMachine_erase`), but a
  general witness gets `let`s in its method bodies, which erase to object
  encodings.  Lifting this needs target typing carried back to source typing
  (below).  Runs from the empty store are unaffected.
* The older fragment results are kept and remain restricted:
  `safety_of_source'` (term and witnesses in `TmFrag`/`DmsFrag`),
  `Correspondence.oopsla16_safety_frag`, `Elaboration.elabHasType` with its
  on-the-nose erasure, and `Erasure.Step.simulate` (continuation with no `let`
  frame, `Cont.Evidential`).  `Simulation.Rel.reflect_step` is the simulation
  without that restriction, and `Rel.of_letFree` shows `Erasure`'s fragment is
  a special case of it.

## Modules

| Module | What it establishes |
| --- | --- |
| `PLAN.md` | The design: substitution via prefix restriction, the elaboration of 32 source rules, the metatheory order, and the open questions.  Not code. |
| `Prefix.lean` | The prefix apparatus at a two-zone variable: `scopeAt`, `renameAt`, `selfAt`, `ctxAt`, `Zone`, the `upTo`/`renameUpTo` transport laws, and `renameUpTo_comp` (weakenings out of iterated prefixes compose) with its transport helpers. |
| `Syntax.lean` | The five grammars — inclusion evidence `Le`, observation evidence `Vc` (indexed at its subject's prefix scope), `Atom`, `Tm`, `Defs` — plus `Atom.root` and `Defs.length`.  A location has two `Vc` nodes: `vcLoc ℓ`, and `vcLocAny ℓ T ds`, which carries a `T_Vary` witness's self type and literal as syntax. |
| `Typing.lean` | `StoreTy`/`tyOf` and the two evidence judgments `LeTy` (inclusion) and `VcTy` (observation).  `VcTy` has two location rules: `vcLoc` at the recorded type `tyOf W ℓ`, and `vcLocAny`, the source's `T_Vary` verbatim.  No term typing here. |
| `Structural.lean` | `MonoAt`/`Mono`: a substitution carrying a per-variable image and restriction satisfying the star law.  `Mono` is not closed under restriction; `Subst.lean`'s `MonoSyn` is the answer, and `MonoSyn.toMono` embeds it. |
| `Locality.lean` | Lemma 0, the locality of observation evidence: `VcTy.strengthen` and `VcTy.ofLoc`. |
| `Examples.lean` | The `FunctionField` example elaborated by hand: a closed `bindx` derivation whose method body uses a `selL` under the enclosing self — the judgment `DotToFCdot/RecursiveSubtypingSeparation` shows current FCdot cannot express. |
| `Subst.lean` | `MonoSyn`, the inductive syntax of generated substitutions, closed under restriction (`resSyn`).  The substitution action on all five sorts, the star laws, `toMono`, `restrict_unique`, and the image/restriction laws for iterated prefixes. |
| `SubstTyping.lean` | `MonoSyn.Ev` with `refl`/`lift`/`atNil`; `VcTy.toFull`/`weakenVar`/`strengthenCons`; `MonoSyn.restrict_coh`; `VcTy.descendAbs`/`descend`; `lemmaRVc`/`lemmaR`; and the **unconditional** substitution theorem `LeTy.substEv`/`VcTy.substEv`, one premise, `MonoSyn.Ev`. |
| `TermSubst.lean` | `MonoSyn.Ev.weaken`; `MonoSyn.EvA` (`Ev` plus an atom at each abstract variable) with `refl`/`weaken`/`lift`; `AtomTy.weakenVar`; and the substitution theorem for the three term judgments, `AtomTy.substEv`/`TmTy.substEv`/`DefsTy.substEv`. |
| `StoreTyping.lean` | `Conjunct` and `DmsHasType.conjunct`; `Store.Honest` (every location holds a literal typed at its store type) with `vary`, `member`, `obs`, `alloc`; `varyMember`/`varyObs` for a bare `T_Vary` witness; `Store.Honest.vcLoc_of_vcLocAny`; store renaming for the four source judgments and a substitution's store part as a store renaming.  `TwoObjectStore`. |
| `TermTyping.lean` | The three term judgments `AtomTy` (6 rules), `TmTy` (5), `DefsTy` (3), with two location rules `varConc`/`varConcAny`.  `TmTy.appWeaken`, `AtomTy.toVc`, `Store.Honest.varConc_of_varConcAny`; `FunctionFieldObject`. |
| `Machine.lean` | The runtime: `Inst` and its action on all five sorts, `MachineStore`, `Frame`/`Cont`/`State`, `Step`/`Steps` indexed by `Oopsla16.Grows`, six rules, `State.Final`/`State.Stuck`.  `MonoSyn.ofInst` makes `Inst` a `MonoSyn` at the typing level. |
| `Erasure.lean` | `Tm.erase`/`Defs.erase`/`MachineStore.erase` into `Oopsla16` and its commutation laws; the **evidence skeleton** `Tm.skel`/`Defs.skel`/`Cont.skel` (roots, annotations and term structure kept, casts and atom wrappers forgotten) with `Tm.skel_inst`, `Tm.erase_skel`; `Step.simulate`/`Steps.simulate` under `Cont.Evidential`.  `Counterexample.badRun`. |
| `Forms.lean` | Measures (`Le.size`, `packs`, `Vc.spinePacks`); head shapes `TyHead`/`headOf`/`HeadPair`; `Vc.InNf`, `pushSub`, `RedexFree`, `exposesPack`, `base`; pack bounds `Le.PackBound k` and `Le.Strong` (`PackBound 0`: every concrete selection is `defL`/`defR`); normal forms `LeNf`/`LeNfHead` with strong premises `SLe`, the target's `stpp`.  Definitions and their syntactic laws; no typing result. |
| `Normalizer.lean` | `VcTy.toNf`: spine normalization, structural, no hypothesis.  `VcTy.unfoldStep`/`VcTy.canon`: redex elimination, terminating on `(spinePacks, size)`, under `Contract` (discharged in `Inversion`). |
| `CanonicalForms.lean` | Unconditional: `no_pack_at_abs`, the head table `LeTy.headPair_of_not_trans`, `typ_le_bind_is_trans`, `top_le_bot_is_trans`, `VcTy.base_conc`, `dmsHasType_head`, `Store.Honest.head_tyOf`/`not_vacuous`, `VcTy.vcLocAny_head`/`vcLocAny_not_vacuous`, `obs_conc_easy`, `Store.Honest.defL_as_selL`, `Vacuous`/`LeTy.vacuousMono`, `consistency_nil`.  `consistency`/`no_loc_le_bot` under `BoundsVacuous` (discharged in `Inversion`).  `DishonestStore.topLeBot`. |
| `Inversion.lean` | **Transitivity elimination for closed inclusions.**  `EvB`/`LeTy.substB` (substitution keeping a pack bound); `LeTy.pushback`, `LeNf.precompose`, `SLe.nf` with soundness `LeNf.toSLe`; `LitTy`/`RecordedLit` (the only store fact used) with `typInv`/`fnInv`/`bindInv`, `dmsLitTy`, `varyLitTy`, `defsLitTy`; the pack-count tower `ObsInv`/`ObsInv.step`/`LeTy.strengthenAt`.  Results, each at `RecordedLit` and at `Store.Honest`: `nf`, `strengthen`, `clean`, `invTyp`, `invTypTyp`, `invIntoBind`, `invBind`, `obsTyp`, `obsBind`, `obsFun`, `contract`, `canon`, `boundsVacuous`, `no_loc_le_bot`, `consistency_honest` (and `consistency_honest'` via vacuity), `obs_conc_admissible`.  Examples over `TwoObjectStore`. |
| `Preservation.lean` | `TmTy.substEv_skel`/`DefsTy.substEv_skel`; `ContTy`, `StateTy` (typing up to evidence), `MachineStore.Honest` with `nil`/`member`/`obs`/`method`/`alloc`; the views `viewLet`/`viewNew`/`viewApp`/`viewAtom`; the six step cases `StateTy.let_`/`castPush`/`castAtom`/`rename`/`alloc` (no hypothesis) and `StateTy.app` (under `AppInversion`); `AppInversion`, `ObsFunInversion`, `AppInversion.ofObs`, `LocType.method`; `StateTy.erase_eq`; `preservation`, `preservation_steps`, `preservation_init`; the counterexample `OnTheNose`/`MachineStore.Honest.app_var_untypable`; the bridge `Store.Honest.toMachine`/`toMachine_erase`/`toMachine_honest`/`StateTy.ofSource`. |
| `Progress.lean` | `State.CanStep`; `progress_of_not_app` (no typing, no store invariant); `progress_app`, `progress`, `not_stuck`, `safety`, `safety_of_source`, all under `AppInversion`. |
| `MethodInversion.lean` | `defsTy_erase_of_conjunct`, `MachineStore.Honest.recordedLit`, `LocBase.toLocType`; **`obsFunInversion` and `appInversion`**, inhabiting the two hypotheses; and the hypothesis-free `preservation'`, `preservation_steps'`, `preservation_init'`, `progress'`, `not_stuck'`, `safety'`, `safety_of_source'`. |
| `Elaboration.lean` | `elabStp`/`elabHtp`: all 18 `Stp` rules and all 3 `Htp` rules, at an arbitrary `StoreTy`, no hypothesis.  `elabAtom`/`elabHasType`/`elabDms` on the fragment `TmFrag`/`DmsFrag` (variable operands at every `tapp`, both annotations on every `dfun`), no hypothesis; `T_Vary` becomes `AtomTy.varConcAny`.  `elab_recursive`.  `elabAtom` is compiled by well-founded recursion (irreducible by default). |
| `ElaborationErasure.lean` | `elabHasType_erase`/`elabDms_erase`: the fragment elaboration erases to the source term, on the nose, at every store typing.  Four worked instances. |
| `Correspondence.lean` | **The operational correspondence.**  Source evaluation contexts `ECtx` with `ECtx.step`, `ECtx.plug_inv`; `Corr` (by recursion on the target term: atoms are roots, `cast` transparent, `let d u` is `E[r0]`; annotations never read, type members compared exactly), `DmsCorr`, `StoreCorr`, `KCorr`, `Cont.fill`, `corr_fill_iff`, `Rel`; `Corr.skel_iff`, `Rel.of_skel`, `StateTy.corr_witness`; the A-normal shapes `Corr.anf_app`/`anf_recv`/`anf_arg`; commutation with every substitution (`Corr.substEv` etc.); `Rel.init`/`init_iff`, `Rel.final`, `Rel.answer_final`; `SrcStuck`.  The specs `ElabSpec`, `ElabSpecGen` (with `toElabSpec`), `SimStepSpec`, `SimStuckSpec`, `SimSpec`, `Oopsla16Safety`; `transport`, `transport_from`; `normalize` (administrative steps terminate at a focused state); **`sim_step`, `sim_stuck`, `sim_spec`**, no hypothesis; `oopsla16_safety` under `ElabSpec`; `elabSpec_frag`, `oopsla16_safety_frag`.  `LiteralReflection.literal_reflection_false`: "a related target state that steps has a source that steps" is false. |
| `ElaborationFull.lean` | **Elaboration of every source typing.**  `TmElab`/`DefsElabC` (term, typing, correspondence); `TmElab.app` (`T_App` binds both operands), `TmElab.appVar` (`T_AppVar` binds only the receiver, keeping the dependent result type); unannotated `dfun` takes `D_Fun`'s types; `elabTm`/`elabDefs` over all 8 + 3 rules at any store typing; **`elabSpecGen`, `elabSpec`**, `oopsla16Safety_holds`, `oopsla16_safety'`, `oopsla16_progress`, all without hypothesis.  Worked example `CurryCall` (outside `TmFrag`). |
| `Simulation.lean` | **The backward simulation and its consequences.**  `Rel.alloc_reflect`, `Rel.app_reflect`, `Rel.reflect_step`, `Rel.reflect_steps` (each target step is zero or one source step at the same `Grows` index); `Rel.steps'`, `sim_step_plus` (no stuttering); `Rel.final_tm`, `final_run`, `answer_run`, `answer_iff_final`; `Rel.stuck_reflect`, `stuck_iff`, `safe_iff`; `Rel.focused_reflect`, `Rel.progress_reflect`; the invariant `Simulated` with `step`, `steps`, `progress`, `not_stuck`, `reachable_progress`, `of_typed`, `of_frag`, and `of_elab`/`elab_adequacy` under `ElabSpec`; `Rel.of_letFree`. |
| `SourceSafety.lean` | **The end of the line.**  `Simulated.init`, `elab_adequacy'` (the `ElabSpec` theorems at `elabSpec`); `StoreCorr.ofHonest`, `Simulated.of_honest`; **`Oopsla16.oopsla16_safety`, `oopsla16_not_stuck`**, `oopsla16_safety_honest`, `oopsla16_not_stuck_honest`.  Worked instances `ex0_safe`, `RecursiveArg` (a method demanding `μz.T(z)` applied to a literal typed by two `stp_bindx`; the source run, both headline theorems, and the target run reaching a final state), `HonestCall` (over `TwoObjectStore`). |

## Road to a WadlerFest-style safety theorem

In dependency order.

1. **Substitution theorem** — **done.**  `LeTy.substEv`/`VcTy.substEv` (and
   `AtomTy`/`TmTy`/`DefsTy.substEv`) hold with `MonoSyn.Ev`/`EvA` as their only
   premise, which `refl` inhabits.
2. **Canonical forms** — **done**, over an honest store: `Inversion`
   eliminates transitivity from every closed inclusion and inverts closed
   observations of a location at type members, recursive types and method
   types.  Transitivity is eliminated in the empty local context only, as in
   the reference.
3. **Preservation** — **done**, up to evidence: `preservation'`,
   `preservation_steps'`.
4. **Progress** — **done**: `progress'`, `not_stuck'`, `safety'`.
5. **Elaboration from `Oopsla16.Stp`/`HasType`** — **done**:
   `ElaborationFull.elabTm`/`elabDefs` elaborate every source typing, general
   `tapp` by A-normalisation and unannotated `dfun` by `D_Fun`'s types
   (`elabSpec`).
6. **Operational correspondence** — **done**, in place of an erasure
   equation: `Correspondence.Corr`/`Rel` with the forward simulation
   (`sim_step`, `sim_stuck`) and `Simulation`'s backward one
   (`Rel.reflect_step`).  The on-the-nose erasure equation still holds only on
   the fragment, and cannot hold beyond it: a `let` erases to an object
   encoding.
7. **Safety transport** — **done**: `Oopsla16.oopsla16_safety`,
   `oopsla16_not_stuck`, with no hypothesis, in the shape of
   `DotToFCdot/Safety.lean` (`Simulated`, `Rel.final_tm`/`Rel.answer_final`
   for `final_erase`/`final_reflect`).

## What remains

* **Honest-store safety for general stored witnesses.**  Needs a translation
  of target typing back into source typing, so that source honesty survives
  the elaboration of `let`-bearing method bodies.  `obs_conc_admissible` is the
  selection case of it; the translation is not built.  `T_Vary` witnesses read
  whole stored literals, so matching type members alone is not enough.
* No determinism theorem for either machine (the simulation uses only
  `ECtx.plug_inv`, determinism at a focused redex), and no statement about
  divergence (`sim_step_plus` is the piece it would use).

## Integration notes

* **The source-safety chain.**  `Correspondence` imports `MethodInversion`;
  `ElaborationFull` and `Simulation` each import only `Correspondence`;
  `SourceSafety` imports both.  So the `ElabSpec`-taking theorems of
  `Correspondence` and `Simulation` keep the hypothesis (they sit below
  `elabSpec`), and their doc comments name `ElaborationFull.elabSpec` and the
  hypothesis-free restatements.
* **Hypothesis-carrying statements are kept, not replaced.**  `Normalizer`,
  `CanonicalForms`, `Preservation` and `Progress` likewise keep theirs, with
  the hypothesis-free versions in `Inversion` and `MethodInversion`.  Doc
  comments that still said an obligation was open (`Correspondence`,
  `Simulation`, `MethodInversion`, `Progress`, `Preservation`, `Erasure`,
  `Elaboration`) were corrected during integration; the edits are doc-only.
* **Duplicates to fold later.**  `Inversion.LocBase` and
  `Preservation.LocType` are the same two location nodes
  (`LocBase.toLocType` bridges them); `Inversion.dmsTyp_label_lt` and
  `Preservation.dms_get?_lt` are the same lemma, on separate import branches;
  `FCdotR.Ctx.renameStore` in `StoreTyping.lean` still shadows
  `Oopsla16.Ctx.renameStore`.  `Preservation`'s `TmTy.Core`, `TmTy.core` and
  `Tm.skel_eq_*` compile but are unused.  `ElaborationFull.oopsla16_safety'`
  and `Oopsla16.oopsla16_safety`, and `ElaborationFull.oopsla16_progress` and
  `Oopsla16.oopsla16_not_stuck`, state the same things.  None was folded:
  each fold either deletes a theorem or moves a definition across import
  branches.
* **`Inst` and `MonoSyn` are two functions.**  `MonoSyn.ofInst` bridges them;
  their syntactic actions genuinely differ (`Vc.inst` sends `vcVar` at the
  instantiated binder to `vcLoc`, `Le.inst` leaves `defL`/`defR` sub-evidence
  alone), and `Tm.erase_inst_subst` proves the two erase to the same source
  term.
* `Oopsla16/SubstLemmas.lean` carries `@[simp]` lemmas that change the global
  simp set downstream; all five libraries rebuild without regression.
