# FCdotR — status

State of the `Coercions.FCdotR` library as integrated on branch
`fcdot-recursive-subtyping`.  FCdotR is the explicit-evidence **target** for
the `Coercions.Oopsla16` source (Rompf–Amin OOPSLA'16 DOT, which has
recursive subtyping).  It is a *second* target: the WadlerFest→FCdot chain in
`DotMNF`/`DotToFCdot`/`FCdot` is not reused, only imitated.

`lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR` completes in **114 jobs**.
Its only warning is the pre-existing unused `termination_by` at
`FCdot/Syntax.lean:221`, outside this library.  There is no `sorry`, `admit`,
`axiom`, `native_decide` or `partial` anywhere in `FCdotR/` or `Oopsla16/`
outside doc comments.  An environment-wide audit of every constant defined in
`Coercions.FCdotR.*` and `Coercions.Oopsla16.*` reports `checked 5818
constants; offending: 0`: nothing uses an axiom beyond `propext` and
`Quot.sound`.

**Over an honest store, canonical forms, consistency, preservation and
progress are all proved with no unproved hypothesis**, and so is type safety
of the FCdotR machine (`MethodInversion.safety'`, `safety_of_source'`).  What
is still missing is the transport of safety to `Oopsla16`'s own semantics
(road items 5–7 below).

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

`ObsConcAdmissible` (`CanonicalForms`) is a named statement rather than a
hypothesis — nothing takes it as an argument — and `Inversion.obs_conc_admissible`
proves it over every honest store.  `VaryEv` and `LemmaR`, hypotheses of
earlier rounds, are gone: `VaryEv` was false and was removed when the target
acquired `T_Vary` verbatim (`VcTy.vcLocAny`, `AtomTy.varConcAny`); `LemmaR` is
inhabited by `SubstTyping.lemmaR`.

The results are nonetheless **restricted**, by invariants and fragments that
are not hypotheses:

* `Store.Honest` (source store) and `MachineStore.Honest` (machine store) are
  real store invariants; `CanonicalForms.DishonestStore` shows that `LeTy`
  alone is inconsistent, so they cannot be dropped.
* Preservation types a state **up to evidence** (`Preservation.StateTy`: some
  typed term and continuation with the state's skeleton).  On-the-nose typing
  is false for this machine (`Preservation.OnTheNose`).
* `safety_of_source` needs the source term and every stored witness in the
  elaboration's fragment (`TmFrag`/`DmsFrag`); `Step.simulate` needs a
  continuation with no `let` frame (`Cont.Evidential`).

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
| `Elaboration.lean` | `elabStp`/`elabHtp`: all 18 `Stp` rules and all 3 `Htp` rules, at an arbitrary `StoreTy`, no hypothesis.  `elabAtom`/`elabHasType`/`elabDms` on the fragment `TmFrag`/`DmsFrag` (variable operands at every `tapp`, both annotations on every `dfun`), no hypothesis; `T_Vary` becomes `AtomTy.varConcAny`.  `elab_recursive`. |
| `ElaborationErasure.lean` | `elabHasType_erase`/`elabDms_erase`: the elaborated term erases to the source term, on the nose, at every store typing.  Four worked instances. |

## Road to a WadlerFest-style safety theorem

In dependency order.

1. **Substitution theorem** — **done.**  `LeTy.substEv`/`VcTy.substEv` (and
   `AtomTy`/`TmTy`/`DefsTy.substEv`) hold with `MonoSyn.Ev`/`EvA` as their only
   premise, which `refl` inhabits.
2. **Canonical forms** — **done**, over an honest store:
   `Inversion` eliminates transitivity from every closed inclusion and inverts
   closed observations of a location at type members, recursive types and
   method types, which inhabits `Contract` and `BoundsVacuous` and proves
   consistency with honesty as the only hypothesis.  Transitivity is eliminated
   in the empty local context only, as in the reference.
3. **Preservation** — **done**, up to evidence: `preservation'` and
   `preservation_steps'` carry a typed state over an honest machine store along
   any run with no hypothesis, typing each state by a witness with its
   skeleton, because on-the-nose typing is false (`OnTheNose`).
4. **Progress** — **done**: `progress'` and `not_stuck'` hold with no
   hypothesis, and `safety'`/`safety_of_source'` combine them into type safety
   of the FCdotR machine.
5. **Elaboration from `Oopsla16.Stp`/`HasType`** — *partial*: all subtyping
   and observation rules elaborate unconditionally, but terms only on the
   fragment `TmFrag`/`DmsFrag`; general `tapp` needs let-normalisation and its
   operational correspondence, and unannotated `dfun` types but does not erase
   on the nose.
6. **Erasure equality** — *partial*: elaborated terms erase to their sources
   on the fragment, but the machine simulation `Step.simulate` holds only
   while the continuation has no `let` frame, because `let` erases to an object
   encoding whose consumption extends the source store.
7. **Safety transport** — *not started*: the target side it needs (items 3
   and 4) is now proved, but the `DotToFCdot/Safety.lean` shape
   (`Simulated`, `final_erase`/`final_reflect`, `dot_safety`,
   `dot_not_stuck`) for `Oopsla16` waits on items 5 and 6.

## Integration notes

* **`MethodInversion` joins two tracks.**  It imports `Inversion` and
  `Progress` (hence `Preservation`) and reads `ObsFunInversion`, `LocType` and
  `MachineStore.Honest`.  Renaming any of those breaks the root build; that is
  intended, since it is the one place the hypothesis is discharged.
* **Hypothesis-carrying statements are kept, not replaced.**  `Normalizer`,
  `CanonicalForms`, `Preservation` and `Progress` sit below the proofs of their
  hypotheses in the import order, so their theorems keep the argument; their
  doc comments now say where it is discharged, and the hypothesis-free versions
  live in `Inversion` and `MethodInversion`.  Doc comments that still said
  "nothing inhabits" were corrected during integration.
* **Duplicates to fold later.**  `Inversion.LocBase` and
  `Preservation.LocType` are the same two location nodes
  (`LocBase.toLocType` bridges them); `Inversion.dmsTyp_label_lt` and
  `Preservation.dms_get?_lt` are the same lemma (renamed apart to avoid a
  clash); `FCdotR.Ctx.renameStore` in `StoreTyping.lean` still shadows
  `Oopsla16.Ctx.renameStore`.  `Preservation`'s `TmTy.Core`, `TmTy.core` and
  `Tm.skel_eq_*` compile but are unused.
* **Source honesty is not maintained through a run.**  The machine is kept
  honest by `MachineStore.Honest`, which types stored *target* literals.
  Keeping `Store.Honest` of the erased store instead would need a translation
  of target typing back into source typing; `obs_conc_admissible` is the
  selection case of that translation and is now proved, but the translation is
  not built.  `Store.Honest.toMachine` goes the other way, source to machine,
  on the elaboration's fragment.
* **`Inst` and `MonoSyn` are two functions.**  `MonoSyn.ofInst` bridges them;
  their syntactic actions genuinely differ (`Vc.inst` sends `vcVar` at the
  instantiated binder to `vcLoc`, `Le.inst` leaves `defL`/`defR` sub-evidence
  alone), and `Tm.erase_inst_subst` proves the two erase to the same source
  term.
* `Oopsla16/SubstLemmas.lean` carries `@[simp]` lemmas that change the global
  simp set downstream; all five libraries rebuild without regression.
