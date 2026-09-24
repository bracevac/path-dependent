# FCdotR — status

State of the `Coercions.FCdotR` library as integrated on branch
`fcdot-recursive-subtyping`.  FCdotR is the explicit-evidence **target** for
the `Coercions.Oopsla16` source (Rompf–Amin OOPSLA'16 DOT, which has
recursive subtyping).  It is a *second* target: the WadlerFest→FCdot chain in
`DotMNF`/`DotToFCdot`/`FCdot` is not reused, only imitated.

`lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR`, run on a clean export
of the committed tree, completes in **113 jobs**.  Its only warning is the
pre-existing unused `termination_by` at `FCdot/Syntax.lean:221`, outside this
library.  There is no `sorry`, `admit`, `axiom` declaration, `native_decide`
or `partial` anywhere in `FCdotR/` or `Oopsla16/` outside comments.  The axiom audit
`audit/AxiomAudit.lean` (see *Reproducing the checks*) visits every constant
defined in `Coercions.FCdotR.*` and `Coercions.Oopsla16.*` and reports
`checked 7565 constants; offending: 0`: nothing uses an axiom beyond `propext`
and `Quot.sound`.

The history of the two figures, each job count measured on a clean export of
the commit (`git archive`), so that no uncommitted module of another library
enters it:

| commit | jobs | constants | added since the row above |
| --- | --- | --- | --- |
| `aa7ca71` | 107 | 6258 | |
| `5324088` | 108 | 6323 | `Deliverables.lean` (one job, 65 constants) |
| `4312920` | 111 | 7179 | the `LitMatch` premise of the location rules (47 constants), the checker `Checker`, `CheckerCompleteness`, `CheckerExamples` (three jobs, 809 constants) |
| `d3fd166` | 112 | 7336 | `LitMatch` demanding both annotations, `Dms.Annotated`/`Store.Annotated`, the converse lemmas (`varyLitMatch_annotated`, `LitMatch.no_unannotated_method`, …) and the module `Admissibility` (one job, 157 constants) |
| this change | 113 | 7565 | the module `Coverage`, the reference's examples `ex1`, `ex2` and `paper_lst` and the section on stored annotations in `CheckerExamples` (one job, 229 constants) |

The commit messages of `aa7ca71`, `5324088`, `4312920` and `d3fd166` gave
118, 119, 122 and 123 jobs, and earlier versions of this file repeated some of
them.  Those figures were measured on a working tree that also held eleven
uncommitted modules of the WadlerFest line, which the uncommitted edits to
`FCdot.lean` and `DotToFCdot.lean` import; they are not the counts of the
commits.  The constant counts are not affected, since the audit visits only
`FCdotR` and `Oopsla16`.  On that working tree the same command now completes
in 124 jobs.

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
`oopsla16_not_stuck` mentions only `Oopsla16`'s `HasType`, `Steps`, `Step` and
`IsAnswer`.  `oopsla16_safety` also uses `FCdotR.SrcStuck`, a definition in
namespace `FCdotR` (`Correspondence.lean`) whose body, shown above, uses only
`Oopsla16.Tm.IsAnswer` and `Oopsla16.Step`.  So the meaning of either statement
does not depend on the correspondence or on the target.  The positive form is proved
constructively from the `Simulated` invariant, not derived from the negative
one (that would need classical logic).  Naming follows the brief: here
`…_safety` is the negative form and `…_not_stuck` the positive one, the reverse
of `DotMNF.dot_safety`/`dot_not_stuck`.

**Not vacuous** (`Coverage.NonVacuity`; at integration this was a scratch
file, and it is now part of the library).  Typed closed programs exist:
`Oopsla16.Examples.ex0` and `SourceSafety.RecursiveArg.progTy` (the latter
outside `TmFrag`, and needing `stp_bindx`).  `SrcStuck` is inhabited:
`NonVacuity.badTerm_stuck` is `SrcStuck PackingCounterexample.G badTerm`.  The
ill-typed `tapp (tobj dnil) 0 (tobj dnil)` reaches a stuck configuration from
the empty store in two source steps (`ill_reaches_stuck`), so
`oopsla16_safety` refutes every typing of it (`ill_untypable`); and
`oopsla16_safety_honest` over `TwoObjectStore.honest` refutes every
`Oopsla16` typing of `badTerm`, which only the `htp_pack` extension types
(`badTerm_untypable`).

The honest-store versions `Oopsla16.oopsla16_safety_honest` and
`oopsla16_not_stuck_honest` start from a term typed over an honest source
store (`Store.Honest G W`).  The term is arbitrary; the literal each location
was typed from must lie in `DmsFrag` (see *Restrictions*).

`ElaborationFull.oopsla16_safety'`/`oopsla16Safety_holds` and
`ElaborationFull.oopsla16_progress` are the same two statements, proved in that
module; `SourceSafety` restates them in the source's namespace.

### What the headline does not say

The adversarial review at integration found no defect that makes
`oopsla16_safety` prove less than its statement says.  It found two limits.
Both can be read off the statement, and no doc comment overstates either.

* **No preservation for the source.**  The reference's `type_safety`
  (`dot_soundness.v:1131`) also re-types the stepped term at the same type `T`.
  The Lean conclusion never mentions `T`: it says "typable at some type,
  therefore never stuck".  Nothing in FCdotR proves that a reached source
  term, or the final answer, has type `T` in `Oopsla16`.  *Preservation* in
  this file always means the FCdotR machine's, up to evidence.  The closest
  source-side statement is `Oopsla16.reachable_related`: the target state
  related to a reached configuration is typed at `T`, moved along the
  allocations.  WadlerFest's `DotMNF.dot_safety` has the same shape.
* **The run starts from the empty store.**  The reference's statement is one
  step over any store.  Iterated, it implies the Lean headline only together
  with determinism of `step`, which holds by inspection of `dot.v:197-212` but
  is proved by neither artifact.  The Lean headline does not imply the
  reference's statement: it says nothing about types after a step, nor about
  other starting stores.  For a closed program nothing is lost: a `Tm [] []`
  cannot mention a location, and every configuration reachable from it,
  allocations included, is covered.  But safety cannot be restarted from an arbitrary
  typed configuration over an arbitrary store.  A store holding one object
  with a Curry-style identity method, and the term `id.0(id)`, is typed by
  `T_Vary` and steps, so the reference covers it; the headline needs the empty
  store, and the honest-store versions cannot be applied, because no honest
  witness at that location is in `DmsFrag` (`Coverage.CurryGap`:
  `idApp_typed`, `idApp_steps`, `not_frag`; at integration this was the
  review scratch file `R4Store.lean`).

## Hypotheses

Every hypothesis structure still in the code is **inhabited**.  Each is kept as
an explicit argument only in the modules that sit below its proof in the import
order; the doc comment of every theorem that takes one names where it is
discharged.  The exception is `Store.Annotated G`, which is a property of one
store rather than a structure to inhabit: it holds at the empty store and at
the stores of the honest-store theorems, and fails at some honest stores (last
row).

| Hypothesis | Taken by | What it says | Discharged by |
| --- | --- | --- | --- |
| `Contract G W` | `Normalizer`: `VcTy.unfoldStep`, `VcTy.canon` | an unfolding-over-packing redex can be contracted without growing the spine pack count | `Inversion.Store.Honest.contract` (any honest store); `Store.Honest.canon` is `canon` without it |
| `BoundsVacuous G W` | `CanonicalForms`: `consistency`, `no_loc_le_bot` | the bounds a closed observation of a location reports are sound for `Vacuous` | `Inversion.Store.Honest.boundsVacuous`; `consistency_honest`, `Store.Honest.no_loc_le_bot` are the theorems without it |
| `AppInversion` | `Preservation`: `StateTy.app`, `preservation`, `preservation_steps`, `preservation_init`; `Progress`: `progress_app`, `progress`, `not_stuck`, `safety`, `safety_of_source` | canonical forms for methods: a closed atom at `{l : S0 → U0}` over an honest machine store is rooted at a location storing a method at `l` | `MethodInversion.appInversion`; the primed theorems in `MethodInversion` are the unprimed ones without it |
| `ObsFunInversion` | `Preservation`: `AppInversion.ofObs` | the evidence-level content of `AppInversion`: a closed observation at a method type inverts to a method conjunct of a location node's type | `MethodInversion.obsFunInversion`, from `Inversion.RecordedLit.obsFun` |
| `ElabSpec` | `Correspondence`: `transport`, `oopsla16_safety`; `Simulation`: `Simulated.of_elab`, `elab_adequacy` | every closed source typing elaborates to a typed FCdotR term whose initial state is related (`Rel`) to the source term | `ElaborationFull.elabSpec` (via `elabSpecGen`); `SourceSafety`'s `Simulated.init`, `elab_adequacy'`, `Oopsla16.oopsla16_safety` are the theorems without it |
| `SimSpec` (`SimStepSpec ∧ SimStuckSpec`) | `Correspondence`: `transport`, `transport_from`; `SimStepSpec` alone: `Rel.steps` | a source step from a related pair is matched by a target run; a stuck source makes a related target run into a stuck state | `Correspondence.sim_spec` (`sim_step`, `sim_stuck`), in the same module; `Simulation.Rel.steps'` is `Rel.steps` without it |
| `Store.Annotated G` (an instance argument) | `Elaboration`: `elabAtom`, `elabHasType`, `elabDms` and their erasure and correspondence theorems; `ElaborationFull`: `elabTm`, `elabDefs`; `Correspondence.ElabSpecGen` (explicit), hence `elabSpecGen` | every method stored in `G` carries both annotations, which the elaboration of `T_Vary` uses (`varyLitMatch`); a `T_Vary` premise pair gives the location rules' premise only at an annotated location (`varyLitMatch_annotated`), and that an elaboration at every store typing needs the hypothesis is argued, not proved | at the empty store by the instance `Store.Annotated.nil`, which is how `ElabSpecGen.toElabSpec`, `elabSpec`, `reachable_related` and every empty-store theorem get it; at a store of the honest-store theorems by `Store.Honest.annotated` (fragment witnesses); at `TwoObjectStore` by an instance.  **Not dischargeable in general**: `Admissibility.CurryStore` is honest and not annotated (`CurryStore.not_annotated`) |

`ObsConcAdmissible` (`CanonicalForms`) is a named statement rather than a
hypothesis — nothing takes it as an argument — and `Inversion.obs_conc_admissible`
proves it over every honest store.  `VaryEv` and `LemmaR`, hypotheses of
earlier rounds, are gone: `VaryEv` fails in general (argued in `Elaboration`'s
header, not proved) and was removed when the target acquired location rules
at the types the source's `T_Vary` gives (`VcTy.vcLocAny`, `AtomTy.varConcAny`,
whose premise is now `LitMatch`, at annotated locations); `LemmaR` is
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
* **The location rules are not `T_Vary`, and `T_Vary` reaches them only at an
  annotated location.**  `VcTy.vcLocAny` and `AtomTy.varConcAny` take
  `LitMatch`: type members exact, method members at exactly the two
  annotations of a method stored with both, no method body typed.  Over an
  honest store every typing they give is a source typing
  (`Admissibility.Store.Honest.litMatch_stp`, `litMatch_hasType`,
  `varConcAny_admissible`, `vcLocAny_admissible`).  `T_Vary` gives the match
  exactly when the stored methods are annotated (`varyLitMatch`,
  `varyLitMatch_annotated`), so the term elaboration takes `Store.Annotated G`
  (table above).  At commit `4312920` a method member was compared with the
  stored annotations by `EqSome`, which let an unannotated stored method match
  every method type and typed `ℓ.0(ℓ)` at `⊥` over `{def 0(y) = y}` (an audit
  probe, not in the repository); that term is now rejected
  (`CheckerExamples.appBot_untypable`).  The rules still take the stored
  annotations on trust, as `vcLoc` takes `W`: over the annotated store
  holding `{def 0(y : ⊤) : ⊥ = y}` the target types `ℓ.0(ℓ)` at `⊥` at every
  store typing, `Oopsla16` types it at no type, and the store has no honest
  store typing (`Coverage.UncheckedBody.appBot_typed`, `app_untypable`,
  `not_honest`).  So the admissibility above needs an honest store: at any
  location without a `T_Vary` typing, `loc ℓ ⊤` is typed at every `W` and
  the source types `ℓ` at nothing (`Coverage.noVary_not_admissible`).  No
  safety theorem is affected: each starts from an honest store, the empty one
  or one given with its honesty, and the machine keeps its store honest
  (`MachineStore.Honest`).
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
| `README.md` | What the library is, its modules in reading order, the main theorems, and the design points. |
| `PLAN.md` | The design: substitution via prefix restriction, the elaboration of 32 source rules, the metatheory order, and the open questions.  Not code. |
| `Prefix.lean` | The prefix apparatus at a two-zone variable: `scopeAt`, `renameAt`, `selfAt`, `ctxAt`, `Zone`, the `upTo`/`renameUpTo` transport laws, and `renameUpTo_comp` (weakenings out of iterated prefixes compose) with its transport helpers. |
| `Syntax.lean` | The five grammars — inclusion evidence `Le`, observation evidence `Vc` (indexed at its subject's prefix scope), `Atom`, `Tm`, `Defs` — plus `Atom.root` and `Defs.length`.  A location has two `Vc` nodes, `vcLoc ℓ` and `vcLocAny ℓ T`, the second carrying a self type as syntax, and two atoms, `var (conc ℓ)` and `loc ℓ T`. |
| `Typing.lean` | `StoreTy`/`tyOf`; `LitMatch`, the decidable premise of the location rules (a type matches a stored literal member by member: type members exact, method members at a stored method's two annotations, which must both be present); the two evidence judgments `LeTy` (inclusion) and `VcTy` (observation).  `VcTy` has two location rules: `vcLoc` at the recorded type `tyOf W ℓ`, and `vcLocAny` at a carried self type whose instance matches the stored literal, which is not `T_Vary`.  No term typing here. |
| `Structural.lean` | `MonoAt`/`Mono`: a substitution carrying a per-variable image and restriction satisfying the star law.  `Mono` is not closed under restriction; `Subst.lean`'s `MonoSyn` is the answer, and `MonoSyn.toMono` embeds it. |
| `Locality.lean` | Lemma 0, the locality of observation evidence: `VcTy.strengthen` and `VcTy.ofLoc`. |
| `Examples.lean` | The `FunctionField` example elaborated by hand: a closed `bindx` derivation whose method body uses a `selL` under the enclosing self.  That FCdot cannot express its WadlerFest counterpart is `DotMNF.RecursiveSubtyping.FunctionField.no_coercion` in `DotToFCdot/RecursiveSubtypingSeparation.lean`, uncommitted work (`README.md`, *References to uncommitted work*), so not proved in the repository. |
| `Subst.lean` | `MonoSyn`, the inductive syntax of generated substitutions, closed under restriction (`resSyn`).  The substitution action on all five sorts, the star laws, `toMono`, `restrict_unique`, and the image/restriction laws for iterated prefixes. |
| `SubstTyping.lean` | `MonoSyn.Ev` with `refl`/`lift`/`atNil`; `VcTy.toFull`/`weakenVar`/`strengthenCons`; `MonoSyn.restrict_coh`; `VcTy.descendAbs`/`descend`; `lemmaRVc`/`lemmaR`; and the **unconditional** substitution theorem `LeTy.substEv`/`VcTy.substEv`, one premise, `MonoSyn.Ev`. |
| `TermSubst.lean` | `MonoSyn.Ev.weaken`; `MonoSyn.EvA` (`Ev` plus an atom at each abstract variable) with `refl`/`weaken`/`lift`; `AtomTy.weakenVar`; and the substitution theorem for the three term judgments, `AtomTy.substEv`/`TmTy.substEv`/`DefsTy.substEv`. |
| `StoreTyping.lean` | `Conjunct`, `DmsHasType.conjunct` and `DmsHasType.conjunctFun`; `dms_get?_head`/`dms_get?_tail`; `Dm.Annotated`, `Dms.Annotated` (decidable) and the class `Store.Annotated` with the instance `Store.Annotated.nil`, `Store.Annotated.cons`, decidability, `Dms.annotated_subst`; `Store.Honest` (every location holds a literal typed at its store type) with `vary`, `member`, `method`, `obs`, `alloc`; `dmsLitMatch`/`varyLitMatch` (a `T_Vary` premise pair gives `LitMatch` when the stored literal is annotated) and the converses `dmsLitMatch_annotated`/`varyLitMatch_annotated`, with `varyLitMatch_iff`; `LitMatch.storedMethod` and `LitMatch.no_unannotated_method` (a method member needs a method stored with both annotations); `varyMember`/`varyMethod`/`varyObs` for a bare `T_Vary` witness; `Store.Honest.vcLoc_of_vcLocAny` (at an annotated location), `Store.Honest.litMatch_tyOf_iff`, `Store.Honest.not_vcLocAny_tyOf` (and only there); store renaming for the four source judgments; a substitution's store part, with `defs_get?`, `LitMatch.subst` and `varyTy` moving `LitMatch` along it.  `TwoObjectStore`, with `TwoObjectStore.annotated`. |
| `TermTyping.lean` | The three term judgments `AtomTy` (6 rules), `TmTy` (5), `DefsTy` (3), one rule per syntax node, with two location rules: `varConc` on `var (conc ℓ)` and `varConcAny` on `loc ℓ T`.  `TmTy.appWeaken`, `AtomTy.toVc`, `Store.Honest.varConc_of_varConcAny` (at an annotated location); `FunctionFieldObject`. |
| `Admissibility.lean` | **Over an honest store the location rules derive nothing the source cannot.**  `Conjunct.stp`; `Store.Honest.litMatch_stp` (a matched type is a source supertype of the recorded type, empty context) and `litMatch_stpAt` (any context); `Store.Honest.litMatch_hasType`/`litMatch_hasTypeAt` (`T_Vary` at the honesty witness, then `T_Sub`); `Store.Honest.varConcAny_admissible`, `vcLocAny_admissible`; at a location holding a method without both annotations, `varConcAny_not_vary` and `vcLocAny_not_vary` (the location rules give no `T_Vary` type); `muDrop_admissible`.  Worked instance `CurryStore`: an honest store holding `{def 0(y) = y}` without annotations, `not_annotated`, `lit_not_annotated`, `varyTyped`, `loc_untypable` (`loc ℓ` at the `T_Vary` type, at every store typing), `varConcTyped` (`var (conc ℓ)` at that type, through the honest store typing), `topTyped`. |
| `Machine.lean` | The runtime: `Inst` and its action on all five sorts, `MachineStore`, `Frame`/`Cont`/`State`, `Step`/`Steps` indexed by `Oopsla16.Grows`, six rules, `State.Final`/`State.Stuck`.  `MonoSyn.ofInst` makes `Inst` a `MonoSyn` at the typing level. |
| `Erasure.lean` | `Tm.erase`/`Defs.erase`/`MachineStore.erase` into `Oopsla16` and its commutation laws; the **evidence skeleton** `Tm.skel`/`Defs.skel`/`Cont.skel` (roots, annotations and term structure kept, casts and atom wrappers forgotten) with `Tm.skel_inst`, `Tm.erase_skel`; `Step.simulate`/`Steps.simulate` under `Cont.Evidential`.  `Counterexample.badRun`. |
| `Forms.lean` | Measures (`Le.size`, `packs`, `Vc.spinePacks`); head shapes `TyHead`/`headOf`/`HeadPair`; `Vc.InNf`, `pushSub`, `RedexFree`, `exposesPack`, `base`; pack bounds `Le.PackBound k` and `Le.Strong` (`PackBound 0`: every concrete selection is `defL`/`defR`); normal forms `LeNf`/`LeNfHead` with strong premises `SLe`, the target's `stpp`.  Definitions and their syntactic laws; no typing result. |
| `Normalizer.lean` | `VcTy.toNf`: spine normalization, structural, no hypothesis.  `VcTy.unfoldStep`/`VcTy.canon`: redex elimination, terminating on `(spinePacks, size)`, under `Contract` (discharged in `Inversion`). |
| `CanonicalForms.lean` | Unconditional: `no_pack_at_abs`, the head table `LeTy.headPair_of_not_trans`, `typ_le_bind_is_trans`, `top_le_bot_is_trans`, `VcTy.base_conc`, `dmsHasType_head`, `Store.Honest.head_tyOf`/`not_vacuous`, `VcTy.vcLocAny_head`/`vcLocAny_not_vacuous`, `obs_conc_easy`, `Store.Honest.defL_as_selL`, `Vacuous`/`LeTy.vacuousMono`, `consistency_nil`.  `consistency`/`no_loc_le_bot` under `BoundsVacuous` (discharged in `Inversion`).  `DishonestStore.topLeBot`. |
| `Inversion.lean` | **Transitivity elimination for closed inclusions.**  `EvB`/`LeTy.substB` (substitution keeping a pack bound); `LeTy.pushback`, `LeNf.precompose`, `SLe.nf` with soundness `LeNf.toSLe`; `LitTy`/`RecordedLit` (the only store fact used) with `typInv`/`fnInv`/`bindInv`, `LitMatch.toLitTy`, `dmsLitTy`, `varyLitTy`, `defsLitTy`; the pack-count tower `ObsInv`/`ObsInv.step`/`LeTy.strengthenAt`.  Results, each at `RecordedLit` and at `Store.Honest`: `nf`, `strengthen`, `clean`, `invTyp`, `invTypTyp`, `invIntoBind`, `invBind`, `obsTyp`, `obsBind`, `obsFun`, `contract`, `canon`, `boundsVacuous`, `no_loc_le_bot`, `consistency_honest` (and `consistency_honest'` via vacuity), `obs_conc_admissible`.  Examples over `TwoObjectStore`. |
| `Preservation.lean` | `TmTy.substEv_skel`/`DefsTy.substEv_skel`; `ContTy`, `StateTy` (typing up to evidence), `MachineStore.Honest` with `nil`/`member`/`obs`/`method`/`alloc`; the views `viewLet`/`viewNew`/`viewApp`/`viewAtom`; the six step cases `StateTy.let_`/`castPush`/`castAtom`/`rename`/`alloc` (no hypothesis) and `StateTy.app` (under `AppInversion`); `AppInversion`, `ObsFunInversion`, `AppInversion.ofObs`, `LitMatch.method`, `LocType.method`; `StateTy.erase_eq`; `preservation`, `preservation_steps`, `preservation_init`; the counterexample `OnTheNose`/`MachineStore.Honest.app_var_untypable`; the bridge `Store.Honest.toMachine`/`toMachine_erase`/`toMachine_honest`/`StateTy.ofSource`. |
| `Progress.lean` | `State.CanStep`; `progress_of_not_app` (no typing, no store invariant); `progress_app`, `progress`, `not_stuck`, `safety`, `safety_of_source`, all under `AppInversion`. |
| `MethodInversion.lean` | `defsTy_erase_of_conjunct`, `MachineStore.Honest.recordedLit`, `LocBase.toLocType`; **`obsFunInversion` and `appInversion`**, inhabiting the two hypotheses; and the hypothesis-free `preservation'`, `preservation_steps'`, `preservation_init'`, `progress'`, `not_stuck'`, `safety'`, `safety_of_source'`. |
| `Elaboration.lean` | `elabStp`/`elabHtp`: all 18 `Stp` rules and all 3 `Htp` rules, at an arbitrary `StoreTy`, no hypothesis.  `elabAtom`/`elabHasType`/`elabDms` on the fragment `TmFrag`/`DmsFrag` (variable operands at every `tapp`, both annotations on every `dfun`), under the instance `Store.Annotated G`; `T_Vary` becomes the atom `loc ℓ T`, typed by `AtomTy.varConcAny`.  `DmFrag.annotated`, `DmsFrag.annotated`, `Store.Honest.annotated`.  `elab_recursive`.  `elabAtom` is compiled by well-founded recursion (irreducible by default). |
| `ElaborationErasure.lean` | `elabHasType_erase`/`elabDms_erase`: the fragment elaboration erases to the source term, on the nose, at every store typing, over every annotated store.  Four worked instances. |
| `Correspondence.lean` | **The operational correspondence.**  Source evaluation contexts `ECtx` with `ECtx.step`, `ECtx.plug_inv`; `Corr` (by recursion on the target term: atoms are roots, `cast` transparent, `let d u` is `E[r0]`; annotations never read, type members compared exactly), `DmsCorr`, `StoreCorr`, `KCorr`, `Cont.fill`, `corr_fill_iff`, `Rel`; `Corr.skel_iff`, `Rel.of_skel`, `StateTy.corr_witness`; the A-normal shapes `Corr.anf_app`/`anf_recv`/`anf_arg`; commutation with every substitution (`Corr.substEv` etc.); `Rel.init`/`init_iff`, `Rel.final`, `Rel.answer_final`; `SrcStuck`.  The specs `ElabSpec`, `ElabSpecGen` (over annotated stores, with `toElabSpec` at the empty store), `SimStepSpec`, `SimStuckSpec`, `SimSpec`, `Oopsla16Safety`; `transport`, `transport_from`; `normalize` (administrative steps terminate at a focused state); **`sim_step`, `sim_stuck`, `sim_spec`**, no hypothesis; `oopsla16_safety` under `ElabSpec`; `elabSpec_frag`, `oopsla16_safety_frag`.  `LiteralReflection.literal_reflection_false`: "a related target state that steps has a source that steps" is false. |
| `ElaborationFull.lean` | **Elaboration of every source typing over an annotated store.**  `TmElab`/`DefsElabC` (term, typing, correspondence); `TmElab.app` (`T_App` binds both operands), `TmElab.appVar` (`T_AppVar` binds only the receiver, keeping the dependent result type); unannotated `dfun` takes `D_Fun`'s types; `elabTm`/`elabDefs` over all 8 + 3 rules at any store typing, over an annotated store (`Store.Annotated G`, an instance); **`elabSpecGen`** (under `ElabSpecGen`'s hypothesis `Store.Annotated G`), **`elabSpec`**, `oopsla16Safety_holds`, `oopsla16_safety'`, `oopsla16_progress`, the last four without hypothesis.  Worked example `CurryCall` (outside `TmFrag`). |
| `Simulation.lean` | **The backward simulation and its consequences.**  `Rel.alloc_reflect`, `Rel.app_reflect`, `Rel.reflect_step`, `Rel.reflect_steps` (each target step is zero or one source step at the same `Grows` index); `Rel.steps'`, `sim_step_plus` (no stuttering); `Rel.final_tm`, `final_run`, `answer_run`, `answer_iff_final`; `Rel.stuck_reflect`, `stuck_iff`, `safe_iff`; `Rel.focused_reflect`, `Rel.progress_reflect`; the invariant `Simulated` with `step`, `steps`, `progress`, `not_stuck`, `reachable_progress`, `of_typed`, `of_frag`, and `of_elab`/`elab_adequacy` under `ElabSpec`; `Rel.of_letFree`. |
| `SourceSafety.lean` | **The end of the line.**  `Simulated.init`, `elab_adequacy'` (the `ElabSpec` theorems at `elabSpec`); `StoreCorr.ofHonest`, `Simulated.of_honest`; **`Oopsla16.oopsla16_safety`, `oopsla16_not_stuck`**, `oopsla16_safety_honest`, `oopsla16_not_stuck_honest`.  Worked instances `ex0_safe`, `RecursiveArg` (a method demanding `μz.T(z)` applied to a literal typed by two `stp_bindx`; the source run, both headline theorems, and the target run reaching a final state), `HonestCall` (over `TwoObjectStore`). |
| `Deliverables.lean` | **The WadlerFest deliverables that were missing**, each a short corollary, none with a hypothesis.  `reachable_consistent`, `elab_reachable_consistent` (every machine store a typed program reaches is honest and proves no closed `⊤ ≤ ⊥`); `reachable_realized`, `elab_reachable_realized` (stored type members are exactly the recorded ones); `MachineStore.Honest.nf`, `consistent`, `realized`; `Oopsla16.reachable_simulated`, `Oopsla16.reachable_related` (every reachable source configuration is related to a typed, consistent target state that the elaboration reaches); `litStoreTy`, `closedStp_nf`, **`Oopsla16.stp_consistent`** (no source store derives `⊤ <: ⊥`); `Corr.coherent`, `Corr.final_iff`, `elab_coherence`, `elab_final_iff` (coherence as equal answers). |
| `Coverage.lean` | **What the safety theorems reach, and what the location rules trust.**  `VaryWitness`, `HasType.varyWitness` (every source typing of a location contains a `T_Vary` at it), `Store.Honest.varyWitness` and `honestOfVaryWitness` (a store has an honest store typing exactly when every location has a `T_Vary` typing), `noVary_not_admissible` (at a location without one, `loc ℓ ⊤` is typed at every store typing and the source types `ℓ` at nothing); `TmFrag.ofSubst`, `DmFrag.ofSubst`, `DmsFrag.ofSubst` (the fragment is reflected by substitution).  `NonVacuity`: `badTerm_stuck`, `ill_reaches_stuck`, `ill_untypable`, `badTerm_untypable`.  `CurryGap`, over `Admissibility.CurryStore`: `idApp_typed`, `idApp_steps`, `not_frag` (a typed configuration that steps, over an honest store none of whose witnesses is in `DmsFrag`).  `UncheckedBody`, a store holding `{def 0(y : ⊤) : ⊥ = y}`: the instance `annotated`; `appBot_typed` (`ℓ.0(ℓ)` at `⊥` at every store typing), `appBot_erase`; `stuckProg_typed`, `stuckProg_run`, `stuckTm_stuck`; `not_honest` (through `oopsla16_safety_honest`), `loc_untypable`, `app_untypable`. |
| `Checker.lean` | **An executable checker for the five judgments.**  `memberMatchB` (a method member is accepted only against a method stored with both annotations, and only at them), `litMatchB` (structural, through `litMatchBAux` at a variable scope index) with `litMatchB_sound`, `litMatchB_complete`, `litMatchB_iff` and `LitMatch.instSubsingleton`; a local `PartialRename` with `Ty.rename?` (sound and complete for renamings it inverts), `Ty.strengthen?`, `Ty.strengthenW?`; `witness?`; the result structures `LeChecked`, `VcChecked`, `AtomChecked`, `TmChecked`, `DefsChecked`, which carry the derivation; the kernels `synthLeCore`/`synthVcCore` (well-founded on the evidence's size, reduced by the kernel) and `synthAtomCore`, `synthTmCore`/`synthDefsCore` (structural), at every store scope, store, store typing, context and subject; `synthLe`, `checkLe`, `synthVc`, `checkVc`, `synthAtom`, `checkAtom`, `synthTm`, `checkTm`, `synthDefs`, `checkDefs`, each with a soundness function returning the derivation (`synthLe_sound`, `checkLe_sound`, …). |
| `CheckerCompleteness.lean` | **Completeness, and uniqueness of derivations.**  `LeTy.complete`, `VcTy.complete`, `AtomTy.complete`, `TmTy.complete`, `DefsTy.complete`: the kernel returns every derivation itself, `synthLeCore G W Γ e = some ⟨S, T, h⟩`.  Hence `LeTy.unique`, `VcTy.unique`, `AtomTy.unique`, `TmTy.unique`, `DefsTy.unique` and `Subsingleton` instances: each judgment has at most one derivation.  `synth…_complete`, `synth…_iff`, `check…_complete`, `check…_iff` (against `Nonempty`), `check…_eq_false_iff`; `LeTy.endpoints_unique`, `VcTy.type_unique`, `AtomTy.type_unique`, `TmTy.type_unique`, `DefsTy.type_unique`.  No hypothesis and no acceptance predicate. |
| `CheckerExamples.lean` | **The checker run by the kernel** (`decide +kernel`): every derivation of `Oopsla16/Examples.lean`, elaborated and checked at its source type; the reference's `ex1` and `ex2` (`dot_exs.v:180-208`) as `Oopsla16` derivations (`DotExs`), elaborated and checked, `ex1` also through the fragment elaboration with its erasure equation and `ex2` with its correspondence; the reference's `paper_lst` (`dot_exs.v:211-322`, the paper's list module) the same way (`PaperLst`), accepted at the module type through both elaborations and rejected at `⊤`; `FCdotR/Examples.lean` and `TermTyping.FunctionFieldObject`, each accepted and rejected at a wrong type, and the literal at `μz. T(z)`; rejections for packing at an abstract variable (`PackingCounterexample`'s `bad`, `badEv_untypable`), the fold-exposing `μT ≤ T{x}`, an escaping `let`, and non-defining bounds; locations over `TwoObjectStore` (`loc` exact and at `⊤`, rejected at inexact bounds and at an absent method, `selQ` through `vcLocAny`, the lie `lieEv` rejected while the same lie through `vcLoc` over `DishonestStore` is accepted); locations over `Admissibility.CurryStore`, whose method has no annotations (`loc ℓ` rejected at the two method types tried, the type `T_Vary` gives and `{0 : ⊤ → ⊥} ∧ ⊤`, the latter also as an observation; `ℓ.0(ℓ)` at `⊥` rejected, `appBot_untypable`; `loc ℓ` accepted at `⊤`; `var (conc ℓ)` accepted at the type `T_Vary` gives through the honest store typing, and `ℓ.0(ℓ)` through it at `⊤`; at a store typing recording `⊤`, which `wtopCurry_not_honest` shows dishonest, `var (conc ℓ)` rejected at that type and accepted at `⊤`), and over the same method stored with both annotations (accepted at them, rejected at another codomain); stored annotations taken on trust over `Coverage.UncheckedBody.G` (`loc ℓ` accepted at `{0 : ⊤ → ⊥} ∧ ⊤` and `ℓ.0(ℓ)` at `⊥` at two store typings, `appBot_trusted` read off a verdict and equal to `UncheckedBody.appBot_typed`); the elaboration of `qTyped` at the honest and a dishonest store typing; the worked programs `CurryCall`, `RecursiveArg`, `HonestCall` and those of `ElaborationErasure`.  107 verdicts, 64 accepted and 43 rejected, plus 9 derivations read off accepted verdicts (`ex0_typed`, `recursive_checked`, …) and 7 untypability theorems read off rejected ones: 123 declarations decided by `decide +kernel`, 73 accepting and 50 rejecting (counted with comments removed).  The whole file builds in about 5 s; the slowest verdicts, the three on `paper_lst`, take about 0.7 s each in the kernel, and the two on `RecursiveArg` about 0.25 s. |

## WadlerFest deliverables

What the WadlerFest line (`DotToFCdot/README.md`, `FCdot/README.md`) proves,
and its counterpart here.  Names are in namespace `FCdotR` unless they start
with `Oopsla16.`.  **New** marks what `Deliverables.lean` and the checker
(`Checker`, `CheckerCompleteness`, `CheckerExamples`) add.

| WadlerFest | Here |
| --- | --- |
| Typedness: `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translate_typed` | `elabStp`, `elabHtp`, `elabAtom` (`AtomElab.typed`), `elabTm` (`TmElab.typed`), `elabDefs` (`DefsElabC.typed`): the typing is part of the result.  The term elaborations take the hypothesis that the store is annotated (`Store.Annotated`), which the empty store is |
| `HasTy.translateAtom_root` | `AtomElab.root` |
| Erasure equality `HasTy.translate_erase` | Not applicable beyond the fragment: a `let` erases to an object encoding.  `TmElab.corr` (`Corr`) takes its place.  On the fragment: `elabHasType_erase`, `elabDms_erase` |
| `coherence` (equal erasures) | Equal erasures are false (`T_App` and `T_AppVar` bind different operands; a Curry-style method gets the types its typing chose).  **New**: `elab_coherence`, `elab_final_iff` (same answers), from `Corr.coherent`, `Corr.final_iff` |
| `dot_safety` (positive form) | `Oopsla16.oopsla16_not_stuck` |
| `dot_not_stuck` (negative form) | `Oopsla16.oopsla16_safety` |
| `simulated_init`, `Simulated.steps`, `Simulated.progress` | `Simulated.init`, `Simulated.steps`, `Simulated.progress`; **new** `Oopsla16.reachable_simulated`, `Oopsla16.reachable_related` |
| `final_erase`, `final_reflect` | `Rel.final_tm`, `Rel.final`, `Rel.answer_final`, `Rel.answer_iff_final` |
| `reachable_consistent` (`DotMNF`, `FCdot`) | **New**: `reachable_consistent`, `elab_reachable_consistent`, and the last conjunct of `Oopsla16.reachable_related`.  Source side, for every store: **new** `Oopsla16.stp_consistent` |
| `reachable_realized` | **New**: `reachable_realized`, `elab_reachable_realized` (a location stores `a = TX` exactly when its recorded type has `{a : TX..TX}`).  FCdotR has no equality evidence; `defL`/`defR` read the store directly |
| Checker with completeness (`FCdot.checkTm_iff` and friends) | **New**: `checkLe_iff`, `checkVc_iff`, `checkAtom_iff`, `checkTm_iff`, `checkDefs_iff` (against `Nonempty`, the judgments being `Type`-valued), with soundness `check…_sound` and completeness `LeTy.complete` and siblings, which return the derivation itself; derivations are unique (`LeTy.unique`, …) and types are determined by the syntax (`LeTy.endpoints_unique`, …).  The checker decides FCdotR typing of fully annotated terms, not `Oopsla16` typing |
| `preservation` | `preservation'`, `preservation_steps'`, `preservation_init'`, up to evidence; on-the-nose preservation is false (`OnTheNose`) |
| `progress`, `not_stuck` | `progress'`, `not_stuck'`, `safety'` |
| Erasure simulation, target to runtime (`erase_step`) | `Rel.reflect_step`, `Rel.reflect_steps` (each target step is zero or one source step); on the nose only without `let` frames: `Step.simulate`, `Steps.simulate` |
| Erasure simulation, runtime to target (`erase_reflect`) | `sim_step`, `Rel.steps'`, `sim_step_plus`, `sim_stuck` |
| Canonical forms of closed evidence | `Store.Honest.nf`, `RecordedLit.nf`, `Store.Honest.obsTyp`/`obsBind`/`obsFun`, `Store.Honest.canon`, `appInversion`; **new** `MachineStore.Honest.nf`, `closedStp_nf` |
| No closed `⊤ ≤ ⊥`; shapes of closed inclusions | `consistency_honest`, `RecordedLit.consistency`, `LeTy.headPair_of_not_trans`, `top_le_bot_is_trans`; **new** `MachineStore.Honest.consistent` |
| `WadlerFest`, `RetainedSafety`, `SortedSafety` | Not applicable: they cover other presentations of the WadlerFest source (annotated machine, reduction orders, sorted labels).  `Oopsla16` has one machine |
| Examples E1 to E8 decided in the kernel (`FCdot/Examples.lean`), each with an erasure link to its source term | **New**: `CheckerExamples`, decided by `decide +kernel`: the elaborated `Oopsla16` examples, the reference's own `ex1`, `ex2` and `paper_lst` (`dot_exs.v`, as `Oopsla16` derivations in `CheckerExamples.DotExs` and `CheckerExamples.PaperLst`; the fragment elaborations of `ex1` and `paper_lst` erase back to them, `ex2`'s elaboration corresponds to it by `Corr`), the hand-written FCdotR examples, the restrictions as rejections, locations, stored annotations taken on trust, and the worked programs `SourceSafety.RecursiveArg`, `HonestCall`, `ElaborationFull.CurryCall` and those of `ElaborationErasure`.  **Not done**: no `Oopsla16` counterpart of E1 to E8 is written |

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
3. **Preservation** — **done** for the FCdotR machine, up to evidence:
   `preservation'`, `preservation_steps'`.  There is no preservation for the
   `Oopsla16` machine (see *What the headline does not say*).
4. **Progress** — **done**: `progress'`, `not_stuck'`, `safety'`.
5. **Elaboration from `Oopsla16.Stp`/`HasType`** — **done** for every
   typing over an annotated store, so for every typing over the empty store:
   `ElaborationFull.elabTm`/`elabDefs` elaborate general `tapp` by
   A-normalisation and an unannotated `dfun` in the term by `D_Fun`'s types
   (`elabSpec`).  Over a store holding a method without annotations the
   elaboration does not apply: there the location rules give no type `T_Vary`
   gives, and `varConc` gives only the recorded type (see *What remains*).
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
  selection case of it; the translation is not built.  The location rules read
  a stored literal's type members and method annotations (`LitMatch`), and the
  machine store annotates a Curry-style method with the types its honesty
  witness checked, so matching type members alone is not enough.  The
  reference covers such stores; a one-object store with a Curry-style method is
  an example (`Coverage.CurryGap`), and no theorem here derives source safety
  from it.
* **`T_Vary` over a store holding a method without annotations.**  The
  location rules refuse a method member of such a location
  (`LitMatch.no_unannotated_method`), and every `T_Vary` type lists every
  method, so the location rules give no type `T_Vary` gives there
  (`Admissibility.varConcAny_not_vary`, `vcLocAny_not_vary`).  `varConc` still
  types the location at `tyOf W ℓ`, which over an honest `W` is a `T_Vary`
  type (`CurryStore.varConcTyped`), but at no other type.  So the elaboration
  here, which works at every store typing, does not cover such a store, and
  neither do the honest-store theorems (`Admissibility.CurryStore` is one:
  honest, not annotated, and no witness is in `DmsFrag`,
  `Coverage.CurryGap.not_frag`).  That no elaboration at every store typing could
  cover it with the present rules is argued, not proved.  A location rule
  whose premises are `T_Vary`'s own covers it, as up to commit `5324088`, where
  `elabSpecGen` needed no store hypothesis, but checking that premise means
  deciding `Oopsla16` typing, which is what the location rules were changed to
  avoid.
* **Source admissibility of the rest of the target.**  Over an honest store,
  the location rules and `refl`/`muDrop` are admissible in the source
  (`Admissibility`).  `selL`/`selR` at a location, and observations built on a
  location node by `vcPack`, `vcUnfold` and `vcSub`, are not translated back
  into `Stp`/`HasType`; `obs_conc_admissible` gives their bounds only as
  target inclusions.  The README's *Where FCdotR is not a rule-for-rule image
  of `Oopsla16`* lists every such rule with its status.
* **Preservation for the source.**  No theorem says a reached `Oopsla16` term
  has the program's type.  Either a direct proof in the source, as the
  reference gives, or the translation of target typing back into source typing
  from the item above would supply it.
* No determinism theorem for either machine (the simulation uses only
  `ECtx.plug_inv`, determinism at a focused redex), and no statement about
  divergence (`sim_step_plus` is the piece it would use).
* **Examples.**  The reference's `dot_exs.v` is ported in full (`ex0` in
  `Oopsla16/Examples.lean`; `ex1`, `ex2` and `paper_lst` in `CheckerExamples`),
  but no `Oopsla16` counterpart of the WadlerFest examples E1 to E8
  (`FCdot/Examples.lean`) is written.

## Adversarial review

Run at integration, against the working tree with `Deliverables.lean`.  Its
probe files were scratch files outside the repository, so what rests on them
alone cannot be reproduced from the repository; each compiled with `propext`
and `Quot.sound` only.  Two of them have since become part of the library:
the non-vacuity checks (`Coverage.NonVacuity`) and the Curry-style store that
no safety theorem covers (`Coverage.CurryGap`).

* **The calculus matches `dot.v:197-393` rule by rule, up to the documented
  deviations: ARGUED.**  Every rule of `HasType` (8), `DmsHasType` (3),
  `Stp` (18), `Htp` (3) and `Step` (4) was printed and compared with the Coq
  rule; each matches once the documented scoping changes are applied.  The
  comparison is by reading, not a proof: the two definitions live in
  different proof assistants.  The indexing supplies each dropped `closed`
  premise, as well-scopedness, as an explicit weakening or as the prefix
  indexing of `Ctx` (`Oopsla16/README.md`, *Design*).  For contexts, stores
  and syntax it imposes a stronger condition than the reference does
  (`Oopsla16/README.md`, *Deviations from `dot.v`*, items 8-10): a `Ctx`
  entry may mention only its own variable and older ones, where `T_Varz`
  needs only `closed (length GH) (length G1) 0 T` (`dot.v:229`); a stored
  object has every variable in range, where `venv` constrains nothing; and a
  term or type with an out-of-range variable cannot be written, where Coq's
  `step` also reduces some configurations that contain one.  Apart from these
  restrictions the comparison found no typing rule tighter than the Coq one
  and no reduction rule looser.  Coq's `subst` and the Lean single-binder
  substitution agree at the top level, where the machine runs, so `ST_Obj`
  and `ST_AppAbs` agree.  That too is argued, not proved.  For the step
  relation it was also tested, which is not a proof either: both step
  relations, transcribed to Python, agree at every step of 160,000 random
  configurations (`coq/oopsla16-deviations/step_differential.py`, seeds 0 to
  7; `Oopsla16/README.md`, *Deviations from `dot.v`*, item 6).
* **Nothing changed underneath the headline.**  The definitions in
  `Oopsla16/Typing.lean`, `Semantics.lean` and `Syntax.lean` are unchanged
  since commit `08b8a75`; only comments were edited since, in `Typing.lean`
  and `Syntax.lean`.  (Checked by comparing the files with comments removed;
  the fingerprint of *Reproducing the checks* covers every `Oopsla16`
  constant from `aa7ca71` on.)  `Context.lean` changed afterwards: `scopeUpTo` and
  `varUpTo` were redefined in `5823790`, and a scratch proof, not part of the
  repository, shows the old and new definitions give the same scope, the same
  variable and the same weakening.  Every other change to `Oopsla16/` since
  `08b8a75` adds definitions or lemmas without changing an existing
  definition (`tailBelow`, `scopeUpTo_varUpTo` and `Vr.rename` in `5823790`,
  `Ctx.renameStore` and `Ctx.weakenStore` in `27985ea`, the module
  `SubstLemmas`, which `Oopsla16.lean` now imports) or edits only comments and
  documentation.  The headline refers only to `HasType`, `Steps`, `Step`,
  `Tm.IsAnswer` and `FCdotR.SrcStuck`, whose body uses only `Tm.IsAnswer` and
  `Step`, and no automatic implicit variable entered its statement.
* **Not vacuous, and it rules programs out.**  `caller2.0(ff)`, a new program
  whose method has no type annotations and whose argument is typed through two
  uses of `stp_bindx`, is typed at `⊤` and runs four steps (two allocations, two
  method calls) to an answer; `oopsla16_not_stuck` produces a step at its third
  configuration.  An object with a type member at label 0, called at that
  label, gets stuck after three steps, and `(new{}).0(new{})` gets stuck too, so
  the theorem refutes every typing of either program.  These were scratch
  probes; the library now proves the last one (`Coverage.NonVacuity.ill_untypable`),
  and `SourceSafety.RecursiveArg` is a program of the first kind.
* **Limits, not defects**: no preservation for the source, and the run starts
  from the empty store; see *What the headline does not say*.
* **Stale documents**, now corrected: `Oopsla16/README.md` said no soundness
  proof existed, and the top-level `README.md` said `Oopsla16` had no
  metatheory and its target was still being designed.
* No `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`
  or debugging option in `FCdotR/` or `Oopsla16/`.  (The two scripts of
  `FCdotR/audit/`, which no library builds, print their reports with
  `#eval`.)

## Reproducing the checks

From the repository root, after `lake build FCdot DotMNF DotToFCdot Oopsla16
FCdotR`:

* `lake env lean lean/Coercions/FCdotR/audit/AxiomAudit.lean` prints
  `checked 7565 constants; offending: 0` (the axiom audit above).  It lists
  every constant of `FCdotR` and `Oopsla16` that uses an axiom other than
  `propext` and `Quot.sound`, `sorryAx` included.
* `lake env lean lean/Coercions/FCdotR/audit/Oopsla16Fingerprint.lean` prints a
  row for every constant of `Oopsla16` (name, kind, hash of the type, hash of
  the value of a definition), then `total 1015` and
  `digest 1836387099973842417`.  The same two lines come out on clean exports
  of `aa7ca71`, `4312920` and `d3fd166`, and on this change, so no statement,
  rule, type or definition of `Oopsla16` has changed since `aa7ca71`.  The
  fingerprint does not hash proofs of theorems; comparing the `Oopsla16`
  sources with their comments removed shows that nothing but comments has
  changed since `aa7ca71` either.
* `COQC=/path/to/coqc coq/oopsla16-deviations/build.sh` builds the Coq proofs
  about the reference's own rules and runs their block check; the step
  relation's differential test is `coq/oopsla16-deviations/step_differential.py`
  (its README says how to run it).
* A job count is only a count of the commit when the build runs on a clean
  export (`git archive <commit> lean lean-toolchain lakefile.toml
  lake-manifest.json`), since `lake build FCdot DotToFCdot` also builds any
  module the working tree's `FCdot.lean` and `DotToFCdot.lean` import.

Not reproducible from the repository: the probes of the *Adversarial review*
that are not in `Coverage`, the audit probe that typed `ℓ.0(ℓ)` at `⊥` at
commit `4312920`, and the scratch proof about `scopeUpTo`/`varUpTo`.  Each is
marked where it is cited.

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
  (`LocBase.toLocType` bridges them); `FCdotR.Ctx.renameStore` in
  `StoreTyping.lean` still shadows `Oopsla16.Ctx.renameStore`.
  `Preservation`'s `TmTy.Core`, `TmTy.core` and `Tm.skel_eq_*` compile but
  are unused.  `ElaborationFull.oopsla16_safety'` and
  `Oopsla16.oopsla16_safety`, and `ElaborationFull.oopsla16_progress` and
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
