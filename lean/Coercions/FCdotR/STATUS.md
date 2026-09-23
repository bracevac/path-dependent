# FCdotR — status

State of the `Coercions.FCdotR` library as integrated on branch
`fcdot-recursive-subtyping`.  FCdotR is the explicit-evidence **target** for
the `Coercions.Oopsla16` source (Rompf–Amin OOPSLA'16 DOT, which has
recursive subtyping).  It is a *second* target: the WadlerFest→FCdot chain in
`DotMNF`/`DotToFCdot`/`FCdot` is not reused, only imitated.

`lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR` completes in **110 jobs**.
No `sorry`, `admit`, `axiom`, `native_decide` or `partial` anywhere in
`FCdotR/` or `Oopsla16/` outside doc comments.  Every result named below
depends on at most `propext` and `Quot.sound`.

Two results are stated with an **unproved hypothesis**, taken as an explicit
argument and named in the declaration's doc comment.  Nothing inhabits either
except at the empty store.  A third, `VaryEv`, has been **removed**:

| Hypothesis | Where | What it says | Free at |
| --- | --- | --- | --- |
| ~~`VaryEv`~~ — **removed** | `Elaboration.lean` (deleted) | at every location, the recorded type is included in whatever type a source `T_Vary` derived there | — |
| `Contract` | `Normalizer.lean` | an unfolding-over-packing redex can be contracted without growing the spine pack count | nothing |
| `BoundsVacuous` | `CanonicalForms.lean` | the bounds a closed observation of a location reports are sound for `Vacuous` | empty store (`boundsVacuous_nil`) |

`VaryEv` was removed rather than proved because it is false in general — a
stored literal has no principal type, so two `T_Vary` derivations at one
location can give incomparable types — and the target now has `T_Vary`
verbatim (`VcTy.vcLocAny`, `AtomTy.varConcAny`), which the elaboration uses
directly.

`LemmaR`, the hypothesis the substitution theorem used to carry, is **gone**:
`lemmaR` inhabits it outright.

## Modules

| Module | What it establishes |
| --- | --- |
| `PLAN.md` | The design: substitution via prefix restriction, the elaboration of 32 source rules, the metatheory order, and the open questions.  Not code. |
| `Prefix.lean` | The prefix apparatus at a two-zone variable: `scopeAt`, `renameAt`, `selfAt`, `ctxAt`, `Zone`, the `upTo`/`renameUpTo` transport laws, and `renameUpTo_comp` (weakenings out of iterated prefixes compose) with its transport helpers. |
| `Syntax.lean` | The five grammars — inclusion evidence `Le`, observation evidence `Vc` (indexed at its subject's prefix scope), `Atom`, `Tm`, `Defs` — plus `Atom.root` and `Defs.length`.  A location has two `Vc` nodes: `vcLoc ℓ`, and `vcLocAny ℓ T ds`, which carries a `T_Vary` witness's self type and literal as syntax. |
| `Typing.lean` | `StoreTy`/`tyOf` and the two evidence judgments `LeTy` (inclusion) and `VcTy` (observation).  `VcTy` has two location rules: `vcLoc` at the recorded type `tyOf W ℓ`, and `vcLocAny`, the source's `T_Vary` verbatim (its two premises, concluding at `T.substVr (conc ℓ)`).  No term typing here. |
| `Structural.lean` | `MonoAt`/`Mono`: a substitution carrying a per-variable image and restriction satisfying the star law.  Its closing note records that `Mono` is not closed under restriction; `Subst.lean`'s `MonoSyn` is the answer, and `MonoSyn.toMono` embeds it. |
| `Locality.lean` | Lemma 0, the locality of observation evidence: `VcTy.strengthen` and `VcTy.ofLoc`. |
| `Examples.lean` | The `FunctionField` example elaborated by hand: a closed `bindx` derivation whose method body uses a `selL` under the enclosing self — the judgment `DotToFCdot/RecursiveSubtypingSeparation` shows current FCdot cannot express. |
| `Subst.lean` | `MonoSyn`, the inductive syntax of generated substitutions, closed under restriction (`resSyn`).  The substitution action on all five sorts, the star laws, `toMono`, `restrict_unique`, and the image/restriction laws for iterated prefixes (`restrict_abs_rename`, `image_restrict`, `scopeAt_image_restrict`). |
| `SubstTyping.lean` | Imports `StoreTyping` for the `vcLocAny` clause.  `MonoSyn.Ev` with `refl`/`lift`/`atNil`; `VcTy.toFull`/`weakenVar`/`strengthenCons`; `MonoSyn.restrict_coh` (coherence of iterated restriction, via `restrict_unique`); `VcTy.descendAbs`/`descend` (iterated strengthening); `lemmaRVc`/`lemmaR`; and the **unconditional** substitution theorem `LeTy.substEv`/`VcTy.substEv`, one premise, `MonoSyn.Ev`. |
| `TermSubst.lean` | `MonoSyn.Ev.weaken`; `MonoSyn.EvA` (`Ev` plus an atom at each abstract variable, which `Vc` cannot supply because it has no `pack` at an abstract subject) with `refl`/`weaken`/`lift`; `AtomTy.weakenVar`; and the substitution theorem for the three term judgments, `AtomTy.substEv`/`TmTy.substEv`/`DefsTy.substEv`, recording the atom's root and the defs' length because the conclusions mention them. |
| `StoreTyping.lean` | `Conjunct` and `DmsHasType.conjunct`; `Store.Honest`, the invariant that every location holds a literal typed at its store type; `Honest.vary`, `Honest.member`, `Honest.obs`, `Honest.alloc`.  `varyMember`/`varyObs`: the same facts for a bare `T_Vary` witness, with no store invariant (`Honest.member` is now `varyMember` at the honesty witness).  `Store.Honest.vcLoc_of_vcLocAny`: over an honest store `vcLoc` is `vcLocAny` at `W ℓ`.  Store renaming for all four source judgments, and a substitution's store part as a store renaming (`storeRen`, `StoreMap.ofSubst`, `varyTyped`/`varyStored`/`varyTy`), which moves a `T_Vary` witness along a substitution.  `TwoObjectStore`. |
| `TermTyping.lean` | The three term judgments `AtomTy` (6 rules), `TmTy` (5), `DefsTy` (3).  `AtomTy` has two location rules: `varConc` at the recorded type, and `varConcAny`, `T_Vary` verbatim.  `TmTy.appWeaken`, `AtomTy.toVc` (`varConcAny` goes to `vcLocAny`), `Store.Honest.varConc_of_varConcAny`; `FunctionFieldObject`. |
| `Machine.lean` | The runtime: `Inst` and its action on all five sorts, `MachineStore`, `Frame`/`Cont`/`State`, `Step`/`Steps` indexed by `Oopsla16.Grows`, six rules.  Plus `MonoSyn.ofInst`, the bridge that makes `Inst` a `MonoSyn` at the typing level. |
| `Erasure.lean` | `Tm.erase`/`Defs.erase`/`MachineStore.erase` into `Oopsla16`, the commutation laws with instantiation, generated substitution (`erase_subst`) and store renaming, the agreement `erase_inst_subst`, and `Step.simulate`/`Steps.simulate`.  `Counterexample.badRun`. |
| `Forms.lean` | Measures `Le.size`, `Le.packs`/`Vc.packs`, and `Vc.spinePacks` (packs on the spine over one subject, not descending into a `vcSub`'s inclusions); head shapes `TyHead`/`headOf` and `HeadPair`; `Vc.InNf`, `Vc.pushSub`, `Vc.RedexFree`, `Vc.exposesPack`, `Vc.base`. |
| `Normalizer.lean` | `VcTy.toNf`: spine normalization, structural, typed, no fuel, no hypothesis.  `VcTy.unfoldStep` and `VcTy.canon`: redex elimination, terminating on `(spinePacks, size)` lexicographically — which **settles `PLAN.md` §I's open question affirmatively**.  `canon` takes `Contract`. |
| `CanonicalForms.lean` | Unconditional: `no_pack_at_abs`, `LeTy.headPair_of_not_trans` (the head table), `typ_le_bind_is_trans`, `top_le_bot_is_trans`, `VcTy.base_conc` (now: the foot is `vcLoc ℓ` or some `vcLocAny ℓ T ds`), `dmsHasType_head`, `Store.Honest.head_tyOf`, `Store.Honest.not_vacuous`, `VcTy.vcLocAny_head`, `VcTy.vcLocAny_not_vacuous`, `obs_conc_easy`, `Store.Honest.defL_as_selL`.  `Vacuous` and `LeTy.vacuousMono` (16 of 18 rules with no hypothesis); `consistency` under `BoundsVacuous`, `consistency_nil` unconditionally.  `DishonestStore.topLeBot`: `LeTy` alone *is* inconsistent, so the store hypothesis does real work. |
| `Elaboration.lean` | `elabStp`/`elabHtp`: **all 18 `Stp` rules and all 3 `Htp` rules**, at an arbitrary `StoreTy`, no honesty and no hypothesis of any kind.  `elabAtom`/`elabHasType`/`elabDms` on the fragment `TmFrag`/`DmsFrag` (variable operands at every `tapp`, both annotations on every `dfun`), likewise at an arbitrary `StoreTy` and with **no hypothesis**: `T_Vary` becomes `AtomTy.varConcAny`.  `elab_recursive`: the elaboration of the source derivation *is* `Examples.recursive`, by `rfl`. |
| `ElaborationErasure.lean` | `elabHasType_erase`/`elabDms_erase`: the elaborated term erases to the source term, on the nose, at every store typing.  Four worked instances, one of them a `T_Vary` over the two-object store at a store typing (`Wtop`) that disagrees with the source. |

## Road to a WadlerFest-style safety theorem

In dependency order.

1. **Substitution theorem** — **done.**  `LeTy.substEv`/`VcTy.substEv` discharge
   every clause of both evidence judgments with `MonoSyn.Ev` as their only
   premise, and `MonoSyn.Ev.refl` inhabits that premise, so the theorem is not
   vacuous.  The former hypothesis `LemmaR` is discharged by `lemmaR`, which
   splits into the coherence of iterated restriction (`MonoSyn.restrict_coh`,
   via `restrict_unique`, with no induction over `MonoSyn` generators) and
   iterated strengthening (`VcTy.descendAbs`).  `TermSubst.lean` adds the same
   theorem for `AtomTy`/`TmTy`/`DefsTy` under `MonoSyn.EvA`.
2. **Canonical forms** — *partial.*  The observation half is built:
   `VcTy.toNf` normalizes the `vcSub` spine unconditionally, and `VcTy.canon`
   eliminates redexes with a proved termination measure.  The remaining
   content is **transitivity elimination for closed `LeTy`**: inverting a
   closed `T1 ≤ {a : S..U}` or `μT ≤ μT'` to the rule that introduced the
   member.  That single missing inversion is what blocks `Contract` (which
   also needs `LeTy.substEv` — now available) and `BoundsVacuous` alike, which
   is why the two hypotheses are not independent of each other.  The
   unconditional pieces listed in the module table are done.
3. **Preservation** — *not started.*  Blocked on 2, not on 1 any more.  Two
   obstacles are already visible: `Machine.lean`'s `rename` and `app` rules
   substitute an atom's *root* and drop its coercions, which is sound at
   runtime but not type-preserving (`FCdot.Machine` keeps them via
   `Tm.adjust`); and `Store.Honest` is an invariant of an `Oopsla16.Store`,
   whereas preservation needs honesty of `MachineStore` or of its erasure.
4. **Progress** — *not started.*  Blocked on 2.
5. **Elaboration from `Oopsla16.Stp`/`HasType`** — *partial.*  The subtyping
   and observation half is **complete and unconditional**: `elabStp`/`elabHtp`
   cover all 18 + 3 rules at an arbitrary `StoreTy`, with no store invariant,
   and every scope coincidence they need is definitional.  The term half
   covers the fragment `TmFrag`/`DmsFrag` and is now **unconditional** as
   well: `T_Vary` elaborates to `AtomTy.varConcAny`, the source rule verbatim,
   so the former hypothesis `VaryEv` is gone.  What remains: general `tapp`
   (needs let-normalisation and its operational correspondence) and unannotated
   `dfun` (typing already works; only the on-the-nose erasure fails).  The cost
   of the change moves to the metatheory: preservation and canonical forms must
   now treat `vcLocAny`/`varConcAny` as a second base case.  The consistency
   argument only needs type members to be exact `TX..TX`, which `D_Typ` gives
   whatever type a witness picks (`varyMember`), and the substitution theorems
   already cover both rules.
6. **Erasure equality** — *partial.*  Two halves, in different states.  The
   elaboration half is done on the fragment (`elabHasType_erase`).  The machine
   half, `Step.simulate`/`Steps.simulate`, holds only under `Cont.Evidential`
   and on the let-free fragment; the gap is structural, since `let` erases by
   an object encoding, so the step consuming a `let` frame erases to a
   configuration whose store has been extended.  Closing it means a source-side
   `let` or a simulation up to store extension.
7. **Safety transport** — *not started.*  The `DotToFCdot/Safety.lean` shape
   (`Simulated`, `final_erase`/`final_reflect`, `dot_safety`,
   `dot_not_stuck`) needs 3, 4, 5 and 6.

## Integration notes

* **The `Store` clash is resolved.**  `Machine.lean`'s target store is now
  `FCdotR.MachineStore`, so bare `Store` unambiguously means `Oopsla16.Store`
  everywhere in `FCdotR`.  The old hazard — the enclosing namespace silently
  beating an `open Oopsla16 (Store)` with no ambiguity error — is gone, and a
  preservation module can hold both stores at once.
* **`Inst` is a `MonoSyn` at the typing level, but they are still two
  functions.**  `MonoSyn.ofInst` bridges them and `Machine.lean` now imports
  `Subst.lean`, so everything typing-level goes through `MonoSyn`.  The two
  *syntactic actions* genuinely differ and are both kept: `Vc.inst` sends
  `vcVar` at the instantiated binder to `vcLoc`, where `Vc.subst` keeps
  `vcVar`; and `Le.inst` leaves a `defL`/`defR`'s sub-evidence alone where
  `Le.subst` re-traverses it through `atNil`.  So `Le.inst e ι y = e.subst
  (MonoSyn.ofInst ι y)` is false as stated, and collapsing them would change
  the machine's evidence.  What `Erasure` actually needs is proved instead:
  `Tm.erase_inst_subst`, the two actions erase to the same source term.
* **`Ctx.renameStore` is defined twice.**  `Oopsla16.Ctx.renameStore` /
  `Ctx.weakenStore` now exist in `Oopsla16/Context.lean` where they belong,
  but `FCdotR.Ctx.renameStore` in `StoreTyping.lean` still shadows them inside
  `namespace FCdotR`.  Nothing is ambiguous and nothing broke; the `FCdotR`
  copy and its three lemmas should eventually move or be deleted in favour of
  the `Oopsla16` one.
* **Two doc comments were corrected during integration**, because they asserted
  something that had since become false: `Normalizer.lean`'s `Contract` and
  `Elaboration.lean`'s `VaryEv` both said the substitution theorem was
  conditional on an uninhabited `LemmaR`.  It is not, and both now say what is
  actually missing.  (`VaryEv` has since been removed altogether; see the
  hypothesis table.)
* `Oopsla16/SubstLemmas.lean` carries `@[simp]` lemmas that change the global
  simp set for everything downstream.  All five libraries were rebuilt;
  nothing regressed.
