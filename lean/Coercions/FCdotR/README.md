# FCdotR

FCdotR is the explicit-evidence target for [`../Oopsla16`](../Oopsla16/README.md),
the Rompf--Amin OOPSLA 2016 calculus with recursive subtyping.  Its types,
contexts and stores are `Oopsla16`'s, unchanged, so the type translation is the
identity.  What changes is that every use of subtyping, and every variable
typing that a type selection relies on, is a proof term (*evidence*) that the
machine carries and never inspects.  Every source typing derivation over a
store whose stored methods are annotated, the empty store included, elaborates
into a typed FCdotR term, the FCdotR machine is proved safe, and a
correspondence between the two machines carries that safety back to
`Oopsla16`'s own substitution machine.  This is the second line of the
development.  It follows the structure of the WadlerFest line (`../DotMNF` →
`../DotToFCdot` → `../FCdot`) without reusing its code, and shares only
`FCdot/Debruijn.lean` with it.  [`STATUS.md`](STATUS.md) has the full
inventory, a result-by-result comparison with the WadlerFest line, and the
open items.

## Modules

In reading order; each module imports only the FCdotR modules above it.

| module | contents |
|---|---|
| `Prefix` | the prefix at a variable of either zone: `scopeAt` (with `scopeAt (conc ℓ) = []`), `renameAt`, `selfAt`, `ctxAt`, and their transport laws |
| `Syntax` | inclusion evidence `Le` (the image of `Stp`), observation evidence `Vc` (the image of `Htp`, scoped at its subject's prefix), atoms (with `loc ℓ T`, a location at a carried self type), terms with `let`, definition lists; `Atom.root` |
| `Typing` | the store typing `StoreTy`/`tyOf`; `LitMatch`, a decidable match of a type against a stored literal (type members exact, method members at a stored method's two annotations); the evidence judgments `LeTy` and `VcTy`; two location rules, `vcLoc` (the recorded type) and `vcLocAny` (a carried self type matching the stored literal, which is not `T_Vary`) |
| `Locality` | an observation depends only on its subject's prefix: `VcTy.strengthen`, `VcTy.ofLoc` |
| `Examples` | `FunctionField` as closed evidence (`recursive_typed`); that FCdot cannot express its WadlerFest counterpart is proved only in uncommitted work (*References to uncommitted work*, below) |
| `Structural` | `Mono`, substitutions that respect prefixes, as a record |
| `Subst` | `MonoSyn`, the inductive syntax of the substitutions the metatheory performs, closed under restriction; its action on all five sorts |
| `StoreTyping` | `Store.Honest` (every location holds a literal typed at its recorded type); `Dms.Annotated`, `Store.Annotated` (every stored method carries both annotations); `varyLitMatch` and its converse `varyLitMatch_annotated` (a `T_Vary` premise pair gives `LitMatch` exactly at an annotated location); `LitMatch.no_unannotated_method`; `Store.Honest.member`/`method`; store renaming for the source judgments; `TwoObjectStore` |
| `SubstTyping` | `MonoSyn.Ev`, `lemmaR`, and the substitution theorem for evidence, `LeTy.substEv`/`VcTy.substEv`, with no side condition |
| `TermTyping` | `AtomTy`, `TmTy`, `DefsTy`: the source's term rules one for one except at a location, with subsumption as a syntax node and application on atoms |
| `Admissibility` | over an honest store the location rules derive nothing the source cannot: `Store.Honest.litMatch_stp`, `litMatch_hasType`, `varConcAny_admissible`, `vcLocAny_admissible`; at an unannotated location they give no `T_Vary` type: `varConcAny_not_vary`, `vcLocAny_not_vary`; `muDrop_admissible`; `CurryStore`, an honest store holding a method without annotations |
| `TermSubst` | the substitution theorem for atoms, terms and definition lists |
| `Machine` | the store-and-continuation machine, six rules, indexed by `Oopsla16.Grows`; `State.Final`, `State.Stuck` |
| `Erasure` | erasure into `Oopsla16` terms, with `let` as an object encoding; the evidence skeleton `Tm.skel`; the simulation without `let` frames, `Step.simulate` |
| `Forms` | sizes and pack counts (`Vc.spinePacks`, `Le.PackBound`, `Le.Strong`), head shapes, normal forms `LeNf` |
| `Normalizer` | spine normalization `VcTy.toNf`; redex elimination `VcTy.canon`, under `Contract` |
| `CanonicalForms` | `no_pack_at_abs`, the head table `LeTy.headPair_of_not_trans`, `top_le_bot_is_trans`; `DishonestStore.topLeBot` (a store typing that lies proves `⊤ ≤ ⊥`) |
| `Inversion` | transitivity elimination for closed inclusions over an honest store: `LeTy.pushback`, `SLe.nf`, the pack-count tower `ObsInv`; `Store.Honest.nf`, `consistency_honest`, `Store.Honest.obsTyp`/`obsBind`/`obsFun` |
| `Elaboration` | `elabStp`, `elabHtp`: all 18 + 3 rules at any store typing; `elabHasType` on the fragment `TmFrag` (variable operands, annotated methods), over an annotated store; `Store.Honest.annotated` |
| `ElaborationErasure` | on the fragment, the elaboration erases to the source term exactly |
| `Preservation` | `StateTy` (typing up to evidence), `MachineStore.Honest`, the six step cases, `OnTheNose` (exact typing fails) |
| `Progress` | `progress`, `not_stuck`, `safety`, under `AppInversion` |
| `MethodInversion` | `appInversion`; the hypothesis-free `preservation'`, `progress'`, `not_stuck'`, `safety'` |
| `Correspondence` | the relation `Corr`/`Rel` between source configurations and target states; the forward simulation `sim_step`, `sim_stuck`; `transport` |
| `ElaborationFull` | `elabTm`, `elabDefs` for every source typing over an annotated store (general application through `let`, unannotated methods in the term at `D_Fun`'s types); `elabSpecGen`, `elabSpec` |
| `Simulation` | the backward simulation `Rel.reflect_step`; answers and stuck states agree across `Rel`; the invariant `Simulated` |
| `SourceSafety` | **`Oopsla16.oopsla16_safety`, `Oopsla16.oopsla16_not_stuck`**, and the honest-store versions; worked instances `ex0_safe`, `RecursiveArg`, `HonestCall` |
| `Deliverables` | the remaining WadlerFest counterparts: consistency and recorded type members along runs, `Oopsla16.reachable_related`, `Oopsla16.stp_consistent`, coherence as equal answers |
| `Coverage` | what the safety theorems reach: `NonVacuity` (they refute typings of programs that get stuck); `CurryGap` (a typed configuration over a store with a Curry-style method that no Lean safety theorem covers); `UncheckedBody` (the location rules trust stored annotations: over the annotated store holding `{def 0(y : ⊤) : ⊥ = y}`, which has no honest store typing, the target types `ℓ.0(ℓ)` at `⊥` at every `W`, and `Oopsla16` types it at nothing); `noVary_not_admissible` (without a `T_Vary` typing at a location, the location rules are not admissible there); `HasType.varyWitness`, `DmsFrag.ofSubst` |
| `Checker` | an executable checker for the five judgments: `litMatchB` decides `LitMatch`; `Ty.strengthen?` strengthens a type by a partial renaming; the kernels `synthLeCore`, `synthVcCore`, `synthAtomCore`, `synthTmCore`, `synthDefsCore` return the derivation they validate; `synth…`/`check…` with their soundness |
| `CheckerCompleteness` | the kernels return every derivation (`LeTy.complete`, …), so each judgment has at most one (`LeTy.unique`, …); the decision procedures `checkLe_iff`, `checkVc_iff`, `checkAtom_iff`, `checkTm_iff`, `checkDefs_iff`; types determined by the syntax |
| `CheckerExamples` | the checker run by the kernel: the elaborated `Oopsla16` examples and the reference's `ex1`, `ex2` and `paper_lst` (`dot_exs.v`), the hand-written FCdotR examples, the calculus's restrictions as rejections, locations over `TwoObjectStore`, locations whose stored method has no annotations, stored annotations taken on trust, the worked programs |

`PLAN.md` is the design the library was built from; `STATUS.md` is its
current state.

## Main theorems

Names are in namespace `FCdotR` unless they start with `Oopsla16.`.

```
Oopsla16.oopsla16_safety    : HasType Store.nil Ctx.nil t T → Steps g Store.nil t G' t' →
                                ¬ SrcStuck G' t'
Oopsla16.oopsla16_not_stuck : HasType Store.nil Ctx.nil t T → Steps g Store.nil t G' t' →
                                t'.IsAnswer ∨ ∃ σ' g' G'' t'', Step g' G' t' G'' t''
```

`SrcStuck G t` is `¬ t.IsAnswer ∧ ¬ ∃ σ' g G' t', Step g G t G' t'`.  It is a
definition in namespace `FCdotR` (`Correspondence.SrcStuck`), and its body uses
only `Oopsla16`'s `IsAnswer` and `Step`.  Apart from it, both statements use
only `Oopsla16`'s `HasType`, `Steps`, `Step` and `IsAnswer`.

* `Oopsla16.oopsla16_safety`: a closed program typed over the empty store
  never reaches a configuration that is neither an answer nor able to step.
* `Oopsla16.oopsla16_not_stuck`: the same, stated positively: every
  configuration it reaches is an answer or takes a step.
* `Oopsla16.oopsla16_safety_honest`, `Oopsla16.oopsla16_not_stuck_honest`: the
  same from a nonempty store, provided each stored object was typed from a
  literal in the fragment `DmsFrag`.  That proviso is an explicit hypothesis,
  `hf`, next to the honest store `h`; neither is an unproved proposition.
* `Oopsla16.stp_consistent`: no store, reachable or not, lets source
  subtyping derive `⊤ <: ⊥` in the empty context.
* `Oopsla16.reachable_related`: every configuration a typed program reaches is
  matched by a typed target state, with a consistent store, that the elaborated
  program reaches at the same allocation index.
* `elabStp`, `elabHtp`, `elabTm`, `elabDefs`: every source subtyping and
  variable-observation derivation becomes target evidence, and every term or
  definition-list typing over an annotated store becomes a target term or
  definition list; the typing is part of the result.  The term elaborations'
  one hypothesis, `Store.Annotated G`, says every method the store holds
  carries both annotations.  The empty store has it.
* `elabSpec`: every closed source typing elaborates to a typed target program
  whose start state corresponds to the source program.
* `Store.Honest.litMatch_stp`, `Store.Honest.litMatch_hasType`: over an honest
  store, a type at which the location rules observe `ℓ` is a source supertype
  of `ℓ`'s recorded type, and `Oopsla16` types `ℓ` at it.  So the location
  rules derive nothing the source cannot (`varConcAny_admissible`,
  `vcLocAny_admissible`).
* `varyLitMatch`, `varyLitMatch_annotated`: a pair of `T_Vary` premises gives
  the location rules' premise exactly when the stored literal is annotated.
  So at a location holding a method without both annotations the location
  rules give no type `T_Vary` gives (`varConcAny_not_vary`,
  `vcLocAny_not_vary`).
* `Coverage.UncheckedBody.appBot_typed`, `app_untypable`: the location rules
  take a stored method's annotations on trust.  Over the annotated store
  holding `{def 0(y : ⊤) : ⊥ = y}`, the target types `ℓ.0(ℓ)` at `⊥` at every
  store typing, and `Oopsla16` types it at no type; that store has no honest
  store typing (`not_honest`).  So the admissibility above needs honesty,
  although the location rules do not read `W`.
* `Coverage.NonVacuity.ill_untypable`, `badTerm_untypable`: two programs that
  get stuck, one from the empty store and one from an honest store, whose
  every `Oopsla16` typing the safety theorems refute.
* `safety'`, `progress'`, `preservation'`: a closed typed FCdotR program never
  gets stuck; a typed state over an honest store is final or can step; a step
  keeps a state typed, up to evidence.
* `sim_step`, `sim_stuck`, `Rel.reflect_step`: each source step is matched by
  a target run, a stuck source configuration makes the target run into a stuck
  state, and each target step is matched by at most one source step.
* `Store.Honest.nf`, `consistency_honest`: over an honest store every closed
  inclusion has a normal form without transitivity, and none proves `⊤ ≤ ⊥`.
* `reachable_consistent`, `reachable_realized`: every store a closed typed
  FCdotR program reaches is honest, proves no `⊤ ≤ ⊥`, and records its type
  members exactly.
* `elab_coherence`, `elab_final_iff`: two elaborations of one source term
  reach a final state together, with the same answer location.
* `checkLe_iff`, `checkVc_iff`, `checkAtom_iff`, `checkTm_iff`,
  `checkDefs_iff`: the checker decides each typing judgment of FCdotR, for
  example `checkTm G W Γ t T = true ↔ Nonempty (TmTy G W Γ t T)`.
  `LeTy.complete` and its siblings say the kernel returns every derivation, so
  each judgment has at most one (`LeTy.unique`, …).  `CheckerExamples` runs the
  checker in the kernel.

Axioms: `propext` and `Quot.sound` for every constant of `FCdotR` and
`Oopsla16`.  The audit `audit/AxiomAudit.lean`, which no library builds, checks
all 7565 of them (`STATUS.md`, *Reproducing the checks*); `audit/` also holds
a fingerprint of `Oopsla16`'s constants.  No `sorry`, `axiom`, `admit`,
`partial` or `native_decide`.

## Design

* **Observation evidence is scoped at its subject's prefix.**  An observation
  `Vc` is evidence that a variable or a location has a type, and a type
  selection `p.A` inside subtyping reads its bounds from one.  Its type lives in
  the scope that existed when the subject was introduced; for a location that
  is the empty local scope.  So the source's restriction on `htp_sub`, which
  forbids using hypotheses introduced after the variable, is the type of the
  judgment, and one rule covers both kinds of subject, which is what lets
  substitution replace a variable by a location without changing the rule.
* **Packing only at locations.**  The observation rule `vcPack` folds a
  subject's type into a recursive type, and its subject index is a location, so
  no rule types it at an abstract variable (`no_pack_at_abs`).  That is the
  source's own restriction: `Oopsla16/PackingCounterexample` shows that
  allowing it at an abstract variable produces a well-typed stuck program.  It
  is needed at a location because an atom may pack, and an atom rooted at a
  location becomes observation evidence when it is substituted for a variable.
* **`bindx` takes the opened body.**  The recursive subtyping rule `bindx`
  proves `μz.S ≤ μz.T` from `S ≤ T` under the hypothesis `z : S`, the body
  itself, and never under the folded `z : μz.S`.  The folded hypothesis would
  let a selection on `z` read through a packing, which is the power the source
  forbids.  For the same reason `muDrop` (`μ(T↑) ≤ T`) only drops a binder the
  body does not use.
* **Transitivity elimination by counting packings.**  Canonical forms need
  every closed inclusion rewritten without `trans` steps.  Undoing a packing
  substitutes a location into a `bindx` premise, which creates new selections on
  that location that must be undone in turn.  The induction that breaks this
  circle is on the number of packings on an observation's spine (`ObsInv`,
  `ObsInv.step`, `LeTy.strengthenAt`): every selection created observes the
  location with fewer packings than the one undone, as with the pack count of
  the reference's `htpy`.
* **Preservation up to evidence.**  The machine substitutes a root location and
  drops the coercions around it, so the term it produces is in general not
  typable as it stands (`Preservation.OnTheNose`).  A state counts as typed when
  some typed term has the same *skeleton*: the same term structure, roots and
  annotations, with casts forgotten (`StateTy`, `Tm.skel`).  The substitution
  theorem supplies that term, and the machine reads nothing the skeleton
  forgets.
* **A location is observed at any type that matches its literal, and that is
  not `T_Vary`.**  The location rules `VcTy.vcLocAny` and `AtomTy.varConcAny`
  observe `ℓ` at a self type the syntax carries, instantiated at `ℓ`, when that
  instance matches the stored literal (`LitMatch`): `⊤`, or an intersection
  whose type members are the stored ones, exact, and whose method members are
  exactly the two annotations of a method stored with both.  No method body is
  re-typed and members may be left out, so the rules accept types `T_Vary`
  does not give: `⊤` at every location, for one.  Over an honest store they
  are admissible in the source all the same (`Store.Honest.litMatch_stp`,
  `litMatch_hasType`).  They do not read `W`, but they take the stored
  annotations on trust, as `vcLoc` takes `W`: over the annotated store
  holding `{def 0(y : ⊤) : ⊥ = y}`, which has no honest store typing, they
  type `ℓ.0(ℓ)` at `⊥` at every `W`, and `Oopsla16` does not type it at all
  (`Coverage.UncheckedBody`).  So
  admissibility needs an honest store: at a location without a `T_Vary`
  typing, `loc ℓ ⊤` is typed at every `W` while the source types `ℓ` at
  nothing (`Coverage.noVary_not_admissible`).  A source `T_Vary` gives the match exactly when the
  methods stored at `ℓ` carry both annotations (`varyLitMatch`,
  `varyLitMatch_annotated`).  At a location holding a method without them the
  location rules give no type `T_Vary` gives (`varConcAny_not_vary`,
  `vcLocAny_not_vary`).  `varConc` still types `var (conc ℓ)` at `tyOf W ℓ`,
  which over an honest `W` is a `T_Vary` type, but at no other type.  So the
  term elaboration, which works at every store typing, takes the hypothesis
  `Store.Annotated G`, and `T_Vary` then elaborates at any store typing; that
  the hypothesis is necessary is argued, not proved.  The headline theorems
  are unaffected: they start from the empty store or from stores whose
  witnesses are in `DmsFrag`, and both are annotated.  The rules are sound
  because every result is proved for them as stated, and the body the machine
  runs is typed by the machine store's honesty invariant, whose erased store
  annotates every method with the types its body was checked at.  The match is decidable, and every syntax node has
  exactly one typing rule, which is what makes typing decidable (`Checker`,
  `CheckerCompleteness`).
* **The two machines are related, not equated by erasure.**  The target applies
  atoms and has `let`; the source applies arbitrary terms and has no `let`, so
  an elaborated term does not erase to its source.  `Corr` relates them: an atom
  stands for its root, a cast is invisible, and `let x = d in u` stands for a
  source term with `d`'s counterpart in the hole of an evaluation context.  The
  forward simulation and `transport` turn target safety into source safety; the
  backward simulation accounts for every target step by at most one source
  step.

## Where FCdotR is not a rule-for-rule image of `Oopsla16`

Types, contexts and source stores are `Oopsla16`'s own (`Syntax`), so the type
translation is the identity.  These target rules are exact images of source
rules, with the same premises plus the store-typing index `W`:

* the evidence rules `bot`, `top`, `dfun`, `dtyp`, `defL`/`defR`
  (`stp_strong_sel1`/`2`), `bindx`, the ∧ and ∨ rules and `trans`;
* `selL`/`selR`, `vcVar`, `vcUnfold` and `vcSub` when the subject is an
  abstract variable;
* the term rules `varAbs`, `pack`, `unpack`, `new`, `dnil` and `dty`, and
  `AtomTy.cast` and `TmTy.cast`, which are `T_Sub` at an atom and at a term.

Being an image concerns the premises and the conclusion.  The nodes of these
rules also carry as syntax what the source rule leaves implicit: a `cast`
carries its coercion (subsumption is a node, not a rule), `pack`, `unpack`
and `vcUnfold` their bodies, and `new` its self type (item 21).  `TmTy.atom`,
which makes an atom a term, has no source rule behind it: the source has one
sort of terms, and a variable is one of them.  It belongs with the other
changes to the term syntax, item 21.

Everything else is listed below, continuing the numbering of the deviations of
the source (`../Oopsla16/README.md`, *Deviations from `dot.v`*).  Each item has
a status: **PROVED** (the named theorem proves it), **ARGUED** (only comments
argue it) or **NEITHER** (nothing does; the item records a gap).

17. **`refl` and `muDrop` are primitive.**  `stp_selx` and `stp_bind1` have no
    primitive image; `elabStp` sends them to `refl` and to
    `trans (bindx …) (muDrop …)`.  Both extra rules hold in the source:
    **PROVED** (`Oopsla16.Stp.refl`, `muDrop_admissible`).
18. **`selL`/`selR` accept a location as subject.**  The source resolves a
    selection on a location only through `stp_strong_sel1`/`2` or `stp_selx`;
    the target also reads the bounds off an observation of the location.  With
    a store typing that lies, the target proves `⊤ ≤ ⊥` where the source cannot:
    **PROVED** (`CanonicalForms.DishonestStore.topLeBot`,
    `Oopsla16.stp_consistent`).  With an honest store typing the bounds read
    are the stored member's, as target inclusions
    (`Inversion.obs_conc_admissible`); that nothing more is derived, as a
    source `Stp`: **NEITHER**.
19. **Observing a location.**  The target adds `vcLoc` (which reads `W`),
    `vcLocAny`, `vcPack`, and `vcUnfold`/`vcSub` with a location as subject;
    the source's `Htp` observes abstract variables only and cannot pack.  The
    set mirrors the reference's proof-internal `htpy`
    (`dot_soundness.v:215-236`), except at its base: `htpy`'s `TY_Vary` is
    `T_Vary`, while `vcLocAny` takes `LitMatch` (item 27).  That `vcPack` has
    no typing at an abstract variable: **PROVED**
    (`CanonicalForms.no_pack_at_abs`).  Over an honest store, the type `vcLoc`
    gives is a `T_Vary` type, at the honesty witness (**PROVED**,
    `Store.Honest.vary`), and `vcLocAny` is admissible in the source
    (**PROVED**, item 27); observations built on them with `vcPack`,
    `vcUnfold` and `vcSub`, read back as source typings: **NEITHER**.
20. **`varConc` types a location at the type `W` records.**  No source rule
    does.  Over an honest store that type is a `T_Vary` type, at the honesty
    witness: **PROVED** (`Store.Honest.vary`).  It is the only type `varConc`
    gives; other `T_Vary` types have no image through it.
21. **Terms are in A-normal form.**  Atoms and terms are two sorts, and
    `TmTy.atom` makes an atom a term.  Applications take atoms, and `T_App`
    and `T_AppVar` become one rule (`TmTy.app`, with `TmTy.appWeaken`).
    `let` is a rule with no source counterpart, and `new` carries the self
    type.  A general application elaborates through `let` (`TmElab.app`,
    `TmElab.appVar`).  Source to target, typed and corresponding, over an
    annotated store: **PROVED** (`elabTm`, `Corr`).  Target to source:
    **NEITHER**.
22. **Methods always carry both annotations.**  `Defs.dfun` has a domain and a
    codomain, and `DefsTy.dfun` has no `EqSome`.  A method written without
    annotations in the source is given the types `D_Fun` checked, and erasure
    writes them back as `some` (`Erasure.Defs.erase`).  That every source
    definition-list typing over an annotated store elaborates, whether or not
    the list's own methods are annotated: **PROVED** (`elabDefs`); the round
    trip changes the annotations (item 25).
23. **The machine is different.**  A store-and-continuation machine with six
    rules replaces the four-rule substitution machine.  `alloc` is `ST_Obj`
    without the self type, `app` is `ST_AppAbs` on atom roots, and
    `ST_App1`/`ST_App2` exist only as continuation frames; four administrative
    rules correspond to no source step; the machine store holds target
    definitions, related to the source store with annotations ignored.  The
    correspondence: **PROVED** (`sim_step`, `sim_stuck`, `Rel.reflect_step`).
24. **Target preservation holds only up to evidence.**  The machine drops an
    atom's evidence when it substitutes, and the reduct need not be typable on
    the nose.  **PROVED** as stated (`preservation'`, up to the evidence
    skeleton, `StateTy`), and on-the-nose preservation is refuted
    (`Preservation.OnTheNose.reduct_untypable`).
25. **Elaborate-then-erase is not the identity.**  `let` erases to an object
    encoding (`Erasure.letEncode`), and an unannotated method comes back
    annotated, which is why the `_honest` theorems need `DmsFrag`.  The equation
    on the fragment: **PROVED** (`elabHasType_erase`, `elabDms_erase`); off it
    the equation is false and `Corr` replaces it.
26. **In general only source-to-target typing is proved.**  Every source
    evidence derivation elaborates, and every source term typing does over an
    annotated store (`elabStp`, `elabHtp`, `elabTm`).  That the target proves
    no more than the source: **NEITHER** in general.  It is false over a lying
    store typing (item 18), and false at every store typing over a store with
    a location that has no `T_Vary` typing, which every store without an
    honest store typing has, classically (item 27,
    `Coverage.noVary_not_admissible`; `Coverage.UncheckedBody` is an annotated
    instance).  Over an honest store it is **PROVED** for the
    location rules (item 27) and for `refl` and `muDrop` (item 17); it is
    open for `selL`/`selR` at a location (item 18) and for the observations
    built on a location node (item 19).
27. **The location rules are not `T_Vary`.**  `VcTy.vcLocAny` and
    `AtomTy.varConcAny` observe `ℓ` at a self type `T` whenever `T[ℓ]` matches
    the literal stored at `ℓ` (`Typing.LitMatch`): `⊤`, or a right-nested
    intersection whose type members are exactly the literal's at their labels
    and whose method members are exactly the two annotations of a method
    stored with both.  `T_Vary` (`dot.v:220-226`) re-types the whole literal,
    method bodies included.
    * What the match does not check: no method body is typed, members may be
      omitted, reordered or repeated, and `⊤` matches every location.
    * What it does check: a type member is the stored one, and a method member
      needs a method stored with both annotations and equals them
      (`LitMatch.storedMethod`).  At commit
      `4312920` a method member was only compared with the annotations by
      `EqSome`, so an unannotated stored method matched every method type:
      over a store holding `{def 0(y) = y}`, `ℓ.0(ℓ)` had type `⊥` (shown by
      an audit probe against that commit, not kept in the repository).  The
      same term is now rejected (`CheckerExamples.appBot_untypable`).
    * What the rules trust: the stored annotations, as `vcLoc` trusts `W`.  The
      store typing plays no part in them, but a method member is accepted at
      the annotations whether or not the stored body has the annotated type.
      Over the store holding `{def 0(y : ⊤) : ⊥ = y}`, which is annotated, the
      target types `ℓ.0(ℓ)` at `⊥` at every store typing, while `Oopsla16`
      types neither `ℓ.0(ℓ)` nor `ℓ` at any type, and the store has no honest
      store typing: **PROVED** (`Coverage.UncheckedBody.appBot_typed`,
      `app_untypable`, `loc_untypable`, `not_honest`; `CheckerExamples`
      accepts the term at two store typings).  So the admissibility of the
      next bullet needs an honest store: over this store it fails at every
      `W`, and so it does at every location that has no `T_Vary` typing,
      where `loc ℓ ⊤` is typed and the source types `ℓ` at nothing
      (**PROVED**, `Coverage.noVary_not_admissible`).
    * Over an honest store the rules are admissible in the source: every
      conjunct of a matched type is a conjunct of the recorded type, so
      `Oopsla16` proves `tyOf W ℓ <: B` and types `ℓ` at `B` by `T_Vary` and
      `T_Sub`.  **PROVED** (`Store.Honest.litMatch_stp`,
      `Store.Honest.litMatch_hasType`, `Store.Honest.varConcAny_admissible`,
      `Store.Honest.vcLocAny_admissible`).
    * A `T_Vary` premise pair gives the rules' premise exactly when the
      literal stored at the location is annotated: **PROVED**
      (`varyLitMatch`, which takes `Dms.Annotated`, and its converse
      `varyLitMatch_annotated`).  `elabTm`, `elabSpecGen` and `ElabSpecGen`
      take `Store.Annotated G`.
    * At a location holding a method without both annotations the location
      rules give no type `T_Vary` gives: no `loc ℓ T'` or `vcLocAny ℓ T'` with
      `T'[ℓ]` a `T_Vary` type has a typing.  **PROVED**
      (`Admissibility.varConcAny_not_vary`, `Admissibility.vcLocAny_not_vary`,
      and `CurryStore.loc_untypable` for `Admissibility.CurryStore`;
      `CheckerExamples` rejects the `T_Vary` type there, and also
      `{0 : ⊤ → ⊥} ∧ ⊤`; that the latter is not a `T_Vary` type either,
      since `D_Fun` would have to type the body `y : ⊤` at `⊥`, is
      **ARGUED** only).  Another target rule
      can still give such a typing an image: `varConc` types `var (conc ℓ)`
      at `tyOf W ℓ`, which over an honest `W` is a `T_Vary` type
      (`Store.Honest.vary`; `CurryStore.varConcTyped`, accepted in
      `CheckerExamples`).  But `varConc` gives that one type only, and
      `ElabSpecGen` asks for every `W` and every `T_Vary` typing.  That the
      hypothesis is therefore needed for an elaboration at every store typing:
      **ARGUED**, not proved.
    * The headline theorems are unaffected.  `oopsla16_safety` and
      `oopsla16_not_stuck` start from the empty store, which is annotated
      (`Store.Annotated.nil`); the `_honest` versions start from stores whose
      witnesses are in `DmsFrag`, which are annotated
      (`Store.Honest.annotated`).  Their statements did not change.
    * Soundness of the target with the rules as stated: **PROVED** (`safety'`,
      `preservation'`, `progress'`).  These theorems assume an honest machine
      store, whose invariant types every stored body at the method's
      annotations, so there the trust described above is justified; at run
      time the erased machine store annotates every method, and a matched
      method member is the stored method's type (`Preservation.LitMatch.method`).

## What is not here

* **The checker decides FCdotR typing, nothing more.**  It checks fully
  annotated evidence and terms, such as the elaboration produces; it does not
  decide `Oopsla16` typing.  Like the rules it decides, it takes two things on
  trust.  `vcLoc` and `var (conc ℓ)` read their types off the store typing
  `W`.  The location rules `vcLocAny` and `loc ℓ T` read a method member's
  types off the stored method's annotations and do not type its body.  That
  `W` tells the truth, and that each stored body has its annotated type, is
  the separate invariant `Store.Honest`.  Over the annotated store holding
  `{def 0(y : ⊤) : ⊥ = y}`, which has no honest store typing, the checker
  accepts `ℓ.0(ℓ)` at `⊥` at every `W`, where `Oopsla16` types it at nothing
  (`Coverage.UncheckedBody`, `CheckerExamples`).
* **No source-side preservation.**  The headline theorems say a reached
  configuration is never stuck.  They do not say it, or the final answer, has
  the program's type in `Oopsla16`.  The closest statement is
  `Oopsla16.reachable_related`, which types the related *target* state at the
  program's type.
* **Safety from a typed store is limited to fragment literals.**  The
  reference's `type_safety` is a one-step statement over any store.  Here a run
  must start from the empty store, or from a store whose objects were typed from
  `DmsFrag` literals; a store holding a method without type annotations, for
  example, is not covered (`Coverage.CurryGap` has a typed configuration over
  such a store that no theorem here reaches), and over such a store the term
  elaboration's hypothesis `Store.Annotated G` fails.  Lifting the fragment restriction would
  take target typing carried back into source typing.  Covering unannotated
  stored methods would take a location rule that types them: the rule of
  commit `5324088`, whose premises were `T_Vary`'s own, did, and its
  elaboration needed no store hypothesis, but checking such a premise means
  deciding `Oopsla16` typing (`STATUS.md`, *What remains*).  That nothing
  short of that suffices is argued, not proved.
* **No erasure equation beyond the fragment.**  A `let` erases to an object
  encoding, and two typings of one term may elaborate to different terms, so
  coherence is stated as equal answers (`elab_coherence`), not equal erasures.
* No determinism theorem for either machine, and no statement about
  divergence.
* No correspondence with `../DotMNF` or `../FCdot`.

## References to uncommitted work

Some comments here and in `../Oopsla16` compare FCdotR with results of the
WadlerFest line that live in files **not committed** to the repository at the
time of writing (none of them is in commit `d3fd166`):
`DotToFCdot/RecursiveSubtypingSeparation.lean` and
`DotToFCdot/RecursiveSubtypingLimit.lean`,
`DotToFCdot/RecursiveSelectionCounterexample.lean`,
`DotToFCdot/RecursiveTranslationCounterexample.lean`,
`FCdot/RecursiveEvidence.lean`, `FCdot/ReceiverCounterexample.lean` and
`FCdot/RecursiveTypes.lean`; the discussion of `FunctionField` in
`DotToFCdot/RecursiveSubtyping.md` is an uncommitted edit as well.  No FCdotR
or `Oopsla16` module imports them, and no result here depends on them.  Each
comparison is motivation, not a result of this library.  In particular, that
FCdot has no closed inclusion evidence for the WadlerFest counterpart of
`Oopsla16.Examples.FunctionField` (a field of function type in place of the
method) is the theorem `DotMNF.RecursiveSubtyping.FunctionField.no_coercion`
of `RecursiveSubtypingSeparation.lean`; until that file is committed, the
repository does not prove it.
