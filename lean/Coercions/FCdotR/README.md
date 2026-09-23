# FCdotR

FCdotR is the explicit-evidence target for [`../Oopsla16`](../Oopsla16/README.md),
the Rompf--Amin OOPSLA 2016 calculus with recursive subtyping.  Its types,
contexts and stores are `Oopsla16`'s, unchanged, so the type translation is the
identity.  What changes is that every use of subtyping, and every variable
typing that a type selection relies on, is a proof term (*evidence*) that the
machine carries and never inspects.  Every source typing derivation elaborates
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
| `Syntax` | inclusion evidence `Le` (the image of `Stp`), observation evidence `Vc` (the image of `Htp`, scoped at its subject's prefix), atoms, terms with `let`, definition lists; `Atom.root` |
| `Typing` | the store typing `StoreTy`/`tyOf`; the evidence judgments `LeTy` and `VcTy`; two location rules, `vcLoc` (the recorded type) and `vcLocAny` (`T_Vary` verbatim) |
| `Locality` | an observation depends only on its subject's prefix: `VcTy.strengthen`, `VcTy.ofLoc` |
| `Examples` | `FunctionField` as closed evidence (`recursive_typed`), a recursive coercion FCdot cannot express |
| `Structural` | `Mono`, substitutions that respect prefixes, as a record |
| `Subst` | `MonoSyn`, the inductive syntax of the substitutions the metatheory performs, closed under restriction; its action on all five sorts |
| `StoreTyping` | `Store.Honest` (every location holds a literal typed at its recorded type); store renaming for the source judgments; `TwoObjectStore` |
| `SubstTyping` | `MonoSyn.Ev`, `lemmaR`, and the substitution theorem for evidence, `LeTy.substEv`/`VcTy.substEv`, with no side condition |
| `TermTyping` | `AtomTy`, `TmTy`, `DefsTy`: the source's term rules one for one, with subsumption as a syntax node and application on atoms |
| `TermSubst` | the substitution theorem for atoms, terms and definition lists |
| `Machine` | the store-and-continuation machine, six rules, indexed by `Oopsla16.Grows`; `State.Final`, `State.Stuck` |
| `Erasure` | erasure into `Oopsla16` terms, with `let` as an object encoding; the evidence skeleton `Tm.skel`; the simulation without `let` frames, `Step.simulate` |
| `Forms` | sizes and pack counts (`Vc.spinePacks`, `Le.PackBound`, `Le.Strong`), head shapes, normal forms `LeNf` |
| `Normalizer` | spine normalization `VcTy.toNf`; redex elimination `VcTy.canon`, under `Contract` |
| `CanonicalForms` | `no_pack_at_abs`, the head table `LeTy.headPair_of_not_trans`, `top_le_bot_is_trans`; `DishonestStore.topLeBot` (a store typing that lies proves `⊤ ≤ ⊥`) |
| `Inversion` | transitivity elimination for closed inclusions over an honest store: `LeTy.pushback`, `SLe.nf`, the pack-count tower `ObsInv`; `Store.Honest.nf`, `consistency_honest`, `Store.Honest.obsTyp`/`obsBind`/`obsFun` |
| `Elaboration` | `elabStp`, `elabHtp`: all 18 + 3 rules at any store typing; `elabHasType` on the fragment `TmFrag` (variable operands, annotated methods) |
| `ElaborationErasure` | on the fragment, the elaboration erases to the source term exactly |
| `Preservation` | `StateTy` (typing up to evidence), `MachineStore.Honest`, the six step cases, `OnTheNose` (exact typing fails) |
| `Progress` | `progress`, `not_stuck`, `safety`, under `AppInversion` |
| `MethodInversion` | `appInversion`; the hypothesis-free `preservation'`, `progress'`, `not_stuck'`, `safety'` |
| `Correspondence` | the relation `Corr`/`Rel` between source configurations and target states; the forward simulation `sim_step`, `sim_stuck`; `transport` |
| `ElaborationFull` | `elabTm`, `elabDefs` for every source typing (general application through `let`, unannotated methods at `D_Fun`'s types); `elabSpec` |
| `Simulation` | the backward simulation `Rel.reflect_step`; answers and stuck states agree across `Rel`; the invariant `Simulated` |
| `SourceSafety` | **`Oopsla16.oopsla16_safety`, `Oopsla16.oopsla16_not_stuck`**, and the honest-store versions; worked instances `ex0_safe`, `RecursiveArg`, `HonestCall` |
| `Deliverables` | the remaining WadlerFest counterparts: consistency and recorded type members along runs, `Oopsla16.reachable_related`, `Oopsla16.stp_consistent`, coherence as equal answers |

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

`SrcStuck G t` is `¬ t.IsAnswer ∧ ¬ ∃ σ' g G' t', Step g G t G' t'`.  Both
statements use only `Oopsla16`'s `HasType`, `Steps`, `Step` and `IsAnswer`.

* `Oopsla16.oopsla16_safety`: a closed program typed over the empty store
  never reaches a configuration that is neither an answer nor able to step.
* `Oopsla16.oopsla16_not_stuck`: the same, stated positively: every
  configuration it reaches is an answer or takes a step.
* `Oopsla16.oopsla16_safety_honest`, `Oopsla16.oopsla16_not_stuck_honest`: the
  same from a nonempty store, provided each stored object was typed from a
  literal in the fragment `DmsFrag`.
* `Oopsla16.stp_consistent`: no store, reachable or not, lets source
  subtyping derive `⊤ <: ⊥` in the empty context.
* `Oopsla16.reachable_related`: every configuration a typed program reaches is
  matched by a typed target state, with a consistent store, that the elaborated
  program reaches at the same allocation index.
* `elabStp`, `elabHtp`, `elabTm`, `elabDefs`: every source derivation becomes
  target evidence, a target term or a definition list, and its typing is part
  of the result.
* `elabSpec`: every closed source typing elaborates to a typed target program
  whose start state corresponds to the source program.
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

Axioms: `propext` and `Quot.sound` for every constant of `FCdotR` and
`Oopsla16` (an audit of the whole environment checks 6323 constants).  No
`sorry`, `axiom`, `admit`, `partial` or `native_decide`.

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
* **The two machines are related, not equated by erasure.**  The target applies
  atoms and has `let`; the source applies arbitrary terms and has no `let`, so
  an elaborated term does not erase to its source.  `Corr` relates them: an atom
  stands for its root, a cast is invisible, and `let x = d in u` stands for a
  source term with `d`'s counterpart in the hole of an evaluation context.  The
  forward simulation and `transport` turn target safety into source safety; the
  backward simulation accounts for every target step by at most one source
  step.

## What is not here

* **No checker.**  The location rules `VcTy.vcLocAny` and `AtomTy.varConcAny`
  take a source typing derivation as premise, and that derivation is not part
  of the evidence.  Checking them would mean deciding `Oopsla16` typing, so the
  premise has to be carried as target evidence first.
* **No source-side preservation.**  The headline theorems say a reached
  configuration is never stuck.  They do not say it, or the final answer, has
  the program's type in `Oopsla16`.  The closest statement is
  `Oopsla16.reachable_related`, which types the related *target* state at the
  program's type.
* **Safety from a typed store is limited to fragment literals.**  The
  reference's `type_safety` is a one-step statement over any store.  Here a run
  must start from the empty store, or from a store whose objects were typed from
  `DmsFrag` literals; a store holding a method without type annotations, for
  example, is not covered.  Lifting this needs target typing carried back into source typing.
* **No erasure equation beyond the fragment.**  A `let` erases to an object
  encoding, and two typings of one term may elaborate to different terms, so
  coherence is stated as equal answers (`elab_coherence`), not equal erasures.
* No determinism theorem for either machine, and no statement about
  divergence.
* No correspondence with `../DotMNF` or `../FCdot`.
