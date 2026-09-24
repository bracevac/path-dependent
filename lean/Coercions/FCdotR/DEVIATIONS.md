# Where FCdotR is not a rule-for-rule image of `Oopsla16`

The itemized list behind the overview in [`README.md`](README.md).

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
the source (`../Oopsla16/DEVIATIONS.md`).  Each item has
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
