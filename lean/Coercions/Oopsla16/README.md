# Oopsla16

The Rompf--Amin calculus of
[*Type Soundness for Dependent Object Types*](https://namin.seas.harvard.edu/files/soundness_oopsla16.pdf),
transcribed from the authors' Coq artifact `TiarkRompf/minidot`, commit
`ef1143dc1875d389c47083cd324971b1b86686d1`,
directory `oopsla16/`, file `dot.v`. This is the source specification for
recursive subtyping: unlike WadlerFest DOT, it has `stp_bindx` and `stp_bind1`,
and its `type_safety` (`dot_soundness.v:1131`) is proved.

The library is independent of `../DotMNF`, `../FCdot` and `../DotToFCdot`. It
shares only `FCdot/Debruijn.lean`, which is generic scoping infrastructure.
Its explicit-evidence target is [`../FCdotR`](../FCdotR/README.md), which
proves its type safety (see *What is not here*).

| module | contents |
|---|---|
| `Syntax` | labels `Lb := Nat`; two-zone variables `Vr σ s` (`conc` for the store, `abs` for hypotheses and binders); types `⊥ ⊤ {def l(x:S):U} {type l:S..U} p.l {z=>T} ∧ ∨`; terms, definitions `dfun`/`dty`, definition lists `Dms`; positional member lookup `Dms.get?`; stores `Store σ σ'` |
| `Structural` | renaming of the local scope and of the store scope; `Subst` and `substVr` (`open 0 v`); weakenings; `Store.lookup` |
| `SubstLemmas` | identity, composition and fusion laws for `Subst`, covering renaming, store renaming, weakening and `open 0 v` at once |
| `Context` | `scopeUpTo`/`renameUpTo`/`varUpTo`, the prefix at a variable; contexts with self-referential entries; `Ctx.lookupAt`, `Ctx.lookup`, `Ctx.upTo` |
| `Semantics` | store growth `Grows`; `Step` (`ST_Obj`, `ST_AppAbs`, `ST_App1`, `ST_App2`), `Steps`, `Tm.IsAnswer` |
| `Typing` | `EqSome`; the mutual family `HasType`, `DmsHasType`, `Stp`, `Htp` with the reference's 8 + 3 + 18 + 3 rules and rule names |
| `Lemmas` | `Stp.refl`, reflexivity by structural recursion on the type |
| `Examples` | `ex0`; `FunctionField`, a self-dependent method under `stp_bindx`; `forgetSelf`, a `stp_bind1` instance |
| `PackingCounterexample` | an isolated extension adding the packing rule to `Htp`, and a well-typed stuck program |

## Design

The port is a reformulation, not a transcription. Scoping is intrinsic, in the
discipline of `FCdot/Debruijn.lean`, which the rest of this development uses.
Three things of the reference are therefore absent, and one thing it leaves
implicit becomes explicit.

* **`closed i j k T` is gone** (`dot.v:100-127`), and with it every
  closedness premise of every rule. The judgment block `dot.v:219-393` has 25
  of them (24 `closed`, one `vr_closed`), besides 10 `open 0` equations among
  the premises, one `open 0` in the conclusion of `htp_unpack` (`dot.v:383`),
  and `T_Vary`'s two `subst` equations (`dot.v:223-224`). Twenty of the 25 are
  well-scopedness, which the indexing supplies, or redundant. Three say that a
  type does not mention a variable: `T_App`'s result (`dot.v:249`), `D_Fun`'s
  parameter type (`dot.v:276`) and `stp_bind1`'s right-hand side
  (`dot.v:332`); here each is an explicit weakening, `.weaken`. Two constrain
  the context, `T_Varz`'s (`dot.v:229`) and `htp_var`'s (`dot.v:378`); here
  they are the prefix indexing of `Ctx`, which is a real restriction (see
  *What the two datatypes constrain*).
* **`TVarB` is gone** (`dot.v:23`). A bound variable is an abstract variable of
  an extended scope, so `open 0 u T` (`dot.v:135`) is `Ty.substVr T u` and every
  `T' = open 0 (TVar false (length GH)) T` side condition disappears. `stp_bindx`
  shrinks from eight lines to three.
* **The derivation-size index is gone** (`dot.v:219`, `:263`, `:285`, `:375`).
  The reference uses it for inductions that recurse on a bound rather than on
  the derivation: transitivity pushback and narrowing, and also `all_extend`
  (`dot.v:559`), `all_closed` (`dot.v:668`), `stp_splice_aux` (`dot.v:1533`),
  `stp_upgrade_gh_aux` (`dot.v:1745`), `subst_aux` (`dot_soundness.v:499`) and
  `hastp_subst_aux` (`dot_soundness.v:854`). No rule constrains the index.
  Derivations here are `Type`-valued data, as in `../DotMNF/Typing.lean`,
  because a translation into explicit evidence is a function on derivations.
  If a size measure is ever needed, `sizeOf` supplies one.
* **Store weakening becomes explicit.** The reference's concrete identifiers are
  absolute positions, "invariant under context extension" (`dot.v:21-22`), so
  allocation costs it nothing. Here the two congruence rules of `Step` carry a
  `Grows` index and rename the operand they do not reduce.

Two features of the reference are kept exactly, because they are what its
soundness rests on.

**Variables have two zones.** `Vr.conc` indexes the store and `Vr.abs` the
local context, and the distinction is syntactic, so `stp_strong_sel1` can
resolve a concrete selection precisely against the stored definition while
`stp_sel1` resolves an abstract one through `Htp`. The two scopes are separate
indices `Ty σ s` rather than one scope with a distinguished prefix, because
`stp_strong_sel1` checks its premise in the *empty* local scope over the full
store (`dot.v:308`).

**Labels are positional and share one namespace.** `Lb := Nat` indexes both
`TFun` and `TTyp`, a member's label is the length of its tail (`dot.v:269`,
`dot.v:278`), and lookup is by position. There is no type/term label category,
so the `WadlerFest/LabelSorted` discipline of `../DotMNF` has no analogue here,
and no distinctness condition is needed: an object with `n` members has exactly
the labels `n-1, ..., 0`.

### Context entries may mention their own binder

`DotMNF.Ctx.cons` takes a `Ty s` and therefore cannot hold an opened self type;
`DotMNF` binds the folded `μ(x. T)` and recovers the opened body by `Rec-E`.
The reference does the opposite. `stp_bindx` (`dot.v:335-341`) and `T_Obj`
(`dot.v:241-245`) push `open 0 (TVar false (length GH)) T`, which mentions the
variable it introduces, and `Htp` has no rule that folds an abstract variable
back up. So `Ctx.cons` here takes a `Ty σ (s,x)`. A hypothesis that does not
mention its own binder — the parameter of `stp_fun` and `D_Fun` — is a
weakening.

The extrinsic shadow of this is visible in the reference: `htp_var` and
`htp_unpack` require `closed (S x) ...`, not `closed x ...` (`dot.v:378`,
`dot.v:382`).

### The context truncation of `htp_sub` becomes scoping

This is the one place where the reformulation does more than remove noise.
The reference writes

```coq
| htp_sub: forall GH GU GL G1 x T1 T2 n1 n2,
    htp GH G1 x T1 n1 -> stp GL G1 T1 T2 n2 ->
    length GL = S x -> GH = GU ++ GL ->
    htp GH G1 x T2 (S (n1+n2)).
```

`GL` is the suffix holding exactly the hypotheses `0 ... x`; the discarded
prefix `GU` is everything introduced after `x`, including the self assumption
of an enclosing `stp_bindx`. Those two equations are the restriction that makes
recursive subtyping sound, and the artifact flags them with a comment.

Here `Htp` types a variable at a type of **its own prefix scope**,

```lean
inductive Htp : {σ s : Sig} → Store σ σ → Ctx σ s → (x : BVar s .var) →
    Ty σ (scopeUpTo x) → Type
```

and `htp_sub` widens in `Γ.upTo x`. Both side conditions disappear: a
hypothesis introduced after `x` is not in scope in the ordinary sense of the
word, and `stp_sel1` has to weaken its result back into the ambient scope with
`renameUpTo x`.

This is faithful only if every type the reference's `htp` assigns to `x` is
closed at `S x`, i.e. mentions only `x` and older variables. The reference does
not prove that. It proves `htp_closed` (`dot.v:781-784`), closedness at
`length GH`, and `htp_closed1` (`dot.v:786-789`), `x < length GH`. The `S x`
version is proved, on the reference's own definitions, as `htp_closed_Sx` in
`../../../coq/oopsla16-deviations/ctx_restriction.v`. That the Lean `Htp`
derives exactly what the reference's `htp` derives is argued rule by rule, not
proved.

### What the two datatypes constrain, and what they do not

`venv := list vl` (`dot.v:69`) is unconstrained: the artifact has no store
well-formedness predicate, every stored object is bounded by the same
`length G1`, and `type_safety` is stated for an arbitrary store. A stored
object may therefore mention a location allocated after it, and two objects may
mention each other. `Store` is indexed twice for that reason — `Store σ σ'`
holds the objects at the binders of `σ'`, each well scoped in the full store
scope `σ`, and a complete store is `Store σ σ`. Indexing each entry by its own
prefix would have been strictly stronger than the reference.

`Store` is still a **restriction** of `venv`. Each entry is a `Dms σ []`, so a
stored object mentions no abstract variable, no dangling `TVarB` and no
location outside the store. `venv` admits all three, and the reference derives
judgments over such stores: `stp_strong_sel1`/`stp_strong_sel2` read only the
member they select, so a closed term is typed over a store whose other member
is ill scoped (`store_restriction_is_real` in
`../../../coq/oopsla16-deviations/store_restriction.v`). The reference's
`type_safety` therefore covers configurations no Lean `Store` can express.
The Lean theorems start from the empty store, and in the reference every store
reached by running a closed, well-scoped term from the empty store has all its
variables in range, so no reachable configuration is lost; that is argued, not
proved.

`Ctx` is indexed by prefixes, and that is a restriction too: Coq's `tenv` is an
unconstrained `list ty`, so it admits an entry mentioning a *newer* variable,
which `T_Varz` (`dot.v:227-230`, which needs only `closed (length GH) …`)
accepts. No such context arises in a derivation that starts from a
prefix-closed context, the empty one included. Every rule that extends the
context pushes an entry closed at its own position or below: `stp_fun` and
`D_Fun` push a type of the old scope (for `stp_fun` by the regularity lemma
`stp_closed1`, `dot.v:830`, not by a premise), `stp_bind1`, `stp_bindx` and
`T_Obj` push the opened body, `T_Vary` starts a fresh `[T']`, and `htp_sub`
passes to a suffix. This is **proved** on the reference's own rules in
`../../../coq/oopsla16-deviations/ctx_restriction.v`: the 32 rules with the
premise "the context is prefix-closed" added to each derive, from every
prefix-closed context, exactly the judgments of the reference at the same size
index (`restriction_harmless`), in particular from the empty context
(`restriction_harmless_empty`); and the restriction is real
(`ctx_restriction_is_real`). That prefix-closed Coq contexts correspond one to
one to Lean `Ctx` values is argued, not proved. The prefix indexing is what
makes `Ctx.lookupAt`, and with it the `Htp` indexing below, well typed.

### No packing in `Htp`, and why that is not a proof device

`Htp` has `htp_unpack` and no packing rule, while `HasType` has both
`T_VarPack` and `T_VarUnpack`. A type selection used inside subtyping may
therefore not be justified by first packing its receiver into a `TBind`. That
is exactly the step `DotToFCdot/RecursiveSelectionCounterexample.lean` uses to
break the corresponding WadlerFest extension, and it is why that counterexample
is not an attack on the calculus formalized here. That file is uncommitted
work at the time of writing (`../FCdotR/README.md`, *References to uncommitted
work*); `PackingCounterexample` below makes the point within this library.

Section 3 of the paper calls this the first of two contractiveness
restrictions, says both are "necessary for the proofs", and conjectures that
they "could be lifted without breaking soundness, since we can always construct
explicit conversion functions that use rules (VARPACK) and (VARUNPACK) on
proper term bindings". Of the second restriction it says separately that it is
"not just a technical device, it seems reasonable for soundness".

`PackingCounterexample` adds the first restriction's missing rule and nothing
else. Over a two-object store with

```text
p.B = {A : D .. D'}
p.C = {K : p.B .. p.C} ∧ ({missing : ∀(_:⊤) ⊤} ∧ ⊥)
D   = μ _. p.B          D' = μ _. p.C          q.A = D
```

`packing_is_unsound` exhibits a closed program that is well typed at `⊤`, is
not an answer, and cannot step, so the progress half of the reference's
`type_safety` fails. Three points fix the scope of that result.

* The **second** restriction is kept and satisfied: `htp_sub` still widens in
  `Γ.upTo x`, and every use of it is at the self introduced by `stp_bindx`,
  which is the newest binder, so `Γ.upTo z = Γ` and `length GL = S x` holds
  with `GU` empty. The restriction is not stressed — it never constrains a
  selection on the innermost self — but it is not lifted either.
* Most of the derivation needs no new rule. `dSubPlain` derives `D <: D'` under
  `z : p.B` in the unmodified calculus, from the bounds of `z.A`. The packing
  rule buys exactly one step, packing that same `z` so that `z.K` becomes
  readable.
* The culprit is the interaction. WadlerFest DOT and pDOT take the `Sel`
  premise from ordinary typing, with recursive introduction available, and are
  sound; they have no `stp_bindx`. What is unsound is recursive subtyping
  together with a packing rule in the selection judgment.

Both recursive types ignore their self binder, so the result does not depend on
which closedness index a packing mirror is given.

The same result is mechanized in Coq at `../../../coq/oopsla16-packing/`, in
the artifact's own definitions and carrying `closed`, `TVarB` and the size
index. Lines 25-410 of its specification `dot_spec.v` are byte-identical to
`dot.v:14-399`; its lines 10-24 replace the `SfLib`/`Arith` imports. Its
extended judgment block differs from `dot.v:219-393` by one character, so the
result does not depend on the choices this port makes. The extension is not a
conservative extension — it proves `μ(_.p.B) <: μ(_.p.C)`, a statement of the
old vocabulary — but it is a subsystem of `Oopsla16` with `htp_pack`: every
constructor is an existing rule with the same indices, `htp_pack`, or an
embedding of an existing derivation.

## Correspondence with `dot.v`

Rule names are the Coq names verbatim, so the correspondence is the identity on
names. Type and term constructor names are also the Coq names (`TBot`, `TFun`,
`tobj`, `dcons`), which additionally avoids every Lean keyword clash. Functions
and lemmas use this development's `Subject.camelCase` convention.

| Lean | Coq | `dot.v` | note |
|---|---|---|---|
| `Lb` | `lb` | 18 | `Nat`; one namespace |
| `Vr.conc x` | `TVar true x` | 21 | store zone |
| `Vr.abs x` | `TVar false x` | 22 | local zone |
| — | `TVarB x` | 23 | absorbed into the local scope |
| `Ty`, `Tm`, `Dm`, `Dms`, `Store` | `ty`, `tm`, `dm`, `dms`, `venv` | 26-69 | constructor names verbatim |
| `Ctx σ s` | `tenv` | 70 | entries may mention their own binder |
| — | `vr_closed`, `closed` | 89-127 | intrinsic |
| `Ty.substVr T v` | `open 0 v T` | 135 | |
| `Ty.rename`, `Ty.renameStore` | — | | implicit in the reference |
| `Dms.get? ds l` | `index l (dms_to_list ds)` | 77, 59 | |
| `Store.lookup G x` | `index x G1 = Some (vobj ds)` | 77 | total |
| `Step` | `step` | 197-212 | plus the `Grows` index |
| `EqSome` | `eq_some` | 216 | |
| `HasType` (8 rules) | `has_type` | 219-260 | |
| `DmsHasType` (3) | `dms_has_type` | 263-282 | |
| `Stp` (18) | `stp` | 285-372 | |
| `Htp` (3) | `htp` | 375-393 | indexed at `Ty σ (scopeUpTo x)` |
| `scopeUpTo x`, `Ctx.upTo` | `GL`, `length GL = S x`, `GH = GU ++ GL` | 391-392 | |
| — | derivation size `n` | 219, 263, 285, 375 | dropped |

## Deviations from `dot.v`

In brief; the itemized list, with Lean and Coq line citations and a status for
each item (PROVED, ARGUED or NEITHER), is [`DEVIATIONS.md`](DEVIATIONS.md).

* **Same rules.** The four judgments have the reference's 32 rules and `Step`
  its 4, one for one, under the reference's names. Nothing is added.
* **Written differently.** Intrinsic scoping replaces `closed`, `TVarB` and
  `open`; weakening is explicit; `htp_sub`'s truncated context is a prefix
  scope; the size index is dropped; `Step` carries a store-growth index. That
  this is faithful is argued, not proved: Coq and Lean definitions cannot be
  related formally. The step relation is also tested against a transcription
  of the reference (`../../../coq/oopsla16-deviations/step_differential.py`).
* **Lean admits less, in three places.** Contexts may mention only older
  variables (harmless: proved in Coq on the reference's own rules). Stored
  objects must be well scoped (the reference covers stores the port cannot
  express, proved in Coq; that this costs the empty-store theorems nothing is
  argued). Out-of-range syntax cannot be written (argued harmless).
* **The theorems prove less than `type_safety`.** There is no preservation for
  the source, and the starting store is the empty one or one of annotated
  objects. Reading the reference's one-step statement as "every run is safe"
  needs `step` to be deterministic, which holds by inspection and is proved in
  neither artifact.

## What is not here

* **No soundness proof inside this library; one is transported from
  `../FCdotR`.** `dot_soundness.v` is 1261 lines on top of `dot.v`'s 2093, and
  its architecture — a precise subtyping relation `stpp`, a pack-counted
  variable typing `htpy`, narrowing, substitution, and transitivity pushback —
  is not reproduced here. Instead every typing of this calculus over a store
  whose stored methods carry both annotations, the empty store included,
  elaborates into the explicit-evidence calculus FCdotR, whose machine is
  proved safe, and a correspondence between the two machines carries safety
  back.
  * `Oopsla16.oopsla16_safety` and `Oopsla16.oopsla16_not_stuck`
    (`../FCdotR/SourceSafety.lean`): a closed term typed over the empty store
    never reaches a stuck configuration of this library's `Step`; every
    configuration it reaches is an answer or takes a step. No hypothesis. The
    statements mention only `HasType`, `Steps`, `Step` and `Tm.IsAnswer`, and,
    in `oopsla16_safety`, `FCdotR.SrcStuck`, a definition in `FCdotR` whose
    body uses only `Tm.IsAnswer` and `Step`.
  * `Oopsla16.stp_consistent` (`../FCdotR/Deliverables.lean`): no store derives
    `⊤ <: ⊥` in the empty context.
  * Two parts of `type_safety` have no counterpart. It re-types the stepped
    term at the same type; nothing here re-types a source term after a step.
    And it holds over any store, whereas these theorems start from the empty
    store, or, in the `_honest` versions, from a store whose objects were typed
    from literals with variable operands and annotated methods. *Deviations
    from `dot.v`* above lists these gaps with the others.

  FCdotR's `Inversion` is where the reference's pushback and pack count
  reappear, as transitivity elimination for closed evidence. See
  `../FCdotR/README.md` and `../FCdotR/STATUS.md`.
* **No correspondence with `../DotMNF`.** The two calculi differ in more than
  presentation: methods versus first-class functions, unions, general
  applications, positional versus nominal labels, two zones versus one, a
  substitution machine versus a store-and-continuation machine. Any claim
  relating them needs an explicit translation.
* **No examples for unions.** `stp_or1`, `stp_or21` and `stp_or22` are
  unexercised in `dot_exs.v` as well.
* `dot_exs.v`'s `ex1`, `ex2` and `paper_lst` are ported only outside this
  library, in `../FCdotR/CheckerExamples.lean`.

The Coq sources were read; the historical Coq 8.4pl6 build was not rerun.
