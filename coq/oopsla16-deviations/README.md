# Two restrictions of the Lean port, checked in the reference's own definitions

The Lean port of Rompf and Amin's OOPSLA 2016 DOT
(`../../lean/Coercions/Oopsla16/`) has fewer contexts and fewer stores than the
Coq reference, and it relies on one closedness fact that the reference never
proves. This directory mechanizes these three points in Coq, using the
reference's own definitions:

| deviation of the Lean port | result here | what it shows |
|---|---|---|
| contexts are indexed by prefixes | `restriction_harmless`, `restriction_harmless_empty`, `ctx_restriction_is_real` | the restriction is real, but no judgment reachable from the empty context changes |
| `Htp` is typed in the prefix scope of `x` | `htp_closed_Sx` | every type `htp` assigns to `x` is closed at `S x` |
| stored objects have all variables in range | `store_restriction_is_real` | the reference types closed terms over stores the Lean port cannot express |

These are items 8, 4 and 9 of the deviation audit of the Lean port.

What is proved here is proved about the Coq reference alone. The link to the
Lean port is that `ctx_ok` and `store_types_ok` (below) are the Coq images of
the Lean datatypes `Ctx` and `Store`. That link is **argued, not proved**:
the two systems cannot be related formally.

| file | contents |
|---|---|
| `regularity.v` | the reference's regularity lemma `all_closed` (`dot.v:668`) and its helpers, re-proved for Coq 8.19 with unchanged statements |
| `ctx_restriction.v` | `ctx_ok`, the four restricted judgments, `htp_closed_Sx`, `restriction_harmless`, `restriction_harmless_empty`, `ctx_restriction_is_real` |
| `store_restriction.v` | `store_types_ok`, three stores that violate it, `store_restriction_is_real` |
| `assumptions.v` | `Print Assumptions` for every result |
| `check_block.sh` | checks that the restricted judgments are the reference's rules plus one premise |
| `check_statements.sh` | checks that the lemmas of `regularity.v` keep the reference's statements |
| `build.sh` | builds everything and runs `check_block.sh` |

The specification of the reference is `../oopsla16-packing/dot_spec.v`,
compiled from that directory (see Building). It is not copied here.

## Provenance

The reference is `TiarkRompf/minidot` at commit
`ef1143dc1875d389c47083cd324971b1b86686d1`, directory `oopsla16`: `dot.v`
(definitions and regularity) and `dot_soundness.v` (`type_safety`, line 1131).
The artifact targets Coq 8.4pl6. Everything here was compiled with Coq 8.19.2.

`../oopsla16-packing/dot_spec.v` lines 25–410 are byte-identical to `dot.v`
lines 14–399, as that directory's README explains. Its only change is the
preamble: `Require Export SfLib` and the `Arith` imports are replaced by
`Require Export List` and a local definition of `beq_nat`, which Coq 8.19 no
longer provides. Beyond line 399, `dot.v` contains lemmas and proofs only, and
they do not compile under Coq 8.19 (`omega`, SfLib's `Case`). `regularity.v`
re-proves the ones needed here. Its lemma statements are the reference's, token
for token, apart from two lemmas that 8.4's standard library provided
(`beq_nat_true_iff`, `beq_nat_false_iff`):

```sh
curl -LO https://raw.githubusercontent.com/TiarkRompf/minidot/ef1143dc1875d389c47083cd324971b1b86686d1/oopsla16/dot.v
./check_statements.sh dot.v
```

## Contexts (items 8 and 4)

### The restriction

In the reference, a context is `tenv := list ty` (`dot.v:70`): any list of
types. A variable is its absolute position, and the entry at position `x` may
mention any variable, including newer ones. The Lean `Ctx σ s`
(`Oopsla16/Context.lean`) stores each entry in the scope of its own variable
and the older ones. Stated in the reference's definitions, this is:

```coq
Definition ctx_ok (GH: tenv) (G1: venv) :=
  forall x T, index x GH = Some T -> closed (S x) (length G1) 0 T.
```

Here the entry at `x` mentions only abstract variables `0 .. x`, only
allocated locations, and no unbound `TVarB`.

`has_type_r`, `dms_has_type_r`, `stp_r` and `htp_r` are the reference's four
judgments (`dot.v:219-393`, 32 rules). Each rule has one extra first premise
`ctx_ok GH G1`, so every context that occurs in a restricted derivation is a
`ctx_ok` context. Coq cannot add a premise to an existing inductive type, so
the four judgments are declared again with the suffix `_r` on the names of the
judgments and the rules.

**How the block was checked.** `check_block.sh` extracts the block from
`ctx_restriction.v` and checks three things:

1. It mentions no unrestricted judgment (`has_type`, `dms_has_type`, `stp`,
   `htp`).
2. It contains exactly 32 lines `ctx_ok GH G1 ->`, each directly after the
   `forall` line that opens a rule.
3. After deleting those 32 lines and the `_r` suffixes, `diff` against
   `dot.v:219-393` is empty.

`./check_block.sh` takes the reference text from `../oopsla16-packing/dot_spec.v`
lines 230–404. `./check_block.sh dot.v` uses the fetched `dot.v` directly. Both
report `OK`. The check was tested on four altered copies of the block, and it
rejected each one: `htp_var`'s `closed (S x)` weakened to `closed (length GH)`,
`length GL = S x` changed to `length GL = x`, a premise `True` added, and a
`ctx_ok` premise moved below another premise.

### The results

```coq
Theorem restriction_harmless: forall GH G1, ctx_ok GH G1 ->
  (forall T1 T2 n, stp GH G1 T1 T2 n <-> stp_r GH G1 T1 T2 n) /\
  (forall x T n, htp GH G1 x T n <-> htp_r GH G1 x T n) /\
  (forall t T n, has_type GH G1 t T n <-> has_type_r GH G1 t T n) /\
  (forall ds T n, dms_has_type GH G1 ds T n <-> dms_has_type_r GH G1 ds T n).

Corollary restriction_harmless_empty: forall G1 t T n,
  has_type [] G1 t T n <-> has_type_r [] G1 t T n.
```

From any `ctx_ok` context, the reference's rules and the restricted rules
derive exactly the same judgments, at the same size index, for all four
judgments. The store `G1` is arbitrary in both.

- The direction to `_r` (lemma `all_restrict`) says that every reference
  derivation starting from a `ctx_ok` context uses only `ctx_ok` contexts.
  The contexts pushed by `stp_fun`, `D_Fun`, `stp_bind1`, `stp_bindx` and
  `T_Obj` are closed at their own position, the empty context of
  `stp_strong_sel1/2` is trivially `ctx_ok`, and `htp_sub`'s suffix `GL` of a
  `ctx_ok` context is again `ctx_ok`.
- The converse (`all_unrestrict`) holds in every context, because it only
  deletes premises.

`restriction_harmless_empty` is the case that matters for the Lean port.
`type_safety` (`dot_soundness.v:1131`) has the hypothesis `has_type [] G t T n1`.
In the empty context, the restriction therefore changes neither the premise of
the reference's safety theorem nor any judgment derived beneath it.

```coq
Definition GHbad : tenv := [TTop; TSel (TVar false 1) 0].

Theorem ctx_restriction_is_real:
  ~ ctx_ok GHbad [] /\
  has_type GHbad [] (tvar false 0) (TSel (TVar false 1) 0) 1 /\
  (forall n, ~ htp GHbad [] 0 (TSel (TVar false 1) 0) n) /\
  (forall t T n, ~ has_type_r GHbad [] t T n).
```

The restriction is a real one. In `GHbad`, the entry of variable 0 mentions
the newer variable 1. The reference types variable 0 at that entry by `T_Varz`
(`dot.v:227`), which checks only `closed (length GH) …`. On the other hand, no
`htp` derivation gives variable 0 that type: `htp_var` (`dot.v:376`) checks
`closed (S x) …`, and the proof uses `htp_closed_Sx` below to rule out every
other route. The last conjunct holds simply because every
restricted rule carries the `ctx_ok` premise. No Lean `Ctx` has the shape of
`GHbad`, so the Lean port cannot state this judgment.

### The closedness fact behind the `Htp` indexing

```coq
Lemma htp_closed_Sx: forall GH G1 x T n,
  htp GH G1 x T n -> closed (S x) (length G1) 0 T.
```

The Lean port types `Htp` at `Ty σ (scopeUpTo x)`, the scope of `x` and the
older variables (`Oopsla16/Typing.lean`, `Oopsla16/Context.lean`). This choice
can express every conclusion of the reference's `htp` only if each such type
mentions no variable newer than `x`. `htp_closed_Sx` proves this, for every
context and every store. The reference itself proves only the weaker

```coq
Lemma htp_closed: forall x GH G1 T2 n,
  htp GH G1 x T2 n -> closed (length GH) (length G1) 0 T2.   (* dot.v:781 *)
Lemma htp_closed1: forall x GH G1 T2 n,
  htp GH G1 x T2 n -> x < length GH.                          (* dot.v:786 *)
```

which `regularity.v` re-proves with those statements. `htp_closed_Sx` is new.
The proof is by induction on `htp`: `htp_var` and `htp_unpack` check
`closed (S x)` themselves, and `htp_sub` concludes with an `stp` in `GL`,
where `length GL = S x`.

What this does **not** prove: that the Lean `Htp` derives exactly what the
reference's `htp` derives. That correspondence is argued rule by rule in
`Oopsla16/Typing.lean`.

## Stores (item 9)

The reference's store is `venv := list vl` (`dot.v:69`). It has no
well-formedness condition, and `type_safety` is stated for every store:

```coq
Theorem type_safety : forall G t T n1,
  has_type [] G t T n1 ->
  (exists x, t = tvar true x /\ (exists ds, index x G = Some ds)) \/
  (exists G' t' n2, step G t (G'++G) t' /\ has_type [] (G'++G) t' T n2).
```

The Lean store `Store σ σ` holds entries `Dms σ []`
(`Oopsla16/Syntax.lean`). Because it is intrinsically scoped, a stored
object mentions no abstract variable, no unbound `TVarB` and no location that
has not been allocated. For type members, that condition reads:

```coq
Definition store_types_ok (G1: venv) :=
  forall x ds l TX,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    closed 0 (length G1) 0 TX.
```

`store_types_ok` is a necessary condition for a store to be a Lean store. It is
not sufficient, because method members are unconstrained here. A store that
violates it therefore has no Lean counterpart.

```coq
Definition Gbad_abs  : venv := [vobj (dcons (dty (TSel (TVar false 3) 0)) (dcons (dty TTop) dnil))].
Definition Gbad_loc  : venv := [vobj (dcons (dty (TSel (TVar true 7) 0)) (dcons (dty TTop) dnil))].
Definition Gbad_bvar : venv := [vobj (dcons (dty (TSel (TVarB 0) 0)) (dcons (dty TTop) dnil))].

Theorem store_restriction_is_real:
  forall G, G = Gbad_abs \/ G = Gbad_loc \/ G = Gbad_bvar ->
  ~ store_types_ok G /\
  stp [] G (TSel (TVar true 0) 0) TTop 2 /\
  has_type [] G (tobj dnil) (TSel (TVar true 0) 0) 5.
```

Each store holds a single object with two type members. Labels count from the
end, so member 0 is `dty TTop`. Member 1 mentions, in turn, a free abstract
variable, an unallocated location, and a dangling bound variable.
`stp_strong_sel1` and `stp_strong_sel2` (`dot.v:305`, `310`) look up only the
member they select. The reference therefore derives judgments over these
stores through member 0, and it types the closed term `tobj dnil` at the
selection `(TVar true 0).0`: first `T_Obj` at `TBind TTop`, then subsumption
through `stp_strong_sel2`. The general form is `typed_over_top_member`, which
holds for any one-object store whose member 0 is `dty TTop`.

So the hypothesis of `type_safety` holds over these stores, and the
reference's safety theorem makes a claim about them. The Lean safety theorems
cannot cover them, because the Lean port cannot express them. We do not invoke
`type_safety` itself: its proof is part of the Coq 8.4 artifact, which is not
compiled here.

What this does **not** prove: that such stores never arise when a program
runs from the empty store. The Lean documentation relies on this to call the
restriction harmless for its empty-store theorem. It is argued there, and it is
proved neither here nor in the Lean development.

## Building

```sh
./build.sh                                   # coqc from PATH
COQC=/Users/oliver/apps/coq/bin/coqc ./build.sh
./build.sh clean
```

`build.sh` compiles `../oopsla16-packing/dot_spec.v` with
`coqc -Q . "" -o dot_spec.vo`. This writes `dot_spec.vo` into this directory
and nothing into `../oopsla16-packing`. It then compiles `regularity.v`,
`ctx_restriction.v`, `store_restriction.v` and `assumptions.v`, and runs
`check_block.sh`. The only warnings are `dot_spec.v`'s three deprecated
`Hint Unfold` / `Hint Immediate` lines, which come from the reference.

## Assumptions

None of the files contains `Admitted`, `admit`, `Axiom`, `Parameter`,
`Hypothesis` or `Variable`. The output of `assumptions.v` under Coq 8.19.2 is:

```
Print Assumptions all_closed.                 Closed under the global context
Print Assumptions htp_closed_Sx.              Closed under the global context
Print Assumptions restriction_harmless.       Closed under the global context
Print Assumptions restriction_harmless_empty. Closed under the global context
Print Assumptions ctx_restriction_is_real.    Closed under the global context
Print Assumptions bad_stores_not_ok.          Closed under the global context
Print Assumptions typed_over_top_member.      Closed under the global context
Print Assumptions store_restriction_is_real.  Closed under the global context
```

This directory is outside `rocq/`, so it is not part of the Rocq build or its
CI.
