# Packing in `htp` and recursive subtyping are jointly unsound

A Coq mechanization, in the reference calculus's own definitions, of the result
that `../../lean/Coercions/Oopsla16/PackingCounterexample.lean` proves in an
intrinsically scoped Lean port.

Rompf and Amin, *Type Soundness for Dependent Object Types*, OOPSLA 2016,
section 3, on the judgement `Γ ⊢ x :! T` that subtyping's type selections go
through:

> there are two contractiveness restrictions on type selections that ensure
> well-founded induction in the proofs (Section 6.2). First, the typing
> assignment judgement used in type selections, `Γ ⊢ x :! T`, forbids
> (VARPACK). … Second, type selections restrict the environment to disregard
> bindings introduced after the self. … While these restrictions are necessary
> for the proofs, they do not limit expressiveness of the type system in any
> significant way. … We conjecture that these contractiveness restrictions
> could be lifted without breaking soundness, since we can always construct
> explicit conversion functions that use rules (VARPACK) and (VARUNPACK) on
> proper term bindings.

Of the second restriction the paper says separately that it is "not just a
technical device, it seems reasonable for soundness". This development lifts
the **first** restriction only, keeping the second, and derives a well-typed
stuck program.

| file | contents |
|---|---|
| `dot_spec.v` | the specification of `oopsla16/dot.v` lines 1–399, compiling under Coq 8.19 |
| `dot_packing.v` | the four judgments with `htp_pack` added, the construction, and `packing_unsound` |

## Provenance and fidelity

The reference is `TiarkRompf/minidot` at commit
`ef1143dc1875d389c47083cd324971b1b86686d1`, directory `oopsla16`, file
`dot.v`. The artifact targets Coq 8.4pl6.

`dot_spec.v` lines 25–410 are **byte-identical** to `dot.v` lines 14–399:

```sh
cmp <(sed -n '14,399p' dot.v) <(sed -n '25,410p' dot_spec.v)
```

The only change is the preamble. `Require Export SfLib` is replaced by
`Require Export List` plus a local definition of `beq_nat`, which 8.19 removed
from `Arith.EqNat`; defining it locally is what keeps `index`, `vr_open`,
`vr_subst` and `subst_tm` character-identical. Nothing from `Arith.Lt` is used
before line 400. `dot.v` lines 400 onward are infrastructure lemmas for the
soundness proof and are not needed here.

`dot_packing.v` lines 45–219 re-declare the four judgments as
`has_typeP` / `dms_has_typeP` / `stpP` / `htpP`, because Coq cannot add a
constructor to an existing inductive. Undoing that renaming and diffing against
`dot.v` lines 219–393 gives **one differing character** — a period, because
`htp_pack` follows `htp_sub`:

```sh
diff <(sed -n '219,393p' dot.v) \
     <(sed -n '45,219p' dot_packing.v | perl -pe 's/\bdms_has_typeP\b/dms_has_type/g;
        s/\bhas_typeP\b/has_type/g; s/\bstpP\b/stp/g; s/\bhtpP\b/htp/g')
```

`extend_all` proves that every derivation of the original four judgments is a
derivation of the `P` versions at the same size index, so the extension is a
supersystem and no original rule was quietly weakened.

## The one added rule

```coq
| htp_pack: forall GH G1 x TX n1,
    htpP GH G1 x (open 0 (TVar false x) TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htpP GH G1 x (TBind TX) (S n1)
```

the exact converse of `htp_unpack` (`dot.v:380-383`) and the mirror of
`T_VarPack` (`dot.v:231-235`). It is used **once**, at `z_packed`.

`htp_sub` is unchanged: `length GL = S x` and `GH = GU ++ GL` are both present,
and every use in the construction is at `GU = []`, `GL = [pB]`,
`length GL = 1 = S 0`. The second restriction is satisfied, not lifted.

## The construction

```coq
Definition pB    := TSel (TVar true 0) 0.
Definition pC    := TSel (TVar true 0) 1.
Definition D     := TBind pB.      Definition D' := TBind pC.
Definition Bbody := TTyp 0 D D'.
Definition Cbody := TAnd (TTyp 1 pB pC) (TAnd (TFun 2 TTop TTop) TBot).
Definition G1    := [vobj qds; vobj pds].    (* p at index 0, q at index 1 *)
```

`dsub_plain` derives `D <: D'` under `[pB]` in the **unmodified** `stp`: the
bounds of `z.A` suffice. The packing rule buys exactly one step, packing that
same `z` so that `z.K` becomes readable, after which `stp_bindx` abstracts
`p.B <: p.C` to `D <: D'` in the empty context. Type member covariance then
gives `q` the type `p.B`, and pack, subsume, unpack give it `p.C`, whose upper
bound contains `TBot`.

`packing_unsound` is the negation of the disjunction of `type_safety`
(`dot_soundness.v:1131`), instantiated at this store and at
`tapp (tvar true 1) 2 (tvar true 1)`, with `has_typeP` in **both** disjuncts so
the extension's extra typing power cannot rescue preservation.

Both recursive types ignore their self binder, so no `TVarB` occurs anywhere in
the construction and every `closed i j k` obligation holds for all `i`, all
`j ≥ 1` and all `k`. A weaker closedness premise on `htp_pack` is therefore not
needed and a stronger one would not block it: the result does not depend on
closedness bookkeeping, which is why the Lean port's dropping of `closed` and
`TVarB` hides nothing.

`p_typed` additionally checks that both stored objects type-check in the
unmodified calculus, so the counterexample does not rest on an ill-formed
store. `type_safety` has no store premise in any case.

## Building

```sh
coqc dot_spec.v && coqc dot_packing.v
```

Coq 8.19.2. `Print Assumptions packing_unsound` reports *Closed under the
global context*; there are no `admit`s, `Admitted`s or added axioms in either
file. This directory is deliberately outside `rocq/`, so it is not part of the
Rocq build or its CI.
