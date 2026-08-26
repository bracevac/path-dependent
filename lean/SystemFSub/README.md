# SystemFSub

`SystemFSub` is a proof-relevant presentation of full declarative System F<:
and its derivation-directed elaboration into `SystemFCo`.

Both source and target use one heterogeneous binder signature. A source bound
`X <: B` elaborates to two target declarations: a type variable `X` and a
coercion variable `c : X => B`. Source subtyping derivations become target
coercion syntax; source subsumption becomes an explicit target cast; and a
bounded type abstraction becomes a type abstraction followed by a coercion
abstraction. The compiler theorem is split into:

- `elaborateSubTyping`: generated coercions are well typed; and
- `elaborateTermTyping`: generated target terms preserve source types.

`ElaborationRegression.lean` exercises bound evidence and explicit casts.
`ElaborationAllRegression.lean` exercises full bounded-universal subtyping,
including polymorphic, qualified, and arrow coercions.

Type preservation of elaboration plus target safety is not, by itself, a
source soundness theorem: target cast steps may be administratively silent.
The operational layer therefore maps both languages to an intrinsically
scoped common runtime. It proves forward erasure, lifts runtime steps back to
finite target reductions, and reflects source stuckness. The final theorem is:

```text
source_not_goesWrong : empty |- t : T  ->  not (GoesWrong t)
```

`ElaborationSafetyRegression.lean` applies this theorem to both closed source
regressions, rather than merely proving safety of their compiled targets.

Build with:

```sh
lake build SystemFSub
```
