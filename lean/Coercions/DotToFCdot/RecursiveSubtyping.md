# Recursive subtyping: bounded evidence experiments

[RecursiveSubtyping.lean](RecursiveSubtyping.lean) constructs FCdot coercions for two recursive-subtyping principles. It does not extend `DotMNF.Sub` or `WadlerFest.Sub`, and does not establish support for the Rompf--Amin calculus.

## Published rules and their scope

Rompf and Amin's BINDX and BIND1 rules have the following premises:

\[
\frac{\Gamma,z:S(z)\vdash S(z)<:T(z)}
     {\Gamma\vdash\mu z.S(z)<:\mu z.T(z)}
\qquad
\frac{\Gamma,z:S(z)\vdash S(z)<:U}
     {\Gamma\vdash\mu z.S(z)<:U}
\quad(z\notin\mathrm{FV}(U)).
\]

Their selection rules use a separate path-typing judgment that excludes VARPACK. Selection also restricts the context: bindings introduced by subtyping after the selected variable are discarded. Ordinary term bindings and temporary subtyping bindings must therefore be distinguished. There is no symmetric BIND2 rule. The paper conjectures that these restrictions might be removed without losing soundness; its proof does not establish that extension. The calculus also has methods, unions, and general method applications, so these recursive rules cannot by themselves identify it with the present source calculus. See [*Type Soundness for Dependent Object Types (DOT)*, Figure 1, section 3, and sections 6.2/6.5](https://namin.seas.harvard.edu/files/soundness_oopsla16.pdf).

## Checked coercions

`project_typed` establishes target evidence for

\[
\mu z.(T\land U(z))\;<:\;T\qquad(z\notin\mathrm{FV}(T)).
\]

`T` is arbitrary and may depend on outer variables. Its independence from the recursive self is enforced by scope: the body contains `T.weaken`. An object-shaped `T` is obtained by copying its translated telescope. Otherwise the coercion extracts its closed self-bound. This is a BIND1 instance whose premise is intersection elimination.

`width_typed` establishes target evidence for

\[
\mu z.(S(z)\land U(z))\;<:\;\mu z.S(z)
\]

when `S` is declaration-shaped. `S` may contain self-dependent member bounds and field types. This restriction ensures that its self telescope contains no self-bounds, so the existing identity morphism can copy its propositions. `U` is unrestricted. This is a BINDX instance whose premise is intersection elimination.

`projectCodomain_typed` uses the first coercion below a dependent function codomain. The retained result may depend on the function parameter. Thus the experiment addresses a use of recursive subtyping that cannot be expressed merely by wrapping an existing variable in Rec-I/Rec-E.

All three statements hold in an arbitrary target context. Their evidence uses existing `.obj`, `.bound`, and `.pi` constructors; target normalization and preservation are unchanged. Installing these principles as source rules would still require extending the translation and its proofs. That integration is outside this experiment.

## A concrete obligation for general BINDX

`Chain.premise` checks the following opened-self subtyping derivation in the existing annotated source rules. `Chain.premise_labelSorted` certifies every judgment in this derivation, including intermediate types, so the premise belongs to the public label-sorted source:

\[
\begin{aligned}
S(z)&=(\{A:\bot..z.B\}\land\{B:\bot..\top\})\land\{a:z.A\},\\
T(z)&=\{B:\bot..\top\}\land\{a:z.B\},\\
z:S(z)&\vdash S(z)<:T(z).
\end{aligned}
\]

The target field proposition requires composing two facts from the same receiver: `z.a <= z.A` and `z.A <= z.B`. Current object templates contain one source hole, with both additional coercion sides closed with respect to the self binder. They do not directly provide this construction. This identifies a translation obligation, not a nonexpressibility theorem or an unsoundness counterexample.

A bounded next experiment is to permit finite compositions of source holes and prove their interpretation against a receiver view. One route to general BINDX would abstract over receiver evidence and require a normalization argument for instantiation. Existing typed atom substitution is relevant, but recursive atom wrappers alone do not discharge the fresh receiver into a closed coercion. Simply importing unrestricted BINDX would leave these obligations unresolved; no unsoundness counterexample to that exact source-assumed rule is claimed here.

## Verification

The module was checked with Lean 4.29.1 against the existing development. A `#print axioms` audit reports only `propext` and `Quot.sound` for `project_typed`, `width_typed`, and `projectCodomain_typed`. `Chain.premise` and `Chain.premise_labelSorted` depend on no axioms. There are no `sorry`, `admit`, or added axioms.
