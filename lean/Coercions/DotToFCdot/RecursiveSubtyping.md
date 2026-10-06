# Recursive subtyping and finite compositions of self facts

[RecursiveSubtyping.lean](RecursiveSubtyping.lean) constructs FCdot coercions for two recursive-subtyping principles and a recursive coercion that composes two facts about self. It does not extend `DotMNF.Sub` or `WadlerFest.Sub`, and does not establish support for the Rompf--Amin calculus.

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

All three statements hold in an arbitrary target context. These three coercions require no additional target constructs: their evidence uses `.obj`, `.bound`, and `.pi`. Installing these principles as source rules would still require extending the translation and its proofs. That integration is outside this experiment.

## Composing two facts about self

`Chain.premise` checks the following opened-self subtyping derivation in the existing annotated source rules. `Chain.premise_labelSorted` certifies every judgment in this derivation, including intermediate types, so the premise belongs to the public label-sorted source:

\[
\begin{aligned}
S(z)&=(\{A:\bot..z.B\}\land\{B:\bot..\top\})\land\{a:z.A\},\\
T(z)&=\{B:\bot..\top\}\land\{a:z.B\},\\
z:S(z)&\vdash S(z)<:T(z).
\end{aligned}
\]

The target field proposition requires composing two facts from the same receiver: `z.a <= z.A` and `z.A <= z.B`. The original object templates contained one source hole, with both additional coercion sides closed with respect to the self binder. A finite composition of such templates now provides the required evidence.

The new morphism rule is:

\[
\frac{
  \Gamma\vdash m:\Psi\Rightarrow\Phi
  \qquad\Gamma\vdash p:\Psi\Rightarrow[S\sqsubseteq M]
  \qquad\Gamma\vdash q:\Psi\Rightarrow[M\sqsubseteq T]
}{
  \Gamma\vdash\operatorname{leTrans}(m,p,q):
  \Psi\Rightarrow\Phi,[S\sqsubseteq T]
}.
\]

Both premise templates read the same source telescope. Their proposition types may mention self. The rule neither extends the typing context with a self assumption nor allows an arbitrary coercion under that assumption. Normalization produces a finite template tree whose leaves read source propositions. `Chain.coercion_typed` uses this rule to establish

\[
\varnothing\vdash e:\llbracket\mu z.S(z)\rrbracket
  \le\llbracket\mu z.T(z)\rrbracket.
\]

`Chain.coercion_normalizes` checks the resulting template tree. The bounds of `B` and presence of `a` are copied; the field upper bound composes source positions 5 and 1.

## Why interpretation remains structural

A composed template is interpreted against an already obtained receiver view. Interpretation recursively obtains the two child forms and composes them. It does not ask the evidence normalizer to reinterpret an arbitrary derivation in a newly constructed self context.

Object-coercion composition substitutes templates for their source holes. Substitution descends into both children of a composed template, and preserves their typing against the original source telescope. The form-algebra proofs extend by the corresponding structural cases. The canonical-forms theorem normalizes each premise morphism by induction on its typing derivation; a singleton-inclusion inversion supplies its typed local template. The preservation, progress, and consistency results continue to use the same canonical-forms theorem.

Thus the added proof work is finite template substitution, typed interpretation, and the additional structural cases of the normalizer. The experiment does not introduce an inertness hypothesis for an arbitrary self context or a second typing relation for reading its assumptions.

The closed regression has `A = (top -> top)`, `B = top`, and an identity-function field `a`. Its precise-to-source coercion also composes templates. `Chain.receiver_typed` checks the composite cast at the allocated object; `Chain.receiver_view` computes the target view, whose field upper bound is the form `top`. This tests both substitution of composed templates and interpretation at an actual receiver.

## Remaining correspondence obligation

The example discharges one concrete recursive-subtyping conclusion. A general BINDX translation would need an extraction theorem: from an opened-self source derivation, construct a finite target template with the corresponding endpoints. The present development proves no such theorem. Recursive elimination, self-dependent bounds, nested recursive types, and the source's companion selection restrictions remain part of that correspondence question. The success of `Chain` alone does not establish that every opened-self derivation has a template in the extended grammar.

## Verification

The module is checked with Lean 4.29.1 against the FCdot development. An axiom audit of canonical forms, preservation, and all new `Chain` theorems reports only `propext` and `Quot.sound`; `Chain.premise` and its label-sortedness certificate depend on no axioms. The new coercions are checked by the proof-producing executable checker, and the normalization and concrete-view equalities are kernel-checked computations using the defining equations. There are no `sorry`, `admit`, or added axioms.
