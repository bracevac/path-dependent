# LambdaPFC

`LambdaPFC` explores an evidence-passing account of subtyping for LambdaP.  It
is a separate Lean library and leaves the proved `LambdaP` development
unchanged.  Both libraries are checked by `lake build`.  System FC supplies the
design precedent for typed, erasable coercion syntax; the codes here are
directed witnesses of inclusion.

## First checkpoint: dependent pairs

The first checkpoint isolates covariance of dependent pairs with proper
members.  Its source rule has the following form:

\[
\frac{
  S <: S'
  \qquad
  T <: T'
}{
  \mathsf{Pair}(S, a, x.T) <: \mathsf{Pair}(S', a, x.T')
}
\]

The member premise is intrinsically scoped beneath the binder for the first
component and records the assumed type `S`.  Evidence elaboration records it
as an abstraction:

\[
\frac{
  c_1 : S \Rightarrow S'
  \qquad
  c_2 : \mathsf{abs}\;S\;(T \Rightarrow T')
}{
  \mathsf{pair}(c_1,c_2) :
  \mathsf{Pair}(S,a,x.T) \Rightarrow
  \mathsf{Pair}(S',a,x.T')
}
\]

The interpretation of `c_2` is delayed until a concrete pair is available.
If its first component is the runtime location `y`, the interpreter extends
the current valuation with `x = y` and applies the member evidence in that
extended environment.  This is the point at which the evidence-passing proof
differs from a proof that first opens the member types at a statically known
singleton path.

The abstraction has a primitive bound rule

\[
\mathsf{bound}_S : \mathsf{Single}(x) \Rightarrow S,
\]

whose interpretation consumes the premise that the actual first component
realizes `S`.  Together with first-component widening, it derives the general
conversion

\[
\mathsf{Pair}(S,a,x.\mathsf{Single}(x))
<:
\mathsf{Pair}(\mathsf{Top},a,x.S).
\]

The development currently proves:

- erasure of evidence to the source subtyping relation;
- existence of evidence for every derivation in the source fragment;
- a semantic action theorem for every evidence term;
- the unrestricted dependent-pair case for the source fragment;
- preservation of the underlying runtime location and both pair observations
  when evidence is applied; and
- an inhabited regression
  `Pair Top (fun x => Single x) <: Pair Top (fun _ => Top)`.

The regression uses `Top` for the source first-component type, so the member
conversion cannot be obtained from LambdaP's singleton-first pair rule.

## Second checkpoint: one abstract member

`Member.lean` represents a realized member `p.A : L..U` by a recorded witness
`W`, path-resolution evidence for `p.A = W`, and two directed evidence terms:

\[
L \Rightarrow W
\qquad\text{and}\qquad
W \Rightarrow U.
\]

Introduction at the lower bound and elimination at the upper bound apply these
evidence terms without changing the runtime location.  `MemberProbe.lean`
checks an inhabited instance in which the lower bound is a singleton type and
the recorded witness is `Top`.

The second checkpoint is one hop.  The evidence stored in a
member package belongs to the structurally interpreted fragment from the first
checkpoint.  If stored evidence may itself select another abstract member, a
recursive interpreter would invoke evidence that is not a subterm of the
current evidence term.

## Third checkpoint: operational coercions

`CoercionMachine.lean` gives selection evidence an operational semantics.
Coercion code consists of static evidence, composition, lower-bound selection,
and upper-bound selection.  A typed runtime world supplies a canonical witness
and lower and upper coercion code for every checked member.  The machine uses a
typed continuation stack.  Lower-bound selection schedules the stored lower
code followed by a frame that hides the witness; upper-bound selection reveals
the witness and schedules the stored upper code.  Retrieved code is never
interpreted by a recursive call in the selection step.

The mechanized results are:

- erasure from coercion code to an extended source subtyping relation;
- determinism of runtime path and member lookup;
- intrinsic type preservation of every machine step;
- typed progress;
- preservation of the runtime location by one step and by finite executions;
- final-state inversion; and
- extraction of a target realization from any finite run to a final state.

`CoercionProbe.lean` constructs a concrete member world and checks terminating
lower- and upper-bound selection runs.  The world exposes the stored coercion,
subsequent steps execute it and hide or reveal the witness, and the final state
realizes the declared target at the original runtime location.

General normalization remains open.  The small `Model` type used in these
checkpoints is a finite function and admits cyclic references, whereas the
LambdaP store is append-only.  A full argument must construct the coercion
world from that stratified store and derive a decreasing rank for retrieved
evidence.  Preservation and progress alone would permit infinite evidence-only
execution and would therefore be insufficient to obtain the target
realization.  The present machine obtains code from `CoWorld.lower` and
`CoWorld.upper`; connecting those operations to concrete runtime path lookup
and the source store-typing judgment is also open.

## Scope

This checkpoint covers `Top`, `Bot`, singleton realization and bound widening,
runtime path resolution, and dependent pairs whose member has kind `star`.
The source fragment omits singleton aliasing and the full context-sensitive
path-typing rules.  The semantic realization relation has constructors for the
inhabited forms needed by the probes.

Functions, term reduction, progress, preservation for the source machine, and
an elaboration theorem from the complete LambdaP subtyping relation are also
outside the current checkpoint.  Accordingly, `LambdaPFC` does not yet claim
type soundness for LambdaP.  The operational code grammar also still lacks a
general dependent-pair constructor whose open member body may itself contain
selection coercions; `static` currently embeds only the first checkpoint's
selection-free pair evidence.

## Files

- `Evidence.lean` defines the source fragment, evidence sorts, evidence terms,
  and evidence erasure.
- `Model.lean` defines runtime path resolution, positive realization, evidence
  action, typed casts, and observations.
- `PairProbe.lean` contains the inhabited unrestricted-covariance regression.
- `Member.lean` defines packages with recorded witnesses and evidence for their
  bounds.
- `MemberProbe.lean` contains the inhabited one-hop abstract-member regression.
- `CoercionMachine.lean` defines selection coercions, canonical member worlds,
  the typed stack machine, finite execution, and conditional result extraction.
- `CoercionProbe.lean` contains concrete terminating lower- and upper-selection
  executions.
