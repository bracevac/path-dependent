# LambdaPFC Metatheory

This note gives a TAPL-style account of the progress and preservation proofs
for `LambdaPFC`. It states the mathematical argument explicitly and records
how each traditional proof ingredient is represented in Lean.

The central result is:

~~~text
∅ ⊢ t : T        initial(t) →* c
────────────────────────────────
       c is final or can step
~~~

The proof has the familiar progress-and-preservation shape, but its invariant
is adapted to a store-indexed, path-dependent CK machine.

## 1. High-level overview

### 1.1 The calculus and machine in one page

LambdaPFC terms are in monadic normal form. Functions and pairs are values;
applications consume paths; and a let expression names the result of a
computation:

~~~text
p ::= x | p.fst | p.a

v ::= λ(x:S).t | pair y a d

t ::= path p | v | p q | let x = s in t
~~~

The type and member categories used below are:

~~~text
T ::= Top | Bot | (x:S) → T | Pair(x:S, a:τ) | {p} | p.A
τ ::= T | L..U
d ::= val z | type W
~~~

`{p}` is the singleton type containing exactly the location denoted
by `p`. `p.A` is the abstract type obtained by selecting a
type member. A generalized member signature `τ` is either a proper
term type `T` or a type interval `L..U`. A pair value stores
an existing first-component location `y` and either a term-member
location `val z` or a concrete type definition `type W`.

Both function codomains and pair-member signatures are dependent: the result
`T` in `(x:S)→T` and the signature `τ` in
`Pair(x:S,a:τ)` may mention `x`.

A selected path may resolve either to a term location or to a stored type
definition:

~~~text
p ⇓σ loc x          p denotes location x
p ⇓σ type W         p denotes stored type W
~~~

For example:

~~~text
σ(r) = pair f a (val g)
    (var r).fst ⇓σ loc f
    (var r).a   ⇓σ loc g

σ(q) = pair f A (type W)
    (var q).A   ⇓σ type W
~~~

A matching label returns the current cell's member. With a different label,
lookup continues through `.fst`, so nested pair cells form a record
spine: an outer field can be skipped to reach an earlier field.

The machine state `⟨σ,K,t⟩` consists of an append-only store,
a stack of suspended let bodies, and the currently focused term. Values are
allocated only when a continuation is waiting for them. Under an empty
continuation, either a variable location or a syntactic value is already a
final answer.

There are five machine moves. Application opens a stored lambda body; a
non-variable term path canonicalizes to the location it denotes; a let pushes
its body and focuses its bound computation; return opens that frame with an
already existing location; and allocation stores a value at fresh location
`0` before starting the waiting body. These are exactly the cases in the
progress and preservation proofs.

Here `body[x]` means: replace the newest bound variable in
`body` by the location path `var x`. Likewise,
`U[q]` substitutes an arbitrary path `q` for the newest
dependent type variable in `U`. Machine application and return open
binders only with concrete locations; the source application rule may mention
the original argument path in its result type.

Lean represents a location in an `n`-cell store by `Fin n`.
The newest cell is index `0`. Allocation therefore shifts every old
location `i` to `i+1`; applying this shift uniformly to a
term, type, or proof is called *weakening*. For example:

~~~text
σ₁ = [0 ↦ id]
allocate v
σ₂ = [0 ↦ v, 1 ↦ id]

weaken(var 0 in σ₁) = var 1 in σ₂
~~~

### 1.2 A small execution to keep in mind

Let:

~~~text
F  = Top → Top
id = λ(x:Top). path x

program = let f = id in path f
~~~

The typing derivation uses singleton introduction followed by widening:

~~~text
x:Top ⊢ path x : {x}       {x} <: Top    [s-widen]
──────────────────────────────────────
        x:Top ⊢ path x : Top
──────────────────────────────────────
           ∅ ⊢ id : F

f:F ⊢ path f : {f}         {f} <: F      [s-widen]
──────────────────────────────────────
          f:F ⊢ path f : F
──────────────────────────────────────
          ∅ ⊢ program : F
~~~

Routine well-formedness premises are omitted. In the first subsumption there
is also a direct `{x}<:Top` derivation via the top rule, but this
example deliberately chooses singleton widening. Because subtyping evidence
is proof-relevant, that choice later compiles to `c-widen` rather
than `c-top`.

The last line uses the source let rule:

~~~text
∅ ⊢ id : F       f:F ⊢ path f : F
──────────────────────────────────── t-let
 ∅ ⊢ let f=id in path f : F
~~~

The right premise is checked with a hypothetical variable `f:F`.
At runtime there is no location for that variable yet: the machine must first
evaluate `id` and learn where its result lives.

This is the first important difference from a simply typed canonical-forms
proof: a path term is introduced at a singleton, and its useful interface is
obtained through subtyping.

In named notation the execution is:

~~~text
⟨empty, [], let f=id in path f⟩
    →let_push
⟨empty, [path f], id⟩
    →allocate
⟨σ₁, [], path (var 0)⟩

where σ₁ = [0 ↦ id]
~~~

The final state is a live location under the empty continuation.

This short trace already contains most of the preservation architecture:

- Operationally, `let_push` puts the open body `path f` on
  the control stack and focuses `id`. That stack entry means:
  “when the bound computation produces a location usable at `F`,
  continue by letting `f` denote that location.”
- On the proof side, the typing evidence for the whole let already contains
  three pieces: evidence that `id:F`; the proof of
  `f:F ⊢ path f:F` together with the current environment; and any
  final subsumption applied to the let result. Preservation keeps the first
  piece as the typing evidence for the newly focused term and attaches the
  other two pieces to the new stack entry.
- `allocate` extends the store, weakens old evidence, and makes
  fresh location `0` realize `F`;
- the body is already intrinsically scoped at one additional location, so the
  transition does not perform a textual substitution—the fresh slot
  `0` now denotes the allocated value;
- the final path is typed from its singleton `{var 0}` and widened
  to the stored function type.

If the body were `let g = path f in path g`, the inner bound
computation would finish at the existing location `f`. The machine
would use `return`, not allocate a duplicate cell: it opens the
suspended body with that existing location.

### 1.3 Two typing levels

The source layer contains the declarative judgments:

~~~text
Γ ⊢ p ⇒ τ       precise path typing
Γ ⊢ τ <: τ′     subtyping
Γ ⊢ τ wf        well-formedness
Γ ⊢ t : T       term typing
~~~

Execution, however, introduces concrete store locations, and allocation
changes the intrinsic scope of every term and type. The runtime layer
therefore records what the current store actually supports:

~~~text
ρ ⊨σ Γ               valuation ρ realizes source context Γ in σ
σ ⊨ x : T            location x realizes T
σ ⊢tm t : T          normalized runtime term evidence
σ ⊢K K : S ⇒ T       continuation evidence
⊢ ⟨σ,K,t⟩ : T        complete state evidence
~~~

Preservation does not reconstruct a source derivation
`Γ ⊢ t′ : T` after each step. Instead, the outer source derivation
is interpreted into store-local evidence, and progress and preservation are
proved for that evidence. Derivations saved beneath function, let, and pair
binders are interpreted or compiled later, when execution supplies their
concrete binder locations.

Crucially, this interpretation consumes the **typing derivation**, not merely
the term syntax:

~~~text
code : Γ ⊢ t : T        env : ρ realizes Γ in σ
────────────────────────────────────────────────
interpret(code,env) : σ ⊢tm ρ(t) : ρ(T)
~~~

The same source term can have different derivations because subsumption can
be proved in different ways. `interpret` follows the chosen
derivation, and each subtyping subderivation is compiled into a corresponding
`Coercion`. This is proof computation inside Lean; it is not an
interpreter executed by the object-language CK machine. Runtime states contain
only a store, continuation bodies, and a term—never typing proofs or casts.

### 1.4 The runtime invariant in plain language

The names in the Lean development are compact, so it helps to say what each
one certifies.

**`Environment Γ ρ σ`** says that every free source variable is
already mapped by `ρ` to a location in `σ` realizing
the type recorded for it in `Γ`.

**`Store.Possible σ x T`** is a canonical-form certificate for
location `x`. It records enough store structure to use the same
location at type `T`:

- at `Top`, no further observation is needed;
- at a function type, it exposes an actual stored abstraction, a saved body
  derivation, an input adapter, and a deferred result adapter;
- at a pair type, it exposes the stored pair plus realizations of its first
  component and member;
- at a singleton type, it records a path resolving to `x`;
- at a selected type, it records the selected stored type and evidence that
  `x` realizes it.

There is deliberately no certificate for `Bot`.

**`Path.Referent.Realizes σ r τ`** extends this idea to both kinds
of path result. A proper type is realized by a location. An interval
`L..U` is realized by a stored type `W` together with:

~~~text
L ⇝ W ⇝ U
~~~

**`Coercion σ τ τ′`** is a finite metatheoretic adapter. It does
not change the store, the referent, or the running term. Its action transforms
only the certificate:

~~~text
C : σ ⊢ τ ⇝ τ′       R : σ ⊨ r : τ
─────────────────────────────────────
          action(C,R) : σ ⊨ r : τ′
~~~

Finally, the three closure families postpone reasoning beneath binders. A
closure here is proof data, not an object-language value. It pairs a
derivation containing one hypothetical variable with the already interpreted
environment for all its other variables. To *instantiate* the closure is to
supply the concrete store location that replaces that hypothetical variable.

For a body closure, the essential before-and-after picture is:

~~~text
saved:
    code : Γ,x:S ⊢ body : T
    env  : ρ realizes Γ in σ

later:
    arg  : σ ⊨ y : ρ(S)
────────────────────────────────
    σ ⊢tm ρ(body)[y] : ρ(T)[y]
~~~

So it is almost right to say that a closure captures “the derivation and the
runtime store.” More precisely, it captures the derivation plus a semantic
environment whose locations are certified in a particular store, and the
closure itself is indexed by that store. It does not copy the store as an
independent field. Because stores only grow, weakening transports the closure
and its environment when allocation extends the store.

| Closure | Saved information | Later instantiated when |
|---|---|---|
| `BodyClosure` | Body typing and its outer environment | Beta, return, or allocation supplies an argument location |
| `DeferredCoercion` | Function-codomain comparison under a binder | Function application supplies the argument location |
| `MemberClosure` | Dependent pair-member comparison | Pair realization exposes its stored first-component location |

`TermEvidence` packages syntax-directed runtime term evidence. Its
four forms carry:

| Focused term | Evidence retained |
|---|---|
| `path p` | a resolution `p ⇓σ loc x` and a suffix `{p} ⇝ T` |
| a value | its abstraction/pair introduction evidence and a suffix to `T` |
| `p q` | operator evidence, argument evidence, the dependent codomain `U`, and `U[q] ⇝ T` |
| `let x=s in body` | evidence for `s`, a body closure waiting for `x`, and a result suffix |

A runtime continuation `K` is just a list of open let bodies. The
separate judgment

~~~text
σ ⊢K K : S ⇒ T
~~~

says: if the focused computation produces a location usable at `S`,
then the suspended bodies in `K` can safely resume and eventually
produce an answer of type `T`. The empty continuation maps a type to
itself. A nonempty continuation records a `BodyClosure` for its
first body, a coercion from that body's result to the type expected by the
remaining frames, and evidence for the remaining frames.

Its two rules are:

~~~text
──────────────────────────── hole
σ ⊢K [] : T ⇒ T

σ ⊢K K : U ⇒ T
BodyClosure σ S body V.weaken
σ ⊢ V ⇝ U
──────────────────────────── cons
σ ⊢K body::K : S ⇒ T
~~~

`State.Evidence` combines term evidence
`σ ⊢tm t:S` with continuation evidence
`σ ⊢K K:S⇒T`. The intermediate `S` may change when the
machine changes focus; the final answer type `T` is what
preservation tracks.

Source subsumption may occur anywhere in a typing derivation. Runtime term
evidence normalizes it into one suffix coercion attached to the outer
syntax-directed constructor. Thus path evidence always exposes a resolution
plus a singleton-to-result coercion; application evidence exposes its
operator, argument, codomain, and result coercion; and let evidence exposes
its bound computation, body closure, and result coercion. Value evidence
exposes the abstraction or pair introduction data plus its result coercion.
Progress and preservation can invert these four evidence forms directly
without first peeling off an arbitrary number of subsumption rules.

### 1.5 How coercions work

Coercions are proof-executable semantic evidence, not casts in the object
language. The CK machine never evaluates a coercion.

#### Singleton widening

A path term is introduced at its singleton type. If `p ⇓σ loc x`
and `σ ⊨ x:T`, widening builds:

~~~text
{p} ⇝ T
~~~

Acting on the singleton certificate for `p` recovers the existing
certificate `σ ⊨ x:T`. In the running example, this is how
`path (var 0)` is viewed at `F`.

#### Aliases

If paths `p` and `q` both resolve to the same location,
alias coercion gives:

~~~text
{q} ⇝ {p}
~~~

This does not claim that the paths are syntactically equal. It records only
the runtime fact needed to transport singleton evidence. Preservation uses
this when a compound path steps to its canonical location variable.

Runtime path equality is also lifted structurally through types and
signatures. Consequently, if `q` and `var y` resolve to the same referent,
the proof can transport an entire dependent codomain `U[y]` to `U[q]`, not
merely convert `{var y}` to `{q}`.

#### Function coercion

To view a function `Fun S U` at
`Fun S′ U′`, function subtyping supplies:

~~~text
S′ ⇝ S                         contravariant input adapter
U ⇝ U′ under a binder S′       deferred result adapter
~~~

Suppose the location actually stores `λ(x:A).body`. Its existing
function certificate already contains an adapter from `S` to
`A`. Coercion action prepends `S′ ⇝ S` to that input
adapter. It narrows the saved output evidence accordingly and postpones the
dependent codomain comparison until a concrete argument location is known.
The stored lambda and store binding do not change.

For example, let `F=Top→Top` and
`L=F→Top`. Contravariance gives `F <: L`. After
allocating `id:F`, an operator path may carry the suffix:

~~~text
{f} ⇝ F ⇝ L
~~~

Applying that suffix changes the certificate from “`f` names this
location” to “this location can be called as an `L`.” Inverting
the resulting function certificate still exposes the same stored
`id` abstraction.

Concretely, the function-subtyping premises are `F<:Top` for the
contravariant domain and `Top<:Top` for the result. The same
`path f` can be widened to `F` as the argument, giving:

~~~text
f:F ⊢ path f : L       f:F ⊢ path f : F
─────────────────────────────────────────
              f:F ⊢ f f : Top
~~~

Thus `let f=id in f f` is a closed instance of the application case.

#### Selection and dependent pairs

If `p.A` resolves to stored type `W` with interval
evidence:

~~~text
L ⇝ W ⇝ U
~~~

then selection coercions implement `L <: p.A` and
`p.A <: U`.

For `Pair S a d <: Pair S′ a d′`, the first-component coercion can
run immediately. The comparison `d <: d′` cannot: both signatures
refer to the pair's bound first component. It is stored as a
`MemberClosure` and instantiated only after pair inversion reveals
the actual first-component location.

### 1.6 What technical problems this design localizes

The semantic layer does not make the hard dependent reasoning disappear. It
concentrates each issue in one explicit mechanism:

| Problem in a direct TAPL proof | LambdaPFC mechanism |
|---|---|
| Arbitrary subsumption obscures the last typing rule | Normalize it into one suffix coercion |
| A path of function type need not syntactically be a lambda | Resolve it, execute its suffix, then invert function realization |
| Beta replaces source path `q` by resolved location `y` inside a dependent codomain | Use runtime path equality to transport `U[y]` to `U[q]` |
| Function and let bodies, and pair members, are typed beneath dependent binders | Save closures and instantiate them only at concrete locations |
| Allocation shifts every old `Fin` index | Use a heterogeneous step relation and weaken each part of the evidence uniformly |
| Pair coercion descends through stored older referents | Use append-only store strata plus coercion-tree size for termination |
| Operational premises live in `Prop` while evidence lives in `Type` | Return evidence under `Nonempty` |

This avoids a monolithic dependent substitution theorem, a global store-typing
judgment threaded through every rule, and cast terms in the runtime language.
The cost is concentrated in typed path resolution, coercion action, closure
instantiation, and the allocation case.

### 1.7 What this sidesteps relative to the DOT literature

“Sidesteps” has two importantly different meanings here:

1. some traditional proof obligations are **replaced by local semantic
   operations**; the reasoning still exists, but in a different form;
2. other obligations are **absent because LambdaPFC omits the feature** that
   creates them.

Confusing these would make the proof sound more general than it is.

#### Bad bounds and inversion through transitivity

The classic DOT difficulty begins with an abstract member:

~~~text
x : { A : L..U }

L <: x.A       x.A <: U
──────────────────────
        L <: U
~~~

If the assumed object type has incompatible bounds, a context can manufacture
an unintended subtyping fact. This is the “bad bounds” problem. A separate
but adjacent difficulty is inversion in the presence of explicit
transitivity: a derivation may end in arbitrarily many transitivity and
subsumption steps, so inspecting a term of function type no longer directly
reveals a function-introduction rule.
DOT soundness proofs recover usable inversion only in suitably constrained
runtime contexts, for example through transitivity pushback, precise typing,
or the inert/tight-typing decomposition
([Rompf and Amin 2016](https://doi.org/10.1145/2983990.2984008);
[Rapoport et al. 2017](https://doi.org/10.1145/3133870)).

LambdaPFC does not prove that arbitrary source subtyping is invertible.
Instead:

- the selection-subtyping and well-formed-interval rules require an explicit
  proof that `L <: U`;
- a realized interval contains an actual stored witness `W` and
  coercions `L ⇝ W` and `W ⇝ U`;
- an `Environment` can interpret a source context only when every
  binding has corresponding runtime realization evidence;
- transitivity compiles directly to coercion composition; and
- progress first executes the accumulated coercion and then inverts the
  resulting `Store.Possible` certificate.

Thus canonical forms are proved for a realized store location, not by
normalizing or inverting an arbitrary declarative subtyping derivation. The
bad-bounds issue is localized at realization and interval construction; it is
not solved for the richer recursive and intersection-heavy contexts of full
DOT. In fact, requiring `L <: U` independently means an abstract member
cannot introduce a fresh custom subtyping relation as it can in full DOT.
That is a genuine expressiveness restriction, not merely a different proof
of the same language.

#### Global narrowing and a general typing-substitution theorem

In textbook preservation, beta reduction normally invokes:

~~~text
Γ,x:S ⊢ body : T       Γ ⊢ v : S
─────────────────────────────────
        Γ ⊢ body[v/x] : T[v/x]
~~~

For DOT-like systems, general environment narrowing and substitution interact
with path selections, abstract bounds, and transitivity; some rich systems do
not satisfy the usual lemmas in unrestricted form
([Amin and Rompf 2017](https://doi.org/10.1145/3009837.3009866)).

LambdaPFC needs only the runtime instances that execution actually reaches.
A `BodyClosure` retains the open typing derivation until a concrete
argument location is known. It then extends the semantic environment with
proof that this location realizes `S` and reruns the fundamental
interpretation. `DeferredCoercion` does the analogous job for a
function codomain, while `MemberClosure` waits for the first
component stored in a pair.

`BodyClosure` and `MemberClosure` replace the needed syntactic
binder-substitution instances. For functions, `DeferredCoercion.narrow`
records the domain adjustment explicitly, and later instantiation performs
only the corresponding location-specific narrowing step. The development
therefore needs neither one large syntactic substitution theorem nor a global
narrowing theorem. It does **not** eliminate substitution reasoning: it still
proves the renaming, opening, and weakening equations needed to show that the
instantiated syntax and types are the expected ones.

#### Arbitrary path replacement and path termination

Fully path-dependent pDOT showed that naively allowing any path before a type
selection is unsound: the path might fail to reach a value whose concrete
member witnesses its advertised bounds. pDOT therefore carefully restricts
which paths may occur in types and develops singleton propagation and a
source-level path-replacement relation
([Rapoport and Lhoták 2019](https://doi.org/10.1145/3360571)).

LambdaPFC makes a narrower choice. A path contains only a variable, first
projections, and selections through immutable pair cells—never a method call,
arbitrary computation, or mutable field. Pair references point to older
store entries. Typed path resolution consequently produces the concrete
referent and its realization together.

Alias reasoning is still necessary, but it is store-indexed:

~~~text
p ⇓σ r       q ⇓σ r
───────────────────
        p ≈σ q
~~~

Structural runtime conversion then transports an entire dependent type along
`p ≈σ q`. This centralizes the replacement needed by beta and pair
selection. It does not provide a source-level normalization or replacement
algorithm for arbitrary potentially nonterminating paths.

#### Recursive self types and step indexing

Recursive objects can make semantic realization circular: proving that an
object realizes its recursive type may require assuming the same fact about
the object. For its richer combination of recursive self types and
impredicative type members, gDOT uses a guarded, step-indexed logical relation
in Iris
([Giarrusso et al. 2020](https://doi.org/10.1145/3408996)).

LambdaPFC has no recursive type, self type, `fix`, or `letrec`.
Moreover, both referents stored in a pair predate the pair cell. Therefore
coercion action can recurse using the concrete allocation order:

~~~text
if σ(x) = pair y a d, then
    stratum(loc y) < stratum(loc x)
    stratum(referent(d)) < stratum(loc x)
~~~

Coercion-tree size handles recursive calls at the same referent. Avoiding
step indexing is therefore a benefit of the acyclic calculus restriction,
not evidence that the same rank would handle recursive DOT—or that every
recursive DOT proof must use step indexing.

#### Mutation and global heap typing

Mutation adds a second evolving invariant: the contents of every heap cell
must continue to agree with its assigned type after an update. Mutable DOT,
for example, adds an explicit store typing used by its canonical-forms and
substitution arguments
([Rapoport and Lhoták 2016](https://arxiv.org/abs/1611.07610)). Its types
deliberately do not depend on mutable heap locations, so it illustrates the
heap-typing obligation rather than mutable path-dependent selection itself.

LambdaPFC's store is immutable and append-only. Existing bindings and path
resolutions never change. Instead of maintaining one global
“every cell has its declared type” judgment, the proof carries local
`Store.Possible` certificates for exactly the locations it uses.
Allocation establishes the new certificate and uniformly weakens old
evidence. This does not address assignment, deallocation, cyclic
initialization, or concurrency.

#### Runtime casts and coercion coherence

Derivation-directed coercion translations often put casts into an
intermediate language; System FC, for example, has explicit equality evidence
designed to be erased before execution
([Sulzmann et al. 2007](https://doi.org/10.1145/1190315.1190324)).
Such translations may also need a coherence result saying that different
derivations induce observationally equivalent programs.

LambdaPFC's coercions are proof objects only. Every coercion must preserve
realization of the **same referent**, but coercions never appear in
`Tm` or in a machine transition. The soundness proof therefore needs
neither cast-preservation cases nor an erasure theorem. It also does not prove
that two derivations of the same subtyping judgment compile to equal
coercions; type safety requires each compiled coercion to be valid, not
coherent as executable code.

#### Other cases absent from the baseline

Several additional simplifications come directly from the grammar:

- monadic normal form makes application operands paths, so there are no
  left/right evaluation-context cases;
- pair components are already allocated locations or stored types, so member
  initializers do not evaluate inside a pair;
- let result types are formed outside the bound variable and merely weakened
  beneath it, so a local let variable cannot escape in the answer type;
- the baseline has no recursion, mutation, polymorphism, intersection,
  union, capture checking, exceptions, or pattern matching.

The intersection/union and capture variants elsewhere in this repository
explore some of those dimensions separately. The baseline theorem here should
not be read as covering them.

The honest summary is:

~~~text
arbitrary global syntactic obligation
            ↓
local reasoning at one realized store, referent, or binder location
~~~

What remains substantial is exactly the bridge: typed paths must resolve,
every source subtyping derivation must compile, every coercion must preserve
realization, all evidence must survive allocation, and the five machine steps
must preserve the complete state invariant.

### 1.8 Proof pipeline

The overall flow is:

~~~text
source typing Γ ⊢ t : T
          +
environment ρ satisfying Γ in σ
          │
          ▼
normalized term evidence σ ⊢tm ρ(t) : ρ(T)
          │
          ▼
state evidence ⊢ ⟨σ,K,t⟩ : T
       ┌──┴───────────────┐
       ▼                  ▼
    progress       one-step preservation
                          │
                          ▼
                 finite preservation
                          │
                          ▼
                     type safety
~~~

For a closed term, both the source context and initial store are empty, so the
interpretation immediately supplies evidence for the initial state.

## 2. Operational and semantic notation

Write:

~~~text
p ⇓σ r                path p resolves in store σ to referent r
σ(x) = v              store σ binds location x to value v
σ ⊨ x : T             location x realizes proper type T
σ ⊨ r : τ             generalized referent r realizes signature τ
σ ⊢ τ ⇝ τ′            semantic coercion from τ to τ′
σ ⊢tm t : T           normalized runtime term evidence
σ ⊢K K : S ⇒ T        K maps a current result S to final result T
⊢ ⟨σ,K,t⟩ : T         complete state evidence
~~~

State evidence has one rule:

~~~text
σ ⊢tm t : S       σ ⊢K K : S ⇒ T
──────────────────────────────────
       ⊢ ⟨σ,K,t⟩ : T
~~~

Thus `S` is the focused term's current type, whereas `T` is the answer
type of the entire continuation.

### 2.1 Reading the invariant on the running example

Let `F₀` denote `F` in the empty-store scope. Before the
first step, source interpretation has produced the following proof objects:

~~~text
Eid   : empty ⊢tm id : F₀

Bbody : BodyClosure empty F₀ (path f) F₀.weaken
        -- if given a location of type F₀, the open body is safe

Crefl : empty ⊢ F₀ ⇝ F₀

Elet  : empty ⊢tm (let f=id in path f) : F₀
      = let(Eid, Bbody, Crefl)

K₀    : empty ⊢K [] : F₀ ⇒ F₀
      = hole

state = ok(K₀, Elet)
~~~

`Bbody` deserves emphasis. It does not yet prove a closed runtime
term `path f`, because `f` has no store location.
It retains the source premise `f:F ⊢ path f:F` and the environment
for every variable outside that binder. Later it can turn that premise into
runtime term evidence once supplied with a concrete location realizing
`F₀`.

Operationally, `let_push` performs:

~~~text
⟨empty, [], let f=id in path f⟩
    →
⟨empty, [path f], id⟩
~~~

The stack contains only the open body syntax. The semantic proof that this
stack is safe is kept separately. Preservation rearranges the objects above
as follows:

~~~text
new term evidence:
    Eid : empty ⊢tm id : F₀

new continuation evidence:
    K₁ = cons(K₀, Bbody, Crefl)
       : empty ⊢K [path f] : F₀ ⇒ F₀

new state evidence:
    ok(K₁, Eid)
~~~

Why does `K₁` have that type? If the focused computation returns a
location realizing `F₀`, `Bbody` can instantiate
`f` with that location and produce the body at
`F₀.weaken`. The weakening disappears again when the body is opened
at an existing old-store location; `Crefl` adapts the resulting
`F₀` to the input `F₀` expected by `K₀`.
Thus the new frame maps the result of `id` to the same final answer
type as the original let.

The focused term is a value and a continuation is waiting, so the next rule
is allocation. Write `F₁=F₀.weaken` for the extended-store type.
The machine stores `id` at fresh location `0`, pops the
waiting body, and starts that body in the enlarged store:

~~~text
⟨empty, [path f], id⟩
    →
⟨σ₁, [], path (var 0)⟩
~~~

On the proof side, `Eid` and the fresh store binding construct:

~~~text
σ₁ ⊨ 0 : F₁
~~~

This is the concrete argument that `Bbody` was waiting for.
`BodyClosure.allocate` maps its formal variable `f` to
fresh location `0` and interprets its retained body derivation in
the extended store. Schematically, suppressing the leading reflexive coercion
introduced by source interpretation, the resulting path evidence is:

~~~text
path(
  Resolve.var,
  widen(Resolve.var, σ₁ ⊨ 0 : F₁)
)
~~~

The first field says that `var 0` resolves to location
`0`. The second changes the available singleton view
`{var 0}` into the advertised type `F₁`. With an empty
continuation, the location is final.

In the alias variant, the focused bound term is already
`path (var x)`. The return transition is:

~~~text
⟨σ, body :: K, path (var x)⟩ → ⟨σ, K, body[x]⟩
~~~

Its path evidence shows that existing location `x` realizes the
frame's input type. `BodyClosure.apply` uses that fact to interpret
the body with its formal variable mapped to `x`. No new store cell
is created.

## 3. Fundamental interpretation

### Lemma 3.1: Typed path resolution

If:

~~~text
Γ ⊢ p ⇒ τ       ρ ⊨σ Γ
~~~

then there is a runtime referent `r` such that:

~~~text
ρ(p) ⇓σ r       σ ⊨ r : ρ(τ)
~~~

### Proof

By induction on `Γ ⊢ p ⇒ τ`.

**Variable.** Choose `r=loc ρ(x)`. Variable resolution gives
`ρ(x) ⇓σ loc ρ(x)`, and the semantic environment supplies
`σ ⊨ ρ(x) : ρ(Γ(x))`.

**First projection.** Apply the induction hypothesis to the receiver. Its
precise type is a pair, so inversion of its realization exposes a stored pair
binding, a first-component location `y`, and
`σ ⊨ y:ρ(S)`. The runtime first-projection rule resolves the
projected path to `loc y`.

**Matching selection.** Apply the induction hypothesis to the receiver and
invert its pair realization. The store binding exposes the member referent.
The receiver's first projection and the stored first-component variable both
resolve to the same location, so runtime path equality transports the stored
dependent-member realization to the source rule's opened signature. The
runtime matching-selection rule resolves the selection to that referent.

**Missed-label selection.** Apply the two induction hypotheses: one to the
outer receiver and one to the earlier selection through its first component.
Invert the receiver's pair realization to obtain its first-component
location. Resolution congruence reroots the earlier selection at this
location, and the unequal-label premise supplies the runtime miss rule. The
earlier induction hypothesis already provides the required realization. ∎

This is `Path.Ty.resolve` in
[`SemanticAction.lean`](SemanticAction.lean).

### Lemma 3.2: Subtyping compilation

If:

~~~text
Γ ⊢ τ <: τ′       ρ ⊨σ Γ
~~~

then:

~~~text
σ ⊢ ρ(τ) ⇝ ρ(τ′)
~~~

### Proof

By induction on the source subtyping derivation.

Reflexivity, transitivity, bottom, and top compile to the corresponding
semantic coercions.

For singleton widening, Lemma 3.1 resolves the typed path and supplies the
target realization. For singleton symmetry, resolving a path whose precise
type is another singleton and inverting that singleton realization shows
that both paths resolve to the same location; construct an alias coercion.

For lower and upper type-selection rules, Lemma 3.1 resolves the selected
path to a type referent. Inverting its interval realization exposes the stored
lower and upper coercions, from which `selLo` and
`selHi` are constructed. Their static bound-consistency premises
constrain the source derivations but are not carried into these coercions.

For function subtyping, compile the contravariant domain premise immediately.
The codomain premise remains under a binder, so save its source derivation and
environment as a `DeferredCoercion`.

For dependent-pair subtyping, compile the first-component premise immediately
and save the member premise as a `MemberClosure`. It will be
compiled after the concrete stored first-component location is known.

For interval subtyping, compile the lower and upper coercions. The static
nonempty-bounds premise constrains the source derivation but contributes no
runtime coercion evidence. ∎

This is `Tau.Sub.compile` in
[`SemanticAction.lean`](SemanticAction.lean).

### Theorem 3.3: Source typing interpretation

If:

~~~text
Γ ⊢ t : T       ρ ⊨σ Γ
~~~

then:

~~~text
σ ⊢tm ρ(t) : ρ(T)
~~~

### Proof

By induction on the derivation of `Γ ⊢ t : T`.

**Path.** Typed path resolution produces a referent together with evidence
that it realizes the path's precise signature. Since that signature is a
proper type, the referent must be a location. Construct path evidence with a
reflexive suffix coercion.

**Abstraction.** Save the body derivation and semantic environment in a
`BodyClosure`. Construct abstraction value evidence with reflexive suffix.

**Application.** Apply both induction hypotheses and construct normalized
application evidence. Renaming commutes with opening the dependent codomain,
so the result type is the expected renamed type.

**Term-member pair.** Construct pair-value evidence with reflexive coercion.

**Type-member pair.** Construct type-pair value evidence with reflexive
coercion. The weakening/renaming identity aligns the member interval.

**Let.** Interpret the bound computation using the induction hypothesis. Save
the body derivation and environment in a `BodyClosure`. The final result
coercion is reflexive.

**Subsumption.** The induction hypothesis gives evidence at the source type.
Compile the source subtyping derivation under the semantic environment and
append the resulting coercion with `TermEvidence.cast`. ∎

The Lean proof is `Tm.Ty.interpret` in
[`SemanticFundamental.lean`](SemanticFundamental.lean).

## 4. Supporting lemmas

### Lemma 4.1: Typed path realization

If:

~~~text
σ ⊢tm path p : T       p ⇓σ loc x
~~~

then:

~~~text
σ ⊨ x : T
~~~

### Proof

Normalized path evidence contains:

~~~text
C : σ ⊢ {p} ⇝ T
~~~

The resolution constructs the singleton realization `σ ⊨ x : {p}`.
Executing `C` on that realization yields `σ ⊨ x : T`. ∎

This is `TermEvidence.pathPossibleAt` in
[`SemanticProgress.lean`](SemanticProgress.lean).

### Lemma 4.2: Function canonical forms

If:

~~~text
σ ⊨ f : Fun S U
~~~

then there exist `A`, `body`, and `B` such that:

~~~text
σ(f) = λ(A).body
BodyClosure σ A body B
Cin  : σ ⊢ S ⇝ A
Cout : DeferredCoercion σ S B U
~~~

### Proof

Invert `Store.Possible σ f (Fun S U)`. Because its index is a function type,
the only possible constructor is `Store.Possible.fun`, which contains
exactly the binding, closure, input coercion, and deferred output coercion
above. ∎

This is the semantic counterpart of TAPL's function canonical-forms lemma.
Lean performs this indexed inversion inline in
`TermEvidence.progress` rather than giving it a separate theorem name.

### Lemma 4.3: Body instantiation

If:

~~~text
BodyClosure σ S body T       σ ⊨ x : S
~~~

then:

~~~text
σ ⊢tm body[x] : T[x]
~~~

### Proof

Invert the closure. It contains a source derivation:

~~~text
Γ,z:S ⊢ body : T
~~~

and a saved environment `ρ ⊨σ Γ`. Extend the environment with `z ↦ x`;
the realization premise shows that the extended environment satisfies
`Γ,z:S`. Apply Theorem 3.3 to the saved derivation and simplify renaming
followed by opening. ∎

This is `BodyClosure.apply` in
[`SemanticFundamental.lean`](SemanticFundamental.lean). It replaces the
ordinary term-substitution lemma.

### Lemma 4.4: Deferred codomain instantiation

If:

~~~text
D : DeferredCoercion σ S B U       σ ⊨ x : S
~~~

then:

~~~text
σ ⊢ B[x] ⇝ U[x]
~~~

### Proof

By induction on `D`.

Reflexivity instantiates to reflexivity. Transitivity instantiates both
premises and composes them. A suspended runtime conversion is opened at the
same location path on both sides.

For narrowing, execute the saved domain coercion on `σ ⊨ x:S`,
then apply the induction hypothesis with the converted realization.

For a saved source derivation, extend its environment with the concrete
location realization and compile the codomain subtyping premise in that
extended environment. The renaming/opening equations identify the compiled
types with `B[x]` and `U[x]`. ∎

This is `DeferredCoercion.instantiate` in
[`SemanticAction.lean`](SemanticAction.lean).

### Lemma 4.5: Coercion action

If:

~~~text
C : σ ⊢ τ ⇝ τ′       σ ⊨ r : τ
~~~

then:

~~~text
σ ⊨ r : τ′
~~~

### Proof

By well-founded induction on:

~~~text
(stratum(r), treeSize(C))
~~~

and case analysis on `C`.

Reflexivity, composition, runtime conversion, top, singleton widening and
aliasing, and selection coercions follow from their realization data and
recursive calls on smaller coercions. Bottom is impossible because there is
no location realization of `Bot`.

For functions, retain the same stored abstraction and body closure, compose
the new contravariant domain coercion with the stored input coercion, and
narrow the stored deferred output along that domain coercion before composing
the target codomain evidence.

For dependent pairs, invert the pair realization to expose its stored first
component and member referent. Act on the first-component realization and
instantiate the suspended member coercion at the concrete first-component
location. Execute that instantiated coercion on the stored member realization.
These referents are older than the pair cell, so the primary stratum measure
decreases.

For intervals, compose the lower coercion before the stored lower witness and
the stored upper witness before the new upper coercion. ∎

The implementation is `Coercion.action` in
[`SemanticAction.lean`](SemanticAction.lean).

### Lemma 4.6: Allocation

Suppose:

~~~text
ValueEvidence σ v S
v is a syntactic value
BodyClosure σ S body T
~~~

Let `σ′ = Store.val σ v`. Then:

~~~text
σ′ ⊢tm body : T
~~~

The visible `body` and `T` already live in the
one-larger binder/store scope. Old ambient store evidence is weakened
internally when constructing this result.

### Proof

1. Weaken the value evidence into `σ′`.
2. The fresh binding establishes `σ′(0)=v.weaken`; when using
   named-location notation, this weakening is implicit.
3. Hence location `0` realizes `S.weaken`.
4. Weaken the body closure into `σ′`.
5. Apply it at fresh location `0`.
6. Simplify the composition of lifted weakening and opening at zero:

   ~~~text
   weaken.ext ; openAt 0 = id
   ~~~

The resulting runtime term is exactly the machine target `body`, and
its type is exactly the closure result `T`. For a continuation
frame this result is specialized to `V.weaken`. ∎

This is `BodyClosure.allocate` in
[`SemanticAllocation.lean`](SemanticAllocation.lean).

## 5. Progress

### Theorem 5.1: Runtime progress

If:

~~~text
⊢ ⟨σ,K,t⟩ : T
~~~

then the state is final or there exists `c′` such that:

~~~text
⟨σ,K,t⟩ → c′
~~~

### Proof

Invert state evidence:

~~~text
σ ⊢tm t : S
σ ⊢K K : S ⇒ T
~~~

Proceed by cases on the normalized term evidence.

#### Case P-Path

We have:

~~~text
t = path p
p ⇓σ loc x
C : σ ⊢ {p} ⇝ S
~~~

Proceed by cases on `p`.

If `p = var x`, proceed by cases on `K`.

- If `K=[]`, the state is final by the location-final rule.
- If `K=body::K′`, take the return transition:

  ~~~text
  ⟨σ,body::K′,path (var x)⟩ → ⟨σ,K′,body[x]⟩
  ~~~

If `p=q.fst` or `p=q.a`, it is not a variable. Take the path
canonicalization transition:

~~~text
⟨σ,K,path p⟩ → ⟨σ,K,path (var x)⟩
~~~

using `p ⇓σ loc x`.

For a concrete selection example, suppose:

~~~text
σ(r) = pair f a (val f)
p    = (var r).a
p ⇓σ loc f
~~~

Then `path p` steps to `path (var f)`. The machine does
not rewrite its advertised type. Preservation prepends an alias coercion from
`{var f}` back to `{p}` and retains the old suffix.

#### Case P-Value

`ValueEvidence.isValue` establishes that the term is syntactically an
abstraction or pair. Proceed by cases on `K`.

- If `K=[]`, the state is final.
- If `K=body::K′`, take the allocation transition:

  ~~~text
  ⟨σ,body::K′,v⟩
      →
  ⟨Store.val σ v,weaken(K′),body⟩
  ~~~

#### Case P-App

Application evidence contains:

~~~text
σ ⊢tm path p : Fun S U
σ ⊢tm path q : S
Cresult : σ ⊢ U[q] ⇝ R
~~~

Invert the two path-evidence derivations:

~~~text
p ⇓σ loc f
q ⇓σ loc y
~~~

By Lemma 4.1, `σ ⊨ f : Fun S U`. By Lemma 4.2, `f` is bound to an
actual stored abstraction:

~~~text
σ(f) = λ(A).body
~~~

All premises of the application transition now hold:

~~~text
⟨σ,K,p q⟩ → ⟨σ,K,body[y]⟩
~~~

The argument's type realization is not needed merely to exhibit the step; it
will be used by preservation.

In the function-view example from Section 1.5, the operator suffix is:

~~~text
{f} ⇝ F ⇝ L
~~~

Acting on it leaves the stored `id` unchanged but produces a
function certificate at `L`. Inverting that certificate is the
canonical-forms step which supplies the operational abstraction binding.

#### Case P-Let

Take `let_push` immediately:

~~~text
⟨σ,K,let x=s in body⟩ → ⟨σ,body::K,s⟩
~~~

These cases exhaust `TermEvidence`. Therefore the state is final or can
step. ∎

The Lean proof is `TermEvidence.progress`, lifted through
`State.Evidence.progress`, in
[`SemanticProgress.lean`](SemanticProgress.lean).

### Corollary 5.2: Closed progress

If:

~~~text
∅ ⊢ t : T
~~~

then:

~~~text
Progress(initial(t))
~~~

### Proof

Interpret the source derivation in the empty environment, combine it with the
empty continuation, and apply Theorem 5.1. ∎

This is `Tm.Ty.closed_progress` in
[`SemanticSafety.lean`](SemanticSafety.lean).

## 6. Preservation

### 6.1 Allocation extension

Write `T ⪯alloc U` when `U` is obtained from `T` by zero or more store
allocations:

~~~text
T ⪯alloc T

T ⪯alloc U
──────────────
T ⪯alloc U.weaken
~~~

This is `Ty.Extends`. It records scope extension, not subtyping.

### Lemma 6.1: Allocation extensions compose

If:

~~~text
S ⪯alloc T       T ⪯alloc U
~~~

then:

~~~text
S ⪯alloc U
~~~

### Proof

By induction on the second derivation.

- Reflexivity returns the first derivation.
- Allocation applies the induction hypothesis and then one `alloc`
  constructor. ∎

### Theorem 6.2: One-step preservation

If:

~~~text
⊢ source : T       source → target
~~~

then there exists `U` such that:

~~~text
T ⪯alloc U       ‖⊢ target : U‖
~~~

### Proof

Invert source state evidence:

~~~text
σ ⊢tm t : R
σ ⊢K K : R ⇒ T
~~~

Proceed by cases on the operational step.

#### Case E-App

The step has premises:

~~~text
p ⇓σ loc f
q ⇓σ loc y
σ(f) = λ(A).body
~~~

and target:

~~~text
⟨σ,K,body[y]⟩
~~~

Inverting application evidence yields:

~~~text
σ ⊢tm path p : Fun S U
σ ⊢tm path q : S
Cresult : σ ⊢ U[q] ⇝ R
~~~

By path realization:

~~~text
σ ⊨ y : S
σ ⊨ f : Fun S U
~~~

Invert the function realization:

~~~text
σ(f) = λ(A₀).body₀
BodyClosure σ A₀ body₀ B
Cin  : σ ⊢ S ⇝ A₀
Cout : DeferredCoercion σ S B U
~~~

Store lookup is functional, so the semantic binding and operational binding
identify the entire stored abstraction, including both its domain annotation
and body: `A₀=A` and `body₀=body`.

Execute the input coercion:

~~~text
σ ⊨ y : S       Cin : σ ⊢ S ⇝ A₀
──────────────────────────────────
             σ ⊨ y : A₀
~~~

Apply the body closure:

~~~text
σ ⊢tm body[y] : B[y]
~~~

Instantiate the deferred output coercion using the original realization
`σ ⊨ y:S`:

~~~text
σ ⊢ B[y] ⇝ U[y]
~~~

The source result type mentions argument path `q`, while the reduct uses
location path `var y`. Both paths resolve to the same location, so runtime
path equality yields:

~~~text
σ ⊢ U[y] ⇝ U[q]
~~~

Compose all result coercions:

~~~text
B[y] ⇝ U[y] ⇝ U[q] ⇝ R
~~~

The relocation step is essential even for dependent identity. This is a
separate typing of the identity syntax from the running
`id : Top→Top` example above. Let:

~~~text
I    = (z:Top) → {z}
idᵈ  = λ(z:Top). path z
U(z) = {z}
q    = r.a
q ⇓σ loc y
~~~

Suppose `idᵈ` is stored at some function location and the pair
selection `r.a` resolves to argument location `y`. The
source application `idᵈ (r.a)` is assigned result
`{r.a}`. Executing the stored identity opens its body at the
concrete location and initially gives:

~~~text
path (var y) : {var y}
~~~

The two types are not syntactically equal. Runtime equality observes that
`r.a` and `var y` resolve to the same location and
constructs:

~~~text
{var y} ⇝ {r.a}
~~~

Thus preservation transports the concrete reduct back to the path-dependent
type stated by the source application, rather than pretending the two paths
are definitionally equal.

Thus:

~~~text
σ ⊢tm body[y] : R
~~~

Reuse the unchanged continuation. The final state has type `T`, witnessed by
the reflexive allocation extension.

The central Lean expression is:

~~~lean
((closure.apply (input.actionPossible argumentPossible)).cast
  (output.instantiate argumentPossible)).cast
  (relocate.trans suffix)
~~~

#### Case E-Path

The transition is:

~~~text
p ⇓σ loc x
Not p.IsVar
────────────────────────
⟨σ,K,path p⟩ → ⟨σ,K,path (var x)⟩
~~~

The non-variable premise prevents this rule from overlapping with return and
final-location states; preservation does not otherwise use it.

Path evidence contains:

~~~text
C : σ ⊢ {p} ⇝ R
~~~

Since `p` and `var x` resolve to the same location, singleton aliasing
gives:

~~~text
σ ⊢ {var x} ⇝ {p}
~~~

Compose:

~~~text
{var x} ⇝ {p} ⇝ R
~~~

This gives target term evidence at `R`; reuse the continuation and the
reflexive allocation extension.

#### Case E-Let-Push

The transition is:

~~~text
⟨σ,K,let x=s in body⟩ → ⟨σ,body::K,s⟩
~~~

Inverting let evidence gives:

~~~text
σ ⊢tm s : S
BodyClosure σ S body V.weaken
Csuffix : σ ⊢ V ⇝ R
~~~

The old continuation has type `σ ⊢K K:R⇒T`. Construct its new top frame:

~~~text
BodyClosure σ S body V.weaken
Csuffix : σ ⊢ V ⇝ R
σ ⊢K K : R ⇒ T
────────────────────────────
σ ⊢K body::K : S ⇒ T
~~~

Pair this continuation evidence with `σ ⊢tm s:S`. The final type remains
`T`.

#### Case E-Return

The transition is:

~~~text
⟨σ,body::K,path (var x)⟩ → ⟨σ,K,body[x]⟩
~~~

Inverting the continuation gives:

~~~text
σ ⊢K K : U ⇒ T
BodyClosure σ S body V.weaken
Csuffix : σ ⊢ V ⇝ U
~~~

The current path evidence and variable resolution give:

~~~text
σ ⊨ x : S
~~~

Apply the closure:

~~~text
σ ⊢tm body[x] : (V.weaken)[x]
~~~

Since `V` is independent of the let-bound variable:

~~~text
(V.weaken)[x] = V
~~~

Cast by `Csuffix`, obtaining `σ ⊢tm body[x]:U`, and pair it with the tail
continuation. The final type remains `T`.

#### Case E-Allocate

The transition is:

~~~text
⟨σ,body::K,v⟩
    →
⟨σ′,weaken(K),body⟩

where σ′ = Store.val σ v
~~~

Inverting the continuation gives:

~~~text
σ ⊢K K : U ⇒ T
BodyClosure σ S body V.weaken
Csuffix : σ ⊢ V ⇝ U
~~~

The current term evidence and the operational proof that `v` is a value
give `ValueEvidence σ v S`, propositionally truncated as `Nonempty`.

By Lemma 4.6:

~~~text
σ′ ⊢tm body : V.weaken
~~~

Weaken the frame coercion:

~~~text
σ′ ⊢ V.weaken ⇝ U.weaken
~~~

Therefore:

~~~text
σ′ ⊢tm body : U.weaken
~~~

Weaken the tail continuation:

~~~text
σ′ ⊢K weaken(K) : U.weaken ⇒ T.weaken
~~~

Hence:

~~~text
⊢ ⟨σ′,weaken(K),body⟩ : T.weaken
~~~

Choose the existential result `T′=T.weaken` and witness
`T ⪯alloc T′` with one allocation constructor. ∎

The Lean proof is `State.Evidence.preservation` in
[`SemanticPreservation.lean`](SemanticPreservation.lean).

## 7. Finite preservation and type safety

### Theorem 7.1: Finite preservation

If:

~~~text
⊢ source : T       source →* target
~~~

then there exists `U` such that:

~~~text
T ⪯alloc U       ‖⊢ target : U‖
~~~

### Proof

By induction on `source →* target`.

**Reflexivity.** Choose `U=T`, reflexive extension, and the original state
evidence.

**Step followed by execution.** Apply one-step preservation to the first
transition, obtaining middle-state evidence at some `U`. Apply the induction
hypothesis to the remaining execution, obtaining final evidence at some
`V`. Compose `T ⪯alloc U` and `U ⪯alloc V`. ∎

This is `State.Steps.preservation` in
[`SemanticSafety.lean`](SemanticSafety.lean).

### Theorem 7.2: Closed type safety

If:

~~~text
∅ ⊢ t : T       initial(t) →* target
~~~

then `target` is final or can take another step.

### Proof

1. Interpret the closed source typing derivation to obtain evidence for
   `initial(t)`.
2. Apply finite preservation to obtain evidence for `target`.
3. Apply runtime progress to that evidence. ∎

The Lean proof is `Tm.Ty.closed_type_safety` in
[`SemanticSafety.lean`](SemanticSafety.lean).

## 8. Lean theorem and source map

- [`Typing.lean`](Typing.lean): source path typing, subtyping,
  well-formedness, and term typing.
- [`Runtime.lean`](Runtime.lean): stores, path resolution, CK transitions,
  final states, and finite executions.
- [`RuntimeEquality.lean`](RuntimeEquality.lean): store-induced path
  equality and structural conversion used to transport dependent types.
- [`StoreStratification.lean`](StoreStratification.lean): the
  append-only store order used to justify coercion action on pair referents.
- [`SemanticEvidence.lean`](SemanticEvidence.lean): environments,
  realizations, coercions, and suspended binder evidence.
- [`SemanticAction.lean`](SemanticAction.lean): typed path resolution,
  compilation of subtyping, and coercion action.
- [`SemanticTyping.lean`](SemanticTyping.lean): normalized value, term,
  continuation, and state evidence.
- [`SemanticFundamental.lean`](SemanticFundamental.lean): source
  interpretation and body instantiation.
- [`SemanticAllocation.lean`](SemanticAllocation.lean): realization of
  stored values and fresh allocation.
- [`SemanticWeakening.lean`](SemanticWeakening.lean) and
  [`SemanticTypingWeakening.lean`](SemanticTypingWeakening.lean):
  preservation of semantic and machine evidence across allocation.
- [`SemanticProgress.lean`](SemanticProgress.lean): progress.
- [`SemanticPreservation.lean`](SemanticPreservation.lean): heterogeneous
  one-step preservation.
- [`SemanticSafety.lean`](SemanticSafety.lean): finite preservation and
  closed type safety.

### 8.1 Principal theorem chain

The corresponding Lean declarations are:

~~~text
Tm.Ty.interpret
    Γ ⊢ t : T  →  ρ ⊨σ Γ  →  σ ⊢tm ρ(t) : ρ(T)

Tm.Ty.initialEvidence
    ∅ ⊢ t : T  →  ⊢ initial(t) : T

TermEvidence.progress
    σ ⊢tm t : T  →  Progress(⟨σ,K,t⟩)

State.Evidence.progress
    ⊢ c : T  →  Progress(c)

Tm.Ty.closed_progress
    ∅ ⊢ t : T  →  Progress(initial(t))

State.Evidence.preservation
    ⊢ c : T  →  c → c′
      →  ∃U. T ⪯alloc U ∧ ‖⊢ c′ : U‖

State.Steps.preservation
    ⊢ c : T  →  c →* c′
      →  ∃U. T ⪯alloc U ∧ ‖⊢ c′ : U‖

Tm.Ty.closed_finite_preservation
    ∅ ⊢ t : T  →  initial(t) →* c
      →  ∃U. T ⪯alloc U ∧ ‖⊢ c : U‖

Tm.Ty.closed_type_safety
    ∅ ⊢ t : T  →  initial(t) →* c  →  Progress(c)
~~~

Here `‖A‖` denotes Lean's `Nonempty A`. It appears because machine steps
are propositions while semantic evidence is proof-relevant data in
`Type 1`.

## 9. Mechanization notes

- The static well-formedness premises determine which source typing
  derivations may be constructed, but the fundamental interpretation does not
  inspect their proof terms.
- `Nonempty` is required only because operational steps and value
  classification live in `Prop`, while semantic evidence lives in
  `Type 1`.
- The paper's named presentation can preserve a literally identical result
  type because globally fresh names do not shift old names. The intrinsic
  Lean presentation instead records the corresponding weakening with
  `Ty.Extends`.
