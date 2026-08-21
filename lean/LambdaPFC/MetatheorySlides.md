# LambdaPFC soundness

## Derivation-directed, store-indexed evidence for path-dependent pairs

Central question:

> Can both components of an immutable dependent pair be covariant while
> retaining non-variable paths through immutable pair spines and declarative
> transitivity?

Result: a mechanized progress-and-preservation proof for the calculus, with
no casts or type checks in the runtime language.

---

# 1. The deliberately small calculus

~~~text
p ::= x | p.fst | p.a

v ::= λ(x:S).t | pair y a d

t ::= path p | v | p q | let x = s in t

T ::= Top | Bot | (x:S)→T | Pair(x:S,a:τ) | {p} | p.A
τ ::= T | L..U
~~~

- Paths traverse immutable pair cells.
- Pair components are existing locations or stored type definitions.
- Applications take paths; lets sequence computations.
- No recursive self types, mutation, intersections/unions, or captures in
  this baseline.

Nested pairs form record spines: if the outer label differs, lookup continues
through `.fst`.

---

# 2. The rule that drives the proof

~~~text
Γ ⊢ S <: S′
Γ,x:S ⊢ τ <: τ′
──────────────────────────────────────── pair
Γ ⊢ Pair(x:S,a:τ) <: Pair(x:S′,a:τ′)
~~~

The member comparison is checked under the **source** first-component type.

At compile time, `x` is hypothetical. At runtime, a realized pair
reveals a concrete first-component location:

~~~text
σ(z) = pair y a d
σ ⊨ y : S
σ ⊨ referent(d) : τ[y/x]
~~~

Only then can the second premise be interpreted at `y`.

---

# 3. The central move: interpret derivations

The semantic interpretation consumes a proof-relevant typing derivation, not
only syntax:

~~~text
code : Γ ⊢ t : T        env : ρ realizes Γ in σ
────────────────────────────────────────────────
interpret(code,env) : σ ⊢tm ρ(t) : ρ(T)
~~~

Likewise, under the same environment:

~~~text
Γ ⊢ τ <: τ′        env : ρ realizes Γ in σ
────────────────────────────────────────── compile
σ ⊢ ρ(τ) ⇝ ρ(τ′)
~~~

- Different subtyping derivations may compile differently.
- Transitivity becomes coercion composition.
- This is Lean proof computation, not object-language execution.

---

# 4. What a runtime type means

`Store.Possible σ x T` is a canonical-form certificate for location
`x` at type `T`.

- `Top`: no observation required.
- `Fun S U`: exposes a stored lambda, its body closure, input
  adapter, and deferred output adapter.
- `Pair S a τ`: exposes the stored pair and realizations of both
  components.
- `{p}`: records that `p` resolves to `x`.
- `p.A`: records the selected stored type and realization at it.
- `Bot`: no constructor.

A type-member referent realizes `L..U` by storing a concrete witness:

~~~text
L ⇝ W ⇝ U
~~~

Canonical forms therefore come from runtime realization—not inversion of an
arbitrary declarative subtyping derivation.

---

# 5. Coercions change evidence, not programs

~~~text
C : σ ⊢ τ ⇝ τ′       R : σ ⊨ r : τ
─────────────────────────────────────
          action(C,R) : σ ⊨ r : τ′
~~~

`Coercion.action` preserves the same store and referent.

Examples:

- singleton widening: `{p} ⇝ T` recovers the known realization of
  the location denoted by `p`;
- aliases: co-resolving paths give `{q} ⇝ {p}`;
- functions: prepend a contravariant input adapter and defer the dependent
  output comparison;
- selections: use the stored witness `L ⇝ W ⇝ U`;
- pairs: convert the first location now and the member after its binder is
  instantiated.

There is no cast syntax, cast transition, or erasure theorem.

---

# 6. Closures postpone exactly one missing location

~~~text
saved:
    code : Γ,x:S ⊢ body : T
    env  : ρ realizes Γ in σ

later:
    arg  : σ ⊨ y : ρ(S)
────────────────────────────────
    σ ⊢tm ρ(body)[y] : ρ(T)[y]
~~~

Three forms:

- `BodyClosure`: function or let body typing;
- `DeferredCoercion`: function-codomain subtyping;
- `MemberClosure`: dependent pair-member subtyping.

They retain the source derivation plus an environment certified in `σ`.
Allocation weakening transports them to an extended store.

This replaces a general typing-substitution theorem with the concrete
location-specific instances execution actually needs.

The complete machine invariant also types the control stack, which is a list
of suspended let bodies:

~~~text
σ ⊢tm t : S       σ ⊢K K : S ⇒ T
──────────────────────────────────
       ⊢ ⟨σ,K,t⟩ : T
~~~

The focused type `S` may change after a transition; `T` is
the final answer type tracked by preservation.

---

# 7. A closed path-dependent example

~~~text
I   = Top → Top
r₁  = { A = I }
r₂  = { r₁; x = implementation }

use = λ(f : r₂.A). f implementation
r₃  = { r₂; use }

result = r₃.use r₃.x
~~~

What the typing exercises:

- `r₂.A` skips the outer `x` field to reach
  `r₁.A`;
- `r₃.A` would skip both `use` and `x`;
- the annotation on `use` is literally the selected type
  `r₂.A`;
- the stored exact definition `A=I` supports both
  `I <: r₂.A` and `r₂.A <: I`;
- the final application views `r₃.x` at the domain expected by
  `r₃.use`.

The theorem specializes closed finite-prefix safety to this program.

---

# 8. Progress is four evidence cases

Normalized `TermEvidence` has exactly four outer forms:

1. **Path**
   - variable + empty continuation: final;
   - variable + frame: return;
   - compound path: resolve and canonicalize to its location.
2. **Value**
   - empty continuation: final;
   - frame waiting: allocate.
3. **Application**
   - resolve operator and argument;
   - execute the operator suffix;
   - invert `Possible Fun` to expose the stored lambda;
   - take the application step.
4. **Let**
   - push its body and focus its bound computation.

No source-subtyping inversion occurs in progress.

---

# 9. Preservation is the five machine rules

~~~text
Evidence(c,T)       c → c′
────────────────────────────────────────────
∃T′. T Extends T′ ∧ Nonempty(Evidence(c′,T′))
~~~

- **Application:** instantiate the stored body and dependent result evidence.
- **Path canonicalization:** prepend an alias coercion.
- **Let push:** move the body closure and result suffix into continuation
  evidence.
- **Return:** instantiate that closure at an existing location.
- **Allocation:** establish the fresh realization and weaken the tail.

The dependent beta chain is:

~~~text
body[y] : B[y]
          │ saved function output
          ▼
         U[y]
          │ q and var y resolve together
          ▼
         U[q]
          │ application's final suffix
          ▼
           T
~~~

Runtime path equality transports the entire dependent codomain, not merely a
singleton type.

---

# 10. Allocation and termination

Allocation changes the intrinsic scope:

~~~text
T : Ty n       T.weaken : Ty (n+1)
~~~

`Ty.Extends` records zero or more such changes across a finite
execution. It is scope extension, not subtyping.

Coercion action is well founded on:

~~~text
(stratum(referent), treeSize(coercion))
~~~

For `σ(x)=pair y a d`:

~~~text
stratum(loc y)       < stratum(loc x)
stratum(referent d)  < stratum(loc x)
~~~

Pair recursion moves to an older referent; same-referent recursion moves to a
strict coercion subtree.

---

# 11. Position relative to DOT and pDOT

Localized into runtime evidence:

- selected-type canonical forms → concrete witness `L ⇝ W ⇝ U`;
- transitivity-obscured inversion → execute a compiled coercion first;
- narrowing and substitution → instantiate closures at realized locations;
- path replacement → store co-resolution plus structural runtime conversion;
- global store typing → local realization certificates plus weakening.

Avoided by restricting the calculus:

- fresh bad-bound relations → require `L <: U` independently;
- recursive self types and circular semantic worlds;
- computational or cyclic paths;
- mutation and heap updates;
- intersections/unions, captures, polymorphism, and pattern matching.

This is not a proof of full DOT. In particular, requiring `L <: U`
independently prevents abstract members from introducing fresh custom
subtyping relations.

---

# 12. Result, non-results, and discussion

Mechanized result:

~~~text
∅ ⊢ t : T       initial(t) →* c
────────────────────────────────
       c is final or can step
~~~

Not established:

- normalization;
- decidability or an algorithmic type system;
- admissibility of transitivity;
- equality/coherence of compiled coercions;
- recursion, mutation, or the other omitted features.

Questions:

1. Is realization-directed subtyping interpretation a useful complement to
   inert/tight typing for larger path-dependent calculi?
2. Which restriction should be relaxed first without losing the
   allocation-order argument?
3. Can the source-to-runtime bridge be factored into a reusable core shared
   by the capture and intersection variants?

---

# Backup: pointers

- [Full pedagogical walkthrough](Metatheory.md)
- [Static semantics](Typing.lean)
- [Semantic evidence](SemanticEvidence.lean)
- [Subtyping compilation and coercion action](SemanticAction.lean)
- [Progress](SemanticProgress.lean)
- [Preservation](SemanticPreservation.lean)
- [Finite safety](SemanticSafety.lean)
