# LambdaPFC and LambdaPFCI

## Interpreting typing proofs at concrete stores

The proof idea in one line:

~~~text
declarative source derivation
            ↓ interpret
finite evidence about one concrete store
            ↓ preserve with the machine
progress and preservation
~~~

The runtime language contains no proofs, coercions, casts, or type checks.

---

# 1. Why the textbook proof becomes awkward

Four mismatches appear at once:

1. A source variable is hypothetical; execution uses a concrete store
   location.
2. A source path may be compound; execution eventually identifies one
   location or stored type.
3. Subsumption hides the introduction rule needed for canonical forms.
4. Allocation adds a location and shifts every old intrinsic index.

The goal is not to prove large global substitution and inversion lemmas and
then recover these runtime facts indirectly. The proof records the runtime
facts explicitly when they become known.

---

# 2. The language boundary

~~~text
p ::= x | p.fst | p.a

v ::= λ(x:S).t | pair y a d

t ::= path p | v | p q | let x = s in t

T ::= Top | Bot | (x:S)→T | Pair(x:S,a:τ) | {p} | p.A
τ ::= T | L..U
d ::= val z | type W
~~~

- Paths traverse immutable pair spines.
- A pair points to already allocated locations or stores a type definition.
- Applications take paths; lets sequence computations.
- The baseline has no recursive self types, mutation, intersections/unions,
  or capture checking.
- `LambdaPFCI` separately adds intersections and unions without changing the
  machine.

These restrictions matter to the proof and must not be confused with the
semantic technique itself.

---

# 3. A path-dependent program

~~~text
I   = Top → Top
r₁  = { A = I }
r₂  = { r₁; x = implementation }

use = λ(f : r₂.A). f implementation
r₃  = { r₂; use }

result = r₃.use r₃.x
~~~

This exercises:

- lookup through a nested record spine;
- an exact stored type viewed abstractly through a selection;
- a function whose parameter is literally the selected type `r₂.A`;
- conversion between source paths and the locations found at runtime.

The final theorem says that every finite execution prefix of this closed
program ends in a state that is final or can step.

---

# 4. The semantic bridge

Let `ρ` map source variables to locations in store `σ`.

~~~text
D : Γ ⊢ t : T          ρ ⊨σ Γ
──────────────────────────────── interpretation
         σ ⊢run ρ(t) : ρ(T)
~~~

`ρ ⊨σ Γ` means that every variable in `Γ` is mapped to a location that
supports its declared type.

Interpretation recurses on the chosen derivation `D`, not merely on `t`.
Consequently, a subsumption step is visible and can be translated into
semantic evidence.

This is proof computation in Lean. Machine states still contain only a
store, a continuation, and a term.

---

# 5. What it means for a location to have a type

Write:

~~~text
σ ⊨ x : T       location x supports proper type T
σ ⊨ r : τ       referent r supports generalized signature τ
~~~

These judgments are constructive canonical-form evidence:

- at a function type, expose the stored lambda and suspended body proof;
- at a pair type, expose the stored pair and both component realizations;
- at `{p}`, record that `p` resolves to this location;
- at `p.A`, record the selected stored type and realization at it;
- at `Top`, require no observation;
- at `Bot`, provide no case.

A stored type `W` supports an interval `L..U` by carrying:

~~~text
L ⇝ W ⇝ U
~~~

Canonical forms are therefore obtained by inspecting realized evidence at a
location, rather than by inverting arbitrary source subtyping.

---

# 6. Subtyping becomes proof-only coercion

Under a realized environment:

~~~text
Γ ⊢ τ <: τ′       ρ ⊨σ Γ
────────────────────────── compilation
      σ ⊢ ρ(τ) ⇝ ρ(τ′)
~~~

A coercion acts on evidence while preserving the referent:

~~~text
σ ⊢ τ ⇝ τ′       σ ⊨ r : τ
─────────────────────────── action
          σ ⊨ r : τ′
~~~

Examples:

- transitivity becomes composition;
- singleton widening recovers the known type of a resolved location;
- co-resolving paths transport singleton and dependent-type evidence;
- function coercion adapts the input now and delays the dependent output;
- type selection uses the concrete interval witness `L ⇝ W ⇝ U`.

Nothing is added to the program being evaluated.

---

# 7. Delay a binder until its location exists

Before the argument is known, retain:

~~~text
Dbody : Γ,x:S ⊢ body : T
env   : ρ ⊨σ Γ
~~~

When execution supplies a location:

~~~text
σ ⊨ y : ρ(S)
──────────────────────────────── instantiation
σ ⊢run ρ(body)[y] : ρ(T)[y]
~~~

The same pattern suspends:

- a function or let body;
- a dependent function-codomain comparison;
- a dependent pair-member comparison.

This replaces the needed instances of a global typing-substitution theorem
with interpretation at the concrete locations execution actually reaches.
Renaming, opening, and weakening equations are still required.

---

# 8. Intersections are paired certificates

The separate `LambdaPFCI` variant adds the standard meet rules:

~~~text
S <: T       S <: U
───────────────────       T ∧ U <: T       T ∧ U <: U
     S <: T ∧ U
~~~

Their runtime meaning is direct:

~~~text
σ ⊨ x:T       σ ⊨ x:U
─────────────────────
       σ ⊨ x:T ∧ U
~~~

Both certificates describe the **same location**.

- meet introduction runs two coercions on one input certificate;
- meet elimination returns one retained certificate;
- no intersection value, cast, or transition is added;
- no separate term-introduction rule is needed—ordinary subsumption supplies
  an intersection view.

The companion union evidence is tagged left or right. Its tag exists only in
the proof and selects the appropriate branch during coercion action.

Small closed example: if `S=Top→F`, `L=F→F`, `R=F`, and one closure has type
`S` with `S<:L` and `S<:R`, subsumption gives it `L∧R`. In `f f`, the operator
uses the retained `L` certificate and the argument uses the retained `R`
certificate; execution still calls the one stored closure.

---

# 9. Restricted record-view merging

Let `Pₐ(S,T)` mean one pair cell with predecessor type `S` and term member
`a:T`.

~~~text
Pₐ(S,T) ∧ Pₐ(S,U) <: Pₐ(S,T ∧ U)
~~~

Soundness argument:

1. both source certificates concern one receiver location `r`;
2. invert both as pair certificates;
3. immutable lookup functionality identifies the same stored pair and member
   location `m`;
4. retain both certificates `σ ⊨ m:T` and `σ ⊨ m:U`;
5. rebuild one pair certificate with member `T ∧ U`.

No records are combined at runtime.

For a type member, two views of the same stored witness `W` merge as:

~~~text
L₁..U₁  and  L₂..U₂
          ↓
(L₁ ∨ L₂)..(U₁ ∧ U₂)
~~~

This is deliberately restricted to the same physical slot and label—not a
general record-intersection or row-merge operation.

---

# 10. The complete machine invariant

A continuation is a stack of suspended let bodies.

~~~text
σ ⊢run t : S       σ ⊢cont K : S ⇒ T
─────────────────────────────────────
            ⊨ ⟨σ,K,t⟩ : T
~~~

Meaning:

- the focused term will produce a location usable at `S`;
- the continuation knows how to turn such a result into a final answer at
  `T`.

A nonempty frame retains an open body proof and a coercion from that body's
result to the input type expected by the remaining frames.

The focused type `S` changes as control moves. The answer type `T` is the
quantity preserved by the machine, except for scope extension at allocation.

---

# 11. Progress

Runtime term evidence has four syntax-directed forms.

1. **Path**
   - a variable is final under an empty continuation or returns to a frame;
   - a compound path steps to the location it resolves to.
2. **Value**
   - final under an empty continuation;
   - otherwise allocated for the waiting frame.
3. **Application**
   - resolve operator and argument;
   - act on the operator's accumulated coercion;
   - function realization exposes the stored lambda;
   - take the application step.
4. **Let**
   - push its body and focus the bound computation.

The continuation's typing data is not needed to choose a step; preservation
uses it to type the successor.

Intersections add no fifth case: they occur inside the coercion suffixes and
location certificates used by these same four cases.

---

# 12. Preservation

Write `T ⪯ T′` when `T′` is `T` transported through zero or more allocations.

~~~text
⊨ c : T       c → c′
────────────────────────────
∃T′. T ⪯ T′  and  ⊨ c′ : T′
~~~

Five cases:

- **application:** instantiate the stored body and dependent result evidence;
- **path:** prepend evidence that the old path and its location co-resolve;
- **let push:** move the suspended body proof into continuation evidence;
- **return:** instantiate it at an existing location;
- **allocation:** establish the fresh location's realization and transport all
  old evidence to the larger store.

For dependent beta, if `q` resolves to `y`:

~~~text
body[y] : B[y]  ⇝  U[y]  ⇝  U[q]  ⇝  T
                    ^         ^
              saved result   path co-resolution
~~~

For `LambdaPFCI`, this proof is unchanged. The new work was already discharged
by meet/join coercion action, same-cell record merging, structural conversion,
and weakening.

---

# 13. What is avoided, and what is only relocated

Relocated into store-indexed evidence:

- canonical forms hidden by subsumption;
- the runtime instances of narrowing and binder substitution;
- replacement of a source path by the location it denotes;
- preservation of existing facts when the store grows.

Avoided by restricting the language:

- fresh bad-bound relations: using `L..U` requires an independent proof of
  `L <: U`;
- recursive self-reference and cyclic path lookup;
- mutation and heap updates;
- the baseline's omitted type and term forms.

So this is not a simpler proof of full DOT or pDOT. It tests a different
factorization of the soundness argument on a deliberately smaller calculus.

Intersections test that factorization further: they enlarge certificate
structure and subtyping interpretation, while leaving the machine and the
progress/preservation case split fixed.

---

# 14. Result and open questions

~~~text
∅ ⊢ t : T       initial(t) →* c
────────────────────────────────
       c is final or can step
~~~

Not established:

- normalization or termination;
- decidable or algorithmic typing/subtyping;
- admissibility of transitivity;
- coherence of different compiled subtyping derivations;
- a translation or simulation relating this calculus to DOT or pDOT.

Questions worth discussing:

1. Does derivation-to-evidence interpretation remain useful when genuine DOT
   bounds are restored?
2. Can store-indexed path equality be related to a useful fragment of pDOT
   replacement?
3. Which restriction can be relaxed without losing the simple acyclic-store
   argument?
4. Which aligned record merges can be generalized without making precise path
   lookup ambiguous?

---

# Backup: implementation map

| Mathematical object | Lean declaration |
|---|---|
| `ρ ⊨σ Γ` | `Environment` |
| `σ ⊨ x:T` | `Store.Possible` |
| `σ ⊨ r:τ` | `Path.Referent.Realizes` |
| `σ ⊢ τ ⇝ τ′` | `Coercion` |
| `σ ⊢run t:T` | `TermEvidence` |
| `σ ⊢cont K:S⇒T` | `Tm.Cont.Evidence` |
| derivation interpretation | `Tm.Ty.interpret` |
| coercion compilation/action | `Tau.Sub.compile`, `Coercion.action` |
| progress/preservation | `TermEvidence.progress`, `State.Evidence.preservation` |

Intersection/union implementation map:

| Mathematical addition | `LambdaPFCI` location |
|---|---|
| `T ∧ U`, `T ∨ U`, meet/join rules | `Syntax.lean`, `Typing.lean` |
| paired/tagged realization | `SemanticEvidence.lean` |
| compilation and coercion action | `SemanticAction.lean` |
| runtime conversion and allocation transport | `RuntimeEquality.lean`, `SemanticWeakening.lean` |
| worked programs | `IntersectionRegression.lean`, `RecordIntersectionRegression.lean`, `AlignedRecordIntersectionRegression.lean`, `TypeMemberIntersectionRegression.lean`, `TypeMemberUnionRegression.lean` |

- [Full walkthrough](Metatheory.md)
- [Source typing](Typing.lean)
- [Semantic evidence](SemanticEvidence.lean)
- [Progress](SemanticProgress.lean)
- [Preservation](SemanticPreservation.lean)
