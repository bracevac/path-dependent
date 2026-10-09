# FCdot with captures

The target calculus, extended with capture sets.  A type is a shape with a capture set beside it,
`S ^ C`, and the shapes are the vanilla types plus the box `□ T`.  Inclusion evidence pairs a shape
coercion with a capture coercion, and both erase.  Every term has a use set, the capabilities it may
read, and the module `Prediction` proves that along a run the roots of the use set do not grow
and that a state reads only roots its use set covers.

Contexts and stores gain capture binders, each with a bound (`CapBound`: a scope root,
a rigid platform capability, an upper bound, or an instance).  An object type can state what its
members capture, through capture propositions in its telescope.  An object literal records a capture
witness per label and the capture set its introduction assigns to it.  Boxing is a value and
unboxing a term, so the capability an atom denotes is always the capability of its root.

## Reading order

| module | contents |
|---|---|
| `Debruijn` | signatures with two binder kinds, term variables and capture variables, with bound variables and renamings |
| `Syntax` | capture atoms, capture sets, shapes, types `S ^ C` and propositions. Evidence `ShapeCo`, `CapCo`, `CapEq`, `LeCo`. Atoms gain `recap`, which keeps an atom's shape and widens its capture set. Terms with `unbox` and declared use sets, values with `box`, `Tm.uses`, `Tm.inspects` |
| `Context` | term and capture binders, lookup of types, definitions, capture definitions (`Ctx.lookupDefC`) and fields |
| `Typing` | the judgments for shape, capture and type inclusion, capture equality, presence, morphisms, atoms, terms, values, fields |
| `Store` | stores with data-free capture slots and store typing `⊢ σ : Γ`. A binder's capture set is its stored value's annotation (`Store.Typed.lookup_annot`) |
| `Normalizer` | head forms of closed evidence, including `Form.boxed`, views of atoms, and the fuel-indexed normalizer |
| `Machine` | continuations, states, the step relation with the `unbox` steps, the use set of a state (`State.uses`), store extension `Store.Ext` |
| `Erasure` | erasure into the shared runtime: a box to the runtime's box, an unboxing to its `unbox` |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | renaming and substitution at both binder kinds, and their action on typing |
| `Preservation` | inversion lemmas, `preservation` |
| `ErasureMetatheory` | forward simulation `erase_step`, backward simulation `erase_reflect`, final states |
| `Checker`, `CheckerCompleteness` | the decision procedure and `checkTm_iff` |
| `Resolution` | alias-tolerant resolution of shapes, the roots of a capture set (`Ctx.roots`, `Ctx.Root`), `CapLe`, `RootsEq` |
| `FormTyping` | typed forms, entries and views, with capture entries |
| `FormAlgebra` | composition and application of typed forms, fuel monotonicity |
| `CanonicalForms` | canonical forms for shape, capture and type evidence and for atoms, `closed_box_inversion`, `preservation'`, `erase_reflect'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions, no closed `⊤ ≤ ⊥`, over a typed store a platform capability never sinks to `{}`, `reachable_consistent` |
| `Prediction` | `step_uses`, `capture_prediction`, `inspects_covered`, `effect_safety`, `effect_safety_unbox`, `returned_capture_bound` |
| `Examples` | the vanilla E1 to E8 at pure types, the capture examples, and the target side of the source examples |

## Notation

Only notation that is new relative to the vanilla calculus.  All of it is `scoped` in namespace `FCdot`.

| | |
|---|---|
| `S ^ C`, `Ty.pure S` | the type with shape `S` and capture set `C`, and the pure type `S ^ []` |
| `□ T` | the box shape |
| `var x`, `cvar κ`, `name x ℓ` | capture atoms: a term variable, a capture variable, a capture member `x∙ℓ` |
| `s,c` | a signature extended by a capture binder, beside `s,x` |
| `C₁ ⊑ᶜ C₂`, `C₁ ≐ᶜ C₂` | capture propositions in a telescope, under the self like every proposition |
| `Γ ⊢ˢ e : S ≤ T` | shape inclusion evidence (the vanilla `Γ ⊢ e : S ≤ T`) |
| `Γ ⊢ᶜ f : C ⊑ D`, `Γ ⊢ᶜ φ : C ≡ D` | capture inclusion and capture equality evidence |
| `Γ ⊢ capt e f : S ^ C ≤ S' ^ C'` | type inclusion, a shape inclusion paired with a capture inclusion |
| `Γ ⊢ᶠ[A] F` | field typing at the literal's assigned capture set `A` |
| `σ ⊢ e ⇓ˢ[n] F` | head form of a shape coercion |
| `σ ⊢ a ⇓ᶜ[n] (a', F)` | the chain of casts of an atom, with the atom under it |

Lean names spell `ᶜ` as the suffix `C` (`Ctx.consC`, `Store.consC`, `Ctx.lookupDefC`, `SideC`).

The roots of a capture set are the capture variables it reaches through the context.  A term
variable leads to the capture set of its type, a capture member to its witness, and a capture
variable to its bound, until a scope root or a platform capability.  `CapLe Γ C D` says every root
of `C` is a root of `D`.  It is the meaning of capture evidence and of the prediction theorems.

## Main theorems

Every theorem of the base calculus holds here, with `Ty` read as `Shape` where the base position
carries no capture set.  `checkTm_iff`, `has_canon`, `preservation'`, `progress`, `not_stuck`,
`erase_step` and `erase_reflect'` keep their form.  Three changed in a way a reader would notice:

- `shape_canon` is the vanilla `le_canon`.  The new `le_canon` reads a type inclusion at its shapes.
- `atom_canon` gains a conjunct: over a typed store, an atom's root is below the capture set of its type.
- `closed_le_shapes` gains a disjunct: the target of the inclusion resolves to a box.  The conclusion
  is weaker than the base theorem.

New:

- `cap_canon`: over a typed store, capture inclusion evidence means `CapLe`.
- `capeq_canon`: over a typed store, capture equality evidence means the two sets have the same roots.
- `closed_box_inversion`: over a typed store, an atom of box type is rooted at a stored box.
- `Store.Typed.no_cap_star_le_nil`: over a typed store, no evidence puts a platform capability
  (a star binder) below the empty set.
- `step_uses`: one step of a typed state embeds the old store in the new one, and the roots of the
  use set do not grow.
- `capture_prediction`: the same along a run from a typed state.
- `inspects_covered`: the root a state reads is covered by its use set.
- `effect_safety`: from a typed state whose use set has no root `κ`, a run never reaches a state
  that reads a variable rooted at the image of `κ` in the end store.  It says something at a rigid
  or star binder `κ`.  For a bounded or instantiated `κ` it holds for a trivial reason.  A stored box
  has the empty annotation, so reading a box is not flagged.
- `effect_safety_unbox`: from a typed state whose use set has no root `κ`, a run never reaches a
  state that unboxes an atom whose root holds a stored box `□ b` with `b` rooted at the image of
  `κ` in the end store.  The unboxing of a capability is charged here.
- `returned_capture_bound`: a returned value or atom is bounded by the capture set of the answer's type.

The checker decides the examples in the kernel.  `C1_typed` accepts the closure
`λ^{log}(u). let _ = log u in λ^{console}(v). console v`.  `C6_rejected` refuses the variant whose
inner lambda claims no capability, and `C6_covered` instantiates the prediction on a run.
`C6_safe` applies `effect_safety` to the second program: no state reached from it, with a typed
store, reads a variable rooted at the image of `κ₂` in that store.  `C6_rejected` and `C7_rejected` are checker verdicts on one term each, with fixed evidence.
`C7_rejected` refuses a client that unboxes a capability its use set does not name.

Axioms: `propext` and `Quot.sound` at most.  No `sorry`, `axiom` or `native_decide`.
