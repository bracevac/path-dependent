# PDot.FCp: the coercion target

FCp is the target of plan X (Part T).  Paths are terms, and path evidence `Γ ⊢ᵖ P : T` types the
path `P.path`.  Path equality `Γ ⊢ π : p ≃ q` is evidence, and the replacement of a path by its alias
inside a type is the type equality `lift (h. T) π`.  A literal `obj (z : Tel) ds` declares a
telescope of propositions: bounds `S ⊑ T`, fields `fld a T`, aliases `≈ q` and self bounds `is T`.
A field may hold a path, a lambda or a nested literal, and each is reachable by selection.  A context
binds a variable opaque at a type, or transparent at a type with the block of its literal.  There is
no subsumption.  Every use of subtyping is evidence that erases.

The machine allocates at a `let` of a value, substitutes path evidence at a `let` of a path, and
applies a path through its application view, as pDOT's `red_app` looks the closure up.  It has no
projection step and never copies an object.  The erasure maps FCp into the runtime
`../Runtime.lean`.  The metatheory reads closed evidence over a typed store `⊢ σ : Γ` through a
closed reading: the canonical walk `Γ.canon p`, with the one name `none` for every cyclic path,
resolution `Γ.res T` and the normal type `Γ.norm T`.  The checker never computes them.

Stage N1 of plan XII adds the class primitive of FCn.  A literal may hold a class entry
`ds ▹ {class C = U}` (`Defs.cls`), and DF-Cls declares it with the two bounds `⊥ ⊑ w∙C` and
`w∙C ⊑ μ(o : TelB)`, where `U` is that object type at the literal's path.  The seal `seal p C`
(`LeCo.seal`) is LE-Seal: when the block at `p` holds the class entry `C = U`, it includes `U` in
`p∙C`.  A block exists only at a transparent binder, so in a typed program a seal names the self of
an enclosing literal (`Class.sealOpaque_rejected` in `Examples`).  In this first version `defAt` also
reads a class entry, so EQ-Def at `p∙C` answers `U` (`Class.classDefP_v1`), and every new case of
the metatheory reduces to the cases of DF-Typ and EQ-Def.  The later stage NT of the plan stops that
reading, so that a class is opaque outside its seal.

## What is proved

Over a typed store `hσ : ⊢ σ : Γ` (`Store.Typed σ Γ`):

- `alias_canon`: `Γ ⊢ π : p ≃ q` gives `Γ.canon p = Γ.canon q`.  A closed alias names one location.
- `eq_canon`: `Γ ⊢ φ : S ≡ T` gives `Γ.norm S = Γ.norm T`.
- `le_canon`: closed inclusion evidence `Γ ⊢ e : S ≤ T` has a head normal form typed from `S` to
  `T`.  `mor_canon`: closed morphism evidence `Γ ⊢ m : src ⇒ Tel` has entries typed from `src` to
  `Tel`.
- `path_view`: a typed path `Γ ⊢ᵖ P : T` has `Γ.res T ≠ ⊥` and a view typed against `Γ.res T`: an
  object view at an object type, a function view at a function type, none at an abstract selection.
- `app_view_exists`: a path typed at `Π(z : S) T` has an application view.  It names a closure
  `lam (z : S₀) t₀` with `t₀` typed, a head that casts it to `Π(z : S) T`, and the runtime's lookup
  of `P.path` reaches that closure.
- `lookup_step_typed`: a typed path looks up in one step to a value, to a nested literal, or to a
  path typed at the same type.  `path_safe`: every lookup sequence of a typed path ends at a value
  or a nested literal, or takes one more step.
- `canon_lookup`: a path whose canonical name is `some c` looks up to `c`.  `canon_cyclic`: a path
  whose canonical name is `none` has an infinite lookup.
- `no_top_le_bot`: no evidence proves `⊤ ≤ ⊥` in `Γ`.  `closed_le_shapes`: the shapes a closed
  inclusion can relate.  `gdot3_any`: no literal at gDOT's bad-bounds telescope is typed in `Γ`.

Of the application view `appView` itself, with no hypothesis:

- `appView_det`: the view is a function of the evidence.
- `appView_sound`: every application view reaches the closure it names.

On the machine `Step appView`:

- `preservation'`: a step from a state typed at `U` reaches a state typed at `U` renamed by the
  step.  `Steps.typed` iterates it along a run.
- `progress`: a typed state is final or steps.  `not_stuck`: a typed state is not stuck.
- `Step.det`: over a deterministic view the machine is deterministic, and `appView` is one
  (`appView_det`).
- `erase_step`: over a sound view a step erases to a runtime step or keeps the erasure, and
  `appView` is one (`appView_sound`).  `erase_reflect'`: a runtime step of the erasure of a typed
  state is matched by one or more machine steps, whose last state erases to the runtime's result.
- `reachable_consistent`: for a closed term typed in the empty context, every store that a run from
  it reaches is typed and proves no `⊤ ≤ ⊥`.  The typing of the term is needed: an untyped program
  runs to a store holding N3's dangling literal, and that store has no typing
  (`X5Ex.DanglingRun.store_untyped`).  `Steps.consistent` says the same from any typed state.

The checker decides typing: `checkTm_iff` and `checkPath_iff`, from soundness and completeness for
every judgment of the two typing blocks, evidence and terms.  The negative examples N1 to N3 have
no typing (`Examples`), and the gate C0 stores are typed and their facts hold (`CanonExamples`,
`CanonicalExamples`).

## What it leaves out

FCp types some terms that pDOT rejects: the reflexive singleton `sngl P P.path (refl P.path)`, the
empty literal, and `lift` along a symmetric path equality (plan X, decision 21).  The theorems above
hold of these terms too.  The machine takes the application view as a parameter, and only
`appView` is proved deterministic and sound.

## Modules

| module | contents |
|---|---|
| `Syntax` | types, propositions, telescopes, the evidence families `PEq`, `PathCo`, `LeCo`, `EqCo`, `Morphism`, `Side`, terms, values, definitions, stores, continuations, renaming and the two substitutions |
| `RenameLemmas` | the composition laws of renaming and substitution for every family |
| `Context` | contexts with opaque and transparent binders, blocks, `Ctx.blockAt`, `Ctx.nodeAt`, `Ctx.defAt` |
| `Typing` | the rules of T.3 as two mutual blocks, evidence and terms, with the inversions of `VA-Obj` and the definition rules |
| `Store` | store typing `⊢ σ : Γ`, `Store.Typed.get_shape` |
| `Machine` | states, continuation typing, the machine `Step V` over an application view `V`, `Step.det` |
| `Model` | path models of a fixed context, for the negative examples |
| `TypingRename` | typing under renaming |
| `TypingSubst` | typing under substitution by path evidence |
| `Transparency` | `Ctx.Refines`: an opaque binder refines to a transparent one |
| `Examples` | N1 to N3 have no typing, the binder example, the risk of `adjust`, three checker verdicts |
| `Erasure` | erasure into the runtime, `erase_step`, the shuffles and their measure |
| `Checker` | the checker of T.8 and its soundness |
| `CheckerCompleteness` | completeness, `checkTm_iff`, `checkPath_iff` |
| `Canon` | the canonical walk `Ctx.canon`, its laws, `canon_lookup`, `canon_cyclic` |
| `Resolution` | resolution `Ctx.res`, the normal type `Ctx.norm`, their laws |
| `CanonExamples` | the stores recorded by gate C0 and E12, with walk and resolution facts |
| `Normalizer` | forms, views, the normalizer relations, `appView`, determinism, the computable versions with `appViewOf` |
| `FormTyping` | the closed readings and the typing of forms and views |
| `FormAlgebra` | composition and application of typed forms, transport of views |
| `CanonicalForms` | the mutual theorem, `alias_canon`, `eq_canon`, `le_canon`, `mor_canon`, `path_view`, `app_view_exists`, `appView_sound` |
| `LookupSafety` | `lookup_step_typed`, `path_safe` |
| `Consistency` | `no_top_le_bot`, `closed_le_shapes`, `gdot3_any` |
| `CanonicalExamples` | the gate C0 stores read through evidence, E5 and E7 final stores with their safe answers |
| `Preservation` | `preservation'`, `Steps.typed` |
| `Progress` | `progress`, `not_stuck` |
| `ErasureMetatheory` | `erase_reflect'`, `reachable_consistent`, `Steps.consistent` |
