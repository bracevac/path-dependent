# Nominal.FCn: the coercion target with classes

FCn is the target of plan XII: FCp, the target of plan X (Part T), with the class primitive of stage
N1, described after this paragraph.  Paths are terms, and path evidence `Γ ⊢ᵖ P : T` types the
path `P.path`.  Path equality `Γ ⊢ π : p ≃ q` is evidence, and the replacement of a path by its alias
inside a type is the type equality `lift (h. T) π`.  A literal `obj (z : Tel) ds` declares a
telescope of propositions: bounds `S ⊑ T`, fields `fld a T`, aliases `≈ q` and self bounds `is T`.
A field may hold a path, a lambda or a nested literal, and each is reachable by selection.  A context
binds a variable opaque at a type, or transparent at a type with the block of its literal.  There is
no subsumption.  Every use of subtyping is evidence that erases.

The machine allocates at a `let` of a value, substitutes path evidence at a `let` of a path, and
applies a path through its application view, as pDOT's `red_app` looks the closure up.  It has no
projection step and never copies an object.  The erasure maps FCn into the runtime
`../../PDot/Runtime.lean`, which the PDot tree shares.  The metatheory reads closed evidence over a typed store `⊢ σ : Γ` through a
closed reading: the canonical walk `Γ.canon p`, with the one name `none` for every cyclic path,
resolution `Γ.res T` and the normal type `Γ.norm T`.  The checker never computes them.

Stage N1 of plan XII adds the class primitive of FCn, and stage NT closes it.  A literal may hold a
class entry `ds ▹ {class C = U}` (`Defs.cls`), and DF-Cls declares it with the two bounds `⊥ ⊑ w∙C`
and `w∙C ⊑ μ(o : TelB)`, where `U` is that object type at the literal's path.  The seal `seal p C`
(`LeCo.seal`) is LE-Seal: when the block at `p` holds the class entry `C = U`, it includes `U` in
`p∙C`.  A block exists only at a transparent binder, so in a typed program a seal names the self of
an enclosing literal (`Class.sealOpaque_rejected` in `Examples`).  A class entry is no type
definition: `defAt` skips it, so EQ-Def has no type at `p∙C` (`Class.classDefP_none`), and
resolution stops at a class selection (`Ctx.res_cls`).  The closed reading has an instance view
`inst W` for a path at a class, with `W` its view at the body, and two form atoms: `seal p C` and
`unseal p C`, the read of the class's upper bound.  `ClassForms` proves the canonical forms of the
primitive: a closed path at a class has an instance view (`class_view`), closed evidence into a type
below a class from a type not below it holds a seal (`le_below`, `le_below_sealFree`,
`nominal_literal`), and a typed program in a context of opaque binders seals only selves of the
literals around it (`seal_scope`).  These are not nominality.  A forged instance meets each of them,
since LE-Seal holds at every class of a stored literal (`ClassEx.Store1.forge`), and `seal_scope`
says nothing of a state whose store holds a literal (`ClassEx.Forge`).  Plan XII states nominality
at the source.  Stage NR proves a run-time statement.  Take a reachable state of a typed program
that meets `Tm.InitSeals`, and a path of its fragment that meets the provenance predicate under the
run's records and is typed at a class.  Up to `canon`, the path names a store variable whose
allocation record holds a key below that class.

Stage NR proves the run-time provenance of class instances in terms of allocation records.  An
allocation record gives each store variable a set of keys `(q, C)`, `q` the seal's owner path, and
every owner is older than the variable whose record holds its key.  At `MS-LetVal` the new variable
gets the record `allocLbl u v`.  It holds the keys of the seal sites of the variable in the
continuation `u` and at the self of the literal `v`, inside lambda bodies too.  So a key says that
the allocating scope permits a seal of the variable at `q∙C`, in code that may be dormant.  The
predicate `State.SealsAtCtors` admits a seal only at the head of a path cast at a store variable
whose record holds its key, or at the binder of a `let` of a value or a literal's self.  It holds of
the initial state of a program that meets `Tm.InitSeals` and is preserved by every rule of the
machine with records `AStep` (`Provenance`), and `appView` meets its hypothesis (`ProvenanceViews`).
A `member` read adds no seal to a normal form.  Take a reachable state of a typed program that
meets `Tm.InitSeals`, and a path of every former but `sel` and `unfold` that meets the predicate
under the run's records and is typed at a class selection.  Up to `canon`, the path names a store
variable whose record holds a key `(q, D)` with `q∙D` below the class (`provenance`,
`ProvenanceClass`).  The path in focus meets the predicate with no hypothesis (`provenance_focus`).
The parameter forgery of `ClassEx.Forge` and a module method that seals a literal it captures both
fail `Tm.InitSeals` (`ProvEx.ForgeRun`, `ProvEx.CapRun`).

An allocation record tracks the class seal sites permitted by the allocating scope, including sites
inside dormant code.  It is not by itself a log of executed constructors or executed seal uses.
Three facts fix the reading of the theorem.  The records depend on FCn evidence and are not in
general recoverable from an erased runtime configuration.  Two programs with identical erased runs
can have different records.  `ProvEx.Dormant` checks both: a lambda that is never called and holds
a seal site of an instance puts a key in the instance's record (`trace_erase_eq`, `keys_on`,
`keys_off`).  The substantive result is that one record environment is computed along the run
before the queried path is chosen.  `provenance` gives the records `A` before it quantifies over
the path.  Two runs to one state compute one record (`ASteps.alloc_unique`).  The invariant of the
records survives every step of the machine (`AStep.sealsAtCtors`).  The construction of an
application view and the normalization of evidence keep it too (`appView_sealsOK`, `Hnf.ok`).  So
the record is not chosen after the run to fit a class conclusion.

## What is proved

Over a typed store `hσ : ⊢ σ : Γ` (`Store.Typed σ Γ`):

- `alias_canon`: `Γ ⊢ π : p ≃ q` gives `Γ.canon p = Γ.canon q`.  A closed alias names one location.
- `eq_canon`: `Γ ⊢ φ : S ≡ T` gives `Γ.norm S = Γ.norm T`.
- `le_canon`: closed inclusion evidence `Γ ⊢ e : S ≤ T` has a head normal form typed from `S` to
  `T`.  `mor_canon`: closed morphism evidence `Γ ⊢ m : src ⇒ Tel` has entries typed from `src` to
  `Tel`.
- `path_view`: a typed path `Γ ⊢ᵖ P : T` has `Γ.res T ≠ ⊥` and a view typed against `Γ.res T`: an
  object view at an object type, a function view at a function type, an instance view at a class
  selection, none at an abstract selection.
- `app_view_exists`: a path typed at `Π(z : S) T` has an application view.  It names a closure
  `lam (z : S₀) t₀` with `t₀` typed, a head that casts it to `Π(z : S) T`, and the runtime's lookup
  of `P.path` reaches that closure.
- `lookup_step_typed`: a typed path looks up in one step to a value, to a nested literal, or to a
  path typed at the same type.  `path_safe`: every lookup sequence of a typed path ends at a value
  or a nested literal, or takes one more step.
- `canon_lookup`: a path whose canonical name is `some c` looks up to `c`.  `canon_cyclic`: a path
  whose canonical name is `none` has an infinite lookup.
- `no_top_le_bot`: no evidence proves `⊤ ≤ ⊥` in `Γ`.  `closed_le_shapes`: the shapes a closed
  inclusion can relate, a class selection on either side among them.  `gdot3_any`: no literal at
  gDOT's bad-bounds telescope is typed in `Γ`.
- `class_view`, `le_below`, `le_below_sealFree`, `nominal_literal`, `seal_scope`: the canonical forms
  of the class primitive (`ClassForms`).

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
- `reachable_sealsAtCtors_appView`: every state that a program meeting `Tm.InitSeals` reaches meets
  the predicate under the records of its run, and every owner of those records is older than its
  variable.
- `ASteps.alloc_unique`: over a deterministic view, two runs from one state to one machine state
  compute one record.  A run that returns to a state adds no variable and keeps the record.  The
  machine with records is deterministic (`AStep.det`).
- `provenance`: in such a state of a typed program, a path of every former but `sel` and `unfold`
  that meets the predicate under the run's records and is typed at a class selection `p∙C` names,
  up to `canon`, a store variable whose record holds a key `(q, D)` with `q∙D` below `C`.  The key
  says that the allocating scope permits a seal of the variable at `q∙D`, in code that may be
  dormant.
- `provenance_focus`: the same of the path in focus, with no hypothesis on its seals.

The checker decides typing: `checkTm_iff` and `checkPath_iff`, from soundness and completeness for
every judgment of the two typing blocks, evidence and terms.  The negative examples N1 to N3 have
no typing (`Examples`), and the gate C0 stores are typed and their facts hold (`CanonExamples`,
`CanonicalExamples`).

## What it leaves out

FCn types some terms that pDOT-C rejects: the reflexive singleton `sngl P P.path (refl P.path)`, the
empty literal, and `lift` along a symmetric path equality (plan X, decision 21).  The theorems above
hold of these terms too.  The machine takes the application view as a parameter, and only
`appView` is proved deterministic and sound.

The provenance corollary is not proved at a field selection `sel` or at `unfold`, and the records
live beside the machine, not in the store.  No run-time class tag, pattern matching or constructor
authenticity is claimed.  A result of that kind needs a notion of constructor event defined
independently of `allocLbl` membership.

## Modules

| module | contents |
|---|---|
| `Syntax` | types, propositions, telescopes, the evidence families `PEq`, `PathCo`, `LeCo`, `EqCo`, `Morphism`, `Side`, terms, values, definitions, stores, continuations, renaming and the two substitutions |
| `RenameLemmas` | the composition laws of renaming and substitution for every family |
| `Context` | contexts with opaque and transparent binders, blocks, `Ctx.blockAt`, `Ctx.nodeAt`, `Ctx.defAt`, `Ctx.clsAt` |
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
| `Normalizer` | forms with `seal` and `unseal`, views with the instance view, the normalizer relations, `appView`, determinism, the computable versions with `appViewOf` |
| `FormTyping` | the closed readings and the typing of forms and views |
| `FormAlgebra` | composition and application of typed forms, transport of views |
| `CanonicalForms` | the mutual theorem, `alias_canon`, `eq_canon`, `le_canon`, `mor_canon`, `path_view`, `app_view_exists`, `appView_sound` |
| `LookupSafety` | `lookup_step_typed`, `path_safe` |
| `Consistency` | `no_top_le_bot`, `closed_le_shapes`, `gdot3_any` |
| `ClassForms` | the canonical forms of the class primitive: `class_view`, `Below`, `le_below`, `le_below_sealFree`, `nominal_literal`, `seal_scope` |
| `CanonicalExamples` | the gate C0 stores read through evidence, E5 and E7 final stores with their safe answers |
| `ClassExamples` | the running store of classes through the closed reading, and a forged instance at the end of a run |
| `Preservation` | `preservation'`, `Steps.typed` |
| `Progress` | `progress`, `not_stuck` |
| `ErasureMetatheory` | `erase_reflect'`, `reachable_consistent`, `Steps.consistent` |
| `Provenance` | owners, keys and allocation records, the predicate `sealsOK` and its seal sites, the machine with records `AStep`, its determinism `AStep.det` and `ASteps.alloc_unique`, `AStep.sealsAtCtors`, `reachable_sealsAtCtors` |
| `ProvenanceViews` | forms and views meet the predicate, `appView_sealsOK` |
| `ProvenanceClass` | every seal of a normal form is a seal of the evidence's head (`Hnf.sf`), the fragment, `frag_provenance`, `provenance`, `provenance_focus` |
| `ProvenanceExamples` | the machine with records computed, N1's class program, two forging runs, a cast constructor, the application heads, a function instance, a dormant seal |
