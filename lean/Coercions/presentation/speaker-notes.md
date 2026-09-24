# Speaker cues and sources

The main talk has 63 slides. Six reference slides give further syntax,
translation clauses, and the separate pushback strategy. Slides 5--6 explain
the annotated frontend; slides 56--62 cover retained-let reduction and its
all-order safety theorem. The detailed direct-proof comparison is retained.
All paths below are relative to the `Coercions` directory.

1. **Result.** The input is a source typing derivation, not just a term.
   The output is a target term containing explicit evidence. Both erase to
   the same untyped program. Sources: `DotToFCdot/README.md`,
   `DotToFCdot/TermsTyped.lean`, `DotToFCdot/Erasure.lean`.

2. **Source essentials.** `R` is a fixed source type, for example `{b:top}`.
   The tiny object has recursive type `mu(z.{a:R})`. Opening its self type
   at `x` permits the projection. Sources: `DotMNF/Syntax.lean`,
   `DotMNF/Typing.lean`.

3. **Source type grammar.** Every raw recursive body is accepted by recursive
   introduction and elimination. Lambda domains and let result types have no
   type well-formedness restriction either. `Ty.Decl` and `Ty.isDecl` remain
   as translation classifiers; they impose no condition on source typing.
   The dependent function parameter binds only its codomain. Sources:
   `DotMNF/Syntax.lean`, `DotMNF/Typing.lean` (`HasTy.recI`, `HasTy.recE`).

4. **Source term grammar.** All term, value, and definition constructors
   are shown. There is no empty definition constructor. Object self binds
   in both member types and field terms; a lambda parameter binds in its
   body, and a let variable in its continuation. Distinctness applies across
   type and term labels. Source: `DotMNF/Syntax.lean`.

5. **Annotated frontend.** `WadlerFest` independently states the annotated
   rules of Amin et al., Figures 1--2. An object is `nu(z:T)d`, where self
   scopes over both annotation and definitions. Its ordinary context binds
   self at the opened body T. Definition conjunction enforces disjoint
   labels, rather than placing an additional distinctness premise on object
   introduction. Sources: `DotMNF/WadlerFest/Syntax.lean`,
   `DotMNF/WadlerFest/Typing.lean`. The public `WadlerFest.Sorted`
   interface uses distinct `TypeLabel` and `TermLabel` constructor arguments.
   Its typing and subtyping certificates cover all intermediate judgments,
   rather than only their endpoints. Sources: `DotMNF/WadlerFest/Sorted.lean`,
   `DotMNF/WadlerFest/LabelSorted.lean`.

6. **Opened-self correspondence.** `strip` is the slide notation for
   `eraseAnnotations`. It removes only object self annotations, unlike the
   shared-runtime erasure used later. Context simulation supplies a DOT-MNF
   variable-typing derivation for each annotated assumption. At literal self,
   recursive elimination derives the opened body from the local recursive
   self binding. Mutual recursion transports term, subtyping, and definition
   derivations. `HasTy.eraseAnnotations_closed` covers all closed annotated
   programs. This is a one-way typing correspondence; reverse annotation
   synthesis is not formalized. Source:
   `DotMNF/WadlerFest/Correspondence.lean` (`Ctx.Simulates.self`,
   `HasTy.eraseAnnotations`, `HasTy.eraseAnnotations_closed`).

7. **Bad bounds.** The display combines the two member-selection rules.
   In a hypothetical inconsistent context, subsumption can retype an
   already typed term arbitrarily. Source safety concerns closed programs
   and the stores they actually reach. Sources: `DotMNF/Typing.lean`,
   `DotMNF/Examples.lean`.

8. **Target type grammar.** These are the complete type, proposition, and
   telescope categories. All entries share the object's self binder; individual
   entries do not bind. A self-bound may mention that self in raw syntax and
   in a recursively folded type. The `bound`, `intoBnd`, and morphism-bound
   evidence rules introduce or extract bounds independent of a fresh self.
   To use a self-dependent bound, atom unfolding first opens it at the root.
   This permits recursively folded types with self-dependent bounds.
   Sources: `FCdot/Syntax.lean`,
   `FCdot/Typing.lean`, `DotToFCdot/Types.lean` (`Ty.telSelf`).

9. **Member type names.** The type x.ell belongs to the family of type
   names associated with variable x. A type-member selection x.A translates
   to this form; so does the named result type used for field a. A name
   alone establishes neither field presence nor an exact definition.
   Source: `FCdot/Syntax.lean`, `FCdot/Typing.lean`.

10. **Target types.** A block name is a type-level name attached to a
   variable. It does not establish that a term field exists. A telescope
   is an ordered list over one self binder; its entries do not bind.
   Sources: `FCdot/Syntax.lean`, `FCdot/Context.lean`.

11. **Evidence, judgments, and derivations.** A telescope contains proposition
   syntax. An alias such as e := refl(tau) defines an object-language proof
   term; Delta |- e : tau <= tau is its typing judgment. A calligraphic
   E :: Delta |- e : tau <= tau names a derivation of that judgment.
   The cast contains e, not E. Calligraphic H and D similarly name source
   typing and subtyping derivations. Sources: `FCdot/Syntax.lean`,
   `FCdot/Typing.lean`, `DotMNF/Typing.lean`.

12. **Casts.** Source subsumption becomes a target term constructor carrying
   inclusion evidence. Ordinary target term typing has no subsumption rule.
   Sources: `FCdot/Typing.lean`, `DotToFCdot/Terms.lean`.

13. **Target atom grammar.** All atom constructors are shown. The named
   self binders in fold and both scope only over their telescope annotations.
   Equal roots for both is a typing condition. Casts and recursive wrappers
   retain the receiver's original variable. Source: `FCdot/Syntax.lean`.

14. **Complete root definition.** The five clauses exactly follow
    Atom.root: a variable returns itself; cast, fold, and unfold recurse
    on their atom; both recurses on its first operand. Equal roots for
    both is a typing premise, not part of the definition of root.
    Root never traverses witness definitions or field bodies. Recursive
    object dependencies therefore do not threaten this structural recursion.
    Source: `FCdot/Syntax.lean`, `FCdot/Typing.lean`.

15. **Target term and value grammars.** Applications take atoms; projection
    also carries field-presence evidence. Both terms and values have cast
    constructors. A value cast is a wrapper. Lambda and let bind only in
    their bodies/continuations. Source: `FCdot/Syntax.lean`.

16. **Target object definitions.** Witnesses and fields are separate finite
    lists, each with empty and extension constructors. Object self scopes
    over both lists. Same-block aliases and cycles are allowed; raw lists
    may repeat labels, with later entries shadowing earlier ones.
    Source: `FCdot/Syntax.lean`.

17. **Declarations.** A type member contributes two inclusions. A field
   contributes presence and an inclusion from its named type. Weakening
   under the fresh self is implicit in the named notation.
   Source: `DotToFCdot/Types.lean`.

18. **Structural type translation.** Bottom, selections, and dependent
   functions translate directly. Top is the empty target object type.
   Intersection concatenates telescopes; recursion reads the body using its
   own self. Named notation suppresses weakening into a fresh binder.
   The two telescope functions differ exactly at that choice of self.
   Source: `DotToFCdot/Types.lean` (`Ty.translate`, `Ty.tel`, `Ty.telSelf`).

19. **Arbitrary intersection operands.** The object-shape test identifies
   top, declarations, intersections, and recursive types whose bodies have
   declaration shape. Any other operand enters `tel` as one self-independent
   bound on its whole translation. This includes a recursive type with a
   nondeclaration body even though its translation is syntactically an
   object type. It cannot simply contribute its `telSelf`, whose bounds may
   mention its own self. These are translation cases, not source restrictions.
   Sources: `DotToFCdot/Types.lean` (`Ty.isObj`, `Ty.tel_of_not_isObj`),
   `DotToFCdot/Evidence.lean` (`into`, `intoAtom`).

20. **Self-dependent recursive body.** The slide displays the essential
   opening step on `mu(z.z.A)`. Atom unfolding opens its bound at the root x,
   yielding an object with a bound independent of the new self w. A bound
   coercion may then extract x.A. The uniform `recEAtom` implementation also
   inserts a refold at `tel(T[x/z])`, which is type-preserving here. The
   inverse adapter packages the result in a one-bound telescope and folds.
   No inhabitation claim is being made for an arbitrary recursive type.
   Sources: `DotToFCdot/Types.lean`, `DotToFCdot/Evidence.lean`,
   `DotToFCdot/Examples.lean` (E12).

21. **Instantiate self.** The receiver's type lists propositions under
    the binder z. The root x supplies the variable that replaces z when
    those propositions are used. Field presence is relative to that self;
    inclusion endpoints explicitly substitute x for z. These are promises
    made by the type, before any evaluation of the stored field body.
    Source: `FCdot/Typing.lean`.

22. **Extract evidence.** read abbreviates the relevant member evidence
    constructor, with reflexivity as the object coercion. The definitions
    p := read(r,0) and e := read(r,1) introduce proof terms. Separate
    judgments in Delta establish field presence at x and inclusion from
    x.a to tau[x/z]. Substitution reaches the entire endpoint, allowing tau
    itself to refer to self. read constructs proof syntax without evaluating
    a runtime field. Source: `FCdot/Typing.lean`.

23. **Projection.** This is the actual projection clause of the translation.
   Presence evidence permits field access at `x.a`'s block-type name; the
   bound then casts the result to the advertised source type.
   Source: `DotToFCdot/Terms.lean`.

24. **Stable member identity.** This is the E4 acceptance test. In the
   translated context, x has exactly two facts: [[S]] <= x.B and x.B <= [[T]].
   The defined proof term e composes them. The atom cast(w,e) has type [[T]]
   and root w, so its lower-bound evidence concludes [[R]] <= w.A. Context
   consistency is not required: a total translation must handle derivations
   under these hypothetical assumptions. A fresh name from reopening a
   coerced existential package would not establish the needed fact about the
   original member. Sources: `DotMNF/Examples.lean` (E4),
   `DotToFCdot/Evidence.lean`, `paper/sections/overview.tex`.

25. **Object coercions.** The example is field covariance. The recipe copies
   fact zero and composes fact one with the given inclusion. Its side
   evidence lives in the outer context and cannot mention the fresh self.
   Composition therefore substitutes into numbered positions. Sources:
   `DotToFCdot/Evidence.lean`, `FCdot/FormAlgebra.lean`.

26. **Precise stores.** For the running one-field object, the witness defines
    its field-type name. Equality proves its advertised upper bound. A
    typed store keeps uncast literals at their own types; allocation
    moves their casts to uses. Inertness remains essential. Sources:
    `FCdot/Store.lean`, `FCdot/Machine.lean`, `DotToFCdot/Types.lean`.

27. **Concrete source program.** R is forall(y:top)top and rho is its
    target translation. Choose the direct derivation: variable and lambda
    rules for identity, field and object introduction, then recursive
    elimination and projection in the let body. No extra source subsumption
    is inserted. Sources: `DotMNF/Typing.lean`, `DotToFCdot/Terms.lean`.

28. **Concrete field translation.** Delta_z is the transparent literal self
    context: it records z at its precise object type, witness a=rho, and
    field presence a. This recorded definition authorizes def(z,a); an
    opaque assumption z at the same type would not suffice. The aliases
    delta_z := def(z,a) and kappa_z := eqToLe(symm(delta_z)) define proof
    terms; their separate judgments in Delta_z establish z.a == rho and
    rho <= z.a. DefsTy.translateFields inserts the latter cast around the
    lambda. Self z scopes over both W and F. Sources:
    `DotToFCdot/Terms.lean`, `DotToFCdot/Types.lean`,
    `FCdot/Context.lean`, `FCdot/Typing.lean`.

29. **Concrete object coercion.** Psi is the precise literal telescope,
    with equality at index 0 and presence at index 1. Phi is the advertised
    telescope, with presence at index 0 and the upper bound at index 1.
    The displayed m is exactly litMorphism for the one-field declaration:
    has(nil,1) supplies target fact 0; le(...,none,eq(0),none) supplies target
    fact 1 without additional side coercions. The alias chi := obj(Psi,m)
    is litCo. Its separate typing judgment has the empty context: chi is
    closed, as are the precise and advertised object types in this example.
    Sources: `DotToFCdot/Evidence.lean`.

30. **Complete translated program.** The receiver, presence proof, and
    upper-bound proof are metalevel abbreviations, not extra target lets.
    Before allocation, their judgments use the let-body context Delta_x,
    whose ordinary opaque binder gives x the advertised type mu(z.Phi).
    r_x = fold(z.Phi,unfold(x)) is the actual translation of the chosen Rec-E
    derivation. read(r_x,i) expands to member(r_x,refl(mu(z.Phi)),i).
    The field-body cast kappa_z is inside the object's self scope; the outer
    cast chi converts the precise literal type to the advertised type.
    The alias u names the complete target program; the separate judgment
    empty |- u : rho states its typing.
    Named notation suppresses weakening, alpha-renaming, and atom/value
    embeddings only. Allocation subsequently stores the bare literal and
    moves chi to its uses. Sources: `DotToFCdot/Terms.lean`,
    `DotToFCdot/Evidence.lean`.

31. **Source machine.** This is the continuation machine, not the retained-let
   reduction relation introduced later. Allocation extends the signature and
   weakens every pending frame. Variable binding instead substitutes the
   existing variable. Application consults the stored closure, and projection
   substitutes the receiver for the object self in the selected field body.
   The annotated machine differs only in retaining self annotations. Its
   annotation erasure preserves and reflects steps, finite runs, finality,
   and stuckness. Sources: `DotMNF/Machine.lean`,
   `DotMNF/WadlerFest/Machine.lean`, `DotMNF/WadlerFest/Erasure.lean`.

32. **Comparison invariants.** The direct baseline is Rapoport, Kabir, He,
    and Lhotak, A Simple Soundness Proof for Dependent Object Types (2017).
    Its direct argument retains typing with inert runtime assumptions.
    The displayed store-state invariant is a schematic adaptation, not a
    statement mechanized in DotMNF. Here Simulated instead retains some
    typed FCdot state with equal erasure; it does not retype source states.
    Sources: the 2017 paper, Section 3; [Safety.v][coq-safety];
    `DotToFCdot/Safety.lean`.

33. **Inert contexts and precise typing.** In the direct baseline, inert
    types are dependent functions or recursive records with exact type
    members and distinct type-member labels. Their field types and function
    domains need not be inert. Precise variable typing exposes a binding
    using lookup, recursive elimination, and intersection projection; it
    does not use general subsumption. Sources: the 2017 paper, Sections
    3.2-3.3; [PreciseTyping.v][coq-precise].

34. **Selection replacement.** Tight selection uses an exact member exposed
    by precise typing. In an inert context, a tight typing at {A:S..T}
    yields an exact member {A:R..R} and tight relations S <: R <: T.
    Compose these with tight selection to recover the two general selection
    conclusions. This enables general-to-tight typing; it does not remove
    transitivity from tight typing. Premises under new binders can remain
    general. Sources: the 2017 paper, Lemmas 3.4-3.5;
    [TightTyping.v][coq-tight], [GeneralToTight.v][coq-general].

35. **Using the direct inversion results.** For variables in inert contexts,
    general typing converts to tight typing and then invertible typing.
    The invertible rules separate a precise elimination phase from
    introductions, allowing induction to recover an original declaration.
    Field inversion supplies a precise field type below the advertised
    one; value inversion connects that type to a runtime object and body.
    This order of use differs from the construction order on slide 51.
    Sources: the 2017 paper, Sections 3.3-3.4;
    [InvertibleTyping.v][coq-invertible], [CanonicalForms.v][coq-canonical].

36. **Head-form grammar.** This is the complete current `Form` grammar.
   There is no `eqv` constructor. Both reflexive evidence and equality
   conversion normalize to `id`; typedness requires equal resolved endpoint
   shapes. Function forms retain typed inclusion proof terms, including the
   codomain evidence under its hypothetical parameter. `obj` carries `Entries`,
   while `into` carries the distinct `FreeEntries` category. Source:
   `FCdot/Normalizer.lean` (`Form`), `FCdot/FormTyping.lean` (`FormTyped`).

37. **Local and object entries.** These are exactly the `LocalEntry` and
   `Entry` constructors. A local template contains no general bound form.
   `copyBound` records the original position of a copied bound, unlike
   `bnd(F)`, which supplies a coercion from the whole input object. Object
   entries contain no `thru` routes. Composition operates on these grammars
   with a size measure. Sources: `FCdot/Normalizer.lean`,
   `FCdot/FormTyping.lean` (`EntryTyped`, `EntriesTyped`),
   `FCdot/FormAlgebra.lean`.

38. **Free entries and routes.** `FreeEntry` is either `bnd(F)` or
   `thru(F,L)`, and `FreeEntries` is its telescope-shaped list. The final
   component of a route is a `LocalEntry`, not an arbitrary `Entry` or
   `FreeEntry`; routes cannot nest in that component. A route reaches an
   intermediate object view before applying the local template. These
   entries are useful when pairing coercions whose facts do not refer to
   the same original telescope. Source: `FCdot/Normalizer.lean`
   (`FreeEntry`, `FreeEntries`, `freeEntryAt`, `freeEntriesAt`),
   `FCdot/FormTyping.lean` (`BndsTyped`).

39. **Views.** The complete `PropForm` and `View` grammars are shown.
   A precise stored literal supplies an equality form for each witness and
   a concrete location/label pair for each field. View equalities assert
   equal resolved shapes; they do not carry proof terms as payloads. A
   bound's form is typed from the root's own type, which matters when
   following an atom through recursive folding or bounds. Sources:
   `FCdot/Normalizer.lean` (`PropForm`, `View`),
   `FCdot/FormTyping.lean` (`ViewTyped`).

40. **Canonical forms theorem.** The slide suppresses the existential fuel
   bound and successful Option wrapper. Given a typed store and inclusion
   derivation, `le_canon` produces a typed head form. The mutual theorem also
   handles equality, presence, morphisms, atoms, and their cast chains.
   Equality identifies resolved endpoint shapes; presence proves a real
   stored field. The theorem normalizes store-closed evidence, not arbitrary
   open hypothetical contexts or complete programs. Source:
   `FCdot/CanonicalForms.lean`; see `FCdot/FormAlgebra.lean` for typed
   composition and application, and `FCdot/Resolution.lean` for alias cycles.

41. **Canonical forms.** The theorem normalizes evidence over a typed store
    to typed head forms. These expose the action of a cast at the resolved
    outer type shapes. The proof is mutual structural induction on evidence
    and atom typing derivations. Function forms provide argument/result
    coercions. This is neither program termination nor normalization in
    arbitrary hypothetical contexts. Sources:
    `FCdot/CanonicalForms.lean`,
    `FCdot/Progress.lean`, `FCdot/Consistency.lean`.

42. **Allocation.** The direct reconstruction recovers an inert precise
    type P below the type expected by the continuation, then narrows the
    unchanged continuation to x:P. FCdot decomposes the adapted value into
    a bare literal and composite coercion. It stores the literal precisely
    and rewrites uses of x to cast(x,e); typed substitution checks the new
    continuation. Weakening under the fresh binder is implicit. Its
    transparent binding records witnesses and fields. Sources:
    [Narrowing.v][coq-narrowing], [Safety.v][coq-safety];
    `DotMNF/Machine.lean`, `FCdot/Preservation.lean`.

43. **Direct application.** Inversion recovers the actual closure domain S0
    and body type T0, with S <: S0 and T0 <: T under x:S. The slide follows
    one valid reconstruction: narrow the body, subsume its result, then
    substitute the argument. Equivalently, first subsume the argument to
    S0, substitute, then subsume the result. Neither order adds source
    syntax: the reduct is t0[y/x]. This source preservation development
    is not mechanized locally. Sources: [CanonicalForms.v][coq-canonical],
    [Narrowing.v][coq-narrowing], [Substitution.v][coq-substitution],
    [Safety.v][coq-safety]; `DotMNF/Machine.lean`.

44. **Target application.** This is the pi-head-form case. Canonical forms
    supply d:tau<=tau0 and codomain evidence c under the advertised domain
    tau. The closure receives cast(s,d); the result is cast by c[x:=s].
    These substitutions use different atoms but the same root, so the
    result types agree. Ordinary typed substitution establishes preservation.
    Bare-variable and identity-form application cases omit these casts.
    Equality proof terms normalize to the identity form. Sources: `FCdot/Machine.lean`,
    `FCdot/Preservation.lean`, `FCdot/CanonicalForms.lean`.

45. **Projection.** The direct reconstruction combines variable/value
    inversion, self substitution, and subsumption at an intermediate field
    type. FCdot instead stores each field body at its self block name z.a.
    Presence canonical forms prove that lookup succeeds; projection itself
    looks up the body without evaluating the presence proof. Replacing self
    by x gives a body at x.a, and the pending explicit cast supplies the
    advertised result type. Sources: [CanonicalForms.v][coq-canonical],
    [Safety.v][coq-safety]; `FCdot/Typing.lean`,
    `FCdot/Progress.lean`, `FCdot/Preservation.lean`.

46. **Transitivity and composition.** Assume a typed store. N_Sigma denotes
    head normalization, with sufficient fuel and successful Option wrappers
    suppressed. Form.combine_typed proves that
    composing typed forms succeeds and preserves their endpoints, by an
    induction on form sizes. The subsequent canonical-forms proof uses
    this lemma in its transitivity case. This is head normalization:
    function forms retain typed domain and codomain evidence, potentially
    containing transitivity, rather than normalizing under the parameter.
    Sources: `FCdot/Normalizer.lean`,
    `FCdot/FormAlgebra.lean`, `FCdot/CanonicalForms.lean`.

47. **Composition of templates.** The field-covariance example composes
    two recipes by substituting the first recipe into the second's indexed
    hole. Side evidence is typed in the ambient context before adding self;
    it need not be closed in the empty context. Its normalization therefore
    uses the same typed store, without introducing a hypothetical self.
    After side normalization, template composition and application use
    typed forms and views. Sources: `FCdot/Typing.lean`,
    `FCdot/Normalizer.lean`, `FCdot/FormAlgebra.lean`.

48. **Why restrict morphisms?** The unrestricted evidence body is a
    hypothetical alternative, not an FCdot constructor. Its self binder
    has no stored literal, so the closed-store normalization hypothesis
    does not apply. Substituting a receiver produces new evidence outside
    the original induction hypothesis. Templates avoid that obligation by
    combining already typed forms and looking up existing view entries.
    Do not claim every executable recursive call is on a raw subterm:
    the bound-view case combines a retrieved form with the remaining form,
    then applies the result at the root. Its proof uses the previously
    established composition and root-view lemmas. Sources:
    `FCdot/FormTyping.lean`, `FCdot/Normalizer.lean`,
    `FCdot/FormAlgebra.lean`, `FCdot/CanonicalForms.lean`.

49. **Cast substitution.** Both displayed parameter bindings are opaque.
    Typed substitution adapts evidence under x:tau to x:tau' by replacing
    x with cast(x,e); weakening e into the extended context is implicit.
    The proof syntax changes, while the identity root map leaves dependent
    endpoint types unchanged. Function-form composition uses this operation
    on codomain evidence, without normalizing it under the binder.
    Allocation uses its transparent-binding variant to retain casts at
    uses of a precisely stored literal. Thus the source All translation
    needs no narrowing lemma, but the target still performs binder
    adaptation. Sources: `FCdot/TypingSubst.lean`,
    `FCdot/Preservation.lean`,
    `FCdot/FormAlgebra.lean`, `DotToFCdot/EvidenceTyped.lean`.

50. **Bad bounds and consistency.** The bad binder is an ordinary opaque
    assumption, and the displayed evidence is legal in that hypothetical
    context. A typed store cannot realize this context: canonical forms
    rule out evidence from top to bottom there. Consistency is derived
    from store typing and canonical forms, not assumed for every context
    or used to establish the main normalization theorem. Along execution,
    preservation maintains the precise store discipline. Sources:
    `FCdot/Consistency.lean`, `FCdot/Store.lean`,
    `DotToFCdot/Consistency.lean`.

51. **Both dependency orders are acyclic.** The direct 2017 construction
    establishes narrowing and precise-type facts, tight-to-invertible
    conversion, selection replacement, general-to-tight conversion, then
    canonical forms and safety. This is not the order in which those
    conversions are used at a runtime redex. FCdot establishes typed atom
    substitution and resolution, form composition/application, precise views
    and canonical forms, then final target preservation/progress. Its
    Preservation module first proves a conditional theorem with FormsTyped;
    FormAlgebra imports its substitution lemmas, and CanonicalForms later
    discharges that premise. Precise store typing retains inertness in this
    organization. Neither argument depends on a circular theorem proof.
    Sources: [GeneralToTight.v][coq-general],
    [InvertibleTyping.v][coq-invertible], [Safety.v][coq-safety];
    `FCdot/Preservation.lean`, `FCdot/CanonicalForms.lean`.

52. **Typing preservation.** Context well-formedness requires precise
    literal self bindings with exact definitions and distinct labels.
    It does not require consistent bounds for ordinary assumptions.
    Sources: `DotToFCdot/EvidenceTyped.lean`,
    `DotToFCdot/TermsTyped.lean`.

53. **Erasure and coherence.** Erasure equality holds without the context
    well-formedness premise. Coherence is literal equality of erasures for
    two typings of the same term, even at different result types.
    It is not a separate full-abstraction theorem.
    Source: `DotToFCdot/Erasure.lean`.

54. **Simulation.** The invariant existentially relates a source state to
    a typed target state in the same signature with equal erasure. Erase a
    source step, reflect the runtime step to a target run, and preserve the
    target's typing. The resulting target witness establishes Simulated
    for the source reduct without constructing its source typing derivation.
    For progress, exhaust the finitely many pending cast-frame steps before
    transferring target finality or a genuine runtime step back to source.
    Sources: `DotToFCdot/Safety.lean`.

55. **Safety.** No reachable source state is stuck. The source proof uses
    translation and simulation; runtime shape reasoning resides in target
    canonical forms. Every target store reached by the translation of a
    closed well-typed source program also remains consistent. Sources:
    `DotToFCdot/Safety.lean`, `DotToFCdot/Consistency.lean`.

56. **Retained-let computation.** `Retained.Red` independently presents
   the paper's rules on annotated terms. The ambient store records enclosing
   value lets; the bindings themselves remain in the term. At top level
   it is empty. Application and projection use that surrounding environment,
   while alias elimination substitutes an existing variable. Field selection
   is relational membership (`Defs.HasField`), not right-biased lookup.
   Typing gives distinct labels in every nested object, reconciling membership
   with machine lookup. Source: `DotMNF/WadlerFest/Reduction.lean`.

57. **Overlapping reductions.** Both `letRHS` and `letValue` rules are
   present without priorities. Reassociation may overlap with an internal
   right-hand-side step. The rules are not defined by readback or by a
   selected machine strategy. Named notation suppresses the lifted weakening
   of w in the associativity rule. Source:
   `DotMNF/WadlerFest/Reduction.lean` (`Red.assoc`, `Red.letRHS`,
   `Red.letValue`); `DotMNF/WadlerFest/OperationalExamples.lean` checks
   nested-let applications whose reduction orders reconverge.

58. **Readback.** `Cont.plug` rebuilds pending let contexts and `Store.close`
   rebuilds retained value lets. `State.readback` composes them. A frame push
   changes no term. Allocation can move a newly stored value outside several
   pending frames, corresponding to several retained reassociations.
   `Step.readback` therefore gives zero or more retained steps, and
   `Steps.readback` extends this to finite runs. Sources:
   `DotMNF/WadlerFest/Readback.lean` (`Cont.plug`, `Store.close`,
   `State.readback`, `Step.readback`, `Steps.readback`).

59. **Finite observations.** Answers are exactly variables, values, and
   answers under retained value bindings. The observed result is the exact closed
   annotated term reconstructed by readback, including all retained bindings.
   A stuck term is neither Answer nor reducible. Sources:
   `DotMNF/WadlerFest/Reduction.lean` (`Answer`, `Stuck`),
   `DotMNF/WadlerFest/MachineBehavior.lean` (`Outcome`, `Behavior`),
   `DotMNF/WadlerFest/Readback.lean` (`State.Final.readback`).

60. **Backward finite-behavior preservation.** For any retained step and
   continuation, a finite machine behavior of the reduct can be reconstructed
   for the original term. Behaviors record either stuckness or an exact
   readback answer. Reassociation uses `Cont.Fuses`, while reduction beneath
   a retained value uses allocation and the extended store. The only source
   invariant is distinctness throughout the syntax, supplied by typing and
   preserved by reduction. Sources:
   `DotMNF/WadlerFest/OperationalCorrespondence.lean` (`Red.behavior_back`,
   `Steps.behavior_back`), `DotMNF/WadlerFest/MachineBehavior.lean`
   (`Cont.Fuses.behavior_back`), `DotMNF/WadlerFest/WellFormed.lean`.

61. **Operational correspondence.** `answer_iff_machine` assumes a closed
   term t with distinct definitions throughout and an answer q. It equates
   a retained run to q with a machine run to a final state whose readback is
   exactly q. `stuck_iff_machine` equates existence of finite stuck runs.
   A stuck machine state's raw readback need not itself be stuck: pending
   frames may require reassociation first. The theorem accounts for those
   steps. No divergence equivalence, strong bisimulation, source preservation,
   or confluence theorem is claimed. Source:
   `DotMNF/WadlerFest/OperationalCorrespondence.lean`
   (`answer_iff_machine`, `stuck_iff_machine`).

62. **Safety for all retained orders.** Assume an annotated typing derivation
   and any finite retained run. A stuck reduct yields a stuck machine
   behavior; backward behavior preservation lifts it to the initial program.
   Annotation erasure, DOT-MNF translation, and FCdot safety exclude that
   behavior. Syntactic trichotomy then gives Answer or a further retained
   step. This theorem covers every reduction order, including overlaps
   between reassociation and evaluation-context steps. Source:
   `DotToFCdot/RetainedSafety.lean` (`Retained.not_stuck`, `Retained.safety`),
   `DotToFCdot/WadlerFest.lean` (`dot_safety`, `dot_not_stuck`).
   The public theorem `WadlerFest.Sorted.safety` additionally packages every
   successor in the label-sorted syntax. Its translation preserves typing
   and erasure through the same route. Source: `DotToFCdot/SortedSafety.lean`.

63. **Mechanized scope.** The public `WadlerFest.Sorted` interface enforces
    disjoint type-label and term-label categories in syntax and in each
    judgment of its derivations. Forgetting the certificates exposes the
    internal annotated calculus, whose typing correspondence and FCdot
    translation remain unchanged. Public retained reduction is closed on
    sorted syntax. The implementation is intrinsically scoped; it does not
    formalize a conversion from named terms modulo alpha-equivalence.
    Variable paths, arbitrary recursive bodies, arbitrary intersections,
    and same-block aliases are covered. Recursive subtyping is absent from
    WadlerFest itself; pDOT-style stable paths require separate identities
    and lookup metatheory. Sources: `DotMNF/WadlerFest/Sorted.lean`,
    `DotMNF/WadlerFest/LabelSorted.lean`, `DotToFCdot/SortedSafety.lean`,
    `DotMNF/README.md`.

64. **Source rules.** The local source has variable paths, unrestricted
    intersections, and arbitrary recursive bodies. There is no `Ty.Wf`
    premise on recursive introduction/elimination, function annotations, or
    let result types. Object definition typing supplies exact type members
    and checks field bodies. The object rule also requires distinct labels.
    Sources: `DotMNF/Syntax.lean`, `DotMNF/Typing.lean`.

65. **Evidence reference.** These are object-language constructors for
    inclusion, equality, presence, and telescope morphisms. The codomain
    evidence in pi(e,x.f) binds x. Telescope annotations bind self, while
    template sides are checked before that self is added. Proof-term
    definitions remain distinct from the displayed typing judgments.
    Sources: `FCdot/Syntax.lean`, `FCdot/Typing.lean`.

66. **Morphism syntax and judgments.** This is the complete `Hole`, `Side`,
   and `Morphism` syntax. `none` acts as identity and may have self-dependent
   endpoints. A present side `some(e)` is checked in the outer context,
   before the fresh self binder. A bound entry uses evidence from the entire
   source object type and produces a self-independent bound. The four
   displayed judgments check different proof families; none is itself a
   proof-term definition. Sources: `FCdot/Syntax.lean`, `FCdot/Typing.lean`.

67. **The two telescope translations.** `tel` weakens source endpoints
   under a fresh self. `telSelf` reuses the body's innermost self, so its
   nonobject case does not weaken the bound. Recursive declaration bodies
   can flatten their propositions; other recursive types enter `tel` as one
   bound on their complete translation. Nested recursive declaration bodies
   in `telSelf` open their inner telescope at the current self. `Ty.Decl`
   is only a classifier used to make these cases correct. It no longer
   restricts any source typing rule. Source: `DotToFCdot/Types.lean`.

68. **Recursive adapters and precise types.** `recIAtom` puts the opened body
    into its telescope with `intoAtom`, unfolds at the root, then folds with
    `telSelf`. `recEAtom` unfolds the recursive atom, refolds at the telescope
    of the opened source body, and extracts its sole bound if that body is
    not an object shape. `Ty.tel_substVar` equates the relevant opened
    telescopes. Both adapters preserve the root and erasure. This admits
    functions, selections, unrestricted intersections, and nested recursive
    bodies without changing FCdot typing or its safety argument. Precise
    literal types still record one equality per witness and field presence.
    Sources: `DotToFCdot/Evidence.lean` (`recIAtom`, `recEAtom`),
    `DotToFCdot/TypesLemmas.lean` (`Ty.tel_substVar`),
    `DotToFCdot/Examples.lean` (E9--E12).

69. **A different direct strategy.** Rompf and Amin, Type Soundness for
    Dependent Object Types (DOT) (2016), Section 6.1, prove narrowing for
    abstract bindings structurally while retaining transitivity as a rule,
    then prove transitivity pushback where the abstract context is empty.
    That supplies subtyping inversion in concrete runtime contexts. This
    ordering is already acyclic. Their calculus includes recursive
    subtyping; local DotMNF instead has variable Rec-I/Rec-E and no recursive
    subtyping rule. Do not describe pushback as a requirement of all direct
    DOT proofs: the main 2017 comparison uses tight and invertible typing.

Comparison sources and scope: the main direct baseline is Rapoport, Kabir,
He, and Lhotak,
[A Simple Soundness Proof for Dependent Object Types](https://arxiv.org/pdf/1706.03814).
It and local DotMNF both have variable paths, unrestricted intersections,
and arbitrary term bodies in fields. The annotated WadlerFest frontend retains the paper's self-type annotations
and opened-self assumptions. Annotation erasure has a proved typing and
machine correspondence with local DOT-MNF, whose self context remembers
literal definitions at a recursive type. Both admit arbitrary recursive
bodies. The presentation compares proof obligations and organization;
the direct 2017 proof itself is not re-mechanized in this repository. The separate
reference is Rompf and Amin,
[Type Soundness for Dependent Object Types (DOT)](https://namin.seas.harvard.edu/files/soundness_oopsla16.pdf).
Both published direct strategies already give acyclic proof organizations;
the translation changes the judgments and evidence carrying the obligations.

Public Coq entry points for the 2017 comparison:

| File | Relevant definitions or theorems |
| --- | --- |
| [TightTyping.v][coq-tight] | `ty_trm_t`, `subtyp_t` |
| [PreciseTyping.v][coq-precise] | `precise_inert_typ`, `pf_inert_unique_tight_bounds` |
| [InvertibleTyping.v][coq-invertible] | `tight_to_invertible`, `invertible_typing_closure_tight` |
| [GeneralToTight.v][coq-general] | `sel_premise`, `sel_replacement`, `general_to_tight` |
| [CanonicalForms.v][coq-canonical] | `canonical_forms_fun`, `canonical_forms_obj` |
| [Narrowing.v][coq-narrowing] | `narrow_rules`, `narrow_typing` |
| [Substitution.v][coq-substitution] | `subst_ty_trm` |
| [Safety.v][coq-safety] | `sta_trm_typ`, `val_typing`, `preservation`, `progress` |

The companion [evaluation-context Safety.v][coq-safety-ec] corresponds to
the paper's evaluation-context presentation. The main artifact links above
use its store-machine development; the slide invariant remains schematic.

[coq-tight]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/TightTyping.v
[coq-precise]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/PreciseTyping.v
[coq-invertible]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/InvertibleTyping.v
[coq-general]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/GeneralToTight.v
[coq-canonical]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/CanonicalForms.v
[coq-narrowing]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/Narrowing.v
[coq-substitution]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/Substitution.v
[coq-safety]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/Safety.v
[coq-safety-ec]: https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof-ec/Safety.v

Circularity clarification: the source E2 example defines a recursive member
A = forall(y:z.A)z.A; E7 defines the mutual aliases A=z.B and B=z.A.
Both are mechanized in `DotMNF/Examples.lean`. Field bodies can also be
mutually recursive: nu(z.a=z.b & b=z.a) has type
mu(z.{a:top} & {b:top}) by recursive elimination and projection in the
self context. Projecting a alternates between the two fields under
`DotMNF/Machine.lean`; this last example follows from the rules and is
not a separately checked example in this revision. Alias head resolution
maps a constructor-free cycle to top for canonical-form reasoning; it does
not establish an equality of that alias with top or evaluate field bodies.
