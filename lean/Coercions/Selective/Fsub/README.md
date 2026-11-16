# Selective subtyping for full F-sub

This directory studies selective subtyping in plain full System F-sub, where the idea can be seen
without path dependency. Types are `Top | X | S → T | ∀(X <: S). T`, and the rule for universals is
the full one: bounds are contravariant and bodies are compared under the target bound.

The primitive relation `Γ ⊢ S ≤₀ T` (`Prim`) has five rules: reflexivity, `Top`, the declared bound
of a variable, arrows and universals. It has no transitivity rule, transitivity is not admissible
(`primitive_nontrans`), and `prim?` decides it (`prim?_iff`). Everything else is a certificate, and two
forms are enough:

```text
Γ ⊢ S ≤₀ T                         Γ ⊢ c : S ⇒ M    Γ ⊢ d : M ⇒ T
──────────────────────             ──────────────────────────────
Γ ⊢ step[S,T] : S ⇒ T              Γ ⊢ c ; d : S ⇒ T
```

`coercion_iff` says that a certificate from `S` to `T` exists exactly when `S <: T` holds in
declarative full F-sub with its transitivity rule. No further constructor is needed for the
metatheory: lifting a certificate under an arrow or a universal, narrowing a bound, substituting a
type, and inverting a certificate between two arrows or two universals are functions on certificates
built from `step` and `;` (`Cert.narrow`, `Cert.inst`, `Cert.arrInv`, `Cert.allInv`, with the typing
lemmas `CTy.narrow`, `CTy.inst`, `CTy.arr_inv`, `CTy.all_inv`).

Terms are `x | λ(x : S). t | t u | Λ(X <: S). t | t [U] | t ▷ c`. The typing judgment `HTy` has no
subsumption rule. It applies one primitive comparison at the argument of an application and at the
bound of a type application, and a cast applies its written certificate. A term has at most one type
(`HTy.unique`), and `synthTm` checks it (`synthTm_iff`). Progress, preservation and safety are
proved directly on erased terms, for terms closed in term variables. Preservation shows that the
reduct has an annotation; it does not compute one.

`typability_iff` relates the calculus to declarative F-sub: `FTy Γ Δ e T` holds exactly when some
annotated term with erasure `e` has type `T`. `FTy` is stated with a subsumption rule over `Sub`,
which has a transitivity rule, and uses no certificate. So every declarative typing has an
elaboration at the same type with the same erasure (`elaboration_complete`), and every typed
annotated term erases to a declaratively typed one (`elaboration_typed`). `FTy` is a proposition, so
these are statements that an annotated term exists. The elaboration itself is a function on
derivations given as data: `FDer` is the type of derivations of `FTy`, `FDer.elab` returns the
annotated term, `FDer.elab_erase` says it erases to the source term and `FDer.elab_typed` that it
has the same type (`Elab.lean`). For subtyping, `Sub.toCert` is the function from derivations to
certificates.

Compared with the DOT design `H` in the parent directory, F-sub needs no evidence beyond `step` and
`;`, because a variable's bound is read from the context and never depends on the typing of a
receiver. [`../Bridge`](../Bridge/README.md) translates these certificates into `H`.

The checker decides validity of a given certificate. `coercion_iff` relates certificate existence to
full F-sub subtyping; it supplies no procedure for deciding existence.

[`REFERENCE.md`](REFERENCE.md) has the module list, the theorem inventory and the limits of the
implementation. The library imports nothing outside this directory. From the repository root:

```sh
lake build SelectiveFsub
lake env lean lean/Coercions/Selective/Fsub/Axioms.lean
```
