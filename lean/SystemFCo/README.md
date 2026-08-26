# SystemFCo

`SystemFCo` is a small System-FC-like target with **object-language directed
coercions**. It is not the store-indexed semantic-evidence construction used
by the LambdaP developments.

The target has three binder sorts in one ordered signature: term variables,
type variables, and coercion variables. Its terms include term/type/coercion
abstraction and application, plus an explicit cast `cast e gamma`. Its
coercion syntax includes variables, reflexivity, composition, `Top`, function,
polymorphic, and coercion-qualified coercions. There is no target subtyping
judgment and no target subsumption rule: a typed `cast` is the only way to
change an expression's type.

Casts have an explicit administrative semantics. Reflexive casts disappear,
compositions split, and structural casts push through matching term, type, or
coercion applications. Consequently, saying that coercions erase requires a
separate operational-correspondence theorem; target type safety alone does
not establish erasure.

The development proves:

- typing preservation under mixed renaming and substitution;
- stability of values and reduction under heterogeneous substitution;
- progress for closed target expressions;
- one-step and finite-step preservation;
- deterministic reduction; and
- finite type safety (`SystemFCo.Exp.soundness`).

`ChurchPackage.lean` builds hidden type witnesses with explicit lower and
upper coercion fields entirely as a library over the core calculus. This is
the package representation used by the path-dependent translation.

Build with:

```sh
lake build SystemFCo
```
