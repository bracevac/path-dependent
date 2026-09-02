# Coercions

Lean formalizations of type-preserving translations from DOT fragments into
explicit-coercion calculi.  This directory was cut down in September 2026 to
the parts that carry general theorems; the removed material (captured DOT
sources, the many-sorted cumulative compilers, the checked front end, the
certificate study, the classifier and Capybara case studies, and the
intersection, recursive-object, and path-alias FCsub layers) lives in git
history before the `coercions-cut` branch.

- `FCsub` is the standalone type-constraint target: System F-sub with
  explicit coercions, telescope-constrained quantifiers, and head-guarded
  recursive projections.  It has `progress`, `preservation`, and a total
  checker with `checkTerm_iff` completeness.
- `DOT/Acyclic` is the acyclic, variable-path, one-type-member-per-object
  DOT source (`Source`) and its explicitly coerced Stage A form (`Explicit`)
  with elaboration, normalization, and a checker.
- `Translation/Acyclic` and `Translation/StableRoots` are the DOT-to-FCsub
  bridge.  `StableRoots.TermTranslation.compile` is total on the
  `StableHasTy` fragment and `sound` gives target typing, literal erasure
  equality, and a source-to-target step correspondence.
- `ManySortedFC` is the static layer of the two-sorted (type and capture)
  target: syntax, checked evidence, sound and complete evidence and term
  checkers, theory models and maps, a closed consistency model, a
  separation consistency model distinguishing read-only overlap from
  disjointness, and a decidable ground classifier kind algebra.  It has no
  operational semantics or type-safety theorem.

Known limits that the next milestone must address: source objects carry no
term members and erase to a constant; FCsub has no products, no recursive
values, and no intersection types; no term compiler exists for
intersections, recursive self types, or general paths; `StableHasTy` is a
side predicate on derivations rather than a source-level fragment; and no
closed-context consistency or coherence theorem exists for the bridge.

Example and regression files use `native_decide`, so those specific results
depend on `Lean.ofReduceBool`.  The core metatheory uses only `propext` and
`Quot.sound`.

`All.lean` imports the complete development.
