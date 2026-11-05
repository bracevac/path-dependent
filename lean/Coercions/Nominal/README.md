# Nominal

pDOT-C, pDOT with classes and traits, by coercions.  This tree is a copy of `PDot/` (plan X and its
front end of plan XI) that adds one definition and two rules to the source and a class primitive to
the target.  A class definition `{class C = T}` declares the class `C` with the bounds `⊥` and `T`,
so the declaration puts nothing below `p.C` but `⊥`.  The seal `subtyp_seal` gives `T <: p.C`,
only inside the literal that defines `C`.  Every source derivation translates to a typed
term of FCn, which is FCp with a class entry and a seal, and FCn is type safe.  So pDOT-C's safety is
proved about its own reduction and lookup, as plan X proves pDOT's.  The front end types programs
with classes, in the paper's notation and as Scala files, and its search is nominal: it reaches a
class type only through declared parents, aliases of paths and `⊥`, or by the seal at a
constructor's instance.  The design is plan XII (`plan-12-nominal.md`).  The PDot tree does not
change.

## What is proved

- `Nominal.safety`, `Nominal.reachable_typed`, `Nominal.reachable_run` (`Translation/Safety.lean`):
  the three theorems of plan X with their statements, about pDOT-C derivations.  Let
  `d : HasTy .nil t T` type a closed source term and `Reds ⟨[], .nil, t⟩ c` be a run.  Then the
  term of `c` is a normal form or `c` takes a step, and a path in focus has a safe lookup.  The
  erasure of `c` is the erasure of an FCn state typed at `⟦T⟧`, over a store that proves no
  `⊤ ≤ ⊥`, and the FCn machine runs the image of `d` to a state with that erasure.
- `HasTy.translate_typed`, `Sub.translate_typed`, `DefsTy.translate_typed`: in related contexts the
  image of a derivation is typed at the translated type.  Rel-Self also asks that each class of a
  self type is the class entry of the target at the same path (`Ctx.ClsAgree`), and
  `Ctx.rel_translate` relates a class-free context to its translation.
- `HasTy.plain_of_clsFree`, `Ctx.selfCls_none_of_classFree`: a class-free term in a class-free
  context uses neither new rule.  So plan X's pDOT is the class-free restriction of pDOT-C.
- FCn's theorems are FCp's, with the cases of DF-Cls and LE-Seal: preservation, progress,
  `erase_reflect'`, `reachable_consistent`, the canonical forms of closed evidence, `no_top_le_bot`
  and `checkTm_iff`.  The FCn README states them.
- `Factor.sub`, `Ty.Structural.not_factor`, `class_order` (`Source/Nominal.lean`): a factorization
  through `p.C` is a subtyping, no structural type factors through a class type, and between class
  types a factorization is the order of declared parents up to aliases of paths.
- NOM-A, the search (`Frontend/Pipeline.lean`).  `sub?_nominal`: every answer of the front end's
  search to `S <: p.C`, with `C` a class label of the run and in any context, factors.  `S` goes up
  through operands of `∧`, upper bounds read off views and alias replacements to `⊥` or to `q.C`
  with `q` an alias of `p`.  `path?_nominal`: every answer to `q : p.C` comes from a view of `q`
  that factors, or `q` is a tagged instance of a class below `C`.  `path?_structural`: a path whose
  views are all structural and that is no tagged variable has no class type.
- NOM-B, the program.  `compile_nominal_resolved`: every step into a class type of a compiled
  derivation carries its certificate.  `compile_seal_sites`: every seal of a compiled derivation
  is the last step of a path answer at a tagged variable.  For a Scala file, `ofScala_tags` says
  that the mapping writes a tag only on a constructor's instance literal, and `scala_seal_sites`
  puts the three together for an `ok` outcome.
- `provenance`, `provenance_focus` (`FCn/ProvenanceClass.lean`): in a reachable state of a typed FCn
  program that meets `Tm.InitSeals`, a path at a class selection, of every former but a field
  selection and `unfold`, that meets the provenance predicate under the run's records names up to
  `canon` a store variable whose record holds a key at a class below its class.  The key says that
  the allocating scope permits a seal of the variable at that class, in code that may be dormant
  (`ProvEx.Dormant` in `FCn/ProvenanceExamples.lean`).  The path in focus meets the predicate.
- The examples.  E14, a trait and a class that extends it, is typed by hand
  (`Source/Programs.lean`), its image is checked in FCn with two class entries and three seals
  (`E14_checks`), and it runs on both machines to one runtime configuration (`Pages.E14`).  The
  same program written in the notation, `Run_src` in `Frontend/Examples.lean`, is compiled by the
  front end at the body of the trait, checked in FCn and run.  193 Scala files under
  `scala/nominal/` are judged in the kernel against their headers (`ScalaCorpus/Nominal.lean`).

## What it leaves out

- The nominality theorem is about the derivations that the front end's search builds.  It is not
  stated over the declarative `Sub`, where a binder at `⊥` or an alias with bounds at `C` puts `⊤`
  below `p.C`, nor over closed evidence in a typed FCn store, where a forged instance meets every
  canonical form of the class primitive (plan XII, "What is not claimed").  Stage NT stops FCn's
  closed reading at classes, so a class is opaque outside its seal, and proves those canonical forms
  in `FCn/ClassForms.lean`.  They are no nominality theorem.
- The provenance theorem of stage NR (`FCn/ProvenanceClass.lean`) is proved for FCn programs that
  meet its initial condition, and the initial condition is checked on named compiled programs
  (`Frontend/Provenance.lean`).  That every program the front end compiles meets it is not stated:
  the front end's certificates record the tagged variable of a seal, not that the seal's owner is
  older.  The corollary is not proved at a field selection or at `unfold`.  An allocation record
  is not by itself a log of executed constructors or executed seal uses, so no run-time class tag
  and no constructor authenticity is claimed.
- Type parameters, `super`, anonymous and local classes, classes inside classes, `object o extends
  T`, overloading, parents not reached through objects, cyclic inheritance and imports are outside
  the Scala subset.  The reader refuses each with a rule and a position.
- The typer's fuel stays `2 ^ 15`.  A chain of four classes, each with a constructor argument and a
  method, answers `limit`, and so does a diamond of five classes that scalac accepts.  The field
  `super$K` that checks the parent arguments of a class costs fuel from the same tank.  A file whose
  argument obligations do not hold by their form can answer `limit` where scalac accepts it.  An
  abstract class `K(x)` that gives its parent the unstable `x.y`, with a concrete `L(z) extends
  K(z)`, answers `limit` and is `ok` at `2 ^ 22` with 38565 units.  Six abstract classes that each
  give their parent a subclass argument three times answer `limit` and are `ok` there with 97226
  units.  A file that scalac rejects can answer `limit` too, where a failing subtyping goes through
  module aliases in nested objects: a parent's parameter at an alias of one class, given an
  argument at an alias of another class, answers `limit` and is `rejected` at `2 ^ 22` with 45000
  to 105000 units.
- What the PDot tree leaves out holds here too: pDOT's disjunctive safety and its own preservation
  are not stated, and FCn types some terms that pDOT-C rejects, among them `x : x.type`.

## Layout

`Source/` is pDOT as its Coq formalization states it, transcribed in plan X, with the class
definition `Def.cls` and the rules `ty_def_cls` and `subtyp_seal` of pDOT-C.  `Ctx.selfCls` reads
the class that a self binder declares at a path.  `Nominal.lean` holds the nominal vocabulary
`IsView`, `Up`, `Factor` and `ClassReach` with its three theorems.  The fidelity table of its README
marks the three rows that Coq's pDOT has not.

The runtime is `../PDot/Runtime.lean`, imported and not copied, since both trees erase into the same
untyped pDOT.

`FCn/` is the target.  A literal may hold a class entry, DF-Cls declares it with the bounds `⊥` and
its body, and the seal `seal p C` (LE-Seal) includes the body in `p∙C` where the block at `p` holds
the entry.  Every theorem of FCp holds, with the new cases.

`Translation/` maps a class definition to a class entry and a seal to a seal, with Rel-Self's
premise `ClsAgree`, and carries FCn's safety to pDOT-C.  Its examples check and run E14.

`Frontend/` is the front end, the libraries `NominalFrontend`, `NominalScalaRead` and
`NominalScala`, which are not default targets.  A program is written under `pdc%`, with the class
forms `class C = T` and `ν(x) as p.C {ds}`, or as a `.scala` file whose classes and traits the
mapping turns into class definitions, module functions, witnesses, constructors with tagged
instances and forwarders.  The search carries the certificates of NOM-A.  The checks of `ScalaClasses`
reject scalac's override and shape errors with scalac's message, shortened for OV-Abstract and
OV-Private.  OV-Private rejects a plain constructor parameter named in a member's signature.  Its
second walk at an alias removes the report only where scalac's does, on the corpus and on the
review probes.  That is tested, not proved.  See [Frontend/README.md](Frontend/README.md).

## Building

`lake build Nominal` builds the calculus, and `Nominal` is a default target.  `lake build
NominalFrontend NominalScalaRead NominalScala` builds the front ends.  `lake build
ScalaCorpusNominal` judges the corpus in 6 min 20 s at a peak of 12.0 GB (plan XII, D-19).  The path
layer is imported from `Paths/FCdot` and the runtime from `PDot/`, and neither tree changes.  The
tree has no `sorry`, `axiom`, `native_decide`, `partial`, `unsafe`, `implemented_by`, Mathlib or
`aesop`.  The roots `Frontend.lean`, `Frontend/ScalaRead.lean` and `Frontend/ScalaCmd.lean` end
with `#assert_no_wf`, and every theorem that a stage of plan XII names depends on `propext` and
`Quot.sound` at most (`#print axioms`, at each stage).

## What is taken from Martres' thesis, and what differs

Guillaume Martres, *Type-Preserving Compilation of Class-Based Languages* (EPFL thesis, 2023),
compiles Featherweight Java, then classes with traits and type parameters, then Dependent Scala,
into DOT.  The pages below are the thesis's own page numbers (plan XII, D-23).

Taken.

- The class table as one object bound before the program (Figure 3.7, p.29, and
  `let ct = {ct ⇒ (|CT|)} in |e|`, p.30).  Ours is the stem literal of the Scala mapping, which
  holds the classes of a file at the paths of their objects, so a class reached through a path is
  `p.C`.
- The class as a type member whose upper bound is its parents intersected with its own structure,
  `C = ct.B ∧ {this ⇒ ⟦C⟧}` (p.29), and with traits `C = ct.B ∧ ⋀⟨ct.D⟩ ∧ {this ⇒ ⟦C⟧}`
  (Figure 5.9, p.77).  Ours is `class K = μ(this. ⋀ᴸ decls(K)) ∧ ⋀ᴿ parents(K)`, declared
  `{K : ⊥..Body}`.
- The constructor as a method of the table, `new_C(f_param) : |C| = {this ⇒ (|C|)}` (p.29), and
  `|new C(e)| := ct.new_C(|e|)` (Figure 3.6, p.28).  Ours is the field `new$K`, whose body is the
  instance literal tagged with its class.
- Linearization and the implementer `mimpl` (pp.73-74).  Method overrides with equal parameters
  and covariant results (p.74).  `noAccidentalOverride` and `isValid` (Figure 5.8, p.75).
  Linearization is the reader's `Scope.lin`.  `mimpl` is in `Frontend/ScalaClasses.lean`, and so
  is `noAccidentalOverride`, as the check OV-Accidental.  The override condition of `isValid` is
  the witnesses `ov`, `ovp` and `ovv` that the mapping writes and the typer checks.
- Type members: the instance takes the upper bound and the class type declares both bounds
  (Figure 7.12, p.114).  Overriding of type members by narrower bounds, and `isValid` for proper
  classes (Figure 7.10, p.107, explained on pp.107-108).  TT-Super and TT-AndLR (Figure 7.4,
  p.101) as the meet of upper bounds.
- Method bodies typed under `this : C` with the class's members abstract (DT-Method, Figure 7.11,
  p.108).  Ours types them in module functions under the receiver `this : z.K`.
- Algorithmic subtyping without transitivity through bounds (AS-Sel1, AS-Sel2 and the example of
  p.102).  Our typer rejects that example too (limitation L1 of the Frontend README, and the corpus
  file `neg/BoundsTransitivity`), and NOM-A is stated about the algorithmic judgment, as his
  Theorem 7.5.6 (p.111) relates the algorithmic judgment to the declarative one.
- And-Bind (p.49) is the rule LE-Pair of FCn.

What differs, and why.

- Where nominality lives.  His class is a tight alias in `ct`, so his target typing is structural
  and his source typing nominal.  He proves `{this ⇒ ⟦C⟧} <: |C|` by BindX and the alias's lower
  bound (Lemma 3.2.6, stated p.32, proved pp.32-33).  Ours declares the class with lower bound `⊥`
  in its own literal, seals only at constructors' instances, and proves NOM-A and NOM-B in Lean
  about the derivations the typer builds.
- The road of footnote 8 (p.14).  He kept subtyping preservation, `|Γ| ⊢ |S| <: |T|`, and declined
  to insert coercions, which would make the expression translation more complex.  Ours translates
  every source subtyping into FCn evidence (plan X), and the two class forms add two evidence
  equations, among them `⟦subtyp_seal⟧ = seal p C`.
- The target.  His is oopslaDOT with BindX and Bind1 (p.11, p.14), And-Bind (p.49, Theorem 4.3.1)
  and And-I' (pp.78-80, Theorem 5.5.5).  Ours is FCn, which has LE-Pair for And-Bind and PA-Both
  for And-I on paths, and has neither a BindX step under the self nor And-I' for terms.  So an
  intersection receiver with a common method is ours-stricter (`disagree/AndCall`), and And-Fun was
  out of reach for him too (p.76, p.124).
- Paths and inner classes.  His Dependent Scala has variables as prefixes (Figure 7.1, p.97), and
  he asks for pDOT rebased on oopslaDOT for inner classes (p.121).  Ours has classes in objects
  reached through any path, and `val` aliases of them.  Classes inside classes (FJI) stay out of
  this version.
- Getters (Figure 3.7, p.29).  Not used: a `val` parameter is a path field, so `c.p.T` is a
  path-dependent type (`pos/ValParamPrefix`).
- Type parameters (chapters 4 and 5).  Out of this version.  The `ct.C` indirection that keeps
  F-bounded hierarchies finite (TR-ClassAlt does not terminate on `class C ◁ B[C]`, p.50) is our
  class name, and the BindX step it costs (p.49) needs a rule in our target, the later stage NP.
- Mechanization.  His translation proofs are on paper (p.124).  Ours are Lean theorems with axioms
  at most `propext` and `Quot.sound`.
- Local classes (p.122), wildcards and capture (p.123), pattern matching (p.123): out of this
  version.  Pattern matching needs a notion of constructor event defined independently of
  `allocLbl` membership.  The records of NR track permitted seal sites, not executed constructors.
