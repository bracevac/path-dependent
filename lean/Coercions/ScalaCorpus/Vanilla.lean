import Coercions.Frontend

/-!
# The vanilla Scala corpus

The files under `scala/vanilla/` are Scala programs of the vanilla subset
(plan IX, S-23).  Each one is checked twice.  scalac compiles it, and the
command below judges it with the vanilla front end in the kernel.  The folder
says how the two verdicts relate.

`pos/` holds the files that both accept.  Our outcome is `ok`.  `neg/` holds the
files that scalac refuses and the front end does not accept.  Its header
`// ours:` names our kind, `rejected`, `unknown` or `limit`.  `disagree/` holds
the files where the two verdicts differ.  Its headers `// ours:` and
`// scalac:` give both, and `// cause:` says why.  `outside/` holds the files
that the front end does not take.  The reader or the member check of S-17
refuses each one.  Its header `// rule:` names the rule, and `// scalac:` gives
the verdict of scalac.  In every folder a `// error` marker ends each line where
scalac reports an error.

Lean reads two headers.  `// ours:` fixes the expected kind in `neg/` and
`disagree/`.  `// same as:` names an example program of the front end.  The
other headers are comments for readers and for the scripts of
`notes-scala-xv2/`.

`scala_corpus` reads the files of the four folders in order.  For a file
`S.scala` in `folder` it adds, under `ScalaCorpus.Vanilla.folder.S`, the
characters `chars`.  When the reader takes the file it adds the term `prog`,
the label table `table` and the theorem `read` that the reader makes that pair
of `chars`.  Then it adds `verdict`, which states the kind of `outcome chars`.
A `// same as:` header adds `same`: the file and the example resolve to the
same partial term at `exampleTable`, and that term exists (S-24).  Each theorem
is checked by `decide +kernel`.  A header that does not match the outcome is an
error, and the build fails.

The `lakefile.toml` declares `scala/vanilla` as an input directory of the
library `ScalaCorpusVanilla`.  So Lake rebuilds this module when a `.scala` file
under it changes, and only this module (S-3).

The template theorems carry facts about the examples over to their Scala texts.
`compileE` and `compile` read a term only through `resolveP`, so a `same`
theorem moves a fact across.  E1 written as Scala does not compile at any
budget.  E10t written as Scala compiles, and the target checker accepts its
translation.  P5 written as Scala is another term than `P5src` with the same
resolution.  `#assert_axioms` ends the module.
-/

scala_corpus vanilla "scala/vanilla"

namespace ScalaCorpus.Vanilla

open Frontend

/-- `compileE` reads a term only through `resolveP`, so two terms with one resolution compile alike. -/
theorem compileE_congr {b : Budget} {Λ : LabelTable} {e e' : STm}
    (h : resolveP Λ e = resolveP Λ e') : compileE b Λ e = compileE b Λ e' := by
  unfold compileE; rw [h]

/-- `compile` the same. -/
theorem compile_congr {b : Budget} {Λ : LabelTable} {e e' : STm}
    (h : resolveP Λ e = resolveP Λ e') : compile b Λ e = compile b Λ e' := by
  unfold compile; rw [compileE_congr h]

/-- E1 written as Scala does not compile at any budget, as `Frontend.E1_rejected` says of E1. -/
theorem E1_rejected (b : Budget) : compile b exampleTable neg.E1.prog = none := by
  rw [compile_congr neg.E1.same.1]; exact Frontend.E1_rejected b

/-- E10t written as Scala compiles. -/
theorem E10t_compiles : (compile {} exampleTable pos.E10t.prog).isSome = true := by
  rw [compile_congr pos.E10t.same.1]; exact Frontend.E10t_compiles

/-- The target checker accepts the translation of E10t written as Scala. -/
theorem E10t_checks : CheckerAccepts {} exampleTable pos.E10t.prog E10t_compiles :=
  compile_checks_get E10t_compiles

/-- P5 written as Scala is another term than `P5src`: an unused binder reads back as `_`.  Its resolution is
P5's. -/
theorem P5_alpha : pos.P5.prog ≠ P5src ∧
    resolveP exampleTable pos.P5.prog = resolveP exampleTable P5src :=
  ⟨by decide, pos.P5.same.1⟩

end ScalaCorpus.Vanilla

#assert_axioms ScalaCorpus.Vanilla
