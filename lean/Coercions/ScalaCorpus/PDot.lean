import Coercions.PDot.Frontend.ScalaCmd

/-!
# The pDOT Scala corpus

The files under `scala/pdot/` are Scala programs of the pDOT subset (plan XI,
"The corpus, the harness, CI").  Each one is checked twice.  scalac compiles
it, and the command below judges it with the pDOT Scala front end in the
kernel.  The folder says how the two verdicts relate.

`pos/` holds the files that both accept.  Our outcome is `ok`.  `neg/` holds the
files that scalac refuses and the front end does not accept.  Its header
`// ours:` names our kind, `rejected`, `unknown` or `limit`.  `disagree/` holds
the files where the two verdicts differ.  Its headers `// ours:` and
`// scalac:` give both, and `// cause:` says why.  `outside/` holds the files
that the front end does not take.  The reader or the member check of R-M
refuses each one.  Its header `// rule:` names the rule, and `// scalac:` gives
the verdict of scalac.  In every folder a `// error` marker ends each line where
scalac reports an error, and a `// warn` marker each line where it warns.

Lean reads two headers.  `// ours:` fixes the expected kind in `neg/` and
`disagree/`.  `// same as:` names an example program of the front end.  No
file of the corpus has one yet.  The other headers are comments for readers
and for the harness `scripts/scala/Agree.lean`.

`pdot_scala_corpus` reads the files of the four folders in order.  For a file
`S.scala` in `folder` it adds, under `ScalaCorpus.PDot.folder.S`, the
characters `chars`.  When the reader takes the file it adds the term `prog`,
the label table `table`, the module paths `modules` and the theorem `read`
that the reader makes those three of `chars`.  Then it adds `verdict`, which
states the kind of `outcome chars`.  A `// same as:` header would add `same`:
the file and the example resolve to the same partial term at the file's
table, and that term exists.  Each theorem is checked by `decide +kernel`.  A
header that does not match the outcome is an error, and the build fails.

The `lakefile.toml` declares `scala/pdot` as an input directory of the
library `ScalaCorpusPDot`.  So Lake rebuilds this module when a `.scala` file
under it changes, and only this module.

`compileE` and `compile` read a term only through `resolveP`, so two terms
with one resolution compile alike.  A `same` theorem moves a fact about an
example to its file through these two lemmas.  `#assert_axioms` ends the
module.
-/

pdot_scala_corpus PDot "scala/pdot"

namespace ScalaCorpus.PDot

open PDotFrontend

/-- `compileE` reads a term only through `resolveP`, so two terms with one resolution compile alike. -/
theorem compileE_congr {b : Budget} {Λ : LabelTable} {e e' : STm}
    (h : resolveP Λ e = resolveP Λ e') : compileE b Λ e = compileE b Λ e' := by
  unfold compileE; rw [h]

/-- `compile` the same. -/
theorem compile_congr {b : Budget} {Λ : LabelTable} {e e' : STm}
    (h : resolveP Λ e = resolveP Λ e') : compile b Λ e = compile b Λ e' := by
  unfold compile; rw [compileE_congr h]

end ScalaCorpus.PDot

#assert_axioms ScalaCorpus.PDot
