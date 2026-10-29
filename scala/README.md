# Scala programs

This folder holds Scala programs that two judges read.  scalac 3.8.4 compiles each file with its default
flags, and a front end of `lean/Coercions/` reads the same bytes in Lean.  The claim: every corpus file that
our front end accepts, scalac 3.8.4 accepts too, apart from the files of `disagree/`, each with its cause.
It is tested on these files and not proved, it holds for the pinned compiler only, and it compares verdicts,
not types.  The pair of our outcome and scalac's verdict gives each file a class (plan IX, S-21): agree-accept,
agree-reject, ours-stricter, ours-looser, refuse-differently, agree-giveup, broken, or outside when our front
end refuses the file as outside its subset.  The claim is that no file but those of `disagree/` is ours-looser.

**`vanilla/`** is the corpus of the vanilla front end, `lean/Coercions/Frontend/`.  It holds 169 files, 74
in `pos/`, 31 in `neg/`, 10 in `disagree/` and 54 in `outside/`.  Each file starts with
`import scala.reflect.Selectable.reflectiveSelectable`, then the headers of its folder, then `object <Stem> {`,
where the stem is the file name without `.scala`.  The module `Coercions.ScalaCorpus.Vanilla` judges every
file in the kernel when it builds, see [ScalaCorpus](../lean/Coercions/ScalaCorpus/README.md).
[`vanilla/TABLE.md`](vanilla/TABLE.md) is what the harness wrote on its last run, one row per file with
scalac's verdict and warnings, our outcome and its type in Scala, the class, the cause or rule, the fill and
the round trip.  Nobody edits the table by hand.  The six ours-looser files are all in `disagree/`.

**`pdot/`** is the corpus of the pDOT Scala front end, `lean/Coercions/PDot/Frontend/` (plan XI).  It holds 78
files, 33 in `pos/`, 15 in `neg/`, 8 in `disagree/` and 22 in `outside/`, with the headers and markers of the
vanilla corpus.  Its center is the module idioms that pDOT is for: nested objects, `val` aliases of module paths,
parameters at `x.type`, and paths of length two in types.  The module `Coercions.ScalaCorpus.PDot` judges every
file in the kernel when `lake build ScalaCorpusPDot` builds it.  The harness runs as `lake env lean --run
scripts/scala/Agree.lean pdot scala/pdot`, after `lake build Frontend PDotFrontend PDotScala`, and writes
[`pdot/TABLE.md`](pdot/TABLE.md).  33 files are agree-accept, 15 agree-reject and 22 outside.  The other eight are
the files of `disagree/`.  Three are ours-looser.  In DepCo scalac compares the domains of dependent function
types by equality and pDOT compares them contravariantly.  In Mid scalac checks an argument against one function
type of an intersection and DOT against the other.  In X3 scalac types a closure at the function part of its
expected type and DOT at the lower bound of `y.A`.  Five are ours-stricter.  pDOT has no rule `x : x.type` in
SnglRefl, ReflSngl and TS (N4), its subtyping widens no singleton in SnglInFn, and its elaborator widens an
inferred `this` result in DefThisInfer.  The fills hold less well than in the vanilla corpus.  The fill printer
drops every written self type, so a lambda field prints with no declared type (F-L).  It prints a `let` that the
elaborator inserted as a `val` with no written type, which scalac widens (F-W).  Of the 32 fills, 25 are
agree-accept.  scalac compiles the fills of Chain, E3m, E5m, E5Obj and R7Direct, which our side rejects, and
rejects the fills of Recursion and UnstableSngl.  The row of each of these seven names its cause.  ReplPrefix has
no fill, since its printed fill has the shape on which scalac crashes (R-K).  All 57 files that the reader takes
read back the same.  Of the 28 example programs, PQ reads back the same, 25 have no Scala form, and R2 and E11
read back to another term, for the cause that the table gives.

**`pos/`** holds the files that both judges accept.  Its one header is `// same as: <example>`, which names
an example program of the front end and makes the kernel prove that file and example resolve to the same
term, or `// from: <origin>`, which says where the file comes from.

**`neg/`** holds the files that scalac rejects and our front end does not accept.  Its headers are
`// ours:` with our kind, `rejected`, `unknown` or `limit`, then `// same as:` or `// from:`.  A neg file has
one fault, so that one error cannot hide another.

**`disagree/`** holds the files where the two verdicts differ, the exceptions the claim lists.  Its headers
are `// ours:`, `// scalac:` with `ok` or `error`, `// cause:` with one line on why the two differ, then
`// same as:` or `// from:`.

**`outside/`** holds the files that our front end refuses, by a rule of the reader or by the member check.
Its headers are `// scalac:`, `// rule:` with the rule that refuses the file, and `// from:`.

A line where scalac reports an error ends with `// error`, and a line where it reports a warning ends with
`// warn`, once per diagnostic, as in the tests of the Scala 3 compiler.  In every folder the markers must
equal scalac's diagnostics as multisets of lines and kinds.

To add a file, write it in the folder that its two verdicts name, with the headers of that folder and no
markers, and run the harness.  Its `FAIL` line names the lines where scalac reports, and the markers go there.
Then `lake build ScalaCorpusVanilla` gives the kernel's verdict.  A header that contradicts our outcome fails
the build with an error that names the file.  Run the harness again until it prints `0 failures`, and commit
the table it wrote with the file.

The harness [`scripts/scala/Agree.lean`](../scripts/scala/Agree.lean) runs from the repository root, after
`lake build Frontend PDotFrontend PDotScala`, as `lake env lean --run scripts/scala/Agree.lean vanilla scala/vanilla`.
It needs scalac 3.8.4 on the `PATH` and fails on another version.  It runs our front end on every file.  scalac
compiles the pos files and the fills our front end accepts in one run, and every other file alone, four at a
time, with a deadline of 120 s per run.  It checks the headers, the markers, the claim, the fills (F, the
programs with every inferred annotation written) and the round trips (R, each file printed as Scala and read
back), and writes `TABLE.md` into the corpus.  Each failed check prints one line `FAIL <subject>: <what>`.
The exit code is 0 when every check holds, 1 when one fails, and 2 on a usage fault.  `--raw <dir>` saves
every output of scalac, and `--timeout <ms>` replaces the deadline.  CI runs the same command in the
`frontends` job of [`lean.yml`](../.github/workflows/lean.yml) and fails when the table differs from the
committed one.
