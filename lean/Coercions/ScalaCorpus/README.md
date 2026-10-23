# ScalaCorpus

One corpus module per Scala-syntax front end. Each judges the files of
`scala/<x>/` in the kernel at build time, by the front end's `outcome` on the
characters of each file. A file whose outcome differs from what its folder and
its headers say fails the build.

## Modules

| module | contents |
|---|---|
| `Vanilla` | the 169 files of `scala/vanilla/` by `scala_corpus`, the congruence lemmas and the template theorems |

## Main theorems

- `ScalaCorpus.Vanilla.<folder>.<Stem>.read`, for each of the 116 files the reader takes: `readVanilla` makes the term `prog` and the label table `table` of the file's characters `chars`.
- `ScalaCorpus.Vanilla.<folder>.<Stem>.verdict`, for each of the 169 files: the kind of `outcome chars` is the one that the folder and the `// ours:` header fix.
- `ScalaCorpus.Vanilla.<folder>.<Stem>.same`, for each of the 77 files with a `// same as:` header: the file and the example it names resolve to the same partial term at `exampleTable`, and that term exists.
- `compileE_congr`, `compile_congr`: two terms with one resolution compile alike, so a `same` theorem moves a fact about an example to its file.
- `E1_rejected`: E1 written as Scala does not compile at any budget.
- `E10t_compiles`, `E10t_checks`: E10t written as Scala compiles, and the target checker accepts its translation.
- `P5_alpha`: P5 written as Scala is another term than `P5src`, with the same resolution.
- `#assert_axioms ScalaCorpus.Vanilla` ends the module. It fails when a theorem of the namespace depends on an axiom other than `propext` and `Quot.sound`.

## Building

`lake build ScalaCorpusVanilla`, which is not a default target and takes about
a minute. Lake rebuilds the module when a `.scala` file under `scala/vanilla/`
changes, since the library needs the input directory `scala-vanilla` of
`lakefile.toml`.
