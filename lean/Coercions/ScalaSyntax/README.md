# ScalaSyntax

The reader that the Scala-syntax front ends share. It reads the characters of
a `.scala` file into a syntax tree, refuses a file with a position and a
reason, and prints a tree back to text. Every definition is structural, so the
kernel runs the reader on the bytes of a file.

## Modules

| module | contents |
|---|---|
| `Lex` | the lexer, with the position of every token and every refusal, and the column rule |
| `Ast` | the syntax tree, the union of the four subsets, and equality of types and declarations |
| `Parse` | the parser, a recursive descent on fuel from the tokens to the tree |
| `Scope` | the checks on the tree: names and scopes, cycles, literals under written types, the label table |
| `Print` | the printer from the tree back to text, in the layout of the column rule |
| `Read` | reading and listing files at elaboration, the characters of a file for the kernel, `#assert_no_wf` and `#assert_axioms` |
| `Tests` | the string checks, by `#eval expect` |

## Main theorems

- `Ty.beq_refl`, `Decls.beq_refl`: `Ty.beq` and `Decls.beq` call every type and every list of declarations equal to itself.
- `Ty.eq_of_beq`, `Decls.eq_of_beq`: types and declarations that they call equal are equal. With the two above they give `DecidableEq Ty` and `DecidableEq Decls`, written by hand since Lean v4.29.1 derives none for the nested `Option Ty` of `Decls.typ`.
- The theorems about the bytes of a file are in the corpus modules, see [../ScalaCorpus/](../ScalaCorpus/README.md).

## Building

`lake build ScalaSyntax`. It is not a default target, and
`lake build Frontend` builds it too. The root module ends with
`#assert_no_wf ScalaSyntax`, and there is no `sorry`, `axiom` or
`native_decide`.
