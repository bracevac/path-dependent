import Lean
import Coercions.ScalaSyntax.Read
import Coercions.Frontend.Scala

/-!
# The commands that read Scala files

The only module of the front end with meta code.  Two commands read `.scala`
files at elaboration (plan IX, S-1), with paths relative to the package root
(S-4), and state what the library makes of them as kernel theorems.

`scala_example X from "path"` reads one file.  A file the reader refuses is an
error at the path, written `path:line:col: message` (S-6).  Otherwise the
command adds, under the current namespace, `X.chars`, the characters of the
file as constructor terms, `X.prog` and `X.table`, the surface term and the
label table that `readProgram` computes, and the theorem

`X.read : (readVanilla X.chars).toOption = some (X.prog, X.table)`

by `decide +kernel` (S-2).  So the term is what the library's own reader makes
of those characters, checked in the kernel.

`scala_corpus x "dir"` judges a corpus (S-23).  It reads the files of the
folders `pos`, `neg`, `disagree` and `outside` of `dir`, in this order.  A
missing folder counts as empty.  A file `S.scala` gets in namespace
`ScalaCorpus.X.folder.S` what `scala_example` adds, only `chars` when the
reader refuses it, then the theorem `verdict : (outcome chars).kind = k` by
`decide +kernel`.  The folder and the header `// ours: k` fix `k`.  A header `// same as: N` adds the
theorem `same`: the file and the example `N` resolve to the same partial term
at `exampleTable`, and that term exists (S-24).  The command runs `readProgram`
and `outcome` before it adds anything for a file.  A file whose headers or
outcome do not match is an error at the command and gets no declaration.

The values reach the environment by `ToExpr`.  The derived instance for the
mutual `STm` and `SDefs` is `partial`, so those two are written here, each
structural.  A declaration built here names its field `«type»`, since
`Notation` makes `type` a keyword in every module of the front end.
-/

namespace Frontend.Scala

open Lean Elab Command

/-! ## Values as expressions -/

deriving instance ToExpr for SType
deriving instance ToExpr for FCdot.Label

mutual
/-- The expression that builds a surface term. -/
def stmExpr (e : STm) : Expr :=
  match e with
  | .var x => mkApp (mkConst ``STm.var) (toExpr x)
  | .lam x T t => mkApp3 (mkConst ``STm.lam) (toExpr x) (toExpr T) (stmExpr t)
  | .obj x T d => mkApp3 (mkConst ``STm.obj) (toExpr x) (toExpr T) (sdefsExpr d)
  | .app t u => mkApp2 (mkConst ``STm.app) (stmExpr t) (stmExpr u)
  | .proj t a => mkApp2 (mkConst ``STm.proj) (stmExpr t) (toExpr a)
  | .«let» x T t u => mkApp4 (mkConst ``STm.«let») (toExpr x) (toExpr T) (stmExpr t) (stmExpr u)
  | .asc t T => mkApp2 (mkConst ``STm.asc) (stmExpr t) (toExpr T)
termination_by structural e

/-- The expression that builds surface definitions. -/
def sdefsExpr (d : SDefs) : Expr :=
  match d with
  | .typ A T => mkApp2 (mkConst ``SDefs.typ) (toExpr A) (toExpr T)
  | .trm a T t => mkApp3 (mkConst ``SDefs.trm) (toExpr a) (toExpr T) (stmExpr t)
  | .and d e => mkApp2 (mkConst ``SDefs.and) (sdefsExpr d) (sdefsExpr e)
termination_by structural d
end

instance : ToExpr STm := ⟨stmExpr, mkConst ``STm⟩
instance : ToExpr SDefs := ⟨sdefsExpr, mkConst ``SDefs⟩

/-! ## Kinds as words -/

/-- A kind as a header writes it. -/
def Kind.word : Kind → String
  | .ok => "ok"
  | .rejected => "rejected"
  | .unknown => "unknown"
  | .limit => "limit"
  | .outside => "outside"

/-- The kind a header word names. -/
def Kind.ofWord? (w : String) : Option Kind :=
  [Kind.ok, .rejected, .unknown, .limit, .outside].find? fun k => k.word == w

/-- The constructor of a kind, for a theorem's statement. -/
def Kind.ctor : Kind → Name
  | .ok => ``Kind.ok
  | .rejected => ``Kind.rejected
  | .unknown => ``Kind.unknown
  | .limit => ``Kind.limit
  | .outside => ``Kind.outside

/-! ## Reading a file -/

/-- Add the definition `n : ty := value`. -/
def addValue (n : Name) (ty value : Expr) : CommandElabM Unit :=
  liftCoreM <| addAndCompile <| .defnDecl {
    name := n, levelParams := [], «type» := ty, value := value,
    hints := .abbrev, safety := .safe }

/-- Add the theorem `n : prop` by `decide +kernel`.  The name is absolute, so
the current namespace does not prefix it a second time. -/
def addKernelThm (n : Name) (prop : Term) : CommandElabM Unit := do
  let thm := mkIdent (`_root_ ++ n)
  elabCommand (← `(theorem $thm : $prop := by decide +kernel))

/-- Add `prog` and `table` under `ns`, and the theorem `read` that the
characters `ns.chars` read to them (S-2). -/
def addProgram (ns : Name) (e : STm) (Λ : LabelTable) : CommandElabM Unit := do
  addValue (ns ++ `prog) (mkConst ``STm) (toExpr e)
  addValue (ns ++ `table) (mkConst ``LabelTable) (toExpr Λ)
  let chars := mkCIdent (ns ++ `chars)
  let prog := mkCIdent (ns ++ `prog)
  let table := mkCIdent (ns ++ `table)
  addKernelThm (ns ++ `read) (← `((readVanilla $chars).toOption = some ($prog, $table)))

/-! ## `scala_example` -/

/-- `scala_example X from "path"` reads the file at `path`, relative to the
package root.  It adds `X.chars`, `X.prog`, `X.table` and the theorem
`X.read`, or reports the refusal of the reader at the path. -/
syntax (name := scalaExample) "scala_example " ident " from " str : command

@[command_elab scalaExample, inherit_doc scalaExample]
def elabScalaExample : CommandElab
  | `(scala_example $x:ident from $p:str) => do
    let rel := p.getString
    let (_, cs) ← ScalaSyntax.readScala p rel
    match readProgram cs with
    | .error err => ScalaSyntax.reportErr p rel err
    | .ok (_, e, Λ) =>
      let ns := (← getCurrNamespace) ++ x.getId
      ScalaSyntax.spliceChars (ns ++ `chars) cs
      addProgram ns e Λ
  | _ => throwUnsupportedSyntax

/-! ## `scala_corpus` -/

/-- The folders of a corpus, in the order the command reads them. -/
def corpusFolders : List String := ["pos", "neg", "disagree", "outside"]

/-- The rest of the first line of `text` that starts with `key`, trimmed. -/
def header (text key : String) : Option String :=
  (text.splitOn "\n").findSome? fun l =>
    if l.startsWith key then some (l.drop key.length).trimAscii.toString else none

/-- The kind a file of `folder` must have, from the header `// ours:`, or the
fault of the header.  `pos` wants `ok` and `outside` wants `outside`.  `neg`
and `disagree` need the header, `neg` one of `rejected`, `unknown`, `limit`. -/
def expectedKind (path folder : String) : Option String → Except String Kind
  | none =>
    if folder == "pos" then .ok .ok
    else if folder == "outside" then .ok .outside
    else .error s!"{path}: a file in {folder}/ needs a `// ours:` header"
  | some w =>
    match Kind.ofWord? w with
    | none => .error s!"{path}: `// ours: {w}` names no outcome"
    | some k =>
      let fits :=
        if folder == "pos" then k == .ok
        else if folder == "outside" then k == .outside
        else if folder == "neg" then k == .rejected || k == .unknown || k == .limit
        else true
      if fits then .ok k
      else .error s!"{path}: `// ours: {w}` contradicts the folder {folder}/"

/-- Check the headers of the file `path` in `folder`, and compare its outcome
with the kind they fix.  The answer is that kind and the example a `// same
as:` header names, or the first fault. -/
def judgeFile (env : Environment) (path folder : String) (cs : List Char) :
    Except String (Kind × Option Name) := do
  let text := String.ofList cs
  let k ← expectedKind path folder (header text "// ours: ")
  let same ← match header text "// same as: " with
    | none => pure none
    | some n =>
      let c := n.toName
      if env.contains c then pure (some c)
      else throw s!"{path}: `// same as: {n}` names no constant"
  if same.isSome && (readProgram cs).toOption.isNone then
    throw s!"{path}: `// same as:` needs a file that the reader takes"
  let o := outcome cs
  unless o.kind == k do
    throw s!"{path}: expected {k.word}, ours is {o.text}"
  pure (k, same)

/-- `scala_corpus x "dir"` judges the files of the folders `pos`, `neg`,
`disagree` and `outside` of `dir`, relative to the package root.  A file
`S.scala` gets `chars`, then `prog`, `table` and `read` when the reader takes
it, then `verdict`, and `same` with a `// same as:` header, in namespace
`ScalaCorpus.X.folder.S`, where `X` is `x` with its first letter upper case. -/
syntax (name := scalaCorpus) "scala_corpus " ident str : command

@[command_elab scalaCorpus, inherit_doc scalaCorpus]
def elabScalaCorpus : CommandElab
  | `(scala_corpus $x:ident $d:str) => do
    let dir := d.getString
    let root ← ScalaSyntax.packageRoot d
    unless ← (root / dir).isDir do
      throwErrorAt d "{root / dir}: no such folder"
    let base := `ScalaCorpus ++ x.getId.eraseMacroScopes.capitalize
    for folder in corpusFolders do
      unless ← (root / dir / folder).isDir do continue
      for file in ← ScalaSyntax.listScala (dir ++ "/" ++ folder) do
        let stem := Name.mkSimple (file.fileStem.getD "")
        let path := dir ++ "/" ++ folder ++ "/" ++ file.fileName.getD ""
        let (_, cs) ← ScalaSyntax.readScala d path
        match judgeFile (← getEnv) path folder cs with
        | .error msg => logError msg
        | .ok (k, same) =>
          let ns := base ++ .mkSimple folder ++ stem
          ScalaSyntax.spliceChars (ns ++ `chars) cs
          if let .ok (_, e, Λ) := readProgram cs then
            addProgram ns e Λ
          let chars := mkCIdent (ns ++ `chars)
          addKernelThm (ns ++ `verdict) (← `((outcome $chars).kind = $(mkCIdent k.ctor)))
          if let some c := same then
            let prog := mkCIdent (ns ++ `prog)
            let ex := mkCIdent c
            let tbl := mkCIdent ``exampleTable
            addKernelThm (ns ++ `same) (← `(resolveP $tbl $prog = resolveP $tbl $ex ∧
              (resolveP $tbl $ex).isSome = true))
  | _ => throwUnsupportedSyntax

end Frontend.Scala
