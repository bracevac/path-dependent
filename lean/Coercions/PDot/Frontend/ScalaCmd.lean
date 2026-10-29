import Lean
import Coercions.ScalaSyntax.Read
import Coercions.PDot.Frontend.ScalaTests

/-!
# The commands that read pDOT Scala files

The only module of the pDOT Scala front end with meta code.  Two commands read `.scala` files at
elaboration, with paths relative to the package root, and state what the library makes of them as
kernel theorems (plan XI, "Commands and the corpus module", after `Frontend/ScalaCmd.lean`).

`pdot_scala_example X from "path"` reads one file.  A file the reader refuses is an error at the path,
written `path:line:col: message`.  Otherwise the command adds, under the current namespace, `X.chars`,
`X.prog`, `X.table`, `X.modules` and the theorem
`X.read : (readPDot X.chars).toOption = some (X.prog, X.table, X.modules)` by `decide +kernel`.

`pdot_scala_corpus x "dir"` judges the folders `pos`, `neg`, `disagree` and `outside` of `dir`, in this
order, a missing folder counting as empty.  A file `F.scala` gets in namespace
`ScalaCorpus.X.folder.F` what `pdot_scala_example` adds, only `chars` when the reader refuses it, then
`verdict : (outcome chars).kind = k` by `decide +kernel`, the kind its folder and `// ours:` header fix.
A header `// same as: E` adds `same : resolveP table prog = resolveP table E ∧
(resolveP table E).isSome = true`.  A file whose headers or outcome do not match is an error at the
command and gets no declaration.

`ToExpr` for `STm` and `SDefs` is written here, structural, since the derived instance of a mutual type
is `partial`.  The module ends with the library's no-well-founded check.
-/

namespace PDotFrontend.Scala

open Lean Elab Command

/-! ## Values as expressions -/

deriving instance ToExpr for SPath
deriving instance ToExpr for SType
deriving instance ToExpr for SBind
deriving instance ToExpr for Paths.FCdot.Label

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
  | .alias x p u => mkApp3 (mkConst ``STm.alias) (toExpr x) (toExpr p) (stmExpr u)
  | .bind k x t u => mkApp4 (mkConst ``STm.bind) (toExpr k) (toExpr x) (stmExpr t) (stmExpr u)
termination_by structural e
/-- The expression that builds surface definitions. -/
def sdefsExpr (d : SDefs) : Expr :=
  match d with
  | .nil => mkConst ``SDefs.nil
  | .typ ds A T => mkApp3 (mkConst ``SDefs.typ) (sdefsExpr ds) (toExpr A) (toExpr T)
  | .trm ds a T t => mkApp4 (mkConst ``SDefs.trm) (sdefsExpr ds) (toExpr a) (toExpr T) (stmExpr t)
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

/-- Add the theorem `n : prop` by `decide +kernel`.  The name is absolute, so the current namespace
does not prefix it a second time. -/
def addKernelThm (n : Name) (prop : Term) : CommandElabM Unit := do
  let thm := mkIdent (`_root_ ++ n)
  elabCommand (← `(theorem $thm : $prop := by decide +kernel))

/-- Add `prog`, `table` and `modules` under `ns`, and the theorem `read`. -/
def addProgram (ns : Name) (e : STm) (Λ : LabelTable) (ms : List (List Paths.FCdot.Label)) : CommandElabM Unit := do
  addValue (ns ++ `prog) (mkConst ``STm) (toExpr e)
  addValue (ns ++ `table) (mkConst ``LabelTable) (toExpr Λ)
  addValue (ns ++ `modules) (toTypeExpr (List (List Paths.FCdot.Label))) (toExpr ms)
  let chars := mkCIdent (ns ++ `chars)
  let prog := mkCIdent (ns ++ `prog)
  let table := mkCIdent (ns ++ `table)
  let modules := mkCIdent (ns ++ `modules)
  addKernelThm (ns ++ `read) (← `((readPDot $chars).toOption = some ($prog, $table, $modules)))

/-! ## `pdot_scala_example` -/

/-- `pdot_scala_example X from "path"` reads the file at `path`, relative to the package root, and adds
`X.chars`, `X.prog`, `X.table`, `X.modules` and the theorem `X.read`, or reports the refusal at the path. -/
syntax (name := pdotScalaExample) "pdot_scala_example " ident " from " str : command

@[command_elab pdotScalaExample, inherit_doc pdotScalaExample]
def elabPDotScalaExample : CommandElab
  | `(pdot_scala_example $x:ident from $p:str) => do
    let rel := p.getString
    let (_, cs) ← ScalaSyntax.readScala p rel
    match readPDot cs with
    | .error err => ScalaSyntax.reportErr p rel err
    | .ok (e, Λ, ms) =>
      let ns := (← getCurrNamespace) ++ x.getId
      ScalaSyntax.spliceChars (ns ++ `chars) cs
      addProgram ns e Λ ms
  | _ => throwUnsupportedSyntax

/-! ## `pdot_scala_corpus` -/

/-- The folders of a corpus, in the order the command reads them. -/
def corpusFolders : List String := ["pos", "neg", "disagree", "outside"]

/-- The rest of the first line of `text` that starts with `key`, trimmed. -/
def header (text key : String) : Option String :=
  (text.splitOn "\n").findSome? fun l =>
    if l.startsWith key then some (l.drop key.length).trimAscii.toString else none

/-- The kind a file of `folder` must have, from the header `// ours:`, or the fault of the header.
`pos` wants `ok` and `outside` wants `outside`.  `neg` and `disagree` need the header, `neg` one of
`rejected`, `unknown`, `limit`. -/
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

/-- Check the headers of the file `path` in `folder`, and compare its outcome with the kind they fix.
The answer is that kind and the example a `// same as:` header names, or the first fault. -/
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
  if same.isSome && (readPDot cs).toOption.isNone then
    throw s!"{path}: `// same as:` needs a file that the reader takes"
  let o := outcome cs
  unless o.kind == k do
    throw s!"{path}: expected {k.word}, ours is {o.text}"
  pure (k, same)

/-- `pdot_scala_corpus x "dir"` judges the files of the folders `pos`, `neg`, `disagree` and `outside` of
`dir` in namespace `ScalaCorpus.X.folder.F`, `X` being `x` with its first letter upper case. -/
syntax (name := pdotScalaCorpus) "pdot_scala_corpus " ident str : command

@[command_elab pdotScalaCorpus, inherit_doc pdotScalaCorpus]
def elabPDotScalaCorpus : CommandElab
  | `(pdot_scala_corpus $x:ident $d:str) => do
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
          if let .ok (e, Λ, ms) := readPDot cs then
            addProgram ns e Λ ms
          let chars := mkCIdent (ns ++ `chars)
          addKernelThm (ns ++ `verdict) (← `((outcome $chars).kind = $(mkCIdent k.ctor)))
          if let some c := same then
            let prog := mkCIdent (ns ++ `prog)
            let tbl := mkCIdent (ns ++ `table)
            let ex := mkCIdent c
            addKernelThm (ns ++ `same) (← `(resolveP $tbl $prog = resolveP $tbl $ex ∧
              (resolveP $tbl $ex).isSome = true))
  | _ => throwUnsupportedSyntax

end PDotFrontend.Scala

#assert_no_wf PDotFrontend.Scala
