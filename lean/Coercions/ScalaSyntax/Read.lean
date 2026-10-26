import Lean
import Coercions.ScalaSyntax.Lex

/-!
# The meta side of the Scala reader

The only module of the `ScalaSyntax` library that imports `Lean`, and the only
one that touches files.  A command of a front end reads a `.scala` file at
elaboration (plan IX, S-1) with the pieces below.  It finds the package root
(S-4), reads the file or lists a folder, reports a refusal of the reader at
its own syntax (S-6), and adds the characters of the file as constructor
terms, so that the kernel runs the structural reader on them (S-2).
`String.toList` runs here, in compiled code at elaboration, and the kernel
never sees it: it depends on `Classical.choice` in Lean v4.29.1.

Two commands check what is built.  `#assert_no_wf` is copied from
`Frontend/Surface.lean`.  `#assert_axioms` closes each corpus module (S-23),
as d3's sweep of its corpus did
(`notes-scala-frontends/scratch-d3/harness/CorpusDir.lean`).
-/

namespace ScalaSyntax

/-! ## `#assert_no_wf`

Every recursive definition of the reader is structural, so the kernel reduces
it.  This command fails the build when Lean compiles a definition by
well-founded recursion instead. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by
well-founded recursion.  Lean picks a combinator specialised to the measure,
such as `WellFounded.Nat.fix`, so the test is membership in the `WellFounded`
namespace. -/
elab "#assert_no_wf " ns:ident : command => do
  let env ← getEnv
  let bad := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if ns.getId.isPrefixOf n && d.value.getUsedConstants.any (`WellFounded).isPrefixOf then
        acc.push n
      else acc
    | _ => acc
  unless bad.isEmpty do throwError "well-founded definitions: {bad}"

section
open Lean Elab Command

/-! ## `#assert_axioms`

A theorem about the characters of a file holds in the kernel with at most
`propext` and `Quot.sound` (plan IX, constraint 3).  A `String` function that
the kernel would run brings in `Classical.choice`, and this command catches
it. -/

/-- Fails when a theorem under the namespace `ns` depends on an axiom other
than `propext` and `Quot.sound`, and names each such theorem with those
axioms.  A private theorem has a name outside `ns` and is not swept. -/
elab "#assert_axioms " ns:ident : command => do
  let env ← getEnv
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ => if ns.getId.isPrefixOf n then acc.push n else acc
    | _ => acc
  let mut bad : Array MessageData := #[]
  for n in thms do
    let other := (← liftCoreM (collectAxioms n)).filter fun a => a != ``propext && a != ``Quot.sound
    unless other.isEmpty do
      bad := bad.push m!"{n} depends on {other.toList}"
  unless bad.isEmpty do
    throwError "axioms beyond propext and Quot.sound:{indentD (MessageData.joinSep bad.toList Format.line)}"

/-! ## The package root -/

/-- The first directory from `dir` upwards that holds `lakefile.toml`, within
`n` steps. -/
def rootAbove : Nat → System.FilePath → IO (Option System.FilePath)
  | 0, _ => pure none
  | n + 1, dir => do
    if ← (dir / "lakefile.toml").pathExists then return some dir
    match dir.parent with
    | some p => rootAbove n p
    | none => return none

/-- The package root above the directory `start` (plan IX, S-4):
`IO.FS.realPath` of `start`, then up to the first directory that holds
`lakefile.toml`.  Without `realPath` a relative start such as `lean/Coercions`
has no parent above the working directory, and the walk stops short (refute-d3
F11). -/
def findRoot (start : System.FilePath) : IO System.FilePath := do
  let dir ← IO.FS.realPath start
  match ← rootAbove (dir.components.length + 1) dir with
  | some root => return root
  | none => throw (IO.userError s!"no lakefile.toml in {dir} or above it")

/-- The package root of the Lean file being elaborated, found from the file's
directory.  A failure is reported at `stx`. -/
def packageRoot (stx : Syntax) : CommandElabM System.FilePath := do
  let file : System.FilePath := ← getFileName
  let dir := match file.parent with
    | some d => if d.toString.isEmpty then "." else d
    | none => "."
  try findRoot dir
  catch e => throwErrorAt stx "{file}: {e.toMessageData}"

/-! ## Files -/

/-- The file named by `rel` relative to the package root, and its characters.
A missing or unreadable file is an error at `stx` that names the path. -/
def readScala (stx : Syntax) (rel : String) : CommandElabM (System.FilePath × List Char) := do
  let path := (← packageRoot stx) / rel
  unless ← path.pathExists do
    throwErrorAt stx "{path}: no such file"
  let text ← try IO.FS.readFile path
    catch e => throwErrorAt stx "{path}: {e.toMessageData}"
  return (path, text.toList)

/-- The `.scala` files of the folder named by `rel` relative to the package
root, sorted by name.  A missing folder is an error at the command. -/
def listScala (rel : String) : CommandElabM (List System.FilePath) := do
  let dir := (← packageRoot (← getRef)) / rel
  unless ← dir.isDir do
    throwError "{dir}: no such folder"
  let files ← (← dir.readDir).filterM fun e => do
    return e.path.extension == some "scala" && !(← e.path.isDir)
  return (files.qsort fun a b => a.fileName < b.fileName).toList.map (·.path)

/-- Report the refusal `e` of the reader in the file `path` at `stx`, as
`path:line:col: message` (plan IX, S-6). -/
def reportErr (stx : Syntax) (path : String) (e : Err) : CommandElabM α :=
  throwErrorAt stx "{path}:{e.pos.line}:{e.pos.col}: {e.msg}"

/-- Add `def n : List Char := [c₁, …, cₙ]`, the characters as constructor
terms, so that the kernel runs the reader on them without decoding a `String`
(plan IX, S-1, S-2). -/
def spliceChars (n : Name) (cs : List Char) : CommandElabM Unit :=
  liftCoreM <| addAndCompile <| .defnDecl {
    name := n, levelParams := [], type := mkApp (mkConst ``List [0]) (mkConst ``Char),
    value := toExpr cs, hints := .abbrev, safety := .safe }

end

end ScalaSyntax
