import Coercions.Frontend

/-!
# The harness of the Scala front ends

This program judges a corpus of `.scala` files twice, by a front end and by
scalac, and writes what it finds to the corpus's `TABLE.md` (plan IX, S-25
and S-26).  It runs from the package root.

```
lake env lean --run scripts/scala/Agree.lean <front end> <corpus dir> [--raw <dir>] [--timeout <ms>]
```

The front end is one of `frontEnds`.  The corpus dir holds the folders `pos`,
`neg`, `disagree` and `outside`, and nothing else but `TABLE.md`.  A missing
folder counts as empty.  `--raw <dir>` writes every output of scalac, in the
form of XV2's saved outputs.  `--timeout <ms>` replaces the deadline of
120000 ms for the compile runs.  The exit code is 0 when every expectation
holds, 1 when one fails, and 2 on a usage fault.  The table is written in
both of the first two cases.

Our side runs the front end's `outcome` on the characters of each file.  For
a pos file that it types, it prints the fill, the compiled program with every
slot written, as the object `<Stem>Fill` in a temporary folder, and runs on
the fill's text again.  For a file the reader takes, it prints the program and
reads it back, the round trip (plan S-27).  The front end's example programs
take the same round trip.

scalac 3.8.4 runs with its default flags.  The pos files that our side reads
and the fills that our side accepts again compile in one run.  The run is
accepted when it exits 0 with no error header and a position on every header.
Otherwise each of them compiles alone, as every other file and fill does, four
at a time.  A run that passes its deadline is killed with SIGKILL, which
reaches the whole process group of the run.  The verdict of a file is `ok`
(exit 0, no error header naming it), `error` (exit 1, at least one),
`timeout`, or `crash` (anything else).

The pair of our kind and scalac's verdict gives the class of plan S-21:
agree-accept, ours-stricter, ours-looser, agree-reject, refuse-differently,
agree-giveup, broken, or outside when our side refuses the file as outside
the subset.  The claim is that no file outside `disagree/` is ours-looser.

The checks cover the entries of the corpus dir, the headers each folder
takes, the expectations of each folder, the markers (plan IX, S-22), the
claim, the end of each run and the version of scalac.  F applies the claim to
the fills: a fill is agree-accept, or it is ours-stricter, agree-reject or
refuse-differently and prints a written self type as an ascribed literal
(XV1 D-12).  R asks every file the reader takes to read back the same, and
every example program to read back the same or to have no Scala form for one
of the reasons of `gapReasons`.  Each failed check prints one line
`FAIL <subject>: <what>`.  They replace XV2's shell scripts `scalac-run.sh`,
`check-folders.sh` and `check-markers.sh`.
-/

open Frontend Frontend.Scala

namespace Agree

/-! ## Front ends -/

/-- What a front end makes of one file, as the harness reads it. -/
structure Ours where
  /-- `Kind.word` of the outcome. -/
  kind : String
  /-- `Outcome.text`. -/
  text : String
  /-- For `ok`, the type in Scala, or `no Scala form: <reason>`. -/
  scala : Option String
  /-- For `ok`: the fill's text named `<Stem>Fill`, or why there is none. -/
  fill : Option (Except String (List Char))
  /-- For a fill: `some "D-12"` when its strict printing fails with `gapSelfType`. -/
  fillCause : Option String
  /-- The round trip's answer and whether it is `same`, none when the reader refuses. -/
  trip : Option (String × Bool)
deriving Inhabited

/-- A front end the harness can judge a corpus with. -/
structure FrontEnd where
  name : String
  /-- The stem names the fill's object. -/
  ours : String → List Char → Ours
  /-- Name, round trip answer, and whether the answer is allowed. -/
  examples : List (String × String × Bool)

/-- A type of the vanilla front end in Scala, with the printer context of a fill. -/
def scalaType (Λ : LabelTable) (T : DotMNF.Ty []) : String :=
  let c : PCtx := { thisName := none, hidden := [], dep := false, body := false, fill := true }
  match tyToScala c (sTyOf Λ .nil T) with
  | .ok (T', _) => String.ofList (ScalaSyntax.Print.ty none T')
  | .error why => s!"no Scala form: {why}"

/-- The answer of a round trip as the table writes it. -/
def tripText : Trip → String
  | .same => "same"
  | .gap why => s!"gap: {why}"
  | .unreadable err => s!"unreadable {err.pos.line}:{err.pos.col}: {err.msg}"
  | .differs => "differs"
  | .unresolved => "unresolved"

/-- Whether a round trip is `same`. -/
def tripSame : Trip → Bool
  | .same => true
  | _ => false

/-- The vanilla front end.  The fill prints with `fillToScala`.  It has the
cause of D-12 when the strict printing `toScala` of the same term fails with
exactly `gapSelfType`.  A file's round trip uses the file's own table, an
example's the table of its names. -/
def vanilla : FrontEnd where
  name := "vanilla"
  ours stem cs :=
    let o := outcome cs
    let trip := match readVanilla cs with
      | .ok (e, Λ) =>
        let t := roundTrip Λ e
        some (tripText t, tripSame t)
      | .error _ => none
    match o with
    | .ok Λ a T =>
      let cause := match toScala (fillSTm Λ a) with
        | .error why => if why == gapSelfType then some "D-12" else none
        | .ok _ => none
      { kind := o.kind.word, text := o.text, scala := some (scalaType Λ T),
        fill := some ((fillToScala Λ a).map fun P => ScalaSyntax.print { P with name := stem ++ "Fill" }),
        fillCause := cause, trip }
    | _ => { kind := o.kind.word, text := o.text, scala := none, fill := none, fillCause := none, trip }
  examples := Frontend.Scala.Tests.examples.map fun (n, e) =>
    let t := roundTrip (labelsOfProgram e) e
    (n, tripText t, match t with | .same | .gap _ => true | _ => false)

/-- The front ends the command line names. -/
def frontEnds : List FrontEnd := [vanilla]

/-! ## The runner -/

/-- The end of one process: its exit code, none after the deadline, and its
standard output followed by its standard error. -/
structure Ran where
  exit : Option UInt32
  out : String

/-- Run `cmd args` with a deadline of `ms` milliseconds.  Two dedicated tasks
read the pipes to the end, and the loop polls `tryWait` every 50 ms.  At the
deadline the process group gets SIGKILL.  `kill` throws when the group is
already gone, and that throw is dropped.  A command that cannot start ends
with exit 127 and the error as its output. -/
partial def spawnRun (cmd : String) (args : Array String) (ms : Nat) : IO Ran := do
  let t0 ← IO.monoMsNow
  let child ← try
      IO.Process.spawn { cmd, args, stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
    catch e => return { exit := some 127, out := s!"{cmd}: {e}\n" }
  let out ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← IO.asTask child.stderr.readToEnd .dedicated
  let rec loop : IO (Option UInt32) := do
    match ← child.tryWait with
    | some c => return some c
    | none =>
      if (← IO.monoMsNow) - t0 ≥ ms then
        try child.kill catch _ => pure ()
        let _ ← child.wait
        return none
      IO.sleep 50
      loop
  let code ← loop
  let o ← IO.ofExcept out.get
  let e ← IO.ofExcept err.get
  return { exit := code, out := o ++ e }

/-- Run scalac on each argument list, at most four runs at a time.  A run
starts whenever fewer than four are running.  The answers keep the order of
the jobs. -/
partial def pool (jobs : Array (Array String)) (ms : Nat) : IO (Array Ran) := do
  let mut next := 0
  let mut running : Array (Nat × Task (Except IO.Error Ran)) := #[]
  let mut done : Array Ran := Array.replicate jobs.size { exit := none, out := "" }
  while next < jobs.size || !running.isEmpty do
    while next < jobs.size && running.size < 4 do
      let t ← IO.asTask (spawnRun "scalac" jobs[next]! ms) .dedicated
      running := running.push (next, t)
      next := next + 1
    let mut still := #[]
    for (i, t) in running do
      if ← IO.hasFinished t then
        done := done.set! i (← IO.ofExcept t.get)
      else
        still := still.push (i, t)
    running := still
    if !running.isEmpty then IO.sleep 50
  return done

/-! ## Diagnostic headers and verdicts -/

/-- A diagnostic header of scalac. -/
structure Diag where
  /-- An error, or else a warning. -/
  isErr : Bool
  /-- The text between `-- [` and `]`. -/
  code : Option String
  /-- The base name of the file, the line and the column. -/
  pos : Option (String × Nat × Nat)
  /-- The line as scalac wrote it. -/
  line : String
deriving Inhabited

/-- Whether `key` occurs in `l`. -/
def holds (l key : String) : Bool := (l.splitOn key).length > 1

/-- The base name of a path. -/
def baseName (p : String) : String := (p.splitOn "/").getLast!

/-- The position of a header, read from the right of the text after the last
`key`: trailing dashes and spaces dropped, then the last two fields at `:` are
the line and the column, and the fields before them the path. -/
def posOf (l key : String) : Option (String × Nat × Nat) :=
  let rest := (l.splitOn key).getLast!
  let rest := String.ofList (rest.toList.reverse.dropWhile (fun c => c == '-' || c == ' ')).reverse
  let parts := rest.splitOn ":"
  let n := parts.length
  if n < 3 then none
  else
    match (parts[n - 2]!).toNat?, (parts[n - 1]!).toNat? with
    | some ln, some col => some (baseName (":".intercalate (parts.take (n - 2))), ln, col)
    | _, _ => none

/-- A line that starts with `-- ` and holds `Error: `, or else `Warning: `. -/
def diagOf (l : String) : Option Diag :=
  if !l.startsWith "-- " then none
  else
    let key? := if holds l "Error: " then some (true, "Error: ")
      else if holds l "Warning: " then some (false, "Warning: ") else none
    match key? with
    | none => none
    | some (isErr, key) =>
      let code := if l.startsWith "-- [" then
          some (String.ofList ((l.toList.drop 4).takeWhile (· != ']')))
        else none
      some { isErr, code, pos := posOf l key, line := l }

/-- The headers of an output. -/
def diagsOf (out : String) : List Diag := (out.splitOn "\n").filterMap diagOf

/-- Whether a header names the file `name`. -/
def names (name : String) (d : Diag) : Bool :=
  match d.pos with
  | some (b, _, _) => b == name
  | none => false

/-- scalac's verdict on one file. -/
inductive Verdict where
  | ok
  | error
  | timeout
  | crash (n : UInt32)
deriving Inhabited

/-- What scalac said about one file. -/
structure Seen where
  verdict : Verdict
  /-- The headers with a position that name the file. -/
  diags : List Diag
  /-- The headers of a run alone that have no position. -/
  noPos : List String
  /-- The output that `--raw` writes for the file. -/
  raw : String
deriving Inhabited

/-- `[exit <n>]` after an output, with `124` for a timeout as `timeout(1)` writes it. -/
def exitLine (r : Ran) : String :=
  let body := if r.out.isEmpty || r.out.endsWith "\n" then r.out else r.out ++ "\n"
  body ++ s!"[exit {r.exit.getD 124}]\n"

/-- The verdict of the file `name` run alone. -/
def seenAlone (name : String) (r : Ran) : Seen :=
  let ds := diagsOf r.out
  let mine := ds.filter (names name)
  let errs := (mine.filter (·.isErr)).length
  let v := match r.exit with
    | none => .timeout
    | some 0 => if errs == 0 then .ok else .crash 0
    | some 1 => if errs ≥ 1 then .error else .crash 1
    | some n => .crash n
  { verdict := v, diags := mine, noPos := (ds.filter (·.pos.isNone)).map (·.line), raw := exitLine r }

/-- The verdict of the file `name` in an accepted batch. -/
def seenBatch (name : String) (r : Ran) : Seen :=
  let mine := (diagsOf r.out).filter (names name)
  { verdict := .ok, diags := mine, noPos := [],
    raw := String.join (mine.map (·.line ++ "\n")) ++ "[exit 0]\n" }

/-- Whether a batch run is accepted: exit 0, no error header, and a position on every header. -/
def batchAccepted (r : Ran) : Bool :=
  let ds := diagsOf r.out
  r.exit == some 0 && !ds.any (·.isErr) && ds.all (·.pos.isSome)

/-- The line of a header, `0` without a position. -/
def Diag.lineNo (d : Diag) : Nat := match d.pos with | some (_, l, _) => l | none => 0

/-- The column of a header, `0` without a position. -/
def Diag.col (d : Diag) : Nat := match d.pos with | some (_, _, c) => c | none => 0

/-- The code of a header as a cell writes it. -/
def Diag.codeText (d : Diag) : String := d.code.getD "no code"

/-- Headers sorted by line, then column, then code, written `<code> at <line>` and joined by `, `. -/
def diagList (ds : List Diag) : String :=
  let lt (a b : Diag) : Bool :=
    a.lineNo < b.lineNo || (a.lineNo == b.lineNo &&
      (a.col < b.col || (a.col == b.col && a.codeText < b.codeText)))
  ", ".intercalate ((ds.toArray.qsort lt).toList.map fun d => s!"{d.codeText} at {d.lineNo}")

/-- The `scalac` cell. -/
def scalacCell (s : Seen) : String :=
  match s.verdict with
  | .ok => "ok"
  | .error => "error: " ++ diagList (s.diags.filter (·.isErr))
  | .timeout => "timeout"
  | .crash n => s!"crash: exit {n}"

/-- The `warnings` cell. -/
def warningsCell (s : Seen) : String := diagList (s.diags.filter (!·.isErr))

/-- The verdict as a header word. -/
def Verdict.word : Verdict → String
  | .ok => "ok"
  | .error => "error"
  | .timeout => "timeout"
  | .crash _ => "crash"

/-! ## Classes -/

/-- The classes of S-21, in the order the output and the table count them. -/
def classes : List String :=
  ["agree-accept", "ours-stricter", "ours-looser", "agree-reject", "refuse-differently",
   "agree-giveup", "broken", "outside"]

/-- The class of the pair of our kind and scalac's verdict (S-21). -/
def classOf (kind : String) : Verdict → String
  | .crash _ => if kind == "outside" then "outside" else "broken"
  | .ok =>
    if kind == "outside" then "outside" else if kind == "ok" then "agree-accept" else "ours-stricter"
  | .error =>
    if kind == "outside" then "outside" else if kind == "ok" then "ours-looser"
    else if kind == "limit" then "refuse-differently" else "agree-reject"
  | .timeout =>
    if kind == "outside" then "outside" else if kind == "ok" then "ours-looser"
    else if kind == "limit" then "agree-giveup" else "refuse-differently"

/-- The class rule of F (H-7): whether a fill of the class `cls` fails.  An
agree-accept fill passes.  An ours-stricter, agree-reject or
refuse-differently fill passes only with a cause.  Any other class fails. -/
def fillFails (cls : String) (cause : Option String) : Bool :=
  if cls == "agree-accept" then false
  else if cls == "ours-stricter" || cls == "agree-reject" || cls == "refuse-differently" then cause.isNone
  else true

/-- The answers of a round trip, in the order the output counts them. -/
def answers : List String := ["same", "gap", "unreadable", "differs", "unresolved"]

/-- The first word of a round trip's answer. -/
def answerWord (a : String) : String := String.ofList (a.toList.takeWhile fun c => c != ':' && c != ' ')

/-! ## The corpus -/

/-- One file of the corpus. -/
structure CFile where
  folder : String
  stem : String
  /-- `<corpus dir>/<folder>/<Stem>.scala`. -/
  path : String
  text : String
  ours : Ours
deriving Inhabited

/-- The fill of a pos file. -/
structure FillOf where
  /-- `<Stem>Fill`. -/
  name : String
  /-- The fill's file under the temporary root. -/
  path : String
  /-- Our side on the fill's text. -/
  ours : Ours
deriving Inhabited

/-- An input of scalac: a corpus file or a fill. -/
structure Src where
  /-- The path scalac is given. -/
  path : String
  /-- The base name its headers carry. -/
  name : String
  /-- The folder, or `fills`. -/
  group : String
  /-- Where `--raw` writes its output, below the raw dir. -/
  rawRel : String
  /-- Whether it goes in the batch (H-4). -/
  inBatch : Bool
deriving Inhabited

/-- The entries of a folder, sorted by name. -/
def entries (d : System.FilePath) : IO (Array IO.FS.DirEntry) := do
  let es ← d.readDir
  return es.qsort fun a b => a.fileName < b.fileName

/-- Whether a path is a regular file. -/
def isRegular (p : System.FilePath) : IO Bool := do
  try
    let m ← p.metadata
    return m.«type» == .file
  catch _ => return false

/-- The `.scala` files of the corpus in table order, as (folder, file name,
path), and the lines of check 0 for every other entry. -/
def listCorpus (dir : String) : IO (Array (String × String × String) × Array String) := do
  let mut bad := #[]
  for e in ← entries dir do
    let p := dir ++ "/" ++ e.fileName
    let ok ← if corpusFolders.contains e.fileName then (p : System.FilePath).isDir
      else if e.fileName == "TABLE.md" then isRegular p
      else pure false
    if !ok then bad := bad.push s!"FAIL {p}: not a corpus folder"
  let mut files := #[]
  for folder in corpusFolders do
    let d := dir ++ "/" ++ folder
    if !(← (d : System.FilePath).isDir) then continue
    for e in ← entries d do
      let p := d ++ "/" ++ e.fileName
      if (← isRegular p) && (e.fileName : System.FilePath).extension == some "scala" then
        files := files.push (folder, e.fileName, p)
      else
        bad := bad.push s!"FAIL {p}: not a .scala file"
  return (files, bad)

/-- The lines of a text. -/
def linesOf (t : String) : List String := t.splitOn "\n"

/-- How many lines start with `// <name>: `. -/
def headerCount (t name : String) : Nat :=
  ((linesOf t).filter (·.startsWith s!"// {name}: ")).length

/-- The six header names of XV2's C-4. -/
def headerNames : List String := ["ours", "scalac", "cause", "rule", "same as", "from"]

/-- The headers a folder takes (C-4). -/
def takes : String → List String
  | "pos" => ["same as", "from"]
  | "neg" => ["ours", "same as", "from"]
  | "disagree" => ["ours", "scalac", "cause", "same as", "from"]
  | _ => ["scalac", "rule", "from"]

/-- The markers of a text: each `// error` and `// warn` with its line. -/
def markersOf (t : String) : List (Nat × String) := Id.run do
  let mut ms := []
  let mut n := 0
  for l in linesOf t do
    n := n + 1
    ms := ms ++ List.replicate ((l.splitOn "// error").length - 1) (n, "error")
    ms := ms ++ List.replicate ((l.splitOn "// warn").length - 1) (n, "warn")
  return ms

/-- A multiset of `(line, kind)` sorted by line, then kind. -/
def sortMarks (ms : List (Nat × String)) : List (Nat × String) :=
  (ms.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).toList

/-- `[<l> <kind>, …]`. -/
def markText (ms : List (Nat × String)) : String :=
  "[" ++ ", ".intercalate (ms.map fun (l, k) => s!"{l} {k}") ++ "]"

/-! ## The expectations -/

/-- The text of check 13 when a run gave no verdict `ok` or `error`. -/
def endWhat (ms : Nat) (s : Seen) : Option String :=
  match s.verdict with
  | .timeout => some s!"scalac timeout after {ms} ms"
  | .crash n => some s!"scalac crash: exit {n} with {(s.diags.filter (·.isErr)).length} error headers"
  | _ => none

/-- The checks 1 to 14 of one file, as `FAIL` lines in the order of the
checks.  `before` holds the (stem, folder) of the files before it in table
order, and `ms` is the deadline of the compile runs. -/
def fileFails (before : List (String × String)) (ms : Nat) (f : CFile) (s : Seen) : List String :=
  Id.run do
  let mut out : List String := []
  let fail (w : String) : String := s!"FAIL {f.path}: {w}"
  -- 1
  if let some (_, g) := before.find? (·.1 == f.stem) then
    out := out ++ [fail s!"the stem {f.stem} is also in {g}/"]
  -- 2
  let pat := s!"object {f.stem} \{"
  if !(linesOf f.text).any (fun l => l.startsWith pat || holds l (" " ++ pat)) then
    out := out ++ [fail s!"no line holds object {f.stem} \{"]
  -- 3
  let same := headerCount f.text "same as" > 0
  let src := headerCount f.text "from" > 0
  if same && src then out := out ++ [fail "both // same as: and // from:"]
  if !same && !src then out := out ++ [fail "neither // same as: nor // from:"]
  -- 4
  for h in headerNames do
    let k := headerCount f.text h
    if k > 0 && !(takes f.folder).contains h then
      out := out ++ [fail s!"{f.folder}/ takes no // {h}: header"]
    else if k > 1 then
      out := out ++ [fail s!"{f.folder}/ takes one // {h}: header"]
  -- 5 and 7
  match expectedKind f.path f.folder (header f.text "// ours: ") with
  | .error msg =>
    let pre := f.path ++ ": "
    let msg := if msg.startsWith pre then String.ofList (msg.toList.drop pre.length) else msg
    out := out ++ [fail msg]
  | .ok k =>
    if k.word != f.ours.kind then
      out := out ++ [fail s!"expected {k.word}, ours is {f.ours.text}"]
  -- 6
  let scl := header f.text "// scalac: "
  if f.folder == "disagree" || f.folder == "outside" then
    if scl.isNone then out := out ++ [fail "no // scalac:"]
  if f.folder == "disagree" && (header f.text "// cause: ").isNone then
    out := out ++ [fail "no // cause:"]
  if f.folder == "outside" && (header f.text "// rule: ").isNone then
    out := out ++ [fail "no // rule:"]
  let cls := classOf f.ours.kind s.verdict
  let cell := scalacCell s
  let decided := match s.verdict with | .ok => true | .error => true | _ => false
  if decided then
    -- 8
    if f.folder == "pos" && s.verdict.word != "ok" then
      out := out ++ [fail s!"scalac {cell}, pos/ wants ok"]
    if f.folder == "neg" && s.verdict.word != "error" then
      out := out ++ [fail s!"scalac {cell}, neg/ wants error"]
    -- 9
    if f.folder == "disagree" || f.folder == "outside" then
      if let some w := scl then
        if w != s.verdict.word then
          out := out ++ [fail s!"// scalac: {w}, the run says {s.verdict.word}"]
    -- 10
    if f.folder == "disagree" && cls != "ours-looser" && cls != "ours-stricter" then
      out := out ++ [fail s!"the pair {f.ours.kind}/{s.verdict.word} is no disagreement"]
    -- 11
    let marks := sortMarks (markersOf f.text)
    let want := sortMarks (s.diags.map fun d => (d.lineNo, if d.isErr then "error" else "warn"))
    if marks != want then
      out := out ++ [fail s!"markers {markText marks} scalac {markText want}"]
  -- 12
  if cls == "ours-looser" && f.folder != "disagree" then
    out := out ++ [fail s!"ours-looser outside disagree/ (ours {f.ours.text}, scalac {cell})"]
  -- 13
  if let some w := endWhat ms s then out := out ++ [fail w]
  -- 14
  for l in s.noPos do
    out := out ++ [fail s!"a diagnostic header without a position: {l}"]
  return out

/-- F on the fill of a pos file (H-7): the `<what>` of the first item that
applies, or none.  `stems` are the stems of the corpus, `fl` the fill with
scalac's verdict on it. -/
def fillWhat (stems : List String) (ms : Nat) (f : CFile) (fl : Option (FillOf × Seen)) :
    Option String :=
  if f.folder != "pos" then none
  else
    match f.ours.fill, fl with
    | some (.error why), _ =>
      if gapReasons.contains why || why.startsWith "reader: " then none else some s!"no fill: {why}"
    | some (.ok _), some (g, s) =>
      let cls := classOf g.ours.kind s.verdict
      let tail := s!"scalac {scalacCell s}, ours {g.ours.text}"
      if stems.contains g.name then some s!"the fill's object {g.name} is a corpus stem"
      else match endWhat ms s with
        | some w => some s!"the fill: {w}"
        | none =>
          if !fillFails cls f.ours.fillCause then none
          else if cls == "outside" then some s!"the fill does not read back: {g.ours.text}"
          else if cls == "ours-stricter" || cls == "agree-reject" || cls == "refuse-differently" then
            some s!"the fill is {cls} without the cause of D-12: {tail}"
          else some s!"the fill is {cls}: {tail}"
    | _, _ => none

/-- The `fill` cell of a file (H-6). -/
def fillCell (f : CFile) (fl : Option (FillOf × Seen)) : String :=
  if f.folder != "pos" then ""
  else
    match f.ours.fill, fl with
    | some (.error why), _ => s!"no fill: {why}"
    | some (.ok _), some (g, s) =>
      let cls := classOf g.ours.kind s.verdict
      if cls == "agree-accept" then cls
      else
        let mark := if f.ours.fillCause.isSome then " (D-12)" else ""
        s!"{cls}{mark}: scalac {scalacCell s}, ours {g.ours.text}"
    | _, _ => ""

/-! ## The table and the output -/

/-- Seconds with one decimal. -/
def secs (ms : Nat) : String :=
  let t := (ms + 50) / 100
  s!"{t / 10}.{t % 10}"

/-- A deadline as the table writes it. -/
def deadlineText (ms : Nat) : String :=
  if ms % 1000 == 0 then s!"{ms / 1000} s" else s!"{ms} ms"

/-- A cell: every `|` written `\|`, every line break a space. -/
def cellText (s : String) : String := (s.replace "|" "\\|").replace "\n" " "

/-- A table row. -/
def row (cells : List String) : String := "| " ++ " | ".intercalate (cells.map cellText) ++ " |"

/-- `<folder> <n>` for each folder with a count above zero, then `fills <n>`,
joined by `, `. -/
def folderCounts (fs : List String) : String :=
  ", ".intercalate (((corpusFolders ++ ["fills"]).filterMap fun d =>
    let n := (fs.filter (· == d)).length
    if n == 0 then none else some s!"{d} {n}"))

/-- `<folder> <n>` for each of the four folders. -/
def allFolderCounts (fs : List String) : String :=
  ", ".intercalate (corpusFolders.map fun d => s!"{d} {(fs.filter (· == d)).length}")

/-- `<class> <n>` for each class. -/
def classCounts (cs : List String) : String :=
  ", ".intercalate (classes.map fun c => s!"{c} {(cs.filter (· == c)).length}")

/-- `<word> <n>` for each word of `ws` that occurs in `xs`, joined by `, `. -/
def someCounts (ws xs : List String) : String :=
  ", ".intercalate (ws.filterMap fun w =>
    let n := (xs.filter (· == w)).length
    if n == 0 then none else some s!"{w} {n}")

/-- `, ` and the text, or nothing for an empty text. -/
def andThen (s : String) : String := if s.isEmpty then "" else ", " ++ s

/-- What the output and the table say about the fills and the round trips. -/
structure Summary where
  /-- The number of fills. -/
  fills : Nat
  /-- The fills' class counts, the classes with at least one fill. -/
  fillClasses : String
  /-- The number of fills with the cause of D-12. -/
  d12 : Nat
  /-- The number of files the reader takes. -/
  trips : Nat
  /-- Their answers, counted. -/
  tripCounts : String
  /-- The number of example programs. -/
  examples : Nat
  /-- Their answers, counted. -/
  exampleCounts : String

/-- The section "Example programs": one line per answer, in the order of first
appearance, with the names in order.  The answer `gap: <reason>` is written
`gap, <reason>`. -/
def exampleLines (exs : List (String × String × Bool)) : List String :=
  let keys := (exs.map (·.2.1)).eraseDups
  keys.map fun k =>
    let ns := (exs.filter (·.2.1 == k)).map (·.1)
    let label := if k.startsWith "gap: " then "gap, " ++ String.ofList (k.toList.drop 5) else k
    s!"- {label.replace "\n" " "} ({ns.length}): {", ".intercalate ns}"

/-- The version scalac printed, from its first line. -/
def versionOf (first : String) : String :=
  let key := "Scala compiler version "
  if first.startsWith key then
    String.ofList ((first.toList.drop key.length).takeWhile (· != ' '))
  else if first.isEmpty then "of no version" else first

/-- The text of `TABLE.md`. -/
def tableText (fe : FrontEnd) (dir version : String) (ms : Nat) (fs : Array CFile)
    (ss : Array Seen) (fills : Array String) (sum : Summary) : String :=
  let fillClasses := if sum.fillClasses.isEmpty then "" else sum.fillClasses ++ ".  "
  let head := [
    s!"# The {fe.name} corpus against scalac",
    "",
    s!"Written by `lake env lean --run scripts/scala/Agree.lean {fe.name} {dir}`.  Do not edit it by hand.",
    "CI runs the same command and fails when the file it writes differs from this one.",
    "",
    s!"- scalac {version}, default flags, {deadlineText ms} per run.",
    s!"- Files: {fs.size}.  {allFolderCounts (fs.toList.map (·.folder))}.",
    s!"- Classes (plan S-21): {classCounts ((fs.zip ss).toList.map fun (f, s) => classOf f.ours.kind s.verdict)}.",
    s!"- Fills of the pos files (F): {sum.fills}.  {fillClasses}{sum.d12} print a written self type as an ascribed literal (XV1 D-12).  F admits a fill of another class than agree-accept only with that cause, and its row says (D-12).",
    s!"- Round trips (R): {sum.trips} files the reader takes{andThen sum.tripCounts}.  {sum.examples} example programs{andThen sum.exampleCounts}.",
    "",
    "## Files",
    "",
    "| file | folder | scalac | warnings | ours | ours in Scala | class | cause or rule | fill | round trip |",
    "|---|---|---|---|---|---|---|---|---|---|"]
  let rows := ((fs.zip ss).zip fills).toList.map fun ((f, s), fill) =>
    let cause :=
      if f.folder == "disagree" then (header f.text "// cause: ").getD ""
      else if f.folder == "outside" then (header f.text "// rule: ").getD ""
      else ""
    row [f.stem, f.folder, scalacCell s, warningsCell s, f.ours.text, f.ours.scala.getD "",
      classOf f.ours.kind s.verdict, cause, fill, (f.ours.trip.map (·.1)).getD ""]
  let tail := ["", "## Example programs", ""] ++ exampleLines fe.examples
  "\n".intercalate (head ++ rows ++ tail) ++ "\n"

/-- Write `<raw>/<rel>` when `--raw` was given. -/
def writeRaw (raw : Option String) (rel : String) (content : String) : IO Unit := do
  if let some r := raw then
    let p : System.FilePath := r ++ "/" ++ rel
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeFile p content

/-- The usage text. -/
def usage : String :=
  "usage: lake env lean --run scripts/scala/Agree.lean <front end> <corpus dir> [--raw <dir>] [--timeout <ms>]\n" ++
  "front ends: " ++ ", ".intercalate (frontEnds.map (·.name))

/-- The options after the corpus dir, each at most once. -/
def parseOpts (raw : Option String) (ms : Option Nat) : List String → Option (Option String × Option Nat)
  | [] => some (raw, ms)
  | "--raw" :: d :: rest => if raw.isSome then none else parseOpts (some d) ms rest
  | "--timeout" :: n :: rest =>
    match n.toNat? with
    | some k => if ms.isSome || k == 0 then none else parseOpts raw (some k) rest
    | none => none
  | _ => none

/-- The corpus dir as given, with a leading `./` and a trailing `/` dropped. -/
partial def normDir (d : String) : String :=
  if d.startsWith "./" && d.length > 2 then normDir (String.ofList (d.toList.drop 2))
  else if d.endsWith "/" && d.length > 1 then normDir (String.ofList d.toList.dropLast)
  else d

/-- Judge the corpus `dir` with the front end `fe`. -/
def judge (fe : FrontEnd) (dir : String) (raw : Option String) (ms t0 : Nat) : IO UInt32 := do
  IO.println s!"agree: front end {fe.name}, corpus {dir}"
  let root ← IO.FS.createTempDir
  try
    let mut global : Array String := #[]
    -- check 15, the version
    let v ← spawnRun "scalac" #["-version"] 120000
    let first := ((linesOf v.out).headD "").trimAscii.toString
    IO.println s!"agree: {first}"
    if !first.startsWith "Scala compiler version 3.8.4 " then
      global := global.push s!"FAIL scalac: the version is {first}, the harness wants 3.8.4"
    -- check 0 and the files
    let (listed, bad) ← listCorpus dir
    global := global ++ bad
    let mut fs : Array CFile := #[]
    let s0 ← IO.monoMsNow
    for (folder, name, path) in listed do
      let text ← IO.FS.readFile path
      let stem := ((name : System.FilePath).fileStem).getD name
      fs := fs.push { folder, stem, path, text, ours := fe.ours stem text.toList }
    -- the fills of the pos files, written under the temporary root and read by our side
    let mut fills : Array (Nat × FillOf) := #[]
    for i in [0:fs.size] do
      let f := fs[i]!
      if f.folder == "pos" then
        if let some (.ok cs) := f.ours.fill then
          let name := f.stem ++ "Fill"
          let p := root / "fill" / s!"{name}.scala"
          IO.FS.createDirAll (root / "fill")
          IO.FS.writeFile p (String.ofList cs)
          fills := fills.push (i, { name, path := p.toString, ours := fe.ours name cs })
    let exs := fe.examples
    let nTrips := (fs.filter (·.ours.trip.isSome)).size
    let s1 ← IO.monoMsNow
    IO.println s!"agree: {fs.size} files, {allFolderCounts (fs.toList.map (·.folder))}"
    IO.println s!"agree: ours on {fs.size} files, {fills.size} fills, {nTrips} round trips and {exs.length} examples in {secs (s1 - s0)} s"
    -- the inputs of scalac: the files in table order, then the fills
    let fileSrc (f : CFile) : Src :=
      { path := f.path, name := f.stem ++ ".scala", group := f.folder,
        rawRel := s!"{f.folder}/{f.stem}.out.txt",
        inBatch := f.folder == "pos" && f.ours.kind != "outside" }
    let fillSrc (g : FillOf) : Src :=
      { path := g.path, name := g.name ++ ".scala", group := "fills",
        rawRel := s!"fill/{g.name}.out.txt", inBatch := g.ours.kind == "ok" }
    let srcs : Array Src := fs.map fileSrc ++ fills.map (fillSrc ·.2)
    -- the batch
    let mut seen : Array (Option Seen) := Array.replicate srcs.size none
    let batch := (List.range srcs.size).filter fun i => srcs[i]!.inBatch
    let mut alone := (List.range srcs.size).filter fun i => !srcs[i]!.inBatch
    let mut runNo := 0
    if batch.isEmpty then
      IO.println "agree: scalac on 0 files at once"
    else
      let out := root / s!"run{runNo}"
      runNo := runNo + 1
      IO.FS.createDirAll out
      let b0 ← IO.monoMsNow
      let r ← spawnRun "scalac" (#["-color:never", "-d", out.toString] ++ (batch.map fun i => srcs[i]!.path).toArray) ms
      let b1 ← IO.monoMsNow
      writeRaw raw "batch.out.txt" (exitLine r)
      let ended := match r.exit with | some n => s!"exit {n}" | none => "timeout"
      let line := s!"agree: scalac on {batch.length} files at once ({folderCounts (batch.map fun i => srcs[i]!.group)}), {ended} in {secs (b1 - b0)} s"
      if batchAccepted r then
        IO.println line
        for i in batch do
          seen := seen.set! i (some (seenBatch srcs[i]!.name r))
      else
        IO.println (line ++ ", so each alone")
        alone := List.range srcs.size
    -- the runs alone
    let mut jobs : Array (Array String) := #[]
    for i in alone do
      let out := root / s!"run{runNo}"
      runNo := runNo + 1
      IO.FS.createDirAll out
      jobs := jobs.push #["-color:never", "-d", out.toString, srcs[i]!.path]
    let a0 ← IO.monoMsNow
    let rs ← pool jobs ms
    let a1 ← IO.monoMsNow
    for (i, r) in alone.zip rs.toList do
      seen := seen.set! i (some (seenAlone srcs[i]!.name r))
    IO.println s!"agree: scalac on {alone.length} files alone ({folderCounts (alone.map fun i => srcs[i]!.group)}), 4 at a time, in {secs (a1 - a0)} s"
    let all : Array Seen := seen.map (·.getD { verdict := .crash 0, diags := [], noPos := [], raw := "" })
    for (src, s) in srcs.zip all do
      writeRaw raw src.rawRel s.raw
    let ss := all.extract 0 fs.size
    let fillSeen := all.extract fs.size all.size
    let mut fillOf : Array (Option (FillOf × Seen)) := Array.replicate fs.size none
    for ((i, g), s) in fills.zip fillSeen do
      fillOf := fillOf.set! i (some (g, s))
    IO.println s!"agree: classes {classCounts ((fs.zip ss).toList.map fun (f, s) => classOf f.ours.kind s.verdict)}"
    let tripWords := fs.toList.filterMap fun f => f.ours.trip.map fun (a, _) => answerWord a
    let sum : Summary := {
      fills := fills.size,
      fillClasses := someCounts classes ((fills.zip fillSeen).toList.map fun ((_, g), s) => classOf g.ours.kind s.verdict),
      d12 := (fills.filter fun (i, _) => fs[i]!.ours.fillCause.isSome).size,
      trips := tripWords.length, tripCounts := someCounts answers tripWords,
      examples := exs.length, exampleCounts := someCounts answers (exs.map fun (_, a, _) => answerWord a) }
    IO.println s!"agree: fills {sum.fills}{andThen sum.fillClasses}, {sum.d12} in the form of D-12"
    IO.println s!"agree: round trips {sum.trips} files{andThen sum.tripCounts}, {sum.examples} examples{andThen sum.exampleCounts}"
    -- the expectations: the global ones, then for each file its checks, its fill and its round trip
    let mut fails := global
    for (n, a, allowed) in exs do
      if !allowed then fails := fails.push s!"FAIL example {n}: round trip {a}"
    let stems := fs.toList.map (·.stem)
    let mut before : List (String × String) := []
    for i in [0:fs.size] do
      let f := fs[i]!
      fails := fails ++ (fileFails before ms f ss[i]!).toArray
      if let some w := fillWhat stems ms f fillOf[i]! then
        fails := fails.push s!"FAIL {f.path}: {w}"
      if let some (a, false) := f.ours.trip then
        fails := fails.push s!"FAIL {f.path}: round trip {a}"
      before := before ++ [(f.stem, f.folder)]
    for l in fails do IO.println l
    -- the table
    let tablePath := dir ++ "/TABLE.md"
    let fillCells := (Array.range fs.size).map fun i => fillCell fs[i]! fillOf[i]!
    IO.FS.writeFile tablePath (tableText fe dir (versionOf first) ms fs ss fillCells sum)
    IO.println s!"agree: wrote {tablePath}"
    let t1 ← IO.monoMsNow
    let noun := if fails.size == 1 then "failure" else "failures"
    IO.println s!"agree: {fails.size} {noun} in {secs (t1 - t0)} s"
    return if fails.isEmpty then (0 : UInt32) else 1
  finally
    IO.FS.removeDirAll root

/-- The command line of the harness. -/
def harness (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let fault : IO UInt32 := do
    IO.eprintln usage
    return 2
  match args with
  | name :: dir :: rest =>
    match frontEnds.find? (·.name == name), parseOpts none none rest with
    | some fe, some (raw, ms) =>
      if !(← (dir : System.FilePath).isDir) then fault
      else judge fe (normDir dir) raw (ms.getD 120000) t0
    | _, _ => fault
  | _ => fault

end Agree

def main (args : List String) : IO UInt32 := do
  Agree.harness args
