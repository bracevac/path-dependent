import Coercions.ScalaSyntax.Scope

/-!
# The printer

The reader run backwards.  `print` writes a `Program` as the text of a
`.scala` file: the header imports, a blank line, `object Name {`, the prelude,
the program and `}`.  The front ends print their terms through it (plan IX,
S-27), and reading the text back gives the tree back up to positions, the
round trip (R) of the plan.

The layout is the one of `E5.scala` and of the judge's `CapP` and `ClsP`.

* One statement, member or declaration per line, two spaces per level.  The
  first statement of a brace region goes on the line after its `{`, and the
  `}` at the indentation of the line that holds the `{`.
* A refinement stays on one line, with `;`, when it has at most three members,
  every refinement inside it has too, and `{ … }` takes at most 100 columns.
  Blocks and object literals always span lines, as in `E5.scala` and `CapP`.
* After `=` or `=>`, a right side or a lambda body that spans lines goes on the
  next line, two spaces further in, unless it is a block, whose `{` stays on
  the line.  No other line break is written.
* Parentheses where Scala would read the text otherwise: `A & (B & C)`,
  `(S => T) & U`, `(S => T) => U`, `(S & T)^{c}`, `(S^) & T` (a bare `^`
  before `&` is an infix operator, probe `HatAnd`), and a lambda under an
  ascription, as a receiver or as a function, `(((x: S) => e): T)`.

So the text satisfies the column rule by construction.  Every line break
starts a statement at the column of its region, puts a `}` at the indentation
of the line of its `{`, or continues a statement after `=` or `=>` two spaces
right of the line it leaves.  A type ends on a line at the indentation it
started from, and so does a block or a literal.  The line that a statement
continues from is then its first line, its latest continuation line, or a `}`
line at the indentation of one of them, so a continuation is never left of the
one before.  Inside `(` the column rule checks nothing but the brace regions,
which follow the same pattern.  scalac 3.8.4 parses the printed text of each
program of `Tests` as it parses the text as written, with and without
`-no-indent`, up to the block `{ e }` that its default mode makes of the body
`e` of a lambda that starts a line, when `e` is not a block
(`notes-scala-xv0/scalac-g4/`).

`print` is structural and returns `List Char`, so the kernel runs it, and the
round trip of E5 is a theorem by `decide +kernel`
(`notes-scala-xv0/kernel-read.lean`).  The fixed words are spelled out as
lists of characters and names are read off their bytes, as in `Scope`, since
`String.toList` depends on `Classical.choice` in Lean v4.29.1 and the kernel
decodes a `String` literal slowly.

This module imports Lean core only, through `Scope`.
-/

namespace ScalaSyntax

namespace Print

/-! ## Text -/

/-- The characters of a name.  The parser makes ASCII names, one byte per
character. -/
def name (x : String) : List Char := Scope.nameChars x

/-- A line break and `n` spaces of indentation. -/
def nl (n : Nat) : List Char := '\n' :: List.replicate n ' '

/-- The text `t` in parentheses when `b` holds. -/
def parensIf (b : Bool) (t : List Char) : List Char := if b then '(' :: t ++ [')'] else t

/-! ### Fixed words -/

/-- `Any`. -/
def wAny : List Char := ['A', 'n', 'y']

/-- `Nothing`. -/
def wNothing : List Char := ['N', 'o', 't', 'h', 'i', 'n', 'g']

/-- `this`. -/
def wThis : List Char := ['t', 'h', 'i', 's']

/-- `caps.any`. -/
def wCapsAny : List Char := ['c', 'a', 'p', 's', '.', 'a', 'n', 'y']

/-- `.only[`, before a classifier. -/
def wOnly : List Char := ['.', 'o', 'n', 'l', 'y', '[']

/-- `type `. -/
def wType : List Char := ['t', 'y', 'p', 'e', ' ']

/-- `val `. -/
def wVal : List Char := ['v', 'a', 'l', ' ']

/-- `def `. -/
def wDef : List Char := ['d', 'e', 'f', ' ']

/-- `program`. -/
def wProgram : List Char := ['p', 'r', 'o', 'g', 'r', 'a', 'm']

/-- `new Object {`. -/
def wNewObject : List Char := ['n', 'e', 'w', ' ', 'O', 'b', 'j', 'e', 'c', 't', ' ', '{']

/-- `import `. -/
def wImport : List Char := ['i', 'm', 'p', 'o', 'r', 't', ' ']

/-- `object `. -/
def wObject : List Char := ['o', 'b', 'j', 'e', 'c', 't', ' ']

/-- `class `. -/
def wClass : List Char := ['c', 'l', 'a', 's', 's', ' ']

/-- `trait `. -/
def wTrait : List Char := ['t', 'r', 'a', 'i', 't', ' ']

/-- ` extends `. -/
def wExtends : List Char := [' ', 'e', 'x', 't', 'e', 'n', 'd', 's', ' ']

/-- `caps.SharedCapability`. -/
def wShared : List Char :=
  ['c', 'a', 'p', 's', '.', 'S', 'h', 'a', 'r', 'e', 'd', 'C', 'a', 'p', 'a', 'b', 'i', 'l', 'i', 't', 'y']

/-- `, caps.Classifier`, after the parent of a classifier trait. -/
def wClassifier : List Char :=
  [',', ' ', 'c', 'a', 'p', 's', '.', 'C', 'l', 'a', 's', 's', 'i', 'f', 'i', 'e', 'r']

/-! ## Capture sets -/

/-- A capture reference. -/
def capRef : CapRef → List Char
  | .var _ x => name x
  | .any _ => wCapsAny
  | .only _ (some x) k => name x ++ wOnly ++ name k ++ [']']
  | .only _ none k => wCapsAny ++ wOnly ++ name k ++ [']']

/-- The references of a capture set, separated by commas. -/
def capRefs : CapSet → List Char
  | [] => []
  | [c] => capRef c
  | c :: cs => capRef c ++ [',', ' '] ++ capRefs cs

/-- A capture set, `{c1, …, cn}`. -/
def capSet (cs : CapSet) : List Char := '{' :: capRefs cs ++ ['}']

/-- A bound of a capture member after its symbol `sym`, if any. -/
def capBound (sym : List Char) : Option CapSet → List Char
  | some cs => sym ++ capSet cs
  | none => []

/-- An arrow with the spaces around it: ` => `, ` -> ` or ` ->{c} `. -/
def arrow : Arrow → List Char
  | .fat => [' ', '=', '>', ' ']
  | .thin none => [' ', '-', '>', ' ']
  | .thin (some cs) => [' ', '-', '>'] ++ capSet cs ++ [' ']

/-! ## Types -/

/-- Whether a type is a function type. -/
def isFn : Ty → Bool
  | .fn .. => true
  | _ => false

/-- Whether a type is an intersection. -/
def isAnd : Ty → Bool
  | .and .. => true
  | _ => false

/-- Whether a type is a capturing type. -/
def isCapt : Ty → Bool
  | .capt .. => true
  | _ => false

/-- Whether the text of a type ends with a bare `^`.  The right operand of an
intersection prints without parentheses unless it is an intersection or a
function type. -/
def bareHat : Ty → Bool
  | .capt _ _ none => true
  | .and _ (.capt _ _ none) => true
  | _ => false

/-- The number of declarations of a refinement. -/
def count : Decls → Nat
  | .nil => 0
  | .typ _ _ _ _ r | .alias _ _ _ r | .val _ _ _ r | .cap _ _ _ _ r | .capAlias _ _ _ r => count r + 1

mutual
/-- Whether every refinement in a type has at most three members. -/
def small (T : Ty) : Bool :=
  match T with
  | .any _ | .nothing _ | .sel .. => true
  | .refine _ ds => decide (count ds ≤ 3) && smallDecls ds
  | .and S U | .fn _ _ S _ U => small S && small U
  | .capt _ S _ => small S
termination_by structural T
/-- Whether every refinement in an optional type has at most three
members. -/
def smallOpt (T : Option Ty) : Bool :=
  match T with
  | some U => small U
  | none => true
termination_by structural T
/-- Whether every refinement in the declarations has at most three
members. -/
def smallDecls (ds : Decls) : Bool :=
  match ds with
  | .nil => true
  | .typ _ _ lo hi r => smallOpt lo && smallOpt hi && smallDecls r
  | .alias _ _ T r | .val _ _ T r => small T && smallDecls r
  | .cap _ _ _ _ r | .capAlias _ _ _ r => smallDecls r
termination_by structural ds
end

/-- Whether a refinement with the declarations `ds` stays on one line, when
`one` is their text on one line: at most three members, every refinement
inside it too, and at most 100 columns for `{ one }`. -/
def fits (ds : Decls) (one : List Char) : Bool :=
  decide (count ds ≤ 3) && smallDecls ds && decide (one.length + 4 ≤ 100)

/-- A declaration `d` of a refinement, followed by the declarations `r`: on a
line of its own at the indentation `j` when `i` is `some j`, or on one line
when `i` is `none`, with `; ` when more follow. -/
def item (i : Option Nat) (r : Decls) (d : List Char) : List Char :=
  match i, r with
  | some j, _ => nl j ++ d
  | none, .nil => d
  | none, _ => d ++ [';', ' ']

mutual
/-- A type that starts on a line at the indentation `i`, or all on one line
when `i` is `none`.  It ends on a line at the indentation `i` too. -/
def ty (i : Option Nat) (T : Ty) : List Char :=
  match T with
  | .any _ => wAny
  | .nothing _ => wNothing
  | .sel _ (.this _) A => wThis ++ '.' :: name A
  | .sel _ (.var _ x) A => name x ++ '.' :: name A
  | .refine _ ds =>
    let one := decls none ds
    match i with
    | some j =>
      if fits ds one then ['{', ' '] ++ one ++ [' ', '}']
      else '{' :: decls (some (j + 2)) ds ++ nl j ++ ['}']
    | none => ['{', ' '] ++ one ++ [' ', '}']
  | .and S U =>
    parensIf (isFn S || bareHat S) (ty i S) ++ [' ', '&', ' '] ++ parensIf (isFn U || isAnd U) (ty i U)
  | .fn _ (some x) S a U => '(' :: name x ++ [':', ' '] ++ ty i S ++ [')'] ++ arrow a ++ ty i U
  | .fn _ none S a U => parensIf (isFn S) (ty i S) ++ arrow a ++ ty i U
  | .capt _ S c => parensIf (isFn S || isAnd S || isCapt S) (ty i S) ++ '^' :: (c.map capSet).getD []
termination_by structural T
/-- An optional type after the symbol `sym`, if any. -/
def tyOpt (i : Option Nat) (sym : List Char) (T : Option Ty) : List Char :=
  match T with
  | some U => sym ++ ty i U
  | none => []
termination_by structural T
/-- The declarations of a refinement, one per line at the indentation `i`, or
on one line separated by `;` when `i` is `none`. -/
def decls (i : Option Nat) (ds : Decls) : List Char :=
  match ds with
  | .nil => []
  | .typ _ A lo hi r =>
    item i r (wType ++ name A ++ tyOpt i [' ', '>', ':', ' '] lo ++ tyOpt i [' ', '<', ':', ' '] hi) ++
      decls i r
  | .alias _ A T r => item i r (wType ++ name A ++ [' ', '=', ' '] ++ ty i T) ++ decls i r
  | .val _ a T r => item i r (wVal ++ name a ++ [':', ' '] ++ ty i T) ++ decls i r
  | .cap _ C lo hi r =>
    item i r (wType ++ name C ++ '^' :: capBound [' ', '>', ':', ' '] lo ++ capBound [' ', '<', ':', ' '] hi) ++
      decls i r
  | .capAlias _ C c r => item i r (wType ++ name C ++ ['^', ' ', '=', ' '] ++ capSet c) ++ decls i r
termination_by structural ds
end

/-- Whether a type spans lines: a refinement in it does not fit on one
line. -/
def long (T : Ty) : Bool :=
  match T with
  | .refine _ ds => !fits ds (decls none ds)
  | .and S U | .fn _ _ S _ U => long S || long U
  | .capt _ S _ => long S
  | .any _ | .nothing _ | .sel .. => false
termination_by structural T

/-! ## Terms -/

/-- Whether a term is a lambda. -/
def isLam : Tm → Bool
  | .lam .. => true
  | _ => false

/-- Whether a term is a block. -/
def isBlock : Tm → Bool
  | .block .. => true
  | _ => false

/-- Whether a term spans lines: it holds a block, an object literal, or a type
that spans lines. -/
def multi (t : Tm) : Bool :=
  match t with
  | .var .. | .this _ => false
  | .sel s _ _ => multi s
  | .app f e => multi f || multi e
  | .lam _ _ T b => (T.map long).getD false || multi b
  | .asc _ e T => multi e || long T
  | .block .. | .lit .. => true
termination_by structural t

/-- Whether the right side of `=` or the body of `=>` goes on the next line:
it spans lines and is not a block. -/
def breaks (e : Tm) : Bool := multi e && !isBlock e

/-- What goes between `=` or `=>` and the term after it: a line break to the
indentation `k` when `b` holds, else a space. -/
def gap (b : Bool) (k : Nat) : List Char := if b then nl k else [' ']

/-- A written type after `:`, if any, on a line at the indentation `i`. -/
def ascribed (i : Nat) (T : Option Ty) : List Char := tyOpt (some i) [':', ' '] T

mutual
/-- A term that starts on a line at the indentation `i`, and the indentation
of the line it ends on.  That is `i` unless the term ends with a lambda body
on its own line. -/
def tm (i : Nat) (t : Tm) : List Char × Nat :=
  match t with
  | .var _ x => (name x, i)
  | .this _ => (wThis, i)
  | .sel s _ a =>
    let (u, j) := tm i s
    (parensIf (isLam s) u ++ '.' :: name a, j)
  | .app f e =>
    let (u, j) := tm i f
    let (v, k) := tm j e
    (parensIf (isLam f) u ++ '(' :: v ++ [')'], k)
  | .lam _ x T b =>
    let param := match T with
      | some U => '(' :: name x ++ [':', ' '] ++ ty (some i) U ++ [')']
      | none => name x
    let k := if breaks b then i + 2 else i
    let (u, j) := tm k b
    (param ++ [' ', '=', '>'] ++ gap (breaks b) k ++ u, j)
  | .asc _ e T =>
    let (u, j) := tm i e
    ('(' :: parensIf (isLam e) u ++ [':', ' '] ++ ty (some j) T ++ [')'], j)
  | .block _ ss => ('{' :: stats (i + 2) ss ++ nl i ++ ['}'], i)
  | .lit _ s ds =>
    let self := match s with
      | some x => nl (i + 2) ++ name x ++ [' ', '=', '>']
      | none => []
    (wNewObject ++ self ++ defs (i + 2) ds ++ nl i ++ ['}'], i)
termination_by structural t
/-- The statements of a block, each on its own line at the indentation
`i`. -/
def stats (i : Nat) (ss : Stats) : List Char :=
  match ss with
  | .last t => nl i ++ (tm i t).1
  | .val _ x T e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ wVal ++ name x ++ ascribed i T ++ [' ', '='] ++ gap (breaks e) k ++ (tm k e).1 ++ stats i r
termination_by structural ss
/-- The members of an object literal, each on its own line at the
indentation `i`. -/
def defs (i : Nat) (ds : Defs) : List Char :=
  match ds with
  | .nil => []
  | .typ _ A T r => nl i ++ wType ++ name A ++ [' ', '=', ' '] ++ ty (some i) T ++ defs i r
  | .val _ a T e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ wVal ++ name a ++ ascribed i T ++ [' ', '='] ++ gap (breaks e) k ++ (tm k e).1 ++ defs i r
  | .cap _ C c r => nl i ++ wType ++ name C ++ ['^', ' ', '=', ' '] ++ capSet c ++ defs i r
termination_by structural ds
end

/-! ## Files -/

/-- The header imports, each on its own line. -/
def imports : List (Pos × String) → List Char
  | [] => []
  | (_, x) :: is => wImport ++ name x ++ '\n' :: imports is

/-- A line of the prelude. -/
def preludeItem : PreludeItem → List Char
  | .capClass _ C => wClass ++ name C ++ wExtends ++ wShared
  | .classifier _ K none => wTrait ++ name K ++ wExtends ++ wShared ++ wClassifier
  | .classifier _ K (some P) => wTrait ++ name K ++ wExtends ++ name P ++ wClassifier
  | .platClass _ C K => wClass ++ name C ++ wExtends ++ name K

/-- The platform parameters, `x: C^`, separated by commas. -/
def params : List (Pos × String × String) → List Char
  | [] => []
  | [(_, x, C)] => name x ++ [':', ' '] ++ name C ++ ['^']
  | (_, x, C) :: ps => name x ++ [':', ' '] ++ name C ++ ['^', ',', ' '] ++ params ps

/-- The head of the program: `val program`, or `def program(x: C^, …)` with
the platform as its parameters. -/
def head : Option (List (Pos × String × String)) → List Char
  | none => wVal ++ wProgram
  | some ps => wDef ++ wProgram ++ '(' :: params ps ++ [')']

end Print

open Print in
/-- The text of a file (plan IX, S-27): the header imports, a blank line,
`object Name {`, the prelude, the program and `}`, in the layout of the column
rule.  Reading it back gives the program back up to positions. -/
def print (P : Program) : List Char :=
  let k := if breaks P.body then 4 else 2
  imports P.imports ++ (if P.imports.isEmpty then [] else ['\n']) ++
    wObject ++ name P.name ++ [' ', '{'] ++ (P.prelude.map fun l => nl 2 ++ preludeItem l).flatten ++
    nl 2 ++ head P.params ++ ascribed 2 P.ty ++ [' ', '='] ++ gap (breaks P.body) k ++ (tm k P.body).1 ++
    ['\n', '}', '\n']

end ScalaSyntax
