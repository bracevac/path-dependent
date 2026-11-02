import Coercions.Nominal.Frontend.ScalaRead.Parse
import Coercions.ScalaSyntax.Print

/-!
# The printer of the pDOT Scala subset

The reader run backwards (plan XI, "Reuse", and plan IX, S-27).  `print`
writes a `File` as the text of a `.scala` file: the header import, a blank
line, `object Name {`, the members, `val program` and `}`.  Reading the text
back gives the tree back up to positions.

The layout is the one of the vanilla printer `ScalaSyntax.Print`, with three
new forms.

* An object member spans lines as a literal does: `object o {`, its members
  one per line two spaces further in, and `}` at the indentation of the line
  that holds the `{`.
* A `def` prints its parameter lists in a row, `(x1: S1)(x2: S2)`.
* A self name goes on its own line after `{`, as the first statement of the
  region.  So the text reads back without the self-name pass of the parser:
  `{` is followed by a token that starts a line, the column rule opens a
  region there, and `s =>` is its first statement.

Everything else is vanilla's.  One member, declaration or statement per line,
two spaces per level.  A refinement stays on one line, with `;`, when it has
at most three members, every one of them small, and `{ … }` takes at most 100
columns.  After `=` or `=>`, a right side that spans lines goes on the next
line two spaces further in, unless it is a block.  Parentheses where Scala
would read the text otherwise: `A & (B & C)`, `(S => T) & U`,
`(S => T) => U`, and a lambda under an ascription, as a receiver or as a
function.

Classes and traits print as written: `[abstract] class C(val x: T, y: U)
extends P(a, b) with Q {`, the members one per line two spaces further in, and
`}`.  A body with no member prints no braces.  `new q.C(a, b)` prints in
place, and `new q.C` without arguments prints no parentheses.

`print` is structural and returns `List Char`, so the kernel runs it.  The
fixed words are lists of characters spelled out, and names are read off their
bytes by `ScalaSyntax.Print.name`.
-/

namespace NominalFrontend.ScalaRead

open ScalaSyntax.Print (name nl parensIf gap wAny wNothing wThis wType wVal wDef wProgram wNewObject wImport
  wObject wClass wTrait wExtends)

namespace Print

/-- `.type`. -/
def wDotType : List Char := ['.', 't', 'y', 'p', 'e']

/-- `new `. -/
def wNew : List Char := ['n', 'e', 'w', ' ']

/-- `abstract `. -/
def wAbstract : List Char := ['a', 'b', 's', 't', 'r', 'a', 'c', 't', ' ']

/-- `override `. -/
def wOverride : List Char := ['o', 'v', 'e', 'r', 'r', 'i', 'd', 'e', ' ']

/-- ` with `. -/
def wWith : List Char := [' ', 'w', 'i', 't', 'h', ' ']

/-- `override ` when `o`. -/
def ovw (o : Bool) : List Char := if o then wOverride else []

/-- The header line, `import scala.reflect.Selectable.reflectiveSelectable`. -/
def wHeader : List Char := wImport ++ Parse.headerChars

/-- A path: `this`, `x`, `q.a`. -/
def path : Path → List Char
  | .this _ => wThis
  | .var _ x => name x
  | .sel q _ a => path q ++ '.' :: name a

/-- Whether a type is a function type. -/
def isFn : Ty → Bool
  | .fn .. => true
  | _ => false

/-- Whether a type is an intersection. -/
def isAnd : Ty → Bool
  | .and .. => true
  | _ => false

/-- The number of declarations of a refinement. -/
def count : Decls → Nat
  | .nil => 0
  | .typ _ _ _ _ r | .alias _ _ _ r | .val _ _ _ r => count r + 1

mutual
/-- Whether a type is small: every refinement inside it has at most three
members, every one of them small. -/
def small (T : Ty) : Bool :=
  match T with
  | .any _ | .nothing _ | .sel .. | .sngl .. | .name .. => true
  | .refine _ ds => decide (count ds ≤ 3) && smallDecls ds
  | .and S U | .fn _ _ S U => small S && small U
termination_by structural T
/-- Whether a bound is absent or small. -/
def smallB (b : Bound) : Bool :=
  match b with
  | .absent => true
  | .given T => small T
termination_by structural b
/-- Whether every declaration has small types. -/
def smallDecls (ds : Decls) : Bool :=
  match ds with
  | .nil => true
  | .typ _ _ lo hi r => smallB lo && smallB hi && smallDecls r
  | .alias _ _ T r | .val _ _ T r => small T && smallDecls r
termination_by structural ds
end

/-- Whether a refinement stays on one line: at most three members, every one
small, and `{ one }` within 100 columns. -/
def fits (ds : Decls) (one : List Char) : Bool :=
  decide (count ds ≤ 3) && smallDecls ds && decide (one.length + 4 ≤ 100)

/-- A declaration `d` followed by the declarations `r`: on its own line at the
indentation `j` under `some j`, else followed by `; ` unless it is the last. -/
def item (i : Option Nat) (r : Decls) (d : List Char) : List Char :=
  match i, r with
  | some j, _ => nl j ++ d
  | none, .nil => d
  | none, _ => d ++ [';', ' ']

mutual
/-- A type on a line at the indentation `j` under `some j`, or on one line
under `none`. -/
def ty (i : Option Nat) (T : Ty) : List Char :=
  match T with
  | .any _ => wAny
  | .nothing _ => wNothing
  | .sel _ q A => path q ++ '.' :: name A
  | .sngl _ q => path q ++ wDotType
  | .name _ A => name A
  | .refine _ ds =>
    let one := decls none ds
    match i with
    | some j =>
      if fits ds one then ['{', ' '] ++ one ++ [' ', '}']
      else '{' :: decls (some (j + 2)) ds ++ nl j ++ ['}']
    | none => ['{', ' '] ++ one ++ [' ', '}']
  | .and S U => parensIf (isFn S) (ty i S) ++ [' ', '&', ' '] ++ parensIf (isFn U || isAnd U) (ty i U)
  | .fn _ (some x) S U => '(' :: name x ++ [':', ' '] ++ ty i S ++ [')', ' ', '=', '>', ' '] ++ ty i U
  | .fn _ none S U => parensIf (isFn S) (ty i S) ++ [' ', '=', '>', ' '] ++ ty i U
termination_by structural T
/-- A bound after its symbol `sym`, or nothing when it is absent. -/
def bnd (i : Option Nat) (sym : List Char) (b : Bound) : List Char :=
  match b with
  | .absent => []
  | .given T => sym ++ ty i T
termination_by structural b
/-- The declarations of a refinement, one per line at the indentation `j`
under `some j`, or separated by `; ` under `none`. -/
def decls (i : Option Nat) (ds : Decls) : List Char :=
  match ds with
  | .nil => []
  | .typ _ A lo hi r =>
    item i r (wType ++ name A ++ bnd i [' ', '>', ':', ' '] lo ++ bnd i [' ', '<', ':', ' '] hi) ++ decls i r
  | .alias _ A T r => item i r (wType ++ name A ++ [' ', '=', ' '] ++ ty i T) ++ decls i r
  | .val _ a T r => item i r (wVal ++ name a ++ [':', ' '] ++ ty i T) ++ decls i r
termination_by structural ds
end

/-- Whether a type spans lines: some refinement in it does not fit on one
line. -/
def long (T : Ty) : Bool :=
  match T with
  | .refine _ ds => !fits ds (decls none ds)
  | .and S U | .fn _ _ S U => long S || long U
  | _ => false
termination_by structural T

/-- Whether a term is a lambda. -/
def isLam : Tm → Bool
  | .lam .. => true
  | _ => false

/-- Whether a term is `new` with no arguments, which a selection or an application parenthesizes, since
`new K.v` reads as `new` of the class `K.v` and `new K(e)` as `new` with an argument (G-4). -/
def isBareNew : Tm → Bool
  | .new _ _ .nil => true
  | _ => false

/-- Whether a term is a block. -/
def isBlock : Tm → Bool
  | .block .. => true
  | _ => false

mutual
/-- Whether a term spans lines: it holds a block or a literal, or a type that
spans lines. -/
def multi (t : Tm) : Bool :=
  match t with
  | .path _ => false
  | .sel s _ _ => multi s
  | .app f e => multi f || multi e
  | .lam _ _ T b => (T.map long).getD false || multi b
  | .asc _ e T => multi e || long T
  | .block .. | .lit .. => true
  | .new _ _ as => multiArgs as
termination_by structural t
/-- Whether an argument spans lines. -/
def multiArgs (as : Args) : Bool :=
  match as with
  | .nil => false
  | .cons t r => multi t || multiArgs r
termination_by structural as
end

/-- Whether the right side of `=` or the body of `=>` goes on the next line:
it spans lines and is not a block. -/
def breaks (e : Tm) : Bool := multi e && !isBlock e

/-- A written type after its symbol `sym`, if any, on a line at the
indentation `i`. -/
def tyOpt (i : Nat) (sym : List Char) : Option Ty → List Char
  | some T => sym ++ ty (some i) T
  | none => []

/-- A self name on its own line at the indentation `i`, `s =>`, if any. -/
def selfLine (i : Nat) : Option String → List Char
  | some x => nl i ++ name x ++ [' ', '=', '>']
  | none => []

/-- A class reference, `C` or `q.C`. -/
def classRef (K : ClassRef) : List Char :=
  match K.pre with
  | some q => path q ++ '.' :: name K.name
  | none => name K.name

/-- A constructor parameter, `x: T` or `val x: T`. -/
def cparam (i : Nat) (x : CParam) : List Char :=
  (if x.isVal then wVal else []) ++ name x.name ++ [':', ' '] ++ ty (some i) x.ty

/-- Constructor parameters separated by `, `. -/
def cparams (i : Nat) : List CParam → List Char
  | [] => []
  | [x] => cparam i x
  | x :: xs => cparam i x ++ [',', ' '] ++ cparams i xs

/-- The keyword of a class definition. -/
def clsWord : ClsKind → List Char
  | .concrete => wClass
  | .abstract => wAbstract ++ wClass
  | .trait => wTrait

/-- The parameter lists of a `def` in a row, `(x1: S1)(x2: S2)`. -/
def params (i : Nat) : List Param → List Char
  | [] => []
  | x :: xs => '(' :: name x.name ++ [':', ' '] ++ ty (some i) x.ty ++ [')'] ++ params i xs

mutual
/-- A term that starts on a line at the indentation `i`, and the indentation
of the line it ends on.  That is `i` unless the term ends with a lambda body
on its own line. -/
def tm (i : Nat) (t : Tm) : List Char × Nat :=
  match t with
  | .path q => (path q, i)
  | .sel s _ a =>
    let (u, j) := tm i s
    (parensIf (isLam s || isBareNew s) u ++ '.' :: name a, j)
  | .app f e =>
    let (u, j) := tm i f
    let (v, k) := tm j e
    (parensIf (isLam f || isBareNew f) u ++ '(' :: v ++ [')'], k)
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
  | .lit _ s ms => (wNewObject ++ selfLine (i + 2) s ++ mems (i + 2) ms ++ nl i ++ ['}'], i)
  | .new _ K as =>
    match as with
    | .nil => (wNew ++ classRef K, i)
    | _ =>
      let (u, j) := args i as
      (wNew ++ classRef K ++ '(' :: u ++ [')'], j)
termination_by structural t
/-- Arguments separated by `, `, and the indentation of the line the last ends on. -/
def args (i : Nat) (as : Args) : List Char × Nat :=
  match as with
  | .nil => ([], i)
  | .cons t .nil => tm i t
  | .cons t r =>
    let (u, j) := tm i t
    let (v, k) := args j r
    (u ++ [',', ' '] ++ v, k)
termination_by structural as
/-- The parents of a class, ` extends P(args)` then ` with Q` each, `first` before the first. -/
def parents (i : Nat) (first : Bool) (Ps : Parents) : List Char :=
  match Ps with
  | .nil => []
  | .cons P as r =>
    (if first then wExtends else wWith) ++ classRef P ++
      (match as with
       | .nil => []
       | _ => '(' :: (args i as).1 ++ [')']) ++ parents i false r
termination_by structural Ps
/-- The members of a class or trait body, each on its own line at the indentation `i`. -/
def cmems (i : Nat) (ms : CMems) : List Char :=
  match ms with
  | .nil => []
  | .typ _ o A lo hi r =>
    nl i ++ ovw o ++ wType ++ name A ++ bnd (some i) [' ', '>', ':', ' '] lo ++ bnd (some i) [' ', '<', ':', ' '] hi ++
      cmems i r
  | .alias _ o A T r => nl i ++ ovw o ++ wType ++ name A ++ [' ', '=', ' '] ++ ty (some i) T ++ cmems i r
  | .valDecl _ o a T r => nl i ++ ovw o ++ wVal ++ name a ++ [':', ' '] ++ ty (some i) T ++ cmems i r
  | .val _ o a T e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ ovw o ++ wVal ++ name a ++ [':', ' '] ++ ty (some i) T ++ [' ', '='] ++ gap (breaks e) k ++ (tm k e).1 ++
      cmems i r
  | .defDecl _ o f ps R r => nl i ++ ovw o ++ wDef ++ name f ++ params i ps ++ [':', ' '] ++ ty (some i) R ++ cmems i r
  | .defn _ o f ps R e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ ovw o ++ wDef ++ name f ++ params i ps ++ [':', ' '] ++ ty (some i) R ++ [' ', '='] ++ gap (breaks e) k ++
      (tm k e).1 ++ cmems i r
termination_by structural ms
/-- The statements of a block, each on its own line at the indentation
`i`. -/
def stats (i : Nat) (ss : Stats) : List Char :=
  match ss with
  | .last t => nl i ++ (tm i t).1
  | .val _ x T e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ wVal ++ name x ++ tyOpt i [':', ' '] T ++ [' ', '='] ++ gap (breaks e) k ++ (tm k e).1 ++ stats i r
termination_by structural ss
/-- The members of the wrapper, an object or a literal, each on its own line
at the indentation `i`. -/
def mems (i : Nat) (ms : Mems) : List Char :=
  match ms with
  | .nil => []
  | .obj _ o s b r =>
    nl i ++ wObject ++ name o ++ [' ', '{'] ++ selfLine (i + 2) s ++ mems (i + 2) b ++ nl i ++ ['}'] ++ mems i r
  | .typ _ A T r => nl i ++ wType ++ name A ++ [' ', '=', ' '] ++ ty (some i) T ++ mems i r
  | .val _ a T e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ wVal ++ name a ++ tyOpt i [':', ' '] T ++ [' ', '='] ++ gap (breaks e) k ++ (tm k e).1 ++ mems i r
  | .defn _ f ps R e r =>
    let k := if breaks e then i + 2 else i
    nl i ++ wDef ++ name f ++ params i ps ++ tyOpt i [':', ' '] R ++ [' ', '='] ++ gap (breaks e) k ++
      (tm k e).1 ++ mems i r
  | .cls _ k C ps Ps b r =>
    nl i ++ clsWord k ++ name C ++
      (match ps with
       | [] => []
       | _ => '(' :: cparams i ps ++ [')']) ++ parents i true Ps ++
      (match b with
       | .nil => []
       | _ => [' ', '{'] ++ cmems (i + 2) b ++ nl i ++ ['}']) ++ mems i r
termination_by structural ms
end

end Print

/-- The text of a file: the header, a blank line, the wrapper object with its
members, `val program` and `}`, ending with a line break. -/
def print (F : File) : List Char :=
  let k := if Print.breaks F.body then 4 else 2
  Print.wHeader ++ ['\n', '\n'] ++ wObject ++ name F.name ++ [' ', '{'] ++ Print.mems 2 F.mems ++
    nl 2 ++ wVal ++ wProgram ++ Print.tyOpt 2 [':', ' '] F.ty ++ [' ', '='] ++ gap (Print.breaks F.body) k ++
    (Print.tm k F.body).1 ++ ['\n', '}', '\n']

end NominalFrontend.ScalaRead
