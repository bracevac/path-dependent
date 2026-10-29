import Coercions.PDot.Frontend.ScalaRead.Ast
import Coercions.ScalaSyntax.Parse

/-!
# The parser of the pDOT Scala subset

`parseFile` reads the characters of a `.scala` file into a `File` (plan XI,
"XS: the Scala subset").  It runs the shared lexer, a pass on self names, the
column rule of plan IX, and a recursive descent on fuel from the tokens to the
tree.  Every refusal has a position and a message that names the construct.

The lexer, the column rule and the combinators of the descent are the vanilla
reader's, imported unchanged (`ScalaSyntax.lex`, `ScalaSyntax.layout`,
`ScalaSyntax.Parse`).

The self-name pass.  `new Object { o =>` with the members on later lines
opens a one-line region at `{` under the column rule, and the next line is
refused.  scalac reads that shape (XS0's `pos/E5m.scala`).  So `scan` takes
out each self name `s =>` that follows the `{` of `object o {` or `new Object {`
on its line when the members start a later line, runs the column rule on the
rest, and puts the pair back after its `{`.  A block `{ x =>` is no template
and keeps the column rule's refusal.

The descent has one function per production of the grammar, and the fuel falls
by one at each call.  A selection on a path folds into a longer path
(`selOn`), so a term path is always `Tm.path`.
-/

namespace PDotFrontend.ScalaRead

open ScalaSyntax (Pos Err Tok Token)

/-! ## The self-name pass -/

/-- A self name `s =>` taken out of the tokens: the `{` it follows, the name,
and the arrow. -/
structure Lifted where
  /-- The `{` the self name follows. -/
  brace : Pos
  /-- `s`. -/
  name : Token
  /-- `=>`. -/
  arrow : Token

/-- Where the scan stands: 0 anywhere, 1 after `object`, 2 after `new`, 3 after
`object o` or `new Object`, where a `{` opens a template. -/
def stepState : Nat → Tok → Nat
  | _, .kw "object" => 1
  | _, .kw "new" => 2
  | 1, .ident _ _ => 3
  | 2, .ident "Object" _ => 3
  | _, _ => 0

/-- Take out each `s =>` after a template's `{` on its line, when the token
after `=>` starts a later line. -/
def liftSelves : Nat → List Token → List Token × List Lifted
  | _, [] => ([], [])
  | st, t :: rest =>
    let skip : List Token × List Lifted :=
      match liftSelves (stepState st t.tok) rest with
      | (ts', ls) => (t :: ts', ls)
    match rest with
    | s :: r :: u :: ts =>
      if decide (st = 3) && t.tok == .sym "{" && r.tok == .sym "=>" && u.first then
        match s.tok with
        | .ident _ _ =>
          match liftSelves 0 (u :: ts) with
          | (ts', ls) => (t :: ts', ⟨t.pos, s, r⟩ :: ls)
        | _ => skip
      else skip
    | _ => skip

/-- Put each self name back after its `{`. -/
def lowerSelves (ls : List Lifted) : List Token → List Token
  | [] => []
  | t :: ts =>
    match t.tok, ls.find? (fun l => decide (l.brace = t.pos)) with
    | .sym "{", some l => t :: l.name :: l.arrow :: lowerSelves ls ts
    | _, _ => t :: lowerSelves ls ts

/-- The tokens of a file: the lexer, the self-name pass, the column rule of
plan IX, the self names put back. -/
def scan (cs : List Char) : Except Err (List Token) := do
  let ts ← ScalaSyntax.lex cs
  let (ts', ls) := liftSelves 0 ts
  let ts'' ← ScalaSyntax.layout ts'
  return lowerSelves ls ts''

namespace Parse

open ScalaSyntax.Parse (Parser endTok next sees advance advanceBy refuse expected afterExpr expectSym pName
  noFuel bound isSep skipSeps afterClose startsLambda pImports lastPos)

/-! ## The messages -/

/-- R-A: a type member of an object or a literal with no `=`. -/
def msgRA : String := "a type member of an object is an alias in pDOT"
/-- R-P: a def with no list, an empty list, two parameters in a list, or a def
in a refinement. -/
def msgRP : String := "a def takes one parameter per list, and a refinement declares no def"
/-- R-O: an object in a block or a term. -/
def msgRO : String := "an object is a member of the wrapper, an object or a literal"
/-- R-O: a member named `program` other than the wrapper's last `val`. -/
def msgProgram : String := "`program` names the program of the wrapper object: rename this member"
/-- A def in a block or a term. -/
def msgDefTerm : String := "a def is a member of the wrapper, an object or a literal"
/-- A member after `program`, or a wrapper with no `val program`. -/
def msgAfter : String := "the wrapper object ends with `val program`"
/-- R-T: `class` or `trait`. -/
def msgRT : String := "classes and traits are outside the subset"
/-- R-T: `extends`. -/
def msgExtends : String := "`extends` is outside the subset"
/-- R-I: an import beyond the header. -/
def msgRI : String := "imports other than the header's are outside the subset"
/-- A file with no import, or whose first import is not the header. -/
def msgHeader : String := "the header is the one line `import scala.reflect.Selectable.reflectiveSelectable`"

/-- `scala.reflect.Selectable.reflectiveSelectable`, spelled out. -/
def headerChars : List Char :=
  ['s', 'c', 'a', 'l', 'a', '.', 'r', 'e', 'f', 'l', 'e', 'c', 't', '.',
   'S', 'e', 'l', 'e', 'c', 't', 'a', 'b', 'l', 'e', '.',
   'r', 'e', 'f', 'l', 'e', 'c', 't', 'i', 'v', 'e', 'S', 'e', 'l', 'e', 'c', 't', 'a', 'b', 'l', 'e']

/-! ## Types -/

/-- The member after `q.` in a type: more path steps, then `A` or `type`.  The
head is the `.`. -/
def pTyPath : Nat → Path → Parser Ty
  | 0, _ => noFuel
  | n + 1, q => do
    advance
    let t ← next
    match t.tok with
    | .kw "type" =>
      advance
      return .sngl t.pos q
    | .ident a _ =>
      advance
      if (← sees (.sym ".")) then pTyPath n (.sel q t.pos a) else return .sel t.pos q a
    | _ => expected "a type member or `type`"

mutual
/-- `(x: S) => T`, or Infix [`=>` Type]. -/
def pType : Nat → Parser Ty
  | 0 => noFuel
  | n + 1 => do
    match (← get) with
    | ⟨.sym "(", _, _⟩ :: ⟨.ident x _, _, _⟩ :: ⟨.sym ":", _, _⟩ :: _ =>
      advanceBy 3
      let S ← pType n
      let c ← next
      if c.tok == .sym "," then refuse c.pos "functions of several parameters are outside the subset"
      expectSym ")"
      let a ← next
      if a.tok == .sym "=>" then
        advance
        return .fn a.pos (some x) S (← pType n)
      refuse a.pos "a named tuple `(x: S)` is outside the subset: write `(x: S) => T`"
    | _ =>
      let S ← pInfix n
      let a ← next
      if a.tok == .sym "=>" then
        advance
        return .fn a.pos none S (← pType n)
      return S
/-- Simple {`&` Simple}. -/
def pInfix : Nat → Parser Ty
  | 0 => noFuel
  | n + 1 => do pAnds n (← pSimple n)
/-- The operands after `&`, nested to the left. -/
def pAnds : Nat → Ty → Parser Ty
  | 0, _ => noFuel
  | n + 1, S => do
    if (← sees (.sym "&")) then
      advance
      pAnds n (.and S (← pSimple n))
    else return S
/-- `Any`, `Nothing`, a path then a member, a bare member, `( Type )`,
`{ Decls }`. -/
def pSimple : Nat → Parser Ty
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .ident "Any" _ =>
      advance
      return .any t.pos
    | .ident "Nothing" _ =>
      advance
      return .nothing t.pos
    | .ident x _ =>
      advance
      if (← sees (.sym ".")) then pTyPath n (.var t.pos x) else return .name t.pos x
    | .kw "this" =>
      advance
      if !(← sees (.sym ".")) then expected "`.` after `this` in a type"
      pTyPath n (.this t.pos)
    | .sym "(" =>
      match (← get) with
      | _ :: ⟨.ident _ _, _, _⟩ :: ⟨.sym ":", _, _⟩ :: _ =>
        refuse t.pos "put the dependent function type in its own parentheses: ((x: S) => T)"
      | _ => pure ()
      advance
      let T ← pType n
      let c ← next
      if c.tok == .sym "," then refuse c.pos "tuples and functions of several parameters are outside the subset"
      expectSym ")"
      return T
    | .sym "{" =>
      advance
      if (← sees (.sym "}")) then refuse t.pos "an empty refinement is outside the subset: write `Any`"
      let ds ← pDecls n
      expectSym "}"
      return .refine t.pos ds
    | .sym "=>" => refuse t.pos "by-name types are outside the subset"
    | _ => expected "a type"
/-- `type A [>: T] [<: T]`, `type A = T`, `val a: T`.  A `def` is refused. -/
def pDecls : Nat → Parser Decls
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .kw "type" =>
      advance
      let (p, A) ← pName
      if (← sees (.sym "=")) then
        advance
        let T ← pType n
        return .alias p A T (← pDeclsRest n)
      let lo ← bound ">:" (pType n)
      let hi ← bound "<:" (pType n)
      return .typ p A (match lo with | some T => .given T | none => .absent)
        (match hi with | some T => .given T | none => .absent) (← pDeclsRest n)
    | .kw "val" =>
      advance
      let (p, a) ← pName
      expectSym ":"
      let T ← pType n
      return .val p a T (← pDeclsRest n)
    | .kw "def" => refuse t.pos msgRP
    | _ => expected "`type` or `val`"
/-- After a declaration: separators and more, or the `}`. -/
def pDeclsRest : Nat → Parser Decls
  | 0 => noFuel
  | n + 1 => do
    if isSep (← next).tok then
      skipSeps
      if (← sees (.sym "}")) then return .nil
      pDecls n
    else if (← sees (.sym "}")) then return .nil
    else expected "`;` or `}`"
end

/-! ## Terms and members -/

/-- `t.a`, folded into the path when `t` is one. -/
def selOn (t : Tm) (p : Pos) (a : String) : Tm :=
  match t with
  | .path q => .path (.sel q p a)
  | _ => .sel t p a

/-- A self name `s =>` after a template's `{`.  A typed self is refused. -/
def pSelf : Parser (Option String) := do
  match (← get) with
  | ⟨.ident s _, _, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ =>
    advanceBy 2
    skipSeps
    return some s
  | ⟨.ident _ _, _, _⟩ :: ⟨.sym ":", q, _⟩ :: _ => refuse q "a typed self is outside the subset"
  | _ => return none

/-- `(x: T)`, one parameter list of a def.  The head is `(`. -/
def pParam (n : Nat) : Parser Param := do
  let o ← next
  advance
  if (← sees (.sym ")")) then refuse o.pos msgRP
  let (p, x) ← pName
  expectSym ":"
  let T ← pType n
  let c ← next
  if c.tok == .sym "," then refuse c.pos msgRP
  expectSym ")"
  return ⟨p, x, T⟩

/-- The parameter lists of a def, while `(` follows. -/
def pParams : Nat → Parser (List Param)
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .sym "(" =>
      let x ← pParam n
      return x :: (← pParams n)
    | .sym "[" => refuse t.pos "type parameters are outside the subset"
    | _ => return []

mutual
/-- A lambda in one of its three forms, or Postfix. -/
def pExpr : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do
    match (← get) with
    | ⟨.ident x _, p, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ =>
      advanceBy 2
      return .lam p x none (← pExpr n)
    | ⟨.sym "(", _, _⟩ :: ⟨.ident x _, p, _⟩ :: ⟨.sym ")", _, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ =>
      advanceBy 4
      return .lam p x none (← pExpr n)
    | ⟨.sym "(", _, _⟩ :: ⟨.ident x _, p, _⟩ :: ⟨.sym ":", _, _⟩ :: ts =>
      if afterClose 0 ts != some (.sym "=>") then pPostfix n
      else
        advanceBy 3
        let T ← pType n
        let c ← next
        if c.tok == .sym "," then refuse c.pos "lambdas of several parameters are outside the subset"
        expectSym ")"
        expectSym "=>"
        return .lam p x (some T) (← pExpr n)
    | _ => pPostfix n
/-- Atom, then selections and applications. -/
def pPostfix : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do pSuffix n (← pAtom n)
/-- `.a` and `(e)` after a term. -/
def pSuffix : Nat → Tm → Parser Tm
  | 0, _ => noFuel
  | n + 1, t => do
    let tk ← next
    match tk.tok with
    | .sym "." =>
      advance
      let (p, a) ← pName
      pSuffix n (selOn t p a)
    | .sym "(" =>
      advance
      if (← sees (.sym ")")) then refuse tk.pos "an application without an argument is outside the subset"
      let u ← pExpr n
      let c ← next
      match c.tok with
      | .sym ")" =>
        advance
        pSuffix n (.app t u)
      | .sym "," => refuse c.pos "several arguments are outside the subset"
      | _ => afterExpr "`)`"
    | .sym "{" => refuse tk.pos "a block argument `f { … }` is outside the subset: write `f({ … })`"
    | .sym "[" => refuse tk.pos "type arguments are outside the subset"
    | .ident _ _ => refuse tk.pos "infix and postfix operators are outside the subset"
    | _ => return t
/-- A name, `this`, `( Expr )`, `( Postfix : Type )`, a block, a literal. -/
def pAtom : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .ident x _ =>
      advance
      return .path (.var t.pos x)
    | .kw "this" =>
      advance
      return .path (.this t.pos)
    | .sym "(" =>
      advance
      if (← sees (.sym ")")) then refuse t.pos "the unit value `()` is outside the subset"
      let lam := startsLambda (← get)
      let e ← pExpr n
      let c ← next
      match c.tok with
      | .sym ")" =>
        advance
        return e
      | .sym ":" =>
        if lam then refuse c.pos "put the lambda in its own parentheses: ((x: S) => e): T"
        advance
        let T ← pType n
        expectSym ")"
        return .asc c.pos e T
      | .sym "," => refuse c.pos "tuples are outside the subset"
      | _ => expected "`)` or `:`"
    | .sym "{" =>
      advance
      let ss ← pStats n
      expectSym "}"
      return .block t.pos ss
    | .kw "new" => pLiteral n
    | .kw "class" | .kw "trait" => refuse t.pos msgRT
    | .kw "extends" => refuse t.pos msgExtends
    | .kw "object" => refuse t.pos msgRO
    | .kw "def" => refuse t.pos msgDefTerm
    | .kw "type" => refuse t.pos "a type definition in a term is outside the subset"
    | .kw "import" => refuse t.pos msgRI
    | _ => expected "an expression"
/-- The `val`s of a block, then its result. -/
def pStats : Nat → Parser Stats
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .kw "val" =>
      advance
      let (p, x) ← pName
      let T ← bound ":" (pType n)
      expectSym "="
      let e ← pExpr n
      let s ← next
      if s.tok == .sym "}" then refuse s.pos "a block ends with its result, not with a `val`"
      if !isSep s.tok then afterExpr "a line break or `;`"
      skipSeps
      let u ← next
      if u.tok == .sym "}" then refuse u.pos "a block ends with its result, not with a `val`"
      return .val p x T e (← pStats n)
    | _ =>
      let e ← pExpr n
      if isSep (← next).tok then
        skipSeps
        let u ← next
        if u.tok == .sym "}" then return .last e
        refuse u.pos "a block holds `val`s and then one result"
      if (← sees (.sym "}")) then return .last e
      afterExpr "`}`"
/-- `new Object { [s =>] Mems }`. -/
def pLiteral : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    advance
    let c ← next
    match c.tok with
    | .ident "Object" _ => advance
    | .ident _ _ => refuse c.pos "`new` takes only `Object` in the subset: write `new Object { … }`"
    | _ => expected "`Object`"
    expectSym "{"
    let self ← pSelf
    if (← sees (.sym "}")) then refuse t.pos "an empty object literal is outside the subset"
    let ms ← pMems n false
    expectSym "}"
    return .lit t.pos self ms
/-- Members, one or more.  At the wrapper's level (`top`) they stop before
`val program`. -/
def pMems : Nat → Bool → Parser Mems
  | 0, _ => noFuel
  | n + 1, top => do
    match (← get) with
    | ⟨.kw "val", _, _⟩ :: ⟨.ident "program" _, q, _⟩ :: _ =>
      if top then return .nil
      refuse q msgProgram
    | _ => pure ()
    let t ← next
    match t.tok with
    | .kw "object" =>
      advance
      let (p, o) ← pName
      if decide (o = "program") then refuse p msgProgram
      if (← sees (.kw "extends")) then refuse (← next).pos msgExtends
      let b ← next
      expectSym "{"
      let self ← pSelf
      if (← sees (.sym "}")) then refuse b.pos "an empty object is outside the subset"
      let body ← pMems n false
      expectSym "}"
      return .obj p o self body (← pMemsRest n top)
    | .kw "type" =>
      advance
      let (p, A) ← pName
      if !(← sees (.sym "=")) then refuse p msgRA
      advance
      let T ← pType n
      return .typ p A T (← pMemsRest n top)
    | .kw "val" =>
      advance
      let (p, a) ← pName
      let T ← bound ":" (pType n)
      expectSym "="
      let e ← pExpr n
      return .val p a T e (← pMemsRest n top)
    | .kw "def" =>
      advance
      let (p, f) ← pName
      if decide (f = "program") then refuse p msgProgram
      let ps ← pParams n
      if ps.isEmpty then refuse p msgRP
      let R ← bound ":" (pType n)
      expectSym "="
      let e ← pExpr n
      return .defn p f ps R e (← pMemsRest n top)
    | .kw "class" | .kw "trait" => refuse t.pos msgRT
    | .kw "extends" => refuse t.pos msgExtends
    | .kw "import" => refuse t.pos msgRI
    | _ => expected (if top then "a member or `val program`" else "a member")
/-- After a member: separators and more, or the `}`.  At the wrapper's level a
`}` is refused: the wrapper has no `val program`. -/
def pMemsRest : Nat → Bool → Parser Mems
  | 0, _ => noFuel
  | n + 1, top => do
    if isSep (← next).tok then
      skipSeps
      if (← sees (.sym "}")) then
        if top then refuse (← next).pos msgAfter else return .nil
      pMems n top
    else if (← sees (.sym "}")) then
      if top then refuse (← next).pos msgAfter else return .nil
    else afterExpr (if top then "a line break or `;`" else "`;` or `}`")
end

/-! ## The file -/

/-- The imports at the top: the header alone.  None, or a first import other
than the header, gets msgHeader.  An import after the header gets msgRI. -/
def checkHeader : List (Pos × String) → Parser Unit
  | [] => refuse ⟨1, 1⟩ msgHeader
  | (p, i) :: rest =>
    if !decide (i = String.ofList headerChars) then refuse p msgHeader
    else match rest with
      | [] => pure ()
      | (q, _) :: _ => refuse q msgRI

/-- The header, `object W {`, the members, `val program [: T] = e`, `}`. -/
def pFile (n : Nat) : Parser File := do
  checkHeader (← pImports n)
  if !(← sees (.kw "object")) then expected "`object`"
  advance
  let (p, W) ← pName
  expectSym "{"
  match (← get) with
  | ⟨.ident _ _, _, _⟩ :: ⟨.sym "=>", q, _⟩ :: _ => refuse q "a self name on the wrapper object is outside the subset"
  | _ => pure ()
  let ms ← pMems n true
  advanceBy 2
  let T ← bound ":" (pType n)
  expectSym "="
  let e ← pExpr n
  let s ← next
  skipSeps
  let t ← next
  match t.tok with
  | .sym "}" => advance
  | .kw "object" | .kw "val" | .kw "def" | .kw "type" => refuse t.pos msgAfter
  | _ =>
    if isSep s.tok then refuse t.pos msgAfter
    afterExpr "`}`"
  skipSeps
  if (← next).tok != .sym "" then expected "the end of the file"
  return ⟨p, W, ms, T, e⟩

end Parse

/-- The file of a list of laid out tokens, or the first refusal.  The fuel is
`8 * n + 8` for `n` tokens, as the vanilla parser's. -/
def parseTokens (ts : List Token) : Except Err File :=
  (Parse.pFile (8 * ts.length + 8)).run' (ts ++ [ScalaSyntax.Parse.endTok (ScalaSyntax.Parse.lastPos ts)])

/-- The file of the characters of a `.scala` file, or the first refusal of the
lexer, the column rule or the parser. -/
def parseFile : List Char → Except Err File := fun cs => scan cs >>= parseTokens

end PDotFrontend.ScalaRead
