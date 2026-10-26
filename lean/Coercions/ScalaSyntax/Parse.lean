import Coercions.ScalaSyntax.Ast

/-!
# The parser

The second stage of the Scala reader.  `parseTokens` reads the tokens that
`tokens` laid out into a `Program` by recursive descent, and refuses at its
position every construct that the subsets leave out, with a message that names
it.  `parseFile` runs the lexer, the column rule and the parser in turn.

The grammar is the union of the plan's sections on the vanilla subset,
Captures and Classifiers.  Three choices follow scalac's own parser.

* After `(x:` or `(x)` in a term, the parser looks ahead to the matching `)`.
  A following `=>` makes a lambda parameter, and otherwise the parentheses
  hold an expression.  In a type, `(x:` can only start a dependent function
  type.  So an error points at the real fault (d3 §3).
* A lambda followed by `:` inside parentheses is refused, since scalac reads
  `((x: S) => e: T)` as a lambda whose body is ascribed (refute-d1 F5).
* After `->`, a `{` opens a capture set only when a name, `this` or `}`
  follows it, and otherwise the result type is a refinement.  A bare `^`
  before `&` is refused, since scalac reads that `^` as an infix type
  operator (probes `ArrowRefine` and `HatAnd` of `notes-scala-xv0/scalac-g2/`).

The parser only reads the shape of the file.  Whether a name is in scope, a
member is declared, or a capture form belongs to a front end is decided later,
by `check` and by each front end's translation.

Every function is structural.  The two mutual blocks of the descent take a
fuel that falls by one at each call, `8 * n + 8` for `n` tokens (d1's bound),
and every loop outside them takes a fuel of at least the number of tokens it
can still read.  No `String` is read character by character.

The helpers of the descent live in `ScalaSyntax.Parse`, so that the short
names stay free for the later modules of `ScalaSyntax`.

This module imports Lean core only, through `Ast`.
-/

namespace ScalaSyntax

namespace Parse

/-! ## The parser monad -/

/-- A parser: from the tokens still to read, a result and the tokens after
it, or a refusal. -/
abbrev Parser := StateT (List Token) (Except Err)

/-- The token that marks the end of the file, at the position of the file's
last token.  The lexer never makes an empty `sym`, so nothing else matches
it. -/
def endTok (p : Pos) : Token := ⟨.sym "", p, false⟩

/-- The token at the head.  The parser never reads the end marker, so the
list is never empty. -/
def next : Parser Token := do
  match (← get) with
  | t :: _ => pure t
  | [] => pure (endTok ⟨0, 0⟩)

/-- Whether the head token is `t`. -/
def sees (t : Tok) : Parser Bool := do
  return (← next).tok == t

/-- Drop the head token. -/
def advance : Parser Unit := modify List.tail

/-- Drop `k` tokens, which the caller has matched. -/
def advanceBy (k : Nat) : Parser Unit := modify (·.drop k)

/-- Refuse at `p` with the reason `msg`. -/
def refuse (p : Pos) (msg : String) : Parser α := throw ⟨p, msg⟩

/-- How a message names a token. -/
def describe : Tok → String
  | .ident s _ | .kw s | .reserved s => "`" ++ s ++ "`"
  | .sym "" => "the end of the file"
  | .sym s => "`" ++ s ++ "`"
  | .sep => "a line break"

/-- Refuse at the head token, where `what` was expected.  A word that Scala
reserves is refused as outside the subset, whatever was expected. -/
def expected (what : String) : Parser α := do
  let t ← next
  match t.tok with
  | .reserved s => refuse t.pos ("`" ++ s ++ "` is outside the subset")
  | tok => refuse t.pos ("expected " ++ what ++ ", found " ++ describe tok)

/-- Refuse at the head token after an expression, where `what` was expected.
A `:` there is an ascription outside parentheses. -/
def afterExpr (what : String) : Parser α := do
  let t ← next
  if t.tok == .sym ":" then refuse t.pos "an ascription goes in its own parentheses: (e: T)"
  expected what

/-- Read the symbol `s`, or refuse. -/
def expectSym (s : String) : Parser Unit := do
  if (← sees (.sym s)) then advance else expected ("`" ++ s ++ "`")

/-- Read a name, and give its position. -/
def pName : Parser (Pos × String) := do
  let t ← next
  match t.tok with
  | .ident x _ =>
    advance
    pure (t.pos, x)
  | _ => expected "a name"

/-- The fuel ran out.  The fuel that `parseTokens` gives suffices, so no input
reaches this. -/
def noFuel : Parser α := do
  refuse (← next).pos "the parser ran out of fuel"

/-- After the symbol `s`, a phrase read by `p`, if the head is `s`. -/
def bound (s : String) (p : Parser α) : Parser (Option α) := do
  if (← sees (.sym s)) then
    advance
    return some (← p)
  return none

/-! ## Separators -/

/-- A separator of statements: a line break that the column rule made one,
or `;`. -/
def isSep : Tok → Bool
  | .sep | .sym ";" => true
  | _ => false

/-- The tokens after the separators at the head. -/
def dropSeps : List Token → List Token
  | [] => []
  | t :: ts => if isSep t.tok then dropSeps ts else t :: ts

/-- Skip the separators at the head, if any. -/
def skipSeps : Parser Unit := modify dropSeps

/-! ## Lookahead -/

/-- The token after the `)` that closes an open `(`, read `d` levels of
parentheses deep. -/
def afterClose : Nat → List Token → Option Tok
  | _, [] => none
  | 0, ⟨.sym ")", _, _⟩ :: ts => ts.head?.map (·.tok)
  | d + 1, ⟨.sym ")", _, _⟩ :: ts => afterClose d ts
  | d, ⟨.sym "(", _, _⟩ :: ts => afterClose (d + 1) ts
  | d, _ :: ts => afterClose d ts

/-- Whether the tokens start a lambda: `x =>`, `(x) =>` or `(x: T) =>`. -/
def startsLambda : List Token → Bool
  | ⟨.ident _ _, _, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ => true
  | ⟨.sym "(", _, _⟩ :: ⟨.ident _ _, _, _⟩ :: ⟨.sym ")", _, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ => true
  | ⟨.sym "(", _, _⟩ :: ⟨.ident _ _, _, _⟩ :: ⟨.sym ":", _, _⟩ :: ts =>
    afterClose 0 ts == some (.sym "=>")
  | _ => false

/-- Whether a `{` after `->` opens a capture set: a name, `this` or `}`
follows it, as in scalac (`canStartCaptureSetContentsTokens`). -/
def capSetAhead : List Token → Bool
  | ⟨.sym "{", _, _⟩ :: ⟨.ident _ _, _, _⟩ :: _ => true
  | ⟨.sym "{", _, _⟩ :: ⟨.kw "this", _, _⟩ :: _ => true
  | ⟨.sym "{", _, _⟩ :: ⟨.sym "}", _, _⟩ :: _ => true
  | _ => false

/-! ## Capture sets -/

/-- The classifier of `.only[K]`, after `.only`. -/
def pOnly : Parser String := do
  expectSym "["
  let (_, k) ← pName
  expectSym "]"
  return k

/-- A capture reference: `x`, `caps.any`, `x.only[K]` or `caps.any.only[K]`.
`this` crashes the pickler of scalac 3.8.4 in a capture set (refute-d3
`cap/ThisCap`), and `caps.cap` is experimental, so both are refused. -/
def pCapRef : Parser CapRef := do
  let t ← next
  match t.tok with
  | .kw "this" => refuse t.pos "`this` in a capture set is outside the subset"
  | .ident x _ =>
    advance
    if !(← sees (.sym ".")) then return .var t.pos x
    advance
    let (q, y) ← pName
    if x == "caps" then
      if y != "any" then
        refuse q ("`caps." ++ y ++ "` is outside the subset" ++
          (if y == "cap" then ": write `caps.any`" else ""))
      if !(← sees (.sym ".")) then return .any t.pos
      advance
      let (r, z) ← pName
      if z != "only" then refuse r ("`." ++ z ++ "` in a capture set is outside the subset")
      return .only t.pos none (← pOnly)
    if y != "only" then refuse q ("`." ++ y ++ "` in a capture set is outside the subset")
    return .only t.pos (some x) (← pOnly)
  | _ => expected "a capture reference"

/-- The references of a capture set after its `{`, one or more, separated by
commas.  Each step reads a token, so the number of tokens is enough fuel. -/
def pCapRefs : Nat → Parser CapSet
  | 0 => noFuel
  | n + 1 => do
    let c ← pCapRef
    if (← sees (.sym ",")) then
      advance
      return c :: (← pCapRefs n)
    return [c]

/-- A capture set, `{c1, …, cn}`, possibly empty. -/
def pCapSet : Parser CapSet := do
  expectSym "{"
  if (← sees (.sym "}")) then
    advance
    return []
  let cs ← pCapRefs ((← get).length + 1)
  if !(← sees (.sym "}")) then expected "`,` or `}`"
  advance
  return cs

/-- The arrow of a function type at the head, if any: its position and its
kind. -/
def pArrow : Parser (Option (Pos × Arrow)) := do
  let t ← next
  match t.tok with
  | .sym "=>" =>
    advance
    return some (t.pos, .fat)
  | .sym "->" =>
    advance
    if capSetAhead (← get) then return some (t.pos, .thin (some (← pCapSet)))
    return some (t.pos, .thin none)
  | _ => return none

/-- The member after `q.` in a type, `q.A`. -/
def pMember (q : Path) : Parser Ty := do
  let t ← next
  match t.tok with
  | .ident A _ =>
    advance
    let u ← next
    if u.tok == .sym "." then refuse u.pos "paths of length two are outside the subset"
    return .sel t.pos q A
  | .kw "type" => refuse t.pos "singleton types `x.type` are outside the subset"
  | _ => expected "a type member"

/-! ## Types -/

mutual
/-- `Type ::= Dom Arrow Type | Infix`, where `Dom ::= (x: Type) | Infix` and
`Arrow ::= => | -> | ->{…}`. -/
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
      match (← pArrow) with
      | some (p, a) => return .fn p (some x) S a (← pType n)
      | none =>
        refuse (← next).pos "a named tuple `(x: S)` is outside the subset: write `(x: S) => T`"
    | _ =>
      let S ← pInfix n
      match (← pArrow) with
      | some (p, a) => return .fn p none S a (← pType n)
      | none => return S
/-- `Infix ::= Capt {& Capt}`. -/
def pInfix : Nat → Parser Ty
  | 0 => noFuel
  | n + 1 => do pAnds n (← pCapt n)
/-- The operands after `S` in `S & T & …`, nested to the left as in Scala. -/
def pAnds : Nat → Ty → Parser Ty
  | 0, _ => noFuel
  | n + 1, S => do
    if (← sees (.sym "&")) then
      advance
      pAnds n (.and S (← pCapt n))
    else return S
/-- `Capt ::= Simple [^ [CapSet]]`.  The `^` binds to the operand of `&`. -/
def pCapt : Nat → Parser Ty
  | 0 => noFuel
  | n + 1 => do
    let S ← pSimple n
    let t ← next
    if t.tok != .sym "^" then return S
    advance
    if (← sees (.sym "{")) then return .capt t.pos S (some (← pCapSet))
    if (← sees (.sym "&")) then
      refuse t.pos "a bare `^` before `&` is an infix operator in Scala: write `(S^) & T`"
    return .capt t.pos S none
/-- `Simple ::= Any | Nothing | x.A | this.A | (Type) | { Decl {Sep Decl} }`. -/
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
      if !(← sees (.sym ".")) then refuse t.pos ("the type `" ++ x ++ "` is outside the subset")
      advance
      pMember (.var t.pos x)
    | .kw "this" =>
      advance
      if !(← sees (.sym ".")) then expected "`.` after `this` in a type"
      advance
      pMember (.this t.pos)
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
/-- The declarations of a refinement after its `{`, one or more.  A capture
member is `type C^`, with capture sets as its bounds. -/
def pDecls : Nat → Parser Decls
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .kw "type" =>
      advance
      let (p, A) ← pName
      if (← sees (.sym "^")) then
        advance
        if (← sees (.sym "=")) then
          advance
          let c ← pCapSet
          return .capAlias p A c (← pDeclsRest n)
        let lo ← bound ">:" pCapSet
        let hi ← bound "<:" pCapSet
        return .cap p A lo hi (← pDeclsRest n)
      if (← sees (.sym "=")) then
        advance
        let T ← pType n
        return .alias p A T (← pDeclsRest n)
      let lo ← bound ">:" (pType n)
      let hi ← bound "<:" (pType n)
      return .typ p A lo hi (← pDeclsRest n)
    | .kw "val" =>
      advance
      let (p, a) ← pName
      expectSym ":"
      let T ← pType n
      return .val p a T (← pDeclsRest n)
    | .kw "def" => refuse t.pos "methods are outside the subset"
    | _ => expected "`type` or `val`"
/-- After a declaration: the end of the refinement at `}`, or separators and
more declarations. -/
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

/-! ## Terms -/

/-- The self name of a literal after its `{`, if one is written.  A typed
self `s: T =>` is refused. -/
def pSelf : Parser (Option String) := do
  match (← get) with
  | ⟨.ident s _, _, _⟩ :: ⟨.sym "=>", _, _⟩ :: _ =>
    advanceBy 2
    skipSeps
    return some s
  | ⟨.ident _ _, _, _⟩ :: ⟨.sym ":", q, _⟩ :: _ => refuse q "a typed self is outside the subset"
  | _ => return none

mutual
/-- `Expr ::= Params => Expr | Postfix`, where `Params ::= x | (x) | (x: Type)`. -/
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
/-- `Postfix ::= Atom {.a | (Expr)}`. -/
def pPostfix : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do pSuffix n (← pAtom n)
/-- The selections and applications after the term `t`. -/
def pSuffix : Nat → Tm → Parser Tm
  | 0, _ => noFuel
  | n + 1, t => do
    let tk ← next
    match tk.tok with
    | .sym "." =>
      advance
      let (p, a) ← pName
      pSuffix n (.sel t p a)
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
/-- `Atom ::= x | this | (Expr) | (Expr: Type) | Block | Literal`. -/
def pAtom : Nat → Parser Tm
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .ident x _ =>
      advance
      return .var t.pos x
    | .kw "this" =>
      advance
      return .this t.pos
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
    | .kw "class" | .kw "trait" =>
      refuse t.pos "classes and traits are outside the subset, except the prelude's"
    | .kw "object" => refuse t.pos "objects other than the wrapper are outside the subset"
    | .kw "def" => refuse t.pos "methods are outside the subset"
    | .kw "type" => refuse t.pos "a type definition in a term is outside the subset"
    | .kw "import" => refuse t.pos "imports other than the header's are outside the subset"
    | .kw "extends" => refuse t.pos "`extends` is outside the subset, except in the prelude"
    | _ => expected "an expression"
/-- The statements of a block after its `{`: `val`s, each followed by a
separator, then the result. -/
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
/-- `Literal ::= new Object { [s =>] LitDef {Sep LitDef} }`.  `new` takes
`Object` only. -/
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
    let ds ← pDefs n
    expectSym "}"
    return .lit t.pos self ds
/-- The members of a literal after its `{` and self name, one or more.  A
capture member is `type C^ = {…}`. -/
def pDefs : Nat → Parser Defs
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .kw "type" =>
      advance
      let (p, A) ← pName
      if (← sees (.sym "^")) then
        advance
        expectSym "="
        let c ← pCapSet
        return .cap p A c (← pDefsRest n)
      if !(← sees (.sym "=")) then
        refuse (← next).pos "a type member of an object literal is an alias: `type A = T`"
      advance
      let T ← pType n
      return .typ p A T (← pDefsRest n)
    | .kw "val" =>
      advance
      let (p, a) ← pName
      let T ← bound ":" (pType n)
      expectSym "="
      let e ← pExpr n
      return .val p a T e (← pDefsRest n)
    | .kw "def" => refuse t.pos "methods are outside the subset"
    | _ => expected "`val` or `type`"
/-- After a member of a literal: the end of the literal at `}`, or separators
and more members. -/
def pDefsRest : Nat → Parser Defs
  | 0 => noFuel
  | n + 1 => do
    if isSep (← next).tok then
      skipSeps
      if (← sees (.sym "}")) then return .nil
      pDefs n
    else if (← sees (.sym "}")) then return .nil
    else afterExpr "`;` or `}`"
end

/-! ## Files -/

/-- The rest of a dotted name after its first part `acc`. -/
def pDotted : Nat → String → Parser String
  | 0, _ => noFuel
  | n + 1, acc => do
    if (← sees (.sym ".")) then
      advance
      let (_, y) ← pName
      pDotted n (acc ++ "." ++ y)
    else return acc

/-- The header imports, each followed by a separator, at their first names. -/
def pImports : Nat → Parser (List (Pos × String))
  | 0 => noFuel
  | n + 1 => do
    if !(← sees (.kw "import")) then return []
    advance
    let (p, x) ← pName
    let i ← pDotted n x
    let t ← next
    if !isSep t.tok && t.tok != .sym "" then expected "a line break or `;`"
    skipSeps
    return (p, i) :: (← pImports n)

/-- The shapes of a prelude class. -/
def classShape : String :=
  "a prelude class is `class C extends caps.SharedCapability` or `class C extends K`"

/-- The shapes of a prelude trait. -/
def traitShape : String :=
  "a prelude trait is `trait K extends caps.SharedCapability, caps.Classifier` " ++
    "or `trait K extends P, caps.Classifier`"

/-- Refuse with `shape` at the head unless it is `extends`, then read it. -/
def expectExtends (shape : String) : Parser Unit := do
  let t ← next
  if t.tok != .kw "extends" then refuse t.pos shape
  advance

/-- Refuse with `shape` at the head unless it is a separator, then skip the
separators. -/
def endItem (shape : String) : Parser Unit := do
  let t ← next
  if !isSep t.tok then refuse t.pos shape
  skipSeps

/-- The prelude lines, in the three shapes of `PreludeItem`, each followed by
a separator.  Any other class or trait is refused. -/
def pPrelude : Nat → Parser (List PreludeItem)
  | 0 => noFuel
  | n + 1 => do
    let t ← next
    match t.tok with
    | .kw "class" =>
      advance
      let (p, C) ← pName
      expectExtends classShape
      let (q, x) ← pName
      let P ← pDotted n x
      let item ←
        if P == "caps.SharedCapability" then pure (PreludeItem.capClass p C)
        else if P == x then pure (PreludeItem.platClass p C x)
        else refuse q classShape
      endItem classShape
      return item :: (← pPrelude n)
    | .kw "trait" =>
      advance
      let (p, K) ← pName
      expectExtends traitShape
      let (q, x) ← pName
      let P ← pDotted n x
      let c ← next
      if c.tok != .sym "," then refuse c.pos traitShape
      advance
      let (r, y) ← pName
      if (← pDotted n y) != "caps.Classifier" then refuse r traitShape
      let parent ←
        if P == "caps.SharedCapability" then pure none
        else if P == x then pure (some x)
        else refuse q traitShape
      endItem traitShape
      return .classifier p K parent :: (← pPrelude n)
    | _ => return []

/-- A platform parameter of `def program`, `x: C^`. -/
def pParam : Parser (Pos × String × String) := do
  let (p, x) ← pName
  expectSym ":"
  let (_, C) ← pName
  let t ← next
  if t.tok != .sym "^" then refuse t.pos "a platform parameter is `x: C^`"
  advance
  if (← sees (.sym "{")) then refuse t.pos "a platform parameter is `x: C^`, with no capture set"
  return (p, x, C)

/-- The platform parameters, one or more, separated by commas. -/
def pParams : Nat → Parser (List (Pos × String × String))
  | 0 => noFuel
  | n + 1 => do
    let x ← pParam
    if (← sees (.sym ",")) then
      advance
      return x :: (← pParams n)
    return [x]

/-- The name `program` after `val` or `def`. -/
def pProgramName : Parser Unit := do
  let (p, x) ← pName
  if x != "program" then refuse p ("the wrapper object holds `program`, found `" ++ x ++ "`")

/-- The program: `val program [: T] = e`, or `def program(x: C^, …) [: T] = e`
with the platform as its parameters.  An empty platform is `val program`. -/
def pProgram (n : Nat) :
    Parser (Option (List (Pos × String × String)) × Option Ty × Tm) := do
  let t ← next
  match t.tok with
  | .kw "val" =>
    advance
    pProgramName
    let T ← bound ":" (pType n)
    expectSym "="
    return (none, T, ← pExpr n)
  | .kw "def" =>
    advance
    pProgramName
    let u ← next
    match u.tok with
    | .sym "(" => advance
    | .sym "[" => refuse u.pos "type parameters are outside the subset"
    | _ => refuse u.pos "`def program` takes the platform as parameters: `def program(x: C^, …)`"
    let v ← next
    if v.tok == .sym ")" then refuse v.pos "an empty platform is `val program`"
    let ps ← pParams n
    expectSym ")"
    let w ← next
    if w.tok == .sym "(" then refuse w.pos "several parameter lists are outside the subset"
    let T ← bound ":" (pType n)
    expectSym "="
    return (some ps, T, ← pExpr n)
  | _ => expected "`val program` or `def program`"

/-- A file: the header imports, `object Name {`, the prelude, the program and
`}`, then nothing. -/
def pFile (n : Nat) : Parser Program := do
  let imports ← pImports n
  if !(← sees (.kw "object")) then expected "`object`"
  advance
  let (_, name) ← pName
  expectSym "{"
  let prelude ← pPrelude n
  let (params, ty, body) ← pProgram n
  let s ← next
  skipSeps
  let t ← next
  match t.tok with
  | .sym "}" => advance
  | .kw "class" | .kw "trait" => refuse t.pos "the prelude goes before the program"
  | _ =>
    if isSep s.tok then refuse t.pos "the wrapper object holds the prelude and one program"
    afterExpr "`}`"
  skipSeps
  if (← next).tok != .sym "" then expected "the end of the file"
  return { imports, name, prelude, params, ty, body }

/-- The position of the last token, or `1:1` for no token. -/
def lastPos : List Token → Pos
  | [] => ⟨1, 1⟩
  | [t] => t.pos
  | _ :: ts => lastPos ts

end Parse

open Parse in
/-- The program of a list of laid out tokens, or the first refusal.  The fuel
is `8 * n + 8` for `n` tokens: every call of the descent below one that has
fuel `k` has `k - 1`, and the descent is at most four calls deep per token it
has read. -/
def parseTokens (ts : List Token) : Except Err Program :=
  (pFile (8 * ts.length + 8)).run' (ts ++ [endTok (lastPos ts)])

/-- The program of the characters of a file, or the first refusal of the
lexer, the column rule or the parser. -/
def parseFile : List Char → Except Err Program := fun cs => tokens cs >>= parseTokens

end ScalaSyntax
