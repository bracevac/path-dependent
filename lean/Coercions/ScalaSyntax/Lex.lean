/-!
# Tokens and the column rule

The first stage of the Scala reader.  `lex` turns the characters of a file
into tokens with their positions, and refuses, at its position, every
character and word that the subset leaves out.  `layout` checks how the lines
are laid out and inserts a `sep` where a line break ends a statement.
`tokens` runs the two in turn.

Braces alone do not turn off Scala 3's indentation rules, so the column rule
of plan IX (S-10) admits only layouts that scalac reads alike with and
without `-no-indent`.  Inside braces, statements start on their own lines at
one column or share a line separated by `;`.  A statement continues on a
later line only after a token that cannot end it, and a line may start with
`}` or `)` anywhere.

Every function is structural, on the list it walks or on a fuel of at most
the length of the input plus one, so the kernel reduces the reader on the
characters of a file.  Nothing here reads a `String` character by character,
since `String.toList` depends on `Classical.choice` in Lean v4.29.1.  Names
are built with `String.ofList`, and characters are compared one by one.

This module imports Lean core only.
-/

namespace ScalaSyntax

/-! ## Positions, refusals, tokens -/

/-- A position in a file, a 1-based line and a 1-based column. -/
structure Pos where
  line : Nat
  col : Nat
deriving DecidableEq, Repr

/-- A refusal of the reader: where, and the reason. -/
structure Err where
  pos : Pos
  msg : String
deriving DecidableEq, Repr

/-- A token of the subset. -/
inductive Tok where
  /-- A name: a letter, then letters, digits and `_`.  `upper` is the case of
  the first letter, so no later stage needs the characters of the name. -/
  | ident (s : String) (upper : Bool)
  /-- A word of the subset: `import`, `object`, `val`, `def`, `type`, `new`,
  `this`, `class`, `trait`, `extends`. -/
  | kw (s : String)
  /-- Any other hard or soft keyword of Scala 3.  The parser refuses it. -/
  | reserved (s : String)
  /-- A delimiter or one of the operators of the subset. -/
  | sym (s : String)
  /-- A line break that ends a statement, inserted by `layout`. -/
  | sep
deriving DecidableEq, Repr

/-- A token, its position, and whether it is the first token of its line.  A
`sep` carries the position of the token it stands before. -/
structure Token where
  tok : Tok
  pos : Pos
  first : Bool
deriving DecidableEq, Repr

/-- The position `n` columns to the right. -/
def Pos.right (p : Pos) (n : Nat) : Pos := ⟨p.line, p.col + n⟩

/-- The position after the character `c`. -/
def Pos.adv (p : Pos) (c : Char) : Pos :=
  if c == '\n' then ⟨p.line + 1, 1⟩ else p.right 1

/-! ## Characters

Each class is spelled out, character by character. -/

/-- A character that Scala reads into a name: an ASCII letter, a digit, `_`
or `$`.  The subset refuses `$` later, with the name it occurs in. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- One of Scala's ASCII operator characters. -/
def isOpChar (c : Char) : Bool :=
  c == '!' || c == '#' || c == '%' || c == '&' || c == '*' || c == '+' || c == '-' ||
  c == '/' || c == ':' || c == '<' || c == '=' || c == '>' || c == '?' || c == '@' ||
  c == '\\' || c == '^' || c == '|' || c == '~'

/-- The token of a delimiter character. -/
def delimSym : Char → Option String
  | '{' => some "{"
  | '}' => some "}"
  | '(' => some "("
  | ')' => some ")"
  | '[' => some "["
  | ']' => some "]"
  | ',' => some ","
  | ';' => some ";"
  | '.' => some "."
  | _ => none

/-- The operators of the subset.  Any other run of operator characters is
refused. -/
def opSym : List Char → Option String
  | [':'] => some ":"
  | ['='] => some "="
  | ['=', '>'] => some "=>"
  | ['-', '>'] => some "->"
  | ['&'] => some "&"
  | ['^'] => some "^"
  | ['<', ':'] => some "<:"
  | ['>', ':'] => some ">:"
  | _ => none

/-- How a word reads: a word of the subset, a word Scala reserves, or a
name. -/
inductive Word where
  /-- A word of the subset, a `Tok.kw`. -/
  | kw
  /-- A hard or soft keyword of Scala 3 outside the subset, a `Tok.reserved`. -/
  | reserved
  /-- Any other word, a `Tok.ident`. -/
  | name

/-- The words of the subset, then the hard keywords of Scala 3 (with
`forSome` and `macro`, which its scanner still reserves), then its soft
keywords. -/
def wordOf : List Char → Word
  | ['i','m','p','o','r','t'] | ['o','b','j','e','c','t'] | ['v','a','l'] | ['d','e','f']
  | ['t','y','p','e'] | ['n','e','w'] | ['t','h','i','s'] | ['c','l','a','s','s']
  | ['t','r','a','i','t'] | ['e','x','t','e','n','d','s'] => .kw
  | ['a','b','s','t','r','a','c','t'] | ['c','a','s','e'] | ['c','a','t','c','h'] | ['d','o']
  | ['e','l','s','e'] | ['e','n','u','m'] | ['e','x','p','o','r','t'] | ['f','a','l','s','e']
  | ['f','i','n','a','l'] | ['f','i','n','a','l','l','y'] | ['f','o','r']
  | ['f','o','r','S','o','m','e'] | ['g','i','v','e','n'] | ['i','f']
  | ['i','m','p','l','i','c','i','t'] | ['l','a','z','y'] | ['m','a','c','r','o']
  | ['m','a','t','c','h'] | ['n','u','l','l'] | ['o','v','e','r','r','i','d','e']
  | ['p','a','c','k','a','g','e'] | ['p','r','i','v','a','t','e']
  | ['p','r','o','t','e','c','t','e','d'] | ['r','e','t','u','r','n'] | ['s','e','a','l','e','d']
  | ['s','u','p','e','r'] | ['t','h','e','n'] | ['t','h','r','o','w'] | ['t','r','u','e']
  | ['t','r','y'] | ['v','a','r'] | ['w','h','i','l','e'] | ['w','i','t','h']
  | ['y','i','e','l','d'] => .reserved
  | ['a','s'] | ['d','e','r','i','v','e','s'] | ['e','n','d'] | ['e','x','t','e','n','s','i','o','n']
  | ['i','n','f','i','x'] | ['i','n','l','i','n','e'] | ['o','p','a','q','u','e'] | ['o','p','e','n']
  | ['t','r','a','n','s','p','a','r','e','n','t'] | ['u','s','i','n','g'] => .reserved
  | _ => .name

/-! ## Runs of characters -/

/-- The longest prefix of name characters, and the rest. -/
def takeName : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isNameChar c then
      match takeName cs with
      | (a, r) => (c :: a, r)
    else ([], c :: cs)

/-- The longest prefix of operator characters, and the rest.  As in Scala, a
`/` that starts a comment ends the operator. -/
def takeOp : List Char → List Char × List Char
  | [] => ([], [])
  | '/' :: '/' :: cs => ([], '/' :: '/' :: cs)
  | '/' :: '*' :: cs => ([], '/' :: '*' :: cs)
  | c :: cs =>
    if isOpChar c then
      match takeOp cs with
      | (a, r) => (c :: a, r)
    else ([], c :: cs)

/-- Whether the characters start with an operator character that Scala would
read into a name ending in `_`. -/
def joinsOp : List Char → Bool
  | '/' :: '/' :: _ => false
  | '/' :: '*' :: _ => false
  | c :: _ => isOpChar c
  | [] => false

/-- The characters after a `//` comment, from its line break on, and the
position of that line break. -/
def skipLine : List Char → Pos → List Char × Pos
  | [], p => ([], p)
  | '\n' :: cs, p => ('\n' :: cs, p)
  | _ :: cs, p => skipLine cs (p.right 1)

/-- The characters after a block comment whose opening `/*` has been read, and
the position after its closing `*/`.  Block comments nest, and `d` counts the
open ones inside the first.  `none` when the comment is never closed. -/
def skipBlock : Nat → List Char → Pos → Option (List Char × Pos)
  | _, [], _ => none
  | 0, '*' :: '/' :: cs, p => some (cs, p.right 2)
  | d + 1, '*' :: '/' :: cs, p => skipBlock d cs (p.right 2)
  | d, '/' :: '*' :: cs, p => skipBlock (d + 1) cs (p.right 2)
  | d, c :: cs, p => skipBlock d cs (p.adv c)

/-! ## The lexer -/

/-- The token of a word `w` that starts at `p`, with the characters after
it.  Scala reads `$` as a letter and a name ending in `_` together with the
operator after it, so both are refused here. -/
def word (w rest : List Char) (p : Pos) : Except Err (Tok × List Char × Pos) :=
  if w.contains '$' then .error ⟨p, "names with `$` are outside the subset"⟩
  else
    match w with
    | ['_'] => .error ⟨p, "placeholders are outside the subset"⟩
    | '_' :: _ => .error ⟨p, "names that start with `_` are outside the subset"⟩
    | c :: _ =>
      if w.getLast? == some '_' && joinsOp rest then
        .error ⟨p, "a name ending in `_` takes the operator after it in Scala: put a space between them"⟩
      else
        let s := String.ofList w
        let t := match wordOf w with
          | .kw => Tok.kw s
          | .reserved => Tok.reserved s
          | .name => Tok.ident s c.isUpper
        .ok (t, rest, p.right w.length)
    | [] => .error ⟨p, "empty name"⟩

/-- The token that starts with the character `c` at `p`, the characters after
it, and the position after it.  Spaces, line breaks and comments are read by
`lexF`. -/
def lexOne (c : Char) (cs : List Char) (p : Pos) : Except Err (Tok × List Char × Pos) :=
  if c == '\t' then .error ⟨p, "tabs are outside the subset"⟩
  else if c.toNat > 127 then .error ⟨p, "non-ASCII characters are outside the subset"⟩
  else if c.toNat < 32 || c.toNat == 127 then .error ⟨p, "control characters are outside the subset"⟩
  else if c.isDigit then .error ⟨p, "number literals are outside the subset"⟩
  else if c == '"' || c == '\'' then .error ⟨p, "string and character literals are outside the subset"⟩
  else if c == '`' then .error ⟨p, "backquoted names are outside the subset"⟩
  else if isNameChar c then
    match takeName cs with
    | (more, rest) => word (c :: more) rest p
  else
    match delimSym c with
    | some s => .ok (.sym s, cs, p.right 1)
    | none =>
      match takeOp cs with
      | (more, rest) =>
        match opSym (c :: more) with
        | some s => .ok (.sym s, rest, p.right (more.length + 1))
        | none => .error ⟨p, "operator `" ++ String.ofList (c :: more) ++ "` is outside the subset"⟩

/-- The tokens of `cs`, which starts at `p`.  `bol` holds while no token has
been read on the current line, and `dirty` once a comment has been skipped on
it.  Every step reads at least one character, so a fuel of the length plus
one suffices.

scalac measures the indentation of a line by the spaces before its first
character, even when that is a comment, so a token after a comment cannot
start a line here (probe `LayG`). -/
def lexF : Nat → List Char → Pos → Bool → Bool → Except Err (List Token)
  | 0, _, p, _, _ => .error ⟨p, "the lexer ran out of fuel"⟩
  | _ + 1, [], _, _, _ => .ok []
  | n + 1, '\n' :: cs, p, _, _ => lexF n cs ⟨p.line + 1, 1⟩ true false
  | n + 1, '\r' :: '\n' :: cs, p, _, _ => lexF n cs ⟨p.line + 1, 1⟩ true false
  | n + 1, ' ' :: cs, p, bol, dirty => lexF n cs (p.right 1) bol dirty
  | n + 1, '/' :: '/' :: cs, p, bol, _ =>
    match skipLine cs (p.right 2) with
    | (rest, q) => lexF n rest q bol true
  | n + 1, '/' :: '*' :: cs, p, bol, _ =>
    match skipBlock 0 cs (p.right 2) with
    | some (rest, q) => lexF n rest q (bol || q.line != p.line) true
    | none => .error ⟨p, "unclosed comment"⟩
  | n + 1, c :: cs, p, bol, dirty =>
    match lexOne c cs p with
    | .error e => .error e
    | .ok (t, rest, q) =>
      if bol && dirty then
        .error ⟨p, "a comment before the first token of a line is outside the subset"⟩
      else
        match lexF n rest q false false with
        | .error e => .error e
        | .ok ts => .ok (⟨t, p, bol⟩ :: ts)

/-- The tokens of a file, without `sep`s. -/
def lex (cs : List Char) : Except Err (List Token) :=
  lexF (cs.length + 1) cs ⟨1, 1⟩ true false

/-! ## The column rule

A region is the file's top level, at column 1, or the inside of a `{`.  A
`{` whose `}` is on its line is a one-line region, and its statements are
separated by `;` only.  Otherwise its first statement starts the next line,
and that line's column is the region's column `c`.

In a region at column `c`, outside any nested bracket, a line at column `c`
begins a statement, a line further right continues one, and a line further
left must start with the `}` that closes the region.  Inside `(` or `[` line
breaks insert nothing.

Two refinements of plan IX (S-10), each from a probe that scalac reads
differently in its two layout modes.  A continuation line may not go left of
an earlier continuation line of its statement (`LayI`, `LayJ`): after `=` or
`=>` scalac opens an indented region there, and a line further left closes
it.  A `;` may not end a statement on a continuation line (`LayN`): scalac
reads what follows into the indented region. -/

/-- An open bracket, innermost first on the stack.  The bottom is `file`. -/
inductive Open where
  /-- The file's top level, a region at column 1.  `f` is the column of the
  last continuation line of the current statement, or 1 on its first line. -/
  | file (f : Nat)
  /-- A `{` whose region spans lines: its position, the region's column `c`,
  and `f` as for `file`. -/
  | block (p : Pos) (c f : Nat)
  /-- A `{` whose region is one line: its position, and the position of the
  first token after it. -/
  | line (p q : Pos)
  /-- A `(`, or a `[` when `square` holds. -/
  | paren (p : Pos) (square : Bool)

/-- The tokens after which the next line may continue a statement.  None of
them can end a statement. -/
def continues : Tok → Bool
  | .sym "=" | .sym "=>" | .sym "->" | .sym "(" | .sym "{" | .sym "," | .sym ":" | .sym "&"
  | .sym "<:" | .sym ">:" => true
  | _ => false

/-- A token that may start a line at any column. -/
def closesLine : Tok → Bool
  | .sym "}" | .sym ")" => true
  | _ => false

/-- Whether a statement that starts after `prev` gets a `sep`: not at the
start of the file or of a region, and not after a `;`, which already
separates it, as in scalac. -/
def sepAfter : Option Tok → Bool
  | none => false
  | some (.sym "{") => false
  | some (.sym ";") => false
  | some _ => true

/-- The first token after the innermost open one-line `{`, if any. -/
def oneLine? : List Open → Option Pos
  | [] => none
  | .line _ q :: _ => some q
  | _ :: stk => oneLine? stk

/-- A line that starts with `t`, after the token `prev`, in a region at column
`c` whose current statement's last continuation line is at `f`.  Returns the
new `f`, and whether the line begins a statement.  A statement's first line is
at `c`, so a continuation line at or right of `f` is also indented further
than the first line of its statement. -/
def regionLine (t : Token) (prev : Option Tok) (c f : Nat) : Except Err (Nat × Bool) :=
  if closesLine t.tok then .ok (f, false)
  else if t.pos.col == c then .ok (c, true)
  else if t.pos.col < c then .error ⟨t.pos, "line is indented too far to the left"⟩
  else if !(prev.map continues).getD false then
    .error ⟨t.pos, "a continuation line must follow one of = => -> ( { , : & <: >:"⟩
  else if t.pos.col < f then
    .error ⟨t.pos, "a continuation line must be indented at least as far as the continuation line before it"⟩
  else .ok (t.pos.col, false)

/-- The column rule at a token `t` that starts its line, after the token
`prev`: the new stack, and whether `t` begins a statement. -/
def lineStart (t : Token) (prev : Option Tok) (stk : List Open) :
    Except Err (List Open × Bool) :=
  match oneLine? stk with
  | some q => .error ⟨q, "the first statement after `{` goes on the next line, indented"⟩
  | none =>
    match stk with
    | .file f :: rest =>
      match regionLine t prev 1 f with
      | .ok (f', b) => .ok (.file f' :: rest, b)
      | .error e => .error e
    | .block p c f :: rest =>
      match regionLine t prev c f with
      | .ok (f', b) => .ok (.block p c f' :: rest, b)
      | .error e => .error e
    | _ => .ok (stk, false)

/-- The closing symbol of a `paren`. -/
def closer (square : Bool) : String := if square then "]" else ")"

/-- The stack after a closing symbol `s` at `p`, which must match the
innermost open bracket. -/
def close (s : String) (p : Pos) (stk : List Open) : Except Err (List Open) :=
  match stk with
  | .block .. :: rest | .line .. :: rest =>
    if s == "}" then .ok rest else .error ⟨p, "expected `}`, found `" ++ s ++ "`"⟩
  | .paren _ sq :: rest =>
    if s == closer sq then .ok rest else .error ⟨p, "expected `" ++ closer sq ++ "`, found `" ++ s ++ "`"⟩
  | _ => .error ⟨p, "unmatched `" ++ s ++ "`"⟩

/-- The stack after the token `t`.  `next` is the token after it, which tells
a one-line `{` from one that spans lines, and `lc` is the column of the first
token of `t`'s line.  The first statement of a `{` that spans lines must lie
right of the indentation of that line, the spaces before its first token. -/
def bracket (t : Token) (next : Option Token) (lc : Nat) (stk : List Open) :
    Except Err (List Open) :=
  match t.tok with
  | .sym "{" =>
    match next with
    | none => .ok (.line t.pos t.pos :: stk)
    | some u =>
      if u.first then
        if u.pos.col < lc && !closesLine u.tok then
          .error ⟨u.pos, "the first statement after `{` goes on the next line, indented"⟩
        else .ok (.block t.pos u.pos.col u.pos.col :: stk)
      else .ok (.line t.pos u.pos :: stk)
  | .sym "(" => .ok (.paren t.pos false :: stk)
  | .sym "[" => .ok (.paren t.pos true :: stk)
  | .sym "}" => close "}" t.pos stk
  | .sym ")" => close ")" t.pos stk
  | .sym "]" => close "]" t.pos stk
  | .sym ";" =>
    let onCont := match stk with
      | .file f :: _ => decide (1 < f)
      | .block _ c f :: _ => decide (c < f)
      | _ => false
    if onCont then
      .error ⟨t.pos, "`;` on a continuation line is outside the subset: start the next statement on its own line"⟩
    else .ok stk
  | _ => .ok stk

/-- The innermost bracket still open at the end of the file. -/
def unclosed : List Open → Option Err
  | .block p .. :: _ | .line p _ :: _ => some ⟨p, "`{` is never closed"⟩
  | .paren p sq :: _ => some ⟨p, (if sq then "`[`" else "`(`") ++ " is never closed"⟩
  | _ => none

/-- The column rule over `ts`, with the stack `stk`, the token `prev` before
`ts`, and the column `lc` of the first token of the current line. -/
def layoutGo : List Token → List Open → Option Tok → Nat → Except Err (List Token)
  | [], stk, _, _ =>
    match unclosed stk with
    | some e => .error e
    | none => .ok []
  | t :: ts, stk, prev, lc =>
    match (if t.first then lineStart t prev stk else .ok (stk, false)) with
    | .error e => .error e
    | .ok (stk', begins) =>
      let lc' := if t.first then t.pos.col else lc
      match bracket t ts.head? lc' stk' with
      | .error e => .error e
      | .ok stk'' =>
        match layoutGo ts stk'' (some t.tok) lc' with
        | .error e => .error e
        | .ok rest =>
          if begins && sepAfter prev then .ok (⟨.sep, t.pos, false⟩ :: t :: rest)
          else .ok (t :: rest)

/-- The column rule of plan IX (S-10): the tokens with a `sep` before every
line that starts a statement, except the first of the file or of a region and
a line after `;`, or the first line that breaks the rule. -/
def layout (ts : List Token) : Except Err (List Token) :=
  layoutGo ts [.file 1] none 0

/-- The tokens of a file, laid out by the column rule. -/
def tokens (cs : List Char) : Except Err (List Token) :=
  lex cs >>= layout

end ScalaSyntax
