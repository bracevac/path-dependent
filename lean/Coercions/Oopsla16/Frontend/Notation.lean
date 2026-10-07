import Coercions.Oopsla16.Frontend.Surface

/-!
# The surface notation of the Oopsla16 front end

Three syntax categories, `o16Ty`, `o16Tm` and `o16Dm`, hold the paper's concrete
syntax.  Three term level entry points, `o16Ty%`, `o16%` and `o16Dm%`, expand a
piece of that syntax into a constructor application of `SType`, `STm`, `SDm` or
`SDms`.  Names stay strings here, as `Surface.lean` leaves them: no label is
looked up and no de Bruijn index is computed, which is the resolver's work.

## Precedences

`∧` is right leaning at 65 and `∨` is right leaning at 60, so `∧` binds tighter
and a mixed chain such as `⊤ ∧ ⊥ ∨ ⊤` reads `(⊤ ∧ ⊥) ∨ ⊤`.  A call on a
receiver that is itself a term, rather than a bare name, sits at 80, so a chain
`x.m(y).n(z)` keeps building on the previous call.  The closed forms and the
parenthesis forms sit at `max`.

## Dotted identifiers

Lean's lexer reads `x.m` as a single `ident` whose `Name` has two components,
exactly as the vanilla front end found for its own dotted names.  A method call
is therefore the rule `ident "(" o16Tm ")"`, and the macro splits the name into
a receiver and a method label.  A name of any other length is rejected where a
call or a selection needs exactly two parts: a bare variable accepts only one
part, and a type selection `x.L` accepts only two.  The trailing rule
`o16Tm:80 "." ident "(" o16Tm ")"` is for a receiver that is not itself a bare
name, for instance a literal directly followed by a call.

## No `let`

The surface term has no `let` former: an ascription is the only purely front
end construct, and it erases to its own subterm.  There is consequently no
`let` syntax here either, unlike the general shape of the paper's notation,
since there would be nothing for it to expand into.
-/

namespace Oopsla16Frontend

open Lean

/-! ## The three categories -/

declare_syntax_cat o16Ty
declare_syntax_cat o16Tm
declare_syntax_cat o16Dm

/-- `⊤`, the top type. -/
syntax:max "⊤" : o16Ty
/-- `⊥`, the bottom type. -/
syntax:max "⊥" : o16Ty
/-- `{type L : S..U}`, a type member declaration. -/
syntax:max "{" "type" ident " : " o16Ty ".." o16Ty "}" : o16Ty
/-- `{def m(x : S) : U}`, a method member declaration.  `U` may mention `x`. -/
syntax:max "{" "def" ident "(" ident " : " o16Ty ")" " : " o16Ty "}" : o16Ty
/-- `x.L`, a type selection.  One `ident`, split inside the macro. -/
syntax:max ident : o16Ty
/-- `μ(z. T)`, a recursive self type. -/
syntax:max "μ" "(" ident "." o16Ty ")" : o16Ty
/-- `S ∧ T`, an intersection, right leaning, binding tighter than `∨`. -/
syntax:65 o16Ty:66 " ∧ " o16Ty:65 : o16Ty
/-- `S ∨ T`, a union, right leaning. -/
syntax:60 o16Ty:61 " ∨ " o16Ty:60 : o16Ty
/-- Parentheses. -/
syntax:max "(" o16Ty ")" : o16Ty

/-- `x`, a bare variable.  One `ident` of a single part. -/
syntax:max ident : o16Tm
/-- `x.m(u)`, a method call on a named receiver.  One dotted `ident`, split
inside the macro, then the argument. -/
syntax:max ident "(" o16Tm ")" : o16Tm
/-- `t.m(u)` on a receiver that is not a bare name, for instance a literal. -/
syntax:80 o16Tm:80 "." ident "(" o16Tm ")" : o16Tm
/-- `new {z ⇒ d₁ … dₙ}`, an object literal with no written self type. -/
syntax:max "new" "{" ident " ⇒ " o16Dm* "}" : o16Tm
/-- `new {z : T ⇒ d₁ … dₙ}`, an object literal with its self type written. -/
syntax:max "new" "{" ident " : " o16Ty " ⇒ " o16Dm* "}" : o16Tm
/-- `(t : T)`, an ascription.  Front end only, it erases to `t`. -/
syntax:max "(" o16Tm " : " o16Ty ")" : o16Tm
/-- Parentheses. -/
syntax:max "(" o16Tm ")" : o16Tm

/-- `type L = T`, a type member definition. -/
syntax "type" ident " = " o16Ty : o16Dm
/-- `def m(x) = t`, a method with neither annotation. -/
syntax "def" ident "(" ident ")" " = " o16Tm : o16Dm
/-- `def m(x) : U = t`, a method annotated at its result only. -/
syntax "def" ident "(" ident ")" " : " o16Ty " = " o16Tm : o16Dm
/-- `def m(x : S) = t`, a method annotated at its parameter only. -/
syntax "def" ident "(" ident " : " o16Ty ")" " = " o16Tm : o16Dm
/-- `def m(x : S) : U = t`, a method annotated at both. -/
syntax "def" ident "(" ident " : " o16Ty ")" " : " o16Ty " = " o16Tm : o16Dm

/-- Expand an `o16Ty` into an `SType`. -/
syntax:max "o16Ty% " o16Ty : term
/-- Expand an `o16Tm` into an `STm`. -/
syntax:max "o16% " o16Tm : term
/-- Expand an `o16Dm` into an `SDm`. -/
syntax:max "o16Dm% " o16Dm : term

/-! ## Taking a dotted identifier apart

Splitting a name into its parts is one pure function, so the probes below test
the decision with `decide` like every other check in this module.  The two
`MacroM` wrappers only turn the answer into syntax, or report a bad name with
`Macro.throwErrorAt`, which points at the offending identifier. -/

/-- The components of a name, outermost first, as strings. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- The receiver and the label of a two part name.  A call and a type
selection each need exactly two parts, the one way this grammar builds a name
of more than one component. -/
def twoParts (n : Name) : Option (String × String) :=
  match nameParts n [] with
  | [recv, lbl] => some (recv, lbl)
  | _ => none

/-- A surface type built from a bare name is the selection `x.L`. -/
private def tyOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match twoParts x.getId with
  | some (r, l) => `(SType.sel $(quote r) $(quote l))
  | none =>
    Macro.throwErrorAt x
      "a surface type built from a name is the selection x.L, which has exactly two parts"

/-- A surface term built from a one part name is the variable `x`. -/
private def varOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match nameParts x.getId [] with
  | [v] => `(STm.var $(quote v))
  | _ =>
    Macro.throwErrorAt x
      "a bare surface name is the variable x; a dotted name needs a call, x.m(u)"

/-- A surface call built from a two part name is `x.m(u)`. -/
private def callOfIdent (x : Ident) (u : TSyntax `term) : MacroM (TSyntax `term) := do
  match twoParts x.getId with
  | some (r, m) => `(STm.call (STm.var $(quote r)) $(quote m) $u)
  | none =>
    Macro.throwErrorAt x
      "a surface call built from a name is x.m(u), which has exactly two parts"

/-- The label a surface `ident` carries, as a string literal. -/
private def str (x : Ident) : TSyntax `term := quote x.getId.toString

/-! ## The macros -/

macro_rules
  | `(o16Ty% ⊤) => `(SType.top)
  | `(o16Ty% ⊥) => `(SType.bot)
  | `(o16Ty% { type $L:ident : $S:o16Ty .. $U:o16Ty }) =>
      `(SType.typ $(str L) (o16Ty% $S) (o16Ty% $U))
  | `(o16Ty% { def $m:ident ( $x:ident : $S:o16Ty ) : $U:o16Ty }) =>
      `(SType.fn $(str m) $(str x) (o16Ty% $S) (o16Ty% $U))
  | `(o16Ty% $x:ident) => tyOfIdent x
  | `(o16Ty% μ ( $z:ident . $T:o16Ty )) => `(SType.mu $(str z) (o16Ty% $T))
  | `(o16Ty% $S:o16Ty ∧ $T:o16Ty) => `(SType.and (o16Ty% $S) (o16Ty% $T))
  | `(o16Ty% $S:o16Ty ∨ $T:o16Ty) => `(SType.or (o16Ty% $S) (o16Ty% $T))
  | `(o16Ty% ( $T:o16Ty )) => `(o16Ty% $T)

macro_rules
  | `(o16% $x:ident) => varOfIdent x
  | `(o16% $x:ident ( $u:o16Tm )) => do callOfIdent x (← `(o16% $u))
  | `(o16% $t:o16Tm . $m:ident ( $u:o16Tm )) => `(STm.call (o16% $t) $(str m) (o16% $u))
  | `(o16% new { $z:ident ⇒ $ds:o16Dm* }) => do
      let ds ← ds.mapM fun d => `(o16Dm% $d)
      let mut lit ← `(SDms.nil)
      for d in ds.reverse do
        lit ← `(SDms.cons $d $lit)
      `(STm.obj $(str z) none $lit)
  | `(o16% new { $z:ident : $T:o16Ty ⇒ $ds:o16Dm* }) => do
      let ds ← ds.mapM fun d => `(o16Dm% $d)
      let mut lit ← `(SDms.nil)
      for d in ds.reverse do
        lit ← `(SDms.cons $d $lit)
      `(STm.obj $(str z) (some (o16Ty% $T)) $lit)
  | `(o16% ( $t:o16Tm : $T:o16Ty )) => `(STm.asc (o16% $t) (o16Ty% $T))
  | `(o16% ( $t:o16Tm )) => `(o16% $t)

macro_rules
  | `(o16Dm% type $L:ident = $T:o16Ty) => `(SDm.typ $(str L) (o16Ty% $T))
  | `(o16Dm% def $m:ident ( $x:ident ) = $t:o16Tm) =>
      `(SDm.fn $(str m) $(str x) none none (o16% $t))
  | `(o16Dm% def $m:ident ( $x:ident ) : $U:o16Ty = $t:o16Tm) =>
      `(SDm.fn $(str m) $(str x) none (some (o16Ty% $U)) (o16% $t))
  | `(o16Dm% def $m:ident ( $x:ident : $S:o16Ty ) = $t:o16Tm) =>
      `(SDm.fn $(str m) $(str x) (some (o16Ty% $S)) none (o16% $t))
  | `(o16Dm% def $m:ident ( $x:ident : $S:o16Ty ) : $U:o16Ty = $t:o16Tm) =>
      `(SDm.fn $(str m) $(str x) (some (o16Ty% $S)) (some (o16Ty% $U)) (o16% $t))

/-! ## One check per surface form

Every one of these reduces in the kernel, so `by decide` is the right tactic,
as it is in `Surface.lean`. -/

/-! ### Types -/

example : (o16Ty% ⊤) = SType.top := by decide
example : (o16Ty% ⊥) = SType.bot := by decide
example : (o16Ty% { type A : ⊥ .. ⊤ }) = SType.typ "A" .bot .top := by decide
example : (o16Ty% { def f(x : ⊤) : ⊥ }) = SType.fn "f" "x" .top .bot := by decide
example : (o16Ty% x.A) = SType.sel "x" "A" := by decide
example : (o16Ty% μ(z. { def f(x : ⊤) : z.B })) =
    SType.mu "z" (.fn "f" "x" .top (.sel "z" "B")) := by decide
example : (o16Ty% ⊤ ∧ ⊥) = SType.and .top .bot := by decide
/-- `∧` leans right. -/
example : (o16Ty% ⊤ ∧ ⊥ ∧ ⊤) = SType.and .top (.and .bot .top) := by decide
example : (o16Ty% ⊤ ∨ ⊥) = SType.or .top .bot := by decide
/-- `∧` binds tighter than `∨`, so it groups to the left operand first. -/
example : (o16Ty% ⊤ ∧ ⊥ ∨ ⊤) = SType.or (.and .top .bot) .top := by decide
example : (o16Ty% ( ⊤ )) = SType.top := by decide
/-- A parenthesis regroups an intersection to the left. -/
example : (o16Ty% ( ⊤ ∧ ⊥ ) ∧ ⊤) = SType.and (.and .top .bot) .top := by decide

/-! ### Terms -/

example : (o16% x) = STm.var "x" := by decide
example : (o16% x.m(y)) = STm.call (.var "x") "m" (.var "y") := by decide
/-- A chain of calls keeps building on the previous one. -/
example : (o16% x.m(y).n(z)) = STm.call (.call (.var "x") "m" (.var "y")) "n" (.var "z") := by
  decide
/-- A call whose receiver is a literal, not a bare name, goes through the
trailing rule. -/
example : (o16% (new { z ⇒ }).m(y)) = STm.call (.obj "z" none .nil) "m" (.var "y") := by decide
example : (o16% new { z ⇒ }) = STm.obj "z" none .nil := by decide
example : (o16% new { z ⇒ type B = ⊤ def f(y) = y }) =
    STm.obj "z" none (.cons (.typ "B" .top) (.cons (.fn "f" "y" none none (.var "y")) .nil)) := by
  decide
example : (o16% new { z : { def f(x : ⊤) : ⊤ } ⇒ def f(x) = x }) =
    STm.obj "z" (some (.fn "f" "x" .top .top)) (.cons (.fn "f" "x" none none (.var "x")) .nil) := by
  decide
example : (o16% (x : ⊤)) = STm.asc (.var "x") .top := by decide
example : (o16% ( x )) = STm.var "x" := by decide

/-! ### Member definitions -/

example : (o16Dm% type A = ⊤) = SDm.typ "A" .top := by decide
example : (o16Dm% def f(x) = x) = SDm.fn "f" "x" none none (.var "x") := by decide
example : (o16Dm% def f(x) : ⊤ = x) = SDm.fn "f" "x" none (some .top) (.var "x") := by decide
example : (o16Dm% def f(x : ⊥) = x) = SDm.fn "f" "x" (some .bot) none (.var "x") := by decide
example : (o16Dm% def f(x : ⊥) : ⊤ = x) = SDm.fn "f" "x" (some .bot) (some .top) (.var "x") := by
  decide

/-! ### Names

The decision each category makes about a name is tested at the decision
itself, which is a plain function and reduces like everything else here. -/

example : twoParts `x = none := by decide
example : twoParts `x.A = some ("x", "A") := by decide
example : twoParts `x.a.A = none := by decide
example : nameParts `x [] = ["x"] := by decide
example : nameParts `x.a [] = ["x", "a"] := by decide
example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ## The version's examples, in the notation

`FunctionField`, the two self types. -/

/-- `S(z)`. -/
def Sbody : SType := o16Ty% { type A : ⊥ .. z.B } ∧ { type B : ⊥ .. ⊤ } ∧ { def f(x : ⊤) : z.A }
/-- `T(z)`. -/
def Tbody : SType := o16Ty% { def f(x : ⊤) : z.B }

example : Sbody = .and (.typ "A" .bot (.sel "z" "B"))
    (.and (.typ "B" .bot .top) (.fn "f" "x" .top (.sel "z" "A"))) := by decide
example : Tbody = SType.fn "f" "x" .top (.sel "z" "B") := by decide

/-- `ex0`, the empty object. -/
def ex0src : STm := o16% new { z ⇒ }
/-- `ex0`, ascribed at `⊤`. -/
def ex0AscSrc : STm := o16% (new { z ⇒ } : ⊤)

example : ex0src = STm.obj "z" none .nil := by decide
example : ex0AscSrc = STm.asc (.obj "z" none .nil) .top := by decide

/-- `RecursiveArg.prog`: a Curry style caller applied to a Curry style
argument.  Both literals carry a self type, since both methods are Curry
style. -/
def recArgSrc : STm :=
  o16% (new { c : { def apply(x : μ(z. { def f(y : ⊤) : z.B })) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = y }).apply(
         new { z : { type A : z.B .. z.B } ∧ { type B : ⊤ .. ⊤ } ∧ { def f(y : ⊤) : z.A } ∧ ⊤ ⇒
              type A = z.B
              type B = ⊤
              def f(y) = y })

example : recArgSrc =
    .call
      (.obj "c"
        (some (.and (.fn "apply" "x" (.mu "z" (.fn "f" "y" .top (.sel "z" "B"))) .top) .top))
        (.cons (.fn "apply" "y" none none (.var "y")) .nil))
      "apply"
      (.obj "z"
        (some (.and (.typ "A" (.sel "z" "B") (.sel "z" "B"))
                (.and (.typ "B" .top .top)
                  (.and (.fn "f" "y" .top (.sel "z" "A")) .top))))
        (.cons (.typ "A" (.sel "z" "B"))
          (.cons (.typ "B" .top)
            (.cons (.fn "f" "y" none none (.var "y")) .nil)))) := by
  decide

/-- `polyId`. -/
def polyId : SType :=
  o16Ty% { def apply(t : { type T : ⊥ .. ⊤ }) : { def apply(x : t.T) : t.T } }

example : polyId =
    SType.fn "apply" "t" (.typ "T" .bot .top)
      (.fn "apply" "x" (.sel "t" "T") (.sel "t" "T")) := by decide

/-- `ex1`'s term, fully annotated, so no self type is needed. -/
def ex1src : STm :=
  o16% new { o ⇒ def apply(t : { type T : ⊥ .. ⊤ }) : { def apply(x : t.T) : t.T } =
                  new { p ⇒ def apply(x : t.T) : t.T = x } }

example : ex1src =
    STm.obj "o" none
      (.cons (.fn "apply" "t"
          (some (.typ "T" .bot .top))
          (some (.fn "apply" "x" (.sel "t" "T") (.sel "t" "T")))
          (.obj "p" none
            (.cons (.fn "apply" "x" (some (.sel "t" "T")) (some (.sel "t" "T")) (.var "x"))
              .nil)))
        .nil) := by
  decide

/-- `ex2`'s term, open in `y : polyId`. -/
def ex2src : STm := o16% y.apply(new { o ⇒ type T = ⊤ })

example : ex2src =
    STm.call (.var "y") "apply" (.obj "o" none (.cons (.typ "T" .top) .nil)) := by decide

/-- A literal written twice in `CurryCall.prog`, once as the method's own
call and once as the outer argument.  Both occurrences are the same surface
value. -/
private def curryInnerObjSrc : STm :=
  o16% new { i : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒ def apply(y) = y }

/-- `CurryCall.prog`. -/
def curryCallSrc : STm :=
  o16% (new { c : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = (new { i : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒ def apply(y) = y }).apply(y) }).apply(
         new { i : { def apply(y : ⊤) : ⊤ } ∧ ⊤ ⇒ def apply(y) = y })

private def curryInnerObjHand : STm :=
  .obj "i" (some (.and (.fn "apply" "y" .top .top) .top))
    (.cons (.fn "apply" "y" none none (.var "y")) .nil)

example : curryInnerObjSrc = curryInnerObjHand := by decide

example : curryCallSrc =
    .call
      (.obj "c" (some (.and (.fn "apply" "y" .top .top) .top))
        (.cons (.fn "apply" "y" none none
            (.call curryInnerObjHand "apply" (.var "y")))
          .nil))
      "apply"
      curryInnerObjHand := by
  decide

/-- The self type of `List`, the module's recursive type. -/
private def paperListTy : SType :=
  .mu "this"
    (.and (.fn "head" "u" .top (.sel "this" "Elem"))
      (.and (.fn "tail" "u" .top (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "this" "Elem"))))
        (.typ "Elem" .bot .top)))

/-- The `nil` cell's body: both methods call themselves on their argument,
since `nil` never answers either one. -/
private def paperNilBody : STm :=
  .obj "this" none
    (.cons (.fn "head" "u" (some .top) (some .bot) (.call (.var "this") "head" (.var "u")))
      (.cons (.fn "tail" "u" (some .top) (some .bot) (.call (.var "this") "tail" (.var "u")))
        (.cons (.typ "Elem" .bot) .nil)))

/-- The innermost cell a `cons` call builds, once it holds both the head and
the tail it was given. -/
private def paperConsInnerBody : STm :=
  .obj "this" none
    (.cons (.fn "head" "u" (some .top) (some (.sel "t" "T")) (.var "hd"))
      (.cons (.fn "tail" "u" (some .top)
                (some (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T")))) (.var "tl"))
        (.cons (.typ "Elem" (.sel "t" "T")) .nil)))

/-- `cons`'s second curried layer, taking the tail. -/
private def paperConsO2Body : STm :=
  .obj "o2" none
    (.cons (.fn "apply" "tl"
        (some (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T"))))
        (some (.and (.sel "m" "List") (.typ "Elem" (.sel "t" "T") (.sel "t" "T"))))
        paperConsInnerBody)
      .nil)

/-- `cons`'s first curried layer, taking the head. -/
private def paperConsO1Body : STm :=
  .obj "o1" none
    (.cons (.fn "apply" "hd"
        (some (.sel "t" "T"))
        (some (.fn "apply" "tl"
                (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T")))
                (.and (.sel "m" "List") (.typ "Elem" (.sel "t" "T") (.sel "t" "T")))))
        paperConsO2Body)
      .nil)

/-- `cons`'s own written result type, the type its body is checked at. -/
private def paperConsResultTy : SType :=
  .fn "apply" "hd" (.sel "t" "T")
    (.fn "apply" "tl" (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T")))
      (.and (.sel "m" "List") (.typ "Elem" (.sel "t" "T") (.sel "t" "T"))))

/-- `cons`'s entry in the module's own ascribed type, weaker than the body's
own result type at the innermost bound. -/
private def paperModuleConsTy : SType :=
  .fn "apply" "hd" (.sel "t" "T")
    (.fn "apply" "tl" (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T")))
      (.and (.sel "m" "List") (.typ "Elem" .bot (.sel "t" "T"))))

/-- The module's own ascribed type. -/
private def paperModuleTy : SType :=
  .mu "m"
    (.and (.fn "nil" "u" .top (.and (.sel "m" "List") (.typ "Elem" .bot .bot)))
      (.and (.fn "cons" "t" (.typ "T" .bot .top) paperModuleConsTy)
        (.typ "List" .bot paperListTy)))

/-- `paper_lst`, the list module of the paper, ascribed at its own module
type.  Every method is annotated, so no literal needs a self type. -/
def paperLstSrc : STm :=
  o16% (new { m ⇒
    def nil(u : ⊤) : m.List ∧ { type Elem : ⊥ .. ⊥ } =
      new { this ⇒ def head(u : ⊤) : ⊥ = this.head(u)
                  def tail(u : ⊤) : ⊥ = this.tail(u)
                  type Elem = ⊥ }
    def cons(t : { type T : ⊥ .. ⊤ }) :
        { def apply(hd : t.T) : { def apply(tl : m.List ∧ { type Elem : ⊥ .. t.T }) :
                                  m.List ∧ { type Elem : t.T .. t.T } } } =
      new { o1 ⇒ def apply(hd : t.T) : { def apply(tl : m.List ∧ { type Elem : ⊥ .. t.T }) :
                                           m.List ∧ { type Elem : t.T .. t.T } } =
        new { o2 ⇒ def apply(tl : m.List ∧ { type Elem : ⊥ .. t.T }) : m.List ∧ { type Elem : t.T .. t.T } =
          new { this ⇒ def head(u : ⊤) : t.T = hd
                      def tail(u : ⊤) : m.List ∧ { type Elem : ⊥ .. t.T } = tl
                      type Elem = t.T } } }
    type List = μ(this. { def head(u : ⊤) : this.Elem }
                      ∧ { def tail(u : ⊤) : m.List ∧ { type Elem : ⊥ .. this.Elem } }
                      ∧ { type Elem : ⊥ .. ⊤ }) }
    : μ(m. { def nil(u : ⊤) : m.List ∧ { type Elem : ⊥ .. ⊥ } }
         ∧ { def cons(t : { type T : ⊥ .. ⊤ }) :
              { def apply(hd : t.T) : { def apply(tl : m.List ∧ { type Elem : ⊥ .. t.T }) :
                                        m.List ∧ { type Elem : ⊥ .. t.T } } } }
         ∧ { type List : ⊥ .. μ(this. { def head(u : ⊤) : this.Elem }
                                   ∧ { def tail(u : ⊤) : m.List ∧ { type Elem : ⊥ .. this.Elem } }
                                   ∧ { type Elem : ⊥ .. ⊤ }) }))

example : paperLstSrc =
    .asc
      (.obj "m" none
        (.cons (.fn "nil" "u" (some .top)
                  (some (.and (.sel "m" "List") (.typ "Elem" .bot .bot))) paperNilBody)
          (.cons (.fn "cons" "t" (some (.typ "T" .bot .top)) (some paperConsResultTy)
                    paperConsO1Body)
            (.cons (.typ "List" paperListTy) .nil))))
      paperModuleTy := by
  decide

end Oopsla16Frontend
