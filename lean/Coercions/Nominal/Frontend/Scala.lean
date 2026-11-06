import Coercions.Nominal.Frontend.Pipeline
import Coercions.Nominal.Frontend.ScalaRead.Scope
import Coercions.Nominal.Frontend.ScalaRead.Print
import Coercions.Nominal.Frontend.ScalaClasses

/-!
# Scala programs in the pDOT front end

The reader of `Nominal/Frontend/ScalaRead/` turns the characters of a `.scala` file into a `File` and
checks its names and scopes.  This module maps that tree to the surface syntax of the pDOT front end,
an `STm` (plan XI, "The Scala mapping, one case per construct").

The mapping `⟦·⟧` follows the plan's tables, one case per construct.  `Any` and `Nothing` are `⊤` and
`⊥`.  A refinement is a right-nested `∧` of its declarations, under `μ` when the body names the
refinement's binder.  `S => T` is `∀(_ : S) T`.  A written path takes its root from the scope: `this`
and a self name read as the binder of their template, a bare member `m` of a template `r` reads as
`⟦r⟧.m`.

The mapping adds binders whose names no Scala text contains.  The stem is `σ`.  An object, a literal
and a refinement at template depth `d + 1` bind `ν` followed by `d + 1` primes.  Templates on one chain
have different depths, so no binder shadows another, and a Scala parameter never captures a template
member.  A literal under its written type `T` reads as `let ℓ = ν(z) {ℓself = z, ⟦ms⟧} in (ℓ : ⟦T⟧)`.

The stem exists when the wrapper has members or when the program names the wrapper.  Then the program
is `let σ = ν(σ) {ℓself = σ, ⟦ms⟧} in ⟦e⟧`.  Every template starts with the hidden field `ℓself = z`
(D-7).  A term path whose kind is an object or a literal reads as `⟦p⟧.ℓself`, so its type is the
template's self type and not its singleton.

A block `val x = p` with `p` a module path is an alias, `alias x ⟦p⟧ ⟦r⟧`, and so is
`val x: p.type = p`.  The front end resolves an alias by substitution of the path for `x` (D-12).

The mapping adds two kinds of `bind`.  `bind .unstable ·u` binds the shortest unstable prefix of a term
path and then each later step in turn (D-10).  `bind .widen ·v` binds an application that is a lambda
body or a block result with no written type around it, and the right side of an untyped block `val`
that is no path.

A block `val x: T = e` with a written type reads as `let x : ⟦T⟧ = ⟦e⟧ in ⟦r⟧`, a typed `let`, which
binds `x` at `⟦T⟧` in both modes: a written type is never widened.  A literal `e` reads under `T`
(D-16), and when the block does not return `x` its `let` is untyped, since the literal form carries
the type.

Three flags of `tmS` place these.  `wr` says that a written type stands around the term.  `res` says
that the term is a lambda body or a block result.  `under` is the written type a literal stands under,
since a literal is only read under one (D-16).

`readFile` parses (`ScalaRead.parseFile`), checks (`ScalaRead.check`), maps (`ofScala`), numbers the
member names (`ScalaRead.labels`, with the labels of the inherited type witnesses, `labelsN`) and gives the module chains as label chains from `σ` (D-13).
`readNominal` is its projection to the term, the table and the chains.  Every function is structural.

`outcome` reads a file, compiles its term in the Scala mode with the file's module chains
(`compileE`), and then runs the member check R-M (D-19).  R-M walks the typing derivation of the
compiled term.  Each written type of the partial term is checked in the context the derivation gives
it, and a nested literal's definitions are opened at their path as `adnew` types them.  A type
selection `p.A` needs a bound of `A` from some view of `p` (`Core.bounds`).  Each field step of a
path needs a view that declares the field (`Core.views`).  R-M walks into refinements too, with
`μ U` opened in `Γ.cons (.mu U)`, as the vanilla check does.  D-19 left the inside of a refinement
to a syntactic check, and this walk replaces that sentence.  Each lookup has a fresh tank, and a
marked tank answers `limit`, so `outcome` never answers `unknown`.  An undeclared member gives
`outside` with scalac's E008, at the first selection of that member's name in the text.  The
theorems say that an `ok` outcome is the compilation of the term `readNominal` gives, that its
derivation checks in FCn, and that its term is safe.

The printers go the other way.  `toScala` prints a surface term as a `File` and checks it with the
reader, or gives the reason it has no Scala form, one of ten (`gapReasons`).  `fillToScala` prints
the elaborated term with every slot written.  `roundTrip` prints a term, reads the text back, and
compares the two resolutions.  The printed wrapper is `Main`.  The stem's binder prints as `Main`, an
object's binder as the object's name when it is not the innermost template, the innermost template's
binder as `this` outside a dependent function type.  A refinement's member prints bare when no inner
template declares that name.  A literal's binder prints as a generated self name `self<k>` when its
members name it.  A step `ℓself` prints as nothing, and so does a declaration `{ℓself : U}`.  In
`S ∧ U` a side that is one gives the other side, and a lone one prints `Any`, so an inferred `this`
result that widens to its object's self type prints without the hidden field.  A lambda field with a
declared type whose binders equal the lambda's prints as a `def` of as many lists, any other lambda
field as a `val`.  `Outcome.text` prints a type with these printers (`tyText`) and a reason with
`reasonText`.  A type with no Scala form prints as `(no Scala form: <reason>)`.

Plan XII N3 g1 passes the class forms through: `ptmSubst` substitutes in a tag and `pdefSubst` in a
class definition.

Plan XII N6 maps classes and traits ("The mapping, one equation per construct").  A class or trait `K`
of a template `z` becomes `class K = Body(K)`, its module functions `f$K` and `val` witnesses `a$K`
under the receiver `this : z.K`, its override witnesses, and for a concrete class the constructor
`new$K`, whose body is the tagged literal `ν(i) as z.K {…}` with the members of `names(K)`: hidden
fields, `val` parameters at their arguments, type members at the first alias or the meet of the upper
bounds, path `val`s, and forwarders to the module functions of the implementer.  `Body(K)` is
`μ(this. ⋀ᴸ decls(K)) ∧ ⋀ᴿ parents(K)`, a parameter type read in the class head (`Scope.headEnv`).  A
type of another class is read at the binder of `K` or of its instance, and a template not around `K`
by its path from the stem (`clsSubst`).  A type member that `K` inherits from two classes and does not
declare gets the witnesses `ovc` of their pairwise consistency.  A witness whose obligation holds by its
form is left out.
`new p.K(ē)` is `let ·n = ⟦p⟧.new$K ē in ·n`, `this` in a body is `this.ℓself`, and a plain parameter
`x` is the hidden field `ℓx$K`.  That a signature through `ℓx$K` is expressible in FCn does not make the
Scala signature legal: the check OV-Private of `ScalaClasses.lean` refuses a member of `K` whose signature
names `x`, unless OV-Private's second walk at an alias removes the report.  Where it makes no second walk,
it refuses.  The check runs after the mapping and before the typer.  The mapping refuses two shapes as
outside: more than one argument for one parameter, which scalac tuples, and a parent's argument that is no
path.  `outcome` runs the checks of
`ScalaClasses.lean` before the typer and answers `rejected` with scalac's text (`Outcome.checked`).
`ofScala_tags` says that the mapping writes a tag only on the instance literal of a constructor, and
`scala_seal_sites` that an `ok` outcome seals only at tagged variables.  The printers give a class
definition and a tagged literal the gap `gapClass`.
-/

namespace NominalFrontend.Scala

open ScalaSyntax (Pos Err)
open Paths.FCdot (Sig BVar Label Rename Path PathSubst)
open NominalFrontend.ScalaRead (File Mems Stats Decls Bound Param ClsDecl ClassRef CMems Args newName modName hidName
  witName superName)
open Paths.FCdot (Label)
open NominalFrontend.ScalaRead.Scope (Entry lookup lookupTyp thisOf kindPath clsOf? clsKey memCls headEnv lookupCls
  clsKind refEnv?)

/-! ## Names -/

/-- The binder of the stem. -/
def stemName : String := "σ"
/-- The binder of a literal under its written type (D-16). -/
def litName : String := "ℓ"
/-- The binder of `bind .widen`. -/
def wideName : String := "·v"
/-- The binder of `bind .unstable`. -/
def unstName : String := "·u"
/-- The binder of `S => T`. -/
def anonName : String := "_"
/-- The label name of the hidden self-alias field (D-7). -/
def selfName : String := ScalaRead.selfLabelName
/-- The binder of the result of `new` (D-15). -/
def newVar : String := "·n"
/-- The binder of a forwarder's partial application (D-9). -/
def fwdVar : String := "·g"
/-- The binder of an override witness (D-13). -/
def witVar : String := "·w"
/-- The parameter of the constructor of a class without parameters (D-8, Ctor-Nil). -/
def nilVar : String := "·c"
/-- The binder of an argument at the type of its parameter in `super$K`. -/
def supVar : String := "·s"
/-- The name of the argument of the parent's parameter `y` in `super$K`. -/
def supArg (y : String) : String := "·p" ++ y
/-- The name of the parameter `x` of `K` in the lambda of `super$K`, when an obligation names an outer `x`. -/
def supKeep (x : String) : String := "·k" ++ x
/-- The name of the outer variable `x` in the obligations of `super$K`, when `K` has a parameter `x`. -/
def supOut (x : String) : String := "·o" ++ x

/-- The binder of a template at depth `d`: `σ` for the stem, `ν'`, `ν''`, … below it. -/
def tmplName : Nat → String
  | 0 => stemName
  | d + 1 => String.ofList ('ν' :: List.replicate (d + 1) '\'')

/-- The number of templates in a context. -/
def tmplCount : List Entry → Nat
  | [] => 0
  | .tmpl _ :: env => tmplCount env + 1
  | _ :: env => tmplCount env

/-- The binder of the template at the head of `env`. -/
def binderOf (env : List Entry) : String := tmplName (tmplCount env - 1)

/-! ## Messages for cases `check` refuses first -/

/-- A name the scope does not know. -/
def msgScope (x : String) : String := "`" ++ x ++ "` is not in scope"
/-- `this` with no template around it. -/
def msgThisOutside : String := "`this` outside every template"
/-- A bare type name no enclosing template declares. -/
def msgTypeOutside (A : String) : String := "the type `" ++ A ++ "` is outside the subset"
/-- A refinement with no declaration. -/
def msgEmptyRefinement : String := "an empty refinement is outside the subset"
/-- A literal with no written type around it (D-16). -/
def msgLitNoType : String := "an object literal needs a written type: scalac types it as Object"
/-- A field whose right side is neither a path nor a lambda. -/
def msgField : String := "a field holds a path or a value in pDOT: move the computation into `program`"
/-- More arguments than parameters, which scalac tuples (probes P01, P02). -/
def msgTupled : String := "more arguments than the one parameter: scalac tuples them, which is outside the subset"
/-- An argument of a parent that is no path. -/
def msgParentArg : String := "an argument of a parent is a path in this stage"

/-! ## Contexts -/

/-- The context of the mapping: the reader's scope entries, innermost first, and the fuel of `kindPath`. -/
structure MCtx where
  env : List Entry
  fuel : Nat

/-- The context with one more entry. -/
def MCtx.push (c : MCtx) (e : Entry) : MCtx := { c with env := e :: c.env }

/-! ## Surface helpers -/

/-- A surface path as a term, by `var` and `proj`. -/
def pathTm : SPath → STm
  | .var x => .var x
  | .sel p a => .proj (pathTm p) a

/-- The root variable of a surface path. -/
def pathRoot : SPath → String
  | .var x => x
  | .sel p _ => pathRoot p

/-- Whether `b` is the root of a path in a type. -/
def tyMentions (b : String) : SType → Bool
  | .top | .bot => false
  | .typ _ S T => tyMentions b S || tyMentions b T
  | .fld _ T => tyMentions b T
  | .sngl p | .sel p _ => decide (pathRoot p = b)
  | .mu _ T => tyMentions b T
  | .all _ S T => tyMentions b S || tyMentions b T
  | .and S T => tyMentions b S || tyMentions b T

/-- Whether `b` is the root of a path in a type outside every binder of that name. -/
def tyFree (b : String) : SType → Bool
  | .top | .bot => false
  | .typ _ S T => tyFree b S || tyFree b T
  | .fld _ T => tyFree b T
  | .sngl p | .sel p _ => decide (pathRoot p = b)
  | .mu x T => !decide (x = b) && tyFree b T
  | .all x S T => tyFree b S || (!decide (x = b) && tyFree b T)
  | .and S T => tyFree b S || tyFree b T

/-- Whether `b` is the root of a path in an optional type. -/
def tyOptMentions (b : String) : Option SType → Bool
  | some T => tyMentions b T
  | none => false

mutual
/-- Whether the name `b` occurs as a variable or as a path root in a term. -/
def tmMentions (b : String) (e : STm) : Bool :=
  match e with
  | .var x => decide (x = b)
  | .lam _ T t => tyOptMentions b T || tmMentions b t
  | .obj _ T d => tyOptMentions b T || defsMention b d
  | .app t u => tmMentions b t || tmMentions b u
  | .proj t _ => tmMentions b t
  | .«let» _ T t u => tyOptMentions b T || tmMentions b t || tmMentions b u
  | .asc t T => tmMentions b t || tyMentions b T
  | .alias _ p u => decide (pathRoot p = b) || tmMentions b u
  | .bind _ _ t u => tmMentions b t || tmMentions b u
  | .inst _ p _ d => decide (pathRoot p = b) || defsMention b d
termination_by structural e
/-- Whether `b` occurs in a list of definitions. -/
def defsMention (b : String) (d : SDefs) : Bool :=
  match d with
  | .nil => false
  | .typ ds _ T => defsMention b ds || tyMentions b T
  | .trm ds _ T t => defsMention b ds || tyOptMentions b T || tmMentions b t
  | .cls ds _ T => defsMention b ds || tyMentions b T
termination_by structural d
end

/-- The first definition of every template, `ℓself = z` (D-7). -/
def selfDefs (z : String) : SDefs := .trm .nil selfName none (.var z)

/-- `let ℓ = ν(z) {ds} in (ℓ : T)`, a literal under its written type (D-16). -/
def litForm (z : String) (ds : SDefs) (T : SType) : STm :=
  .«let» litName none (.obj z none ds) (.asc (.var litName) T)

/-- Whether the stem was made. -/
def isStem : STm → Bool
  | .«let» x none (.obj y none _) _ => decide (x = stemName) && decide (y = stemName)
  | _ => false

/-! ## Paths -/

/-- The label of the member `x` of the template at the head of `env`: `ℓx$K` for a plain parameter `x`
of a class `K` (D-11), else `x`. -/
def memLabel (env : List Entry) (x : String) : String :=
  match clsOf? env with
  | some d => if d.plain x then hidName x d.name else x
  | none => x

/-- A path of a written type: the root by the scope, `this` and a self name as the template's binder,
a bare member `m` of `r` as `⟦r⟧.m`, a plain parameter `x` of a class `K` as `⟦r⟧.ℓx$K`. -/
def pathS (env : List Entry) : ScalaRead.Path → Except Err SPath
  | .this p =>
    match thisOf env with
    | some env' => pure (.var (binderOf env'))
    | none => throw ⟨p, msgThisOutside⟩
  | .var p x =>
    match lookup x env with
    | .param .. | .val .. => pure (.var x)
    | .self env' => pure (.var (binderOf env'))
    | .member env' => pure (.sel (.var (binderOf env')) (memLabel env' x))
    | _ => throw ⟨p, msgScope x⟩
  | .sel q _ a => do
    let q' ← pathS env q
    match q, thisOf env with
    | .this _, some env' => pure (.sel q' (memLabel env' a))
    | _, _ => pure (.sel q' a)

/-- The shortest prefix of length two or more of a proper prefix whose kind is a method or unstable,
with the steps after it. -/
def unstIn (n : Nat) (env : List Entry) : ScalaRead.Path → Option (ScalaRead.Path × List String)
  | .this _ | .var _ _ => none
  | .sel q p a =>
    match unstIn n env q with
    | some (r, cs) => some (r, cs ++ [a])
    | none =>
      match kindPath n env none (.sel q p a) with
      | .meth _ | .unstable => some (.sel q p a, [])
      | _ => none

/-- The shortest unstable prefix of length two or more of a term path, the whole path included unless
it is a method, with the steps after it (D-10). -/
def termUnst? (n : Nat) (env : List Entry) : ScalaRead.Path → Option (ScalaRead.Path × List String)
  | .sel q p a =>
    match unstIn n env q with
    | some (r, cs) => some (r, cs ++ [a])
    | none =>
      match kindPath n env none (.sel q p a) with
      | .unstable => some (.sel q p a, [])
      | _ => none
  | _ => none

/-- The bindings of the steps after an unstable prefix bound to `·u`. -/
def unstRest : List String → STm
  | [] => .var unstName
  | [c] => .proj (.var unstName) c
  | c :: cs => .bind .unstable unstName (.proj (.var unstName) c) (unstRest cs)

/-- A term path: the unstable prefix bound first (D-10), else the path, with `.ℓself` when its kind is
an object or a literal (D-7). -/
def termPath (c : MCtx) (q : ScalaRead.Path) : Except Err STm :=
  match termUnst? c.fuel c.env q with
  | some (r, cs) => do
    let r' ← pathS c.env r
    pure (.bind .unstable unstName (pathTm r') (unstRest cs))
  | none => do
    let q' ← pathS c.env q
    match (kindPath c.fuel c.env none q).word, q with
    | .obj, _ | .lit, _ | .inst, .this _ => pure (.proj (pathTm q') selfName)
    | _, _ => pure (pathTm q')

/-- The path of an unstable chain `bind .unstable ·u q (…)`, read back (D-10). -/
def unstPath? (q : SPath) : STm → Option SPath
  | .var _ => some q
  | .proj (.var _) a => some (q.sel a)
  | .bind .unstable _ (.proj (.var _) a) r => unstPath? (q.sel a) r
  | _ => none

/-- The path that a term of `termPath` stands for: the term when it is a path, else the unstable prefix with the
steps after it read back.  The instance literal holds that path for a parent's argument (`argPath`), and the
field `super$K` checks the argument bound first. -/
def termPathOf? : STm → Option SPath
  | .bind .unstable _ t r => t.toPath?.bind (unstPath? · r)
  | t => t.toPath?

/-! ## Types -/

mutual
/-- A written type as a surface type. -/
def tyS (c : MCtx) (T : ScalaRead.Ty) : Except Err SType :=
  match T with
  | .any _ => pure .top
  | .nothing _ => pure .bot
  | .sel _ q A => do
    let q' ← pathS c.env q
    pure (.sel q' A)
  | .sngl _ q => do
    let q' ← pathS c.env q
    pure (.sngl q')
  | .name p A =>
    match lookupTyp A c.env with
    | some env' => pure (.sel (.var (binderOf env')) A)
    | none => throw ⟨p, msgTypeOutside A⟩
  | .refine p ds => do
    let c' := c.push (.tmpl (.ref p ds))
    let b := binderOf c'.env
    let body ← declsS c' p ds
    pure (if tyMentions b body then .mu b body else body)
  | .and S U => do
    let S' ← tyS c S
    let U' ← tyS c U
    pure (.and S' U')
  | .fn _ (some x) S U => do
    let S' ← tyS c S
    let U' ← tyS (c.push (.param x (some S) false)) U
    pure (.all x S' U')
  | .fn _ none S U => do
    let S' ← tyS c S
    let U' ← tyS c U
    pure (.all anonName S' U')
termination_by structural T
/-- A bound of a type member, `dflt` when it is absent. -/
def boundS (c : MCtx) (dflt : SType) (b : Bound) : Except Err SType :=
  match b with
  | .absent => pure dflt
  | .given T => tyS c T
termination_by structural b
/-- The declarations of a refinement as a right-nested `∧`.  An empty refinement is refused at `p`. -/
def declsS (c : MCtx) (p : Pos) (ds : Decls) : Except Err SType :=
  match ds with
  | .nil => throw ⟨p, msgEmptyRefinement⟩
  | .typ _ A lo hi r => do
    let S ← boundS c .bot lo
    let U ← boundS c .top hi
    match r with
    | .nil => pure (.typ A S U)
    | _ => do
      let rest ← declsS c p r
      pure (.and (.typ A S U) rest)
  | .alias _ A T r => do
    let T' ← tyS c T
    match r with
    | .nil => pure (.typ A T' T')
    | _ => do
      let rest ← declsS c p r
      pure (.and (.typ A T' T') rest)
  | .val _ a T r => do
    let T' ← tyS c T
    match r with
    | .nil => pure (.fld a T')
    | _ => do
      let rest ← declsS c p r
      pure (.and (.fld a T') rest)
termination_by structural ds
end

/-- An optional written type. -/
def tyOptS (c : MCtx) : Option ScalaRead.Ty → Except Err (Option SType)
  | some T => some <$> tyS c T
  | none => pure none

/-- The parameters of a def, each in scope of the later ones: their names and mapped domains, and the
context after them. -/
def paramsS (c : MCtx) : List Param → Except Err (List (String × SType) × MCtx)
  | [] => pure ([], c)
  | x :: xs => do
    let S ← tyS c x.ty
    let (rest, c') ← paramsS (c.push (.param x.name (some x.ty) false)) xs
    pure ((x.name, S) :: rest, c')

/-- `∀(x₁ : S₁) … ∀(xₙ : Sₙ) R`. -/
def allChain : List (String × SType) → SType → SType
  | [], R => R
  | (x, S) :: xs, R => .all x S (allChain xs R)

/-- `λ(x₁ : S₁). … λ(xₙ : Sₙ). b`. -/
def lamChain : List (String × SType) → STm → STm
  | [], b => b
  | (x, S) :: xs, b => .lam x (some S) (lamChain xs b)

/-! ## Classes (plan XII, "The mapping, one equation per construct") -/

/-- The path a name stands for in a substitution of roots. -/
def lookupS (x : String) : List (String × SPath) → Option SPath
  | [] => none
  | (y, p) :: σ => if decide (x = y) then some p else lookupS x σ

/-- A substitution of roots without the name `x`, under a binder of that name. -/
def dropS (x : String) : List (String × SPath) → List (String × SPath)
  | [] => []
  | (y, p) :: σ => if decide (x = y) then dropS x σ else (y, p) :: dropS x σ

/-- A path with its root replaced by the path the substitution gives it. -/
def substRoot (σ : List (String × SPath)) : SPath → SPath
  | .var x => (lookupS x σ).getD (.var x)
  | .sel p a => .sel (substRoot σ p) a

/-- A type with the roots of its paths replaced, simultaneously, a binder of the type hiding its name. -/
def substRoots (σ : List (String × SPath)) : SType → SType
  | .top => .top
  | .bot => .bot
  | .typ A S T => .typ A (substRoots σ S) (substRoots σ T)
  | .fld a T => .fld a (substRoots σ T)
  | .sngl p => .sngl (substRoot σ p)
  | .sel p A => .sel (substRoot σ p) A
  | .mu x T => .mu x (substRoots (dropS x σ) T)
  | .all x S T => .all x (substRoots σ S) (substRoots (dropS x σ) T)
  | .and S T => .and (substRoots σ S) (substRoots σ T)

/-- The path from the stem of the template at the head of `env`: `σ` for the stem, `p.o` for an object
`o` of the template at `p`, none for another template. -/
def tmplPath : List Entry → Option SPath
  | [] => none
  | .tmpl (.stem ..) :: _ => some (.var stemName)
  | .tmpl (.obj _ o _ _) :: env => (tmplPath env).map (·.sel o)
  | .tmpl _ :: _ => none
  | _ :: env => tmplPath env

/-- The binder of each template of a context that is the stem or an object, with its path from the stem. -/
def objSubst : List Entry → List (String × SPath)
  | [] => []
  | e :: env =>
    (match e, tmplPath (e :: env) with
     | .tmpl _, some p => [(binderOf (e :: env), p)]
     | _, _ => []) ++ objSubst env

/-- The binders of the stem and the objects around the class at the head of `eD` that are not around the
class at the head of `eK`, each with its path from the stem.  The others are in scope at `K`. -/
def relSubst (eD eK : List Entry) : List (String × SPath) :=
  (objSubst eD.tail).filter fun bp => !(objSubst eK.tail).contains bp

/-- The substitution that reads a type of the class at the head of `eD` at the binder `b` inside the template
of the class at the head of `eK`: the class's binder to `b`, each binder of the stem and the objects around it
and not around `K` to its path from the stem. -/
def clsSubst (eD eK : List Entry) (b : String) : List (String × SPath) :=
  (binderOf eD, .var b) :: relSubst eD eK

/-- The template of the class at the head of `eD` as a path at the class at the head of `eK`: its binder when it
is around `K`, else its path from the stem. -/
def tmplAt (eD eK : List Entry) : Option SPath :=
  (tmplPath eD.tail).map fun p =>
    match (objSubst eK.tail).find? fun bp => decide (bp.2 = p) with
    | some (b, _) => .var b
    | none => p

/-- The parameters of a class at its body binder `b`: `b.x` for a `val` parameter, `b.ℓx$K` for a plain one. -/
def paramSubst (d : ClsDecl) (b : String) : List (String × SPath) :=
  d.params.map fun x => (x.name, .sel (.var b) (if x.isVal then x.name else hidName x.name d.name))

/-- `⋀ᴸ`: the left-nested intersection, `⊤` for none. -/
def andL : List SType → SType
  | [] => .top
  | T :: Ts => Ts.foldl .and T

/-- `⋀ᴿ`: the right-nested intersection ending in `⊤`. -/
def andR : List SType → SType
  | [] => .top
  | T :: Ts => .and T (andR Ts)

/-- A class reference as a written type, `C` or `q.C`. -/
def refTy (P : ClassRef) : ScalaRead.Ty :=
  match P.pre with
  | none => .name P.pos P.name
  | some q => .sel P.pos q P.name

/-- `own(m)` for each member of a class body, in text order, in the body's context `cK`. -/
def ownDecls (cK : MCtx) : CMems → Except Err (List SType)
  | .nil => pure []
  | .typ _ _ A lo hi r => do
    let S ← boundS cK .bot lo
    let U ← boundS cK .top hi
    let rest ← ownDecls cK r
    pure (.typ A S U :: rest)
  | .alias _ _ A T r => do
    let T' ← tyS cK T
    let rest ← ownDecls cK r
    pure (.typ A T' T' :: rest)
  | .valDecl _ _ a T r | .val _ _ a T _ r => do
    let T' ← tyS cK T
    let rest ← ownDecls cK r
    pure (.fld a T' :: rest)
  | .defDecl _ _ f ps R r | .defn _ _ f ps R _ r => do
    let (doms, cP) ← paramsS cK ps
    let R' ← tyS cP R
    let rest ← ownDecls cK r
    pure (.fld f (allChain doms R') :: rest)

/-- `class K = Body(K)` after `ds`: `μ(b. ⋀ᴸ decls(K)) ∧ ⋀ᴿ parents(K)`, with `decls(K)` the self-alias field,
`hid` of every plain parameter, `vdec` of every `val` parameter, then `own` of every member.  A parameter's
type is read in the head context, its parameters at their fields (N5 departure 4). -/
def clsDefS (c : MCtx) (d : ClsDecl) (ds : SDefs) : Except Err SDefs := do
  let cK := c.push (.tmpl (.cls d))
  let b := binderOf cK.env
  let hc : MCtx := { c with env := headEnv cK.env }
  let ps ← d.params.mapM fun x => do
    let S ← tyS hc x.ty
    pure (x, substRoots (paramSubst d b) S)
  let hid := ps.filterMap fun (x, S) => if x.isVal then none else some (SType.fld (hidName x.name d.name) S)
  let vdec := ps.filterMap fun (x, S) => if x.isVal then some (SType.fld x.name S) else none
  let own ← ownDecls cK d.body
  let parents ← d.parents.refs.mapM fun P => tyS c (refTy P)
  pure (.cls ds d.name (.and (.mu b (andL (.fld selfName (.sngl (.var b)) :: hid ++ vdec ++ own))) (andR parents)))

/-- The declared type of the member `a` in the body of the class whose context is `cD`, if it declares one. -/
def bodyTy (cD : MCtx) (a : String) : CMems → Except Err (Option SType)
  | .nil => pure none
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r => bodyTy cD a r
  | .valDecl _ _ b T r | .val _ _ b T _ r =>
    if decide (a = b) then some <$> tyS cD T else bodyTy cD a r
  | .defDecl _ _ f ps R r | .defn _ _ f ps R _ r =>
    if decide (a = f) then do
      let (doms, cP) ← paramsS cD ps
      let R' ← tyS cP R
      pure (some (allChain doms R'))
    else bodyTy cD a r

/-- The declared type of the term member `a` of the class at the head of `eD`, read at the binder `b`
(`clsSubst`): a `val` parameter's type in the head context, a body member's in the body. -/
def memTy (c : MCtx) (eK eD : List Entry) (b a : String) : Except Err (Option SType) :=
  match clsOf? eD with
  | none => pure none
  | some d =>
    match d.params.find? fun x => x.isVal && decide (x.name = a) with
    | some x => do
      let S ← tyS { c with env := headEnv eD } x.ty
      pure (some (substRoots (clsSubst eD eK b) (substRoots (paramSubst d (binderOf eD)) S)))
    | none => do
      let T ← bodyTy { c with env := eD } a d.body
      pure (T.map (substRoots (clsSubst eD eK b)))

/-- The bounds of the type member `A` of the class at the head of `eD`, read at the binder `b`: an alias as
both bounds, an absent bound as `⊥` or `⊤`. -/
def memBounds (c : MCtx) (eK eD : List Entry) (b A : String) : Except Err (Option (SType × SType)) :=
  match (clsOf? eD).bind (·.body.findTyp A) with
  | some (.alias T) => do
    let T' ← tyS { c with env := eD } T
    let T'' := substRoots (clsSubst eD eK b) T'
    pure (some (T'', T''))
  | some (.bounds lo hi) => do
    let S ← boundS { c with env := eD } .bot lo
    let U ← boundS { c with env := eD } .top hi
    pure (some (substRoots (clsSubst eD eK b) S, substRoots (clsSubst eD eK b) U))
  | none => pure none

/-- The first `n` binders of a dependent function type, and the rest. -/
def splitAll : Nat → SType → List (String × SType) × SType
  | n + 1, .all x S T => let (ps, R) := splitAll n T; ((x, S) :: ps, R)
  | _, T => ([], T)

/-- A dependent function type with the result after its first `n` binders replaced by `⊤`. -/
def resTop : Nat → SType → SType
  | n + 1, .all x S T => .all x S (resTop n T)
  | _, _ => .top

/-- The witness `l : ∀(b : recv) ∀(·w : S) T = λ(b : recv). λ(·w : S). ·w` after `ds` (D-13), left out when
`S <: T` holds by its form: `S = T`, `S = ⊥` or `T = ⊤`. -/
def witS (ds : SDefs) (l b : String) (recv S T : SType) : SDefs :=
  if decide (S = T) || decide (S = .bot) || decide (T = .top) then ds
  else .trm ds l (some (.all b recv (.all witVar S T))) (.lam b (some recv) (.lam witVar (some S) (.var witVar)))

/-- The number of lists of the member `a` of the class at the head of `e`, `none` for a `val`. -/
def defLists (e : List Entry) (a : String) : Option Nat :=
  match (clsOf? e).bind (·.findMem a) with
  | some (.defn n) => some n
  | _ => none

/-- The witnesses of the term member `a` of `K` at the receiver `b : recv` after `ds`: for each `D ≠ E` of `L`
that declares `a`, `E` the class of `eff(a, K)`, `ov` and `ovp` for a `def`, `ovv` for a `val`, unless the two
types are equal or a class `P ≠ K` of `L` has `eff(a, P)` from `E` and `D` in `L(P)`. -/
def trmWits (c : MCtx) (K : String) (eK : List Entry) (L : List (List Entry)) (b : String) (recv : SType) (ds : SDefs) (a : String) :
    Except Err SDefs :=
  match Classes.effCls a L with
  | none => pure ds
  | some eE => do
    match ← memTy c eK eE b a with
    | none => pure ds
    | some FE =>
      let Ds := L.filter fun eD => !decide (clsKey eD = clsKey eE) && Classes.declaresAt a eD &&
        !(L.tail.any fun eP => match Classes.effCls a (Classes.linD eP) with
          | some eE' => decide (clsKey eE' = clsKey eE) && memCls eD (Classes.linD eP)
          | none => false)
      Ds.foldlM (fun ds eD => do
        match ← memTy c eK eD b a with
        | none => pure ds
        | some FD =>
          let D := Classes.nameAt eD
          match defLists eE a with
          | some n => pure (witS (witS ds (witName "ov" K a D) b recv FE FD) (witName "ovp" K a D) b recv
              (resTop n FD) (resTop n FE))
          | none => pure (witS ds (witName "ovv" K a D) b recv FE FD)) ds

/-- The witnesses `ovl` and `ovu` of the type member `A` that the body of `K` declares, for each `D ≠ K` of
`L(K)` that declares it, unless the two bounds are equal. -/
def typWits (c : MCtx) (K : String) (eK : List Entry) (L : List (List Entry)) (b : String) (recv : SType)
    (ds : SDefs) (A : String) : Except Err SDefs := do
  match ← memBounds c eK eK b A with
  | none => pure ds
  | some (LK, UK) =>
    L.tail.foldlM (fun ds eD => do
      if !Classes.declaresTypAt A eD then pure ds
      else
        match ← memBounds c eK eD b A with
        | none => pure ds
        | some (LD, UD) =>
          let D := Classes.nameAt eD
          pure (witS (witS ds (witName "ovl" K A D) b recv LD LK) (witName "ovu" K A D) b recv UK UD)) ds

/-- The witnesses `ovc` of the type member `A` that `K` inherits and does not declare: for each ordered pair
`D ≠ E` of classes of `L(K)` after `K` that declare `A`, `ovc$K$A$D$E : ∀(b : recv) ∀(·w : L_D) U_E`, the
pairwise consistency scalac asks of two inherited declarations (probes Q26, V1 to V5), left out by its form
as every witness. -/
def inhWits (c : MCtx) (K : String) (eK : List Entry) (L : List (List Entry)) (b : String) (recv : SType)
    (ds : SDefs) (A : String) : Except Err SDefs := do
  let Ds := L.tail.filter (Classes.declaresTypAt A)
  Ds.foldlM (fun ds eD => do
    match ← memBounds c eK eD b A with
    | none => pure ds
    | some (LD, _) =>
      Ds.foldlM (fun ds eE => do
        if decide (clsKey eD = clsKey eE) then pure ds else
        match ← memBounds c eK eE b A with
        | none => pure ds
        | some (_, UE) => pure (witS ds (witName "ovc" K A (Classes.nameAt eD ++ "$" ++ Classes.nameAt eE)) b recv LD UE)) ds) ds

/-- The type members of `names(K)` that `K` does not declare. -/
def inhTyps (d : ClsDecl) (L : List (List Entry)) : List String :=
  (Classes.names L).filterMap fun
    | .typ A => if d.body.declaresTyp A then none else some A
    | _ => none

/-- The labels of the witnesses of `inhWits` for the class at the head of `e`, one per ordered pair, written
or not. -/
def inhLabels (e : List Entry) : List (String × Bool) :=
  match clsOf? e with
  | some d =>
    let L := Classes.linD e
    (inhTyps d L).flatMap fun A =>
      let Ds := L.tail.filter (Classes.declaresTypAt A)
      Ds.flatMap fun eD => Ds.filterMap fun eE =>
        if decide (clsKey eD = clsKey eE) then none
        else some (witName "ovc" d.name A (Classes.nameAt eD ++ "$" ++ Classes.nameAt eE), false)
  | none => []

/-- `witnesses(K)` after `ds`, at the receiver `b : z.K` with `b` the body's binder (plan 784 to 796, D-13). -/
def witnessesS (c : MCtx) (d : ClsDecl) (ds : SDefs) : Except Err SDefs := do
  let eK := (c.push (.tmpl (.cls d))).env
  let b := binderOf eK
  let recv : SType := .sel (.var (binderOf c.env)) d.name
  let L := Classes.linD eK
  let ds ← (Classes.termNames L).foldlM (trmWits c d.name eK L b recv) ds
  let ds ← d.body.typNames.foldlM (typWits c d.name eK L b recv) ds
  (inhTyps d L).foldlM (inhWits c d.name eK L b recv) ds

/-- The position of `y` in a list of parameters. -/
def indexOf (y : String) : List ScalaRead.CParam → Option Nat
  | [] => none
  | x :: xs => if decide (x.name = y) then some 0 else (indexOf y xs).map (· + 1)

/-- The `j`-th argument. -/
def argAt : Nat → Args → Option ScalaRead.Tm
  | _, .nil => none
  | 0, .cons t _ => some t
  | j + 1, .cons _ r => argAt j r

/-- `arg(K, D, y)` (plan 811 to 812): the parameter `y` itself at `K`, else the `j`-th argument of the first
parent of the class `E` of `L(K)` whose first parent is `D`, `y` the `j`-th parameter of `D`, read in the head
context of `E` with each parameter of `E` replaced by its argument and the stem and objects around `E` by their
paths.  An unstable argument (D-10) is the path it reads back to (`termPathOf?`): the literal holds the
argument's value, and the field `super$E` of the class `E` that gives it checks it bound first.  Fuelled by the
length of `L(K)`. -/
def argPath (c : MCtx) (eK : List Entry) (L : List (List Entry)) : Nat → List Entry → String → Option SPath
  | 0, _, _ => none
  | n + 1, eD, y =>
    if decide (clsKey eD = clsKey eK) then some (.var y)
    else
      L.findSome? fun eE =>
        match clsOf? eE, (clsOf? eD).bind fun dD => indexOf y dD.params with
        | some dE, some j =>
          match dE.parents with
          | .cons P as _ =>
            if ((refEnv? eE.tail P).map fun eP => decide (clsKey eP = clsKey eD)).getD false then
              match argAt j as with
              | some (.path q) =>
                match termPath { c with env := headEnv eE } q with
                | .ok t => (termPathOf? t).map fun p =>
                    substRoot ((dE.params.filterMap fun x => (argPath c eK L n eE x.name).map (x.name, ·)) ++
                      relSubst eE eK) p
                | .error _ => none
              | _ => none
            else none
          | .nil => none
        | _, _ => none

/-- A path of a `val`'s right side in the body of `P`, read in an instance with self `i`: `bP.x` for a
parameter `x` of `P` as its argument, the root `bP` as `i`, the stem and objects around `P` as their paths. -/
def instPath (bP i : String) (args objs : List (String × SPath)) : SPath → SPath
  | .var x => if decide (x = bP) then .var i else (lookupS x objs).getD (.var x)
  | .sel p a =>
    match p with
    | .var x => if decide (x = bP) then (lookupS a args).getD (.sel (.var i) a) else .sel (instPath bP i args objs p) a
    | _ => .sel (instPath bP i args objs p) a

/-- `apps(g, ys)` (plan 813 to 814): `g y` for the last name, `let g = g y in …` before it. -/
def appsS : List String → STm
  | [] => .var fwdVar
  | [y] => .app (.var fwdVar) (.var y)
  | y :: ys => .«let» fwdVar none (.app (.var fwdVar) (.var y)) (appsS ys)

/-- The forwarder `f : F = Λs(Ls, let ·g = zD.f$D i in apps(·g, names Ls))` after `ds`, `Ls` the first `n`
binders of `F` (D-9, plan 810). -/
def fwdS (ds : SDefs) (f : String) (F : SType) (n : Nat) (zD : SPath) (D i : String) : SDefs :=
  let ps := (splitAll n F).1
  .trm ds f (some F) (lamChain ps (.«let» fwdVar none (.app (pathTm (zD.sel (modName f D))) (.var i))
    (appsS (ps.map (·.1)))))

/-- `inst(m)` after `ds` for the member `m` of `names(K)` in the instance with self `i` (plan 803 to 810). -/
def instMem (c : MCtx) (eK : List Entry) (L : List (List Entry)) (i : String) (arg : List Entry → String → SPath) (ds : SDefs) :
    Classes.IName → Except Err SDefs
  | .hid x D =>
    match L.find? fun e => decide (Classes.nameAt e = D) with
    | some eD => pure (.trm ds (hidName x D) none (pathTm (arg eD x)))
    | none => pure ds
  | .typ A => do
    match L.findSome? fun eD => (clsOf? eD).bind fun dD =>
        if dD.body.aliases A then (dD.body.findTyp A).map (eD, ·) else none with
    | some (eD, .alias T) => do
      let T' ← tyS { c with env := eD } T
      pure (.typ ds A (substRoots (clsSubst eD eK i) T'))
    | _ => do
      let Us ← L.filterMapM fun eD => do
        match (clsOf? eD).bind (·.body.findTyp A) with
        | some (.bounds _ hi) => do
          let U ← boundS { c with env := eD } .top hi
          pure (if decide (U = .top) then none else some (substRoots (clsSubst eD eK i) U))
        | _ => pure none
      pure (.typ ds A (andL Us))
  | .trm a =>
    match Classes.mimpl a L with
    | none => pure ds
    | some eP =>
      match clsOf? eP, tmplAt eP eK with
      | some dP, some zP =>
        if dP.params.any fun x => x.isVal && decide (x.name = a) then pure (.trm ds a none (pathTm (arg eP a)))
        else
          match dP.body.valRhs? a with
          | some (.path q) => do
            let t ← termPath { c with env := eP } q
            match t.toPath? with
            | some p =>
              let args := dP.params.map fun x => (if x.isVal then x.name else hidName x.name dP.name, arg eP x.name)
              pure (.trm ds a none (pathTm (instPath (binderOf eP) i args (relSubst eP eK) p)))
            | none => pure ds
          | some _ => do
            match ← memTy c eK eP i a with
            | some F => pure (fwdS ds a F 1 zP dP.name i)
            | none => pure ds
          | none => do
            match ← memTy c eK eP i a, defLists eP a with
            | some F, some n => pure (fwdS ds a F n zP dP.name i)
            | _, _ => pure ds
      | _, _ => pure ds

/-- `Inst(K) = ν(i) as z.K {ℓself = i, insts(K)}`, the members in the order of `names(K)` (plan 800 to 810).
The literal stands bare, since resolution binds it already (`Resolve.lean:378-382`).  An argument the parents do
not give reads as `σ`: the class checks reject such a file first.  An argument that is an unstable path is held
as that path (`argPath`), and `super$E` checks it, `E` the class that gives it (`superS`).  A `val` parameter
that a class of `L(K)` overrides holds the override (`instMem`), and `super$K` checks the argument `K` gives it
(`supOverridden`). -/
def instS (c : MCtx) (d : ClsDecl) : Except Err STm := do
  let eK := (c.push (.tmpl (.cls d))).env
  let i := binderOf eK
  let L := Classes.linD eK
  let arg (eD : List Entry) (y : String) : SPath := (argPath c eK L L.length eD y).getD (.var stemName)
  let ds ← (Classes.names L).foldlM (instMem c eK L i arg) (selfDefs i)
  pure (.inst i (.var (binderOf c.env)) d.name ds)

/-- `ctor(K)` after `ds`: `new$K : Πs(params K, z.K) = Λs(params K, Inst(K))`, the parameter types read in the
head context, or `∀(·c : ⊤) z.K` when `K` has no parameter (Ctor-Nil, D-8). -/
def ctorS (c : MCtx) (d : ClsDecl) (ds : SDefs) : Except Err SDefs := do
  let hc : MCtx := { c with env := headEnv (.tmpl (.cls d) :: c.env) }
  let ps ← d.params.mapM fun x => do
    let S ← tyS hc x.ty
    pure (x.name, S)
  let inst ← instS c d
  let ps' := if ps.isEmpty then [(nilVar, SType.top)] else ps
  pure (.trm ds (newName d.name) (some (allChain ps' (.sel (.var (binderOf c.env)) d.name))) (lamChain ps' inst))

/-- `alias x₁ = p₁ in … alias xₙ = pₙ in b`. -/
def aliasChain : List (String × SPath) → STm → STm
  | [], b => b
  | (x, p) :: r, b => .alias x p (aliasChain r b)

/-- `let ·s : T₁ = ·py₁ in … let ·s : Tₙ = ·pyₙ in ·s`: each argument at the type of its parameter. -/
def supChecks : List (String × SType) → STm
  | [] => .var supVar
  | (y, T) :: r => .«let» supVar (some T) (.var (supArg y)) (supChecks r)

/-- The arguments of the first parent, each bound to `·py` for the parameter `y` it gives, in the class's head
context `hc` as `ctorS` reads them: an alias when the argument maps to a path, a `let` otherwise. -/
def supBinds (hc : MCtx) : List ScalaRead.CParam → Args → STm → Except Err STm
  | y :: ys, .cons (.path q) r, b => do
    let t ← termPath hc q
    let rest ← supBinds hc ys r b
    match t.toPath? with
    | some p => pure (.alias (supArg y.name) p rest)
    | none => pure (.«let» (supArg y.name) none t rest)
  | _, _, b => pure b

/-- The parameters of `D` given an unstable argument (D-10), read in the head context `hc`. -/
def argsUnst (hc : MCtx) : List ScalaRead.CParam → Args → List String
  | y :: ys, .cons (.path q) r => (if (termUnst? hc.fuel hc.env q).isSome then [y.name] else []) ++ argsUnst hc ys r
  | _, _ => []

/-- The parameters of `D` given an argument that maps to a path, each with that path, read in the head context
`hc`. -/
def argsSubst (hc : MCtx) : List ScalaRead.CParam → Args → List (String × SPath)
  | y :: ys, .cons (.path q) r =>
    (match termPath hc q with
     | .ok t => (t.toPath?.map (y.name, ·)).toList
     | .error _ => []) ++ argsSubst hc ys r
  | _, _ => []

/-- The substitution of `supByForm`: each parameter of `D` at its argument's path, then `rel`, when every
parameter of `D` is given an argument that maps to a path, else empty. -/
def supSubst (hc : MCtx) (ys : List ScalaRead.CParam) (as : Args) (rel : List (String × SPath)) :
    List (String × SPath) :=
  if (argsSubst hc ys as).length = ys.length then argsSubst hc ys as ++ rel else []

/-- The names that the binders of a type bind. -/
def tyBinders : SType → List String
  | .top | .bot | .sngl _ | .sel _ _ => []
  | .typ _ S T | .and S T => tyBinders S ++ tyBinders T
  | .fld _ T => tyBinders T
  | .mu x T => x :: tyBinders T
  | .all x S T => x :: (tyBinders S ++ tyBinders T)

/-- Whether the obligation of the parameter `y` of `D` at its type `T` holds by its form: `σA` gives `y` a
parameter `x` of `K`, the type of `x` in `ps` is `T` with the substitution `σA` applied, no binder of `T`
has the name of a root of a path of `σA`, so the substitution captures nothing, and every parameter of `K`
that `T` names is a name that `σA` replaces, so no outer variable of `T` reads as a parameter of `K`.  `σA` is
empty unless every parameter of `D` is given an argument that maps to a path. -/
def supByForm (ps : List (String × SType)) (σA : List (String × SPath)) (y : String) (T : SType) : Bool :=
  match lookupS y σA with
  | some (.var x) =>
    !((tyBinders T).any fun b => σA.any fun bp => decide (pathRoot bp.2 = b)) &&
      (ps.all fun xS => (lookupS xS.1 σA).isSome || !tyFree xS.1 T) &&
      decide (ps.lookup x = some (substRoots σA T))
  | _ => false

/-- The conjuncts of a type at its top: the parts of an intersection, else the type itself. -/
def andParts : SType → List SType
  | .and S T => andParts S ++ andParts T
  | T => [T]

/-- Whether a conjunct of the type of the parameter `y` of `D` holds by its form: it is a singleton `q.type`
whose root `σS` replaces, and `q` with `σS` applied is the path `σS` gives `y`.  `σS` gives each parameter of `D`
whose argument maps to a path that path, and the stem and objects around `D` their paths.  The obligation is
then `p : p.type` for the stable path `p`, which scalac concludes and which the front end refuses by design
(N4). -/
def snglByForm (σS : List (String × SPath)) (y : String) : SType → Bool
  | .sngl q =>
    match lookupS (pathRoot q) σS, lookupS y σS with
    | some _, some p => decide (substRoot σS q = p)
    | _, _ => false
  | _ => false

/-- The type of the parameter `y` of `D` without its conjuncts that hold by their form (`snglByForm`), `none`
when every conjunct does.  A type with no such conjunct comes back unchanged. -/
def supDropSngl (σS : List (String × SPath)) (y : String) (T : SType) : Option SType :=
  let Us := andParts T
  if Us.any (snglByForm σS y) then
    match Us.filter fun U => !snglByForm σS y U with
    | [] => none
    | Vs => some (andL Vs)
  else some T

/-- The `val` parameters of the first parent `D` (at `eD`) whose implementer in `L = L(K)` is not `D`: a class
or trait of `L(K)` overrides them, so the instance literal of `K` holds the override and not the argument. -/
def supOverridden (eD : List Entry) (D : ClsDecl) (L : List (List Entry)) : List String :=
  (D.params.filter fun y => y.isVal &&
    ((Classes.mimpl y.name L).map fun eP => !decide (clsKey eP = clsKey eD)).getD false).map (·.name)

/-- The parameters of `K` whose names are roots in an obligation of `super$K`.  Such a root is a variable
outside the class, since the parameters of `D` are replaced already, and the lambda of `super$K` would capture
it. -/
def supCaptured (ps Ts : List (String × SType)) : List String :=
  (ps.map (·.1)).filter fun x => Ts.any fun yT => tyFree x yT.2

/-- The parameters of `K` for the lambda of `super$K`: each name of `cap` renamed to `·kx`, each type read with
the renamings of the parameters before it, as `lamChain` scopes them. -/
def supParams (cap : List String) : List (String × SType) → List (String × SPath) → List (String × SType)
  | [], _ => []
  | (x, S) :: r, σ =>
    if cap.contains x then (supKeep x, substRoots σ S) :: supParams cap r ((x, .var (supKeep x)) :: σ)
    else (x, substRoots σ S) :: supParams cap r (dropS x σ)

/-- `super(K)` after `ds`, for a class `K` whose first parent `D` is given arguments (review Priority 1):
`super$K : Πs(params K, ⊤) = Λs(params K, binds(args, checks))`.  The parameters of `K` are read in the head
context as `ctorS` reads them.  Each argument is bound to the name of the parameter of `D` it gives, and is
checked at that parameter's type, read in the head context of `D` with the parameters of `D` at their
arguments and the stem and objects around `D` at their paths.  The field builds no instance and carries no tag,
so a class without a constructor stays without one.
For a class without a constructor (`conc = false`) every obligation is checked, except one that holds by its
form (`supByForm`).  For a class with a constructor (`conc = true`) the typing of its instance literal checks
the other arguments, so only these are checked here: an unstable argument (D-10), an argument of a `val`
parameter of `D` that a class of `L(K)` overrides (`supOverridden`), and an argument whose parameter's type
names a parameter of these two kinds.  The literal holds the unstable path, and the check here binds it first,
as scalac reads it as an unknown value.  The literal holds the override of an overridden parameter, so the
argument appears there nowhere.  In both modes a singleton conjunct `q.type` of an obligation is left out when
`q` and the argument map to the same path (`supDropSngl`).  With no obligation left the field is left out.  A parameter of `K` whose name is an outer root of an obligation (`supCaptured`) is bound as `·kx`, the
outer variable is aliased to `·ox` and the name `x` back to `·kx`, so the lambda captures nothing. -/
def superS (c : MCtx) (d : ClsDecl) (conc : Bool) (ds : SDefs) : Except Err SDefs :=
  match d.parents with
  | .cons P as _ =>
    match (refEnv? c.env P).bind fun eD => (clsOf? eD).map (eD, ·) with
    | some (eD, D) =>
      if Classes.argsNil as || D.params.isEmpty then pure ds
      else do
        let eK := (c.push (.tmpl (.cls d))).env
        let hc : MCtx := { c with env := headEnv eK }
        let unst := argsUnst hc D.params as
        let ovr := supOverridden eD D (Classes.linD eK)
        if conc && unst.isEmpty && ovr.isEmpty then pure ds
        else do
          let ps ← d.params.mapM fun x => do
            let S ← tyS hc x.ty
            pure (x.name, S)
          let rel := relSubst eD eK
          let σA := supSubst hc D.params as rel
          let σD := D.params.map (fun y => (y.name, SPath.var (supArg y.name))) ++ rel
          let Rs ← D.params.mapM fun y => do
            let T ← tyS { c with env := headEnv eD } y.ty
            pure (y.name, T)
          let σS := argsSubst hc D.params as ++ rel
          let keep := unst ++ ovr
          let Ts := ((Rs.filter fun yT => unst.contains yT.1 || (conc && ovr.contains yT.1) ||
              (conc && keep.any fun u => tyFree u yT.2) || (!conc && !supByForm ps σA yT.1 yT.2)).filterMap
              fun yT => (supDropSngl σS yT.1 yT.2).map fun T => (yT.1, substRoots σD T))
          if Ts.isEmpty then pure ds
          else do
            let cap := supCaptured ps Ts
            let σO := cap.map fun x => (x, SPath.var (supOut x))
            let body ← supBinds hc D.params as (supChecks (Ts.map fun yT => (yT.1, substRoots σO yT.2)))
            let qs := supParams cap ps []
            let qs' := if qs.isEmpty then [(nilVar, SType.top)] else qs
            let body' := aliasChain (cap.map fun x => (supOut x, .var x))
              (aliasChain (cap.map fun x => (x, .var (supKeep x))) body)
            pure (.trm ds (superName d.name) (some (allChain qs' .top)) (lamChain qs' body'))
    | none => pure ds
  | .nil => pure ds

/-- The shapes the mapping refuses at a class head: a first parent with one parameter given more arguments,
which scalac tuples into it (probe P02), and an argument of a parent that is no path. -/
def headOk (c : MCtx) (d : ClsDecl) : Except Err Unit :=
  match d.parents with
  | .cons P as _ => do
    match (refEnv? c.env P).bind clsOf? with
    | some D => if D.params.length = 1 && 1 < Classes.argsLen as then throw ⟨P.pos, msgTupled⟩
    | none => pure ()
    if !Classes.argsPaths as then throw ⟨P.pos, msgParentArg⟩
  | .nil => pure ()

/-- The prefix of `new p.K`: `⟦p⟧`, or the binder of the template declaring a bare `K`. -/
def newPre (c : MCtx) (K : ClassRef) : Except Err SPath :=
  match K.pre with
  | some q => pathS c.env q
  | none =>
    match lookupCls K.name c.env with
    | some (_ :: envT) => pure (.var (binderOf envT))
    | _ => throw ⟨K.pos, msgScope K.name⟩

/-- The arity the mapping refuses at `new p.K(ē)`: more than one argument to a `K` with one parameter, which
scalac tuples into it (probes P01, P16).  With no parameter or two or more, the check `Classes.checkNew`
answers "too many arguments" (probe Q29). -/
def newArity (c : MCtx) (K : ClassRef) (n : Nat) : Except Err Unit :=
  match clsKind c.fuel c.env K with
  | .inst e =>
    match clsOf? e with
    | some d => if d.params.length = 1 && 1 < n then throw ⟨K.pos, msgTupled⟩ else pure ()
    | none => pure ()
  | _ => pure ()

/-- `f a₁ … aₙ`, applications nested to the left. -/
def appChain : STm → List STm → STm
  | f, [] => f
  | f, a :: as => appChain (.app f a) as

/-! ## Terms -/

/-- Whether a term is an object literal. -/
def isLit : ScalaRead.Tm → Bool
  | .lit .. => true
  | _ => false

/-- Whether a term is an application. -/
def isApp : ScalaRead.Tm → Bool
  | .app .. => true
  | _ => false

/-- Whether a block ends with the bare name `x`. -/
def returns (x : String) : Stats → Bool
  | .last (.path (.var _ y)) => decide (y = x)
  | _ => false

/-- The path of `val x: q'.type = q`, when both sides are one path. -/
def sameSngl? : Option ScalaRead.Ty → ScalaRead.Tm → Option ScalaRead.Path
  | some (.sngl _ q'), .path q => if decide (q.erase = q'.erase) then some q else none
  | _, _ => none

mutual
/-- A term.  `wr`: a written type stands around it.  `res`: it is a lambda body or a block result.
`under`: the written type a literal stands under. -/
def tmS (c : MCtx) (wr res : Bool) (under : Option ScalaRead.Ty) (t : ScalaRead.Tm) : Except Err STm :=
  match t with
  | .path q => termPath c q
  | .sel u _ a => do
    let u' ← tmS c false false none u
    pure (.proj u' a)
  | .app f u => do
    let f' ← tmS c false false none f
    let u' ← tmS c false false none u
    if res && !wr then pure (.bind .widen wideName (.app f' u') (.var wideName))
    else pure (.app f' u')
  | .lam _ x T b => do
    let T' ← tyOptS c T
    let b' ← tmS (c.push (.param x T false)) wr true none b
    pure (.lam x T' b')
  | .asc _ e T =>
    if isLit e then tmS c true false (some T) e
    else do
      let e' ← tmS c true false none e
      let T' ← tyS c T
      pure (.asc e' T')
  | .block _ ss => statsS c wr ss
  | .lit p s ms =>
    match under with
    | some T => do
      let c' := c.push (.tmpl (.lit p s ms))
      let z := binderOf c'.env
      let ds ← memsS c' (selfDefs z) ms
      let T' ← tyS c T
      pure (litForm z ds T')
    | none => throw ⟨p, msgLitNoType⟩
  | .new _ K as => do
    let args ← argsS c as
    newArity c K args.length
    let pre ← newPre c K
    pure (.«let» newVar none (appChain (pathTm (pre.sel (newName K.name))) (if args.isEmpty then [.var stemName] else args))
      (.var newVar))
termination_by structural t
/-- The arguments of `new`, each an operand. -/
def argsS (c : MCtx) (as : Args) : Except Err (List STm) :=
  match as with
  | .nil => pure []
  | .cons t r => do
    let t' ← tmS c false false none t
    let r' ← argsS c r
    pure (t' :: r')
termination_by structural as
/-- A block's statements, the last one its result. -/
def statsS (c : MCtx) (wr : Bool) (ss : Stats) : Except Err STm :=
  match ss with
  | .last t => tmS c wr true none t
  | .val _ x none e r => do
    let r' ← statsS (c.push (.val x none e)) wr r
    match e with
    | .path q =>
      match kindPath c.fuel c.env none q with
      | .obj _ => do
        let q' ← pathS c.env q
        pure (.alias x q' r')
      | _ => do
        let q' ← termPath c q
        pure (.«let» x none q' r')
    | _ => do
      let e' ← tmS c false false none e
      pure (.bind .widen wideName e' (.«let» x none (.var wideName) r'))
  | .val _ x (some T) e r => do
    let r' ← statsS (c.push (.val x (some T) e)) wr r
    match sameSngl? (some T) e with
    | some q => do
      let q' ← pathS c.env q
      pure (.alias x q' r')
    | none => do
      let T' ← tyS c T
      if returns x r then do
        let e' ← tmS c true false (some T) e
        pure (.«let» x (some T') e' (.var x))
      else if isLit e then do
        let e' ← tmS c true false (some T) e
        pure (.«let» x none e' r')
      else do
        let e' ← tmS c true false none e
        pure (.«let» x (some T') e' r')
termination_by structural ss
/-- The members of a template, appended to `ds`. -/
def memsS (c : MCtx) (ds : SDefs) (ms : Mems) : Except Err SDefs :=
  match ms with
  | .nil => pure ds
  | .obj p o s b r => do
    let c' := c.push (.tmpl (.obj p o s b))
    let z := binderOf c'.env
    let bd ← memsS c' (selfDefs z) b
    memsS c (.trm ds o none (.obj z none bd)) r
  | .typ _ A T r => do
    let T' ← tyS c T
    memsS c (.typ ds A T') r
  | .val p a T e r => do
    let T' ← tyOptS c T
    match e with
    | .lam .. => do
      let e' ← tmS c T.isSome false none e
      memsS c (.trm ds a T' e') r
    | .path q => do
      let q' ← pathS c.env q
      memsS c (.trm ds a T' (pathTm q')) r
    | _ => throw ⟨p, msgField⟩
  | .defn _ f ps R e r => do
    let (doms, cP) ← paramsS c ps
    let R' ← tyOptS cP R
    let body ← tmS cP R.isSome true R e
    memsS c (.trm ds f (R'.map (allChain doms)) (lamChain doms body)) r
  | .cls p k C ps Ps b r => do
    let d : ClsDecl := ⟨p, k, C, ps, Ps, b⟩
    headOk c d
    let ds₁ ← clsDefS c d ds
    let ds₂ ← cmemsS (c.push (.tmpl (.cls d))) (binderOf c.env) C ds₁ b
    let ds₃ ← witnessesS c d ds₂
    let ds₄ ← if k = .concrete then ctorS c d ds₃ >>= superS c d true else superS c d false ds₃
    memsS c ds₄ r
termination_by structural ms
/-- The module functions and `val` witnesses of a class body after `ds`, in text order, each under the receiver
`b : z.K`, `b` the body's binder (D-9, D-10). -/
def cmemsS (cK : MCtx) (z K : String) (ds : SDefs) (ms : CMems) : Except Err SDefs :=
  match ms with
  | .nil => pure ds
  | .typ _ _ _ _ _ r | .alias _ _ _ _ r | .valDecl _ _ _ _ r | .defDecl _ _ _ _ _ r => cmemsS cK z K ds r
  | .val p _ a T e r => do
    let recv : SType := .sel (.var z) K
    let T' ← tyS cK T
    let e' ← match e with
      | .lam .. => tmS cK true false none e
      | .path q => termPath cK q
      | _ => throw ⟨p, msgField⟩
    cmemsS cK z K (.trm ds (modName a K) (some (.all (binderOf cK.env) recv T')) (.lam (binderOf cK.env) (some recv) e')) r
  | .defn _ _ f ps R e r => do
    let recv : SType := .sel (.var z) K
    let (doms, cP) ← paramsS cK ps
    let R' ← tyS cP R
    let body ← tmS cP true true (some R) e
    cmemsS cK z K (.trm ds (modName f K) (some (.all (binderOf cK.env) recv (allChain doms R')))
      (.lam (binderOf cK.env) (some recv) (lamChain doms body))) r
termination_by structural ms
end

/-! ## Programs -/

/-- A parsed and checked file as a surface term.  With members, or with a reference to the wrapper,
the program is `let σ = ν(σ) {ℓself = σ, ⟦ms⟧} in ⟦e⟧` (D-6). -/
def ofScala (F : File) : Except Err STm := do
  let c : MCtx := ⟨ScalaRead.Scope.stemEnv F, F.size + 1⟩
  let body ← match F.ty with
    | none => tmS c false true none F.body
    | some T =>
      if isLit F.body then tmS c true false (some T) F.body
      else do
        let e ← tmS c true false none F.body
        let T' ← tyS c T
        pure (.asc e T')
  let ds ← memsS c (selfDefs stemName) F.mems
  match F.mems with
  | .nil => if tmMentions stemName body then pure (.«let» stemName none (.obj stemName none ds) body) else pure body
  | _ => pure (.«let» stemName none (.obj stemName none ds) body)

/-- The labels of a chain of object names. -/
def chainLabels (Λ : LabelTable) : List String → Option (List Label)
  | [] => some []
  | a :: as => do
    let l ← labelTrm? Λ a
    let ls ← chainLabels Λ as
    pure (l :: ls)

/-- The module chains of a file as label chains from `σ`, the stem's own `[]` first, empty without a
stem (D-13). -/
def modulesOf (Λ : LabelTable) (F : File) (stem : Bool) : List (List Label) :=
  if stem then [] :: (ScalaRead.modules F).filterMap (chainLabels Λ) else []

/-- The label table of a file: the reader's (`ScalaRead.labels`) with the labels of `inhLabels` after the
hidden labels and before `ℓself`. -/
def labelsN (F : File) : LabelTable :=
  let Λ := intern [] 0 0 (F.labelNames ++ ScalaRead.hiddenNames F ++
    (F.mems.clsEnvs (ScalaRead.Scope.stemEnv F)).flatMap inhLabels)
  Λ ++ [(ScalaRead.selfLabelName, .trm (ScalaRead.countTrm Λ))]

/-- Parse, check, map, and number: the file, its term, its table, its modules. -/
def readFile (cs : List Char) : Except Err (File × STm × LabelTable × List (List Label)) := do
  let F ← ScalaRead.parseFile cs
  ScalaRead.check F
  let e ← ofScala F
  let Λ := labelsN F
  pure (F, e, Λ, modulesOf Λ F (isStem e))

/-- The surface term, the label table and the module chains of the characters of a file. -/
def readNominal (cs : List Char) : Except Err (STm × LabelTable × List (List Label)) :=
  (readFile cs).map fun (_, e, Λ, ms) => (e, Λ, ms)

/-! ## The member check R-M (D-19) -/

open Nominal.Source (Ty Dec Ctx) in
mutual
/-- Substitution of paths in a partial term, as `ATm.subst`. -/
def ptmSubst : {s₁ s₂ : Sig} → PTm s₁ → PathSubst s₁ s₂ → PTm s₂
  | _, _, .path p, σ => .path (p.subst σ)
  | _, _, .app p q, σ => .app (p.subst σ) (q.subst σ)
  | _, _, .lam S t, σ => .lam (S.map (·.subst σ)) (ptmSubst t σ.lift)
  | _, _, .new T ds, σ => .new (T.map (·.subst σ.lift)) (pdefsSubst ds σ.lift)
  | _, _, .«let» g W t u, σ => .«let» (g.subst σ) (W.map (·.subst σ)) (ptmSubst t σ) (ptmSubst u σ.lift)
termination_by structural _ _ t => t
/-- Substitution of paths in a definition of a partial term. -/
def pdefSubst : {s₁ s₂ : Sig} → PDef s₁ → PathSubst s₁ s₂ → PDef s₂
  | _, _, .typ A T, σ => .typ A (T.subst σ)
  | _, _, .path a p, σ => .path a (p.subst σ)
  | _, _, .lam a U S t, σ => .lam a (U.map (·.subst σ)) (S.map (·.subst σ)) (ptmSubst t σ.lift)
  | _, _, .new a T ds, σ => .new a (T.map (·.subst σ.lift)) (pdefsSubst ds σ.lift)
  | _, _, .cls C T, σ => .cls C (T.subst σ)
termination_by structural _ _ d => d
/-- Substitution of paths in the definitions of a partial term. -/
def pdefsSubst : {s₁ s₂ : Sig} → PDefs s₁ → PathSubst s₁ s₂ → PDefs s₂
  | _, _, .nil, _ => .nil
  | _, _, .cons ds d, σ => .cons (pdefsSubst ds σ) (pdefSubst d σ)
termination_by structural _ _ ds => ds
end

/-- The answer of the member check. -/
inductive MemberCheck where
  | ok
  /-- A selection names the member `l`, a type member when `typ`, a field otherwise, that no view of its
  prefix declares. -/
  | undeclared (typ : Bool) (l : Label)
  | limit
deriving DecidableEq, Repr

/-- The first answer that is not `ok`, else the second. -/
def MemberCheck.andThen : MemberCheck → MemberCheck → MemberCheck
  | .ok, m => m
  | m, _ => m

/-- The tank of one lookup. -/
def freshTank : Frontend.Fuel.Tank := ⟨Core.defaultFuel, false⟩

open Nominal.Source (Ty Dec Ctx) in
/-- Every field step of `p` names a field that some view of its prefix declares. -/
def pathOk {s : Sig} (Γ : Ctx s) : Path s → MemberCheck
  | .var _ => .ok
  | .sel q a =>
    (pathOk Γ q).andThen
      (let r := Core.views Γ (q.sel a) freshTank
       if r.2.out then .limit else if r.1.isEmpty then .undeclared false a else .ok)

open Nominal.Source (Ty Dec Ctx) in
/-- Some view of `p` declares the type member `A`. -/
def boundOk {s : Sig} (Γ : Ctx s) (p : Path s) (A : Label) : MemberCheck :=
  let r := Core.bounds Γ p A freshTank
  if r.2.out then .limit else if r.1.isEmpty then .undeclared true A else .ok

open Nominal.Source (Ty Dec Ctx) in
mutual
/-- The selections of a written type, refinements included.  `μ(z. U)` binds `z` at itself and
`∀(x : S) U` binds `x` at `S` in `U`, as the vanilla check (`Frontend/Scala.lean:411-420`). -/
def memberTy {s : Sig} (Γ : Ctx s) (T : Ty s) : MemberCheck :=
  match T with
  | .top | .bot => .ok
  | .rcd D => memberDec Γ D
  | .mu U => memberTy (Γ.cons (.mu U)) U
  | .sel p A => (pathOk Γ p).andThen (boundOk Γ p A)
  | .sngl p => pathOk Γ p
  | .all S U => (memberTy Γ S).andThen (memberTy (Γ.cons S) U)
  | .and S U => (memberTy Γ S).andThen (memberTy Γ U)
termination_by structural T
/-- The selections of a declaration, its bounds or its field type. -/
def memberDec {s : Sig} (Γ : Ctx s) (D : Dec s) : MemberCheck :=
  match D with
  | .typ _ S U => (memberTy Γ S).andThen (memberTy Γ U)
  | .trm _ U => memberTy Γ U
termination_by structural D
end

open Nominal.Source (Ty Dec Ctx) in
/-- The selections of a written type, if there is one. -/
def memberOpt {s : Sig} (Γ : Ctx s) : Option (Ty s) → MemberCheck
  | none => .ok
  | some T => memberTy Γ T

open Nominal.Source (Ty Dec Ctx) in
/-- The selections of a class body `μ(this. U) ∧ P`: `U` with `this` at the whole body, so that a member
inherited through `P` is declared, then `P`. -/
def memberCls {s : Sig} (Γ : Ctx s) (T : Ty s) : MemberCheck :=
  match T with
  | .and (.mu U) P => (memberTy (Γ.cons T) U).andThen (memberTy Γ P)
  | _ => memberTy Γ T

open Nominal.Source (Ty Dec Ctx) in
mutual
/-- The written slots of `p`, each in the context the derivation gives it. -/
def memberD : {s : Sig} → {Γ : Ctx s} → {a : ATm s} → {T : Ty s} → AHasTy Γ a T → PTm s → MemberCheck
  | _, _, _, _, .asub d _, p => memberD d p
  | _, Γ, _, _, .alam d, .lam o t => (memberOpt Γ o).andThen (memberD d t)
  | _, _, _, _, .anew d, .new _ ds => memberDefsD d ds
  | _, Γ, _, _, .aletN d₁ d₂, .«let» _ o t u => (memberOpt Γ o).andThen ((memberD d₁ t).andThen (memberD d₂ u))
  | _, Γ, _, _, .aletS d₁ d₂, .«let» _ o t u => (memberOpt Γ o).andThen ((memberD d₁ t).andThen (memberD d₂ u))
  | _, _, _, _, _, _ => .ok
termination_by structural _ _ _ _ d => d
/-- The written slots of the definitions of a partial term, each in the context of its typing derivation. -/
def memberDefsD : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} →
    ADefsTy Γ r ds T → PDefs s → MemberCheck
  | _, _, _, _, _, .adone d, .cons .nil pd => memberDefD d pd
  | _, _, _, _, _, .adcons dds d _, .cons pds pd => (memberDefsD dds pds).andThen (memberDefD d pd)
  | _, _, _, _, _, _, _ => .ok
termination_by structural _ _ _ _ _ d => d
/-- The written slots of one definition of a partial term.  A nested literal's definitions are opened at `r.sel b`,
as `adnew` types them (`Nominal/Frontend/Judgment.lean:144-146`). -/
def memberDefD : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {ad : ADef s} → {D : Dec s} →
    ADefTy Γ r ad D → PDef s → MemberCheck
  | _, Γ, _, _, _, .adtyp, .typ _ T => memberTy Γ T
  | _, Γ, _, _, _, .adcls _, .cls _ T => memberCls Γ T
  | _, Γ, _, _, _, .adlam d, .lam _ o S t => (memberOpt Γ o).andThen (memberD d (.lam S t))
  | _, _, r, .new b _ _, _, .adnew _ dd, .new _ _ pds => memberDefsD dd (pdefsSubst pds (PathSubst.one (r.sel b)))
  | _, _, _, _, _, _, _ => .ok
termination_by structural _ _ _ _ _ d => d
end

/-- The member check of a program that compiled to `r`.  It is `ok` when `e` does not resolve, which
`compileE` has refused already. -/
def members (Λ : LabelTable) (e : STm) (r : (a : ATm []) × Compiled a) : MemberCheck :=
  match resolveP Λ e with
  | some p => memberD r.2.ann p
  | none => .ok

/-! ### Where the refusal sits -/

/-- The name of a label in a table. -/
def nameOf : LabelTable → Label → Option String
  | [], _ => none
  | (n, l') :: Λ, l => if decide (l' = l) then some n else nameOf Λ l

/-- The first step `a` of a path, at its name, with the prefix as text. -/
def stepIn (a : String) : ScalaRead.Path → Option (Pos × String)
  | .this _ | .var _ _ => none
  | .sel q p b => (stepIn a q).or (if decide (b = a) then some (p, q.text) else none)

mutual
/-- The first selection of the member `x` in a written type, a type member when `typ`. -/
def selTy (typ : Bool) (x : String) (T : ScalaRead.Ty) : Option (Pos × String) :=
  match T with
  | .any _ | .nothing _ | .name .. => none
  | .sel p q A =>
    if typ then (if decide (A = x) then some (p, q.text) else none) else stepIn x q
  | .sngl _ q => if typ then none else stepIn x q
  | .refine _ ds => selDecls typ x ds
  | .and S U | .fn _ _ S U => (selTy typ x S).or (selTy typ x U)
termination_by structural T
/-- The first selection of the member `x` in a bound. -/
def selBound (typ : Bool) (x : String) (b : Bound) : Option (Pos × String) :=
  match b with
  | .absent => none
  | .given T => selTy typ x T
termination_by structural b
/-- The first selection of the member `x` in the declarations of a refinement. -/
def selDecls (typ : Bool) (x : String) (ds : Decls) : Option (Pos × String) :=
  match ds with
  | .nil => none
  | .typ _ _ lo hi r => (selBound typ x lo).or ((selBound typ x hi).or (selDecls typ x r))
  | .alias _ _ T r | .val _ _ T r => (selTy typ x T).or (selDecls typ x r)
termination_by structural ds
end

/-- The first selection of the member `x` in a written type, if there is one. -/
def selTyOpt (typ : Bool) (x : String) : Option ScalaRead.Ty → Option (Pos × String)
  | some T => selTy typ x T
  | none => none

/-- The first selection of the member `x` in the parameter types of a list. -/
def selParams (typ : Bool) (x : String) : List Param → Option (Pos × String)
  | [] => none
  | y :: ys => (selTy typ x y.ty).or (selParams typ x ys)

mutual
/-- The first selection of the member `x` in a written type inside a term. -/
def selTm (typ : Bool) (x : String) (t : ScalaRead.Tm) : Option (Pos × String) :=
  match t with
  | .path _ => none
  | .sel u _ _ => selTm typ x u
  | .app f u => (selTm typ x f).or (selTm typ x u)
  | .lam _ _ T b => (selTyOpt typ x T).or (selTm typ x b)
  | .asc _ e T => (selTm typ x e).or (selTy typ x T)
  | .block _ ss => selStats typ x ss
  | .lit _ _ ms => selMems typ x ms
  | .new _ K as => (if typ then none else K.pre.bind (stepIn x)).or (selArgs typ x as)
termination_by structural t
/-- The first selection of the member `x` in a written type inside arguments. -/
def selArgs (typ : Bool) (x : String) (as : Args) : Option (Pos × String) :=
  match as with
  | .nil => none
  | .cons t r => (selTm typ x t).or (selArgs typ x r)
termination_by structural as
/-- The first selection of the member `x` in parents: a class reference `q.C` selects the type `C` on `q`. -/
def selParents (typ : Bool) (x : String) (Ps : ScalaRead.Parents) : Option (Pos × String) :=
  match Ps with
  | .nil => none
  | .cons P as r =>
    let here := match P.pre with
      | some q => if typ then (if decide (P.name = x) then some (P.pos, q.text) else none) else stepIn x q
      | none => none
    here.or ((selArgs typ x as).or (selParents typ x r))
termination_by structural Ps
/-- The first selection of the member `x` in a written type inside a class body. -/
def selCMems (typ : Bool) (x : String) (ms : CMems) : Option (Pos × String) :=
  match ms with
  | .nil => none
  | .typ _ _ _ lo hi r => (selBound typ x lo).or ((selBound typ x hi).or (selCMems typ x r))
  | .alias _ _ _ T r | .valDecl _ _ _ T r => (selTy typ x T).or (selCMems typ x r)
  | .val _ _ _ T e r => (selTy typ x T).or ((selTm typ x e).or (selCMems typ x r))
  | .defDecl _ _ _ ps R r => (selParams typ x ps).or ((selTy typ x R).or (selCMems typ x r))
  | .defn _ _ _ ps R e r =>
    (selParams typ x ps).or ((selTy typ x R).or ((selTm typ x e).or (selCMems typ x r)))
termination_by structural ms
/-- The first selection of the member `x` in a written type inside a block. -/
def selStats (typ : Bool) (x : String) (ss : Stats) : Option (Pos × String) :=
  match ss with
  | .last t => selTm typ x t
  | .val _ _ T e r => (selTyOpt typ x T).or ((selTm typ x e).or (selStats typ x r))
termination_by structural ss
/-- The first selection of the member `x` in a written type inside template members. -/
def selMems (typ : Bool) (x : String) (ms : Mems) : Option (Pos × String) :=
  match ms with
  | .nil => none
  | .obj _ _ _ b r => (selMems typ x b).or (selMems typ x r)
  | .typ _ _ T r => (selTy typ x T).or (selMems typ x r)
  | .val _ _ T e r => (selTyOpt typ x T).or ((selTm typ x e).or (selMems typ x r))
  | .defn _ _ ps R e r =>
    (selParams typ x ps).or ((selTyOpt typ x R).or ((selTm typ x e).or (selMems typ x r)))
  | .cls _ _ _ ps Ps b r =>
    (ps.findSome? fun y => selTy typ x y.ty).or ((selParents typ x Ps).or ((selCMems typ x b).or (selMems typ x r)))
termination_by structural ms
end

/-- The refusal of R-M, at the first selection of the member in the text, or at `1:1`. -/
def undeclaredErr (F : File) (typ : Bool) (x : String) : Err :=
  let what := (if typ then "type " else "value ") ++ x ++ " is not a member"
  match (selMems typ x F.mems).or ((selTyOpt typ x F.ty).or (selTm typ x F.body)) with
  | some (p, q) => ⟨p, what ++ " of the type of " ++ q ++ " (scalac E008)"⟩
  | none => ⟨⟨1, 1⟩, what ++ " (scalac E008)"⟩

/-! ## Outcomes -/

/-- The five kinds of an outcome. -/
inductive Kind where
  | ok
  | rejected
  | unknown
  | limit
  | outside
deriving DecidableEq, Repr

/-- The outcome of a file: compiled, rejected by the typer, rejected by a check of the classes with scalac's
text, out of fuel, or outside the subset. -/
inductive Outcome where
  | ok (Λ : LabelTable) (r : (a : ATm []) × Compiled a)
  | rejected (Λ : LabelTable) (why : PReason)
  | checked (Λ : LabelTable) (err : Err)
  | limit (Λ : LabelTable)
  | outside (err : Err)

/-- The kind of an outcome. -/
def Outcome.kind : Outcome → Kind
  | .ok .. => .ok
  | .rejected .. | .checked .. => .rejected
  | .limit _ => .limit
  | .outside _ => .outside

/-- The budget of a file: the Scala mode and its module chains. -/
def budgetOf (ms : List (List Label)) : Budget := { mode := .scala, modules := ms }

/-- Read, check the classes, compile in the Scala mode, then the member check R-M. -/
def outcome (cs : List Char) : Outcome :=
  match readFile cs with
  | .error err => .outside err
  | .ok (F, e, Λ, ms) =>
    match Classes.check F with
    | .error err => .checked Λ err
    | .ok () =>
      match compileE (budgetOf ms) Λ e with
      | .error .limit => .limit Λ
      | .error r => .rejected Λ r
      | .ok r =>
        match members Λ e r with
        | .ok => .ok Λ r
        | .undeclared typ l => .outside (undeclaredErr F typ ((nameOf Λ l).getD "?"))
        | .limit => .limit Λ

/-- An `ok` outcome is the compilation of the term `readNominal` gives, in the Scala mode with the file's
module chains. -/
theorem outcome_ok {cs : List Char} {Λ : LabelTable} {r : (a : ATm []) × Compiled a}
    (h : outcome cs = .ok Λ r) :
    ∃ e ms, readNominal cs = .ok (e, Λ, ms) ∧ compile { mode := .scala, modules := ms } Λ e = some r := by
  unfold outcome at h
  split at h
  · cases h
  · rename_i F e Λ' ms hr
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
      · rename_i r' hc
        split at h
        · cases h
          refine ⟨e, ms, ?_, ?_⟩
          · simp [readNominal, hr, Except.map]
          · simp [compile, budgetOf] at hc ⊢
            rw [hc]
            rfl
        · cases h
        · cases h

/-- An `ok` outcome's derivation translates to an FCn term that the checker accepts. -/
theorem outcome_checks {cs : List Char} {Λ : LabelTable} {a : ATm []} {c : Compiled a}
    (h : outcome cs = .ok Λ ⟨a, c⟩) : Nominal.FCn.checkTm .nil c.deriv.translate c.ty.translate = true := by
  obtain ⟨_, _, _, hc⟩ := outcome_ok h
  exact compile_checks hc

/-- An `ok` outcome's term is safe: every configuration it reduces to is a normal form or steps, and a
path it reduces to is safe in the store. -/
theorem outcome_safe {cs : List Char} {Λ : LabelTable} {a : ATm []} {c : Compiled a}
    (h : outcome cs = .ok Λ ⟨a, c⟩) {c' : Nominal.Source.Conf} (hc : Nominal.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    (Nominal.Source.NormForm c'.tm ∨ ∃ c'', Nominal.Source.Step c' c'') ∧
    (∀ p, c'.tm = .path p → Nominal.Source.PathSafe c'.store p) := by
  obtain ⟨_, _, _, hk⟩ := outcome_ok h
  exact compile_safe hk hc

/-! ## Tags (plan XII, `ofScala_tags` and `scala_seal_sites`) -/

mutual
/-- Whether every tagged literal of a term sits where the mapping writes one: the body of a constructor
field `new$K` of a template `z`, tagged `z.K`. -/
def tmTags (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ t => tmTags t
  | .obj z _ d => defsTags z d
  | .app t u => tmTags t && tmTags u
  | .proj t _ => tmTags t
  | .«let» _ _ t u => tmTags t && tmTags u
  | .asc t _ => tmTags t
  | .alias _ _ u => tmTags u
  | .bind _ _ t u => tmTags t && tmTags u
  | .inst _ _ _ _ => false
termination_by structural e
/-- The same for the definitions of a template whose binder is `z`. -/
def defsTags (z : String) (d : SDefs) : Bool :=
  match d with
  | .nil => true
  | .typ ds _ _ => defsTags z ds
  | .trm ds a _ t => defsTags z ds && (tmTags t || ctorTags z a t)
  | .cls ds _ _ => defsTags z ds
termination_by structural d
/-- Whether `t` is `λ(x₁ : S₁). … λ(xₙ : Sₙ). ν(i) as z.K {ds}` with `a = new$K` and every tag of `ds`
where `defsTags i` allows it. -/
def ctorTags (z a : String) (t : STm) : Bool :=
  match t with
  | .lam _ _ b => ctorTags z a b
  | .inst i p K ds => decide (a = newName K) && decide (p = .var z) && defsTags i ds
  | _ => false
termination_by structural t
end


/-! ### Lemmas for `ofScala_tags` -/

theorem bind_ok {ε : Type u} {α β : Type v} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pathTm_tags : (p : SPath) → tmTags (pathTm p) = true
  | .var _ => by simp [pathTm, tmTags]
  | .sel p _ => by simp [pathTm, tmTags, pathTm_tags p]

theorem lamChain_tags : (ps : List (String × SType)) → (b : STm) → tmTags (lamChain ps b) = tmTags b
  | [], _ => rfl
  | _ :: ps, b => by simp [lamChain, tmTags, lamChain_tags ps b]

theorem lamChain_ctor (z a : String) : (ps : List (String × SType)) → (b : STm) →
    ctorTags z a (lamChain ps b) = ctorTags z a b
  | [], _ => rfl
  | _ :: ps, b => by simp [lamChain, ctorTags, lamChain_ctor z a ps b]

theorem unstRest_tags : (cs : List String) → tmTags (unstRest cs) = true
  | [] => by simp [unstRest, tmTags]
  | [_] => by simp [unstRest, tmTags]
  | _ :: _ :: cs => by simp [unstRest, tmTags, unstRest_tags (_ :: cs)]

theorem termPath_tags {c : MCtx} {q : ScalaRead.Path} {e : STm} (h : termPath c q = .ok e) : tmTags e = true := by
  unfold termPath at h
  split at h
  · obtain ⟨r', -, h⟩ := bind_ok h
    cases h
    simp [tmTags, pathTm_tags, unstRest_tags]
  · obtain ⟨q', -, h⟩ := bind_ok h
    split at h <;> cases h <;> simp [tmTags, pathTm_tags]

theorem appChain_tags : (f : STm) → (as : List STm) → tmTags f = true → as.all tmTags = true →
    tmTags (appChain f as) = true
  | _, [], hf, _ => hf
  | f, a :: as, hf, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    exact appChain_tags (.app f a) as (by simp [tmTags, hf, ha.1]) ha.2

theorem foldlM_inv {α : Type u} (P : SDefs → Prop) {f : SDefs → α → Except Err SDefs}
    (hf : ∀ ds x ds', f ds x = .ok ds' → P ds → P ds') :
    (xs : List α) → (ds ds' : SDefs) → xs.foldlM f ds = .ok ds' → P ds → P ds'
  | [], ds, ds', h, hp => by cases h; exact hp
  | x :: xs, ds, ds', h, hp => by
    simp only [List.foldlM] at h
    obtain ⟨d₁, h₁, h₂⟩ := bind_ok h
    exact foldlM_inv P hf xs d₁ ds' h₂ (hf ds x d₁ h₁ hp)

theorem witS_tags {z : String} {ds : SDefs} (l b : String) (recv S T : SType) (h : defsTags z ds = true) :
    defsTags z (witS ds l b recv S T) = true := by
  unfold witS
  split
  · exact h
  · simp [defsTags, tmTags, h]

theorem trmWits_tags {z : String} {c : MCtx} {K : String} {eK : List Entry} {L : List (List Entry)} {b : String}
    {recv : SType} {ds ds' : SDefs} {a : String} (h : trmWits c K eK L b recv ds a = .ok ds')
    (hd : defsTags z ds = true) : defsTags z ds' = true := by
  unfold trmWits at h
  split at h
  · cases h; exact hd
  · obtain ⟨FE?, -, h⟩ := bind_ok h
    split at h
    · cases h; exact hd
    · refine foldlM_inv (defsTags z · = true) ?_ _ _ _ h hd
      intro ds₀ eD ds₁ h₁ hp
      obtain ⟨FD?, -, h₁⟩ := bind_ok h₁
      split at h₁
      · cases h₁; exact hp
      · split at h₁ <;> cases h₁
        · exact witS_tags _ _ _ _ _ (witS_tags _ _ _ _ _ hp)
        · exact witS_tags _ _ _ _ _ hp

theorem typWits_tags {z : String} {c : MCtx} {K : String} {eK : List Entry} {L : List (List Entry)} {b : String}
    {recv : SType} {ds ds' : SDefs} {A : String} (h : typWits c K eK L b recv ds A = .ok ds')
    (hd : defsTags z ds = true) : defsTags z ds' = true := by
  unfold typWits at h
  obtain ⟨B?, -, h⟩ := bind_ok h
  split at h
  · cases h; exact hd
  · refine foldlM_inv (defsTags z · = true) ?_ _ _ _ h hd
    intro ds₀ eD ds₁ h₁ hp
    split at h₁
    · cases h₁; exact hp
    · obtain ⟨B'?, -, h₁⟩ := bind_ok h₁
      split at h₁
      · cases h₁; exact hp
      · cases h₁
        exact witS_tags _ _ _ _ _ (witS_tags _ _ _ _ _ hp)

theorem inhWits_tags {z : String} {c : MCtx} {K : String} {eK : List Entry} {L : List (List Entry)} {b : String}
    {recv : SType} {ds ds' : SDefs} {A : String} (h : inhWits c K eK L b recv ds A = .ok ds')
    (hd : defsTags z ds = true) : defsTags z ds' = true := by
  unfold inhWits at h
  refine foldlM_inv (defsTags z · = true) ?_ _ _ _ h hd
  intro ds₀ eD ds₁ h₁ hp
  obtain ⟨B?, -, h₁⟩ := bind_ok h₁
  split at h₁
  · cases h₁; exact hp
  · refine foldlM_inv (defsTags z · = true) ?_ _ _ _ h₁ hp
    intro ds₂ eE ds₃ h₂ hq
    split at h₂
    · cases h₂; exact hq
    · obtain ⟨B'?, -, h₂⟩ := bind_ok h₂
      split at h₂
      · cases h₂; exact hq
      · cases h₂
        exact witS_tags _ _ _ _ _ hq

theorem witnessesS_tags {z : String} {c : MCtx} {d : ScalaRead.ClsDecl} {ds ds' : SDefs}
    (h : witnessesS c d ds = .ok ds') (hd : defsTags z ds = true) : defsTags z ds' = true := by
  unfold witnessesS at h
  obtain ⟨d₁, h₁, h₂⟩ := bind_ok h
  obtain ⟨d₂, h₂, h₃⟩ := bind_ok h₂
  have t₁ := foldlM_inv (defsTags z · = true) (fun _ _ _ hx hp => trmWits_tags hx hp) _ _ _ h₁ hd
  have t₂ := foldlM_inv (defsTags z · = true) (fun _ _ _ hx hp => typWits_tags hx hp) _ _ _ h₂ t₁
  exact foldlM_inv (defsTags z · = true) (fun _ _ _ hx hp => inhWits_tags hx hp) _ _ _ h₃ t₂

theorem clsDefS_tags {z : String} {c : MCtx} {d : ScalaRead.ClsDecl} {ds ds' : SDefs}
    (h : clsDefS c d ds = .ok ds') (hd : defsTags z ds = true) : defsTags z ds' = true := by
  unfold clsDefS at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  simp [defsTags, hd]

theorem appsS_tags : (ys : List String) → tmTags (appsS ys) = true
  | [] => by simp [appsS, tmTags]
  | [_] => by simp [appsS, tmTags]
  | _ :: _ :: ys => by simp [appsS, tmTags, appsS_tags (_ :: ys)]

theorem fwdS_tags {z : String} {ds : SDefs} (f : String) (F : SType) (n : Nat) (zD : SPath) (D i : String)
    (h : defsTags z ds = true) : defsTags z (fwdS ds f F n zD D i) = true := by
  simp [fwdS, defsTags, h, lamChain_tags, tmTags, pathTm_tags, appsS_tags]

theorem instMem_tags {c : MCtx} {eK : List Entry} {L : List (List Entry)} {i : String}
    {arg : List Entry → String → SPath} {ds ds' : SDefs} {m : Classes.IName}
    (h : instMem c eK L i arg ds m = .ok ds') (hd : defsTags i ds = true) : defsTags i ds' = true := by
  unfold instMem at h
  split at h
  · split at h <;> cases h
    · simp [defsTags, hd, pathTm_tags]
    · exact hd
  · split at h
    · obtain ⟨_, -, h⟩ := bind_ok h
      cases h
      simp [defsTags, hd]
    · obtain ⟨_, -, h⟩ := bind_ok h
      cases h
      simp [defsTags, hd]
  · split at h
    · cases h; exact hd
    · split at h
      · split at h
        · cases h; simp [defsTags, hd, pathTm_tags]
        · split at h
          · obtain ⟨t, -, h⟩ := bind_ok h
            split at h <;> cases h
            · simp [defsTags, hd, pathTm_tags]
            · exact hd
          · obtain ⟨F?, -, h⟩ := bind_ok h
            split at h <;> cases h
            · exact fwdS_tags _ _ _ _ _ _ hd
            · exact hd
          · obtain ⟨F?, -, h⟩ := bind_ok h
            split at h <;> cases h
            · exact fwdS_tags _ _ _ _ _ _ hd
            · exact hd
      · cases h; exact hd

theorem instS_tags {c : MCtx} {d : ScalaRead.ClsDecl} {t : STm} (h : instS c d = .ok t) :
    ctorTags (binderOf c.env) (newName d.name) t = true := by
  unfold instS at h
  obtain ⟨ds, h₁, h⟩ := bind_ok h
  cases h
  have : defsTags (binderOf (c.push (Entry.tmpl (.cls d))).env) ds = true :=
    foldlM_inv (defsTags _ · = true) (fun _ _ _ hx hp => instMem_tags hx hp) _ _ _ h₁ (by simp [selfDefs, defsTags, tmTags])
  simp [ctorTags, this]

theorem ctorS_tags {c : MCtx} {d : ScalaRead.ClsDecl} {ds ds' : SDefs} (h : ctorS c d ds = .ok ds')
    (hd : defsTags (binderOf c.env) ds = true) : defsTags (binderOf c.env) ds' = true := by
  unfold ctorS at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨t, ht, h⟩ := bind_ok h
  cases h
  simp [defsTags, hd, lamChain_ctor, instS_tags ht]

theorem aliasChain_tags : (xs : List (String × SPath)) → (b : STm) → tmTags (aliasChain xs b) = tmTags b
  | [], _ => rfl
  | _ :: xs, b => by simp [aliasChain, tmTags, aliasChain_tags xs b]

theorem supChecks_tags : (Ts : List (String × SType)) → tmTags (supChecks Ts) = true
  | [] => by simp [supChecks, tmTags]
  | _ :: r => by simp [supChecks, tmTags, supChecks_tags r]

theorem supBinds_tags {hc : MCtx} : (ys : List ScalaRead.CParam) → (as : Args) → ∀ {b e : STm},
    supBinds hc ys as b = .ok e → tmTags b = true → tmTags e = true
  | [], _, b, e, h, hb => by
    simp only [supBinds] at h
    cases h
    exact hb
  | _ :: _, .nil, b, e, h, hb => by
    simp only [supBinds] at h
    cases h
    exact hb
  | y :: ys, .cons t r, b, e, h, hb => by
    cases t with
    | path q =>
      simp only [supBinds] at h
      obtain ⟨t', ht, h⟩ := bind_ok h
      obtain ⟨rest, hr, h⟩ := bind_ok h
      have tr := supBinds_tags ys r hr hb
      split at h <;> cases h <;> simp [tmTags, tr, termPath_tags ht]
    | _ =>
      simp only [supBinds] at h
      cases h
      exact hb

theorem superS_tags {c : MCtx} {d : ScalaRead.ClsDecl} {conc : Bool} {ds ds' : SDefs}
    (h : superS c d conc ds = .ok ds') (hd : defsTags (binderOf c.env) ds = true) :
    defsTags (binderOf c.env) ds' = true := by
  unfold superS at h
  split at h
  · split at h
    · split at h
      · cases h; exact hd
      · dsimp only at h
        split at h
        · cases h; exact hd
        · obtain ⟨_, -, h⟩ := bind_ok h
          obtain ⟨_, -, h⟩ := bind_ok h
          split at h
          · cases h; exact hd
          · obtain ⟨body, hb, h⟩ := bind_ok h
            cases h
            simp [defsTags, hd, lamChain_tags, aliasChain_tags, supBinds_tags _ _ hb (supChecks_tags _)]
    · cases h; exact hd
  · cases h; exact hd

theorem litForm_tags (z : String) (ds : SDefs) (T : SType) : tmTags (litForm z ds T) = defsTags z ds := by
  simp [litForm, tmTags]

mutual
theorem tmS_tags : (t : ScalaRead.Tm) → ∀ {c : MCtx} {wr res : Bool} {under : Option ScalaRead.Ty} {e : STm},
    tmS c wr res under t = .ok e → tmTags e = true
  | .path q, c, wr, res, under, e, h => by
    simp only [tmS] at h
    exact termPath_tags h
  | .sel u p a, c, wr, res, under, e, h => by
    simp only [tmS] at h
    obtain ⟨u', hu, h⟩ := bind_ok h
    cases h
    simp [tmTags, tmS_tags u hu]
  | .app f u, c, wr, res, under, e, h => by
    simp only [tmS] at h
    obtain ⟨f', hf, h⟩ := bind_ok h
    obtain ⟨u', hu, h⟩ := bind_ok h
    split at h <;> cases h <;> simp [tmTags, tmS_tags f hf, tmS_tags u hu]
  | .lam p x T b, c, wr, res, under, e, h => by
    simp only [tmS] at h
    obtain ⟨T', -, h⟩ := bind_ok h
    obtain ⟨b', hb, h⟩ := bind_ok h
    cases h
    simp [tmTags, tmS_tags b hb]
  | .asc p e₀ T, c, wr, res, under, e, h => by
    simp only [tmS] at h
    split at h
    · exact tmS_tags e₀ h
    · obtain ⟨e', he, h⟩ := bind_ok h
      obtain ⟨T', -, h⟩ := bind_ok h
      cases h
      simp [tmTags, tmS_tags e₀ he]
  | .block p ss, c, wr, res, under, e, h => by
    simp only [tmS] at h
    exact statsS_tags ss h
  | .lit p s ms, c, wr, res, under, e, h => by
    simp only [tmS] at h
    split at h
    · obtain ⟨ds, hds, h⟩ := bind_ok h
      obtain ⟨T', -, h⟩ := bind_ok h
      cases h
      rw [litForm_tags]
      exact memsS_tags ms hds (by simp [selfDefs, defsTags, tmTags])
    · cases h
  | .new p K as, c, wr, res, under, e, h => by
    simp only [tmS] at h
    obtain ⟨args, ha, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨pre, -, h⟩ := bind_ok h
    cases h
    have hargs := argsS_tags as ha
    simp only [tmTags, Bool.and_true]
    apply appChain_tags _ _ (pathTm_tags _)
    split
    · simp [tmTags]
    · exact hargs
theorem argsS_tags : (as : ScalaRead.Args) → ∀ {c : MCtx} {es : List STm}, argsS c as = .ok es → es.all tmTags = true
  | .nil, c, es, h => by
    simp only [argsS] at h
    cases h
    rfl
  | .cons t r, c, es, h => by
    simp only [argsS] at h
    obtain ⟨t', ht, h⟩ := bind_ok h
    obtain ⟨r', hr, h⟩ := bind_ok h
    cases h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨tmS_tags t ht, argsS_tags r hr⟩
theorem statsS_tags : (ss : ScalaRead.Stats) → ∀ {c : MCtx} {wr : Bool} {e : STm}, statsS c wr ss = .ok e →
    tmTags e = true
  | .last t, c, wr, e, h => by
    simp only [statsS] at h
    exact tmS_tags t h
  | .val p x none e₀ r, c, wr, e, h => by
    simp only [statsS] at h
    obtain ⟨r', hr, h⟩ := bind_ok h
    have hr' := statsS_tags r hr
    split at h
    · split at h
      · obtain ⟨q', -, h⟩ := bind_ok h
        cases h
        simp [tmTags, hr']
      · obtain ⟨q', hq, h⟩ := bind_ok h
        cases h
        simp [tmTags, hr', termPath_tags hq]
    · obtain ⟨e', he, h⟩ := bind_ok h
      cases h
      simp [tmTags, hr', tmS_tags e₀ he]
  | .val p x (some T) e₀ r, c, wr, e, h => by
    simp only [statsS] at h
    obtain ⟨r', hr, h⟩ := bind_ok h
    have hr' := statsS_tags r hr
    split at h
    · obtain ⟨q', -, h⟩ := bind_ok h
      cases h
      simp [tmTags, hr']
    · obtain ⟨T', -, h⟩ := bind_ok h
      split at h
      · obtain ⟨e', he, h⟩ := bind_ok h
        cases h
        simp [tmTags, tmS_tags e₀ he]
      · split at h
        · obtain ⟨e', he, h⟩ := bind_ok h
          cases h
          simp [tmTags, hr', tmS_tags e₀ he]
        · obtain ⟨e', he, h⟩ := bind_ok h
          cases h
          simp [tmTags, hr', tmS_tags e₀ he]
theorem memsS_tags : (ms : ScalaRead.Mems) → ∀ {c : MCtx} {ds ds' : SDefs}, memsS c ds ms = .ok ds' →
    defsTags (binderOf c.env) ds = true → defsTags (binderOf c.env) ds' = true
  | .nil, c, ds, ds', h, hd => by
    simp only [memsS] at h
    cases h
    exact hd
  | .obj p o s b r, c, ds, ds', h, hd => by
    simp only [memsS] at h
    obtain ⟨bd, hb, h⟩ := bind_ok h
    have hbd := memsS_tags b hb (by simp [selfDefs, defsTags, tmTags])
    exact memsS_tags r h (by simp [defsTags, tmTags, hd, hbd])
  | .typ p A T r, c, ds, ds', h, hd => by
    simp only [memsS] at h
    obtain ⟨T', -, h⟩ := bind_ok h
    exact memsS_tags r h (by simp [defsTags, hd])
  | .val p a T e₀ r, c, ds, ds', h, hd => by
    simp only [memsS] at h
    obtain ⟨T', -, h⟩ := bind_ok h
    split at h
    · obtain ⟨e', he, h⟩ := bind_ok h
      exact memsS_tags r h (by simp [defsTags, hd, tmS_tags _ he])
    · obtain ⟨q', -, h⟩ := bind_ok h
      exact memsS_tags r h (by simp [defsTags, hd, pathTm_tags])
    · cases h
  | .defn p f ps R e₀ r, c, ds, ds', h, hd => by
    simp only [memsS] at h
    obtain ⟨⟨doms, cP⟩, -, h⟩ := bind_ok h
    obtain ⟨R', -, h⟩ := bind_ok h
    obtain ⟨body, hb, h⟩ := bind_ok h
    exact memsS_tags r h (by simp [defsTags, hd, lamChain_tags, tmS_tags e₀ hb])
  | .cls p k C ps Ps b r, c, ds, ds', h, hd => by
    simp only [memsS] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨d₁, h₁, h⟩ := bind_ok h
    obtain ⟨d₂, h₂, h⟩ := bind_ok h
    obtain ⟨d₃, h₃, h⟩ := bind_ok h
    have t₁ := clsDefS_tags h₁ hd
    have t₂ := cmemsS_tags b h₂ t₁
    have t₃ := witnessesS_tags h₃ t₂
    split at h
    · obtain ⟨d₄, h₄, h⟩ := bind_ok h
      obtain ⟨d₅, h₅, h₄⟩ := bind_ok h₄
      exact memsS_tags r h (superS_tags h₄ (ctorS_tags h₅ t₃))
    · obtain ⟨d₄, h₄, h⟩ := bind_ok h
      exact memsS_tags r h (superS_tags h₄ t₃)
theorem cmemsS_tags : (ms : ScalaRead.CMems) → ∀ {cK : MCtx} {z' z K : String} {ds ds' : SDefs},
    cmemsS cK z K ds ms = .ok ds' → defsTags z' ds = true → defsTags z' ds' = true
  | .nil, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    cases h
    exact hd
  | .typ _ _ _ _ _ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    exact cmemsS_tags r h hd
  | .alias _ _ _ _ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    exact cmemsS_tags r h hd
  | .valDecl _ _ _ _ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    exact cmemsS_tags r h hd
  | .defDecl _ _ _ _ _ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    exact cmemsS_tags r h hd
  | .val p o a T e₀ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    obtain ⟨T', -, h⟩ := bind_ok h
    split at h
    · obtain ⟨e', he, h⟩ := bind_ok h
      exact cmemsS_tags r h (by simp [defsTags, hd, tmTags, tmS_tags _ he])
    · obtain ⟨e', he, h⟩ := bind_ok h
      exact cmemsS_tags r h (by simp [defsTags, hd, tmTags, termPath_tags he])
    · cases h
  | .defn p o f ps R e₀ r, cK, z', z, K, ds, ds', h, hd => by
    simp only [cmemsS] at h
    obtain ⟨⟨doms, cP⟩, -, h⟩ := bind_ok h
    obtain ⟨R', -, h⟩ := bind_ok h
    obtain ⟨body, hb, h⟩ := bind_ok h
    exact cmemsS_tags r h (by simp [defsTags, hd, tmTags, lamChain_tags, tmS_tags e₀ hb])
end

theorem stem_tags {c : MCtx} {ms : ScalaRead.Mems} {body e : STm} (hc : binderOf c.env = stemName)
    (tb : tmTags body = true)
    (h : (do
      let ds ← memsS c (selfDefs stemName) ms
      match ms with
      | .nil => if tmMentions stemName body then pure (.«let» stemName none (.obj stemName none ds) body) else pure body
      | _ => pure (.«let» stemName none (.obj stemName none ds) body)) = Except.ok e) : tmTags e = true := by
  obtain ⟨ds, hds, h⟩ := bind_ok h
  have td : defsTags stemName ds = true := by
    have := memsS_tags ms hds (by rw [hc]; simp [selfDefs, defsTags, tmTags])
    rwa [hc] at this
  split at h
  · split at h <;> cases h
    · simp [tmTags, td, tb]
    · exact tb
  · cases h
    simp [tmTags, td, tb]

theorem ofScala_tags {F : File} {e : STm} (h : ofScala F = .ok e) : tmTags e = true := by
  unfold ofScala at h
  dsimp only at h
  split at h
  · obtain ⟨body, hb, h⟩ := bind_ok h
    exact stem_tags rfl (tmS_tags _ hb) h
  · split at h
    · obtain ⟨body, hb, h⟩ := bind_ok h
      exact stem_tags rfl (tmS_tags _ hb) h
    · obtain ⟨e', he, h⟩ := bind_ok h
      obtain ⟨T', -, h⟩ := bind_ok h
      exact stem_tags rfl (by simp [tmTags, tmS_tags _ he]) h

/-- The term of a file the reader takes is the mapping's. -/
theorem readFile_ofScala {cs : List Char} {F : File} {e : STm} {Λ : LabelTable} {ms : List (List Label)}
    (h : readFile cs = .ok (F, e, Λ, ms)) : ofScala F = .ok e := by
  unfold readFile at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i F' _ _ _ _ e' he
        cases h
        exact he

/-- An `ok` outcome seals only at tagged variables (`compile_seal_sites`), the mapped term carries a tag only on
a constructor's instance literal (`ofScala_tags`), and the derivation carries the certificate `Nom` at the
resolved term's class labels (`compile_nominal_resolved`), whose `SealAt` part gives each seal's class a
`Factor` from the class of the sealed instance. -/
theorem scala_seal_sites {cs : List Char} {Λ : LabelTable} {a : ATm []} {c : Compiled a}
    (h : outcome cs = .ok Λ ⟨a, c⟩) :
    c.ann.SealsTagged ∧ ∃ e ms p, readNominal cs = .ok (e, Λ, ms) ∧ tmTags e = true ∧
      compileE (budgetOf ms) Λ e = .ok ⟨a, c⟩ ∧ resolveP Λ e = some p ∧ c.ann.Nom p.classLabels := by
  unfold outcome at h
  split at h
  · cases h
  · rename_i F e Λ' ms hr
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
      · rename_i r' hc
        split at h
        · cases h
          obtain ⟨p, hp, hn⟩ := compile_nominal_resolved hc
          exact ⟨compile_seal_sites hc, e, ms, p, by simp [readNominal, hr, Except.map],
            ofScala_tags (readFile_ofScala hr), hc, hp, by simpa [budgetOf] using hn⟩
        · cases h
        · cases h


/-! ## The printers -/

/-! ### Why a term has no Scala form -/

/-- Why a written self type has no Scala form. -/
def gapSelfType : String := "a written self type has no Scala form: scalac never writes one (plan IX S-12)"
/-- Why a literal with no written type around it has no Scala form. -/
def gapUntypedLiteral : String := "an object literal needs a written type: scalac types it as Object (plan IX S-12)"
/-- Why a literal whose first definition is not `ℓself = z` has no Scala form. -/
def gapSelfField : String := "a literal whose first definition is not its self-alias field `ℓself` has no Scala form (D-7)"
/-- Why a `μ` whose body is not one refinement has no Scala form. -/
def gapMuBody : String := "a μ whose body is not one refinement has no Scala form (plan IX S-15)"
/-- Why a `μ` binder named inside an inner template has no Scala form. -/
def gapMuOuter : String := "a μ named from inside an inner template has no Scala form: the inner `this` hides it (plan IX S-13)"
/-- Why a literal's binder named inside a dependent function type has no Scala form. -/
def gapLitOuter : String := "a literal named from inside a dependent function type has no Scala form (plan IX S-13)"
/-- Why a `bind` outside the shapes of the mapping has no Scala form. -/
def gapBind : String := "an inserted binding outside the shapes of the mapping has no Scala form"
/-- Why a field that holds no path, lambda or object has no Scala form. -/
def gapField : String := "a field that holds no path, lambda or object has no Scala form (R-R)"
/-- Why a literal ascribed directly has no Scala form. -/
def gapAscLiteral : String := "a literal ascribed directly reads back as `let ℓ = ν(s) {…} in (ℓ : T)` (D-16)"
/-- Why a class definition or a tagged literal has no Scala form (plan XII N6, the cause F-C of N7). -/
def gapClass : String := "a class definition or a tagged literal has no Scala form: the printers do not read the mapping's classes back (plan XII N6)"

/-- The ten reasons of the printers, in the order of their definitions. -/
def gapReasons : List String :=
  [gapSelfType, gapUntypedLiteral, gapSelfField, gapMuBody, gapMuOuter, gapLitOuter, gapBind,
   gapField, gapAscLiteral, gapClass]

/-! ### The context of the printer -/

/-- How a template's binder prints when it is not the innermost template. -/
inductive TForm where
  | stem
  | obj (o : String)
  | lit (self : Option String)
  | ref

/-- A template of the printer: its binder, if any, and its form. -/
structure PT where
  binder : Option String
  form : TForm
  /-- The type members it declares, for a refinement. -/
  typs : List String := []
  /-- The fields it declares, for a refinement. -/
  trms : List String := []

/-- The type members and fields of a chain of declarations. -/
def chainNames : SType → List String × List String
  | .typ A _ _ => ([A], [])
  | .fld a _ => ([], [a])
  | .and S U =>
    let (a, b) := chainNames S
    let (c, d) := chainNames U
    (a ++ c, b ++ d)
  | _ => ([], [])

/-- Whether the member `m` of the refinement bound to `x` prints bare: `x` binds an outer refinement,
and no template inside it declares `m` (D-11 read backwards). -/
def bareOk (x : String) (typ : Bool) (m : String) : List PT → Bool
  | [] => false
  | t :: ts =>
    if decide (t.binder = some x) then (match t.form with | .ref => true | _ => false)
    else if (if typ then t.typs else t.trms).contains m then false
    else bareOk x typ m ts

/-- The context of the printer.  The templates, innermost first.  Whether a dependent function type
stands around.  Whether the type is the body of the `μ` being printed.  Whether a fill is printed.  The
wrapper's name. -/
structure PCtx where
  tmpls : List PT
  dep : Bool
  body : Bool
  fill : Bool
  wrapper : String

/-- Enter a template, which becomes the innermost one. -/
def PCtx.enter (c : PCtx) (t : PT) (body : Bool) : PCtx := { c with tmpls := t :: c.tmpls, body }

/-- The parts of a declaration: in the body of the `μ` being printed it belongs to that refinement,
elsewhere it opens a refinement of its own. -/
def PCtx.member (c : PCtx) : PCtx :=
  if c.body then { c with body := false } else c.enter ⟨none, .ref, [], []⟩ false

/-- The printed root of a template binder that is not innermost. -/
def outerRoot (c : PCtx) (x : String) : List PT → Except String (Option ScalaRead.Path)
  | [] => pure none
  | t :: ts =>
    if decide (t.binder = some x) then
      match t.form with
      | .stem => pure (some (.var .zero c.wrapper))
      | .obj o => pure (some (.var .zero o))
      | .lit (some s) => pure (some (.var .zero s))
      | .lit none => throw gapLitOuter
      | .ref => throw gapMuOuter
    else outerRoot c x ts

/-- A surface path as a Scala path.  The innermost template's binder prints as `this`, an outer
template's as its name, a step `ℓself` not at all (refute-d3 R6). -/
def pathP (c : PCtx) : SPath → Except String ScalaRead.Path
  | .var x =>
    match c.tmpls with
    | t :: _ =>
      if decide (t.binder = some x) && !c.dep then pure (.this .zero)
      else do
        match ← outerRoot c x c.tmpls with
        | some q => pure q
        | none => pure (.var .zero x)
    | [] => pure (.var .zero x)
  | .sel q a =>
    if decide (a = selfName) then pathP c q
    else match q with
      | .var x =>
        if bareOk x false a c.tmpls && !(match c.tmpls with
            | t :: _ => decide (t.binder = some x) && !c.dep
            | [] => false) then pure (.var .zero a)
        else do
          let q' ← pathP c q
          pure (.sel q' .zero a)
      | _ => do
        let q' ← pathP c q
        pure (.sel q' .zero a)

/-- Two chains of declarations, one after the other. -/
def appendDecls (ds es : Decls) : Decls :=
  match ds with
  | .nil => es
  | .typ p A lo hi r => .typ p A lo hi (appendDecls r es)
  | .alias p A T r => .alias p A T (appendDecls r es)
  | .val p a T r => .val p a T (appendDecls r es)

/-- The names a chain of declarations declares, in order. -/
def memName : Decls → List String
  | .nil => []
  | .typ _ A _ _ r | .alias _ A _ r | .val _ A _ r => A :: memName r

/-- Whether a type is the declaration of the hidden self-alias field, `{ℓself : U}` (D-7). -/
def isSelfDec : SType → Bool
  | .fld a _ => decide (a = selfName)
  | _ => false

/-- A surface type as a Scala type, and, when it is a chain of declarations with distinct names, the
chain. -/
def tyP (c : PCtx) (T : SType) : Except String (ScalaRead.Ty × Option Decls) :=
  match T with
  | .top => pure (.any .zero, none)
  | .bot => pure (.nothing .zero, none)
  | .typ A S U => do
    let (S', _) ← tyP c.member S
    let (U', _) ← tyP c.member U
    let d : Decls :=
      if decide (S = U) then .alias .zero A S' .nil
      else .typ .zero A (if decide (S = .bot) then .absent else .given S')
        (if decide (U = .top) then .absent else .given U') .nil
    pure (.refine .zero d, some d)
  | .fld a U => if decide (a = selfName) then pure (.any .zero, none) else do
    let (U', _) ← tyP c.member U
    let d : Decls := .val .zero a U' .nil
    pure (.refine .zero d, some d)
  | .sel p A =>
    match p with
    | .var x =>
      if bareOk x true A c.tmpls && !(match c.tmpls with
          | t :: _ => decide (t.binder = some x) && !c.dep
          | [] => false) then pure (.name .zero A, none)
      else do
        let p' ← pathP c p
        pure (.sel .zero p' A, none)
    | _ => do
      let p' ← pathP c p
      pure (.sel .zero p' A, none)
  | .sngl p => do
    let p' ← pathP c p
    pure (.sngl .zero p', none)
  | .mu x U => if isSelfDec U then pure (.any .zero, none) else do
    let (U', ch) ← tyP (c.enter ⟨some x, .ref, (chainNames U).1, (chainNames U).2⟩ true) U
    match ch with
    | none => throw gapMuBody
    | some _ => pure (U', none)
  | .all x S U => do
    let used := tyMentions x U
    let c' := { c with dep := c.dep || used, body := false }
    let (S', _) ← tyP c' S
    let (U', _) ← tyP c' U
    pure (.fn .zero (if used then some x else none) S' U', none)
  | .and S U => if isSelfDec S then tyP c U else if isSelfDec U then tyP c S else do
    let (S', cs) ← tyP c S
    let (U', cu) ← tyP c U
    match cs, cu with
    | some d, some ds =>
      if (memName d).any (memName ds).contains then pure (.and S' U', none)
      else pure (.refine .zero (appendDecls d ds), some (appendDecls d ds))
    | _, _ => pure (.and S' U', none)
termination_by structural T

/-- A surface type as a Scala type. -/
def tyP' (c : PCtx) (T : SType) : Except String ScalaRead.Ty := (·.1) <$> tyP c T

/-- An optional surface type as an optional Scala type. -/
def tyOptP (c : PCtx) : Option SType → Except String (Option ScalaRead.Ty)
  | none => pure none
  | some T => some <$> tyP' c T

/-! ### Terms -/

/-- Statements as a term: a lone term as itself, more statements as a block. -/
def toTmP : Stats → ScalaRead.Tm
  | .last t => t
  | ss => .block .zero ss

/-- The written type and the term of an ascription, or no type and the term itself. -/
def splitAsc : ScalaRead.Tm → Option ScalaRead.Ty × ScalaRead.Tm
  | .asc _ t T => (some T, t)
  | t => (none, t)

/-- The surface path of a term that is a path. -/
def tmPath? : STm → Option SPath
  | .var x => some (.var x)
  | .proj t a => (tmPath? t).map (·.sel a)
  | _ => none

/-- The written type of the literal form `let ℓ = ν(z) {ds} in (ℓ : T)`. -/
def litFormType : STm → Option SType
  | .«let» y none (.obj _ _ _) (.asc (.var w) T) => if decide (w = y) then some T else none
  | _ => none

/-- Whether a surface term is an object literal. -/
def isObj : STm → Bool
  | .obj .. => true
  | _ => false

/-- Whether a surface term is an ascription of a term that is no object literal. -/
def isAscNonObj : STm → Bool
  | .asc t _ => !isObj t
  | _ => false

/-- Whether a surface term is the variable `x`. -/
def isVar (x : String) : STm → Bool
  | .var y => decide (y = x)
  | _ => false

/-- A block `val x: T = rhs` before the statements `r`.  With `nested`, the `val` opens a block of its
own, since `x` is already a `val` of the enclosing block. -/
def joinVal (nested : Bool) (x : String) (T : Option ScalaRead.Ty) (rhs : ScalaRead.Tm) (r : Stats) : Stats :=
  if nested then .last (.block .zero (.val .zero x T rhs r)) else .val .zero x T rhs r

/-- Two lists of members, one after the other. -/
def appendMems (ds es : Mems) : Mems :=
  match ds with
  | .nil => es
  | .obj p o s b r => .obj p o s b (appendMems r es)
  | .typ p A T r => .typ p A T (appendMems r es)
  | .val p a T e r => .val p a T e (appendMems r es)
  | .defn p f ps R e r => .defn p f ps R e (appendMems r es)
  | .cls p k C ps Ps b r => .cls p k C ps Ps b (appendMems r es)

/-- A def's lists, its result and its body: the binders of the declared type equal those of the
lambdas, at the same domains, at least one. -/
def defSplit? : SType → STm → Option (List (String × SType) × SType × STm)
  | .all x S F, .lam y (some S') t =>
    if decide (x = y) && decide (S = S') && !decide (x = anonName) then
      match defSplit? F t with
      | some (ps, R, b) => some ((x, S) :: ps, R, b)
      | none => some ([(x, S)], F, t)
    else none
  | _, _ => none

/-- The definitions after `ℓself = z`, or `none`. -/
def dropSelf : SDefs → Option SDefs
  | .trm .nil a _ (.var _) => if decide (a = selfName) then some .nil else none
  | .nil => none
  | .typ ds A T => (dropSelf ds).map (.typ · A T)
  | .trm ds a T t => (dropSelf ds).map (.trm · a T t)
  | .cls ds C T => (dropSelf ds).map (.cls · C T)

/-- The self name a literal prints with: none when its binder occurs only as `ℓself = z`. -/
def litSelf (z : String) (d : SDefs) (depth : Nat) : Option String :=
  match dropSelf d with
  | some d' => if defsMention z d' then some ("self" ++ toString depth) else none
  | none => none

mutual
/-- The statements of a surface term.  `block` holds the names a later `val` of the block may not
take. -/
def tmP (c : PCtx) (block : List String) (e : STm) : Except String Stats :=
  match e with
  | .var y => do
    let q ← pathP c (.var y)
    pure (.last (.path q))
  | .proj t a =>
    match tmPath? t with
    | some q => do
      let q' ← pathP c (q.sel a)
      pure (.last (.path q'))
    | none => do
      let t' ← tmP c [] t
      pure (.last (.sel (toTmP t') .zero a))
  | .lam x T t => do
    let T' ← tyOptP c T
    let t' ← tmP c [] t
    pure (.last (.lam .zero x T' (toTmP t')))
  | .obj _ _ _ => throw gapUntypedLiteral
  | .app t u => do
    let t' ← tmP c [] t
    let u' ← tmP c [] u
    pure (.last (.app (toTmP t') (toTmP u')))
  | .asc t T =>
    if isObj t then throw gapAscLiteral
    else do
      let t' ← tmP c [] t
      let T' ← tyP' c T
      pure (.last (.asc .zero (toTmP t') T'))
  | .«let» y none (.obj z T d) (.asc (.var w) U) =>
    if decide (w = y) then
      if T.isSome && !c.fill then throw gapSelfType
      else do
        let ds ← defsP (c.enter ⟨some z, .lit (litSelf z d c.tmpls.length), [], []⟩ false) d
        let U' ← tyP' c U
        pure (.last (.asc .zero (.lit .zero (litSelf z d (c.tmpls.length)) ds) U'))
    else throw gapUntypedLiteral
  | .«let» x none t u => do
    let t' ← tmP c [] t
    let typed := ((litFormType t).isSome || isAscNonObj t) && !isVar x u
    let (T', rhs) := if typed then splitAsc (toTmP t') else (none, toTmP t')
    let nested := block.contains x
    let r ← tmP c (if nested then [x] else x :: block) u
    pure (joinVal nested x T' rhs r)
  | .«let» x (some U) t u => do
    let t' ← tmP c [] t
    let U' ← tyP' c U
    let rhs := match litFormType t with
      | some T => if decide (T = U) then (splitAsc (toTmP t')).2 else toTmP t'
      | none => toTmP t'
    let nested := block.contains x
    let r ← tmP c (if nested then [x] else x :: block) u
    pure (joinVal nested x (some U') rhs r)
  | .alias x p u => do
    let p' ← pathP c p
    let nested := block.contains x
    let r ← tmP c (if nested then [x] else x :: block) u
    pure (joinVal nested x (some (.sngl .zero p')) (.path p') r)
  | .bind .widen v t u =>
    match u with
    | .var w => if decide (w = v) then tmP c block t else throw gapBind
    | .«let» x none (.var w) r =>
      if decide (w = v) then do
        let t' ← tmP c [] t
        let nested := block.contains x
        let r' ← tmP c (if nested then [x] else x :: block) r
        pure (joinVal nested x none (toTmP t') r')
      else throw gapBind
    | _ => throw gapBind
  | .bind .unstable _ t r =>
    match (tmPath? t).bind (unstPath? · r) with
    | some q => do
      let q' ← pathP c q
      pure (.last (.path q'))
    | none => throw gapBind
  | .inst _ _ _ _ => throw gapClass
termination_by structural e
/-- The body of `n ≥ 1` lambdas. -/
def peelP (c : PCtx) (n : Nat) (t : STm) : Except String Stats :=
  match n, t with
  | 1, .lam _ _ b => tmP c [] b
  | n + 2, .lam _ _ b => peelP c (n + 1) b
  | _, _ => throw gapBind
termination_by structural t
/-- Definitions as members, in order. -/
def defsP (c : PCtx) (d : SDefs) : Except String Mems :=
  match d with
  | .nil => throw gapSelfField
  | .trm .nil a _ (.var _) => if decide (a = selfName) then pure .nil else throw gapSelfField
  | .typ ds A T => do
    let r ← defsP c ds
    let T' ← tyP' c T
    pure (appendMems r (.typ .zero A T' .nil))
  | .trm ds a T t => do
    let r ← defsP c ds
    let m ← match t with
      | .obj z S e =>
        if S.isSome && !c.fill then throw gapSelfType
        else do
          let b ← defsP (c.enter ⟨some z, .obj a, [], []⟩ false) e
          pure (Mems.obj .zero a none b .nil)
      | .lam lx lD lb =>
        match T with
        | some F =>
          match defSplit? F t with
          | some (ps, R, body) => do
            let ps' ← ps.mapM fun (x, S) => do
              let S' ← tyP' c S
              pure (⟨.zero, x, S'⟩ : Param)
            let R' ← tyP' c R
            let b ← match ps.length with
              | k + 2 => peelP c (k + 1) lb
              | _ => tmP c [] lb
            let bt := match litFormType body with
              | some T₀ => if decide (T₀ = R) then (splitAsc (toTmP b)).2 else toTmP b
              | none => toTmP b
            pure (Mems.defn .zero a ps' (some R') bt .nil)
          | none => do
            let F' ← tyP' c F
            let D' ← tyOptP c lD
            let b' ← tmP c [] lb
            pure (Mems.val .zero a (some F') (.lam .zero lx D' (toTmP b')) .nil)
        | none => do
          let D' ← tyOptP c lD
          let b' ← tmP c [] lb
          pure (Mems.val .zero a none (.lam .zero lx D' (toTmP b')) .nil)
      | _ =>
        match tmPath? t with
        | some q => do
          let q' ← pathP c q
          match T with
          | some _ => pure (Mems.val .zero a (some (.sngl .zero q')) (.path q') .nil)
          | none => pure (Mems.val .zero a none (.path q') .nil)
        | none => throw gapField
    pure (appendMems r m)
  | .cls _ _ _ => throw gapClass
termination_by structural d
end

/-! ### Programs -/

/-- Whether a surface term is an ascription. -/
def isAscS : STm → Bool
  | .asc .. => true
  | _ => false

/-- The name of a printed wrapper object. -/
def mainName : String := "Main"

/-- A surface term as a file, checked by the reader.  The stem gives the members.  With `fill`, a
written self type is dropped and a typed `let` prints as `({ val x = t; u }: U)`. -/
def toScalaWith (fill : Bool) (e : STm) : Except String File := do
  let cs (z : String) : PCtx :=
    { tmpls := [⟨some z, .stem, [], []⟩], dep := false, body := false, fill, wrapper := mainName }
  let (mems, body, x) ← match e with
    | .«let» x none (.obj y T d) u =>
      if (decide (x = stemName) && decide (y = stemName)) || (fill && (litFormType e).isNone) then do
        if T.isSome && !fill then throw gapSelfType
        let ms ← defsP (cs y) d
        pure (ms, u, x)
      else pure (.nil, e, stemName)
    | _ => pure (.nil, e, stemName)
  let r ← tmP (cs x) [] body
  let (ty, b) := if (litFormType body).isSome || isAscS body then splitAsc (toTmP r) else (none, toTmP r)
  let F : File := ⟨.zero, mainName, mems, ty, b⟩
  match ScalaRead.check F with
  | .ok _ => pure F
  | .error err => throw ("reader: " ++ err.msg)

/-- A surface term as a file, or the reason it has none. -/
def toScala (e : STm) : Except String File := toScalaWith false e

/-! ### Fills -/

/-- The name of a binder introduced under the signature `s`. -/
def binderName (s : Sig) : String := "x" ++ toString s.length

/-- The name of a label in the table, or `?`. -/
def labelText (Λ : LabelTable) (l : Label) : String := (nameOf Λ l).getD "?"

/-- The name of a variable in the list of binder names, or `?`. -/
def varName {s : Sig} (ns : List String) (y : BVar s .var) : String := ns.getD (BVar.idx y) "?"

/-- A pDOT path as a surface path, binders named by the list, labels by the table. -/
def pathOf (Λ : LabelTable) {s : Sig} (ns : List String) : Path s → SPath
  | .var y => .var (varName ns y)
  | .sel q a => .sel (pathOf Λ ns q) (labelText Λ a)

open Nominal.Source (Ty Dec) in
/-- A pDOT type as a surface type, binders named by depth, labels by the table. -/
def sTyOf (Λ : LabelTable) {s : Sig} (ns : List String) (T : Ty s) : SType :=
  match T with
  | .top => .top
  | .bot => .bot
  | .rcd (.typ A S U) => .typ (labelText Λ A) (sTyOf Λ ns S) (sTyOf Λ ns U)
  | .rcd (.trm a U) => .fld (labelText Λ a) (sTyOf Λ ns U)
  | .and S U => .and (sTyOf Λ ns S) (sTyOf Λ ns U)
  | .sel p A => .sel (pathOf Λ ns p) (labelText Λ A)
  | .mu U => .mu (binderName s) (sTyOf Λ (binderName s :: ns) U)
  | .all S U => .all (binderName s) (sTyOf Λ ns S) (sTyOf Λ (binderName s :: ns) U)
  | .sngl p => .sngl (pathOf Λ ns p)
termination_by structural T

mutual
/-- An elaborated term as a surface term with every slot written.  An ascription `let % : T = t in %`
prints as `(t : T)`, a `let` tagged `widen` as `bind .widen`. -/
def fillTm (Λ : LabelTable) : {s : Sig} → List String → ATm s → STm
  | _, ns, .path p => pathTm (pathOf Λ ns p)
  | _, ns, .app p q => .app (pathTm (pathOf Λ ns p)) (pathTm (pathOf Λ ns q))
  | s, ns, .lam S t => .lam (binderName s) (some (sTyOf Λ ns S)) (fillTm Λ (binderName s :: ns) t)
  | s, ns, .new T d =>
    .obj (binderName s) (some (sTyOf Λ (binderName s :: ns) T)) (fillDefs Λ (binderName s :: ns) d)
  | _, ns, .«let» .asc (some T) t (.path (.var .here)) => .asc (fillTm Λ ns t) (sTyOf Λ ns T)
  | s, ns, .«let» .widen none t u => .bind .widen (binderName s) (fillTm Λ ns t) (fillTm Λ (binderName s :: ns) u)
  | s, ns, .«let» _ W t u =>
    .«let» (binderName s) (W.map (sTyOf Λ ns)) (fillTm Λ ns t) (fillTm Λ (binderName s :: ns) u)
termination_by structural _ _ a => a
/-- Elaborated definitions as surface definitions, in order. -/
def fillDefs (Λ : LabelTable) : {s : Sig} → List String → ADefs s → SDefs
  | _, _, .nil => .nil
  | _, ns, .cons ds d => fillDef Λ ns (fillDefs Λ ns ds) d
termination_by structural _ _ d => d
/-- One elaborated definition added after the surface definitions `ds`. -/
def fillDef (Λ : LabelTable) : {s : Sig} → List String → SDefs → ADef s → SDefs
  | _, ns, ds, .typ A T => .typ ds (labelText Λ A) (sTyOf Λ ns T)
  | _, ns, ds, .path a p => .trm ds (labelText Λ a) (some (.sngl (pathOf Λ ns p))) (pathTm (pathOf Λ ns p))
  | s, ns, ds, .lam a S t =>
    .trm ds (labelText Λ a) none (.lam (binderName s) (some (sTyOf Λ ns S)) (fillTm Λ (binderName s :: ns) t))
  | s, ns, ds, .new a T e =>
    .trm ds (labelText Λ a) none
      (.obj (binderName s) (some (sTyOf Λ (binderName s :: ns) T)) (fillDefs Λ (binderName s :: ns) e))
  | _, ns, ds, .cls C T => .cls ds (labelText Λ C) (sTyOf Λ ns T)
termination_by structural _ _ _ d => d
end

/-- The fill of a compiled program as a file, every slot written, `ℓself` dropped. -/
def fillToScala (Λ : LabelTable) (a : ATm []) : Except String File := toScalaWith true (fillTm Λ [] a)

/-! ### Round trips -/

/-- The result of a round trip.  The same resolution, no Scala form, a text the reader refuses, another
resolution, or a term that does not resolve. -/
inductive Trip where
  | same
  | gap (why : String)
  | unreadable (err : Err)
  | differs
  | unresolved
deriving Repr

/-- Print a term, read the text back, and compare the two resolutions (the round trip R). -/
def roundTrip (Λ : LabelTable) (e : STm) : Trip :=
  match resolveP Λ e with
  | none => .unresolved
  | some p =>
    match toScala e with
    | .error why => .gap why
    | .ok F =>
      match readNominal (ScalaRead.print F) with
      | .error err => .unreadable err
      | .ok (e', _, _) => if decide (resolveP Λ e' = some p) then .same else .differs

/-! ### Outcomes as text -/

/-- A closed pDOT type as Scala text, or the reason it has none. -/
def tyText (Λ : LabelTable) (T : Nominal.Source.Ty []) : String :=
  let c : PCtx := { tmpls := [], dep := false, body := false, fill := true, wrapper := mainName }
  match tyP' c (sTyOf Λ [] T) with
  | .ok T' => String.ofList (ScalaRead.Print.ty none T')
  | .error why => "(no Scala form: " ++ why ++ ")"

/-- The text of a reason of the pDOT typer. -/
def treasonText (Λ : LabelTable) : TReason → String
  | .selfSingleton _ => "a path at its own singleton, which no pDOT rule concludes (N4)"
  | .notTight b => "a nested literal whose type member " ++ labelText Λ b ++ " is no alias"
  | .dupLabel l => "two definitions of " ++ labelText Λ l
  | .fieldNotFun l => "the field " ++ labelText Λ l ++ " holds a lambda at a type that is no function type"
  | .noField a => "no view declares the field " ++ labelText Λ a
  | .notFunction => "the callee has no function type"
  | .argMismatch => "the argument meets no domain of the callee"
  | .literalGoal => "a literal meets a goal only through a let"

/-- The text of a reason the front end rejects a program. -/
def reasonText (Λ : LabelTable) : PReason → String
  | .missingParamType _ => "missing parameter type (scalac E081)"
  | .cyclicRef l => "recursive value " ++ labelText Λ l ++ " needs type (scalac E044)"
  | .needsExplicitType l => labelText Λ l ++ " needs an explicit type"
  | .ambiguous l => "the candidates of " ++ labelText Λ l ++ " have no least type"
  | .landed r => treasonText Λ r
  | .mismatch => "Type mismatch"
  | .limit => "Recursion limit exceeded"

/-- The text of an outcome.  `ok` with the type, `rejected` with the reason, `limit`, or `outside` at a
line and column with the refusal's message. -/
def Outcome.text : Outcome → String
  | .ok Λ r => "ok : " ++ tyText Λ r.2.ty
  | .rejected Λ r => "rejected: " ++ reasonText Λ r
  | .checked _ e => "rejected " ++ toString e.pos.line ++ ":" ++ toString e.pos.col ++ ": " ++ e.msg
  | .limit _ => "limit: Recursion limit exceeded"
  | .outside e => "outside " ++ toString e.pos.line ++ ":" ++ toString e.pos.col ++ ": " ++ e.msg

end NominalFrontend.Scala
