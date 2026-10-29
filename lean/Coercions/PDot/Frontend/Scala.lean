import Coercions.PDot.Frontend.Pipeline
import Coercions.PDot.Frontend.ScalaRead.Scope
import Coercions.PDot.Frontend.ScalaRead.Print

/-!
# Scala programs in the pDOT front end

The reader of `PDot/Frontend/ScalaRead/` turns the characters of a `.scala` file into a `File` and
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

Three flags of `tmS` place these.  `wr` says that a written type stands around the term.  `res` says
that the term is a lambda body or a block result.  `under` is the written type a literal stands under,
since a literal is only read under one (D-16).

`readFile` parses (`ScalaRead.parseFile`), checks (`ScalaRead.check`), maps (`ofScala`), numbers the
member names (`ScalaRead.labels`) and gives the module chains as label chains from `σ` (D-13).
`readPDot` is its projection to the term, the table and the chains.  Every function is structural.

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
theorems say that an `ok` outcome is the compilation of the term `readPDot` gives, that its
derivation checks in FCp, and that its term is safe.

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
-/

namespace PDotFrontend.Scala

open ScalaSyntax (Pos Err)
open Paths.FCdot (Sig BVar Label Rename Path PathSubst)
open PDotFrontend.ScalaRead (File Mems Stats Decls Bound Param)
open PDotFrontend.ScalaRead.Scope (Entry lookup lookupTyp thisOf kindPath)

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
termination_by structural e
/-- Whether `b` occurs in a list of definitions. -/
def defsMention (b : String) (d : SDefs) : Bool :=
  match d with
  | .nil => false
  | .typ ds _ T => defsMention b ds || tyMentions b T
  | .trm ds _ T t => defsMention b ds || tyOptMentions b T || tmMentions b t
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

/-- A path of a written type: the root by the scope, `this` and a self name as the template's binder,
a bare member `m` of `r` as `⟦r⟧.m`. -/
def pathS (env : List Entry) : ScalaRead.Path → Except Err SPath
  | .this p =>
    match thisOf env with
    | some env' => pure (.var (binderOf env'))
    | none => throw ⟨p, msgThisOutside⟩
  | .var p x =>
    match lookup x env with
    | .param .. | .val .. => pure (.var x)
    | .self env' => pure (.var (binderOf env'))
    | .member env' => pure (.sel (.var (binderOf env')) x)
    | _ => throw ⟨p, msgScope x⟩
  | .sel q _ a => do
    let q' ← pathS env q
    pure (.sel q' a)

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
    match (kindPath c.fuel c.env none q).word with
    | .obj | .lit => pure (.proj (pathTm q') selfName)
    | _ => pure (pathTm q')

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
termination_by structural t
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
        pure (.«let» x none (.asc e' T') r')
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

/-- Parse, check, map, and number: the file, its term, its table, its modules. -/
def readFile (cs : List Char) : Except Err (File × STm × LabelTable × List (List Label)) := do
  let F ← ScalaRead.parseFile cs
  ScalaRead.check F
  let e ← ofScala F
  let Λ := ScalaRead.labels F
  pure (F, e, Λ, modulesOf Λ F (isStem e))

/-- The surface term, the label table and the module chains of the characters of a file. -/
def readPDot (cs : List Char) : Except Err (STm × LabelTable × List (List Label)) :=
  (readFile cs).map fun (_, e, Λ, ms) => (e, Λ, ms)

/-! ## The member check R-M (D-19) -/

open PDot.Source (Ty Dec Ctx) in
mutual
/-- Substitution of paths in a partial term, as `ATm.subst`. -/
def ptmSubst : {s₁ s₂ : Sig} → PTm s₁ → PathSubst s₁ s₂ → PTm s₂
  | _, _, .path p, σ => .path (p.subst σ)
  | _, _, .app p q, σ => .app (p.subst σ) (q.subst σ)
  | _, _, .lam S t, σ => .lam (S.map (·.subst σ)) (ptmSubst t σ.lift)
  | _, _, .new T ds, σ => .new (T.map (·.subst σ.lift)) (pdefsSubst ds σ.lift)
  | _, _, .«let» g W t u, σ => .«let» g (W.map (·.subst σ)) (ptmSubst t σ) (ptmSubst u σ.lift)
termination_by structural _ _ t => t
/-- Substitution of paths in a definition of a partial term. -/
def pdefSubst : {s₁ s₂ : Sig} → PDef s₁ → PathSubst s₁ s₂ → PDef s₂
  | _, _, .typ A T, σ => .typ A (T.subst σ)
  | _, _, .path a p, σ => .path a (p.subst σ)
  | _, _, .lam a U S t, σ => .lam a (U.map (·.subst σ)) (S.map (·.subst σ)) (ptmSubst t σ.lift)
  | _, _, .new a T ds, σ => .new a (T.map (·.subst σ.lift)) (pdefsSubst ds σ.lift)
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

open PDot.Source (Ty Dec Ctx) in
/-- Every field step of `p` names a field that some view of its prefix declares. -/
def pathOk {s : Sig} (Γ : Ctx s) : Path s → MemberCheck
  | .var _ => .ok
  | .sel q a =>
    (pathOk Γ q).andThen
      (let r := Core.views Γ (q.sel a) freshTank
       if r.2.out then .limit else if r.1.isEmpty then .undeclared false a else .ok)

open PDot.Source (Ty Dec Ctx) in
/-- Some view of `p` declares the type member `A`. -/
def boundOk {s : Sig} (Γ : Ctx s) (p : Path s) (A : Label) : MemberCheck :=
  let r := Core.bounds Γ p A freshTank
  if r.2.out then .limit else if r.1.isEmpty then .undeclared true A else .ok

open PDot.Source (Ty Dec Ctx) in
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

open PDot.Source (Ty Dec Ctx) in
/-- The selections of a written type, if there is one. -/
def memberOpt {s : Sig} (Γ : Ctx s) : Option (Ty s) → MemberCheck
  | none => .ok
  | some T => memberTy Γ T

open PDot.Source (Ty Dec Ctx) in
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
as `adnew` types them (`PDot/Frontend/Judgment.lean:123-126`). -/
def memberDefD : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {ad : ADef s} → {D : Dec s} →
    ADefTy Γ r ad D → PDef s → MemberCheck
  | _, Γ, _, _, _, .adtyp, .typ _ T => memberTy Γ T
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
termination_by structural t
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

/-- The outcome of a file: compiled, rejected by the typer, out of fuel, or outside the subset. -/
inductive Outcome where
  | ok (Λ : LabelTable) (r : (a : ATm []) × Compiled a)
  | rejected (Λ : LabelTable) (why : PReason)
  | limit (Λ : LabelTable)
  | outside (err : Err)

/-- The kind of an outcome. -/
def Outcome.kind : Outcome → Kind
  | .ok .. => .ok
  | .rejected .. => .rejected
  | .limit _ => .limit
  | .outside _ => .outside

/-- The budget of a file: the Scala mode and its module chains. -/
def budgetOf (ms : List (List Label)) : Budget := { mode := .scala, modules := ms }

/-- Read, compile in the Scala mode, then the member check R-M. -/
def outcome (cs : List Char) : Outcome :=
  match readFile cs with
  | .error err => .outside err
  | .ok (F, e, Λ, ms) =>
    match compileE (budgetOf ms) Λ e with
    | .error .limit => .limit Λ
    | .error r => .rejected Λ r
    | .ok r =>
      match members Λ e r with
      | .ok => .ok Λ r
      | .undeclared typ l => .outside (undeclaredErr F typ ((nameOf Λ l).getD "?"))
      | .limit => .limit Λ

/-- An `ok` outcome is the compilation of the term `readPDot` gives, in the Scala mode with the file's
module chains. -/
theorem outcome_ok {cs : List Char} {Λ : LabelTable} {r : (a : ATm []) × Compiled a}
    (h : outcome cs = .ok Λ r) :
    ∃ e ms, readPDot cs = .ok (e, Λ, ms) ∧ compile { mode := .scala, modules := ms } Λ e = some r := by
  unfold outcome at h
  split at h
  · cases h
  · rename_i F e Λ' ms hr
    split at h
    · cases h
    · cases h
    · rename_i r' hc
      split at h
      · cases h
        refine ⟨e, ms, ?_, ?_⟩
        · simp [readPDot, hr, Except.map]
        · simp [compile, budgetOf] at hc ⊢
          rw [hc]
          rfl
      · cases h
      · cases h

/-- An `ok` outcome's derivation translates to an FCp term that the checker accepts. -/
theorem outcome_checks {cs : List Char} {Λ : LabelTable} {a : ATm []} {c : Compiled a}
    (h : outcome cs = .ok Λ ⟨a, c⟩) : PDot.FCp.checkTm .nil c.deriv.translate c.ty.translate = true := by
  obtain ⟨_, _, _, hc⟩ := outcome_ok h
  exact compile_checks hc

/-- An `ok` outcome's term is safe: every configuration it reduces to is a normal form or steps, and a
path it reduces to is safe in the store. -/
theorem outcome_safe {cs : List Char} {Λ : LabelTable} {a : ATm []} {c : Compiled a}
    (h : outcome cs = .ok Λ ⟨a, c⟩) {c' : PDot.Source.Conf} (hc : PDot.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    (PDot.Source.NormForm c'.tm ∨ ∃ c'', PDot.Source.Step c' c'') ∧
    (∀ p, c'.tm = .path p → PDot.Source.PathSafe c'.store p) := by
  obtain ⟨_, _, _, hk⟩ := outcome_ok h
  exact compile_safe hk hc

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
/-- Why a typed `let` whose body is not its variable has no Scala form. -/
def gapLetType : String := "`let x : U = t in u` with `u` not `x` has no Scala form (plan IX S-11)"
/-- Why a `bind` outside the shapes of the mapping has no Scala form. -/
def gapBind : String := "an inserted binding outside the shapes of the mapping has no Scala form"
/-- Why a field that holds no path, lambda or object has no Scala form. -/
def gapField : String := "a field that holds no path, lambda or object has no Scala form (R-R)"
/-- Why a literal ascribed directly has no Scala form. -/
def gapAscLiteral : String := "a literal ascribed directly reads back as `let ℓ = ν(s) {…} in (ℓ : T)` (D-16)"

/-- The ten reasons of the printers, in the order of their definitions. -/
def gapReasons : List String :=
  [gapSelfType, gapUntypedLiteral, gapSelfField, gapMuBody, gapMuOuter, gapLitOuter, gapLetType, gapBind,
   gapField, gapAscLiteral]

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
  | .mu x U => do
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
      match memName d with
      | [A] =>
        if (memName ds).contains A then pure (.and S' U', none)
        else pure (.refine .zero (appendDecls d ds), some (appendDecls d ds))
      | _ => pure (.and S' U', none)
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

/-- The path of an unstable chain `bind .unstable ·u q (…)`, read back (D-10). -/
def unstPath? (q : SPath) : STm → Option SPath
  | .var _ => some q
  | .proj (.var _) a => some (q.sel a)
  | .bind .unstable _ (.proj (.var _) a) r => unstPath? (q.sel a) r
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
  | .«let» x (some U) t u =>
    if isVar x u then do
      let t' ← tmP c [] t
      let U' ← tyP' c U
      let rhs := match litFormType t with
        | some T => if decide (T = U) then (splitAsc (toTmP t')).2 else toTmP t'
        | none => toTmP t'
      let nested := block.contains x
      let r ← tmP c (if nested then [x] else x :: block) u
      pure (joinVal nested x (some U') rhs r)
    else if c.fill then do
      let t' ← tmP c [] t
      let U' ← tyP' c U
      let r ← tmP c [x] u
      pure (.last (.asc .zero (.block .zero (.val .zero x none (toTmP t') r)) U'))
    else throw gapLetType
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

open PDot.Source (Ty Dec) in
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
      match readPDot (ScalaRead.print F) with
      | .error err => .unreadable err
      | .ok (e', _, _) => if decide (resolveP Λ e' = some p) then .same else .differs

/-! ### Outcomes as text -/

/-- A closed pDOT type as Scala text, or the reason it has none. -/
def tyText (Λ : LabelTable) (T : PDot.Source.Ty []) : String :=
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
  | .limit _ => "limit: Recursion limit exceeded"
  | .outside e => "outside " ++ toString e.pos.line ++ ":" ++ toString e.pos.col ++ ": " ++ e.msg

end PDotFrontend.Scala
