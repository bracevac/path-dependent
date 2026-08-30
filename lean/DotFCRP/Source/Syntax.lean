import DotFCR.Source.Runtime

/-!
# Traceable-path DOT syntax

`DotFCRP` is the finite, transparent-path extension of `DotFCR`.  A stable
path has a variable root followed by zero or more term-field selections.  In
particular, `r.a.b` is represented by two applications of `Path.select`.

Only paths occur in type selections and singleton types.  Arbitrary terms are
deliberately not paths; this is the syntactic half of the M6 boundary between
transparent aliases and opaque or dynamically computed receivers.
-/

namespace DotFCRP.Source

open DotFC

/-- Term and type-member labels share the source-level natural-number space. -/
abbrev Name : Type := Nat

/-- Stable paths: a scoped variable root and a finite term-label spine. -/
inductive Path : Sig → Type where
  | var {scope : Sig} (root : BVar scope .term) : Path scope
  | select {scope : Sig} (receiver : Path scope) (label : Name) : Path scope
deriving DecidableEq

namespace Path

/-- Rename the root of a stable path; the selection spine is unchanged. -/
def rename {source target : Sig} (path : Path source)
    (rho : Rename source target) : Path target :=
  match path with
  | .var root => .var (rho.var root)
  | .select receiver label => .select (receiver.rename rho) label

/-- Weaken a path below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (path : Path scope) :
    Path (scope ▹ kind) :=
  path.rename Rename.succ

/-- The variable at the root of a path. -/
def root {scope : Sig} : Path scope → BVar scope .term
  | .var rootVariable => rootVariable
  | .select receiver _ => receiver.root

/-- The labels after a path's variable root, in source order. -/
def labels {scope : Sig} : Path scope → List Name
  | .var _ => []
  | .select receiver label => receiver.labels ++ [label]

@[simp]
theorem rename_id {scope : Sig} (path : Path scope) :
    path.rename Rename.id = path := by
  induction path with
  | var => rfl
  | select receiver label induction => simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} (path : Path first)
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (path.rename firstRename).rename secondRename =
      path.rename (firstRename.comp secondRename) := by
  induction path with
  | var => rfl
  | select receiver label induction => simp [rename, induction]

@[simp]
theorem root_rename {source target : Sig} (path : Path source)
    (rho : Rename source target) :
    (path.rename rho).root = rho.var path.root := by
  induction path with
  | var => rfl
  | select receiver label induction => simpa [rename, root] using induction

@[simp]
theorem labels_rename {source target : Sig} (path : Path source)
    (rho : Rename source target) :
    (path.rename rho).labels = path.labels := by
  induction path with
  | var => rfl
  | select receiver label induction => simp [rename, labels, induction]

end Path

/-- Simultaneous substitution of stable paths for term variables. -/
structure PathSubst (source target : Sig) where
  var : BVar source .term → Path target

namespace PathSubst

@[ext]
theorem ext {source target : Sig} {first second : PathSubst source target}
    (equal : ∀ root, first.var root = second.var root) : first = second := by
  cases first
  cases second
  congr
  funext root
  exact equal root

/-- Identity path substitution. -/
def id {scope : Sig} : PathSubst scope scope where
  var := Path.var

/-- Regard a variable renaming as a path substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    PathSubst source target where
  var := fun root => .var (rho.var root)

/-- Lift a substitution through a term binder. -/
def lift {source target : Sig} (substitution : PathSubst source target) :
    PathSubst (source ▹ .term) (target ▹ .term) where
  var := fun
    | .here => .var .here
    | .there root => (substitution.var root).weaken

/-- Replace the newest term binder by a stable path. -/
def openAt {scope : Sig} (replacement : Path scope) :
    PathSubst (scope ▹ .term) scope where
  var := fun
    | .here => replacement
    | .there root => .var root

@[simp]
theorem lift_id {scope : Sig} :
    (id (scope := scope)).lift =
      (id : PathSubst (scope ▹ .term) (scope ▹ .term)) := by
  ext root
  cases root <;> rfl

end PathSubst

namespace Path

/-- Substitute path roots while preserving selection spines. -/
def subst {source target : Sig} (path : Path source)
    (substitution : PathSubst source target) : Path target :=
  match path with
  | .var root => substitution.var root
  | .select receiver label => .select (receiver.subst substitution) label

/-- Open a path below one term binder. -/
def «open» {scope : Sig} (path : Path (scope ▹ .term))
    (replacement : Path scope) : Path scope :=
  path.subst (PathSubst.openAt replacement)

@[simp]
theorem subst_id {scope : Sig} (path : Path scope) :
    path.subst PathSubst.id = path := by
  induction path with
  | var => rfl
  | select receiver label induction => simp [subst, induction]

@[simp]
theorem subst_ofRename {source target : Sig} (path : Path source)
    (rho : Rename source target) :
    path.subst (PathSubst.ofRename rho) = path.rename rho := by
  induction path with
  | var => rfl
  | select receiver label induction => simp [subst, rename, induction]

@[simp]
theorem open_here {scope : Sig} (replacement : Path scope) :
    (Path.var (.here : BVar (scope ▹ .term) .term)).open replacement =
      replacement := rfl

@[simp]
theorem open_there {scope : Sig} (root : BVar scope .term)
    (replacement : Path scope) :
    (Path.var (.there root : BVar (scope ▹ .term) .term)).open replacement =
      .var root := rfl

end Path

/-! ## Types and terms -/

/-- Recursive DOT types whose selections may use arbitrary stable paths and
whose singleton type records a stable path identity. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | all {scope : Sig} (domain : Ty scope)
      (codomain : Ty (scope ▹ .term)) : Ty scope
  | member {scope : Sig} (label : Name) (lower upper : Ty scope) : Ty scope
  | sel {scope : Sig} (path : Path scope) (label : Name) : Ty scope
  | singleton {scope : Sig} (path : Path scope) : Ty scope
  | inter {scope : Sig} (left right : Ty scope) : Ty scope
  | mu {scope : Sig} (body : Ty (scope ▹ .term)) : Ty scope
deriving DecidableEq

/-- One exact type definition. -/
structure TypeDef (scope : Sig) where
  label : Name
  witness : Ty scope
deriving DecidableEq

/-- Path-DOT terms.  Variables and ANF applications now accept stable paths;
recursive type-member objects remain explicit and erase statically. -/
inductive Tm : Sig → Type where
  | ref {scope : Sig} (path : Path scope) : Tm scope
  | lam {scope : Sig} (domain : Ty scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | obj {scope : Sig} (definitions : List (TypeDef scope)) : Tm scope
  | recObj {scope : Sig}
      (definitions : List (TypeDef (scope ▹ .term))) : Tm scope
  | app {scope : Sig} (function argument : Path scope) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
deriving DecidableEq

namespace Ty

def exact {scope : Sig} (label : Name) (witness : Ty scope) : Ty scope :=
  .member label witness witness

def rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (domain.rename rho) (codomain.rename rho.lift)
  | .member label lower upper =>
      .member label (lower.rename rho) (upper.rename rho)
  | .sel path label => .sel (path.rename rho) label
  | .singleton path => .singleton (path.rename rho)
  | .inter left right => .inter (left.rename rho) (right.rename rho)
  | .mu body => .mu (body.rename rho.lift)

def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename Rename.succ

def subst {source target : Sig} (type : Ty source)
    (substitution : PathSubst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain =>
      .all (domain.subst substitution) (codomain.subst substitution.lift)
  | .member label lower upper =>
      .member label (lower.subst substitution) (upper.subst substitution)
  | .sel path label => .sel (path.subst substitution) label
  | .singleton path => .singleton (path.subst substitution)
  | .inter left right =>
      .inter (left.subst substitution) (right.subst substitution)
  | .mu body => .mu (body.subst substitution.lift)

def «open» {scope : Sig} (type : Ty (scope ▹ .term))
    (replacement : Path scope) : Ty scope :=
  type.subst (PathSubst.openAt replacement)

@[simp]
theorem rename_id {scope : Sig} (type : Ty scope) :
    type.rename Rename.id = type := by
  induction type with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, lowerInduction, upperInduction]
  | sel path label => simp [rename]
  | singleton path => simp [rename]
  | inter left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | mu body induction => simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} (type : Ty first)
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (type.rename firstRename).rename secondRename =
      type.rename (firstRename.comp secondRename) := by
  induction type generalizing second third with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction, Rename.lift_comp]
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, lowerInduction, upperInduction]
  | sel path label => simp [rename]
  | singleton path => simp [rename]
  | inter left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | mu body induction =>
      simp [rename, induction, Rename.lift_comp]

@[simp]
theorem subst_id {scope : Sig} (type : Ty scope) :
    type.subst PathSubst.id = type := by
  induction type with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [subst, domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp [subst, lowerInduction, upperInduction]
  | sel path label => simp [subst]
  | singleton path => simp [subst]
  | inter left right leftInduction rightInduction =>
      simp [subst, leftInduction, rightInduction]
  | mu body induction => simp [subst, induction]

end Ty

namespace TypeDef

def exactTy {scope : Sig} (definition : TypeDef scope) : Ty scope :=
  .exact definition.label definition.witness

def rename {source target : Sig} (definition : TypeDef source)
    (rho : Rename source target) : TypeDef target where
  label := definition.label
  witness := definition.witness.rename rho

def subst {source target : Sig} (definition : TypeDef source)
    (substitution : PathSubst source target) : TypeDef target where
  label := definition.label
  witness := definition.witness.subst substitution

@[simp]
theorem rename_id {scope : Sig} (definition : TypeDef scope) :
    definition.rename Rename.id = definition := by
  cases definition
  simp [rename]

end TypeDef

namespace TypeDefs

def exact {scope : Sig} : List (TypeDef scope) → Ty scope
  | [] => .top
  | [definition] => definition.exactTy
  | definition :: remaining => .inter definition.exactTy (exact remaining)

def rename {source target : Sig} (definitions : List (TypeDef source))
    (rho : Rename source target) : List (TypeDef target) :=
  definitions.map fun definition => definition.rename rho

def subst {source target : Sig} (definitions : List (TypeDef source))
    (substitution : PathSubst source target) : List (TypeDef target) :=
  definitions.map fun definition => definition.subst substitution

@[simp]
theorem rename_id {scope : Sig} (definitions : List (TypeDef scope)) :
    rename definitions Rename.id = definitions := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction => simp [rename]

end TypeDefs

namespace Tm

def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .ref path => .ref (path.rename rho)
  | .lam domain body => .lam (domain.rename rho) (body.rename rho.lift)
  | .obj definitions => .obj (TypeDefs.rename definitions rho)
  | .recObj definitions => .recObj (TypeDefs.rename definitions rho.lift)
  | .app function argument => .app (function.rename rho) (argument.rename rho)
  | .let' rhs body => .let' (rhs.rename rho) (body.rename rho.lift)

def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

def subst {source target : Sig} (term : Tm source)
    (substitution : PathSubst source target) : Tm target :=
  match term with
  | .ref path => .ref (path.subst substitution)
  | .lam domain body =>
      .lam (domain.subst substitution) (body.subst substitution.lift)
  | .obj definitions => .obj (TypeDefs.subst definitions substitution)
  | .recObj definitions =>
      .recObj (TypeDefs.subst definitions substitution.lift)
  | .app function argument =>
      .app (function.subst substitution) (argument.subst substitution)
  | .let' rhs body =>
      .let' (rhs.subst substitution) (body.subst substitution.lift)

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | ref selected => simp [rename]
  | lam domain body induction => simp [rename, induction]
  | obj definitions => simp [rename]
  | recObj definitions => simp [rename]
  | app function argument => simp [rename]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]

end Tm

/-! ## Constructor-for-constructor embedding of recursive DOT syntax -/

namespace Legacy

def ty {scope : Sig} : DotFCR.Source.Ty scope → Ty scope
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (ty domain) (ty codomain)
  | .member label lower upper => .member label (ty lower) (ty upper)
  | .sel root label => .sel (.var root) label
  | .inter left right => .inter (ty left) (ty right)
  | .mu body => .mu (ty body)

def typeDef {scope : Sig} (definition : DotFCR.Source.TypeDef scope) :
    TypeDef scope where
  label := definition.label
  witness := ty definition.witness

def typeDefs {scope : Sig}
    (definitions : List (DotFCR.Source.TypeDef scope)) :
    List (TypeDef scope) :=
  definitions.map typeDef

def tm {scope : Sig} : DotFCR.Source.Tm scope → Tm scope
  | .var root => .ref (.var root)
  | .lam domain body => .lam (ty domain) (tm body)
  | .obj definitions => .obj (typeDefs definitions)
  | .recObj definitions => .recObj (typeDefs definitions)
  | .app function argument => .app (.var function) (.var argument)
  | .let' rhs body => .let' (tm rhs) (tm body)

@[simp]
theorem ty_rename {source target : Sig} (type : DotFCR.Source.Ty source)
    (rho : Rename source target) :
    ty (type.rename rho) = (ty type).rename rho := by
  induction type generalizing target with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp only [DotFCR.Source.Ty.rename, ty, Ty.rename]
      rw [domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp only [DotFCR.Source.Ty.rename, ty, Ty.rename]
      rw [lowerInduction, upperInduction]
  | sel => rfl
  | inter left right leftInduction rightInduction =>
      simp only [DotFCR.Source.Ty.rename, ty, Ty.rename]
      rw [leftInduction, rightInduction]
  | mu body induction =>
      simp only [DotFCR.Source.Ty.rename, ty, Ty.rename]
      rw [induction]

@[simp]
theorem tm_rename {source target : Sig} (term : DotFCR.Source.Tm source)
    (rho : Rename source target) :
    tm (term.rename rho) = (tm term).rename rho := by
  induction term generalizing target with
  | var => rfl
  | lam domain body induction =>
      simp only [DotFCR.Source.Tm.rename, tm, Tm.rename]
      rw [ty_rename, induction]
  | obj definitions =>
      simp only [DotFCR.Source.Tm.rename, tm, Tm.rename]
      congr
      induction definitions with
      | nil => rfl
      | cons definition remaining induction =>
          simp [DotFCR.Source.TypeDefs.rename, TypeDefs.rename, typeDefs,
            typeDef, DotFCR.Source.TypeDef.rename, TypeDef.rename,
            ty_rename]
  | recObj definitions =>
      simp only [DotFCR.Source.Tm.rename, tm, Tm.rename]
      congr
      induction definitions with
      | nil => rfl
      | cons definition remaining induction =>
          simp [DotFCR.Source.TypeDefs.rename, TypeDefs.rename, typeDefs,
            typeDef, DotFCR.Source.TypeDef.rename, TypeDef.rename,
            ty_rename]
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFCR.Source.Tm.rename, tm, Tm.rename]
      rw [rhsInduction, bodyInduction]

end Legacy

end DotFCRP.Source
