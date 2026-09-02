import Coercions.ManySortedFC.Syntax

/-!
# Static substitution for the many-sorted coercion calculus

`SymbolArgs` supplies one ambient witness for every symbol in a names-first
theory.  `StaticSubst` simultaneously preserves ordinary term variables and
replaces static symbols by expressions of the same sort.  Evidence binders are
proof-only for the syntax in this module, so complete theory instantiation
drops their scope after replacing the symbol block.
-/

namespace ManySortedFC

/-! ## Heterogeneous symbol arguments -/

/-- Simultaneous witnesses for a heterogeneous symbol block.

The list head is the newest symbol, matching `symbolKinds`, `Sig.extendMany`,
and the heterogeneous de Bruijn convention.  Every witness lives in the same
ambient scope, so the witnesses are genuinely simultaneous. -/
inductive SymbolArgs (scope : Sig) : List StaticSort -> Type where
  | nil : SymbolArgs scope []
  | cons {sort : StaticSort} {symbols : List StaticSort}
      (newest : StaticExpr sort scope) (older : SymbolArgs scope symbols) :
      SymbolArgs scope (sort :: symbols)
deriving DecidableEq

namespace SymbolArgs

/-- Rename every witness without changing the heterogeneous symbol shape. -/
def rename {source target : Sig} {symbols : List StaticSort}
    (arguments : SymbolArgs source symbols) (rho : Rename source target) :
    SymbolArgs target symbols :=
  match arguments with
  | .nil => .nil
  | .cons newest older =>
      .cons (newest.rename rho) (older.rename rho)

/-- Weaken all witnesses below one fresh binder. -/
def weaken {scope : Sig} {symbols : List StaticSort} {kind : BinderKind}
    (arguments : SymbolArgs scope symbols) :
    SymbolArgs (scope ▹ kind) symbols :=
  arguments.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {symbols : List StaticSort}
    (arguments : SymbolArgs scope symbols) :
    arguments.rename Rename.id = arguments := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      simp only [rename, StaticExpr.rename_id, induction]

@[simp]
theorem rename_comp {first second third : Sig}
    {symbols : List StaticSort} (arguments : SymbolArgs first symbols)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (arguments.rename rho₁).rename rho₂ =
      arguments.rename (rho₁.comp rho₂) := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      simp only [rename, StaticExpr.rename_comp, induction]

end SymbolArgs

/-! ## Simultaneous static substitutions -/

namespace StaticExpr

/-- Embed an abstract symbol as a static expression of its intrinsic sort. -/
def symbol {scope : Sig} {sort : StaticSort}
    (name : BVar scope (.symbol sort)) : StaticExpr sort scope :=
  match sort with
  | .type => .type (.tvar name)
  | .capture => .capture (.cvar name)

end StaticExpr

/-- A simultaneous substitution for the variables visible in static syntax.

Term variables remain stable variables because captures may contain singleton
term capabilities.  Static symbols may be replaced by arbitrary expressions,
but the dependent field enforces preservation of their sort.  Static syntax
cannot mention evidence variables, which is why no evidence component is
needed. -/
structure StaticSubst (source target : Sig) where
  termVar : BVar source .term -> BVar target .term
  symbolVar : {sort : StaticSort} ->
    BVar source (.symbol sort) -> StaticExpr sort target

namespace StaticSubst

@[ext]
theorem ext {source target : Sig}
    {first second : StaticSubst source target}
    (terms : forall index, first.termVar index = second.termVar index)
    (symbols : forall {sort : StaticSort}
      (index : BVar source (.symbol sort)),
      first.symbolVar index = second.symbolVar index) :
    first = second := by
  cases first
  cases second
  congr
  · funext index
    exact terms index
  · funext sort index
    exact symbols index

/-- Identity static substitution. -/
def id {scope : Sig} : StaticSubst scope scope where
  termVar := fun index => index
  symbolVar := StaticExpr.symbol

/-- Embed a kind-preserving renaming as a static substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    StaticSubst source target where
  termVar := fun index => rho.var index
  symbolVar := fun index => StaticExpr.symbol (rho.var index)

/-- Preserve a fresh ordinary term variable. -/
def liftTerm {source target : Sig}
    (substitution : StaticSubst source target) :
    StaticSubst (source ▹ .term) (target ▹ .term) where
  termVar := fun
    | .here => .here
    | .there index => .there (substitution.termVar index)
  symbolVar := fun
    | .there index => (substitution.symbolVar index).weaken

/-- Preserve a fresh static symbol of the given sort. -/
def liftSymbol {source target : Sig}
    (substitution : StaticSubst source target) (sort : StaticSort) :
    StaticSubst (source ▹ .symbol sort) (target ▹ .symbol sort) where
  termVar := fun
    | .there index => .there (substitution.termVar index)
  symbolVar := fun
    | .here => StaticExpr.symbol .here
    | .there index => (substitution.symbolVar index).weaken

/-- Preserve a fresh proof-only evidence binder. -/
def liftEvidence {source target : Sig}
    (substitution : StaticSubst source target) (relation : Relation) :
    StaticSubst (source ▹ .evidence relation)
      (target ▹ .evidence relation) where
  termVar := fun
    | .there index => .there (substitution.termVar index)
  symbolVar := fun
    | .there index => (substitution.symbolVar index).weaken

/-- Preserve one heterogeneous binder. -/
def lift {source target : Sig} (substitution : StaticSubst source target)
    (kind : BinderKind) :
    StaticSubst (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => substitution.liftTerm
  | .symbol sort => substitution.liftSymbol sort
  | .evidence relation => substitution.liftEvidence relation

/-- Preserve a heterogeneous binder block. -/
def liftMany {source target : Sig}
    (substitution : StaticSubst source target) : (kinds : Sig) ->
    StaticSubst (Sig.extendMany source kinds) (Sig.extendMany target kinds)
  | [] => substitution
  | kind :: rest => (substitution.liftMany rest).lift kind

/-- Preserve a homogeneous block of binders. -/
def liftN {source target : Sig}
    (substitution : StaticSubst source target) (kind : BinderKind) :
    (count : Nat) →
      StaticSubst (Sig.extendN source kind count)
        (Sig.extendN target kind count)
  | 0 => substitution
  | count + 1 => (substitution.liftN kind count).lift kind

/-- Preserve the homogeneous type self names of a recursive block. -/
def liftTypes {source target : Sig}
    (substitution : StaticSubst source target) (names : Nat) :
    StaticSubst (TypeScope source names) (TypeScope target names) :=
  substitution.liftN (.symbol .type) names

/-- Preserve a heterogeneous symbol block. -/
def liftSymbols {source target : Sig}
    (substitution : StaticSubst source target)
    (symbols : List StaticSort) :
    StaticSubst (SymbolScope source symbols) (SymbolScope target symbols) :=
  substitution.liftMany (symbolKinds symbols)

/-- Preserve the evidence binders of a theory. -/
def liftEvidenceBlock {source target : Sig}
    (substitution : StaticSubst source target)
    (relations : List Relation) :
    StaticSubst (Sig.extendMany source (evidenceKinds relations))
      (Sig.extendMany target (evidenceKinds relations)) :=
  substitution.liftMany (evidenceKinds relations)

/-- Preserve a complete names-first static scope. -/
def liftStatic {source target : Sig}
    (substitution : StaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation) :
    StaticSubst (StaticScope source symbols relations)
      (StaticScope target symbols relations) :=
  (substitution.liftSymbols symbols).liftEvidenceBlock relations

/-- Preserve the proof-only assumptions introduced by a modal lock. -/
def liftModal {source target : Sig}
    (substitution : StaticSubst source target)
    (separationCount : Nat) (modes : List CaptureMode) :
    StaticSubst (ModalScope source separationCount modes)
      (ModalScope target separationCount modes) :=
  substitution.liftEvidenceBlock
    (modalRelations separationCount modes)

/-- Eliminate the newest static symbol. -/
def instantiateSymbol {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    StaticSubst (source ▹ .symbol sort) target where
  termVar := fun
    | .there index => substitution.termVar index
  symbolVar := fun
    | .here => replacement
    | .there index => substitution.symbolVar index

/-- Remove one proof-only source binder. -/
def dropEvidence {source target : Sig}
    (substitution : StaticSubst source target) (relation : Relation) :
    StaticSubst (source ▹ .evidence relation) target where
  termVar := fun
    | .there index => substitution.termVar index
  symbolVar := fun
    | .there index => substitution.symbolVar index

/-- Remove a heterogeneous block of proof-only source binders. -/
def dropEvidenceBlock {source target : Sig}
    (substitution : StaticSubst source target) :
    (relations : List Relation) ->
    StaticSubst (Sig.extendMany source (evidenceKinds relations)) target
  | [] => substitution
  | relation :: rest =>
      (substitution.dropEvidenceBlock rest).dropEvidence relation

/-- Extend an ambient substitution with simultaneous heterogeneous witnesses.

The recursive call installs the older tail first; the list head is then the
newest source symbol eliminated by `instantiateSymbol`. -/
def fromSymbolArgs {source target : Sig}
    (base : StaticSubst source target) :
    {symbols : List StaticSort} -> SymbolArgs target symbols ->
      StaticSubst (SymbolScope source symbols) target
  | [], .nil => base
  | _ :: _, .cons newest older =>
      (fromSymbolArgs base older).instantiateSymbol newest

/-- Instantiate a symbol block relative to an ambient renaming. -/
def ofSymbolArgs {source target : Sig} (ambient : Rename source target)
    {symbols : List StaticSort} (arguments : SymbolArgs target symbols) :
    StaticSubst (SymbolScope source symbols) target :=
  fromSymbolArgs (ofRename ambient) arguments

/-- Extend an ambient substitution with homogeneous simultaneous type
witnesses. -/
def fromTypeArgs {source target : Sig} (base : StaticSubst source target) :
    {names : Nat} → TypeArgs target names →
      StaticSubst (TypeScope source names) target
  | 0, .nil => base
  | _ + 1, .snoc initial witness =>
      (fromTypeArgs base initial).instantiateSymbol (.type witness)

/-- Instantiate the self-name suffix of a recursive type block. -/
def ofTypeArgs {source target : Sig} (ambient : Rename source target)
    {names : Nat} (arguments : TypeArgs target names) :
    StaticSubst (TypeScope source names) target :=
  fromTypeArgs (ofRename ambient) arguments

/-- Interpret a complete static scope: instantiate every symbol, then remove
its proof-only evidence binders. -/
def staticOfSymbolArgs {source target : Sig}
    (ambient : Rename source target) {symbols : List StaticSort}
    (arguments : SymbolArgs target symbols) (relations : List Relation) :
    StaticSubst (StaticScope source symbols relations) target :=
  (ofSymbolArgs ambient arguments).dropEvidenceBlock relations

end StaticSubst

/-! ## Capture-avoiding action on static syntax -/

mutual

/-- Apply a simultaneous static substitution to a capture expression. -/
def Capture.substitute {source target : Sig} (capture : Capture source)
    (substitution : StaticSubst source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right =>
      .union (left.substitute substitution) (right.substitute substitution)
  | .readOnly capture => .readOnly (capture.substitute substitution)
  | .singleton capability =>
      .singleton (substitution.termVar capability)
  | .cvar name =>
      match substitution.symbolVar name with
      | .capture replacement => replacement
  | .project capture kind =>
      .project (capture.substitute substitution) kind

/-- Substitute every capture in a separation context. -/
def SeparationContext.substitute {count : Nat} {source target : Sig}
    (context : SeparationContext count source)
    (substitution : StaticSubst source target) :
    SeparationContext count target :=
  match context with
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.substitute substitution)
        (capture.substitute substitution)

/-- Substitute every capture in a mode context. -/
def ModeContext.substitute {modes : List CaptureMode}
    {source target : Sig} (context : ModeContext modes source)
    (substitution : StaticSubst source target) :
    ModeContext modes target :=
  match context with
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.substitute substitution)
        (capture.substitute substitution)

/-- Substitute both components of a modal context. -/
def ModalContext.substitute {separationCount : Nat}
    {modes : List CaptureMode} {source target : Sig}
    (context : ModalContext separationCount modes source)
    (substitution : StaticSubst source target) :
    ModalContext separationCount modes target :=
  match context with
  | .mk separation mode =>
      .mk (separation.substitute substitution)
        (mode.substitute substitution)

/-- Apply a simultaneous static substitution to a type. -/
def Ty.substitute {source target : Sig} (type : Ty source)
    (substitution : StaticSubst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .tvar name =>
      match substitution.symbolVar name with
      | .type replacement => replacement
  | .capturing captures shape =>
      .capturing (captures.substitute substitution)
        (shape.substitute substitution)
  | .arr domain codomain =>
      .arr (domain.substitute substitution) (codomain.substitute substitution)
  | .modal requirements body =>
      .modal (requirements.substitute substitution)
        (body.substitute substitution)
  | @Ty.forallT _ symbols relations theory body =>
      .forallT (theory.substitute substitution)
        (body.substitute (substitution.liftStatic symbols relations))
  | @Ty.existsT _ symbols relations theory payload =>
      .existsT (theory.substitute substitution)
        (payload.substitute (substitution.liftStatic symbols relations))
  | .recProj bodies index =>
      .recProj (bodies.substitute substitution) index

/-- Substitute the ambient scope of every recursive body while preserving
its homogeneous suffix of self names. -/
def RecBodies.substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : StaticSubst source target) :
    RecBodies target bound count :=
  match bodies with
  | .nil => .nil
  | .snoc initial body =>
      .snoc (initial.substitute substitution)
        (body.substitute (substitution.liftTypes bound))

/-- Apply a simultaneous static substitution without changing the sort. -/
def StaticExpr.substitute {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source)
    (substitution : StaticSubst source target) : StaticExpr sort target :=
  match expression with
  | .type type => .type (type.substitute substitution)
  | .capture capture => .capture (capture.substitute substitution)

/-- Substitute every static expression in a proposition. -/
def Proposition.substitute {relation : Relation} {source target : Sig}
    (proposition : Proposition relation source)
    (substitution : StaticSubst source target) :
    Proposition relation target :=
  match proposition with
  | .equality left right =>
      .equality (left.substitute substitution)
        (right.substitute substitution)
  | .inclusion lower upper =>
      .inclusion (lower.substitute substitution)
        (upper.substitute substitution)
  | .separate left right =>
      .separate (left.substitute substitution) (right.substitute substitution)
  | .disjoint left right =>
      .disjoint (left.substitute substitution) (right.substitute substitution)
  | .mode capture => .mode (capture.substitute substitution)
  | .captureHasKind capture kind =>
      .captureHasKind (capture.substitute substitution) kind

/-- Substitute the ambient scope of a names-first theory. -/
def Theory.substitute {source target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations)
    (substitution : StaticSubst source target) :
    Theory target symbols relations :=
  match theory with
  | .nil => .nil
  | .cons proposition rest =>
      .cons (proposition.substitute (substitution.liftSymbols symbols))
        (rest.substitute substitution)

end

@[simp]
theorem Ty.substitute_recProj {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (index : Fin names)
    (substitution : StaticSubst source target) :
    (Ty.recProj bodies index).substitute substitution =
      .recProj (bodies.substitute substitution) index := rfl

namespace TypeArgs

/-- Substitute every homogeneous type witness. -/
def substitute {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count)
    (substitution : StaticSubst source target) : TypeArgs target count :=
  match arguments with
  | .nil => .nil
  | .snoc initial type =>
      .snoc (initial.substitute substitution)
        (type.substitute substitution)

end TypeArgs

/-! ## Instantiating names-first theories -/

namespace Proposition

/-- Instantiate all symbols of a theory proposition simultaneously. -/
def instantiateSymbols {scope : Sig} {symbols : List StaticSort}
    {relation : Relation}
    (proposition : Proposition relation (SymbolScope scope symbols))
    (arguments : SymbolArgs scope symbols) : Proposition relation scope :=
  proposition.substitute
    (StaticSubst.ofSymbolArgs Rename.id arguments)

end Proposition

namespace Capture

/-- Instantiate a capture expression below a complete theory scope. -/
def instantiateStatic {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (body : Capture (StaticScope scope symbols relations))
    (arguments : SymbolArgs scope symbols) : Capture scope :=
  body.substitute
    (StaticSubst.staticOfSymbolArgs Rename.id arguments relations)

end Capture

namespace Ty

/-- Instantiate a type below a complete theory scope. -/
def instantiateStatic {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (body : Ty (StaticScope scope symbols relations))
    (arguments : SymbolArgs scope symbols) : Ty scope :=
  body.substitute
    (StaticSubst.staticOfSymbolArgs Rename.id arguments relations)

end Ty

namespace StaticExpr

/-- Instantiate a sort-indexed expression below a complete theory scope. -/
def instantiateStatic {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} {sort : StaticSort}
    (body : StaticExpr sort (StaticScope scope symbols relations))
    (arguments : SymbolArgs scope symbols) : StaticExpr sort scope :=
  body.substitute
    (StaticSubst.staticOfSymbolArgs Rename.id arguments relations)

end StaticExpr

end ManySortedFC
