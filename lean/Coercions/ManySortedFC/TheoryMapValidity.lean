import Coercions.ManySortedFC.TheoryMapCheckerCompleteness
import Coercions.ManySortedFC.TheoryMapMetatheory

/-!
# Validity of identity and composition for cross-shape theory maps

Evidence-aware static substitution preserves declarative evidence typing.
Consequently the canonical identity map is valid, and valid cross-shape maps
are closed under composition.  The corresponding checker-acceptance laws are
constructive consequences of checker completeness.
-/

namespace ManySortedFC

namespace StaticSubst

@[simp]
theorem ofRename_liftTerm {source target : Sig} (rho : Rename source target) :
    (ofRename rho).liftTerm = ofRename rho.lift := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro sort index
    cases index with
    | there index => cases sort <;> rfl

@[simp]
theorem ofRename_liftSymbol {source target : Sig} (rho : Rename source target)
    (sort : StaticSort) :
    (ofRename rho).liftSymbol sort = ofRename rho.lift := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro other index
    cases index with
    | here => rfl
    | there index => cases other <;> rfl

@[simp]
theorem ofRename_liftEvidence {source target : Sig}
    (rho : Rename source target) (relation : Relation) :
    (ofRename rho).liftEvidence relation = ofRename rho.lift := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro sort index
    cases index with
    | there index => cases sort <;> rfl

@[simp]
theorem ofRename_lift {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) :
    (ofRename rho).lift kind = ofRename rho.lift := by
  cases kind <;> simp [StaticSubst.lift]

@[simp]
theorem ofRename_liftMany {source target : Sig} (rho : Rename source target) :
    ∀ kinds : Sig,
      (ofRename rho).liftMany kinds = ofRename (rho.liftMany kinds)
  | [] => rfl
  | kind :: rest => by
      simp only [liftMany, Rename.liftMany_cons, ofRename_liftMany rho rest]
      exact ofRename_lift _ _

@[simp]
theorem ofRename_liftSymbols {source target : Sig}
    (rho : Rename source target) (symbols : List StaticSort) :
    (ofRename rho).liftSymbols symbols = ofRename (rho.liftSymbols symbols) := by
  unfold StaticSubst.liftSymbols Rename.liftSymbols
  exact ofRename_liftMany _ _

@[simp]
theorem ofRename_liftStatic {source target : Sig} (rho : Rename source target)
    (symbols : List StaticSort) (relations : List Relation) :
    (ofRename rho).liftStatic symbols relations =
      ofRename (rho.liftStatic symbols relations) := by
  unfold liftStatic Rename.liftStatic StaticSubst.liftSymbols
    StaticSubst.liftEvidenceBlock Rename.liftSymbols Rename.liftEvidence
  simp

@[simp]
theorem ofRename_liftModal {source target : Sig} (rho : Rename source target)
    (separationCount : Nat) (modes : List CaptureMode) :
    (ofRename rho).liftModal separationCount modes =
      ofRename (rho.liftModal separationCount modes) := by
  unfold StaticSubst.liftModal Rename.liftModal
    StaticSubst.liftEvidenceBlock Rename.liftEvidence
  exact ofRename_liftMany _ _

end StaticSubst

mutual

@[simp]
def Capture.substitute_ofRename {source target : Sig}
    (capture : Capture source) (rho : Rename source target) :
    capture.substitute (StaticSubst.ofRename rho) = capture.rename rho :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.substitute, Capture.rename,
        Capture.substitute_ofRename left, Capture.substitute_ofRename right]
  | .readOnly capture => by
      simp only [Capture.substitute, Capture.rename,
        Capture.substitute_ofRename capture]
  | .singleton _ => rfl
  | .cvar _ => rfl

@[simp]
def SeparationContext.substitute_ofRename {count : Nat}
    {source target : Sig} (context : SeparationContext count source)
    (rho : Rename source target) :
    context.substitute (StaticSubst.ofRename rho) = context.rename rho :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.substitute, SeparationContext.rename,
        SeparationContext.substitute_ofRename rest,
        Capture.substitute_ofRename capture]

@[simp]
def ModeContext.substitute_ofRename {modes : List CaptureMode}
    {source target : Sig} (context : ModeContext modes source)
    (rho : Rename source target) :
    context.substitute (StaticSubst.ofRename rho) = context.rename rho :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.substitute, ModeContext.rename,
        ModeContext.substitute_ofRename rest,
        Capture.substitute_ofRename capture]

@[simp]
def ModalContext.substitute_ofRename {separationCount : Nat}
    {modes : List CaptureMode} {source target : Sig}
    (context : ModalContext separationCount modes source)
    (rho : Rename source target) :
    context.substitute (StaticSubst.ofRename rho) = context.rename rho :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.substitute, ModalContext.rename,
        SeparationContext.substitute_ofRename separation,
        ModeContext.substitute_ofRename mode]

@[simp]
def Ty.substitute_ofRename {source target : Sig}
    (type : Ty source) (rho : Rename source target) :
    type.substitute (StaticSubst.ofRename rho) = type.rename rho :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .capturing captures shape => by
      simp only [Ty.substitute, Ty.rename, Capture.substitute_ofRename,
        Ty.substitute_ofRename]
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.rename, Ty.substitute_ofRename]
  | .modal requirements body => by
      simp only [Ty.substitute, Ty.rename,
        ModalContext.substitute_ofRename requirements,
        Ty.substitute_ofRename body]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.substitute, Ty.rename, Theory.substitute_ofRename,
        StaticSubst.ofRename_liftStatic, Ty.substitute_ofRename]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.substitute, Ty.rename, Theory.substitute_ofRename,
        StaticSubst.ofRename_liftStatic, Ty.substitute_ofRename]

@[simp]
def StaticExpr.substitute_ofRename {source target : Sig}
    {sort : StaticSort} (expression : StaticExpr sort source)
    (rho : Rename source target) :
    expression.substitute (StaticSubst.ofRename rho) =
      expression.rename rho :=
  match expression with
  | .type type => by simp only [StaticExpr.substitute, StaticExpr.rename,
      Ty.substitute_ofRename]
  | .capture capture => by simp only [StaticExpr.substitute,
      StaticExpr.rename, Capture.substitute_ofRename]

@[simp]
def Proposition.substitute_ofRename {source target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (rho : Rename source target) :
    proposition.substitute (StaticSubst.ofRename rho) =
      proposition.rename rho :=
  match proposition with
  | .equality left right => by simp only [Proposition.substitute,
      Proposition.rename, StaticExpr.substitute_ofRename]
  | .inclusion lower upper => by simp only [Proposition.substitute,
      Proposition.rename, StaticExpr.substitute_ofRename]
  | .separate left right => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_ofRename]
  | .disjoint left right => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_ofRename]
  | .mode capture => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_ofRename]

@[simp]
def Theory.substitute_ofRename {source target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations) (rho : Rename source target) :
    theory.substitute (StaticSubst.ofRename rho) = theory.rename rho :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by
      simp only [Theory.substitute, Theory.rename,
        StaticSubst.ofRename_liftSymbols, Proposition.substitute_ofRename,
        Theory.substitute_ofRename]

end


namespace StaticSubst

/-- Postcompose a static substitution with a structural renaming. -/
def postRename {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    StaticSubst source target where
  termVar := fun index => rho.var (substitution.termVar index)
  symbolVar := fun index => (substitution.symbolVar index).rename rho

@[simp]
theorem postRename_lift {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target)
    (kind : BinderKind) :
    (substitution.postRename rho).lift kind =
      (substitution.lift kind).postRename rho.lift := by
  apply ext
  · intro index
    cases kind <;> cases index <;> rfl
  · intro sort index
    cases kind with
    | term =>
        cases index with
        | there index =>
            change ((substitution.symbolVar index).rename rho).weaken =
              ((substitution.symbolVar index).weaken).rename rho.lift
            unfold StaticExpr.weaken
            rw [StaticExpr.rename_comp, StaticExpr.rename_comp,
              Rename.succ_lift_comm]
    | symbol newest =>
        cases index with
        | here => cases sort <;> rfl
        | there index =>
            change ((substitution.symbolVar index).rename rho).weaken =
              ((substitution.symbolVar index).weaken).rename rho.lift
            unfold StaticExpr.weaken
            rw [StaticExpr.rename_comp, StaticExpr.rename_comp,
              Rename.succ_lift_comm]
    | evidence relation =>
        cases index with
        | there index =>
            change ((substitution.symbolVar index).rename rho).weaken =
              ((substitution.symbolVar index).weaken).rename rho.lift
            unfold StaticExpr.weaken
            rw [StaticExpr.rename_comp, StaticExpr.rename_comp,
              Rename.succ_lift_comm]

@[simp]
theorem postRename_liftMany {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    ∀ kinds : Sig,
    (substitution.postRename rho).liftMany kinds =
      (substitution.liftMany kinds).postRename (rho.liftMany kinds)
  | [] => rfl
  | kind :: rest => by
      simp only [StaticSubst.liftMany, Rename.liftMany,
        postRename_liftMany substitution rho rest, postRename_lift]
      rfl

@[simp]
theorem postRename_liftSymbols {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target)
    (symbols : List StaticSort) :
    (substitution.postRename rho).liftSymbols symbols =
      (substitution.liftSymbols symbols).postRename
        (rho.liftSymbols symbols) := by
  unfold StaticSubst.liftSymbols Rename.liftSymbols
  exact postRename_liftMany _ _ _

@[simp]
theorem postRename_liftStatic {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    (substitution.postRename rho).liftStatic symbols relations =
      (substitution.liftStatic symbols relations).postRename
        (rho.liftStatic symbols relations) := by
  unfold StaticSubst.liftStatic Rename.liftStatic
    StaticSubst.liftEvidenceBlock Rename.liftEvidence
  simp

@[simp]
theorem postRename_liftModal {source middle target : Sig}
    (substitution : StaticSubst source middle) (rho : Rename middle target)
    (separationCount : Nat) (modes : List CaptureMode) :
    (substitution.postRename rho).liftModal separationCount modes =
      (substitution.liftModal separationCount modes).postRename
        (rho.liftModal separationCount modes) := by
  unfold StaticSubst.liftModal Rename.liftModal
    StaticSubst.liftEvidenceBlock Rename.liftEvidence
  exact postRename_liftMany _ _ _

end StaticSubst

mutual

@[simp]
def Capture.substitute_postRename {source middle target : Sig}
    (capture : Capture source) (substitution : StaticSubst source middle)
    (rho : Rename middle target) :
    (capture.substitute substitution).rename rho =
      capture.substitute (substitution.postRename rho) :=
  match capture with
  | .empty => rfl
  | .union left right => by simp only [Capture.substitute,
      Capture.rename, Capture.substitute_postRename left,
      Capture.substitute_postRename right]
  | .readOnly capture => by simp only [Capture.substitute,
      Capture.rename, Capture.substitute_postRename capture]
  | .singleton _ => rfl
  | .cvar name => by
      generalize equality : substitution.symbolVar name = expression
      cases expression with
      | capture replacement =>
          simp only [Capture.substitute, StaticSubst.postRename]
          rw [equality]
          rfl

@[simp]
def SeparationContext.substitute_postRename {count : Nat}
    {source middle target : Sig} (context : SeparationContext count source)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (context.substitute substitution).rename rho =
      context.substitute (substitution.postRename rho) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.substitute, SeparationContext.rename,
        SeparationContext.substitute_postRename rest,
        Capture.substitute_postRename capture]

@[simp]
def ModeContext.substitute_postRename {modes : List CaptureMode}
    {source middle target : Sig} (context : ModeContext modes source)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (context.substitute substitution).rename rho =
      context.substitute (substitution.postRename rho) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.substitute, ModeContext.rename,
        ModeContext.substitute_postRename rest,
        Capture.substitute_postRename capture]

@[simp]
def ModalContext.substitute_postRename {separationCount : Nat}
    {modes : List CaptureMode} {source middle target : Sig}
    (context : ModalContext separationCount modes source)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (context.substitute substitution).rename rho =
      context.substitute (substitution.postRename rho) :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.substitute, ModalContext.rename,
        SeparationContext.substitute_postRename separation,
        ModeContext.substitute_postRename mode]

@[simp]
def Ty.substitute_postRename {source middle target : Sig}
    (type : Ty source) (substitution : StaticSubst source middle)
    (rho : Rename middle target) :
    (type.substitute substitution).rename rho =
      type.substitute (substitution.postRename rho) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      generalize equality : substitution.symbolVar name = expression
      cases expression with
      | type replacement =>
          simp only [Ty.substitute, StaticSubst.postRename]
          rw [equality]
          rfl
  | .capturing captures shape => by simp only [Ty.substitute, Ty.rename,
      Capture.substitute_postRename, Ty.substitute_postRename]
  | .arr domain codomain => by simp only [Ty.substitute, Ty.rename,
      Ty.substitute_postRename]
  | .modal requirements body => by
      simp only [Ty.substitute, Ty.rename,
        ModalContext.substitute_postRename requirements,
        Ty.substitute_postRename body]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.substitute, Ty.rename, Theory.substitute_postRename,
        Ty.substitute_postRename, StaticSubst.postRename_liftStatic]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.substitute, Ty.rename, Theory.substitute_postRename,
        Ty.substitute_postRename, StaticSubst.postRename_liftStatic]

@[simp]
def StaticExpr.substitute_postRename {source middle target : Sig}
    {sort : StaticSort} (expression : StaticExpr sort source)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (expression.substitute substitution).rename rho =
      expression.substitute (substitution.postRename rho) :=
  match expression with
  | .type type => by simp only [StaticExpr.substitute, StaticExpr.rename,
      Ty.substitute_postRename]
  | .capture capture => by simp only [StaticExpr.substitute,
      StaticExpr.rename, Capture.substitute_postRename]

@[simp]
def Proposition.substitute_postRename {source middle target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (proposition.substitute substitution).rename rho =
      proposition.substitute (substitution.postRename rho) :=
  match proposition with
  | .equality left right => by simp only [Proposition.substitute,
      Proposition.rename, StaticExpr.substitute_postRename]
  | .inclusion lower upper => by simp only [Proposition.substitute,
      Proposition.rename, StaticExpr.substitute_postRename]
  | .separate left right => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_postRename]
  | .disjoint left right => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_postRename]
  | .mode capture => by simp only [Proposition.substitute,
      Proposition.rename, Capture.substitute_postRename]

@[simp]
def Theory.substitute_postRename {source middle target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations)
    (substitution : StaticSubst source middle) (rho : Rename middle target) :
    (theory.substitute substitution).rename rho =
      theory.substitute (substitution.postRename rho) :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by simp only [Theory.substitute,
      Theory.rename, Proposition.substitute_postRename,
      Theory.substitute_postRename, StaticSubst.postRename_liftSymbols]

end

namespace StaticSubst

/-- Applying `after` following `before` has the same static action as
`result`. -/
structure Follows {source middle target : Sig}
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target) : Prop where
  term : ∀ index, after.termVar (before.var index) = result.termVar index
  symbol : ∀ {sort : StaticSort}
      (index : BVar source (.symbol sort)),
    after.symbolVar (before.var index) = result.symbolVar index

namespace Follows

def instantiateSymbol {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    Follows (Rename.succ (scope := source) (kind := .symbol sort))
      (substitution.instantiateSymbol replacement) substitution := by
  constructor
  · intro index
    rfl
  · intro other index
    rfl

def dropEvidence {source target : Sig}
    (substitution : StaticSubst source target) (relation : Relation) :
    Follows (Rename.succ (scope := source) (kind := .evidence relation))
      (substitution.dropEvidence relation) substitution := by
  constructor
  · intro index
    rfl
  · intro sort index
    rfl

def ofRename {source target : Sig} (rho : Rename source target) :
    Follows rho (StaticSubst.ofRename Rename.id)
      (StaticSubst.ofRename rho) := by
  constructor <;> intros <;> rfl

def instantiateBothSymbol {source middle target : Sig}
    {before : Rename source middle} {after : StaticSubst middle target}
    {result : StaticSubst source target}
    (follows : Follows before after result) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    Follows before.lift (after.instantiateSymbol replacement)
      (result.instantiateSymbol replacement) := by
  constructor
  · intro index
    cases index with
    | there index => exact follows.term index
  · intro other index
    cases index with
    | here => rfl
    | there index => exact follows.symbol index

def dropAfter {source middle target : Sig}
    {before : Rename source middle} {after : StaticSubst middle target}
    {result : StaticSubst source target}
    (follows : Follows before after result) (relation : Relation) :
    Follows (before.comp
      (Rename.succ (scope := middle) (kind := .evidence relation)))
      (after.dropEvidence relation) result := by
  constructor
  · intro index
    exact follows.term index
  · intro sort index
    exact follows.symbol index

def fromSymbolArgs {source target : Sig} (rho : Rename source target) :
    {symbols : List StaticSort} → (arguments : SymbolArgs target symbols) →
    Follows (rho.liftSymbols symbols)
      (StaticSubst.ofSymbolArgs Rename.id arguments)
      (StaticSubst.fromSymbolArgs (StaticSubst.ofRename rho) arguments)
  | [], .nil => ofRename rho
  | _ :: _, .cons newest older =>
      (fromSymbolArgs rho older).instantiateBothSymbol newest

def fromEvidenceArgs {source target : Sig}
    (base : TermStaticSubst source target) :
    {relations : List Relation} → (arguments : EvidenceArgs target relations) →
    Follows (Rename.weakenMany source (evidenceKinds relations))
      (TermStaticSubst.fromEvidenceArgs base arguments).static base.static
  | [], .nil => by
      constructor <;> intros <;> rfl
  | _ :: _, .cons newest older =>
      (fromEvidenceArgs base older).dropAfter _

def lift {source middle target : Sig} {before : Rename source middle}
    {after : StaticSubst middle target} {result : StaticSubst source target}
    (follows : Follows before after result) (kind : BinderKind) :
    Follows before.lift (after.lift kind) (result.lift kind) := by
  constructor
  · intro index
    cases kind with
    | term =>
        cases index with
        | here => rfl
        | there index =>
            change BVar.there (after.termVar (before.var index)) =
              BVar.there (result.termVar index)
            rw [follows.term]
    | symbol sort =>
        cases index with
        | there index =>
            change BVar.there (after.termVar (before.var index)) =
              BVar.there (result.termVar index)
            rw [follows.term]
    | evidence relation =>
        cases index with
        | there index =>
            change BVar.there (after.termVar (before.var index)) =
              BVar.there (result.termVar index)
            rw [follows.term]
  · intro sort index
    cases kind with
    | term =>
        cases index with
        | there index =>
            change (after.symbolVar (before.var index)).weaken =
              (result.symbolVar index).weaken
            rw [follows.symbol]
    | symbol newest =>
        cases index with
        | here => rfl
        | there index =>
            change (after.symbolVar (before.var index)).weaken =
              (result.symbolVar index).weaken
            rw [follows.symbol]
    | evidence relation =>
        cases index with
        | there index =>
            change (after.symbolVar (before.var index)).weaken =
              (result.symbolVar index).weaken
            rw [follows.symbol]

def liftMany {source middle target : Sig} {before : Rename source middle}
    {after : StaticSubst middle target} {result : StaticSubst source target}
    (follows : Follows before after result) : ∀ kinds : Sig,
    Follows (before.liftMany kinds) (after.liftMany kinds)
      (result.liftMany kinds)
  | [] => follows
  | kind :: rest => (follows.liftMany rest).lift kind

def liftSymbols {source middle target : Sig} {before : Rename source middle}
    {after : StaticSubst middle target} {result : StaticSubst source target}
    (follows : Follows before after result) (symbols : List StaticSort) :
    Follows (before.liftSymbols symbols) (after.liftSymbols symbols)
      (result.liftSymbols symbols) :=
  follows.liftMany (symbolKinds symbols)

def liftStatic {source middle target : Sig} {before : Rename source middle}
    {after : StaticSubst middle target} {result : StaticSubst source target}
    (follows : Follows before after result) (symbols : List StaticSort)
    (relations : List Relation) :
    Follows (before.liftStatic symbols relations)
      (after.liftStatic symbols relations)
      (result.liftStatic symbols relations) :=
  (follows.liftSymbols symbols).liftMany (evidenceKinds relations)

def liftModal {source middle target : Sig} {before : Rename source middle}
    {after : StaticSubst middle target} {result : StaticSubst source target}
    (follows : Follows before after result) (separationCount : Nat)
    (modes : List CaptureMode) :
    Follows (before.liftModal separationCount modes)
      (after.liftModal separationCount modes)
      (result.liftModal separationCount modes) := by
  unfold Rename.liftModal StaticSubst.liftModal
    StaticSubst.liftEvidenceBlock Rename.liftEvidence
  exact follows.liftMany (evidenceKinds (modalRelations separationCount modes))

end Follows
end StaticSubst

mutual

def Capture.rename_substitute {source middle target : Sig}
    (capture : Capture source) (before : Rename source middle)
    (after : StaticSubst middle target) (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (capture.rename before).substitute after = capture.substitute result :=
  match capture with
  | .empty => rfl
  | .union left right => by simp only [Capture.rename, Capture.substitute,
      Capture.rename_substitute left before after result follows,
      Capture.rename_substitute right before after result follows]
  | .readOnly capture => by simp only [Capture.rename, Capture.substitute,
      Capture.rename_substitute capture before after result follows]
  | .singleton index => by simp [Capture.rename, Capture.substitute,
      follows.term]
  | .cvar index => by
      simp [Capture.rename, Capture.substitute, follows.symbol]

def SeparationContext.rename_substitute {count : Nat}
    {source middle target : Sig} (context : SeparationContext count source)
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (context.rename before).substitute after = context.substitute result :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.rename, SeparationContext.substitute,
        SeparationContext.rename_substitute rest before after result follows,
        Capture.rename_substitute capture before after result follows]

def ModeContext.rename_substitute {modes : List CaptureMode}
    {source middle target : Sig} (context : ModeContext modes source)
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (context.rename before).substitute after = context.substitute result :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.rename, ModeContext.substitute,
        ModeContext.rename_substitute rest before after result follows,
        Capture.rename_substitute capture before after result follows]

def ModalContext.rename_substitute {separationCount : Nat}
    {modes : List CaptureMode} {source middle target : Sig}
    (context : ModalContext separationCount modes source)
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (context.rename before).substitute after = context.substitute result :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.rename, ModalContext.substitute,
        SeparationContext.rename_substitute separation before after result
          follows,
        ModeContext.rename_substitute mode before after result follows]

def Ty.rename_substitute {source middle target : Sig}
    (type : Ty source) (before : Rename source middle)
    (after : StaticSubst middle target) (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (type.rename before).substitute after = type.substitute result :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar index => by
      simp [Ty.rename, Ty.substitute, follows.symbol]
  | .capturing captures shape => by simp only [Ty.rename, Ty.substitute,
      Capture.rename_substitute captures before after result follows,
      Ty.rename_substitute shape before after result follows]
  | .arr domain codomain => by simp only [Ty.rename, Ty.substitute,
      Ty.rename_substitute domain before after result follows,
      Ty.rename_substitute codomain before after result follows]
  | .modal requirements body => by
      simp only [Ty.rename, Ty.substitute,
        ModalContext.rename_substitute requirements before after result follows,
        Ty.rename_substitute body before after result follows]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.rename, Ty.substitute,
        Theory.rename_substitute theory before after result follows,
        Ty.rename_substitute body _ _ _
          (follows.liftStatic symbols relations)]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.rename, Ty.substitute,
        Theory.rename_substitute theory before after result follows,
        Ty.rename_substitute payload _ _ _
          (follows.liftStatic symbols relations)]

def StaticExpr.rename_substitute {source middle target : Sig}
    {sort : StaticSort} (expression : StaticExpr sort source)
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (expression.rename before).substitute after =
      expression.substitute result :=
  match expression with
  | .type type => by simp only [StaticExpr.rename, StaticExpr.substitute,
      Ty.rename_substitute type before after result follows]
  | .capture capture => by simp only [StaticExpr.rename,
      StaticExpr.substitute,
      Capture.rename_substitute capture before after result follows]

def Proposition.rename_substitute {source middle target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (before : Rename source middle) (after : StaticSubst middle target)
    (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (proposition.rename before).substitute after =
      proposition.substitute result :=
  match proposition with
  | .equality left right => by simp only [Proposition.rename,
      Proposition.substitute,
      StaticExpr.rename_substitute left before after result follows,
      StaticExpr.rename_substitute right before after result follows]
  | .inclusion lower upper => by simp only [Proposition.rename,
      Proposition.substitute,
      StaticExpr.rename_substitute lower before after result follows,
      StaticExpr.rename_substitute upper before after result follows]
  | .separate left right => by simp only [Proposition.rename,
      Proposition.substitute,
      Capture.rename_substitute left before after result follows,
      Capture.rename_substitute right before after result follows]
  | .disjoint left right => by simp only [Proposition.rename,
      Proposition.substitute,
      Capture.rename_substitute left before after result follows,
      Capture.rename_substitute right before after result follows]
  | .mode capture => by simp only [Proposition.rename,
      Proposition.substitute,
      Capture.rename_substitute capture before after result follows]

def Theory.rename_substitute {source middle target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations) (before : Rename source middle)
    (after : StaticSubst middle target) (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (theory.rename before).substitute after = theory.substitute result :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by simp only [Theory.rename,
      Theory.substitute,
      Proposition.rename_substitute proposition _ _ _
        (follows.liftSymbols symbols),
      Theory.rename_substitute rest before after result follows]

end

namespace StaticSubst.Follows

def weaken {source target : Sig} (substitution : StaticSubst source target)
    (kind : BinderKind) :
    StaticSubst.Follows
      (Rename.succ (scope := source) (kind := kind))
      (substitution.lift kind)
      (substitution.postRename
        (Rename.succ (scope := target) (kind := kind))) := by
  constructor
  · intro index
    cases kind <;> rfl
  · intro sort index
    cases kind <;> cases sort <;> rfl

end StaticSubst.Follows

namespace StaticExpr

def weaken_substitute_lift {source target : Sig} {sort : StaticSort}
    (expression : StaticExpr sort source)
    (substitution : StaticSubst source target) (kind : BinderKind) :
    expression.weaken.substitute (substitution.lift kind) =
      (expression.substitute substitution).weaken := by
  unfold StaticExpr.weaken
  rw [StaticExpr.rename_substitute expression Rename.succ
    (substitution.lift kind)
    (substitution.postRename Rename.succ)
    (StaticSubst.Follows.weaken substitution kind)]
  exact (StaticExpr.substitute_postRename expression substitution
    Rename.succ).symm

end StaticExpr

namespace StaticSubst

def comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    StaticSubst source target where
  termVar := fun index => after.termVar (before.termVar index)
  symbolVar := fun index => (before.symbolVar index).substitute after

@[simp]
theorem lift_comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target)
    (kind : BinderKind) :
    (before.comp after).lift kind =
      (before.lift kind).comp (after.lift kind) := by
  apply ext
  · intro index
    cases kind <;> cases index <;> rfl
  · intro sort index
    cases kind with
    | term =>
        cases index with
        | there index =>
            exact (StaticExpr.weaken_substitute_lift
              (before.symbolVar index) after .term).symm
    | symbol newest =>
        cases index with
        | here => cases sort <;> rfl
        | there index =>
            exact (StaticExpr.weaken_substitute_lift
              (before.symbolVar index) after (.symbol newest)).symm
    | evidence relation =>
        cases index with
        | there index =>
            exact (StaticExpr.weaken_substitute_lift
              (before.symbolVar index) after (.evidence relation)).symm

@[simp]
theorem liftMany_comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    ∀ kinds : Sig,
    (before.comp after).liftMany kinds =
      (before.liftMany kinds).comp (after.liftMany kinds)
  | [] => rfl
  | kind :: rest => by
      simp only [StaticSubst.liftMany, liftMany_comp before after rest,
        lift_comp]
      rfl

@[simp]
theorem liftSymbols_comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target)
    (symbols : List StaticSort) :
    (before.comp after).liftSymbols symbols =
      (before.liftSymbols symbols).comp (after.liftSymbols symbols) := by
  unfold StaticSubst.liftSymbols
  exact liftMany_comp _ _ _

@[simp]
theorem liftStatic_comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    (before.comp after).liftStatic symbols relations =
      (before.liftStatic symbols relations).comp
        (after.liftStatic symbols relations) := by
  unfold StaticSubst.liftStatic StaticSubst.liftEvidenceBlock
  simp

@[simp]
theorem liftModal_comp {source middle target : Sig}
    (before : StaticSubst source middle) (after : StaticSubst middle target)
    (separationCount : Nat) (modes : List CaptureMode) :
    (before.comp after).liftModal separationCount modes =
      (before.liftModal separationCount modes).comp
        (after.liftModal separationCount modes) := by
  unfold StaticSubst.liftModal StaticSubst.liftEvidenceBlock
  exact liftMany_comp _ _ _

end StaticSubst

mutual

@[simp]
def Capture.substitute_comp {source middle target : Sig}
    (capture : Capture source) (before : StaticSubst source middle)
    (after : StaticSubst middle target) :
    (capture.substitute before).substitute after =
      capture.substitute (before.comp after) :=
  match capture with
  | .empty => rfl
  | .union left right => by simp only [Capture.substitute,
      Capture.substitute_comp left, Capture.substitute_comp right]
  | .readOnly capture => by simp only [Capture.substitute,
      Capture.substitute_comp capture]
  | .singleton _ => rfl
  | .cvar name => by
      generalize equality : before.symbolVar name = expression
      cases expression with
      | capture replacement =>
          simp only [Capture.substitute, StaticSubst.comp]
          rw [equality]
          rfl

@[simp]
def SeparationContext.substitute_comp {count : Nat}
    {source middle target : Sig} (context : SeparationContext count source)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (context.substitute before).substitute after =
      context.substitute (before.comp after) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.substitute,
        SeparationContext.substitute_comp rest,
        Capture.substitute_comp capture]

@[simp]
def ModeContext.substitute_comp {modes : List CaptureMode}
    {source middle target : Sig} (context : ModeContext modes source)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (context.substitute before).substitute after =
      context.substitute (before.comp after) :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.substitute, ModeContext.substitute_comp rest,
        Capture.substitute_comp capture]

@[simp]
def ModalContext.substitute_comp {separationCount : Nat}
    {modes : List CaptureMode} {source middle target : Sig}
    (context : ModalContext separationCount modes source)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (context.substitute before).substitute after =
      context.substitute (before.comp after) :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.substitute,
        SeparationContext.substitute_comp separation,
        ModeContext.substitute_comp mode]

@[simp]
def Ty.substitute_comp {source middle target : Sig}
    (type : Ty source) (before : StaticSubst source middle)
    (after : StaticSubst middle target) :
    (type.substitute before).substitute after =
      type.substitute (before.comp after) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      generalize equality : before.symbolVar name = expression
      cases expression with
      | type replacement =>
          simp only [Ty.substitute, StaticSubst.comp]
          rw [equality]
          rfl
  | .capturing captures shape => by simp only [Ty.substitute,
      Capture.substitute_comp, Ty.substitute_comp]
  | .arr domain codomain => by simp only [Ty.substitute,
      Ty.substitute_comp]
  | .modal requirements body => by
      simp only [Ty.substitute, ModalContext.substitute_comp requirements,
        Ty.substitute_comp body]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.substitute, Theory.substitute_comp, Ty.substitute_comp,
        StaticSubst.liftStatic_comp]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.substitute, Theory.substitute_comp, Ty.substitute_comp,
        StaticSubst.liftStatic_comp]

@[simp]
def StaticExpr.substitute_comp {source middle target : Sig}
    {sort : StaticSort} (expression : StaticExpr sort source)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (expression.substitute before).substitute after =
      expression.substitute (before.comp after) :=
  match expression with
  | .type type => by simp only [StaticExpr.substitute, Ty.substitute_comp]
  | .capture capture => by simp only [StaticExpr.substitute,
      Capture.substitute_comp]

@[simp]
def Proposition.substitute_comp {source middle target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (proposition.substitute before).substitute after =
      proposition.substitute (before.comp after) :=
  match proposition with
  | .equality left right => by simp only [Proposition.substitute,
      StaticExpr.substitute_comp]
  | .inclusion lower upper => by simp only [Proposition.substitute,
      StaticExpr.substitute_comp]
  | .separate left right => by simp only [Proposition.substitute,
      Capture.substitute_comp]
  | .disjoint left right => by simp only [Proposition.substitute,
      Capture.substitute_comp]
  | .mode capture => by simp only [Proposition.substitute,
      Capture.substitute_comp]

@[simp]
def Theory.substitute_comp {source middle target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations)
    (before : StaticSubst source middle) (after : StaticSubst middle target) :
    (theory.substitute before).substitute after =
      theory.substitute (before.comp after) :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by simp only [Theory.substitute,
      Proposition.substitute_comp, Theory.substitute_comp,
      StaticSubst.liftSymbols_comp]

end

namespace StaticSubst.Follows

def instantiateAfter {source middle target : Sig}
    {before : Rename source middle} {after : StaticSubst middle target}
    {result : StaticSubst source target}
    (follows : StaticSubst.Follows before after result)
    {sort : StaticSort} (replacement : StaticExpr sort target) :
    StaticSubst.Follows
      (before.comp (Rename.succ (scope := middle) (kind := .symbol sort)))
      (after.instantiateSymbol replacement) result := by
  constructor
  · exact follows.term
  · intro other index
    exact follows.symbol index

def transRename {first middle third target : Sig}
    {before₁ : Rename first middle} {after₁ : StaticSubst middle target}
    {result₁ : StaticSubst first target}
    {before₂ : Rename middle third} {after₂ : StaticSubst third target}
    (firstFollows : StaticSubst.Follows before₁ after₁ result₁)
    (secondFollows : StaticSubst.Follows before₂ after₂ after₁) :
    StaticSubst.Follows (before₁.comp before₂) after₂ result₁ := by
  constructor
  · intro index
    change after₂.termVar (before₂.var (before₁.var index)) =
      result₁.termVar index
    rw [secondFollows.term, firstFollows.term]
  · intro sort index
    change after₂.symbolVar (before₂.var (before₁.var index)) =
      result₁.symbolVar index
    rw [secondFollows.symbol, firstFollows.symbol]

def eliminateSymbolArgs {source target : Sig}
    (base : StaticSubst source target) :
    {symbols : List StaticSort} → (arguments : SymbolArgs target symbols) →
    StaticSubst.Follows (Rename.weakenSymbols symbols)
      (StaticSubst.fromSymbolArgs base arguments) base
  | [], .nil => by
      constructor <;> intros <;> rfl
  | _ :: _, .cons newest older =>
      (eliminateSymbolArgs base older).instantiateAfter newest

end StaticSubst.Follows

namespace StaticExpr

theorem symbol_substitute {source target : Sig} {sort : StaticSort}
    (index : BVar source (.symbol sort))
    (substitution : StaticSubst source target) :
    (StaticExpr.symbol index).substitute substitution =
      substitution.symbolVar index := by
  generalize equality : substitution.symbolVar index = expression
  cases sort <;> cases expression <;>
    simp only [StaticExpr.symbol, StaticExpr.substitute, Ty.substitute,
      Capture.substitute] <;> rw [equality]

def weaken_substitute_instantiateSymbol {source target : Sig}
    {sort newest : StaticSort} (expression : StaticExpr sort source)
    (substitution : StaticSubst source target)
    (replacement : StaticExpr newest target) :
    expression.weaken.substitute
        (substitution.instantiateSymbol replacement) =
      expression.substitute substitution := by
  unfold StaticExpr.weaken
  exact StaticExpr.rename_substitute expression Rename.succ
    (substitution.instantiateSymbol replacement) substitution
    (StaticSubst.Follows.instantiateSymbol substitution replacement)

end StaticExpr

namespace StaticSubst

def instantiateSymbols_naturality {source target : Sig}
    (substitution : TermStaticSubst source target) :
    {symbols : List StaticSort} → (arguments : SymbolArgs source symbols) →
    (StaticSubst.ofSymbolArgs Rename.id arguments).comp substitution.static =
      (substitution.static.liftSymbols symbols).comp
        (StaticSubst.ofSymbolArgs Rename.id
          (arguments.substitute substitution))
  | [], .nil => by
      apply ext
      · intro index
        rfl
      · intro sort index
        simp only [StaticSubst.ofSymbolArgs, StaticSubst.fromSymbolArgs,
          StaticSubst.comp, StaticSubst.liftSymbols, symbolKinds,
          StaticSubst.liftMany, SymbolArgs.substitute]
        change ((StaticSubst.ofRename Rename.id).symbolVar index).substitute
            substitution.static =
          (substitution.static.symbolVar index).substitute
            (StaticSubst.ofRename Rename.id)
        rw [show (StaticSubst.ofRename Rename.id).symbolVar index =
          StaticExpr.symbol index by rfl,
          StaticExpr.symbol_substitute,
          StaticExpr.substitute_ofRename, StaticExpr.rename_id]
  | newestSort :: symbols, .cons newest older => by
      have induction := instantiateSymbols_naturality substitution older
      apply ext
      · intro index
        cases index with
        | there index =>
            exact congrArg (fun current => current.termVar index) induction
      · intro sort index
        cases index with
        | here =>
            simp only [StaticSubst.ofSymbolArgs,
              StaticSubst.fromSymbolArgs, StaticSubst.comp,
              StaticSubst.liftSymbols, symbolKinds, StaticSubst.liftMany,
              StaticSubst.lift, StaticSubst.liftSymbol,
              SymbolArgs.substitute]
            change newest.substitute substitution.static =
              (StaticExpr.symbol (.here : BVar
                (SymbolScope target (newestSort :: symbols))
                  (.symbol newestSort))).substitute
                ((StaticSubst.ofSymbolArgs Rename.id
                  (older.substitute substitution)).instantiateSymbol
                    (newest.substitute substitution.static))
            rw [StaticExpr.symbol_substitute]
            rfl
        | there index =>
            simp only [StaticSubst.ofSymbolArgs, StaticSubst.fromSymbolArgs,
              StaticSubst.comp, StaticSubst.liftSymbols, symbolKinds,
              StaticSubst.liftMany, StaticSubst.lift,
              StaticSubst.liftSymbol,
              SymbolArgs.substitute]
            change ((StaticSubst.ofSymbolArgs Rename.id older).symbolVar
                index).substitute substitution.static =
              ((substitution.static.liftSymbols symbols).symbolVar
                index).weaken.substitute
                  ((StaticSubst.ofSymbolArgs Rename.id
                    (older.substitute substitution)).instantiateSymbol
                      (newest.substitute substitution.static))
            rw [StaticExpr.weaken_substitute_instantiateSymbol]
            exact congrArg (fun current => current.symbolVar index) induction

end StaticSubst

namespace Proposition

def instantiateSymbols_substitute {source target : Sig}
    {symbols : List StaticSort} {relation : Relation}
    (proposition : Proposition relation (SymbolScope source symbols))
    (arguments : SymbolArgs source symbols)
    (substitution : TermStaticSubst source target) :
    (proposition.instantiateSymbols arguments).substitute
        substitution.static =
      (proposition.substitute
        (substitution.static.liftSymbols symbols)).instantiateSymbols
          (arguments.substitute substitution) := by
  unfold Proposition.instantiateSymbols
  rw [Proposition.substitute_comp, Proposition.substitute_comp,
    StaticSubst.instantiateSymbols_naturality]

end Proposition

namespace ConstraintRef

def toEvidenceBVar (symbolScope : Sig) {relations : List Relation}
    {relation : Relation} : ConstraintRef relations relation →
    BVar (Sig.extendMany symbolScope (evidenceKinds relations))
      (.evidence relation)
  | .here => .here
  | .there reference => .there (reference.toEvidenceBVar symbolScope)

end ConstraintRef

namespace EvidenceArgs

@[simp]
theorem lookup_rename {source target : Sig} {relations : List Relation}
    (arguments : EvidenceArgs source relations) (rho : Rename source target)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    (arguments.rename rho).lookup reference =
      (arguments.lookup reference).rename rho := by
  induction arguments with
  | nil => nomatch reference
  | cons newest older induction =>
      cases reference with
      | here => rfl
      | there reference => exact induction reference

end EvidenceArgs

namespace Theory

def propositionAt_rename {source target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations) (rho : Rename source target)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    (theory.rename rho).propositionAt reference =
      (theory.propositionAt reference).rename (rho.liftSymbols symbols) := by
  cases theory with
  | nil => nomatch reference
  | cons proposition rest =>
      cases reference with
      | here => rfl
      | there reference => exact propositionAt_rename rest rho reference

end Theory

namespace TheoryMap

@[simp]
theorem openedEvidence_lookup (symbolScope : Sig)
    {relations : List Relation} {relation : Relation}
    (reference : ConstraintRef relations relation) :
    (openedEvidence symbolScope relations).lookup reference =
      .var (reference.toEvidenceBVar symbolScope) := by
  induction reference with
  | here => rfl
  | there reference induction =>
      simp [openedEvidence, induction, ConstraintRef.toEvidenceBVar,
        Evidence.rename]

end TheoryMap

namespace Ctx

def lookup_extendTheoryEvidence_constraint {scope : Sig}
    {symbols : List StaticSort} (symbolContext : Ctx (SymbolScope scope symbols))
    {relations : List Relation} (theory : Theory scope symbols relations)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    (extendTheoryEvidence symbolContext theory).lookup
        (reference.toEvidenceBVar (SymbolScope scope symbols)) =
      Binding.evidence
        ((theory.propositionAt reference).rename
          (Rename.weakenMany (SymbolScope scope symbols)
            (evidenceKinds relations))) := by
  cases theory with
  | nil => nomatch reference
  | cons proposition rest =>
      rename_i _ relations
      cases reference with
      | here =>
          change Binding.evidence
              ((proposition.rename
                (Rename.weakenMany (SymbolScope scope symbols)
                  (evidenceKinds relations))).rename Rename.succ) =
            Binding.evidence
              (proposition.rename
                (Rename.weakenMany (SymbolScope scope symbols)
                  (evidenceKinds (_ :: relations))))
          rw [Proposition.rename_comp]
          rfl
      | there reference =>
          change ((extendTheoryEvidence symbolContext rest).lookup
              (reference.toEvidenceBVar
                (SymbolScope scope symbols))).weaken =
            Binding.evidence
              ((rest.propositionAt reference).rename
                (Rename.weakenMany (SymbolScope scope symbols)
                  (evidenceKinds (_ :: relations))))
          rw [lookup_extendTheoryEvidence_constraint symbolContext rest
            reference]
          change Binding.evidence
              (((rest.propositionAt reference).rename
                (Rename.weakenMany (SymbolScope scope symbols)
                  (evidenceKinds relations))).rename Rename.succ) = _
          rw [Proposition.rename_comp]
          rfl

end Ctx

namespace Binding

def substitute {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (substitution : StaticSubst source target) :
    Binding target kind :=
  match binding with
  | .term type => .term (type.substitute substitution)
  | .symbol => .symbol
  | .evidence proposition => .evidence (proposition.substitute substitution)

def rename_substitute {source middle target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (before : Rename source middle)
    (after : StaticSubst middle target) (result : StaticSubst source target)
    (follows : StaticSubst.Follows before after result) :
    (binding.rename before).substitute after = binding.substitute result := by
  cases binding with
  | term type => simp [Binding.rename, Binding.substitute,
      Ty.rename_substitute type before after result follows]
  | symbol => rfl
  | evidence proposition => simp [Binding.rename, Binding.substitute,
      Proposition.rename_substitute proposition before after result follows]

@[simp]
theorem evidenceProposition_rename {source target : Sig}
    {relation : Relation} (binding : Binding source (.evidence relation))
    (rho : Rename source target) :
    (binding.rename rho).evidenceProposition =
      binding.evidenceProposition.rename rho := by
  cases binding
  rfl

@[simp]
theorem substitute_ofRename {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (rho : Rename source target) :
    binding.substitute (StaticSubst.ofRename rho) = binding.rename rho := by
  cases binding <;> simp [Binding.substitute, Binding.rename]

end Binding

namespace Ctx

def lookup_extendSymbols {scope : Sig} (context : Ctx scope) :
    (symbols : List StaticSort) → {kind : BinderKind} →
      (index : BVar scope kind) →
    (context.extendSymbols symbols).lookup
        ((Rename.weakenSymbols symbols).var index) =
      (context.lookup index).rename (Rename.weakenSymbols symbols)
  | [], _, index => by
      simpa only [symbolKinds, Rename.weakenMany, Rename.id_var] using
        (Binding.rename_id (context.lookup index)).symm
  | sort :: rest, _, index => by
      change ((context.extendSymbols rest).lookup
          ((Rename.weakenSymbols rest).var index)).rename
            (Rename.succ (kind := .symbol sort)) =
        (context.lookup index).rename
          ((Rename.weakenSymbols rest).comp Rename.succ)
      rw [lookup_extendSymbols context rest index]
      exact Binding.rename_comp _ _ _

def lookup_extendTheoryEvidence {ambient : Sig}
    {symbols : List StaticSort}
    (symbolContext : Ctx (SymbolScope ambient symbols)) :
    {relations : List Relation} →
      (theory : Theory ambient symbols relations) →
      {kind : BinderKind} →
      (index : BVar (SymbolScope ambient symbols) kind) →
    (extendTheoryEvidence symbolContext theory).lookup
        ((Rename.weakenMany (SymbolScope ambient symbols)
          (evidenceKinds relations)).var index) =
      (symbolContext.lookup index).rename
        (Rename.weakenMany (SymbolScope ambient symbols)
          (evidenceKinds relations))
  | [], .nil, _, index => by
      simpa only [evidenceKinds, Rename.weakenMany, Rename.id_var] using
        (Binding.rename_id (symbolContext.lookup index)).symm
  | relation :: relations, .cons proposition rest, _, index => by
      change ((extendTheoryEvidence symbolContext rest).lookup
          ((Rename.weakenMany (SymbolScope ambient symbols)
            (evidenceKinds relations)).var index)).rename
              (Rename.succ (kind := .evidence relation)) =
        (symbolContext.lookup index).rename
          ((Rename.weakenMany (SymbolScope ambient symbols)
            (evidenceKinds relations)).comp Rename.succ)
      rw [lookup_extendTheoryEvidence symbolContext rest index]
      exact Binding.rename_comp _ _ _

def lookup_extendTheory_ambient {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) {kind : BinderKind}
    (index : BVar scope kind) :
    (context.extendTheory theory).lookup
        ((Rename.weakenStatic symbols relations).var index) =
      (context.lookup index).rename
        (Rename.weakenStatic symbols relations) := by
  unfold extendTheory Rename.weakenStatic
  rw [Rename.comp_var]
  rw [lookup_extendTheoryEvidence (context.extendSymbols symbols) theory]
  rw [lookup_extendSymbols]
  exact Binding.rename_comp _ _ _

end Ctx

namespace Proposition

def rename_instantiateSymbols {source target : Sig}
    {symbols : List StaticSort} {relation : Relation}
    (proposition : Proposition relation (SymbolScope source symbols))
    (rho : Rename source target) (arguments : SymbolArgs target symbols) :
    (proposition.rename (rho.liftSymbols symbols)).instantiateSymbols
        arguments =
      proposition.substitute
        (StaticSubst.fromSymbolArgs (StaticSubst.ofRename rho) arguments) :=
  Proposition.rename_substitute proposition (rho.liftSymbols symbols)
    (StaticSubst.ofSymbolArgs Rename.id arguments)
    (StaticSubst.fromSymbolArgs (StaticSubst.ofRename rho) arguments)
    (StaticSubst.Follows.fromSymbolArgs rho arguments)

def weakenEvidence_substitute {source target : Sig}
    {relations : List Relation} {relation : Relation}
    (proposition : Proposition relation source)
    (base : TermStaticSubst source target)
    (arguments : EvidenceArgs target relations) :
    (proposition.rename
      (Rename.weakenMany source (evidenceKinds relations))).substitute
        (TermStaticSubst.fromEvidenceArgs base arguments).static =
      proposition.substitute base.static :=
  Proposition.rename_substitute proposition
    (Rename.weakenMany source (evidenceKinds relations))
    (TermStaticSubst.fromEvidenceArgs base arguments).static base.static
    (StaticSubst.Follows.fromEvidenceArgs base arguments)

end Proposition

namespace TermStaticSubst

def ofRename {source target : Sig} (rho : Rename source target) :
    TermStaticSubst source target where
  static := StaticSubst.ofRename rho
  evidenceVar := fun index => .var (rho.var index)

@[simp]
theorem fromSymbolArgs_static {source target : Sig}
    (base : TermStaticSubst source target) {symbols : List StaticSort}
    (arguments : SymbolArgs target symbols) :
    (TermStaticSubst.fromSymbolArgs base arguments).static =
      StaticSubst.fromSymbolArgs base.static arguments := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      simp [TermStaticSubst.fromSymbolArgs,
        StaticSubst.fromSymbolArgs, TermStaticSubst.instantiateSymbol,
        induction]

structure Preserves {source target : Sig}
    (sourceContext : Ctx source) (targetContext : Ctx target)
    (substitution : TermStaticSubst source target) : Type where
  term : ∀ index : BVar source .term,
    targetContext.lookup (substitution.static.termVar index) =
      (sourceContext.lookup index).substitute substitution.static
  evidence : ∀ {relation : Relation}
      (index : BVar source (.evidence relation)),
    Evidence.Proves targetContext (substitution.evidenceVar index)
      ((sourceContext.lookup index).evidenceProposition.substitute
        substitution.static)

namespace Preserves

noncomputable def weakenTheory {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) :
    (TermStaticSubst.ofRename
      (Rename.weakenStatic symbols relations)).Preserves context
        (context.extendTheory theory) := by
  constructor
  · intro index
    change (context.extendTheory theory).lookup
        ((Rename.weakenStatic symbols relations).var index) =
      (context.lookup index).substitute
        (StaticSubst.ofRename
          (Rename.weakenStatic symbols relations))
    rw [Ctx.lookup_extendTheory_ambient]
    exact (Binding.substitute_ofRename _ _).symm
  · intro relation index
    change Evidence.Proves (context.extendTheory theory)
      (.var ((Rename.weakenStatic symbols relations).var index))
      ((context.lookup index).evidenceProposition.substitute
        (StaticSubst.ofRename
          (Rename.weakenStatic symbols relations)))
    apply Evidence.Proves.var
    rw [Ctx.lookup_extendTheory_ambient]
    cases context.lookup index with
    | evidence proposition =>
        simp [Binding.rename, Binding.evidenceProposition,
          Proposition.substitute_ofRename]

noncomputable def instantiateSymbol {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    {sort : StaticSort} (replacement : StaticExpr sort target) :
    (substitution.instantiateSymbol replacement).Preserves
      (sourceContext.extendSymbol sort) targetContext := by
  let follows := StaticSubst.Follows.instantiateSymbol
    substitution.static replacement
  constructor
  · intro index
    cases index with
    | there index =>
        change targetContext.lookup (substitution.static.termVar index) =
          ((sourceContext.lookup index).rename Rename.succ).substitute
            (substitution.instantiateSymbol replacement).static
        rw [preserves.term]
        exact (Binding.rename_substitute (sourceContext.lookup index)
          Rename.succ _ _ follows).symm
  · intro relation index
    cases index with
    | there index =>
        simp only [TermStaticSubst.instantiateSymbol, Ctx.extendSymbol,
          Ctx.lookup_there, Binding.weaken,
          Binding.evidenceProposition_rename]
        change Evidence.Proves targetContext
          (substitution.evidenceVar index)
          (((sourceContext.lookup index).evidenceProposition.rename
            Rename.succ).substitute
              (substitution.instantiateSymbol replacement).static)
        have typing := preserves.evidence index
        have fusion := Proposition.rename_substitute
          (sourceContext.lookup index).evidenceProposition Rename.succ
          (substitution.instantiateSymbol replacement).static
          substitution.static follows
        rw [fusion]
        exact typing

noncomputable def fromSymbolArgs {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {base : TermStaticSubst source target}
    (preserves : base.Preserves sourceContext targetContext) :
    {symbols : List StaticSort} → (arguments : SymbolArgs target symbols) →
    (TermStaticSubst.fromSymbolArgs base arguments).Preserves
      (sourceContext.extendSymbols symbols) targetContext
  | [], .nil => preserves
  | _ :: _, .cons newest older =>
      (fromSymbolArgs preserves older).instantiateSymbol newest

noncomputable def instantiateEvidence {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    {relation : Relation} {proposition : Proposition relation source}
    {replacement : Evidence relation target}
    (replacementTyping : Evidence.Proves targetContext replacement
      (proposition.substitute substitution.static)) :
    (substitution.instantiateEvidence replacement).Preserves
      (sourceContext.extendEvidence proposition) targetContext := by
  let follows := StaticSubst.Follows.dropEvidence
    substitution.static relation
  constructor
  · intro index
    cases index with
    | there index =>
        change targetContext.lookup (substitution.static.termVar index) =
          ((sourceContext.lookup index).rename Rename.succ).substitute
            (substitution.instantiateEvidence replacement).static
        rw [preserves.term]
        exact (Binding.rename_substitute (sourceContext.lookup index)
          Rename.succ _ _ follows).symm
  · intro other index
    cases index with
    | here =>
        change Evidence.Proves targetContext replacement
          ((proposition.rename Rename.succ).substitute
            (substitution.instantiateEvidence replacement).static)
        have fusion := Proposition.rename_substitute proposition Rename.succ
          (substitution.instantiateEvidence replacement).static
          substitution.static follows
        rw [fusion]
        exact replacementTyping
    | there index =>
        simp only [TermStaticSubst.instantiateEvidence, Ctx.extendEvidence,
          Ctx.lookup_there, Binding.weaken,
          Binding.evidenceProposition_rename]
        change Evidence.Proves targetContext
          (substitution.evidenceVar index)
          (((sourceContext.lookup index).evidenceProposition.rename
            Rename.succ).substitute
              (substitution.instantiateEvidence replacement).static)
        have typing := preserves.evidence index
        have fusion := Proposition.rename_substitute
          (sourceContext.lookup index).evidenceProposition Rename.succ
          (substitution.instantiateEvidence replacement).static
          substitution.static follows
        rw [fusion]
        exact typing

noncomputable def fromTheoryEvidence {source target : Sig}
    {symbols : List StaticSort} {targetContext : Ctx target}
    (rho : Rename source target)
    (symbolContext : Ctx (SymbolScope source symbols))
    (arguments : SymbolArgs target symbols)
    (base : TermStaticSubst (SymbolScope source symbols) target)
    (baseEq : base.static =
      StaticSubst.fromSymbolArgs (StaticSubst.ofRename rho) arguments)
    (basePreserves : base.Preserves symbolContext targetContext) :
    {relations : List Relation} →
      (theory : Theory source symbols relations) →
      (evidence : EvidenceArgs target relations) →
      Theory.SatisfiedBy targetContext arguments (theory.rename rho)
        evidence →
    (TermStaticSubst.fromEvidenceArgs base evidence).Preserves
      (Ctx.extendTheoryEvidence symbolContext theory) targetContext
  | [], .nil, .nil, satisfaction => by
      cases satisfaction
      exact basePreserves
  | relation :: relations, .cons proposition rest, .cons newest older,
      satisfaction => by
      change Theory.SatisfiedBy targetContext arguments
        (.cons (proposition.rename (rho.liftSymbols symbols))
          (rest.rename rho)) (.cons newest older) at satisfaction
      cases satisfaction with
      | cons head tail =>
          let olderPreserves := fromTheoryEvidence rho symbolContext arguments
            base baseEq basePreserves rest older tail
          let stored := proposition.rename
            (Rename.weakenMany (SymbolScope source symbols)
              (evidenceKinds relations))
          have cancelled :
              stored.substitute
                  (TermStaticSubst.fromEvidenceArgs base older).static =
                proposition.substitute base.static := by
            exact Proposition.weakenEvidence_substitute proposition base older
          have mapped :
              (proposition.rename
                (rho.liftSymbols symbols)).instantiateSymbols arguments =
                  proposition.substitute base.static := by
            rw [baseEq]
            exact Proposition.rename_instantiateSymbols proposition rho
              arguments
          have newestTyping : Evidence.Proves targetContext newest
              (stored.substitute
                (TermStaticSubst.fromEvidenceArgs base older).static) := by
            rw [cancelled, ← mapped]
            exact head
          exact olderPreserves.instantiateEvidence newestTyping

end Preserves

end TermStaticSubst

namespace Evidence.Proves

noncomputable def substitute {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {relation : Relation}
    {evidence : Evidence relation source}
    {proposition : Proposition relation source}
    (typing : Evidence.Proves sourceContext evidence proposition)
    (substitution : TermStaticSubst source target)
    (preserves : substitution.Preserves sourceContext targetContext) :
    Evidence.Proves targetContext (evidence.substitute substitution)
      (proposition.substitute substitution.static) := by
  induction typing with
  | var binding =>
      rename_i relation' index proposition'
      have result := preserves.evidence index
      rw [binding] at result
      exact result
  | equalityRefl => exact .equalityRefl _
  | equalitySymm _ induction => exact .equalitySymm induction
  | equalityTrans _ _ firstInduction secondInduction =>
      exact .equalityTrans firstInduction secondInduction
  | equalityArrow _ _ domainInduction codomainInduction =>
      exact .equalityArrow domainInduction codomainInduction
  | equalityCapturing _ _ captureInduction shapeInduction =>
      exact .equalityCapturing captureInduction shapeInduction
  | equalityCaptureUnion _ _ leftInduction rightInduction =>
      exact .equalityCaptureUnion leftInduction rightInduction
  | equalityCaptureReadOnly _ induction =>
      exact .equalityCaptureReadOnly induction
  | inclusionRefl => exact .inclusionRefl _
  | inclusionTrans _ _ firstInduction secondInduction =>
      exact .inclusionTrans firstInduction secondInduction
  | equalityToInclusion _ induction =>
      exact .equalityToInclusion induction
  | typeTop => exact .typeTop _
  | typeBottom => exact .typeBottom _
  | typeArrow _ _ domainInduction codomainInduction =>
      exact .typeArrow domainInduction codomainInduction
  | typeCapturing _ _ captureInduction shapeInduction =>
      exact .typeCapturing captureInduction shapeInduction
  | captureEmpty => exact .captureEmpty _
  | captureUnionLeft => exact .captureUnionLeft _ _
  | captureUnionRight => exact .captureUnionRight _ _
  | captureUnionElim _ _ leftInduction rightInduction =>
      exact .captureUnionElim leftInduction rightInduction
  | captureVariable binding =>
      rename_i index captures shape
      exact Evidence.Proves.captureVariable
        (captures := captures.substitute substitution.static)
        (shape := shape.substitute substitution.static) (by
          rw [preserves.term]
          simp [binding, Binding.substitute, Ty.substitute])
  | captureReadOnly => exact .captureReadOnly _
  | captureReadOnlyMono _ induction =>
      exact .captureReadOnlyMono induction
  | modeEmpty => exact .modeEmpty _
  | modeUnion _ _ leftInduction rightInduction =>
      exact .modeUnion leftInduction rightInduction
  | modeSubcapture _ _ subcaptureInduction modeInduction =>
      exact .modeSubcapture subcaptureInduction modeInduction
  | modeWritable => exact .modeWritable _
  | modeReadOnly => exact .modeReadOnly _
  | separateSymm _ induction => exact .separateSymm induction
  | separateUnion _ _ leftInduction rightInduction =>
      exact .separateUnion leftInduction rightInduction
  | separateEmpty => exact .separateEmpty _
  | separateReadOnly _ _ leftInduction rightInduction =>
      exact .separateReadOnly leftInduction rightInduction
  | separateSubcapture _ _ subcaptureInduction separationInduction =>
      exact .separateSubcapture subcaptureInduction separationInduction
  | separateOfDisjoint _ induction => exact .separateOfDisjoint induction
  | disjointSymm _ induction => exact .disjointSymm induction
  | disjointUnion _ _ leftInduction rightInduction =>
      exact .disjointUnion leftInduction rightInduction
  | disjointEmpty => exact .disjointEmpty _
  | disjointEquality _ _ equalityInduction disjointInduction =>
      exact .disjointEquality equalityInduction disjointInduction

end Evidence.Proves

namespace TheoryMap

def fromBoundSymbols {scope target : Sig} (symbols : List StaticSort)
    (rho : Rename (SymbolScope scope symbols) target) :
    StaticSubst.fromSymbolArgs
        (StaticSubst.ofRename
          ((Rename.weakenSymbols symbols).comp rho))
        ((boundSymbols scope symbols).rename rho) =
      StaticSubst.ofRename rho := by
  induction symbols generalizing target with
  | nil =>
      have identity := congrArg (fun current =>
        StaticSubst.ofRename current) (Rename.id_comp rho)
      simpa only [Rename.weakenSymbols, symbolKinds, Rename.weakenMany,
        boundSymbols, SymbolArgs.rename, StaticSubst.fromSymbolArgs] using
          identity
  | cons sort rest induction =>
      simp only [boundSymbols, SymbolArgs.rename,
        StaticSubst.fromSymbolArgs]
      rw [SymbolArgs.rename_comp]
      have ambientEq :
          (Rename.weakenSymbols (sort :: rest)).comp rho =
            (Rename.weakenSymbols rest).comp
              ((Rename.succ (scope := SymbolScope scope rest)
                (kind := .symbol sort)).comp rho) := by
        rw [← Rename.comp_assoc]
        rfl
      rw [ambientEq]
      have previousEq := induction ((Rename.succ
        (scope := SymbolScope scope rest) (kind := .symbol sort)).comp rho)
      calc
        ((StaticSubst.ofRename ((Rename.weakenSymbols rest).comp
            (Rename.succ.comp rho))).fromSymbolArgs
            ((boundSymbols scope rest).rename
              (Rename.succ.comp rho))).instantiateSymbol
                ((StaticExpr.symbol BVar.here).rename rho) =
          (StaticSubst.ofRename (Rename.succ.comp rho)).instantiateSymbol
            ((StaticExpr.symbol BVar.here).rename rho) :=
          congrArg (fun current => current.instantiateSymbol
            ((StaticExpr.symbol BVar.here).rename rho)) previousEq
        _ = StaticSubst.ofRename rho := by
          apply StaticSubst.ext
          · intro index
            cases index with
            | there index => rfl
          · exact fun {_lookedSort} index => by
              cases index with
              | here =>
                  exact TheoryMap.rename_symbol
                    (BVar.here : BVar (SymbolScope scope (sort :: rest))
                      (.symbol sort)) rho
              | there index => rfl

def identitySymbolSubstitution (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) :
    StaticSubst.fromSymbolArgs
        (StaticSubst.ofRename
          (Rename.weakenStatic symbols relations))
        (openedSymbols scope symbols relations) =
      StaticSubst.ofRename
        (Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds relations)) := by
  unfold openedSymbols Rename.weakenStatic
  exact fromBoundSymbols symbols
    (Rename.weakenMany (SymbolScope scope symbols)
      (evidenceKinds relations))

@[simp]
theorem identity_mappedConstraintAt {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) {relation : Relation}
    (reference : ConstraintRef relations relation) :
    (identity theory).mappedConstraintAt reference =
      (theory.propositionAt reference).rename
        (Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds relations)) := by
  unfold mappedConstraintAt openedTarget identity
  rw [Theory.propositionAt_rename,
    Proposition.rename_instantiateSymbols,
    identitySymbolSubstitution, Proposition.substitute_ofRename]

def substitution_followsAmbient {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) :
    StaticSubst.Follows
      (Rename.weakenStatic targetSymbols targetRelations)
      mapping.substitution.static
      (StaticSubst.ofRename
        (Rename.weakenStatic (scope := scope)
          sourceSymbols sourceRelations)) := by
  let base := TermStaticSubst.ofRename
    (Rename.weakenStatic (scope := scope) sourceSymbols sourceRelations)
  let symbolSubstitution := TermStaticSubst.fromSymbolArgs base mapping.symbols
  have symbols := StaticSubst.Follows.eliminateSymbolArgs base.static
    mapping.symbols
  have evidence := StaticSubst.Follows.fromEvidenceArgs symbolSubstitution
    mapping.evidence
  change StaticSubst.Follows
    ((Rename.weakenSymbols targetSymbols).comp
      (Rename.weakenMany (SymbolScope scope targetSymbols)
        (evidenceKinds targetRelations)))
    (TermStaticSubst.fromEvidenceArgs symbolSubstitution
      mapping.evidence).static base.static
  exact symbols.transRename (by
    simpa [symbolSubstitution] using evidence)

noncomputable def substitution_preserves {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {mapping : TheoryMap source target}
    (typing : HasType context mapping) :
    mapping.substitution.Preserves (context.extendTheory target)
      (context.extendTheory source) := by
  let rho := Rename.weakenStatic (scope := scope)
    sourceSymbols sourceRelations
  let base := TermStaticSubst.ofRename rho
  let ambient := TermStaticSubst.Preserves.weakenTheory context source
  let symbolPreserves :=
    TermStaticSubst.Preserves.fromSymbolArgs ambient mapping.symbols
  change Theory.SatisfiedBy (context.extendTheory source) mapping.symbols
    (target.rename rho) mapping.evidence at typing
  change (TermStaticSubst.fromEvidenceArgs
      (TermStaticSubst.fromSymbolArgs base mapping.symbols)
      mapping.evidence).Preserves
    (Ctx.extendTheoryEvidence (context.extendSymbols targetSymbols) target)
    (context.extendTheory source)
  exact TermStaticSubst.Preserves.fromTheoryEvidence rho
    (context.extendSymbols targetSymbols) mapping.symbols
    (TermStaticSubst.fromSymbolArgs base mapping.symbols)
    (TermStaticSubst.fromSymbolArgs_static base mapping.symbols)
    symbolPreserves target mapping.evidence typing

def openedTarget_substitute {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source middle) :
    (openedTarget middle target).substitute mapping.substitution.static =
      openedTarget source target := by
  unfold openedTarget
  rw [Theory.rename_substitute target
    (Rename.weakenStatic middleSymbols middleRelations)
    mapping.substitution.static
    (StaticSubst.ofRename
      (Rename.weakenStatic sourceSymbols sourceRelations))
    (mapping.substitution_followsAmbient)]
  exact Theory.substitute_ofRename target _

end TheoryMap

namespace Theory.SatisfiedBy

noncomputable def ofConstraintAt {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    (proofs : ∀ {relation : Relation}
      (reference : ConstraintRef relations relation),
      Evidence.Proves context (evidence.lookup reference)
        ((theory.propositionAt reference).instantiateSymbols arguments)) :
    Theory.SatisfiedBy context arguments theory evidence := by
  cases theory with
  | nil =>
      cases evidence
      exact .nil
  | cons proposition rest =>
      cases evidence with
      | cons newest older =>
          exact Theory.SatisfiedBy.cons (proofs .here)
            (ofConstraintAt (theory := rest) (evidence := older)
              (fun reference => proofs (.there reference)))

noncomputable def substitute {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {symbols : List StaticSort} {arguments : SymbolArgs source symbols}
    {relations : List Relation} {theory : Theory source symbols relations}
    {evidence : EvidenceArgs source relations}
    (satisfaction : Theory.SatisfiedBy sourceContext arguments theory evidence)
    (substitution : TermStaticSubst source target)
    (preserves : substitution.Preserves sourceContext targetContext) :
    Theory.SatisfiedBy targetContext (arguments.substitute substitution)
      (theory.substitute substitution.static)
      (evidence.substitute substitution) := by
  induction satisfaction with
  | nil => exact .nil
  | cons head tail induction =>
      have substituted := Evidence.Proves.substitute head substitution
        preserves
      rw [Proposition.instantiateSymbols_substitute] at substituted
      exact Theory.SatisfiedBy.cons substituted induction

end Theory.SatisfiedBy

namespace TheoryMap

noncomputable def identity_hasType {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (context : Ctx scope) (theory : Theory scope symbols relations) :
    HasType context (identity theory) := by
  apply Theory.SatisfiedBy.ofConstraintAt
  intro relation reference
  change Evidence.Proves (context.extendTheory theory)
    ((identity theory).evidenceAt reference)
    ((identity theory).mappedConstraintAt reference)
  unfold evidenceAt
  change Evidence.Proves (context.extendTheory theory)
    ((openedEvidence (SymbolScope scope symbols) relations).lookup reference)
    ((identity theory).mappedConstraintAt reference)
  rw [openedEvidence_lookup]
  apply Evidence.Proves.var
  unfold Ctx.extendTheory
  rw [Ctx.lookup_extendTheoryEvidence_constraint]
  rw [identity_mappedConstraintAt]

theorem identity_check_isSome {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (context : Ctx scope) (theory : Theory scope symbols relations) :
    (check context (identity theory)).isSome = true :=
  check_isSome_iff.mpr ⟨identity_hasType context theory⟩

noncomputable def compose_hasType {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {first : TheoryMap source middle}
    {second : TheoryMap middle target}
    (firstTyping : HasType context first)
    (secondTyping : HasType context second) :
    HasType context (compose first second) := by
  have result := Theory.SatisfiedBy.substitute secondTyping
    first.substitution (first.substitution_preserves firstTyping)
  rw [openedTarget_substitute first] at result
  exact result

theorem compose_check_isSome {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {first : TheoryMap source middle}
    {second : TheoryMap middle target}
    (firstTyping : HasType context first)
    (secondTyping : HasType context second) :
    (check context (compose first second)).isSome = true :=
  check_isSome_iff.mpr ⟨compose_hasType firstTyping secondTyping⟩

end TheoryMap

end ManySortedFC
