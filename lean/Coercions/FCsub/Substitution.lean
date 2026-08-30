import Coercions.FCsub.Recursion

/-!
# Four-sort substitution for standalone FCsub

The type-only substitution in `FCsub.Telescope` is sufficient for telescope
endpoints.  Operational semantics additionally has to eliminate ordinary
term binders, abstract type names, equality evidence, and directed-inclusion
evidence.  `Subst` supplies all four sorts simultaneously and is used by
ordinary beta reduction, package opening, static application, and `newtype`.
-/

namespace FCsub

/-- A simultaneous, capture-avoiding substitution for every variable sort
that can occur in FCsub syntax. -/
structure Subst (source target : Sig) where
  termVar : BVar source .term → Tm target
  typeVar : BVar source .type → Ty target
  equalityVar : BVar source (.evidence .equality) → EqCo target
  inclusionVar : BVar source (.evidence .inclusion) → LeCo target

namespace Subst

@[ext]
theorem ext {source target : Sig} {first second : Subst source target}
    (terms : ∀ index, first.termVar index = second.termVar index)
    (types : ∀ index, first.typeVar index = second.typeVar index)
    (equalities : ∀ index,
      first.equalityVar index = second.equalityVar index)
    (inclusions : ∀ index,
      first.inclusionVar index = second.inclusionVar index) :
    first = second := by
  cases first
  cases second
  congr
  · funext index
    exact terms index
  · funext index
    exact types index
  · funext index
    exact equalities index
  · funext index
    exact inclusions index

/-- Identity four-sort substitution. -/
def id {scope : Sig} : Subst scope scope where
  termVar := Tm.var
  typeVar := Ty.tvar
  equalityVar := EqCo.var
  inclusionVar := LeCo.var

/-- Embed a kind-preserving renaming as a substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    Subst source target where
  termVar := fun index => .var (rho.var index)
  typeVar := fun index => .tvar (rho.var index)
  equalityVar := fun index => .var (rho.var index)
  inclusionVar := fun index => .var (rho.var index)

/-- Preserve a fresh ordinary term variable. -/
def liftTerm {source target : Sig} (substitution : Subst source target) :
    Subst (source ▹ .term) (target ▹ .term) where
  termVar := fun
    | .here => .var .here
    | .there index => (substitution.termVar index).weaken
  typeVar := fun
    | .there index => (substitution.typeVar index).weaken
  equalityVar := fun
    | .there index => (substitution.equalityVar index).weaken
  inclusionVar := fun
    | .there index => (substitution.inclusionVar index).weaken

/-- Preserve a fresh abstract type name. -/
def liftType {source target : Sig} (substitution : Subst source target) :
    Subst (source ▹ .type) (target ▹ .type) where
  termVar := fun
    | .there index => (substitution.termVar index).weaken
  typeVar := fun
    | .here => .tvar .here
    | .there index => (substitution.typeVar index).weaken
  equalityVar := fun
    | .there index => (substitution.equalityVar index).weaken
  inclusionVar := fun
    | .there index => (substitution.inclusionVar index).weaken

/-- Preserve a fresh equality-evidence variable. -/
def liftEquality {source target : Sig}
    (substitution : Subst source target) :
    Subst (source ▹ .evidence .equality)
      (target ▹ .evidence .equality) where
  termVar := fun
    | .there index => (substitution.termVar index).weaken
  typeVar := fun
    | .there index => (substitution.typeVar index).weaken
  equalityVar := fun
    | .here => .var .here
    | .there index => (substitution.equalityVar index).weaken
  inclusionVar := fun
    | .there index => (substitution.inclusionVar index).weaken

/-- Preserve a fresh directed-inclusion-evidence variable. -/
def liftInclusion {source target : Sig}
    (substitution : Subst source target) :
    Subst (source ▹ .evidence .inclusion)
      (target ▹ .evidence .inclusion) where
  termVar := fun
    | .there index => (substitution.termVar index).weaken
  typeVar := fun
    | .there index => (substitution.typeVar index).weaken
  equalityVar := fun
    | .there index => (substitution.equalityVar index).weaken
  inclusionVar := fun
    | .here => .var .here
    | .there index => (substitution.inclusionVar index).weaken

/-- Preserve one heterogeneous binder. -/
def lift {source target : Sig} (substitution : Subst source target)
    (kind : BinderKind) : Subst (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => substitution.liftTerm
  | .type => substitution.liftType
  | .evidence .equality => substitution.liftEquality
  | .evidence .inclusion => substitution.liftInclusion

/-- Preserve a homogeneous suffix of binders. -/
def liftN {source target : Sig} (substitution : Subst source target)
    (kind : BinderKind) : (count : Nat) →
    Subst (Sig.extendN source kind count) (Sig.extendN target kind count)
  | 0 => substitution
  | count + 1 => (liftN substitution kind count).lift kind

def liftTypes {source target : Sig} (substitution : Subst source target)
    (names : Nat) :
    Subst (TypeScope source names) (TypeScope target names) :=
  substitution.liftN .type names

def liftStatic {source target : Sig} (substitution : Subst source target)
    (names constraints : Nat) :
    Subst (StaticScope source names constraints)
      (StaticScope target names constraints) :=
  (substitution.liftTypes names).liftN (.evidence .inclusion) constraints

def liftPayload {source target : Sig} (substitution : Subst source target)
    (names constraints : Nat) :
    Subst (PayloadScope source names constraints)
      (PayloadScope target names constraints) :=
  (substitution.liftStatic names constraints).liftTerm

def liftNewtype {source target : Sig} (substitution : Subst source target) :
    Subst (NewtypeScope source) (NewtypeScope target) :=
  substitution.liftType.liftEquality

/-- Eliminate the newest ordinary term variable. -/
def instantiateTerm {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target) :
    Subst (source ▹ .term) target where
  termVar := fun
    | .here => replacement
    | .there index => substitution.termVar index
  typeVar := fun
    | .there index => substitution.typeVar index
  equalityVar := fun
    | .there index => substitution.equalityVar index
  inclusionVar := fun
    | .there index => substitution.inclusionVar index

/-- Eliminate the newest abstract type name. -/
def instantiateType {source target : Sig}
    (substitution : Subst source target) (replacement : Ty target) :
    Subst (source ▹ .type) target where
  termVar := fun
    | .there index => substitution.termVar index
  typeVar := fun
    | .here => replacement
    | .there index => substitution.typeVar index
  equalityVar := fun
    | .there index => substitution.equalityVar index
  inclusionVar := fun
    | .there index => substitution.inclusionVar index

/-- Eliminate the newest equality-evidence variable. -/
def instantiateEquality {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target) :
    Subst (source ▹ .evidence .equality) target where
  termVar := fun
    | .there index => substitution.termVar index
  typeVar := fun
    | .there index => substitution.typeVar index
  equalityVar := fun
    | .here => replacement
    | .there index => substitution.equalityVar index
  inclusionVar := fun
    | .there index => substitution.inclusionVar index

/-- Eliminate the newest directed-inclusion-evidence variable. -/
def instantiateInclusion {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target) :
    Subst (source ▹ .evidence .inclusion) target where
  termVar := fun
    | .there index => substitution.termVar index
  typeVar := fun
    | .there index => substitution.typeVar index
  equalityVar := fun
    | .there index => substitution.equalityVar index
  inclusionVar := fun
    | .here => replacement
    | .there index => substitution.inclusionVar index

/-- Eliminate all names using simultaneous type arguments. -/
def fromTypeArgs {source target : Sig} (base : Subst source target) :
    {names : Nat} → TypeArgs target names →
      Subst (TypeScope source names) target
  | 0, .nil => base
  | _ + 1, .snoc initial replacement =>
      (fromTypeArgs base initial).instantiateType replacement

/-- Eliminate a suffix of directed evidence binders. -/
def fromInclusionArgs {source target : Sig} (base : Subst source target) :
    {constraints : Nat} → LeArgs target constraints →
      Subst (Sig.extendN source (.evidence .inclusion) constraints) target
  | 0, .nil => base
  | _ + 1, .snoc initial replacement =>
      (fromInclusionArgs base initial).instantiateInclusion replacement

/-- Eliminate a complete names-first static scope. -/
def fromStaticArgs {source target : Sig} (base : Subst source target)
    {names constraints : Nat} (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst (StaticScope source names constraints) target :=
  fromInclusionArgs (fromTypeArgs base types) evidence

/-- Instantiate a complete static scope relative to an ambient renaming. -/
def ofStaticArgs {source target : Sig} (ambient : Rename source target)
    {names constraints : Nat} (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst (StaticScope source names constraints) target :=
  fromStaticArgs (ofRename ambient) types evidence

/-- Eliminate a static telescope and its separate payload binder. -/
def ofPayloadArgs {source target : Sig} (ambient : Rename source target)
    {names constraints : Nat} (types : TypeArgs target names)
    (evidence : LeArgs target constraints) (payload : Tm target) :
    Subst (PayloadScope source names constraints) target :=
  (ofStaticArgs ambient types evidence).instantiateTerm payload

/-- Eliminate the private name and equality witness introduced by
`newtype`. -/
def ofNewtype {source target : Sig} (ambient : Rename source target)
    (witness : Ty target) (equality : EqCo target) :
    Subst (NewtypeScope source) target :=
  ((ofRename ambient).instantiateType witness).instantiateEquality equality

end Subst

/-! ## Capture-avoiding action on every syntactic category -/

mutual

def Ty.substitute {source target : Sig} (type : Ty source)
    (substitution : Subst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .tvar name => substitution.typeVar name
  | .arr domain codomain =>
      .arr (domain.substitute substitution)
        (codomain.substitute substitution.liftTerm)
  | .existsT telescope payload =>
      .existsT (telescope.substitute substitution)
        (payload.substitute (substitution.liftStatic _ _))
  | .forallT telescope body =>
      .forallT (telescope.substitute substitution)
        (body.substitute (substitution.liftStatic _ _))
  | .recProj bodies index => .recProj (bodies.substitute substitution) index

def RecBodies.substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : Subst source target) : RecBodies target bound count :=
  match bodies with
  | .nil => .nil
  | .snoc initial body =>
      .snoc (initial.substitute substitution)
        (body.substitute (substitution.liftTypes bound))

def Proposition.substitute {source target : Sig}
    (proposition : Proposition source) (substitution : Subst source target) :
    Proposition target :=
  match proposition with
  | .inclusion lower upper =>
      .inclusion (lower.substitute substitution) (upper.substitute substitution)

def Telescope.substitute {source target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (substitution : Subst source target) :
    Telescope target names constraints :=
  match telescope with
  | .nil => .nil
  | .snoc initial proposition =>
      .snoc (initial.substitute substitution)
        (proposition.substitute (substitution.liftTypes names))

end

def TypeArgs.substitute {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count) (substitution : Subst source target) :
    TypeArgs target count :=
  match arguments with
  | .nil => .nil
  | .snoc initial type =>
      .snoc (initial.substitute substitution) (type.substitute substitution)

def EqCo.substitute {source target : Sig} (evidence : EqCo source)
    (substitution : Subst source target) : EqCo target :=
  match evidence with
  | .var index => substitution.equalityVar index
  | .refl type => .refl (type.substitute substitution)
  | .symm inner => .symm (inner.substitute substitution)
  | .trans first second =>
      .trans (first.substitute substitution) (second.substitute substitution)
  | .unfoldRec bodies index =>
      .unfoldRec (bodies.substitute substitution) index

mutual

def LeCo.substitute {source target : Sig} (evidence : LeCo source)
    (substitution : Subst source target) : LeCo target :=
  match evidence with
  | .var index => substitution.inclusionVar index
  | .refl type => .refl (type.substitute substitution)
  | .trans first second =>
      .trans (first.substitute substitution) (second.substitute substitution)
  | .top sourceType => .top (sourceType.substitute substitution)
  | .bot targetType => .bot (targetType.substitute substitution)
  | .eqToLe equality => .eqToLe (equality.substitute substitution)
  | .arr domain codomain =>
      .arr (domain.substitute substitution)
        (codomain.substitute substitution.liftTerm)
  | .existsT adaptation sourcePayload targetPayload payload =>
      .existsT (adaptation.substitute substitution)
        (sourcePayload.substitute (substitution.liftStatic _ _))
        (targetPayload.substitute (substitution.liftStatic _ _))
        (payload.substitute (substitution.liftStatic _ _))
  | .forallT adaptation sourceBody targetBody body =>
      .forallT (adaptation.substitute substitution)
        (sourceBody.substitute (substitution.liftStatic _ _))
        (targetBody.substitute (substitution.liftStatic _ _))
        (body.substitute (substitution.liftStatic _ _))

def LeArgs.substitute {source target : Sig} {count : Nat}
    (arguments : LeArgs source count) (substitution : Subst source target) :
    LeArgs target count :=
  match arguments with
  | .nil => .nil
  | .snoc initial evidence =>
      .snoc (initial.substitute substitution)
        (evidence.substitute substitution)

def TelMor.substitute {source target : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor source sourceNames sourceConstraints
      targetNames targetConstraints)
    (substitution : Subst source target) :
    TelMor target sourceNames sourceConstraints targetNames targetConstraints :=
  match morphism with
  | .refl telescope => .refl (telescope.substitute substitution)
  | .map sourceTelescope targetTelescope names evidence =>
      .map (sourceTelescope.substitute substitution)
        (targetTelescope.substitute substitution)
        (names.substitute
          (substitution.liftStatic sourceNames sourceConstraints))
        (evidence.substitute
          (substitution.liftStatic sourceNames sourceConstraints))
  | .trans first second =>
      .trans (first.substitute substitution) (second.substitute substitution)

end

def Tm.substitute {source target : Sig} (term : Tm source)
    (substitution : Subst source target) : Tm target :=
  match term with
  | .unit => .unit
  | .var index => substitution.termVar index
  | .lam domain body =>
      .lam (domain.substitute substitution)
        (body.substitute substitution.liftTerm)
  | .app function argument =>
      .app (function.substitute substitution) (argument.substitute substitution)
  | .let' rhs body =>
      .let' (rhs.substitute substitution)
        (body.substitute substitution.liftTerm)
  | .cast inner evidence =>
      .cast (inner.substitute substitution)
        (evidence.substitute substitution)
  | .pack telescope payloadType witnesses evidence payload =>
      .pack (telescope.substitute substitution)
        (payloadType.substitute (substitution.liftStatic _ _))
        (witnesses.substitute substitution)
        (evidence.substitute substitution)
        (payload.substitute substitution)
  | .open telescope payloadType scrutinee body =>
      .open (telescope.substitute substitution)
        (payloadType.substitute (substitution.liftStatic _ _))
        (scrutinee.substitute substitution)
        (body.substitute (substitution.liftPayload _ _))
  | .slam telescope body =>
      .slam (telescope.substitute substitution)
        (body.substitute (substitution.liftStatic _ _))
  | .sapp telescope function witnesses evidence =>
      .sapp (telescope.substitute substitution)
        (function.substitute substitution)
        (witnesses.substitute substitution)
        (evidence.substitute substitution)
  | .newtype witness body =>
      .newtype (witness.substitute substitution)
        (body.substitute substitution.liftNewtype)
  | .foldRec bodies index inner =>
      .foldRec (bodies.substitute substitution) index
        (inner.substitute substitution)
  | .unfoldRec bodies index inner =>
      .unfoldRec (bodies.substitute substitution) index
        (inner.substitute substitution)

/-! ## Operational instantiation forms -/

namespace Tm

/-- Ordinary term-variable opening. -/
def instantiateTerm {scope : Sig} (body : Tm (scope ▹ .term))
    (replacement : Tm scope) : Tm scope :=
  body.substitute (Subst.id.instantiateTerm replacement)

/-- Instantiate all names and constraint evidence of a static body. -/
def instantiateStatic {scope : Sig} {names constraints : Nat}
    (body : Tm (StaticScope scope names constraints))
    (types : TypeArgs scope names) (evidence : LeArgs scope constraints) :
    Tm scope :=
  body.substitute (Subst.fromStaticArgs Subst.id types evidence)

/-- Instantiate a package body, with its runtime payload kept separate from
the telescope's static entries. -/
def instantiatePayload {scope : Sig} {names constraints : Nat}
    (body : Tm (PayloadScope scope names constraints))
    (types : TypeArgs scope names) (evidence : LeArgs scope constraints)
    (payload : Tm scope) : Tm scope :=
  body.substitute
    ((Subst.fromStaticArgs Subst.id types evidence).instantiateTerm payload)

/-- Open a private name by replacing it with its witness and its equality
assumption with reflexivity at that witness. -/
def instantiateNewtype {scope : Sig} (body : Tm (NewtypeScope scope))
    (witness : Ty scope) : Tm scope :=
  body.substitute
    ((Subst.id.instantiateType witness).instantiateEquality (.refl witness))

end Tm

namespace LeCo

def instantiateStatic {scope : Sig} {names constraints : Nat}
    (evidence : LeCo (StaticScope scope names constraints))
    (types : TypeArgs scope names) (arguments : LeArgs scope constraints) :
    LeCo scope :=
  evidence.substitute (Subst.fromStaticArgs Subst.id types arguments)

end LeCo

/-! ## Applying telescope morphisms to realizations -/

/-- A concrete realization supplies one witness per abstract name and one
certificate per constraint. -/
structure Realization (scope : Sig) (names constraints : Nat) where
  types : TypeArgs scope names
  evidence : LeArgs scope constraints
deriving DecidableEq

namespace TelMor

/-- The syntactic source interface recorded by a morphism. -/
def sourceTelescope {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) :
    Telescope scope sourceNames sourceConstraints :=
  match morphism with
  | .refl telescope => telescope
  | .map source _ _ _ => source
  | .trans first _ => first.sourceTelescope

/-- The syntactic target interface recorded by a morphism. -/
def targetTelescope {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) :
    Telescope scope targetNames targetConstraints :=
  match morphism with
  | .refl telescope => telescope
  | .map _ target _ _ => target
  | .trans _ second => second.targetTelescope

/-- Execute the explicit fields of a telescope morphism.  This is purely
static: it builds target witnesses and evidence but contributes no runtime
computation. -/
def apply {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (source : Realization scope sourceNames sourceConstraints) :
    Realization scope targetNames targetConstraints :=
  match morphism with
  | .refl _ => source
  | .map _ _ names evidence =>
      let substitution :=
        Subst.fromStaticArgs Subst.id source.types source.evidence
      ⟨names.substitute substitution, evidence.substitute substitution⟩
  | .trans first second => second.apply (first.apply source)

/-- The abstract names and evidence assumptions of an opened source
telescope, in their own complete static scope. -/
def assumptions (scope : Sig) (names constraints : Nat) :
    Realization (StaticScope scope names constraints) names constraints :=
  ⟨TypeArgs.boundNames scope names constraints,
    LeArgs.selectAssumptions scope names constraints (fun index => index)⟩

/-- Reinterpret a target package body in the source package scope of an
existential coercion.  Target static variables are supplied by the
morphism; the target payload variable is supplied by coercing the source
payload with `payloadEvidence`. -/
def payloadSubstitution {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints)) :
    Subst (PayloadScope scope targetNames targetConstraints)
      (PayloadScope scope sourceNames sourceConstraints) :=
  let openedMorphism :=
    morphism.rename (Rename.weakenStatic sourceNames sourceConstraints)
  let targetRealization :=
    openedMorphism.apply (assumptions scope sourceNames sourceConstraints)
  let targetTypes := targetRealization.types.weaken (kind := .term)
  let targetEvidence := targetRealization.evidence.weaken (kind := .term)
  let ambient :=
    Subst.ofRename (Rename.weakenPayload sourceNames sourceConstraints)
  let staticSubstitution :=
    Subst.fromStaticArgs ambient targetTypes targetEvidence
  staticSubstitution.instantiateTerm
    (.cast (.var .here) payloadEvidence.weaken)

@[simp]
theorem apply_refl {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (realization : Realization scope names constraints) :
    (TelMor.refl telescope).apply realization = realization := rfl

@[simp]
theorem apply_trans {scope : Sig}
    {firstNames firstConstraints middleNames middleConstraints
      lastNames lastConstraints : Nat}
    (first : TelMor scope firstNames firstConstraints
      middleNames middleConstraints)
    (second : TelMor scope middleNames middleConstraints
      lastNames lastConstraints)
    (realization : Realization scope firstNames firstConstraints) :
    (TelMor.trans first second).apply realization =
      second.apply (first.apply realization) := rfl

end TelMor

end FCsub
