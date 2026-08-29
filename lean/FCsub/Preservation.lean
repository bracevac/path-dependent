import FCsub.Dynamics
import FCsub.SubstitutionMetatheory

/-!
# Preservation for annotated FCsub

The main theorem is stated through `Nonempty` because reduction is a
Prop-valued relation while the structural typing judgment is proof-relevant
and Type-valued.  This is the strongest ordinary preservation proposition
without changing either kernel judgment.
-/

namespace FCsub

namespace Tm.Step

/-! ## Ordinary binder instantiation -/

private def instantiateTermSquare {scope : Sig} (replacement : Tm scope) :
    PartialTypeRename.SubstSquare
      (PartialTypeRename.dropTerm (scope := scope))
      (Subst.id.instantiateTerm replacement) Subst.id
      PartialTypeRename.id where
  typeVar := fun name => by
    cases name with
    | there name => rfl

private theorem strengthenTerm_eq_instantiate {scope : Sig}
    (type : Ty (scope ▹ .term)) (replacement : Tm scope) :
    type.strengthenTerm =
      some (type.substitute (Subst.id.instantiateTerm replacement)) := by
  have natural := Ty.rename?_substitute_square type
    (PartialTypeRename.dropTerm (scope := scope))
    (Subst.id.instantiateTerm replacement) Subst.id
    PartialTypeRename.id (instantiateTermSquare replacement)
  change type.rename? PartialTypeRename.dropTerm = some _
  cases equation : type.rename? PartialTypeRename.dropTerm with
  | none => simp [equation] at natural
  | some result =>
      simp only [equation, Option.map_some, Ty.substitute_id,
        Ty.rename?_id] at natural
      exact natural

private theorem substitute_instantiateTerm_eq_of_strengthen {scope : Sig}
    {type : Ty (scope ▹ .term)} {result : Ty scope}
    (replacement : Tm scope)
    (nonescape : type.strengthenTerm = some result) :
    type.substitute (Subst.id.instantiateTerm replacement) = result := by
  have natural := Ty.rename?_substitute_square type
    (PartialTypeRename.dropTerm (scope := scope))
    (Subst.id.instantiateTerm replacement) Subst.id
    PartialTypeRename.id (instantiateTermSquare replacement)
  change type.rename? PartialTypeRename.dropTerm = some result at nonescape
  rw [nonescape] at natural
  apply Option.some.inj
  simpa only [Option.map_some, Ty.substitute_id, Ty.rename?_id,
    Option.bind_some] using natural.symm

/-! A successful partial closing observes only variables on which the
operational substitution agrees with that closing.  This local relation is
used for the generative-name redex, where the operational substitution also
has an irrelevant fallback for the rejected fresh name. -/

private structure PartialCompatible {source target : Sig}
    (removal : PartialTypeRename source target)
    (substitution : Subst source target) : Prop where
  typeVar : ∀ name targetName,
    removal.typeVar name = some targetName →
      substitution.typeVar name = .tvar targetName

namespace PartialCompatible

private def liftTerm {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution) :
    PartialCompatible removal.liftTerm substitution.liftTerm where
  typeVar := fun name targetName equation => by
    cases name with
    | there name =>
        cases targetName with
        | there targetName =>
            have base : removal.typeVar name = some targetName := by
              simpa [PartialTypeRename.liftTerm] using equation
            simp [Subst.liftTerm, compatible.typeVar name targetName base,
              Ty.weaken, Ty.rename]

private def liftType {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution) :
    PartialCompatible removal.liftType substitution.liftType where
  typeVar := fun name targetName equation => by
    cases name with
    | here =>
        cases targetName with
        | here => rfl
        | there targetName =>
            simp [PartialTypeRename.liftType] at equation
    | there name =>
        cases targetName with
        | here => simp [PartialTypeRename.liftType] at equation
        | there targetName =>
            have base : removal.typeVar name = some targetName := by
              simpa [PartialTypeRename.liftType] using equation
            simp [Subst.liftType, compatible.typeVar name targetName base,
              Ty.weaken, Ty.rename]

private def liftEvidence {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution)
    (relation : Relation) :
    PartialCompatible (removal.liftEvidence relation)
      (substitution.lift (.evidence relation)) where
  typeVar := fun name targetName equation => by
    cases name with
    | there name =>
        cases targetName with
        | there targetName =>
            have base : removal.typeVar name = some targetName := by
              simpa [PartialTypeRename.liftEvidence] using equation
            cases relation <;>
              simp [Subst.lift, Subst.liftEquality,
                Subst.liftInclusion,
                compatible.typeVar name targetName base,
                Ty.weaken, Ty.rename]

private def lift {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution)
    (kind : BinderKind) :
    PartialCompatible (removal.lift kind) (substitution.lift kind) :=
  match kind with
  | .term => compatible.liftTerm
  | .type => compatible.liftType
  | .evidence relation => compatible.liftEvidence relation

private def liftN {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution)
    (kind : BinderKind) : (count : Nat) →
    PartialCompatible (removal.liftN kind count)
      (substitution.liftN kind count)
  | 0 => compatible
  | count + 1 => (liftN compatible kind count).lift kind

private def liftTypes {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution) (names : Nat) :
    PartialCompatible (removal.liftTypes names)
      (substitution.liftTypes names) :=
  compatible.liftN .type names

private def liftStatic {source target : Sig}
    {removal : PartialTypeRename source target}
    {substitution : Subst source target}
    (compatible : PartialCompatible removal substitution)
    (names constraints : Nat) :
    PartialCompatible (removal.liftStatic names constraints)
      (substitution.liftStatic names constraints) :=
  (compatible.liftTypes names).liftN (.evidence .inclusion) constraints

end PartialCompatible

mutual

private def Ty.substitute_eq_of_partial_success {source target : Sig}
    (type : Ty source) (removal : PartialTypeRename source target)
    (substitution : Subst source target)
    (compatible : PartialCompatible removal substitution)
    {result : Ty target} (success : type.rename? removal = some result) :
    type.substitute substitution = result :=
  match type with
  | .top => Option.some.inj success
  | .bot => Option.some.inj success
  | .one => Option.some.inj success
  | .tvar name => by
      cases equation : removal.typeVar name with
      | none => simp [Ty.rename?, equation] at success
      | some targetName =>
          have resultEq : Ty.tvar targetName = result := by
            exact Option.some.inj (by simpa [Ty.rename?, equation] using success)
          exact (compatible.typeVar name targetName equation).trans resultEq
  | .arr domain codomain => by
      cases domainEq : domain.rename? removal with
      | none => simp [Ty.rename?, domainEq] at success
      | some domainResult =>
          cases codomainEq : codomain.rename? removal.liftTerm with
          | none => simp [Ty.rename?, domainEq, codomainEq] at success
          | some codomainResult =>
              have resultEq : Ty.arr domainResult codomainResult = result := by
                exact Option.some.inj (by
                  simpa [Ty.rename?, domainEq, codomainEq] using success)
              rw [← resultEq]
              simp only [Ty.substitute]
              rw [Ty.substitute_eq_of_partial_success domain removal
                substitution compatible domainEq]
              rw [Ty.substitute_eq_of_partial_success codomain
                removal.liftTerm substitution.liftTerm
                compatible.liftTerm codomainEq]
  | .existsT telescope payload => by
      cases telescopeEq : telescope.rename? removal with
      | none => simp [Ty.rename?, telescopeEq] at success
      | some telescopeResult =>
          cases payloadEq : payload.rename? (removal.liftStatic _ _) with
          | none => simp [Ty.rename?, telescopeEq, payloadEq] at success
          | some payloadResult =>
              have resultEq : Ty.existsT telescopeResult payloadResult =
                  result := by
                exact Option.some.inj (by
                  simpa [Ty.rename?, telescopeEq, payloadEq] using success)
              rw [← resultEq]
              simp only [Ty.substitute]
              rw [Telescope.substitute_eq_of_partial_success _ telescope
                removal substitution compatible telescopeEq]
              rw [Ty.substitute_eq_of_partial_success payload
                (removal.liftStatic _ _) (substitution.liftStatic _ _)
                (compatible.liftStatic _ _) payloadEq]
  | .forallT telescope body => by
      cases telescopeEq : telescope.rename? removal with
      | none => simp [Ty.rename?, telescopeEq] at success
      | some telescopeResult =>
          cases bodyEq : body.rename? (removal.liftStatic _ _) with
          | none => simp [Ty.rename?, telescopeEq, bodyEq] at success
          | some bodyResult =>
              have resultEq : Ty.forallT telescopeResult bodyResult =
                  result := by
                exact Option.some.inj (by
                  simpa [Ty.rename?, telescopeEq, bodyEq] using success)
              rw [← resultEq]
              simp only [Ty.substitute]
              rw [Telescope.substitute_eq_of_partial_success _ telescope
                removal substitution compatible telescopeEq]
              rw [Ty.substitute_eq_of_partial_success body
                (removal.liftStatic _ _) (substitution.liftStatic _ _)
                (compatible.liftStatic _ _) bodyEq]

private def Proposition.substitute_eq_of_partial_success
    {source target : Sig} (proposition : Proposition source)
    (removal : PartialTypeRename source target)
    (substitution : Subst source target)
    (compatible : PartialCompatible removal substitution)
    {result : Proposition target}
    (success : proposition.rename? removal = some result) :
    proposition.substitute substitution = result :=
  match proposition with
  | .inclusion lower upper => by
      cases lowerEq : lower.rename? removal with
      | none => simp [Proposition.rename?, lowerEq] at success
      | some lowerResult =>
          cases upperEq : upper.rename? removal with
          | none => simp [Proposition.rename?, lowerEq, upperEq] at success
          | some upperResult =>
              have resultEq : Proposition.inclusion lowerResult upperResult =
                  result := by
                exact Option.some.inj (by
                  simpa [Proposition.rename?, lowerEq, upperEq] using success)
              rw [← resultEq]
              simp only [Proposition.substitute]
              rw [Ty.substitute_eq_of_partial_success lower removal
                substitution compatible lowerEq]
              rw [Ty.substitute_eq_of_partial_success upper removal
                substitution compatible upperEq]

private def Telescope.substitute_eq_of_partial_success
    {source target : Sig} {names : Nat} (constraints : Nat)
    (telescope : Telescope source names constraints)
    (removal : PartialTypeRename source target)
    (substitution : Subst source target)
    (compatible : PartialCompatible removal substitution)
    {result : Telescope target names constraints}
    (success : telescope.rename? removal = some result) :
    telescope.substitute substitution = result :=
  match constraints, telescope with
  | 0, .nil => by
      exact Option.some.inj success
  | _ + 1, .snoc initial proposition => by
      cases initialEq : initial.rename? removal with
      | none => simp [Telescope.rename?, initialEq] at success
      | some initialResult =>
          cases propositionEq :
              proposition.rename? (removal.liftTypes names) with
          | none =>
              simp [Telescope.rename?, initialEq, propositionEq] at success
          | some propositionResult =>
              have resultEq : Telescope.snoc initialResult propositionResult =
                  result := by
                exact Option.some.inj (by
                  simpa [Telescope.rename?, initialEq, propositionEq] using
                    success)
              rw [← resultEq]
              simp only [Telescope.substitute]
              rw [Telescope.substitute_eq_of_partial_success _ initial
                removal substitution compatible initialEq]
              rw [Proposition.substitute_eq_of_partial_success proposition
                (removal.liftTypes names) (substitution.liftTypes names)
                (compatible.liftTypes names) propositionEq]

end

private def newtypeCompatible {scope : Sig} (witness : Ty scope) :
    PartialCompatible (PartialTypeRename.dropNewtype scope)
      ((Subst.id.instantiateType witness).instantiateEquality
        (.refl witness)) where
  typeVar := fun name targetName equation => by
    cases name with
    | there name =>
        cases name with
        | here =>
            simp [PartialTypeRename.dropNewtype,
              PartialTypeRename.comp, PartialTypeRename.dropEvidence,
              PartialTypeRename.dropType] at equation
        | there name =>
            have same : targetName = name := by
              simpa [PartialTypeRename.dropNewtype,
                PartialTypeRename.comp, PartialTypeRename.dropEvidence,
                PartialTypeRename.dropType] using
                (Option.some.inj equation).symm
            subst targetName
            rfl

private theorem substitute_instantiateNewtype_eq_of_strengthen
    {scope : Sig} {type : Ty (NewtypeScope scope)} {result : Ty scope}
    (witness : Ty scope)
    (nonescape : type.strengthenNewtype = some result) :
    type.substitute
        ((Subst.id.instantiateType witness).instantiateEquality
          (.refl witness)) = result := by
  apply Ty.substitute_eq_of_partial_success type
    (PartialTypeRename.dropNewtype scope)
    ((Subst.id.instantiateType witness).instantiateEquality (.refl witness))
    (newtypeCompatible witness)
  exact nonescape

private def typeArgsCompatible {scope : Sig} : {names : Nat} →
    (witnesses : TypeArgs scope names) →
    PartialCompatible (PartialTypeRename.dropTypes scope names)
      (Subst.fromTypeArgs Subst.id witnesses)
  | 0, .nil => by
      constructor
      intro name targetName equation
      simpa [PartialTypeRename.dropTypes, PartialTypeRename.id,
        Subst.fromTypeArgs, Subst.id] using Option.some.inj equation
  | _ + 1, .snoc initial witness => by
      constructor
      intro name targetName equation
      cases name with
      | here =>
          simp [PartialTypeRename.dropTypes, PartialTypeRename.comp,
            PartialTypeRename.dropType] at equation
      | there name =>
          have initialEquation :
              (PartialTypeRename.dropTypes scope _).typeVar name =
                some targetName := by
            simpa [PartialTypeRename.dropTypes, PartialTypeRename.comp,
              PartialTypeRename.dropType] using equation
          exact (typeArgsCompatible initial).typeVar name targetName
            initialEquation

private def staticArgsCompatible {scope : Sig} {names : Nat}
    (witnesses : TypeArgs scope names) : {constraints : Nat} →
    (evidence : LeArgs scope constraints) →
    PartialCompatible
      (PartialTypeRename.dropStatic scope names constraints)
      (Subst.fromStaticArgs Subst.id witnesses evidence)
  | 0, .nil => by
      constructor
      intro name targetName equation
      apply (typeArgsCompatible witnesses).typeVar name targetName
      simpa [PartialTypeRename.dropStatic,
        PartialTypeRename.dropEvidenceN, PartialTypeRename.comp,
        PartialTypeRename.id] using equation
  | _ + 1, .snoc initial certificate => by
      constructor
      intro name targetName equation
      cases name with
      | there name =>
          have initialEquation :
              (PartialTypeRename.dropStatic scope names _).typeVar name =
                some targetName := by
            simpa [PartialTypeRename.dropStatic,
              PartialTypeRename.dropEvidenceN,
              PartialTypeRename.dropEvidence, PartialTypeRename.comp] using
                equation
          exact (staticArgsCompatible witnesses initial).typeVar name
            targetName initialEquation

private def payloadCompatible {scope : Sig} {names constraints : Nat}
    (witnesses : TypeArgs scope names) (evidence : LeArgs scope constraints)
    (payload : Tm scope) :
    PartialCompatible
      (PartialTypeRename.dropPayload scope names constraints)
      ((Subst.fromStaticArgs Subst.id witnesses evidence).instantiateTerm
        payload) where
  typeVar := fun name targetName equation => by
    cases name with
    | there name =>
        have staticEquation :
            (PartialTypeRename.dropStatic scope names constraints).typeVar
                name = some targetName := by
          simpa [PartialTypeRename.dropPayload,
            PartialTypeRename.dropTerm, PartialTypeRename.comp] using equation
        exact (staticArgsCompatible witnesses evidence).typeVar name
          targetName staticEquation

private theorem substitute_instantiatePayload_eq_of_strengthen
    {scope : Sig} {names constraints : Nat}
    {type : Ty (PayloadScope scope names constraints)} {result : Ty scope}
    (witnesses : TypeArgs scope names) (evidence : LeArgs scope constraints)
    (payload : Tm scope)
    (nonescape : type.strengthenPayload = some result) :
    type.substitute
        ((Subst.fromStaticArgs Subst.id witnesses evidence).instantiateTerm
          payload) = result := by
  apply Ty.substitute_eq_of_partial_success type
    (PartialTypeRename.dropPayload scope names constraints)
    ((Subst.fromStaticArgs Subst.id witnesses evidence).instantiateTerm
      payload)
    (payloadCompatible witnesses evidence payload)
  exact nonescape

/-! ## Payload-interface closing -/

private theorem dropTypes_weakenTypes {scope : Sig} (names : Nat)
    (name : BVar scope .type) :
    (PartialTypeRename.dropTypes scope names).typeVar
        ((Rename.weakenTypes names).var name) = some name := by
  induction names with
  | zero => rfl
  | succ names induction =>
      simpa [PartialTypeRename.dropTypes, PartialTypeRename.comp,
        PartialTypeRename.dropType, Rename.weakenTypes, Rename.weakenN]
        using induction

private theorem dropTypes_eq_some {scope : Sig} {names : Nat}
    (name : BVar (TypeScope scope names) .type)
    (ambient : BVar scope .type)
    (equation : (PartialTypeRename.dropTypes scope names).typeVar name =
      some ambient) :
    name = (Rename.weakenTypes names).var ambient := by
  induction names with
  | zero =>
      simpa [PartialTypeRename.dropTypes, PartialTypeRename.id,
        Rename.weakenTypes, Rename.weakenN] using Option.some.inj equation
  | succ names induction =>
      cases name with
      | here =>
          simp [PartialTypeRename.dropTypes, PartialTypeRename.comp,
            PartialTypeRename.dropType] at equation
      | there name =>
          have smaller :
              (PartialTypeRename.dropTypes scope names).typeVar name =
                some ambient := by
            simpa [PartialTypeRename.dropTypes, PartialTypeRename.comp,
              PartialTypeRename.dropType] using equation
          have identity := induction name smaller
          simpa [Rename.weakenTypes, Rename.weakenN] using
            congrArg (fun index =>
              BVar.there (newest := .type) index) identity

private theorem dropStatic_weakenStatic {scope : Sig} (names constraints : Nat)
    (name : BVar scope .type) :
    (PartialTypeRename.dropStatic scope names constraints).typeVar
        ((Rename.weakenStatic names constraints).var name) = some name := by
  induction constraints with
  | zero =>
      simpa [PartialTypeRename.dropStatic,
        PartialTypeRename.dropEvidenceN, PartialTypeRename.comp,
        PartialTypeRename.id, Rename.weakenStatic, Rename.weakenN] using
          dropTypes_weakenTypes names name
  | succ constraints induction =>
      simpa [PartialTypeRename.dropStatic,
        PartialTypeRename.dropEvidenceN, PartialTypeRename.dropEvidence,
        PartialTypeRename.comp, Rename.weakenStatic, Rename.weakenN] using
          induction

private theorem dropStatic_eq_some {scope : Sig} {names constraints : Nat}
    (name : BVar (StaticScope scope names constraints) .type)
    (ambient : BVar scope .type)
    (equation :
      (PartialTypeRename.dropStatic scope names constraints).typeVar name =
        some ambient) :
    name = (Rename.weakenStatic names constraints).var ambient := by
  induction constraints with
  | zero =>
      have base :
          (PartialTypeRename.dropTypes scope names).typeVar name =
            some ambient := by
        simpa [PartialTypeRename.dropStatic,
          PartialTypeRename.dropEvidenceN, PartialTypeRename.comp,
          PartialTypeRename.id] using equation
      simpa [Rename.weakenStatic, Rename.weakenN] using
        dropTypes_eq_some name ambient base
  | succ constraints induction =>
      cases name with
      | there name =>
          have smaller :
              (PartialTypeRename.dropStatic scope names constraints).typeVar
                  name = some ambient := by
            simpa [PartialTypeRename.dropStatic,
              PartialTypeRename.dropEvidenceN,
              PartialTypeRename.dropEvidence,
              PartialTypeRename.comp] using equation
          have identity := induction name smaller
          simpa [Rename.weakenStatic, Rename.weakenN] using
            congrArg (fun index =>
              BVar.there (newest := .evidence .inclusion) index) identity

private theorem dropPayload_weakenPayload {scope : Sig}
    (names constraints : Nat) (name : BVar scope .type) :
    (PartialTypeRename.dropPayload scope names constraints).typeVar
        ((Rename.weakenPayload names constraints).var name) = some name := by
  simpa [PartialTypeRename.dropPayload, PartialTypeRename.dropTerm,
    PartialTypeRename.comp, Rename.weakenPayload] using
      dropStatic_weakenStatic names constraints name

private theorem dropPayload_eq_some {scope : Sig} {names constraints : Nat}
    (name : BVar (PayloadScope scope names constraints) .type)
    (ambient : BVar scope .type)
    (equation :
      (PartialTypeRename.dropPayload scope names constraints).typeVar name =
        some ambient) :
    name = (Rename.weakenPayload names constraints).var ambient := by
  cases name with
  | there name =>
      have static :
          (PartialTypeRename.dropStatic scope names constraints).typeVar name =
            some ambient := by
        simpa [PartialTypeRename.dropPayload,
          PartialTypeRename.dropTerm, PartialTypeRename.comp] using equation
      simpa [Rename.weakenPayload] using
        congrArg (fun index => BVar.there (newest := .term) index)
          (dropStatic_eq_some name ambient static)

private def retargetPayloadPartial (scope : Sig)
    (targetNames targetConstraints sourceNames sourceConstraints : Nat) :
    PartialTypeRename
      (PayloadScope scope targetNames targetConstraints)
      (PayloadScope scope sourceNames sourceConstraints) where
  typeVar := fun name =>
    (PartialTypeRename.dropPayload scope targetNames targetConstraints).typeVar
      name |>.map
        (Rename.weakenPayload sourceNames sourceConstraints).var

private def retargetPayloadSquare (scope : Sig)
    (targetNames targetConstraints sourceNames sourceConstraints : Nat) :
    PartialTypeRename.Square
      (PartialTypeRename.dropPayload scope targetNames targetConstraints)
      Rename.id
      (Rename.weakenPayload sourceNames sourceConstraints)
      (retargetPayloadPartial scope targetNames targetConstraints
        sourceNames sourceConstraints) where
  typeVar := fun _ => rfl

private def payloadSectionSquare (scope : Sig) (names constraints : Nat) :
    PartialTypeRename.Square PartialTypeRename.id
      (Rename.weakenPayload names constraints) Rename.id
      (PartialTypeRename.dropPayload scope names constraints) where
  typeVar := fun name => by
    simpa [PartialTypeRename.id] using
      (dropPayload_weakenPayload names constraints name).symm

private theorem retargetPayload_success {scope : Sig}
    {targetNames targetConstraints sourceNames sourceConstraints : Nat}
    {type : Ty (PayloadScope scope targetNames targetConstraints)}
    {result : Ty scope}
    (nonescape : type.strengthenPayload = some result) :
    type.rename?
        (retargetPayloadPartial scope targetNames targetConstraints
          sourceNames sourceConstraints) =
      some (result.rename
        (Rename.weakenPayload sourceNames sourceConstraints)) := by
  have natural := Ty.rename?_square type
    (PartialTypeRename.dropPayload scope targetNames targetConstraints)
    Rename.id (Rename.weakenPayload sourceNames sourceConstraints)
    (retargetPayloadPartial scope targetNames targetConstraints
      sourceNames sourceConstraints)
    (retargetPayloadSquare scope targetNames targetConstraints
      sourceNames sourceConstraints)
  change type.rename?
      (PartialTypeRename.dropPayload scope targetNames targetConstraints) =
        some result at nonescape
  rw [nonescape] at natural
  simpa only [Option.map_some, Ty.rename_id] using natural.symm

private theorem payloadSubstitution_typeVar_weakenPayload
    {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints))
    (name : BVar scope .type) :
    (morphism.payloadSubstitution payloadEvidence).typeVar
        ((Rename.weakenPayload targetNames targetConstraints).var name) =
      .tvar ((Rename.weakenPayload sourceNames sourceConstraints).var name) := by
  unfold TelMor.payloadSubstitution
  dsimp only
  let openedMorphism :=
    morphism.rename (Rename.weakenStatic sourceNames sourceConstraints)
  let targetRealization :=
    openedMorphism.apply
      (TelMor.assumptions scope sourceNames sourceConstraints)
  have natural := Ty.substitute_weakenStatic_fromStaticArgs (.tvar name)
    (Subst.ofRename (Rename.weakenPayload sourceNames sourceConstraints))
    targetRealization.types.weaken targetRealization.evidence.weaken
  simpa only [openedMorphism, targetRealization, Rename.weakenPayload,
    Rename.comp_var, Subst.instantiateTerm, Ty.rename, Ty.substitute,
    Subst.ofRename] using natural

private def payloadMorphismCompatible {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints)) :
    PartialCompatible
      (retargetPayloadPartial scope targetNames targetConstraints
        sourceNames sourceConstraints)
      (morphism.payloadSubstitution payloadEvidence) where
  typeVar := fun name targetName equation => by
    cases dropped : ((PartialTypeRename.dropPayload scope targetNames
        targetConstraints).typeVar name) with
    | none =>
        simp [retargetPayloadPartial, dropped] at equation
    | some ambient =>
        have targetEquation :
            (Rename.weakenPayload sourceNames sourceConstraints).var ambient =
              targetName := by
          exact Option.some.inj (by
            simpa [retargetPayloadPartial, dropped] using equation)
        subst targetName
        have nameEquation := dropPayload_eq_some name ambient dropped
        subst name
        exact payloadSubstitution_typeVar_weakenPayload morphism
          payloadEvidence ambient

private theorem strengthenPayload_payloadSubstitution {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints))
    {type : Ty (PayloadScope scope targetNames targetConstraints)}
    {result : Ty scope}
    (nonescape : type.strengthenPayload = some result) :
    Ty.strengthenPayload
        (type.substitute (morphism.payloadSubstitution payloadEvidence)) =
      some result := by
  have success := retargetPayload_success
    (sourceNames := sourceNames) (sourceConstraints := sourceConstraints)
    nonescape
  have substituted := Ty.substitute_eq_of_partial_success type
    (retargetPayloadPartial scope targetNames targetConstraints
      sourceNames sourceConstraints)
    (morphism.payloadSubstitution payloadEvidence)
    (payloadMorphismCompatible morphism payloadEvidence) success
  rw [substituted]
  change (result.rename
      (Rename.weakenPayload sourceNames sourceConstraints)).rename?
        (PartialTypeRename.dropPayload scope sourceNames sourceConstraints) =
      some result
  have sectionNatural := Ty.rename?_square result PartialTypeRename.id
    (Rename.weakenPayload sourceNames sourceConstraints) Rename.id
    (PartialTypeRename.dropPayload scope sourceNames sourceConstraints)
    (payloadSectionSquare scope sourceNames sourceConstraints)
  simpa only [Ty.rename?_id, Option.map_some, Ty.rename_id] using
    sectionNatural.symm

/-! ## Certificate-normalization cases -/

private theorem preserveCastRefl {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type result : Ty scope}
    (typing : Tm.HasType context (.cast term (.refl type)) result) :
    Nonempty (Tm.HasType context term result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping
      exact ⟨termTyping⟩

private theorem preserveCastTrans {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {first second : LeCo scope} {result : Ty scope}
    (typing : Tm.HasType context (.cast term (.trans first second)) result) :
    Nonempty
      (Tm.HasType context (.cast (.cast term first) second) result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | trans firstTyping secondTyping =>
          exact ⟨.cast (.cast termTyping firstTyping) secondTyping⟩

private theorem preserveCastEqRefl {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type result : Ty scope}
    (typing : Tm.HasType context
      (.cast term (.eqToLe (.refl type))) result) :
    Nonempty (Tm.HasType context term result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | eqToLe equalityTyping =>
          cases equalityTyping
          exact ⟨termTyping⟩

private theorem preserveCastEqSymmRefl {scope : Sig}
    {context : Ctx scope} {term : Tm scope} {type result : Ty scope}
    (typing : Tm.HasType context
      (.cast term (.eqToLe (.symm (.refl type)))) result) :
    Nonempty (Tm.HasType context term result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | eqToLe equalityTyping =>
          cases equalityTyping with
          | symm innerTyping =>
              cases innerTyping
              exact ⟨termTyping⟩

private theorem preserveCastEqSymmSymm {scope : Sig}
    {context : Ctx scope} {term : Tm scope} {evidence : EqCo scope}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.cast term (.eqToLe (.symm (.symm evidence)))) result) :
    Nonempty (Tm.HasType context (.cast term (.eqToLe evidence)) result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | eqToLe equalityTyping =>
          cases equalityTyping with
          | symm innerTyping =>
              cases innerTyping with
              | symm baseTyping =>
                  exact ⟨.cast termTyping (.eqToLe baseTyping)⟩

private theorem preserveCastEqSymmTrans {scope : Sig}
    {context : Ctx scope} {term : Tm scope} {first second : EqCo scope}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.cast term (.eqToLe (.symm (.trans first second)))) result) :
    Nonempty (Tm.HasType context
      (.cast term
        (.trans (.eqToLe (.symm second)) (.eqToLe (.symm first)))) result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | eqToLe equalityTyping =>
          cases equalityTyping with
          | symm innerTyping =>
              cases innerTyping with
              | trans firstTyping secondTyping =>
                  exact ⟨.cast termTyping
                    (.trans (.eqToLe (.symm secondTyping))
                      (.eqToLe (.symm firstTyping)))⟩

private theorem preserveCastEqTrans {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {first second : EqCo scope} {result : Ty scope}
    (typing : Tm.HasType context
      (.cast term (.eqToLe (.trans first second))) result) :
    Nonempty (Tm.HasType context
      (.cast term (.trans (.eqToLe first) (.eqToLe second))) result) := by
  cases typing with
  | cast termTyping evidenceTyping =>
      cases evidenceTyping with
      | eqToLe equalityTyping =>
          cases equalityTyping with
          | trans firstTyping secondTyping =>
              exact ⟨.cast termTyping
                (.trans (.eqToLe firstTyping) (.eqToLe secondTyping))⟩

/-! ## Computational ordinary-binder cases -/

private theorem preserveBeta {scope : Sig} {context : Ctx scope}
    {domain : Ty scope} {body : Tm (scope ▹ .term)}
    {argument : Tm scope} {result : Ty scope}
    (typing : Tm.HasType context (.app (.lam domain body) argument) result) :
    Nonempty (Tm.HasType context (body.instantiateTerm argument) result) := by
  cases typing with
  | app functionTyping argumentTyping nonescape =>
      cases functionTyping with
      | lam bodyTyping =>
          have argumentTypingId : Tm.HasType context argument
              (domain.substitute Subst.id) := by
            simpa only [Ty.substitute_id] using argumentTyping
          let contexts := (Ctx.Substitutes.id context).instantiateTerm
            domain argument argumentTypingId
          have instantiated := bodyTyping.substitute contexts
          have endpoint := substitute_instantiateTerm_eq_of_strengthen
            argument nonescape
          exact ⟨by
            simpa only [Tm.instantiateTerm, endpoint] using instantiated⟩

private theorem preserveZeta {scope : Sig} {context : Ctx scope}
    {rhs : Tm scope} {body : Tm (scope ▹ .term)} {result : Ty scope}
    (typing : Tm.HasType context (.let' rhs body) result) :
    Nonempty (Tm.HasType context (body.instantiateTerm rhs) result) := by
  cases typing with
  | @let' _ _ _ _ bound _ _ rhsTyping bodyTyping nonescape =>
      have rhsTypingId : Tm.HasType context rhs
          (bound.substitute Subst.id) := by
        simpa only [Ty.substitute_id] using rhsTyping
      let contexts := (Ctx.Substitutes.id context).instantiateTerm
        bound rhs rhsTypingId
      have instantiated := bodyTyping.substitute contexts
      have endpoint := substitute_instantiateTerm_eq_of_strengthen
        rhs nonescape
      exact ⟨by
        simpa only [Tm.instantiateTerm, endpoint] using instantiated⟩

private theorem preserveAppCastArrow {scope : Sig}
    {context : Ctx scope} {function argument : Tm scope}
    {domain : LeCo scope} {codomain : LeCo (scope ▹ .term)}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.app (.cast function (.arr domain codomain)) argument) result) :
    Nonempty (Tm.HasType context
      (.cast (.app function (.cast argument domain))
        (codomain.substitute (Subst.id.instantiateTerm argument))) result) := by
  cases typing with
  | app functionTyping argumentTyping nonescape =>
      cases functionTyping with
      | cast innerTyping evidenceTyping =>
          cases evidenceTyping with
          | @arr _ _ _ _ _ _ sourceCodomain targetCodomain
              domainTyping codomainTyping =>
              have castArgumentTyping :=
                Tm.HasType.cast argumentTyping domainTyping
              have sourceNonescape := strengthenTerm_eq_instantiate
                sourceCodomain argument
              have innerAppTyping := Tm.HasType.app innerTyping
                castArgumentTyping sourceNonescape
              let contexts := (Ctx.Substitutes.id context).instantiateTerm
                _ argument (by
                  simpa only [Ty.substitute_id] using argumentTyping)
              have instantiatedEvidence := codomainTyping.substitute contexts
              have casted := Tm.HasType.cast innerAppTyping
                instantiatedEvidence
              have endpoint := substitute_instantiateTerm_eq_of_strengthen
                argument nonescape
              rw [endpoint] at casted
              exact ⟨casted⟩

private theorem preserveSappSlam {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {body : Tm (StaticScope scope names constraints)}
    {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.sapp telescope (.slam telescope body) witnesses evidence) result) :
    Nonempty
      (Tm.HasType context (body.instantiateStatic witnesses evidence) result) := by
  cases typing with
  | sapp functionTyping argumentsTyping =>
      cases functionTyping with
      | slam bodyValue bodyTyping =>
          have argumentsTypingId : LeArgs.HasType context
              (telescope.substitute Subst.id) witnesses evidence := by
            simpa only [Telescope.substitute_id] using argumentsTyping
          let contexts := argumentsTypingId.substitutesTelescope telescope
            (Ctx.Substitutes.id context)
          have instantiated := bodyTyping.substitute contexts
          rw [← Ty.instantiateStatic_as_substitute] at instantiated
          exact ⟨instantiated⟩

private theorem preserveSappCastForall {scope : Sig}
    {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {adaptation : TelMor scope targetNames targetConstraints
      sourceNames sourceConstraints}
    {sourceBody : Ty (StaticScope scope sourceNames sourceConstraints)}
    {targetBody : Ty (StaticScope scope targetNames targetConstraints)}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    {bodyEvidence : LeCo
      (StaticScope scope targetNames targetConstraints)}
    {function : Tm scope} {witnesses : TypeArgs scope targetNames}
    {evidence : LeArgs scope targetConstraints} {result : Ty scope}
    (typing : Tm.HasType context
      (.sapp targetTelescope
        (.cast function
          (.forallT adaptation sourceBody targetBody bodyEvidence))
        witnesses evidence) result) :
    Nonempty (Tm.HasType context
      (.cast
        (.sapp adaptation.targetTelescope function
          (adaptation.apply ⟨witnesses, evidence⟩).types
          (adaptation.apply ⟨witnesses, evidence⟩).evidence)
        (bodyEvidence.instantiateStatic witnesses evidence)) result) := by
  cases typing with
  | sapp functionTyping argumentsTyping =>
      cases functionTyping with
      | cast innerTyping evidenceTyping =>
          cases evidenceTyping with
          | forallT adaptationTyping bodyTyping =>
              let targetRealization :
                  Realization scope targetNames targetConstraints :=
                ⟨witnesses, evidence⟩
              have sourceArgumentsTyping :=
                adaptationTyping.applyRealization targetRealization
                  argumentsTyping
              have sourceArgumentsTyping' : LeArgs.HasType context
                  adaptation.targetTelescope
                  (adaptation.apply targetRealization).types
                  (adaptation.apply targetRealization).evidence := by
                simpa only [adaptationTyping.targetTelescope_eq] using
                  sourceArgumentsTyping
              have innerTyping' : Tm.HasType context function
                  (.forallT adaptation.targetTelescope sourceBody) := by
                simpa only [adaptationTyping.targetTelescope_eq] using
                  innerTyping
              have sourceApplication := Tm.HasType.sapp innerTyping'
                sourceArgumentsTyping'
              have argumentsTypingId : LeArgs.HasType context
                  (targetTelescope.substitute Subst.id) witnesses evidence := by
                simpa only [Telescope.substitute_id] using argumentsTyping
              let contexts := argumentsTypingId.substitutesTelescope
                targetTelescope (Ctx.Substitutes.id context)
              have instantiatedEvidence := bodyTyping.substitute contexts
              have instantiatedEvidence' : LeCo.HasType context
                  (bodyEvidence.instantiateStatic witnesses evidence)
                  ((adaptation.pull sourceBody).instantiateStatic witnesses)
                  (targetBody.instantiateStatic witnesses) := by
                rw [Ty.instantiateStatic_as_substitute
                    (adaptation.pull sourceBody) witnesses evidence,
                  Ty.instantiateStatic_as_substitute targetBody witnesses
                    evidence]
                simpa only [LeCo.instantiateStatic] using
                  instantiatedEvidence
              rw [TelMor.pull_instantiateStatic_apply adaptation sourceBody
                targetRealization] at instantiatedEvidence'
              exact ⟨.cast sourceApplication instantiatedEvidence'⟩

private theorem preserveOpenPack {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {payloadType : Ty (StaticScope scope names constraints)}
    {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
    {payload : Tm scope} {body : Tm (PayloadScope scope names constraints)}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.open telescope payloadType
        (.pack telescope payloadType witnesses evidence payload) body)
      result) :
    Nonempty (Tm.HasType context
      (body.instantiatePayload witnesses evidence payload) result) := by
  cases typing with
  | openT packageTyping bodyTyping nonescape =>
      cases packageTyping with
      | pack argumentsTyping payloadTyping =>
          have argumentsTypingId : LeArgs.HasType context
              (telescope.substitute Subst.id) witnesses evidence := by
            simpa only [Telescope.substitute_id] using argumentsTyping
          let staticContexts := argumentsTypingId.substitutesTelescope
            telescope (Ctx.Substitutes.id context)
          have payloadTypingSubstituted : Tm.HasType context payload
              (payloadType.substitute
                (Subst.fromStaticArgs Subst.id witnesses evidence)) := by
            rw [← Ty.instantiateStatic_as_substitute payloadType witnesses
              evidence]
            exact payloadTyping
          let payloadContexts := staticContexts.instantiateTerm payloadType
            payload payloadTypingSubstituted
          have instantiated := bodyTyping.substitute payloadContexts
          have endpoint := substitute_instantiatePayload_eq_of_strengthen
            witnesses evidence payload nonescape
          exact ⟨by
            simpa only [Tm.instantiatePayload, endpoint] using instantiated⟩

private theorem preserveOpenCastExists {scope : Sig}
    {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {adaptation : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {sourcePayload : Ty
      (StaticScope scope sourceNames sourceConstraints)}
    {targetPayload : Ty
      (StaticScope scope targetNames targetConstraints)}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    {payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints)}
    {package : Tm scope}
    {body : Tm (PayloadScope scope targetNames targetConstraints)}
    {result : Ty scope}
    (typing : Tm.HasType context
      (.open targetTelescope targetPayload
        (.cast package
          (.existsT adaptation sourcePayload targetPayload payloadEvidence))
        body) result) :
    Nonempty (Tm.HasType context
      (.open adaptation.sourceTelescope sourcePayload package
        (body.substitute
          (adaptation.payloadSubstitution payloadEvidence))) result) := by
  cases typing with
  | openT packageTyping bodyTyping nonescape =>
      cases packageTyping with
      | cast innerTyping evidenceTyping =>
          cases evidenceTyping with
          | existsT adaptationTyping payloadTyping =>
              let contexts := adaptationTyping.payloadSubstitution
                payloadTyping
              have substitutedBody := bodyTyping.substitute contexts
              have substitutedNonescape :=
                strengthenPayload_payloadSubstitution adaptation
                  payloadEvidence nonescape
              rw [adaptationTyping.sourceTelescope_eq]
              exact ⟨.openT innerTyping substitutedBody
                substitutedNonescape⟩

private theorem preserveNewtype {scope : Sig} {context : Ctx scope}
    {witness : Ty scope} {body : Tm (NewtypeScope scope)}
    {result : Ty scope}
    (typing : Tm.HasType context (.newtype witness body) result) :
    Nonempty
      (Tm.HasType context (body.instantiateNewtype witness) result) := by
  cases typing with
  | newtype bodyTyping nonescape =>
      let name : Ty (scope ▹ .type) := .tvar .here
      let weakenedWitness : Ty (scope ▹ .type) := witness.weaken
      let typeContexts :=
        (Ctx.Substitutes.id context).instantiateType witness
      have equalityTyping : EqCo.HasType context (.refl witness)
          (name.substitute (Subst.id.instantiateType witness))
          (weakenedWitness.substitute
            (Subst.id.instantiateType witness)) := by
        change EqCo.HasType context (.refl witness) witness
          (witness.weaken.substitute
            (Subst.id.instantiateType witness))
        rw [Ty.substitute_weaken_instantiateType witness Subst.id witness,
          Ty.substitute_id]
        exact EqCo.HasType.refl witness
      let contexts := typeContexts.instantiateEquality name weakenedWitness
        (.refl witness) equalityTyping
      have instantiated := bodyTyping.substitute contexts
      have endpoint := substitute_instantiateNewtype_eq_of_strengthen
        witness nonescape
      rw [endpoint] at instantiated
      exact ⟨instantiated⟩

/-! ## Preservation -/

/-- Every annotated reduction step preserves its structural FCsub type.
`Nonempty` is necessary because `Step` is Prop-valued while `HasType` is
proof-relevant and Type-valued. -/
theorem preservation {scope : Sig} {context : Ctx scope}
    {term next : Tm scope} {type : Ty scope}
    (step : Tm.Step term next) (typing : Tm.HasType context term type) :
    Nonempty (Tm.HasType context next type) := by
  induction step generalizing context type with
  | appFunction step induction =>
      cases typing with
      | app functionTyping argumentTyping nonescape =>
          obtain ⟨functionTyping'⟩ := induction functionTyping
          exact ⟨.app functionTyping' argumentTyping nonescape⟩
  | appArgument _ step induction =>
      cases typing with
      | app functionTyping argumentTyping nonescape =>
          obtain ⟨argumentTyping'⟩ := induction argumentTyping
          exact ⟨.app functionTyping argumentTyping' nonescape⟩
  | beta _ =>
      exact preserveBeta typing
  | appCastArrow _ _ =>
      exact preserveAppCastArrow typing
  | letRhs step induction =>
      cases typing with
      | let' rhsTyping bodyTyping nonescape =>
          obtain ⟨rhsTyping'⟩ := induction rhsTyping
          exact ⟨.let' rhsTyping' bodyTyping nonescape⟩
  | zeta _ =>
      exact preserveZeta typing
  | castInner step induction =>
      cases typing with
      | cast termTyping evidenceTyping =>
          obtain ⟨termTyping'⟩ := induction termTyping
          exact ⟨.cast termTyping' evidenceTyping⟩
  | castRefl _ =>
      exact preserveCastRefl typing
  | castTrans _ =>
      exact preserveCastTrans typing
  | castEqRefl _ =>
      exact preserveCastEqRefl typing
  | castEqSymmRefl _ =>
      exact preserveCastEqSymmRefl typing
  | castEqSymmSymm _ =>
      exact preserveCastEqSymmSymm typing
  | castEqSymmTrans _ =>
      exact preserveCastEqSymmTrans typing
  | castEqTrans _ =>
      exact preserveCastEqTrans typing
  | packPayload step induction =>
      cases typing with
      | pack argumentsTyping payloadTyping =>
          obtain ⟨payloadTyping'⟩ := induction payloadTyping
          exact ⟨.pack argumentsTyping payloadTyping'⟩
  | openScrutinee step induction =>
      cases typing with
      | openT packageTyping bodyTyping nonescape =>
          obtain ⟨packageTyping'⟩ := induction packageTyping
          exact ⟨.openT packageTyping' bodyTyping nonescape⟩
  | openPack _ =>
      exact preserveOpenPack typing
  | openCastExists _ =>
      exact preserveOpenCastExists typing
  | sappFunction step induction =>
      cases typing with
      | sapp functionTyping argumentsTyping =>
          obtain ⟨functionTyping'⟩ := induction functionTyping
          exact ⟨.sapp functionTyping' argumentsTyping⟩
  | sappSlam _ =>
      exact preserveSappSlam typing
  | sappCastForall _ =>
      exact preserveSappCastForall typing
  | newtype =>
      exact preserveNewtype typing

end Tm.Step

end FCsub
