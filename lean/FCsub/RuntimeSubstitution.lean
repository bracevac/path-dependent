import FCsub.Runtime

/-!
# Substitution algebra for the erased runtime

Runtime terms mention only ordinary term variables, but their intrinsic
signatures retain erased type and evidence binders.  The heterogeneous lift
below is therefore needed to state erasure/substitution commutation cleanly.
-/

namespace FCsub.Runtime

namespace Subst

/-- Lift a runtime substitution below any FCsub binder kind. -/
def liftKind {source target : Sig} (substitution : Subst source target)
    (kind : BinderKind) : Subst (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => substitution.lift
  | .type =>
      { var := fun
          | .there index => (substitution.var index).weaken }
  | .evidence _relation =>
      { var := fun
          | .there index => (substitution.var index).weaken }

def liftN {source target : Sig} (substitution : Subst source target)
    (kind : BinderKind) : (count : Nat) →
    Subst (Sig.extendN source kind count) (Sig.extendN target kind count)
  | 0 => substitution
  | count + 1 => (liftN substitution kind count).liftKind kind

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
  (substitution.liftStatic names constraints).lift

def liftNewtype {source target : Sig} (substitution : Subst source target) :
    Subst (NewtypeScope source) (NewtypeScope target) :=
  (substitution.liftKind .type).liftKind (.evidence .equality)

/-- Precompose a substitution with a renaming. -/
def preRename {first second third : Sig} (rho : Rename first second)
    (substitution : Subst second third) : Subst first third where
  var := fun index => substitution.var (rho.var index)

/-- Rename every term supplied by a substitution. -/
def postRename {first second third : Sig} (substitution : Subst first second)
    (rho : Rename second third) : Subst first third where
  var := fun index => (substitution.var index).rename rho

@[simp]
theorem liftKind_ofRename {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) :
    (ofRename rho).liftKind kind = ofRename (rho.lift (kind := kind)) := by
  apply Subst.ext
  intro index
  cases kind with
  | term => cases index <;> rfl
  | type => cases index with | there index => rfl
  | evidence relation => cases index with | there index => rfl

@[simp]
theorem lift_ofRename {source target : Sig} (rho : Rename source target) :
    (ofRename rho).lift = ofRename rho.lift := by
  simpa [liftKind] using liftKind_ofRename rho .term

@[simp]
theorem liftN_ofRename {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) (count : Nat) :
    (ofRename rho).liftN kind count = ofRename (rho.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [liftN, induction, Rename.liftN, liftKind_ofRename]

@[simp]
theorem liftTypes_ofRename {source target : Sig}
    (rho : Rename source target) (names : Nat) :
    (ofRename rho).liftTypes names = ofRename (rho.liftTypes names) := by
  exact liftN_ofRename rho .type names

@[simp]
theorem liftStatic_ofRename {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    (ofRename rho).liftStatic names constraints =
      ofRename (rho.liftStatic names constraints) := by
  simp [liftStatic, Rename.liftStatic]

@[simp]
theorem liftPayload_ofRename {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    (ofRename rho).liftPayload names constraints =
      ofRename (rho.liftPayload names constraints) := by
  simp [liftPayload, Rename.liftPayload]

@[simp]
theorem liftNewtype_ofRename {source target : Sig}
    (rho : Rename source target) :
    (ofRename rho).liftNewtype = ofRename rho.liftNewtype := by
  simp [liftNewtype, Rename.liftNewtype]

@[simp]
theorem preRename_liftKind {first second third : Sig}
    (rho : Rename first second) (substitution : Subst second third)
    (kind : BinderKind) :
    (preRename rho substitution).liftKind kind =
      preRename (rho.lift (kind := kind)) (substitution.liftKind kind) := by
  apply Subst.ext
  intro index
  cases kind with
  | term => cases index <;> rfl
  | type => cases index with | there index => rfl
  | evidence relation => cases index with | there index => rfl

@[simp]
theorem preRename_lift {first second third : Sig}
    (rho : Rename first second) (substitution : Subst second third) :
    (preRename rho substitution).lift =
      preRename rho.lift substitution.lift := by
  simpa [liftKind] using preRename_liftKind rho substitution .term

@[simp]
theorem postRename_liftKind {first second third : Sig}
    (substitution : Subst first second) (rho : Rename second third)
    (kind : BinderKind) :
    (postRename substitution rho).liftKind kind =
      postRename (substitution.liftKind kind) (rho.lift (kind := kind)) := by
  apply Subst.ext
  intro index
  cases kind with
  | term =>
      cases index with
      | here => rfl
      | there index =>
          simp only [liftKind, lift, postRename, Tm.weaken,
            Tm.rename_comp, Rename.succ_lift_comm]
  | type =>
      cases index with
      | there index =>
          simp only [liftKind, postRename, Tm.weaken,
            Tm.rename_comp, Rename.succ_lift_comm]
  | evidence relation =>
      cases index with
      | there index =>
          simp only [liftKind, postRename, Tm.weaken,
            Tm.rename_comp, Rename.succ_lift_comm]

@[simp]
theorem postRename_lift {first second third : Sig}
    (substitution : Subst first second) (rho : Rename second third) :
    (postRename substitution rho).lift =
      postRename substitution.lift rho.lift := by
  simpa [liftKind] using postRename_liftKind substitution rho .term

end Subst

namespace Tm

theorem subst_congr {source target : Sig} (term : Tm source)
    {first second : Subst source target}
    (equal : ∀ index, first.var index = second.var index) :
    term.subst first = term.subst second := by
  have substitutions : first = second := Subst.ext equal
  cases substitutions
  rfl

@[simp]
theorem subst_ofRename {source target : Sig} (term : Tm source)
    (rho : Rename source target) :
    term.subst (Subst.ofRename rho) = term.rename rho := by
  induction term generalizing target with
  | var index => rfl
  | lam body induction =>
      simp only [subst, rename, Subst.lift_ofRename, induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [subst, rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [subst, rename, rhsInduction, Subst.lift_ofRename,
        bodyInduction]

@[simp]
theorem rename_subst {first second third : Sig} (term : Tm first)
    (rho : Rename first second) (substitution : Subst second third) :
    (term.rename rho).subst substitution =
      term.subst (Subst.preRename rho substitution) := by
  induction term generalizing second third with
  | var index => rfl
  | lam body induction =>
      simp only [rename, subst, induction, Subst.preRename_lift]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, subst, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [rename, subst, rhsInduction,
        Subst.preRename_lift, bodyInduction]

@[simp]
theorem subst_rename {first second third : Sig} (term : Tm first)
    (substitution : Subst first second) (rho : Rename second third) :
    (term.subst substitution).rename rho =
      term.subst (Subst.postRename substitution rho) := by
  induction term generalizing second third with
  | var index => rfl
  | lam body induction =>
      simp only [subst, rename, induction, Subst.postRename_lift]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [subst, rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [subst, rename, rhsInduction,
        Subst.postRename_lift, bodyInduction]

/-- Substitution commutes with weakening below any erased binder. -/
@[simp]
theorem weaken_subst_liftKind {source target : Sig} (term : Tm source)
    (substitution : Subst source target) (kind : BinderKind) :
    term.weaken.subst (substitution.liftKind kind) =
      (term.subst substitution).weaken := by
  calc
    term.weaken.subst (substitution.liftKind kind) =
        term.subst (Subst.preRename Rename.succ
          (substitution.liftKind kind)) :=
      rename_subst term Rename.succ (substitution.liftKind kind)
    _ = term.subst (Subst.postRename substitution Rename.succ) := by
      apply subst_congr
      intro index
      cases kind <;> rfl
    _ = (term.subst substitution).weaken := by
      exact (subst_rename term substitution Rename.succ).symm

end Tm

namespace Subst

/-- Diagrammatic composition: substitute with `first`, then `second`. -/
def comp {first second third : Sig} (firstSubst : Subst first second)
    (secondSubst : Subst second third) : Subst first third where
  var := fun index => (firstSubst.var index).subst secondSubst

@[simp]
theorem liftKind_comp {first second third : Sig}
    (firstSubst : Subst first second) (secondSubst : Subst second third)
    (kind : BinderKind) :
    (firstSubst.comp secondSubst).liftKind kind =
      (firstSubst.liftKind kind).comp (secondSubst.liftKind kind) := by
  apply Subst.ext
  intro index
  cases kind with
  | term =>
      cases index with
      | here => rfl
      | there index =>
          exact (Tm.weaken_subst_liftKind
            (firstSubst.var index) secondSubst .term).symm
  | type =>
      cases index with
      | there index =>
          exact (Tm.weaken_subst_liftKind
            (firstSubst.var index) secondSubst .type).symm
  | evidence relation =>
      cases index with
      | there index =>
          exact (Tm.weaken_subst_liftKind
            (firstSubst.var index) secondSubst (.evidence relation)).symm

@[simp]
theorem lift_comp {first second third : Sig}
    (firstSubst : Subst first second) (secondSubst : Subst second third) :
    (firstSubst.comp secondSubst).lift =
      firstSubst.lift.comp secondSubst.lift := by
  simpa [liftKind] using liftKind_comp firstSubst secondSubst .term

end Subst

namespace Tm

@[simp]
theorem subst_comp {first second third : Sig} (term : Tm first)
    (firstSubst : Subst first second) (secondSubst : Subst second third) :
    (term.subst firstSubst).subst secondSubst =
      term.subst (firstSubst.comp secondSubst) := by
  induction term generalizing second third with
  | var index => rfl
  | lam body induction =>
      simp only [subst, induction, Subst.lift_comp]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [subst, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [subst, rhsInduction, bodyInduction, Subst.lift_comp]

end Tm

namespace Subst

@[simp]
theorem comp_id {source target : Sig} (substitution : Subst source target) :
    substitution.comp id = substitution := by
  apply ext
  intro index
  simp [comp]

@[simp]
theorem id_comp {source target : Sig} (substitution : Subst source target) :
    id.comp substitution = substitution := by
  apply ext
  intro index
  rfl

@[simp]
theorem ofRename_comp {first second third : Sig}
    (rho : Rename first second) (substitution : Subst second third) :
    (ofRename rho).comp substitution = preRename rho substitution := by
  apply ext
  intro index
  rfl

@[simp]
theorem comp_ofRename {first second third : Sig}
    (substitution : Subst first second) (rho : Rename second third) :
    substitution.comp (ofRename rho) = postRename substitution rho := by
  apply ext
  intro index
  exact Tm.subst_ofRename _ _

@[simp]
theorem liftN_comp {first second third : Sig}
    (firstSubst : Subst first second) (secondSubst : Subst second third)
    (kind : BinderKind) (count : Nat) :
    (firstSubst.comp secondSubst).liftN kind count =
      (firstSubst.liftN kind count).comp
        (secondSubst.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, liftKind_comp, induction]
      rfl

@[simp]
theorem liftTypes_comp {first second third : Sig}
    (firstSubst : Subst first second) (secondSubst : Subst second third)
    (names : Nat) :
    (firstSubst.comp secondSubst).liftTypes names =
      (firstSubst.liftTypes names).comp (secondSubst.liftTypes names) := by
  exact liftN_comp firstSubst secondSubst .type names

@[simp]
theorem liftStatic_comp {first second third : Sig}
    (firstSubst : Subst first second) (secondSubst : Subst second third)
    (names constraints : Nat) :
    (firstSubst.comp secondSubst).liftStatic names constraints =
      (firstSubst.liftStatic names constraints).comp
        (secondSubst.liftStatic names constraints) := by
  simp [liftStatic]

/-- Dropping erased type binders is natural in the ambient runtime
substitution. -/
@[simp]
theorem liftTypes_comp_dropTypes {source target : Sig}
    (substitution : Subst source target) (names : Nat) :
    (substitution.liftTypes names).comp
        (dropTypes (scope := target) names) =
      (dropTypes (scope := source) names).comp substitution := by
  induction names with
  | zero => simp [liftTypes, liftN, dropTypes]
  | succ names induction =>
      apply ext
      intro index
      cases index with
      | there index =>
          simp only [liftTypes, liftN, liftKind, comp, dropTypes]
          calc
            ((substitution.liftN .type names).var index).weaken.subst
                (dropTypes (scope := target) (names + 1)) =
                ((substitution.liftN .type names).var index).subst
                  (dropTypes (scope := target) names) := by
              simp only [Tm.weaken]
              rw [Tm.rename_subst]
              apply Tm.subst_congr
              intro inner
              rfl
            _ = ((dropTypes (scope := source) names).var index).subst
                substitution := by
              have point := congrArg (fun current => current.var index) induction
              exact point

/-- Dropping a complete static suffix commutes with ambient runtime
substitution. -/
@[simp]
theorem liftStatic_comp_dropStatic {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    (substitution.liftStatic names constraints).comp
        (dropStatic (scope := target) names constraints) =
      (dropStatic (scope := source) names constraints).comp substitution := by
  induction constraints with
  | zero =>
      simp [liftStatic, liftN, dropStatic]
  | succ constraints induction =>
      apply ext
      intro index
      cases index with
      | there index =>
          simp only [liftStatic, liftN, liftKind, comp, dropStatic]
          calc
            (((substitution.liftTypes names).liftN
                (.evidence .inclusion) constraints).var index).weaken.subst
                (dropStatic (scope := target) names (constraints + 1)) =
                (((substitution.liftTypes names).liftN
                  (.evidence .inclusion) constraints).var index).subst
                  (dropStatic (scope := target) names constraints) := by
              simp only [Tm.weaken]
              rw [Tm.rename_subst]
              apply Tm.subst_congr
              intro inner
              rfl
            _ = ((dropStatic (scope := source) names constraints).var
                  index).subst substitution := by
              have point := congrArg (fun current => current.var index) induction
              exact point

/-- Dropping a static telescope while retaining its payload is natural in
the ambient substitution, lifted below the retained term binder. -/
@[simp]
theorem liftPayload_comp_dropPayload {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    (substitution.liftPayload names constraints).comp
        (dropPayload (scope := target) names constraints) =
      (dropPayload (scope := source) names constraints).comp
        substitution.lift := by
  apply ext
  intro index
  cases index with
  | here => rfl
  | there index =>
      simp only [liftPayload, comp, lift, dropPayload]
      calc
        ((substitution.liftStatic names constraints).var index).weaken.subst
            (dropPayload (scope := target) names constraints) =
            (((substitution.liftStatic names constraints).var index).subst
              (dropStatic (scope := target) names constraints)).weaken := by
          simp only [Tm.weaken]
          rw [Tm.rename_subst, Tm.subst_rename]
          apply Tm.subst_congr
          intro inner
          rfl
        _ = (((dropStatic (scope := source) names constraints).var index).subst
              substitution).weaken := by
          have point := congrArg (fun current => current.var index)
            (liftStatic_comp_dropStatic substitution names constraints)
          simpa [comp] using congrArg Tm.weaken point
        _ = ((dropStatic (scope := source) names constraints).var index).weaken.subst
              substitution.lift := by
          exact (Tm.weaken_subst_liftKind
            ((dropStatic (scope := source) names constraints).var index)
            substitution .term).symm

/-- Dropping the private type/equality pair commutes with ambient runtime
substitution. -/
@[simp]
theorem liftNewtype_comp_dropNewtype {source target : Sig}
    (substitution : Subst source target) :
    substitution.liftNewtype.comp (dropNewtype (scope := target)) =
      (dropNewtype (scope := source)).comp substitution := by
  apply ext
  intro index
  cases index with
  | there index =>
      cases index with
      | there index =>
          simp only [liftNewtype, liftKind, comp, dropNewtype]
          simp only [Tm.weaken]
          rw [Tm.rename_comp, Tm.rename_subst]
          change (substitution.var index).subst
              (preRename (Rename.succ.comp Rename.succ)
                (dropNewtype (scope := target))) = substitution.var index
          calc
            _ = (substitution.var index).subst id := by
              apply Tm.subst_congr
              intro inner
              rfl
            _ = substitution.var index := Tm.subst_id _

@[simp]
theorem ofRename_weakenTypes_comp_dropTypes {scope : Sig} (names : Nat) :
    (ofRename (Rename.weakenTypes (scope := scope) names)).comp
        (dropTypes names) = id := by
  induction names with
  | zero => rfl
  | succ names induction =>
      apply ext
      intro index
      have point := congrArg (fun current => current.var index) induction
      simpa [Rename.weakenTypes, Rename.weakenN, Rename.comp,
        comp, dropTypes, ofRename, id] using point

@[simp]
theorem ofRename_weakenStatic_comp_dropStatic {scope : Sig}
    (names constraints : Nat) :
    (ofRename (Rename.weakenStatic (scope := scope) names constraints)).comp
        (dropStatic names constraints) = id := by
  induction constraints with
  | zero =>
      simpa [Rename.weakenStatic, Rename.weakenN, dropStatic] using
        ofRename_weakenTypes_comp_dropTypes (scope := scope) names
  | succ constraints induction =>
      apply ext
      intro index
      have point := congrArg (fun current => current.var index) induction
      simpa [Rename.weakenStatic, Rename.weakenN, Rename.comp,
        comp, dropStatic, ofRename, id] using point

@[simp]
theorem ofRename_weakenPayload_comp_dropPayload {scope : Sig}
    (names constraints : Nat) :
    (ofRename (Rename.weakenPayload (scope := scope) names constraints)).comp
        (dropPayload names constraints) = ofRename Rename.succ := by
  apply ext
  intro index
  have point := congrArg (fun current => current.var index)
    (ofRename_weakenStatic_comp_dropStatic (scope := scope)
      names constraints)
  simpa [Rename.weakenPayload, Rename.comp, comp, dropPayload,
    ofRename, id, Tm.weaken, Tm.subst_ofRename] using
    congrArg Tm.weaken point

@[simp]
theorem preRename_liftStatic_dropStatic {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    preRename (rho.liftStatic names constraints)
        (dropStatic (scope := target) names constraints) =
      postRename (dropStatic (scope := source) names constraints) rho := by
  rw [← ofRename_comp, ← liftStatic_ofRename,
    liftStatic_comp_dropStatic, comp_ofRename]

@[simp]
theorem preRename_liftPayload_dropPayload {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    preRename (rho.liftPayload names constraints)
        (dropPayload (scope := target) names constraints) =
      postRename (dropPayload (scope := source) names constraints)
        rho.lift := by
  rw [← ofRename_comp, ← liftPayload_ofRename,
    liftPayload_comp_dropPayload, lift_ofRename, comp_ofRename]

@[simp]
theorem preRename_liftNewtype_dropNewtype {source target : Sig}
    (rho : Rename source target) :
    preRename rho.liftNewtype (dropNewtype (scope := target)) =
      postRename (dropNewtype (scope := source)) rho := by
  rw [← ofRename_comp, ← liftNewtype_ofRename,
    liftNewtype_comp_dropNewtype, comp_ofRename]

end Subst

end FCsub.Runtime
