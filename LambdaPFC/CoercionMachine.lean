import LambdaPFC.Member

/-!
An operational account of evidence retrieved from abstract members.

Selection coercions are reduced by looking up the code stored for the selected
member.  The retrieved code is placed on a typed control stack; `step` does not
interpret it recursively.  The reduction relation is therefore well-founded as
a definition even when stored coercions contain further selections; cycles
appear as infinite executions and must be excluded separately.
-/

namespace LambdaPFC

open LambdaP

/-- Static evidence that a path has an abstract member with given bounds. -/
structure MemberSignature where
  Check : {n : Nat} -> Path n -> Name -> Ty n -> Ty n -> Prop

/-- Directed coercion code, including neutral abstract-member selections. -/
inductive Coercion (sig : MemberSignature) :
    {n : Nat} -> Ty n -> Ty n -> Type where
| static : Evidence (.map S T) -> Coercion sig S T
| trans : Coercion sig S T -> Coercion sig T U -> Coercion sig S U
| selLo : sig.Check p A L U -> Coercion sig L (.TSel p A)
| selHi : sig.Check p A L U -> Coercion sig (.TSel p A) U

/-- Source subtyping obtained by erasing operational coercion code. -/
inductive CoSub (sig : MemberSignature) :
    {n : Nat} -> Ty n -> Ty n -> Prop where
| static : Sub S T -> CoSub sig S T
| trans : CoSub sig S T -> CoSub sig T U -> CoSub sig S U
| selLo : sig.Check p A L U -> CoSub sig L (.TSel p A)
| selHi : sig.Check p A L U -> CoSub sig (.TSel p A) U

/-- Erasure retains the source selection premises and forgets executable code. -/
theorem Coercion.erase (c : Coercion sig S T) : CoSub sig S T := by
  induction c with
  | static c => exact .static c.erase
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | selLo h => exact .selLo h
  | selHi h => exact .selHi h

/--
A typed runtime environment for member coercions at one fixed valuation.  Each
checked member has an internal witness, resolves to that witness in the runtime
model, and supplies lower and upper coercion code.  The witness is canonical
for a given path and label, independently of the bounds derivation.
-/
structure CoWorld (sig : MemberSignature) {n m : Nat}
    (rho : Valuation n m) where
  model : Model m
  witness : Path n -> Name -> Ty n
  resolves : forall {p : Path n} {A : Name} {L U : Ty n}
      (_h : sig.Check p A L U),
    Resolve model rho (p.sel A) (.type (instantiateTy rho (witness p A)))
  lower : forall {p : Path n} {A : Name} {L U : Ty n}
      (_h : sig.Check p A L U),
    Coercion sig L (witness p A)
  upper : forall {p : Path n} {A : Name} {L U : Ty n}
      (_h : sig.Check p A L U),
    Coercion sig (witness p A) U

/--
Runtime classification used by the coercion machine.  The `selected` clause
keeps the hidden witness behind the surface selection `p.A`.
-/
inductive ValueAt {n m : Nat} {rho : Valuation n m}
    {sig : MemberSignature} (W : CoWorld sig rho) :
    Fin m -> Ty n -> Prop where
| base : Possible W.model rho x T -> ValueAt W x T
| selected :
    (h : sig.Check p A L U) ->
    ValueAt W x (W.witness p A) ->
    ValueAt W x (.TSel p A)

/-- Static evidence also acts on the extended runtime classification. -/
def Evidence.actionAt
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {S T : Ty n} {x : Fin m}
    (c : Evidence (.map S T)) (v : ValueAt W x S) : ValueAt W x T :=
  match c with
  | .refl => v
  | .trans c1 c2 => c2.actionAt (c1.actionAt v)
  | .bot => by
      cases v with
      | base hv => cases hv
  | .top => .base .top
  | .pair cFirst cMember => by
      cases v with
      | base hv =>
          exact .base ((Evidence.pair cFirst cMember).action W.model rho x hv)

/-- Reveal the witness associated with a selected value and a bounds check. -/
def ValueAt.unselect
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {p : Path n} {A : Name} {L U : Ty n}
    {x : Fin m} (_h : sig.Check p A L U)
    (v : ValueAt W x (.TSel p A)) : ValueAt W x (W.witness p A) := by
  cases v with
  | base hv => cases hv
  | selected h' hv => exact hv

/--
A typed continuation from the current type to the final target.  `seal` hides
a completed lower-bound coercion behind the corresponding abstract selection.
-/
inductive Stack {n m : Nat} {rho : Valuation n m}
    {sig : MemberSignature} (W : CoWorld sig rho) :
    Ty n -> Ty n -> Type where
| done : Stack W T T
| apply : Coercion sig S T -> Stack W T U -> Stack W S U
| hide :
    (h : sig.Check p A L U) ->
    Stack W (.TSel p A) T ->
    Stack W (W.witness p A) T

/-- A well-typed coercion-machine state with a fixed final target. -/
structure State {n m : Nat} {rho : Valuation n m}
    {sig : MemberSignature} (W : CoWorld sig rho) (target : Ty n) where
  current : Ty n
  raw : Fin m
  realizes : ValueAt W raw current
  stack : Stack W current target

/-- Initial state for applying a coercion to a classified runtime value. -/
def State.start
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {S T : Ty n} {x : Fin m}
    (c : Coercion sig S T) (v : ValueAt W x S) : State W T :=
  ⟨S, x, v, .apply c .done⟩

/-- One administrative or coercion-reduction step. -/
inductive State.Step
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} :
    State W target -> State W target -> Prop where
| pack
    (h : sig.Check p A L U) (x : Fin m)
    (v : ValueAt W x (W.witness p A))
    (k : Stack W (.TSel p A) target) :
    Step
      ⟨W.witness p A, x, v, Stack.hide (W := W) h k⟩
      ⟨.TSel p A, x, .selected h v, k⟩
| static
    (c : Evidence (.map S T)) (x : Fin m) (v : ValueAt W x S)
    (k : Stack W T target) :
    Step
      ⟨S, x, v, .apply (.static c) k⟩
      ⟨T, x, c.actionAt v, k⟩
| split
    (c1 : Coercion sig S T) (c2 : Coercion sig T U)
    (x : Fin m) (v : ValueAt W x S) (k : Stack W U target) :
    Step
      ⟨S, x, v, .apply (.trans c1 c2) k⟩
      ⟨S, x, v, .apply c1 (.apply c2 k)⟩
| lower
    (h : sig.Check p A L U) (x : Fin m) (v : ValueAt W x L)
    (k : Stack W (.TSel p A) target) :
    Step
      ⟨L, x, v, .apply (.selLo h) k⟩
      ⟨L, x, v,
        Stack.apply (W := W) (W.lower h) (Stack.hide (W := W) h k)⟩
| upper
    (h : sig.Check p A L U) (x : Fin m)
    (v : ValueAt W x (.TSel p A)) (k : Stack W U target) :
    Step
      ⟨.TSel p A, x, v, .apply (.selHi h) k⟩
      ⟨W.witness p A, x, v.unselect h, .apply (W.upper h) k⟩

/-- A state is final exactly when its typed control stack is empty. -/
inductive State.Final
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} : State W target -> Prop where
| done (x : Fin m) (v : ValueAt W x target) :
    Final ⟨target, x, v, .done⟩

/-- A final state contains a realization of its declared target. -/
theorem State.Final.target_realized
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} {s : State W target}
    (h : s.Final) : ValueAt W s.raw target := by
  cases h
  assumption

/-- Every well-typed state is final or takes a step. -/
theorem State.progress
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} (s : State W target) :
    s.Final \/ exists s', s.Step s' := by
  cases s with
  | mk current raw realizes stack =>
      cases stack with
      | done => exact Or.inl (.done _ _)
      | hide h k => exact Or.inr ⟨_, .pack h raw realizes k⟩
      | apply c k =>
          cases c with
          | static c => exact Or.inr ⟨_, .static c raw realizes k⟩
          | trans c1 c2 => exact Or.inr ⟨_, .split c1 c2 raw realizes k⟩
          | selLo h => exact Or.inr ⟨_, .lower h raw realizes k⟩
          | selHi h => exact Or.inr ⟨_, .upper h raw realizes k⟩

/-- Erasure of a machine state is its underlying runtime location. -/
def State.erase
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} (s : State W target) : Fin m :=
  s.raw

/-- Coercion reduction preserves erased runtime data. -/
theorem State.Step.preserves_erase
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} {s s' : State W target}
    (h : s.Step s') : s'.erase = s.erase := by
  cases h <;> rfl

/-- Reflexive, transitive closure of coercion reduction. -/
inductive State.Steps
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} :
    State W target -> State W target -> Prop where
| refl : Steps s s
| tail : s1.Step s2 -> Steps s2 s3 -> Steps s1 s3

/-- Any finite coercion execution preserves erased runtime data. -/
theorem State.Steps.preserves_erase
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {target : Ty n} {s s' : State W target}
    (h : s.Steps s') : s'.erase = s.erase := by
  induction h with
  | refl => rfl
  | tail hstep _ ih => exact ih.trans hstep.preserves_erase

/-- A finite run from a coercion application to a final state. -/
structure Coercion.Run
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {S T : Ty n} {x : Fin m}
    (c : Coercion sig S T) (v : ValueAt W x S) where
  finish : State W T
  steps : (State.start c v).Steps finish
  final : finish.Final

/-- A terminating coercion run yields the target realization. -/
theorem Coercion.Run.result
    {n m : Nat} {rho : Valuation n m} {sig : MemberSignature}
    {W : CoWorld sig rho} {S T : Ty n} {x : Fin m}
    {c : Coercion sig S T} {v : ValueAt W x S}
    (run : c.Run v) : ValueAt W x T := by
  have hraw : run.finish.raw = x := by
    simpa [State.erase, State.start] using run.steps.preserves_erase
  rw [← hraw]
  exact run.final.target_realized

end LambdaPFC
