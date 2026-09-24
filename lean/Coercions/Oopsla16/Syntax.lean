import Coercions.FCdot.Debruijn

/-!
# Syntax of the OOPSLA'16 reference DOT calculus

The calculus of `oopsla16/dot.v` from the pinned minidot artifact
`ef1143dc1875d389c47083cd324971b1b86686d1`, in the intrinsically scoped
discipline of `FCdot.Debruijn` rather than the reference's locally nameless
one.  Three deviations follow from that choice and are recorded once here.

* The reference's `closed i j k T` predicate (`dot.v:100-127`) and every
  `closed` premise of every rule disappear: scoping is the indexing.  Three of
  those premises say that a type does not mention a variable; they become
  explicit weakenings.  Two constrain the context; they become the prefix
  indexing of `Ctx`, which is a restriction (`README.md`).
* The reference's `TVarB` (`dot.v:23`) disappears: a bound variable is an
  abstract variable of an extended scope, so `open 0 u T` (`dot.v:135`) is
  `Ty.substVr T u`.
* The derivation-size index of `dot.v:219-393` is dropped.  The reference
  uses it for its inductions on derivation size (transitivity pushback and
  narrowing, and also `all_extend`, `all_closed`, `stp_splice_aux`,
  `stp_upgrade_gh_aux`, `subst_aux`, `hastp_subst_aux`); derivations here are
  `Type`-valued data and carry their own structural measure.

What does **not** change is the part of the reference that carries its
soundness.  Variables still have **two zones**, and the distinction is
syntactic: `Vr.conc` indexes the runtime store, `Vr.abs` indexes the
hypothetical context, and subtyping resolves a selection on the first against
the stored definition and on the second through the packing-free judgment
`Htp`.  Labels are still **positional** and share one namespace: `Lb := Nat`
indexes both `TFun` and `TTyp`, a member's label is the length of its tail
(`dot.v:269`, `dot.v:278`), and there is no type/term label category and no
distinctness condition.  `Dms` is still a bespoke cons list.

Types carry two scopes, written `Ty σ s`: `σ` is the store scope and `s` is
the local scope of hypotheses and enclosing binders.  They are separate
because the reference keeps them separate — `stp_strong_sel1` checks its
premise in the *empty* local scope over the *full* store (`dot.v:308`) — and
because a rule must be able to dispatch on which zone a receiver lives in.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-! ## Labels

`lb := nat`, `dot.v:18`.  One namespace for type and method members alike; a
member's label is its position in the enclosing definition list. -/

abbrev Lb : Type := Nat

/-! ## Variables -/

/-- Variables, `dot.v:20-24`, with the bound form absorbed into the local
scope `s`.  `TVar true x` is `conc x` and `TVar false x` is `abs x`. -/
inductive Vr : Sig → Sig → Type where
  /-- A concrete variable: a location of the runtime store. -/
  | conc : BVar σ .var → Vr σ s
  /-- An abstract variable: a hypothesis or an enclosing binder. -/
  | abs : BVar s .var → Vr σ s
deriving DecidableEq

/-! ## Types -/

/-- Types, `dot.v:26-38`. -/
inductive Ty : Sig → Sig → Type where
  /-- `TBot`, `dot.v:27`. -/
  | TBot : Ty σ s
  /-- `TTop`, `dot.v:28`. -/
  | TTop : Ty σ s
  /-- `TFun l S U`, the method member `{ def l(x : S) : U^x }`.  `dot.v:29-31`. -/
  | TFun : Lb → Ty σ s → Ty σ (s,x) → Ty σ s
  /-- `TTyp l S U`, the type member `{ type l : S..U }`.  `dot.v:32`. -/
  | TTyp : Lb → Ty σ s → Ty σ s → Ty σ s
  /-- `TSel p l`, the type selection `p.l`.  `dot.v:33`. -/
  | TSel : Vr σ s → Lb → Ty σ s
  /-- `TBind T`, the recursive type `{ z => T^z }`.  `dot.v:34-35`. -/
  | TBind : Ty σ (s,x) → Ty σ s
  /-- `TAnd S T`, `dot.v:36`. -/
  | TAnd : Ty σ s → Ty σ s → Ty σ s
  /-- `TOr S T`, `dot.v:37`. -/
  | TOr : Ty σ s → Ty σ s → Ty σ s
deriving DecidableEq

/-! ## Terms, definitions and definition lists -/

mutual

/-- Terms, `dot.v:40-44`.  Application is general: neither operand is
restricted to a variable, so the calculus is not in normal form. -/
inductive Tm : Sig → Sig → Type where
  /-- `tvar b x`, `dot.v:41`. -/
  | tvar : Vr σ s → Tm σ s
  /-- `tobj ds`, `dot.v:43`.  The reference's self is the next slot of the
  abstract context; here it is the binder of `ds`. -/
  | tobj : Dms σ (s,x) → Tm σ s
  /-- `tapp t l u`, `dot.v:44`. -/
  | tapp : Tm σ s → Lb → Tm σ s → Tm σ s

/-- Member definitions, `dot.v:46-51`.  The label is the position in the
enclosing `Dms`, so `Dm` carries none. -/
inductive Dm : Sig → Sig → Type where
  /-- `dfun OS OU t`, `dot.v:48-50`.  Both annotations are optional, which is
  how the reference shows that Church and Curry style both work; `D_Fun`
  relates them to the checked types by `EqSome`.  The codomain and the body
  bind the parameter. -/
  | dfun : Option (Ty σ s) → Option (Ty σ (s,x)) → Tm σ (s,x) → Dm σ s
  /-- `dty T`, `dot.v:51`. -/
  | dty : Ty σ s → Dm σ s

/-- Definition lists, `dot.v:53-57`.  A bespoke cons list, for the reason
given at `dot.v:53`: substitution is one mutual structural recursion. -/
inductive Dms : Sig → Sig → Type where
  /-- `dnil`, `dot.v:55`. -/
  | dnil : Dms σ s
  /-- `dcons d ds`, `dot.v:56`: `d` is the newest member and its label is the
  length of `ds`. -/
  | dcons : Dm σ s → Dms σ s → Dms σ s

end

/-- `dms_to_list`, `dot.v:59-63`. -/
def Dms.toList : Dms σ s → List (Dm σ s)
  | .dnil => []
  | .dcons d ds => d :: ds.toList

/-- The number of members, hence the label of the next member to be consed. -/
def Dms.length (ds : Dms σ s) : Nat := ds.toList.length

@[simp] theorem Dms.length_dnil : (Dms.dnil (σ := σ) (s := s)).length = 0 := rfl

@[simp] theorem Dms.length_dcons (d : Dm σ s) (ds : Dms σ s) :
    (Dms.dcons d ds).length = ds.length + 1 := rfl

/-- The member at label `l`, i.e. `index l (dms_to_list ds)` of `dot.v:203`.
Labels count from the end, so the member at the front of a list of `n` members
has label `n - 1` and the oldest member has label `0`. -/
def Dms.get? : Dms σ s → Lb → Option (Dm σ s)
  | .dnil, _ => none
  | .dcons d ds, l => if l = ds.length then some d else ds.get? l

/-! ## Values and stores

A value is an allocated object.  The reference substitutes the object's own
new location into its definitions at allocation (`dot.v:199-200`), so a stored
definition list that `step` builds from a well-scoped term has no free
abstract variable.

`venv := list vl` (`dot.v:69`) is otherwise unconstrained: there is no store
well-formedness predicate anywhere in the artifact, every stored object is
bounded by the same `length G1`, and `type_safety` (`dot_soundness.v:1131`) is
stated for an arbitrary store.  A stored object may therefore mention a
location allocated *after* it, and two objects may mention each other.  So the
store is indexed *twice*: `Store σ σ'` holds the objects at the binders of
`σ'`, each living in the full store scope `σ`, and a complete store is
`Store σ σ`.  Indexing the entries by their own prefix instead would be
strictly stronger than the reference.

**`Store` is nonetheless a restriction of `venv`.**  Each entry is a
`Dms σ []`, so every variable in a stored object is in range: it mentions no
abstract variable, no dangling `TVarB` and no location outside the store.
`venv` admits objects that break each of the three, and the reference derives
judgments over such stores, since `stp_strong_sel1`/`stp_strong_sel2` read the
one member they select (`coq/oopsla16/deviations/store_restriction.v`,
`store_restriction_is_real`).  So `type_safety` speaks about configurations no
`Store` can express.  In the reference, every store reached by running a
closed, well-scoped term from the empty store has all its variables in range,
so no reachable configuration is lost; that is argued, not proved. -/

/-- A store fragment: one object per binder of `σ'`, each well scoped in the
full store scope `σ`.  A complete store is `Store σ σ`.  `venv`, `dot.v:69`. -/
inductive Store : Sig → Sig → Type where
  /-- The empty fragment. -/
  | nil : Store σ []
  /-- One more location. -/
  | cons : Store σ σ' → Dms σ [] → Store σ (σ',x)

end Oopsla16
