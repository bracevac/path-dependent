import Coercions.FCdotR.Machine
import Coercions.Oopsla16.PackingCounterexample

/-!
# Erasure into the source, and the simulation

The target's terms erase into the **source's own** terms — `Oopsla16.Tm`, not
a separate untyped runtime as in the main line, because the type translation
here is the identity and the source is already the right untyped language.
Atoms erase to their root variable, coercions and the self annotation of a
literal vanish, and a definition list keeps its types as the annotations the
source's `EqSome` admits.

## `let`

The source has no `let`.  Erasure is nonetheless total: `let x = t in u`
becomes `letEncode`, the application `(ν(_. { λ(x). u })).0 (t)`, which is the
standard encoding and is what the store-and-continuation shape of this machine
is A-normalising away from.  Everything below is proved for *all* terms.

What the encoding cannot do is simulate.  `Cont.plug` — the source context a
continuation erases to — sends a `let` frame to that application, so the
machine's `let` step erases to an *equality* of configurations, which is what
one wants; but the `rename` step that consumes a `let` frame erases to a source
configuration that must first allocate the encoding's object, and the two store
scopes then differ.  So the simulation theorem below carries the hypothesis
`st.K.Evidential`: the continuation holds coercion frames only.  Under that
hypothesis every rule is covered, `rename` included (it cannot fire), and the
hypothesis holds throughout the run of a term with no `let` in it.  That is the
honest fragment, and it is stated as such rather than patched.

## What is proved

* `Tm.erase_inst`, `Defs.erase_inst`: erasure commutes with the machine's
  substitution, `(t.inst ι y).erase = t.erase.subst (ι.toSubst y)`.
* `Tm.erase_renameStore`, `MachineStore.erase_renameStore`: and with allocation's
  store weakening.
* `Tm.erase_subst`, `Defs.erase_subst`: the same for `Subst`'s *generated*
  substitution, and `Tm.erase_inst_subst`, which says the machine's traversal
  and that one erase to the same source term.  `Machine.MonoSyn.ofInst` is what
  makes the two comparable.
* `Step.simulate`: one machine step erases to **zero or one** source step, at
  the very same `Grows` index — zero for the three administrative rules, one
  for `alloc` (`ST_Obj`) and `app` (`ST_AppAbs`).
* `State.LetFree` and `Step.letFree`: the fragment the hypothesis describes is
  closed under stepping, and `Steps.simulate` iterates the simulation on it.
* `badRun`: the two-object store of `Oopsla16.PackingCounterexample` as an
  FCdotR program that allocates both objects and runs to a stuck state whose
  store erases to that counterexample's `G`, whose term erases to its
  `badTerm`, and whose erasure is stuck for the reason that module proves.

What is **not** here: any typing property.  The machine drops an atom's
coercions when it substitutes (see `Machine`), so the erasure results below are
runtime statements only, and a preservation theorem would need the substitution
theorem `Structural` is still missing.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Subst Grows)

/-! ## The source encoding of `let` -/

/-- `let x = t in u`, in a calculus that has only methods: a one-method object
applied to `t`, the method's parameter being `x`.  The renaming pushes `u`
under the object's self binder, which the body ignores. -/
def letEncode {σ s : Sig} (t : Oopsla16.Tm σ s) (u : Oopsla16.Tm σ (s,x)) :
    Oopsla16.Tm σ s :=
  .tapp (.tobj (.dcons (.dfun none none
    (u.subst (Subst.ofRename (Rename.succ.lift)))) .dnil)) 0 t

/-- Weakening past a binder commutes with a lifted substitution.  This is the
one law the encoding needs, and it is why the erasure of a `let` is stable
under substitution. -/
theorem Subst.succLift_comm {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (Subst.ofRename (Rename.succ.lift)).comp θ.lift.lift
      = θ.lift.comp (Subst.ofRename (Rename.succ.lift)) := by
  apply Subst.ext <;> intro z
  · rfl
  · cases z with
    | here => rfl
    | there z =>
        show ((θ.abs z).weaken).weaken
            = ((θ.abs z).weaken).subst (Subst.ofRename (Rename.succ.lift))
        cases θ.abs z <;> rfl

/-- The encoding commutes with substitution. -/
theorem letEncode_subst {σ1 σ2 s1 s2 : Sig} (t : Oopsla16.Tm σ1 s1)
    (u : Oopsla16.Tm σ1 (s1,x)) (θ : Subst σ1 s1 σ2 s2) :
    (letEncode t u).subst θ = letEncode (t.subst θ) (u.subst θ.lift) := by
  simp only [letEncode, Oopsla16.Tm.subst, Oopsla16.Dms.subst, Oopsla16.Dm.subst,
    Option.map_none, Oopsla16.Tm.subst_comp, Subst.succLift_comm]

/-! ## Erasure -/

/-- An atom erases to its root: every coercion, pack and unpack is a no-op. -/
def Atom.erase {σ s : Sig} (a : Atom σ s) : Oopsla16.Tm σ s := .tvar a.root

mutual

/-- A term erases to a source term.  The self annotation of a literal and
every coercion vanish. -/
def Tm.erase {σ s : Sig} : Tm σ s → Oopsla16.Tm σ s
  | .atom a => a.erase
  | .new _ ds => .tobj ds.erase
  | .app a l b => .tapp a.erase l b.erase
  | .let t u => letEncode t.erase u.erase
  | .cast t _ => t.erase

/-- A definition list erases to a source definition list, its annotations
being the ones the source's `EqSome` accepts. -/
def Defs.erase {σ s : Sig} : Defs σ s → Oopsla16.Dms σ s
  | .dnil => .dnil
  | .dty T ds => .dcons (.dty T) ds.erase
  | .dfun S U t ds => .dcons (.dfun (some S) (some U) t.erase) ds.erase

end

/-- A store erases entrywise.  This is the sharing the brief asked for: the
machine's store *is* the source's, up to this map. -/
def MachineStore.erase {σ : Sig} : {σ' : Sig} → MachineStore σ σ' → Oopsla16.Store σ σ'
  | _, .nil => .nil
  | _, .cons G ds => .cons G.erase ds.erase

/-- The source context a frame erases to: a coercion frame is the identity
context, a `let` frame is the encoding. -/
def Frame.plug {σ : Sig} : Frame σ → Oopsla16.Tm σ [] → Oopsla16.Tm σ []
  | .let u, t => letEncode t u.erase
  | .cast _, t => t

/-- The source context a continuation erases to. -/
def Cont.plug {σ : Sig} : Cont σ → Oopsla16.Tm σ [] → Oopsla16.Tm σ []
  | .nil, t => t
  | .cons K f, t => K.plug (f.plug t)

/-- The store half of a state's erasure. -/
def State.eraseStore {σ : Sig} (st : State σ) : Oopsla16.Store σ σ := st.G.erase

/-- The term half of a state's erasure: the running term in its continuation's
context. -/
def State.eraseTm {σ : Sig} (st : State σ) : Oopsla16.Tm σ [] :=
  st.K.plug st.t.erase

/-! ## Erasure commutes with the machine's substitution -/

/-- An instantiation does not move locations. -/
@[simp] theorem Inst.toSubst_conc {σ : Sig} : {s1 s2 : Sig} → (ι : Inst s1 s2) →
    (y c : BVar σ .var) → (ι.toSubst y).conc c = c
  | _, _, .base, _, _ => rfl
  | _, _, .lift ι, y, c => Inst.toSubst_conc ι y c

/-- `Vr.instAbs` is the action of the substitution the instantiation denotes. -/
@[simp] theorem Vr.instAbs_eq {σ : Sig} : {s1 s2 : Sig} → (ι : Inst s1 s2) →
    (z : BVar s1 .var) → (y : BVar σ .var) →
    Vr.instAbs ι z y = (ι.toSubst y).abs z
  | _, _, .base, .here, _ => rfl
  | _, _, .lift _, .here, _ => rfl
  | _, _, .lift ι, .there z, y => by
      show (Vr.instAbs ι z y).weaken = ((ι.toSubst y).abs z).weaken
      rw [Vr.instAbs_eq ι z y]

/-- `Vr.inst` is the action of the substitution the instantiation denotes. -/
@[simp] theorem Vr.inst_eq {σ s1 s2 : Sig} (p : Vr σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) : Vr.inst p ι y = p.subst (ι.toSubst y) := by
  cases p with
  | conc c => exact congrArg Vr.conc (Inst.toSubst_conc ι y c).symm
  | abs z => exact Vr.instAbs_eq ι z y

/-- Instantiation does not move an atom's root, beyond instantiating it. -/
@[simp] theorem Atom.root_inst {σ : Sig} : {s1 s2 : Sig} → (a : Atom σ s1) →
    (ι : Inst s1 s2) → (y : BVar σ .var) →
    (a.inst ι y).root = Vr.inst a.root ι y
  | _, _, .var _, _, _ => rfl
  | _, _, .cast a _, ι, y => Atom.root_inst a ι y
  | _, _, .pack _ a, ι, y => Atom.root_inst a ι y
  | _, _, .unpack _ a, ι, y => Atom.root_inst a ι y

/-- Erasure commutes with instantiation, at an atom. -/
@[simp] theorem Atom.erase_inst {σ s1 s2 : Sig} (a : Atom σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) : (a.inst ι y).erase = a.erase.subst (ι.toSubst y) := by
  show Oopsla16.Tm.tvar _ = Oopsla16.Tm.tvar _
  rw [Atom.root_inst, Vr.inst_eq]

mutual

/-- Erasure commutes with instantiation, at a term. -/
@[simp] theorem Tm.erase_inst {σ : Sig} : {s1 s2 : Sig} → (t : Tm σ s1) →
    (ι : Inst s1 s2) → (y : BVar σ .var) →
    (t.inst ι y).erase = t.erase.subst (ι.toSubst y)
  | _, _, .atom a, ι, y => by
      simp only [Tm.inst, Tm.erase, Atom.erase_inst]
  | _, _, .new _ ds, ι, y => by
      simp only [Tm.inst, Tm.erase, Oopsla16.Tm.subst, Defs.erase_inst ds ι.lift y]
      rfl
  | _, _, .app a l b, ι, y => by
      simp only [Tm.inst, Tm.erase, Oopsla16.Tm.subst, Atom.erase_inst]
  | _, _, .let t u, ι, y => by
      simp only [Tm.inst, Tm.erase, letEncode_subst, Tm.erase_inst t ι y,
        Tm.erase_inst u ι.lift y]
      rfl
  | _, _, .cast t _, ι, y => by
      simp only [Tm.inst, Tm.erase, Tm.erase_inst t ι y]

/-- Erasure commutes with instantiation, at a definition list. -/
@[simp] theorem Defs.erase_inst {σ : Sig} : {s1 s2 : Sig} → (ds : Defs σ s1) →
    (ι : Inst s1 s2) → (y : BVar σ .var) →
    (ds.inst ι y).erase = ds.erase.subst (ι.toSubst y)
  | _, _, .dnil, _, _ => rfl
  | _, _, .dty T ds, ι, y => by
      simp only [Defs.inst, Defs.erase, Oopsla16.Dms.subst, Oopsla16.Dm.subst,
        Defs.erase_inst ds ι y]
  | _, _, .dfun S U t ds, ι, y => by
      simp only [Defs.inst, Defs.erase, Oopsla16.Dms.subst, Oopsla16.Dm.subst,
        Option.map_some, Defs.erase_inst ds ι y, Tm.erase_inst t ι.lift y]
      rfl

end

/-! ### … and with the generated substitution

`Machine.MonoSyn.ofInst` exhibits the machine's `Inst` as one of `Subst`'s
generated substitutions, so `Subst`'s own traversal has the same laws.  The two
traversals are *not* the same function — `Machine`'s header says where and why
they differ on evidence — but the pair of results below says they agree after
erasure, which is all a runtime statement can see, and the second of each pair
is what a preservation proof will use, because it is the traversal
`SubstTyping` and `TermSubst` are stated about. -/

/-- Erasure commutes with the generated substitution, at an atom. -/
theorem Atom.erase_subst {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (a : Atom σ1 s1) (m : MonoSyn θ) : (a.subst m).erase = a.erase.subst θ := by
  show Oopsla16.Tm.tvar _ = Oopsla16.Tm.tvar _
  rw [Atom.root_subst]

mutual

/-- Erasure commutes with the generated substitution, at a term. -/
theorem Tm.erase_subst {σ1 σ2 : Sig} : {s1 s2 : Sig} →
    {θ : Subst σ1 s1 σ2 s2} → (t : Tm σ1 s1) → (m : MonoSyn θ) →
    (t.subst m).erase = t.erase.subst θ
  | _, _, _, .atom a, m => by
      simp only [Tm.subst, Tm.erase, Atom.erase_subst]
  | _, _, _, .new _ ds, m => by
      simp only [Tm.subst, Tm.erase, Oopsla16.Tm.subst, Defs.erase_subst ds m.lift]
  | _, _, _, .app a l b, m => by
      simp only [Tm.subst, Tm.erase, Oopsla16.Tm.subst, Atom.erase_subst]
  | _, _, _, .let t u, m => by
      simp only [Tm.subst, Tm.erase, letEncode_subst, Tm.erase_subst t m,
        Tm.erase_subst u m.lift]
  | _, _, _, .cast t _, m => by
      simp only [Tm.subst, Tm.erase, Tm.erase_subst t m]

/-- Erasure commutes with the generated substitution, at a definition list. -/
theorem Defs.erase_subst {σ1 σ2 : Sig} : {s1 s2 : Sig} →
    {θ : Subst σ1 s1 σ2 s2} → (ds : Defs σ1 s1) → (m : MonoSyn θ) →
    (ds.subst m).erase = ds.erase.subst θ
  | _, _, _, .dnil, _ => rfl
  | _, _, _, .dty T ds, m => by
      simp only [Defs.subst, Defs.erase, Oopsla16.Dms.subst, Oopsla16.Dm.subst,
        Defs.erase_subst ds m]
  | _, _, _, .dfun S U t ds, m => by
      simp only [Defs.subst, Defs.erase, Oopsla16.Dms.subst, Oopsla16.Dm.subst,
        Option.map_some, Defs.erase_subst ds m, Tm.erase_subst t m.lift]

end

/-- **The machine's traversal and `Subst`'s erase to the same term**, at an
atom. -/
theorem Atom.erase_inst_subst {σ s1 s2 : Sig} (a : Atom σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) :
    (a.inst ι y).erase = (a.subst (MonoSyn.ofInst ι y)).erase := by
  rw [Atom.erase_inst, Atom.erase_subst]

/-- The same, at a term.  This is the sense in which the machine's `rename`,
`alloc` and `app` rules perform the substitution `TermSubst.TmTy.substEv` is
stated about. -/
theorem Tm.erase_inst_subst {σ s1 s2 : Sig} (t : Tm σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) :
    (t.inst ι y).erase = (t.subst (MonoSyn.ofInst ι y)).erase := by
  rw [Tm.erase_inst, Tm.erase_subst]

/-- The same, at a definition list. -/
theorem Defs.erase_inst_subst {σ s1 s2 : Sig} (ds : Defs σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) :
    (ds.inst ι y).erase = (ds.subst (MonoSyn.ofInst ι y)).erase := by
  rw [Defs.erase_inst, Defs.erase_subst]

/-! ## Erasure commutes with allocation's store weakening -/

/-- Renaming the store does not move an atom's root, beyond renaming it. -/
@[simp] theorem Atom.root_renameStore : {σ1 σ2 s : Sig} →
    (a : Atom σ1 s) → (ρ : Rename σ1 σ2) →
    (a.renameStore ρ).root = a.root.subst (Subst.ofStore ρ)
  | _, _, _, .var _, _ => rfl
  | _, _, _, .cast a _, ρ => Atom.root_renameStore a ρ
  | _, _, _, .pack _ a, ρ => Atom.root_renameStore a ρ
  | _, _, _, .unpack _ a, ρ => Atom.root_renameStore a ρ

/-- Erasure commutes with store renaming, at an atom. -/
@[simp] theorem Atom.erase_renameStore {σ1 σ2 s : Sig} (a : Atom σ1 s)
    (ρ : Rename σ1 σ2) :
    (a.renameStore ρ).erase = a.erase.subst (Subst.ofStore ρ) := by
  show Oopsla16.Tm.tvar _ = Oopsla16.Tm.tvar _
  rw [Atom.root_renameStore]

/-- A store renaming is unchanged by lifting: it does not touch the local
scope. -/
@[simp] theorem Subst.lift_ofStore {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) :
    (Subst.ofStore (s := s) ρ).lift = Subst.ofStore ρ := by
  apply Subst.ext <;> intro z
  · rfl
  · cases z <;> rfl

mutual

/-- Erasure commutes with store renaming, at a term. -/
@[simp] theorem Tm.erase_renameStore : {σ1 σ2 s : Sig} → (t : Tm σ1 s) →
    (ρ : Rename σ1 σ2) →
    (t.renameStore ρ).erase = t.erase.subst (Subst.ofStore ρ)
  | _, _, _, .atom a, ρ => by
      simp only [Tm.renameStore, Tm.erase, Atom.erase_renameStore]
  | _, _, _, .new _ ds, ρ => by
      simp only [Tm.renameStore, Tm.erase, Oopsla16.Tm.subst, Subst.lift_ofStore,
        Defs.erase_renameStore ds ρ]
  | _, _, _, .app a l b, ρ => by
      simp only [Tm.renameStore, Tm.erase, Oopsla16.Tm.subst,
        Atom.erase_renameStore]
  | _, _, _, .let t u, ρ => by
      simp only [Tm.renameStore, Tm.erase, letEncode_subst, Subst.lift_ofStore,
        Tm.erase_renameStore t ρ, Tm.erase_renameStore u ρ]
  | _, _, _, .cast t _, ρ => by
      simp only [Tm.renameStore, Tm.erase, Tm.erase_renameStore t ρ]

/-- Erasure commutes with store renaming, at a definition list. -/
@[simp] theorem Defs.erase_renameStore : {σ1 σ2 s : Sig} →
    (ds : Defs σ1 s) → (ρ : Rename σ1 σ2) →
    (ds.renameStore ρ).erase = ds.erase.subst (Subst.ofStore ρ)
  | _, _, _, .dnil, _ => rfl
  | _, _, _, .dty T ds, ρ => by
      simp only [Defs.renameStore, Defs.erase, Oopsla16.Dms.subst,
        Oopsla16.Dm.subst, Defs.erase_renameStore ds ρ]
  | _, _, _, .dfun S U t ds, ρ => by
      simp only [Defs.renameStore, Defs.erase, Oopsla16.Dms.subst,
        Oopsla16.Dm.subst, Option.map_some, Subst.lift_ofStore,
        Defs.erase_renameStore ds ρ, Tm.erase_renameStore t ρ]

end

/-- Erasure commutes with store renaming, at a store. -/
@[simp] theorem MachineStore.erase_renameStore : {σ1 σ2 σ3 : Sig} →
    (G : MachineStore σ1 σ3) → (ρ : Rename σ1 σ2) →
    (G.renameStore ρ).erase = G.erase.renameStore ρ
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons G ds, ρ => by
      simp only [MachineStore.renameStore, MachineStore.erase, Oopsla16.Store.renameStore,
        MachineStore.erase_renameStore G ρ, Defs.erase_renameStore ds ρ]

/-- Erasure commutes with lookup. -/
@[simp] theorem MachineStore.erase_lookup {σ : Sig} : {σ' : Sig} → (G : MachineStore σ σ') →
    (z : BVar σ' .var) → (G.lookup z).erase = G.erase.lookup z
  | _, .cons _ _, .here => rfl
  | _, .cons G _, .there z => MachineStore.erase_lookup G z

/-- Erasure preserves the number of members, hence every label. -/
@[simp] theorem Defs.erase_length {σ s : Sig} : (ds : Defs σ s) →
    ds.erase.length = ds.length
  | .dnil => rfl
  | .dty _ ds => congrArg (· + 1) (Defs.erase_length ds)
  | .dfun _ _ _ ds => congrArg (· + 1) (Defs.erase_length ds)

/-- A method of the machine's store is the method the source reads at the same
label. -/
theorem Defs.erase_fun? {σ s : Sig} : (ds : Defs σ s) → (l : Lb) →
    {S : Ty σ s} → {U : Ty σ (s,x)} → {t : Tm σ (s,x)} →
    ds.fun? l = some (S, U, t) →
    ds.erase.get? l = some (.dfun (some S) (some U) t.erase)
  | .dnil, _, _, _, _, h => by cases h
  | .dty _ ds, l, _, _, _, h => by
      simp only [Defs.fun?] at h
      split at h
      · cases h
      · rename_i hne
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, hne,
          if_false, Defs.erase_fun? ds l h]
  | .dfun S U t ds, l, _, _, _, h => by
      simp only [Defs.fun?] at h
      split at h
      · rename_i heq
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, heq,
          if_true]
        cases h
        rfl
      · rename_i hne
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, hne,
          if_false, Defs.erase_fun? ds l h]

/-- A type member survives erasure **unchanged** — the type translation is the
identity — so `LeTy.defL` and `LeTy.defR`, which read the *source* store, read
exactly the members the machine's store holds.  That is the sense in which the
two stores are one. -/
theorem Defs.erase_ty? {σ s : Sig} : (ds : Defs σ s) → (l : Lb) →
    {T : Ty σ s} → ds.ty? l = some T →
    ds.erase.get? l = some (.dty T)
  | .dnil, _, _, h => by cases h
  | .dty T ds, l, _, h => by
      simp only [Defs.ty?] at h
      split at h
      · rename_i heq
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, heq, if_true]
        cases h
        rfl
      · rename_i hne
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, hne,
          if_false, Defs.erase_ty? ds l h]
  | .dfun _ _ _ ds, l, _, h => by
      simp only [Defs.ty?] at h
      split at h
      · cases h
      · rename_i hne
        simp only [Defs.erase, Oopsla16.Dms.get?, Defs.erase_length, hne,
          if_false, Defs.erase_ty? ds l h]

/-! ## The simulation -/

/-- Continuations of coercion frames only.  They erase to the identity
context, which is what makes a machine step visible to the source. -/
def Cont.Evidential {σ : Sig} : Cont σ → Prop
  | .nil => True
  | .cons K (.cast _) => K.Evidential
  | .cons _ (.let _) => False

/-- A coercion-only continuation is the identity context. -/
theorem Cont.plug_of_evidential {σ : Sig} : (K : Cont σ) → K.Evidential →
    (t : Oopsla16.Tm σ []) → K.plug t = t
  | .nil, _, _ => rfl
  | .cons K (.cast _), h, t => Cont.plug_of_evidential K h t
  | .cons _ (.let _), h, _ => absurd h (by simp [Cont.Evidential])

/-- Allocation preserves being coercion-only. -/
theorem Cont.evidential_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    (K : Cont σ1) → K.Evidential → (K.renameStore ρ).Evidential
  | .nil, _ => trivial
  | .cons K (.cast _), h => Cont.evidential_renameStore ρ K h
  | .cons _ (.let _), h => absurd h (by simp [Cont.Evidential])

/-- **A machine step erases to zero or one source step**, at the same `Grows`
index: zero for `let`, `castPush` and `castAtom`, one for `alloc` (`ST_Obj`)
and `app` (`ST_AppAbs`).

The hypothesis is that the continuation holds no `let` frame.  It is what
excludes `rename`, the one rule the encoding of `let` cannot follow, and it
holds throughout the run of a `let`-free term. -/
theorem Step.simulate {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} (h : Step g st st') (hK : st.K.Evidential) :
    Oopsla16.Steps g st.eraseStore st.eraseTm st'.eraseStore st'.eraseTm := by
  cases h with
  | «let» => exact .refl
  | castPush => exact .refl
  | castAtom => exact .refl
  | rename => exact absurd hK (by simp [Cont.Evidential])
  | @alloc G K T ds =>
      refine Oopsla16.Steps.tail (g := .refl) (h := .snoc .refl) .refl ?_
      rw [show (State.eraseTm ⟨G, K, .new T ds⟩) = .tobj ds.erase from
            Cont.plug_of_evidential K hK _,
          show (State.eraseTm ⟨G.weakenStore.cons (ds.weakenStore.inst .base .here),
              K.weakenStore, .atom (.var (.conc .here))⟩) = .tvar (.conc .here) from
            Cont.plug_of_evidential _ (Cont.evidential_renameStore _ K hK) _,
          show (State.eraseStore ⟨G.weakenStore.cons (ds.weakenStore.inst .base .here),
              K.weakenStore, .atom (.var (.conc .here))⟩)
            = G.erase.weakenStore.cons (ds.erase.weakenStore.substVr (.conc .here)) from by
            simp only [State.eraseStore, MachineStore.erase, MachineStore.erase_renameStore,
              Defs.erase_inst, Defs.erase_renameStore]
            rfl]
      exact .ST_Obj
  | @app G K a b l S U t hf =>
      refine Oopsla16.Steps.tail (g := .refl) (h := .refl) .refl ?_
      have e1 : (State.eraseTm ⟨G, K, .app a l b⟩)
          = .tapp (.tvar (.conc (Vr.loc a.root))) l
              (.tvar (.conc (Vr.loc b.root))) := by
        show K.plug (Tm.erase (.app a l b)) = _
        rw [Cont.plug_of_evidential K hK]
        simp only [Tm.erase, Atom.erase, Vr.conc_loc]
      have e2 : (State.eraseTm ⟨G, K, t.inst .base (Vr.loc b.root)⟩)
          = t.erase.substVr (.conc (Vr.loc b.root)) := by
        show K.plug (Tm.erase (t.inst .base (Vr.loc b.root))) = _
        rw [Cont.plug_of_evidential K hK]
        exact Tm.erase_inst t .base _
      rw [e1, e2]
      exact .ST_AppAbs (MachineStore.erase_lookup G (Vr.loc a.root)
        ▸ Defs.erase_fun? (G.lookup (Vr.loc a.root)) l hf)

/-! ## The let-free fragment

The hypothesis of `Step.simulate` is a property of one state.  What makes it
the *fragment* it is called is that it is preserved: a state whose term, store
and continuation hold no `let` steps to another such state.  So on that
fragment the simulation iterates, which is `Steps.simulate`. -/

mutual

/-- Terms with no `let`.  Atoms and evidence cannot contain one. -/
def Tm.LetFree {σ : Sig} : {s : Sig} → Tm σ s → Prop
  | _, .atom _ => True
  | _, .new _ ds => ds.LetFree
  | _, .app _ _ _ => True
  | _, .let _ _ => False
  | _, .cast t _ => t.LetFree

/-- Definition lists whose method bodies have no `let`. -/
def Defs.LetFree {σ : Sig} : {s : Sig} → Defs σ s → Prop
  | _, .dnil => True
  | _, .dty _ ds => ds.LetFree
  | _, .dfun _ _ t ds => t.LetFree ∧ ds.LetFree

end

mutual

/-- Instantiation introduces no `let`. -/
theorem Tm.letFree_inst {σ : Sig} : {s1 s2 : Sig} → (t : Tm σ s1) →
    (ι : Inst s1 s2) → (y : BVar σ .var) → t.LetFree → (t.inst ι y).LetFree
  | _, _, .atom _, _, _, _ => trivial
  | _, _, .new _ ds, ι, y, h => Defs.letFree_inst ds ι.lift y h
  | _, _, .app _ _ _, _, _, _ => trivial
  | _, _, .let _ _, _, _, h => h.elim
  | _, _, .cast t _, ι, y, h => Tm.letFree_inst t ι y h

/-- Instantiation introduces no `let`, in a definition list. -/
theorem Defs.letFree_inst {σ : Sig} : {s1 s2 : Sig} → (ds : Defs σ s1) →
    (ι : Inst s1 s2) → (y : BVar σ .var) → ds.LetFree → (ds.inst ι y).LetFree
  | _, _, .dnil, _, _, _ => trivial
  | _, _, .dty _ ds, ι, y, h => Defs.letFree_inst ds ι y h
  | _, _, .dfun _ _ t ds, ι, y, h =>
      ⟨Tm.letFree_inst t ι.lift y h.1, Defs.letFree_inst ds ι y h.2⟩

end

mutual

/-- Allocation's weakening introduces no `let`. -/
theorem Tm.letFree_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (t : Tm σ1 s) → t.LetFree → (t.renameStore ρ).LetFree
  | _, .atom _, _ => trivial
  | _, .new _ ds, h => Defs.letFree_renameStore ρ ds h
  | _, .app _ _ _, _ => trivial
  | _, .let _ _, h => h.elim
  | _, .cast t _, h => Tm.letFree_renameStore ρ t h

/-- Allocation's weakening introduces no `let`, in a definition list. -/
theorem Defs.letFree_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (ds : Defs σ1 s) → ds.LetFree → (ds.renameStore ρ).LetFree
  | _, .dnil, _ => trivial
  | _, .dty _ ds, h => Defs.letFree_renameStore ρ ds h
  | _, .dfun _ _ t ds, h =>
      ⟨Tm.letFree_renameStore ρ t h.1, Defs.letFree_renameStore ρ ds h.2⟩

end

/-- Stores whose objects have no `let` in a method body. -/
def MachineStore.LetFree {σ : Sig} : {σ' : Sig} → MachineStore σ σ' → Prop
  | _, .nil => True
  | _, .cons G ds => G.LetFree ∧ ds.LetFree

/-- A stored object of a `let`-free store is `let`-free. -/
theorem MachineStore.letFree_lookup {σ : Sig} : {σ' : Sig} → (G : MachineStore σ σ') →
    (z : BVar σ' .var) → G.LetFree → (G.lookup z).LetFree
  | _, .cons _ _, .here, h => h.2
  | _, .cons G _, .there z, h => MachineStore.letFree_lookup G z h.1

/-- Allocation's weakening preserves a `let`-free store. -/
theorem MachineStore.letFree_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {σ3 : Sig} → (G : MachineStore σ1 σ3) → G.LetFree → (G.renameStore ρ).LetFree
  | _, .nil, _ => trivial
  | _, .cons G ds, h =>
      ⟨MachineStore.letFree_renameStore ρ G h.1, Defs.letFree_renameStore ρ ds h.2⟩

/-- A method of a `let`-free definition list has a `let`-free body. -/
theorem Defs.letFree_fun? {σ s : Sig} : (ds : Defs σ s) → (l : Lb) →
    {S : Ty σ s} → {U : Ty σ (s,x)} → {t : Tm σ (s,x)} → ds.LetFree →
    ds.fun? l = some (S, U, t) → t.LetFree
  | .dnil, _, _, _, _, _, hf => by cases hf
  | .dty _ ds, l, _, _, _, h, hf => by
      simp only [Defs.fun?] at hf
      split at hf
      · cases hf
      · exact Defs.letFree_fun? ds l h hf
  | .dfun _ _ t ds, l, _, _, _, h, hf => by
      simp only [Defs.fun?] at hf
      split at hf
      · cases hf; exact h.1
      · exact Defs.letFree_fun? ds l h.2 hf

/-- The states the simulation iterates on: no `let` anywhere, so no `let`
frame is ever pushed and the continuation stays a stack of coercions. -/
def State.LetFree {σ : Sig} (st : State σ) : Prop :=
  st.K.Evidential ∧ st.t.LetFree ∧ st.G.LetFree

/-- The fragment is closed under stepping. -/
theorem Step.letFree {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} (h : Step g st st') (hL : st.LetFree) : st'.LetFree := by
  obtain ⟨hK, ht, hG⟩ := hL
  cases h with
  | «let» => exact ht.elim
  | castPush => exact ⟨hK, ht, hG⟩
  | castAtom => exact ⟨hK, trivial, hG⟩
  | rename => exact hK.elim
  | @alloc G K _ ds =>
      exact ⟨Cont.evidential_renameStore _ K hK, trivial,
        MachineStore.letFree_renameStore _ G hG,
        Defs.letFree_inst _ .base .here (Defs.letFree_renameStore _ ds ht)⟩
  | @app G _ _ _ l _ _ t hf =>
      exact ⟨hK, Tm.letFree_inst t .base _
        (Defs.letFree_fun? _ l (MachineStore.letFree_lookup G _ hG) hf), hG⟩

/-- A run stays in the fragment. -/
theorem Steps.letFree {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} (h : Steps g st st') (hL : st.LetFree) : st'.LetFree := by
  induction h with
  | refl => exact hL
  | tail _ hstep ih => exact hstep.letFree (ih hL)

/-- Growth composition is associative.  `Oopsla16.Semantics` defines `comp`
but not this law, and concatenating two source runs needs it. -/
theorem growsCompAssoc {σ1 σ2 σ3 : Sig} (g : Grows σ1 σ2) (h : Grows σ2 σ3) :
    {σ4 : Sig} → (k : Grows σ3 σ4) → (g.comp h).comp k = g.comp (h.comp k)
  | _, .refl => rfl
  | _, .snoc k => congrArg Grows.snoc (growsCompAssoc g h k)

/-- Source runs concatenate. -/
theorem srcStepsTrans {σ1 : Sig} {G1 : Oopsla16.Store σ1 σ1}
    {t1 : Oopsla16.Tm σ1 []} : {σ2 σ3 : Sig} → {g : Grows σ1 σ2} →
    {h : Grows σ2 σ3} → {G2 : Oopsla16.Store σ2 σ2} → {t2 : Oopsla16.Tm σ2 []} →
    {G3 : Oopsla16.Store σ3 σ3} → {t3 : Oopsla16.Tm σ3 []} →
    Oopsla16.Steps g G1 t1 G2 t2 → Oopsla16.Steps h G2 t2 G3 t3 →
    Oopsla16.Steps (g.comp h) G1 t1 G3 t3 := by
  intro σ2 σ3 g h G2 t2 G3 t3 h1 h2
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih =>
      have hc := Oopsla16.Steps.tail (ih h1) hstep
      rwa [growsCompAssoc] at hc

/-- **A `let`-free run erases to a source run**, at the same `Grows` index.
This is `Step.simulate` iterated: the fragment is closed under stepping, so
the continuation never acquires a `let` frame. -/
theorem Steps.simulate {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} (h : Steps g st st') (hL : st.LetFree) :
    Oopsla16.Steps g st.eraseStore st.eraseTm st'.eraseStore st'.eraseTm := by
  induction h with
  | refl => exact .refl
  | tail hs hstep ih =>
      exact srcStepsTrans (ih hL) (hstep.simulate (hs.letFree hL).1)

/-! ## The counterexample store, as a program that builds it

`Oopsla16.PackingCounterexample` is stated over a *given* two-object store.
Here is a closed FCdotR program that allocates that store and then runs to the
stuck term, with `p` and `q` landing at the very locations the counterexample
names.  Nothing about it is typed: it is a runtime statement, and the
counterexample's own typing derivations are the source's. -/

namespace Counterexample

open Oopsla16.PackingCounterexample (A B C K missing S2 p q)

/-- The self of the object being allocated, seen from inside a `TBind` that
ignores its own binder. -/
abbrev selfUnder {σ s : Sig} : Vr σ ((s,x),x) := .abs (.there .here)

/-- `p.B`, with `p` the self of the literal being allocated. -/
abbrev selfB {σ s : Sig} : Ty σ (s,x) := .TSel (.abs .here) B
/-- `p.C`, with `p` the self of the literal being allocated. -/
abbrev selfC {σ s : Sig} : Ty σ (s,x) := .TSel (.abs .here) C

/-- `D = μ _. p.B`, the recursive type whose body ignores its self. -/
abbrev selfD {σ s : Sig} : Ty σ (s,x) := .TBind (.TSel selfUnder B)
/-- `D' = μ _. p.C`. -/
abbrev selfD' {σ s : Sig} : Ty σ (s,x) := .TBind (.TSel selfUnder C)

/-- The body of `p.B`: `{A : D .. D'}`. -/
abbrev bBody {σ s : Sig} : Ty σ (s,x) := .TTyp A selfD selfD'
/-- The body of `p.C`: the bad-bounds member, a method `q` will not have, and
bottom. -/
abbrev cBody {σ s : Sig} : Ty σ (s,x) :=
  .TAnd (.TTyp K selfB selfC) (.TAnd (.TFun missing .TTop .TTop) .TBot)

/-- `p`'s definitions: `B` at label `0`, `C` at label `1`. -/
abbrev pDefs {σ s : Sig} : Defs σ (s,x) := .dty cBody (.dty bBody .dnil)

/-- `p`'s self type, the intersection its definitions have. -/
abbrev pType {σ s : Sig} : Ty σ (s,x) :=
  .TAnd (.TTyp C cBody cBody) (.TAnd (.TTyp B bBody bBody) .TTop)

/-- `D = μ _. p.B` seen from inside `q`'s literal, where `p` is a variable of
the scope the literal is allocated in: one weakening for `q`'s self, one for
the recursive binder the body ignores. -/
abbrev dAt {σ s : Sig} (pv : Vr σ s) : Ty σ (s,x) :=
  .TBind (.TSel pv.weaken.weaken B)

/-- `q`'s single definition, `A = D`, where `D` mentions the already allocated
`p` — which, in the program, is the enclosing `let`'s variable. -/
abbrev qDefs {σ s : Sig} (pv : Vr σ s) : Defs σ (s,x) := .dty (dAt pv) .dnil

/-- `q`'s self type. -/
abbrev qType {σ s : Sig} (pv : Vr σ s) : Ty σ (s,x) :=
  .TAnd (.TTyp A (dAt pv) (dAt pv)) .TTop

/-- The stuck term: invoke on `q` a method `q` does not have.  Both operands
are the newest `let` variable. -/
abbrev badTm {σ : Sig} : Tm σ (([],x),x) :=
  .app (.var (.abs .here)) missing (.var (.abs .here))

/-- The program: allocate `p`, allocate `q`, then invoke. -/
abbrev prog : Tm [] [] :=
  .let (.new pType pDefs)
    (.let (.new (qType (.abs .here)) (qDefs (.abs .here))) badTm)

/-- The initial state. -/
abbrev initState : State [] := ⟨.nil, .nil, prog⟩

/-- **The run.**  The program allocates both objects and reaches a state that

* erases, store and term, to exactly the configuration
  `Oopsla16.PackingCounterexample` is stated over — `p` and `q` land at the
  locations that module names, and the two runtime checks are kernel `rfl`s;
* is stuck, and whose erasure is stuck too (`badTerm_stuck`);
* is in the `let`-free fragment, so `Steps.simulate` applies from it onwards.

The *program* is not in that fragment: allocating two objects needs two `let`s,
and those are the steps the source encoding cannot follow.  What the run shows
is that the machine nonetheless arrives at the source's own stuck
configuration. -/
theorem badRun :
    ∃ (g : Grows [] S2) (st : State S2),
      Steps g initState st ∧
      st.eraseStore = Oopsla16.PackingCounterexample.G ∧
      st.eraseTm = Oopsla16.PackingCounterexample.badTerm ∧
      st.Stuck ∧ st.LetFree ∧
      ¬ ∃ (σ' : Sig) (g' : Grows S2 σ') (G' : Oopsla16.Store σ' σ')
          (t' : Oopsla16.Tm σ' []),
          Oopsla16.Step g' st.eraseStore st.eraseTm G' t' := by
  have h1 := Steps.tail (Steps.refl (st := initState)) Step.«let»
  have h2 := Steps.tail h1 Step.alloc
  have h3 := Steps.tail h2 Step.rename
  have h4 := Steps.tail h3 Step.«let»
  have h5 := Steps.tail h4 Step.alloc
  have h6 := Steps.tail h5 Step.rename
  refine ⟨_, _, h6, rfl, rfl, ⟨?_, ?_⟩, ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial⟩,
    Oopsla16.PackingCounterexample.badTerm_stuck⟩
  · rintro ⟨-, a, ha⟩
    exact absurd ha (by
      show ¬ (Tm.app _ _ _ = Tm.atom a)
      intro h
      cases h)
  · rintro ⟨σ', g, st', hstep⟩
    cases hstep with
    | app hf =>
        rw [show ((MachineStore.lookup _ _).fun? missing) = none from rfl] at hf
        cases hf

end Counterexample

end FCdotR
