import Coercions.CapturesCC.FCdot.Erasure
import Coercions.CapturesCC.FCdot.CanonicalForms

namespace CapturesCC

/-!
# Erasure metatheory: FCdot against the shared runtime

The erasure of `Erasure.lean` is a simulation between the FCdot store
machine of `Machine.lean` and the untyped runtime of `Runtime.lean`.

* `erase_step`: every FCdot step either is a cast-frame shuffle, which the
  erasure does not see, or erases to exactly one runtime step.
* `erase_reflect`: every runtime step out of an erased state is realized by
  a nonempty run of the FCdot machine, after finitely many cast-frame steps.
* `final_erase` / `final_reflect`: final states correspond, up to a pending
  cast frame.

`Store.Typed` enters only to know that store entries are literals, which is
what makes the reflection of `app` and `proj` steps possible.  Reflection of
an application through a *wrapped* atom additionally needs that the head
normalization of the atom's casts succeeds with an identity, a conversion,
or a function form; that is the canonical-forms theorem, which lives
elsewhere, so `erase_reflect` takes it as an explicit hypothesis `hcf`.
-/

/-! ## Runtime lemmas -/

namespace Runtime

open FCdot (Kind Sig BVar Rename Label)

/-! ### Renaming by the identity -/

mutual

theorem Tm.rename_id {s : Sig} (t : Tm s) : t.rename Rename.id = t := by
  match t with
  | .var x => simp [Tm.rename]
  | .lam t => simp [Tm.rename, Rename.lift_id, Tm.rename_id t]
  | .obj F => simp [Tm.rename, Rename.lift_id, Fields.rename_id F]
  | .app x y => simp [Tm.rename]
  | .proj x ℓ => simp [Tm.rename]
  | .let t u => simp [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | .letex t u => simp [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | .box x => simp [Tm.rename]
  | .unbox x => simp [Tm.rename]

theorem Fields.rename_id {s : Sig} (F : Fields s) : F.rename Rename.id = F := by
  match F with
  | .nil => simp [Fields.rename]
  | .cons F ℓ t => simp [Fields.rename, Fields.rename_id F, Tm.rename_id t]

end

/-! ### Inversions of the runtime step relation

Each inversion is stated in continuation-passing form: the successor state
is determined, so any predicate holding of it holds of the actual successor.
This avoids transporting states along the signature equation. -/

theorem Step.let_inv {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {u : Tm (s,x)}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .let t u⟩ r) (hm : motive s ⟨σ, .cons K u, t⟩) : motive s' r := by
  cases h with
  | «let» => exact hm
  | alloc hv => cases hv
  | allocE hv => cases hv

theorem Step.app_inv {s s' : Sig} {σ : Store s} {K : Cont s} {x y : BVar s .var}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .app x y⟩ r)
    (hm : ∀ t, σ.lookup x = .lam t → motive s ⟨σ, K, t.map (VRen.enter y)⟩) : motive s' r := by
  cases h with
  | app hl => exact hm _ hl
  | alloc hv => cases hv
  | allocE hv => cases hv

theorem Step.proj_inv {s s' : Sig} {σ : Store s} {K : Cont s} {x : BVar s .var} {ℓ : Label}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .proj x ℓ⟩ r)
    (hm : ∀ F t, σ.lookup x = .obj F → F.get? ℓ = some t →
      motive s ⟨σ, K, t.map (VRen.enterObj x)⟩) : motive s' r := by
  cases h with
  | proj hl hg => exact hm _ _ hl hg
  | alloc hv => cases hv
  | allocE hv => cases hv

/-- Inversion of the runtime `unbox` step, in the same continuation-passing
form as `app_inv` and `proj_inv`: the only step out of an unboxing reads a
box at the receiver and continues at its content. -/
theorem Step.unbox_inv {s s' : Sig} {σ : Store s} {K : Cont s} {x : BVar s .var}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .unbox x⟩ r)
    (hm : ∀ y, σ.lookup x = .box y → motive s ⟨σ, K, .var y⟩) : motive s' r := by
  cases h with
  | unbox hl => exact hm _ hl
  | alloc hv => cases hv
  | allocE hv => cases hv

theorem Step.var_cons_inv {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm (s,x)}
    {y : BVar s .var} {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, .cons K u, .var y⟩ r) (hm : motive s ⟨σ, K, u.substVar y⟩) :
    motive s' r := by
  cases h with
  | rename => exact hm
  | alloc hv => cases hv

theorem Step.var_nil_inv {s s' : Sig} {σ : Store s} {y : BVar s .var} {r : State s'}
    (h : Step ⟨σ, .nil, .var y⟩ r) : False := by
  cases h

theorem Step.value_cons_inv {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm (s,x)}
    {v : Tm s} {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (hv : IsValue v) (h : Step ⟨σ, .cons K u, v⟩ r)
    (hm : motive (s,x) ⟨.cons σ v, K.weaken, u⟩) : motive s' r := by
  cases h with
  | alloc => exact hm
  | «let» => cases hv
  | letex => cases hv
  | app => cases hv
  | proj => cases hv
  | rename => cases hv
  | unbox => cases hv

theorem Step.value_nil_inv {s s' : Sig} {σ : Store s} {v : Tm s} {r : State s'}
    (hv : IsValue v) (h : Step ⟨σ, .nil, v⟩ r) : False := by
  cases h <;> cases hv

/-! ### Inversions of the three unpacking steps

One per new step, in the same continuation-passing form.  The unpacking
frame is a constructor of its own, so a step out of a state whose frame is
`cons` never matches one of these, and the reverse. -/

theorem Step.letex_inv {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {u : Tm ((s,c),x)}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .letex t u⟩ r) (hm : motive s ⟨σ, .consE K u, t⟩) : motive s' r := by
  cases h with
  | letex => exact hm
  | alloc hv => cases hv
  | allocE hv => cases hv

theorem Step.var_consE_inv {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm ((s,c),x)}
    {y : BVar s .var} {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, .consE K u, .var y⟩ r)
    (hm : motive (s,c) ⟨σ.consC, Cont.weaken (k := .cap) K, u.substVar (.there y)⟩) :
    motive s' r := by
  cases h with
  | unpack => exact hm
  | allocE hv => cases hv

theorem Step.value_consE_inv {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm ((s,c),x)}
    {v : Tm s} {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (hv : IsValue v) (h : Step ⟨σ, .consE K u, v⟩ r)
    (hm : motive ((s,c),x) ⟨(σ.consC).cons (Tm.weaken (k := .cap) v),
      Cont.weaken (Cont.weaken (k := .cap) K), u⟩) : motive s' r := by
  cases h with
  | allocE => exact hm
  | «let» => cases hv
  | letex => cases hv
  | app => cases hv
  | proj => cases hv
  | unpack => cases hv
  | unbox => cases hv

end Runtime

namespace FCdot

/-! ## Commutation of erasure with renaming -/

mutual

/-- Erasure commutes with renaming. -/
theorem Tm.erase_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).erase = t.erase.rename ρ := by
  match t with
  | .atom a => simp [Tm.rename, Tm.erase, Runtime.Tm.rename]
  | .val v => simp [Tm.rename, Tm.erase, Value.erase_rename v]
  | .app a b => simp [Tm.rename, Tm.erase, Runtime.Tm.rename]
  | .proj a ℓ _ => simp [Tm.rename, Tm.erase, Runtime.Tm.rename]
  | .let t u U f =>
      simp [Tm.rename, Tm.erase, Runtime.Tm.rename, Tm.erase_rename t, Tm.erase_rename u]
  | .cast t e => simp [Tm.rename, Tm.erase, Tm.erase_rename t]
  | .castE t g => simp [Tm.rename, Tm.erase, Tm.erase_rename t]
  | .letex t u U hh f =>
      simp [Tm.rename, Tm.erase, Runtime.Tm.rename, Tm.erase_rename t, Tm.erase_rename u]
  | .unbox a U f => simp [Tm.rename, Tm.erase, Runtime.Tm.rename, Atom.root_rename]

theorem Value.erase_rename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    (v.rename ρ).erase = v.erase.rename ρ := by
  match v with
  | .lam A S t g => simp [Value.rename, Value.erase, Runtime.Tm.rename, Tm.erase_rename t]
  | .obj A W Wc F =>
      simp [Value.rename, Value.erase, Runtime.Tm.rename, Fields.erase_rename F]
  | .box a => simp [Value.rename, Value.erase, Runtime.Tm.rename, Atom.root_rename]
  | .pack C h e v => simp [Value.rename, Value.erase, Value.erase_rename v]
  | .cast v e => simp [Value.rename, Value.erase, Value.erase_rename v]

theorem Fields.erase_rename {s1 s2 : Sig} (F : Fields s1) (ρ : Rename s1 s2) :
    (F.rename ρ).erase = F.erase.rename ρ := by
  match F with
  | .nil => simp [Fields.rename, Fields.erase, Runtime.Fields.rename]
  | .cons F ℓ t g =>
      simp [Fields.rename, Fields.erase, Runtime.Fields.rename, Fields.erase_rename F,
        Tm.erase_rename t]

end

/-- Erasure commutes with weakening of terms. -/
theorem Tm.erase_weaken {s : Sig} (t : Tm s) :
    (t.weaken (k := .var)).erase = t.erase.weaken := by
  simp [Tm.weaken, Runtime.Tm.weaken, Tm.erase_rename]

/-- Erasure commutes with weakening of values. -/
theorem Value.erase_weaken {s : Sig} {k : Kind} (v : Value s) :
    (v.weaken (k := k)).erase = v.erase.weaken := by
  simp [Value.weaken, Runtime.Tm.weaken, Value.erase_rename]

/-- Erasure commutes with renaming of continuations; cast frames vanish. -/
theorem Cont.erase_rename {s1 s2 : Sig} :
    ∀ (K : Cont s1) (ρ : Rename s1 s2), (K.rename ρ).erase = K.erase.rename ρ
  | .nil, ρ => by simp [Cont.rename, Cont.erase, Runtime.Cont.rename]
  | .cons K (.let u U f), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Runtime.Cont.rename,
        Cont.erase_rename K, Tm.erase_rename]
  | .cons K (.cast e), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Cont.erase_rename K]
  | .cons K (.castE g), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Cont.erase_rename K]
  | .cons K (.letex u U hh f), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Runtime.Cont.rename,
        Cont.erase_rename K, Tm.erase_rename]

/-- Erasure commutes with weakening of continuations. -/
theorem Cont.erase_weaken {s : Sig} (K : Cont s) : K↑.erase = K.erase.weaken := by
  simp [Cont.weaken, Runtime.Cont.weaken, Cont.erase_rename]

/-- The capture-kind twin, beside its term twin for the reason
`Cont.weakenC` sits beside `Cont.weaken`: the unpacking steps weaken a
continuation into the scope the unpacked binder opens. -/
theorem Cont.erase_weakenC {s : Sig} (K : Cont s) :
    K.weakenC.erase = Runtime.Cont.weaken (k := .cap) K.erase := by
  simp [Cont.weakenC, Runtime.Cont.weaken, Cont.erase_rename]

/-! ## Commutation of erasure with substitution

An atom erases to its root variable, and a capture atom has no runtime
content at all, so substituting erases to the map of term variables the
substitution induces on roots.  The vanilla line read the right side as a
renaming.  A substitution is no longer kind preserving, so the right side is
`Runtime.Tm.map` at `Subst.rootVar`, which is the same map of the same
variables. -/

theorem Subst.rootVar_lift {s1 s2 : Sig} (σ : Subst s1 s2) :
    σ.lift.rootVar = Runtime.VRen.lift σ.rootVar := by
  funext z
  cases z with
  | here => rfl
  | there z => exact Subst.lift_rootVar_there σ z

theorem Subst.rootVar_liftC {s1 s2 : Sig} (σ : Subst s1 s2) :
    σ.liftC.rootVar = Runtime.VRen.liftC σ.rootVar := by
  funext z
  cases z with
  | there z => exact Subst.liftC_rootVar_there σ z

mutual

/-- Erasure turns substitution into the map of roots. -/
theorem Tm.erase_subst {s1 s2 : Sig} (t : Tm s1) (σ : Subst s1 s2) :
    (t.subst σ).erase = t.erase.map σ.rootVar := by
  match t with
  | .atom p => simp [Tm.subst, Tm.erase, Runtime.Tm.map, PAtom.root_subst]
  | .val v => simp [Tm.subst, Tm.erase, Value.erase_subst v]
  | .app a b => simp [Tm.subst, Tm.erase, Runtime.Tm.map, Atom.root_subst]
  | .proj a ℓ _ => simp [Tm.subst, Tm.erase, Runtime.Tm.map, Atom.root_subst]
  | .let t u U f =>
      simp [Tm.subst, Tm.erase, Runtime.Tm.map, Tm.erase_subst t, Tm.erase_subst u,
        Subst.rootVar_lift]
  | .cast t e => simp [Tm.subst, Tm.erase, Tm.erase_subst t]
  | .castE t g => simp [Tm.subst, Tm.erase, Tm.erase_subst t]
  | .letex t u U hh f =>
      simp [Tm.subst, Tm.erase, Runtime.Tm.map, Tm.erase_subst t, Tm.erase_subst u,
        Subst.rootVar_lift, Subst.rootVar_liftC]
  | .unbox a U f => simp [Tm.subst, Tm.erase, Runtime.Tm.map, Atom.root_subst]

theorem Value.erase_subst {s1 s2 : Sig} (v : Value s1) (σ : Subst s1 s2) :
    (v.subst σ).erase = v.erase.map σ.rootVar := by
  match v with
  | .lam A S t g =>
      simp [Value.subst, Value.erase, Runtime.Tm.map, Tm.erase_subst t,
        Subst.rootVar_lift, Subst.rootVar_liftC]
  | .obj A W Wc F =>
      simp [Value.subst, Value.erase, Runtime.Tm.map, Fields.erase_subst F,
        Subst.rootVar_lift, Subst.rootVar_liftC]
  | .box a => simp [Value.subst, Value.erase, Runtime.Tm.map, Atom.root_subst]
  | .pack C h e v => simp [Value.subst, Value.erase, Value.erase_subst v]
  | .cast v e => simp [Value.subst, Value.erase, Value.erase_subst v]

theorem Fields.erase_subst {s1 s2 : Sig} (F : Fields s1) (σ : Subst s1 s2) :
    (F.subst σ).erase = F.erase.map σ.rootVar := by
  match F with
  | .nil => simp [Fields.subst, Fields.erase, Runtime.Fields.map]
  | .cons F ℓ t g =>
      simp [Fields.subst, Fields.erase, Runtime.Fields.map, Fields.erase_subst F,
        Tm.erase_subst t]

end

theorem Subst.rootVar_single {s : Sig} (a : Atom s) :
    (Subst.single a).rootVar = Runtime.VRen.ofRename (Rename.subst a.root) := by
  funext z; cases z <;> rfl

theorem Subst.rootVar_enter {s : Sig} (b : Atom s) :
    (Subst.enter b).rootVar = Runtime.VRen.enter b.root := by
  funext z
  cases z with
  | here => rfl
  | there z => cases z with | there z => cases z with | there z => rfl

theorem Subst.rootVar_enterObj {s : Sig} (y : BVar s .var) :
    (Subst.enterObj y).rootVar = Runtime.VRen.enterObj y := by
  funext z
  cases z with
  | here => rfl
  | there z => cases z with | there z => rfl

/-- Instantiating the innermost binder by an atom erases to instantiating by
the atom's root. -/
theorem Tm.erase_substAtom {s : Sig} (u : Tm (s,x)) (a : Atom s) :
    (u.substAtom a).erase = u.erase.substVar (a.root) := by
  rw [Tm.substAtom, Tm.erase_subst, Subst.rootVar_single, Runtime.Tm.substVar,
    Runtime.Tm.rename_eq_ofRename]

/-- Entering a closure's body erases to the runtime's own entering map. -/
theorem Tm.erase_enter {s : Sig} (t : Tm (((s,c),c),x)) (b : Atom s) :
    (t.subst (Subst.enter b)).erase = t.erase.map (Runtime.VRen.enter b.root) := by
  rw [Tm.erase_subst, Subst.rootVar_enter]

/-- Entering an object body erases to the runtime's own entering map. -/
theorem Tm.erase_enterObj {s : Sig} (t : Tm ((s,c),x)) (y : BVar s .var) :
    (t.subst (Subst.enterObj y)).erase = t.erase.map (Runtime.VRen.enterObj y) := by
  rw [Tm.erase_subst, Subst.rootVar_enterObj]

theorem Subst.rootVar_selfCast {s : Sig} (E : LeCo (s,x)) :
    (Subst.selfCast E).rootVar = Runtime.VRen.ofRename Rename.id := by
  funext z; cases z <;> rfl

/-- Adjusting a continuation body to a stripped value only inserts casts, so
the erasure is unchanged. -/
theorem Tm.erase_adjust {s : Sig} (u : Tm (s,x)) (v : Value s) :
    (u.adjust v).erase = u.erase := by
  unfold Tm.adjust
  cases v.composite? with
  | none => rfl
  | some E =>
      rw [Tm.erase_subst, Subst.rootVar_selfCast, ← Runtime.Tm.rename_eq_ofRename,
        Runtime.Tm.rename_id]

/-! ## Erasure of the machine's data -/

/-- Cast wrappers on a value are invisible to the erasure. -/
theorem Value.erase_core {s : Sig} : ∀ v : Value s, v.core.erase = v.erase
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  -- `Value.core` reads through no pack, so it is the identity here.
  | .pack _ _ _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.erase, Value.erase_core v]

/-- Applying an answer coercion to a value is invisible to the erasure: a
plain coercion adds a cast wrapper, a packing coercion adds a pack wrapper,
a congruence rewrites the wrappers of a pack and leaves anything else alone,
and all of them erase to nothing. -/
@[simp] theorem Value.erase_applyE {s : Sig} :
    ∀ (v : Value s) (g : ELeCo s), (v.applyE g).erase = v.erase
  | _, .plain _ => rfl
  | _, .pack _ _ _ => rfl
  | .lam _ _ _ _, .cong _ _ => rfl
  | .obj _ _ _ _, .cong _ _ => rfl
  | .box _, .cong _ _ => rfl
  | .pack _ _ _ _, .cong _ _ => rfl
  | .cast _ _, .cong _ _ => rfl
  | v, .trans g g' => by
      rw [Value.applyE_trans, Value.erase_applyE _ g', Value.erase_applyE v g]

/-- Store lookup commutes with erasure. -/
theorem Store.lookup_erase {s : Sig} :
    ∀ (σ : Store s) (x : BVar s .var), σ.erase.lookup x = (σ.lookup x).erase
  | .cons σ v, .here => by
      simp [Store.erase, Store.lookup, Runtime.Store.lookup, Value.erase_weaken]
  | .cons σ v, .there y => by
      simp [Store.erase, Store.lookup, Runtime.Store.lookup, Value.erase_weaken,
        Store.lookup_erase σ y]
  | .consC σ _, .there y => by
      simp [Store.erase, Store.lookup, Runtime.Store.lookup, Value.erase_weaken,
        Store.lookup_erase σ y]

/-- Field lookup commutes with erasure. -/
theorem Fields.erase_get? {s : Sig} :
    ∀ (F : Fields s) (ℓ : Label), F.erase.get? ℓ = (F.get? ℓ).map Tm.erase
  | .nil, ℓ => rfl
  | .cons F ℓ' t g, ℓ => by
      by_cases h : ℓ = ℓ' <;>
        simp [Fields.erase, Fields.get?, Runtime.Fields.get?, h, Fields.erase_get? F ℓ]

/-- Every erased value is a runtime value. -/
theorem Value.erase_isValue {s : Sig} : ∀ v : Value s, Runtime.IsValue v.erase
  | .lam _ _ _ _ => .lam
  | .obj _ _ _ _ => .obj
  | .box _ => .box
  | .pack _ _ _ v => by simpa [Value.erase] using Value.erase_isValue v
  | .cast v _ => by simpa [Value.erase] using Value.erase_isValue v

/-! ## Store entries are literals

`Value.isLiteral_rename` and `Store.Typed.lookup_isLiteral` live in
`Store.lean` now.  They read no erasure and `CanonicalForms.lean`, which this
module imports, needs them. -/

/-- A packed value is never stored: `Store.Typed` premises `Value.HasType`
(`FCdot/Store.lean:86-90`) and `Value.HasType` has no rule for a pack.  That
is the reason the three lemmas below may ask their value not to be one. -/
theorem Store.Typed.lookup_notPack {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    (x : BVar s .var) : ∀ C h₀ e v₀, σ.lookup x ≠ .pack C h₀ e v₀ := by
  intro C h₀ e v₀ heq
  have hv := hσ.lookup x
  rw [heq] at hv
  cases hv

/-- A literal that is not a pack and whose erasure is a runtime lambda is a
lambda.  The pack premise is what `Value.IsLiteral`'s catch-all leaves open:
a pack erases to its payload, so a packed lambda erases to a runtime lambda
without being one, and `Store.Typed.lookup_notPack` discharges the premise at
the one place the lemma is used. -/
theorem Value.erase_eq_lam {s : Sig} :
    ∀ (v : Value s) (t' : Runtime.Tm (Sig.body s)), v.IsLiteral →
      (∀ C h₀ e v₀, v ≠ .pack C h₀ e v₀) → v.erase = .lam t' →
      ∃ (A : CaptureSet s) (S₀ : Dom s) (t₀ : Tm (Sig.body s)) (g : CapCo (Sig.body s)),
        v = .lam A S₀ t₀ g ∧ t₀.erase = t'
  | .lam A S t g, t', _, _, h => ⟨A, S, t, g, rfl, by simpa [Value.erase] using h⟩
  | .obj _ _ _ _, t', _, _, h => by simp [Value.erase] at h
  | .box _, t', _, _, h => by simp [Value.erase] at h
  | .pack _ _ _ _, _, _, hnp, _ => absurd rfl (hnp _ _ _ _)
  | .cast _ _, _, hlit, _, _ => hlit.elim

/-- A literal whose erasure is a runtime object is an object.  A box now
erases to the runtime's box, not to an object, so the box disjunct stage A2
carried here is gone. -/
theorem Value.erase_eq_obj {s : Sig} :
    ∀ (v : Value s) (F' : Runtime.Fields ((s,c),x)), v.IsLiteral →
      (∀ C h₀ e v₀, v ≠ .pack C h₀ e v₀) → v.erase = .obj F' →
      ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
          (F : Fields ((s,c),x)),
        v = .obj A W Wc F ∧ F.erase = F'
  | .lam _ _ _ _, F', _, _, h => by simp [Value.erase] at h
  | .obj A W Wc F, F', _, _, h => ⟨A, W, Wc, F, rfl, by simpa [Value.erase] using h⟩
  | .box _, F', _, _, h => by simp [Value.erase] at h
  | .pack _ _ _ _, _, _, hnp, _ => absurd rfl (hnp _ _ _ _)
  | .cast _ _, _, hlit, _, _ => hlit.elim

/-- A literal whose erasure is a runtime box is a box, at the same root. -/
theorem Value.erase_eq_box {s : Sig} :
    ∀ (v : Value s) (y : BVar s .var), v.IsLiteral →
      (∀ C h₀ e v₀, v ≠ .pack C h₀ e v₀) → v.erase = .box y →
      ∃ b : Atom s, v = .box b ∧ b.root = y
  | .lam _ _ _ _, y, _, _, h => by simp [Value.erase] at h
  | .obj _ _ _ _, y, _, _, h => by simp [Value.erase] at h
  | .box b, y, _, _, h => ⟨b, rfl, by simpa [Value.erase] using h⟩
  | .pack _ _ _ _, _, _, hnp, _ => absurd rfl (hnp _ _ _ _)
  | .cast _ _, _, hlit, _, _ => hlit.elim

end FCdot

namespace FCdot

/-- The `unbox` steps erase to the runtime's `unbox` step, for any result
atom with the boxed atom's root: `unboxRefl` hands back `b` itself and
`unboxCast` hands it back under a cast, and a cast on an atom erases to
nothing. -/
theorem unbox_erase_step' {s : Sig} {σ : Store s} {K : Cont s} {a b : Atom s} {c : PAtom s}
    {U : CaptureSet s} {f : CapCo s} (h : σ.lookup a.root = .box b) (hc : c.root = b.root) :
    Runtime.Step ⌊(⟨σ, K, .unbox a U f⟩ : State s)⌋ ⌊(⟨σ, K, .atom c⟩ : State s)⌋ := by
  simp only [State.erase, Tm.erase, hc]
  exact Runtime.Step.unbox (by rw [Store.lookup_erase, h]; rfl)

/-! ## Forward simulation -/

/-- Every FCdot step is either a cast-frame shuffle, which the erasure does
not see and which stays in the same signature, or it erases to exactly one
runtime step. -/
theorem erase_step {s s' : Sig} {st : State s} {st' : State s'} (h : Step st st') :
    (st.CastRedex ∧ ∃ hs : s = s', hs ▸ st.erase = st'.erase) ∨
      Runtime.Step st.erase st'.erase := by
  cases h with
  | «let» =>
      refine Or.inr ?_
      simp only [State.erase, Cont.erase, Tm.erase]
      exact Runtime.Step.let
  | castPush => exact Or.inl ⟨Or.inl ⟨_, _, rfl⟩, rfl, rfl⟩
  | castVal => exact Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Or.inl ⟨_, rfl⟩⟩)), rfl, rfl⟩
  | castAtom =>
      refine Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Or.inr ⟨_, rfl⟩⟩)), rfl, ?_⟩
      simp only [State.erase, Cont.erase, Tm.erase, PAtom.root_applyE]
  -- The three answer-cast steps erase to nothing, as their plain twins do.
  | castEPush => exact Or.inl ⟨Or.inr (Or.inl ⟨_, _, rfl⟩), rfl, rfl⟩
  | castEVal =>
      refine Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨_, _, rfl, Or.inl ⟨_, rfl⟩⟩)), rfl, ?_⟩
      simp only [State.erase, Cont.erase, Tm.erase, Value.erase_applyE]
  | castEAtom =>
      refine Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨_, _, rfl, Or.inr ⟨_, rfl⟩⟩)), rfl, ?_⟩
      simp only [State.erase, Cont.erase, Tm.erase, PAtom.root_applyE]
  | letex =>
      refine Or.inr ?_
      simp only [State.erase, Cont.erase, Tm.erase]
      exact Runtime.Step.letex
  -- The payload of a packed atom is read at the same root, so the unpacking
  -- erases to the runtime's own, which substitutes that root.
  | unpackAtom =>
      refine Or.inr ?_
      simp only [State.erase, Store.erase, Cont.erase, Tm.erase, Tm.erase_substAtom,
        Cont.erase_weakenC, Atom.root, Atom.weaken, Atom.root_rename, PAtom.root]
      exact Runtime.Step.unpack
  -- A packed value erases to its payload, and the wrappers the step puts on
  -- it erase to nothing, so the store gains the payload's erasure weakened.
  | unpackVal =>
      refine Or.inr ?_
      simp only [State.erase, Store.erase, Cont.erase, Tm.erase, Value.erase_core,
        Value.erase, Value.erase_weaken, Cont.erase_weaken, Cont.erase_weakenC,
        Tm.erase_adjust]
      exact Runtime.Step.allocE (Value.erase_isValue _)
  | alloc =>
      refine Or.inr ?_
      simp only [State.erase, Store.erase, Cont.erase, Tm.erase, Value.erase_core,
        Cont.erase_weaken, Tm.erase_adjust]
      exact Runtime.Step.alloc (Value.erase_isValue _)
  | rename =>
      refine Or.inr ?_
      simp only [State.erase, Cont.erase, Tm.erase, Tm.erase_substAtom]
      exact Runtime.Step.rename
  | appVar hl =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Atom.root, Tm.erase_enter]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | appCastRefl hl hne hform hF =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.erase_enter]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | appCast hl hne hform =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.erase_enter, Atom.root]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | proj hl hg =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.erase_enterObj]
      refine Runtime.Step.proj (by rw [Store.lookup_erase, hl]; rfl) ?_
      rw [Fields.erase_get?, hg]
      rfl
  | unboxRefl hl _ _ => exact Or.inr (unbox_erase_step' hl rfl)
  | unboxCast hl _ => exact Or.inr (unbox_erase_step' hl rfl)

end FCdot

namespace FCdot

/-! ## Cast-frame normalization

A state whose next step is a cast-frame shuffle can take that step without
changing the erasure, and a measure counting the cast nodes at the head of
the term and the cast frames at the top of the continuation strictly drops.
Iterating reaches a state that is not a cast redex. -/

/-- Number of cast nodes at the head of a term. -/
def Tm.castDepth : Tm s → Nat
  | .atom _ => 0
  | .val _ => 0
  | .app _ _ => 0
  | .proj _ _ _ => 0
  | .let _ _ _ _ => 0
  | .letex _ _ _ _ _ => 0
  | .unbox _ _ _ => 0
  | .cast t _ => t.castDepth + 1
  -- An answer cast counts as its plain twin does.
  | .castE t _ => t.castDepth + 1

/-- Number of cast frames at the top of a continuation. -/
def Cont.castDepth : Cont s → Nat
  | .nil => 0
  | .cons _ (.let _ _ _) => 0
  | .cons _ (.letex _ _ _ _) => 0
  | .cons K (.cast _) => K.castDepth + 1
  | .cons K (.castE _) => K.castDepth + 1

/-- Cast-frame steps strictly decrease this measure: `castPush` trades one
head cast for one cast frame, and `castVal`/`castAtom` consume a frame. -/
def State.castMeasure (st : State s) : Nat := 2 * st.t.castDepth + st.K.castDepth

theorem State.not_castRedex_of_measure_zero {s : Sig} (st : State s)
    (h : st.castMeasure = 0) : ¬ st.CastRedex := by
  obtain ⟨σ, K, t⟩ := st
  rintro (⟨t0, e, ht⟩ | ⟨t0, g, ht⟩ | ⟨K0, e, hK, _⟩ | ⟨K0, g, hK, _⟩)
  · subst ht
    simp only [State.castMeasure, Tm.castDepth] at h
    omega
  · subst ht
    simp only [State.castMeasure, Tm.castDepth] at h
    omega
  · subst hK
    simp only [State.castMeasure, Cont.castDepth] at h
    omega
  · subst hK
    simp only [State.castMeasure, Cont.castDepth] at h
    omega

/-- `castPush` trades one head cast for one cast frame. -/
theorem State.castMeasure_castPush {s : Sig} (σ : Store s) (K : Cont s) (t : Tm s)
    (e : LeCo s) :
    (⟨σ, K ▹ .cast e, t⟩ : State s).castMeasure < (⟨σ, K, .cast t e⟩ : State s).castMeasure := by
  simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
  omega

/-- `castEPush` trades one head answer cast for one answer-cast frame. -/
theorem State.castMeasure_castEPush {s : Sig} (σ : Store s) (K : Cont s) (t : Tm s)
    (g : ELeCo s) :
    (⟨σ, K ▹ .castE g, t⟩ : State s).castMeasure
      < (⟨σ, K, .castE t g⟩ : State s).castMeasure := by
  simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
  omega

/-- `castVal` and `castAtom` consume a cast frame, leaving a cast-free term. -/
theorem State.castMeasure_castFrame {s : Sig} (σ : Store s) (K : Cont s) (e : LeCo s)
    {t t' : Tm s} (ht : t.castDepth = 0) (ht' : t'.castDepth = 0) :
    (⟨σ, K, t'⟩ : State s).castMeasure < (⟨σ, K ▹ .cast e, t⟩ : State s).castMeasure := by
  simp only [State.castMeasure, Cont.castDepth, ht, ht']
  omega

/-- `castEVal` and `castEAtom` consume an answer-cast frame, leaving a
cast-free term: `applyE` puts its result under a wrapper, not under a cast
node of the term. -/
theorem State.castMeasure_castEFrame {s : Sig} (σ : Store s) (K : Cont s) (g : ELeCo s)
    {t t' : Tm s} (ht : t.castDepth = 0) (ht' : t'.castDepth = 0) :
    (⟨σ, K, t'⟩ : State s).castMeasure < (⟨σ, K ▹ .castE g, t⟩ : State s).castMeasure := by
  simp only [State.castMeasure, Cont.castDepth, ht, ht']
  omega

/-- A cast redex steps, without changing the erasure or the store, to a state
of strictly smaller cast measure. -/
theorem castRedex_steps {s : Sig} (st : State s) (h : st.CastRedex) :
    ∃ st' : State s, Step st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      st'.castMeasure < st.castMeasure := by
  obtain ⟨σ, K, t⟩ := st
  rcases h with ⟨t0, e, ht⟩ | ⟨t0, g, ht⟩ | ⟨K0, e, hK, ⟨v, hvt⟩ | ⟨a, hat⟩⟩ |
    ⟨K0, g, hK, ⟨v, hvt⟩ | ⟨a, hat⟩⟩
  · subst ht
    exact ⟨_, .castPush, rfl, rfl, State.castMeasure_castPush σ K t0 e⟩
  · subst ht
    exact ⟨_, .castEPush, rfl, rfl, State.castMeasure_castEPush σ K t0 g⟩
  · subst hK hvt
    exact ⟨_, .castVal, rfl, rfl, State.castMeasure_castFrame σ K0 e rfl rfl⟩
  · subst hK hat
    exact ⟨_, .castAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castFrame σ K0 e rfl rfl⟩
  · subst hK hvt
    exact ⟨_, .castEVal, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl⟩
  · subst hK hat
    exact ⟨_, .castEAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl⟩

theorem Steps.head {s s' s'' : Sig} {st : State s} {st' : State s'} {st'' : State s''}
    (h : Step st st') (hs : Steps st' st'') : Steps st st'' := by
  induction hs with
  | refl => exact .tail .refl h
  | tail _ h2 ih => exact .tail (ih h) h2

/-- Iterating a cast-frame step that preserves a predicate `P` and strictly
decreases the cast measure reaches a state that is not a cast redex.
`castRedex_normalize` and `castRedex_normalize_inv` are the instances
`P := True` and `P := State.CastInv · Γ`. -/
theorem castRedex_normalize_of {s : Sig} (P : State s → Prop)
    (hstep : ∀ st : State s, P st → st.CastRedex →
      ∃ st' : State s, st ⟶ st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
        st'.castMeasure < st.castMeasure ∧ P st')
    (st : State s) (hp : P st) :
    ∃ st' : State s, st ⟶* st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex ∧ P st' := by
  suffices key : ∀ (n : Nat) (st : State s), P st → st.castMeasure ≤ n →
      ∃ st' : State s, st ⟶* st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
        ¬ st'.CastRedex ∧ P st' from key st.castMeasure st hp (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro st hp hm
      exact ⟨st, .refl, rfl, rfl,
        State.not_castRedex_of_measure_zero st (Nat.le_zero.mp hm), hp⟩
  | succ n ih =>
      intro st hp hm
      by_cases hc : st.CastRedex
      · obtain ⟨st1, hstep, he1, hs1, hlt, hp1⟩ := hstep st hp hc
        obtain ⟨st2, hsteps, he2, hs2, hnc, hp2⟩ := ih st1 hp1 (by omega)
        exact ⟨st2, Steps.head hstep hsteps, he2.trans he1, hs2.trans hs1, hnc, hp2⟩
      · exact ⟨st, .refl, rfl, rfl, hc, hp⟩

/-- Every state reaches, by cast-frame steps only, a state with the same
erasure and store that is not a cast redex. -/
theorem castRedex_normalize {s : Sig} (st : State s) :
    ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex := by
  obtain ⟨st', hsteps, he, hs, hnc, -⟩ :=
    castRedex_normalize_of (fun _ => True)
      (fun st _ hc =>
        let ⟨st', hstep, he, hs, hlt⟩ := castRedex_steps st hc
        ⟨st', hstep, he, hs, hlt, trivial⟩)
      st trivial
  exact ⟨st', hsteps, he, hs, hnc⟩

/-! ### Carrying typing through cast-frame normalization

Reflection of a runtime application step needs the head atom of the residual
application to be typed at a function type.  Cast-frame steps do not preserve
term typing on the nose (`castVal` and `castAtom` push a coercion into a
value or an atom, and the resulting wrapper is typed only because the frame
was), but they do preserve the weaker invariant below, which is all the
application case uses. -/

/-- Invariant along cast-frame steps: the running term has an answer, or it
is already a value or an atom.  A focus is what has an answer, so the first
disjunct is read at the answer sort. -/
def State.CastInv (st : State s) (Γ : Ctx s) : Prop :=
  (∃ E, Γ ⊢ st.t :ᵉ E) ∨ (∃ v, st.t = .val v) ∨ (∃ a, st.t = .atom a)

/-- The cast-frame step of `castRedex_steps` preserves the invariant. -/
theorem castRedex_steps_inv {s : Sig} (st : State s) (Γ : Ctx s) (hq : st.CastInv Γ)
    (h : st.CastRedex) :
    ∃ st' : State s, Step st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      st'.castMeasure < st.castMeasure ∧ st'.CastInv Γ := by
  obtain ⟨σ, K, t⟩ := st
  rcases h with ⟨t0, e, ht⟩ | ⟨t0, g, ht⟩ | ⟨K0, e, hK, ⟨v, hvt⟩ | ⟨a, hat⟩⟩ |
    ⟨K0, g, hK, ⟨v, hvt⟩ | ⟨a, hat⟩⟩
  · subst ht
    refine ⟨_, .castPush, rfl, rfl, State.castMeasure_castPush σ K t0 e, ?_⟩
    rcases hq with ⟨T, hT⟩ | ⟨v, hvv⟩ | ⟨a, haa⟩
    · cases hT with
      | cast ht' _ => exact Or.inl ⟨_, ht'⟩
    · simp at hvv
    · simp at haa
  · subst ht
    refine ⟨_, .castEPush, rfl, rfl, State.castMeasure_castEPush σ K t0 g, ?_⟩
    rcases hq with ⟨T, hT⟩ | ⟨v, hvv⟩ | ⟨a, haa⟩
    · cases hT with
      | castE ht' _ => exact Or.inl ⟨_, ht'⟩
    · simp at hvv
    · simp at haa
  · subst hK hvt
    exact ⟨_, .castVal, rfl, rfl, State.castMeasure_castFrame σ K0 e rfl rfl,
      Or.inr (Or.inl ⟨_, rfl⟩)⟩
  · subst hK hat
    exact ⟨_, .castAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castFrame σ K0 e rfl rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  · subst hK hvt
    exact ⟨_, .castEVal, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl, Or.inr (Or.inl ⟨_, rfl⟩)⟩
  · subst hK hat
    exact ⟨_, .castEAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩

/-- `castRedex_normalize`, carrying the invariant to the normal form. -/
theorem castRedex_normalize_inv {s : Sig} (st : State s) (Γ : Ctx s)
    (hq : st.CastInv Γ) :
    ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex ∧ st'.CastInv Γ :=
  castRedex_normalize_of (State.CastInv · Γ) (fun st hq hc => castRedex_steps_inv st Γ hq hc)
    st hq

/-! ### Carrying the frame's answer through cast-frame normalization

`State.CastInv` says what the vanilla line needed: at a `let` frame the
focus is a value or an atom, and both steps fire.  The two frames of this
stage read more.  An unpacking frame steps only at a packed focus, a `let`
frame only at a plain one, and the erasure tells the two apart nowhere,
since a pack erases to what it wraps.  So the backward simulation needs the
focus to match the frame, and what says so is the continuation's typing,
which cast-frame steps carry exactly as `preservation` does.  The store is
untouched by those steps, so the context stays fixed and the three
canonical-forms obligations keep their subject. -/

/-- The typed invariant: the focus has an answer and the continuation
accepts it.  With the store typing it is `State.Typed`, and the store is
what a cast-frame step leaves alone. -/
def State.CastTyped (st : State s) (Γ : Ctx s) (V : Ty s) : Prop :=
  ∃ E : ETy s, Γ ⊢ st.t :ᵉ E ∧ Γ ⊢ₖ st.K : E ⇒ V

theorem State.CastTyped.castInv {s : Sig} {st : State s} {Γ : Ctx s} {V : Ty s}
    (h : st.CastTyped Γ V) : st.CastInv Γ := by
  obtain ⟨E, ht, -⟩ := h
  exact Or.inl ⟨E, ht⟩

/-- The cast-frame step of `castRedex_steps` preserves the typed invariant.
It is the six cast-frame cases of `preservation` at a fixed context, which
is what they are there too: none of them touches the store. -/
theorem castRedex_steps_typed {s : Sig} (st : State s) (Γ : Ctx s) (V : Ty s)
    (hq : st.CastTyped Γ V) (h : st.CastRedex) :
    ∃ st' : State s, Step st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      st'.castMeasure < st.castMeasure ∧ st'.CastTyped Γ V := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨E, ht, hK⟩ := hq
  rcases h with ⟨t0, e, hte⟩ | ⟨t0, g, hte⟩ | ⟨K0, e, hKe, ⟨v, hvt⟩ | ⟨a, hat⟩⟩ |
    ⟨K0, g, hKe, ⟨v, hvt⟩ | ⟨a, hat⟩⟩
  · subst hte
    refine ⟨_, .castPush, rfl, rfl, State.castMeasure_castPush σ K t0 e, ?_⟩
    cases ht with | cast ht' he => exact ⟨_, ht', .cast he hK⟩
  · subst hte
    refine ⟨_, .castEPush, rfl, rfl, State.castMeasure_castEPush σ K t0 g, ?_⟩
    cases ht with | castE ht' hg => exact ⟨_, ht', .castE hg hK⟩
  · subst hKe hvt
    refine ⟨_, .castVal, rfl, rfl, State.castMeasure_castFrame σ K0 e rfl rfl, ?_⟩
    cases ht with
    | val hv =>
        cases hK with
        | cast he hK' => exact ⟨_, .val (.plain (hv.ty_inv.cast he)), hK'⟩
  · subst hKe hat
    refine ⟨_, .castAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castFrame σ K0 e rfl rfl, ?_⟩
    cases ht with
    | atom hp =>
        cases hK with
        | cast he hK' =>
            exact ⟨_, .atom (PAtom.HasType.applyE (.plain _) hp (.plain he)), hK'⟩
  · subst hKe hvt
    refine ⟨_, .castEVal, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl, ?_⟩
    cases ht with
    | val hv =>
        cases hK with
        | castE hg hK' => exact ⟨_, .val (Value.HasTypeE.applyE _ hv hg), hK'⟩
  · subst hKe hat
    refine ⟨_, .castEAtom, by simp [State.erase, Cont.erase, Tm.erase], rfl,
      State.castMeasure_castEFrame σ K0 g rfl rfl, ?_⟩
    cases ht with
    | atom hp =>
        cases hK with
        | castE hg hK' => exact ⟨_, .atom (PAtom.HasType.applyE _ hp hg), hK'⟩

/-- `castRedex_normalize`, carrying the typed invariant to the normal
form. -/
theorem castRedex_normalize_typed {s : Sig} (st : State s) (Γ : Ctx s) (V : Ty s)
    (hq : st.CastTyped Γ V) :
    ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex ∧ st'.CastTyped Γ V :=
  castRedex_normalize_of (fun st => State.CastTyped st Γ V)
    (fun st hq hc => castRedex_steps_typed st Γ V hq hc) st hq

/-! ## Backward simulation -/

/-- The FCdot step realizing a runtime application step at a wrapped atom,
given the head form of the atom's casts. -/
theorem app_step_of_form {s : Sig} {σ : Store s} {K : Cont s} {a b : Atom s}
    {A : CaptureSet s} {S₀ : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    {n : Nat} {a' : Atom s} {F : Form s}
    (hv : σ.lookup a.root = .lam A S₀ t₀ g) (hne : a ≠ .var a.root)
    (hform : σ ⊢ a ⇓ᶜ[n] (a', F))
    (hF : F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) :
    ∃ st' : State s, Step (⟨σ, K, .app a b⟩ : State s) st' ∧
      st'.erase =
        (⟨σ.erase, K.erase, t₀.erase.map (Runtime.VRen.enter b.root)⟩ : Runtime.State s) := by
  rcases hF with hF | ⟨φ, hF⟩ | ⟨d, c, hF⟩
  · subst hF
    exact ⟨_, Step.appCastRefl hv hne hform (Or.inl rfl), by
      simp [State.erase, Tm.erase_enter]⟩
  · subst hF
    exact ⟨_, Step.appCastRefl hv hne hform (Or.inr ⟨φ, rfl⟩), by
      simp [State.erase, Tm.erase_enter]⟩
  · subst hF
    exact ⟨_, Step.appCast hv hne hform, by
      simp [State.erase, Tm.erase, Tm.erase_enter, Atom.root]⟩

/-- Reflection of a runtime `rename` step: an atom under a `let` frame is
substituted into the frame's body. -/
theorem erase_reflect_rename {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm (s,x)}
    {U : CaptureSet s} {f : CapCo (s,x)} {a : Atom s} {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K ▹ .let u U f, .atom (.plain a)⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K ▹ .let u U f, .atom (.plain a)⟩ : State s) ⟶ st' ∧
      ⌊st'⌋ = r := by
  simp only [State.erase, Cont.erase, Tm.erase] at h
  refine Runtime.Step.var_cons_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K ▹ .let u U f, .atom (.plain a)⟩ : State s) ⟶ st' ∧
      ⌊st'⌋ = r') h ?_
  exact ⟨_, .rename, by simp [State.erase, Tm.erase_substAtom]⟩

/-- Reflection of a runtime `alloc` step: a value under a `let` frame is
stored, with its casts stripped and pushed into the frame's body. -/
theorem erase_reflect_alloc {s s' : Sig} {σ : Store s} {K : Cont s} {u : Tm (s,x)}
    {U : CaptureSet s} {f : CapCo (s,x)} {v : Value s} {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K ▹ .let u U f, .val v⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K ▹ .let u U f, .val v⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Cont.erase, Tm.erase] at h
  refine Runtime.Step.value_cons_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K ▹ .let u U f, .val v⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r')
    (Value.erase_isValue v) h ?_
  exact ⟨_, .alloc, by
    simp [State.erase, Store.erase, Cont.erase_weaken, Value.erase_core, Tm.erase_adjust]⟩

/-- Reflection of a runtime `app` step.  The store entry at the head's root
is a literal, hence a lambda; a bare variable steps by `appVar`, and a
wrapped atom by `app_step_of_form` once `hcf` supplies the head form of its
casts. -/
theorem erase_reflect_app {s s' : Sig} {σ : Store s} {K : Cont s} {a b : Atom s}
    {Γ : Ctx s} {r : Runtime.State s'} (hσ : ⊢ σ : Γ)
    (hcf : a ≠ .var a.root → ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c))
    (h : Runtime.Step ⌊(⟨σ, K, .app a b⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K, .app a b⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Tm.erase] at h
  refine Runtime.Step.app_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K, .app a b⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r') h ?_
  intro t' hlk
  rw [Store.lookup_erase] at hlk
  obtain ⟨A, S₀, t₀, g, hv, rfl⟩ :=
    Value.erase_eq_lam _ t' (hσ.lookup_isLiteral a.root) (hσ.lookup_notPack a.root) hlk
  by_cases hne : a = .var a.root
  · have hstep : (⟨σ, K, .app (.var a.root) b⟩ : State s) ⟶
        ⟨σ, K, t₀.subst (Subst.enter b)⟩ := Step.appVar hv
    rw [← hne] at hstep
    exact ⟨_, hstep, by simp [State.erase, Tm.erase_enter]⟩
  · obtain ⟨n, a', F, hform, hF⟩ := hcf hne
    exact app_step_of_form (K := K) (b := b) hv hne hform hF

/-- Reflection of a runtime `proj` step: `hfld` names the object at the root
and the field being projected -- the canonical-forms obligation `has_canon`
discharges (`closed_has_field`), and the same fact progress uses.  The store
entry is read from `hfld` rather than from the erasure. -/
theorem erase_reflect_proj {s s' : Sig} {σ : Store s} {K : Cont s} {a : Atom s} {ℓ : Label}
    {hh : Has s} {r : Runtime.State s'}
    (hfld : ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
        (F : Fields ((s,c),x)) (t : Tm ((s,c),x)),
      σ.lookup a.root = .obj A W Wc F ∧ F.get? ℓ = some t)
    (h : Runtime.Step ⌊(⟨σ, K, .proj a ℓ hh⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K, .proj a ℓ hh⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Tm.erase] at h
  refine Runtime.Step.proj_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K, .proj a ℓ hh⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r') h ?_
  intro F' t' hlk hg
  rw [Store.lookup_erase] at hlk
  obtain ⟨A, W, Wc, F, t0, hv, hgg⟩ := hfld
  rw [hv] at hlk
  obtain rfl : F.erase = F' := by simpa [Value.erase] using hlk
  rw [Fields.erase_get?, hgg, Option.map_some] at hg
  exact ⟨_, Step.proj hv hgg, by
    simp [State.erase, Tm.erase_enterObj, Option.some.inj hg]⟩

/-- Reflection of the runtime `unbox` step an `unbox` erases to: `hbx` names
the stored box and the head form of the atom's casts -- the canonical-forms
obligation `closed_box_inversion` discharges -- and the machine's two
`unbox` steps consume exactly those three head forms. -/
theorem erase_reflect_unbox {s s' : Sig} {σ : Store s} {K : Cont s} {a : Atom s}
    {U : CaptureSet s} {f : CapCo s} {r : Runtime.State s'}
    (hbx : ∃ (b a' : Atom s) (n : Nat) (F : Form s), σ.lookup a.root = .box b ∧
      σ ⊢ a ⇓ᶜ[n] (a', F) ∧ (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d))
    (h : Runtime.Step ⌊(⟨σ, K, .unbox a U f⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K, .unbox a U f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  obtain ⟨b, a', n, F, hv, hform, hF⟩ := hbx
  simp only [State.erase, Tm.erase] at h
  refine Runtime.Step.unbox_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K, .unbox a U f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r') h ?_
  intro y hlk
  rw [Store.lookup_erase, hv] at hlk
  obtain rfl : b.root = y := by simpa [Value.erase] using hlk
  rcases hF with rfl | ⟨φ, rfl⟩ | ⟨d, rfl⟩
  · exact ⟨_, Step.unboxRefl hv hform (Or.inl rfl), by simp [State.erase, Tm.erase]⟩
  · exact ⟨_, Step.unboxRefl hv hform (Or.inr ⟨φ, rfl⟩), by simp [State.erase, Tm.erase]⟩
  · exact ⟨_, Step.unboxCast hv hform, by simp [State.erase, Tm.erase, Atom.root]⟩

/-- Reflection of a runtime `let` step: the body becomes a `let` frame. -/
theorem erase_reflect_let {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {u : Tm (s,x)}
    {U : CaptureSet s} {f : CapCo (s,x)} {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K, .let t u U f⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K, .let t u U f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Tm.erase] at h
  refine Runtime.Step.let_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K, .let t u U f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r') h ?_
  exact ⟨_, .let, by simp [State.erase, Cont.erase]⟩

/-- Reflection of a runtime `letex` step: the body becomes an unpacking
frame. -/
theorem erase_reflect_letex {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s}
    {u : Tm ((s,c),x)} {U : CaptureSet s} {h₁ : CapCo s} {f : CapCo ((s,c),x)}
    {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K, .letex t u U h₁ f⟩ : State s)⌋ r) :
    ∃ st' : State s', (⟨σ, K, .letex t u U h₁ f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Tm.erase] at h
  refine Runtime.Step.letex_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K, .letex t u U h₁ f⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r') h ?_
  exact ⟨_, .letex, by simp [State.erase, Cont.erase]⟩

/-- Reflection of the runtime `unpack` step: a packed atom at an unpacking
frame.  The wrapper is read at the same root as its payload, so the runtime
step substitutes the root the FCdot step substitutes the payload at. -/
theorem erase_reflect_unpackAtom {s s' : Sig} {σ : Store s} {K : Cont s}
    {u : Tm ((s,c),x)} {U : CaptureSet s} {h₁ : CapCo s} {f : CapCo ((s,c),x)}
    {C : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {a : Atom s}
    {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K ▹ .letex u U h₁ f, .atom (.pack C h₀ e a)⟩ : State s)⌋ r) :
    ∃ st' : State s',
      (⟨σ, K ▹ .letex u U h₁ f, .atom (.pack C h₀ e a)⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Cont.erase, Tm.erase, PAtom.root] at h
  refine Runtime.Step.var_consE_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K ▹ .letex u U h₁ f, .atom (.pack C h₀ e a)⟩ : State s) ⟶ st' ∧
      ⌊st'⌋ = r') h ?_
  exact ⟨_, .unpackAtom, by
    simp [State.erase, Store.erase, Tm.erase_substAtom, Cont.erase_weakenC,
      Atom.root, Atom.weaken]⟩

/-- Reflection of the runtime `allocE` step: a packed value at an unpacking
frame.  A pack erases to what it wraps, so the store gains that erasure, as
the runtime step asks. -/
theorem erase_reflect_unpackVal {s s' : Sig} {σ : Store s} {K : Cont s}
    {u : Tm ((s,c),x)} {U : CaptureSet s} {h₁ : CapCo s} {f : CapCo ((s,c),x)}
    {C : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {v : Value s}
    {r : Runtime.State s'}
    (h : Runtime.Step ⌊(⟨σ, K ▹ .letex u U h₁ f, .val (.pack C h₀ e v)⟩ : State s)⌋ r) :
    ∃ st' : State s',
      (⟨σ, K ▹ .letex u U h₁ f, .val (.pack C h₀ e v)⟩ : State s) ⟶ st' ∧ ⌊st'⌋ = r := by
  simp only [State.erase, Cont.erase, Tm.erase, Value.erase] at h
  refine Runtime.Step.value_consE_inv (motive := fun s'' r' =>
    ∃ st' : State s'', (⟨σ, K ▹ .letex u U h₁ f, .val (.pack C h₀ e v)⟩ : State s) ⟶ st' ∧
      ⌊st'⌋ = r') (Value.erase_isValue v) h ?_
  exact ⟨_, .unpackVal, by
    simp [State.erase, Store.erase, Value.erase_core, Value.erase,
      Value.erase_weaken, Cont.erase_weaken, Cont.erase_weakenC, Tm.erase_adjust]⟩

/-- Reflection at a state that is not a cast redex: one FCdot step realizes
the runtime step.  `hcf` is the canonical-forms obligation for a coerced
function atom, `hat` says that a residual application is applied to a typed
function atom, `hfl` names the object a residual projection reads, and `hbx`
the box a residual unboxing reads with the head form of its casts. -/
theorem erase_reflect_aux {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {Γ : Ctx s}
    {r : Runtime.State s'} (hσ : ⊢ σ : Γ)
    (hcf : ∀ (a : Atom s) (S : Dom s) (T : Cod s) (C : CaptureSet s),
      Γ ⊢ₐ a : (Π(S) T) ^ C →
      a ≠ .var a.root → ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c))
    (hat : ∀ a b : Atom s, t = .app a b →
      ∃ (S : Dom s) (T : Cod s) (C : CaptureSet s), Γ ⊢ₐ a : (Π(S) T) ^ C)
    (hfl : ∀ (a : Atom s) (ℓ : Label) (hh : Has s), t = .proj a ℓ hh →
      ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
        (F : Fields ((s,c),x)) (t0 : Tm ((s,c),x)),
        σ.lookup a.root = .obj A W Wc F ∧ F.get? ℓ = some t0)
    (hbx : ∀ (a : Atom s) (U : CaptureSet s) (f : CapCo s), t = .unbox a U f →
      ∃ (b a' : Atom s) (n : Nat) (F : Form s), σ.lookup a.root = .box b ∧
        σ ⊢ a ⇓ᶜ[n] (a', F) ∧ (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d))
    (hq : ∃ (E : ETy s) (V : Ty s), Γ ⊢ t :ᵉ E ∧ Γ ⊢ₖ K : E ⇒ V)
    (hnc : ¬ (State.CastRedex ⟨σ, K, t⟩))
    (h : Runtime.Step (State.erase ⟨σ, K, t⟩) r) :
    ∃ st' : State s', Step (⟨σ, K, t⟩ : State s) st' ∧ st'.erase = r := by
  obtain ⟨E, V, ht, hKt⟩ := hq
  cases t with
  | atom p =>
      cases K with
      | nil => exact (Runtime.Step.var_nil_inv h).elim
      | cons K0 fr =>
          cases fr with
          -- A `let` frame accepts a plain answer, so the focus is a plain
          -- atom and the `rename` step fires.
          | «let» u U f =>
              cases ht with
              | atom hp =>
                  cases hKt with
                  | «let» hu hf hK' =>
                      obtain ⟨a, rfl, -⟩ := hp.ty_inv
                      exact erase_reflect_rename h
          | cast e => exact absurd (Or.inr (Or.inr (Or.inl ⟨K0, e, rfl, Or.inr ⟨p, rfl⟩⟩))) hnc
          | castE g => exact absurd (Or.inr (Or.inr (Or.inr ⟨K0, g, rfl, Or.inr ⟨p, rfl⟩⟩))) hnc
          -- An unpacking frame accepts an existential, so `pack_canon` names
          -- the wrapper and the matching unpack fires.
          | letex u U h₁ f =>
              cases ht with
              | atom hp =>
                  cases hKt with
                  | letex hh hu hf hK' =>
                      obtain ⟨C, h₀, e, a, S, rfl, -, -, -⟩ := pack_canon hp
                      exact erase_reflect_unpackAtom h
  | val v =>
      cases K with
      | nil => exact (Runtime.Step.value_nil_inv (Value.erase_isValue v) h).elim
      | cons K0 fr =>
          cases fr with
          | «let» u U f => exact erase_reflect_alloc h
          | cast e => exact absurd (Or.inr (Or.inr (Or.inl ⟨K0, e, rfl, Or.inl ⟨v, rfl⟩⟩))) hnc
          | castE g => exact absurd (Or.inr (Or.inr (Or.inr ⟨K0, g, rfl, Or.inl ⟨v, rfl⟩⟩))) hnc
          | letex u U h₁ f =>
              cases ht with
              | val hv =>
                  cases hKt with
                  | letex hh hu hf hK' =>
                      obtain ⟨C, h₀, e, v₀, S, rfl, -, -, -⟩ := pack_canon_val hv
                      exact erase_reflect_unpackVal h
  | app a b =>
      exact erase_reflect_app hσ
        (fun hne => let ⟨S, T, C, hpi⟩ := hat a b rfl; hcf a S T C hpi hne) h
  | proj a ℓ hh => exact erase_reflect_proj (hfl a ℓ hh rfl) h
  | unbox a U f => exact erase_reflect_unbox (hbx a U f rfl) h
  | «let» t u U f => exact erase_reflect_let h
  | letex t u U h₁ f => exact erase_reflect_letex h
  | cast t e => exact absurd (Or.inl ⟨t, e, rfl⟩) hnc
  | castE t g => exact absurd (Or.inr (Or.inl ⟨t, g, rfl⟩)) hnc

/-- Backward simulation: every runtime step out of an erased state is
realized by a run of the FCdot machine, which first takes the pending
cast-frame steps. -/
theorem erase_reflect {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ)
    (hcf : ∀ (a : Atom s) (S : Dom s) (T : Cod s) (C : CaptureSet s),
      Γ ⊢ₐ a : (Π(S) T) ^ C →
      a ≠ .var a.root → ∃ n a' F, st.σ ⊢ a ⇓ᶜ[n] (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c))
    (hfd : ∀ (hh : Has s) (x : BVar s .var) (ℓ : Label), Γ ⊢ hh : x ∋ ℓ →
      ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
        (F : Fields ((s,c),x)) (t0 : Tm ((s,c),x)),
        st.σ.lookup x = .obj A W Wc F ∧ F.get? ℓ = some t0)
    (hbox : ∀ (a : Atom s) (T : Ty s) (D : CaptureSet s), Γ ⊢ₐ a : (□ T) ^ D →
      ∃ (b a' : Atom s) (n : Nat) (F : Form s), st.σ.lookup a.root = .box b ∧
        st.σ ⊢ a ⇓ᶜ[n] (a', F) ∧ (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d))
    (hty : ∃ (E : ETy s) (V : Ty s), Γ ⊢ st.t :ᵉ E ∧ Γ ⊢ₖ st.K : E ⇒ V)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r := by
  obtain ⟨E0, V0, ht0, hK0⟩ := hty
  obtain ⟨st1, hsteps, herase, hstore, hnc, hinv⟩ :=
    castRedex_normalize_typed st Γ V0 ⟨E0, ht0, hK0⟩
  have hσ1 : ⊢ st1.σ : Γ := by rw [hstore]; exact hσ
  have hcf1 : ∀ (a : Atom s) (S : Dom s) (T : Cod s) (C : CaptureSet s),
      Γ ⊢ₐ a : (Π(S) T) ^ C →
      a ≠ .var a.root → ∃ n a' F, st1.σ ⊢ a ⇓ᶜ[n] (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
    rw [hstore]; exact hcf
  obtain ⟨E1, ht1, hK1⟩ := hinv
  have hat : ∀ a b : Atom s, st1.t = .app a b →
      ∃ (S : Dom s) (T : Cod s) (C : CaptureSet s), Γ ⊢ₐ a : (Π(S) T) ^ C := by
    intro a b hab
    rw [hab] at ht1
    cases ht1 with
    | app hpa _ => exact ⟨_, _, _, hpa⟩
  have hfl : ∀ (a : Atom s) (ℓ : Label) (hh : Has s), st1.t = .proj a ℓ hh →
      ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
        (F : Fields ((s,c),x)) (t0 : Tm ((s,c),x)),
        st1.σ.lookup a.root = .obj A W Wc F ∧ F.get? ℓ = some t0 := by
    intro a ℓ hh hab
    rw [hstore]
    rw [hab] at ht1
    cases ht1 with
    | proj _ hhh => exact hfd _ _ _ hhh
  have hbx : ∀ (a : Atom s) (U : CaptureSet s) (f : CapCo s), st1.t = .unbox a U f →
      ∃ (b a' : Atom s) (n : Nat) (F : Form s), st1.σ.lookup a.root = .box b ∧
        st1.σ ⊢ a ⇓ᶜ[n] (a', F) ∧ (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d) := by
    intro a U f hab
    rw [hstore]
    rw [hab] at ht1
    cases ht1 with
    | unbox hba _ => exact hbox _ _ _ hba
  rw [← herase] at h
  suffices key : ∃ st' : State s', Step st1 st' ∧ st'.erase = r by
    obtain ⟨st', hstep, heq⟩ := key
    exact ⟨st', Steps.tail hsteps hstep, heq⟩
  clear hsteps herase hstore hσ hcf hfd hbox
  obtain ⟨σ, K, t⟩ := st1
  exact erase_reflect_aux hσ1 hcf1 hat hfl hbx ⟨_, _, ht1, hK1⟩ hnc h

/-! ## Final states -/

/-- A final FCdot state erases to a final runtime state. -/
theorem final_erase {s : Sig} {st : State s} (h : st.Final) : st.erase.Final := by
  obtain ⟨σ, K, t⟩ := st
  rcases h with ⟨hK, v, hv⟩ | ⟨hK, a, ha⟩
  · subst hK; subst hv
    exact ⟨rfl, Or.inl (Value.erase_isValue v)⟩
  · subst hK; subst ha
    exact ⟨rfl, Or.inr ⟨a.root, rfl⟩⟩

/-- Conversely, a state whose erasure is final is itself final, unless a cast
frame is still pending. -/
theorem final_reflect {s : Sig} {st : State s} {Γ : Ctx s} (hσ : ⊢ st.σ : Γ)
    (h : st.erase.Final) : st.Final ∨ st.CastRedex := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨hK, ht⟩ := h
  cases t with
  | atom p =>
      cases K with
      | nil => exact Or.inl (Or.inr ⟨rfl, p, rfl⟩)
      | cons K0 fr =>
          cases fr with
          | «let» u U f => simp [State.erase, Cont.erase] at hK
          | letex u U h₁ f => simp [State.erase, Cont.erase] at hK
          | cast e => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨K0, e, rfl, Or.inr ⟨p, rfl⟩⟩)))
          | castE g => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨K0, g, rfl, Or.inr ⟨p, rfl⟩⟩)))
  | val v =>
      cases K with
      | nil => exact Or.inl (Or.inl ⟨rfl, v, rfl⟩)
      | cons K0 fr =>
          cases fr with
          | «let» u U f => simp [State.erase, Cont.erase] at hK
          | letex u U h₁ f => simp [State.erase, Cont.erase] at hK
          | cast e => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨K0, e, rfl, Or.inl ⟨v, rfl⟩⟩)))
          | castE g => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨K0, g, rfl, Or.inl ⟨v, rfl⟩⟩)))
  | app a b | proj a ℓ hh | «let» t u U f | unbox a U f | letex t u U h₁ f =>
      -- the erasure is an application, projection, `let` or unpacking: not
      -- final
      simp only [State.erase, Tm.erase] at ht
      exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
  | cast t e => exact Or.inr (Or.inl ⟨t, e, rfl⟩)
  | castE t g => exact Or.inr (Or.inr (Or.inl ⟨t, g, rfl⟩))

/-- Backward simulation over typed stores.  It stands here rather than at the
end of `CanonicalForms.lean`, where the vanilla line keeps it, because this
module now imports that one: `erase_reflect` reads the answer sort, so
`CanonicalForms` has to be green before it.  The statement is unchanged. -/
theorem erase_reflect' {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ)
    (hty : ∃ (E : ETy s) (V : Ty s), Γ ⊢ st.t :ᵉ E ∧ Γ ⊢ₖ st.K : E ⇒ V)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect hσ (fun _ _ _ _ ha _ => closedAtomForm_pi hσ ha)
    (fun _ _ _ hh => closed_has_field hσ hh)
    (fun _ _ _ ha => closed_box_inversion hσ ha) hty h

end FCdot

end CapturesCC
