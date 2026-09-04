import Coercions.FCdot.Erasure
import Coercions.FCdot.Preservation

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

theorem Step.app_inv {s s' : Sig} {σ : Store s} {K : Cont s} {x y : BVar s .var}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .app x y⟩ r)
    (hm : ∀ t, σ.lookup x = .lam t → motive s ⟨σ, K, t.substVar y⟩) : motive s' r := by
  cases h with
  | app hl => exact hm _ hl
  | alloc hv => cases hv

theorem Step.proj_inv {s s' : Sig} {σ : Store s} {K : Cont s} {x : BVar s .var} {ℓ : Label}
    {r : State s'} {motive : ∀ s'', State s'' → Prop}
    (h : Step ⟨σ, K, .proj x ℓ⟩ r)
    (hm : ∀ F t, σ.lookup x = .obj F → F.get? ℓ = some t →
      motive s ⟨σ, K, t.substVar x⟩) : motive s' r := by
  cases h with
  | proj hl hg => exact hm _ _ hl hg
  | alloc hv => cases hv

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
  | app => cases hv
  | proj => cases hv
  | rename => cases hv

theorem Step.value_nil_inv {s s' : Sig} {σ : Store s} {v : Tm s} {r : State s'}
    (hv : IsValue v) (h : Step ⟨σ, .nil, v⟩ r) : False := by
  cases h <;> cases hv

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
  | .let t u =>
      simp [Tm.rename, Tm.erase, Runtime.Tm.rename, Tm.erase_rename t, Tm.erase_rename u]
  | .cast t e => simp [Tm.rename, Tm.erase, Tm.erase_rename t]

theorem Value.erase_rename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    (v.rename ρ).erase = v.erase.rename ρ := by
  match v with
  | .lam S t => simp [Value.rename, Value.erase, Runtime.Tm.rename, Tm.erase_rename t]
  | .obj W F =>
      simp [Value.rename, Value.erase, Runtime.Tm.rename, Fields.erase_rename F]
  | .cast v e => simp [Value.rename, Value.erase, Value.erase_rename v]

theorem Fields.erase_rename {s1 s2 : Sig} (F : Fields s1) (ρ : Rename s1 s2) :
    (F.rename ρ).erase = F.erase.rename ρ := by
  match F with
  | .nil => simp [Fields.rename, Fields.erase, Runtime.Fields.rename]
  | .cons F ℓ t =>
      simp [Fields.rename, Fields.erase, Runtime.Fields.rename, Fields.erase_rename F,
        Tm.erase_rename t]

end

/-- Erasure commutes with weakening of terms. -/
theorem Tm.erase_weaken {s : Sig} (t : Tm s) :
    (t.weaken (k := .var)).erase = t.erase.weaken := by
  simp [Tm.weaken, Runtime.Tm.weaken, Tm.erase_rename]

/-- Erasure commutes with weakening of values. -/
theorem Value.erase_weaken {s : Sig} (v : Value s) :
    (v.weaken (k := .var)).erase = v.erase.weaken := by
  simp [Value.weaken, Runtime.Tm.weaken, Value.erase_rename]

/-- Erasure commutes with renaming of continuations; cast frames vanish. -/
theorem Cont.erase_rename {s1 s2 : Sig} :
    ∀ (K : Cont s1) (ρ : Rename s1 s2), (K.rename ρ).erase = K.erase.rename ρ
  | .nil, ρ => by simp [Cont.rename, Cont.erase, Runtime.Cont.rename]
  | .cons K (.let u), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Runtime.Cont.rename,
        Cont.erase_rename K, Tm.erase_rename]
  | .cons K (.cast e), ρ => by
      simp [Cont.rename, Frame.rename, Cont.erase, Cont.erase_rename K]

/-- Erasure commutes with weakening of continuations. -/
theorem Cont.erase_weaken {s : Sig} (K : Cont s) : K.weaken.erase = K.erase.weaken := by
  simp [Cont.weaken, Runtime.Cont.weaken, Cont.erase_rename]

/-! ## Commutation of erasure with atom substitution

An atom erases to its root variable, so substituting atoms erases to
renaming by the induced renaming of roots. -/

mutual

/-- Erasure turns atom substitution into the renaming of roots. -/
theorem Tm.erase_subst {s1 s2 : Sig} (t : Tm s1) (σ : Subst s1 s2) :
    (t.subst σ).erase = t.erase.rename σ.root := by
  match t with
  | .atom a => simp [Tm.subst, Tm.erase, Runtime.Tm.rename, Subst.root_var]
  | .val v => simp [Tm.subst, Tm.erase, Value.erase_subst v]
  | .app a b => simp [Tm.subst, Tm.erase, Runtime.Tm.rename, Subst.root_var]
  | .proj a ℓ _ => simp [Tm.subst, Tm.erase, Runtime.Tm.rename, Subst.root_var]
  | .let t u =>
      simp [Tm.subst, Tm.erase, Runtime.Tm.rename, Tm.erase_subst t, Tm.erase_subst u]
  | .cast t e => simp [Tm.subst, Tm.erase, Tm.erase_subst t]

theorem Value.erase_subst {s1 s2 : Sig} (v : Value s1) (σ : Subst s1 s2) :
    (v.subst σ).erase = v.erase.rename σ.root := by
  match v with
  | .lam S t => simp [Value.subst, Value.erase, Runtime.Tm.rename, Tm.erase_subst t]
  | .obj W F =>
      simp [Value.subst, Value.erase, Runtime.Tm.rename, Fields.erase_subst F]
  | .cast v e => simp [Value.subst, Value.erase, Value.erase_subst v]

theorem Fields.erase_subst {s1 s2 : Sig} (F : Fields s1) (σ : Subst s1 s2) :
    (F.subst σ).erase = F.erase.rename σ.root := by
  match F with
  | .nil => simp [Fields.subst, Fields.erase, Runtime.Fields.rename]
  | .cons F ℓ t =>
      simp [Fields.subst, Fields.erase, Runtime.Fields.rename, Fields.erase_subst F,
        Tm.erase_subst t]

end

/-- Instantiating the innermost binder by an atom erases to instantiating by
the atom's root. -/
theorem Tm.erase_substAtom {s : Sig} (u : Tm (s,x)) (a : Atom s) :
    (u.substAtom a).erase = u.erase.substVar a.root := by
  simp [Tm.substAtom, Tm.erase_subst, Runtime.Tm.substVar]

/-- Substituting the self binder of a stored field erases to the same
substitution on the runtime term. -/
theorem Tm.selfAt_erase {s : Sig} (t : Tm (s,x)) (y : BVar s .var) :
    (t.selfAt y).erase = t.erase.substVar y := by
  simp [Tm.selfAt, Tm.erase_rename, Runtime.Tm.substVar]

/-- Adjusting a continuation body to a stripped value only inserts casts, so
the erasure is unchanged. -/
theorem Tm.erase_adjust {s : Sig} (u : Tm (s,x)) (v : Value s) :
    (u.adjust v).erase = u.erase := by
  unfold Tm.adjust
  cases v.composite? with
  | none => rfl
  | some E => simp [Tm.erase_subst, Runtime.Tm.rename_id]

/-! ## Erasure of the machine's data -/

/-- Cast wrappers on a value are invisible to the erasure. -/
theorem Value.erase_core {s : Sig} : ∀ v : Value s, v.core.erase = v.erase
  | .lam _ _ => rfl
  | .obj _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.erase, Value.erase_core v]

/-- Store lookup commutes with erasure. -/
theorem Store.lookup_erase {s : Sig} :
    ∀ (σ : Store s) (x : BVar s .var), σ.erase.lookup x = (σ.lookup x).erase
  | .cons σ v, .here => by
      simp [Store.erase, Store.lookup, Runtime.Store.lookup, Value.erase_weaken]
  | .cons σ v, .there y => by
      simp [Store.erase, Store.lookup, Runtime.Store.lookup, Value.erase_weaken,
        Store.lookup_erase σ y]

/-- Field lookup commutes with erasure. -/
theorem Fields.erase_get? {s : Sig} :
    ∀ (F : Fields s) (ℓ : Label), F.erase.get? ℓ = (F.get? ℓ).map Tm.erase
  | .nil, ℓ => rfl
  | .cons F ℓ' t, ℓ => by
      by_cases h : ℓ = ℓ' <;>
        simp [Fields.erase, Fields.get?, Runtime.Fields.get?, h, Fields.erase_get? F ℓ]

/-- Every erased value is a runtime value. -/
theorem Value.erase_isValue {s : Sig} : ∀ v : Value s, Runtime.IsValue v.erase
  | .lam _ _ => .lam
  | .obj _ _ => .obj
  | .cast v _ => by simpa [Value.erase] using Value.erase_isValue v

/-! ## Store entries are literals -/

/-- Being a literal is stable under renaming. -/
theorem Value.isLiteral_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), v.IsLiteral → (v.rename ρ).IsLiteral
  | .lam _ _, _, _ => trivial
  | .obj _ _, _, _ => trivial
  | .cast _ _, _, h => h.elim

/-- Entries of a typed store are literals, in any scope. -/
theorem Store.Typed.lookup_isLiteral {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : Store.Typed σ Γ) : ∀ x : BVar s .var, (σ.lookup x).IsLiteral := by
  induction h with
  | nil => intro x; cases x
  | @cons s0 σ0 Γ0 v T hσ hlit hv ih =>
      intro x
      cases x with
      | here => exact Value.isLiteral_rename v _ hlit
      | there y => exact Value.isLiteral_rename _ _ (ih y)

/-- A literal whose erasure is a runtime lambda is a lambda. -/
theorem Value.erase_eq_lam {s : Sig} :
    ∀ (v : Value s) (t' : Runtime.Tm (s,x)), v.IsLiteral → v.erase = .lam t' →
      ∃ (S₀ : Ty s) (t₀ : Tm (s,x)), v = .lam S₀ t₀ ∧ t₀.erase = t'
  | .lam S t, t', _, h => ⟨S, t, rfl, by simpa [Value.erase] using h⟩
  | .obj _ _, t', _, h => by simp [Value.erase] at h
  | .cast _ _, _, hlit, _ => hlit.elim

/-- A literal whose erasure is a runtime object is an object. -/
theorem Value.erase_eq_obj {s : Sig} :
    ∀ (v : Value s) (F' : Runtime.Fields (s,x)), v.IsLiteral → v.erase = .obj F' →
      ∃ (W : Witnesses (s,x)) (F : Fields (s,x)), v = .obj W F ∧ F.erase = F'
  | .lam _ _, F', _, h => by simp [Value.erase] at h
  | .obj W F, F', _, h => ⟨W, F, rfl, by simpa [Value.erase] using h⟩
  | .cast _ _, _, hlit, _ => hlit.elim

end FCdot

namespace FCdot

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
  | castVal => exact Or.inl ⟨Or.inr ⟨_, _, rfl, Or.inl ⟨_, rfl⟩⟩, rfl, rfl⟩
  | castAtom => exact Or.inl ⟨Or.inr ⟨_, _, rfl, Or.inr ⟨_, rfl⟩⟩, rfl, rfl⟩
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
      simp only [State.erase, Tm.erase, Atom.root, Tm.erase_substAtom]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | appCastRefl hl hne hform hF =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.erase_substAtom]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | appCast hl hne hform =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.erase_substAtom, Atom.root]
      exact Runtime.Step.app (by rw [Store.lookup_erase, hl]; rfl)
  | proj hl hg =>
      refine Or.inr ?_
      simp only [State.erase, Tm.erase, Tm.selfAt_erase]
      refine Runtime.Step.proj (by rw [Store.lookup_erase, hl]; rfl) ?_
      rw [Fields.erase_get?, hg]
      rfl

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
  | .let _ _ => 0
  | .cast t _ => t.castDepth + 1

/-- Number of cast frames at the top of a continuation. -/
def Cont.castDepth : Cont s → Nat
  | .nil => 0
  | .cons _ (.let _) => 0
  | .cons K (.cast _) => K.castDepth + 1

/-- Cast-frame steps strictly decrease this measure: `castPush` trades one
head cast for one cast frame, and `castVal`/`castAtom` consume a frame. -/
def State.castMeasure (st : State s) : Nat := 2 * st.t.castDepth + st.K.castDepth

theorem State.not_castRedex_of_measure_zero {s : Sig} (st : State s)
    (h : st.castMeasure = 0) : ¬ st.CastRedex := by
  obtain ⟨σ, K, t⟩ := st
  rintro (⟨t0, e, ht⟩ | ⟨K0, e, hK, _⟩)
  · subst ht
    simp only [State.castMeasure, Tm.castDepth] at h
    omega
  · subst hK
    simp only [State.castMeasure, Cont.castDepth] at h
    omega

/-- A cast redex steps, without changing the erasure or the store, to a state
of strictly smaller cast measure. -/
theorem castRedex_steps {s : Sig} (st : State s) (h : st.CastRedex) :
    ∃ st' : State s, Step st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      st'.castMeasure < st.castMeasure := by
  obtain ⟨σ, K, t⟩ := st
  rcases h with ⟨t0, e, ht⟩ | ⟨K0, e, hK, hv⟩
  · subst ht
    refine ⟨⟨σ, .cons K (.cast e), t0⟩, .castPush, rfl, rfl, ?_⟩
    simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
    omega
  · subst hK
    rcases hv with ⟨v, hvt⟩ | ⟨a, hat⟩
    · subst hvt
      refine ⟨⟨σ, K0, .val (.cast v e)⟩, .castVal, rfl, rfl, ?_⟩
      simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
      omega
    · subst hat
      refine ⟨⟨σ, K0, .atom (.cast a e)⟩, .castAtom, rfl, rfl, ?_⟩
      simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
      omega

theorem Steps.head {s s' s'' : Sig} {st : State s} {st' : State s'} {st'' : State s''}
    (h : Step st st') (hs : Steps st' st'') : Steps st st'' := by
  induction hs with
  | refl => exact .tail .refl h
  | tail _ h2 ih => exact .tail (ih h) h2

/-- Every state reaches, by cast-frame steps only, a state with the same
erasure and store that is not a cast redex. -/
theorem castRedex_normalize {s : Sig} (st : State s) :
    ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex := by
  suffices key : ∀ (n : Nat) (st : State s), st.castMeasure ≤ n →
      ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
        ¬ st'.CastRedex from key st.castMeasure st (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro st hm
      exact ⟨st, .refl, rfl, rfl,
        State.not_castRedex_of_measure_zero st (Nat.le_zero.mp hm)⟩
  | succ n ih =>
      intro st hm
      by_cases hc : st.CastRedex
      · obtain ⟨st1, hstep, he1, hs1, hlt⟩ := castRedex_steps st hc
        obtain ⟨st2, hsteps, he2, hs2, hnc⟩ := ih st1 (by omega)
        exact ⟨st2, Steps.head hstep hsteps, by rw [he2, he1], by rw [hs2, hs1], hnc⟩
      · exact ⟨st, .refl, rfl, rfl, hc⟩

/-! ### Carrying typing through cast-frame normalization

Reflection of a runtime application step needs the head atom of the residual
application to be typed at a function type.  Cast-frame steps do not preserve
term typing on the nose (`castVal` and `castAtom` push a coercion into a
value or an atom, and the resulting wrapper is typed only because the frame
was), but they do preserve the weaker invariant below, which is all the
application case uses. -/

/-- Invariant along cast-frame steps: the running term is typed, or it is
already a value or an atom. -/
def State.CastInv (st : State s) (Γ : Ctx s) : Prop :=
  (∃ T, Tm.HasType Γ st.t T) ∨ (∃ v, st.t = .val v) ∨ (∃ a, st.t = .atom a)

/-- The cast-frame step of `castRedex_steps` preserves the invariant. -/
theorem castRedex_steps_inv {s : Sig} (st : State s) (Γ : Ctx s) (hq : st.CastInv Γ)
    (h : st.CastRedex) :
    ∃ st' : State s, Step st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      st'.castMeasure < st.castMeasure ∧ st'.CastInv Γ := by
  obtain ⟨σ, K, t⟩ := st
  rcases h with ⟨t0, e, ht⟩ | ⟨K0, e, hK, hv⟩
  · subst ht
    refine ⟨⟨σ, .cons K (.cast e), t0⟩, .castPush, rfl, rfl, ?_, ?_⟩
    · simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
      omega
    · rcases hq with ⟨T, hT⟩ | ⟨v, hvv⟩ | ⟨a, haa⟩
      · cases hT with
        | cast ht' _ => exact Or.inl ⟨_, ht'⟩
      · simp at hvv
      · simp at haa
  · subst hK
    rcases hv with ⟨v, hvt⟩ | ⟨a, hat⟩
    · subst hvt
      refine ⟨⟨σ, K0, .val (.cast v e)⟩, .castVal, rfl, rfl, ?_, Or.inr (Or.inl ⟨_, rfl⟩)⟩
      simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
      omega
    · subst hat
      refine ⟨⟨σ, K0, .atom (.cast a e)⟩, .castAtom, rfl, rfl, ?_, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      simp only [State.castMeasure, Tm.castDepth, Cont.castDepth]
      omega

/-- `castRedex_normalize`, carrying the invariant to the normal form. -/
theorem castRedex_normalize_inv {s : Sig} (st : State s) (Γ : Ctx s)
    (hq : st.CastInv Γ) :
    ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
      ¬ st'.CastRedex ∧ st'.CastInv Γ := by
  suffices key : ∀ (n : Nat) (st : State s), st.CastInv Γ → st.castMeasure ≤ n →
      ∃ st' : State s, Steps st st' ∧ st'.erase = st.erase ∧ st'.σ = st.σ ∧
        ¬ st'.CastRedex ∧ st'.CastInv Γ from key st.castMeasure st hq (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro st hq hm
      exact ⟨st, .refl, rfl, rfl,
        State.not_castRedex_of_measure_zero st (Nat.le_zero.mp hm), hq⟩
  | succ n ih =>
      intro st hq hm
      by_cases hc : st.CastRedex
      · obtain ⟨st1, hstep, he1, hs1, hlt, hq1⟩ := castRedex_steps_inv st Γ hq hc
        obtain ⟨st2, hsteps, he2, hs2, hnc, hq2⟩ := ih st1 hq1 (by omega)
        exact ⟨st2, Steps.head hstep hsteps, by rw [he2, he1], by rw [hs2, hs1], hnc, hq2⟩
      · exact ⟨st, .refl, rfl, rfl, hc, hq⟩

/-! ## Backward simulation -/

/-- The FCdot step realizing a runtime application step at a wrapped atom,
given the head form of the atom's casts. -/
theorem app_step_of_form {s : Sig} {σ : Store s} {K : Cont s} {a b : Atom s}
    {S₀ : Ty s} {t₀ : Tm (s,x)} {n : Nat} {a' : Atom s} {F : Form s}
    (hv : σ.lookup a.root = .lam S₀ t₀) (hne : a ≠ .var a.root)
    (hform : closedAtomForm σ n a = some (a', F))
    (hF : F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) :
    ∃ st' : State s, Step (⟨σ, K, .app a b⟩ : State s) st' ∧
      st'.erase = (⟨σ.erase, K.erase, t₀.erase.substVar b.root⟩ : Runtime.State s) := by
  rcases hF with hF | ⟨φ, hF⟩ | ⟨d, c, hF⟩
  · subst hF
    exact ⟨_, Step.appCastRefl hv hne hform (Or.inl rfl), by
      simp [State.erase, Tm.erase_substAtom]⟩
  · subst hF
    exact ⟨_, Step.appCastRefl hv hne hform (Or.inr ⟨φ, rfl⟩), by
      simp [State.erase, Tm.erase_substAtom]⟩
  · subst hF
    exact ⟨_, Step.appCast hv hne hform, by
      simp [State.erase, Tm.erase, Tm.erase_substAtom, Atom.root]⟩

/-- Reflection at a state that is not a cast redex: one FCdot step realizes
the runtime step.  `hcf` is the canonical-forms obligation and `hat` says
that a residual application is applied to a typed function atom. -/
theorem erase_reflect_aux {s s' : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {Γ : Ctx s}
    {r : Runtime.State s'} (hσ : Store.Typed σ Γ)
    (hcf : ∀ (a : Atom s) (S : Ty s) (T : Ty (s,x)), Atom.HasType Γ a (.pi S T) →
      a ≠ .var a.root → ∃ n a' F, closedAtomForm σ n a = some (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c))
    (hat : ∀ a b : Atom s, t = .app a b →
      ∃ (S : Ty s) (T : Ty (s,x)), Atom.HasType Γ a (.pi S T))
    (hnc : ¬ (State.CastRedex ⟨σ, K, t⟩))
    (h : Runtime.Step (State.erase ⟨σ, K, t⟩) r) :
    ∃ st' : State s', Step (⟨σ, K, t⟩ : State s) st' ∧ st'.erase = r := by
  cases t with
  | atom a =>
      cases K with
      | nil =>
          simp only [State.erase, Cont.erase, Tm.erase] at h
          exact (Runtime.Step.var_nil_inv h).elim
      | cons K0 f =>
          cases f with
          | «let» u =>
              simp only [State.erase, Cont.erase, Tm.erase] at h
              refine Runtime.Step.var_cons_inv (motive := fun s'' r' =>
                ∃ st' : State s'', Step (⟨σ, .cons K0 (.let u), .atom a⟩ : State s) st' ∧
                  st'.erase = r') h ?_
              exact ⟨_, .rename, by simp [State.erase, Tm.erase_substAtom]⟩
          | cast e => exact absurd (Or.inr ⟨K0, e, rfl, Or.inr ⟨a, rfl⟩⟩) hnc
  | val v =>
      cases K with
      | nil =>
          simp only [State.erase, Cont.erase, Tm.erase] at h
          exact (Runtime.Step.value_nil_inv (Value.erase_isValue v) h).elim
      | cons K0 f =>
          cases f with
          | «let» u =>
              simp only [State.erase, Cont.erase, Tm.erase] at h
              refine Runtime.Step.value_cons_inv (motive := fun s'' r' =>
                ∃ st' : State s'', Step (⟨σ, .cons K0 (.let u), .val v⟩ : State s) st' ∧
                  st'.erase = r') (Value.erase_isValue v) h ?_
              exact ⟨_, .alloc, by
                simp [State.erase, Store.erase, Cont.erase_weaken, Value.erase_core,
                  Tm.erase_adjust]⟩
          | cast e => exact absurd (Or.inr ⟨K0, e, rfl, Or.inl ⟨v, rfl⟩⟩) hnc
  | app a b =>
      simp only [State.erase, Tm.erase] at h
      refine Runtime.Step.app_inv (motive := fun s'' r' =>
        ∃ st' : State s'', Step (⟨σ, K, .app a b⟩ : State s) st' ∧ st'.erase = r') h ?_
      intro t' hlk
      rw [Store.lookup_erase] at hlk
      obtain ⟨S₀, t₀, hv, ht₀⟩ :=
        Value.erase_eq_lam _ t' (hσ.lookup_isLiteral a.root) hlk
      subst ht₀
      by_cases hne : a = .var a.root
      · have hstep : Step (⟨σ, K, .app (.var a.root) b⟩ : State s) ⟨σ, K, t₀.substAtom b⟩ :=
          Step.appVar hv
        rw [← hne] at hstep
        exact ⟨_, hstep, by simp [State.erase, Tm.erase_substAtom]⟩
      · obtain ⟨S, T, hpi⟩ := hat a b rfl
        obtain ⟨n, a', F, hform, hF⟩ := hcf a S T hpi hne
        exact app_step_of_form (K := K) (b := b) hv hne hform hF
  | proj a ℓ hh =>
      simp only [State.erase, Tm.erase] at h
      refine Runtime.Step.proj_inv (motive := fun s'' r' =>
        ∃ st' : State s'', Step (⟨σ, K, .proj a ℓ hh⟩ : State s) st' ∧ st'.erase = r') h ?_
      intro F' t' hlk hg
      rw [Store.lookup_erase] at hlk
      obtain ⟨W, F, hv, hF⟩ :=
        Value.erase_eq_obj _ F' (hσ.lookup_isLiteral a.root) hlk
      subst hF
      rw [Fields.erase_get?] at hg
      cases hgg : F.get? ℓ with
      | none => rw [hgg] at hg; simp at hg
      | some t0 =>
          rw [hgg] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          exact ⟨_, Step.proj hv hgg, by simp [State.erase, Tm.selfAt_erase, hg]⟩
  | «let» t u =>
      simp only [State.erase, Tm.erase] at h
      refine Runtime.Step.let_inv (motive := fun s'' r' =>
        ∃ st' : State s'', Step (⟨σ, K, .let t u⟩ : State s) st' ∧ st'.erase = r') h ?_
      exact ⟨_, .let, by simp [State.erase, Cont.erase]⟩
  | cast t e => exact absurd (Or.inl ⟨t, e, rfl⟩) hnc

/-- Backward simulation: every runtime step out of an erased state is
realized by a run of the FCdot machine, which first takes the pending
cast-frame steps. -/
theorem erase_reflect {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : Store.Typed st.σ Γ)
    (hcf : ∀ (a : Atom s) (S : Ty s) (T : Ty (s,x)), Atom.HasType Γ a (.pi S T) →
      a ≠ .var a.root → ∃ n a' F, closedAtomForm st.σ n a = some (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c))
    (hty : ∃ T, Tm.HasType Γ st.t T)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r := by
  obtain ⟨st1, hsteps, herase, hstore, hnc, hinv⟩ :=
    castRedex_normalize_inv st Γ (Or.inl hty)
  have hσ1 : Store.Typed st1.σ Γ := by rw [hstore]; exact hσ
  have hcf1 : ∀ (a : Atom s) (S : Ty s) (T : Ty (s,x)), Atom.HasType Γ a (.pi S T) →
      a ≠ .var a.root → ∃ n a' F, closedAtomForm st1.σ n a = some (a', F) ∧
        (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
    rw [hstore]; exact hcf
  have hat : ∀ a b : Atom s, st1.t = .app a b →
      ∃ (S : Ty s) (T : Ty (s,x)), Atom.HasType Γ a (.pi S T) := by
    intro a b hab
    rcases hinv with ⟨T, hT⟩ | ⟨v, hv⟩ | ⟨a0, ha0⟩
    · rw [hab] at hT
      cases hT with
      | app hpa _ => exact ⟨_, _, hpa⟩
    · rw [hab] at hv; simp at hv
    · rw [hab] at ha0; simp at ha0
  rw [← herase] at h
  suffices key : ∃ st' : State s', Step st1 st' ∧ st'.erase = r by
    obtain ⟨st', hstep, heq⟩ := key
    exact ⟨st', Steps.tail hsteps hstep, heq⟩
  clear hsteps herase hstore hσ hcf hty hinv
  obtain ⟨σ, K, t⟩ := st1
  exact erase_reflect_aux hσ1 hcf1 hat hnc h

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
theorem final_reflect {s : Sig} {st : State s} {Γ : Ctx s} (hσ : Store.Typed st.σ Γ)
    (h : st.erase.Final) : st.Final ∨ st.CastRedex := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨hK, ht⟩ := h
  cases t with
  | atom a =>
      cases K with
      | nil => exact Or.inl (Or.inr ⟨rfl, a, rfl⟩)
      | cons K0 f =>
          cases f with
          | «let» u => simp [State.erase, Cont.erase] at hK
          | cast e => exact Or.inr (Or.inr ⟨K0, e, rfl, Or.inr ⟨a, rfl⟩⟩)
  | val v =>
      cases K with
      | nil => exact Or.inl (Or.inl ⟨rfl, v, rfl⟩)
      | cons K0 f =>
          cases f with
          | «let» u => simp [State.erase, Cont.erase] at hK
          | cast e => exact Or.inr (Or.inr ⟨K0, e, rfl, Or.inl ⟨v, rfl⟩⟩)
  | app a b =>
      exfalso
      simp only [State.erase, Tm.erase] at ht
      rcases ht with hv | ⟨y, hy⟩
      · cases hv
      · cases hy
  | proj a ℓ =>
      exfalso
      simp only [State.erase, Tm.erase] at ht
      rcases ht with hv | ⟨y, hy⟩
      · cases hv
      · cases hy
  | «let» t u =>
      exfalso
      simp only [State.erase, Tm.erase] at ht
      rcases ht with hv | ⟨y, hy⟩
      · cases hv
      · cases hy
  | cast t e => exact Or.inr (Or.inl ⟨t, e, rfl⟩)

end FCdot
