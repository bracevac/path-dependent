import Coercions.DotMNF.Machine
import Coercions.Runtime

/-!
# Erasure of DOT-MNF into the shared runtime

Erasure drops types and type members and keeps everything else: paths become
variables, object literals keep their term members only, and the store and
the continuation are erased pointwise.  Erasure is the identity on
signatures.

The two theorems of milestone M2 are `DotMNF.erase_step` and
`DotMNF.erase_reflect`: the machine of §3.5 and the runtime machine of §4
are in lockstep, in both directions, with no administrative equivalence.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Concatenation of runtime field lists

`Runtime.Fields` is a snoc list whose outermost entry shadows on lookup, so
appending the fields of the right conjunct of a definition list outermost
matches `Defs.lookupTrm`, which prefers the right conjunct. -/

def appendFields : Runtime.Fields s → Runtime.Fields s → Runtime.Fields s
  | F, .nil => F
  | F, .cons G ℓ t => .cons (appendFields F G) ℓ t

theorem or_map {α β : Type} (f : α → β) (o o' : Option α) :
    (o.or o').map f = (o.map f).or (o'.map f) := by
  cases o <;> rfl

theorem appendFields_get? {s : Sig} (F G : Runtime.Fields s) (ℓ : Label) :
    (appendFields F G).get? ℓ = (G.get? ℓ).or (F.get? ℓ) := by
  match G with
  | .nil => rfl
  | .cons G ℓ' t =>
      simp only [appendFields, Runtime.Fields.get?, appendFields_get? F G ℓ]
      split <;> rfl

theorem appendFields_rename {s1 s2 : Sig} (F G : Runtime.Fields s1) (ρ : Rename s1 s2) :
    (appendFields F G).rename ρ = appendFields (F.rename ρ) (G.rename ρ) := by
  match G with
  | .nil => rfl
  | .cons G ℓ t =>
      simp only [appendFields, Runtime.Fields.rename, appendFields_rename F G ρ]

/-! ## Erasure of terms -/

mutual

def Tm.erase : Tm s → Runtime.Tm s
  | .path p => .var p.root
  | .val v => v.erase
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let t u => .let t.erase u.erase

def Value.erase : Value s → Runtime.Tm s
  | .obj d => .obj d.erase
  | .lam _ t => .lam t.erase

/-- Type members erase to nothing. -/
def Defs.erase : Defs s → Runtime.Fields s
  | .typ _ _ => .nil
  | .trm a t => .cons .nil a t.erase
  | .and d1 d2 => appendFields d1.erase d2.erase

end

def Store.erase : Store s → Runtime.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.erase v.erase

def Cont.erase : Cont s → Runtime.Cont s
  | .nil => .nil
  | .cons K u => .cons K.erase u.erase

def State.erase (st : State s) : Runtime.State s :=
  ⟨st.σ.erase, st.K.erase, st.t.erase⟩

/-! ## Erasure commutes with renaming -/

mutual

theorem Tm.erase_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).erase = t.erase.rename ρ := by
  match t with
  | .path p => simp only [Tm.rename, Tm.erase, Runtime.Tm.rename, Path.root_rename]
  | .val v => simp only [Tm.rename, Tm.erase, Value.erase_rename v ρ]
  | .app x y => simp only [Tm.rename, Tm.erase, Runtime.Tm.rename]
  | .proj x a => simp only [Tm.rename, Tm.erase, Runtime.Tm.rename]
  | .let t u =>
      simp only [Tm.rename, Tm.erase, Runtime.Tm.rename,
        Tm.erase_rename t ρ, Tm.erase_rename u ρ.lift]

theorem Value.erase_rename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    (v.rename ρ).erase = v.erase.rename ρ := by
  match v with
  | .obj d => simp only [Value.rename, Value.erase, Runtime.Tm.rename, Defs.erase_rename d ρ.lift]
  | .lam S t => simp only [Value.rename, Value.erase, Runtime.Tm.rename, Tm.erase_rename t ρ.lift]

theorem Defs.erase_rename {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2) :
    (d.rename ρ).erase = d.erase.rename ρ := by
  match d with
  | .typ A T => simp only [Defs.rename, Defs.erase, Runtime.Fields.rename]
  | .trm a t => simp only [Defs.rename, Defs.erase, Runtime.Fields.rename, Tm.erase_rename t ρ]
  | .and d1 d2 =>
      simp only [Defs.rename, Defs.erase, appendFields_rename,
        Defs.erase_rename d1 ρ, Defs.erase_rename d2 ρ]

end

theorem Tm.erase_substVar {s : Sig} (t : Tm (s,x)) (y : BVar s .var) :
    (t.substVar y).erase = t.erase.substVar y :=
  Tm.erase_rename t (Rename.subst y)

theorem Value.erase_weaken {s : Sig} (v : Value s) :
    (v.weaken).erase = v.erase.weaken :=
  Value.erase_rename v Rename.succ

theorem Cont.erase_rename {s1 s2 : Sig} (K : Cont s1) (ρ : Rename s1 s2) :
    (K.rename ρ).erase = K.erase.rename ρ := by
  match K with
  | .nil => rfl
  | .cons K u =>
      simp only [Cont.rename, Cont.erase, Runtime.Cont.rename,
        Cont.erase_rename K ρ, Tm.erase_rename u ρ.lift]

theorem Cont.erase_weaken {s : Sig} (K : Cont s) : (K.weaken).erase = K.erase.weaken :=
  Cont.erase_rename K Rename.succ

/-! ## Erasure commutes with store lookup and with definition lookup -/

theorem Store.lookup_erase {s : Sig} (σ : Store s) (x : BVar s .var) :
    σ.erase.lookup x = (σ.lookup x).erase := by
  match σ, x with
  | .cons _ v, .here =>
      simp only [Store.erase, Runtime.Store.lookup, Store.lookup, Value.erase_weaken]
  | .cons σ _, .there y =>
      simp only [Store.erase, Runtime.Store.lookup, Store.lookup, Value.erase_weaken,
        Store.lookup_erase σ y]

theorem Defs.erase_lookupTrm {s : Sig} (d : Defs s) (ℓ : Label) :
    d.erase.get? ℓ = (d.lookupTrm ℓ).map Tm.erase := by
  match d with
  | .typ A T => rfl
  | .trm a t =>
      simp only [Defs.erase, Defs.lookupTrm, Runtime.Fields.get?]
      split <;> rfl
  | .and d1 d2 =>
      simp only [Defs.erase, Defs.lookupTrm, appendFields_get?, or_map,
        Defs.erase_lookupTrm d1 ℓ, Defs.erase_lookupTrm d2 ℓ]

theorem Value.isValue_erase {s : Sig} (v : Value s) : Runtime.IsValue v.erase := by
  match v with
  | .obj d => exact Runtime.IsValue.obj
  | .lam S t => exact Runtime.IsValue.lam

/-! ## Simulation -/

/-- The projection case of `erase_step`, as a lemma so that the erased field
list is named rather than inferred. -/
theorem step_proj_erase {s : Sig} {σ : Store s} {K : Cont s} {x : BVar s .var} {a : Label}
    {d : Defs (s,x)} {t : Tm (s,x)}
    (hl : σ.lookup x = .obj d) (hd : d.lookupTrm a = some t) :
    Runtime.Step (State.erase ⟨σ, K, .proj x a⟩) (State.erase ⟨σ, K, t.substVar x⟩) := by
  simp only [State.erase, Tm.erase, Tm.erase_substVar]
  refine Runtime.Step.proj (F := d.erase) ?_ ?_
  · rw [Store.lookup_erase, hl]; rfl
  · rw [Defs.erase_lookupTrm, hd]; rfl

/-- Every source step erases to exactly one runtime step. -/
theorem erase_step {s s' : Sig} {st : State s} {st' : State s'} (h : Step st st') :
    Runtime.Step st.erase st'.erase := by
  cases h with
  | «let» =>
      simp only [State.erase, Tm.erase, Cont.erase]
      exact Runtime.Step.let
  | alloc =>
      simp only [State.erase, Tm.erase, Cont.erase, Store.erase, Cont.erase_weaken]
      exact Runtime.Step.alloc (Value.isValue_erase _)
  | rename =>
      simp only [State.erase, Tm.erase, Cont.erase, Path.root, Tm.erase_substVar]
      exact Runtime.Step.rename
  | app hl =>
      simp only [State.erase, Tm.erase, Tm.erase_substVar]
      refine Runtime.Step.app ?_
      rw [Store.lookup_erase, hl]
      rfl
  | proj hl hd => exact step_proj_erase hl hd

/-! ## Reflection

Every runtime step of an erased state is the erasure of a source step.  The
three interesting cases are factored out, because the case analysis on the
continuation duplicates them. -/

theorem reflect_let {s : Sig} {σ : Store s} {K : Cont s} {t : Tm s} {u : Tm (s,x)} :
    ∃ st' : State s, Step ⟨σ, K, .let t u⟩ st' ∧
      st'.erase = ⟨σ.erase, .cons K.erase u.erase, t.erase⟩ :=
  ⟨⟨σ, .cons K u, t⟩, Step.let, rfl⟩

theorem reflect_app {s : Sig} {σ : Store s} {K : Cont s} {x y : BVar s .var}
    {t₀ : Runtime.Tm (s,x)} (hl : σ.erase.lookup x = .lam t₀) :
    ∃ st' : State s, Step ⟨σ, K, .app x y⟩ st' ∧
      st'.erase = ⟨σ.erase, K.erase, t₀.substVar y⟩ := by
  rw [Store.lookup_erase] at hl
  cases hv : σ.lookup x with
  | obj d => rw [hv] at hl; simp [Value.erase] at hl
  | lam S t =>
      rw [hv] at hl
      simp only [Value.erase, Runtime.Tm.lam.injEq] at hl
      subst hl
      exact ⟨⟨σ, K, t.substVar y⟩, Step.app hv, by
        simp only [State.erase, Tm.erase_substVar]⟩

theorem reflect_proj {s : Sig} {σ : Store s} {K : Cont s} {x : BVar s .var} {ℓ : Label}
    {F : Runtime.Fields (s,x)} {t₀ : Runtime.Tm (s,x)}
    (hl : σ.erase.lookup x = .obj F) (hf : F.get? ℓ = some t₀) :
    ∃ st' : State s, Step ⟨σ, K, .proj x ℓ⟩ st' ∧
      st'.erase = ⟨σ.erase, K.erase, t₀.substVar x⟩ := by
  rw [Store.lookup_erase] at hl
  cases hv : σ.lookup x with
  | lam S t => rw [hv] at hl; simp [Value.erase] at hl
  | obj d =>
      rw [hv] at hl
      simp only [Value.erase, Runtime.Tm.obj.injEq] at hl
      subst hl
      rw [Defs.erase_lookupTrm] at hf
      cases hd : d.lookupTrm ℓ with
      | none => rw [hd] at hf; simp at hf
      | some t =>
          rw [hd] at hf
          injection hf with hf
          subst hf
          exact ⟨⟨σ, K, t.substVar x⟩, Step.proj hv hd, by
            simp only [State.erase, Tm.erase_substVar]⟩

/-- Every runtime step out of an erased state is the erasure of a source
step, at the same target state. -/
theorem erase_reflect {s s' : Sig} {st : State s} {r : Runtime.State s'}
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Step st st' ∧ st'.erase = r := by
  obtain ⟨σ, K, t⟩ := st
  match K, t with
  | .nil, .path (.var x) =>
      simp only [State.erase, Cont.erase, Tm.erase, Path.root] at h
      cases h
  | .nil, .val (.lam S t) =>
      simp only [State.erase, Cont.erase, Tm.erase, Value.erase] at h
      cases h
  | .nil, .val (.obj d) =>
      simp only [State.erase, Cont.erase, Tm.erase, Value.erase] at h
      cases h
  | .nil, .app x y =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | app hl => exact reflect_app hl
  | .nil, .proj x ℓ =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | proj hl hf => exact reflect_proj hl hf
  | .nil, .let t u =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | «let» => exact reflect_let
  | .cons K u, .path (.var x) =>
      simp only [State.erase, Cont.erase, Tm.erase, Path.root] at h
      cases h with
      | alloc hv => cases hv
      | rename =>
          exact ⟨⟨σ, K, u.substVar x⟩, Step.rename, by
            simp only [State.erase, Tm.erase_substVar]⟩
  | .cons K u, .val (.lam S t) =>
      simp only [State.erase, Cont.erase, Tm.erase, Value.erase] at h
      cases h with
      | alloc hv =>
          exact ⟨⟨.cons σ (.lam S t), K.weaken, u⟩, Step.alloc, by
            simp only [State.erase, Store.erase, Cont.erase_weaken, Value.erase]⟩
  | .cons K u, .val (.obj d) =>
      simp only [State.erase, Cont.erase, Tm.erase, Value.erase] at h
      cases h with
      | alloc hv =>
          exact ⟨⟨.cons σ (.obj d), K.weaken, u⟩, Step.alloc, by
            simp only [State.erase, Store.erase, Cont.erase_weaken, Value.erase]⟩
  | .cons K u, .app x y =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | alloc hv => cases hv
      | app hl => exact reflect_app hl
  | .cons K u, .proj x ℓ =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | alloc hv => cases hv
      | proj hl hf => exact reflect_proj hl hf
  | .cons K u, .let t u' =>
      simp only [State.erase, Cont.erase, Tm.erase] at h
      cases h with
      | alloc hv => cases hv
      | «let» => exact reflect_let

end DotMNF
