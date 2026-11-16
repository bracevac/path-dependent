import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.Machine

/-!
# Selective DOT: typed machine states

The machine runs erased terms. A state is typed when its store, its term and
its continuation are the erasures of typed annotated ones. The annotations are
not part of the state: typing a state says that they exist.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-- A stored value has a type when it is the erasure of an annotated value that
has the type by its introduction rule. -/
def ValTy (Γ : Ctx s) (v : Value s) (T : Ty s) : Prop :=
  ∃ v' : Value s, v'.erase = v ∧ HasTy Γ (.val v') T

/-- Store typing: each value is typed in the context of the values before it. -/
inductive StoreTy : {s : Sig} → Ctx s → Store s → Prop where
  | nil : StoreTy .nil .nil
  | cons : StoreTy Γ σ → ValTy Γ v T → StoreTy (Γ.cons T) (σ.cons v)

/-- Continuation typing: `K` takes an answer of type `T` to an answer of type `U`.
Each frame is the erasure of a typed annotated term. -/
inductive ContTy : {s : Sig} → Ctx s → Cont s → Ty s → Ty s → Prop where
  | nil : ContTy Γ .nil T T
  | cons : u'.erase = u → HasTy (Γ.cons T) u' M.weaken → ContTy Γ K M U →
      ContTy Γ (.cons K u) T U

/-- A state is typed when its store is typed and its term and continuation are
erasures of typed annotated ones. -/
def StateTy (st : State s) : Prop :=
  ∃ (Γ : Ctx s) (t' : Tm s) (T U : Ty s),
    StoreTy Γ st.σ ∧ t'.erase = st.t ∧ HasTy Γ t' T ∧ ContTy Γ st.K T U

/-- The term under the casts of a typed term: it has the same erasure, it is
typed, and its type converts to the type of the whole. -/
theorem HasTy.strip {Γ : Ctx s} : ∀ {t : Tm s} {T : Ty s}, HasTy Γ t T →
    ∃ (t0 : Tm s) (T0 : Ty s), t0.erase = t.erase ∧ HasTy Γ t0 T0 ∧
      (∀ u c, t0 ≠ .cast u c) ∧ (T0 = T ∨ ∃ c, CertTy Γ c T0 T)
  | _, _, .path h => ⟨_, _, rfl, .path h, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .lam h => ⟨_, _, rfl, .lam h, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .app h1 h2 h3 => ⟨_, _, rfl, .app h1 h2 h3, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .obj h hd => ⟨_, _, rfl, .obj h hd, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .proj h => ⟨_, _, rfl, .proj h, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .let h1 h2 => ⟨_, _, rfl, .let h1 h2, (fun _ _ e => by cases e), .inl rfl⟩
  | _, _, .cast h hc =>
      match HasTy.strip h with
      | ⟨t0, T0, e, h0, hn, .inl eq⟩ => ⟨t0, T0, e, h0, hn, .inr ⟨_, eq ▸ hc⟩⟩
      | ⟨t0, T0, e, h0, hn, .inr ⟨_, hc0⟩⟩ => ⟨t0, T0, e, h0, hn, .inr ⟨_, .seq hc0 hc⟩⟩

end SelDot
