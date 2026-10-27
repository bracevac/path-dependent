import Coercions.PDot.FCp.Store

/-!
# The FCp machine (plan T.4)

A state is a store, a continuation of frames and a term.  The machine allocates only at a
top-level `let` of a value, substitutes path evidence at a `let` of a path, pushes casts into
frames and out again, and applies a path by its application view.

The application view `σ ⊢ P ⇓[n] (lam (z : S₀) t₀, F)` of T.7 belongs to the design round C0,
which may amend it, so the machine takes it as a parameter `V : AppView` (decision D7 of the groups
file).  `V σ P S₀ t₀ h` says that `P` reaches the closure `lam (z : S₀) t₀` of `σ` and that its casts
have the head `h`, with the fuel inside `V`.  `Step.det` asks `V.Det`, and the erasure asks
`V.Sound` (group g4).

The continuation typing `Γ ⊢ₖ K : T ⇒ V` reads the frames from the newest: a `let` frame takes
the hole's type to the body's, a cast frame takes it along its inclusion.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

inductive Cont.Typed : Ctx s → Cont s → Ty s → Ty s → Prop where                   -- Γ ⊢ₖ K : T ⇒ V
  -- K-Nil       binders T
  | nil : Cont.Typed Γ .nil T T
  -- K-Let       binders T U V K, z of u
  | lett : Tm.HasType (Γ.cons (.opaque T)) u U.weaken → Cont.Typed Γ K U V → Cont.Typed Γ (.cons K (.lett u)) T V
  -- K-Cast      binders e T U V K
  | cast : LeCo.HasType Γ e T U → Cont.Typed Γ K U V → Cont.Typed Γ (.cons K (.cast e)) T V

structure State (s : Sig) where                            -- ⟨σ, K, t⟩
  σ : Store s
  K : Cont s
  t : Tm s
def State.Typed (st : State s) (U : Ty s) : Prop :=
  ∃ (Γ : Ctx s) (T : Ty s), Store.Typed st.σ Γ ∧ Tm.HasType Γ st.t T ∧ Cont.Typed Γ st.K T U
def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ ((∃ v, st.t = .val v) ∨ ∃ P, st.t = .path P)

inductive AppHead : Sig → Type where                       -- the heads the machine reads (D7)
  | id : AppHead s                                          -- id
  | pi : LeCo s → LeCo (s,x) → AppHead s                    -- pi d (z. c)
  | eqv : EqCo s → AppHead s                                -- eqv φ
deriving instance DecidableEq for AppHead

/-- `V σ P S₀ t₀ h`: `P` reaches the closure `lam (z : S₀) t₀` of `σ`, and its casts have the head `h`.
The application view `σ ⊢ P ⇓[n] (lam (z : S₀) t₀, F)` of T.7, given to the machine as a parameter. -/
abbrev AppView : Type := ∀ {s : Sig}, Store s → PathCo s → Ty s → Tm (s,x) → AppHead s → Prop
def AppView.Det (V : AppView) : Prop :=
  ∀ {s : Sig} {σ : Store s} {P : PathCo s} {S₀ S₀' : Ty s} {t₀ t₀' : Tm (s,x)} {h h' : AppHead s},
    V σ P S₀ t₀ h → V σ P S₀' t₀' h' → S₀ = S₀' ∧ t₀ = t₀' ∧ h = h'

inductive Step (V : AppView) : State s → State s' → Prop where                    -- st ⟶ st'
  -- MS-Let      binders σ K t, z of u
  | lett : Step V ⟨σ, K, .lett t u⟩ ⟨σ, .cons K (.lett u), t⟩
  -- MS-CastPush binders σ K t e
  | castPush : Step V ⟨σ, K, .cast t e⟩ ⟨σ, .cons K (.cast e), t⟩
  -- MS-CastVal  binders σ K e v
  | castVal : Step V ⟨σ, .cons K (.cast e), .val v⟩ ⟨σ, K, .val (.cast v e)⟩
  -- MS-CastPath binders σ K e P
  | castPath : Step V ⟨σ, .cons K (.cast e), .path P⟩ ⟨σ, K, .path (.cast P e)⟩
  -- MS-LetVal   binders σ K v, z of u, the new store variable x = z
  | letVal : Step V ⟨σ, .cons K (.lett u), .val v⟩ ⟨σ.cons v.core, K.weaken, u.adjust v⟩
  -- MS-LetPath  binders σ K P, z of u
  | letPath : Step V ⟨σ, .cons K (.lett u), .path P⟩ ⟨σ, K, u.substCo P⟩
  -- MS-AppId    binders σ P S₀ K Q, z of t₀
  | appId : V σ P S₀ t₀ .id → Step V ⟨σ, K, .app P Q⟩ ⟨σ, K, t₀.substCo Q⟩
  -- MS-AppPi    binders σ P S₀ d K Q, z of t₀ c
  | appPi : V σ P S₀ t₀ (.pi d c) → Step V ⟨σ, K, .app P Q⟩ ⟨σ, K, .cast (t₀.substCo (.cast Q d)) (c.substCo Q)⟩
  -- MS-AppEq    binders σ P S₀ φ K Q, z of t₀
  | appEq : V σ P S₀ t₀ (.eqv φ) → Step V ⟨σ, K, .app P Q⟩ ⟨σ, K, .cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))⟩

inductive Steps (V : AppView) : State s → State s' → Prop where                   -- st ⟶* st'
  | refl : Steps V st st
  | tail : Steps V st st' → Step V st' st'' → Steps V st st''
def State.Stuck (V : AppView) (st : State s) : Prop := ¬ st.Final ∧ ¬ ∃ (s' : Sig) (st' : State s'), Step V st st'

/-- The machine is deterministic once the application view is. -/
theorem Step.det {V : AppView} (hV : V.Det) {st : State s} {st₁ : State s₁} {st₂ : State s₂} (h₁ : Step V st st₁) (h₂ : Step V st st₂) : s₁ = s₂ ∧ HEq st₁ st₂ := by
  cases h₁ with
  | lett => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | castPush => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | castVal => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | castPath => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | letVal => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | letPath => cases h₂ <;> exact ⟨rfl, HEq.rfl⟩
  | appId h => cases h₂ with
    | appId h' => obtain ⟨rfl, rfl, -⟩ := hV h h'; exact ⟨rfl, HEq.rfl⟩
    | appPi h' => nomatch (hV h h').2.2
    | appEq h' => nomatch (hV h h').2.2
  | appPi h => cases h₂ with
    | appId h' => nomatch (hV h h').2.2
    | appPi h' => obtain ⟨rfl, rfl, e⟩ := hV h h'; cases e; exact ⟨rfl, HEq.rfl⟩
    | appEq h' => nomatch (hV h h').2.2
  | appEq h => cases h₂ with
    | appId h' => nomatch (hV h h').2.2
    | appPi h' => nomatch (hV h h').2.2
    | appEq h' => obtain ⟨rfl, rfl, e⟩ := hV h h'; cases e; exact ⟨rfl, HEq.rfl⟩

end PDot.FCp
