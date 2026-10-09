import Coercions.Classifiers.FCdot.CanonicalForms

namespace Classifiers

/-!
# Runs of the machine are determined

A state has at most one successor: the shape of the state selects the rule,
the store lookups the premises read are functions, and the head form of a
chain of casts does not depend on the fuel it is computed at
(`closedAtomForm_det`).  So two runs from one state are prefixes of each
other (`Steps.linear`).

Only three rules extend the signature, and each of them extends it.  So a
run that ends at the signature it started from never allocates, and it leaves
the store as it found it (`Steps.store_eq`).  Together the two facts say that
every state a run reaches at a given signature has one and the same store.
That is how a statement about the store of the state a theorem matches to a
source state is proved: write out one run to a state at that signature, and
read the store off it (`Steps.store_of_reach`).

The roots of a variable in a typed store are the roots of the annotation of
the literal stored at it (`Store.Typed.root_var_iff`).  So a variable that
holds a pure literal has no root (`root_var_pure`).
-/

namespace FCdot

/-- **One step is determined.**  The successor of a state does not depend on
the derivation of the step, up to its signature. -/
theorem Step.det {s s₁ s₂ : Sig} {a : State s} {b : State s₁} {c : State s₂}
    (h₁ : a ⟶ b) (h₂ : a ⟶ c) : (⟨s₁, b⟩ : (s : Sig) × State s) = ⟨s₂, c⟩ := by
  cases h₁ <;> cases h₂ <;> first
    | rfl
    | (simp_all [Atom.root]; done)
    | (revert ‹closedAtomForm _ _ _ = some _›
       revert ‹closedAtomForm _ _ _ = some _›
       intro hA hB
       cases closedAtomForm_det hA hB
       simp_all; done)

/-- A run either stays where it is or begins with a step. -/
theorem Steps.head_cases {s s' : Sig} {a : State s} {b : State s'} (h : a ⟶* b) :
    (⟨s, a⟩ : (s : Sig) × State s) = ⟨s', b⟩ ∨
      ∃ (s₁ : Sig) (c : State s₁), (a ⟶ c) ∧ (c ⟶* b) := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
      rcases ih with he | ⟨s₁, c, hac, hcb⟩
      · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
        cases eq_of_heq he
        exact Or.inr ⟨_, _, step, .refl⟩
      · exact Or.inr ⟨s₁, c, hac, .tail hcb step⟩

/-- **Two runs from one state are prefixes of each other.** -/
theorem Steps.linear {s s₁ s₂ : Sig} {a : State s} {b : State s₁} {c : State s₂}
    (hb : a ⟶* b) (hc : a ⟶* c) : (b ⟶* c) ∨ (c ⟶* b) := by
  induction hc with
  | refl => exact Or.inr hb
  | tail _ step ih =>
      rcases ih hb with h | h
      · exact Or.inl (.tail h step)
      · rcases Steps.head_cases h with he | ⟨_, d, hcd, hdb⟩
        · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
          cases eq_of_heq he
          exact Or.inl (.tail .refl step)
        · obtain ⟨rfl, he⟩ := Sigma.mk.inj (Step.det hcd step)
          cases eq_of_heq he
          exact Or.inr hdb

/-- A step keeps the signature and the store, or it extends the signature. -/
theorem Step.sig {s s' : Sig} {a : State s} {b : State s'} (h : a ⟶ b) :
    (∃ e : s = s', e ▸ a.σ = b.σ) ∨ s.length < s'.length := by
  cases h <;> first
    | exact Or.inl ⟨rfl, rfl⟩
    | (right; simp only [List.length_cons]; omega)

/-- The same along a run. -/
theorem Steps.sig {s s' : Sig} {a : State s} {b : State s'} (h : a ⟶* b) :
    (∃ e : s = s', e ▸ a.σ = b.σ) ∨ s.length < s'.length := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | tail _ step ih =>
      rcases ih with ⟨rfl, h₁⟩ | h₁ <;> rcases Step.sig step with ⟨rfl, h₂⟩ | h₂
      · exact Or.inl ⟨rfl, h₁.trans h₂⟩
      · exact Or.inr h₂
      · exact Or.inr h₁
      · exact Or.inr (Nat.lt_trans h₁ h₂)

/-- **A run that ends at its own signature leaves the store as it found
it.**  Only the three allocating rules change the store, and each of them
extends the signature. -/
theorem Steps.store_eq {s : Sig} {a b : State s} (h : a ⟶* b) : a.σ = b.σ := by
  rcases Steps.sig h with ⟨e, he⟩ | hlt
  · exact he
  · exact absurd hlt (Nat.lt_irrefl _)

/-- **Every state a run reaches at a given signature has one store.**  Two
states reached from one state at the same signature have the same store.
`Steps.linear` puts one after the other, and `Steps.store_eq` reads the
store off the run between them. -/
theorem Steps.store_of_reach {s₀ s : Sig} {a : State s₀} {L st : State s}
    (hL : a ⟶* L) (hst : a ⟶* st) : st.σ = L.σ := by
  rcases Steps.linear hL hst with h | h
  · exact (Steps.store_eq h).symm
  · exact Steps.store_eq h

/-! ## Reading the roots of a variable off the store -/

/-- In a typed store, a variable has the roots of the annotation of the
literal stored at it. -/
theorem Store.Typed.root_var_iff {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    (x : BVar s .var) (a : CapAtom s) :
    Γ.Root a [CapAtom.var x] ↔ Γ.Root a (σ.lookup x).annot := by
  rw [← hσ.lookup_annot x]
  exact Ctx.Root_var Γ x a

/-- **A variable that holds a pure literal has no root.**  In a typed store,
a variable whose stored literal carries the empty annotation is rooted
nowhere. -/
theorem root_var_pure {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    {x : BVar s .var} (hx : (σ.lookup x).annot = []) (a : CapAtom s) :
    ¬ Γ.Root a [CapAtom.var x] := by
  intro h
  rw [hσ.root_var_iff, hx] at h
  obtain ⟨n, hn⟩ := h
  simp [Ctx.roots_eq_expand_caps, Ctx.expand] at hn

/-! ## A `let` of a cast value -/

/-- The four steps that bind a value under an answer cast: push the `let`
frame, push the cast frame, apply the cast to the value, and allocate the
value without its casts.  The body is adjusted to the casts the value
carried. -/
theorem Steps.letCastE {s : Sig} {σ : Store s} {K : Cont s} {v : Value s} {e : LeCo s}
    {u : Tm (s,x)} {U : CaptureSet s} {f : CapCo (s,x)} :
    (⟨σ, K, .let (.castE (.val v) (.plain e)) u U f⟩ : State s) ⟶*
      ⟨σ.cons (Value.cast v e).core, K.weaken, u.adjust (Value.cast v e)⟩ :=
  .tail (.tail (.tail (.tail .refl .let) .castEPush) .castEVal) .alloc

end FCdot

end Classifiers
