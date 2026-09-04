import Coercions.FCdot.CanonicalTyped
import Coercions.FCdot.Resolution

/-!
# Views, telescope by telescope

Helpers for building typed views: indexing an appended view, extending a
typed view by one proposition, instantiation of weakened propositions, and
field presence in a typed store.
-/

namespace FCdot

/-! ## Indexing appended views -/

theorem View.nth?_append_lt : ∀ (V V' : View s) (i : Nat), i < V.length →
    View.nth? (V ++ V') i = View.nth? V i
  | [], _, i, h => by simp at h
  | _ :: V, V', 0, _ => rfl
  | _ :: V, V', i + 1, h => by
      simp only [List.cons_append, View.nth?]
      exact View.nth?_append_lt V V' i (by simpa using h)

theorem View.nth?_append_length : ∀ (V : View s) (P : PropForm s),
    View.nth? (V ++ [P]) V.length = some P
  | [], P => rfl
  | Q :: V, P => by
      simp only [List.cons_append, List.length_cons, View.nth?]
      exact View.nth?_append_length V P

theorem View.nth?_lt_length : ∀ (V : View s) (i : Nat) (P : PropForm s),
    View.nth? V i = some P → i < V.length
  | [], _, _, h => by simp [View.nth?] at h
  | _ :: V, 0, _, _ => by simp
  | _ :: V, i + 1, P, h => by
      simp only [View.nth?] at h
      have := View.nth?_lt_length V i P h
      simp; omega

theorem Entries.nth?_append_length : ∀ (Es : List (Entry s)) (E : Entry s),
    Entries.nth? (Es ++ [E]) Es.length = some E
  | [], E => rfl
  | _ :: Es, E => by
      simp only [List.cons_append, List.length_cons, Entries.nth?]
      exact Entries.nth?_append_length Es E

theorem Entries.nth?_append_lt : ∀ (Es Es' : List (Entry s)) (i : Nat), i < Es.length →
    Entries.nth? (Es ++ Es') i = Entries.nth? Es i
  | [], _, i, h => by simp at h
  | _ :: Es, Es', 0, _ => rfl
  | _ :: Es, Es', i + 1, h => by
      simp only [List.cons_append, Entries.nth?]
      exact Entries.nth?_append_lt Es Es' i (by simpa using h)

/-- A telescope position is below the telescope's length. -/
theorem Telescope.At.lt {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel.At i P) : i < Tel.length := by
  induction h with
  | @here Tel P => simp [Telescope.length]
  | there _ ih => simp [Telescope.length]; omega

/-! ## Instantiating weakened propositions -/

theorem Ty.weaken_substVar (T : Ty s) (r : BVar s .var) :
    (T.weaken (k := .var))⟦r⟧ = T := by
  simp only [Ty.weaken, Ty.substVar, Ty.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Ty.rename_id T

theorem Proposition.weaken_substVar (P : Proposition s) (r : BVar s .var) :
    (P.weaken (k := .var))⟦r⟧ = P := by
  simp only [Proposition.weaken, Proposition.substVar, Proposition.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Proposition.rename_id P

/-! ## Injectivity of renaming -/

def Rename.Injective (ρ : Rename s1 s2) : Prop :=
  ∀ {k} (x y : BVar s1 k), ρ.var x = ρ.var y → x = y

theorem Rename.Injective.lift {ρ : Rename s1 s2} (h : ρ.Injective) {k : Kind} :
    (ρ.lift (k := k)).Injective := by
  intro k' x y hxy
  cases x <;> cases y <;> simp at hxy
  · rfl
  · rw [h _ _ hxy]

theorem Rename.succ_injective {s : Sig} {k : Kind} : (Rename.succ (s := s) (k := k)).Injective := by
  intro k' x y hxy
  simpa using hxy

mutual

theorem Ty.rename_inj {s1 s2 : Sig} (T T' : Ty s1) (ρ : Rename s1 s2) (hρ : ρ.Injective)
    (h : T.rename ρ = T'.rename ρ) : T = T' := by
  match T with
  | .top => cases T' <;> simp [Ty.rename] at h ⊢
  | .bot => cases T' <;> simp [Ty.rename] at h ⊢
  | .sel x ℓ =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨hρ _ _ h.1, h.2⟩
  | .pi S T =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ.lift hρ.lift h.2⟩
  | .obj Tel =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact Telescope.rename_inj Tel _ ρ.lift hρ.lift h

theorem Proposition.rename_inj {s1 s2 : Sig} (P P' : Proposition s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : P.rename ρ = P'.rename ρ) : P = P' := by
  match P with
  | .le S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ hρ h.2⟩
  | .eq S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ hρ h.2⟩
  | .has ℓ => cases P' <;> simp [Proposition.rename] at h ⊢ <;> exact h

theorem Telescope.rename_inj {s1 s2 : Sig} (Tel Tel' : Telescope s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : Tel.rename ρ = Tel'.rename ρ) : Tel = Tel' := by
  match Tel with
  | .nil => cases Tel' <;> simp [Telescope.rename] at h ⊢
  | .cons Tel P =>
      cases Tel' <;> simp [Telescope.rename] at h ⊢
      exact ⟨Telescope.rename_inj Tel _ ρ hρ h.1, Proposition.rename_inj P _ ρ hρ h.2⟩

end

theorem Telescope.weaken_inj {Tel₁ Tel₂ : Telescope s} {k : Kind}
    (h : (Tel₁.weaken (k := k)) = Tel₂↑) : Tel₁ = Tel₂ :=
  Telescope.rename_inj _ _ _ Rename.succ_injective h

@[simp] theorem Telescope.weaken_nil {s : Sig} {k : Kind} :
    (Telescope.nil (s := s)).weaken (k := k) = .nil := rfl

@[simp] theorem Telescope.weaken_cons (Tel : Telescope s) (P : Proposition s) {k : Kind} :
    (Tel.cons P).weaken (k := k) = Tel↑.cons P↑ := rfl

@[simp] theorem Proposition.weaken_le (S T : Ty s) {k : Kind} :
    (Proposition.le S T).weaken (k := k) = .le S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_eq (S T : Ty s) {k : Kind} :
    (Proposition.eq S T).weaken (k := k) = .eq S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_has (ℓ : Label) {k : Kind} :
    (Proposition.has (s := s) ℓ).weaken (k := k) = .has ℓ := rfl

theorem Telescope.weaken_substVar (Tel : Telescope s) (r : BVar s .var) :
    (Tel.weaken (k := .var))⟦r⟧ = Tel := by
  simp only [Telescope.weaken, Telescope.substVar, Telescope.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Telescope.rename_id Tel

/-- Instantiating a self-substituted, weakened proposition at any root gives
the original instantiation. -/
theorem Proposition.substVar_weaken_substVar (P : Proposition (s,x)) (r r' : BVar s .var) :
    ((P⟦r⟧).weaken (k := .var))⟦r'⟧ = P⟦r⟧ := by
  rw [Proposition.weaken_substVar]

theorem Telescope.At.weaken {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P) : (Tel.weaken (k := .var)).At i (P↑) := by
  induction h with
  | here => simp only [Telescope.weaken, Telescope.rename]; rw [← Telescope.length_rename]; exact .here
  | there _ ih => exact .there ih

theorem Telescope.At.rename_inv : {Tel : Telescope s1} → {ρ : Rename s1 s2} → {i : Nat} →
    {P : Proposition s2} → (Tel.rename ρ).At i P → ∃ P₀, Tel.At i P₀ ∧ P = P₀.rename ρ
  | .nil, _, _, _, h => by simp [Telescope.rename] at h; cases h
  | .cons Tel Q, ρ, i, P, h => by
      simp only [Telescope.rename] at h
      cases h with
      | here => exact ⟨Q, by rw [Telescope.length_rename]; exact .here, rfl⟩
      | there h' =>
          obtain ⟨P₀, hP₀, rfl⟩ := Telescope.At.rename_inv h'
          exact ⟨P₀, .there hP₀, rfl⟩

/-! ## Typed views -/

section
variable {σ : Store s} {Γ : Ctx s}

theorem ViewTyped_nil {r : BVar s .var} : ViewTyped Γ r σ [] (.nil : Telescope (s,x)) :=
  ⟨rfl, fun _ _ h => by cases h⟩

theorem ViewTyped_cons {V : View s} {Tel : Telescope (s,x)} {P : Proposition (s,x)}
    {P' : PropForm s} {r : BVar s .var}
    (hV : Γ ⊨[r, σ] V : Tel)
    (hP : PropFormTyped Γ r σ (some P') (P⟦r⟧)) :
    Γ ⊨[r, σ] (V ++ [P']) : (.cons Tel P) := by
  refine ⟨by simp [Telescope.length, hV.1], fun i Q hQ => ?_⟩
  cases hQ with
  | here =>
      rw [← hV.1, View.nth?_append_length]
      exact hP
  | there hQ' =>
      rw [View.nth?_append_lt _ _ _ (by rw [hV.1]; exact hQ'.lt)]
      exact hV.2 i Q hQ'

/-- A typed view has an entry at every telescope position. -/
theorem ViewTyped.nth?_isSome {V : View s} {Tel : Telescope (s,x)} {r : BVar s .var}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {P : Proposition (s,x)} (h : Tel.At i P) :
    ∃ Q, View.nth? V i = some Q := by
  have := hV.2 i P h
  cases hq : View.nth? V i with
  | none => rw [hq] at this; cases P <;> exact absurd this (by simp [PropFormTyped])
  | some Q => exact ⟨Q, rfl⟩

end

/-! ## Field presence in a typed store -/

theorem Fields.get?_isSome_of_mem : {F : Fields s} → {ℓ : Label} → ℓ ∈ F.labels →
    (F.get? ℓ).isSome
  | .nil, _, h => by simp [Fields.labels] at h
  | .cons F ℓ' t, ℓ, h => by
      simp only [Fields.labels, List.mem_cons] at h
      by_cases hℓ : ℓ = ℓ'
      · simp [Fields.get?, hℓ]
      · simp only [Fields.get?, hℓ, if_false]
        exact Fields.get?_isSome_of_mem (h.resolve_left hℓ)

end FCdot
