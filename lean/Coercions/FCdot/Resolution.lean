import Coercions.FCdot.Normalizer
import Coercions.FCdot.Typing
import Coercions.FCdot.TypingRename

/-!
# Resolution through transparent definitions

`Ctx.resolve` follows transparent definitions at the head of a type with a
fixed fuel budget `Γ.length + 1`.  That budget suffices because an alias
chain strictly increases the de Bruijn index of the selected binder: a
binder's definition mentions only the binder itself or older binders
(`Ctx.lookupDef_sel_le`), and guardedness rules out the binder itself
(`Ctx.WellDefined`).  Hence `resolve` is idempotent and commutes with one
unfolding step, and store contexts are well-defined
(`Store.Typed.wellDefined`).
-/

namespace FCdot

/-! ## Positions of bound variables -/

/-- The de Bruijn index of a bound variable (newest binder is `0`). -/
def BVar.toNat : BVar s k → Nat
  | .here => 0
  | .there y => y.toNat + 1

@[simp] theorem BVar.toNat_here : (BVar.here (s := s) (k := k)).toNat = 0 := rfl

@[simp] theorem BVar.toNat_there (y : BVar s k) :
    (BVar.there (k0 := k0) y).toNat = y.toNat + 1 := rfl

theorem BVar.toNat_lt : ∀ {s : Sig} {k : Kind} (x : BVar s k), x.toNat < s.length
  | _, _, .here => by simp [BVar.toNat]
  | _, _, .there y => by
      have := BVar.toNat_lt y
      simp [BVar.toNat]
      omega

theorem Ctx.length_eq : ∀ {s : Sig} (Γ : Ctx s), Γ.length = s.length
  | _, .nil => rfl
  | _, .cons Γ _ => by simp [Ctx.length, Ctx.length_eq Γ]

theorem BVar.toNat_lt_ctxLength {Γ : Ctx s} (x : BVar s .var) : x.toNat < Γ.length := by
  rw [Ctx.length_eq]; exact BVar.toNat_lt x

/-! ## Positions mentioned by definitions -/

/-- A weakened type is a selection only if it already was one. -/
theorem Ty.weaken_eq_sel {s : Sig} {k : Kind} {W : Ty s} {y : BVar (s,,k) .var} {ℓ : Label}
    (h : (W.weaken (k := k)) = .sel y ℓ) : ∃ z, W = .sel z ℓ ∧ y = .there z := by
  cases W with
  | bot => simp [Ty.weaken, Ty.rename] at h
  | sel z ℓ' =>
      refine ⟨z, ?_, ?_⟩
      · simp [Ty.weaken, Ty.rename] at h
        simp [h.2]
      · simp [Ty.weaken, Ty.rename] at h
        exact h.1.symm
  | pi => simp [Ty.weaken, Ty.rename] at h
  | obj => simp [Ty.weaken, Ty.rename] at h

/-- A definition of a binder mentions only that binder itself or strictly
older ones. -/
theorem Ctx.lookupDef_sel_le : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var) (ℓ ℓ' : Label)
    (y : BVar s .var), Γ.lookupDef x ℓ = some (.sel y ℓ') → y = x ∨ x.toNat < y.toNat
  | _, .cons _ (.transparent _ _ _), .here, ℓ, ℓ', y, _ => by
      cases y with
      | here => exact Or.inl rfl
      | there z => exact Or.inr (by simp [BVar.toNat])
  | _, .cons _ (.opaque _), .here, ℓ, ℓ', y, h => by
      simp at h
  | _, .cons Γ b, .there x', ℓ, ℓ', y, h => by
      rw [Ctx.lookupDef_there] at h
      cases hd : Γ.lookupDef x' ℓ with
      | none => rw [hd] at h; simp at h
      | some W =>
          rw [hd] at h
          simp only [Option.map_some] at h
          obtain ⟨z, hW, hy⟩ := Ty.weaken_eq_sel (Option.some.inj h)
          subst hW
          subst hy
          rcases Ctx.lookupDef_sel_le Γ x' ℓ ℓ' z hd with h1 | h1
          · exact Or.inl (by rw [h1])
          · exact Or.inr (by simp [BVar.toNat]; omega)

/-! ## Well-defined contexts -/

/-- Every transparent binding's definitions are guarded: a binder's definition
is never a bare name of that same binder. -/
def Ctx.WellDefined (Γ : Ctx s) : Prop :=
  ∀ (x : BVar s .var) (ℓ ℓ' : Label), Γ.lookupDef x ℓ ≠ some (.sel x ℓ')

/-- Under well-definedness, a definition mentions only strictly older binders. -/
theorem Ctx.lookupDef_sel_lt {Γ : Ctx s} (hwd : Γ.WellDefined)
    {x y : BVar s .var} {ℓ ℓ' : Label} (h : Γ.lookupDef x ℓ = some (.sel y ℓ')) :
    x.toNat < y.toNat := by
  rcases Ctx.lookupDef_sel_le Γ x ℓ ℓ' y h with h1 | h1
  · exact absurd (h1 ▸ h) (hwd x ℓ ℓ')
  · exact h1

/-! ## Basic resolution equations -/

theorem Ctx.resolveFuel_zero (Γ : Ctx s) (T : Ty s) : Γ.resolveFuel 0 T = T := rfl

/-- With any fuel, a type whose head is not a selection resolves to itself. -/
theorem Ctx.resolveFuel_nonSel (Γ : Ctx s) (n : Nat) {T : Ty s}
    (h : ∀ x ℓ, T ≠ .sel x ℓ) : Γ.resolveFuel n T = T := by
  cases n with
  | zero => rfl
  | succ n => cases T with
    | bot => rfl
    | sel x ℓ => exact absurd rfl (h x ℓ)
    | pi => rfl
    | obj => rfl

theorem Ctx.resolve_nonSel (Γ : Ctx s) {T : Ty s} (h : ∀ x ℓ, T ≠ .sel x ℓ) :
    Γ.resolve T = T := Γ.resolveFuel_nonSel _ h

@[simp] theorem Ctx.resolve_top (Γ : Ctx s) : Γ.resolve (.top : Ty s) = .top :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_bot (Γ : Ctx s) : Γ.resolve (.bot : Ty s) = .bot :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) :
    Γ.resolve (.pi S T) = .pi S T :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_obj (Γ : Ctx s) (Tel : Telescope (s,x)) :
    Γ.resolve (.obj Tel) = .obj Tel :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

theorem Ctx.resolveFuel_sel_none (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolveFuel n (.sel x ℓ) = .sel x ℓ := by
  cases n with
  | zero => rfl
  | succ n => simp [Ctx.resolveFuel, h]

theorem Ctx.resolve_sel_none (Γ : Ctx s) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolve (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_sel_none _ h

theorem Ctx.resolveFuel_sel_some (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    {W : Ty s} (h : Γ.lookupDef x ℓ = some W) :
    Γ.resolveFuel (n + 1) (.sel x ℓ) = Γ.resolveFuel n W := by
  simp [Ctx.resolveFuel, h]

/-- Resolution steps compose: resolution is following the alias chain. -/
theorem Ctx.resolveFuel_add (Γ : Ctx s) :
    ∀ (n m : Nat) (T : Ty s), Γ.resolveFuel m (Γ.resolveFuel n T) = Γ.resolveFuel (n + m) T
  | 0, m, T => by rw [Ctx.resolveFuel_zero, Nat.zero_add]
  | n + 1, m, T => by
      cases T with
      | bot =>
          rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel m (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel (n + 1 + m) (by intro x ℓ h; cases h)]
      | pi S T =>
          rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel m (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel (n + 1 + m) (by intro x ℓ h; cases h)]
      | obj Tel =>
          rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel m (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel (n + 1 + m) (by intro x ℓ h; cases h)]
      | sel x ℓ =>
          cases hd : Γ.lookupDef x ℓ with
          | none =>
              rw [Γ.resolveFuel_sel_none (n + 1) hd, Γ.resolveFuel_sel_none m hd,
                Γ.resolveFuel_sel_none (n + 1 + m) hd]
          | some W =>
              rw [Γ.resolveFuel_sel_some n hd,
                show n + 1 + m = (n + m) + 1 by omega, Γ.resolveFuel_sel_some (n + m) hd]
              exact Ctx.resolveFuel_add Γ n m W

/-! ## Termination of alias chains -/

/-- Fuel `n` suffices for `T` when every selection at the head of `T` is at a
binder whose index leaves at most `n` older binders to traverse. -/
def Ctx.FuelFor (Γ : Ctx s) (n : Nat) (T : Ty s) : Prop :=
  ∀ (x : BVar s .var) (ℓ : Label), T = .sel x ℓ → Γ.length ≤ n + x.toNat

theorem Ctx.fuelFor_of_nonSel {Γ : Ctx s} {n : Nat} {T : Ty s}
    (h : ∀ x ℓ, T ≠ .sel x ℓ) : Γ.FuelFor n T := by
  intro x ℓ hT; exact absurd hT (h x ℓ)

theorem Ctx.fuelFor_length {Γ : Ctx s} (T : Ty s) : Γ.FuelFor Γ.length T := by
  intro x ℓ _; omega

theorem Ctx.FuelFor.mono {Γ : Ctx s} {n m : Nat} {T : Ty s}
    (h : Γ.FuelFor n T) (hnm : n ≤ m) : Γ.FuelFor m T := by
  intro x ℓ hT
  have := h x ℓ hT
  omega

/-- Once the fuel suffices, one more unit changes nothing. -/
theorem Ctx.resolveFuel_succ_eq {Γ : Ctx s} (hwd : Γ.WellDefined) :
    ∀ (n : Nat) (T : Ty s), Γ.FuelFor n T → Γ.resolveFuel n T = Γ.resolveFuel (n + 1) T
  | 0, T, hf => by
      cases T with
      | bot => rw [Γ.resolveFuel_nonSel 0 (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel 1 (by intro x ℓ h; cases h)]
      | pi S T => rw [Γ.resolveFuel_nonSel 0 (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel 1 (by intro x ℓ h; cases h)]
      | obj Tel => rw [Γ.resolveFuel_nonSel 0 (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel 1 (by intro x ℓ h; cases h)]
      | sel x ℓ =>
          have h1 := hf x ℓ rfl
          have h2 : x.toNat < Γ.length := BVar.toNat_lt_ctxLength x
          omega
  | n + 1, T, hf => by
      cases T with
      | bot => rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel (n + 2) (by intro x ℓ h; cases h)]
      | pi S T => rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel (n + 2) (by intro x ℓ h; cases h)]
      | obj Tel => rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel (n + 2) (by intro x ℓ h; cases h)]
      | sel x ℓ =>
          have hx := hf x ℓ rfl
          cases hd : Γ.lookupDef x ℓ with
          | none => rw [Γ.resolveFuel_sel_none (n + 1) hd, Γ.resolveFuel_sel_none (n + 2) hd]
          | some W =>
              rw [Γ.resolveFuel_sel_some n hd, Γ.resolveFuel_sel_some (n + 1) hd]
              refine Ctx.resolveFuel_succ_eq hwd n W ?_
              intro y ℓ' hW
              subst hW
              have := Ctx.lookupDef_sel_lt hwd hd
              omega

/-- Any fuel beyond a sufficient amount gives the same result. -/
theorem Ctx.resolveFuel_eq_of_le {Γ : Ctx s} (hwd : Γ.WellDefined) {T : Ty s} :
    ∀ {n m : Nat}, Γ.FuelFor n T → n ≤ m → Γ.resolveFuel n T = Γ.resolveFuel m T := by
  intro n m hf hnm
  induction m with
  | zero => have : n = 0 := by omega
            rw [this]
  | succ m ih =>
      by_cases h : n = m + 1
      · rw [h]
      · have hnm' : n ≤ m := by omega
        rw [ih hnm']
        exact Ctx.resolveFuel_succ_eq hwd m T (hf.mono hnm')

/-- `Γ.length + 1` is enough fuel for every type. -/
theorem Ctx.resolveFuel_stable {Γ : Ctx s} (hwd : Γ.WellDefined) {n : Nat} {T : Ty s}
    (hn : Γ.length + 1 ≤ n) : Γ.resolveFuel n T = Γ.resolve T := by
  rw [Ctx.resolve]
  exact (Ctx.resolveFuel_eq_of_le hwd ((Ctx.fuelFor_length T).mono (by omega)) hn).symm

/-- Resolution is idempotent. -/
theorem Ctx.resolve_resolve {Γ : Ctx s} (hwd : Γ.WellDefined) (T : Ty s) :
    Γ.resolve (Γ.resolve T) = Γ.resolve T := by
  rw [Ctx.resolve, Ctx.resolve, Ctx.resolveFuel_add]
  exact Ctx.resolveFuel_stable hwd (by omega)

/-- Resolution commutes with one unfolding step. -/
theorem Ctx.resolve_sel_some {Γ : Ctx s} (hwd : Γ.WellDefined) {x : BVar s .var} {ℓ : Label}
    {W : Ty s} (h : Γ.lookupDef x ℓ = some W) :
    Γ.resolve (.sel x ℓ) = Γ.resolve W := by
  rw [Ctx.resolve, Γ.resolveFuel_sel_some Γ.length h]
  exact Ctx.resolveFuel_eq_of_le hwd (Ctx.fuelFor_length W) (by omega)

/-! ## Store contexts are well-defined -/

theorem Witnesses.guarded_get {s : Sig} :
    ∀ (W : Witnesses (s,x)), W.Guarded → ∀ (ℓ : Label), (W.get ℓ).isSelfName = false
  | .nil, _, _ => rfl
  | .cons W ℓ' T, h, ℓ => by
      rw [Witnesses.Guarded, Witnesses.all, Bool.and_eq_true] at h
      by_cases hℓ : ℓ = ℓ'
      · subst hℓ
        simpa [Witnesses.get] using h.1
      · rw [show Witnesses.get (.cons W ℓ' T) ℓ = W.get ℓ by simp [Witnesses.get, hℓ]]
        exact Witnesses.guarded_get W h.2 ℓ

theorem Value.witnesses_guarded {Γ : Ctx s} {v : Value s} {T : Ty s}
    (hlit : v.IsLiteral) (hv : Γ ⊢ᵥ v : T) : v.witnesses.Guarded := by
  cases v with
  | lam S t => rfl
  | obj W F => cases hv with
      | obj hg _ => exact hg
  | cast v e => exact absurd hlit (by simp [Value.IsLiteral])

theorem Store.Typed.wellDefined {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    Γ.WellDefined := by
  induction h with
  | nil => intro x ℓ ℓ' _; cases x
  | @cons s0 σ0 Γ0 v T hσ hlit hv ih =>
      intro x ℓ ℓ' hbad
      cases x with
      | here =>
          rw [Ctx.lookupDef_here_transparent] at hbad
          have hg := Witnesses.guarded_get _ (Value.witnesses_guarded hlit hv) ℓ
          rw [Option.some.inj hbad] at hg
          simp [Ty.isSelfName] at hg
      | there y =>
          rw [Ctx.lookupDef_there] at hbad
          cases hd : Γ0.lookupDef y ℓ with
          | none => rw [hd] at hbad; simp at hbad
          | some W =>
              rw [hd] at hbad
              simp only [Option.map_some] at hbad
              obtain ⟨z, hW, hy⟩ := Ty.weaken_eq_sel (Option.some.inj hbad)
              have hz : y = z := by injection hy
              subst hz
              subst hW
              exact absurd hd (ih y ℓ ℓ')


end FCdot
