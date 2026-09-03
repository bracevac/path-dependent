import Coercions.FCdot.CanonicalTyped

/-!
# Resolution, chains, and depth monotonicity

Three independent pieces of infrastructure for the canonical-forms
development.

*Resolution.*  `Ctx.resolve` follows transparent definitions at the head of a
type with a fixed fuel budget `Γ.length + 1`.  That budget suffices because an
alias chain strictly increases the de Bruijn index of the selected binder: a
binder's definition mentions only the binder itself or older binders
(`Ctx.lookupDef_sel_le`), and guardedness rules out the binder itself
(`Ctx.WellDefined`).  Hence `resolve` is idempotent and commutes with one
unfolding step, and store contexts are well-defined
(`Store.Typed.wellDefined`).

*Chains.*  A well-typed chain of object-coercion steps composes: chains
concatenate (`ChainWellTyped_append`), a one-step chain closes to a typed
object coercion (`ChainWellTyped.close_typed`), and casting an atom through
every step of a chain transports it from the chain's source to its target
(`ChainWellTyped_chainAtom`).

*Depth.*  `FormTyped` is indexed by a proof-theoretic budget.  The applicative
clause of the object case quantifies over all input depths `j' ≤ j`, which
makes the whole predicate downward closed in the depth without any induction.
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
  | top => simp [Ty.weaken, Ty.rename] at h
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
    | top => rfl
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
      | top =>
          rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel m (by intro x ℓ h; cases h),
            Γ.resolveFuel_nonSel (n + 1 + m) (by intro x ℓ h; cases h)]
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
      | top => rw [Γ.resolveFuel_nonSel 0 (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel 1 (by intro x ℓ h; cases h)]
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
      | top => rw [Γ.resolveFuel_nonSel (n + 1) (by intro x ℓ h; cases h),
          Γ.resolveFuel_nonSel (n + 2) (by intro x ℓ h; cases h)]
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
    (hlit : v.IsLiteral) (hv : Value.HasType Γ v T) : v.witnesses.Guarded := by
  cases v with
  | lam S t => rfl
  | obj Tel W E F => exact (hv.obj_inv).2.1
  | cast v e => exact absurd hlit (by simp [Value.IsLiteral])

theorem Store.Typed.wellDefined {σ : Store s} {Γ : Ctx s} (h : Store.Typed σ Γ) :
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

/-! ## Chains of object-coercion steps -/

section

variable {s : Sig} {Γ : Ctx s}

/-- Cast an atom through every step of a chain, in order. -/
def ChainStep.chainAtom' : List (ChainStep s) → Atom s → Atom s
  | [], a => a
  | c :: cs, a => ChainStep.chainAtom' cs (.cast a c.close)

@[simp] theorem ChainStep.chainAtom'_nil (a : Atom s) :
    ChainStep.chainAtom' [] a = a := rfl

@[simp] theorem ChainStep.chainAtom'_cons (c : ChainStep s) (cs : List (ChainStep s))
    (a : Atom s) :
    ChainStep.chainAtom' (c :: cs) a = ChainStep.chainAtom' cs (.cast a c.close) := rfl

/-- Chains concatenate. -/
theorem ChainWellTyped_append :
    ∀ (cs₁ : List (ChainStep s)) {cs₂ : List (ChainStep s)} {S M T : Ty s},
      ChainWellTyped Γ cs₁ S M → ChainWellTyped Γ cs₂ M T →
      ChainWellTyped Γ (cs₁ ++ cs₂) S T := by
  intro cs₁
  induction cs₁ with
  | nil =>
      intro cs₂ S M T h1 h2
      rw [ChainWellTyped] at h1
      subst h1
      exact h2
  | cons c cs ih =>
      intro cs₂ S M T h1 h2
      cases c with
      | conv φ =>
          obtain ⟨S', hφ, hres, hrest⟩ := h1
          exact ⟨S', hφ, hres, ih hrest h2⟩
      | clos s' Tel m η =>
          obtain ⟨Δ, Tel₂, hm, hη, hS, hrest⟩ := h1
          exact ⟨Δ, Tel₂, hm, hη, hS, ih hrest h2⟩

/-- A one-step chain closes to a typed coercion. -/
theorem ChainWellTyped.close_typed {c : ChainStep s} {S T : Ty s}
    (h : ChainWellTyped Γ [c] S T) : LeCo.HasType Γ c.close S T := by
  cases c with
  | conv φ =>
      obtain ⟨S', hφ, _, hrest⟩ := h
      rw [ChainWellTyped] at hrest
      subst hrest
      exact .eqToLe hφ
  | clos s' Tel m η =>
      obtain ⟨Δ, Tel₂, hm, hη, hS, hrest⟩ := h
      rw [ChainWellTyped] at hrest
      subst hS
      subst hrest
      have hm' := Morphism.HasType.subst (σ := η.toSubst) (hη.lift (.opaque (.obj Tel))) hm
      simp only [Binding.rename_opaque, Ty.rename] at hm'
      exact .obj hm'

/-- Casting an atom through a well-typed chain transports it from the
chain's source to its target. -/
theorem ChainWellTyped_chainAtom :
    ∀ (cs : List (ChainStep s)) {S T : Ty s} {a : Atom s},
      ChainWellTyped Γ cs S T → Atom.HasType Γ a S →
      Atom.HasType Γ (ChainStep.chainAtom' cs a) T := by
  intro cs
  induction cs with
  | nil =>
      intro S T a h ha
      rw [ChainWellTyped] at h
      subst h
      exact ha
  | cons c cs ih =>
      intro S T a h ha
      cases c with
      | conv φ =>
          obtain ⟨S', hφ, hres, hrest⟩ := h
          refine ih hrest (Atom.HasType.cast ha ?_)
          exact ChainWellTyped.close_typed (c := .conv φ) ⟨S', hφ, hres, rfl⟩
      | clos s' Tel m η =>
          obtain ⟨Δ, Tel₂, hm, hη, hS, hrest⟩ := h
          subst hS
          refine ih hrest (Atom.HasType.cast ha ?_)
          exact ChainWellTyped.close_typed (c := .clos s' Tel m η) ⟨Δ, Tel₂, hm, hη, rfl, rfl⟩

end

/-! ## The fuel-loss budget -/

@[simp] theorem fuelLoss_zero : fuelLoss 0 = 0 := rfl

theorem fuelLoss_succ (n : Nat) : fuelLoss (n + 1) = 2 * fuelLoss n + 1 := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [fuelLoss, Nat.pow_succ]
  omega

theorem fuelLoss_mono {m n : Nat} (h : m ≤ n) : fuelLoss m ≤ fuelLoss n := by
  simp only [fuelLoss]
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) h) 1

theorem fuelLoss_add_le (a b : Nat) : fuelLoss a + fuelLoss b ≤ fuelLoss (max a b + 1) := by
  have ha : 2 ^ a ≤ 2 ^ (max a b) := Nat.pow_le_pow_right (by omega) (Nat.le_max_left a b)
  have hb : 2 ^ b ≤ 2 ^ (max a b) := Nat.pow_le_pow_right (by omega) (Nat.le_max_right a b)
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [fuelLoss, Nat.pow_succ]
  omega

/-! ## Depth monotonicity -/

section

variable {s : Sig} {σ : Store s} {Γ : Ctx s}

/-- Typedness of a proposition form is monotone in the form predicate. -/
theorem PropFormTypedWith_mono {FT FT' : Form s → Ty s → Ty s → Prop}
    (hm : ∀ F S T, FT F S T → FT' F S T) {P : Option (PropForm s)} {Q : Proposition s}
    {r : BVar s .var} (h : PropFormTypedWith σ Γ FT P Q r) :
    PropFormTypedWith σ Γ FT' P Q r := by
  cases P with
  | none => exact absurd h (by simp [PropFormTypedWith])
  | some Pf =>
      cases Pf with
      | le F =>
          cases Q with
          | le S T => exact hm _ _ _ h
          | eq S T => exact absurd h (by simp [PropFormTypedWith])
          | has ℓ => exact absurd h (by simp [PropFormTypedWith])
      | eq =>
          cases Q with
          | le S T => exact absurd h (by simp [PropFormTypedWith])
          | eq S T => exact h
          | has ℓ => exact absurd h (by simp [PropFormTypedWith])
      | has y ℓ =>
          cases Q with
          | le S T => exact absurd h (by simp [PropFormTypedWith])
          | eq S T => exact absurd h (by simp [PropFormTypedWith])
          | has ℓ' => exact h

/-- Typedness of a view is monotone in the form predicate. -/
theorem ViewTypedWith_mono {FT FT' : Form s → Ty s → Ty s → Prop}
    (hm : ∀ F S T, FT F S T → FT' F S T) {V : View s} {Tel : Telescope (s,x)} {a : Atom s}
    (h : ViewTypedWith σ Γ FT V Tel a) : ViewTypedWith σ Γ FT' V Tel a :=
  fun i P hP => PropFormTypedWith_mono hm (h i P hP)

/-- Form typedness is downward closed in the depth. -/
theorem FormTyped_mono {k k' : Nat} {F : Form s} {S T : Ty s}
    (hk : k' ≤ k) (h : FormTyped σ Γ k F S T) : FormTyped σ Γ k' F S T := by
  cases F with
  | bot => rw [FormTyped] at h ⊢; exact h
  | top => rw [FormTyped] at h ⊢; exact h
  | id => rw [FormTyped] at h ⊢; exact h
  | eqv φ => rw [FormTyped] at h ⊢; exact h
  | pi d c => rw [FormTyped] at h ⊢; exact h
  | obj cs =>
      cases k' with
      | zero =>
          cases k with
          | zero => exact h
          | succ j =>
              rw [FormTyped] at h
              rw [FormTyped]
              obtain ⟨Tel₁, Tel₂, h1, h2, h3, _⟩ := h
              exact ⟨Tel₁, Tel₂, h1, h2, h3⟩
      | succ j' =>
          cases k with
          | zero => omega
          | succ j =>
              rw [FormTyped] at h ⊢
              obtain ⟨Tel₁, Tel₂, h1, h2, h3, hcl⟩ := h
              refine ⟨Tel₁, Tel₂, h1, h2, h3, fun a ha V => ?_⟩
              obtain ⟨t, L, hcl'⟩ := hcl a ha V
              exact ⟨t, L, fun j'' ht hle => hcl' j'' ht (by omega)⟩

/-- The depth-independent content of form typedness. -/
theorem FormTyped_shape_mono {k : Nat} {F : Form s} {S T : Ty s}
    (h : FormTyped σ Γ k F S T) : FormTyped σ Γ 0 F S T :=
  FormTyped_mono (Nat.zero_le k) h

/-- Away from object forms, typedness does not depend on the depth at all. -/
theorem FormTyped_mono_nonObj {k k' : Nat} {F : Form s} {S T : Ty s}
    (hF : ∀ cs, F ≠ .obj cs) :
    FormTyped σ Γ k F S T ↔ FormTyped σ Γ k' F S T := by
  cases F with
  | bot => rw [FormTyped, FormTyped]
  | top => rw [FormTyped, FormTyped]
  | id => rw [FormTyped, FormTyped]
  | eqv φ => rw [FormTyped, FormTyped]
  | pi d c => rw [FormTyped, FormTyped]
  | obj cs => exact absurd rfl (hF cs)

theorem ViewTyped_mono {k k' : Nat} {V : View s} {Tel : Telescope (s,x)} {a : Atom s}
    (hk : k' ≤ k) (h : ViewTyped σ Γ k V Tel a) : ViewTyped σ Γ k' V Tel a :=
  ViewTypedWith_mono (fun _ _ _ hF => FormTyped_mono hk hF) h

theorem PropFormTyped_mono {k k' : Nat} {P : Option (PropForm s)} {Q : Proposition s}
    {r : BVar s .var} (hk : k' ≤ k) (h : PropFormTyped σ Γ k P Q r) :
    PropFormTyped σ Γ k' P Q r :=
  PropFormTypedWith_mono (fun _ _ _ hF => FormTyped_mono hk hF) h

theorem EnvCanon_mono {s' : Sig} {k k' : Nat} {η : Env s s'} {Δ : Ctx s'}
    (hk : k' ≤ k) (h : EnvCanon σ Γ k η Δ) : EnvCanon σ Γ k' η Δ :=
  ⟨h.1, fun y Tel hy => ViewTyped_mono hk (h.2.1 y Tel hy), h.2.2⟩

end

/-! ## Building views telescope by telescope -/

namespace Depth

/-- Indexing below the split point ignores the appended tail. -/
theorem nth?_append_lt : ∀ (V V' : View s) (i : Nat), i < V.length →
    View.nth? (V ++ V') i = View.nth? V i
  | [], _, i, h => by simp at h
  | _ :: V, V', 0, _ => rfl
  | _ :: V, V', i + 1, h => by
      simp only [List.cons_append, View.nth?]
      exact nth?_append_lt V V' i (by simpa using h)

/-- Indexing exactly at the split point returns the appended element. -/
theorem nth?_append_length : ∀ (V : View s) (P : PropForm s),
    View.nth? (V ++ [P]) V.length = some P
  | [], P => rfl
  | Q :: V, P => by
      simp only [List.cons_append, List.length_cons, View.nth?]
      exact nth?_append_length V P

end Depth

/-- A telescope position is below the telescope's length. -/
theorem Telescope.At.lt {s : Sig} {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P) : i < Tel.length := by
  induction h with
  | @here Tel P => simp [Telescope.length]
  | there _ ih => simp [Telescope.length]; omega

section

variable {s : Sig} {σ : Store s} {Γ : Ctx s}

@[simp] theorem PropFormTypedWith_le_iff {FT : Form s → Ty s → Ty s → Prop}
    {F : Form s} {S T : Ty s} {r : BVar s .var} :
    PropFormTypedWith σ Γ FT (some (.le F)) (.le S T) r ↔ FT F S T := Iff.rfl

@[simp] theorem PropFormTypedWith_eq_iff {FT : Form s → Ty s → Ty s → Prop}
    {S T : Ty s} {r : BVar s .var} :
    PropFormTypedWith σ Γ FT (some .eq) (.eq S T) r ↔ Γ.resolve S = Γ.resolve T := Iff.rfl

@[simp] theorem PropFormTypedWith_has_iff {FT : Form s → Ty s → Ty s → Prop}
    {y : BVar s .var} {ℓ ℓ' : Label} {r : BVar s .var} :
    PropFormTypedWith σ Γ FT (some (.has y ℓ)) (.has ℓ') r ↔
      (y = r ∧ ℓ = ℓ' ∧ σ.HasField r ℓ) := Iff.rfl

/-- The empty view is typed against the empty telescope. -/
theorem ViewTypedWith_nil {FT : Form s → Ty s → Ty s → Prop} {a : Atom s} :
    ViewTypedWith σ Γ FT [] (.nil : Telescope (s,x)) a := by
  intro i P h
  cases h

/-- Extending a view and its telescope in lockstep. -/
theorem ViewTypedWith_cons {FT : Form s → Ty s → Ty s → Prop} {V : View s}
    {Tel : Telescope (s,x)} {P : Proposition (s,x)} {P' : PropForm s} {a : Atom s}
    (hlen : V.length = Tel.length)
    (hV : ViewTypedWith σ Γ FT V Tel a)
    (hP : PropFormTypedWith σ Γ FT (some P') (P.substVar a.root) a.root) :
    ViewTypedWith σ Γ FT (V ++ [P']) (.cons Tel P) a := by
  intro i Q hQ
  cases hQ with
  | here =>
      rw [← hlen, Depth.nth?_append_length]
      exact hP
  | there hQ' =>
      rw [Depth.nth?_append_lt _ _ _ (by rw [hlen]; exact hQ'.lt)]
      exact hV i Q hQ'

end

end FCdot
