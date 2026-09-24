import Coercions.Separation.FCdot.Context
import Coercions.Separation.FCdot.RenameLemmas

namespace Separation

/-!
# Names, kills and the side conditions

Plan V-D, S0.2 and S0.3.  A kill is lexical: it flips the bit of a capture
binder in a typing context and never touches a store.  What a kill reads is
the list of *names* of a capture set, the binders a use of the set can reach.
Names are computed structurally, without fuel, so that the kernel decides
them.  They follow a term binder to its declared set, an instance or bounded
binder to its set, and a capture name to every witness its label reaches by
self reference.  They stop at every other capture binder, and a root opens
into every capture binder that is no root, at every level (plan-5h decision
38).

The side conditions of the typing rules read names and bits and never roots:
`Ctx.Accessible`, `Ctx.ConsumeOk`, `Ctx.KillOk`, `Ctx.AccessOnly` and
`Ctx.ArgSep`.  Each is decidable.  No side condition reads a mask.  Possible ownership is closed over the finite binder list in a
bounded number of rounds (`Ctx.ownClosure`), and so it is decidable too
(`Ctx.mayOwnB_iff`).

This module sits before `Typing.lean`, because the level rule asks its atom to
be access only.
-/

namespace FCdot

/-! ## The capture binders of a context -/

/-- Every capture binder of `Γ`. -/
def Ctx.capBinders : Ctx s → List (BVar s .cap)
  | .nil => []
  | .cons Γ _ => (Ctx.capBinders Γ).map .there
  | .consC Γ _ => .here :: (Ctx.capBinders Γ).map .there

@[simp] theorem Ctx.capBinders_cons (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).capBinders = Γ.capBinders.map .there := rfl

@[simp] theorem Ctx.capBinders_consC (Γ : Ctx s) (b : CapBound s) :
    (Γ.consC b).capBinders = .here :: Γ.capBinders.map .there := rfl

/-- Every capture binder is listed. -/
theorem Ctx.mem_capBinders {s : Sig} (Γ : Ctx s) : ∀ κ : BVar s .cap, κ ∈ Γ.capBinders := by
  induction Γ with
  | nil => intro κ; cases κ
  | cons Γ b ih =>
      intro κ
      cases κ with
      | there κ₀ =>
          simp only [Ctx.capBinders_cons, List.mem_map]
          exact ⟨κ₀, ih κ₀, rfl⟩
  | consC Γ b ih =>
      intro κ
      cases κ with
      | here => simp
      | there κ₀ =>
          simp only [Ctx.capBinders_consC, List.mem_cons, List.mem_map]
          exact Or.inr ⟨κ₀, ih κ₀, rfl⟩

/-! ## Weakening facts for atoms and sets -/

theorem CapAtom.weaken_inj {a b : CapAtom s}
    (h : CapAtom.weaken (k := k) a = CapAtom.weaken (k := k) b) : a = b :=
  CapAtom.rename_inj a b Rename.succ Rename.succ_injective h

theorem CapAtom.cvar_here_ne_weaken (a : CapAtom s) :
    CapAtom.cvar (BVar.here (s := s)) ≠ CapAtom.weaken (k := .cap) a := by
  cases a <;> simp [CapAtom.weaken, CapAtom.rename, Rename.succ]

theorem CapAtom.weaken_eq_top {a : CapAtom s} :
    CapAtom.weaken (k := k) a = CapAtom.top ↔ a = CapAtom.top := by
  cases a <;> simp [CapAtom.weaken, CapAtom.rename]

theorem CapAtom.cvar_there (κ : BVar s .cap) :
    (CapAtom.cvar (BVar.there (k0 := k) κ) : CapAtom (s,,k)) =
      CapAtom.weaken (k := k) (CapAtom.cvar κ) := rfl

theorem CaptureSet.singleton_cvar_there (κ : BVar s .cap) :
    ([CapAtom.cvar (BVar.there (k0 := k) κ)] : CaptureSet (s,,k)) =
      CaptureSet.weaken (k := k) [CapAtom.cvar κ] := rfl

theorem CaptureSet.mem_weaken {x : CapAtom (s,,k)} {L : CaptureSet s} :
    x ∈ CaptureSet.weaken (k := k) L ↔ ∃ y ∈ L, x = CapAtom.weaken (k := k) y := by
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem CaptureSet.weaken_mem_weaken {a : CapAtom s} {L : CaptureSet s} :
    CapAtom.weaken (k := k) a ∈ CaptureSet.weaken (k := k) L ↔ a ∈ L := by
  rw [CaptureSet.mem_weaken]
  constructor
  · rintro ⟨y, hy, hya⟩; rwa [CapAtom.weaken_inj hya]
  · intro h; exact ⟨a, h, rfl⟩

/-- A name in a weakened set is a weakened name. -/
theorem CaptureSet.cvar_mem_weaken {L : CaptureSet s} {κ : BVar (s,,k) .cap}
    (h : CapAtom.cvar κ ∈ CaptureSet.weaken (k := k) L) :
    ∃ κ₀, κ = .there κ₀ ∧ CapAtom.cvar κ₀ ∈ L := by
  obtain ⟨y, hy, hyx⟩ := CaptureSet.mem_weaken.mp h
  cases y with
  | cvar κ₀ =>
      simp only [CapAtom.weaken, CapAtom.rename, Rename.succ_var, CapAtom.cvar.injEq] at hyx
      exact ⟨κ₀, hyx, hy⟩
  | var _ => simp [CapAtom.weaken, CapAtom.rename] at hyx
  | name _ _ => simp [CapAtom.weaken, CapAtom.rename] at hyx
  | top => simp [CapAtom.weaken, CapAtom.rename] at hyx
  | mode _ _ => simp [CapAtom.weaken, CapAtom.rename] at hyx

theorem CaptureSet.nodup_weaken : ∀ {L : CaptureSet s}, L.Nodup →
    (CaptureSet.weaken (k := k) L).Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
      rw [List.nodup_cons] at h
      show (CapAtom.weaken (k := k) a :: CaptureSet.weaken (k := k) L).Nodup
      rw [List.nodup_cons, CaptureSet.weaken_mem_weaken]
      exact ⟨h.1, CaptureSet.nodup_weaken h.2⟩

/-- `W` lists capture binders only. -/
def CaptureSet.IsNames (W : CaptureSet s) : Prop := ∀ a ∈ W, ∃ κ, a = CapAtom.cvar κ

/-- The Bool twin of `IsNames`. -/
def CaptureSet.isNamesB (W : CaptureSet s) : Bool :=
  W.all fun
    | .cvar _ => true
    | _ => false

theorem CaptureSet.isNamesB_iff (W : CaptureSet s) : W.isNamesB = true ↔ W.IsNames := by
  unfold CaptureSet.isNamesB CaptureSet.IsNames
  rw [List.all_eq_true]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  cases a <;> simp

instance CaptureSet.IsNames.instDecidable (W : CaptureSet s) : Decidable W.IsNames :=
  decidable_of_iff _ (CaptureSet.isNamesB_iff W)

theorem CaptureSet.IsNames.weaken {W : CaptureSet s} (h : W.IsNames) :
    (CaptureSet.weaken (k := k) W).IsNames := by
  intro a ha
  obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp ha
  obtain ⟨κ, rfl⟩ := h y hy
  exact ⟨.there κ, rfl⟩

theorem CaptureSet.IsNames.rename {W : CaptureSet s1} (h : W.IsNames) (ρ : Rename s1 s2) :
    (W.rename ρ).IsNames := by
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  obtain ⟨κ, rfl⟩ := h y hy
  exact ⟨ρ.var κ, rfl⟩

theorem CaptureSet.elem_weaken (C : CaptureSet s) (a : CapAtom s) :
    (CaptureSet.weaken (k := k) C).elem (CapAtom.weaken (k := k) a) = C.elem a := by
  rw [Bool.eq_iff_iff, CaptureSet.elem_iff, CaptureSet.elem_iff, CaptureSet.weaken_mem_weaken]

/-- A weakened set never lists the newest capture binder. -/
theorem CaptureSet.elem_weaken_here (C : CaptureSet s) :
    (CaptureSet.weaken (k := .cap) C).elem (.cvar .here) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [CaptureSet.elem_iff, CaptureSet.mem_weaken] at h
  obtain ⟨y, -, hy⟩ := h
  exact CapAtom.cvar_here_ne_weaken y hy

/-! ## Kills -/

/-- The bound with its bit killed.  A flavour without a bit is unchanged. -/
def CapBound.kill : CapBound s → CapBound s
  | .loc _ C => .loc false C
  | .own _ W => .own false W
  | .param _ => .param false
  | b => b

/-- Flip the bit of one binder in place.  Nothing is renamed, because a bit
mentions no binder. -/
def Ctx.killAt : Ctx s → BVar s .cap → Ctx s
  | .consC Γ b, .here => .consC Γ b.kill
  | .consC Γ b, .there κ => .consC (Γ.killAt κ) b
  | .cons Γ b, .there κ => .cons (Γ.killAt κ) b

/-- Kill every binder of a list. -/
def Ctx.killNames (Γ : Ctx s) (D : List (BVar s .cap)) : Ctx s := D.foldl Ctx.killAt Γ

/-! ## Possible ownership, closed in bounded rounds -/

/-- The claims of an old binder on an old binder survive a term binder. -/
theorem Ctx.claimsB_cons_there (Γ : Ctx s) (b : Binding s) (h κ : BVar s .cap) :
    (Γ.cons b).claimsB (.there h) (.there κ) = Γ.claimsB h κ := by
  unfold Ctx.claimsB
  rw [show (Γ.cons b).lookupCap (.there h) = CapBound.weaken (k := .var) (Γ.lookupCap h)
    from rfl]
  cases Γ.lookupCap h with
  | own k W => exact CaptureSet.elem_weaken W (.cvar κ)
  | loc k C => exact CaptureSet.elem_weaken C (.cvar κ)
  | param k => simp [CapBound.weaken, CapBound.rename]
  | root => rfl
  | star => rfl
  | upper C => rfl
  | inst C => rfl

/-- And a capture binder. -/
theorem Ctx.claimsB_consC_there (Γ : Ctx s) (b : CapBound s) (h κ : BVar s .cap) :
    (Γ.consC b).claimsB (.there h) (.there κ) = Γ.claimsB h κ := by
  unfold Ctx.claimsB
  rw [show (Γ.consC b).lookupCap (.there h) = CapBound.weaken (k := .cap) (Γ.lookupCap h)
    from rfl]
  cases Γ.lookupCap h with
  | own k W => exact CaptureSet.elem_weaken W (.cvar κ)
  | loc k C => exact CaptureSet.elem_weaken C (.cvar κ)
  | param k => simp [CapBound.weaken, CapBound.rename]
  | root => rfl
  | star => rfl
  | upper C => rfl
  | inst C => rfl

/-- Nobody claims the newest capture binder. -/
theorem Ctx.claimsB_right_here (Γ : Ctx s) (b : CapBound s) (h : BVar (s,c) .cap) :
    (Γ.consC b).claimsB h .here = false := by
  unfold Ctx.claimsB
  cases h with
  | here =>
      rw [show (Γ.consC b).lookupCap .here = CapBound.weaken (k := .cap) b from rfl]
      cases b with
      | own k W => exact CaptureSet.elem_weaken_here W
      | loc k C => exact CaptureSet.elem_weaken_here C
      | param k => simp [CapBound.weaken, CapBound.rename]
      | root => rfl
      | star => rfl
      | upper C => rfl
      | inst C => rfl
  | there h₀ =>
      rw [show (Γ.consC b).lookupCap (.there h₀) = CapBound.weaken (k := .cap) (Γ.lookupCap h₀)
        from rfl]
      cases Γ.lookupCap h₀ with
      | own k W => exact CaptureSet.elem_weaken_here W
      | loc k C => exact CaptureSet.elem_weaken_here C
      | param k => simp [CapBound.weaken, CapBound.rename]
      | root => rfl
      | star => rfl
      | upper C => rfl
      | inst C => rfl

/-- A claim points to an older binder. -/
theorem Ctx.claimsB_depth : ∀ {s : Sig} (Γ : Ctx s) (h κ : BVar s .cap),
    Γ.claimsB h κ = true → h.depth < κ.depth
  | _, .consC _ _, _, .here, hh => by rw [Ctx.claimsB_right_here] at hh; cases hh
  | _, .consC _ _, .here, .there _, _ => by simp
  | _, .consC Γ b, .there h, .there κ, hh => by
      rw [Ctx.claimsB_consC_there] at hh
      have := Ctx.claimsB_depth Γ h κ hh
      simp only [BVar.depth_there]
      omega
  | _, .cons Γ b, .there h, .there κ, hh => by
      rw [Ctx.claimsB_cons_there] at hh
      have := Ctx.claimsB_depth Γ h κ hh
      simp only [BVar.depth_there]
      omega

/-- So possible ownership points to older binders too. -/
theorem Ctx.MayOwn.depth {Γ : Ctx s} {h κ : BVar s .cap} (hm : Γ.MayOwn h κ) :
    h.depth < κ.depth := by
  induction hm with
  | direct hd => exact Ctx.claimsB_depth Γ _ _ hd
  | trans _ _ ih₁ ih₂ => omega

/-- One round of the closure: every binder a listed binder claims. -/
def Ctx.ownStep (Γ : Ctx s) (L : List (BVar s .cap)) : List (BVar s .cap) :=
  L ++ Γ.capBinders.filter fun κ => L.any fun h => Γ.claimsB h κ

/-- `D` and every name a name of `D` may own.  A claim always points to an
older binder, so `Γ.capBinders.length` rounds reach the fixed point
(`Ctx.mem_ownClosure`).  The round is `Ctx.ownStep`, so this is the plan's
`Nat.repeat (fun L => L ++ ...)` by unfolding. -/
def Ctx.ownClosure (Γ : Ctx s) (D : List (BVar s .cap)) : List (BVar s .cap) :=
  Nat.repeat Γ.ownStep Γ.capBinders.length D

theorem Ctx.mem_ownStep {Γ : Ctx s} {L : List (BVar s .cap)} {κ : BVar s .cap} :
    κ ∈ Γ.ownStep L ↔ κ ∈ L ∨ ∃ h ∈ L, Γ.claimsB h κ = true := by
  unfold Ctx.ownStep
  rw [List.mem_append, List.mem_filter, List.any_eq_true]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨Γ.mem_capBinders κ, h⟩

/-- `Nat.repeat` unfolds on the inside too. -/
theorem Nat.repeat_succ_inner {α : Type} (f : α → α) : ∀ (n : Nat) (a : α),
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a)
  | 0, _ => rfl
  | n + 1, a => by
      show f (Nat.repeat f (n + 1) a) = f (Nat.repeat f n (f a))
      rw [Nat.repeat_succ_inner f n a]

theorem Ctx.ownIter_mono {Γ : Ctx s} {D : List (BVar s .cap)} {κ : BVar s .cap} :
    ∀ {k k' : Nat}, k ≤ k' → κ ∈ Nat.repeat Γ.ownStep k D → κ ∈ Nat.repeat Γ.ownStep k' D
  | k, 0, hk, h => by rw [Nat.le_zero.mp hk] at h; exact h
  | k, k' + 1, hk, h => by
      rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
      · exact Ctx.mem_ownStep.mpr (Or.inl (Ctx.ownIter_mono (Nat.le_of_lt_succ hlt) h))
      · rw [show k = k' + 1 by omega] at h; exact h

theorem Ctx.ownIter_sound {Γ : Ctx s} {D : List (BVar s .cap)} :
    ∀ (k : Nat) (κ : BVar s .cap), κ ∈ Nat.repeat Γ.ownStep k D →
      κ ∈ D ∨ ∃ h ∈ D, Γ.MayOwn h κ
  | 0, _, h => Or.inl h
  | k + 1, κ, h => by
      rcases Ctx.mem_ownStep.mp h with h | ⟨c, hc, hcl⟩
      · exact Ctx.ownIter_sound k κ h
      · rcases Ctx.ownIter_sound k c hc with hc | ⟨h₀, hh₀, hm⟩
        · exact Or.inr ⟨c, hc, .direct hcl⟩
        · exact Or.inr ⟨h₀, hh₀, .trans hm (.direct hcl)⟩

/-- A chain of claims of a given length. -/
inductive Ctx.ClaimChain (Γ : Ctx s) : Nat → BVar s .cap → BVar s .cap → Prop where
  | one : Γ.claimsB h κ = true → Γ.ClaimChain 1 h κ
  | cons : Γ.claimsB h c = true → Γ.ClaimChain n c κ → Γ.ClaimChain (n + 1) h κ

theorem Ctx.ClaimChain.append {Γ : Ctx s} {h κ κ' : BVar s .cap} {n m : Nat}
    (h₁ : Γ.ClaimChain n h κ) (h₂ : Γ.ClaimChain m κ κ') : Γ.ClaimChain (n + m) h κ' := by
  induction h₁ with
  | one hc => rw [Nat.add_comm]; exact .cons hc h₂
  | cons hc _ ih => rw [Nat.add_right_comm]; exact .cons hc (ih h₂)

theorem Ctx.MayOwn.chain {Γ : Ctx s} {h κ : BVar s .cap} (hm : Γ.MayOwn h κ) :
    ∃ n, Γ.ClaimChain n h κ := by
  induction hm with
  | direct hd => exact ⟨1, .one hd⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨n, hn⟩ := ih₁
      obtain ⟨m, hm⟩ := ih₂
      exact ⟨n + m, hn.append hm⟩

/-- The capture binders at depth `d` or deeper. -/
def Ctx.capCountFrom (Γ : Ctx s) (d : Nat) : Nat :=
  (Γ.capBinders.filter fun κ => decide (d ≤ κ.depth)).length

theorem List.length_filter_le_of_imp {α : Type} {p q : α → Bool} :
    ∀ (L : List α), (∀ a ∈ L, p a = true → q a = true) →
      (L.filter p).length ≤ (L.filter q).length
  | [], _ => Nat.le_refl _
  | a :: L, h => by
      have ih := List.length_filter_le_of_imp L (fun b hb => h b (List.mem_cons_of_mem a hb))
      have ha := h a (List.mem_cons_self ..)
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- Strictly more when one element passes the second test and not the first. -/
theorem List.length_filter_lt_of_imp {α : Type} {p q : α → Bool} :
    ∀ (L : List α), (∀ a ∈ L, p a = true → q a = true) →
      (∃ a ∈ L, q a = true ∧ p a = false) →
      (L.filter p).length < (L.filter q).length
  | [], _, ⟨_, ha, _⟩ => by simp at ha
  | a :: L, h, ⟨b, hb, hqb, hpb⟩ => by
      have hle := List.length_filter_le_of_imp L (fun c hc => h c (List.mem_cons_of_mem a hc))
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [hqb, hpb]; omega
      · have ih := List.length_filter_lt_of_imp L
          (fun c hc => h c (List.mem_cons_of_mem a hc)) ⟨b, hb, hqb, hpb⟩
        have ha := h a (List.mem_cons_self ..)
        cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem Ctx.capCountFrom_anti (Γ : Ctx s) {d d' : Nat} (h : d ≤ d') :
    Γ.capCountFrom d' ≤ Γ.capCountFrom d :=
  List.length_filter_le_of_imp _ (fun κ _ hk => by simp at hk ⊢; omega)

theorem Ctx.capCountFrom_step (Γ : Ctx s) (κ : BVar s .cap) :
    Γ.capCountFrom (κ.depth + 1) < Γ.capCountFrom κ.depth :=
  List.length_filter_lt_of_imp _ (fun c _ hc => by simp at hc ⊢; omega)
    ⟨κ, Γ.mem_capBinders κ, by simp, by simp⟩

theorem Ctx.capCountFrom_le (Γ : Ctx s) (d : Nat) : Γ.capCountFrom d ≤ Γ.capBinders.length :=
  List.length_filter_le _ _

/-- A chain of `n` claims from `h` passes `n` binders deeper than `h`. -/
theorem Ctx.ClaimChain.length_le {Γ : Ctx s} {n : Nat} {h κ : BVar s .cap}
    (hc : Γ.ClaimChain n h κ) : n ≤ Γ.capCountFrom (h.depth + 1) := by
  induction hc with
  | @one h' κ' hcl =>
      have hd := Ctx.claimsB_depth Γ _ _ hcl
      have h1 := Γ.capCountFrom_anti (show h'.depth + 1 ≤ κ'.depth from hd)
      have h2 := Γ.capCountFrom_step κ'
      omega
  | @cons h' c κ' n' hcl _ ih =>
      have hd := Ctx.claimsB_depth Γ _ _ hcl
      have h1 := Γ.capCountFrom_anti (show h'.depth + 1 ≤ c.depth from hd)
      have h2 := Γ.capCountFrom_step c
      omega

/-- A chain of `n` claims from a listed binder lands in the `n`-th round. -/
theorem Ctx.ClaimChain.mem_iter {Γ : Ctx s} {n : Nat} {h κ : BVar s .cap}
    (hc : Γ.ClaimChain n h κ) : ∀ {D : List (BVar s .cap)}, h ∈ D →
      κ ∈ Nat.repeat Γ.ownStep n D := by
  induction hc with
  | one hcl => intro D hD; exact Ctx.mem_ownStep.mpr (Or.inr ⟨_, hD, hcl⟩)
  | @cons h' c κ' n' hcl _ ih =>
      intro D hD
      rw [Nat.repeat_succ_inner]
      exact ih (Ctx.mem_ownStep.mpr (Or.inr ⟨h', hD, hcl⟩))

/-- **The closure is possible ownership.** -/
theorem Ctx.mem_ownClosure {Γ : Ctx s} {D : List (BVar s .cap)} {κ : BVar s .cap} :
    κ ∈ Γ.ownClosure D ↔ κ ∈ D ∨ ∃ h ∈ D, Γ.MayOwn h κ := by
  constructor
  · exact Ctx.ownIter_sound _ κ
  · rintro (h | ⟨h, hD, hm⟩)
    · exact Ctx.ownIter_mono (Nat.zero_le _) h
    · obtain ⟨n, hn⟩ := hm.chain
      have hle := hn.length_le
      have hcap := Γ.capCountFrom_le (h.depth + 1)
      exact Ctx.ownIter_mono (by omega) (hn.mem_iter hD)

/-- The Bool twin of `MayOwn`. -/
def Ctx.mayOwnB (Γ : Ctx s) (h κ : BVar s .cap) : Bool :=
  decide (κ ∈ Γ.ownClosure [h] ∧ κ ≠ h)

theorem Ctx.mayOwnB_iff {Γ : Ctx s} {h κ : BVar s .cap} :
    Γ.mayOwnB h κ = true ↔ Γ.MayOwn h κ := by
  unfold Ctx.mayOwnB
  rw [decide_eq_true_iff, Ctx.mem_ownClosure]
  constructor
  · rintro ⟨h₁ | ⟨h', hh', hm⟩, hne⟩
    · exact absurd (List.mem_singleton.mp h₁) hne
    · rw [List.mem_singleton.mp hh'] at hm; exact hm
  · intro hm
    refine ⟨Or.inr ⟨h, List.mem_singleton_self h, hm⟩, fun he => ?_⟩
    have := hm.depth
    rw [he] at this
    exact Nat.lt_irrefl _ this

instance Ctx.MayOwn.instDecidable (Γ : Ctx s) (h κ : BVar s .cap) : Decidable (Γ.MayOwn h κ) :=
  decidable_of_iff _ Ctx.mayOwnB_iff

instance Ctx.Related.instDecidable (Γ : Ctx s) (κ₁ κ₂ : BVar s .cap) :
    Decidable (Γ.Related κ₁ κ₂) := by
  unfold Ctx.Related; infer_instance

/-! ## Masking, consumability and distinctness -/

/-- Masked: some heir owns it.  Decidable over the finite binder list. -/
def Ctx.Masked (Γ : Ctx s) (κ : BVar s .cap) : Prop :=
  Γ.capBinders.any (fun h => Γ.ownsB h κ) = true

instance Ctx.Masked.instDecidable (Γ : Ctx s) (κ : BVar s .cap) : Decidable (Γ.Masked κ) := by
  unfold Ctx.Masked; infer_instance

/-- A name that a use may consume here: a consumable flavour and a live bit.
It reads no mask (plan-5h decision 38), so every judgment survives an heir
the machine appends, and a masked name is refused by the clause of
`State.TypedAt`. -/
def Ctx.Consumable (Γ : Ctx s) (κ : BVar s .cap) : Prop :=
  (Γ.lookupCap κ).consumable = true ∧ Γ.BitLive κ

instance Ctx.Consumable.instDecidable (Γ : Ctx s) (κ : BVar s .cap) :
    Decidable (Γ.Consumable κ) := by
  unfold Ctx.Consumable Ctx.BitLive; infer_instance

/-! ## Effective liveness (plan-5h decision 39)

A killed name that a live heir owns is reached through that heir, so access
reads it as live.  Consumption keeps reading the bit (`Ctx.Consumable`), so a
transferred name is never consumable again. -/

/-- A live bit, or an heir that owns the binder and is itself effectively
live. -/
inductive Ctx.EffLive (Γ : Ctx s) : BVar s .cap → Prop where
  | live {κ : BVar s .cap} : Γ.BitLive κ → Γ.EffLive κ
  | owned {h κ : BVar s .cap} : Γ.ownsB h κ = true → Γ.EffLive h → Γ.EffLive κ

/-- The Bool twin with fuel. -/
def Ctx.effLiveN (Γ : Ctx s) : Nat → BVar s .cap → Bool
  | 0, κ => (Γ.lookupCap κ).live
  | n+1, κ => (Γ.lookupCap κ).live ||
      Γ.capBinders.any (fun h => Γ.ownsB h κ && Γ.effLiveN n h)

/-- An owner is younger than what it owns (`Ctx.claimsB_depth`), so the
binder's depth is enough fuel. -/
def Ctx.effLiveB (Γ : Ctx s) (κ : BVar s .cap) : Bool := Γ.effLiveN κ.depth κ

theorem Ctx.effLiveN_sound {Γ : Ctx s} : ∀ (n : Nat) (κ : BVar s .cap),
    Γ.effLiveN n κ = true → Γ.EffLive κ
  | 0, _, h => .live h
  | n+1, _, h => by
      simp only [Ctx.effLiveN, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨h', -, ho, hl⟩
      · exact .live h
      · exact .owned ho (Ctx.effLiveN_sound n h' hl)

theorem Ctx.effLiveN_mono {Γ : Ctx s} : ∀ {n m : Nat} {κ : BVar s .cap}, n ≤ m →
    Γ.effLiveN n κ = true → Γ.effLiveN m κ = true
  | 0, 0, _, _, h => h
  | 0, _+1, κ, _, h => by
      simp [Ctx.effLiveN, show (Γ.lookupCap κ).live = true from h]
  | _+1, 0, _, hle, _ => absurd hle (by omega)
  | _+1, _+1, _, hle, h => by
      simp only [Ctx.effLiveN, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | ⟨h', hm, ho, hl⟩
      · exact Or.inl h
      · exact Or.inr ⟨h', hm, ho, Ctx.effLiveN_mono (by omega) hl⟩

/-- An owner is younger than what it owns. -/
theorem Ctx.depth_lt_of_ownsB {Γ : Ctx s} {h κ : BVar s .cap} (ho : Γ.ownsB h κ = true) :
    h.depth < κ.depth :=
  Ctx.claimsB_depth Γ h κ (Ctx.claimsB_of_ownsB ho)

theorem Ctx.effLiveB_complete {Γ : Ctx s} {κ : BVar s .cap} (h : Γ.EffLive κ) :
    Γ.effLiveB κ = true := by
  induction h with
  | @live κ hl =>
      unfold Ctx.effLiveB
      cases κ.depth with
      | zero => exact hl
      | succ n => simp [Ctx.effLiveN, show (Γ.lookupCap κ).live = true from hl]
  | @owned h κ ho _ ih =>
      unfold Ctx.effLiveB at ih ⊢
      have hd := Ctx.depth_lt_of_ownsB ho
      obtain ⟨m, hm⟩ : ∃ m, κ.depth = m + 1 := ⟨κ.depth - 1, by omega⟩
      rw [hm]
      simp only [Ctx.effLiveN, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨h, Γ.mem_capBinders h, ho, Ctx.effLiveN_mono (by omega) ih⟩

theorem Ctx.effLiveB_iff {Γ : Ctx s} {κ : BVar s .cap} : Γ.effLiveB κ = true ↔ Γ.EffLive κ :=
  ⟨Ctx.effLiveN_sound _ _, Ctx.effLiveB_complete⟩

instance Ctx.EffLive.instDecidable (Γ : Ctx s) (κ : BVar s .cap) : Decidable (Γ.EffLive κ) :=
  decidable_of_iff _ Ctx.effLiveB_iff

/-- An owned binder is effectively live when its owner is. -/
theorem Ctx.EffLive.owns {Γ : Ctx s} {h κ : BVar s .cap} (ho : Γ.Owns h κ)
    (hl : Γ.EffLive h) : Γ.EffLive κ := by
  induction ho with
  | direct hd => exact .owned hd hl
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hl)

/-- With no heir the two readings agree, so no judgment over a context with
no heir changes, and typing time has none. -/
theorem Ctx.effLive_iff_of_noHeir {Γ : Ctx s} (hn : ∀ h κ, Γ.ownsB h κ = false)
    {κ : BVar s .cap} : Γ.EffLive κ ↔ Γ.BitLive κ := by
  constructor
  · intro h
    cases h with
    | live hl => exact hl
    | owned ho _ => rw [hn] at ho; cases ho
  · exact .live

/-- The side condition of `distinct` (S1): no bit is read (Fact 4). -/
def Ctx.DistinctOk (Γ : Ctx s) (κ₁ κ₂ : BVar s .cap) : Prop :=
  κ₁ ≠ κ₂ ∧ (Γ.lookupCap κ₁).consumable = true ∧ (Γ.lookupCap κ₂).consumable = true ∧
    ¬ Γ.Related κ₁ κ₂

instance Ctx.DistinctOk.instDecidable (Γ : Ctx s) (κ₁ κ₂ : BVar s .cap) :
    Decidable (Γ.DistinctOk κ₁ κ₂) := by
  unfold Ctx.DistinctOk; infer_instance

/-- The scope a fresh pack opens: a root, then an heir of the witness.  The
twin of `Ctx.scopeInst`. -/
def Ctx.scopeOwn (Γ : Ctx s) (W : CaptureSet s) : Ctx (Sig.scope s) :=
  (Γ.consC .root).consC (.own true W↑)

/-! ## Effective modes along a path

A name reached through a chain of moded atoms carries the meet of their
modes.  `CapAtom.applyEMode m a` puts the effective mode `m` on top of `a`
through the meet, and `EMode.comb` is what that does to effective modes.
`CapAtom.reapply a x` is `x.applyEMode a.effMode` (`CapAtom.reapply_eq`). -/

/-- Put an effective mode on top of an atom, through the meet. -/
def CapAtom.applyEMode : EMode → CapAtom s → CapAtom s
  | .eps, a => a
  | .ro, a => CapAtom.withMode .ro a
  | .consume, a => CapAtom.withMode .consume a

/-- The effective mode of `m` on top of an atom at `e`. -/
def EMode.comb : EMode → EMode → EMode
  | .eps, e => e
  | .ro, _ => .ro
  | .consume, .ro => .ro
  | .consume, _ => .consume

theorem EMode.le_refl (m : EMode) : m ≤ m := Nat.le_refl _

theorem EMode.le_trans {a b c : EMode} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

theorem EMode.ro_le (m : EMode) : EMode.ro ≤ m := Nat.zero_le _

theorem EMode.le_consume (m : EMode) : m ≤ EMode.consume := by
  cases m <;> decide

theorem EMode.comb_assoc (m m' e : EMode) : m.comb (m'.comb e) = (m.comb m').comb e := by
  cases m <;> cases m' <;> cases e <;> rfl

theorem EMode.comb_mono (m : EMode) {e e' : EMode} (h : e ≤ e') : m.comb e ≤ m.comb e' := by
  cases m <;> cases e <;> cases e' <;> first | decide | exact absurd h (by decide)

theorem EMode.comb_eps (m : EMode) : m.comb .eps = m := by cases m <;> rfl

@[simp] theorem CapAtom.base_applyEMode (m : EMode) (a : CapAtom s) :
    (a.applyEMode m).base = a.base := by
  cases m <;> simp [CapAtom.applyEMode]

@[simp] theorem CapAtom.effMode_applyEMode (m : EMode) (a : CapAtom s) :
    (a.applyEMode m).effMode = m.comb a.effMode := by
  cases m with
  | eps => rfl
  | ro => rfl
  | consume =>
      simp only [CapAtom.applyEMode, CapAtom.withMode]
      cases h : a.effMode with
      | ro => simp [EMode.comb, h]
      | eps => simp [EMode.comb, CapAtom.effMode]
      | consume => simp [EMode.comb, CapAtom.effMode]

theorem CapAtom.withMode_consume_idem (a : CapAtom s) :
    CapAtom.withMode .consume (CapAtom.withMode .consume a) = CapAtom.withMode .consume a := by
  unfold CapAtom.withMode
  by_cases h : a.effMode = .ro
  · simp [h]
  · simp [h, CapAtom.effMode]

/-- Re-applying the modes of `a` is putting its effective mode on top. -/
theorem CapAtom.reapply_eq : ∀ (a x : CapAtom s), a.reapply x = x.applyEMode a.effMode
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .top, _ => rfl
  | .mode .ro a, x => by
      show CapAtom.withMode .ro (a.reapply x) = CapAtom.withMode .ro x
      simp [CapAtom.withMode]
  | .mode .consume a, x => by
      show CapAtom.withMode .consume (a.reapply x) = _
      rw [CapAtom.reapply_eq a x]
      cases h : a.effMode with
      | ro =>
          simp [CapAtom.applyEMode, CapAtom.effMode, h, CapAtom.withMode]
      | eps => simp [CapAtom.applyEMode, CapAtom.effMode, h]
      | consume =>
          simp only [CapAtom.applyEMode, CapAtom.effMode, h]
          rw [CapAtom.withMode_consume_idem]
          rfl

theorem CapAtom.applyEMode_rename (m : EMode) (a : CapAtom s1) (ρ : Rename s1 s2) :
    (a.applyEMode m).rename ρ = (a.rename ρ).applyEMode m := by
  cases m <;> simp [CapAtom.applyEMode, CapAtom.withMode_rename]

theorem CapAtom.applyEMode_weaken (m : EMode) (a : CapAtom s) :
    CapAtom.weaken (k := k) (a.applyEMode m) = (CapAtom.weaken (k := k) a).applyEMode m :=
  CapAtom.applyEMode_rename m a _

theorem CapAtom.applyEMode_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ)
    (m : EMode) (a : CapAtom s1) :
    (a.applyEMode m).subst σ = (a.subst σ).applyEMode m := by
  cases m <;> simp [CapAtom.applyEMode, CapAtom.withMode_subst hσ]

theorem EMode.comb_mono_left {m m' : EMode} (h : m ≤ m') (e : EMode) : m.comb e ≤ m'.comb e := by
  cases m <;> cases m' <;> cases e <;> first | decide | exact absurd h (by decide)

/-! ## The use mode (plan-5h decision 39)

The mode a use of an atom puts on the names and roots it reaches.  It is the
effective mode, except that `consume` on a term binder or a capture name
raises nothing: consumption is named on capture binders only.  A term binder
is instantiated by the machine at a store binder whose names are covered by
those of its declared type only up to ownership, and the machine transfers
only the witness of a fresh pack, a list of capture binders. -/

/-- The atom is a term binder or a capture name. -/
def CapAtom.isTermB : CapAtom s → Bool
  | .var _ | .name _ _ => true
  | _ => false

/-- The mode a use of `a` puts on the names and roots it reaches. -/
def CapAtom.useMode (a : CapAtom s) : EMode :=
  if a.base.isTermB = true ∧ a.effMode = .consume then .eps else a.effMode

/-- Put the use mode of `a` on a name it reaches, through the meet. -/
def CapAtom.useApply (a x : CapAtom s) : CapAtom s := x.applyEMode a.useMode

theorem CapAtom.useMode_of_not_termB {a : CapAtom s} (h : a.base.isTermB = false) :
    a.useMode = a.effMode := by
  unfold CapAtom.useMode; simp [h]

theorem CapAtom.useMode_of_ne_consume {a : CapAtom s} (h : a.effMode ≠ .consume) :
    a.useMode = a.effMode := by
  unfold CapAtom.useMode; simp [h]

/-- Off term binders and capture names the use mode reapplies the modes. -/
theorem CapAtom.useApply_eq_reapply {a : CapAtom s} (h : a.base.isTermB = false) :
    a.useApply = a.reapply := by
  funext x
  rw [CapAtom.reapply_eq]
  unfold CapAtom.useApply
  rw [CapAtom.useMode_of_not_termB h]

theorem CapAtom.useMode_le_effMode (a : CapAtom s) : a.useMode ≤ a.effMode := by
  unfold CapAtom.useMode
  split
  · rename_i h; rw [h.2]; decide
  · exact EMode.le_refl _

/-- The use mode is `consume` exactly on a consuming atom off term binders. -/
theorem CapAtom.useMode_eq_consume {a : CapAtom s} :
    a.useMode = .consume ↔ a.effMode = .consume ∧ a.base.isTermB = false := by
  unfold CapAtom.useMode
  by_cases h1 : a.base.isTermB = true <;> by_cases h2 : a.effMode = .consume <;> simp_all

/-- On a term binder or a capture name the use mode never consumes. -/
theorem CapAtom.useMode_ne_consume {a : CapAtom s} (h : a.base.isTermB = true) :
    a.useMode ≠ .consume := by
  rw [Ne, CapAtom.useMode_eq_consume, h]; simp

@[simp] theorem CapAtom.isTermB_rename (a : CapAtom s1) (ρ : Rename s1 s2) :
    (a.rename ρ).isTermB = a.isTermB := by
  cases a <;> rfl

theorem CapAtom.isTermB_subst {σ : Subst s1 s2} {a : CapAtom s1} (h : a.isTermB = true) :
    (a.subst σ).isTermB = true := by
  cases a <;> simp_all [CapAtom.isTermB, CapAtom.subst]

/-- A renaming keeps the use mode. -/
@[simp] theorem CapAtom.useMode_rename (a : CapAtom s1) (ρ : Rename s1 s2) :
    (a.rename ρ).useMode = a.useMode := by
  unfold CapAtom.useMode
  rw [CapAtom.base_rename, CapAtom.isTermB_rename, CapAtom.effMode_rename]

theorem CapAtom.useMode_rename_le (a : CapAtom s1) (ρ : Rename s1 s2) :
    (a.rename ρ).useMode ≤ a.useMode := by
  rw [CapAtom.useMode_rename]; exact EMode.le_refl _

theorem CapAtom.useMode_weaken (a : CapAtom s) :
    (CapAtom.weaken (k := k) a).useMode = a.useMode :=
  CapAtom.useMode_rename a _

theorem CapAtom.useApply_rename (a x : CapAtom s1) (ρ : Rename s1 s2) :
    (a.useApply x).rename ρ = (a.rename ρ).useApply (x.rename ρ) := by
  unfold CapAtom.useApply
  rw [CapAtom.applyEMode_rename, CapAtom.useMode_rename]

theorem CapAtom.weaken_useApply {k : Kind} (c x : CapAtom s) :
    (CapAtom.weaken (k := k) c).useApply (CapAtom.weaken (k := k) x) =
      CapAtom.weaken (k := k) (c.useApply x) :=
  (CapAtom.useApply_rename c x _).symm

/-- A substitution whose capture images carry no mode never raises the use
mode: it sends a term binder to a term binder, and a capture binder to an
atom that may be a term binder. -/
theorem CapAtom.useMode_subst_le {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ)
    (a : CapAtom s1) : (a.subst σ).useMode ≤ a.useMode := by
  unfold CapAtom.useMode
  rw [CapAtom.base_subst hσ, CapAtom.effMode_subst hσ]
  by_cases h1 : a.base.isTermB = true
  · rw [CapAtom.isTermB_subst h1, h1]; exact EMode.le_refl _
  · have h1' : a.base.isTermB = false := by simpa using h1
    rw [h1']
    simp only [Bool.false_eq_true, false_and, if_false]
    split
    · rename_i h; rw [h.2]; decide
    · exact EMode.le_refl _

/-- The use mode of a wrapped atom: `consume` on a term binder or a capture
name adds nothing, and every other wrapper rides on top through the meet. -/
theorem CapAtom.useApply_mode (m : Mode) (a x : CapAtom s) :
    (CapAtom.mode m a).useApply x =
      if m = .consume ∧ a.base.isTermB = true then a.useApply x
      else CapAtom.withMode m (a.useApply x) := by
  split
  · rename_i h
    obtain ⟨rfl, ht⟩ := h
    unfold CapAtom.useApply CapAtom.useMode
    congr 1
    simp only [CapAtom.base_mode, ht, true_and]
    show (if (if a.effMode = .ro then EMode.ro else EMode.consume) = .consume then EMode.eps
      else (if a.effMode = .ro then EMode.ro else EMode.consume)) =
      (if a.effMode = .consume then EMode.eps else a.effMode)
    cases a.effMode <;> rfl
  · rename_i h
    cases m with
    | ro =>
        unfold CapAtom.useApply
        rw [CapAtom.useMode_of_ne_consume (a := CapAtom.mode .ro a) (by
          show EMode.ro ≠ EMode.consume; decide)]
        show CapAtom.withMode .ro x = CapAtom.withMode .ro (x.applyEMode a.useMode)
        simp only [CapAtom.withMode, CapAtom.base_applyEMode]
    | consume =>
        have ht : a.base.isTermB = false := by simpa using h
        rw [CapAtom.useApply_eq_reapply (a := CapAtom.mode .consume a) (by simpa using ht),
          CapAtom.useApply_eq_reapply ht]
        rfl

/-- A base atom puts no mode. -/
theorem CapAtom.useApply_of_base {c : CapAtom s} (h : c.base = c) (x : CapAtom s) :
    c.useApply x = x := by
  unfold CapAtom.useApply
  rw [CapAtom.useMode_of_ne_consume (by rw [CapAtom.effMode_of_base h]; decide),
    CapAtom.effMode_of_base h]
  rfl

@[simp] theorem CapAtom.base_useApply (a x : CapAtom s) : (a.useApply x).base = x.base :=
  CapAtom.base_applyEMode _ _

@[simp] theorem CapAtom.effMode_useApply (a x : CapAtom s) :
    (a.useApply x).effMode = a.useMode.comb x.effMode :=
  CapAtom.effMode_applyEMode _ _

/-! ## Capture names reached by self reference

A capture witness of a transparent binder may name the block's own capture
names, `.name .here ℓ'`.  The names of a capture name follow those self
references through every label they reach, carrying the effective mode of
the path, and collect the other atoms of every witness so reached.  A state
of the search is a label with the effective mode of the path to it.  There
are finitely many states, so as many rounds as there are states reach the
fixed point. -/

/-- The label of a self reference. -/
def CapAtom.selfLabel? (a : CapAtom (s,x)) : Option Label :=
  match a.base with
  | .name .here ℓ => some ℓ
  | _ => none

/-- Every atom of every witness. -/
def CapWitnesses.atoms : CapWitnesses s → CaptureSet s
  | .nil => []
  | .cons W _ C => W.atoms ++ C

/-- The states one step from a state: the self references of its witness. -/
def CapWitnesses.succs (Wc : CapWitnesses (s,x)) (p : Label × EMode) : List (Label × EMode) :=
  (Wc.get p.1).filterMap fun a => a.selfLabel?.map fun ℓ' => (ℓ', p.2.comb a.useMode)

/-- One round of the search. -/
def CapWitnesses.reachStep (Wc : CapWitnesses (s,x)) (V : List (Label × EMode)) :
    List (Label × EMode) :=
  V ++ (V.flatMap Wc.succs).filter fun p => !V.contains p

/-- Every state the search from `ℓ` can visit. -/
def CapWitnesses.states (Wc : CapWitnesses (s,x)) (ℓ : Label) : List (Label × EMode) :=
  (ℓ :: Wc.atoms.filterMap CapAtom.selfLabel?).flatMap fun l =>
    [(l, .ro), (l, .eps), (l, .consume)]

/-- The states reached from `ℓ` at the plain mode. -/
def CapWitnesses.reachPairs (Wc : CapWitnesses (s,x)) (ℓ : Label) : List (Label × EMode) :=
  Nat.repeat Wc.reachStep (Wc.states ℓ).length [(ℓ, .eps)]

/-- The atoms a capture name reaches: every atom of a reached witness that is
no self reference, under the effective mode of the path. -/
def CapWitnesses.reach (Wc : CapWitnesses (s,x)) (ℓ : Label) : CaptureSet (s,x) :=
  (Wc.reachPairs ℓ).flatMap fun p =>
    ((Wc.get p.1).filter fun a => a.selfLabel?.isNone).map (CapAtom.applyEMode p.2)

/-! ## The names of a set -/

/-- The names a base atom of a capture witness stands for, one binder out:
the witness lives in the scope of the block itself, and `f` is the names in
the scope outside it.  The binder itself stands for its declared set `T`. -/
def Ctx.selfInner (f : CapAtom s → CaptureSet s) (T : Ty s) : CapAtom (s,x) → CaptureSet s
  | .var .here => T.captureSet.flatMap fun (c : CapAtom s) => (f c.base).map c.useApply
  | .var (.there y) => f (.var y)
  | .cvar (.there κ) => f (.cvar κ)
  | .name (.there y) ℓ' => f (.name y ℓ')
  | .top => [.top]
  | _ => []

/-- The same for an atom with modes: they ride on top. -/
def Ctx.namesSelfWith (f : CapAtom s → CaptureSet s) (T : Ty s) (a : CapAtom (s,x)) :
    CaptureSet s :=
  (Ctx.selfInner f T a.base).map (CapAtom.applyEMode a.useMode)

/-- Phase one, structural on the context, in two readings told apart by
`p` (plan-5h S0.3, decision 37).  A term binder is followed to its declared
capture set, except that in the mode reading (`p = true`) a parameter
(`Binding.formal`) stands for itself.  `.inst C` and `.upper C` are followed
to `C`.  Every other capture binder, the universal root and every scope root
stay.  A capture name of a transparent binder is the union of the atoms,
other than self references, of every witness its label reaches by self
reference, and a capture name of an opaque binder or a parameter is the level
root of that binder.  Modes ride on top by `useApply` (decision 39).  A moded atom has no
names of its own: the callers read the base. -/
def Ctx.namesCapsP (p : Bool) : {s : Sig} → Ctx s → CapAtom s → CaptureSet s
  | _, .cons Γ b, .var .here =>
      if p && b.isFormal then [.var .here] else
      CaptureSet.weaken
        (b.ty.captureSet.flatMap fun (a : CapAtom _) => (Γ.namesCapsP p a.base).map a.useApply)
  | _, .cons Γ _, .var (.there y) => (Γ.namesCapsP p (.var y)).weaken
  | _, .consC Γ _, .var (.there y) => (Γ.namesCapsP p (.var y)).weaken
  | _, .consC Γ (.upper C), .cvar .here =>
      CaptureSet.weaken (C.flatMap fun (a : CapAtom _) => (Γ.namesCapsP p a.base).map a.useApply)
  | _, .consC Γ (.inst C), .cvar .here =>
      CaptureSet.weaken (C.flatMap fun (a : CapAtom _) => (Γ.namesCapsP p a.base).map a.useApply)
  | _, .consC _ .root, .cvar .here => [.cvar .here]
  | _, .consC _ .star, .cvar .here => [.cvar .here]
  | _, .consC _ (.loc _ _), .cvar .here => [.cvar .here]
  | _, .consC _ (.own _ _), .cvar .here => [.cvar .here]
  | _, .consC _ (.param _), .cvar .here => [.cvar .here]
  | _, .cons Γ _, .cvar (.there κ) => (Γ.namesCapsP p (.cvar κ)).weaken
  | _, .consC Γ _, .cvar (.there κ) => (Γ.namesCapsP p (.cvar κ)).weaken
  | _, .cons Γ (.transparent T _ Wc _), .name .here ℓ =>
      CaptureSet.weaken ((Wc.reach ℓ).flatMap (Ctx.namesSelfWith (fun a => Γ.namesCapsP p a) T))
  | _, .cons Γ (.opaque _), .name .here _ => [CapAtom.weaken Γ.rootAtom]
  | _, .cons Γ (.formal _), .name .here _ => [CapAtom.weaken Γ.rootAtom]
  | _, .cons Γ _, .name (.there y) ℓ => (Γ.namesCapsP p (.name y ℓ)).weaken
  | _, .consC Γ _, .name (.there y) ℓ => (Γ.namesCapsP p (.name y ℓ)).weaken
  | _, _, .top => [.top]
  | _, _, .mode _ _ => []

/-- The names a kill reads: a parameter is followed to its declared set. -/
abbrev Ctx.namesCaps (Γ : Ctx s) : CapAtom s → CaptureSet s := Γ.namesCapsP false

/-- The names a mode bound reads: a parameter is a plain leaf. -/
abbrev Ctx.modeCaps (Γ : Ctx s) : CapAtom s → CaptureSet s := Γ.namesCapsP true

/-- Phase two: open every root, in the current context, into itself and every
capture binder that is not a root, at every level (plan-5h decision 38).  It
keeps modes.  Every scope root is sent to `⊤` before its body runs, so a root
names what `⊤` names once the scope is flattened into the store.  In a
context with no scope root this is the expansion of `Ctx.expandAtom` over all
stopped binders. -/
def Ctx.expandNames (Γ : Ctx s) (a : CapAtom s) : CaptureSet s :=
  if Γ.isRootB a.base then
    a :: (Γ.capBinders.filter fun κ =>
      !(Γ.lookupCap κ).isRoot).map fun κ => a.reapply (.cvar κ)
  else [a]

/-- The names of one atom. -/
def Ctx.namesAtom (Γ : Ctx s) (a : CapAtom s) : CaptureSet s :=
  ((Γ.namesCaps a.base).map a.useApply).flatMap Γ.expandNames

/-- The names of a set. -/
def Ctx.names (Γ : Ctx s) (C : CaptureSet s) : CaptureSet s := C.flatMap Γ.namesAtom

/-! ## The side conditions

All decidable, all reading names and bits and never roots. -/

/-- The capture binder an atom is, if it is one. -/
def CapAtom.cvar? : CapAtom s → Option (BVar s .cap)
  | .cvar κ => some κ
  | _ => none

/-- The consumed names of a set: its `consume`-moded names. -/
def Ctx.consumedNames (Γ : Ctx s) (C : CaptureSet s) : List (BVar s .cap) :=
  (Γ.names C).filterMap fun a => if a.effMode = .consume then a.base.cvar? else none

/-- The kill a head causes: its consumed names and everything they may own. -/
def Ctx.killFor (Γ : Ctx s) (C : CaptureSet s) : Ctx s :=
  Γ.killNames (Γ.ownClosure (Γ.consumedNames C))

/-- What a name opened after the head may come to own. -/
def Ctx.claimsFor (Γ : Ctx s) (C : CaptureSet s) : CaptureSet s :=
  (Γ.ownClosure (Γ.consumedNames C)).map CapAtom.cvar

/-- The context of a `newLet` body: a fresh location that claims nothing,
then the cell binder declared at it. -/
def Ctx.cellCtx (Γ : Ctx s) (T : Ty s) : Ctx ((s,c),x) :=
  (Γ.consC (.loc true [])).cons
    (.opaque ((Shape.cell (Ty.weaken (k := .cap) T)) ^ [CapAtom.cvar .here]))

/-- The context of a `letexF` body: the head's consumed names killed, then an
opened name that claims them, then the payload binder (Fact 4 of plan-5h). -/
def Ctx.freshCtx (Γ : Ctx s) (C : CaptureSet s) (T : Ty (s,c)) : Ctx ((s,c),x) :=
  ((Γ.killFor C).consC (.loc true (Γ.claimsFor C))).cons (.opaque T)

/-- Every capture binder `C` names is effectively live: live, or owned by a
live heir through a chain of heirs (plan-5h decision 39). -/
def Ctx.Accessible (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names C, ∀ κ, a.base = .cvar κ → Γ.EffLive κ

/-- Every consumed name of `C` is a consumable, live, unmasked binder. -/
def Ctx.ConsumeOk (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names C, a.effMode = .consume → ∃ κ, a.base = .cvar κ ∧ Γ.Consumable κ

/-- Every consumed name of `C` is a consumable capture binder: the premise of
every kill site (plan-5h decision 38).  The flavour half of `ConsumeOk`, with
no bit.  A kill set that consumes a root, a star or an instance would kill
every binder a later weakening appends. -/
def Ctx.KillOk (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names C, a.effMode = .consume → ∃ κ, a.base = .cvar κ ∧
    (Γ.lookupCap κ).consumable = true

/-- The consumed leaves of a set: its `consume`-moded names of phase one, with
no root opened.  `consume ⊤` has none.  The clause of `State.TypedAt` reads
them. -/
def Ctx.consumedLeaves (Γ : Ctx s) (C : CaptureSet s) : List (BVar s .cap) :=
  (C.flatMap fun a => (Γ.namesCaps a.base).map a.useApply).filterMap
    fun a => if a.effMode = .consume then a.base.cvar? else none

/-- `C` consumes nothing in the names a kill reads.  g3's body of
`Ctx.AccessOnly`, kept for the kill (`Ctx.killFor_of_noConsume`).  The
premise of the level rule is `Ctx.AccessOnly` below, read in the mode
reading. -/
def Ctx.NoConsume (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names C, a.effMode ≠ .consume

/-- No binder `B` names is a name `C` consumes or may own through one, and
none may own a name `C` consumes (plan-5h decision 39). -/
def Ctx.ArgSep (Γ : Ctx s) (B C : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names B, ∀ κ, a.base = .cvar κ →
    κ ∉ Γ.ownClosure (Γ.consumedNames C) ∧ ∀ l ∈ Γ.consumedNames C, ¬ Γ.MayOwn κ l

/-- A statement about the capture binder an atom is, decided by matching. -/
instance CapAtom.decForallCvar (a : CapAtom s) (P : BVar s .cap → Prop) [DecidablePred P] :
    Decidable (∀ κ, a = .cvar κ → P κ) :=
  match a with
  | .cvar κ =>
      if h : P κ then .isTrue (fun _ he => by cases he; exact h)
      else .isFalse (fun H => h (H κ rfl))
  | .var _ => .isTrue (fun _ he => by cases he)
  | .name _ _ => .isTrue (fun _ he => by cases he)
  | .top => .isTrue (fun _ he => by cases he)
  | .mode _ _ => .isTrue (fun _ he => by cases he)

instance CapAtom.decExistsCvar (a : CapAtom s) (P : BVar s .cap → Prop) [DecidablePred P] :
    Decidable (∃ κ, a = .cvar κ ∧ P κ) :=
  match a with
  | .cvar κ =>
      if h : P κ then .isTrue ⟨κ, rfl, h⟩
      else .isFalse (fun ⟨_, he, hp⟩ => by cases he; exact h hp)
  | .var _ => .isFalse (fun ⟨_, he, _⟩ => by cases he)
  | .name _ _ => .isFalse (fun ⟨_, he, _⟩ => by cases he)
  | .top => .isFalse (fun ⟨_, he, _⟩ => by cases he)
  | .mode _ _ => .isFalse (fun ⟨_, he, _⟩ => by cases he)

instance Ctx.Accessible.instDecidable (Γ : Ctx s) (C : CaptureSet s) :
    Decidable (Γ.Accessible C) := by
  unfold Ctx.Accessible; infer_instance

instance Ctx.ConsumeOk.instDecidable (Γ : Ctx s) (C : CaptureSet s) :
    Decidable (Γ.ConsumeOk C) := by
  unfold Ctx.ConsumeOk; infer_instance

instance Ctx.KillOk.instDecidable (Γ : Ctx s) (C : CaptureSet s) :
    Decidable (Γ.KillOk C) := by
  unfold Ctx.KillOk; infer_instance

instance Ctx.NoConsume.instDecidable (Γ : Ctx s) (C : CaptureSet s) :
    Decidable (Γ.NoConsume C) := by
  unfold Ctx.NoConsume; infer_instance

instance Ctx.ArgSep.instDecidable (Γ : Ctx s) (B C : CaptureSet s) :
    Decidable (Γ.ArgSep B C) := by
  unfold Ctx.ArgSep; infer_instance

/-! ## Mode bounds on names

A mode bound reads only the effective modes of names, and expansion of a root
keeps the mode of the root.  So a bound is a bound on the modes of the first
phase, atom by atom.  Mode bounds read the mode reading `Ctx.modeCaps`, in
which a parameter is a plain leaf (decision 37).  `Ctx.ModeBound Γ a m` is
the bound for one base atom, `Ctx.AccessOnly` is the plain bound of a set,
and `Ctx.noConsume_iff` is the same equivalence for the full reading.  A
context map that carries every such bound, `Ctx.ModeMap`, carries the level
rule's premise. -/

/-- The largest effective mode below which `e` on top of it stays at `m`. -/
def EMode.thr : EMode → EMode → EMode
  | .ro, _ => .consume
  | .eps, m => m
  | .consume, .consume => .consume
  | .consume, _ => .ro

theorem EMode.comb_le_iff (e z m : EMode) : e.comb z ≤ m ↔ z ≤ e.thr m := by
  cases e <;> cases z <;> cases m <;> decide

theorem EMode.le_eps_iff (m : EMode) : m ≤ .eps ↔ m ≠ .consume := by
  cases m <;> decide

theorem EMode.thr_mono (e : EMode) {m m' : EMode} (h : m ≤ m') : e.thr m ≤ e.thr m' := by
  cases e <;> cases m <;> cases m' <;> first | decide | exact absurd h (by decide)

theorem EMode.thr_anti {m1 m2 : EMode} (h : m1 ≤ m2) (m : EMode) : m2.thr m ≤ m1.thr m := by
  cases m1 <;> cases m2 <;> cases m <;> first | decide | exact absurd h (by decide)

/-- Every name of the first phase of `a`, in the mode reading, is at most at
mode `m`. -/
def Ctx.ModeBound (Γ : Ctx s) (a : CapAtom s) (m : EMode) : Prop :=
  ∀ z ∈ Γ.modeCaps a, z.effMode ≤ m

/-- Every atom of `C` has its names at most at mode `m`, modes on top. -/
def Ctx.SetBound (Γ : Ctx s) (C : CaptureSet s) (m : EMode) : Prop :=
  ∀ c ∈ C, Γ.ModeBound c.base (c.useMode.thr m)

/-- `C` consumes nothing once every parameter is instantiated: the premise of
`level`, `ownLe`, the argument of `app`, the witness of a pack and the
capture witnesses of a literal (plan-5h S0.3). -/
def Ctx.AccessOnly (Γ : Ctx s) (C : CaptureSet s) : Prop := Γ.SetBound C .eps

instance Ctx.ModeBound.instDecidable (Γ : Ctx s) (a : CapAtom s) (m : EMode) :
    Decidable (Γ.ModeBound a m) := by
  unfold Ctx.ModeBound; infer_instance

instance Ctx.SetBound.instDecidable (Γ : Ctx s) (C : CaptureSet s) (m : EMode) :
    Decidable (Γ.SetBound C m) := by
  unfold Ctx.SetBound; infer_instance

instance Ctx.AccessOnly.instDecidable (Γ : Ctx s) (C : CaptureSet s) :
    Decidable (Γ.AccessOnly C) := by
  unfold Ctx.AccessOnly; infer_instance

theorem Ctx.ModeBound.mono {Γ : Ctx s} {a : CapAtom s} {m m' : EMode} (h : Γ.ModeBound a m)
    (hm : m ≤ m') : Γ.ModeBound a m' :=
  fun z hz => EMode.le_trans (h z hz) hm

theorem Ctx.SetBound.mono {Γ : Ctx s} {C : CaptureSet s} {m m' : EMode} (h : Γ.SetBound C m)
    (hm : m ≤ m') : Γ.SetBound C m' :=
  fun c hc => (h c hc).mono (EMode.thr_mono _ hm)

/-- A bound through any first phase `N`, read on the names with the modes on
top. -/
theorem CaptureSet.bound_flatMap_iff (N : CapAtom s → CaptureSet s) {C : CaptureSet s}
    {m : EMode} :
    (∀ c ∈ C, ∀ y ∈ N c.base, y.effMode ≤ c.useMode.thr m) ↔
      ∀ z ∈ C.flatMap (fun (c : CapAtom s) => (N c.base).map c.useApply), z.effMode ≤ m := by
  constructor
  · intro h z hz
    obtain ⟨c, hc, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    rw [CapAtom.effMode_useApply, EMode.comb_le_iff]
    exact h c hc y hy
  · intro h c hc y hy
    have := h (c.useApply y) (List.mem_flatMap.mpr ⟨c, hc, List.mem_map_of_mem hy⟩)
    rwa [CapAtom.effMode_useApply, EMode.comb_le_iff] at this

/-- The set form, read on the names with the modes on top. -/
theorem Ctx.setBound_iff {Γ : Ctx s} {C : CaptureSet s} {m : EMode} :
    Γ.SetBound C m ↔
      ∀ z ∈ C.flatMap (fun (c : CapAtom s) => (Γ.modeCaps c.base).map c.useApply),
        z.effMode ≤ m :=
  CaptureSet.bound_flatMap_iff (fun a => Γ.modeCaps a)

theorem Ctx.setBound_cons {Γ : Ctx s} {c : CapAtom s} {C : CaptureSet s} {m : EMode} :
    Γ.SetBound (c :: C) m ↔ Γ.ModeBound c.base (c.useMode.thr m) ∧ Γ.SetBound C m := by
  constructor
  · intro h
    exact ⟨h c (List.mem_cons_self ..), fun d hd => h d (List.mem_cons_of_mem c hd)⟩
  · rintro ⟨h₁, h₂⟩ d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h₁
    · exact h₂ d hd

/-- The head of an expansion is the atom itself. -/
theorem Ctx.mem_expandNames_self (Γ : Ctx s) (a : CapAtom s) : a ∈ Γ.expandNames a := by
  unfold Ctx.expandNames
  split
  · exact List.mem_cons_self ..
  · exact List.mem_singleton_self a

/-- Expansion keeps the mode of the root. -/
theorem Ctx.effMode_of_mem_expandNames {Γ : Ctx s} {a y : CapAtom s}
    (h : y ∈ Γ.expandNames a) : y.effMode = a.effMode := by
  unfold Ctx.expandNames at h
  split at h
  · rcases List.mem_cons.mp h with rfl | h
    · rfl
    · obtain ⟨κ, -, rfl⟩ := List.mem_map.mp h
      rw [CapAtom.reapply_eq, CapAtom.effMode_applyEMode]
      exact EMode.comb_eps _
  · rw [List.mem_singleton.mp h]

/-- **Consuming nothing is a bound on modes** in the full reading.  Expansion
is invisible to it.  g3's `Ctx.accessOnly_iff`. -/
theorem Ctx.noConsume_iff {Γ : Ctx s} {C : CaptureSet s} :
    Γ.NoConsume C ↔ ∀ c ∈ C, ∀ z ∈ Γ.namesCaps c.base, z.effMode ≤ c.useMode.thr .eps := by
  rw [CaptureSet.bound_flatMap_iff (fun a => Γ.namesCaps a)]
  constructor
  · intro h z hz
    obtain ⟨c, hc, hz⟩ := List.mem_flatMap.mp hz
    rw [EMode.le_eps_iff]
    exact h z (List.mem_flatMap.mpr ⟨c, hc,
      List.mem_flatMap.mpr ⟨z, hz, Γ.mem_expandNames_self z⟩⟩)
  · intro h y hy
    obtain ⟨c, hc, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨z, hz, hy⟩ := List.mem_flatMap.mp hy
    rw [Ctx.effMode_of_mem_expandNames hy, ← EMode.le_eps_iff]
    exact h z (List.mem_flatMap.mpr ⟨c, hc, hz⟩)

/-- The singleton form, which the level rule reads. -/
theorem Ctx.accessOnly_singleton {Γ : Ctx s} {e : CapAtom s} :
    Γ.AccessOnly [e] ↔ Γ.ModeBound e.base (e.useMode.thr .eps) := by
  unfold Ctx.AccessOnly
  rw [Ctx.setBound_cons]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ hd => by cases hd⟩⟩

theorem Ctx.setBound_singleton {Γ : Ctx s} {c : CapAtom s} {m : EMode} :
    Γ.SetBound [c] m ↔ Γ.ModeBound c.base (c.useMode.thr m) := by
  rw [Ctx.setBound_cons]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ hd => by cases hd⟩⟩

/-! ### Weakening -/

theorem Ctx.namesCapsP_weaken (p : Bool) (Γ : Ctx s) (b : Binding s) :
    ∀ a : CapAtom s,
      (Γ.cons b).namesCapsP p (CapAtom.weaken a) = CaptureSet.weaken (Γ.namesCapsP p a)
  | .var _ => rfl
  | .cvar _ => rfl
  | .name _ _ => rfl
  | .top => by cases Γ <;> rfl
  | .mode _ _ => by simp [CapAtom.weaken, CapAtom.rename, Ctx.namesCapsP, CaptureSet.weaken,
      CaptureSet.rename]

theorem Ctx.namesCapsP_weakenC (p : Bool) (Γ : Ctx s) (b : CapBound s) :
    ∀ a : CapAtom s,
      (Γ.consC b).namesCapsP p (CapAtom.weaken a) = CaptureSet.weaken (Γ.namesCapsP p a)
  | .var _ => rfl
  | .cvar _ => rfl
  | .name _ _ => rfl
  | .top => by cases Γ <;> rfl
  | .mode _ _ => by simp [CapAtom.weaken, CapAtom.rename, Ctx.namesCapsP, CaptureSet.weaken,
      CaptureSet.rename]

theorem Ctx.namesCaps_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).namesCaps (CapAtom.weaken a) = CaptureSet.weaken (Γ.namesCaps a) :=
  Ctx.namesCapsP_weaken false Γ b a

theorem Ctx.namesCaps_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).namesCaps (CapAtom.weaken a) = CaptureSet.weaken (Γ.namesCaps a) :=
  Ctx.namesCapsP_weakenC false Γ b a

theorem Ctx.modeCaps_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).modeCaps (CapAtom.weaken a) = CaptureSet.weaken (Γ.modeCaps a) :=
  Ctx.namesCapsP_weaken true Γ b a

theorem Ctx.modeCaps_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).modeCaps (CapAtom.weaken a) = CaptureSet.weaken (Γ.modeCaps a) :=
  Ctx.namesCapsP_weakenC true Γ b a

/-- **The two readings agree in a context that binds no parameter**, and so
in every store context. -/
theorem Ctx.namesCapsP_eq_of_formalFree : ∀ {s : Sig} {Γ : Ctx s}, Γ.formalFree = true →
    ∀ (p q : Bool), Γ.namesCapsP p = Γ.namesCapsP q
  | _, .nil, _, p, q => by
      funext a
      match a with
      | .top => rfl
      | .mode _ _ => rfl
  | _, .cons Γ b, h, p, q => by
      have h' : b.isFormal = false ∧ Γ.formalFree = true := by
        simpa [Ctx.formalFree] using h
      have ih := Ctx.namesCapsP_eq_of_formalFree h'.2 p q
      funext a
      match a, b with
      | .var .here, b =>
          simp only [Ctx.namesCapsP, h'.1, Bool.and_false, ih]
      | .var (.there y), _ => simp only [Ctx.namesCapsP, ih]
      | .cvar (.there κ), _ => simp only [Ctx.namesCapsP, ih]
      | .name .here ℓ, .transparent T _ Wc _ => simp only [Ctx.namesCapsP, ih]
      | .name .here ℓ, .opaque _ => rfl
      | .name .here ℓ, .formal _ => rfl
      | .name (.there y) ℓ, _ => simp only [Ctx.namesCapsP, ih]
      | .top, _ => rfl
      | .mode _ _, _ => rfl
  | _, .consC Γ b, h, p, q => by
      have ih := Ctx.namesCapsP_eq_of_formalFree (Γ := Γ) h p q
      funext a
      match a, b with
      | .var (.there y), _ => simp only [Ctx.namesCapsP, ih]
      | .cvar .here, .upper C => simp only [Ctx.namesCapsP, ih]
      | .cvar .here, .inst C => simp only [Ctx.namesCapsP, ih]
      | .cvar .here, .root => rfl
      | .cvar .here, .star => rfl
      | .cvar .here, .loc _ _ => rfl
      | .cvar .here, .own _ _ => rfl
      | .cvar .here, .param _ => rfl
      | .cvar (.there κ), _ => simp only [Ctx.namesCapsP, ih]
      | .name (.there y) ℓ, _ => simp only [Ctx.namesCapsP, ih]
      | .top, _ => rfl
      | .mode _ _, _ => rfl

theorem CaptureSet.forall_weaken_effMode {L : CaptureSet s} {m : EMode} :
    (∀ z ∈ CaptureSet.weaken (k := k) L, z.effMode ≤ m) ↔ ∀ z ∈ L, z.effMode ≤ m := by
  constructor
  · intro h z hz
    have := h _ (CaptureSet.weaken_mem_weaken.mpr hz)
    rwa [CapAtom.weaken, CapAtom.effMode_rename] at this
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp hz
    rw [CapAtom.weaken, CapAtom.effMode_rename]
    exact h y hy

theorem Ctx.modeBound_weaken_iff (Γ : Ctx s) (b : Binding s) (a : CapAtom s) (m : EMode) :
    (Γ.cons b).ModeBound (CapAtom.weaken a) m ↔ Γ.ModeBound a m := by
  unfold Ctx.ModeBound
  rw [Ctx.modeCaps_weaken]
  exact CaptureSet.forall_weaken_effMode

theorem Ctx.modeBound_weakenC_iff (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) (m : EMode) :
    (Γ.consC b).ModeBound (CapAtom.weaken a) m ↔ Γ.ModeBound a m := by
  unfold Ctx.ModeBound
  rw [Ctx.modeCaps_weakenC]
  exact CaptureSet.forall_weaken_effMode

/-! ### The clauses at the newest binder -/

/-- A term binder that is no parameter has the bounds of its declared set. -/
theorem Ctx.modeBound_cons_here (Γ : Ctx s) {b : Binding s} (hb : b.isFormal = false)
    (m : EMode) : (Γ.cons b).ModeBound (.var .here) m ↔ Γ.SetBound b.ty.captureSet m := by
  unfold Ctx.ModeBound
  rw [Ctx.setBound_iff]
  show (∀ z ∈ (if true && b.isFormal then _ else _), _) ↔ _
  rw [hb]
  exact CaptureSet.forall_weaken_effMode

/-- A parameter is a plain leaf. -/
theorem Ctx.modeBound_cons_formal (Γ : Ctx s) (T : Ty s) (m : EMode) :
    (Γ.cons (.formal T)).ModeBound (.var .here) m ↔ EMode.eps ≤ m := by
  unfold Ctx.ModeBound
  simp [Ctx.namesCapsP, Binding.isFormal, CapAtom.effMode]

theorem Ctx.modeBound_consC_upper (Γ : Ctx s) (C : CaptureSet s) (m : EMode) :
    (Γ.consC (.upper C)).ModeBound (.cvar .here) m ↔ Γ.SetBound C m := by
  unfold Ctx.ModeBound
  rw [Ctx.setBound_iff]
  exact CaptureSet.forall_weaken_effMode

theorem Ctx.modeBound_consC_inst (Γ : Ctx s) (C : CaptureSet s) (m : EMode) :
    (Γ.consC (.inst C)).ModeBound (.cvar .here) m ↔ Γ.SetBound C m := by
  unfold Ctx.ModeBound
  rw [Ctx.setBound_iff]
  exact CaptureSet.forall_weaken_effMode

/-- A capture binder that is neither bounded nor an instance is a leaf, in
both readings. -/
theorem Ctx.namesCapsP_consC_leaf (p : Bool) (Γ : Ctx s) {b : CapBound s}
    (hu : ∀ C, b ≠ .upper C) (hi : ∀ C, b ≠ .inst C) :
    (Γ.consC b).namesCapsP p (.cvar .here) = [.cvar .here] := by
  cases b with
  | upper C => exact absurd rfl (hu C)
  | inst C => exact absurd rfl (hi C)
  | root => rfl
  | star => rfl
  | loc _ _ => rfl
  | own _ _ => rfl
  | param _ => rfl

theorem Ctx.namesCaps_consC_leaf (Γ : Ctx s) {b : CapBound s}
    (hu : ∀ C, b ≠ .upper C) (hi : ∀ C, b ≠ .inst C) :
    (Γ.consC b).namesCaps (.cvar .here) = [.cvar .here] :=
  Ctx.namesCapsP_consC_leaf false Γ hu hi

theorem Ctx.modeBound_consC_leaf (Γ : Ctx s) {b : CapBound s}
    (hu : ∀ C, b ≠ .upper C) (hi : ∀ C, b ≠ .inst C) (m : EMode) :
    (Γ.consC b).ModeBound (.cvar .here) m ↔ EMode.eps ≤ m := by
  unfold Ctx.ModeBound Ctx.modeCaps
  rw [Ctx.namesCapsP_consC_leaf true Γ hu hi]
  simp [CapAtom.effMode]

/-- A capture name of a transparent binder: every atom its label reaches. -/
theorem Ctx.modeBound_cons_name_transparent (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) (ℓ : Label) (m : EMode) :
    (Γ.cons (.transparent T W Wc Fs)).ModeBound (.name .here ℓ) m ↔
      ∀ r ∈ Wc.reach ℓ, ∀ z ∈ Ctx.selfInner (fun a => Γ.modeCaps a) T r.base,
        z.effMode ≤ r.useMode.thr m := by
  unfold Ctx.ModeBound
  refine CaptureSet.forall_weaken_effMode.trans ?_
  constructor
  · intro h r hr z hz
    have := h (z.applyEMode r.useMode) (List.mem_flatMap.mpr ⟨r, hr, List.mem_map_of_mem hz⟩)
    rwa [CapAtom.effMode_applyEMode, EMode.comb_le_iff] at this
  · intro h y hy
    obtain ⟨r, hr, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [CapAtom.effMode_applyEMode, EMode.comb_le_iff]
    exact h r hr z hz

/-- A capture name of an opaque binder is its level root, at the plain mode. -/
theorem Ctx.modeBound_cons_name_opaque (Γ : Ctx s) (T : Ty s) (ℓ : Label) (m : EMode) :
    (Γ.cons (.opaque T)).ModeBound (.name .here ℓ) m ↔ EMode.eps ≤ m := by
  unfold Ctx.ModeBound
  show (∀ z ∈ [CapAtom.weaken Γ.rootAtom], _) ↔ _
  have h : (CapAtom.weaken (k := .var) Γ.rootAtom).effMode = .eps := by
    unfold Ctx.rootAtom
    cases Γ.root? <;> rfl
  simp [h]

/-- A capture name of a parameter is its level root, at the plain mode. -/
theorem Ctx.modeBound_cons_name_formal (Γ : Ctx s) (T : Ty s) (ℓ : Label) (m : EMode) :
    (Γ.cons (.formal T)).ModeBound (.name .here ℓ) m ↔ EMode.eps ≤ m := by
  unfold Ctx.ModeBound
  show (∀ z ∈ [CapAtom.weaken Γ.rootAtom], _) ↔ _
  have h : (CapAtom.weaken (k := .var) Γ.rootAtom).effMode = .eps := by
    unfold Ctx.rootAtom
    cases Γ.root? <;> rfl
  simp [h]

/-- The universal root is a leaf. -/
theorem Ctx.modeBound_top (Γ : Ctx s) (m : EMode) : Γ.ModeBound .top m ↔ EMode.eps ≤ m := by
  unfold Ctx.ModeBound
  cases Γ <;> simp [Ctx.namesCapsP, CapAtom.effMode]

/-- A moded atom has no names of its own. -/
theorem Ctx.modeBound_mode (Γ : Ctx s) (md : Mode) (a : CapAtom s) (m : EMode) :
    Γ.ModeBound (.mode md a) m := by
  intro z hz
  cases Γ <;> simp [Ctx.namesCapsP] at hz

/-! ### Maps between contexts that carry the bounds -/

/-- `f` carries every mode bound from `Γ` to `Γ'`. -/
def Ctx.ModeMap (Γ : Ctx s1) (f : CapAtom s1 → CapAtom s2) (Γ' : Ctx s2) : Prop :=
  ∀ a m, Γ.ModeBound a m → Γ'.ModeBound (f a) m

/-- A mode map that commutes with `base` and never raises the use mode
carries set bounds. -/
theorem Ctx.ModeMap.setBound {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap f Γ') (hb : ∀ a, (f a).base = f a.base) (he : ∀ a, (f a).useMode ≤ a.useMode)
    {C : CaptureSet s1} {m : EMode} (hC : Γ.SetBound C m) : Γ'.SetBound (C.map f) m := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  rw [hb]
  exact (h _ _ (hC c₀ hc₀)).mono (EMode.thr_anti (he c₀) m)

/-- A mode map carries the level rule's premise. -/
theorem Ctx.ModeMap.accessOnly {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap f Γ') (hb : ∀ a, (f a).base = f a.base) (he : ∀ a, (f a).useMode ≤ a.useMode)
    {e : CapAtom s1} (hacc : Γ.AccessOnly [e]) : Γ'.AccessOnly [f e] := by
  rw [Ctx.accessOnly_singleton] at hacc ⊢
  rw [hb]
  exact (h _ _ hacc).mono (EMode.thr_anti (he e) _)

theorem Ctx.ModeMap.id (Γ : Ctx s) : Γ.ModeMap (fun a => a) Γ := fun _ _ h => h

theorem Ctx.ModeMap.comp {Γ : Ctx s1} {Γ' : Ctx s2} {Γ'' : Ctx s3}
    {f : CapAtom s1 → CapAtom s2} {g : CapAtom s2 → CapAtom s3}
    (h : Γ.ModeMap f Γ') (h' : Γ'.ModeMap g Γ'') : Γ.ModeMap (fun a => g (f a)) Γ'' :=
  fun a m hm => h' _ _ (h a m hm)

theorem Ctx.ModeMap.weaken (Γ : Ctx s) (b : Binding s) :
    Γ.ModeMap (CapAtom.weaken (k := .var)) (Γ.cons b) :=
  fun a m h => (Γ.modeBound_weaken_iff b a m).mpr h

theorem Ctx.ModeMap.weakenC (Γ : Ctx s) (b : CapBound s) :
    Γ.ModeMap (CapAtom.weaken (k := .cap)) (Γ.consC b) :=
  fun a m h => (Γ.modeBound_weakenC_iff b a m).mpr h

/-! ### The search for self references under a map of atoms -/

/-- A map of atoms of the block's scope that keeps self references, modes and
the meet. -/
structure CapAtom.SelfMap (g : CapAtom (s1,x) → CapAtom (s2,x)) : Prop where
  selfLabel : ∀ a, (g a).selfLabel? = a.selfLabel?
  effMode : ∀ a, (g a).effMode = a.effMode
  applyEMode : ∀ m a, g (a.applyEMode m) = (g a).applyEMode m

/-- A self reference is a capture name. -/
theorem CapAtom.isTermB_of_selfLabel {a : CapAtom (s,x)} {l : Label} (h : a.selfLabel? = some l) :
    a.base.isTermB = true := by
  unfold CapAtom.selfLabel? at h
  split at h
  · rename_i heq; rw [heq]; rfl
  · cases h

theorem CapAtom.useMode_congr {a : CapAtom s1} {b : CapAtom s2}
    (hb : a.base.isTermB = b.base.isTermB) (he : a.effMode = b.effMode) :
    a.useMode = b.useMode := by
  unfold CapAtom.useMode; rw [hb, he]

theorem CapWitnesses.succs_map {g : CapAtom (s1,x) → CapAtom (s2,x)} (hg : CapAtom.SelfMap g)
    {Wc : CapWitnesses (s1,x)} {Wc' : CapWitnesses (s2,x)}
    (hget : ∀ l, Wc'.get l = (Wc.get l).map g) (p : Label × EMode) :
    Wc'.succs p = Wc.succs p := by
  unfold CapWitnesses.succs
  rw [hget, List.filterMap_map]
  congr 1
  funext a
  simp only [Function.comp_def, hg.selfLabel]
  cases hs : a.selfLabel? with
  | none => rfl
  | some l =>
      simp only [Option.map_some]
      have hs' : (g a).selfLabel? = some l := by rw [hg.selfLabel, hs]
      rw [CapAtom.useMode_congr (by rw [CapAtom.isTermB_of_selfLabel hs',
        CapAtom.isTermB_of_selfLabel hs]) (hg.effMode a)]

theorem CapWitnesses.reach_map {g : CapAtom (s1,x) → CapAtom (s2,x)} (hg : CapAtom.SelfMap g)
    {Wc : CapWitnesses (s1,x)} {Wc' : CapWitnesses (s2,x)}
    (hget : ∀ l, Wc'.get l = (Wc.get l).map g) (hat : Wc'.atoms = Wc.atoms.map g) (ℓ : Label) :
    Wc'.reach ℓ = (Wc.reach ℓ).map g := by
  have hstep : Wc'.reachStep = Wc.reachStep := by
    funext V
    unfold CapWitnesses.reachStep
    rw [show Wc'.succs = Wc.succs from funext (CapWitnesses.succs_map hg hget)]
  have hstates : Wc'.states ℓ = Wc.states ℓ := by
    unfold CapWitnesses.states
    rw [hat, List.filterMap_map]
    have hf : (CapAtom.selfLabel? ∘ g) = CapAtom.selfLabel? := funext hg.selfLabel
    rw [hf]
  have hpairs : Wc'.reachPairs ℓ = Wc.reachPairs ℓ := by
    unfold CapWitnesses.reachPairs
    rw [hstep, hstates]
  unfold CapWitnesses.reach
  rw [hpairs, List.map_flatMap]
  congr 1
  funext p
  rw [hget, List.filter_map, List.map_map, List.map_map]
  have hf : ((fun a => a.selfLabel?.isNone) ∘ g) = fun a => a.selfLabel?.isNone := by
    funext a; simp [hg.selfLabel]
  rw [hf]
  congr 1
  funext a
  simp [hg.applyEMode]

/-! ### The search reaches its fixed point

Every state the search visits is one of `Wc.states ℓ`, and each round that
is not yet closed adds a new one, so after as many rounds as there are states
the visited list is closed under `CapWitnesses.succs`. -/

/-- A list of states closed under one step. -/
def CapWitnesses.Closed (Wc : CapWitnesses (s,x)) (V : List (Label × EMode)) : Prop :=
  ∀ p ∈ V, ∀ q ∈ Wc.succs p, q ∈ V

theorem CapWitnesses.mem_reachStep {Wc : CapWitnesses (s,x)} {V : List (Label × EMode)}
    {q : Label × EMode} : q ∈ Wc.reachStep V ↔ q ∈ V ∨ ∃ p ∈ V, q ∈ Wc.succs p := by
  unfold CapWitnesses.reachStep
  rw [List.mem_append, List.mem_filter, List.mem_flatMap]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hq : q ∈ V
      · exact Or.inl hq
      · exact Or.inr ⟨h, by simpa using hq⟩

theorem CapAtom.selfLabel?_eq_some {a : CapAtom (s,x)} {l : Label} :
    a.selfLabel? = some l ↔ a.base = .name .here l := by
  unfold CapAtom.selfLabel?
  generalize a.base = b
  cases b with
  | name y l' =>
      cases y with
      | here => simp
      | there y => simp
  | var _ | cvar _ | top | mode _ _ => simp

theorem CapWitnesses.mem_get_atoms :
    ∀ {Wc : CapWitnesses s} {l : Label} {a : CapAtom s}, a ∈ Wc.get l → a ∈ Wc.atoms
  | .nil, _, _, h => by cases h
  | .cons W l' C, l, a, h => by
      unfold CapWitnesses.get at h
      unfold CapWitnesses.atoms
      split at h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (CapWitnesses.mem_get_atoms h)

theorem CapWitnesses.mem_states_of_label {Wc : CapWitnesses (s,x)} {ℓ l : Label} (m : EMode)
    (hl : l = ℓ ∨ l ∈ Wc.atoms.filterMap CapAtom.selfLabel?) : (l, m) ∈ Wc.states ℓ := by
  unfold CapWitnesses.states
  rw [List.mem_flatMap]
  refine ⟨l, ?_, ?_⟩
  · rcases hl with rfl | hl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ hl
  · cases m <;> simp

theorem CapWitnesses.succs_mem_states {Wc : CapWitnesses (s,x)} {ℓ : Label}
    {p q : Label × EMode} (hq : q ∈ Wc.succs p) : q ∈ Wc.states ℓ := by
  unfold CapWitnesses.succs at hq
  obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
  cases hs : a.selfLabel? with
  | none => rw [hs] at hq; cases hq
  | some l =>
      rw [hs] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      exact CapWitnesses.mem_states_of_label _
        (Or.inr (List.mem_filterMap.mpr ⟨a, CapWitnesses.mem_get_atoms ha, hs⟩))

theorem CapWitnesses.reachIter_states (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    ∀ (k : Nat) (q : Label × EMode), q ∈ Nat.repeat Wc.reachStep k [(ℓ, .eps)] →
      q ∈ Wc.states ℓ
  | 0, q, h => by
      rw [List.mem_singleton.mp h]
      exact CapWitnesses.mem_states_of_label _ (Or.inl rfl)
  | k + 1, q, h => by
      rcases CapWitnesses.mem_reachStep.mp h with h | ⟨_, _, hq⟩
      · exact CapWitnesses.reachIter_states Wc ℓ k q h
      · exact CapWitnesses.succs_mem_states hq

/-- The visited states counted in the list of all states. -/
def CapWitnesses.visitedCount (Wc : CapWitnesses (s,x)) (ℓ : Label) (V : List (Label × EMode)) :
    Nat :=
  ((Wc.states ℓ).filter fun p => decide (p ∈ V)).length

instance CapWitnesses.Closed.instDecidable (Wc : CapWitnesses (s,x)) (V : List (Label × EMode)) :
    Decidable (Wc.Closed V) := by
  unfold CapWitnesses.Closed; infer_instance

theorem CapWitnesses.not_closed_exists {Wc : CapWitnesses (s,x)} {V : List (Label × EMode)}
    (h : ¬ Wc.Closed V) : ∃ p ∈ V, ∃ q ∈ Wc.succs p, q ∉ V := by
  rcases (inferInstance : Decidable (∃ p ∈ V, ∃ q ∈ Wc.succs p, q ∉ V)) with hno | hyes
  · refine absurd ?_ h
    intro p hp q hq
    rcases (inferInstance : Decidable (q ∈ V)) with hn | hy
    · exact absurd ⟨p, hp, q, hq, hn⟩ hno
    · exact hy
  · exact hyes

theorem CapWitnesses.reachIter_closed_or (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    ∀ k : Nat, Wc.Closed (Nat.repeat Wc.reachStep k [(ℓ, .eps)]) ∨
      k + 1 ≤ Wc.visitedCount ℓ (Nat.repeat Wc.reachStep k [(ℓ, .eps)])
  | 0 => by
      right
      unfold CapWitnesses.visitedCount
      have h0 : (ℓ, EMode.eps) ∈ Wc.states ℓ := CapWitnesses.mem_states_of_label _ (Or.inl rfl)
      have := List.length_filter_lt_of_imp (p := fun _ => false)
        (q := fun p => decide (p ∈ Nat.repeat Wc.reachStep 0 [(ℓ, EMode.eps)])) (Wc.states ℓ)
        (fun _ _ h => by cases h) ⟨_, h0, by simp [Nat.repeat], rfl⟩
      simp at this
      omega
  | k + 1 => by
      rcases CapWitnesses.reachIter_closed_or Wc ℓ k with hc | hk
      · left
        intro p hp q hq
        have hp' : p ∈ Nat.repeat Wc.reachStep k [(ℓ, .eps)] := by
          rcases CapWitnesses.mem_reachStep.mp hp with hp | ⟨p₀, hp₀, hpq⟩
          · exact hp
          · exact hc p₀ hp₀ p hpq
        exact CapWitnesses.mem_reachStep.mpr (Or.inl (hc p hp' q hq))
      · by_cases hcl : Wc.Closed (Nat.repeat Wc.reachStep (k + 1) [(ℓ, .eps)])
        · exact Or.inl hcl
        · right
          have hnc : ¬ Wc.Closed (Nat.repeat Wc.reachStep k [(ℓ, .eps)]) := by
            intro hc
            apply hcl
            intro p hp q hq
            have hp' : p ∈ Nat.repeat Wc.reachStep k [(ℓ, .eps)] := by
              rcases CapWitnesses.mem_reachStep.mp hp with hp | ⟨p₀, hp₀, hpq⟩
              · exact hp
              · exact hc p₀ hp₀ p hpq
            exact CapWitnesses.mem_reachStep.mpr (Or.inl (hc p hp' q hq))
          obtain ⟨p, hp, q, hq, hnq⟩ := CapWitnesses.not_closed_exists hnc
          have hlt := List.length_filter_lt_of_imp
            (p := fun p => decide (p ∈ Nat.repeat Wc.reachStep k [(ℓ, EMode.eps)]))
            (q := fun p => decide (p ∈ Nat.repeat Wc.reachStep (k + 1) [(ℓ, EMode.eps)]))
            (Wc.states ℓ)
            (fun r _ hr => by
              simp only [decide_eq_true_eq] at hr ⊢
              exact CapWitnesses.mem_reachStep.mpr (Or.inl hr))
            ⟨q, CapWitnesses.succs_mem_states hq,
              by simp only [decide_eq_true_eq]
                 exact CapWitnesses.mem_reachStep.mpr (Or.inr ⟨p, hp, hq⟩),
              by simpa using hnq⟩
          unfold CapWitnesses.visitedCount at hk ⊢
          omega

/-- **The search is closed.** -/
theorem CapWitnesses.reachPairs_closed (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    Wc.Closed (Wc.reachPairs ℓ) := by
  rcases CapWitnesses.reachIter_closed_or Wc ℓ (Wc.states ℓ).length with h | h
  · exact h
  · have := List.length_filter_le (fun p => decide (p ∈ Wc.reachPairs ℓ)) (Wc.states ℓ)
    unfold CapWitnesses.visitedCount at h
    unfold CapWitnesses.reachPairs at this
    omega

theorem CapWitnesses.start_mem_reachPairs (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    (ℓ, EMode.eps) ∈ Wc.reachPairs ℓ := by
  unfold CapWitnesses.reachPairs
  generalize (Wc.states ℓ).length = k
  induction k with
  | zero => exact List.mem_singleton_self _
  | succ k ih => exact CapWitnesses.mem_reachStep.mpr (Or.inl ih)

/-- A self reference of a reached witness is reached, at the mode of the path. -/
theorem CapWitnesses.reachPairs_step {Wc : CapWitnesses (s,x)} {ℓ : Label} {p : Label × EMode}
    (hp : p ∈ Wc.reachPairs ℓ) {c : CapAtom (s,x)} (hc : c ∈ Wc.get p.1) {l : Label}
    (hl : c.base = .name .here l) : (l, p.2.comb c.useMode) ∈ Wc.reachPairs ℓ := by
  refine CapWitnesses.reachPairs_closed Wc ℓ p hp _ ?_
  unfold CapWitnesses.succs
  refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
  rw [CapAtom.selfLabel?_eq_some.mpr hl]
  rfl

/-- Every other atom of a reached witness is reached, under the mode of the
path. -/
theorem CapWitnesses.mem_reach {Wc : CapWitnesses (s,x)} {ℓ : Label} {p : Label × EMode}
    (hp : p ∈ Wc.reachPairs ℓ) {c : CapAtom (s,x)} (hc : c ∈ Wc.get p.1)
    (hn : c.selfLabel? = none) : c.applyEMode p.2 ∈ Wc.reach ℓ := by
  unfold CapWitnesses.reach
  exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, by simp [hn]⟩)⟩

/-- A consumable binder is its own name, in both readings. -/
theorem Ctx.namesCapsP_consumable (p : Bool) : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.lookupCap κ).consumable = true → Γ.namesCapsP p (.cvar κ) = [.cvar κ]
  | _, .consC _ b, .here, h => by
      have h' : (CapBound.weaken (k := .cap) b).consumable = true := h
      rw [CapBound.consumable_weaken] at h'
      cases b <;> first | rfl | simp [CapBound.consumable] at h'
  | _, .consC Γ _, .there κ, h => by
      have h' : (CapBound.weaken (Γ.lookupCap κ)).consumable = true := h
      rw [CapBound.consumable_weaken] at h'
      show CaptureSet.weaken (Γ.namesCapsP p (.cvar κ)) = _
      rw [Ctx.namesCapsP_consumable p Γ κ h']
      rfl
  | _, .cons Γ _, .there κ, h => by
      have h' : (CapBound.weaken (Γ.lookupCap κ)).consumable = true := h
      rw [CapBound.consumable_weaken] at h'
      show CaptureSet.weaken (Γ.namesCapsP p (.cvar κ)) = _
      rw [Ctx.namesCapsP_consumable p Γ κ h']
      rfl

theorem Ctx.namesCaps_consumable {s : Sig} (Γ : Ctx s) (κ : BVar s .cap)
    (h : (Γ.lookupCap κ).consumable = true) : Γ.namesCaps (.cvar κ) = [.cvar κ] :=
  Ctx.namesCapsP_consumable false Γ κ h

theorem List.filterMap_eq_nil_of {α β : Type} {f : α → Option β} :
    ∀ L : List α, (∀ a ∈ L, f a = none) → L.filterMap f = []
  | [], _ => rfl
  | a :: L, h => by
      rw [List.filterMap_cons, h a (List.mem_cons_self ..)]
      exact List.filterMap_eq_nil_of L (fun b hb => h b (List.mem_cons_of_mem a hb))

theorem List.filter_const_false {α : Type} : ∀ L : List α, L.filter (fun _ => false) = []
  | [] => rfl
  | _ :: L => List.filter_const_false L

/-- A head that consumes nothing causes no kill. -/
theorem Ctx.killFor_of_noConsume {Γ : Ctx s} {C : CaptureSet s} (h : Γ.NoConsume C) :
    Γ.killFor C = Γ := by
  have hc : Γ.consumedNames C = [] := by
    unfold Ctx.consumedNames
    refine List.filterMap_eq_nil_of _ (fun a ha => ?_)
    rw [if_neg (h a ha)]
  unfold Ctx.killFor Ctx.ownClosure
  rw [hc]
  have : ∀ k, Nat.repeat Γ.ownStep k ([] : List (BVar s .cap)) = [] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        show Γ.ownStep (Nat.repeat Γ.ownStep k []) = []
        rw [ih]
        exact List.filter_const_false Γ.capBinders
  rw [this]
  rfl

/-- A set that consumes nothing is separated from every set: nothing it
consumes can be named.  It is `ArgSep` on a base program. -/
theorem Ctx.argSep_of_noConsume {Γ : Ctx s} {B C : CaptureSet s} (h : Γ.NoConsume C) :
    Γ.ArgSep B C := by
  intro _ _ κ _
  have hc : Γ.consumedNames C = [] := by
    unfold Ctx.consumedNames
    refine List.filterMap_eq_nil_of _ (fun a ha => ?_)
    rw [if_neg (h a ha)]
  rw [hc]
  refine ⟨fun hκ => ?_, fun l hl => absurd hl List.not_mem_nil⟩
  rw [Ctx.mem_ownClosure] at hκ
  rcases hκ with hκ | ⟨_, hh, _⟩
  · exact absurd hκ (List.not_mem_nil)
  · exact absurd hh (List.not_mem_nil)

/-- A set that consumes nothing passes the kill premise, so every base head
passes. -/
theorem Ctx.KillOk.of_noConsume {Γ : Ctx s} {C : CaptureSet s} (h : Γ.NoConsume C) :
    Γ.KillOk C := fun a ha hm => absurd hm (h a ha)

/-- `ConsumeOk` gives `KillOk`: the callee's set at `app` needs no new
premise. -/
theorem Ctx.KillOk.of_consumeOk {Γ : Ctx s} {C : CaptureSet s} (h : Γ.ConsumeOk C) :
    Γ.KillOk C := by
  intro a ha hm
  obtain ⟨κ, hb, hc⟩ := h a ha hm
  exact ⟨κ, hb, hc.1⟩

/-! ### Consumed leaves -/

theorem CapAtom.cvar?_eq_some {a : CapAtom s} {κ : BVar s .cap} :
    a.cvar? = some κ ↔ a = .cvar κ := by
  cases a <;> simp [CapAtom.cvar?]

theorem Ctx.leafFn_eq_some {a : CapAtom s} {κ : BVar s .cap} :
    (if a.effMode = .consume then a.base.cvar? else none) = some κ ↔
      a.effMode = .consume ∧ a.base = .cvar κ := by
  by_cases h : a.effMode = .consume
  · rw [if_pos h, CapAtom.cvar?_eq_some]; exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · rw [if_neg h]; simp [h]

/-- **A consumed leaf is a consumed name.** -/
theorem Ctx.consumedLeaves_sub (Γ : Ctx s) (C : CaptureSet s) {κ : BVar s .cap}
    (h : κ ∈ Γ.consumedLeaves C) : κ ∈ Γ.consumedNames C := by
  unfold Ctx.consumedLeaves at h
  unfold Ctx.consumedNames
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.mp h
  obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hx
  refine List.mem_filterMap.mpr ⟨x, ?_, hfx⟩
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_flatMap.mpr ⟨x, hxc, Γ.mem_expandNames_self x⟩⟩

theorem CapAtom.weaken_base' {k : Kind} (a : CapAtom s) :
    (CapAtom.weaken (k := k) a).base = CapAtom.weaken (k := k) a.base := by
  simp [CapAtom.weaken]

theorem CapAtom.weaken_effMode' {k : Kind} (a : CapAtom s) :
    (CapAtom.weaken (k := k) a).effMode = a.effMode := by
  simp [CapAtom.weaken]

theorem CapAtom.weaken_reapply {k : Kind} (c x : CapAtom s) :
    (CapAtom.weaken (k := k) c).reapply (CapAtom.weaken (k := k) x) =
      CapAtom.weaken (k := k) (c.reapply x) := by
  rw [CapAtom.reapply_eq, CapAtom.reapply_eq, CapAtom.weaken_effMode']
  exact (CapAtom.applyEMode_weaken _ _).symm

theorem CapAtom.weaken_cvar? {k : Kind} (a : CapAtom s) :
    (CapAtom.weaken (k := k) a).cvar? = a.cvar?.map BVar.there := by
  cases a <;> rfl

theorem Ctx.leafFn_weaken {k : Kind} (a : CapAtom s) :
    (if (CapAtom.weaken (k := k) a).effMode = .consume then
        (CapAtom.weaken (k := k) a).base.cvar? else none) =
      (if a.effMode = .consume then a.base.cvar? else none).map BVar.there := by
  rw [CapAtom.weaken_effMode', CapAtom.weaken_base']
  by_cases h : a.effMode = .consume
  · rw [if_pos h, if_pos h, CapAtom.weaken_cvar?]
  · rw [if_neg h, if_neg h]; rfl

/-- **The leaves of an old set under a capture weakening** are its leaves, with
no premise on the set. -/
theorem Ctx.consumedLeaves_weakenC (Γ : Ctx s) (b : CapBound s) (C : CaptureSet s) :
    (Γ.consC b).consumedLeaves (CaptureSet.weaken (k := .cap) C) =
      (Γ.consumedLeaves C).map BVar.there := by
  unfold Ctx.consumedLeaves
  have hph : ∀ c : CapAtom s,
      ((Γ.consC b).namesCaps (CapAtom.weaken (k := .cap) c).base).map
          (CapAtom.weaken (k := .cap) c).useApply
        = ((Γ.namesCaps c.base).map c.useApply).map (CapAtom.weaken (k := .cap)) := by
    intro c
    rw [CapAtom.weaken_base', Ctx.namesCaps_weakenC]
    simp only [CaptureSet.weaken, CaptureSet.rename, List.map_map]
    apply List.map_congr_left
    intro x _
    exact CapAtom.weaken_useApply c x
  show ((C.map (CapAtom.weaken (k := .cap))).flatMap _).filterMap _ = _
  rw [List.flatMap_map]
  simp only [hph]
  rw [← List.map_flatMap, List.filterMap_map, List.map_filterMap]
  congr 1
  funext a
  exact Ctx.leafFn_weaken a

/-- The same under a term binder. -/
theorem Ctx.consumedLeaves_weaken (Γ : Ctx s) (b : Binding s) (C : CaptureSet s) :
    (Γ.cons b).consumedLeaves (CaptureSet.weaken (k := .var) C) =
      (Γ.consumedLeaves C).map BVar.there := by
  unfold Ctx.consumedLeaves
  have hph : ∀ c : CapAtom s,
      ((Γ.cons b).namesCaps (CapAtom.weaken (k := .var) c).base).map
          (CapAtom.weaken (k := .var) c).useApply
        = ((Γ.namesCaps c.base).map c.useApply).map (CapAtom.weaken (k := .var)) := by
    intro c
    rw [CapAtom.weaken_base', Ctx.namesCaps_weaken]
    simp only [CaptureSet.weaken, CaptureSet.rename, List.map_map]
    apply List.map_congr_left
    intro x _
    exact CapAtom.weaken_useApply c x
  show ((C.map (CapAtom.weaken (k := .var))).flatMap _).filterMap _ = _
  rw [List.flatMap_map]
  simp only [hph]
  rw [← List.map_flatMap, List.filterMap_map, List.map_filterMap]
  congr 1
  funext a
  exact Ctx.leafFn_weaken a

/-- A consumable witness name of a fresh pack is a leaf of its charge. -/
theorem Ctx.mem_consumedLeaves_charge (Γ : Ctx s) {W : CaptureSet s} {κ : BVar s .cap}
    (hW : CapAtom.cvar κ ∈ W) (hc : (Γ.lookupCap κ).consumable = true) :
    κ ∈ Γ.consumedLeaves (W.map (CapAtom.mode .consume)) := by
  unfold Ctx.consumedLeaves
  refine List.mem_filterMap.mpr ⟨CapAtom.mode .consume (.cvar κ), ?_, ?_⟩
  · refine List.mem_flatMap.mpr ⟨CapAtom.mode .consume (.cvar κ), List.mem_map_of_mem hW, ?_⟩
    show CapAtom.mode .consume (.cvar κ) ∈
      List.map (CapAtom.mode Mode.consume (CapAtom.cvar κ)).useApply (Γ.namesCaps (CapAtom.cvar κ))
    rw [Ctx.namesCaps_consumable Γ κ hc]
    exact List.mem_singleton.mpr rfl
  · rfl

/-! ### All roots open the same binders -/

/-- **All roots at one mode open the same binders** (plan-5h decision 38).  So
sending a scope root to `⊤` changes no name but the root itself. -/
theorem Ctx.expandNames_root (Γ : Ctx s) {r r' : CapAtom s} (hr : Γ.isRootB r = true)
    (hr' : Γ.isRootB r' = true) (m : EMode) :
    (Γ.expandNames (r.applyEMode m)).tail = (Γ.expandNames (r'.applyEMode m)).tail := by
  have hb : ∀ {a : CapAtom s}, Γ.isRootB a = true → a.base = a ∧ a.effMode = .eps := by
    intro a ha; cases a <;> simp_all [Ctx.isRootB, CapAtom.base, CapAtom.effMode]
  obtain ⟨hb1, he1⟩ := hb hr
  obtain ⟨hb2, he2⟩ := hb hr'
  unfold Ctx.expandNames
  rw [CapAtom.base_applyEMode, CapAtom.base_applyEMode, hb1, hb2, if_pos hr, if_pos hr']
  simp only [List.tail_cons]
  apply List.map_congr_left
  intro κ _
  rw [CapAtom.reapply_eq, CapAtom.reapply_eq, CapAtom.effMode_applyEMode,
    CapAtom.effMode_applyEMode, he1, he2]

/-- **In a context that binds no parameter, access-only is consuming
nothing**, and so in every store context. -/
theorem Ctx.accessOnly_iff_noConsume {Γ : Ctx s} (h : Γ.formalFree = true) {C : CaptureSet s} :
    Γ.AccessOnly C ↔ Γ.NoConsume C := by
  rw [Ctx.noConsume_iff]
  unfold Ctx.AccessOnly Ctx.SetBound Ctx.ModeBound Ctx.modeCaps Ctx.namesCaps
  rw [Ctx.namesCapsP_eq_of_formalFree h true false]

/-- **A set of consumable names is access-only**: each name is itself in
the mode reading, at the plain mode.  A fresh pack's residual reads it when
it uses `ownLe` in `Ctx.scopeOwn W`. -/
theorem Ctx.accessOnly_of_consumable {Γ : Ctx s} {W : CaptureSet s} (hW : W.IsNames)
    (hc : ∀ κ, CapAtom.cvar κ ∈ W → (Γ.lookupCap κ).consumable = true) :
    Γ.AccessOnly W := by
  intro c hcW
  obtain ⟨κ, rfl⟩ := hW c hcW
  intro z hz
  have hn : Γ.modeCaps (CapAtom.cvar κ) = [CapAtom.cvar κ] :=
    Ctx.namesCapsP_consumable true Γ κ (hc κ hcW)
  have hz' : z ∈ Γ.modeCaps (CapAtom.cvar κ) := hz
  rw [hn, List.mem_singleton] at hz'
  subst hz'
  exact EMode.le_refl _

/-- **The residual of a fresh pack may put the witness below the heir**: in
`Ctx.scopeOwn W` the twice weakened witness is access-only when every name of
`W` is consumable, so `ownLe` at the heir has its premise. -/
theorem Ctx.accessOnly_scopeOwn {Γ : Ctx s} {W : CaptureSet s} (hW : W.IsNames)
    (hc : ∀ κ, CapAtom.cvar κ ∈ W → (Γ.lookupCap κ).consumable = true) :
    (Γ.scopeOwn W).AccessOnly
      (CaptureSet.weaken (k := .cap) (CaptureSet.weaken (k := .cap) W)) := by
  refine Ctx.accessOnly_of_consumable (hW.weaken.weaken) ?_
  intro κ hκ
  obtain ⟨κ₁, rfl, hκ₁⟩ := CaptureSet.cvar_mem_weaken hκ
  obtain ⟨κ₀, rfl, hκ₀⟩ := CaptureSet.cvar_mem_weaken hκ₁
  show (CapBound.weaken (k := .cap) (CapBound.weaken (k := .cap) (Γ.lookupCap κ₀))).consumable
    = true
  rw [CapBound.consumable_weaken, CapBound.consumable_weaken]
  exact hc κ₀ hκ₀

/-- On names, the charged witness is the witness at the `consume` mode. -/
theorem CaptureSet.charged_of_isNames : ∀ {W : CaptureSet s}, W.IsNames → W.charged = W.consume
  | [], _ => rfl
  | a :: W, h => by
      obtain ⟨κ, rfl⟩ := h a (List.mem_cons_self ..)
      have ih := CaptureSet.charged_of_isNames (W := W) (fun b hb => h b (List.mem_cons_of_mem _ hb))
      simp only [CaptureSet.charged, CaptureSet.consume, List.map_cons] at ih ⊢
      rw [ih]
      rfl

/-- A statement about every capture binder a set lists, as a statement about
its elements. -/
theorem CaptureSet.forall_cvar_mem_iff {W : CaptureSet s} {P : BVar s .cap → Prop} :
    (∀ κ, CapAtom.cvar κ ∈ W → P κ) ↔ ∀ a ∈ W, ∀ κ, a = CapAtom.cvar κ → P κ :=
  ⟨fun h _ ha κ he => h κ (he ▸ ha), fun h κ hκ => h _ hκ κ rfl⟩

instance CaptureSet.decForallCvarMem (W : CaptureSet s) (P : BVar s .cap → Prop)
    [DecidablePred P] : Decidable (∀ κ, CapAtom.cvar κ ∈ W → P κ) :=
  decidable_of_iff _ CaptureSet.forall_cvar_mem_iff.symm

/-! ## The algebra of mode bounds

`Ctx.ModeLe Γ C D` says every mode bound of `D` is one of `C`.  Closed
capture evidence `C ⊑ D` never raises the mode of a name in a store
(`Ctx.modeSound_store`).  The lemmas below take the evidence rules one by
one.  They read the mode reading only, and they hold in every context. -/

/-- Every mode bound of `D` is a mode bound of `C`. -/
def Ctx.ModeLe (Γ : Ctx s) (C D : CaptureSet s) : Prop :=
  ∀ m, Γ.SetBound D m → Γ.SetBound C m

/-- Both directions. -/
def Ctx.ModeEq (Γ : Ctx s) (C D : CaptureSet s) : Prop := Γ.ModeLe C D ∧ Γ.ModeLe D C

theorem Ctx.ModeLe.refl (Γ : Ctx s) (C : CaptureSet s) : Γ.ModeLe C C := fun _ h => h

theorem Ctx.ModeLe.trans {Γ : Ctx s} {C₁ C₂ C₃ : CaptureSet s} (h₁ : Γ.ModeLe C₁ C₂)
    (h₂ : Γ.ModeLe C₂ C₃) : Γ.ModeLe C₁ C₃ :=
  fun m h => h₁ m (h₂ m h)

theorem Ctx.ModeLe.of_subset {Γ : Ctx s} {C D : CaptureSet s} (h : C.Subset D) :
    Γ.ModeLe C D :=
  fun _ hD c hc => hD c (h c hc)

theorem Ctx.ModeLe.union {Γ : Ctx s} {C₁ C₂ D : CaptureSet s} (h₁ : Γ.ModeLe C₁ D)
    (h₂ : Γ.ModeLe C₂ D) : Γ.ModeLe (C₁ ∪ C₂) D := by
  intro m hD c hc
  rw [CaptureSet.union_def] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ m hD c hc
  · exact h₂ m hD c hc

theorem Ctx.ModeEq.refl (Γ : Ctx s) (C : CaptureSet s) : Γ.ModeEq C C :=
  ⟨Ctx.ModeLe.refl Γ C, Ctx.ModeLe.refl Γ C⟩

theorem Ctx.ModeEq.symm {Γ : Ctx s} {C D : CaptureSet s} (h : Γ.ModeEq C D) : Γ.ModeEq D C :=
  ⟨h.2, h.1⟩

theorem Ctx.ModeEq.trans {Γ : Ctx s} {C₁ C₂ C₃ : CaptureSet s} (h₁ : Γ.ModeEq C₁ C₂)
    (h₂ : Γ.ModeEq C₂ C₃) : Γ.ModeEq C₁ C₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩


theorem EMode.thr_ro_left (m : EMode) : EMode.thr .ro m = .consume := rfl

theorem EMode.thr_eps_left (m : EMode) : EMode.thr .eps m = m := rfl

/-! ### Weakening of set bounds -/

theorem Ctx.setBound_weaken_iff (Γ : Ctx s) (b : Binding s) (C : CaptureSet s) (m : EMode) :
    (Γ.cons b).SetBound (CaptureSet.weaken C) m ↔ Γ.SetBound C m := by
  constructor
  · intro h c hc
    have := h _ (CaptureSet.weaken_mem_weaken.mpr hc)
    rw [CapAtom.weaken, CapAtom.base_rename, CapAtom.useMode_rename] at this
    exact (Γ.modeBound_weaken_iff b _ _).mp this
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp hc
    rw [CapAtom.weaken, CapAtom.base_rename, CapAtom.useMode_rename]
    exact (Γ.modeBound_weaken_iff b _ _).mpr (h y hy)

theorem Ctx.setBound_weakenC_iff (Γ : Ctx s) (b : CapBound s) (C : CaptureSet s) (m : EMode) :
    (Γ.consC b).SetBound (CaptureSet.weaken C) m ↔ Γ.SetBound C m := by
  constructor
  · intro h c hc
    have := h _ (CaptureSet.weaken_mem_weaken.mpr hc)
    rw [CapAtom.weaken, CapAtom.base_rename, CapAtom.useMode_rename] at this
    exact (Γ.modeBound_weakenC_iff b _ _).mp this
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp hc
    rw [CapAtom.weaken, CapAtom.base_rename, CapAtom.useMode_rename]
    exact (Γ.modeBound_weakenC_iff b _ _).mpr (h y hy)

theorem Ctx.modeLe_weaken_iff (Γ : Ctx s) (b : Binding s) (C D : CaptureSet s) :
    (Γ.cons b).ModeLe (CaptureSet.weaken C) (CaptureSet.weaken D) ↔ Γ.ModeLe C D := by
  constructor
  · intro h m hD
    exact (Γ.setBound_weaken_iff b C m).mp (h m ((Γ.setBound_weaken_iff b D m).mpr hD))
  · intro h m hD
    exact (Γ.setBound_weaken_iff b C m).mpr (h m ((Γ.setBound_weaken_iff b D m).mp hD))

theorem Ctx.modeLe_weakenC_iff (Γ : Ctx s) (b : CapBound s) (C D : CaptureSet s) :
    (Γ.consC b).ModeLe (CaptureSet.weaken C) (CaptureSet.weaken D) ↔ Γ.ModeLe C D := by
  constructor
  · intro h m hD
    exact (Γ.setBound_weakenC_iff b C m).mp (h m ((Γ.setBound_weakenC_iff b D m).mpr hD))
  · intro h m hD
    exact (Γ.setBound_weakenC_iff b C m).mpr (h m ((Γ.setBound_weakenC_iff b D m).mp hD))

/-! ### The names of a binder, one binder at a time -/

/-- The binder of a term variable is a parameter. -/
def Ctx.isFormalVar : Ctx s → BVar s .var → Bool
  | .cons _ b, .here => b.isFormal
  | .cons Γ _, .there y => Γ.isFormalVar y
  | .consC Γ _, .there y => Γ.isFormalVar y

/-- A context that binds no parameter has no parameter variable. -/
theorem Ctx.isFormalVar_of_formalFree : ∀ {s : Sig} {Γ : Ctx s}, Γ.formalFree = true →
    ∀ x, Γ.isFormalVar x = false
  | _, .cons Γ b, h, .here => by
      have h' : b.isFormal = false ∧ Γ.formalFree = true := by simpa [Ctx.formalFree] using h
      exact h'.1
  | _, .cons Γ b, h, .there y => by
      have h' : b.isFormal = false ∧ Γ.formalFree = true := by simpa [Ctx.formalFree] using h
      exact Ctx.isFormalVar_of_formalFree h'.2 y
  | _, .consC Γ _, h, .there y => Ctx.isFormalVar_of_formalFree (Γ := Γ) h y

/-- A binder that records fields is transparent, so it is no parameter. -/
theorem Ctx.isFormalVar_of_lookupFields : ∀ {s : Sig} {Γ : Ctx s} {y : BVar s .var}
    {Fs : List Label}, Γ.lookupFields y = some Fs → Γ.isFormalVar y = false
  | _, .cons _ b, .here, _, h => by
      cases b with
      | «opaque» _ => rfl
      | transparent _ _ _ _ => rfl
      | formal _ => cases h
  | _, .cons Γ b, .there y, Fs, h =>
      Ctx.isFormalVar_of_lookupFields (Γ := Γ) (y := y) (Fs := Fs) (by cases b <;> exact h)
  | _, .consC Γ _, .there y, Fs, h =>
      Ctx.isFormalVar_of_lookupFields (Γ := Γ) (y := y) (Fs := Fs) h

theorem Ty.captureSet_renameSucc (T : Ty s) :
    (T.rename (Rename.succ (k := k))).captureSet = CaptureSet.weaken T.captureSet := by
  cases T; rfl

/-- A term binder that is no parameter has the bounds of its declared set. -/
theorem Ctx.modeBound_var : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var),
    Γ.isFormalVar x = false → ∀ m : EMode,
    Γ.ModeBound (.var x) m ↔ Γ.SetBound (Γ.lookupTy x).captureSet m
  | _, .cons Γ b, .here, hx, m => by
      rw [Ctx.modeBound_cons_here Γ hx]
      show _ ↔ (Γ.cons b).SetBound (b.ty.rename Rename.succ).captureSet m
      rw [Ty.captureSet_renameSucc]
      exact (Γ.setBound_weaken_iff b _ m).symm
  | _, .cons Γ b, .there y, hx, m => by
      show (Γ.cons b).ModeBound (CapAtom.weaken (.var y)) m ↔
        (Γ.cons b).SetBound ((Γ.lookupTy y).rename Rename.succ).captureSet m
      rw [Γ.modeBound_weaken_iff b, Ty.captureSet_renameSucc]
      exact (Ctx.modeBound_var Γ y hx m).trans (Γ.setBound_weaken_iff b _ m).symm
  | _, .consC Γ b, .there y, hx, m => by
      show (Γ.consC b).ModeBound (CapAtom.weaken (.var y)) m ↔
        (Γ.consC b).SetBound ((Γ.lookupTy y).rename Rename.succ).captureSet m
      rw [Γ.modeBound_weakenC_iff b, Ty.captureSet_renameSucc]
      exact (Ctx.modeBound_var Γ y hx m).trans (Γ.setBound_weakenC_iff b _ m).symm

/-- A capture binder that is neither bounded nor an instance stands for itself. -/
def CapBound.isLeaf : CapBound s → Bool
  | .upper _ | .inst _ => false
  | _ => true

theorem CapBound.isLeaf_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).isLeaf = b.isLeaf := by
  cases b <;> rfl

theorem Ctx.modeBound_leaf : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.lookupCap κ).isLeaf = true → ∀ m, Γ.ModeBound (.cvar κ) m ↔ EMode.eps ≤ m
  | _, .consC Γ b, .here, h, m => by
      have hb : b.isLeaf = true := by
        have h' : (CapBound.weaken (k := .cap) b).isLeaf = true := h
        rwa [CapBound.weaken, CapBound.isLeaf_rename] at h'
      refine Ctx.modeBound_consC_leaf Γ ?_ ?_ m
      · intro C hC; subst hC; simp [CapBound.isLeaf] at hb
      · intro C hC; subst hC; simp [CapBound.isLeaf] at hb
  | _, .consC Γ b, .there κ, h, m => by
      have h' : (Γ.lookupCap κ).isLeaf = true := by
        have h'' : (CapBound.weaken (k := .cap) (Γ.lookupCap κ)).isLeaf = true := h
        rwa [CapBound.weaken, CapBound.isLeaf_rename] at h''
      show (Γ.consC b).ModeBound (CapAtom.weaken (.cvar κ)) m ↔ _
      rw [Γ.modeBound_weakenC_iff b]
      exact Ctx.modeBound_leaf Γ κ h' m
  | _, .cons Γ b, .there κ, h, m => by
      have h' : (Γ.lookupCap κ).isLeaf = true := by
        have h'' : (CapBound.weaken (k := .var) (Γ.lookupCap κ)).isLeaf = true := h
        rwa [CapBound.weaken, CapBound.isLeaf_rename] at h''
      show (Γ.cons b).ModeBound (CapAtom.weaken (.cvar κ)) m ↔ _
      rw [Γ.modeBound_weaken_iff b]
      exact Ctx.modeBound_leaf Γ κ h' m

/-- An instance binder has the bounds of its set. -/
theorem Ctx.modeBound_inst : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) (C : CaptureSet s),
    Γ.lookupCap κ = .inst C → ∀ m, Γ.ModeBound (.cvar κ) m ↔ Γ.SetBound C m
  | _, .consC Γ b, .here, C, h, m => by
      cases b with
      | inst C₀ =>
          have hC : C = CaptureSet.weaken C₀ := by
            have h' : CapBound.inst (C₀.rename Rename.succ) = CapBound.inst C := h
            cases h'; rfl
          subst hC
          rw [Ctx.modeBound_consC_inst, Γ.setBound_weakenC_iff]
      | root | star | upper _ | loc _ _ | own _ _ | param _ => cases h
  | _, .consC Γ b, .there κ, C, h, m => by
      have h' : CapBound.weaken (k := .cap) (Γ.lookupCap κ) = .inst C := h
      cases hb : Γ.lookupCap κ with
      | inst C₀ =>
          rw [hb] at h'
          have hC : C = CaptureSet.weaken C₀ := by cases h'; rfl
          subst hC
          show (Γ.consC b).ModeBound (CapAtom.weaken (.cvar κ)) m ↔ _
          rw [Γ.modeBound_weakenC_iff b, Γ.setBound_weakenC_iff b]
          exact Ctx.modeBound_inst Γ κ C₀ hb m
      | root | star | upper _ | loc _ _ | own _ _ | param _ => rw [hb] at h'; cases h'
  | _, .cons Γ b, .there κ, C, h, m => by
      have h' : CapBound.weaken (k := .var) (Γ.lookupCap κ) = .inst C := h
      cases hb : Γ.lookupCap κ with
      | inst C₀ =>
          rw [hb] at h'
          have hC : C = CaptureSet.weaken C₀ := by cases h'; rfl
          subst hC
          show (Γ.cons b).ModeBound (CapAtom.weaken (.cvar κ)) m ↔ _
          rw [Γ.modeBound_weaken_iff b, Γ.setBound_weaken_iff b]
          exact Ctx.modeBound_inst Γ κ C₀ hb m
      | root | star | upper _ | loc _ _ | own _ _ | param _ => rw [hb] at h'; cases h'

/-! ### The rules one by one -/

/-- A root is a plain leaf: it has no read-only bound. -/
theorem Ctx.setBound_root {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) {m : EMode}
    (h : Γ.SetBound [r] m) : EMode.eps ≤ m := by
  rw [Ctx.setBound_singleton] at h
  cases r with
  | top => exact (Γ.modeBound_top _).mp h
  | cvar κ =>
      have hl : (Γ.lookupCap κ).isLeaf = true := by
        have hr' : (Γ.lookupCap κ).isRoot = true := hr
        cases hb : Γ.lookupCap κ <;> simp_all [CapBound.isRoot, CapBound.isLeaf]
      exact (Γ.modeBound_leaf κ hl _).mp h
  | var _ => cases hr
  | name _ _ => cases hr
  | mode _ _ => cases hr

theorem Ctx.modeLe_level {Γ : Ctx s} {e r : CapAtom s} (hr : Γ.IsRoot r)
    (he : Γ.AccessOnly [e]) : Γ.ModeLe [e] [r] := by
  intro m hD
  exact Ctx.SetBound.mono he (Ctx.setBound_root hr hD)

/-- The use mode is monotone in the mode of `atMode`. -/
theorem CapAtom.useMode_atMode_le (a : CapAtom s) {m1 m2 : EMode} (h : m1 ≤ m2) :
    (a.atMode m1).useMode ≤ (a.atMode m2).useMode := by
  unfold CapAtom.useMode
  rw [CapAtom.base_atMode, CapAtom.base_atMode, CapAtom.effMode_atMode, CapAtom.effMode_atMode]
  generalize a.base.isTermB = t
  cases t <;> cases m1 <;> cases m2 <;> first | decide | exact absurd h (by decide)

theorem Ctx.modeLe_modeLe {Γ : Ctx s} (a : CapAtom s) {m1 m2 : EMode} (h : m1 ≤ m2) :
    Γ.ModeLe [a.atMode m1] [a.atMode m2] := by
  intro m hD
  rw [Ctx.setBound_singleton, CapAtom.base_atMode] at hD ⊢
  exact hD.mono (EMode.thr_anti (CapAtom.useMode_atMode_le a h) m)

theorem Ctx.setBound_ro (Γ : Ctx s) (C : CaptureSet s) (m : EMode) : Γ.SetBound C.ro m := by
  intro c hc
  obtain ⟨c₀, -, rfl⟩ := List.mem_map.mp hc
  rw [CapAtom.useMode_of_ne_consume (by rw [CapAtom.effMode_withMode_ro]; decide),
    CapAtom.effMode_withMode_ro, EMode.thr_ro_left]
  exact fun z _ => EMode.le_consume _

theorem Ctx.modeLe_roMap (Γ : Ctx s) (C D : CaptureSet s) : Γ.ModeLe C.ro D.ro :=
  fun m _ => Γ.setBound_ro C m

theorem Ctx.modeLe_ownLe {Γ : Ctx s} {a : CapAtom s} {W : CaptureSet s} (hO : Γ.OwnOf a W)
    (hW : Γ.AccessOnly W) : Γ.ModeLe W [a] := by
  intro m hD
  cases a with
  | cvar κ =>
      have hl : (Γ.lookupCap κ).isLeaf = true := by
        have hO' : (Γ.lookupCap κ).ownSet? = some W := hO
        cases hb : Γ.lookupCap κ <;> simp_all [CapBound.ownSet?, CapBound.isLeaf]
      rw [Ctx.setBound_singleton] at hD
      exact Ctx.SetBound.mono hW ((Γ.modeBound_leaf κ hl _).mp hD)
  | var _ => cases hO
  | name _ _ => cases hO
  | top => cases hO
  | mode _ _ => cases hO

theorem Ctx.modeEq_instC {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} (hI : Γ.InstOf a C) :
    Γ.ModeEq [a] C := by
  cases a with
  | cvar κ =>
      have hb : Γ.lookupCap κ = .inst C := by
        have hI' : (Γ.lookupCap κ).instSet? = some C := hI
        cases hb : Γ.lookupCap κ <;> simp_all [CapBound.instSet?]
      have := Γ.modeBound_inst κ C hb
      refine ⟨fun m hD => ?_, fun m hD => ?_⟩
      · rw [Ctx.setBound_singleton]; exact (this m).mpr hD
      · rw [Ctx.setBound_singleton] at hD; exact (this m).mp hD
  | var _ => cases hI
  | name _ _ => cases hI
  | top => cases hI
  | mode _ _ => cases hI

/-! ### A capture name has the bounds of its definition

`defC` says `{x∙ℓ} ≡ (Wc.get ℓ)⟦x⟧` for a transparent `x`.  The names of
`x∙ℓ` are every atom reached through the self references of the witness,
under the mode of the path, and the names of the definition are its atoms,
with every self reference read as the capture name it is.  The two agree on
every mode bound, by two facts about the search: a path can be continued
from any state it reaches (`reachPairs_comp`), and every path leaves the
start through one self reference of the start's own witness
(`reachPairs_decomp`). -/

theorem EMode.thr_comb (e x k : EMode) : (e.comb x).thr k = x.thr (e.thr k) := by
  cases e <;> cases x <;> cases k <;> rfl

theorem CapWitnesses.mem_succs {Wc : CapWitnesses (s,x)} {p q : Label × EMode} :
    q ∈ Wc.succs p ↔ ∃ a ∈ Wc.get p.1, ∃ l, a.selfLabel? = some l ∧
      q = (l, p.2.comb a.useMode) := by
  unfold CapWitnesses.succs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hq⟩
    cases hs : a.selfLabel? with
    | none => rw [hs] at hq; cases hq
    | some l =>
        rw [hs] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        exact ⟨a, ha, l, hs, hq.symm⟩
  · rintro ⟨a, ha, l, hs, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [hs, Option.map_some]

/-- The successors of a state shifted by a mode are the shifted successors. -/
theorem CapWitnesses.succs_shift {Wc : CapWitnesses (s,x)} {p q : Label × EMode} (e : EMode)
    (hq : q ∈ Wc.succs p) : (q.1, e.comb q.2) ∈ Wc.succs (p.1, e.comb p.2) := by
  obtain ⟨a, ha, l, hs, rfl⟩ := CapWitnesses.mem_succs.mp hq
  exact CapWitnesses.mem_succs.mpr ⟨a, ha, l, hs, by rw [EMode.comb_assoc]⟩

/-- A path from `ℓ` to `(l', e')` continues by any path from `l'`, under `e'`. -/
theorem CapWitnesses.reachPairs_comp {Wc : CapWitnesses (s,x)} {ℓ l' : Label} {e' : EMode}
    (h : (l', e') ∈ Wc.reachPairs ℓ) :
    ∀ n (q : Label × EMode), q ∈ Nat.repeat Wc.reachStep n [(l', .eps)] →
      (q.1, e'.comb q.2) ∈ Wc.reachPairs ℓ
  | 0, q, hq => by
      rw [List.mem_singleton.mp hq, EMode.comb_eps]
      exact h
  | n + 1, q, hq => by
      rcases CapWitnesses.mem_reachStep.mp hq with hq | ⟨p, hp, hpq⟩
      · exact CapWitnesses.reachPairs_comp h n q hq
      · exact CapWitnesses.reachPairs_closed Wc ℓ _ (CapWitnesses.reachPairs_comp h n p hp) _
          (CapWitnesses.succs_shift e' hpq)

/-- Every state but the start is reached through a self reference of the
start's witness. -/
def CapWitnesses.Decomp (Wc : CapWitnesses (s,x)) (ℓ : Label) (q : Label × EMode) : Prop :=
  q = (ℓ, .eps) ∨ ∃ c ∈ Wc.get ℓ, ∃ l, c.selfLabel? = some l ∧
    ∃ e'', (q.1, e'') ∈ Wc.reachPairs l ∧ q.2 = c.useMode.comb e''

theorem CapWitnesses.decomp_iter (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    ∀ n (q : Label × EMode), q ∈ Nat.repeat Wc.reachStep n [(ℓ, .eps)] → Wc.Decomp ℓ q
  | 0, q, hq => Or.inl (List.mem_singleton.mp hq)
  | n + 1, q, hq => by
      rcases CapWitnesses.mem_reachStep.mp hq with hq | ⟨p, hp, hpq⟩
      · exact CapWitnesses.decomp_iter Wc ℓ n q hq
      · obtain ⟨a, ha, l, hs, rfl⟩ := CapWitnesses.mem_succs.mp hpq
        rcases CapWitnesses.decomp_iter Wc ℓ n p hp with rfl | ⟨c, hc, lc, hcs, e'', hre, he⟩
        · right
          refine ⟨a, ha, l, hs, .eps, CapWitnesses.start_mem_reachPairs Wc l, ?_⟩
          show EMode.comb .eps a.useMode = a.useMode.comb .eps
          rw [EMode.comb_eps]; rfl
        · right
          refine ⟨c, hc, lc, hcs, e''.comb a.useMode, ?_, ?_⟩
          · refine CapWitnesses.reachPairs_closed Wc lc _ hre _ ?_
            exact CapWitnesses.mem_succs.mpr ⟨a, ha, l, hs, rfl⟩
          · show p.2.comb a.useMode = _
            rw [he, EMode.comb_assoc]

theorem CapWitnesses.reachPairs_decomp {Wc : CapWitnesses (s,x)} {ℓ : Label} {q : Label × EMode}
    (hq : q ∈ Wc.reachPairs ℓ) : Wc.Decomp ℓ q :=
  CapWitnesses.decomp_iter Wc ℓ _ q hq

/-- The names of an atom of a witness that is no self reference, in the
context of its binder. -/
theorem Ctx.modeCaps_transparent_nonself (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) {c : CapAtom (s,x)} (hn : c.selfLabel? = none) :
    (Γ.cons (.transparent T W Wc Fs)).modeCaps c.base =
      CaptureSet.weaken (Ctx.selfInner (fun a => Γ.modeCaps a) T c.base) := by
  unfold CapAtom.selfLabel? at hn
  generalize c.base = b at hn ⊢
  cases b with
  | var y =>
      cases y with
      | here => rfl
      | there y => rfl
  | cvar κ =>
      cases κ with
      | there κ => rfl
  | name y l =>
      cases y with
      | here => simp at hn
      | there y => rfl
  | top => rfl
  | mode _ _ => rfl

/-- The bound of a witness atom that is no self reference. -/
theorem Ctx.modeBound_transparent_nonself (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) {c : CapAtom (s,x)} (hn : c.selfLabel? = none)
    (k : EMode) :
    (Γ.cons (.transparent T W Wc Fs)).ModeBound c.base k ↔
      ∀ z ∈ Ctx.selfInner (fun a => Γ.modeCaps a) T c.base, z.effMode ≤ k := by
  unfold Ctx.ModeBound
  rw [Ctx.modeCaps_transparent_nonself Γ T W Wc Fs hn]
  exact CaptureSet.forall_weaken_effMode

/-- The bound of a state of the search: every non-self atom of its witness,
under the mode of the path. -/
def CapWitnesses.StateBound (Wc : CapWitnesses (s,x)) (N : CapAtom (s,x) → CaptureSet s)
    (l : Label) (k : EMode) : Prop :=
  ∀ c ∈ Wc.get l, c.selfLabel? = none → ∀ z ∈ N c.base, z.effMode ≤ c.useMode.thr k

/-- The path mode of a reached state never consumes: a step reads the use
mode of a self reference, a capture name (plan-5h decision 39). -/
theorem CapWitnesses.reachPairs_ne_consume (Wc : CapWitnesses (s,x)) (ℓ : Label) :
    ∀ n (p : Label × EMode), p ∈ Nat.repeat Wc.reachStep n [(ℓ, .eps)] → p.2 ≠ .consume
  | 0, p, hp => by rw [List.mem_singleton.mp hp]; intro h; cases h
  | n + 1, p, hp => by
      rcases CapWitnesses.mem_reachStep.mp hp with hp | ⟨q, hq, hqp⟩
      · exact CapWitnesses.reachPairs_ne_consume Wc ℓ n p hp
      · obtain ⟨a, -, l, hs, rfl⟩ := CapWitnesses.mem_succs.mp hqp
        show q.2.comb a.useMode ≠ .consume
        have h1 := CapWitnesses.reachPairs_ne_consume Wc ℓ n q hq
        have h2 := CapAtom.useMode_ne_consume (CapAtom.isTermB_of_selfLabel hs)
        revert h1 h2
        generalize q.2 = e1
        generalize a.useMode = e2
        cases e1 <;> cases e2 <;> decide

/-- Off `consume`, putting a mode on an atom puts it on the use mode. -/
theorem CapAtom.useMode_applyEMode {e : EMode} (he : e ≠ .consume) (c : CapAtom s) :
    (c.applyEMode e).useMode = e.comb c.useMode := by
  cases e with
  | eps => rfl
  | ro =>
      show (CapAtom.withMode .ro c).useMode = .ro
      rw [CapAtom.useMode_of_ne_consume (by rw [CapAtom.effMode_withMode_ro]; decide)]
      rfl
  | consume => exact absurd rfl he

theorem CapWitnesses.reach_bound_iff (Wc : CapWitnesses (s,x)) (N : CapAtom (s,x) → CaptureSet s)
    (ℓ : Label) (k : EMode) :
    (∀ r ∈ Wc.reach ℓ, ∀ z ∈ N r.base, z.effMode ≤ r.useMode.thr k) ↔
      ∀ p ∈ Wc.reachPairs ℓ, Wc.StateBound N p.1 (p.2.thr k) := by
  constructor
  · intro h p hp c hc hn z hz
    have := h _ (CapWitnesses.mem_reach hp hc hn) z (by rwa [CapAtom.base_applyEMode])
    rwa [CapAtom.useMode_applyEMode (Wc.reachPairs_ne_consume ℓ _ p hp), EMode.thr_comb] at this
  · intro h r hr z hz
    unfold CapWitnesses.reach at hr
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hc, hn⟩ := List.mem_filter.mp hc
    have hn' : c.selfLabel? = none := by simpa using hn
    rw [CapAtom.base_applyEMode] at hz
    rw [CapAtom.useMode_applyEMode (Wc.reachPairs_ne_consume ℓ _ p hp), EMode.thr_comb]
    exact h p hp c hc hn' z hz

/-- **A capture name of a transparent binder has the bounds of its witness.** -/
theorem Ctx.modeEq_name_here (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) (ℓ : Label) :
    (Γ.cons (.transparent T W Wc Fs)).ModeEq [CapAtom.name .here ℓ] (Wc.get ℓ) := by
  let Δ := Γ.cons (.transparent T W Wc Fs)
  let N : CapAtom (s,x) → CaptureSet s := Ctx.selfInner (fun a => Γ.modeCaps a) T
  -- the bound of a capture name, by the search
  have hname : ∀ l k, Δ.ModeBound (.name .here l) k ↔
      ∀ p ∈ Wc.reachPairs l, Wc.StateBound N p.1 (p.2.thr k) := fun l k =>
    (Γ.modeBound_cons_name_transparent T W Wc Fs l k).trans (Wc.reach_bound_iff N l k)
  -- the bound of the witness, atom by atom
  have hwit : ∀ k, Δ.SetBound (Wc.get ℓ) k ↔
      Wc.StateBound N ℓ k ∧ ∀ c ∈ Wc.get ℓ, ∀ l, c.selfLabel? = some l →
        Δ.ModeBound (.name .here l) (c.useMode.thr k) := by
    intro k
    constructor
    · intro h
      refine ⟨fun c hc hn z hz => ?_, fun c hc l hl => ?_⟩
      · exact (Γ.modeBound_transparent_nonself T W Wc Fs hn _).mp (h c hc) z hz
      · have := h c hc
        rwa [CapAtom.selfLabel?_eq_some.mp hl] at this
    · rintro ⟨h₁, h₂⟩ c hc
      cases hs : c.selfLabel? with
      | none => exact (Γ.modeBound_transparent_nonself T W Wc Fs hs _).mpr (h₁ c hc hs)
      | some l =>
          rw [CapAtom.selfLabel?_eq_some.mp hs]
          exact h₂ c hc l hs
  refine ⟨fun k hD => ?_, fun k hD => ?_⟩
  · -- from the witness to the name
    obtain ⟨h₁, h₂⟩ := (hwit k).mp hD
    rw [Ctx.setBound_singleton]
    show Δ.ModeBound (.name .here ℓ) (EMode.thr .eps k)
    rw [EMode.thr_eps_left]
    refine (hname ℓ k).mpr (fun p hp => ?_)
    rcases CapWitnesses.reachPairs_decomp hp with rfl | ⟨c, hc, l, hs, e'', hre, he⟩
    · exact h₁
    · have := (hname l _).mp (h₂ c hc l hs) (p.1, e'') hre
      rw [he, EMode.thr_comb]
      exact this
  · -- from the name to the witness
    rw [Ctx.setBound_singleton] at hD
    change Δ.ModeBound (.name .here ℓ) (EMode.thr .eps k) at hD
    rw [EMode.thr_eps_left, hname] at hD
    refine (hwit k).mpr ⟨?_, fun c hc l hs => ?_⟩
    · have := hD (ℓ, .eps) (CapWitnesses.start_mem_reachPairs Wc ℓ)
      exact this
    · refine (hname l _).mpr (fun q hq => ?_)
      have hstep : (l, c.useMode) ∈ Wc.reachPairs ℓ := by
        have := CapWitnesses.reachPairs_step (CapWitnesses.start_mem_reachPairs Wc ℓ) hc
          (CapAtom.selfLabel?_eq_some.mp hs)
        simpa [CapAtom.effMode_applyEMode, EMode.comb] using this
      have hq' := CapWitnesses.reachPairs_comp hstep _ q hq
      have := hD _ hq'
      rw [EMode.thr_comb] at this
      exact this

/-- **`defC` keeps every mode bound, in any context.** -/
theorem Ctx.modeEq_defC : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var) (ℓ : Label) (C : CaptureSet s),
    Γ.lookupDefC x ℓ = some C → Γ.ModeEq [CapAtom.name x ℓ] C
  | _, .cons Γ (.transparent T W Wc Fs), .here, ℓ, C, h => by
      have hC : C = Wc.get ℓ := by
        have h' : some (Wc.get ℓ) = some C := h
        cases h'; rfl
      subst hC
      exact Ctx.modeEq_name_here Γ T W Wc Fs ℓ
  | _, .cons Γ (.opaque _), .here, _, _, h => by cases h
  | _, .cons Γ (.formal _), .here, _, _, h => by cases h
  | _, .cons Γ b, .there y, ℓ, C, h => by
      have h' : (Γ.lookupDefC y ℓ).map CaptureSet.weaken = some C := by cases b <;> exact h
      cases hd : Γ.lookupDefC y ℓ with
      | none => rw [hd] at h'; cases h'
      | some C₀ =>
          rw [hd] at h'
          have hC : C = CaptureSet.weaken C₀ := by cases h'; rfl
          subst hC
          have ih := Ctx.modeEq_defC Γ y ℓ C₀ hd
          refine ⟨fun k hk => ?_, fun k hk => ?_⟩
          · rw [Ctx.setBound_singleton]
            show (Γ.cons b).ModeBound (CapAtom.weaken (.name y ℓ)) _
            rw [Γ.modeBound_weaken_iff b]
            have := ih.1 k ((Γ.setBound_weaken_iff b C₀ k).mp hk)
            rwa [Ctx.setBound_singleton] at this
          · rw [Ctx.setBound_singleton] at hk
            change (Γ.cons b).ModeBound (CapAtom.weaken (.name y ℓ)) _ at hk
            rw [Γ.modeBound_weaken_iff b] at hk
            refine (Γ.setBound_weaken_iff b C₀ k).mpr (ih.2 k ?_)
            rw [Ctx.setBound_singleton]; exact hk
  | _, .consC Γ b, .there y, ℓ, C, h => by
      have h' : (Γ.lookupDefC y ℓ).map CaptureSet.weaken = some C := h
      cases hd : Γ.lookupDefC y ℓ with
      | none => rw [hd] at h'; cases h'
      | some C₀ =>
          rw [hd] at h'
          have hC : C = CaptureSet.weaken C₀ := by cases h'; rfl
          subst hC
          have ih := Ctx.modeEq_defC Γ y ℓ C₀ hd
          refine ⟨fun k hk => ?_, fun k hk => ?_⟩
          · rw [Ctx.setBound_singleton]
            show (Γ.consC b).ModeBound (CapAtom.weaken (.name y ℓ)) _
            rw [Γ.modeBound_weakenC_iff b]
            have := ih.1 k ((Γ.setBound_weakenC_iff b C₀ k).mp hk)
            rwa [Ctx.setBound_singleton] at this
          · rw [Ctx.setBound_singleton] at hk
            change (Γ.consC b).ModeBound (CapAtom.weaken (.name y ℓ)) _ at hk
            rw [Γ.modeBound_weakenC_iff b] at hk
            refine (Γ.setBound_weakenC_iff b C₀ k).mpr (ih.2 k ?_)
            rw [Ctx.setBound_singleton]; exact hk

end FCdot

end Separation
