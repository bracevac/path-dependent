import Coercions.Separation.FCdot.TypingRename

namespace Separation

/-!
# Transparency is a refinement

`Ctx.Refines Γ Γ'` says that `Γ'` has the same variable types as `Γ` and at
least as many block definitions and field labels.  Every typing family is
monotone in this order; in particular a term typed with an opaque binder is
typed with the corresponding transparent binder, which is what allocation
needs.
-/

namespace FCdot

/-- Renaming a binding by the identity. -/
theorem Binding.rename_id' (b : Binding s) : b.rename Rename.id = b := by
  cases b <;> simp [Binding.rename, Rename.lift_id]

theorem CapBound.rename_id' (b : CapBound s) : b.rename Rename.id = b := by
  cases b <;> simp [CapBound.rename]

/-- A map of mode bounds that is the identity on atoms, read as a renaming. -/
theorem Ctx.ModeMap.idRename {Γ Γ' : Ctx s} (h : Γ.ModeMap (fun a => a) Γ') :
    Γ.ModeMap (·.rename Rename.id) Γ' := fun a m ha => by
  show Γ'.ModeBound (a.rename Rename.id) m
  rw [CapAtom.rename_id]
  exact h a m ha

/-- Passing under a term binder, at the identity. -/
theorem Ctx.ModeMap.idLift {Γ Γ' : Ctx s} (h : Γ.ModeMap (fun a => a) Γ') (b : Binding s) :
    (Γ.cons b).ModeMap (fun a => a) (Γ'.cons b) := by
  have h' := h.idRename.renameLift b
  rw [Rename.lift_id, Binding.rename_id'] at h'
  intro a m ha
  have := h' a m ha
  simpa using this

/-- Passing under a capture binder, at the identity. -/
theorem Ctx.ModeMap.idLiftC {Γ Γ' : Ctx s} (h : Γ.ModeMap (fun a => a) Γ') (b : CapBound s) :
    (Γ.consC b).ModeMap (fun a => a) (Γ'.consC b) := by
  have h' := h.idRename.renameLiftC b
  rw [Rename.lift_id, CapBound.rename_id'] at h'
  intro a m ha
  have := h' a m ha
  simpa using this

/-! ## Flavours, bits and names under a refinement

A refinement is the identity on atoms, so the kill fields read at the same
binder on both sides. -/

theorem Ctx.KillMap.idOf {Γ Γ' : Ctx s}
    (hcons : ∀ κ, (Γ.lookupCap κ).consumable = true → (Γ'.lookupCap κ).consumable = true)
    (hlive : ∀ κ, (Γ.lookupCap κ).consumable = true → Γ.BitLive κ → Γ'.BitLive κ)
    (hown : ∀ h κ, Γ.ownsB h κ = true → Γ'.ownsB h κ = true) :
    Γ.KillMap (fun a => a) Γ' :=
  (Ctx.KillMap.ofRename (ρ := Rename.id) (fun _ _ _ he => he) hcons hlive hown).congr
    (fun a => (CapAtom.rename_id a).symm)

namespace Ctx.KillMap

variable {Γ Γ' : Ctx s}

theorem id_cons (h : Γ.KillMap (fun a => a) Γ') {κ : BVar s .cap}
    (hc : (Γ.lookupCap κ).consumable = true) : (Γ'.lookupCap κ).consumable = true :=
  h.cons κ κ hc rfl

theorem id_live (h : Γ.KillMap (fun a => a) Γ') {κ : BVar s .cap}
    (hc : (Γ.lookupCap κ).consumable = true) (hl : Γ.BitLive κ) : Γ'.BitLive κ :=
  h.live κ κ hc rfl hl

theorem id_owns (h : Γ.KillMap (fun a => a) Γ') {h₀ κ : BVar s .cap}
    (ho : Γ.ownsB h₀ κ = true) : Γ'.ownsB h₀ κ = true :=
  h.owns h₀ κ h₀ κ rfl rfl ho

theorem idRefl (Γ : Ctx s) : Γ.KillMap (fun a => a) Γ :=
  Ctx.KillMap.idOf (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h)

theorem idTrans {Γ₁ Γ₂ Γ₃ : Ctx s} (h₁ : Γ₁.KillMap (fun a => a) Γ₂)
    (h₂ : Γ₂.KillMap (fun a => a) Γ₃) : Γ₁.KillMap (fun a => a) Γ₃ :=
  Ctx.KillMap.idOf (fun _ hc => h₂.id_cons (h₁.id_cons hc))
    (fun _ hc hl => h₂.id_live (h₁.id_cons hc) (h₁.id_live hc hl))
    (fun _ _ ho => h₂.id_owns (h₁.id_owns ho))

theorem idCons (h : Γ.KillMap (fun a => a) Γ') (b : Binding s) :
    (Γ.cons b).KillMap (fun a => a) (Γ'.cons b) := by
  refine Ctx.KillMap.idOf ?_ ?_ ?_
  · intro κ hc
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc ⊢
        exact h.id_cons hc
  · intro κ hc hl
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc
        rw [Ctx.bitLive_there] at hl ⊢
        exact h.id_live hc hl
  · intro h₀ κ ho
    obtain ⟨h₁, κ₁, rfl, rfl, ho₁⟩ := Ctx.ownsB_cons_cases ho
    rw [Ctx.ownsB_cons_there]; exact h.id_owns ho₁

theorem idConsC (h : Γ.KillMap (fun a => a) Γ') (b : CapBound s) :
    (Γ.consC b).KillMap (fun a => a) (Γ'.consC b) := by
  refine Ctx.KillMap.idOf ?_ ?_ ?_
  · intro κ hc
    cases κ with
    | here => exact hc
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc ⊢
        exact h.id_cons hc
  · intro κ hc hl
    cases κ with
    | here => exact hl
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
        rw [Ctx.bitLive_thereC] at hl ⊢
        exact h.id_live hc hl
  · intro h₀ κ ho
    rcases Ctx.ownsB_consC_cases ho with ⟨rfl, κ₁, rfl, hb⟩ | ⟨h₁, κ₁, rfl, rfl, ho₁⟩
    · rw [Ctx.ownsB_consC_here_there]; exact hb
    · rw [Ctx.ownsB_consC_there]; exact h.id_owns ho₁

/-- Through two locations whose claims differ: a location owns nothing. -/
theorem idConsCLoc (h : Γ.KillMap (fun a => a) Γ') (k : Bool) (Cl Cl' : CaptureSet s) :
    (Γ.consC (.loc k Cl)).KillMap (fun a => a) (Γ'.consC (.loc k Cl')) := by
  refine Ctx.KillMap.idOf ?_ ?_ ?_
  · intro κ hc
    cases κ with
    | here => rfl
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc ⊢
        exact h.id_cons hc
  · intro κ hc hl
    cases κ with
    | here => exact hl
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
        rw [Ctx.bitLive_thereC] at hl ⊢
        exact h.id_live hc hl
  · intro h₀ κ ho
    rcases Ctx.ownsB_consC_cases ho with ⟨rfl, κ₁, rfl, hb⟩ | ⟨h₁, κ₁, rfl, rfl, ho₁⟩
    · cases hb
    · rw [Ctx.ownsB_consC_there]; exact h.id_owns ho₁

end Ctx.KillMap

namespace Ctx.NamesMap

variable {Γ Γ' : Ctx s}

theorem idLift (h : Γ.NamesMap (fun a => a) Γ') (b : Binding s) :
    (Γ.cons b).NamesMap (fun a => a) (Γ'.cons b) := by
  have h' := (h.congr (fun a => CapAtom.rename_id a)).renameLift b
  rw [Rename.lift_id, Binding.rename_id'] at h'
  exact h'.congr (fun a => (CapAtom.rename_id a).symm)

theorem idLiftC (h : Γ.NamesMap (fun a => a) Γ') (b : CapBound s) :
    (Γ.consC b).NamesMap (fun a => a) (Γ'.consC b) := by
  have h' := (h.congr (fun a => CapAtom.rename_id a)).renameLiftC b
    (Or.inr (fun κ' => ⟨κ', rfl⟩))
  rw [Rename.lift_id, CapBound.rename_id'] at h'
  exact h'.congr (fun a => (CapAtom.rename_id a).symm)

theorem idLiftCLoc (h : Γ.NamesMap (fun a => a) Γ') {k : Bool} {Cl Cl' : CaptureSet s}
    (hcl : ∀ κ, CapAtom.cvar κ ∈ Cl' → CapAtom.cvar κ ∈ Cl) :
    (Γ.consC (.loc k Cl)).NamesMap (fun a => a) (Γ'.consC (.loc k Cl')) := by
  have h' := (h.congr (fun a => CapAtom.rename_id a)).renameLiftCLoc (k := k) (Cl := Cl)
    (Cl' := Cl') (fun κ'' hκ'' => ⟨κ'', rfl, hcl κ'' hκ''⟩)
  rw [Rename.lift_id] at h'
  exact h'.congr (fun a => (CapAtom.rename_id a).symm)

end Ctx.NamesMap

/-- `Γ'` knows everything `Γ` knows, with the same types. -/
structure Ctx.Refines {s : Sig} (Γ Γ' : Ctx s) : Prop where
  ty : ∀ x, Γ'.lookupTy x = Γ.lookupTy x
  def_ : ∀ x l (W : Shape s), Γ.lookupDef x l = some W → Γ'.lookupDef x l = some W
  defC : ∀ x l (C : CaptureSet s), Γ.lookupDefC x l = some C → Γ'.lookupDefC x l = some C
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields x = some Fs
  /-- Refinement adds block definitions and field labels to term binders and
      never touches the capture spine, so the innermost root is the same. -/
  rootEq : Γ'.root? = Γ.root?
  /-- And so is the level of every binder. -/
  lvlEq : ∀ {k : Kind} (y : BVar s k), Γ'.lvl y = Γ.lvl y
  /-- And so is the answer to whether a capture binder is a root. -/
  capEq : ∀ κ : BVar s .cap, (Γ'.lookupCap κ).isRoot = (Γ.lookupCap κ).isRoot
  /-- And so is the set an instance binder was opened at.  It is the fourth
      capture field, the one `CapEq.HasType.instC` reads. -/
  capInstEq : ∀ κ : BVar s .cap, (Γ'.lookupCap κ).instSet? = (Γ.lookupCap κ).instSet?
  /-- And so is the set an heir owns, which `CapCo.HasType.ownLe` reads. -/
  capOwnEq : ∀ κ : BVar s .cap, (Γ'.lookupCap κ).ownSet? = (Γ.lookupCap κ).ownSet?
  /-- And a capture binder that is a location claiming nothing stays one,
      which `Value.HasType.cell` reads, whatever the bit. -/
  capLoc : ∀ (κ : BVar s .cap) (k : Bool), (Γ.lookupCap κ).locBit? = some k →
      ∃ k', (Γ'.lookupCap κ).locBit? = some k'
  /-- The names of every atom keep their mode bounds, which the level rule's
      premise reads. -/
  modeBound : Γ.ModeMap (fun a => a) Γ'
  /-- The flavour, the bit and the owners of a consumable binder survive
      (plan-5h S0.8): what `ELeCo.packF` reads. -/
  kill : Γ.KillMap (fun a => a) Γ'

namespace Ctx.Refines

theorem refl {Γ : Ctx s} : Ctx.Refines Γ Γ where
  ty := fun _ => rfl
  def_ := fun _ _ _ h => h
  defC := fun _ _ _ h => h
  fields := fun _ _ h => h
  rootEq := rfl
  lvlEq := fun _ => rfl
  capEq := fun _ => rfl
  capInstEq := fun _ => rfl
  capOwnEq := fun _ => rfl
  capLoc := fun _ k h => ⟨k, h⟩
  modeBound := Ctx.ModeMap.id Γ
  kill := Ctx.KillMap.idRefl Γ

theorem trans {Γ1 Γ2 Γ3 : Ctx s} (h1 : Ctx.Refines Γ1 Γ2) (h2 : Ctx.Refines Γ2 Γ3) :
    Ctx.Refines Γ1 Γ3 where
  ty := fun x => (h2.ty x).trans (h1.ty x)
  def_ := fun x l W h => h2.def_ x l W (h1.def_ x l W h)
  defC := fun x l C h => h2.defC x l C (h1.defC x l C h)
  fields := fun x Fs h => h2.fields x Fs (h1.fields x Fs h)
  rootEq := h2.rootEq.trans h1.rootEq
  lvlEq := fun y => (h2.lvlEq y).trans (h1.lvlEq y)
  capEq := fun κ => (h2.capEq κ).trans (h1.capEq κ)
  capInstEq := fun κ => (h2.capInstEq κ).trans (h1.capInstEq κ)
  capOwnEq := fun κ => (h2.capOwnEq κ).trans (h1.capOwnEq κ)
  capLoc := fun κ k h => by
    obtain ⟨k₁, h₁⟩ := h1.capLoc κ k h
    exact h2.capLoc κ k₁ h₁
  modeBound := h1.modeBound.comp h2.modeBound
  kill := h1.kill.idTrans h2.kill

theorem cons {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (b : Binding s) :
    Ctx.Refines (Γ.cons b) (Γ'.cons b) where
  ty := by
    intro x
    cases x with
    | here => rfl
    | there y => simp [h.ty y]
  def_ := by
    intro x l W hW
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | formal T => simp at hW
        | transparent T W' Wc' Fs => exact hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  defC := by
    intro x l C hC
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hC
        | formal T => simp at hC
        | transparent T W' Wc' Fs => exact hC
    | there y =>
        rw [Ctx.lookupDefC_there] at hC ⊢
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | formal T => simp at hFs
        | transparent T W' Wc' Fs' => exact hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs ⊢
        exact h.fields y Fs hFs
  rootEq := by
    rw [Ctx.root?_cons, Ctx.root?_cons, h.rootEq]
  lvlEq := by
    intro k y
    cases y with
    | here => simp [h.rootEq]
    | there y0 => simp [h.lvlEq]
  capEq := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑).isRoot = ((Γ.lookupCap κ0)↑).isRoot
        simp [h.capEq]
  capInstEq := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,x)).instSet? = ((Γ.lookupCap κ0)↑).instSet?
        rw [CapBound.instSet?_weaken, CapBound.instSet?_weaken, h.capInstEq]
  capOwnEq := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,x)).ownSet? = ((Γ.lookupCap κ0)↑).ownSet?
        rw [CapBound.ownSet?_weaken, CapBound.ownSet?_weaken, h.capOwnEq]
  capLoc := by
    intro κ k hk
    cases κ with
    | there κ0 =>
        show ∃ k', ((Γ'.lookupCap κ0)↑ : CapBound (s,x)).locBit? = some k'
        rw [CapBound.locBit?_weaken]
        have hk' : ((Γ.lookupCap κ0)↑ : CapBound (s,x)).locBit? = some k := hk
        rw [CapBound.locBit?_weaken] at hk'
        exact h.capLoc κ0 k hk'
  modeBound := h.modeBound.idLift b
  kill := h.kill.idCons b

/-- Weakening an opaque binder to the transparent binder of the same type.
The capture names of the opaque binder stand for its level root at the plain
mode, so the witnesses must consume nothing through their names
(`hWc`).  On a base program no atom carries a mode, and `hWc` holds. -/
theorem transparent {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)}
    {Fs : List Label}
    (hWc : ∀ ℓ, (Γ.cons (.transparent T W Wc Fs)).AccessOnly [.name .here ℓ]) :
    Ctx.Refines (Γ.cons (.opaque T)) (Γ.cons (.transparent T W Wc Fs)) where
  ty := by
    intro x
    cases x with
    | here => rfl
    | there y => rfl
  def_ := by
    intro x l W' hW
    cases x with
    | here => simp at hW
    | there y => rw [Ctx.lookupDef_there] at hW ⊢; exact hW
  defC := by
    intro x l C' hC
    cases x with
    | here => simp at hC
    | there y => rw [Ctx.lookupDefC_there] at hC ⊢; exact hC
  fields := by
    intro x Fs' hFs
    cases x with
    | here => simp at hFs
    | there y => rw [Ctx.lookupFields_there] at hFs ⊢; exact hFs
  rootEq := rfl
  lvlEq := by
    intro k y
    cases y with
    | here => rfl
    | there y0 => rfl
  capEq := by
    intro κ
    cases κ with
    | there κ0 => rfl
  capInstEq := by
    intro κ
    cases κ with
    | there κ0 => rfl
  capOwnEq := by
    intro κ
    cases κ with
    | there κ0 => rfl
  capLoc := by
    intro κ k hk
    cases κ with
    | there κ0 => exact ⟨k, hk⟩
  kill := by
    refine Ctx.KillMap.idOf ?_ ?_ ?_
    · intro κ hc; cases κ with | there κ0 => exact hc
    · intro κ _ hl; cases κ with | there κ0 => exact hl
    · intro h₀ κ ho
      obtain ⟨h₁, κ₁, rfl, rfl, ho₁⟩ := Ctx.ownsB_cons_cases ho
      rw [Ctx.ownsB_cons_there]; exact ho₁
  modeBound := by
    intro a m ha
    cases a with
    | var y =>
        cases y with
        | here =>
            show (Γ.cons (.transparent T W Wc Fs)).ModeBound (.var .here) m
            rw [Ctx.modeBound_cons_here _ rfl] at ha ⊢
            exact ha
        | there y₀ =>
            exact (Γ.modeBound_weaken_iff _ (.var y₀) m).mpr
              ((Γ.modeBound_weaken_iff _ (.var y₀) m).mp ha)
    | cvar κ =>
        cases κ with
        | there κ₀ =>
            exact (Γ.modeBound_weaken_iff _ (.cvar κ₀) m).mpr
              ((Γ.modeBound_weaken_iff _ (.cvar κ₀) m).mp ha)
    | name y l =>
        cases y with
        | here =>
            rw [Ctx.modeBound_cons_name_opaque] at ha
            have := Ctx.accessOnly_singleton.mp (hWc l)
            exact this.mono ha
        | there y₀ =>
            exact (Γ.modeBound_weaken_iff _ (.name y₀ l) m).mpr
              ((Γ.modeBound_weaken_iff _ (.name y₀ l) m).mp ha)
    | top => exact (Ctx.modeBound_top _ m).mpr ((Ctx.modeBound_top _ m).mp ha)
    | mode md a => exact Ctx.modeBound_mode _ md a m

/-- A refinement keeps the premise `AccessOnly`. -/
theorem accessOnly {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {C : CaptureSet s}
    (hC : Γ.AccessOnly C) : Γ'.AccessOnly C :=
  fun c hc => h.modeBound _ _ (hC c hc)

theorem transparentOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {x : BVar s .var}
    (ht : Γ.IsTransparent x) : Γ'.IsTransparent x := by
  obtain ⟨Fs, hFs⟩ := Ctx.isTransparent_iff.mp ht
  exact Ctx.IsTransparent.of_lookup (h.fields x Fs hFs)

theorem consC {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (b : CapBound s) :
    Ctx.Refines (Γ.consC b) (Γ'.consC b) where
  ty := by
    intro x
    cases x with
    | there y => simp [h.ty y]
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC ⊢
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs ⊢
        exact h.fields y Fs hFs
  rootEq := by
    cases b with
    | root => rfl
    | star | upper C | inst C | loc _ C | own _ C | param _ =>
        rw [Ctx.root?_consC_of_not_root _ _ rfl, Ctx.root?_consC_of_not_root _ _ rfl, h.rootEq]
  lvlEq := by
    intro k y
    cases y with
    | here =>
        cases b with
        | root => rfl
        | star | upper C | inst C | loc _ C | own _ C | param _ =>
            rw [Ctx.lvl_consC_here_of_not_root _ _ rfl, Ctx.lvl_consC_here_of_not_root _ _ rfl,
              h.rootEq]
    | there y0 => simp [h.lvlEq]
  capEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑).isRoot = ((Γ.lookupCap κ0)↑).isRoot
        simp [h.capEq]
  capInstEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).instSet? = ((Γ.lookupCap κ0)↑).instSet?
        rw [CapBound.instSet?_weaken, CapBound.instSet?_weaken, h.capInstEq]
  capOwnEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).ownSet? = ((Γ.lookupCap κ0)↑).ownSet?
        rw [CapBound.ownSet?_weaken, CapBound.ownSet?_weaken, h.capOwnEq]
  capLoc := by
    intro κ k hk
    cases κ with
    | here => exact ⟨k, hk⟩
    | there κ0 =>
        show ∃ k', ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).locBit? = some k'
        rw [CapBound.locBit?_weaken]
        have hk' : ((Γ.lookupCap κ0)↑ : CapBound (s,c)).locBit? = some k := hk
        rw [CapBound.locBit?_weaken] at hk'
        exact h.capLoc κ0 k hk'
  modeBound := h.modeBound.idLiftC b
  kill := h.kill.idConsC b

/-! ### The scope contexts

A scope, a lambda body and an object body are built from the two `cons`
lemmas above, so refinement passes under all three. -/

theorem scope {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') : Ctx.Refines Γ.scope Γ'.scope :=
  (h.consC .root).consC .star

theorem scopeInst {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (C : CaptureSet s) :
    Ctx.Refines (Γ.scopeInst C) (Γ'.scopeInst C) :=
  (h.consC .root).consC (.inst C↑)

theorem body {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (T : Dom s) :
    Ctx.Refines (Γ.body T) (Γ'.body T) :=
  (h.scope).cons _

theorem objBody {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (ls : List Label) :
    Ctx.Refines (Γ.objBody T W Wc ls) (Γ'.objBody T W Wc ls) :=
  (h.consC .root).cons _


/-! ### Kills under a refinement

The kill a head causes on the refined side is part of the kill it causes on
the source side, because names only shrink under a refinement that keeps
them (`Ctx.NamesMap`).  So the two killed contexts are a refinement again,
with the target more live. -/

/-- Between killed contexts: the target kills a part of what the source
kills. -/
theorem killNames {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {D D' : List (BVar s .cap)}
    (hD : ∀ κ ∈ D', κ ∈ D) : Ctx.Refines (Γ.killNames D) (Γ'.killNames D') where
  ty x := by rw [Ctx.lookupTy_killNames, Ctx.lookupTy_killNames]; exact h.ty x
  def_ x l W hd := by rw [Ctx.lookupDef_killNames] at hd ⊢; exact h.def_ x l W hd
  defC x l C hd := by rw [Ctx.lookupDefC_killNames] at hd ⊢; exact h.defC x l C hd
  fields x Fs hf := by rw [Ctx.lookupFields_killNames] at hf ⊢; exact h.fields x Fs hf
  rootEq := by rw [Ctx.root?_killNames, Ctx.root?_killNames]; exact h.rootEq
  lvlEq y := by rw [Ctx.lvl_killNames, Ctx.lvl_killNames]; exact h.lvlEq y
  capEq κ := by
    rw [Ctx.lookupCap_killNames_isRoot, Ctx.lookupCap_killNames_isRoot]; exact h.capEq κ
  capInstEq κ := by
    rw [Ctx.lookupCap_killNames_instSet?, Ctx.lookupCap_killNames_instSet?]; exact h.capInstEq κ
  capOwnEq κ := by
    rw [Ctx.lookupCap_killNames_ownSet?, Ctx.lookupCap_killNames_ownSet?]; exact h.capOwnEq κ
  capLoc κ k hk := by
    have hs : ((Γ.killNames D).locBit? (.cvar κ)).isSome = true := by
      show ((Γ.killNames D).lookupCap κ).locBit?.isSome = true
      rw [hk]; rfl
    rw [Ctx.locBit?_killNames_isSome] at hs
    obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨k₁, hk₁⟩ := h.capLoc κ k₀ hk₀
    have hs' : ((Γ'.killNames D').locBit? (.cvar κ)).isSome = true := by
      rw [Ctx.locBit?_killNames_isSome]
      show (Γ'.lookupCap κ).locBit?.isSome = true
      rw [hk₁]; rfl
    exact Option.isSome_iff_exists.mp hs'
  modeBound := h.modeBound.killNames D D'
  kill := h.kill.killNames (fun κ₁ κ₂ κ' h₁ h₂ => by cases h₁; cases h₂; rfl)
    (fun κ' hκ' => ⟨κ', hD κ' hκ', rfl⟩)

theorem killFor {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ')
    {C : CaptureSet s} (hk : Γ.KillOk C) : Ctx.Refines (Γ.killFor C) (Γ'.killFor C) := by
  have hC : C.map (fun a => a) = C := List.map_id C
  refine h.killNames ?_
  intro κ hκ
  have := hN.killSet CapAtom.nameMapFn_id hk κ (by rw [hC]; exact hκ)
  obtain ⟨κ₀, h₀, he⟩ := this
  cases he
  exact h₀

/-- Two locations whose claims differ, with the target claiming nothing
when the source claims nothing. -/
theorem consCLoc {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (k : Bool) {Cl Cl' : CaptureSet s}
    (hCl : Cl = [] → Cl' = []) :
    Ctx.Refines (Γ.consC (.loc k Cl)) (Γ'.consC (.loc k Cl')) where
  ty := by
    intro x
    cases x with
    | there y => simp [h.ty y]
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC ⊢
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs ⊢
        exact h.fields y Fs hFs
  rootEq := by
    rw [Ctx.root?_consC_of_not_root _ _ rfl, Ctx.root?_consC_of_not_root _ _ rfl, h.rootEq]
  lvlEq := by
    intro k' y
    cases y with
    | here =>
        rw [Ctx.lvl_consC_here_of_not_root _ _ rfl, Ctx.lvl_consC_here_of_not_root _ _ rfl,
          h.rootEq]
    | there y0 => simp [h.lvlEq]
  capEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑).isRoot = ((Γ.lookupCap κ0)↑).isRoot
        simp [h.capEq]
  capInstEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).instSet? = ((Γ.lookupCap κ0)↑).instSet?
        rw [CapBound.instSet?_weaken, CapBound.instSet?_weaken, h.capInstEq]
  capOwnEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).ownSet? = ((Γ.lookupCap κ0)↑).ownSet?
        rw [CapBound.ownSet?_weaken, CapBound.ownSet?_weaken, h.capOwnEq]
  capLoc := by
    intro κ k₀ hk
    cases κ with
    | here =>
        have hk' : (CapBound.weaken (k := .cap) (CapBound.loc k Cl)).locBit? = some k₀ := hk
        rw [CapBound.locBit?_weaken] at hk'
        have hCl0 : Cl = [] := by
          cases Cl with
          | nil => rfl
          | cons _ _ => simp [CapBound.locBit?] at hk'
        refine ⟨k, ?_⟩
        show (CapBound.weaken (k := .cap) (CapBound.loc k Cl')).locBit? = some k
        rw [CapBound.locBit?_weaken, hCl hCl0]; rfl
    | there κ0 =>
        show ∃ k', ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).locBit? = some k'
        rw [CapBound.locBit?_weaken]
        have hk' : ((Γ.lookupCap κ0)↑ : CapBound (s,c)).locBit? = some k₀ := hk
        rw [CapBound.locBit?_weaken] at hk'
        exact h.capLoc κ0 k₀ hk'
  modeBound := by
    have h0 := h.modeBound.idLiftC (.loc k Cl)
    have hmc : (Γ'.consC (CapBound.loc k Cl)).modeCaps =
        (Γ'.consC (CapBound.loc k Cl')).modeCaps := by
      funext a
      rcases CapAtom.consC_cases a with rfl | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
      · rfl
      · simp only [Ctx.modeCaps, Ctx.namesCapsP_weakenC]
      · simp only [Ctx.modeCaps, Ctx.namesCapsP_mode]
    intro a m ha
    have := h0 a m ha
    unfold Ctx.ModeBound at this ⊢
    rw [← hmc]; exact this
  kill := h.kill.idConsCLoc k Cl Cl'

theorem claimsFor_cover {Γ Γ' : Ctx s} (hN : Γ.NamesMap (fun a => a) Γ') {C : CaptureSet s}
    (hk : Γ.KillOk C) :
    ∀ κ, CapAtom.cvar κ ∈ Γ'.claimsFor C → CapAtom.cvar κ ∈ Γ.claimsFor C := by
  intro κ hκ
  have hC : C.map (fun a => a) = C := List.map_id C
  unfold Ctx.claimsFor at hκ ⊢
  obtain ⟨κ₁, h₁, he⟩ := List.mem_map.mp hκ
  have he' := CapAtom.cvar.inj he
  subst he'
  obtain ⟨κ₀, h₀, hf⟩ := hN.killSet CapAtom.nameMapFn_id hk κ₁ (by rw [hC]; exact h₁)
  cases hf
  exact List.mem_map_of_mem h₀

/-- **The body context of `letexF` under a refinement.** -/
theorem freshCtx {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ')
    {C : CaptureSet s} (hk : Γ.KillOk C) (T : Ty (s,c)) :
    Ctx.Refines (Γ.freshCtx C T) (Γ'.freshCtx C T) := by
  unfold Ctx.freshCtx
  refine ((h.killFor hN hk).consCLoc true ?_).cons _
  intro h0
  cases h' : Γ'.claimsFor C with
  | nil => rfl
  | cons a L =>
      have ha : a ∈ Γ'.claimsFor C := by rw [h']; exact List.mem_cons_self ..
      have ha' := ha
      unfold Ctx.claimsFor at ha'
      obtain ⟨κ₁, -, rfl⟩ := List.mem_map.mp ha'
      have := claimsFor_cover hN hk κ₁ ha
      rw [h0] at this
      cases this

end Ctx.Refines

namespace Ctx.NamesMap

variable {Γ Γ' : Ctx s}

theorem idScope (h : Γ.NamesMap (fun a => a) Γ') : Γ.scope.NamesMap (fun a => a) Γ'.scope :=
  (h.idLiftC .root).idLiftC .star

theorem idScopeInst (h : Γ.NamesMap (fun a => a) Γ') (C : CaptureSet s) :
    (Γ.scopeInst C).NamesMap (fun a => a) (Γ'.scopeInst C) :=
  (h.idLiftC .root).idLiftC _

theorem idBody (h : Γ.NamesMap (fun a => a) Γ') (T : Dom s) :
    (Γ.body T).NamesMap (fun a => a) (Γ'.body T) :=
  h.idScope.idLift _

theorem idObjBody (h : Γ.NamesMap (fun a => a) Γ') (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (ls : List Label) :
    (Γ.objBody T W Wc ls).NamesMap (fun a => a) (Γ'.objBody T W Wc ls) :=
  (h.idLiftC .root).idLift _

/-- The kills a head causes on both sides, at the identity. -/
theorem idKillFor (h : Γ.NamesMap (fun a => a) Γ') {C : CaptureSet s} (hk : Γ.KillOk C) :
    (Γ.killFor C).NamesMap (fun a => a) (Γ'.killFor C) := by
  have := h.killFor CapAtom.nameMapFn_id hk
  rwa [show C.map (fun a => a) = C from List.map_id C] at this

/-- The kill premise at the identity. -/
theorem idKillOk (h : Γ.NamesMap (fun a => a) Γ') (hkm : Γ.KillMap (fun a => a) Γ')
    {C : CaptureSet s} (hk : Γ.KillOk C) : Γ'.KillOk C := by
  have := h.killOk hkm CapAtom.nameMapFn_id hk
  rwa [show C.map (fun a => a) = C from List.map_id C] at this

theorem idFreshCtx (h : Γ.NamesMap (fun a => a) Γ') {C : CaptureSet s} (hk : Γ.KillOk C)
    (T : Ty (s,c)) :
    (Γ.freshCtx C T).NamesMap (fun a => a) (Γ'.freshCtx C T) := by
  unfold Ctx.freshCtx
  exact ((h.idKillFor hk).idLiftCLoc (Ctx.Refines.claimsFor_cover h hk)).idLift _

end Ctx.NamesMap

/-! ## Levels under a refinement

The three new fields say that a refinement leaves the capture spine alone,
so every level fact reads the same on both sides.  That is what the `level`
rule needs, and it is why the monotonicity theorems keep their meaning. -/

theorem Ctx.Refines.lvlAtom {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (a : CapAtom s) :
    Γ'.lvlAtom a = Γ.lvlAtom a := by
  induction a <;> simp_all [Ctx.lvlAtom, h.lvlEq]

theorem Ctx.Refines.isRootB {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (a : CapAtom s) :
    Γ'.isRootB a = Γ.isRootB a := by
  cases a <;> simp [Ctx.isRootB, h.capEq]

theorem Ctx.Refines.isRoot {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {r : CapAtom s}
    (hr : Γ.IsRoot r) : Γ'.IsRoot r := by
  unfold Ctx.IsRoot
  rw [h.isRootB]
  exact hr

theorem Ctx.Refines.instOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {a : CapAtom s}
    {C : CaptureSet s} (hI : Γ.InstOf a C) : Γ'.InstOf a C := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | mode m a => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | cvar κ =>
      show (Γ'.lookupCap κ).instSet? = some C
      rw [h.capInstEq]
      exact hI

theorem Ctx.Refines.ownOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {a : CapAtom s}
    {W : CaptureSet s} (hO : Γ.OwnOf a W) : Γ'.OwnOf a W := by
  cases a with
  | top => simp [Ctx.OwnOf, Ctx.ownSet?] at hO
  | var x => simp [Ctx.OwnOf, Ctx.ownSet?] at hO
  | name x l => simp [Ctx.OwnOf, Ctx.ownSet?] at hO
  | mode m a => simp [Ctx.OwnOf, Ctx.ownSet?] at hO
  | cvar κ =>
      show (Γ'.lookupCap κ).ownSet? = some W
      rw [h.capOwnEq]
      exact hO

/-- A location that claims nothing stays one under refinement. -/
theorem Ctx.Refines.locOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {a : CapAtom s}
    {k : Bool} (hL : Γ.LocOf a k) : ∃ k', Γ'.LocOf a k' := by
  cases a with
  | top => simp [Ctx.LocOf, Ctx.locBit?] at hL
  | var x => simp [Ctx.LocOf, Ctx.locBit?] at hL
  | name x l => simp [Ctx.LocOf, Ctx.locBit?] at hL
  | mode m a => simp [Ctx.LocOf, Ctx.locBit?] at hL
  | cvar κ => exact h.capLoc κ k hL

theorem Ctx.Refines.lvlLe {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {e r : CapAtom s}
    (hl : Γ.LvlLe e r) : Γ'.LvlLe e r := by
  unfold Ctx.LvlLe Ctx.lvlLeB
  rw [h.lvlAtom]
  exact hl

/-! ## Monotonicity of the typing families -/

mutual

/-- The capture family reads a context only at `defC` and through atoms, and
both survive a refinement. -/
theorem CapCo.HasType.refine {Γ Γ' : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) : Γ' ⊢ᶜ f : C ⊑ D := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.refine hR) (hg.refine hR)
  | .elem hs => exact .elem hs
  | .union hf hg => exact .union (hf.refine hR) (hg.refine hR)
  | .capvar ha => exact .capvar (ha.refine hR)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .eqToLe hφ => exact .eqToLe (hφ.refine hR)
  | .level h₁ h₂ h₃ =>
      exact .level (hR.isRoot h₁) (hR.lvlLe h₂)
        (hR.modeBound.accessOnly (fun _ => rfl) (fun _ => EMode.le_refl _) h₃)
  | .modeLe hm => exact .modeLe hm
  | .roMap hf => exact .roMap (hf.refine hR)
  | .ownLe hO hW => exact .ownLe (hR.ownOf hO) (hR.accessOnly hW)

theorem CapEq.HasType.refine {Γ Γ' : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) : Γ' ⊢ᶜ φ : C ≡ D := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .defC hd => exact .defC (hR.defC _ _ _ hd)
  | .instC hI => exact .instC (hR.instOf hI)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem CapStep.HasType.refine {Γ Γ' : Ctx s} {st : CapStep s} {X Y : CaptureSet (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : CapStep.HasType Γ st X Y) : CapStep.HasType Γ' st X Y := by
  match h with
  | .closed hf => exact .closed (hf.refine hR)
  | .incl hs => exact .incl hs

theorem SideC.HasType.refine {Γ Γ' : Ctx s} {q : SideC s} {X Y : CaptureSet (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : SideC.HasType Γ q X Y) : SideC.HasType Γ' q X Y := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.refine hR) (hq.refine hR)

theorem ShapeCo.HasType.refine {Γ Γ' : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ˢ e : S ≤ T) : Γ' ⊢ˢ e : S ≤ T := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.refine hR) (hf.refine hR)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.refine hR)
  | .pi he hf hc =>
      exact .pi (LeCo.HasType.refine hR.scope he) (ELeCo.HasType.refine (hR.body _) hf) hc
  | .obj hm => exact .obj (hm.refine hR)
  | .pair he hf => exact .pair (he.refine hR) (hf.refine hR)
  | .bound hAt => exact .bound hAt
  | .intoBnd he => exact .intoBnd (he.refine hR)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .boxed hd => exact .boxed (LeCo.HasType.refine hR hd)
  | .toReader => exact .toReader
  | .readerCov hd => exact .readerCov (LeCo.HasType.refine hR hd)

theorem LeCo.HasType.refine {Γ Γ' : Ctx s} {d : LeCo s} {S T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ d : S ≤ T) : Γ' ⊢ d : S ≤ T := by
  match h with
  | .capt he hf => exact .capt (he.refine hR) (hf.refine hR)

theorem ELeCo.HasType.refine {Γ Γ' : Ctx s} {g : ELeCo s} {E E' : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᵉ g : E ≤ E') : Γ' ⊢ᵉ g : E ≤ E' := by
  match h with
  | .plain he => exact .plain (LeCo.HasType.refine hR he)
  | .pack hc he hA =>
      exact .pack (hc.refine hR) (LeCo.HasType.refine (hR.scopeInst _) he) (hR.accessOnly hA)
  | .cong hc he =>
      exact .cong (hc.refine hR) (LeCo.HasType.refine hR.scope he)
  | .trans hg hh => exact .trans (hg.refine hR) (hh.refine hR)
  | .packF hN hD hc he =>
      exact .packF hN hD (fun κ hκ => hR.kill.consumable (hc κ hκ) rfl)
        (LeCo.HasType.refine ((hR.consC _).consC _) he)
  | .congF he => exact .congF (LeCo.HasType.refine ((hR.consC _).consC _) he)

theorem EqCo.HasType.refine {Γ Γ' : Ctx s} {φ : EqCo s} {S T : Shape s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ φ : S ≡ T) : Γ' ⊢ φ : S ≡ T := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .def hd => exact .def (hR.def_ _ _ _ hd)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem Has.HasType.refine {Γ Γ' : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ hh : x ∋ l) : Γ' ⊢ hh : x ∋ l := by
  match h with
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .field hf hm => exact .field (hR.fields _ _ hf) hm

theorem Side.HasType.refine {Γ Γ' : Ctx s} {σ : Side s} {X Y : Shape (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Side.HasType Γ σ X Y) : Side.HasType Γ' σ X Y := by
  match h with
  | .none => exact .none
  | .some he => exact .some (he.refine hR)

theorem Morphism.HasType.refine {Γ Γ' : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ m : src ⇒ Tel := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost => exact .le (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .leEq hm hAt hpre hpost => exact .leEq (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .eq hm hAt => exact .eq (hm.refine hR) hAt
  | .eqSym hm hAt => exact .eqSym (hm.refine hR) hAt
  | .has hm hAt => exact .has (hm.refine hR) hAt
  | .bnd hm he => exact .bnd (hm.refine hR) (he.refine hR)
  | .leC hm hh hq hq' => exact .leC (hm.refine hR) hh (hq.refine hR) (hq'.refine hR)
  | .eqC hm hAt => exact .eqC (hm.refine hR) hAt
  | .eqSymC hm hAt => exact .eqSymC (hm.refine hR) hAt

theorem Atom.HasType.refine {Γ Γ' : Ctx s} {a : Atom s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ₐ a : T) : Γ' ⊢ₐ a : T := by
  match h with
  | @Atom.HasType.var _ _ x => rw [← hR.ty x]; exact .var
  | .cast ha he => exact .cast (ha.refine hR) (LeCo.HasType.refine hR he)
  | .unfoldSelf ha => exact .unfoldSelf (ha.refine hR)
  | .foldSelf ha => exact .foldSelf (ha.refine hR)
  | .both ha hb hr => exact .both (ha.refine hR) (hb.refine hR) hr
  | .recap ha hf => exact .recap (ha.refine hR) (hf.refine hR)

end

/-- The packed-atom wrapper premises only judgments of the block above. -/
theorem PAtom.HasType.refine {Γ Γ' : Ctx s} {p : PAtom s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ₚ p : E) : Γ' ⊢ₚ p : E := by
  match h with
  | .plain ha => exact .plain (Atom.HasType.refine hR ha)
  | .pack ha hc he hA =>
      exact .pack (Atom.HasType.refine hR ha) (CapCo.HasType.refine hR hc)
        (LeCo.HasType.refine (hR.scopeInst _) he) (hR.accessOnly hA)
  | .packF ha hN hD hc he =>
      exact .packF (Atom.HasType.refine hR ha) hN hD
        (fun κ hκ => hR.kill.consumable (hc κ hκ) rfl)
        (LeCo.HasType.refine ((hR.consC _).consC _) he)

mutual

/-- The term rules read names, kills and claims, so the refinement lemma of
the term block takes `Ctx.NamesMap` at the identity (plan-5h S0.8). -/
theorem Tm.HasType.refine {Γ Γ' : Ctx s} {t : Tm s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ') (h : Γ ⊢ t :ᵉ E) :
    Γ' ⊢ t :ᵉ E := by
  have hf := CapAtom.nameMapFn_id (s := s)
  have hm : ∀ C : CaptureSet s, C.map (fun a => a) = C := fun C => List.map_id C
  match h with
  | .atom ha => exact .atom (PAtom.HasType.refine hR ha)
  | .val hv hcf => exact .val (hv.refine hR hN) hcf
  | @Tm.HasType.app _ _ a C b T U ha hb hA hK hacc hbA hsep =>
      have hA' : Γ'.Accessible C := by
        have := hN.accessible hR.kill hf hA; rwa [hm] at this
      have hK' : Γ'.ConsumeOk C := by
        have := hN.consumeOk hR.kill hf hK; rwa [hm] at this
      have hbA' : Γ'.Accessible [CapAtom.var b.root] := by
        have := hN.accessible hR.kill hf hbA; rwa [hm] at this
      have hsep' : Γ'.ArgSep [CapAtom.var b.root] C := by
        have := hN.argSep hf hsep (Ctx.KillOk.of_consumeOk hK); rwa [hm, hm] at this
      exact .app (ha.refine hR) (hb.refine hR) hA' hK' (hR.accessOnly hacc) hbA' hsep'
  | @Tm.HasType.proj _ _ a T hh l ha hhh hA hK =>
      have hA' : Γ'.Accessible T.captureSet := by
        have := hN.accessible hR.kill hf hA; rwa [hm] at this
      have hK' : Γ'.ConsumeOk T.captureSet := by
        have := hN.consumeOk hR.kill hf hK; rwa [hm] at this
      exact .proj (ha.refine hR) (hhh.refine hR) hA' hK'
  | @Tm.HasType.let _ _ t T u E f U' ht hko hu hf' =>
      have hk : Ctx.Refines (Γ.killFor t.uses) (Γ'.killFor t.uses) := hR.killFor hN hko
      have hkN := hN.idKillFor hko
      exact .let (ht.refine hR hN) (hN.idKillOk hR.kill hko) (hu.refine (hk.cons _) (hkN.idLift _))
        (hf'.refine (hk.cons _))
  | .cast ht he => exact .cast (ht.refine hR hN) (LeCo.HasType.refine hR he)
  | @Tm.HasType.castE _ _ t E g E' ht hko hg =>
      have hk : Ctx.Refines (Γ.killFor t.uses) (Γ'.killFor t.uses) := hR.killFor hN hko
      exact .castE (ht.refine hR hN) (hN.idKillOk hR.kill hko) (ELeCo.HasType.refine hk hg)
  | @Tm.HasType.letex _ _ t h u f T C₀ U' E ht hko hc hkU hsep hbA hu hf' =>
      have hk : Ctx.Refines (Γ.killFor t.uses) (Γ'.killFor t.uses) := hR.killFor hN hko
      have hkN := hN.idKillFor hko
      have hsep' : Γ'.ArgSep C₀ U' := by
        have := hN.argSep hf hsep hkU; rwa [hm, hm] at this
      have hbA' : (Γ'.killFor t.uses).Accessible C₀ := by
        have := hkN.accessible hk.kill hf hbA; rwa [hm] at this
      exact .letex (ht.refine hR hN) (hN.idKillOk hR.kill hko) (hc.refine hR)
        (hN.idKillOk hR.kill hkU) hsep' hbA'
        (hu.refine ((hk.consC .star).cons _) ((hkN.idLiftC .star).idLift _))
        (hf'.refine ((hk.consC .star).cons _))
  | @Tm.HasType.unbox _ _ a D C S f U ha hf' hA =>
      have hA' : Γ'.Accessible D := by
        have := hN.accessible hR.kill hf hA; rwa [hm] at this
      exact .unbox (ha.refine hR) (hf'.refine hR) hA'
  | .newLet ha hT hu hf' =>
      exact .newLet (ha.refine hR) hT (hu.refine ((hR.consC _).cons _) ((hN.idLiftC _).idLift _))
        (hf'.refine ((hR.consC _).cons _))
  | @Tm.HasType.read _ _ a S C T ha hS hA =>
      have hA' : Γ'.Accessible C := by
        have := hN.accessible hR.kill hf hA; rwa [hm] at this
      exact .read (ha.refine hR) hS hA'
  | @Tm.HasType.write _ _ a b T C ha hb hA =>
      have hA' : Γ'.Accessible C := by
        have := hN.accessible hR.kill hf hA; rwa [hm] at this
      exact .write (ha.refine hR) (hb.refine hR) hA'
  | @Tm.HasType.letexF _ _ t u f T E U' ht hko hu hf' =>
      have hk : Ctx.Refines (Γ.freshCtx t.uses T) (Γ'.freshCtx t.uses T) :=
        hR.freshCtx hN hko T
      exact .letexF (ht.refine hR hN) (hN.idKillOk hR.kill hko)
        (hu.refine hk (hN.idFreshCtx hko T)) (hf'.refine hk)

theorem Value.HasType.refine {Γ Γ' : Ctx s} {v : Value s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ v : T := by
  match h with
  | .lam ht hg => exact .lam (ht.refine (hR.body _) (hN.idBody _)) (hg.refine (hR.body _))
  | .obj hF hW =>
      exact .obj (hF.refine (hR.objBody _ _ _ _) (hN.idObjBody _ _ _ _))
        (fun ℓ hℓ => (hR.cons _).accessOnly (hW ℓ hℓ))
  | .box ha => exact .box (ha.refine hR)
  | .cast hv he => exact .cast (hv.refine hR hN) (LeCo.HasType.refine hR he)
  | .cell hℓ ha hT =>
      obtain ⟨k', hk'⟩ := hR.locOf hℓ
      exact .cell hk' (ha.refine hR) hT
  | .reader htr hty => exact .reader (hR.transparentOf htr) (by rw [hR.ty]; exact hty)

theorem Value.HasTypeE.refine {Γ Γ' : Ctx s} {v : Value s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ') (h : Γ ⊢ᵥᵉ v : E) :
    Γ' ⊢ᵥᵉ v : E := by
  match h with
  | .plain hv => exact .plain (hv.refine hR hN)
  | .pack hv hc he hA =>
      exact .pack (hv.refine hR hN) (hc.refine hR) (LeCo.HasType.refine (hR.scopeInst _) he)
        (hR.accessOnly hA)
  | .packF hv hNm hD hc he =>
      exact .packF (hv.refine hR hN) hNm hD (fun κ hκ => hR.kill.consumable (hc κ hκ) rfl)
        (LeCo.HasType.refine ((hR.consC _).consC _) he)

theorem Fields.HasType.refine {Γ Γ' : Ctx (s,x)} {F : Fields (s,x)} {A : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (hN : Γ.NamesMap (fun a => a) Γ') (h : Γ ⊢ᶠ[A] F) :
    Γ' ⊢ᶠ[A] F := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg => exact .cons (hF.refine hR hN) (ht.refine hR hN) (hg.refine hR)

end

/-! ## Reviving bits

A kill changes bits and nothing else, so the identity from a killed context
to the context it was killed from is a refinement, and it keeps names.  Every
judgment typed under kills holds without them.  For atoms and evidence the
converse holds too (`Atom.HasType.unkill` below), since a fresh pack inside a
pi codomain packs nothing (plan-5h decision 38). -/

/-- Reviving the bits of a killed context is a refinement. -/
theorem Ctx.Refines.revive (Γ : Ctx s) (D : List (BVar s .cap)) :
    Ctx.Refines (Γ.killNames D) Γ :=
  (Ctx.Refines.refl (Γ := Γ)).killNames (D' := []) (fun _ h => by cases h)

/-- Reviving the bits of a killed context keeps names. -/
theorem Ctx.NamesMap.revive (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).NamesMap (fun a => a) Γ :=
  (Ctx.NamesMap.refl Γ).killNames D [] (fun _ h => by cases h)

theorem Atom.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {a : Atom s} {T : Ty s}
    (h : Γ.killNames D ⊢ₐ a : T) : Γ ⊢ₐ a : T :=
  h.refine (Ctx.Refines.revive Γ D)

theorem PAtom.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {p : PAtom s} {E : ETy s}
    (h : Γ.killNames D ⊢ₚ p : E) : Γ ⊢ₚ p : E :=
  h.refine (Ctx.Refines.revive Γ D)

theorem CapCo.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {f : CapCo s}
    {C C' : CaptureSet s} (h : Γ.killNames D ⊢ᶜ f : C ⊑ C') : Γ ⊢ᶜ f : C ⊑ C' :=
  h.refine (Ctx.Refines.revive Γ D)

theorem CapEq.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {φ : CapEq s}
    {C C' : CaptureSet s} (h : Γ.killNames D ⊢ᶜ φ : C ≡ C') : Γ ⊢ᶜ φ : C ≡ C' :=
  h.refine (Ctx.Refines.revive Γ D)

theorem ShapeCo.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {e : ShapeCo s}
    {S T : Shape s} (h : Γ.killNames D ⊢ˢ e : S ≤ T) : Γ ⊢ˢ e : S ≤ T :=
  h.refine (Ctx.Refines.revive Γ D)

theorem LeCo.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {d : LeCo s} {S T : Ty s}
    (h : Γ.killNames D ⊢ d : S ≤ T) : Γ ⊢ d : S ≤ T :=
  h.refine (Ctx.Refines.revive Γ D)

theorem ELeCo.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {g : ELeCo s}
    {E E' : ETy s} (h : Γ.killNames D ⊢ᵉ g : E ≤ E') : Γ ⊢ᵉ g : E ≤ E' :=
  h.refine (Ctx.Refines.revive Γ D)

theorem EqCo.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {φ : EqCo s} {S T : Shape s}
    (h : Γ.killNames D ⊢ φ : S ≡ T) : Γ ⊢ φ : S ≡ T :=
  h.refine (Ctx.Refines.revive Γ D)

theorem Has.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {hh : Has s}
    {x : BVar s .var} {l : Label} (h : Γ.killNames D ⊢ hh : x ∋ l) : Γ ⊢ hh : x ∋ l :=
  h.refine (Ctx.Refines.revive Γ D)

theorem Morphism.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)}
    {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ.killNames D ⊢ m : src ⇒ Tel) : Γ ⊢ m : src ⇒ Tel :=
  h.refine (Ctx.Refines.revive Γ D)

/-! ### Unkill in both directions

Atom and evidence typing reads no bit but the witness of a fresh pack, and
under the codomain of an arrow coercion that witness is empty (plan-5h
decision 38).  So the judgments of the type-sort block hold under kills
exactly when they hold without them (plan-5h S0.8). -/

/-- **Atom typing reads no bit.** -/
theorem Atom.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {a : Atom s} {T : Ty s} :
    Γ.killNames D ⊢ₐ a : T ↔ Γ ⊢ₐ a : T := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [Atom.rename_id, Ty.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [Atom.rename_id, Ty.rename_id] at this

theorem CapCo.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {f : CapCo s}
    {C C' : CaptureSet s} : Γ.killNames D ⊢ᶜ f : C ⊑ C' ↔ Γ ⊢ᶜ f : C ⊑ C' := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [CapCo.rename_id, CaptureSet.rename_id, CaptureSet.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [CapCo.rename_id, CaptureSet.rename_id, CaptureSet.rename_id] at this

theorem CapEq.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {φ : CapEq s}
    {C C' : CaptureSet s} : Γ.killNames D ⊢ᶜ φ : C ≡ C' ↔ Γ ⊢ᶜ φ : C ≡ C' := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [CapEq.rename_id, CaptureSet.rename_id, CaptureSet.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [CapEq.rename_id, CaptureSet.rename_id, CaptureSet.rename_id] at this

theorem ShapeCo.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {e : ShapeCo s}
    {S T : Shape s} : Γ.killNames D ⊢ˢ e : S ≤ T ↔ Γ ⊢ˢ e : S ≤ T := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [ShapeCo.rename_id, Shape.rename_id, Shape.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [ShapeCo.rename_id, Shape.rename_id, Shape.rename_id] at this

theorem LeCo.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {e : LeCo s} {S T : Ty s} :
    Γ.killNames D ⊢ e : S ≤ T ↔ Γ ⊢ e : S ≤ T := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [LeCo.rename_id, Ty.rename_id, Ty.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [LeCo.rename_id, Ty.rename_id, Ty.rename_id] at this

theorem EqCo.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {φ : EqCo s}
    {S T : Shape s} : Γ.killNames D ⊢ φ : S ≡ T ↔ Γ ⊢ φ : S ≡ T := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [EqCo.rename_id, Shape.rename_id, Shape.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [EqCo.rename_id, Shape.rename_id, Shape.rename_id] at this

theorem Has.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)} {hh : Has s}
    {x : BVar s .var} {l : Label} : Γ.killNames D ⊢ hh : x ∋ l ↔ Γ ⊢ hh : x ∋ l := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [Has.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [Has.rename_id] at this

theorem Morphism.HasType.unkill {Γ : Ctx s} {D : List (BVar s .cap)}
    {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)} :
    Γ.killNames D ⊢ m : src ⇒ Tel ↔ Γ ⊢ m : src ⇒ Tel := by
  constructor
  · intro h
    have := h.renameH (Ctx.RenH.reviveNames Γ D)
    rwa [Morphism.rename_id, Rename.lift_id, Telescope.rename_id, Telescope.rename_id] at this
  · intro h
    have := h.renameH (Ctx.RenH.killNames Γ D)
    rwa [Morphism.rename_id, Rename.lift_id, Telescope.rename_id, Telescope.rename_id] at this

/-- **Term typing is monotone in bits**: a derivation under kills holds
without them. -/
theorem Tm.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {t : Tm s} {E : ETy s}
    (h : Γ.killNames D ⊢ t :ᵉ E) : Γ ⊢ t :ᵉ E :=
  h.refine (Ctx.Refines.revive Γ D) (Ctx.NamesMap.revive Γ D)

theorem Value.HasType.revive {Γ : Ctx s} {D : List (BVar s .cap)} {v : Value s} {T : Ty s}
    (h : Γ.killNames D ⊢ᵥ v : T) : Γ ⊢ᵥ v : T :=
  h.refine (Ctx.Refines.revive Γ D) (Ctx.NamesMap.revive Γ D)

theorem Value.HasTypeE.revive {Γ : Ctx s} {D : List (BVar s .cap)} {v : Value s} {E : ETy s}
    (h : Γ.killNames D ⊢ᵥᵉ v : E) : Γ ⊢ᵥᵉ v : E :=
  h.refine (Ctx.Refines.revive Γ D) (Ctx.NamesMap.revive Γ D)

theorem Fields.HasType.revive {Γ : Ctx (s,x)} {D : List (BVar (s,x) .cap)} {F : Fields (s,x)}
    {A : CaptureSet s} (h : Γ.killNames D ⊢ᶠ[A] F) : Γ ⊢ᶠ[A] F :=
  h.refine (Ctx.Refines.revive Γ D) (Ctx.NamesMap.revive Γ D)

