import Coercions.CapturesCC.FCdot.FormTyping
import Coercions.CapturesCC.FCdot.Preservation

namespace CapturesCC

/-!
# The algebra of typed forms: composition, application, fuel

Three facts about forms that the canonical-forms theorem consumes.

* *Composition.*  `Form.combine` of two typed forms is a typed form
  (`Form.combine_typed`); composing object forms routes the second form's
  presence entries through the first (`EntriesTyped.through`).  The chain
  of casts composes the same way (`ChainTyped.combine`), and plain typedness
  lifts to the opened shapes at any root (`FormTyped.atRoot`).
* *Application.*  Applying a typed form to the typed view of an atom gives
  the typed view of the target (`viewThrough_typed`, `entriesAt_typed`).
* *Fuel.*  Every function of the normalizer is monotone in its fuel, so a
  result found with fuel `n` is found with every larger fuel, and two
  successful runs agree (`hnf_le`, `view_le`, ..., `hnf_det`).

Everything is structural: no depth, no environments.
-/

namespace FCdot

/-! ## A self-cast substitution between opaque binders

`Form.combine` on two function forms retypes the first codomain evidence
under the *second* source's domain binder, by casting the binder through the
composite domain evidence.  `Subst.Typed.selfCast` (`Preservation.lean`)
does this for a transparent target binder; the version needed here has an
opaque one. -/

theorem Subst.Typed.selfCastOpaque {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    (hE : Γ ⊢ E : S₀ ≤ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E↑) (Γ.cons (.opaque S₀)) where
  var := by
    intro y
    cases y with
    | here =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.cast (.var .here) E↑)
          (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E↑).root)
        have hE' : (Γ.cons (.opaque S₀)) ⊢ E↑ : S₀↑ ≤ T↑ :=
          hE.weaken _
        have hvar : (Γ.cons (.opaque S₀)) ⊢ₐ .var .here : S₀↑ := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.opaque S₀)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.var (.there z))
          (((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E↑).root)
        simpa using Atom.HasType.var (Γ := Γ.cons (.opaque S₀)) (x := .there z)
  ty := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simp
  transparent := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simpa using (Ctx.isTransparent_there Γ _ z).mp ht
  def_ := by
    intro y l W hW
    cases y with
    | here => simp at hW
    | there z =>
        rw [Ctx.lookupDef_there] at hW
        simpa using hW
  defC := by
    intro y l C hC
    cases y with
    | here => simp at hC
    | there z =>
        rw [Ctx.lookupDefC_there] at hC
        simpa using hC
  fields := by
    intro y Fs hFs
    cases y with
    | here => simp at hFs
    | there z =>
        rw [Ctx.lookupFields_there] at hFs
        simpa using hFs
  capRoot := by
    intro r hr
    simp only [Subst.selfCast_root, CapAtom.rename_id]
    unfold Ctx.IsRoot
    rw [← Ctx.isRootB_cons_eq Γ (Binding.opaque T) (.opaque S₀) r]
    exact hr
  capLvl := by
    intro e r _ hl
    simp only [Subst.selfCast_root, CapAtom.rename_id]
    unfold Ctx.LvlLe
    rw [← Ctx.lvlLeB_cons_eq Γ (Binding.opaque T) (.opaque S₀) e r]
    exact hl
  capInner := by
    simp only [Subst.selfCast_root, CapAtom.rename_id]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Typedness depends on an endpoint only through its shape -/

mutual

theorem FormTyped.srcRes {s : Sig} {Γ : Ctx s} {ρ : Option (BVar s .var)} {F : Form s}
    {S S' T : Shape s} (h : Γ.resolveAt? ρ S = Γ.resolveAt? ρ S') (hF : FormTyped Γ ρ F S' T) :
    FormTyped Γ ρ F S T := by
  match hF with
  | .bot hS => exact .bot (h.trans hS)
  | .top hT => exact .top hT
  | .id hres => exact .id (h.trans hres)
  | .eqv hres => exact .eqv (h.trans hres)
  | .pi hS hT hd hc => exact .pi (h.trans hS) hT hd hc
  | .obj hS hT hEs => exact .obj (h.trans hS) hT hEs
  | .boxed hS hT hd => exact .boxed (h.trans hS) hT hd
  | .bnd hS hAt hF' => exact .bnd (h.trans hS) hAt hF'
  | .into hT hB => exact .into hT (BndsTyped.srcRes h hB)

theorem BndsTyped.srcRes {s : Sig} {Γ : Ctx s} {ρ : Option (BVar s .var)} {S S' : Shape s}
    {Es : Entries s} {Tel : Telescope (s,x)}
    (h : Γ.resolveAt? ρ S = Γ.resolveAt? ρ S') (hB : BndsTyped Γ ρ S' Es Tel) :
    BndsTyped Γ ρ S Es Tel := by
  match hB with
  | .nil => exact .nil
  | .cons hB' hF => exact .cons (BndsTyped.srcRes h hB') (FormTyped.srcRes h hF)
  | .thru hB' hH hM hE => exact .thru (BndsTyped.srcRes h hB') (FormTyped.srcRes h hH) hM hE

end

theorem FormTyped.tgtRes {s : Sig} {Γ : Ctx s} {ρ : Option (BVar s .var)} {F : Form s}
    {S T T' : Shape s} (h : Γ.resolveAt? ρ T' = Γ.resolveAt? ρ T) (hF : FormTyped Γ ρ F S T') :
    FormTyped Γ ρ F S T := by
  match hF with
  | .bot hS => exact .bot hS
  | .top hT => exact .top (h.symm.trans hT)
  | .id hres => exact .id (hres.trans h)
  | .eqv hres => exact .eqv (hres.trans h)
  | .pi hS hT hd hc => exact .pi hS (h.symm.trans hT) hd hc
  | .obj hS hT hEs => exact .obj hS (h.symm.trans hT) hEs
  | .boxed hS hT hd => exact .boxed hS (h.symm.trans hT) hd
  | .bnd hS hAt hF' => exact .bnd hS hAt (FormTyped.tgtRes h hF')
  | .into hT hB => exact .into (h.symm.trans hT) hB

theorem ChainTyped.srcRes {r : BVar s .var} {F : Form s} {S S' T : Shape s}
    (h : Γ.resolveAt r S = Γ.resolveAt r S') (hF : Γ ⊨[r] F : S' ≤ T) : Γ ⊨[r] F : S ≤ T :=
  FormTyped.srcRes (by simpa using h) hF

theorem ChainTyped.tgtRes {r : BVar s .var} {F : Form s} {S T T' : Shape s}
    (h : Γ.resolveAt r T' = Γ.resolveAt r T) (hF : Γ ⊨[r] F : S ≤ T') : Γ ⊨[r] F : S ≤ T :=
  FormTyped.tgtRes (by simpa using h) hF

/-! ## Opening a telescope at a root

Typedness of entries is stable under opening both telescopes at a root: a
closed side stays closed, and holes follow the renaming. -/

theorem Shape.weaken_inj {A B : Shape s} (h : (A.weaken (k := .var)) = B.weaken) : A = B :=
  Shape.rename_inj _ _ _ Rename.succ_injective h

theorem SideTyped.open (r : BVar s .var) {F : Form s} {S X : Shape (s,x)}
    (h : SideTyped Γ F S X) : SideTyped Γ F ((S⟦r⟧)↑) ((X⟦r⟧)↑) := by
  cases h with
  | id => exact .id
  | closed hF => rw [Shape.weaken_substVar, Shape.weaken_substVar]; exact .closed hF

/-- A capture step opened at a root: a closed step is between weakened closed
sets, which opening leaves alone; an inclusion step is opened pointwise, and a
syntactic inclusion survives a renaming. -/
theorem CapStepTyped.open (r : BVar s .var) {st : CapStep s} {X Y : CaptureSet (s,x)}
    (h : CapStepTyped Γ st X Y) : CapStepTyped Γ st ((X⟦r⟧)↑) ((Y⟦r⟧)↑) := by
  cases h with
  | closed hle =>
      rw [CaptureSet.rename_subst_weaken, CaptureSet.rename_subst_weaken]
      exact .closed hle
  | incl hsub => exact .incl ((hsub.rename (Rename.subst r)).rename Rename.succ)

theorem SideTypedC.open (r : BVar s .var) : ∀ {q : SideC s} {X Y : CaptureSet (s,x)},
    SideTypedC Γ q X Y → SideTypedC Γ q ((X⟦r⟧)↑) ((Y⟦r⟧)↑)
  | _, _, _, .nil => .nil
  | _, _, _, .cons hst hq => .cons (hst.open r) (SideTypedC.open r hq)

/-- Capture-template sides compose by concatenating their chains. -/
theorem SideTypedC.append : ∀ {q q' : SideC s} {X Y Z : CaptureSet (s,x)},
    SideTypedC Γ q X Y → SideTypedC Γ q' Y Z → SideTypedC Γ (q ++ q') X Z
  | _, _, _, _, _, .nil, h => h
  | _, _, _, _, _, .cons hst hq, h => .cons hst (SideTypedC.append hq h)

theorem Telescope.HoleAtC.open (r : BVar s .var) {Tel : Telescope (s,x)} {h : HoleC}
    {C₁ C₂ : CaptureSet (s,x)} (hh : Tel.HoleAtC h C₁ C₂) :
    ((Tel⟦r⟧)↑).HoleAtC h ((C₁⟦r⟧)↑) ((C₂⟦r⟧)↑) := by
  cases hh with
  | leC hAt => exact .leC ((hAt.rename _).rename _)
  | eqC hAt => exact .eqC ((hAt.rename _).rename _)
  | eqSymC hAt => exact .eqSymC ((hAt.rename _).rename _)

theorem Telescope.HoleAt.open (r : BVar s .var) {Tel : Telescope (s,x)} {h : Hole}
    {X Y : Shape (s,x)} (hh : Tel.HoleAt h X Y) :
    ((Tel⟦r⟧)↑).HoleAt h ((X⟦r⟧)↑) ((Y⟦r⟧)↑) := by
  cases hh with
  | le hAt => exact .le ((hAt.rename _).rename _)
  | eq hAt => exact .eq ((hAt.rename _).rename _)
  | eqSym hAt => exact .eqSym ((hAt.rename _).rename _)

/-! ## Plain typedness gives typedness at the shapes opened at any root

The opened shape of an endpoint is a non-name type determined by the plain
shape, and resolution is the identity on it. -/

mutual

theorem FormTyped.atRoot {s : Sig} {Γ : Ctx s} {F : Form s} {S T : Shape s} (r : BVar s .var)
    (h : Γ ⊨ F : S ≤ T) : Γ ⊨[r] F : S ≤ T := by
  match h with
  | .bot hS => exact .bot (Ctx.resolveAt_of_resolve r hS)
  | .top hT => exact .top (Ctx.resolveAt_of_resolve r hT)
  | .id hres => exact .id (Ctx.resolveAt_of_resolve r hres)
  | .eqv hres => exact .eqv (Ctx.resolveAt_of_resolve r hres)
  | .pi hS hT hd hc =>
      exact .pi (Ctx.resolveAt_of_resolve r hS) (Ctx.resolveAt_of_resolve r hT) hd hc
  | .obj hS hT hEs =>
      exact .obj (Ctx.resolveAt_of_resolve r hS) (Ctx.resolveAt_of_resolve r hT)
        (EntriesTyped.atRoot r hEs)
  | .boxed hS hT hd =>
      exact .boxed (Ctx.resolveAt_of_resolve r hS) (Ctx.resolveAt_of_resolve r hT) hd
  | .bnd (T := T') (Tel := Tel) (i := i) hS hAt hF' =>
      refine .bnd (Ctx.resolveAt_of_resolve r hS) ?_ (FormTyped.atRoot r hF')
      have h1 : Telescope.At (Tel⟦r⟧) i ((⊑ T'↑ : Proposition (s,x))⟦r⟧) :=
        hAt.rename (Rename.subst r)
      rw [show ((⊑ T'↑ : Proposition (s,x))⟦r⟧) = ⊑ T' from by
        simp [Proposition.substVar_bnd]] at h1
      exact h1.weaken
  | .into hT hB =>
      exact .into (Ctx.resolveAt_of_resolve r hT) (BndsTyped.atRoot r hB)

theorem EntriesTyped.atRoot {s : Sig} {Γ : Ctx s} (r : BVar s .var)
    {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s} (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) :
    EntriesTyped Γ (some r) ((Tel₁⟦r⟧)↑) Es ((Tel₂⟦r⟧)↑) := by
  match h with
  | .nil => exact .nil
  | .le h' hh hpre hpost =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_le,
        Proposition.weaken_le]
      exact .le (EntriesTyped.atRoot r h') (hh.open r) (hpre.open r) (hpost.open r)
  | .eq h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq]
      exact .eq (EntriesTyped.atRoot r h') ((hAt.rename _).rename _)
  | .eqSym h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq]
      exact .eqSym (EntriesTyped.atRoot r h') ((hAt.rename _).rename _)
  | .has h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_has,
        Proposition.weaken_has]
      exact .has (EntriesTyped.atRoot r h') ((hAt.rename _).rename _)
  | .bnd (Tel₁ := Tel₁) h' hG =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_bnd,
        Proposition.weaken_bnd, Shape.weaken_substVar]
      refine .bnd (EntriesTyped.atRoot r h') ?_
      refine FormTyped.srcRes ?_ (FormTyped.atRoot r hG)
      simp
  | .bndId (X := X) (Tel₁ := Tel₁) (j := j) h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_bnd,
        Proposition.weaken_bnd]
      refine .bndId (EntriesTyped.atRoot r h') ?_
      have h1 : Telescope.At (Tel₁⟦r⟧) j ((⊑ X : Proposition (s,x))⟦r⟧) :=
        hAt.rename (Rename.subst r)
      exact h1.weaken
  | .leC h' hh hpre hpost =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_leC,
        Proposition.weaken_leC]
      exact .leC (EntriesTyped.atRoot r h') (hh.open r) (hpre.open r) (hpost.open r)
  | .eqC h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eqC,
        Proposition.weaken_eqC]
      exact .eqC (EntriesTyped.atRoot r h') ((hAt.rename _).rename _)
  | .eqSymC h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eqC,
        Proposition.weaken_eqC]
      exact .eqSymC (EntriesTyped.atRoot r h') ((hAt.rename _).rename _)

theorem BndsTyped.atRoot {s : Sig} {Γ : Ctx s} (r : BVar s .var) {S : Shape s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ none S Es Tel) :
    BndsTyped Γ (some r) S Es ((Tel⟦r⟧)↑) := by
  match h with
  | .nil => exact .nil
  | .cons h' hF =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_bnd,
        Proposition.weaken_bnd, Shape.weaken_substVar]
      exact .cons (BndsTyped.atRoot r h') (FormTyped.atRoot r hF)
  | .thru (M := M) (TelM := TelM) h' hH hM hE =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons]
      exact .thru (BndsTyped.atRoot r h') (FormTyped.atRoot r hH)
        (Ctx.resolveAt_of_resolve r hM) (EntryTyped.atRoot r hE)

theorem EntryTyped.atRoot {s : Sig} {Γ : Ctx s} (r : BVar s .var) {Tel₁ : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} (h : EntryTyped Γ none Tel₁ E P) :
    EntryTyped Γ (some r) ((Tel₁⟦r⟧)↑) E ((P⟦r⟧)↑) := by
  match h with
  | .le hh hpre hpost =>
      simp only [Proposition.substVar_le, Proposition.weaken_le]
      exact .le (hh.open r) (hpre.open r) (hpost.open r)
  | .eq hAt =>
      simp only [Proposition.substVar_eq, Proposition.weaken_eq]
      exact .eq ((hAt.rename _).rename _)
  | .eqSym hAt =>
      simp only [Proposition.substVar_eq, Proposition.weaken_eq]
      exact .eqSym ((hAt.rename _).rename _)
  | .has hAt =>
      simp only [Proposition.substVar_has, Proposition.weaken_has]
      exact .has ((hAt.rename _).rename _)
  | .bnd (Tel₁ := Tel₁) hG =>
      simp only [Proposition.substVar_bnd, Proposition.weaken_bnd, Shape.weaken_substVar]
      refine .bnd (FormTyped.srcRes ?_ (FormTyped.atRoot r hG))
      simp
  | .bndId (X := X) (j := j) hAt =>
      simp only [Proposition.substVar_bnd, Proposition.weaken_bnd]
      refine .bndId ?_
      have h1 : Telescope.At (Tel₁⟦r⟧) j ((⊑ X : Proposition (s,x))⟦r⟧) :=
        hAt.rename (Rename.subst r)
      exact h1.weaken
  | .leC hh hpre hpost =>
      simp only [Proposition.substVar_leC, Proposition.weaken_leC]
      exact .leC (hh.open r) (hpre.open r) (hpost.open r)
  | .eqC hAt =>
      simp only [Proposition.substVar_eqC, Proposition.weaken_eqC]
      exact .eqC ((hAt.rename _).rename _)
  | .eqSymC hAt =>
      simp only [Proposition.substVar_eqC, Proposition.weaken_eqC]
      exact .eqSymC ((hAt.rename _).rename _)

end

/-- Entries typed plainly are typed at the opened telescopes. -/
theorem EntriesTyped.open (r : BVar s .var) {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) : EntriesTyped Γ (some r) ((Tel₁⟦r⟧)↑) Es ((Tel₂⟦r⟧)↑) :=
  EntriesTyped.atRoot r h

/-! ## Entries by position -/

theorem EntriesTyped.length {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) : Es.length = Tel₂.length := by
  match h with
  | .nil => rfl
  | .le h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]
  | .eq h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .eqSym h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .has h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .bnd h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .bndId h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .leC h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]
  | .eqC h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .eqSymC h' _ => simp [Entries.length, Telescope.length, h'.length]

/-- The entry at an inclusion of the target is a template. -/
theorem EntriesTyped.At_le {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {S T : Shape (s,x)}
    (hAt : Tel₂ ∋ (j ↦ S ⊑ T)) :
    ∃ pre h' post X Y, Es ∋ (j ↦ .le pre h' post) ∧ Tel₁.HoleAt h' X Y ∧
      SideTyped Γ pre S X ∧ SideTyped Γ post Y T := by
  match h with
  | .nil => cases hAt
  | .le hEs hh hpre hpost =>
      cases hAt with
      | here => exact ⟨_, _, _, _, _, by rw [← hEs.length]; exact .here, hh, hpre, hpost⟩
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .leC hEs _ _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .eqC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .eqSymC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩

/-- The entry at an equality of the target reads a source equality, possibly
flipped. -/
theorem EntriesTyped.At_eq {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {X Y : Shape (s,x)}
    (hAt : Tel₂ ∋ (j ↦ X ≐ Y)) :
    ∃ k b, Es ∋ (j ↦ .eq k b) ∧
      (b = false ∧ Tel₁ ∋ (k ↦ X ≐ Y) ∨ b = true ∧ Tel₁ ∋ (k ↦ Y ≐ X)) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eq hEs hAt₁ =>
      cases hAt with
      | here => exact ⟨_, false, by rw [← hEs.length]; exact .here, Or.inl ⟨rfl, hAt₁⟩⟩
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqSym hEs hAt₁ =>
      cases hAt with
      | here => exact ⟨_, true, by rw [← hEs.length]; exact .here, Or.inr ⟨rfl, hAt₁⟩⟩
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .leC hEs _ _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqSymC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩

/-- The entry at a presence proposition of the target is a presence entry
pointing at a presence proposition of the source. -/
theorem EntriesTyped.At_has {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {ℓ : Label}
    (hAt : Tel₂ ∋ (j ↦ ∋ ℓ)) :
    ∃ j', Es ∋ (j ↦ .has j') ∧ Tel₁ ∋ (j' ↦ ∋ ℓ) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .has hEs hT =>
      cases hAt with
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, hT⟩
      | there hAt' => obtain ⟨j', hj', hT'⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT'⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .leC hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .eqC hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .eqSymC hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩

/-- The entry at a bound of the target is a bound entry: either a closed
coercion out of the source object type, or the identity on a source bound. -/
theorem EntriesTyped.At_bnd {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {X : Shape (s,x)}
    (hAt : Tel₂ ∋ (j ↦ ⊑ X)) :
    ∃ G, Es ∋ (j ↦ .bnd G) ∧
      ((∃ T : Shape s, X = Shape.weaken T ∧ FormTyped Γ ρ G (μ Tel₁) T) ∨
        (∃ k, G = .bnd k .id ∧ Tel₁ ∋ (k ↦ ⊑ X))) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .bnd hEs hG =>
      cases hAt with
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, Or.inl ⟨_, rfl, hG⟩⟩
      | there hAt' => obtain ⟨G, hG', hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG', hk⟩
  | .bndId hEs hT =>
      cases hAt with
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, Or.inr ⟨_, rfl, hT⟩⟩
      | there hAt' => obtain ⟨G, hG', hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG', hk⟩
  | .leC hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .eqC hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .eqSymC hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩

/-- The bound entry of typed entries, as a form out of any source with the
right shape. -/
theorem EntriesTyped.At_bnd' {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} {S : Shape s} (hS : Γ.resolveAt? ρ S = μ Tel₁)
    (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {T : Shape s} (hAt : Tel₂ ∋ (j ↦ ⊑ T↑)) :
    ∃ G, Es ∋ (j ↦ .bnd G) ∧ FormTyped Γ ρ G S T := by
  obtain ⟨G, hGat, hdisj⟩ := h.At_bnd hAt
  refine ⟨G, hGat, ?_⟩
  rcases hdisj with ⟨T₀, hX, hGt⟩ | ⟨k, rfl, hAt'⟩
  · obtain rfl := Shape.weaken_inj hX
    exact hGt.srcRes (hS.trans (Ctx.resolveAt?_obj_self hS).symm)
  · exact .bnd hS hAt' (.id rfl)

/-- The entry at a subcapturing proposition of the target is a capture
template around a capture proposition of the source. -/
theorem EntriesTyped.At_leC {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {D₁ D₂ : CaptureSet (s,x)}
    (hAt : Tel₂ ∋ (j ↦ D₁ ⊑ᶜ D₂)) :
    ∃ pre h' post X Y, Es ∋ (j ↦ .leC pre h' post) ∧ Tel₁.HoleAtC h' X Y ∧
      SideTypedC Γ pre D₁ X ∧ SideTypedC Γ post Y D₂ := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .leC hEs hh hpre hpost =>
      cases hAt with
      | here => exact ⟨_, _, _, _, _, by rw [← hEs.length]; exact .here, hh, hpre, hpost⟩
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .eqC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩
  | .eqSymC hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh, hpre, hpost⟩ := hEs.At_leC hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh, hpre, hpost⟩

/-- The entry at a capture equality of the target reads a source capture
equality, possibly flipped. -/
theorem EntriesTyped.At_eqC {ρ : Option (BVar s .var)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {C₁ C₂ : CaptureSet (s,x)}
    (hAt : Tel₂ ∋ (j ↦ C₁ ≐ᶜ C₂)) :
    ∃ k b, Es ∋ (j ↦ .eqC k b) ∧
      (b = false ∧ Tel₁ ∋ (k ↦ C₁ ≐ᶜ C₂) ∨ b = true ∧ Tel₁ ∋ (k ↦ C₂ ≐ᶜ C₁)) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .leC hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqC hEs hAt₁ =>
      cases hAt with
      | here => exact ⟨_, false, by rw [← hEs.length]; exact .here, Or.inl ⟨rfl, hAt₁⟩⟩
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩
  | .eqSymC hEs hAt₁ =>
      cases hAt with
      | here => exact ⟨_, true, by rw [← hEs.length]; exact .here, Or.inr ⟨rfl, hAt₁⟩⟩
      | there hAt' => obtain ⟨k, b, hE, hk⟩ := hEs.At_eqC hAt'; exact ⟨k, b, .there hE, hk⟩

/-- The entries of a coercion into a bounds-only object type, by position. -/
theorem BndsTyped.length {ρ : Option (BVar s .var)} {S : Shape s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ ρ S Es Tel) : Es.length = Tel.length := by
  match h with
  | .nil => rfl
  | .cons h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .thru h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]

/-- Composing past the identity template on a source bound. -/
theorem FormTyped.bnd_id_inv {ρ : Option (BVar s .var)} {M T : Shape s} {k : Nat}
    (h : FormTyped Γ ρ (.bnd k .id) M T) {F : Form s} {U : Shape s}
    (hF : FormTyped Γ ρ F T U) : FormTyped Γ ρ (.bnd k F) M U := by
  cases h with
  | bnd hM hAt hid =>
      cases hid with
      | id hres => exact .bnd hM hAt (hF.srcRes hres)

/-- The entry of view-free entries at a bound of the target: a bound entry,
or a routed identity template on a bound of the object type the route
reaches. -/
theorem BndsTyped.At_bnd {ρ : Option (BVar s .var)} {S : Shape s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ ρ S Es Tel) {j : Nat} {X : Shape (s,x)}
    (hAt : Tel ∋ (j ↦ ⊑ X)) {T : Shape s} (hX : X = T↑) :
    (∃ G : Form s, Es ∋ (j ↦ .bnd G) ∧ FormTyped Γ ρ G S T) ∨
    (∃ (H : Form s) (M : Shape s) (k : Nat), Es ∋ (j ↦ .thru H (.bnd (.bnd k .id))) ∧
      FormTyped Γ ρ H S M ∧
      ∀ (F : Form s) (U : Shape s), FormTyped Γ ρ F T U → FormTyped Γ ρ (.bnd k F) M U) := by
  match h with
  | .nil => cases hAt
  | .cons h' hF =>
      cases hAt with
      | here =>
          obtain rfl := Shape.weaken_inj hX.symm
          exact Or.inl ⟨_, by rw [← h'.length]; exact .here, hF⟩
      | there hAt' =>
          rcases h'.At_bnd hAt' hX with ⟨G, hG, hT⟩ | ⟨H, M, k, hG, hH, hk⟩
          · exact Or.inl ⟨G, .there hG, hT⟩
          · exact Or.inr ⟨H, M, k, .there hG, hH, hk⟩
  | .thru (M := M) (TelM := TelM) h' hH hM hE =>
      cases hAt with
      | here =>
          cases hE with
          | bnd hG =>
              obtain rfl := Shape.weaken_inj hX
              exact Or.inr ⟨_, M, _, by rw [← h'.length]; exact .here, hH,
                fun F U hF =>
                  (hG.srcRes (hM.trans (Ctx.resolveAt?_obj_self hM).symm)).bnd_id_inv hF⟩
          | bndId hAt' =>
              subst hX
              exact Or.inr ⟨_, M, _, by rw [← h'.length]; exact .here, hH,
                fun F U hF => FormTyped.bnd_id_inv (.bnd hM hAt' (.id rfl)) hF⟩
      | there hAt' =>
          rcases h'.At_bnd hAt' hX with ⟨G, hG, hT⟩ | ⟨H', M', k, hG, hH', hk⟩
          · exact Or.inl ⟨G, .there hG, hT⟩
          · exact Or.inr ⟨H', M', k, .there hG, hH', hk⟩

/-- An entry found by position is a subterm. -/
theorem Entries.At.sizeOf_lt {Es : Entries s} {j : Nat} {E : Entry s}
    (h : Es ∋ (j ↦ E)) : sizeOf E < sizeOf Es := by
  induction h with
  | here => simp; omega
  | there _ ih => simp; omega

/-! ## Composition of typed forms

Composition substitutes the second coercion's templates into the first's.
The sides of a template are closed forms that compose by `Form.combine`
again, so the three facts are proven together by induction on the size of
the two forms, as the definitions recurse. -/

/-- A form combined with the identity on either side is unchanged. -/
theorem Form.combine_id_left (G : Form s) : Form.combine .id G = some G := by
  cases G <;> simp [Form.combine]

theorem Form.combine_id_right (F : Form s) : Form.combine F .id = some F := by
  cases F <;> simp [Form.combine]

/-- Composition on the far side of a bound cast, when the second form is not
one of the three absorbed by an earlier clause. -/
theorem Form.combine_bnd (i : Nat) {F G H : Form s} (h1 : G ≠ .id) (h2 : G ≠ .top)
    (h3 : ∀ Es, G ≠ .into Es) (h : F.combine G = some H) :
    (Form.bnd i F).combine G = some (.bnd i H) := by
  cases G <;> simp_all [Form.combine]

/-- The identity template on a source bound, recognised. -/
theorem Form.isBndId_eq_true {F : Form s} (h : F.isBndId = true) : ∃ k, F = .bnd k .id := by
  cases F with
  | bnd k G =>
      cases G with
      | id => exact ⟨k, rfl⟩
      | bot => simp [Form.isBndId] at h
      | top => simp [Form.isBndId] at h
      | eqv _ => simp [Form.isBndId] at h
      | pi _ _ => simp [Form.isBndId] at h
      | obj _ => simp [Form.isBndId] at h
      | boxed _ => simp [Form.isBndId] at h
      | bnd _ _ => simp [Form.isBndId] at h
      | into _ => simp [Form.isBndId] at h
  | bot => simp [Form.isBndId] at h
  | top => simp [Form.isBndId] at h
  | id => simp [Form.isBndId] at h
  | eqv _ => simp [Form.isBndId] at h
  | pi _ _ => simp [Form.isBndId] at h
  | obj _ => simp [Form.isBndId] at h
  | boxed _ => simp [Form.isBndId] at h
  | into _ => simp [Form.isBndId] at h

/-- Prefixing a bound entry that is not an identity template composes. -/
theorem Entry.prefix_bnd {F G : Form s} (h : G.isBndId = false) :
    Entry.prefix F (.bnd G) = (Form.combine F G).map Entry.bnd := by
  cases G with
  | bnd k G' =>
      cases G' with
      | id => simp [Form.isBndId] at h
      | bot => simp [Entry.prefix]
      | top => simp [Entry.prefix]
      | eqv _ => simp [Entry.prefix]
      | pi _ _ => simp [Entry.prefix]
      | obj _ => simp [Entry.prefix]
      | boxed _ => simp [Entry.prefix]
      | bnd _ _ => simp [Entry.prefix]
      | into _ => simp [Entry.prefix]
  | bot => simp [Entry.prefix]
  | top => simp [Entry.prefix]
  | id => simp [Entry.prefix]
  | eqv _ => simp [Entry.prefix]
  | pi _ _ => simp [Entry.prefix]
  | obj _ => simp [Entry.prefix]
  | boxed _ => simp [Entry.prefix]
  | into _ => simp [Entry.prefix]

theorem combine_typed_aux {ρ : Option (BVar s .var)} : ∀ n : Nat,
    (∀ (F G : Form s) (S M T : Shape s), sizeOf F + sizeOf G ≤ n →
      FormTyped Γ ρ F S M → FormTyped Γ ρ G M T →
      ∃ H, F.combine G = some H ∧ FormTyped Γ ρ H S T) ∧
    (∀ (Es₁ Es₂ : Entries s) (Tel₁ TelM Tel₂ : Telescope (s,x)), sizeOf Es₁ + sizeOf Es₂ ≤ n →
      Γ.resolveAt? ρ (μ Tel₁) = μ Tel₁ → Γ.resolveAt? ρ (μ TelM) = μ TelM →
      EntriesTyped Γ ρ Tel₁ Es₁ TelM → EntriesTyped Γ ρ TelM Es₂ Tel₂ →
      ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ EntriesTyped Γ ρ Tel₁ Es Tel₂) ∧
    (∀ (F : Form s) (Es : Entries s) (S M : Shape s) (Tel : Telescope (s,x)),
      sizeOf F + sizeOf Es ≤ n →
      FormTyped Γ ρ F S M → BndsTyped Γ ρ M Es Tel →
      ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel) ∧
    (∀ (F : Form s) (Es : Entries s) (S M : Shape s) (TelM Tel : Telescope (s,x)),
      sizeOf F + sizeOf Es ≤ n →
      FormTyped Γ ρ F S M → Γ.resolveAt? ρ M = μ TelM → EntriesTyped Γ ρ TelM Es Tel →
      ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro F G _ _ _ hn; cases F <;> simp at hn
      · intro Es₁ Es₂ _ _ _ hn; cases Es₁ <;> simp at hn
      · intro F Es _ _ _ hn; cases F <;> simp at hn
      · intro F Es _ _ _ _ hn; cases F <;> simp at hn
  | n + 1 => by
      obtain ⟨ihF, ihE, ihB, ihP⟩ := combine_typed_aux (ρ := ρ) n
      -- sides compose, at smaller size
      have side : ∀ (F G : Form s) (S X Y : Shape (s,x)), sizeOf F + sizeOf G ≤ n →
          SideTyped Γ F S X → SideTyped Γ G X Y →
          ∃ H, F.combine G = some H ∧ SideTyped Γ H S Y := by
        intro F G S X Y hn h₁ h₂
        cases h₁ with
        | id =>
            refine ⟨G, Form.combine_id_left G, ?_⟩
            cases h₂ with
            | id => exact .id
            | closed hG => exact .closed hG
        | closed hF =>
            rename_i A B
            generalize hX : (B.weaken : Shape (s,x)) = X at h₂
            cases h₂ with
            | id => rw [← hX]; exact ⟨F, Form.combine_id_right F, .closed hF⟩
            | closed hG =>
                obtain rfl := Shape.weaken_inj hX
                obtain ⟨H, hH, hHt⟩ :=
                  (combine_typed_aux (ρ := none) n).1 F G _ _ _ hn hF hG
                exact ⟨H, hH, .closed hHt⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro F G S M T hn hF hG
        cases hF with
        | bot hS =>
            refine ⟨.bot, ?_, .bot hS⟩
            cases G <;> simp [Form.combine]
        | id hres => exact ⟨G, Form.combine_id_left G, hG.srcRes hres⟩
        | top hM =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => exact ⟨.top, by simp [Form.combine], .top (hres ▸ hM)⟩
            | eqv hres => exact ⟨.top, by simp [Form.combine], .top (hres ▸ hM)⟩
            | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
            | obj ho hT hEs =>
                rw [hM] at ho
                obtain rfl := Shape.obj.inj ho
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihP .top _ S M _ _ (by simp at hn ⊢; omega) (.top hM) hM hEs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
            | boxed hb _ _ => rw [hM] at hb; exact absurd hb (by simp)
            | bnd ho hAt _ =>
                rw [hM] at ho
                obtain rfl := Shape.obj.inj ho
                cases hAt
            | into hT hBs =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB .top _ S M _ (by simp at hn ⊢; omega) (.top hM) hBs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
        | eqv hres =>
            rename_i φ
            cases hG with
            | bot hb => exact ⟨.bot, by simp [Form.combine], .bot (hres.trans hb)⟩
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres' => exact ⟨.eqv φ, by simp [Form.combine], .eqv (hres.trans hres')⟩
            | eqv hres' =>
                rename_i ψ
                exact ⟨.eqv (.trans φ ψ), by simp [Form.combine], .eqv (hres.trans hres')⟩
            | pi hp hT hd hc =>
                refine ⟨_, ?_, .pi (hres.trans hp) hT hd hc⟩; simp [Form.combine]
            | obj ho hT hEs =>
                refine ⟨_, ?_, .obj (hres.trans ho) hT hEs⟩; simp [Form.combine]
            | boxed hb hT hd =>
                refine ⟨_, ?_, .boxed (hres.trans hb) hT hd⟩; simp [Form.combine]
            | bnd ho hAt hF' =>
                refine ⟨_, ?_, .bnd (hres.trans ho) hAt hF'⟩; simp [Form.combine]
            | into hT hBs =>
                refine ⟨_, ?_, .into hT (hBs.srcRes hres)⟩; simp [Form.combine]
        | pi hS hM hd hc =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => refine ⟨_, ?_, .pi hS (hres ▸ hM) hd hc⟩; simp [Form.combine]
            | eqv hres => refine ⟨_, ?_, .pi hS (hres ▸ hM) hd hc⟩; simp [Form.combine]
            | pi hp hT hd₂ hc₂ =>
                rw [hM] at hp
                obtain ⟨rfl, rfl⟩ := Shape.pi.inj hp
                refine ⟨_, ?_, .pi hS hT (.trans hd₂ hd) (.trans
                  (by simpa using LeCo.HasType.subst (Subst.Typed.selfCastOpaque hd₂) hc) hc₂)⟩
                simp [Form.combine]
            | obj ho _ _ => rw [hM] at ho; exact absurd ho (by simp)
            | boxed hb _ _ => rw [hM] at hb; exact absurd hb (by simp)
            | bnd ho _ _ => rw [hM] at ho; exact absurd ho (by simp)
            | into hT hBs =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB _ _ S M _ (by simp at hn ⊢; omega) (.pi hS hM hd hc) hBs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
        | obj hS hM hEs =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => refine ⟨_, ?_, .obj hS (hres.symm.trans hM) hEs⟩; simp [Form.combine]
            | eqv hres => refine ⟨_, ?_, .obj hS (hres.symm.trans hM) hEs⟩; simp [Form.combine]
            | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
            | obj hM' hT hEs₂ =>
                rw [hM] at hM'
                obtain rfl := Shape.obj.inj hM'
                obtain ⟨Es, hEs', hT'⟩ := ihE _ _ _ _ _ (by simp at hn; omega)
                  (Ctx.resolveAt?_obj_self hS) (Ctx.resolveAt?_obj_self hM) hEs hEs₂
                exact ⟨.obj Es, by simp [Form.combine, hEs'], .obj hS hT hT'⟩
            | boxed hb _ _ => rw [hM] at hb; exact absurd hb (by simp)
            | bnd ho hAt hF' =>
                rw [hM] at ho
                obtain rfl := Shape.obj.inj ho
                obtain ⟨G, hGat, hGt⟩ := hEs.At_bnd' hS hAt
                have hsz := hGat.sizeOf_lt
                obtain ⟨H, hH, hHt⟩ := ihF G _ S _ T (by simp at hn hsz ⊢; omega) hGt hF'
                refine ⟨H, ?_, hHt⟩
                obtain ⟨_, hA⟩ := Entries.getBnd?Attach_eq_some hGat.get?
                simp [Form.combine, hA, hH]
            | into hT hBs =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB _ _ S M _ (by simp at hn ⊢; omega) (.obj hS hM hEs) hBs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
        | boxed hS hM hd =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => refine ⟨_, ?_, .boxed hS (hres ▸ hM) hd⟩; simp [Form.combine]
            | eqv hres => refine ⟨_, ?_, .boxed hS (hres ▸ hM) hd⟩; simp [Form.combine]
            | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
            | obj ho _ _ => rw [hM] at ho; exact absurd ho (by simp)
            | boxed hb hT hd₂ =>
                rw [hM] at hb
                obtain rfl := Shape.box.inj hb
                exact ⟨_, by simp [Form.combine], .boxed hS hT (.trans hd hd₂)⟩
            | bnd ho _ _ => rw [hM] at ho; exact absurd ho (by simp)
            | into hT hBs =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB _ _ S M _ (by simp at hn ⊢; omega) (.boxed hS hM hd) hBs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
        | bnd hS hAt hF' =>
            cases hG with
            | id hres =>
                exact ⟨_, Form.combine_id_right _, .bnd hS hAt (hF'.tgtRes hres)⟩
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | into hT hBs =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB _ _ S M _ (by simp at hn ⊢; omega) (.bnd hS hAt hF') hBs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
            | bot hb =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ .bot _ M T (by simp at hn ⊢; omega) hF' (.bot hb)
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
            | eqv hres =>
                rename_i φ
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ (.eqv φ) _ M T (by simp at hn ⊢; omega) hF' (.eqv hres)
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
            | pi hp hT hd hc =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ _ _ M T (by simp at hn ⊢; omega) hF' (.pi hp hT hd hc)
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
            | obj ho hT hEs =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ _ _ M T (by simp at hn ⊢; omega) hF' (.obj ho hT hEs)
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
            | boxed hb hT hd =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ _ _ M T (by simp at hn ⊢; omega) hF' (.boxed hb hT hd)
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
            | bnd ho hAt' hF'' =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ _ _ M T (by simp at hn ⊢; omega) hF' (.bnd ho hAt' hF'')
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH,
                  .bnd hS hAt hHt⟩
        | into hM hBs =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => exact ⟨_, Form.combine_id_right _, .into (hres.symm.trans hM) hBs⟩
            | eqv hres =>
                refine ⟨_, ?_, .into (hres.symm.trans hM) hBs⟩; simp [Form.combine]
            | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
            | boxed hb _ _ => rw [hM] at hb; exact absurd hb (by simp)
            | obj ho hT hEs₂ =>
                rw [hM] at ho
                obtain rfl := Shape.obj.inj ho
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihP _ _ S M _ _ (by simp at hn ⊢; omega) (.into hM hBs) hM hEs₂
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
            | bnd ho hAt hF' =>
                rw [hM] at ho
                obtain rfl := Shape.obj.inj ho
                rcases hBs.At_bnd hAt rfl with ⟨G, hGat, hGt⟩ | ⟨H₀, M₀, k, hGat, hH₀, hk⟩
                · have hsz := hGat.sizeOf_lt
                  obtain ⟨H, hH, hHt⟩ := ihF G _ S _ T (by simp at hn hsz ⊢; omega) hGt hF'
                  refine ⟨H, ?_, hHt⟩
                  obtain ⟨_, hA⟩ := Entries.get?Attach_eq_some hGat.get?
                  simp [Form.combine, hA, hH]
                · have hsz := hGat.sizeOf_lt
                  obtain ⟨H, hH, hHt⟩ :=
                    ihF H₀ _ S M₀ T (by simp at hn hsz ⊢; omega) hH₀ (hk _ _ hF')
                  refine ⟨H, ?_, hHt⟩
                  obtain ⟨_, hA⟩ := Entries.get?Attach_eq_some hGat.get?
                  simp [Form.combine, hA, hH]
            | into hT hBs₂ =>
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihB _ _ S M _ (by simp at hn ⊢; omega) (.into hM hBs) hBs₂
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
      · intro Es₁ Es₂ Tel₁ TelM Tel₂ hn hop₁ hopM h₁ h₂
        match h₂ with
        | .nil => exact ⟨.nil, by simp [Entries.through], .nil⟩
        | .le (pre := pre) (post := post) h₂' hh hpre hpost =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            cases hh with
            | le hAt =>
                obtain ⟨pre₁, h₁', post₁, X₁, Y₁, hE, hh₁, hpre₁, hpost₁⟩ := h₁.At_le hAt
                have hsz := hE.sizeOf_lt
                obtain ⟨pre', hpre', hpreT⟩ :=
                  side pre pre₁ _ _ _ (by simp at hn hsz ⊢; omega) hpre hpre₁
                obtain ⟨post', hpost', hpostT⟩ :=
                  side post₁ post _ _ _ (by simp at hn hsz ⊢; omega) hpost₁ hpost
                refine ⟨Es ▹ .le pre' h₁' post', ?_, .le hT hh₁ hpreT hpostT⟩
                obtain ⟨_, hA⟩ := Entries.get?Attach_eq_some hE.get?
                simp only [Entries.through, hEs]
                unfold Entry.through
                simp [Hole.index, hA, hpre', hpost']
            | eq hAt =>
                obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
                refine ⟨Es ▹ .le pre (if b then .eqSym k else .eq k) post, ?_, ?_⟩
                · obtain ⟨_, hA⟩ := Entries.get?Attach_eq_some hE.get?
                  simp only [Entries.through, hEs]
                  unfold Entry.through
                  simp [Hole.index, hA]
                · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
                  · exact .le hT (.eq hk) hpre hpost
                  · exact .le hT (.eqSym hk) hpre hpost
            | eqSym hAt =>
                obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
                refine ⟨Es ▹ .le pre (if b then .eq k else .eqSym k) post, ?_, ?_⟩
                · obtain ⟨_, hA⟩ := Entries.get?Attach_eq_some hE.get?
                  simp only [Entries.through, hEs]
                  unfold Entry.through
                  simp [Hole.index, hA]
                · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
                  · exact .le hT (.eqSym hk) hpre hpost
                  · exact .le hT (.eq hk) hpre hpost
        | .eq h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
            refine ⟨Es ▹ .eq k b, ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eq hT hk
              · exact .eqSym hT hk
        | .eqSym h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
            refine ⟨Es ▹ .eq k (!b), ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eqSym hT hk
              · exact .eq hT hk
        | .has h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨j', hj', hT'⟩ := h₁.At_has hAt
            exact ⟨Es ▹ .has j', by simp [Entries.through, hEs, Entry.through, hj'.get?], .has hT hT'⟩
        | .bnd (G := G) h₂' hG =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨H, hH, hHt⟩ := ihF (.obj Es₁) G (μ Tel₁) (μ TelM) _
              (by simp at hn ⊢; omega) (.obj hop₁ hopM h₁) hG
            refine ⟨Es ▹ .bnd H, ?_, .bnd hT hHt⟩
            simp [Entries.through, hEs, Entry.through, hH]
        | .bndId (j := k) h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨G, hGat, hdisj⟩ := h₁.At_bnd hAt
            obtain ⟨_, hA⟩ := Entries.getBnd?Attach_eq_some hGat.get?
            refine ⟨Es ▹ .bnd G, ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, Form.combine, hA,
                Form.combine_id_right]
            · rcases hdisj with ⟨T₀, rfl, hGt⟩ | ⟨k', rfl, hAt'⟩
              · exact .bnd hT hGt
              · exact .bndId hT hAt'
        -- A capture template composes by concatenating its chains with the
        -- middle's; a middle capture equality contributes the identity chain,
        -- so the outer sides are kept and only the hole is retargeted.
        | .leC (pre := pre) (post := post) h₂' hh hpre hpost =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            cases hh with
            | leC hAt =>
                obtain ⟨pre₁, h₁', post₁, X₁, Y₁, hE, hh₁, hpre₁, hpost₁⟩ := h₁.At_leC hAt
                refine ⟨Es ▹ .leC (pre ++ pre₁) h₁' (post₁ ++ post), ?_,
                  .leC hT hh₁ (hpre.append hpre₁) (hpost₁.append hpost)⟩
                simp only [Entries.through, hEs]
                unfold Entry.through
                simp [HoleC.index, hE.get?]
            | eqC hAt =>
                obtain ⟨k, b, hE, hk⟩ := h₁.At_eqC hAt
                refine ⟨Es ▹ .leC pre (if b then .eqSymC k else .eqC k) post, ?_, ?_⟩
                · simp only [Entries.through, hEs]
                  unfold Entry.through
                  simp [HoleC.index, hE.get?]
                · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
                  · exact .leC hT (.eqC hk) hpre hpost
                  · exact .leC hT (.eqSymC hk) hpre hpost
            | eqSymC hAt =>
                obtain ⟨k, b, hE, hk⟩ := h₁.At_eqC hAt
                refine ⟨Es ▹ .leC pre (if b then .eqC k else .eqSymC k) post, ?_, ?_⟩
                · simp only [Entries.through, hEs]
                  unfold Entry.through
                  simp [HoleC.index, hE.get?]
                · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
                  · exact .leC hT (.eqSymC hk) hpre hpost
                  · exact .leC hT (.eqC hk) hpre hpost
        | .eqC h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eqC hAt
            refine ⟨Es ▹ .eqC k b, ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eqC hT hk
              · exact .eqSymC hT hk
        | .eqSymC h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eqC hAt
            refine ⟨Es ▹ .eqC k (!b), ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eqSymC hT hk
              · exact .eqC hT hk
      · intro F Es S M Tel hn hF hB
        match hB with
        | .nil => exact ⟨.nil, by simp [Entries.mapPrefix], .nil⟩
        | .cons (F := G) (T := T₀) hB' hG =>
            obtain ⟨Es', hEs', hT'⟩ := ihB F _ S M _ (by simp at hn ⊢; omega) hF hB'
            by_cases hsh : G.isBndId = true
            · obtain ⟨k, rfl⟩ := Form.isBndId_eq_true hsh
              obtain ⟨TelM, hM⟩ : ∃ TelM, Γ.resolveAt? ρ M = μ TelM := by
                cases hG with | bnd hM _ _ => exact ⟨_, hM⟩
              refine ⟨Es' ▹ .thru F (.bnd (.bnd k .id)), ?_, ?_⟩
              · simp [Entries.mapPrefix, hEs', Entry.prefix]
              · exact .thru hT' hF hM
                  (.bnd (hG.srcRes ((Ctx.resolveAt?_obj_self hM).trans hM.symm)))
            · obtain ⟨H, hH, hHt⟩ := ihF F G S M _ (by simp at hn ⊢; omega) hF hG
              have hpre := Entry.prefix_bnd (F := F) (Bool.not_eq_true _ ▸ hsh)
              exact ⟨Es' ▹ .bnd H, by simp [Entries.mapPrefix, hEs', hpre, hH], .cons hT' hHt⟩
        | .thru (H := H₀) (E := E₀) hB' hH₀ hM₀ hE₀ =>
            obtain ⟨Es', hEs', hT'⟩ := ihB F _ S M _ (by simp at hn ⊢; omega) hF hB'
            obtain ⟨K, hK, hKt⟩ := ihF F H₀ S M _ (by simp at hn ⊢; omega) hF hH₀
            exact ⟨Es' ▹ .thru K E₀, by simp [Entries.mapPrefix, hEs', Entry.prefix, hK],
              .thru hT' hKt hM₀ hE₀⟩
      · intro F Es S M TelM Tel hn hF hM hEs
        match hEs with
        | .nil => exact ⟨.nil, by simp [Entries.mapPrefix], .nil⟩
        | .le (pre := pre) (h := h) (post := post) hEs' hh hpre hpost =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.le pre h post),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix],
              .thru hT' hF hM (.le hh hpre hpost)⟩
        | .eq (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.eq j false),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.eq hAt)⟩
        | .eqSym (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.eq j true),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.eqSym hAt)⟩
        | .has (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.has j),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.has hAt)⟩
        | .bnd (G := G) hEs' hG =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            by_cases hsh : G.isBndId = true
            · obtain ⟨k, rfl⟩ := Form.isBndId_eq_true hsh
              refine ⟨Es' ▹ .thru F (.bnd (.bnd k .id)), ?_, ?_⟩
              · simp [Entries.mapPrefix, hEs'', Entry.prefix]
              · exact .thru hT' hF hM (.bnd hG)
            · have hG' : FormTyped Γ ρ G M _ :=
                hG.srcRes (hM.trans (Ctx.resolveAt?_obj_self hM).symm)
              obtain ⟨H, hH, hHt⟩ := ihF F G S M _ (by simp at hn ⊢; omega) hF hG'
              have hpre := Entry.prefix_bnd (F := F) (Bool.not_eq_true _ ▸ hsh)
              exact ⟨Es' ▹ .bnd H, by simp [Entries.mapPrefix, hEs'', hpre, hH], .cons hT' hHt⟩
        | .bndId (j := k) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.bnd (.bnd k .id)),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.bndId hAt)⟩
        | .leC (pre := pre) (h := h) (post := post) hEs' hh hpre hpost =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.leC pre h post),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix],
              .thru hT' hF hM (.leC hh hpre hpost)⟩
        | .eqC (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.eqC j false),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.eqC hAt)⟩
        | .eqSymC (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.eqC j true),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.eqSymC hAt)⟩

theorem Form.combine_typed {ρ : Option (BVar s .var)} {F G : Form s} {S M T : Shape s}
    (hF : FormTyped Γ ρ F S M) (hG : FormTyped Γ ρ G M T) :
    ∃ H, F.combine G = some H ∧ FormTyped Γ ρ H S T :=
  (combine_typed_aux _).1 F G S M T (Nat.le_refl _) hF hG

theorem EntriesTyped.through {ρ : Option (BVar s .var)} {Tel₁ TelM Tel₂ : Telescope (s,x)}
    {Es₁ Es₂ : Entries s}
    (hop₁ : Γ.resolveAt? ρ (μ Tel₁) = μ Tel₁) (hopM : Γ.resolveAt? ρ (μ TelM) = μ TelM)
    (h₁ : EntriesTyped Γ ρ Tel₁ Es₁ TelM) (h₂ : EntriesTyped Γ ρ TelM Es₂ Tel₂) :
    ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ EntriesTyped Γ ρ Tel₁ Es Tel₂ :=
  (combine_typed_aux _).2.1 Es₁ Es₂ Tel₁ TelM Tel₂ (Nat.le_refl _) hop₁ hopM h₁ h₂

theorem BndsTyped.mapPrefix {ρ : Option (BVar s .var)} {F : Form s} {Es : Entries s}
    {S M : Shape s} {Tel : Telescope (s,x)}
    (hF : FormTyped Γ ρ F S M) (hB : BndsTyped Γ ρ M Es Tel) :
    ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel :=
  (combine_typed_aux _).2.2.1 F Es S M Tel (Nat.le_refl _) hF hB

theorem EntriesTyped.mapPrefix {ρ : Option (BVar s .var)} {F : Form s} {Es : Entries s}
    {S M : Shape s} {TelM Tel : Telescope (s,x)}
    (hF : FormTyped Γ ρ F S M) (hM : Γ.resolveAt? ρ M = μ TelM)
    (hEs : EntriesTyped Γ ρ TelM Es Tel) :
    ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel :=
  (combine_typed_aux _).2.2.2 F Es S M TelM Tel (Nat.le_refl _) hF hM hEs

theorem SideTyped.combine {F G : Form s} {S X Y : Shape (s,x)}
    (h₁ : SideTyped Γ F S X) (h₂ : SideTyped Γ G X Y) :
    ∃ H, F.combine G = some H ∧ SideTyped Γ H S Y := by
  cases h₁ with
  | id =>
      refine ⟨G, Form.combine_id_left G, ?_⟩
      cases h₂ with
      | id => exact .id
      | closed hG => exact .closed hG
  | closed hF =>
      rename_i A B
      generalize hX : (B.weaken : Shape (s,x)) = X at h₂
      cases h₂ with
      | id => rw [← hX]; exact ⟨F, Form.combine_id_right F, .closed hF⟩
      | closed hG =>
          obtain rfl := Shape.weaken_inj hX
          obtain ⟨H, hH, hHt⟩ := Form.combine_typed hF hG
          exact ⟨H, hH, .closed hHt⟩

/-- The chain of casts composes: a corollary of `Form.combine_typed` at the
opened shapes. -/
theorem ChainTyped.combine {r : BVar s .var} {F G : Form s} {S M T : Shape s}
    (hF : Γ ⊨[r] F : S ≤ M) (hG : Γ ⊨[r] G : M ≤ T) :
    ∃ H, F.combine G = some H ∧ Γ ⊨[r] H : S ≤ T :=
  Form.combine_typed hF hG

/-! ## Pairing -/

/-- Identity entries are typed from any telescope agreeing with the target at
its positions. -/
theorem Telescope.identityEntries_typed {ρ : Option (BVar s .var)} :
    ∀ (Tel Tel' : Telescope (s,x)),
      (∀ i P, Tel ∋ (i ↦ P) → Tel' ∋ (i ↦ P)) → EntriesTyped Γ ρ Tel' Tel.identityEntries Tel
  | .nil, _, _ => by rw [Telescope.identityEntries]; exact .nil
  | .cons Tel (.le S T), Tel', h => by
      rw [Telescope.identityEntries]
      exact .le (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (.le (h _ _ .here)) .id .id
  | .cons Tel (.eq S T), Tel', h => by
      rw [Telescope.identityEntries]
      exact .eq (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)
  | .cons Tel (.has ℓ), Tel', h => by
      rw [Telescope.identityEntries]
      exact .has (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)
  | .cons Tel (.bnd X), Tel', h => by
      rw [Telescope.identityEntries]
      exact .bndId (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)
  | .cons Tel (.leC C D), Tel', h => by
      rw [Telescope.identityEntries]
      exact .leC (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (.leC (h _ _ .here)) .nil .nil
  | .cons Tel (.eqC C D), Tel', h => by
      rw [Telescope.identityEntries]
      exact .eqC (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)

theorem Telescope.identityEntries_self {ρ : Option (BVar s .var)} (Tel : Telescope (s,x)) :
    EntriesTyped Γ ρ Tel Tel.identityEntries Tel :=
  Telescope.identityEntries_typed Tel Tel fun _ _ h => h

/-- Identity entries depend only on the kinds of the propositions. -/
theorem Telescope.identityEntries_rename : ∀ (Tel : Telescope (s,x)) (ρ : Rename (s,x) (s,x)),
    (Tel.rename ρ).identityEntries = Tel.identityEntries
  | .nil, _ => rfl
  | .cons Tel (.le _ _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.eq _ _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.has _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.bnd _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.leC _ _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.eqC _ _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]

/-- Positions of the first telescope of a concatenation. -/
theorem Telescope.At.append_left {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel ∋ (i ↦ P)) : ∀ Tel' : Telescope s', (Tel ++ Tel') ∋ (i ↦ P)
  | .nil => h
  | .cons Tel' _ => .there (Telescope.At.append_left h Tel')

theorem EntriesTyped.append {ρ : Option (BVar s .var)} {Tel Tel₁ Tel₂ : Telescope (s,x)}
    {Es₁ Es₂ : Entries s}
    (h₁ : EntriesTyped Γ ρ Tel Es₁ Tel₁) (h₂ : EntriesTyped Γ ρ Tel Es₂ Tel₂) :
    EntriesTyped Γ ρ Tel (Es₁ ++ Es₂) (Tel₁ ++ Tel₂) := by
  match h₂ with
  | .nil => exact h₁
  | .le h₂' hh hpre hpost => exact .le (h₁.append h₂') hh hpre hpost
  | .eq h₂' hAt => exact .eq (h₁.append h₂') hAt
  | .eqSym h₂' hAt => exact .eqSym (h₁.append h₂') hAt
  | .has h₂' hAt => exact .has (h₁.append h₂') hAt
  | .bnd h₂' hG => exact .bnd (h₁.append h₂') hG
  | .bndId h₂' hAt => exact .bndId (h₁.append h₂') hAt
  | .leC h₂' hh hpre hpost => exact .leC (h₁.append h₂') hh hpre hpost
  | .eqC h₂' hAt => exact .eqC (h₁.append h₂') hAt
  | .eqSymC h₂' hAt => exact .eqSymC (h₁.append h₂') hAt

theorem BndsTyped.append {ρ : Option (BVar s .var)} {S : Shape s} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es₁ Es₂ : Entries s}
    (h₁ : BndsTyped Γ ρ S Es₁ Tel₁) (h₂ : BndsTyped Γ ρ S Es₂ Tel₂) :
    BndsTyped Γ ρ S (Es₁ ++ Es₂) (Tel₁ ++ Tel₂) := by
  match h₂ with
  | .nil => exact h₁
  | .cons h₂' hF => exact .cons (h₁.append h₂') hF
  | .thru h₂' hH hM hE => exact .thru (h₁.append h₂') hH hM hE

/-- Opening distributes over concatenation. -/
theorem Telescope.openAt?_append (ρ : Option (BVar s .var)) (Tel₁ Tel₂ : Telescope (s,x)) :
    Telescope.openAt? ρ (Tel₁ ++ Tel₂) =
      Telescope.openAt? ρ Tel₁ ++ Telescope.openAt? ρ Tel₂ := by
  cases ρ with
  | none => rfl
  | some r => simp [Telescope.openAt?, Telescope.substVar, Telescope.weaken]

/-- An absorbing form is typed evidence for every inclusion out of its
source. -/
theorem Form.absorbs_typed {ρ : Option (BVar s .var)} : ∀ (F : Form s) (S M U : Shape s),
    F.absorbs = true → FormTyped Γ ρ F S M → FormTyped Γ ρ F S U
  | .bot, _, _, _, _, h => by cases h with | bot hS => exact .bot hS
  | .bnd _ F, _, _, _, hab, h => by
      cases h with
      | bnd hS hAt hF =>
          exact .bnd hS hAt (Form.absorbs_typed F _ _ _ (by simpa [Form.absorbs] using hab) hF)
  | .top, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .id, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .eqv _, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .pi _ _, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .obj _, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .boxed _, _, _, _, hab, _ => by simp [Form.absorbs] at hab
  | .into _, _, _, _, hab, _ => by simp [Form.absorbs] at hab

/-- The view-free entries read off a non-absorbing form into an object
type. -/
theorem Form.freeEntries_typed {ρ : Option (BVar s .var)} : ∀ (F : Form s) {S : Shape s}
    {Tel Tel' : Telescope (s,x)}, FormTyped Γ ρ F S (μ Tel') →
    Γ.resolveAt? ρ (μ Tel') = μ Tel' → Tel.identityEntries = Tel'.identityEntries →
    F.absorbs = false →
    ∃ Es, F.freeEntries Tel = some Es ∧ BndsTyped Γ ρ S Es Tel'
  | .bot, _, _, _, _, _, _, hab => by simp [Form.absorbs] at hab
  | .top, S, Tel, Tel', h, hop, hI, _ => by
      cases h with
      | top hT =>
          rw [hop] at hT
          obtain rfl := Shape.obj.inj hT
          rw [Telescope.identityEntries] at hI
          refine ⟨.nil, ?_, .nil⟩
          simp [Form.freeEntries, Form.toEntries, hI, Entries.mapPrefix]
  | .id, S, Tel, Tel', h, hop, hI, _ => by
      cases h with
      | id hres =>
          rw [hop] at hres
          obtain ⟨Es, hEs, hT⟩ :=
            EntriesTyped.mapPrefix (Γ := Γ) (F := .id) (.id rfl) hres
              (Telescope.identityEntries_self Tel')
          exact ⟨Es, by simp [Form.freeEntries, Form.toEntries, hI, hEs], hT⟩
  | .eqv φ, S, Tel, Tel', h, hop, hI, _ => by
      cases h with
      | eqv hres =>
          rw [hop] at hres
          obtain ⟨Es, hEs, hT⟩ :=
            EntriesTyped.mapPrefix (Γ := Γ) (F := .id) (.id rfl) hres
              (Telescope.identityEntries_self Tel')
          exact ⟨Es, by simp [Form.freeEntries, Form.toEntries, hI, hEs], hT⟩
  | .pi d c, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | pi _ hT _ _ => rw [hop] at hT; exact absurd hT (by simp)
  | .boxed d, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | boxed _ hT _ => rw [hop] at hT; exact absurd hT (by simp)
  | .obj Es₀, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | obj hS hT hEs =>
          rw [hop] at hT
          obtain rfl := Shape.obj.inj hT
          obtain ⟨Es, hEs', hT'⟩ :=
            EntriesTyped.mapPrefix (Γ := Γ) (F := .id) (.id rfl) hS hEs
          exact ⟨Es, by simp [Form.freeEntries, Form.toEntries, hEs'], hT'⟩
  | .into Es₀, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | into hT hB =>
          rw [hop] at hT
          obtain rfl := Shape.obj.inj hT
          exact ⟨Es₀, by simp [Form.freeEntries], hB⟩
  | .bnd i F, S, Tel, Tel', h, hop, hI, hab => by
      cases h with
      | bnd hS hAt hF =>
          obtain ⟨Es, hEs, hT⟩ :=
            Form.freeEntries_typed F hF hop hI (by simpa [Form.absorbs] using hab)
          obtain ⟨Es', hEs', hT'⟩ := BndsTyped.mapPrefix (.bnd hS hAt (.id rfl)) hT
          exact ⟨Es', by simp [Form.freeEntries, hEs, hEs'], hT'⟩

/-- Pairing typed forms.  The annotated telescopes only supply the kinds of
the propositions (for identity entries); the typing telescopes may differ
from them by a renaming. -/
theorem Form.pair_typed {ρ : Option (BVar s .var)} {F G : Form s} {S : Shape s}
    {Tel₁ Tel₂ Tel₁' Tel₂' : Telescope (s,x)}
    (hF : FormTyped Γ ρ F S (μ Tel₁')) (hG : FormTyped Γ ρ G S (μ Tel₂'))
    (hop₁ : Γ.resolveAt? ρ (μ Tel₁') = μ Tel₁') (hop₂ : Γ.resolveAt? ρ (μ Tel₂') = μ Tel₂')
    (hI₁ : Tel₁.identityEntries = Tel₁'.identityEntries)
    (hI₂ : Tel₂.identityEntries = Tel₂'.identityEntries) :
    ∃ H, Form.pair Tel₁ Tel₂ F G = some H ∧ FormTyped Γ ρ H S (μ (Tel₁' ++ Tel₂')) := by
  have hopA : Γ.resolveAt? ρ (μ (Tel₁' ++ Tel₂')) = μ (Tel₁' ++ Tel₂') := by
    rw [Ctx.resolveAt?_obj, Telescope.openAt?_append,
      Ctx.resolveAt?_opened hop₁, Ctx.resolveAt?_opened hop₂]
  by_cases hF0' : F.isBot = true
  · obtain rfl := Form.isBot_eq_true.mp hF0'
    cases hF with
    | bot hS => exact ⟨.bot, by simp [Form.pair], .bot hS⟩
  have hF0 : F ≠ .bot := fun h => hF0' (Form.isBot_eq_true.mpr h)
  by_cases hG0' : G.isBot = true
  · obtain rfl := Form.isBot_eq_true.mp hG0'
    cases hG with
    | bot hS => exact ⟨.bot, by cases F <;> simp [Form.pair], .bot hS⟩
  have hG0 : G ≠ .bot := fun h => hG0' (Form.isBot_eq_true.mpr h)
  by_cases hTT' : F.isTop = true ∧ G.isTop = true
  · obtain ⟨rfl, rfl⟩ :=
      (⟨Form.isTop_eq_true.mp hTT'.1, Form.isTop_eq_true.mp hTT'.2⟩ : F = .top ∧ G = .top)
    refine ⟨.top, by simp [Form.pair], .top ?_⟩
    cases hF with
    | top hT₁ =>
      cases hG with
      | top hT₂ =>
        rw [hop₁] at hT₁; rw [hop₂] at hT₂
        obtain rfl := Shape.obj.inj hT₁
        obtain rfl := Shape.obj.inj hT₂
        exact hopA
  have hpair : Form.pair Tel₁ Tel₂ F G =
      (if F.absorbs then some F
       else if G.absorbs then some G
       else do
        let Es₁ ← F.freeEntries Tel₁
        let Es₂ ← G.freeEntries Tel₂
        pure (.into (Es₁ ++ Es₂))) := by
    have hTT : ¬ (F = .top ∧ G = .top) := fun h =>
      hTT' ⟨Form.isTop_eq_true.mpr h.1, Form.isTop_eq_true.mpr h.2⟩
    cases F <;> cases G <;> simp_all [Form.pair]
  by_cases hab1 : F.absorbs = true
  · exact ⟨F, by rw [hpair, if_pos hab1], Form.absorbs_typed F _ _ _ hab1 hF⟩
  by_cases hab2 : G.absorbs = true
  · exact ⟨G, by rw [hpair, if_neg hab1, if_pos hab2], Form.absorbs_typed G _ _ _ hab2 hG⟩
  obtain ⟨Es₁, hEs₁, hT₁⟩ :=
    Form.freeEntries_typed F hF hop₁ hI₁ (by simpa using hab1)
  obtain ⟨Es₂, hEs₂, hT₂⟩ :=
    Form.freeEntries_typed G hG hop₂ hI₂ (by simpa using hab2)
  refine ⟨.into (Es₁ ++ Es₂), ?_, .into hopA (hT₁.append hT₂)⟩
  rw [hpair, if_neg hab1, if_neg hab2]
  simp [hEs₁, hEs₂]

/-! ## Applying a typed object form to a typed view -/

/-- Concatenation of typed views. -/
theorem ViewTyped.append {r : BVar s .var} {V₁ V₂ : View s} {Tel₁ Tel₂ : Telescope (s,x)}
    (h₁ : Γ ⊨[r, σ] V₁ : Tel₁) (h₂ : Γ ⊨[r, σ] V₂ : Tel₂) :
    Γ ⊨[r, σ] V₁ ++ V₂ : Tel₁ ++ Tel₂ := by
  induction h₂ with
  | nil => exact h₁
  | le _ hF ih => exact .le ih hF
  | eq _ hE ih => exact .eq ih hE
  | has _ hH ih => exact .has ih hH
  | bnd _ hG ih => exact .bnd ih hG
  | leC _ hC ih => exact .leC ih hC
  | eqC _ hC ih => exact .eqC ih hC

/-- A capture-template side instantiated at a root: the roots of its source
are among the roots of its target.  A closed step is between weakened closed
sets, which instantiation leaves alone; an inclusion step is a syntactic
inclusion, which instantiation preserves. -/
theorem SideTypedC.inst (r : BVar s .var) : ∀ {q : SideC s} {X Y : CaptureSet (s,x)},
    SideTypedC Γ q X Y → CapLe Γ (X⟦r⟧) (Y⟦r⟧)
  | _, _, _, .nil => CapLe.refl _ _
  | _, _, _, .cons hst hq => by
      refine CapLe.trans ?_ (SideTypedC.inst r hq)
      cases hst with
      | closed hle =>
          rw [CaptureSet.rename_subst_weaken, CaptureSet.rename_subst_weaken]; exact hle
      | incl hsub => exact CapLe.of_subset (hsub.rename (Rename.subst r))

/-- A closed side instantiated at a root is a typed coercion form. -/
theorem SideTyped.inst (r : BVar s .var) {F : Form s} {S X : Shape (s,x)}
    (h : SideTyped Γ F S X) : Γ ⊨ F : S⟦r⟧ ≤ X⟦r⟧ := by
  cases h with
  | id => exact .id rfl
  | closed hF => rw [Shape.weaken_substVar, Shape.weaken_substVar]; exact hF

/-- In a telescope that is already open at `r`, a bound is a weakened closed
type. -/
theorem Telescope.opened_bnd {r : BVar s .var} {Tel : Telescope (s,x)}
    (hop : Telescope.openAt? (some r) Tel = Tel) {j : Nat} {X : Shape (s,x)}
    (hAt : Tel ∋ (j ↦ ⊑ X)) : X = (X⟦r⟧)↑ := by
  rw [← hop] at hAt
  simp only [Telescope.openAt?_some, Telescope.weaken] at hAt
  obtain ⟨P₀, hP₀, hEq⟩ := Telescope.At.rename_inv hAt
  cases P₀ with
  | bnd Y =>
      simp only [Proposition.rename] at hEq
      obtain rfl : X = Y.weaken := by injection hEq
      rw [Shape.weaken_substVar]
  | le _ _ => simp [Proposition.rename] at hEq
  | eq _ _ => simp [Proposition.rename] at hEq
  | has _ => simp [Proposition.rename] at hEq
  | leC _ _ => simp [Proposition.rename] at hEq
  | eqC _ _ => simp [Proposition.rename] at hEq

end

/-! ## Fuel monotonicity and determinism -/

section
variable (σ : Store s)

theorem normalizer_succ : ∀ n : Nat,
    (∀ (e : ShapeCo s) (F : Form s), σ ⊢ e ⇓ˢ[n] F → σ ⊢ e ⇓ˢ[(n + 1)] F) ∧
    (∀ (p : Side s) (F : Form s), sideForm σ n p = some F → sideForm σ (n + 1) p = some F) ∧
    (∀ (m : Morphism s) (Es : Entries s), σ ⊢ m ⇓ₘ[n] Es → σ ⊢ m ⇓ₘ[(n + 1)] Es) ∧
    (∀ (a : Atom s) (V : View s), σ ⊢ a ⇓ᵥ[n] V → σ ⊢ a ⇓ᵥ[(n + 1)] V) ∧
    (∀ (F : Form s) (a : Atom s) (V : View s),
      viewThrough σ n F a = some V → viewThrough σ (n + 1) F a = some V) ∧
    (∀ (x : BVar s .var) (h : Has s) (p : BVar s .var × Label),
      σ ⊢ x ; h ⇓ₕ[n] p → σ ⊢ x ; h ⇓ₕ[(n + 1)] p) ∧
    (∀ (a : Atom s) (p : Atom s × Form s), σ ⊢ a ⇓ᶜ[n] p → σ ⊢ a ⇓ᶜ[(n + 1)] p) ∧
    (∀ (a : Atom s) (C : Form s) (V : View s) (E : Entry s) (P : PropForm s),
      Entry.at σ n a C V E = some P → Entry.at σ (n + 1) a C V E = some P) ∧
    (∀ (a : Atom s) (C : Form s) (V : View s) (Es : Entries s) (V' : View s),
      entriesAt σ n a C V Es = some V' → entriesAt σ (n + 1) a C V Es = some V') ∧
    (∀ (d : LeCo s) (F : Form s), σ ⊢ d ⇓[n] F → σ ⊢ d ⇓[(n + 1)] F)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h; rw [hnfShape] at h; cases h
      · intro p F h; rw [sideForm] at h; cases h
      · intro m Es h; rw [entries] at h; cases h
      · intro a V h; rw [view] at h; cases h
      · intro F a V h; rw [viewThrough] at h; cases h
      · intro x hh p h; rw [hasView] at h; cases h
      · intro a p h; rw [closedAtomForm] at h; cases h
      · intro a C V E P h; rw [Entry.at] at h; cases h
      · intro a C V Es V' h; rw [entriesAt] at h; cases h
      · intro d F h; rw [hnf] at h; cases h
  | n + 1 => by
      obtain ⟨ih1, ih0, ih2, ih3, ih4, ih5, ih6, ih7, ih8, ihL⟩ := normalizer_succ n
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h
        cases e with
        | refl T => rw [hnfShape] at h; rw [hnfShape]; exact h
        | top T => rw [hnfShape] at h; rw [hnfShape]; exact h
        | bot T => rw [hnfShape] at h; rw [hnfShape]; exact h
        | eqToLe φ => rw [hnfShape] at h; rw [hnfShape]; exact h
        | pi d c => rw [hnfShape] at h; rw [hnfShape]; exact h
        | boxed d => rw [hnfShape] at h; rw [hnfShape]; exact h
        | bound Tel i => rw [hnfShape] at h; rw [hnfShape]; exact h
        | intoBnd e =>
            cases he : hnfShape σ n e with
            | none => simp [hnfShape, he] at h
            | some F₁ => simpa [hnfShape, he, ih1 e F₁ he] using h
        | obj Tel m =>
            cases hm : entries σ n m with
            | none => simp [hnfShape, hm] at h
            | some Es => simpa [hnfShape, hm, ih2 m Es hm] using h
        | pair Tel₁ Tel₂ e f =>
            cases he : hnfShape σ n e with
            | none => simp [hnfShape, he] at h
            | some F₁ =>
                cases hf : hnfShape σ n f with
                | none => simp [hnfShape, he, hf] at h
                | some G => simpa [hnfShape, he, hf, ih1 e F₁ he, ih1 f G hf] using h
        | trans e f =>
            cases he : hnfShape σ n e with
            | none => simp [hnfShape, he] at h
            | some F₁ =>
                cases hf : hnfShape σ n f with
                | none => simp [hnfShape, he, hf] at h
                | some G => simpa [hnfShape, he, hf, ih1 e F₁ he, ih1 f G hf] using h
        | member a e i =>
            cases he : hnfShape σ n e with
            | none => simp [hnfShape, he] at h
            | some F₁ =>
                cases hv : viewThrough σ n F₁ a with
                | none => simp [hnfShape, he, hv] at h
                | some V => simpa [hnfShape, he, hv, ih1 e F₁ he, ih4 F₁ a V hv] using h
      · intro p F h
        cases p with
        | none => rw [sideForm] at h; rw [sideForm]; exact h
        | some e =>
            rw [sideForm] at h; rw [sideForm]
            exact ih1 e F h
      · intro m Es h
        cases m with
        | nil => rw [entries] at h; rw [entries]; exact h
        | le m pre hh post =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ =>
                cases hpre : sideForm σ n pre with
                | none => simp [entries, hm, hpre] at h
                | some F =>
                    cases hpost : sideForm σ n post with
                    | none => simp [entries, hm, hpre, hpost] at h
                    | some G =>
                        simpa [entries, hm, hpre, hpost, ih2 m Es₀ hm, ih0 pre F hpre,
                          ih0 post G hpost] using h
        | eq m j b =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | has m j =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | bnd m e =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ =>
                cases he : hnfShape σ n e with
                | none => simp [entries, hm, he] at h
                | some F => simpa [entries, hm, he, ih2 m Es₀ hm, ih1 e F he] using h
        | leC m pre hh post =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | eqC m j b =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
      · intro a V h
        cases a with
        | var x => rw [view] at h; rw [view]; exact h
        | cast a e =>
            cases he : hnf σ n e with
            | none => simp [view, he] at h
            | some F => simp [view, ihL e F he, ih4 F a V (by simpa [view, he] using h)]
        | foldSelf Tel a => simp only [view] at h ⊢; exact ih3 a V h
        | unfoldSelf a => simp only [view] at h ⊢; exact ih3 a V h
        | recap a f => simp only [view] at h ⊢; exact ih3 a V h
        | both Tel₁ Tel₂ a b =>
            cases ha : view σ n a with
            | none => simp [view, ha] at h
            | some V₁ =>
                cases hb : view σ n b with
                | none => simp [view, ha, hb] at h
                | some V₂ => simpa [view, ha, hb, ih3 a V₁ ha, ih3 b V₂ hb] using h
      · intro F a V h
        cases F with
        | id => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | eqv φ => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | obj Es =>
            cases hv : view σ n a with
            | none => simp [viewThrough, hv] at h
            | some V₀ =>
                cases hc : closedAtomForm σ n a with
                | none => simp [viewThrough, hv, hc] at h
                | some p =>
                    obtain ⟨a₀, C₀⟩ := p
                    have h' : entriesAt σ n a C₀ V₀ Es = some V := by
                      simpa [viewThrough, hv, hc] using h
                    simpa [viewThrough, ih3 a V₀ hv, ih6 a _ hc] using ih8 a C₀ V₀ Es V h'
        | into Es =>
            cases hv : view σ n a with
            | none => simp [viewThrough, hv] at h
            | some V₀ =>
                cases hc : closedAtomForm σ n a with
                | none => simp [viewThrough, hv, hc] at h
                | some p =>
                    obtain ⟨a₀, C₀⟩ := p
                    have h' : entriesAt σ n a C₀ V₀ Es = some V := by
                      simpa [viewThrough, hv, hc] using h
                    simpa [viewThrough, ih3 a V₀ hv, ih6 a _ hc] using ih8 a C₀ V₀ Es V h'
        | bnd i F =>
            cases hv : view σ n a with
            | none => simp [viewThrough, hv] at h
            | some V₀ =>
                cases hg : V₀.get? i with
                | none => simp [viewThrough, hv, hg] at h
                | some P =>
                    cases hb : P.bndForm? with
                    | none => simp [viewThrough, hv, hg, hb] at h
                    | some G =>
                        cases hcm : G.combine F with
                        | none => simp [viewThrough, hv, hg, hb, hcm] at h
                        | some H =>
                            have h' : viewThrough σ n H (.var a.root) = some V := by
                              simpa [viewThrough, hv, hg, hb, hcm] using h
                            simpa [viewThrough, ih3 a V₀ hv, hg, hb, hcm] using
                              ih4 H (.var a.root) V h'
        | pi d c => rw [viewThrough] at h; rw [viewThrough]; exact h
        | boxed d => rw [viewThrough] at h; rw [viewThrough]; exact h
        | top => rw [viewThrough] at h; rw [viewThrough]; exact h
        | bot => rw [viewThrough] at h; rw [viewThrough]; exact h
      · intro x hh p hp
        cases hh with
        | field ℓ => rw [hasView] at hp; rw [hasView]; exact hp
        | member a e i =>
            cases he : hnfShape σ n e with
            | none => simp [hasView, he] at hp
            | some F =>
                cases hv : viewThrough σ n F a with
                | none => simp [hasView, he, hv] at hp
                | some V => simpa [hasView, he, hv, ih1 e F he, ih4 F a V hv] using hp
      · intro a p h
        cases a with
        | var x => rw [closedAtomForm] at h; rw [closedAtomForm]; exact h
        | cast a e =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q =>
                cases he : hnf σ n e with
                | none => simp [closedAtomForm, hc, he] at h
                | some G =>
                    simpa [closedAtomForm, hc, he, ih6 a q hc, ihL e G he] using h
        | foldSelf Tel a =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q => simpa [closedAtomForm, hc, ih6 a q hc] using h
        | unfoldSelf a =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q => simpa [closedAtomForm, hc, ih6 a q hc] using h
        | recap a f =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q => simpa [closedAtomForm, hc, ih6 a q hc] using h
        | both Tel₁ Tel₂ a b =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q =>
                cases hd : closedAtomForm σ n b with
                | none => simp [closedAtomForm, hc, hd] at h
                | some q' =>
                    simpa [closedAtomForm, hc, hd, ih6 a q hc, ih6 b q' hd] using h
      · intro a C V E P h
        cases E with
        | le pre hh post => simp only [Entry.at] at h ⊢; exact h
        | eq j b => simp only [Entry.at] at h ⊢; exact h
        | has j => simp only [Entry.at] at h ⊢; exact h
        | leC pre hh post => simp only [Entry.at] at h ⊢; exact h
        | eqC j b => simp only [Entry.at] at h ⊢; exact h
        | bnd G => simp only [Entry.at] at h ⊢; exact h
        | thru H E =>
            cases hv : viewThrough σ n H a with
            | none => simp [Entry.at, hv] at h
            | some V₁ =>
                cases hcm : C.combine H with
                | none => simp [Entry.at, hv, hcm] at h
                | some C₁ =>
                    have h' : Entry.at σ n a C₁ V₁ E = some P := by
                      simpa [Entry.at, hv, hcm] using h
                    simpa [Entry.at, ih4 H a V₁ hv, hcm] using ih7 a C₁ V₁ E P h'
      · intro a C V Es V' h
        cases Es with
        | nil => simp only [entriesAt] at h ⊢; exact h
        | cons Es₀ E =>
            cases he : entriesAt σ n a C V Es₀ with
            | none => simp [entriesAt, he] at h
            | some V₀ =>
                cases hE : Entry.at σ n a C V E with
                | none => simp [entriesAt, he, hE] at h
                | some P =>
                    simpa [entriesAt, he, hE, ih8 a C V Es₀ V₀ he,
                      ih7 a C V E P hE] using h
      · intro d F h
        cases d with
        | capt e f => rw [hnf_capt] at h ⊢; exact ih1 e F h

variable {σ}

/-- Fuel monotonicity of the head form of a shape inclusion. -/
theorem hnfShape_le {n n' : Nat} {e : ShapeCo s} {F : Form s} (h : n ≤ n')
    (hF : σ ⊢ e ⇓ˢ[n] F) : σ ⊢ e ⇓ˢ[n'] F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).1 e F ih

theorem hnf_le {n n' : Nat} {e : LeCo s} {F : Form s} (h : n ≤ n') (hF : σ ⊢ e ⇓[n] F) :
    σ ⊢ e ⇓[n'] F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2 e F ih

theorem sideForm_le {n n' : Nat} {p : Side s} {F : Form s} (h : n ≤ n')
    (hF : sideForm σ n p = some F) : sideForm σ n' p = some F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).2.1 p F ih

theorem entries_le {n n' : Nat} {m : Morphism s} {Es : Entries s} (h : n ≤ n')
    (hE : σ ⊢ m ⇓ₘ[n] Es) : σ ⊢ m ⇓ₘ[n'] Es := by
  induction h with
  | refl => exact hE
  | step _ ih => exact (normalizer_succ σ _).2.2.1 m Es ih

theorem view_le {n n' : Nat} {a : Atom s} {V : View s} (h : n ≤ n') (hV : σ ⊢ a ⇓ᵥ[n] V) :
    σ ⊢ a ⇓ᵥ[n'] V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.1 a V ih

theorem viewThrough_le {n n' : Nat} {F : Form s} {a : Atom s} {V : View s} (h : n ≤ n')
    (hV : viewThrough σ n F a = some V) : viewThrough σ n' F a = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.1 F a V ih

theorem hasView_le {n n' : Nat} {x : BVar s .var} {hh : Has s} {p : BVar s .var × Label}
    (h : n ≤ n') (hp : σ ⊢ x ; hh ⇓ₕ[n] p) : σ ⊢ x ; hh ⇓ₕ[n'] p := by
  induction h with
  | refl => exact hp
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.1 x hh p ih

theorem closedAtomForm_succ (n : Nat) (a : Atom s) (r : Atom s × Form s)
    (h : σ ⊢ a ⇓ᶜ[n] r) : σ ⊢ a ⇓ᶜ[(n + 1)] r :=
  (normalizer_succ σ n).2.2.2.2.2.2.1 a r h

theorem entryAt_le {n n' : Nat} {a : Atom s} {C : Form s} {V : View s} {E : Entry s}
    {P : PropForm s} (h : n ≤ n') (hP : Entry.at σ n a C V E = some P) :
    Entry.at σ n' a C V E = some P := by
  induction h with
  | refl => exact hP
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.1 a C V E _ ih

theorem entriesAt_le {n n' : Nat} {a : Atom s} {C : Form s} {V : View s} {Es : Entries s}
    {V' : View s} (h : n ≤ n') (hV : entriesAt σ n a C V Es = some V') :
    entriesAt σ n' a C V Es = some V' := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.1 a C V Es V' ih

theorem closedAtomForm_le {n n' : Nat} {a : Atom s} {r : Atom s × Form s} (h : n ≤ n')
    (hr : σ ⊢ a ⇓ᶜ[n] r) : σ ⊢ a ⇓ᶜ[n'] r := by
  induction h with
  | refl => exact hr
  | step _ ih => exact closedAtomForm_succ _ a r ih

/-! ## Determinism -/

theorem hnf_det {n₁ n₂ : Nat} {e : LeCo s} {F₁ F₂ : Form s}
    (h₁ : σ ⊢ e ⇓[n₁] F₁) (h₂ : σ ⊢ e ⇓[n₂] F₂) : F₁ = F₂ :=
  Option.some.inj ((hnf_le (Nat.le_max_left n₁ n₂) h₁).symm.trans (hnf_le (Nat.le_max_right n₁ n₂) h₂))

theorem hnfShape_det {n₁ n₂ : Nat} {e : ShapeCo s} {F₁ F₂ : Form s}
    (h₁ : σ ⊢ e ⇓ˢ[n₁] F₁) (h₂ : σ ⊢ e ⇓ˢ[n₂] F₂) : F₁ = F₂ :=
  Option.some.inj ((hnfShape_le (Nat.le_max_left n₁ n₂) h₁).symm.trans
    (hnfShape_le (Nat.le_max_right n₁ n₂) h₂))

theorem view_det {n₁ n₂ : Nat} {a : Atom s} {V₁ V₂ : View s}
    (h₁ : σ ⊢ a ⇓ᵥ[n₁] V₁) (h₂ : σ ⊢ a ⇓ᵥ[n₂] V₂) : V₁ = V₂ :=
  Option.some.inj ((view_le (Nat.le_max_left n₁ n₂) h₁).symm.trans (view_le (Nat.le_max_right n₁ n₂) h₂))

theorem closedAtomForm_det {n₁ n₂ : Nat} {a : Atom s} {r₁ r₂ : Atom s × Form s}
    (h₁ : σ ⊢ a ⇓ᶜ[n₁] r₁) (h₂ : σ ⊢ a ⇓ᶜ[n₂] r₂) : r₁ = r₂ :=
  Option.some.inj ((closedAtomForm_le (Nat.le_max_left n₁ n₂) h₁).symm.trans
    (closedAtomForm_le (Nat.le_max_right n₁ n₂) h₂))

end

section
variable {σ : Store s} {Γ : Ctx s} {r : BVar s .var}

/-! ## The view of an atom through a typed form -/

/-- The view of the literal at a root is typed at the root's type. -/
def RootViewTyped (Γ : Ctx s) (σ : Store s) (r : BVar s .var) : Prop :=
  (∀ Tel : Telescope (s,x), Γ.resolve ((Γ.lookupTy r).shape) = μ Tel →
      Γ ⊨[r, σ] ((σ.lookup r).precView r) : Tel) ∧
    Γ.resolve ((Γ.lookupTy r).shape) ≠ ⊥

theorem Shape.unfoldAt_eq_bot {r : BVar s .var} {X : Shape s} (h : X.unfoldAt r = ⊥) : X = ⊥ := by
  cases X <;> simp [Shape.unfoldAt] at h ⊢

theorem Shape.unfoldAt_eq_obj {r : BVar s .var} {X : Shape s} {Tel : Telescope (s,x)}
    (h : X.unfoldAt r = μ Tel) : ∃ Tel₀, X = μ Tel₀ ∧ (Tel₀⟦r⟧)↑ = Tel := by
  cases X with
  | obj Tel₀ => exact ⟨Tel₀, rfl, Shape.obj.inj h⟩
  | bot => simp [Shape.unfoldAt] at h
  | sel _ _ => simp [Shape.unfoldAt] at h
  | pi _ _ => simp [Shape.unfoldAt] at h
  | box _ => simp [Shape.unfoldAt] at h

/-- The view of the root variable, at the shapes opened at the root. -/
theorem RootViewTyped.opened (hroot : RootViewTyped Γ σ r) :
    (∀ Tel : Telescope (s,x), Γ.resolveAt? (some r) ((Γ.lookupTy r).shape) = μ Tel →
        Γ ⊨[r, σ] ((σ.lookup r).precView r) : Tel) ∧
      Γ.resolveAt? (some r) ((Γ.lookupTy r).shape) ≠ ⊥ := by
  refine ⟨fun Tel h => ?_, fun h => hroot.2 (Shape.unfoldAt_eq_bot h)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Shape.unfoldAt_eq_obj h
  exact ViewTyped_unfold (hroot.1 Tel₀ h₀)

/-! ## Applying typed entries to the view of an atom -/

/-- Instantiating one typed entry at the typed view of the object type the
entry reads. -/
theorem EntryTyped.at_typed {r : BVar s .var} {M : Shape s} {TelM : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} {C : Form s} {V : View s} (a : Atom s)
    (hC : Γ ⊨[r] C : (Γ.lookupTy r).shape ≤ M) (hM : Γ.resolveAt? (some r) M = μ TelM)
    (hV : Γ ⊨[r, σ] V : TelM) (hE : EntryTyped Γ (some r) TelM E P) :
    ∃ m Q, Entry.at σ m a C V E = some Q ∧
      ∀ {V₀ : View s} {Tel₀ : Telescope (s,x)},
        Γ ⊨[r, σ] V₀ : Tel₀ → Γ ⊨[r, σ] V₀ ▹ Q : Tel₀ ▹ P := by
  have hop : Γ.resolveAt? (some r) (μ TelM) = μ TelM := Ctx.resolveAt?_obj_self hM
  have hCT : Γ ⊨[r] C : (Γ.lookupTy r).shape ≤ μ TelM := hC.tgtRes (hM.trans hop.symm)
  match hE with
  | .le (pre := pre) (post := post) hh hpre hpost =>
      have hpre' := hpre.inst r
      have hpost' := hpost.inst r
      cases hh with
      | le hAt =>
          obtain ⟨G, hG, hGt⟩ := hV.le_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' hGt
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [Entry.at, Hole.index, hG.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
      | eq hAt =>
          obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE')
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [Entry.at, Hole.index, hq.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
      | eqSym hAt =>
          obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE'.symm)
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [Entry.at, Hole.index, hq.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
  | .eq hAt =>
      obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
      exact ⟨1, .eq, by simp [Entry.at, hq.get?], fun hV₀ => .eq hV₀ hE'⟩
  | .eqSym hAt =>
      obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
      exact ⟨1, .eq, by simp [Entry.at, hq.get?], fun hV₀ => .eq hV₀ hE'.symm⟩
  | .has (ℓ := ℓ) hAt =>
      obtain ⟨hq, hHF⟩ := hV.has_entry hAt
      exact ⟨1, .has r ℓ, by simp [Entry.at, hq.get?], fun hV₀ => .has hV₀ hHF⟩
  | .bnd (j := k) hG =>
      have hG' : Γ ⊨[r] (Form.bnd k .id) : M ≤ _ := hG.srcRes (hM.trans hop.symm)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG'
      exact ⟨1, .bnd H, by simp [Entry.at, hH],
        fun hV₀ => .bnd hV₀ (by rwa [Shape.weaken_substVar])⟩
  | .bndId (X := X) (j := k) hAt =>
      have hX : X = (X⟦r⟧)↑ := Telescope.opened_bnd (Ctx.resolveAt?_opened hM) hAt
      have hAt' : TelM ∋ (k ↦ ⊑ ((X⟦r⟧)↑)) := by rw [← hX]; exact hAt
      have hBnd : Γ ⊨[r] (Form.bnd k .id) : M ≤ X⟦r⟧ := .bnd hM hAt' (.id rfl)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hBnd
      exact ⟨1, .bnd H, by simp [Entry.at, hH], fun hV₀ => .bnd hV₀ hHt⟩
  -- A capture slot carries no data: its typedness is the inclusion of roots
  -- at the root, put together by transitivity from the two side chains and
  -- the slot the hole names.
  | .leC hh hpre hpost =>
      have hpre' := hpre.inst r
      have hpost' := hpost.inst r
      cases hh with
      | leC hAt =>
          obtain ⟨hq, hle⟩ := hV.leC_entry hAt
          exact ⟨1, .leC, by simp [Entry.at, HoleC.index, hq.get?],
            fun hV₀ => .leC hV₀ (hpre'.trans (hle.trans hpost'))⟩
      | eqC hAt =>
          obtain ⟨hq, heq⟩ := hV.eqC_entry hAt
          exact ⟨1, .leC, by simp [Entry.at, HoleC.index, hq.get?],
            fun hV₀ => .leC hV₀ (hpre'.trans (heq.le.trans hpost'))⟩
      | eqSymC hAt =>
          obtain ⟨hq, heq⟩ := hV.eqC_entry hAt
          exact ⟨1, .leC, by simp [Entry.at, HoleC.index, hq.get?],
            fun hV₀ => .leC hV₀ (hpre'.trans (heq.symm.le.trans hpost'))⟩
  | .eqC hAt =>
      obtain ⟨hq, heq⟩ := hV.eqC_entry hAt
      exact ⟨1, .eqC, by simp [Entry.at, hq.get?], fun hV₀ => .eqC hV₀ heq⟩
  | .eqSymC hAt =>
      obtain ⟨hq, heq⟩ := hV.eqC_entry hAt
      exact ⟨1, .eqC, by simp [Entry.at, hq.get?], fun hV₀ => .eqC hV₀ heq.symm⟩

/-- Applying typed view-free entries at a root: the view of the source is
consulted only through the routes of the entries, which are sub-forms. -/
theorem entriesAtBnds_typed {r : BVar s .var} {S : Shape s} {C : Form s} {a : Atom s}
    (V : View s) (hC : Γ ⊨[r] C : (Γ.lookupTy r).shape ≤ S) :
    ∀ {Es : Entries s} {Tel : Telescope (s,x)},
      (∀ (H : Form s) (M : Shape s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
        Γ ⊨[r] H : S ≤ M → Γ.resolveAt? (some r) M = μ TelM →
        ∃ m V'', viewThrough σ m H a = some V'' ∧ Γ ⊨[r, σ] V'' : TelM) →
      BndsTyped Γ (some r) S Es Tel →
      ∃ m V', entriesAt σ m a C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel
  | _, _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, hIH, .cons hB' hG => by
      obtain ⟨m, V', hV', hT⟩ :=
        entriesAtBnds_typed V hC (fun H M TelM hlt => hIH H M TelM (by simp; omega)) hB'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Shape.weaken_substVar])⟩
      simp [entriesAt, entriesAt_le (Nat.le_succ m) hV', Entry.at, hH]
  | _, _, hIH, .thru hB' hH hM hE => by
      obtain ⟨m₁, V₁, hV₁, hT₁⟩ :=
        entriesAtBnds_typed V hC (fun H' M' TelM' hlt => hIH H' M' TelM' (by simp; omega)) hB'
      obtain ⟨m₂, V₂, hV₂, hT₂⟩ := hIH _ _ _ (by simp; omega) hH hM
      obtain ⟨C', hC', hC'T⟩ := Form.combine_typed hC hH
      obtain ⟨m₃, Q, hQ, hQt⟩ := EntryTyped.at_typed a hC'T hM hT₂ hE
      refine ⟨max m₁ (max m₂ m₃) + 2, V₁ ▹ Q, ?_, hQt hT₁⟩
      have h₁ := entriesAt_le (σ := σ) (a := a) (C := C) (V := V)
        (Nat.le_trans (Nat.le_max_left m₁ (max m₂ m₃)) (Nat.le_succ _)) hV₁
      have h₂ := viewThrough_le (σ := σ)
        (Nat.le_trans (Nat.le_max_left m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hV₂
      have h₃ := entryAt_le (σ := σ) (a := a)
        (Nat.le_trans (Nat.le_max_right m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hQ
      simp [entriesAt, h₁, Entry.at, h₂, hC', h₃]

/-- Applying typed entries to a typed view at a root. -/
theorem entriesAt_typed {r : BVar s .var} {Tel₁ : Telescope (s,x)}
    {V : View s} {C : Form s} {S : Shape s} (a : Atom s)
    (hC : Γ ⊨[r] C : (Γ.lookupTy r).shape ≤ S) (hS : Γ.resolveAt r S = μ Tel₁)
    (hV : Γ ⊨[r, σ] V : Tel₁) :
    ∀ {Es : Entries s} {Tel₂ : Telescope (s,x)}, EntriesTyped Γ (some r) Tel₁ Es Tel₂ →
      ∃ m V', entriesAt σ m a C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂
  | _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, .le hEs' hh hpre hpost => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.le hh hpre hpost)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eq hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.eq hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eqSym hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.eqSym hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .has hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.has hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .bnd hEs' hG => by
      have hSA : Γ.resolveAt? (some r) S = μ Tel₁ := hS
      have hop : Γ.resolveAt? (some r) (μ Tel₁) = μ Tel₁ := Ctx.resolveAt?_obj_self hSA
      have hCT : Γ ⊨[r] C : (Γ.lookupTy r).shape ≤ μ Tel₁ := hC.tgtRes (hSA.trans hop.symm)
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hCT hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Shape.weaken_substVar])⟩
      simp [entriesAt, entriesAt_le (Nat.le_succ m) hV', Entry.at, hH]
  | _, _, .bndId (X := X) (j := j) hEs' hAt => by
      have hSA : Γ.resolveAt? (some r) S = μ Tel₁ := hS
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.bndId hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .leC hEs' hh hpre hpost => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.leC hh hpre hpost)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eqC hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.eqC hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eqSymC hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hC hS hV (.eqSymC hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]

/-- The view of the root variable through a typed form. -/
theorem viewThroughVar_typed {r : BVar s .var} (hroot : RootViewTyped Γ σ r) :
    ∀ (k : Nat) (F : Form s) (T : Shape s), sizeOf F ≤ k → Γ ⊨[r] F : (Γ.lookupTy r).shape ≤ T →
      ∃ m V', viewThrough σ m F (.var r) = some V' ∧
        (∀ Tel : Telescope (s,x), Γ.resolveAt? (some r) T = μ Tel → Γ ⊨[r, σ] V' : Tel) ∧
        Γ.resolveAt? (some r) T ≠ ⊥
  | 0, F, _, hk, _ => by cases F <;> simp at hk
  | k + 1, F, T, hk, hF => by
    obtain ⟨hrv, hrb⟩ := hroot.opened
    have hview : ∀ n : Nat, view σ (n + 1) (.var r) = some ((σ.lookup r).precView r) := fun _ => rfl
    have hchain : ∀ n : Nat, closedAtomForm σ (n + 1) (.var r) = some (.var r, .id) := fun _ => rfl
    have hCid : Γ ⊨[r] (Form.id) : (Γ.lookupTy r).shape ≤ (Γ.lookupTy r).shape := .id rfl
    match hF with
    | .bot hS => exact absurd hS hrb
    | .top hT =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h
          obtain rfl := Shape.obj.inj (by simpa using h : (μ .nil : Shape s) = μ Tel)
          exact .nil
        · rw [hT]; simp
    | .id hres =>
        exact ⟨2, _, by simp [viewThrough, hview],
          fun Tel h => hrv Tel (hres.trans h), by rw [← hres]; exact hrb⟩
    | .eqv hres =>
        exact ⟨2, _, by simp [viewThrough, hview],
          fun Tel h => hrv Tel (hres.trans h), by rw [← hres]; exact hrb⟩
    | .pi _ hT _ _ =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h; exact absurd h (by simp)
        · rw [hT]; simp
    | .boxed _ hT _ =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h; exact absurd h (by simp)
        · rw [hT]; simp
    | .obj hS hT hEs =>
        obtain ⟨m, V', hV', hT'⟩ := entriesAt_typed (.var r) hCid hS (hrv _ hS) hEs
        refine ⟨m + 2, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, hview, hchain, entriesAt_le (Nat.le_succ m) hV']
        · rw [hT] at h; obtain rfl := Shape.obj.inj h; exact hT'
        · rw [hT]; simp
    | .into (Es := Es) hT hB =>
        have hIH : ∀ (H : Form s) (M : Shape s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
            Γ ⊨[r] H : (Γ.lookupTy r).shape ≤ M → Γ.resolveAt? (some r) M = μ TelM →
            ∃ m V'', viewThrough σ m H (.var r) = some V'' ∧ Γ ⊨[r, σ] V'' : TelM := by
          intro H M TelM hlt hH hM
          have hsz : sizeOf H ≤ k := by simp at hk; omega
          obtain ⟨m, V'', hV'', hVt'', _⟩ := viewThroughVar_typed hroot k H M hsz hH
          exact ⟨m, V'', hV'', hVt'' _ hM⟩
        obtain ⟨m, V', hV', hT'⟩ :=
          entriesAtBnds_typed ((σ.lookup r).precView r) hCid hIH hB
        refine ⟨m + 2, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, hview, hchain, entriesAt_le (Nat.le_succ m) hV']
        · rw [hT] at h; obtain rfl := Shape.obj.inj h; exact hT'
        · rw [hT]; simp
    | .bnd hS hAt _ =>
        obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
        exact absurd hG (Value.precView_noBnd r _ _ _)

/-- Applying a typed form to the typed view of an atom yields the typed view
of the target. -/
theorem viewThrough_typed_aux {a a' : Atom s} {V : View s} {C : Form s}
    {n : Nat} (hroot : RootViewTyped Γ σ a.root)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hC : σ ⊢ a ⇓ᶜ[n] (a', C)) :
    ∀ (k : Nat) (F : Form s) (S T : Shape s), sizeOf F ≤ k →
      Γ ⊨[a.root] F : S ≤ T →
      Γ ⊨[a.root] C : (Γ.lookupTy a.root).shape ≤ S →
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S = μ Tel → Γ ⊨[a.root, σ] V : Tel) →
      Γ.resolveAt? (some a.root) S ≠ ⊥ →
      ∃ m V', viewThrough σ m F a = some V' ∧
        (∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) T = μ Tel → Γ ⊨[a.root, σ] V' : Tel) ∧
        Γ.resolveAt? (some a.root) T ≠ ⊥
  | 0, F, _, _, hk, _, _, _, _ => by cases F <;> simp at hk
  | k + 1, F, S, T, hk, hF, hCt, hVt, hnb => by
    match hF with
    | .bot hS => exact absurd hS hnb
    | .top hT =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h
          obtain rfl := Shape.obj.inj (by simpa using h : (μ .nil : Shape s) = μ Tel)
          exact .nil
        · rw [hT]; simp
    | .id hres =>
        exact ⟨n + 1, V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h),
          by rw [← hres]; exact hnb⟩
    | .eqv hres =>
        exact ⟨n + 1, V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h),
          by rw [← hres]; exact hnb⟩
    | .pi _ hT _ _ =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h; exact absurd h (by simp)
        · rw [hT]; simp
    | .boxed _ hT _ =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h; exact absurd h (by simp)
        · rw [hT]; simp
    | .obj hS hT hEs =>
        obtain ⟨m, V', hV', hT'⟩ := entriesAt_typed a hCt hS (hVt _ hS) hEs
        refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, view_le (Nat.le_max_left n m) hV,
            closedAtomForm_le (Nat.le_max_left n m) hC,
            entriesAt_le (Nat.le_max_right n m) hV']
        · rw [hT] at h; obtain rfl := Shape.obj.inj h; exact hT'
        · rw [hT]; simp
    | .into (Es := Es) hT hB =>
        have hIH : ∀ (H : Form s) (M : Shape s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
            Γ ⊨[a.root] H : S ≤ M → Γ.resolveAt? (some a.root) M = μ TelM →
            ∃ m V'', viewThrough σ m H a = some V'' ∧ Γ ⊨[a.root, σ] V'' : TelM := by
          intro H M TelM hlt hH hM
          have hsz : sizeOf H ≤ k := by simp at hk; omega
          obtain ⟨m, V'', hV'', hVt'', _⟩ :=
            viewThrough_typed_aux hroot hV hC k H S M hsz hH hCt hVt hnb
          exact ⟨m, V'', hV'', hVt'' _ hM⟩
        obtain ⟨m, V', hV', hT'⟩ := entriesAtBnds_typed V hCt hIH hB
        refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, view_le (Nat.le_max_left n m) hV,
            closedAtomForm_le (Nat.le_max_left n m) hC,
            entriesAt_le (Nat.le_max_right n m) hV']
        · rw [hT] at h; obtain rfl := Shape.obj.inj h; exact hT'
        · rw [hT]; simp
    | .bnd hS hAt hF' =>
        obtain ⟨G, hG, hGt⟩ := (hVt _ hS).bnd_entry hAt
        rw [Shape.weaken_substVar] at hGt
        obtain ⟨H, hH, hHt⟩ := Form.combine_typed hGt hF'
        obtain ⟨m, V', hV', hVt', hnb'⟩ := viewThroughVar_typed hroot _ H _ (Nat.le_refl _) hHt
        refine ⟨max n m + 1, V', ?_, hVt', hnb'⟩
        simpa [viewThrough, view_le (Nat.le_max_left n m) hV, hG.get?, PropForm.bndForm?, hH]
          using viewThrough_le (Nat.le_max_right n m) hV'

theorem viewThrough_typed {F : Form s} {S T : Shape s} {a a' : Atom s} {V : View s} {C : Form s}
    {n : Nat} (hroot : RootViewTyped Γ σ a.root)
    (hF : Γ ⊨[a.root] F : S ≤ T)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hC : σ ⊢ a ⇓ᶜ[n] (a', C))
    (hCt : Γ ⊨[a.root] C : (Γ.lookupTy a.root).shape ≤ S)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S = μ Tel → Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some a.root) S ≠ ⊥) :
    ∃ m V', viewThrough σ m F a = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) T = μ Tel → Γ ⊨[a.root, σ] V' : Tel) ∧
      Γ.resolveAt? (some a.root) T ≠ ⊥ :=
  viewThrough_typed_aux hroot hV hC (sizeOf F) F S T (Nat.le_refl _) hF hCt hVt hnb

end

end FCdot

end CapturesCC
