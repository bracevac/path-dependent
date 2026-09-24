import Coercions.Paths.FCdot.FormTyping
import Coercions.Paths.FCdot.Preservation
import Coercions.Paths.FCdot.FieldCo

namespace Paths

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
  fields := by
    intro y Fs hFs
    cases y with
    | here => simp at hFs
    | there z =>
        rw [Ctx.lookupFields_there] at hFs
        simpa using hFs
  lookupB := by
    refine Ctx.lookupBlock_rename ?_
    intro y B' hB'
    cases y with
    | here => simp at hB'
    | there z =>
        rw [Ctx.blockAt_there] at hB'
        obtain ⟨B₀, hB₀, rfl⟩ := Option.map_eq_some_iff.mp hB'
        simp only [Subst.selfCast_root, Rename.id_var, Ctx.blockAt_there, hB₀,
          Option.map_some, Block.rename_id]
  nodeB := by
    refine Ctx.nodeBlock_rename ?_
    intro y B' hB'
    cases y with
    | here => simp at hB'
    | there z =>
        rw [Ctx.blockAt_there] at hB'
        obtain ⟨B₀, hB₀, rfl⟩ := Option.map_eq_some_iff.mp hB'
        simp only [Subst.selfCast_root, Rename.id_var, Ctx.blockAt_there, hB₀,
          Option.map_some, Block.rename_id]

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Typedness depends on an endpoint only through its shape -/

mutual

theorem FormTyped.srcRes {s : Sig} {Γ : Ctx s} {ρ : Option (Path s)} {F : Form s}
    {S S' T : Ty s} (h : Γ.resolveAt? ρ S = Γ.resolveAt? ρ S') (hF : FormTyped Γ ρ F S' T) :
    FormTyped Γ ρ F S T := by
  match hF with
  | .bot hS => exact .bot (h.trans hS)
  | .top hT => exact .top hT
  | .id hres => exact .id (h.trans hres)
  | .eqv hres => exact .eqv (h.trans hres)
  | .pi hS hT hd hc => exact .pi (h.trans hS) hT hd hc
  | .obj hS hT hEs => exact .obj (h.trans hS) hT hEs
  | .bnd hS hAt hF' => exact .bnd (h.trans hS) hAt hF'
  | .into hT hB => exact .into hT (BndsTyped.srcRes h hB)

theorem BndsTyped.srcRes {s : Sig} {Γ : Ctx s} {ρ : Option (Path s)} {S S' : Ty s}
    {Es : Entries s} {Tel : Telescope (s,x)}
    (h : Γ.resolveAt? ρ S = Γ.resolveAt? ρ S') (hB : BndsTyped Γ ρ S' Es Tel) :
    BndsTyped Γ ρ S Es Tel := by
  match hB with
  | .nil => exact .nil
  | .cons hB' hF => exact .cons (BndsTyped.srcRes h hB') (FormTyped.srcRes h hF)
  | .thru hB' hH hM hE => exact .thru (BndsTyped.srcRes h hB') (FormTyped.srcRes h hH) hM hE
  | .aliasTo hB' hρ hb => exact .aliasTo (BndsTyped.srcRes h hB') hρ hb

end

theorem FormTyped.tgtRes {s : Sig} {Γ : Ctx s} {ρ : Option (Path s)} {F : Form s}
    {S T T' : Ty s} (h : Γ.resolveAt? ρ T' = Γ.resolveAt? ρ T) (hF : FormTyped Γ ρ F S T') :
    FormTyped Γ ρ F S T := by
  match hF with
  | .bot hS => exact .bot hS
  | .top hT => exact .top (h.symm.trans hT)
  | .id hres => exact .id (hres.trans h)
  | .eqv hres => exact .eqv (hres.trans h)
  | .pi hS hT hd hc => exact .pi hS (h.symm.trans hT) hd hc
  | .obj hS hT hEs => exact .obj hS (h.symm.trans hT) hEs
  | .bnd hS hAt hF' => exact .bnd hS hAt (FormTyped.tgtRes h hF')
  | .into hT hB => exact .into (h.symm.trans hT) hB

/-- A form stays typed when its source is replaced by one of the same shape
in its mode.  Every clause of `FormTyped` reads its source through
`Γ.resolveAt? ρ`, apart from `into`, whose `BndsTyped` passes the source on to
`FormTyped`.  This is `FormTyped.srcRes` read forwards.  T1's `sel` case uses
it to move the chain's source to `Γ.nodeTy (p.a)` by the third conjunct of
`Store.Typed.fieldCo` (P1.8). -/
theorem FormTyped.congr_src {s : Sig} {Γ : Ctx s} {ρ : Option (Path s)} {F : Form s}
    {S S' T : Ty s} (h : Γ.resolveAt? ρ S = Γ.resolveAt? ρ S') (hF : FormTyped Γ ρ F S T) :
    FormTyped Γ ρ F S' T :=
  FormTyped.srcRes h.symm hF

theorem ChainTyped.srcRes {r : Path s} {F : Form s} {S S' T : Ty s}
    (h : Γ.resolveAt r S = Γ.resolveAt r S') (hF : Γ ⊨[r] F : S' ≤ T) : Γ ⊨[r] F : S ≤ T :=
  FormTyped.srcRes (by simpa using h) hF

theorem ChainTyped.tgtRes {r : Path s} {F : Form s} {S T T' : Ty s}
    (h : Γ.resolveAt r T' = Γ.resolveAt r T) (hF : Γ ⊨[r] F : S ≤ T') : Γ ⊨[r] F : S ≤ T :=
  FormTyped.tgtRes (by simpa using h) hF

/-! ## Opening a telescope at a root

Typedness of entries is stable under opening both telescopes at a root: a
closed side stays closed, and holes follow the renaming. -/

theorem Ty.weaken_inj {A B : Ty s} (h : (A.weaken (k := .var)) = B.weaken) : A = B :=
  Ty.rename_inj _ _ _ Rename.succ_injective h

theorem SideTyped.open (r : Path s) {F : Form s} {S X : Ty (s,x)}
    (h : SideTyped Γ F S X) :
    SideTyped Γ F ((S.substPath r)↑) ((X.substPath r)↑) := by
  cases h with
  | id => exact .id
  | closed hF => rw [Ty.weaken_substPath, Ty.weaken_substPath]; exact .closed hF
  | bot hall => rw [Ty.weaken_substPath]; exact .bot hall
  | top hall => rw [Ty.weaken_substPath]; exact .top hall
  | free hall => exact .free hall

theorem Telescope.HoleAt.open (r : Path s) {Tel : Telescope (s,x)} {h : Hole}
    {X Y : Ty (s,x)} (hh : Tel.HoleAt h X Y) :
    ((Tel.substPath r)↑).HoleAt h ((X.substPath r)↑) ((Y.substPath r)↑) := by
  cases hh with
  | le hAt => exact .le ((hAt.substPath r).rename _)
  | eq hAt => exact .eq ((hAt.substPath r).rename _)
  | eqSym hAt => exact .eqSym ((hAt.substPath r).rename _)

/-! ## Plain typedness gives typedness at the shapes opened at any root

The opened shape of an endpoint is a non-name type determined by the plain
shape, and resolution is the identity on it. -/

mutual

theorem FormTyped.atRoot {s : Sig} {Γ : Ctx s} {F : Form s} {S T : Ty s} (r : Path s)
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
  | .bnd (T := T') (Tel := Tel) (i := i) hS hAt hF' =>
      refine .bnd (Ctx.resolveAt_of_resolve r hS) ?_ (FormTyped.atRoot r hF')
      have h1 : Telescope.At (Tel.substPath r) i ((⊑ T'↑ : Proposition (s,x)).substPath r) :=
        hAt.substPath r
      rw [show ((⊑ T'↑ : Proposition (s,x)).substPath r) = ⊑ T' from by
        simp [Proposition.substPath_bnd, Ty.weaken_substPath]] at h1
      exact h1.weaken
  | .into hT hB =>
      exact .into (Ctx.resolveAt_of_resolve r hT) (BndsTyped.atRoot r hB)

theorem EntriesTyped.atRoot {s : Sig} {Γ : Ctx s} (r : Path s)
    {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s} (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) :
    EntriesTyped Γ (some r) ((Tel₁.substPath r)↑) Es ((Tel₂.substPath r)↑) := by
  match h with
  | .nil => exact .nil
  | .le h' hh hpre hpost =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_le,
        Proposition.weaken_le]
      exact .le (EntriesTyped.atRoot r h') (hh.open r) (hpre.open r) (hpost.open r)
  | .eq h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_eq,
        Proposition.weaken_eq]
      exact .eq (EntriesTyped.atRoot r h') ((hAt.substPath r).rename _)
  | .eqSym h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_eq,
        Proposition.weaken_eq]
      exact .eqSym (EntriesTyped.atRoot r h') ((hAt.substPath r).rename _)
  | .has h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_has,
        Proposition.weaken_has]
      exact .has (EntriesTyped.atRoot r h') ((hAt.substPath r).rename _)
  | .hasVal h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_hasVal,
        Proposition.weaken_hasVal]
      exact .hasVal (EntriesTyped.atRoot r h') ((hAt.substPath r).rename _)
  | .hasOfVal h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_has,
        Proposition.weaken_has]
      exact .hasOfVal (EntriesTyped.atRoot r h') ((hAt.substPath r).rename _)
  | .alias h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_alias,
        Proposition.weaken_alias]
      have h1 := (hAt.substPath r).weaken
      simp only [Proposition.substPath_alias, Proposition.weaken_alias] at h1
      exact .alias (EntriesTyped.atRoot r h') h1
  | .bnd (Tel₁ := Tel₁) h' hG =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_bnd,
        Proposition.weaken_bnd, Ty.weaken_substPath]
      refine .bnd (EntriesTyped.atRoot r h') ?_
      refine FormTyped.srcRes ?_ (FormTyped.atRoot r hG)
      simp [Telescope.weaken_substPath]
  | .bndId (X := X) (Tel₁ := Tel₁) (j := j) h' hAt =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_bnd,
        Proposition.weaken_bnd]
      refine .bndId (EntriesTyped.atRoot r h') ?_
      have h1 : Telescope.At (Tel₁.substPath r) j ((⊑ X : Proposition (s,x)).substPath r) :=
        hAt.substPath r
      exact h1.weaken

theorem BndsTyped.atRoot {s : Sig} {Γ : Ctx s} (r : Path s) {S : Ty s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ none S Es Tel) :
    BndsTyped Γ (some r) S Es ((Tel.substPath r)↑) := by
  match h with
  | .nil => exact .nil
  | .cons h' hF =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_bnd,
        Proposition.weaken_bnd, Ty.weaken_substPath]
      exact .cons (BndsTyped.atRoot r h') (FormTyped.atRoot r hF)
  | .thru (M := M) (TelM := TelM) h' hH hM hE =>
      simp only [Telescope.substPath_cons, Telescope.weaken_cons]
      exact .thru (BndsTyped.atRoot r h') (FormTyped.atRoot r hH)
        (Ctx.resolveAt_of_resolve r hM) (EntryTyped.atRoot r hE)

theorem EntryTyped.atRoot {s : Sig} {Γ : Ctx s} (r : Path s) {Tel₁ : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} (h : EntryTyped Γ none Tel₁ E P) :
    EntryTyped Γ (some r) ((Tel₁.substPath r)↑) E ((P.substPath r)↑) := by
  match h with
  | .le hh hpre hpost =>
      simp only [Proposition.substPath_le, Proposition.weaken_le]
      exact .le (hh.open r) (hpre.open r) (hpost.open r)
  | .eq hAt =>
      simp only [Proposition.substPath_eq, Proposition.weaken_eq]
      exact .eq ((hAt.substPath r).rename _)
  | .eqSym hAt =>
      simp only [Proposition.substPath_eq, Proposition.weaken_eq]
      exact .eqSym ((hAt.substPath r).rename _)
  | .has hAt =>
      simp only [Proposition.substPath_has, Proposition.weaken_has]
      exact .has ((hAt.substPath r).rename _)
  | .hasVal hAt =>
      simp only [Proposition.substPath_hasVal, Proposition.weaken_hasVal]
      exact .hasVal ((hAt.substPath r).rename _)
  | .hasOfVal hAt =>
      simp only [Proposition.substPath_has, Proposition.weaken_has]
      exact .hasOfVal ((hAt.substPath r).rename _)
  | .alias hAt =>
      simp only [Proposition.substPath_alias, Proposition.weaken_alias]
      have h1 := (hAt.substPath r).weaken
      simp only [Proposition.substPath_alias, Proposition.weaken_alias] at h1
      exact .alias h1
  | .bnd (Tel₁ := Tel₁) hG =>
      simp only [Proposition.substPath_bnd, Proposition.weaken_bnd, Ty.weaken_substPath]
      refine .bnd (FormTyped.srcRes ?_ (FormTyped.atRoot r hG))
      simp [Telescope.weaken_substPath]
  | .bndId (X := X) (j := j) hAt =>
      simp only [Proposition.substPath_bnd, Proposition.weaken_bnd]
      refine .bndId ?_
      have h1 : Telescope.At (Tel₁.substPath r) j ((⊑ X : Proposition (s,x)).substPath r) :=
        hAt.substPath r
      exact h1.weaken

end

/-- Entries typed plainly are typed at the opened telescopes. -/
theorem EntriesTyped.open (r : Path s) {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) :
    EntriesTyped Γ (some r) ((Tel₁.substPath r)↑) Es ((Tel₂.substPath r)↑) :=
  EntriesTyped.atRoot r h

/-! ## Entries by position -/

theorem EntriesTyped.length {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) : Es.length = Tel₂.length := by
  match h with
  | .nil => rfl
  | .le h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]
  | .eq h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .eqSym h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .has h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .bnd h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .bndId h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .hasVal h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .hasOfVal h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .alias h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .aliasTo h' _ _ => simp [Entries.length, Telescope.length, h'.length]

/-- The entry at an inclusion of the target is a template. -/
theorem EntriesTyped.At_le {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {S T : Ty (s,x)}
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
  | .hasVal hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .hasOfVal hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .alias hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩
  | .aliasTo hEs _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨pre, h', post, X, Y, hE, hh', hpre', hpost'⟩ := hEs.At_le hAt'
          exact ⟨pre, h', post, X, Y, .there hE, hh', hpre', hpost'⟩

/-- The entry at an equality of the target reads a source equality, possibly
flipped. -/
theorem EntriesTyped.At_eq {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {X Y : Ty (s,x)}
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
  | .hasVal hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .hasOfVal hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .alias hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩
  | .aliasTo hEs _ _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨k, b, hE, hk⟩ := hEs.At_eq hAt'; exact ⟨k, b, .there hE, hk⟩

/-- The entry at a presence proposition of the target is a presence entry
pointing at a presence or a stable presence of the source.  The second
disjunct is the `hasOfVal` entry, which reads a stable presence as a
presence; the entry itself is `.has j'` in both. -/
theorem EntriesTyped.At_has {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {ℓ : Label}
    (hAt : Tel₂ ∋ (j ↦ ∋ ℓ)) :
    ∃ j', Es ∋ (j ↦ .has j') ∧ (Tel₁ ∋ (j' ↦ ∋ ℓ) ∨ Tel₁ ∋ (j' ↦ ∋ᵛ ℓ)) := by
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
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, Or.inl hT⟩
      | there hAt' => obtain ⟨j', hj', hT'⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT'⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .hasVal hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .hasOfVal hEs hT =>
      cases hAt with
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, Or.inr hT⟩
      | there hAt' => obtain ⟨j', hj', hT'⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT'⟩
  | .alias hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩
  | .aliasTo hEs _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_has hAt'; exact ⟨j', .there hj', hT⟩

/-- The entry at a stable presence of the target is a stable-presence entry
pointing at a stable presence of the source. -/
theorem EntriesTyped.At_hasVal {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {ℓ : Label}
    (hAt : Tel₂ ∋ (j ↦ ∋ᵛ ℓ)) :
    ∃ j', Es ∋ (j ↦ .hasVal j') ∧ Tel₁ ∋ (j' ↦ ∋ᵛ ℓ) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .hasVal hEs hT =>
      cases hAt with
      | here => exact ⟨_, by rw [← hEs.length]; exact .here, hT⟩
      | there hAt' => obtain ⟨j', hj', hT'⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT'⟩
  | .hasOfVal hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .alias hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩
  | .aliasTo hEs _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨j', hj', hT⟩ := hEs.At_hasVal hAt'; exact ⟨j', .there hj', hT⟩

/-- The entry at an alias of the target either inherits a source alias by
index, or is a constant alias read at the receiver the mode names. -/
theorem EntriesTyped.At_alias {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {q : Path (s,x)}
    (hAt : Tel₂ ∋ (j ↦ ≈ q)) :
    (∃ j', Es ∋ (j ↦ .alias j') ∧ Tel₁ ∋ (j' ↦ ≈ q)) ∨
      (∃ p q₀, ρ = some p ∧ q = q₀.weaken ∧ Es ∋ (j ↦ .aliasTo p q₀) ∧
        p = q₀) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ _ _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .eq hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .eqSym hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .has hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .bnd hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .bndId hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .hasVal hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .hasOfVal hEs _ =>
      cases hAt with
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .alias hEs hT =>
      cases hAt with
      | here => exact Or.inl ⟨_, by rw [← hEs.length]; exact .here, hT⟩
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT'⟩ | ⟨p, q₀, hρ, hq, hj', hb⟩
          · exact Or.inl ⟨j', .there hj', hT'⟩
          · exact Or.inr ⟨p, q₀, hρ, hq, .there hj', hb⟩
  | .aliasTo hEs hρ hb =>
      cases hAt with
      | here => exact Or.inr ⟨_, _, hρ, rfl, by rw [← hEs.length]; exact .here, hb⟩
      | there hAt' =>
          rcases hEs.At_alias hAt' with ⟨j', hj', hT'⟩ | ⟨p, q₀, hρ', hq, hj', hb'⟩
          · exact Or.inl ⟨j', .there hj', hT'⟩
          · exact Or.inr ⟨p, q₀, hρ', hq, .there hj', hb'⟩

/-- The entry at a bound of the target is a bound entry: either a closed
coercion out of the source object type, or the identity on a source bound. -/
theorem EntriesTyped.At_bnd {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {X : Ty (s,x)}
    (hAt : Tel₂ ∋ (j ↦ ⊑ X)) :
    ∃ G, Es ∋ (j ↦ .bnd G) ∧
      ((∃ T : Ty s, X = Ty.weaken T ∧ FormTyped Γ ρ G (μ Tel₁) T) ∨
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
  | .hasVal hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .hasOfVal hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .alias hEs _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩
  | .aliasTo hEs _ _ =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hk⟩ := hEs.At_bnd hAt'; exact ⟨G, .there hG, hk⟩

/-- The bound entry of typed entries, as a form out of any source with the
right shape. -/
theorem EntriesTyped.At_bnd' {ρ : Option (Path s)} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es : Entries s} {S : Ty s} (hS : Γ.resolveAt? ρ S = μ Tel₁)
    (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {T : Ty s} (hAt : Tel₂ ∋ (j ↦ ⊑ T↑)) :
    ∃ G, Es ∋ (j ↦ .bnd G) ∧ FormTyped Γ ρ G S T := by
  obtain ⟨G, hGat, hdisj⟩ := h.At_bnd hAt
  refine ⟨G, hGat, ?_⟩
  rcases hdisj with ⟨T₀, hX, hGt⟩ | ⟨k, rfl, hAt'⟩
  · obtain rfl := Ty.weaken_inj hX
    exact hGt.srcRes (hS.trans (Ctx.resolveAt?_obj_self hS).symm)
  · exact .bnd hS hAt' (.id rfl)

/-- The entries of a coercion into a bounds-only object type, by position. -/
theorem BndsTyped.length {ρ : Option (Path s)} {S : Ty s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ ρ S Es Tel) : Es.length = Tel.length := by
  match h with
  | .nil => rfl
  | .cons h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .thru h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]
  | .aliasTo h' _ _ => simp [Entries.length, Telescope.length, h'.length]

/-- Composing past the identity template on a source bound. -/
theorem FormTyped.bnd_id_inv {ρ : Option (Path s)} {M T : Ty s} {k : Nat}
    (h : FormTyped Γ ρ (.bnd k .id) M T) {F : Form s} {U : Ty s}
    (hF : FormTyped Γ ρ F T U) : FormTyped Γ ρ (.bnd k F) M U := by
  cases h with
  | bnd hM hAt hid =>
      cases hid with
      | id hres => exact .bnd hM hAt (hF.srcRes hres)

/-- The entry of view-free entries at a bound of the target: a bound entry,
or a routed identity template on a bound of the object type the route
reaches. -/
theorem BndsTyped.At_bnd {ρ : Option (Path s)} {S : Ty s} {Es : Entries s}
    {Tel : Telescope (s,x)} (h : BndsTyped Γ ρ S Es Tel) {j : Nat} {X : Ty (s,x)}
    (hAt : Tel ∋ (j ↦ ⊑ X)) {T : Ty s} (hX : X = T↑) :
    (∃ G : Form s, Es ∋ (j ↦ .bnd G) ∧ FormTyped Γ ρ G S T) ∨
    (∃ (H : Form s) (M : Ty s) (k : Nat), Es ∋ (j ↦ .thru H (.bnd (.bnd k .id))) ∧
      FormTyped Γ ρ H S M ∧
      ∀ (F : Form s) (U : Ty s), FormTyped Γ ρ F T U → FormTyped Γ ρ (.bnd k F) M U) := by
  match h with
  | .nil => cases hAt
  | .cons h' hF =>
      cases hAt with
      | here =>
          obtain rfl := Ty.weaken_inj hX.symm
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
              obtain rfl := Ty.weaken_inj hX
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
  | .aliasTo h' _ _ =>
      cases hAt with
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
      | bnd _ _ => simp [Form.isBndId] at h
      | into _ => simp [Form.isBndId] at h
  | bot => simp [Form.isBndId] at h
  | top => simp [Form.isBndId] at h
  | id => simp [Form.isBndId] at h
  | eqv _ => simp [Form.isBndId] at h
  | pi _ _ => simp [Form.isBndId] at h
  | obj _ => simp [Form.isBndId] at h
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
      | bnd _ _ => simp [Entry.prefix]
      | into _ => simp [Entry.prefix]
  | bot => simp [Entry.prefix]
  | top => simp [Entry.prefix]
  | id => simp [Entry.prefix]
  | eqv _ => simp [Entry.prefix]
  | pi _ _ => simp [Entry.prefix]
  | obj _ => simp [Entry.prefix]
  | into _ => simp [Entry.prefix]

/-! ### Sides, uniformly

A typed side is the identity, or a closed form at every pair of endpoints
its two *pins* allow: an endpoint is pinned to a weakened closed type, or it
is free.  The four constructors `closed`, `bot`, `top` and `free` are the
four pin patterns, and reading them uniformly is what makes the composition
of two sides one argument instead of sixteen. -/

/-- An endpoint of a side, pinned or free. -/
def Pinned {s : Sig} (a : Option (Ty s)) (T : Ty s) : Prop := ∀ A, a = some A → T = A

theorem Pinned.none {s : Sig} (T : Ty s) : Pinned none T := by
  intro A hA; cases hA

theorem Pinned.getD {s : Sig} (a : Option (Ty s)) : Pinned a (a.getD ⊤) := by
  intro A hA; rw [hA]; rfl

theorem Pinned.some {s : Sig} (A : Ty s) : Pinned (some A) A := by
  intro A' hA'; cases hA'; rfl

/-- The side of `Side.bot`: `bot` proves every target out of `⊥`. -/
theorem SideTyped.ofBot {X : Ty (s,x)} : SideTyped Γ .bot (⊥ : Ty (s,x)) X :=
  SideTyped.bot (A := ⊥) fun _ => .bot (by simp)

/-- The side of `Side.top`: `top` reads nothing of its source. -/
theorem SideTyped.ofTop {X : Ty (s,x)} : SideTyped Γ .top X (⊤ : Ty (s,x)) :=
  SideTyped.top (B := ⊤) fun _ => .top (by simp)

/-- A typed side read through its pins. -/
theorem SideTyped.gen {F : Form s} {S X : Ty (s,x)} (h : SideTyped Γ F S X) :
    (F = .id ∧ S = X) ∨ ∃ a b : Option (Ty s),
      (∀ A, a = some A → S = A↑) ∧ (∀ B, b = some B → X = B↑) ∧
      ∀ S₀ T₀ : Ty s, Pinned a S₀ → Pinned b T₀ → FormTyped Γ none F S₀ T₀ := by
  cases h with
  | id => exact Or.inl ⟨rfl, rfl⟩
  | @closed _ A B hF =>
      refine Or.inr ⟨some A, some B, ?_, ?_, ?_⟩
      · intro A' hA'; cases hA'; rfl
      · intro B' hB'; cases hB'; rfl
      · intro S₀ T₀ hS hT
        obtain rfl := hS A rfl
        obtain rfl := hT B rfl
        exact hF
  | @bot _ A _ hall =>
      refine Or.inr ⟨some A, none, ?_, ?_, ?_⟩
      · intro A' hA'; cases hA'; rfl
      · intro B' hB'; cases hB'
      · intro S₀ T₀ hS _
        obtain rfl := hS A rfl
        exact hall T₀
  | @top _ B _ hall =>
      refine Or.inr ⟨none, some B, ?_, ?_, ?_⟩
      · intro A' hA'; cases hA'
      · intro B' hB'; cases hB'; rfl
      · intro S₀ T₀ _ hT
        obtain rfl := hT B rfl
        exact hall S₀
  | free hall =>
      refine Or.inr ⟨none, none, ?_, ?_, ?_⟩
      · intro A' hA'; cases hA'
      · intro B' hB'; cases hB'
      · intro S₀ T₀ _ _
        exact hall S₀ T₀

/-- A side built from its pins. -/
theorem SideTyped.ofGen {F : Form s} {S X : Ty (s,x)} {a b : Option (Ty s)}
    (hS : ∀ A, a = some A → S = A↑) (hX : ∀ B, b = some B → X = B↑)
    (hF : ∀ S₀ T₀ : Ty s, Pinned a S₀ → Pinned b T₀ → FormTyped Γ none F S₀ T₀) :
    SideTyped Γ F S X := by
  cases a with
  | none =>
      cases b with
      | none => exact .free fun S₀ T₀ => hF S₀ T₀ (Pinned.none _) (Pinned.none _)
      | some B =>
          rw [hX B rfl]
          exact .top fun S₀ => hF S₀ B (Pinned.none _) (Pinned.some B)
  | some A =>
      cases b with
      | none =>
          rw [hS A rfl]
          exact .bot fun T₀ => hF A T₀ (Pinned.some A) (Pinned.none _)
      | some B =>
          rw [hS A rfl, hX B rfl]
          exact .closed (hF A B (Pinned.some A) (Pinned.some B))

/-- The composite of two typed sides, given that the two forms compose as
closed forms at every pair of endpoints.  The two middle pins name one
closed type, and the composite keeps the outer two pins. -/
theorem SideTyped.combine_of {F G : Form s} {S X Y : Ty (s,x)}
    (comb : ∀ A B C : Ty s, FormTyped Γ none F A B → FormTyped Γ none G B C →
      ∃ H, F.combine G = some H ∧ FormTyped Γ none H A C)
    (h₁ : SideTyped Γ F S X) (h₂ : SideTyped Γ G X Y) :
    ∃ H, F.combine G = some H ∧ SideTyped Γ H S Y := by
  rcases h₁.gen with ⟨rfl, rfl⟩ | ⟨a₁, b₁, hS₁, hX₁, hF₁⟩
  · exact ⟨G, Form.combine_id_left G, h₂⟩
  rcases h₂.gen with ⟨rfl, rfl⟩ | ⟨a₂, b₂, hS₂, hX₂, hF₂⟩
  · exact ⟨F, Form.combine_id_right F, SideTyped.ofGen hS₁ hX₁ hF₁⟩
  obtain ⟨M₀, hM₁, hM₂⟩ : ∃ M₀ : Ty s, Pinned b₁ M₀ ∧ Pinned a₂ M₀ := by
    cases hb : b₁ with
    | some B =>
        refine ⟨B, ?_, ?_⟩
        · exact Pinned.some B
        · intro A' hA'
          have h1 : X = B↑ := hX₁ B hb
          have h2 : X = A'↑ := hS₂ A' hA'
          exact Ty.weaken_inj (h1.symm.trans h2)
    | none =>
        cases ha : a₂ with
        | some A₂ => exact ⟨A₂, Pinned.none _, Pinned.some A₂⟩
        | none => exact ⟨⊤, Pinned.none _, Pinned.none _⟩
  obtain ⟨H, hH, _⟩ := comb (a₁.getD ⊤) M₀ (b₂.getD ⊤)
    (hF₁ _ _ (Pinned.getD a₁) hM₁) (hF₂ _ _ hM₂ (Pinned.getD b₂))
  refine ⟨H, hH, SideTyped.ofGen hS₁ hX₂ ?_⟩
  intro S₀ T₀ hS₀ hT₀
  obtain ⟨H', hH', hHt⟩ := comb S₀ M₀ T₀ (hF₁ _ _ hS₀ hM₁) (hF₂ _ _ hM₂ hT₀)
  obtain rfl : H' = H := Option.some.inj (hH'.symm.trans hH)
  exact hHt

theorem combine_typed_aux {ρ : Option (Path s)} : ∀ n : Nat,
    (∀ (F G : Form s) (S M T : Ty s), sizeOf F + sizeOf G ≤ n →
      FormTyped Γ ρ F S M → FormTyped Γ ρ G M T →
      ∃ H, F.combine G = some H ∧ FormTyped Γ ρ H S T) ∧
    (∀ (Es₁ Es₂ : Entries s) (Tel₁ TelM Tel₂ : Telescope (s,x)), sizeOf Es₁ + sizeOf Es₂ ≤ n →
      Γ.resolveAt? ρ (μ Tel₁) = μ Tel₁ → Γ.resolveAt? ρ (μ TelM) = μ TelM →
      EntriesTyped Γ ρ Tel₁ Es₁ TelM → EntriesTyped Γ ρ TelM Es₂ Tel₂ →
      ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ EntriesTyped Γ ρ Tel₁ Es Tel₂) ∧
    (∀ (F : Form s) (Es : Entries s) (S M : Ty s) (Tel : Telescope (s,x)),
      sizeOf F + sizeOf Es ≤ n →
      FormTyped Γ ρ F S M → BndsTyped Γ ρ M Es Tel →
      ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel) ∧
    (∀ (F : Form s) (Es : Entries s) (S M : Ty s) (TelM Tel : Telescope (s,x)),
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
      have side : ∀ (F G : Form s) (S X Y : Ty (s,x)), sizeOf F + sizeOf G ≤ n →
          SideTyped Γ F S X → SideTyped Γ G X Y →
          ∃ H, F.combine G = some H ∧ SideTyped Γ H S Y := by
        intro F G S X Y hn h₁ h₂
        exact SideTyped.combine_of
          (fun A B C hF hG => (combine_typed_aux (ρ := none) n).1 F G A B C hn hF hG) h₁ h₂
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
                obtain rfl := Ty.obj.inj ho
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihP .top _ S M _ _ (by simp at hn ⊢; omega) (.top hM) hM hEs
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
            | bnd ho hAt _ =>
                rw [hM] at ho
                obtain rfl := Ty.obj.inj ho
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
                obtain ⟨rfl, rfl⟩ := Ty.pi.inj hp
                refine ⟨_, ?_, .pi hS hT (.trans hd₂ hd) (.trans
                  (by simpa using LeCo.HasType.subst (Subst.Typed.selfCastOpaque hd₂) hc) hc₂)⟩
                simp [Form.combine]
            | obj ho _ _ => rw [hM] at ho; exact absurd ho (by simp)
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
                obtain rfl := Ty.obj.inj hM'
                obtain ⟨Es, hEs', hT'⟩ := ihE _ _ _ _ _ (by simp at hn; omega)
                  (Ctx.resolveAt?_obj_self hS) (Ctx.resolveAt?_obj_self hM) hEs hEs₂
                exact ⟨.obj Es, by simp [Form.combine, hEs'], .obj hS hT hT'⟩
            | bnd ho hAt hF' =>
                rw [hM] at ho
                obtain rfl := Ty.obj.inj ho
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
            | bnd ho hAt' hF'' =>
                obtain ⟨H, hH, hHt⟩ :=
                  ihF _ _ _ M T (by simp at hn ⊢; omega) hF' (.bnd ho hAt' hF'')
                exact ⟨_, Form.combine_bnd _ (by simp) (by simp) (by simp) hH, .bnd hS hAt hHt⟩
        | into hM hBs =>
            cases hG with
            | bot hb => rw [hM] at hb; exact absurd hb (by simp)
            | top hT => exact ⟨.top, by simp [Form.combine], .top hT⟩
            | id hres => exact ⟨_, Form.combine_id_right _, .into (hres.symm.trans hM) hBs⟩
            | eqv hres =>
                refine ⟨_, ?_, .into (hres.symm.trans hM) hBs⟩; simp [Form.combine]
            | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
            | obj ho hT hEs₂ =>
                rw [hM] at ho
                obtain rfl := Ty.obj.inj ho
                obtain ⟨Es', hEs', hT'⟩ :=
                  ihP _ _ S M _ _ (by simp at hn ⊢; omega) (.into hM hBs) hM hEs₂
                exact ⟨.into Es', by simp [Form.combine, hEs'], .into hT hT'⟩
            | bnd ho hAt hF' =>
                rw [hM] at ho
                obtain rfl := Ty.obj.inj ho
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
            rcases hT' with hT' | hT'
            · exact ⟨Es ▹ .has j',
                by simp [Entries.through, hEs, Entry.through, hj'.get?], .has hT hT'⟩
            · exact ⟨Es ▹ .has j',
                by simp [Entries.through, hEs, Entry.through, hj'.get?], .hasOfVal hT hT'⟩
        | .hasVal h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨j', hj', hT'⟩ := h₁.At_hasVal hAt
            exact ⟨Es ▹ .hasVal j',
              by simp [Entries.through, hEs, Entry.through, hj'.get?], .hasVal hT hT'⟩
        | .hasOfVal h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            obtain ⟨j', hj', hT'⟩ := h₁.At_hasVal hAt
            exact ⟨Es ▹ .has j',
              by simp [Entries.through, hEs, Entry.through, hj'.get?], .hasOfVal hT hT'⟩
        | .alias h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            rcases h₁.At_alias hAt with ⟨j', hj', hT'⟩ | ⟨p, q₀, hρ, rfl, hj', hb⟩
            · exact ⟨Es ▹ .alias j',
                by simp [Entries.through, hEs, Entry.through, hj'.get?], .alias hT hT'⟩
            · exact ⟨Es ▹ .aliasTo p q₀,
                by simp [Entries.through, hEs, Entry.through, hj'.get?], .aliasTo hT hρ hb⟩
        | .aliasTo h₂' hρ hb =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hop₁ hopM h₁ h₂'
            exact ⟨Es ▹ .aliasTo _ _, by simp [Entries.through, hEs, Entry.through],
              .aliasTo hT hρ hb⟩
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
        | .aliasTo hB' hρ hb =>
            obtain ⟨Es', hEs', hT'⟩ := ihB F _ S M _ (by simp at hn ⊢; omega) hF hB'
            exact ⟨Es' ▹ .aliasTo _ _, by simp [Entries.mapPrefix, hEs', Entry.prefix],
              .aliasTo hT' hρ hb⟩
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
        | .hasVal (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.hasVal j),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.hasVal hAt)⟩
        | .hasOfVal (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.has j),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.hasOfVal hAt)⟩
        | .alias (j := j) hEs' hAt =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .thru F (.alias j),
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .thru hT' hF hM (.alias hAt)⟩
        | .aliasTo hEs' hρ hb =>
            obtain ⟨Es', hEs'', hT'⟩ := ihP F _ S M _ _ (by simp at hn ⊢; omega) hF hM hEs'
            exact ⟨Es' ▹ .aliasTo _ _,
              by simp [Entries.mapPrefix, hEs'', Entry.prefix], .aliasTo hT' hρ hb⟩

theorem Form.combine_typed {ρ : Option (Path s)} {F G : Form s} {S M T : Ty s}
    (hF : FormTyped Γ ρ F S M) (hG : FormTyped Γ ρ G M T) :
    ∃ H, F.combine G = some H ∧ FormTyped Γ ρ H S T :=
  (combine_typed_aux _).1 F G S M T (Nat.le_refl _) hF hG

theorem EntriesTyped.through {ρ : Option (Path s)} {Tel₁ TelM Tel₂ : Telescope (s,x)}
    {Es₁ Es₂ : Entries s}
    (hop₁ : Γ.resolveAt? ρ (μ Tel₁) = μ Tel₁) (hopM : Γ.resolveAt? ρ (μ TelM) = μ TelM)
    (h₁ : EntriesTyped Γ ρ Tel₁ Es₁ TelM) (h₂ : EntriesTyped Γ ρ TelM Es₂ Tel₂) :
    ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ EntriesTyped Γ ρ Tel₁ Es Tel₂ :=
  (combine_typed_aux _).2.1 Es₁ Es₂ Tel₁ TelM Tel₂ (Nat.le_refl _) hop₁ hopM h₁ h₂

theorem BndsTyped.mapPrefix {ρ : Option (Path s)} {F : Form s} {Es : Entries s}
    {S M : Ty s} {Tel : Telescope (s,x)}
    (hF : FormTyped Γ ρ F S M) (hB : BndsTyped Γ ρ M Es Tel) :
    ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel :=
  (combine_typed_aux _).2.2.1 F Es S M Tel (Nat.le_refl _) hF hB

theorem EntriesTyped.mapPrefix {ρ : Option (Path s)} {F : Form s} {Es : Entries s}
    {S M : Ty s} {TelM Tel : Telescope (s,x)}
    (hF : FormTyped Γ ρ F S M) (hM : Γ.resolveAt? ρ M = μ TelM)
    (hEs : EntriesTyped Γ ρ TelM Es Tel) :
    ∃ Es', Entries.mapPrefix F Es = some Es' ∧ BndsTyped Γ ρ S Es' Tel :=
  (combine_typed_aux _).2.2.2 F Es S M TelM Tel (Nat.le_refl _) hF hM hEs

theorem SideTyped.combine {F G : Form s} {S X Y : Ty (s,x)}
    (h₁ : SideTyped Γ F S X) (h₂ : SideTyped Γ G X Y) :
    ∃ H, F.combine G = some H ∧ SideTyped Γ H S Y :=
  SideTyped.combine_of (fun _ _ _ hF hG => Form.combine_typed hF hG) h₁ h₂

/-- The chain of casts composes: a corollary of `Form.combine_typed` at the
opened shapes. -/
theorem ChainTyped.combine {r : BVar s .var} {F G : Form s} {S M T : Ty s}
    (hF : Γ ⊨[r] F : S ≤ M) (hG : Γ ⊨[r] G : M ≤ T) :
    ∃ H, F.combine G = some H ∧ Γ ⊨[r] H : S ≤ T :=
  Form.combine_typed hF hG

/-! ## Pairing -/

/-- Identity entries are typed from any telescope agreeing with the target at
its positions. -/
theorem Telescope.identityEntries_typed {ρ : Option (Path s)} :
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
  | .cons Tel (.hasVal ℓ), Tel', h => by
      rw [Telescope.identityEntries]
      exact .hasVal (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)
  | .cons Tel (.alias q), Tel', h => by
      rw [Telescope.identityEntries]
      exact .alias (Telescope.identityEntries_typed Tel Tel' fun i P hP => h i P (.there hP))
        (h _ _ .here)

theorem Telescope.identityEntries_self {ρ : Option (Path s)} (Tel : Telescope (s,x)) :
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
  | .cons Tel (.hasVal _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]
  | .cons Tel (.alias _), ρ => by
      simp [Telescope.rename, Proposition.rename, Telescope.identityEntries,
        Telescope.identityEntries_rename Tel ρ, Telescope.length_rename]

/-- Positions of the first telescope of a concatenation. -/
theorem Telescope.At.append_left {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel ∋ (i ↦ P)) : ∀ Tel' : Telescope s', (Tel ++ Tel') ∋ (i ↦ P)
  | .nil => h
  | .cons Tel' _ => .there (Telescope.At.append_left h Tel')

theorem EntriesTyped.append {ρ : Option (Path s)} {Tel Tel₁ Tel₂ : Telescope (s,x)}
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
  | .hasVal h₂' hAt => exact .hasVal (h₁.append h₂') hAt
  | .hasOfVal h₂' hAt => exact .hasOfVal (h₁.append h₂') hAt
  | .alias h₂' hAt => exact .alias (h₁.append h₂') hAt
  | .aliasTo h₂' hρ hb => exact .aliasTo (h₁.append h₂') hρ hb

theorem BndsTyped.append {ρ : Option (Path s)} {S : Ty s} {Tel₁ Tel₂ : Telescope (s,x)}
    {Es₁ Es₂ : Entries s}
    (h₁ : BndsTyped Γ ρ S Es₁ Tel₁) (h₂ : BndsTyped Γ ρ S Es₂ Tel₂) :
    BndsTyped Γ ρ S (Es₁ ++ Es₂) (Tel₁ ++ Tel₂) := by
  match h₂ with
  | .nil => exact h₁
  | .cons h₂' hF => exact .cons (h₁.append h₂') hF
  | .thru h₂' hH hM hE => exact .thru (h₁.append h₂') hH hM hE
  | .aliasTo h₂' hρ hb => exact .aliasTo (h₁.append h₂') hρ hb

/-- Opening distributes over concatenation. -/
theorem Telescope.openAt?_append (ρ : Option (Path s)) (Tel₁ Tel₂ : Telescope (s,x)) :
    Telescope.openAt? ρ (Tel₁ ++ Tel₂) =
      Telescope.openAt? ρ Tel₁ ++ Telescope.openAt? ρ Tel₂ := by
  cases ρ with
  | none => rfl
  | some r => simp [Telescope.openAt?, Telescope.append_substPath, Telescope.weaken]

/-- An absorbing form is typed evidence for every inclusion out of its
source. -/
theorem Form.absorbs_typed {ρ : Option (Path s)} : ∀ (F : Form s) (S M U : Ty s),
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
  | .into _, _, _, _, hab, _ => by simp [Form.absorbs] at hab

/-- The view-free entries read off a non-absorbing form into an object
type. -/
theorem Form.freeEntries_typed {ρ : Option (Path s)} : ∀ (F : Form s) {S : Ty s}
    {Tel Tel' : Telescope (s,x)}, FormTyped Γ ρ F S (μ Tel') →
    Γ.resolveAt? ρ (μ Tel') = μ Tel' → Tel.identityEntries = Tel'.identityEntries →
    F.absorbs = false →
    ∃ Es, F.freeEntries Tel = some Es ∧ BndsTyped Γ ρ S Es Tel'
  | .bot, _, _, _, _, _, _, hab => by simp [Form.absorbs] at hab
  | .top, S, Tel, Tel', h, hop, hI, _ => by
      cases h with
      | top hT =>
          rw [hop] at hT
          obtain rfl := Ty.obj.inj hT
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
  | .obj Es₀, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | obj hS hT hEs =>
          rw [hop] at hT
          obtain rfl := Ty.obj.inj hT
          obtain ⟨Es, hEs', hT'⟩ :=
            EntriesTyped.mapPrefix (Γ := Γ) (F := .id) (.id rfl) hS hEs
          exact ⟨Es, by simp [Form.freeEntries, Form.toEntries, hEs'], hT'⟩
  | .into Es₀, S, Tel, Tel', h, hop, _, _ => by
      cases h with
      | into hT hB =>
          rw [hop] at hT
          obtain rfl := Ty.obj.inj hT
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
theorem Form.pair_typed {ρ : Option (Path s)} {F G : Form s} {S : Ty s}
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
        obtain rfl := Ty.obj.inj hT₁
        obtain rfl := Ty.obj.inj hT₂
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
theorem ViewTyped.append {r : Path s} {V₁ V₂ : View s} {Tel₁ Tel₂ : Telescope (s,x)}
    (h₁ : Γ ⊨[r, σ] V₁ : Tel₁) (h₂ : Γ ⊨[r, σ] V₂ : Tel₂) :
    Γ ⊨[r, σ] V₁ ++ V₂ : Tel₁ ++ Tel₂ := by
  induction h₂ with
  | nil => exact h₁
  | le _ hF ih => exact .le ih hF
  | eq _ hE ih => exact .eq ih hE
  | has _ hH ih => exact .has ih hH
  | hasVal _ hH ih => exact .hasVal ih hH
  | alias _ hA ih => exact .alias ih hA
  | bnd _ hG ih => exact .bnd ih hG

/-- A closed side instantiated at a root is a typed coercion form. -/
theorem SideTyped.inst (r : Path s) {F : Form s} {S X : Ty (s,x)}
    (h : SideTyped Γ F S X) : Γ ⊨ F : S.substPath r ≤ X.substPath r := by
  cases h with
  | id => exact .id rfl
  | closed hF => rw [Ty.weaken_substPath, Ty.weaken_substPath]; exact hF
  | bot hall => rw [Ty.weaken_substPath]; exact hall _
  | top hall => rw [Ty.weaken_substPath]; exact hall _
  | free hall => exact hall _ _

/-- In a telescope that is already open at `r`, a bound is a weakened closed
type. -/
theorem Telescope.opened_bnd {r : Path s} {Tel : Telescope (s,x)}
    (hop : Telescope.openAt? (some r) Tel = Tel) {j : Nat} {X : Ty (s,x)}
    (hAt : Tel ∋ (j ↦ ⊑ X)) : X = ((X.substPath r)↑) := by
  rw [← hop] at hAt
  simp only [Telescope.openAt?_some, Telescope.weaken] at hAt
  obtain ⟨P₀, hP₀, hEq⟩ := Telescope.At.rename_inv hAt
  cases P₀ with
  | bnd Y =>
      simp only [Proposition.rename] at hEq
      obtain rfl : X = Y.weaken := by injection hEq
      rw [Ty.weaken_substPath]
  | le _ _ => simp [Proposition.rename] at hEq
  | eq _ _ => simp [Proposition.rename] at hEq
  | has _ => simp [Proposition.rename] at hEq
  | hasVal _ => simp [Proposition.rename] at hEq
  | alias _ => simp [Proposition.rename] at hEq

end

/-! ## Fuel monotonicity and determinism -/

section
variable (σ : Store s)

theorem normalizer_succ : ∀ n : Nat,
    (∀ (e : LeCo s) (F : Form s), σ ⊢ e ⇓[n] F → σ ⊢ e ⇓[(n + 1)] F) ∧
    (∀ (p : Side s) (F : Form s), sideForm σ n p = some F → sideForm σ (n + 1) p = some F) ∧
    (∀ (m : Morphism s) (Es : Entries s), σ ⊢ m ⇓ₘ[n] Es → σ ⊢ m ⇓ₘ[(n + 1)] Es) ∧
    (∀ (a : Atom s) (V : View s), σ ⊢ a ⇓ᵥ[n] V → σ ⊢ a ⇓ᵥ[(n + 1)] V) ∧
    (∀ (F : Form s) (a : Atom s) (V : View s),
      viewThrough σ n F a = some V → viewThrough σ (n + 1) F a = some V) ∧
    (∀ (p : Path s) (h : Has s) (q : Path s × Label),
      σ ⊢ p ; h ⇓ₕ[n] q → σ ⊢ p ; h ⇓ₕ[(n + 1)] q) ∧
    (∀ (a : Atom s) (p : Atom s × Form s), σ ⊢ a ⇓ᶜ[n] p → σ ⊢ a ⇓ᶜ[(n + 1)] p) ∧
    (∀ (a : Atom s) (C : Form s) (V : View s) (E : Entry s) (P : PropForm s),
      Entry.at σ n a C V E = some P → Entry.at σ (n + 1) a C V E = some P) ∧
    (∀ (a : Atom s) (C : Form s) (V : View s) (Es : Entries s) (V' : View s),
      entriesAt σ n a C V Es = some V' → entriesAt σ (n + 1) a C V Es = some V') ∧
    (∀ (P : PathCo s) (V : View s), pathView σ n P = some V → pathView σ (n + 1) P = some V) ∧
    (∀ (F : Form s) (P : PathCo s) (V : View s),
      pathViewThrough σ n F P = some V → pathViewThrough σ (n + 1) F P = some V) ∧
    (∀ (F : Form s) (r : Path s) (V : View s),
      pathViewThroughPath σ n F r = some V → pathViewThroughPath σ (n + 1) F r = some V) ∧
    (∀ (r : Path s) (C : Form s) (V : View s) (E : Entry s) (P : PropForm s),
      pathEntryAt σ n r C V E = some P → pathEntryAt σ (n + 1) r C V E = some P) ∧
    (∀ (r : Path s) (C : Form s) (V : View s) (Es : Entries s) (V' : View s),
      pathEntriesAt σ n r C V Es = some V' → pathEntriesAt σ (n + 1) r C V Es = some V') ∧
    (∀ (P : PathCo s) (F : Form s),
      pathChainForm σ n P = some F → pathChainForm σ (n + 1) P = some F)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h; rw [hnf] at h; cases h
      · intro p F h; rw [sideForm] at h; cases h
      · intro m Es h; rw [entries] at h; cases h
      · intro a V h; rw [view] at h; cases h
      · intro F a V h; rw [viewThrough] at h; cases h
      · intro x hh p h; rw [hasView] at h; cases h
      · intro a p h; rw [closedAtomForm] at h; cases h
      · intro a C V E P h; rw [Entry.at] at h; cases h
      · intro a C V Es V' h; rw [entriesAt] at h; cases h
      · intro P V h; rw [pathView] at h; cases h
      · intro F P V h; rw [pathViewThrough] at h; cases h
      · intro F r V h; rw [pathViewThroughPath] at h; cases h
      · intro r C V E P h; rw [pathEntryAt] at h; cases h
      · intro r C V Es V' h; rw [pathEntriesAt] at h; cases h
      · intro P F h; rw [pathChainForm] at h; cases h
  | n + 1 => by
      obtain ⟨ih1, ih0, ih2, ih3, ih4, ih5, ih6, ih7, ih8, ih9, ih10, ih11, ih12, ih13, ih14⟩ :=
        normalizer_succ n
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h
        cases e with
        | refl T => rw [hnf] at h; rw [hnf]; exact h
        | top T => rw [hnf] at h; rw [hnf]; exact h
        | bot T => rw [hnf] at h; rw [hnf]; exact h
        | eqToLe φ => rw [hnf] at h; rw [hnf]; exact h
        | pi d c => rw [hnf] at h; rw [hnf]; exact h
        | bound Tel i => rw [hnf] at h; rw [hnf]; exact h
        | intoBnd e =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ => simpa [hnf, he, ih1 e F₁ he] using h
        | obj Tel m =>
            cases hm : entries σ n m with
            | none => simp [hnf, hm] at h
            | some Es => simpa [hnf, hm, ih2 m Es hm] using h
        | pair Tel₁ Tel₂ e f =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hf : hnf σ n f with
                | none => simp [hnf, he, hf] at h
                | some G => simpa [hnf, he, hf, ih1 e F₁ he, ih1 f G hf] using h
        | trans e f =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hf : hnf σ n f with
                | none => simp [hnf, he, hf] at h
                | some G => simpa [hnf, he, hf, ih1 e F₁ he, ih1 f G hf] using h
        | member a e i =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hv : viewThrough σ n F₁ a with
                | none => simp [hnf, he, hv] at h
                | some V => simpa [hnf, he, hv, ih1 e F₁ he, ih4 F₁ a V hv] using h
        | memberP P e i =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hv : pathViewThrough σ n F₁ P with
                | none => simp [hnf, he, hv] at h
                | some V => simpa [hnf, he, hv, ih1 e F₁ he, ih10 F₁ P V hv] using h
      · intro p F h
        cases p with
        | none => rw [sideForm] at h; rw [sideForm]; exact h
        | some e =>
            rw [sideForm] at h; rw [sideForm]
            exact ih1 e F h
        | bot X => rw [sideForm] at h; rw [sideForm]; exact h
        | top X => rw [sideForm] at h; rw [sideForm]; exact h
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
                cases he : hnf σ n e with
                | none => simp [entries, hm, he] at h
                | some F => simpa [entries, hm, he, ih2 m Es₀ hm, ih1 e F he] using h
        | hasVal m j =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | hasOfVal m j =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | aliasCopy m j =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
      · intro a V h
        cases a with
        | var x => rw [view] at h; rw [view]; exact h
        | cast a e =>
            cases he : hnf σ n e with
            | none => simp [view, he] at h
            | some F => simp [view, ih1 e F he, ih4 F a V (by simpa [view, he] using h)]
        | foldSelf Tel a => simp only [view] at h ⊢; exact ih3 a V h
        | unfoldSelf a => simp only [view] at h ⊢; exact ih3 a V h
        | both Tel₁ Tel₂ a b =>
            cases ha : view σ n a with
            | none => simp [view, ha] at h
            | some V₁ =>
                cases hb : view σ n b with
                | none => simp [view, ha, hb] at h
                | some V₂ => simpa [view, ha, hb, ih3 a V₁ ha, ih3 b V₂ hb] using h
        | sngl a q α => rw [view] at h; rw [view]; exact h
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
        | top => rw [viewThrough] at h; rw [viewThrough]; exact h
        | bot => rw [viewThrough] at h; rw [viewThrough]; exact h
      · intro x hh p hp
        cases hh with
        | field ℓ => rw [hasView] at hp; rw [hasView]; exact hp
        | member a e i =>
            cases he : hnf σ n e with
            | none => simp [hasView, he] at hp
            | some F =>
                cases hv : viewThrough σ n F a with
                | none => simp [hasView, he, hv] at hp
                | some V => simpa [hasView, he, hv, ih1 e F he, ih4 F a V hv] using hp
        | memberP P e i =>
            cases he : hnf σ n e with
            | none => simp [hasView, he] at hp
            | some F =>
                cases hv : pathViewThrough σ n F P with
                | none => simp [hasView, he, hv] at hp
                | some V => simpa [hasView, he, hv, ih1 e F he, ih10 F P V hv] using hp
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
                    simpa [closedAtomForm, hc, he, ih6 a q hc, ih1 e G he] using h
        | foldSelf Tel a =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some q => simpa [closedAtomForm, hc, ih6 a q hc] using h
        | unfoldSelf a =>
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
        | sngl a q α =>
            cases hc : closedAtomForm σ n a with
            | none => simp [closedAtomForm, hc] at h
            | some p' => simpa [closedAtomForm, hc, ih6 a p' hc] using h
      · intro a C V E P h
        cases E with
        | le pre hh post => simp only [Entry.at] at h ⊢; exact h
        | eq j b => simp only [Entry.at] at h ⊢; exact h
        | has j => simp only [Entry.at] at h ⊢; exact h
        | hasVal j => simp only [Entry.at] at h ⊢; exact h
        | alias j => simp only [Entry.at] at h ⊢; exact h
        | aliasTo p q => simp only [Entry.at] at h ⊢; exact h
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
      · intro P V h
        cases P with
        | var x => rw [pathView] at h; rw [pathView]; exact h
        | sel P a i =>
            cases hE : σ.fieldCo P.path a with
            | none => simp [pathView, hE] at h
            | some E =>
                cases hF : hnf σ n E with
                | none => simp [pathView, hE, hF] at h
                | some F =>
                    have h' : pathViewThroughPath σ n F (.sel P.path a) = some V := by
                      simpa [pathView, hE, hF] using h
                    simpa [pathView, hE, ih1 E F hF] using ih11 F _ V h'
        | cast P e =>
            cases he : hnf σ n e with
            | none => simp [pathView, he] at h
            | some F =>
                simp [pathView, ih1 e F he, ih10 F P V (by simpa [pathView, he] using h)]
        | alias α p P => simp only [pathView] at h ⊢; exact ih9 P V h
        | foldSelf Tel P => simp only [pathView] at h ⊢; exact ih9 P V h
        | unfoldSelf P => simp only [pathView] at h ⊢; exact ih9 P V h
        | both Tel₁ Tel₂ P Q =>
            cases hP : pathView σ n P with
            | none => simp [pathView, hP] at h
            | some V₁ =>
                cases hQ : pathView σ n Q with
                | none => simp [pathView, hP, hQ] at h
                | some V₂ => simpa [pathView, hP, hQ, ih9 P V₁ hP, ih9 Q V₂ hQ] using h
        | sngl P q α => rw [pathView] at h; rw [pathView]; exact h
        | node p W ls vls => rw [pathView] at h; rw [pathView]; exact h
      · intro F P V h
        cases F with
        | id => simp only [pathViewThrough] at h ⊢; exact ih9 P V h
        | eqv φ => simp only [pathViewThrough] at h ⊢; exact ih9 P V h
        | obj Es =>
            cases hv : pathView σ n P with
            | none => simp [pathViewThrough, hv] at h
            | some V₀ =>
                cases hc : pathChainForm σ n P with
                | none => simp [pathViewThrough, hv, hc] at h
                | some C₀ =>
                    have h' : pathEntriesAt σ n P.path C₀ V₀ Es = some V := by
                      simpa [pathViewThrough, hv, hc] using h
                    simpa [pathViewThrough, ih9 P V₀ hv, ih14 P C₀ hc] using
                      ih13 P.path C₀ V₀ Es V h'
        | into Es =>
            cases hv : pathView σ n P with
            | none => simp [pathViewThrough, hv] at h
            | some V₀ =>
                cases hc : pathChainForm σ n P with
                | none => simp [pathViewThrough, hv, hc] at h
                | some C₀ =>
                    have h' : pathEntriesAt σ n P.path C₀ V₀ Es = some V := by
                      simpa [pathViewThrough, hv, hc] using h
                    simpa [pathViewThrough, ih9 P V₀ hv, ih14 P C₀ hc] using
                      ih13 P.path C₀ V₀ Es V h'
        | bnd i F =>
            cases hv : pathView σ n P with
            | none => simp [pathViewThrough, hv] at h
            | some V₀ =>
                cases hg : V₀.get? i with
                | none => simp [pathViewThrough, hv, hg] at h
                | some Q =>
                    cases hb : Q.bndForm? with
                    | none => simp [pathViewThrough, hv, hg, hb] at h
                    | some G =>
                        cases hcm : G.combine F with
                        | none => simp [pathViewThrough, hv, hg, hb, hcm] at h
                        | some H =>
                            have h' : pathViewThroughPath σ n H P.path = some V := by
                              simpa [pathViewThrough, hv, hg, hb, hcm] using h
                            simpa [pathViewThrough, ih9 P V₀ hv, hg, hb, hcm] using
                              ih11 H P.path V h'
        | pi d c => rw [pathViewThrough] at h; rw [pathViewThrough]; exact h
        | top => rw [pathViewThrough] at h; rw [pathViewThrough]; exact h
        | bot => rw [pathViewThrough] at h; rw [pathViewThrough]; exact h
      · intro F r V h
        cases F with
        | id => rw [pathViewThroughPath] at h; rw [pathViewThroughPath]; exact h
        | eqv φ => rw [pathViewThroughPath] at h; rw [pathViewThroughPath]; exact h
        | obj Es =>
            cases hv : σ.blockView r with
            | none => simp [pathViewThroughPath, hv] at h
            | some V₀ =>
                have h' : pathEntriesAt σ n r .id V₀ Es = some V := by
                  simpa [pathViewThroughPath, hv] using h
                simpa [pathViewThroughPath, hv] using ih13 r .id V₀ Es V h'
        | into Es =>
            cases hv : σ.blockView r with
            | none => simp [pathViewThroughPath, hv] at h
            | some V₀ =>
                have h' : pathEntriesAt σ n r .id V₀ Es = some V := by
                  simpa [pathViewThroughPath, hv] using h
                simpa [pathViewThroughPath, hv] using ih13 r .id V₀ Es V h'
        | bnd i F =>
            cases hv : σ.blockView r with
            | none => simp [pathViewThroughPath, hv] at h
            | some V₀ =>
                cases hg : V₀.get? i with
                | none => simp [pathViewThroughPath, hv, hg] at h
                | some Q =>
                    cases hb : Q.bndForm? with
                    | none => simp [pathViewThroughPath, hv, hg, hb] at h
                    | some G =>
                        cases hcm : G.combine F with
                        | none => simp [pathViewThroughPath, hv, hg, hb, hcm] at h
                        | some H =>
                            have h' : pathViewThroughPath σ n H r = some V := by
                              simpa [pathViewThroughPath, hv, hg, hb, hcm] using h
                            simpa [pathViewThroughPath, hv, hg, hb, hcm] using
                              ih11 H r V h'
        | pi d c => rw [pathViewThroughPath] at h; rw [pathViewThroughPath]; exact h
        | top => rw [pathViewThroughPath] at h; rw [pathViewThroughPath]; exact h
        | bot => rw [pathViewThroughPath] at h; rw [pathViewThroughPath]; exact h
      · intro r C V E P h
        cases E with
        | le pre hh post => simp only [pathEntryAt] at h ⊢; exact h
        | eq j b => simp only [pathEntryAt] at h ⊢; exact h
        | has j => simp only [pathEntryAt] at h ⊢; exact h
        | hasVal j => simp only [pathEntryAt] at h ⊢; exact h
        | alias j => simp only [pathEntryAt] at h ⊢; exact h
        | aliasTo p q => simp only [pathEntryAt] at h ⊢; exact h
        | bnd G => simp only [pathEntryAt] at h ⊢; exact h
        | thru H E =>
            cases hcm : C.combine H with
            | none => simp [pathEntryAt, hcm] at h
            | some C₁ =>
                cases hv : pathViewThroughPath σ n C₁ r with
                | none => simp [pathEntryAt, hcm, hv] at h
                | some V₁ =>
                    have h' : pathEntryAt σ n r C₁ V₁ E = some P := by
                      simpa [pathEntryAt, hv, hcm] using h
                    simpa [pathEntryAt, ih11 C₁ r V₁ hv, hcm] using ih12 r C₁ V₁ E P h'
      · intro r C V Es V' h
        cases Es with
        | nil => simp only [pathEntriesAt] at h ⊢; exact h
        | cons Es₀ E =>
            cases he : pathEntriesAt σ n r C V Es₀ with
            | none => simp [pathEntriesAt, he] at h
            | some V₀ =>
                cases hE : pathEntryAt σ n r C V E with
                | none => simp [pathEntriesAt, he, hE] at h
                | some P =>
                    simpa [pathEntriesAt, he, hE, ih13 r C V Es₀ V₀ he,
                      ih12 r C V E P hE] using h
      · intro P F h
        cases P with
        | var x => rw [pathChainForm] at h; rw [pathChainForm]; exact h
        | sel P a i =>
            cases hE : σ.fieldCo P.path a with
            | none => simp [pathChainForm, hE] at h
            | some E =>
                have h' : hnf σ n E = some F := by simpa [pathChainForm, hE] using h
                simpa [pathChainForm, hE] using ih1 E F h'
        | cast P e =>
            cases hc : pathChainForm σ n P with
            | none => simp [pathChainForm, hc] at h
            | some F₀ =>
                cases he : hnf σ n e with
                | none => simp [pathChainForm, hc, he] at h
                | some G => simpa [pathChainForm, hc, he, ih14 P F₀ hc, ih1 e G he] using h
        | alias α p P => simp only [pathChainForm] at h ⊢; exact ih14 P F h
        | foldSelf Tel P => simp only [pathChainForm] at h ⊢; exact ih14 P F h
        | unfoldSelf P => simp only [pathChainForm] at h ⊢; exact ih14 P F h
        | both Tel₁ Tel₂ P Q =>
            cases hP : pathChainForm σ n P with
            | none => simp [pathChainForm, hP] at h
            | some F₁ =>
                cases hQ : pathChainForm σ n Q with
                | none => simp [pathChainForm, hP, hQ] at h
                | some F₂ =>
                    simpa [pathChainForm, hP, hQ, ih14 P F₁ hP, ih14 Q F₂ hQ] using h
        | sngl P q α =>
            cases hc : pathChainForm σ n P with
            | none => simp [pathChainForm, hc] at h
            | some F₀ => simpa [pathChainForm, hc, ih14 P F₀ hc] using h
        | node p W ls vls => rw [pathChainForm] at h; rw [pathChainForm]; exact h


variable {σ}

theorem hnf_le {n n' : Nat} {e : LeCo s} {F : Form s} (h : n ≤ n') (hF : σ ⊢ e ⇓[n] F) :
    σ ⊢ e ⇓[n'] F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).1 e F ih

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

theorem hasView_le {n n' : Nat} {x : Path s} {hh : Has s} {p : Path s × Label}
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

/-! ### The path family

The same monotonicity, for the six functions of the view of a stable path.
`hnf` reads them through its `memberP` clause, so they are part of one
induction with the atom family. -/

theorem pathView_le {n n' : Nat} {P : PathCo s} {V : View s} (h : n ≤ n')
    (hV : pathView σ n P = some V) : pathView σ n' P = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.1 P V ih

theorem pathViewThrough_le {n n' : Nat} {F : Form s} {P : PathCo s} {V : View s} (h : n ≤ n')
    (hV : pathViewThrough σ n F P = some V) : pathViewThrough σ n' F P = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.2.1 F P V ih

theorem pathViewThroughPath_le {n n' : Nat} {F : Form s} {r : Path s} {V : View s} (h : n ≤ n')
    (hV : pathViewThroughPath σ n F r = some V) : pathViewThroughPath σ n' F r = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.2.2.1 F r V ih

theorem pathEntryAt_le {n n' : Nat} {r : Path s} {C : Form s} {V : View s} {E : Entry s}
    {P : PropForm s} (h : n ≤ n') (hP : pathEntryAt σ n r C V E = some P) :
    pathEntryAt σ n' r C V E = some P := by
  induction h with
  | refl => exact hP
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.2.2.2.1 r C V E _ ih

theorem pathEntriesAt_le {n n' : Nat} {r : Path s} {C : Form s} {V : View s} {Es : Entries s}
    {V' : View s} (h : n ≤ n') (hV : pathEntriesAt σ n r C V Es = some V') :
    pathEntriesAt σ n' r C V Es = some V' := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.2.2.2.2.1 r C V Es V' ih

theorem pathChainForm_le {n n' : Nat} {P : PathCo s} {F : Form s} (h : n ≤ n')
    (hF : pathChainForm σ n P = some F) : pathChainForm σ n' P = some F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2 P F ih

/-! ## Determinism -/

theorem hnf_det {n₁ n₂ : Nat} {e : LeCo s} {F₁ F₂ : Form s}
    (h₁ : σ ⊢ e ⇓[n₁] F₁) (h₂ : σ ⊢ e ⇓[n₂] F₂) : F₁ = F₂ :=
  Option.some.inj ((hnf_le (Nat.le_max_left n₁ n₂) h₁).symm.trans (hnf_le (Nat.le_max_right n₁ n₂) h₂))

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

/-! ## A stable field of a block is a field of it

`Store.blockOf` answers a block built by the block builder out of a stored
value, and in such a block every stable label is a label.  That is what
reads a stable presence as a presence, which is the `hasOfVal` entry. -/

mutual

/-- Every stable label of the block is a label of it, hereditarily. -/
def Block.ValsAreFields : Block s → Prop
  | .obj _ ls vls ch => (∀ ℓ, ℓ ∈ vls → ℓ ∈ ls) ∧ ch.ValsAreFields
  | .fwd _ => True

def Children.ValsAreFields : Children s → Prop
  | .nil => True
  | .cons ch _ b => ch.ValsAreFields ∧ b.ValsAreFields

end

theorem Fields.mem_labels_of_mem_valLabels : ∀ (F : Fields s) (ℓ : Label),
    ℓ ∈ F.valLabels → ℓ ∈ F.labels
  | .nil, ℓ, h => by simp [Fields.valLabels] at h
  | .cons F ℓ' t, ℓ, h => by
      simp only [Fields.valLabels] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h'
        · simp [Fields.labels]
        · simp [Fields.labels, Fields.mem_labels_of_mem_valLabels F ℓ h']
      · simp [Fields.labels,
          Fields.mem_labels_of_mem_valLabels F ℓ (List.mem_filter.mp h).1]

/-- Dropping the entries at a label keeps the property of the rest. -/
theorem Children.valsAreFields_dropLabel : ∀ (ch : Children s) (ℓ : Label),
    ch.ValsAreFields → (ch.dropLabel ℓ).ValsAreFields
  | .nil, _, _ => trivial
  | .cons ch ℓ' b, ℓ, h => by
      rw [Children.dropLabel]
      split
      · exact Children.valsAreFields_dropLabel ch ℓ h.1
      · exact ⟨Children.valsAreFields_dropLabel ch ℓ h.1, h.2⟩

mutual

theorem Block.valsAreFields_subst : ∀ (B : Block s1) (σ : PathSubst s1 s2),
    B.ValsAreFields → (B.subst σ).ValsAreFields
  | .obj W ls vls ch, σ, h => by
      refine ⟨h.1, Children.valsAreFields_subst ch σ h.2⟩
  | .fwd q, σ, _ => trivial

theorem Children.valsAreFields_subst : ∀ (ch : Children s1) (σ : PathSubst s1 s2),
    ch.ValsAreFields → (ch.subst σ).ValsAreFields
  | .nil, _, _ => trivial
  | .cons ch ℓ b, σ, h =>
      ⟨Children.valsAreFields_subst ch σ h.1, Block.valsAreFields_subst b σ h.2⟩

end

mutual

theorem Value.blockSelf_valsAreFields : ∀ {s : Sig} (v : Value s),
    (Value.blockSelf (s := s) v).ValsAreFields
  | _, .lam _ _ => ⟨by intro ℓ h; simp at h, trivial⟩
  | _, .cast v _ => Value.blockSelf_valsAreFields v
  | _, .obj W F =>
      ⟨fun ℓ h => Fields.mem_labels_of_mem_valLabels F ℓ h,
        Fields.children_valsAreFields F (.var .here)⟩

theorem Fields.children_valsAreFields : ∀ {s : Sig} (F : Fields s) (p : Path s),
    (F.children p).ValsAreFields
  | _, .nil, _ => trivial
  | _, .cons F ℓ t, p => by
      rw [Fields.children]
      cases ht : t.childAt (.sel p ℓ) with
      | none => exact Children.valsAreFields_dropLabel _ ℓ (Fields.children_valsAreFields F p)
      | some b =>
          exact ⟨Fields.children_valsAreFields F p, Tm.childAt_valsAreFields t (.sel p ℓ) b ht⟩

theorem Tm.childAt_valsAreFields : ∀ {s : Sig} (t : Tm s) (p : Path s) (B : Block s),
    t.childAt p = some B → B.ValsAreFields
  | _, .val v, p, B, h => by
      rw [Tm.childAt] at h
      cases hv : v.isStableLit with
      | false => simp [hv] at h
      | true =>
          simp only [hv, if_true, Option.some.injEq] at h
          subst h
          exact Block.valsAreFields_subst _ _ (Value.blockSelf_valsAreFields v)
  | _, .atom a, _, B, h => by
      rw [Tm.childAt] at h; obtain rfl := Option.some.inj h; trivial
  | _, .cast t _, p, B, h => by
      rw [Tm.childAt] at h
      split at h
      · cases h
      · exact Tm.childAt_valsAreFields t p B h
  | _, .app _ _, _, _, h => by rw [Tm.childAt] at h; cases h
  | _, .proj _ _ _, _, _, h => by rw [Tm.childAt] at h; cases h
  | _, .let _ _, _, _, h => by rw [Tm.childAt] at h; cases h

end

theorem Value.blocksAt_valsAreFields (v : Value s) (p : Path s) :
    (v.blocksAt p).ValsAreFields :=
  Block.valsAreFields_subst _ _ (Value.blockSelf_valsAreFields v)

theorem Children.at?_valsAreFields : ∀ (ch : Children s) (ℓ : Label) (B : Block s),
    ch.ValsAreFields → ch.at? ℓ = some B → B.ValsAreFields
  | .nil, _, _, _, h => by rw [Children.at?] at h; cases h
  | .cons ch ℓ' b, ℓ, B, hch, h => by
      rw [Children.at?] at h
      by_cases hℓ : ℓ = ℓ'
      · rw [if_pos hℓ] at h; obtain rfl := Option.some.inj h; exact hch.2
      · rw [if_neg hℓ] at h; exact Children.at?_valsAreFields ch ℓ B hch.1 h

theorem Store.blockOf_valsAreFields (σ : Store s) : ∀ (p : Path s) (B : Block s),
    σ.blockOf p = some B → B.ValsAreFields
  | .var x, B, h => by
      rw [Store.blockOf] at h
      obtain rfl := Option.some.inj h
      exact Value.blocksAt_valsAreFields _ _
  | .sel p a, B, h => by
      rw [Store.blockOf] at h
      cases hp : σ.blockOf p with
      | none => rw [hp] at h; cases h
      | some B₀ =>
          have hB₀ := Store.blockOf_valsAreFields σ p B₀ hp
          rw [hp] at h
          cases B₀ with
          | fwd q => cases h
          | obj W ls vls ch =>
              simp only at h
              cases hch : ch.at? a with
              | none => rw [hch] at h; cases h
              | some b =>
                  have hb := Children.at?_valsAreFields ch a b hB₀.2 hch
                  rw [hch] at h
                  cases b with
                  | obj W' ls' vls' ch' =>
                      simp only at h
                      obtain rfl := Option.some.inj h
                      exact hb
                  | fwd q =>
                      cases q with
                      | var y =>
                          simp only at h
                          obtain rfl := Option.some.inj h
                          exact Value.blocksAt_valsAreFields _ _
                      | sel _ _ => simp only at h; cases h

/-- A stable field of a path is a field of it. -/
theorem Store.hasField_of_hasValFieldP {σ : Store s} {p : Path s} {ℓ : Label}
    (h : σ.HasValFieldP p ℓ) : σ.HasFieldP p ℓ := by
  obtain ⟨W, Fs, vls, ch, hb, hℓ⟩ := h
  exact ⟨W, Fs, vls, ch, hb, (Store.blockOf_valsAreFields σ p _ hb).1 ℓ hℓ⟩

/-! ## The view of an atom through a typed form -/

/-- The view of the literal at a root is typed at the root's type. -/
def RootViewTyped (Γ : Ctx s) (σ : Store s) (r : BVar s .var) : Prop :=
  (∀ Tel : Telescope (s,x), Γ.resolve (Γ.lookupTy r) = μ Tel →
      Γ ⊨[Path.var r, σ] ((σ.lookup r).precView (.var r)) : Tel) ∧
    Γ.resolve (Γ.lookupTy r) ≠ ⊥

theorem Ty.unfoldAt_eq_bot {r : Path s} {X : Ty s} (h : X.unfoldAt r = ⊥) : X = ⊥ := by
  cases X <;> simp [Ty.unfoldAt] at h ⊢

theorem Ty.unfoldAt_eq_obj {r : Path s} {X : Ty s} {Tel : Telescope (s,x)}
    (h : X.unfoldAt r = μ Tel) : ∃ Tel₀, X = μ Tel₀ ∧ ((Tel₀.substPath r)↑) = Tel := by
  cases X with
  | obj Tel₀ => exact ⟨Tel₀, rfl, Ty.obj.inj h⟩
  | bot => simp [Ty.unfoldAt] at h
  | sel _ _ => simp [Ty.unfoldAt] at h
  | pi _ _ => simp [Ty.unfoldAt] at h

/-- The view of the root variable, at the shapes opened at the root. -/
theorem RootViewTyped.opened (hroot : RootViewTyped Γ σ r) :
    (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var r)) (Γ.lookupTy r) = μ Tel →
        Γ ⊨[Path.var r, σ] ((σ.lookup r).precView (.var r)) : Tel) ∧
      Γ.resolveAt? (some (Path.var r)) (Γ.lookupTy r) ≠ ⊥ := by
  refine ⟨fun Tel h => ?_, fun h => hroot.2 (Ty.unfoldAt_eq_bot h)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Ty.unfoldAt_eq_obj h
  exact ViewTyped_unfold (hroot.1 Tel₀ h₀)

/-- The constant alias entry, read into a view at the receiver it names, which
is the path it names (decision 24). -/
theorem ViewTyped.aliasTo {r : Path s} {V : View s} {Tel : Telescope (s,x)} {q : Path s}
    (hV : Γ ⊨[r, σ] V : Tel) (hb : r = q) :
    Γ ⊨[r, σ] V ▹ .alias q : Tel ▹ ≈ (q.weaken) := by
  have halias := ViewTyped.alias (q := q.weaken) hV (by rw [Path.weaken_substPath]; exact hb)
  rwa [Path.weaken_substPath] at halias

/-! ## Applying typed entries to the view of an atom -/

/-- Instantiating one typed entry at the typed view of the object type the
entry reads.  The root of the mode is the atom's own root: a stable presence
and a constant alias are read at the receiver, and the receiver of the
instance is the atom. -/
theorem EntryTyped.at_typed {r : Path s} {M : Ty s} {TelM : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} {C : Form s} {V : View s} (a : Atom s)
    (hr : r = Path.var a.root)
    (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ M) (hM : Γ.resolveAt? (some r) M = μ TelM)
    (hV : Γ ⊨[r, σ] V : TelM) (hE : EntryTyped Γ (some r) TelM E P) :
    ∃ m Q, Entry.at σ m a C V E = some Q ∧
      ∀ {V₀ : View s} {Tel₀ : Telescope (s,x)},
        Γ ⊨[r, σ] V₀ : Tel₀ → Γ ⊨[r, σ] V₀ ▹ Q : Tel₀ ▹ P := by
  have hop : Γ.resolveAt? (some r) (μ TelM) = μ TelM := Ctx.resolveAt?_obj_self hM
  have hCT : Γ ⊨[r] C : Γ.nodeTy r ≤ μ TelM := hC.tgtRes (hM.trans hop.symm)
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
  | .hasVal (ℓ := ℓ) hAt =>
      obtain ⟨hq, hHF⟩ := hV.hasVal_entry hAt
      exact ⟨1, .hasVal ℓ, by simp [Entry.at, hq.get?], fun hV₀ => .hasVal hV₀ hHF⟩
  | .hasOfVal (ℓ := ℓ) hAt =>
      subst hr
      obtain ⟨hq, hHF⟩ := hV.hasVal_entry hAt
      exact ⟨1, .has (Path.var a.root) ℓ, by simp [Entry.at, hq.get?],
        fun hV₀ => .has hV₀ (Store.hasField_of_hasValFieldP hHF)⟩
  | .alias (q := q) hAt =>
      obtain ⟨hq, hb⟩ := hV.alias_entry hAt
      exact ⟨1, .alias (q.substPath r), by simp [Entry.at, hq.get?],
        fun hV₀ => .alias hV₀ hb⟩
  | .aliasTo (p := p) (q := q) hρ hb =>
      obtain rfl : p = r := (Option.some.inj hρ).symm
      subst hr
      exact ⟨1, .alias q, by simp [Entry.at], fun hV₀ => ViewTyped.aliasTo hV₀ hb⟩
  | .bnd (j := k) hG =>
      have hG' : Γ ⊨[r] (Form.bnd k .id) : M ≤ _ := hG.srcRes (hM.trans hop.symm)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG'
      exact ⟨1, .bnd H, by simp [Entry.at, hH],
        fun hV₀ => .bnd hV₀ (by rwa [Ty.weaken_substPath])⟩
  | .bndId (X := X) (j := k) hAt =>
      have hX : X = ((X.substPath r)↑) := Telescope.opened_bnd (Ctx.resolveAt?_opened hM) hAt
      have hAt' : TelM ∋ (k ↦ ⊑ ((X.substPath r)↑)) := by rw [← hX]; exact hAt
      have hBnd : Γ ⊨[r] (Form.bnd k .id) : M ≤ X.substPath r := .bnd hM hAt' (.id rfl)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hBnd
      exact ⟨1, .bnd H, by simp [Entry.at, hH], fun hV₀ => .bnd hV₀ hHt⟩

/-- Applying typed view-free entries at a root: the view of the source is
consulted only through the routes of the entries, which are sub-forms. -/
theorem entriesAtBnds_typed {r : Path s} {S : Ty s} {C : Form s} {a : Atom s}
    (hr : r = Path.var a.root) (V : View s) (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ S) :
    ∀ {Es : Entries s} {Tel : Telescope (s,x)},
      (∀ (H : Form s) (M : Ty s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
        Γ ⊨[r] H : S ≤ M → Γ.resolveAt? (some r) M = μ TelM →
        ∃ m V'', viewThrough σ m H a = some V'' ∧ Γ ⊨[r, σ] V'' : TelM) →
      BndsTyped Γ (some r) S Es Tel →
      ∃ m V', entriesAt σ m a C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel
  | _, _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, hIH, .cons hB' hG => by
      obtain ⟨m, V', hV', hT⟩ :=
        entriesAtBnds_typed hr V hC (fun H M TelM hlt => hIH H M TelM (by simp; omega)) hB'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Ty.weaken_substPath])⟩
      simp [entriesAt, entriesAt_le (Nat.le_succ m) hV', Entry.at, hH]
  | _, _, hIH, .thru hB' hH hM hE => by
      obtain ⟨m₁, V₁, hV₁, hT₁⟩ :=
        entriesAtBnds_typed hr V hC (fun H' M' TelM' hlt => hIH H' M' TelM' (by simp; omega)) hB'
      obtain ⟨m₂, V₂, hV₂, hT₂⟩ := hIH _ _ _ (by simp; omega) hH hM
      obtain ⟨C', hC', hC'T⟩ := Form.combine_typed hC hH
      obtain ⟨m₃, Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC'T hM hT₂ hE
      refine ⟨max m₁ (max m₂ m₃) + 2, V₁ ▹ Q, ?_, hQt hT₁⟩
      have h₁ := entriesAt_le (σ := σ) (a := a) (C := C) (V := V)
        (Nat.le_trans (Nat.le_max_left m₁ (max m₂ m₃)) (Nat.le_succ _)) hV₁
      have h₂ := viewThrough_le (σ := σ)
        (Nat.le_trans (Nat.le_max_left m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hV₂
      have h₃ := entryAt_le (σ := σ) (a := a)
        (Nat.le_trans (Nat.le_max_right m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hQ
      simp [entriesAt, h₁, Entry.at, h₂, hC', h₃]
  | _, _, hIH, .aliasTo hB' hρ hb => by
      obtain ⟨m, V', hV', hT⟩ :=
        entriesAtBnds_typed hr V hC (fun H M TelM hlt => hIH H M TelM (by simp; omega)) hB'
      obtain rfl := Option.some.inj hρ
      subst hr
      refine ⟨m + 2, _, ?_, ViewTyped.aliasTo hT hb⟩
      simp [entriesAt, entriesAt_le (Nat.le_succ m) hV', Entry.at]

/-- Applying typed entries to a typed view at a root. -/
theorem entriesAt_typed {r : Path s} {Tel₁ : Telescope (s,x)}
    {V : View s} {C : Form s} {S : Ty s} (a : Atom s) (hr : r = Path.var a.root)
    (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ S) (hS : Γ.resolveAt r S = μ Tel₁)
    (hV : Γ ⊨[r, σ] V : Tel₁) :
    ∀ {Es : Entries s} {Tel₂ : Telescope (s,x)}, EntriesTyped Γ (some r) Tel₁ Es Tel₂ →
      ∃ m V', entriesAt σ m a C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂
  | _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, .le hEs' hh hpre hpost => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.le hh hpre hpost)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eq hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.eq hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .eqSym hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.eqSym hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .has hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.has hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .hasVal hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.hasVal hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .hasOfVal hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.hasOfVal hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .alias hEs' hAt => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.alias hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .aliasTo hEs' hρ hb => by
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.aliasTo hρ hb)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]
  | _, _, .bnd hEs' hG => by
      have hSA : Γ.resolveAt? (some r) S = μ Tel₁ := hS
      have hop : Γ.resolveAt? (some r) (μ Tel₁) = μ Tel₁ := Ctx.resolveAt?_obj_self hSA
      have hCT : Γ ⊨[r] C : Γ.nodeTy r ≤ μ Tel₁ := hC.tgtRes (hSA.trans hop.symm)
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hCT hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Ty.weaken_substPath])⟩
      simp [entriesAt, entriesAt_le (Nat.le_succ m) hV', Entry.at, hH]
  | _, _, .bndId (X := X) (j := j) hEs' hAt => by
      have hSA : Γ.resolveAt? (some r) S = μ Tel₁ := hS
      obtain ⟨m, V', hV', hT⟩ := entriesAt_typed a hr hC hS hV hEs'
      obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.at_typed a hr hC hS hV (.bndId hAt)
      refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
      have h₁ := entriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
      have h₂ := entryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
      simp [entriesAt, h₁, h₂]


/-- The view of the root variable through a typed form. -/
theorem viewThroughVar_typed {r : BVar s .var} (hroot : RootViewTyped Γ σ r) :
    ∀ (k : Nat) (F : Form s) (T : Ty s), sizeOf F ≤ k →
      Γ ⊨[Path.var r] F : Γ.lookupTy r ≤ T →
      ∃ m V', viewThrough σ m F (.var r) = some V' ∧
        (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var r)) T = μ Tel →
          Γ ⊨[Path.var r, σ] V' : Tel) ∧
        Γ.resolveAt? (some (Path.var r)) T ≠ ⊥
  | 0, F, _, hk, _ => by cases F <;> simp at hk
  | k + 1, F, T, hk, hF => by
    obtain ⟨hrv, hrb⟩ := hroot.opened
    have hview : ∀ n : Nat, view σ (n + 1) (.var r) = some ((σ.lookup r).precView (.var r)) :=
      fun _ => rfl
    have hchain : ∀ n : Nat, closedAtomForm σ (n + 1) (.var r) = some (.var r, .id) := fun _ => rfl
    have hCid : Γ ⊨[Path.var r] (Form.id) : Γ.lookupTy r ≤ Γ.lookupTy r := .id rfl
    match hF with
    | .bot hS => exact absurd hS hrb
    | .top hT =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h
          obtain rfl := Ty.obj.inj (by simpa using h : (μ .nil : Ty s) = μ Tel)
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
    | .obj hS hT hEs =>
        obtain ⟨m, V', hV', hT'⟩ := entriesAt_typed (.var r) rfl hCid hS (hrv _ hS) hEs
        refine ⟨m + 2, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, hview, hchain, entriesAt_le (Nat.le_succ m) hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .into (Es := Es) hT hB =>
        have hIH : ∀ (H : Form s) (M : Ty s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
            Γ ⊨[Path.var r] H : Γ.lookupTy r ≤ M →
            Γ.resolveAt? (some (Path.var r)) M = μ TelM →
            ∃ m V'', viewThrough σ m H (.var r) = some V'' ∧ Γ ⊨[Path.var r, σ] V'' : TelM := by
          intro H M TelM hlt hH hM
          have hsz : sizeOf H ≤ k := by simp at hk; omega
          obtain ⟨m, V'', hV'', hVt'', _⟩ := viewThroughVar_typed hroot k H M hsz hH
          exact ⟨m, V'', hV'', hVt'' _ hM⟩
        obtain ⟨m, V', hV', hT'⟩ :=
          entriesAtBnds_typed (a := .var r) rfl ((σ.lookup r).precView (.var r)) hCid hIH hB
        refine ⟨m + 2, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, hview, hchain, entriesAt_le (Nat.le_succ m) hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .bnd hS hAt _ =>
        obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
        exact absurd hG (Value.precView_noBnd (.var r) _ _ _)

/-- Applying a typed form to the typed view of an atom yields the typed view
of the target. -/
theorem viewThrough_typed_aux {a a' : Atom s} {V : View s} {C : Form s}
    {n : Nat} (hroot : RootViewTyped Γ σ a.root)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hC : σ ⊢ a ⇓ᶜ[n] (a', C)) :
    ∀ (k : Nat) (F : Form s) (S T : Ty s), sizeOf F ≤ k →
      Γ ⊨[Path.var a.root] F : S ≤ T →
      Γ ⊨[Path.var a.root] C : Γ.lookupTy a.root ≤ S →
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) S = μ Tel →
        Γ ⊨[Path.var a.root, σ] V : Tel) →
      Γ.resolveAt? (some (Path.var a.root)) S ≠ ⊥ →
      ∃ m V', viewThrough σ m F a = some V' ∧
        (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) T = μ Tel →
          Γ ⊨[Path.var a.root, σ] V' : Tel) ∧
        Γ.resolveAt? (some (Path.var a.root)) T ≠ ⊥
  | 0, F, _, _, hk, _, _, _, _ => by cases F <;> simp at hk
  | k + 1, F, S, T, hk, hF, hCt, hVt, hnb => by
    match hF with
    | .bot hS => exact absurd hS hnb
    | .top hT =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h
          obtain rfl := Ty.obj.inj (by simpa using h : (μ .nil : Ty s) = μ Tel)
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
    | .obj hS hT hEs =>
        obtain ⟨m, V', hV', hT'⟩ := entriesAt_typed a rfl hCt hS (hVt _ hS) hEs
        refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, view_le (Nat.le_max_left n m) hV,
            closedAtomForm_le (Nat.le_max_left n m) hC,
            entriesAt_le (Nat.le_max_right n m) hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .into (Es := Es) hT hB =>
        have hIH : ∀ (H : Form s) (M : Ty s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
            Γ ⊨[Path.var a.root] H : S ≤ M →
            Γ.resolveAt? (some (Path.var a.root)) M = μ TelM →
            ∃ m V'', viewThrough σ m H a = some V'' ∧ Γ ⊨[Path.var a.root, σ] V'' : TelM := by
          intro H M TelM hlt hH hM
          have hsz : sizeOf H ≤ k := by simp at hk; omega
          obtain ⟨m, V'', hV'', hVt'', _⟩ :=
            viewThrough_typed_aux hroot hV hC k H S M hsz hH hCt hVt hnb
          exact ⟨m, V'', hV'', hVt'' _ hM⟩
        obtain ⟨m, V', hV', hT'⟩ := entriesAtBnds_typed (a := a) rfl V hCt hIH hB
        refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [viewThrough, view_le (Nat.le_max_left n m) hV,
            closedAtomForm_le (Nat.le_max_left n m) hC,
            entriesAt_le (Nat.le_max_right n m) hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .bnd hS hAt hF' =>
        obtain ⟨G, hG, hGt⟩ := (hVt _ hS).bnd_entry hAt
        rw [Ty.weaken_substPath] at hGt
        obtain ⟨H, hH, hHt⟩ := Form.combine_typed hGt hF'
        obtain ⟨m, V', hV', hVt', hnb'⟩ := viewThroughVar_typed hroot _ H _ (Nat.le_refl _) hHt
        refine ⟨max n m + 1, V', ?_, hVt', hnb'⟩
        simpa [viewThrough, view_le (Nat.le_max_left n m) hV, hG.get?, PropForm.bndForm?, hH]
          using viewThrough_le (Nat.le_max_right n m) hV'

theorem viewThrough_typed {F : Form s} {S T : Ty s} {a a' : Atom s} {V : View s} {C : Form s}
    {n : Nat} (hroot : RootViewTyped Γ σ a.root)
    (hF : Γ ⊨[Path.var a.root] F : S ≤ T)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hC : σ ⊢ a ⇓ᶜ[n] (a', C))
    (hCt : Γ ⊨[Path.var a.root] C : Γ.lookupTy a.root ≤ S)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) S = μ Tel →
      Γ ⊨[Path.var a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some (Path.var a.root)) S ≠ ⊥) :
    ∃ m V', viewThrough σ m F a = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) T = μ Tel →
        Γ ⊨[Path.var a.root, σ] V' : Tel) ∧
      Γ.resolveAt? (some (Path.var a.root)) T ≠ ⊥ :=
  viewThrough_typed_aux hroot hV hC (sizeOf F) F S T (Nat.le_refl _) hF hCt hVt hnb

end


/-! ## The path family: the view of a node, and views through typed forms

The twins of `EntryTyped.at_typed`, `entriesAtBnds_typed`, `entriesAt_typed`,
`viewThroughVar_typed` and `viewThrough_typed` for `pathEntryAt`,
`pathEntriesAt`, `pathViewThroughPath` and `pathViewThrough` (P1.8).  The
receiver is a path.  A routed entry reads the block at the root through the
chain and the route (`pathEntryAt`), so the one fact the routes need is the
view of the block at a node through a form typed from the node's type
(`NodeViewTyped`, `pathViewThroughPath_typed`). -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- The equation forms of a witness list with its self instantiated are the
list's own. -/
theorem Witnesses.eqFormsAt_substPath :
    ∀ (W : Witnesses (s,x)) (q : Path s), (W.substPath q).eqFormsAt = W.eqForms
  | .nil, _ => rfl
  | .cons W _ _, q => by
      have ih := Witnesses.eqFormsAt_substPath W q
      simp only [Witnesses.substPath, Witnesses.subst, Witnesses.eqFormsAt,
        Witnesses.eqForms] at ih ⊢
      rw [ih]

/-- The equation forms of a node's witnesses, read under one more binder. -/
theorem Witnesses.eqForms_rename_succ :
    ∀ W : Witnesses s, (W.rename (Rename.succ (k := .var))).eqForms = W.eqFormsAt
  | .nil => rfl
  | .cons W _ _ => by
      simp only [Witnesses.rename, Witnesses.eqForms, Witnesses.eqFormsAt,
        Witnesses.eqForms_rename_succ W]

theorem Witnesses.eqFormsAt_noBnd : ∀ W : Witnesses s, W.eqFormsAt.NoBnd
  | .nil => by rw [Witnesses.eqFormsAt]; exact View.NoBnd.nil
  | .cons W _ _ => by
      rw [Witnesses.eqFormsAt]
      exact (Witnesses.eqFormsAt_noBnd W).cons (by intro G h; cases h)

/-- The view of a block has no bound entries. -/
theorem Block.precView_noBnd : ∀ (B : Block s) (p : Path s) (V : View s),
    B.precView p = some V → V.NoBnd
  | .obj W ls vls _, p, V, h => by
      simp only [Block.precView, Option.some.injEq] at h
      subst h
      exact Fields.hasValForms_noBnd vls _
        (Fields.hasForms_noBnd p ls _ (Witnesses.eqFormsAt_noBnd W))
  | .fwd _, _, _, h => by simp [Block.precView] at h

theorem Store.blockView_noBnd {r : Path s} {V : View s} (h : σ.blockView r = some V) :
    V.NoBnd := by
  unfold Store.blockView at h
  cases hb : σ.blockOf r with
  | none => rw [hb] at h; cases h
  | some B => rw [hb] at h; exact Block.precView_noBnd B r V h

/-! ### The precise view at a root -/

/-- Equation forms, typed at a root whose definitions the witnesses give. -/
theorem eqForms_typedAt (r : Path s) (W₀ : Witnesses (s,x))
    (hdef : ∀ ℓ, Γ.resolve (Ty.sel r ℓ) = Γ.resolve ((W₀.get ℓ).substPath r)) :
    ∀ W : Witnesses (s,x), Γ ⊨[r, σ] W.eqForms : W₀.eqEntriesOf .here W
  | .nil => by simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]; exact .nil
  | .cons W ℓ _ => by
      simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]
      exact .eq (eqForms_typedAt r W₀ hdef W) (hdef ℓ)

/-- Presence forms at a root, typed. -/
theorem hasForms_typedAt (r : Path s) :
    ∀ (ls : List Label) (V : View s) (Tel : Telescope (s,x)),
      Γ ⊨[r, σ] V : Tel → (∀ ℓ ∈ ls, σ.HasFieldP r ℓ) →
      Γ ⊨[r, σ] Fields.hasForms r V ls : Tel.hasEntries ls
  | [], _, _, hV, _ => hV
  | ℓ :: ls, _, _, hV, hF =>
      hasForms_typedAt r ls _ _ (.has hV (hF ℓ (by simp))) (fun ℓ' h => hF ℓ' (by simp [h]))

/-- Stable-presence forms at a root, typed. -/
theorem hasValForms_typedAt (r : Path s) :
    ∀ (ls : List Label) (V : View s) (Tel : Telescope (s,x)),
      Γ ⊨[r, σ] V : Tel → (∀ ℓ ∈ ls, σ.HasValFieldP r ℓ) →
      Γ ⊨[r, σ] Fields.hasValForms V ls : Tel.hasValEntries ls
  | [], _, _, hV, _ => hV
  | ℓ :: ls, _, _, hV, hF =>
      hasValForms_typedAt r ls _ _ (.hasVal hV (hF ℓ (by simp)))
        (fun ℓ' h => hF ℓ' (by simp [h]))

/-- The view of the block the store gives a root, typed at the literal
telescope whose definitions are the block's. -/
theorem blockView_typedAt {r : Path s} {Wb : Witnesses s} {ls vls : List Label}
    {ch : Children s} (hb : σ.blockOf r = some (.obj Wb ls vls ch)) (W₀ : Witnesses (s,x))
    (hdef : ∀ ℓ, Γ.resolve (Ty.sel r ℓ) = Γ.resolve ((W₀.get ℓ).substPath r))
    (hcount : Wb.eqFormsAt = W₀.eqForms) :
    σ.blockView r = some (Fields.hasValForms (Fields.hasForms r W₀.eqForms ls) vls) ∧
      Γ ⊨[r, σ] Fields.hasValForms (Fields.hasForms r W₀.eqForms ls) vls :
        Telescope.ofLiteral W₀ ls vls := by
  refine ⟨by simp [Store.blockView, hb, Block.precView, hcount], ?_⟩
  unfold Telescope.ofLiteral Witnesses.eqEntries
  exact hasValForms_typedAt r vls _ _
    (hasForms_typedAt r ls _ _ (eqForms_typedAt r W₀ hdef W₀)
      (fun ℓ h => ⟨Wb, ls, vls, ch, hb, h⟩))
    (fun ℓ h => ⟨Wb, ls, vls, ch, hb, h⟩)

/-- The view of the block at a root is typed at the node's type.  The twin of
`RootViewTyped` for a path root, read off the block the store gives it. -/
def NodeViewTyped (Γ : Ctx s) (σ : Store s) (r : Path s) : Prop :=
  ∃ V, σ.blockView r = some V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve (Γ.nodeTy r) = μ Tel → Γ ⊨[r, σ] V : Tel) ∧
    Γ.resolve (Γ.nodeTy r) ≠ ⊥

/-- The view of a node, at the shapes opened at the node. -/
theorem NodeViewTyped.opened {r : Path s} (h : NodeViewTyped Γ σ r) :
    ∃ V, σ.blockView r = some V ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some r) (Γ.nodeTy r) = μ Tel →
        Γ ⊨[r, σ] V : Tel) ∧
      Γ.resolveAt? (some r) (Γ.nodeTy r) ≠ ⊥ := by
  obtain ⟨V, hV, hVt, hnb⟩ := h
  refine ⟨V, hV, fun Tel h' => ?_, fun h' => hnb (Ty.unfoldAt_eq_bot h')⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Ty.unfoldAt_eq_obj h'
  exact ViewTyped_unfold (hVt Tel₀ h₀)

/-- The view of a node below a variable, over a typed store. -/
theorem Store.Typed.nodeView_sel (hσ : ⊢ σ : Γ) {p : Path s} {a : Label} {Wb : Witnesses s}
    {ls vls : List Label} {ch : Children s}
    (hn : Γ.nodeBlock (.sel p a) = some (.obj Wb ls vls ch)) :
    NodeViewTyped Γ σ (.sel p a) := by
  have hb := Store.Typed.blockOf_node hσ hn
  have hty : Γ.nodeTy (.sel p a) = μ (Telescope.ofLiteral (Wb.rename Rename.succ) ls vls) := by
    rw [Ctx.nodeTy_sel, hn]
  have hlk := Ctx.nodeBlock_lookupBlock Γ hn
  have hdef : ∀ ℓ, Γ.resolve (Ty.sel (.sel p a) ℓ)
      = Γ.resolve (((Wb.rename Rename.succ).get ℓ).substPath (.sel p a)) := by
    intro ℓ
    rw [Witnesses.get_rename]
    have hw := Ty.weaken_substPath (Wb.get ℓ) (.sel p a)
    simp only [Ty.weaken] at hw
    rw [hw]
    exact Ctx.resolve_selP_some (by simp [Ctx.lookupDefP, hlk])
  obtain ⟨hV, hVt⟩ := blockView_typedAt hb (Wb.rename Rename.succ) hdef
    (Witnesses.eqForms_rename_succ Wb).symm
  refine ⟨_, hV, fun Tel h => ?_, by rw [hty]; simp⟩
  rw [hty, Ctx.resolve_obj] at h
  obtain rfl := Ty.obj.inj h
  exact hVt

/-- The view of a store variable's block is its literal's precise view. -/
theorem Store.blockView_var {x : BVar s .var} (hlit : (σ.lookup x).IsLiteral) :
    σ.blockView (.var x) = some ((σ.lookup x).precView (.var x)) := by
  have hb : σ.blockOf (.var x) = some ((σ.lookup x).blocksAt (.var x)) := rfl
  cases hl : σ.lookup x with
  | lam S t => rw [Store.blockView, hb, hl]; rfl
  | obj W F =>
      rw [Store.blockView, hb, hl]
      show some (Fields.hasValForms
          (Fields.hasForms (.var x) (W.substPath (.var x)).eqFormsAt F.labels) F.valLabels) = _
      rw [Witnesses.eqFormsAt_substPath]
      rfl
  | cast v e => rw [hl] at hlit; exact hlit.elim

/-- The view of a store variable's block, typed at the variable's type. -/
theorem Store.Typed.nodeView_var (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    NodeViewTyped Γ σ (.var x) := by
  have hv := hσ.lookup x
  have hlit := hσ.isLiteral_lookup x
  refine ⟨_, Store.blockView_var hlit, ?_⟩
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      refine ⟨fun Tel h => ?_, by rw [Ctx.nodeTy_var, hT]; simp⟩
      rw [Ctx.nodeTy_var, hT] at h
      simp at h
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      refine ⟨fun Tel h => ?_, by rw [Ctx.nodeTy_var, hT]; simp⟩
      rw [Ctx.nodeTy_var, hT, Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      have hb : σ.blockOf (.var x) = some (.obj (W.substPath (.var x)) F.labels F.valLabels
          ((F.children (.var .here)).substPath (.var x))) := by
        show some ((σ.lookup x).blocksAt (.var x)) = _
        rw [hl]
        rfl
      have hdef : ∀ ℓ, Γ.resolve (Ty.sel (.var x) ℓ)
          = Γ.resolve ((W.get ℓ).substPath (.var x)) := by
        intro ℓ
        rw [Ty.substPath_var]
        have hd := hσ.lookupDef x ℓ
        rw [hl] at hd
        exact Ctx.resolve_sel_some hd
      obtain ⟨_, hVt⟩ := blockView_typedAt hb W hdef (Witnesses.eqFormsAt_substPath W _)
      exact hVt
  | cast v e => rw [hl] at hlit; exact hlit.elim

/-- The precise view of a location is typed at its type: the base's
`precView_typed`, whose root is now the path `.var x`. -/
theorem Store.Typed.precView_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) : RootViewTyped Γ σ x := by
  obtain ⟨V, hV, hVt, hnb⟩ := hσ.nodeView_var x
  rw [Store.blockView_var (hσ.isLiteral_lookup x)] at hV
  obtain rfl := Option.some.inj hV
  exact ⟨hVt, hnb⟩

/-! ### Entries at a path -/

/-- Instantiating one typed entry at the typed view of the object type the
entry reads, at a path root.  `EntryTyped.at_typed` with the receiver a path. -/
theorem EntryTyped.pathAt_typed {r : Path s} {M : Ty s} {TelM : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} {C : Form s} {V : View s}
    (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ M) (hM : Γ.resolveAt? (some r) M = μ TelM)
    (hV : Γ ⊨[r, σ] V : TelM) (hE : EntryTyped Γ (some r) TelM E P) :
    ∃ m Q, pathEntryAt σ m r C V E = some Q ∧
      ∀ {V₀ : View s} {Tel₀ : Telescope (s,x)},
        Γ ⊨[r, σ] V₀ : Tel₀ → Γ ⊨[r, σ] V₀ ▹ Q : Tel₀ ▹ P := by
  have hop : Γ.resolveAt? (some r) (μ TelM) = μ TelM := Ctx.resolveAt?_obj_self hM
  match hE with
  | .le (pre := pre) (post := post) hh hpre hpost =>
      have hpre' := hpre.inst r
      have hpost' := hpost.inst r
      cases hh with
      | le hAt =>
          obtain ⟨G, hG, hGt⟩ := hV.le_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' hGt
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [pathEntryAt, Hole.index, hG.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
      | eq hAt =>
          obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE')
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [pathEntryAt, Hole.index, hq.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
      | eqSym hAt =>
          obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE'.symm)
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          exact ⟨1, .le H₂, by simp [pathEntryAt, Hole.index, hq.get?, hH₁, hH₂],
            fun hV₀ => .le hV₀ hH₂t⟩
  | .eq hAt =>
      obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
      exact ⟨1, .eq, by simp [pathEntryAt, hq.get?], fun hV₀ => .eq hV₀ hE'⟩
  | .eqSym hAt =>
      obtain ⟨hq, hE'⟩ := hV.eq_entry hAt
      exact ⟨1, .eq, by simp [pathEntryAt, hq.get?], fun hV₀ => .eq hV₀ hE'.symm⟩
  | .has (ℓ := ℓ) hAt =>
      obtain ⟨hq, hHF⟩ := hV.has_entry hAt
      exact ⟨1, .has r ℓ, by simp [pathEntryAt, hq.get?], fun hV₀ => .has hV₀ hHF⟩
  | .hasVal (ℓ := ℓ) hAt =>
      obtain ⟨hq, hHF⟩ := hV.hasVal_entry hAt
      exact ⟨1, .hasVal ℓ, by simp [pathEntryAt, hq.get?], fun hV₀ => .hasVal hV₀ hHF⟩
  | .hasOfVal (ℓ := ℓ) hAt =>
      obtain ⟨hq, hHF⟩ := hV.hasVal_entry hAt
      exact ⟨1, .has r ℓ, by simp [pathEntryAt, hq.get?],
        fun hV₀ => .has hV₀ (Store.hasField_of_hasValFieldP hHF)⟩
  | .alias (q := q) hAt =>
      obtain ⟨hq, hb⟩ := hV.alias_entry hAt
      exact ⟨1, .alias (q.substPath r), by simp [pathEntryAt, hq.get?],
        fun hV₀ => .alias hV₀ hb⟩
  | .aliasTo (p := p) (q := q) hρ hb =>
      obtain rfl : p = r := (Option.some.inj hρ).symm
      exact ⟨1, .alias q, by simp [pathEntryAt], fun hV₀ => ViewTyped.aliasTo hV₀ hb⟩
  | .bnd (j := k) hG =>
      have hG' : Γ ⊨[r] (Form.bnd k .id) : M ≤ _ := hG.srcRes (hM.trans hop.symm)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG'
      exact ⟨1, .bnd H, by simp [pathEntryAt, hH],
        fun hV₀ => .bnd hV₀ (by rwa [Ty.weaken_substPath])⟩
  | .bndId (X := X) (j := k) hAt =>
      have hX : X = ((X.substPath r)↑) := Telescope.opened_bnd (Ctx.resolveAt?_opened hM) hAt
      have hAt' : TelM ∋ (k ↦ ⊑ ((X.substPath r)↑)) := by rw [← hX]; exact hAt
      have hBnd : Γ ⊨[r] (Form.bnd k .id) : M ≤ X.substPath r := .bnd hM hAt' (.id rfl)
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hBnd
      exact ⟨1, .bnd H, by simp [pathEntryAt, hH], fun hV₀ => .bnd hV₀ hHt⟩

/-- Applying typed view-free entries at a path root.  A routed entry reads the
block at the root through the chain composed with its route, so the view of
the node through that composite is what the hypothesis supplies. -/
theorem pathEntriesAtBnds_typed {r : Path s} {S : Ty s} {C : Form s}
    (V : View s) (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ S) :
    ∀ {Es : Entries s} {Tel : Telescope (s,x)},
      (∀ (H C' : Form s) (M : Ty s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
        Γ ⊨[r] H : S ≤ M → C.combine H = some C' → Γ.resolveAt? (some r) M = μ TelM →
        ∃ m V'', pathViewThroughPath σ m C' r = some V'' ∧ Γ ⊨[r, σ] V'' : TelM) →
      BndsTyped Γ (some r) S Es Tel →
      ∃ m V', pathEntriesAt σ m r C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel
  | _, _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, hIH, .cons hB' hG => by
      obtain ⟨m, V', hV', hT⟩ := pathEntriesAtBnds_typed V hC
        (fun H C' M TelM hlt => hIH H C' M TelM (by simp; omega)) hB'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hC hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Ty.weaken_substPath])⟩
      simp [pathEntriesAt, pathEntriesAt_le (Nat.le_succ m) hV', pathEntryAt, hH]
  | _, _, hIH, .thru hB' hH hM hE => by
      obtain ⟨m₁, V₁, hV₁, hT₁⟩ := pathEntriesAtBnds_typed V hC
        (fun H' C' M' TelM' hlt => hIH H' C' M' TelM' (by simp; omega)) hB'
      obtain ⟨C', hC', hC'T⟩ := Form.combine_typed hC hH
      obtain ⟨m₂, V₂, hV₂, hT₂⟩ := hIH _ _ _ _ (by simp; omega) hH hC' hM
      obtain ⟨m₃, Q, hQ, hQt⟩ := EntryTyped.pathAt_typed hC'T hM hT₂ hE
      refine ⟨max m₁ (max m₂ m₃) + 2, V₁ ▹ Q, ?_, hQt hT₁⟩
      have h₁ := pathEntriesAt_le (σ := σ) (r := r) (C := C) (V := V)
        (Nat.le_trans (Nat.le_max_left m₁ (max m₂ m₃)) (Nat.le_succ _)) hV₁
      have h₂ := pathViewThroughPath_le (σ := σ)
        (Nat.le_trans (Nat.le_max_left m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hV₂
      have h₃ := pathEntryAt_le (σ := σ) (r := r)
        (Nat.le_trans (Nat.le_max_right m₂ m₃) (Nat.le_max_right m₁ (max m₂ m₃))) hQ
      simp [pathEntriesAt, h₁, pathEntryAt, h₂, hC', h₃]
  | _, _, hIH, .aliasTo hB' hρ hb => by
      obtain ⟨m, V', hV', hT⟩ := pathEntriesAtBnds_typed V hC
        (fun H C' M TelM hlt => hIH H C' M TelM (by simp; omega)) hB'
      obtain rfl := Option.some.inj hρ
      refine ⟨m + 2, _, ?_, ViewTyped.aliasTo hT hb⟩
      simp [pathEntriesAt, pathEntriesAt_le (Nat.le_succ m) hV', pathEntryAt]

/-- One more typed entry at a path root. -/
theorem pathEntriesAt_step {r : Path s} {Tel₁ : Telescope (s,x)}
    {V : View s} {C : Form s} {S : Ty s}
    (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ S) (hS : Γ.resolveAt r S = μ Tel₁)
    (hV : Γ ⊨[r, σ] V : Tel₁) {Es : Entries s} {Tel₂ : Telescope (s,x)} {E : Entry s}
    {P : Proposition (s,x)}
    (hEs : ∃ m V', pathEntriesAt σ m r C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂)
    (hE : EntryTyped Γ (some r) Tel₁ E P) :
    ∃ m V', pathEntriesAt σ m r C V (Es ▹ E) = some V' ∧ Γ ⊨[r, σ] V' : Tel₂ ▹ P := by
  obtain ⟨m, V', hV', hT⟩ := hEs
  obtain ⟨m', Q, hQ, hQt⟩ := EntryTyped.pathAt_typed hC hS hV hE
  refine ⟨max m m' + 2, V' ▹ Q, ?_, hQt hT⟩
  have h₁ := pathEntriesAt_le (Nat.le_trans (Nat.le_max_left m m') (Nat.le_succ _)) hV'
  have h₂ := pathEntryAt_le (Nat.le_trans (Nat.le_max_right m m') (Nat.le_succ _)) hQ
  simp [pathEntriesAt, h₁, h₂]

/-- Applying typed entries to a typed view at a path root. -/
theorem pathEntriesAt_typed {r : Path s} {Tel₁ : Telescope (s,x)}
    {V : View s} {C : Form s} {S : Ty s}
    (hC : Γ ⊨[r] C : Γ.nodeTy r ≤ S) (hS : Γ.resolveAt r S = μ Tel₁)
    (hV : Γ ⊨[r, σ] V : Tel₁) :
    ∀ {Es : Entries s} {Tel₂ : Telescope (s,x)}, EntriesTyped Γ (some r) Tel₁ Es Tel₂ →
      ∃ m V', pathEntriesAt σ m r C V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂
  | _, _, .nil => ⟨1, .nil, rfl, .nil⟩
  | _, _, .le hEs' hh hpre hpost =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.le hh hpre hpost)
  | _, _, .eq hEs' hAt => pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.eq hAt)
  | _, _, .eqSym hEs' hAt =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.eqSym hAt)
  | _, _, .has hEs' hAt => pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.has hAt)
  | _, _, .hasVal hEs' hAt =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.hasVal hAt)
  | _, _, .hasOfVal hEs' hAt =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.hasOfVal hAt)
  | _, _, .alias hEs' hAt =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.alias hAt)
  | _, _, .aliasTo hEs' hρ hb =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.aliasTo hρ hb)
  | _, _, .bndId hEs' hAt =>
      pathEntriesAt_step hC hS hV (pathEntriesAt_typed hC hS hV hEs') (.bndId hAt)
  | _, _, .bnd hEs' hG => by
      have hSA : Γ.resolveAt? (some r) S = μ Tel₁ := hS
      have hop : Γ.resolveAt? (some r) (μ Tel₁) = μ Tel₁ := Ctx.resolveAt?_obj_self hSA
      have hCT : Γ ⊨[r] C : Γ.nodeTy r ≤ μ Tel₁ := hC.tgtRes (hSA.trans hop.symm)
      obtain ⟨m, V', hV', hT⟩ := pathEntriesAt_typed hC hS hV hEs'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hCT hG
      refine ⟨m + 2, V' ▹ .bnd H, ?_, .bnd hT (by rwa [Ty.weaken_substPath])⟩
      simp [pathEntriesAt, pathEntriesAt_le (Nat.le_succ m) hV', pathEntryAt, hH]

/-! ### Views through typed forms -/

/-- The view of a node through a form typed from the node's type.  The twin
of `viewThroughVar_typed`. -/
theorem pathViewThroughPath_typed {r : Path s} (hroot : NodeViewTyped Γ σ r) :
    ∀ (k : Nat) (F : Form s) (T : Ty s), sizeOf F ≤ k →
      Γ ⊨[r] F : Γ.nodeTy r ≤ T →
      ∃ m V', pathViewThroughPath σ m F r = some V' ∧
        (∀ Tel : Telescope (s,x), Γ.resolveAt? (some r) T = μ Tel → Γ ⊨[r, σ] V' : Tel) ∧
        Γ.resolveAt? (some r) T ≠ ⊥
  | 0, F, _, hk, _ => by cases F <;> simp at hk
  | k + 1, F, T, hk, hF => by
    obtain ⟨V₀, hV₀, hrv, hrb⟩ := hroot.opened
    have hCid : Γ ⊨[r] (Form.id) : Γ.nodeTy r ≤ Γ.nodeTy r := .id rfl
    match hF with
    | .bot hS => exact absurd hS hrb
    | .top hT =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h
          obtain rfl := Ty.obj.inj (by simpa using h : (μ .nil : Ty s) = μ Tel)
          exact .nil
        · rw [hT]; simp
    | .id hres =>
        exact ⟨1, V₀, by simp [pathViewThroughPath, hV₀],
          fun Tel h => hrv Tel (hres.trans h), by rw [← hres]; exact hrb⟩
    | .eqv hres =>
        exact ⟨1, V₀, by simp [pathViewThroughPath, hV₀],
          fun Tel h => hrv Tel (hres.trans h), by rw [← hres]; exact hrb⟩
    | .pi _ hT _ _ =>
        refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
        · rw [hT] at h; exact absurd h (by simp)
        · rw [hT]; simp
    | .obj hS hT hEs =>
        obtain ⟨m, V', hV', hT'⟩ := pathEntriesAt_typed hCid hS (hrv _ hS) hEs
        refine ⟨m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [pathViewThroughPath, hV₀, hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .into (Es := Es) hT hB =>
        have hIH : ∀ (H C' : Form s) (M : Ty s) (TelM : Telescope (s,x)),
            sizeOf H < sizeOf Es →
            Γ ⊨[r] H : Γ.nodeTy r ≤ M → Form.combine .id H = some C' →
            Γ.resolveAt? (some r) M = μ TelM →
            ∃ m V'', pathViewThroughPath σ m C' r = some V'' ∧ Γ ⊨[r, σ] V'' : TelM := by
          intro H C' M TelM hlt hH hC' hM
          rw [Form.combine_id_left] at hC'
          obtain rfl := Option.some.inj hC'
          have hsz : sizeOf H ≤ k := by simp at hk; omega
          obtain ⟨m, V'', hV'', hVt'', _⟩ := pathViewThroughPath_typed hroot k H M hsz hH
          exact ⟨m, V'', hV'', hVt'' _ hM⟩
        obtain ⟨m, V', hV', hT'⟩ := pathEntriesAtBnds_typed V₀ hCid hIH hB
        refine ⟨m + 1, V', ?_, fun Tel h => ?_, ?_⟩
        · simp [pathViewThroughPath, hV₀, hV']
        · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
        · rw [hT]; simp
    | .bnd hS hAt _ =>
        obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
        exact absurd hG (Store.blockView_noBnd hV₀ _ _)

/-- The view of a stable path through a typed form, from the view and the
chain of the path.  The twin of `viewThrough_typed`.  A routed entry and a
bound cast read the node through a form typed from the node's type, which
`pathViewThroughPath_typed` covers, so no induction on the form is needed. -/
theorem pathViewThrough_typed {F : Form s} {S T : Ty s} {P : PathCo s} {V : View s}
    {C : Form s} {n : Nat} (hroot : NodeViewTyped Γ σ P.path)
    (hF : Γ ⊨[P.path] F : S ≤ T)
    (hV : pathView σ n P = some V)
    (hC : pathChainForm σ n P = some C)
    (hCt : Γ ⊨[P.path] C : Γ.nodeTy P.path ≤ S)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some P.path) S = μ Tel →
      Γ ⊨[P.path, σ] V : Tel)
    (hnb : Γ.resolveAt? (some P.path) S ≠ ⊥) :
    ∃ m V', pathViewThrough σ m F P = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some P.path) T = μ Tel →
        Γ ⊨[P.path, σ] V' : Tel) ∧
      Γ.resolveAt? (some P.path) T ≠ ⊥ := by
  have hnode : ∀ (C' : Form s) (M : Ty s) (TelM : Telescope (s,x)),
      Γ ⊨[P.path] C' : Γ.nodeTy P.path ≤ M → Γ.resolveAt? (some P.path) M = μ TelM →
      ∃ m V'', pathViewThroughPath σ m C' P.path = some V'' ∧ Γ ⊨[P.path, σ] V'' : TelM := by
    intro C' M TelM hC' hM
    obtain ⟨m, V'', hV'', hVt'', _⟩ :=
      pathViewThroughPath_typed hroot (sizeOf C') C' M (Nat.le_refl _) hC'
    exact ⟨m, V'', hV'', hVt'' _ hM⟩
  match hF with
  | .bot hS => exact absurd hS hnb
  | .top hT =>
      refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h
        obtain rfl := Ty.obj.inj (by simpa using h : (μ .nil : Ty s) = μ Tel)
        exact .nil
      · rw [hT]; simp
  | .id hres =>
      exact ⟨n + 1, V, by simp [pathViewThrough, hV], fun Tel h => hVt Tel (hres.trans h),
        by rw [← hres]; exact hnb⟩
  | .eqv hres =>
      exact ⟨n + 1, V, by simp [pathViewThrough, hV], fun Tel h => hVt Tel (hres.trans h),
        by rw [← hres]; exact hnb⟩
  | .pi _ hT _ _ =>
      refine ⟨1, .nil, rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h; exact absurd h (by simp)
      · rw [hT]; simp
  | .obj hS hT hEs =>
      obtain ⟨m, V', hV', hT'⟩ := pathEntriesAt_typed hCt hS (hVt _ hS) hEs
      refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
      · simp [pathViewThrough, pathView_le (Nat.le_max_left n m) hV,
          pathChainForm_le (Nat.le_max_left n m) hC,
          pathEntriesAt_le (Nat.le_max_right n m) hV']
      · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
      · rw [hT]; simp
  | .into hT hB =>
      obtain ⟨m, V', hV', hT'⟩ := pathEntriesAtBnds_typed V hCt
        (fun H C' M TelM _ hH hC' hM => by
          obtain ⟨C₁, hC₁, hC₁t⟩ := Form.combine_typed hCt hH
          rw [hC₁] at hC'
          obtain rfl := Option.some.inj hC'
          exact hnode _ _ _ hC₁t hM) hB
      refine ⟨max n m + 1, V', ?_, fun Tel h => ?_, ?_⟩
      · simp [pathViewThrough, pathView_le (Nat.le_max_left n m) hV,
          pathChainForm_le (Nat.le_max_left n m) hC,
          pathEntriesAt_le (Nat.le_max_right n m) hV']
      · rw [hT] at h; obtain rfl := Ty.obj.inj h; exact hT'
      · rw [hT]; simp
  | .bnd hS hAt hF' =>
      obtain ⟨G, hG, hGt⟩ := (hVt _ hS).bnd_entry hAt
      rw [Ty.weaken_substPath] at hGt
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hGt hF'
      obtain ⟨m, V', hV', hVt', hnb'⟩ :=
        pathViewThroughPath_typed hroot _ H _ (Nat.le_refl _) hHt
      refine ⟨max n m + 1, V', ?_, hVt', hnb'⟩
      simpa [pathViewThrough, pathView_le (Nat.le_max_left n m) hV, hG.get?,
        PropForm.bndForm?, hH] using pathViewThroughPath_le (Nat.le_max_right n m) hV'

end

end FCdot

end Paths
