import Coercions.FCdot.FormTyping
import Coercions.FCdot.Preservation

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

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Typedness depends on an endpoint only through its shape -/

theorem FormTyped.srcRes {F : Form s} {S S' T : Ty s}
    (h : Γ.resolve S = Γ.resolve S') (hF : Γ ⊨ F : S' ≤ T) : Γ ⊨ F : S ≤ T := by
  cases hF with
  | bot hS => exact .bot (h.trans hS)
  | top hT => exact .top hT
  | id hres => exact .id (h.trans hres)
  | eqv hres => exact .eqv (h.trans hres)
  | pi hS hT hd hc => exact .pi (h.trans hS) hT hd hc
  | obj hS hT hEs => exact .obj (h.trans hS) hT hEs

theorem FormTyped.tgtRes {F : Form s} {S T T' : Ty s}
    (h : Γ.resolve T' = Γ.resolve T) (hF : Γ ⊨ F : S ≤ T') : Γ ⊨ F : S ≤ T := by
  cases hF with
  | bot hS => exact .bot hS
  | top hT => exact .top (h.symm.trans hT)
  | id hres => exact .id (hres.trans h)
  | eqv hres => exact .eqv (hres.trans h)
  | pi hS hT hd hc => exact .pi hS (h.symm.trans hT) hd hc
  | obj hS hT hEs => exact .obj hS (h.symm.trans hT) hEs

theorem ChainTyped.srcRes {r : BVar s .var} {F : Form s} {S S' T : Ty s}
    (h : Γ.resolveAt r S = Γ.resolveAt r S') (hF : Γ ⊨[r] F : S' ≤ T) : Γ ⊨[r] F : S ≤ T := by
  rw [ChainTyped, h]; exact hF

theorem ChainTyped.tgtRes {r : BVar s .var} {F : Form s} {S T T' : Ty s}
    (h : Γ.resolveAt r T' = Γ.resolveAt r T) (hF : Γ ⊨[r] F : S ≤ T') : Γ ⊨[r] F : S ≤ T := by
  rw [ChainTyped, ← h]; exact hF

/-! ## Opening a telescope at a root

Typedness of entries is stable under opening both telescopes at a root: a
closed side stays closed, and holes follow the renaming. -/

theorem Ty.weaken_inj {A B : Ty s} (h : (A.weaken (k := .var)) = B.weaken) : A = B :=
  Ty.rename_inj _ _ _ Rename.succ_injective h

theorem SideTyped.open (r : BVar s .var) {F : Form s} {S X : Ty (s,x)}
    (h : SideTyped Γ F S X) : SideTyped Γ F ((S⟦r⟧)↑) ((X⟦r⟧)↑) := by
  cases h with
  | id => exact .id
  | closed hF => rw [Ty.weaken_substVar, Ty.weaken_substVar]; exact .closed hF

theorem Telescope.HoleAt.open (r : BVar s .var) {Tel : Telescope (s,x)} {h : Hole}
    {X Y : Ty (s,x)} (hh : Tel.HoleAt h X Y) :
    ((Tel⟦r⟧)↑).HoleAt h ((X⟦r⟧)↑) ((Y⟦r⟧)↑) := by
  cases hh with
  | le hAt => exact .le ((hAt.rename _).rename _)
  | eq hAt => exact .eq ((hAt.rename _).rename _)
  | eqSym hAt => exact .eqSym ((hAt.rename _).rename _)

theorem EntriesTyped.open (r : BVar s .var) {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) : Γ ⊨ Es : ((Tel₁⟦r⟧)↑) ⇒ ((Tel₂⟦r⟧)↑) := by
  match h with
  | .nil => exact .nil
  | .le h' hh hpre hpost =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_le,
        Proposition.weaken_le]
      exact .le (EntriesTyped.open r h') (hh.open r) (hpre.open r) (hpost.open r)
  | .eq h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq]
      exact .eq (EntriesTyped.open r h') ((hAt.rename _).rename _)
  | .eqSym h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq]
      exact .eqSym (EntriesTyped.open r h') ((hAt.rename _).rename _)
  | .has h' hAt =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_has,
        Proposition.weaken_has]
      exact .has (EntriesTyped.open r h') ((hAt.rename _).rename _)

/-! ## Plain typedness gives typedness at the shapes opened at any root

The opened shape of an endpoint is a non-name type determined by the plain
shape, and resolution is the identity on it. -/

theorem FormTyped.atRoot {F : Form s} {S T : Ty s} (r : BVar s .var)
    (h : Γ ⊨ F : S ≤ T) : Γ ⊨[r] F : S ≤ T := by
  cases h with
  | bot hS => exact .bot (by simp [Ctx.resolveAt, hS])
  | top hT => exact .top (by simp [Ctx.resolveAt, hT])
  | id hres => exact .id (by simp only [Ctx.resolveAt]; rw [hres])
  | eqv hres => exact .eqv (by simp only [Ctx.resolveAt]; rw [hres])
  | pi hS hT hd hc => exact .pi (by simp [Ctx.resolveAt, hS]) (by simp [Ctx.resolveAt, hT]) hd hc
  | obj hS hT hEs =>
      exact .obj (by simp [Ctx.resolveAt, hS]) (by simp [Ctx.resolveAt, hT]) (hEs.open r)

/-! ## Entries by position -/

theorem EntriesTyped.length {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) : Es.length = Tel₂.length := by
  match h with
  | .nil => rfl
  | .le h' _ _ _ => simp [Entries.length, Telescope.length, h'.length]
  | .eq h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .eqSym h' _ => simp [Entries.length, Telescope.length, h'.length]
  | .has h' _ => simp [Entries.length, Telescope.length, h'.length]

/-- Entries typed from an empty source prove nothing. -/
theorem EntriesTyped.nil_src {Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : .nil ⇒ Tel₂) : Tel₂ = .nil := by
  match h with
  | .nil => rfl
  | .le _ hh _ _ => cases hh with | le hAt => cases hAt | eq hAt => cases hAt | eqSym hAt => cases hAt
  | .eq _ hAt => cases hAt
  | .eqSym _ hAt => cases hAt
  | .has _ hAt => cases hAt

/-- The entry at an inclusion of the target is a template. -/
theorem EntriesTyped.At_le {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) {j : Nat} {S T : Ty (s,x)} (hAt : Tel₂ ∋ (j ↦ S ⊑ T)) :
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

/-- The entry at an equality of the target reads a source equality, possibly
flipped. -/
theorem EntriesTyped.At_eq {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) {j : Nat} {X Y : Ty (s,x)} (hAt : Tel₂ ∋ (j ↦ X ≐ Y)) :
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

/-- The entry at a presence proposition of the target is a presence entry
pointing at a presence proposition of the source. -/
theorem EntriesTyped.At_has {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s}
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) {j : Nat} {ℓ : Label} (hAt : Tel₂ ∋ (j ↦ ∋ ℓ)) :
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

theorem combine_typed_aux : ∀ n : Nat,
    (∀ (F G : Form s) (S M T : Ty s), sizeOf F + sizeOf G ≤ n →
      Γ ⊨ F : S ≤ M → Γ ⊨ G : M ≤ T → ∃ H, F.combine G = some H ∧ Γ ⊨ H : S ≤ T) ∧
    (∀ (Es₁ Es₂ : Entries s) (Tel₁ TelM Tel₂ : Telescope (s,x)), sizeOf Es₁ + sizeOf Es₂ ≤ n →
      Γ ⊨ Es₁ : Tel₁ ⇒ TelM → Γ ⊨ Es₂ : TelM ⇒ Tel₂ →
      ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ Γ ⊨ Es : Tel₁ ⇒ Tel₂)
  | 0 => by
      refine ⟨?_, ?_⟩
      · intro F G _ _ _ hn; cases F <;> simp at hn
      · intro Es₁ Es₂ _ _ _ hn; cases Es₁ <;> simp at hn
  | n + 1 => by
      obtain ⟨ihF, ihE⟩ := combine_typed_aux n
      -- sides compose, at smaller size
      have side : ∀ (F G : Form s) (S X Y : Ty (s,x)), sizeOf F + sizeOf G ≤ n →
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
            generalize hX : (B.weaken : Ty (s,x)) = X at h₂
            cases h₂ with
            | id => rw [← hX]; exact ⟨F, Form.combine_id_right F, .closed hF⟩
            | closed hG =>
                obtain rfl := Ty.weaken_inj hX
                obtain ⟨H, hH, hHt⟩ := ihF F G _ _ _ hn hF hG
                exact ⟨H, hH, .closed hHt⟩
      refine ⟨?_, ?_⟩
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
                obtain rfl := hEs.nil_src
                exact ⟨.top, by simp [Form.combine], .top hT⟩
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
                obtain ⟨Es, hEs', hT'⟩ := ihE _ _ _ _ _ (by simp at hn; omega) hEs hEs₂
                exact ⟨.obj Es, by simp [Form.combine, hEs'], .obj hS hT hT'⟩
      · intro Es₁ Es₂ Tel₁ TelM Tel₂ hn h₁ h₂
        match h₂ with
        | .nil => exact ⟨.nil, by simp [Entries.through], .nil⟩
        | .le (pre := pre) (post := post) h₂' hh hpre hpost =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) h₁ h₂'
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
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
            refine ⟨Es ▹ .eq k b, ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eq hT hk
              · exact .eqSym hT hk
        | .eqSym h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) h₁ h₂'
            obtain ⟨k, b, hE, hk⟩ := h₁.At_eq hAt
            refine ⟨Es ▹ .eq k (!b), ?_, ?_⟩
            · simp [Entries.through, hEs, Entry.through, hE.get?]
            · rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
              · exact .eqSym hT hk
              · exact .eq hT hk
        | .has h₂' hAt =>
            obtain ⟨Es, hEs, hT⟩ := ihE _ _ _ _ _ (by simp at hn; omega) h₁ h₂'
            obtain ⟨j', hj', hT'⟩ := h₁.At_has hAt
            exact ⟨Es ▹ .has j', by simp [Entries.through, hEs, Entry.through, hj'.get?], .has hT hT'⟩

theorem Form.combine_typed {F G : Form s} {S M T : Ty s}
    (hF : Γ ⊨ F : S ≤ M) (hG : Γ ⊨ G : M ≤ T) :
    ∃ H, F.combine G = some H ∧ Γ ⊨ H : S ≤ T :=
  (combine_typed_aux _).1 F G S M T (Nat.le_refl _) hF hG

theorem EntriesTyped.through {Tel₁ TelM Tel₂ : Telescope (s,x)} {Es₁ Es₂ : Entries s}
    (h₁ : Γ ⊨ Es₁ : Tel₁ ⇒ TelM) (h₂ : Γ ⊨ Es₂ : TelM ⇒ Tel₂) :
    ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ Γ ⊨ Es : Tel₁ ⇒ Tel₂ :=
  (combine_typed_aux _).2 Es₁ Es₂ Tel₁ TelM Tel₂ (Nat.le_refl _) h₁ h₂

theorem SideTyped.combine {F G : Form s} {S X Y : Ty (s,x)}
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
      generalize hX : (B.weaken : Ty (s,x)) = X at h₂
      cases h₂ with
      | id => rw [← hX]; exact ⟨F, Form.combine_id_right F, .closed hF⟩
      | closed hG =>
          obtain rfl := Ty.weaken_inj hX
          obtain ⟨H, hH, hHt⟩ := Form.combine_typed hF hG
          exact ⟨H, hH, .closed hHt⟩

/-- The chain of casts composes: a corollary of `Form.combine_typed` at the
opened shapes. -/
theorem ChainTyped.combine {r : BVar s .var} {F G : Form s} {S M T : Ty s}
    (hF : Γ ⊨[r] F : S ≤ M) (hG : Γ ⊨[r] G : M ≤ T) :
    ∃ H, F.combine G = some H ∧ Γ ⊨[r] H : S ≤ T :=
  Form.combine_typed hF hG

/-! ## Pairing -/

/-- Identity entries are typed from any telescope agreeing with the target at
its positions. -/
theorem Telescope.identityEntries_typed : ∀ (Tel Tel' : Telescope (s,x)),
    (∀ i P, Tel ∋ (i ↦ P) → Tel' ∋ (i ↦ P)) → Γ ⊨ Tel.identityEntries : Tel' ⇒ Tel
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

theorem Telescope.identityEntries_self (Tel : Telescope (s,x)) :
    Γ ⊨ Tel.identityEntries : Tel ⇒ Tel :=
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

/-- Positions of the first telescope of a concatenation. -/
theorem Telescope.At.append_left {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel ∋ (i ↦ P)) : ∀ Tel' : Telescope s', (Tel ++ Tel') ∋ (i ↦ P)
  | .nil => h
  | .cons Tel' _ => .there (Telescope.At.append_left h Tel')

theorem EntriesTyped.append {Tel Tel₁ Tel₂ : Telescope (s,x)} {Es₁ Es₂ : Entries s}
    (h₁ : Γ ⊨ Es₁ : Tel ⇒ Tel₁) (h₂ : Γ ⊨ Es₂ : Tel ⇒ Tel₂) :
    Γ ⊨ Es₁ ++ Es₂ : Tel ⇒ Tel₁ ++ Tel₂ := by
  match h₂ with
  | .nil => exact h₁
  | .le h₂' hh hpre hpost => exact .le (h₁.append h₂') hh hpre hpost
  | .eq h₂' hAt => exact .eq (h₁.append h₂') hAt
  | .eqSym h₂' hAt => exact .eqSym (h₁.append h₂') hAt
  | .has h₂' hAt => exact .has (h₁.append h₂') hAt

/-- A form into an object type is `bot`, `top` into the empty telescope, or
has a source resolving to an object type. -/
theorem FormTyped.into_obj {F : Form s} {S : Ty s} {Tel : Telescope (s,x)}
    (h : Γ ⊨ F : S ≤ μ Tel) :
    F = .bot ∨ (F = .top ∧ Tel = .nil) ∨ ∃ Tel', Γ.resolve S = μ Tel' := by
  cases h with
  | bot _ => exact Or.inl rfl
  | top hT => exact Or.inr (Or.inl ⟨rfl, Ty.obj.inj (by simpa using hT)⟩)
  | id hres => exact Or.inr (Or.inr ⟨Tel, by simpa using hres⟩)
  | eqv hres => exact Or.inr (Or.inr ⟨Tel, by simpa using hres⟩)
  | pi _ hT _ _ => simp at hT
  | obj hS _ _ => exact Or.inr (Or.inr ⟨_, hS⟩)

/-- The entries read off a non-`bot` form into an object type. -/
theorem Form.toEntries_typed {F : Form s} {S : Ty s} {Tel Tel₁ Tel₁' : Telescope (s,x)}
    (h : Γ ⊨ F : S ≤ μ Tel₁') (hS : Γ.resolve S = μ Tel) (hI : Tel₁.identityEntries = Tel₁'.identityEntries)
    (hnb : F ≠ .bot) :
    ∃ Es, F.toEntries Tel₁ = some Es ∧ Γ ⊨ Es : Tel ⇒ Tel₁' := by
  cases h with
  | bot _ => exact absurd rfl hnb
  | top hT =>
      obtain rfl := Ty.obj.inj (by simpa using hT : (μ Tel₁' : Ty s) = μ .nil)
      exact ⟨_, rfl, by rw [hI, Telescope.identityEntries]; exact .nil⟩
  | id hres =>
      rw [hS] at hres
      obtain rfl := Ty.obj.inj (by simpa using hres)
      exact ⟨_, rfl, by rw [hI]; exact Telescope.identityEntries_self _⟩
  | eqv hres =>
      rw [hS] at hres
      obtain rfl := Ty.obj.inj (by simpa using hres)
      exact ⟨_, rfl, by rw [hI]; exact Telescope.identityEntries_self _⟩
  | pi _ hT _ _ => simp at hT
  | obj hS' hT hEs =>
      rw [hS] at hS'
      obtain rfl := Ty.obj.inj hS'
      obtain rfl := Ty.obj.inj (by simpa using hT)
      exact ⟨_, rfl, hEs⟩

/-- Pairing typed forms.  The annotated telescopes only supply the kinds of
the propositions (for identity entries); the typing telescopes may differ
from them by a renaming. -/
theorem Form.pair_typed {F G : Form s} {S : Ty s} {Tel₁ Tel₂ Tel₁' Tel₂' : Telescope (s,x)}
    (hF : Γ ⊨ F : S ≤ μ Tel₁') (hG : Γ ⊨ G : S ≤ μ Tel₂')
    (hI₁ : Tel₁.identityEntries = Tel₁'.identityEntries)
    (hI₂ : Tel₂.identityEntries = Tel₂'.identityEntries) :
    ∃ H, Form.pair Tel₁ Tel₂ F G = some H ∧ Γ ⊨ H : S ≤ μ (Tel₁' ++ Tel₂') := by
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
  have hSrc : ∀ {H : Form s} {Tel' : Telescope (s,x)}, Γ ⊨ H : S ≤ μ Tel' → H ≠ .bot → H ≠ .top →
      ∃ Tel, Γ.resolve S = μ Tel := by
    intro H Tel' hH h0 ht
    rcases hH.into_obj with h | ⟨h, _⟩ | h
    · exact absurd h h0
    · exact absurd h ht
    · exact h
  by_cases hFT' : F.isTop = true
  · obtain rfl := Form.isTop_eq_true.mp hFT'
    by_cases hGT' : G.isTop = true
    · obtain rfl := Form.isTop_eq_true.mp hGT'
      cases hF with
      | top hT₁ =>
        cases hG with
        | top hT₂ =>
          obtain rfl := Ty.obj.inj (by simpa using hT₁ : (μ Tel₁' : Ty s) = μ .nil)
          obtain rfl := Ty.obj.inj (by simpa using hT₂ : (μ Tel₂' : Ty s) = μ .nil)
          exact ⟨.top, by simp [Form.pair], .top (by simp)⟩
    · have hGT : G ≠ .top := fun h => hGT' (Form.isTop_eq_true.mpr h)
      obtain ⟨Tel, hS⟩ := hSrc hG hG0 hGT
      obtain ⟨Es₁, hEs₁, hT₁⟩ := Form.toEntries_typed hF hS hI₁ hF0
      obtain ⟨Es₂, hEs₂, hT₂⟩ := Form.toEntries_typed hG hS hI₂ hG0
      refine ⟨.obj (Es₁ ++ Es₂), ?_, .obj hS (by simp) (hT₁.append hT₂)⟩
      cases G <;> simp_all [Form.pair, Form.toEntries]
  · have hFT : F ≠ .top := fun h => hFT' (Form.isTop_eq_true.mpr h)
    obtain ⟨Tel, hS⟩ := hSrc hF hF0 hFT
    obtain ⟨Es₁, hEs₁, hT₁⟩ := Form.toEntries_typed hF hS hI₁ hF0
    obtain ⟨Es₂, hEs₂, hT₂⟩ := Form.toEntries_typed hG hS hI₂ hG0
    refine ⟨.obj (Es₁ ++ Es₂), ?_, .obj hS (by simp) (hT₁.append hT₂)⟩
    cases F <;> cases G <;> simp_all [Form.pair, Form.toEntries]

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

/-- A closed side instantiated at a root is a typed coercion form. -/
theorem SideTyped.inst (r : BVar s .var) {F : Form s} {S X : Ty (s,x)}
    (h : SideTyped Γ F S X) : Γ ⊨ F : S⟦r⟧ ≤ X⟦r⟧ := by
  cases h with
  | id => exact .id rfl
  | closed hF => rw [Ty.weaken_substVar, Ty.weaken_substVar]; exact hF

/-- Applying typed entries to a typed view at a root. -/
theorem entriesAt_typed {Tel₁ Tel₂ : Telescope (s,x)} {Es : Entries s} {V : View s}
    {r : BVar s .var}
    (hEs : Γ ⊨ Es : Tel₁ ⇒ Tel₂) (hV : Γ ⊨[r, σ] V : Tel₁) :
    ∃ V', entriesAt V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂ := by
  match hEs with
  | .nil => exact ⟨.nil, rfl, .nil⟩
  | .le (pre := pre) (post := post) hEs' hh hpre hpost =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      have hpre' := hpre.inst r
      have hpost' := hpost.inst r
      cases hh with
      | le hAt =>
          obtain ⟨G, hG, hGt⟩ := hV.le_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' hGt
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          refine ⟨V' ▹ .le H₂, ?_, .le hT hH₂t⟩
          simp [entriesAt, hV', Entry.at, Hole.index, hG.get?, hH₁, hH₂]
      | eq hAt =>
          obtain ⟨hq, hE⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE)
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          refine ⟨V' ▹ .le H₂, ?_, .le hT hH₂t⟩
          simp [entriesAt, hV', Entry.at, Hole.index, hq.get?, hH₁, hH₂]
      | eqSym hAt =>
          obtain ⟨hq, hE⟩ := hV.eq_entry hAt
          obtain ⟨H₁, hH₁, hH₁t⟩ := Form.combine_typed hpre' (FormTyped.id hE.symm)
          obtain ⟨H₂, hH₂, hH₂t⟩ := Form.combine_typed hH₁t hpost'
          refine ⟨V' ▹ .le H₂, ?_, .le hT hH₂t⟩
          simp [entriesAt, hV', Entry.at, Hole.index, hq.get?, hH₁, hH₂]
  | .eq hEs' hAt =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      obtain ⟨hq, hE⟩ := hV.eq_entry hAt
      exact ⟨V' ▹ .eq, by simp [entriesAt, hV', Entry.at, hq.get?], .eq hT hE⟩
  | .eqSym hEs' hAt =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      obtain ⟨hq, hE⟩ := hV.eq_entry hAt
      exact ⟨V' ▹ .eq, by simp [entriesAt, hV', Entry.at, hq.get?], .eq hT hE.symm⟩
  | .has (ℓ := ℓ) hEs' hAt =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      obtain ⟨hq, hHF⟩ := hV.has_entry hAt
      exact ⟨V' ▹ .has r ℓ, by simp [entriesAt, hV', Entry.at, hq.get?], .has hT hHF⟩

/-- Applying a typed form to the typed view of an atom yields the typed view
of the target. -/
theorem viewThrough_typed {F : Form s} {S T : Ty s} {a : Atom s} {V : View s} {n : Nat}
    (hF : Γ ⊨ F : S ≤ T)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolve S = μ Tel → Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolve S ≠ ⊥) :
    ∃ V', viewThrough σ (n + 1) F a = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → Γ ⊨[a.root, σ] V' : Tel) ∧
      Γ.resolve T ≠ ⊥ := by
  cases hF with
  | bot hS => exact absurd hS hnb
  | top hT =>
      refine ⟨.nil, rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h
        obtain rfl := Ty.obj.inj (by simpa using h : (μ .nil : Ty s) = μ Tel)
        exact .nil
      · rw [hT]; simp
  | id hres =>
      exact ⟨V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h), by rw [← hres]; exact hnb⟩
  | eqv hres =>
      exact ⟨V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h), by rw [← hres]; exact hnb⟩
  | pi _ hT _ _ =>
      refine ⟨.nil, rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h; exact absurd h (by simp)
      · rw [hT]; simp
  | obj hS hT hEs =>
      obtain ⟨V', hV', hT'⟩ := entriesAt_typed hEs (hVt _ hS)
      refine ⟨V', by simp [viewThrough, hV, hV'], fun Tel h => ?_, ?_⟩
      · rw [hT] at h
        obtain rfl := Ty.obj.inj h
        exact hT'
      · rw [hT]; simp

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
    (∀ (x : BVar s .var) (h : Has s) (p : BVar s .var × Label),
      σ ⊢ x ; h ⇓ₕ[n] p → σ ⊢ x ; h ⇓ₕ[(n + 1)] p)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h; rw [hnf] at h; cases h
      · intro p F h; rw [sideForm] at h; cases h
      · intro m Es h; rw [entries] at h; cases h
      · intro a V h; rw [view] at h; cases h
      · intro F a V h; rw [viewThrough] at h; cases h
      · intro x hh p h; rw [hasView] at h; cases h
  | n + 1 => by
      obtain ⟨ih1, ih0, ih2, ih3, ih4, ih5⟩ := normalizer_succ n
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e F h
        cases e with
        | refl T => rw [hnf] at h; rw [hnf]; exact h
        | top T => rw [hnf] at h; rw [hnf]; exact h
        | bot T => rw [hnf] at h; rw [hnf]; exact h
        | eqToLe φ => rw [hnf] at h; rw [hnf]; exact h
        | pi d c => rw [hnf] at h; rw [hnf]; exact h
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
      · intro F a V h
        cases F with
        | id => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | eqv φ => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | obj Es =>
            cases hv : view σ n a with
            | none => simp [viewThrough, hv] at h
            | some V₀ => simpa [viewThrough, hv, ih3 a V₀ hv] using h
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

theorem hasView_le {n n' : Nat} {x : BVar s .var} {hh : Has s} {p : BVar s .var × Label}
    (h : n ≤ n') (hp : σ ⊢ x ; hh ⇓ₕ[n] p) : σ ⊢ x ; hh ⇓ₕ[n'] p := by
  induction h with
  | refl => exact hp
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2.2 x hh p ih

theorem closedAtomForm_succ : ∀ (n : Nat) (a : Atom s) (r : Atom s × Form s),
    σ ⊢ a ⇓ᶜ[n] r → σ ⊢ a ⇓ᶜ[(n + 1)] r
  | 0, _, _, h => by simp [closedAtomForm] at h
  | n + 1, a, r, h => by
      cases a with
      | var x => rw [closedAtomForm] at h; rw [closedAtomForm]; exact h
      | cast a e =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              cases he : hnf σ n e with
              | none => simp [closedAtomForm, hc, he] at h
              | some G =>
                  simpa [closedAtomForm, hc, he, closedAtomForm_succ n a _ hc,
                    hnf_le (Nat.le_succ n) he] using h
      | foldSelf Tel a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              simpa [closedAtomForm, hc, closedAtomForm_succ n a _ hc] using h
      | unfoldSelf a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              simpa [closedAtomForm, hc, closedAtomForm_succ n a _ hc] using h
      | both Tel₁ Tel₂ a b =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              cases hd : closedAtomForm σ n b with
              | none => simp [closedAtomForm, hc, hd] at h
              | some q =>
                  obtain ⟨b', G⟩ := q
                  simpa [closedAtomForm, hc, hd, closedAtomForm_succ n a _ hc,
                    closedAtomForm_succ n b _ hd] using h

theorem closedAtomForm_le {n n' : Nat} {a : Atom s} {r : Atom s × Form s} (h : n ≤ n')
    (hr : σ ⊢ a ⇓ᶜ[n] r) : σ ⊢ a ⇓ᶜ[n'] r := by
  induction h with
  | refl => exact hr
  | step _ ih => exact closedAtomForm_succ _ a r ih

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

end FCdot
