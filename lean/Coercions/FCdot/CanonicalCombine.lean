import Coercions.FCdot.CanonicalViews
import Coercions.FCdot.Preservation

/-!
# Composition and application of typed forms

`Form.combine` composes typed forms; `entriesAt` applies a typed object
form to a typed view.  Both are structural: no depth, no fuel.
-/

namespace FCdot

/-! ## A self-cast substitution between opaque binders

`Form.combine` on two function forms retypes the first codomain evidence
under the *second* source's domain binder, by casting the binder through the
composite domain evidence.  `Subst.Typed.selfCast` (`Preservation.lean`)
does this for a transparent target binder; the version needed here has an
opaque one. -/

theorem Subst.Typed.selfCastOpaque {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    (hE : LeCo.HasType Γ E S₀ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E.weaken) (Γ.cons (.opaque S₀)) where
  var := by
    intro y
    cases y with
    | here =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.cast (.var .here) E.weaken)
          (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E.weaken).root)
        have hE' : LeCo.HasType (Γ.cons (.opaque S₀)) E.weaken S₀.weaken T.weaken :=
          hE.weaken _
        have hvar : Atom.HasType (Γ.cons (.opaque S₀)) (.var .here) S₀.weaken := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.opaque S₀)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.var (.there z))
          (((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E.weaken).root)
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
variable {σ : Store s} {Γ : Ctx s} {ρ : Option (BVar s .var)}

/-! ## Shapes in either mode -/

theorem Ctx.resolveAt_bot_iff (Γ : Ctx s) (ρ : Option (BVar s .var)) (T : Ty s) :
    Γ.resolveAt ρ T = .bot ↔ Γ.resolve T = .bot := by
  cases ρ with
  | none => rfl
  | some r =>
      simp only [Ctx.resolveAt]
      cases Γ.resolve T <;> simp [Ty.unfoldAt]

theorem Ctx.resolveAt_top_iff (Γ : Ctx s) (ρ : Option (BVar s .var)) (T : Ty s) :
    Γ.resolveAt ρ T = .top ↔ Γ.resolve T = .top := by
  cases ρ with
  | none => rfl
  | some r =>
      simp only [Ctx.resolveAt]
      cases Γ.resolve T <;> simp [Ty.unfoldAt]

theorem Ctx.resolveAt_pi_iff (Γ : Ctx s) (ρ : Option (BVar s .var)) (T : Ty s) (S₁ : Ty s)
    (T₁ : Ty (s,x)) : Γ.resolveAt ρ T = .pi S₁ T₁ ↔ Γ.resolve T = .pi S₁ T₁ := by
  cases ρ with
  | none => rfl
  | some r =>
      simp only [Ctx.resolveAt]
      cases Γ.resolve T <;> simp [Ty.unfoldAt]

theorem Ctx.resolveAt_none (Γ : Ctx s) (T : Ty s) : Γ.resolveAt none T = Γ.resolve T := rfl

/-! ## Plain typedness implies typedness at any root -/

mutual

theorem FormTyped.atRoot {F : Form s} {S T : Ty s} (r : BVar s .var)
    (h : FormTyped Γ none F S T) : FormTyped Γ (some r) F S T := by
  match h with
  | .bot hS => exact .bot hS
  | .top hT => exact .top hT
  | .id hres => exact .id (by simp only [Ctx.resolveAt] at hres ⊢; rw [hres])
  | .eqv hres => exact .eqv (by simp only [Ctx.resolveAt] at hres ⊢; rw [hres])
  | .pi hS hT hd hc => exact .pi hS hT hd hc
  | .obj hS hT hEs =>
      refine .obj ?_ ?_ (EntriesTyped.atRoot r hEs)
      · simp only [Ctx.resolveAt] at hS ⊢; rw [hS]; simp [Ty.unfoldAt]
      · simp only [Ctx.resolveAt] at hT ⊢; rw [hT]; simp [Ty.unfoldAt]

theorem EntriesTyped.atRoot {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} (r : BVar s .var)
    (h : EntriesTyped Γ none Tel₁ Es Tel₂) : EntriesTyped Γ (some r) Tel₁ Es Tel₂ := by
  match h with
  | .nil => exact .nil
  | .le h' hF => exact .le (EntriesTyped.atRoot r h') (FormTyped.atRoot r hF)
  | .eq h' hE => exact .eq (EntriesTyped.atRoot r h') hE
  | .has h' hAt => exact .has (EntriesTyped.atRoot r h') hAt

end

/-- Typedness of a form only depends on the source through its shape. -/
theorem FormTyped.srcRes {F : Form s} {S S' T : Ty s}
    (h : Γ.resolveAt ρ S = Γ.resolveAt ρ S') (hF : FormTyped Γ ρ F S' T) : FormTyped Γ ρ F S T := by
  cases hF with
  | bot hS => exact .bot ((Ctx.resolveAt_bot_iff Γ ρ S).mp (h.trans ((Ctx.resolveAt_bot_iff Γ ρ S').mpr hS)))
  | top hT => exact .top hT
  | id hres => exact .id (h.trans hres)
  | eqv hres => exact .eqv (h.trans hres)
  | pi hS hT hd hc =>
      exact .pi ((Ctx.resolveAt_pi_iff Γ ρ S _ _).mp (h.trans ((Ctx.resolveAt_pi_iff Γ ρ S' _ _).mpr hS))) hT hd hc
  | obj hS hT hEs => exact .obj (h.trans hS) hT hEs

/-- Typedness of a form only depends on the target through its shape. -/
theorem FormTyped.tgtRes {F : Form s} {S T T' : Ty s}
    (h : Γ.resolveAt ρ T' = Γ.resolveAt ρ T) (hF : FormTyped Γ ρ F S T') : FormTyped Γ ρ F S T := by
  cases hF with
  | bot hS => exact .bot hS
  | top hT => exact .top ((Ctx.resolveAt_top_iff Γ ρ T).mp (h.symm.trans ((Ctx.resolveAt_top_iff Γ ρ T').mpr hT)))
  | id hres => exact .id (hres.trans h)
  | eqv hres => exact .eqv (hres.trans h)
  | pi hS hT hd hc =>
      exact .pi hS ((Ctx.resolveAt_pi_iff Γ ρ T _ _).mp (h.symm.trans ((Ctx.resolveAt_pi_iff Γ ρ T' _ _).mpr hT))) hd hc
  | obj hS hT hEs => exact .obj hS (h.symm.trans hT) hEs

/-! ## Entries by position -/

theorem EntriesTyped.length {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)}
    (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) : Es.length = Tel₂.length := by
  match h with
  | .nil => rfl
  | .le h' _ => simp [Telescope.length, h'.length]
  | .eq h' _ => simp [Telescope.length, h'.length]
  | .has h' _ => simp [Telescope.length, h'.length]

theorem EntriesTyped.nth?_has {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)}
    (h : EntriesTyped Γ ρ Tel₁ Es Tel₂) {j : Nat} {ℓ : Label} (hAt : Tel₂.At j (.has ℓ)) :
    ∃ j', Entries.nth? Es j = some (.has j') ∧ Tel₁.At j' (.has ℓ) := by
  match h with
  | .nil => cases hAt
  | .le hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨j', hj', hT⟩ := hEs.nth?_has hAt'
          refine ⟨j', ?_, hT⟩
          rw [Entries.nth?_append_lt _ _ _ (by rw [hEs.length]; exact hAt'.lt)]
          exact hj'
  | .eq hEs _ =>
      cases hAt with
      | there hAt' =>
          obtain ⟨j', hj', hT⟩ := hEs.nth?_has hAt'
          refine ⟨j', ?_, hT⟩
          rw [Entries.nth?_append_lt _ _ _ (by rw [hEs.length]; exact hAt'.lt)]
          exact hj'
  | @EntriesTyped.has _ _ _ _ _ Es j₀ ℓ₀ hEs hT =>
      cases hAt with
      | here =>
          refine ⟨j₀, ?_, hT⟩
          rw [← hEs.length]
          exact Entries.nth?_append_length Es _
      | there hAt' =>
          obtain ⟨j', hj', hT'⟩ := hEs.nth?_has hAt'
          refine ⟨j', ?_, hT'⟩
          rw [Entries.nth?_append_lt _ _ _ (by rw [hEs.length]; exact hAt'.lt)]
          exact hj'

/-! ## Routing entries through a first coercion -/

theorem Entries.through_snoc (Es₁ : List (Entry s)) :
    ∀ (Es : List (Entry s)) (E : Entry s),
      Entries.through Es₁ (Es ++ [E]) =
        (Entries.through Es₁ Es).bind (fun Es' => (Entry.through Es₁ E).map (fun E' => Es' ++ [E']))
  | [], E => by
      cases h : Entry.through Es₁ E <;> simp [Entries.through, h]
  | E₀ :: Es, E => by
      simp only [List.cons_append, Entries.through]
      cases h₀ : Entry.through Es₁ E₀ with
      | none => simp
      | some E₀' =>
          rw [Entries.through_snoc Es₁ Es E]
          cases h : Entries.through Es₁ Es with
          | none => simp
          | some Es' =>
              cases h' : Entry.through Es₁ E with
              | none => simp
              | some E' => simp

theorem EntriesTyped.through {Tel₁ TelM Tel₂ : Telescope s} {Es₁ Es₂ : List (Entry s)}
    (h₁ : EntriesTyped Γ ρ Tel₁ Es₁ TelM) (h₂ : EntriesTyped Γ ρ TelM Es₂ Tel₂) :
    ∃ Es, Entries.through Es₁ Es₂ = some Es ∧ EntriesTyped Γ ρ Tel₁ Es Tel₂ := by
  match h₂ with
  | .nil => exact ⟨[], rfl, .nil⟩
  | .le h₂' hF =>
      obtain ⟨Es, hEs, hT⟩ := h₁.through h₂'
      refine ⟨Es ++ [.le _], ?_, .le hT hF⟩
      rw [Entries.through_snoc, hEs]; rfl
  | .eq h₂' hE =>
      obtain ⟨Es, hEs, hT⟩ := h₁.through h₂'
      refine ⟨Es ++ [.eq], ?_, .eq hT hE⟩
      rw [Entries.through_snoc, hEs]; rfl
  | .has h₂' hAt =>
      obtain ⟨Es, hEs, hT⟩ := h₁.through h₂'
      obtain ⟨j', hj', hT'⟩ := h₁.nth?_has hAt
      refine ⟨Es ++ [.has j'], ?_, .has hT hT'⟩
      rw [Entries.through_snoc, hEs]
      simp [Entry.through, hj']

/-! ## Composition of typed forms -/

theorem Form.combine_typed {F G : Form s} {S M T : Ty s}
    (hF : FormTyped Γ ρ F S M) (hG : FormTyped Γ ρ G M T) :
    ∃ H, F.combine G = some H ∧ FormTyped Γ ρ H S T := by
  cases hF with
  | bot hS =>
      refine ⟨.bot, ?_, .bot hS⟩
      cases G <;> rfl
  | id hres =>
      exact ⟨G, by cases G <;> rfl, hG.srcRes hres⟩
  | top hM =>
      have hM' : Γ.resolveAt ρ M = .top := (Ctx.resolveAt_top_iff Γ ρ M).mpr hM
      cases hG with
      | bot hb => rw [hM] at hb; exact absurd hb (by simp)
      | top hT => exact ⟨.top, rfl, .top hT⟩
      | id hres => exact ⟨.top, rfl, .top ((Ctx.resolveAt_top_iff Γ ρ T).mp (hres ▸ hM'))⟩
      | eqv hres => exact ⟨.top, rfl, .top ((Ctx.resolveAt_top_iff Γ ρ T).mp (hres ▸ hM'))⟩
      | pi hp _ _ _ => rw [hM] at hp; exact absurd hp (by simp)
      | obj ho _ _ => rw [hM'] at ho; exact absurd ho (by simp)
  | eqv hres =>
      cases hG with
      | bot hb =>
          exact ⟨.bot, rfl, .bot ((Ctx.resolveAt_bot_iff Γ ρ S).mp
            (hres.trans ((Ctx.resolveAt_bot_iff Γ ρ M).mpr hb)))⟩
      | top hT => exact ⟨.top, rfl, .top hT⟩
      | id hres' => exact ⟨.eqv _, rfl, .eqv (hres.trans hres')⟩
      | eqv hres' => exact ⟨.eqv _, rfl, .eqv (hres.trans hres')⟩
      | pi hp hT hd hc =>
          exact ⟨.pi _ _, rfl, .pi ((Ctx.resolveAt_pi_iff Γ ρ S _ _).mp
            (hres.trans ((Ctx.resolveAt_pi_iff Γ ρ M _ _).mpr hp))) hT hd hc⟩
      | obj ho hT hEs => exact ⟨.obj _, rfl, .obj (hres.trans ho) hT hEs⟩
  | pi hS hM hd hc =>
      have hM' : Γ.resolveAt ρ M = .pi _ _ := (Ctx.resolveAt_pi_iff Γ ρ M _ _).mpr hM
      cases hG with
      | bot hb => rw [hM] at hb; exact absurd hb (by simp)
      | top hT => exact ⟨.top, rfl, .top hT⟩
      | id hres =>
          exact ⟨.pi _ _, rfl, .pi hS ((Ctx.resolveAt_pi_iff Γ ρ T _ _).mp (hres ▸ hM')) hd hc⟩
      | eqv hres =>
          exact ⟨.pi _ _, rfl, .pi hS ((Ctx.resolveAt_pi_iff Γ ρ T _ _).mp (hres ▸ hM')) hd hc⟩
      | pi hp hT hd₂ hc₂ =>
          rw [hM] at hp
          have hpi := (Ty.pi.injEq _ _ _ _).mp hp
          obtain ⟨hs, ht⟩ := hpi
          subst hs; subst ht
          refine ⟨.pi _ _, rfl, .pi hS hT (.trans hd₂ hd) (.trans ?_ hc₂)⟩
          have hsub := LeCo.HasType.subst (Subst.Typed.selfCastOpaque hd₂) hc
          simpa using hsub
      | obj ho _ _ => rw [hM'] at ho; exact absurd ho (by simp)
  | obj hS hM hEs =>
      cases hG with
      | bot hb =>
          have := (Ctx.resolveAt_bot_iff Γ ρ M).mpr hb
          rw [hM] at this; exact absurd this (by simp)
      | top hT => exact ⟨.top, rfl, .top hT⟩
      | id hres => exact ⟨.obj _, rfl, .obj hS (hres.symm.trans hM) hEs⟩
      | eqv hres => exact ⟨.obj _, rfl, .obj hS (hres.symm.trans hM) hEs⟩
      | pi hp _ _ _ =>
          have := (Ctx.resolveAt_pi_iff Γ ρ M _ _).mpr hp
          rw [hM] at this; exact absurd this (by simp)
      | obj hM' hT hEs₂ =>
          rw [hM] at hM'
          have hTel := Telescope.weaken_inj ((Ty.obj.injEq _ _).mp hM')
          subst hTel
          obtain ⟨Es, hEs', hT'⟩ := hEs.through hEs₂
          exact ⟨.obj Es, by simp [Form.combine, hEs'], .obj hS hT hT'⟩

/-! ## Applying a typed object form to a typed view -/

theorem entriesAt_snoc (V : View s) :
    ∀ (Es : List (Entry s)) (E : Entry s),
      entriesAt V (Es ++ [E]) =
        (entriesAt V Es).bind (fun V' =>
          (match E with
            | .le F => some (PropForm.le F)
            | .eq => some PropForm.eq
            | .has j => View.nth? V j).map (fun P => V' ++ [P]))
  | [], E => by cases E with
      | le F => simp [entriesAt]
      | eq => simp [entriesAt]
      | has j => cases h : View.nth? V j <;> simp [entriesAt, h]
  | E₀ :: Es, E => by
      have ih := entriesAt_snoc V Es E
      cases E₀ with
      | le F =>
          simp only [List.cons_append, entriesAt]
          rw [ih]
          cases h : entriesAt V Es <;> cases E <;> simp
          all_goals (cases h' : View.nth? V _ <;> simp)
      | eq =>
          simp only [List.cons_append, entriesAt]
          rw [ih]
          cases h : entriesAt V Es <;> cases E <;> simp
          all_goals (cases h' : View.nth? V _ <;> simp)
      | has j =>
          simp only [List.cons_append, entriesAt]
          cases h₀ : View.nth? V j with
          | none => simp
          | some P₀ =>
              rw [ih]
              cases h : entriesAt V Es <;> cases E <;> simp
              all_goals (cases h' : View.nth? V _ <;> simp)

/-- Applying typed entries (over opened telescopes) to a typed view at a root. -/
theorem entriesAt_typed {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {V : View s}
    {r : BVar s .var}
    (hEs : EntriesTyped Γ none Tel₁ Es Tel₂) (hV : ViewTyped Γ r σ V Tel₁.weaken) :
    ∃ V', entriesAt V Es = some V' ∧ ViewTyped Γ r σ V' Tel₂.weaken := by
  match hEs with
  | .nil => exact ⟨[], rfl, ViewTyped_nil⟩
  | @EntriesTyped.le _ _ _ _ _ Es F S' T' hEs' hF =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      refine ⟨V' ++ [.le F], ?_, ?_⟩
      · rw [entriesAt_snoc, hV']; rfl
      · rw [Telescope.weaken_cons, Proposition.weaken_le]
        refine ViewTyped_cons hT ?_
        show FormTyped Γ none F ((S'.weaken (k := .var)).substVar r) ((T'.weaken (k := .var)).substVar r)
        rw [Ty.weaken_substVar, Ty.weaken_substVar]
        exact hF
  | .eq hEs' hE =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      refine ⟨V' ++ [.eq], ?_, ?_⟩
      · rw [entriesAt_snoc, hV']; rfl
      · rw [Telescope.weaken_cons, Proposition.weaken_eq]
        refine ViewTyped_cons hT ?_
        show Γ.resolve ((_ : Ty s).weaken.substVar r) = Γ.resolve ((_ : Ty s).weaken.substVar r)
        rw [Ty.weaken_substVar, Ty.weaken_substVar]
        exact hE
  | @EntriesTyped.has _ _ _ _ _ Es j ℓ hEs' hAt =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      have hP := hV.2 j _ hAt.weaken
      cases hQ : View.nth? V j with
      | none => rw [hQ] at hP; exact absurd hP (by simp [PropFormTyped])
      | some Q =>
          rw [hQ] at hP
          refine ⟨V' ++ [Q], ?_, ?_⟩
          · rw [entriesAt_snoc, hV']; simp [hQ]
          · rw [Telescope.weaken_cons, Proposition.weaken_has]
            exact ViewTyped_cons hT hP

/-- Applying a typed form to the typed view of an atom yields the typed view
of the target. -/
theorem viewThrough_typed {F : Form s} {S T : Ty s} {a : Atom s} {V : View s} {n : Nat}
    (hF : FormTyped Γ none F S T)
    (hV : view σ n a = some V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolve S = .obj Tel → ViewTyped Γ a.root σ V Tel)
    (hnb : Γ.resolve S ≠ .bot) :
    ∃ V', viewThrough σ (n + 1) F a = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolve T = .obj Tel → ViewTyped Γ a.root σ V' Tel) ∧
      Γ.resolve T ≠ .bot := by
  cases hF with
  | bot hS => exact absurd hS hnb
  | top hT =>
      refine ⟨[], rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h; exact absurd h (by simp)
      · rw [hT]; simp
  | id hres =>
      simp only [Ctx.resolveAt] at hres
      exact ⟨V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h), by rw [← hres]; exact hnb⟩
  | eqv hres =>
      simp only [Ctx.resolveAt] at hres
      exact ⟨V, by simp [viewThrough, hV], fun Tel h => hVt Tel (hres.trans h), by rw [← hres]; exact hnb⟩
  | pi _ hT _ _ =>
      refine ⟨[], rfl, fun Tel h => ?_, ?_⟩
      · rw [hT] at h; exact absurd h (by simp)
      · rw [hT]; simp
  | obj hS hT hEs =>
      simp only [Ctx.resolveAt] at hS hT
      obtain ⟨V', hV', hT'⟩ := entriesAt_typed hEs (hVt _ hS)
      refine ⟨V', by simp [viewThrough, hV, hV'], fun Tel h => ?_, ?_⟩
      · rw [hT] at h
        have hTel := (Ty.obj.injEq _ _).mp h
        subst hTel
        exact hT'
      · rw [hT]; simp

end

end FCdot
