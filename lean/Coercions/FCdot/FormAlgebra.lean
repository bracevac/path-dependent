import Coercions.FCdot.FormTyping
import Coercions.FCdot.Preservation

/-!
# The algebra of typed forms: composition, application, fuel

Three facts about forms that the canonical-forms theorem consumes.

* *Composition.*  `Form.combine` of two typed forms is a typed form
  (`Form.combine_typed`); composing object forms routes the second form's
  presence entries through the first (`EntriesTyped.through`).
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
    (h : Γ ⊨ F : S ≤ T) : Γ ⊨[r] F : S ≤ T := by
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
    (h : Γ ⊨ Es : Tel₁ ⇒ Tel₂) : Γ ⊨[r] Es : Tel₁ ⇒ Tel₂ := by
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
          have hpi := Ty.pi.inj hp
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
          have hTel := Telescope.weaken_inj (Ty.obj.inj hM')
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
    (hEs : Γ ⊨ Es : Tel₁ ⇒ Tel₂) (hV : Γ ⊨[r, σ] V : Tel₁↑) :
    ∃ V', entriesAt V Es = some V' ∧ Γ ⊨[r, σ] V' : Tel₂↑ := by
  match hEs with
  | .nil => exact ⟨[], rfl, ViewTyped_nil⟩
  | @EntriesTyped.le _ _ _ _ _ Es F S' T' hEs' hF =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      refine ⟨V' ++ [.le F], ?_, ?_⟩
      · rw [entriesAt_snoc, hV']; rfl
      · rw [Telescope.weaken_cons, Proposition.weaken_le]
        refine ViewTyped_cons hT ?_
        show Γ ⊨ F : ((S'.weaken (k := .var))⟦r⟧) ≤ ((T'.weaken (k := .var))⟦r⟧)
        rw [Ty.weaken_substVar, Ty.weaken_substVar]
        exact hF
  | .eq hEs' hE =>
      obtain ⟨V', hV', hT⟩ := entriesAt_typed hEs' hV
      refine ⟨V' ++ [.eq], ?_, ?_⟩
      · rw [entriesAt_snoc, hV']; rfl
      · rw [Telescope.weaken_cons, Proposition.weaken_eq]
        refine ViewTyped_cons hT ?_
        show Γ.resolve ((_ : Ty s)↑.substVar r) = Γ.resolve ((_ : Ty s)↑.substVar r)
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
    (hF : Γ ⊨ F : S ≤ T)
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolve S = .obj Tel → Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolve S ≠ .bot) :
    ∃ V', viewThrough σ (n + 1) F a = some V' ∧
      (∀ Tel : Telescope (s,x), Γ.resolve T = .obj Tel → Γ ⊨[a.root, σ] V' : Tel) ∧
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
        have hTel := Ty.obj.inj h
        subst hTel
        exact hT'
      · rw [hT]; simp

end

/-! ## Fuel monotonicity and determinism -/

section
variable (σ : Store s)

theorem normalizer_succ : ∀ n : Nat,
    (∀ (e : LeCo s) (F : Form s), σ ⊢ e ⇓[n] F → σ ⊢ e ⇓[(n + 1)] F) ∧
    (∀ (m : Morphism s) (Es : List (Entry s)), σ ⊢ m ⇓ₘ[n] Es → σ ⊢ m ⇓ₘ[(n + 1)] Es) ∧
    (∀ (a : Atom s) (V : View s), σ ⊢ a ⇓ᵥ[n] V → σ ⊢ a ⇓ᵥ[(n + 1)] V) ∧
    (∀ (F : Form s) (a : Atom s) (V : View s),
      viewThrough σ n F a = some V → viewThrough σ (n + 1) F a = some V) ∧
    (∀ (x : BVar s .var) (h : Has s) (p : BVar s .var × Label),
      σ ⊢ x ; h ⇓ₕ[n] p → σ ⊢ x ; h ⇓ₕ[(n + 1)] p)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e F h; rw [hnf] at h; cases h
      · intro m Es h; rw [entries] at h; cases h
      · intro a V h; rw [view] at h; cases h
      · intro F a V h; rw [viewThrough] at h; cases h
      · intro x hh p h; rw [hasView] at h; cases h
  | n + 1 => by
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := normalizer_succ n
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      · intro m Es h
        cases m with
        | nil => rw [entries] at h; rw [entries]; exact h
        | le m e =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ =>
                cases he : hnf σ n e with
                | none => simp [entries, hm, he] at h
                | some F => simpa [entries, hm, he, ih2 m Es₀ hm, ih1 e F he] using h
        | eq m φ =>
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
            | some F => simpa [view, he, ih1 e F he, ih4 F a V (by simpa [view, he] using h)] using h
        | foldSelf Tel a => simp only [view] at h ⊢; exact ih3 a V h
        | unfoldSelf a => simp only [view] at h ⊢; exact ih3 a V h
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

theorem entries_le {n n' : Nat} {m : Morphism s} {Es : List (Entry s)} (h : n ≤ n')
    (hE : σ ⊢ m ⇓ₘ[n] Es) : σ ⊢ m ⇓ₘ[n'] Es := by
  induction h with
  | refl => exact hE
  | step _ ih => exact (normalizer_succ σ _).2.1 m Es ih

theorem view_le {n n' : Nat} {a : Atom s} {V : View s} (h : n ≤ n') (hV : σ ⊢ a ⇓ᵥ[n] V) :
    σ ⊢ a ⇓ᵥ[n'] V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.1 a V ih

theorem viewThrough_le {n n' : Nat} {F : Form s} {a : Atom s} {V : View s} (h : n ≤ n')
    (hV : viewThrough σ n F a = some V) : viewThrough σ n' F a = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.1 F a V ih

theorem hasView_le {n n' : Nat} {x : BVar s .var} {hh : Has s} {p : BVar s .var × Label}
    (h : n ≤ n') (hp : σ ⊢ x ; hh ⇓ₕ[n] p) : σ ⊢ x ; hh ⇓ₕ[n'] p := by
  induction h with
  | refl => exact hp
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2 x hh p ih

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
