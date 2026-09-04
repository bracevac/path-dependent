import Coercions.FCdot.CanonicalCombine
import Coercions.FCdot.CanonicalMono
import Coercions.FCdot.ErasureMetatheory

/-!
# Canonical forms

Over a typed store, every closed piece of evidence normalizes to a typed head
form, every concrete atom has a typed view, and every closed atom's chain of
casts normalizes to a form typed from the root's type to the atom's type, as
seen from the root.  The proof is a structural induction on typing
derivations: object coercions are between opened telescopes, so nothing is
ever re-normalized at an instantiation.

Coercion forms and views are typed with plain shapes; only the chain of casts
of an atom (`closedAtomForm`) is typed at the atom's root.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Views are stable under folding and unfolding the self block -/

theorem ViewTyped_unfold {r : BVar s .var} {V : View s} {Tel : Telescope (s,x)}
    (h : Γ ⊨[r, σ] V : Tel) : Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑) := by
  refine ⟨?_, fun i P hP => ?_⟩
  · rw [h.1]; simp [Telescope.weaken, Telescope.substVar, Telescope.length_rename]
  · simp only [Telescope.weaken, Telescope.substVar] at hP
    obtain ⟨P₁, hP₁, rfl⟩ := Telescope.At.rename_inv hP
    obtain ⟨P₀, hP₀, rfl⟩ := Telescope.At.rename_inv hP₁
    have := h.2 i P₀ hP₀
    have e : ((P₀.rename (Rename.subst r)).rename Rename.succ)⟦r⟧ = P₀⟦r⟧ :=
      Proposition.substVar_weaken_substVar P₀ r r
    rw [e]
    exact this

theorem ViewTyped_fold {r : BVar s .var} {V : View s} {Tel : Telescope (s,x)}
    (h : Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑)) : Γ ⊨[r, σ] V : Tel := by
  refine ⟨?_, fun i P₀ hP₀ => ?_⟩
  · rw [h.1]; simp [Telescope.weaken, Telescope.substVar, Telescope.length_rename]
  · have hP : ((Tel⟦r⟧).weaken (k := .var)) ∋ (i ↦ ((P₀⟦r⟧).weaken (k := .var))) :=
      (hP₀.rename (Rename.subst r)).rename (Rename.succ (k := .var))
    have := h.2 i _ hP
    have e : ((P₀⟦r⟧).weaken (k := .var))⟦r⟧ = P₀⟦r⟧ :=
      Proposition.substVar_weaken_substVar P₀ r r
    rw [e] at this
    exact this

/-! ## The precise view of a location -/

theorem eqForms_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) {W₀ : Witnesses (s,x)}
    (hW : (σ.lookup x).witnesses = W₀) :
    ∀ W : Witnesses (s,x), Γ ⊨[x, σ] W.eqForms : (W₀.eqEntriesOf W)
  | .nil => by simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]; exact ViewTyped_nil
  | .cons W ℓ T => by
      simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]
      refine ViewTyped_cons (eqForms_typed hσ x hW W) ?_
      show Γ.resolve ((Ty.sel .here ℓ).substVar x) = Γ.resolve ((W₀.get ℓ)⟦x⟧)
      have hd : Γ.lookupDef x ℓ = some ((W₀.get ℓ)⟦x⟧) := by
        rw [hσ.lookupDef x ℓ, hW]
      have : (Ty.sel .here ℓ).substVar x = .sel x ℓ := rfl
      rw [this]
      exact Ctx.resolve_sel_some (Store.Typed.wellDefined hσ) hd

theorem hasForms_typed (x : BVar s .var) :
    ∀ (ls : List Label) (V : View s) (Tel : Telescope (s,x)),
      Γ ⊨[x, σ] V : Tel → (∀ ℓ ∈ ls, σ.HasField x ℓ) →
      Γ ⊨[x, σ] (V ++ Fields.hasForms x ls) : (Tel.hasEntries ls)
  | [], V, Tel, hV, _ => by simpa [Fields.hasForms, Telescope.hasEntries] using hV
  | ℓ :: ls, V, Tel, hV, hF => by
      simp only [Fields.hasForms, Telescope.hasEntries]
      rw [show V ++ (PropForm.has x ℓ :: Fields.hasForms x ls)
          = (V ++ [PropForm.has x ℓ]) ++ Fields.hasForms x ls by simp]
      refine hasForms_typed x ls _ _ (ViewTyped_cons hV ?_) (fun ℓ' h => hF ℓ' (by simp [h]))
      exact ⟨rfl, rfl, hF ℓ (by simp)⟩

/-- The precise view of a location is typed at its type. -/
theorem precView_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∀ Tel : Telescope (s,x), Γ.resolve (Γ.lookupTy x) = .obj Tel →
      Γ ⊨[x, σ] ((σ.lookup x).precView x) : Tel) ∧
    Γ.resolve (Γ.lookupTy x) ≠ .bot := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      simp at h
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _, _⟩ := hv.obj_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      have hTel := (Ty.obj.injEq _ _).mp h
      subst hTel
      simp only [Value.precView, Telescope.ofLiteral, Witnesses.eqEntries]
      refine hasForms_typed x F.labels _ _ (eqForms_typed hσ x (by rw [hl]; rfl) W) ?_
      intro ℓ hℓ
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem hℓ⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Field presence recorded in the context is field presence in the store. -/
theorem Store.Typed.hasField (hσ : ⊢ σ : Γ) {x : BVar s .var} {Fs : List Label}
    {ℓ : Label} (hF : Γ.lookupFields x = some Fs) (hmem : ℓ ∈ Fs) : σ.HasField x ℓ := by
  rw [hσ.lookupFields x] at hF
  have hFs := (Option.some.injEq _ _).mp hF
  subst hFs
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t => rw [hl] at hmem; simp [Value.fieldLabels] at hmem
  | obj W F =>
      rw [hl] at hmem
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem (by simpa [Value.fieldLabels] using hmem)⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-! ## Statements -/

def LeConcl (σ : Store s) (Γ : Ctx s) (e : LeCo s) (S T : Ty s) : Prop :=
  ∃ n F, hnf σ n e = some F ∧ Γ ⊨ F : S ≤ T

def EqConcl (Γ : Ctx s) (S T : Ty s) : Prop := Γ.resolve S = Γ.resolve T

def HasConcl (σ : Store s) (h : Has s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ n, hasView σ n x h = some (x, ℓ) ∧ σ.HasField x ℓ

def MorConcl (σ : Store s) (Γ : Ctx s) (src : Telescope s) (m : Morphism s) (Tel : Telescope s) :
    Prop :=
  ∃ n Es, entries σ n m = some Es ∧ Γ ⊨ Es : src ⇒ Tel

def AtomConcl (σ : Store s) (Γ : Ctx s) (a : Atom s) (S : Ty s) : Prop :=
  ∃ n V, view σ n a = some V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve S = .obj Tel → Γ ⊨[a.root, σ] V : Tel) ∧
    Γ.resolve S ≠ .bot

/-- The entry of a typed view at a proposition of the telescope. -/
theorem ViewTyped.at {r : BVar s .var} {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {P : Proposition (s,x)} (hAt : Tel.At i P) :
    PropFormTyped Γ r σ (View.nth? V i) (P⟦r⟧) :=
  hV.2 i P hAt

variable (hσ : ⊢ σ : Γ)
include hσ

set_option linter.unusedSectionVars false in
mutual

theorem le_canon {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) : LeConcl σ Γ e S T := by
  match h with
  | @LeCo.HasType.refl _ _ T => exact ⟨1, _, rfl, .eqv rfl⟩
  | @LeCo.HasType.top _ _ T => exact ⟨1, _, rfl, .top (by simp)⟩
  | @LeCo.HasType.bot _ _ T => exact ⟨1, _, rfl, .bot (by simp)⟩
  | .eqToLe hφ => exact ⟨1, _, rfl, .eqv (eq_canon hφ)⟩
  | @LeCo.HasType.pi _ _ d S₂ S₁ c T₁ T₂ hd hc =>
      exact ⟨1, _, rfl, .pi (by simp) (by simp) hd hc⟩
  | @LeCo.HasType.obj _ _ Tel m Tel' hm =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, .obj Es, by simp [hnf, hEs], .obj (by simp [Ctx.resolveAt]) (by simp [Ctx.resolveAt]) hT⟩
  | .trans he hf =>
      obtain ⟨n₁, F, hF, hFt⟩ := le_canon he
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon hf
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt hGt
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt', _⟩ :=
        viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
      have hP := (hVt' Tel (by simp)).at hAt
      cases hq : View.nth? V' i with
      | none => rw [hq] at hP; simp [PropFormTyped, Proposition.rename] at hP
      | some Q =>
          cases Q with
          | le G =>
              rw [hq] at hP
              refine ⟨max n₁ n₂ + 2, G, ?_, ?_⟩
              · simp [hnf, hnf_le (by omega : n₂ ≤ max n₁ n₂ + 1) hF, hV', hq]
              · simpa [PropFormTyped, Proposition.substVar, Proposition.rename, Ty.substVar] using hP
          | eq => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP
          | has y ℓ => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP

theorem eq_canon {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) : EqConcl Γ S T := by
  match h with
  | .refl => rfl
  | .symm h' => exact (eq_canon h').symm
  | .trans h₁ h₂ => exact (eq_canon h₁).trans (eq_canon h₂)
  | .def hdef => exact Ctx.resolve_sel_some (Store.Typed.wellDefined hσ) hdef
  | @EqCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt', _⟩ :=
        viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
      have hP := (hVt' Tel (by simp)).at hAt
      cases hq : View.nth? V' i with
      | none => rw [hq] at hP; simp [PropFormTyped, Proposition.rename] at hP
      | some Q =>
          cases Q with
          | le G => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP
          | eq =>
              rw [hq] at hP
              simpa [PropFormTyped, Proposition.substVar, Proposition.rename, Ty.substVar, EqConcl] using hP
          | has y ℓ => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP

theorem has_canon {hh : Has s} {x : BVar s .var} {ℓ : Label} (h : Has.HasType Γ hh x ℓ) :
    HasConcl σ hh x ℓ := by
  match h with
  | .field hF hmem => exact ⟨1, rfl, hσ.hasField hF hmem⟩
  | @Has.HasType.member _ _ a S e Tel i ℓ ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt', _⟩ :=
        viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
      have hP := (hVt' Tel (by simp)).at hAt
      cases hq : View.nth? V' i with
      | none => rw [hq] at hP; simp [PropFormTyped, Proposition.rename] at hP
      | some Q =>
          cases Q with
          | le G => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP
          | eq => rw [hq] at hP; simp [PropFormTyped, Proposition.substVar, Proposition.rename] at hP
          | has y ℓ' =>
              rw [hq] at hP
              simp only [PropFormTyped, Proposition.substVar, Proposition.rename] at hP
              obtain ⟨rfl, rfl, hHF⟩ := hP
              refine ⟨max n₁ n₂ + 2, ?_, hHF⟩
              simp [hasView, hnf_le (by omega : n₂ ≤ max n₁ n₂ + 1) hF, hV', hq]

theorem mor_canon {src : Telescope s} {m : Morphism s} {Tel : Telescope s}
    (h : Γ ⊢ m : src ⇒ Tel) : MorConcl σ Γ src m Tel := by
  match h with
  | .nil => exact ⟨1, [], rfl, .nil⟩
  | .le hm he =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      refine ⟨max n₁ n₂ + 1, Es ++ [.le F], ?_, .le hT hFt⟩
      simp [entries, entries_le (Nat.le_max_left n₁ n₂) hEs, hnf_le (Nat.le_max_right n₁ n₂) hF]
  | .eq hm hφ =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ++ [.eq], by simp [entries, hEs], .eq hT (eq_canon hφ)⟩
  | .has hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ++ [.has _], by simp [entries, hEs], .has hT hAt⟩

theorem atom_canon {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) : AtomConcl σ Γ a S := by
  match h with
  | @Atom.HasType.var _ _ x =>
      obtain ⟨hV, hnb⟩ := precView_typed hσ x
      exact ⟨1, _, rfl, hV, hnb⟩
  | .cast ha he =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt', hnb'⟩ :=
        viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
      refine ⟨max n₁ n₂ + 2, V', ?_, hVt', hnb'⟩
      simp [view, hnf_le (by omega : n₂ ≤ max n₁ n₂ + 1) hF, hV']
  | @Atom.HasType.unfoldSelf _ _ a Tel ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      have hTel := (Ty.obj.injEq _ _).mp h
      subst hTel
      exact ViewTyped_unfold (hVt Tel (by simp))
  | @Atom.HasType.foldSelf _ _ a Tel ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      have hTel := (Ty.obj.injEq _ _).mp h
      subst hTel
      exact ViewTyped_fold (hVt ((Tel⟦a.root⟧)↑) (Ctx.resolve_obj _ _))

end

end

end FCdot
