import Coercions.FCdot.FormAlgebra
import Coercions.FCdot.ErasureMetatheory

/-!
# Canonical forms

Over a typed store `⊢ σ : Γ`, every closed piece of evidence typed in `Γ`
normalizes to typed data:

* `le_canon`: `Γ ⊢ e : S ≤ T` gives `σ ⊢ e ⇓[n] F` with `Γ ⊨ F : S ≤ T`;
* `eq_canon`: `Γ ⊢ φ : S ≡ T` gives `Γ.resolve S = Γ.resolve T`;
* `has_canon`: `Γ ⊢ h : x ∋ ℓ` gives `σ ⊢ x ; h ⇓ₕ[n] (x, ℓ)` and the object
  stored at `x` has field `ℓ`;
* `mor_canon`: a typed morphism has typed entries;
* `atom_canon`: `Γ ⊢ₐ a : S` gives a view `σ ⊢ a ⇓ᵥ[n] V` typed at every
  telescope `S` resolves to, and `S` does not resolve to `⊥`.

The proof is a structural induction on typing derivations.  Object coercions
are between opened telescopes, so nothing is ever re-normalized at an
instantiation: the `member` cases take an entry out of the atom's view.

The chain of casts of a closed atom then normalizes to a form typed from the
root's type to the atom's type, at the root (`closedAtomForm_typed`).  This
discharges the `FormsTyped` obligation of `preservation` and the
canonical-forms hypothesis of `erase_reflect` (`preservation'`,
`erase_reflect'`).
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Views are stable under folding and unfolding the self block -/

theorem ViewTyped_unfold {r : BVar s .var} {V : View s} {Tel : Telescope (s,x)}
    (h : Γ ⊨[r, σ] V : Tel) : Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑) := by
  induction h with
  | nil => exact .nil
  | le _ hF ih =>
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_le]
      exact .le ih (by rwa [Ty.weaken_substVar, Ty.weaken_substVar])
  | eq _ hE ih =>
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_eq]
      exact .eq ih (by rwa [Ty.weaken_substVar, Ty.weaken_substVar])
  | has _ hH ih =>
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_has]
      exact .has ih hH

theorem ViewTyped_fold {r : BVar s .var} : ∀ {V : View s} {Tel : Telescope (s,x)},
    Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑) → Γ ⊨[r, σ] V : Tel
  | _, .nil, h => by cases h; exact .nil
  | _, .cons Tel (.le S T), h => by
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_le] at h
      cases h with
      | le hV hF =>
          exact .le (ViewTyped_fold hV) (by rwa [Ty.weaken_substVar, Ty.weaken_substVar] at hF)
  | _, .cons Tel (.eq S T), h => by
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_eq] at h
      cases h with
      | eq hV hE =>
          exact .eq (ViewTyped_fold hV) (by rwa [Ty.weaken_substVar, Ty.weaken_substVar] at hE)
  | _, .cons Tel (.has ℓ), h => by
      simp only [Telescope.substVar, Telescope.rename, Proposition.rename, Telescope.weaken_cons,
        Proposition.weaken_has] at h
      cases h with
      | has hV hH => exact .has (ViewTyped_fold hV) hH

/-! ## The precise view of a location -/

theorem eqForms_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) {W₀ : Witnesses (s,x)}
    (hW : (σ.lookup x).witnesses = W₀) :
    ∀ W : Witnesses (s,x), Γ ⊨[x, σ] W.eqForms : W₀.eqEntriesOf .here W
  | .nil => by simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]; exact .nil
  | .cons W ℓ T => by
      simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]
      refine .eq (eqForms_typed hσ x hW W) ?_
      show Γ.resolve (x ∙ ℓ) = Γ.resolve ((W₀.get ℓ)⟦x⟧)
      have hd : Γ.lookupDef x ℓ = some ((W₀.get ℓ)⟦x⟧) := by
        rw [hσ.lookupDef x ℓ, hW]
      exact Ctx.resolve_sel_some (Store.Typed.wellDefined hσ) hd

theorem hasForms_typed (x : BVar s .var) :
    ∀ (ls : List Label) (V : View s) (Tel : Telescope (s,x)),
      Γ ⊨[x, σ] V : Tel → (∀ ℓ ∈ ls, σ.HasField x ℓ) →
      Γ ⊨[x, σ] Fields.hasForms x V ls : Tel.hasEntries ls
  | [], V, Tel, hV, _ => hV
  | ℓ :: ls, V, Tel, hV, hF =>
      hasForms_typed x ls _ _ (.has hV (hF ℓ (by simp))) (fun ℓ' h => hF ℓ' (by simp [h]))

/-- The precise view of a location is typed at its type. -/
theorem precView_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∀ Tel : Telescope (s,x), Γ.resolve (Γ.lookupTy x) = μ Tel →
      Γ ⊨[x, σ] ((σ.lookup x).precView x) : Tel) ∧
    Γ.resolve (Γ.lookupTy x) ≠ ⊥ := by
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
      obtain rfl := Ty.obj.inj h
      simp only [Value.precView, Telescope.ofLiteral, Witnesses.eqEntries]
      refine hasForms_typed x F.labels _ _ (eqForms_typed hσ x (by rw [hl]; rfl) W) ?_
      intro ℓ hℓ
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem hℓ⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Field presence recorded in the context is field presence in the store. -/
theorem Store.Typed.hasField (hσ : ⊢ σ : Γ) {x : BVar s .var} {Fs : List Label}
    {ℓ : Label} (hF : Γ.lookupFields x = some Fs) (hmem : ℓ ∈ Fs) : σ.HasField x ℓ := by
  rw [hσ.lookupFields x] at hF
  obtain rfl := Option.some.inj hF
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t => rw [hl] at hmem; simp [Value.fieldLabels] at hmem
  | obj W F =>
      rw [hl] at hmem
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem (by simpa [Value.fieldLabels] using hmem)⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-! ## Statements -/

def LeConcl (σ : Store s) (Γ : Ctx s) (e : LeCo s) (S T : Ty s) : Prop :=
  ∃ n F, σ ⊢ e ⇓[n] F ∧ Γ ⊨ F : S ≤ T

def EqConcl (Γ : Ctx s) (S T : Ty s) : Prop := Γ.resolve S = Γ.resolve T

def HasConcl (σ : Store s) (h : Has s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ n, σ ⊢ x ; h ⇓ₕ[n] (x, ℓ) ∧ σ.HasField x ℓ

def MorConcl (σ : Store s) (Γ : Ctx s) (src : Telescope s) (m : Morphism s) (Tel : Telescope s) :
    Prop :=
  ∃ n Es, σ ⊢ m ⇓ₘ[n] Es ∧ Γ ⊨ Es : src ⇒ Tel

def AtomConcl (σ : Store s) (Γ : Ctx s) (a : Atom s) (S : Ty s) : Prop :=
  ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve S = μ Tel → Γ ⊨[a.root, σ] V : Tel) ∧
    Γ.resolve S ≠ ⊥

/-! ## Views through coercions -/

/-- The view of an atom through a coercion to an object type, from the
normal forms of both.  Fuel: one more than the larger of the two. -/
theorem view_through_obj {a : Atom s} {S : Ty s} {Tel : Telescope (s,x)} {V : View s}
    {F : Form s} {e : LeCo s} {n₁ n₂ : Nat}
    (hV : σ ⊢ a ⇓ᵥ[n₁] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolve S = μ Tel → Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolve S ≠ ⊥)
    (hF : σ ⊢ e ⇓[n₂] F) (hFt : Γ ⊨ F : S ≤ μ Tel) :
    ∃ V', viewThrough σ (max n₁ n₂ + 1) F a = some V' ∧ Γ ⊨[a.root, σ] V' : Tel := by
  obtain ⟨V', hV', hVt', _⟩ :=
    viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
  exact ⟨V', hV', hVt' Tel (Ctx.resolve_obj _ _)⟩

/-- Fuel bookkeeping: a normal form found with fuel `n₂` is found with
`max n₁ n₂ + 1`. -/
theorem hnf_le_max {e : LeCo s} {F : Form s} {n₁ n₂ : Nat} (hF : σ ⊢ e ⇓[n₂] F) :
    σ ⊢ e ⇓[max n₁ n₂ + 1] F :=
  hnf_le (Nat.le_trans (Nat.le_max_right n₁ n₂) (Nat.le_succ _)) hF

variable (hσ : ⊢ σ : Γ)
include hσ

set_option linter.unusedSectionVars false in
mutual

theorem le_canon {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) : LeConcl σ Γ e S T := by
  match h with
  | .refl => exact ⟨1, _, rfl, .eqv rfl⟩
  | .top => exact ⟨1, _, rfl, .top (by simp)⟩
  | .bot => exact ⟨1, _, rfl, .bot (by simp)⟩
  | .eqToLe hφ => exact ⟨1, _, rfl, .eqv (eq_canon hφ)⟩
  | .pi hd hc => exact ⟨1, _, rfl, .pi (by simp) (by simp) hd hc⟩
  | .obj hm =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, .obj Es, by simp [hnf, hEs], .obj (by simp) (by simp) hT⟩
  | .trans he hf =>
      obtain ⟨n₁, F, hF, hFt⟩ := le_canon he
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon hf
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt hGt
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .member ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt'⟩ := view_through_obj hV hVt hnb hF hFt
      obtain ⟨G, hG, hGt⟩ := hVt'.le_entry hAt
      exact ⟨max n₁ n₂ + 2, G, by simp [hnf, hnf_le_max hF, hV', hG.get?], hGt⟩

theorem eq_canon {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) : EqConcl Γ S T := by
  match h with
  | .refl => rfl
  | .symm h' => exact (eq_canon h').symm
  | .trans h₁ h₂ => exact (eq_canon h₁).trans (eq_canon h₂)
  | .def hdef => exact Ctx.resolve_sel_some (Store.Typed.wellDefined hσ) hdef
  | .member ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt'⟩ := view_through_obj hV hVt hnb hF hFt
      exact (hVt'.eq_entry hAt).2

theorem has_canon {hh : Has s} {x : BVar s .var} {ℓ : Label} (h : Γ ⊢ hh : x ∋ ℓ) :
    HasConcl σ hh x ℓ := by
  match h with
  | .field hF hmem => exact ⟨1, rfl, hσ.hasField hF hmem⟩
  | .member ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt'⟩ := view_through_obj hV hVt hnb hF hFt
      obtain ⟨hq, hHF⟩ := hVt'.has_entry hAt
      exact ⟨max n₁ n₂ + 2, by simp [hasView, hnf_le_max hF, hV', hq.get?], hHF⟩

theorem mor_canon {src : Telescope s} {m : Morphism s} {Tel : Telescope s}
    (h : Γ ⊢ m : src ⇒ Tel) : MorConcl σ Γ src m Tel := by
  match h with
  | .nil => exact ⟨1, .nil, rfl, .nil⟩
  | .le hm he =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      refine ⟨max n₁ n₂ + 1, Es ▹ .le F, ?_, .le hT hFt⟩
      simp [entries, entries_le (Nat.le_max_left n₁ n₂) hEs, hnf_le (Nat.le_max_right n₁ n₂) hF]
  | .eq hm hφ =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .eq, by simp [entries, hEs], .eq hT (eq_canon hφ)⟩
  | .has hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .has hT hAt⟩

theorem atom_canon {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) : AtomConcl σ Γ a S := by
  match h with
  | .var =>
      obtain ⟨hV, hnb⟩ := precView_typed hσ _
      exact ⟨1, _, rfl, hV, hnb⟩
  | .cast ha he =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := atom_canon ha
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨V', hV', hVt', hnb'⟩ :=
        viewThrough_typed hFt (view_le (Nat.le_max_left n₁ n₂) hV) hVt hnb
      exact ⟨max n₁ n₂ + 2, V', by simp [view, hnf_le_max hF, hV'], hVt', hnb'⟩
  | .unfoldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      exact ViewTyped_unfold (hVt _ (Ctx.resolve_obj _ _))
  | .foldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      exact ViewTyped_fold (hVt _ (Ctx.resolve_obj _ _))

end

end

/-! ## The chain of casts of a closed atom -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- The root of an atom under wrappers. -/
@[simp] theorem Atom.root_cast (a : Atom s) (e : LeCo s) : (Atom.cast a e).root = a.root := rfl
@[simp] theorem Atom.root_foldSelf (Tel : Telescope (s,x)) (a : Atom s) :
    (Atom.foldSelf Tel a).root = a.root := rfl
@[simp] theorem Atom.root_unfoldSelf (a : Atom s) : (Atom.unfoldSelf a).root = a.root := rfl

/-- Opening the self block at the root is invisible to `foldSelf`. -/
theorem Ctx.resolveAt_fold (Γ : Ctx s) (r : BVar s .var) (Tel : Telescope (s,x)) :
    Γ.resolveAt r (μ Tel) = Γ.resolveAt r (μ ((Tel⟦r⟧)↑)) := by
  simp [Ctx.resolveAt]

/-- The chain of casts of a closed atom normalizes to a form typed from the
root's type to the atom's type, at the root. -/
theorem closedAtomForm_typed (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s}
    (h : Γ ⊢ₐ a : S) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      Γ ⊨[a.root] F : (Γ.lookupTy a.root) ≤ S := by
  match h with
  | .var => exact ⟨1, _, .id, rfl, .id rfl⟩
  | .cast (e := e) ha he =>
      obtain ⟨n₁, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon hσ he
      obtain ⟨H, hH, hHt⟩ := ChainTyped.combine hFt (hGt.atRoot _)
      refine ⟨max n₁ n₂ + 1, .cast a' e, H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF,
          hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simp only [Atom.root_cast]; exact hHt
  | .unfoldSelf (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      refine ⟨n + 1, .unfoldSelf a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_unfoldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ _ Tel)
  | .foldSelf (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      refine ⟨n + 1, .foldSelf Tel a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_foldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ _ Tel).symm

/-- The type recorded for a location is a function or an object type. -/
theorem Store.Typed.lookupTy_shape (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∃ S T, Γ.lookupTy x = Π(S) T) ∨ ∃ Tel, Γ.lookupTy x = μ Tel := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      exact Or.inl ⟨_, _, hT⟩
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _, _⟩ := hv.obj_inv
      exact Or.inr ⟨_, hT⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- The head form of a function atom's casts is the identity, an equality, or
a `pi` form. -/
theorem closedAtomForm_pi (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} {T : Ty (s,x)}
    (h : Γ ⊢ₐ a : Π(S) T) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  refine ⟨n, a', F, hF, ?_⟩
  cases hFt with
  | bot hb =>
      rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hb
      · simp [Ctx.resolveAt, ho] at hb
  | top ht => simp [Ctx.resolveAt] at ht
  | id _ => exact Or.inl rfl
  | eqv _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | pi _ _ _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | obj _ ho _ => simp [Ctx.resolveAt] at ho

/-- The canonical-forms obligation of preservation. -/
theorem Store.Typed.formsTyped (hσ : ⊢ σ : Γ) : FormsTyped σ Γ where
  pi := by
    intro a S T n a' d c S₀ T₀ ha hF hlk
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = .pi d c := (Prod.mk.inj hd).2.symm
    subst hFe
    cases hFt with
    | pi hS hT hd hc =>
        simp only [Ctx.resolveAt, hlk, Ctx.resolve_pi, Ty.unfoldAt_pi] at hS hT
        obtain ⟨rfl, rfl⟩ := Ty.pi.inj hS
        obtain ⟨rfl, rfl⟩ := Ty.pi.inj hT
        exact ⟨hd, hc⟩
  refl := by
    intro a S T n a' F ha hF hid
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = F := (Prod.mk.inj hd).2.symm
    subst hFe
    have hres : Γ.resolve (Γ.resolveAt a.root (Γ.lookupTy a.root)) =
        Γ.resolve (Γ.resolveAt a.root (Π(S) T)) := by
      rcases hid with rfl | ⟨φ, rfl⟩
      · cases hFt with | id h => exact h
      · cases hFt with | eqv h => exact h
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
    · simp only [Ctx.resolveAt, hp, Ctx.resolve_pi, Ty.unfoldAt_pi] at hres
      obtain ⟨rfl, rfl⟩ := Ty.pi.inj hres
      exact hp
    · simp [Ctx.resolveAt, ho] at hres

/-! ## Corollaries without obligations -/

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun _ hσ => hσ.formsTyped) hT step

/-- Backward simulation over typed stores. -/
theorem erase_reflect' {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ) (hty : ∃ T, Γ ⊢ st.t : T)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect hσ (fun _ _ _ ha _ => closedAtomForm_pi hσ ha) hty h

end

end FCdot
