import Coercions.Nominal.FCn.ProvenanceViews
import Coercions.Nominal.FCn.ClassForms

/-!
# Run-time provenance at a class type (plan XII, stage NR)

The corollary of the predicate through the canonical forms of `ClassForms`.  Every seal of a normal
form is a seal of the evidence's own head (`Hnf.sf`): a `member` read returns a bound entry of a
view, and under the predicate no bound entry holds a seal.  So over a typed store, a path of the
fragment `PathCo.Frag` that meets the predicate and is typed below a class `C` names, up to `canon`,
a store variable recorded at a class `q∙D` below `C` (`frag_provenance`).  The fragment is every path
former but a field selection and `unfold`.  `provenance` reads it at every state a typed program
meeting `Tm.InitSeals` reaches on the machine `Step appView`.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The seals the evidence's head writes -/

mutual
/-- The seals the normalizer can read off the evidence's own atoms. -/
def LeCo.sealsIn : LeCo s → List (Path s × Label)
  | .trans e f => LeCo.sealsIn e ++ LeCo.sealsIn f
  | .obj _ m => Morphism.sealsIn m
  | .pair _ _ e f => LeCo.sealsIn e ++ LeCo.sealsIn f
  | .intoBnd e => LeCo.sealsIn e
  | .seal p C => [(p, C)]
  | _ => []
def Morphism.sealsIn : Morphism s → List (Path s × Label)
  | .nil => []
  | .le m pre _ post => Morphism.sealsIn m ++ Side.sealsIn pre ++ Side.sealsIn post
  | .fld m _ sd => Morphism.sealsIn m ++ Side.sealsIn sd
  | .alias m _ => Morphism.sealsIn m
  | .is m e => Morphism.sealsIn m ++ LeCo.sealsIn e
def Side.sealsIn : Side s → List (Path s × Label)
  | .some e => LeCo.sealsIn e
  | _ => []
end

theorem Form.seals_append : ∀ (F G : Form s), Form.seals (F.append G) = Form.seals F ++ Form.seals G
  | .nil, _ => rfl
  | .cons A F, G => by
      simp only [Form.append, Form.seals, Form.seals_append F G, List.append_assoc]

mutual
/-- A seal of the evidence's own atoms sits at the head, at the variable the evidence acts on. -/
theorem LeCo.sealsOK_sealsIn : ∀ {h : Option (Path s)} {ξ : Alloc s} (e : LeCo s) {q : Path s} {D : Label},
    LeCo.sealsOK h ξ e = true → (q, D) ∈ LeCo.sealsIn e → ∃ y, h = some (.var y) ∧ ξ y (q, D) = true
  | _, _, .trans e f, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at h₁
      simp only [LeCo.sealsIn, List.mem_append] at h₂
      rcases h₂ with h₂ | h₂
      · exact LeCo.sealsOK_sealsIn e h₁.1 h₂
      · exact LeCo.sealsOK_sealsIn f h₁.2 h₂
  | _, _, .obj _ m, _, _, h₁, h₂ => Morphism.sealsOK_sealsIn m h₁ h₂
  | _, _, .pair _ _ e f, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at h₁
      simp only [LeCo.sealsIn, List.mem_append] at h₂
      rcases h₂ with h₂ | h₂
      · exact LeCo.sealsOK_sealsIn e h₁.1 h₂
      · exact LeCo.sealsOK_sealsIn f h₁.2 h₂
  | _, _, .intoBnd e, _, _, h₁, h₂ => LeCo.sealsOK_sealsIn e h₁ h₂
  | h, _, .seal _ C, _, _, h₁, h₂ => by
      simp only [LeCo.sealsIn, List.mem_singleton, Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      match h, h₁ with
      | some (.var y), h₁ => exact ⟨y, rfl, h₁⟩
      | some (.sel _ _), h₁ => simp [LeCo.sealsOK] at h₁
      | none, h₁ => simp [LeCo.sealsOK] at h₁
  | _, _, .refl _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .top _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .bot _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .eqToLe _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .pi _ _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .bound _ _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
  | _, _, .member _ _ _, _, _, _, h₂ => by simp [LeCo.sealsIn] at h₂
theorem Morphism.sealsOK_sealsIn : ∀ {h : Option (Path s)} {ξ : Alloc s} (m : Morphism s) {q : Path s} {D : Label},
    Morphism.sealsOK h ξ m = true → (q, D) ∈ Morphism.sealsIn m → ∃ y, h = some (.var y) ∧ ξ y (q, D) = true
  | _, _, .nil, _, _, _, h₂ => by simp [Morphism.sealsIn] at h₂
  | _, _, .le m pre _ post, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at h₁
      simp only [Morphism.sealsIn, List.mem_append] at h₂
      rcases h₂ with (h₂ | h₂) | h₂
      · exact Morphism.sealsOK_sealsIn m h₁.1.1 h₂
      · exact (Side.sealsOK_sealsIn pre h₁.1.2 h₂).elim
      · exact (Side.sealsOK_sealsIn post h₁.2 h₂).elim
  | _, _, .fld m _ sd, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at h₁
      simp only [Morphism.sealsIn, List.mem_append] at h₂
      rcases h₂ with h₂ | h₂
      · exact Morphism.sealsOK_sealsIn m h₁.1 h₂
      · exact (Side.sealsOK_sealsIn sd h₁.2 h₂).elim
  | _, _, .alias m _, _, _, h₁, h₂ => Morphism.sealsOK_sealsIn m h₁ h₂
  | _, _, .is m e, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at h₁
      simp only [Morphism.sealsIn, List.mem_append] at h₂
      rcases h₂ with h₂ | h₂
      · exact Morphism.sealsOK_sealsIn m h₁.1 h₂
      · exact LeCo.sealsOK_sealsIn e h₁.2 h₂
/-- A side never holds a seal of the evidence's own atoms. -/
theorem Side.sealsOK_sealsIn : ∀ {ξ : Alloc s} (sd : Side s) {q : Path s} {D : Label},
    Side.sealsOK ξ sd = true → (q, D) ∈ Side.sealsIn sd → False
  | _, .some e, _, _, h₁, h₂ => by
      obtain ⟨_, e', _⟩ := LeCo.sealsOK_sealsIn (h := none) e h₁ h₂
      cases e'
  | _, .none, _, _, _, h₂ => by simp [Side.sealsIn] at h₂
  | _, .bot _, _, _, _, h₂ => by simp [Side.sealsIn] at h₂
  | _, .top _, _, _, _, h₂ => by simp [Side.sealsIn] at h₂
end

/-! ### Every seal of a normal form is a seal of the evidence's own head (the `member` case)

`Form.sf` says that every bound entry an `obj` atom builds has seal-free sides, `View.sf` that every
bound entry of a view is seal-free.  A `member` read returns a bound entry of a view, so it adds no
seal.  With `LeCo.sealsOK`, the sides of a morphism hold no seal, so every view the path view builds
meets `View.sf`, and every seal of a normal form is a seal of the evidence's head atoms. -/

mutual
def Atom.sf : Atom s → Bool
  | .obj Es => Entries.sf Es
  | .pair F G => Form.sf F && Form.sf G
  | .into F => Form.sf F
  | .eqv _ => true
  | .pi _ _ => true
  | .top => true
  | .bot => true
  | .bnd _ => true
  | .seal _ _ => true
  | .unseal _ _ => true
def Form.sf : Form s → Bool
  | .nil => true
  | .cons a F => Atom.sf a && Form.sf F
def Entry.sf : Entry s → Bool
  | .le pre _ post => (SideF.seals pre).isEmpty && SideF.sf pre && (SideF.seals post).isEmpty && SideF.sf post
  | .fld _ sd => SideF.sf sd
  | .alias _ => true
  | .is F => Form.sf F
def Entries.sf : Entries s → Bool
  | .nil => true
  | .cons Es e => Entries.sf Es && Entry.sf e
def SideF.sf : SideF s → Bool
  | .some F => Form.sf F
  | .none => true
  | .bot => true
  | .top => true
end

mutual
def View.sf : View s → Bool
  | .obj V => VEntries.sf V
  | .fn _ _ => true
  | .inst W => View.sf W
  | .none => true
def VEntry.sf : VEntry s → Bool
  | .le F => (Form.seals F).isEmpty && Form.sf F
  | .fld _ W => View.sf W
  | .alias => true
  | .is W => View.sf W
def VEntries.sf : VEntries s → Bool
  | .nil => true
  | .cons V e => VEntries.sf V && VEntry.sf e
end

section SealFree

theorem listNil_of_isEmpty {α : Type} : ∀ {l : List α}, l.isEmpty = true → l = []
  | [], _ => rfl
  | _ :: _, h => by cases h

theorem listNil_of_forall_not_mem {α : Type} : ∀ {l : List α}, (∀ a, a ∈ l → False) → l = []
  | [], _ => rfl
  | a :: _, h => (h a (List.Mem.head _)).elim

theorem Form.sf_append : ∀ (F G : Form s), Form.sf (F.append G) = (Form.sf F && Form.sf G)
  | .nil, _ => by simp [Form.append, Form.sf]
  | .cons a F, G => by simp only [Form.append, Form.sf, Form.sf_append F G, Bool.and_assoc]

theorem SideF.sf_form : ∀ (sd : SideF s), Form.sf sd.form = SideF.sf sd
  | .none => rfl
  | .some _ => rfl
  | .bot => rfl
  | .top => rfl

theorem SideF.seals_form : ∀ (sd : SideF s), Form.seals sd.form = SideF.seals sd
  | .none => rfl
  | .some _ => rfl
  | .bot => rfl
  | .top => rfl

/-- A bound entry built from clean pieces is clean. -/
theorem VEntry.sf_le3 {F G H : Form s} (hF : (Form.seals F).isEmpty = true) (hF' : Form.sf F = true)
    (hG : (Form.seals G).isEmpty = true) (hG' : Form.sf G = true)
    (hH : (Form.seals H).isEmpty = true) (hH' : Form.sf H = true) :
    VEntry.sf (.le (F.append (G.append H))) = true := by
  have hF := listNil_of_isEmpty hF
  have hG := listNil_of_isEmpty hG
  have hH := listNil_of_isEmpty hH
  simp only [VEntry.sf, Form.seals_append, Form.sf_append, hF, hG, hH, hF', hG', hH', List.append_nil,
    List.isEmpty_nil, Bool.and_self]

theorem Form.single_eqv_clean (φ : EqCo s) :
    (Form.seals (Form.single (.eqv φ))).isEmpty = true ∧ Form.sf (Form.single (.eqv φ)) = true := by
  simp [Form.single, Form.seals, Atom.seals, Form.sf, Atom.sf]

theorem VEntries.sf_append : ∀ (V V' : VEntries s), VEntries.sf V = true → VEntries.sf V' = true →
    VEntries.sf (V.append V') = true
  | _, .nil, h, _ => h
  | V, .cons V' e, h, h' => by
      simp only [VEntries.append, VEntries.sf, Bool.and_eq_true] at h' ⊢
      exact ⟨VEntries.sf_append V V' h h'.1, h'.2⟩

theorem VEntries.sf_get : ∀ (V : VEntries s) {i : Nat} {e : VEntry s}, VEntries.sf V = true → V.get i = some e →
    VEntry.sf e = true
  | .nil, _, _, _, h => by simp [VEntries.get] at h
  | .cons V e', i, e, hV, h => by
      simp only [VEntries.sf, Bool.and_eq_true] at hV
      simp only [VEntries.get] at h
      split at h
      · cases h; exact hV.2
      · exact VEntries.sf_get V hV.1 h

theorem VEntry.sf_bridge {F : Form s} (he : VEntry.sf (.le F) = true) (φ ψ : EqCo s) :
    VEntry.sf (.le ((Form.single (.eqv φ)).append (F.append (Form.single (.eqv ψ))))) = true := by
  simp only [VEntry.sf, Bool.and_eq_true] at he
  exact VEntry.sf_le3 (Form.single_eqv_clean φ).1 (Form.single_eqv_clean φ).2 he.1 he.2
    (Form.single_eqv_clean ψ).1 (Form.single_eqv_clean ψ).2

mutual
theorem View.sf_liftAct : ∀ (T : Ty (s,x)) (π : PEq s) (r : Path s) (W : View s), View.sf W = true →
    View.sf (View.liftAct T π r W) = true
  | .mu Tel, π, r, .obj V, hW => VEntries.sf_liftAct V Tel π r hW
  | .pi _ _, _, _, .fn _ _, _ => rfl
  | .bot, _, _, .obj _, hW => hW
  | .sel _ _, _, _, .obj _, hW => hW
  | .pi _ _, _, _, .obj _, hW => hW
  | .bot, _, _, .fn _ _, hW => hW
  | .sel _ _, _, _, .fn _ _, hW => hW
  | .mu _, _, _, .fn _ _, hW => hW
  | .bot, _, _, .inst _, hW => hW
  | .sel _ _, _, _, .inst _, hW => hW
  | .pi _ _, _, _, .inst _, hW => hW
  | .mu _, _, _, .inst _, hW => hW
  | .bot, _, _, .none, hW => hW
  | .sel _ _, _, _, .none, hW => hW
  | .pi _ _, _, _, .none, hW => hW
  | .mu _, _, _, .none, hW => hW
theorem VEntries.sf_liftAct : ∀ (V : VEntries s) (Tel : Telescope ((s,x),x)) (π : PEq s) (r : Path s),
    VEntries.sf V = true → VEntries.sf (VEntries.liftAct V Tel π r) = true
  | .cons V e, .cons Tel pr, π, r, hV => by
      simp only [VEntries.liftAct, VEntries.sf, Bool.and_eq_true] at hV ⊢
      exact ⟨VEntries.sf_liftAct V Tel π r hV.1, VEntry.sf_liftAct e pr π r hV.2⟩
  | .cons _ _, .nil, _, _, hV => hV
  | .nil, _, _, _, hV => by cases ‹Telescope ((s,x),x)› <;> exact hV
theorem VEntry.sf_liftAct : ∀ (e : VEntry s) (pr : Pr ((s,x),x)) (π : PEq s) (r : Path s),
    VEntry.sf e = true → VEntry.sf (VEntry.liftAct e pr π r) = true
  | .le F, .le S T, π, r, he => VEntry.sf_bridge he _ _
  | .fld a W, .fld _ T, π, r, he => View.sf_liftAct _ π _ W he
  | .is W, .is T, π, r, he => View.sf_liftAct _ π r W he
  | .le _, .fld _ _, _, _, he => he
  | .le _, .alias _, _, _, he => he
  | .le _, .is _, _, _, he => he
  | .fld _ _, .le _ _, _, _, he => he
  | .fld _ _, .alias _, _, _, he => he
  | .fld _ _, .is _, _, _, he => he
  | .is _, .le _ _, _, _, he => he
  | .is _, .fld _ _, _, _, he => he
  | .is _, .alias _, _, _, he => he
  | .alias, _, _, _, he => by cases ‹Pr ((s,x),x)› <;> exact he
end

theorem View.sf_liftK : ∀ (T : Ty (s,x)) (π : PEq s) (κ : List (Dir s)) (r : Path s) (W : View s),
    View.sf W = true → View.sf (View.liftK T π κ r W) = true
  | T, π, [], r, W, hW => View.sf_liftAct T π r W hW
  | .pi S _, π, .dom :: κ, r, W, hW => View.sf_liftK S π κ r W hW
  | .pi _ U, π, .cod p :: κ, r, W, hW => View.sf_liftK _ π κ r W hW
  | .bot, _, _ :: _, _, _, hW => by simp only [View.liftK]; exact hW
  | .sel _ _, _, _ :: _, _, _, hW => by simp only [View.liftK]; exact hW
  | .mu _, _, _ :: _, _, _, hW => by simp only [View.liftK]; exact hW

theorem View.sf_transport : ∀ (b : Bool) (φ : EqCo s) (κ : List (Dir s)) (r : Path s) (W : View s),
    View.sf W = true → View.sf (View.transport b φ κ r W) = true
  | _, .refl _, _, _, _, hW => hW
  | b, .symm φ, κ, r, W, hW => View.sf_transport (!b) φ κ r W hW
  | true, .trans φ ψ, κ, r, W, hW => View.sf_transport true ψ κ r _ (View.sf_transport true φ κ r W hW)
  | false, .trans φ ψ, κ, r, W, hW => View.sf_transport false φ κ r _ (View.sf_transport false ψ κ r W hW)
  | _, .defP _ _, _, _, _, hW => hW
  | true, .lift T π, κ, r, W, hW => View.sf_liftK T π κ r W hW
  | false, .lift T π, κ, r, W, hW => View.sf_liftK T (.symm π) κ r W hW
  | b, .dom φ, κ, r, W, hW => View.sf_transport b φ (.dom :: κ) r W hW
  | b, .cod φ p, κ, r, W, hW => View.sf_transport b φ (.cod p :: κ) r W hW

mutual
theorem View.sf_repath (Γ : Ctx s) : ∀ (W : View s) (T : Ty s) (π : PEq s) (r r' : Path s),
    View.sf W = true → View.sf (View.repath Γ W T π r r') = true
  | .obj V, T, π, r, r', hW => by
      simp only [View.repath]
      split
      · exact VEntries.sf_repath Γ V _ π r r' hW
      · exact hW
  | .inst W, T, π, r, r', hW => by
      simp only [View.repath]
      split
      · exact View.sf_repath Γ W _ π r r' hW
      · exact hW
  | .fn _ _, _, _, _, _, hW => hW
  | .none, _, _, _, _, hW => hW
theorem VEntries.sf_repath (Γ : Ctx s) : ∀ (V : VEntries s) (Tel : Telescope (s,x)) (π : PEq s) (r r' : Path s),
    VEntries.sf V = true → VEntries.sf (VEntries.repath Γ V Tel π r r') = true
  | .cons V e, .cons Tel pr, π, r, r', hV => by
      simp only [VEntries.repath, VEntries.sf, Bool.and_eq_true] at hV ⊢
      exact ⟨VEntries.sf_repath Γ V Tel π r r' hV.1, VEntry.sf_repath Γ e pr π r r' hV.2⟩
  | .cons _ _, .nil, _, _, _, hV => hV
  | .nil, _, _, _, _, hV => by cases ‹Telescope (s,x)› <;> exact hV
theorem VEntry.sf_repath (Γ : Ctx s) : ∀ (e : VEntry s) (pr : Pr (s,x)) (π : PEq s) (r r' : Path s),
    VEntry.sf e = true → VEntry.sf (VEntry.repath Γ e pr π r r') = true
  | .le F, .le S T, π, _, _, he => VEntry.sf_bridge he _ _
  | .fld a W, .fld _ T, π, r, r', he =>
      View.sf_liftAct T (.symm π) (r'.sel a) _ (View.sf_repath Γ W _ (.sel π a) _ _ he)
  | .is W, .is T, π, r, r', he =>
      View.sf_liftAct T (.symm π) r' _ (View.sf_repath Γ W _ π r r' he)
  | .le _, .fld _ _, _, _, _, he => he
  | .le _, .alias _, _, _, _, he => he
  | .le _, .is _, _, _, _, he => he
  | .fld _ _, .le _ _, _, _, _, he => he
  | .fld _ _, .alias _, _, _, _, he => he
  | .fld _ _, .is _, _, _, _, he => he
  | .is _, .le _ _, _, _, _, he => he
  | .is _, .fld _ _, _, _, _, he => he
  | .is _, .alias _, _, _, _, he => he
  | .alias, _, _, _, _, he => by cases ‹Pr (s,x)› <;> exact he
end

mutual
theorem Atom.sf_apply : ∀ (a : Atom s) (r : Path s) (W : View s), Atom.sf a = true → View.sf W = true →
    View.sf (View.applyAtom a r W) = true
  | .eqv φ, r, W, _, hW => View.sf_transport true φ [] r W hW
  | .pi _ _, _, .fn _ _, _, _ => rfl
  | .pi _ _, _, .obj _, _, hW => hW
  | .pi _ _, _, .inst _, _, hW => hW
  | .pi _ _, _, .none, _, hW => hW
  | .obj Es, r, .obj V, ha, hW => Entries.sf_apply Es r V ha hW
  | .obj _, _, .fn _ _, _, hW => hW
  | .obj _, _, .inst _, _, hW => hW
  | .obj _, _, .none, _, hW => hW
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, hW => hW
  | .pair F G, r, W, ha, hW => by
      simp only [Atom.sf, Bool.and_eq_true] at ha
      have h₁ := Form.sf_apply F r W ha.1 hW
      have h₂ := Form.sf_apply G r W ha.2 hW
      simp only [View.applyAtom]
      generalize View.applyForm F r W = W₁ at h₁ ⊢
      generalize View.applyForm G r W = W₂ at h₂ ⊢
      cases W₁ with
      | obj V =>
          cases W₂ with
          | obj V' => exact VEntries.sf_append V V' h₁ h₂
          | fn _ _ => exact h₁
          | inst _ => exact h₁
          | none => exact h₁
      | fn _ _ => exact h₁
      | inst _ => exact h₁
      | none => exact h₁
  | .bnd i, _, .obj V, _, hW => by
      simp only [View.applyAtom]
      split
      · rename_i W e
        exact VEntries.sf_get V hW e
      · rfl
  | .bnd _, _, .fn _ _, _, hW => hW
  | .bnd _, _, .inst _, _, hW => hW
  | .bnd _, _, .none, _, hW => hW
  | .into F, r, W, ha, hW => by
      simp only [View.applyAtom, View.sf, VEntries.sf, VEntry.sf, Bool.true_and]
      exact Form.sf_apply F r W ha hW
  | .seal _ _, _, _, _, hW => hW
  | .unseal _ _, _, .inst W, _, hW => hW
  | .unseal _ _, _, .obj _, _, _ => rfl
  | .unseal _ _, _, .fn _ _, _, _ => rfl
  | .unseal _ _, _, .none, _, _ => rfl
theorem Form.sf_apply : ∀ (F : Form s) (r : Path s) (W : View s), Form.sf F = true → View.sf W = true →
    View.sf (View.applyForm F r W) = true
  | .nil, _, _, _, hW => hW
  | .cons a F, r, W, hF, hW => by
      simp only [Form.sf, Bool.and_eq_true] at hF
      exact Form.sf_apply F r _ hF.2 (Atom.sf_apply a r W hF.1 hW)
theorem Entries.sf_apply : ∀ (Es : Entries s) (r : Path s) (V : VEntries s), Entries.sf Es = true →
    VEntries.sf V = true → VEntries.sf (Entries.apply Es r V) = true
  | .nil, _, _, _, _ => rfl
  | .cons Es e, r, V, hE, hV => by
      simp only [Entries.sf, Bool.and_eq_true] at hE
      simp only [Entries.apply, VEntries.sf, Bool.and_eq_true]
      exact ⟨Entries.sf_apply Es r V hE.1 hV, Entry.sf_apply e r V hE.2 hV⟩
theorem Entry.sf_apply : ∀ (e : Entry s) (r : Path s) (V : VEntries s), Entry.sf e = true →
    VEntries.sf V = true → VEntry.sf (Entry.apply e r V) = true
  | .le pre _ post, _, V, he, hV => by
      simp only [Entry.sf, Bool.and_eq_true] at he
      simp only [Entry.apply]
      split
      · rename_i F e
        have hF := VEntries.sf_get V hV e
        simp only [VEntry.sf, Bool.and_eq_true] at hF
        exact VEntry.sf_le3 (by rw [SideF.seals_form]; exact he.1.1.1) (by rw [SideF.sf_form]; exact he.1.1.2)
          hF.1 hF.2 (by rw [SideF.seals_form]; exact he.1.2) (by rw [SideF.sf_form]; exact he.2)
      · rfl
  | .fld _ sd, r, V, he, hV => by
      simp only [Entry.apply]
      split
      · rename_i a W e
        have hW := VEntries.sf_get V hV e
        simp only [VEntry.sf] at hW ⊢
        exact SideF.sf_apply sd _ W he hW
      · rfl
  | .alias _, _, _, _, _ => rfl
  | .is F, r, V, he, hV => Form.sf_apply F r (.obj V) he hV
theorem SideF.sf_apply : ∀ (sd : SideF s) (r : Path s) (W : View s), SideF.sf sd = true → View.sf W = true →
    View.sf (SideF.apply sd r W) = true
  | .none, _, _, _, hW => hW
  | .some F, r, W, hs, hW => Form.sf_apply F r W hs hW
  | .bot, _, _, _, hW => hW
  | .top, _, _, _, _ => rfl
end

mutual
theorem litView_sf : ∀ (l : Path s) (ds : Defs s), VEntries.sf (litView l ds) = true
  | _, .nil => rfl
  | l, .typ ds _ _ => by
      simp only [litView, VEntries.sf, litView_sf l ds]
      simp [VEntry.sf, Form.single, Form.seals, Atom.seals, Form.sf, Atom.sf]
  | l, .fld ds a rhs => by
      simp only [litView, VEntries.sf, VEntry.sf, litView_sf l ds, rhsView_sf l a rhs, Bool.and_self]
  | l, .cls ds _ _ => by
      simp only [litView, VEntries.sf, litView_sf l ds]
      simp [VEntry.sf, Form.single, Form.seals, Atom.seals, Form.sf, Atom.sf]
theorem rhsView_sf : ∀ (l : Path s) (a : Label) (rhs : Rhs s), View.sf (rhsView l a rhs) = true
  | _, _, .path _ => rfl
  | _, _, .fn _ => rfl
  | l, a, .nest _ ds => litView_sf (l.sel a) ds
end

theorem varView_sf (σ : Store s) (x : BVar s .var) : View.sf (varView σ x) = true := by
  unfold varView
  split
  · rfl
  · exact litView_sf _ _
  · rfl

/-- A side meeting the predicate has no seal in its own head. -/
theorem LeCo.sealsIn_none {ξ : Alloc s} {e : LeCo s} (h : LeCo.sealsOK none ξ e = true) :
    ∀ a, a ∈ LeCo.sealsIn e → False := fun ⟨q, D⟩ ha => by
  obtain ⟨_, e', _⟩ := LeCo.sealsOK_sealsIn e h ha
  cases e'

mutual
/-- **Every seal of a normal form is a seal of the evidence's head**, for evidence meeting the
predicate at any head.  A `member` read adds no seal. -/
theorem Hnf.sf {A : Alloc s} {σ : Store s} {Γ : Ctx s} : ∀ {e : LeCo s} {S T : Ty s} {F : Form s},
    Hnf σ Γ e S T F → ∀ {h : Option (Path s)}, LeCo.sealsOK h A e = true →
    Form.sf F = true ∧ ∀ a, a ∈ Form.seals F → a ∈ LeCo.sealsIn e
  | _, _, _, _, .refl, _, _ => ⟨rfl, fun _ ha => by simp [Form.seals] at ha⟩
  | _, _, _, _, .trans h₁ h₂, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      obtain ⟨s₁, i₁⟩ := Hnf.sf h₁ he.1
      obtain ⟨s₂, i₂⟩ := Hnf.sf h₂ he.2
      refine ⟨by rw [Form.sf_append, s₁, s₂]; rfl, fun a ha => ?_⟩
      rw [Form.seals_append, List.mem_append] at ha
      simp only [LeCo.sealsIn, List.mem_append]
      rcases ha with ha | ha
      · exact .inl (i₁ a ha)
      · exact .inr (i₂ a ha)
  | _, _, _, _, .top, _, _ => ⟨rfl, fun _ ha => by simp [Form.single, Form.seals, Atom.seals] at ha⟩
  | _, _, _, _, .bot, _, _ => ⟨rfl, fun _ ha => by simp [Form.single, Form.seals, Atom.seals] at ha⟩
  | _, _, _, _, .eqToLe _, _, _ => ⟨rfl, fun _ ha => by simp [Form.single, Form.seals, Atom.seals] at ha⟩
  | _, _, _, _, .pi _ _, _, _ => ⟨rfl, fun _ ha => by simp [Form.single, Form.seals, Atom.seals] at ha⟩
  | _, _, _, _, .obj hm, _, he => by
      obtain ⟨s₁, i₁⟩ := HnfM.sf hm he
      refine ⟨by simp only [Form.single, Form.sf, Atom.sf, s₁, Bool.and_self], fun a ha => ?_⟩
      simp only [Form.single, Form.seals, Atom.seals, List.append_nil] at ha
      exact i₁ a ha
  | _, _, _, _, .pair h₁ h₂, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      obtain ⟨s₁, i₁⟩ := Hnf.sf h₁ he.1
      obtain ⟨s₂, i₂⟩ := Hnf.sf h₂ he.2
      refine ⟨by simp only [Form.single, Form.sf, Atom.sf, s₁, s₂, Bool.and_self], fun a ha => ?_⟩
      simp only [Form.single, Form.seals, Atom.seals, List.append_nil, List.mem_append] at ha
      simp only [LeCo.sealsIn, List.mem_append]
      rcases ha with ha | ha
      · exact .inl (i₁ a ha)
      · exact .inr (i₂ a ha)
  | _, _, _, _, .bound _, _, _ => ⟨rfl, fun _ ha => by simp [Form.single, Form.seals, Atom.seals] at ha⟩
  | _, _, _, _, .intoBnd h₁, _, he => by
      obtain ⟨s₁, i₁⟩ := Hnf.sf h₁ he
      refine ⟨by simp only [Form.single, Form.sf, Atom.sf, s₁, Bool.and_self], fun a ha => ?_⟩
      simp only [Form.single, Form.seals, Atom.seals, List.append_nil] at ha
      exact i₁ a ha
  | _, _, _, _, .member (P := P) hP he' _ hV hg, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      have hW := PV.sf hP he.1
      have hF := (Hnf.sf he' he.2).1
      have hV' := Form.sf_apply _ P.path _ hF hW
      rw [hV] at hV'
      have hG := VEntries.sf_get _ hV' hg
      simp only [VEntry.sf, Bool.and_eq_true] at hG
      exact ⟨hG.2, fun a ha => by rw [listNil_of_isEmpty hG.1] at ha; cases ha⟩
  | _, _, _, _, .seal _, _, _ => ⟨rfl, fun a ha => by simpa [Form.single, Form.seals, Atom.seals, LeCo.sealsIn] using ha⟩
theorem HnfM.sf {A : Alloc s} {σ : Store s} {Γ : Ctx s} : ∀ {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} {Es : Entries s}, HnfM σ Γ src m Tel Es →
    ∀ {h : Option (Path s)}, Morphism.sealsOK h A m = true →
    Entries.sf Es = true ∧ ∀ a, a ∈ Entries.seals Es → a ∈ Morphism.sealsIn m
  | _, _, _, _, .nil, _, _ => ⟨rfl, fun _ ha => by simp [Entries.seals] at ha⟩
  | _, _, _, _, .le h₁ _ h₂ h₃, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      obtain ⟨s₁, i₁⟩ := HnfM.sf h₁ hm.1.1
      obtain ⟨s₂, e₂⟩ := HnfS.sf h₂ hm.1.2
      obtain ⟨s₃, e₃⟩ := HnfS.sf h₃ hm.2
      refine ⟨by simp only [Entries.sf, Entry.sf, s₁, s₂, s₃, e₂, e₃, List.isEmpty_nil, Bool.and_self], fun a ha => ?_⟩
      simp only [Entries.seals, Entry.seals, e₂, e₃, List.append_nil] at ha
      simp only [Morphism.sealsIn, List.mem_append]
      exact .inl (.inl (i₁ a ha))
  | _, _, _, _, .fld h₁ _ h₂, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      obtain ⟨s₁, i₁⟩ := HnfM.sf h₁ hm.1
      obtain ⟨s₂, e₂⟩ := HnfS.sf h₂ hm.2
      refine ⟨by simp only [Entries.sf, Entry.sf, s₁, s₂, Bool.and_self], fun a ha => ?_⟩
      simp only [Entries.seals, Entry.seals, e₂, List.append_nil] at ha
      simp only [Morphism.sealsIn, List.mem_append]
      exact .inl (i₁ a ha)
  | _, _, _, _, .alias h₁ _, _, hm => by
      obtain ⟨s₁, i₁⟩ := HnfM.sf h₁ hm
      refine ⟨by simp only [Entries.sf, Entry.sf, s₁, Bool.and_self], fun a ha => ?_⟩
      simp only [Entries.seals, Entry.seals, List.append_nil] at ha
      exact i₁ a ha
  | _, _, _, _, .is h₁ h₂, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      obtain ⟨s₁, i₁⟩ := HnfM.sf h₁ hm.1
      obtain ⟨s₂, i₂⟩ := Hnf.sf h₂ hm.2
      refine ⟨by simp only [Entries.sf, Entry.sf, s₁, s₂, Bool.and_self], fun a ha => ?_⟩
      simp only [Entries.seals, Entry.seals, List.mem_append] at ha
      simp only [Morphism.sealsIn, List.mem_append]
      rcases ha with ha | ha
      · exact .inl (i₁ a ha)
      · exact .inr (i₂ a ha)
theorem HnfS.sf {A : Alloc s} {σ : Store s} {Γ : Ctx s} : ∀ {sd : Side s} {X Y : Ty (s,x)} {sf : SideF s},
    HnfS σ Γ sd X Y sf → Side.sealsOK A sd = true → SideF.sf sf = true ∧ SideF.seals sf = []
  | _, _, _, _, .none, _ => ⟨rfl, rfl⟩
  | _, _, _, _, .some h₁, hs => by
      obtain ⟨s₁, i₁⟩ := Hnf.sf h₁ (h := none) hs
      refine ⟨s₁, ?_⟩
      show Form.seals _ = []
      exact listNil_of_forall_not_mem (fun a ha => LeCo.sealsIn_none hs a (i₁ a ha))
  | _, _, _, _, .bot, _ => ⟨rfl, rfl⟩
  | _, _, _, _, .top, _ => ⟨rfl, rfl⟩
theorem PV.sf {A : Alloc s} {σ : Store s} {Γ : Ctx s} : ∀ {P : PathCo s} {T : Ty s} {W : View s},
    PV σ Γ P T W → PathCo.sealsOK A P = true → View.sf W = true
  | _, _, _, .var _, _ => varView_sf σ _
  | _, _, _, .sel hP _ hg, hok => VEntries.sf_get _ (PV.sf hP hok) hg
  | _, _, _, .cast hP he, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact Form.sf_apply _ _ _ (Hnf.sf he hok.2).1 (PV.sf hP hok.1)
  | _, _, _, .alias hQ, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact View.sf_repath Γ _ _ _ _ _ (PV.sf hQ hok.2)
  | _, _, _, .sngl, _ => rfl
  | _, _, _, .fldI hQ, hok => by
      simp only [View.sf, VEntries.sf, VEntry.sf, Bool.true_and]
      exact PV.sf hQ hok
  | _, _, _, .unfold hP, hok => PV.sf hP hok
  | _, _, _, .fold hP, hok => PV.sf hP hok
  | _, _, _, .both hP hQ, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact VEntries.sf_append _ _ (PV.sf hP hok.1) (PV.sf hQ hok.2)
end

end SealFree

/-- `fold` keeps a self bound `is X↑` at its index: the folded path's type is below `C` when the
fold's is. -/
theorem Below.unfoldTel {Γ : Ctx s} {c : Path s} {C : Label} {Tel : Telescope (s,x)} {p : Path s}
    (h : Below Γ c C (.mu Tel)) : Below Γ c C (.mu (Tel.substPath p).weaken) := by
  obtain ⟨i, X, hi, hX⟩ := h.mu_inv
  have h1 := hi.subst (PathSubst.one p)
  have e1 : (Pr.is X.weaken : Pr (s,x)).subst (PathSubst.one p) = .is X := by
    show Pr.is ((X.weaken).substPath p) = _
    rw [Ty.weaken_substPath]
  rw [e1] at h1
  have h2 := h1.rename (Rename.succ (k := .var))
  exact .is (Γ.res_mu _) h2 hX

/-- No self bound in a singleton or a one-field type: neither is below a class. -/
theorem Below.not_sngl {Γ : Ctx s} {c : Path s} {C : Label} {q : Path s} (h : Below Γ c C (Ty.sngl q)) : False := by
  obtain ⟨i, X, hi, _⟩ := h.mu_inv
  rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi
  · cases e
  · exact Telescope.At.nil_of_eq hi rfl
theorem Below.not_fld {Γ : Ctx s} {c : Path s} {C : Label} {a : Label} {T : Ty (s,x)}
    (h : Below Γ c C (.mu (.cons .nil (.fld a T)))) : False := by
  obtain ⟨i, X, hi, _⟩ := h.mu_inv
  rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi
  · cases e
  · exact Telescope.At.nil_of_eq hi rfl

/-- The telescope of typed definitions has no self bound `is X`: DF-Typ and DF-Cls add `le`, DF-Path,
DF-Fun and DF-Nest add `fld`. -/
theorem Defs.HasType.not_at_is {Γ : Ctx s} {p : Path s} {ds : Defs s} {Tel : Telescope (s,x)} :
    Defs.HasType Γ p ds Tel → ∀ {i : Nat} {X : Ty (s,x)}, ¬ Tel.At i (.is X)
  | .nil, _, _, h => Telescope.At.nil_of_eq h rfl
  | .typ hds _ _, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
      · cases e
      · rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
        · cases e
        · exact Defs.HasType.not_at_is hds h
  | .path hds _ _ _, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
      · cases e
      · exact Defs.HasType.not_at_is hds h
  | .fn hds _ _ _, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
      · cases e
      · exact Defs.HasType.not_at_is hds h
  | .nest hds _ _, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
      · cases e
      · exact Defs.HasType.not_at_is hds h
  | .cls hds _ _, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
      · cases e
      · rcases Telescope.At.cons_of_eq h rfl with ⟨_, e⟩ | h
        · cases e
        · exact Defs.HasType.not_at_is hds h

/-- The type of a store variable is below no class: a function type, or a literal's object type with
no self bound. -/
theorem Store.Typed.var_not_below {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) (y : BVar s .var)
    {c : Path s} {C : Label} : ¬ Below Γ c C (Γ.ty y) := fun hB => by
  rcases hσ.get_shape y with ⟨S, t, T, _, hT, _⟩ | ⟨Tel, ds, hg, hT, _⟩
  · rw [hT] at hB
    exact hB.not_pi
  · rw [hT] at hB
    obtain ⟨i, X, hi, _⟩ := hB.mu_inv
    exact Defs.HasType.not_at_is (hσ.literal y hg) hi

/-- The last seal of a chain of `trans`: the evidence ends in `seal q D`. -/
def LeCo.lastSeal : LeCo s → Option (Path s × Label)
  | .seal q D => some (q, D)
  | .trans _ f => LeCo.lastSeal f
  | _ => none

/-- Evidence that ends in a seal is typed into that seal's class selection. -/
theorem LeCo.lastSeal_target {Γ : Ctx s} : ∀ {e : LeCo s} {S T : Ty s} {q : Path s} {D : Label},
    LeCo.HasType Γ e S T → LeCo.lastSeal e = some (q, D) → T = .sel q D
  | .seal _ _, _, _, _, _, h, hl => by
      simp only [LeCo.lastSeal, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      cases h; rfl
  | .trans _ f, _, _, _, _, h, hl => by
      cases h with
      | trans _ h₂ => exact LeCo.lastSeal_target (e := f) h₂ hl
  | .refl _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .top _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .bot _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .eqToLe _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .pi _ _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .obj _ _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .pair _ _ _ _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .bound _ _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .intoBnd _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | .member _ _ _, _, _, _, _, _, hl => by simp [LeCo.lastSeal] at hl

/-- The last seal sits at the head: at the variable the evidence acts on, with an admitted label. -/
theorem LeCo.lastSeal_ok {ξ : Alloc s} : ∀ {h : Option (Path s)} {e : LeCo s} {q : Path s} {D : Label},
    LeCo.sealsOK h ξ e = true → LeCo.lastSeal e = some (q, D) → ∃ y, h = some (.var y) ∧ ξ y (q, D) = true
  | h, .seal _ _, _, _, hok, hl => by
      simp only [LeCo.lastSeal, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      match h, hok with
      | some (.var y), hok => exact ⟨y, rfl, hok⟩
      | some (.sel _ _), hok => simp [LeCo.sealsOK] at hok
      | none, hok => simp [LeCo.sealsOK] at hok
  | _, .trans _ f, _, _, hok, hl => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at hok
      exact LeCo.lastSeal_ok (e := f) hok.2 hl
  | _, .refl _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .top _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .bot _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .eqToLe _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .pi _ _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .obj _ _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .pair _ _ _ _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .bound _ _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .intoBnd _, _, _, _, hl => by simp [LeCo.lastSeal] at hl
  | _, .member _ _ _, _, _, _, hl => by simp [LeCo.lastSeal] at hl

/-- A cast whose evidence ends in a seal, decided. -/
def PathCo.endsInSeal : PathCo s → Bool
  | .cast _ e => (LeCo.lastSeal e).isSome
  | _ => false

/-- The fragment of the corollary: every path former but a field selection `sel` and `unfold`.  A cast
is in it when its operand is, or when its evidence ends in a seal, over any path. -/
def PathCo.Frag : PathCo s → Prop
  | .var _ => True
  | .cast P e => PathCo.Frag P ∨ (LeCo.lastSeal e).isSome
  | .both _ _ P Q => PathCo.Frag P ∧ PathCo.Frag Q
  | .alias _ _ Q => PathCo.Frag Q
  | .fold _ P => PathCo.Frag P
  | .sngl _ _ _ => True
  | .fldI _ _ _ => True
  | .sel _ _ _ => False
  | .unfold _ => False

/-- **The corollary on the fragment.**  Over a typed store, a path of the fragment that meets the
predicate and is typed at a type below the class `C` names, up to `canon`, a store variable `y` whose
allocation sealed it at the class `q∙D` itself (its record holds `(q, D)`), and `q∙D` is below `C`. -/
theorem frag_provenance {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {A : Alloc s} {c : Path s} {C : Label} :
    ∀ (P : PathCo s) {T : Ty s}, PathCo.Frag P → PathCo.sealsOK A P = true → PathCo.HasType Γ P T →
      Below Γ c C T → ∃ y q D, Γ.canon P.path = Γ.canon (.var y) ∧ A y (q, D) = true ∧ Below Γ c C (.sel q D)
  | .var y, _, _, _, hT, hB => by
      cases hT with
      | var e => exact absurd (e ▸ hB) (Store.Typed.var_not_below hσ y)
  | .cast P e, _, hf, hok, hT, hB => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      cases hT with
      | cast hP he =>
          rcases hf with hfP | hl
          · obtain ⟨F, hF, hb⟩ := le_below hσ he hB
            rcases hb with hS | ⟨q, D, hq, hqD⟩
            · exact frag_provenance hσ P hfP hok.1 hP hS
            · obtain ⟨y, hy, hA⟩ := LeCo.sealsOK_sealsIn e hok.2 ((Hnf.sf hF hok.2).2 _ hq)
              exact ⟨y, q, D, by rw [PathCo.path, Option.some.inj hy], hA, hqD⟩
          · obtain ⟨⟨q, D⟩, hl⟩ := Option.isSome_iff_exists.1 hl
            have hT := LeCo.lastSeal_target he hl
            subst hT
            obtain ⟨y, hy, hA⟩ := LeCo.lastSeal_ok hok.2 hl
            exact ⟨y, q, D, by rw [PathCo.path, Option.some.inj hy], hA, hB⟩
  | .both Tel Tel' P Q, _, hf, hok, hT, hB => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      cases hT with
      | both hP hQ hpq =>
          obtain ⟨i, X, hi, hX⟩ := hB.mu_inv
          rcases Telescope.At.of_append Tel Tel' hi with hi | ⟨j, -, hj⟩
          · exact frag_provenance hσ P hf.1 hok.1 hP (.is (Γ.res_mu Tel) hi hX)
          · obtain ⟨y, q, D, hy, hA, hqD⟩ := frag_provenance hσ Q hf.2 hok.2 hQ (.is (Γ.res_mu Tel') hj hX)
            exact ⟨y, q, D, by rw [PathCo.path, ← hpq, hy], hA, hqD⟩
  | .alias P₀ π Q, _, hf, hok, hT, hB => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      cases hT with
      | alias _ hπ hQ =>
          obtain ⟨y, q, D, hy, hA, hqD⟩ := frag_provenance hσ Q hf hok.2 hQ hB
          exact ⟨y, q, D, by rw [PathCo.path, alias_canon hσ hπ, hy], hA, hqD⟩
  | .fold Tel P, _, hf, hok, hT, hB => by
      cases hT with
      | fold hP =>
          obtain ⟨y, q, D, hy, hA, hqD⟩ := frag_provenance hσ P hf hok hP (Below.unfoldTel hB)
          exact ⟨y, q, D, by rw [PathCo.path, hy], hA, hqD⟩
  | .sngl _ _ _, _, _, _, hT, hB => by
      cases hT with
      | sngl _ _ => exact (Below.not_sngl hB).elim
  | .fldI _ _ _, _, _, _, hT, hB => by
      cases hT with
      | fldI _ _ => exact (Below.not_fld hB).elim
  | .sel _ _ _, _, hf, _, _, _ => hf.elim
  | .unfold _, _, hf, _, _, _ => hf.elim

/-- **The reachable-state theorem at the machine `Step appView`**: no hypothesis left. -/
theorem reachable_sealsAtCtors_appView {t : Tm []} {s' : Sig} {st : State s'} (ht : Tm.InitSeals t = true)
    (run : Steps appView ⟨.nil, .nil, t⟩ st) :
    ∃ A : Alloc s', ASteps appView ⟨⟨.nil, .nil, t⟩, Alloc.empty⟩ ⟨st, A⟩ ∧ State.SealsAtCtors A st = true ∧
      A.OwnersOlder :=
  reachable_sealsAtCtors appView_sealsOK ht run

/-- **The provenance theorem, at a class selection**, for a reachable state of the machine `Step appView`.  A
typed program that meets the initial condition reaches only states whose allocation records `A` (the
function of the run that `AStep` computes) have this property: every owner is older than the variable it
seals, and a path of the fragment that meets the predicate under `A` and is typed at a class selection
`p∙C` names, up to `canon`, a store variable `y` whose allocation sealed it at a class `q∙D` below `C`. -/
theorem provenance {t : Tm []} {T₀ : Ty []} (ht : Tm.HasType .nil t T₀) (hi : Tm.InitSeals t = true) {s' : Sig}
    {st : State s'} (run : Steps appView ⟨.nil, .nil, t⟩ st) :
    ∃ (A : Alloc s') (Γ : Ctx s'), ASteps appView ⟨⟨.nil, .nil, t⟩, Alloc.empty⟩ ⟨st, A⟩ ∧
      State.SealsAtCtors A st = true ∧ A.OwnersOlder ∧ Store.Typed st.σ Γ ∧
      ∀ (P : PathCo s') (p c : Path s') (C : Label) (U : Ty s'), PathCo.Frag P → PathCo.sealsOK A P = true →
        PathCo.HasType Γ P (.sel p C) → Γ.canon p = some c → Γ.clsOf (.sel p C) = some U →
        ∃ y q D, Γ.canon P.path = Γ.canon (.var y) ∧ A y (q, D) = true ∧ Below Γ c C (.sel q D) := by
  obtain ⟨A, hA, hst, hold⟩ := reachable_sealsAtCtors_appView hi run
  obtain ⟨ρ, Γ, T, hσ, _, _⟩ := Steps.typed (st := ⟨.nil, .nil, t⟩) ⟨.nil, T₀, .nil, ht, .nil⟩ run
  refine ⟨A, Γ, hA, hst, hold, hσ, fun P p c C U hf hok hP hc hcl => ?_⟩
  exact frag_provenance hσ P hf hok hP (.self (Ctx.res_cls hcl) hc)

/-- **Provenance of the focus.**  The same at the path the reached state holds in focus: no
hypothesis on the path but its typing and the fragment. -/
theorem provenance_focus {t : Tm []} {T₀ : Ty []} (ht : Tm.HasType .nil t T₀) (hi : Tm.InitSeals t = true)
    {s' : Sig} {st : State s'} (run : Steps appView ⟨.nil, .nil, t⟩ st) {P : PathCo s'} (hP : st.t = .path P) :
    ∃ (A : Alloc s') (Γ : Ctx s'), ASteps appView ⟨⟨.nil, .nil, t⟩, Alloc.empty⟩ ⟨st, A⟩ ∧ Store.Typed st.σ Γ ∧
      ∀ (p c : Path s') (C : Label) (U : Ty s'), PathCo.Frag P → PathCo.HasType Γ P (.sel p C) →
        Γ.canon p = some c → Γ.clsOf (.sel p C) = some U →
        ∃ y q D, Γ.canon P.path = Γ.canon (.var y) ∧ A y (q, D) = true ∧ Below Γ c C (.sel q D) := by
  obtain ⟨A, Γ, hA, hst, _, hσ, hprov⟩ := provenance ht hi run
  exact ⟨A, Γ, hA, hσ, fun p c C U hf hT hc hcl =>
    hprov P p c C U hf (State.focus_sealsOK hst hP) hT hc hcl⟩

end Nominal.FCn
