import Coercions.Nominal.FCn.Provenance

/-!
# Run-time provenance: the application view meets the predicate (plan XII, stage NR)

Forms and views carry evidence only in `eqv` and `pi` atoms and in the stored values of function
views.  `Form.ok` and `View.ok` ask those to meet the predicate, with no seal at the head of a `pi`
atom's components.  The normalizer, the path view, the stored casts and the collapse of a function
form keep both, so `appView` meets `AppView.SealsOK`.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The application view meets the hypothesis: `appView_sealsOK`

Forms and views carry evidence only in `eqv` and `pi` atoms and in the stored values of function
views.  `Form.ok` asks those to meet the predicate with no seal at the head, `View.ok` asks it of
every form and function value of a view.  The normalizer, the path view, the stored casts and the
collapse of the head keep both. -/

mutual
def Atom.ok : Alloc s → Atom s → Bool
  | A, .eqv φ => EqCo.sealsOK A φ
  | A, .pi e f => LeCo.sealsOK none A e && LeCo.sealsOK none (A.cons Lbl.none) f
  | A, .obj Es => Entries.ok A Es
  | A, .pair F G => Form.ok A F && Form.ok A G
  | A, .into F => Form.ok A F
  | _, .top => true
  | _, .bot => true
  | _, .bnd _ => true
  | _, .seal _ _ => true
  | _, .unseal _ _ => true
def Form.ok : Alloc s → Form s → Bool
  | _, .nil => true
  | A, .cons a F => Atom.ok A a && Form.ok A F
def Entry.ok : Alloc s → Entry s → Bool
  | A, .le pre _ post => SideF.ok A pre && SideF.ok A post
  | A, .fld _ sd => SideF.ok A sd
  | _, .alias _ => true
  | A, .is F => Form.ok A F
def Entries.ok : Alloc s → Entries s → Bool
  | _, .nil => true
  | A, .cons Es e => Entries.ok A Es && Entry.ok A e
def SideF.ok : Alloc s → SideF s → Bool
  | _, .none => true
  | A, .some F => Form.ok A F
  | _, .bot => true
  | _, .top => true
end

mutual
def View.ok : Alloc s → View s → Bool
  | A, .obj V => VEntries.ok A V
  | A, .fn v F => Value.sealsOK A v && Form.ok A F
  | A, .inst W => View.ok A W
  | _, .none => true
def VEntry.ok : Alloc s → VEntry s → Bool
  | A, .le F => Form.ok A F
  | A, .fld _ W => View.ok A W
  | _, .alias => true
  | A, .is W => View.ok A W
def VEntries.ok : Alloc s → VEntries s → Bool
  | _, .nil => true
  | A, .cons V e => VEntries.ok A V && VEntry.ok A e
end

section Views
variable {A : Alloc s}

theorem Form.ok_append : ∀ (F G : Form s), Form.ok A (F.append G) = (Form.ok A F && Form.ok A G)
  | .nil, _ => by simp [Form.append, Form.ok]
  | .cons a F, G => by simp only [Form.append, Form.ok, Form.ok_append F G, Bool.and_assoc]

theorem VEntries.ok_append : ∀ (V V' : VEntries s), VEntries.ok A V = true → VEntries.ok A V' = true →
    VEntries.ok A (V.append V') = true
  | _, .nil, h, _ => h
  | V, .cons V' e, h, h' => by
      simp only [VEntries.append, VEntries.ok, Bool.and_eq_true] at h' ⊢
      exact ⟨VEntries.ok_append V V' h h'.1, h'.2⟩

theorem VEntries.ok_get : ∀ (V : VEntries s) {i : Nat} {e : VEntry s}, VEntries.ok A V = true → V.get i = some e →
    VEntry.ok A e = true
  | .nil, _, _, _, h => by simp [VEntries.get] at h
  | .cons V e', i, e, hV, h => by
      simp only [VEntries.ok, Bool.and_eq_true] at hV
      simp only [VEntries.get] at h
      split at h
      · cases h; exact hV.2
      · exact VEntries.ok_get V hV.1 h

theorem SideF.ok_form : ∀ (sd : SideF s), SideF.ok A sd = true → Form.ok A sd.form = true
  | .none, _ => rfl
  | .some _, h => h
  | .bot, _ => rfl
  | .top, _ => rfl

theorem Form.ok_single_eqv {φ : EqCo s} (h : EqCo.sealsOK A φ = true) : Form.ok A (Form.single (.eqv φ)) = true := by
  simp only [Form.single, Form.ok, Atom.ok, h, Bool.and_self]

/-! ### `liftAct`, `liftK`, `transport`, `repath` -/

mutual
theorem View.ok_liftAct : ∀ (T : Ty (s,x)) (π : PEq s) (r : Path s) (W : View s), View.ok A W = true →
    PEq.sealsOK A π = true → View.ok A (View.liftAct T π r W) = true
  | .mu Tel, π, r, .obj V, hW, hπ => VEntries.ok_liftAct V Tel π r hW hπ
  | .pi S T, π, _, .fn v F, hW, hπ => by
      simp only [View.liftAct, View.ok, Bool.and_eq_true, Form.ok_append] at hW ⊢
      exact ⟨hW.1, hW.2, Form.ok_single_eqv hπ⟩
  | .bot, _, _, .obj _, hW, _ => hW
  | .sel _ _, _, _, .obj _, hW, _ => hW
  | .pi _ _, _, _, .obj _, hW, _ => hW
  | .bot, _, _, .fn _ _, hW, _ => hW
  | .sel _ _, _, _, .fn _ _, hW, _ => hW
  | .mu _, _, _, .fn _ _, hW, _ => hW
  | .bot, _, _, .inst _, hW, _ => hW
  | .sel _ _, _, _, .inst _, hW, _ => hW
  | .pi _ _, _, _, .inst _, hW, _ => hW
  | .mu _, _, _, .inst _, hW, _ => hW
  | .bot, _, _, .none, hW, _ => hW
  | .sel _ _, _, _, .none, hW, _ => hW
  | .pi _ _, _, _, .none, hW, _ => hW
  | .mu _, _, _, .none, hW, _ => hW
theorem VEntries.ok_liftAct : ∀ (V : VEntries s) (Tel : Telescope ((s,x),x)) (π : PEq s) (r : Path s),
    VEntries.ok A V = true → PEq.sealsOK A π = true → VEntries.ok A (VEntries.liftAct V Tel π r) = true
  | .cons V e, .cons Tel pr, π, r, hV, hπ => by
      simp only [VEntries.liftAct, VEntries.ok, Bool.and_eq_true] at hV ⊢
      exact ⟨VEntries.ok_liftAct V Tel π r hV.1 hπ, VEntry.ok_liftAct e pr π r hV.2 hπ⟩
  | .cons _ _, .nil, _, _, hV, _ => hV
  | .nil, _, _, _, hV, _ => by cases ‹Telescope ((s,x),x)› <;> exact hV
theorem VEntry.ok_liftAct : ∀ (e : VEntry s) (pr : Pr ((s,x),x)) (π : PEq s) (r : Path s),
    VEntry.ok A e = true → PEq.sealsOK A π = true → VEntry.ok A (VEntry.liftAct e pr π r) = true
  | .le F, .le S T, π, r, he, hπ => by
      simp only [VEntry.liftAct, VEntry.ok, Form.ok_append, Bool.and_eq_true] at he ⊢
      exact ⟨Form.ok_single_eqv (A := A) (φ := .lift _ (.symm π)) hπ, he, Form.ok_single_eqv hπ⟩
  | .fld a W, .fld _ T, π, r, he, hπ => View.ok_liftAct _ π _ W he hπ
  | .is W, .is T, π, r, he, hπ => View.ok_liftAct _ π r W he hπ
  | .le _, .fld _ _, _, _, he, _ => he
  | .le _, .alias _, _, _, he, _ => he
  | .le _, .is _, _, _, he, _ => he
  | .fld _ _, .le _ _, _, _, he, _ => he
  | .fld _ _, .alias _, _, _, he, _ => he
  | .fld _ _, .is _, _, _, he, _ => he
  | .is _, .le _ _, _, _, he, _ => he
  | .is _, .fld _ _, _, _, he, _ => he
  | .is _, .alias _, _, _, he, _ => he
  | .alias, _, _, _, he, _ => by cases ‹Pr ((s,x),x)› <;> exact he
end

theorem View.ok_liftK : ∀ (T : Ty (s,x)) (π : PEq s) (κ : List (Dir s)) (r : Path s) (W : View s),
    View.ok A W = true → PEq.sealsOK A π = true → View.ok A (View.liftK T π κ r W) = true
  | T, π, [], r, W, hW, hπ => View.ok_liftAct T π r W hW hπ
  | .pi S _, π, .dom :: κ, r, W, hW, hπ => View.ok_liftK S π κ r W hW hπ
  | .pi _ U, π, .cod p :: κ, r, W, hW, hπ => View.ok_liftK _ π κ r W hW hπ
  | .bot, _, _ :: _, _, _, hW, _ => by simp only [View.liftK]; exact hW
  | .sel _ _, _, _ :: _, _, _, hW, _ => by simp only [View.liftK]; exact hW
  | .mu _, _, _ :: _, _, _, hW, _ => by simp only [View.liftK]; exact hW

theorem View.ok_transport : ∀ (b : Bool) (φ : EqCo s) (κ : List (Dir s)) (r : Path s) (W : View s),
    EqCo.sealsOK A φ = true → View.ok A W = true → View.ok A (View.transport b φ κ r W) = true
  | _, .refl _, _, _, _, _, hW => hW
  | b, .symm φ, κ, r, W, hφ, hW => View.ok_transport (!b) φ κ r W hφ hW
  | true, .trans φ ψ, κ, r, W, hφ, hW => by
      simp only [EqCo.sealsOK, Bool.and_eq_true] at hφ
      exact View.ok_transport true ψ κ r _ hφ.2 (View.ok_transport true φ κ r W hφ.1 hW)
  | false, .trans φ ψ, κ, r, W, hφ, hW => by
      simp only [EqCo.sealsOK, Bool.and_eq_true] at hφ
      exact View.ok_transport false φ κ r _ hφ.1 (View.ok_transport false ψ κ r W hφ.2 hW)
  | _, .defP _ _, _, _, _, _, hW => hW
  | true, .lift T π, κ, r, W, hφ, hW => View.ok_liftK T π κ r W hW hφ
  | false, .lift T π, κ, r, W, hφ, hW => View.ok_liftK T (.symm π) κ r W hW hφ
  | b, .dom φ, κ, r, W, hφ, hW => View.ok_transport b φ (.dom :: κ) r W hφ hW
  | b, .cod φ p, κ, r, W, hφ, hW => View.ok_transport b φ (.cod p :: κ) r W hφ hW

mutual
theorem View.ok_repath (Γ : Ctx s) : ∀ (W : View s) (T : Ty s) (π : PEq s) (r r' : Path s),
    View.ok A W = true → PEq.sealsOK A π = true → View.ok A (View.repath Γ W T π r r') = true
  | .obj V, T, π, r, r', hW, hπ => by
      simp only [View.repath]
      split
      · exact VEntries.ok_repath Γ V _ π r r' hW hπ
      · exact hW
  | .inst W, T, π, r, r', hW, hπ => by
      simp only [View.repath]
      split
      · exact View.ok_repath Γ W _ π r r' hW hπ
      · exact hW
  | .fn _ _, _, _, _, _, hW, _ => hW
  | .none, _, _, _, _, hW, _ => hW
theorem VEntries.ok_repath (Γ : Ctx s) : ∀ (V : VEntries s) (Tel : Telescope (s,x)) (π : PEq s) (r r' : Path s),
    VEntries.ok A V = true → PEq.sealsOK A π = true → VEntries.ok A (VEntries.repath Γ V Tel π r r') = true
  | .cons V e, .cons Tel pr, π, r, r', hV, hπ => by
      simp only [VEntries.repath, VEntries.ok, Bool.and_eq_true] at hV ⊢
      exact ⟨VEntries.ok_repath Γ V Tel π r r' hV.1 hπ, VEntry.ok_repath Γ e pr π r r' hV.2 hπ⟩
  | .cons _ _, .nil, _, _, _, hV, _ => hV
  | .nil, _, _, _, _, hV, _ => by cases ‹Telescope (s,x)› <;> exact hV
theorem VEntry.ok_repath (Γ : Ctx s) : ∀ (e : VEntry s) (pr : Pr (s,x)) (π : PEq s) (r r' : Path s),
    VEntry.ok A e = true → PEq.sealsOK A π = true → VEntry.ok A (VEntry.repath Γ e pr π r r') = true
  | .le F, .le S T, π, _, _, he, hπ => by
      simp only [VEntry.repath, VEntry.ok, Form.ok_append, Bool.and_eq_true] at he ⊢
      exact ⟨Form.ok_single_eqv hπ, he, Form.ok_single_eqv (A := A) (φ := .lift T (.symm π)) hπ⟩
  | .fld a W, .fld _ T, π, r, r', he, hπ =>
      View.ok_liftAct T (.symm π) (r'.sel a) _ (View.ok_repath Γ W _ (.sel π a) _ _ he hπ) hπ
  | .is W, .is T, π, r, r', he, hπ =>
      View.ok_liftAct T (.symm π) r' _ (View.ok_repath Γ W _ π r r' he hπ) hπ
  | .le _, .fld _ _, _, _, _, he, _ => he
  | .le _, .alias _, _, _, _, he, _ => he
  | .le _, .is _, _, _, _, he, _ => he
  | .fld _ _, .le _ _, _, _, _, he, _ => he
  | .fld _ _, .alias _, _, _, _, he, _ => he
  | .fld _ _, .is _, _, _, _, he, _ => he
  | .is _, .le _ _, _, _, _, he, _ => he
  | .is _, .fld _ _, _, _, _, he, _ => he
  | .is _, .alias _, _, _, _, he, _ => he
  | .alias, _, _, _, _, he, _ => by cases ‹Pr (s,x)› <;> exact he
end

/-! ### Applying forms to views -/

mutual
theorem Atom.ok_apply : ∀ (a : Atom s) (r : Path s) (W : View s), Atom.ok A a = true → View.ok A W = true →
    View.ok A (View.applyAtom a r W) = true
  | .eqv φ, r, W, ha, hW => View.ok_transport true φ [] r W ha hW
  | .pi e f, _, .fn v F, ha, hW => by
      simp only [View.applyAtom, View.ok, Form.ok_append, Bool.and_eq_true] at hW ⊢
      exact ⟨hW.1, hW.2, by simp only [Form.single, Form.ok, ha, Bool.and_self]⟩
  | .pi _ _, _, .obj _, _, hW => hW
  | .pi _ _, _, .inst _, _, hW => hW
  | .pi _ _, _, .none, _, hW => hW
  | .obj Es, r, .obj V, ha, hW => Entries.ok_apply Es r V ha hW
  | .obj _, _, .fn _ _, _, hW => hW
  | .obj _, _, .inst _, _, hW => hW
  | .obj _, _, .none, _, hW => hW
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, hW => hW
  | .pair F G, r, W, ha, hW => by
      simp only [Atom.ok, Bool.and_eq_true] at ha
      have h₁ := Form.ok_apply F r W ha.1 hW
      have h₂ := Form.ok_apply G r W ha.2 hW
      simp only [View.applyAtom]
      generalize View.applyForm F r W = W₁ at h₁ ⊢
      generalize View.applyForm G r W = W₂ at h₂ ⊢
      cases W₁ with
      | obj V =>
          cases W₂ with
          | obj V' => exact VEntries.ok_append V V' h₁ h₂
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
        exact VEntries.ok_get V hW e
      · rfl
  | .bnd _, _, .fn _ _, _, hW => hW
  | .bnd _, _, .inst _, _, hW => hW
  | .bnd _, _, .none, _, hW => hW
  | .into F, r, W, ha, hW => by
      simp only [View.applyAtom, View.ok, VEntries.ok, VEntry.ok, Bool.true_and]
      exact Form.ok_apply F r W ha hW
  | .seal _ _, _, _, _, hW => hW
  | .unseal _ _, _, .inst W, _, hW => hW
  | .unseal _ _, _, .obj _, _, _ => rfl
  | .unseal _ _, _, .fn _ _, _, _ => rfl
  | .unseal _ _, _, .none, _, _ => rfl
theorem Form.ok_apply : ∀ (F : Form s) (r : Path s) (W : View s), Form.ok A F = true → View.ok A W = true →
    View.ok A (View.applyForm F r W) = true
  | .nil, _, _, _, hW => hW
  | .cons a F, r, W, hF, hW => by
      simp only [Form.ok, Bool.and_eq_true] at hF
      exact Form.ok_apply F r _ hF.2 (Atom.ok_apply a r W hF.1 hW)
theorem Entries.ok_apply : ∀ (Es : Entries s) (r : Path s) (V : VEntries s), Entries.ok A Es = true →
    VEntries.ok A V = true → VEntries.ok A (Entries.apply Es r V) = true
  | .nil, _, _, _, _ => rfl
  | .cons Es e, r, V, hE, hV => by
      simp only [Entries.ok, Bool.and_eq_true] at hE
      simp only [Entries.apply, VEntries.ok, Bool.and_eq_true]
      exact ⟨Entries.ok_apply Es r V hE.1 hV, Entry.ok_apply e r V hE.2 hV⟩
theorem Entry.ok_apply : ∀ (e : Entry s) (r : Path s) (V : VEntries s), Entry.ok A e = true →
    VEntries.ok A V = true → VEntry.ok A (Entry.apply e r V) = true
  | .le pre _ post, _, V, he, hV => by
      simp only [Entry.ok, Bool.and_eq_true] at he
      simp only [Entry.apply]
      split
      · rename_i F e
        have hF := VEntries.ok_get V hV e
        simp only [VEntry.ok, Form.ok_append, Bool.and_eq_true] at hF ⊢
        exact ⟨SideF.ok_form pre he.1, hF, SideF.ok_form post he.2⟩
      · rfl
  | .fld _ sd, r, V, he, hV => by
      simp only [Entry.apply]
      split
      · rename_i a W e
        have hW := VEntries.ok_get V hV e
        simp only [VEntry.ok] at hW ⊢
        exact SideF.ok_apply sd _ W he hW
      · rfl
  | .alias _, _, _, _, _ => rfl
  | .is F, r, V, he, hV => Form.ok_apply F r (.obj V) he hV
theorem SideF.ok_apply : ∀ (sd : SideF s) (r : Path s) (W : View s), SideF.ok A sd = true → View.ok A W = true →
    View.ok A (SideF.apply sd r W) = true
  | .none, _, _, _, hW => hW
  | .some F, r, W, hs, hW => Form.ok_apply F r W hs hW
  | .bot, _, _, _, hW => hW
  | .top, _, _, _, _ => rfl
end

/-! ### Stored values, literal views, variable views -/

/-- What a store holds at `x`, read at the full signature: a literal's definitions with its self
admitting the keys of `x`, any other value as itself. -/
def Got.ok (A : Alloc s) (x : BVar s .var) : Value s → Bool
  | .obj _ ds => Defs.sealsOK (A.consO (A x)) ds
  | v => Value.sealsOK A v

theorem Key.rename_succ (k : Key s) : Key.rename k (Rename.succ (k := .var)) = Key.weaken k := rfl

theorem Key.weaken_rename_subst (k : Key s) (x : BVar s .var) :
    Key.rename (Key.weaken k : Key (s,x)) (Rename.subst x) = k := by
  obtain ⟨q, C⟩ := k
  simp only [Key.rename, Key.weaken]
  congr 1
  induction q with
  | var y => rfl
  | sel q a ih => exact congrArg (Path.sel · a) ih

/-- A literal read at `x` keeps its sites: the stored check at `B` gives the read check at `A.consO (A x)`,
when the keys `B` admits at the self are those `A` admits at `x`, and below it those of `A`. -/
theorem Defs.sealsOK_reread {A : Alloc s} {B : Alloc (s',x)} {ρ : Rename s' s} {x : BVar s .var} {ds : Defs (s',x)}
    (h : Defs.sealsOK B ds = true)
    (hB : ∀ y k, B y k = true → ∃ k₀ : Key s', k = k₀.weaken ∧
      (match y with
       | .here => A x (Key.rename k₀ ρ)
       | .there z => A (ρ.var z) (Key.rename k₀ ρ)) = true) :
    Defs.sealsOK (A.consO (A x)) (ds.rename ρ.lift) = true :=
  Defs.sealsOK_rename ds ρ.lift h (fun y C hs => by
    obtain ⟨k₀, rfl, hk⟩ := hB y C (Defs.sealsOK_site ds h hs)
    rw [Key.weaken_rename]
    cases y with
    | here => show (A.consO (A x)) .here _ = true; rw [Alloc.consO_here]; exact hk
    | there z => show (A.consO (A x)) (.there (ρ.var z)) _ = true; rw [Alloc.consO_there]; exact hk)

theorem Store.sealsOK_get : ∀ {s : Sig} {A : Alloc s} (σ : Store s) (x : BVar s .var), Store.sealsOK A σ = true →
    Got.ok A x (σ.get x) = true
  | _, A, .cons σ v, .here, h => by
      simp only [Store.sealsOK, Bool.and_eq_true] at h
      have hv := h.2
      cases v with
      | obj Tel ds =>
          show Defs.sealsOK (A.consO (A .here)) (ds.rename Rename.succ.lift) = true
          exact Defs.sealsOK_reread hv (fun y k hk => by
            obtain ⟨k₀, rfl⟩ := Alloc.consO_true hk
            refine ⟨k₀, rfl, ?_⟩
            cases y with
            | here => rw [Alloc.consO_here] at hk; exact hk
            | there z => rw [Alloc.consO_there] at hk; exact hk)
      | lam S t =>
          show Value.sealsOK A ((Value.lam S t).rename Rename.succ) = true
          exact Value.sealsOK_rename _ Rename.succ hv (fun x C hs => Value.sealsOK_site (ξ := A.tail) _ hv hs)
      | cast w e =>
          show Value.sealsOK A ((Value.cast w e).rename Rename.succ) = true
          exact Value.sealsOK_rename _ Rename.succ hv (fun x C hs => Value.sealsOK_site (ξ := A.tail) _ hv hs)
  | _, A, .cons σ v, .there y, h => by
      simp only [Store.sealsOK, Bool.and_eq_true] at h
      have ih := Store.sealsOK_get σ y h.1
      show Got.ok A (.there y) ((σ.get y).rename Rename.succ) = true
      cases e : σ.get y with
      | obj Tel ds =>
          rw [e] at ih
          show Defs.sealsOK (A.consO (A (.there y))) (ds.rename Rename.succ.lift) = true
          exact Defs.sealsOK_reread ih (fun y' k hk => by
            obtain ⟨k₀, rfl⟩ := Alloc.consO_true hk
            refine ⟨k₀, rfl, ?_⟩
            cases y' with
            | here => rw [Alloc.consO_here] at hk; exact hk
            | there z => rw [Alloc.consO_there] at hk; exact hk)
      | lam S t =>
          rw [e] at ih
          show Value.sealsOK A ((Value.lam S t).rename Rename.succ) = true
          exact Value.sealsOK_rename _ Rename.succ ih (fun x C hs => Value.sealsOK_site (ξ := A.tail) _ ih hs)
      | cast w e' =>
          rw [e] at ih
          show Value.sealsOK A ((Value.cast w e').rename Rename.succ) = true
          exact Value.sealsOK_rename _ Rename.succ ih (fun x C hs => Value.sealsOK_site (ξ := A.tail) _ ih hs)

mutual
theorem litView_ok : ∀ (l : Path s) (ds : Defs s), Defs.sealsOK A ds = true → VEntries.ok A (litView l ds) = true
  | _, .nil, _ => rfl
  | l, .typ ds _ _, h => by
      simp only [litView, VEntries.ok, VEntry.ok, Bool.and_eq_true]
      exact ⟨⟨litView_ok l ds h, rfl⟩, rfl⟩
  | l, .fld ds a rhs, h => by
      simp only [Defs.sealsOK, Bool.and_eq_true] at h
      simp only [litView, VEntries.ok, VEntry.ok, Bool.and_eq_true]
      exact ⟨litView_ok l ds h.1, rhsView_ok l a rhs h.2⟩
  | l, .cls ds _ _, h => by
      simp only [litView, VEntries.ok, VEntry.ok, Bool.and_eq_true]
      exact ⟨⟨litView_ok l ds h, rfl⟩, rfl⟩
theorem rhsView_ok : ∀ (l : Path s) (a : Label) (rhs : Rhs s), Rhs.sealsOK A rhs = true →
    View.ok A (rhsView l a rhs) = true
  | _, _, .path _, _ => rfl
  | _, _, .fn v, h => by
      simp only [rhsView, View.ok, Form.ok, Bool.and_true]
      exact h
  | l, a, .nest _ ds, h => litView_ok (l.sel a) ds h
end

theorem varView_ok {σ : Store s} (hσ : Store.sealsOK A σ = true) (x : BVar s .var) : View.ok A (varView σ x) = true := by
  have h := Store.sealsOK_get σ x hσ
  unfold varView
  split
  · rename_i S t e
    rw [e] at h
    simp only [View.ok, Form.ok, Bool.and_true]
    exact h
  · rename_i Tel ds e
    rw [e] at h
    simp only [View.ok]
    apply litView_ok
    exact Defs.sealsOK_rename ds (Rename.subst x) h (fun y C hs => by
      have h' := Defs.sealsOK_site ds h hs
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      rw [Key.weaken_rename_subst]
      cases y with
      | here => rw [Alloc.consO_here] at h'; exact h'
      | there z => rw [Alloc.consO_there] at h'; exact h')
  · rfl

/-! ### The normalizer and the path view -/

mutual
theorem Hnf.ok {σ : Store s} {Γ : Ctx s} (hσ : Store.sealsOK A σ = true) : ∀ {e : LeCo s} {S T : Ty s} {F : Form s},
    Hnf σ Γ e S T F → ∀ {h : Option (Path s)}, LeCo.sealsOK h A e = true → Form.ok A F = true
  | _, _, _, _, .refl, _, _ => rfl
  | _, _, _, _, .trans h₁ h₂, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      rw [Form.ok_append, Hnf.ok hσ h₁ he.1, Hnf.ok hσ h₂ he.2]; rfl
  | _, _, _, _, .top, _, _ => rfl
  | _, _, _, _, .bot, _, _ => rfl
  | _, _, _, _, .eqToLe _, _, he => by simp only [Form.single, Form.ok, Atom.ok, Bool.and_true]; exact he
  | _, _, _, _, .pi _ _, _, he => by simp only [Form.single, Form.ok, Atom.ok, Bool.and_true]; exact he
  | _, _, _, _, .obj hm, _, he => by
      simp only [Form.single, Form.ok, Atom.ok, Bool.and_true]
      exact HnfM.ok hσ hm he
  | _, _, _, _, .pair h₁ h₂, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      simp only [Form.single, Form.ok, Atom.ok, Bool.and_true, Bool.and_eq_true]
      exact ⟨Hnf.ok hσ h₁ he.1, Hnf.ok hσ h₂ he.2⟩
  | _, _, _, _, .bound _, _, _ => rfl
  | _, _, _, _, .intoBnd h₁, _, he => by
      simp only [Form.single, Form.ok, Atom.ok, Bool.and_true]
      exact Hnf.ok hσ h₁ he
  | _, _, _, _, .member (P := P) hP he' _ hV hg, _, he => by
      simp only [LeCo.sealsOK, Bool.and_eq_true] at he
      have hW := PV.ok hσ hP he.1
      have hF := Hnf.ok hσ he' he.2
      have hV' := Form.ok_apply _ P.path _ hF hW
      rw [hV] at hV'
      exact VEntries.ok_get _ hV' hg
  | _, _, _, _, .seal _, _, _ => rfl
theorem HnfM.ok {σ : Store s} {Γ : Ctx s} (hσ : Store.sealsOK A σ = true) : ∀ {src : Telescope (s,x)}
    {m : Morphism s} {Tel : Telescope (s,x)} {Es : Entries s}, HnfM σ Γ src m Tel Es →
    ∀ {h : Option (Path s)}, Morphism.sealsOK h A m = true → Entries.ok A Es = true
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .le h₁ _ h₂ h₃, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      simp only [Entries.ok, Entry.ok, Bool.and_eq_true]
      exact ⟨HnfM.ok hσ h₁ hm.1.1, HnfS.ok hσ h₂ hm.1.2, HnfS.ok hσ h₃ hm.2⟩
  | _, _, _, _, .fld h₁ _ h₂, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      simp only [Entries.ok, Entry.ok, Bool.and_eq_true]
      exact ⟨HnfM.ok hσ h₁ hm.1, HnfS.ok hσ h₂ hm.2⟩
  | _, _, _, _, .alias h₁ _, _, hm => by
      simp only [Entries.ok, Entry.ok, Bool.and_true]
      exact HnfM.ok hσ h₁ hm
  | _, _, _, _, .is h₁ h₂, _, hm => by
      simp only [Morphism.sealsOK, Bool.and_eq_true] at hm
      simp only [Entries.ok, Entry.ok, Bool.and_eq_true]
      exact ⟨HnfM.ok hσ h₁ hm.1, Hnf.ok hσ h₂ hm.2⟩
theorem HnfS.ok {σ : Store s} {Γ : Ctx s} (hσ : Store.sealsOK A σ = true) : ∀ {sd : Side s} {X Y : Ty (s,x)}
    {sf : SideF s}, HnfS σ Γ sd X Y sf → Side.sealsOK A sd = true → SideF.ok A sf = true
  | _, _, _, _, .none, _ => rfl
  | _, _, _, _, .some h₁, hs => Hnf.ok hσ h₁ (h := none) hs
  | _, _, _, _, .bot, _ => rfl
  | _, _, _, _, .top, _ => rfl
theorem PV.ok {σ : Store s} {Γ : Ctx s} (hσ : Store.sealsOK A σ = true) : ∀ {P : PathCo s} {T : Ty s} {W : View s},
    PV σ Γ P T W → PathCo.sealsOK A P = true → View.ok A W = true
  | _, _, _, .var _, _ => varView_ok hσ _
  | _, _, _, .sel hP _ hg, hok => VEntries.ok_get _ (PV.ok hσ hP hok) hg
  | _, _, _, .cast hP he, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact Form.ok_apply _ _ _ (Hnf.ok hσ he hok.2) (PV.ok hσ hP hok.1)
  | _, _, _, .alias hQ, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact View.ok_repath Γ _ _ _ _ _ (PV.ok hσ hQ hok.2) hok.1.2
  | _, _, _, .sngl, _ => rfl
  | _, _, _, .fldI hQ, hok => by
      simp only [View.ok, VEntries.ok, VEntry.ok, Bool.true_and]
      exact PV.ok hσ hQ hok
  | _, _, _, .unfold hP, hok => PV.ok hσ hP hok
  | _, _, _, .fold hP, hok => PV.ok hσ hP hok
  | _, _, _, .both hP hQ, hok => by
      simp only [PathCo.sealsOK, Bool.and_eq_true] at hok
      exact VEntries.ok_append _ _ (PV.ok hσ hP hok.1) (PV.ok hσ hQ hok.2)
end

theorem NormV.ok {σ : Store s} {Γ : Ctx s} {r : Path s} (hσ : Store.sealsOK A σ = true) :
    ∀ {v : Value s} {X : Ty s} {W : View s}, NormV σ Γ r v X W → Value.sealsOK A v = true → View.ok A W = true
  | _, _, _, .lam _, hv => by
      simp only [View.ok, Form.ok, Bool.and_true]
      exact hv
  | _, _, _, .cast hv' he, hv => by
      simp only [Value.sealsOK, Bool.and_eq_true] at hv
      exact Form.ok_apply _ _ _ (Hnf.ok hσ he (h := none) hv.2) (NormV.ok hσ hv' hv.1)

/-! ### The collapse of a function form -/

def Acc.ok (A : Alloc s) : Acc s → Bool
  | .start => true
  | .eqv χ => EqCo.sealsOK A χ
  | .pi d c => LeCo.sealsOK none A d && LeCo.sealsOK none (A.cons Lbl.none) c
  | .piEqv d c χ => LeCo.sealsOK none A d && LeCo.sealsOK none (A.cons Lbl.none) c && EqCo.sealsOK A χ

theorem Alloc.cons_weaken_ok {A : Alloc s} {b : Label → Bool} (x : BVar s .var) (C : Key s) (hx : A x C = true) :
    (A.cons b) (Rename.succ.var x) (Key.rename C Rename.succ) = true := by
  show (A.cons b) (.there x) (Key.weaken C) = true
  rw [Alloc.cons_there]; exact hx

/-- The codomain under a domain cast `z := cast z e↑`, the domain admitting no seal. -/
theorem LeCo.sealsOK_selfCast {c : LeCo (s,x)} {e : LeCo s} (hc : LeCo.sealsOK none (A.cons Lbl.none) c = true)
    (he : LeCo.sealsOK none A e = true) : LeCo.sealsOK none (A.cons Lbl.none) (c.subst (CoSubst.selfCast e)) = true :=
  LeCo.sealsOK_subst (h := none) c (CoSubst.selfCast e) hc
    (fun x => by
      cases x with
      | here =>
          show (true && LeCo.sealsOK (some (Path.var .here)) _ (e.rename Rename.succ)) = true
          simp only [Bool.true_and]
          exact LeCo.sealsOK_head _ _
            (LeCo.sealsOK_rename (h := none) e Rename.succ he
              (fun x C hs => Alloc.cons_weaken_ok x C (LeCo.sealsOK_site e he hs)))
      | there y => rfl)
    (fun x C hs => by
      rw [Key.subst_selfCast]
      have h' := LeCo.sealsOK_site c hc hs
      cases x with
      | here =>
          obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
          simp [Alloc.cons_here, Lbl.none] at h'
      | there y => exact ⟨.there y, rfl, h'⟩)

theorem EqCo.sealsOK_weaken {χ : EqCo s} (h : EqCo.sealsOK A χ = true) (b : Label → Bool) :
    EqCo.sealsOK (A.cons b) χ.weaken = true :=
  EqCo.sealsOK_rename χ Rename.succ h (fun x C hs => Alloc.cons_weaken_ok x C (EqCo.sealsOK_site χ h hs))

theorem pushDom_ok {χ : EqCo s} {e : LeCo s} (hχ : EqCo.sealsOK A χ = true) (he : LeCo.sealsOK none A e = true) :
    LeCo.sealsOK none A (pushDom χ e) = true := by
  simp only [pushDom, LeCo.sealsOK, EqCo.sealsOK, Bool.and_eq_true]
  exact ⟨he, hχ⟩

theorem pushCod_ok {χ : EqCo s} {f : LeCo (s,x)} (hχ : EqCo.sealsOK A χ = true)
    (hf : LeCo.sealsOK none (A.cons Lbl.none) f = true) : LeCo.sealsOK none (A.cons Lbl.none) (pushCod χ f) = true := by
  simp only [pushCod, LeCo.sealsOK, EqCo.sealsOK, Bool.and_eq_true]
  exact ⟨EqCo.sealsOK_weaken hχ _, hf⟩

theorem Acc.ok_step : ∀ (a : Acc s) (at' : Atom s) {a' : Acc s}, Acc.ok A a = true → Atom.ok A at' = true →
    a.step at' = some a' → Acc.ok A a' = true
  | .start, .eqv φ, _, _, hφ, h => by cases h; exact hφ
  | .eqv χ, .eqv φ, _, hχ, hφ, h => by
      cases h; simp only [Acc.ok, EqCo.sealsOK, Bool.and_eq_true]; exact ⟨hχ, hφ⟩
  | .pi d c, .eqv φ, _, ha, hφ, h => by
      cases h; simp only [Acc.ok, Bool.and_eq_true] at ha ⊢; exact ⟨ha, hφ⟩
  | .piEqv d c χ, .eqv φ, _, ha, hφ, h => by
      cases h; simp only [Acc.ok, EqCo.sealsOK, Bool.and_eq_true] at ha ⊢; exact ⟨ha.1, ha.2, hφ⟩
  | .start, .pi e f, _, _, hp, h => by cases h; exact hp
  | .eqv χ, .pi e f, _, hχ, hp, h => by
      cases h
      simp only [Atom.ok, Bool.and_eq_true] at hp
      simp only [Acc.ok, Bool.and_eq_true]
      exact ⟨pushDom_ok hχ hp.1, pushCod_ok hχ hp.2⟩
  | .pi d c, .pi e f, _, ha, hp, h => by
      cases h
      simp only [Atom.ok, Bool.and_eq_true] at hp
      simp only [Acc.ok, Bool.and_eq_true] at ha
      simp only [Acc.ok, LeCo.sealsOK, Bool.and_eq_true]
      exact ⟨⟨hp.1, ha.1⟩, LeCo.sealsOK_selfCast ha.2 hp.1, hp.2⟩
  | .piEqv d c χ, .pi e f, _, ha, hp, h => by
      cases h
      simp only [Atom.ok, Bool.and_eq_true] at hp
      simp only [Acc.ok, Bool.and_eq_true] at ha
      simp only [Acc.ok, LeCo.sealsOK, Bool.and_eq_true]
      exact ⟨⟨pushDom_ok ha.2 hp.1, ha.1.1⟩, LeCo.sealsOK_selfCast ha.1.2 (pushDom_ok ha.2 hp.1), pushCod_ok ha.2 hp.2⟩
  | .start, .obj _, _, _, _, h => by cases h
  | .start, .top, _, _, _, h => by cases h
  | .start, .bot, _, _, _, h => by cases h
  | .start, .pair _ _, _, _, _, h => by cases h
  | .start, .bnd _, _, _, _, h => by cases h
  | .start, .into _, _, _, _, h => by cases h
  | .start, .seal _ _, _, _, _, h => by cases h
  | .start, .unseal _ _, _, _, _, h => by cases h
  | .eqv _, .obj _, _, _, _, h => by cases h
  | .eqv _, .top, _, _, _, h => by cases h
  | .eqv _, .bot, _, _, _, h => by cases h
  | .eqv _, .pair _ _, _, _, _, h => by cases h
  | .eqv _, .bnd _, _, _, _, h => by cases h
  | .eqv _, .into _, _, _, _, h => by cases h
  | .eqv _, .seal _ _, _, _, _, h => by cases h
  | .eqv _, .unseal _ _, _, _, _, h => by cases h
  | .pi _ _, .obj _, _, _, _, h => by cases h
  | .pi _ _, .top, _, _, _, h => by cases h
  | .pi _ _, .bot, _, _, _, h => by cases h
  | .pi _ _, .pair _ _, _, _, _, h => by cases h
  | .pi _ _, .bnd _, _, _, _, h => by cases h
  | .pi _ _, .into _, _, _, _, h => by cases h
  | .pi _ _, .seal _ _, _, _, _, h => by cases h
  | .pi _ _, .unseal _ _, _, _, _, h => by cases h
  | .piEqv _ _ _, .obj _, _, _, _, h => by cases h
  | .piEqv _ _ _, .top, _, _, _, h => by cases h
  | .piEqv _ _ _, .bot, _, _, _, h => by cases h
  | .piEqv _ _ _, .pair _ _, _, _, _, h => by cases h
  | .piEqv _ _ _, .bnd _, _, _, _, h => by cases h
  | .piEqv _ _ _, .into _, _, _, _, h => by cases h
  | .piEqv _ _ _, .seal _ _, _, _, _, h => by cases h
  | .piEqv _ _ _, .unseal _ _, _, _, _, h => by cases h

theorem Acc.ok_run : ∀ (a : Acc s) (F : Form s) {a' : Acc s}, Acc.ok A a = true → Form.ok A F = true →
    a.run F = some a' → Acc.ok A a' = true
  | a, .nil, _, ha, _, h => by cases h; exact ha
  | a, .cons at' F, a', ha, hF, h => by
      simp only [Form.ok, Bool.and_eq_true] at hF
      simp only [Acc.run, Option.bind_eq_some_iff] at h
      obtain ⟨a₁, h₁, h₂⟩ := h
      exact Acc.ok_run a₁ F (Acc.ok_step a at' ha hF.1 h₁) hF.2 h₂

theorem Acc.ok_head : ∀ (a : Acc s), Acc.ok A a = true → AppHead.sealsOK A a.head = true
  | .start, _ => rfl
  | .eqv _, h => h
  | .pi _ _, h => h
  | .piEqv d c χ, h => by
      simp only [Acc.ok, Bool.and_eq_true] at h
      have hd : LeCo.sealsOK none A (.eqToLe (.symm (.dom χ))) = true := h.2
      simp only [Acc.head, AppHead.sealsOK, LeCo.sealsOK, EqCo.sealsOK, Bool.and_eq_true]
      exact ⟨⟨h.2, h.1.1⟩, LeCo.sealsOK_selfCast h.1.2 hd, EqCo.sealsOK_weaken h.2 _⟩

theorem collapse_ok {F : Form s} {h : AppHead s} (hF : Form.ok A F = true) (hc : collapse F = some h) :
    AppHead.sealsOK A h = true := by
  simp only [collapse, Option.map_eq_some_iff] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  exact Acc.ok_head a (Acc.ok_run .start F rfl hF ha)

end Views

/-- **The application view meets the hypothesis.**  So preservation holds of the machine
`Step appView` with no hypothesis left. -/
theorem appView_sealsOK : AppView.SealsOK appView := by
  intro s σ P S₀ t₀ h A hv hσ hP
  obtain ⟨Γ, S, T, v, F, X, W, F', _, _, hPV, hN, hA, hc⟩ := hv
  have hfn := PV.ok hσ hPV hP
  simp only [View.ok, Bool.and_eq_true] at hfn
  have hW := NormV.ok hσ hN hfn.1
  have h' := Form.ok_apply F P.path W hfn.2 hW
  rw [hA] at h'
  simp only [View.ok, Bool.and_eq_true] at h'
  exact ⟨h'.1, collapse_ok h'.2 hc⟩

end Nominal.FCn
