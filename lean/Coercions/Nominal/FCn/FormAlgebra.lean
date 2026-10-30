import Coercions.Nominal.FCn.FormTyping
import Coercions.Nominal.FCn.TypingSubst

/-!
# The algebra of typed forms and views (plan X, T.7 fixed by C0)

Composition of typed forms is concatenation (`FormT.append`, `FnFormT.append`).  `SoundEq.norm` is
the closed reading of type equality: one normal type.  A path equality moves a view at a hole
(`View.liftAct_typed`, `View.liftK_typed`), type equality evidence moves views at every position
(`SoundEq.transport`), and an alias step moves a view to the aliased path (`View.repath_typed`).
`FormT.apply` applies a typed form to a typed view.  `View.vals` says that a function view names a
value the store gave it.  The head of a typed function form is typed (`Acc.step_typed`,
`collapse_typed`).  There `eqv` meets `pi`, and only there, where both ends are syntactic.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.  The plan's `FormTyped.comp` and `FormTyped.apply`
are `FormT.append` and `FormT.apply`.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

variable {Γ : Ctx s} {γ : PDot.Runtime.Store s}

/-! ## Forms -/

theorem FormT.append : FormT Γ γ F S M → FormT Γ γ G M T → FormT Γ γ (F.append G) S T
  | .nil, hG => hG
  | .cons hA hF, hG => .cons hA (FormT.append hF hG)

theorem FormT.single (h : AtomT Γ γ A S T) : FormT Γ γ (.single A) S T := .cons h .nil

theorem FnFormT.append : FnFormT Γ γ F S M → FnFormT Γ γ G M T → FnFormT Γ γ (F.append G) S T
  | .nil, hG => hG
  | .cons hA hF, hG => .cons hA (FnFormT.append hF hG)

theorem FnFormT.single (h : FnAtomT Γ γ A S T) : FnFormT Γ γ (.single A) S T := .cons h .nil

theorem SoundEq.typed : SoundEq Γ γ φ S T → EqCo.HasType Γ φ S T
  | .refl => .refl
  | .symm h => .symm h.typed
  | .trans h₁ h₂ => .trans h₁.typed h₂.typed
  | .defP h => .defP h
  | .lift hπ _ => .lift hπ
  | .dom h => .dom h.typed
  | .cod h => .cod h.typed

/-- The closed reading of type equality: one normal type. -/
theorem SoundEq.norm : SoundEq Γ γ φ S T → Γ.norm S = Γ.norm T
  | .refl => rfl
  | .symm h => h.norm.symm
  | .trans h₁ h₂ => h₁.norm.trans h₂.norm
  | .defP h => Γ.norm_defAt h
  | .lift (T := T) _ hr => Γ.norm_substPath T hr.1
  | .dom h => by
      have e := h.norm
      rw [Γ.norm_pi, Γ.norm_pi] at e
      injection e with _ e₁ _
      exact Γ.norm_congr e₁
  | .cod (p := p) h => by
      have e := h.norm
      rw [Γ.norm_pi, Γ.norm_pi] at e
      injection e with _ _ e₂
      exact Γ.norm_cod e₂ p

/-! ## Readings -/

theorem PRead.refl (p : Path s) : PRead Γ γ p p := ⟨rfl, PDot.Runtime.Joinable.refl γ p⟩
theorem PRead.symm (h : PRead Γ γ p q) : PRead Γ γ q p := ⟨h.1.symm, h.2.symm⟩
theorem PRead.trans (h₁ : PRead Γ γ p q) (h₂ : PRead Γ γ q r) : PRead Γ γ p r := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
theorem PRead.sel (h : PRead Γ γ p q) (a : Label) : PRead Γ γ (p.sel a) (q.sel a) :=
  ⟨canon_sel_congr Γ h.1 a, h.2.sel a⟩

theorem PRead.subst {σ σ' : PathSubst s' s} (h : ∀ y, PRead Γ γ (σ.var y) (σ'.var y)) (X : Path s') :
    PRead Γ γ (X.subst σ) (X.subst σ') :=
  ⟨CFn.Cong.subst Γ.canon_cong (fun y => (h y).1) X, PDot.Runtime.Joinable.subst (fun y => (h y).2) X⟩

theorem PRead.one (h : PRead Γ γ p q) : ∀ y, PRead Γ γ ((PathSubst.one p).var y) ((PathSubst.one q).var y)
  | .here => h
  | .there _ => PRead.refl _

theorem PRead.substPath (h : PRead Γ γ p q) (X : Path (s,x)) : PRead Γ γ (X.substPath p) (X.substPath q) := by
  rw [← Path.subst_one, ← Path.subst_one]
  exact PRead.subst h.one X

theorem FieldOK.of_join {r r' : Path s} {a : Label} (h : FieldOK γ r a) (hj : PDot.Runtime.Joinable γ r' r) :
    FieldOK γ r' a := fun k hk hn => h k (PDot.Runtime.Joinable.star_val hk hn hj) hn

theorem RLam.of_join {r r' : Path s} {v : Value s} (h : RLam γ r v) (hj : PDot.Runtime.Joinable γ r' r) :
    RLam γ r' v := PDot.Runtime.Joinable.star_val h rfl hj.symm

theorem Live.sel {r : Path s} {a : Label} (h : Live γ (r.sel a)) : Live γ r ∧ FieldOK γ r a := h

/-! ## Substitution at two binders -/

theorem PathSubst.swap_eq (r p : Path s) :
    (PathSubst.one (r.weaken (k := .var))).comp (PathSubst.one p) =
      (PathSubst.one p).lift.comp (PathSubst.one r) := by
  apply PathSubst.funext'
  intro y
  cases y with
  | here =>
      show (r.weaken).subst (PathSubst.one p) = r
      rw [Path.subst_one, Path.weaken_substPath]
  | there y =>
      cases y with
      | here =>
          show p = (p.weaken).subst (PathSubst.one r)
          rw [Path.subst_one, Path.weaken_substPath]
      | there y => rfl

theorem Ty.swap (S : Ty ((s,x),x)) (r p : Path s) :
    (S.substPath r.weaken).substPath p = (S.subst (PathSubst.one p).lift).substPath r := by
  unfold Ty.substPath
  rw [Ty.subst_subst, Ty.subst_subst, PathSubst.swap_eq]

theorem Path.swap (q : Path ((s,x),x)) (r p : Path s) :
    (q.substPath r.weaken).substPath p = (q.subst (PathSubst.one p).lift).substPath r := by
  rw [← Path.subst_one, ← Path.subst_one, ← Path.subst_one, Paths.FCdot.Path.subst_subst,
    Paths.FCdot.Path.subst_subst, PathSubst.swap_eq]

/-! ## Moving a view along a path equality at a hole -/

section Lift
variable {π : PEq s} {p q : Path s}

theorem canon_one_congr (hr : PRead Γ γ p q) (P : Path (s,x)) :
    Γ.canon (P.subst (PathSubst.one p)) = Γ.canon (P.subst (PathSubst.one q)) :=
  CFn.Cong.subst Γ.canon_cong (fun y => (hr.one y).1) P

mutual
theorem View.liftAct_typed (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q) :
    ∀ (W : View s) (T : Ty (s,x)) (r : Path s), ViewT Γ γ r (Γ.res (T.substPath p)) W →
      ViewT Γ γ r (Γ.res (T.substPath q)) (View.liftAct T π r W)
  | .obj V, T, r, h => by
      obtain ⟨Tel', e, hV, hl⟩ := h.obj_inv
      cases T with
      | mu Tel =>
          have e' : Tel' = Tel.subst (PathSubst.one p).lift := by
            rw [show (Ty.mu Tel).substPath p = .mu (Tel.subst (PathSubst.one p).lift) from rfl, Γ.res_mu] at e
            cases e; rfl
          subst e'
          rw [show (Ty.mu Tel).substPath q = .mu (Tel.subst (PathSubst.one q).lift) from rfl, Γ.res_mu]
          exact .obj (VEntries.liftAct_typed hπ hr V Tel r hV) hl
      | sel P A =>
          have hc := canon_one_congr hr P
          rcases Γ.res_sel_cases hc A with ⟨_, _, h₁, _⟩ | heq
          · rw [show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at e
            cases e
          · simp only [View.liftAct]
            rw [show (Ty.sel P A).substPath q = .sel (P.subst (PathSubst.one q)) A from rfl, ← heq]
            exact h
      | bot =>
          rw [show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at e
          cases e
      | pi S U =>
          rw [show (Ty.pi S U).substPath p = .pi (S.substPath p) (U.subst (PathSubst.one p).lift) from rfl,
            Γ.res_pi] at e
          cases e
  | .fn v F, T, r, h => by
      obtain ⟨X, S, U, e, hv, hlam, hF, hl, hR⟩ := h.fn_inv
      cases T with
      | pi S' U' =>
          have hres : ∀ z, Γ.res ((Ty.pi S' U').substPath z) = (Ty.pi S' U').substPath z := fun z => Γ.res_pi _ _
          rw [hres] at e
          rw [hres]
          simp only [View.liftAct]
          have hA : FnAtomT Γ γ (.eqv (.lift (.pi S' U') π)) ((Ty.pi S' U').substPath p) ((Ty.pi S' U').substPath q) :=
            .eqv (.lift hπ hr)
          rw [← e] at hF
          have hF' := FnFormT.append hF (FnFormT.single hA)
          have e2 : (Ty.pi S' U').substPath q = .pi (S'.substPath q) (U'.subst (PathSubst.one q).lift) := rfl
          rw [e2] at hF' ⊢
          exact .fn hv hlam hF' hl hR
      | sel P A =>
          have hc := canon_one_congr hr P
          rcases Γ.res_sel_cases hc A with ⟨_, _, h₁, _⟩ | heq
          · rw [show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at e
            cases e
          · simp only [View.liftAct]
            rw [show (Ty.sel P A).substPath q = .sel (P.subst (PathSubst.one q)) A from rfl, ← heq]
            exact h
      | bot =>
          rw [show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at e
          cases e
      | mu Tel =>
          rw [show (Ty.mu Tel).substPath p = .mu (Tel.subst (PathSubst.one p).lift) from rfl, Γ.res_mu] at e
          cases e
  | .none, T, r, h => by
      obtain ⟨p', A', e, hn, hl⟩ := h.none_inv
      have hW : View.liftAct T π r .none = .none := by cases T <;> rfl
      rw [hW]
      cases T with
      | sel P A =>
          have hc := canon_one_congr hr P
          rcases Γ.res_sel_cases hc A with ⟨_, h₂, _, h₄⟩ | heq
          · rw [show (Ty.sel P A).substPath q = .sel (P.subst (PathSubst.one q)) A from rfl, h₄]
            exact .none h₂ hl
          · rw [show (Ty.sel P A).substPath q = .sel (P.subst (PathSubst.one q)) A from rfl, ← heq]
            exact h
      | bot =>
          rw [show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at e
          cases e
      | pi S U =>
          rw [show (Ty.pi S U).substPath p = .pi (S.substPath p) (U.subst (PathSubst.one p).lift) from rfl,
            Γ.res_pi] at e
          cases e
      | mu Tel =>
          rw [show (Ty.mu Tel).substPath p = .mu (Tel.subst (PathSubst.one p).lift) from rfl, Γ.res_mu] at e
          cases e
theorem VEntries.liftAct_typed (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q) :
    ∀ (V : VEntries s) (Tel : Telescope ((s,x),x)) (r : Path s),
      VEntriesT Γ γ r (Tel.subst (PathSubst.one p).lift) V →
      VEntriesT Γ γ r (Tel.subst (PathSubst.one q).lift) (VEntries.liftAct V Tel π r)
  | .nil, Tel, r, h => by
      cases Tel with
      | nil => exact .nil
      | cons Tel pr => cases h
  | .cons V e, Tel, r, h => by
      cases Tel with
      | nil => cases h
      | cons Tel pr =>
          cases h with
          | cons hV he =>
              exact .cons (VEntries.liftAct_typed hπ hr V Tel r hV) (VEntry.liftAct_typed hπ hr e pr r he)
theorem VEntry.liftAct_typed (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q) :
    ∀ (e : VEntry s) (pr : Pr ((s,x),x)) (r : Path s),
      VEntryT Γ γ r (pr.subst (PathSubst.one p).lift) e →
      VEntryT Γ γ r (pr.subst (PathSubst.one q).lift) (VEntry.liftAct e pr π r)
  | .le F, pr, r, h => by
      cases pr with
      | le S T =>
          cases h with
          | le hF =>
              simp only [VEntry.liftAct]
              apply VEntryT.le
              rw [← Ty.swap, ← Ty.swap] at hF ⊢
              refine FormT.append (FormT.single (.eqv (.lift hπ.symm hr.symm))) (FormT.append hF ?_)
              exact FormT.single (.eqv (.lift hπ hr))
      | fld _ _ => cases h
      | alias _ => cases h
      | is _ => cases h
  | .fld a W, pr, r, h => by
      cases pr with
      | fld a' T =>
          cases h with
          | fld hW =>
              simp only [VEntry.liftAct]
              apply VEntryT.fld
              rw [← Ty.swap] at hW ⊢
              exact View.liftAct_typed hπ hr W (T.substPath r.weaken) (r.sel a) hW
      | le _ _ => cases h
      | alias _ => cases h
      | is _ => cases h
  | .is W, pr, r, h => by
      cases pr with
      | is T =>
          cases h with
          | is hW =>
              simp only [VEntry.liftAct]
              apply VEntryT.is
              rw [← Ty.swap] at hW ⊢
              exact View.liftAct_typed hπ hr W (T.substPath r.weaken) r hW
      | le _ _ => cases h
      | fld _ _ => cases h
      | alias _ => cases h
  | .alias, pr, r, h => by
      cases pr with
      | alias q' =>
          cases h with
          | alias hq =>
              simp only [VEntry.liftAct]
              apply VEntryT.alias
              have e1 := Path.swap q' r p
              have e2 := Path.swap q' r q
              show PRead Γ γ r ((q'.subst (PathSubst.one q).lift).substPath r)
              have hq' : PRead Γ γ r ((q'.subst (PathSubst.one p).lift).substPath r) := hq
              rw [← e1] at hq'
              rw [← e2]
              exact hq'.trans (hr.substPath (q'.substPath r.weaken))
      | le _ _ => cases h
      | fld _ _ => cases h
      | is _ => cases h
end

theorem View.liftK_typed (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q) :
    ∀ (κ : List (Dir s)) (T : Ty (s,x)) (r : Path s) (R : Ty s) (W : View s),
      Γ.comp κ (T.substPath p) = some R → ViewT Γ γ r R W →
      ∃ R', Γ.comp κ (T.substPath q) = some R' ∧ ViewT Γ γ r R' (View.liftK T π κ r W)
  | [], T, r, R, W, hc, hW => by
      simp only [Ctx.comp] at hc
      cases hc
      exact ⟨_, rfl, View.liftAct_typed hπ hr W T r hW⟩
  | .dom :: κ, T, r, R, W, hc, hW => by
      cases T with
      | pi S U =>
          have e : ∀ z, Γ.res ((Ty.pi S U).substPath z) = .pi (S.substPath z) (U.subst (PathSubst.one z).lift) :=
            fun z => Γ.res_pi _ _
          simp only [Ctx.comp, e] at hc ⊢
          exact View.liftK_typed hπ hr κ S r R W hc hW
      | sel P A =>
          have hcp := canon_one_congr hr P
          rcases Γ.res_sel_cases hcp A with ⟨_, _, h₁, _⟩ | heq
          · simp only [Ctx.comp, show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at hc
            cases hc
          · refine ⟨R, ?_, hW⟩
            rw [Γ.comp_congr (show Γ.res ((Ty.sel P A).substPath q) = Γ.res ((Ty.sel P A).substPath p) from heq.symm)]
            exact hc
      | bot => simp only [Ctx.comp, show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at hc; cases hc
      | mu Tel =>
          simp only [Ctx.comp, show (Ty.mu Tel).substPath p = .mu (Tel.subst (PathSubst.one p).lift) from rfl,
            Γ.res_mu] at hc
          cases hc
  | .cod p' :: κ, T, r, R, W, hc, hW => by
      cases T with
      | pi S U =>
          have e : ∀ z, Γ.res ((Ty.pi S U).substPath z) = .pi (S.substPath z) (U.subst (PathSubst.one z).lift) :=
            fun z => Γ.res_pi _ _
          simp only [Ctx.comp, e] at hc ⊢
          rw [← Ty.swap] at hc ⊢
          exact View.liftK_typed hπ hr κ (U.substPath p'.weaken) r R W hc hW
      | sel P A =>
          have hcp := canon_one_congr hr P
          rcases Γ.res_sel_cases hcp A with ⟨_, _, h₁, _⟩ | heq
          · simp only [Ctx.comp, show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at hc
            cases hc
          · refine ⟨R, ?_, hW⟩
            rw [Γ.comp_congr (show Γ.res ((Ty.sel P A).substPath q) = Γ.res ((Ty.sel P A).substPath p) from heq.symm)]
            exact hc
      | bot => simp only [Ctx.comp, show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at hc; cases hc
      | mu Tel =>
          simp only [Ctx.comp, show (Ty.mu Tel).substPath p = .mu (Tel.subst (PathSubst.one p).lift) from rfl,
            Γ.res_mu] at hc
          cases hc

end Lift

/-! ## Type equality evidence moves views, at every position -/

def TransportOK (Γ : Ctx s) (γ : PDot.Runtime.Store s) (φ : EqCo s) (S T : Ty s) : Prop :=
  ∀ (κ : List (Dir s)) (r : Path s) (R : Ty s) (W : View s),
    (Γ.comp κ S = some R → ViewT Γ γ r R W →
      ∃ R', Γ.comp κ T = some R' ∧ ViewT Γ γ r R' (View.transport true φ κ r W)) ∧
    (Γ.comp κ T = some R → ViewT Γ γ r R W →
      ∃ R', Γ.comp κ S = some R' ∧ ViewT Γ γ r R' (View.transport false φ κ r W))

theorem SoundEq.transport : SoundEq Γ γ φ S T → TransportOK Γ γ φ S T
  | .refl => fun κ r R W => ⟨fun hc hW => ⟨R, hc, hW⟩, fun hc hW => ⟨R, hc, hW⟩⟩
  | .symm h => fun κ r R W => by
      have ih := h.transport κ r R W
      exact ⟨fun hc hW => ih.2 hc hW, fun hc hW => ih.1 hc hW⟩
  | .trans h₁ h₂ => fun κ r R W => by
      refine ⟨fun hc hW => ?_, fun hc hW => ?_⟩
      · obtain ⟨R₁, hc₁, hW₁⟩ := (h₁.transport κ r R W).1 hc hW
        obtain ⟨R₂, hc₂, hW₂⟩ := (h₂.transport κ r R₁ _).1 hc₁ hW₁
        exact ⟨R₂, hc₂, hW₂⟩
      · obtain ⟨R₁, hc₁, hW₁⟩ := (h₂.transport κ r R W).2 hc hW
        obtain ⟨R₂, hc₂, hW₂⟩ := (h₁.transport κ r R₁ _).2 hc₁ hW₁
        exact ⟨R₂, hc₂, hW₂⟩
  | .defP h => fun κ r R W => by
      have e := Γ.comp_congr (Γ.res_defAt h) κ
      exact ⟨fun hc hW => ⟨R, e ▸ hc, hW⟩, fun hc hW => ⟨R, e.symm ▸ hc, hW⟩⟩
  | .lift (T := T) hπ hr => fun κ r R W =>
      ⟨fun hc hW => View.liftK_typed hπ hr κ T r R W hc hW,
       fun hc hW => View.liftK_typed hπ.symm hr.symm κ T r R W hc hW⟩
  | .dom (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) h => fun κ r R W => by
      have e₁ : Γ.comp (.dom :: κ) (.pi S₁ T₁) = Γ.comp κ S₁ := by simp only [Ctx.comp, Γ.res_pi]
      have e₂ : Γ.comp (.dom :: κ) (.pi S₂ T₂) = Γ.comp κ S₂ := by simp only [Ctx.comp, Γ.res_pi]
      have ih := h.transport (.dom :: κ) r R W
      refine ⟨fun hc hW => ?_, fun hc hW => ?_⟩
      · obtain ⟨R', hc', hW'⟩ := ih.1 (e₁ ▸ hc) hW
        exact ⟨R', e₂ ▸ hc', hW'⟩
      · obtain ⟨R', hc', hW'⟩ := ih.2 (e₂ ▸ hc) hW
        exact ⟨R', e₁ ▸ hc', hW'⟩
  | .cod (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (p := p) h => fun κ r R W => by
      have e₁ : Γ.comp (.cod p :: κ) (.pi S₁ T₁) = Γ.comp κ (T₁.substPath p) := by simp only [Ctx.comp, Γ.res_pi]
      have e₂ : Γ.comp (.cod p :: κ) (.pi S₂ T₂) = Γ.comp κ (T₂.substPath p) := by simp only [Ctx.comp, Γ.res_pi]
      have ih := h.transport (.cod p :: κ) r R W
      refine ⟨fun hc hW => ?_, fun hc hW => ?_⟩
      · obtain ⟨R', hc', hW'⟩ := ih.1 (e₁ ▸ hc) hW
        exact ⟨R', e₂ ▸ hc', hW'⟩
      · obtain ⟨R', hc', hW'⟩ := ih.2 (e₂ ▸ hc) hW
        exact ⟨R', e₁ ▸ hc', hW'⟩

/-- An `eqv` atom applied to a view at the resolution of its left type. -/
theorem SoundEq.apply (h : SoundEq Γ γ φ S T) (r : Path s) (W : View s) (hW : ViewT Γ γ r (Γ.res S) W) :
    ViewT Γ γ r (Γ.res T) (View.transport true φ [] r W) := by
  obtain ⟨R', hc, hW'⟩ := (h.transport [] r (Γ.res S) W).1 rfl hW
  simp only [Ctx.comp] at hc
  cases hc
  exact hW'

/-! ## Moving a view to an aliased path -/

mutual
theorem View.repath_typed : ∀ (W : View s) (T : Ty s) (π : PEq s) (r r' : Path s),
    PEq.HasType Γ π r' r → PRead Γ γ r' r → Live γ r' → ViewT Γ γ r (Γ.res T) W →
    ViewT Γ γ r' (Γ.res T) (View.repath Γ W T π r r')
  | .obj V, T, π, r, r', hπ, hr, hl, h => by
      obtain ⟨Tel, e, hV, _⟩ := h.obj_inv
      simp only [View.repath, e]
      exact .obj (VEntries.repath_typed V Tel π r r' hπ hr hl hV) hl
  | .fn v F, T, π, r, r', hπ, hr, hl, h => by
      obtain ⟨X, S, U, e, hv, hlam, hF, _, hR⟩ := h.fn_inv
      simp only [View.repath]
      rw [e]
      exact .fn hv hlam hF hl (hR.of_join hr.2)
  | .none, T, π, r, r', hπ, hr, hl, h => by
      obtain ⟨p, A, e, hn, _⟩ := h.none_inv
      simp only [View.repath]
      rw [e]
      exact .none hn hl
theorem VEntries.repath_typed : ∀ (V : VEntries s) (Tel : Telescope (s,x)) (π : PEq s) (r r' : Path s),
    PEq.HasType Γ π r' r → PRead Γ γ r' r → Live γ r' → VEntriesT Γ γ r Tel V →
    VEntriesT Γ γ r' Tel (VEntries.repath Γ V Tel π r r')
  | .nil, Tel, _, _, _, _, _, _, h => by
      cases h
      exact .nil
  | .cons V e, Tel, π, r, r', hπ, hr, hl, h => by
      cases Tel with
      | nil => cases h
      | cons Tel pr =>
          cases h with
          | cons hV he =>
              exact .cons (VEntries.repath_typed V Tel π r r' hπ hr hl hV) (VEntry.repath_typed e pr π r r' hπ hr hl he)
theorem VEntry.repath_typed : ∀ (e : VEntry s) (pr : Pr (s,x)) (π : PEq s) (r r' : Path s),
    PEq.HasType Γ π r' r → PRead Γ γ r' r → Live γ r' → VEntryT Γ γ r pr e →
    VEntryT Γ γ r' pr (VEntry.repath Γ e pr π r r')
  | .le F, pr, π, r, r', hπ, hr, hl, h => by
      cases pr with
      | le S T =>
          cases h with
          | le hF =>
              simp only [VEntry.repath]
              apply VEntryT.le
              refine FormT.append (FormT.single (.eqv (.lift hπ hr))) (FormT.append hF ?_)
              exact FormT.single (.eqv (.lift hπ.symm hr.symm))
      | fld _ _ => cases h
      | alias _ => cases h
      | is _ => cases h
  | .fld a W, pr, π, r, r', hπ, hr, hl, h => by
      cases pr with
      | fld a' T =>
          cases h with
          | fld hW =>
              simp only [VEntry.repath]
              apply VEntryT.fld
              have hla := hW.live
              have hl' : Live γ (r'.sel a) := ⟨hl, hla.2.of_join hr.2⟩
              have h1 := View.repath_typed W (T.substPath r) (.sel π a) (r.sel a) (r'.sel a) (.sel hπ) (hr.sel a) hl' hW
              exact View.liftAct_typed hπ.symm hr.symm _ T (r'.sel a) h1
      | le _ _ => cases h
      | alias _ => cases h
      | is _ => cases h
  | .is W, pr, π, r, r', hπ, hr, hl, h => by
      cases pr with
      | is T =>
          cases h with
          | is hW =>
              simp only [VEntry.repath]
              apply VEntryT.is
              have h1 := View.repath_typed W (T.substPath r) π r r' hπ hr hl hW
              exact View.liftAct_typed hπ.symm hr.symm _ T r' h1
      | le _ _ => cases h
      | fld _ _ => cases h
      | alias _ => cases h
  | .alias, pr, π, r, r', hπ, hr, hl, h => by
      cases pr with
      | alias q =>
          cases h with
          | alias hq =>
              simp only [VEntry.repath]
              apply VEntryT.alias
              exact hr.trans (hq.trans (hr.symm.substPath q))
      | le _ _ => cases h
      | fld _ _ => cases h
      | is _ => cases h
end

/-! ## Applying a form to a view -/

theorem SideT.form_typed (r : Path s) : SideT Γ γ sd X Y → FormT Γ γ sd.form (X.substPath r) (Y.substPath r)
  | .none => .nil
  | .some (X := X₀) (Y := Y₀) hF => by
      simp only [SideF.form]
      rw [Ty.weaken_substPath, Ty.weaken_substPath]
      exact hF
  | .bot => FormT.single .bot
  | .top => FormT.single .top

theorem Ty.top_substPath (r : Path s) : (Ty.top : Ty (s,x)).substPath r = .top := rfl

theorem VEntriesT.append : ∀ {Tel' : Telescope (s,x)} {V' : VEntries s}, VEntriesT Γ γ r Tel V →
    VEntriesT Γ γ r Tel' V' → VEntriesT Γ γ r (Tel ++ Tel') (V.append V')
  | _, _, hV, .nil => hV
  | _, _, hV, .cons hV' he => .cons (VEntriesT.append hV hV') he

mutual
theorem AtomT.apply : AtomT Γ γ A S T → ∀ (r : Path s) (W : View s), ViewT Γ γ r (Γ.res S) W →
    ViewT Γ γ r (Γ.res T) (View.applyAtom A r W)
  | .eqv h, r, W, hW => by
      simp only [View.applyAtom]
      exact h.apply r W hW
  | .pi (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) he hf, r, W, hW => by
      rw [Γ.res_pi] at hW ⊢
      obtain ⟨v, F, X, rfl, hv, hlam, hF, hR⟩ := hW.pi_inv
      simp only [View.applyAtom]
      exact .fn hv hlam (FnFormT.append hF (FnFormT.single (.pi he hf))) hW.live hR
  | .obj hEs, r, W, hW => by
      rw [Γ.res_mu] at hW ⊢
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      simp only [View.applyAtom]
      exact .obj (EntriesT.apply hEs r V hV hW.live) hW.live
  | .top, r, W, hW => by
      have : View.applyAtom (.top : Atom s) r W = .obj .nil := by cases W <;> rfl
      rw [this, Γ.res_mu]
      exact .obj .nil hW.live
  | .bot, r, W, hW => by
      rw [Γ.res_bot] at hW
      exact absurd hW ViewT.not_bot
  | .pair (F := F) (G := G) hF hG, r, W, hW => by
      have h1 := FormT.apply hF r W hW
      have h2 := FormT.apply hG r W hW
      rw [Γ.res_mu] at h1 h2 ⊢
      obtain ⟨V, e1, hV⟩ := h1.mu_inv
      obtain ⟨V', e2, hV'⟩ := h2.mu_inv
      simp only [View.applyAtom, e1, e2]
      exact .obj (VEntriesT.append hV hV') hW.live
  | .bnd (T := T) hi, r, W, hW => by
      rw [Γ.res_mu] at hW
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      obtain ⟨e, hg, he⟩ := hV.get hi
      cases he with
      | is hW' =>
          simp only [View.applyAtom, hg]
          rw [Ty.weaken_substPath] at hW'
          exact hW'
  | .into (T := T) hF, r, W, hW => by
      simp only [View.applyAtom]
      rw [Γ.res_mu]
      have h1 := FormT.apply hF r W hW
      refine .obj (.cons .nil (.is ?_)) hW.live
      rw [Ty.weaken_substPath]
      exact h1
theorem FormT.apply : FormT Γ γ F S T → ∀ (r : Path s) (W : View s), ViewT Γ γ r (Γ.res S) W →
    ViewT Γ γ r (Γ.res T) (View.applyForm F r W)
  | .nil, _, W, hW => hW
  | .cons hA hF, r, W, hW => FormT.apply hF r _ (AtomT.apply hA r W hW)
theorem EntriesT.apply : EntriesT Γ γ src Es Tel → ∀ (r : Path s) (V : VEntries s), VEntriesT Γ γ r src V →
    Live γ r → VEntriesT Γ γ r Tel (Entries.apply Es r V)
  | .nil, r, V, hV, _ => .nil
  | .le (pre := pre) (post := post) hEs hj hpre hpost, r, V, hV, hl => by
      obtain ⟨e, hg, he⟩ := hV.get hj
      cases he with
      | le hF =>
          simp only [Entries.apply, Entry.apply, hg]
          exact .cons (EntriesT.apply hEs r V hV hl)
            (.le (FormT.append (hpre.form_typed r) (FormT.append hF (hpost.form_typed r))))
  | .fld hEs hj hsd, r, V, hV, hl => by
      obtain ⟨e, hg, he⟩ := hV.get hj
      cases he with
      | fld hW =>
          simp only [Entries.apply, Entry.apply, hg]
          exact .cons (EntriesT.apply hEs r V hV hl) (.fld (SideT.apply hsd r _ _ hW))
  | .alias hEs hj, r, V, hV, hl => by
      obtain ⟨e, hg, he⟩ := hV.get hj
      cases he with
      | alias hq =>
          simp only [Entries.apply, Entry.apply]
          exact .cons (EntriesT.apply hEs r V hV hl) (.alias hq)
  | .is (T := T) hEs hF, r, V, hV, hl => by
      simp only [Entries.apply, Entry.apply]
      refine .cons (EntriesT.apply hEs r V hV hl) (.is ?_)
      rw [Ty.weaken_substPath]
      have h0 : ViewT Γ γ r (Γ.res (.mu src)) (.obj V) := by rw [Γ.res_mu]; exact .obj hV hl
      exact FormT.apply hF r _ h0
theorem SideT.apply : SideT Γ γ sd X Y → ∀ (r t : Path s) (W : View s), ViewT Γ γ t (Γ.res (X.substPath r)) W →
    ViewT Γ γ t (Γ.res (Y.substPath r)) (SideF.apply sd t W)
  | .none, r, t, W, hW => hW
  | .some (X := X₀) (Y := Y₀) hF, r, t, W, hW => by
      simp only [SideF.apply]
      rw [Ty.weaken_substPath] at hW ⊢
      exact FormT.apply hF t W hW
  | .bot, r, t, W, hW => by
      rw [show (Ty.bot : Ty (s,x)).substPath r = .bot from rfl, Γ.res_bot] at hW
      exact absurd hW ViewT.not_bot
  | .top, r, t, W, hW => by
      simp only [SideF.apply]
      rw [Ty.top_substPath, Γ.res_mu]
      exact .obj .nil hW.live
end

end Nominal.FCn

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Every function view in a view names one value

The view operations never invent a stored value: a function view in the output carries a value of
a function view of the input.  So the closure a view names is the one the store gave it. -/

mutual
def View.vals : View s → Value s → Prop
  | .obj V, v₀ => VEntries.vals V v₀
  | .fn v _, v₀ => v = v₀
  | .none, _ => True
def VEntries.vals : VEntries s → Value s → Prop
  | .nil, _ => True
  | .cons V e, v₀ => VEntries.vals V v₀ ∧ VEntry.vals e v₀
def VEntry.vals : VEntry s → Value s → Prop
  | .le _, _ => True
  | .fld _ W, v₀ => View.vals W v₀
  | .alias, _ => True
  | .is W, v₀ => View.vals W v₀
end

theorem VEntries.get_vals : ∀ (V : VEntries s) (i : Nat) (e : VEntry s) (v₀ : Value s),
    VEntries.vals V v₀ → V.get i = some e → VEntry.vals e v₀
  | .nil, _, _, _, _, h => by cases h
  | .cons V e', i, e, v₀, hv, h => by
      simp only [VEntries.get] at h
      split at h
      · cases h; exact hv.2
      · exact VEntries.get_vals V i e v₀ hv.1 h

theorem VEntries.append_vals : ∀ (V V' : VEntries s) (v₀ : Value s),
    VEntries.vals V v₀ → VEntries.vals V' v₀ → VEntries.vals (V.append V') v₀
  | _, .nil, _, h, _ => h
  | V, .cons V' _, v₀, h, h' => ⟨VEntries.append_vals V V' v₀ h h'.1, h'.2⟩

mutual
theorem View.liftAct_vals : ∀ (W : View s) (T : Ty (s,x)) (π : PEq s) (r : Path s) (v₀ : Value s),
    View.vals W v₀ → View.vals (View.liftAct T π r W) v₀
  | .obj V, T, π, r, v₀, h => by
      cases T with
      | mu Tel => exact VEntries.liftAct_vals V Tel π r v₀ h
      | sel _ _ => exact h
      | bot => exact h
      | pi _ _ => exact h
  | .fn v F, T, π, r, v₀, h => by
      cases T with
      | pi _ _ => exact h
      | sel _ _ => exact h
      | bot => exact h
      | mu _ => exact h
  | .none, T, _, _, _, h => by cases T <;> exact h
theorem VEntries.liftAct_vals : ∀ (V : VEntries s) (Tel : Telescope ((s,x),x)) (π : PEq s) (r : Path s) (v₀ : Value s),
    VEntries.vals V v₀ → VEntries.vals (VEntries.liftAct V Tel π r) v₀
  | .nil, Tel, _, _, _, h => by cases Tel <;> exact h
  | .cons V e, .nil, _, _, _, h => h
  | .cons V e, .cons Tel pr, π, r, v₀, h =>
      ⟨VEntries.liftAct_vals V Tel π r v₀ h.1, VEntry.liftAct_vals e pr π r v₀ h.2⟩
theorem VEntry.liftAct_vals : ∀ (e : VEntry s) (pr : Pr ((s,x),x)) (π : PEq s) (r : Path s) (v₀ : Value s),
    VEntry.vals e v₀ → VEntry.vals (VEntry.liftAct e pr π r) v₀
  | .le _, pr, _, _, _, h => by cases pr <;> trivial
  | .fld a W, pr, π, r, v₀, h => by
      cases pr with
      | fld _ T => exact View.liftAct_vals W _ π (r.sel a) v₀ h
      | le _ _ => exact h
      | alias _ => exact h
      | is _ => exact h
  | .alias, pr, _, _, _, h => by cases pr <;> trivial
  | .is W, pr, π, r, v₀, h => by
      cases pr with
      | is T => exact View.liftAct_vals W _ π r v₀ h
      | le _ _ => exact h
      | alias _ => exact h
      | fld _ _ => exact h
end

theorem View.liftK_vals : ∀ (κ : List (Dir s)) (T : Ty (s,x)) (π : PEq s) (r : Path s) (W : View s) (v₀ : Value s),
    View.vals W v₀ → View.vals (View.liftK T π κ r W) v₀
  | [], T, π, r, W, v₀, h => View.liftAct_vals W T π r v₀ h
  | .dom :: κ, T, π, r, W, v₀, h => by
      cases T with
      | pi S _ => exact View.liftK_vals κ S π r W v₀ h
      | sel _ _ => exact h
      | bot => exact h
      | mu _ => exact h
  | .cod p :: κ, T, π, r, W, v₀, h => by
      cases T with
      | pi _ U => exact View.liftK_vals κ _ π r W v₀ h
      | sel _ _ => exact h
      | bot => exact h
      | mu _ => exact h

theorem View.transport_vals : ∀ (b : Bool) (φ : EqCo s) (κ : List (Dir s)) (r : Path s) (W : View s) (v₀ : Value s),
    View.vals W v₀ → View.vals (View.transport b φ κ r W) v₀
  | _, .refl _, _, _, _, _, h => h
  | b, .symm φ, κ, r, W, v₀, h => View.transport_vals (!b) φ κ r W v₀ h
  | true, .trans φ ψ, κ, r, W, v₀, h =>
      View.transport_vals true ψ κ r _ v₀ (View.transport_vals true φ κ r W v₀ h)
  | false, .trans φ ψ, κ, r, W, v₀, h =>
      View.transport_vals false φ κ r _ v₀ (View.transport_vals false ψ κ r W v₀ h)
  | _, .defP _ _, _, _, _, _, h => h
  | true, .lift T π, κ, r, W, v₀, h => View.liftK_vals κ T π r W v₀ h
  | false, .lift T _, κ, r, W, v₀, h => View.liftK_vals κ T _ r W v₀ h
  | b, .dom φ, _, r, W, v₀, h => View.transport_vals b φ _ r W v₀ h
  | b, .cod φ _, _, r, W, v₀, h => View.transport_vals b φ _ r W v₀ h

mutual
theorem View.applyAtom_vals : ∀ (A : Atom s) (r : Path s) (W : View s) (v₀ : Value s),
    View.vals W v₀ → View.vals (View.applyAtom A r W) v₀
  | .eqv φ, r, W, v₀, h => View.transport_vals true φ [] r W v₀ h
  | .pi e f, r, W, v₀, h => by
      cases W with
      | fn v F => exact h
      | obj _ => exact h
      | none => exact h
  | .obj Es, r, W, v₀, h => by
      cases W with
      | obj V => exact Entries.apply_vals Es r V v₀ h
      | fn _ _ => exact h
      | none => exact h
  | .top, r, W, v₀, h => by cases W <;> trivial
  | .bot, r, W, v₀, h => by cases W <;> exact h
  | .pair F G, r, W, v₀, h => by
      have h1 := View.applyForm_vals F r W v₀ h
      have h2 := View.applyForm_vals G r W v₀ h
      simp only [View.applyAtom]
      cases e1 : View.applyForm F r W with
      | obj V =>
          cases e2 : View.applyForm G r W with
          | obj V' => rw [e1] at h1; rw [e2] at h2; exact VEntries.append_vals V V' v₀ h1 h2
          | fn _ _ => rw [e1] at h1; exact h1
          | none => rw [e1] at h1; exact h1
      | fn _ _ => rw [e1] at h1; exact h1
      | none => rw [e1] at h1; exact h1
  | .bnd i, r, W, v₀, h => by
      cases W with
      | obj V =>
          simp only [View.applyAtom]
          split
          · rename_i W' hg
            exact VEntries.get_vals V i (.is W') v₀ h hg
          · trivial
      | fn _ _ => exact h
      | none => exact h
  | .into F, r, W, v₀, h => ⟨trivial, View.applyForm_vals F r W v₀ h⟩
theorem View.applyForm_vals : ∀ (F : Form s) (r : Path s) (W : View s) (v₀ : Value s),
    View.vals W v₀ → View.vals (View.applyForm F r W) v₀
  | .nil, _, _, _, h => h
  | .cons A F, r, W, v₀, h => View.applyForm_vals F r _ v₀ (View.applyAtom_vals A r W v₀ h)
theorem Entries.apply_vals : ∀ (Es : Entries s) (r : Path s) (V : VEntries s) (v₀ : Value s),
    VEntries.vals V v₀ → VEntries.vals (Entries.apply Es r V) v₀
  | .nil, _, _, _, _ => trivial
  | .cons Es e, r, V, v₀, h => ⟨Entries.apply_vals Es r V v₀ h, Entry.apply_vals e r V v₀ h⟩
theorem Entry.apply_vals : ∀ (e : Entry s) (r : Path s) (V : VEntries s) (v₀ : Value s),
    VEntries.vals V v₀ → VEntry.vals (Entry.apply e r V) v₀
  | .le pre j post, r, V, v₀, h => by
      simp only [Entry.apply]
      split <;> trivial
  | .fld j sd, r, V, v₀, h => by
      simp only [Entry.apply]
      split
      · rename_i a W hg
        exact SideF.apply_vals sd (r.sel a) W v₀ (VEntries.get_vals V j (.fld a W) v₀ h hg)
      · trivial
  | .alias _, _, _, _, _ => trivial
  | .is F, r, V, v₀, h => View.applyForm_vals F r (.obj V) v₀ h
theorem SideF.apply_vals : ∀ (sd : SideF s) (r : Path s) (W : View s) (v₀ : Value s),
    View.vals W v₀ → View.vals (SideF.apply sd r W) v₀
  | .none, _, _, _, h => h
  | .some F, r, W, v₀, h => View.applyForm_vals F r W v₀ h
  | .bot, _, _, _, h => h
  | .top, _, _, _, _ => trivial
end

theorem Ty.rename_succ_lift_substPath_here (T : Ty (s,x)) :
    (T.rename (Rename.succ (k := .var)).lift).substPath (.var .here) = T := by
  rw [Ty.substPath, PathSubst.one_var, Ty.subst_ofRename, Ty.rename_rename, Rename.succ_lift_comp_subst_here,
    Ty.rename_id]

theorem cod_weaken_typed {Γ : Ctx s} {χ : EqCo s} {S₁ S₂ S : Ty s} {T₁ T₂ : Ty (s,x)}
    (h : EqCo.HasType Γ χ (.pi S₁ T₁) (.pi S₂ T₂)) :
    EqCo.HasType (Γ.cons (.opaque S)) (.cod χ.weaken (.var .here)) T₁ T₂ := by
  have h1 := EqCo.HasType.rename (Rename.Typed.succ Γ (.opaque S)) h
  have h2 := EqCo.HasType.cod (p := .var .here) h1
  rw [Ty.rename_succ_lift_substPath_here, Ty.rename_succ_lift_substPath_here] at h2
  exact h2

theorem selfCast_typed {Γ : Ctx s} {E : LeCo s} {S S' : Ty s} {c : LeCo (s,x)} {T₀ T : Ty (s,x)}
    (hE : LeCo.HasType Γ E S' S) (hc : LeCo.HasType (Γ.cons (.opaque S)) c T₀ T) :
    LeCo.HasType (Γ.cons (.opaque S')) (c.subst (CoSubst.selfCast E)) T₀ T := by
  have h := LeCo.HasType.subst (CoSubst.Typed.selfCast hE (.opaque S') rfl) hc
  rw [CoSubst.selfCast_paths, Ty.subst_ofRename, Ty.subst_ofRename, Ty.rename_id, Ty.rename_id] at h
  exact h

theorem LeCo.HasType.pi_inv_of_eq : ∀ {Γ : Ctx s} {e' : LeCo s} {A B : Ty s}, LeCo.HasType Γ e' A B →
    ∀ (e : LeCo s) (f : LeCo (s,x)), e' = .pi e f →
      ∃ S₁ T₁ S₂ T₂, A = .pi S₁ T₁ ∧ B = .pi S₂ T₂ ∧ LeCo.HasType Γ e S₂ S₁ ∧ LeCo.HasType (Γ.cons (.opaque S₂)) f T₁ T₂
  | _, _, _, _, .pi he hf, _, _, h => by cases h; exact ⟨_, _, _, _, rfl, rfl, he, hf⟩
  | _, _, _, _, .refl, _, _, h => nomatch h
  | _, _, _, _, .trans _ _, _, _, h => nomatch h
  | _, _, _, _, .top, _, _, h => nomatch h
  | _, _, _, _, .bot, _, _, h => nomatch h
  | _, _, _, _, .eqToLe _, _, _, h => nomatch h
  | _, _, _, _, .obj _, _, _, h => nomatch h
  | _, _, _, _, .pair _ _, _, _, h => nomatch h
  | _, _, _, _, .bound _, _, _, h => nomatch h
  | _, _, _, _, .intoBnd _, _, _, h => nomatch h
  | _, _, _, _, .member _ _ _, _, _, h => nomatch h

theorem Acc.step_typed {Γ : Ctx s} {γ : PDot.Runtime.Store s} {S₀ : Ty s} {T₀ : Ty (s,x)} :
    ∀ {a : Acc s} {X Y : Ty s} {A : Atom s}, AccT Γ S₀ T₀ a X → FnAtomT Γ γ A X Y →
      ∃ a', a.step A = some a' ∧ AccT Γ S₀ T₀ a' Y
  | _, _, _, _, .start, .eqv h => ⟨_, rfl, .eqv h.typed⟩
  | _, _, _, _, .eqv hχ, .eqv h => ⟨_, rfl, .eqv (.trans hχ h.typed)⟩
  | _, _, _, _, .pi hd hc, .eqv h => ⟨_, rfl, .piEqv hd hc h.typed⟩
  | _, _, _, _, .piEqv hd hc hχ, .eqv h => ⟨_, rfl, .piEqv hd hc (.trans hχ h.typed)⟩
  | _, _, _, _, .start, .pi he hf => ⟨_, rfl, .pi he hf⟩
  | _, _, _, _, .eqv hχ, .pi he hf =>
      ⟨_, rfl, .pi (.trans he (.eqToLe (.symm (.dom hχ)))) (.trans (.eqToLe (cod_weaken_typed hχ)) hf)⟩
  | _, _, _, _, .pi hd hc, .pi he hf => ⟨_, rfl, .pi (.trans he hd) (.trans (selfCast_typed he hc) hf)⟩
  | _, _, _, _, .piEqv hd hc hχ, .pi he hf =>
      have hE := LeCo.HasType.trans he (.eqToLe (.symm (.dom hχ)))
      ⟨_, rfl, .pi (.trans hE hd) (.trans (selfCast_typed hE hc) (.trans (.eqToLe (cod_weaken_typed hχ)) hf))⟩

theorem Acc.run_typed {Γ : Ctx s} {γ : PDot.Runtime.Store s} {S₀ : Ty s} {T₀ : Ty (s,x)} :
    ∀ {a : Acc s} {X Y : Ty s} {F : Form s}, AccT Γ S₀ T₀ a X → FnFormT Γ γ F X Y →
      ∃ a', a.run F = some a' ∧ AccT Γ S₀ T₀ a' Y
  | _, _, _, _, ha, .nil => ⟨_, rfl, ha⟩
  | _, _, _, _, ha, .cons hA hF => by
      obtain ⟨a', e, ha'⟩ := Acc.step_typed ha hA
      obtain ⟨a'', e', ha''⟩ := Acc.run_typed ha' hF
      exact ⟨a'', by simp only [Acc.run, e, Option.bind_some, e'], ha''⟩

theorem Acc.head_typed {Γ : Ctx s} {S₀ S : Ty s} {T₀ T : Ty (s,x)} {a : Acc s} (h : AccT Γ S₀ T₀ a (.pi S T)) :
    HeadTyped Γ a.head S₀ T₀ S T := by
  cases h with
  | start => exact ⟨rfl, rfl⟩
  | eqv hχ => exact hχ
  | pi hd hc => exact ⟨hd, hc⟩
  | piEqv hd hc hχ =>
      have hE := LeCo.HasType.eqToLe (EqCo.HasType.symm (EqCo.HasType.dom hχ))
      exact ⟨.trans hE hd, .trans (selfCast_typed hE hc) (.eqToLe (cod_weaken_typed hχ))⟩

theorem collapse_typed {Γ : Ctx s} {γ : PDot.Runtime.Store s} {S₀ S : Ty s} {T₀ T : Ty (s,x)} {F : Form s}
    (h : FnFormT Γ γ F (.pi S₀ T₀) (.pi S T)) : ∃ hd, collapse F = some hd ∧ HeadTyped Γ hd S₀ T₀ S T := by
  obtain ⟨a, e, ha⟩ := Acc.run_typed (AccT.start (Γ := Γ) (S₀ := S₀) (T₀ := T₀)) h
  exact ⟨a.head, by simp only [collapse, e, Option.map_some], Acc.head_typed ha⟩

end Nominal.FCn

