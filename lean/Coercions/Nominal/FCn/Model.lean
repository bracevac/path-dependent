import Coercions.Nominal.FCn.Typing
import Coercions.Nominal.Source.Model

/-!
# Path models of a fixed context

A tool for the negative examples (decision D11 of the groups file).  A model of a context `Γ`
reads every type as a set of paths `sem T p`, path equality as a relation `peq`, type equality as
a relation `teq`, and marks the paths it reaches.  It asks one closure property per rule of the
evidence block whose conclusion is in `Γ`.  `μ(w : Tel)` holds at a reachable path `p` when every
proposition of `Tel` holds at `p`, read by `semPrOf` with the self at `p`.

The six soundness theorems then read the six evidence judgments of `Γ` in the model: a path
typing as membership, a path equality as `peq`, an inclusion as inclusion, a type equality as
`teq`, a morphism as preservation of the propositions at a reachable path, and a side as inclusion
under the self.  `LE-Pi` is the one rule with a premise in another context, and the field `pi`
closes it, since no path is in a function type.  So the soundness proof is one structural
recursion on the evidence block at the fixed `Γ`, as X0's (`PDot/Source/Model.lean`).

A path that the model does not reach has no typing in `Γ` (`Model.reach_path`).
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

def semPrOf (sem : Ty s → Path s → Prop) (peq : Path s → Path s → Prop) : Pr (s,x) → Path s → Prop
  | .le S T, p => ∀ r, sem (S.substPath p) r → sem (T.substPath p) r      -- S⟨p⟩ ⊆ T⟨p⟩
  | .fld a T, p => sem (T.substPath p) (p.sel a)                         -- p.a ∈ T⟨p⟩
  | .alias q, p => peq p (q.substPath p)                                 -- p related to q⟨p⟩
  | .is T, p => sem (T.substPath p) p                                    -- p ∈ T⟨p⟩

structure Model (Γ : Ctx s) where
  sem : Ty s → Path s → Prop
  reach : Path s → Prop
  peq : Path s → Path s → Prop
  teq : Ty s → Ty s → Prop
  -- PA-Var: x ∈ Γ.ty x
  var : ∀ x, sem (Γ.ty x) (.var x)
  -- members are reachable, and reachability is closed under prefixes (PA-FldI)
  reach_sem : ∀ T p, sem T p → reach p
  reach_sel : ∀ p a, reach (p.sel a) → reach p
  -- μ(w : Tel) holds at a reachable p when every proposition of Tel holds at p
  mu : ∀ Tel p, sem (.mu Tel) p ↔ reach p ∧ ∀ i pr, Tel.At i pr → semPrOf sem peq pr p
  -- no path is in ⊥ or in a function type, so LE-Pi reads nothing of its premise in Γ, z : opaque S₂
  bot : ∀ p, ¬ sem .bot p
  pi : ∀ S T p, ¬ sem (.pi S T) p
  -- PA-Alias: p ∈ S, p related to q, q ∈ T  ⟹  p ∈ T
  alias : ∀ S T p q, sem S p → peq p q → sem T q → sem T p
  peq_refl : ∀ p, peq p p
  peq_symm : ∀ p q, peq p q → peq q p
  peq_trans : ∀ p q r, peq p q → peq q r → peq p r
  peq_sel : ∀ p q a, peq p q → peq (p.sel a) (q.sel a)
  teq_sem : ∀ S T, teq S T → ∀ p, sem S p → sem T p
  teq_refl : ∀ T, teq T T
  teq_symm : ∀ S T, teq S T → teq T S
  teq_trans : ∀ S M T, teq S M → teq M T → teq S T
  teq_defP : ∀ p A W, Γ.defAt p A = some W → teq (.sel p A) W
  teq_lift : ∀ (T : Ty (s,x)) p q, peq p q → teq (T.substPath p) (T.substPath q)
  teq_dom : ∀ S₁ T₁ S₂ T₂, teq (.pi S₁ T₁) (.pi S₂ T₂) → teq S₁ S₂
  teq_cod : ∀ S₁ T₁ S₂ T₂ p, teq (.pi S₁ T₁) (.pi S₂ T₂) → teq (T₁.substPath p) (T₂.substPath p)

theorem Model.top (M : Model Γ) : ∀ p, M.reach p → M.sem .top p :=
  fun _ hp => (M.mu .nil _).2 ⟨hp, fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim⟩

/-- `semPrOf` reads a proposition only through its instance at the path. -/
theorem semPrOf_congr {sem : Ty s → Path s → Prop} {peq : Path s → Path s → Prop} {p : Path s} :
    ∀ {pr₁ pr₂ : Pr (s,x)}, pr₁.substPath p = pr₂.substPath p →
      (semPrOf sem peq pr₁ p ↔ semPrOf sem peq pr₂ p)
  | .le S₁ T₁, .le S₂ T₂, h => by
      have h' : S₁.substPath p = S₂.substPath p ∧ T₁.substPath p = T₂.substPath p := Pr.le.inj h
      show (∀ r, sem (S₁.substPath p) r → sem (T₁.substPath p) r) ↔
        (∀ r, sem (S₂.substPath p) r → sem (T₂.substPath p) r)
      rw [h'.1, h'.2]
  | .fld a₁ T₁, .fld a₂ T₂, h => by
      have h' : a₁ = a₂ ∧ T₁.substPath p = T₂.substPath p := Pr.fld.inj h
      show sem (T₁.substPath p) (p.sel a₁) ↔ sem (T₂.substPath p) (p.sel a₂)
      rw [h'.1, h'.2]
  | .alias q₁, .alias q₂, h => by
      have h' : q₁.subst (PathSubst.one p) = q₂.subst (PathSubst.one p) := Pr.alias.inj h
      rw [Path.subst_one, Path.subst_one] at h'
      show peq p (q₁.substPath p) ↔ peq p (q₂.substPath p)
      rw [h']
  | .is T₁, .is T₂, h => by
      have h' : T₁.substPath p = T₂.substPath p := Pr.is.inj h
      show sem (T₁.substPath p) p ↔ sem (T₂.substPath p) p
      rw [h']
  | .le _ _, .fld _ _, h => nomatch h
  | .le _ _, .alias _, h => nomatch h
  | .le _ _, .is _, h => nomatch h
  | .fld _ _, .le _ _, h => nomatch h
  | .fld _ _, .alias _, h => nomatch h
  | .fld _ _, .is _, h => nomatch h
  | .alias _, .le _ _, h => nomatch h
  | .alias _, .fld _ _, h => nomatch h
  | .alias _, .is _, h => nomatch h
  | .is _, .le _ _, h => nomatch h
  | .is _, .fld _ _, h => nomatch h
  | .is _, .alias _, h => nomatch h

/-- A proposition opened at `p` and weakened back under the self reads at `p` as the original. -/
theorem semPrOf_weaken_substPath {sem : Ty s → Path s → Prop} {peq : Path s → Path s → Prop}
    (pr : Pr (s,x)) (p : Path s) :
    semPrOf sem peq (pr.substPath p).weaken p ↔ semPrOf sem peq pr p :=
  semPrOf_congr (Pr.weaken_substPath (pr.substPath p) p)

mutual
theorem Model.sound_peq {Γ : Ctx s} (M : Model Γ) : ∀ {π : PEq s} {p q : Path s}, PEq.HasType Γ π p q → M.peq p q
  | _, _, _, .refl => M.peq_refl _
  | _, _, _, .symm h => M.peq_symm _ _ (Model.sound_peq M h)
  | _, _, _, .trans h₁ h₂ => M.peq_trans _ _ _ (Model.sound_peq M h₁) (Model.sound_peq M h₂)
  | _, _, _, .sel h => M.peq_sel _ _ _ (Model.sound_peq M h)
  | _, _, _, .member hP he hi => by
      have h₀ := Model.sound_path M hP
      exact ((M.mu _ _).1 (Model.sound_le M he _ h₀)).2 _ _ hi
theorem Model.sound_path {Γ : Ctx s} (M : Model Γ) : ∀ {P : PathCo s} {T : Ty s}, PathCo.HasType Γ P T → M.sem T P.path
  | _, _, .var h => h ▸ M.var _
  | _, _, .sel hP hi => by
      have h := Model.sound_path M hP
      exact ((M.mu _ _).1 h).2 _ _ hi
  | _, _, .cast hP he => by
      have h := Model.sound_path M hP
      exact Model.sound_le M he _ h
  | _, _, .alias h₀ hπ hQ => by
      have h₁ := Model.sound_path M h₀
      have h₂ := Model.sound_path M hQ
      exact M.alias _ _ _ _ h₁ (Model.sound_peq M hπ) h₂
  | _, _, .sngl (q := q) hP hπ => by
      have h := Model.sound_path M hP
      refine (M.mu _ _).2 ⟨M.reach_sem _ _ h, fun i pr hi => ?_⟩
      obtain ⟨-, rfl⟩ := Telescope.At.single_iff.1 hi
      show M.peq _ ((q.weaken (k := .var)).substPath _)
      rw [Path.weaken_substPath]
      exact Model.sound_peq M hπ
  | _, _, .fldI (p := p) (a := a) (T := T) hQ e => by
      have h := Model.sound_path M hQ
      rw [e] at h
      refine (M.mu _ _).2 ⟨M.reach_sel _ _ (M.reach_sem _ _ h), fun i pr hi => ?_⟩
      obtain ⟨-, rfl⟩ := Telescope.At.single_iff.1 hi
      show M.sem (T.weaken.substPath p) (p.sel a)
      rw [Ty.weaken_substPath]
      exact h
  | _, _, .unfold (P := P) hP => by
      have h := (M.mu _ _).1 (Model.sound_path M hP)
      refine (M.mu _ _).2 ⟨h.1, fun i pr hi => ?_⟩
      obtain ⟨pr₁, hi₁, rfl⟩ := Telescope.At.rename_iff.1 hi
      obtain ⟨pr₀, hi₀, rfl⟩ := Telescope.At.subst_iff.1 hi₁
      exact (semPrOf_weaken_substPath pr₀ P.path).2 (h.2 _ _ hi₀)
  | _, _, .fold (P := P) hP => by
      have h := (M.mu _ _).1 (Model.sound_path M hP)
      refine (M.mu _ _).2 ⟨h.1, fun i pr hi => ?_⟩
      exact (semPrOf_weaken_substPath pr P.path).1 (h.2 _ _ ((hi.subst (PathSubst.one P.path)).rename Rename.succ))
  | _, _, .both hP hQ e => by
      have h := (M.mu _ _).1 (Model.sound_path M hP)
      have h' := (M.mu _ _).1 (Model.sound_path M hQ)
      rw [e] at h'
      refine (M.mu _ _).2 ⟨h.1, fun i pr hi => ?_⟩
      rcases Telescope.At.append_iff.1 hi with hi | ⟨j, -, hj⟩
      · exact h.2 _ _ hi
      · exact h'.2 _ _ hj
theorem Model.sound_le {Γ : Ctx s} (M : Model Γ) : ∀ {e : LeCo s} {S T : Ty s}, LeCo.HasType Γ e S T → ∀ p, M.sem S p → M.sem T p
  | _, _, _, .refl, _, h => h
  | _, _, _, .trans h₁ h₂, p, h => Model.sound_le M h₂ p (Model.sound_le M h₁ p h)
  | _, _, _, .top, p, h => M.top p (M.reach_sem _ _ h)
  | _, _, _, .bot, p, h => absurd h (M.bot p)
  | _, _, _, .eqToLe hφ, p, h => M.teq_sem _ _ (Model.sound_eq M hφ) p h
  | _, _, _, .pi _ _, p, h => absurd h (M.pi _ _ p)
  | _, _, _, .obj hm, p, h => by
      have h' := (M.mu _ _).1 h
      exact (M.mu _ _).2 ⟨h'.1, Model.sound_mor M hm p h'.1 h'.2⟩
  | _, _, _, .pair he hf, p, h => by
      have h₁ := (M.mu _ _).1 (Model.sound_le M he p h)
      have h₂ := (M.mu _ _).1 (Model.sound_le M hf p h)
      refine (M.mu _ _).2 ⟨h₁.1, fun i pr hi => ?_⟩
      rcases Telescope.At.append_iff.1 hi with hi | ⟨j, -, hj⟩
      · exact h₁.2 _ _ hi
      · exact h₂.2 _ _ hj
  | _, _, _, .bound (T := T) hi, p, h => by
      have h' : M.sem (T.weaken.substPath p) p := ((M.mu _ _).1 h).2 _ _ hi
      rw [Ty.weaken_substPath] at h'
      exact h'
  | _, _, _, .intoBnd (T := T) he, p, h => by
      have h' := Model.sound_le M he p h
      refine (M.mu _ _).2 ⟨M.reach_sem _ _ h, fun i pr hi => ?_⟩
      obtain ⟨-, rfl⟩ := Telescope.At.single_iff.1 hi
      show M.sem (T.weaken.substPath p) p
      rw [Ty.weaken_substPath]
      exact h'
  | _, _, _, .member hP he hi, p, h => by
      have h₀ := Model.sound_path M hP
      exact ((M.mu _ _).1 (Model.sound_le M he _ h₀)).2 _ _ hi p h
theorem Model.sound_eq {Γ : Ctx s} (M : Model Γ) : ∀ {φ : EqCo s} {S T : Ty s}, EqCo.HasType Γ φ S T → M.teq S T
  | _, _, _, .refl => M.teq_refl _
  | _, _, _, .symm h => M.teq_symm _ _ (Model.sound_eq M h)
  | _, _, _, .trans h₁ h₂ => M.teq_trans _ _ _ (Model.sound_eq M h₁) (Model.sound_eq M h₂)
  | _, _, _, .defP h => M.teq_defP _ _ _ h
  | _, _, _, .lift hπ => M.teq_lift _ _ _ (Model.sound_peq M hπ)
  | _, _, _, .dom h => M.teq_dom _ _ _ _ (Model.sound_eq M h)
  | _, _, _, .cod h => M.teq_cod _ _ _ _ _ (Model.sound_eq M h)
theorem Model.sound_mor {Γ : Ctx s} (M : Model Γ) : ∀ {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}, Morphism.HasType Γ src m Tel → ∀ p, M.reach p → (∀ i pr, src.At i pr → semPrOf M.sem M.peq pr p) → ∀ i pr, Tel.At i pr → semPrOf M.sem M.peq pr p
  | _, _, _, .nil, _, _, _, _, _, hi => (Telescope.At.nil_of_eq hi rfl).elim
  | _, _, _, .le hm hj hpre hpost, p, hr, hs, i, pr, hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨-, rfl⟩ | hi
      · intro r h
        exact Model.sound_side M hpost p r (hs _ _ hj r (Model.sound_side M hpre p r h))
      · exact Model.sound_mor M hm p hr hs i pr hi
  | _, _, _, .fld hm hj hsd, p, hr, hs, i, pr, hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨-, rfl⟩ | hi
      · exact Model.sound_side M hsd p _ (hs _ _ hj)
      · exact Model.sound_mor M hm p hr hs i pr hi
  | _, _, _, .alias hm hj, p, hr, hs, i, pr, hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨-, rfl⟩ | hi
      · exact hs _ _ hj
      · exact Model.sound_mor M hm p hr hs i pr hi
  | _, _, _, .is (T := T) hm he, p, hr, hs, i, pr, hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨-, rfl⟩ | hi
      · show M.sem (T.weaken.substPath p) p
        rw [Ty.weaken_substPath]
        exact Model.sound_le M he p ((M.mu _ _).2 ⟨hr, hs⟩)
      · exact Model.sound_mor M hm p hr hs i pr hi
theorem Model.sound_side {Γ : Ctx s} (M : Model Γ) : ∀ {sd : Side s} {X Y : Ty (s,x)}, Side.HasType Γ sd X Y → ∀ p r, M.sem (X.substPath p) r → M.sem (Y.substPath p) r
  | _, _, _, .none, _, _, h => h
  | _, _, _, .some he, p, r, h => by
      rw [Ty.weaken_substPath] at h ⊢
      exact Model.sound_le M he r h
  | _, _, _, .bot, _, r, h => absurd h (M.bot r)
  | _, _, _, .top, _, r, h => M.top r (M.reach_sem _ _ h)
end

/-- A typed path is reached by every model of its context. -/
theorem Model.reach_path {Γ : Ctx s} (M : Model Γ) {P : PathCo s} {T : Ty s} (h : PathCo.HasType Γ P T) : M.reach P.path :=
  M.reach_sem _ _ (M.sound_path h)

end Nominal.FCn
