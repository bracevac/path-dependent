import Coercions.Oopsla16.Structural

/-!
# The substitution algebra

Identity, composition, and the fusion laws, for the one simultaneous
substitution of `Structural`.  Because renaming the local scope, renaming the
store scope, weakening and single-binder substitution are all instances of
`Subst`, these are one family of laws rather than the three the reference
needs — `dot.v:400-2093` spends about 170 lines on `subst_open`, `subst_open3`,
`subst_open4`, `subst_open5`, `subst_open_commute*` and `splice_open_permute*`,
which are the same content stated once per pair of operations.

Everything here is proved by structural recursion mirroring the definitions,
which is this development's idiom (`FCdot/RenameLemmas.lean`).
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

namespace Subst

/-- The identity substitution. -/
def id {σ s : Sig} : Subst σ s σ s where
  conc := fun l => l
  abs := .abs

/-- Composition. -/
def comp {σ1 σ2 σ3 s1 s2 s3 : Sig} (θ : Subst σ1 s1 σ2 s2)
    (φ : Subst σ2 s2 σ3 s3) : Subst σ1 s1 σ3 s3 where
  conc := fun l => φ.conc (θ.conc l)
  abs := fun y => (θ.abs y).subst φ

/-- Two substitutions agreeing on both zones are equal. -/
theorem ext {σ1 σ2 s1 s2 : Sig} {θ φ : Subst σ1 s1 σ2 s2}
    (hc : ∀ l, θ.conc l = φ.conc l) (ha : ∀ y, θ.abs y = φ.abs y) : θ = φ := by
  cases θ; cases φ
  simp only [Subst.mk.injEq]
  exact ⟨funext hc, funext ha⟩

@[simp] theorem id_conc {σ s : Sig} (l : BVar σ .var) :
    (id (σ := σ) (s := s)).conc l = l := rfl
@[simp] theorem id_abs {σ s : Sig} (y : BVar s .var) :
    (id (σ := σ) (s := s)).abs y = .abs y := rfl
@[simp] theorem comp_conc {σ1 σ2 σ3 s1 s2 s3 : Sig} (θ : Subst σ1 s1 σ2 s2)
    (φ : Subst σ2 s2 σ3 s3) (l : BVar σ1 .var) :
    (θ.comp φ).conc l = φ.conc (θ.conc l) := rfl
@[simp] theorem comp_abs {σ1 σ2 σ3 s1 s2 s3 : Sig} (θ : Subst σ1 s1 σ2 s2)
    (φ : Subst σ2 s2 σ3 s3) (y : BVar s1 .var) :
    (θ.comp φ).abs y = (θ.abs y).subst φ := rfl

/-- Weakening a variable commutes with a lifted substitution. -/
@[simp] theorem weaken_subst_lift {σ1 σ2 s1 s2 : Sig} (v : Vr σ1 s1)
    (φ : Subst σ1 s1 σ2 s2) : (v.weaken).subst φ.lift = (v.subst φ).weaken := by
  cases v <;> rfl

@[simp] theorem lift_id {σ s : Sig} : (id (σ := σ) (s := s)).lift = id := by
  apply ext <;> intro y
  · rfl
  · cases y <;> rfl

theorem lift_comp {σ1 σ2 σ3 s1 s2 s3 : Sig} (θ : Subst σ1 s1 σ2 s2)
    (φ : Subst σ2 s2 σ3 s3) : (θ.comp φ).lift = θ.lift.comp φ.lift := by
  apply ext <;> intro y
  · rfl
  · cases y with
    | here => rfl
    | there y => exact (weaken_subst_lift (θ.abs y) φ).symm

end Subst

/-! ## The identity law -/

@[simp] theorem Vr.subst_id {σ s : Sig} (v : Vr σ s) : v.subst Subst.id = v := by
  cases v <;> rfl

@[simp] theorem Ty.subst_id : {σ s : Sig} → (T : Ty σ s) → T.subst Subst.id = T
  | _, _, .TBot => rfl
  | _, _, .TTop => rfl
  | _, _, .TFun l T1 T2 => by
      simp only [Ty.subst, Subst.lift_id, Ty.subst_id T1, Ty.subst_id T2]
  | _, _, .TTyp l T1 T2 => by simp only [Ty.subst, Ty.subst_id T1, Ty.subst_id T2]
  | _, _, .TSel p l => by simp only [Ty.subst, Vr.subst_id]
  | _, _, .TBind T => by simp only [Ty.subst, Subst.lift_id, Ty.subst_id T]
  | _, _, .TAnd T1 T2 => by simp only [Ty.subst, Ty.subst_id T1, Ty.subst_id T2]
  | _, _, .TOr T1 T2 => by simp only [Ty.subst, Ty.subst_id T1, Ty.subst_id T2]

mutual

@[simp] theorem Tm.subst_id : {σ s : Sig} → (t : Tm σ s) → t.subst Subst.id = t
  | _, _, .tvar v => by simp only [Tm.subst, Vr.subst_id]
  | _, _, .tobj ds => by simp only [Tm.subst, Subst.lift_id, Dms.subst_id ds]
  | _, _, .tapp t1 l t2 => by simp only [Tm.subst, Tm.subst_id t1, Tm.subst_id t2]

@[simp] theorem Dm.subst_id : {σ s : Sig} → (d : Dm σ s) → d.subst Subst.id = d
  | _, _, .dty T => by simp only [Dm.subst, Ty.subst_id]
  | _, _, .dfun OT1 OT2 t => by
      cases OT1 <;> cases OT2 <;>
        simp only [Dm.subst, Subst.lift_id, Option.map, Ty.subst_id, Tm.subst_id t]

@[simp] theorem Dms.subst_id : {σ s : Sig} → (ds : Dms σ s) → ds.subst Subst.id = ds
  | _, _, .dnil => rfl
  | _, _, .dcons d ds => by simp only [Dms.subst, Dm.subst_id d, Dms.subst_id ds]

end

/-! ## The fusion law -/

@[simp] theorem Vr.subst_comp {σ1 σ2 σ3 s1 s2 s3 : Sig} (v : Vr σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) (φ : Subst σ2 s2 σ3 s3) :
    (v.subst θ).subst φ = v.subst (θ.comp φ) := by
  cases v <;> rfl

@[simp] theorem Ty.subst_comp : {σ1 σ2 σ3 s1 s2 s3 : Sig} → (T : Ty σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (φ : Subst σ2 s2 σ3 s3) →
    (T.subst θ).subst φ = T.subst (θ.comp φ)
  | _, _, _, _, _, _, .TBot, _, _ => rfl
  | _, _, _, _, _, _, .TTop, _, _ => rfl
  | _, _, _, _, _, _, .TFun l T1 T2, θ, φ => by
      simp only [Ty.subst, Subst.lift_comp, Ty.subst_comp T1, Ty.subst_comp T2]
  | _, _, _, _, _, _, .TTyp l T1 T2, θ, φ => by
      simp only [Ty.subst, Ty.subst_comp T1, Ty.subst_comp T2]
  | _, _, _, _, _, _, .TSel p l, θ, φ => by simp only [Ty.subst, Vr.subst_comp]
  | _, _, _, _, _, _, .TBind T, θ, φ => by
      simp only [Ty.subst, Subst.lift_comp, Ty.subst_comp T]
  | _, _, _, _, _, _, .TAnd T1 T2, θ, φ => by
      simp only [Ty.subst, Ty.subst_comp T1, Ty.subst_comp T2]
  | _, _, _, _, _, _, .TOr T1 T2, θ, φ => by
      simp only [Ty.subst, Ty.subst_comp T1, Ty.subst_comp T2]

mutual

@[simp] theorem Tm.subst_comp : {σ1 σ2 σ3 s1 s2 s3 : Sig} → (t : Tm σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (φ : Subst σ2 s2 σ3 s3) →
    (t.subst θ).subst φ = t.subst (θ.comp φ)
  | _, _, _, _, _, _, .tvar v, θ, φ => by simp only [Tm.subst, Vr.subst_comp]
  | _, _, _, _, _, _, .tobj ds, θ, φ => by
      simp only [Tm.subst, Subst.lift_comp, Dms.subst_comp ds]
  | _, _, _, _, _, _, .tapp t1 l t2, θ, φ => by
      simp only [Tm.subst, Tm.subst_comp t1, Tm.subst_comp t2]

@[simp] theorem Dm.subst_comp : {σ1 σ2 σ3 s1 s2 s3 : Sig} → (d : Dm σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (φ : Subst σ2 s2 σ3 s3) →
    (d.subst θ).subst φ = d.subst (θ.comp φ)
  | _, _, _, _, _, _, .dty T, θ, φ => by simp only [Dm.subst, Ty.subst_comp]
  | _, _, _, _, _, _, .dfun OT1 OT2 t, θ, φ => by
      cases OT1 <;> cases OT2 <;>
        simp only [Dm.subst, Subst.lift_comp, Option.map, Ty.subst_comp,
          Tm.subst_comp t]

@[simp] theorem Dms.subst_comp : {σ1 σ2 σ3 s1 s2 s3 : Sig} → (ds : Dms σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (φ : Subst σ2 s2 σ3 s3) →
    (ds.subst θ).subst φ = ds.subst (θ.comp φ)
  | _, _, _, _, _, _, .dnil, _, _ => rfl
  | _, _, _, _, _, _, .dcons d ds, θ, φ => by
      simp only [Dms.subst, Dm.subst_comp d, Dms.subst_comp ds]

end

end Oopsla16
