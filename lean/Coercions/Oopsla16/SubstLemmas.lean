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

@[simp] theorem ofRename_id {σ s : Sig} :
    Subst.ofRename (σ := σ) (Rename.id (s := s)) = id := rfl

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

@[simp] theorem Vr.subst_id {σ s : Sig} (v : Vr σ s) : v.subst Subst.id = v := by
  cases v <;> rfl

@[simp] theorem Vr.subst_comp {σ1 σ2 σ3 s1 s2 s3 : Sig} (v : Vr σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) (φ : Subst σ2 s2 σ3 s3) :
    (v.subst θ).subst φ = v.subst (θ.comp φ) := by
  cases v <;> rfl

namespace Subst

/-- Composition is associative. -/
theorem comp_assoc {σ1 σ2 σ3 σ4 s1 s2 s3 s4 : Sig} (θ : Subst σ1 s1 σ2 s2)
    (φ : Subst σ2 s2 σ3 s3) (ψ : Subst σ3 s3 σ4 s4) :
    (θ.comp φ).comp ψ = θ.comp (φ.comp ψ) := by
  apply ext <;> intro y
  · rfl
  · exact Vr.subst_comp _ _ _

/-- The action of a substitution on the empty local scope: only its store
part survives, because `BVar [] .var` is uninhabited. -/
def atNil {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) : Subst σ1 [] σ2 [] where
  conc := θ.conc
  abs := fun y => nomatch y

/-- Weakening out of the empty local scope commutes with substituting. -/
theorem nil_comp {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (ofRename (renameNil (s := s1))).comp θ
      = (atNil θ).comp (ofRename (renameNil (s := s2))) := by
  apply ext <;> intro y
  · rfl
  · exact nomatch y

end Subst

/-! ## The identity law -/

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

/-! ## Two instances the typing rules read off directly

`T_App` (`dot.v:246-250`) is the instance of `T_AppVar` whose codomain does not
mention the parameter, and `T_Vary`'s conclusion (`dot.v:226`) is weakened out
of the empty local scope.  Both are instances of the identity law. -/

/-- Instantiating a weakening changes nothing.  This is the reference's
`z ∉ FV(T)` side condition on a codomain. -/
@[simp] theorem Ty.substVr_weaken {σ s : Sig} (T : Ty σ s) (v : Vr σ s) :
    T.weaken.substVr v = T := by
  show (T.subst (Subst.ofRename (Rename.succ (k := .var)))).subst (Subst.one v) = T
  rw [Ty.subst_comp,
    show (Subst.ofRename (Rename.succ (k := .var))).comp (Subst.one v)
        = Subst.id (σ := σ) (s := s) from by apply Subst.ext <;> intro y <;> rfl,
    Ty.subst_id]

/-- Weakening out of the empty local scope *into* the empty local scope is the
identity, because `BVar [] .var` is uninhabited.  This is what makes `T_Vary`'s
conclusion readable at `s = []` as the stored literal's type itself. -/
@[simp] theorem Ty.rename_renameNil_nil {σ : Sig} (T : Ty σ []) :
    T.rename (renameNil (s := [])) = T := by
  show T.subst (Subst.ofRename (renameNil (s := []))) = T
  have h : Subst.ofRename (renameNil (s := [])) = Subst.id (σ := σ) (s := []) := by
    apply Subst.ext <;> intro y <;> first | rfl | exact nomatch y
  rw [h]
  exact Ty.subst_id T

/-! ## Renaming the store commutes with the local scope

The store scope and the local scope are separate indices, so a store renaming
passes through every local operation untouched.  Stated once on `Subst`, the
laws for types and definition lists follow by fusion.  This is what the
reference gets for free from absolute positions (`dot.v:21-22`). -/

namespace Subst

/-- Pushing a store renaming under a local binder changes nothing: it does not
touch the local scope. -/
@[simp] theorem lift_ofStore {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) :
    (ofStore (s := s) ρ).lift = ofStore (s := (s,x)) ρ := by
  apply ext
  · intro l; rfl
  · intro y; cases y <;> rfl

/-- A local renaming and a store renaming commute. -/
theorem ofRename_comp_ofStore {σ1 σ2 s1 s2 : Sig} (ρ' : Rename s1 s2)
    (ρ : Rename σ1 σ2) :
    (ofRename (σ := σ1) ρ').comp (ofStore ρ) = (ofStore ρ).comp (ofRename ρ') := by
  apply ext <;> intro y <;> rfl

/-- Instantiating a local binder and renaming the store commute; the
instantiating variable is itself renamed. -/
theorem one_comp_ofStore {σ1 σ2 s : Sig} (v : Vr σ1 s) (ρ : Rename σ1 σ2) :
    (one v).comp (ofStore ρ) = (ofStore ρ).comp (one (v.subst (ofStore ρ))) := by
  apply ext
  · intro l; rfl
  · intro y; cases y <;> rfl

end Subst

/-- Renaming the store commutes with renaming the local scope. -/
theorem Ty.renameStore_rename {σ1 σ2 s1 s2 : Sig} (T : Ty σ1 s1) (ρ' : Rename s1 s2)
    (ρ : Rename σ1 σ2) :
    (T.rename ρ').renameStore ρ = (T.renameStore ρ).rename ρ' := by
  show (T.subst (Subst.ofRename ρ')).subst (Subst.ofStore ρ)
      = (T.subst (Subst.ofStore ρ)).subst (Subst.ofRename ρ')
  rw [Ty.subst_comp, Ty.subst_comp, Subst.ofRename_comp_ofStore]

/-- The weakening instance of `Ty.renameStore_rename`. -/
theorem Ty.renameStore_weaken {σ1 σ2 s : Sig} (T : Ty σ1 s) (ρ : Rename σ1 σ2) :
    T.weaken.renameStore ρ = (T.renameStore ρ).weaken :=
  Ty.renameStore_rename T Rename.succ ρ

/-- Renaming the store commutes with instantiating a local binder. -/
theorem Ty.renameStore_substVr {σ1 σ2 s : Sig} (T : Ty σ1 (s,x)) (v : Vr σ1 s)
    (ρ : Rename σ1 σ2) :
    (T.substVr v).renameStore ρ
      = (T.renameStore ρ).substVr (v.subst (Subst.ofStore ρ)) := by
  show (T.subst (Subst.one v)).subst (Subst.ofStore ρ)
      = (T.subst (Subst.ofStore ρ)).subst (Subst.one (v.subst (Subst.ofStore ρ)))
  rw [Ty.subst_comp, Ty.subst_comp, Subst.one_comp_ofStore]

/-- The same, for definition lists: what `T_Vary` and `ST_Obj` need. -/
theorem Dms.renameStore_substVr {σ1 σ2 s : Sig} (ds : Dms σ1 (s,x)) (v : Vr σ1 s)
    (ρ : Rename σ1 σ2) :
    (ds.substVr v).renameStore ρ
      = (ds.renameStore ρ).substVr (v.subst (Subst.ofStore ρ)) := by
  show (ds.subst (Subst.one v)).subst (Subst.ofStore ρ)
      = (ds.subst (Subst.ofStore ρ)).subst (Subst.one (v.subst (Subst.ofStore ρ)))
  rw [Dms.subst_comp, Dms.subst_comp, Subst.one_comp_ofStore]

/-! ### Pushing a store renaming through a constructor

Stated with `renameStore` on both sides rather than by unfolding to `subst`,
so that a rewrite that has to follow — `renameStore_weaken`,
`renameStore_substVr`, `renameStore_rename` — still finds its pattern. -/

/-- Bottom is closed. -/
@[simp] theorem Ty.renameStore_TBot {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) :
    (Ty.TBot (σ := σ1) (s := s)).renameStore ρ = .TBot := rfl

/-- Top is closed. -/
@[simp] theorem Ty.renameStore_TTop {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) :
    (Ty.TTop (σ := σ1) (s := s)).renameStore ρ = .TTop := rfl

/-- A method member: the codomain is under a local binder, which the store renaming ignores. -/
@[simp] theorem Ty.renameStore_TFun {σ1 σ2 s : Sig} (l : Lb) (T1 : Ty σ1 s)
    (T2 : Ty σ1 (s,x)) (ρ : Rename σ1 σ2) :
    (Ty.TFun l T1 T2).renameStore ρ
      = .TFun l (T1.renameStore ρ) (T2.renameStore ρ) := by
  show Ty.TFun l (T1.subst (Subst.ofStore ρ)) (T2.subst (Subst.ofStore ρ).lift) = _
  rw [Subst.lift_ofStore]

/-- A type member. -/
@[simp] theorem Ty.renameStore_TTyp {σ1 σ2 s : Sig} (l : Lb) (T1 T2 : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    (Ty.TTyp l T1 T2).renameStore ρ
      = .TTyp l (T1.renameStore ρ) (T2.renameStore ρ) := rfl

/-- A selection: only the receiver moves, and only if it is a location. -/
@[simp] theorem Ty.renameStore_TSel {σ1 σ2 s : Sig} (p : Vr σ1 s) (l : Lb)
    (ρ : Rename σ1 σ2) :
    (Ty.TSel p l).renameStore ρ = .TSel (p.subst (Subst.ofStore ρ)) l := rfl

/-- A recursive type; again the local binder is ignored. -/
@[simp] theorem Ty.renameStore_TBind {σ1 σ2 s : Sig} (T : Ty σ1 (s,x))
    (ρ : Rename σ1 σ2) :
    (Ty.TBind T).renameStore ρ = .TBind (T.renameStore ρ) := by
  show Ty.TBind (T.subst (Subst.ofStore ρ).lift) = _
  rw [Subst.lift_ofStore]

/-- An intersection. -/
@[simp] theorem Ty.renameStore_TAnd {σ1 σ2 s : Sig} (T1 T2 : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    (Ty.TAnd T1 T2).renameStore ρ = .TAnd (T1.renameStore ρ) (T2.renameStore ρ) := rfl

/-- A union. -/
@[simp] theorem Ty.renameStore_TOr {σ1 σ2 s : Sig} (T1 T2 : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    (Ty.TOr T1 T2).renameStore ρ = .TOr (T1.renameStore ρ) (T2.renameStore ρ) := rfl

/-- A variable term. -/
@[simp] theorem Tm.renameStore_tvar {σ1 σ2 s : Sig} (v : Vr σ1 s)
    (ρ : Rename σ1 σ2) :
    (Tm.tvar v).renameStore ρ = .tvar (v.subst (Subst.ofStore ρ)) := rfl

/-- An object literal. -/
@[simp] theorem Tm.renameStore_tobj {σ1 σ2 s : Sig} (ds : Dms σ1 (s,x))
    (ρ : Rename σ1 σ2) :
    (Tm.tobj ds).renameStore ρ = .tobj (ds.renameStore ρ) := by
  show Tm.tobj (ds.subst (Subst.ofStore ρ).lift) = _
  rw [Subst.lift_ofStore]

/-- An application. -/
@[simp] theorem Tm.renameStore_tapp {σ1 σ2 s : Sig} (t1 : Tm σ1 s) (l : Lb)
    (t2 : Tm σ1 s) (ρ : Rename σ1 σ2) :
    (Tm.tapp t1 l t2).renameStore ρ
      = .tapp (t1.renameStore ρ) l (t2.renameStore ρ) := rfl

/-- The empty definition list. -/
@[simp] theorem Dms.renameStore_dnil {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) :
    (Dms.dnil (σ := σ1) (s := s)).renameStore ρ = .dnil := rfl

/-- A definition list cons. -/
@[simp] theorem Dms.renameStore_dcons {σ1 σ2 s : Sig} (d : Dm σ1 s) (ds : Dms σ1 s)
    (ρ : Rename σ1 σ2) :
    (Dms.dcons d ds).renameStore ρ
      = .dcons (d.subst (Subst.ofStore ρ)) (ds.renameStore ρ) := rfl

/-- A type definition. -/
@[simp] theorem Dm.renameStore_dty {σ1 σ2 s : Sig} (T : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    (Dm.dty T).subst (Subst.ofStore ρ) = .dty (T.renameStore ρ) := rfl

/-- A method definition, with both optional annotations. -/
@[simp] theorem Dm.renameStore_dfun {σ1 σ2 s : Sig} (OT1 : Option (Ty σ1 s))
    (OT2 : Option (Ty σ1 (s,x))) (t : Tm σ1 (s,x)) (ρ : Rename σ1 σ2) :
    (Dm.dfun OT1 OT2 t).subst (Subst.ofStore ρ)
      = .dfun (OT1.map (fun T => T.renameStore ρ))
          (OT2.map (fun T => T.renameStore ρ)) (t.renameStore ρ) := by
  show Dm.dfun (OT1.map (fun T => T.subst (Subst.ofStore ρ)))
      (OT2.map (fun T => T.subst (Subst.ofStore ρ).lift))
      (t.subst (Subst.ofStore ρ).lift) = _
  rw [Subst.lift_ofStore]

/-! ## Positional labels survive substitution

A member's label is the length of its tail (`dot.v:269`, `dot.v:278`), and
substitution is length-preserving, so `Dms.get?` commutes with it. -/

/-- Substitution does not change the number of members. -/
@[simp] theorem Dms.length_subst {σ1 σ2 s1 s2 : Sig} :
    (ds : Dms σ1 s1) → (θ : Subst σ1 s1 σ2 s2) → (ds.subst θ).length = ds.length
  | .dnil, _ => rfl
  | .dcons d ds, θ => by
      show (ds.subst θ).length + 1 = ds.length + 1
      rw [Dms.length_subst ds θ]

/-- Reading a member commutes with substitution.  `index l (dms_to_list ds)` of
`dot.v:203`, substituted. -/
theorem Dms.get?_subst {σ1 σ2 s1 s2 : Sig} :
    (ds : Dms σ1 s1) → (θ : Subst σ1 s1 σ2 s2) → (a : Lb) →
    (ds.subst θ).get? a = (ds.get? a).map (fun d => d.subst θ)
  | .dnil, _, _ => rfl
  | .dcons d ds, θ, a => by
      show (if a = (ds.subst θ).length then some (d.subst θ) else (ds.subst θ).get? a)
          = Option.map (fun e => Dm.subst e θ)
              (if a = ds.length then some d else ds.get? a)
      rw [Dms.length_subst ds θ]
      by_cases h : a = ds.length
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; exact Dms.get?_subst ds θ a

/-- Looking a location up in a renamed store is looking it up and renaming.
Every entry already lives in the full store scope, so no index moves. -/
theorem Store.lookup_renameStore {σ1 σ2 : Sig} : {σ' : Sig} → (G : Store σ1 σ') →
    (ρ : Rename σ1 σ2) → (l : BVar σ' .var) →
    (G.renameStore ρ).lookup l = (G.lookup l).renameStore ρ
  | _, .cons _ _, _, .here => rfl
  | _, .cons G _, ρ, .there y => Store.lookup_renameStore G ρ y

end Oopsla16
