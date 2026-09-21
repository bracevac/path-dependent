import Coercions.Oopsla16.Syntax

/-!
# Renaming and substitution

Two independent renaming families, one per scope, and a substitution of
variables for local variables.

Renaming the local scope is the usual capture-avoiding traversal.  Renaming
the store scope is what the reference gets for free from absolute positions:
its concrete identifiers are "invariant under context extension"
(`dot.v:21-22`), so allocation needs no adjustment there, whereas here the
weakening is explicit and is exactly `Rename.succ` on `σ`.

Substitution is a genuine substitution rather than a renaming, because the
reference's `open 0 u T` may replace a binder by a *concrete* variable: both
`T_Vary` (`dot.v:220-226`) and `ST_Obj` (`dot.v:199-200`) substitute a store
location for the object's self.  `Subst` therefore maps local variables to
`Vr`, and `Ty.substVr` is the single-binder case that the rules use.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-! ## The empty local scope -/

/-- The unique renaming out of the empty local scope; `BVar [] .var` is
uninhabited.  It weakens the premise of `stp_strong_sel1`/`stp_strong_sel2`
(`dot.v:308`, `dot.v:313`), which the reference checks in `stp []`. -/
def renameNil {s : Sig} : Rename [] s where
  var := fun x => nomatch x

/-! ## Renaming the local scope -/

def Vr.rename : Vr σ s1 → Rename s1 s2 → Vr σ s2
  | .conc x, _ => .conc x
  | .abs x, ρ => .abs (ρ.var x)

def Ty.rename : Ty σ s1 → Rename s1 s2 → Ty σ s2
  | .TBot, _ => .TBot
  | .TTop, _ => .TTop
  | .TFun l T1 T2, ρ => .TFun l (T1.rename ρ) (T2.rename ρ.lift)
  | .TTyp l T1 T2, ρ => .TTyp l (T1.rename ρ) (T2.rename ρ)
  | .TSel p l, ρ => .TSel (p.rename ρ) l
  | .TBind T, ρ => .TBind (T.rename ρ.lift)
  | .TAnd T1 T2, ρ => .TAnd (T1.rename ρ) (T2.rename ρ)
  | .TOr T1 T2, ρ => .TOr (T1.rename ρ) (T2.rename ρ)

mutual

def Tm.rename : Tm σ s1 → Rename s1 s2 → Tm σ s2
  | .tvar v, ρ => .tvar (v.rename ρ)
  | .tobj ds, ρ => .tobj (ds.rename ρ.lift)
  | .tapp t1 l t2, ρ => .tapp (t1.rename ρ) l (t2.rename ρ)

def Dm.rename : Dm σ s1 → Rename s1 s2 → Dm σ s2
  | .dty T, ρ => .dty (T.rename ρ)
  | .dfun OT1 OT2 t, ρ =>
      .dfun (OT1.map (fun T => T.rename ρ)) (OT2.map (fun T => T.rename ρ.lift))
        (t.rename ρ.lift)

def Dms.rename : Dms σ s1 → Rename s1 s2 → Dms σ s2
  | .dnil, _ => .dnil
  | .dcons d ds, ρ => .dcons (d.rename ρ) (ds.rename ρ)

end

/-- Weaken under one new local binder. -/
def Vr.weaken (v : Vr σ s) : Vr σ (s,x) := v.rename Rename.succ
/-- Weaken under one new local binder. -/
def Ty.weaken (T : Ty σ s) : Ty σ (s,x) := T.rename Rename.succ
/-- Weaken under one new local binder. -/
def Tm.weaken (t : Tm σ s) : Tm σ (s,x) := t.rename Rename.succ
/-- Weaken under one new local binder. -/
def Dms.weaken (ds : Dms σ s) : Dms σ (s,x) := ds.rename Rename.succ

/-! ## Renaming the store scope -/

def Vr.renameStore : Vr σ1 s → Rename σ1 σ2 → Vr σ2 s
  | .conc x, ρ => .conc (ρ.var x)
  | .abs x, _ => .abs x

def Ty.renameStore : Ty σ1 s → Rename σ1 σ2 → Ty σ2 s
  | .TBot, _ => .TBot
  | .TTop, _ => .TTop
  | .TFun l T1 T2, ρ => .TFun l (T1.renameStore ρ) (T2.renameStore ρ)
  | .TTyp l T1 T2, ρ => .TTyp l (T1.renameStore ρ) (T2.renameStore ρ)
  | .TSel p l, ρ => .TSel (p.renameStore ρ) l
  | .TBind T, ρ => .TBind (T.renameStore ρ)
  | .TAnd T1 T2, ρ => .TAnd (T1.renameStore ρ) (T2.renameStore ρ)
  | .TOr T1 T2, ρ => .TOr (T1.renameStore ρ) (T2.renameStore ρ)

mutual

def Tm.renameStore : Tm σ1 s → Rename σ1 σ2 → Tm σ2 s
  | .tvar v, ρ => .tvar (v.renameStore ρ)
  | .tobj ds, ρ => .tobj (ds.renameStore ρ)
  | .tapp t1 l t2, ρ => .tapp (t1.renameStore ρ) l (t2.renameStore ρ)

def Dm.renameStore : Dm σ1 s → Rename σ1 σ2 → Dm σ2 s
  | .dty T, ρ => .dty (T.renameStore ρ)
  | .dfun OT1 OT2 t, ρ =>
      .dfun (OT1.map (fun T => T.renameStore ρ)) (OT2.map (fun T => T.renameStore ρ))
        (t.renameStore ρ)

def Dms.renameStore : Dms σ1 s → Rename σ1 σ2 → Dms σ2 s
  | .dnil, _ => .dnil
  | .dcons d ds, ρ => .dcons (d.renameStore ρ) (ds.renameStore ρ)

end

/-- Weaken under one newly allocated store location. -/
def Ty.weakenStore (T : Ty σ s) : Ty (σ,x) s := T.renameStore Rename.succ
/-- Weaken under one newly allocated store location. -/
def Tm.weakenStore (t : Tm σ s) : Tm (σ,x) s := t.renameStore Rename.succ
/-- Weaken under one newly allocated store location. -/
def Dms.weakenStore (ds : Dms σ s) : Dms (σ,x) s := ds.renameStore Rename.succ

/-! ## Substitution of variables for local variables -/

/-- A substitution of the local scope: each local variable becomes a variable
of either zone. -/
structure Subst (σ : Sig) (s1 s2 : Sig) where
  var : BVar s1 .var → Vr σ s2

/-- Push a substitution under one binder. -/
def Subst.lift (θ : Subst σ s1 s2) : Subst σ (s1,x) (s2,x) where
  var := fun
    | .here => .abs .here
    | .there y => (θ.var y).weaken

/-- Substitute the innermost binder, `open 0 v` of `dot.v:136`. -/
def Subst.one (v : Vr σ s) : Subst σ (s,x) s where
  var := fun
    | .here => v
    | .there y => .abs y

def Vr.subst : Vr σ s1 → Subst σ s1 s2 → Vr σ s2
  | .conc x, _ => .conc x
  | .abs y, θ => θ.var y

def Ty.subst : Ty σ s1 → Subst σ s1 s2 → Ty σ s2
  | .TBot, _ => .TBot
  | .TTop, _ => .TTop
  | .TFun l T1 T2, θ => .TFun l (T1.subst θ) (T2.subst θ.lift)
  | .TTyp l T1 T2, θ => .TTyp l (T1.subst θ) (T2.subst θ)
  | .TSel p l, θ => .TSel (p.subst θ) l
  | .TBind T, θ => .TBind (T.subst θ.lift)
  | .TAnd T1 T2, θ => .TAnd (T1.subst θ) (T2.subst θ)
  | .TOr T1 T2, θ => .TOr (T1.subst θ) (T2.subst θ)

mutual

def Tm.subst : Tm σ s1 → Subst σ s1 s2 → Tm σ s2
  | .tvar v, θ => .tvar (v.subst θ)
  | .tobj ds, θ => .tobj (ds.subst θ.lift)
  | .tapp t1 l t2, θ => .tapp (t1.subst θ) l (t2.subst θ)

def Dm.subst : Dm σ s1 → Subst σ s1 s2 → Dm σ s2
  | .dty T, θ => .dty (T.subst θ)
  | .dfun OT1 OT2 t, θ =>
      .dfun (OT1.map (fun T => T.subst θ)) (OT2.map (fun T => T.subst θ.lift))
        (t.subst θ.lift)

def Dms.subst : Dms σ s1 → Subst σ s1 s2 → Dms σ s2
  | .dnil, _ => .dnil
  | .dcons d ds, θ => .dcons (d.subst θ) (ds.subst θ)

end

/-- `open 0 v T`, `dot.v:136`: instantiate the innermost binder by `v`. -/
def Ty.substVr (T : Ty σ (s,x)) (v : Vr σ s) : Ty σ s := T.subst (Subst.one v)
/-- `subst_tm`, `dot.v:172`, at the innermost binder. -/
def Tm.substVr (t : Tm σ (s,x)) (v : Vr σ s) : Tm σ s := t.subst (Subst.one v)
/-- `subst_dms`, `dot.v:185`, at the innermost binder. -/
def Dms.substVr (ds : Dms σ (s,x)) (v : Vr σ s) : Dms σ s := ds.subst (Subst.one v)

/-! ## Store lookup -/

/-- The definitions stored at a location.  Every entry already lives in the
full store scope, so there is nothing to weaken.  Corresponds to
`index x G1 = Some (vobj ds)`. -/
def Store.lookup : Store σ σ' → BVar σ' .var → Dms σ []
  | .cons _ ds, .here => ds
  | .cons G _, .there y => G.lookup y

/-- Rename every entry's store scope, which is what allocation needs. -/
def Store.renameStore : Store σ1 σ' → Rename σ1 σ2 → Store σ2 σ'
  | .nil, _ => .nil
  | .cons G d, ρ => .cons (G.renameStore ρ) (d.renameStore ρ)

/-- Weaken a store under one newly allocated location. -/
def Store.weakenStore (G : Store σ σ') : Store (σ,x) σ' := G.renameStore Rename.succ

@[simp] theorem Store.lookup_renameStore (G : Store σ1 σ') (ρ : Rename σ1 σ2)
    (y : BVar σ' .var) : (G.renameStore ρ).lookup y = (G.lookup y).renameStore ρ := by
  induction G with
  | nil => exact nomatch y
  | cons G d ih => cases y with
    | here => rfl
    | there y => exact ih y

end Oopsla16
