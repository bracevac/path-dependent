import Coercions.Oopsla16.Syntax

/-!
# Simultaneous substitution

One traversal per syntactic category, not three.  A `Subst` maps both scopes
at once: store locations to store locations — the reference never substitutes
for a concrete variable — and local variables to variables of *either* zone,
which is what `open 0 u T` needs when `u` is a store location, as it is in
`T_Vary` (`dot.v:220-226`) and `ST_Obj` (`dot.v:199-200`).

Renaming the local scope, renaming the store scope, weakening and
single-binder substitution are then all instances, so the composition and
commutation lemmas a metatheory needs are one family rather than three.

Renaming the store scope is what the reference gets for free from absolute
positions, which are "invariant under context extension" (`dot.v:21-22`).
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-- The unique map out of the empty local scope; `BVar [] .var` is
uninhabited.  It weakens the premise of `stp_strong_sel1`/`stp_strong_sel2`
(`dot.v:308`, `dot.v:313`), which the reference checks in `stp []`. -/
def renameNil {s : Sig} : Rename [] s where
  var := fun x => nomatch x

/-- Weaken a variable under one new local binder.  `Vr` is flat, so this is
not a traversal. -/
def Vr.weaken : Vr σ s → Vr σ (s,x)
  | .conc x => .conc x
  | .abs y => .abs (.there y)

/-- A simultaneous map of both scopes. -/
structure Subst (σ1 s1 σ2 s2 : Sig) where
  /-- Store locations go to store locations. -/
  conc : BVar σ1 .var → BVar σ2 .var
  /-- Local variables go to variables of either zone. -/
  abs : BVar s1 .var → Vr σ2 s2

namespace Subst

/-- Push under one binder. -/
def lift (θ : Subst σ1 s1 σ2 s2) : Subst σ1 (s1,x) σ2 (s2,x) where
  conc := θ.conc
  abs := fun | .here => .abs .here | .there y => (θ.abs y).weaken

/-- A renaming of the local scope. -/
def ofRename (ρ : Rename s1 s2) : Subst σ s1 σ s2 where
  conc := fun x => x
  abs := fun y => .abs (ρ.var y)

/-- A renaming of the store scope. -/
def ofStore (ρ : Rename σ1 σ2) : Subst σ1 s σ2 s where
  conc := fun x => ρ.var x
  abs := .abs

/-- `open 0 v`, `dot.v:136`: instantiate the innermost binder by `v`. -/
def one (v : Vr σ s) : Subst σ (s,x) σ s where
  conc := fun x => x
  abs := fun | .here => v | .there y => .abs y

end Subst

/-! ## The traversals -/

def Vr.subst : Vr σ1 s1 → Subst σ1 s1 σ2 s2 → Vr σ2 s2
  | .conc x, θ => .conc (θ.conc x)
  | .abs y, θ => θ.abs y

def Ty.subst : Ty σ1 s1 → Subst σ1 s1 σ2 s2 → Ty σ2 s2
  | .TBot, _ => .TBot
  | .TTop, _ => .TTop
  | .TFun l T1 T2, θ => .TFun l (T1.subst θ) (T2.subst θ.lift)
  | .TTyp l T1 T2, θ => .TTyp l (T1.subst θ) (T2.subst θ)
  | .TSel p l, θ => .TSel (p.subst θ) l
  | .TBind T, θ => .TBind (T.subst θ.lift)
  | .TAnd T1 T2, θ => .TAnd (T1.subst θ) (T2.subst θ)
  | .TOr T1 T2, θ => .TOr (T1.subst θ) (T2.subst θ)

mutual

def Tm.subst : Tm σ1 s1 → Subst σ1 s1 σ2 s2 → Tm σ2 s2
  | .tvar v, θ => .tvar (v.subst θ)
  | .tobj ds, θ => .tobj (ds.subst θ.lift)
  | .tapp t1 l t2, θ => .tapp (t1.subst θ) l (t2.subst θ)

def Dm.subst : Dm σ1 s1 → Subst σ1 s1 σ2 s2 → Dm σ2 s2
  | .dty T, θ => .dty (T.subst θ)
  | .dfun OT1 OT2 t, θ =>
      .dfun (OT1.map (fun T => T.subst θ)) (OT2.map (fun T => T.subst θ.lift))
        (t.subst θ.lift)

def Dms.subst : Dms σ1 s1 → Subst σ1 s1 σ2 s2 → Dms σ2 s2
  | .dnil, _ => .dnil
  | .dcons d ds, θ => .dcons (d.subst θ) (ds.subst θ)

end

/-! ## The instances the rules use -/

/-- Rename the local scope. -/
abbrev Ty.rename (T : Ty σ s1) (ρ : Rename s1 s2) : Ty σ s2 := T.subst (.ofRename ρ)
/-- Weaken under one new local binder. -/
abbrev Ty.weaken (T : Ty σ s) : Ty σ (s,x) := T.rename Rename.succ
/-- Rename the store scope. -/
abbrev Ty.renameStore (T : Ty σ1 s) (ρ : Rename σ1 σ2) : Ty σ2 s := T.subst (.ofStore ρ)
/-- Weaken under one newly allocated location. -/
abbrev Ty.weakenStore (T : Ty σ s) : Ty (σ,x) s := T.renameStore Rename.succ
/-- `open 0 v T`, `dot.v:136`. -/
abbrev Ty.substVr (T : Ty σ (s,x)) (v : Vr σ s) : Ty σ s := T.subst (.one v)

/-- `subst_tm`, `dot.v:172`, at the innermost binder. -/
abbrev Tm.substVr (t : Tm σ (s,x)) (v : Vr σ s) : Tm σ s := t.subst (.one v)
/-- Weaken under one newly allocated location. -/
abbrev Tm.weakenStore (t : Tm σ s) : Tm (σ,x) s := t.subst (.ofStore Rename.succ)
/-- Rename the store scope. -/
abbrev Tm.renameStore (t : Tm σ1 s) (ρ : Rename σ1 σ2) : Tm σ2 s := t.subst (.ofStore ρ)

/-- `subst_dms`, `dot.v:185`, at the innermost binder. -/
abbrev Dms.substVr (ds : Dms σ (s,x)) (v : Vr σ s) : Dms σ s := ds.subst (.one v)
/-- Weaken under one newly allocated location. -/
abbrev Dms.weakenStore (ds : Dms σ s) : Dms (σ,x) s := ds.subst (.ofStore Rename.succ)
/-- Rename the store scope. -/
abbrev Dms.renameStore (ds : Dms σ1 s) (ρ : Rename σ1 σ2) : Dms σ2 s := ds.subst (.ofStore ρ)

/-! ## Store lookup -/

/-- The definitions stored at a location.  Every entry already lives in the
full store scope, so there is nothing to weaken.  This is
`index x G1 = Some (vobj ds)` of `dot.v:203`, made total. -/
def Store.lookup : Store σ σ' → BVar σ' .var → Dms σ []
  | .cons _ ds, .here => ds
  | .cons G _, .there y => G.lookup y

/-- Rename every entry's store scope, which is what allocation needs. -/
def Store.renameStore : Store σ1 σ' → Rename σ1 σ2 → Store σ2 σ'
  | .nil, _ => .nil
  | .cons G d, ρ => .cons (G.renameStore ρ) (d.renameStore ρ)

/-- Weaken a store under one newly allocated location. -/
abbrev Store.weakenStore (G : Store σ σ') : Store (σ,x) σ' := G.renameStore Rename.succ

end Oopsla16
