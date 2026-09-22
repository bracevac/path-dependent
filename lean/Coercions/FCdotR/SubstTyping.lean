import Coercions.FCdotR.Subst
import Coercions.FCdotR.Locality

/-!
# Preservation of typing under substitution

The two evidence judgments transported along a generated substitution:

```text
LeTy G W Γ e S T   →   LeTy G' W' Γ' f (S[θ]) (T[θ])
VcTy G W Γ p v T   →   VcTy G' W' Γ' (m.image p) w (T[m↾p])
```

The conclusions are stated **existentially**, as a substituted term paired with
its derivation, and not as a statement about `Le.subst`/`Vc.subst`.  That is
forced, not stylistic: the `vcVar` clause must hand back the *hypothesis's*
evidence for the image, and the image's evidence is in general not `vcVar` —
substituting an abstract variable by a location replaces `htp_var` by whatever
observes the store.  `Le.subst` and `Vc.subst` remain the erasure-preserving
action on syntax; this module is the semantic content.

`MonoSyn.Ev` is the plan's `Subst.Ev` (§B.3).  Its three fields are the minimal
agreement the induction consumes, and no more:

* `defs` — the stored definitions agree: `G'.lookup (θ.conc ℓ)` is
  `G.lookup ℓ` substituted.  Only `defL`/`defR` read it, and they read it
  through `Dms.get?_subst`.
* `tys` — the stored literals' *types* agree at the same location.  Only
  `vcLoc` reads it.  It is stated at `tyOf`, i.e. after the self has been
  instantiated, because that is the only form any rule mentions; requiring
  `W' (θ.conc ℓ) = (W ℓ)[…]` would be strictly stronger and is not needed.
* `vc` — for each abstract variable, observation evidence for its image at its
  substituted lookup type.  This is the reference's `Definition Subst`
  (`dot_soundness.v:262`), whose hypothesis is an `htpy` and not a `has_type`.

There is deliberately **no** field relating `Γ'` to `Γ` pointwise, and none
requiring `(Γ.upTo x)[θ↾x] = Γ'.upTo (θ.abs x)`; `Structural` records why that
equality fails and is not needed.

## What is assumed, and why

The `vcSub` clause needs the inclusion premise transported *inside the
subject's prefix*, so it needs a `MonoSyn.Ev` for the restricted substitution
over the restricted contexts.  That is the plan's **Lemma R** (§B.4).  It is
taken here as an explicit hypothesis, `LemmaR`, threaded through the induction:
every other clause is discharged, so the remaining obligation of the whole
substitution theorem is exactly one statement, written out below, and no
`sorry` stands in for it.

`LemmaR` is *not* provable from the data in this module as it stands.  Its
`vc` field at `y : BVar (scopeUpTo x) .var` must produce evidence at the type
`((Γ.upTo x).lookupAt y)[(m↾x)↾y]` from the outer field at
`z = (renameUpTo x).var y`, which delivers `(Γ.lookupAt z)[m↾z]`.  The two are
related by `Prefix.lookupAt_upTo`, an `HEq` whose scope equation is
`scopeUpTo_renameUpTo`, *together with* the coherence
`(m↾x)↾y ≅ m↾z`, which is a heterogeneous equality of substitutions in both
their domain and their codomain scope.  `MonoSyn` makes that coherence
*provable per generator* rather than assumable — which is the point of the
generator tree — but the proof is a genuine `HEq` induction that this session
did not carry out.  `VcTy.toFull` below is the other half of the plan's
Lemma 0, added because Lemma R's proof needs the weakening direction that
`Locality` does not state.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Subst Dms scopeUpTo varUpTo renameUpTo renameNil)

/-! ## Two substitution laws on types -/

/-- A weakened variable is the successor renaming applied. -/
theorem Vr.weaken_eq_subst_succ {σ s : Sig} (v : Vr σ s) :
    v.weaken = v.subst (Subst.ofRename (Rename.succ (k := .var))) := by
  cases v <;> rfl

/-- Weakening commutes with a lifted substitution.  This is `stp_fun`'s and
`muDrop`'s bookkeeping: a hypothesis that does not mention its own binder stays
one. -/
theorem Ty.weaken_subst_lift {σ1 σ2 s1 s2 : Sig} (T : Ty σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) : T.weaken.subst θ.lift = (T.subst θ).weaken := by
  show (T.subst (Subst.ofRename (Rename.succ (k := .var)))).subst θ.lift
      = (T.subst θ).subst (Subst.ofRename (Rename.succ (k := .var)))
  rw [Ty.subst_comp, Ty.subst_comp]
  refine congrArg (fun φ => T.subst φ) (Subst.ext (fun _ => rfl) ?_)
  intro y
  exact Vr.weaken_eq_subst_succ _

/-- Weakening out of the empty local scope commutes with substituting: the type
level of `Subst.nil_comp`, and what `defL`/`defR` need to relocate their
conclusion. -/
theorem Ty.renameNil_subst {σ1 σ2 s1 s2 : Sig} (T : Ty σ1 [])
    (θ : Subst σ1 s1 σ2 s2) :
    (T.rename (renameNil (s := s1))).subst θ
      = (T.subst (Subst.atNil θ)).rename (renameNil (s := s2)) := by
  show (T.subst (Subst.ofRename (renameNil (s := s1)))).subst θ
      = (T.subst (Subst.atNil θ)).subst (Subst.ofRename (renameNil (s := s2)))
  rw [Ty.subst_comp, Ty.subst_comp, Subst.nil_comp]

/-! ## Locality, the remaining direction

`Locality` proves that an observation of an abstract variable *restricts* to
that variable's prefix.  The converse — that it re-enters the full context —
is what Lemma R's proof needs, and it is the same one-line recursion. -/

/-- An observation over a prefix re-enters the full context.  With
`VcTy.strengthen` this is the plan's Lemma 0 as an isomorphism. -/
def VcTy.toFull {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {x : BVar s .var} : {v : Vc σ (scopeUpTo x)} → {T : Ty σ (scopeUpTo x)} →
    VcTy G W (Γ.upTo x) (.abs (varUpTo x)) v T → VcTy G W Γ (.abs x) v T
  | _, _, .vcVar => (lookupAt_upTo_self Γ x) ▸ .vcVar
  | _, _, .vcUnfold d => .vcUnfold (toFull d)
  | _, _, .vcSub T1 d e =>
      .vcSub (Γ := Γ) (p := .abs x) T1 (toFull d) (by
        rw [show ctxAt Γ (Vr.abs x) = (Γ.upTo x).upTo (varUpTo x) from
              (upTo_upTo_self Γ x).symm]
        exact e)

/-- An observation of an abstract variable survives one more hypothesis.  Every
former consults only `ctxAt Γ (.abs x)`, which `Ctx.cons` leaves alone. -/
def VcTy.weakenVar {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) {x0 : BVar s .var} :
    {v : Vc σ (scopeUpTo x0)} → {T : Ty σ (scopeUpTo x0)} →
    VcTy G W Γ (.abs x0) v T → VcTy G W (Γ.cons S) (.abs (.there x0)) v T
  | _, _, .vcVar => .vcVar
  | _, _, .vcUnfold d => .vcUnfold (weakenVar S d)
  | _, _, .vcSub T1 d e =>
      .vcSub (Γ := Γ.cons S) (p := .abs (.there x0)) T1 (weakenVar S d) e

/-! ## The hypothesis structure -/

/-- The plan's `Subst.Ev`: what evidence substitution consumes.  Store
agreement in both components, and observation evidence for the image of every
abstract variable at its substituted lookup type. -/
structure MonoSyn.Ev {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (G : Store σ1 σ1) (W : StoreTy σ1) (Γ : Ctx σ1 s1) (m : MonoSyn θ)
    (G' : Store σ2 σ2) (W' : StoreTy σ2) (Γ' : Ctx σ2 s2) : Type where
  /-- The stored definitions agree at every location. -/
  defs : (l : BVar σ1 .var) →
      G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ)
  /-- The stored literals' types agree at every location. -/
  tys : (l : BVar σ1 .var) →
      tyOf W' (θ.conc l) = (tyOf W l).subst (Subst.atNil θ)
  /-- Observation evidence for the image of every abstract variable. -/
  vc : (x : BVar s1 .var) →
      Σ w : Vc σ2 (scopeAt (m.image (.abs x))),
        VcTy G' W' Γ' (m.image (.abs x)) w
          ((Γ.lookupAt x).subst (m.restrict (.abs x)))

namespace MonoSyn.Ev

/-- The action of the identity on the empty local scope is the identity.  A
`Subst σ [] σ []` is its store part, and the identity's is the identity. -/
theorem atNil_id {σ s : Sig} :
    Subst.atNil (Subst.id (σ := σ) (s := s)) = Subst.id (σ := σ) (s := []) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- The identity substitution carries a hypothesis structure: `Ev` is
inhabited, so the theorem below is not vacuous.  Every variable's own
hypothesis observes it, which is `htp_var`. -/
def refl {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    Ev G W Γ (MonoSyn.id (σ := σ) (s := s)) G W Γ where
  defs := fun l => by
    show G.lookup l = (G.lookup l).subst (Subst.atNil Subst.id)
    rw [atNil_id, Dms.subst_id]
  tys := fun l => by
    show tyOf W l = (tyOf W l).subst (Subst.atNil Subst.id)
    rw [atNil_id, Ty.subst_id]
  vc := fun x => ⟨.vcVar, by
    show VcTy G W Γ (Vr.abs x) Vc.vcVar ((Γ.lookupAt x).subst Subst.id)
    rw [Ty.subst_id]
    exact .vcVar⟩

/-- Restricting to the empty local scope.  The variable field is vacuous and
the store fields are unchanged, because `Subst.atNil` keeps the store part. -/
def atNil {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : Ev G W Γ m G' W' Γ') : Ev G W .nil m.atNil G' W' .nil where
  defs := E.defs
  tys := E.tys
  vc := fun x => nomatch x

/-- Pushing under a binder.  At the new binder the evidence is `vcVar`; at an
older one it is the outer evidence, weakened by `VcTy.weakenVar` at an abstract
image and by `VcTy.ofLoc` at a concrete one. -/
def lift {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : Ev G W Γ m G' W' Γ') (S : Ty σ1 (s1,x)) :
    Ev G W (Γ.cons S) m.lift G' W' (Γ'.cons (S.subst θ.lift)) where
  defs := E.defs
  tys := E.tys
  vc := by
    intro y
    cases y with
    | here => exact ⟨.vcVar, .vcVar⟩
    | there y =>
        have hy : Σ w : Vc σ2 (scopeAt ((m.atAbs y).image)),
            VcTy G' W' Γ' ((m.atAbs y).image) w
              ((Γ.lookupAt y).subst ((m.atAbs y).restrict)) := E.vc y
        revert hy
        show (Σ w : Vc σ2 (scopeAt ((m.atAbs y).image)),
                VcTy G' W' Γ' ((m.atAbs y).image) w
                  ((Γ.lookupAt y).subst ((m.atAbs y).restrict))) →
            Σ w : Vc σ2 (scopeAt ((m.atAbs y).underLift.image)),
              VcTy G' W' (Γ'.cons (S.subst θ.lift)) ((m.atAbs y).underLift.image) w
                ((Γ.lookupAt y).subst ((m.atAbs y).underLift.restrict))
        cases m.atAbs y with
        | toAbs z r himg hstar hself hsyn =>
            exact fun hy => ⟨hy.1, VcTy.weakenVar (S.subst θ.lift) hy.2⟩
        | toConc l r himg hstar hself hsyn =>
            exact fun hy => ⟨hy.1, VcTy.ofLoc hy.2⟩

end MonoSyn.Ev

/-! ## The store part of a restriction

A restriction acts on the store exactly as the substitution does — the star law
says so on the `conc` component — so the two store-agreement fields of a
hypothesis structure survive restriction untouched.  Only the variable field
does not, which is what isolates the obligation below. -/

/-- A restriction agrees with the substitution on locations. -/
theorem MonoSyn.restrict_conc {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (m : MonoSyn θ) (p : Vr σ1 s1) (l : BVar σ1 .var) :
    (m.restrict p).conc l = θ.conc l :=
  (congrArg (fun t => Subst.conc t l) (m.star p)).symm

/-- Hence a restriction and the substitution have the same action on the empty
local scope. -/
theorem MonoSyn.atNil_restrict {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (m : MonoSyn θ) (p : Vr σ1 s1) :
    Subst.atNil (m.restrict p) = Subst.atNil θ :=
  Subst.ext (m.restrict_conc p) (fun y => nomatch y)

/-- **Lemma R**, the one obligation this module assumes: a hypothesis structure
restricts to the subject's prefix.  At a location it is immediate — the
variable field is vacuous and both contexts are `.nil` — so its content is the
abstract case, where it is the coherence of iterated restriction. -/
abbrev LemmaR : Type :=
  ∀ {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2},
    MonoSyn.Ev G W Γ m G' W' Γ' → (p : Vr σ1 s1) →
    MonoSyn.Ev G W (ctxAt Γ p) (m.resSyn p) G' W' (ctxAt Γ' (m.image p))

/-! ## The substitution theorem

One mutual recursion, one clause per former, structure-preserving.  No
canonical forms, no narrowing, no transitivity pushback and no pack count
occurs in any clause, which is what keeps this module below the normalizer in
the import order. -/

mutual

/-- Inclusion evidence transported along a generated substitution. -/
def LeTy.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {e : Le σ1 s1} {S T : Ty σ1 s1} (R : LemmaR)
    (d : LeTy G W Γ e S T) {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    {m : MonoSyn θ} {G' : Store σ2 σ2} {W' : StoreTy σ2}
    {Γ' : Ctx σ2 s2} (E : MonoSyn.Ev G W Γ m G' W' Γ') :
    Σ f : Le σ2 s2, LeTy G' W' Γ' f (S.subst θ) (T.subst θ) :=
  match d with
  | .refl T0 => ⟨.refl _, .refl (T0.subst _)⟩
  | .top T0 => ⟨.top _, .top (T0.subst _)⟩
  | .bot T0 => ⟨.bot _, .bot (T0.subst _)⟩
  | .trans M d1 d2 =>
      ⟨.trans (M.subst _) (LeTy.substEv R d1 E).1 (LeTy.substEv R d2 E).1,
        .trans _ (LeTy.substEv R d1 E).2 (LeTy.substEv R d2 E).2⟩
  | .dtyp (l := l) d1 d2 =>
      ⟨.dtyp l (LeTy.substEv R d1 E).1 (LeTy.substEv R d2 E).1,
        .dtyp (LeTy.substEv R d1 E).2 (LeTy.substEv R d2 E).2⟩
  | .andI (T1 := T1) T2 d1 d2 =>
      ⟨.andI _ _ (LeTy.substEv R d1 E).1 (LeTy.substEv R d2 E).1,
        .andI _ _ (LeTy.substEv R d1 E).2 (LeTy.substEv R d2 E).2⟩
  | .andE1 T2 d1 =>
      ⟨.andE1 _ (LeTy.substEv R d1 E).1, .andE1 _ (LeTy.substEv R d1 E).2⟩
  | .andE2 T1 d1 =>
      ⟨.andE2 _ (LeTy.substEv R d1 E).1, .andE2 _ (LeTy.substEv R d1 E).2⟩
  | .orI1 T2 d1 =>
      ⟨.orI1 _ (LeTy.substEv R d1 E).1, .orI1 _ (LeTy.substEv R d1 E).2⟩
  | .orI2 T1 d1 =>
      ⟨.orI2 _ (LeTy.substEv R d1 E).1, .orI2 _ (LeTy.substEv R d1 E).2⟩
  | .orE S1 S2 d1 d2 =>
      ⟨.orE _ _ (LeTy.substEv R d1 E).1 (LeTy.substEv R d2 E).1,
        .orE _ _ (LeTy.substEv R d1 E).2 (LeTy.substEv R d2 E).2⟩
  | .dfun (l := l) (S2 := S2) d1 d2 =>
      ⟨.dfun l (LeTy.substEv R d1 E).1
          (LeTy.substEv R d2 (Ty.weaken_subst_lift S2 θ ▸ E.lift S2.weaken)).1,
        .dfun (LeTy.substEv R d1 E).2
          (LeTy.substEv R d2 (Ty.weaken_subst_lift S2 θ ▸ E.lift S2.weaken)).2⟩
  | .bindx S0 T0 d1 =>
      ⟨.bindx (S0.subst θ.lift) (T0.subst θ.lift)
          (LeTy.substEv R d1 (E.lift S0)).1,
        .bindx _ _ (LeTy.substEv R d1 (E.lift S0)).2⟩
  | .muDrop T0 =>
      ⟨.muDrop (T0.subst θ), by
        show LeTy _ _ _ (Le.muDrop (T0.subst θ))
          (Ty.TBind (T0.weaken.subst θ.lift)) (T0.subst θ)
        rw [Ty.weaken_subst_lift]
        exact .muDrop _⟩
  | .defL (l := l) (a := a) (TX := TX) (T2 := T2) hget d1 =>
      ⟨.defL (θ.conc l) a (LeTy.substEv R d1 E.atNil).1, by
        show LeTy _ _ _ (Le.defL (θ.conc l) a _)
          (Ty.TSel (.conc (θ.conc l)) a) ((T2.rename renameNil).subst θ)
        rw [Ty.renameNil_subst]
        refine .defL ?_ (LeTy.substEv R d1 E.atNil).2
        rw [E.defs l, Dms.get?_subst, hget]
        rfl⟩
  | .defR (l := l) (a := a) (T1 := T1) (TX := TX) hget d1 =>
      ⟨.defR (θ.conc l) a (LeTy.substEv R d1 E.atNil).1, by
        show LeTy _ _ _ (Le.defR (θ.conc l) a _)
          ((T1.rename renameNil).subst θ) (Ty.TSel (.conc (θ.conc l)) a)
        rw [Ty.renameNil_subst]
        refine .defR ?_ (LeTy.substEv R d1 E.atNil).2
        rw [E.defs l, Dms.get?_subst, hget]
        rfl⟩
  | .selL (p := p) (a := a) (U := U) dv =>
      ⟨.selL (m.image p) a (VcTy.substEv R dv E).1, by
        show LeTy _ _ _ (Le.selL (m.image p) a _)
          (Ty.TSel (p.subst θ) a) ((U.rename (renameAt p)).subst θ)
        rw [← m.image_eq p, m.star_ty p U]
        exact .selL (VcTy.substEv R dv E).2⟩
  | .selR (p := p) (a := a) (S := S0) dv =>
      ⟨.selR (m.image p) a (VcTy.substEv R dv E).1, by
        show LeTy _ _ _ (Le.selR (m.image p) a _)
          ((S0.rename (renameAt p)).subst θ) (Ty.TSel (p.subst θ) a)
        rw [← m.image_eq p, m.star_ty p S0]
        exact .selR (VcTy.substEv R dv E).2⟩

/-- Observation evidence transported along a generated substitution.  The type
moves by the *restriction* at the subject, which is what makes the statement
true at a subject whose image is a location. -/
def VcTy.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {p : Vr σ1 s1} {v : Vc σ1 (scopeAt p)}
    {T : Ty σ1 (scopeAt p)} (R : LemmaR) (d : VcTy G W Γ p v T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.Ev G W Γ m G' W' Γ') :
    Σ w : Vc σ2 (scopeAt (m.image p)),
      VcTy G' W' Γ' (m.image p) w (T.subst (m.restrict p)) :=
  match d with
  | .vcVar (x := x) => E.vc x
  | .vcLoc (l := l) => ⟨.vcLoc (θ.conc l), (E.tys l) ▸ VcTy.vcLoc⟩
  | .vcPack (l := l) (T := T0) dv =>
      ⟨.vcPack (T0.subst (Subst.atNil θ).lift) (VcTy.substEv R dv E).1,
        .vcPack ((m.substVr_selfAt (.conc l) T0) ▸ (VcTy.substEv R dv E).2)⟩
  | .vcUnfold (p := p) (T := T0) dv =>
      ⟨.vcUnfold (T0.subst (m.restrict p).lift) (VcTy.substEv R dv E).1, by
        rw [m.substVr_selfAt p T0]
        exact .vcUnfold (VcTy.substEv R dv E).2⟩
  | .vcSub (p := p) T1 dv de =>
      ⟨.vcSub (T1.subst (m.restrict p)) (LeTy.substEv R de (R E p)).1
          (VcTy.substEv R dv E).1,
        .vcSub _ (VcTy.substEv R dv E).2 (LeTy.substEv R de (R E p)).2⟩

end

/-- What remains of Lemma R once the store fields are discharged: the
*variable* field of a restricted hypothesis structure, at an abstract subject.
This is the whole of the obligation, and it is a statement about observation
evidence alone.

Its content, spelled out: the outer field at `z = (renameUpTo x).var y` gives
evidence over `Γ'` for the image of `z`; `VcTy.strengthen` and `VcTy.toFull`
move it between `Γ'` and the prefixes, `Prefix.upTo_upTo` and
`Prefix.lookupAt_upTo` identify the contexts and the lookup types, and what is
still missing is the *coherence* `(m↾x)↾y ≅ m↾z` — a heterogeneous equality of
substitutions, since `scopeUpTo z = scopeUpTo y` only by
`scopeUpTo_renameUpTo` and the two codomain scopes agree only by a second
instance of it.  `MonoSyn` makes that coherence provable one generator at a
time; carrying the `HEq` elimination through `Type`-valued evidence is the work
that is not done here. -/
abbrev LemmaRVc : Type :=
  ∀ {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2},
    MonoSyn.Ev G W Γ m G' W' Γ' → (x : BVar s1 .var) →
    (y : BVar (scopeUpTo x) .var) →
    Σ w : Vc σ2 (scopeAt ((m.resSyn (.abs x)).image (.abs y))),
      VcTy G' W' (ctxAt Γ' (m.image (.abs x)))
        ((m.resSyn (.abs x)).image (.abs y)) w
        (((Γ.upTo x).lookupAt y).subst ((m.resSyn (.abs x)).restrict (.abs y)))

/-- Lemma R follows from its variable field alone.  At a location it is
unconditional: both restricted contexts are `.nil`, the variable field is
vacuous because `BVar [] .var` is uninhabited, and the store fields are
`MonoSyn.Ev.atNil`.  At an abstract subject the store fields are the outer
ones, transported along `MonoSyn.restrict_conc`. -/
def LemmaR.ofVc (H : LemmaRVc) : LemmaR := by
  intro σ1 σ2 s1 s2 θ m G W Γ G' W' Γ' E p
  cases p with
  | conc l => exact E.atNil
  | abs x =>
      exact
        { defs := fun l => by
            rw [m.atNil_restrict (.abs x), m.restrict_conc (.abs x) l]
            exact E.defs l
          tys := fun l => by
            rw [m.atNil_restrict (.abs x), m.restrict_conc (.abs x) l]
            exact E.tys l
          vc := fun y => H E x y }

end FCdotR
