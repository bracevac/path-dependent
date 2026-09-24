import Coercions.FCdotR.CanonicalForms
import Coercions.FCdotR.SubstTyping
import Coercions.FCdotR.TermTyping

/-!
# Inversion: transitivity elimination for closed inclusion evidence

The half of canonical forms that `Normalizer` and `CanonicalForms` left open.
Over an **honest** store (`StoreTyping.Store.Honest`), and with no other
hypothesis, every closed inclusion is inverted to the rule that introduced the
head of its endpoints, through any number of `trans`, intersection, union and
selection steps (`Store.Honest.nf`, and the inversion lemmas
`Store.Honest.invTyp`, `invTypTyp`, `invIntoBind`, `invBind`).  From that:

* `Normalizer.Contract` is inhabited (`Store.Honest.contract`), so redex
  elimination `VcTy.canon` holds outright (`Store.Honest.canon`);
* `CanonicalForms.BoundsVacuous` is inhabited (`Store.Honest.boundsVacuous`);
* **consistency** holds with the honesty of the store as its only hypothesis
  (`consistency_honest`), and so does `no_loc_le_bot`;
* `obs_conc_admissible`, the converse of `obs_conc_easy`: the concrete
  `selL`/`selR` add no power over `defL`/`defR`;
* canonical forms for closed observations of a location at a type member
  (`obsTyp`), a recursive type (`obsBind`) and a method type (`obsFun`).

The honesty hypothesis cannot be dropped: `CanonicalForms.DishonestStore`
derives `⊤ ≤ ⊥` over a store typing that lies.  It is used in one place only,
to know that the recorded type of every location is a *literal type*
(`RecordedLit`), so every result is also stated at `RecordedLit G W`, which
another store invariant can supply — `defsLitTy` is the entry point for one
phrased with the target's `DefsTy`, as a machine store's is.

## How

The reference proves the same facts in `dot_soundness.v` with precise
subtyping `stpp`, the pushback lemma, and a pack-counted variable typing
`htpy`; the argument here has the same three parts.

1. **Strong evidence and its normal forms.**  Evidence is *strong*
   (`Forms.Le.Strong`) when it selects on no location through an observation:
   every concrete selection is `defL`/`defR`, as in the source.  `Forms.LeNf`
   is the normal-form datatype, the target's `stpp`.  `LeTy.pushback`
   eliminates transitivity from strong closed evidence by structural recursion
   (`stp_trans_pushback_aux`); `LeNf.precompose` is the half of the composition
   of forms that needs no recursion, and `SLe.nf` is the normalizer.  Its
   soundness — the `FormTyped` obligation — is `LeNf.toSLe`: normal forms are
   intrinsically typed and map back to strong evidence.  No fuel is used.  The
   narrowing and weakening that the recursive formers need are instances of
   the bounded substitution theorem below (`SLe.narrow`, `SLe.weaken`), so no
   separate narrowing lemma exists.
2. **The store.**  A stored literal's type is `⊤` or an intersection of members
   whose type members are exact (`D_Typ`) — the shape `LitTy`.  A normal form
   out of it into `{a : S..U}` reads the stored `dty TX` with bounds
   `S ≤ TX ≤ U`, one into a method type ends at a method conjunct, and none
   leads into a recursive type (`LitTy.typInv`, `fnInv`, `bindInv`).  This is
   the only place a store invariant is read: for `vcLoc` through
   `RecordedLit`, for `vcLocAny` through the premise it carries, which forgets
   to a `LitTy` (`LitMatch.toLitTy`).
3. **The pack-count tower.**  Arbitrary evidence may contain concrete
   `selL`/`selR`.  `ObsInv G W k` inverts clean observations with fewer than `k`
   packings on the spine; given it, `LeTy.strengthenAt` turns evidence with
   `Forms.Le.PackBound k` into strong evidence, and `ObsInv.step` builds level
   `k+1`.  Undoing a packing substitutes the packed observation into a strong
   `bindx`/`bind1` premise; `LeTy.substB` records that the concrete selections
   this creates observe the location through that observation's spine, which
   has fewer than `k` packings, so level `k` strengthens the result.  This is
   the reference's `subst_aux`/`pre_canon_typ` circle (`dot_soundness.v:425,
   499`), with the pack count as its measure.

`EvB`/`LeTy.substB` at the top of the module are `SubstTyping.LeTy.substEv`
with that bound carried through every clause.

## What is not here

* Nothing about a stored method's **body**: `obsFun` finds the method
  conjunct of the location node's type and relates its annotations to the
  observed method type, and stops there.  Reading the conjunct back as the
  stored method and typing its body is the business of whoever owns the store
  invariant (`Preservation`'s `LocType.method` does it for a machine store).
* No statement about open inclusions beyond strengthening: transitivity is
  eliminated only in the empty local context, as in the reference.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst DmsHasType scopeUpTo varUpTo
  renameUpTo renameNil)

/-! ## Substitution that tracks concrete selections

`SubstTyping.LeTy.substEv` returns *some* evidence at the substituted types and
says nothing about its shape.  Transitivity elimination needs one fact about
that shape: how many packings the observation of a location carries, wherever a
selection on a location occurs.  Substituting a location for an abstract
variable is exactly what creates such selections — `selL (abs z) v` becomes
`selL (conc ℓ) v'`, and `v'` is the observation the substitution supplied for
`z`, extended by the spine of `v` — so the bound has to be threaded through the
substitution, not read off afterwards.

`EvB k` is `MonoSyn.Ev` whose observations satisfy `PackBound k` and, when
their subject is a location, have fewer than `k` packings on their spine.
`LeTy.substB`/`VcTy.substB` are `substEv` with the bound carried along: same
clauses, same helper lemmas, one more component in each result.  Keeping it a
separate theorem rather than a lemma about `substEv`'s output is deliberate:
`substEv`'s recursive calls go through `MonoSyn.Ev.lift` and `lemmaR`, whose
variable fields are built by tactic, and restating their evidence is more
fragile than rebuilding them with the bound in place. -/

/-- `MonoSyn.Ev` with a pack bound on the observation supplied for each
variable. -/
structure EvB {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} (k : Nat)
    (G : Store σ1 σ1) (W : StoreTy σ1) (Γ : Ctx σ1 s1) (m : MonoSyn θ)
    (G' : Store σ2 σ2) (W' : StoreTy σ2) (Γ' : Ctx σ2 s2) : Type where
  /-- The stored definitions agree at every location. -/
  defs : (l : BVar σ1 .var) →
      G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ)
  /-- The stored literals' types agree at every location. -/
  tys : (l : BVar σ1 .var) →
      tyOf W' (θ.conc l) = (tyOf W l).subst (Subst.atNil θ)
  /-- Observation evidence for the image of every abstract variable, bounded. -/
  vc : (x : BVar s1 .var) →
      Σ w : Vc σ2 (scopeAt (m.image (.abs x))),
        VcTy G' W' Γ' (m.image (.abs x)) w
          ((Γ.lookupAt x).subst (m.restrict (.abs x))) ×
        PLift (w.PackBound k ∧
          (zone (m.image (.abs x)) = .concrete → w.spinePacks < k))

namespace EvB

/-- Restricting to the empty local scope; the variable field is vacuous. -/
def atNil {k : Nat} {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : EvB k G W Γ m G' W' Γ') : EvB k G W .nil m.atNil G' W' .nil where
  defs := E.defs
  tys := E.tys
  vc := fun x => nomatch x

/-- Pushing under a binder: `MonoSyn.Ev.lift` with the bound carried.  At the
new binder the evidence is `vcVar`, which is bounded by anything and observes an
abstract variable; at an older binder it is the outer evidence, unchanged. -/
def lift {k : Nat} {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : EvB k G W Γ m G' W' Γ') (S : Ty σ1 (s1,x)) :
    EvB k G W (Γ.cons S) m.lift G' W' (Γ'.cons (S.subst θ.lift)) where
  defs := E.defs
  tys := E.tys
  vc := by
    intro y
    cases y with
    | here => exact ⟨.vcVar, .vcVar, ⟨trivial, fun h => nomatch h⟩⟩
    | there y =>
        have hy : Σ w : Vc σ2 (scopeAt ((m.atAbs y).image)),
            VcTy G' W' Γ' ((m.atAbs y).image) w
              ((Γ.lookupAt y).subst ((m.atAbs y).restrict)) ×
            PLift (w.PackBound k ∧
              (zone ((m.atAbs y).image) = .concrete → w.spinePacks < k)) := E.vc y
        revert hy
        show (Σ w : Vc σ2 (scopeAt ((m.atAbs y).image)),
                VcTy G' W' Γ' ((m.atAbs y).image) w
                  ((Γ.lookupAt y).subst ((m.atAbs y).restrict)) ×
                PLift (w.PackBound k ∧
                  (zone ((m.atAbs y).image) = .concrete → w.spinePacks < k))) →
            Σ w : Vc σ2 (scopeAt ((m.atAbs y).underLift.image)),
              VcTy G' W' (Γ'.cons (S.subst θ.lift)) ((m.atAbs y).underLift.image) w
                ((Γ.lookupAt y).subst ((m.atAbs y).underLift.restrict)) ×
              PLift (w.PackBound k ∧
                (zone ((m.atAbs y).underLift.image) = .concrete → w.spinePacks < k))
        cases m.atAbs y with
        | toAbs z r himg hstar hself hsyn =>
            exact fun hy => ⟨hy.1, VcTy.weakenVar (S.subst θ.lift) hy.2.1,
              ⟨hy.2.2.down.1, fun h => nomatch h⟩⟩
        | toConc l r himg hstar hself hsyn =>
            exact fun hy => ⟨hy.1, VcTy.ofLoc hy.2.1, hy.2.2⟩

end EvB

/-- `SubstTyping.VcTy.Descended` with the bound on the descended evidence. -/
structure VcTy.DescendedB {σ s : Sig} (k : Nat) (G : Store σ σ) (W : StoreTy σ)
    (Γ : Ctx σ s) (x : BVar s .var) (z : BVar (scopeUpTo x) .var)
    (T : Ty σ (scopeUpTo ((renameUpTo x).var z))) : Type where
  /-- The type, read in the prefix's scope. -/
  ty : Ty σ (scopeUpTo z)
  /-- It is the type it came from. -/
  hty : HEq ty T
  /-- The evidence, read in the prefix's scope. -/
  vc : Vc σ (scopeUpTo z)
  /-- Its derivation, over the truncated context. -/
  deriv : VcTy G W (Γ.upTo x) (.abs z) vc ty
  /-- It keeps the bound: descending never changes the evidence. -/
  bnd : vc.PackBound k

/-- `SubstTyping.VcTy.descendAbs` with the bound carried: strengthening does not
touch the evidence, so the bound it had is the bound it keeps. -/
def VcTy.descendAbsB {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {k : Nat} :
    {s : Sig} → (Γ : Ctx σ s) → (x : BVar s .var) →
    (z : BVar (scopeUpTo x) .var) →
    {w : Vc σ (scopeUpTo ((renameUpTo x).var z))} →
    {T : Ty σ (scopeUpTo ((renameUpTo x).var z))} →
    VcTy G W Γ (.abs ((renameUpTo x).var z)) w T → w.PackBound k →
    VcTy.DescendedB k G W Γ x z T
  | _, .cons _ _, .here, _, _, _, d, hb => ⟨_, HEq.rfl, _, d, hb⟩
  | _, .cons Γ0 _, .there x0, z, _, _, d, hb =>
      let r := VcTy.descendAbsB Γ0 x0 z (VcTy.strengthenCons d) hb
      ⟨r.ty, r.hty, r.vc, r.deriv, r.bnd⟩

/-- `SubstTyping.VcTy.descend` with the bound carried.  At a location the
evidence is literally unchanged, so its spine count is too. -/
def VcTy.descendB {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {k : Nat} (q : Vr σ s) (u : Vr σ (scopeAt q)) (p : Vr σ s)
    (hp : p = u.rename (renameAt q)) {w : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (d : VcTy G W Γ p w T)
    (hw : w.PackBound k ∧ (zone p = .concrete → w.spinePacks < k))
    (T' : Ty σ (scopeAt u)) (hT : HEq T' T) :
    Σ w' : Vc σ (scopeAt u), VcTy G W (ctxAt Γ q) u w' T' ×
      PLift (w'.PackBound k ∧ (zone u = .concrete → w'.spinePacks < k)) := by
  subst hp
  cases q with
  | conc l =>
      cases u with
      | conc l' =>
          refine ⟨w, ?_, ⟨hw⟩⟩
          rw [eq_of_heq hT]
          exact VcTy.ofLoc d
      | abs u0 => exact nomatch u0
  | abs x =>
      cases u with
      | conc l' =>
          refine ⟨w, ?_, ⟨hw⟩⟩
          rw [eq_of_heq hT]
          exact VcTy.ofLoc d
      | abs z =>
          have r := VcTy.descendAbsB Γ x z d hw.1
          refine ⟨r.vc, ?_, ⟨r.bnd, fun h => nomatch h⟩⟩
          rw [← eq_of_heq (r.hty.trans hT.symm)]
          exact r.deriv

/-- **Lemma R with the bound**: `SubstTyping.lemmaR` for `EvB`.  At a location
it is `EvB.atNil`; at an abstract subject the variable field is the outer one
descended into the prefix, which keeps its evidence and hence its bound. -/
def EvB.restrict {k : Nat} {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    {m : MonoSyn θ} {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : EvB k G W Γ m G' W' Γ') :
    (p : Vr σ1 s1) → EvB k G W (ctxAt Γ p) (m.resSyn p) G' W' (ctxAt Γ' (m.image p))
  | .conc _ => E.atNil
  | .abs x =>
      { defs := fun l => by
          rw [m.atNil_restrict (.abs x), m.restrict_conc (.abs x) l]
          exact E.defs l
        tys := fun l => by
          rw [m.atNil_restrict (.abs x), m.restrict_conc (.abs x) l]
          exact E.tys l
        vc := fun y =>
          VcTy.descendB (m.image (.abs x)) ((m.resSyn (.abs x)).image (.abs y))
            (m.image (.abs ((renameUpTo x).var y))) (m.image_restrict x y)
            (E.vc ((renameUpTo x).var y)).2.1 (E.vc ((renameUpTo x).var y)).2.2.down _
            (heq_ty_subst (scopeUpTo_renameUpTo x y).symm (m.scopeAt_image_restrict x y)
              (lookupAt_upTo Γ x y) (m.restrict_coh x y)) }

/-- Every variable is in one of the two zones. -/
theorem zone_cases {σ s : Sig} (p : Vr σ s) :
    zone p = .concrete ∨ zone p = .abstract := by
  cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

mutual

/-- **Inclusion evidence substituted, with its pack bound kept.**  The clauses
are `SubstTyping.LeTy.substEv`'s; the only new content is the `selL`/`selR`
clause, where the image of the subject may be a location and the observation
has to stay below the bound. -/
def LeTy.substB {k : Nat} {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {e : Le σ1 s1} {S T : Ty σ1 s1}
    (d : LeTy G W Γ e S T) (he : e.PackBound k) {σ2 s2 : Sig}
    {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ} {G' : Store σ2 σ2} {W' : StoreTy σ2}
    {Γ' : Ctx σ2 s2} (E : EvB k G W Γ m G' W' Γ') :
    Σ f : Le σ2 s2, LeTy G' W' Γ' f (S.subst θ) (T.subst θ) × PLift (f.PackBound k) :=
  match d, he with
  | .refl T0, _ => ⟨.refl _, .refl (T0.subst _), ⟨trivial⟩⟩
  | .top T0, _ => ⟨.top _, .top (T0.subst _), ⟨trivial⟩⟩
  | .bot T0, _ => ⟨.bot _, .bot (T0.subst _), ⟨trivial⟩⟩
  | .trans M d1 d2, he =>
      let r1 := LeTy.substB d1 he.1 E
      let r2 := LeTy.substB d2 he.2 E
      ⟨.trans (M.subst _) r1.1 r2.1, .trans _ r1.2.1 r2.2.1,
        ⟨r1.2.2.down, r2.2.2.down⟩⟩
  | .dtyp (l := l) d1 d2, he =>
      let r1 := LeTy.substB d1 he.1 E
      let r2 := LeTy.substB d2 he.2 E
      ⟨.dtyp l r1.1 r2.1, .dtyp r1.2.1 r2.2.1, ⟨r1.2.2.down, r2.2.2.down⟩⟩
  | .andI (T1 := T1) T2 d1 d2, he =>
      let r1 := LeTy.substB d1 he.1 E
      let r2 := LeTy.substB d2 he.2 E
      ⟨.andI _ _ r1.1 r2.1, .andI _ _ r1.2.1 r2.2.1, ⟨r1.2.2.down, r2.2.2.down⟩⟩
  | .andE1 T2 d1, he =>
      let r1 := LeTy.substB d1 he E
      ⟨.andE1 _ r1.1, .andE1 _ r1.2.1, ⟨r1.2.2.down⟩⟩
  | .andE2 T1 d1, he =>
      let r1 := LeTy.substB d1 he E
      ⟨.andE2 _ r1.1, .andE2 _ r1.2.1, ⟨r1.2.2.down⟩⟩
  | .orI1 T2 d1, he =>
      let r1 := LeTy.substB d1 he E
      ⟨.orI1 _ r1.1, .orI1 _ r1.2.1, ⟨r1.2.2.down⟩⟩
  | .orI2 T1 d1, he =>
      let r1 := LeTy.substB d1 he E
      ⟨.orI2 _ r1.1, .orI2 _ r1.2.1, ⟨r1.2.2.down⟩⟩
  | .orE S1 S2 d1 d2, he =>
      let r1 := LeTy.substB d1 he.1 E
      let r2 := LeTy.substB d2 he.2 E
      ⟨.orE _ _ r1.1 r2.1, .orE _ _ r1.2.1 r2.2.1, ⟨r1.2.2.down, r2.2.2.down⟩⟩
  | .dfun (l := l) (S2 := S2) d1 d2, he =>
      let r1 := LeTy.substB d1 he.1 E
      let r2 := LeTy.substB d2 he.2 (Ty.weaken_subst_lift S2 θ ▸ E.lift S2.weaken)
      ⟨.dfun l r1.1 r2.1, .dfun r1.2.1 r2.2.1, ⟨r1.2.2.down, r2.2.2.down⟩⟩
  | .bindx S0 T0 d1, he =>
      let r1 := LeTy.substB d1 he (E.lift S0)
      ⟨.bindx (S0.subst θ.lift) (T0.subst θ.lift) r1.1, .bindx _ _ r1.2.1, ⟨r1.2.2.down⟩⟩
  | .muDrop T0, _ =>
      ⟨.muDrop (T0.subst θ), by
        show LeTy _ _ _ (Le.muDrop (T0.subst θ))
          (Ty.TBind (T0.weaken.subst θ.lift)) (T0.subst θ)
        rw [Ty.weaken_subst_lift]
        exact .muDrop _, ⟨trivial⟩⟩
  | .defL (l := l) (a := a) (TX := TX) (T2 := T2) hget d1, he =>
      let r1 := LeTy.substB d1 he E.atNil
      ⟨.defL (θ.conc l) a r1.1, by
        show LeTy _ _ _ (Le.defL (θ.conc l) a _)
          (Ty.TSel (.conc (θ.conc l)) a) ((T2.rename renameNil).subst θ)
        rw [Ty.renameNil_subst]
        refine .defL ?_ r1.2.1
        rw [E.defs l, Dms.get?_subst, hget]
        rfl, ⟨r1.2.2.down⟩⟩
  | .defR (l := l) (a := a) (T1 := T1) (TX := TX) hget d1, he =>
      let r1 := LeTy.substB d1 he E.atNil
      ⟨.defR (θ.conc l) a r1.1, by
        show LeTy _ _ _ (Le.defR (θ.conc l) a _)
          ((T1.rename renameNil).subst θ) (Ty.TSel (.conc (θ.conc l)) a)
        rw [Ty.renameNil_subst]
        refine .defR ?_ r1.2.1
        rw [E.defs l, Dms.get?_subst, hget]
        rfl, ⟨r1.2.2.down⟩⟩
  | .selL (p := p) (a := a) (U := U) dv, he =>
      let r := VcTy.substB dv he.1 he.2 E
      ⟨.selL (m.image p) a r.1, by
        show LeTy _ _ _ (Le.selL (m.image p) a _)
          (Ty.TSel (p.subst θ) a) ((U.rename (renameAt p)).subst θ)
        rw [← m.image_eq p, m.star_ty p U]
        exact .selL r.2.1,
        ⟨r.2.2.down.1, fun hc => (zone_cases p).elim
          (fun hz => Nat.lt_of_le_of_lt (Nat.le_of_eq (r.2.2.down.2.1 hz)) (he.2 hz))
          (fun hz => r.2.2.down.2.2 hz hc)⟩⟩
  | .selR (p := p) (a := a) (S := S0) dv, he =>
      let r := VcTy.substB dv he.1 he.2 E
      ⟨.selR (m.image p) a r.1, by
        show LeTy _ _ _ (Le.selR (m.image p) a _)
          ((S0.rename (renameAt p)).subst θ) (Ty.TSel (p.subst θ) a)
        rw [← m.image_eq p, m.star_ty p S0]
        exact .selR r.2.1,
        ⟨r.2.2.down.1, fun hc => (zone_cases p).elim
          (fun hz => Nat.lt_of_le_of_lt (Nat.le_of_eq (r.2.2.down.2.1 hz)) (he.2 hz))
          (fun hz => r.2.2.down.2.2 hz hc)⟩⟩

/-- **Observation evidence substituted, with its pack bound kept.**  At a
location the spine count is unchanged, because substitution never touches a
location's spine; at an abstract subject whose image is a location the spine
is the supplied observation's, which `EvB` bounds. -/
def VcTy.substB {k : Nat} {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {p : Vr σ1 s1} {v : Vc σ1 (scopeAt p)}
    {T : Ty σ1 (scopeAt p)} (d : VcTy G W Γ p v T) (hv : v.PackBound k)
    (hp : zone p = .concrete → v.spinePacks < k)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : EvB k G W Γ m G' W' Γ') :
    Σ w : Vc σ2 (scopeAt (m.image p)),
      VcTy G' W' Γ' (m.image p) w (T.subst (m.restrict p)) ×
      PLift (w.PackBound k ∧ (zone p = .concrete → w.spinePacks = v.spinePacks) ∧
        (zone p = .abstract → zone (m.image p) = .concrete → w.spinePacks < k)) :=
  match d, hv, hp with
  | .vcVar (x := x), _, _ =>
      ⟨(E.vc x).1, (E.vc x).2.1,
        ⟨(E.vc x).2.2.down.1, (fun h => nomatch h), fun _ hc => (E.vc x).2.2.down.2 hc⟩⟩
  | .vcLoc (l := l), _, _ =>
      ⟨.vcLoc (θ.conc l), (E.tys l) ▸ VcTy.vcLoc,
        ⟨trivial, fun _ => rfl, fun h => nomatch h⟩⟩
  | .vcLocAny (l := l) (T := T0) h0, _, _ =>
      ⟨.vcLocAny (θ.conc l) (T0.subst (Subst.atNil θ).lift), by
        have h := VcTy.vcLocAny (G := G') (W := W') (Γ := Γ') (l := θ.conc l)
          (T := T0.renameStore (storeRen θ)) (by
            rw [← varyTy θ l T0]
            exact LitMatch.subst (Subst.atNil θ) (defs_get? θ (E.defs l)) h0)
        rw [← varyTy θ l T0, Ty.renameStore, ← atNil_lift_eq_ofStore] at h
        exact h, ⟨trivial, fun _ => rfl, fun h => nomatch h⟩⟩
  | .vcPack (l := l) (T := T0) dv, hv, hp =>
      let r := VcTy.substB dv hv (fun _ => Nat.lt_of_succ_lt (hp rfl)) E
      ⟨.vcPack (T0.subst (Subst.atNil θ).lift) r.1,
        .vcPack ((m.substVr_selfAt (.conc l) T0) ▸ r.2.1),
        ⟨r.2.2.down.1, fun _ => congrArg (· + 1) (r.2.2.down.2.1 rfl),
          fun h => nomatch h⟩⟩
  | .vcUnfold (p := p) (T := T0) dv, hv, hp =>
      let r := VcTy.substB dv hv hp E
      ⟨.vcUnfold (T0.subst (m.restrict p).lift) r.1, by
        rw [m.substVr_selfAt p T0]
        exact .vcUnfold r.2.1, ⟨r.2.2.down.1, r.2.2.down.2.1, r.2.2.down.2.2⟩⟩
  | .vcSub (p := p) T1 dv de, hv, hp =>
      let r := VcTy.substB dv hv.2 hp E
      let rl := LeTy.substB de hv.1 (E.restrict p)
      ⟨.vcSub (T1.subst (m.restrict p)) rl.1 r.1, .vcSub _ r.2.1 rl.2.1,
        ⟨⟨rl.2.2.down, r.2.2.down.1⟩, r.2.2.down.2.1, r.2.2.down.2.2⟩⟩

end

/-! ## Strong inclusions: composition, casts, weakening and narrowing -/

namespace SLe

/-- Reflexivity is strong. -/
def refl {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} (T : Ty σ s) :
    SLe G W Γ T T :=
  ⟨.refl T, .refl T, trivial⟩

/-- Strong inclusions compose by `trans`, and the composite is strong. -/
def trans {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {S M T : Ty σ s} (d1 : SLe G W Γ S M) (d2 : SLe G W Γ M T) : SLe G W Γ S T :=
  ⟨.trans M d1.ev d2.ev, .trans M d1.typed d2.typed, ⟨d1.strong, d2.strong⟩⟩

/-- Rewrite the left endpoint along an equation; the evidence is unchanged. -/
def castL {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {S S' T : Ty σ s} (h : S = S') (d : SLe G W Γ S T) : SLe G W Γ S' T :=
  h ▸ d

/-- Rewrite the right endpoint along an equation; the evidence is unchanged. -/
def castR {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {S T T' : Ty σ s} (h : T = T') (d : SLe G W Γ S T) : SLe G W Γ S T' :=
  h ▸ d

end SLe

/-- Rewrite the right endpoint of an inclusion derivation along an equation. -/
def LeTy.castR {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {e : Le σ s} {S T T' : Ty σ s} (h : T = T') (d : LeTy G W Γ e S T) :
    LeTy G W Γ e S T' :=
  h ▸ d

/-- Rewrite the left endpoint of an inclusion derivation along an equation. -/
def LeTy.castL {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {e : Le σ s} {S S' T : Ty σ s} (h : S = S') (d : LeTy G W Γ e S T) :
    LeTy G W Γ e S' T :=
  h ▸ d

/-- Rewrite the type of an observation along an equation; the evidence is
unchanged.  Stated as a function so that the equation is checked up to
definitional equality of the scope indices, which `rw` does not see through. -/
def VcTy.castT {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {p : Vr σ s} {v : Vc σ (scopeAt p)} {T T' : Ty σ (scopeAt p)} (h : T = T')
    (d : VcTy G W Γ p v T) : VcTy G W Γ p v T' :=
  h ▸ d

/-- A local renaming acts on the empty local scope as the identity: only its
store part survives, and that is the identity. -/
theorem atNil_ofRename {σ s1 s2 : Sig} (ρ : Rename s1 s2) :
    Subst.atNil (Subst.ofRename (σ := σ) ρ) = Subst.id (σ := σ) (s := []) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- Instantiating a binder acts on the empty local scope as the identity. -/
theorem atNil_one {σ s : Sig} (v : Vr σ s) :
    Subst.atNil (Subst.one v) = Subst.id (σ := σ) (s := []) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- The bounded hypothesis structure for weakening a closed inclusion under one
hypothesis.  There is no variable to supply, so the bound is free. -/
def EvB.weakenNil {k : Nat} {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (X : Ty σ ([],x)) :
    EvB k G W .nil (MonoSyn.weaken (σ := σ) (s := [])) G W (Ctx.nil.cons X) where
  defs := fun l => by
    show G.lookup l = (G.lookup l).subst (Subst.atNil (Subst.ofRename Rename.succ))
    rw [atNil_ofRename, Dms.subst_id]
  tys := fun l => by
    show tyOf W l = (tyOf W l).subst (Subst.atNil (Subst.ofRename Rename.succ))
    rw [atNil_ofRename, Ty.subst_id]
  vc := fun x => nomatch x

/-- **Weakening a strong closed inclusion** under one hypothesis keeps it
strong: `LeTy.substB` along the local weakening, at bound `0`. -/
def SLe.weaken {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {S T : Ty σ []}
    (X : Ty σ ([],x)) (d : SLe G W .nil S T) :
    SLe G W (Ctx.nil.cons X) S.weaken T.weaken :=
  let r := LeTy.substB d.typed d.strong (EvB.weakenNil (k := 0) X)
  ⟨r.1, r.2.1, r.2.2.down⟩

/-- The bounded hypothesis structure for narrowing the single hypothesis of a
one-variable context from `B` to `A`, given `A ≤ B` under `A`.  The variable is
observed by `vcSub A e vcVar`, an observation of an abstract variable, so no
concrete selection is created and the bound is `0`. -/
def EvB.narrow {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {A B : Ty σ ([],x)}
    (e : SLe G W (Ctx.nil.cons A) A B) :
    EvB 0 G W (Ctx.nil.cons B) (MonoSyn.id (σ := σ) (s := ([],x))) G W
      (Ctx.nil.cons A) where
  defs := fun l => by
    show G.lookup l = (G.lookup l).subst (Subst.atNil Subst.id)
    rw [MonoSyn.Ev.atNil_id, Dms.subst_id]
  tys := fun l => by
    show tyOf W l = (tyOf W l).subst (Subst.atNil Subst.id)
    rw [MonoSyn.Ev.atNil_id, Ty.subst_id]
  vc := fun y => match y with
    | .here => ⟨.vcSub A e.ev .vcVar,
        VcTy.castT (Γ := Ctx.nil.cons A) (p := .abs .here) (Ty.subst_id B).symm
          (VcTy.vcSub (σ := σ) (s := ([],x)) (G := G) (W := W) (Γ := Ctx.nil.cons A)
            (p := .abs .here) A .vcVar e.typed),
        ⟨⟨e.strong, trivial⟩, fun h => nomatch h⟩⟩
    | .there y => nomatch y

/-- **Narrowing a strong inclusion** in a one-variable context: the hypothesis
`B` may be replaced by any `A` with a strong `A ≤ B` under `A`.  This is the
reference's `stp_narrow0` (`dot.v:2067`), obtained here as an instance of the
bounded substitution theorem at the identity. -/
def SLe.narrow {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {A B X Y : Ty σ ([],x)}
    (d : SLe G W (Ctx.nil.cons B) X Y) (e : SLe G W (Ctx.nil.cons A) A B) :
    SLe G W (Ctx.nil.cons A) X Y :=
  match LeTy.substB d.typed d.strong (EvB.narrow e) with
  | ⟨f, hf, hb⟩ =>
      ⟨f, LeTy.castL (Ty.subst_id X) (LeTy.castR (Ty.subst_id Y) hf), hb.down⟩

/-- A closed selection is on a location, so strong evidence has no `selL`. -/
theorem Le.selL_not_strong {σ : Sig} {a : Lb} :
    (p : Vr σ []) → (v : Vc σ (scopeAt p)) → ¬ (Le.selL p a v).Strong
  | .abs x, _ => nomatch x
  | .conc _, _ => fun h => Nat.not_lt_zero _ (h.2 rfl)

/-- A closed selection is on a location, so strong evidence has no `selR`. -/
theorem Le.selR_not_strong {σ : Sig} {a : Lb} :
    (p : Vr σ []) → (v : Vc σ (scopeAt p)) → ¬ (Le.selR p a v).Strong
  | .abs x, _ => nomatch x
  | .conc _, _ => fun h => Nat.not_lt_zero _ (h.2 rfl)

/-! ## Normal forms: reflexivity, soundness, and transitivity elimination

`Forms.LeNf` is the normal-form datatype; it is intrinsically typed, so its
`FormTyped` soundness is the map back to strong evidence, `LeNf.toSLe`.
Transitivity is eliminated by `LeTy.pushback`, the reference's
`stp_trans_pushback_aux` (`dot_soundness.v:140`): a strong closed inclusion
followed by a normal form is a normal form.  The recursion is structural on the
strong derivation.  Its only non-structural ingredients are `SLe.narrow`, used
at exactly the three places the reference narrows (`dot_soundness.v:175, 189,
195`: method against method, and `bindx` against `bind1`/`bindx`), and
`SLe.weaken`, used for `dfun`'s domain and for `muDrop`. -/

/-- Every closed type has a normal form of reflexivity.  Not a recursion: the
premises of every form are strong inclusions, and reflexivity is one. -/
def LeNf.refl {σ : Sig} {G : Store σ σ} {W : StoreTy σ} : (T : Ty σ []) → LeNf G W T T
  | .TBot => .head (.bot _)
  | .TTop => .top _
  | .TFun _ S U => .head (.fn (SLe.refl S) (SLe.refl U))
  | .TTyp _ S U => .head (.typ (SLe.refl S) (SLe.refl U))
  | .TSel p a => .head (.selx p a)
  | .TBind T => .head (.bindx (SLe.refl T))
  | .TAnd A B => .and2 ⟨.andE1 B (.refl A), .andE1 B (.refl A), trivial⟩
      ⟨.andE2 A (.refl B), .andE2 A (.refl B), trivial⟩
  | .TOr A B => .head (.or1 (.or21 (SLe.refl A)) (.or22 (SLe.refl B)))

mutual

/-- **Soundness of normal forms**: every normal form is a strong closed
inclusion between its endpoints. -/
def LeNf.toSLe {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {T1 T2 : Ty σ []} → LeNf G W T1 T2 → SLe G W .nil T1 T2
  | _, _, .top T => ⟨.top T, .top T, trivial⟩
  | _, _, .and2 s1 s2 =>
      ⟨.andI _ _ s1.ev s2.ev, .andI _ _ s1.typed s2.typed, ⟨s1.strong, s2.strong⟩⟩
  | _, _, .or21 s => ⟨.orI1 _ s.ev, .orI1 _ s.typed, s.strong⟩
  | _, _, .or22 s => ⟨.orI2 _ s.ev, .orI2 _ s.typed, s.strong⟩
  | _, _, .sel2 hg s =>
      SLe.castL (Ty.rename_renameNil_nil _) ⟨.defR _ _ s.ev, .defR hg s.typed, s.strong⟩
  | _, _, .head h => LeNfHead.toSLe h

/-- Soundness of the left-headed normal forms. -/
def LeNfHead.toSLe {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {T1 T2 : Ty σ []} → LeNfHead G W T1 T2 → SLe G W .nil T1 T2
  | _, _, .bot T => ⟨.bot T, .bot T, trivial⟩
  | _, _, .fn s1 s2 =>
      ⟨.dfun _ s1.ev s2.ev, .dfun s1.typed s2.typed, ⟨s1.strong, s2.strong⟩⟩
  | _, _, .typ s1 s2 =>
      ⟨.dtyp _ s1.ev s2.ev, .dtyp s1.typed s2.typed, ⟨s1.strong, s2.strong⟩⟩
  | _, _, .sel1 hg n =>
      let r := LeNf.toSLe n
      SLe.castR (Ty.rename_renameNil_nil _) ⟨.defL _ _ r.ev, .defL hg r.typed, r.strong⟩
  | _, _, .selx _ _ => SLe.refl _
  | _, _, .bind1 (T1 := T1) (T2 := T2) s =>
      ⟨.trans (.TBind T2.weaken) (.bindx T1 T2.weaken s.ev) (.muDrop T2),
        .trans _ (.bindx _ _ s.typed) (.muDrop T2), ⟨s.strong, trivial⟩⟩
  | _, _, .bindx s => ⟨.bindx _ _ s.ev, .bindx _ _ s.typed, s.strong⟩
  | _, _, .and11 n =>
      let r := LeNf.toSLe n
      ⟨.andE1 _ r.ev, .andE1 _ r.typed, r.strong⟩
  | _, _, .and12 n =>
      let r := LeNf.toSLe n
      ⟨.andE2 _ r.ev, .andE2 _ r.typed, r.strong⟩
  | _, _, .or1 n1 n2 =>
      let r1 := LeNf.toSLe n1
      let r2 := LeNf.toSLe n2
      ⟨.orE _ _ r1.ev r2.ev, .orE _ _ r1.typed r2.typed, ⟨r1.strong, r2.strong⟩⟩

end

/-- The normal forms decided by the right head absorb a strong inclusion on
their left, by one `trans` into their premises; a form decided by the left head
is handed back for inspection.  This is the half of `Form.combine` that needs
no recursion. -/
def LeNf.precompose {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {T1 T2 T3 : Ty σ []}
    (s : SLe G W .nil T1 T2) : LeNf G W T2 T3 → LeNf G W T1 T3 ⊕ LeNfHead G W T2 T3
  | .top _ => .inl (.top _)
  | .and2 s1 s2 => .inl (.and2 (s.trans s1) (s.trans s2))
  | .or21 s1 => .inl (.or21 (s.trans s1))
  | .or22 s2 => .inl (.or22 (s.trans s2))
  | .sel2 hg s1 => .inl (.sel2 hg (s.trans s1))
  | .head h => .inr h

/-- Rewrite the left endpoint of a left-headed normal form. -/
def LeNfHead.castL {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {S S' T : Ty σ []}
    (h : S = S') (n : LeNfHead G W S T) : LeNfHead G W S' T :=
  h ▸ n

/-- Rewrite the left endpoint of a normal form. -/
def LeNf.castL {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {S S' T : Ty σ []}
    (h : S = S') (n : LeNf G W S T) : LeNf G W S' T :=
  h ▸ n

/-- **Transitivity elimination at a left-headed form.**  A strong closed
inclusion `T1 ≤ T2` followed by a form decided by the head of `T2` is a normal
form `T1 ≤ T3`.  Structural recursion on the strong derivation; `trans` is
eliminated by two recursive calls, the congruences compose their premises, and
the recursive formers `bindx`/`dfun` compose under their binder after
narrowing.  The two concrete selection rules cannot occur: the evidence is
strong. -/
def LeTy.pushbackHead {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {e : Le σ []} → {T1 T2 T3 : Ty σ []} →
    LeTy G W .nil e T1 T2 → e.Strong → LeNfHead G W T2 T3 → LeNf G W T1 T3
  | _, _, _, _, .refl _, _, h => .head h
  | _, _, _, _, .trans _ d1 d2, hs, h =>
      match LeNf.precompose ⟨_, d1, hs.1⟩ (LeTy.pushbackHead d2 hs.2 h) with
      | .inl r => r
      | .inr h1 => LeTy.pushbackHead d1 hs.1 h1
  | _, _, _, _, .top _, _, h => nomatch h
  | _, _, _, _, .bot _, _, _ => .head (.bot _)
  | _, _, _, _, .dtyp d1 d2, hs, .typ s1 s2 =>
      .head (.typ (s1.trans ⟨_, d1, hs.1⟩) (SLe.trans ⟨_, d2, hs.2⟩ s2))
  | _, _, _, _, .dfun d1 d2, hs, .fn s1 s2 =>
      .head (.fn (s1.trans ⟨_, d1, hs.1⟩)
        ((SLe.narrow ⟨_, d2, hs.2⟩ (s1.weaken _)).trans s2))
  | _, _, _, _, .andI _ _ d1 _, hs, .and11 n1 =>
      match LeNf.precompose ⟨_, d1, hs.1⟩ n1 with
      | .inl r => r
      | .inr h1 => LeTy.pushbackHead d1 hs.1 h1
  | _, _, _, _, .andI _ _ _ d2, hs, .and12 n2 =>
      match LeNf.precompose ⟨_, d2, hs.2⟩ n2 with
      | .inl r => r
      | .inr h2 => LeTy.pushbackHead d2 hs.2 h2
  | _, _, _, _, .andE1 _ d1, hs, h => .head (.and11 (LeTy.pushbackHead d1 hs h))
  | _, _, _, _, .andE2 _ d1, hs, h => .head (.and12 (LeTy.pushbackHead d1 hs h))
  | _, _, _, _, .orI1 _ d1, hs, .or1 n1 _ =>
      match LeNf.precompose ⟨_, d1, hs⟩ n1 with
      | .inl r => r
      | .inr h1 => LeTy.pushbackHead d1 hs h1
  | _, _, _, _, .orI2 _ d1, hs, .or1 _ n2 =>
      match LeNf.precompose ⟨_, d1, hs⟩ n2 with
      | .inl r => r
      | .inr h2 => LeTy.pushbackHead d1 hs h2
  | _, _, _, _, .orE _ _ d1 d2, hs, h =>
      .head (.or1 (LeTy.pushbackHead d1 hs.1 h) (LeTy.pushbackHead d2 hs.2 h))
  | _, _, _, _, .defL (T2 := T2) hg d1, hs, h =>
      .head (.sel1 hg (LeTy.pushbackHead d1 hs
        (LeNfHead.castL (Ty.rename_renameNil_nil T2) h)))
  | _, _, _, _, .defR (T1 := T1) hg d1, hs, .sel1 hg' n1 =>
      LeNf.castL (Ty.rename_renameNil_nil T1).symm (by
        rw [hg] at hg'
        simp only [Option.some.injEq, Dm.dty.injEq] at hg'
        subst hg'
        exact match LeNf.precompose ⟨_, d1, hs⟩ n1 with
          | .inl r => r
          | .inr h1 => LeTy.pushbackHead d1 hs h1)
  | _, _, _, _, .defR (T1 := T1) hg d1, hs, .selx _ _ =>
      LeNf.castL (Ty.rename_renameNil_nil T1).symm (.sel2 hg ⟨_, d1, hs⟩)
  | _, _, _, _, .selL (p := p) (v := v) _, hs, _ => absurd hs (Le.selL_not_strong p v)
  | _, _, _, _, .selR (p := p) (v := v) _, hs, _ => absurd hs (Le.selR_not_strong p v)
  | _, _, _, _, .bindx _ _ d1, hs, .bind1 s =>
      .head (.bind1 (SLe.trans ⟨_, d1, hs⟩ (s.narrow ⟨_, d1, hs⟩)))
  | _, _, _, _, .bindx _ _ d1, hs, .bindx s =>
      .head (.bindx (SLe.trans ⟨_, d1, hs⟩ (s.narrow ⟨_, d1, hs⟩)))
  | _, _, _, _, .muDrop T, _, h =>
      .head (.bind1 ((LeNf.head h).toSLe.weaken T.weaken))

/-- **Transitivity elimination**: a strong closed inclusion followed by any
normal form is a normal form. -/
def LeTy.pushback {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {e : Le σ []}
    {T1 T2 T3 : Ty σ []} (d : LeTy G W .nil e T1 T2) (hs : e.Strong)
    (n : LeNf G W T2 T3) : LeNf G W T1 T3 :=
  match LeNf.precompose ⟨_, d, hs⟩ n with
  | .inl r => r
  | .inr h => LeTy.pushbackHead d hs h

/-- **The normalizer for strong closed evidence.**  Every strong closed
inclusion has a normal form, with no hypothesis on the store. -/
def SLe.nf {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {S T : Ty σ []}
    (d : SLe G W .nil S T) : LeNf G W S T :=
  LeTy.pushback d.typed d.strong (LeNf.refl T)

/-! ## A stored literal's type, inverted

The base of every observation spine at a location is the type of its stored
literal — `tyOf W ℓ` for `vcLoc`, a self type `T.substVr ℓ` that matches the
stored literal for `vcLocAny` — and both `DmsHasType` and `LitMatch` conclude
only at `⊤` or a right-nested intersection of members whose type members are
exact (`D_Typ`).  `LitTy g B` names that shape, relative to a member lookup `g`
(the stored literal's `Dms.get?`): each type member is exact and is what `g`
finds at its label.  It is `LitMatch` with the method annotations forgotten
(`LitMatch.toLitTy`).
Out of such a type, a normal form into a type member is a chain of
`and11`/`and12` ending in the congruence `typ`, whose bounds are the stored
definition; into a method type it ends in the congruence `fn` at a method
conjunct; and into a recursive type there is none.

`LitTy` is the only thing the rest of the module asks of the store:
`RecordedLit G W` says the store typing records a literal type at every
location.  `Store.Honest` gives it (`Store.Honest.recordedLit`), and so can any
other invariant that types the stored literals — a machine store's, say — by
proving the same shape. -/

/-- **The type of a stored literal**, relative to its member lookup `g`: `⊤`, or
an intersection of a member with the type of the rest.  A type member is exact
and is what `g` finds at its label; a method member is recorded by its type
only. -/
inductive LitTy {σ : Sig} (g : Lb → Option (Dm σ [])) : Ty σ [] → Type where
  /-- The empty literal's type. -/
  | top : LitTy g .TTop
  /-- A type member, exact, found by `g` at its label. -/
  | typ {b : Lb} {TX B : Ty σ []} :
      g b = some (.dty TX) → LitTy g B → LitTy g (.TAnd (.TTyp b TX TX) B)
  /-- A method member. -/
  | fn {b : Lb} {S : Ty σ []} {U : Ty σ ([],x)} {B : Ty σ []} :
      LitTy g B → LitTy g (.TAnd (.TFun b S U) B)

/-- **The location rules' premise gives a literal type**: a type that matches
the stored literal has its shape, the method annotations forgotten. -/
def LitMatch.toLitTy {σ : Sig} {g : Lb → Option (Dm σ [])} :
    {B : Ty σ []} → LitMatch g B → LitTy g B
  | _, .top => .top
  | _, .typ h r => .typ h r.toLitTy
  | _, .fn _ r => .fn r.toLitTy

/-- **A literal type into a type member** reads the stored definition: a normal
form `B ≤ {a : S..U}` out of a literal type finds `dty TX` at `a` together with
strong `S ≤ TX` and `TX ≤ U`. -/
def LitTy.typInv {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {g : Lb → Option (Dm σ [])}
    {a : Lb} {S U : Ty σ []} : {B : Ty σ []} → LitTy g B →
    LeNf G W B (.TTyp a S U) →
    (TX : Ty σ []) × PLift (g a = some (.dty TX)) × SLe G W .nil S TX ×
      SLe G W .nil TX U
  | _, .top, n => by
      cases n with
      | head h => cases h
  | _, .typ (b := b) (TX := TX) (B := B) hg rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 =>
                  cases h1 with
                  | typ s1 s2 => exact ⟨TX, ⟨hg⟩, s1, s2⟩
          | and12 n2 => exact LitTy.typInv rest n2
  | _, .fn (b := b) (S := S1) (U := U1) (B := B) rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 => cases h1
          | and12 n2 => exact LitTy.typInv rest n2

/-- **A literal type is never below a recursive type.**  No normal form relates
`⊤`, a type member or a method member to `μT`. -/
theorem LitTy.bindInv {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {g : Lb → Option (Dm σ [])} {T : Ty σ ([],x)} : {B : Ty σ []} → LitTy g B →
    LeNf G W B (.TBind T) → False
  | _, .top, n => by
      cases n with
      | head h => cases h
  | _, .typ (b := b) (TX := TX) (B := B) _ rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 => cases h1
          | and12 n2 => exact LitTy.bindInv rest n2
  | _, .fn (b := b) (S := S1) (U := U1) (B := B) rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 => cases h1
          | and12 n2 => exact LitTy.bindInv rest n2

/-- **A literal type into a method type** finds a method conjunct at the same
label, related to the target by strong inclusions: the domain contravariantly,
the codomain under the parameter at the target's domain — `stp_fun`'s shape. -/
def LitTy.fnInv {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {g : Lb → Option (Dm σ [])}
    {a : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)} : {B : Ty σ []} → LitTy g B →
    LeNf G W B (.TFun a S0 U0) →
    (S : Ty σ []) × (U : Ty σ ([],x)) × Conjunct B (.TFun a S U) ×
      SLe G W .nil S0 S × SLe G W (Ctx.nil.cons S0.weaken) U U0
  | _, .top, n => by
      cases n with
      | head h => cases h
  | _, .typ (b := b) (TX := TX) (B := B) _ rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 => cases h1
          | and12 n2 =>
              let r := LitTy.fnInv rest n2
              exact ⟨r.1, r.2.1, .there r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩
  | _, .fn (b := b) (S := S1) (U := U1) (B := B) rest, n => by
      cases n with
      | head h =>
          cases h with
          | and11 n1 =>
              cases n1 with
              | head h1 =>
                  cases h1 with
                  | fn s1 s2 => exact ⟨S1, U1, .here, s1, s2⟩
          | and12 n2 =>
              let r := LitTy.fnInv rest n2
              exact ⟨r.1, r.2.1, .there r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩

/-- **A typed definition list has a literal type**, under any substitution `θ`
into the empty scope and relative to any lookup `g` that finds every member of
the list, substituted.  The shape `StoreTyping.dmsLitMatch` proves, without its
method case: a literal type records a method by its type only, so no annotation
is asked for, and the list need not be annotated. -/
def dmsLitTy {σ s1 : Sig} {G : Store σ σ} {Γ : Ctx σ s1} (θ : Subst σ s1 σ [])
    (g : Lb → Option (Dm σ [])) :
    {ds : Dms σ s1} → {T : Ty σ s1} → DmsHasType G Γ ds T →
    (∀ a d, ds.get? a = some d → g a = some (d.subst θ)) → LitTy g (T.subst θ)
  | _, _, .D_Nil, _ => .top
  | _, _, .D_Typ (ds := ds) (T11 := T11) hds, hg =>
      .typ (hg ds.length (.dty T11) (dms_get?_head _ ds))
        (dmsLitTy θ g hds (fun a d h => hg a d (dms_get?_tail _ h)))
  | _, _, .D_Fun hds _ _ _, hg =>
      .fn (dmsLitTy θ g hds (fun a d h => hg a d (dms_get?_tail _ h)))

/-- **A `T_Vary` witness gives a literal type**: a literal typed at `T` under its
own self, instantiating to what `ℓ` stores, has type `T[ℓ]` of literal shape
relative to the stored lookup.  No store invariant is used;
`Store.Honest.recordedLit` applies it to the honesty witness at each
location. -/
def varyLitTy {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) :
    LitTy (G.lookup l).get? (T.substVr (.conc l)) :=
  dmsLitTy (Subst.one (.conc l)) _ hd (fun a d h => by
    rw [← hs, Dms.get?_subst, h]; rfl)

/-- **A target definition list's type is a literal type** relative to any lookup
that finds each of its type-member conjuncts.  `DefsTy` concludes at the same
three shapes as `DmsHasType`, so this is `dmsLitTy` for the target's own
definitions; the lookup condition is stated on conjuncts, so the positional
reasoning is left to whoever relates the lookup to the list.  This is the entry
point for a store invariant phrased with `DefsTy`, such as a machine store's. -/
def defsLitTy {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ []}
    (g : Lb → Option (Dm σ [])) : {ds : Defs σ []} → {T : Ty σ []} →
    DefsTy G W Γ ds T →
    (∀ {a : Lb} {TX : Ty σ []}, Conjunct T (.TTyp a TX TX) → g a = some (.dty TX)) →
    LitTy g T
  | _, _, .dnil, _ => .top
  | _, _, .dty hds, hg => .typ (hg .here) (defsLitTy g hds (fun c => hg (.there c)))
  | _, _, .dfun hds _, hg => .fn (defsLitTy g hds (fun c => hg (.there c)))

/-- **The store typing records literal types**: at every location, the recorded
type is a literal type relative to what the store holds there.  This is all the
inversion below asks of the store. -/
abbrev RecordedLit {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type :=
  (l : BVar σ .var) → LitTy (G.lookup l).get? (tyOf W l)

/-- **An honest store records literal types**: the honesty witness at each
location is a `T_Vary` witness at the recorded type. -/
def Store.Honest.recordedLit {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hG : Store.Honest G W) : RecordedLit G W :=
  fun l => varyLitTy (hG.at' l).typed (hG.at' l).stored

/-- The type a location node of an observation spine reports: the recorded one
(`vcLoc`), or a self type that matches the stored literal (`vcLocAny`).  Kept
as data so that a consumer can read a conjunct of it back as a stored
member. -/
inductive LocBase {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var) :
    Ty σ [] → Type where
  /-- `vcLoc`'s: the store typing's entry. -/
  | recorded : LocBase G W l (tyOf W l)
  /-- `vcLocAny`'s: a self type, instantiated at the location, with the match
  that is the rule's premise. -/
  | witness {T : Ty σ ([],x)} :
      LitMatch (G.lookup l).get? (T.substVr (.conc l)) →
      LocBase G W l (T.substVr (.conc l))

/-! ## Substituting a location for the self of a recursive form

The premise of a `bindx`/`bind1` normal form lives under the self hypothesis
`z : T`.  Instantiating `z` by a location `ℓ` observed at `T[ℓ]` is one
`MonoSyn.oneConc` substitution, whose hypothesis structure is that observation.
Two versions: the plain one for `SubstTyping.LeTy.substEv`, and the bounded one
for `LeTy.substB`, which records that every concrete selection the substitution
creates observes `ℓ` through the supplied observation's spine. -/

/-- The hypothesis structure of the machine's substitution, at a given
observation of the location. -/
def MonoSyn.Ev.oneConc {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {l : BVar σ .var} {T : Ty σ ([],x)} {w : Vc σ []}
    (dw : VcTy G W .nil (.conc l) w (T.substVr (.conc l))) :
    MonoSyn.Ev G W (Ctx.nil.cons T) (MonoSyn.oneConc l) G W .nil where
  defs := fun l0 => by
    show G.lookup l0 = (G.lookup l0).subst (Subst.atNil (Subst.one (.conc l)))
    rw [atNil_one, Dms.subst_id]
  tys := fun l0 => by
    show tyOf W l0 = (tyOf W l0).subst (Subst.atNil (Subst.one (.conc l)))
    rw [atNil_one, Ty.subst_id]
  vc := fun y => match y with
    | .here => ⟨w, dw⟩
    | .there y => nomatch y

/-- The bounded hypothesis structure of the machine's substitution: the supplied
observation satisfies the bound and has fewer than `k` packings on its spine. -/
def EvB.oneConc {k : Nat} {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {l : BVar σ .var} {T : Ty σ ([],x)} {w : Vc σ []}
    (dw : VcTy G W .nil (.conc l) w (T.substVr (.conc l))) (hw : w.PackBound k)
    (hk : w.spinePacks < k) :
    EvB k G W (Ctx.nil.cons T) (MonoSyn.oneConc l) G W .nil where
  defs := (MonoSyn.Ev.oneConc dw).defs
  tys := (MonoSyn.Ev.oneConc dw).tys
  vc := fun y => match y with
    | .here => ⟨w, dw, ⟨hw, fun _ => hk⟩⟩
    | .there y => nomatch y

/-! ## The pack-count tower

Arbitrary evidence may select on a location through an observation
(`selL`/`selR` at `conc ℓ`), which strong evidence may not.  Turning the first
into the second needs the observation inverted to the stored definition, and
inverting an observation needs its recursive steps undone, which substitutes a
location into a `bindx`/`bind1` premise — creating new concrete selections.
The reference breaks this circle with the pack count of `htpy`
(`dot_soundness.v:215`, `subst_aux` at `:499`); so does this section.

`ObsInv G W k` is observation inversion for **clean** observations (every
inclusion on the spine strong) with fewer than `k` packings on the spine, below
a recursive type, a type member and a method type.  Given it:

* `LeTy.strengthenAt` turns evidence with `PackBound k` into strong evidence:
  a concrete selection's observation has fewer than `k` packings, so after its
  own inclusions are strengthened (`VcTy.cleanAt`) `ObsInv` inverts it, and the
  selection becomes `defL`/`defR` at the stored definition.
* `ObsInv.step` builds `ObsInv G W (k+1)`.  Undoing a `vcPack` over a clean
  observation `w` with `w.spinePacks < k` substitutes `w` into a strong premise;
  by `LeTy.substB` the result has `PackBound k`, so `strengthenAt` at level `k`
  makes it strong again, and the observation that remains has fewer packings.

Level `0` is vacuous, so every level exists (`RecordedLit.obsInv`), and every
piece of evidence has *some* pack bound (`Le.packBound_of_packs`).  Only the
base cases of the observation inversion read the store, through `LitTy`: for
`vcLoc` by `RecordedLit`, for `vcLocAny` by its own premise
(`LitMatch.toLitTy`). -/

/-- What a clean closed observation of `ℓ` below a method type `{a : S0 → U0}`
inverts to: the type its location node reports, a method conjunct of that type
at the same label, and strong inclusions relating the conjunct to the observed
method type as `stp_fun` does. -/
structure ObsFun {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var)
    (a : Lb) (S0 : Ty σ []) (U0 : Ty σ ([],x)) : Type where
  /-- The type the spine's location node reports … -/
  base : Ty σ []
  /-- … as one of the two location nodes reports it. -/
  baseOf : LocBase G W l base
  /-- The method conjunct's domain … -/
  S : Ty σ []
  /-- … and codomain. -/
  U : Ty σ ([],x)
  /-- The conjunct. -/
  conj : Conjunct base (.TFun a S U)
  /-- The observed domain is included in the conjunct's. -/
  dom : SLe G W .nil S0 S
  /-- The conjunct's codomain is included in the observed one, under the
  parameter at the observed domain. -/
  cod : SLe G W (Ctx.nil.cons S0.weaken) U U0

/-- Observation inversion for clean closed observations of a location with
fewer than `k` packings on the spine: out of a recursive type the opened body
is observed with strictly fewer packings, out of a type member the stored
definition is found with strong bounds, and out of a method type a method
conjunct of the location node's type is found. -/
structure ObsInv {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (k : Nat) : Type where
  /-- A clean observation below a recursive type unfolds, losing a packing. -/
  bind : ∀ {l : BVar σ .var} {T0 : Ty σ []} {T : Ty σ ([],x)} {v : Vc σ []},
    VcTy G W .nil (.conc l) v T0 → v.Strong → v.spinePacks < k →
    SLe G W .nil T0 (.TBind T) →
    (u : Vc σ []) × VcTy G W .nil (.conc l) u (T.substVr (.conc l)) ×
      PLift (u.Strong ∧ u.spinePacks < v.spinePacks)
  /-- A clean observation below a type member reads the stored definition. -/
  typ : ∀ {l : BVar σ .var} {T0 : Ty σ []} {a : Lb} {S U : Ty σ []} {v : Vc σ []},
    VcTy G W .nil (.conc l) v T0 → v.Strong → v.spinePacks < k →
    SLe G W .nil T0 (.TTyp a S U) →
    (TX : Ty σ []) × PLift ((G.lookup l).get? a = some (.dty TX)) ×
      SLe G W .nil S TX × SLe G W .nil TX U
  /-- A clean observation below a method type finds a method conjunct. -/
  fn : ∀ {l : BVar σ .var} {T0 : Ty σ []} {a : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)}
    {v : Vc σ []},
    VcTy G W .nil (.conc l) v T0 → v.Strong → v.spinePacks < k →
    SLe G W .nil T0 (.TFun a S0 U0) → ObsFun G W l a S0 U0

/-- Level `0` is vacuous: no spine has fewer than zero packings. -/
def ObsInv.zero {σ : Sig} {G : Store σ σ} {W : StoreTy σ} : ObsInv G W 0 where
  bind := fun _ _ hk _ => absurd hk (Nat.not_lt_zero _)
  typ := fun _ _ hk _ => absurd hk (Nat.not_lt_zero _)
  fn := fun _ _ hk _ => absurd hk (Nat.not_lt_zero _)

/-- A selection on either zone, made strong.  At an abstract subject the clean
observation is kept; at a location it is inverted by `ObsInv` and the selection
becomes `defL` at the stored definition. -/
def selLStrong {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {k : Nat} (O : ObsInv G W k) {a : Lb} :
    (p : Vr σ s) → {U : Ty σ (scopeAt p)} → (w : Vc σ (scopeAt p)) →
    VcTy G W Γ p w (.TTyp a .TBot U) → w.Strong →
    (zone p = .concrete → w.spinePacks < k) →
    SLe G W Γ (.TSel p a) (U.rename (renameAt p))
  | .abs _, _, w, dw, hw, _ => ⟨.selL _ a w, .selL dw, ⟨hw, fun h => nomatch h⟩⟩
  | .conc l, _, _, dw, hw, hk =>
      match O.typ (VcTy.ofLoc (Γ' := .nil) dw) hw (hk rfl) (SLe.refl _) with
      | ⟨_, hg, _, sU⟩ => ⟨.defL l a sU.ev, .defL hg.down sU.typed, sU.strong⟩

/-- The `selR` counterpart of `selLStrong`: at a location the selection becomes
`defR` at the stored definition. -/
def selRStrong {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {k : Nat} (O : ObsInv G W k) {a : Lb} :
    (p : Vr σ s) → {S : Ty σ (scopeAt p)} → (w : Vc σ (scopeAt p)) →
    VcTy G W Γ p w (.TTyp a S .TTop) → w.Strong →
    (zone p = .concrete → w.spinePacks < k) →
    SLe G W Γ (S.rename (renameAt p)) (.TSel p a)
  | .abs _, _, w, dw, hw, _ => ⟨.selR _ a w, .selR dw, ⟨hw, fun h => nomatch h⟩⟩
  | .conc l, _, _, dw, hw, hk =>
      match O.typ (VcTy.ofLoc (Γ' := .nil) dw) hw (hk rfl) (SLe.refl _) with
      | ⟨_, hg, sS, _⟩ => ⟨.defR l a sS.ev, .defR hg.down sS.typed, sS.strong⟩

mutual

/-- **Strengthening.**  Evidence with pack bound `k`, in any context, is
replaced by strong evidence between the same types, given observation inversion
below `k`.  Every rule is kept except a concrete selection, which becomes
`defL`/`defR`. -/
def LeTy.strengthenAt {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {k : Nat}
    (O : ObsInv G W k) : {s : Sig} → {Γ : Ctx σ s} → {e : Le σ s} →
    {S T : Ty σ s} → LeTy G W Γ e S T → e.PackBound k → SLe G W Γ S T
  | _, _, _, _, _, .refl T0, _ => SLe.refl T0
  | _, _, _, _, _, .top T0, _ => ⟨_, .top T0, trivial⟩
  | _, _, _, _, _, .bot T0, _ => ⟨_, .bot T0, trivial⟩
  | _, _, _, _, _, .muDrop T0, _ => ⟨_, .muDrop T0, trivial⟩
  | _, _, _, _, _, .trans _ d1 d2, he =>
      SLe.trans (LeTy.strengthenAt O d1 he.1) (LeTy.strengthenAt O d2 he.2)
  | _, _, _, _, _, .dtyp d1 d2, he =>
      let r1 := LeTy.strengthenAt O d1 he.1
      let r2 := LeTy.strengthenAt O d2 he.2
      ⟨.dtyp _ r1.ev r2.ev, .dtyp r1.typed r2.typed, ⟨r1.strong, r2.strong⟩⟩
  | _, _, _, _, _, .dfun d1 d2, he =>
      let r1 := LeTy.strengthenAt O d1 he.1
      let r2 := LeTy.strengthenAt O d2 he.2
      ⟨.dfun _ r1.ev r2.ev, .dfun r1.typed r2.typed, ⟨r1.strong, r2.strong⟩⟩
  | _, _, _, _, _, .andI _ _ d1 d2, he =>
      let r1 := LeTy.strengthenAt O d1 he.1
      let r2 := LeTy.strengthenAt O d2 he.2
      ⟨.andI _ _ r1.ev r2.ev, .andI _ _ r1.typed r2.typed, ⟨r1.strong, r2.strong⟩⟩
  | _, _, _, _, _, .andE1 _ d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.andE1 _ r.ev, .andE1 _ r.typed, r.strong⟩
  | _, _, _, _, _, .andE2 _ d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.andE2 _ r.ev, .andE2 _ r.typed, r.strong⟩
  | _, _, _, _, _, .orI1 _ d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.orI1 _ r.ev, .orI1 _ r.typed, r.strong⟩
  | _, _, _, _, _, .orI2 _ d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.orI2 _ r.ev, .orI2 _ r.typed, r.strong⟩
  | _, _, _, _, _, .orE _ _ d1 d2, he =>
      let r1 := LeTy.strengthenAt O d1 he.1
      let r2 := LeTy.strengthenAt O d2 he.2
      ⟨.orE _ _ r1.ev r2.ev, .orE _ _ r1.typed r2.typed, ⟨r1.strong, r2.strong⟩⟩
  | _, _, _, _, _, .defL hg d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.defL _ _ r.ev, .defL hg r.typed, r.strong⟩
  | _, _, _, _, _, .defR hg d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.defR _ _ r.ev, .defR hg r.typed, r.strong⟩
  | _, _, _, _, _, .selL (p := p) dv, he =>
      let r := VcTy.cleanAt O dv he.1
      selLStrong O p r.1 r.2.1 r.2.2.down.1
        (fun hz => by rw [r.2.2.down.2]; exact he.2 hz)
  | _, _, _, _, _, .selR (p := p) dv, he =>
      let r := VcTy.cleanAt O dv he.1
      selRStrong O p r.1 r.2.1 r.2.2.down.1
        (fun hz => by rw [r.2.2.down.2]; exact he.2 hz)
  | _, _, _, _, _, .bindx S0 T0 d1, he =>
      let r := LeTy.strengthenAt O d1 he
      ⟨.bindx S0 T0 r.ev, .bindx S0 T0 r.typed, r.strong⟩

/-- **Cleaning an observation**: every inclusion on its spine is strengthened.
The spine itself — its bases, packings and unfoldings — is unchanged, so the
pack count is too. -/
def VcTy.cleanAt {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {k : Nat}
    (O : ObsInv G W k) {s : Sig} {Γ : Ctx σ s} {p : Vr σ s}
    {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (d : VcTy G W Γ p v T) (hv : v.PackBound k) :
    (w : Vc σ (scopeAt p)) × VcTy G W Γ p w T ×
      PLift (w.Strong ∧ w.spinePacks = v.spinePacks) :=
  match d, hv with
  | .vcVar (x := x0), _ => ⟨.vcVar, .vcVar, ⟨trivial, rfl⟩⟩
  | .vcLoc (l := l0), _ => ⟨_, .vcLoc, ⟨trivial, rfl⟩⟩
  | .vcLocAny (l := l0) (T := T0) h, _ => ⟨.vcLocAny l0 T0, .vcLocAny h, ⟨trivial, rfl⟩⟩
  | .vcPack (T := T0) dv, hv =>
      let r := VcTy.cleanAt O dv hv
      ⟨.vcPack T0 r.1, .vcPack r.2.1,
        ⟨r.2.2.down.1, congrArg (· + 1) r.2.2.down.2⟩⟩
  | .vcUnfold (T := T0) dv, hv =>
      let r := VcTy.cleanAt O dv hv
      ⟨.vcUnfold T0 r.1, .vcUnfold r.2.1, ⟨r.2.2.down.1, r.2.2.down.2⟩⟩
  | .vcSub T1 dv de, hv =>
      let r := VcTy.cleanAt O dv hv.2
      let re := LeTy.strengthenAt O de hv.1
      ⟨.vcSub T1 re.ev r.1, .vcSub T1 r.2.1 re.typed,
        ⟨⟨re.strong, r.2.2.down.1⟩, r.2.2.down.2⟩⟩

end

/-- **One level up, below a recursive type.**  The step of the reference's
`pre_canon_bind_aux` (`dot_soundness.v:268`).  A clean observation below `μT`
is inverted by recursion on the observation:

* a literal type is never below a recursive type (`LitTy.bindInv`);
* a widening composes with the inclusion and recurses;
* an unfolding is undone by the recursive call below its own recursive type,
  and the inclusion is reapplied to the unfolded observation — no packing is
  consumed, so the count is inherited;
* a packing is undone by the normal form of `μT' ≤ μT`, whose premise is
  instantiated at the location with the packed observation `w`.  Since
  `w.spinePacks < k`, the substituted premise has pack bound `k`, so
  `strengthenAt` at the level below makes it strong. -/
def ObsInv.bindStep {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hR : RecordedLit G W)
    {k : Nat} (O : ObsInv G W k) {l : BVar σ .var} {T : Ty σ ([],x)}
    {v : Vc σ []} {T0 : Ty σ []} (dv : VcTy G W .nil (.conc l) v T0) (hv : v.Strong)
    (hk : v.spinePacks < k + 1) (d : SLe G W .nil T0 (.TBind T)) :
    (u : Vc σ []) × VcTy G W .nil (.conc l) u (T.substVr (.conc l)) ×
      PLift (u.Strong ∧ u.spinePacks < v.spinePacks) :=
  match dv, hv, hk, d with
  | .vcLoc, _, _, d => (LitTy.bindInv (hR l) d.nf).elim
  | .vcLocAny h, _, _, d => (LitTy.bindInv h.toLitTy d.nf).elim
  | .vcSub T1 dv' de, hv, hk, d =>
      let r := ObsInv.bindStep hR O dv' hv.2 hk (SLe.trans ⟨_, de, hv.1⟩ d)
      ⟨r.1, r.2.1, ⟨r.2.2.down.1, r.2.2.down.2⟩⟩
  | .vcUnfold (T := T') dv', hv, hk, d =>
      let r := ObsInv.bindStep hR O dv' hv hk (SLe.refl (.TBind T'))
      ⟨.vcUnfold T (.vcSub _ d.ev r.1), .vcUnfold (.vcSub _ r.2.1 d.typed),
        ⟨⟨d.strong, r.2.2.down.1⟩, r.2.2.down.2⟩⟩
  | .vcPack (T := T') (v := w) dw, hv, hk, d =>
      match d.nf with
      | .head (.bindx s) =>
          match LeTy.substB s.typed (Le.PackBound.mono (Nat.zero_le k) _ s.strong)
              (EvB.oneConc dw (Vc.PackBound.mono (Nat.zero_le k) _ hv)
                (Nat.lt_of_succ_lt_succ hk)) with
          | ⟨_, hf, hb⟩ =>
              let sf := LeTy.strengthenAt O hf hb.down
              ⟨.vcSub _ sf.ev w, .vcSub _ dw sf.typed,
                ⟨⟨sf.strong, hv⟩, Nat.lt_succ_self _⟩⟩
      | .head (.bind1 s) =>
          match LeTy.substB s.typed (Le.PackBound.mono (Nat.zero_le k) _ s.strong)
              (EvB.oneConc dw (Vc.PackBound.mono (Nat.zero_le k) _ hv)
                (Nat.lt_of_succ_lt_succ hk)) with
          | ⟨_, hf, hb⟩ =>
              let sf := LeTy.strengthenAt O (LeTy.castR (Ty.substVr_weaken _ _) hf)
                hb.down
              ⟨.vcUnfold T (.vcSub _ sf.ev w), .vcUnfold (.vcSub _ dw sf.typed),
                ⟨⟨sf.strong, hv⟩, Nat.lt_succ_self _⟩⟩

/-- **One level up, below a type member.**  The step of the reference's
`pre_canon_typ_aux` (`dot_soundness.v:425`).  The base cases read the store:
`D_Typ` makes the member exact (`LitTy.typInv`).  An unfolding is undone at the
same level by `bindStep` and the rest handed to the level below; a packing is
undone through the `bind1` premise, instantiated and strengthened as in
`bindStep`, and the packed observation handed to the level below. -/
def ObsInv.typStep {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hR : RecordedLit G W)
    {k : Nat} (O : ObsInv G W k) {l : BVar σ .var} {a : Lb} {S U : Ty σ []}
    {v : Vc σ []} {T0 : Ty σ []} (dv : VcTy G W .nil (.conc l) v T0) (hv : v.Strong)
    (hk : v.spinePacks < k + 1) (d : SLe G W .nil T0 (.TTyp a S U)) :
    (TX : Ty σ []) × PLift ((G.lookup l).get? a = some (.dty TX)) ×
      SLe G W .nil S TX × SLe G W .nil TX U :=
  match dv, hv, hk, d with
  | .vcLoc, _, _, d => LitTy.typInv (hR l) d.nf
  | .vcLocAny h, _, _, d => LitTy.typInv h.toLitTy d.nf
  | .vcSub T1 dv' de, hv, hk, d =>
      ObsInv.typStep hR O dv' hv.2 hk (SLe.trans ⟨_, de, hv.1⟩ d)
  | .vcUnfold (T := T') dv', hv, hk, d =>
      let r := ObsInv.bindStep hR O dv' hv hk (SLe.refl (.TBind T'))
      O.typ r.2.1 r.2.2.down.1
        (Nat.lt_of_lt_of_le r.2.2.down.2 (Nat.le_of_lt_succ hk)) d
  | .vcPack (T := T') (v := w) dw, hv, hk, d =>
      match d.nf with
      | .head (.bind1 s) =>
          match LeTy.substB s.typed (Le.PackBound.mono (Nat.zero_le k) _ s.strong)
              (EvB.oneConc dw (Vc.PackBound.mono (Nat.zero_le k) _ hv)
                (Nat.lt_of_succ_lt_succ hk)) with
          | ⟨_, hf, hb⟩ =>
              O.typ dw hv (Nat.lt_of_succ_lt_succ hk)
                (LeTy.strengthenAt O (LeTy.castR (Ty.substVr_weaken _ _) hf) hb.down)

/-- **One level up, below a method type.**  The reference's `canon_fun_aux`
(`dot_soundness.v:1051`), by the same recursion as `typStep`; at the base the
normal form ends in the congruence `fn` at a method conjunct (`LitTy.fnInv`),
and the location node is recorded (`LocBase`). -/
def ObsInv.fnStep {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hR : RecordedLit G W)
    {k : Nat} (O : ObsInv G W k) {l : BVar σ .var} {a : Lb} {S0 : Ty σ []}
    {U0 : Ty σ ([],x)} {v : Vc σ []} {T0 : Ty σ []}
    (dv : VcTy G W .nil (.conc l) v T0) (hv : v.Strong) (hk : v.spinePacks < k + 1)
    (d : SLe G W .nil T0 (.TFun a S0 U0)) : ObsFun G W l a S0 U0 :=
  match dv, hv, hk, d with
  | .vcLoc, _, _, d =>
      let r := LitTy.fnInv (hR l) d.nf
      ⟨_, .recorded, r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩
  | .vcLocAny h, _, _, d =>
      let r := LitTy.fnInv h.toLitTy d.nf
      ⟨_, .witness h, r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩
  | .vcSub T1 dv' de, hv, hk, d =>
      ObsInv.fnStep hR O dv' hv.2 hk (SLe.trans ⟨_, de, hv.1⟩ d)
  | .vcUnfold (T := T') dv', hv, hk, d =>
      let r := ObsInv.bindStep hR O dv' hv hk (SLe.refl (.TBind T'))
      O.fn r.2.1 r.2.2.down.1
        (Nat.lt_of_lt_of_le r.2.2.down.2 (Nat.le_of_lt_succ hk)) d
  | .vcPack (T := T') (v := w) dw, hv, hk, d =>
      match d.nf with
      | .head (.bind1 s) =>
          match LeTy.substB s.typed (Le.PackBound.mono (Nat.zero_le k) _ s.strong)
              (EvB.oneConc dw (Vc.PackBound.mono (Nat.zero_le k) _ hv)
                (Nat.lt_of_succ_lt_succ hk)) with
          | ⟨_, hf, hb⟩ =>
              O.fn dw hv (Nat.lt_of_succ_lt_succ hk)
                (LeTy.strengthenAt O (LeTy.castR (Ty.substVr_weaken _ _) hf) hb.down)

/-- The tower's step: observation inversion below `k` gives it below `k+1`. -/
def ObsInv.step {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hR : RecordedLit G W)
    {k : Nat} (O : ObsInv G W k) : ObsInv G W (k + 1) where
  bind := fun dv hv hk d => ObsInv.bindStep hR O dv hv hk d
  typ := fun dv hv hk d => ObsInv.typStep hR O dv hv hk d
  fn := fun dv hv hk d => ObsInv.fnStep hR O dv hv hk d

/-- **Every level of the tower**, over a store typing that records literal
types. -/
def RecordedLit.obsInv {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hR : RecordedLit G W) : (k : Nat) → ObsInv G W k
  | 0 => ObsInv.zero
  | k + 1 => ObsInv.step hR (hR.obsInv k)

/-! ## Consequences

Everything below needs `RecordedLit G W` and nothing else; `Store.Honest`
supplies it.  Each result is stated at `RecordedLit` and, under the same name,
at `Store.Honest`. -/

namespace RecordedLit

variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hR : RecordedLit G W)

/-- **Strengthening**: every inclusion, in any context, is included by strong
evidence between the same types.  The level used is one more than the
evidence's total pack count. -/
def strengthen {s : Sig} {Γ : Ctx σ s} {e : Le σ s} {S T : Ty σ s}
    (d : LeTy G W Γ e S T) : SLe G W Γ S T :=
  LeTy.strengthenAt (hR.obsInv (e.packs + 1)) d (Le.packBound_of_packs e (Nat.lt_succ_self _))

/-- **Cleaning** an observation: the same subject, type and spine, every
inclusion on the spine strong. -/
def clean {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)}
    {T : Ty σ (scopeAt p)} (d : VcTy G W Γ p v T) :
    (w : Vc σ (scopeAt p)) × VcTy G W Γ p w T ×
      PLift (w.Strong ∧ w.spinePacks = v.spinePacks) :=
  VcTy.cleanAt (hR.obsInv (v.packs + 1)) d (Vc.packBound_of_packs v (Nat.lt_succ_self _))

/-- **The normalizer**: every closed inclusion has a normal form.  The target's
`stp_trans_pushback` (`dot_soundness.v:201`), extended to the concrete
`selL`/`selR` the source does not have. -/
def nf {e : Le σ []} {S T : Ty σ []} (d : LeTy G W .nil e S T) : LeNf G W S T :=
  (hR.strengthen d).nf

/-- **Canonical forms at a type member**, the target's `canon_typ`
(`dot_soundness.v:843`): a closed observation of a location at `{a : S..U}`
finds the stored definition `dty TX` at `a`, with strong `S ≤ TX` and
`TX ≤ U`. -/
def obsTyp {l : BVar σ .var} {a : Lb} {S U : Ty σ []} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TTyp a S U)) :
    (TX : Ty σ []) × PLift ((G.lookup l).get? a = some (.dty TX)) ×
      SLe G W .nil S TX × SLe G W .nil TX U :=
  let r := hR.clean dv
  (hR.obsInv (r.1.spinePacks + 1)).typ r.2.1 r.2.2.down.1 (Nat.lt_succ_self _)
    (SLe.refl _)

/-- **Canonical forms at a recursive type**, the target's `canon_bind`
(`dot_soundness.v:831`): a closed observation of a location at `μT` gives a
clean observation at the opened body `T[ℓ]` with strictly fewer packings on the
spine. -/
def obsBind {l : BVar σ .var} {T : Ty σ ([],x)} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TBind T)) :
    (u : Vc σ []) × VcTy G W .nil (.conc l) u (T.substVr (.conc l)) ×
      PLift (u.Strong ∧ u.spinePacks < v.spinePacks) :=
  let r := hR.clean dv
  let o := (hR.obsInv (r.1.spinePacks + 1)).bind r.2.1 r.2.2.down.1
    (Nat.lt_succ_self _) (SLe.refl _)
  ⟨o.1, o.2.1, ⟨o.2.2.down.1, Nat.lt_of_lt_of_eq o.2.2.down.2 r.2.2.down.2⟩⟩

/-- **Canonical forms at a method type**, the target's `canon_fun`
(`dot_soundness.v:1115`) at the evidence level: a closed observation of a
location at `{a : S0 → U0}` stands on a location node whose type has a method
conjunct at `a`, related to `S0`/`U0` by strong inclusions. -/
def obsFun {l : BVar σ .var} {a : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TFun a S0 U0)) : ObsFun G W l a S0 U0 :=
  let r := hR.clean dv
  (hR.obsInv (r.1.spinePacks + 1)).fn r.2.1 r.2.2.down.1 (Nat.lt_succ_self _)
    (SLe.refl _)

/-- **Inversion into a type member.**  A closed inclusion into `{a : S..U}` is,
after transitivity elimination, a form decided by its left head: `⊥`; the
congruence `typ` at the same label; `sel1` through a stored definition,
recursively a normal form; `bind1`, whose premise is strong under the self; or
`and11`/`and12`/`or1`, recursively normal forms.  The right-headed forms cannot
conclude at a type member. -/
def invTyp {e : Le σ []} {T1 : Ty σ []} {a : Lb} {S U : Ty σ []}
    (d : LeTy G W .nil e T1 (.TTyp a S U)) : LeNfHead G W T1 (.TTyp a S U) :=
  match hR.nf d with
  | .head h => h

/-- **Inversion between type members**: `{a : S1..U1} ≤ {b : S2..U2}` closed
forces the same label and strong inclusions of the bounds, whatever `trans`,
intersection, union or selection steps the evidence used. -/
def invTypTyp {e : Le σ []} {a b : Lb} {S1 U1 S2 U2 : Ty σ []}
    (d : LeTy G W .nil e (.TTyp a S1 U1) (.TTyp b S2 U2)) :
    PLift (a = b) × SLe G W .nil S2 S1 × SLe G W .nil U1 U2 := by
  have n := hR.nf d
  cases n with
  | head h =>
      cases h with
      | typ s1 s2 => exact ⟨⟨rfl⟩, s1, s2⟩

/-- **Inversion into a recursive type.**  A closed inclusion into `μT` is a form
decided by its left head: `⊥`, `sel1` through a stored definition,
`bind1`/`bindx` from a recursive type, or `and11`/`and12`/`or1`.  No
right-headed form concludes at `μT`. -/
def invIntoBind {e : Le σ []} {T1 : Ty σ []} {T : Ty σ ([],x)}
    (d : LeTy G W .nil e T1 (.TBind T)) : LeNfHead G W T1 (.TBind T) :=
  match hR.nf d with
  | .head h => h

/-- **Inversion between recursive types**: a closed `μT ≤ μT'` is a `bindx` or a
`bind1`, with a strong premise under the self hypothesis `z : T`. -/
def invBind {e : Le σ []} {T T' : Ty σ ([],x)}
    (d : LeTy G W .nil e (.TBind T) (.TBind T')) :
    SLe G W (Ctx.nil.cons T) T T' ⊕ SLe G W (Ctx.nil.cons T) T (Ty.TBind T').weaken :=
  match hR.nf d with
  | .head (.bindx s) => .inl s
  | .head (.bind1 s) => .inr s

/-- **`Normalizer.Contract` is inhabited.**  The inclusion `μT ≤ μT'` is
inverted by `invBind`, and its strong premise is instantiated at the location
with the given observation `w` by the plain substitution theorem.  The
contracted observation is `w` widened (and, for `bind1`, unfolded), so its
spine is `w`'s: the bound `≤ w.spinePacks` holds on the nose. -/
def contract : Contract G W where
  step := fun dw de =>
    match hR.invBind de with
    | .inl s =>
        let f := LeTy.substEv s.typed (MonoSyn.Ev.oneConc dw)
        ⟨.vcSub _ f.1 _, .vcSub _ dw f.2, ⟨Nat.le_refl _⟩⟩
    | .inr s =>
        let f := LeTy.substEv s.typed (MonoSyn.Ev.oneConc dw)
        ⟨.vcUnfold _ (.vcSub _ f.1 _),
          .vcUnfold (.vcSub _ dw (LeTy.castR (Ty.substVr_weaken _ _) f.2)),
          ⟨Nat.le_refl _⟩⟩

/-- **Redex elimination with no hypothesis**: `Normalizer.VcTy.canon` at the
inhabitant `contract`. -/
def canon {l : BVar σ .var} {v : Vc σ []} {T : Ty σ []}
    (d : VcTy G W .nil (.conc l) v T) : VcRf G W l v T :=
  VcTy.canon hR.contract v.spinePacks v d (Nat.le_refl _)

end RecordedLit

/-- Strong closed inclusion runs downhill for vacuity, with no hypothesis: the
two rules `LeTy.vacuousMono` needs `BoundsVacuous` for are the concrete
selections, and strong evidence has none. -/
theorem LeTy.vacuousStrong {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {e : Le σ []} → {S T : Ty σ []} → LeTy G W .nil e S T → e.Strong →
    Vacuous G T → Vacuous G S
  | _, _, _, .refl _, _, h => h
  | _, _, _, .trans _ d1 d2, hs, h =>
      LeTy.vacuousStrong d1 hs.1 (LeTy.vacuousStrong d2 hs.2 h)
  | _, _, _, .top _, _, h => absurd h Vacuous.not_top
  | _, _, _, .bot _, _, _ => .bot
  | _, _, _, .dtyp _ _, _, h => absurd h Vacuous.not_typ
  | _, _, _, .dfun _ _, _, h => absurd h Vacuous.not_fun
  | _, _, _, .andI _ _ d1 d2, hs, h =>
      (Vacuous.and_inv h).elim (fun h1 => LeTy.vacuousStrong d1 hs.1 h1)
        (fun h2 => LeTy.vacuousStrong d2 hs.2 h2)
  | _, _, _, .andE1 _ d, hs, h => .andL (LeTy.vacuousStrong d hs h)
  | _, _, _, .andE2 _ d, hs, h => .andR (LeTy.vacuousStrong d hs h)
  | _, _, _, .orI1 _ d, hs, h => LeTy.vacuousStrong d hs (Vacuous.or_inv h).1
  | _, _, _, .orI2 _ d, hs, h => LeTy.vacuousStrong d hs (Vacuous.or_inv h).2
  | _, _, _, .orE _ _ d1 d2, hs, h =>
      .or (LeTy.vacuousStrong d1 hs.1 h) (LeTy.vacuousStrong d2 hs.2 h)
  | _, _, _, .defL hg d, hs, h =>
      .sel hg (LeTy.vacuousStrong d hs (Vacuous.unrename h))
  | _, _, _, .defR hg d, hs, h =>
      Vacuous.rename (LeTy.vacuousStrong d hs (Vacuous.sel_inv hg h))
  | _, _, _, .selL (p := p) (v := v) _, hs, _ => absurd hs (Le.selL_not_strong p v)
  | _, _, _, .selR (p := p) (v := v) _, hs, _ => absurd hs (Le.selR_not_strong p v)
  | _, _, _, .bindx _ _ _, _, _ => .bind
  | _, _, _, .muDrop _, _, _ => .bind

/-- **`CanonicalForms.BoundsVacuous` holds** whenever the store typing records
literal types.  A closed observation at `{a : S..U}` brackets the stored
definition by strong inclusions (`RecordedLit.obsTyp`), and strong inclusions
run downhill for vacuity with no hypothesis (`LeTy.vacuousStrong`). -/
theorem RecordedLit.boundsVacuous {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hR : RecordedLit G W) : BoundsVacuous G W where
  lower := fun dv h =>
    match hR.obsTyp dv with
    | ⟨_, hg, sS, _⟩ => LeTy.vacuousStrong sS.typed sS.strong (Vacuous.sel_inv hg.down h)
  upper := fun dv h =>
    match hR.obsTyp dv with
    | ⟨_, hg, _, sU⟩ => .sel hg.down (LeTy.vacuousStrong sU.typed sU.strong h)

/-- **Consistency** whenever the store typing records literal types: no closed
evidence includes `⊤` in `⊥`, because its normal form would be a form decided
by the head `⊤`, and there is none. -/
theorem RecordedLit.consistency {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {e : Le σ []} (hR : RecordedLit G W) (h : LeTy G W .nil e .TTop .TBot) : False :=
  match hR.nf h with
  | .head h' => nomatch h'

/-- `obs_conc_admissible` whenever the store typing records literal types. -/
def RecordedLit.obsConcAdmissible {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hR : RecordedLit G W) : ObsConcAdmissible G W := fun dv =>
  match hR.obsTyp dv with
  | ⟨TX, hg, sS, sU⟩ => ⟨TX, hg, ⟨_, sS.typed⟩, ⟨_, sU.typed⟩⟩

/-! ### Over an honest store -/

namespace Store.Honest

variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (hG : Store.Honest G W)

/-- `RecordedLit.strengthen` over an honest store. -/
def strengthen {s : Sig} {Γ : Ctx σ s} {e : Le σ s} {S T : Ty σ s}
    (d : LeTy G W Γ e S T) : SLe G W Γ S T :=
  hG.recordedLit.strengthen d

/-- `RecordedLit.clean` over an honest store. -/
def clean {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)}
    {T : Ty σ (scopeAt p)} (d : VcTy G W Γ p v T) :
    (w : Vc σ (scopeAt p)) × VcTy G W Γ p w T ×
      PLift (w.Strong ∧ w.spinePacks = v.spinePacks) :=
  hG.recordedLit.clean d

/-- **The normalizer over an honest store**: every closed inclusion has a normal
form. -/
def nf {e : Le σ []} {S T : Ty σ []} (d : LeTy G W .nil e S T) : LeNf G W S T :=
  hG.recordedLit.nf d

/-- `RecordedLit.obsTyp` over an honest store: canonical forms at a type
member. -/
def obsTyp {l : BVar σ .var} {a : Lb} {S U : Ty σ []} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TTyp a S U)) :
    (TX : Ty σ []) × PLift ((G.lookup l).get? a = some (.dty TX)) ×
      SLe G W .nil S TX × SLe G W .nil TX U :=
  hG.recordedLit.obsTyp dv

/-- `RecordedLit.obsBind` over an honest store: canonical forms at a recursive
type. -/
def obsBind {l : BVar σ .var} {T : Ty σ ([],x)} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TBind T)) :
    (u : Vc σ []) × VcTy G W .nil (.conc l) u (T.substVr (.conc l)) ×
      PLift (u.Strong ∧ u.spinePacks < v.spinePacks) :=
  hG.recordedLit.obsBind dv

/-- `RecordedLit.obsFun` over an honest store: canonical forms at a method
type. -/
def obsFun {l : BVar σ .var} {a : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)} {v : Vc σ []}
    (dv : VcTy G W .nil (.conc l) v (.TFun a S0 U0)) : ObsFun G W l a S0 U0 :=
  hG.recordedLit.obsFun dv

/-- **Inversion into a type member** over an honest store
(`RecordedLit.invTyp`). -/
def invTyp {e : Le σ []} {T1 : Ty σ []} {a : Lb} {S U : Ty σ []}
    (d : LeTy G W .nil e T1 (.TTyp a S U)) : LeNfHead G W T1 (.TTyp a S U) :=
  hG.recordedLit.invTyp d

/-- **Inversion between type members** over an honest store
(`RecordedLit.invTypTyp`). -/
def invTypTyp {e : Le σ []} {a b : Lb} {S1 U1 S2 U2 : Ty σ []}
    (d : LeTy G W .nil e (.TTyp a S1 U1) (.TTyp b S2 U2)) :
    PLift (a = b) × SLe G W .nil S2 S1 × SLe G W .nil U1 U2 :=
  hG.recordedLit.invTypTyp d

/-- **Inversion into a recursive type** over an honest store
(`RecordedLit.invIntoBind`). -/
def invIntoBind {e : Le σ []} {T1 : Ty σ []} {T : Ty σ ([],x)}
    (d : LeTy G W .nil e T1 (.TBind T)) : LeNfHead G W T1 (.TBind T) :=
  hG.recordedLit.invIntoBind d

/-- **Inversion between recursive types** over an honest store
(`RecordedLit.invBind`). -/
def invBind {e : Le σ []} {T T' : Ty σ ([],x)}
    (d : LeTy G W .nil e (.TBind T) (.TBind T')) :
    SLe G W (Ctx.nil.cons T) T T' ⊕ SLe G W (Ctx.nil.cons T) T (Ty.TBind T').weaken :=
  hG.recordedLit.invBind d

/-- **`Normalizer.Contract` is inhabited over every honest store**
(`RecordedLit.contract`). -/
def contract : Contract G W := hG.recordedLit.contract

/-- **Redex elimination over an honest store, with no hypothesis**:
`Normalizer.VcTy.canon` at `Store.Honest.contract`. -/
def canon {l : BVar σ .var} {v : Vc σ []} {T : Ty σ []}
    (d : VcTy G W .nil (.conc l) v T) : VcRf G W l v T :=
  hG.recordedLit.canon d

end Store.Honest

/-- **`CanonicalForms.BoundsVacuous` holds over every honest store**
(`RecordedLit.boundsVacuous`). -/
theorem Store.Honest.boundsVacuous {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hG : Store.Honest G W) : BoundsVacuous G W :=
  hG.recordedLit.boundsVacuous

/-- `CanonicalForms.no_loc_le_bot` with its hypothesis discharged: no closed
inclusion over an honest store empties a location. -/
theorem Store.Honest.no_loc_le_bot {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {e : Le σ []} (hG : Store.Honest G W) (l : BVar σ .var)
    (h : LeTy G W .nil e (tyOf W l) .TBot) : False :=
  FCdotR.no_loc_le_bot hG hG.boundsVacuous l h

/-- **Consistency over an honest store, with no other hypothesis.**  No closed
evidence includes `⊤` in `⊥`. -/
theorem consistency_honest {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {e : Le σ []}
    (hG : Store.Honest G W) (h : LeTy G W .nil e .TTop .TBot) : False :=
  hG.recordedLit.consistency h

/-- The same, by `CanonicalForms.consistency` at the inhabitant of its
hypothesis: the vacuity argument and the normal-form argument agree. -/
theorem consistency_honest' {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {e : Le σ []}
    (hG : Store.Honest G W) (h : LeTy G W .nil e .TTop .TBot) : False :=
  consistency hG hG.boundsVacuous h

/-- **`obs_conc_admissible`**, the converse of `obs_conc_easy`: over an honest
store, every closed observation of a location at a type member is bracketed by
the definition the store holds.  So the concrete `selL`/`selR` add no power over
`defL`/`defR`. -/
def obs_conc_admissible {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hG : Store.Honest G W) : ObsConcAdmissible G W :=
  hG.recordedLit.obsConcAdmissible

/-! ## The honest two-object store

`StoreTyping.TwoObjectStore.honest` is an honest store with cross-referencing
entries; over it the results above hold with nothing left to discharge. -/

namespace TwoObjectStore

open Oopsla16.PackingCounterexample (S2 G)

/-- Consistency over the two-object store, unconditionally. -/
example {e : Le S2 []} (h : LeTy G W .nil e .TTop .TBot) : False :=
  consistency_honest honest h

/-- `obs_conc_admissible` over the two-object store. -/
example : ObsConcAdmissible G W := obs_conc_admissible honest

/-- The contraction hypothesis of redex elimination, over the two-object
store. -/
example : Contract G W := honest.contract

end TwoObjectStore

end FCdotR
