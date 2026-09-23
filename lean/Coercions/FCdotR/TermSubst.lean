import Coercions.FCdotR.SubstTyping
import Coercions.FCdotR.TermTyping

/-!
# Preservation of term typing under substitution

`SubstTyping` transports the two *evidence* judgments along a generated
substitution.  This module does the same for the three *term* judgments of
`TermTyping`:

```text
AtomTy G W Γ a T   →   AtomTy G' W' Γ' b (T[θ])
TmTy   G W Γ t T   →   TmTy   G' W' Γ' u (T[θ])
DefsTy G W Γ ds T  →   DefsTy G' W' Γ' es (T[θ])
```

Three things are forced by the source's rules and are worth reading off.

* **The hypothesis structure is bigger.**  `MonoSyn.Ev` gives, for each
  abstract variable, *observation* evidence for its image; that is all the
  evidence judgments consume, and it is the reference's `Definition Subst`
  (`dot_soundness.v:262`).  `AtomTy.varAbs` needs more: an **atom** typed at
  the image's substituted lookup type, because an atom is not evidence and
  cannot be recovered from evidence — `Vc` has no `pack` at an abstract
  subject, `Atom` does.  `MonoSyn.EvA` is `MonoSyn.Ev` plus that field.
* **The conclusion records the root.**  `AtomTy.pack`, `AtomTy.unpack` and
  `TmTy.app` all mention `a.root` in their conclusion's type, so a theorem that
  only produced *some* atom of the right type would not compose.  `AtomAt`
  therefore carries `atom.root = p`, and the theorem produces an atom rooted at
  `a.root[θ]`.  This is the term-level counterpart of `Atom.root_subst`.
* **The conclusion records the length.**  `DefsTy.dty` and `DefsTy.dfun` put
  `ds.length` in the label of the member they add, so `DefsAt` carries
  `defs.length = n` for the same reason.

The one lemma that is not a direct consequence of `SubstTyping` is
`AtomTy.weakenVar`: `MonoSyn.EvA.lift` has to weaken the atom it already has
under one more hypothesis.  It is a recursion of its own rather than an
instance of the theorem below, because as an instance it would be a call of
`AtomTy.substEv` on a derivation that is not a subterm of the one being
consumed, and the recursion would not be structural.  It is short because
`AtomTy` has no rule that introduces a binder: only `cast` leaves the judgment,
and it leaves it into `LeTy`, whose weakening *is* an instance of
`LeTy.substEv`.

What this module does **not** contain: any operational statement, and any
elaboration.  The machine's own substitution is `Machine.Inst`, which
`Machine.MonoSyn.ofInst` exhibits as a generated substitution, so the theorem
below covers it.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Subst Dms scopeUpTo varUpTo renameUpTo renameNil)

/-! ## Substitution laws the term rules need

`SubstTyping` needed weakening past a binder (`Ty.weaken_subst_lift`) and
weakening out of the empty local scope (`Ty.renameNil_subst`).  The term rules
need, in addition, the law for *instantiating* a binder — `T_VarPack`,
`T_VarUnpack` and `T_AppVar` all instantiate one — and two readings of
`Ctx.lookup`. -/

/-- Instantiating a binder and then substituting is substituting under the
binder and then instantiating by the substituted variable.  The substitution
level of the reference's `subst_open` family (`dot.v:400-2093`). -/
theorem Subst.one_comp {σ1 σ2 s1 s2 : Sig} (v : Vr σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) :
    (Subst.one v).comp θ = θ.lift.comp (Subst.one (v.subst θ)) := by
  apply Subst.ext
  · intro _; rfl
  · intro y
    cases y with
    | here => rfl
    | there w => exact (Vr.weaken_subst_one (θ.abs w) (v.subst θ)).symm

/-- The type level of `Subst.one_comp`: `(T{v})[θ] = (T[θ⇑]){v[θ]}`.  This is
what `pack`, `unpack` and `app` need in every clause below. -/
theorem Ty.substVr_subst {σ1 σ2 s1 s2 : Sig} (T : Ty σ1 (s1,x)) (v : Vr σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) :
    (T.substVr v).subst θ = (T.subst θ.lift).substVr (v.subst θ) := by
  show (T.subst (Subst.one v)).subst θ
      = (T.subst θ.lift).subst (Subst.one (v.subst θ))
  rw [Ty.subst_comp, Ty.subst_comp, Subst.one_comp]

/-- Weakening out of the empty local scope lands wherever it is sent: any two
renamings out of `[]` agree, because `BVar [] .var` is uninhabited.  This is
what relocates `AtomTy.varConc`'s conclusion. -/
theorem Ty.renameNil_rename {σ s1 s2 : Sig} (T : Ty σ []) (ρ : Rename s1 s2) :
    (T.rename (renameNil (s := s1))).rename ρ = T.rename (renameNil (s := s2)) := by
  show (T.subst (Subst.ofRename (renameNil (s := s1)))).subst (Subst.ofRename ρ)
      = T.subst (Subst.ofRename (renameNil (s := s2)))
  rw [Ty.subst_comp]
  exact congrArg (fun φ => T.subst φ) (Subst.ext (fun _ => rfl) (fun y => nomatch y))

/-- A substitution acts on the empty local scope as the identity if it is a
renaming of that scope: there is nothing there to rename. -/
theorem Subst.atNil_ofRename {σ s1 s2 : Sig} (ρ : Rename s1 s2) :
    Subst.atNil (Subst.ofRename (σ := σ) ρ) = Subst.id (σ := σ) (s := []) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- The newest hypothesis is its own type: `renameUpTo .here` is the identity,
so no weakening happens. -/
theorem Ctx.lookup_cons_here {σ s : Sig} (Γ : Ctx σ s) (S : Ty σ (s,x)) :
    (Γ.cons S).lookup .here = S :=
  Ty.subst_id S

/-- An older hypothesis' type is the outer one, weakened. -/
theorem Ctx.lookup_cons_there {σ s : Sig} (Γ : Ctx σ s) (S : Ty σ (s,x))
    (y : BVar s .var) : (Γ.cons S).lookup (.there y) = (Γ.lookup y).weaken := by
  show (Γ.lookupAt y).subst (Subst.ofRename ((renameUpTo y).comp Rename.succ))
      = ((Γ.lookupAt y).subst (Subst.ofRename (renameUpTo y))).subst
          (Subst.ofRename (Rename.succ (k := .var)))
  rw [Ty.subst_comp]
  exact congrArg (fun φ => (Γ.lookupAt y).subst φ)
    (Subst.ext (fun _ => rfl) (fun _ => rfl))

/-! ## An atom at a given root and type

Every conclusion below is of this shape: the produced atom, the variable it is
rooted at, and its derivation.  The root is part of the statement because
`pack`, `unpack` and `app` read it off. -/

/-- An atom rooted at `p` and typed at `T`. -/
structure AtomAt {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (p : Vr σ s) (T : Ty σ s) : Type where
  /-- The atom. -/
  atom : Atom σ s
  /-- Its root, which casts, packs and unpacks do not move. -/
  root : atom.root = p
  /-- Its derivation. -/
  deriv : AtomTy G W Γ atom T

/-- A definition list of a given length and type.  The length is part of the
statement because `D_Typ` and `D_Fun` put it in the label of the member they
add. -/
structure DefsAt {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (n : Nat) (T : Ty σ s) : Type where
  /-- The definition list. -/
  defs : Defs σ s
  /-- Its length. -/
  length : defs.length = n
  /-- Its derivation. -/
  deriv : DefsTy G W Γ defs T

/-! ## Weakening

The two instances of `SubstTyping`'s theorem that the hypothesis structure
below needs, plus the one recursion that is not an instance. -/

/-- Local weakening carries a hypothesis structure: every variable's image is
its own successor, the restriction is the identity, and the store is
untouched. -/
def MonoSyn.Ev.weaken {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) :
    MonoSyn.Ev G W Γ (MonoSyn.weaken (σ := σ) (s := s)) G W (Γ.cons S) where
  defs := fun l => by
    show G.lookup l
        = (G.lookup l).subst (Subst.atNil (Subst.ofRename (Rename.succ (k := .var))))
    rw [Subst.atNil_ofRename, Dms.subst_id]
  tys := fun l => by
    show tyOf W l
        = (tyOf W l).subst (Subst.atNil (Subst.ofRename (Rename.succ (k := .var))))
    rw [Subst.atNil_ofRename, Ty.subst_id]
  vc := fun x0 => ⟨.vcVar, by
    refine Eq.mpr (congrArg
      (fun (T0 : Ty σ (scopeUpTo x0)) =>
        VcTy G W (Γ.cons S) (Vr.abs (.there x0)) Vc.vcVar T0)
      (Ty.subst_id (Γ.lookupAt x0))) ?_
    exact VcTy.weakenVar S VcTy.vcVar⟩

/-- **Weakening an atom's typing.**  A recursion on the derivation, not an
instance of `AtomTy.substEv` below: as an instance it would be a call on a
derivation that is not a subterm of the one being consumed.  It is short
because `AtomTy` introduces no binder, so the only judgment it leaves into is
`LeTy`, whose weakening *is* an instance of `LeTy.substEv`. -/
def AtomTy.weakenVar {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) : {a : Atom σ s} → {T : Ty σ s} → AtomTy G W Γ a T →
    AtomAt G W (Γ.cons S) a.root.weaken T.weaken
  | _, _, .varAbs (x := x0) =>
      ⟨.var (.abs (.there x0)), rfl, by
        show AtomTy G W (Γ.cons S) (.var (.abs (.there x0))) ((Γ.lookup x0).weaken)
        rw [← Ctx.lookup_cons_there Γ S x0]
        exact .varAbs⟩
  | _, _, .varConc (l := l) =>
      ⟨.var (.conc l), rfl, by
        show AtomTy G W (Γ.cons S) (.var (.conc l))
            (((tyOf W l).rename (renameNil (s := s))).rename
              (Rename.succ (k := .var)))
        rw [Ty.renameNil_rename]
        exact .varConc⟩
  | _, _, .varConcAny (l := l) (T := T0) hd hs =>
      ⟨.var (.conc l), rfl, by
        show AtomTy G W (Γ.cons S) (.var (.conc l))
            (((T0.substVr (.conc l)).rename (renameNil (s := s))).rename
              (Rename.succ (k := .var)))
        rw [Ty.renameNil_rename]
        exact .varConcAny hd hs⟩
  | _, _, .cast (e := e) ha he =>
      match AtomTy.weakenVar S ha with
      | ⟨b, hroot, hd⟩ =>
          ⟨.cast b (LeTy.substEv he (MonoSyn.Ev.weaken S)).1, hroot,
            .cast hd (LeTy.substEv he (MonoSyn.Ev.weaken S)).2⟩
  | _, _, .pack (a := a0) (T := T0) ha =>
      match AtomTy.weakenVar S ha with
      | ⟨b, hroot, hd⟩ =>
          ⟨.pack (T0.subst (Subst.ofRename (Rename.succ (k := .var))).lift) b,
            hroot, by
              refine AtomTy.pack ?_
              rw [hroot, Vr.weaken_eq_subst_succ a0.root,
                ← Ty.substVr_subst T0 a0.root
                  (Subst.ofRename (Rename.succ (k := .var)))]
              exact hd⟩
  | _, _, .unpack (a := a0) (T := T0) ha =>
      match AtomTy.weakenVar S ha with
      | ⟨b, hroot, hd⟩ =>
          ⟨.unpack (T0.subst (Subst.ofRename (Rename.succ (k := .var))).lift) b,
            hroot, by
              have h : (T0.substVr a0.root).weaken
                  = (T0.subst (Subst.ofRename (Rename.succ (k := .var))).lift).substVr
                      b.root := by
                rw [hroot, Vr.weaken_eq_subst_succ a0.root]
                exact Ty.substVr_subst T0 a0.root _
              rw [h]
              exact AtomTy.unpack hd⟩

/-! ## The hypothesis structure for terms -/

/-- `MonoSyn.Ev` together with what `AtomTy.varAbs` needs: for every abstract
variable, an atom rooted at its image and typed at its substituted lookup
type.  The extra field is exactly the difference between the reference's
substitution lemma for `htp` and the one for `has_type`. -/
structure MonoSyn.EvA {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (G : Store σ1 σ1) (W : StoreTy σ1) (Γ : Ctx σ1 s1) (m : MonoSyn θ)
    (G' : Store σ2 σ2) (W' : StoreTy σ2) (Γ' : Ctx σ2 s2) : Type where
  /-- The evidence-level agreement, which the `cast` clauses consume through
  `LeTy.substEv`. -/
  ev : MonoSyn.Ev G W Γ m G' W' Γ'
  /-- An atom for the image of every abstract variable. -/
  atom : (x : BVar s1 .var) →
      AtomAt G' W' Γ' (θ.abs x) ((Γ.lookup x).subst θ)

namespace MonoSyn.EvA

/-- The identity carries one: every variable is its own atom. -/
def refl {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    EvA G W Γ (MonoSyn.id (σ := σ) (s := s)) G W Γ where
  ev := MonoSyn.Ev.refl
  atom := fun x => ⟨.var (.abs x), rfl, by
    show AtomTy G W Γ (.var (.abs x)) ((Γ.lookup x).subst Subst.id)
    rw [Ty.subst_id]
    exact .varAbs⟩

/-- Local weakening carries one. -/
def weaken {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) : EvA G W Γ (MonoSyn.weaken (σ := σ) (s := s)) G W (Γ.cons S) where
  ev := MonoSyn.Ev.weaken S
  atom := fun x => ⟨.var (.abs (.there x)), rfl, by
    show AtomTy G W (Γ.cons S) (.var (.abs (.there x))) ((Γ.lookup x).weaken)
    rw [← Ctx.lookup_cons_there Γ S x]
    exact .varAbs⟩

/-- Pushing under a binder.  At the new binder the atom is that binder; at an
older one it is the outer atom, weakened by `AtomTy.weakenVar`. -/
def lift {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : EvA G W Γ m G' W' Γ') (S : Ty σ1 (s1,x)) :
    EvA G W (Γ.cons S) m.lift G' W' (Γ'.cons (S.subst θ.lift)) where
  ev := E.ev.lift S
  atom := by
    intro y
    cases y with
    | here =>
        refine ⟨.var (.abs .here), rfl, ?_⟩
        have h : AtomTy G' W' (Γ'.cons (S.subst θ.lift)) (.var (.abs .here))
            ((Γ'.cons (S.subst θ.lift)).lookup .here) := .varAbs
        rw [Ctx.lookup_cons_here Γ' (S.subst θ.lift)] at h
        rw [Ctx.lookup_cons_here Γ S]
        exact h
    | there y =>
        match AtomTy.weakenVar (S.subst θ.lift) (E.atom y).deriv with
        | ⟨b, hroot, hd⟩ =>
            refine ⟨b, ?_, ?_⟩
            · rw [hroot, (E.atom y).root]
              rfl
            · rw [Ctx.lookup_cons_there Γ S y, Ty.weaken_subst_lift]
              exact hd

end MonoSyn.EvA

/-! ## The substitution theorem for terms

One mutual recursion, one clause per former, structure-preserving.  Every
clause with a binder rebuilds the hypothesis structure with `EvA.lift`; every
clause with a coercion calls `LeTy.substEv`, which takes no hypothesis beyond
`MonoSyn.Ev`. -/

mutual

/-- Atom typing transported along a generated substitution, with the image's
root recorded. -/
def AtomTy.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {a : Atom σ1 s1} {T : Ty σ1 s1} (d : AtomTy G W Γ a T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') :
    AtomAt G' W' Γ' (a.root.subst θ) (T.subst θ) :=
  match d with
  | .varAbs (x := x0) => E.atom x0
  | .varConc (l := l) =>
      ⟨.var (.conc (θ.conc l)), rfl, by
        show AtomTy G' W' Γ' (.var (.conc (θ.conc l)))
            (((tyOf W l).rename (renameNil (s := s1))).subst θ)
        rw [Ty.renameNil_subst, ← E.ev.tys l]
        exact .varConc⟩
  | .varConcAny (l := l) (T := T0) hd hs =>
      ⟨.var (.conc (θ.conc l)), rfl, by
        show AtomTy G' W' Γ' (.var (.conc (θ.conc l)))
            (((T0.substVr (.conc l)).rename (renameNil (s := s1))).subst θ)
        rw [Ty.renameNil_subst, varyTy θ l T0]
        exact .varConcAny (varyTyped θ E.ev.defs hd) (varyStored θ E.ev.defs hs)⟩
  | .cast (e := e) ha he =>
      match AtomTy.substEv ha E with
      | ⟨b, hroot, hd⟩ =>
          ⟨.cast b (LeTy.substEv he E.ev).1, hroot,
            .cast hd (LeTy.substEv he E.ev).2⟩
  | .pack (a := a0) (T := T0) ha =>
      match AtomTy.substEv ha E with
      | ⟨b, hroot, hd⟩ =>
          ⟨.pack (T0.subst θ.lift) b, hroot, by
            refine AtomTy.pack ?_
            rw [hroot, ← Ty.substVr_subst T0 a0.root θ]
            exact hd⟩
  | .unpack (a := a0) (T := T0) ha =>
      match AtomTy.substEv ha E with
      | ⟨b, hroot, hd⟩ =>
          ⟨.unpack (T0.subst θ.lift) b, hroot, by
            have h : (T0.substVr a0.root).subst θ
                = (T0.subst θ.lift).substVr b.root := by
              rw [hroot]
              exact Ty.substVr_subst T0 a0.root θ
            rw [h]
            exact AtomTy.unpack hd⟩

/-- Term typing transported along a generated substitution. -/
def TmTy.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {t : Tm σ1 s1} {T : Ty σ1 s1} (d : TmTy G W Γ t T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') :
    Σ u : Tm σ2 s2, TmTy G' W' Γ' u (T.subst θ) :=
  match d with
  | .atom ha =>
      match AtomTy.substEv ha E with
      | ⟨b, _, hd⟩ => ⟨.atom b, .atom hd⟩
  | .new T0 hds =>
      match DefsTy.substEv hds (E.lift T0) with
      | ⟨es, _, hd⟩ => ⟨.new (T0.subst θ.lift) es, .new _ hd⟩
  | .app (l := l) (b := b0) (U := U) ha hb =>
      match AtomTy.substEv ha E, AtomTy.substEv hb E with
      | ⟨ba, _, hda⟩, ⟨bb, hrootb, hdb⟩ =>
          ⟨.app ba l bb, by
            have h : (U.substVr b0.root).subst θ
                = (U.subst θ.lift).substVr bb.root := by
              rw [hrootb]
              exact Ty.substVr_subst U b0.root θ
            rw [h]
            exact .app hda hdb⟩
  | .let (S := S0) (T := T0) ht hu =>
      ⟨.let (TmTy.substEv ht E).1
          (TmTy.substEv hu (Ty.weaken_subst_lift S0 θ ▸ E.lift S0.weaken)).1,
        .let (TmTy.substEv ht E).2
          (Ty.weaken_subst_lift T0 θ ▸
            (TmTy.substEv hu (Ty.weaken_subst_lift S0 θ ▸ E.lift S0.weaken)).2)⟩
  | .cast (e := e) ht he =>
      ⟨.cast (TmTy.substEv ht E).1 (LeTy.substEv he E.ev).1,
        .cast (TmTy.substEv ht E).2 (LeTy.substEv he E.ev).2⟩

/-- Definition-list typing transported along a generated substitution, with the
image's length recorded. -/
def DefsTy.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {ds : Defs σ1 s1} {T : Ty σ1 s1} (d : DefsTy G W Γ ds T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') :
    DefsAt G' W' Γ' ds.length (T.subst θ) :=
  match d with
  | .dnil => ⟨.dnil, rfl, .dnil⟩
  | .dty (T := T0) (ds := ds0) hds =>
      match DefsTy.substEv hds E with
      | ⟨es, hlen, hd⟩ =>
          ⟨.dty (T0.subst θ) es, congrArg (· + 1) hlen, by
            rw [← hlen]
            exact .dty hd⟩
  | .dfun (S := S0) (U := U0) (ds := ds0) hds ht =>
      match DefsTy.substEv hds E,
          TmTy.substEv ht (Ty.weaken_subst_lift S0 θ ▸ E.lift S0.weaken) with
      | ⟨es, hlen, hd⟩, ⟨u, hu⟩ =>
          ⟨.dfun (S0.subst θ) (U0.subst θ.lift) u es,
            congrArg (· + 1) hlen, by
              rw [← hlen]
              exact .dfun hd hu⟩

end

end FCdotR
