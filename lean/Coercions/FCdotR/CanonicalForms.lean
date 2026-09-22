import Coercions.FCdotR.Normalizer

/-!
# Canonical forms for closed evidence

What the head shapes of the eighteen inclusion rules force, and what
consistency at the empty local context reduces to.

Three results are unconditional.

* `no_pack_at_abs`: no rule types a `vcPack` whose subject is an abstract
  variable.  `Typing` arranges this by making the subject index of `VcTy.vcPack`
  the constructor `Vr.conc`; this is the statement that the arrangement works,
  and it is the target's form of the restriction `Oopsla16/PackingCounterexample`
  shows the source needs.
* `LeTy.headPair_of_not_trans`: a single inclusion rule other than `trans`
  relates types whose outermost formers stand in one of ten named relations.
* Its corollaries `typ_le_bind_is_trans` and `top_le_bot_is_trans`: an inclusion
  from a type member to a recursive type, or from `⊤` to `⊥`, can only be a
  transitivity chain.  These are the two inversions the red team proved by cases
  on one example store; here they hold over every store and in every context.

Then consistency itself, which is **not** unconditional.  `Vacuous` is a
syntactic over-approximation of "no value of this store inhabits this type":
`⊥` is vacuous, a recursive type is vacuous, an intersection is vacuous when a
conjunct is, a union when both are, and a concrete selection when the type
stored at that member is.  `LeTy.vacuousMono` proves that a closed inclusion
runs downhill for it — `S ≤ T` and `T` vacuous force `S` vacuous — and
`consistency` follows, since `⊥` is vacuous and `⊤` is not.

Sixteen of the eighteen rules are discharged outright, including `bindx` and
`muDrop`, which need no premise at all because every recursive type is declared
vacuous.  The two that are not are `selL` and `selR`, and they are exactly the
two that read an observation of a location.  So the whole of consistency sits on
the hypothesis `BoundsVacuous`: a closed observation of `ℓ` at `{a : S..U}`
brackets the *stored* member — `S` is vacuous if `ℓ.a` is, and `ℓ.a` is vacuous
if `U` is.  **Nothing here inhabits `BoundsVacuous`**, and both `consistency` and
`obs_conc_admissible`'s hard half say so.  `BoundsVacuous` is the `Vacuous`
shadow of `ObsConcAdmissible`; the two cannot be derived from each other here,
because getting from the inclusions `S ≤ TX ≤ U` that `ObsConcAdmissible` hands
back to a `Vacuous` fact needs `vacuousMono` at those inclusions, and they are
not subderivations of anything.  Closing the gap needs the inversion of a closed
inclusion at a `TTyp` — transitivity elimination — which needs `Normalizer`'s
`Contract`, which needs the substitution theorem.  That is the chain, and it is
why item 2 of `STATUS.md` is not independent of item 1.

One case is unconditional: over the **empty store** there are no locations, so
`BoundsVacuous` holds vacuously and `consistency` is a theorem
(`consistency_nil`).
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst DmsHasType renameNil)

/-! ## Shape inversions -/

/-- **No rule packs an abstract variable.**  `VcTy.vcPack`'s subject index is
the constructor `Vr.conc`, so a `vcPack` node at an abstract subject has no
typing at all — it is untypable, not merely underivable. -/
theorem no_pack_at_abs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {x : BVar s .var} {T : Ty σ (Oopsla16.scopeUpTo x,x)}
    {v : Vc σ (Oopsla16.scopeUpTo x)} {T' : Ty σ (Oopsla16.scopeUpTo x)}
    (h : VcTy G W Γ (.abs x) (.vcPack T v) T') : False := by
  cases h

/-- **The head table.**  A single inclusion rule other than `trans` relates
types whose outermost formers stand in one of the ten relations `HeadPair`
lists.  Everything else this module proves about closed inclusions is read off
this. -/
theorem LeTy.headPair_of_not_trans {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} {e : Le σ s} {S T : Ty σ s} :
    LeTy G W Γ e S T → e.isTrans = false → HeadPair (headOf S) (headOf T) := by
  intro h he
  cases h <;> simp_all [HeadPair, headOf, Le.isTrans]

/-- **A closed inclusion from a type member to a recursive type is a
transitivity chain.**  No congruence relates `{a : S..U}` to `μT`, no rule
introduces a `μ` on the right from a non-`μ` left, and the source has no
`stp_bind2`; so the only rule left is `trans`. -/
theorem typ_le_bind_is_trans {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} {e : Le σ s} {a : Lb} {S U : Ty σ s} {T : Ty σ (s,x)}
    (h : LeTy G W Γ e (.TTyp a S U) (.TBind T)) :
    ∃ M e1 e2, e = .trans M e1 e2 := by
  refine Le.exists_trans e ?_
  cases he : e.isTrans with
  | true => rfl
  | false =>
      have := h.headPair_of_not_trans he
      simp [HeadPair, headOf] at this

/-- **A closed inclusion from `⊤` to `⊥` is a transitivity chain.**  So the
consistency argument only ever has to look at what a `trans` chain can pass
through, which is what `LeTy.vacuousMono` does. -/
theorem top_le_bot_is_trans {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} {e : Le σ s} (h : LeTy G W Γ e .TTop .TBot) :
    ∃ M e1 e2, e = .trans M e1 e2 := by
  refine Le.exists_trans e ?_
  cases he : e.isTrans with
  | true => rfl
  | false =>
      have := h.headPair_of_not_trans he
      simp [HeadPair, headOf] at this

/-! ## Vacuity -/

/-- A syntactic over-approximation of "no value of this store inhabits this
type".  `⊥` is vacuous; a recursive type is vacuous, which is sound here only
because nothing below ever needs a recursive type to be inhabited; an
intersection is vacuous as soon as a conjunct is, a union when both are; and a
concrete selection is vacuous when the type the store records at that member is.
Neither a type member, a method member, `⊤` nor an abstract selection is ever
vacuous. -/
inductive Vacuous {σ : Sig} (G : Store σ σ) : {s : Sig} → Ty σ s → Prop where
  /-- `⊥` is vacuous. -/
  | bot {s : Sig} : Vacuous G (.TBot : Ty σ s)
  /-- A recursive type is vacuous. -/
  | bind {s : Sig} {T : Ty σ (s,x)} : Vacuous G (.TBind T)
  /-- An intersection whose first conjunct is vacuous. -/
  | andL {s : Sig} {T1 T2 : Ty σ s} : Vacuous G T1 → Vacuous G (.TAnd T1 T2)
  /-- An intersection whose second conjunct is vacuous. -/
  | andR {s : Sig} {T1 T2 : Ty σ s} : Vacuous G T2 → Vacuous G (.TAnd T1 T2)
  /-- A union both of whose disjuncts are vacuous. -/
  | or {s : Sig} {T1 T2 : Ty σ s} :
      Vacuous G T1 → Vacuous G T2 → Vacuous G (.TOr T1 T2)
  /-- A selection on a location whose stored member is vacuous. -/
  | sel {s : Sig} {l : BVar σ .var} {a : Lb} {TX : Ty σ []} :
      (G.lookup l).get? a = some (.dty TX) → Vacuous G TX →
      Vacuous G (.TSel (.conc l) a : Ty σ s)

/-- `⊤` is not vacuous.  This one fact is the whole of `consistency`. -/
theorem Vacuous.not_top {σ s : Sig} {G : Store σ σ} :
    ¬ Vacuous G (.TTop : Ty σ s) := by intro h; cases h

/-- A type member is not vacuous. -/
theorem Vacuous.not_typ {σ s : Sig} {G : Store σ σ} {a : Lb} {S U : Ty σ s} :
    ¬ Vacuous G (.TTyp a S U) := by intro h; cases h

/-- A method member is not vacuous. -/
theorem Vacuous.not_fun {σ s : Sig} {G : Store σ σ} {a : Lb} {S : Ty σ s}
    {U : Ty σ (s,x)} : ¬ Vacuous G (.TFun a S U) := by intro h; cases h

/-- A selection on an abstract variable is not vacuous. -/
theorem Vacuous.not_sel_abs {σ s : Sig} {G : Store σ σ} {x : BVar s .var}
    {a : Lb} : ¬ Vacuous G (.TSel (.abs x) a : Ty σ s) := by intro h; cases h

/-- Inverting a vacuous intersection. -/
theorem Vacuous.and_inv {σ s : Sig} {G : Store σ σ} {A B : Ty σ s}
    (h : Vacuous G (.TAnd A B)) : Vacuous G A ∨ Vacuous G B := by
  cases h with
  | andL h => exact Or.inl h
  | andR h => exact Or.inr h

/-- Inverting a vacuous union. -/
theorem Vacuous.or_inv {σ s : Sig} {G : Store σ σ} {A B : Ty σ s}
    (h : Vacuous G (.TOr A B)) : Vacuous G A ∧ Vacuous G B := by
  cases h with
  | or h1 h2 => exact ⟨h1, h2⟩

/-- Inverting a vacuous selection on a location: the member the store records
there is vacuous. -/
theorem Vacuous.sel_inv {σ s : Sig} {G : Store σ σ} {l : BVar σ .var} {a : Lb}
    {TX : Ty σ []} (hg : (G.lookup l).get? a = some (.dty TX))
    (h : Vacuous G (.TSel (.conc l) a : Ty σ s)) : Vacuous G TX := by
  cases h with
  | sel hg' h' =>
      rw [hg] at hg'
      simp only [Option.some.injEq, Dm.dty.injEq] at hg'
      subst hg'
      exact h'

/-- Vacuity is insensitive to the weakening out of the empty local scope. -/
theorem Vacuous.unrename {σ : Sig} {G : Store σ σ} {T : Ty σ []}
    (h : Vacuous G (T.rename (renameNil (s := [])))) : Vacuous G T := by
  simpa using h

/-- The converse of `Vacuous.unrename`. -/
theorem Vacuous.rename {σ : Sig} {G : Store σ σ} {T : Ty σ []}
    (h : Vacuous G T) : Vacuous G (T.rename (renameNil (s := []))) := by
  simpa using h

/-- **The hypothesis consistency rests on.**  A closed observation of a location
at a type member brackets the member the store records there, in the sense of
`Vacuous`: the lower bound is vacuous if the selection is, and the selection is
vacuous if the upper bound is.

This is the `Vacuous` shadow of `ObsConcAdmissible`.  **Nothing in this
development inhabits it.**  It is what `Store.Honest` should buy, and buying it
needs the inversion of a closed inclusion at a `TTyp`, i.e. transitivity
elimination — see the module header. -/
structure BoundsVacuous {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Prop where
  /-- A vacuous selection forces a vacuous lower bound. -/
  lower : ∀ {l : BVar σ .var} {a : Lb} {S : Ty σ []} {v : Vc σ []},
    VcTy G W .nil (.conc l) v (.TTyp a S .TTop) →
    Vacuous G (.TSel (.conc l) a : Ty σ []) → Vacuous G S
  /-- A vacuous upper bound forces a vacuous selection. -/
  upper : ∀ {l : BVar σ .var} {a : Lb} {U : Ty σ []} {v : Vc σ []},
    VcTy G W .nil (.conc l) v (.TTyp a .TBot U) →
    Vacuous G U → Vacuous G (.TSel (.conc l) a : Ty σ [])

/-- **Closed inclusion runs downhill for vacuity.**  Sixteen of the eighteen
rules are discharged with no hypothesis: `bindx` and `muDrop` in particular need
no premise, because every recursive type is declared vacuous, and the
congruences `dtyp`/`dfun` are vacuous in their antecedent.  The two that use
`BoundsVacuous` are `selL` and `selR`.

The recursion is on the size of the evidence, not on its structure, because
`LeTy` and `VcTy` are mutually inductive and only the inclusion half is
traversed.

**Stated with an unproved hypothesis:** `hb : BoundsVacuous G W`, which nothing
inhabits. -/
theorem LeTy.vacuousMono {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hb : BoundsVacuous G W) :
    {e : Le σ []} → {S T : Ty σ []} → LeTy G W .nil e S T →
    Vacuous G T → Vacuous G S
  | _, _, _, .refl _, h => h
  | _, _, _, .trans _ d1 d2, h =>
      LeTy.vacuousMono hb d1 (LeTy.vacuousMono hb d2 h)
  | _, _, _, .top _, h => absurd h Vacuous.not_top
  | _, _, _, .bot _, _ => .bot
  | _, _, _, .dtyp _ _, h => absurd h Vacuous.not_typ
  | _, _, _, .dfun _ _, h => absurd h Vacuous.not_fun
  | _, _, _, .andI _ _ d1 d2, h =>
      (Vacuous.and_inv h).elim (fun h1 => LeTy.vacuousMono hb d1 h1)
        (fun h2 => LeTy.vacuousMono hb d2 h2)
  | _, _, _, .andE1 _ d, h => .andL (LeTy.vacuousMono hb d h)
  | _, _, _, .andE2 _ d, h => .andR (LeTy.vacuousMono hb d h)
  | _, _, _, .orI1 _ d, h => LeTy.vacuousMono hb d (Vacuous.or_inv h).1
  | _, _, _, .orI2 _ d, h => LeTy.vacuousMono hb d (Vacuous.or_inv h).2
  | _, _, _, .orE _ _ d1 d2, h =>
      .or (LeTy.vacuousMono hb d1 h) (LeTy.vacuousMono hb d2 h)
  | _, _, _, .defL hg d, h =>
      .sel hg (LeTy.vacuousMono hb d (Vacuous.unrename h))
  | _, _, _, .defR hg d, h =>
      Vacuous.rename (LeTy.vacuousMono hb d (Vacuous.sel_inv hg h))
  | _, _, _, .selL (p := p) (U := U) hv, h => by
      cases p with
      | abs x => exact nomatch x
      | conc l =>
          have h' : Vacuous G (U.rename (renameNil (s := []))) := h
          exact hb.upper hv (Vacuous.unrename h')
  | _, _, _, .selR (p := p) (S := S0) hv, h => by
      cases p with
      | abs x => exact nomatch x
      | conc l =>
          show Vacuous G (S0.rename (renameNil (s := [])))
          exact Vacuous.rename (hb.lower hv h)
  | _, _, _, .bindx _ _ _, _ => .bind
  | _, _, _, .muDrop _, _ => .bind
  termination_by e => e.size
  decreasing_by all_goals (simp only [Le.size]; omega)

/-- **Consistency over an honest store.**  No closed evidence includes `⊤` in
`⊥`.

**Stated with an unproved hypothesis.**  `hb : BoundsVacuous G W` is the
soundness of the bounds a closed observation of a location can report, and
nothing in this development inhabits it; the module header says what closing it
needs.  The honesty of the store is carried because it is what should buy `hb`,
but the proof below does not use it. -/
theorem consistency {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {e : Le σ []}
    (_hG : Store.Honest G W) (hb : BoundsVacuous G W)
    (h : LeTy G W .nil e .TTop .TBot) : False :=
  Vacuous.not_top (LeTy.vacuousMono hb h .bot)

/-- Over the **empty store** there are no locations, so `BoundsVacuous` holds
with nothing to prove. -/
theorem boundsVacuous_nil {G : Store [] []} {W : StoreTy []} :
    BoundsVacuous G W where
  lower := fun {l} => nomatch l
  upper := fun {l} => nomatch l

/-- **Consistency over the empty store, unconditionally.**  A sanity check that
the vacuity argument is not vacuous itself: with no store to read, the
`selL`/`selR` cases cannot arise and the remaining sixteen rules settle it. -/
theorem consistency_nil {G : Store [] []} {W : StoreTy []} {e : Le [] []}
    (h : LeTy G W .nil e .TTop .TBot) : False :=
  Vacuous.not_top (LeTy.vacuousMono boundsVacuous_nil h .bot)



/-! ## What an honest store offers the induction

Two unconditional facts about the type a location carries.  They are the base
case of the induction `obs_conc_admissible` needs — the `vcLoc` clause — and they
are proved outright, without canonical forms, because `DmsHasType` concludes at
only three shapes. -/

/-- A definition list's type is `⊤` or a right-nested intersection, and stays so
under any substitution of its scope.  `D_Nil`, `D_Typ` and `D_Fun` are the only
rules, and the last two conclude at a `TAnd`.  Written prefix, not as
`DmsHasType.head`: dot notation on an `Oopsla16` judgment would look for the
name in `Oopsla16`, which this module may not extend. -/
theorem dmsHasType_head {σ s1 : Sig} {G : Store σ σ} {Γ : Ctx σ s1} :
    {ds : Dms σ s1} → {T : Ty σ s1} → DmsHasType G Γ ds T →
    ∀ {s2 : Sig} (θ : Subst σ s1 σ s2),
      headOf (T.subst θ) = .top ∨ headOf (T.subst θ) = .and
  | _, _, .D_Nil, _, _ => Or.inl rfl
  | _, _, .D_Typ _, _, _ => Or.inr rfl
  | _, _, .D_Fun _ _ _ _, _, _ => Or.inr rfl

/-- **A location never carries a type member at its head.**  So `vcLoc` — the
base of every observation spine at a location — is never itself an observation
at `{a : S..U}`, and the induction `obs_conc_admissible` needs starts at a point
where there is nothing to prove.  Unconditional. -/
theorem Store.Honest.head_tyOf {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hG : Store.Honest G W) (l : BVar σ .var) :
    headOf (tyOf W l) = .top ∨ headOf (tyOf W l) = .and :=
  dmsHasType_head (hG.at' l).typed (Subst.one (.conc l))

/-- The type a definition list carries is not vacuous, under any substitution:
its conjuncts are type and method members, which are never vacuous, and its
spine ends in `⊤`.  Written prefix, for the reason `dmsHasType_head` gives. -/
theorem dmsHasType_not_vacuous {σ s1 : Sig} {G : Store σ σ} {Γ : Ctx σ s1} :
    {ds : Dms σ s1} → {T : Ty σ s1} → DmsHasType G Γ ds T →
    ∀ {s2 : Sig} (θ : Subst σ s1 σ s2), ¬ Vacuous G (T.subst θ)
  | _, _, .D_Nil, _, _ => Vacuous.not_top
  | _, _, .D_Typ hds, _, θ => fun h =>
      (Vacuous.and_inv h).elim Vacuous.not_typ (dmsHasType_not_vacuous hds θ)
  | _, _, .D_Fun hds _ _ _, _, θ => fun h =>
      (Vacuous.and_inv h).elim Vacuous.not_fun (dmsHasType_not_vacuous hds θ)

/-- **The type of a location is never vacuous.**  Unconditional, and the fact
that makes `Vacuous` a non-trivial invariant of an honest store: were it
vacuous, every location would be provably empty.  Together with
`LeTy.vacuousMono` it says no closed inclusion sends a location's type to `⊥`,
which is `consistency` localized at a location. -/
theorem Store.Honest.not_vacuous {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (hG : Store.Honest G W) (l : BVar σ .var) : ¬ Vacuous G (tyOf W l) :=
  dmsHasType_not_vacuous (hG.at' l).typed (Subst.one (.conc l))

/-- **No closed inclusion empties a location.**  A corollary of the previous two
results; it is `consistency` read at a location's own type instead of at `⊤`.

**Stated with an unproved hypothesis:** `hb : BoundsVacuous G W`. -/
theorem no_loc_le_bot {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {e : Le σ []}
    (hG : Store.Honest G W) (hb : BoundsVacuous G W) (l : BVar σ .var)
    (h : LeTy G W .nil e (tyOf W l) .TBot) : False :=
  hG.not_vacuous l (LeTy.vacuousMono hb h .bot)


/-- **Every closed observation of a location stands on that location.**  The
spine of a typed observation at `conc ℓ` has `vcLoc ℓ` at its foot: `vcVar` is
the only other base and it has no rule at a concrete subject.  This is the part
of `vc_canon` that needs nothing — no store invariant, no normalization, no
hypothesis. -/
theorem VcTy.base_conc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} : {v : Vc σ []} → {T : Ty σ []} →
    VcTy G W Γ (.conc l) v T → v.base = .vcLoc l
  | _, _, .vcLoc => rfl
  | _, _, .vcPack (v := v0) h => VcTy.base_conc (v := v0) h
  | _, _, .vcUnfold (v := v0) h => VcTy.base_conc (v := v0) h
  | _, _, .vcSub (v := v0) _ h _ => VcTy.base_conc (v := v0) h

/-! ## The store hypothesis is indispensable

`consistency` carries `Store.Honest` and `BoundsVacuous`, and it is worth
knowing that carrying *something* is not a formality.  Here is one location,
holding the empty object, whose store typing claims it has a member with the
bounds `⊤..⊥`.  Reading that claim off with `vcLoc`, widening it twice with
`dtyp`, and joining the two selections with `trans` gives closed evidence for
`⊤ ≤ ⊥`.  So `LeTy` on its own — over an arbitrary `StoreTy` — is inconsistent,
and every route to `consistency` has to go through an invariant tying `W` to
`G`.

The store typing below is of course not honest, and `badW_not_honest` proves it
with `Store.Honest.head_tyOf`: `DmsHasType` never concludes at a type member. -/

namespace DishonestStore

/-- One location. -/
abbrev S1 : Sig := ([],x)

/-- The store: a single empty object. -/
def G : Store S1 S1 := .cons .nil .dnil

/-- That location. -/
abbrev l : BVar S1 .var := .here

/-- A store typing that lies: it says the object has a type member with bounds
`⊤..⊥`.  Nothing in `Typing` forbids it, which is what `Store.Honest` is for. -/
def W : StoreTy S1 := fun _ => .TTyp 0 .TTop .TBot

/-- The lie, widened so that its upper bound is `⊤`: usable by `selR`. -/
def obsUpper : (v : Vc S1 []) × VcTy G W .nil (.conc l) v (.TTyp 0 .TTop .TTop) :=
  ⟨_, VcTy.vcSub (p := (.conc l : Vr S1 [])) (.TTyp 0 .TTop .TBot) VcTy.vcLoc
      (.dtyp (.refl .TTop) (.bot .TTop))⟩

/-- The lie, widened so that its lower bound is `⊥`: usable by `selL`. -/
def obsLower : (v : Vc S1 []) × VcTy G W .nil (.conc l) v (.TTyp 0 .TBot .TBot) :=
  ⟨_, VcTy.vcSub (p := (.conc l : Vr S1 [])) (.TTyp 0 .TTop .TBot) VcTy.vcLoc
      (.dtyp (.bot .TTop) (.refl .TBot))⟩

/-- `⊤` is below the selection. -/
def topLeSel :
    (e : Le S1 []) × LeTy G W .nil e (.TTop : Ty S1 []) (.TSel (.conc l) 0) :=
  ⟨_, LeTy.selR (p := (.conc l : Vr S1 [])) (S := .TTop) obsUpper.2⟩

/-- The selection is below `⊥`. -/
def selLeBot :
    (e : Le S1 []) × LeTy G W .nil e (.TSel (.conc l) 0) (.TBot : Ty S1 []) :=
  ⟨_, LeTy.selL (p := (.conc l : Vr S1 [])) (U := .TBot) obsLower.2⟩

/-- **Closed evidence for `⊤ ≤ ⊥` over a dishonest store typing.**  So no
unconditional `consistency` is available for `LeTy`, and the hypothesis
`consistency` carries is doing real work. -/
def topLeBot :
    (e : Le S1 []) × LeTy G W .nil e (.TTop : Ty S1 []) (.TBot : Ty S1 []) :=
  ⟨_, .trans (.TSel (.conc l) 0) topLeSel.2 selLeBot.2⟩

/-- And that store typing is not honest: `DmsHasType` concludes at `⊤` or at an
intersection, never at a type member. -/
theorem badW_not_honest (hG : Store.Honest G W) : False := by
  have hh : headOf (tyOf W l) = TyHead.typ := rfl
  rcases hG.head_tyOf l with h | h <;> rw [hh] at h <;> simp at h

end DishonestStore

/-! ## `obs_conc_admissible` -/

/-- **The statement of `obs_conc_admissible`.**  A closed observation of a
location at a type member is bracketed by the definition the store holds: there
is a stored `dty TX` at that label, and closed inclusions `S ≤ TX` and
`TX ≤ U`. -/
def ObsConcAdmissible {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type :=
  ∀ {l : BVar σ .var} {a : Lb} {S U : Ty σ []} {v : Vc σ []},
    VcTy G W .nil (.conc l) v (.TTyp a S U) →
      (TX : Ty σ []) × PLift ((G.lookup l).get? a = some (.dty TX)) ×
        ((dS : Le σ []) × LeTy G W .nil dS S TX) ×
        ((dU : Le σ []) × LeTy G W .nil dU TX U)

/-- **The easy half**, restated: over an honest store the definition that
`defL`/`defR` read is observable at exactly its own bounds.  This is
`Store.Honest.obs`, and it is the direction that does not need canonical
forms. -/
def obs_conc_easy {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (hG : Store.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G W Γ (.conc l) v (.TTyp a TX TX) :=
  hG.obs l hg

/-- **A consequence of the easy half**: over an honest store every `defL` is
subsumed by a `selL`, because the exact bounds the store records can be widened
to `⊥..TX` and observed.  So the concrete selection rules `selL`/`selR` really
are the more permissive pair, as `PLAN.md` §I says; `obs_conc_admissible` is the
claim that they are no *more* permissive. -/
def Store.Honest.defL_as_selL {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (hG : Store.Honest G W) (l : BVar σ .var) {a : Lb}
    {TX : Ty σ []} (hg : (G.lookup l).get? a = some (.dty TX)) :
    (e : Le σ s) × LeTy G W Γ e (.TSel (.conc l) a)
      (TX.rename (renameNil (s := s))) := by
  exact ⟨_, LeTy.selL (p := (Vr.conc l : Vr σ s)) (a := a) (U := TX)
    (VcTy.vcSub (p := (Vr.conc l : Vr σ s)) (.TTyp a TX TX)
      (hG.obs (Γ := Γ) l hg).2 (.dtyp (.bot TX) (.refl TX)))⟩

end FCdotR
