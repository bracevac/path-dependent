import Coercions.FCdotR.Typing
import Coercions.Oopsla16.SubstLemmas
import Coercions.Oopsla16.PackingCounterexample

/-!
# Store typing: tying `StoreTy` to the store it describes

`Typing` carries the type of each stored literal as a bare function
`StoreTy σ := (l : BVar σ .var) → Ty σ ([],x)`, so that `tyOf` is data and its
stability under allocation is that function's extension rather than a
derivation's.  Nothing there says the function tells the truth, and until it
does, `VcTy.vcLoc` — and with it every concrete `selL`/`selR` — is a licence to
invent types for locations.  This module supplies the missing invariant.

```text
Store.Honest G W  ≔  for every ℓ there is a literal ds with
                     ⊢d ds : W ℓ   under the self  W ℓ,  and  ds[ℓ/z] = G(ℓ)
```

That is `T_Vary`'s two premises (`dot.v:220-226`) lifted out of the rule and
made an invariant of the pair `(G, W)`.  Three things follow, and they are what
the module proves.

* **`AtomTy.varConc` is `T_Vary`.**  `Store.Honest.vary` produces the source
  derivation the target's rule asserts, so reading a location's type off `W`
  is not a new power.
* **`W` agrees with what `defL`/`defR` read.**  `DmsHasType` only ever concludes
  at a right-nested intersection — `TAnd (TTyp ..) (TAnd .. TTop)` — and
  `D_Typ` makes a type member *exact*.  So if the stored literal defines `a` to
  be `TX`, which is the premise of `LeTy.defL`/`LeTy.defR`, then `tyOf W ℓ`
  has `{a : TX .. TX}` as a conjunct (`Store.Honest.member`), and the
  observation `selL`/`selR` want is derivable (`Store.Honest.obs`).  The shape
  is named, as data, by `Conjunct`.
* **Honesty survives allocation.**  `Store.Honest.alloc` mirrors `ST_Obj`
  (`Semantics.lean`), extending `W` by one entry.

The last one needs a fact the reference never has to state: its concrete
identifiers are absolute positions and are therefore "invariant under context
extension" (`dot.v:21-22`), whereas here a store weakening is a real renaming.
So the second half of this module proves that **the four source judgments are
stable under a store renaming that transports lookups** (`StoreMap`), which is
the intrinsic-scoping cost of `dot.v:21-22` and is reused by every later
preservation argument.

**`VcTy.vcLocAny` needs none of this.**  It carries its own `T_Vary` witness,
so the facts above hold of it with no store invariant: `varyMember` and
`varyObs` are the witness-level versions of `Store.Honest.member` and
`Store.Honest.obs` (`member` is now `varyMember` at the honesty witness), and
`Store.Honest.vcLoc_of_vcLocAny` says that over an honest store `vcLoc` is
`vcLocAny` at the recorded type.  The section *A substitution's store part*
moves such a witness along a substitution, which is what the `vcLocAny` and
`AtomTy.varConcAny` clauses of the two substitution theorems use.

The module closes with `Store.Honest` instantiated at the two-object store of
`Oopsla16/PackingCounterexample`, so that the invariant is known to be
inhabited by something with cross-referencing entries and positional labels.

What this module does **not** contain: any typing of the target's own terms
(that is `TermTyping`), any operational semantics for FCdotR, and any
completeness claim — `Store.Honest` is an invariant a machine maintains, not a
characterisation of the stores `Typing` admits.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst HasType DmsHasType Stp Htp EqSome
  renameNil renameUpTo varUpTo scopeUpTo)

/-! ## Conjuncts

`DmsHasType` concludes at a right-nested intersection whose conjuncts are the
members, in order (`dot.v:263-282`).  `Conjunct T M` names one of them.  It is
`Type`-valued, like every judgment here, because its payoff is *evidence*:
`Conjunct.ev` is the `andE1`/`andE2` chain that projects the member out. -/

/-- `T` is a right-nested intersection one of whose conjuncts is `M`. -/
inductive Conjunct {σ s : Sig} : Ty σ s → Ty σ s → Type where
  /-- The member is the head conjunct. -/
  | here {T1 T2 : Ty σ s} : Conjunct (.TAnd T1 T2) T1
  /-- The member is further along the spine. -/
  | there {T1 T2 M : Ty σ s} : Conjunct T2 M → Conjunct (.TAnd T1 T2) M

/-- The inclusion a conjunct *is*: a chain of `andE2` ending in an `andE1`. -/
def Conjunct.ev {σ s : Sig} {T M : Ty σ s} : Conjunct T M → Le σ s
  | .here (T1 := T1) (T2 := T2) => .andE1 T2 (.refl T1)
  | .there (T1 := T1) h => .andE2 T1 h.ev

/-- And that chain is typed: an intersection is included in each conjunct. -/
def Conjunct.typed {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {T M : Ty σ s} : (h : Conjunct T M) → LeTy G W Γ h.ev T M
  | .here => .andE1 _ (.refl _)
  | .there h => .andE2 _ h.typed

/-- Conjuncts survive substitution, because `TAnd` is a plain congruence. -/
def Conjunct.subst {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    {T M : Ty σ1 s1} → Conjunct T M → Conjunct (T.subst θ) (M.subst θ)
  | _, _, .here => .here
  | _, _, .there h => .there (Conjunct.subst θ h)

/-- **A definition list's type declares each of its type members, exactly.**
`D_Typ` (`dot.v:266-271`) gives a type member the bounds `T11..T11`, so reading
the member at label `a` off the definitions and reading it off the type agree.
This is the shape statement the module header promises. -/
def DmsHasType.conjunct {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → DmsHasType G Γ ds T → {a : Lb} →
    {TX : Ty σ s} → ds.get? a = some (.dty TX) → Conjunct T (.TTyp a TX TX)
  | _, _, .D_Nil, _, _, hg => by simp [Dms.get?] at hg
  | _, _, .D_Typ (ds := ds) (T11 := T11) hds, a, TX, hg => by
      have hg' : (if a = ds.length then some (Dm.dty T11) else ds.get? a)
          = some (.dty TX) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'
        have hT : T11 = TX := by simpa using hg'
        subst hT
        subst h
        exact .here
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunct hds hg')
  | _, _, .D_Fun (ds := ds) (OT11 := OT11) (OT12 := OT12) (t12 := t12) hds _ _ _,
      a, TX, hg => by
      have hg' : (if a = ds.length then some (Dm.dfun OT11 OT12 t12) else ds.get? a)
          = some (.dty TX) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'; simp at hg'
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunct hds hg')

/-! ## Honest stores -/

/-- What honesty asks at one location: the store typing's entry is a type the
stored literal really has under its own self, and instantiating that self by
the location gives what the store holds.  These are exactly `T_Vary`'s two
premises (`dot.v:220-226`). -/
structure HonestAt {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var) :
    Type where
  /-- The literal, before its self is instantiated. -/
  defs : Dms σ ([],x)
  /-- It has the recorded type, under that type as its self assumption. -/
  typed : DmsHasType G (Ctx.nil.cons (W l)) defs (W l)
  /-- Instantiating the self by the location gives the stored literal. -/
  stored : defs.substVr (.conc l) = G.lookup l

/-- An honest store: every location's literal really has the type the store
typing records for it.  The reference has no such predicate — `venv` is
unconstrained (`dot.v:69`) and `T_Vary` re-derives the literal's type at every
use — which is exactly why `StoreTy` needs one here. -/
structure Store.Honest {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type where
  /-- The witness at each location. -/
  at' : (l : BVar σ .var) → HonestAt G W l

/-- **`AtomTy.varConc` is the reference's `T_Vary`.**  Over an honest store the
type the target reads off `W` is one the source assigns to the location, so
indexing by a function rather than by a derivation costs nothing. -/
def Store.Honest.vary {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (h : Store.Honest G W) (l : BVar σ .var) :
    HasType G Γ (.tvar (.conc l)) ((tyOf W l).rename renameNil) :=
  .T_Vary (h.at' l).typed (h.at' l).stored

/-- **A `T_Vary` witness agrees with what `defL`/`defR` read.**  If a literal
`ds` has type `T` under its own self and instantiates to what `ℓ` stores — the
two premises of `T_Vary`, and of `VcTy.vcLocAny` — and the stored literal
defines the type member `a` to be `TX`, then `T` instantiated at `ℓ` has
`{a : TX .. TX}` among its conjuncts.  `D_Typ` makes the member exact whatever
type the witness picks, so this needs no store invariant: it is the fact about
`vcLocAny` that the consistency argument would consume, and
`Store.Honest.member` is its instance at the recorded type. -/
def varyMember {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    Conjunct (T.substVr (.conc l)) (.TTyp a TX TX) := by
  have hg2 : (ds.substVr (.conc l)).get? a = some (.dty TX) := by
    rw [hs]; exact hg
  rw [Dms.get?_subst] at hg2
  cases hget : ds.get? a with
  | none => rw [hget] at hg2; simp at hg2
  | some d =>
      rw [hget] at hg2
      cases d with
      | dfun _ _ _ => simp [Dm.subst] at hg2
      | dty TX0 =>
          have hTX : TX0.substVr (.conc l) = TX := by
            simp only [Option.map_some, Dm.subst] at hg2
            injection hg2 with e
            injection e
          have hc := Conjunct.subst (Subst.one (Vr.conc l))
            (DmsHasType.conjunct hd hget)
          simp only [Ty.subst] at hc
          rw [show Ty.subst TX0 (Subst.one (Vr.conc l)) = TX from hTX] at hc
          exact hc

/-- **The store typing agrees with what `defL`/`defR` read.**  If the literal
stored at `ℓ` defines the type member `a` to be `TX` — the premise of
`LeTy.defL` and `LeTy.defR`, and the reference's `stp_strong_sel1/2`
(`dot.v:305-314`) — then `tyOf W ℓ` has `{a : TX .. TX}` among its conjuncts.
The instance of `varyMember` at the honesty witness. -/
def Store.Honest.member {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    Conjunct (tyOf W l) (.TTyp a TX TX) :=
  varyMember (h.at' l).typed (h.at' l).stored hg

/-- The observation of a location that `selL`/`selR` consume, built from the
definition `defL`/`defR` read.  Over an honest store the two ways of resolving
a concrete type selection therefore agree, which is the easy half of the
`obs_conc_admissible` question `PLAN.md` leaves open. -/
def Store.Honest.obs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (h : Store.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G W Γ (.conc l) v (.TTyp a TX TX) :=
  let c := h.member l hg
  ⟨.vcSub (tyOf W l) c.ev (.vcLoc l),
    VcTy.vcSub (Γ := Γ) (p := .conc l) (tyOf W l) VcTy.vcLoc c.typed⟩

/-- The observation `selL`/`selR` consume, built through a `T_Vary` witness
rather than through the store typing: `vcLocAny` widened to the member by
`varyMember`.  The `vcLocAny` counterpart of `Store.Honest.obs`, with no
honesty hypothesis. -/
def varyObs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} {T : Ty σ ([],x)} {ds : Dms σ ([],x)}
    (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G W Γ (.conc l) v (.TTyp a TX TX) :=
  let c := varyMember hd hs hg
  ⟨.vcSub (T.substVr (.conc l)) c.ev (.vcLocAny l T ds),
    VcTy.vcSub (Γ := Γ) (p := .conc l) (T.substVr (.conc l))
      (VcTy.vcLocAny hd hs) c.typed⟩

/-- **Over an honest store `vcLoc` is an instance of `vcLocAny`.**  The
honesty witness at `ℓ` is a pair of `T_Vary` premises at the recorded type
`W ℓ`, and `tyOf W ℓ` is `(W ℓ).substVr (conc ℓ)` by definition, so
`VcTy.vcLocAny` with that witness observes `ℓ` at exactly the type `VcTy.vcLoc`
reads off `W`.  So adding `vcLocAny` added no power over an honest store that
`vcLoc` did not already have at `W ℓ`; what it adds is the observation at
*other* types the literal has, which is what the source's `T_Vary` licenses. -/
def Store.Honest.vcLoc_of_vcLocAny {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : Store.Honest G W) (l : BVar σ .var) :
    VcTy G W Γ (.conc l) (.vcLocAny l (W l) (h.at' l).defs) (tyOf W l) :=
  .vcLocAny (h.at' l).typed (h.at' l).stored

/-! ## Store renaming

The reference's concrete identifiers are absolute positions, "invariant under
context extension" (`dot.v:21-22`), so allocation costs it nothing.  Here a
store weakening is a real renaming of the store scope, and the four judgments
have to be shown stable under it.  The local scope is a separate index and is
never touched, so `scopeUpTo` is unchanged throughout and no scope transport
appears; the only content is that a renamed store's lookups are the renamed
lookups.

`Ctx.renameStore` and the three lemmas about it live here rather than in
`Oopsla16.Context`, so they are written prefix: dot notation would look for
them in `Oopsla16`. -/

/-- Rename every context entry's store scope. -/
def Ctx.renameStore {σ1 σ2 : Sig} :
    {s : Sig} → Ctx σ1 s → Rename σ1 σ2 → Ctx σ2 s
  | _, .nil, _ => .nil
  | _, .cons Γ T, ρ => .cons (Ctx.renameStore Γ ρ) (T.renameStore ρ)

/-- Reading a hypothesis in its own prefix commutes with a store renaming. -/
theorem Ctx.lookupAt_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (Γ : Ctx σ1 s) → (y : BVar s .var) →
    (Ctx.renameStore Γ ρ).lookupAt y = (Γ.lookupAt y).renameStore ρ
  | _, .cons _ _, .here => rfl
  | _, .cons Γ _, .there y => Ctx.lookupAt_renameStore ρ Γ y

/-- Reading a hypothesis commutes with a store renaming. -/
theorem Ctx.lookup_renameStore {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) (Γ : Ctx σ1 s)
    (y : BVar s .var) :
    (Ctx.renameStore Γ ρ).lookup y = (Γ.lookup y).renameStore ρ := by
  show ((Ctx.renameStore Γ ρ).lookupAt y).rename (renameUpTo y)
      = ((Γ.lookupAt y).rename (renameUpTo y)).renameStore ρ
  rw [Ctx.lookupAt_renameStore ρ Γ y]
  exact (Ty.renameStore_rename (Γ.lookupAt y) (renameUpTo y) ρ).symm

/-- Truncating at a variable commutes with a store renaming. -/
theorem Ctx.upTo_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (Γ : Ctx σ1 s) → (y : BVar s .var) →
    (Ctx.renameStore Γ ρ).upTo y = Ctx.renameStore (Γ.upTo y) ρ
  | _, .cons _ _, .here => rfl
  | _, .cons Γ _, .there y => Ctx.upTo_renameStore ρ Γ y

/-- Extending by a hypothesis that does not mention itself — the parameter of
`stp_fun`, `D_Fun`, `stp_bind1` — commutes with a store renaming.  Stated
separately because the weakening has to be pushed past the renaming. -/
theorem Ctx.renameStore_consWeaken {σ1 σ2 s : Sig} (Γ : Ctx σ1 s) (T : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    Ctx.renameStore (Γ.cons T.weaken) ρ
      = (Ctx.renameStore Γ ρ).cons ((T.renameStore ρ).weaken) := by
  show (Ctx.renameStore Γ ρ).cons (T.weaken.renameStore ρ) = _
  rw [Ty.renameStore_weaken]

/-- An optional annotation's agreement with a checked type survives a map;
this is what `D_Fun`'s two `EqSome` premises need (`dot.v:216`). -/
theorem eqSome_map {α β : Type} (f : α → β) {o : Option α} {a : α}
    (h : EqSome o a) : EqSome (o.map f) (f a) := by
  cases h with
  | inl h => exact Or.inl (by rw [h]; rfl)
  | inr h => exact Or.inr (by rw [h]; rfl)

/-- A renaming of the store scope that transports every lookup.  Allocation is
the instance `StoreMap.alloc`. -/
structure StoreMap {σ1 σ2 : Sig} (G1 : Store σ1 σ1) (G2 : Store σ2 σ2) : Type where
  /-- The renaming of locations. -/
  ren : Rename σ1 σ2
  /-- It carries each stored literal to the one at the image location. -/
  lookup : ∀ l : BVar σ1 .var, (G1.lookup l).renameStore ren = G2.lookup (ren.var l)

mutual

/-- `has_type` is stable under a store renaming. -/
def HasType.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {t : Oopsla16.Tm σ1 s} → {T : Ty σ1 s} →
    HasType G1 Γ t T →
    HasType G2 (Ctx.renameStore Γ m.ren) (t.renameStore m.ren) (T.renameStore m.ren)
  | _, _, _, _, .T_Vary (x := y) (ds := ds) (T := T) hd hs => by
      have hs' : (ds.renameStore m.ren).substVr
          ((Vr.conc y).subst (Subst.ofStore m.ren)) = G2.lookup (m.ren.var y) := by
        rw [← Dms.renameStore_substVr, hs]
        exact m.lookup y
      rw [Ty.renameStore_rename, Ty.renameStore_substVr]
      exact .T_Vary (DmsHasType.renameStore m hd) hs'
  | _, _, _, _, .T_Varz => by
      rw [← Ctx.lookup_renameStore]
      exact .T_Varz
  | _, _, _, _, .T_VarPack h => by
      have h' := HasType.renameStore m h
      rw [Ty.renameStore_substVr] at h'
      simp only [Ty.renameStore_TBind]
      exact .T_VarPack h'
  | _, _, _, _, .T_VarUnpack h => by
      have h' := HasType.renameStore m h
      simp only [Ty.renameStore_TBind] at h'
      rw [Ty.renameStore_substVr]
      exact .T_VarUnpack h'
  | _, _, _, _, .T_Obj hd => by
      simp only [Ty.renameStore_TBind, Oopsla16.Tm.renameStore_tobj]
      exact .T_Obj (DmsHasType.renameStore m hd)
  | _, _, _, _, .T_App h1 h2 => by
      have h1' := HasType.renameStore m h1
      simp only [Ty.renameStore_TFun] at h1'
      rw [Ty.renameStore_weaken] at h1'
      exact .T_App h1' (HasType.renameStore m h2)
  | _, _, _, _, .T_AppVar h1 h2 => by
      have h1' := HasType.renameStore m h1
      simp only [Ty.renameStore_TFun] at h1'
      rw [Ty.renameStore_substVr]
      exact .T_AppVar h1' (HasType.renameStore m h2)
  | _, _, _, _, .T_Sub h hs =>
      .T_Sub (HasType.renameStore m h) (Stp.renameStore m hs)

/-- `dms_has_type` is stable under a store renaming.  The positional labels
survive because substitution preserves length (`Dms.length_subst`). -/
def DmsHasType.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {ds : Dms σ1 s} → {T : Ty σ1 s} →
    DmsHasType G1 Γ ds T →
    DmsHasType G2 (Ctx.renameStore Γ m.ren) (ds.renameStore m.ren)
      (T.renameStore m.ren)
  | _, _, _, _, .D_Nil => .D_Nil
  | _, _, _, _, .D_Typ (ds := ds) hd => by
      simp only [Ty.renameStore_TAnd, Ty.renameStore_TTyp,
        Dms.renameStore_dcons, Dm.renameStore_dty]
      rw [← Dms.length_subst ds (Subst.ofStore m.ren)]
      exact .D_Typ (DmsHasType.renameStore m hd)
  | _, _, _, _, .D_Fun (ds := ds) hd ht e1 e2 => by
      have ht' := HasType.renameStore m ht
      rw [Ctx.renameStore_consWeaken] at ht'
      simp only [Ty.renameStore_TAnd, Ty.renameStore_TFun,
        Dms.renameStore_dcons, Dm.renameStore_dfun]
      rw [← Dms.length_subst ds (Subst.ofStore m.ren)]
      exact .D_Fun (DmsHasType.renameStore m hd) ht'
        (eqSome_map _ e1) (eqSome_map _ e2)

/-- `stp` is stable under a store renaming.  The two concrete-selection rules
are the only ones that consult the store, and they consult it through
`Dms.get?`, which commutes with substitution. -/
def Stp.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {T1 T2 : Ty σ1 s} → Stp G1 Γ T1 T2 →
    Stp G2 (Ctx.renameStore Γ m.ren) (T1.renameStore m.ren) (T2.renameStore m.ren)
  | _, _, _, _, .stp_bot => .stp_bot
  | _, _, _, _, .stp_top => .stp_top
  | _, _, _, _, .stp_fun h1 h2 => by
      have h2' := Stp.renameStore m h2
      rw [Ctx.renameStore_consWeaken] at h2'
      simp only [Ty.renameStore_TFun]
      exact .stp_fun (Stp.renameStore m h1) h2'
  | _, _, _, _, .stp_typ h1 h2 => by
      simp only [Ty.renameStore_TTyp]
      exact .stp_typ (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_strong_sel1 (x := y) (l := a) (TX := TX) hg h => by
      have hg' : (G2.lookup (m.ren.var y)).get? a
          = some (.dty (TX.renameStore m.ren)) := by
        rw [← m.lookup y, Dms.get?_subst, hg]; rfl
      simp only [Ty.renameStore_TSel]
      rw [Ty.renameStore_rename]
      exact .stp_strong_sel1 hg' (Stp.renameStore m h)
  | _, _, _, _, .stp_strong_sel2 (x := y) (l := a) (TX := TX) hg h => by
      have hg' : (G2.lookup (m.ren.var y)).get? a
          = some (.dty (TX.renameStore m.ren)) := by
        rw [← m.lookup y, Dms.get?_subst, hg]; rfl
      simp only [Ty.renameStore_TSel]
      rw [Ty.renameStore_rename]
      exact .stp_strong_sel2 hg' (Stp.renameStore m h)
  | _, _, _, _, .stp_sel1 h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TTyp, Ty.renameStore_TBot,
        Ty.renameStore_TSel] at h' ⊢
      rw [Ty.renameStore_rename]
      exact .stp_sel1 h'
  | _, _, _, _, .stp_sel2 h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TTyp, Ty.renameStore_TTop,
        Ty.renameStore_TSel] at h' ⊢
      rw [Ty.renameStore_rename]
      exact .stp_sel2 h'
  | _, _, _, _, .stp_selx => .stp_selx
  | _, _, _, _, .stp_bind1 h => by
      have h' := Stp.renameStore m h
      rw [Ty.renameStore_weaken] at h'
      simp only [Ty.renameStore_TBind]
      exact .stp_bind1 h'
  | _, _, _, _, .stp_bindx h => by
      simp only [Ty.renameStore_TBind]
      exact .stp_bindx (Stp.renameStore m h)
  | _, _, _, _, .stp_and11 h => by
      simp only [Ty.renameStore_TAnd]; exact .stp_and11 (Stp.renameStore m h)
  | _, _, _, _, .stp_and12 h => by
      simp only [Ty.renameStore_TAnd]; exact .stp_and12 (Stp.renameStore m h)
  | _, _, _, _, .stp_and2 h1 h2 => by
      simp only [Ty.renameStore_TAnd]
      exact .stp_and2 (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_or21 h => by
      simp only [Ty.renameStore_TOr]; exact .stp_or21 (Stp.renameStore m h)
  | _, _, _, _, .stp_or22 h => by
      simp only [Ty.renameStore_TOr]; exact .stp_or22 (Stp.renameStore m h)
  | _, _, _, _, .stp_or1 h1 h2 => by
      simp only [Ty.renameStore_TOr]
      exact .stp_or1 (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_trans h1 h2 =>
      .stp_trans (Stp.renameStore m h1) (Stp.renameStore m h2)

/-- `htp` is stable under a store renaming.  The subject and its prefix scope
are untouched, so this is the one judgment where nothing has to be said. -/
def Htp.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {y : BVar s .var} → {T : Ty σ1 (scopeUpTo y)} →
    Htp G1 Γ y T → Htp G2 (Ctx.renameStore Γ m.ren) y (T.renameStore m.ren)
  | _, _, _, _, .htp_var => by
      rw [← Ctx.lookupAt_renameStore]
      exact .htp_var
  | _, _, _, _, .htp_unpack h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TBind] at h'
      rw [Ty.renameStore_substVr]
      exact .htp_unpack h'
  | _, _, _, _, .htp_sub h hs => by
      have hs' := Stp.renameStore m hs
      rw [← Ctx.upTo_renameStore] at hs'
      exact .htp_sub (Htp.renameStore m h) hs'

end

/-! ## A substitution's store part

`Subst.conc` maps locations to locations (`Oopsla16.Structural`): the reference
never substitutes for a concrete variable.  So the store part of *any*
substitution is a renaming of the store scope, and the judgment-renaming
results above apply to it.  That is what carries a `T_Vary` witness — the two
premises of `VcTy.vcLocAny` and `AtomTy.varConcAny` — along a substitution, and
it is what `SubstTyping` and `TermSubst` consume in those clauses.

Written prefix rather than as `Subst.storeRen`, for the reason
`Ctx.renameStore` above gives: dot notation on an `Oopsla16.Subst` would look
for the name in `Oopsla16`. -/

/-- The store part of a substitution, read as a renaming of the store scope. -/
def storeRen {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) : Rename σ1 σ2 where
  var := fun {k} => match k with | .var => θ.conc

/-- On the empty local scope a substitution *is* its store renaming: there is
no local variable left for the two to differ at. -/
theorem atNil_eq_ofStore {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    Subst.atNil θ = Subst.ofStore (s := []) (storeRen θ) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- The same one binder in, which is where a stored literal and its self type
live. -/
theorem atNil_lift_eq_ofStore {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (Subst.atNil θ).lift = Subst.ofStore (s := ([],x)) (storeRen θ) := by
  rw [atNil_eq_ofStore, Subst.lift_ofStore]

/-- **A substitution's store part is a store map**, as soon as the two stores
agree at every location in the sense `SubstTyping.MonoSyn.Ev`'s `defs` field
states.  The agreement is taken here as a bare hypothesis, so that this
definition sits below `SubstTyping` in the import order. -/
def StoreMap.ofSubst {σ1 σ2 s1 s2 : Sig} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    (θ : Subst σ1 s1 σ2 s2)
    (hG : ∀ l : BVar σ1 .var,
      G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ)) :
    StoreMap G G' where
  ren := storeRen θ
  lookup := fun l => by
    show (G.lookup l).renameStore (storeRen θ) = G'.lookup (θ.conc l)
    rw [hG l, atNil_eq_ofStore]

/-- **The typing half of a transported `T_Vary` witness.**  A literal that has
the type `T` under its own self still does after its store scope is renamed by
the substitution's store part. -/
def varyTyped {σ1 σ2 s1 s2 : Sig} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    (θ : Subst σ1 s1 σ2 s2)
    (hG : ∀ l : BVar σ1 .var,
      G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ))
    {T : Ty σ1 ([],x)} {ds : Dms σ1 ([],x)}
    (hd : DmsHasType G (Ctx.nil.cons T) ds T) :
    DmsHasType G' (Ctx.nil.cons (T.renameStore (storeRen θ)))
      (ds.renameStore (storeRen θ)) (T.renameStore (storeRen θ)) :=
  DmsHasType.renameStore (StoreMap.ofSubst θ hG) hd

/-- **The stored half of a transported `T_Vary` witness.**  Instantiating the
renamed literal's self by the image location gives what the image store holds:
`Dms.renameStore_substVr` composed with the store agreement. -/
theorem varyStored {σ1 σ2 s1 s2 : Sig} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    (θ : Subst σ1 s1 σ2 s2)
    (hG : ∀ l : BVar σ1 .var,
      G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ))
    {l : BVar σ1 .var} {ds : Dms σ1 ([],x)}
    (hs : ds.substVr (.conc l) = G.lookup l) :
    (ds.renameStore (storeRen θ)).substVr (.conc (θ.conc l))
      = G'.lookup (θ.conc l) := by
  have h : (G.lookup l).renameStore (storeRen θ) = G'.lookup (θ.conc l) :=
    (StoreMap.ofSubst θ hG).lookup l
  show (ds.renameStore (storeRen θ)).substVr
      ((Vr.conc l).subst (Subst.ofStore (storeRen θ))) = G'.lookup (θ.conc l)
  rw [← Dms.renameStore_substVr, hs, h]

/-- **The type a transported witness reports.**  Substituting the type a
`T_Vary` witness gives at `ℓ` is instantiating the renamed self type at the
image location.  This is the equation the `vcLocAny`/`varConcAny` clauses of
the two substitution theorems close with. -/
theorem varyTy {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) (l : BVar σ1 .var)
    (T : Ty σ1 ([],x)) :
    (T.substVr (.conc l)).subst (Subst.atNil θ)
      = (T.renameStore (storeRen θ)).substVr (.conc (θ.conc l)) := by
  rw [atNil_eq_ofStore]
  exact Ty.renameStore_substVr T (.conc l) (storeRen θ)

/-! ## Allocation

`ST_Obj` (`Semantics.lean`, `dot.v:199-200`) allocates one location and
substitutes it for the literal's self.  Honesty is preserved by extending `W`
with the literal's type, weakened. -/

/-- Allocating one location is a store map: every old lookup is weakened. -/
def StoreMap.alloc {σ : Sig} (G : Store σ σ) (d : Dms (σ,x) []) :
    StoreMap G (G.weakenStore.cons d) where
  ren := Rename.succ
  lookup := fun l => (Store.lookup_renameStore G Rename.succ l).symm

/-- The store typing extended by one newly allocated location. -/
def StoreTy.alloc {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x)) : StoreTy (σ,x)
  | .here => TD.weakenStore
  | .there l => (W l).weakenStore

/-- At the newly allocated location the recorded type is the literal's type,
weakened, with its self instantiated there. -/
theorem tyOf_alloc_here {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x)) :
    tyOf (StoreTy.alloc W TD) .here = TD.weakenStore.substVr (.conc .here) := rfl

/-- At an old location the recorded type is the old one, weakened.  This is the
`tys` field of a store-weakening hypothesis structure, and the target machine's
honesty invariant (`Preservation.MachineStore.Honest.alloc`) consumes it. -/
theorem tyOf_alloc_there {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x))
    (l : BVar σ .var) :
    tyOf (StoreTy.alloc W TD) (.there l) = (tyOf W l).weakenStore := by
  show ((W l).weakenStore).substVr (.conc (.there l))
      = ((W l).substVr (.conc l)).renameStore Rename.succ
  rw [Ty.renameStore_substVr]
  rfl

/-- **Honesty is preserved by allocation.**  The statement mirrors
`Step.ST_Obj`: from a literal that is well typed under its own self over the
old store, the store `G` extended with that literal at its own new location is
honest at `W` extended with the literal's type.  Both halves go through
`DmsHasType.renameStore`, which is where the reference's `dot.v:21-22` is
being paid for. -/
def Store.Honest.alloc {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) {D : Dms σ ([],x)} {TD : Ty σ ([],x)}
    (hd : DmsHasType G (Ctx.nil.cons TD) D TD) :
    Store.Honest (G.weakenStore.cons (D.weakenStore.substVr (.conc .here)))
      (StoreTy.alloc W TD) where
  at' := fun
    | .here =>
        { defs := D.weakenStore
          typed := DmsHasType.renameStore (StoreMap.alloc G _) hd
          stored := rfl }
    | .there l =>
        { defs := (h.at' l).defs.weakenStore
          typed := DmsHasType.renameStore (StoreMap.alloc G _) (h.at' l).typed
          stored := by
            show ((h.at' l).defs.renameStore Rename.succ).substVr
                ((Vr.conc l).subst (Subst.ofStore Rename.succ)) = _
            rw [← Dms.renameStore_substVr, (h.at' l).stored]
            exact (Store.lookup_renameStore G Rename.succ l).symm }

/-! ## An honest store

`Oopsla16.PackingCounterexample` builds a two-object store over which the
reference calculus is well behaved — its unsoundness needs the *extra* rule
`htp_pack`, not the store.  So it is the natural test that `Store.Honest` is
inhabited by something non-trivial: two locations, whose definitions mention
the older one, and whose labels are positional. -/

namespace TwoObjectStore

open Oopsla16.PackingCounterexample
  (A B C D S2 p q Bbody Cbody pDefs qDefs G)

/-- The store typing of the two-object store.  Each entry is the right-nested
intersection `D_Typ` produces: `p` has `C` at label `1` and `B` at label `0`,
`q` has `A` at label `0`, every bound exact, and each spine ends in `⊤`. -/
def W : StoreTy S2
  | .here => .TAnd (.TTyp A D D) .TTop
  | .there .here =>
      .TAnd (.TTyp C Cbody Cbody) (.TAnd (.TTyp B Bbody Bbody) .TTop)

/-- The two-object store is honest at `W`.  Both `stored` obligations are
`rfl`: the stored literals mention no abstract variable, so instantiating the
self changes nothing. -/
def honest : Store.Honest G W where
  at' := fun
    | .here =>
        { defs := qDefs, typed := .D_Typ .D_Nil, stored := rfl }
    | .there .here =>
        { defs := pDefs, typed := .D_Typ (.D_Typ .D_Nil), stored := rfl }

/-- The member lemma fires on it: `p`'s definition of `B`, which `defL`/`defR`
read off the store, is the bounds `tyOf W p` declares. -/
example : Conjunct (tyOf W p) (.TTyp B Bbody Bbody) := honest.member p rfl

/-- And `q`'s definition of `A`. -/
example : Conjunct (tyOf W q) (.TTyp A D D) := honest.member q rfl

/-- So the observation a concrete `selL`/`selR` consumes is available. -/
example :
    (v : Vc S2 []) × VcTy G W (Ctx.nil (σ := S2)) (.conc p) v (.TTyp C Cbody Cbody) :=
  honest.obs p rfl

/-- Allocating a third object — the empty one — keeps the store honest. -/
example :
    Store.Honest ((G.weakenStore).cons ((Dms.dnil (σ := S2) (s := ([],x))).weakenStore.substVr
      (.conc .here))) (StoreTy.alloc W .TTop) :=
  honest.alloc (D := .dnil) (TD := .TTop) .D_Nil

end TwoObjectStore

end FCdotR
