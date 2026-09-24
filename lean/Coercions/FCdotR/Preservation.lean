import Coercions.FCdotR.TermSubst
import Coercions.FCdotR.Erasure
import Coercions.FCdotR.ElaborationErasure

/-!
# Preservation for the FCdotR machine

Every step of a typed machine state over an honest machine store yields a
typed machine state over an honest machine store: for five of the six rules of
`Machine.Step` with **no hypothesis**, and for `app` under one named
hypothesis, `AppInversion` — canonical forms for methods, the receiver-side
instance of the transitivity elimination for closed evidence.  This module does
not prove it; `MethodInversion.appInversion` inhabits it, from
`Inversion.RecordedLit.obsFun`, and `MethodInversion.preservation'` is the
theorem below with the hypothesis gone.

## The two obstacles, and how they are resolved

**1. The machine substitutes roots.**  `Machine`'s `rename` and `app` rules
write an atom's **root** and drop its coercions.  The state that produces is in
general **not** typable as it stands — `OnTheNose` below is a state typed on
the nose whose `rename` step yields an invocation of a bare location, which no
typing admits over an honest store (`MachineStore.Honest.app_var_untypable`).
Substituting the whole atom instead (`FCdot`'s `Tm.adjust` route) does not
help either, because the body's *evidence* mentions the bound variable too: a
`vcVar` at it must become observation evidence for the atom at the bound type,
and that evidence is not a function of the atom's syntax — `cast a e` does not
record its source type, which `vcSub` needs.

So the rules are **kept as they are** (option (b)), and a state is typed when
some typed term and some typed continuation have its **skeleton** (`Erasure`,
*The evidence skeleton*): the same term and frame structure, the same roots and
the same type annotations, with atom wrappers, term-level casts and coercion
frames forgotten.  The typed substitution theorem `TmTy.substEv`, fed by
`MonoSyn.EvA.oneConc` — whose atom field is the **whole** witness atom and
whose observation field is that atom's `AtomTy.toVc` — re-chooses the reduct's
evidence, and `TmTy.substEv_skel` says its output has the skeleton of the
machine's reduct (`Tm.skel_inst`).  The machine reads nothing the skeleton
forgets, erasure factors through it (`Tm.erase_skel`), and `Erasure`'s
`Step.simulate` is untouched.

**2. Honesty of the machine store.**  `MachineStore.Honest G W` is the
target's own invariant: every location holds a definition list with the
skeleton of one typed by `DefsTy`, over the erased store, at `tyOf W ℓ`.  It
is **not** `Store.Honest G.erase W`: that asks for *source* typings of the
erased literals, and allocation could only maintain it by erasing target
typing into source typing, which needs a concrete `selL` to be admissible as
`stp_strong_sel1` (`PLAN.md` §I's `obs_conc_admissible`) and a translation of
target typing derivations back into source ones.  `Inversion.obs_conc_admissible`
now proves the first over an honest source store; the second is not built.  The
two invariants are connected in both directions that are provable:

* `MachineStore.Honest` gives `Store.Honest`'s consequences over `G.erase`
  with the same statements — `member` (type members exact, the only fact the
  consistency argument consumes) and `obs` — and one it cannot give,
  `method`: the stored body typed, which the `app` case runs.
* `Store.Honest` gives `MachineStore.Honest` through elaboration: an honest
  source store whose witnesses are in the fragment is the erasure of the
  honest machine store `Store.Honest.toMachine`, and `StateTy.ofSource` starts
  a typed run from any elaborable source configuration over it.

Throughout, the typing is over `G.erase`, so `TermTyping`'s two location rules
apply to running programs verbatim: `varConc` at `W`'s entry, which honesty
justifies by `DefsTy`, and `varConcAny` at any self type that matches the
erased store's literal.  The erasure annotates every method, so that match
fixes each method member's types.  `MachineStore.Honest.alloc` extends honesty
along `alloc`.

## What is proved

* `TmTy.substEv_skel`, `DefsTy.substEv_skel`: the substitution theorem's
  output has the substituted skeleton.
* `DefsTy.conjunct`, `DefsTy.method`: members of a typed definition list.
* `ContTy`, `StateTy`, `MachineStore.Honest` with `nil`, `member`, `obs`,
  `method`, `alloc`; `ContTy.renameStore`; the views `TmTy.viewLet`,
  `viewNew`, `viewApp`, `viewAtom` and `ContTy.peelLet`.
* The five unconditional cases `StateTy.let_`, `StateTy.castPush`,
  `StateTy.castAtom`, `StateTy.rename`, `StateTy.alloc`, and `StateTy.app`
  under `AppInversion`.
* `ObsFunInversion`, the evidence-level content of `AppInversion` (a closed
  observation of a location at a method type inverts to a method conjunct of
  a location node's type), and `AppInversion.ofObs`, which derives the one
  from the other with no further hypothesis (`LocType.method`,
  `DefsTy.fun?_of_conjunct`, `LitMatch.method`).
* `StateTy.erase_eq`: the typed witness erases to the state it types.
* `preservation`, `preservation_steps`, `preservation_init`, all under
  `AppInversion`, which only the `app` case uses.
* `OnTheNose`: the counterexample to typing the running term itself.
* `Store.Honest.toMachine`, `toMachine_erase`, `toMachine_honest`,
  `StateTy.ofSource`: the bridge from source honesty.

What this module does **not** contain: progress (`Progress`), any proof of
`AppInversion` (that is `MethodInversion.appInversion`, which imports this
module), and any simulation up to the skeleton beyond what `Erasure` already
proves for the let-free fragment (the general one is `Correspondence` and
`Simulation`, which relate states by `Correspondence.Rel`, a property of
skeletons).
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Subst Grows renameNil)

/-! ## The substitution theorem, read on skeletons -/

mutual

/-- **The typed substitution theorem produces the machine's reduct, up to
evidence.**  Whatever evidence and atom wrappers `TmTy.substEv` chooses, its
output term has the skeleton of the input with the substitution applied to
roots and types — which, by `Tm.skel_inst`, is the skeleton of what the
machine's `rename`, `alloc` and `app` rules write. -/
theorem TmTy.substEv_skel {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {t : Tm σ1 s1} {T : Ty σ1 s1} (d : TmTy G W Γ t T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') :
    (TmTy.substEv d E).1.skel = t.skelSubst θ :=
  match d with
  | .atom ha => by
      simp only [TmTy.substEv]
      rcases h : AtomTy.substEv ha E with ⟨b, hroot, hd⟩
      simp only [Tm.skel, Tm.skelSubst, hroot]
  | .new T0 hds => by
      simp only [TmTy.substEv]
      have ih := DefsTy.substEv_skel hds (E.lift T0)
      revert ih
      rcases h : DefsTy.substEv hds (E.lift T0) with ⟨es, hlen, hd⟩
      intro ih
      simp only [Tm.skel, Tm.skelSubst] at ih ⊢
      rw [ih]
  | .app ha hb => by
      simp only [TmTy.substEv]
      rcases h1 : AtomTy.substEv ha E with ⟨ba, hra, hda⟩
      rcases h2 : AtomTy.substEv hb E with ⟨bb, hrb, hdb⟩
      simp only [Tm.skel, Tm.skelSubst, hra, hrb]
  | .let ht hu => by
      simp only [TmTy.substEv, Tm.skel, Tm.skelSubst]
      rw [TmTy.substEv_skel ht E, TmTy.substEv_skel hu]
  | .cast ht _ => by
      simp only [TmTy.substEv, Tm.skel, Tm.skelSubst]
      exact TmTy.substEv_skel ht E

/-- The same, at a definition list. -/
theorem DefsTy.substEv_skel {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {Γ : Ctx σ1 s1} {ds : Defs σ1 s1} {T : Ty σ1 s1} (d : DefsTy G W Γ ds T)
    {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') :
    (DefsTy.substEv d E).defs.skel = ds.skelSubst θ :=
  match d with
  | .dnil => rfl
  | .dty hds => by
      simp only [DefsTy.substEv]
      have ih := DefsTy.substEv_skel hds E
      revert ih
      rcases h : DefsTy.substEv hds E with ⟨es, hlen, hd⟩
      intro ih
      simp only [Defs.skel, Defs.skelSubst] at ih ⊢
      rw [ih]
  | .dfun (S := S0) hds ht => by
      simp only [DefsTy.substEv]
      have ih1 := DefsTy.substEv_skel hds E
      have ih2 := TmTy.substEv_skel ht (Ty.weaken_subst_lift S0 θ ▸ (E.lift S0.weaken))
      revert ih1 ih2
      rcases h1 : DefsTy.substEv hds E with ⟨es, hlen, hd⟩
      rcases h2 : TmTy.substEv ht (Ty.weaken_subst_lift S0 θ ▸ (E.lift S0.weaken))
        with ⟨u, hu⟩
      intro ih1 ih2
      simp only [Defs.skel, Defs.skelSubst] at ih1 ih2 ⊢
      rw [ih1, ih2]

end

/-! ## Members of a typed definition list

`DefsTy` concludes at a right-nested intersection whose conjuncts are the
members in order, exactly as `DmsHasType` does, so the two facts
`StoreTyping` reads off a source literal can be read off a target one. -/

/-- A typed definition list's type declares each of its type members exactly:
the target counterpart of `DmsHasType.conjunct`. -/
def DefsTy.conjunct {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    {ds : Defs σ s} → {T : Ty σ s} → DefsTy G W Γ ds T → {a : Lb} →
    {TX : Ty σ s} → ds.ty? a = some TX → Conjunct T (.TTyp a TX TX)
  | _, _, .dnil, _, _, hg => by simp [Defs.ty?] at hg
  | _, _, .dty (T := T0) (ds := ds) hds, a, TX, hg => by
      have hg' : (if a = ds.length then some T0 else ds.ty? a) = some TX := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'
        have hT : T0 = TX := by simpa using hg'
        subst hT
        subst h
        exact .here
      · rw [if_neg h] at hg'
        exact .there (DefsTy.conjunct hds hg')
  | _, _, .dfun (ds := ds) hds _, a, TX, hg => by
      have hg' : (if a = ds.length then none else ds.ty? a) = some TX := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'
        cases hg'
      · rw [if_neg h] at hg'
        exact .there (DefsTy.conjunct hds hg')

/-- A typed definition list's type declares each of its methods, and the
method's body is typed under its parameter.  The second half has no source
counterpart in `StoreTyping`: it is what the `app` case runs. -/
def DefsTy.method {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    {ds : Defs σ s} → {T : Ty σ s} → DefsTy G W Γ ds T → {a : Lb} →
    {S : Ty σ s} → {U : Ty σ (s,x)} → {t : Tm σ (s,x)} →
    ds.fun? a = some (S, U, t) →
    Conjunct T (.TFun a S U) × TmTy G W (Γ.cons S.weaken) t U
  | _, _, .dnil, _, _, _, _, hf => by simp [Defs.fun?] at hf
  | _, _, .dty (ds := ds) hds, a, S, U, t, hf => by
      have hf' : (if a = ds.length then none else ds.fun? a) = some (S, U, t) := hf
      by_cases h : a = ds.length
      · rw [if_pos h] at hf'
        cases hf'
      · rw [if_neg h] at hf'
        exact ⟨.there (DefsTy.method hds hf').1, (DefsTy.method hds hf').2⟩
  | _, _, .dfun (S := S0) (U := U0) (t := t0) (ds := ds) hds ht, a, S, U, t, hf => by
      have hf' : (if a = ds.length then some (S0, U0, t0) else ds.fun? a)
          = some (S, U, t) := hf
      by_cases h : a = ds.length
      · rw [if_pos h] at hf'
        simp only [Option.some.injEq, Prod.mk.injEq] at hf'
        obtain ⟨rfl, rfl, rfl⟩ := hf'
        subst h
        exact ⟨.here, ht⟩
      · rw [if_neg h] at hf'
        exact ⟨.there (DefsTy.method hds hf').1, (DefsTy.method hds hf').2⟩

/-! ## Continuations -/

/-- `K : S ⇒ U`: the continuation accepts a value of type `S` and delivers one
of type `U`.  A `let` frame's body is typed under the accepted type, as
`TmTy.let` types it; a coercion frame is an inclusion.  Frames are innermost
last, as in `Machine.Cont`. -/
inductive ContTy {σ : Sig} (G : Store σ σ) (W : StoreTy σ) :
    Cont σ → Ty σ [] → Ty σ [] → Type where
  /-- The empty continuation delivers what it accepts. -/
  | nil {T : Ty σ []} : ContTy G W .nil T T
  /-- `let x = □ in u`, then `K`. -/
  | «let» {K : Cont σ} {u : Tm σ ([],x)} {S T U : Ty σ []} :
      TmTy G W (Ctx.nil.cons S.weaken) u T.weaken → ContTy G W K T U →
      ContTy G W (K ▹ .let u) S U
  /-- `□ ▸ e`, then `K`. -/
  | cast {K : Cont σ} {e : Le σ []} {S T U : Ty σ []} :
      LeTy G W Ctx.nil e S T → ContTy G W K T U → ContTy G W (K ▹ .cast e) S U

/-! ## The machine store -/

/-- What honesty asks of one location of the machine store: a definition list
typed, over the erased store, at the type the store typing records, and with
the skeleton of what the location holds.  It is *after* the self has been
instantiated, because the machine stores literals that way; the source-level
`HonestAt` is before. -/
structure MachineStore.HonestAt {σ : Sig} (G : MachineStore σ σ) (W : StoreTy σ)
    (l : BVar σ .var) : Type where
  /-- A typed definition list … -/
  defs : Defs σ []
  /-- … at the recorded type … -/
  typed : DefsTy G.erase W Ctx.nil defs (tyOf W l)
  /-- … with the skeleton of the stored one. -/
  skel : defs.skel = (G.lookup l).skel

/-- **The machine store is honest**: every location's stored literal has, up
to evidence, the type the store typing records.  The target's own invariant;
see the module header for why it is not `Store.Honest G.erase W`. -/
structure MachineStore.Honest {σ : Sig} (G : MachineStore σ σ) (W : StoreTy σ) :
    Type where
  /-- The witness at each location. -/
  at' : (l : BVar σ .var) → MachineStore.HonestAt G W l

/-- The empty store is honest at any store typing: it has no locations. -/
def MachineStore.Honest.nil (W : StoreTy []) :
    MachineStore.Honest (MachineStore.nil : MachineStore [] []) W :=
  ⟨fun l => nomatch l⟩

/-- **The store typing agrees with what `defL`/`defR` read**, over the machine
store: `Store.Honest.member`'s statement verbatim at `G.erase`.  So every
argument that consumes only exactness of type members — which is all the
consistency argument consumes — runs over a machine store. -/
def MachineStore.Honest.member {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.erase.lookup l).get? a = some (.dty TX)) :
    Conjunct (tyOf W l) (.TTyp a TX TX) :=
  DefsTy.conjunct (h.at' l).typed (Defs.ty?_of_erase _ a (by
    rw [Defs.erase_of_skel (h.at' l).skel, MachineStore.erase_lookup]
    exact hg))

/-- The observation `selL`/`selR` consume, built from the definition
`defL`/`defR` read: `Store.Honest.obs` over the machine store. -/
def MachineStore.Honest.obs {σ s : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : MachineStore.Honest G W) (l : BVar σ .var) {a : Lb}
    {TX : Ty σ []} (hg : (G.erase.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G.erase W Γ (.conc l) v (.TTyp a TX TX) :=
  let c := h.member l hg
  ⟨.vcSub (tyOf W l) c.ev (.vcLoc l),
    VcTy.vcSub (Γ := Γ) (p := .conc l) (tyOf W l) VcTy.vcLoc c.typed⟩

/-- **A stored method is declared at the recorded type, and its body is
typed**, up to evidence.  This is what `Store.Honest` cannot give — it types
the *erased* body in the source — and what the `app` case runs. -/
def MachineStore.Honest.method {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) (l : BVar σ .var) {a : Lb} {S : Ty σ []}
    {U : Ty σ ([],x)} {t : Tm σ ([],x)} (hf : (G.lookup l).fun? a = some (S, U, t)) :
    Conjunct (tyOf W l) (.TFun a S U) ×
      ((t0 : Tm σ ([],x)) × TmTy G.erase W (Ctx.nil.cons S.weaken) t0 U ×
        PLift (t0.skel = t.skel)) := by
  have hd := (h.at' l).typed
  have hs := (h.at' l).skel
  generalize (h.at' l).defs = d at hd hs
  cases hf0 : d.fun? a with
  | none =>
      exfalso
      obtain ⟨t1, h1, _⟩ := Defs.fun?_of_skel hs hf
      rw [hf0] at h1
      cases h1
  | some p =>
      obtain ⟨S', U', t0⟩ := p
      have heq : S' = S ∧ U' = U ∧ t0.skel = t.skel := by
        obtain ⟨t1, h1, h2⟩ := Defs.fun?_of_skel hs hf
        rw [hf0] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        exact ⟨rfl, rfl, h2⟩
      obtain ⟨rfl, rfl, h3⟩ := heq
      exact ⟨(DefsTy.method hd hf0).1, ⟨t0, (DefsTy.method hd hf0).2, ⟨h3⟩⟩⟩

/-! ## Hypothesis structures for the machine's substitutions

Every substitution the machine performs is one of three: a location for the
single binder of `([],x)` (`rename`, `app`, and `alloc`'s self), and a store
weakening (`alloc`).  Each gets its `MonoSyn.EvA` here, once. -/

/-- On the empty local scope, instantiating a binder does nothing: there is no
binder left, and locations are untouched. -/
theorem atNil_oneConc {σ : Sig} (l : BVar σ .var) :
    Subst.atNil (Subst.one (σ := σ) (s := []) (.conc l)) = Subst.id :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- On the empty local scope, a store renaming's action is itself. -/
theorem atNil_ofStore' {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    Subst.atNil (Subst.ofStore (s := []) ρ) = Subst.ofStore (s := []) ρ :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- **Instantiating the self or the parameter by a location**, from a closed
atom rooted there at the instantiated type.  The atom is the image, and its
observation evidence (`AtomTy.toVc`) is the image's evidence — so the atom's
casts reach every use of the binder, in the terms *and* in the evidence. -/
def MonoSyn.EvA.oneConcAt {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (X : Ty σ ([],x)) {l : BVar σ .var} {a : Atom σ []} (hroot : a.root = .conc l)
    (ha : AtomTy G W Ctx.nil a (X.substVr (.conc l))) :
    MonoSyn.EvA G W (Ctx.nil.cons X) (MonoSyn.oneConc l) G W Ctx.nil where
  ev :=
    { defs := fun l' => by
        show G.lookup l' = (G.lookup l').subst (Subst.atNil (Subst.one (Vr.conc l)))
        rw [atNil_oneConc, Oopsla16.Dms.subst_id]
      tys := fun l' => by
        show tyOf W l' = (tyOf W l').subst (Subst.atNil (Subst.one (Vr.conc l)))
        rw [atNil_oneConc, Oopsla16.Ty.subst_id]
      vc := fun
        | .here => by
            obtain ⟨v, hv⟩ := ha.toVc
            have hl : a.rootLoc = l := by
              show locOf a.root = l
              rw [hroot]
              rfl
            rw [hl] at hv
            exact ⟨v, hv⟩
        | .there y => nomatch y }
  atom := fun
    | .here => ⟨a, hroot, by
        show AtomTy G W Ctx.nil a
          (((Ctx.nil.cons X).lookup .here).subst (Subst.one (Vr.conc l)))
        rw [Ctx.lookup_cons_here]
        exact ha⟩
    | .there y => nomatch y

/-- The instance at a parameter that does not mention itself: a `let`-bound
variable or a method parameter. -/
def MonoSyn.EvA.oneConc {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (S : Ty σ [])
    {l : BVar σ .var} {a : Atom σ []} (hroot : a.root = .conc l)
    (ha : AtomTy G W Ctx.nil a S) :
    MonoSyn.EvA G W (Ctx.nil.cons S.weaken) (MonoSyn.oneConc l) G W Ctx.nil :=
  MonoSyn.EvA.oneConcAt S.weaken hroot
    (by rw [Oopsla16.Ty.substVr_weaken]; exact ha)

/-- **A store renaming at the empty local scope**, from the two store
agreements.  There is no variable, so neither variable field has anything to
supply. -/
def MonoSyn.EvA.store {σ1 σ2 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} (ρ : Rename σ1 σ2)
    (hG : ∀ l, G'.lookup (ρ.var l) = (G.lookup l).renameStore ρ)
    (hW : ∀ l, tyOf W' (ρ.var l) = (tyOf W l).renameStore ρ) :
    MonoSyn.EvA G W Ctx.nil (MonoSyn.ofStore (s := []) ρ) G' W' Ctx.nil where
  ev :=
    { defs := fun l => by
        show G'.lookup (ρ.var l) = (G.lookup l).subst (Subst.atNil (Subst.ofStore ρ))
        rw [atNil_ofStore', hG l]
      tys := fun l => by
        show tyOf W' (ρ.var l) = (tyOf W l).subst (Subst.atNil (Subst.ofStore ρ))
        rw [atNil_ofStore', hW l]
      vc := fun y => nomatch y }
  atom := fun y => nomatch y

/-! ## Allocation -/

/-- **Allocation's store weakening carries a hypothesis structure**, from the
old store to the extended one, at the extended store typing. -/
def MachineStore.allocEv {σ : Sig} (G : MachineStore σ σ) (W : StoreTy σ)
    (T : Ty σ ([],x)) (d : Defs (σ,x) []) :
    MonoSyn.EvA G.erase W Ctx.nil (MonoSyn.ofStore (s := []) Rename.succ)
      (G.weakenStore.cons d).erase (StoreTy.alloc W T) Ctx.nil :=
  MonoSyn.EvA.store Rename.succ
    (fun l => by
      show (G.weakenStore.erase).lookup l = _
      rw [MachineStore.erase_renameStore, Oopsla16.Store.lookup_renameStore])
    (fun l => tyOf_alloc_there W T l)

/-- **Honesty is preserved by allocation.**  The statement mirrors
`Machine.Step.alloc`: from a literal typed under its own self — up to
evidence, as the running term's typing gives it — the store extended with that
literal, weakened and instantiated at its new location, is honest at the store
typing extended by the literal's type.  The new location's witness is the
literal's typing moved in two substitutions, store weakening and then the
self's instantiation by `var (conc here)`, typed by `varConc`; the old
locations' witnesses are store-weakened. -/
def MachineStore.Honest.alloc {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) {T : Ty σ ([],x)} {ds ds0 : Defs σ ([],x)}
    (hd : DefsTy G.erase W (Ctx.nil.cons T) ds0 T) (hsk : ds0.skel = ds.skel) :
    MachineStore.Honest (G.weakenStore.cons (ds.weakenStore.inst .base .here))
      (StoreTy.alloc W T) where
  at' := fun
    | .here => by
        have E1 := MachineStore.allocEv G W T (ds.weakenStore.inst .base .here)
        have r1 := DefsTy.substEv hd (E1.lift T)
        have hs1 := DefsTy.substEv_skel hd (E1.lift T)
        have hX : T.subst (Subst.ofStore (s := []) Rename.succ).lift = T.weakenStore :=
          by rw [Subst.lift_ofStore]
        have hvar : AtomTy (G.weakenStore.cons (ds.weakenStore.inst .base .here)).erase
            (StoreTy.alloc W T) Ctx.nil (.var (.conc .here))
            ((T.subst (Subst.ofStore (s := []) Rename.succ).lift).substVr (.conc .here)) := by
          rw [hX]
          have hv := AtomTy.varConc (G := (G.weakenStore.cons
            (ds.weakenStore.inst .base .here)).erase) (W := StoreTy.alloc W T)
            (Γ := Ctx.nil) (l := .here)
          rw [Oopsla16.Ty.rename_renameNil_nil] at hv
          exact hv
        have E2 := MonoSyn.EvA.oneConcAt _ rfl hvar
        refine ⟨(DefsTy.substEv (DefsTy.substEv hd (E1.lift T)).deriv E2).defs, ?_, ?_⟩
        · have hd2 := (DefsTy.substEv (DefsTy.substEv hd (E1.lift T)).deriv E2).deriv
          have e : (T.subst (Subst.ofStore (s := []) Rename.succ).lift).subst
              (Subst.one (Vr.conc BVar.here)) = tyOf (StoreTy.alloc W T) .here := by
            rw [hX]; rfl
          rw [← e]
          exact hd2
        · rw [DefsTy.substEv_skel, ← Defs.skelSubst_skel, DefsTy.substEv_skel,
            Defs.skelSubst_congr hsk]
          show _ = (Defs.inst (ds.weakenStore) .base .here).skel
          rw [Defs.skel_inst,
            ← Defs.skelSubst_skel (ds.weakenStore), Defs.skel_renameStore,
            Subst.lift_ofStore]
          rfl
    | .there l => by
        have E1 := MachineStore.allocEv G W T (ds.weakenStore.inst .base .here)
        refine ⟨(DefsTy.substEv (h.at' l).typed E1).defs, ?_, ?_⟩
        · have hd1 := (DefsTy.substEv (h.at' l).typed E1).deriv
          rw [tyOf_alloc_there]
          exact hd1
        · rw [DefsTy.substEv_skel, Defs.skelSubst_congr (h.at' l).skel,
            ← Defs.skel_renameStore]
          show _ = (G.weakenStore.lookup l).skel
          rw [MachineStore.lookup_renameStore]

/-- **A continuation's typing survives a store renaming**, up to evidence:
each `let` body by the term substitution theorem, each coercion by the
evidence one.  Allocation is the instance. -/
def ContTy.renameStore {σ1 σ2 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {ρ : Rename σ1 σ2}
    (E : MonoSyn.EvA G W Ctx.nil (MonoSyn.ofStore (s := []) ρ) G' W' Ctx.nil) :
    {K : Cont σ1} → {S U : Ty σ1 []} → ContTy G W K S U →
    (K' : Cont σ2) × ContTy G' W' K' (S.renameStore ρ) (U.renameStore ρ) ×
      PLift (K'.skel = K.skelStore ρ)
  | _, _, _, .nil => ⟨.nil, .nil, ⟨rfl⟩⟩
  | _, _, _, .let (u := u) (S := S) (T := T) du dK =>
      let r := ContTy.renameStore E dK
      let E' : MonoSyn.EvA G W (Ctx.nil.cons S.weaken) (MonoSyn.ofStore ρ).lift G' W'
          (Ctx.nil.cons (S.renameStore ρ).weaken) :=
        Ty.weaken_subst_lift S (Subst.ofStore ρ) ▸ E.lift S.weaken
      ⟨r.1 ▹ .let (TmTy.substEv du E').1,
        .let (Ty.weaken_subst_lift T (Subst.ofStore ρ) ▸ (TmTy.substEv du E').2) r.2.1,
        ⟨by
          show Cont.skel r.1 ▹ .let (TmTy.substEv du E').1.skel = _
          rw [r.2.2.down, TmTy.substEv_skel, Subst.lift_ofStore]
          rfl⟩⟩
  | _, _, _, .cast (e := e) de dK =>
      let r := ContTy.renameStore E dK
      ⟨r.1 ▹ .cast (LeTy.substEv de E.ev).1, .cast (LeTy.substEv de E.ev).2 r.2.1,
        ⟨r.2.2.down⟩⟩

/-! ## Typed states -/

/-- A type moved along a store growth: one store weakening per allocation.
It is what a result type becomes after a step, and it is the identity along
`Grows.refl` definitionally. -/
def Ty.alongGrows {σ1 s : Sig} : {σ2 : Sig} → Grows σ1 σ2 → Ty σ1 s → Ty σ2 s
  | _, .refl, T => T
  | _, .snoc g, T => (Ty.alongGrows g T).weakenStore

/-- Moving along a composite growth is moving twice. -/
theorem Ty.alongGrows_comp {σ1 σ2 s : Sig} (g : Grows σ1 σ2) (T : Ty σ1 s) :
    {σ3 : Sig} → (h : Grows σ2 σ3) →
    Ty.alongGrows (g.comp h) T = Ty.alongGrows h (Ty.alongGrows g T)
  | _, .refl => rfl
  | _, .snoc h => by
      show (Ty.alongGrows (g.comp h) T).weakenStore = _
      rw [Ty.alongGrows_comp g T h]
      rfl

/-- **A typed machine state, up to evidence.**  Over the erased store and at
the store typing `W`, some term typed at `ty` has the running term's skeleton,
and some continuation `ty ⇒ U` has the continuation's skeleton.  The module
header says why the running term itself cannot be asked to be typed. -/
structure StateTy {σ : Sig} (st : State σ) (W : StoreTy σ) (U : Ty σ []) : Type where
  /-- The type of the running term. -/
  ty : Ty σ []
  /-- A typed term … -/
  tm : Tm σ []
  /-- … its derivation … -/
  tmTy : TmTy st.G.erase W Ctx.nil tm ty
  /-- … with the running term's skeleton. -/
  tmSkel : tm.skel = st.t.skel
  /-- A typed continuation … -/
  cont : Cont σ
  /-- … its derivation … -/
  contTy : ContTy st.G.erase W cont ty U
  /-- … with the continuation's skeleton. -/
  contSkel : cont.skel = st.K.skel

/-- A closed term typed over the empty store starts a typed run, on the nose.
Elaboration (`Elaboration.elabHasType`) produces such terms. -/
def StateTy.init {W : StoreTy []} {t : Tm [] []} {T : Ty [] []}
    (d : TmTy Store.nil W Ctx.nil t T) :
    StateTy ⟨MachineStore.nil, .nil, t⟩ W T :=
  ⟨T, t, d, rfl, .nil, .nil, rfl⟩

/-- The `FunctionField` object literal of `TermTyping` starts a typed run. -/
example : StateTy ⟨MachineStore.nil, .nil, FunctionFieldObject.literal.1⟩
    FunctionFieldObject.W (.TBind FunctionFieldObject.Sexact) :=
  StateTy.init FunctionFieldObject.literal.2

/-! ## Peeling coercions

A typed witness may carry coercions where the running term has none: the
skeleton forgets term-level casts and coercion frames.  These two recursions
collect them into one inclusion, exposing the node the machine is about to
consume. -/

/-- A typed term with its outermost casts collected: the first node that is
not a cast, typed, and an inclusion from its type to the whole term's. -/
structure TmTy.Core {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (t : Tm σ [])
    (T : Ty σ []) : Type where
  /-- The first node that is not a cast. -/
  core : Tm σ []
  /-- Its type. -/
  ty : Ty σ []
  /-- Its derivation. -/
  deriv : TmTy G W Ctx.nil core ty
  /-- The collected casts, as one inclusion. -/
  le : Le σ []
  /-- Typed. -/
  leTy : LeTy G W Ctx.nil le ty T
  /-- Casts are invisible to the skeleton. -/
  skel : core.skel = t.skel
  /-- It is not a cast. -/
  notCast : ∀ (t' : Tm σ []) (e' : Le σ []), core ≠ .cast t' e'

/-- Collect a typed term's outermost casts. -/
def TmTy.core {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {t : Tm σ []} → {T : Ty σ []} → TmTy G W Ctx.nil t T → TmTy.Core G W t T
  | _, T, .atom ha =>
      ⟨_, T, .atom ha, .refl T, .refl T, rfl, fun _ _ h => by cases h⟩
  | _, _, .new T0 hds =>
      ⟨_, _, .new T0 hds, .refl _, .refl _, rfl, fun _ _ h => by cases h⟩
  | _, _, .app ha hb =>
      ⟨_, _, .app ha hb, .refl _, .refl _, rfl, fun _ _ h => by cases h⟩
  | _, T, .let ht hu =>
      ⟨_, T, .let ht hu, .refl T, .refl T, rfl, fun _ _ h => by cases h⟩
  | _, _, .cast (S := S) ht he =>
      let c := TmTy.core ht
      ⟨c.core, c.ty, c.deriv, .trans S c.le _, .trans S c.leTy he, c.skel, c.notCast⟩

/-- A node that is not a cast, with the skeleton of a `let`, is a `let`. -/
theorem Tm.skel_eq_let {σ s : Sig} {c : Tm σ s}
    (hnc : ∀ (t' : Tm σ s) (e' : Le σ s), c ≠ .cast t' e') {t : Tm σ s}
    {u : Tm σ (s,x)} (h : c.skel = (Tm.let t u).skel) :
    ∃ t0 u0, c = .let t0 u0 ∧ t0.skel = t.skel ∧ u0.skel = u.skel := by
  cases c with
  | «let» t0 u0 =>
      simp only [Tm.skel, Tm.let.injEq] at h
      exact ⟨t0, u0, rfl, h.1, h.2⟩
  | cast t' e' => exact absurd rfl (hnc t' e')
  | atom _ => simp [Tm.skel] at h
  | new _ _ => simp [Tm.skel] at h
  | app _ _ _ => simp [Tm.skel] at h

/-- A node that is not a cast, with the skeleton of an allocation, is an
allocation at the same self type. -/
theorem Tm.skel_eq_new {σ s : Sig} {c : Tm σ s}
    (hnc : ∀ (t' : Tm σ s) (e' : Le σ s), c ≠ .cast t' e') {T : Ty σ (s,x)}
    {ds : Defs σ (s,x)} (h : c.skel = (Tm.new T ds).skel) :
    ∃ ds0, c = .new T ds0 ∧ ds0.skel = ds.skel := by
  cases c with
  | new T0 ds0 =>
      simp only [Tm.skel, Tm.new.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨ds0, rfl, h2⟩
  | cast t' e' => exact absurd rfl (hnc t' e')
  | atom _ => simp [Tm.skel] at h
  | «let» _ _ => simp [Tm.skel] at h
  | app _ _ _ => simp [Tm.skel] at h

/-- A node that is not a cast, with the skeleton of an invocation, is an
invocation of the same label at atoms with the same roots. -/
theorem Tm.skel_eq_app {σ s : Sig} {c : Tm σ s}
    (hnc : ∀ (t' : Tm σ s) (e' : Le σ s), c ≠ .cast t' e') {a b : Atom σ s}
    {l : Lb} (h : c.skel = (Tm.app a l b).skel) :
    ∃ a0 b0, c = .app a0 l b0 ∧ a0.root = a.root ∧ b0.root = b.root := by
  cases c with
  | app a0 l0 b0 =>
      simp only [Tm.skel, Tm.app.injEq, Atom.var.injEq] at h
      obtain ⟨h1, rfl, h3⟩ := h
      exact ⟨a0, b0, rfl, h1, h3⟩
  | cast t' e' => exact absurd rfl (hnc t' e')
  | atom _ => simp [Tm.skel] at h
  | «let» _ _ => simp [Tm.skel] at h
  | new _ _ => simp [Tm.skel] at h

/-- A node that is not a cast, with the skeleton of an atom, is an atom with
the same root. -/
theorem Tm.skel_eq_atom {σ s : Sig} {c : Tm σ s}
    (hnc : ∀ (t' : Tm σ s) (e' : Le σ s), c ≠ .cast t' e') {a : Atom σ s}
    (h : c.skel = (Tm.atom a).skel) : ∃ a0, c = .atom a0 ∧ a0.root = a.root := by
  cases c with
  | atom a0 =>
      simp only [Tm.skel, Tm.atom.injEq, Atom.var.injEq] at h
      exact ⟨a0, rfl, h⟩
  | cast t' e' => exact absurd rfl (hnc t' e')
  | «let» _ _ => simp [Tm.skel] at h
  | new _ _ => simp [Tm.skel] at h
  | app _ _ _ => simp [Tm.skel] at h

/-- A typed continuation whose skeleton begins with a `let` frame, with the
coercion frames in front of that frame collected into one inclusion. -/
structure ContTy.LetHead {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (S U : Ty σ [])
    (K1 : Cont σ) (u1 : Tm σ ([],x)) : Type where
  /-- The type the `let` frame binds. -/
  bound : Ty σ []
  /-- The collected coercion frames, as one inclusion. -/
  le : Le σ []
  /-- Typed. -/
  leTy : LeTy G W Ctx.nil le S bound
  /-- The `let` body. -/
  body : Tm σ ([],x)
  /-- Its result type. -/
  res : Ty σ []
  /-- Its derivation. -/
  bodyTy : TmTy G W (Ctx.nil.cons bound.weaken) body res.weaken
  /-- With the skeleton of the frame's body. -/
  bodySkel : body.skel = u1.skel
  /-- The rest of the continuation. -/
  rest : Cont σ
  /-- Typed. -/
  restTy : ContTy G W rest res U
  /-- With the skeleton of the frame's continuation. -/
  restSkel : rest.skel = K1.skel

/-- Collect the coercion frames in front of a continuation's first `let`
frame. -/
def ContTy.peelLet {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {K : Cont σ} → {S U : Ty σ []} → ContTy G W K S U → {K1 : Cont σ} →
    {u1 : Tm σ ([],x)} → K.skel = (K1 ▹ .let u1).skel → ContTy.LetHead G W S U K1 u1
  | _, _, _, .nil, _, _, h => absurd h (by simp [Cont.skel])
  | _, S, _, .let (K := K0) (u := u) (T := T) du dK, K1, u1, h => by
      simp only [Cont.skel, Cont.cons.injEq, Frame.let.injEq] at h
      exact ⟨S, .refl S, .refl S, u, T, du, h.2, K0, dK, h.1⟩
  | _, _, _, .cast (T := T) (e := e) de dK, K1, u1, h =>
      let r := ContTy.peelLet dK h
      ⟨r.bound, .trans T e r.le, .trans T de r.leTy, r.body, r.res, r.bodyTy,
        r.bodySkel, r.rest, r.restTy, r.restSkel⟩

/-! ## Views of a typed witness

`StateTy` hands over *some* typed term with the running term's skeleton.  Each
rule of the machine consumes one node, and a view exposes that node's
sub-derivations, with the witness's outer casts collected into one inclusion
(`TmTy.core` does the collecting alone; a view also opens the node).  The
skeleton fixes the node, so every other constructor is refuted by the
skeleton equation, and a view is total on the witnesses it is asked about. -/

/-- A typed witness with the skeleton of `let t u`, opened. -/
structure LetView {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (t : Tm σ [])
    (u : Tm σ ([],x)) (T : Ty σ []) : Type where
  /-- The type the `let` binds. -/
  bound : Ty σ []
  /-- The `let`'s own result type. -/
  res : Ty σ []
  /-- The bound term … -/
  tm : Tm σ []
  /-- … typed … -/
  tmTy : TmTy G W Ctx.nil tm bound
  /-- … with the skeleton of `t`. -/
  tmSkel : tm.skel = t.skel
  /-- The body … -/
  body : Tm σ ([],x)
  /-- … typed under the bound variable … -/
  bodyTy : TmTy G W (Ctx.nil.cons bound.weaken) body res.weaken
  /-- … with the skeleton of `u`. -/
  bodySkel : body.skel = u.skel
  /-- The witness's outer casts, collected. -/
  le : Le σ []
  /-- Typed. -/
  leTy : LeTy G W Ctx.nil le res T

/-- Open a typed witness with the skeleton of a `let`. -/
def TmTy.viewLet {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {t : Tm σ []}
    {u : Tm σ ([],x)} : {tm : Tm σ []} → {T : Ty σ []} → TmTy G W Ctx.nil tm T →
    tm.skel = (Tm.let t u).skel → LetView G W t u T
  | _, _, .let (S := S0) (T := T0) ht hu, h => by
      simp only [Tm.skel, Tm.let.injEq] at h
      exact ⟨S0, T0, _, ht, h.1, _, hu, h.2, .refl T0, .refl T0⟩
  | _, _, .cast (S := S0) (e := e) ht he, h =>
      let v := TmTy.viewLet ht h
      { v with le := .trans S0 v.le e, leTy := .trans S0 v.leTy he }
  | _, _, .atom _, h => absurd h (by simp [Tm.skel])
  | _, _, .new _ _, h => absurd h (by simp [Tm.skel])
  | _, _, .app _ _, h => absurd h (by simp [Tm.skel])

/-- A typed witness with the skeleton of `new T ds`, opened.  The self type is
kept by the skeleton, so it is the running term's own. -/
structure NewView {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (T0 : Ty σ ([],x))
    (ds : Defs σ ([],x)) (T : Ty σ []) : Type where
  /-- The literal's definitions … -/
  defs : Defs σ ([],x)
  /-- … typed under the self … -/
  defsTy : DefsTy G W (Ctx.nil.cons T0) defs T0
  /-- … with the skeleton of `ds`. -/
  defsSkel : defs.skel = ds.skel
  /-- The witness's outer casts, collected. -/
  le : Le σ []
  /-- Typed. -/
  leTy : LeTy G W Ctx.nil le (.TBind T0) T

/-- Open a typed witness with the skeleton of an allocation. -/
def TmTy.viewNew {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {T0 : Ty σ ([],x)}
    {ds : Defs σ ([],x)} : {tm : Tm σ []} → {T : Ty σ []} → TmTy G W Ctx.nil tm T →
    tm.skel = (Tm.new T0 ds).skel → NewView G W T0 ds T
  | _, _, .new T1 hds, h => by
      simp only [Tm.skel, Tm.new.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨_, hds, h2, .refl _, .refl _⟩
  | _, _, .cast (S := S0) (e := e) ht he, h =>
      let v := TmTy.viewNew ht h
      { v with le := .trans S0 v.le e, leTy := .trans S0 v.leTy he }
  | _, _, .atom _, h => absurd h (by simp [Tm.skel])
  | _, _, .let _ _, h => absurd h (by simp [Tm.skel])
  | _, _, .app _ _, h => absurd h (by simp [Tm.skel])

/-- A typed witness with the skeleton of `app a l b`, opened: the receiver at a
method type, the argument at its domain, both rooted where the running term's
operands are. -/
structure AppView {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (a : Atom σ [])
    (l : Lb) (b : Atom σ []) (T : Ty σ []) : Type where
  /-- The receiver atom … -/
  fn : Atom σ []
  /-- The argument atom … -/
  arg : Atom σ []
  /-- The method's domain … -/
  dom : Ty σ []
  /-- … and codomain, as the receiver's type declares them. -/
  cod : Ty σ ([],x)
  /-- The receiver is typed at the method type. -/
  fnTy : AtomTy G W Ctx.nil fn (.TFun l dom cod)
  /-- The argument is typed at the domain. -/
  argTy : AtomTy G W Ctx.nil arg dom
  /-- The receiver is rooted where the running term's is. -/
  fnRoot : fn.root = a.root
  /-- So is the argument. -/
  argRoot : arg.root = b.root
  /-- The witness's outer casts, collected. -/
  le : Le σ []
  /-- Typed, from the codomain at the argument's root. -/
  leTy : LeTy G W Ctx.nil le (cod.substVr b.root) T

/-- Open a typed witness with the skeleton of an invocation. -/
def TmTy.viewApp {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {a b : Atom σ []}
    {l : Lb} : {tm : Tm σ []} → {T : Ty σ []} → TmTy G W Ctx.nil tm T →
    tm.skel = (Tm.app a l b).skel → AppView G W a l b T
  | _, _, .app (b := b0) (U := U0) ha hb, h => by
      simp only [Tm.skel, Tm.app.injEq, Atom.var.injEq] at h
      obtain ⟨h1, rfl, h3⟩ := h
      refine ⟨_, _, _, U0, ha, hb, h1, h3, .refl (U0.substVr b0.root), ?_⟩
      rw [← h3]
      exact .refl _
  | _, _, .cast (S := S0) (e := e) ht he, h =>
      let v := TmTy.viewApp ht h
      { v with le := .trans S0 v.le e, leTy := .trans S0 v.leTy he }
  | _, _, .atom _, h => absurd h (by simp [Tm.skel])
  | _, _, .new _ _, h => absurd h (by simp [Tm.skel])
  | _, _, .let _ _, h => absurd h (by simp [Tm.skel])

/-- A typed witness with the skeleton of an atom: an atom with the same root,
the witness's term-level casts moved onto it. -/
structure AtomView {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (a : Atom σ [])
    (T : Ty σ []) : Type where
  /-- The atom. -/
  atom : Atom σ []
  /-- Typed at the witness's type. -/
  atomTy : AtomTy G W Ctx.nil atom T
  /-- Rooted where the running atom is. -/
  root : atom.root = a.root

/-- Open a typed witness with the skeleton of an atom.  A term-level cast
becomes an atom-level one, which does not move the root. -/
def TmTy.viewAtom {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {a : Atom σ []} :
    {tm : Tm σ []} → {T : Ty σ []} → TmTy G W Ctx.nil tm T →
    tm.skel = (Tm.atom a).skel → AtomView G W a T
  | _, _, .atom ha, h => by
      simp only [Tm.skel, Tm.atom.injEq, Atom.var.injEq] at h
      exact ⟨_, ha, h⟩
  | _, _, .cast (e := e) ht he, h =>
      let v := TmTy.viewAtom ht h
      ⟨.cast v.atom e, .cast v.atomTy he, v.root⟩
  | _, _, .new _ _, h => absurd h (by simp [Tm.skel])
  | _, _, .let _ _, h => absurd h (by simp [Tm.skel])
  | _, _, .app _ _, h => absurd h (by simp [Tm.skel])

/-! ## The five unconditional cases -/

/-- **`let` pushes a frame.**  The witness's `let` is opened: its bound term
becomes the running witness, and its body becomes a `let` frame over a coercion
frame holding the witness's collected casts. -/
def StateTy.let_ {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {t : Tm σ []}
    {u : Tm σ ([],x)} {W : StoreTy σ} {U : Ty σ []}
    (d : StateTy ⟨G, K, .let t u⟩ W U) : StateTy ⟨G, K ▹ .let u, t⟩ W U :=
  let v := TmTy.viewLet d.tmTy d.tmSkel
  { ty := v.bound
    tm := v.tm
    tmTy := v.tmTy
    tmSkel := v.tmSkel
    cont := (d.cont ▹ .cast v.le) ▹ .let v.body
    contTy := .let v.bodyTy (.cast v.leTy d.contTy)
    contSkel := by
      show Cont.skel d.cont ▹ .let v.body.skel = K.skel ▹ .let u.skel
      rw [d.contSkel, v.bodySkel] }

/-- **`castPush` is invisible to the typing.**  A term-level cast and a coercion
frame have the same (empty) skeleton, so the witness is unchanged. -/
def StateTy.castPush {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {t : Tm σ []}
    {e : Le σ []} {W : StoreTy σ} {U : Ty σ []}
    (d : StateTy ⟨G, K, .cast t e⟩ W U) : StateTy ⟨G, K ▹ .cast e, t⟩ W U :=
  ⟨d.ty, d.tm, d.tmTy, d.tmSkel, d.cont, d.contTy, d.contSkel⟩

/-- **`castAtom` is invisible to the typing.**  An atom-level cast does not move
the root, and a coercion frame has no skeleton, so the witness is unchanged. -/
def StateTy.castAtom {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {a : Atom σ []}
    {e : Le σ []} {W : StoreTy σ} {U : Ty σ []}
    (d : StateTy ⟨G, K ▹ .cast e, .atom a⟩ W U) :
    StateTy ⟨G, K, .atom (.cast a e)⟩ W U :=
  ⟨d.ty, d.tm, d.tmTy, d.tmSkel, d.cont, d.contTy, d.contSkel⟩

/-- **`rename` substitutes a typed atom.**  The machine writes the let-bound
atom's root into the body; the witness writes the **whole** witness atom,
wrapped in the casts collected from the coercion frames in front of the `let`
frame, through `TmTy.substEv` with `MonoSyn.EvA.oneConc`.  The two agree on
skeletons (`TmTy.substEv_skel`, `Tm.skel_inst`), which is the resolution of
the root-substitution obstacle: the machine's rule is kept, and the dropped
coercions survive in the witness. -/
def StateTy.rename {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {u : Tm σ ([],x)}
    {a : Atom σ []} {W : StoreTy σ} {U : Ty σ []}
    (d : StateTy ⟨G, K ▹ .let u, .atom a⟩ W U) :
    StateTy ⟨G, K, u.inst .base (Vr.loc a.root)⟩ W U := by
  have va := TmTy.viewAtom d.tmTy d.tmSkel
  have lh := ContTy.peelLet d.contTy d.contSkel
  have hroot : (Atom.cast va.atom lh.le).root = .conc (Vr.loc a.root) := by
    show va.atom.root = _
    rw [va.root, Vr.conc_loc]
  have E := MonoSyn.EvA.oneConc lh.bound hroot (AtomTy.cast va.atomTy lh.leTy)
  have hsk := TmTy.substEv_skel lh.bodyTy E
  generalize TmTy.substEv lh.bodyTy E = r at hsk
  obtain ⟨u', hu'⟩ := r
  have hsk' : u'.skel = lh.body.skelSubst (Subst.one (Vr.conc (Vr.loc a.root))) := hsk
  have hty : lh.res.weaken.subst (Subst.one (Vr.conc (Vr.loc a.root))) = lh.res :=
    Oopsla16.Ty.substVr_weaken _ _
  rw [hty] at hu'
  exact
    { ty := lh.res
      tm := u'
      tmTy := hu'
      tmSkel := (hsk'.trans (Tm.skelSubst_congr lh.bodySkel _)).trans
        (Tm.skel_inst u .base (Vr.loc a.root)).symm
      cont := lh.rest
      contTy := lh.restTy
      contSkel := lh.restSkel }

/-- The fresh location, at the allocated literal's type with its self
instantiated there: `varConc` over the extended store typing. -/
def MachineStore.allocVar {σ : Sig} (G : MachineStore σ σ) (W : StoreTy σ)
    (T : Ty σ ([],x)) (d : Defs (σ,x) []) :
    AtomTy (G.weakenStore.cons d).erase (StoreTy.alloc W T) Ctx.nil
      (.var (.conc .here))
      ((T.subst (Subst.ofStore (s := []) Rename.succ).lift).substVr (.conc .here)) := by
  rw [Subst.lift_ofStore]
  have hv := AtomTy.varConc (G := (G.weakenStore.cons d).erase)
    (W := StoreTy.alloc W T) (Γ := Ctx.nil) (l := .here)
  rw [Oopsla16.Ty.rename_renameNil_nil] at hv
  exact hv

/-- **`alloc` extends the store honestly and returns a typed location.**  The
store typing grows by the literal's self type (`StoreTy.alloc`), honesty by
`MachineStore.Honest.alloc`, the continuation by `ContTy.renameStore`, and the
running witness is the fresh location packed at the literal's recursive type
and cast by the witness's collected casts, all weakened. -/
def StateTy.alloc {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {T : Ty σ ([],x)}
    {ds : Defs σ ([],x)} {W : StoreTy σ} {U : Ty σ []}
    (h : MachineStore.Honest G W) (d : StateTy ⟨G, K, .new T ds⟩ W U) :
    MachineStore.Honest (G.weakenStore.cons (ds.weakenStore.inst .base .here))
        (StoreTy.alloc W T) ×
      StateTy ⟨G.weakenStore.cons (ds.weakenStore.inst .base .here), K.weakenStore,
        .atom (.var (.conc .here))⟩ (StoreTy.alloc W T) U.weakenStore := by
  have v := TmTy.viewNew d.tmTy d.tmSkel
  have E1 := MachineStore.allocEv G W T (ds.weakenStore.inst .base .here)
  have e' := LeTy.substEv v.leTy E1.ev
  have rK := ContTy.renameStore E1 d.contTy
  have hvar := MachineStore.allocVar G W T (ds.weakenStore.inst .base .here)
  refine ⟨h.alloc v.defsTy v.defsSkel,
    { ty := d.ty.weakenStore
      tm := .atom (.cast (.pack (T.subst (Subst.ofStore Rename.succ).lift)
        (.var (.conc .here))) e'.1)
      tmTy := .atom (.cast (.pack hvar) e'.2)
      tmSkel := rfl
      cont := rK.1
      contTy := rK.2.1
      contSkel := ?_ }⟩
  have e1 : d.cont.skel = K.skel := d.contSkel
  show rK.1.skel = (K.renameStore Rename.succ).skel
  rw [rK.2.2.down, Cont.skel_renameStore, ← Cont.skelStore_skel, e1,
    Cont.skelStore_skel]

/-! ## Application, under canonical forms for methods -/

/-- What `AppInversion` delivers at one location: the method the store holds
there at label `l`, and closed inclusions relating its annotations to the
method type the receiver was typed at — the domain contravariantly, the
codomain under the parameter, exactly as `stp_fun` (`LeTy.dfun`) relates two
method types. -/
structure AppInv {σ : Sig} (G : MachineStore σ σ) (W : StoreTy σ)
    (ℓ : BVar σ .var) (l : Lb) (S0 : Ty σ []) (U0 : Ty σ ([],x)) : Type where
  /-- The stored method's domain … -/
  S : Ty σ []
  /-- … codomain … -/
  U : Ty σ ([],x)
  /-- … and body. -/
  body : Tm σ ([],x)
  /-- They are what the machine's `Defs.fun?` finds. -/
  lookup : (G.lookup ℓ).fun? l = some (S, U, body)
  /-- The declared domain is included in the stored one … -/
  dom : Le σ []
  /-- … closed. -/
  domTy : LeTy G.erase W Ctx.nil dom S0 S
  /-- The stored codomain is included in the declared one, under the
  parameter at the declared domain … -/
  cod : Le σ ([],x)
  /-- … typed. -/
  codTy : LeTy G.erase W (Ctx.nil.cons S0.weaken) cod U U0

/-- **Canonical forms for methods, as a hypothesis structure.**  A closed atom
typed at a method type `{l : S0 → U0}` over an honest machine store is rooted
at a location whose stored literal has a method at `l`, with domain and
codomain related to `S0`/`U0` by closed inclusions (`AppInv`).

This is the one piece of canonical forms preservation and progress consume.
**Nothing in this module inhabits it; `MethodInversion.appInversion` does**,
over every honest machine store.  Discharging it is the receiver-side instance of transitivity elimination for closed evidence:
`AtomTy.toVc` turns the atom into a closed observation of its root,
`Normalizer`'s `VcTy.toNf`/`VcTy.canon` bring that observation to a location
node (`vcLoc` or `vcLocAny`) under a normalized spine, and the remaining
closed inclusion from the location's type — a right-nested intersection of
stored members, by `DefsTy` or by `vcLocAny`'s `LitMatch` premise — to
`{l : S0 → U0}` must be inverted to the conjunct at `l`.  Reading that
conjunct back as the stored method is proved here (`LocType.method`,
positional labels); the inversion is `Inversion.RecordedLit.obsFun`, the method
counterpart of the closed-inclusion inversion that also inhabits `Contract`
(`Normalizer`) and `BoundsVacuous` (`CanonicalForms`).

Its evidence-level content, with the machine store read back out, is
`ObsFunInversion` below; `AppInversion.ofObs` derives this structure from that
one with no further hypothesis, so a normalizer only has to deliver the
evidence-level statement. -/
structure AppInversion : Type where
  /-- The inversion, at every store scope. -/
  inv : ∀ {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ},
    MachineStore.Honest G W →
    ∀ {a : Atom σ []} {l : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)},
      AtomTy G.erase W Ctx.nil a (.TFun l S0 U0) →
      AppInv G W (Vr.loc a.root) l S0 U0

/-! ### The evidence-level content of `AppInversion`

`AppInversion` speaks about the machine store and about evidence at once.  Its
content is at the evidence level alone, and `ObsFunInversion` states it there:
a closed observation of a location at a method type stands on a **location
node** — `vcLoc`, reporting `tyOf W ℓ`, or `vcLocAny`, reporting a self type
that matches the stored literal (`LocType`) — whose reported type has a method
conjunct at the same label, related to the observed method type by closed
inclusions.  That is the statement a normalizer produces: normalize the spine,
read the base, invert the closed inclusion from the base's type.
`AppInversion.ofObs` derives `AppInversion` from it **with no further
hypothesis**: `AtomTy.toVc` supplies the observation, and reading the conjunct
back as the stored method is proved here for both kinds of location node
(`LocType.method`), positional labels doing the work for `vcLoc`. -/

/-- The type a location node reports for `ℓ`: the recorded one (`vcLoc`), or a
self type that matches the stored literal (`vcLocAny`). -/
inductive LocType {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (ℓ : BVar σ .var) :
    Ty σ [] → Type where
  /-- `vcLoc`'s: the store typing's entry. -/
  | recorded : LocType G W ℓ (tyOf W ℓ)
  /-- `vcLocAny`'s: a self type, instantiated at `ℓ`, with the match that is
  the rule's premise. -/
  | witness {T : Ty σ ([],x)} :
      LitMatch (G.lookup ℓ).get? (T.substVr (.conc ℓ)) →
      LocType G W ℓ (T.substVr (.conc ℓ))

/-- What a closed observation of `ℓ` at `{l : S0 → U0}` inverts to. -/
structure ObsFunInv {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (ℓ : BVar σ .var)
    (l : Lb) (S0 : Ty σ []) (U0 : Ty σ ([],x)) : Type where
  /-- The type the spine's location node reports … -/
  base : Ty σ []
  /-- … as one of the two location nodes reports it. -/
  baseTy : LocType G W ℓ base
  /-- The method conjunct's domain … -/
  S : Ty σ []
  /-- … and codomain. -/
  U : Ty σ ([],x)
  /-- The conjunct. -/
  conj : Conjunct base (.TFun l S U)
  /-- The observed domain is included in the conjunct's … -/
  dom : Le σ []
  /-- … closed. -/
  domTy : LeTy G W Ctx.nil dom S0 S
  /-- The conjunct's codomain is included in the observed one, under the
  parameter … -/
  cod : Le σ ([],x)
  /-- … typed. -/
  codTy : LeTy G W (Ctx.nil.cons S0.weaken) cod U U0

/-- **Canonical forms for method observations, as a hypothesis structure**,
the evidence-level content of `AppInversion`.  Nothing in this module inhabits
it; `MethodInversion.obsFunInversion` does, by `Inversion.RecordedLit.obsFun`
over the literal types an honest machine store records. -/
structure ObsFunInversion : Type where
  /-- The inversion, at every store scope, over an honest machine store. -/
  inv : ∀ {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ},
    MachineStore.Honest G W →
    ∀ {ℓ : BVar σ .var} {v : Vc σ []} {l : Lb} {S0 : Ty σ []} {U0 : Ty σ ([],x)},
      VcTy G.erase W Ctx.nil (.conc ℓ) v (.TFun l S0 U0) → ObsFunInv G.erase W ℓ l S0 U0

/-- A method found at a label is below the length. -/
theorem Defs.fun?_lt {σ s : Sig} : (ds : Defs σ s) → {l : Lb} →
    {p : Ty σ s × Ty σ (s,x) × Tm σ (s,x)} → ds.fun? l = some p → l < ds.length
  | .dnil, _, _, h => by cases h
  | .dty _ ds, l, _, h => by
      simp only [Defs.fun?] at h
      split at h
      · cases h
      · exact Nat.lt_succ_of_lt (Defs.fun?_lt ds h)
  | .dfun _ _ _ ds, l, _, h => by
      simp only [Defs.fun?] at h
      split at h
      · rename_i heq
        rw [heq]
        exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Defs.fun?_lt ds h)

/-- **A method conjunct of a typed definition list's type is a method of the
list**, with the same annotations: the converse of `DefsTy.method`. -/
theorem DefsTy.fun?_of_conjunct {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} : {ds : Defs σ s} → {T : Ty σ s} → DefsTy G W Γ ds T →
    {l : Lb} → {S : Ty σ s} → {U : Ty σ (s,x)} → Conjunct T (.TFun l S U) →
    ∃ t, ds.fun? l = some (S, U, t)
  | _, _, .dnil, _, _, _, c => nomatch c
  | _, _, .dty (ds := ds) hds, l, _, _, c => by
      cases c with
      | there c =>
          obtain ⟨t, ht⟩ := DefsTy.fun?_of_conjunct hds c
          refine ⟨t, ?_⟩
          have hlt := Defs.fun?_lt ds ht
          simp only [Defs.fun?]
          rw [if_neg (Nat.ne_of_lt hlt)]
          exact ht
  | _, _, .dfun (S := S0) (U := U0) (t := t0) (ds := ds) hds _, l, _, _, c => by
      cases c with
      | here => exact ⟨t0, by simp [Defs.fun?]⟩
      | there c =>
          obtain ⟨t, ht⟩ := DefsTy.fun?_of_conjunct hds c
          refine ⟨t, ?_⟩
          have hlt := Defs.fun?_lt ds ht
          simp only [Defs.fun?]
          rw [if_neg (Nat.ne_of_lt hlt)]
          exact ht

/-- **A method conjunct of a matched type is a method of the machine store**,
at the conjunct's own types.  `LitMatch` finds a stored method at the
conjunct's label whose annotations agree with it by `EqSome`, and the erased
machine store carries both annotations (`Defs.fun?_of_erase`), so there
`EqSome` is equality. -/
theorem LitMatch.method {σ : Sig} {G : MachineStore σ σ} {ℓ : BVar σ .var} :
    {B : Ty σ []} → LitMatch (G.erase.lookup ℓ).get? B →
    {l : Lb} → {S : Ty σ []} → {U : Ty σ ([],x)} →
    Conjunct B (.TFun l S U) → ∃ t, (G.lookup ℓ).fun? l = some (S, U, t)
  | _, .top, _, _, _, c => nomatch c
  | _, .typ _ r, _, _, _, c => by
      cases c with
      | there c => exact LitMatch.method r c
  | _, .fn (b := b) hg e1 e2 r, _, _, _, c => by
      cases c with
      | here =>
          rw [← MachineStore.erase_lookup] at hg
          obtain ⟨S', U', t', hf, hS, hU, _⟩ := Defs.fun?_of_erase _ b hg
          refine ⟨t', ?_⟩
          rw [hf]
          rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
          · rw [e1] at hS; cases hS
          · rw [e1] at hS; cases hS
          · rw [e2] at hU; cases hU
          · rw [e1] at hS; rw [e2] at hU
            cases hS; cases hU; rfl
      | there c => exact LitMatch.method r c

/-- **A location node's method conjunct is the stored method.**  For `vcLoc`
by honesty (`DefsTy.fun?_of_conjunct` on the witness, moved along the skeleton
by `Defs.fun?_of_skel`); for `vcLocAny` by its premise (`LitMatch.method`),
whose `EqSome` annotations meet the machine store's, which are always present
(`Defs.fun?_of_erase`). -/
theorem LocType.method {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) {ℓ : BVar σ .var} {B : Ty σ []}
    (hB : LocType G.erase W ℓ B) {l : Lb} {S : Ty σ []} {U : Ty σ ([],x)}
    (c : Conjunct B (.TFun l S U)) : ∃ t, (G.lookup ℓ).fun? l = some (S, U, t) := by
  cases hB with
  | recorded =>
      obtain ⟨t0, ht0⟩ := DefsTy.fun?_of_conjunct (h.at' ℓ).typed c
      obtain ⟨t1, ht1, _⟩ := Defs.fun?_of_skel (h.at' ℓ).skel.symm ht0
      exact ⟨t1, ht1⟩
  | witness h0 => exact LitMatch.method h0 c

/-- The location an atom of empty local scope is rooted at, read either way. -/
theorem locOf_eq_loc {σ : Sig} : (p : Vr σ []) → locOf p = Vr.loc p
  | .conc _ => rfl
  | .abs x => nomatch x

/-- **`AppInversion` from its evidence-level content**, with no further
hypothesis: the atom becomes an observation of its root (`AtomTy.toVc`), the
observation inverts by `ObsFunInversion`, and the conjunct it inverts to is the
stored method (`LocType.method`). -/
def AppInversion.ofObs (hobs : ObsFunInversion) : AppInversion where
  inv := fun {σ} {G} {W} h {a} {l} {S0} {U0} ha => by
    obtain ⟨v, hv⟩ := AtomTy.toVc ha
    rw [show a.rootLoc = Vr.loc a.root from locOf_eq_loc a.root] at hv
    have o := hobs.inv h hv
    have hex := LocType.method h o.baseTy o.conj
    have hs : ((G.lookup (Vr.loc a.root)).fun? l).isSome := by
      obtain ⟨t, ht⟩ := hex
      rw [ht]
      rfl
    have hget : ((G.lookup (Vr.loc a.root)).fun? l).get hs
        = (o.S, o.U, (((G.lookup (Vr.loc a.root)).fun? l).get hs).2.2) := by
      obtain ⟨t, ht⟩ := hex
      rw [Option.get_of_eq_some hs ht]
    exact
      { S := o.S
        U := o.U
        body := (((G.lookup (Vr.loc a.root)).fun? l).get hs).2.2
        lookup := by
          rw [← hget]
          exact (Option.some_get hs).symm
        dom := o.dom
        domTy := o.domTy
        cod := o.cod
        codTy := o.codTy }

/-- **`app` runs the stored body, typed** — under `AppInversion`.  The body is
typed by honesty (`MachineStore.Honest.method`) at the stored annotations; the
argument witness, cast into the stored domain by the inversion's `dom`,
instantiates the parameter through `TmTy.substEv`; and the result is cast back
into the receiver's declared codomain by the inversion's `cod`, instantiated at
the argument, and then by the witness's own collected casts.

**Stated with a hypothesis:** `hinv : AppInversion`, which this module does
not prove; `MethodInversion.appInversion` inhabits it. -/
def StateTy.app (hinv : AppInversion) {σ : Sig} {G : MachineStore σ σ}
    {K : Cont σ} {a b : Atom σ []} {l : Lb} {S : Ty σ []} {U : Ty σ ([],x)}
    {t : Tm σ ([],x)} {W : StoreTy σ} {R : Ty σ []}
    (h : MachineStore.Honest G W)
    (hf : (G.lookup (Vr.loc a.root)).fun? l = some (S, U, t))
    (d : StateTy ⟨G, K, .app a l b⟩ W R) :
    StateTy ⟨G, K, t.inst .base (Vr.loc b.root)⟩ W R := by
  have v := TmTy.viewApp d.tmTy d.tmSkel
  have inv := hinv.inv h v.fnTy
  have hlk : (G.lookup (Vr.loc a.root)).fun? l = some (inv.S, inv.U, inv.body) := by
    rw [← v.fnRoot]
    exact inv.lookup
  have heq : (inv.S, inv.U, inv.body) = (S, U, t) :=
    Option.some.inj (hlk.symm.trans hf)
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hS, hU, _⟩ := heq
  have domTy := inv.domTy
  rw [hS] at domTy
  have codTy := inv.codTy
  rw [hU] at codTy
  have hrb : v.arg.root = .conc (Vr.loc b.root) := by
    rw [v.argRoot, Vr.conc_loc]
  have hrb1 : (Atom.cast v.arg inv.dom).root = .conc (Vr.loc b.root) := hrb
  have E := MonoSyn.EvA.oneConc S hrb1 (AtomTy.cast v.argTy domTy)
  have E' := MonoSyn.EvA.oneConc v.dom hrb v.argTy
  have mt := (h.method (Vr.loc a.root) hf).2
  have hsk := TmTy.substEv_skel mt.2.1 E
  generalize TmTy.substEv mt.2.1 E = r at hsk
  obtain ⟨u', hu'⟩ := r
  have hsk' : u'.skel = mt.1.skelSubst (Subst.one (Vr.conc (Vr.loc b.root))) := hsk
  have c := LeTy.substEv codTy E'.ev
  have le2 := v.leTy
  rw [← Vr.conc_loc b.root] at le2
  exact
    { ty := d.ty
      tm := .cast (.cast u' c.1) v.le
      tmTy := .cast (.cast hu' c.2) le2
      tmSkel := (hsk'.trans (Tm.skelSubst_congr mt.2.2.down _)).trans
        (Tm.skel_inst t .base (Vr.loc b.root)).symm
      cont := d.cont
      contTy := d.contTy
      contSkel := d.contSkel }

/-! ## A typed witness erases to the state

The machine reads nothing the skeleton forgets, and neither does erasure: a
continuation's source context depends only on its skeleton, as a term's
erasure does (`Tm.erase_skel`).  So the witness a `StateTy` carries and the
state it types erase to the **same source term**, which is what a transport of
safety to `Oopsla16` would read off. -/

/-- A continuation's source context depends only on its skeleton. -/
theorem Cont.plug_skel {σ : Sig} : (K : Cont σ) → (t : Oopsla16.Tm σ []) →
    K.skel.plug t = K.plug t
  | .nil, _ => rfl
  | .cons K (.let u), t => by
      show K.skel.plug (letEncode t u.skel.erase) = K.plug (letEncode t u.erase)
      rw [Tm.erase_skel, Cont.plug_skel K]
  | .cons K (.cast _), t => Cont.plug_skel K t

/-- **The witness erases to the state.**  The typed term plugged into the typed
continuation erases to the running term plugged into the running
continuation. -/
theorem StateTy.erase_eq {σ : Sig} {st : State σ} {W : StoreTy σ} {U : Ty σ []}
    (d : StateTy st W U) : d.cont.plug d.tm.erase = st.eraseTm := by
  show d.cont.plug d.tm.erase = st.K.plug st.t.erase
  rw [← Cont.plug_skel d.cont, d.contSkel, Cont.plug_skel, ← Tm.erase_skel d.tm,
    d.tmSkel, Tm.erase_skel]

/-! ## Preservation -/

/-- **Preservation**, one step.  An honest store and a typed state step to an
honest store, at a store typing that has grown along the step, and a typed
state whose result type has moved along the same growth.  The `let`,
`castPush`, `castAtom`, `rename` and `alloc` cases use no hypothesis
(`StateTy.let_`, …, `StateTy.alloc`); the `app` case is `StateTy.app`.

**Stated with a hypothesis:** `hinv : AppInversion`, used by the `app` case
only and inhabited by `MethodInversion.appInversion`;
`MethodInversion.preservation'` is this theorem without it. -/
theorem preservation (hinv : AppInversion) {σ1 σ2 : Sig} {g : Grows σ1 σ2}
    {st : State σ1} {st' : State σ2} {W : StoreTy σ1} {T : Ty σ1 []}
    (h : MachineStore.Honest st.G W) (d : StateTy st W T) (hs : Step g st st') :
    ∃ W' : StoreTy σ2,
      Nonempty (MachineStore.Honest st'.G W' × StateTy st' W' (Ty.alongGrows g T)) := by
  cases hs with
  | «let» => exact ⟨W, ⟨(h, d.let_)⟩⟩
  | castPush => exact ⟨W, ⟨(h, d.castPush)⟩⟩
  | castAtom => exact ⟨W, ⟨(h, d.castAtom)⟩⟩
  | rename => exact ⟨W, ⟨(h, d.rename)⟩⟩
  | alloc => exact ⟨_, ⟨StateTy.alloc h d⟩⟩
  | app hf => exact ⟨W, ⟨(h, StateTy.app hinv h hf d)⟩⟩

/-- **Preservation**, along a run.

**Stated with a hypothesis:** `hinv : AppInversion`, inhabited by
`MethodInversion.appInversion`; `MethodInversion.preservation_steps'` is this
theorem without it.  A run with no `app` step does not use it, but the
statement does not track that. -/
theorem preservation_steps (hinv : AppInversion) {σ1 σ2 : Sig} {g : Grows σ1 σ2}
    {st : State σ1} {st' : State σ2} {W : StoreTy σ1} {T : Ty σ1 []}
    (h : MachineStore.Honest st.G W) (d : StateTy st W T) (hs : Steps g st st') :
    ∃ W' : StoreTy σ2,
      Nonempty (MachineStore.Honest st'.G W' × StateTy st' W' (Ty.alongGrows g T)) := by
  induction hs with
  | refl => exact ⟨W, ⟨(h, d)⟩⟩
  | tail _ hs2 ih =>
      obtain ⟨W1, ⟨h1, d1⟩⟩ := ih h d
      obtain ⟨W2, ⟨h2, d2⟩⟩ := preservation hinv h1 d1 hs2
      refine ⟨W2, ⟨(h2, ?_)⟩⟩
      rw [Ty.alongGrows_comp]
      exact d2

/-- A closed term typed over the empty store, run from the empty continuation,
stays typed over an honest store at every reachable state.

**Stated with a hypothesis:** `hinv : AppInversion`, inhabited by
`MethodInversion.appInversion`; `MethodInversion.preservation_init'` is this
theorem without it. -/
theorem preservation_init (hinv : AppInversion) {W : StoreTy []} {t : Tm [] []}
    {T : Ty [] []} (d : TmTy Store.nil W Ctx.nil t T) {σ : Sig} {g : Grows [] σ}
    {st' : State σ} (hs : Steps g ⟨MachineStore.nil, .nil, t⟩ st') :
    ∃ W' : StoreTy σ,
      Nonempty (MachineStore.Honest st'.G W' × StateTy st' W' (Ty.alongGrows g T)) :=
  preservation_steps hinv (MachineStore.Honest.nil W) (StateTy.init d) hs

/-! ## The on-the-nose statement is false

The module header claims that the machine's `rename` rule, which writes an
atom's root and drops its coercions, produces states that are **not** typable
as they stand, so that no preservation theorem with the running term itself
typed can hold for this machine.  Here is the claim, machine-checked.

A **bare** location `var ℓ` is typed only by `varConc`, at the type the store
typing records, which is the type of a definition list — `⊤` or an
intersection, by `DefsTy` over an honest machine store — so it is never typed
at a method type, and an invocation whose receiver is a bare location is
untypable (`MachineStore.Honest.app_var_untypable`).  `OnTheNose` exhibits a
state typed on the nose — witness *equal* to the running term and
continuation — whose `rename` step produces exactly such an invocation, while
`StateTy.rename` still types it up to evidence. -/

/-- The shape a definition list's type has: `⊤` or an intersection.  Written
prefix, not as `Ty.ObjShape`: dot notation on an `Oopsla16.Ty` would look for
the name in `Oopsla16`. -/
def ObjShape {σ s : Sig} (T : Ty σ s) : Prop :=
  T = .TTop ∨ ∃ T1 T2 : Ty σ s, T = .TAnd T1 T2

/-- The shape survives substitution, since `⊤` and `∧` are congruences. -/
theorem ObjShape.subst {σ1 σ2 s1 s2 : Sig} {T : Ty σ1 s1} (h : ObjShape T)
    (θ : Subst σ1 s1 σ2 s2) : ObjShape (T.subst θ) := by
  rcases h with rfl | ⟨T1, T2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl⟩

/-- A type of that shape is not a method type. -/
theorem ObjShape.ne_fun {σ s : Sig} {T : Ty σ s} (h : ObjShape T) {l : Lb}
    {S : Ty σ s} {U : Ty σ (s,x)} : T ≠ .TFun l S U := by
  rcases h with rfl | ⟨T1, T2, rfl⟩ <;> intro h <;> cases h

/-- A typed target definition list has that shape. -/
theorem DefsTy.objShape {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    {ds : Defs σ s} → {T : Ty σ s} → DefsTy G W Γ ds T → ObjShape T
  | _, _, .dnil => Or.inl rfl
  | _, _, .dty _ => Or.inr ⟨_, _, rfl⟩
  | _, _, .dfun _ _ => Or.inr ⟨_, _, rfl⟩

/-- **Over an honest machine store a bare location has no method type.**  The
only rule for `var ℓ` is `varConc`, which reports the store typing's type, and
honesty types that by `DefsTy`: it is not a `TFun`.  The other location rule
types the atom `loc ℓ T`, not `var ℓ`. -/
theorem MachineStore.Honest.var_not_fun {σ : Sig} {G : MachineStore σ σ}
    {W : StoreTy σ} (h : MachineStore.Honest G W) {ℓ : BVar σ .var} {l : Lb}
    {S : Ty σ []} {U : Ty σ ([],x)}
    (d : AtomTy G.erase W Ctx.nil (.var (.conc ℓ)) (.TFun l S U)) : False := by
  generalize hT : (Ty.TFun l S U : Ty σ []) = T at d
  generalize ha : (Atom.var (.conc ℓ) : Atom σ []) = a at d
  cases d with
  | varAbs => cases ha
  | varConc =>
      rename_i l'
      exact (((h.at' l').typed.objShape.subst _).ne_fun) hT.symm
  | varConcAny => cases ha
  | cast => cases ha
  | pack => cases ha
  | unpack => cases ha

/-- **An invocation whose receiver is a bare location is untypable** over an
honest machine store, at every type. -/
theorem MachineStore.Honest.app_var_untypable {σ : Sig} {G : MachineStore σ σ}
    {W : StoreTy σ} (h : MachineStore.Honest G W) {ℓ : BVar σ .var} {l : Lb}
    {b : Atom σ []} {T : Ty σ []}
    (d : TmTy G.erase W Ctx.nil (.app (.var (.conc ℓ)) l b) T) : False := by
  generalize ht : (Tm.app (.var (.conc ℓ)) l b : Tm σ []) = t at d
  cases d with
  | app ha _ =>
      simp only [Tm.app.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      exact h.var_not_fun ha
  | atom => cases ht
  | new => cases ht
  | «let» => cases ht
  | cast => cases ht

namespace OnTheNose

/-- One location. -/
abbrev σ1 : Sig := ([],x)

/-- That location. -/
abbrev ℓ : BVar σ1 .var := .here

/-- A one-method object: method `0`, from `⊤` to `⊤`, returning its
argument. -/
abbrev d : Defs σ1 [] := .dfun .TTop .TTop (.atom (.var (.abs .here))) .dnil

/-- The store holding it. -/
abbrev G : MachineStore σ1 σ1 := .cons .nil d

/-- Its store typing: the method, then `⊤`, as `D_Fun` and `D_Nil` give it. -/
abbrev W : StoreTy σ1 := fun _ => .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- The store is honest, on the nose. -/
def honest : MachineStore.Honest G W :=
  ⟨fun
    | .here => ⟨d, .dfun .dnil (.atom .varAbs), rfl⟩⟩

/-- The `let`-bound atom: the location, cast to its method member. -/
abbrev a0 : Atom σ1 [] := .cast (.var (.conc ℓ)) (.andE1 .TTop (.refl (.TFun 0 .TTop .TTop)))

/-- The `let` body: invoke the bound variable's method on the bound variable,
widened to `⊤`. -/
abbrev u : Tm σ1 ([],x) :=
  .app (.var (.abs .here)) 0 (.cast (.var (.abs .here)) (.top (.TFun 0 .TTop .TTop)))

/-- The state: `a0` returned into `let x = □ in u`. -/
abbrev st : State σ1 := ⟨G, .nil ▹ .let u, .atom a0⟩

/-- **The state is typed on the nose**: the witness term and continuation are
the running ones. -/
def stTy : StateTy st W .TTop :=
  { ty := .TFun 0 .TTop .TTop
    tm := .atom a0
    tmTy := .atom (.cast .varConc (.andE1 _ (.refl _)))
    tmSkel := rfl
    cont := .nil ▹ .let u
    contTy := .let (by
        show TmTy G.erase W (Ctx.nil.cons (Ty.TFun 0 .TTop .TTop).weaken) u .TTop
        exact TmTy.app (S := .TTop) (U := .TTop) .varAbs (.cast .varAbs (.top _))) .nil
    contSkel := rfl }

/-- It steps by `rename`, to `u` with the location's root written in. -/
theorem step : Step .refl st ⟨G, .nil, u.inst .base ℓ⟩ := Step.rename

/-- **The reduct is untypable**, at every type and at every store typing at
which the store is honest: its receiver is the bare location, the cast having
been dropped with the rest of the atom. -/
theorem reduct_untypable {W' : StoreTy σ1} (h : MachineStore.Honest G W')
    {T : Ty σ1 []} (dt : TmTy G.erase W' Ctx.nil (u.inst .base ℓ) T) : False :=
  h.app_var_untypable (ℓ := ℓ) (l := 0) dt

/-- **And it is typed up to evidence**, by the `rename` case of
preservation. -/
def reductTy : StateTy ⟨G, .nil, u.inst .base ℓ⟩ W .TTop := stTy.rename

end OnTheNose

/-! ## From an honest source store to an honest machine store

`MachineStore.Honest` is not `Store.Honest` of the erasure (module header), but
the two are connected in the direction elaboration goes: a source store that is
honest in the source's sense, with every literal's witness in the elaborable
fragment (`Elaboration.DmsFrag`), is the **erasure of an honest machine store**
— the store of the witnesses' elaborations, each with its self instantiated at
its own location.  So every source configuration the elaboration covers starts
the target machine in an honest state, and `StateTy.ofSource` types it there
on the nose. -/

/-- A machine store with the shape of a source store, one given definition list
per location.  The source store is recursed on only for its shape. -/
def MachineStore.ofShape {σ : Sig} : {σ' : Sig} → Store σ σ' →
    (BVar σ' .var → Defs σ []) → MachineStore σ σ'
  | _, .nil, _ => .nil
  | _, .cons G _, f => .cons (MachineStore.ofShape G (fun l => f (.there l))) (f .here)

/-- Its lookups are the given lists. -/
theorem MachineStore.lookup_ofShape {σ : Sig} : {σ' : Sig} → (G : Store σ σ') →
    (f : BVar σ' .var → Defs σ []) → (l : BVar σ' .var) →
    (MachineStore.ofShape G f).lookup l = f l
  | _, .cons _ _, _, .here => rfl
  | _, .cons G _, f, .there l => MachineStore.lookup_ofShape G (fun l => f (.there l)) l

/-- It erases to the source store as soon as every given list erases to the
source's entry. -/
theorem MachineStore.erase_ofShape {σ : Sig} : {σ' : Sig} → (G : Store σ σ') →
    (f : BVar σ' .var → Defs σ []) → (∀ l, (f l).erase = G.lookup l) →
    (MachineStore.ofShape G f).erase = G
  | _, .nil, _, _ => rfl
  | _, .cons G ds, f, hf => by
      show MachineStore.erase (.cons (MachineStore.ofShape G (fun l => f (.there l)))
        (f .here)) = _
      simp only [MachineStore.erase]
      rw [MachineStore.erase_ofShape G (fun l => f (.there l)) (fun l => hf (.there l))]
      exact congrArg _ (hf .here)

/-- The elaborated literal at a location, before its self is instantiated. -/
def Store.Honest.elabAt {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) (l : BVar σ .var) :
    DefsElab G W (Ctx.nil.cons (W l)) (h.at' l).defs (W l) :=
  elabDms W (h.at' l).typed (hf l)

/-- **The machine store of an honest source store**: each witness elaborated,
with its self instantiated at its own location, as `Machine.Step.alloc` would
have stored it. -/
def Store.Honest.toMachine {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) : MachineStore σ σ :=
  MachineStore.ofShape G (fun l => (h.elabAt hf l).defs.inst .base l)

/-- It erases to the source store. -/
theorem Store.Honest.toMachine_erase {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) :
    (h.toMachine hf).erase = G := by
  apply MachineStore.erase_ofShape
  intro l
  rw [Defs.erase_inst]
  show ((h.elabAt hf l).defs.erase).substVr (.conc l) = _
  rw [show (h.elabAt hf l).defs.erase = (h.at' l).defs from
    elabDms_erase W (h.at' l).typed (hf l)]
  exact (h.at' l).stored

/-- **It is honest**, at the same store typing.  At each location the witness
is the elaborated literal with its self instantiated through the substitution
theorem, the self being typed by `varConc` at `tyOf W ℓ`; its skeleton is the
stored literal's by `DefsTy.substEv_skel` and `Defs.skel_inst`. -/
def Store.Honest.toMachine_honest {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) :
    MachineStore.Honest (h.toMachine hf) W where
  at' := fun l => by
    have r := h.elabAt hf l
    have hvar : AtomTy G W Ctx.nil (.var (.conc l)) ((W l).substVr (.conc l)) := by
      have hv := AtomTy.varConc (G := G) (W := W) (Γ := Ctx.nil) (l := l)
      rw [Oopsla16.Ty.rename_renameNil_nil] at hv
      exact hv
    have E := MonoSyn.EvA.oneConcAt (W l) rfl hvar
    refine ⟨(DefsTy.substEv (h.elabAt hf l).typed E).defs, ?_, ?_⟩
    · rw [h.toMachine_erase hf]
      exact (DefsTy.substEv (h.elabAt hf l).typed E).deriv
    · rw [DefsTy.substEv_skel]
      show _ = (MachineStore.lookup (MachineStore.ofShape G _) l).skel
      rw [MachineStore.lookup_ofShape, Defs.skel_inst]
      rfl

/-- **A source configuration in the fragment starts a typed, honest run.**  A
term typed over an honest source store, the term and every stored witness in
the elaborable fragment, elaborates to a machine state whose store erases to
the source store, whose term erases to the source term, and which is typed on
the nose over an honest machine store. -/
def StateTy.ofSource {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs)
    {t : Oopsla16.Tm σ []} {T : Ty σ []} (ht : Oopsla16.HasType G Ctx.nil t T)
    (ft : TmFrag t) :
    (st : State σ) × MachineStore.Honest st.G W × StateTy st W T ×
      PLift (st.G.erase = G ∧ st.eraseTm = t) := by
  have e := h.toMachine_erase hf
  refine ⟨⟨h.toMachine hf, .nil, (elabHasType W ht ft).1⟩, h.toMachine_honest hf,
    ⟨T, (elabHasType W ht ft).1, ?_, rfl, .nil, .nil, rfl⟩, ⟨e, ?_⟩⟩
  · show TmTy (h.toMachine hf).erase W Ctx.nil _ T
    rw [e]
    exact (elabHasType W ht ft).2
  · exact elabHasType_erase W ht ft

end FCdotR
