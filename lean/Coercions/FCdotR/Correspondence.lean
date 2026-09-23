import Coercions.FCdotR.MethodInversion

/-!
# The operational correspondence between `Oopsla16` and the FCdotR machine

`MethodInversion.safety'` says the FCdotR machine, run from a closed typed
term, never reaches a stuck state.  This module relates that machine to
`Oopsla16`'s own substitution machine (`Oopsla16.Semantics`) and carries the
statement back: a relation between a **source configuration** `(G, t)` —
`G : Oopsla16.Store σ σ`, `t : Oopsla16.Tm σ []` — and a **target state**
`st : State σ` at the same store scope, the laws of that relation, the
simulation, and the transport of safety.

## The relation, and the four choices it makes

* **A-normalisation up to evaluation contexts.**  The source applies arbitrary
  terms and has no `let`; the target applies atoms and has `let`.  `Corr r d`
  is defined by recursion on the *target* term `d`: an atom is its root, an
  object literal is an object literal, an application of atoms is an
  application of variables, a `cast` is transparent, and
  `let d u` corresponds to `E[r0]` whenever `d` corresponds to `r0` and the
  body `u` corresponds to the *residual* `E↑[x]` — the source evaluation
  context `E` (`ECtx`), weakened, with the `let`-bound variable in its hole.
  So every A-normal shape an elaboration may choose for `tapp t1 l t2` is
  accepted (both operands bound, `Corr.anf_app`; receiver only,
  `Corr.anf_recv`, which is what dependent `T_AppVar` needs; argument only,
  `Corr.anf_arg`; neither, `Corr.app`), and the source's left-to-right order is
  kept, because `ECtx.app2` puts the hole in argument position only under a
  variable receiver, exactly as `ST_App2` does.
* **Up to annotations.**  `Corr` never reads a type annotation: not the
  optional `dfun` annotations of the source, not the required `Defs.dfun`
  domain and codomain of the target, not the self type of `Tm.new`.  Type
  members are compared exactly (`DmsCorr.dty`), because the type translation
  is the identity and `LeTy.defL`/`defR` read them.  The source machine ignores
  every annotation, so nothing is lost.
* **Up to evidence.**  `Corr r d ↔ Corr r d.skel` (`Corr.skel_iff`), so the
  relation is a property of skeletons: `Rel.of_skel` transports it between
  states with one skeleton, and `StateTy.corr_witness` says the typed witness
  that `Preservation.StateTy` provides corresponds to the source whenever the
  running state does.
* **Continuations are re-plugged, stores are compared pointwise.**
  `Rel G t st` is `StoreCorr G st.G` (every location's source definitions
  correspond to its target definitions) and `Corr t (st.K.fill st.t)`, where
  `Cont.fill` rebuilds the pending `let` and `cast` frames as term
  constructors.  The two push steps are then identities of the relation, and
  `corr_fill_iff` decomposes it into a source context `C` for the
  continuation (`KCorr`), `t = C.plug r0` and `Corr r0 st.t`.

## Stuck reflection, and why it is not stated literally

"If a related target state can step then the source can step" is **false**
for any relation that, like this one, accepts the target's administrative
steps: `LiteralReflection.literal_reflection_false` exhibits a related state
that pushes a `let` frame while the source is stuck.  The obligation is
therefore stated as what the transport needs — a stuck source configuration
has a target run from any related state to a stuck state (`SimStuckSpec`) —
and the answer direction separately (`Rel.final`).

## INTERFACE FOR THE NEXT STAGES

The statements, verbatim from the declarations below (`Store`, `Ctx`, `Ty`,
`Grows` and `HasType` are `Oopsla16`'s; `Tm`, `State`, `Steps`, `TmTy`,
`StoreTy`, `MachineStore` are FCdotR's):

```lean
abbrev ElabSpec : Prop :=
  ∀ {t : Oopsla16.Tm [] []} {T : Ty [] []}, HasType Store.nil Ctx.nil t T →
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧ Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩

abbrev SimStepSpec : Prop :=
  ∀ {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {t : Oopsla16.Tm σ1 []}
    {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1},
    Rel G t st → Oopsla16.Step g G t G' t' → ∃ st' : State σ2, Steps g st st' ∧ Rel G' t' st'

abbrev SimStuckSpec : Prop :=
  ∀ {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ},
    Rel G t st → SrcStuck G t →
      ∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' ∧ st'.Stuck

abbrev SimSpec : Prop := SimStepSpec ∧ SimStuckSpec

abbrev Oopsla16Safety : Prop :=
  ∀ {t : Oopsla16.Tm [] []} {T : Ty [] []}, HasType Store.nil Ctx.nil t T →
    ∀ {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []},
      Oopsla16.Steps g Store.nil t G' t' → ¬ SrcStuck G' t'
```

with `SrcStuck G t := ¬ t.IsAnswer ∧ ¬ ∃ σ' g G' t', Oopsla16.Step g G t G' t'`.

* **The transport is proved**: `transport : ElabSpec → SimSpec → Oopsla16Safety`,
  from `MethodInversion.safety'`, which has no hypothesis.
* **Track SIM is discharged here**: `sim_step : SimStepSpec`,
  `sim_stuck : SimStuckSpec`, `sim_spec : SimSpec`, with no hypothesis.  So
  `oopsla16_safety` takes `ElabSpec` as its **only** unproved hypothesis.
* **Track ELAB is the obligation this module leaves open**: inhabit
  `ElabSpec`.  `ElaborationFull.elabSpec` discharges it downstream, so
  `ElaborationFull.oopsla16Safety_holds` and `SourceSafety`'s
  `Oopsla16.oopsla16_safety` hold with no hypothesis.  The natural
  route is the compositional `ElabSpecGen` (every `HasType` derivation, at any
  store, store typing, context and scope, elaborates to a `TmTy` derivation at
  the same type whose term corresponds), which `ElabSpecGen.toElabSpec`
  reduces to `ElabSpec`.  The tools it needs are here: the introduction rules
  `Corr.var_of_root`, `Corr.obj`, `Corr.app_of_root`, `Corr.let_`,
  `Corr.cast`, `DmsCorr.dnil`/`dty`/`dfun` (annotations free), the three
  A-normal shapes `Corr.anf_app`/`anf_recv`/`anf_arg`, and `Corr.substEv`,
  which moves a correspondence along the typed substitution theorem
  `TmTy.substEv` (a weakening, for the operand that goes under a `let`;
  `Corr.subst` is the same for the syntactic `Tm.subst`).
* On the fragment `Elaboration.TmFrag` (variable operands, annotated methods)
  `ElabSpec` already holds (`elabSpec_frag`), so `oopsla16_safety_frag` is
  source safety on that fragment **with no hypothesis**.

## What this module does not contain

No elaboration of a general `tapp` or of an unannotated `dfun`, i.e. no proof
of `ElabSpec` (that is `ElaborationFull`, which imports this module); no source-side preservation or canonical forms (none is needed:
the simulation is untyped and all typing is the target's); no statement of
determinism for `Oopsla16.Step` as such — `ECtx.plug_inv`, its form at a
focused redex, is all the simulation uses; and no use of classical logic.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst Grows HasType DmsHasType)

/-! ## Evaluation contexts of the source

`ST_App1` reduces the receiver of an application, `ST_App2` the argument once
the receiver is a variable; these are the only congruences, so the evaluation
contexts are the following, at any scope (method bodies live under binders
and are instantiated later). -/

/-- An evaluation context of `Oopsla16`'s machine: the hole, the receiver of
an application, or the argument of an application whose receiver is a
variable. -/
inductive ECtx : Sig → Sig → Type where
  /-- The hole. -/
  | hole {σ s : Sig} : ECtx σ s
  /-- `E l t2`: the receiver position (`ST_App1`). -/
  | app1 {σ s : Sig} (E : ECtx σ s) (l : Lb) (t2 : Oopsla16.Tm σ s) : ECtx σ s
  /-- `p l E`: the argument position under a variable receiver (`ST_App2`). -/
  | app2 {σ s : Sig} (p : Vr σ s) (l : Lb) (E : ECtx σ s) : ECtx σ s

/-- Fill the hole. -/
def ECtx.plug {σ s : Sig} : ECtx σ s → Oopsla16.Tm σ s → Oopsla16.Tm σ s
  | .hole, t => t
  | .app1 E l t2, t => .tapp (E.plug t) l t2
  | .app2 p l E, t => .tapp (.tvar p) l (E.plug t)

/-- The action of a source substitution on a context. -/
def ECtx.subst {σ1 σ2 s1 s2 : Sig} : ECtx σ1 s1 → Subst σ1 s1 σ2 s2 → ECtx σ2 s2
  | .hole, _ => .hole
  | .app1 E l t2, θ => .app1 (E.subst θ) l (t2.subst θ)
  | .app2 p l E, θ => .app2 (p.subst θ) l (E.subst θ)

/-- Weaken a context under one new local binder. -/
abbrev ECtx.weaken {σ s : Sig} (E : ECtx σ s) : ECtx σ (s,x) :=
  E.subst (Subst.ofRename Rename.succ)

/-- Rename a context's store scope. -/
abbrev ECtx.renameStore {σ1 σ2 s : Sig} (E : ECtx σ1 s) (ρ : Rename σ1 σ2) : ECtx σ2 s :=
  E.subst (Subst.ofStore ρ)

/-- **The residual of a context**: the context weakened under a new binder,
with that binder in its hole.  A target `let x = d in u` corresponds to `E[r0]`
when `u` corresponds to this term — the variable occurs exactly once, in
evaluation position. -/
abbrev ECtx.residual {σ s : Sig} (E : ECtx σ s) : Oopsla16.Tm σ (s,x) :=
  E.weaken.plug (.tvar (.abs .here))

/-- Composition of contexts, innermost last:
`(E1.comp E2).plug t = E1.plug (E2.plug t)` (`ECtx.plug_comp`). -/
def ECtx.comp {σ s : Sig} : ECtx σ s → ECtx σ s → ECtx σ s
  | .hole, E2 => E2
  | .app1 E l t2, E2 => .app1 (E.comp E2) l t2
  | .app2 p l E, E2 => .app2 p l (E.comp E2)

/-- Plugging a composite plugs twice. -/
theorem ECtx.plug_comp {σ s : Sig} : (E1 E2 : ECtx σ s) → (t : Oopsla16.Tm σ s) →
    (E1.comp E2).plug t = E1.plug (E2.plug t)
  | .hole, _, _ => rfl
  | .app1 E l t2, E2, t => congrArg (fun z => Oopsla16.Tm.tapp z l t2) (ECtx.plug_comp E E2 t)
  | .app2 p l E, E2, t => congrArg (Oopsla16.Tm.tapp (.tvar p) l) (ECtx.plug_comp E E2 t)

/-- Substitution commutes with plugging. -/
theorem ECtx.plug_subst {σ1 σ2 s1 s2 : Sig} : (E : ECtx σ1 s1) → (t : Oopsla16.Tm σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (E.plug t).subst θ = (E.subst θ).plug (t.subst θ)
  | .hole, _, _ => rfl
  | .app1 E l t2, t, θ =>
      congrArg (fun z => Oopsla16.Tm.tapp z l (t2.subst θ)) (ECtx.plug_subst E t θ)
  | .app2 p l E, t, θ =>
      congrArg (Oopsla16.Tm.tapp (.tvar (p.subst θ)) l) (ECtx.plug_subst E t θ)

/-- The fusion law for contexts. -/
theorem ECtx.subst_comp {σ1 σ2 σ3 s1 s2 s3 : Sig} : (E : ECtx σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (φ : Subst σ2 s2 σ3 s3) →
    (E.subst θ).subst φ = E.subst (θ.comp φ)
  | .hole, _, _ => rfl
  | .app1 E l t2, θ, φ => by
      simp only [ECtx.subst, ECtx.subst_comp E θ φ, Oopsla16.Tm.subst_comp]
  | .app2 p l E, θ, φ => by
      simp only [ECtx.subst, ECtx.subst_comp E θ φ, Oopsla16.Vr.subst_comp]

/-- The identity law for contexts. -/
theorem ECtx.subst_id {σ s : Sig} : (E : ECtx σ s) → E.subst Subst.id = E
  | .hole => rfl
  | .app1 E l t2 => by simp only [ECtx.subst, ECtx.subst_id E, Oopsla16.Tm.subst_id]
  | .app2 p l E => by simp only [ECtx.subst, ECtx.subst_id E, Oopsla16.Vr.subst_id]

/-- Renaming the store along the identity changes nothing. -/
theorem ECtx.renameStore_id {σ s : Sig} (E : ECtx σ s) : E.renameStore Rename.id = E :=
  ECtx.subst_id E

/-- Substitution distributes over composition. -/
theorem ECtx.comp_subst {σ1 σ2 s1 s2 : Sig} : (E1 E2 : ECtx σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → (E1.comp E2).subst θ = (E1.subst θ).comp (E2.subst θ)
  | .hole, _, _ => rfl
  | .app1 E l t2, E2, θ => by simp only [ECtx.comp, ECtx.subst, ECtx.comp_subst E E2 θ]
  | .app2 p l E, E2, θ => by simp only [ECtx.comp, ECtx.subst, ECtx.comp_subst E E2 θ]

/-- Weakening commutes with a lifted substitution, as substitutions. -/
theorem Subst.succ_comp_lift {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (Subst.ofRename Rename.succ).comp θ.lift
      = θ.comp (Subst.ofRename (Rename.succ (k := .var))) := by
  apply Oopsla16.Subst.ext <;> intro y
  · rfl
  · show (θ.abs y).weaken = (θ.abs y).subst (Subst.ofRename Rename.succ)
    cases θ.abs y <;> rfl

/-- Instantiating a weakening is the identity, as substitutions. -/
theorem Subst.succ_comp_one {σ s : Sig} (v : Vr σ s) :
    (Subst.ofRename (Rename.succ (k := .var))).comp (Subst.one v) = Oopsla16.Subst.id := by
  apply Oopsla16.Subst.ext <;> intro y <;> rfl

/-- Weakening a context commutes with a lifted substitution. -/
theorem ECtx.weaken_subst_lift {σ1 σ2 s1 s2 : Sig} (E : ECtx σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) : E.weaken.subst θ.lift = (E.subst θ).weaken := by
  show (E.subst _).subst _ = (E.subst θ).subst _
  rw [ECtx.subst_comp, ECtx.subst_comp, Subst.succ_comp_lift]

/-- The residual commutes with a lifted substitution: what a `let` body
becomes under the machine's instantiation or a store renaming is the residual
of the substituted context. -/
theorem ECtx.residual_subst_lift {σ1 σ2 s1 s2 : Sig} (E : ECtx σ1 s1)
    (θ : Subst σ1 s1 σ2 s2) : E.residual.subst θ.lift = (E.subst θ).residual := by
  rw [ECtx.residual, ECtx.plug_subst, ECtx.weaken_subst_lift]
  rfl

/-- **Instantiating the residual refills the hole**: the `let`-bound variable,
replaced by `v`, puts `v` back where the bound term was.  This is the
machine's `rename` step read on the source. -/
theorem ECtx.residual_one {σ s : Sig} (E : ECtx σ s) (v : Vr σ s) :
    E.residual.subst (Subst.one v) = E.plug (.tvar v) := by
  rw [ECtx.residual, ECtx.plug_subst, ECtx.weaken, ECtx.subst_comp, Subst.succ_comp_one,
    ECtx.subst_id]
  rfl

/-! ## The term correspondence -/

mutual

/-- **`Corr r d`: the source term `r` is what the target term `d` computes**,
up to evidence, annotations and A-normalisation.  By recursion on `d`:

* an atom corresponds to its root variable — casts, packs and unpacks vanish;
* `new T ds` corresponds to an object literal with corresponding definitions,
  whatever the self type `T`;
* an application of atoms corresponds to the application of their roots;
* `let d u` corresponds to `E[r0]` when `d` corresponds to `r0` and `u` to the
  residual `E↑[x]`;
* a term-level `cast` is transparent. -/
def Corr {σ : Sig} : {s : Sig} → Oopsla16.Tm σ s → Tm σ s → Prop
  | _, r, .atom a => r = .tvar a.root
  | _, r, .new _ ds => ∃ Ds, r = .tobj Ds ∧ DmsCorr Ds ds
  | _, r, .app a l b => r = .tapp (.tvar a.root) l (.tvar b.root)
  | s, r, .let d u => ∃ (E : ECtx σ s) (r0 : Oopsla16.Tm σ s),
      r = E.plug r0 ∧ Corr r0 d ∧ Corr E.residual u
  | _, r, .cast d _ => Corr r d

/-- **`DmsCorr Ds ds`: member by member, at the same positions.**  A type
member is compared exactly; a method's annotations are ignored on both sides
and only the bodies are related. -/
def DmsCorr {σ : Sig} : {s : Sig} → Dms σ s → Defs σ s → Prop
  | _, Ds, .dnil => Ds = .dnil
  | _, Ds, .dty T ds => ∃ Ds', Ds = .dcons (.dty T) Ds' ∧ DmsCorr Ds' ds
  | s, Ds, .dfun _ _ d ds => ∃ (o1 : Option (Ty σ s)) (o2 : Option (Ty σ (s,x)))
      (r : Oopsla16.Tm σ (s,x)) (Ds' : Dms σ s),
      Ds = .dcons (.dfun o1 o2 r) Ds' ∧ Corr r d ∧ DmsCorr Ds' ds

end

/-! ### Introduction rules

`Corr` is a recursive definition, so anonymous-constructor notation does not
see through it; these are its rules as lemmas. -/

/-- An atom corresponds to its root. -/
theorem Corr.var {σ s : Sig} (a : Atom σ s) : Corr (.tvar a.root) (.atom a) := rfl

/-- An atom corresponds to the variable it is rooted at. -/
theorem Corr.var_of_root {σ s : Sig} {a : Atom σ s} {p : Vr σ s} (h : a.root = p) :
    Corr (.tvar p) (.atom a) := by
  subst h
  rfl

/-- An object literal corresponds to an object literal, whatever its self
type. -/
theorem Corr.obj {σ s : Sig} {Ds : Dms σ (s,x)} {ds : Defs σ (s,x)} (T : Ty σ (s,x))
    (h : DmsCorr Ds ds) : Corr (.tobj Ds) (.new T ds) := ⟨Ds, rfl, h⟩

/-- An application of atoms corresponds to the application of their roots. -/
theorem Corr.app {σ s : Sig} (a : Atom σ s) (l : Lb) (b : Atom σ s) :
    Corr (.tapp (.tvar a.root) l (.tvar b.root)) (.app a l b) := rfl

/-- An application of atoms corresponds to the application of the variables
they are rooted at. -/
theorem Corr.app_of_root {σ s : Sig} {a b : Atom σ s} {p q : Vr σ s} (l : Lb)
    (ha : a.root = p) (hb : b.root = q) :
    Corr (.tapp (.tvar p) l (.tvar q)) (.app a l b) := by
  subst ha hb
  rfl

/-- `let d u` corresponds to `E[r0]` when `d` corresponds to `r0` and `u` to
the residual of `E`. -/
theorem Corr.let_ {σ s : Sig} {r0 : Oopsla16.Tm σ s} {d : Tm σ s} {u : Tm σ (s,x)}
    (E : ECtx σ s) (h1 : Corr r0 d) (h2 : Corr E.residual u) :
    Corr (E.plug r0) (.let d u) := ⟨E, r0, rfl, h1, h2⟩

/-- A term-level cast is transparent. -/
theorem Corr.cast {σ s : Sig} {r : Oopsla16.Tm σ s} {d : Tm σ s} (e : Le σ s) (h : Corr r d) :
    Corr r (.cast d e) := h

/-- The empty definition lists correspond. -/
theorem DmsCorr.dnil {σ s : Sig} : DmsCorr (σ := σ) (s := s) .dnil .dnil := rfl

/-- A type member corresponds to the same type member. -/
theorem DmsCorr.dty {σ s : Sig} {Ds : Dms σ s} {ds : Defs σ s} (T : Ty σ s)
    (h : DmsCorr Ds ds) : DmsCorr (.dcons (.dty T) Ds) (.dty T ds) := ⟨Ds, rfl, h⟩

/-- A method corresponds to a method with a corresponding body, **whatever
the annotations** on either side. -/
theorem DmsCorr.dfun {σ s : Sig} {Ds : Dms σ s} {ds : Defs σ s} {r : Oopsla16.Tm σ (s,x)}
    {d : Tm σ (s,x)} (o1 : Option (Ty σ s)) (o2 : Option (Ty σ (s,x))) (S : Ty σ s)
    (U : Ty σ (s,x)) (hb : Corr r d) (h : DmsCorr Ds ds) :
    DmsCorr (.dcons (.dfun o1 o2 r) Ds) (.dfun S U d ds) := ⟨o1, o2, r, Ds, rfl, hb, h⟩

/-! ### The three A-normal shapes of an application

What an elaboration of `T_App`/`T_AppVar` produces when an operand is not a
variable.  In each, the atoms may carry any evidence; only their roots are
fixed. -/

/-- **Both operands bound**: `let x1 = d1 in let x2 = d2 in x1 l x2`.  The
argument's translation lives under the first binder, so it corresponds to the
weakened argument. -/
theorem Corr.anf_app {σ s : Sig} {t1 t2 : Oopsla16.Tm σ s} {d1 : Tm σ s} {d2 : Tm σ (s,x)}
    (l : Lb) {a b : Atom σ ((s,x),x)} (h1 : Corr t1 d1)
    (h2 : Corr (t2.subst (Subst.ofRename Rename.succ)) d2)
    (ha : a.root = .abs (.there .here)) (hb : b.root = .abs .here) :
    Corr (.tapp t1 l t2) (.let d1 (.let d2 (.app a l b))) :=
  Corr.let_ (.app1 .hole l t2) h1
    (Corr.let_ (.app2 (.abs .here) l .hole) h2 (Corr.app_of_root l ha hb))

/-- **Receiver bound, argument a variable**: `let x1 = d1 in x1 l b`.  This is
the shape a dependent `T_AppVar` needs, since binding the argument would let
the result type mention a `let`-bound variable. -/
theorem Corr.anf_recv {σ s : Sig} {t1 : Oopsla16.Tm σ s} {q : Vr σ s} {d1 : Tm σ s}
    (l : Lb) {a b : Atom σ (s,x)} (h1 : Corr t1 d1) (ha : a.root = .abs .here)
    (hb : b.root = q.weaken) : Corr (.tapp t1 l (.tvar q)) (.let d1 (.app a l b)) :=
  Corr.let_ (.app1 .hole l (.tvar q)) h1
    (Corr.app_of_root l ha (hb.trans (Vr.weaken_eq_subst_succ q)))

/-- **Receiver a variable, argument bound**: `let x2 = d2 in a l x2`. -/
theorem Corr.anf_arg {σ s : Sig} {p : Vr σ s} {t2 : Oopsla16.Tm σ s} {d2 : Tm σ s}
    (l : Lb) {a b : Atom σ (s,x)} (ha : a.root = p.weaken) (h2 : Corr t2 d2)
    (hb : b.root = .abs .here) : Corr (.tapp (.tvar p) l t2) (.let d2 (.app a l b)) :=
  Corr.let_ (.app2 p l .hole) h2
    (Corr.app_of_root l (ha.trans (Vr.weaken_eq_subst_succ p)) hb)

/-! ## Evidence invariance and substitution -/

mutual

/-- **The correspondence reads only the skeleton.** -/
theorem Corr.skel_iff {σ : Sig} : {s : Sig} → (d : Tm σ s) →
    ∀ r : Oopsla16.Tm σ s, Corr r d.skel ↔ Corr r d
  | _, .atom _, _ => Iff.rfl
  | _, .new _ ds, r => by simp only [Tm.skel, Corr, DmsCorr.skel_iff ds]
  | _, .app _ _ _, _ => Iff.rfl
  | _, .let d u, r => by simp only [Tm.skel, Corr, Corr.skel_iff d, Corr.skel_iff u]
  | _, .cast d _, r => Corr.skel_iff d r

/-- The same, at a definition list. -/
theorem DmsCorr.skel_iff {σ : Sig} : {s : Sig} → (ds : Defs σ s) →
    ∀ Ds : Dms σ s, DmsCorr Ds ds.skel ↔ DmsCorr Ds ds
  | _, .dnil, _ => Iff.rfl
  | _, .dty _ ds, Ds => by simp only [Defs.skel, DmsCorr, DmsCorr.skel_iff ds]
  | _, .dfun _ _ d ds, Ds => by
      simp only [Defs.skel, DmsCorr, Corr.skel_iff d, DmsCorr.skel_iff ds]

end

mutual

/-- **The correspondence commutes with every substitution**, read on the
substituted skeleton (`Erasure.Tm.skelSubst`).  One statement covers the
machine's instantiation, a store renaming and the typed substitution, because
all three have that skeleton. -/
theorem Corr.skelSubst {σ1 σ2 : Sig} : {s1 s2 : Sig} → (d : Tm σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → {r : Oopsla16.Tm σ1 s1} → Corr r d →
    Corr (r.subst θ) (d.skelSubst θ)
  | _, _, .atom _, _, _, h => by subst h; rfl
  | _, _, .new _ ds, θ, _, h => by
      obtain ⟨Ds, h1, h2⟩ := h
      subst h1
      exact ⟨Ds.subst θ.lift, rfl, DmsCorr.skelSubst ds θ.lift h2⟩
  | _, _, .app _ _ _, _, _, h => by subst h; rfl
  | _, _, .let d u, θ, _, h => by
      obtain ⟨E, r0, h1, h2, h3⟩ := h
      subst h1
      refine ⟨E.subst θ, r0.subst θ, ECtx.plug_subst E r0 θ, Corr.skelSubst d θ h2, ?_⟩
      rw [← ECtx.residual_subst_lift]
      exact Corr.skelSubst u θ.lift h3
  | _, _, .cast d _, θ, _, h => Corr.skelSubst d θ h

/-- The same, at a definition list. -/
theorem DmsCorr.skelSubst {σ1 σ2 : Sig} : {s1 s2 : Sig} → (ds : Defs σ1 s1) →
    (θ : Subst σ1 s1 σ2 s2) → {Ds : Dms σ1 s1} → DmsCorr Ds ds →
    DmsCorr (Ds.subst θ) (ds.skelSubst θ)
  | _, _, .dnil, _, _, h => by subst h; rfl
  | _, _, .dty _ ds, θ, _, h => by
      obtain ⟨Ds', h1, h2⟩ := h
      subst h1
      exact ⟨Ds'.subst θ, rfl, DmsCorr.skelSubst ds θ h2⟩
  | _, _, .dfun _ _ d ds, θ, _, h => by
      obtain ⟨o1, o2, r, Ds', h1, h2, h3⟩ := h
      subst h1
      exact ⟨o1.map (fun T => T.subst θ), o2.map (fun T => T.subst θ.lift), r.subst θ.lift,
        Ds'.subst θ, rfl, Corr.skelSubst d θ.lift h2, DmsCorr.skelSubst ds θ h3⟩

end

/-- **The machine's instantiation**: what `rename`, `alloc` and `app`
substitute on the target is what the source substitutes. -/
theorem Corr.inst {σ s1 s2 : Sig} {r : Oopsla16.Tm σ s1} {d : Tm σ s1} (h : Corr r d)
    (ι : Inst s1 s2) (y : BVar σ .var) : Corr (r.subst (ι.toSubst y)) (d.inst ι y) :=
  (Corr.skel_iff _ _).1 (by rw [Tm.skel_inst]; exact Corr.skelSubst d _ h)

/-- The machine's instantiation, at a definition list. -/
theorem DmsCorr.inst {σ s1 s2 : Sig} {Ds : Dms σ s1} {ds : Defs σ s1} (h : DmsCorr Ds ds)
    (ι : Inst s1 s2) (y : BVar σ .var) : DmsCorr (Ds.subst (ι.toSubst y)) (ds.inst ι y) :=
  (DmsCorr.skel_iff _ _).1 (by rw [Defs.skel_inst]; exact DmsCorr.skelSubst ds _ h)

/-- **Store renaming**, which allocation performs on both sides. -/
theorem Corr.renameStore {σ1 σ2 s : Sig} {r : Oopsla16.Tm σ1 s} {d : Tm σ1 s} (h : Corr r d)
    (ρ : Rename σ1 σ2) : Corr (r.renameStore ρ) (d.renameStore ρ) :=
  (Corr.skel_iff _ _).1 (by rw [Tm.skel_renameStore]; exact Corr.skelSubst d _ h)

/-- Store renaming, at a definition list. -/
theorem DmsCorr.renameStore {σ1 σ2 s : Sig} {Ds : Dms σ1 s} {ds : Defs σ1 s}
    (h : DmsCorr Ds ds) (ρ : Rename σ1 σ2) : DmsCorr (Ds.renameStore ρ) (ds.renameStore ρ) :=
  (DmsCorr.skel_iff _ _).1 (by rw [Defs.skel_renameStore]; exact DmsCorr.skelSubst ds _ h)

/-- **The syntactic substitution** `Subst.Tm.subst` at a generated
substitution corresponds to the substituted source term. -/
theorem Corr.subst {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {r : Oopsla16.Tm σ1 s1}
    {d : Tm σ1 s1} (h : Corr r d) (m : MonoSyn θ) : Corr (r.subst θ) (d.subst m) :=
  (Corr.skel_iff _ _).1 (by rw [Tm.skel_subst]; exact Corr.skelSubst d _ h)

/-- The typed substitution, at a definition list. -/
theorem DmsCorr.subst {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {Ds : Dms σ1 s1}
    {ds : Defs σ1 s1} (h : DmsCorr Ds ds) (m : MonoSyn θ) : DmsCorr (Ds.subst θ) (ds.subst m) :=
  (DmsCorr.skel_iff _ _).1 (by rw [Defs.skel_subst]; exact DmsCorr.skelSubst ds _ h)

/-- **The typed substitution theorem's output corresponds** to the substituted
source term.  `TermSubst.TmTy.substEv` re-chooses evidence, so its output is
not `t.subst m`; but it has the substituted skeleton
(`Preservation.TmTy.substEv_skel`), which is all the correspondence reads.
This is how an elaboration weakens a typed operand under a `let`
(`MonoSyn.EvA.weaken`) and keeps its correspondence. -/
theorem Corr.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {t : Tm σ1 s1} {T : Ty σ1 s1} {r : Oopsla16.Tm σ1 s1} (h : Corr r t)
    (d : TmTy G W Γ t T) {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') : Corr (r.subst θ) (TmTy.substEv d E).1 :=
  (Corr.skel_iff _ _).1 (by rw [TmTy.substEv_skel]; exact Corr.skelSubst t θ h)

/-- The typed substitution theorem's output, at a definition list. -/
theorem DmsCorr.substEv {σ1 s1 : Sig} {G : Store σ1 σ1} {W : StoreTy σ1} {Γ : Ctx σ1 s1}
    {ds : Defs σ1 s1} {T : Ty σ1 s1} {Ds : Dms σ1 s1} (h : DmsCorr Ds ds)
    (d : DefsTy G W Γ ds T) {σ2 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {m : MonoSyn θ}
    {G' : Store σ2 σ2} {W' : StoreTy σ2} {Γ' : Ctx σ2 s2}
    (E : MonoSyn.EvA G W Γ m G' W' Γ') : DmsCorr (Ds.subst θ) (DefsTy.substEv d E).defs :=
  (DmsCorr.skel_iff _ _).1 (by rw [DefsTy.substEv_skel]; exact DmsCorr.skelSubst ds θ h)

/-! ## Definition lists: positions and lookups -/

/-- Corresponding lists have the same length, hence the same labels. -/
theorem DmsCorr.length {σ s : Sig} : (ds : Defs σ s) → {Ds : Dms σ s} → DmsCorr Ds ds →
    Ds.length = ds.length
  | .dnil, _, h => by subst h; rfl
  | .dty _ ds, _, h => by
      obtain ⟨_, h1, h2⟩ := h
      subst h1
      exact congrArg (· + 1) (DmsCorr.length ds h2)
  | .dfun _ _ _ ds, _, h => by
      obtain ⟨_, _, _, _, h1, _, h2⟩ := h
      subst h1
      exact congrArg (· + 1) (DmsCorr.length ds h2)

/-- **A method the source reads is a method the target reads**, at the same
label, with a corresponding body. -/
theorem DmsCorr.get?_dfun {σ s : Sig} : (ds : Defs σ s) → {Ds : Dms σ s} → DmsCorr Ds ds →
    {l : Lb} → {o1 : Option (Ty σ s)} → {o2 : Option (Ty σ (s,x))} →
    {r : Oopsla16.Tm σ (s,x)} → Ds.get? l = some (.dfun o1 o2 r) →
    ∃ (S : Ty σ s) (U : Ty σ (s,x)) (d : Tm σ (s,x)), ds.fun? l = some (S, U, d) ∧ Corr r d
  | .dnil, _, h, _, _, _, _, hg => by subst h; cases hg
  | .dty _ ds, _, h, l, _, _, _, hg => by
      obtain ⟨Ds', h1, h2⟩ := h
      subst h1
      have hlen := DmsCorr.length ds h2
      simp only [Oopsla16.Dms.get?] at hg
      simp only [Defs.fun?]
      split at hg
      · cases hg
      · rename_i hne
        rw [if_neg (by rw [← hlen]; exact hne)]
        exact DmsCorr.get?_dfun ds h2 hg
  | .dfun S U d ds, _, h, l, _, _, _, hg => by
      obtain ⟨_, _, r', Ds', h1, hc, h2⟩ := h
      subst h1
      have hlen := DmsCorr.length ds h2
      simp only [Oopsla16.Dms.get?] at hg
      simp only [Defs.fun?]
      split at hg
      · rename_i heq
        cases hg
        rw [if_pos (by rw [← hlen]; exact heq)]
        exact ⟨S, U, d, rfl, hc⟩
      · rename_i hne
        rw [if_neg (by rw [← hlen]; exact hne)]
        exact DmsCorr.get?_dfun ds h2 hg

/-- **A method the target reads is a method the source reads**, at the same
label, with a corresponding body and some annotations. -/
theorem DmsCorr.fun?_some {σ s : Sig} : (ds : Defs σ s) → {Ds : Dms σ s} → DmsCorr Ds ds →
    {l : Lb} → {S : Ty σ s} → {U : Ty σ (s,x)} → {d : Tm σ (s,x)} →
    ds.fun? l = some (S, U, d) →
    ∃ (o1 : Option (Ty σ s)) (o2 : Option (Ty σ (s,x))) (r : Oopsla16.Tm σ (s,x)),
      Ds.get? l = some (.dfun o1 o2 r) ∧ Corr r d
  | .dnil, _, _, _, _, _, _, hf => by cases hf
  | .dty _ ds, _, h, l, _, _, _, hf => by
      obtain ⟨Ds', h1, h2⟩ := h
      subst h1
      have hlen := DmsCorr.length ds h2
      simp only [Defs.fun?] at hf
      simp only [Oopsla16.Dms.get?]
      split at hf
      · cases hf
      · rename_i hne
        rw [if_neg (by rw [hlen]; exact hne)]
        exact DmsCorr.fun?_some ds h2 hf
  | .dfun _ _ _ ds, _, h, l, _, _, _, hf => by
      obtain ⟨o1, o2, r, Ds', h1, hc, h2⟩ := h
      subst h1
      have hlen := DmsCorr.length ds h2
      simp only [Defs.fun?] at hf
      simp only [Oopsla16.Dms.get?]
      split at hf
      · rename_i heq
        cases hf
        rw [if_pos (by rw [hlen]; exact heq)]
        exact ⟨o1, o2, r, rfl, hc⟩
      · rename_i hne
        rw [if_neg (by rw [hlen]; exact hne)]
        exact DmsCorr.fun?_some ds h2 hf

/-! ## Stores -/

/-- **Corresponding stores**: at every location, the source's definitions
correspond to the machine's.  Up to annotations and evidence, the machine store
is therefore the source store, as `MachineStore.erase` says up to annotations
on the nose. -/
def StoreCorr {σ : Sig} (G : Store σ σ) (Gt : MachineStore σ σ) : Prop :=
  ∀ l : BVar σ .var, DmsCorr (G.lookup l) (Gt.lookup l)

/-- The empty stores correspond. -/
theorem StoreCorr.nil : StoreCorr (Store.nil : Store [] []) MachineStore.nil :=
  fun l => nomatch l

/-- Weakening both stores and adding corresponding entries keeps them
corresponding. -/
theorem StoreCorr.cons_weaken {σ : Sig} {G : Store σ σ} {Gt : MachineStore σ σ}
    (h : StoreCorr G Gt) {Ds : Dms (σ,x) []} {ds : Defs (σ,x) []} (hd : DmsCorr Ds ds) :
    StoreCorr (G.weakenStore.cons Ds) (Gt.weakenStore.cons ds) := fun l =>
  match l with
  | .here => hd
  | .there l => by
      show DmsCorr (G.weakenStore.lookup l) (Gt.weakenStore.lookup l)
      rw [Oopsla16.Store.lookup_renameStore, MachineStore.lookup_renameStore]
      exact (h l).renameStore _

/-- **Allocation keeps the stores corresponding**: `ST_Obj`'s store and the
machine's `alloc` store, from corresponding literals. -/
theorem StoreCorr.alloc {σ : Sig} {G : Store σ σ} {Gt : MachineStore σ σ}
    (h : StoreCorr G Gt) {D : Dms σ ([],x)} {ds : Defs σ ([],x)} (hd : DmsCorr D ds) :
    StoreCorr (G.weakenStore.cons (D.weakenStore.substVr (.conc .here)))
      (Gt.weakenStore.cons (ds.weakenStore.inst .base .here)) :=
  h.cons_weaken ((hd.renameStore Rename.succ).inst .base .here)

/-- An honest machine store's typed witnesses correspond to the source store
wherever the running store does: the witness has the running entry's
skeleton. -/
theorem MachineStore.Honest.dmsCorr {σ : Sig} {G : Store σ σ} {Gt : MachineStore σ σ}
    {W : StoreTy σ} (h : MachineStore.Honest Gt W) (hs : StoreCorr G Gt) (l : BVar σ .var) :
    DmsCorr (G.lookup l) (h.at' l).defs := by
  rw [← DmsCorr.skel_iff, (h.at' l).skel, DmsCorr.skel_iff]
  exact hs l

/-! ## Continuations -/

/-- **Re-plug a continuation's frames as term constructors**: a `let` frame
becomes a `let`, a coercion frame a `cast`.  Unlike `Erasure.Cont.plug`, this
stays in the target. -/
def Cont.fill {σ : Sig} : Cont σ → Tm σ [] → Tm σ []
  | .nil, t => t
  | .cons K (.let u), t => K.fill (.let t u)
  | .cons K (.cast e), t => K.fill (.cast t e)

/-- Filling commutes with the skeleton. -/
theorem Cont.skel_fill {σ : Sig} : (K : Cont σ) → (t : Tm σ []) →
    (K.fill t).skel = K.skel.fill t.skel
  | .nil, _ => rfl
  | .cons K (.let u), t => by
      show (K.fill (.let t u)).skel = _
      rw [Cont.skel_fill K]
      rfl
  | .cons K (.cast e), t => by
      show (K.fill (.cast t e)).skel = _
      rw [Cont.skel_fill K]
      rfl

/-- Filling commutes with a store renaming. -/
theorem Cont.fill_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : (K : Cont σ1) →
    (t : Tm σ1 []) → (K.fill t).renameStore ρ = (K.renameStore ρ).fill (t.renameStore ρ)
  | .nil, _ => rfl
  | .cons K (.let u), t => Cont.fill_renameStore ρ K (.let t u)
  | .cons K (.cast e), t => Cont.fill_renameStore ρ K (.cast t e)

/-- **Filling is monotone**: a running term that corresponds to at least what
another does can replace it under any continuation. -/
theorem Cont.corr_fill_mono {σ : Sig} : (K : Cont σ) → {t t' : Tm σ []} →
    (∀ r, Corr r t → Corr r t') → ∀ r, Corr r (K.fill t) → Corr r (K.fill t')
  | .nil, _, _, hm => hm
  | .cons K (.let u), t, t', hm =>
      Cont.corr_fill_mono K (t := .let t u) (t' := .let t' u) (fun r h => by
        obtain ⟨E, r0, h1, h2, h3⟩ := h
        exact ⟨E, r0, h1, hm r0 h2, h3⟩)
  | .cons K (.cast _), _, _, hm => Cont.corr_fill_mono K hm

/-- **`KCorr K C`: the continuation `K` is the source context `C`.**  Each
`let` frame contributes the context whose residual its body corresponds to,
innermost last; coercion frames contribute nothing. -/
def KCorr {σ : Sig} : Cont σ → ECtx σ [] → Prop
  | .nil, C => C = .hole
  | .cons K (.let u), C => ∃ C' E : ECtx σ [], KCorr K C' ∧ C = C'.comp E ∧ Corr E.residual u
  | .cons K (.cast _), C => KCorr K C

/-- **Decomposition**: a filled continuation corresponds to a source term
exactly when that term is a source context for the continuation, plugged with
what the running term corresponds to. -/
theorem corr_fill_iff {σ : Sig} : (K : Cont σ) → (t : Tm σ []) → (r : Oopsla16.Tm σ []) →
    (Corr r (K.fill t) ↔
      ∃ (C : ECtx σ []) (r0 : Oopsla16.Tm σ []), KCorr K C ∧ r = C.plug r0 ∧ Corr r0 t)
  | .nil, t, r => by
      constructor
      · intro h
        exact ⟨.hole, r, rfl, rfl, h⟩
      · rintro ⟨C, r0, hC, hr, h⟩
        have hC' : C = .hole := hC
        subst hC' hr
        exact h
  | .cons K (.let u), t, r => by
      constructor
      · intro h
        obtain ⟨C, r1, hK, hr, h1⟩ := (corr_fill_iff K (.let t u) r).1 h
        obtain ⟨E, r0, h2, h3, h4⟩ := h1
        refine ⟨C.comp E, r0, ⟨C, E, hK, rfl, h4⟩, ?_, h3⟩
        rw [ECtx.plug_comp, hr, h2]
      · rintro ⟨C, r0, hK, hr, h⟩
        obtain ⟨C', E, hK', hC, h3⟩ := hK
        refine (corr_fill_iff K (.let t u) r).2 ⟨C', E.plug r0, hK', ?_, ⟨E, r0, rfl, h, h3⟩⟩
        rw [hr, hC, ECtx.plug_comp]
  | .cons K (.cast e), t, r => corr_fill_iff K (.cast t e) r

/-- A store renaming moves a continuation's source context along. -/
theorem KCorr.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : (K : Cont σ1) →
    {C : ECtx σ1 []} → KCorr K C → KCorr (K.renameStore ρ) (C.renameStore ρ)
  | .nil, _, h => by
      have h' : _ = ECtx.hole := h
      subst h'
      rfl
  | .cons K (.let u), _, h => by
      obtain ⟨C', E, hK, hC, h3⟩ := h
      subst hC
      refine ⟨C'.renameStore ρ, E.renameStore ρ, KCorr.renameStore ρ K hK,
        ECtx.comp_subst C' E _, ?_⟩
      have h4 := Corr.renameStore h3 ρ
      rw [Oopsla16.Tm.renameStore, ← Oopsla16.Subst.lift_ofStore, ECtx.residual_subst_lift] at h4
      exact h4
  | .cons K (.cast _), _, h => KCorr.renameStore ρ K h

/-! ## The relation between configurations and states -/

/-- **The correspondence between a source configuration and a target
state**, at one store scope: the stores correspond pointwise and the source
term corresponds to the state's filled continuation.  Up to annotations
(`Corr`, `DmsCorr`), up to evidence (`Rel.of_skel`), and up to A-normalisation
(`ECtx`). -/
structure Rel {σ : Sig} (G : Store σ σ) (t : Oopsla16.Tm σ []) (st : State σ) : Prop where
  /-- The stores correspond. -/
  store : StoreCorr G st.G
  /-- The source term is what the state computes. -/
  tm : Corr t (st.K.fill st.t)

/-- **Initial states**: a closed target term corresponding to a closed source
term starts a related run. -/
theorem Rel.init {t : Oopsla16.Tm [] []} {d : Tm [] []} (h : Corr t d) :
    Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩ := ⟨StoreCorr.nil, h⟩

/-- An initial state is related exactly when its term corresponds. -/
theorem Rel.init_iff {t : Oopsla16.Tm [] []} {d : Tm [] []} :
    Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩ ↔ Corr t d := ⟨fun h => h.tm, Rel.init⟩

/-- The machine's `let` step is invisible to the relation. -/
theorem Rel.let_ {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {d : Tm σ []} {u : Tm σ ([],x)} (h : Rel G t ⟨Gt, K, .let d u⟩) :
    Rel G t ⟨Gt, K ▹ .let u, d⟩ := ⟨h.store, h.tm⟩

/-- The machine's `castPush` step is invisible to the relation. -/
theorem Rel.castPush {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {d : Tm σ []} {e : Le σ []} (h : Rel G t ⟨Gt, K, .cast d e⟩) :
    Rel G t ⟨Gt, K ▹ .cast e, d⟩ := ⟨h.store, h.tm⟩

/-- The machine's `castAtom` step keeps the relation, the source not moving. -/
theorem Rel.castAtom {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {a : Atom σ []} {e : Le σ []} (h : Rel G t ⟨Gt, K ▹ .cast e, .atom a⟩) :
    Rel G t ⟨Gt, K, .atom (.cast a e)⟩ :=
  ⟨h.store, Cont.corr_fill_mono K (t := .cast (.atom a) e) (t' := .atom (.cast a e))
    (fun _ h => h) t h.tm⟩

/-- **The machine's `rename` step keeps the relation, the source not
moving**: substituting the atom's root into the `let` body refills the
context's hole with the variable that was there (`ECtx.residual_one`). -/
theorem Rel.rename {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {u : Tm σ ([],x)} {a : Atom σ []} (h : Rel G t ⟨Gt, K ▹ .let u, .atom a⟩) :
    Rel G t ⟨Gt, K, u.inst .base (Vr.loc a.root)⟩ :=
  ⟨h.store, Cont.corr_fill_mono K (t := .let (.atom a) u) (t' := u.inst .base (Vr.loc a.root))
    (fun r hr => by
      obtain ⟨E, r0, h1, h2, h3⟩ := hr
      have h4 := Corr.inst h3 .base (Vr.loc a.root)
      have h5 : r0 = .tvar a.root := h2
      rw [show (Inst.base.toSubst (Vr.loc a.root) : Subst σ ([],x) σ []) =
        Subst.one (.conc (Vr.loc a.root)) from rfl, ECtx.residual_one, Vr.conc_loc] at h4
      rw [h1, h5]
      exact h4) t h.tm⟩

/-- **A related final state has a source answer.** -/
theorem Rel.final {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) (hf : st.Final) : t.IsAnswer := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨hK, a, ha⟩ := hf
  simp only at hK ha
  subst hK ha
  have ht : t = .tvar a.root := h.tm
  subst ht
  rw [← Vr.conc_loc a.root]
  trivial

/-- **The relation is invariant under evidence**: a state with the same
store, continuation and term skeletons is related to the same configuration. -/
theorem Rel.of_skel {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st st' : State σ}
    (h : Rel G t st) (hG : ∀ l, (st'.G.lookup l).skel = (st.G.lookup l).skel)
    (hK : st'.K.skel = st.K.skel) (ht : st'.t.skel = st.t.skel) : Rel G t st' := by
  refine ⟨fun l => ?_, ?_⟩
  · rw [← DmsCorr.skel_iff, hG, DmsCorr.skel_iff]
    exact h.store l
  · rw [← Corr.skel_iff, Cont.skel_fill, hK, ht, ← Cont.skel_fill, Corr.skel_iff]
    exact h.tm

/-- **The typed witness corresponds too**: whenever a typed state is related,
the term and continuation `Preservation.StateTy` exhibits — which carry the
evidence the running state has dropped — correspond to the same source term.
So preservation's witness and the running term are interchangeable for the
relation. -/
theorem StateTy.corr_witness {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    {W : StoreTy σ} {U : Ty σ []} (d : StateTy st W U) (h : Rel G t st) :
    Corr t (d.cont.fill d.tm) := by
  rw [← Corr.skel_iff, Cont.skel_fill, d.contSkel, d.tmSkel, ← Cont.skel_fill, Corr.skel_iff]
  exact h.tm

/-! ## The source machine -/

/-- **A stuck source configuration**: not an answer, and no step. -/
def SrcStuck {σ : Sig} (G : Store σ σ) (t : Oopsla16.Tm σ []) : Prop :=
  ¬ t.IsAnswer ∧
    ¬ ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
      Oopsla16.Step g G t G' t'

/-- A variable does not step. -/
theorem tvar_not_step {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {p : Vr σ1 []}
    {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} : ¬ Oopsla16.Step g G (.tvar p) G' t' := by
  intro h
  cases h

/-- An answer does not step. -/
theorem answer_not_step {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} (ha : t.IsAnswer) :
    ¬ Oopsla16.Step g G t G' t' := by
  cases t with
  | tvar p => exact tvar_not_step
  | tobj _ => exact ha.elim
  | tapp _ _ _ => exact ha.elim

/-- Plugging yields a variable only at the hole. -/
theorem ECtx.plug_eq_tvar {σ s : Sig} : (E : ECtx σ s) → {t : Oopsla16.Tm σ s} →
    {p : Vr σ s} → E.plug t = .tvar p → t = .tvar p
  | .hole, _, _, h => h
  | .app1 _ _ _, _, _, h => by cases h
  | .app2 _ _ _, _, _, h => by cases h

/-- A context plugged with a non-variable is not an answer. -/
theorem ECtx.plug_not_answer {σ : Sig} (E : ECtx σ []) {t : Oopsla16.Tm σ []}
    (hnv : ∀ p, t ≠ .tvar p) : ¬ (E.plug t).IsAnswer := by
  cases E with
  | hole =>
      intro ha
      cases t with
      | tvar p => exact hnv p rfl
      | tobj _ => exact ha
      | tapp _ _ _ => exact ha
  | app1 _ _ _ => exact id
  | app2 _ _ _ => exact id

/-- **The congruence rules, closed under composition**: a step lifts through
any evaluation context, which is weakened along the step's allocation, as
`ST_App1` and `ST_App2` weaken the operand they do not reduce. -/
theorem ECtx.step {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {t : Oopsla16.Tm σ1 []}
    {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} (hs : Oopsla16.Step g G t G' t') :
    (E : ECtx σ1 []) → Oopsla16.Step g G (E.plug t) G' ((E.renameStore g.rename).plug t')
  | .hole => hs
  | .app1 E _ _ => .ST_App1 (ECtx.step hs E)
  | .app2 p _ E => by
      cases p with
      | conc f => exact .ST_App2 (ECtx.step hs E)
      | abs z => exact nomatch z

/-- Inverting a step of an application whose receiver is not a variable: it is
`ST_App1`. -/
theorem step_app1_inv {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    {u : Oopsla16.Tm σ1 []} {l : Lb} {t2 : Oopsla16.Tm σ1 []} {t' : Oopsla16.Tm σ2 []}
    (hs : Oopsla16.Step g G (.tapp u l t2) G' t') (hnv : ∀ p, u ≠ .tvar p) :
    ∃ u', Oopsla16.Step g G u G' u' ∧ t' = .tapp u' l (t2.renameStore g.rename) := by
  cases hs with
  | ST_AppAbs _ => exact absurd rfl (hnv _)
  | ST_App1 h => exact ⟨_, h, rfl⟩
  | ST_App2 _ => exact absurd rfl (hnv _)

/-- Inverting a step of an application of a variable to a non-variable: it is
`ST_App2`. -/
theorem step_app2_inv {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    {p : Vr σ1 []} {l : Lb} {u : Oopsla16.Tm σ1 []} {t' : Oopsla16.Tm σ2 []}
    (hs : Oopsla16.Step g G (.tapp (.tvar p) l u) G' t') (hnv : ∀ q, u ≠ .tvar q) :
    ∃ u', Oopsla16.Step g G u G' u' ∧
      t' = .tapp (.tvar (p.subst (Subst.ofStore g.rename))) l u' := by
  cases hs with
  | ST_AppAbs _ => exact absurd rfl (hnv _)
  | ST_App1 h => exact absurd h tvar_not_step
  | ST_App2 h => exact ⟨_, h, rfl⟩

/-- **Focused inversion**: a step of a context plugged with a non-variable is
a step of the plugged term, lifted.  This is the form of determinism the
simulation needs — at the focus, the source has no choice — and it keeps the
step's store scope and `Grows` index, so no dependent equation arises. -/
theorem ECtx.plug_inv {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {G' : Store σ2 σ2} :
    (E : ECtx σ1 []) → {t0 : Oopsla16.Tm σ1 []} → {t' : Oopsla16.Tm σ2 []} →
    (∀ p, t0 ≠ .tvar p) → Oopsla16.Step g G (E.plug t0) G' t' →
    ∃ t0', Oopsla16.Step g G t0 G' t0' ∧ t' = (E.renameStore g.rename).plug t0'
  | .hole, _, _, _, hs => ⟨_, hs, rfl⟩
  | .app1 E _ _, _, _, hnv, hs => by
      obtain ⟨u', h1, h2⟩ := step_app1_inv hs (fun p h => hnv p (ECtx.plug_eq_tvar E h))
      obtain ⟨t0', h3, h4⟩ := ECtx.plug_inv E hnv h1
      exact ⟨t0', h3, by rw [h2, h4]; rfl⟩
  | .app2 _ _ E, _, _, hnv, hs => by
      obtain ⟨u', h1, h2⟩ := step_app2_inv hs (fun p h => hnv p (ECtx.plug_eq_tvar E h))
      obtain ⟨t0', h3, h4⟩ := ECtx.plug_inv E hnv h1
      exact ⟨t0', h3, by rw [h2, h4]; rfl⟩

/-! ## Target runs -/

/-- Growth along no allocation, then along `g`, is growth along `g`.
`Oopsla16.Grows.comp` recurses on its second argument, so this needs a
proof. -/
theorem growsReflComp {σ1 : Sig} : {σ2 : Sig} → (g : Grows σ1 σ2) → Grows.refl.comp g = g
  | _, .refl => rfl
  | _, .snoc g => congrArg Grows.snoc (growsReflComp g)

/-- Target runs concatenate, their `Grows` indices composing. -/
theorem Steps.trans {σ1 : Sig} {st1 : State σ1} : {σ2 σ3 : Sig} → {g : Grows σ1 σ2} →
    {h : Grows σ2 σ3} → {st2 : State σ2} → {st3 : State σ3} →
    Steps g st1 st2 → Steps h st2 st3 → Steps (g.comp h) st1 st3 := by
  intro σ2 σ3 g h st2 st3 h1 h2
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih =>
      have hc := Steps.tail (ih h1) hstep
      rwa [growsCompAssoc] at hc

/-- One step is a run at the same index. -/
theorem Steps.single {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1} {st' : State σ2}
    (h : Step g st st') : Steps g st st' := by
  have hc := Steps.tail Steps.refl h
  rwa [growsReflComp] at hc

/-- An invocation of a label the receiver's root does not define is a stuck
target state. -/
theorem State.stuck_app {σ : Sig} {Gt : MachineStore σ σ} {K : Cont σ} {a b : Atom σ []}
    {l : Lb} (hf : (Gt.lookup (Vr.loc a.root)).fun? l = none) :
    State.Stuck ⟨Gt, K, .app a l b⟩ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, a', ha⟩
    exact absurd ha (by
      show ¬ (Tm.app _ _ _ = Tm.atom a')
      intro h
      cases h)
  · rintro ⟨σ', g, st', hs⟩
    cases hs with
    | app hf' =>
        rw [hf] at hf'
        cases hf'

/-! ## The specifications

The statements the later stages inhabit, and the statement they combine to.
`ElabSpec` is the one this module does **not** prove (`ElaborationFull.elabSpec`
does); `SimStepSpec` and `SimStuckSpec` are proved below (`sim_step`,
`sim_stuck`). -/

/-- The store typing of the empty store. -/
def emptyStoreTy : StoreTy [] := fun l => nomatch l

/-- **Track ELAB's obligation**: every closed source typing over the empty
store yields a target term typed over the empty store whose initial machine
state is related to the source's initial configuration.  By `Rel.init_iff`,
the relation part is just `Corr t d`.  Not proved here, except on the fragment
(`elabSpec_frag`); proved in general by `ElaborationFull.elabSpec`. -/
abbrev ElabSpec : Prop :=
  ∀ {t : Oopsla16.Tm [] []} {T : Ty [] []}, HasType Store.nil Ctx.nil t T →
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧ Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩

/-- **The compositional form of `ElabSpec`**, which an elaboration by
recursion on derivations would produce: every source typing, at any store,
store typing, context and scope, elaborates to a target typing at the same
type whose term corresponds.  A strengthening, not an obligation;
`ElabSpecGen.toElabSpec` is the reduction. -/
abbrev ElabSpecGen : Type :=
  ∀ {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} {t : Oopsla16.Tm σ s}
    {T : Ty σ s}, HasType G Γ t T → (d : Tm σ s) × TmTy G W Γ d T × PLift (Corr t d)

/-- The compositional form implies the closed one. -/
theorem ElabSpecGen.toElabSpec (E : ElabSpecGen) : ElabSpec := fun ht =>
  ⟨emptyStoreTy, (E emptyStoreTy ht).1, _, ⟨(E emptyStoreTy ht).2.1⟩,
    Rel.init (E emptyStoreTy ht).2.2.down⟩

/-- **Track SIM's first obligation**: every source step from a related
configuration is matched by a target run, at the **same** `Grows` index, to a
related state.  Proved: `sim_step`. -/
abbrev SimStepSpec : Prop :=
  ∀ {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {t : Oopsla16.Tm σ1 []}
    {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1},
    Rel G t st → Oopsla16.Step g G t G' t' → ∃ st' : State σ2, Steps g st st' ∧ Rel G' t' st'

/-- **Track SIM's second obligation, stuck reflection in the form the
transport needs**: from a state related to a stuck source configuration, the
target runs into a stuck state.  The literal form — "a related target state
that can step has a source that can step" — is false
(`LiteralReflection.literal_reflection_false`).  Proved: `sim_stuck`. -/
abbrev SimStuckSpec : Prop :=
  ∀ {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ},
    Rel G t st → SrcStuck G t →
      ∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' ∧ st'.Stuck

/-- Track SIM's obligations together.  Proved: `sim_spec`. -/
abbrev SimSpec : Prop := SimStepSpec ∧ SimStuckSpec

/-- **Type safety of `Oopsla16`'s own machine**: no configuration reachable
from a closed term typed over the empty store is stuck.  `oopsla16_safety`
proves it under `ElabSpec`; `ElaborationFull.oopsla16Safety_holds` proves it
outright. -/
abbrev Oopsla16Safety : Prop :=
  ∀ {t : Oopsla16.Tm [] []} {T : Ty [] []}, HasType Store.nil Ctx.nil t T →
    ∀ {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []},
      Oopsla16.Steps g Store.nil t G' t' → ¬ SrcStuck G' t'

/-! ## The transport -/

/-- The simulation along a whole source run.

**Stated with a hypothesis:** `hS : SimStepSpec`, inhabited by `sim_step`. -/
theorem Rel.steps (hS : SimStepSpec) {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1}
    (h : Rel G t st) (run : Oopsla16.Steps g G t G' t') :
    ∃ st' : State σ2, Steps g st st' ∧ Rel G' t' st' := by
  induction run with
  | refl => exact ⟨st, .refl, h⟩
  | tail _ hstep ih =>
      obtain ⟨st1, h1, hr1⟩ := ih h
      obtain ⟨st2, h2, hr2⟩ := hS hr1 hstep
      exact ⟨st2, Steps.trans h1 h2, hr2⟩

/-- **The transport from one typed target term**: if a closed typed target
term's initial state is related to a source term, no configuration the source
reaches is stuck.  The source run is simulated by a target run from the typed
term; a stuck source configuration would lead the target into a stuck state;
`MethodInversion.safety'` says there is none.

**Stated with a hypothesis:** `hS : SimSpec`, inhabited by `sim_spec`. -/
theorem transport_from (hS : SimSpec) {W : StoreTy []} {d : Tm [] []} {T' : Ty [] []}
    (hd : TmTy Store.nil W Ctx.nil d T') {t : Oopsla16.Tm [] []}
    (hc : Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (run : Oopsla16.Steps g Store.nil t G' t') :
    ¬ SrcStuck G' t' := by
  intro hst
  obtain ⟨st1, h1, hr1⟩ := Rel.steps hS.1 hc run
  obtain ⟨_, _, st2, h2, hst2⟩ := hS.2 hr1 hst
  exact safety' hd (Steps.trans h1 h2) hst2

/-- **The transport argument**: `ElabSpec` and `SimSpec`, with the target's
hypothesis-free `safety'`, give type safety of `Oopsla16`.

**Stated with two hypotheses:** `hE : ElabSpec`, which this module does not
prove (Track ELAB; `ElaborationFull.elabSpec` inhabits it), and `hS : SimSpec`,
which `sim_spec` inhabits. -/
theorem transport (hE : ElabSpec) (hS : SimSpec) : Oopsla16Safety := by
  intro t T ht σ g G' t' run
  obtain ⟨W, d, T', ⟨hd⟩, hc⟩ := hE ht
  exact transport_from hS hd hc run

/-! ## The simulation

Two phases.  **Administrative normalisation** (`normalize`): the four steps
`let`, `castPush`, `castAtom` and `rename` keep the relation with the source
standing still, and they terminate — `castAtom` and `rename` consume a frame,
`let` and `castPush` shrink the running term — at a *focused* state: final, or
about to allocate, or about to invoke.  **The focus** (`Rel.sim_new`,
`Rel.sim_app`): the relation decomposes the source term as a context plugged
with the focused redex; `ECtx.plug_inv` says the source's step is that redex's
contraction, and the target's `alloc` or `app` performs the same one. -/

/-- The relation, decomposed at the running term. -/
theorem Rel.decompose {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {d : Tm σ []} (h : Rel G t ⟨Gt, K, d⟩) :
    ∃ (C : ECtx σ []) (r0 : Oopsla16.Tm σ []), KCorr K C ∧ t = C.plug r0 ∧ Corr r0 d :=
  (corr_fill_iff K d t).1 h.tm

/-- A state about to allocate has a source that allocates. -/
theorem Rel.new_steps {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {T : Ty σ ([],x)} {ds : Defs σ ([],x)} (h : Rel G t ⟨Gt, K, .new T ds⟩) :
    ∃ (G' : Store (σ,x) (σ,x)) (t' : Oopsla16.Tm (σ,x) []),
      Oopsla16.Step (.snoc .refl) G t G' t' := by
  obtain ⟨C, r0, -, ht, hr0⟩ := h.decompose
  obtain ⟨Ds, hr0', -⟩ := hr0
  subst ht hr0'
  exact ⟨_, _, ECtx.step .ST_Obj C⟩

/-- **The allocation case**: every source step from a configuration related
to a state about to allocate is `ST_Obj` in context, and the machine's
`alloc` matches it. -/
theorem Rel.sim_new {σ σ2 : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {T : Ty σ ([],x)} {ds : Defs σ ([],x)} {g : Grows σ σ2} {G' : Store σ2 σ2}
    {t' : Oopsla16.Tm σ2 []} (h : Rel G t ⟨Gt, K, .new T ds⟩)
    (hs : Oopsla16.Step g G t G' t') :
    ∃ st' : State σ2, Step g ⟨Gt, K, .new T ds⟩ st' ∧ Rel G' t' st' := by
  obtain ⟨C, r0, hK, ht, hr0⟩ := h.decompose
  obtain ⟨Ds, hr0', hDs⟩ := hr0
  subst ht hr0'
  obtain ⟨t0', hs0, ht'⟩ := ECtx.plug_inv C (fun p h => by cases h) hs
  subst ht'
  cases hs0
  refine ⟨_, Step.alloc, ⟨StoreCorr.alloc h.store hDs, ?_⟩⟩
  exact (corr_fill_iff _ _ _).2
    ⟨C.renameStore Rename.succ, _, KCorr.renameStore _ K hK, rfl, rfl⟩

/-- A state about to invoke a method its receiver defines has a source that
invokes it. -/
theorem Rel.app_steps {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {a b : Atom σ []} {l : Lb} {S : Ty σ []} {U : Ty σ ([],x)}
    {body : Tm σ ([],x)} (h : Rel G t ⟨Gt, K, .app a l b⟩)
    (hf : (Gt.lookup (Vr.loc a.root)).fun? l = some (S, U, body)) :
    ∃ t' : Oopsla16.Tm σ [], Oopsla16.Step .refl G t G t' := by
  obtain ⟨C, r0, -, ht, hr0⟩ := h.decompose
  have hr0' : r0 = .tapp (.tvar a.root) l (.tvar b.root) := hr0
  subst ht hr0'
  obtain ⟨o1, o2, r, hg, -⟩ := DmsCorr.fun?_some _ (h.store (Vr.loc a.root)) hf
  rw [← Vr.conc_loc a.root, ← Vr.conc_loc b.root]
  exact ⟨_, ECtx.step (.ST_AppAbs hg) C⟩

/-- **The invocation case**: every source step from a configuration related
to a state about to invoke is `ST_AppAbs` in context, and the machine's `app`
matches it, running a body that corresponds to the source's. -/
theorem Rel.sim_app {σ σ2 : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {a b : Atom σ []} {l : Lb} {g : Grows σ σ2} {G' : Store σ2 σ2}
    {t' : Oopsla16.Tm σ2 []} (h : Rel G t ⟨Gt, K, .app a l b⟩)
    (hs : Oopsla16.Step g G t G' t') :
    ∃ st' : State σ2, Step g ⟨Gt, K, .app a l b⟩ st' ∧ Rel G' t' st' := by
  obtain ⟨C, r0, hK, ht, hr0⟩ := h.decompose
  have hr0' : r0 = .tapp (.tvar a.root) l (.tvar b.root) := hr0
  subst ht hr0'
  obtain ⟨t0', hs0, ht'⟩ := ECtx.plug_inv C (fun p h => by cases h) hs
  subst ht'
  rw [← Vr.conc_loc a.root, ← Vr.conc_loc b.root] at hs0
  cases hs0 with
  | ST_AppAbs hl =>
      obtain ⟨S, U, body, hf, hc⟩ := DmsCorr.get?_dfun _ (h.store (Vr.loc a.root)) hl
      refine ⟨_, Step.app hf, ⟨h.store, ?_⟩⟩
      rw [show (Grows.refl : Grows σ σ).rename = Rename.id from rfl, ECtx.renameStore_id]
      exact (corr_fill_iff _ _ _).2 ⟨C, _, hK, rfl, Corr.inst hc .base _⟩
  | ST_App1 h1 => exact absurd h1 tvar_not_step
  | ST_App2 h2 => exact absurd h2 tvar_not_step

/-- **A stuck invocation is stuck in the source too.** -/
theorem Rel.app_stuck {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {Gt : MachineStore σ σ}
    {K : Cont σ} {a b : Atom σ []} {l : Lb} (h : Rel G t ⟨Gt, K, .app a l b⟩)
    (hf : (Gt.lookup (Vr.loc a.root)).fun? l = none) : SrcStuck G t := by
  obtain ⟨C, r0, -, ht, hr0⟩ := h.decompose
  have hr0' : r0 = .tapp (.tvar a.root) l (.tvar b.root) := hr0
  subst ht hr0'
  refine ⟨ECtx.plug_not_answer C (fun p h => by cases h), ?_⟩
  rintro ⟨σ', g, G', t', hs⟩
  obtain ⟨t0', hs0, -⟩ := ECtx.plug_inv C (fun p h => by cases h) hs
  rw [← Vr.conc_loc a.root, ← Vr.conc_loc b.root] at hs0
  cases hs0 with
  | ST_AppAbs hl =>
      obtain ⟨S, U, body, hf', -⟩ := DmsCorr.get?_dfun _ (h.store (Vr.loc a.root)) hl
      rw [hf] at hf'
      cases hf'
  | ST_App1 h1 => exact tvar_not_step h1
  | ST_App2 h2 => exact tvar_not_step h2

/-- The administrative measure of a term: its `let` and `cast` nodes outside
object literals, the nodes `let` and `castPush` take apart. -/
def Tm.nAdm {σ : Sig} : {s : Sig} → Tm σ s → Nat
  | _, .atom _ => 0
  | _, .new _ _ => 0
  | _, .app _ _ _ => 0
  | _, .let t u => t.nAdm + u.nAdm + 1
  | _, .cast t _ => t.nAdm + 1

/-- The machine's instantiation keeps the administrative measure. -/
theorem Tm.nAdm_inst {σ : Sig} : {s1 s2 : Sig} → (t : Tm σ s1) → (ι : Inst s1 s2) →
    (y : BVar σ .var) → (t.inst ι y).nAdm = t.nAdm
  | _, _, .atom _, _, _ => rfl
  | _, _, .new _ _, _, _ => rfl
  | _, _, .app _ _ _, _, _ => rfl
  | _, _, .let t u, ι, y => by
      show (t.inst ι y).nAdm + (u.inst ι.lift y).nAdm + 1 = _
      rw [Tm.nAdm_inst t ι y, Tm.nAdm_inst u ι.lift y]
      rfl
  | _, _, .cast t _, ι, y => by
      show (t.inst ι y).nAdm + 1 = _
      rw [Tm.nAdm_inst t ι y]
      rfl

/-- The administrative measure of a continuation: one per frame, plus a
`let` frame's body. -/
def Cont.nAdm {σ : Sig} : Cont σ → Nat
  | .nil => 0
  | .cons K (.let u) => K.nAdm + u.nAdm + 1
  | .cons K (.cast _) => K.nAdm + 1

/-- **A focused state**: final, about to allocate, or about to invoke — the
states at which the machine's next step, if any, is visible to the source. -/
def State.Focused {σ : Sig} (st : State σ) : Prop :=
  st.Final ∨ (∃ T ds, st.t = .new T ds) ∨ (∃ a l b, st.t = .app a l b)

/-- **Administrative normalisation**: every state reaches a focused state by
steps that allocate nothing and keep every relation it satisfies.  By
well-founded recursion on the lexicographic pair (measure of state, measure of
running term). -/
theorem normalize {σ : Sig} (Gt : MachineStore σ σ) : (K : Cont σ) → (d : Tm σ []) →
    ∃ st' : State σ, Steps .refl ⟨Gt, K, d⟩ st' ∧ st'.Focused ∧
      ∀ (G : Store σ σ) (t : Oopsla16.Tm σ []), Rel G t ⟨Gt, K, d⟩ → Rel G t st'
  | .nil, .atom a => ⟨_, .refl, Or.inl ⟨rfl, a, rfl⟩, fun _ _ h => h⟩
  | .cons K (.let u), .atom a =>
      have ⟨st', h1, h2, h3⟩ := normalize Gt K (u.inst .base (Vr.loc a.root))
      ⟨st', Steps.trans (Steps.single Step.rename) h1, h2, fun G t h => h3 G t h.rename⟩
  | .cons K (.cast e), .atom a =>
      have ⟨st', h1, h2, h3⟩ := normalize Gt K (.atom (.cast a e))
      ⟨st', Steps.trans (Steps.single Step.castAtom) h1, h2, fun G t h => h3 G t h.castAtom⟩
  | _, .new T ds => ⟨_, .refl, Or.inr (Or.inl ⟨T, ds, rfl⟩), fun _ _ h => h⟩
  | _, .app a l b => ⟨_, .refl, Or.inr (Or.inr ⟨a, l, b, rfl⟩), fun _ _ h => h⟩
  | K, .let d u =>
      have ⟨st', h1, h2, h3⟩ := normalize Gt (K ▹ .let u) d
      ⟨st', Steps.trans (Steps.single Step.let) h1, h2, fun G t h => h3 G t h.let_⟩
  | K, .cast d e =>
      have ⟨st', h1, h2, h3⟩ := normalize Gt (K ▹ .cast e) d
      ⟨st', Steps.trans (Steps.single Step.castPush) h1, h2, fun G t h => h3 G t h.castPush⟩
termination_by K d => (K.nAdm + d.nAdm, d.nAdm)
decreasing_by
  all_goals
    rw [Prod.lex_def]
    simp only [Cont.nAdm, Tm.nAdm, Tm.nAdm_inst]
    first
      | exact Or.inl (by omega)
      | exact Or.inr ⟨by omega, by omega⟩

/-- **Answers correspond**: a state related to a source answer reaches a final
state administratively. -/
theorem Rel.answer_final {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) (ha : t.IsAnswer) :
    ∃ st' : State σ, Steps .refl st st' ∧ st'.Final ∧ Rel G t st' := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨⟨Gt1, K1, d1⟩, h1, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G t h
  rcases hfoc with hfin | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact ⟨_, h1, hfin, hr⟩
  · simp only at hd
    subst hd
    obtain ⟨_, _, hs⟩ := Rel.new_steps hr
    exact absurd hs (answer_not_step ha)
  · simp only at hd
    subst hd
    obtain ⟨C, r0, -, ht, hr0⟩ := hr.decompose
    have hr0' : r0 = .tapp (.tvar a.root) l (.tvar b.root) := hr0
    subst ht hr0'
    exact absurd ha (ECtx.plug_not_answer C (fun p h => by cases h))

/-- **`SimStepSpec` holds**: normalise, then match the source's step at the
focus.  No hypothesis. -/
theorem sim_step : SimStepSpec := by
  intro σ1 σ2 g G t G' t' st h hs
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨⟨Gt1, K1, d1⟩, h1, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G t h
  rcases hfoc with hfin | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact absurd hs (answer_not_step (hr.final hfin))
  · simp only at hd
    subst hd
    obtain ⟨st2, h2, hr2⟩ := Rel.sim_new hr hs
    refine ⟨st2, ?_, hr2⟩
    have hc := Steps.tail h1 h2
    rwa [growsReflComp] at hc
  · simp only at hd
    subst hd
    obtain ⟨st2, h2, hr2⟩ := Rel.sim_app hr hs
    refine ⟨st2, ?_, hr2⟩
    have hc := Steps.tail h1 h2
    rwa [growsReflComp] at hc

/-- **`SimStuckSpec` holds**: normalise; a final state would make the source
an answer, an allocation or a defined invocation would make it step, so the
focus is an invocation of an undefined label, which is stuck.  No
hypothesis. -/
theorem sim_stuck : SimStuckSpec := by
  intro σ G t st h hst
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨⟨Gt1, K1, d1⟩, h1, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G t h
  rcases hfoc with hfin | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact absurd (hr.final hfin) hst.1
  · simp only at hd
    subst hd
    obtain ⟨G', t', hs⟩ := Rel.new_steps hr
    exact absurd ⟨_, _, G', t', hs⟩ hst.2
  · simp only at hd
    subst hd
    cases hf : (Gt1.lookup (Vr.loc a.root)).fun? l with
    | none => exact ⟨_, _, _, h1, State.stuck_app hf⟩
    | some p =>
        obtain ⟨S, U, body⟩ := p
        obtain ⟨t', hs⟩ := Rel.app_steps hr hf
        exact absurd ⟨_, _, G, t', hs⟩ hst.2

/-- **`SimSpec` holds**, with no hypothesis. -/
theorem sim_spec : SimSpec := ⟨sim_step, sim_stuck⟩

/-- **Type safety of `Oopsla16`'s machine, from the elaboration**: no
configuration reachable from a closed term typed over the empty store is
stuck.

**Stated with a hypothesis:** `hE : ElabSpec`, the elaboration of general
source typings into related typed target terms, which this module does not
prove (Track ELAB).  `ElaborationFull.elabSpec` inhabits it, and
`ElaborationFull.oopsla16_safety'` and `SourceSafety`'s
`Oopsla16.oopsla16_safety` are this theorem without the hypothesis.  On the
fragment `TmFrag` it is also `elabSpec_frag`, and `oopsla16_safety_frag` is
this theorem there.  `SimSpec` is not a hypothesis: `sim_spec` proves it. -/
theorem oopsla16_safety (hE : ElabSpec) {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) {σ : Sig} {g : Grows [] σ} {G' : Store σ σ}
    {t' : Oopsla16.Tm σ []} (run : Oopsla16.Steps g Store.nil t G' t') : ¬ SrcStuck G' t' :=
  transport hE sim_spec ht run

/-! ## The elaborable fragment -/

mutual

/-- **The fragment elaboration corresponds to its source**, at every store
typing: an elaborated atom is rooted at the source's variable, and the
elaboration introduces no `let`. -/
theorem elabHasType_corr {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} :
    {t : Oopsla16.Tm σ s} → {T : Ty σ s} → (h : HasType G Γ t T) → (f : TmFrag t) →
    Corr t (elabHasType W h f).1
  | _, _, .T_Vary hds heq, _ => by
      simp only [elabHasType]
      exact (elabAtom_erase W (.T_Vary hds heq)).symm
  | _, _, .T_Varz, _ => by simp only [elabHasType]; rfl
  | _, _, .T_VarPack h, _ => by
      simp only [elabHasType]
      exact (elabAtom_erase W (.T_VarPack h)).symm
  | _, _, .T_VarUnpack h, _ => by
      simp only [elabHasType]
      exact (elabAtom_erase W (.T_VarUnpack h)).symm
  | _, _, .T_Obj (T := T) hds, .tobj f => by
      simp only [elabHasType]
      exact Corr.obj T (elabDms_corr W hds f)
  | _, _, .T_App h1 h2, .tapp => by
      simp only [elabHasType]
      exact Corr.app_of_root _ (elabAtom W h1).root (elabAtom W h2).root
  | _, _, .T_AppVar h1 h2, .tapp => by
      simp only [elabHasType]
      exact Corr.app_of_root _ (elabAtom W h1).root (elabAtom W h2).root
  | _, _, .T_Sub h hs, f => by
      simp only [elabHasType]
      exact elabHasType_corr W h f

/-- The same, at a definition list; the annotations play no part. -/
theorem elabDms_corr {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → (h : DmsHasType G Γ ds T) → (f : DmsFrag ds) →
    DmsCorr ds (elabDms W h f).defs
  | _, _, .D_Nil, _ => by simp only [elabDms]; rfl
  | _, _, .D_Typ (T11 := T11) hds, .dcons _ f => by
      simp only [elabDms]
      exact DmsCorr.dty T11 (elabDms_corr W hds f)
  | _, _, .D_Fun (T11 := T11) (T12 := T12) hds hb _ _, .dcons (.dfun fb) f => by
      simp only [elabDms]
      exact DmsCorr.dfun _ _ T11 T12 (elabHasType_corr W hb fb) (elabDms_corr W hds f)

end

/-- **`ElabSpec` on the fragment `TmFrag`**, by `Elaboration.elabHasType`. -/
theorem elabSpec_frag {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) (ft : TmFrag t) :
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧
        Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩ :=
  ⟨emptyStoreTy, (elabHasType emptyStoreTy ht ft).1, T,
    ⟨(elabHasType emptyStoreTy ht ft).2⟩, Rel.init (elabHasType_corr emptyStoreTy ht ft)⟩

/-- **Type safety of `Oopsla16`'s machine on the fragment, with no
hypothesis**: a closed term typed over the empty store, all of whose
applications (method bodies included) have variable operands and all of whose
methods are fully annotated, never reaches a stuck configuration. -/
theorem oopsla16_safety_frag {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) (ft : TmFrag t) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (run : Oopsla16.Steps g Store.nil t G' t') :
    ¬ SrcStuck G' t' := by
  obtain ⟨W, d, T', ⟨hd⟩, hc⟩ := elabSpec_frag ht ft
  exact transport_from sim_spec hd hc run

/-! ## The literal stuck reflection is false

One location holding no member; the source invokes it on itself, which is
stuck; the related target state binds the receiver first, and can push that
`let`. -/

namespace LiteralReflection

/-- One location. -/
abbrev σ1 : Sig := ([],x)

/-- The source store: the location holds no member. -/
abbrev G : Store σ1 σ1 := .cons .nil .dnil

/-- The machine store: the same. -/
abbrev Gt : MachineStore σ1 σ1 := .cons .nil .dnil

/-- The source term: invoke label `0` on the location, with itself. -/
abbrev t : Oopsla16.Tm σ1 [] := .tapp (.tvar (.conc .here)) 0 (.tvar (.conc .here))

/-- The target state: the receiver `let`-bound, then the invocation. -/
abbrev st : State σ1 :=
  ⟨Gt, .nil, .let (.atom (.var (.conc .here))) (.app (.var (.abs .here)) 0 (.var (.conc .here)))⟩

/-- The two are related. -/
theorem rel : Rel G t st :=
  ⟨fun l => match l with | .here => rfl,
    Corr.let_ (.app1 .hole 0 (.tvar (.conc .here)))
      (Corr.var (σ := σ1) (s := []) (.var (.conc .here)))
      (Corr.app (σ := σ1) (s := ([],x)) (.var (.abs .here)) 0 (.var (.conc .here)))⟩

/-- The target state can step: it pushes the `let`. -/
theorem target_steps : st.CanStep := ⟨_, _, _, Step.let⟩

/-- The source configuration cannot. -/
theorem source_stuck :
    ¬ ∃ (σ' : Sig) (g : Grows σ1 σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
      Oopsla16.Step g G t G' t' := by
  rintro ⟨σ', g, G', t', hs⟩
  cases hs with
  | ST_AppAbs hl => cases hl
  | ST_App1 h => exact tvar_not_step h
  | ST_App2 h => exact tvar_not_step h

/-- **"A related target state that can step has a source that can step" is
false.** -/
theorem literal_reflection_false :
    ¬ ∀ {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ},
        Rel G t st → st.CanStep →
          ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
            Oopsla16.Step g G t G' t' :=
  fun H => source_stuck (H rel target_steps)

end LiteralReflection

end FCdotR
