import Coercions.Classifiers.FCdot.Consistency

namespace Classifiers

/-!
# Capture prediction (stage A2.5)

The use-set half of preservation, and what follows from it along a run.

A term's use set is computed by `Tm.uses`, a total structural function, and a
state's use set unites it with the sets the let frames of the continuation
declare.  Typing discharges a body's use set against the declared set with
explicit capture evidence, and `cap_canon` reads that evidence as
subcapturing.  So one step never grows the roots of a state's use set:

* `step_uses`: one step, with the store extension it performs.
* `capture_prediction`: the same along a run, the extensions composed.
* `inspects_covered`: the root a state reads is in its use set.
* `effect_safety`: a run of a state whose use set has no root `κ` never reads
  a root with root `κ`.
* `returned_capture_bound`: an answer's annotation, and the root of a
  returned atom, are bounded by the capture set of the answer's type.

Nothing here is in a type, so no form, entry, or slot of the normalizer is
involved.  Every case of `step_uses` is either an inclusion of syntactic sets
or one application of `cap_canon` to evidence that the typing rule of the
redex provides.
-/

namespace FCdot

/-- Membership in a union of capture sets. -/
theorem CaptureSet.mem_union {s : Sig} {a : CapAtom s} {C D : CaptureSet s} :
    a ∈ C ∪ D ↔ a ∈ C ∨ a ∈ D := List.mem_append

/-- Membership in a union of use sets, up to the order of the union.  Every
inclusion of syntactic sets in `step_uses` is discharged with this. -/
local macro "mem_uses" : tactic =>
  `(tactic| (intro c hc;
             try simp only [Tm.uses_atom, Tm.uses_val, Tm.uses_app, Tm.uses_proj,
               Tm.uses_let, Tm.uses_cast, Tm.uses_castE, Tm.uses_letex,
               Tm.uses_unbox, usesK_nil, usesK_let,
               usesK_cast, usesK_castE, usesK_letex, PAtom.root_applyE,
               PAtom.root_plain, Atom.root, CaptureSet.weaken, CaptureSet.rename_union,
               CaptureSet.rename_nil, CaptureSet.mem_union, List.mem_cons,
               List.not_mem_nil, or_false, false_or] at hc ⊢;
             first
               | exact hc
               | simp [hc]
               | (rcases hc with hc | hc <;> simp [hc])
               | (rcases hc with hc | hc | hc <;> simp [hc])
               | (rcases hc with hc | hc | hc | hc <;> simp [hc])))

/-! ## Small facts about `CapLe` and annotations -/

/-- Subcapturing from a membership inclusion. -/
theorem CapLe.mem {s : Sig} {Γ : Ctx s} {C D : CaptureSet s}
    (h : ∀ a : CapAtom s, a ∈ C → a ∈ D) : CapLe Γ C D := CapLe.of_subset h

/-- The closing set of a lambda body or of a field, instantiated at the
argument or at the object's variable. -/
theorem CaptureSet.closing_substVar {s : Sig} (A : CaptureSet s) (y : BVar s .var) :
    (((A↑ : CaptureSet (s,x)) ∪ [CapAtom.var .here]))⟦y⟧ = A ∪ [CapAtom.var y] := by
  show CaptureSet.rename _ _ = _
  rw [CaptureSet.rename_union]
  rw [show CaptureSet.rename (A↑) (Rename.subst y) = A from
        CaptureSet.rename_subst_weaken A y]
  rfl

/-- The closing set of a body, read at the argument: the substitution a step
performs when it enters a closure's body cancels the three weakenings and
sends the parameter to the argument's root.  This is
`CaptureSet.closing_substVar` in the representation of the stage. -/
theorem CaptureSet.closing_subst_enter {s : Sig} (A : CaptureSet s) (b : Atom s) :
    ((A↑↑↑ : CaptureSet (Sig.body s)) ∪ [CapAtom.var .here]).subst (Subst.enter b)
      = A ∪ [CapAtom.var b.root] := by
  rw [CaptureSet.subst_union, CaptureSet.weaken3_subst_enter]
  rfl

/-- A value's annotation survives the stripping of its casts. -/
@[simp] theorem Value.core_annot {s : Sig} : ∀ v : Value s, v.core.annot = v.annot
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .pack _ _ _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.core_annot v]

/-- A variable has exactly the roots of the annotation of the value stored at
it.  This is `Ctx.Root_var` composed with `Store.Typed.lookup_annot`, and it
is what turns a use of a variable into a use of the capture set the stored
value announces. -/
theorem Store.Typed.root_annot {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    (x : BVar s .var) : RootsEq Γ [CapAtom.var x] (σ.lookup x).annot := by
  have h := Ctx.Root_var Γ x
  rwa [hσ.lookup_annot x] at h

/-! ## The use set of a step's result -/

/-- The body of a stored closure, instantiated at the argument: its use set
lies below the closure's variable united with the argument's root.  The
closure's closing evidence `g` is substituted by the argument, and the
closure's annotation is the capture set of its variable. -/
theorem Store.Typed.app_uses {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ S : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    {T : Cod s} {C : CaptureSet s} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g)
    (hty : Γ.lookupTy x = (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root))) :
    CapLe Γ (t₀.subst (Subst.enter b)).uses ([CapAtom.var x] ∪ [CapAtom.var b.root]) := by
  obtain ⟨T₀, hlk, ht₀, hg⟩ := hσ.lam_closing hx
  rw [hty] at hlk
  obtain ⟨hC, hpi⟩ := Ty.capt.inj hlk
  obtain ⟨rfl, -⟩ := Shape.pi.inj hpi
  have hsub := hg.subst (Subst.Typed.enter hσ.rootFree hb)
  rw [CaptureSet.closing_subst_enter, ← Tm.uses_subst] at hsub
  have hA : RootsEq Γ [CapAtom.var x] A := by
    rw [show A = (σ.lookup x).annot by rw [hx]; rfl]
    exact hσ.root_annot x
  exact (cap_canon hσ hsub).trans
    (CapLe.union (hA.symm.le.trans (CapLe.mem (by simp))) (CapLe.mem (by simp)))

/-- The field of a stored literal, read at the object's variable: its use set
lies below that variable.  The field's closing evidence is renamed by
`Rename.subst`, and the literal's annotation is the capture set of its
variable. -/
theorem Store.Typed.proj_uses {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)}
    {F : Fields ((s,c),x)} {ℓ : Label} {t : Tm ((s,c),x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    CapLe Γ (t.subst (Subst.enterObj y)).uses [CapAtom.var y] := by
  obtain ⟨-, -, g', hg'⟩ := Tm.HasType.projFieldFull hσ hx hg
  have hA : RootsEq Γ [CapAtom.var y] A := by
    rw [show A = (σ.lookup y).annot by rw [hx]; rfl]
    exact hσ.root_annot y
  exact (cap_canon hσ hg').trans (CapLe.union hA.symm.le (CapLe.refl _ _))

/-! ## The unpack and the binder it opens -/

/-- The charge a `letex` body declares, instantiated at the atom the unpack
substitutes: the declared set loses one of its two weakenings, and the opened
binder comes back to the innermost position. -/
theorem CaptureSet.letexCharge_substVar {s : Sig} (U' : CaptureSet s) (y : BVar (s,c) .var) :
    CaptureSet.substVar
        ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.cvar (BVar.there BVar.here)]) y
      = CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here] := by
  show CaptureSet.rename _ _ = _
  rw [CaptureSet.rename_union,
    show CaptureSet.rename
        (CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        (Rename.subst y) = CaptureSet.weaken (k := .cap) U' from
      CaptureSet.rename_subst_weaken _ y]
  rfl

/-- **The declared bound, consumed.**  The binder the unpack opens is an
instance of the witness set, the wrapper puts that set below the declared
bound, and the frame puts the declared bound below the use set the body
declares.  So the opened binder brings no root the state did not have.  The
statement produces evidence rather than subcapturing, so that a caller may
weaken it into the store's next context. -/
theorem CapCo.HasType.instHere {s : Sig} {Γ : Ctx s} {C C₀ U' : CaptureSet s}
    {h₀ h : CapCo s} (hb : Γ ⊢ᶜ h₀ : C ⊑ C₀) (hh : Γ ⊢ᶜ h : C₀ ⊑ U') :
    ∃ f' : CapCo (s,c), (Γ.consC (.inst C)) ⊢ᶜ f'
      : [CapAtom.cvar BVar.here] ⊑ CaptureSet.weaken (k := .cap) U' :=
  ⟨_, (CapCo.HasType.eqToLe (CapEq.HasType.instC (a := CapAtom.cvar BVar.here)
      (C := CaptureSet.weaken (k := .cap) C) rfl)).trans
    ((hb.weakenC (.inst C) rfl).trans (hh.weakenC (.inst C) rfl))⟩

/-! ## One step -/

/-- The use set of a state that steps without extending the store. -/
theorem step_uses_same {s : Sig} {σ : Store s} {Γ : Ctx s} {K K' : Cont s} {t t' : Tm s}
    (hσ : ⊢ σ : Γ) (h : CapLe Γ (t'.uses ∪ usesK K') (t.uses ∪ usesK K)) :
    ∃ ρ : Rename s s, Store.Ext σ σ ρ ∧
      ∀ Γ' : Ctx s, ⊢ σ : Γ' →
        CapLe Γ' (State.uses ⟨σ, K', t'⟩) ((State.uses ⟨σ, K, t⟩).rename ρ) := by
  refine ⟨Rename.id, .refl, fun Γ' hσ' => ?_⟩
  obtain rfl := Store.Typed.ctx_unique hσ' hσ
  simpa using h

/-- `unpackAtom`: the use set of the state after the unpack.  The body's
avoidance evidence, transported to the store's `.inst C` context and
instantiated at the wrapper's atom, bounds the body's use set by the declared
set together with the opened binder, and `CapCo.HasType.instHere` puts the
opened binder below the declared set. -/
theorem step_uses_unpackAtom {s : Sig} {sigma : Store s} {Gamma : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {f : CapCo ((s,c),x)}
    {C C0 : CaptureSet s} {h0 h : CapCo s} {e : LeCo (Sig.scope s)} {a : Atom s}
    {S : Ty s} {T : Dom s}
    (hsig : Store.Typed sigma Gamma)
    (ha : Gamma ⊢ₐ a : S) (hb : Gamma ⊢ᶜ h0 : C ⊑ C0)
    (he : Gamma.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S))
      ≤ T.underRoot)
    (hh : Gamma ⊢ᶜ h : C0 ⊑ U')
    (hf : ((Gamma.consC .star).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)])) :
    ∃ rho : Rename s (s,c),
      Store.Ext sigma (sigma.consC (.inst C)) rho ∧
      ∀ Gamma' : Ctx (s,c), Store.Typed (sigma.consC (.inst C)) Gamma' →
        CapLe Gamma' (State.uses ⟨sigma.consC (.inst C), K.weakenC,
            u.substAtom (.cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot))⟩)
          ((State.uses ⟨sigma, K ▹ .letex u U' h f, .atom (.pack C h0 e a)⟩).rename rho) := by
  refine ⟨Rename.succ,
    by rw [← Rename.id_comp (Rename.succ (k := .cap))]; exact .consC .refl _ rfl,
    fun Gamma' hsig' => ?_⟩
  obtain rfl := Store.Typed.ctx_unique hsig' (hsig.consC rfl)
  obtain ⟨f', hf'⟩ := CapCo.HasType.instHere hb hh
  have hpay := Atom.HasType.unpackPayload hsig.rootFree ha he
  have hbody := CapCo.HasType.substAtom
    (CapCo.HasType.letexCharge_instC (C := C) hf) hpay
  rw [CaptureSet.letexCharge_substVar, ← Tm.uses_substAtom] at hbody
  have hle := cap_canon hsig' hbody
  simp only [State.uses_mk, Tm.uses_atom, PAtom.root_pack, usesK_letex, usesK_weakenC,
    CaptureSet.rename_union]
  have hU : CapLe (Gamma.consC (.inst C)) (CaptureSet.weaken (k := .cap) U')
      (CaptureSet.rename [CapAtom.var a.root] Rename.succ ∪
        (CaptureSet.weaken (k := .cap) (usesK K) ∪ CaptureSet.rename U' Rename.succ)) :=
    CapLe.mem (fun c hc =>
      CaptureSet.mem_union.mpr (Or.inr (CaptureSet.mem_union.mpr (Or.inr hc))))
  refine CapLe.union (hle.trans (CapLe.union hU ((cap_canon hsig' hf').trans hU)))
    (CapLe.mem (fun c hc =>
      CaptureSet.mem_union.mpr (Or.inr (CaptureSet.mem_union.mpr (Or.inl hc)))))

/-- `unpackVal`: the same, with the allocation machinery `CapCo.HasType.adjust`
already packages.  The evidence is weakened once more, past the binder the
literal is stored at. -/
theorem step_uses_unpackVal {s : Sig} {sigma : Store s} {Gamma : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {f : CapCo ((s,c),x)}
    {C C0 : CaptureSet s} {h0 h : CapCo s} {e : LeCo (Sig.scope s)} {v : Value s}
    {S : Ty s} {T : Dom s} {w : Value (s,c)}
    (hw : w = Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot))
    (hsig : Store.Typed sigma Gamma)
    (hv0 : Gamma ⊢ᵥ v : S) (hb : Gamma ⊢ᶜ h0 : C ⊑ C0)
    (he : Gamma.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S))
      ≤ T.underRoot)
    (hh : Gamma ⊢ᶜ h : C0 ⊑ U')
    (hf : ((Gamma.consC .star).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)])) :
    ∃ rho : Rename s ((s,c),x),
      Store.Ext sigma ((sigma.consC (.inst C)).cons w.core) rho ∧
      ∀ Gamma' : Ctx ((s,c),x),
        Store.Typed ((sigma.consC (.inst C)).cons w.core) Gamma' →
        CapLe Gamma' (State.uses ⟨(sigma.consC (.inst C)).cons w.core,
            (K.weakenC).weaken, u.adjust w⟩)
          ((State.uses ⟨sigma, K ▹ .letex u U' h f, .val (.pack C h0 e v)⟩).rename rho) := by
  have hwt : (Gamma.consC (.inst C)) ⊢ᵥ w : T := by
    rw [hw]; exact Value.HasType.unpackPayload hsig.rootFree hv0 he
  obtain ⟨f', hf'⟩ := CapCo.HasType.instHere hb hh
  refine ⟨(Rename.succ (k := .cap)).comp (Rename.succ (k := .var)),
    by rw [← Rename.id_comp (Rename.succ (k := .cap))]
       exact (Store.Ext.consC .refl _ rfl).cons _,
    fun Gamma' hsig' => ?_⟩
  obtain ⟨S0, hcore, hlit, hd⟩ := Value.HasType.coreDecomp w T hwt
  obtain rfl := Store.Typed.ctx_unique hsig' (Store.Typed.cons (hsig.consC rfl) hlit hcore)
  have hfc : ((Gamma.consC (.inst C)).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ CaptureSet.weaken (k := .var)
        (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here]) := by
    have h2 := CapCo.HasType.letexCharge_instC (C := C) hf
    rwa [show CaptureSet.weaken (k := .var)
          (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here])
        = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
            ∪ [CapAtom.cvar (.there .here)]) from CaptureSet.rename_union _ _ _]
  have hle : CapLe ((Gamma.consC (.inst C)).cons (.transparent S0 w.core.witnesses
        w.core.capWitnesses w.core.fieldLabels))
      (u.adjust w).uses (CaptureSet.weaken (k := .var)
      (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here])) := by
    rcases hd with ⟨hn, rfl⟩ | ⟨E, hE?, hE⟩
    · exact cap_canon hsig' (CapCo.HasType.adjust_none hn hfc)
    · exact cap_canon hsig' (CapCo.HasType.adjust hE? hE hfc)
  have hf2 := cap_canon hsig' (CapCo.HasType.weaken hf'
    (Binding.transparent S0 w.core.witnesses w.core.capWitnesses w.core.fieldLabels))
  have hLeq : State.uses ⟨(sigma.consC (.inst C)).cons w.core,
        (K.weakenC).weaken, u.adjust w⟩
      = (u.adjust w).uses
        ∪ CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) (usesK K)) := by
    simp only [State.uses_mk, usesK_weaken, usesK_weakenC]
  have hReq : (State.uses ⟨sigma, K ▹ .letex u U' h f, .val (.pack C h0 e v)⟩).rename
        ((Rename.succ (k := .cap)).comp (Rename.succ (k := .var)))
      = CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) (usesK K))
        ∪ CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U') := by
    simp only [State.uses_mk, Tm.uses_val, usesK_letex, CaptureSet.weaken,
      CaptureSet.rename_union, CaptureSet.rename_comp, CaptureSet.rename_nil]
    rfl
  have hCharge : CaptureSet.weaken (k := .var)
        (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here])
      = CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U')
        ∪ CaptureSet.weaken (k := .var) [CapAtom.cvar (BVar.here (k := .cap))] :=
    CaptureSet.rename_union _ _ _
  rw [hLeq, hReq]
  rw [hCharge] at hle
  have hU : CapLe ((Gamma.consC (.inst C)).cons (.transparent S0 w.core.witnesses
        w.core.capWitnesses w.core.fieldLabels))
      (CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
      (CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) (usesK K))
        ∪ CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U')) :=
    CapLe.mem (fun c hc => CaptureSet.mem_union.mpr (Or.inr hc))
  exact CapLe.union (hle.trans (CapLe.union hU (hf2.trans hU)))
    (CapLe.mem (fun c hc => CaptureSet.mem_union.mpr (Or.inl hc)))

/-- **The use-set half of preservation.**  One step of a typed state embeds
the old store into the new one, and the roots of the use set do not grow
along that embedding. -/
theorem step_uses {s s' : Sig} {st : State s} {st' : State s'} {Γ : Ctx s} {U : Ty s}
    (hσ : ⊢ st.σ : Γ) (hT : State.Typed st U) (step : st ⟶ st') :
    ∃ ρ : Rename s s', Store.Ext st.σ st'.σ ρ ∧
      ∀ Γ' : Ctx s', ⊢ st'.σ : Γ' → CapLe Γ' st'.uses ((st.uses).rename ρ) := by
  cases step <;> obtain ⟨Γ₀, T, hσ₀, ht, hK⟩ := hT <;>
    obtain rfl := Store.Typed.ctx_unique hσ hσ₀
  -- The four cases in which the two use sets are equal as sets.
  case «let» =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case castPush =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case castVal =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case castAtom =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  -- The answer-cast steps and the `letex` push: the two use sets are equal as
  -- sets, because an answer cast charges nothing of its own and `applyE`
  -- moves no root (`PAtom.root_applyE`).
  case castEPush =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case castEVal =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case castEAtom =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  case letex =>
      exact step_uses_same hσ (CapLe.mem (by mem_uses))
  -- The two unpacks: the store gains the witness as an instance binder, and
  -- the binder it opens is charged to the set the frame declares.
  case unpackAtom =>
      cases ht with
      | atom hp =>
        cases hK with
        | letex hh hu hf hK' =>
          cases hp with
          | pack ha hb he => exact step_uses_unpackAtom hσ ha hb he hh hf
  case unpackVal =>
      cases ht with
      | val hv =>
        cases hK with
        | letex hh hu hf hK' =>
          cases hv with
          | pack hv0 hb he => exact step_uses_unpackVal rfl hσ hv0 hb he hh hf
  -- Allocation: the let's avoidance evidence, transported into the
  -- transparent context of the freshly stored literal by the substitution
  -- `Tm.adjust` applies to the body.
  case alloc =>
      rename_i σ K u U' f v
      cases ht with
      | val hv =>
          cases hK with
          | «let» hu hf hK' =>
              obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v _ hv.ty_inv
              refine ⟨Rename.succ, by rw [← Rename.id_comp Rename.succ]; exact .cons .refl _,
                fun Γ' hσ' => ?_⟩
              obtain rfl := Store.Typed.ctx_unique hσ' (Store.Typed.cons hσ hlit hcore)
              have hle : CapLe (Γ.cons (.transparent S₀ v.core.witnesses v.core.capWitnesses
                  v.core.fieldLabels)) (u.adjust v).uses (U'↑) := by
                rcases hd with ⟨hn, rfl⟩ | ⟨E, hE?, hE⟩
                · exact cap_canon hσ' (CapCo.HasType.adjust_none (W := v.core.witnesses)
                    (Wc := v.core.capWitnesses) (Fs := v.core.fieldLabels) hn hf)
                · exact cap_canon hσ' (CapCo.HasType.adjust (W := v.core.witnesses)
                    (Wc := v.core.capWitnesses) (Fs := v.core.fieldLabels) hE? hE hf)
              simp only [State.uses_mk, Tm.uses_val, usesK_weaken, CaptureSet.rename_union]
              exact CapLe.union (hle.trans (CapLe.mem (by mem_uses))) (CapLe.mem (by mem_uses))
  -- Renaming: the let's avoidance evidence, instantiated at the atom.
  case rename =>
      cases ht with
      | atom hp =>
        cases hp with
        | plain ha =>
          cases hK with
          | «let» hu hf hK' =>
              refine step_uses_same hσ ?_
              have hle := cap_canon hσ (hf.letBody_substAtom ha)
              exact CapLe.union (hle.trans (CapLe.mem (by mem_uses)))
                (CapLe.mem (by mem_uses))
  -- The three application steps: the closure's closing evidence at the
  -- argument, and the closure's annotation read at its variable.
  case appVar =>
      rename_i hx
      cases ht with
      | app ha hb =>
          refine step_uses_same hσ ?_
          have hle := hσ.app_uses hx (Atom.HasType.var_inv ha).symm hb
          exact CapLe.union (hle.trans (CapLe.mem (by mem_uses)))
            (CapLe.mem (by mem_uses))
  case appCastRefl =>
      rename_i hx hne hcf hid
      cases ht with
      | app hA hb =>
          refine step_uses_same hσ ?_
          obtain ⟨C₀, hty⟩ := Ty.shape_eq_iff.mp (hσ.formsTyped.refl hA hcf hid)
          have hle := hσ.app_uses hx hty hb
          exact CapLe.union (hle.trans (CapLe.mem (by mem_uses)))
            (CapLe.mem (by mem_uses))
  case appCast =>
      rename_i hx hne hcf
      cases ht with
      | app hA hb =>
          refine step_uses_same hσ ?_
          obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv (hσ.lam_of_lookup hx)
          obtain ⟨hdom, hcod⟩ := hσ.formsTyped.pi hA hcf (by rw [hTe]; rfl)
          have hle := hσ.app_uses hx hTe (Atom.HasType.castDom hσ.rootFree hdom hb)
          simp only [Atom.root_cast] at hle
          simp only [Tm.uses_castE]
          exact CapLe.union (hle.trans (CapLe.mem (by mem_uses)))
            (CapLe.mem (by mem_uses))
  -- Projection: the field's closing evidence at the object's variable.
  case proj =>
      rename_i hx hg
      cases ht with
      | proj _ _ =>
          refine step_uses_same hσ ?_
          have hle := hσ.proj_uses hx hg
          exact CapLe.union (hle.trans (CapLe.mem (by mem_uses)))
            (CapLe.mem (by mem_uses))
  -- The two unbox steps: the boxed atom's root is below the boxed capture
  -- set, and that set is below the set the unboxing charges.
  case unboxRefl =>
      rename_i hx hcf hid
      cases ht with
      | unbox hA hf =>
          refine step_uses_same hσ ?_
          have hb := hσ.unboxRefl_result hσ.formsTyped hx hA hcf hid
          have h7 := (atom_canon hσ hb).capLe
          simp only [Ty.captureSet_capt] at h7
          refine CapLe.union ?_ (CapLe.mem (by mem_uses))
          exact (h7.trans (cap_canon hσ hf)).trans
            (CapLe.mem (by mem_uses))
  case unboxCast =>
      rename_i hx hcf
      cases ht with
      | unbox hA hf =>
          refine step_uses_same hσ ?_
          have hb := hσ.unboxCast_result hσ.formsTyped hx hA hcf
          have h7 := (atom_canon hσ hb).capLe
          simp only [Ty.captureSet_capt, Atom.root_cast] at h7
          refine CapLe.union ?_ (CapLe.mem (by mem_uses))
          exact (h7.trans (cap_canon hσ hf)).trans
            (CapLe.mem (by mem_uses))

/-! ## Along a run -/

/-- **Capture prediction.**  Along any run from a typed state the store only
grows, and the roots of the use set only shrink: every root of the use set at
the end is the image of a root of the use set at the start. -/
theorem capture_prediction {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (run : st ⟶* st') :
    ∃ ρ : Rename s s', Store.Ext st.σ st'.σ ρ ∧
      ∀ Γ' : Ctx s', ⊢ st'.σ : Γ' → CapLe Γ' st'.uses ((st.uses).rename ρ) := by
  induction run with
  | refl =>
      exact ⟨Rename.id, .refl, fun Γ' _ => by
        simp only [CaptureSet.rename_id]; exact CapLe.refl _ _⟩
  | tail run' step ih =>
      obtain ⟨ρ₁, hE₁, h₁⟩ := ih hT
      obtain ⟨U₁, hT₁⟩ := Steps.typed hT run'
      obtain ⟨Γ₁, T₁, hσ₁, ht₁, hK₁⟩ := hT₁
      obtain ⟨ρ₂, hE₂, h₂⟩ := step_uses hσ₁ ⟨Γ₁, T₁, hσ₁, ht₁, hK₁⟩ step
      refine ⟨ρ₁.comp ρ₂, hE₁.comp hE₂, fun Γ₂ hσ₂ => ?_⟩
      rw [← CaptureSet.rename_comp]
      exact (h₂ Γ₂ hσ₂).trans (hE₂.capLe hσ₁ hσ₂ (h₁ Γ₁ hσ₁))

/-- The root a state reads is covered by its use set. -/
theorem inspects_covered {s : Sig} {st : State s} {Γ : Ctx s} {x : BVar s .var}
    (h : st.inspects = some x) : CapLe Γ [CapAtom.var x] st.uses :=
  CapLe.mem (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact State.inspects_mem_uses h)

/-- **Effect safety.**  A run from a typed state whose use set has no root
`κ` never reaches a state that reads a root with root `κ`.  This is capture
prediction and `inspects_covered`, transported along the store extension by
the roots lemma. -/
theorem effect_safety {s s' : Sig} {st : State s} {st' : State s'} {Γ : Ctx s}
    {Γ' : Ctx s'} {U : Ty s} {κ : BVar s .cap} {x : BVar s' .var}
    (hT : State.Typed st U) (hσ : ⊢ st.σ : Γ) (run : st ⟶* st')
    (hκ : ¬ Γ.Root (CapAtom.cvar κ) st.uses)
    (hin : st'.inspects = some x) (hσ' : ⊢ st'.σ : Γ') :
    ∃ ρ : Rename s s', Store.Ext st.σ st'.σ ρ ∧
      ¬ Γ'.Root (CapAtom.cvar (ρ.var κ)) [CapAtom.var x] := by
  obtain ⟨ρ, hE, hpred⟩ := capture_prediction hT run
  refine ⟨ρ, hE, fun hr => hκ ?_⟩
  have h1 : Γ'.Root (CapAtom.cvar (ρ.var κ)) st'.uses :=
    inspects_covered hin _ hr
  have h2 : Γ'.Root (CapAtom.cvar (ρ.var κ)) ((st.uses).rename ρ) :=
    hpred Γ' hσ' _ h1
  exact (hE.root_iff hσ hσ' (CapAtom.cvar κ) st.uses).mp h2

/-- **Classified prediction.**  Along any run from a typed state whose use set
is kinded at `φ`, the use set stays kinded at `φ`.  This is
`capture_prediction` with the kinding carried to the new context by
`Store.Ext.kindLe` and pulled back along the predicted inclusion by
`Ctx.KindLe.mono`. -/
theorem classified_prediction {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    {Γ : Ctx s} {φ : Cls.Kind}
    (hT : State.Typed st U) (hσ : ⊢ st.σ : Γ) (hk : Γ.KindLe st.uses φ) (run : st ⟶* st') :
    ∃ ρ : Rename s s', Store.Ext st.σ st'.σ ρ ∧
      ∀ Γ' : Ctx s', ⊢ st'.σ : Γ' →
        CapLe Γ' st'.uses ((st.uses).rename ρ) ∧ Γ'.KindLe st'.uses φ := by
  obtain ⟨ρ, hE, hpred⟩ := capture_prediction hT run
  refine ⟨ρ, hE, fun Γ' hσ' => ⟨hpred Γ' hσ', ?_⟩⟩
  exact Ctx.KindLe.mono (hpred Γ' hσ') (hE.kindLe hσ hσ' hk)

/-- **Classified effect safety.**  A program whose use set is kinded at `φ`
never reads a capability whose classifier lies outside `φ`.  This is
`classified_prediction` and `inspects_covered`. -/
theorem classified_effect_safety {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    {Γ : Ctx s} {Γ' : Ctx s'} {φ : Cls.Kind} {x : BVar s' .var}
    (hT : State.Typed st U) (hσ : ⊢ st.σ : Γ) (hk : Γ.KindLe st.uses φ) (run : st ⟶* st')
    (hin : st'.inspects = some x) (hσ' : ⊢ st'.σ : Γ') :
    ∀ a : CapAtom s', Γ'.Root a [CapAtom.var x] → φ.Contains (Γ'.classOf a) := by
  obtain ⟨ρ, hE, hpred⟩ := classified_prediction hT hσ hk run
  exact Ctx.KindLe.mono (inspects_covered hin) (hpred Γ' hσ').2

/-! ## The capture set of an answer -/

/-- The value half of `returned_capture_bound`: the annotation of a returned
value is bounded by the capture set of the type it is returned at.  The value
may carry casts; its core is a literal typed at its own annotation, and the
composite of the casts is closed capture evidence. -/
theorem returned_capture_bound_val {s : Sig} {σ : Store s} {Γ : Ctx s} {v : Value s}
    {S : Shape s} {C : CaptureSet s}
    (hT : State.Typed ⟨σ, .nil, .val v⟩ (S ^ C)) (hσ : ⊢ σ : Γ) :
    CapLe Γ v.annot C := by
  obtain ⟨Γ₀, T, hσ₀, ht, hK⟩ := hT
  obtain rfl := Store.Typed.ctx_unique hσ hσ₀
  cases hK
  cases ht with
  | val hv =>
      obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v (S ^ C) hv.ty_inv
      have hann : S₀.captureSet = v.annot := by
        rw [Value.HasType.captureSet_annot hcore hlit, Value.core_annot]
      rcases hd with ⟨-, rfl⟩ | ⟨E, -, hE⟩
      · simp only [Ty.captureSet_capt] at hann
        rw [← hann]
        exact CapLe.refl _ _
      · have hle := le_canon_cap hσ hE
        rw [hann] at hle
        simpa using hle

/-- The atom half of `returned_capture_bound`: the root of a returned atom is
bounded by the capture set of the type it is returned at.  This is item 7 of
the canonical-forms theorem. -/
theorem returned_capture_bound_atom {s : Sig} {σ : Store s} {Γ : Ctx s} {a : Atom s}
    {S : Shape s} {C : CaptureSet s}
    (hT : State.Typed ⟨σ, .nil, .atom (.plain a)⟩ (S ^ C)) (hσ : ⊢ σ : Γ) :
    CapLe Γ [CapAtom.var a.root] C := by
  obtain ⟨Γ₀, T, hσ₀, ht, hK⟩ := hT
  obtain rfl := Store.Typed.ctx_unique hσ hσ₀
  cases hK
  cases ht with
  | atom hp => cases hp with | plain ha => simpa using (atom_canon hσ ha).capLe

/-- **The capture set of an answer**, in both halves: the annotation of a
returned value, and the root of a returned atom, are bounded by the capture
set of the answer's type. -/
theorem returned_capture_bound {s : Sig} {σ : Store s} {Γ : Ctx s} {S : Shape s}
    {C : CaptureSet s} (hσ : ⊢ σ : Γ) :
    (∀ v : Value s, State.Typed ⟨σ, .nil, .val v⟩ (S ^ C) → CapLe Γ v.annot C) ∧
      (∀ a : Atom s, State.Typed ⟨σ, .nil, .atom (.plain a)⟩ (S ^ C) →
        CapLe Γ [CapAtom.var a.root] C) :=
  ⟨fun _ hT => returned_capture_bound_val hT hσ,
    fun _ hT => returned_capture_bound_atom hT hσ⟩

end FCdot

end Classifiers
