import Coercions.Captures.FCdot.Consistency

namespace Captures

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
               Tm.uses_let, Tm.uses_cast, Tm.uses_unbox, usesK_nil, usesK_let,
               usesK_cast, Atom.root, CaptureSet.weaken, CaptureSet.rename_union,
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

/-- A value's annotation survives the stripping of its casts. -/
@[simp] theorem Value.core_annot {s : Sig} : ∀ v : Value s, v.core.annot = v.annot
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
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
    {A : CaptureSet s} {S₀ S : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)} {T : Ty (s,x)}
    {C : CaptureSet s} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g)
    (hty : Γ.lookupTy x = (Π(S) T) ^ C) (hb : Γ ⊢ₐ b : S) :
    CapLe Γ (t₀.substAtom b).uses ([CapAtom.var x] ∪ [CapAtom.var b.root]) := by
  obtain ⟨T₀, hlk, ht₀, hg⟩ := hσ.lam_closing hx
  rw [hty] at hlk
  obtain ⟨hC, hpi⟩ := Ty.capt.inj hlk
  obtain ⟨rfl, -⟩ := Shape.pi.inj hpi
  have hsub := hg.substAtom hb
  rw [CaptureSet.closing_substVar, ← Tm.uses_substAtom] at hsub
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
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields (s,x)}
    {ℓ : Label} {t : Tm (s,x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    CapLe Γ (t.selfAt y).uses [CapAtom.var y] := by
  obtain ⟨-, -, g', hg'⟩ := Tm.HasType.projFieldFull hσ hx hg
  have hA : RootsEq Γ [CapAtom.var y] A := by
    rw [show A = (σ.lookup y).annot by rw [hx]; rfl]
    exact hσ.root_annot y
  exact (cap_canon hσ hg').trans (CapLe.union hA.symm.le (CapLe.refl _ _))

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
  -- Allocation: the let's avoidance evidence, transported into the
  -- transparent context of the freshly stored literal by the substitution
  -- `Tm.adjust` applies to the body.
  case alloc =>
      rename_i σ K u U' f v
      cases ht with
      | val hv =>
          cases hK with
          | «let» hu hf hK' =>
              obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v T hv
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
      | atom ha =>
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
          have hle := hσ.app_uses hx hTe (hb.cast hdom)
          simp only [Atom.root_cast] at hle
          simp only [Tm.uses_cast]
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
      obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v (S ^ C) hv
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
    (hT : State.Typed ⟨σ, .nil, .atom a⟩ (S ^ C)) (hσ : ⊢ σ : Γ) :
    CapLe Γ [CapAtom.var a.root] C := by
  obtain ⟨Γ₀, T, hσ₀, ht, hK⟩ := hT
  obtain rfl := Store.Typed.ctx_unique hσ hσ₀
  cases hK
  cases ht with
  | atom ha => simpa using (atom_canon hσ ha).capLe

/-- **The capture set of an answer**, in both halves: the annotation of a
returned value, and the root of a returned atom, are bounded by the capture
set of the answer's type. -/
theorem returned_capture_bound {s : Sig} {σ : Store s} {Γ : Ctx s} {S : Shape s}
    {C : CaptureSet s} (hσ : ⊢ σ : Γ) :
    (∀ v : Value s, State.Typed ⟨σ, .nil, .val v⟩ (S ^ C) → CapLe Γ v.annot C) ∧
      (∀ a : Atom s, State.Typed ⟨σ, .nil, .atom a⟩ (S ^ C) →
        CapLe Γ [CapAtom.var a.root] C) :=
  ⟨fun _ hT => returned_capture_bound_val hT hσ,
    fun _ hT => returned_capture_bound_atom hT hσ⟩

end FCdot

end Captures
