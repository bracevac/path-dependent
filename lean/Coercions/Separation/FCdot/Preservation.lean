import Coercions.Separation.FCdot.Retyping
import Coercions.Separation.FCdot.CanonicalForms

namespace Separation

/-!
# Preservation for the FCdot store machine

Every step of a well-typed state yields a well-typed state; allocation
extends the signature, and the result type is transported along the
signature embedding (`Rename.succ` for `alloc`, the identity otherwise).
The lemmas each step reads are in `Retyping.lean`.
-/

namespace FCdot

/-! ## The steps that substitute into a body

These read `Tm.HasType.subst` along a substitution into the store context,
which needs a `Ctx.NamesMap` the substitution's own premises do not give.  They
stay here until the store forms of the substitution lemmas land (group g8,
`s0-g6r.md`). -/

/-- `alloc`: the stripped literal is stored at its own type, and the
continuation body is adjusted to use the new variable under the composite of
the stripped casts. -/
theorem preservation_alloc {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)} {v : Value s} {T U : Ty s}
    (hσ : ⊢ σ : Γ) (hms : Γ.ModeSound) (hv : Γ ⊢ᵥ v : T)
    (hK : Γ ⊢ₖ K ▹ .let u U' f : .ty T ⇒ U) :
    State.Typed ⟨.cons σ v.core, K↑, u.adjust v⟩ U↑ := by
  cases hK with
  | «let» hu _ hK' =>
      obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v T hv
      have hWc := hcore.obj_names_accessOnly hlit
      refine ⟨_, _, Store.Typed.cons hσ hlit hcore, ?_, Cont.Typed.weaken hK' _⟩
      rcases hd with ⟨hn, rfl⟩ | ⟨E, hE?, hE⟩
      · rw [show u.adjust v = u by simp [Tm.adjust, hn]]
        exact hu.refine (Ctx.Refines.transparent hWc)
      · rw [show u.adjust v = u.subst (Subst.selfCast E↑) by simp [Tm.adjust, hE?]]
        simpa using hu.subst (Subst.Typed.selfCast (W := v.core.witnesses)
          (Fs := v.core.fieldLabels) hE hms hWc)

/-- β: a closure applied at its own function type.  The step enters the body
by one substitution, which instantiates the parameter at the argument, the
arrow's capture binder at the argument's root and the body root at the
universal root, and the last of the three is what asks the context to bind no
root of its own (B1.5, discharged at the machine by `Store.Typed.rootFree`). -/
theorem Value.HasType.beta {s : Sig} {Γ : Ctx s} {A : CaptureSet s} {S₀ S : Dom s}
    {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)} {T : Cod s} {C : CaptureSet s}
    {b : Atom s} (hΓ : Γ.root? = none)
    (hlam : Γ ⊢ᵥ .lam A S₀ t₀ g : (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root)))
    (hacc : Γ.AccessOnly [CapAtom.var b.root])
    (hbn : ∀ ℓ, Γ.AccessOnly [CapAtom.name b.root ℓ]) :
    Γ ⊢ t₀.subst (Subst.enter b) :ᵉ T.subst (Subst.arg b) := by
  obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv hlam
  obtain ⟨-, rfl, rfl⟩ : C = A ∧ S = S₀ ∧ T = T₀ := by
    simpa [Ty.capt.injEq, Shape.pi.injEq] using hTe
  have h := ht₀.subst (Subst.Typed.enter hΓ hb hacc hbn)
  rwa [Cod.underRoot_enter] at h

/-- β for a closure stored at the root of an atom whose type is that root's
type: `appVar`, and `appCastRefl` where the casts normalize to the identity. -/
theorem Store.Typed.beta {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ S : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    {T : Cod s} {C : CaptureSet s} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) (hty : Γ.lookupTy x = (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root)))
    (hacc : Γ.AccessOnly [CapAtom.var b.root]) :
    Γ ⊢ t₀.subst (Subst.enter b) :ᵉ T.subst (Subst.arg b) :=
  (hty ▸ hσ.lam_of_lookup hx).beta hσ.rootFree hb hacc (hσ.names_accessOnly b.root)

/-- β through a function coercion `pi d c`: the argument is cast by the
domain evidence read at the argument's root, and the result by the codomain
evidence read at the argument. -/
theorem Tm.HasType.betaCast {s : Sig} {Γ : Ctx s} {S₀ S : Dom s} {t₀ : Tm (Sig.body s)}
    {T₀ T : Cod s} {d : LeCo (Sig.scope s)} {c : ELeCo (Sig.body s)} {b : Atom s}
    (hΓ : Γ.root? = none)
    (ht₀ : (Γ.body S₀) ⊢ t₀ :ᵉ T₀.underRoot)
    (hdom : Γ.scope ⊢ d : S.underRoot ≤ S₀.underRoot)
    (hcod : (Γ.body S) ⊢ᵉ c : T₀.underRoot ≤ T.underRoot)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root)))
    (hacc : Γ.AccessOnly [CapAtom.var b.root])
    (hbn : ∀ ℓ, Γ.AccessOnly [CapAtom.name b.root ℓ]) :
    Γ ⊢ .castE (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
        (c.subst (Subst.enter b)) :ᵉ T.subst (Subst.arg b) := by
  -- the domain evidence, instantiated at the argument's root
  have hb' := Atom.HasType.castDom hΓ hdom hb hacc
  have hcod' := ELeCo.HasType.subst (Subst.Typed.enter hΓ hb hacc hbn) hcod
  rw [Cod.underRoot_enter, Cod.underRoot_enter] at hcod'
  refine Tm.HasType.castE ?_ hcod'
  have h := ht₀.subst (Subst.Typed.enter hΓ hb' hacc hbn)
  rw [Cod.underRoot_enter, Ty.arg_congr T₀ (a := .cast b (d.subst (Subst.enterC b)))
    (a' := b) rfl] at h
  exact h

/-- Projecting a field of a stored object literal, in full: the field's body
with the self binder replaced by the object's variable has the projection's
type, the object's type is the precise object type at its own annotation, and
the field's closing evidence, read at the same variable, puts the body's use
set below that annotation united with the variable.  `Tm.HasType.projField`
below is the first component, the one preservation uses; `step_uses` reads
the third at the `proj` step. -/
theorem Tm.HasType.projFieldFull {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields ((s,c),x)}
    {ℓ : Label} {t : Tm ((s,c),x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    (Γ ⊢ t.subst (Subst.enterObj y) : (y ∙ ℓ) ^ [CapAtom.name y ℓ]) ∧
      Γ.lookupTy y = (μ (Telescope.ofLiteral W Wc F.labels)) ^ A ∧
      ∃ g', Γ ⊢ᶜ g' : (t.subst (Subst.enterObj y)).uses ⊑ (A ∪ [CapAtom.var y]) := by
  have hval := hσ.lookup y
  rw [hx] at hval
  obtain ⟨hTe, hF⟩ := Value.HasType.obj_inv hval
  have hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧) := by
    intro l
    have hlk := hσ.lookupDef y l
    rw [hx] at hlk
    simpa [Value.witnesses] using hlk
  have hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧) := by
    intro l
    have hlk := hσ.lookupDefC y l
    rw [hx] at hlk
    simpa [Value.capWitnesses] using hlk
  have hfields : Γ.lookupFields y = some F.labels := by
    have hlk := hσ.lookupFields y
    rw [hx] at hlk
    simpa [Value.fieldLabels] using hlk
  have hname : ∀ ℓ m, (Γ.cons (.transparent ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A)
      W Wc F.labels)).ModeBound (.name .here ℓ) m → Γ.ModeBound (.name y ℓ) m := by
    intro ℓ m h
    rw [hσ.modeBound_name y ℓ m, hTe, hx]
    exact h
  have hsub := Subst.Typed.enterObj (W := W) (Wc := Wc) (ls := F.labels)
    hσ.rootFree hTe hdef hdefC hfields (Ctx.modeMap_enterObj hTe hfields hname)
  obtain ⟨ht, ⟨g', hg'⟩⟩ := Fields.HasType.getFull F hF ℓ t hg
  refine ⟨?_, hTe, ⟨g'.subst (Subst.enterObj y), ?_⟩⟩
  · simpa [Ty.subst, Shape.subst, CaptureSet.subst, CapAtom.subst, Subst.rootVar,
      Subst.enterObj, Atom.root] using ht.subst hsub
  · have h := hg'.subst hsub
    rw [CaptureSet.subst_union, CaptureSet.weaken2_subst_enterObj, ← Tm.uses_subst] at h
    simpa [CaptureSet.subst, CapAtom.subst, Subst.rootVar, Subst.enterObj, Atom.root] using h

/-- Projecting a field of a stored object literal: the field's body, with the
self binder replaced by the object's variable, has the projection's type. -/
theorem Tm.HasType.projField {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields ((s,c),x)}
    {ℓ : Label} {t : Tm ((s,c),x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    Γ ⊢ t.subst (Subst.enterObj y) : (y ∙ ℓ) ^ [CapAtom.name y ℓ] :=
  (Tm.HasType.projFieldFull hσ hx hg).1

/-- `Tm.HasType.substAtom` at the answer sort. -/
theorem Tm.HasType.substAtomE {s : Sig} {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)} {E : ETy (s,x)}
    {a : Atom s} (hu : (Γ.cons (.opaque T)) ⊢ u :ᵉ E) (ha : Γ ⊢ₐ a : T)
    (hms : Γ.ModeSound) (hn : ∀ ℓ, Γ.AccessOnly [CapAtom.name a.root ℓ]) :
    Γ ⊢ u.substAtom a :ᵉ (E⟦a.root⟧) := by
  have := hu.subst (Subst.Typed.single ha (Ctx.modeMap_single hms ha hn))
  simpa [Tm.substAtom] using this

/-- `Tm.HasType.letBody_substAtom` at the answer sort: what `rename` and
`unpackAtom` produce. -/
theorem Tm.HasType.letBody_substAtomE {s : Sig} {Γ : Ctx s} {T : Ty s} {E : ETy s}
    {u : Tm (s,x)} {a : Atom s}
    (hu : (Γ.cons (.opaque T)) ⊢ u :ᵉ E↑) (ha : Γ ⊢ₐ a : T)
    (hms : Γ.ModeSound) (hn : ∀ ℓ, Γ.AccessOnly [CapAtom.name a.root ℓ]) :
    Γ ⊢ u.substAtom a :ᵉ E := by
  have := Tm.HasType.substAtomE hu ha hms hn
  rwa [ETy.weaken_substVar] at this

/-- `rename`: the body of a let frame, instantiated at the atom the state
carries, is typed at the frame's result type. -/
theorem Tm.HasType.letBody_substAtom {s : Sig} {Γ : Ctx s} {T U : Ty s} {u : Tm (s,x)}
    {a : Atom s} (hu : (Γ.cons (.opaque T)) ⊢ u : U↑) (ha : Γ ⊢ₐ a : T)
    (hms : Γ.ModeSound) (hn : ∀ ℓ, Γ.AccessOnly [CapAtom.name a.root ℓ]) :
    Γ ⊢ u.substAtom a : U := by
  simpa using hu.substAtom ha (Ctx.modeMap_single hms ha hn)

/-- The frame's body, read in the store's `.inst C` context.  This is
`Ctx.Ren.instC` lifted by the payload binder, at the identity renaming. -/
theorem Tm.HasType.letexBody_instC {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T : Dom s}
    {u : Tm ((s,c),x)} {E : ETy s} (hC : Γ.AccessOnly C)
    (hu : ((Γ.consC .star).cons (.opaque T)) ⊢ u :ᵉ
      (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E))) :
    ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ u :ᵉ
      (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) := by
  have h := hu.rename ((Ctx.Ren.instC (Γ := Γ) (C := C) hC).lift (.opaque T))
  simpa [Binding.rename, Rename.lift_id] using h

/-- `unpackAtom`: the store gains the witness as an instance binder, the
continuation is weakened into the new scope, and the body is instantiated at
the wrapper's atom read there. -/
theorem preservation_unpackAtom {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {h : CapCo s} {f : CapCo ((s,c),x)}
    {C C₀ : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {a : Atom s}
    {T : Dom s} {U : Ty s}
    (hσ : ⊢ σ : Γ) (hms : (Γ.consC (.inst C)).ModeSound)
    (hp : Γ ⊢ₚ .pack C h₀ e a : ∃ᶜ[C₀] T)
    (hK : Γ ⊢ₖ K ▹ .letex u U' h f : ∃ᶜ[C₀] T ⇒ U) :
    State.Typed ⟨σ.consC (.inst C), K.weakenC,
        u.substAtom (.cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot))⟩
      (Ty.weaken (k := .cap) U) := by
  cases hK with
  | letex hh hu hf hK' =>
      cases hp with
      | pack ha hb he hA =>
          have hσ' : ⊢ σ.consC (.inst C) : Γ.consC (.inst C) := hσ.consC rfl
          refine ⟨Γ.consC (.inst C), _, hσ', ?_, Cont.Typed.weakenC hK' (.inst C) rfl⟩
          exact Tm.HasType.letBody_substAtomE (Tm.HasType.letexBody_instC hA hu)
            (Atom.HasType.unpackPayload hσ.rootFree ha he) hms (hσ'.names_accessOnly _)

/-- `unpackVal`: the store gains the witness as an instance binder and then the
literal, which is what `preservation_alloc` already packages. -/
theorem preservation_unpackVal {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {h : CapCo s} {f : CapCo ((s,c),x)}
    {C C₀ : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {v : Value s}
    {T : Dom s} {U : Ty s}
    (hσ : ⊢ σ : Γ) (hms : (Γ.consC (.inst C)).ModeSound)
    (hv : Γ ⊢ᵥᵉ .pack C h₀ e v : ∃ᶜ[C₀] T)
    (hK : Γ ⊢ₖ K ▹ .letex u U' h f : ∃ᶜ[C₀] T ⇒ U) :
    State.Typed
      ⟨(σ.consC (.inst C)).cons
          (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot)).core,
        (K.weakenC).weaken,
        u.adjust (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot))⟩
      (Ty.weaken (k := .var) (Ty.weaken (k := .cap) U)) := by
  cases hK with
  | letex hh hu hf hK' =>
      cases hv with
      | pack hv₀ hb he hA =>
          have hf' : ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ᶜ f :
              u.uses ⊑ CaptureSet.weaken (k := .var)
                (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here]) := by
            have h := CapCo.HasType.letexCharge_instC (C := C) hA hf
            rwa [show CaptureSet.weaken (k := .var)
                (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here])
              = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
                  ∪ [CapAtom.cvar (.there .here)]) from
              CaptureSet.rename_union _ _ _]
          exact preservation_alloc (hσ.consC rfl) hms
            (Value.HasType.unpackPayload hσ.rootFree hv₀ he)
            (Cont.Typed.let (Tm.HasType.letexBody_instC hA hu) hf'
              (Cont.Typed.weakenC hK' (.inst C) rfl))

theorem preservation {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hF : ∀ Γ, ⊢ st.σ : Γ → FormsTyped st.σ Γ)
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) := by
  cases step <;> obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
  case «let» =>
      cases ht with
      | «let» ht' hu hf => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .let hu hf hK⟩
  case castPush =>
      cases ht with
      | cast ht' he => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .cast he hK⟩
  case castVal =>
      cases ht with
      | val hv =>
          cases hK with
          | cast he hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .val (.plain (hv.ty_inv.cast he)), hK'⟩
  case castAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | cast he hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .atom (PAtom.HasType.applyE (.plain _) hp (.plain he)), hK'⟩
  case alloc =>
      cases ht with
      | val hv =>
          cases hK with
          | «let» hu hf hK' =>
              exact ⟨Rename.succ,
                preservation_alloc hσ (hF Γ hσ).modeSound hv.ty_inv (.let hu hf hK')⟩
  case rename =>
      cases ht with
      | atom hp =>
          cases hp with
          | plain ha =>
              cases hK with
              | «let» hu _ hK' =>
                  exact State.Typed.exists_rename_id
                    ⟨Γ, _, hσ, Tm.HasType.letBody_substAtomE hu ha (hF Γ hσ).modeSound
                      (hσ.names_accessOnly _), hK'⟩
  -- The three answer-cast steps.  None has a premise, and none reads a head
  -- form: the frame holds the coercion and `applyE` is total.
  case castEPush =>
      cases ht with
      | castE ht' hg => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .castE hg hK⟩
  case castEVal =>
      cases ht with
      | val hv =>
          cases hK with
          | castE hg hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .val (Value.HasTypeE.applyE _ hv hg), hK'⟩
  case castEAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | castE hg hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .atom (PAtom.HasType.applyE _ hp hg), hK'⟩
  case letex =>
      cases ht with
      | letex ht' hh hu hf =>
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .letex hh hu hf hK⟩
  case unpackAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | letex hh hu hf hK' =>
              exact ⟨Rename.succ,
                preservation_unpackAtom hσ ((hF Γ hσ).modeSoundC _ rfl) hp
                  (.letex hh hu hf hK')⟩
  case unpackVal =>
      cases ht with
      | val hv =>
          cases hK with
          | letex hh hu hf hK' =>
              refine ⟨Rename.succ.comp Rename.succ, ?_⟩
              have h := preservation_unpackVal hσ ((hF Γ hσ).modeSoundC _ rfl) hv
                (.letex hh hu hf hK')
              simpa only [Ty.weaken, Ty.rename_comp] using h
  case appVar hx =>
      cases ht with
      | app ha hb hacc =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, hσ.beta hx (Atom.HasType.var_inv ha).symm hb hacc, hK⟩
  case appCastRefl hx _ hcf hid =>
      cases ht with
      | app ha hb hacc =>
          obtain ⟨C₀, hty⟩ := Ty.shape_eq_iff.mp ((hF Γ hσ).refl ha hcf hid)
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, hσ.beta hx hty hb hacc, hK⟩
  case appCast hx _ hcf =>
      cases ht with
      | app ha hb hacc =>
          obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv (hσ.lam_of_lookup hx)
          obtain ⟨hdom, hcod⟩ := (hF Γ hσ).pi ha hcf (by rw [hTe]; rfl)
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, ht₀.betaCast hσ.rootFree hdom hcod hb hacc
              (hσ.names_accessOnly _), hK⟩
  case proj hx hg =>
      cases ht with
      | proj _ _ => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, Tm.HasType.projField hσ hx hg, hK⟩
  case unboxRefl hx hcf hid =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (.plain (hσ.unboxRefl_result (hF Γ hσ) hx ha hcf hid)), hK⟩
  case unboxCast hx hcf =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (.plain (hσ.unboxCast_result (hF Γ hσ) hx ha hcf)), hK⟩

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun _ hσ => hσ.formsTyped) hT step

end FCdot

end Separation
