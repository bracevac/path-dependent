import Coercions.FCdot.Checker

/-!
# Completeness of the FCdot checker

`Coercions.FCdot.Checker` gives an executable kernel that returns the very
derivation it validated, so soundness is extraction.  This file proves the
converse: every derivation is accepted, and the synthesising cores reproduce
exactly the outputs the derivation assigns.

Because the syntax is fully annotated — `LeCo.obj` carries its source
telescope, `Atom.foldSelf` its target telescope — the evidence layer is
completely determined by its input: no acceptance predicate is needed, and
`synthLe`, `synthEq`, `synthHas`, `synthMorphism` and `synthAtom` are total
inverses of the typing relations.

Since `Tm.proj` now carries its own field-presence evidence, the term layer
searches for nothing either: completeness is unconditional throughout, and the
checking modes are genuine decision procedures.
-/

namespace FCdot

/-! ## Kernel plumbing

Each core builds its result through a small helper; these lemmas evaluate the
helpers at the data a derivation supplies.  Results carry a proof field, so two
results with the same data are equal by proof irrelevance: the statements below
are equations, not mere `isSome` facts. -/

section Plumbing
variable {s : Sig}

theorem exists_of_isSome {α : Type} {o : Option α} (h : o.isSome = true) : ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

theorem leMember_eq {Γ : Ctx s} {a : Atom s} {e : LeCo s} {i : Nat} {S : Ty s}
    {S' T' : Ty (s,x)} {Tel : Telescope (s,x)} (ha : Γ ⊢ₐ a : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.le S' T')) :
    leMember i ha he = some ⟨S'⟦a.root⟧, T'⟦a.root⟧, .member ha he hAt⟩ := by
  simp [leMember, Telescope.getAt?_of_At hAt]

theorem eqMember_eq {Γ : Ctx s} {a : Atom s} {e : LeCo s} {i : Nat} {S : Ty s}
    {S' T' : Ty (s,x)} {Tel : Telescope (s,x)} (ha : Γ ⊢ₐ a : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.eq S' T')) :
    eqMember i ha he = some ⟨S'⟦a.root⟧, T'⟦a.root⟧, .member ha he hAt⟩ := by
  simp [eqMember, Telescope.getAt?_of_At hAt]

theorem hasMember_eq {Γ : Ctx s} {a : Atom s} {e : LeCo s} {i : Nat} {S : Ty s} {ℓ : Label}
    {Tel : Telescope (s,x)} (ha : Γ ⊢ₐ a : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.has ℓ)) :
    hasMember i a.root ha he = some ⟨ℓ, .member ha he hAt⟩ := by
  simp [hasMember, Telescope.getAt?_of_At hAt]

theorem morHas_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat} {ℓ : Label}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) (hAt : src.At j (.has ℓ)) :
    morHas j hm = some ⟨Tel ▹ ∋ ℓ, .has hm hAt⟩ := by
  simp [morHas, Telescope.getAt?_of_At hAt]

theorem morEq_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {X Y : Ty (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eq X Y)) :
    morEq j false hm = some ⟨Tel ▹ X ≐ Y, .eq hm hAt⟩ := by
  simp [morEq, Telescope.getAt?_of_At hAt]

theorem morEqSym_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {X Y : Ty (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eq X Y)) :
    morEq j true hm = some ⟨Tel ▹ Y ≐ X, .eqSym hm hAt⟩ := by
  simp [morEq, Telescope.getAt?_of_At hAt]

theorem lePair_eq {Γ : Ctx s} {e f : LeCo s} {S : Ty s} {Tel₁ Tel₂ : Telescope (s,x)}
    (he : Γ ⊢ e : S ≤ μ Tel₁) (hf : Γ ⊢ f : S ≤ μ Tel₂) :
    lePair Tel₁ Tel₂ he hf = some ⟨S, μ (Tel₁ ++ Tel₂), .pair he hf⟩ := by
  simp [lePair]

theorem atomBoth_eq {Γ : Ctx s} {a b : Atom s} {Tel₁ Tel₂ : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : μ Tel₁) (hb : Γ ⊢ₐ b : μ Tel₂) (hr : b.root = a.root) :
    atomBoth Tel₁ Tel₂ ha hb = some ⟨μ (Tel₁ ++ Tel₂), .both ha hb hr⟩ := by
  simp [atomBoth, hr]

theorem atomUnfold_eq {Γ : Ctx s} {b : Atom s} {Tel : Telescope (s,x)}
    (hb : Γ ⊢ₐ b : .obj Tel) :
    atomUnfold hb = some ⟨.obj (Tel⟦b.root⟧)↑, .unfoldSelf hb⟩ := rfl

theorem tmApp_eq {Γ : Ctx s} {a b : Atom s} {S : Ty s} {T : Ty (s,x)}
    (ha : Γ ⊢ₐ a : .pi S T) (hb : Γ ⊢ₐ b : S) :
    tmApp ha hb = some ⟨T⟦b.root⟧, .app ha hb⟩ := by
  simp [tmApp]

end Plumbing

/-! ## Completeness for evidence

The five evidence judgements are mutually inductive, so the proof is a single
mutual recursion on the derivation.  Every core synthesises, so each statement
is an equation: the kernel returns precisely the derivation's outputs. -/

mutual

/-- The kernel synthesises the endpoints of every inclusion derivation. -/
theorem LeCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {e : LeCo s} {S T : Ty s}
    (h : Γ ⊢ e : S ≤ T), synthLeCore Γ e = some ⟨S, T, h⟩
  | _, _, _, _, _, .refl => by simp [synthLeCore]
  | _, _, _, _, _, .top => by simp [synthLeCore]
  | _, _, _, _, _, .bot => by simp [synthLeCore]
  | _, _, _, _, _, .eqToLe hφ => by
      simp [synthLeCore, EqCo.HasType.complete hφ]
  | _, _, _, _, _, .trans he hf => by
      simp [synthLeCore, LeCo.HasType.complete he, LeCo.HasType.complete hf]
  | _, _, _, _, _, .pi he hf => by
      simp [synthLeCore, LeCo.HasType.complete he, LeCo.HasType.complete hf]
  | _, _, _, _, _, .obj hm => by
      simp [synthLeCore, Morphism.HasType.complete hm]
  | _, _, _, _, _, .pair he hf => by
      simp [synthLeCore, LeCo.HasType.complete he, LeCo.HasType.complete hf, lePair_eq he hf]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthLeCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        leMember_eq ha he hAt]

/-- The kernel synthesises the endpoints of every equality derivation. -/
theorem EqCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {φ : EqCo s} {S T : Ty s}
    (h : Γ ⊢ φ : S ≡ T), synthEqCore Γ φ = some ⟨S, T, h⟩
  | _, _, _, _, _, .refl => by simp [synthEqCore]
  | _, _, _, _, _, .symm hφ => by
      simp [synthEqCore, EqCo.HasType.complete hφ]
  | _, _, _, _, _, .trans hφ hψ => by
      simp [synthEqCore, EqCo.HasType.complete hφ, EqCo.HasType.complete hψ]
  | _, _, _, _, _, .def hd => by
      simp [synthEqCore, witness?_eq_some hd]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthEqCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        eqMember_eq ha he hAt]

/-- The kernel synthesises the label of every field-presence derivation. -/
theorem Has.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label}
    (h : Has.HasType Γ hv y ℓ), synthHasCore Γ hv y = some ⟨ℓ, h⟩
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthHasCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        hasMember_eq ha he hAt]
  | _, _, _, _, _, .field hf hm => by
      simp [synthHasCore, witness?_eq_some hf, hm]

/-- The kernel accepts every `pre` side at the endpoint next to its hole, and
synthesises the outer one. -/
theorem Side.HasType.completePre : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {S X : Ty (s,x)}
    (h : Side.HasType Γ side S X), checkPreCore Γ side X = some ⟨S, h⟩
  | _, _, _, _, _, .none => by simp [checkPreCore]
  | _, _, _, _, _, .some he => by
      simp [checkPreCore, LeCo.HasType.complete he]

/-- The same for `post` sides. -/
theorem Side.HasType.completePost : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {Y T : Ty (s,x)}
    (h : Side.HasType Γ side Y T), checkPostCore Γ side Y = some ⟨T, h⟩
  | _, _, _, _, _, .none => by simp [checkPostCore]
  | _, _, _, _, _, .some he => by
      simp [checkPostCore, LeCo.HasType.complete he]

/-- The kernel synthesises the target telescope of every morphism derivation. -/
theorem Morphism.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)}
    {m : Morphism s} {Tel : Telescope (s,x)} (h : Γ ⊢ m : src ⇒ Tel),
      synthMorCore Γ src m = some ⟨Tel, h⟩
  | _, _, _, _, _, .nil => by simp [synthMorCore]
  | _, _, _, _, _, .le hm hAt hpre hpost => by
      simp [synthMorCore, Morphism.HasType.complete hm, Hole.read?_of_Reads (.le hAt),
        Side.HasType.completePre hpre, Side.HasType.completePost hpost]
  | _, _, _, _, _, .leEq hm hAt hpre hpost => by
      simp [synthMorCore, Morphism.HasType.complete hm, Hole.read?_of_Reads (.eq hAt),
        Side.HasType.completePre hpre, Side.HasType.completePost hpost]
  | _, _, _, _, _, .leEqSym hm hAt hpre hpost => by
      simp [synthMorCore, Morphism.HasType.complete hm, Hole.read?_of_Reads (.eqSym hAt),
        Side.HasType.completePre hpre, Side.HasType.completePost hpost]
  | _, _, _, _, _, .eq hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morEq_eq hm hAt]
  | _, _, _, _, _, .eqSym hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morEqSym_eq hm hAt]
  | _, _, _, _, _, .has hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morHas_eq hm hAt]

/-- The kernel synthesises the type of every atom derivation. -/
theorem Atom.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T), synthAtomCore Γ a = some ⟨T, h⟩
  | _, _, _, _, .var => by simp [synthAtomCore]
  | _, _, _, _, .cast hb he => by
      simp [synthAtomCore, Atom.HasType.complete hb, LeCo.HasType.complete he]
  | _, _, _, _, .unfoldSelf hb => by
      simp [synthAtomCore, Atom.HasType.complete hb, atomUnfold_eq hb]
  | _, _, _, _, .foldSelf hb => by
      simp [synthAtomCore, Atom.HasType.complete hb]
  | _, _, _, _, .both ha hb hr => by
      simp [synthAtomCore, Atom.HasType.complete ha, Atom.HasType.complete hb,
        atomBoth_eq ha hb hr]

end

/-! ## Completeness for terms

Terms, values and field blocks form the second mutual family.  Every rule of
this layer carries the evidence its premises need, so the statements are again
plain equations, with no side condition. -/

mutual

/-- The kernel synthesises the type of every term derivation. -/
theorem Tm.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T), synthTmCore Γ t = some ⟨T, h⟩
  | _, _, _, _, .atom ha => by
      simp [synthTmCore, Atom.HasType.complete ha]
  | _, _, _, _, .val hv => by
      simp [synthTmCore, Value.HasType.complete hv]
  | _, _, _, _, .app ha hb => by
      simp [synthTmCore, Atom.HasType.complete ha, Atom.HasType.complete hb, tmApp_eq ha hb]
  | _, _, _, _, .proj ha hh => by
      simp [synthTmCore, Atom.HasType.complete ha, Has.HasType.complete hh]
  | _, _, _, _, .let ht hu => by
      simp [synthTmCore, Tm.HasType.complete ht, Tm.HasType.complete hu,
        Ty.strengthenW?_weaken]
  | _, _, _, _, .cast ht he => by
      simp [synthTmCore, Tm.HasType.complete ht, LeCo.HasType.complete he]

/-- The kernel synthesises the type of every value derivation. -/
theorem Value.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T), synthValueCore Γ v = some ⟨T, h⟩
  | _, _, _, _, .lam ht => by
      simp [synthValueCore, Tm.HasType.complete ht]
  | _, _, _, _, .obj hg hF => by
      simp only [Witnesses.Guarded] at hg
      simp [synthValueCore, hg, Fields.HasType.complete hF]
  | _, _, _, _, .cast hv he => by
      simp [synthValueCore, Value.HasType.complete hv, LeCo.HasType.complete he]

/-- The kernel accepts every field block derivation. -/
theorem Fields.HasType.complete : ∀ {s : Sig} {Γ : Ctx (s,x)} {F : Fields (s,x)}
    (h : Γ ⊢ᶠ F), checkFieldsCore Γ F = some ⟨h⟩
  | _, _, _, .nil => by simp [checkFieldsCore]
  | _, _, _, .cons hF ht => by
      simp [checkFieldsCore, Fields.HasType.complete hF, Tm.HasType.complete ht]

end

/-! ## Public interface

Soundness lives in `Coercions.FCdot.Checker`; here it is paired with
completeness into decision procedures. -/

section Public
variable {s : Sig}

theorem synthLe_complete {Γ : Ctx s} {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    synthLe Γ e = some (S, T) := by
  simp [synthLe, LeCo.HasType.complete h]

theorem synthLe_iff {Γ : Ctx s} {e : LeCo s} {S T : Ty s} :
    synthLe Γ e = some (S, T) ↔ Γ ⊢ e : S ≤ T :=
  ⟨synthLe_sound, synthLe_complete⟩

theorem checkLe_complete {Γ : Ctx s} {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    checkLe Γ e S T = true :=
  decide_eq_true (synthLe_complete h)

theorem checkLe_iff {Γ : Ctx s} {e : LeCo s} {S T : Ty s} :
    checkLe Γ e S T = true ↔ Γ ⊢ e : S ≤ T :=
  ⟨checkLe_sound, checkLe_complete⟩

theorem synthEq_complete {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) :
    synthEq Γ φ = some (S, T) := by
  simp [synthEq, EqCo.HasType.complete h]

theorem synthEq_iff {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} :
    synthEq Γ φ = some (S, T) ↔ Γ ⊢ φ : S ≡ T :=
  ⟨synthEq_sound, synthEq_complete⟩

theorem checkEq_complete {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) :
    checkEq Γ φ S T = true :=
  decide_eq_true (synthEq_complete h)

theorem checkEq_iff {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} :
    checkEq Γ φ S T = true ↔ Γ ⊢ φ : S ≡ T :=
  ⟨checkEq_sound, checkEq_complete⟩

theorem synthHas_complete {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label}
    (h : Has.HasType Γ hv y ℓ) : synthHas Γ hv y = some ℓ := by
  simp [synthHas, Has.HasType.complete h]

theorem synthHas_iff {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label} :
    synthHas Γ hv y = some ℓ ↔ Has.HasType Γ hv y ℓ :=
  ⟨synthHas_sound, synthHas_complete⟩

theorem checkHas_complete {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label}
    (h : Has.HasType Γ hv y ℓ) : checkHas Γ hv y ℓ = true :=
  decide_eq_true (synthHas_complete h)

theorem checkHas_iff {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label} :
    checkHas Γ hv y ℓ = true ↔ Has.HasType Γ hv y ℓ :=
  ⟨checkHas_sound, checkHas_complete⟩

theorem synthMorphism_complete {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} (h : Γ ⊢ m : src ⇒ Tel) :
    synthMorphism Γ src m = some Tel := by
  simp [synthMorphism, Morphism.HasType.complete h]

theorem synthMorphism_iff {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} :
    synthMorphism Γ src m = some Tel ↔ Γ ⊢ m : src ⇒ Tel :=
  ⟨synthMorphism_sound, synthMorphism_complete⟩

theorem checkMorphism_complete {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} (h : Γ ⊢ m : src ⇒ Tel) : checkMorphism Γ src m Tel = true :=
  decide_eq_true (synthMorphism_complete h)

theorem checkMorphism_iff {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} :
    checkMorphism Γ src m Tel = true ↔ Γ ⊢ m : src ⇒ Tel :=
  ⟨checkMorphism_sound, checkMorphism_complete⟩

theorem synthAtom_complete {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    synthAtom Γ a = some T := by
  simp [synthAtom, Atom.HasType.complete h]

theorem synthAtom_iff {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    synthAtom Γ a = some T ↔ Γ ⊢ₐ a : T :=
  ⟨synthAtom_sound, synthAtom_complete⟩

theorem checkAtom_complete {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    checkAtom Γ a T = true :=
  decide_eq_true (synthAtom_complete h)

theorem checkAtom_iff {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    checkAtom Γ a T = true ↔ Γ ⊢ₐ a : T :=
  ⟨checkAtom_sound, checkAtom_complete⟩

theorem synthTm_complete {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : Γ ⊢ t : T) :
    synthTm Γ t = some T := by
  simp [synthTm, Tm.HasType.complete h]

theorem synthTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} :
    synthTm Γ t = some T ↔ Γ ⊢ t : T :=
  ⟨synthTm_sound, synthTm_complete⟩

theorem checkTm_complete {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : Γ ⊢ t : T) :
    checkTm Γ t T = true :=
  decide_eq_true (synthTm_complete h)

theorem checkTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} :
    checkTm Γ t T = true ↔ Γ ⊢ t : T :=
  ⟨checkTm_sound, checkTm_complete⟩

theorem synthValue_complete {Γ : Ctx s} {v : Value s} {T : Ty s} (h : Γ ⊢ᵥ v : T) :
    synthValue Γ v = some T := by
  simp [synthValue, Value.HasType.complete h]

theorem synthValue_iff {Γ : Ctx s} {v : Value s} {T : Ty s} :
    synthValue Γ v = some T ↔ Γ ⊢ᵥ v : T :=
  ⟨synthValue_sound, synthValue_complete⟩

theorem checkValue_complete {Γ : Ctx s} {v : Value s} {T : Ty s} (h : Γ ⊢ᵥ v : T) :
    checkValue Γ v T = true :=
  decide_eq_true (synthValue_complete h)

theorem checkValue_iff {Γ : Ctx s} {v : Value s} {T : Ty s} :
    checkValue Γ v T = true ↔ Γ ⊢ᵥ v : T :=
  ⟨checkValue_sound, checkValue_complete⟩

theorem checkFields_complete {Γ : Ctx (s,x)} {F : Fields (s,x)} (h : Γ ⊢ᶠ F) :
    checkFields Γ F = true := by
  simp [checkFields, Fields.HasType.complete h]

theorem checkFields_iff {Γ : Ctx (s,x)} {F : Fields (s,x)} :
    checkFields Γ F = true ↔ Γ ⊢ᶠ F :=
  ⟨checkFields_sound, checkFields_complete⟩

end Public

/-! ## Determinism

Synthesis is a function, so the evidence layer pins its outputs down with no
hypothesis whatsoever: this is the determinism that makes the checking modes
sound to implement by synthesis and comparison. -/

section Determinism
variable {s : Sig}

theorem LeCo.HasType.endpoints_unique {Γ : Ctx s} {e : LeCo s} {S T S' T' : Ty s}
    (h : Γ ⊢ e : S ≤ T) (h' : Γ ⊢ e : S' ≤ T') : S = S' ∧ T = T' := by
  have := (synthLe_complete h).symm.trans (synthLe_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem EqCo.HasType.endpoints_unique {Γ : Ctx s} {φ : EqCo s} {S T S' T' : Ty s}
    (h : Γ ⊢ φ : S ≡ T) (h' : Γ ⊢ φ : S' ≡ T') : S = S' ∧ T = T' := by
  have := (synthEq_complete h).symm.trans (synthEq_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem Has.HasType.label_unique {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ ℓ' : Label}
    (h : Has.HasType Γ hv y ℓ) (h' : Has.HasType Γ hv y ℓ') : ℓ = ℓ' := by
  have := (synthHas_complete h).symm.trans (synthHas_complete h')
  simpa using this

theorem Morphism.HasType.telescope_unique {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel Tel' : Telescope (s,x)} (h : Γ ⊢ m : src ⇒ Tel)
    (h' : Γ ⊢ m : src ⇒ Tel') : Tel = Tel' := by
  have := (synthMorphism_complete h).symm.trans (synthMorphism_complete h')
  simpa using this

theorem Atom.HasType.type_unique {Γ : Ctx s} {a : Atom s} {T T' : Ty s}
    (h : Γ ⊢ₐ a : T) (h' : Γ ⊢ₐ a : T') : T = T' := by
  have := (synthAtom_complete h).symm.trans (synthAtom_complete h')
  simpa using this

end Determinism

/-! ### Determinism for terms

The term layer is deterministic as well.  The proof is a direct induction on
the derivations rather than a corollary of synthesis: the projection rule fixes
the type as `a.root.ℓ` whatever evidence it used. -/

mutual

theorem Tm.HasType.type_unique : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T T' : Ty s},
    Γ ⊢ t : T → Γ ⊢ t : T' → T = T'
  | _, _, _, _, _, .atom ha, h' => by
      cases h' with
      | atom ha' => exact ha.type_unique ha'
  | _, _, _, _, _, .val hv, h' => by
      cases h' with
      | val hv' => exact Value.HasType.type_unique hv hv'
  | _, _, _, _, _, .app ha hb, h' => by
      cases h' with
      | app ha' hb' =>
          have hp := ha.type_unique ha'
          injection hp with _ _ hT
          rw [hT]
  | _, _, _, _, _, .proj _ _, h' => by
      cases h' with
      | proj _ _ => rfl
  | _, _, _, _, _, .let ht hu, h' => by
      cases h' with
      | «let» ht' hu' =>
          have hT := Tm.HasType.type_unique ht ht'
          subst hT
          have hU := Tm.HasType.type_unique hu hu'
          have := congrArg Ty.strengthen? hU
          rw [Ty.strengthen?_weaken, Ty.strengthen?_weaken] at this
          exact Option.some.inj this
  | _, _, _, _, _, .cast _ he, h' => by
      cases h' with
      | cast _ he' => exact (he.endpoints_unique he').2

theorem Value.HasType.type_unique : ∀ {s : Sig} {Γ : Ctx s} {v : Value s} {T T' : Ty s},
    Γ ⊢ᵥ v : T → Γ ⊢ᵥ v : T' → T = T'
  | _, _, _, _, _, .lam ht, h' => by
      cases h' with
      | lam ht' => rw [Tm.HasType.type_unique ht ht']
  | _, _, _, _, _, .obj _ _, h' => by
      cases h' with
      | obj _ _ => rfl
  | _, _, _, _, _, .cast _ he, h' => by
      cases h' with
      | cast _ he' => exact (he.endpoints_unique he').2

end

end FCdot
