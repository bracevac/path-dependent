import Coercions.CapturesCC.FCdot.Checker

namespace CapturesCC

/-!
# Completeness of the FCdot checker

`Coercions.CapturesCC.FCdot.Checker` gives an executable kernel that returns the
very derivation it validated, so soundness is extraction.  This file proves the
converse: every derivation is accepted, and the synthesising cores reproduce
exactly the outputs the derivation assigns.

Because the syntax is fully annotated — `ShapeCo.obj` carries its source
telescope, `Atom.foldSelf` its target telescope — the evidence layer is
completely determined by its input: no acceptance predicate is needed, and
`synthShape`, `synthCap`, `synthLe`, `synthEq`, `synthHas`, `synthMorphism`
and `synthAtom` are total inverses of the typing relations.

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

theorem capElem_eq {Γ : Ctx s} {C D : CaptureSet s} (h : C.Subset D) :
    capElem (Γ := Γ) C D = some ⟨C, D, .elem h⟩ := by
  simp only [capElem, dif_pos h]

theorem leMember_eq {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} {i : Nat} {S : Shape s}
    {C : CaptureSet s} {S' T' : Shape (s,x)} {Tel : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : S ^ C) (he : Γ ⊢ˢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.le S' T')) :
    leMember i ha he = some ⟨S'⟦a.root⟧, T'⟦a.root⟧, .member ha he hAt⟩ := by
  simp [leMember, Telescope.getAt?_of_At hAt]

theorem eqMember_eq {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} {i : Nat} {S : Shape s}
    {C : CaptureSet s} {S' T' : Shape (s,x)} {Tel : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : S ^ C) (he : Γ ⊢ˢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.eq S' T')) :
    eqMember i ha he = some ⟨S'⟦a.root⟧, T'⟦a.root⟧, .member ha he hAt⟩ := by
  simp [eqMember, Telescope.getAt?_of_At hAt]

theorem hasMember_eq {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} {i : Nat} {S : Shape s}
    {C : CaptureSet s} {ℓ : Label} {Tel : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : S ^ C) (he : Γ ⊢ˢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.has ℓ)) :
    hasMember i a.root ha he = some ⟨ℓ, .member ha he hAt⟩ := by
  simp [hasMember, Telescope.getAt?_of_At hAt]

theorem morHas_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat} {ℓ : Label}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) (hAt : src.At j (.has ℓ)) :
    morHas j hm = some ⟨Tel ▹ ∋ ℓ, .has hm hAt⟩ := by
  simp [morHas, Telescope.getAt?_of_At hAt]

theorem morEq_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {X Y : Shape (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eq X Y)) :
    morEq j false hm = some ⟨Tel ▹ X ≐ Y, .eq hm hAt⟩ := by
  simp [morEq, Telescope.getAt?_of_At hAt]

theorem morEqSym_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {X Y : Shape (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eq X Y)) :
    morEq j true hm = some ⟨Tel ▹ Y ≐ X, .eqSym hm hAt⟩ := by
  simp [morEq, Telescope.getAt?_of_At hAt]

theorem leBound_eq {Γ : Ctx s} {Tel : Telescope (s,x)} {i : Nat} {S : Shape s}
    (hAt : Tel ∋ (i ↦ ⊑ S↑)) :
    leBound (Γ := Γ) Tel i = some ⟨μ Tel, S, .bound hAt⟩ := by
  simp [leBound, Telescope.getAt?_of_At hAt, Shape.strengthenW?_weaken]

theorem morBnd_eq {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s} {e : ShapeCo s}
    {S : Shape s} (hm : Γ ⊢ m : src ⇒ Tel) (he : Γ ⊢ˢ e : μ src ≤ S) :
    morBnd hm he = some ⟨Tel ▹ ⊑ S↑, .bnd hm he⟩ := by
  simp [morBnd]

theorem lePair_eq {Γ : Ctx s} {e f : ShapeCo s} {S : Shape s} {Tel₁ Tel₂ : Telescope (s,x)}
    (he : Γ ⊢ˢ e : S ≤ μ Tel₁) (hf : Γ ⊢ˢ f : S ≤ μ Tel₂) :
    lePair Tel₁ Tel₂ he hf = some ⟨S, μ (Tel₁ ++ Tel₂), .pair he hf⟩ := by
  simp [lePair]

theorem atomBoth_eq {Γ : Ctx s} {a b : Atom s} {Tel₁ Tel₂ : Telescope (s,x)}
    {C : CaptureSet s}
    (ha : Γ ⊢ₐ a : (μ Tel₁) ^ C) (hb : Γ ⊢ₐ b : (μ Tel₂) ^ C) (hr : b.root = a.root) :
    atomBoth Tel₁ Tel₂ ha hb = some ⟨(μ (Tel₁ ++ Tel₂)) ^ C, .both ha hb hr⟩ := by
  simp [atomBoth, hr]

theorem atomUnfold_eq {Γ : Ctx s} {b : Atom s} {Tel : Telescope (s,x)} {C : CaptureSet s}
    (hb : Γ ⊢ₐ b : (μ Tel) ^ C) :
    atomUnfold hb = some ⟨(μ (Tel⟦b.root⟧)↑) ^ C, .unfoldSelf hb⟩ := rfl

theorem atomFold_eq {Γ : Ctx s} {b : Atom s} {Tel : Telescope (s,x)} {C : CaptureSet s}
    (hb : Γ ⊢ₐ b : (μ (Tel⟦b.root⟧)↑) ^ C) :
    atomFold Tel hb = some ⟨(μ Tel) ^ C, .foldSelf hb⟩ := by
  simp [atomFold]

theorem tmUnbox_eq {Γ : Ctx s} {a : Atom s} {f : CapCo s} {S : Shape s}
    {C D U : CaptureSet s} (ha : Γ ⊢ₐ a : (□ (S ^ C)) ^ D) (hf : Γ ⊢ᶜ f : C ⊑ U) :
    tmUnbox U ha hf = some ⟨.ty (S ^ C), .unbox ha hf⟩ := by
  simp [tmUnbox]

theorem tmApp_eq {Γ : Ctx s} {a b : Atom s} {C : CaptureSet s} {T : Dom s} {U : Cod s}
    (ha : Γ ⊢ₐ a : (Π(T) U) ^ C)
    (hb : Γ ⊢ₐ b : T.subst (Subst.singleC (CapAtom.var b.root))) :
    tmApp ha hb = some ⟨U.subst (Subst.arg b), .app ha hb⟩ := by
  simp [tmApp]

theorem capMember_eq {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} {i : Nat} {S : Shape s}
    {D : CaptureSet s} {C₁ C₂ : CaptureSet (s,x)} {Tel : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : S ^ D) (he : Γ ⊢ˢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.leC C₁ C₂)) :
    capMember i ha he = some ⟨C₁⟦a.root⟧, C₂⟦a.root⟧, .member ha he hAt⟩ := by
  simp [capMember, Telescope.getAt?_of_At hAt]

theorem capEqMember_eq {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} {i : Nat} {S : Shape s}
    {D : CaptureSet s} {C₁ C₂ : CaptureSet (s,x)} {Tel : Telescope (s,x)}
    (ha : Γ ⊢ₐ a : S ^ D) (he : Γ ⊢ˢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.eqC C₁ C₂)) :
    capEqMember i ha he = some ⟨C₁⟦a.root⟧, C₂⟦a.root⟧, .member ha he hAt⟩ := by
  simp [capEqMember, Telescope.getAt?_of_At hAt]

theorem capVar_eq {Γ : Ctx s} {a : Atom s} {S : Shape s} {C : CaptureSet s}
    (ha : Γ ⊢ₐ a : S ^ C) : capVar ha = ⟨[CapAtom.var a.root], C, .capvar ha⟩ := rfl

theorem atomRecap_eq {Γ : Ctx s} {a : Atom s} {f : CapCo s} {S : Shape s}
    {C C' : CaptureSet s} (ha : Γ ⊢ₐ a : S ^ C)
    (hf : Γ ⊢ᶜ f : [CapAtom.var a.root] ⊑ C') :
    atomRecap ha hf = some ⟨S ^ C', .recap ha hf⟩ := by
  simp [atomRecap]

theorem morEqC_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {C D : CaptureSet (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eqC C D)) :
    morEqC j false hm = some ⟨Tel ▹ C ≐ᶜ D, .eqC hm hAt⟩ := by
  simp [morEqC, Telescope.getAt?_of_At hAt]

theorem morEqSymC_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {C D : CaptureSet (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.eqC C D)) :
    morEqC j true hm = some ⟨Tel ▹ D ≐ᶜ C, .eqSymC hm hAt⟩ := by
  simp [morEqC, Telescope.getAt?_of_At hAt]

end Plumbing

/-! ## Completeness for evidence

The evidence judgements of the mutual block are proven by a single mutual
recursion on the derivation.  Every core synthesises, so each statement is an
equation: the kernel returns precisely the derivation's outputs. -/

mutual

/-- The kernel synthesises both capture sets of every capture-inclusion
derivation. -/
theorem CapCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ f : C ⊑ D), synthCapCore Γ f = some ⟨C, D, h⟩
  | _, _, _, _, _, .refl => by simp [synthCapCore]
  | _, _, _, _, _, .elem hs => by simp [synthCapCore, capElem_eq hs]
  | _, _, _, _, _, .trans hf hg => by
      simp [synthCapCore, CapCo.HasType.complete hf, CapCo.HasType.complete hg]
  | _, _, _, _, _, .union hf hg => by
      simp [synthCapCore, CapCo.HasType.complete hf, CapCo.HasType.complete hg]
  | _, _, _, _, _, .capvar ha => by
      simp [synthCapCore, Atom.HasType.complete ha, capVar_eq ha]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthCapCore, Atom.HasType.complete ha, ShapeCo.HasType.complete he,
        capMember_eq ha he hAt]
  | _, _, _, _, _, .eqToLe hφ => by
      simp [synthCapCore, CapEq.HasType.complete hφ]
  | _, _, _, _, _, .level h₁ h₂ => by
      simp [synthCapCore, h₁, h₂]

/-- The kernel synthesises both capture sets of every capture-equality
derivation. -/
theorem CapEq.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D), synthCapEqCore Γ φ = some ⟨C, D, h⟩
  | _, _, _, _, _, .refl => by simp [synthCapEqCore]
  | _, _, _, _, _, .symm hφ => by
      simp [synthCapEqCore, CapEq.HasType.complete hφ]
  | _, _, _, _, _, .trans hφ hψ => by
      simp [synthCapEqCore, CapEq.HasType.complete hφ, CapEq.HasType.complete hψ]
  | _, _, _, _, _, .defC hd => by
      simp [synthCapEqCore, witness?_eq_some hd]
  | _, _, _, _, _, .instC hI => by
      simp only [synthCapEqCore, dif_pos hI]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthCapEqCore, Atom.HasType.complete ha, ShapeCo.HasType.complete he,
        capEqMember_eq ha he hAt]

/-- The kernel accepts every `pre` capture chain at the endpoint next to its
hole, and synthesises the outer one. -/
theorem SideC.HasType.completePre : ∀ {s : Sig} {Γ : Ctx s} {q : SideC s}
    {X Y : CaptureSet (s,x)} (h : SideC.HasType Γ q X Y),
      checkPreCoreC Γ q Y = some ⟨X, h⟩
  | _, _, _, _, _, .nil => by simp [checkPreCoreC]
  | _, _, _, _, _, .cons (.closed hf) hq => by
      simp [checkPreCoreC, SideC.HasType.completePre hq, CapCo.HasType.complete hf]
  | _, _, _, _, _, .cons (.incl hs) hq => by
      simp [checkPreCoreC, SideC.HasType.completePre hq, hs]

/-- The same for `post` capture chains. -/
theorem SideC.HasType.completePost : ∀ {s : Sig} {Γ : Ctx s} {q : SideC s}
    {X Y : CaptureSet (s,x)} (h : SideC.HasType Γ q X Y),
      checkPostCoreC Γ q X = some ⟨Y, h⟩
  | _, _, _, _, _, .nil => by simp [checkPostCoreC]
  | _, _, _, _, _, .cons (.closed hf) hq => by
      simp [checkPostCoreC, CapCo.HasType.complete hf, SideC.HasType.completePost hq]
  | _, _, _, _, _, .cons (.incl hs) hq => by
      simp [checkPostCoreC, hs, SideC.HasType.completePost hq]

/-- The kernel synthesises the endpoints of every shape-inclusion derivation. -/
theorem ShapeCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T), synthShapeCore Γ e = some ⟨S, T, h⟩
  | _, _, _, _, _, .refl => by simp [synthShapeCore]
  | _, _, _, _, _, .top => by simp [synthShapeCore]
  | _, _, _, _, _, .bot => by simp [synthShapeCore]
  | _, _, _, _, _, .eqToLe hφ => by
      simp [synthShapeCore, EqCo.HasType.complete hφ]
  | _, _, _, _, _, .trans he hf => by
      simp [synthShapeCore, ShapeCo.HasType.complete he, ShapeCo.HasType.complete hf]
  | _, _, _, _, _, .pi he hf => by
      simp only [synthShapeCore]
      simp only [LeCo.HasType.complete he]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom, witness_underRootDom]
      simp only [witness?_some, Option.bind_eq_bind, Option.bind,
        ELeCo.HasType.complete hf]
      rw [witness_underRootCod, witness_underRootCod]
  | _, _, _, _, _, .obj hm => by
      simp [synthShapeCore, Morphism.HasType.complete hm]
  | _, _, _, _, _, .pair he hf => by
      simp [synthShapeCore, ShapeCo.HasType.complete he, ShapeCo.HasType.complete hf,
        lePair_eq he hf]
  | _, _, _, _, _, .bound hAt => by
      simp [synthShapeCore, leBound_eq hAt]
  | _, _, _, _, _, .intoBnd he => by
      simp [synthShapeCore, ShapeCo.HasType.complete he]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthShapeCore, Atom.HasType.complete ha, ShapeCo.HasType.complete he,
        leMember_eq ha he hAt]
  | _, _, _, _, _, .boxed hd => by
      simp [synthShapeCore, LeCo.HasType.complete hd]

/-- The kernel synthesises the endpoints of every type-inclusion derivation. -/
theorem LeCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {d : LeCo s} {S T : Ty s}
    (h : Γ ⊢ d : S ≤ T), synthLeCore Γ d = some ⟨S, T, h⟩
  | _, _, _, _, _, .capt he hf => by
      simp [synthLeCore, ShapeCo.HasType.complete he, CapCo.HasType.complete hf]

/-- The kernel synthesises the endpoints of every equality derivation. -/
theorem EqCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {φ : EqCo s} {S T : Shape s}
    (h : Γ ⊢ φ : S ≡ T), synthEqCore Γ φ = some ⟨S, T, h⟩
  | _, _, _, _, _, .refl => by simp [synthEqCore]
  | _, _, _, _, _, .symm hφ => by
      simp [synthEqCore, EqCo.HasType.complete hφ]
  | _, _, _, _, _, .trans hφ hψ => by
      simp [synthEqCore, EqCo.HasType.complete hφ, EqCo.HasType.complete hψ]
  | _, _, _, _, _, .def hd => by
      simp [synthEqCore, witness?_eq_some hd]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthEqCore, Atom.HasType.complete ha, ShapeCo.HasType.complete he,
        eqMember_eq ha he hAt]

/-- The kernel synthesises the label of every field-presence derivation. -/
theorem Has.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {hv : Has s} {y : BVar s .var} {ℓ : Label}
    (h : Has.HasType Γ hv y ℓ), synthHasCore Γ hv y = some ⟨ℓ, h⟩
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthHasCore, Atom.HasType.complete ha, ShapeCo.HasType.complete he,
        hasMember_eq ha he hAt]
  | _, _, _, _, _, .field hf hm => by
      simp [synthHasCore, witness?_eq_some hf, hm]

/-- The kernel accepts every `pre` side at the endpoint next to its hole, and
synthesises the outer one. -/
theorem Side.HasType.completePre : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {S X : Shape (s,x)}
    (h : Side.HasType Γ side S X), checkPreCore Γ side X = some ⟨S, h⟩
  | _, _, _, _, _, .none => by simp [checkPreCore]
  | _, _, _, _, _, .some he => by
      simp [checkPreCore, ShapeCo.HasType.complete he]

/-- The same for `post` sides. -/
theorem Side.HasType.completePost : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {Y T : Shape (s,x)}
    (h : Side.HasType Γ side Y T), checkPostCore Γ side Y = some ⟨T, h⟩
  | _, _, _, _, _, .none => by simp [checkPostCore]
  | _, _, _, _, _, .some he => by
      simp [checkPostCore, ShapeCo.HasType.complete he]

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
  | _, _, _, _, _, .bnd hm he => by
      simp [synthMorCore, Morphism.HasType.complete hm, ShapeCo.HasType.complete he,
        morBnd_eq hm he]
  | _, _, _, _, _, .leC hm hh hq hq' => by
      simp [synthMorCore, Morphism.HasType.complete hm, HoleC.read?_of_HoleAtC hh,
        SideC.HasType.completePre hq, SideC.HasType.completePost hq']
  | _, _, _, _, _, .eqC hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morEqC_eq hm hAt]
  | _, _, _, _, _, .eqSymC hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morEqSymC_eq hm hAt]

/-- The kernel synthesises the type of every atom derivation. -/
theorem Atom.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T), synthAtomCore Γ a = some ⟨T, h⟩
  | _, _, _, _, .var => by simp [synthAtomCore]
  | _, _, _, _, .cast hb he => by
      simp [synthAtomCore, Atom.HasType.complete hb, LeCo.HasType.complete he]
  | _, _, _, _, .unfoldSelf hb => by
      simp [synthAtomCore, Atom.HasType.complete hb, atomUnfold_eq hb]
  | _, _, _, _, .foldSelf hb => by
      simp [synthAtomCore, Atom.HasType.complete hb, atomFold_eq hb]
  | _, _, _, _, .both ha hb hr => by
      simp [synthAtomCore, Atom.HasType.complete ha, Atom.HasType.complete hb,
        atomBoth_eq ha hb hr]
  | _, _, _, _, .recap ha hf => by
      simp [synthAtomCore, Atom.HasType.complete ha, CapCo.HasType.complete hf,
        atomRecap_eq ha hf]

theorem ELeCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s}
    (h : Γ ⊢ᵉ g : E ≤ E'), synthELeCore Γ g = some ⟨E, E', h⟩
  | _, _, _, _, _, .plain he => by
      simp [synthELeCore, LeCo.HasType.complete he]
  | _, _, _, _, _, .pack hc he => by
      simp only [synthELeCore, CapCo.HasType.complete hc, LeCo.HasType.complete he,
        Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom]
      simp only [witness?_some, Option.bind_eq_bind, Option.bind]
      rw [Ty.strengthenC2?_weaken]
      simp
  | _, _, _, _, _, .cong hc he => by
      simp only [synthELeCore, CapCo.HasType.complete hc, LeCo.HasType.complete he,
        Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom, witness_underRootDom]
  | _, _, _, _, _, .trans hg hh => by
      simp [synthELeCore, ELeCo.HasType.complete hg, ELeCo.HasType.complete hh]

end

/-- The packed-atom wrapper premises only judgments of the block above. -/
theorem PAtom.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {p : PAtom s} {E : ETy s}
    (h : Γ ⊢ₚ p : E), synthPAtomCore Γ p = some ⟨E, h⟩
  | _, _, _, _, .plain ha => by
      simp [synthPAtomCore, Atom.HasType.complete ha]
  | _, _, _, _, .pack ha hc he => by
      simp only [synthPAtomCore, Atom.HasType.complete ha, CapCo.HasType.complete hc,
        LeCo.HasType.complete he, Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom]
      simp

/-! ## Completeness for terms

Terms, values and field blocks form the second mutual family.  Every rule of
this layer carries the evidence its premises need, so the statements are again
plain equations, with no side condition. -/

mutual

/-- The kernel synthesises the type of every term derivation. -/
theorem Tm.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {E : ETy s}
    (h : Γ ⊢ t :ᵉ E), synthTmCore Γ t = some ⟨E, h⟩
  | _, _, _, _, .atom ha => by
      simp [synthTmCore, PAtom.HasType.complete ha]
  | _, _, .val (.lam _ _ _ _), _, .val (.plain hv') => by
      simp [synthTmCore, Value.HasType.complete hv']
  | _, _, .val (.obj _ _ _ _), _, .val (.plain hv') => by
      simp [synthTmCore, Value.HasType.complete hv']
  | _, _, .val (.box _), _, .val (.plain hv') => by
      simp [synthTmCore, Value.HasType.complete hv']
  | _, _, .val (.cast _ _), _, .val (.plain hv') => by
      simp [synthTmCore, Value.HasType.complete hv']
  | _, _, .val (.pack _ _ _ _), _, .val (.pack hv' hc he) => by
      simp only [synthTmCore, Value.HasType.complete hv', CapCo.HasType.complete hc,
        LeCo.HasType.complete he, Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom]
      simp
  | _, _, _, _, .app ha hb => by
      simp [synthTmCore, Atom.HasType.complete ha, Atom.HasType.complete hb, tmApp_eq ha hb]
  | _, _, _, _, .proj ha hh => by
      simp [synthTmCore, Atom.HasType.complete ha, Has.HasType.complete hh]
  | _, _, _, _, .let ht hu hf => by
      simp [synthTmCore, Tm.HasType.complete ht, Tm.HasType.complete hu,
        CapCo.HasType.complete hf, ETy.strengthenW?_weaken]
  | _, _, _, _, .cast ht he => by
      simp [synthTmCore, Tm.HasType.complete ht, LeCo.HasType.complete he]
  | _, _, _, _, .castE ht hg => by
      simp [synthTmCore, Tm.HasType.complete ht, ELeCo.HasType.complete hg]
  | _, _, _, _, .letex ht hc hu hf => by
      simp [synthTmCore, Tm.HasType.complete ht, CapCo.HasType.complete hc,
        Tm.HasType.complete hu, CapCo.HasType.complete hf, ETy.strengthenVC2?_weaken]
  | _, _, _, _, .unbox ha hf => by
      simp [synthTmCore, Atom.HasType.complete ha, CapCo.HasType.complete hf,
        tmUnbox_eq ha hf]

/-- The kernel synthesises the type of every value derivation. -/
theorem Value.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T), synthValueCore Γ v = some ⟨T, h⟩
  | _, _, _, _, .lam ht hg => by
      simp only [synthValueCore, Tm.HasType.complete ht, Option.bind_eq_bind, Option.bind]
      rw [witness_underRootCod]
      simp [CapCo.HasType.complete hg]
  | _, _, _, _, .obj hF => by
      simp [synthValueCore, Fields.HasType.complete hF]
  | _, _, _, _, .box ha => by
      simp [synthValueCore, Atom.HasType.complete ha, valueBox]
  | _, _, _, _, .cast hv he => by
      simp [synthValueCore, Value.HasType.complete hv, LeCo.HasType.complete he]

/-- The kernel accepts every field block derivation. -/
theorem Fields.HasType.complete : ∀ {s : Sig} {Γ : Ctx (s,x)} {A : CaptureSet s}
    {F : Fields (s,x)}
    (h : Γ ⊢ᶠ[A] F), checkFieldsCore A Γ F = some ⟨h⟩
  | _, _, _, _, .nil => by simp [checkFieldsCore]
  | _, _, _, _, .cons hF ht hg => by
      simp [checkFieldsCore, Fields.HasType.complete hF, Tm.HasType.complete ht,
        CapCo.HasType.complete hg]

end

/-- Values at the answer sort.  A packed value is never `plain`, because
`Value.HasType` has no `pack` rule. -/
theorem Value.HasTypeE.complete : ∀ {s : Sig} {Γ : Ctx s} {v : Value s} {E : ETy s}
    (h : Γ ⊢ᵥᵉ v : E), synthValueECore Γ v = some ⟨E, h⟩
  | _, _, .lam _ _ _ _, _, .plain hv => by
      simp [synthValueECore, Value.HasType.complete hv]
  | _, _, .obj _ _ _ _, _, .plain hv => by
      simp [synthValueECore, Value.HasType.complete hv]
  | _, _, .box _, _, .plain hv => by
      simp [synthValueECore, Value.HasType.complete hv]
  | _, _, .cast _ _, _, .plain hv => by
      simp [synthValueECore, Value.HasType.complete hv]
  | _, _, .pack _ _ _ _, _, .pack hv hc he => by
      simp only [synthValueECore, Value.HasType.complete hv, CapCo.HasType.complete hc,
        LeCo.HasType.complete he, Option.bind_eq_bind, Option.bind]
      rw [witness_underRootDom]
      simp


/-! ## Public interface

Soundness lives in `Coercions.CapturesCC.FCdot.Checker`; here it is paired with
completeness into decision procedures. -/

section Public
variable {s : Sig}

theorem synthShape_complete {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s} (h : Γ ⊢ˢ e : S ≤ T) :
    synthShape Γ e = some (S, T) := by
  simp [synthShape, ShapeCo.HasType.complete h]

theorem synthShape_iff {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s} :
    synthShape Γ e = some (S, T) ↔ Γ ⊢ˢ e : S ≤ T :=
  ⟨synthShape_sound, synthShape_complete⟩

theorem checkShape_complete {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s} (h : Γ ⊢ˢ e : S ≤ T) :
    checkShape Γ e S T = true :=
  decide_eq_true (synthShape_complete h)

theorem checkShape_iff {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s} :
    checkShape Γ e S T = true ↔ Γ ⊢ˢ e : S ≤ T :=
  ⟨checkShape_sound, checkShape_complete⟩

theorem synthCap_complete {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s} (h : Γ ⊢ᶜ f : C ⊑ D) :
    synthCap Γ f = some (C, D) := by
  simp [synthCap, CapCo.HasType.complete h]

theorem synthCap_iff {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s} :
    synthCap Γ f = some (C, D) ↔ Γ ⊢ᶜ f : C ⊑ D :=
  ⟨synthCap_sound, synthCap_complete⟩

theorem checkCap_complete {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s} (h : Γ ⊢ᶜ f : C ⊑ D) :
    checkCap Γ f C D = true :=
  decide_eq_true (synthCap_complete h)

theorem checkCap_iff {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s} :
    checkCap Γ f C D = true ↔ Γ ⊢ᶜ f : C ⊑ D :=
  ⟨checkCap_sound, checkCap_complete⟩

theorem synthCapEq_complete {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) : synthCapEq Γ φ = some (C, D) := by
  simp [synthCapEq, CapEq.HasType.complete h]

theorem synthCapEq_iff {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s} :
    synthCapEq Γ φ = some (C, D) ↔ Γ ⊢ᶜ φ : C ≡ D :=
  ⟨synthCapEq_sound, synthCapEq_complete⟩

theorem checkCapEq_complete {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) : checkCapEq Γ φ C D = true :=
  decide_eq_true (synthCapEq_complete h)

theorem checkCapEq_iff {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s} :
    checkCapEq Γ φ C D = true ↔ Γ ⊢ᶜ φ : C ≡ D :=
  ⟨checkCapEq_sound, checkCapEq_complete⟩

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

theorem synthEq_complete {Γ : Ctx s} {φ : EqCo s} {S T : Shape s} (h : Γ ⊢ φ : S ≡ T) :
    synthEq Γ φ = some (S, T) := by
  simp [synthEq, EqCo.HasType.complete h]

theorem synthEq_iff {Γ : Ctx s} {φ : EqCo s} {S T : Shape s} :
    synthEq Γ φ = some (S, T) ↔ Γ ⊢ φ : S ≡ T :=
  ⟨synthEq_sound, synthEq_complete⟩

theorem checkEq_complete {Γ : Ctx s} {φ : EqCo s} {S T : Shape s} (h : Γ ⊢ φ : S ≡ T) :
    checkEq Γ φ S T = true :=
  decide_eq_true (synthEq_complete h)

theorem checkEq_iff {Γ : Ctx s} {φ : EqCo s} {S T : Shape s} :
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

theorem synthTmE_complete {Γ : Ctx s} {t : Tm s} {E : ETy s} (h : Γ ⊢ t :ᵉ E) :
    synthTmE Γ t = some E := by
  simp [synthTmE, Tm.HasType.complete h]

theorem synthTmE_iff {Γ : Ctx s} {t : Tm s} {E : ETy s} :
    synthTmE Γ t = some E ↔ Γ ⊢ t :ᵉ E :=
  ⟨synthTmE_sound, synthTmE_complete⟩

theorem checkTmE_complete {Γ : Ctx s} {t : Tm s} {E : ETy s} (h : Γ ⊢ t :ᵉ E) :
    checkTmE Γ t E = true :=
  decide_eq_true (synthTmE_complete h)

theorem checkTmE_iff {Γ : Ctx s} {t : Tm s} {E : ETy s} :
    checkTmE Γ t E = true ↔ Γ ⊢ t :ᵉ E :=
  ⟨checkTmE_sound, checkTmE_complete⟩

theorem synthTm_complete {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : Γ ⊢ t : T) :
    synthTm Γ t = some T := by
  simp [synthTm, synthTmE_complete h]

theorem synthTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} :
    synthTm Γ t = some T ↔ Γ ⊢ t : T :=
  ⟨synthTm_sound, synthTm_complete⟩

theorem checkTm_complete {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : Γ ⊢ t : T) :
    checkTm Γ t T = true :=
  checkTmE_complete h

theorem checkTm_iff {Γ : Ctx s} {t : Tm s} {T : Ty s} :
    checkTm Γ t T = true ↔ Γ ⊢ t : T :=
  ⟨checkTm_sound, checkTm_complete⟩

theorem synthPAtom_complete {Γ : Ctx s} {p : PAtom s} {E : ETy s} (h : Γ ⊢ₚ p : E) :
    synthPAtom Γ p = some E := by
  simp [synthPAtom, PAtom.HasType.complete h]

theorem synthPAtom_iff {Γ : Ctx s} {p : PAtom s} {E : ETy s} :
    synthPAtom Γ p = some E ↔ Γ ⊢ₚ p : E :=
  ⟨synthPAtom_sound, synthPAtom_complete⟩

theorem checkPAtom_complete {Γ : Ctx s} {p : PAtom s} {E : ETy s} (h : Γ ⊢ₚ p : E) :
    checkPAtom Γ p E = true :=
  decide_eq_true (synthPAtom_complete h)

theorem checkPAtom_iff {Γ : Ctx s} {p : PAtom s} {E : ETy s} :
    checkPAtom Γ p E = true ↔ Γ ⊢ₚ p : E :=
  ⟨checkPAtom_sound, checkPAtom_complete⟩

theorem synthELe_complete {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s} (h : Γ ⊢ᵉ g : E ≤ E') :
    synthELe Γ g = some (E, E') := by
  simp [synthELe, ELeCo.HasType.complete h]

theorem synthELe_iff {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s} :
    synthELe Γ g = some (E, E') ↔ Γ ⊢ᵉ g : E ≤ E' :=
  ⟨synthELe_sound, synthELe_complete⟩

theorem checkELe_complete {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s} (h : Γ ⊢ᵉ g : E ≤ E') :
    checkELe Γ g E E' = true :=
  decide_eq_true (synthELe_complete h)

theorem checkELe_iff {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s} :
    checkELe Γ g E E' = true ↔ Γ ⊢ᵉ g : E ≤ E' :=
  ⟨checkELe_sound, checkELe_complete⟩

theorem synthValueE_complete {Γ : Ctx s} {v : Value s} {E : ETy s} (h : Γ ⊢ᵥᵉ v : E) :
    synthValueE Γ v = some E := by
  simp [synthValueE, Value.HasTypeE.complete h]

theorem synthValueE_iff {Γ : Ctx s} {v : Value s} {E : ETy s} :
    synthValueE Γ v = some E ↔ Γ ⊢ᵥᵉ v : E :=
  ⟨synthValueE_sound, synthValueE_complete⟩

theorem checkValueE_complete {Γ : Ctx s} {v : Value s} {E : ETy s} (h : Γ ⊢ᵥᵉ v : E) :
    checkValueE Γ v E = true :=
  decide_eq_true (synthValueE_complete h)

theorem checkValueE_iff {Γ : Ctx s} {v : Value s} {E : ETy s} :
    checkValueE Γ v E = true ↔ Γ ⊢ᵥᵉ v : E :=
  ⟨checkValueE_sound, checkValueE_complete⟩

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

theorem checkFields_complete {Γ : Ctx (s,x)} {A : CaptureSet s} {F : Fields (s,x)}
    (h : Γ ⊢ᶠ[A] F) : checkFields A Γ F = true := by
  simp [checkFields, Fields.HasType.complete h]

theorem checkFields_iff {Γ : Ctx (s,x)} {A : CaptureSet s} {F : Fields (s,x)} :
    checkFields A Γ F = true ↔ Γ ⊢ᶠ[A] F :=
  ⟨checkFields_sound, checkFields_complete⟩

end Public

/-! ## Determinism

Synthesis is a function, so the evidence layer pins its outputs down with no
hypothesis whatsoever: this is the determinism that makes the checking modes
sound to implement by synthesis and comparison. -/

section Determinism
variable {s : Sig}

theorem ShapeCo.HasType.endpoints_unique {Γ : Ctx s} {e : ShapeCo s} {S T S' T' : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T) (h' : Γ ⊢ˢ e : S' ≤ T') : S = S' ∧ T = T' := by
  have := (synthShape_complete h).symm.trans (synthShape_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem CapCo.HasType.endpoints_unique {Γ : Ctx s} {f : CapCo s} {C D C' D' : CaptureSet s}
    (h : Γ ⊢ᶜ f : C ⊑ D) (h' : Γ ⊢ᶜ f : C' ⊑ D') : C = C' ∧ D = D' := by
  have := (synthCap_complete h).symm.trans (synthCap_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem CapEq.HasType.endpoints_unique {Γ : Ctx s} {φ : CapEq s} {C D C' D' : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) (h' : Γ ⊢ᶜ φ : C' ≡ D') : C = C' ∧ D = D' := by
  have := (synthCapEq_complete h).symm.trans (synthCapEq_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem LeCo.HasType.endpoints_unique {Γ : Ctx s} {e : LeCo s} {S T S' T' : Ty s}
    (h : Γ ⊢ e : S ≤ T) (h' : Γ ⊢ e : S' ≤ T') : S = S' ∧ T = T' := by
  have := (synthLe_complete h).symm.trans (synthLe_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem EqCo.HasType.endpoints_unique {Γ : Ctx s} {φ : EqCo s} {S T S' T' : Shape s}
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

The term layer is deterministic as well.  Synthesis is a function and it is
complete, so each of the four judgments below pins its output down with no
hypothesis whatsoever. -/

theorem Tm.HasType.type_unique {s : Sig} {Γ : Ctx s} {t : Tm s} {E E' : ETy s}
    (h : Γ ⊢ t :ᵉ E) (h' : Γ ⊢ t :ᵉ E') : E = E' := by
  have hh := (Tm.HasType.complete h).symm.trans (Tm.HasType.complete h')
  simp only [Option.some.injEq, TmChecked.mk.injEq] at hh
  exact hh

theorem Value.HasType.type_unique {s : Sig} {Γ : Ctx s} {v : Value s} {T T' : Ty s}
    (h : Γ ⊢ᵥ v : T) (h' : Γ ⊢ᵥ v : T') : T = T' := by
  have hh := (Value.HasType.complete h).symm.trans (Value.HasType.complete h')
  simp only [Option.some.injEq, ValueChecked.mk.injEq] at hh
  exact hh

theorem PAtom.HasType.type_unique {s : Sig} {Γ : Ctx s} {p : PAtom s} {E E' : ETy s}
    (h : Γ ⊢ₚ p : E) (h' : Γ ⊢ₚ p : E') : E = E' := by
  have hh := (PAtom.HasType.complete h).symm.trans (PAtom.HasType.complete h')
  simp only [Option.some.injEq, PAtomChecked.mk.injEq] at hh
  exact hh

theorem Value.HasTypeE.type_unique {s : Sig} {Γ : Ctx s} {v : Value s} {E E' : ETy s}
    (h : Γ ⊢ᵥᵉ v : E) (h' : Γ ⊢ᵥᵉ v : E') : E = E' := by
  have hh := (Value.HasTypeE.complete h).symm.trans (Value.HasTypeE.complete h')
  simp only [Option.some.injEq, ValueEChecked.mk.injEq] at hh
  exact hh

theorem ELeCo.HasType.endpoints_unique {s : Sig} {Γ : Ctx s} {g : ELeCo s}
    {E E' F F' : ETy s} (h : Γ ⊢ᵉ g : E ≤ F) (h' : Γ ⊢ᵉ g : E' ≤ F') : E = E' ∧ F = F' := by
  have hh := (synthELe_complete h).symm.trans (synthELe_complete h')
  simp only [Option.some.injEq, Prod.mk.injEq] at hh
  exact hh

end FCdot

end CapturesCC
