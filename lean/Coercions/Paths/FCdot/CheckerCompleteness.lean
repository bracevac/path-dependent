import Coercions.Paths.FCdot.Checker
import Coercions.Paths.FCdot.Transparency

namespace Paths

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

theorem leMemberP_eq {Γ : Ctx s} {P : PathCo s} {e : LeCo s} {i : Nat} {S : Ty s}
    {S' T' : Ty (s,x)} {Tel : Telescope (s,x)} (hP : Γ ⊢ᵖ P : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.le S' T')) :
    leMemberP i hP he = some ⟨S'.substPath P.path, T'.substPath P.path, .memberP hP he hAt⟩ := by
  simp [leMemberP, Telescope.getAt?_of_At hAt]

theorem eqMemberP_eq {Γ : Ctx s} {P : PathCo s} {e : LeCo s} {i : Nat} {S : Ty s}
    {S' T' : Ty (s,x)} {Tel : Telescope (s,x)} (hP : Γ ⊢ᵖ P : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.eq S' T')) :
    eqMemberP i hP he = some ⟨S'.substPath P.path, T'.substPath P.path, .memberP hP he hAt⟩ := by
  simp [eqMemberP, Telescope.getAt?_of_At hAt]

theorem hasMemberP_eq {Γ : Ctx s} {P : PathCo s} {e : LeCo s} {i : Nat} {S : Ty s} {ℓ : Label}
    {Tel : Telescope (s,x)} (hP : Γ ⊢ᵖ P : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.has ℓ)) :
    hasMemberP i P.path hP he = some ⟨ℓ, .memberP hP he hAt⟩ := by
  simp [hasMemberP, Telescope.getAt?_of_At hAt]

theorem aliasMember_eq {Γ : Ctx s} {P : PathCo s} {e : LeCo s} {i : Nat} {S : Ty s}
    {q : Path (s,x)} {Tel : Telescope (s,x)} (hP : Γ ⊢ᵖ P : S) (he : Γ ⊢ e : S ≤ .obj Tel)
    (hAt : Tel.At i (.alias q)) :
    aliasMember i hP he = some ⟨P.path, q.substPath P.path, .member hP he hAt⟩ := by
  simp [aliasMember, Telescope.getAt?_of_At hAt]

theorem pathSel_eq {Γ : Ctx s} {P : PathCo s} {a : Label} {i : Nat}
    {Tel : Telescope (s,x)} (hP : Γ ⊢ᵖ P : .obj Tel) (hAt : Tel.At i (.hasVal a)) :
    pathSel a i hP = some ⟨P.path ∙ a, .sel hP hAt⟩ := by
  simp [pathSel, Telescope.getAt?_of_At hAt]

theorem pathNode_eq {Γ : Ctx s} {p : Path s} {W : Witnesses (s,x)} {ls vls : List Label}
    {ch : Children s} (hs : p.isSel = true)
    (hn : Γ.nodeBlock p = some (.obj (W.substPath p) ls vls ch)) :
    pathNode Γ p W ls vls = some ⟨μ (Telescope.ofLiteral W ls vls), .node hs hn⟩ := by
  unfold pathNode
  rw [dif_pos hs]
  split
  · next W' ls' vls' ch' h =>
      rw [hn] at h
      simp only [Option.some.injEq, Block.obj.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp
  · next h => rw [hn] at h; exact absurd rfl (h _ _ _ _)

theorem morHasVal_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat} {ℓ : Label}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) (hAt : src.At j (.hasVal ℓ)) :
    morHasVal j hm = some ⟨Tel ▹ ∋ᵛ ℓ, .hasVal hm hAt⟩ := by
  simp [morHasVal, Telescope.getAt?_of_At hAt]

theorem morHasOfVal_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat} {ℓ : Label}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) (hAt : src.At j (.hasVal ℓ)) :
    morHasOfVal j hm = some ⟨Tel ▹ ∋ ℓ, .hasOfVal hm hAt⟩ := by
  simp [morHasOfVal, Telescope.getAt?_of_At hAt]

theorem morAliasCopy_eq {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {j : Nat}
    {q : Path (s,x)} {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel)
    (hAt : src.At j (.alias q)) :
    morAliasCopy j hm = some ⟨Tel ▹ ≈ q, .aliasCopy hm hAt⟩ := by
  simp [morAliasCopy, Telescope.getAt?_of_At hAt]

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

theorem leBound_eq {Γ : Ctx s} {Tel : Telescope (s,x)} {i : Nat} {T : Ty s}
    (hAt : Tel ∋ (i ↦ ⊑ T↑)) :
    leBound (Γ := Γ) Tel i = some ⟨μ Tel, T, .bound hAt⟩ := by
  simp [leBound, Telescope.getAt?_of_At hAt, Ty.strengthenW?_weaken]

theorem morBnd_eq {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s} {e : LeCo s}
    {T : Ty s} (hm : Γ ⊢ m : src ⇒ Tel) (he : Γ ⊢ e : μ src ≤ T) :
    morBnd hm he = some ⟨Tel ▹ ⊑ T↑, .bnd hm he⟩ := by
  simp [morBnd]

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
  | _, _, _, _, _, .bound hAt => by
      simp [synthLeCore, leBound_eq hAt]
  | _, _, _, _, _, .intoBnd he => by
      simp [synthLeCore, LeCo.HasType.complete he]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthLeCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        leMember_eq ha he hAt]
  | _, _, _, _, _, .memberP hP he hAt => by
      simp [synthLeCore, PathCo.HasType.complete hP, LeCo.HasType.complete he,
        leMemberP_eq hP he hAt]

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
  | _, _, _, _, _, .defP hd => by
      simp [synthEqCore, witness?_eq_some hd]
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthEqCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        eqMember_eq ha he hAt]
  | _, _, _, _, _, .memberP hP he hAt => by
      simp [synthEqCore, PathCo.HasType.complete hP, LeCo.HasType.complete he,
        eqMemberP_eq hP he hAt]

/-- The kernel synthesises the label of every field-presence derivation. -/
theorem Has.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {hv : Has s} {y : Path s} {ℓ : Label}
    (h : Has.HasType Γ hv y ℓ), synthHasCore Γ hv y = some ⟨ℓ, h⟩
  | _, _, _, _, _, .member ha he hAt => by
      simp [synthHasCore, Atom.HasType.complete ha, LeCo.HasType.complete he,
        hasMember_eq ha he hAt]
  | _, _, _, _, _, .memberP hP he hAt => by
      simp [synthHasCore, PathCo.HasType.complete hP, LeCo.HasType.complete he,
        hasMemberP_eq hP he hAt]
  | _, _, _, _, _, .field hf hm => by
      simp [synthHasCore, witness?_eq_some hf, hm]

/-- The kernel accepts every `pre` side at the endpoint next to its hole, and
synthesises the outer one. -/
theorem Side.HasType.completePre : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {S X : Ty (s,x)}
    (h : Side.HasType Γ side S X), checkPreCore Γ side X = some ⟨S, h⟩
  | _, _, _, _, _, .none => by simp [checkPreCore]
  | _, _, _, _, _, .bot => by simp [checkPreCore]
  | _, _, _, _, _, .top => by simp [checkPreCore]
  | _, _, _, _, _, .some he => by
      simp [checkPreCore, LeCo.HasType.complete he]

/-- The same for `post` sides. -/
theorem Side.HasType.completePost : ∀ {s : Sig} {Γ : Ctx s} {side : Side s} {Y T : Ty (s,x)}
    (h : Side.HasType Γ side Y T), checkPostCore Γ side Y = some ⟨T, h⟩
  | _, _, _, _, _, .none => by simp [checkPostCore]
  | _, _, _, _, _, .bot => by simp [checkPostCore]
  | _, _, _, _, _, .top => by simp [checkPostCore]
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
  | _, _, _, _, _, .bnd hm he => by
      simp [synthMorCore, Morphism.HasType.complete hm, LeCo.HasType.complete he,
        morBnd_eq hm he]
  | _, _, _, _, _, .hasVal hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morHasVal_eq hm hAt]
  | _, _, _, _, _, .hasOfVal hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morHasOfVal_eq hm hAt]
  | _, _, _, _, _, .aliasCopy hm hAt => by
      simp [synthMorCore, Morphism.HasType.complete hm, morAliasCopy_eq hm hAt]

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
  | _, _, _, _, .sngl hb hα => by
      simp [synthAtomCore, Atom.HasType.complete hb, AliasCo.HasType.complete hα]

/-- The kernel synthesises the type of every stable-path derivation. -/
theorem PathCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {P : PathCo s} {T : Ty s}
    (h : Γ ⊢ᵖ P : T), synthPathCore Γ P = some ⟨T, h⟩
  | _, _, _, _, .var => by simp [synthPathCore]
  | _, _, _, _, .sel hP hAt => by
      simp [synthPathCore, PathCo.HasType.complete hP, pathSel_eq hP hAt]
  | _, _, _, _, .cast hQ he => by
      simp [synthPathCore, PathCo.HasType.complete hQ, LeCo.HasType.complete he]
  | _, _, _, _, .alias hα hQ => by
      simp [synthPathCore, AliasCo.HasType.complete hα, PathCo.HasType.complete hQ]
  | _, _, _, _, .unfoldSelf hQ => by
      simp [synthPathCore, PathCo.HasType.complete hQ]
  | _, _, _, _, .foldSelf hQ => by
      simp [synthPathCore, PathCo.HasType.complete hQ]
  | _, _, _, _, .both hQ hR hr => by
      simp [synthPathCore, PathCo.HasType.complete hQ, PathCo.HasType.complete hR, hr]
  | _, _, _, _, .sngl hQ hα => by
      simp [synthPathCore, PathCo.HasType.complete hQ, AliasCo.HasType.complete hα]
  | _, _, _, _, .node hs hn => by
      simp [synthPathCore, pathNode_eq hs hn]

/-- The kernel synthesises both paths of every alias derivation. -/
theorem AliasCo.HasType.complete : ∀ {s : Sig} {Γ : Ctx s} {α : AliasCo s} {p q : Path s}
    (h : Γ ⊢ α : p ≋ q), synthAliasCore Γ α = some ⟨p, q, h⟩
  | _, _, _, _, _, .refl => by simp [synthAliasCore]
  | _, _, _, _, _, .symm hβ => by
      simp [synthAliasCore, AliasCo.HasType.complete hβ]
  | _, _, _, _, _, .trans hβ hγ => by
      simp [synthAliasCore, AliasCo.HasType.complete hβ, AliasCo.HasType.complete hγ]
  | _, _, _, _, _, .sel hβ => by
      simp [synthAliasCore, AliasCo.HasType.complete hβ]
  | _, _, _, _, _, .member hP he hAt => by
      simp [synthAliasCore, PathCo.HasType.complete hP, LeCo.HasType.complete he,
        aliasMember_eq hP he hAt]

end

/-! ## Completeness for terms

Terms, values and field blocks form the second mutual family.  Every rule of
this layer carries the evidence its premises need, so the statements are again
plain equations, with no side condition. -/

mutual

/-- The body of a `Tm.HasType.let` derivation is typed under the binder the
checker picks: an opaque binder knows nothing, so any binder of its type
refines it. -/
theorem Tm.HasType.forLet_body {s : Sig} {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)} {U : Ty (s,x)}
    (hu : Γ.cons (.opaque T) ⊢ u : U) : Γ.cons (Binding.forLet T) ⊢ u : U :=
  hu.refine (by
    have hr := Ctx.Refines.ofOpaque (Γ := Γ) (Binding.forLet T)
    rwa [Binding.ty_forLet] at hr)

/-- The binder the checker picks at a singleton is the forwarding binder. -/
theorem Binding.forLet_snglOf {s : Sig} (q : Path s) :
    Binding.forLet (Ty.snglOf q) = Binding.fwdAt q := by
  simp [Binding.forLet, Ty.sngl?_snglOf]

/-- The body of a `Tm.HasType.letPath` derivation is already typed under the
binder the checker picks. -/
theorem Tm.HasType.forLet_body_sngl {s : Sig} {Γ : Ctx s} {q : Path s} {u : Tm (s,x)}
    {U : Ty (s,x)} (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U) :
    Γ.cons (Binding.forLet (Ty.snglOf q)) ⊢ u : U := by
  rw [Binding.forLet_snglOf]; exact hu

/-- The kernel synthesises the type of every term derivation.  The recursion is
on the term and not on the derivation: at a `let` whose term has a singleton
type the checker takes the forwarding binder, and the body of a
`Tm.HasType.let` derivation is carried there by `Ctx.Refines.ofOpaque` before
the recursive call.  That call is on the same body, which is a strict subterm
of the `let`, so the measure is the term. -/
theorem Tm.HasType.complete {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T) : synthTmCore Γ t = some ⟨T, h⟩ := by
  match t, h with
  | _, .atom ha => simp [synthTmCore, Atom.HasType.complete ha]
  | _, .val hv => simp [synthTmCore, Value.HasType.complete hv]
  | _, .app ha hb =>
      simp [synthTmCore, Atom.HasType.complete ha, Atom.HasType.complete hb, tmApp_eq ha hb]
  | _, .proj ha hh =>
      simp [synthTmCore, Atom.HasType.complete ha, Has.HasType.complete hh]
  | .let t0 u0, .let ht hu =>
      have hu' := Tm.HasType.forLet_body hu
      simp [synthTmCore, Tm.HasType.complete ht, Tm.HasType.complete hu',
        Ty.strengthenW?_weaken]
  | .let t0 u0, .letPath ht hu =>
      have hu' := Tm.HasType.forLet_body_sngl hu
      simp [synthTmCore, Tm.HasType.complete ht, Tm.HasType.complete hu',
        Ty.strengthenW?_weaken]
  | _, .cast ht he =>
      simp [synthTmCore, Tm.HasType.complete ht, LeCo.HasType.complete he]
termination_by sizeOf t

/-- The kernel synthesises the type of every value derivation. -/
theorem Value.HasType.complete {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) : synthValueCore Γ v = some ⟨T, h⟩ := by
  match v, h with
  | _, .lam ht => simp [synthValueCore, Tm.HasType.complete ht]
  | _, .obj hF => simp [synthValueCore, Fields.HasType.complete hF]
  | _, .cast hv he =>
      simp [synthValueCore, Value.HasType.complete hv, LeCo.HasType.complete he]
termination_by sizeOf v

/-- The kernel accepts every field block derivation. -/
theorem Fields.HasType.complete {s : Sig} {Γ : Ctx (s,x)} {F : Fields (s,x)}
    (h : Γ ⊢ᶠ F) : checkFieldsCore Γ F = some ⟨h⟩ := by
  match F, h with
  | _, .nil => simp [checkFieldsCore]
  | _, .cons hF ht =>
      simp [checkFieldsCore, Fields.HasType.complete hF, Tm.HasType.complete ht]
termination_by sizeOf F

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

/-- The measure is the term, as in `Tm.HasType.complete`: the two `let` rules
agree on a `let` at a singleton only after the opaque body is carried to the
forwarding binder, and that body is a strict subterm. -/
theorem Tm.HasType.type_unique {s : Sig} {Γ : Ctx s} {t : Tm s} {T T' : Ty s}
    (h : Γ ⊢ t : T) (h' : Γ ⊢ t : T') : T = T' := by
  match t, h with
  | _, .atom ha =>
      cases h' with
      | atom ha' => exact ha.type_unique ha'
  | _, .val hv =>
      cases h' with
      | val hv' => exact Value.HasType.type_unique hv hv'
  | _, .app ha hb =>
      cases h' with
      | app ha' hb' =>
          have hp := ha.type_unique ha'
          injection hp with _ _ hT
          rw [hT]
  | _, .proj _ _ =>
      cases h' with
      | proj _ _ => rfl
  | .let t0 u0, .let ht hu =>
      cases h' with
      | «let» ht' hu' =>
          have hT := Tm.HasType.type_unique ht ht'
          subst hT
          have hU := Tm.HasType.type_unique hu hu'
          have hs := congrArg Ty.strengthen? hU
          rw [Ty.strengthen?_weaken, Ty.strengthen?_weaken] at hs
          exact Option.some.inj hs
      | letPath ht' hu' =>
          have hT := Tm.HasType.type_unique ht ht'
          subst hT
          have hU := Tm.HasType.type_unique (Tm.HasType.forLet_body hu)
            (Tm.HasType.forLet_body_sngl hu')
          have hs := congrArg Ty.strengthen? hU
          rw [Ty.strengthen?_weaken, Ty.strengthen?_weaken] at hs
          exact Option.some.inj hs
  | .let t0 u0, .letPath ht hu =>
      cases h' with
      | «let» ht' hu' =>
          have hT := Tm.HasType.type_unique ht' ht
          subst hT
          have hU := Tm.HasType.type_unique (Tm.HasType.forLet_body_sngl hu)
            (Tm.HasType.forLet_body hu')
          have hs := congrArg Ty.strengthen? hU
          rw [Ty.strengthen?_weaken, Ty.strengthen?_weaken] at hs
          exact Option.some.inj hs
      | letPath ht' hu' =>
          have hT := Tm.HasType.type_unique ht ht'
          obtain rfl := Ty.snglOf_inj hT
          have hU := Tm.HasType.type_unique hu hu'
          have hs := congrArg Ty.strengthen? hU
          rw [Ty.strengthen?_weaken, Ty.strengthen?_weaken] at hs
          exact Option.some.inj hs
  | _, .cast _ he =>
      cases h' with
      | cast _ he' => exact (he.endpoints_unique he').2
termination_by sizeOf t

theorem Value.HasType.type_unique {s : Sig} {Γ : Ctx s} {v : Value s} {T T' : Ty s}
    (h : Γ ⊢ᵥ v : T) (h' : Γ ⊢ᵥ v : T') : T = T' := by
  match v, h with
  | _, .lam ht =>
      cases h' with
      | lam ht' => rw [Tm.HasType.type_unique ht ht']
  | _, .obj _ =>
      cases h' with
      | obj _ => rfl
  | _, .cast _ he =>
      cases h' with
      | cast _ he' => exact (he.endpoints_unique he').2
termination_by sizeOf v

end

end FCdot

end Paths
