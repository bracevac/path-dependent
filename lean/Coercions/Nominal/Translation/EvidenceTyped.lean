import Coercions.Nominal.Translation.Evidence

/-!
# The evidence is typed (plan X, Parts TR.3, TR.4 and TR.8, stage X6 group g2)

In related contexts `G ≈ Δ`, the image of a path typing `G ⊢ path p : T` types `p` at `⟦T⟧` in FCn,
and the image of a subtyping `G ⊢ S <: T` is a coercion `⟦S⟧ ≤ ⟦T⟧`.  `HasTy.pathImage_typed` and
`Sub.translate_typed` are one mutual theorem, structural over `HasTy` and `Sub`, with one case per
source rule.  `HasTy.translatePath_typed` is TR.8's statement at a path term.

The cases.  `ty_var` reads `Ctx.Rel.ty_plain` or `Ctx.Rel.ty_self` with `Ty.recElimCo_typed`.
`ty_new_elim` is `PA-Sel` at index 0.  `ty_rcd_intro` is `PA-FldI`.  `ty_sngl` is `PA-Alias` whose
first premise types the new path, with `aliasEv_typed`.  `ty_path_elim` is `PA-Sngl` over `PA-Sel`
over `PA-Alias` over `PA-FldI`, with `PE-Sel`.  `ty_rec_intro` and `ty_rec_elim` are
`Ty.recIntroCo_typed` and `Ty.recElimCo_typed`, which read `Ty.tel_fold`.  `ty_and_intro` is
`PA-Both` over `Ty.intoPath_typed`.  `ty_sub` is `PA-Cast`.  The four rules whose term is not a path
are refuted by their equation.  In `Sub`, `subtyp_and11` and `subtyp_and12` are `LE-Obj` over identity
templates or `LE-Bound`.  `subtyp_and2` is `LE-Pair`.  `subtyp_fld` and `subtyp_typ` are `LE-Obj`
over `MO-Fld`, `MO-Le` and `SD-Some`.  The replacement rules are `LE-Eq` over `EQ-Lift` with
`Repl.translate_hole`.  `subtyp_sel2` and `subtyp_sel1` are `LE-Member` at indices 0 and 1.
`subtyp_all` is `LE-Pi` with `Ctx.Rel.var`.  `subtyp_seal` (plan XII) is `LE-Seal` at
`Ctx.Rel.selfCls`, since `⟦p.C⟧ = p∙C`.

Identity templates copy a telescope whose every `is` proposition is a weakened type,
`Translation.ClosedIs`.  Every `tel⁺ T` is one (`Ty.telP_closedIs`).

The examples type the images of X0's E9, E10 and E11 (`Source/Examples.lean:56-172`).
`E9_image_alias` shows by `decide +kernel` that the image of `ty_sngl` is a forward `alias` whose first
premise is the image of the derivation that types the new path.  `Sub.translate_sngl_pq_irrel` and
its twin show by `rfl` that the second premise of a replacement rule is not read (decision D13).
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The image of `ty_rec_elim` is typed: from `P` at `⟦μ(z. T₀)⟧` with path `p`, an evidence at
`⟦T₀⟨p⟩⟧`.  The tel-like case reads `Ty.tel_fold`. -/
theorem Ty.recElimCo_typed {Δ : FCn.Ctx s} {P : FCn.PathCo s} {p : Path s} (T₀ : Ty (s,x))
    (hP : FCn.PathCo.HasType Δ P (Ty.mu T₀).translate) (hp : P.path = p) :
    FCn.PathCo.HasType Δ ((T₀.substPath p).recElimCo P) (T₀.substPath p).translate := by
  subst hp
  unfold Ty.recElimCo
  have hu := FCn.PathCo.HasType.unfold hP
  split
  · next h =>
      rw [Ty.translate_of_telLike h]
      apply FCn.PathCo.HasType.fold
      show FCn.PathCo.HasType Δ (.unfold P) (.mu (((T₀.substPath P.path).telP).substPath P.path).weaken)
      rw [Ty.tel_fold]; exact hu
  · next h =>
      have h' : (T₀.substPath P.path).telLike = false := by simpa using h
      have h₀ : T₀.telLike = false := by rw [← Ty.telLike_subst T₀ (PathSubst.one P.path)]; exact h'
      refine FCn.PathCo.HasType.cast (S := .mu (Ty.telP (T₀.substPath P.path))) ?_ ?_
      · rw [Ty.telP_of_not_telLike h']
        have e : T₀.tel = .cons .nil (.is T₀.translate) := Ty.telAt_of_not_telLike .here h₀
        have hu' : FCn.PathCo.HasType Δ (.unfold P) (.mu (T₀.tel.substPath P.path).weaken) := hu
        rw [e] at hu'
        rw [Ty.translate_substPath]
        exact hu'
      · rw [Ty.telP_of_not_telLike h']
        exact FCn.LeCo.HasType.bound .here

/-- The image of `ty_rec_intro` is typed: from `P` at `⟦T₀⟨p⟩⟧` with path `p`, an evidence at
`⟦μ(z. T₀)⟧`.  The tel-like case reads `Ty.tel_fold`. -/
theorem Ty.recIntroCo_typed {Δ : FCn.Ctx s} {P : FCn.PathCo s} {p : Path s} (T₀ : Ty (s,x))
    (hP : FCn.PathCo.HasType Δ P (T₀.substPath p).translate) (hp : P.path = p) :
    FCn.PathCo.HasType Δ (T₀.recIntroCo p P) (Ty.mu T₀).translate := by
  subst hp
  unfold Ty.recIntroCo
  split
  · next h =>
      have h' : (T₀.substPath P.path).telLike = true := by rw [Ty.substPath, Ty.telLike_subst]; exact h
      rw [Ty.translate_of_telLike h'] at hP
      apply FCn.PathCo.HasType.fold
      have hu := FCn.PathCo.HasType.unfold hP
      show FCn.PathCo.HasType Δ (.unfold P) (.mu (T₀.tel.substPath P.path).weaken)
      rw [← Ty.tel_fold]; exact hu
  · next h =>
      have h₀ : T₀.telLike = false := by simpa using h
      apply FCn.PathCo.HasType.fold
      have e : T₀.tel = .cons .nil (.is T₀.translate) := Ty.telAt_of_not_telLike .here h₀
      show FCn.PathCo.HasType Δ (.cast P _) (.mu (T₀.tel.substPath (FCn.PathCo.cast P _).path).weaken)
      rw [e]
      show FCn.PathCo.HasType Δ (.cast P _) (.mu (.cons .nil (.is (T₀.translate.substPath P.path).weaken)))
      rw [← Ty.translate_substPath]
      exact FCn.PathCo.HasType.cast hP (FCn.LeCo.HasType.intoBnd FCn.LeCo.HasType.refl)

/-- `into` is typed: from `P` at `⟦T⟧`, an evidence at `μ(w : tel⁺ T)`. -/
theorem Ty.intoPath_typed {Δ : FCn.Ctx s} {P : FCn.PathCo s} (T : Ty s)
    (hP : FCn.PathCo.HasType Δ P T.translate) : FCn.PathCo.HasType Δ (T.intoPath P) (.mu T.telP) := by
  unfold Ty.intoPath
  split
  · next h => rw [← Ty.translate_of_telLike h]; exact hP
  · next h =>
      rw [Ty.telP_of_not_telLike (by simpa using h)]
      exact FCn.PathCo.HasType.cast hP (FCn.LeCo.HasType.intoBnd FCn.LeCo.HasType.refl)

/-- `into'` is typed: from a coercion `S ≤ ⟦T⟧`, a coercion `S ≤ μ(w : tel⁺ T)`. -/
theorem Ty.into_typed {Δ : FCn.Ctx s} {e : FCn.LeCo s} {S : FCn.Ty s} (T : Ty s)
    (he : FCn.LeCo.HasType Δ e S T.translate) : FCn.LeCo.HasType Δ (T.into e) S (.mu T.telP) := by
  unfold Ty.into
  split
  · next h => rw [← Ty.translate_of_telLike h]; exact he
  · next h =>
      rw [Ty.telP_of_not_telLike (by simpa using h)]
      exact FCn.LeCo.HasType.intoBnd he

-- a telescope whose every `is` proposition is a weakened type, which identity templates can copy
/-- A telescope whose every `is` proposition is a weakened type.  Its identity template types,
since `MO-Is` concludes `is T.weaken`. -/
inductive _root_.Nominal.Translation.ClosedIs : {s : Sig} → FCn.Telescope (s,x) → Prop where
  -- the empty telescope
  | nil : Translation.ClosedIs (.nil : FCn.Telescope (s,x))
  -- binders Tel X Y, a bound proposition X ⊑ Y
  | le {Tel : FCn.Telescope (s,x)} {X Y : FCn.Ty (s,x)} : Translation.ClosedIs Tel → Translation.ClosedIs (.cons Tel (.le X Y))
  -- binders Tel a X, a field proposition fld a X
  | fld {Tel : FCn.Telescope (s,x)} {a : Label} {X : FCn.Ty (s,x)} : Translation.ClosedIs Tel → Translation.ClosedIs (.cons Tel (.fld a X))
  -- binders Tel q, an alias proposition ≈ q
  | alias {Tel : FCn.Telescope (s,x)} {q : Path (s,x)} : Translation.ClosedIs Tel → Translation.ClosedIs (.cons Tel (.alias q))
  -- binders Tel T, a proposition is T↑ over a type T of the outer signature
  | is {Tel : FCn.Telescope (s,x)} {T : FCn.Ty s} : Translation.ClosedIs Tel → Translation.ClosedIs (.cons Tel (.is T.weaken))

/-- Appending keeps `ClosedIs`. -/
theorem _root_.Nominal.Translation.ClosedIs.append {Tel : FCn.Telescope (s,x)} (h : Translation.ClosedIs Tel) :
    ∀ {Tel' : FCn.Telescope (s,x)}, Translation.ClosedIs Tel' → Translation.ClosedIs (Tel ++ Tel')
  | _, .nil => h
  | _, .le h' => .le (Translation.ClosedIs.append h h')
  | _, .fld h' => .fld (Translation.ClosedIs.append h h')
  | _, .alias h' => .alias (Translation.ClosedIs.append h h')
  | _, .is h' => .is (Translation.ClosedIs.append h h')

-- one mutual block
mutual
/-- `tel⁺ {D}` satisfies `ClosedIs`. -/
theorem Dec.telP_closedIs : ∀ (D : Dec s), Translation.ClosedIs D.telP
  | .typ _ _ _ => .le (.le .nil)
  | .trm _ _ => .fld .nil
/-- `tel⁺ T` satisfies `ClosedIs`. -/
theorem Ty.telP_closedIs : ∀ (T : Ty s), Translation.ClosedIs T.telP
  | .top => .nil
  | .rcd D => Dec.telP_closedIs D
  | .and T U => Translation.ClosedIs.append (Ty.telP_closedIs T) (Ty.telP_closedIs U)
  | .bot => .is .nil
  | .sel _ _ => .is .nil
  | .mu _ => .is .nil
  | .all _ _ => .is .nil
  | .sngl _ => .is .nil
end
-- end of the block

/-- The identity template of `Tel` types from `src` to `Tel` when every proposition of `Tel` at
index `i` is the proposition of `src` at `off + i`. -/
theorem _root_.Nominal.Translation.identityMorphism_typed {Δ : FCn.Ctx s} (src : FCn.Telescope (s,x)) (off : Nat) :
    ∀ {Tel : FCn.Telescope (s,x)}, Translation.ClosedIs Tel → (∀ i pr, Tel.At i pr → src.At (off + i) pr) →
      FCn.Morphism.HasType Δ src (Translation.identityMorphism src off Tel) Tel
  | _, .nil, _ => .nil
  | _, .le h, hi => .le (Translation.identityMorphism_typed src off h (fun i pr hi' => hi i pr (.there hi'))) (hi _ _ .here) .none .none
  | _, .fld h, hi => .fld (Translation.identityMorphism_typed src off h (fun i pr hi' => hi i pr (.there hi'))) (hi _ _ .here) .none
  | _, .alias h, hi => .alias (Translation.identityMorphism_typed src off h (fun i pr hi' => hi i pr (.there hi'))) (hi _ _ .here)
  | _, .is h, hi => .is (Translation.identityMorphism_typed src off h (fun i pr hi' => hi i pr (.there hi'))) (.bound (hi _ _ .here))

/-- The image of `subtyp_and11` is a coercion `⟦T ∧ U⟧ ≤ ⟦T⟧`. -/
theorem Ty.projL_typed {Δ : FCn.Ctx s} (T U : Ty s) :
    FCn.LeCo.HasType Δ (Ty.projL T U) (Ty.and T U).translate T.translate := by
  unfold Ty.projL
  split
  · next h =>
      rw [Ty.translate_of_telLike h]
      exact .obj (Translation.identityMorphism_typed _ 0 (Ty.telP_closedIs T)
        (fun i pr hi => by rw [Nat.zero_add]; exact hi.append_left _))
  · next h =>
      refine .bound ?_
      have e := Ty.telP_of_not_telLike (T := T) (by simpa using h)
      show (T.telP ++ U.telP).At 0 _
      rw [e]; exact FCn.Telescope.At.append_left .here _

/-- The image of `subtyp_and12` is a coercion `⟦T ∧ U⟧ ≤ ⟦U⟧`. -/
theorem Ty.projR_typed {Δ : FCn.Ctx s} (T U : Ty s) :
    FCn.LeCo.HasType Δ (Ty.projR T U) (Ty.and T U).translate U.translate := by
  unfold Ty.projR
  split
  · next h =>
      rw [Ty.translate_of_telLike h]
      exact .obj (Translation.identityMorphism_typed _ _ (Ty.telP_closedIs U)
        (fun i pr hi => FCn.Telescope.At.append_right _ hi))
  · next h =>
      refine .bound ?_
      have e := Ty.telP_of_not_telLike (T := U) (by simpa using h)
      show (T.telP ++ U.telP).At (T.telP.length) _
      have := FCn.Telescope.At.append_right T.telP (j := 0) (Tel' := U.telP) (pr := .is U.translate.weaken) (by rw [e]; exact .here)
      simpa using this

/-- `π(d₁)` is typed: from `P` at `⟦q.type⟧`, the path equality `P.path ≃ q`, by `PE-Member` at
index 0. -/
theorem _root_.Nominal.Translation.aliasEv_typed {Δ : FCn.Ctx s} {P : FCn.PathCo s} {q : Path s}
    (hP : FCn.PathCo.HasType Δ P (FCn.Ty.sngl q)) : FCn.PEq.HasType Δ (Translation.aliasEv P q) P.path q := by
  have h := FCn.PEq.HasType.member (i := 0) (q := q.weaken) hP FCn.LeCo.HasType.refl .here
  rwa [Paths.FCdot.Path.weaken_substPath] at h

-- one mutual block, structural over HasTy and Sub, one case per source rule
mutual
/-- In related contexts the image of a path typing types the path at the translated type.  An
equation form (D12): the term is generalized by `t = .path p`. -/
theorem HasTy.pathImage_typed : ∀ {G : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy G t T) {Δ : FCn.Ctx s},
    Ctx.Rel G Δ → ∀ (p : Path s), t = .path p →
      ∃ P, d.pathImage = some P ∧ FCn.PathCo.HasType Δ P T.translate ∧ P.path = p
  | G, _, T, .ty_var (x := x) hx, Δ, h, p, e => by
      cases e
      cases hs : G.isSelf x with
      | false =>
          refine ⟨.var x, by simp only [HasTy.pathImage, hs]; rfl, .var ?_, rfl⟩
          rw [Ctx.Rel.ty_plain h hs, hx]
      | true =>
          obtain ⟨T₀, e₁, e₂⟩ := Ctx.Rel.ty_self h hs
          refine ⟨T.recElimCo (.var x), by simp only [HasTy.pathImage, hs]; rfl, ?_, Ty.recElimCo_path _ _⟩
          rw [← hx, e₂]
          exact Ty.recElimCo_typed T₀ (.var e₁) rfl
  | _, _, _, .ty_all_intro _, _, _, _, e => nomatch e
  | _, _, _, .ty_all_elim _ _, _, _, _, e => nomatch e
  | _, _, _, .ty_new_intro _, _, _, _, e => nomatch e
  | _, _, _, .ty_let _ _, _, _, _, e => nomatch e
  | _, _, _, .ty_new_elim (p := p') (a := a) (T := T) d, Δ, h, p, e => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p' rfl
      cases e
      refine ⟨.sel P a 0, by simp only [HasTy.pathImage, hd]; rfl, ?_, by simp only [FCn.PathCo.path, hp]⟩
      have := FCn.PathCo.HasType.sel (i := 0) (a := a) (T := T.translate.weaken) hP .here
      rwa [FCn.Ty.weaken_substPath] at this
  | _, _, _, .ty_rcd_intro (p := p') (a := a) (T := T) d, Δ, h, p, e => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h (p'.sel a) rfl
      cases e
      exact ⟨.fldI p' a P, by simp only [HasTy.pathImage, hd]; rfl, .fldI hP hp, rfl⟩
  | _, _, _, .ty_sngl (p := p') (q := q) d₁ d₂, Δ, h, p, e => by
      obtain ⟨P, hd₁, hP, hp⟩ := HasTy.pathImage_typed d₁ h p' rfl
      obtain ⟨Q, hd₂, hQ, hq⟩ := HasTy.pathImage_typed d₂ h q rfl
      cases e
      refine ⟨.alias P (Translation.aliasEv P q) Q, by simp only [HasTy.pathImage, hd₁, hd₂], ?_, hp⟩
      exact .alias hP (by rw [hq]; exact Translation.aliasEv_typed hP) hQ
  | _, _, _, .ty_path_elim (p := p') (q := q) (a := a) (T := T) d₁ d₂, Δ, h, p, e => by
      obtain ⟨P, hd₁, hP, hp⟩ := HasTy.pathImage_typed d₁ h p' rfl
      obtain ⟨Q, hd₂, hQ, hq⟩ := HasTy.pathImage_typed d₂ h (q.sel a) rfl
      cases e
      refine ⟨.sngl (.sel (.alias P (Translation.aliasEv P q) (.fldI q a Q)) a 0) (q.sel a) (.sel (Translation.aliasEv P q) a),
        by simp only [HasTy.pathImage, hd₁, hd₂], ?_, by simp only [FCn.PathCo.path, hp]⟩
      have hπ := Translation.aliasEv_typed hP
      have hF : FCn.PathCo.HasType Δ (.fldI q a Q) (.mu (.cons .nil (.fld a T.translate.weaken))) := .fldI hQ hq
      have hA := FCn.PathCo.HasType.alias hP hπ hF
      have hS := FCn.PathCo.HasType.sel (i := 0) (a := a) (T := T.translate.weaken) hA .here
      exact .sngl hS (.sel hπ)
  | _, _, _, .ty_rec_intro (p := p') (T := T) d, Δ, h, p, e => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p' rfl
      cases e
      exact ⟨T.recIntroCo p' P, by simp only [HasTy.pathImage, hd]; rfl, Ty.recIntroCo_typed T hP hp,
        by rw [Ty.recIntroCo_path, hp]⟩
  | _, _, _, .ty_rec_elim (p := p') (T := T) d, Δ, h, p, e => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p' rfl
      cases e
      exact ⟨(T.substPath p').recElimCo P, by simp only [HasTy.pathImage, hd]; rfl, Ty.recElimCo_typed T hP hp,
        by rw [Ty.recElimCo_path, hp]⟩
  | _, _, _, .ty_and_intro (p := p') (T := T) (U := U) d₁ d₂, Δ, h, p, e => by
      obtain ⟨P, hd₁, hP, hp⟩ := HasTy.pathImage_typed d₁ h p' rfl
      obtain ⟨Q, hd₂, hQ, hq⟩ := HasTy.pathImage_typed d₂ h p' rfl
      cases e
      refine ⟨.both T.telP U.telP (T.intoPath P) (U.intoPath Q), by simp only [HasTy.pathImage, hd₁, hd₂], ?_,
        by rw [FCn.PathCo.path, Ty.intoPath_path, hp]⟩
      exact .both (Ty.intoPath_typed T hP) (Ty.intoPath_typed U hQ) (by rw [Ty.intoPath_path, Ty.intoPath_path, hp, hq])
  | _, _, _, .ty_sub d e', Δ, h, p, e => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p e
      exact ⟨.cast P e'.translate, by simp only [HasTy.pathImage, hd]; rfl, .cast hP (Sub.translate_typed e' h), hp⟩
/-- In related contexts the image of a subtyping `S <: T` is a coercion `⟦S⟧ ≤ ⟦T⟧`. -/
theorem Sub.translate_typed : ∀ {G : Ctx s} {S T : Ty s} (d : Sub G S T) {Δ : FCn.Ctx s},
    Ctx.Rel G Δ → FCn.LeCo.HasType Δ d.translate S.translate T.translate
  | _, _, _, .subtyp_top, _, _ => .top
  | _, _, _, .subtyp_bot, _, _ => .bot
  | _, _, _, .subtyp_refl, _, _ => .refl
  | _, _, _, .subtyp_trans e₁ e₂, _, h => .trans (Sub.translate_typed e₁ h) (Sub.translate_typed e₂ h)
  | _, _, _, .subtyp_and11 (T := T) (U := U), _, _ => Ty.projL_typed T U
  | _, _, _, .subtyp_and12 (T := T) (U := U), _, _ => Ty.projR_typed T U
  | _, _, _, .subtyp_and2 (T := T) (U := U) e₁ e₂, _, h =>
      .pair (Ty.into_typed T (Sub.translate_typed e₁ h)) (Ty.into_typed U (Sub.translate_typed e₂ h))
  | _, _, _, .subtyp_fld (a := a) (T := T) (U := U) e, _, h =>
      .obj (.fld .nil .here (.some (Sub.translate_typed e h)))
  | _, _, _, .subtyp_typ (A := A) e₁ e₂, _, h =>
      .obj (.le (.le .nil (.there .here) (.some (Sub.translate_typed e₁ h)) .none) .here .none
        (.some (Sub.translate_typed e₂ h)))
  | _, _, _, .subtyp_sngl_pq (p := p) (q := q) d₁ _ r, Δ, h => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d₁ h p rfl
      have hπ := Translation.aliasEv_typed hP
      rw [hp] at hπ
      have hl := FCn.EqCo.HasType.lift (T := r.hole.translate) hπ
      rw [(Repl.translate_hole r).1, (Repl.translate_hole r).2] at hl
      show FCn.LeCo.HasType Δ (.eqToLe (.lift r.hole.translate (Translation.aliasEv (d₁.pathImage.getD _) q))) _ _
      rw [hd]; exact .eqToLe hl
  | _, _, _, .subtyp_sngl_qp (p := p) (q := q) d₁ _ r, Δ, h => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d₁ h p rfl
      have hπ := Translation.aliasEv_typed hP
      rw [hp] at hπ
      have hl := FCn.EqCo.HasType.lift (T := r.hole.translate) (FCn.PEq.HasType.symm hπ)
      rw [(Repl.translate_hole r).1, (Repl.translate_hole r).2] at hl
      show FCn.LeCo.HasType Δ (.eqToLe (.lift r.hole.translate (.symm (Translation.aliasEv (d₁.pathImage.getD _) q)))) _ _
      rw [hd]; exact .eqToLe hl
  | _, _, _, .subtyp_sel2 (p := p) (A := A) (S := S) (T := T) d, Δ, h => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p rfl
      have hm := FCn.LeCo.HasType.member (i := 0) hP FCn.LeCo.HasType.refl (.there .here)
      rw [hp, FCn.Ty.weaken_substPath] at hm
      show FCn.LeCo.HasType Δ (.member (d.pathImage.getD _) _ 0) _ _
      rw [hd]; exact hm
  | _, _, _, .subtyp_sel1 (p := p) (A := A) (S := S) (T := T) d, Δ, h => by
      obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p rfl
      have hm := FCn.LeCo.HasType.member (i := 1) hP FCn.LeCo.HasType.refl .here
      rw [hp, FCn.Ty.weaken_substPath] at hm
      show FCn.LeCo.HasType Δ (.member (d.pathImage.getD _) _ 1) _ _
      rw [hd]; exact hm
  | _, _, _, .subtyp_all e₁ e₂, _, h => .pi (Sub.translate_typed e₁ h) (Sub.translate_typed e₂ (.var h))
  | _, _, _, .subtyp_seal hs, _, h => .seal (h.selfCls hs)    -- LE-Seal at Ctx.Rel.selfCls
end
-- end of the block

/-- TR.8's `translatePath_typed`: in related contexts the image of a derivation at a path term types
that path at the translated type. -/
theorem HasTy.translatePath_typed {G : Ctx s} {Δ : FCn.Ctx s} {p : Path s} {T : Ty s}
    (d : HasTy G (.path p) T) (h : Ctx.Rel G Δ) :
    FCn.PathCo.HasType Δ d.translatePath T.translate ∧ d.translatePath.path = p := by
  obtain ⟨P, hd, hP, hp⟩ := HasTy.pathImage_typed d h p rfl
  unfold HasTy.translatePath
  rw [hd]
  exact ⟨hP, hp⟩

/-- E9: the image of `x.a.b : ⊤`, singleton creation and propagation, is typed. -/
theorem E9_image_typed : FCn.PathCo.HasType e9_G.translate E9_xab_S.translatePath FCn.Ty.top :=
  (HasTy.translatePath_typed E9_xab_S (e9_G.rel_translate rfl)).1

/-- E9: the image of `ty_sngl` is a forward `alias` whose first premise is the image of the derivation
that types the new path `x.a.b`. -/
theorem E9_image_alias :
    E9_xab_S.translatePath = .alias E9_xab.translatePath (Translation.aliasEv E9_xab.translatePath (e9_x.sel e9_b)) E9_xb.translatePath := by
  decide +kernel

/-- E10: the images of two replacement steps are typed, `E10_pq` at the right operand by `rand2` and
`E10_qp` at the left one by `rand1`. -/
theorem E10_image_typed :
    FCn.PathCo.HasType e10_G.translate E10_pq.translatePath (e10_ty e10_p e10_q).translate ∧
    FCn.PathCo.HasType e10_G.translate E10_qp.translatePath (e10_ty e10_q e10_p).translate :=
  ⟨(HasTy.translatePath_typed E10_pq (e10_G.rel_translate rfl)).1, (HasTy.translatePath_typed E10_qp (e10_G.rel_translate rfl)).1⟩

/-- E11: the image of Fld-I is typed by `PA-FldI`, which compares paths syntactically. -/
theorem E11_image_typed (T : Ty []) :
    FCn.PathCo.HasType (e11_G T).translate (E11_d T).translatePath (Ty.rcd (.trm e11_a T.weaken.weaken)).translate :=
  (HasTy.translatePath_typed (E11_d T) ((e11_G T).rel_translate rfl)).1

/-- Decision 13: the image of `subtyp_sngl_pq` does not read its second premise. -/
theorem Sub.translate_sngl_pq_irrel {G : Ctx s} {p q : Path s} {U T T' : Ty s} (d₁ : HasTy G (.path p) (.sngl q))
    (d₂ d₂' : HasTy G (.path q) U) (r : Repl p q T T') :
    (Sub.subtyp_sngl_pq d₁ d₂ r).translate = (Sub.subtyp_sngl_pq d₁ d₂' r).translate := rfl

/-- Decision 13: the image of `subtyp_sngl_qp` does not read its second premise. -/
theorem Sub.translate_sngl_qp_irrel {G : Ctx s} {p q : Path s} {U T T' : Ty s} (d₁ : HasTy G (.path p) (.sngl q))
    (d₂ d₂' : HasTy G (.path q) U) (r : Repl q p T T') :
    (Sub.subtyp_sngl_qp d₁ d₂ r).translate = (Sub.subtyp_sngl_qp d₁ d₂' r).translate := rfl

end Nominal.Source
