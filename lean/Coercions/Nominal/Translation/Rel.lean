import Coercions.Nominal.Translation.TypesLemmas

/-!
# Related contexts (plan X, Part TR.1, stage X6 group g2)

`Ctx.Rel G Δ`, written `G ≈ Δ`, relates a source context to a target context binder by binder.  A
plain binder `z : T` becomes `z : opaque ⟦T⟧`.  A self binder `z :ˢ T` becomes a binder `b` of any
transparency whose type is `⟦μ(z. T)⟧`.  The plan writes the premise `b.ty = (⟦μ(z. T)⟧)↑`
(`plan-10-pdot.md:716`).  The type of an FCn binding is in the outer signature and `Ctx.ty` weakens
it (`FCp/Context.lean:28-39`), so here the premise is `b.ty = (Ty.mu T).translate` (decision D5 of
the groups file).  The translation emits no `defP`, so a binder may be opaque or transparent at any
block.

`Ctx.isSelf G x` (`Source/Binding.lean`) decides whether `x` is bound by a self binder.
`Ctx.Rel.ty_plain` reads the type of a plain variable in `Δ`.  `Ctx.Rel.ty_self` reads a self variable's type as `⟦μ(z. T₀)⟧`, with
`G.lookup x = T₀⟨x⟩`.  Below a self binder `G.lookup` weakens, so `T₀` is the weakened body.

Plan XII adds one premise to Rel-Self, `Ctx.ClsAgree Δ T b`: each class that the self type `T`
declares at a field path `bs` of its self, read by `Ty.clsAt`, is the class of `Δ, z : b` at the
path `z.bs`, translated.  `Ctx.Rel.clsAt_ext` lifts it to every self binder of the context, and
`Ctx.Rel.selfCls` reads it at the class reading `G.selfCls p C` of the source.  That is the premise
of LE-Seal at the image of `subtyp_seal`.  An opaque binder has no block, so at an opaque `b` the
premise holds exactly when `T` declares no class.

`Ctx.translate` gives a source context a related target context, with every binder opaque
(decision D14), when the context is class-free (`Ctx.clsFree`).  Then `Ty.clsAt_none_of_clsFree`
empties the premise of `ClsAgree` at each self binder.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- `ClsAgree Δ T b` of Rel-Self (plan XII): each class that the self type `T` declares at the field path `bs` of its
self is the class of `Δ, z : b` at the same path, translated. -/
def Ctx.ClsAgree (Δ : FCn.Ctx s) (T : Ty (s,x)) (b : FCn.Binding s) : Prop :=
  ∀ (bs : List Label) (C : Label) (U : Ty (s,x)), T.clsAt (.var .here) bs C = some U →
    (Δ.cons b).clsAt ((Path.var .here).nomExt bs) C = some U.translate

/-- `G ≈ Δ` of TR.1: a source context and a target context with the same binders, each target
binder's type the translation of the source binder's. -/
inductive Ctx.Rel : Ctx s → FCn.Ctx s → Prop where           -- G ≈ Δ
  -- Rel-Nil
  | nil : Ctx.Rel .nil .nil
  -- Rel-Var     binders G Δ T, z the new variable
  | var : Ctx.Rel G Δ → Ctx.Rel (G.cons T) (Δ.cons (.opaque T.translate))
  -- Rel-Self    binders G Δ T b, ClsAgree of plan XII, T over (s,z), b opaque or transparent at any block
  | self : Ctx.Rel G Δ → b.ty = (Ty.mu T).translate → Ctx.ClsAgree Δ T b → Ctx.Rel (G.consSelf T) (Δ.cons b)

/-- Renaming commutes with opening a body at a path. -/
theorem Ty.substPath_rename (T : Ty (s₁,x)) (q : Path s₁) (ρ : Rename s₁ s₂) :
    (T.substPath q).rename ρ = (T.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Ty.rename_eq_subst, Ty.substPath_subst, PathSubst.lift_ofRename, ← Ty.rename_eq_subst, Paths.FCdot.Path.subst_ofRename]

/-- Renaming commutes with extending a path by field labels. -/
theorem Path.ext_rename (p : Path s₁) (bs : List Label) (ρ : Rename s₁ s₂) :
    (p.nomExt bs).rename ρ = (p.rename ρ).nomExt bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons a bs ih => exact ih (p.sel a)

/-- Every path is its root variable extended by field labels. -/
theorem Path.exists_ext_root : ∀ (p : Path s), ∃ bs, p = (Path.var p.root).nomExt bs
  | .var x => ⟨[], rfl⟩
  | .sel p a => by
      obtain ⟨bs, e⟩ := Path.exists_ext_root p
      refine ⟨bs ++ [a], ?_⟩
      rw [Path.ext_append]
      show Path.sel p a = Path.sel ((Path.var p.root).nomExt bs) a
      rw [← e]

/-- Renaming keeps a class body a class body. -/
theorem Ty.clsBody_rename (T : Ty s₁) (ρ : Rename s₁ s₂) : (T.rename ρ).clsBody = T.clsBody := by
  rw [Ty.rename_eq_subst, Ty.clsBody_subst]

/-- Renaming commutes with the class declared at `C`. -/
theorem Ty.findCls_rename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂) (C : Label),
    (T.rename ρ).findCls C = (T.findCls C).map (Ty.rename · ρ)
  | .and T U, ρ, C => by
      simp only [Ty.rename, Ty.findCls, Ty.findCls_rename T ρ C, Ty.findCls_rename U ρ C]
      cases U.findCls C <;> rfl
  | .rcd (.typ C' L U), ρ, C => by
      simp only [Ty.rename, Dec.rename, Ty.findCls, Ty.clsBody_rename]
      have e : (L.rename ρ = .bot) ↔ (L = .bot) := by rw [Ty.rename_eq_subst]; exact Ty.subst_eq_bot_iff L _
      by_cases h : L = .bot ∧ C = C' ∧ U.clsBody = true
      · rw [if_pos (by rw [e]; exact h), if_pos h]; rfl
      · rw [if_neg (by rw [e]; exact h), if_neg h]; rfl
  | .rcd (.trm _ _), _, _ => rfl
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl
  | .sngl _, _, _ => rfl

/-- Renaming commutes with the body of a `μ`, under one binder. -/
theorem Ty.muBody_rename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂), (T.rename ρ).muBody = T.muBody.map (Ty.rename · ρ.lift)
  | .mu _, _ => rfl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .rcd _, _ => rfl
  | .and _ _, _ => rfl
  | .sel _ _, _ => rfl
  | .all _ _, _ => rfl
  | .sngl _, _ => rfl

/-- Renaming commutes with the body of the nested object at `b`, under one binder. -/
theorem Ty.findNest_rename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂) (b : Label),
    (T.rename ρ).findNest b = (T.findNest b).map (Ty.rename · ρ.lift)
  | .and T U, ρ, b => by
      simp only [Ty.rename, Ty.findNest, Ty.findNest_rename T ρ b, Ty.findNest_rename U ρ b]
      cases U.findNest b <;> rfl
  | .rcd (.trm b' V), ρ, b => by
      simp only [Ty.rename, Dec.rename, Ty.findNest]
      by_cases h : b = b'
      · rw [if_pos h, if_pos h, Ty.muBody_rename]
      · rw [if_neg h, if_neg h]; rfl
  | .rcd (.typ _ _ _), _, _ => rfl
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl
  | .sngl _, _, _ => rfl

/-- Renaming commutes with the class reading `T.clsAt r bs C`. -/
theorem Ty.clsAt_rename : ∀ (bs : List Label) (T : Ty s₁) (r : Path s₁) (ρ : Rename s₁ s₂) (C : Label),
    (T.rename ρ).clsAt (r.rename ρ) bs C = (T.clsAt r bs C).map (Ty.rename · ρ)
  | [], T, _, ρ, C => Ty.findCls_rename T ρ C
  | b :: bs, T, r, ρ, C => by
      simp only [Ty.clsAt, Ty.findNest_rename]
      cases T.findNest b with
      | none => rfl
      | some U =>
          show ((U.rename ρ.lift).substPath ((r.rename ρ).sel b)).clsAt ((r.rename ρ).sel b) bs C = _
          have e : (U.rename ρ.lift).substPath ((r.rename ρ).sel b) = (U.substPath (r.sel b)).rename ρ :=
            (Ty.substPath_rename U (r.sel b) ρ).symm
          rw [e]
          exact Ty.clsAt_rename bs _ (r.sel b) ρ C

/-- Weakening a body under its binder and opening it at that binder gives the body back. -/
theorem Ty.rename_succ_lift_substPath_here (T : Ty (s,x)) :
    (T.rename (Rename.succ.lift)).substPath (.var .here) = T := by
  rw [Ty.rename_eq_subst, Ty.substPath, Ty.subst_subst]
  have : (PathSubst.ofRename ((Rename.succ (s := s) (k := .var)).lift (k := .var))).comp (PathSubst.one (.var .here)) =
      PathSubst.ofRename Rename.id := by
    apply PathSubst.funext'; intro y; rcases y with _ | y <;> rfl
  rw [this, Ty.subst_ofRename_id]

/-- At a plain variable the target type is the translated source type. -/
theorem Ctx.Rel.ty_plain : ∀ {G : Ctx s} {Δ : FCn.Ctx s} {x : BVar s .var}, Ctx.Rel G Δ → G.isSelf x = false →
    Δ.ty x = (G.lookup x).translate
  | _, _, .here, .var (T := T) _, _ => (Ty.translate_weaken T).symm
  | _, _, .here, .self _ _ _, h => nomatch h
  | _, _, .there y, .var h, hs => by
      show (_ : FCn.Ty _).weaken = (Ty.weaken _).translate
      rw [Ctx.Rel.ty_plain h hs, Ty.translate_weaken]
  | _, _, .there y, .self h _ _, hs => by
      show (_ : FCn.Ty _).weaken = (Ty.weaken _).translate
      rw [Ctx.Rel.ty_plain h hs, Ty.translate_weaken]

/-- At a self variable the target type is `⟦μ(z. T₀)⟧` for a body `T₀` that opens at the variable
to the source type. -/
theorem Ctx.Rel.ty_self : ∀ {G : Ctx s} {Δ : FCn.Ctx s} {x : BVar s .var}, Ctx.Rel G Δ → G.isSelf x = true →
    ∃ T₀ : Ty (s,x), Δ.ty x = (Ty.mu T₀).translate ∧ G.lookup x = T₀.substPath (.var x)
  | _, _, .here, .var _, h => nomatch h
  | _, _, .here, .self (T := T) (b := b) _ hb _, _ => by
      refine ⟨T.rename Rename.succ.lift, ?_, (Ty.rename_succ_lift_substPath_here T).symm⟩
      show b.ty.weaken = FCn.Ty.mu ((T.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
      rw [hb, Ty.telAt_rename]; rfl
  | _, _, .there y, .var h, hs => by
      obtain ⟨T₀, e₁, e₂⟩ := Ctx.Rel.ty_self h hs
      refine ⟨T₀.rename Rename.succ.lift, ?_, ?_⟩
      · show (_ : FCn.Ty _).weaken = FCn.Ty.mu ((T₀.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
        rw [e₁, Ty.telAt_rename]; rfl
      · show (Ty.weaken _) = _
        rw [e₂, Ty.weaken, Ty.substPath_rename]; rfl
  | _, _, .there y, .self h _ _, hs => by
      obtain ⟨T₀, e₁, e₂⟩ := Ctx.Rel.ty_self h hs
      refine ⟨T₀.rename Rename.succ.lift, ?_, ?_⟩
      · show (_ : FCn.Ty _).weaken = FCn.Ty.mu ((T₀.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
        rw [e₁, Ty.telAt_rename]; rfl
      · show (Ty.weaken _) = _
        rw [e₂, Ty.weaken, Ty.substPath_rename]; rfl

/-- `ClsAgree` at every self binder: a class that the type of a self variable `x` declares at the
path `x.bs` is the class of `Δ` at `x.bs`, translated. -/
theorem Ctx.Rel.clsAt_ext : ∀ {G : Ctx s} {Δ : FCn.Ctx s}, Ctx.Rel G Δ → ∀ (x : BVar s .var) (bs : List Label) (C : Label) (U : Ty s),
    G.isSelf x = true → (G.lookup x).clsAt (.var x) bs C = some U → Δ.clsAt ((Path.var x).nomExt bs) C = some U.translate
  | _, _, .self _ _ ha, .here, bs, C, U, _, h => ha bs C U h
  | _, _, .var _, .here, _, _, _, hs, _ => nomatch hs
  | _, _, .var (Δ := Δ) h, .there y, bs, C, U, hs, hc => by
      have e : (Path.var (.there y) : Path (_,x)) = (Path.var y).rename (Rename.succ (k := .var)) := rfl
      rw [e, ← Path.ext_rename, FCn.Ctx.clsAt_weaken]
      change (Ty.weaken _).clsAt _ bs C = some U at hc
      rw [Ty.weaken, e, Ty.clsAt_rename] at hc
      cases h₁ : (Ctx.lookup _ y).clsAt (.var y) bs C with
      | none => rw [h₁] at hc; cases hc
      | some U₀ =>
          rw [h₁] at hc; cases hc
          rw [Ctx.Rel.clsAt_ext h y bs C U₀ hs h₁, Option.map_some, Ty.translate_rename]
  | _, _, .self (Δ := Δ) h _ _, .there y, bs, C, U, hs, hc => by
      have e : (Path.var (.there y) : Path (_,x)) = (Path.var y).rename (Rename.succ (k := .var)) := rfl
      rw [e, ← Path.ext_rename, FCn.Ctx.clsAt_weaken]
      change (Ty.weaken _).clsAt _ bs C = some U at hc
      rw [Ty.weaken, e, Ty.clsAt_rename] at hc
      cases h₁ : (Ctx.lookup _ y).clsAt (.var y) bs C with
      | none => rw [h₁] at hc; cases hc
      | some U₀ =>
          rw [h₁] at hc; cases hc
          rw [Ctx.Rel.clsAt_ext h y bs C U₀ hs h₁, Option.map_some, Ty.translate_rename]

/-- The class reading of the source is the class reading of the target, translated: `G.selfCls p C
= some U` gives `Δ.clsAt p C = some ⟦U⟧`, the premise of LE-Seal. -/
theorem Ctx.Rel.selfCls {G : Ctx s} {Δ : FCn.Ctx s} (h : Ctx.Rel G Δ) {p : Path s} {C : Label} {U : Ty s}
    (hc : G.selfCls p C = some U) : Δ.clsAt p C = some U.translate := by
  obtain ⟨bs, e⟩ := Path.exists_ext_root p
  rw [e] at hc ⊢
  rw [Ctx.selfCls_ext] at hc
  split at hc
  · next hs => exact h.clsAt_ext _ bs C U hs hc
  · cases hc

/-- The target context of a source context, every binder opaque (D14). -/
def Ctx.translate : Ctx s → FCn.Ctx s                         -- D14
  | .nil => .nil                                              -- [] ↦ []
  | .cons G T => .cons G.translate (.opaque T.translate)                    -- z : T ↦ z : opaque ⟦T⟧
  | .consSelf G T => .cons G.translate (.opaque (Ty.mu T).translate)        -- z :ˢ T ↦ z : opaque ⟦μ(z. T)⟧

/-- A class-free source context is related to its translation (plan XII adds the hypothesis
`G.clsFree = true`, since an opaque self binder has no block for `ClsAgree`). -/
theorem Ctx.rel_translate : ∀ (G : Ctx s), G.clsFree = true → Ctx.Rel G G.translate
  | .nil, _ => .nil
  | .cons G _, h => .var (Ctx.rel_translate G h)
  | .consSelf G T, h => by
      simp only [Ctx.clsFree, Bool.and_eq_true] at h
      refine .self (Ctx.rel_translate G h.1) rfl ?_
      intro bs C U hU
      rw [Ty.clsAt_none_of_clsFree bs _ C h.2] at hU
      cases hU

end Nominal.Source
