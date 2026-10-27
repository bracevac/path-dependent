import Coercions.PDot.Translation.TypesLemmas

/-!
# Related contexts (plan X, Part TR.1, stage X6 group g2)

`Ctx.Rel G Δ`, written `G ≈ Δ`, relates a source context to a target context binder by binder.  A
plain binder `z : T` becomes `z : opaque ⟦T⟧`.  A self binder `z :ˢ T` becomes a binder `b` of any
transparency whose type is `⟦μ(z. T)⟧`.  The plan writes the premise `b.ty = (⟦μ(z. T)⟧)↑`
(`plan-10-pdot.md:716`).  The type of an FCp binding is in the outer signature and `Ctx.ty` weakens
it (`FCp/Context.lean:28-39`), so here the premise is `b.ty = (Ty.mu T).translate` (decision D5 of
the groups file).  The translation emits no `defP`, so a binder may be opaque or transparent at any
block.

`Ctx.isSelf G x` decides whether `x` is bound by a self binder.  `Ctx.Rel.ty_plain` reads the type
of a plain variable in `Δ`.  `Ctx.Rel.ty_self` reads a self variable's type as `⟦μ(z. T₀)⟧`, with
`G.lookup x = T₀⟨x⟩`.  Below a self binder `G.lookup` weakens, so `T₀` is the weakened body.

`Ctx.translate` gives every source context a related target context, with every binder opaque
(decision D14).
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- Whether a variable is bound by a self binder `z :ˢ T` of the context. -/
def Ctx.isSelf : Ctx s → BVar s .var → Bool
  | .cons _ _, .here => false                                 -- (G, z : T): a plain binder
  | .consSelf _ _, .here => true                              -- (G, z :ˢ T): a self binder
  | .cons G _, .there y => G.isSelf y                         -- (G, z : T), y older than z
  | .consSelf G _, .there y => G.isSelf y                     -- (G, z :ˢ T), y older than z

/-- `G ≈ Δ` of TR.1: a source context and a target context with the same binders, each target
binder's type the translation of the source binder's. -/
inductive Ctx.Rel : Ctx s → FCp.Ctx s → Prop where           -- G ≈ Δ
  -- Rel-Nil
  | nil : Ctx.Rel .nil .nil
  -- Rel-Var     binders G Δ T, z the new variable
  | var : Ctx.Rel G Δ → Ctx.Rel (G.cons T) (Δ.cons (.opaque T.translate))
  -- Rel-Self    binders G Δ b, T over (s,z), b opaque or transparent at any block
  | self : Ctx.Rel G Δ → b.ty = (Ty.mu T).translate → Ctx.Rel (G.consSelf T) (Δ.cons b)

/-- Renaming commutes with opening a body at a path. -/
theorem Ty.substPath_rename (T : Ty (s₁,x)) (q : Path s₁) (ρ : Rename s₁ s₂) :
    (T.substPath q).rename ρ = (T.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Ty.rename_eq_subst, Ty.substPath_subst, PathSubst.lift_ofRename, ← Ty.rename_eq_subst, Paths.FCdot.Path.subst_ofRename]

/-- Weakening a body under its binder and opening it at that binder gives the body back. -/
theorem Ty.rename_succ_lift_substPath_here (T : Ty (s,x)) :
    (T.rename (Rename.succ.lift)).substPath (.var .here) = T := by
  rw [Ty.rename_eq_subst, Ty.substPath, Ty.subst_subst]
  have : (PathSubst.ofRename ((Rename.succ (s := s) (k := .var)).lift (k := .var))).comp (PathSubst.one (.var .here)) =
      PathSubst.ofRename Rename.id := by
    apply PathSubst.funext'; intro y; rcases y with _ | y <;> rfl
  rw [this, Ty.subst_ofRename_id]

/-- At a plain variable the target type is the translated source type. -/
theorem Ctx.Rel.ty_plain : ∀ {G : Ctx s} {Δ : FCp.Ctx s} {x : BVar s .var}, Ctx.Rel G Δ → G.isSelf x = false →
    Δ.ty x = (G.lookup x).translate
  | _, _, .here, .var (T := T) _, _ => (Ty.translate_weaken T).symm
  | _, _, .here, .self _ _, h => nomatch h
  | _, _, .there y, .var h, hs => by
      show (_ : FCp.Ty _).weaken = (Ty.weaken _).translate
      rw [Ctx.Rel.ty_plain h hs, Ty.translate_weaken]
  | _, _, .there y, .self h _, hs => by
      show (_ : FCp.Ty _).weaken = (Ty.weaken _).translate
      rw [Ctx.Rel.ty_plain h hs, Ty.translate_weaken]

/-- At a self variable the target type is `⟦μ(z. T₀)⟧` for a body `T₀` that opens at the variable
to the source type. -/
theorem Ctx.Rel.ty_self : ∀ {G : Ctx s} {Δ : FCp.Ctx s} {x : BVar s .var}, Ctx.Rel G Δ → G.isSelf x = true →
    ∃ T₀ : Ty (s,x), Δ.ty x = (Ty.mu T₀).translate ∧ G.lookup x = T₀.substPath (.var x)
  | _, _, .here, .var _, h => nomatch h
  | _, _, .here, .self (T := T) (b := b) _ hb, _ => by
      refine ⟨T.rename Rename.succ.lift, ?_, (Ty.rename_succ_lift_substPath_here T).symm⟩
      show b.ty.weaken = FCp.Ty.mu ((T.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
      rw [hb, Ty.telAt_rename]; rfl
  | _, _, .there y, .var h, hs => by
      obtain ⟨T₀, e₁, e₂⟩ := Ctx.Rel.ty_self h hs
      refine ⟨T₀.rename Rename.succ.lift, ?_, ?_⟩
      · show (_ : FCp.Ty _).weaken = FCp.Ty.mu ((T₀.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
        rw [e₁, Ty.telAt_rename]; rfl
      · show (Ty.weaken _) = _
        rw [e₂, Ty.weaken, Ty.substPath_rename]; rfl
  | _, _, .there y, .self h _, hs => by
      obtain ⟨T₀, e₁, e₂⟩ := Ctx.Rel.ty_self h hs
      refine ⟨T₀.rename Rename.succ.lift, ?_, ?_⟩
      · show (_ : FCp.Ty _).weaken = FCp.Ty.mu ((T₀.rename Rename.succ.lift).telAt (Rename.succ.lift.var .here))
        rw [e₁, Ty.telAt_rename]; rfl
      · show (Ty.weaken _) = _
        rw [e₂, Ty.weaken, Ty.substPath_rename]; rfl

/-- The target context of a source context, every binder opaque (D14). -/
def Ctx.translate : Ctx s → FCp.Ctx s                         -- D14
  | .nil => .nil                                              -- [] ↦ []
  | .cons G T => .cons G.translate (.opaque T.translate)                    -- z : T ↦ z : opaque ⟦T⟧
  | .consSelf G T => .cons G.translate (.opaque (Ty.mu T).translate)        -- z :ˢ T ↦ z : opaque ⟦μ(z. T)⟧

/-- Every source context is related to its translation. -/
theorem Ctx.rel_translate : ∀ (G : Ctx s), Ctx.Rel G G.translate
  | .nil => .nil
  | .cons G _ => .var (Ctx.rel_translate G)
  | .consSelf G _ => .self (Ctx.rel_translate G) rfl

end PDot.Source
