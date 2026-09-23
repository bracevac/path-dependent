import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.DotMNF.Examples

/-!
# The gDOT acceptance tests, and P1e (P3.1, P3.2, P3.3)

**Test B, gDOT Sec. 3 refuted.**  `ν(x. {A = S})` has no type
`μ(x. {A : ⊤..⊥})` in the empty source context, for any `S`
(`acceptance_gdot3`), and no closed literal has that type
(`acceptance_gdot3_any`).  The proof reads no source inversion (decisions 15
and 35).  It translates the derivation (`HasTy.translate_typed`), peels the
casts of the image down to the literal (`translate_tower`, `CastTower.typed`),
allocates the literal as the one entry of a typed store, reads `⊤ ≤ x ∙ A` and
`x ∙ A ≤ ⊥` off the cast atom at the store binder by `LeCo.member`, and refutes
the composite by `Store.Typed.no_top_le_bot` (`no_literal_at_bad`).  A closed
term at the bad type exists, `diverging_at_bad_bounds` on X2's literal.  Its
run reaches `o.a` in three steps and then steps to itself (`div_reach`,
`div_loop`), so it never allocates a literal at the bad type.  That is why the
test speaks of literals.

**Test A, gDOT Fig. 2.**  The source is the page `Fig2` of
`DotMNF/Examples.lean`.  The kernel decides every fact here: a checker verdict
`checkTm`, `checkLe` or `checkPath` on the image, a block equation, a
declaration lookup, or an erasure equation.  `acceptance_fig2` is the checker
verdict on the whole program at `⊤`, `acceptance_fig2_typed` its typing by
`FCdot.checkTm_sound`, and the two erasure facts state the same equation by
`decide +kernel` and by `HasTy.translate_erase`.

**P1e, pDOT Fig. 1.**  The page `Fig1` of `DotMNF/Examples.lean`, Fig2 with
`tpe : p.types.Type`, gets the same facts under `Fig1_` (decision 41).
`Fig1_abs_is_abstract` reads the view of `types`, which P1e shares with Fig2,
so its statement is that of `Fig2_abs_is_abstract`.

All names of source pages and labels are those of `DotMNF.Examples`, written
qualified.
-/

namespace Paths
namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

/-! ## Test B: gDOT Sec. 3 -/

/-- A target term that is an object literal under casts. -/
inductive CastTower {s : Sig} : FCdot.Tm s → Prop where
  | lit : CastTower (.val (.obj W F))
  | cast : CastTower t → CastTower (.cast t e)

/-- A typed cast tower is a typed literal and one coercion out of its type. -/
theorem CastTower.typed {s : Sig} {Γ : FCdot.Ctx s} {t : FCdot.Tm s} {T : FCdot.Ty s}
    (ht : CastTower t) (h : FCdot.Tm.HasType Γ t T) :
    ∃ (W : FCdot.Witnesses (s,x)) (F : FCdot.Fields (s,x)) (P : FCdot.Ty s) (e : FCdot.LeCo s),
      FCdot.Value.HasType Γ (.obj W F) P ∧ FCdot.LeCo.HasType Γ e P T := by
  induction ht generalizing T with
  | lit => cases h with | val hv => exact ⟨_, _, _, _, hv, .refl⟩
  | cast _ ih =>
      cases h with
      | cast h1 he =>
          obtain ⟨W, F, P, e, hv, he0⟩ := ih h1
          exact ⟨W, F, P, _, hv, .trans he0 he⟩

/-- The image of a source derivation at an object literal is a cast tower.
Only `obj` and `sub` conclude at `.val (.obj d)`. -/
theorem translate_tower {s : Sig} {Γ : Ctx s} :
    ∀ {d : Defs (s,x)} {T : Ty s} (h : HasTy Γ (.val (.obj d)) T), CastTower h.translate
  | _, _, .obj _ _ => .cast .lit
  | _, _, .sub h _ => .cast (translate_tower h)

/-- The telescope of `μ(x. {A : ⊤..⊥})`, translated. -/
theorem bad_translate (A : Label) :
    (Ty.mu (.typ A (.top : Ty ([],x)) .bot)).translate
      = .obj (((FCdot.Telescope.nil ▹ (⊤ ⊑ (FCdot.Path.var .here) ∙ A))
          ▹ ((FCdot.Path.var .here) ∙ A ⊑ ⊥))) := rfl

/-- Any closed literal typed at a type whose translation is `μ[⊤ ⊑ self ∙ A, self ∙ A ⊑ ⊥]`
gives, once allocated, a typed store that proves `⊤ ≤ ⊥`. -/
theorem no_literal_at_bad {A : Label} {W : FCdot.Witnesses ([],x)} {F : FCdot.Fields ([],x)}
    {P : FCdot.Ty []} {e : FCdot.LeCo []}
    (hv : FCdot.Value.HasType .nil (.obj W F) P)
    (he : FCdot.LeCo.HasType .nil e P (Ty.mu (.typ A (.top : Ty ([],x)) .bot)).translate) :
    False := by
  have hσ : FCdot.Store.Typed (.cons .nil (.obj W F))
      (.cons .nil (.transparent P ((FCdot.Value.obj W F).weaken.blocksAt (.var .here)))) :=
    .cons .nil trivial hv
  rw [bad_translate] at he
  have ha := FCdot.Atom.HasType.cast (FCdot.Atom.HasType.var (Γ := .cons .nil
      (.transparent P ((FCdot.Value.obj W F).weaken.blocksAt (.var .here)))) (x := .here))
    (he.weaken (.transparent P ((FCdot.Value.obj W F).weaken.blocksAt (.var .here))))
  have h0 := FCdot.LeCo.HasType.member ha .refl (i := 0) (.there .here)
  have h1 := FCdot.LeCo.HasType.member ha .refl (i := 1) .here
  exact hσ.no_top_le_bot ⟨_, .trans h0 h1⟩

/-- **Acceptance test B.**  gDOT's Sec. 3 derivation, `ε ⊢ νx.{A = S} : μx.{A >: ⊤ <: ⊥}`,
has no counterpart in the source, for any `S`. -/
theorem acceptance_gdot3 {A : Label} {S : Ty ([],x)} :
    ¬ Nonempty (HasTy .nil (.val (.obj (.typ A S))) (.mu (.typ A .top .bot))) := by
  rintro ⟨h⟩
  obtain ⟨W, F, P, e, hv, he⟩ :=
    CastTower.typed (translate_tower h) (HasTy.translate_typed h .nil)
  exact no_literal_at_bad hv he

/-- The same for every closed literal, whatever its definitions. -/
theorem acceptance_gdot3_any {A : Label} {d : Defs ([],x)} :
    ¬ Nonempty (HasTy .nil (.val (.obj d)) (.mu (.typ A .top .bot))) := by
  rintro ⟨h⟩
  obtain ⟨W, F, P, e, hv, he⟩ :=
    CastTower.typed (translate_tower h) (HasTy.translate_typed h .nil)
  exact no_literal_at_bad hv he

/-! ### A closed term at the bad type exists, and it never allocates a literal there

`let o = ν(x. {a = x.a}) in let y = o.a in y`, X2's literal.  `o.a` diverges,
so the term never reaches a value at the bad type.  The theorems above are
about literals, and this is why they cannot be about terms. -/

/-- `ν(x. {a = x.a})` at `μ(x. {a : {A : ⊤..⊥}})`, closed. -/
def div_x2lit : HasTy Ctx.nil (.val (.obj Examples.X2_Defs)) (.mu Examples.X2_Self) :=
  Examples.X2_lit

def div_ctxO : Ctx ([],x) := Ctx.nil.cons (.mu Examples.X2_Self)

/-- `o.a : {A : ⊤..⊥}` by `Rec-E` and `{}-E`. -/
def div_oa : HasTy div_ctxO (.proj .here Examples.la) (.typ Examples.lA .top .bot) :=
  .proj (HasTy.recE (T := .fld Examples.la (.typ Examples.lA .top .bot)) .var .fld)

def div_ctxY : Ctx (([],x),x) := div_ctxO.cons (.typ Examples.lA .top .bot)

/-- `y : μ(y. {A : ⊤..⊥})` by `Rec-I` at the variable. -/
def div_yMu : HasTy div_ctxY (.path .here) (.mu (.typ Examples.lA .top .bot)) :=
  .recI (T := .typ Examples.lA .top .bot) .var .typ

/-- A closed term at `μ(y. {A : ⊤..⊥})`. -/
def diverging_at_bad_bounds :
    HasTy Ctx.nil
      (.let (.val (.obj Examples.X2_Defs)) (.let (.proj .here Examples.la) (.path .here)))
      (.mu (.typ Examples.lA .top .bot)) :=
  .let div_x2lit (.let div_oa div_yMu (.mu (.typ .top .bot) .typ)) (.mu (.typ .top .bot) .typ)

/-- The program of `diverging_at_bad_bounds`. -/
def div_tm : Tm [] :=
  .let (.val (.obj Examples.X2_Defs)) (.let (.proj .here Examples.la) (.path .here))

/-- The state after the literal is allocated and the inner `let` is pushed. -/
def div_stLoop : State ([],x) :=
  ⟨.cons .nil (.obj Examples.X2_Defs), .cons .nil (.path .here), .proj .here Examples.la⟩

/-- Three steps reach it: push, allocate, push. -/
theorem div_reach : Steps (⟨.nil, .nil, div_tm⟩ : State []) div_stLoop :=
  .tail (.tail (.tail .refl .let) .alloc) .let

/-- And it steps to itself: `o.a` reduces to `o.a`. -/
theorem div_loop : Step div_stLoop div_stLoop := by
  have h := Step.proj (σ := div_stLoop.σ) (K := div_stLoop.K) (x := .here) (a := Examples.la)
    (d := Examples.X2_Defs) (t := .proj .here Examples.la) rfl rfl
  exact h

/-! ## Test A: gDOT Fig. 2 -/

theorem Fig2_pBody_labels :
    Examples.Fig2_pBody.fieldLabels = [Examples.X4_lsymbols, Examples.Fig2_ltypes] ∧
    Examples.Fig2_pBody.valLabels = [Examples.X4_lsymbols, Examples.Fig2_ltypes] := by
  decide +kernel

theorem Fig2_pBlocks :
    Examples.Fig2_pBody.blocks Examples.Fig2_pDefs = (FCdot.Value.obj Examples.Fig2_pBody.witnesses
      (Examples.Fig2_pDefsTy.translateFields .here Examples.Fig2_pBody.literalTy.weaken 0)).blockSelf := by
  decide +kernel

theorem Fig2_pLit_checks :
    FCdot.checkTm Examples.Fig2_Γo.translate Examples.Fig2_pLit.translate
      (Ty.mu Examples.Fig2_pBody).translate = true := by
  decide +kernel

theorem Fig2_crossUpperT_checks :
    FCdot.checkLe Examples.Fig2_Γt.translate Examples.Fig2_crossUpperT.translate
      (Examples.X4_Sym (.there .here)).translate
      (Examples.Fig2_SymT (.there (.there .here)) (.there .here)).translate = true := by
  decide +kernel

theorem Fig2_crossUpperC_checks :
    FCdot.checkLe Examples.Fig2_Γc.translate Examples.Fig2_crossUpperC.translate
      (Examples.X4_Sym .here).translate (Examples.Fig2_SymT (.there .here) .here).translate
      = true := by
  decide +kernel

theorem Fig2_pcTypesAbs_checks :
    FCdot.checkPath Examples.Fig2_Γc.translate Examples.Fig2_pcTypesAbs.translatePath
      (Ty.mu (Examples.Fig2_TAbs .here (.there .here))).translate = true := by
  decide +kernel

theorem Fig2_pcSymbolsAbs_checks :
    FCdot.checkPath Examples.Fig2_Γc.translate Examples.Fig2_pcSymbolsAbs.translatePath
      (Ty.mu (Examples.Fig2_YAbs .here (.there .here) (.there (.there .here)))).translate
      = true := by
  decide +kernel

/-- In the abstract view the member `Type` is declared `⊥..⊤`: the view is abstract, not the
exact `⊤..⊤` of the literal. -/
theorem Fig2_abs_is_abstract :
    (Examples.Fig2_TAbs (.here : BVar ((([],x),x),x) .var) (.there .here)).lookupTypDecl
      Examples.X4_lType = some (.bot, .top) := by
  decide +kernel

theorem Fig2_pcAbs_checks :
    FCdot.checkTm Examples.Fig2_Γc.translate Examples.Fig2_pcAbs.translate
      (Ty.mu Examples.Fig2_pAbs).translate = true := by
  decide +kernel

/-- **Acceptance test A.**  The whole program checks at `⊤` in the empty context. -/
theorem acceptance_fig2 :
    FCdot.checkTm FCdot.Ctx.nil Examples.Fig2_prog_ty.translate Ty.top.translate = true := by
  decide +kernel

theorem acceptance_fig2_typed :
    FCdot.Tm.HasType FCdot.Ctx.nil Examples.Fig2_prog_ty.translate Ty.top.translate :=
  FCdot.checkTm_sound acceptance_fig2

/-- The erasures agree, decided. -/
theorem acceptance_fig2_erase :
    ⌊Examples.Fig2_prog_ty.translate⌋ = Tm.erase Examples.Fig2_prog := by
  decide +kernel

/-- The erasures agree, by the theorem. -/
theorem acceptance_fig2_erase' :
    ⌊Examples.Fig2_prog_ty.translate⌋ = Tm.erase Examples.Fig2_prog :=
  HasTy.translate_erase Examples.Fig2_prog_ty

/-! ## P1e: pDOT Fig. 1 -/

theorem Fig1_pBody_labels :
    Examples.Fig1_pBody.fieldLabels = [Examples.X4_lsymbols, Examples.Fig2_ltypes] ∧
    Examples.Fig1_pBody.valLabels = [Examples.X4_lsymbols, Examples.Fig2_ltypes] := by
  decide +kernel

theorem Fig1_pBlocks :
    Examples.Fig1_pBody.blocks Examples.Fig1_pDefs = (FCdot.Value.obj Examples.Fig1_pBody.witnesses
      (Examples.Fig1_pDefsTy.translateFields .here Examples.Fig1_pBody.literalTy.weaken 0)).blockSelf := by
  decide +kernel

theorem Fig1_pLit_checks :
    FCdot.checkTm Examples.Fig2_Γo.translate Examples.Fig1_pLit.translate
      (Ty.mu Examples.Fig1_pBody).translate = true := by
  decide +kernel

theorem Fig1_crossUpperT_checks :
    FCdot.checkLe Examples.Fig1_Γt.translate Examples.Fig1_crossUpperT.translate
      (Examples.X4_Sym (.there .here)).translate
      (Examples.Fig1_SymT (.there (.there .here)) (.there .here)).translate = true := by
  decide +kernel

theorem Fig1_crossUpperC_checks :
    FCdot.checkLe Examples.Fig1_Γc.translate Examples.Fig1_crossUpperC.translate
      (Examples.X4_Sym .here).translate (Examples.Fig1_SymT (.there .here) .here).translate
      = true := by
  decide +kernel

theorem Fig1_pcTypesAbs_checks :
    FCdot.checkPath Examples.Fig1_Γc.translate Examples.Fig1_pcTypesAbs.translatePath
      (Ty.mu (Examples.Fig2_TAbs .here (.there .here))).translate = true := by
  decide +kernel

theorem Fig1_pcSymbolsAbs_checks :
    FCdot.checkPath Examples.Fig1_Γc.translate Examples.Fig1_pcSymbolsAbs.translatePath
      (Ty.mu (Examples.Fig1_YAbs .here (.there .here) (.there (.there .here)))).translate
      = true := by
  decide +kernel

/-- The view of `types`, shared with Fig2, declares `Type : ⊥..⊤`. -/
theorem Fig1_abs_is_abstract :
    (Examples.Fig2_TAbs (.here : BVar ((([],x),x),x) .var) (.there .here)).lookupTypDecl
      Examples.X4_lType = some (.bot, .top) := by
  decide +kernel

theorem Fig1_pcAbs_checks :
    FCdot.checkTm Examples.Fig1_Γc.translate Examples.Fig1_pcAbs.translate
      (Ty.mu Examples.Fig1_pAbs).translate = true := by
  decide +kernel

/-- P1e: the whole program checks at `⊤` in the empty context. -/
theorem acceptance_fig1 :
    FCdot.checkTm FCdot.Ctx.nil Examples.Fig1_prog_ty.translate Ty.top.translate = true := by
  decide +kernel

theorem acceptance_fig1_typed :
    FCdot.Tm.HasType FCdot.Ctx.nil Examples.Fig1_prog_ty.translate Ty.top.translate :=
  FCdot.checkTm_sound acceptance_fig1

/-- The erasures agree, decided. -/
theorem acceptance_fig1_erase :
    ⌊Examples.Fig1_prog_ty.translate⌋ = Tm.erase Examples.Fig1_prog := by
  decide +kernel

/-- The erasures agree, by the theorem. -/
theorem acceptance_fig1_erase' :
    ⌊Examples.Fig1_prog_ty.translate⌋ = Tm.erase Examples.Fig1_prog :=
  HasTy.translate_erase Examples.Fig1_prog_ty

end DotMNF
end Paths
