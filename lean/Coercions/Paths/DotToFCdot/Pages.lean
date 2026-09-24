import Coercions.Paths.DotToFCdot.Examples
import Coercions.Paths.FCdot.Examples

/-!
# The P3 pages on the target side (P3.3 and P3.4)

Each source page of `DotMNF/Examples.lean` after X4 gets its target facts
here, one namespace per example.  E10 and P2e read X2 and X1 and have no
second source page.  The kernel decides the facts: a checker verdict
`checkTm` or `checkPath` on the image, an erasure equation, or an equation
between computed images.  The typings are read off a verdict by
`FCdot.checkTm_sound`.  The equations `E1p_erase_E1` and `E4p_erase_E4` hold
by `rfl`, since erasure drops types and the hop changes no runtime term.
`E9_forLet` is an instance of `Binding.forLet_snglOf`.  The two `σ_typed`
type a store from checker verdicts through `FCdot.Examples.value_of_check`.

* `E1p`: bad bounds under a lambda at the path `w.f`.  The body's context has
  no block for `w.f`, and `w.f` has a path image through the `∋ᵛ f` of the
  parameter's declared type.  Y5 of `FCdot/Examples.lean` is the hand-written
  twin.  It lists the bound before `∋ᵛ`, where `Ty.translate` lists `∋`, `∋ᵛ`,
  bound, so the two terms differ in their indices.
* `E2p`: a path-keyed block whose witness names its own path.
* `E3p`: two propositions about one block name.
* `E4p`: the counterexample of §1 at a path.
* `E5p`: an object returned from a function and selected through a stable
  field.
* `E6p`: a field typed at a member of its own literal's stable field.
* `E7p`: an alias cycle below a stable field.  Y3 is the hand-written store.
* `E8p`: refining an abstract type at a path, by `And₁` and by `And₂`.
* `E9`: a `let` at a singleton.  The checker binds `y` at the forwarding node
  to `q`.  Over the store of `q` and `x`, `y ∙ B`, `x.a ∙ B` and `q ∙ B` have
  one definition (decision 39).
* `E10`: X2's literal.  The translated self lists no `∋ᵛ`, and `x.a` has no
  path image at any index of its telescope.
* `E11`: a stable field and a forwarding field in one literal.  Over the store
  the forwarding child of `b` reaches `z`'s block, and only `x.a` is a node.
* `P2e`: X1's literal.  The cycle `x.c ∙ A`, `x ∙ B` is resolved in the
  translated self context.
* `P3e`: pDOT's bad bounds through a computation field.  The literal checks,
  and `x.a` has no path image.  The source side proves `P3e_noVfld`.

All names in the statements are those of `DotMNF.Examples`, written qualified,
since this namespace declares labels of its own and `lc` differs in value.
-/

namespace Paths
namespace DotMNF
namespace TargetExamples

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

/-! ## E1p -/

namespace E1p

theorem E1p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E1p.translate
      (Ty.all Examples.E1p_Dom Examples.E1p_Res).translate = true := by
  decide +kernel

theorem E1p_typed :
    FCdot.Tm.HasType FCdot.Ctx.nil Examples.E1p.translate
      (Ty.all Examples.E1p_Dom Examples.E1p_Res).translate :=
  FCdot.checkTm_sound E1p_checks

theorem E1p_erase : ⌊Examples.E1p.translate⌋ = Tm.erase Examples.E1p_term := by decide +kernel

/-- The hop changes no runtime term: E1p and E1 erase alike. -/
theorem E1p_erase_E1 :
    Tm.erase Examples.E1p_term
      = Tm.erase (.val (.lam Examples.E1Dom (.let (.path .here) (.path .here)))) :=
  rfl

/-- The parameter's type translates to `μ[∋ f, ∋ᵛ f, self ∙ f ⊑ {A : ⊤..⊥}]`, with `∋ᵛ`
second.  P1's hand-written Y5 lists the bound second, so its indices differ. -/
theorem Dom_translate :
    (Examples.E1p_Dom : Ty []).translate
      = .obj (((FCdot.Telescope.nil ▹ ∋ Examples.lf) ▹ ∋ᵛ Examples.lf) ▹
        ((FCdot.Path.var .here) ∙ Examples.lf ⊑
          (Ty.typ Examples.lA .top .bot : Ty ([],x)).translate)) := rfl

/-- The context of the lambda body has no block for `w.f`. -/
theorem E1p_no_block :
    Examples.E1p_Ctx1.translate.lookupBlock (.sel (.var .here) Examples.lf) = none := by
  decide +kernel

/-- `w.f` still has a path image, through the `∋ᵛ f` at index 1 of the parameter's
declared type. -/
theorem E1p_path :
    FCdot.synthPath Examples.E1p_Ctx1.translate (.sel (.var .here) Examples.lf 1)
      = some (FCdot.Ty.sel (.var .here) Examples.lf) := by decide +kernel

end E1p

/-! ## E2p -/

namespace E2p

theorem E2p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E2p.translate Ty.top.translate = true := by
  decide +kernel

theorem E2p_erase : ⌊Examples.E2p.translate⌋ = Tm.erase Examples.E2p_term := by decide +kernel

/-- The block at `x.c`, in the translated self context, mentions `x.c` itself. -/
theorem E2p_block :
    (Ctx.nil.consSelf Examples.E2p_outerD Examples.E2p_outerT).translate.lookupDefP
        (.sel (.var .here) Examples.lc) Examples.lA
      = some (FCdot.Ty.pi (FCdot.Ty.sel (.sel (.var .here) Examples.lc) Examples.lA)
          (FCdot.Ty.sel (.sel (.var (.there .here)) Examples.lc) Examples.lA)) := by
  decide +kernel

end E2p

/-! ## E3p -/

namespace E3p

theorem E3p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E3p.translate
      (Ty.all Examples.E3p_Dom (.all Examples.E3T2 Examples.E3T1)).translate = true := by
  decide +kernel

theorem E3p_erase : ⌊Examples.E3p.translate⌋ = Tm.erase Examples.E3p_term := by decide +kernel

end E3p

/-! ## E4p -/

namespace E4p

theorem E4p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E4p.translate Examples.E4p_ty.translate = true := by
  decide +kernel

theorem E4p_erase : ⌊Examples.E4p.translate⌋ = Tm.erase Examples.E4p_term := by decide +kernel

/-- The hop changes no runtime term. -/
theorem E4p_erase_E4 :
    Tm.erase Examples.E4p_term
      = Tm.erase (.val (.lam Examples.E4X (.val (.lam Examples.E4S (.val (.lam Examples.E4Int
          (.let (.val (.lam (.sel (.var (.there .here)) Examples.lA) (.path .here)))
            (.app .here (.there .here)))))))) : Tm []) := rfl

/-- The path image is a cast over a `sel` at the label `a`. -/
def isSelAt (a : Label) : FCdot.PathCo s → Bool
  | .cast (.sel _ b _) _ => b == a
  | _ => false

/-- The prefix of the two bounds is the stable field `x.f`: the path image of `xf4` is a
cast over a `sel` at `f`. -/
theorem E4p_prefix : isSelAt Examples.lf Examples.E4p_xf4.translatePath = true := by
  decide +kernel

end E4p

/-! ## E5p -/

namespace E5p

theorem E5p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E5p.translate
      (Ty.all Examples.E5AT (.sel (.var .here) Examples.lA)).translate = true := by
  decide +kernel

theorem E5p_erase : ⌊Examples.E5p.translate⌋ = Tm.erase Examples.E5p_term := by decide +kernel

/-- `r.o` is a stable path in the client, and its image checks at `μ(u. {a : w.A})`. -/
theorem roPath_checks :
    FCdot.checkPath Examples.E5p_Ctxr.translate Examples.E5p_roPath.translatePath
      Examples.E5p_oTy.translate = true := by decide +kernel

end E5p

/-! ## E6p -/

namespace E6p

theorem E6p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E6p.translate
      (Ty.all Examples.E6Int (.mu Examples.E6p_outerT)).translate = true := by
  decide +kernel

theorem E6p_erase : ⌊Examples.E6p.translate⌋ = Tm.erase Examples.E6p_term := by decide +kernel

/-- The self's block has a node at `x.c` whose `T` is `Int`, and `v` is plain. -/
theorem E6p_block :
    Examples.E6p_Ctxx.translate.lookupDefP (.sel (.var .here) Examples.lc) Examples.lT
        = some (Examples.E6Int : Ty (([],x),x)).translate ∧
      Examples.E6p_outerT.valLabels = [Examples.lc] := by
  decide +kernel

end E6p

/-! ## E7p -/

namespace E7p

theorem E7p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E7p_lit.translate
      (Ty.mu Examples.E7p_outerT).translate = true := by
  decide +kernel

theorem E7p_erase :
    ⌊Examples.E7p_lit.translate⌋ = Tm.erase (.val (.obj Examples.E7p_outerD)) := by
  decide +kernel

/-- The translated self context of the literal. -/
def Γx : FCdot.Ctx ([],x) := (Ctx.nil.consSelf Examples.E7p_outerD Examples.E7p_outerT).translate

/-- Both names of the cycle resolve to `⊤`, in the translated self context. -/
theorem E7p_resolve :
    Γx.resolve (FCdot.Ty.sel (.sel (.var .here) Examples.lc) Examples.lA) = ⊤ ∧
      Γx.resolve (FCdot.Ty.sel (.sel (.var .here) Examples.lc) Examples.lB) = ⊤ := by
  decide +kernel

/-- The cycle runs through the stable field `c`: `c` is the one stable label of the outer
literal, and both names are selections through `x.c`. -/
theorem E7p_stable : Examples.E7p_outerT.valLabels = [Examples.lc] := by decide +kernel

end E7p

/-! ## E8p -/

namespace E8p

theorem E8p_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E8p.translate Examples.E8p_ty.translate = true := by
  decide +kernel

theorem E8p_erase : ⌊Examples.E8p.translate⌋ = Tm.erase Examples.E8p_term := by decide +kernel

/-- The refinement's left operand is a self-bound proposition at the path `x.f`. -/
theorem Ref_translate :
    (Examples.E8p_Ref (.here : BVar ([],x) .var)).translate
      = .obj ((FCdot.Telescope.nil ▹ ⊑ (FCdot.Ty.sel (.sel (.var (.there .here)) Examples.lf)
          Examples.lA))
          ++ (Ty.fld Examples.la (.top : Ty ([],x))).tel) := by decide +kernel

theorem E8p2_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E8p2.translate Examples.E8p_ty.translate = true := by
  decide +kernel

theorem E8p2_erase : ⌊Examples.E8p2.translate⌋ = Tm.erase Examples.E8p_term := by decide +kernel

end E8p

/-! ## E9 -/

namespace E9

theorem E9_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E9.translate Ty.top.translate = true := by
  decide +kernel

theorem E9_typed : FCdot.Tm.HasType FCdot.Ctx.nil Examples.E9.translate Ty.top.translate :=
  FCdot.checkTm_sound E9_checks

theorem E9_erase : ⌊Examples.E9.translate⌋ = Tm.erase Examples.E9_term := by decide +kernel

/-- The let at the singleton translates to the opaque `let` (decision 32), and
the checker binds `y` at the forwarding node to `q` (`Binding.forLet`). -/
theorem E9_forLet :
    FCdot.Binding.forLet (Ty.sngl (.var (.there .here)) : Ty (([],x),x)).translate
      = FCdot.Binding.fwdAt (.var (.there .here)) :=
  FCdot.Binding.forLet_snglOf (.var (.there .here))

/-! ### The one definition, over the store of `q` and `x` -/

def qv : FCdot.Value [] :=
  .obj Examples.E9_qBody.witnesses
    (Examples.E9_qDefsTy.translateFields .here Examples.E9_qBody.literalTy.weaken 0)
def xv : FCdot.Value ([],x) :=
  .obj Examples.E9_xBody.witnesses
    (Examples.E9_xDefsTy.translateFields .here Examples.E9_xBody.literalTy.weaken 0)

theorem qv_typed : FCdot.Value.HasType FCdot.Ctx.nil qv Examples.E9_qBody.literalTy :=
  FCdot.Examples.value_of_check (by decide +kernel)

def Γq : FCdot.Ctx ([],x) :=
  FCdot.Ctx.nil.cons (.transparent Examples.E9_qBody.literalTy (qv.weaken.blocksAt (.var .here)))

theorem xv_typed : FCdot.Value.HasType Γq xv Examples.E9_xBody.literalTy :=
  FCdot.Examples.value_of_check (by decide +kernel)

def Γσ : FCdot.Ctx (([],x),x) :=
  Γq.cons (.transparent Examples.E9_xBody.literalTy (xv.weaken.blocksAt (.var .here)))
def σ : FCdot.Store (([],x),x) := .cons (.cons .nil qv) xv

theorem σ_typed : FCdot.Store.Typed σ Γσ :=
  .cons (.cons .nil trivial qv_typed) trivial xv_typed

/-- The body's `y`, bound at the forwarding node to `q`. -/
def Γy : FCdot.Ctx ((([],x),x),x) := Γσ.cons (FCdot.Binding.fwdAt (.var (.there .here)))

/-- **E9.**  `y ∙ B`, `x.a ∙ B` and `q ∙ B` have one definition, `N`. -/
theorem E9_one_definition :
    Γy.lookupDefP (.var .here) Examples.lB = some (Examples.E9_N : Ty (((([],x),x),x))).translate ∧
      Γy.lookupDefP (.sel (.var (.there .here)) Examples.la) Examples.lB
        = some (Examples.E9_N : Ty (((([],x),x),x))).translate ∧
      Γy.lookupDefP (.var (.there (.there .here))) Examples.lB
        = some (Examples.E9_N : Ty (((([],x),x),x))).translate := by
  decide +kernel

/-- `x.a` is plain and no node: the forwarding serves resolution only (decision 24). -/
theorem E9_xa_plain :
    Examples.E9_xBody.valLabels = [] ∧ Γσ.nodeBlock (.sel (.var .here) Examples.la) = none := by
  decide +kernel

end E9

/-! ## E10, X2's literal on the target side -/

/-- The telescope length of a translated self binder's type. -/
def telLen {s : Sig} : FCdot.Ty s → Nat
  | .obj tel => tel.length
  | _ => 0

namespace E10

def lit : HasTy Ctx.nil (.val (.obj Examples.X2_Defs)) (.mu Examples.X2_Self) := Examples.X2_lit

theorem E10_checks :
    FCdot.checkTm FCdot.Ctx.nil lit.translate (Ty.mu Examples.X2_Self).translate = true := by
  decide +kernel
theorem E10_erase : ⌊lit.translate⌋ = Tm.erase (.val (.obj Examples.X2_Defs)) := by decide +kernel

/-- The field `a` is plain: the self lists no `∋ᵛ`, and `x.a` has no path image. -/
theorem E10_plain :
    (Examples.X2_Self : Ty ([],x)).valLabels = [] ∧
      (Examples.X2_Ctx (Γ := Ctx.nil)).translate.lookupValFieldsP (.var .here) = some [] := by
  decide +kernel
theorem E10_no_path :
    ∀ i < 4, FCdot.synthPath (Examples.X2_Ctx (Γ := Ctx.nil)).translate
      (.sel (.var .here) Examples.la i) = none := by
  decide +kernel

/-- X2's self telescope has 2 entries, so `E10_no_path` covers every index of it. -/
theorem E10_len : telLen ((Examples.X2_Ctx (Γ := Ctx.nil)).translate.lookupTy .here) = 2 := by
  decide +kernel

end E10

/-! ## E11 -/

namespace E11

theorem E11_labels :
    Examples.E11_xBody.fieldLabels = [Examples.lb, Examples.la] ∧
      Examples.E11_xBody.valLabels = [Examples.la] := by decide +kernel

/-- The block: an object child at `a`, a forwarding child at `b`. -/
theorem E11_blocks :
    Examples.E11_xBody.blocks Examples.E11_xDefs
      = .obj Examples.E11_xBody.witnesses [Examples.lb, Examples.la] [Examples.la]
      ((FCdot.Children.nil.cons Examples.la ((FCdot.Block.obj
          (Ty.typ Examples.lA (.top : Ty ((([],x),x),x)) .top).witnesses [] []
          .nil).substPath (.sel (.var .here) Examples.la))).cons Examples.lb
          (.fwd (.var (.there .here)))) := by
  decide +kernel

theorem E11_coherent :
    Examples.E11_xBody.blocks Examples.E11_xDefs = (FCdot.Value.obj Examples.E11_xBody.witnesses
      (Examples.E11_xDefsTy.translateFields .here
        Examples.E11_xBody.literalTy.weaken 0)).blockSelf := by
  decide +kernel

theorem xLit_checks :
    FCdot.checkTm Examples.E11_Γz.translate Examples.E11_xLit.translate
      (Ty.mu Examples.E11_xBody).translate = true := by
  decide +kernel

theorem E11_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.E11.translate Ty.top.translate = true := by
  decide +kernel

theorem E11_erase : ⌊Examples.E11.translate⌋ = Tm.erase Examples.E11_term := by decide +kernel

/-! ### Over the store of `z` and `x` -/

def zv : FCdot.Value [] :=
  .obj Examples.E11_zBody.witnesses
    (Examples.E11_zDefsTy.translateFields .here Examples.E11_zBody.literalTy.weaken 0)
def xv : FCdot.Value ([],x) :=
  .obj Examples.E11_xBody.witnesses
    (Examples.E11_xDefsTy.translateFields .here Examples.E11_xBody.literalTy.weaken 0)

theorem zv_typed : FCdot.Value.HasType FCdot.Ctx.nil zv Examples.E11_zBody.literalTy :=
  FCdot.Examples.value_of_check (by decide +kernel)
def Γzσ : FCdot.Ctx ([],x) :=
  FCdot.Ctx.nil.cons (.transparent Examples.E11_zBody.literalTy (zv.weaken.blocksAt (.var .here)))
theorem xv_typed : FCdot.Value.HasType Γzσ xv Examples.E11_xBody.literalTy :=
  FCdot.Examples.value_of_check (by decide +kernel)
def Γσ : FCdot.Ctx (([],x),x) :=
  Γzσ.cons (.transparent Examples.E11_xBody.literalTy (xv.weaken.blocksAt (.var .here)))

theorem σ_typed : FCdot.Store.Typed (.cons (.cons .nil zv) xv) Γσ :=
  .cons (.cons .nil trivial zv_typed) trivial xv_typed

/-- **E11.**  `x.b` has `z`'s block, `x.b ∙ C` is `z ∙ C`, `x.a` is a node and `x.b` is not. -/
theorem E11_store :
    Γσ.lookupBlock (.sel (.var .here) Examples.lb) = Γσ.lookupBlock (.var (.there .here)) ∧
      Γσ.lookupDefP (.sel (.var .here) Examples.lb) Examples.lC = some ⊤ ∧
      (Γσ.nodeBlock (.sel (.var .here) Examples.la)).isSome = true ∧
      Γσ.nodeBlock (.sel (.var .here) Examples.lb) = none := by
  decide +kernel

end E11

/-! ## P2e, pDOT Sec. 2.2, the length-two path, resolved in the translated self context -/

namespace P2e

/-- The self binder of X1's literal, translated: transparent at `X1_Self.blocks X1_Defs`. -/
def Γx : FCdot.Ctx ([],x) := (Ctx.nil.consSelf Examples.X1_Defs Examples.X1_Self).translate

/-- `x.c ∙ A` is `x ∙ B` and `x ∙ B` is `x.c ∙ A`: the table reads both. -/
theorem P2e_defs :
    Γx.lookupDefP (.sel (.var .here) Examples.X1_lc) Examples.lA
        = some (FCdot.Ty.sel (.var .here) Examples.lB) ∧
      Γx.lookupDefP (.var .here) Examples.lB =
        some (FCdot.Ty.sel (.sel (.var .here) Examples.X1_lc) Examples.lA) := by
  decide +kernel

/-- The chain is cyclic, and alias-tolerant resolution sends both names to `⊤`. -/
theorem P2e_resolve :
    Γx.resolve (FCdot.Ty.sel (.sel (.var .here) Examples.X1_lc) Examples.lA) = ⊤ ∧
      Γx.resolve (FCdot.Ty.sel (.var .here) Examples.lB) = ⊤ := by
  decide +kernel

/-- The erasure of X1's literal. -/
theorem P2e_erase :
    ⌊(Examples.X1_lit (Γ := Ctx.nil)).translate⌋ = Tm.erase (.val (.obj Examples.X1_Defs)) := by
  decide +kernel

end P2e

/-! ## P3e, pDOT Sec. 2.3: the literal is accepted, the elimination is refused -/

namespace P3e

theorem lit_checks :
    FCdot.checkTm FCdot.Ctx.nil Examples.P3e_lit.translate (Ty.mu Examples.P3e_TP).translate
      = true := by
  decide +kernel

/-- No field is stable, so the translated self lists no `∋ᵛ`. -/
theorem P3e_plain :
    Examples.P3e_TP.valLabels = [] ∧
      Examples.P3e_Γs.translate.lookupValFieldsP (.var .here) = some [] := by
  decide +kernel

/-- `x.a` has no path image at any index of the self's telescope. -/
theorem P3e_no_path :
    ∀ i < 6, FCdot.synthPath Examples.P3e_Γs.translate (.sel (.var .here) Examples.la i) = none := by
  decide +kernel

/-- The self's telescope has 4 entries, so `P3e_no_path` covers every index of it. -/
theorem P3e_len : telLen (Examples.P3e_Γs.translate.lookupTy .here) = 4 := by decide +kernel

end P3e

end TargetExamples
end DotMNF
end Paths
