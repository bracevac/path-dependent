import Coercions.Nominal.FCn.ClassForms
import Coercions.Nominal.FCn.CanonicalExamples

/-!
# Stores of classes through the closed reading (`ClassEx.Store1`, `ClassEx.Forge`)

Two stores read through the canonical forms of the class primitive (`ClassForms`).  A typing is by
the checker over `decide +kernel`, and a fact about resolution or a block is `decide +kernel` over
the computable reading.

- `Store1` holds a module literal `m` with a trait `T`, a class `C` that extends it, an alias `A` of
  `C`, a path field `al` that aliases the module, and a nested literal with a class `D`.  Beside it
  sits a structural literal `i` at the body of `T`.  Resolution stops at each class selection
  (`res_mC`, `res_mA`, `res_alC`, `res_innerD`), and `defAt` answers nothing at `m∙C` (`defP_mC`).
  The constructor's evidence for `C` has an instance view (`Pc_view`), through the path alias too
  (`Pal_view`), and holds a seal (`newC_seals`).  The upcast `m∙C ≤ m∙T` relates two settled
  selections of different labels, so `closed_le_shapes` needs its class alternatives
  (`old_shapes_fail`).  VT-None gives no view at a class selection (`vtnone_excluded`).  The seal
  also puts `i` at `T` with no constructor, and every canonical form holds of it (`forge`,
  `forged_T_view`, `forged_T_seals`).
- `Forge` runs a program whose module declares a trait `T` and a method `forge` that seals its
  argument at `T`.  The checker accepts it and `seal_scope` holds of it (`progF_checks`,
  `progF_scoped`).  Six steps reach a state whose focus is a structural literal sealed at `T`
  (`progF_reaches`).  That path has an instance view and a seal in its form (`forged_view`,
  `forged_seals`), and the conclusion of `seal_scope` fails for it (`forged_unscoped`).
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace ClassEx

/-! ## A module of classes and a structural literal

A module literal `m` declares a trait `T = μ(o : [fld get Π(y:⊤)⊤])`, a class `C` extending it,
`C = μ(o : [fld get Π(y:⊤)⊤, is z∙T])`, an alias `A = z∙C`, a path field `al = z` (an alias of the
module), and a nested literal `inner` with a class `D = μ(o : [fld get Π(y:⊤)⊤])`.  The literal
`i = obj (w : [fld get Π(y:⊤)⊤]) {get = λ(y : ⊤). y}` is stored beside it.  The class in the nested
literal stands for an inner class, which DF-Nest types. -/

namespace Store1

abbrev lT : Label := .typ 0
abbrev lC : Label := .typ 1
abbrev lD : Label := .typ 2
abbrev lA : Label := .typ 3
abbrev lget : Label := .trm 0
abbrev linner : Label := .trm 1
abbrev lal : Label := .trm 2

/-- `Π(y : ⊤) ⊤` -/
abbrev piTT : Ty s := .pi .top .top
/-- `[fld get Π(y : ⊤) ⊤]`: the body of `T` and of `D`, and the instance's telescope. -/
abbrev TelBT : Telescope s := .cons .nil (.fld lget piTT)
abbrev BdT : Ty s := .mu TelBT
/-- The body of `C` under the module's self `w` and its own self `o`: `[fld get Π(y:⊤)⊤, is w∙T]`. -/
abbrev TelBC : Telescope ((s,x),x) := .cons (.cons .nil (.fld lget piTT)) (.is (.sel (.var (.there .here)) lT))
/-- The nested literal's telescope under its self `v`: `[⊥ ⊑ v∙D, v∙D ⊑ μ(o : [fld get Π(y:⊤)⊤])]`. -/
abbrev TelD : Telescope (s,x) := .cons (.cons .nil (.le .bot (.sel (.var .here) lD))) (.le (.sel (.var .here) lD) BdT)
/-- The module's telescope under its self `w`. -/
abbrev TelM : Telescope (s,x) :=
  .cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil
    (.le .bot (.sel (.var .here) lT)))
    (.le (.sel (.var .here) lT) BdT))
    (.le .bot (.sel (.var .here) lC)))
    (.le (.sel (.var .here) lC) (.mu TelBC)))
    (.le (.sel (.var .here) lC) (.sel (.var .here) lA)))
    (.le (.sel (.var .here) lA) (.sel (.var .here) lC)))
    (.fld lal (Ty.sngl (.var .here))))
    (.fld linner (.mu TelD))
/-- The module's definitions under its self `z`. -/
abbrev dsM : Defs (s,x) :=
  .fld (.fld (.typ (.cls (.cls .nil lT BdT) lC (.mu TelBC)) lA (.sel (.var .here) lC))
    lal (.path (.var .here))) linner (.nest TelD (.cls .nil lD BdT))
abbrev modLit : Value [] := .obj TelM dsM
/-- The instance literal, which no constructor built. -/
abbrev dsI : Defs (s,x) := .fld .nil lget (.fn (.lam .top (.path (.var .here))))
abbrev instLit : Value ([],x) := .obj TelBT dsI

abbrev Γ0 : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu TelM) dsM.block)
abbrev σ1 : Store (([],x),x) := (Store.nil.cons modLit).cons instLit
abbrev Γ1 : Ctx (([],x),x) := Γ0.cons (.transparent (.mu TelBT) dsI.block)

abbrev m : Path (([],x),x) := .var (.there .here)
abbrev i : Path (([],x),x) := .var .here
/-- The body of `C` read at `m`: `μ(o : [fld get Π(y:⊤)⊤, is m∙T])`. -/
abbrev TelBCm : Telescope ((([],x),x),x) := .cons (.cons .nil (.fld lget piTT)) (.is (.sel (.var (.there (.there .here))) lT))
abbrev UC : Ty (([],x),x) := .mu TelBCm

theorem modLit_typed : synthValue .nil modLit = some (.mu TelM) := by decide +kernel
theorem instLit_typed : synthValue Γ0 instLit = some (.mu TelBT) := by decide +kernel
/-- The store is typed. -/
theorem σ1_typed : Store.Typed σ1 Γ1 :=
  .obj (.obj .nil (synthValue_sound modLit_typed)) (synthValue_sound instLit_typed)

/-! ### Resolution stops at a class -/

theorem clsAt_mC : Γ1.clsAt m lC = some UC := by decide +kernel
theorem clsAt_mT : Γ1.clsAt m lT = some BdT := by decide +kernel
theorem canon_m : Γ1.canon m = some m := by decide +kernel
theorem res_mC : Γ1.res (.sel m lC) = .sel m lC := Ctx.res_cls (Ctx.clsOf_of_clsAt clsAt_mC)
theorem res_mT : Γ1.res (.sel m lT) = .sel m lT := Ctx.res_cls (Ctx.clsOf_of_clsAt clsAt_mT)
/-- The alias `A = z∙C` unfolds to the class selection and stops there. -/
theorem res_mA : Γ1.res (.sel m lA) = .sel m lC := by decide +kernel
/-- Through the path alias `al = z`: the class is read at the canonical name `m`. -/
theorem clsOf_alC : Γ1.clsOf (.sel (.sel m lal) lC) = some UC := by decide +kernel
theorem res_alC : Γ1.res (.sel (.sel m lal) lC) = .sel (.sel m lal) lC := Ctx.res_cls clsOf_alC
/-- The class of the nested literal. -/
theorem clsOf_innerD : Γ1.clsOf (.sel (.sel m linner) lD) = some BdT := by decide +kernel
theorem res_innerD : Γ1.res (.sel (.sel m linner) lD) = .sel (.sel m linner) lD := Ctx.res_cls clsOf_innerD
/-- The budget counts the one plain definition `A`, not the classes. -/
theorem budgets : Γ1.resBudget = 2 := by decide +kernel

/-! ### The constructor's evidence and N1 -/

/-- `obj (w : [fld get]) (is (fld nil 0 none) (seal m T))`: `μ[fld get] ≤ μ[fld get, is m∙T]`. -/
abbrev morC : Morphism (([],x),x) := .is (.fld .nil 0 .none) (.seal m lT)
abbrev eNewC : LeCo (([],x),x) := .trans (.obj TelBT morC) (.seal m lC)
/-- The literal `i` cast to `m∙C` by the constructor's evidence. -/
abbrev Pc : PathCo (([],x),x) := .cast (.var .here) eNewC

theorem eNewC_typed : LeCo.HasType Γ1 eNewC BdT (.sel m lC) :=
  .trans (.obj (.is (.fld .nil .here .none) (.seal clsAt_mT))) (.seal clsAt_mC)
theorem Pc_typed : PathCo.HasType Γ1 Pc (.sel m lC) := .cast (.var rfl) eNewC_typed

/-- N1 at the constructed instance. -/
theorem Pc_view : ∃ W, PV σ1 Γ1 Pc (.sel m lC) (.inst W) ∧ ViewT Γ1 σ1.erase Pc.path (Γ1.res UC) W :=
  class_view σ1_typed Pc_typed (Ctx.clsOf_of_clsAt clsAt_mC)

/-- The seal acts on the literal's view as the instance view. -/
example : View.applyAtom (.seal m lC) i (varView σ1 .here) = .inst (varView σ1 .here) := rfl

/-! ### Through the path alias: the member read, `lift` at a class selection, and N1 -/

/-- `m.al : sngl m`, by PA-Sel at the path field. -/
theorem mal_typed : PathCo.HasType Γ1 (.sel (.var (.there .here)) lal 6) (Ty.sngl m) := by
  have hAt : (TelM : Telescope ((([],x),x),x)).At 6 (.fld lal (Ty.sngl (.var .here))) := .there .here
  exact PathCo.HasType.sel (Γ := Γ1) (P := .var (.there .here)) (.var rfl) hAt
/-- `π : m.al ≃ m`, by PE-Member at the alias entry of the singleton. -/
abbrev π : PEq (([],x),x) := .member (.sel (.var (.there .here)) lal 6) (.refl (Ty.sngl m)) 0
theorem π_typed : PEq.HasType Γ1 π (.sel m lal) m := .member mal_typed .refl .here
/-- `cast Pc (lift (h. h∙C) (symm π)) : m.al∙C`. -/
abbrev Pal : PathCo (([],x),x) := .cast Pc (.eqToLe (.lift (.sel (.var .here) lC) (.symm π)))
theorem Pal_typed : PathCo.HasType Γ1 Pal (.sel (.sel m lal) lC) :=
  .cast Pc_typed (.eqToLe (.lift (.symm π_typed)))
/-- N1 through the alias: the view moves by `liftAct` at a settled class selection. -/
theorem Pal_view : ∃ W, PV σ1 Γ1 Pal (.sel (.sel m lal) lC) (.inst W) ∧
    ViewT Γ1 σ1.erase Pal.path (Γ1.res UC) W :=
  class_view σ1_typed Pal_typed clsOf_alC
/-- And through the plain alias `A`. -/
theorem PA_view : ∃ W, PV σ1 Γ1 (.cast Pc (.eqToLe (.symm (.defP m lA)))) (.sel m lA) (.inst W) ∧
    ViewT Γ1 σ1.erase Pc.path (Γ1.res UC) W :=
  class_view_res σ1_typed (.cast Pc_typed (.eqToLe (.symm (.defP (by decide +kernel))))) res_mA
    (Ctx.clsOf_of_clsAt clsAt_mC)

/-- A class entry is no definition, so `defAt` answers nothing at `m∙C`. -/
theorem defP_mC : Γ1.defAt m lC = none := Ctx.defAt_none_of_clsAt clsAt_mC
theorem no_defP_mC (W : Ty (([],x),x)) : ¬ EqCo.HasType Γ1 (.defP m lC) (.sel m lC) W := by
  intro h
  cases h with
  | defP h' => rw [defP_mC] at h'; cases h'

/-! ### `Below`, N2 and N3 -/

theorem T_below_T : Below Γ1 m lT (.sel m lT) := .self res_mT canon_m
/-- `C` is below `T`: its body has the self bound `is m∙T`. -/
theorem C_below_T : Below Γ1 m lT (.sel m lC) :=
  .up res_mC (Ctx.clsOf_of_clsAt clsAt_mC) (.is (Ctx.res_mu Γ1 _) .here T_below_T)
/-- N3 at the constructor: its evidence from the literal's type holds a seal of a class below `C`. -/
theorem newC_seals : ∃ F q D, Hnf σ1 Γ1 eNewC BdT (.sel m lC) F ∧ Form.HasSeal F q D ∧ Below Γ1 m lC (.sel q D) :=
  nominal_literal σ1_typed eNewC_typed canon_m (by decide +kernel) (Ctx.res_mu Γ1 _) rfl
/-- And below `T`, through `C`'s declared parent. -/
theorem newC_seals_T : ∃ F, Hnf σ1 Γ1 eNewC BdT (.sel m lC) F ∧
    (Below Γ1 m lT BdT ∨ ∃ q D, Form.HasSeal F q D ∧ Below Γ1 m lT (.sel q D)) :=
  le_below σ1_typed eNewC_typed C_below_T

/-! ### The upcast `m∙C ≤ m∙T` and the class alternatives of `closed_le_shapes` -/

/-- `member m refl 3` reads `m∙C ⊑ μ[fld get, is m∙T]`, then `bound 1` reads the self bound. -/
abbrev eUp : LeCo (([],x),x) := .trans (.member (.var (.there .here)) (.refl (.mu TelM)) 3) (.bound TelBCm 1)
theorem eUp_typed : LeCo.HasType Γ1 eUp (.sel m lC) (.sel m lT) := by
  have hAt : (TelM : Telescope ((([],x),x),x)).At 3 (.le (.sel (.var .here) lC) (.mu TelBC)) :=
    .there (.there (.there (.there .here)))
  have h1 := LeCo.HasType.member (Γ := Γ1) (P := .var (.there .here)) (e := .refl (.mu TelM)) (.var rfl) .refl hAt
  exact .trans h1 (.bound .here)

/-- The disjunction of `closed_le_shapes` without its two class alternatives. -/
def OldShapes (Γ : Ctx s) (γ : PDot.Runtime.Store s) (S T : Ty s) : Prop :=
  Γ.res S = .bot ∨ Γ.res T = .top ∨ Γ.norm S = Γ.norm T ∨
  (∃ S₁ T₁ S₂ T₂, Γ.res S = .pi S₁ T₁ ∧ Γ.res T = .pi S₂ T₂) ∨
  (∃ Tel₁ Tel₂, Γ.res S = .mu Tel₁ ∧ Γ.res T = .mu Tel₂) ∨
  (∃ Tel₁ i X F, Γ.res S = .mu Tel₁ ∧ Tel₁.At i (.is X.weaken) ∧ FormT Γ γ F X T) ∨
  (∃ Tel₂, Γ.res T = .mu Tel₂ ∧ ((∃ Tel₁, Γ.res S = .mu Tel₁) ∨ Telescope.IsOnly Tel₂))

/-- The class alternatives of `closed_le_shapes` are needed: the upcast between two classes relates
two settled selections of different labels. -/
theorem old_shapes_fail : ¬ OldShapes Γ1 σ1.erase (.sel m lC) (.sel m lT) := by
  intro h
  rcases h with h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, _⟩
  · rw [res_mC] at h; cases h
  · rw [res_mT] at h; cases h
  · unfold Ctx.norm at h
    rw [res_mC, res_mT] at h
    have h' : TyO.sel (Γ1.canon m) lC = TyO.sel (Γ1.canon m) lT := h
    injection h' with _ _ e
    cases e
  · rw [res_mC] at h; cases h
  · rw [res_mC] at h; cases h
  · rw [res_mC] at h; cases h
  · rw [res_mT] at h; cases h

/-- N2 at the upcast, the source below `T` by the declared parent. -/
theorem up_below : ∃ F, Hnf σ1 Γ1 eUp (.sel m lC) (.sel m lT) F ∧
    (Below Γ1 m lT (.sel m lC) ∨ ∃ q D, Form.HasSeal F q D ∧ Below Γ1 m lT (.sel q D)) :=
  le_below σ1_typed eUp_typed T_below_T

/-! ### VT-None at a class selection -/

/-- The first and last premises of VT-None hold at the class selection: no alias step, and a live
path. -/
theorem vtnone_premises : Γ1.next (.sel m lC) = none ∧ Live σ1.erase i :=
  ⟨Ctx.next_cls (Ctx.clsOf_of_clsAt clsAt_mC), trivial⟩
/-- The class premise of VT-None excludes the view `none` there, so the view is the instance view
(N1). -/
theorem vtnone_excluded : ¬ ViewT Γ1 σ1.erase i (.sel m lC) .none := by
  intro h
  obtain ⟨W, e, _⟩ := ViewT.cls_inv h (Ctx.clsOf_of_clsAt clsAt_mC)
  cases e

/-! ### A forged instance

Every path at a class body over a typed store extends by the seal to a path at the class, with an
instance view, and every conclusion of N1 to N3 holds of it.  `Pc` above is such a path at `C`. -/

theorem forge {Γ : Ctx s} {P : PathCo s} {p : Path s} {C : Label} {U : Ty s} (hc : Γ.clsAt p C = some U)
    (hP : PathCo.HasType Γ P U) : PathCo.HasType Γ (.cast P (.seal p C)) (.sel p C) := .cast hP (.seal hc)

theorem forge_view {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {p : Path s} {C : Label}
    {U : Ty s} (hc : Γ.clsAt p C = some U) (hP : PathCo.HasType Γ P U) :
    ∃ W, PV σ Γ (.cast P (.seal p C)) (.sel p C) (.inst W) ∧
      ViewT Γ σ.erase P.path (Γ.res U) W :=
  class_view hσ (forge hc hP) (Ctx.clsOf_of_clsAt hc)

/-- The structural literal `i` at the trait `T`, by one seal. -/
theorem forged_T : PathCo.HasType Γ1 (.cast (.var .here) (.seal m lT)) (.sel m lT) := forge clsAt_mT (.var rfl)
theorem forged_T_view : ∃ W, PV σ1 Γ1 (.cast (.var .here) (.seal m lT)) (.sel m lT) (.inst W) ∧
    ViewT Γ1 σ1.erase i (Γ1.res BdT) W := forge_view σ1_typed clsAt_mT (.var rfl)
/-- N3 holds of the forgery: its form is the seal. -/
theorem forged_T_seals : ∃ F q D, Hnf σ1 Γ1 (.seal m lT) BdT (.sel m lT) F ∧ Form.HasSeal F q D ∧
    Below Γ1 m lT (.sel q D) :=
  nominal_literal σ1_typed (.seal clsAt_mT) canon_m (by decide +kernel) (Ctx.res_mu Γ1 _) rfl

end Store1

/-! ## A run that forges an instance

N4 holds of the program and fails after six steps, at a structural literal sealed at a trait that no
constructor built, which N1 and N3 describe as an instance.

    let m = obj (z : [⊥ ⊑ z∙T, z∙T ⊑ BdT, fld forge Π(s : BdT) z∙T])
              {class T = BdT, forge = λ(s : BdT). path (cast s (seal z T))} in
    let l = obj (w : [fld get Π(y:⊤)⊤]) {get = λ(y : ⊤). y} in
    let r = m.forge l in
    path (cast r (top (m∙T)))
-/

namespace Forge

abbrev lT : Label := .typ 40
abbrev lget : Label := .trm 40
abbrev lforge : Label := .trm 41

abbrev piTT : Ty s := .pi .top .top
abbrev TelI : Telescope s := .cons .nil (.fld lget piTT)
abbrev BdT : Ty s := .mu TelI

/-- The module's telescope under its self `w`. -/
abbrev TelM : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .bot (.sel (.var .here) lT))) (.le (.sel (.var .here) lT) BdT))
    (.fld lforge (.pi BdT (.sel (.var (.there .here)) lT)))
/-- `forge = λ(s : BdT). path (cast s (seal z T))`, under the module's self `z`. -/
abbrev forgeFn : Value (s,x) := .lam BdT (.path (.cast (.var .here) (.seal (.var (.there .here)) lT)))
abbrev dsM : Defs (s,x) := .fld (.cls .nil lT BdT) lforge (.fn forgeFn)
abbrev modF : Value s := .obj TelM dsM
abbrev dsI : Defs (s,x) := .fld .nil lget (.fn (.lam .top (.path (.var .here))))
abbrev litL : Value s := .obj TelI dsI

abbrev progF : Tm [] :=
  .lett (.val modF)
    (.lett (.val litL)
      (.lett (.app (.sel (.var (.there .here)) lforge 2) (.var .here))
        (.path (.cast (.var .here) (.top (.sel (.var (.there (.there .here))) lT))))))

theorem progF_checks : checkTm .nil progF .top = true := by decide +kernel

theorem progF_scoped : Tm.SealsScoped (fun _ => false) progF :=
  seal_scope (checkTm_iff.1 progF_checks) (fun x => nomatch x)

/-! ### The run -/

abbrev σ6 : Store (([],x),x) := (Store.nil.cons modF).cons litL
abbrev body : Tm ((([],x),x),x) := .path (.cast (.var .here) (.top (.sel (.var (.there (.there .here))) lT)))
abbrev P6 : PathCo (([],x),x) := .cast (.var .here) (.seal (.var (.there .here)) lT)
abbrev t₀ : Tm ((([],x),x),x) := .path (.cast (.var .here) (.seal (.var (.there (.there .here))) lT))

theorem appViewOf_forge :
    appViewOf σ6 (.sel (.var (.there .here)) lforge 2) = some (BdT, t₀, .id) := by decide +kernel

theorem progF_reaches : Steps appView (⟨.nil, .nil, progF⟩ : State [])
    (⟨σ6, .cons .nil (.lett body), .path P6⟩ : State (([],x),x)) :=
  .tail (.tail (.tail (.tail (.tail (.tail .refl .lett) .letVal) .lett) .letVal) .lett)
    (.appId (appViewOf_iff.1 appViewOf_forge))

/-! ### The reached store: the forged instance and N1 to N4 -/

abbrev Γ6 : Ctx (([],x),x) :=
  (Ctx.nil.cons (.transparent (.mu TelM) dsM.block)).cons (.transparent (.mu TelI) dsI.block)

theorem modF_typed : synthValue .nil (modF : Value []) = some (.mu TelM) := by decide +kernel
theorem litL_typed : synthValue (Ctx.nil.cons (.transparent (.mu TelM) dsM.block)) (litL : Value ([],x)) =
    some (.mu TelI) := by decide +kernel
theorem σ6_typed : Store.Typed σ6 Γ6 :=
  .obj (.obj .nil (synthValue_sound modF_typed)) (synthValue_sound litL_typed)

abbrev m : Path (([],x),x) := .var (.there .here)
theorem clsAt_mT : Γ6.clsAt m lT = some BdT := by decide +kernel
theorem canon_m : Γ6.canon m = some m := by decide +kernel

theorem forged_typed : PathCo.HasType Γ6 P6 (.sel m lT) := Store1.forge clsAt_mT (.var rfl)
theorem forged_view : ∃ W, PV σ6 Γ6 P6 (.sel m lT) (.inst W) ∧ ViewT Γ6 σ6.erase P6.path (Γ6.res BdT) W :=
  class_view σ6_typed forged_typed (Ctx.clsOf_of_clsAt clsAt_mT)
theorem forged_seals : ∃ F q D, Hnf σ6 Γ6 (.seal m lT) BdT (.sel m lT) F ∧ Form.HasSeal F q D ∧
    Below Γ6 m lT (.sel q D) :=
  nominal_literal σ6_typed (.seal clsAt_mT) canon_m (by decide +kernel) (Ctx.res_mu Γ6 _) rfl
theorem forged_unscoped : ¬ Tm.SealsScoped (fun _ => false) (.path P6) := fun h => by
  have h' : (fun _ => false : Scope (([],x),x)) m.root = true := h.2
  cases h'
theorem Γ6_not_allOpaque : ¬ Ctx.AllOpaque Γ6 := fun h => by
  have h' := h .here
  cases h'

end Forge

end ClassEx

end Nominal.FCn
