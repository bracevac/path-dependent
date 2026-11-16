import Coercions.Selective.Witness
import Coercions.Selective.Rename
import Coercions.DotMNF.Examples
import Coercions.Frontend.Examples

/-!
# The example matrix, rows 9-11 and the extra rows

* Row 9: recursive types opened and closed at a variable (`fold`, `unfold`,
  an `unfold` in the middle of a receiver chain).
* Row 10: one implicit step per check position; nested casts erase to the
  subject; the single-step primitive relation against a chained one.
* Row 11: renaming of certificates; substitution of a variable by a closed
  receiver, where a renamed annotation fails and a re-annotation with an
  argument atom (whose receiver is the atom that bound the variable) checks.
* Extra rows: the root identity example `g y u` and its non-`μ` variant with a
  callee cast, the subject-reduction counterexample, receiver retyping at a
  projection (`u.a`, E9, P4), a callee cast (P5), And-I at a variable, the
  scoped receiver under a binder, codomain inversion, and a bridge between
  two different recursive types through a member.

Programs and contexts that come from the exploratory developments are
written out here as DOT-MNF terms and contexts; the
`_erase` theorems state that the annotated programs erase to them, by `rfl`.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Row 9: `μ` opening and closing

`Γμ = r : μ(s. {A : ⊥..s.B} ∧ {B : ⊥..{a:⊤}})`. -/

def muBody : Ty ([],x) := .and (.typ lA .bot (.sel (.var .here) lB)) (.typ lB .bot T1)
def Γμ : Ctx ([],x) := .cons .nil (.mu muBody)
def rB : Ty ([],x) := .sel (.var .here) lB
theorem mu_step1 : Prim Γμ rA rB := prim?_sound (by decide)
theorem mu_step2 : Prim Γμ rB T1 := prim?_sound (by decide)
theorem mu_no_chain : ¬ Prim Γμ rA T1 := not_prim_of (by decide)
theorem mu_co : checkC Γμ (.seq (.step rA rB) (.step rB T1)) rA T1 = true := by decide

/-- `o : μ(s. {A:⊤..⊤})` (copy of `RevB.Δo`), the store context of `ν(s. {A = ⊤})`. -/
def Δo : Ctx ([],x) := .cons .nil (.mu (.typ lA .top .top))
/-- `μ(s. {A:⊥..⊤})` (copy of `RevB.μt`). -/
def μt : Ty ([],x) := .mu (.typ lA .bot .top)

/-- `o` retyped at `μ(s. {A:⊥..⊤})` by `fold (unfold o ▷ step[{A:⊤..⊤}, {A:⊥..⊤}])`. -/
def atomO : Atom ([],x) :=
  .fold (.typ lA .bot .top) (.cast (.unfold (.var .here)) (.step (.typ lA .top .top) (.typ lA .bot .top)))
theorem obj_at_mu_H : synthA Δo atomO = some μt := by decide

/-- `μ(s. s.D ∧ {D : ⊥..{A:⊥..{a:⊤}}})`'s body (copy of `RevB.Qv`). -/
def RInner : Ty s := .typ lA .bot T1
def Qv : Ty ([],x) := .and (.sel (.var .here) lD) (.typ lD .bot RInner)
/-- `v : {B : ⊥..μ(s. s.D ∧ {D : ⊥..{A:⊥..{a:⊤}}})}, y : v.B` (copy of `RevB.Γv`). -/
def Γv : Ctx ([],x,x) := (Ctx.nil.cons (.typ lB .bot (.mu Qv))).cons (.sel (.var .here) lB)

/-- Receiver `r2`: widen `y` to the `μ`, unfold at `y`, then retype `y`
through its own member `D` by a nested positioned step whose receiver is
`r1`. -/
def Q1 : Ty ([],x,x) := .and (.sel (.var .here) lD) (.typ lD .bot RInner)
def r1 : Atom ([],x,x) :=
  .unfold (.cast (.var .here) (.step (.sel (.var (.there .here)) lB) ((Ty.mu Qv).weaken.weaken)))
def r2 : Atom ([],x,x) :=
  .cast r1 (.seq (.step Q1 (.sel (.var .here) lD))
    (.pos (.selU (.cast r1 (.step Q1 (.typ lD .bot RInner))) lD RInner)))
def certV : Cert ([],x,x) := .pos (.selU r2 lA T1)

theorem V_not_primitive : prim? Γv (.sel (.var .here) lA) T1 = false := by decide
theorem unfold_after_cast_H : synthC Γv certV = some (.sel (.var .here) lA, T1) := by decide

/-! ## Row 10: repeated implicit subsumption -/

/-- Nested casts erase to the subject. -/
theorem nested_erase {s : Sig} (t : HTm s) (c d : Cert s) :
    (HTm.cast (HTm.cast t c) d).erase = t.erase := rfl

/-- `y : {B : ⊥..{a:⊤}}, x : {A : ⊥..y.B}`. -/
def Γsh1 : Ctx ([],x,x) := .cons (.cons .nil (.typ lB .bot T1)) (.typ lA .bot (.sel (.var .here) lB))
def sh1xA : Ty ([],x,x) := .sel (.var .here) lA

/-- `≤₀` takes one bound step per position: no hidden chain. -/
theorem B2s_no_hidden_chain : ¬ Prim Γsh1 sh1xA T1 := not_prim_of (by decide)

/-- The rejected alternative B2c, for contrast: bound steps chained
(`x.A ≤ T` from `U ≤ T`). -/
inductive PrimC : {s : Sig} → Ctx s → Ty s → Ty s → Prop where
  | refl : PrimC Γ T T
  | top : PrimC Γ S .top
  | bot : PrimC Γ .bot T
  | andR : PrimC Γ S T → PrimC Γ S U → PrimC Γ S (.and T U)
  | andL1 : PrimC Γ S U → PrimC Γ (.and S T) U
  | andL2 : PrimC Γ T U → PrimC Γ (.and S T) U
  | fld : PrimC Γ T U → PrimC Γ (.fld a T) (.fld a U)
  | typ : PrimC Γ L2 L1 → PrimC Γ U1 U2 → PrimC Γ (.typ A L1 U1) (.typ A L2 U2)
  | all : PrimC Γ S2 S1 → PrimC (Γ.cons S2) T1 T2 → PrimC Γ (.all S1 T1) (.all S2 T2)
  | selU : Exp x (Γ.lookup x) A L U → PrimC Γ U T → PrimC Γ (.sel (.var x) A) T
  | selL : Exp x (Γ.lookup x) A L U → PrimC Γ S L → PrimC Γ S (.sel (.var x) A)

/-- B2c chains two bound steps with no written middle. -/
theorem B2c_hidden_chain : PrimC Γsh1 sh1xA T1 :=
  .selU (x := .here) (L := .bot) (U := .sel (.var (.there .here)) lB) .typ
    (.selU (x := .there .here) (L := .bot) (U := T1) .typ .refl)

/-! ## Row 11: weakening and substitution -/

/-- `T = {a:⊤} ∧ {b:⊤}`. -/
def Tab : Ty s := .and T1 T2
/-- `y : μ(s. {A : T..T})`, a literal's precise type (copy of `SelB.Δy`). -/
def Δy : Ctx ([],x) := .cons .nil (.mu (.typ lA Tab Tab))
def y1A : Ty ([],x) := .sel (.var .here) lA

/-- After `z := y`: the receiver is the argument's own atom. -/
def afterC : Cert ([],x) := .pos (.selU (.cast (.unfold (.var .here)) (.step (.typ lA Tab Tab) RInner)) lA T1)
theorem after_H : synthC Δy afterC = some (y1A, T1) := by decide

/-- Weakening: the renamed certificate checks in the extended context. -/
theorem after_H_weaken (V : Ty ([],x)) :
    CTy (Δy.cons V) (afterC.rename Rename.succ) y1A.weaken (T1 : Ty ([],x)).weaken :=
  (synthC_iff.mp after_H).weaken V

/-- `w : {B : ⊥..{A : ⊥..{a:⊤}}}` (copy of `SelB.ΓW`). -/
def ΓW : Ctx ([],x) := .cons .nil (.typ lB .bot RInner)
def wB : Ty ([],x) := .sel (.var .here) lB
/-- `w : {B : ⊥..{A:⊥..{a:⊤}}}, y : w.B` (copy of `SelB.ΓR`). -/
def ΓR : Ctx ([],x,x) := .cons ΓW wB
def yA : Ty ([],x,x) := .sel (.var .here) lA

/-- The open receiver: `y ▷ step[w.B, {A:⊥..{a:⊤}}]`. -/
def openC : Cert ([],x,x) := .pos (.selU (.cast (.var .here) (.step (.sel (.var (.there .here)) lB) RInner)) lA T1)
theorem open_H : synthC ΓR openC = some (yA, T1) := by decide

/-- `x : {A : ⊤..{A:⊥..{a:⊤}}}, y : ⊤` (copy of `SelB.Γbb`). -/
def Γbb : Ctx ([],x,x) := .cons (.cons .nil (.typ lA .top RInner)) .top
def bbxA : Ty ([],x,x) := .sel (.var (.there .here)) lA
def bbyA : Ty ([],x,x) := .sel (.var .here) lA

/-- The receiver carries the composite `⊤ ⇒ x.A ⇒ {A:⊥..{a:⊤}}`. -/
def bbC : Cert ([],x,x) := .pos (.selU (.cast (.var .here) (.seq (.step .top bbxA) (.step bbxA RInner))) lA T1)
theorem bb_H : synthC Γbb bbC = some (bbyA, T1) := by decide

/-! ### The subject-reduction counterexample

`let y = ν(s : {A : T..T}) {A = T} in let z = (unfold y) ▷ step[{A:⊥..{a:⊤}}, {A:⊥..{a:⊤}}] in
let g = λ(k : K). λ(u : z.A). k u in y`, with `T = {a:⊤} ∧ {b:⊤}` and
`K = ∀(v : {a:⊤}) {a:⊤}`. -/

/-- `K = ∀(v : {a:⊤}) {a:⊤}` (copy of `RevB.K`). -/
def K {s : Sig} : Ty s := .all T1 T1
/-- The stored literal's precise type (copy of `RevB.Ty0`). -/
def Ty0 : Ty [] := .mu (.typ lA Tab Tab)
/-- The stored object, erased (copy of `RevB.objV`). -/
def objV : DotMNF.Value [] := .obj (.typ lA Tab)

/-- The erased program (copy of `RevB.prog.erase`). -/
def progTm : DotMNF.Tm [] :=
  .let (.val (.obj (.typ lA Tab)))
  (.let (.path (.var .here))
  (.let (.val (.lam K (.val (.lam (.sel (.var (.there .here)) lA) (.app (.there .here) .here)))))
  (.path (.var (.there (.there .here))))))

/-- `y.A` in the scope `y, k` (copy of `RevB.yA2`). -/
def yA2 : Ty ([],x,x) := .sel (.var (.there .here)) lA

/-- The reduct after `let`, `alloc`, `let`, `rename` (copy of `RevB.reduct`). -/
def reductTm : DotMNF.Tm ([],x) :=
  .let (.val (.lam K (.val (.lam yA2 (.app (.there .here) .here)))))
    (.path (.var (.there .here)))

def progH : HTm [] :=
  .let (.val (.obj (.typ lA Tab Tab) (.typ lA Tab)))
  (.let (.cast (.atom (.unfold (.var .here))) (.step RInner RInner))
  (.let (.val (.lam K (.val (.lam (.sel (.var (.there .here)) lA)
      (.app (.var (.there .here)) (.var .here))))))
  (.atom (.var (.there (.there .here))))))

theorem progH_erase : progH.erase = progTm := rfl

theorem progH_typed : HTy .nil progH Ty0 := by decide

/-- The machine run of the erased program: `let`, `alloc`, `let`, `rename`. -/
theorem progH_steps :
    DotMNF.Steps (⟨.nil, .nil, progH.erase⟩ : DotMNF.State [])
      (⟨.cons .nil objV, DotMNF.Cont.weaken .nil, reductTm⟩ : DotMNF.State ([],x)) :=
  .tail (.tail (.tail (.tail .refl .let) .alloc) .let) .rename

/-- The renamed annotation (`z := y` in the body): `k u` with no argument evidence. -/
def reductNaive : HTm ([],x) :=
  .let (.val (.lam K (.val (.lam yA2 (.app (.var (.there .here)) (.var .here))))))
    (.atom (.var (.there .here)))

theorem reductNaive_erase : reductNaive.erase = reductTm := rfl

def Γku : Ctx ([],x,x,x) := (Δy.cons K).cons yA2

/-- The one step the application needs, after the substitution. -/
theorem arg_not_prim : ¬ Prim Γku (Γku.lookup .here) T1 := not_prim_of (by decide)

theorem reductNaive_untypable : ∀ U, ¬ HTy Δy reductNaive U := by
  intro U h
  cases h with
  | «let» h1 _ =>
    cases h1 with
    | lam h2 =>
      cases h2 with
      | lam h3 =>
        cases h3 with
        | app ha hb hp =>
          cases ha; cases hb
          exact arg_not_prim hp

/-- The positioned step whose receiver is the atom that bound `z`
(`unfold y ▷ step[{A:T..T}, {A:⊥..{a:⊤}}]`), at the argument of `k`. -/
def cRepair : Cert ([],x,x,x) :=
  .pos (.selU (.cast (.unfold (.var (.there (.there .here)))) (.step (.typ lA Tab Tab) RInner)) lA T1)

/-- The re-annotated reduct: `k (u ▷ cRepair)`; the same erased program. -/
def reductH : HTm ([],x) :=
  .let (.val (.lam K (.val (.lam yA2
      (.app (.var (.there .here)) (.cast (.var .here) cRepair))))))
    (.atom (.var (.there .here)))

theorem reductH_erase : reductH.erase = reductTm := rfl

theorem reductH_typed : HTy Δy reductH (Δy.lookup .here) := by decide

/-- **The argument atom repairs the counterexample**: the typed program
reaches the reduct; the renamed annotation is untypable; a re-annotation with
an argument atom (same erased reduct) is typed in the store context. -/
theorem argument_slot_repairs_counterexample :
    HTy .nil progH Ty0 ∧
    DotMNF.Steps (⟨.nil, .nil, progH.erase⟩ : DotMNF.State [])
      (⟨.cons .nil objV, DotMNF.Cont.weaken .nil, reductTm⟩ : DotMNF.State ([],x)) ∧
    reductNaive.erase = reductTm ∧ (∀ U, ¬ HTy Δy reductNaive U) ∧
    reductH.erase = reductTm ∧ HTy Δy reductH (Δy.lookup .here) :=
  ⟨progH_typed, progH_steps, rfl, reductNaive_untypable, rfl, reductH_typed⟩

/-! ## Extra row R1: root identity, `g y u`

  b : {B : ⊥..⊤}, c : {C : ⊥..⊤}, x : {A : b.B .. c.C},
  g : ∀(o : μ(r. {D : ⊥..⊤} ∧ {a : c.C})) ∀(w : o.D) ⊤,
  y : μ(s. {D : ⊥..⊤} ∧ {a : b.B}),
  u : y.D

and the erased program `let h = g y in h u`.  The argument is the atom
`fold[{D} ∧ {a : c.C}] (unfold y ▷ c)` with
`c = step[{D} ∧ {a:b.B}, {D} ∧ {a:x.A}] ; step[{D} ∧ {a:x.A}, {D} ∧ {a:c.C}]`.
Its root is `y`, so `g (…)` has type `∀(w : y.D) ⊤` and `h u` checks with
`u : y.D` by `refl`.  The labels are those of `DotMNF.Examples` with
`C = .typ 3`, `D = .typ 4`, so that the erased program is literally the
lost program `tPlain`. -/

namespace R1

abbrev lA : Label := DotMNF.Examples.lA
abbrev lB : Label := DotMNF.Examples.lB
abbrev la : Label := DotMNF.Examples.la
def lC : Label := .typ 3
def lD : Label := .typ 4

def Tb : Ty [] := .typ lB .bot .top
def Tc : Ty ([],x) := .typ lC .bot .top
def Tx : Ty ([],x,x) := .typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC)
def Tg : Ty ([],x,x,x) :=
  .all (.mu (.and (.typ lD .bot .top) (.fld la (.sel (.var (.there (.there .here))) lC))))
    (.all (.sel (.var .here) lD) .top)
def Ty' : Ty ([],x,x,x,x) :=
  .mu (.and (.typ lD .bot .top) (.fld la (.sel (.var (.there (.there (.there (.there .here))))) lB)))
def Tu : Ty ([],x,x,x,x,x) := .sel (.var .here) lD

abbrev S6 : Sig := ([],x,x,x,x,x,x)
def vu : BVar S6 .var := .here
def vy : BVar S6 .var := .there .here
def vg : BVar S6 .var := .there (.there .here)
def vx : BVar S6 .var := .there (.there (.there .here))
def vc : BVar S6 .var := .there (.there (.there (.there .here)))
def vb : BVar S6 .var := .there (.there (.there (.there (.there .here))))

def bB6 : Ty S6 := .sel (.var vb) lB
def cC6 : Ty S6 := .sel (.var vc) lC

/-- The lost program (copy of `RevA.tPlain`). -/
def tPlain : DotMNF.Tm [] :=
  .val <| .lam Tb <| .val <| .lam Tc <| .val <| .lam Tx <| .val <| .lam Tg <| .val <| .lam Ty' <|
    .val <| .lam Tu <| .let (.app vg vy) (.app .here (.there .here))

def xA6 : Ty S6 := .sel (.var vx) lA
def Dd : Ty S6 := .typ lD .bot .top
def F0 : Ty S6 := .and Dd (.fld la bB6)
def F1 : Ty S6 := .and Dd (.fld la xA6)
def F2 : Ty S6 := .and Dd (.fld la cC6)
/-- The body of `g`'s recursive domain, under its self binder. -/
def Dbody : Ty (S6,x) := .and (.typ lD .bot .top) (.fld la (.sel (.var (.there vc)) lC))

def cField : Cert S6 := .seq (.step F0 F1) (.step F1 F2)
/-- The argument atom: unfold at `y`, two field steps, fold at `y`. -/
def yArg : Atom S6 := .fold Dbody (.cast (.unfold (.var vy)) cField)

def body6H : HTm S6 := .let (.app (.var vg) yArg) (.app (.var .here) (.var (.there .here)))

def hPlain : HTm [] :=
  .val <| .lam Tb <| .val <| .lam Tc <| .val <| .lam Tx <| .val <| .lam Tg <| .val <| .lam Ty' <|
    .val <| .lam Tu body6H

def PlainTy : Ty [] := .all Tb (.all Tc (.all Tx (.all Tg (.all Ty' (.all Tu .top)))))

/-- **Same erased program** as the lost program. -/
theorem hPlain_erase : hPlain.erase = tPlain := rfl

/-- **R1 is typed.** -/
theorem hPlain_typed : HTy .nil hPlain PlainTy := by decide

def G6 : Ctx S6 :=
  (((((Ctx.nil.cons Tb).cons Tc).cons Tx).cons Tg).cons Ty').cons Tu
theorem yArg_root : yArg.root = vy := rfl

/-- The argument atom keeps the root `y`: `g (…)` has the single type `∀(w : y.D) ⊤`. -/
theorem app_type :
    synthTm G6 (.app (.var vg) yArg) = [.all (.sel (.var vy) lD) .top] := by decide

/-- Safety of the erased program, through the transported route. -/
theorem hPlain_safe {s : Sig} {st : DotMNF.State s}
    (r : DotMNF.Steps (⟨.nil, .nil, tPlain⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety hPlain_typed r

/-! ### R1N: the non-`μ` variant, a cast in function position -/

def TgN : Ty ([],x,x,x) :=
  .all (.and (.typ lD .bot .top) (.fld la (.sel (.var (.there .here)) lC)))
    (.all (.sel (.var .here) lD) .top)
def TyN : Ty ([],x,x,x,x) :=
  .and (.typ lD .bot .top) (.fld la (.sel (.var (.there (.there (.there .here)))) lB))

/-- The erased non-`μ` program. -/
def tPlainN : DotMNF.Tm [] :=
  .val <| .lam Tb <| .val <| .lam Tc <| .val <| .lam Tx <| .val <| .lam TgN <| .val <| .lam TyN <|
    .val <| .lam Tu <| .let (.app vg vy) (.app .here (.there .here))

def Cod : Ty (S6,x) := .all (.sel (.var .here) lD) .top
def GcC : Ty S6 := .all F2 Cod
def GxA : Ty S6 := .all F1 Cod
def GbB : Ty S6 := .all F0 Cod
/-- `g ▷ (step[∀(o : …c.C) …, ∀(o : …x.A) …] ; step[…, ∀(o : …b.B) …])`, by domain contravariance. -/
def gFun : Atom S6 := .cast (.var vg) (.seq (.step GcC GxA) (.step GxA GbB))

def hPlainN : HTm [] :=
  .val <| .lam Tb <| .val <| .lam Tc <| .val <| .lam Tx <| .val <| .lam TgN <| .val <| .lam TyN <|
    .val <| .lam Tu <| .let (.app gFun (.var vy)) (.app (.var .here) (.var (.there .here)))

def PlainTyN : Ty [] := .all Tb (.all Tc (.all Tx (.all TgN (.all TyN (.all Tu .top)))))

theorem hPlainN_erase : hPlainN.erase = tPlainN := rfl
theorem hPlainN_typed : HTy .nil hPlainN PlainTyN := by decide

end R1

/-! ## Extra rows: receivers at projections, callee casts -/

/-- `w : {B:⊥..{A:⊥..{a:⊤}}}, y : w.B, u : y.A` (copy of `SelB.ΓR2`). -/
def ΓR2 : Ctx ([],x,x,x) := .cons ΓR yA

/-- `(u ▷ pos(selU (y ▷ step[w.B, {A:⊥..{a:⊤}}]) A {a:⊤})).a : ⊤`. -/
def uProjH : HTm ([],x,x,x) :=
  .proj (.cast (.var .here)
    (.pos (.selU (.cast (.var (.there .here)) (.step (.sel (.var (.there (.there .here))) lB) RInner))
      lA T1))) la

theorem uProjH_erase : uProjH.erase = .proj .here la := rfl
theorem uProjH_typed : HTy ΓR2 uProjH .top := by decide

/-- E9 with a receiver atom, the same erased program as the frontend's. -/
def E9H : HTm [] :=
  .val (.lam (.typ lA .bot T1) (.val (.lam (.sel (.var .here) lA)
    (.proj (.cast (.var .here) (.step (.sel (.var (.there .here)) lA) T1)) la))))
theorem E9H_erase : E9H.erase = Frontend.E9tm := rfl
theorem E9H_typed : HTy .nil E9H Frontend.E9ty := by decide

def lv : Label := .trm 2
/-- `μ(s. {b:⊤} ∧ ({v:⊤} ∧ {a : s.B}))` (copy of `RevB.P4M`). -/
def P4M : Ty ([],x) := .mu (.and (.fld lb .top) (.and (.fld lv .top) (.fld la (.sel (.var .here) lB))))
/-- Copy of `RevB.P4dom`. -/
def P4dom : Ty [] := .typ lA .bot (.mu (.and (.fld lb .top) (.and (.fld lv .top) (.fld la (.sel (.var .here) lB)))))
/-- The frontend's P4 type (copy of `RevB.P4ty`). -/
def P4ty : Ty [] := .all P4dom (.all (.sel (.var .here) lA) (.sel (.var .here) lB))
/-- The frontend's erased P4 (copy of `RevB.P4h.erase`). -/
def P4tm : DotMNF.Tm [] := .val (.lam P4dom (.val (.lam (.sel (.var .here) lA) (.proj .here la))))

def P4H : HTm [] :=
  .val (.lam P4dom (.val (.lam (.sel (.var .here) lA)
    (.proj (.cast (.var .here) (.step (.sel (.var (.there .here)) lA) P4M.weaken)) la))))
theorem P4H_erase : P4H.erase = P4tm := rfl
theorem P4H_typed : HTy .nil P4H P4ty := by decide

/-- `(∀(_:{a:⊤}) ⊤) ∧ (∀(_:⊤) ⊤)` (copy of `RevB.P5dom`). -/
def P5dom : Ty [] := .and (.all T1 .top) (.all .top .top)
/-- The frontend's erased P5 (copy of `RevB.P5tm`). -/
def P5tm : DotMNF.Tm [] := .val (.lam P5dom (.val (.lam .top (.app (.there .here) .here))))

/-- `λ(f : P5dom). λ(z : ⊤). (f ▷ step[_, ∀(_:⊤) ⊤]) z`: a callee atom. -/
def P5H : HTm [] :=
  .val (.lam P5dom (.val (.lam .top
    (.app (.cast (.var (.there .here)) (.step (P5dom.weaken.weaken) (.all .top .top)))
      (.var .here)))))

theorem P5H_erase : P5H.erase = P5tm := rfl
theorem P5H_typed : HTy .nil P5H (.all P5dom (.all .top .top)) := by decide

/-! ## Extra row: And-I at a variable

`f : ∀(z : μ(s. {a : s.A}) ∧ {A:⊥..⊤}) ⊤, x : μ(s. {A:⊥..⊤} ∧ {a : s.A}) ⊢
f ⟨fold(unfold x ▷ _), unfold x ▷ _⟩ : ⊤`. -/

def IfaceB : Ty ([],x) := .fld la (.sel (.var .here) lA)
def Ubody : Ty ([],x,x) := .and (.typ lA .bot .top) (.fld la (.sel (.var .here) lA))
def ΓAnd : Ctx ([],x,x) :=
  (Ctx.nil.cons (.all (.and (.mu IfaceB) (.typ lA .bot .top)) .top)).cons (.mu Ubody)
def Ux : Ty ([],x,x) := .and (.typ lA .bot .top) (.fld la (.sel (.var .here) lA))
def bothArg : Atom ([],x,x) :=
  .both (.fold (.fld la (.sel (.var .here) lA)) (.cast (.unfold (.var .here)) (.step Ux (.fld la (.sel (.var .here) lA)))))
        (.cast (.unfold (.var .here)) (.step Ux (.typ lA .bot .top)))
def bothApp : HTm ([],x,x) := .app (.var (.there .here)) bothArg
theorem bothApp_erase : bothApp.erase = .app (.there .here) .here := rfl
theorem bothApp_typed : HTy ΓAnd bothApp .top := by decide

/-! ## Extra rows: receivers scoped at the hole

With target `⊤` one primitive step suffices.  The non-`⊤` example
(`goodK`, `badK`) is in row 13 (`Witness.lean`); its receiver-free chain is
`K_receiver_free_chain` (`Negative.lean`). -/

def DomT : Ty [] := .typ lA .bot (.typ lB .bot .top)
def SrcT : Ty [] := .all DomT (.all (.sel (.var .here) lA) (.sel (.var .here) lB))
def DstT : Ty [] := .all DomT (.all (.sel (.var .here) lA) .top)
theorem codexTop_primitive : Prim .nil SrcT DstT := prim?_sound (by decide)

/-- `y : ⊤ ⊢ ∀(x : {A : ⊤..{B:⊥..{a:⊤}}}) y.B ⇒ ∀(x : …) {a:⊤}`.  The receiver
`y ▷ (step[⊤, x.A] ; step[x.A, {B:..}])` mentions the bound `x`. -/
def Γ0 : Ctx ([],x) := .cons .nil .top
def D0 : Ty ([],x) := .typ lA .top RB
def yB : Ty ([],x,x) := .sel (.var (.there .here)) lB
def SrcY : Ty ([],x) := .all D0 yB
def DstY : Ty ([],x) := .all D0 T1
def certY : Cert ([],x) :=
  .pos (.allC D0 (.selU (.cast (.var (.there .here))
    (.seq (.step .top (.sel (.var .here) lA)) (.step (.sel (.var .here) lA) RB))) lB T1))

theorem certY_checks : synthC Γ0 certY = some (SrcY, DstY) := by decide
theorem certY_typed : CTy Γ0 certY SrcY DstY := synthC_iff.mp certY_checks

/-! ## Extra row: codomain inversion

The function chain `∀(x : {A:⊥..{a:⊤}}) x.A ⇒ ∀(x : …) {a:⊤} ⇒ ∀(x : w.B) {a:⊤}`
in `ΓW` decomposes into a domain step and a codomain step under the target
domain `x : w.B`, the latter a positioned step whose receiver is `x ▷ step[w.B, …]`. -/

def xA1 : Ty ([],x,x) := .sel (.var .here) lA
def Fsrc : Ty ([],x) := .all RInner xA1
def Ftgt : Ty ([],x) := .all wB T1
def codC : Cert ([],x,x) :=
  .pos (.selU (.cast (.var .here) (.step (.sel (.var (.there .here)) lB) RInner)) lA T1)

theorem fun_invertible_H :
    CTy ΓW (.step wB RInner) wB RInner ∧ CTy (ΓW.cons wB) codC xA1 T1 ∧
    CTy ΓW (.seq (.step Fsrc (.all wB xA1)) (.pos (.allC wB (.selU (.cast (.var .here)
      (.step (.sel (.var (.there .here)) lB) RInner)) lA T1)))) Fsrc Ftgt := by
  refine ⟨synthC_iff.mp ?_, synthC_iff.mp ?_, synthC_iff.mp ?_⟩ <;> decide

/-! ## Extra row: two different recursive types related through a member

`x : {A : μS..μT} ⊢ μS ⇒ x.A ⇒ μT`: no `μ` congruence is needed. -/

def muS : Ty [] := .mu (.fld la .top)
def muT : Ty [] := .mu (.typ lB .bot .top)
def Gmu : Ctx ([],x) := .cons .nil (.typ lA muS muT)
def bridge : Cert ([],x) := .seq
  (.step muS.weaken (.sel (.var .here) lA))
  (.step (.sel (.var .here) lA) muT.weaken)

theorem muBridge_different : muS ≠ muT := by decide
theorem muBridge_not_primitive : prim? Gmu muS.weaken muT.weaken = false := by decide
theorem muBridge_checks : synthC Gmu bridge = some (muS.weaken, muT.weaken) := by decide
theorem distinct_mu_inclusion : Nonempty (DotMNF.Sub Gmu muS.weaken muT.weaken) :=
  CTy.sound (synthC_iff.mp muBridge_checks)

end Selective
