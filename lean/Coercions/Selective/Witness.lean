import Coercions.Selective.Sound
import Coercions.Selective.Typer
import Coercions.Frontend.Alg

/-!
# The example matrix, rows 1-8 and 12-14

Every negative judgment is a theorem about the inductive `Prim`, by inversion
or from a computed `prim? … = false` through `not_prim_of`.  Every positive
certificate or term judgment is computed by the checkers (`synthC`,
`synthTm`) and read back through their `_iff` theorems.

Labels follow one numbering: `lA = .typ 0`, `lB = .typ 1`, `lC = .typ 2`,
`lD = .typ 3`, `la = .trm 0`, `lb = .trm 1`.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Labels -/

def lA : Label := .typ 0
def lB : Label := .typ 1
def lC : Label := .typ 2
def lD : Label := .typ 3
def la : Label := .trm 0
def lb : Label := .trm 1

/-- `{a : ⊤}`. -/
def T1 : Ty s := .fld la .top
/-- `{b : ⊤}`. -/
def T2 : Ty s := .fld lb .top

/-! ## The realizable context

`Γr = b : {B : ⊥..⊤}, c : {C : ⊥..⊤}, x : {A : b.B .. c.C}`.
In `Γr`: `x = here`, `c = there here`, `b = there (there here)`. -/

abbrev Sr : Sig := [] ,x ,x ,x

def Γb : Ctx ([],x) := .cons .nil (.typ lB .bot .top)
def Γbc : Ctx ([],x,x) := .cons Γb (.typ lC .bot .top)
/-- `{A : b.B .. c.C}` in the scope `b, c`. -/
def xDecl : Ty ([],x,x) := .typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC)
def Γr : Ctx Sr := .cons Γbc xDecl

def rb : BVar Sr .var := .there (.there .here)
def rc : BVar Sr .var := .there .here
def rx : BVar Sr .var := .here

def bB : Ty Sr := .sel (.var rb) lB
def cC : Ty Sr := .sel (.var rc) lC
def xA : Ty Sr := .sel (.var rx) lA

theorem Γr_lookup_x : Γr.lookup rx = .typ lA bB cC := rfl
theorem Γr_lookup_b : Γr.lookup rb = .typ lB .bot .top := rfl
theorem Γr_lookup_c : Γr.lookup rc = .typ lC .bot .top := rfl

/-! ## Row 1: reflexivity, top, bottom, fields, intersections need no middle -/

theorem row1_baseline_steps :
    Prim Γr bB bB ∧ Prim Γr bB .top ∧ Prim Γr .bot cC ∧
    Prim Γr (.fld la (.and bB cC)) (.fld la (.and cC .top)) ∧
    Prim Γr (.typ lA .bot (.and bB cC)) (.typ lA .bot bB) ∧
    Prim Γr (.and (.and T1 T2) T2) T1 := by
  refine ⟨.refl, .top, .bot, ?_, ?_, .andL1 (.andL1 .refl)⟩ <;> exact prim?_sound (by decide)

/-- `f : ∀(_ : {a:⊤}) ⊤, z : {a:⊤} ∧ {b:⊤}`. -/
def Γ1 : Ctx ([],x,x) := .cons (.cons .nil (.all T1 .top)) (.and T1 T2)

/-- `f z` is typed with one implicit step `{a:⊤} ∧ {b:⊤} ≤₀ {a:⊤}` at the argument. -/
theorem row1_app_implicit : HTy Γ1 (.app (.var (.there .here)) (.var .here)) .top := by decide

/-! ## Row 2: E3 (`x : {A : ⊥..{a:⊤}} ∧ {A : {b:⊤}..⊤}, z : {b:⊤}`) -/

def E3Dom : Ty s := .and (.typ lA .bot T1) (.typ lA T2 .top)
def E3Γ : Ctx ([],x,x) := .cons (.cons .nil E3Dom) T2
def e3x : BVar ([],x,x) .var := .there .here
def e3z : BVar ([],x,x) .var := .here
def e3xA : Ty ([],x,x) := .sel (.var e3x) lA

/-- The E3 goal is not `≤₀` in any context (labels differ, no rule applies). -/
theorem E3_not_prim {s : Sig} (Γ : Ctx s) : ¬ Prim Γ T2 T1 := by
  intro h; cases h

theorem E3_half1 : Prim E3Γ T2 e3xA := prim?_sound (by decide)
theorem E3_half2 : Prim E3Γ e3xA T1 := prim?_sound (by decide)

/-- E3's annotation-free check: the variable `z : {b:⊤}` has no type with one
`≤₀` step to `{a:⊤}`, which is all an argument or cast subject allows. -/
theorem E3_rejected : ¬ ∃ V, ATy E3Γ (.var e3z) V ∧ Prim E3Γ V T1 := by
  rintro ⟨V, hV, hp⟩
  cases hV
  have hl : E3Γ.lookup e3z = T2 := rfl
  rw [hl] at hp
  exact E3_not_prim _ hp

/-- E3s: the middle written as the certificate's source. -/
theorem E3s_typed : HTy E3Γ (.cast (.atom (.var e3z)) (.step e3xA T1)) T1 := by decide

/-- E3s in atom form: both steps written. -/
theorem E3s_atom_typed : ATy E3Γ (.cast (.var e3z) (.seq (.step T2 e3xA) (.step e3xA T1))) T1 :=
  synthA_iff.mp (by decide)

/-! ## Row 3: the realizable gap -/

theorem half1 : Prim Γr bB xA := .selL (x := rx) (U := cC) (by rw [Γr_lookup_x]; exact .typ)
theorem half2 : Prim Γr xA cC := .selU (x := rx) (L := bB) (by rw [Γr_lookup_x]; exact .typ)

/-- The composite is not primitive, by inversion on `Prim`. -/
theorem realizable_gap : ¬ Prim Γr bB cC := by
  intro h
  cases h with
  | selU e =>
      rw [Γr_lookup_b] at e
      cases e
  | selL e =>
      rw [Γr_lookup_c] at e
      cases e

/-- The same verdict from the decision procedure. -/
theorem realizable_gap' : ¬ Prim Γr bB cC := not_prim_of (by decide)

/-- The explicit composite. -/
def wit : Cert Sr := .seq (.step bB xA) (.step xA cC)
theorem wit_typed : CTy Γr wit bB cC := .seq (.step half1) (.step half2)
theorem wit_checks : checkC Γr wit bB cC = true := by decide

/-- `≤₀` is not transitive, with a consistent context as witness. -/
theorem primitive_nontrans :
    ¬ ∀ {s : Sig} (Γ : Ctx s) (S M T : Ty s), Prim Γ S M → Prim Γ M T → Prim Γ S T :=
  fun h => realizable_gap (h Γr bB xA cC half1 half2)

/-- Both halves are primitive, the composite is not, and the written
composite certificate is accepted. -/
theorem realizable_nontrans :
    Prim Γr bB xA ∧ Prim Γr xA cC ∧ ¬ Prim Γr bB cC ∧ CTy Γr wit bB cC :=
  ⟨half1, half2, realizable_gap, wit_typed⟩

/-! ### The closed realization

`let b = ν(s : {B:⊤..⊤}) {B = ⊤} in let c = … in let x = … in let f = fLam in
let g1 = f (unfold b) in let g2 = g1 (unfold c) in let g3 = g2 (unfold x) in
let o = unfold b ▷ step[{B:⊤..⊤}, ⊤] in let r = g3 o in r ▷ step[c.C, ⊤]`,
where `fLam = λ(b : {B:⊥..⊤}). λ(c : {C:⊥..⊤}). λ(x : {A : b.B..c.C}).
λ(z : b.B). z ▷ (step[b.B,x.A] ; step[x.A,c.C])`.  The argument atoms
`unfold b` open the literals' recursive types at their roots. -/

def fLam : HVal ([],x,x,x) :=
  .lam (.typ lB .bot .top) (.val (.lam (.typ lC .bot .top) (.val (.lam
    (.typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC))
    (.val (.lam (.sel (.var (.there (.there .here))) lB)
      (.cast (.atom (.var .here))
        (.seq (.step (.sel (.var (.there (.there (.there .here)))) lB) (.sel (.var (.there .here)) lA))
              (.step (.sel (.var (.there .here)) lA) (.sel (.var (.there (.there .here))) lC))))))))))

def realization : HTm [] :=
  .let (.val (.obj (.typ lB .top .top) (.typ lB .top)))
  (.let (.val (.obj (.typ lC .top .top) (.typ lC .top)))
  (.let (.val (.obj (.typ lA .top .top) (.typ lA .top)))
  (.let (.val fLam)
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.cast (.atom (.unfold (.var (.there (.there (.there (.there (.there (.there .here)))))))))
          (.step (.typ lB .top .top) .top))
  (.let (.app (.var (.there .here)) (.var .here))
  (.cast (.atom (.var .here))
    (.step (.sel (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) lC)
      .top))))))))))

/-- The erased program of the boundary-only realization (`SelB.realization.erase`). -/
def realizationTm : DotMNF.Tm [] :=
  .let (.val (.obj (.typ lB .top)))
  (.let (.val (.obj (.typ lC .top)))
  (.let (.val (.obj (.typ lA .top)))
  (.let (.val (.lam (.typ lB .bot .top) (.val (.lam (.typ lC .bot .top) (.val (.lam
      (.typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC))
      (.val (.lam (.sel (.var (.there (.there .here))) lB) (.path (.var .here))))))))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.path (.var (.there (.there (.there (.there (.there (.there .here))))))))
  (.let (.app (.there .here) .here)
  (.path (.var .here))))))))))

theorem realization_erase : realization.erase = realizationTm := rfl

theorem realization_typed : HTy .nil realization .top := by decide

theorem realization_safe {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, realization.erase⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety realization_typed run

/-! ### A closed program whose body needs the gap coercion

`gapFn = λ(b : {B:⊥..⊤}). λ(c : {C:⊥..⊤}). λ(x : {A : b.B..c.C}).
λ(k : ∀(_ : c.C) ⊤). λ(z : b.B). k (z ▷ wit)`, applied to three literals,
`λ(w : c.C). w ▷ step[c.C, ⊤]` and `unfold b ▷ step[{B:⊤..⊤}, ⊤]`.  The
bare body `k z` has no type: the argument `z : b.B` would need the composite
`b.B ⇒ x.A ⇒ c.C` as one implicit step. -/

/-- The signature of `gapFn`'s body: `z, k, x, c, b`. -/
abbrev Sg : Sig := [] ,x ,x ,x ,x ,x

def kTy : Ty Sr := .all (.sel (.var (.there .here)) lC) .top

/-- `wit` in the body's scope (`b = there⁴ here`, `c = there³ here`, `x = there² here`),
under any outer scope. -/
def witG {s : Sig} : Cert (s,x,x,x,x,x) :=
  .seq (.step (.sel (.var (.there (.there (.there (.there .here))))) lB)
              (.sel (.var (.there (.there .here))) lA))
       (.step (.sel (.var (.there (.there .here))) lA)
              (.sel (.var (.there (.there (.there .here)))) lC))

def gapFn {s : Sig} : HTm s :=
  .val (.lam (.typ lB .bot .top) (.val (.lam (.typ lC .bot .top) (.val (.lam
    (.typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC))
    (.val (.lam (.all (.sel (.var (.there .here)) lC) .top)
      (.val (.lam (.sel (.var (.there (.there (.there .here)))) lB)
        (.app (.var (.there .here)) (.cast (.var .here) witG)))))))))))

/-- The context of `gapFn`'s body. -/
def Γgap : Ctx Sg := (Γr.cons kTy).cons (.sel (.var (.there (.there (.there .here)))) lB)

theorem gapNeeded_bare_untypable :
    ∀ U, ¬ HTy Γgap (.app (.var (.there .here)) (.var .here)) U :=
  untypable_of_synthTm (by decide)

/-- The body with the gap coercion at the argument. -/
theorem gapBody_typed : HTy Γgap (.app (.var (.there .here)) (.cast (.var .here) witG)) .top := by
  decide

def gapNeeded : HTm [] :=
  .let (.val (.obj (.typ lB .top .top) (.typ lB .top)))
  (.let (.val (.obj (.typ lC .top .top) (.typ lC .top)))
  (.let (.val (.obj (.typ lA .top .top) (.typ lA .top)))
  (.let gapFn
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.app (.var .here) (.unfold (.var (.there (.there (.there .here))))))
  (.let (.val (.lam (.sel (.var (.there (.there (.there (.there (.there .here)))))) lC)
      (.cast (.atom (.var .here))
        (.step (.sel (.var (.there (.there (.there (.there (.there (.there .here))))))) lC) .top))))
  (.let (.app (.var (.there .here)) (.var .here))
  (.app (.var .here)
    (.cast (.unfold (.var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.step (.typ lB .top .top) .top)))))))))))

theorem gapNeeded_typed : HTy .nil gapNeeded .top := by decide

theorem gapNeeded_safe {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, gapNeeded.erase⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety gapNeeded_typed run

/-! ## Row 4: three bound steps; association

`x0 : {A:⊥..{a:⊤}}, x1 : {A:⊥..x0.A}, x2 : {A:⊥..x1.A}`. -/

def Γ3 : Ctx ([],x,x,x) :=
  .cons (.cons (.cons .nil (.typ lA .bot T1)) (.typ lA .bot (.sel (.var .here) lA)))
    (.typ lA .bot (.sel (.var .here) lA))
def s0A : Ty ([],x,x,x) := .sel (.var (.there (.there .here))) lA
def s1A : Ty ([],x,x,x) := .sel (.var (.there .here)) lA
def s2A : Ty ([],x,x,x) := .sel (.var .here) lA

theorem three_not_prim : ¬ Prim Γ3 s2A T1 := not_prim_of (by decide)
theorem three_not_prim' : ¬ Prim Γ3 s2A s0A := not_prim_of (by decide)

def c3L : Cert ([],x,x,x) := .seq (.seq (.step s2A s1A) (.step s1A s0A)) (.step s0A T1)
def c3R : Cert ([],x,x,x) := .seq (.step s2A s1A) (.seq (.step s1A s0A) (.step s0A T1))
theorem c3L_typed : checkC Γ3 c3L s2A T1 = true := by decide
theorem c3R_typed : checkC Γ3 c3R s2A T1 = true := by decide
/-- Association of `;` does not change the erased program. -/
theorem c3_erase (t : HTm ([],x,x,x)) : (HTm.cast t c3L).erase = (HTm.cast t c3R).erase := rfl

/-! ## Row 5: a chain inside a function result -/

def fnSrc : Ty Sr := .all .top bB.weaken
def fnTgt : Ty Sr := .all .top cC.weaken
theorem fn_not_prim : ¬ Prim Γr fnSrc fnTgt := not_prim_of (by decide)
def fnCo : Cert Sr := .seq (.step fnSrc (.all .top xA.weaken)) (.step (.all .top xA.weaken) fnTgt)
theorem fnCo_checks : checkC Γr fnCo fnSrc fnTgt = true := by decide

/-- `Γr, f : ∀(_:⊤) b.B, z : ⊤`. -/
def Γ5 : Ctx (Sr,x,x) := (Γr.cons fnSrc).cons .top

/-- The chain as a callee atom: `(f ▷ fnCo) z : c.C`. -/
theorem row5_callee :
    HTy Γ5 (.app (.cast (.var (.there .here)) ((fnCo.rename Rename.succ).rename Rename.succ)) (.var .here))
      (.sel (.var (.there (.there (.there .here)))) lC) := by decide

/-! ## Row 6: domain contravariance, dependent codomain under the target domain

`F = ∀(z : {D : ⊥..⊤}) z.D`, `G = ∀(z : {D : ⊥..b.B}) c.C`. -/

def zD : Ty (Sr,x) := .sel (.var .here) lD
def domS : Ty Sr := .typ lD .bot .top
def domT : Ty Sr := .typ lD .bot bB
def Fty : Ty Sr := .all domS zD
def Gty : Ty Sr := .all domT cC.weaken

theorem FG_not_prim : ¬ Prim Γr Fty Gty := not_prim_of (by decide)

/-- Domain step first, then three codomain steps under `z : {D : ⊥..b.B}`. -/
def FGco : Cert Sr :=
  .seq (.step Fty (.all domT zD))
    (.seq (.step (.all domT zD) (.all domT bB.weaken))
      (.seq (.step (.all domT bB.weaken) (.all domT xA.weaken))
        (.step (.all domT xA.weaken) Gty)))
theorem FGco_checks : checkC Γr FGco Fty Gty = true := by decide

/-- Under the source domain the codomain chain does not start. -/
theorem cod_under_source : ¬ Prim (Γr.cons domS) zD bB.weaken := not_prim_of (by decide)

/-! ## Row 7: type-member bounds and field covariance -/

def tySrc : Ty Sr := .typ lA cC bB
def tyTgt : Ty Sr := .typ lA bB cC
theorem ty_not_prim : ¬ Prim Γr tySrc tyTgt := not_prim_of (by decide)
/-- Upper bound first (`b.B ⇒ x.A ⇒ c.C`), then lower bound (reversed). -/
def tyCo : Cert Sr :=
  .seq (.step tySrc (.typ lA cC xA))
    (.seq (.step (.typ lA cC xA) (.typ lA cC cC))
      (.seq (.step (.typ lA cC cC) (.typ lA xA cC)) (.step (.typ lA xA cC) tyTgt)))
theorem tyCo_checks : checkC Γr tyCo tySrc tyTgt = true := by decide

def fdCo : Cert Sr := .seq (.step (.fld la bB) (.fld la xA)) (.step (.fld la xA) (.fld la cC))
theorem fd_not_prim : ¬ Prim Γr (.fld la bB) (.fld la cC) := not_prim_of (by decide)
theorem fdCo_checks : checkC Γr fdCo (.fld la bB) (.fld la cC) = true := by decide

/-! ## Row 8: intersections with a selection operand

`ΓI = x : {A : ⊥..{b:⊤}}, y : x.A ∧ {B : ⊥..{a:⊤}}`. -/

def ΓI : Ctx ([],x,x) := .cons (.cons .nil (.typ lA .bot T2)) (.and (.sel (.var .here) lA) (.typ lB .bot T1))
def iy : BVar ([],x,x) .var := .here
theorem sel_operand_lookup : Prim ΓI (.sel (.var iy) lB) T1 := prim?_sound (by decide)
/-- `(S ∧ T) ∧ U ≤₀ S` without transitivity. -/
theorem assoc_proj : Prim ΓI (.and (.and T1 T2) (.sel (.var iy) lB)) T1 := .andL1 (.andL1 .refl)
/-- A selection operand on the left: `x.A ∧ ⊤ ≤₀ {b:⊤}`. -/
theorem sel_operand_left : Prim ΓI (.and (.sel (.var (.there .here)) lA) .top) T2 :=
  prim?_sound (by decide)
/-- The member `A` of `y` behind the selection operand `x.A` is not looked
up through `x.A`'s bound (restriction R3). -/
theorem no_lookup_through_sel : ¬ Prim ΓI (.sel (.var iy) lA) .bot := not_prim_of (by decide)

/-- `ΓI' = x : {A : ⊥..{C:⊥..{a:⊤}}}, y : x.A ∧ {B : ⊥..⊤}`. -/
def ΓI' : Ctx ([],x,x) :=
  .cons (.cons .nil (.typ lA .bot (.typ lC .bot T1))) (.and (.sel (.var .here) lA) (.typ lB .bot .top))

/-- `y.C ≤₀ {a:⊤}` is not primitive: exposure does not read through `x.A`. -/
theorem row8_not_prim : ¬ Prim ΓI' (.sel (.var .here) lC) T1 := not_prim_of (by decide)

/-- The receiver atom `y ▷ step[x.A ∧ {B:⊥..⊤}, {C:⊥..{a:⊤}}]` exposes `C`. -/
theorem row8_receiver :
    synthC ΓI' (.pos (.selU (.cast (.var .here)
        (.step (.and (.sel (.var (.there .here)) lA) (.typ lB .bot .top)) (.typ lC .bot T1))) lC T1))
      = some (.sel (.var .here) lC, T1) := by decide

/-! ## Row 12: bad bounds

`x : {A : ⊤..⊥}`: `⊤ ≤₀ ⊥` is not primitive; the certificate exists under
this assumption. -/

def rA : Ty ([],x) := .sel (.var .here) lA
def Γbad : Ctx ([],x) := .cons .nil (.typ lA .top .bot)
theorem bad_not_prim : ¬ Prim Γbad .top .bot := not_prim_of (by decide)
theorem bad_co : checkC Γbad (.seq (.step .top rA) (.step rA .bot)) .top .bot = true := by decide
theorem bad_not_prim_any : ¬ Prim (Ctx.nil) (.top : Ty []) .bot := by intro h; cases h

/-- `λ(x : {A:⊤..⊥}). λ(z : ⊤). z ▷ (step[⊤, x.A] ; step[x.A, ⊥])`. -/
def badLam : HTm [] :=
  .val (.lam (.typ lA .top .bot) (.val (.lam .top
    (.cast (.atom (.var .here))
      (.seq (.step .top (.sel (.var (.there .here)) lA)) (.step (.sel (.var (.there .here)) lA) .bot))))))
def badLamTy : Ty [] := .all (.typ lA .top .bot) (.all .top .bot)

theorem badLam_typed : HTy .nil badLam badLamTy := by decide

theorem badLam_safe {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, badLam.erase⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety badLam_typed run

/-- `{A : ⊤..⊥}`, under the self binder. -/
def badTy : Ty ([],x) := .typ lA .top .bot

/-- `ν(s : {a : {A:⊤..⊥}}) {a = s.a}`: a closed literal at a bad-bounds field type. -/
theorem loopObj_bad_H :
    HTy .nil (.val (.obj (.fld la badTy) (.trm la (.proj (.var .here) la)))) (.mu (.fld la badTy)) := by
  decide

/-! ## Row 13: mismatched endpoints and a malformed receiver -/

/-- `x.A ∧ x.A` and `x.A` are `≤₀`-equivalent but syntactically different. -/
def mismC : Cert ([],x,x) :=
  .seq (.step T2 e3xA) (.step (.and e3xA e3xA) T1)
theorem mismC_rejected : synthC E3Γ mismC = none := by decide
theorem mismC_parts : checkC E3Γ (.step T2 e3xA) T2 e3xA = true ∧
    checkC E3Γ (.step (.and e3xA e3xA) T1) (.and e3xA e3xA) T1 = true := by
  decide

/-- `{B : ⊥..{a:⊤}}`. -/
def RB : Ty s := .typ lB .bot T1
def DomK : Ty [] := .typ lA .bot RB
def SrcK : Ty [] := .all DomK (.all (.sel (.var .here) lA) (.sel (.var .here) lB))
def DstK : Ty [] := .all DomK (.all (.sel (.var .here) lA) T1)

/-- The receiver `y ▷ step[x.A, {B:⊥..{a:⊤}}]` is checked in `x, y`. -/
def goodK : Cert [] := .pos (.allC DomK (.allC (.sel (.var .here) lA)
  (.selU (.cast (.var .here) (.step (.sel (.var (.there .here)) lA) RB)) lB T1)))
/-- A valid primitive step `⊥ ≤₀ {B:..}` whose source is not `y`'s type. -/
def badK : Cert [] := .pos (.allC DomK (.allC (.sel (.var .here) lA)
  (.selU (.cast (.var .here) (.step .bot RB)) lB T1)))

theorem K_not_primitive : prim? .nil SrcK DstK = false := by decide
theorem goodK_checks : synthC .nil goodK = some (SrcK, DstK) := by decide
theorem goodK_typed : CTy .nil goodK SrcK DstK := synthC_iff.mp goodK_checks
theorem badK_rejected : synthC .nil badK = none := by decide
theorem badK_untyped : ∀ S T, ¬ CTy .nil badK S T := fun _ _ h => by
  have := synthC_complete h; rw [badK_rejected] at this; cases this

/-! ## Row 14: budgets and divergence

`Frontend.Core.LPCtx` is `p : μ(s. {A : ⊥..∀(y : ⊤) s.A}), q : μ(s. {B :
∀(y : ⊤) s.B..⊤})`; the frontend's fuelled search exhausts every tank on
`p.A ∧ ⊥ <: ∀(y:⊤) q.B`.  `prim?` decides it, and the left-operand goal.
`Γloop = r : μ(s. {A : ⊥..s.A})`: decided false, no divergence. -/

open Frontend.Core (LPCtx LPLeft LPRight) in
theorem LP_prim : Prim LPCtx LPLeft LPRight := prim?_sound (by decide)
open Frontend.Core (LPCtx LPLeft LPRight) in
theorem LP_left_operand : ¬ Prim LPCtx (.sel (.var (.there .here)) (.typ 0)) LPRight :=
  not_prim_of (by decide)
open Frontend.Core (LPCtx LPLeft LPRight) in
/-- The next step after the bound is not primitive either: `∀(y:⊤) p.A ≰₀ ∀(y:⊤) q.B`. -/
theorem LP_left_explicit :
    ¬ Prim LPCtx (.all .top (.sel (.var (.there (.there .here))) (.typ 0))) LPRight :=
  not_prim_of (by decide)

def Γloop : Ctx ([],x) := .cons .nil (.mu (.typ lA .bot (.sel (.var .here) lA)))
theorem loop_decided : ¬ Prim Γloop rA T1 := not_prim_of (by decide)

end Selective
