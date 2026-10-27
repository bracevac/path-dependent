import Coercions.PDot.FCp.CanonExamples
import Coercions.PDot.FCp.CanonicalForms
import Coercions.PDot.FCp.Examples
import Coercions.PDot.FCp.LookupSafety
import Coercions.PDot.FCp.Consistency

/-!
# The recorded stores of gate C0, E5 and E7: canonical forms and lookup (plan X, X4)

The stores of `CanonExamples` with the facts that read evidence.  A typing is by the checker over
`decide +kernel`, a normal form or a view is a derivation of `Hnf` or `PV`, and a computed
application view is `decide +kernel` over `appViewOf`.

- R2 holds N1 and N3.  `R2.n1_form`: the member at the alias root has a typed normal form.
  `R2.P_view`, `R2.P_appView`, `R2.step` and `R2.st'_typed`: on N3's store the machine steps by
  `MS-AppEq` to a typed state.  `R2.appViewOf_P` computes the head `eqv φ`.
- RiskA is risk (a): `trans (eqToLe φ) (pi d (z. c))` normalizes to a chain typed atom by atom, and
  its head pushes `φ` into the `pi` where both ends are syntactic (`RiskA.P'_head`,
  `RiskA.appViewOf_P'`).
- RiskC and TwoAlias are risk (c): a member read through one and two alias steps normalizes to the
  definition pair between one bridge per step on each side (`RiskC.eA_hnf`, `TwoAlias.eA2_hnf`).
- N2: no closed evidence relates the twins (`N2.no_alias`, `N2.no_eq`).  N4: a path of function type
  has an application view (`N4.P_app`, `N4.appViewOf_P`).  F1: a field two literals deep has a path
  view (`F1.P_view`).
- R1Closed and R2Closed are the refuter's R1 and R2 against the merged relations: one typed path has
  one view and one head (`R1Closed.PA_one_view`, `R1Closed.bad_head_excluded`), every step from R1's
  state is typed (`R1Closed.st_steps_typed`), and an untyped alias has no application view
  (`R2Closed.no_app_view`, `R2Closed.appViewOf_Pu`).
- Lookup: no lookup of a typed path gets stuck on the cyclic object E13 (`Cyclic.P_safe`), on risk
  (b), a path field whose body is typed through another path field (`RiskB.P_step`, `RiskB.P_safe`),
  on the two-field cycle (`TwoCycle.P_safe`) and on the newer literal forwarding into an older cycle
  (`OlderCycle.P_safe`).  The dangling literal J1, Fact 2 and pDOT's bad bounds have no typing
  (`j1_untyped`, `fact2_blocked`, `badBounds_blocked`).
- E5 and E7 are the final stores of the two programs that run, written in FCp.  E5's holds `x` and
  the literal `o` allocated by `x.d x`, and its answer `o.incr.decr` is safe (`E5.P_safe`).  E7's
  holds `core`, and the module alias `core.m.f` is safe (`E7.P_safe`).
- S1 is consistent: no evidence proves `⊤ ≤ ⊥` (`S1.consistent`).

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.  The computed application views, E5 and E7 are new.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

namespace R2

/-- `x.b ≃ x`, read off the singleton of the field `b`. -/
def πbx : PEq (([],x),x) := .member (.sel (.var (.there .here)) lb 4) (.refl (Ty.sngl x')) 0
theorem πbx_ty : PEq.HasType Γ πbx (x'.sel lb) x' := synthPEq_sound (by decide +kernel)

/-- `N1`: the member at the alias root, `P2 = x.b` at `x`'s type. -/
def P2 : PathCo (([],x),x) := .alias (.sel (.var (.there .here)) lb 4) πbx (.var (.there .here))
def eA : LeCo (([],x),x) := .member P2 (.refl (Γ.ty (.there .here))) 3
theorem eA_ty : LeCo.HasType Γ eA (.sel (x'.sel lb) lA) (.pi (.sel (x'.sel lb) lC) .top) := synthLe_sound (by decide +kernel)

/-- `le_canon` at `eA`: a typed normal form built from the view of `x.b`, with the bridges
`lift (h. X) π` the alias step adds. -/
theorem n1_form : ∃ F, Hnf σ Γ eA (.sel (x'.sel lb) lA) (.pi (.sel (x'.sel lb) lC) .top) F ∧
    FormT Γ σ.erase F (.sel (x'.sel lb) lA) (.pi (.sel (x'.sel lb) lC) .top) :=
  le_canon σ_typed eA_ty

/-- `N3`: `y` cast by `eqToLe φ`, `φ : Π(x∙C)⊤ ≡ Π(x.b∙C)⊤`, applied to `Q : x.b∙C`. -/
def φ : EqCo (([],x),x) := .lift (.pi (.sel (.var .here) lC) .top) (.symm πbx)
theorem φ_ty : EqCo.HasType Γ φ (.pi (.sel x' lC) .top) (.pi (.sel (x'.sel lb) lC) .top) := synthEq_sound (by decide +kernel)
def P : PathCo (([],x),x) := .cast (.var .here) (.eqToLe φ)
def Q : PathCo (([],x),x) :=
  .cast (.var (.there .here)) (.trans (.top (Γ.ty (.there .here)))
    (.trans (.member (.var (.there .here)) (.refl (Γ.ty (.there .here))) 0)
      (.eqToLe (.lift (.sel (.var .here) lC) (.symm πbx)))))
theorem P_ty : PathCo.HasType Γ P (.pi (.sel (x'.sel lb) lC) .top) := synthPath_sound (by decide +kernel)
theorem Q_ty : PathCo.HasType Γ Q (.sel (x'.sel lb) lC) := synthPath_sound (by decide +kernel)

def st : State (([],x),x) := ⟨σ, .nil, .app P Q⟩
theorem st_typed : st.Typed .top :=
  ⟨Γ, .top, σ_typed, checkTm_iff.1 (by decide +kernel), .nil⟩

/-- The closure `y` holds. -/
def S₀ : Ty (([],x),x) := .sel x' lC
def t₀ : Tm ((([],x),x),x) := .cast (.path (.var .here)) (.top (.sel (.var (.there (.there .here))) lC))
theorem σ_get_y : σ.get .here = .lam S₀ t₀ := rfl
theorem t₀_typed : Tm.HasType (Γ.cons (.opaque S₀)) t₀ .top := synthTm_sound (by decide +kernel)

/-- The path view of `P`: the closure of `y` with the one atom `eqv φ`. -/
theorem P_view : PV σ Γ P (.pi (.sel (x'.sel lb) lC) .top) (.fn (.lam S₀ t₀) (.single (.eqv φ))) := by
  have h := PV.cast (σ := σ) (Γ := Γ) (P := .var .here) (e := .eqToLe φ)
    (PV.var (x := .here) (T := Γ.ty .here) rfl) (Hnf.eqToLe φ_ty)
  exact h

/-- The application view of `P` has the head `eqv φ`: `MS-AppEq` fires. -/
theorem P_appView : appView σ P S₀ t₀ (.eqv φ) :=
  ⟨Γ, _, _, .lam S₀ t₀, .single (.eqv φ), _, _, .single (.eqv φ), σ_typed, P_ty, P_view, .lam t₀_typed, rfl, rfl⟩

def st' : State (([],x),x) :=
  ⟨σ, .nil, .cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))⟩

theorem step : Step appView st st' := .appEq P_appView

/-- The acceptance item: the state after `MS-AppEq` on N3's store is typed. -/
theorem st'_typed : st'.Typed .top := by
  refine ⟨Γ, .top, σ_typed, ?_, .nil⟩
  have h := appEq_typed (S := .sel (x'.sel lb) lC) (T := .top) t₀_typed φ_ty Q_ty
  exact h

end R2

/-! ## Risk (a): `trans (eqToLe φ) (pi d (z. c))`, normalized without reading a store -/

namespace RiskA
open R2
def e : LeCo (([],x),x) := .trans (.eqToLe φ) (.pi (.refl (.sel (x'.sel lb) lC)) (.refl .top))
def P' : PathCo (([],x),x) := .cast (.var .here) e
theorem P'_ty : PathCo.HasType Γ P' (.pi (.sel (x'.sel lb) lC) .top) := synthPath_sound (by decide +kernel)
/-- The normal form is the chain `eqv φ ⨾ pi d c`: each atom typed by its own evidence. -/
theorem e_form : Hnf σ Γ e (.pi (.sel x' lC) .top) (.pi (.sel (x'.sel lb) lC) .top)
    ((Form.single (.eqv φ)).append (.single (.pi (.refl (.sel (x'.sel lb) lC)) (.refl .top)))) :=
  .trans (.eqToLe φ_ty) (.pi .refl .refl)
def F₁ : Form (([],x),x) := (Form.single (.eqv φ)).append (.single (.pi (.refl (.sel (x'.sel lb) lC)) (.refl .top)))
theorem P'_view : PV σ Γ P' (.pi (.sel (x'.sel lb) lC) .top) (.fn (.lam S₀ t₀) F₁) := by
  have h := PV.cast (σ := σ) (Γ := Γ) (P := .var .here) (PV.var (x := .here) (T := Γ.ty .here) rfl) e_form
  exact h
/-- At the application the two ends are syntactic function types, and `eqv φ` is pushed into the
`pi` through `dom φ` and `cod φ`. -/
theorem P'_appView : appView σ P' S₀ t₀
    (.pi (pushDom φ (.refl (.sel (x'.sel lb) lC))) (pushCod φ (.refl .top))) :=
  ⟨Γ, _, _, .lam S₀ t₀, F₁, _, _, F₁, σ_typed, P'_ty, P'_view, .lam t₀_typed, rfl, rfl⟩
theorem P'_head : HeadTyped Γ (.pi (pushDom φ (.refl (.sel (x'.sel lb) lC))) (pushCod φ (.refl .top)))
    S₀ .top (.sel (x'.sel lb) lC) .top := by
  obtain ⟨hd, hc, hh⟩ := collapse_typed (Γ := Γ) (γ := σ.erase)
    (F := (Form.single (.eqv φ)).append (.single (.pi (.refl (.sel (x'.sel lb) lC)) (.refl .top))))
    (.cons (.eqv (φ_ty.sound σ_typed)) (.cons (.pi .refl .refl) .nil))
  cases hc
  exact hh
end RiskA

/-! ## Risk (c): a member read through an alias, with the bridges the alias step builds -/

namespace RiskC
open R2
/-- The normal form of `eA = member (alias (x.b) πbx x) refl 3`: the definition pair at `x`, between
the two bridges of the alias step.  None of the three atoms is a subterm of `eA`. -/
def F₀ : Form (([],x),x) :=
  (Form.single (.eqv (.lift (.sel (.var .here) lA) πbx))).append
    ((Form.single (.eqv (.defP x' lA))).append (.single (.eqv (.lift (.pi (.sel (.var .here) lC) .top) (.symm πbx)))))
theorem eA_hnf : Hnf σ Γ eA (.sel (x'.sel lb) lA) (.pi (.sel (x'.sel lb) lC) .top) F₀ := by
  have hP : PV σ Γ P2 (Γ.ty (.there .here)) _ := PV.alias (PV.var rfl)
  exact .member hP .refl (.there .here) rfl rfl
end RiskC

namespace N2

/-- No closed evidence relates the two store variables. -/
theorem no_alias : ¬ ∃ π, PEq.HasType Γ π xp yp := fun ⟨_, h⟩ => canon_apart (alias_canon σ_typed h)
theorem no_eq : ¬ ∃ φ, EqCo.HasType Γ φ (.sel xp lA) (.pi (.sel xp lC) .top) :=
  fun ⟨_, h⟩ => norm_apart (eq_canon σ_typed h)
end N2

namespace N4

def P : PathCo ([],x) := .sel (.var .here) lf 0
theorem P_ty : PathCo.HasType Γ P (.pi .top .top) := synthPath_sound (by decide +kernel)
/-- `x.f` has a function view, and its application view exists with a typed head. -/
theorem P_app : ∃ S₀ t₀ T₀ h, appView σ P S₀ t₀ h ∧ Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ ∧
    HeadTyped Γ h S₀ T₀ .top .top ∧ Runtime.Lookups σ.erase (.defp P.path) (.defv (Value.lam S₀ t₀).erase) :=
  app_view_exists σ_typed P_ty
end N4

namespace F1

def P : PathCo ([],x) := .sel (.sel (.var .here) la 0) lb 2
theorem P_ty : PathCo.HasType Γ P (.mu telB) := synthPath_sound (by decide +kernel)
/-- The view of `x.a.b` at its declared type is the literal view at `x.a.b`. -/
theorem P_view : ∃ W, PV σ Γ P (.mu telB) W ∧ PViewT Γ σ.erase P.path (.mu telB) W := (path_view σ_typed P_ty).2
end F1

/-! ## R1 closed: one typed path, one view, one head (`refute-c0.md` finding 1)

The refuter's path on N4's store (`scratch-refute/R1_PVIndex.lean:35-39`).  Before repair 1 its
cast had a view at every function type, and the index `Π(⊥)⊤` gave a `pi` head whose domain
evidence has no type.  After the repair that head is no application view, and the path has one
view. -/

namespace R1Closed
open N4
abbrev xp : Path ([],x) := .var .here
def Pc : PathCo ([],x) := .cast (.sel (.var .here) lf 0) (.pi (.refl .top) (.refl .top))
def PA : PathCo ([],x) := .sel (.alias (.var .here) (.refl xp) (.fldI xp lf Pc)) lf 0
theorem PA_ty : PathCo.HasType Γ PA (.pi .top .top) := synthPath_sound (by decide +kernel)
def t₀ : Tm (([],x),x) := .path (.var .here)
/-- The bridge the index `Π(⊥)⊤` put after the cast. -/
def χ : EqCo ([],x) := .lift (Ty.pi .bot .top).weaken (.symm (.refl xp))
/-- R1's head: its domain evidence has no type in `Γ`. -/
def d_b : LeCo ([],x) := .trans (.eqToLe (.symm (.dom χ))) (.refl .top)
def c_b : LeCo (([],x),x) :=
  .trans ((LeCo.refl Ty.top).subst (CoSubst.selfCast (.eqToLe (.symm (.dom χ))))) (.eqToLe (.cod χ.weaken (.var .here)))
theorem d_b_untyped : ∀ S T, ¬ LeCo.HasType Γ d_b S T := fun _ _ h => by
  have := synthLe_complete h
  have e : synthLe Γ d_b = none := by decide +kernel
  rw [e] at this
  cases this
/-- The head the refuter's `c0AppView` gave at the index `Π(⊥)⊤` is no application view. -/
theorem bad_head_excluded : ¬ appView σ PA .top t₀ (.pi d_b c_b) := fun h => by
  obtain ⟨T₀, _, hh⟩ := appView_typed σ_typed PA_ty h
  exact d_b_untyped _ _ hh.1
/-- The path has one path view. -/
theorem PA_one_view : ∀ {T T' W W'}, PV σ Γ PA T W → PV σ Γ PA T' W' → W = W' := fun h h' => PV.det h h'
/-- And an application view with a typed head. -/
theorem PA_app : ∃ S₀ t₀ T₀ h, appView σ PA S₀ t₀ h ∧ Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ ∧
    HeadTyped Γ h S₀ T₀ .top .top ∧ Runtime.Lookups σ.erase (.defp PA.path) (.defv (Value.lam S₀ t₀).erase) :=
  app_view_exists σ_typed PA_ty
/-- The refuter's state `⟨σ, [], app PA Qa⟩` (`R1_PVIndex.lean:152-156`). -/
def Qa : PathCo ([],x) := .cast (.var .here) (.top (Γ.ty .here))
def st : State ([],x) := ⟨σ, .nil, .app PA Qa⟩
theorem st_typed : st.Typed .top := ⟨Γ, .top, σ_typed, synthTm_sound (by decide +kernel), .nil⟩
/-- Every step of the merged machine from that state reaches a typed state. -/
theorem st_steps_typed : ∀ st₂ : State ([],x), Step appView st st₂ → st₂.Typed .top :=
  fun _ hs => app_preservation st_typed hs
end R1Closed

/-! ## R2 closed: an untyped alias has no application view (`refute-c0.md` finding 2)

The refuter's path on N3's store (`scratch-refute/R2_AppSound.lean:33`): `alias (var x) (refl x) (var y)`
has the path `x` and, before repair 2, the view of `y`'s closure. -/

namespace R2Closed
open R2
def Pu : PathCo (([],x),x) := .alias (.var (.there .here)) (.refl x') (.var .here)
theorem Pu_untyped : ∀ T, ¬ PathCo.HasType Γ Pu T := fun T h => by
  have := synthPath_complete h
  have e : synthPath Γ Pu = none := by decide +kernel
  rw [e] at this
  cases this
theorem no_app_view : ∀ S₀ t₀ h, ¬ appView σ Pu S₀ t₀ h := by
  intro S₀ t₀ h ⟨Γ', _, _, _, _, _, _, _, hσ', hP, _⟩
  cases Store.Typed.ctx_unique σ_typed hσ'
  exact Pu_untyped _ hP
end R2Closed

namespace TwoAlias
open R2
/-- `x.b.b`, typed at `(x.b).type` by the field `b` read at `x.b`. -/
def Pbb : PathCo (([],x),x) := .sel P2 lb 4
theorem Pbb_ty : PathCo.HasType Γ Pbb (Ty.sngl (x'.sel lb)) := synthPath_sound (by decide +kernel)
/-- `x.b.b ≃ x.b`, read off that singleton. -/
def π₂ : PEq (([],x),x) := .member Pbb (.refl (Ty.sngl (x'.sel lb))) 0
theorem π₂_ty : PEq.HasType Γ π₂ ((x'.sel lb).sel lb) (x'.sel lb) := synthPEq_sound (by decide +kernel)
def P3 : PathCo (([],x),x) := .alias Pbb π₂ P2
def eA2 : LeCo (([],x),x) := .member P3 (.refl (Γ.ty (.there .here))) 3
theorem eA2_ty : LeCo.HasType Γ eA2 (.sel ((x'.sel lb).sel lb) lA) (.pi (.sel ((x'.sel lb).sel lb) lC) .top) :=
  synthLe_sound (by decide +kernel)
theorem eA2_form : ∃ F, Hnf σ Γ eA2 (.sel ((x'.sel lb).sel lb) lA) (.pi (.sel ((x'.sel lb).sel lb) lC) .top) F ∧
    FormT Γ σ.erase F (.sel ((x'.sel lb).sel lb) lA) (.pi (.sel ((x'.sel lb).sel lb) lC) .top) :=
  le_canon σ_typed eA2_ty
/-- The normal form: two bridges on each side of the definition pair at `x`. -/
def F₂ : Form (([],x),x) :=
  (Form.single (.eqv (.lift (.sel (.var .here) lA) π₂))).append
    (((Form.single (.eqv (.lift (.sel (.var .here) lA) πbx))).append
      ((Form.single (.eqv (.defP x' lA))).append (.single (.eqv (.lift (.pi (.sel (.var .here) lC) .top) (.symm πbx)))))).append
      (.single (.eqv (.lift (.pi (.sel (.var .here) lC) .top) (.symm π₂)))))
theorem eA2_hnf : Hnf σ Γ eA2 (.sel ((x'.sel lb).sel lb) lA) (.pi (.sel ((x'.sel lb).sel lb) lC) .top) F₂ := by
  have hP : PV σ Γ P3 (Γ.ty (.there .here)) _ := PV.alias (PV.alias (PV.var rfl))
  exact .member hP .refl (.there .here) rfl rfl
end TwoAlias

/-! ## The computable application view on the recorded stores

`appViewOf` computes, by `decide +kernel`, the closure and the head that `appView` relates, and
`appViewOf_iff` reads the relation back. -/

namespace R2
/-- On N3's store the head is `eqv φ`, so `MS-AppEq` fires. -/
theorem appViewOf_P : appViewOf σ P = some (S₀, t₀, .eqv φ) := by decide +kernel
end R2

namespace RiskA
open R2
/-- The head of risk (a): `eqv φ` pushed into the `pi` atom. -/
theorem appViewOf_P' : appViewOf σ P' =
    some (S₀, t₀, .pi (pushDom φ (.refl (.sel (x'.sel lb) lC))) (pushCod φ (.refl .top))) := by
  decide +kernel
end RiskA

namespace N4
/-- `x.f` is the stored closure with no cast: the head `id`. -/
theorem appViewOf_P : appViewOf σ P = some (.top, .path (.var .here), .id) := by decide +kernel
end N4

namespace R2Closed
open R2
/-- The untyped alias of R2 has no computed application view either. -/
theorem appViewOf_Pu : appViewOf σ Pu = none := by decide +kernel
end R2Closed

end C0Ex

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

namespace Cyclic

def P : PathCo ([],x) := .sel (.var .here) la 0
theorem P_ty : PathCo.HasType Γ P (Ty.sngl ((Path.var .here).sel la)) := synthPath_sound (by decide +kernel)
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
end Cyclic

namespace RiskB

def P : PathCo ([],x) := .sel (.var .here) la 2
theorem P_ty : PathCo.HasType Γ P (Ty.sngl ((Path.var .here).sel lb)) := synthPath_sound (by decide +kernel)
/-- `x.a` steps to `x.b`, typed at the same type through the body evidence of `a`, which reads
the field `b` of the same literal. -/
theorem P_step : (∃ v, Runtime.LStep σ.erase (.defp P.path) (.defv v)) ∨
    (∃ ds, Runtime.LStep σ.erase (.defp P.path) (.nest ds)) ∨
    ∃ Q, Runtime.LStep σ.erase (.defp P.path) (.defp Q.path) ∧ PathCo.HasType Γ Q (Ty.sngl ((Path.var .here).sel lb)) :=
  lookup_step_typed σ_typed P_ty
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
end RiskB

/-! ## J1, Fact 2 and pDOT §2.3: rejected by the tree's typing, so no typed store holds them -/

theorem j1_untyped (P : PathCo ([],x)) (U : Ty []) : ¬ Value.HasType .nil (.obj danglingTel (danglingDefs P)) U :=
  dangling_untyped P U
theorem fact2_blocked (P : PathCo ([],x)) (U : Ty []) : ¬ Value.HasType .nil (.obj fact2Tel (fact2Defs P)) U :=
  fact2_untyped P U
theorem badBounds_blocked (P : PathCo ([],x)) (v : Value ([],x)) (U : Ty []) :
    ¬ Value.HasType .nil (.obj badBoundsTel (badBoundsDefs P v)) U :=
  badBounds_untyped P v U

namespace TwoCycle

def P : PathCo ([],x) := .sel (.var .here) la 0
theorem P_ty : PathCo.HasType Γ P (Ty.sngl ((Path.var .here).sel lb)) := synthPath_sound (by decide +kernel)
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
theorem P_step : (∃ v, Runtime.LStep σ.erase (.defp P.path) (.defv v)) ∨
    (∃ ds, Runtime.LStep σ.erase (.defp P.path) (.nest ds)) ∨
    ∃ Q, Runtime.LStep σ.erase (.defp P.path) (.defp Q.path) ∧ PathCo.HasType Γ Q (Ty.sngl ((Path.var .here).sel lb)) :=
  lookup_step_typed σ_typed P_ty
end TwoCycle

namespace OlderCycle

def P : PathCo (([],x),x) := .sel (.var .here) lc 0
theorem P_ty : PathCo.HasType Γ P (Ty.sngl (yp.sel la)) := synthPath_sound (by decide +kernel)
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
end OlderCycle

namespace E5
/-- `C`, the source's `sg_C`. -/
abbrev cC : Label := .typ 0
/-- `D`, the source's `sg_D`. -/
abbrev cD : Label := .typ 1
/-- `d`, the source's `sg_d`. -/
abbrev cd : Label := .trm 0
/-- `incr`, the source's `sg_incr`. -/
abbrev cincr : Label := .trm 1
/-- `decr`, the source's `sg_decr`. -/
abbrev cdecr : Label := .trm 2
/-- `μ(c : [fld incr c.type])`, the definition of `C`. -/
def WC : Ty s := .mu (.cons .nil (.fld cincr (Ty.sngl (.var .here))))
/-- `μ(d : [is x∙C, fld decr d.type])`, the definition of `D`, `x` the newest variable outside. -/
def WD : Ty (s,x) := .mu (.cons (.cons .nil (.is (.sel (.var (.there .here)) cC))) (.fld cdecr (Ty.sngl (.var .here))))
/-- The annotation of `x`, under its self `x`. -/
def telX : Telescope ([],x) :=
  .cons (.cons (.cons (.cons (.cons .nil (.le WC (.sel (.var .here) cC))) (.le (.sel (.var .here) cC) WC))
    (.le WD (.sel (.var .here) cD))) (.le (.sel (.var .here) cD) WD))
    (.fld cd (.pi .top (.sel (.var (.there .here)) cD)))
/-- `{incr : o.type} ∧ {decr : o.type}`, under its self `o`. -/
def telO : Telescope (s,x) := .cons (.cons .nil (.fld cincr (Ty.sngl (.var .here)))) (.fld cdecr (Ty.sngl (.var .here)))
/-- `{incr = o} ▹ {decr = o}`. -/
def dsO : Defs (s,x) := .fld (.fld .nil cincr (.path (.var .here))) cdecr (.path (.var .here))
/-- `o : μ(o. To) ≤ x∙C`, `x` three binders out: `o`'s `incr` field, then `C`'s definition. -/
def eC : LeCo (((s,x),x),x) :=
  .trans (.obj telO (.fld .nil 0 .none)) (.eqToLe (.symm (.defP (.var (.there (.there .here))) cC)))
/-- `o : μ(o. To) ≤ x∙D`: the bound `is x∙C` by `eC`, the field `decr`, then `D`'s definition. -/
def eD : LeCo (((s,x),x),x) :=
  .trans (.obj telO (.fld (.is .nil eC) 1 .none)) (.eqToLe (.symm (.defP (.var (.there (.there .here))) cD)))
/-- `λ(u : ⊤). let o = ν(o : To) {incr = o, decr = o} in (o : x∙D)`. -/
def vd : Value ([],x) := .lam .top (.lett (.val (.obj telO dsO)) (.cast (.path (.var .here)) eD))
/-- The definitions of `x`: `C = WC`, `D = WD`, `d = vd`. -/
def dsX : Defs ([],x) := .fld (.typ (.typ .nil cC WC) cD WD) cd (.fn vd)
def litX : Value [] := .obj telX dsX
def Γx : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telX) dsX.block)
/-- E5's final store: `x`, then the literal `o` allocated by `x.d x`. -/
def Γ : Ctx (([],x),x) := Γx.cons (.transparent (.mu telO) dsO.block)
def σ : Store (([],x),x) := (Store.nil.cons litX).cons (.obj telO dsO)
theorem litX_typed : Value.HasType .nil litX (.mu telX) := synthValue_sound (by decide +kernel)
theorem σ_typed : Store.Typed σ Γ := .obj (.obj .nil litX_typed) (synthValue_sound (by decide +kernel))
/-- `o.incr ≃ o`, read off the singleton of the field `incr`. -/
def π : PEq (([],x),x) := .member (.sel (.var .here) cincr 0) (.refl (Ty.sngl (.var .here))) 0
/-- The answer `o.incr.decr`: `decr` read at `o.incr` through the alias to `o`. -/
def P : PathCo (([],x),x) := .sel (.alias (.sel (.var .here) cincr 0) π (.var .here)) cdecr 1
theorem P_ty : PathCo.HasType Γ P (Ty.sngl (((Path.var .here).sel cincr))) := synthPath_sound (by decide +kernel)
theorem P_path : P.path = ((Path.var .here).sel cincr).sel cdecr := rfl
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
end E5

namespace E7
/-- `types`, the source's `e7_types`. -/
abbrev ctypes : Label := .trm 0
/-- `f`, the source's `e7_f`. -/
abbrev cf : Label := .trm 1
/-- `m`, the source's `e7_m`. -/
abbrev cm : Label := .trm 2
/-- `A`, the source's `e7_A`. -/
abbrev cA : Label := .typ 0
/-- `{A : ⊤..⊤} ∧ {f : Π(u : ⊤) ⊤}`, under its self `t`. -/
def telT : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .top (.sel (.var .here) cA))) (.le (.sel (.var .here) cA) .top)) (.fld cf (.pi .top .top))
/-- `{A = ⊤} ▹ {f = λ(u : ⊤). u}`. -/
def dsT : Defs s := .fld (.typ .nil cA .top) cf (.fn (.lam .top (.path (.var .here))))
/-- `{types : μ(t. Tt)} ∧ {m : (c.types).type}`, under its self `c`. -/
def telC : Telescope ([],x) := .cons (.cons .nil (.fld ctypes (.mu telT))) (.fld cm (Ty.sngl ((Path.var .here).sel ctypes)))
/-- `{types = ν(t : Tt) …} ▹ {m = c.types}`. -/
def dsC : Defs ([],x) := .fld (.fld .nil ctypes (.nest telT dsT)) cm (.path (.sel (.var .here) ctypes 0))
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telC) dsC.block)
/-- E7's final store: `core` alone, the run allocates nothing else. -/
def σ : Store ([],x) := Store.nil.cons (.obj telC dsC)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
/-- `core.m ≃ core.types`, read off the singleton of the field `m`. -/
def π : PEq ([],x) := .member (.sel (.var .here) cm 1) (.refl (Ty.sngl ((Path.var .here).sel ctypes))) 0
/-- `core.m.f`: `f` read at the module alias `core.m` through the alias to `core.types`. -/
def P : PathCo ([],x) := .sel (.alias (.sel (.var .here) cm 1) π (.sel (.var .here) ctypes 0)) cf 2
theorem P_ty : PathCo.HasType Γ P (.pi .top .top) := synthPath_sound (by decide +kernel)
theorem P_path : P.path = ((Path.var .here).sel cm).sel cf := rfl
theorem P_safe : Runtime.PathSafe σ.erase P.path := path_safe σ_typed P_ty
end E7

end C0Ex

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

namespace S1

/-- The store is consistent: no evidence proves `⊤ ≤ ⊥`. -/
theorem consistent : ¬ ∃ e, LeCo.HasType Γ e .top .bot := no_top_le_bot σ_typed
end S1

end C0Ex

end PDot.FCp

