import Coercions.Nominal.Frontend.Examples
import Coercions.Nominal.Translation.Provenance

/-!
# Run-time provenance of the front end's class programs (plan XII, stage NR)

The images of the running example and of the tagged nested and self classes meet the initial
condition.  A factory of modules declares two classes of one label: the record names the module whose
constructor ran, and the instance's evidence moved to the other module fails the predicate.  An
instance read through a path field is an `alias` whose path is a selection: the corollary names its
store variable up to `canon`.  Every focus path at a class type of these runs is in the fragment.
-/

namespace NominalFrontend.ProvEx

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.FCn

/-! ### The front end's running example `Run_src` and the tagged nested and self classes -/

namespace Front
open NominalFrontend NominalFrontend.Examples

theorem run_init : (compile {} Λ14 Run_src).map (fun r => Tm.InitSeals r.2.deriv.translate) = some true := by
  decide +kernel
theorem run_every_state : (compile {} Λ14 Run_src).map (fun r => arunAll 40 (startA r.2.deriv.translate)) =
    some (List.replicate 20 true) := by decide +kernel
theorem run_keys : (compile {} Λ14 Run_src).map (fun r =>
    storeKeys (arun 40 (startA r.2.deriv.translate)).1 (arun 40 (startA r.2.deriv.translate)).2.A
      [Nominal.Source.e14_T, Nominal.Source.e14_C]) =
    some [[(1, Nominal.Source.e14_T), (1, Nominal.Source.e14_C)], []] := by
  decide +kernel
theorem nestTag_init : (compile {} ΛO NestTag_src).map (fun r => Tm.InitSeals r.2.deriv.translate) = some true := by
  decide +kernel
theorem selfTag_init : (compile {} ΛO SelfTag_src).map (fun r => Tm.InitSeals r.2.deriv.translate) = some true := by
  decide +kernel
end Front

/-! ### A factory of modules: two classes of one label, told apart by the owner -/

namespace Factory
open NominalFrontend NominalFrontend.Examples

def Fac_src : STm := pdc% let f = λ(u : ⊤). ν(o) {class C = μ(z. {a : ⊤}) ∧ ⊤,
  mk2 : ∀(u : ⊤) o.C = λ(u : ⊤). ν(i) as o.C {a = u}} in
  let ma = f f in let mb = f f in let a = ma.mk2 mb in a

theorem compiles : (compile {} ΛO Fac_src).isSome = true := by decide +kernel
def t : Tm [] := ((compile {} ΛO Fac_src).get compiles).2.deriv.translate
theorem init : Tm.InitSeals t = true := by decide +kernel
theorem every_state : arunAll 60 (startA t) = List.replicate 22 true := by decide +kernel
theorem final : State.finalB (arun 60 (startA t)).2.st = true := by decide +kernel
/-- The instance `i` (index 0) is sealed at `ma∙C` (`ma` of index 2), and at no other owner. -/
theorem keys : storeKeys (arun 60 (startA t)).1 (arun 60 (startA t)).2.A [.typ 0] = [[(2, .typ 0)], [], [], []] := by
  decide +kernel

abbrev lC : Label := .typ 0
abbrev S4 : Sig := (((([],x),x),x),x)
def at4 : (s : Sig) × AState s → Option (AState S4)
  | ⟨[.var, .var, .var, .var], g⟩ => some g
  | _ => none
theorem at4_some : (at4 (arun 60 (startA t))).isSome = true := by decide +kernel
def gF : AState S4 := (at4 (arun 60 (startA t))).get at4_some
theorem ctx_some : (Store.ctx gF.st.σ).isSome = true := by decide +kernel
def ΓF : Ctx S4 := (Store.ctx gF.st.σ).get ctx_some
theorem hσ : Store.Typed gF.st.σ ΓF := Store.ctx_sound (Option.some_get ctx_some).symm

abbrev iv : BVar S4 .var := .here
abbrev mb : Path S4 := .var (.there .here)
abbrev ma : Path S4 := .var (.there (.there .here))

def instCast : PathCo s → Option (PathCo s × LeCo s)
  | .cast P e => if (LeCo.lastSeal e).isSome then some (P, e) else instCast P
  | _ => none
def focusCast (st : State s) : Option (PathCo s × LeCo s) :=
  match st.t with
  | .path P => instCast P
  | _ => none
theorem ev_some : (focusCast gF.st).isSome = true := by decide +kernel
def P0 : PathCo S4 := ((focusCast gF.st).get ev_some).1
def EF : LeCo S4 := ((focusCast gF.st).get ev_some).2
theorem P0_path : P0.path = .var .here := by decide +kernel
theorem ev_last : LeCo.lastSeal EF = some (ma, lC) := by decide +kernel
theorem A_ma : gF.A iv (ma, lC) = true := by decide +kernel
theorem A_mb : gF.A iv (mb, lC) = false := by decide +kernel

def reOwner (q : Path s) : LeCo s → LeCo s
  | .seal _ C => .seal q C
  | .trans e f => .trans e (reOwner q f)
  | e => e
def Pinst : PathCo S4 := .cast P0 EF
def Pmb : PathCo S4 := .cast P0 (reOwner mb EF)

theorem Pinst_typed : synthPath ΓF Pinst = some (.sel ma lC) := by decide +kernel
theorem Pmb_typed : synthPath ΓF Pmb = some (.sel mb lC) := by decide +kernel
/-- The instance's own path meets the predicate under the run's record. -/
theorem Pinst_ok : PathCo.sealsOK gF.A Pinst = true := by decide +kernel
/-- The same evidence ending at `mb∙C` is typed and fails it: the record names `ma`, not `mb`. -/
theorem Pmb_fails : PathCo.sealsOK gF.A Pmb = false := by decide +kernel

theorem cls_ma_some : (ΓF.clsOf (.sel ma lC)).isSome = true := by decide +kernel
theorem canon_ma : ΓF.canon ma = some ma := by decide +kernel
theorem res_ma : ΓF.res (.sel ma lC) = .sel ma lC := Ctx.res_cls (Option.some_get cls_ma_some).symm
/-- The corollary at the instance: it names `i`, recorded at a class below `ma∙C`. -/
theorem corollary_ma : ∃ y q D, ΓF.canon Pinst.path = ΓF.canon (.var y) ∧ gF.A y (q, D) = true ∧
    Below ΓF ma lC (.sel q D) :=
  frag_provenance hσ Pinst (Or.inr (by decide +kernel)) Pinst_ok (synthPath_sound Pinst_typed)
    (.self res_ma canon_ma)
end Factory

/-! ### An instance read through a path field: the `alias` case through `canon` -/

namespace Fwd
open NominalFrontend NominalFrontend.Examples

def ΛF : LabelTable := [("o", .trm 0), ("mk", .trm 1), ("a", .trm 2), ("b", .trm 4), ("C", .typ 0)]
def Fwd_src : STm := pdc% let σ = ν(σ) {o = ν(o) {class C = μ(z. {a : ⊤}) ∧ ⊤},
  mk : ∀(u : ⊤) σ.o.C = λ(u : ⊤). ν(i) as σ.o.C {a = u}} in
  let x = σ.mk σ in let n = ν(n) {b = x} in let r : σ.o.C = n.b in r
theorem compiles : (compile {} ΛF Fwd_src).isSome = true := by decide +kernel
def t : Tm [] := ((compile {} ΛF Fwd_src).get compiles).2.deriv.translate
theorem init : Tm.InitSeals t = true := by decide +kernel
theorem every_state : (arunAll 60 (startA t)).all (· = true) = true := by decide +kernel

/-- The fragment, decided. -/
def fragB : PathCo s → Bool
  | .var _ => true
  | .cast P e => fragB P || (LeCo.lastSeal e).isSome
  | .both _ _ P Q => fragB P && fragB Q
  | .alias _ _ Q => fragB Q
  | .fold _ P => fragB P
  | .sngl _ _ _ => true
  | .fldI _ _ _ => true
  | .sel _ _ _ => false
  | .unfold _ => false
theorem fragB_sound : ∀ (P : PathCo s), fragB P = true → PathCo.Frag P
  | .var _, _ => trivial
  | .cast P e, h => by
      simp only [fragB, Bool.or_eq_true] at h
      rcases h with h1 | h
      · exact .inl (fragB_sound P h1)
      · exact .inr h
  | .both _ _ P Q, h => by
      simp only [fragB, Bool.and_eq_true] at h
      exact ⟨fragB_sound P h.1, fragB_sound Q h.2⟩
  | .alias _ _ Q, h => fragB_sound Q h
  | .fold _ P, h => fragB_sound P h
  | .sngl _ _ _, _ => trivial
  | .fldI _ _ _, _ => trivial
  | .sel _ _ _, h => by simp [fragB] at h
  | .unfold _, h => by simp [fragB] at h

def isAlias : PathCo s → Bool
  | .alias _ _ _ => true
  | _ => false
/-- The first state whose focus is an `alias`, within `m` steps. -/
def firstAlias : Nat → (s : Sig) × AState s → Option ((s : Sig) × AState s)
  | 0, _ => none
  | m+1, ⟨s, g⟩ =>
      match g.st.t with
      | .path P => if isAlias P then some ⟨s, g⟩ else
          match astepOf g with
          | some p => firstAlias m p
          | none => none
      | _ =>
          match astepOf g with
          | some p => firstAlias m p
          | none => none
abbrev S3 : Sig := ((([],x),x),x)
def at3 : Option ((s : Sig) × AState s) → Option (AState S3)
  | some ⟨[.var, .var, .var], g⟩ => some g
  | _ => none
theorem at3_some : (at3 (firstAlias 60 (startA t))).isSome = true := by decide +kernel
def gA : AState S3 := (at3 (firstAlias 60 (startA t))).get at3_some
def focus : PathCo S3 := match gA.st.t with
  | .path P => P
  | _ => .var .here
theorem focus_eq : gA.st.t = .path focus := by decide +kernel
theorem focus_alias : isAlias focus = true := by decide +kernel
/-- The path of the alias is a selection `n∙b`, no variable. -/
theorem focus_path_sel : focus.path.isSel = true := by decide +kernel
theorem focus_frag : fragB focus = true := by decide +kernel
theorem ctx_some : (Store.ctx gA.st.σ).isSome = true := by decide +kernel
def ΓA : Ctx S3 := (Store.ctx gA.st.σ).get ctx_some
theorem hσ : Store.Typed gA.st.σ ΓA := Store.ctx_sound (Option.some_get ctx_some).symm
theorem typed_some : (synthPath ΓA focus).isSome = true := by decide +kernel
def TA : Ty S3 := (synthPath ΓA focus).get typed_some
def pA : Path S3 := match ΓA.res TA with
  | .sel p _ => p
  | _ => .var .here
def CA : Label := match ΓA.res TA with
  | .sel _ C => C
  | _ => .typ 99
theorem res_TA : ΓA.res TA = .sel pA CA := by decide +kernel
theorem canon_some : (ΓA.canon pA).isSome = true := by decide +kernel
def cA : Path S3 := (ΓA.canon pA).get canon_some
theorem cls_some : (ΓA.clsOf (.sel pA CA)).isSome = true := by decide +kernel
theorem gA_ok : State.SealsAtCtors gA.A gA.st = true := by decide +kernel
theorem canon_cA : ΓA.canon pA = some cA := (Option.some_get canon_some).symm
theorem TA_eq : synthPath ΓA focus = some TA := (Option.some_get typed_some).symm
attribute [irreducible] gA focus ΓA TA pA CA cA
theorem focus_typed : PathCo.HasType ΓA focus TA := synthPath_sound TA_eq
theorem focus_below : Below ΓA cA CA TA := .self res_TA canon_cA
theorem focus_ok : PathCo.sealsOK gA.A focus = true := State.focus_sealsOK gA_ok focus_eq
theorem focus_frag' : PathCo.Frag focus := fragB_sound focus focus_frag
/-- The corollary at the alias through the field `n∙b`: it names, up to `canon`, a store variable
recorded at a class below the focus's class. -/
theorem corollary_alias : ∃ y q D, ΓA.canon focus.path = ΓA.canon (.var y) ∧ gA.A y (q, D) = true ∧
    Below ΓA cA CA (.sel q D) :=
  frag_provenance hσ focus focus_frag' focus_ok focus_typed focus_below
end Fwd


/-! ### Every focus path at a class type of these runs is in the fragment -/

namespace Coverage
open NominalFrontend NominalFrontend.Examples

def classFocus (g : AState s) : Option Bool :=
  match g.st.t, Store.ctx g.st.σ with
  | .path P, some Γ =>
      match synthPath Γ P with
      | some T =>
          match Γ.res T with
          | .sel p C => if (Γ.clsOf (.sel p C)).isSome then some (Fwd.fragB P) else none
          | _ => none
      | none => none
  | _, _ => none

def runClass : Nat → (s : Sig) × AState s → List Bool
  | 0, ⟨_, g⟩ => (classFocus g).toList
  | m+1, ⟨_, g⟩ =>
      match astepOf g with
      | some p => (classFocus g).toList ++ runClass m p
      | none => (classFocus g).toList

theorem N1_cover : runClass 40 (startA Class.progC) = [true] := by decide +kernel
theorem E14_cover : runClass 40 (startA Nominal.Source.E14_d.translate) = [true, true] := by decide +kernel
theorem Run_cover : (compile {} Λ14 Run_src).map (fun r => runClass 60 (startA r.2.deriv.translate)) =
    some (List.replicate 7 true) := by decide +kernel
theorem Fwd_cover : runClass 60 (startA Fwd.t) = List.replicate 6 true := by decide +kernel
theorem Fac_cover : runClass 60 (startA Factory.t) = List.replicate 4 true := by decide +kernel
end Coverage

end NominalFrontend.ProvEx
