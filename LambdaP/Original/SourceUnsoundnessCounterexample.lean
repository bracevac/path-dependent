import LambdaP.Original.Machine
import LambdaP.Original.Renaming

/-!
A closed, well-typed source program can reach a stuck application.

The counterexample uses an exact type member `q.A = Top`.  A function `h`
accepts an argument of the selected abstract type `q.A` and returns the path
`q`, but assigns that result the dependent singleton type of its argument.
In the body, with `z : q.A`, the derivation is

`{q} <: Top <: q.A <: {z}`.

The last step is singleton symmetry applied to the precise assumption for
`z`.  An ordinary closure `f` can be passed to `h`, since

`{f} <: type(f) <: Top <: q.A`.

Consequently `h f` has static type `{f}` but evaluates to the location of
the pair `q`.  Binding that result as `r` lets the source type `r` as the
function stored at `f`; evaluation substitutes `q` for `r` and reaches
`q f`, which is stuck because `q` stores a pair rather than an abstraction.
-/

namespace LambdaP.Original
namespace SourceUnsoundnessCounterexample

abbrev label : Name := 0

/-! ## First allocation: the closure `f` -/

abbrev fType0 : Ty 0 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

abbrev fValue0 : Tm 0 :=
  Tm.abs Ty.Top (Tm.path (Path.var 0))

theorem f_value : fValue0.IsValue := by
  exact .abs

theorem f_typed : Tm.Ty Ctx.nil fValue0 fType0 := by
  exact Tm.Ty.abs
    (Tm.Ty.path (Path.Ty.var Ctx.Binds.here)) Tau.Wf.top

abbrev GammaF : Ctx 1 := Ctx.nil.snoc fType0

abbrev sigmaF : Store 1 :=
  Store.val (Store.empty : Store 0) fValue0 f_value

theorem storeF_typed : Store.Ty GammaF sigmaF := by
  exact Store.Ty.val .empty f_typed

/-! ## Second allocation: the exact type member `q.A = Top` -/

abbrev f1 : Fin 1 := 0

abbrev qValue1 : Tm 1 :=
  Tm.pair f1 label (Def.type Ty.Top)

abbrev qType1 : Ty 1 :=
  Ty.Pair (Ty.Single (Path.var f1)) label
    (Tau.intv Ty.Top Ty.Top).weaken

theorem q_value : qValue1.IsValue := by
  exact .pair

theorem q_typed : Tm.Ty GammaF qValue1 qType1 := by
  exact Tm.Ty.tpair Ctx.Binds.here Tau.Wf.top

abbrev GammaQ : Ctx 2 := GammaF.snoc qType1

abbrev sigmaQ : Store 2 := Store.val sigmaF qValue1 q_value

theorem storeQ_typed : Store.Ty GammaQ sigmaQ := by
  exact Store.Ty.val storeF_typed q_typed

abbrev q2 : Fin 2 := 0
abbrev f2 : Fin 2 := 1

abbrev qSel2 : Path 2 := (Path.var q2).sel label

theorem q_binding2 : Ctx.Binds GammaQ q2 qType1.weaken := by
  exact Ctx.Binds.here

theorem f_binding2 : Ctx.Binds GammaQ f2 fType0.weaken.weaken := by
  exact Ctx.Binds.there Ctx.Binds.here

/-- The stored type definition gives the precise interval `Top..Top`. -/
theorem q_selection2 :
    Path.Ty GammaQ qSel2 (Tau.intv Ty.Top Ty.Top) := by
  have hroot : Path.Ty GammaQ (Path.var q2)
      (Tau.ty qType1.weaken) := Path.Ty.var q_binding2
  have hsel := Path.Ty.sel_r hroot
  simpa only [qSel2, qType1, Ty.weaken, Ty.rename, Tau.weaken,
    Tau.rename, Tau.weaken_open] using hsel

theorem q_singleton_wf2 :
    Tau.Wf GammaQ (Tau.ty (Ty.Single qSel2)) := by
  have hroot : Path.Ty GammaQ (Path.var q2)
      (Tau.ty qType1.weaken) := Path.Ty.var q_binding2
  simpa only [qSel2, qType1, Ty.weaken, Ty.rename, Tau.weaken,
    Tau.rename] using (Tau.Wf.sel hroot)

/-! ## Third allocation: the dependent closure `h` -/

abbrev hDomain2 : Ty 2 := Ty.Single qSel2

abbrev z3 : Fin 3 := 0
abbrev q3Body : Fin 3 := 1

abbrev hBody3 : Tm 3 := Tm.path (Path.var q3Body)

abbrev hCodomain3 : Ty 3 := Ty.Single (Path.var z3)

abbrev hType2 : Ty 2 := Ty.Fun hDomain2 hCodomain3

abbrev hValue2 : Tm 2 := Tm.abs hDomain2 hBody3

theorem h_value : hValue2.IsValue := by
  exact .abs

theorem z_binding3 :
    Ctx.Binds (GammaQ.snoc hDomain2) z3 hDomain2.weaken := by
  exact Ctx.Binds.here

theorem q_binding3 :
    Ctx.Binds (GammaQ.snoc hDomain2) q3Body qType1.weaken.weaken := by
  exact Ctx.Binds.there q_binding2

theorem q_selection3 :
    Path.Ty (GammaQ.snoc hDomain2) qSel2.weaken
      (Tau.intv Ty.Top Ty.Top) := by
  simpa only [Tau.weaken, Tau.rename, Ty.rename] using
    (q_selection2.weaken (S := hDomain2))

/-- In `h`'s body, the pair location is assigned the singleton of the
argument: `{q} <: Top <: q.A <: {z}`. -/
theorem h_body_subtyping :
    Tau.Sub (GammaQ.snoc hDomain2)
      (Tau.ty (Ty.Single (Path.var q3Body)))
      (Tau.ty (Ty.Single (Path.var z3))) := by
  apply Tau.Sub.trans Tau.Sub.top
  apply Tau.Sub.trans
  · exact Tau.Sub.sel_lo q_selection3 Tau.Sub.refl
  · exact Tau.Sub.symm (Path.Ty.var z_binding3)

theorem h_body_typed :
    Tm.Ty (GammaQ.snoc hDomain2) hBody3 hCodomain3 := by
  exact Tm.Ty.sub
    (Tm.Ty.path (Path.Ty.var q_binding3))
    h_body_subtyping
    (Tau.Wf.path (Path.Ty.var z_binding3))

theorem h_typed : Tm.Ty GammaQ hValue2 hType2 := by
  exact Tm.Ty.abs h_body_typed q_singleton_wf2

theorem h_type_wf : Tau.Wf GammaQ (Tau.ty hType2) := by
  exact Tau.Wf.fun q_singleton_wf2
    (Tau.Wf.path (Path.Ty.var z_binding3))

abbrev GammaH : Ctx 3 := GammaQ.snoc hType2

abbrev sigmaH : Store 3 := Store.val sigmaQ hValue2 h_value

theorem storeH_typed : Store.Ty GammaH sigmaH := by
  exact Store.Ty.val storeQ_typed h_typed

abbrev h3 : Fin 3 := 0
abbrev q3 : Fin 3 := 1
abbrev f3 : Fin 3 := 2

abbrev fType3 : Ty 3 := fType0.weaken.weaken.weaken
abbrev resultType3 : Ty 3 := Ty.Single (Path.var f3)

theorem h_binding3 : Ctx.Binds GammaH h3 hType2.weaken := by
  exact Ctx.Binds.here

theorem q_bindingH : Ctx.Binds GammaH q3 qType1.weaken.weaken := by
  exact Ctx.Binds.there q_binding2

theorem f_binding3 : Ctx.Binds GammaH f3 fType3 := by
  exact Ctx.Binds.there f_binding2

theorem h_path_function_typed :
    Tm.Ty GammaH (Tm.path (Path.var h3)) hType2.weaken := by
  have hp : Path.Ty GammaH (Path.var h3)
      (Tau.ty hType2.weaken) := Path.Ty.var h_binding3
  exact Tm.Ty.sub (Tm.Ty.path hp) (Tau.Sub.widen hp)
    (h_type_wf.weaken (S := hType2))

theorem q_selectionH :
    Path.Ty GammaH qSel2.weaken (Tau.intv Ty.Top Ty.Top) := by
  simpa only [Tau.weaken, Tau.rename, Ty.rename] using
    (q_selection2.weaken (S := hType2))

/-- The closure `f` is accepted at `h`'s selected abstract domain via
`{f} <: type(f) <: Top <: q.A`. -/
theorem f_argument_typed :
    Tm.Ty GammaH (Tm.path (Path.var f3)) hDomain2.weaken := by
  have hp : Path.Ty GammaH (Path.var f3) (Tau.ty fType3) :=
    Path.Ty.var f_binding3
  apply Tm.Ty.sub (Tm.Ty.path hp)
  · apply Tau.Sub.trans (Tau.Sub.widen hp)
    apply Tau.Sub.trans Tau.Sub.top
    exact Tau.Sub.sel_lo q_selectionH Tau.Sub.refl
  · exact q_singleton_wf2.weaken (S := hType2)

abbrev hApplication3 : Tm 3 :=
  Tm.app (Path.var h3) (Path.var f3)

/-- Statically, `h f` returns the singleton `{f}`. -/
theorem h_application_typed :
    Tm.Ty GammaH hApplication3 resultType3 := by
  have happ := Tm.Ty.app h_path_function_typed f_argument_typed
  simpa only [hApplication3, hType2, hCodomain3, Ty.weaken,
    Ty.rename, Ty.open, Ty.subst, Path.subst, PathSubst.openAt_zero]
    using happ

/-! ## Use the false singleton as a function -/

abbrev r4 : Fin 4 := 0
abbrev f4 : Fin 4 := 3

abbrev finalApplication4 : Tm 4 :=
  Tm.app (Path.var r4) (Path.var f4)

theorem r_binding4 :
    Ctx.Binds (GammaH.snoc resultType3) r4 resultType3.weaken := by
  exact Ctx.Binds.here

theorem f_binding4 :
    Ctx.Binds (GammaH.snoc resultType3) f4 fType3.weaken := by
  exact Ctx.Binds.there f_binding3

/-- Since `r : {f}`, widening gives `{r} <: {f}`; widening `f` then exposes
the function type stored at `f`. -/
theorem r_function_typed :
    Tm.Ty (GammaH.snoc resultType3)
      (Tm.path (Path.var r4)) fType3.weaken := by
  have hr : Path.Ty (GammaH.snoc resultType3) (Path.var r4)
      (Tau.ty resultType3.weaken) := Path.Ty.var r_binding4
  have hf : Path.Ty (GammaH.snoc resultType3) (Path.var f4)
      (Tau.ty fType3.weaken) := Path.Ty.var f_binding4
  apply Tm.Ty.sub (Tm.Ty.path hr)
  · exact Tau.Sub.trans (Tau.Sub.widen hr) (Tau.Sub.widen hf)
  · exact (Tau.Wf.fun Tau.Wf.top
      (Tau.Wf.path (Path.Ty.var Ctx.Binds.here))).weaken
        (S := qType1) |>.weaken (S := hType2) |>.weaken (S := resultType3)

theorem f_top_typed4 :
    Tm.Ty (GammaH.snoc resultType3)
      (Tm.path (Path.var f4)) Ty.Top := by
  have hf : Path.Ty (GammaH.snoc resultType3) (Path.var f4)
      (Tau.ty fType3.weaken) := Path.Ty.var f_binding4
  exact Tm.Ty.sub (Tm.Ty.path hf)
    (Tau.Sub.trans (Tau.Sub.widen hf) Tau.Sub.top) Tau.Wf.top

theorem final_application_typed_singleton :
    Tm.Ty (GammaH.snoc resultType3)
      finalApplication4 (Ty.Single (Path.var f4)) := by
  have happ := Tm.Ty.app r_function_typed f_top_typed4
  simpa only [finalApplication4, fType3, fType0, Ty.weaken,
    Ty.rename, Ty.open, Ty.subst, Path.subst,
    PathSubst.openAt_zero] using happ

theorem final_application_typed_top :
    Tm.Ty (GammaH.snoc resultType3) finalApplication4 Ty.Top := by
  exact Tm.Ty.sub final_application_typed_singleton Tau.Sub.top Tau.Wf.top

/-! ## The closed program -/

abbrev afterH3 : Tm 3 := Tm.let hApplication3 finalApplication4

abbrev afterQ2 : Tm 2 := Tm.let hValue2 afterH3

abbrev afterF1 : Tm 1 := Tm.let qValue1 afterQ2

abbrev program : Tm 0 := Tm.let fValue0 afterF1

theorem afterH_typed : Tm.Ty GammaH afterH3 Ty.Top := by
  exact Tm.Ty.let h_application_typed Tau.Wf.top
    final_application_typed_top

theorem afterQ_typed : Tm.Ty GammaQ afterQ2 Ty.Top := by
  exact Tm.Ty.let h_typed Tau.Wf.top afterH_typed

theorem afterF_typed : Tm.Ty GammaF afterF1 Ty.Top := by
  exact Tm.Ty.let q_typed Tau.Wf.top afterQ_typed

theorem program_typed : Tm.Ty Ctx.nil program Ty.Top := by
  exact Tm.Ty.let f_typed Tau.Wf.top afterF_typed

/-! ## Exact machine execution -/

abbrev s0 : State 0 :=
  ⟨(Store.empty : Store 0), [], program⟩

abbrev s1 : State 0 :=
  ⟨(Store.empty : Store 0), [Tm.Frame.let afterF1], fValue0⟩

abbrev s2 : State 1 :=
  ⟨sigmaF, [], afterF1⟩

abbrev s3 : State 1 :=
  ⟨sigmaF, [Tm.Frame.let afterQ2], qValue1⟩

abbrev s4 : State 2 :=
  ⟨sigmaQ, [], afterQ2⟩

abbrev s5 : State 2 :=
  ⟨sigmaQ, [Tm.Frame.let afterH3], hValue2⟩

abbrev s6 : State 3 :=
  ⟨sigmaH, [], afterH3⟩

abbrev s7 : State 3 :=
  ⟨sigmaH, [Tm.Frame.let finalApplication4], hApplication3⟩

/-- Applying `h` to `f` returns the pair location `q`, despite the static
result type `{f}`. -/
abbrev s8 : State 3 :=
  ⟨sigmaH, [Tm.Frame.let finalApplication4],
    Tm.path (Path.var q3)⟩

/-- The let-frame substitutes `q` for `r`, exposing the stuck application. -/
abbrev endpoint : State 3 :=
  ⟨sigmaH, [], Tm.app (Path.var q3) (Path.var f3)⟩

theorem step01 : State.Step s0 s1 := by
  exact State.Step.let_push

theorem step12 : State.Step s1 s2 := by
  exact State.Step.lift f_value

theorem step23 : State.Step s2 s3 := by
  exact State.Step.let_push

theorem step34 : State.Step s3 s4 := by
  exact State.Step.lift q_value

theorem step45 : State.Step s4 s5 := by
  exact State.Step.let_push

theorem step56 : State.Step s5 s6 := by
  exact State.Step.lift h_value

theorem step67 : State.Step s6 s7 := by
  exact State.Step.let_push

theorem h_store_binding :
    Store.Binds sigmaH h3 hValue2.weaken := by
  exact Store.Binds.here

theorem step78 : State.Step s7 s8 := by
  simpa only [s7, s8, hApplication3, hValue2, hBody3,
    Tm.weaken, Tm.rename, Path.rename, Tm.open,
    FinFun.ext_succ, FinFun.weaken_apply, FinFun.openAt_succ] using
    (State.Step.app (k := [Tm.Frame.let finalApplication4])
      (p := Path.var h3) (q := Path.var f3)
      Path.reduce.var Path.reduce.var h_store_binding)

theorem step8_endpoint : State.Step s8 endpoint := by
  simpa only [s8, endpoint, finalApplication4, Tm.open, Tm.rename,
    Path.rename, FinFun.openAt_zero, FinFun.openAt_succ] using
    (State.Step.rename (σ := sigmaH) (k := [])
      (t := finalApplication4) (x := q3))

/-- Heterogeneous reflexive-transitive closure, needed because allocation
changes the scope index of configurations. -/
inductive Reaches : {n : Nat} -> State n -> {m : Nat} -> State m -> Prop where
| refl {n : Nat} {s : State n} : Reaches s s
| step {n m l : Nat} {a : State n} {b : State m} {c : State l} :
    State.Step a b -> Reaches b c -> Reaches a c

theorem program_reaches_endpoint : Reaches s0 endpoint := by
  apply Reaches.step step01
  apply Reaches.step step12
  apply Reaches.step step23
  apply Reaches.step step34
  apply Reaches.step step45
  apply Reaches.step step56
  apply Reaches.step step67
  apply Reaches.step step78
  apply Reaches.step step8_endpoint
  exact .refl

theorem initial_state_typed : State.Ty Ctx.nil s0 Ty.Top := by
  exact State.Ty.ok Store.Ty.empty (Tm.Cont.Ty.hole Tau.Sub.refl)
    program_typed

/-! ## The endpoint is genuinely stuck -/

theorem q_store_binding :
    Store.Binds sigmaH q3 qValue1.weaken.weaken := by
  exact Store.Binds.there Store.Binds.here

theorem q_not_abstraction :
    forall {A : Ty 3} {body : Tm 4},
      ¬ Store.Binds sigmaH q3 (Tm.abs A body) := by
  intro A body habs
  have heq := habs.unique q_store_binding
  cases heq

theorem endpoint_not_final : ¬ State.IsFinal endpoint := by
  intro hfinal
  cases hfinal with
  | is_val hv => cases hv

def HasStep {n : Nat} (s : State n) : Prop :=
  exists m : Nat, exists s' : State m, State.Step s s'

theorem endpoint_no_step : ¬ HasStep endpoint := by
  rintro ⟨m, s, hstep⟩
  cases hstep with
  | app hq hf hbind =>
      cases hq
      exact q_not_abstraction hbind

/-- A closed source term is well typed at `Top`, reaches the displayed
application, and that application is neither final nor reducible. -/
theorem closed_source_unsoundness :
    State.Ty Ctx.nil s0 Ty.Top ∧
    Reaches s0 endpoint ∧
    ¬ State.IsFinal endpoint ∧
    ¬ HasStep endpoint := by
  exact ⟨initial_state_typed, program_reaches_endpoint,
    endpoint_not_final, endpoint_no_step⟩

end SourceUnsoundnessCounterexample
end LambdaP.Original
