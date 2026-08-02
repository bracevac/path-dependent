import LambdaP.Original.LookupCounterexample

/-!
Can the arbitrary-state counterexample be reached from a closed source term?

For the natural two-let program the answer is no.  The historical `let` rule
forces the body result under two fresh cells to be `R.weaken.weaken` for a
closed result type `R`; the local singleton `{x.1}` is not such a weakening.
The checked program below therefore observes the body at `Top`.  It reaches
the same path-normalization step, but the successor remains typed at `Top`
and is a final location rather than a stuck state.
-/

namespace LambdaP.Original.ClosedCounterexample

open LookupCounterexample

/-! ## The natural nested-let program -/

abbrev body : Tm 2 := Tm.path selected

abbrev inner : Tm 1 := Tm.let xValue body

abbrev program : Tm 0 := Tm.let yValue inner

theorem body_typed_top : Tm.Ty Γ body Ty.Top := by
  exact Tm.Ty.sub (Tm.Ty.path selected_typing) Tau.Sub.top Tau.Wf.top

theorem inner_typed_top : Tm.Ty Γy inner Ty.Top := by
  exact Tm.Ty.let x_public_typing Tau.Wf.top body_typed_top

theorem program_typed_top : Tm.Ty Ctx.nil program Ty.Top := by
  exact Tm.Ty.let y_precise.toTy Tau.Wf.top inner_typed_top

/-! ## Exact machine trace -/

abbrev s0 : State 0 :=
  ⟨(Store.empty : Store 0), [], program⟩

abbrev s1 : State 0 :=
  ⟨(Store.empty : Store 0), [Tm.Frame.let inner], yValue⟩

abbrev s2 : State 1 :=
  ⟨σy, [], inner⟩

abbrev s3 : State 1 :=
  ⟨σy, [Tm.Frame.let body], xValue⟩

abbrev s4 : State 2 := sourceState

abbrev s5 : State 2 := successorState

theorem step01 : State.Step s0 s1 := State.Step.let_push

theorem step12 : State.Step s1 s2 := State.Step.lift y_value

theorem step23 : State.Step s2 s3 := State.Step.let_push

theorem step34 : State.Step s3 s4 := State.Step.lift x_value

theorem step45 : State.Step s4 s5 := source_steps_to_successor

/-- Heterogeneous reflexive-transitive closure, since allocation changes the
scope index of machine states. -/
inductive State.Reaches : {n : Nat} -> State n -> {m : Nat} -> State m -> Prop where
| refl {n : Nat} {s : State n} : State.Reaches s s
| step {n m l : Nat} {a : State n} {b : State m} {c : State l} :
    State.Step a b -> State.Reaches b c -> State.Reaches a c

theorem program_reaches_s5 : State.Reaches s0 s5 := by
  apply State.Reaches.step step01
  apply State.Reaches.step step12
  apply State.Reaches.step step23
  apply State.Reaches.step step34
  apply State.Reaches.step step45
  exact .refl

theorem initial_state_typed : State.Ty Ctx.nil s0 Ty.Top := by
  exact State.Ty.ok Store.Ty.empty (Tm.Cont.Ty.hole .refl)
    program_typed_top

theorem s1_typed_top : State.Ty Ctx.nil s1 Ty.Top := by
  exact State.Ty.ok Store.Ty.empty
    (Tm.Cont.Ty.cons (Tm.Cont.Ty.hole .refl)
      (Tm.Frame.Ty.let inner_typed_top))
    y_precise.toTy

theorem σy_typed : Store.Ty Γy σy := σy_refined.toTy

theorem s2_typed_top : State.Ty Γy s2 Ty.Top := by
  exact State.Ty.ok σy_typed (Tm.Cont.Ty.hole .refl) inner_typed_top

theorem s3_typed_top : State.Ty Γy s3 Ty.Top := by
  exact State.Ty.ok σy_typed
    (Tm.Cont.Ty.cons (Tm.Cont.Ty.hole .refl)
      (Tm.Frame.Ty.let body_typed_top))
    x_public_typing

theorem s4_typed_top : State.Ty Γ s4 Ty.Top := by
  exact State.Ty.ok store_typed (Tm.Cont.Ty.hole .refl) body_typed_top

theorem y_term_typed_top :
    Tm.Ty Γ (Tm.path (Path.var y)) Ty.Top := by
  exact Tm.Ty.sub
    (Tm.Ty.path (Path.Ty.var y_context_binding))
    Tau.Sub.top Tau.Wf.top

theorem s5_typed_top : State.Ty Γ s5 Ty.Top := by
  exact State.Ty.ok store_typed (Tm.Cont.Ty.hole .refl)
    y_term_typed_top

theorem y_store_binding :
    Store.Binds σ y yValue.weaken.weaken := by
  exact Store.Binds.there Store.Binds.here

theorem s5_final : State.IsFinal s5 := by
  exact State.IsFinal.is_var y_store_binding

/-- The natural closed embedding reaches a typed final state, not a stuck
state. -/
theorem natural_program_reaches_typed_final :
    Tm.Ty Ctx.nil program Ty.Top ∧
    State.Reaches s0 s5 ∧
    State.Ty Γ s5 Ty.Top ∧
    State.IsFinal s5 := by
  exact ⟨program_typed_top, program_reaches_s5, s5_typed_top, s5_final⟩

/-! ## Why the local counterexample type cannot escape the lets -/

/-- There are no intrinsically scoped paths in the empty scope. -/
theorem Path.elim0 (p : Path 0) : False := by
  induction p with
  | var z => exact Fin.elim0 z
  | fst p ih => exact ih
  | sel p a ih => exact ih

/-- Weakening a closed type twice cannot produce a singleton rooted at the
newest store cell `x`. -/
theorem closed_type_cannot_weaken_to_local_singleton (R : Ty 0) :
    R.weaken.weaken ≠ Ty.Single (Path.var x).fst := by
  intro heq
  cases R with
  | Top => cases heq
  | Bot => cases heq
  | Fun S T => cases heq
  | Pair S a d => cases heq
  | Single p => exact Path.elim0 p

theorem no_closed_observation_is_local_singleton :
    ¬ ∃ R : Ty 0,
      R.weaken.weaken = Ty.Single (Path.var x).fst := by
  rintro ⟨R, hR⟩
  exact closed_type_cannot_weaken_to_local_singleton R hR

/-! ## Projection and application-operator probes -/

/-- The alias path does not precisely synthesize a pair, so direct projection
from `x.a` cannot be typed. -/
theorem alias_projection_untypable
    {T : Ty 2} : ¬ Path.Ty Γ selected.fst (Tau.ty T) := by
  intro h
  cases h with
  | fst hp => cases path_typing_known hp

/-- For the application probe, mark `Top` and singleton paths with a
non-variable head.  Function and pair heads are deliberately unmarked. -/
def operationTypeMarked : Ty n -> Prop
| .Top => True
| .Bot => False
| .Fun _ _ => False
| .Pair _ _ _ => False
| .Single p => ¬ p.IsVar

def operationSignatureMarked : Tau n k -> Prop
| .ty T => operationTypeMarked T
| .intv _ _ => True

def NonVariableResultsMarked (Δ : Ctx n) : Prop :=
  ∀ {p T}, Path.Ty Δ p (Tau.ty T) ->
    (¬ p.IsVar) -> operationTypeMarked T

def NonVariableAliases (Δ : Ctx n) : Prop :=
  ∀ {p q}, Path.Ty Δ p (Tau.ty (Ty.Single q)) ->
    (¬ q.IsVar) -> ¬ p.IsVar

/-- A second narrow interpretation of all source-subtyping rules.  It rules
out manufacturing a function or pair head from the non-variable alias path.
Interval rules are again discharged by the checked no-interval invariant. -/
theorem sub_preserves_operation_mark
    {Δ : Ctx n} {k : Kind} {d1 d2 : Tau n k}
    (hresults : NonVariableResultsMarked Δ)
    (halias : NonVariableAliases Δ)
    (hintv : LookupCounterexample.NoIntervals Δ)
    (h : Tau.Sub Δ d1 d2) :
    operationSignatureMarked d1 -> operationSignatureMarked d2 := by
  induction h with
  | refl => exact fun hm => hm
  | trans h1 h2 ih1 ih2 =>
      intro hm
      exact ih2 hresults halias hintv (ih1 hresults halias hintv hm)
  | bot => exact fun hm => hm.elim
  | top => exact fun _ => trivial
  | widen hp => exact fun hm => hresults hp hm
  | symm hp => exact fun hm => halias hp hm
  | sel_hi hp hbounds ihbounds => exact (hintv hp).elim
  | sel_lo hp hbounds ihbounds => exact (hintv hp).elim
  | «fun» hdom hcod ihdom ihcod => exact fun hm => hm.elim
  | pair hfst hsnd ihfst ihsnd => exact fun hm => hm.elim
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty => exact fun _ => trivial

theorem nonvariable_results_marked : NonVariableResultsMarked Γ := by
  intro p T hp hnonvar
  cases path_typing_known hp with
  | y => exact (hnonvar .var).elim
  | x => exact (hnonvar .var).elim
  | fst => trivial
  | sel =>
      intro hv
      cases hv

theorem nonvariable_aliases : NonVariableAliases Γ := by
  intro p q hp hq
  cases path_typing_known hp
  exact selected_not_var

theorem selected_operation_marked :
    operationSignatureMarked (Tau.ty (Ty.Single selected)) :=
  selected_not_var

/-- `x.a` cannot be assigned a function head and therefore cannot serve as
the operator of a typed application. -/
theorem alias_operator_not_function
    {S : Ty 2} {T : Ty 3} :
    ¬ Tm.Ty Γ (Tm.path selected) (Ty.Fun S T) := by
  intro ht
  have hsub := term_path_typing_implies_sub ht
  exact sub_preserves_operation_mark nonvariable_results_marked
    nonvariable_aliases no_intervals hsub selected_operation_marked

/-! The alias *can* be passed as an argument to the stored identity-like
lambda, but this is operationally harmless: both operator and argument
resolve to `y`, and the application steps to the final path `y`. -/

theorem y_path_typing :
    Path.Ty Γ (Path.var y) (Tau.ty yType.weaken.weaken) :=
  Path.Ty.var y_context_binding

theorem y_type_wf : Tau.Wf Γ (Tau.ty yType.weaken.weaken) := by
  exact Tau.Wf.fun Tau.Wf.top
    (Tau.Wf.path (Path.Ty.var Ctx.Binds.here))

theorem y_term_function_typing :
    Tm.Ty Γ (Tm.path (Path.var y)) yType.weaken.weaken := by
  exact Tm.Ty.sub (Tm.Ty.path y_path_typing)
    (Tau.Sub.widen y_path_typing) y_type_wf

theorem alias_argument_application_typing :
    Tm.Ty Γ (Tm.app (Path.var y) selected) (Ty.Single selected) := by
  exact Tm.Ty.app y_term_function_typing body_typed_top

abbrev argumentApplicationState : State 2 :=
  ⟨σ, [], Tm.app (Path.var y) selected⟩

theorem alias_argument_application_steps_final :
    State.Step argumentApplicationState s5 := by
  exact State.Step.app Path.reduce.var selected_reduces_to_y y_store_binding

end LambdaP.Original.ClosedCounterexample
