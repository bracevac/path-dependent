import LambdaPHistory.StoreRefinement
import LambdaPHistory.Machine
import LambdaPHistory.PathFunctionality

/-!
A concrete obstruction to dependent-selection preservation for the historical
public store typing.

The store has two cells.  Location `y` contains a small lambda.  Location `x`
contains `<y, a = y>`, but its public context type is widened to
`<Top, a : {self}>`.  Consequently `x.a` synthesizes `{x.1}` while lookup
returns `y`.  The refined store remembers the hidden precise pair type and
the subtype derivation, but the static context alone has no conversion from
the runtime equality `x.1 ↦ y`.
-/

namespace LambdaPHistory.LookupCounterexample

abbrev label : Name := 0

/-! ## The first cell: a minimal lambda at `y` -/

abbrev yType : Ty 0 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

abbrev yValue : Tm 0 :=
  Tm.abs Ty.Top (Tm.path (Path.var 0))

theorem y_value : yValue.IsValue := by
  exact .abs

theorem y_precise : Tm.PreciseTy Ctx.nil yValue yType := by
  exact Tm.PreciseTy.abs
    (Tm.Ty.path (Path.Ty.var Ctx.Binds.here))
    Tau.Wf.top

abbrev Γy : Ctx 1 := Ctx.nil.snoc yType

abbrev σy : Store 1 :=
  Store.val (Store.empty : Store 0) yValue y_value

theorem σy_refined : Store.RefinedTy Γy σy := by
  exact Store.RefinedTy.val .empty y_precise y_precise.toTy .refl y_value

/-! ## The second cell: `<y, a = y>` with a widened dependent public type -/

abbrev y₁ : Fin 1 := 0

abbrev xValue : Tm 1 :=
  Tm.pair y₁ label (Def.val y₁)

theorem x_value : xValue.IsValue := by
  exact .pair

/-- The syntax-directed type of `<y, a = y>`. -/
abbrev xPreciseType : Ty 1 :=
  Ty.Pair (Ty.Single (Path.var y₁)) label
    (Tau.ty (Ty.Single (Path.var y₁).weaken))

/-- The public type hides the first component behind `Top`; the member type
is the singleton of the pair binder itself. -/
abbrev xPublicType : Ty 1 :=
  Ty.Pair Ty.Top label
    (Tau.ty (Ty.Single (Path.var (0 : Fin 2))))

theorem x_precise : Tm.PreciseTy Γy xValue xPreciseType := by
  exact Tm.PreciseTy.pair Ctx.Binds.here Ctx.Binds.here

/-- The crucial dependent widening.  Under the source first-component
singleton, the fresh pair binder is itself known to be the old `y`. -/
theorem x_precise_sub_public :
    Tau.Sub Γy (Tau.ty xPreciseType) (Tau.ty xPublicType) := by
  apply Tau.Sub.pair Tau.Sub.top
  apply Tau.Sub.symm
  exact Path.Ty.var Ctx.Binds.here

theorem x_public_wf : Tau.Wf Γy (Tau.ty xPublicType) := by
  exact Tau.Wf.pair Tau.Wf.top
    (Tau.Wf.path (Path.Ty.var Ctx.Binds.here))

theorem x_public_typing : Tm.Ty Γy xValue xPublicType := by
  exact Tm.Ty.sub x_precise.toTy x_precise_sub_public x_public_wf

abbrev Γ : Ctx 2 := Γy.snoc xPublicType

abbrev σ : Store 2 := Store.val σy xValue x_value

theorem store_refined : Store.RefinedTy Γ σ := by
  exact Store.RefinedTy.val σy_refined x_precise x_public_typing
    x_precise_sub_public x_value

theorem store_typed : Store.Ty Γ σ := store_refined.toTy

/-! ## Static synthesis and dynamic lookup disagree on path syntax -/

abbrev x : Fin 2 := 0
abbrev y : Fin 2 := 1

abbrev selected : Path 2 := (Path.var x).sel label

abbrev selectedType : Tau 2 .star :=
  Tau.ty (Ty.Single (Path.var x).fst)

theorem x_context_binding :
    Ctx.Binds Γ x xPublicType.weaken := by
  exact Ctx.Binds.here

theorem x_path_typing :
    Path.Ty Γ (Path.var x) (Tau.ty xPublicType.weaken) :=
  Path.Ty.var x_context_binding

/-- Static dependent selection substitutes `x.1` for the pair binder. -/
theorem selected_typing : Path.Ty Γ selected selectedType := by
  exact Path.Ty.sel_r x_path_typing

theorem x_store_binding :
    Store.Binds σ x (Tm.pair y label (Def.val y)) := by
  exact Store.Binds.here

/-- Runtime selection follows the concrete stored pair and returns `y`. -/
theorem selected_reduces_to_y : Path.reduce selected σ y := by
  exact Path.reduce.sel_hit Path.reduce.var x_store_binding

/-! ## The missing static conversion is real -/

theorem y_context_binding :
    Ctx.Binds Γ y yType.weaken.weaken := by
  exact Ctx.Binds.there Ctx.Binds.here

/-- The result variable does not precisely synthesize the dependent singleton
`{x.1}`; it synthesizes the weakened function type stored for `y`. -/
theorem y_not_precisely_typed_at_selectedType :
    ¬ Path.Ty Γ (Path.var y) selectedType := by
  intro hy
  cases hy with
  | var hb =>
      have heq := hb.unique y_context_binding
      cases heq

/-- Projection of the widened public pair synthesizes `Top`. -/
theorem x_fst_typing :
    Path.Ty Γ (Path.var x).fst (Tau.ty Ty.Top) := by
  exact Path.Ty.fst x_path_typing

/-- In particular, singleton symmetry cannot directly prove
`{y} <: {x.1}`: its required premise would say that `x.1` precisely
synthesizes `{y}`, contradicting functionality of precise path typing. -/
theorem singleton_symmetry_premise_impossible :
    ¬ Path.Ty Γ (Path.var x).fst
      (Tau.ty (Ty.Single (Path.var y))) := by
  intro hsingle
  cases x_fst_typing.functional hsingle

/-- Packaged statement of the obstruction: the store is refined, static
selection synthesizes `{x.1}`, runtime selection returns `y`, and neither
exact result typing nor the direct singleton-symmetry premise is available. -/
theorem dependent_lookup_obstruction :
    Store.RefinedTy Γ σ ∧
    Path.Ty Γ selected selectedType ∧
    Path.reduce selected σ y ∧
    (¬ Path.Ty Γ (Path.var y) selectedType) ∧
    (¬ Path.Ty Γ (Path.var x).fst
      (Tau.ty (Ty.Single (Path.var y)))) := by
  exact ⟨store_refined, selected_typing, selected_reduces_to_y,
    y_not_precisely_typed_at_selectedType,
    singleton_symmetry_premise_impossible⟩

/-! ## A narrow semantic invariant for full subtyping non-derivability -/

/-- These are all possible precise path typings in the concrete context.
Stating the classification as an indexed family lets dependent elimination
discard impossible kind/signature cases directly. -/
inductive KnownPathTy : {k : Kind} -> Path 2 -> Tau 2 k -> Prop where
| y : KnownPathTy (Path.var y) (Tau.ty yType.weaken.weaken)
| x : KnownPathTy (Path.var x) (Tau.ty xPublicType.weaken)
| fst : KnownPathTy (Path.var x).fst (Tau.ty Ty.Top)
| sel : KnownPathTy selected selectedType

private theorem path_typing_known_aux
    {Δ : Ctx 2} {k : Kind} {p : Path 2} {d : Tau 2 k}
    (h : Path.Ty Δ p d) : Δ = Γ -> KnownPathTy p d := by
  induction h with
  | var hb =>
      intro hΔ
      cases hΔ
      cases hb with
      | here => exact .x
      | there hb =>
          cases hb with
          | here => exact .y
          | there hb => cases hb
  | fst hp ih =>
      intro hΔ
      cases ih hΔ
      exact .fst
  | sel_r hp ih =>
      intro hΔ
      cases ih hΔ
      exact .sel
  | sel_l hp htail hne ihp ihtail =>
      intro hΔ
      cases ihtail hΔ

theorem path_typing_known
    {k : Kind} {p : Path 2} {d : Tau 2 k}
    (h : Path.Ty Γ p d) : KnownPathTy p d :=
  path_typing_known_aux h rfl

/-- No path in this context synthesizes an interval. -/
theorem no_interval_path_typing
    {p : Path 2} {S T : Ty 2} :
    ¬ Path.Ty Γ p (Tau.intv S T) := by
  intro h
  cases path_typing_known h

/-- No path in this context synthesizes the singleton `{y}`. -/
theorem no_y_singleton_path_typing
    {p : Path 2} :
    ¬ Path.Ty Γ p (Tau.ty (Ty.Single (Path.var y))) := by
  intro h
  cases path_typing_known h

/-- A standard shape abstraction of proper types.  All non-singleton shapes
are marked except `Bot`; a singleton is marked exactly when its path is an
atomic variable. -/
def typeMarked : Ty n -> Prop
| .Top => True
| .Bot => False
| .Fun _ _ => True
| .Pair _ _ _ => True
| .Single p => p.IsVar

/-- Intervals need no distinction for this argument; the interesting case is
proper singleton subtyping. -/
def signatureMarked : Tau n k -> Prop
| .ty T => typeMarked T
| .intv _ _ => True

/-- Context entries respect the shape abstraction. -/
def ContextMarked (Δ : Ctx n) : Prop :=
  ∀ {z T}, Ctx.Binds Δ z T -> typeMarked T

/-- A singleton of an atomic variable can only be synthesized by an atomic
variable path. -/
def NoVariableAliases (Δ : Ctx n) : Prop :=
  ∀ {p q}, Path.Ty Δ p (Tau.ty (Ty.Single q)) -> q.IsVar -> p.IsVar

/-- No abstract interval can be selected in the context. -/
def NoIntervals (Δ : Ctx n) : Prop :=
  ∀ {p S T}, ¬ Path.Ty Δ p (Tau.intv S T)

/-- Every subtyping rule preserves the abstraction under the three narrow
structural assumptions above.  This theorem is fully general in the scope
and context, so induction also covers dependent premises under binders. -/
theorem sub_preserves_mark
    {Δ : Ctx n} {k : Kind} {d1 d2 : Tau n k}
    (hctx : ContextMarked Δ)
    (halias : NoVariableAliases Δ)
    (hintv : NoIntervals Δ)
  (h : Tau.Sub Δ d1 d2) :
    signatureMarked d1 -> signatureMarked d2 := by
  induction h with
  | refl => exact fun hm => hm
  | trans h1 h2 ih1 ih2 =>
      intro hm
      exact ih2 hctx halias hintv (ih1 hctx halias hintv hm)
  | bot => exact fun hm => hm.elim
  | top => exact fun _ => trivial
  | widen hp =>
      intro hm
      cases hm
      cases hp with
      | var hb => exact hctx hb
  | symm hp =>
      intro hm
      exact halias hp hm
  | sel_hi hp hbounds ihbounds =>
      intro hm
      cases hm
  | sel_lo hp hbounds ihbounds => exact (hintv hp).elim
  | «fun» hdom hcod ihdom ihcod => exact fun _ => trivial
  | pair hfst hsnd ihfst ihsnd => exact fun _ => trivial
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty => exact fun _ => trivial

theorem context_marked : ContextMarked Γ := by
  intro z T hb
  cases hb with
  | here => trivial
  | there hb =>
      cases hb with
      | here => trivial
      | there hb => cases hb

theorem no_variable_aliases : NoVariableAliases Γ := by
  intro p q hp hq
  cases path_typing_known hp
  cases hq

theorem no_intervals : NoIntervals Γ := by
  intro p S T
  exact no_interval_path_typing

theorem singleton_y_marked :
    signatureMarked (Tau.ty (Ty.Single (Path.var y))) := .var

theorem selected_type_unmarked : ¬ signatureMarked selectedType := by
  intro h
  cases h

/-- Full non-derivability, including every use of transitivity and abstract
bounds—not merely failure of the direct `symm` constructor. -/
theorem no_result_singleton_subtyping :
    ¬ Tau.Sub Γ
      (Tau.ty (Ty.Single (Path.var y))) selectedType := by
  intro hsub
  exact selected_type_unmarked
    (sub_preserves_mark context_marked no_variable_aliases no_intervals
      hsub singleton_y_marked)

/-! ## Ordinary term typing and machine preservation now fail -/

private theorem term_typing_path_implies_sub_aux
    {Δ : Ctx n} {t : Tm n} {T : Ty n}
    (h : Tm.Ty Δ t T) :
    ∀ {p : Path n}, t = Tm.path p ->
      Tau.Sub Δ (Tau.ty (Ty.Single p)) (Tau.ty T) := by
  induction h with
  | path hp =>
      intro p heq
      cases heq
      exact .refl
  | abs ht hwf ih =>
      intro p heq
      cases heq
  | app hp hq ihp ihq =>
      intro r heq
      cases heq
  | pair hy hz =>
      intro p heq
      cases heq
  | tpair hy hwf =>
      intro p heq
      cases heq
  | «let» hs hwf ht ihs iht =>
      intro p heq
      cases heq
  | typed ht hwf ih =>
      intro p heq
      cases heq
  | sub ht hsub hwf ih =>
      intro p heq
      exact .trans (ih heq) hsub

/-- Any ordinary typing of a path term factors through subtyping from its
principal singleton.  This is independent of the concrete counterexample. -/
theorem term_path_typing_implies_sub
    {Δ : Ctx n} {p : Path n} {T : Ty n}
    (h : Tm.Ty Δ (Tm.path p) T) :
    Tau.Sub Δ (Tau.ty (Ty.Single p)) (Tau.ty T) :=
  term_typing_path_implies_sub_aux h rfl

/-- The runtime result is genuinely not typable at the statically selected
singleton—not merely missing an exact `Path.Ty` derivation. -/
theorem y_untypable_at_selected_singleton :
    ¬ Tm.Ty Γ (Tm.path (Path.var y))
      (Ty.Single (Path.var x).fst) := by
  intro ht
  exact no_result_singleton_subtyping
    (term_path_typing_implies_sub ht)

theorem selected_result_wf : Tau.Wf Γ selectedType := by
  exact Tau.Wf.path x_fst_typing

/-- The source path term is ordinarily typed at `{x.1}` by widening its
principal singleton through the precise selection judgment. -/
theorem selected_term_typing :
    Tm.Ty Γ (Tm.path selected) (Ty.Single (Path.var x).fst) := by
  exact Tm.Ty.sub (Tm.Ty.path selected_typing)
    (Tau.Sub.widen selected_typing) selected_result_wf

abbrev sourceState : State 2 := ⟨σ, [], Tm.path selected⟩

abbrev successorState : State 2 :=
  ⟨σ, [], Tm.path (Path.var y)⟩

theorem source_state_typed :
    State.Ty Γ sourceState (Ty.Single (Path.var x).fst) := by
  exact State.Ty.ok store_typed (Tm.Cont.Ty.hole .refl)
    selected_term_typing

theorem selected_not_var : ¬ selected.IsVar := by
  intro h
  cases h

theorem source_steps_to_successor :
    State.Step sourceState successorState := by
  exact State.Step.path selected_reduces_to_y selected_not_var

/-- Even allowing the empty continuation to choose an intermediate input
type cannot type the successor: its two subtype legs would compose to the
forbidden singleton subtyping judgment. -/
theorem successor_state_untypable :
    ¬ State.Ty Γ successorState (Ty.Single (Path.var x).fst) := by
  intro hs
  cases hs with
  | ok hstore hcont ht =>
      cases hcont with
      | hole hsub =>
          exact no_result_singleton_subtyping
            (Tau.Sub.trans (term_path_typing_implies_sub ht) hsub)

/-- A checked, one-step counterexample to preservation for the literal
historical public judgments and machine. -/
theorem source_preservation_counterexample :
    State.Ty Γ sourceState (Ty.Single (Path.var x).fst) ∧
    State.Step sourceState successorState ∧
    ¬ State.Ty Γ successorState (Ty.Single (Path.var x).fst) := by
  exact ⟨source_state_typed, source_steps_to_successor,
    successor_state_untypable⟩

end LambdaPHistory.LookupCounterexample
