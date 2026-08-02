import LambdaP.Original.StructuralValueInversion

/-!
`Store.StructTy.RuntimePathValid` does not follow from `Store.StructTy`.

The counterexample below stores a concrete pair behind the public type
`Top`.  Its first projection reduces to an older location, so raw runtime
equality identifies the projection with that location.  Structural checking,
correctly, cannot eliminate the public `Top` as a pair.

The proof is deliberately semantic rather than an inversion over the last
checking rule.  In a context containing only `Top`, mutual induction over
structural path checking and subtyping shows that every checkable path is an
atomic variable and every checkable generalized type is either `Top` or a
singleton.  This covers conversion, transitivity, promotion, and abstract
bounds without an unproved syntactic inversion principle.
-/

namespace LambdaP.Original

/-! ## A small shape model for all-`Top` contexts -/

/-- The only generalized-type shapes reachable when every context entry is
`Top`.  The path inside a singleton is intentionally ignored. -/
def Tau.TopOrSingleton : Tau n k -> Prop
| .ty .Top => True
| .ty (.Single _) => True
| _ => False

/-- Every binding in the context has public type `Top`. -/
def Ctx.OnlyTop (Gamma : Ctx n) : Prop :=
  forall {x : Fin n} {T : Ty n}, Ctx.Binds Gamma x T -> T = Ty.Top

/-- Structural conversion preserves the outer generalized-type shape. -/
theorem Tau.StructConv.topOrSingleton_iff
    (h : Tau.StructConv R d1 d2) :
    Tau.TopOrSingleton d1 <-> Tau.TopOrSingleton d2 := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | replace template hpq =>
      cases template with
      | ty T =>
          cases T <;> rfl
      | intv S T => rfl

private abbrev CheckOnlyTopMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Gamma R p d) : Prop :=
  Ctx.OnlyTop Gamma -> p.IsVar /\ Tau.TopOrSingleton d

private abbrev SubOnlyTopMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop :=
  Ctx.OnlyTop Gamma ->
    Tau.TopOrSingleton d1 -> Tau.TopOrSingleton d2

/-- In an all-`Top` context structural checking cannot manufacture an
elimination: every checkable path is an atomic variable.  Simultaneously,
its result is either `Top` or a singleton. -/
theorem Path.StructCheck.onlyTop
    (h : Path.StructCheck Gamma R p d) (hGamma : Ctx.OnlyTop Gamma) :
    p.IsVar /\ Tau.TopOrSingleton d := by
  induction h using Path.StructCheck.rec
      (motive_2 := SubOnlyTopMotive) with
  | var hb =>
      cases hGamma hb
      exact ⟨.var, trivial⟩
  | sub hp hs ihp ihs =>
      obtain ⟨hpvar, hpShape⟩ := ihp hGamma
      exact ⟨hpvar, ihs hGamma hpShape⟩
  | promote hp hs ihp ihs =>
      exact ⟨(ihp hGamma).1, ihs hGamma trivial⟩
  | fst hp ih =>
      exact (ih hGamma).2.elim
  | sel_r hp ih =>
      exact (ih hGamma).2.elim
  | sel_l hp htail hne ihp ihtail =>
      exact (ihp hGamma).2.elim
  | refl =>
      exact fun _ hd => hd
  | trans h1 h2 ih1 ih2 =>
      exact fun hctx hd => ih2 hctx (ih1 hctx hd)
  | conv hconv =>
      exact fun _ hd => hconv.topOrSingleton_iff.mp hd
  | bot =>
      exact fun _ hd => hd.elim
  | top =>
      exact fun _ _ => trivial
  | widen hp ih =>
      exact fun hctx _ => (ih hctx).2
  | symm hp ih =>
      exact fun _ _ => trivial
  | sel_hi hp hbounds ihp ihbounds =>
      exact fun hctx _ => (ihp hctx).2.elim
  | sel_lo hp hbounds ihp ihbounds =>
      exact fun _ _ => trivial
  | «fun» hdom hcod ihdom ihcod =>
      exact fun _ hd => hd.elim
  | pair hfst hsnd ihfst ihsnd =>
      exact fun _ hd => hd.elim
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      exact fun _ hd => hd.elim

/-! ## Two cells: an opaque pair whose projection still reduces

Two cells are minimal: a pair value contains a `Fin n` first component, so it
cannot be the first allocation from the empty (`n = 0`) store.
-/

namespace StructuralRuntimePathValidity.Counterexample

abbrev label : Name := 0

abbrev yIntroType : Ty 0 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

abbrev yValue : Tm 0 :=
  Tm.abs Ty.Top (Tm.path (Path.var 0))

theorem y_value : yValue.IsValue := by
  exact .abs

theorem y_intro_typing : Tm.Ty Ctx.nil yValue yIntroType := by
  exact Tm.Ty.abs
    (Tm.Ty.path (Path.Ty.var Ctx.Binds.here)) Tau.Wf.top

/-- The first value is itself hidden behind `Top`; this makes the final
context uniformly `Top` and keeps the non-derivability proof small. -/
theorem y_top_typing : Tm.Ty Ctx.nil yValue Ty.Top := by
  exact Tm.Ty.sub y_intro_typing Tau.Sub.top Tau.Wf.top

abbrev GammaY : Ctx 1 := Ctx.nil.snoc Ty.Top

abbrev sigmaY : Store 1 :=
  Store.val (Store.empty : Store 0) yValue y_value

theorem sigmaY_structTy : Store.StructTy GammaY sigmaY := by
  exact Store.StructTy.val .empty
    (Tm.StructCheck.of_source y_top_typing _) y_value

abbrev y1 : Fin 1 := 0

abbrev xValue : Tm 1 :=
  Tm.pair y1 label (Def.val y1)

theorem x_value : xValue.IsValue := by
  exact .pair

theorem x_precise_typing :
    Tm.Ty GammaY xValue
      (Ty.Pair (Ty.Single (Path.var y1)) label
        (Tau.ty (Ty.Single (Path.var y1).weaken))) := by
  exact Tm.Ty.pair Ctx.Binds.here Ctx.Binds.here

theorem x_top_typing : Tm.Ty GammaY xValue Ty.Top := by
  exact Tm.Ty.sub x_precise_typing Tau.Sub.top Tau.Wf.top

abbrev Gamma : Ctx 2 := GammaY.snoc Ty.Top

abbrev sigma : Store 2 := Store.val sigmaY xValue x_value

theorem store_structTy : Store.StructTy Gamma sigma := by
  exact Store.StructTy.val sigmaY_structTy
    (Tm.StructCheck.of_source x_top_typing _) x_value

abbrev x : Fin 2 := 0
abbrev y : Fin 2 := 1

abbrev projection : Path 2 := (Path.var x).fst

theorem context_onlyTop : Ctx.OnlyTop Gamma := by
  intro z T hb
  cases hb with
  | here => rfl
  | there hb =>
      cases hb with
      | here => rfl
      | there hb => cases hb

theorem y_context_binding : Ctx.Binds Gamma y Ty.Top := by
  exact Ctx.Binds.there Ctx.Binds.here

theorem y_structCheck :
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var y) (Tau.ty Ty.Top) := by
  exact .var y_context_binding

theorem x_store_binding :
    Store.Binds sigma x (Tm.pair y label (Def.val y)) := by
  exact Store.Binds.here

theorem projection_reduces_to_y : Path.reduce projection sigma y := by
  exact Path.reduce.fst Path.reduce.var x_store_binding

theorem y_runtimeEq_projection :
    Path.RuntimeEq sigma (Path.var y) projection := by
  exact Path.RuntimeEq.coresolve Path.reduce.var projection_reduces_to_y

theorem projection_not_structCheck :
    forall {k : Kind} {d : Tau 2 k},
      ¬ Path.StructCheck Gamma (Path.RuntimeEq sigma) projection d := by
  intro k d h
  cases (h.onlyTop context_onlyTop).1

/-- A fully checked counterexample to the proposed consequence. -/
theorem runtimePathValid_counterexample :
    Store.StructTy Gamma sigma /\
      ¬ Store.StructTy.RuntimePathValid Gamma sigma := by
  refine ⟨store_structTy, ?_⟩
  intro hvalid
  have hprojection :=
    (hvalid y_runtimeEq_projection).mp y_structCheck
  exact projection_not_structCheck hprojection

end StructuralRuntimePathValidity.Counterexample

/-! ## What must be strengthened -/

/-- The operational core of the missing invariant: if a path resolves to a
location, its public structural checks must be exactly those of the result
variable.  `Path.StructCheck.reduce_to_var` proves the forward implication
for proper types; the counterexample refutes the reverse implication even at
`Top`.

Unlike raw `RuntimePathValid`, this formulation identifies the allocation
obligation precisely: every newly stored value must expose enough of its
introduction shape in its public type to type all concrete eliminations. -/
def Store.StructTy.CheckedReductionComplete
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {k : Kind} {p : Path n} {x : Fin n} {d : Tau n k},
    Path.reduce p sigma x ->
    (Path.StructCheck Gamma (Path.RuntimeEq sigma) p d <->
      Path.StructCheck Gamma (Path.RuntimeEq sigma) (Path.var x) d)

/-- The counterexample already violates the reverse direction of checked
reduction: the result variable checks at `Top`, but its reducing projection
does not. -/
theorem StructuralRuntimePathValidity.Counterexample.not_checkedReductionComplete :
    ¬ Store.StructTy.CheckedReductionComplete
      StructuralRuntimePathValidity.Counterexample.Gamma
      StructuralRuntimePathValidity.Counterexample.sigma := by
  intro hcomplete
  have hprojection :=
    (hcomplete
      StructuralRuntimePathValidity.Counterexample.projection_reduces_to_y).mpr
        StructuralRuntimePathValidity.Counterexample.y_structCheck
  exact StructuralRuntimePathValidity.Counterexample.projection_not_structCheck
    hprojection

/-- Full runtime-path validity entails checked reduction completeness.  The
converse is not asserted: `RuntimeEq` also contains contextual congruence,
not only co-resolution. -/
theorem Store.StructTy.RuntimePathValid.checkedReductionComplete
    (h : Store.StructTy.RuntimePathValid Gamma sigma) :
    Store.StructTy.CheckedReductionComplete Gamma sigma := by
  intro k p x d hr
  exact h (Path.RuntimeEq.of_reduce hr)

/-- There is no intrinsically scoped closed path. -/
private theorem Path.noClosed (p : Path 0) : False := by
  induction p with
  | var x => exact Fin.elim0 x
  | fst p ih => exact ih
  | sel p a ih => exact ih

private theorem Store.empty_runtimePathValid :
    Store.StructTy.RuntimePathValid Ctx.nil (Store.empty : Store 0) := by
  intro k p q d hpq
  exact (Path.noClosed p).elim

/-- The exact allocation-stable strengthening required if conversion keeps
using *raw* `Path.RuntimeEq`.  In addition to checking the newly allocated
value, each allocation must re-establish full checking validity for the
extended runtime relation.  Thus every prefix of the store carries the
property used by structural conversion.

This rules out precisely the opaque allocation above.  An alternative repair
is to leave opaque allocations legal and replace raw runtime equality in
`Tau.StructConv.replace` by a typed relation carrying the same checking
equivalence.  No invariant which still accepts this opaque allocation can
make its projection through `Top` typing-valid. -/
inductive Store.RuntimeValidStructTy : {n : Nat} -> Ctx n -> Store n -> Prop
where
| empty : Store.RuntimeValidStructTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.RuntimeValidStructTy Gamma sigma ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ->
    (vv : v.IsValue) ->
    Store.StructTy.RuntimePathValid
      (Gamma.snoc T) (Store.val sigma v vv) ->
    Store.RuntimeValidStructTy (Gamma.snoc T) (Store.val sigma v vv)

theorem Store.RuntimeValidStructTy.toStructTy
    (h : Store.RuntimeValidStructTy Gamma sigma) :
    Store.StructTy Gamma sigma := by
  induction h with
  | empty => exact .empty
  | val hstore hcheck vv hvalid ih => exact .val ih hcheck vv

theorem Store.RuntimeValidStructTy.runtimePathValid
    (h : Store.RuntimeValidStructTy Gamma sigma) :
    Store.StructTy.RuntimePathValid Gamma sigma := by
  cases h with
  | empty => exact Store.empty_runtimePathValid
  | val hstore hcheck vv hvalid => exact hvalid

end LambdaP.Original
