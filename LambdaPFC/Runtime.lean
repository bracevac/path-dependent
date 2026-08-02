import Init
import LambdaPFC.Typing

/-!
The operational semantics of `lambda_p`, stated over the native `LambdaPFC`
syntax.  Stores and machine configurations carry their exact scope, so the
allocation transition is heterogeneous: it moves from scope `n` to scope
`n + 1`.

`Path.reduce` is the evaluator used by the term machine and returns a value
location.  `Path.Resolve` is its proof-level generalization to paths ending in
stored type definitions.  The value fragment of `Resolve` agrees exactly with
`reduce`.
-/

namespace LambdaPFC

/-! ## Stores -/

/-- An immutable store of values, indexed by its exact scope. -/
inductive Store : Nat -> Type where
| empty : Store 0
| val : Store n -> (v : Tm n) -> v.IsValue -> Store (n + 1)

/-- Lookup in an intrinsically scoped store. -/
inductive Store.Binds : Store n -> Fin n -> Tm n -> Prop where
| here : Binds (.val sigma v vv) 0 v.weaken
| there :
    Binds sigma x v ->
    Binds (.val sigma u uv) x.succ v.weaken

/-- Executable store lookup. -/
def Store.lookup? : (sigma : Store n) -> Fin n -> Option (Tm n)
| .empty, x => Fin.elim0 x
| .val sigma v _, x =>
    Fin.cases (some v.weaken)
      (fun y => (sigma.lookup? y).map Tm.weaken) x

/-- Every store binding denotes a value. -/
theorem Store.Binds.isValue (h : Store.Binds sigma x v) : v.IsValue := by
  induction h with
  | here => exact Tm.IsValue.weaken (by assumption)
  | there _ ih => exact ih.weaken

/-- Inductive lookup agrees with executable lookup. -/
theorem Store.Binds.lookup_eq (h : Store.Binds sigma x v) :
    sigma.lookup? x = some v := by
  induction h with
  | here => rfl
  | there _ ih =>
      simpa [Store.lookup?] using congrArg (Option.map Tm.weaken) ih

/-- A location has at most one stored value. -/
theorem Store.Binds.unique
    (h1 : Store.Binds sigma x v1) (h2 : Store.Binds sigma x v2) :
    v1 = v2 := by
  apply Option.some.inj
  exact h1.lookup_eq.symm.trans h2.lookup_eq

/-! ## Term-path reduction -/

/-- Resolve a term-denoting path to an atomic store location. -/
inductive Path.reduce : Path n -> Store n -> Fin n -> Prop where
| var : Path.reduce (.var x) sigma x
| fst :
    Path.reduce p sigma x ->
    Store.Binds sigma x (.pair y a d) ->
    Path.reduce p.fst sigma y
| sel_hit :
    Path.reduce p sigma x ->
    Store.Binds sigma x (.pair y a (.val z)) ->
    Path.reduce (p.sel a) sigma z
| sel_miss :
    Path.reduce p sigma x ->
    Store.Binds sigma x (.pair y b d) ->
    Not (a = b) ->
    Path.reduce ((Path.var y).sel a) sigma z ->
    Path.reduce (p.sel a) sigma z

/-- Term-path reduction is deterministic. -/
theorem Path.reduce.deterministic
    (h1 : Path.reduce p sigma x1) (h2 : Path.reduce p sigma x2) :
    x1 = x2 := by
  induction h1 generalizing x2 with
  | var =>
      cases h2
      rfl
  | fst hp1 hb1 ih =>
      cases h2 with
      | fst hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
  | sel_hit hp1 hb1 ih =>
      cases h2 with
      | sel_hit hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_miss hp1 hb1 hne1 _ ihp ihtail =>
      cases h2 with
      | sel_hit hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_miss hp2 hb2 _ htail2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact ihtail htail2

/-- Selection depends only on the location reached by its prefix. -/
theorem Path.reduce.sel_congr
    (hs : Path.reduce (p.sel a) sigma z)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma x) :
    Path.reduce (q.sel a) sigma z := by
  cases hs with
  | sel_hit hp' hb =>
      cases hp.deterministic hp'
      exact .sel_hit hq hb
  | sel_miss hp' hb hne htail =>
      cases hp.deterministic hp'
      exact .sel_miss hq hb hne htail

/-- Old path reductions remain valid after allocation. -/
theorem Path.reduce.weaken
    {n : Nat} {p : Path n} {sigma : Store n} {x : Fin n}
    (h : Path.reduce p sigma x) (v : Tm n) (vv : v.IsValue) :
    Path.reduce p.weaken (Store.val sigma v vv) x.succ := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih (.there hb)
  | sel_hit _ hb ih => exact .sel_hit ih (.there hb)
  | sel_miss _ hb hne _ ihp ihtail =>
      exact .sel_miss ihp (.there hb) hne ihtail

/-! ## Generalized path resolution -/

namespace Path

/-- A path ends at either a value location or a stored type definition. -/
inductive Endpoint (n : Nat) : Type where
| val : Fin n -> Endpoint n
| type : LambdaPFC.Ty n -> Endpoint n

/-- Weaken an endpoint when a fresh store cell is allocated. -/
def Endpoint.weaken : Endpoint n -> Endpoint (n + 1)
| .val x => .val x.succ
| .type T => .type T.weaken

end Path

/-- The endpoint stored by a pair definition. -/
def Def.endpoint : Def n k -> Path.Endpoint n
| .val x => .val x
| .type T => .type T

/-- Follow a path to a value location or a stored type definition. -/
inductive Path.Resolve : Path n -> Store n -> Path.Endpoint n -> Prop where
| var : Path.Resolve (.var x) sigma (.val x)
| fst :
    Path.Resolve p sigma (.val x) ->
    Store.Binds sigma x (.pair y a d) ->
    Path.Resolve p.fst sigma (.val y)
| sel_val :
    Path.Resolve p sigma (.val x) ->
    Store.Binds sigma x (.pair y a (.val z)) ->
    Path.Resolve (p.sel a) sigma (.val z)
| sel_type :
    Path.Resolve p sigma (.val x) ->
    Store.Binds sigma x (.pair y a (.type U)) ->
    Path.Resolve (p.sel a) sigma (.type U)
| sel_miss :
    Path.Resolve p sigma (.val x) ->
    Store.Binds sigma x (.pair y b d) ->
    Not (a = b) ->
    Path.Resolve ((Path.var y).sel a) sigma e ->
    Path.Resolve (p.sel a) sigma e

/-- Generalized path resolution is deterministic. -/
theorem Path.Resolve.deterministic
    (h1 : Path.Resolve p sigma e1) (h2 : Path.Resolve p sigma e2) :
    e1 = e2 := by
  induction h1 generalizing e2 with
  | var =>
      cases h2
      rfl
  | fst hp1 hb1 ih =>
      cases h2 with
      | fst hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
  | sel_val hp1 hb1 ih =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_type hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_type hp1 hb1 ih =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
      | sel_type hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_miss hp1 hb1 hne1 htail1 ihp ihtail =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_type hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_miss hp2 hb2 _ htail2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact ihtail htail2

/-- Every term-path reduction is a value-endpoint resolution. -/
theorem Path.reduce.toResolve (h : Path.reduce p sigma x) :
    Path.Resolve p sigma (.val x) := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih hb
  | sel_hit _ hb ih => exact .sel_val ih hb
  | sel_miss _ hb hne _ ihp ihtail =>
      exact .sel_miss ihp hb hne ihtail

private theorem Path.Resolve.toReduce_of_eq (h : Path.Resolve p sigma e) :
    forall x, e = .val x -> Path.reduce p sigma x := by
  induction h with
  | var =>
      intro x he
      cases he
      exact .var
  | fst hp hb ih =>
      intro x he
      cases he
      exact .fst (ih _ rfl) hb
  | sel_val hp hb ih =>
      intro x he
      cases he
      exact .sel_hit (ih _ rfl) hb
  | sel_type hp hb ih =>
      intro x he
      cases he
  | sel_miss hp hb hne htail ihp ihtail =>
      intro x he
      exact .sel_miss (ihp _ rfl) hb hne (ihtail _ he)

/-- A value-endpoint resolution is a term-path reduction. -/
theorem Path.Resolve.toReduce (h : Path.Resolve p sigma (.val x)) :
    Path.reduce p sigma x :=
  h.toReduce_of_eq x rfl

/-- The value fragment of generalized resolution is exactly term reduction. -/
theorem Path.resolve_val_iff_reduce :
    Path.Resolve p sigma (.val x) <-> Path.reduce p sigma x :=
  .intro Path.Resolve.toReduce Path.reduce.toResolve

/-- Generalized selection depends only on the value endpoint of its prefix. -/
theorem Path.Resolve.sel_congr
    (hs : Path.Resolve (p.sel a) sigma e)
    (hp : Path.Resolve p sigma (.val x))
    (hq : Path.Resolve q sigma (.val x)) :
    Path.Resolve (q.sel a) sigma e := by
  cases hs with
  | sel_val hp' hb =>
      cases hp.deterministic hp'
      exact .sel_val hq hb
  | sel_type hp' hb =>
      cases hp.deterministic hp'
      exact .sel_type hq hb
  | sel_miss hp' hb hne htail =>
      cases hp.deterministic hp'
      exact .sel_miss hq hb hne htail

/-- Generalized resolution remains valid after allocation. -/
theorem Path.Resolve.weaken
    {n : Nat} {p : Path n} {sigma : Store n} {e : Path.Endpoint n}
    (h : Path.Resolve p sigma e) (v : Tm n) (vv : v.IsValue) :
    Path.Resolve p.weaken (Store.val sigma v vv) e.weaken := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih (.there hb)
  | sel_val _ hb ih => exact .sel_val ih (.there hb)
  | sel_type _ hb ih => exact .sel_type ih (.there hb)
  | sel_miss _ hb hne _ ihp ihtail =>
      exact .sel_miss ihp (.there hb) hne ihtail

/-! ## Continuations and configurations -/

/-- A let frame waiting for its bound computation. -/
inductive Tm.Frame : Nat -> Type where
| let : Tm (n + 1) -> Tm.Frame n

/-- A CK continuation. -/
abbrev Tm.Cont (n : Nat) : Type := List (Tm.Frame n)

def Tm.Frame.rename (F : Tm.Frame n) (f : FinFun n m) : Tm.Frame m :=
  match F with
  | .let t => .let (t.rename f.ext)

def Tm.Cont.rename (k : Tm.Cont n) (f : FinFun n m) : Tm.Cont m :=
  k.map (fun F => F.rename f)

def Tm.Frame.weaken (F : Tm.Frame n) : Tm.Frame (n + 1) :=
  F.rename FinFun.weaken

def Tm.Cont.weaken (k : Tm.Cont n) : Tm.Cont (n + 1) :=
  k.rename FinFun.weaken

/-- A machine configuration at store scope `n`. -/
structure State (n : Nat) where
  store : Store n
  cont : Tm.Cont n
  term : Tm n

/-- Final states have an empty continuation and contain a live location or a
syntactic value. -/
inductive State.IsFinal : State n -> Prop where
| location :
    Store.Binds sigma x v ->
    State.IsFinal (State.mk sigma [] (.path (.var x)))
| value :
    v.IsValue ->
    State.IsFinal (State.mk sigma [] v)

/-- The initial machine configuration for a closed term. -/
def State.initial (t : Tm 0) : State 0 :=
  State.mk Store.empty [] t

/-! ## CK transitions -/

/-- One transition of the indexed CK machine. -/
inductive State.Step : State n -> State m -> Prop where
| app :
    Path.reduce p sigma f ->
    Path.reduce q sigma y ->
    Store.Binds sigma f (.abs A body) ->
    State.Step
      (State.mk sigma k (.app p q))
      (State.mk sigma k (body.open y))
| path :
    Path.reduce p sigma x ->
    Not p.IsVar ->
    State.Step
      (State.mk sigma k (.path p))
      (State.mk sigma k (.path (.var x)))
| let_push :
    State.Step
      (State.mk sigma k (.let s body))
      (State.mk sigma (.let body :: k) s)
| return :
    State.Step
      (State.mk sigma (.let body :: k) (.path (.var x)))
      (State.mk sigma k (body.open x))
| allocate :
    (vv : v.IsValue) ->
    State.Step
      (State.mk sigma (.let body :: k) v)
      (State.mk (Store.val sigma v vv) (Tm.Cont.weaken k) body)
| ascribe :
    State.Step
      (State.mk sigma k (.typed t T))
      (State.mk sigma k t)

/-- Reflexive-transitive closure across allocation-induced scope changes. -/
inductive State.Steps : State n -> State m -> Prop where
| refl : State.Steps source source
| tail :
    State.Step source middle ->
    State.Steps middle target ->
    State.Steps source target

/-- Finite executions compose. -/
theorem State.Steps.trans
    (h1 : State.Steps source middle)
    (h2 : State.Steps middle target) :
    State.Steps source target := by
  induction h1 with
  | refl => exact h2
  | tail hstep hrest ih => exact .tail hstep (ih h2)

/-- A state either is final or can take a machine step. -/
inductive State.Progress (s : State n) : Prop where
| final : s.IsFinal -> State.Progress s
| step : State.Step s target -> State.Progress s

theorem State.Progress.path_var
    (hbind : Store.Binds sigma x v) :
    State.Progress (State.mk sigma k (.path (.var x))) := by
  cases k with
  | nil => exact .final (.location hbind)
  | cons F k =>
      cases F
      exact .step .return

theorem State.Progress.value
    (vv : v.IsValue) : State.Progress (State.mk sigma k v) := by
  cases k with
  | nil => exact .final (.value vv)
  | cons F k =>
      cases F
      exact .step (.allocate vv)

theorem State.Progress.path
    (hr : Path.reduce p sigma x) (hvar : Not p.IsVar) :
    State.Progress (State.mk sigma k (.path p)) :=
  .step (.path hr hvar)

theorem State.Progress.app
    (hp : Path.reduce p sigma f)
    (hq : Path.reduce q sigma y)
    (hfun : Store.Binds sigma f (.abs A body)) :
    State.Progress (State.mk sigma k (.app p q)) :=
  .step (.app hp hq hfun)

theorem State.Progress.let_term :
    State.Progress (State.mk sigma k (.let s body)) :=
  .step .let_push

theorem State.Progress.ascribed :
    State.Progress (State.mk sigma k (.typed t T)) :=
  .step .ascribe

end LambdaPFC
