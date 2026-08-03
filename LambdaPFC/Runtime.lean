import Init
import LambdaPFC.Typing

/-!
The operational semantics of `lambda_p`, stated over the native `LambdaPFC`
syntax.  Stores and machine configurations carry their exact scope, so the
allocation transition is heterogeneous: it moves from scope `n` to scope
`n + 1`.

`Path.Resolve` follows a path to either a location or a stored type
definition.  The term machine uses the location case directly.
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

/-- The value stored at a location. -/
def Store.lookup : (sigma : Store n) -> Fin n -> Tm n
| .empty, x => Fin.elim0 x
| .val sigma v _, x =>
    Fin.cases v.weaken (fun y => (sigma.lookup y).weaken) x

/-- Relational lookup agrees with functional lookup. -/
theorem Store.Binds.lookup_eq (h : Store.Binds sigma x v) :
    sigma.lookup x = v := by
  induction h with
  | here => rfl
  | there _ ih => simpa [Store.lookup] using congrArg Tm.weaken ih

theorem Store.Binds.unique
    (h1 : Store.Binds sigma x v1) (h2 : Store.Binds sigma x v2) :
    v1 = v2 :=
  h1.lookup_eq.symm.trans h2.lookup_eq

/-! ## Generalized path resolution -/

namespace Path

/-- The runtime object denoted by a path: a location or a stored type. -/
inductive Referent (n : Nat) : Type where
| loc : Fin n -> Referent n
| type : LambdaPFC.Ty n -> Referent n

/-- Weaken a referent when a fresh store cell is allocated. -/
def Referent.weaken : Referent n -> Referent (n + 1)
| .loc x => .loc x.succ
| .type T => .type T.weaken

end Path

/-- The referent stored by a pair definition. -/
def Def.referent : Def n k -> Path.Referent n
| .val x => .loc x
| .type T => .type T

@[simp] theorem Def.referent_weaken (d : Def n k) :
    (d.rename FinFun.weaken).referent = d.referent.weaken := by
  cases d <;> rfl

/-- Follow a path to a location or a stored type definition. -/
inductive Path.Resolve : Path n -> Store n -> Path.Referent n -> Prop where
| var : Path.Resolve (.var x) sigma (.loc x)
| fst :
    Path.Resolve p sigma (.loc x) ->
    Store.Binds sigma x (.pair y a d) ->
    Path.Resolve p.fst sigma (.loc y)
| sel :
    Path.Resolve p sigma (.loc x) ->
    Store.Binds sigma x (.pair y a d) ->
    Path.Resolve (p.sel a) sigma d.referent
| sel_miss :
    Path.Resolve p sigma (.loc x) ->
    Store.Binds sigma x (.pair y b d) ->
    Not (a = b) ->
    Path.Resolve ((Path.var y).sel a) sigma referent ->
    Path.Resolve (p.sel a) sigma referent

/-- Generalized path resolution is deterministic. -/
theorem Path.Resolve.deterministic
    (h1 : Path.Resolve p sigma referent1)
    (h2 : Path.Resolve p sigma referent2) :
    referent1 = referent2 := by
  induction h1 generalizing referent2 with
  | var =>
      cases h2
      rfl
  | fst hp1 hb1 ih =>
      cases h2 with
      | fst hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
  | sel hp1 hb1 ih =>
      cases h2 with
      | sel hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_miss hp1 hb1 hne1 htail1 ihp ihtail =>
      cases h2 with
      | sel hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_miss hp2 hb2 _ htail2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact ihtail htail2

/-- Generalized selection depends only on the location referent of its prefix. -/
theorem Path.Resolve.sel_congr
    (hs : Path.Resolve (p.sel a) sigma referent)
    (hp : Path.Resolve p sigma (.loc x))
    (hq : Path.Resolve q sigma (.loc x)) :
    Path.Resolve (q.sel a) sigma referent := by
  cases hs with
  | sel hp' hb =>
      cases hp.deterministic hp'
      exact .sel hq hb
  | sel_miss hp' hb hne htail =>
      cases hp.deterministic hp'
      exact .sel_miss hq hb hne htail

/-- Generalized resolution remains valid after allocation. -/
theorem Path.Resolve.weaken
    {n : Nat} {p : Path n} {sigma : Store n}
    {referent : Path.Referent n}
    (h : Path.Resolve p sigma referent) (v : Tm n) (vv : v.IsValue) :
    Path.Resolve p.weaken (Store.val sigma v vv) referent.weaken := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih (.there hb)
  | sel _ hb ih =>
      simpa [Path.weaken] using Path.Resolve.sel ih (.there hb)
  | sel_miss _ hb hne _ ihp ihtail =>
      exact .sel_miss ihp (.there hb) hne ihtail

/-! ## Continuations and configurations -/

/-- A CK continuation is a stack of suspended let bodies. -/
abbrev Tm.Cont (n : Nat) : Type := List (Tm (n + 1))

def Tm.Cont.rename (k : Tm.Cont n) (f : FinFun n m) : Tm.Cont m :=
  k.map (fun body => body.rename f.ext)

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
| location : State.IsFinal (State.mk sigma [] (.path (.var x)))
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
    Path.Resolve p sigma (.loc f) ->
    Path.Resolve q sigma (.loc y) ->
    Store.Binds sigma f (.abs A body) ->
    State.Step
      (State.mk sigma k (.app p q))
      (State.mk sigma k (body.open y))
| path :
    Path.Resolve p sigma (.loc x) ->
    Not p.IsVar ->
    State.Step
      (State.mk sigma k (.path p))
      (State.mk sigma k (.path (.var x)))
| let_push :
    State.Step
      (State.mk sigma k (.let s body))
      (State.mk sigma (body :: k) s)
| return :
    State.Step
      (State.mk sigma (body :: k) (.path (.var x)))
      (State.mk sigma k (body.open x))
| allocate :
    (vv : v.IsValue) ->
    State.Step
      (State.mk sigma (body :: k) v)
      (State.mk (Store.val sigma v vv) (Tm.Cont.weaken k) body)

/-- Reflexive-transitive closure across allocation-induced scope changes. -/
inductive State.Steps : State n -> State m -> Prop where
| refl : State.Steps source source
| tail :
    State.Step source middle ->
    State.Steps middle target ->
    State.Steps source target

/-- A state either is final or can take a machine step. -/
inductive State.Progress (s : State n) : Prop where
| final : s.IsFinal -> State.Progress s
| step : State.Step s target -> State.Progress s

theorem State.Progress.path_var :
    State.Progress (State.mk sigma k (.path (.var x))) := by
  cases k with
  | nil => exact .final .location
  | cons body k => exact .step .return

theorem State.Progress.value
    (vv : v.IsValue) : State.Progress (State.mk sigma k v) := by
  cases k with
  | nil => exact .final (.value vv)
  | cons body k => exact .step (.allocate vv)

theorem State.Progress.path
    (hr : Path.Resolve p sigma (.loc x)) (hvar : Not p.IsVar) :
    State.Progress (State.mk sigma k (.path p)) :=
  .step (.path hr hvar)

theorem State.Progress.app
    (hp : Path.Resolve p sigma (.loc f))
    (hq : Path.Resolve q sigma (.loc y))
    (hfun : Store.Binds sigma f (.abs A body)) :
    State.Progress (State.mk sigma k (.app p q)) :=
  .step (.app hp hq hfun)

theorem State.Progress.let_term :
    State.Progress (State.mk sigma k (.let s body)) :=
  .step .let_push

end LambdaPFC
