import LambdaPHistory.Machine
import LambdaPHistory.DeepPathPreservation
import LambdaPHistory.DeepRenaming
import LambdaPHistory.ScopedRuntimeEq

/-!
A runtime-aware invariant for stores, continuations, and machine states.

The concrete term currently being evaluated is checked with equations from the
current store.  A suspended `let` body is different: its newest variable is a
formal binder, not an allocated location, so its conversion relation is the
binder-safe `Path.ScopedRuntimeEq`.

This file establishes source embedding and the complete big-step path machine
case.  Opening a suspended body and opening a function body are intentionally
left to the structural substitution theorem; no exact-source renaming is
smuggled into this invariant.
-/

namespace LambdaPHistory

/-! ## Deeply typed stores -/

/-- Store typing which retains the runtime-aware checker available when each
cell is allocated. -/
inductive Store.DeepTy : {n : Nat} -> Ctx n -> Store n -> Prop where
| empty : Store.DeepTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.DeepTy Gamma sigma ->
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma) v T ->
    (vv : v.IsValue) ->
    Store.DeepTy (Gamma.snoc T) (Store.val sigma v vv)

/-- Historical store typing embeds in the runtime-aware invariant. -/
theorem Store.Ty.toDeep (h : Store.Ty Gamma sigma) :
    Store.DeepTy Gamma sigma := by
  induction h with
  | empty => exact .empty
  | val hstore ht ih =>
      exact .val ih (Tm.DeepCheck.of_source ht _) (by assumption)

/-! ## Deeply typed continuations -/

/-- A suspended frame checks its body under the formal lift used by the deep
checker.  The concrete store has not yet been extended. -/
inductive Tm.Frame.DeepTy (Gamma : Ctx n) (sigma : Store n) :
    LambdaPHistory.Ty n -> Tm.Frame n ->
      LambdaPHistory.Ty n -> Prop where
| «let» :
    Tm.DeepCheck (Gamma.snoc S) (Path.ConvLift (Path.RuntimeEq sigma))
      t T.weaken ->
    Tm.Frame.DeepTy Gamma sigma S (Tm.Frame.let t) T

/-- Runtime-aware continuation typing. -/
inductive Tm.Cont.DeepTy (Gamma : Ctx n) (sigma : Store n) :
    LambdaPHistory.Ty n -> Tm.Cont n ->
      LambdaPHistory.Ty n -> Prop where
| hole :
    Tau.DeepSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty T) ->
    Tm.Cont.DeepTy Gamma sigma S [] T
| cons :
    Tm.Cont.DeepTy Gamma sigma S E T ->
    Tm.Frame.DeepTy Gamma sigma U F S ->
    Tm.Cont.DeepTy Gamma sigma U (F :: E) T

theorem Tm.Frame.Ty.toDeep
    {n : Nat} {Gamma : Ctx n} {S T : LambdaPHistory.Ty n}
    {F : Tm.Frame n}
    (h : Tm.Frame.Ty Gamma S F T) (sigma : Store n) :
    Tm.Frame.DeepTy Gamma sigma S F T := by
  cases h with
  | «let» ht =>
      exact .let (Tm.DeepCheck.of_source ht _)

theorem Tm.Cont.Ty.toDeep
    {n : Nat} {Gamma : Ctx n} {S T : LambdaPHistory.Ty n}
    {k : Tm.Cont n}
    (h : Tm.Cont.Ty Gamma S k T) (sigma : Store n) :
    Tm.Cont.DeepTy Gamma sigma S k T := by
  induction h with
  | hole hsub => exact .hole (.source hsub)
  | cons hc hf ih => exact .cons ih (hf.toDeep sigma)

/-! ## Deeply typed states -/

/-- Complete runtime-aware state typing. -/
inductive State.DeepTy : Ctx n -> State n ->
    LambdaPHistory.Ty n -> Prop where
| ok :
    Store.DeepTy Gamma sigma ->
    Tm.Cont.DeepTy Gamma sigma S k T ->
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma) t S ->
    State.DeepTy Gamma ⟨sigma, k, t⟩ T

/-- Every historically typed state starts in the stronger proof invariant. -/
theorem State.Ty.toDeep (h : State.Ty Gamma state T) :
    State.DeepTy Gamma state T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .ok hstore.toDeep (hcont.toDeep _) (Tm.DeepCheck.of_source hterm _)

/-- A transition either keeps the current runtime context or allocates one
cell.  This is the deep counterpart of the historical `Preserve` packaging. -/
inductive DeepPreserve : Ctx n -> State m ->
    LambdaPHistory.Ty n -> Prop where
| same : State.DeepTy Gamma state T -> DeepPreserve Gamma state T
| extend :
    State.DeepTy (Gamma.snoc S) state T.weaken ->
    DeepPreserve Gamma state T

/-! ## The original missing path case -/

/-- Big-step replacement of a non-variable path preserves the complete deep
machine invariant. -/
theorem DeepPreserve.path
    (hr : Path.reduce p sigma x)
    (h : State.DeepTy Gamma
      ⟨sigma, k, Tm.path p⟩ T) :
    DeepPreserve Gamma
      ⟨sigma, k, Tm.path (Path.var x)⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont (hterm.reduce_path hr))

/-- Direct packaging for the historical `State.Step.path` constructor. -/
theorem State.Step.deep_path_preservation
    (step : State.Step
      ⟨sigma, k, Tm.path p⟩
      ⟨sigma, k, Tm.path (Path.var x)⟩)
    (h : State.DeepTy Gamma
      ⟨sigma, k, Tm.path p⟩ T) :
    DeepPreserve Gamma
      ⟨sigma, k, Tm.path (Path.var x)⟩ T := by
  cases step with
  | path hr _ => exact DeepPreserve.path hr h

/-! ## Relation maps used by administrative transitions -/

private theorem Renaming.identity (Gamma : Ctx n) :
    Renaming Gamma FinFun.id Gamma := by
  intro x T hx
  simpa only [Ty.rename_id] using hx

/-- Deep checking is monotone in its abstract path relation. -/
theorem Tm.DeepCheck.mono
    {n : Nat} {Gamma : Ctx n} {R R' : Path.ConvRel n}
    {t : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R t T)
    (hmap : forall {p q}, R p q -> R' p q) :
    Tm.DeepCheck Gamma R' t T := by
  have hm : forall {p q}, R p q ->
      R' (p.rename FinFun.id) (q.rename FinFun.id) := by
    intro p q hpq
    simpa only [Path.rename_id] using hmap hpq
  simpa only [Tm.rename_id, Ty.rename_id] using
    h.rename (Renaming.identity Gamma) hm

private theorem Path.RuntimeEq.weaken_into_scoped
    {n : Nat} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) :
    Path.ScopedRuntimeEq sigma p.weaken q.weaken :=
  .old h

/-- Once allocation occurs, the formal scoped relation embeds in the concrete
runtime relation of the extended store. -/
theorem Path.ScopedRuntimeEq.to_extended
    {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue}
    {p q : Path (n + 1)}
    (h : Path.ScopedRuntimeEq sigma p q) :
    Path.RuntimeEq (Store.val sigma v vv) p q := by
  induction h with
  | bound => exact .refl
  | old hpq => exact hpq.weaken v vv
  | symm hpq ih => exact .symm ih
  | trans hpq hqr ih1 ih2 => exact .trans ih1 ih2
  | fst hpq ih => exact (Path.RuntimeEq.isEquivCongr _).fst ih
  | sel hpq ih => exact (Path.RuntimeEq.isEquivCongr _).sel ih _

/-- The smaller formal lift used by `Tm.DeepCheck` embeds in the concrete
runtime relation after the corresponding allocation. -/
theorem Path.ConvLift.to_extended
    {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue}
    {p q : Path (n + 1)}
    (h : Path.ConvLift (Path.RuntimeEq sigma) p q) :
    Path.RuntimeEq (Store.val sigma v vv) p q := by
  cases h with
  | bound => exact .refl
  | weaken hpq => exact hpq.weaken v vv

/-! ## Deep inversion through trailing subsumption -/

private theorem Tm.DeepCheck.typed_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {u : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R u T) :
    forall {t : Tm n} {A : LambdaPHistory.Ty n},
      u = Tm.typed t A ->
      Tm.DeepCheck Gamma R t T /\ Tau.DeepWf Gamma R (Tau.ty T) := by
  induction h with
  | path _ => intro t A heq; cases heq
  | abs _ _ _ => intro t A heq; cases heq
  | app _ _ _ _ => intro t A heq; cases heq
  | pair _ _ => intro t A heq; cases heq
  | tpair _ _ => intro t A heq; cases heq
  | «let» _ _ _ _ _ => intro t A heq; cases heq
  | typed ht hwf ih =>
      intro t A heq
      cases heq
      exact ⟨ht, hwf⟩
  | sub ht hs hwf ih =>
      intro t A heq
      obtain ⟨ht', _⟩ := ih heq
      exact ⟨.sub ht' hs hwf, hwf⟩

theorem Tm.DeepCheck.typed_inv
    (h : Tm.DeepCheck Gamma R (Tm.typed t A) T) :
    Tm.DeepCheck Gamma R t T /\ Tau.DeepWf Gamma R (Tau.ty T) :=
  h.typed_inv_of_eq rfl

private theorem Tm.DeepCheck.let_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {u : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R u T) :
    forall {s : Tm n} {t : Tm (n + 1)}, u = Tm.let s t ->
      exists S,
        Tm.DeepCheck Gamma R s S /\
        Tau.DeepWf Gamma R (Tau.ty T) /\
        Tm.DeepCheck (Gamma.snoc S) (Path.ConvLift R) t T.weaken := by
  induction h with
  | path _ => intro s t heq; cases heq
  | abs _ _ _ => intro s t heq; cases heq
  | app _ _ _ _ => intro s t heq; cases heq
  | pair _ _ => intro s t heq; cases heq
  | tpair _ _ => intro s t heq; cases heq
  | «let» hs hwf ht ihs iht =>
      intro s t heq
      cases heq
      exact ⟨_, hs, hwf, ht⟩
  | typed _ _ _ => intro s t heq; cases heq
  | sub ht hs hwf ih =>
      intro s t heq
      obtain ⟨S, hscrut, _, hbody⟩ := ih heq
      have hs' := hs.rename (Renaming.weaken (S := S))
        (fun hpq => Path.ConvLift.weaken hpq)
      have hwf' := hwf.rename (Renaming.weaken (S := S))
        (fun hpq => Path.ConvLift.weaken hpq)
      refine ⟨S, hscrut, hwf, ?_⟩
      simpa only [Tau.rename, Ty.weaken] using
        Tm.DeepCheck.sub hbody hs' hwf'

theorem Tm.DeepCheck.let_inv
    (h : Tm.DeepCheck Gamma R (Tm.let s t) T) :
    exists S,
      Tm.DeepCheck Gamma R s S /\
      Tau.DeepWf Gamma R (Tau.ty T) /\
      Tm.DeepCheck (Gamma.snoc S) (Path.ConvLift R) t T.weaken :=
  h.let_inv_of_eq rfl

/-! ## Administrative preservation -/

theorem DeepPreserve.let_push
    (h : State.DeepTy Gamma ⟨sigma, k, Tm.let s t⟩ T) :
    DeepPreserve Gamma ⟨sigma, Tm.Frame.let t :: k, s⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      obtain ⟨S, hs, _, hbody⟩ := hterm.let_inv
      exact .same (.ok hstore (.cons hcont (.let hbody)) hs)

theorem DeepPreserve.ascribe
    (h : State.DeepTy Gamma ⟨sigma, k, Tm.typed t A⟩ T) :
    DeepPreserve Gamma ⟨sigma, k, t⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont hterm.typed_inv.1)

/-! ## Weakening continuations across allocation -/

theorem Tm.Frame.DeepTy.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {S T U : LambdaPHistory.Ty n} {F : Tm.Frame n}
    (h : Tm.Frame.DeepTy Gamma sigma S F T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Frame.DeepTy (Gamma.snoc U) (Store.val sigma v vv)
      S.weaken F.weaken T.weaken := by
  cases h with
  | «let» hbody =>
      apply Tm.Frame.DeepTy.let
      have hb := hbody.rename
        (Renaming.ext (Renaming.weaken (S := U)))
        (Path.ConvLift.rename
          (fun hpq => by
            simpa only [Path.weaken] using hpq.weaken v vv))
      rw [← Ty.weaken_rename] at hb
      simpa only [Tm.Frame.weaken, Tm.Frame.rename, Ty.weaken] using hb

theorem Tm.Cont.DeepTy.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {S T U : LambdaPHistory.Ty n} {k : Tm.Cont n}
    (h : Tm.Cont.DeepTy Gamma sigma S k T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Cont.DeepTy (Gamma.snoc U) (Store.val sigma v vv)
      S.weaken k.weaken T.weaken := by
  induction h with
  | hole hs =>
      simpa only [Tm.Cont.weaken, Tm.Cont.rename] using
        Tm.Cont.DeepTy.hole (hs.weaken_runtime U v vv)
  | cons hc hf ih =>
      simpa only [Tm.Cont.weaken, Tm.Cont.rename, List.map_cons] using
        Tm.Cont.DeepTy.cons ih (hf.weaken_runtime v vv)

theorem DeepPreserve.lift
    (vv : v.IsValue)
    (h : State.DeepTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, v⟩ T) :
    DeepPreserve Gamma
      ⟨Store.val sigma v vv, Tm.Cont.weaken k, t⟩ T := by
  cases h with
  | ok hstore hcont hvalue =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              have hbody' : Tm.DeepCheck (Gamma.snoc _)
                  (Path.RuntimeEq (Store.val sigma v vv)) t _ :=
                hbody.mono (fun hpq => hpq.to_extended)
              exact .extend (.ok (.val hstore hvalue vv)
                (hrest.weaken_runtime v vv) hbody')

/-! ## The exact remaining opening contract -/

/-- Runtime substitution for one formal binder.

The replacement premise is deliberately a *term* typing for the location,
not exact path synthesis at `S`: ordinary arguments acquire their parameter
type through the singleton `{x}` and subsumption. -/
def Tm.DeepOpening : Prop :=
  forall {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
      {S : LambdaPHistory.Ty n} {t : Tm (n + 1)}
      {T : LambdaPHistory.Ty (n + 1)} {x : Fin n},
    Tm.DeepCheck (Gamma.snoc S) (Path.ConvLift R) t T ->
    Tm.DeepCheck Gamma R (Tm.path (Path.var x)) S ->
    Tm.DeepCheck Gamma R (t.open x) (T.rename (FinFun.openAt x))

/-- The single-binder opening theorem is sufficient for the complete
historical `rename` transition. -/
theorem DeepPreserve.rename_of_opening
    (hopen : Tm.DeepOpening)
    (h : State.DeepTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, Tm.path (Path.var x)⟩ T) :
    DeepPreserve Gamma ⟨sigma, k, t.open x⟩ T := by
  cases h with
  | ok hstore hcont harg =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              have hopened := hopen hbody harg
              apply DeepPreserve.same
              apply State.DeepTy.ok hstore hrest
              simpa only [Ty.weaken, Ty.rename_rename,
                FinFun.openAt_weaken, Ty.rename_id] using hopened

end LambdaPHistory
