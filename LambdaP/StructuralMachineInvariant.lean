import LambdaP.Machine
import LambdaP.StructuralRuntimeLemmas

/-!
The machine invariant built from fully structural runtime judgments.

Unlike the earlier `DeepMachineInvariant`, no source-subtyping derivation is
kept as an opaque conversion step.  Suspended bodies are checked under
`Path.ScopedLift`; after a variable is supplied, the checked structural
opening theorem discharges that binder.
-/

namespace LambdaP

/-! ## Store, frame, continuation, and state typing -/

inductive Store.StructTy : {n : Nat} -> Ctx n -> Store n -> Prop where
| empty : Store.StructTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.StructTy Gamma sigma ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ->
    (vv : v.IsValue) ->
    Store.StructTy (Gamma.snoc T) (Store.val sigma v vv)

theorem Store.Ty.toStruct (h : Store.Ty Gamma sigma) :
    Store.StructTy Gamma sigma := by
  induction h with
  | empty => exact .empty
  | val hstore ht ih =>
      exact .val ih (Tm.StructCheck.of_source ht _) (by assumption)

/-- Every context index of a structurally typed store is occupied by a
runtime value. -/
theorem Store.StructTy.lookup_value
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.StructTy Gamma sigma) (x : Fin n) :
    exists v, Store.Binds sigma x v /\ v.IsValue := by
  induction h with
  | empty => exact Fin.elim0 x
  | val hstore hterm vv ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨_, .here, vv.weaken⟩
      · obtain ⟨u, hu, huv⟩ := ih y
        exact ⟨u.weaken, .there hu, huv.weaken⟩

inductive Tm.Frame.StructTy (Gamma : Ctx n) (sigma : Store n) :
    LambdaP.Ty n -> Tm.Frame n ->
      LambdaP.Ty n -> Prop where
| «let» :
    Tm.StructCheck (Gamma.snoc S)
      (Path.ScopedLift (Path.RuntimeEq sigma)) t T.weaken ->
    Tm.Frame.StructTy Gamma sigma S (Tm.Frame.let t) T

inductive Tm.Cont.StructTy (Gamma : Ctx n) (sigma : Store n) :
    LambdaP.Ty n -> Tm.Cont n ->
      LambdaP.Ty n -> Prop where
| hole :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty T) ->
    Tm.Cont.StructTy Gamma sigma S [] T
| cons :
    Tm.Cont.StructTy Gamma sigma S E T ->
    Tm.Frame.StructTy Gamma sigma U F S ->
    Tm.Cont.StructTy Gamma sigma U (F :: E) T

theorem Tm.Frame.Ty.toStruct
    {n : Nat} {Gamma : Ctx n} {S T : LambdaP.Ty n}
    {F : Tm.Frame n}
    (h : Tm.Frame.Ty Gamma S F T) (sigma : Store n) :
    Tm.Frame.StructTy Gamma sigma S F T := by
  cases h with
  | «let» ht => exact .let (Tm.StructCheck.of_source ht _)

theorem Tm.Cont.Ty.toStruct
    {n : Nat} {Gamma : Ctx n} {S T : LambdaP.Ty n}
    {k : Tm.Cont n}
    (h : Tm.Cont.Ty Gamma S k T) (sigma : Store n) :
    Tm.Cont.StructTy Gamma sigma S k T := by
  induction h with
  | hole hsub => exact .hole (Tau.StructSub.of_source hsub _)
  | cons hc hf ih => exact .cons ih (hf.toStruct sigma)

inductive State.StructTy : Ctx n -> State n ->
    LambdaP.Ty n -> Prop where
| ok :
    Store.StructTy Gamma sigma ->
    Tm.Cont.StructTy Gamma sigma S k T ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) t S ->
    State.StructTy Gamma ⟨sigma, k, t⟩ T

theorem State.Ty.toStruct (h : State.Ty Gamma state T) :
    State.StructTy Gamma state T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .ok hstore.toStruct (hcont.toStruct _)
        (Tm.StructCheck.of_source hterm _)

inductive StructPreserve : Ctx n -> State m ->
    LambdaP.Ty n -> Prop where
| same : State.StructTy Gamma state T -> StructPreserve Gamma state T
| extend :
    State.StructTy (Gamma.snoc S) state T.weaken ->
    StructPreserve Gamma state T

/-! ## Path-term replacement -/

theorem Tm.StructCheck.reduce_path
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {T : LambdaP.Ty n}
    (hr : Path.reduce p sigma x)
    (h : Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path p) T) :
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) T := by
  cases h.path_inversion rfl with
  | intro U hp hsub hwf =>
      exact .sub (.path (hp.reduce_to_var hr))
        (hsub.reduce_singleton_left hr) hwf

theorem StructPreserve.path
    (hr : Path.reduce p sigma x)
    (h : State.StructTy Gamma ⟨sigma, k, Tm.path p⟩ T) :
    StructPreserve Gamma
      ⟨sigma, k, Tm.path (Path.var x)⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont (hterm.reduce_path hr))

/-! ## Inversion through trailing structural subsumption -/

private theorem Tm.StructCheck.typed_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {u : Tm n} {T : LambdaP.Ty n}
    (h : Tm.StructCheck Gamma R u T) :
    forall {t : Tm n} {A : LambdaP.Ty n},
      u = Tm.typed t A ->
      Tm.StructCheck Gamma R t T /\ Tau.StructWf Gamma R (Tau.ty T) := by
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

theorem Tm.StructCheck.typed_inv
    (h : Tm.StructCheck Gamma R (Tm.typed t A) T) :
    Tm.StructCheck Gamma R t T /\ Tau.StructWf Gamma R (Tau.ty T) :=
  h.typed_inv_of_eq rfl

private theorem Tm.StructCheck.let_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {u : Tm n} {T : LambdaP.Ty n}
    (h : Tm.StructCheck Gamma R u T) :
    forall {s : Tm n} {t : Tm (n + 1)}, u = Tm.let s t ->
      exists S,
        Tm.StructCheck Gamma R s S /\
        Tau.StructWf Gamma R (Tau.ty T) /\
        Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T.weaken := by
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
      have hs' := hs.renameExact (Renaming.weaken (S := S))
        (fun {p q} hpq => Path.ScopedLift.old hpq)
      have hwf' := hwf.renameExact (Renaming.weaken (S := S))
        (fun {p q} hpq => Path.ScopedLift.old hpq)
      refine ⟨S, hscrut, hwf, ?_⟩
      simpa only [Tau.rename, Ty.weaken] using
        Tm.StructCheck.sub hbody hs' hwf'

theorem Tm.StructCheck.let_inv
    (h : Tm.StructCheck Gamma R (Tm.let s t) T) :
    exists S,
      Tm.StructCheck Gamma R s S /\
      Tau.StructWf Gamma R (Tau.ty T) /\
      Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T.weaken :=
  h.let_inv_of_eq rfl

/-! ## Administrative transitions -/

theorem StructPreserve.let_push
    (h : State.StructTy Gamma ⟨sigma, k, Tm.let s t⟩ T) :
    StructPreserve Gamma ⟨sigma, Tm.Frame.let t :: k, s⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      obtain ⟨S, hs, _, hbody⟩ := hterm.let_inv
      exact .same (.ok hstore (.cons hcont (.let hbody)) hs)

theorem StructPreserve.ascribe
    (h : State.StructTy Gamma ⟨sigma, k, Tm.typed t A⟩ T) :
    StructPreserve Gamma ⟨sigma, k, t⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont hterm.typed_inv.1)

/-! ## Allocation -/

theorem Tm.Frame.StructTy.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {S T U : LambdaP.Ty n} {F : Tm.Frame n}
    (h : Tm.Frame.StructTy Gamma sigma S F T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Frame.StructTy (Gamma.snoc U) (Store.val sigma v vv)
      S.weaken F.weaken T.weaken := by
  cases h with
  | «let» hbody =>
      apply Tm.Frame.StructTy.let
      have hb := hbody.renameExact
        (Renaming.ext (Renaming.weaken (S := U)))
        (Path.RelHom.scoped (Path.RelHom.runtime_weaken v vv))
      rw [← Ty.weaken_rename] at hb
      simpa only [Tm.Frame.weaken, Tm.Frame.rename, Ty.weaken] using hb

theorem Tm.Cont.StructTy.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {S T U : LambdaP.Ty n} {k : Tm.Cont n}
    (h : Tm.Cont.StructTy Gamma sigma S k T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Cont.StructTy (Gamma.snoc U) (Store.val sigma v vv)
      S.weaken k.weaken T.weaken := by
  induction h with
  | hole hs =>
      simpa only [Tm.Cont.weaken, Tm.Cont.rename] using
        Tm.Cont.StructTy.hole (hs.weaken_runtime U v vv)
  | cons hc hf ih =>
      simpa only [Tm.Cont.weaken, Tm.Cont.rename, List.map_cons] using
        Tm.Cont.StructTy.cons ih (hf.weaken_runtime v vv)

private theorem Renaming.identity (Gamma : Ctx n) :
    Renaming Gamma FinFun.id Gamma := by
  intro x T hx
  simpa only [Ty.rename_id] using hx

private theorem Path.RelHom.scoped_to_runtime_extension
    {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue} :
    Path.RelHom (Path.ScopedLift (Path.RuntimeEq sigma))
      (Path.RuntimeEq (Store.val sigma v vv)) FinFun.id := by
  intro p q hpq
  simpa only [Path.rename_id] using hpq.to_runtime_extension

theorem StructPreserve.lift
    (vv : v.IsValue)
    (h : State.StructTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, v⟩ T) :
    StructPreserve Gamma
      ⟨Store.val sigma v vv, Tm.Cont.weaken k, t⟩ T := by
  cases h with
  | ok hstore hcont hvalue =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              have hbody' := hbody.renameExact
                (Renaming.identity (Gamma.snoc _))
                (Path.RelHom.scoped_to_runtime_extension (v := v) (vv := vv))
              apply StructPreserve.extend
              apply State.StructTy.ok (.val hstore hvalue vv)
                (hrest.weaken_runtime v vv)
              simpa only [Tm.rename_id, Ty.rename_id] using hbody'

/-! ## Variable opening (`rename`) -/

theorem StructPreserve.rename
    (h : State.StructTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, Tm.path (Path.var x)⟩ T) :
    StructPreserve Gamma ⟨sigma, k, t.open x⟩ T := by
  cases h with
  | ok hstore hcont harg =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              have hopened := hbody.open_var_of_path_term
                (Path.RuntimeEq.isEquivCongr sigma) harg
              apply StructPreserve.same
              apply State.StructTy.ok hstore hrest
              simpa only [Ty.weaken, Ty.rename_rename,
                FinFun.openAt_weaken, Ty.rename_id] using hopened

end LambdaP
