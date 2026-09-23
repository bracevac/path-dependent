import Coercions.FCdotR.Preservation

/-!
# Progress for the FCdotR machine

A typed state over an honest machine store is final or steps.  This is the
companion of `Preservation`, for the same machine (`Machine.Step`, kept as it
is) and the same typing up to evidence (`Preservation.StateTy`).

## Where typing is needed, and where it is not

Five of the six rules of `Machine.Step` fire on **syntax alone**: a `let` or a
`cast` always pushes a frame, a `new` always allocates, and an atom is always
absorbed by the innermost frame, whichever it is — evidence never blocks and
never fires.  So `progress_of_not_app` needs neither a typing nor a store
invariant: every state whose running term is not an invocation is final or
steps.

The sixth rule, `app`, fires only if the receiver's root holds a method at the
invoked label.  That is the one place typing is consumed, and what it consumes
is canonical forms for methods — the hypothesis `AppInversion` of
`Preservation`, the same one the `app` case of preservation takes.
`progress_app` is the invocation case under it, and `progress` the two
together.

`not_stuck` and `safety` are the corollaries in the shape of
`DotToFCdot/Safety.lean`'s `dot_not_stuck`, for the *target* machine: a closed
term typed over the empty store never reaches a stuck state.
`safety_of_source` starts instead from an elaborable source configuration over
an honest source store, through `Preservation.StateTy.ofSource`.  All three
carry `AppInversion`, which `Preservation.AppInversion.ofObs` supplies from its
evidence-level content `ObsFunInversion`.

What this module does **not** contain: any proof of `AppInversion` (that is
`MethodInversion.appInversion`, which imports this module and restates
`progress`, `not_stuck`, `safety` and `safety_of_source` without the
hypothesis), and any transport of safety to `Oopsla16` (that is
`Correspondence`, `ElaborationFull`, `Simulation` and `SourceSafety`, which
relate the machine to the source by `Correspondence.Corr` instead of
`Erasure`'s let-free simulation).
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Subst Grows)

/-- A state that can take a step, to some state at some grown store scope. -/
def State.CanStep {σ : Sig} (st : State σ) : Prop :=
  ∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Step g st st'

/-- **Progress away from invocations, with no hypothesis at all.**  Every state
whose running term is not an `app` is final or steps, whatever its typing and
its store: `let`, `cast` and `new` always fire, and an atom is absorbed by the
innermost frame, or is an answer when there is none.  No evidence is ever
inspected, so none can block. -/
theorem progress_of_not_app {σ : Sig} (st : State σ)
    (hna : ∀ (a : Atom σ []) (l : Lb) (b : Atom σ []), st.t ≠ .app a l b) :
    st.Final ∨ st.CanStep := by
  obtain ⟨G, K, t⟩ := st
  cases t with
  | atom a =>
      cases K with
      | nil => exact Or.inl ⟨rfl, a, rfl⟩
      | cons K f =>
          cases f with
          | «let» u => exact Or.inr ⟨_, _, _, Step.rename⟩
          | cast e => exact Or.inr ⟨_, _, _, Step.castAtom⟩
  | new T ds => exact Or.inr ⟨_, _, _, Step.alloc⟩
  | app a l b => exact absurd rfl (hna a l b)
  | «let» t u => exact Or.inr ⟨_, _, _, Step.let⟩
  | cast t e => exact Or.inr ⟨_, _, _, Step.castPush⟩

/-- **Progress at an invocation.**  The witness's invocation is opened
(`TmTy.viewApp`): its receiver is typed at a method type and rooted where the
running receiver is, so `AppInversion` finds the stored method the machine's
`app` rule looks up.

**Stated with a hypothesis:** `hinv : AppInversion`, which this module does
not prove; `MethodInversion.appInversion` inhabits it. -/
theorem progress_app (hinv : AppInversion) {σ : Sig} {G : MachineStore σ σ}
    {K : Cont σ} {a b : Atom σ []} {l : Lb} {W : StoreTy σ} {U : Ty σ []}
    (h : MachineStore.Honest G W) (d : StateTy ⟨G, K, .app a l b⟩ W U) :
    State.CanStep ⟨G, K, .app a l b⟩ := by
  have v := TmTy.viewApp d.tmTy d.tmSkel
  have inv := hinv.inv h v.fnTy
  have hlk : (G.lookup (Vr.loc a.root)).fun? l = some (inv.S, inv.U, inv.body) := by
    rw [← v.fnRoot]
    exact inv.lookup
  exact ⟨_, _, _, Step.app hlk⟩

/-- **Progress.**  A typed state over an honest machine store is final or
steps.  Every case but the invocation is `progress_of_not_app`, which uses
neither hypothesis; the invocation is `progress_app`.

**Stated with a hypothesis:** `hinv : AppInversion`, used by the invocation
case only and inhabited by `MethodInversion.appInversion`;
`MethodInversion.progress'` is this theorem without it. -/
theorem progress (hinv : AppInversion) {σ : Sig} {st : State σ} {W : StoreTy σ}
    {U : Ty σ []} (h : MachineStore.Honest st.G W) (d : StateTy st W U) :
    st.Final ∨ st.CanStep := by
  obtain ⟨G, K, t⟩ := st
  cases t with
  | app a l b => exact Or.inr (progress_app hinv h d)
  | atom a => exact progress_of_not_app _ (fun _ _ _ h => by cases h)
  | new T ds => exact progress_of_not_app _ (fun _ _ _ h => by cases h)
  | «let» t u => exact progress_of_not_app _ (fun _ _ _ h => by cases h)
  | cast t e => exact progress_of_not_app _ (fun _ _ _ h => by cases h)

/-- **A typed state over an honest store is not stuck.**

**Stated with a hypothesis:** `hinv : AppInversion`, inhabited by
`MethodInversion.appInversion`; `MethodInversion.not_stuck'` is this theorem
without it. -/
theorem not_stuck (hinv : AppInversion) {σ : Sig} {st : State σ} {W : StoreTy σ}
    {U : Ty σ []} (h : MachineStore.Honest st.G W) (d : StateTy st W U) :
    ¬ st.Stuck := by
  intro hst
  rcases progress hinv h d with hf | hs
  · exact hst.1 hf
  · exact hst.2 hs

/-- **Type safety of the FCdotR machine.**  A closed term typed over the empty
store, run from the empty continuation, never reaches a stuck state: every
reachable state is typed over an honest store (`preservation_init`), hence
final or able to step (`progress`).

**Stated with a hypothesis:** `hinv : AppInversion`, canonical forms for
methods, which this module does not prove; `MethodInversion.appInversion`
inhabits it and `MethodInversion.safety'` is this theorem without it. -/
theorem safety (hinv : AppInversion) {W : StoreTy []} {t : Tm [] []}
    {T : Ty [] []} (d : TmTy Store.nil W Ctx.nil t T) {σ : Sig} {g : Grows [] σ}
    {st' : State σ} (hs : Steps g ⟨MachineStore.nil, .nil, t⟩ st') :
    ¬ st'.Stuck := by
  obtain ⟨W', ⟨h', d'⟩⟩ := preservation_init hinv d hs
  exact not_stuck hinv h' d'

/-- **Type safety from an elaborable source configuration.**  A source term
typed over an honest source store, the term and every stored witness in the
elaborable fragment, starts the machine at the state `StateTy.ofSource`
builds — whose store erases to the source store and whose term erases to the
source term — and no run from there reaches a stuck state.

**Stated with a hypothesis:** `hinv : AppInversion`, inhabited by
`MethodInversion.appInversion`; `MethodInversion.safety_of_source'` is this
theorem without it. -/
theorem safety_of_source (hinv : AppInversion) {σ : Sig} {G : Store σ σ}
    {W : StoreTy σ} (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs)
    {t : Oopsla16.Tm σ []} {T : Ty σ []} (ht : Oopsla16.HasType G Ctx.nil t T)
    (ft : TmFrag t) {σ' : Sig} {g : Grows σ σ'} {st' : State σ'}
    (hs : Steps g (StateTy.ofSource h hf ht ft).1 st') : ¬ st'.Stuck := by
  obtain ⟨W', ⟨h', d'⟩⟩ :=
    preservation_steps hinv (StateTy.ofSource h hf ht ft).2.1
      (StateTy.ofSource h hf ht ft).2.2.1 hs
  exact not_stuck hinv h' d'

/-- The `FunctionField` object literal of `TermTyping` runs safely.

**Stated with a hypothesis:** `hinv : AppInversion`, inhabited by
`MethodInversion.appInversion`. -/
example (hinv : AppInversion) {σ : Sig} {g : Grows [] σ} {st' : State σ}
    (hs : Steps g ⟨MachineStore.nil, .nil, FunctionFieldObject.literal.1⟩ st') :
    ¬ st'.Stuck :=
  safety hinv FunctionFieldObject.literal.2 hs

end FCdotR
