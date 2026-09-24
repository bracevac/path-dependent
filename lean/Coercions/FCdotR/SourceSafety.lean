import Coercions.FCdotR.ElaborationFull
import Coercions.FCdotR.Simulation

/-!
# Type safety of `Oopsla16`, transported from FCdotR

This is the end of the line `Oopsla16 → FCdotR`.  The source is the Rompf–Amin
OOPSLA'16 calculus with its own substitution machine (`Oopsla16.Semantics`).
Its safety is stated about that machine, `Oopsla16.Steps`, and is proved
without any source-side preservation or canonical-forms argument.  The typing
work is all done in the target, as in the WadlerFest line
(`DotToFCdot/Safety.lean`, `DotMNF.dot_safety`).

## The headline results, none with a hypothesis

* `Oopsla16.oopsla16_safety`: a closed source term typed over the empty store
  never reaches a stuck configuration (`FCdotR.SrcStuck`: not an answer and
  no `Oopsla16.Step`).
* `Oopsla16.oopsla16_not_stuck`: the positive form, in the shape of
  `DotMNF.dot_safety`.  Every configuration such a term reaches is an answer or
  takes a source step.  Its statement mentions only `Oopsla16` notions.
* `Oopsla16.oopsla16_safety_honest`, `Oopsla16.oopsla16_not_stuck_honest`: the
  same from an **honest initial store** (`Store.Honest`).  The term is
  arbitrary.  The literal each stored location was typed from must lie in the
  fragment `DmsFrag`: variable operands and annotated methods.  That
  restriction is stated in the theorems, and *What this module does not
  contain* below says why it is there.

## How they are assembled

The ingredients are the three stages before this one.

1. **Elaboration** (`ElaborationFull.elabTm`, `elabSpec : ElabSpec`).  Every
   source typing becomes a typed FCdotR term that corresponds to the source
   term (`Correspondence.Corr`).
2. **Simulation** (`Correspondence.sim_step`, `sim_stuck`, `sim_spec :
   SimSpec`).  A source step from a related pair is matched by a target run.
   A stuck source configuration makes the related target run into a stuck
   state.
3. **Target safety** (`MethodInversion.safety'`).  The FCdotR machine run from
   a closed typed term never gets stuck.

`oopsla16_safety` is `Correspondence.transport` at `elabSpec` and `sim_spec`.
`transport` is the stage-1 argument: simulate the source run, carry a stuck
source configuration to a stuck target state, and let `safety'` refute it.

The positive form is not a corollary of the negative one here.  Getting
`answer ∨ step` from `¬ stuck` needs classical logic, and this module uses
none.  It is proved directly from `Simulation.Simulated`: a typed target state
over an honest machine store, related to the source configuration.
`Simulated.init` establishes that invariant for a closed typed term,
`Simulated.steps` carries it along every source run, and `Simulated.progress`
reads off `answer ∨ step`.

The same invariant gives the honest-store versions.  `Simulated.of_honest`
starts it from `Preservation.Store.Honest.toMachine`, the machine store of the
elaborated witnesses, and the elaboration of the term.  `StoreCorr.ofHonest`
relates that machine store to the source store.

This module also restates `Simulation`'s two theorems that took
`hE : ElabSpec` without the hypothesis: `Simulated.init` and `elab_adequacy'`.

## Worked instances

* `SourceSafety.ex0_safe`: the empty object `Oopsla16.Examples.ex0`.
* `SourceSafety.RecursiveArg`: a method that accepts only objects of type
  `μz. T(z)`, applied to an object literal whose typing needs recursive
  subtyping.  That subtyping is `Oopsla16.Examples.FunctionField.recursive`
  (`stp_bindx`).  Its WadlerFest counterpart has no closed inclusion evidence
  in FCdot (`DotMNF.RecursiveSubtyping.FunctionField.no_coercion`, in
  `DotToFCdot/RecursiveSubtypingSeparation.lean`).  The instance
  exhibits the source run: two allocations and one invocation, ending in an
  answer.  It also applies both headline theorems.
* `SourceSafety.HonestCall`: an identity method applied to a location of the
  honest two-object store `StoreTyping.TwoObjectStore`, through
  `oopsla16_safety_honest`.

## What this module does not contain

* **No honest-store theorem for witnesses outside `DmsFrag`.**  The machine's
  honesty invariant `Preservation.MachineStore.Honest` types each stored target
  literal over the machine store's **erasure**.  For a fragment witness,
  elaboration introduces no `let`, so the erasure is the source store on the
  nose (`Store.Honest.toMachine_erase`), and the source-store typings the
  elaboration produces apply as they stand.  A general witness elaborates with
  `let`s in its method bodies.  Those erase to object encodings
  (`Erasure.letEncode`), so the erased machine store is not the source store.
  Retyping the elaboration over it would need target typing carried back
  through erasure into source typing.  The location rules' premise
  (`varConcAny`, `Typing.LitMatch`) reads a stored literal's type members and
  method annotations, and the machine store annotates a Curry-style method
  with the types its honesty witness checked, so a store with the same type
  members is not enough.  `STATUS.md` records that translation as not built.
  Stores reached by running are unaffected: a run from the empty store keeps
  the invariant by preservation, whatever the allocated literals are, which is
  why `oopsla16_safety` has no fragment restriction.
* No source-side typing metatheory, no determinism result, nothing about
  divergence, and no classical logic.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst Grows HasType DmsHasType)

/-! ## `Simulation`'s theorems without `ElabSpec` -/

/-- **A closed typed source term is simulated**: `Simulation.Simulated.of_elab`
at `ElaborationFull.elabSpec`.  No hypothesis.  This is the counterpart of
`DotMNF.simulated_init`. -/
theorem Simulated.init {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) : Simulated Store.nil t :=
  Simulated.of_elab elabSpec ht

/-- **The elaboration is adequate for answers, with no hypothesis**:
`Simulation.elab_adequacy` at `ElaborationFull.elabSpec`.  A closed typed
source term has a typed, related elaboration.  The source reaches an answer
exactly when the target machine run from the elaboration reaches a final
state. -/
theorem elab_adequacy' {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) :
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧
        Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩ ∧
        ((∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
            Oopsla16.Steps g Store.nil t G' t' ∧ t'.IsAnswer) ↔
          (∃ (σ : Sig) (g : Grows [] σ) (st' : State σ),
            Steps g ⟨MachineStore.nil, .nil, d⟩ st' ∧ st'.Final)) :=
  elab_adequacy elabSpec ht

/-! ## From an honest source store -/

/-- **The machine store of an honest source store corresponds to it**.  At each
location it holds the elaborated witness with its self instantiated there.
The elaborated witness corresponds to the source witness
(`Correspondence.elabDms_corr`), instantiation keeps that
(`DmsCorr.inst`), and the source witness instantiated there is what the source
store holds (`HonestAt.stored`). -/
theorem StoreCorr.ofHonest {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) :
    StoreCorr G (h.toMachine hf) := fun l => by
  show DmsCorr (G.lookup l) ((MachineStore.ofShape G _).lookup l)
  rw [MachineStore.lookup_ofShape, ← (h.at' l).stored]
  exact DmsCorr.inst (elabDms_corr (hA := h.annotated hf) W (h.at' l).typed (hf l)) .base l

/-- **A source configuration over an honest store is simulated.**  The term
`t` is arbitrary, so it need not be in `TmFrag`.  The witness each location was
typed from must be in `DmsFrag`.

The machine store is `Store.Honest.toMachine`, honest by
`Store.Honest.toMachine_honest`, and it corresponds to `G` by
`StoreCorr.ofHonest`.  The running term is `ElaborationFull.elabTm`'s
elaboration of `t`, whose hypothesis `Store.Annotated G` the fragment
witnesses supply (`Store.Honest.annotated`).  It is typed over the source
store, which is the machine store's erasure (`Store.Honest.toMachine_erase`).
So the initial state is typed on the nose, with the empty continuation.  No
hypothesis beyond `h` and `hf`. -/
theorem Simulated.of_honest {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs) {t : Oopsla16.Tm σ []}
    {T : Ty σ []} (ht : HasType G Ctx.nil t T) : Simulated G t := by
  have r := elabTm (hA := h.annotated hf) W ht
  have d : TmTy (h.toMachine hf).erase W Ctx.nil r.tm T := by
    rw [h.toMachine_erase hf]
    exact r.typed
  exact ⟨⟨h.toMachine hf, .nil, r.tm⟩, W, T, ⟨StoreCorr.ofHonest h hf, r.corr⟩,
    ⟨h.toMachine_honest hf, ⟨T, r.tm, d, rfl, .nil, .nil, rfl⟩⟩⟩

end FCdotR

/-! ## Type safety of `Oopsla16`

In the source's namespace, as `DotMNF.dot_safety` is in `DotMNF`'s.  The
stuck predicate is `FCdotR.SrcStuck`.  It mentions only `Oopsla16.Tm.IsAnswer`
and `Oopsla16.Step`. -/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-- **Type safety of `Oopsla16`'s own machine, with no hypothesis.**  No
configuration reachable under `Oopsla16.Steps` from a closed term typed over
the empty store is stuck.  There is no restriction on the term: applications
may have arbitrary operands, and methods may be written in Curry style.

This is `FCdotR.transport`, the stage-1 argument, at the two inhabitants.
`FCdotR.elabSpec` elaborates the typing into a typed, related target term.
`FCdotR.sim_spec` simulates the source run from it, and runs a stuck source
configuration into a stuck target state.  `FCdotR.safety'`
(`MethodInversion`) says the target machine never reaches one. -/
theorem oopsla16_safety {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') : ¬ FCdotR.SrcStuck G' t' :=
  FCdotR.transport FCdotR.elabSpec FCdotR.sim_spec ht run

/-- **Progress along every run of `Oopsla16`, with no hypothesis**: every
configuration reachable from a closed term typed over the empty store is an
answer or takes a source step.  This is the positive form of `oopsla16_safety`,
and the shape of `DotMNF.dot_safety`.  Its statement mentions only `Oopsla16`.

It is proved constructively, not derived from `oopsla16_safety`.
`FCdotR.Simulated.init` starts the invariant, and
`FCdotR.Simulated.reachable_progress` carries it along the run and reads off
the disjunction.  `FCdotR.oopsla16_progress` (`ElaborationFull`) is the same
statement, proved directly from the simulation. -/
theorem oopsla16_not_stuck {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') :
    t'.IsAnswer ∨ ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Tm σ' []),
      Step g' G' t' G'' t'' :=
  (FCdotR.Simulated.init ht).reachable_progress run

/-- **Type safety from an honest initial store.**  A term typed over an honest
source store `G` never reaches a stuck configuration.

**Restriction, not a hypothesis:** the literal each location of `G` was typed
from, `(h.at' l).defs`, must be in the elaborable fragment `FCdotR.DmsFrag`.
The term `t` is unrestricted.  The module header says why the restriction is
there.  The empty store satisfies it vacuously.

By `FCdotR.Simulated.of_honest`, `Simulated.steps` and `Simulated.not_stuck`.
No hypothesis. -/
theorem oopsla16_safety_honest {σ : Sig} {G : Store σ σ} {W : FCdotR.StoreTy σ}
    (h : FCdotR.Store.Honest G W) (hf : ∀ l, FCdotR.DmsFrag (h.at' l).defs)
    {t : Tm σ []} {T : Ty σ []} (ht : HasType G Ctx.nil t T)
    {σ' : Sig} {g : Grows σ σ'} {G' : Store σ' σ'} {t' : Tm σ' []}
    (run : Steps g G t G' t') : ¬ FCdotR.SrcStuck G' t' :=
  ((FCdotR.Simulated.of_honest h hf ht).steps run).not_stuck

/-- **Progress from an honest initial store**: the positive form of
`oopsla16_safety_honest`, with the same restriction on the stored witnesses
(`FCdotR.DmsFrag`) and no hypothesis. -/
theorem oopsla16_not_stuck_honest {σ : Sig} {G : Store σ σ} {W : FCdotR.StoreTy σ}
    (h : FCdotR.Store.Honest G W) (hf : ∀ l, FCdotR.DmsFrag (h.at' l).defs)
    {t : Tm σ []} {T : Ty σ []} (ht : HasType G Ctx.nil t T)
    {σ' : Sig} {g : Grows σ σ'} {G' : Store σ' σ'} {t' : Tm σ' []}
    (run : Steps g G t G' t') :
    t'.IsAnswer ∨ ∃ (σ'' : Sig) (g' : Grows σ' σ'') (G'' : Store σ'' σ'') (t'' : Tm σ'' []),
      Step g' G' t' G'' t'' :=
  (FCdotR.Simulated.of_honest h hf ht).reachable_progress run

end Oopsla16

/-! ## Worked instances -/

namespace FCdotR.SourceSafety

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Grows HasType DmsHasType Stp Htp)

/-- **The empty object never gets stuck.**  `Oopsla16.Examples.ex0` types
`{ z => }` at `⊤`.  Every configuration it reaches is not stuck, by
`Oopsla16.oopsla16_safety`. -/
theorem ex0_safe {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g Store.nil (.tobj .dnil) G' t') : ¬ SrcStuck G' t' :=
  Oopsla16.oopsla16_safety Oopsla16.Examples.ex0 run

/-! ### A recursive-subtyping argument

```text
ff     = new { type A = z.B; type B = ⊤; def f(y) = y }   -- precise type μz. P(z)
caller = new { def 0(y) = y }            -- declared at 0 : μz. T(z) → ⊤
prog   = caller 0 ff                     -- T_App, both operands objects
```

`P(z)` is `ff`'s precise type, the one `D_Typ`/`D_Fun` produce:

```text
P(z) = {A : z.B .. z.B} ∧ ({B : ⊤ .. ⊤} ∧ ({f : ∀(_ : ⊤) z.A} ∧ ⊤))
```

It is subsumed to `μz. T(z) = μz. {f : ∀(_ : ⊤) z.B}`, which `caller`'s method
demands.  Two `stp_bindx` steps do it: first `μz. P(z) <: μz. S(z)` (`PS`),
then `Oopsla16.Examples.FunctionField.recursive`.  The method `f` returns its
`⊤` argument at `z.A`.  Two `stp_sel2` steps raise it, through the lower
bounds `⊤ <: z.B` and `z.B <: z.A`.

The program is outside `TmFrag` twice over.  Both operands of its application
are object literals, and both methods are Curry-style. -/

namespace RecursiveArg

open Oopsla16.Examples.FunctionField (A B f Sbody Tbody recursive)

/-- `z.B`, at the self's own scope. -/
abbrev zB : Ty [] ([],x) := .TSel (.abs .here) B

/-- `z.A`, under the method's parameter. -/
abbrev zA : Ty [] (([],x),x) := .TSel (.abs (.there .here)) A

/-- `P(z)`, the precise self type of `ff`. -/
abbrev P : Ty [] ([],x) :=
  .TAnd (.TTyp A zB zB) (.TAnd (.TTyp B .TTop .TTop) (.TAnd (.TFun f .TTop zA) .TTop))

/-- `ff`'s definitions, Curry-style: `type A = z.B`, `type B = ⊤`,
`def f(y) = y`.  The labels are the positions, `A = 2`, `B = 1`, `f = 0`. -/
abbrev Dff : Dms [] ([],x) :=
  .dcons (.dty zB) (.dcons (.dty .TTop) (.dcons (.dfun none none (.tvar (.abs .here))) .dnil))

/-- The context of `f`'s body: the self at `P(z)`, then the parameter at `⊤`. -/
abbrev Γf : Ctx [] (([],x),x) := (Ctx.nil.cons P).cons .TTop

/-- The self's `B` member seen from `f`'s body, through `htp_sub` in the
self's prefix. -/
def memB : Htp Store.nil Γf (.there .here) (.TTyp B .TTop .TTop) :=
  .htp_sub .htp_var (.stp_and12 (.stp_and11 (.stp_typ .stp_top .stp_top)))

/-- The self's `A` member, weakened to the lower bound `z.B`. -/
def memA : Htp Store.nil Γf (.there .here) (.TTyp A zB .TTop) :=
  .htp_sub .htp_var (.stp_and11 (.stp_typ .stp_selx .stp_top))

/-- `⊤ <: z.A` under the parameter: `⊤ <: z.B <: z.A`, by `stp_sel2` twice. -/
def topLeA : Stp Store.nil Γf .TTop zA :=
  .stp_trans (T2 := .TSel (.abs (.there .here)) B) (.stp_sel2 memB) (.stp_sel2 memA)

/-- `f`'s body, the parameter `y : ⊤`, at `z.A`. -/
def bodyTy : HasType Store.nil Γf (.tvar (.abs .here)) zA :=
  .T_Sub (.T_Sub .T_Varz .stp_top) topLeA

/-- `ff`'s definitions at `P(z)`, under the self `P(z)`. -/
def dff : DmsHasType Store.nil (Ctx.nil.cons P) Dff P :=
  .D_Typ (.D_Typ (.D_Fun (T11 := .TTop) (T12 := zA) .D_Nil bodyTy (Or.inl rfl) (Or.inl rfl)))

/-- `P(z) <: S(z)` under the self `P(z)`: every bound of `S` is implied member
by member. -/
def PS : Stp Store.nil (Ctx.nil.cons P) P Sbody :=
  .stp_and2 (.stp_and11 (.stp_typ .stp_bot .stp_selx))
    (.stp_and2 (.stp_and12 (.stp_and11 (.stp_typ .stp_bot .stp_top)))
      (.stp_and12 (.stp_and12 (.stp_and11 (.stp_fun .stp_top .stp_selx)))))

/-- **`ff` at `μz. T(z)`**, by recursive subtyping twice: `μz. P(z) <: μz. S(z)`
by `stp_bindx`, then `FunctionField.recursive`. -/
def ffTy : HasType Store.nil Ctx.nil (.tobj Dff) (.TBind Tbody) :=
  .T_Sub (.T_Obj dff) (.stp_trans (.stp_bindx PS) recursive)

/-- `μz. T(z)` weakened past `caller`'s self, the domain of its method. -/
abbrev Tμ : Ty [] ([],x) := (Ty.TBind Tbody).weaken

/-- `caller`'s self type: `{0 : μz. T(z) → ⊤} ∧ ⊤`. -/
abbrev Tc : Ty [] ([],x) := .TAnd (.TFun 0 Tμ .TTop) .TTop

/-- `caller`'s definitions, Curry-style: `def 0(y) = y`. -/
abbrev Dc : Dms [] ([],x) := .dcons (.dfun none none (.tvar (.abs .here))) .dnil

/-- `caller`'s definitions at its self type.  The body returns the parameter,
forgotten to `⊤`. -/
def dc : DmsHasType Store.nil (Ctx.nil.cons Tc) Dc Tc :=
  .D_Fun (T11 := Tμ) (T12 := .TTop) .D_Nil (.T_Sub .T_Varz .stp_top) (Or.inl rfl) (Or.inl rfl)

/-- Reflexivity at `μz. T(z)`, weakened.  The reference has no reflexivity
rule, so it is derived: `stp_bindx`, then `stp_fun` with `stp_top` and
`stp_selx`. -/
def reflTμ : Stp Store.nil (Ctx.nil.cons Tc) Tμ Tμ :=
  .stp_bindx (.stp_fun .stp_top .stp_selx)

/-- `μz. Tc(z) <: {0 : μz. T(z) → ⊤}`: `caller` forgets its self, which its
method type does not mention (`stp_bind1`). -/
def forgetC : Stp Store.nil Ctx.nil (.TBind Tc) (.TFun 0 (.TBind Tbody) .TTop) :=
  .stp_bind1 (.stp_and11 (.stp_fun reflTμ .stp_top))

/-- The program. -/
abbrev prog : Oopsla16.Tm [] [] := .tapp (.tobj Dc) 0 (.tobj Dff)

/-- **The program is typed at `⊤`**, by `T_App`.  The argument's typing is
`ffTy`, which uses `stp_bindx`. -/
def progTy : HasType Store.nil Ctx.nil prog .TTop :=
  .T_App (T2 := .TTop) (.T_Sub (.T_Obj dc) forgetC) ffTy

/-- The program is outside the fragment `Elaboration.elabHasType` handles. -/
theorem not_frag : TmFrag prog → False := fun h => nomatch h

/-- **The source run of the program.**  `ST_App1` allocates `caller`.
`ST_App2` then allocates `ff`, and `ST_AppAbs` invokes `caller`'s method on
it.  The result is the answer `ff`, the newest location.  Three steps of
`Oopsla16.Step`. -/
theorem prog_runs :
    ∃ (g : Grows [] (([],x),x)) (G' : Store (([],x),x) (([],x),x)),
      Oopsla16.Steps g Store.nil prog G' (.tvar (.conc .here)) :=
  ⟨_, _, .tail (.tail (.tail .refl (.ST_App1 .ST_Obj)) (.ST_App2 .ST_Obj))
    (.ST_AppAbs (OT1 := none) (OT2 := none) (t12 := .tvar (.abs .here)) rfl)⟩

/-- The run ends in an answer. -/
theorem prog_answers :
    ∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
      Oopsla16.Steps g Store.nil prog G' t' ∧ t'.IsAnswer := by
  obtain ⟨g, G', run⟩ := prog_runs
  exact ⟨_, g, G', _, run, trivial⟩

/-- **The program never gets stuck**, by `Oopsla16.oopsla16_safety` at
`progTy`. -/
theorem prog_safe {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g Store.nil prog G' t') : ¬ SrcStuck G' t' :=
  Oopsla16.oopsla16_safety progTy run

/-- **Every configuration the program reaches is an answer or steps**, by
`Oopsla16.oopsla16_not_stuck` at `progTy`. -/
theorem prog_progress {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g Store.nil prog G' t') :
    t'.IsAnswer ∨ ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
      Oopsla16.Step g' G' t' G'' t'' :=
  Oopsla16.oopsla16_not_stuck progTy run

/-- **The target machine run from the elaboration also reaches a final
state**, by `elab_adequacy'` and `prog_answers`. -/
theorem prog_target_final :
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧
        ∃ (σ : Sig) (g : Grows [] σ) (st' : State σ),
          Steps g ⟨MachineStore.nil, .nil, d⟩ st' ∧ st'.Final := by
  obtain ⟨W, d, T', hd, -, hiff⟩ := elab_adequacy' progTy
  exact ⟨W, d, T', hd, hiff.1 prog_answers⟩

end RecursiveArg

/-! ### An honest initial store

The two-object store `StoreTyping.TwoObjectStore` is honest at its store
typing `W`, and both witnesses are type members only, so they lie in
`DmsFrag`.  The program applies a Curry-style identity method to the stored
location `q`.  Its receiver is an object literal, so the term is outside
`TmFrag`. -/

namespace HonestCall

open Oopsla16.PackingCounterexample (S2 q G)

/-- Both witnesses of `TwoObjectStore.honest` are in the fragment: each is a
list of type members. -/
def frag : ∀ l, DmsFrag (TwoObjectStore.honest.at' l).defs
  | .here => .dcons .dty .dnil
  | .there .here => .dcons .dty (.dcons .dty .dnil)

/-- The identity's self type: `{0 : ⊤ → ⊤} ∧ ⊤`. -/
abbrev Tid : Ty S2 ([],x) := .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- The identity literal, Curry-style: `{ def 0(y) = y }`. -/
abbrev Did : Dms S2 ([],x) := .dcons (.dfun none none (.tvar (.abs .here))) .dnil

/-- The program: the identity invoked on `q`. -/
abbrev prog : Oopsla16.Tm S2 [] := .tapp (.tobj Did) 0 (.tvar (.conc q))

/-- The program is outside the fragment `Elaboration.elabHasType` handles:
its receiver is an object literal. -/
theorem not_frag : TmFrag prog → False := fun h => nomatch h

/-- The program is typed at `⊤` over the two-object store.  The receiver
forgets its self (`stp_bind1`), and `q` is typed by `T_Vary` through
honesty (`Store.Honest.vary`), then forgotten to `⊤`. -/
def progTy : HasType G Ctx.nil prog .TTop :=
  .T_App (T2 := .TTop)
    (.T_Sub (.T_Obj (.D_Fun (T11 := .TTop) (T12 := .TTop) .D_Nil (.T_Sub .T_Varz .stp_top)
      (Or.inl rfl) (Or.inl rfl)))
      (.stp_bind1 (.stp_and11 (.stp_fun .stp_top .stp_top))))
    (.T_Sub (TwoObjectStore.honest.vary q) .stp_top)

/-- **The program never gets stuck** on the source machine, started at the
two-object store, by `Oopsla16.oopsla16_safety_honest`. -/
theorem prog_safe {σ : Sig} {g : Grows S2 σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g G prog G' t') : ¬ SrcStuck G' t' :=
  Oopsla16.oopsla16_safety_honest TwoObjectStore.honest frag progTy run

/-- The source run: `ST_App1` allocates the identity, and `ST_AppAbs` returns
`q`, weakened past the new location.  Two steps, ending in an answer. -/
theorem prog_runs :
    ∃ (g : Grows S2 (S2,x)) (G' : Store (S2,x) (S2,x)),
      Oopsla16.Steps g G prog G' (.tvar (.conc (.there q))) :=
  ⟨_, _, .tail (.tail .refl (.ST_App1 .ST_Obj))
    (.ST_AppAbs (OT1 := none) (OT2 := none) (t12 := .tvar (.abs .here)) rfl)⟩

end HonestCall

end FCdotR.SourceSafety
