import Coercions.FCdotR.SourceSafety

/-!
# The WadlerFest deliverables, for `Oopsla16 → FCdotR`

The WadlerFest line (`DotToFCdot`, `FCdot`) proves a fixed list of results.
Most of them already have a counterpart in this line; the table in `STATUS.md`
(*WadlerFest deliverables*) gives each one's Lean name.  This module adds the
counterparts that were missing and follow directly from what exists.  None of
them takes a hypothesis.

## What is here

* **Consistency along runs of a typed program** (the counterpart of
  `FCdot.reachable_consistent` and `DotMNF.reachable_consistent`).
  `reachable_consistent`: every machine state reached from a closed typed
  FCdotR term is typed over an honest machine store, and that store proves no
  closed `⊤ ≤ ⊥`.  `elab_reachable_consistent` is the same for the
  elaboration of a closed `Oopsla16` typing.
* **Stored type members are recorded** (the counterpart of
  `DotMNF.reachable_realized`).  `reachable_realized`: along the same runs,
  a location stores the type member `a = TX` exactly when its recorded type
  has the member `{a : TX..TX}`.
* **Every reachable source configuration is related to a typed target
  state.**  `Oopsla16.reachable_simulated` and `Oopsla16.reachable_related`.
  The second one also says that the target state is reached by running the
  elaboration, at the same allocation index, and that its store is
  consistent.
* **`Oopsla16`'s subtyping is consistent over every store.**
  `Oopsla16.stp_consistent`: no source store, reachable or not, derives
  `⊤ <: ⊥` in the empty context.  `closedStp_nf`: every closed source
  subtyping has a normal form.  The WadlerFest line has no source-side
  statement of this kind.
* **Coherence** (the counterpart of `DotMNF.coherence`).  Two elaborations of
  the same source term need not erase to the same term: `T_App` and
  `T_AppVar` bind different operands, and a Curry-style method gets the types
  its typing chose.  What holds instead is that they compute the same thing.
  `Corr.coherent`: every final state one of them reaches is matched by a
  final state of the other, at the same allocation index, with the same
  answer location, and with both stores matching one source store.
  `Corr.final_iff`: one reaches a final state exactly when the other does.
  `elab_coherence` and `elab_final_iff` are these at two elaborations.
* **Canonical forms over a machine store.**  `MachineStore.Honest.nf`: every
  closed inclusion over an honest machine store has a normal form.  It is
  `Inversion`'s normalizer at `MachineStore.Honest.recordedLit`.

## Why the source's subtyping is consistent over every store

`Inversion`'s consistency argument (`RecordedLit.consistency`) needs a store
typing that records, at each location, a literal type of what is stored there.
The source has no store typing, and source subtyping never reads one; any
store typing will do for elaborating it (`Elaboration.elabStp`).  So for each
source store the argument is run at the store typing that records each stored
type member exactly and each method at `⊤ → ⊤` (`litStoreTy`).  This is also
why the target needs honest stores and the source does not: the target's
`vcLoc` reads the store typing, and a store typing with bad bounds makes
`⊤ ≤ ⊥` derivable (`CanonicalForms.DishonestStore.topLeBot`).
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Grows HasType Stp)

/-! ## A store typing for every source store

`Inversion`'s normalizer asks one thing of a store and a store typing: that the
store typing records, at every location, a *literal type* of what the location
holds (`RecordedLit`).  Every source store has such a store typing:
`litStoreTy` records each type member exactly, at its position, and each method
at `⊤ → ⊤`.  Source subtyping never reads a store typing, so over every source
store the normalizer applies to every elaborated closed source subtyping. -/

/-- **The literal type of a closed definition list**: `⊤` for the empty list;
otherwise the head member, at its position, intersected with the literal type
of the rest.  A type member is recorded exactly, `{a : T..T}`, and a method at
`⊤ → ⊤`. -/
def litTypeOf {σ : Sig} : Dms σ [] → Ty σ []
  | .dnil => .TTop
  | .dcons (.dty T) ds => .TAnd (.TTyp ds.length T T) (litTypeOf ds)
  | .dcons (.dfun _ _ _) ds => .TAnd (.TFun ds.length .TTop .TTop) (litTypeOf ds)

/-- A literal type stays a literal type under a lookup that finds at least the
same type members.  Method members are recorded by their type only, so the
lookup is not asked about them. -/
def LitTy.mono {σ : Sig} {g g' : Lb → Option (Dm σ [])}
    (hg : ∀ {a : Lb} {TX : Ty σ []}, g a = some (.dty TX) → g' a = some (.dty TX)) :
    {B : Ty σ []} → LitTy g B → LitTy g' B
  | _, .top => .top
  | _, .typ h rest => .typ (hg h) (LitTy.mono hg rest)
  | _, .fn rest => .fn (LitTy.mono hg rest)

/-- A type member of the tail of a list is found at the same label in the whole
list: labels are positions, and the tail's labels are below the head's. -/
theorem Dms.get?_dcons_of_dty {σ : Sig} (d0 : Dm σ []) (ds : Dms σ []) {a : Lb}
    {TX : Ty σ []} (h : ds.get? a = some (.dty TX)) :
    (Oopsla16.Dms.dcons d0 ds).get? a = some (.dty TX) := by
  show (if a = ds.length then some d0 else ds.get? a) = some (.dty TX)
  rw [if_neg (Nat.ne_of_lt (dmsTyp_label_lt ds h))]
  exact h

/-- **The literal type of a list is a literal type** relative to the list's
own member lookup. -/
def litTypeOf_litTy {σ : Sig} : (ds : Dms σ []) → LitTy ds.get? (litTypeOf ds)
  | .dnil => by
      rw [litTypeOf]
      exact .top
  | .dcons (.dty T) ds => by
      have hd : (Oopsla16.Dms.dcons (.dty T) ds).get? ds.length = some (.dty T) := by
        show (if ds.length = ds.length then _ else _) = _
        rw [if_pos rfl]
      rw [litTypeOf]
      exact LitTy.typ hd (LitTy.mono (g' := (Oopsla16.Dms.dcons (.dty T) ds).get?)
        (fun h => Dms.get?_dcons_of_dty _ ds h) (litTypeOf_litTy ds))
  | .dcons (.dfun o1 o2 t) ds => by
      rw [litTypeOf]
      exact LitTy.fn (LitTy.mono (g' := (Oopsla16.Dms.dcons (.dfun o1 o2 t) ds).get?)
        (fun h => Dms.get?_dcons_of_dty _ ds h) (litTypeOf_litTy ds))

/-- **The literal store typing of a source store**: at every location, the
literal type of what the location holds, weakened under the unused self. -/
def litStoreTy {σ : Sig} (G : Store σ σ) : StoreTy σ :=
  fun l => (litTypeOf (G.lookup l)).weaken

/-- **Every source store records literal types at its literal store
typing.**  So `Inversion`'s normalizer and consistency argument apply over every
source store. -/
def litStoreTy_recordedLit {σ : Sig} (G : Store σ σ) : RecordedLit G (litStoreTy G) :=
  fun l => by
    show LitTy _ ((litTypeOf (G.lookup l)).weaken.substVr (.conc l))
    rw [Oopsla16.Ty.substVr_weaken]
    exact litTypeOf_litTy _

/-- **Every closed source subtyping has a normal form**, over every store: its
elaboration (`Elaboration.elabStp`) at the literal store typing is normalized
by `Inversion.RecordedLit.nf`.  This is canonical forms of closed evidence, for
`Oopsla16`'s own subtyping. -/
def closedStp_nf {σ : Sig} {G : Store σ σ} {S T : Ty σ []} (h : Stp G Ctx.nil S T) :
    LeNf G (litStoreTy G) S T :=
  (litStoreTy_recordedLit G).nf (elabStp (litStoreTy G) h).2

/-! ## Canonical forms over a machine store -/

/-- **Every closed inclusion over an honest machine store has a normal
form**: `Inversion.RecordedLit.nf` at `MachineStore.Honest.recordedLit`.  It is
the counterpart of FCdot's canonical forms of closed evidence, at the store
the machine runs over. -/
def MachineStore.Honest.nf {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) {e : Le σ []} {S T : Ty σ []}
    (d : LeTy G.erase W .nil e S T) : LeNf G.erase W S T :=
  h.recordedLit.nf d

/-- **An honest machine store is consistent**: no closed evidence over it
includes `⊤` in `⊥`. -/
theorem MachineStore.Honest.consistent {σ : Sig} {G : MachineStore σ σ}
    {W : StoreTy σ} (h : MachineStore.Honest G W) :
    ¬ ∃ e : Le σ [], Nonempty (LeTy G.erase W .nil e .TTop .TBot) :=
  fun ⟨_, ⟨he⟩⟩ => h.recordedLit.consistency he

/-- **An honest machine store's type members are what its store typing
records.**  A location stores the type member `a = TX` exactly when its
recorded type has the member `{a : TX..TX}`.  Left to right is
`MachineStore.Honest.member`; right to left reads the member off the typed
witness, which has the stored list's skeleton. -/
theorem MachineStore.Honest.realized {σ : Sig} {G : MachineStore σ σ}
    {W : StoreTy σ} (h : MachineStore.Honest G W) (l : BVar σ .var) (a : Lb)
    (TX : Ty σ []) :
    (G.erase.lookup l).get? a = some (.dty TX) ↔
      Nonempty (Conjunct (tyOf W l) (.TTyp a TX TX)) := by
  constructor
  · intro hg
    exact ⟨h.member l hg⟩
  · rintro ⟨c⟩
    rw [← MachineStore.erase_lookup, ← Defs.erase_of_skel (h.at' l).skel]
    exact defsTy_erase_of_conjunct (h.at' l).typed c

/-! ## Consistency along runs of a typed program -/

/-- **Every store a closed typed program reaches is consistent.**  Along any
run of the FCdotR machine from a closed term typed over the empty store, the
state is typed at the program's type (moved along the allocations) over an
honest machine store, and that store proves no closed `⊤ ≤ ⊥`.  The
counterpart of `FCdot.reachable_consistent`.  No hypothesis. -/
theorem reachable_consistent {W : StoreTy []} {d : Tm [] []} {T : Ty [] []}
    (hd : TmTy Store.nil W Ctx.nil d T) {σ : Sig} {g : Grows [] σ} {st : State σ}
    (run : Steps g ⟨MachineStore.nil, .nil, d⟩ st) :
    ∃ W' : StoreTy σ,
      Nonempty (MachineStore.Honest st.G W' × StateTy st W' (Ty.alongGrows g T)) ∧
        ¬ ∃ e : Le σ [], Nonempty (LeTy st.G.erase W' .nil e .TTop .TBot) := by
  obtain ⟨W', ⟨hH, hT⟩⟩ := preservation_init' hd run
  exact ⟨W', ⟨hH, hT⟩, hH.consistent⟩

/-- **Every store a closed typed program reaches records its type members.**
Along the same runs as `reachable_consistent`, some honest store typing of the
reached store has, at every location, exactly the stored type members as
members of the recorded type.  The counterpart of `DotMNF.reachable_realized`,
whose block names are defined by the stored witnesses.  No hypothesis. -/
theorem reachable_realized {W : StoreTy []} {d : Tm [] []} {T : Ty [] []}
    (hd : TmTy Store.nil W Ctx.nil d T) {σ : Sig} {g : Grows [] σ} {st : State σ}
    (run : Steps g ⟨MachineStore.nil, .nil, d⟩ st) :
    ∃ W' : StoreTy σ, Nonempty (MachineStore.Honest st.G W') ∧
      ∀ (l : BVar σ .var) (a : Lb) (TX : Ty σ []),
        (st.G.erase.lookup l).get? a = some (.dty TX) ↔
          Nonempty (Conjunct (tyOf W' l) (.TTyp a TX TX)) := by
  obtain ⟨W', ⟨hH, _⟩⟩ := preservation_init' hd run
  exact ⟨W', ⟨hH⟩, hH.realized⟩

/-- **Every store the elaboration of a closed source typing reaches is
consistent.**  `reachable_consistent` at `ElaborationFull.elabTm`, for any store
typing the elaboration is carried out at.  The counterpart of
`DotMNF.reachable_consistent`.  No hypothesis. -/
theorem elab_reachable_consistent {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) (W : StoreTy []) {σ : Sig} {g : Grows [] σ}
    {st : State σ} (run : Steps g ⟨MachineStore.nil, .nil, (elabTm W ht).tm⟩ st) :
    ∃ W' : StoreTy σ,
      Nonempty (MachineStore.Honest st.G W' × StateTy st W' (Ty.alongGrows g T)) ∧
        ¬ ∃ e : Le σ [], Nonempty (LeTy st.G.erase W' .nil e .TTop .TBot) :=
  reachable_consistent (elabTm W ht).typed run

/-- **Every store the elaboration of a closed source typing reaches records its
type members**: `reachable_realized` at `ElaborationFull.elabTm`.  The
counterpart of `DotMNF.reachable_realized`.  No hypothesis. -/
theorem elab_reachable_realized {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) (W : StoreTy []) {σ : Sig} {g : Grows [] σ}
    {st : State σ} (run : Steps g ⟨MachineStore.nil, .nil, (elabTm W ht).tm⟩ st) :
    ∃ W' : StoreTy σ, Nonempty (MachineStore.Honest st.G W') ∧
      ∀ (l : BVar σ .var) (a : Lb) (TX : Ty σ []),
        (st.G.erase.lookup l).get? a = some (.dty TX) ↔
          Nonempty (Conjunct (tyOf W' l) (.TTyp a TX TX)) :=
  reachable_realized (elabTm W ht).typed run

/-! ## Coherence -/

/-- **Two terms that correspond to the same closed source term give the same
answers.**  Every final state the first reaches is matched by a final state
the second reaches, at the same allocation index.  The two final states answer
with the same location, and their stores both correspond to one source store.
No typing is needed: the source run in the middle is what ties them together
(`Rel.final_run`, then `Rel.answer_run`). -/
theorem Corr.coherent {t : Oopsla16.Tm [] []} {d1 d2 : Tm [] []} (h1 : Corr t d1)
    (h2 : Corr t d2) {σ : Sig} {g : Grows [] σ} {st1 : State σ}
    (run : Steps g ⟨MachineStore.nil, .nil, d1⟩ st1) (hf : st1.Final) :
    ∃ (G' : Store σ σ) (st2 : State σ),
      Steps g ⟨MachineStore.nil, .nil, d2⟩ st2 ∧ st2.Final ∧
        StoreCorr G' st1.G ∧ StoreCorr G' st2.G ∧
        ∃ a1 a2 : Atom σ [], st1.t = .atom a1 ∧ st2.t = .atom a2 ∧ a1.root = a2.root := by
  obtain ⟨G', t', srun, ha, hr1⟩ := (Rel.init h1).final_run run hf
  obtain ⟨st2, run2, hf2, hr2⟩ := (Rel.init h2).answer_run srun ha
  obtain ⟨a1, e1, ht1⟩ := hr1.final_tm hf
  obtain ⟨a2, e2, ht2⟩ := hr2.final_tm hf2
  rw [ht1] at ht2
  exact ⟨G', st2, run2, hf2, hr1.store, hr2.store, a1, a2, e1, e2,
    Oopsla16.Tm.tvar.inj ht2⟩

/-- **Two terms that correspond to the same closed source term reach a final
state together**: `Rel.answer_iff_final` twice.  No typing is needed. -/
theorem Corr.final_iff {t : Oopsla16.Tm [] []} {d1 d2 : Tm [] []} (h1 : Corr t d1)
    (h2 : Corr t d2) :
    (∃ (σ : Sig) (g : Grows [] σ) (st : State σ),
        Steps g ⟨MachineStore.nil, .nil, d1⟩ st ∧ st.Final) ↔
      (∃ (σ : Sig) (g : Grows [] σ) (st : State σ),
        Steps g ⟨MachineStore.nil, .nil, d2⟩ st ∧ st.Final) :=
  (Rel.init h1).answer_iff_final.symm.trans (Rel.init h2).answer_iff_final

/-- **Coherence of the elaboration.**  Two typings of the same closed source
term, elaborated at any two store typings, give target programs with the same
answers, in the sense of `Corr.coherent`.  The WadlerFest statement
`DotMNF.coherence` (equal erasures) does not hold here: `T_App` and
`T_AppVar` A-normalise differently, and a Curry-style method is elaborated at
the types its typing chose.  No hypothesis. -/
theorem elab_coherence {t : Oopsla16.Tm [] []} {T1 T2 : Ty [] []}
    (ht1 : HasType Store.nil Ctx.nil t T1) (ht2 : HasType Store.nil Ctx.nil t T2)
    (W1 W2 : StoreTy []) {σ : Sig} {g : Grows [] σ} {st1 : State σ}
    (run : Steps g ⟨MachineStore.nil, .nil, (elabTm W1 ht1).tm⟩ st1) (hf : st1.Final) :
    ∃ (G' : Store σ σ) (st2 : State σ),
      Steps g ⟨MachineStore.nil, .nil, (elabTm W2 ht2).tm⟩ st2 ∧ st2.Final ∧
        StoreCorr G' st1.G ∧ StoreCorr G' st2.G ∧
        ∃ a1 a2 : Atom σ [], st1.t = .atom a1 ∧ st2.t = .atom a2 ∧ a1.root = a2.root :=
  Corr.coherent (elabTm W1 ht1).corr (elabTm W2 ht2).corr run hf

/-- **Two elaborations of the same closed source term reach a final state
together**: `Corr.final_iff` at two elaborations.  No hypothesis. -/
theorem elab_final_iff {t : Oopsla16.Tm [] []} {T1 T2 : Ty [] []}
    (ht1 : HasType Store.nil Ctx.nil t T1) (ht2 : HasType Store.nil Ctx.nil t T2)
    (W1 W2 : StoreTy []) :
    (∃ (σ : Sig) (g : Grows [] σ) (st : State σ),
        Steps g ⟨MachineStore.nil, .nil, (elabTm W1 ht1).tm⟩ st ∧ st.Final) ↔
      (∃ (σ : Sig) (g : Grows [] σ) (st : State σ),
        Steps g ⟨MachineStore.nil, .nil, (elabTm W2 ht2).tm⟩ st ∧ st.Final) :=
  Corr.final_iff (elabTm W1 ht1).corr (elabTm W2 ht2).corr

end FCdotR

/-! ## Reachable source configurations

In the source's namespace, next to `Oopsla16.oopsla16_safety`. -/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-- **Every configuration a closed typed program reaches is simulated**: some
typed target state over an honest machine store is related to it.
`FCdotR.Simulated.init` carried along the run by `FCdotR.Simulated.steps`.
No hypothesis. -/
theorem reachable_simulated {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') : FCdotR.Simulated G' t' :=
  (FCdotR.Simulated.init ht).steps run

/-- **Every configuration a closed typed program reaches is related to a
typed target state that the elaboration reaches.**  Elaborate the typing at
any store typing `W`.  For every source run, the target machine run from the
elaboration reaches, at the same allocation index, a state that is

* related to the source configuration (`FCdotR.Rel`: the stores correspond and
  the source term is what the state computes),
* typed at the program's type, moved along the allocations, over an honest
  machine store, and
* consistent: that store proves no closed `⊤ ≤ ⊥`.

The forward simulation (`FCdotR.Rel.steps'`) gives the state, preservation
(`FCdotR.preservation_init'`) types it, and `Inversion`'s consistency argument
refutes `⊤ ≤ ⊥`.  No hypothesis. -/
theorem reachable_related {t : Tm [] []} {T : Ty [] []} (ht : HasType Store.nil Ctx.nil t T)
    (W : FCdotR.StoreTy []) {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Tm σ []}
    (run : Steps g Store.nil t G' t') :
    ∃ st : FCdotR.State σ,
      FCdotR.Steps g ⟨FCdotR.MachineStore.nil, .nil, (FCdotR.elabTm W ht).tm⟩ st ∧
        FCdotR.Rel G' t' st ∧
        ∃ W' : FCdotR.StoreTy σ,
          Nonempty (FCdotR.MachineStore.Honest st.G W' ×
            FCdotR.StateTy st W' (FCdotR.Ty.alongGrows g T)) ∧
          ¬ ∃ e : FCdotR.Le σ [], Nonempty (FCdotR.LeTy st.G.erase W' .nil e .TTop .TBot) := by
  obtain ⟨st, trun, hr⟩ := (FCdotR.Rel.init (FCdotR.elabTm W ht).corr).steps' run
  obtain ⟨W', hW, hcons⟩ := FCdotR.elab_reachable_consistent ht W trun
  exact ⟨st, trun, hr, W', hW, hcons⟩

/-- **`Oopsla16`'s subtyping is consistent over every store**: no store,
reachable or not, derives `⊤ <: ⊥` in the empty context.  The statement
mentions only `Oopsla16`.  A derivation would elaborate, at the literal store
typing `FCdotR.litStoreTy`, to closed target evidence of `⊤ ≤ ⊥`, which
`FCdotR.RecordedLit.consistency` refutes.  No hypothesis. -/
theorem stp_consistent {σ : Sig} (G : Store σ σ) : ¬ Nonempty (Stp G Ctx.nil .TTop .TBot) :=
  fun ⟨h⟩ => (FCdotR.litStoreTy_recordedLit G).consistency
    (FCdotR.elabStp (FCdotR.litStoreTy G) h).2

end Oopsla16

/-! ## Worked instance -/

namespace FCdotR.Deliverables

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Ty Store Grows Ctx)

/-- Every configuration the recursive-argument program
`SourceSafety.RecursiveArg.prog` reaches is related to a typed target state
reached by its elaboration. -/
example {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g Store.nil SourceSafety.RecursiveArg.prog G' t') :
    ∃ st : State σ,
      Steps g ⟨MachineStore.nil, .nil, (elabTm emptyStoreTy SourceSafety.RecursiveArg.progTy).tm⟩
        st ∧ Rel G' t' st :=
  match Oopsla16.reachable_related SourceSafety.RecursiveArg.progTy emptyStoreTy run with
  | ⟨st, trun, hr, _⟩ => ⟨st, trun, hr⟩

end FCdotR.Deliverables
