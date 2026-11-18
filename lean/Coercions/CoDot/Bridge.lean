import Coercions.CoDot.Admin
import Coercions.CoDot.Elab
import Coercions.DotMNF.Machine

/-!
# The bridge: safety of DOT-MNF from safety of the coercion calculus

The source is `DotMNF` (typing in `DotMNF/Typing.lean`, store machine in
`DotMNF/Machine.lean`), unchanged. Erasure deletes the coercions of a state:
in the running term, in the frames, and in the stored values. It keeps the
scope, the layout of the store and every location; the target allocates
exactly when the source does, so no renaming is involved.

Real steps erase to the same source step; administrative steps erase to no
step. Finality is preserved by erasure and reflected for states with no
administrative step. Source safety follows from target safety (`safety`),
administrative termination (`admin_normalizes`), elaboration and determinism
of the source machine. Neither FCdot nor a preservation proof for the source
typing is used.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Erasure of states -/

def Store.erase : Store s → DotMNF.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.erase v.erase

/-- Cast frames are deleted. -/
def Cont.erase : Cont s → DotMNF.Cont s
  | [] => .nil
  | .let u :: K => .cons (Cont.erase K) u.erase
  | .co _ :: K => Cont.erase K

/-- An elimination in focus erases to the elimination on the location of
its head. -/
def Run.erase : Run s → DotMNF.Tm s
  | .tm t => t.erase
  | .sel e a => .proj e.loc a
  | .app e z _ => .app e.loc z

def State.erase (st : State s) : DotMNF.State s :=
  ⟨st.σ.erase, Cont.erase st.K, st.t.erase⟩

/-! ## Helpers: erasure commutes with the syntax operations -/

mutual

theorem Tm.erase_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).erase = t.erase.rename ρ := by
  match t with
  | .ref x c => rfl
  | .val v c =>
    simp only [Tm.rename, Tm.erase, DotMNF.Tm.rename, Value.erase_rename v ρ]
  | .app x c y d => rfl
  | .proj x c a => rfl
  | .let t u =>
    simp only [Tm.rename, Tm.erase, DotMNF.Tm.rename,
      Tm.erase_rename t ρ, Tm.erase_rename u ρ.lift]
  | .cast t c => simp only [Tm.rename, Tm.erase, Tm.erase_rename t ρ]

theorem Value.erase_rename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    (v.rename ρ).erase = v.erase.rename ρ := by
  match v with
  | .obj d => simp only [Value.rename, Value.erase, DotMNF.Value.rename, Defs.erase_rename d ρ.lift]
  | .lam S t => simp only [Value.rename, Value.erase, DotMNF.Value.rename, Tm.erase_rename t ρ.lift]

theorem Defs.erase_rename {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2) :
    (d.rename ρ).erase = d.erase.rename ρ := by
  match d with
  | .typ A T => rfl
  | .trm a t => simp only [Defs.rename, Defs.erase, DotMNF.Defs.rename, Tm.erase_rename t ρ]
  | .and d1 d2 =>
    simp only [Defs.rename, Defs.erase, DotMNF.Defs.rename,
      Defs.erase_rename d1 ρ, Defs.erase_rename d2 ρ]

end

mutual

theorem Tm.erase_csubst {s1 s2 : Sig} (t : Tm s1) (σ : CoSub s1 s2) :
    (t.csubst σ).erase = t.erase.rename σ.ρ := by
  match t with
  | .ref x c => rfl
  | .val v c =>
    simp only [Tm.csubst, Tm.erase, DotMNF.Tm.rename, Value.erase_csubst v σ]
  | .app x c y d => rfl
  | .proj x c a => rfl
  | .let t u =>
    simp only [Tm.csubst, Tm.erase, DotMNF.Tm.rename,
      Tm.erase_csubst t σ, Tm.erase_csubst u σ.lift]
    rfl
  | .cast t c => simp only [Tm.csubst, Tm.erase, Tm.erase_csubst t σ]

theorem Value.erase_csubst {s1 s2 : Sig} (v : Value s1) (σ : CoSub s1 s2) :
    (v.csubst σ).erase = v.erase.rename σ.ρ := by
  match v with
  | .obj d =>
    simp only [Value.csubst, Value.erase, DotMNF.Value.rename, Defs.erase_csubst d σ.lift]
    rfl
  | .lam S t =>
    simp only [Value.csubst, Value.erase, DotMNF.Value.rename, Tm.erase_csubst t σ.lift]
    rfl

theorem Defs.erase_csubst {s1 s2 : Sig} (d : Defs s1) (σ : CoSub s1 s2) :
    (d.csubst σ).erase = d.erase.rename σ.ρ := by
  match d with
  | .typ A T => rfl
  | .trm a t => simp only [Defs.csubst, Defs.erase, DotMNF.Defs.rename, Tm.erase_csubst t σ]
  | .and d1 d2 =>
    simp only [Defs.csubst, Defs.erase, DotMNF.Defs.rename,
      Defs.erase_csubst d1 σ, Defs.erase_csubst d2 σ]

end

mutual

theorem dotTm_rename_id {s : Sig} (t : DotMNF.Tm s) : t.rename Rename.id = t := by
  match t with
  | .path p => simp only [DotMNF.Tm.rename, DotMNF.Path.rename_id]
  | .val v => simp only [DotMNF.Tm.rename, dotValue_rename_id v]
  | .app x y => rfl
  | .proj x a => rfl
  | .let t u =>
    simp only [DotMNF.Tm.rename, Rename.lift_id, dotTm_rename_id t, dotTm_rename_id u]

theorem dotValue_rename_id {s : Sig} (v : DotMNF.Value s) : v.rename Rename.id = v := by
  match v with
  | .obj d => simp only [DotMNF.Value.rename, Rename.lift_id, dotDefs_rename_id d]
  | .lam S t =>
    simp only [DotMNF.Value.rename, Rename.lift_id, DotMNF.Ty.rename_id, dotTm_rename_id t]

theorem dotDefs_rename_id {s : Sig} (d : DotMNF.Defs s) : d.rename Rename.id = d := by
  match d with
  | .typ A T => simp only [DotMNF.Defs.rename, DotMNF.Ty.rename_id]
  | .trm a t => simp only [DotMNF.Defs.rename, dotTm_rename_id t]
  | .and d1 d2 => simp only [DotMNF.Defs.rename, dotDefs_rename_id d1, dotDefs_rename_id d2]

end

theorem Store.erase_lookup (σ : Store s) (y : BVar s .var) :
    (σ.lookup y).erase = σ.erase.lookup y := by
  match σ, y with
  | .cons σ v, .here =>
    show (v.rename Rename.succ).erase = v.erase.rename Rename.succ
    exact Value.erase_rename v _
  | .cons σ v, .there y =>
    show ((σ.lookup y).rename Rename.succ).erase = (σ.erase.lookup y).rename Rename.succ
    rw [Value.erase_rename, Store.erase_lookup σ y]

theorem option_or_map {α β : Type} (f : α → β) (o o' : Option α) :
    (o.or o').map f = (o.map f).or (o'.map f) := by
  cases o <;> rfl

theorem Defs.erase_lookupTrm (d : Defs s) (a : Label) :
    (d.lookupTrm a).map Tm.erase = d.erase.lookupTrm a := by
  match d with
  | .typ _ _ => rfl
  | .trm b t =>
    simp only [Defs.lookupTrm, Defs.erase, DotMNF.Defs.lookupTrm]
    split <;> rfl
  | .and d1 d2 =>
    simp only [Defs.lookupTrm, Defs.erase, DotMNF.Defs.lookupTrm, option_or_map,
      Defs.erase_lookupTrm d1 a, Defs.erase_lookupTrm d2 a]

theorem Cont.erase_weaken (K : Cont s) :
    Cont.erase (Cont.weaken K) = (Cont.erase K).weaken := by
  induction K with
  | nil => rfl
  | cons f K ih =>
    cases f with
    | «let» u =>
      show DotMNF.Cont.cons (Cont.erase (Cont.weaken K)) (u.rename Rename.succ.lift).erase =
        DotMNF.Cont.cons ((Cont.erase K).rename Rename.succ) (u.erase.rename Rename.succ.lift)
      rw [Tm.erase_rename]
      exact congrArg (fun K' => DotMNF.Cont.cons K' _) ih
    | co c => exact ih

theorem Step.loc_eq {D : BVar s .var → Label → Prop} {e e' : Ev s} (h : Step D e e') :
    e'.loc = e.loc := by
  induction h <;> first | rfl | assumption

/-- A final DOT-MNF state takes no step. -/
theorem dot_final_no_step {st : DotMNF.State s} {st' : DotMNF.State s'} (hf : st.Final)
    (hs : DotMNF.Step st st') : False := by
  obtain ⟨hK, ⟨v, hv⟩ | ⟨p, hp⟩⟩ := hf <;> cases hs <;> simp_all

/-! ## Simulation -/

/-- A real step erases to a step of the DOT-MNF machine. -/
theorem RStep.erase {st : State s} {st' : State s'} (h : RStep st st') :
    DotMNF.Step st.erase st'.erase := by
  cases h with
  | @letPush σ K t u => exact .let
  | @alloc σ u K v c =>
    show DotMNF.Step ⟨σ.erase, .cons (Cont.erase K) u.erase, .val v.erase⟩
      ⟨.cons σ.erase v.erase, Cont.erase (Cont.weaken K), (u.csubst (CoSub.narrow c.weaken)).erase⟩
    rw [Cont.erase_weaken, Tm.erase_csubst]
    show DotMNF.Step _ ⟨_, _, u.erase.rename Rename.id⟩
    rw [dotTm_rename_id]
    exact .alloc
  | @letRef σ u K y c =>
    show DotMNF.Step ⟨σ.erase, .cons (Cont.erase K) u.erase, .path (.var y)⟩
      ⟨σ.erase, Cont.erase K, (u.csubst (CoSub.inst y c)).erase⟩
    rw [Tm.erase_csubst]
    exact .rename
  | @beta σ K f z e S t hl =>
    show DotMNF.Step ⟨σ.erase, Cont.erase K, .app f z⟩
      ⟨σ.erase, Cont.erase K, (t.csubst (CoSub.inst z e)).erase⟩
    rw [Tm.erase_csubst]
    have : σ.erase.lookup f = .lam S t.erase := by rw [← Store.erase_lookup, hl]; rfl
    exact .app this
  | @select t σ K y a d hl ht =>
    show DotMNF.Step ⟨σ.erase, Cont.erase K, .proj y a⟩
      ⟨σ.erase, Cont.erase K, (t.csubst (CoSub.inst y .id)).erase⟩
    rw [Tm.erase_csubst]
    have h1 : σ.erase.lookup y = .obj d.erase := by rw [← Store.erase_lookup, hl]; rfl
    have h2 : d.erase.lookupTrm a = some t.erase := by rw [← Defs.erase_lookupTrm, ht]; rfl
    exact .proj h1 h2

/-- An administrative step does not change the erasure. -/
theorem AStep.erase {st st' : State s} (h : AStep st st') : st'.erase = st.erase := by
  cases h with
  | @evSel e e' σ K a hs =>
    show (⟨σ.erase, Cont.erase K, .proj e'.loc a⟩ : DotMNF.State s) = ⟨σ.erase, Cont.erase K, .proj e.loc a⟩
    rw [hs.loc_eq]
  | @evApp e e' σ K z d hs =>
    show (⟨σ.erase, Cont.erase K, .app e'.loc z⟩ : DotMNF.State s) = ⟨σ.erase, Cont.erase K, .app e.loc z⟩
    rw [hs.loc_eq]
  | _ => rfl

/-- Finality is preserved by erasure. -/
theorem State.Final.erase {st : State s} (h : st.Final) : st.erase.Final := by
  obtain ⟨σ, K, r⟩ := st
  obtain ⟨hK, ⟨y, c, hr⟩ | ⟨v, c, hr⟩⟩ := h
  · cases hK; cases hr; exact ⟨rfl, .inr ⟨.var y, rfl⟩⟩
  · cases hK; cases hr; exact ⟨rfl, .inl ⟨v.erase, rfl⟩⟩

/-- Finality is reflected for states with no administrative step. (It is not
reflected in general: `⟨σ, [co id], x ▷ c⟩` is not final and erases to a final
state.) -/
theorem State.final_of_erase {st : State s} (hn : ∀ st', ¬ AStep st st')
    (h : st.erase.Final) : st.Final := by
  obtain ⟨σ, K, r⟩ := st
  obtain ⟨hK, hr⟩ := h
  have hK' : Cont.erase K = .nil := hK
  have hr' : (∃ v, r.erase = .val v) ∨ (∃ p, r.erase = .path p) := hr
  cases r with
  | tm t =>
    cases t with
    | ref y c =>
      cases K with
      | nil => exact ⟨rfl, .inl ⟨y, c, rfl⟩⟩
      | cons f K =>
        cases f with
        | «let» u => cases hK'
        | co c' => exact absurd .coRef (hn _)
    | val v c =>
      cases K with
      | nil => exact ⟨rfl, .inr ⟨v, c, rfl⟩⟩
      | cons f K =>
        cases f with
        | «let» u => cases hK'
        | co c' => exact absurd .coVal (hn _)
    | cast t c => exact absurd .castPush (hn _)
    | app => rcases hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    | proj => rcases hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    | «let» => rcases hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  | sel => rcases hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  | app => rcases hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-- The DOT-MNF machine is deterministic. -/
theorem dot_step_det {st : DotMNF.State s} {st1 : DotMNF.State s1} {st2 : DotMNF.State s2}
    (h1 : DotMNF.Step st st1) (h2 : DotMNF.Step st st2) :
    (⟨s1, st1⟩ : (s : Sig) × DotMNF.State s) = ⟨s2, st2⟩ := by
  cases h1 with
  | «let» => cases h2; rfl
  | alloc => cases h2; rfl
  | rename => cases h2; rfl
  | app hl =>
    cases h2 with
    | app hl' => rw [hl] at hl'; cases hl'; rfl
  | proj hl ht =>
    cases h2 with
    | proj hl' ht' => rw [hl] at hl'; cases hl'; rw [ht] at ht'; cases ht'; rfl

/-! ## Administrative normalization of a well-typed state -/

theorem ASteps.facts {A : Ty []} {st st' : State s} (h : ASteps st st') :
    MSteps st st' ∧ st'.erase = st.erase ∧ (st.Ok A → st'.Ok A) := by
  induction h with
  | refl => exact ⟨.refl, rfl, id⟩
  | tail _ ha ih =>
    obtain ⟨hm, he, hok⟩ := ih
    exact ⟨.tail hm ha.toMStep, by rw [ha.erase, he], fun h => (hok h).step ha.toMStep⟩

/-- A well-typed state reaches, by administrative steps, a well-typed state
with the same erasure that is final or takes a real step. -/
theorem normalize {A : Ty []} {cst : State s} (hok : cst.Ok A) :
    ∃ cst' : State s, MSteps cst cst' ∧ cst'.Ok A ∧ cst'.erase = cst.erase ∧
      (cst'.Final ∨ ∃ (s' : Sig) (st' : State s'), RStep cst' st') := by
  obtain ⟨cst', hrun, hnf⟩ := admin_normalizes cst
  obtain ⟨hm, he, hok'⟩ := hrun.facts (A := A)
  have hok' := hok' hok
  refine ⟨cst', hm, hok', he, ?_⟩
  rcases hok'.progress with hf | ⟨s', st', hs⟩
  · exact .inl hf
  · rcases hs.split with hr | ⟨_, ha⟩
    · exact .inr ⟨s', st', hr⟩
    · exact absurd ha (hnf _)

/-! ## Execution lifting and source safety -/

/-- Execution lifting: a source step from the erasure of a well-typed target
state is matched by a target run (administrative steps, then one real step)
to a well-typed state that erases to the source successor. -/
theorem lift_step {A : Ty []} {cst : State s} (hok : cst.Ok A)
    {st1 : DotMNF.State s1} (hs : DotMNF.Step cst.erase st1) :
    ∃ cst1 : State s1, MSteps cst cst1 ∧ cst1.Ok A ∧ cst1.erase = st1 := by
  obtain ⟨cst', hm, hok', he, hf | ⟨s'', cst'', hr⟩⟩ := normalize hok
  · exact (dot_final_no_step (he ▸ hf.erase) hs).elim
  · have h2 := hr.erase
    rw [he] at h2
    have hdet := dot_step_det hs h2
    cases hdet
    exact ⟨cst'', .tail hm hr.toMStep, hok'.step hr.toMStep, rfl⟩

/-- A well-typed target state whose erasure is `st`: the source state is
final or takes a step. -/
theorem erase_not_stuck {A : Ty []} {cst : State s} (hok : cst.Ok A) :
    cst.erase.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step cst.erase st' := by
  obtain ⟨cst', _, _, he, hf | ⟨s'', cst'', hr⟩⟩ := normalize hok
  · exact .inl (he ▸ hf.erase)
  · exact .inr ⟨s'', _, he ▸ hr.erase⟩

/-- Generalized reachability. -/
theorem source_reach_aux {A : Ty []} {st0 : DotMNF.State s0} {st : DotMNF.State s}
    (hs : DotMNF.Steps st0 st) (h0 : ∃ cst : State s0, cst.Ok A ∧ cst.erase = st0) :
    ∃ cst : State s, cst.Ok A ∧ cst.erase = st := by
  induction hs with
  | refl => exact h0
  | tail _ h2 ih =>
    obtain ⟨cst, hok, he⟩ := ih h0
    subst he
    obtain ⟨cst1, _, hok1, he1⟩ := lift_step hok h2
    exact ⟨cst1, hok1, he1⟩

theorem ofDot_nil : ofDot .nil = Ctx.nil := by
  unfold ofDot Ctx.nil
  congr 1
  funext x
  nomatch x

/-- Every source state reachable from a closed typed DOT-MNF program is the
erasure of a well-typed target state. -/
theorem source_reach {t : DotMNF.Tm []} {T : Ty []} (h : DotMNF.HasTy .nil t T)
    {st : DotMNF.State s} (hs : DotMNF.Steps (⟨.nil, .nil, t⟩ : DotMNF.State []) st) :
    ∃ cst : State s, cst.Ok T ∧ cst.erase = st := by
  refine source_reach_aux hs ?_
  obtain ⟨t', ht, he⟩ := elaboration h
  rw [ofDot_nil] at ht
  refine ⟨⟨.nil, [], .tm t'⟩, State.Ok.init ht, ?_⟩
  show (⟨.nil, .nil, t'.erase⟩ : DotMNF.State []) = _
  rw [he]

/-- Safety of DOT-MNF: no state reachable from a closed well-typed program is
stuck. The hypothesis is the repository's typing judgment, with subsumption,
unrestricted intersections, recursive types on variables, and no condition on
contexts or bounds. -/
theorem source_safety {t : DotMNF.Tm []} {T : Ty []} (h : DotMNF.HasTy .nil t T)
    {st : DotMNF.State s} (hs : DotMNF.Steps (⟨.nil, .nil, t⟩ : DotMNF.State []) st) :
    ¬ st.Stuck := by
  obtain ⟨cst, hok, he⟩ := source_reach h hs
  subst he
  intro ⟨hnf, hns⟩
  rcases erase_not_stuck hok with hf | hst
  · exact hnf hf
  · exact hns hst

end CoDot
