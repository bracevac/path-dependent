import Coercions.Oopsla16.Frontend.Surface
import Coercions.FCdotR.SourceSafety

/-!
# The source machine as a function

Oopsla16 gives its reduction as a relation, `Oopsla16.Step`: a substitution
machine with congruence rules over a store that only grows.  This module gives
the same machine as a function, so that a program of Oopsla16 runs.

No rule needs a search or a fuel.  The only side condition is a member lookup
in a stored object, which is total.  So `step?` is structural and reduces in
the kernel.

A step may allocate, which extends the store's signature.  So `step?` returns
a `Next`: the new signature, the growth that leads to it, the new store and the
new term.  The term of a configuration lives at the empty local scope `[]`.
Recursion at the fixed index `[]` is not structural, so `stepS` recurses at a
variable index `s` and carries the equation `s = []`.  `noAbs` closes the cases
that would name a bound variable.

Proved:
* `step?` finds a step exactly when the relation has one (`step?_sound`,
  `step?_complete`), and that step is the only one (`step_det`).
* A configuration with no step is an answer or stuck in the sense of
  `FCdotR.SrcStuck`, without classical reasoning.
* The result of the driver `run` is reachable, and every reachable
  configuration is the result of `run` at some number of steps.
-/

namespace Oopsla16Frontend

open FCdot (Sig BVar)
open Oopsla16 (Tm Dms Dm Store Grows Step Steps)

/-! ## One step -/

/-- The result of one step from a store over the signature `σ`: the
signature after the step, how it grew, the store and the term. -/
structure Next (σ : Sig) where
  /-- The signature after the step. -/
  σ' : Sig
  /-- The allocation the step performed. -/
  g : Grows σ σ'
  /-- The store after the step. -/
  G' : Store σ' σ'
  /-- The term after the step. -/
  t' : Tm σ' []

/-- The empty local scope has no variable.  This closes the cases of `stepS`
that would name one. -/
def noAbs {s : Sig} {α : Sort _} (h : s = []) (z : BVar s .var) : α :=
  False.elim (by subst h; exact nomatch z)

/-- One step of `Oopsla16.Step`, at a local scope `s` that the equation says
is empty.

A literal allocates (`ST_Obj`).  A call on two locations looks the method up
in the stored object and substitutes the argument into its body (`ST_AppAbs`).
A call on a location reduces its argument (`ST_App2`).  Any other call reduces
its receiver (`ST_App1`).  A location does not step, and neither does a call
to a member the object lacks or to a type member. -/
def stepS {σ : Sig} (G : Store σ σ) : {s : Sig} → Tm σ s → s = [] → Option (Next σ)
  | _, .tvar _, _ => none
  | _, .tobj D, h => some ⟨_, .snoc .refl,
      G.weakenStore.cons ((h ▸ D : Dms σ ([],x)).weakenStore.substVr (.conc .here)),
      .tvar (.conc .here)⟩
  | _, .tapp (.tvar (.conc f)) l (.tvar (.conc y)), _ =>
      match (G.lookup f).get? l with
      | some (.dfun _ _ t12) => some ⟨σ, .refl, G, t12.substVr (.conc y)⟩
      | _ => none
  | _, .tapp (.tvar (.conc _)) _ (.tvar (.abs z)), h => noAbs h z
  | _, .tapp (.tvar (.conc f)) l (.tobj D), h => (stepS G (.tobj D) h).map fun n =>
      ⟨n.σ', n.g, n.G', .tapp (.tvar (.conc (n.g.rename.var f))) l n.t'⟩
  | _, .tapp (.tvar (.conc f)) l (.tapp u1 l' u2), h => (stepS G (.tapp u1 l' u2) h).map fun n =>
      ⟨n.σ', n.g, n.G', .tapp (.tvar (.conc (n.g.rename.var f))) l n.t'⟩
  | _, .tapp (.tvar (.abs z)) _ _, h => noAbs h z
  | _, .tapp (.tobj D) l t2, h => (stepS G (.tobj D) h).map fun n =>
      ⟨n.σ', n.g, n.G', .tapp n.t' l ((h ▸ t2 : Tm σ []).renameStore n.g.rename)⟩
  | _, .tapp (.tapp u1 l' u2) l t2, h => (stepS G (.tapp u1 l' u2) h).map fun n =>
      ⟨n.σ', n.g, n.G', .tapp n.t' l ((h ▸ t2 : Tm σ []).renameStore n.g.rename)⟩
termination_by structural _ t => t

/-- One step of the source machine from the store `G` and the closed term
`t`, or `none` when the relation has no step there. -/
def step? {σ : Sig} (G : Store σ σ) (t : Tm σ []) : Option (Next σ) := stepS G t rfl

/-! ## Soundness and completeness -/

/-- **Soundness**: a step the function finds is a step of the relation. -/
theorem step?_sound {σ : Sig} {G : Store σ σ} :
    (t : Tm σ []) → (n : Next σ) → step? G t = some n → Step n.g G t n.G' n.t'
  | .tvar _, _, h => by simp [step?, stepS] at h
  | .tobj D, n, h => by
      simp only [step?, stepS, Option.some.injEq] at h; subst h; exact .ST_Obj
  | .tapp (.tvar (.conc f)) l (.tvar (.conc y)), n, h => by
      simp only [step?, stepS] at h
      split at h
      · rename_i OT1 OT2 t12 hl
        simp only [Option.some.injEq] at h; subst h; exact .ST_AppAbs hl
      · simp at h
  | .tapp (.tvar (.conc _)) _ (.tvar (.abs z)), _, _ => nomatch z
  | .tapp (.tvar (.conc f)) l (.tobj D), n, h => by
      simp only [step?, stepS, Option.map_some, Option.some.injEq] at h; subst h
      exact .ST_App2 .ST_Obj
  | .tapp (.tvar (.conc f)) l (.tapp u1 l' u2), n, h => by
      have h' : (step? G (.tapp u1 l' u2)).map (fun n =>
          (⟨n.σ', n.g, n.G', .tapp (.tvar (.conc (n.g.rename.var f))) l n.t'⟩ : Next σ)) = some n := h
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h'
      exact .ST_App2 (step?_sound (.tapp u1 l' u2) m hm)
  | .tapp (.tvar (.abs z)) _ _, _, _ => nomatch z
  | .tapp (.tobj D) l t2, n, h => by
      simp only [step?, stepS, Option.map_some, Option.some.injEq] at h; subst h
      exact .ST_App1 .ST_Obj
  | .tapp (.tapp u1 l' u2) l t2, n, h => by
      have h' : (step? G (.tapp u1 l' u2)).map (fun n =>
          (⟨n.σ', n.g, n.G', .tapp n.t' l (t2.renameStore n.g.rename)⟩ : Next σ)) = some n := h
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h'
      exact .ST_App1 (step?_sound (.tapp u1 l' u2) m hm)

/-- A location does not step. -/
theorem tvar_no_step {σ σ' : Sig} {g : Grows σ σ'} {G : Store σ σ} {v} {G' : Store σ' σ'}
    {t' : Tm σ' []} : ¬ Step g G (.tvar v) G' t' := fun h => nomatch h

/-- **Completeness**: every step of the relation is the step the function
finds, with the same signature, growth, store and term. -/
theorem step?_complete {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {t : Tm σ1 []}
    {G' : Store σ2 σ2} {t' : Tm σ2 []} (h : Step g G t G' t') :
    step? G t = some ⟨σ2, g, G', t'⟩ := by
  induction h with
  | ST_Obj => rfl
  | ST_AppAbs hl => simp [step?, stepS, hl]
  | ST_App1 h1 ih =>
      rename_i G0 G1 t1 t1' l t2
      cases t1 with
      | tvar v => exact absurd h1 tvar_no_step
      | tobj D =>
          cases h1; rfl
      | tapp u1 l' u2 =>
          show (step? G0 (.tapp u1 l' u2)).map _ = _
          rw [ih]; rfl
  | ST_App2 h2 ih =>
      rename_i G0 G1 f l t2 t2'
      cases t2 with
      | tvar v => exact absurd h2 tvar_no_step
      | tobj D =>
          cases h2; rfl
      | tapp u1 l' u2 =>
          show (step? G0 (.tapp u1 l' u2)).map _ = _
          rw [ih]; rfl

/-- The function has no step exactly when the relation has none. -/
theorem step?_eq_none_iff {σ : Sig} {G : Store σ σ} {t : Tm σ []} :
    step? G t = none ↔
      ¬ ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Tm σ' []), Step g G t G' t' := by
  constructor
  · rintro h ⟨σ', g, G', t', hs⟩
    rw [step?_complete hs] at h; cases h
  · intro h
    cases hs : step? G t with
    | none => rfl
    | some n => exact absurd ⟨n.σ', n.g, n.G', n.t', step?_sound t n hs⟩ h

/-- **Classification**: a configuration with no step is an answer or stuck in
the sense of `FCdotR.SrcStuck`. -/
theorem step?_none_classify {σ : Sig} {G : Store σ σ} {t : Tm σ []} (h : step? G t = none) :
    t.IsAnswer ∨ FCdotR.SrcStuck G t := by
  have hn := step?_eq_none_iff.mp h
  match t with
  | .tvar (.conc _) => exact Or.inl trivial
  | .tvar (.abs z) => exact nomatch z
  | .tobj _ => exact Or.inr ⟨fun h => h.elim, hn⟩
  | .tapp _ _ _ => exact Or.inr ⟨fun h => h.elim, hn⟩

/-- **Determinism of `Oopsla16.Step`**.  It follows from completeness, since
both steps are the step the function finds. -/
theorem step_det {σ σ1 σ2 : Sig} {g1 : Grows σ σ1} {g2 : Grows σ σ2} {G : Store σ σ}
    {t : Tm σ []} {G1 : Store σ1 σ1} {t1 : Tm σ1 []} {G2 : Store σ2 σ2} {t2 : Tm σ2 []}
    (h1 : Step g1 G t G1 t1) (h2 : Step g2 G t G2 t2) :
    (⟨σ1, g1, G1, t1⟩ : Next σ) = ⟨σ2, g2, G2, t2⟩ := by
  have e1 := step?_complete h1
  rw [step?_complete h2] at e1
  exact (Option.some.inj e1).symm

/-! ## Answers, decided -/

/-- `Oopsla16.Tm.IsAnswer` as a test: the answers are the locations. -/
def isAnswer {σ : Sig} : Tm σ [] → Bool
  | .tvar (.conc _) => true
  | _ => false

/-- The test decides Oopsla16's answers. -/
theorem isAnswer_iff {σ : Sig} (t : Tm σ []) : isAnswer t = true ↔ t.IsAnswer := by
  match t with
  | .tvar (.conc _) => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | .tvar (.abs z) => exact nomatch z
  | .tobj _ => exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩
  | .tapp _ _ _ => exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩

/-- A configuration the function cannot step and that is no answer is stuck. -/
theorem stuck_of_step?_none {σ : Sig} {G : Store σ σ} {t : Tm σ []} (h : step? G t = none)
    (ha : isAnswer t = false) : FCdotR.SrcStuck G t := by
  rcases step?_none_classify h with h' | h'
  · rw [← isAnswer_iff] at h'; rw [h'] at ha; exact Bool.noConfusion ha
  · exact h'

/-! ## The driver -/

/-- Growth composes with no allocation on the left. -/
theorem Grows.refl_comp {σ1 σ2 : Sig} : (g : Grows σ1 σ2) → Grows.refl.comp g = g
  | .refl => rfl
  | .snoc g => congrArg Grows.snoc (Grows.refl_comp g)

/-- Growth composes associatively. -/
theorem Grows.comp_assoc {σ1 σ2 σ3 : Sig} (g1 : Grows σ1 σ2) (g2 : Grows σ2 σ3) :
    {σ4 : Sig} → (g3 : Grows σ3 σ4) → (g1.comp g2).comp g3 = g1.comp (g2.comp g3)
  | _, .refl => rfl
  | _, .snoc g3 => congrArg Grows.snoc (Grows.comp_assoc g1 g2 g3)

/-- At most `m` steps from the store `G` and the term `t`.  The result is the
configuration after `m` steps, or the first one with no step, whichever comes
first, with the composed growth. -/
def run : Nat → {σ : Sig} → Store σ σ → Tm σ [] → Next σ
  | 0, _, G, t => ⟨_, .refl, G, t⟩
  | m + 1, _, G, t =>
    match step? G t with
    | some n => let r := run m n.G' n.t'; ⟨r.σ', n.g.comp r.g, r.G', r.t'⟩
    | none => ⟨_, .refl, G, t⟩
termination_by structural m => m

/-- Prepending a step to a run. -/
theorem steps_head {σ1 σ2 σ3 : Sig} {h : Grows σ1 σ2} {G : Store σ1 σ1} {t : Tm σ1 []}
    {G1 : Store σ2 σ2} {t1 : Tm σ2 []} (hs : Step h G t G1 t1) :
    {g : Grows σ2 σ3} → {G2 : Store σ3 σ3} → {t2 : Tm σ3 []} →
    Steps g G1 t1 G2 t2 → ∃ g' : Grows σ1 σ3, Steps g' G t G2 t2
  | _, _, _, .refl => ⟨_, .tail .refl hs⟩
  | _, _, _, .tail r s => by
      obtain ⟨g', r'⟩ := steps_head hs r
      exact ⟨_, .tail r' s⟩

/-- **The driver's result is reachable.**  The growth is existential. -/
theorem run_steps : (m : Nat) → {σ : Sig} → (G : Store σ σ) → (t : Tm σ []) →
    ∃ g : Grows σ (run m G t).σ', Steps g G t (run m G t).G' (run m G t).t'
  | 0, _, _, _ => ⟨_, .refl⟩
  | m + 1, _, G, t => by
      simp only [run]
      split
      · rename_i n hn
        obtain ⟨g', r⟩ := run_steps m n.G' n.t'
        exact steps_head (step?_sound t n hn) r
      · exact ⟨_, .refl⟩

/-- One more step of the driver, when the configuration it reached has a
step. -/
theorem run_succ_of_step : (m : Nat) → {σ : Sig} → (G : Store σ σ) → (t : Tm σ []) →
    (n : Next (run m G t).σ') → step? (run m G t).G' (run m G t).t' = some n →
    run (m + 1) G t = ⟨n.σ', (run m G t).g.comp n.g, n.G', n.t'⟩
  | 0, _, G, t, n, hn => by
      have hn' : step? G t = some n := hn
      simp only [run, hn', Grows.refl_comp]
      rfl
  | m + 1, _, G, t, n, hn => by
      cases h0 : step? G t with
      | none =>
          have hr : run (m + 1) G t = ⟨_, .refl, G, t⟩ := by simp only [run, h0]
          have hn' : step? (run (m + 1) G t).G' (run (m + 1) G t).t' = none := by
            rw [hr]; exact h0
          rw [hn'] at hn; cases hn
      | some n0 =>
          have hr : run (m + 1) G t =
              ⟨(run m n0.G' n0.t').σ', n0.g.comp (run m n0.G' n0.t').g,
                (run m n0.G' n0.t').G', (run m n0.G' n0.t').t'⟩ := by
            simp only [run, h0]
          have hr2 : run (m + 2) G t =
              ⟨(run (m + 1) n0.G' n0.t').σ', n0.g.comp (run (m + 1) n0.G' n0.t').g,
                (run (m + 1) n0.G' n0.t').G', (run (m + 1) n0.G' n0.t').t'⟩ := by
            simp only [run, h0]
          revert n hn
          rw [hr]
          intro n hn
          rw [hr2, run_succ_of_step m n0.G' n0.t' n hn]
          simp only [Grows.comp_assoc]

/-- One more step of the driver, from a configuration it is known to reach. -/
theorem run_succ_of_eq {m : Nat} {σ1 σ2 : Sig} {G : Store σ1 σ1} {t : Tm σ1 []}
    {g : Grows σ1 σ2} {G' : Store σ2 σ2} {t' : Tm σ2 []} {n : Next σ2}
    (hm : run m G t = ⟨σ2, g, G', t'⟩) (hn : step? G' t' = some n) :
    run (m + 1) G t = ⟨n.σ', g.comp n.g, n.G', n.t'⟩ := by
  have key := run_succ_of_step m G t
  generalize run m G t = r at key hm
  subst hm
  exact key n hn

/-- **The driver is complete.**  A configuration the relation reaches in any
number of steps is the configuration `run` returns at some number of steps,
with the same growth. -/
theorem run_complete {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {t : Tm σ1 []}
    {G' : Store σ2 σ2} {t' : Tm σ2 []} (h : Steps g G t G' t') :
    ∃ m, run m G t = ⟨σ2, g, G', t'⟩ := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail r s ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨m + 1, ?_⟩
      exact run_succ_of_eq hm (step?_complete s)

/-! ## Probes

Each rule of the machine on small closed terms, by `rfl` or `decide +kernel`.

`idCall` is `new {def apply(x) = x}.apply(new {})`, with `apply` at position
`0`.  It takes three steps: the receiver allocates (`ST_App1`), the argument
allocates (`ST_App2`), and the call returns its argument (`ST_AppAbs`). -/

/-- An object whose only member is the identity method. -/
private abbrev idObj : Dms [] ([],x) := .dcons (.dfun none none (.tvar (.abs .here))) .dnil

/-- The identity method called on an empty object. -/
private abbrev idCall : Tm [] [] := .tapp (.tobj idObj) 0 (.tobj .dnil)

/-- `ST_Obj`: a literal allocates one location and steps to it. -/
example : ∃ G', step? Store.nil (.tobj (.dnil : Dms [] ([],x))) =
    some ⟨_, .snoc .refl, G', .tvar (.conc .here)⟩ := ⟨_, rfl⟩

/-- `ST_App1` around `ST_Obj`: the receiver allocates first. -/
example : ∃ G', step? Store.nil idCall =
    some ⟨_, .snoc .refl, G', .tapp (.tvar (.conc .here)) 0 (.tobj .dnil)⟩ := ⟨_, rfl⟩

/-- `ST_App2` around `ST_Obj`: with a location as receiver the argument
allocates. -/
example : ∃ G', step? (run 1 Store.nil idCall).G' (run 1 Store.nil idCall).t' =
    some ⟨_, .snoc .refl, G', .tapp (.tvar (.conc (.there .here))) 0 (.tvar (.conc .here))⟩ :=
  ⟨_, rfl⟩

/-- `ST_AppAbs`: the call looks up `apply` in the stored receiver and returns
the argument's location, without allocating. -/
example : step? (run 2 Store.nil idCall).G' (run 2 Store.nil idCall).t' =
    some ⟨_, .refl, (run 2 Store.nil idCall).G', .tvar (.conc .here)⟩ := rfl

/-- After three steps `idCall` is an answer, and an answer has no step. -/
example : isAnswer (run 3 Store.nil idCall).t' = true ∧
    (step? (run 3 Store.nil idCall).G' (run 3 Store.nil idCall).t').isNone = true := by
  decide +kernel

/-- Two steps are not enough for `idCall`. -/
example : isAnswer (run 2 Store.nil idCall).t' = false := by decide +kernel

/-- The driver stops at an answer: more fuel changes nothing. -/
example : isAnswer (run 10 Store.nil idCall).t' = true := by decide +kernel

/-- The program of Oopsla16's recursive argument example reaches an answer
in three steps and not in two. -/
example : isAnswer (run 3 Store.nil FCdotR.SourceSafety.RecursiveArg.prog).t' = true ∧
    isAnswer (run 2 Store.nil FCdotR.SourceSafety.RecursiveArg.prog).t' = false := by
  decide +kernel

/-- A call of a member the receiver lacks: `new {}.apply(new {})`. -/
private abbrev missingCall : Tm [] [] := .tapp (.tobj .dnil) 0 (.tobj .dnil)

/-- A call of a type member: `new {type A = ⊤}.A(new {})`, with `A` at
position `0`. -/
private abbrev typeCall : Tm [] [] :=
  .tapp (.tobj (.dcons (.dty .TTop) .dnil)) 0 (.tobj .dnil)

/-- Both calls allocate their operands and then have no step, and neither is
an answer. -/
example : (step? (run 2 Store.nil missingCall).G' (run 2 Store.nil missingCall).t').isNone = true ∧
    isAnswer (run 2 Store.nil missingCall).t' = false ∧
    (step? (run 2 Store.nil typeCall).G' (run 2 Store.nil typeCall).t').isNone = true ∧
    isAnswer (run 2 Store.nil typeCall).t' = false := by
  decide +kernel

/-- So the configuration `missingCall` reaches is stuck. -/
example : FCdotR.SrcStuck (run 2 Store.nil missingCall).G' (run 2 Store.nil missingCall).t' :=
  stuck_of_step?_none (Option.isNone_iff_eq_none.mp (by decide +kernel)) (by decide +kernel)

end Oopsla16Frontend
