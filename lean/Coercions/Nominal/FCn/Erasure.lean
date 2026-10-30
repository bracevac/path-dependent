import Coercions.Nominal.FCn.Machine
import Coercions.PDot.Runtime

/-!
# Erasure into the runtime (plan T.4, "Erasure into the runtime")

The erasure maps FCn into untyped pDOT, `PDot.Runtime`.  It drops every type, every cast and every
type definition, and keeps the path of path evidence.  A literal `obj (z : Tel) ds` erases to
`ν(z) |ds|`, a nested literal `nest (v : Tel) ds` to `nest |ds|`, and a lambda to `λ(z) |t|`.  A state
erases to one runtime configuration: its continuation is plugged with the erased term.

`Tm.erase_rename`, `Tm.erase_subst` and `Tm.erase_substCo` say that erasure commutes with renaming,
with evidence substitution read through `CoSubst.paths`, and with the instantiation of `.here`.
Each is one mutual block over the four term families.  `Cont.plug_red` carries a runtime step under
every frame.

`erase_step` holds for any application view that is sound: the view reaches, in the erased store,
the closure it names (`AppView.Sound`, decision D7 of the groups file).  A step of FCn is either a
runtime step of the erasure or one of four shuffles that keep the erasure (`erase_step_shuffle`).
`Shuffle.measure_lt` and `shuffle_terminates` bound the shuffles.

Binders are named in comments.  `(s,x)` adds one variable, `.here` is the newest.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The erasure -/

mutual
def Tm.erase : Tm s → PDot.Runtime.Tm s
  | .path P => .path P.path                                -- |path P| = path P.path
  | .val v => .val v.erase                                 -- |val v| = val |v|
  | .app P Q => .app P.path Q.path                         -- |app P Q| = app P.path Q.path
  | .lett t u => .lett t.erase u.erase                     -- |let z = t in u| = let z = |t| in |u|
  | .cast t _ => t.erase                                   -- |cast t e| = |t|
def Value.erase : Value s → PDot.Runtime.Val s
  | .lam _ t => .lam t.erase                               -- |lam (z : S) t| = λ(z) |t|
  | .obj _ ds => .new ds.erase                             -- |obj (z : Tel) ds| = ν(z) |ds|
  | .cast v _ => v.erase                                   -- |cast v e| = |v|
def Defs.erase : Defs s → PDot.Runtime.Defs s
  | .nil => .nil                                           -- |[]| = []
  | .typ ds _ _ => ds.erase                                -- |ds ▹ {A = U}| = |ds|
  | .fld ds a rhs => .cons ds.erase a rhs.erase
def Rhs.erase : Rhs s → PDot.Runtime.Rhs s
  | .path P => .defp P.path                                -- a = defp P.path
  | .fn v => .defv v.erase                                 -- a = defv |v|
  | .nest _ ds => .nest ds.erase                           -- a = nest |ds|
end
def Store.erase : Store s → PDot.Runtime.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.erase v.erase
def Cont.plug : Cont s → PDot.Runtime.Tm s → PDot.Runtime.Tm s
  | .nil, r => r                                           -- [].plug r = r
  | .cons K (.lett u), r => K.plug (.lett r u.erase)       -- (K ▹ let z. u).plug r = K.plug (let z = r in |u|)
  | .cons K (.cast _), r => K.plug r                       -- (K ▹ cast e).plug r = K.plug r
def State.erase (st : State s) : PDot.Runtime.Conf := ⟨s, st.σ.erase, st.K.plug st.t.erase⟩   -- |⟨σ, K, t⟩|

/-! ## Erasure and binding -/

mutual
theorem Tm.erase_rename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂), (t.rename ρ).erase = t.erase.rename ρ
  | .path P, ρ => by simp only [Tm.rename, Tm.erase, PDot.Runtime.Tm.rename, PathCo.path_rename]
  | .val v, ρ => by simp only [Tm.rename, Tm.erase, PDot.Runtime.Tm.rename, Value.erase_rename v ρ]
  | .app P Q, ρ => by simp only [Tm.rename, Tm.erase, PDot.Runtime.Tm.rename, PathCo.path_rename]
  | .lett t u, ρ => by
      simp only [Tm.rename, Tm.erase, PDot.Runtime.Tm.rename, Tm.erase_rename t ρ, Tm.erase_rename u ρ.lift]
  | .cast t _, ρ => by simp only [Tm.rename, Tm.erase, Tm.erase_rename t ρ]
theorem Value.erase_rename : ∀ (v : Value s₁) (ρ : Rename s₁ s₂), (v.rename ρ).erase = v.erase.rename ρ
  | .lam _ t, ρ => by simp only [Value.rename, Value.erase, PDot.Runtime.Val.rename, Tm.erase_rename t ρ.lift]
  | .obj _ ds, ρ => by simp only [Value.rename, Value.erase, PDot.Runtime.Val.rename, Defs.erase_rename ds ρ.lift]
  | .cast v _, ρ => by simp only [Value.rename, Value.erase, Value.erase_rename v ρ]
theorem Defs.erase_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂), (ds.rename ρ).erase = ds.erase.rename ρ
  | .nil, _ => rfl
  | .typ ds _ _, ρ => by simp only [Defs.rename, Defs.erase, Defs.erase_rename ds ρ]
  | .fld ds a rhs, ρ => by
      simp only [Defs.rename, Defs.erase, PDot.Runtime.Defs.rename, Defs.erase_rename ds ρ, Rhs.erase_rename rhs ρ]
theorem Rhs.erase_rename : ∀ (rhs : Rhs s₁) (ρ : Rename s₁ s₂), (rhs.rename ρ).erase = rhs.erase.rename ρ
  | .path P, ρ => by simp only [Rhs.rename, Rhs.erase, PDot.Runtime.Rhs.rename, PathCo.path_rename]
  | .fn v, ρ => by simp only [Rhs.rename, Rhs.erase, PDot.Runtime.Rhs.rename, Value.erase_rename v ρ]
  | .nest _ ds, ρ => by simp only [Rhs.rename, Rhs.erase, PDot.Runtime.Rhs.rename, Defs.erase_rename ds ρ]
end

mutual
theorem Tm.erase_subst : ∀ (t : Tm s₁) (σ : CoSubst s₁ s₂), (t.subst σ).erase = t.erase.subst σ.paths
  | .path P, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, PathCo.path_subst]
  | .val v, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, Value.erase_subst v σ]
  | .app P Q, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, PathCo.path_subst]
  | .lett t u, σ => by
      simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, Tm.erase_subst t σ, Tm.erase_subst u σ.lift,
        CoSubst.lift_paths]
  | .cast t _, σ => by simp only [Tm.subst, Tm.erase, Tm.erase_subst t σ]
theorem Value.erase_subst : ∀ (v : Value s₁) (σ : CoSubst s₁ s₂), (v.subst σ).erase = v.erase.subst σ.paths
  | .lam _ t, σ => by
      simp only [Value.subst, Value.erase, PDot.Runtime.Val.subst, Tm.erase_subst t σ.lift, CoSubst.lift_paths]
  | .obj _ ds, σ => by
      simp only [Value.subst, Value.erase, PDot.Runtime.Val.subst, Defs.erase_subst ds σ.lift, CoSubst.lift_paths]
  | .cast v _, σ => by simp only [Value.subst, Value.erase, Value.erase_subst v σ]
theorem Defs.erase_subst : ∀ (ds : Defs s₁) (σ : CoSubst s₁ s₂), (ds.subst σ).erase = ds.erase.subst σ.paths
  | .nil, _ => rfl
  | .typ ds _ _, σ => by simp only [Defs.subst, Defs.erase, Defs.erase_subst ds σ]
  | .fld ds a rhs, σ => by
      simp only [Defs.subst, Defs.erase, PDot.Runtime.Defs.subst, Defs.erase_subst ds σ, Rhs.erase_subst rhs σ]
theorem Rhs.erase_subst : ∀ (rhs : Rhs s₁) (σ : CoSubst s₁ s₂), (rhs.subst σ).erase = rhs.erase.subst σ.paths
  | .path P, σ => by simp only [Rhs.subst, Rhs.erase, PDot.Runtime.Rhs.subst, PathCo.path_subst]
  | .fn v, σ => by simp only [Rhs.subst, Rhs.erase, PDot.Runtime.Rhs.subst, Value.erase_subst v σ]
  | .nest _ ds, σ => by simp only [Rhs.subst, Rhs.erase, PDot.Runtime.Rhs.subst, Defs.erase_subst ds σ]
end

theorem Tm.erase_substCo (t : Tm (s,x)) (Q : PathCo s) : (t.substCo Q).erase = t.erase.substPath Q.path := by
  rw [Tm.substCo, Tm.erase_subst, CoSubst.one_paths, PDot.Runtime.Tm.substPath]

/-- The self cast of `MS-LetVal` moves no path, so the adjusted body erases as the body. -/
theorem Tm.erase_adjust (u : Tm (s,x)) (v : Value s) : (u.adjust v).erase = u.erase := by
  unfold Tm.adjust
  split
  · rfl
  · rw [Tm.erase_subst, CoSubst.selfCast_paths, PDot.Runtime.Tm.subst_ofRename, PDot.Runtime.Tm.rename_id]

theorem Value.erase_core : ∀ (v : Value s), v.core.erase = v.erase
  | .lam _ _ => rfl
  | .obj _ _ => rfl
  | .cast v _ => Value.erase_core v

/-- A runtime step under the frames of a continuation.  The `let` frames are renamed along the step. -/
theorem Cont.plug_red {K : Cont s} {γ : PDot.Runtime.Store s} {γ' : PDot.Runtime.Store s'} {r : PDot.Runtime.Tm s} {r' : PDot.Runtime.Tm s'} {ρ : Rename s s'} (h : PDot.Runtime.Red ⟨s, γ, r⟩ ⟨s', γ', r'⟩ ρ) : PDot.Runtime.Red ⟨s, γ, K.plug r⟩ ⟨s', γ', (K.rename ρ).plug r'⟩ ρ := by
  induction K generalizing r r' with
  | nil => exact h
  | cons K fr ih =>
      cases fr with
      | lett u =>
          have h' := ih (PDot.Runtime.Red.letTgt (t := u.erase) h)
          rw [← Tm.erase_rename u ρ.lift] at h'
          exact h'
      | cast e => exact ih h

/-! ## Erasure and the machine -/

/-- The application view reaches, in the erased store, the closure it names. -/
def AppView.Sound (V : AppView) : Prop :=
  ∀ {s : Sig} {σ : Store s} {P : PathCo s} {S₀ : Ty s} {t₀ : Tm (s,x)} {h : AppHead s},
    V σ P S₀ t₀ h → PDot.Runtime.Lookups σ.erase (.defp P.path) (.defv (.lam t₀.erase))

inductive Shuffle : State s → State s → Prop where        -- the four steps that do not move the erasure
  -- MS-Let      binders σ K t, z of u
  | lett : Shuffle ⟨σ, K, .lett t u⟩ ⟨σ, .cons K (.lett u), t⟩
  -- MS-CastPush binders σ K t e
  | castPush : Shuffle ⟨σ, K, .cast t e⟩ ⟨σ, .cons K (.cast e), t⟩
  -- MS-CastVal  binders σ K e v
  | castVal : Shuffle ⟨σ, .cons K (.cast e), .val v⟩ ⟨σ, K, .val (.cast v e)⟩
  -- MS-CastPath binders σ K e P
  | castPath : Shuffle ⟨σ, .cons K (.cast e), .path P⟩ ⟨σ, K, .path (.cast P e)⟩
def Tm.headSize : Tm s → Nat
  | .lett t _ => t.headSize + 1
  | .cast t _ => t.headSize + 1
  | .path _ => 0
  | .val _ => 0
  | .app _ _ => 0
def Cont.length : Cont s → Nat
  | .nil => 0
  | .cons K _ => K.length + 1
def State.shuffleMeasure (st : State s) : Nat := 2 * st.t.headSize + st.K.length

theorem Shuffle.step {V : AppView} {st st' : State s} : Shuffle st st' → Step V st st'
  | .lett => .lett
  | .castPush => .castPush
  | .castVal => .castVal
  | .castPath => .castPath

theorem Shuffle.erase_eq {st st' : State s} : Shuffle st st' → st.erase = st'.erase
  | .lett => rfl
  | .castPush => rfl
  | .castVal => rfl
  | .castPath => rfl

/-- A step of the machine is a runtime step of the erasure, or one of the four shuffles. -/
theorem erase_step_shuffle {V : AppView} (hV : V.Sound) {st : State s} {st' : State s'} (h : Step V st st') : PDot.Runtime.Step st.erase st'.erase ∨ ∃ e : s' = s, Shuffle st (e ▸ st') := by
  cases h with
  | lett => exact .inr ⟨rfl, .lett⟩
  | castPush => exact .inr ⟨rfl, .castPush⟩
  | castVal => exact .inr ⟨rfl, .castVal⟩
  | castPath => exact .inr ⟨rfl, .castPath⟩
  | @letVal σ K u v =>
      -- RR-LetVal under the frames of K
      refine .inl ⟨Rename.succ, ?_⟩
      have h0 : PDot.Runtime.Red ⟨_, σ.erase, .lett (.val v.erase) u.erase⟩ ⟨_, σ.erase.cons v.erase, u.erase⟩ Rename.succ := .letVal
      have h1 := Cont.plug_red (K := K) h0
      show PDot.Runtime.Red ⟨_, σ.erase, K.plug (.lett (.val v.erase) u.erase)⟩ ⟨_, σ.erase.cons v.core.erase, (K.rename Rename.succ).plug (u.adjust v).erase⟩ Rename.succ
      rw [Value.erase_core, Tm.erase_adjust]
      exact h1
  | @letPath σ K u P =>
      -- RR-LetPath under the frames of K
      refine .inl ⟨Rename.id, ?_⟩
      have h0 : PDot.Runtime.Red ⟨_, σ.erase, .lett (.path P.path) u.erase⟩ ⟨_, σ.erase, u.erase.substPath P.path⟩ Rename.id := .letPath
      have h1 := Cont.plug_red (K := K) h0
      rw [Cont.rename_id] at h1
      show PDot.Runtime.Red ⟨_, σ.erase, K.plug (.lett (.path P.path) u.erase)⟩ ⟨_, σ.erase, K.plug (u.substCo P).erase⟩ Rename.id
      rw [Tm.erase_substCo]
      exact h1
  | @appId σ P S₀ t₀ K Q hv =>
      -- RR-App at the closure the view reaches
      refine .inl ⟨Rename.id, ?_⟩
      have h0 : PDot.Runtime.Red ⟨_, σ.erase, .app P.path Q.path⟩ ⟨_, σ.erase, t₀.erase.substPath Q.path⟩ Rename.id := .app (hV hv)
      have h1 := Cont.plug_red (K := K) h0
      rw [Cont.rename_id] at h1
      show PDot.Runtime.Red ⟨_, σ.erase, K.plug (.app P.path Q.path)⟩ ⟨_, σ.erase, K.plug (t₀.substCo Q).erase⟩ Rename.id
      rw [Tm.erase_substCo]
      exact h1
  | @appPi σ P S₀ t₀ d c K Q hv =>
      -- RR-App, the casts of MS-AppPi erased
      refine .inl ⟨Rename.id, ?_⟩
      have h0 : PDot.Runtime.Red ⟨_, σ.erase, .app P.path Q.path⟩ ⟨_, σ.erase, t₀.erase.substPath Q.path⟩ Rename.id := .app (hV hv)
      have h1 := Cont.plug_red (K := K) h0
      rw [Cont.rename_id] at h1
      show PDot.Runtime.Red ⟨_, σ.erase, K.plug (.app P.path Q.path)⟩ ⟨_, σ.erase, K.plug (t₀.substCo (.cast Q d)).erase⟩ Rename.id
      rw [Tm.erase_substCo]
      exact h1
  | @appEq σ P S₀ t₀ φ K Q hv =>
      -- RR-App, the casts of MS-AppEq erased
      refine .inl ⟨Rename.id, ?_⟩
      have h0 : PDot.Runtime.Red ⟨_, σ.erase, .app P.path Q.path⟩ ⟨_, σ.erase, t₀.erase.substPath Q.path⟩ Rename.id := .app (hV hv)
      have h1 := Cont.plug_red (K := K) h0
      rw [Cont.rename_id] at h1
      show PDot.Runtime.Red ⟨_, σ.erase, K.plug (.app P.path Q.path)⟩ ⟨_, σ.erase, K.plug (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))).erase⟩ Rename.id
      rw [Tm.erase_substCo]
      exact h1

theorem erase_step {V : AppView} (hV : V.Sound) {st : State s} {st' : State s'} (h : Step V st st') : PDot.Runtime.Step st.erase st'.erase ∨ st.erase = st'.erase := by
  rcases erase_step_shuffle hV h with hs | ⟨e, hsh⟩
  · exact .inl hs
  · subst e
    exact .inr hsh.erase_eq

theorem Shuffle.measure_lt {st st' : State s} : Shuffle st st' → st'.shuffleMeasure < st.shuffleMeasure := by
  intro h
  cases h <;> simp only [State.shuffleMeasure, Tm.headSize, Cont.length] <;> omega

theorem shuffle_terminates : WellFounded (fun (st' st : State s) => Shuffle st st') :=
  Subrelation.wf (fun h => Shuffle.measure_lt h) (measure State.shuffleMeasure).wf

end Nominal.FCn
