import Coercions.Nominal.FCn.ProvenanceClass
import Coercions.Nominal.FCn.ClassExamples

/-!
# Run-time provenance: the machine with records, computed, and runs of FCn programs

`astepOf` is one step of the machine with records at `appView`, computed, and `astepOf_sound` its
soundness.  The runs: N1's class program, a forging program that seals a module method's parameter and
one whose method seals a literal it captures (both fail `Tm.InitSeals`, and every state of their runs
fails the predicate), a constructor that casts its literal before it allocates it, the two
application heads of `CanonicalExamples`, the corollary at a store of `ClassExamples`, a class
whose instance is a function, and a dormant seal.  The dormant seal is a negative control on
reading the records.  An allocation record tracks the class seal sites permitted by the allocating
scope, including sites inside dormant code.  It is not by itself a log of executed constructors or
executed seal uses.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The machine with records, computed -/

/-- One step of the machine with allocation records at `appView`, computed. -/
def astepOf {s : Sig} : AState s → Option ((s' : Sig) × AState s')
  | ⟨⟨σ, K, .lett t u⟩, A⟩ => some ⟨s, ⟨⟨σ, .cons K (.lett u), t⟩, A⟩⟩
  | ⟨⟨σ, K, .cast t e⟩, A⟩ => some ⟨s, ⟨⟨σ, .cons K (.cast e), t⟩, A⟩⟩
  | ⟨⟨σ, .cons K (.cast e), .val v⟩, A⟩ => some ⟨s, ⟨⟨σ, K, .val (.cast v e)⟩, A⟩⟩
  | ⟨⟨σ, .cons K (.cast e), .path P⟩, A⟩ => some ⟨s, ⟨⟨σ, K, .path (.cast P e)⟩, A⟩⟩
  | ⟨⟨σ, .cons K (.lett u), .val v⟩, A⟩ =>
      some ⟨(s,x), ⟨⟨σ.cons v.core, K.weaken, u.adjust v⟩, A.consO (allocLbl u v)⟩⟩
  | ⟨⟨σ, .cons K (.lett u), .path P⟩, A⟩ => some ⟨s, ⟨⟨σ, K, u.substCo P⟩, A⟩⟩
  | ⟨⟨σ, K, .app P Q⟩, A⟩ =>
      match appViewOf σ P with
      | some (_, t₀, .id) => some ⟨s, ⟨⟨σ, K, t₀.substCo Q⟩, A⟩⟩
      | some (_, t₀, .pi d c) => some ⟨s, ⟨⟨σ, K, .cast (t₀.substCo (.cast Q d)) (c.substCo Q)⟩, A⟩⟩
      | some (_, t₀, .eqv φ) =>
          some ⟨s, ⟨⟨σ, K, .cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))⟩, A⟩⟩
      | none => none
  | _ => none

theorem astepOf_sound {s : Sig} {g : AState s} {s' : Sig} {g' : AState s'} (h : astepOf g = some ⟨s', g'⟩) :
    AStep appView g g' := by
  obtain ⟨⟨σ, K, t⟩, A⟩ := g
  cases t with
  | lett t u =>
      simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .lett
  | cast t e =>
      simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .castPush
  | app P Q =>
      simp only [astepOf] at h
      split at h
      · rename_i S₀ t₀ hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .appId (appViewOf_iff.1 hv)
      · rename_i S₀ t₀ d c hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .appPi (appViewOf_iff.1 hv)
      · rename_i S₀ t₀ φ hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .appEq (appViewOf_iff.1 hv)
      · cases h
  | val v =>
      cases K with
      | nil => simp [astepOf] at h
      | cons K fr =>
          cases fr with
          | lett u =>
              simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .letVal
          | cast e =>
              simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .castVal
  | path P =>
      cases K with
      | nil => simp [astepOf] at h
      | cons K fr =>
          cases fr with
          | lett u =>
              simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .letPath
          | cast e =>
              simp only [astepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h; cases eq_of_heq h; exact .castPath

/-- At most `m` steps with records. -/
def arun : Nat → (s : Sig) × AState s → (s : Sig) × AState s
  | 0, p => p
  | m+1, ⟨s, g⟩ =>
      match astepOf g with
      | some p => arun m p
      | none => ⟨s, g⟩

theorem ASteps.head {V : AppView} {g : AState s} {g₁ : AState s₁} {g₂ : AState s₂} (h₁ : AStep V g g₁)
    (h₂ : ASteps V g₁ g₂) : ASteps V g g₂ := by
  induction h₂ with
  | refl => exact .tail .refl h₁
  | tail _ h ih => exact .tail (ih h₁) h

theorem arun_steps : ∀ (m : Nat) (p : (s : Sig) × AState s), ASteps appView p.2 (arun m p).2
  | 0, _ => .refl
  | m+1, ⟨s, g⟩ => by
      simp only [arun]
      split
      · rename_i p h
        exact ASteps.head (astepOf_sound h) (arun_steps m p)
      · exact .refl

/-- The path in focus, if the term is a path. -/
def State.focusPath? : State s → Option (PathCo s)
  | ⟨_, _, .path P⟩ => some P
  | _ => none

/-- The predicate at each of the first `m + 1` states of the run, oldest first. -/
def arunAll : Nat → (s : Sig) × AState s → List Bool
  | 0, ⟨_, g⟩ => [State.SealsAtCtors g.A g.st]
  | m+1, ⟨_, g⟩ =>
      match astepOf g with
      | some p => State.SealsAtCtors g.A g.st :: arunAll m p
      | none => [State.SealsAtCtors g.A g.st]

def startA (t : Tm []) : (s : Sig) × AState s := ⟨[], ⟨⟨.nil, .nil, t⟩, Alloc.empty⟩⟩

/-- The variables of a signature, the newest first. -/
def allVars : (s : Sig) → List (BVar s .var)
  | [] => []
  | (.var :: s) => .here :: (allVars s).map .there

/-- The record of every store variable, the newest first: the keys `(i, C)` with `C` among `cands` and
the owner the variable of index `i`, at the full signature. -/
def storeKeys (s : Sig) (A : Alloc s) (cands : List Label) : List (List (Nat × Label)) :=
  (allVars s).map fun y => (allVars s).flatMap fun q =>
    (cands.filter fun C => A y (.var q, C)).map fun C => (BVar.dbIdx q, C)

/-- A final state, decided: no frame, and a value or a path in focus. -/
def State.finalB {s : Sig} : State s → Bool
  | ⟨_, .nil, .val _⟩ => true
  | ⟨_, .nil, .path _⟩ => true
  | _ => false

/-! ### The kinds of step the runs exercise -/

/-- The rule the machine applies at a state, with `MS-LetVal` split by whether `adjust` substitutes. -/
def kindOf {s : Sig} : State s → String
  | ⟨_, _, .lett _ _⟩ => "lett"
  | ⟨_, _, .cast _ _⟩ => "castPush"
  | ⟨_, .cons _ (.cast _), .val _⟩ => "castVal"
  | ⟨_, .cons _ (.cast _), .path _⟩ => "castPath"
  | ⟨_, .cons _ (.lett _), .val v⟩ => match v.composite with
    | some _ => "letVal-adjust"
    | none => "letVal"
  | ⟨_, .cons _ (.lett _), .path _⟩ => "letPath"
  | ⟨σ, _, .app P _⟩ =>
      match appViewOf σ P with
      | some (_, _, .id) => "appId"
      | some (_, _, .pi _ _) => "appPi"
      | some (_, _, .eqv _) => "appEq"
      | none => "stuck"
  | _ => "final"

def arunKinds : Nat → (s : Sig) × AState s → List String
  | 0, ⟨_, g⟩ => [kindOf g.st]
  | m+1, ⟨_, g⟩ =>
      match astepOf g with
      | some p => kindOf g.st :: arunKinds m p
      | none => [kindOf g.st]

namespace ProvEx

/-! ### N1's class program `Class.progC` -/

namespace N1
open Class

theorem init : Tm.InitSeals progC = true := by decide +kernel
/-- Every state of the run meets the predicate, eleven states to the final one. -/
theorem every_state : arunAll 40 (startA progC) = List.replicate 11 true := by decide +kernel
theorem final : State.finalB (arun 40 (startA progC)).2.st = true := by decide +kernel
/-- The record of the instance holds `(m, C)`, `m` the module (index 1), and that of the module no key. -/
theorem keys : storeKeys (arun 40 (startA progC)).1 (arun 40 (startA progC)).2.A [C, get, newC] = [[(1, C)], []] := by
  decide +kernel

/-- Six steps in: the constructor's `let` has allocated the instance, and its seal at `m∙C` is the focus. -/
abbrev g6 := arun 6 (startA progC)
theorem g6_sig : g6.1 = (([],x),x) := by decide +kernel
theorem g6_term : g6.2.st.t = .path (.cast (.var .here) (.seal (.var (.there .here)) C)) := by decide +kernel
theorem g6_keys : storeKeys g6.1 g6.2.A [C] = [[(1, C)], []] := by decide +kernel

end N1

/-! ### The forging run `ClassEx.Forge`: the negative control -/

namespace ForgeRun
open ClassEx.Forge

/-- The forging program fails the initial condition: `forge` seals its parameter. -/
theorem init_fails : Tm.InitSeals progF = false := by decide +kernel
/-- It is typed and runs (`progF_checks`, `progF_reaches`), and every state fails the predicate under
the records of its run: the module in the store still holds `forge`. -/
theorem every_state_fails : arunAll 40 (startA progF) = List.replicate 8 false := by decide +kernel
/-- Six steps in, the forged path `cast l (seal m T)` is the focus, and the record of `l` holds no
key: the scope that allocated `l` has no seal site at `l`. -/
abbrev g6 := arun 6 (startA progF)
theorem g6_sig : g6.1 = (([],x),x) := by decide +kernel
theorem g6_keys : storeKeys g6.1 g6.2.A [lT] = [[], []] := by decide +kernel
theorem g6_term : g6.2.st.t = .path P6 := by decide +kernel
/-- So the forged path is no path the corollary reads: it fails the predicate under the run's record. -/
theorem forged_path_fails : (State.focusPath? g6.2.st).map (PathCo.sealsOK g6.2.A) = some false := by
  decide +kernel
end ForgeRun

/-! ### A constructor whose literal is cast before it is allocated: `MS-CastVal` and `adjust` -/

namespace CastCtor
open Class

/-- `lam ⊤ (let i = cast (val inst) (refl (μ TelI)) in path (cast (var i) (seal z C)))`. -/
def ctorC' : Value ([],x) :=
  .lam .top (.lett (.cast (.val inst) (.refl (.mu TelI))) (.path (.cast (.var .here) (.seal (.var (.there (.there .here))) C))))
def mC' : Value [] := .obj TelmC (.fld (.cls .nil C Bd) newC (.fn ctorC'))
def progC' : Tm [] :=
  .lett (.val mC')
    (.lett (.app (.sel (.var .here) newC 2) (.cast (.var .here) (.top (.mu TelmC))))
      (.path (.cast (.var .here) (.top (.sel (.var (.there .here)) C)))))

theorem checks : checkTm .nil progC' .top = true := by decide +kernel
theorem init : Tm.InitSeals progC' = true := by decide +kernel
theorem every_state : (arunAll 40 (startA progC')).all (· = true) = true := by decide +kernel
theorem final : State.finalB (arun 40 (startA progC')).2.st = true := by decide +kernel
theorem keys : storeKeys (arun 40 (startA progC')).1 (arun 40 (startA progC')).2.A [C] = [[(1, C)], []] := by
  decide +kernel
end CastCtor

/-! ### `MS-AppEq` and `MS-AppPi` on the stores of `CanonicalExamples` -/

namespace Heads
open C0Ex.R2

/-- `MS-AppEq` from N3's state: the predicate before and after, with no label. -/
theorem appEq_step : AStep appView (⟨st, Alloc.empty⟩ : AState (([],x),x)) ⟨st', Alloc.empty⟩ := .appEq P_appView
theorem appEq_before : State.SealsAtCtors Alloc.empty st = true := by decide +kernel
theorem appEq_after : State.SealsAtCtors Alloc.empty st' = true :=
  AStep.sealsAtCtors appView_sealsOK appEq_step appEq_before

/-- `MS-AppPi` from risk (a)'s path `cast y (trans (eqToLe φ) (pi d c))` applied to `Q`. -/
abbrev stPi : State (([],x),x) := ⟨σ, .nil, .app C0Ex.RiskA.P' Q⟩
theorem appPi_kind : (appViewOf σ C0Ex.RiskA.P').map (fun r => match r.2.2 with
    | .pi _ _ => true
    | _ => false) = some true := by decide +kernel
theorem appPi_before : State.SealsAtCtors Alloc.empty stPi = true := by decide +kernel
theorem appPi_after : ∀ (g : (s : Sig) × AState s), astepOf (⟨stPi, Alloc.empty⟩ : AState (([],x),x)) = some g →
    State.SealsAtCtors g.2.A g.2.st = true := fun _ h =>
  AStep.sealsAtCtors appView_sealsOK (astepOf_sound h) appPi_before
theorem appPi_after_computed : (astepOf (⟨stPi, Alloc.empty⟩ : AState (([],x),x))).map
    (fun g' => State.SealsAtCtors g'.2.A g'.2.st) = some true := by decide +kernel
end Heads

/-! ### The corollary at the constructed instance and at the forged one (`ClassEx.Store1`) -/

namespace Store1C
open ClassEx.Store1

/-- A record of `Store1` written by hand, not computed by a run.  It holds the keys `(m, T)` and
`(m, C)` at `i`, the keys of an allocating scope with seal sites of `i` at `m∙T` and `m∙C`. -/
def A1 : Alloc (([],x),x) := fun y k => match y with
  | .here => decide (k = (m, lT)) || decide (k = (m, lC))
  | .there _ => false
theorem Pc_frag : PathCo.Frag Pc := .inl trivial
theorem Pc_ok : PathCo.sealsOK A1 Pc = true := by decide +kernel
/-- The corollary at `Pc : m∙C`: the instance `i`, a key of its record, a class below `C`. -/
theorem Pc_provenance : ∃ y q D, Γ1.canon Pc.path = Γ1.canon (.var y) ∧ A1 y (q, D) = true ∧ Below Γ1 m lC (.sel q D) :=
  frag_provenance σ1_typed Pc Pc_frag Pc_ok Pc_typed (.self res_mC canon_m)
/-- The forged path `cast i (seal m T)` under a record that holds no key at `i`. -/
theorem forged_fails : PathCo.sealsOK Alloc.empty (.cast (.var .here) (.seal m lT) : PathCo (([],x),x)) = false := by
  decide +kernel
end Store1C


/-! ### A function instance: a class with body `⊤` sealed at a stored lambda

    let m = obj (z : [⊥ ⊑ z∙E, z∙E ⊑ ⊤, fld mk Π(u : ⊤) z∙E])
              {class E = ⊤, mk = λ(u : ⊤). let f = λ(y : ⊤). y in path (cast f (trans (top Π(y:⊤)⊤) (seal z E)))} in
    let c = m.mk (cast m ⊤) in
    path (cast c (top m∙E))
-/

namespace FnInst

abbrev lE : Label := .typ 50
abbrev lmk : Label := .trm 50

abbrev TelM : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .bot (.sel (.var .here) lE))) (.le (.sel (.var .here) lE) .top))
    (.fld lmk (.pi .top (.sel (.var (.there .here)) lE)))
abbrev mkFn : Value ([],x) :=
  .lam .top (.lett (.val (.lam .top (.path (.var .here))))
    (.path (.cast (.var .here) (.trans (.top (.pi .top .top)) (.seal (.var (.there (.there .here))) lE)))))
abbrev mE : Value [] := .obj TelM (.fld (.cls .nil lE .top) lmk (.fn mkFn))
abbrev prog : Tm [] :=
  .lett (.val mE)
    (.lett (.app (.sel (.var .here) lmk 2) (.cast (.var .here) (.top (.mu TelM))))
      (.path (.cast (.var .here) (.top (.sel (.var (.there .here)) lE)))))

theorem checks : checkTm .nil prog .top = true := by decide +kernel
theorem init : Tm.InitSeals prog = true := by decide +kernel
theorem every_state : (arunAll 40 (startA prog)).all (· = true) = true := by decide +kernel
theorem final : State.finalB (arun 40 (startA prog)).2.st = true := by decide +kernel
/-- The record of the function `f` holds `(m, E)`, and that of the module no key. -/
theorem keys : storeKeys (arun 40 (startA prog)).1 (arun 40 (startA prog)).2.A [lE] = [[(1, lE)], []] := by
  decide +kernel
/-- The stored instance is a lambda. -/
theorem stored_lam : (match arun 40 (startA prog) with
    | ⟨_, ⟨⟨.cons _ (.lam _ _), _, _⟩, _⟩⟩ => true
    | _ => false) = true := by decide +kernel
end FnInst


/-! ### A forging program by capture: it fails the initial condition

    let l = obj (w : [fld get Π(y:⊤)⊤]) {get = λ(y : ⊤). y} in
    let m = obj (z : [⊥ ⊑ z∙T, z∙T ⊑ BdT, fld forge Π(u : ⊤) z∙T])
              {class T = BdT, forge = λ(u : ⊤). path (cast l (seal z T))} in
    let r = m.forge (m : ⊤) in
    path (cast r (top (m∙T)))

The seal's owner `z` is bound after `l`, so no record of `l` admits it. -/

namespace CapRun

abbrev lT : Label := ClassEx.Forge.lT
abbrev lforge : Label := ClassEx.Forge.lforge
abbrev BdT : Ty s := ClassEx.Forge.BdT
abbrev litL : Value s := ClassEx.Forge.litL

abbrev TelM : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .bot (.sel (.var .here) lT))) (.le (.sel (.var .here) lT) BdT))
    (.fld lforge (.pi .top (.sel (.var (.there .here)) lT)))
abbrev forgeFn : Value (([],x),x) :=
  .lam .top (.path (.cast (.var (.there (.there .here))) (.seal (.var (.there .here)) lT)))
abbrev modC : Value ([],x) := .obj TelM (.fld (.cls .nil lT BdT) lforge (.fn forgeFn))
abbrev progCap : Tm [] :=
  .lett (.val litL)
    (.lett (.val modC)
      (.lett (.app (.sel (.var .here) lforge 2) (.cast (.var .here) (.top (.mu TelM))))
        (.path (.cast (.var .here) (.top (.sel (.var (.there .here)) lT))))))

theorem checks : checkTm .nil progCap .top = true := by decide +kernel
theorem progCap_scoped : Tm.SealsScoped (fun _ => false) progCap := seal_scope (checkTm_iff.1 checks) (fun x => nomatch x)
/-- The capture forgery fails the initial condition. -/
theorem init_fails : Tm.InitSeals progCap = false := by decide +kernel
/-- Every state of its run fails the predicate: the stored module keeps the forging method. -/
theorem every_state_fails : arunAll 40 (startA progCap) = List.replicate 8 false := by decide +kernel
/-- No variable of its run is recorded at `T`. -/
theorem keys : storeKeys (arun 40 (startA progCap)).1 (arun 40 (startA progCap)).2.A [lT] = [[], []] := by
  decide +kernel
end CapRun


theorem N1.kinds : arunKinds 40 (startA Class.progC) =
    ["lett", "letVal", "lett", "appId", "lett", "letVal", "letPath", "lett", "appId", "letPath", "final"] := by
  decide +kernel
theorem CastCtor.kinds : arunKinds 40 (startA CastCtor.progC') =
    ["lett", "letVal", "lett", "appId", "lett", "castPush", "castVal", "letVal-adjust", "letPath", "final"] := by
  decide +kernel
theorem Heads.kinds : kindOf Heads.stPi = "appPi" ∧ kindOf C0Ex.R2.st = "appEq" := by decide +kernel

/-! ### A dormant seal: the records are no log of executed seals

    let m = obj (z : [⊥ ⊑ z∙E, z∙E ⊑ ⊤, fld mk Π(u : ⊤) ⊤])
              {class E = ⊤, mk = λ(u : ⊤). let i = λ(y : ⊤). y in
                                           let d = λ(w : ⊤). path (cast i (trans (top Π(y:⊤)⊤) (seal z E))) in
                                           path (cast i (top Π(y:⊤)⊤))} in
    let c = m.mk (cast m ⊤) in
    path c

The lambda `d` is never called.  `prog true` holds its seal of `i` at `m∙E`, and `prog false` holds
`path (cast i (top Π(y:⊤)⊤))` in its place.  The probe is the dormant-seal probe of the review of
PR #72, with its names adapted to this module.

An allocation record tracks the class seal sites permitted by the allocating scope, including sites
inside dormant code.  It is not by itself a log of executed constructors or executed seal uses.
`allocLbl` reads the seal sites of the allocation's continuation, and `Tm.sealSite` enters lambda
bodies.  So the record of `i` holds `(m, E)` in the run of `prog true` and no key in the run of
`prog false`, although every state of the two runs has one erasure (`trace_erase_eq`).

The records depend on FCn evidence and are not in general recoverable from an erased runtime
configuration.  No path in focus, and no path of an application in focus, needs a record along the
run (`path_foci_need_no_record`).  The `let` of the dormant lambda is in focus at the seventh state
of the run and the lambda as a value at the eighth, and there the focus fails the predicate under
the empty record (`term_foci_on`).  The class query `PmadeUp` is written after the run at its final store.  It fails
the predicate under the empty record (`madeUp_empty`), so it is no path in focus of the run.  The
probe refutes no theorem of `Provenance` or `ProvenanceClass`.  It is no evidence that the front end or
its Scala entry compiles a program with a dormant seal. -/

namespace Dormant

abbrev lE : Label := .typ 50
abbrev lmk : Label := .trm 50

abbrev TelM : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .bot (.sel (.var .here) lE))) (.le (.sel (.var .here) lE) .top))
    (.fld lmk (.pi .top .top))
/-- The body of `d`: with `enabled`, the seal of `i` (index 1) at `z∙E`, `z` the module's self (index 3). -/
def deadBody (enabled : Bool) : Tm (((([],x),x),x),x) :=
  .path (.cast (.var (.there .here))
    (if enabled then .trans (.top (.pi .top .top)) (.seal (.var (.there (.there (.there .here)))) lE)
     else .top (.pi .top .top)))
/-- The method `mk`: allocate `i`, allocate `d`, return `i` at `Π(y:⊤)⊤` cast to `⊤`. -/
def mkFn (enabled : Bool) : Value ([],x) :=
  .lam .top (.lett (.val (.lam .top (.path (.var .here))))
    (.lett (.val (.lam .top (deadBody enabled)))
      (.path (.cast (.var (.there .here)) (.top (.pi .top .top))))))
def modM (enabled : Bool) : Value [] := .obj TelM (.fld (.cls .nil lE .top) lmk (.fn (mkFn enabled)))
def prog (enabled : Bool) : Tm [] :=
  .lett (.val (modM enabled))
    (.lett (.app (.sel (.var .here) lmk 2) (.cast (.var .here) (.top (.mu TelM))))
      (.path (.var .here)))

/-- Both programs are typed and meet the initial condition. -/
theorem checks_on : checkTm .nil (prog true) .top = true := by decide +kernel
theorem checks_off : checkTm .nil (prog false) .top = true := by decide +kernel
theorem init_on : Tm.InitSeals (prog true) = true := by decide +kernel
theorem init_off : Tm.InitSeals (prog false) = true := by decide +kernel
/-- The two programs erase to one runtime term. -/
theorem erase_eq : (prog true).erase = (prog false).erase := rfl
theorem kinds_on : arunKinds 40 (startA (prog true)) =
    ["lett", "letVal", "lett", "appId", "lett", "letVal", "lett", "letVal", "letPath", "final"] := by
  decide +kernel
theorem kinds_off : arunKinds 40 (startA (prog false)) = arunKinds 40 (startA (prog true)) := by
  decide +kernel
/-- With the dormant seal, the record of `i` (the middle variable) holds `(m, E)`, `m` of index 2. -/
theorem keys_on : storeKeys (arun 40 (startA (prog true))).1 (arun 40 (startA (prog true))).2.A [lE] =
    [[], [(2, lE)], []] := by decide +kernel
/-- Without it, no record holds a key at `E`. -/
theorem keys_off : storeKeys (arun 40 (startA (prog false))).1 (arun 40 (startA (prog false))).2.A [lE] =
    [[], [], []] := by decide +kernel
theorem final : State.finalB (arun 40 (startA (prog true))).2.st = true := by decide +kernel
theorem every_state : (arunAll 40 (startA (prog true))).all (· = true) = true := by decide +kernel
/-- The final states erase to one runtime configuration. -/
theorem final_erase_eq : (arun 40 (startA (prog true))).2.st.erase = (arun 40 (startA (prog false))).2.st.erase :=
  rfl

/-- The erasure of each of the first `m + 1` states of the run, oldest first. -/
def eraseTrace : Nat → (s : Sig) × AState s → List PDot.Runtime.Conf
  | 0, ⟨_, g⟩ => [g.st.erase]
  | m+1, ⟨_, g⟩ =>
      match astepOf g with
      | some p => g.st.erase :: eraseTrace m p
      | none => [g.st.erase]
/-- Every state of the two runs has one erasure. -/
theorem trace_erase_eq : eraseTrace 40 (startA (prog true)) = eraseTrace 40 (startA (prog false)) := rfl

/-- The focus path, or the two paths of an application in focus, meet the predicate under the empty record. -/
def focusNeedsNoRecord (st : State s) : Bool := match st.t with
  | .path P => PathCo.sealsOK Alloc.empty P
  | .app P Q => PathCo.sealsOK Alloc.empty P && PathCo.sealsOK Alloc.empty Q
  | _ => true
def traceFocus : Nat → (s : Sig) × AState s → List Bool
  | 0, ⟨_, g⟩ => [focusNeedsNoRecord g.st]
  | n+1, ⟨_, g⟩ => match astepOf g with
    | none => [focusNeedsNoRecord g.st]
    | some g' => focusNeedsNoRecord g.st :: traceFocus n g'
/-- No path in focus, and no path of an application in focus, needs a record along the run of
`prog true`: the seal in `d` never runs. -/
theorem path_foci_need_no_record : traceFocus 40 (startA (prog true)) = List.replicate 10 true := by
  decide +kernel

/-- Each focus term of the first `n + 1` states of the run against the empty record, oldest first. -/
def traceTerm : Nat → (s : Sig) × AState s → List Bool
  | 0, ⟨_, g⟩ => [Tm.sealsOK Alloc.empty g.st.t]
  | n+1, ⟨_, g⟩ => match astepOf g with
    | none => [Tm.sealsOK Alloc.empty g.st.t]
    | some g' => Tm.sealsOK Alloc.empty g.st.t :: traceTerm n g'
/-- The dormant lambda reaches the focus as a value: the seventh state focuses the `let` of `d` and
the eighth the value of `d`, and both fail the predicate under the empty record. -/
theorem term_foci_on : traceTerm 40 (startA (prog true)) =
    [true, true, true, true, true, true, false, false, true, true] := by decide +kernel
/-- Without the seal every focus term meets the predicate under the empty record. -/
theorem term_foci_off : traceTerm 40 (startA (prog false)) = List.replicate 10 true := by decide +kernel

/-! The class query written after the run, at its final store `[d, i, m]`. -/

abbrev S3 : Sig := ((([],x),x),x)
def at3 : (s : Sig) × AState s → Option (AState S3)
  | ⟨[.var, .var, .var], g⟩ => some g
  | _ => none
theorem at3_some : (at3 (arun 40 (startA (prog true)))).isSome = true := by decide +kernel
/-- The final state of the run of `prog true`. -/
def gF : AState S3 := (at3 (arun 40 (startA (prog true)))).get at3_some
theorem ctx_some : (Store.ctx gF.st.σ).isSome = true := by decide +kernel
def ΓF : Ctx S3 := (Store.ctx gF.st.σ).get ctx_some
/-- `cast i (trans (top Π(y:⊤)⊤) (seal m E))`: the dormant seal written as a path at the final store. -/
def PmadeUp : PathCo S3 := .cast (.var (.there .here))
  (.trans (.top (.pi .top .top)) (.seal (.var (.there (.there .here))) lE))
/-- It is typed at the class selection `m∙E`. -/
theorem madeUp_typed : synthPath ΓF PmadeUp = some (.sel (.var (.there (.there .here))) lE) := by decide +kernel
/-- It meets the predicate under the run's records, through the key of the dormant site. -/
theorem madeUp_ok : PathCo.sealsOK gF.A PmadeUp = true := by decide +kernel
/-- It fails the predicate under the empty record.  Every path in focus of the run meets it
(`path_foci_need_no_record`), so `PmadeUp` is none of them. -/
theorem madeUp_empty : PathCo.sealsOK Alloc.empty PmadeUp = false := by decide +kernel
theorem madeUp_frag : PathCo.Frag PmadeUp := Or.inl trivial

end Dormant

end ProvEx

end Nominal.FCn
