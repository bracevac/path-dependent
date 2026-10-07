import Coercions.CapturesCC.Frontend.Typer
import Coercions.CapturesCC.Frontend.Step
import Coercions.CapturesCC.DotToFCdot.Prediction
import Coercions.CapturesCC.FCdot.CheckerCompleteness

/-!
# The pipeline

One function takes a surface program through the whole front end.
Thirteen theorems say what the result is worth.  Each one composes results
of the version.  The front end proves nothing about the calculus.

## The function

`compile` resolves a program over a platform, types it at the platform's
context and checks that the typer kept the program's skeleton.  A platform
is a prefix of capture binders, one per capability the program may use.
The typer elaborates.  Box inference may insert `□ x` and `C ⊸ x`, an
unpacking `letex` may replace a `let`, and an `unbox` gets its set filled.
So the typed term is not the resolved one.  `Compiled` holds the elaborated
term, its use set, its type, the derivation about its erasure, and the proof
that its skeleton is the skeleton of the resolved term.  `ATm.skel` forgets
annotations, capture sets, boxes, unboxings, ascriptions and capture
binders, inlines a `let` of a variable, and does not tell `let` from
`letex`.  So a check on skeletons says that the elaborated program is the
written one up to what the typer adds.

`compile` returns the typer's `Verdict`.  `ok` carries the record.
`rejected` carries a reason with its proof, about the written type, the goal
or the answer it names.  `unknown` says that nothing was found.  A program
that does not resolve is `unknown` too, and so is a program whose answer is
typed but whose skeleton the typer changed, which the typer never does on
the examples.

`compileAndRun` follows `compile` with the executable source machine of
`Step.lean`, from the platform's initial store, at a step budget.

## The log of level steps

`source_lvl_safety` is the version's statement about levels.  It speaks of a
member-free subcapturing at a well-formed context: one built from `refl`,
`trans`, `elem`, `union`, `var` and `level`, with no capture member and no
instance binder.  `levelSteps` reads off the derivation the typer returned
every such subcapturing it contains, together with the context it sits at
and the proof that this context is well formed.  It walks the derivation and
its subtyping premises, and opens a context exactly where the rule does: a
lambda body, an object body, a `let` and a `letex` body, the domain and the
codomain of the arrow rule, and the scope of a pack.  At each subcapturing
premise it decides `memberFree?`.  A member-free premise is logged whole.
Otherwise the walk goes on into its parts.

## The theorems

Throughout, `h : compile b Λ π e = .ok ⟨a, c⟩` is the successful compile.
The platform is `π.plat` and the compiled term is `c.tm.erase`.

* `compile_checks`.  The target checker accepts the translation of the
  derivation.  `FCdot.checkTm_complete` at `HasTy.translate_typed` and
  `Platform.ctx_wf`.
* `compile_uses_checks`.  The target checker accepts the use set evidence
  the translation emits.  `FCdot.checkCap_complete` at
  `HasTy.translate_uses`.
* `compile_erase`.  The translation erases to the compiled term.
  `HasTy.translate_erase`.
* `compile_faithful`.  The elaborated term has the skeleton of the resolved
  term.  It is the `skel` field.
* `compile_safe`.  Every state a run of the compiled term reaches is final
  or has a step.  `DotMNF.dot_safety` is stated at the empty context only,
  so this is composed at the platform from `Platform.simulatedRun`,
  `FCdot.State.Typed.steps`, `Platform.initial_typed` and
  `Simulated.progress`.
* `compile_not_stuck`.  No reachable state is stuck.  From `compile_safe`.
* `compile_run_progress`.  The state the driver `run` returns is final or
  the executable machine finds a step from it.  From `compile_safe`,
  `run_steps` and `step?_eq_none_iff`.
* `compile_capture_prediction`.  Along any run, the matched target state
  uses no more than the translation of the use set the typer found.
  `DotMNF.dot_capture_prediction`.
* `compile_effect_safety`.  A platform capability `κ` that is not in the
  use set the typer found is never the root of a variable a run reads.
  `DotMNF.dot_effect_safety`, with `cvar_mem_translate` to state the premise
  on the source set, where it is decided.
* `compile_lvl_safety`.  At every member-free subcapturing `lo <: hi` of the
  derivation of the compiled program, at the context `Γ` it sits at, `lo`
  is confined to every atom that confines `hi`, at every depth of
  resolution.  So no set leaves the scope of a root it is checked against.
  `DotMNF.source_lvl_safety` at each entry of `levelSteps`.
* `compile_rejected_goal`.  A program rejected by a level escape comes with
  a goal `C <: D` at the context `Γ` the typer reached, and no member-free
  subcapturing proves that goal.  The statement is about that goal.  It
  does not say that no other derivation types the program.
* `compile_checks_get` and `compile_effect_safety_get`.  The same as
  `compile_checks` and `compile_effect_safety`, stated for a program whose
  compile succeeds by a decided test.  For a concrete program the kernel
  reduces the compile, so `(compile b Λ π e).isOk = true` and the premise
  on the use set both close by `decide +kernel`.

The premise `h` is written in every statement because it is what a caller
holds.  The content rides on the type of `c`.  The other premises select
what a theorem speaks of: a run `r`, a read variable `hin`, a capability
`κ` with `hκ`, a log entry with its atom `ρ` and the premise on `hi`.  None
of them is a hypothesis about the compiler.

Everything here lives in `namespace CapturesCCFrontend`.  No definition is
placed in a namespace of the version, and no file of the version is touched.
-/

namespace CapturesCCFrontend

open CapturesCC
open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Defs Ctx HasTy DefsTy Sub
  SubShape Subcap ESub State Step Steps Platform)

/-! ## Member-free subcapturing, decided -/

/-- A subcapturing derivation uses none of `inst`, `selLower` and
`selUpper`.  Those three read an instance binder or a capture member, and
`source_lvl_safety` speaks of the derivations without them. -/
def memberFree? {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (d : Subcap Γ C D) : Bool :=
  match d with
  | .refl => true
  | .trans d e => memberFree? d && memberFree? e
  | .elem _ => true
  | .union d e => memberFree? d && memberFree? e
  | .var => true
  | .inst _ => false
  | .level _ _ => true
  | .selLower _ => false
  | .selUpper _ => false
termination_by structural d

/-- `memberFree?` is sound for the version's `Subcap.MemberFree`. -/
theorem memberFree?_sound {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {d : Subcap Γ C D}
    (h : memberFree? d = true) : d.MemberFree :=
  match d, h with
  | .refl, _ => .refl
  | .trans d e, h => by
      simp only [memberFree?, Bool.and_eq_true] at h
      exact .trans (memberFree?_sound h.1) (memberFree?_sound h.2)
  | .elem _, _ => .elem _
  | .union d e, h => by
      simp only [memberFree?, Bool.and_eq_true] at h
      exact .union (memberFree?_sound h.1) (memberFree?_sound h.2)
  | .var, _ => .var
  | .level h₁ h₂, _ => .level h₁ h₂
termination_by structural d

/-! ## The log of level steps -/

/-- One member-free subcapturing `lo <: hi` of a derivation, at the context
it sits at, with the proof that the context is well formed. -/
structure LevelStep where
  /-- The signature of the context. -/
  sig : Sig
  /-- The context the subcapturing sits at. -/
  ctx : Ctx sig
  /-- The context is well formed. -/
  wf : ctx.Wf
  /-- The set below. -/
  lo : CaptureSet sig
  /-- The set above. -/
  hi : CaptureSet sig
  /-- The subcapturing. -/
  deriv : Subcap ctx lo hi
  /-- It is member free. -/
  free : deriv.MemberFree

mutual

/-- The level steps of a subcapturing: itself when it is member free,
otherwise those of its parts. -/
def subcapSteps {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf) (d : Subcap Γ C D) :
    List LevelStep :=
  if hf : memberFree? d = true then [⟨s, Γ, hwf, C, D, d, memberFree?_sound hf⟩]
  else
    match d with
    | .refl => []
    | .trans d e => subcapSteps hwf d ++ subcapSteps hwf e
    | .elem _ => []
    | .union d e => subcapSteps hwf d ++ subcapSteps hwf e
    | .var => []
    | .inst _ => []
    | .level _ _ => []
    | .selLower h => hasTySteps hwf h
    | .selUpper h => hasTySteps hwf h
termination_by structural d

/-- The level steps of a shape subtyping.  The arrow rule reads its
domains under a scope and its codomains under a lambda body. -/
def subShapeSteps {s : Sig} {Γ : Ctx s} {S T : Shape s} (hwf : Γ.Wf) (d : SubShape Γ S T) :
    List LevelStep :=
  match d with
  | .top => []
  | .bot => []
  | .refl => []
  | .trans d e => subShapeSteps hwf d ++ subShapeSteps hwf e
  | .and1 => []
  | .and2 => []
  | .and d e => subShapeSteps hwf d ++ subShapeSteps hwf e
  | .fld d => subSteps hwf d
  | .typ d e => subShapeSteps hwf d ++ subShapeSteps hwf e
  | .cap f g => subcapSteps hwf f ++ subcapSteps hwf g
  | .box d => subSteps hwf d
  | .selUpper h => hasTySteps hwf h
  | .selLower h => hasTySteps hwf h
  | @SubShape.all _ _ _ T₂ _ _ d e => subSteps hwf.scope d ++ eSubSteps (hwf.body T₂) e
termination_by structural d

/-- The level steps of a subtyping: its shape half and its set half. -/
def subSteps {s : Sig} {Γ : Ctx s} {T U : Ty s} (hwf : Γ.Wf) (d : Sub Γ T U) :
    List LevelStep :=
  match d with
  | .capt d f => subShapeSteps hwf d ++ subcapSteps hwf f
termination_by structural d

/-- The level steps of an answer inclusion.  A pack reads its residual
inclusion under the pack's scope, and the congruence its bodies under a
scope. -/
def eSubSteps {s : Sig} {Γ : Ctx s} {E F : ETy s} (hwf : Γ.Wf) (d : ESub Γ E F) :
    List LevelStep :=
  match d with
  | .ty d => subSteps hwf d
  | @ESub.pack _ _ C _ _ _ f d => subcapSteps hwf f ++ subSteps (hwf.scopeInst C) d
  | .exist f d => subcapSteps hwf f ++ subSteps hwf.scope d
termination_by structural d

/-- The level steps of a typing derivation.  Each premise is read at the
context its rule gives it. -/
def hasTySteps {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {E : ETy s} (hwf : Γ.Wf)
    (d : HasTy U Γ t E) : List LevelStep :=
  match d with
  | .var => []
  | @HasTy.lam _ _ _ T₁ _ _ h _ => hasTySteps (hwf.body T₁) h
  | .app h₁ h₂ => hasTySteps hwf h₁ ++ hasTySteps hwf h₂
  | .obj h hd => defsTySteps (.consSelf (.consRoot hwf) h.literalShape (h.distinctLabels hd)) h
  | .box h => hasTySteps hwf h
  | .proj h => hasTySteps hwf h
  | .let h₁ h₂ _ => hasTySteps hwf h₁ ++ hasTySteps (.cons hwf) h₂
  | .unbox h f => hasTySteps hwf h ++ subcapSteps hwf f
  | .letex h₁ f h₂ => hasTySteps hwf h₁ ++ subcapSteps hwf f ++ hasTySteps (.cons (.consC hwf)) h₂
  | .recI h _ => hasTySteps hwf h
  | .recE h _ => hasTySteps hwf h
  | .andI h₁ h₂ => hasTySteps hwf h₁ ++ hasTySteps hwf h₂
  | .sub h e f => hasTySteps hwf h ++ eSubSteps hwf e ++ subcapSteps hwf f
termination_by structural d

/-- The level steps of a definition typing.  A term member is a typing. -/
def defsTySteps {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d : Defs s} {S : Shape s}
    (hwf : Γ.Wf) (h : DefsTy U Γ d S) : List LevelStep :=
  match h with
  | .typ => []
  | .cap => []
  | .trm h => hasTySteps hwf h
  | .and h₁ h₂ => defsTySteps hwf h₁ ++ defsTySteps hwf h₂
termination_by structural h

end

/-- The log of a derivation at a well-formed context: every member-free
subcapturing it contains, at the context it sits at. -/
def levelSteps {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {E : ETy s} (hwf : Γ.Wf)
    (d : HasTy U Γ t E) : List LevelStep :=
  hasTySteps hwf d

/-! ## The result of a compilation -/

/-- A program typed over a platform.  The elaborated term, its use set and
type, the derivation about its erasure under the platform's context, and the
proof that the elaborated term is the resolved term `a` up to what the typer
adds. -/
structure Compiled {s₀ : Sig} (P : Platform s₀) (a : ATm s₀) where
  /-- The elaborated term. -/
  tm : ATm s₀
  /-- The use set. -/
  use : CaptureSet s₀
  /-- The type. -/
  ty : Ty s₀
  /-- The derivation. -/
  deriv : HasTy use P.ctx tm.erase (.ty ty)
  /-- The elaborated term has the skeleton of the resolved one. -/
  skel : ATm.skel tm = ATm.skel a

/-! ## The pipeline -/

/-- The front end end to end: resolve over the platform, type at the
platform's context, and keep the result when the skeleton is the program's.
A rejection is the typer's, with its reason.  `unknown` is returned when the
program does not resolve, when the typer finds nothing within its budget,
and when the typer changed the program's skeleton.  The result is a
dependent pair, since the record speaks of the resolved term. -/
def compile (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Verdict ((a : ATm π.sig) × Compiled π.plat a) :=
  match resolveTop Λ π e with
  | none => .unknown
  | some a =>
      (synthTop? b π a).bind fun r =>
        match r.split with
        | .inl p =>
            if hs : ATm.skel p.tm = ATm.skel a then .ok ⟨a, ⟨p.tm, p.uses, p.ty, p.deriv, hs⟩⟩
            else .unknown
        | .inr _ => .unknown

/-- The front end followed by the source machine of `Step.lean`, from the
platform's initial store, at a step budget `m`. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Verdict ((s : Sig) × State s) :=
  (compile b Λ π e).map fun r => run m π.sig ⟨π.plat.store, .nil, r.2.tm.erase⟩

/-! ## Logs of results

The log of a typing at a well-formed context and the log of a compiled
program.  A verdict that is not a success has the empty log. -/

/-- The log of the typer's derivation, when the verdict is a success. -/
def logOf {s : Sig} {Γ : Ctx s} (hwf : Γ.Wf) (v : Verdict (Elab Γ)) : List LevelStep :=
  match v with
  | .ok r => levelSteps hwf r.deriv
  | _ => []

/-- The log of the derivation of a compiled program, the one
`compile_lvl_safety` speaks of. -/
def compileLog (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) : List LevelStep :=
  match compile b Λ π e with
  | .ok r => levelSteps (Platform.ctx_wf π.plat) r.2.deriv
  | _ => []

/-! ## The result of a success -/

/-- The result of a verdict that is a success. -/
def Verdict.get {α : Type} : (v : Verdict α) → v.isOk = true → α
  | .ok a, _ => a

/-- A verdict that is a success is `ok` of its result. -/
theorem Verdict.get_eq {α : Type} : ∀ (v : Verdict α) (h : v.isOk = true), v = .ok (v.get h)
  | .ok _, _ => rfl

/-! ## A source reading of the effect premise -/

/-- A capability is in the translation of a set only if it is in the set.
`CaptureSet.translate` keeps the variables and capabilities of a set, maps a
selection to its own atom and drops `any` and `fresh`, so no capability
appears that was not there. -/
theorem cvar_mem_translate {s : Sig} {κ : BVar s .cap} {C : CaptureSet s}
    (h : FCdot.CapAtom.cvar κ ∈ C.translate) : CapAtom.cvar κ ∈ C := by
  induction C with
  | nil => simp at h
  | cons a C ih =>
      cases a with
      | var x =>
          simp only [DotMNF.CaptureSet.translate_cons_var, List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact List.mem_cons_of_mem _ (ih h)
      | cvar κ' =>
          simp only [DotMNF.CaptureSet.translate_cons_cvar, List.mem_cons] at h
          rcases h with h | h
          · cases h; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih h)
      | sel x A =>
          simp only [DotMNF.CaptureSet.translate_cons_sel, List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact List.mem_cons_of_mem _ (ih h)
      | any =>
          simp only [DotMNF.CaptureSet.translate_cons_any] at h
          exact List.mem_cons_of_mem _ (ih h)
      | fresh =>
          simp only [DotMNF.CaptureSet.translate_cons_fresh] at h
          exact List.mem_cons_of_mem _ (ih h)

/-! ## The theorems -/

-- The premise `h` is read by no proof but the last.  It is written because
-- it is what a caller holds.  The content rides on the type of `c`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm} {a : ATm π.sig}
  {c : Compiled π.plat a}

/-- **The target checker accepts the translation.**  `FCdot.checkTm_complete`
at the typedness of the translation under the platform's context. -/
theorem compile_checks (h : compile b Λ π e = .ok ⟨a, c⟩) :
    FCdot.checkTm π.plat.ctx.translate c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (DotMNF.HasTy.translate_typed c.deriv (Platform.ctx_wf π.plat))

/-- **The target checker accepts the use set evidence.**  The translation
emits evidence that the target term uses no more than the translated use set.
`FCdot.checkCap_complete` at `HasTy.translate_uses`. -/
theorem compile_uses_checks (h : compile b Λ π e = .ok ⟨a, c⟩) :
    FCdot.checkCap π.plat.ctx.translate c.deriv.translateUses c.deriv.translate.uses
      c.use.translate = true :=
  FCdot.checkCap_complete (c.deriv.translate_uses (Platform.ctx_wf π.plat))

/-- **The translation erases to the compiled term.**  `HasTy.translate_erase`. -/
theorem compile_erase (h : compile b Λ π e = .ok ⟨a, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase c.tm.erase :=
  DotMNF.HasTy.translate_erase c.deriv

/-- **The compiled term is the written one up to what the typer adds.**  The
elaborated term has the skeleton of the resolved term. -/
theorem compile_faithful (h : compile b Λ π e = .ok ⟨a, c⟩) : ATm.skel c.tm = ATm.skel a :=
  c.skel

/-- **Safety of the compiled program over its platform.**  The subject is a run
`r` from the platform's initial store.  Every state it reaches is final or
has a step.  The matched target run of `Platform.simulatedRun` stays typed by
`FCdot.State.Typed.steps`, and `Simulated.progress` reads progress back. -/
theorem compile_safe (h : compile b Λ π e = .ok ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨stt, hrun, he, -⟩ := π.plat.simulatedRun c.deriv r
  obtain ⟨U, hU⟩ := FCdot.State.Typed.steps ⟨_, π.plat.initial_typed c.deriv⟩ hrun
  exact DotMNF.Simulated.progress ⟨stt, U, hU, he⟩

/-- **No reachable state of the compiled program is stuck.**  The subject is a
run `r` from the platform's initial store. -/
theorem compile_not_stuck (h : compile b Λ π e = .ok ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) : ¬ State.Stuck st := by
  intro ⟨hnf, hns⟩
  rcases compile_safe h r with hf | hs
  · exact hnf hf
  · exact hns hs

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or the executable machine finds a step.
`compile_safe` at the reached state, with `run_steps` for the run and
`step?_eq_none_iff` for the executable half. -/
theorem compile_run_progress (h : compile b Λ π e = .ok ⟨a, c⟩) (m : Nat) :
    let st := (run m π.sig ⟨π.plat.store, .nil, c.tm.erase⟩).2
    State.Final st ∨ (step? st).isSome := by
  intro st
  have hr : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st := run_steps m _
  rcases compile_safe h hr with hfin | hstep
  · exact Or.inl hfin
  · refine Or.inr ?_
    cases hs : step? st with
    | some _ => rfl
    | none => exact absurd hstep (step?_eq_none_iff.mp hs)

/-- **Capture prediction of the compiled program.**  The subject is a run `r`
from the platform's initial store.  A typed target state with the same
erasure exists, its store extends the platform's along a renaming `ρ`, and
its use set is below the translation of the use set the typer found, renamed
by `ρ`.  `DotMNF.dot_capture_prediction`. -/
theorem compile_capture_prediction (h : compile b Λ π e = .ok ⟨a, c⟩) {s : Sig}
    {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.use.translate.rename ρ) :=
  DotMNF.dot_capture_prediction π.plat c.deriv r

/-- **Effect safety of the compiled program.**  The subjects are a platform
capability `κ`, selected by `hκ` as one the use set the typer found does not
hold, a run `r` from the platform's initial store, and a variable `x` the
reached state reads.  Then `κ` is not a root of `x` in the matched target
state.  `DotMNF.dot_effect_safety`, whose premise on the translated set
follows from `hκ` by `cvar_mem_translate` and `CaptureSet.elem_iff`. -/
theorem compile_effect_safety (h : compile b Λ π e = .ok ⟨a, c⟩) {κ : BVar π.sig .cap}
    (hκ : c.use.elem (.cvar κ) = false)
    {s : Sig} {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] := by
  refine DotMNF.dot_effect_safety π.plat c.deriv (fun hm => ?_) r hin
  have hmem := (DotMNF.CaptureSet.elem_iff c.use).mpr (cvar_mem_translate hm)
  rw [hκ] at hmem
  exact Bool.noConfusion hmem

/-- **Level safety of the compiled program.**  The subjects are an entry
`ℓ` of the log of the derivation, a member-free subcapturing `lo <: hi` at
the context it sits at, and an atom `ρ` that confines `hi` at every depth of
resolution.  Then `ρ` confines `lo` at every depth too.  The log is computed
from the derivation by `levelSteps`, and each entry is
`DotMNF.source_lvl_safety` at its own context. -/
theorem compile_lvl_safety (h : compile b Λ π e = .ok ⟨a, c⟩) :
    ∀ ℓ ∈ levelSteps (Platform.ctx_wf π.plat) c.deriv, ∀ (ρ : FCdot.CapAtom ℓ.sig),
      (∀ m, ℓ.ctx.translate.Confined (ℓ.ctx.translate.caps m ℓ.hi.translate) ρ) →
      ∀ n, ℓ.ctx.translate.Confined (ℓ.ctx.translate.caps n ℓ.lo.translate) ρ :=
  fun ℓ _ _ hD => DotMNF.source_lvl_safety ℓ.wf ℓ.free hD

end

/-- **What a rejection by a level escape says.**  The subject is the goal
`C <: D` at the context `Γ` the typer reached, which the verdict names.  No
member-free subcapturing proves it.  The proof is the certificate the reason
carries, built by `escape_rejected_at` from `source_lvl_safety`.  It is
about that goal, not about every derivation of the program. -/
theorem compile_rejected_goal {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm}
    {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {ρ : FCdot.CapAtom s}
    {cert : ¬ ∃ d : Subcap Γ C D, d.MemberFree}
    (h : compile b Λ π e = .rejected (.levelEscape Γ C D ρ cert)) :
    ¬ ∃ d : Subcap Γ C D, d.MemberFree :=
  cert

/-! ## The theorems at a decided compile

A concrete program is compiled by the kernel, so its success is a decided
test and needs no hypothesis.  These two forms take that test and speak of
the record the compile returns. -/

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm}

/-- **The target checker accepts the translation of a program that compiles.**
`compile_checks` at the record `compile` returns.  For a concrete program the
premise closes by `decide +kernel`. -/
theorem compile_checks_get (h : (compile b Λ π e).isOk = true) :
    FCdot.checkTm π.plat.ctx.translate ((compile b Λ π e).get h).2.deriv.translate
      ((compile b Λ π e).get h).2.ty.translate = true :=
  compile_checks (Verdict.get_eq _ h)

/-- **Effect safety of a program that compiles.**  `compile_effect_safety` at
the record `compile` returns.  The subjects are as there: a capability `κ`
that `hκ` selects as absent from the use set the typer found, a run `r` and a
read variable `x`.  For a concrete program both `h` and `hκ` close by
`decide +kernel`. -/
theorem compile_effect_safety_get (h : (compile b Λ π e).isOk = true)
    {κ : BVar π.sig .cap} (hκ : ((compile b Λ π e).get h).2.use.elem (.cvar κ) = false)
    {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, ((compile b Λ π e).get h).2.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] :=
  compile_effect_safety (Verdict.get_eq _ h) hκ r hin

end

/-! ## Checks

The log is computed in the kernel, so whether it is empty is a decided
fact.  Two open examples of the version show that `compile_lvl_safety`
speaks: the caller of `freshCell` at `Z1Ctx` and the call `p f` at
`W2CallCtx`, typed by `synthIn?` at the budgets of `Typer.lean`. -/

section Checks

open CapturesCC.DotMNF.Examples

/-- `Z1Ctx` is well formed. -/
theorem Z1Ctx_wf : Z1Ctx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- `W2CallCtx` is well formed. -/
theorem W2CallCtx_wf : W2CallCtx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- The caller of `freshCell` logs twenty-three member-free subcapturings,
among them the unpacking's bound and the steps under the closure's scope. -/
example : (logOf Z1Ctx_wf (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn)).length = 23 := by
  decide +kernel

/-- The call `p f` logs six, the subcapturings of the argument's check at
the domain. -/
example : (logOf W2CallCtx_wf
    (synthIn? { decls := 0, views := 0, sub := 0, cap := 0, typer := 2, obj := 0 }
      W2CallCtx ps2c (.app (.there .here) .here))).length = 6 := by
  decide +kernel

end Checks

end CapturesCCFrontend
