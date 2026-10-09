import Coercions.Classifiers.Frontend.Typer
import Coercions.Classifiers.Frontend.Step
import Coercions.Classifiers.DotToFCdot.Prediction
import Coercions.Classifiers.DotToFCdot.Consistency
import Coercions.Classifiers.FCdot.CheckerCompleteness

/-!
# The pipeline

`compile` takes a surface program through the whole front end.  Variants ask
for a kind or run the result.  Theorems say what the results are worth.  Each
one composes results of the Classifiers development.  The front end proves
nothing new about the calculus.

## The functions

`compile` resolves a whole program: its classifier declarations, platform,
declared use set and kind, and body.  A platform is a prefix of capture
binders, one per capability the program may use, each declared at a classifier
or at none.  The body is typed at the platform's context.

The typer elaborates, so the typed term is not the resolved one.  Box inference
may insert `□ x` and `C ⊸ x`, an unpacking `letex` may replace a `let`, and an
`unbox` gets its set filled.  `Compiled` holds the elaborated term, its use
set, its type, the derivation about its erasure, and the proof that its
skeleton is the skeleton of the resolved term.  `ATm.skel` forgets annotations,
capture sets, boxes, unboxings, ascriptions and capture binders, inlines a
`let` of a variable, and does not tell `let` from `letex`.  Equal skeletons say
that the elaborated program has the skeleton of the resolved one.

The typer synthesizes the least use set it can, and a declared use set is
binding.  When the program declares `uses C`, `compile` asks the subcapturing
goal from the synthesized set to `C` and widens the derivation by one `sub`.
The goal takes projection steps, so a declared set `{..}.only[K]` is reached
from a synthesized set that is not written as a projection.

`compile` returns the typer's `Verdict`.  `ok` carries the resolved program and
the record.  `rejected` carries a reason with its proof.  `unknown` says that
no answer and no reason was found, or that the typer reached the recursion
limit.  A declared use set that the subcapturing goal does not reach is
rejected when the certificate builder finds a level escape for that goal, and
is `unknown` otherwise.  A program that does not resolve is `unknown`.

`compileKinded` follows `compile` with the kinding goal at a kind `φ` and
returns a `CapKind` of the use set at `φ`.  `compileFiltered` asks instead that
the use set be a projection at `φ`, written `{..}.only[K]` or `{..}.except[K]`.
`Ctx.kindLe_proj` kinds a projection at `φ` in FCdot, so this route needs no
kinding goal.  `compileAndRun` follows `compile` with the machine of
`Step.lean`, from the platform's initial store, at a step budget.

## The log of level steps

`source_lvl_safety` speaks of a member-free subcapturing at a well-formed
context: one built from `refl`, `trans`, `elem`, `union`, `var`, `level`,
`unproj`, `proj` and `projMono`, with no capture member, no instance binder,
and under `proj` a kinding without `ksel`.  `levelSteps` reads off a derivation
every such subcapturing it contains, with its context and the proof that the
context is well formed.  It walks the derivation, its subtyping premises and
its kindings, and opens a context where the rule does.  At each subcapturing
premise it decides `memberFree?`.  A member-free premise is logged whole.
Otherwise the walk goes on into its parts.

## The theorems

`h : compile b Λ p = .ok ⟨r, c⟩` is a successful compile.  The platform is
`r.plat` and the compiled term is `c.tm.erase`.

* `compile_checks`, `compile_uses_checks`.  The FCdot checker accepts the
  translation and its use set evidence.
* `compile_erase`.  The translation erases to the erasure of the compiled term.
* `compile_faithful`.  `r` is the resolution of `p`.  The typer answers on
  the resolved body with the elaborated term and the type of `c`, and the use
  set of `c` is the typer's or the declared one.  The elaborated term has the
  skeleton of the resolved body, so it differs from it only where `ATm.skel`
  forgets.
* `compile_safe`, `compile_not_stuck`, `compile_run_progress`.  Every state a
  run of the compiled term reaches is final or has a step.  `compile_safe` is
  `DotMNF.dot_safety_platform` at the platform of the program, and
  `compile_not_stuck` is `DotMNF.dot_not_stuck_platform`.
* `compile_capture_prediction`.  Along any run, an FCdot state with the same
  erasure and a typed store exists.  It is reached by a run of the FCdot
  machine from the initial state of the translation, it is typed, and it uses
  no more than the translation of the use set of the result, renamed along the
  store extension.
* `compile_effect_safety`.  A platform capability `κ` that is not in the use
  set of the result is not a root, in the matched FCdot state, of a variable a
  run reads.  That state is reached from the initial state of the translation,
  is typed and reads the same variable.  Both premises
  are decided: the use set writes no projection, and `κ` is not in it.  The
  first is needed because `{κ}.only[K]` does not hold `κ` and still reaches it.
* `compile_lvl_safety`.  At every member-free subcapturing `lo <: hi` of the
  derivation, at its context `Γ`, `lo` is confined to every atom that confines
  `hi`.
* `compile_consistent`, `compile_realized`.  Every FCdot state a run of the
  translation reaches from the platform's target store has a typed store.  Its
  context proves no closed `⊤ ≤ ⊥`, and every block name of a store binder is
  defined.
* `compile_checks_get`, `compile_faithful_get`, `compile_effect_safety_get`.
  The same for a program whose compile succeeds by a decided test.  For a concrete program the kernel
  reduces the compile, and the premises close by `decide +kernel`.

With `h : compileKinded b Λ p φ = .ok ⟨r, c, k⟩`:

* `compile_kind_checks`.  The FCdot checker accepts the translation of the
  kinding.
* `compile_classified_prediction`, `compile_classified_effect_safety`,
  `compile_run_classified`.  Along any run, the matched FCdot state is reached
  from the initial state of the translation, is typed, and uses no more than
  the translated use set, which is kinded at `φ`.  Every root of a variable a
  run reads carries a classifier `φ` admits.  The last holds at the state the
  driver `run` returns.

With `h : compileFiltered b Λ p φ = .ok ⟨r, c, f⟩`:

* `compile_filtered_kindLe`, `compile_filtered_prediction`,
  `compile_filtered_effect_safety`.  The translated use set is kinded at `φ`,
  and the two classified statements follow.

Every statement has the premise `h` because it is what a caller holds.  The
content rides on the type of `c`, `k` and `f`, except in `compile_faithful`,
which reads `h` to say how `compile` built `r` and `c`.  The other premises
select what a theorem speaks of.  None of them is a hypothesis about the
compiler.

A rejection for a level escape carries a certificate that no member-free
subcapturing proves the goal the typer reached.  `certify?` builds it by
`escape_rejected_at`, and the kernel computes it.  `compile_rejected_goal` and
`TopEsc_compile_rejected` in `Examples` state two such verdicts of `compile`.
-/

namespace ClassifiersFrontend

open Classifiers
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Defs Ctx HasTy DefsTy Sub
  SubShape Subcap CapKind ESub State Step Steps Platform)

/-! ## Member-free subcapturing, decided -/

mutual

/-- A subcapturing derivation uses none of `inst`, `selLower` and `selUpper`,
and every kinding under a `proj` step uses no `ksel`.  `source_lvl_safety`
speaks of derivations without these rules. -/
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
  | .unproj => true
  | .proj g => kindMemberFree? g
  | .projMono d => memberFree? d
termination_by structural d

/-- A kinding derivation uses no `ksel`, the rule that reads a capture
member bounded by a kind. -/
def kindMemberFree? {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (g : CapKind Γ C φ) : Bool :=
  match g with
  | .nil => true
  | .cons g h => kindMemberFree? g && kindMemberFree? h
  | .kproj _ => true
  | .kcls _ _ => true
  | .kvar _ g => kindMemberFree? g
  | .kcvar _ _ g => kindMemberFree? g
  | .ksel _ => false
  | .kprojS g => kindMemberFree? g
  | .ksub g _ => kindMemberFree? g
  | .kle f g => memberFree? f && kindMemberFree? g
termination_by structural g

end

mutual

/-- `memberFree?` is sound for `Subcap.MemberFree`. -/
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
  | .unproj, _ => .unproj
  | .proj g, h => by
      simp only [memberFree?] at h
      exact .proj (kindMemberFree?_sound h)
  | .projMono d, h => by
      simp only [memberFree?] at h
      exact .projMono (memberFree?_sound h)
termination_by structural d

/-- `kindMemberFree?` is sound for `CapKind.MemberFree`. -/
theorem kindMemberFree?_sound {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    {g : CapKind Γ C φ} (h : kindMemberFree? g = true) : g.MemberFree :=
  match g, h with
  | .nil, _ => .nil
  | .cons g g', h => by
      simp only [kindMemberFree?, Bool.and_eq_true] at h
      exact .cons (kindMemberFree?_sound h.1) (kindMemberFree?_sound h.2)
  | .kproj h₁, _ => .kproj h₁
  | .kcls h₁ h₂, _ => .kcls h₁ h₂
  | .kvar hb g, h => by
      simp only [kindMemberFree?] at h
      exact .kvar hb (kindMemberFree?_sound h)
  | .kcvar hb hi g, h => by
      simp only [kindMemberFree?] at h
      exact .kcvar hb hi (kindMemberFree?_sound h)
  | .kprojS g, h => by
      simp only [kindMemberFree?] at h
      exact .kprojS (kindMemberFree?_sound h)
  | .ksub g hk, h => by
      simp only [kindMemberFree?] at h
      exact .ksub hk (kindMemberFree?_sound h)
  | .kle f g, h => by
      simp only [kindMemberFree?, Bool.and_eq_true] at h
      exact .kle (memberFree?_sound h.1) (kindMemberFree?_sound h.2)
termination_by structural g

end

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
    | .unproj => []
    | .proj g => kindSteps hwf g
    | .projMono d => subcapSteps hwf d
termination_by structural d

/-- The level steps of a kinding: those of the subcapturings it reads
through `kle`, and those of the member typings it reads through `ksel`. -/
def kindSteps {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} (hwf : Γ.Wf)
    (g : CapKind Γ C φ) : List LevelStep :=
  match g with
  | .nil => []
  | .cons g h => kindSteps hwf g ++ kindSteps hwf h
  | .kproj _ => []
  | .kcls _ _ => []
  | .kvar _ g => kindSteps hwf g
  | .kcvar _ _ g => kindSteps hwf g
  | .ksel h => hasTySteps hwf h
  | .kprojS g => kindSteps hwf g
  | .ksub g _ => kindSteps hwf g
  | .kle f g => subcapSteps hwf f ++ kindSteps hwf g
termination_by structural g

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
  | .capkI g => kindSteps hwf g
  | .capk _ => []
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

/-! ## The results of a compilation -/

/-- A program typed over a platform: the elaborated term, its use set and
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

/-- A compiled program whose use set is kinded at `φ`: every capability the
set reaches carries a classifier `φ` admits. -/
structure Kinded {s₀ : Sig} {P : Platform s₀} {a : ATm s₀} (c : Compiled P a) (φ : Cls.Kind) where
  /-- The kinding. -/
  kind : CapKind P.ctx c.use φ

/-- A compiled program whose use set is a projection at `φ`, the form a
program writes as `{..}.only[K]` or `{..}.except[K]`. -/
structure Filtered {s₀ : Sig} {P : Platform s₀} {a : ATm s₀} (c : Compiled P a) (φ : Cls.Kind) where
  /-- The set that is projected. -/
  base : CaptureSet s₀
  /-- The use set is its projection at `φ`. -/
  eq : c.use = CaptureSet.proj base φ

/-- The same compiled program at a larger use set, widened by one `sub`. -/
def Compiled.widen {s₀ : Sig} {P : Platform s₀} {a : ATm s₀} (c : Compiled P a)
    (U : CaptureSet s₀) (e : Subcap P.ctx c.use U) : Compiled P a :=
  ⟨c.tm, U, c.ty, HasTy.sub c.deriv (ESub.refl _) e, c.skel⟩

/-! ## The pipeline -/

/-- The typer on a closed term over a classified platform `P` with names `π`,
at `P`'s context.  An answer that is an existential is rejected, since no
answer inclusion leaves an existential outside every scope. -/
def synthPlat? (b : Budget) (π : PlatformNames) (P : Platform π.sig) (a : ATm π.sig) :
    Verdict (Elab P.ctx) :=
  (synthIn? b P.ctx π.set a).bind fun r =>
    match r.split with
    | .inl _ => .ok r
    | .inr q => .rejected (existentialAt P.ctx q)

/-- Type a resolved term over a classified platform and keep the result
when the skeleton is the term's. -/
def typeAt (b : Budget) (π : PlatformNames) (P : Platform π.sig) (a : ATm π.sig) :
    Verdict (Compiled P a) :=
  (synthPlat? b π P a).bind fun r =>
    match r.split with
    | .inl q =>
        if hs : ATm.skel q.tm = ATm.skel a then .ok ⟨q.tm, q.uses, q.ty, q.deriv, hs⟩
        else .unknown
    | .inr _ => .unknown

/-- Move a compiled program to its declared use set, when it declares one.
The synthesized set is kept when it is the declared one.  Otherwise the
subcapturing goal runs from it to the declared set, from a full tank of the
budget's fuel.  If it finds nothing, the goal goes to the certificate builder:
a level escape is a rejection and anything else is `unknown`. -/
def atDeclared (b : Budget) {s₀ : Sig} (P : Platform s₀) {a : ATm s₀} (c : Compiled P a) :
    Option (CaptureSet s₀) → Verdict (Compiled P a)
  | none => .ok c
  | some U =>
      if c.use = U then .ok c
      else
        match (Core.cap? P.ctx c.use U b.fuel).1 with
        | some e => .ok (c.widen U e)
        | none =>
            match certify? P.ctx c.use U with
            | some r => .rejected r
            | none => .unknown

/-- The front end end to end: resolve the program, type its body over its
classified platform, keep the result when the skeleton is the body's, and move
it to the declared use set. -/
def compile (b : Budget) (Λ : LabelTable) (p : SProg) :
    Verdict ((r : ResolvedProg p.platNames.sig) × Compiled r.plat r.body) :=
  match resolveProg Λ p with
  | none => .unknown
  | some r =>
      ((typeAt b p.platNames r.plat r.body).bind fun c => atDeclared b r.plat c r.uses).map
        fun c => ⟨r, c⟩

/-- `compile`, then the kinding goal for the use set at `φ`, from a full tank
of the budget's fuel. -/
def compileKinded (b : Budget) (Λ : LabelTable) (p : SProg) (φ : Cls.Kind) :
    Verdict ((r : ResolvedProg p.platNames.sig) × (c : Compiled r.plat r.body) × Kinded c φ) :=
  (compile b Λ p).bind fun rc =>
    match (Core.kind? rc.1.plat.ctx rc.2.use φ b.fuel).1 with
    | some g => .ok ⟨rc.1, rc.2, ⟨g⟩⟩
    | none => .unknown

/-- `compile`, then the decision that the use set is a projection at `φ`.
A program that declares `uses {..}.only[K]` reaches this form because `compile`
moves it to the declared set. -/
def compileFiltered (b : Budget) (Λ : LabelTable) (p : SProg) (φ : Cls.Kind) :
    Verdict ((r : ResolvedProg p.platNames.sig) × (c : Compiled r.plat r.body) × Filtered c φ) :=
  (compile b Λ p).bind fun rc =>
    match unprojSetW? rc.2.use with
    | some q =>
        if hφ : q.1.2 = φ then .ok ⟨rc.1, rc.2, ⟨q.1.1, hφ ▸ q.2.symm⟩⟩ else .unknown
    | none => .unknown

/-- The front end followed by the DOT-MNF machine of `Step.lean`, from the
platform's initial store, at a step budget `m`. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (p : SProg) :
    Verdict ((s : Sig) × State s) :=
  (compile b Λ p).map fun rc => run m p.platNames.sig ⟨rc.1.plat.store, .nil, rc.2.tm.erase⟩

/-- A program with no classifier, no declared use set and no declared kind,
over plain platform binders with the given names. -/
def SProg.plain (names : List String) (e : STm) : SProg :=
  ⟨[], names.map fun y => (y, none), none, none, e⟩

/-! ## Logs of results

A verdict that is not a success has the empty log. -/

/-- The log of the typer's derivation, when the verdict is a success. -/
def logOf {s : Sig} {Γ : Ctx s} (hwf : Γ.Wf) (v : Verdict (Elab Γ)) : List LevelStep :=
  match v with
  | .ok r => levelSteps hwf r.deriv
  | _ => []

/-- The log of the derivation of a compiled program, which
`compile_lvl_safety` speaks of. -/
def compileLog (b : Budget) (Λ : LabelTable) (p : SProg) : List LevelStep :=
  match compile b Λ p with
  | .ok rc => levelSteps (Platform.ctx_wf rc.1.plat) rc.2.deriv
  | _ => []

/-! ## The result of a success -/

/-- The result of a verdict that is a success. -/
def Verdict.get {α : Type} : (v : Verdict α) → v.isOk = true → α
  | .ok a, _ => a

/-- A verdict that is a success is `ok` of its result. -/
theorem Verdict.get_eq {α : Type} : ∀ (v : Verdict α) (h : v.isOk = true), v = .ok (v.get h)
  | .ok _, _ => rfl

/-- A sequence that succeeds starts with a success. -/
theorem Verdict.bind_eq_ok {α β : Type} {v : Verdict α} {f : α → Verdict β} {b : β}
    (h : v.bind f = .ok b) : ∃ a, v = .ok a ∧ f a = .ok b := by
  cases v with
  | ok a => exact ⟨a, rfl, h⟩
  | rejected _ => cases h
  | unknown => cases h

/-- A transformed success is the transform of a success. -/
theorem Verdict.map_eq_ok {α β : Type} {v : Verdict α} {f : α → β} {b : β}
    (h : v.map f = .ok b) : ∃ a, v = .ok a ∧ f a = b := by
  cases v with
  | ok a => exact ⟨a, rfl, Verdict.ok.inj h⟩
  | rejected _ => cases h
  | unknown => cases h

/-! ## The effect premise in DOT-MNF terms -/

/-- A capability is in the translation of a set only if it is in the set.
`CaptureSet.translate` keeps variables and capabilities, maps a selection to
its own atom and a projected atom to a projected atom, and drops `any` and
`fresh`. -/
theorem cvar_mem_translate {s : Sig} {κ : BVar s .cap} {C : CaptureSet s}
    (h : FCdot.CapAtom.cvar κ ∈ C.translate) : CapAtom.cvar κ ∈ C := by
  rw [DotMNF.CaptureSet.translate, List.mem_filterMap] at h
  obtain ⟨a, ha, he⟩ := h
  cases a with
  | var x => simp [DotMNF.CapAtom.translate?] at he
  | cvar κ' =>
      simp only [DotMNF.CapAtom.translate?, Option.some.injEq, FCdot.CapAtom.cvar.injEq] at he
      exact he ▸ ha
  | sel x A => simp [DotMNF.CapAtom.translate?] at he
  | any => simp [DotMNF.CapAtom.translate?] at he
  | fresh => simp [DotMNF.CapAtom.translate?] at he
  | proj b φ =>
      rw [DotMNF.CapAtom.translate?_proj] at he
      cases hb : b.translate? <;> simp [hb] at he

/-- The decided form of the effect premise.  On a set that writes no
projection, a capability the set does not hold is no root of its
translation over a platform. -/
theorem not_root_of_elem {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {κ : BVar s₀ .cap}
    (hp : noProj? U = true) (hκ : U.elem (.cvar κ) = false) :
    ¬ P.ctx.translate.Root (FCdot.CapAtom.cvar κ) U.translate :=
  P.not_root_of_not_mem _ _ (DotMNF.CaptureSet.top_not_mem_translate U)
    (DotMNF.CaptureSet.base_of_mem_translate U ((noProj?_iff U).mp hp)) fun hm => by
      have hmem := (DotMNF.CaptureSet.elem_iff (C := U)).mpr (cvar_mem_translate hm)
      rw [hκ] at hmem
      exact Bool.noConfusion hmem

/-! ## The theorems -/

-- `h` is read only by the proof of `compile_faithful`.  It is written because
-- it is what a caller holds.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {p : SProg} {r : ResolvedProg p.platNames.sig}
  {c : Compiled r.plat r.body}

/-- **The FCdot checker accepts the translation.**  `FCdot.checkTm_complete`
at the typedness of the translation under the platform's context. -/
theorem compile_checks (h : compile b Λ p = .ok ⟨r, c⟩) :
    FCdot.checkTm r.plat.ctx.translate c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (DotMNF.HasTy.translate_typed c.deriv (Platform.ctx_wf r.plat))

/-- **The FCdot checker accepts the use set evidence.**
`FCdot.checkCap_complete` at `HasTy.translate_uses`. -/
theorem compile_uses_checks (h : compile b Λ p = .ok ⟨r, c⟩) :
    FCdot.checkCap r.plat.ctx.translate c.deriv.translateUses c.deriv.translate.uses
      c.use.translate = true :=
  FCdot.checkCap_complete (c.deriv.translate_uses (Platform.ctx_wf r.plat))

/-- **The translation erases to the erasure of the compiled term.**
`HasTy.translate_erase`. -/
theorem compile_erase (h : compile b Λ p = .ok ⟨r, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase c.tm.erase :=
  DotMNF.HasTy.translate_erase c.deriv

/-- **What a compiled program is.**  `r` is what `resolveProg` makes of `p`.
The typer `synthIn?` answers on the resolved body, at the platform's context,
with the elaborated term `c.tm` and the plain type `c.ty`.  The use set is the
typer's, or the use set the program declares.  The elaborated term has the
skeleton of the resolved body.  `ATm.skel` forgets annotations, capture sets,
boxes, unboxings, ascriptions and capture binders, inlines a `let` of a
variable, and does not tell `let` from `letex`.  So these are the places where
the elaborated term may differ from the resolved one. -/
theorem compile_faithful (h : compile b Λ p = .ok ⟨r, c⟩) :
    resolveProg Λ p = some r ∧
      (∃ q : Elab r.plat.ctx, synthIn? b r.plat.ctx p.platNames.set r.body = .ok q ∧
        q.tm = c.tm ∧ q.ans = .ty c.ty ∧ (q.uses = c.use ∨ r.uses = some c.use)) ∧
      ATm.skel c.tm = ATm.skel r.body := by
  unfold compile at h
  split at h
  · cases h
  · rename_i r' hr
    obtain ⟨c', hc', he⟩ := Verdict.map_eq_ok h
    cases he
    refine ⟨hr, ?_, c.skel⟩
    obtain ⟨c0, h0, hd⟩ := Verdict.bind_eq_ok hc'
    unfold typeAt at h0
    obtain ⟨e, he, hq⟩ := Verdict.bind_eq_ok h0
    unfold synthPlat? at he
    obtain ⟨q, hq', he'⟩ := Verdict.bind_eq_ok he
    obtain ⟨tm, uses, ans, d⟩ := q
    cases ans with
    | ex C T => cases he'
    | ty T =>
      cases he'
      simp only [Elab.split] at hq
      split at hq
      · cases hq
        refine ⟨⟨tm, uses, .ty T, d⟩, hq', ?_⟩
        unfold atDeclared at hd
        split at hd
        · cases hd; exact ⟨rfl, rfl, Or.inl rfl⟩
        · rename_i U hU
          split at hd
          · cases hd; exact ⟨rfl, rfl, Or.inl rfl⟩
          · split at hd
            · cases hd; exact ⟨rfl, rfl, Or.inr hU⟩
            · split at hd <;> cases hd
      · cases hq

/-- **Safety of the compiled program over its platform.**  Every state of a run
`run'` from the platform's initial store is final or has a step.
`DotMNF.dot_safety_platform`. -/
theorem compile_safe (h : compile b Λ p = .ok ⟨r, c⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  DotMNF.dot_safety_platform r.plat c.deriv run'

/-- **No reachable state of the compiled program is stuck.**
`DotMNF.dot_not_stuck_platform`. -/
theorem compile_not_stuck (h : compile b Λ p = .ok ⟨r, c⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st) :
    ¬ State.Stuck st :=
  DotMNF.dot_not_stuck_platform r.plat c.deriv run'

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or the machine finds a step.  `compile_safe` at
the reached state, with `run_steps` and `step?_eq_none_iff`. -/
theorem compile_run_progress (h : compile b Λ p = .ok ⟨r, c⟩) (m : Nat) :
    let st := (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).2
    State.Final st ∨ (step? st).isSome := by
  intro st
  have hr : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st := run_steps m _
  rcases compile_safe h hr with hfin | hstep
  · exact Or.inl hfin
  · refine Or.inr ?_
    cases hs : step? st with
    | some _ => rfl
    | none => exact absurd hstep (step?_eq_none_iff.mp hs)

/-- **Capture prediction of the compiled program.**  Along a run `run'`, an
FCdot state with the same erasure and a typed store exists.  It is reached by a
run of the FCdot machine from the initial state of the translation, and it is
typed.  Its store extends the platform's along a renaming `ρ`, and its use set
is below the translation of the use set of the result, renamed by `ρ`.
`DotMNF.dot_capture_prediction`. -/
theorem compile_capture_prediction (h : compile b Λ p = .ok ⟨r, c⟩) {s : Sig}
    {st : State s} (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.use.translate.rename ρ) :=
  DotMNF.dot_capture_prediction r.plat c.deriv run'

/-- **Consistency along the run of the translation.**  Every FCdot state that
a run of the translation reaches from the platform's target store has a typed
store, whose context proves no closed `⊤ ≤ ⊥` at any pair of capture sets.
`DotMNF.reachable_consistent`. -/
theorem compile_consistent (h : compile b Λ p = .ok ⟨r, c⟩) {s : Sig} {st : FCdot.State s}
    (run' : FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ :
      FCdot.State p.platNames.sig) st) :
    ∃ Γ : FCdot.Ctx s, FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ (e : FCdot.LeCo s) (C C' : FCdot.CaptureSet s),
        FCdot.LeCo.HasType Γ e (.capt C .top) (.capt C' .bot) :=
  DotMNF.reachable_consistent r.plat c.deriv run'

/-- **Every block name is defined along the run of the translation.**  In the
same states, every block name of every store binder has a definition, given
by closed equality evidence.  `DotMNF.reachable_realized`. -/
theorem compile_realized (h : compile b Λ p = .ok ⟨r, c⟩) {s : Sig} {st : FCdot.State s}
    (run' : FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ :
      FCdot.State p.platNames.sig) st) :
    ∃ Γ : FCdot.Ctx s, FCdot.Store.Typed st.σ Γ ∧
      ∀ (x : BVar s .var) (ℓ : Label), ∃ W, Γ.lookupDef x ℓ = some W ∧
        FCdot.EqCo.HasType Γ (.def x ℓ) (FCdot.Shape.sel x ℓ) W :=
  DotMNF.reachable_realized r.plat c.deriv run'

/-- **Effect safety of the compiled program.**  Take a platform capability `κ`
with two decided facts about the use set of the result: `hp`, that it writes no
projection, and `hκ`, that it does not hold `κ`.  Then along a run `run'`, `κ`
is not a root of any variable `x` the reached state reads, in the matched FCdot
state, which is reached from the initial state of the translation, is typed
and reads `x`.  `DotMNF.dot_effect_safety`, whose premise follows from `hp` and
`hκ` by `not_root_of_elem`. -/
theorem compile_effect_safety (h : compile b Λ p = .ok ⟨r, c⟩) {κ : BVar p.platNames.sig .cap}
    (hp : noProj? c.use = true) (hκ : c.use.elem (.cvar κ) = false)
    {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      stt.inspects = some x ∧ FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] :=
  DotMNF.dot_effect_safety r.plat c.deriv (not_root_of_elem r.plat hp hκ) run' hin

/-- **Level safety of the compiled program.**  Take an entry of the log of the
derivation, a member-free subcapturing `lo <: hi` at its context, and an atom
`ρ` that confines `hi` at every depth of resolution.  Then `ρ` confines `lo` at
every depth too.  Each entry is `DotMNF.source_lvl_safety` at its own context. -/
theorem compile_lvl_safety (h : compile b Λ p = .ok ⟨r, c⟩) :
    ∀ ℓ ∈ levelSteps (Platform.ctx_wf r.plat) c.deriv, ∀ (ρ : FCdot.CapAtom ℓ.sig),
      (∀ m, ℓ.ctx.translate.Confined (ℓ.ctx.translate.caps m ℓ.hi.translate) ρ) →
      ∀ n, ℓ.ctx.translate.Confined (ℓ.ctx.translate.caps n ℓ.lo.translate) ρ :=
  fun ℓ _ _ hD => DotMNF.source_lvl_safety ℓ.wf ℓ.free hD

end

/-! ## The theorems at a decided compile

A concrete program is compiled by the kernel, so its success is a decided test
and needs no hypothesis. -/

section
variable {b : Budget} {Λ : LabelTable} {p : SProg}

/-- **The FCdot checker accepts the translation of a program that
compiles.**  For a concrete program the premise closes by `decide +kernel`. -/
theorem compile_checks_get (h : (compile b Λ p).isOk = true) :
    FCdot.checkTm ((compile b Λ p).get h).1.plat.ctx.translate
      ((compile b Λ p).get h).2.deriv.translate ((compile b Λ p).get h).2.ty.translate = true :=
  compile_checks (Verdict.get_eq _ h)

/-- **What a program that compiles is.**  `compile_faithful` at the record
`compile` returns, for a program whose compile succeeds by a decided test. -/
theorem compile_faithful_get (h : (compile b Λ p).isOk = true) :
    resolveProg Λ p = some ((compile b Λ p).get h).1 ∧
      (∃ q : Elab ((compile b Λ p).get h).1.plat.ctx,
        synthIn? b ((compile b Λ p).get h).1.plat.ctx p.platNames.set
          ((compile b Λ p).get h).1.body = .ok q ∧
        q.tm = ((compile b Λ p).get h).2.tm ∧ q.ans = .ty ((compile b Λ p).get h).2.ty ∧
        (q.uses = ((compile b Λ p).get h).2.use ∨
          ((compile b Λ p).get h).1.uses = some ((compile b Λ p).get h).2.use)) ∧
      ATm.skel ((compile b Λ p).get h).2.tm = ATm.skel ((compile b Λ p).get h).1.body :=
  compile_faithful (Verdict.get_eq _ h)

/-- **Effect safety of a program that compiles.**  `compile_effect_safety` at
the record `compile` returns.  For a concrete program `h`, `hp` and `hκ` close
by `decide +kernel`. -/
theorem compile_effect_safety_get (h : (compile b Λ p).isOk = true)
    {κ : BVar p.platNames.sig .cap} (hp : noProj? ((compile b Λ p).get h).2.use = true)
    (hκ : ((compile b Λ p).get h).2.use.elem (.cvar κ) = false)
    {s : Sig} {st : State s}
    (run' : Steps (⟨((compile b Λ p).get h).1.plat.store, .nil,
      ((compile b Λ p).get h).2.tm.erase⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨((compile b Λ p).get h).1.plat.targetStore, .nil,
        ((compile b Λ p).get h).2.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext ((compile b Λ p).get h).1.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] :=
  compile_effect_safety (Verdict.get_eq _ h) hp hκ run' hin

end

/-! ## The classified theorems

The kinded route: the kinding goal found a `CapKind` of the use set at `φ`,
and the primed theorems of the Classifiers development consume it.  The
filtered route: the use set is a projection at `φ`, so its translation is
kinded at `φ` by `Ctx.kindLe_proj`, and the unprimed theorems take that. -/

section
variable {b : Budget} {Λ : LabelTable} {p : SProg} {φ : Cls.Kind}
  {r : ResolvedProg p.platNames.sig} {c : Compiled r.plat r.body}

/-- **The FCdot checker accepts the translation of the kinding.**
`FCdot.checkKindCo_complete` at `CapKind.translate_typed`. -/
theorem compile_kind_checks {k : Kinded c φ} (h : compileKinded b Λ p φ = .ok ⟨r, c, k⟩) :
    FCdot.checkKindCo r.plat.ctx.translate k.kind.translate c.use.translate φ = true :=
  FCdot.checkKindCo_complete (k.kind.translate_typed (Platform.ctx_wf r.plat))

/-- **Classified prediction of a kinded program.**  Along a run `run'`, the
matched FCdot state uses no more than the translated use set, renamed, and
its use set is kinded at `φ`.  `DotMNF.dot_classified_prediction'`. -/
theorem compile_classified_prediction {k : Kinded c φ}
    (h : compileKinded b Λ p φ = .ok ⟨r, c, k⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.use.translate.rename ρ) ∧ Γ'.KindLe stt.uses φ :=
  DotMNF.dot_classified_prediction' r.plat c.deriv k.kind run'

/-- **Classified effect safety of a kinded program.**  Along a run `run'`,
every root of a variable `x` the reached state reads carries a classifier `φ`
admits.  `DotMNF.dot_classified_effect_safety'`. -/
theorem compile_classified_effect_safety {k : Kinded c φ}
    (h : compileKinded b Λ p φ = .ok ⟨r, c, k⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      stt.inspects = some x ∧ FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] → φ.Contains (Γ'.classOf a) :=
  DotMNF.dot_classified_effect_safety' r.plat c.deriv k.kind run' hin

/-- **Classified effect safety at the state the driver returns.**
`compile_classified_effect_safety` with `run_steps`. -/
theorem compile_run_classified {k : Kinded c φ} (h : compileKinded b Λ p φ = .ok ⟨r, c, k⟩)
    (m : Nat)
    {x : BVar (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).1 .var}
    (hin : (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).2.inspects = some x) :
    ∃ (stt : FCdot.State (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).1)
      (Γ' : FCdot.Ctx (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).1)
      (ρ : Rename p.platNames.sig (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).1),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      stt.inspects = some x ∧
      FCdot.State.erase stt = (run m p.platNames.sig ⟨r.plat.store, .nil, c.tm.erase⟩).2.erase ∧
        FCdot.Store.Typed stt.σ Γ' ∧ FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom _, Γ'.Root a [FCdot.CapAtom.var x] → φ.Contains (Γ'.classOf a) :=
  compile_classified_effect_safety h (run_steps m _) hin

/-- **The translated use set of a filtered program is kinded.**  A
projection at `φ` admits only what `φ` admits.  `FCdot.Ctx.kindLe_proj`
after `CaptureSet.translate_proj`. -/
theorem compile_filtered_kindLe {f : Filtered c φ}
    (h : compileFiltered b Λ p φ = .ok ⟨r, c, f⟩) :
    r.plat.ctx.translate.KindLe c.use.translate φ := by
  rw [f.eq, DotMNF.CaptureSet.translate_proj]
  exact FCdot.Ctx.kindLe_proj _ _ _

/-- **Classified prediction of a filtered program.**
`DotMNF.dot_classified_prediction` at `compile_filtered_kindLe`. -/
theorem compile_filtered_prediction {f : Filtered c φ}
    (h : compileFiltered b Λ p φ = .ok ⟨r, c, f⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.use.translate.rename ρ) ∧ Γ'.KindLe stt.uses φ :=
  DotMNF.dot_classified_prediction r.plat c.deriv (compile_filtered_kindLe h) run'

/-- **Classified effect safety of a filtered program.**
`DotMNF.dot_classified_effect_safety` at `compile_filtered_kindLe`. -/
theorem compile_filtered_effect_safety {f : Filtered c φ}
    (h : compileFiltered b Λ p φ = .ok ⟨r, c, f⟩) {s : Sig} {st : State s}
    (run' : Steps (⟨r.plat.store, .nil, c.tm.erase⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.Steps (⟨r.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State p.platNames.sig) stt ∧ (∃ V, FCdot.State.Typed stt V) ∧
      stt.inspects = some x ∧ FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext r.plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] → φ.Contains (Γ'.classOf a) :=
  DotMNF.dot_classified_effect_safety r.plat c.deriv (compile_filtered_kindLe h) run' hin

end

/-! ## Checks

The log is computed in the kernel, so its length is a decided fact.  Two open
examples have a non-empty log: the caller of `freshCell` at `Z1Ctx` and the
call `p f` at `W2CallCtx`, typed by `synthIn?` at the default fuel.  They are
not compiled programs, so they do not meet the premise of
`compile_lvl_safety`.

`Try.apply`, the first classifier example, goes through all three entry
points.  Its body is the one of `Typer.lean`, with the binders' types written
as ascriptions.  The header declares the use set `{ctl, io}.only[Control]` and
the kind `only[Control]`.  The typer synthesizes that use set, so `compile`
keeps it, and `compileFiltered` reads it as a projection.  The kinding goal
kinds it at the default fuel. -/

section Checks

open Classifiers.DotMNF.Examples

/-- `Z1Ctx` is well formed. -/
theorem Z1Ctx_wf : Z1Ctx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- `W2CallCtx` is well formed. -/
theorem W2CallCtx_wf : W2CallCtx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- The caller of `freshCell` logs twenty-three member-free subcapturings,
among them the unpacking's bound and the steps under the closure's scope. -/
example : (logOf Z1Ctx_wf (synthIn? {} Z1Ctx ps2z Z1callerAnn)).length = 23 := by
  decide +kernel

/-- The call `p f` logs six, the subcapturings of the argument's check at
the domain. -/
example : (logOf W2CallCtx_wf
    (synthIn? {} W2CallCtx ps2c (.app (.there .here) .here))).length = 6 := by
  decide +kernel

/-- `Try.apply` as a whole program: the classifiers, the platform
`[ctl : Control, io : IO]`, the declared use set and kind, and the body
with ascriptions. -/
def CE1AscProg : SProg := { CE1src with body := CE1BodySrc }

/-- It compiles at the default fuel. -/
example : (compile {} Λk CE1AscProg).isOk = true := by decide +kernel

/-- Its use set is the projection at `only[Control]`. -/
example : (compileFiltered {} Λk CE1AscProg (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-- The kinding goal kinds it at `only[Control]`. -/
example : (compileKinded {} Λk CE1AscProg (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-- Its derivation logs fifty-two member-free subcapturings. -/
example : (compileLog {} Λk CE1AscProg).length = 52 := by decide +kernel

end Checks

end ClassifiersFrontend
