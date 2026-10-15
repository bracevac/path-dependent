import Coercions.Classifiers.Frontend.Typer
import Coercions.Classifiers.Frontend.Elab
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

`compileE` resolves a whole program: its classifier declarations, platform,
declared use set and kind, and body.  A platform is a prefix of capture
binders, one per capability the program may use, each declared at a classifier
or at none.  The header resolves apart from the body, and the body resolves to
a partial term (`resolvePProg`), whose empty slots are a lambda's domain, a
literal's self shape and a field's written type.  The body is elaborated at
the platform's context (`elabProgF`, `Elab.lean`).  The elaborator returns a
candidate: the fill, which is the body with its empty slots filled, beside the
typer's own result on it.

The typer elaborates, so the typed term is not the fill.  Box inference may
insert `□ x` and `C ⊸ x`, an unpacking `letex` may replace a `let`, and an
`unbox` gets its set filled.  `Compiled` holds the elaborated term, its use
set, its type, the derivation about its erasure, and the proof that its
skeleton is the skeleton of the fill.  `ATm.skel` forgets annotations, capture
sets, boxes, unboxings, ascriptions and capture binders, inlines a `let` of a
variable, and does not tell `let` from `letex`.  Equal skeletons say that the
elaborated program is the fill up to what the typer adds.  `compileE` keeps
the result when the fill agrees with every slot the program writes
(`PTm.fills`) and the skeletons agree.

Otherwise `compileE` returns the reason the program is rejected: a missing
parameter type, a cyclic reference, a field that needs a written type,
candidates with no least type, a reason of the typer with its proof, a
mismatch, or the recursion limit.  When the elaborator finds no candidate and
no reason of its own, `fillF` fills the body along the goals the elaborator
gives its slots, and the typer's verdict on that fill names the reason, with
its proof: a level escape, an existential answer outside every scope, or a
written type outside the notation.

The typer synthesizes the least use set it can, and a declared use set is
binding.  When the program declares `uses C`, `compile` asks the subcapturing
goal from the synthesized set to `C` and widens the derivation by one `sub`.
The goal takes projection steps, so a declared set `{..}.only[K]` is reached
from a synthesized set that is not written as a projection.

`compile` returns the typer's `Verdict`, read off `compileE` (`compile_eq`).
`ok` carries the resolved program, whose body is the fill, and the record.
`rejected` carries a reason of the typer with its proof.  `unknown` says that
no answer and no such reason was found, or that the recursion limit was
reached.  A declared use set that the subcapturing goal does not reach is
rejected when the certificate builder finds a level escape for that goal, and
is `unknown` otherwise.  A program that does not resolve is `unknown`, and so
is a program whose fill or skeleton does not agree, and a program rejected for
a reason of inference alone.

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
`r.plat`, `r.body` is the fill and the compiled term is `c.tm.erase`.

* `compile_checks`, `compile_uses_checks`.  The FCdot checker accepts the
  translation and its use set evidence.
* `compile_erase`.  The translation erases to the compiled term.
* `compile_faithful`.  The elaborated term has the skeleton of the fill.
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
content rides on the type of `c`, `k` and `f`.  The other premises select what
a theorem speaks of.  None of them is a hypothesis about the compiler.

The theorems that relate a compilation to the elaborator and to the typer:

* `compile_full`.  A program whose body has every slot written compiles as the
  typer's verdict on its resolution, at the same fuel (`compileLanded`).
* `compileE_fills`.  The fill agrees with every slot the body writes, and the
  header is the resolved one.
* `compileE_skel`.  The elaborated term has the skeleton of the partial term.
* `compileE_slot`.  The four reasons that name an empty slot come only from a
  program whose body has an empty slot.
* `elabProg?_mono`, `elabProg?_stable`, `elabTop?_mono` and
  `elabTop?_stable`.  An elaboration that ends unmarked gives the same answer
  at more fuel.
* `elab_complete_direct`, `elab_complete_prog` and their `_fill` forms.  When
  every empty slot sits at a direct site (`Canon`) and the typer types the
  canonical fill, the elaborator accepts the body from some fuel on, with the
  typer's first candidate on the fill.
* `compile_complete_direct`, `compile_complete_canonAt`.  Such a program
  compiles as the typer compiles the program with the fill as its body,
  declared use set included.  A written program whose body is erased compiles
  as the written one does when `canonAt` relates the two.
-/

namespace ClassifiersFrontend

open Frontend.Fuel
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

/-- A program typed over a platform, with the fill `a` it came from: the
program with its empty slots filled.  The record holds the elaborated term,
its use set and type, the derivation about its erasure under the platform's
context, and the proof that the elaborated term is the fill up to what the
typer adds. -/
structure Compiled {s₀ : Sig} (P : Platform s₀) (a : ATm s₀) where
  /-- The elaborated term. -/
  tm : ATm s₀
  /-- The use set. -/
  use : CaptureSet s₀
  /-- The type. -/
  ty : Ty s₀
  /-- The derivation. -/
  deriv : HasTy use P.ctx tm.erase (.ty ty)
  /-- The elaborated term has the skeleton of the fill. -/
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

/-! ## The fill of a failed elaboration

When the elaborator finds no candidate and no reason of its own, the typer
may know why.  `fillF` walks the partial term as the elaborator does and fills
each empty domain with the one the elaborator takes from the goal there.  A
bound term is typed only to learn the type its variable is bound at.  A
literal holds the fill of the elaborator's first candidate.  The typer's
verdict on the fill then carries the reason and its proof. -/

/-- The goal a function part gives the body of a lambda: the codomain of a
function type, or the result part of a side. -/
def FunPart.bodyGoal {s : Sig} : FunPart s → Option (ETy (Sig.body s))
  | .direct _ _ T2 => some (Cod.underRoot T2)
  | .side _ (some V) => some (Cod.underRoot V)
  | _ => Option.none

/-- The goal the elaborator gives the bound term of a `let` whose body has no
empty slot: the dominant formal of the callee at a call argument, the
annotation read at the context at `let x : A = t in x`, and none
otherwise. -/
def boundGoalF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (tag : LetTag) (ann : Option (ETy s))
    (u : PTm (s,x)) : Fu (Option (ETy s)) :=
  match argCallee? tag ann u, u.full? with
  | some g, some _ =>
      Fu.bind (argGoalF Γ g) fun oF => Fu.ret ((oF.bind (formalGoal Γ)).map ETy.ty)
  | none, some _ =>
      match ann with
      | some A =>
          if u.isHere && (writtenAnsWhy A).isNone then
            match readAns Γ ps A with
            | .ty T => Fu.ret (some (.ty T))
            | .ex _ _ => Fu.ret none
          else Fu.ret none
      | none => Fu.ret none
  | _, none => Fu.ret none

/-- The goal of the body of a `let` under its binder: the annotation read at
the context, or else the goal of the `let`, when either is a plain type. -/
def letBodyGoal {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (ann : Option (ETy s))
    (G : Option (ETy s)) : Option (ETy (s,x)) :=
  match ann.map (readAns Γ ps), G with
  | some (.ty A), _ => some (.ty A.weaken)
  | none, some (.ty T) => some (.ty T.weaken)
  | _, _ => none

/-- The fill of a partial term along the goals the elaborator gives its
slots, structural on an index that starts at the size of the term.  A term
with no empty slot is its own fill.  A lambda without a domain takes the
domain of its goal's function part, or the dominant formal of the callee of a
body `g x`.  `none` where the elaborator would find no domain. -/
def fillF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Nat → PTm s → Option (ETy s) → Fu (Option (ATm s))
  | 0, _, _ => markAs none
  | k + 1, p, G =>
      match p.full? with
      | some a => Fu.ret (some a)
      | none =>
          match p with
          | .lam (some T) t =>
              Fu.bind (funPartOf Γ G) fun fp =>
                Fu.bind (fillF (Γ.body (readDom T)) (psBody ps) k t fp.bodyGoal) fun o =>
                  Fu.ret (o.map (.lam T))
          | .lam none t =>
              Fu.bind (funPartOf Γ G) fun fp =>
                match fp.dom? with
                | some D =>
                    Fu.bind (fillF (Γ.body (readDom D)) (psBody ps) k t fp.bodyGoal) fun o =>
                      Fu.ret (o.map (.lam D))
                | none =>
                    match calleeOf? t, t.full? with
                    | some g, some b =>
                        Fu.bind (argGoalF Γ g) fun oD => Fu.ret (oD.map fun D => .lam D b)
                    | _, _ => Fu.ret none
          | .obj o d =>
              Fu.bind (elabF Γ ps (k + 1) (.obj o d) G) fun r =>
                Fu.ret (r.1.head?.map (·.fill))
          | .let tag ann t u =>
              Fu.bind (boundGoalF Γ ps tag ann u) fun gt =>
                Fu.bind (fillF Γ ps k t gt) fun o1 =>
                  match o1 with
                  | none => Fu.ret none
                  | some f1 =>
                      match u.full? with
                      | some b => Fu.ret (some (.let ann f1 b))
                      | none =>
                          Fu.bind (synthF Γ ps f1) fun cs =>
                            match cs with
                            | [] => Fu.ret none
                            | c1 :: _ =>
                                match c1.split with
                                | .inl q =>
                                    Fu.bind (fillF (Γ.cons q.ty) (psVar ps) k u
                                        (letBodyGoal Γ ps ann G)) fun o =>
                                      Fu.ret (o.map (.let ann f1))
                                | .inr q =>
                                    Fu.bind (fillF ((Γ.consC).cons q.body) (psObj ps) k
                                        (u.rename (Rename.succ (k := .cap)).lift) none) fun o =>
                                      Fu.ret (o.map (.letex f1))
          | .letex t u =>
              Fu.bind (fillF Γ ps k t none) fun o1 =>
                match o1 with
                | none => Fu.ret none
                | some f1 =>
                    match u.full? with
                    | some b => Fu.ret (some (.letex f1 b))
                    | none =>
                        Fu.bind (synthF Γ ps f1) fun cs =>
                          match cs with
                          | [] => Fu.ret none
                          | c1 :: _ =>
                              match c1.split with
                              | .inl _ => Fu.ret none
                              | .inr q =>
                                  Fu.bind (fillF ((Γ.consC).cons q.body) (psObj ps) k u none)
                                    fun o => Fu.ret (o.map (.letex f1))
          | .asc t T =>
              Fu.bind (fillF Γ ps k t (some (.ty (readAt Γ ps T)))) fun o =>
                Fu.ret (o.map fun f => .asc f T)
          | .path _ => Fu.ret none
          | .app _ _ => Fu.ret none
          | .proj _ _ => Fu.ret none
          | .box _ => Fu.ret none
          | .unbox _ _ => Fu.ret none
termination_by structural k _ _ => k

/-- The fill of the partial body of a whole program at the context of its
platform, from a full tank of `n` units. -/
def fillProgF (n : Nat) (p : SProg) (h : ProgHeader p.platNames.sig) (q : PTm p.platNames.sig) :
    Option (ATm p.platNames.sig) :=
  (fillF h.plat.ctx p.platNames.set (sizePTm q) q none ⟨n, false⟩).1

/-- The reason of a program the elaborator rejects with no reason of its own:
the typer's reason on the fill of its body, with its proof, or else a
mismatch. -/
def fillReason (b : Budget) (p : SProg) (h : ProgHeader p.platNames.sig)
    (q : PTm p.platNames.sig) : EReason :=
  match fillProgF b.fuel p h q with
  | some a =>
      match synthPlat? b p.platNames h.plat a with
      | .rejected r => .landed r
      | _ => .mismatch
  | none => .mismatch

/-- A verdict as a result with its reason.  A rejection is a reason of the
typer, and `unknown`, which carries none, is a mismatch. -/
def exceptOf {α : Type} : Verdict α → Except EReason α
  | .ok a => .ok a
  | .rejected r => .error (.landed r)
  | .unknown => .error .mismatch

/-- Resolve the header and the partial body, elaborate the body at the
platform's context and the budget's fuel, and keep the first candidate when
its answer is a plain type, its fill agrees with every written slot, and the
elaborated term has the fill's skeleton.  The record then moves to the
declared use set, as `atDeclared` does, and the answer is the header with the
fill as its body, with the record.  Otherwise it is the reason the program is
rejected.  An existential answer is the typer's `existentialAtTop`, as
`synthPlat?` reports it.  A program out of scope or out of the tables has no
resolution, and the reason is a mismatch, which names no slot.  The result is
a dependent pair, since the record speaks of the fill. -/
def compileE (b : Budget) (Λ : LabelTable) (p : SProg) :
    Except EReason ((r : ResolvedProg p.platNames.sig) × Compiled r.plat r.body) :=
  match resolvePProg Λ p with
  | none => .error .mismatch
  | some (h, q) =>
      match (elabProgF b.fuel p h q).1 with
      | .ok c =>
          match c.e.split with
          | .inl e =>
              if q.fills c.fill = true then
                if hs : ATm.skel e.tm = ATm.skel c.fill then
                  exceptOf ((atDeclared b h.plat ⟨e.tm, e.uses, e.ty, e.deriv, hs⟩ h.uses).map
                    fun c' => (⟨h.withBody c.fill, c'⟩ :
                      (r : ResolvedProg p.platNames.sig) × Compiled r.plat r.body))
                else .error .mismatch
              else .error .mismatch
          | .inr x => .error (.landed (existentialAt h.plat.ctx x))
      | .error .mismatch => .error (fillReason b p h q)
      | .error r => .error r

/-- A result with its reason as a verdict.  A reason of the typer is a
rejection with its proof.  Any other reason is `unknown`, which carries
none. -/
def verdictOf {α : Type} : Except EReason α → Verdict α
  | .ok a => .ok a
  | .error (.landed r) => .rejected r
  | .error _ => .unknown

/-- The front end end to end: resolve, elaborate and fill, as a verdict.  A
rejection is the typer's, with its reason.  `unknown` is returned when the
program does not resolve, when the elaborator finds no answer and no reason
of the typer, when it reaches the recursion limit, when the fill or the
skeleton does not agree, and for a reason of inference alone.  The result is
a dependent pair, since the record speaks of the fill. -/
def compile (b : Budget) (Λ : LabelTable) (p : SProg) :
    Verdict ((r : ResolvedProg p.platNames.sig) × Compiled r.plat r.body) :=
  verdictOf (compileE b Λ p)

/-- The typer's verdict on a resolved program whose body has every slot
written, as a compilation: type the body over its classified platform, keep
the result when the skeleton is the body's, and move it to the declared use
set. -/
def compileLanded (b : Budget) (p : SProg) (r : ResolvedProg p.platNames.sig) :
    Verdict ((r : ResolvedProg p.platNames.sig) × Compiled r.plat r.body) :=
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

/-- **The compiled term is the written one up to what the typer adds.**  The
elaborated term has the skeleton of the body `r` holds, the fill: the resolved
body with its empty slots filled. -/
theorem compile_faithful (h : compile b Λ p = .ok ⟨r, c⟩) : ATm.skel c.tm = ATm.skel r.body :=
  c.skel

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

/-! ## Inference and the typer

The theorems that relate a compilation to the elaborator and to the typer. -/

/-- A partial term has at least one node. -/
theorem sizePTm_pos {s : Sig} (p : PTm s) : 0 < sizePTm p := by
  cases p <;> simp only [sizePTm] <;> omega

/-- The size of a partial term as a successor. -/
theorem sizePTm_succ {s : Sig} (p : PTm s) : sizePTm p = (sizePTm p - 1) + 1 := by
  have := sizePTm_pos p
  omega

/-- A term with no empty slot is its own fill. -/
theorem fillF_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) {p : PTm s} {a : ATm s}
    (h : p.full? = some a) (k : Nat) (G : Option (ETy s)) :
    fillF Γ ps (k + 1) p G = Fu.ret (some a) := by
  unfold fillF
  simp only [h]

/-- The body of a program with no empty slot is its own fill. -/
theorem fillProgF_full {n : Nat} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a : ATm p.platNames.sig} (hf : q.full? = some a) :
    fillProgF n p h q = some a := by
  unfold fillProgF
  rw [sizePTm_succ q, fillF_full _ _ hf]
  rfl

/-- From the index the elaborator starts at, a term with no empty slot is the
typer's, with the term itself as the fill. -/
theorem elabInF_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) {p : PTm s} {a : ATm s}
    (h : p.full? = some a) (n : Nat) :
    elabInF Γ ps p n = fullInfer Γ ps a none ⟨n, false⟩ := by
  unfold elabInF
  rw [sizePTm_succ p, elabF_full _ _ h]

/-- A verdict read as a result with its reason and back is the verdict. -/
theorem verdictOf_exceptOf {α : Type} (v : Verdict α) : verdictOf (exceptOf v) = v := by
  cases v <;> rfl

/-- A success of a verdict read as a result is a success of the verdict. -/
theorem exceptOf_map_ok {α β : Type} {v : Verdict α} {f : α → β} {y : β}
    (h : exceptOf (v.map f) = .ok y) : ∃ x, v = .ok x ∧ f x = y := by
  cases v with
  | ok x =>
    simp only [Verdict.map, exceptOf, Except.ok.injEq] at h
    exact ⟨x, rfl, h⟩
  | rejected r => cases h
  | unknown => cases h

/-- The reason of a verdict read as a result is the typer's or a mismatch, so
it names no slot. -/
theorem exceptOf_not_slot {α : Type} {v : Verdict α} {r : EReason}
    (h : exceptOf v = .error r) : r.isSlotReason = false := by
  cases v with
  | ok x => cases h
  | rejected r' =>
    simp only [exceptOf, Except.error.injEq] at h
    subst h
    rfl
  | unknown =>
    simp only [exceptOf, Except.error.injEq] at h
    subst h
    rfl

section
variable {b : Budget} {Λ : LabelTable} {p : SProg}

/-- `compile` is `compileE` read as a verdict. -/
theorem compile_eq (b : Budget) (Λ : LabelTable) (p : SProg) :
    compile b Λ p = verdictOf (compileE b Λ p) := rfl

/-- The typer's verdict on a term whose first candidates end unmarked with
none: a rejection or no answer, never a success. -/
theorem synthIn?_none {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s} {t : Tank}
    (ht : t.out = false) (hs : synthInF Γ ps a b.fuel = (none, t)) :
    (synthIn? b Γ ps a).isOk = false := by
  unfold synthIn?
  rw [hs]
  simp only [ht, Bool.false_eq_true, if_false]
  split <;> rfl

/-- **Every slot written: the typer, at the same fuel.**  A program that
resolves with every slot of its body written compiles as the typer's verdict
on its resolution.  The elaborator gives the typer's first candidate, and a
rejection with no reason of its own goes to the typer on the body itself. -/
theorem compile_full {r : ResolvedProg p.platNames.sig} (hr : resolveProg Λ p = some r) :
    compile b Λ p = compileLanded b p r := by
  rw [resolveProg_eq] at hr
  cases hpp : resolvePProg Λ p with
  | none =>
    rw [hpp] at hr
    cases hr
  | some hq =>
    obtain ⟨hd, q⟩ := hq
    rw [hpp, Option.bind_some] at hr
    cases hf : q.full? with
    | none =>
      rw [hf] at hr
      cases hr
    | some a =>
      rw [hf] at hr
      simp only [Option.map_some, Option.some.injEq] at hr
      subst hr
      have hfill := fillProgF_full (n := b.fuel) (p := p) (h := hd) hf
      have hfills := PTm.fills_of_full? hf
      unfold compile compileE compileLanded typeAt
      rw [hpp]
      dsimp only [ProgHeader.withBody]
      unfold elabProgF elabFirstF
      rw [elabInF_full _ _ hf]
      cases hs : inferF hd.plat.ctx p.platNames.set (sizeATm a) a none ⟨b.fuel, false⟩ with
      | mk cs t =>
        have hsyn : synthInF hd.plat.ctx p.platNames.set a b.fuel = firstCand (cs, t) := by
          unfold synthInF synthF
          rw [hs]
        cases cs with
        | nil =>
          have hfi : fullInfer hd.plat.ctx p.platNames.set a none ⟨b.fuel, false⟩ =
              (([], [.mismatch]), t) := by
            unfold fullInfer
            simp only [Fu.bind, Fu.ret, hs, List.map_nil, List.isEmpty_nil, if_true]
          rw [hfi]
          dsimp only
          cases ht : t.out with
          | true =>
            unfold synthPlat? synthIn?
            rw [hsyn]
            simp [firstCand, ht, Frontend.Reason.Reason.top, verdictOf, Verdict.bind, Verdict.map]
          | false =>
            have hn := synthIn?_none (b := b) ht (by rw [hsyn]; rfl)
            simp only [Frontend.Reason.Reason.top, Bool.false_eq_true, if_false]
            unfold fillReason
            rw [hfill]
            dsimp only
            have hp : (synthPlat? b p.platNames hd.plat a).isOk = false := by
              unfold synthPlat?
              cases hv : synthIn? b hd.plat.ctx p.platNames.set a with
              | ok r => rw [hv] at hn; cases hn
              | rejected r => rfl
              | unknown => rfl
            cases hv : synthPlat? b p.platNames hd.plat a with
            | ok r => rw [hv] at hp; cases hp
            | rejected r => rfl
            | unknown => rfl
        | cons c cs =>
          have hfi : fullInfer hd.plat.ctx p.platNames.set a none ⟨b.fuel, false⟩ =
              (((c :: cs).map fun e => (⟨a, e⟩ : ECand hd.plat.ctx), []), t) := by
            unfold fullInfer
            simp only [Fu.bind, Fu.ret, hs, List.isEmpty_cons, Bool.false_eq_true, if_false]
          rw [hfi]
          cases ht : t.out with
          | true =>
            unfold synthPlat? synthIn?
            rw [hsyn]
            simp [firstCand, ht, verdictOf, Verdict.bind, Verdict.map]
          | false =>
            unfold synthPlat? synthIn?
            rw [hsyn]
            simp only [firstCand, ht, Bool.false_eq_true, if_false, List.map_cons]
            cases hc : c.split with
            | inl e =>
              simp only [Verdict.bind, hc, hfills, if_true]
              by_cases hk : ATm.skel e.tm = ATm.skel a
              · simp only [hk, dif_pos, verdictOf_exceptOf]
              · simp [hk, verdictOf, Verdict.map]
            | inr x =>
              simp [Verdict.bind, hc, verdictOf, Verdict.map]

/-- **Inference fills only empty slots.**  A compiled program is its resolved
header with the fill as its body, and the fill agrees with every slot the
partial body writes. -/
theorem compileE_fills {r : ResolvedProg p.platNames.sig} {c : Compiled r.plat r.body}
    (h : compileE b Λ p = .ok ⟨r, c⟩) :
    ∃ hd q, resolvePProg Λ p = some (hd, q) ∧ r = hd.withBody r.body ∧ q.fills r.body = true := by
  unfold compileE at h
  cases hp : resolvePProg Λ p with
  | none =>
    rw [hp] at h
    cases h
  | some hq =>
    obtain ⟨hd, q⟩ := hq
    rw [hp] at h
    dsimp only at h
    refine ⟨hd, q, rfl, ?_⟩
    cases he : (elabProgF b.fuel p hd q).1 with
    | error r' =>
      rw [he] at h
      cases r' <;> simp at h
    | ok c0 =>
      rw [he] at h
      dsimp only at h
      cases hs : c0.e.split with
      | inr x =>
        rw [hs] at h
        cases h
      | inl e =>
        rw [hs] at h
        dsimp only at h
        by_cases hfa : q.fills c0.fill = true
        · by_cases hk : ATm.skel e.tm = ATm.skel c0.fill
          · rw [if_pos hfa, dif_pos hk] at h
            obtain ⟨c', -, hy⟩ := exceptOf_map_ok h
            cases hy
            exact ⟨rfl, hfa⟩
          · rw [if_pos hfa, dif_neg hk] at h
            cases h
        · rw [if_neg hfa] at h
          cases h

/-- **The skeleton of the program.**  The elaborated term of a compiled program
has the skeleton of the partial body it was resolved to, which forgets every
slot. -/
theorem compileE_skel {r : ResolvedProg p.platNames.sig} {c : Compiled r.plat r.body}
    (h : compileE b Λ p = .ok ⟨r, c⟩) :
    ∃ hd q, resolvePProg Λ p = some (hd, q) ∧ ATm.skel c.tm = PTm.skel q := by
  obtain ⟨hd, q, hp, -, hf⟩ := compileE_fills h
  exact ⟨hd, q, hp, c.skel.trans (PTm.skel_of_fills hf).symm⟩

/-- The reasons of the typer on a term with no empty slot: a mismatch, or
none. -/
theorem fullInfer_reasons {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s}
    {G : Option (ETy s)} (t : Tank) : ∀ r ∈ (fullInfer Γ ps a G t).1.2, r = .mismatch := by
  intro r hr
  simp only [fullInfer, Fu.bind, Fu.ret] at hr
  split at hr
  · simp at hr
    exact hr
  · simp at hr

/-- The reason `elabFirstF` reports when the typer rejects a term with no
empty slot: the recursion limit or a mismatch. -/
theorem elabFirstF_full_error {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {q : PTm s} {a : ATm s}
    (hq : q.full? = some a) {n : Nat} {r : EReason} (h : (elabFirstF Γ ps q n).1 = .error r) :
    r = .limit ∨ r = .mismatch := by
  unfold elabFirstF at h
  have hrs := fullInfer_reasons (Γ := Γ) (ps := ps) (a := a) (G := none) ⟨n, false⟩
  rw [← elabInF_full _ _ hq] at hrs
  revert hrs h
  cases elabInF Γ ps q n with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    intro h hrs
    cases cs with
    | cons c cs =>
      cases ht : t.out <;> simp [ht] at h
      exact Or.inl h.symm
    | nil =>
      simp only [Except.error.injEq] at h
      subst h
      unfold Frontend.Reason.Reason.top
      cases ht : t.out with
      | true => exact Or.inl rfl
      | false =>
        cases rs with
        | nil => exact Or.inr rfl
        | cons r rs => exact Or.inr (hrs r (List.mem_cons_self ..))

/-- The reason of a failed elaboration handed to the typer is the typer's or a
mismatch, so it names no slot. -/
theorem fillReason_not_slot (b : Budget) (p : SProg) (h : ProgHeader p.platNames.sig)
    (q : PTm p.platNames.sig) : (fillReason b p h q).isSlotReason = false := by
  unfold fillReason
  split
  · split <;> rfl
  · rfl

/-- **The slot reasons arise only where a slot is empty.**  A program rejected
for a missing parameter type, a cyclic reference, a definition that needs a
written type, or candidates with no least type resolves to a partial body with
an empty slot. -/
theorem compileE_slot {r : EReason} (h : compileE b Λ p = .error r)
    (hr : r.isSlotReason = true) :
    ∃ hd q, resolvePProg Λ p = some (hd, q) ∧ q.full? = none := by
  unfold compileE at h
  cases hp : resolvePProg Λ p with
  | none =>
    rw [hp] at h
    cases h
    cases hr
  | some hq =>
    obtain ⟨hd, q⟩ := hq
    rw [hp] at h
    dsimp only at h
    refine ⟨hd, q, rfl, ?_⟩
    cases hf : q.full? with
    | none => rfl
    | some a =>
      exfalso
      cases he : (elabProgF b.fuel p hd q).1 with
      | error r' =>
        rw [he] at h
        rcases elabFirstF_full_error hf he with rfl | rfl
        · cases h
          cases hr
        · cases h
          rw [fillReason_not_slot] at hr
          cases hr
      | ok c =>
        rw [he] at h
        dsimp only at h
        split at h
        · split at h
          · split at h
            · rw [exceptOf_not_slot h] at hr
              cases hr
            · cases h
              cases hr
          · cases h
            cases hr
        · cases h
          cases hr

end

/-! ## The tank of an elaboration

`elabF` is framed (`elabF_framed`, `Elab.lean`), so an elaboration that ends
unmarked does the same with more fuel. -/

/-- An elaboration that ends unmarked gives the same answer at every larger
fuel.  So a rejection that ends unmarked is a rejection by the rules. -/
theorem elabFirst?_stable {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {q : PTm s} {n k : Nat}
    {r : Except EReason (ECand Γ)}
    (h : elabFirstF Γ ps q n = (r, ⟨k, false⟩)) (j : Nat) :
    (elabFirstF Γ ps q (n + j)).1 = r := by
  unfold elabFirstF elabInF at h ⊢
  cases hs : elabF Γ ps (sizePTm q) q none ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    have ht : t = ⟨k, false⟩ := by
      cases cs with
      | nil => exact (Prod.mk.inj h).2
      | cons c cs => exact (Prod.mk.inj h).2
    have hf := (elabF_framed Γ ps (sizePTm q) q none).shift _ _ _ hs (by rw [ht]) j
    have hn : (⟨n + j, false⟩ : Tank) = (⟨n, false⟩ : Tank).add j := rfl
    rw [hn, hf]
    subst ht
    cases cs with
    | nil => exact (Prod.mk.inj h).1
    | cons c cs => exact (Prod.mk.inj h).1

/-- An elaborated term ends unmarked. -/
theorem elabFirstF_ok_out {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {q : PTm s} {n : Nat}
    {c : ECand Γ} (h : (elabFirstF Γ ps q n).1 = .ok c) : (elabFirstF Γ ps q n).2.out = false := by
  unfold elabFirstF at h ⊢
  cases hs : elabInF Γ ps q n with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    cases cs with
    | nil => cases h
    | cons c' cs =>
      cases ht : t.out with
      | false => rfl
      | true =>
        simp only [ht, if_true] at h
        cases h

/-- More fuel keeps the answer of an elaboration. -/
theorem elabFirst?_mono {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {q : PTm s} {n m : Nat}
    {c : ECand Γ} (h : (elabFirstF Γ ps q n).1 = .ok c) (hnm : n ≤ m) :
    (elabFirstF Γ ps q m).1 = .ok c := by
  have ho := elabFirstF_ok_out h
  have he : elabFirstF Γ ps q n = (.ok c, ⟨(elabFirstF Γ ps q n).2.left, false⟩) := by
    rw [← h, ← ho]
  have := elabFirst?_stable he (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

/-- A closed elaboration over a platform of plain binders that ends unmarked
gives the same answer at every larger fuel. -/
theorem elabTop?_stable {n k : Nat} {π : PlatformNames} {p : PTm π.sig}
    {r : Except EReason (ECand π.plat.ctx)}
    (h : elabTopF n π p = (r, ⟨k, false⟩)) (j : Nat) : (elabTopF (n + j) π p).1 = r :=
  elabFirst?_stable h j

/-- **More fuel keeps the answer of a closed elaboration.** -/
theorem elabTop?_mono {n m : Nat} {π : PlatformNames} {p : PTm π.sig} {c : ECand π.plat.ctx}
    (h : (elabTopF n π p).1 = .ok c) (hnm : n ≤ m) : (elabTopF m π p).1 = .ok c :=
  elabFirst?_mono h hnm

/-- The elaboration of a whole program's body that ends unmarked gives the
same answer at every larger fuel. -/
theorem elabProg?_stable {n k : Nat} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {r : Except EReason (ECand h.plat.ctx)}
    (he : elabProgF n p h q = (r, ⟨k, false⟩)) (j : Nat) : (elabProgF (n + j) p h q).1 = r :=
  elabFirst?_stable he j

/-- **More fuel keeps the answer of the elaboration of a program's body.**
`compileE` elaborates the body this way. -/
theorem elabProg?_mono {n m : Nat} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {c : ECand h.plat.ctx}
    (he : (elabProgF n p h q).1 = .ok c) (hnm : n ≤ m) : (elabProgF m p h q).1 = .ok c :=
  elabFirst?_mono he hnm

/-! ## Completeness at the direct sites

The elaborator fills a lambda's domain from its goal and hands the filled term
to the typer.  At some sites this is the typer's own clause on the filled
program, after the lookups that read the goal.  At those sites inference loses
no program whose fill the typer types.

`Canon Γ ps p G a` says that `a` is the canonical fill of `p` at the goal `G`:
every empty slot of `p` is at such a site and holds what the elaborator reads
there.  The sites are a lambda without a domain whose body has no empty slot,
at a goal with a function part, the body `g x` of a lambda at a goal without
one, a lambda whose body has an empty slot at a function type or at a goal
whose function part gives the body no goal, a call argument, the bound term of
`let x : A = t in x`, an ascription, a field of a literal with a written self
shape, and a literal without a self shape at a goal that dealiases to a `μ`.
The path from the root to a slot runs through lambdas, `let`s, ascriptions and
literals.  Every candidate of the bound term of such a `let` has a plain
answer, and a slot under its binder is filled alike in the context of every
candidate.

Some sites carry a premise about the typer on the fill.  At a call argument,
at `let x : A = t in x` and at a field of a literal the elaborator keeps the
fill of its first candidate, so the typer's check of the fill must answer.  At
a call argument, at `let x : A = t in x` and at a literal typed by its goal the
elaborator stops at the first try that answers, so the typer must accept the
filled term there.  A clause that checks first and falls back to synthesis
needs the body canonical with no goal as well, unless the typer's check
answers, so that neither falls back.

`Lag R c c'` says that `c'` does what `c` does, with enough fuel.  From a tank
on which `c` ends unmarked, `c'` reaches a related answer.  `Reaches c x` says
that `c` ends unmarked at `x` from some full tank, and from every larger one
with as many more units left.  The elaborator may spend more fuel than the
typer, where it reads a goal.  It may also draw in another order: it closes
and moves each candidate of a lambda's body in turn, where the typer closes
them all and then moves them all.  A framed computation answers alike on every
tank on which it ends unmarked (`settles_unique`), so the order does not change
the answers (`settles_reorder`).

`canon_lag` proves the lag for the typer on the fill against the elaborator on
the partial term, with the same candidates in the same order, derivations
included, each with the fill beside it (`SameCands`).  The relation holds in
any context, so a platform whose binders are declared at classifiers is no
special case.  `elab_complete_first_fill` reads it at the first candidate: the
elaborator accepts a term whose canonical fill the typer types, from some fuel
on, with the typer's first candidate.  Some fuel, and not the typer's, since
the elaborator reads the goal on the same tank.  `elab_complete_direct` says
this of a closed program over plain binders, and `elab_complete_prog` of the
body of a whole program at the context of its platform.
`compile_complete_direct` adds the pipeline: when the fill agrees with every
slot the body writes, the program compiles as the typer compiles the program
with the fill as its body, declared use set and record included
(`compileLanded`).  `canonB` and `canonAt` decide the premises from one fuel,
and `compile_complete_canonAt` says that a written program whose body is
erased compiles as the written program does.

Out of reach are a lambda whose body has an empty slot at a goal whose
function part is reached through an intersection, an alias or a box, where the
elaborator checks the body against the result part and the typer synthesizes
it, a literal whose self shape the rounds form, and a `let` whose bound term has
an existential answer, whose fill is an unpacking. -/

section Complete

open Frontend.Fuel ClassifiersFrontend.Core
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (CapAtom CaptureSet Shape Ty ETy Dom Cod Ctx)
open scoped Classifiers.DotMNF

/-! ### Computations that reach an answer -/

/-- A computation that ends unmarked with `x` from a full tank of `n` units,
and from every larger full tank with as many more units left. -/
def Reaches {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, ∀ k, c ⟨n + k, false⟩ = (x, ⟨m + k, false⟩)

/-- `c'` does what `c` does, with enough fuel.  From a tank on which `c` ends
unmarked with `r`, `c'` reaches an answer related to `r`.  The fuel `c'` needs
is not tied to the fuel `c` spends. -/
def Lag {α β : Type} (R : α → β → Prop) (c : Fu α) (c' : Fu β) : Prop :=
  ∀ t r t', c t = (r, t') → t'.out = false → ∃ r', R r r' ∧ Reaches c' r'

/-- A computation that ends unmarked with `x` from some full tank.  A framed
one then reaches `x`. -/
def SettlesTo {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, c ⟨n, false⟩ = (x, ⟨m, false⟩)

section LagLemmas

variable {α β γ δ : Type}

/-- Two tanks with the same fuel and the same mark are equal. -/
theorem tank_eq {t u : Tank} (hl : t.left = u.left) (ho : t.out = u.out) : t = u := by
  cases t
  cases u
  simp_all

/-- An answer returned at no cost is reached. -/
theorem reaches_ret (x : α) : Reaches (Fu.ret x) x :=
  ⟨0, 0, fun _ => rfl⟩

/-- Reaching composes along a `bind`. -/
theorem reaches_bind {c : Fu α} {f : α → Fu β} {x : α} {y : β} (hc : Reaches c x)
    (hf : Reaches (f x) y) : Reaches (Fu.bind c f) y := by
  obtain ⟨n1, m1, h1⟩ := hc
  obtain ⟨n2, m2, h2⟩ := hf
  refine ⟨n1 + n2, m2 + m1, fun k => ?_⟩
  have e1 : (⟨n1 + n2 + k, false⟩ : Tank) = ⟨n1 + (n2 + k), false⟩ := by rw [Nat.add_assoc]
  have e2 : (⟨m1 + (n2 + k), false⟩ : Tank) = ⟨n2 + (m1 + k), false⟩ := by
    rw [Tank.mk.injEq]
    exact ⟨by omega, rfl⟩
  have e3 : (⟨m2 + (m1 + k), false⟩ : Tank) = ⟨m2 + m1 + k, false⟩ := by rw [Nat.add_assoc]
  show (match c ⟨n1 + n2 + k, false⟩ with | (a, t1) => f a t1) = _
  rw [e1, h1]
  show f x ⟨m1 + (n2 + k), false⟩ = _
  rw [e2, h2, e3]

/-- A framed computation that ends unmarked reaches its answer. -/
theorem reaches_of_run {c : Fu α} (hc : Framed c) {t : Tank} {x : α} {t' : Tank}
    (h : c t = (x, t')) (ho : t'.out = false) : Reaches c x := by
  have hto : t.out = false := hc.start h ho
  refine ⟨t.left, t'.left, fun k => ?_⟩
  have hs := hc.shift t x t' h ho k
  have e1 : t.add k = ⟨t.left + k, false⟩ := tank_eq rfl (by simp [Tank.add, hto])
  have e2 : t'.add k = ⟨t'.left + k, false⟩ := tank_eq rfl (by simp [Tank.add, ho])
  rw [e1, e2] at hs
  exact hs

/-- A framed computation that settles reaches its answer. -/
theorem reaches_settles {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) : Reaches c x := by
  obtain ⟨n, m, h⟩ := hs
  exact reaches_of_run hc h rfl

/-- A computation that reaches an answer settles there. -/
theorem settles_of_reaches {c : Fu α} {x : α} (h : Reaches c x) : SettlesTo c x := by
  obtain ⟨n, m, h⟩ := h
  exact ⟨n, m, h 0⟩

/-- A first try whose answer `ok` accepts ends `stopOr` at once. -/
theorem reaches_stop {a : β} {c : Fu β} : Reaches (stopOr true a c) a :=
  ⟨0, 0, fun _ => rfl⟩

/-- Without `stop`, `stopOr` on an unmarked tank is its second computation. -/
theorem reaches_go {a : β} {c : Fu β} {y : β} (h : Reaches c y) :
    Reaches (stopOr false a c) y := by
  obtain ⟨n, m, h⟩ := h
  exact ⟨n, m, fun k => h k⟩

/-- Two answers returned at no cost lag by nothing. -/
theorem lag_ret {R : α → β → Prop} {x : α} {y : β} (h : R x y) : Lag R (Fu.ret x) (Fu.ret y) := by
  intro t r t' hr _
  simp only [Fu.ret, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨y, h, reaches_ret y⟩

/-- Lags compose along a `bind`.  The continuations need to lag only at answers
the first computation gives on a tank it leaves unmarked. -/
theorem lag_bind {R1 : α → β → Prop} {R2 : γ → δ → Prop} {c : Fu α} {c' : Fu β}
    {f : α → Fu γ} {f' : β → Fu δ} (hc : Lag R1 c c') (hf : ∀ x, Framed (f x))
    (hff : ∀ t x t1, c t = (x, t1) → t1.out = false → ∀ y, R1 x y → Lag R2 (f x) (f' y)) :
    Lag R2 (Fu.bind c f) (Fu.bind c' f') := by
  intro t r t' h ho
  simp only [Fu.bind] at h
  cases hct : c t with
  | mk x t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf x).start h ho
    obtain ⟨y, hR1, h1⟩ := hc t x t1 hct ht1
    obtain ⟨r', hR2, h2⟩ := hff t x t1 hct ht1 y hR1 t1 r t' h ho
    exact ⟨r', hR2, reaches_bind h1 h2⟩

/-- The answer of `c`, mapped. -/
theorem lag_map {R : α → β → Prop} {c : Fu α} {g : α → β} (hc : Framed c) (h : ∀ x, R x (g x)) :
    Lag R c (Fu.bind c fun x => Fu.ret (g x)) := by
  intro t r t' hr ho
  exact ⟨g r, h r, reaches_bind (reaches_of_run hc hr ho) (reaches_ret _)⟩

/-- The answer of `c'`, mapped. -/
theorem lag_map_right {R R' : α → β → Prop} {c : Fu α} {c' : Fu β} {g : β → β}
    (h : Lag R c c') (hg : ∀ x y, R x y → R' x (g y)) :
    Lag R' c (Fu.bind c' fun y => Fu.ret (g y)) := by
  intro t r t' hr ho
  obtain ⟨r', hR, hk⟩ := h t r t' hr ho
  exact ⟨g r', hg _ _ hR, reaches_bind hk (reaches_ret _)⟩

/-- A computation that reaches an answer, run first, keeps the lag. -/
theorem lag_prefix {R : α → γ → Prop} {k : Fu α} {c : Fu β} {f : β → Fu γ} {x : β}
    (hs : Reaches c x) (hf : Lag R k (f x)) : Lag R k (Fu.bind c f) := by
  intro t r t' h ho
  obtain ⟨r', hR, hd⟩ := hf t r t' h ho
  exact ⟨r', hR, reaches_bind hs hd⟩

/-- A framed computation that settles at `x` answers `x` on every tank on which
it ends unmarked. -/
theorem settles_unique {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) {t : Tank} {r : α}
    {t' : Tank} (h : c t = (r, t')) (ho : t'.out = false) : r = x := by
  obtain ⟨n, m, hn⟩ := hs
  have hto : t.out = false := hc.start h ho
  by_cases hle : t.left ≤ n
  · have ht : (⟨n, false⟩ : Tank) = t.add (n - t.left) :=
      tank_eq (by simp [Tank.add]; omega) (by simp [Tank.add, hto])
    have := hc.shift t r t' h ho (n - t.left)
    rw [← ht, hn] at this
    exact (Prod.mk.inj this).1.symm
  · have ht : t = (⟨n, false⟩ : Tank).add (t.left - n) :=
      tank_eq (by simp [Tank.add]; omega) (by simp [Tank.add, hto])
    have := hc.shift ⟨n, false⟩ x ⟨m, false⟩ hn rfl (t.left - n)
    rw [← ht, h] at this
    exact (Prod.mk.inj this).1

/-- A computation that lags behind one that settles reaches a related answer. -/
theorem settles_lag {R : α → β → Prop} {c : Fu α} {c' : Fu β} {x : α} (h : Lag R c c')
    (hs : SettlesTo c x) : ∃ y, R x y ∧ Reaches c' y := by
  obtain ⟨n, m, hn⟩ := hs
  exact h ⟨n, false⟩ x ⟨m, false⟩ hn rfl

/-- A `bind` whose first computation is a `bind`, reassociated. -/
theorem bind_bind {c : Fu α} {f : α → Fu β} {g : β → Fu γ} :
    Fu.bind (Fu.bind c f) g = Fu.bind c (fun x => Fu.bind (f x) g) := by
  funext t
  simp only [Fu.bind]

/-- A `bind` whose first computation returns at no cost. -/
theorem bind_ret {x : α} {f : α → Fu β} : Fu.bind (Fu.ret x) f = f x := by
  funext t
  rfl

/-- A first try whose answer `ok` accepts stops `orElseW`, when the
computation it lags behind settles at an answer that the relation carries to
an accepted one. -/
theorem lag_stop {ρ : Type} {R : α → β × List ρ → Prop} {k : Fu α} {X : Fu (β × List ρ)}
    {ok : β → Bool} {Z : β × List ρ → Fu (β × List ρ)} {x : α}
    (hk : Framed k) (hX : Lag R k X) (hs : SettlesTo k x)
    (hR : ∀ y, R x y → ok y.1 = true) :
    Lag R k (Fu.bind X fun r => stopOr (ok r.1) r (Z r)) := by
  intro t r t' h ho
  have hr := settles_unique hk hs h ho
  subst hr
  obtain ⟨r', hR', hd⟩ := hX t r t' h ho
  refine ⟨r', hR', reaches_bind hd ?_⟩
  rw [hR r' hR']
  exact reaches_stop

/-! ### Answers

A framed computation that ends unmarked answers the same on every tank on
which it ends unmarked (`settles_unique`).  So the answer of a composite
computation is determined by the answers of its parts, whatever the order in
which they draw on the tank. -/

/-- The answers of the two steps of a `bind` that settles. -/
theorem settles_bind_inv {c : Fu α} {f : α → Fu β} {y : β} (hf : ∀ x, Framed (f x)) (h : SettlesTo (Fu.bind c f) y) :
    ∃ x, SettlesTo c x ∧ SettlesTo (f x) y := by
  obtain ⟨n, m, h⟩ := h
  simp only [Fu.bind] at h
  cases hct : c ⟨n, false⟩ with
  | mk x t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf x).start h rfl
    have he : t1 = ⟨t1.left, false⟩ := tank_eq rfl ht1
    refine ⟨x, ⟨n, t1.left, ?_⟩, ⟨t1.left, m, ?_⟩⟩
    · rw [hct, ← he]
    · rw [← he]
      exact h

/-- A `bind` settles where its steps do. -/
theorem settles_bind {c : Fu α} {f : α → Fu β} {x : α} {y : β} (hc : Framed c)
    (hf : ∀ x, Framed (f x)) (h1 : SettlesTo c x) (h2 : SettlesTo (f x) y) :
    SettlesTo (Fu.bind c f) y :=
  settles_of_reaches (reaches_bind (reaches_settles hc h1) (reaches_settles (hf x) h2))

/-- An answer returned at no cost is the one a run settles at. -/
theorem settles_ret_inv {x y : α} (h : SettlesTo (Fu.ret x) y) : x = y := by
  obtain ⟨n, m, h⟩ := h
  simp only [Fu.ret, Prod.mk.injEq] at h
  exact h.1

/-- A run that ends unmarked settles. -/
theorem settles_of_run {c : Fu α} (hc : Framed c) {t : Tank} {x : α} {t' : Tank}
    (h : c t = (x, t')) (ho : t'.out = false) : SettlesTo c x :=
  settles_of_reaches (reaches_of_run hc h ho)

/-- A lag read off the answers: every answer the first computation settles at
is related to one the second settles at. -/
theorem lag_of_settles {R : α → β → Prop} {c : Fu α} {c' : Fu β} (hc : Framed c)
    (hc' : Framed c') (h : ∀ x, SettlesTo c x → ∃ y, R x y ∧ SettlesTo c' y) : Lag R c c' := by
  intro t r t' hr ho
  obtain ⟨y, hR, hy⟩ := h r (settles_of_run hc hr ho)
  exact ⟨y, hR, reaches_settles hc' hy⟩

/-- The answers of a `flatMapL` over a nonempty list. -/
theorem settles_flatMapL_cons {f : α → Fu (List β)} (hf : ∀ x, Framed (f x)) {x : α}
    {xs : List α} {zs : List β} (h : SettlesTo (Fu.flatMapL f (x :: xs)) zs) :
    ∃ ys ws, SettlesTo (f x) ys ∧ SettlesTo (Fu.flatMapL f xs) ws ∧ zs = ys ++ ws := by
  simp only [Fu.flatMapL] at h
  obtain ⟨ys, h1, h2⟩ := settles_bind_inv
    (fun _ => bind_framed (flatMapL_framed hf _) fun _ => ret_framed _) h
  obtain ⟨ws, h3, h4⟩ := settles_bind_inv (fun _ => ret_framed _) h2
  exact ⟨ys, ws, h1, h3, (settles_ret_inv h4).symm⟩

/-- A `flatMapL` over a nonempty list settles where its steps do. -/
theorem settles_flatMapL_of {f : α → Fu (List β)} (hf : ∀ x, Framed (f x)) {x : α}
    {xs : List α} {ys ws : List β} (h1 : SettlesTo (f x) ys)
    (h2 : SettlesTo (Fu.flatMapL f xs) ws) : SettlesTo (Fu.flatMapL f (x :: xs)) (ys ++ ws) := by
  simp only [Fu.flatMapL]
  exact settles_bind (hf x) (fun _ => bind_framed (flatMapL_framed hf _) fun _ => ret_framed _) h1
    (settles_bind (flatMapL_framed hf _) (fun _ => ret_framed _) h2 ⟨0, 0, rfl⟩)

/-- A `flatMapL` over a list split in two is the two `flatMapL`s in turn. -/
theorem flatMapL_append {f : α → Fu (List β)} :
    ∀ l1 l2 : List α, Fu.flatMapL f (l1 ++ l2) =
      Fu.bind (Fu.flatMapL f l1) fun a => Fu.bind (Fu.flatMapL f l2) fun b => Fu.ret (a ++ b)
  | [], l2 => by
    funext t
    simp only [List.nil_append, Fu.flatMapL, Fu.bind, Fu.ret, List.nil_append]
  | x :: xs, l2 => by
    funext t
    simp only [List.cons_append, Fu.flatMapL, Fu.bind, Fu.ret]
    rw [flatMapL_append xs l2]
    simp only [Fu.bind, Fu.ret, List.append_assoc]

/-- A `flatMapL` over a mapped list. -/
theorem flatMapL_map {f : α → Fu (List β)} {g : γ → α} :
    ∀ l : List γ, Fu.flatMapL f (l.map g) = Fu.flatMapL (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, Fu.flatMapL]
    rw [flatMapL_map xs]

end LagLemmas

/-! ### The same candidates -/

/-- The elaborator's candidates are the typer's, in the same order, each with
the fill `a`. -/
def SameCands {s : Sig} {Γ : Ctx s} (a : ATm s) (cs : List (Elab Γ)) (r : Out Γ) : Prop :=
  r.1 = cs.map fun e => (⟨a, e⟩ : ECand Γ)

/-- `c'` is `c` with the fill `a` beside each candidate, and some reasons. -/
def MapsTo {s : Sig} {Γ : Ctx s} (a : ATm s) (c' : Fu (Out Γ)) (c : Fu (List (Elab Γ))) : Prop :=
  ∃ rf : List (Elab Γ) → List EReason,
    c' = Fu.bind c fun es => Fu.ret (es.map fun e => (⟨a, e⟩ : ECand Γ), rf es)

section LagLists

variable {α β γ δ ρ : Type}

/-- A computation with the fill beside each candidate lags behind the typer's. -/
theorem lag_mapsTo {s : Sig} {Γ : Ctx s} {a : ATm s} {c' : Fu (Out Γ)} {c : Fu (List (Elab Γ))}
    (hc : Framed c) (h : MapsTo a c' c) : Lag (SameCands a) c c' := by
  obtain ⟨rf, rfl⟩ := h
  exact lag_map hc fun _ => rfl

/-- The typer on a term with no empty slot, with its reasons, lags behind the
typer. -/
theorem lag_full {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (G : Option (ETy s)) :
    Lag (SameCands a) (inferF Γ ps (sizeATm a) a G) (fullInfer Γ ps a G) :=
  lag_mapsTo (inferF_framed Γ ps _ a G) ⟨_, rfl⟩

/-- The typer's `orElseL` against the elaborator's `orElseO`. -/
theorem lag_orElse {s : Sig} {Γ : Ctx s} {f : ATm s} {a b : Fu (List (Elab Γ))}
    {a' b' : Fu (Out Γ)} (ha : Lag (SameCands f) a a') (hb : Lag (SameCands f) b b')
    (hbf : Framed b) : Lag (SameCands f) (orElseL a b) (orElseO a' b') := by
  unfold orElseL orElseO
  refine lag_bind ha (fun l => ?_) ?_
  · cases l with
    | nil => exact hbf
    | cons _ _ => exact ret_framed _
  · intro _ x _ _ _ y hxy
    obtain ⟨l, rs⟩ := y
    simp only [SameCands] at hxy
    subst hxy
    cases x with
    | nil => exact lag_map_right hb fun _ _ h => h
    | cons c cs => exact lag_ret rfl

/-- The typer's `orElseL` against the elaborator's `orElseO`, when the typer's
first try settles at a candidate, so that neither runs its second try. -/
theorem lag_orElse_stop {s : Sig} {Γ : Ctx s} {f : ATm s} {a b : Fu (List (Elab Γ))}
    {a' b' : Fu (Out Γ)} {c : Elab Γ} {l : List (Elab Γ)} (ha : Lag (SameCands f) a a')
    (haf : Framed a) (hbf : Framed b) (hs : SettlesTo a (c :: l)) :
    Lag (SameCands f) (orElseL a b) (orElseO a' b') := by
  intro t r t' h ho
  unfold orElseL at h
  simp only [Fu.bind] at h
  cases hat : a t with
  | mk x t1 =>
    rw [hat] at h
    have ht1 : t1.out = false := by
      cases x with
      | nil => exact hbf.start h ho
      | cons _ _ =>
        simp only [Fu.ret, Prod.mk.injEq] at h
        rw [h.2]
        exact ho
    have hx := settles_unique haf hs hat ht1
    subst hx
    simp only [Fu.ret, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨y, hy, hry⟩ := ha t (c :: l) t1 hat ht1
    refine ⟨y, hy, ?_⟩
    unfold orElseO
    refine reaches_bind hry ?_
    obtain ⟨yl, rs⟩ := y
    simp only [SameCands] at hy
    subst hy
    exact reaches_ret _

/-- The typer's first success over a list against the elaborator's, over the
same list. -/
theorem lag_firstSome {f : α → Fu (Option γ)} {f' : α → Fu (Option δ × List ρ)} {h : γ → δ} :
    ∀ l : List α, (∀ x ∈ l, Lag (fun o r => r.1 = o.map h) (f x) (f' x)) →
      Lag (fun o r => r.1 = o.map h) (Fu.firstSome f l) (firstSomeR f' l)
  | [], _ => by
    simp only [Fu.firstSome, firstSomeR]
    exact lag_ret rfl
  | x :: xs, hf => by
    have ih := lag_firstSome xs fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    have hx := hf x (List.mem_cons_self ..)
    intro t r t' hr ho
    simp only [Fu.firstSome, Fu.orElse] at hr
    cases hat : f x t with
    | mk o1 t1 =>
      rw [hat] at hr
      cases o1 with
      | some v =>
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨r1, hR, hd⟩ := hx t (some v) t1 hat ho
        refine ⟨r1, hR, ?_⟩
        simp only [firstSomeR, orElseW]
        refine reaches_bind hd ?_
        simp only [hR, Option.map_some, Option.isSome_some]
        exact reaches_stop
      | none =>
        cases ht1 : t1.out with
        | true =>
          simp only [ht1, if_true, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [ht1] at ho
        | false =>
          simp only [ht1, Bool.false_eq_true, if_false] at hr
          obtain ⟨r1, hR1, hd1⟩ := hx t none t1 hat ht1
          obtain ⟨r2, hR2, hd2⟩ := ih t1 r t' hr ho
          refine ⟨(r2.1, r1.2 ++ r2.2), hR2, ?_⟩
          simp only [firstSomeR, orElseW]
          refine reaches_bind hd1 ?_
          simp only [hR1, Option.map_none, Option.isSome_none]
          exact reaches_go (reaches_bind hd2 (reaches_ret _))

/-- The typer's answers over a list against the elaborator's, over the same
list. -/
theorem lag_flatMap {f : α → Fu (List γ)} {f' : α → Fu (List δ × List ρ)} {h : γ → δ}
    (hfr : ∀ x, Framed (f x)) :
    ∀ l : List α, (∀ x ∈ l, Lag (fun ys r => r.1 = ys.map h) (f x) (f' x)) →
      Lag (fun ys r => r.1 = ys.map h) (Fu.flatMapL f l) (flatMapR f' l)
  | [], _ => by
    simp only [Fu.flatMapL, flatMapR]
    exact lag_ret rfl
  | x :: xs, hf => by
    have ih := lag_flatMap hfr xs fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    simp only [Fu.flatMapL, flatMapR]
    refine lag_bind (hf x (List.mem_cons_self ..))
      (fun _ => bind_framed (flatMapL_framed hfr xs) fun _ => ret_framed _) ?_
    intro _ ys1 _ _ _ r1 h1
    refine lag_bind ih (fun _ => ret_framed _) ?_
    intro _ zs _ _ _ r2 h2
    exact lag_ret (by simp only [h1, h2, List.map_append])

/-- `firstSomeR` over a mapped list. -/
theorem firstSomeR_map {f : β → Fu (Option γ × List ρ)} {g : α → β} :
    ∀ l : List α, firstSomeR f (l.map g) = firstSomeR (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, firstSomeR]
    rw [firstSomeR_map xs]

/-- `flatMapR` over a mapped list. -/
theorem flatMapR_map {f : β → Fu (List γ × List ρ)} {g : α → β} :
    ∀ l : List α, flatMapR f (l.map g) = flatMapR (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, flatMapR]
    rw [flatMapR_map xs]

/-- An answer of `mapL`, mapped once more. -/
theorem mapL_post {c : Fu (Option α)} {g : α → β} {k : β → γ} :
    mapL c (fun x => k (g x)) = Fu.bind (mapL c g) fun ys => Fu.ret (ys.map k) := by
  funext t
  simp only [mapL, Fu.bind, Fu.ret]
  cases c t with
  | mk o t1 =>
    cases o <;> rfl

/-- A `flatMapL` whose steps are mapped is the `flatMapL` mapped. -/
theorem flatMapL_post {f : α → Fu (List β)} {f' : α → Fu (List γ)} {k : β → γ}
    (hf : ∀ x, f' x = Fu.bind (f x) fun ys => Fu.ret (ys.map k)) :
    ∀ l : List α, Fu.flatMapL f' l = Fu.bind (Fu.flatMapL f l) fun ys => Fu.ret (ys.map k)
  | [] => by
    funext t
    rfl
  | x :: xs => by
    funext t
    simp only [Fu.flatMapL, hf, Fu.bind, Fu.ret]
    rw [flatMapL_post hf xs]
    cases f x t with
    | mk ys t1 =>
      simp only [Fu.bind, Fu.ret]
      cases Fu.flatMapL f xs t1 with
      | mk zs t2 => simp only [List.map_append]

/-- The candidates moved to a goal, each with the fill `a`, are the typer's
results moved there. -/
theorem finishE_mapsTo {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (a : ATm s)
    (l : List (Elab Γ)) :
    MapsTo a (finishE Γ G (l.map fun e => (⟨a, e⟩ : ECand Γ))) (finishF Γ G l) := by
  cases G with
  | none =>
    refine ⟨fun _ => [], ?_⟩
    funext t
    rfl
  | some E =>
    refine ⟨fun ys => if ys.isEmpty && !l.isEmpty then [.mismatch] else [], ?_⟩
    unfold finishE finishF
    dsimp only
    rw [flatMapL_map]
    have hp := flatMapL_post (f := fun r => mapL (subsumeF Γ r E) Checked.toElab)
      (f' := fun e => mapL (subsumeF Γ e E) fun r => (⟨a, r.toElab⟩ : ECand Γ))
      (k := fun e => (⟨a, e⟩ : ECand Γ)) (fun _ => mapL_post) l
    simp only [hp, bind_bind, bind_ret, List.isEmpty_map]

/-- The typer moves the candidates to the goal after a `let` keeps one per
use set and answer, and so does the elaborator. -/
theorem dedupEC_map {s : Sig} {Γ : Ctx s} (a : ATm s) :
    ∀ l : List (Elab Γ), dedupEC (l.map fun e => (⟨a, e⟩ : ECand Γ)) =
      (dedupE l).map fun e => (⟨a, e⟩ : ECand Γ)
  | [] => rfl
  | e :: es => by
    simp only [List.map_cons, dedupEC, dedupE, dedupEC_map a es, List.filter_map,
      List.cons.injEq, true_and]
    rfl

end LagLists

/-! ### Lambdas -/

section LamLag

variable {s : Sig} {Γ : Ctx s}

/-- The first candidate at an answer is the first candidate found at it. -/
theorem firstChecked_find (E : ETy s) : ∀ rs : List (Elab Γ),
    firstChecked rs E = (rs.find? fun r => decide (r.ans = E)).bind fun r => toChecked r E
  | [] => rfl
  | r :: rs => by
    simp only [firstChecked, List.findSome?_cons, List.find?_cons]
    by_cases h : r.ans = E
    · simp only [h, decide_true, Option.bind_some]
      cases ht : toChecked r E with
      | some c => rfl
      | none => simp [toChecked, h] at ht
    · have ht : toChecked r E = none := by simp [toChecked, h]
      simp only [ht, h, decide_false]
      exact firstChecked_find E rs

/-- The checking route of a lambda reads only the first candidate of its body
at the codomain. -/
theorem lamCheckF_one (T : Dom s) (hwf : Ty.Wf T) (C : CaptureSet s) (T1' : Dom s) (T2 : Cod s)
    {rs : List (Elab (Γ.body T))} {e : Elab (Γ.body T)}
    (h : rs.find? (fun r => decide (r.ans = Cod.underRoot T2)) = some e) :
    lamCheckF Γ T hwf C T1' T2 rs = lamCheckF Γ T hwf C T1' T2 [e] := by
  have he : e.ans = Cod.underRoot T2 := by simpa using List.find?_some h
  unfold lamCheckF
  rw [firstChecked_find, h, firstChecked_find]
  simp [he]

/-- The checking route of a lambda, with the fill beside each candidate. -/
theorem lag_lamCheck (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s) (C : CaptureSet s) (T1' : Dom s)
    (T2 : Cod s) {a : ATm (Sig.body s)} {rs : List (Elab (Γ.body T))} {r : Out (Γ.body T)}
    (hr : r.1 = rs.map fun e => (⟨a, e⟩ : ECand (Γ.body T))) :
    Lag (SameCands (.lam Tw a)) (lamCheckF Γ T hwf C T1' T2 rs)
      (lamCheckE Γ T hwf Tw C T1' T2 r) := by
  unfold lamCheckE
  rw [hr, List.find?_map]
  cases hf : rs.find? (fun r => decide (r.ans = Cod.underRoot T2)) with
  | some e =>
    have hf' : rs.find? ((fun c : ECand (Γ.body T) => decide (c.e.ans = Cod.underRoot T2)) ∘
        fun e => (⟨a, e⟩ : ECand (Γ.body T))) = some e := hf
    simp only [hf', Option.map_some]
    rw [lamCheckF_one T hwf C T1' T2 hf]
    exact lag_mapsTo (lamCheckF_framed _ _ _ _ _ _ _) ⟨_, rfl⟩
  | none =>
    have hf' : rs.find? ((fun c : ECand (Γ.body T) => decide (c.e.ans = Cod.underRoot T2)) ∘
        fun e => (⟨a, e⟩ : ECand (Γ.body T))) = none := hf
    simp only [hf', Option.map_none]
    have hc : firstChecked rs (Cod.underRoot T2) = none := by
      rw [firstChecked_find, hf]
      rfl
    unfold lamCheckF
    rw [hc]
    exact lag_ret rfl

/-- Steps over a list, each followed by a step over its answers, against all
the first steps followed by the second step over all their answers.  The two
draw on the tank in another order, and settle at the same answers when the
second step splits over an append. -/
theorem settles_reorder {α β γ δ ρ : Type} {f : α → Fu (List β)} {F : List β → Fu (List γ)}
    {h : γ → δ} (hf : ∀ x, Framed (f x)) (hF : ∀ l, Framed (F l)) (hF0 : F [] = Fu.ret [])
    (hFa : ∀ l1 l2, F (l1 ++ l2) =
      Fu.bind (F l1) fun x => Fu.bind (F l2) fun y => Fu.ret (x ++ y)) :
    ∀ (l : List α) (X : List γ), SettlesTo (Fu.bind (Fu.flatMapL f l) F) X →
      SettlesTo (flatMapR (fun x => Fu.bind (Fu.flatMapL f [x]) fun ys =>
        Fu.bind (F ys) fun zs => Fu.ret (zs.map h, ([] : List ρ))) l) (X.map h, [])
  | [], X, hX => by
    simp only [Fu.flatMapL, bind_ret, hF0] at hX
    rw [← settles_ret_inv hX]
    exact ⟨0, 0, rfl⟩
  | x :: xs, X, hX => by
    have hg : ∀ x, Framed (Fu.bind (Fu.flatMapL f [x]) fun ys =>
        Fu.bind (F ys) fun zs => Fu.ret (zs.map h, ([] : List ρ))) :=
      fun _ => bind_framed (flatMapL_framed hf _) fun _ => bind_framed (hF _) fun _ => ret_framed _
    obtain ⟨Z, hZ, hFZ⟩ := settles_bind_inv hF hX
    obtain ⟨ys, ws, h1, h2, rfl⟩ := settles_flatMapL_cons hf hZ
    rw [hFa] at hFZ
    obtain ⟨A, hA, hRest⟩ :=
      settles_bind_inv (fun _ => bind_framed (hF _) fun _ => ret_framed _) hFZ
    obtain ⟨B, hB, hAB⟩ := settles_bind_inv (fun _ => ret_framed _) hRest
    have hX' := settles_ret_inv hAB
    subst hX'
    have ih := settles_reorder (h := h) (ρ := ρ) hf hF hF0 hFa xs B
      (settles_bind (flatMapL_framed hf _) hF h2 hB)
    have hx : SettlesTo (Fu.bind (Fu.flatMapL f [x]) fun ys =>
        Fu.bind (F ys) fun zs => Fu.ret (zs.map h, ([] : List ρ))) (A.map h, []) := by
      have h1' : SettlesTo (Fu.flatMapL f [x]) ys := by
        have := settles_flatMapL_of hf (xs := []) h1 ⟨0, 0, rfl⟩
        simpa using this
      exact settles_bind (flatMapL_framed hf _)
        (fun _ => bind_framed (hF _) fun _ => ret_framed _) h1'
        (settles_bind (hF _) (fun _ => ret_framed _) hA ⟨0, 0, rfl⟩)
    simp only [flatMapR]
    refine settles_bind (hg x) (fun _ => bind_framed (flatMapR_framed hg _) fun _ => ret_framed _)
      hx ?_
    refine settles_bind (flatMapR_framed hg _) (fun _ => ret_framed _) ih ?_
    rw [List.map_append]
    exact ⟨0, 0, rfl⟩

/-- The answer goal over an append is the answer goal over each part. -/
theorem finishF_append (G : Option (ETy s)) (l1 l2 : List (Elab Γ)) :
    finishF Γ G (l1 ++ l2) =
      Fu.bind (finishF Γ G l1) fun x => Fu.bind (finishF Γ G l2) fun y => Fu.ret (x ++ y) := by
  cases G with
  | none =>
    funext t
    rfl
  | some E =>
    simp only [finishF]
    exact flatMapL_append l1 l2

/-- The synthesis route of a lambda, with the fill beside each candidate.  The
elaborator closes and moves each candidate of the body in turn, where the
typer closes them all and then moves them all.  Both settle at the same
candidates. -/
theorem lag_lamGen (T : Dom s) (hwf : Ty.Wf T) (Tw : Dom s) (G : Option (ETy s))
    {a : ATm (Sig.body s)} {rs : List (Elab (Γ.body T))} {r : Out (Γ.body T)}
    (hr : r.1 = rs.map fun e => (⟨a, e⟩ : ECand (Γ.body T))) :
    Lag (SameCands (.lam Tw a)) (Fu.bind (lamGenF Γ T hwf rs) (finishF Γ G))
      (lamGenE Γ T hwf Tw G r) := by
  refine lag_of_settles (bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _)
    (lamGenE_framed _ _ _ _ _ _) fun X hX => ?_
  unfold lamGenF at hX
  have hX' := settles_reorder (ρ := EReason)
    (h := fun e => (⟨.lam Tw a, e⟩ : ECand Γ))
    (fun _ => by
      split
      · exact mapL_framed _ (lamUsesF_framed _ _ _)
      · exact ret_framed _)
    (fun _ => finishF_framed _ _ _) (by cases G <;> rfl) (finishF_append G) rs X hX
  have hR : SettlesTo (flatMapR (fun (c : ECand (Γ.body T)) =>
      Fu.bind (lamGenF Γ T hwf [c.e]) fun es =>
        Fu.bind (finishF Γ G es) fun es' =>
          Fu.ret (es'.map fun e => (⟨.lam Tw c.fill, e⟩ : ECand Γ), ([] : List EReason))) r.1)
      (X.map fun e => (⟨.lam Tw a, e⟩ : ECand Γ), []) := by
    rw [hr, flatMapR_map]
    exact hX'
  unfold lamGenE
  refine ⟨_, ?_, settles_bind (flatMapR_framed (fun _ => bind_framed (lamGenF_framed _ _ _ _)
    fun _ => bind_framed (finishF_framed _ _ _) fun _ => ret_framed _) _)
    (fun _ => ret_framed _) hR ⟨0, 0, rfl⟩⟩
  rfl

/-- The typer's clause of a lambda. -/
theorem inferF_lam (ps : CaptureSet s) (T : Dom s) (a : ATm (Sig.body s)) (G : Option (ETy s)) :
    inferF Γ ps (sizeATm (.lam T a)) (.lam T a) G =
      if (writtenWhy (domArrow T)).isNone then
        if hwf : Ty.Wf (readDom T) then
          orElseL
            (match funGoal? G with
              | some (C, T1', T2) =>
                  Fu.bind (inferF (Γ.body (readDom T)) (psBody ps) (sizeATm a) a
                    (some (Cod.underRoot T2))) (lamCheckF Γ (readDom T) hwf C T1' T2)
              | none => Fu.ret [])
            (Fu.bind (inferF (Γ.body (readDom T)) (psBody ps) (sizeATm a) a none) fun rs =>
              Fu.bind (lamGenF Γ (readDom T) hwf rs) (finishF Γ G))
        else Fu.ret []
      else Fu.ret [] := by
  show inferF Γ ps (sizeATm a + 1) (.lam T a) G = _
  rw [inferF]
  rfl

/-- A lambda whose body has an empty slot at a function type: the typer's
clause on the filled lambda, with the fill beside each candidate.  The body
lags at the codomain, and with no goal unless the typer's check answers. -/
theorem lag_lamDirect (ps : CaptureSet s) {Tw : Dom s} {C : CaptureSet s} {T1 : Dom s}
    {T2 : Cod s} {a : ATm (Sig.body s)}
    {body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))}
    (h2 : Lag (SameCands a) (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a
      (some (Cod.underRoot T2))) (body (some (Cod.underRoot T2))))
    (hfb : ∀ hwf : Ty.Wf (readDom Tw),
      Lag (SameCands a) (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a none)
          (body none) ∨
        ∃ c l, SettlesTo (Fu.bind (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a
          (some (Cod.underRoot T2))) (lamCheckF Γ (readDom Tw) hwf C T1 T2)) (c :: l)) :
    Lag (SameCands (.lam Tw a))
      (inferF Γ ps (sizeATm (.lam Tw a)) (.lam Tw a) (some (.ty ((Shape.all T1 T2) ^ C))))
      (lamAtF Γ Tw (some (.ty ((Shape.all T1 T2) ^ C))) (.direct C T1 T2) body) := by
  rw [inferF_lam]
  unfold lamAtF
  cases hW : writtenWhy (domArrow Tw) with
  | some r =>
    simp only [Option.isNone_some, Bool.false_eq_true, if_false]
    exact lag_ret rfl
  | none =>
    simp only [Option.isNone_none, if_true]
    by_cases hwf : Ty.Wf (readDom Tw)
    · simp only [dif_pos hwf, funGoal?]
      have hc := lag_bind h2 (fun _ => lamCheckF_framed _ _ _ _ _ _ _)
        fun _ _ _ _ _ _ hy => lag_lamCheck _ hwf Tw C T1 T2 hy
      have hbf : Framed (Fu.bind (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a none)
          fun rs => Fu.bind (lamGenF Γ (readDom Tw) hwf rs)
            (finishF Γ (some (.ty ((Shape.all T1 T2) ^ C))))) :=
        bind_framed (inferF_framed _ _ _ _ _) fun _ =>
          bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _
      rcases hfb hwf with h1 | ⟨c, l, hs⟩
      · exact lag_orElse hc (lag_bind h1 (fun _ => bind_framed (lamGenF_framed _ _ _ _)
          fun _ => finishF_framed _ _ _) fun _ _ _ _ _ _ hy => lag_lamGen _ hwf Tw _ hy) hbf
      · exact lag_orElse_stop hc (bind_framed (inferF_framed _ _ _ _ _) fun _ =>
          lamCheckF_framed _ _ _ _ _ _ _) hbf hs
    · simp only [dif_neg hwf]
      exact lag_ret rfl

/-- A lambda whose body has an empty slot at a goal that is no function type
and whose function part gives the body no goal: the body synthesized, as the
typer's clause on the filled lambda does. -/
theorem lag_lamSyn (ps : CaptureSet s) {Tw : Dom s} {G : Option (ETy s)} {fp : FunPart s}
    {a : ATm (Sig.body s)} {body : Option (ETy (Sig.body s)) → Fu (Out (Γ.body (readDom Tw)))}
    (hG : funGoal? G = none) (hfp : fp.bodyGoal = none)
    (h1 : Lag (SameCands a) (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a none)
      (body none)) :
    Lag (SameCands (.lam Tw a)) (inferF Γ ps (sizeATm (.lam Tw a)) (.lam Tw a) G)
      (lamAtF Γ Tw G fp body) := by
  rw [inferF_lam]
  unfold lamAtF
  cases hW : writtenWhy (domArrow Tw) with
  | some r =>
    simp only [Option.isNone_some, Bool.false_eq_true, if_false]
    exact lag_ret rfl
  | none =>
    simp only [Option.isNone_none, if_true]
    by_cases hwf : Ty.Wf (readDom Tw)
    · simp only [dif_pos hwf, hG]
      have hb := lag_bind h1 (fun _ => bind_framed (lamGenF_framed _ _ _ _)
          fun _ => finishF_framed _ _ _) fun _ _ _ _ _ _ hy => lag_lamGen _ hwf Tw G hy
      have hbf : Framed (Fu.bind (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a none)
          fun rs => Fu.bind (lamGenF Γ (readDom Tw) hwf rs) (finishF Γ G)) :=
        bind_framed (inferF_framed _ _ _ _ _) fun _ =>
          bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _
      cases fp with
      | direct => simp [FunPart.bodyGoal] at hfp
      | side T1 V =>
        cases V with
        | some => simp [FunPart.bodyGoal] at hfp
        | none => exact lag_orElse (lag_ret rfl) hb hbf
      | none => exact lag_orElse (lag_ret rfl) hb hbf
      | bad => exact lag_orElse (lag_ret rfl) hb hbf
    · simp only [dif_neg hwf]
      exact lag_ret rfl

end LamLag

/-! ### The `let` clause -/

section LetLag

variable {s : Sig} {Γ : Ctx s}

/-- The typer's body of a `let` over a plain bound term. -/
def letBP (Γ : Ctx s) (ps : CaptureSet s) (a2 : ATm (s,x)) : BodyP Γ :=
  fun p o => inferF (Γ.cons p.ty) (psVar ps) (sizeATm a2) a2 o

/-- The typer's body of a `let` over an existential bound term. -/
def letBX (Γ : Ctx s) (ps : CaptureSet s) (a2 : ATm (s,x)) : BodyX Γ :=
  fun q o => inferF ((Γ.consC).cons q.body) (psObj ps) (sizeATm a2)
    (a2.rename (Rename.succ (k := .cap)).lift) o

/-- The typer's clause of a `let`, each step at the size of its term. -/
theorem inferF_let (ps : CaptureSet s) (ann : Option (ETy s)) (a1 : ATm s) (a2 : ATm (s,x))
    (G : Option (ETy s)) :
    inferF Γ ps (sizeATm (.let ann a1 a2)) (.let ann a1 a2) G =
      Fu.bind (inferF Γ ps (sizeATm a1) a1 none) fun r1s =>
        match ann with
        | none =>
            orElseL
              (match G with
                | some E => mapL (Fu.firstSome (fun r1 => letOneF Γ none E r1
                    (letBP Γ ps a2) (letBX Γ ps a2)) r1s) id
                | none => Fu.ret [])
              (Fu.bind (Fu.flatMapL (fun r1 => letBoundF Γ r1 (letBP Γ ps a2) (letBX Γ ps a2)) r1s)
                fun cs => finishF Γ G (dedupE cs))
        | some A =>
            if (writtenAnsWhy A).isNone then
              Fu.bind (mapL (Fu.firstSome (fun r1 => letOneF Γ (some (readAns Γ ps A))
                  (readAns Γ ps A) r1 (letBP Γ ps a2) (letBX Γ ps a2)) r1s) id) (finishF Γ G)
            else Fu.ret [] := by
  show inferF Γ ps (sizeATm a1 + sizeATm a2 + 1) (.let ann a1 a2) G = _
  have e1 : ∀ (Γ' : Ctx s) ps' G', inferF Γ' ps' (sizeATm a1 + sizeATm a2) a1 G' =
      inferF Γ' ps' (sizeATm a1) a1 G' := fun _ _ _ => inferF_index (by omega)
  have e2 : ∀ (Γ' : Ctx (s,x)) ps' G', inferF Γ' ps' (sizeATm a1 + sizeATm a2) a2 G' =
      inferF Γ' ps' (sizeATm a2) a2 G' := fun _ _ _ => inferF_index (by omega)
  have e3 : ∀ (Γ' : Ctx ((s,c),x)) ps' G',
      inferF Γ' ps' (sizeATm a1 + sizeATm a2) (a2.rename (Rename.succ (k := .cap)).lift) G' =
        inferF Γ' ps' (sizeATm a2) (a2.rename (Rename.succ (k := .cap)).lift) G' :=
    fun _ _ _ => by
      rw [inferF_index (by rw [sizeATm_rename]; omega), inferF_index (k := sizeATm a2)
        (by rw [sizeATm_rename]; omega)]
  rw [inferF]
  simp only [e1, e2, e3]
  rfl

theorem letBP_framed (ps : CaptureSet s) (a2 : ATm (s,x)) :
    ∀ p o, Framed (letBP Γ ps a2 p o) := fun _ _ => inferF_framed _ _ _ _ _

theorem letBX_framed (ps : CaptureSet s) (a2 : ATm (s,x)) :
    ∀ q o, Framed (letBX Γ ps a2 q o) := fun _ _ => inferF_framed _ _ _ _ _

/-- The goal at which the clause checks the body of a `let` at the answer
`E`: a plain `E` under the binder, and none for an existential one. -/
def letGoalE {s : Sig} : ETy s → Option (ETy (s,x))
  | .ty T => some (.ty T.weaken)
  | .ex _ _ => none

/-- The goals at which the clause checks the body of a `let`: at the written
answer read at the context, or at the goal.  With neither, none. -/
def letGoals {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Option (ETy s) → Option (ETy s) → List (Option (ETy (s,x)))
  | some A, _ => [letGoalE (readAns Γ ps A)]
  | none, some E => [letGoalE E]
  | none, none => [none]

/-- An optional answer as a list, mapped. -/
theorem listO_map {α β : Type} (f : α → β) : ∀ o : Option α, listO (o.map f) = (listO o).map f
  | some _ => rfl
  | none => rfl

/-- The first candidate at an answer over candidates with one fill. -/
theorem firstCheckedE_map (a : ATm s) (E : ETy s) : ∀ l : List (Elab Γ),
    firstCheckedE (l.map fun e => (⟨a, e⟩ : ECand Γ)) E = (firstChecked l E).map fun c => (a, c)
  | [] => rfl
  | e :: es => by
    simp only [firstCheckedE, firstChecked, List.map_cons, List.findSome?_cons]
    cases toChecked e E with
    | some c => rfl
    | none =>
      have := firstCheckedE_map a E es
      simp only [firstCheckedE, firstChecked] at this
      simpa using this

/-- The first answer of a step over candidates with one fill, each mapped. -/
theorem firstSome_post {α : Type} (a : ATm s) (X : Elab Γ → Fu (Option α)) (g : α → Elab Γ) :
    ∀ l : List (Elab Γ),
      Fu.firstSome (fun (c : ECand Γ) => mapO (X c.e) fun r => (⟨c.fill, g r⟩ : ECand Γ))
          (l.map fun e => (⟨a, e⟩ : ECand Γ)) =
        Fu.bind (Fu.firstSome (fun r => mapO (X r) g) l) fun o =>
          Fu.ret (o.map fun e => (⟨a, e⟩ : ECand Γ))
  | [] => by
    funext t
    rfl
  | e :: es => by
    funext t
    simp only [List.map_cons, Fu.firstSome, Fu.orElse, mapO, Fu.bind, Fu.ret]
    cases X e t with
    | mk o t1 =>
      cases o with
      | some v => rfl
      | none =>
        simp only [Option.map_none]
        cases t1.out with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, if_false]
          have := congrFun (firstSome_post a X g es) t1
          simp only [mapO, Fu.bind, Fu.ret] at this
          exact this

/-- Every candidate of a `let`'s body over a plain bound term, closed, with the
fill of the `let`. -/
theorem lag_letPairs (ps : CaptureSet s) (annR : Option (ETy s)) (p : PElab Γ)
    {ann0 : Option (ETy s)} {a1 : ATm s} {a2 : ATm (s,x)} {o : Option (ETy (s,x))}
    {body : Fu (Out (Γ.cons p.ty))}
    (hb : Lag (SameCands a2) (letBP Γ ps a2 p o) body) :
    Lag (SameCands (.let ann0 a1 a2)) (letPairsF Γ annR p (letBP Γ ps a2 p o))
      (letPairsE Γ annR p (fun f2 => .let ann0 a1 f2) body) := by
  unfold letPairsF letPairsE
  refine lag_bind hb (fun _ => flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _ _)) _)
    fun _ r2s _ _ _ y hy => ?_
  simp only [SameCands] at hy
  rw [hy, flatMapL_map]
  have hp := flatMapL_post (f := fun r => mapL (letFinishF Γ annR p r) id)
    (f' := fun e => mapL (letFinishF Γ annR p e) fun e' =>
      (⟨.let ann0 a1 a2, e'⟩ : ECand Γ))
    (k := fun e => (⟨.let ann0 a1 a2, e⟩ : ECand Γ)) (fun _ => mapL_post) r2s
  simp only [hp, bind_bind, bind_ret]
  exact lag_mapsTo (flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _ _)) _)
    ⟨_, rfl⟩

/-- The `let` at the answer `E` at one plain candidate of the bound term, with
the fill of the `let`. -/
theorem lag_letOne (ps : CaptureSet s) (annR : Option (ETy s)) (E : ETy s) {ann0 : Option (ETy s)}
    {a1 : ATm s} {a2 : ATm (s,x)} {r1 : Elab Γ} {p : PElab Γ} (hs : r1.split = .inl p)
    {bp : BodyPE Γ} {bx : BodyXE Γ} {mkX : ATm s → ATm ((s,c),x) → ATm s}
    (hb : Lag (SameCands a2) (letBP Γ ps a2 p (letGoalE E)) (bp p (letGoalE E))) :
    Lag (fun o r => r.1 = o.map fun e => (⟨.let ann0 a1 a2, e⟩ : ECand Γ))
      (letOneF Γ annR E r1 (letBP Γ ps a2) (letBX Γ ps a2))
      (letOneE Γ annR E ⟨a1, r1⟩ bp bx (fun f1 f2 => .let ann0 f1 f2) mkX) := by
  unfold letOneF letOneE
  dsimp only
  rw [hs]
  cases E with
  | ty G0 =>
    dsimp only
    by_cases hw : tyWf? G0 = true
    · simp only [hw, if_true]
      refine lag_bind hb (fun r2s => ?_) fun _ r2s _ _ _ y hy => ?_
      · dsimp only
        split
        · exact letAtF_framed _ _ _ _ _
        · exact ret_framed _
      · simp only [SameCands] at hy
        dsimp only
        rw [hy, firstCheckedE_map]
        cases firstChecked r2s (.ty G0.weaken) with
        | some c2 =>
          exact lag_map (letAtF_framed _ _ _ _ _) fun _ => rfl
        | none => exact lag_ret rfl
    · simp only [hw, Bool.false_eq_true, if_false]
      exact lag_ret rfl
  | ex C T =>
    dsimp only
    cases annR with
    | none => exact lag_ret rfl
    | some A =>
      dsimp only
      refine lag_bind (lag_letPairs ps (some A) p hb) (fun _ => firstSome_framed (fun _ =>
        mapO_framed _ (subsumeF_framed _ _ _)) _) fun _ rs _ _ _ y hy => ?_
      simp only [SameCands] at hy
      rw [hy, firstSome_post (.let ann0 a1 a2) (fun r => subsumeF Γ r (.ex C T)) Checked.toElab,
        bind_bind]
      simp only [bind_ret]
      exact lag_map (firstSome_framed (fun _ => mapO_framed _ (subsumeF_framed _ _ _)) _)
        fun _ => rfl

/-- The candidates moved to a goal after the elaborator's last step, with any
reasons. -/
theorem lag_finishE (G : Option (ETy s)) (a : ATm s) (l : List (Elab Γ))
    (rf : Out Γ → List EReason) :
    Lag (SameCands a) (finishF Γ G l)
      (Fu.bind (finishE Γ G (l.map fun e => (⟨a, e⟩ : ECand Γ))) fun r' => Fu.ret (r'.1, rf r')) := by
  obtain ⟨rf0, h⟩ := finishE_mapsTo Γ G a l
  rw [h, bind_bind]
  simp only [bind_ret]
  exact lag_mapsTo (finishF_framed _ _ _) ⟨_, rfl⟩

/-- The clause of a `let` checked at the answer `E`, over plain candidates of
the bound term. -/
theorem lag_letSpecial (ps : CaptureSet s) (annR : Option (ETy s)) (E : ETy s)
    {ann0 : Option (ETy s)} {a1 : ATm s} {a2 : ATm (s,x)} {r1s : List (Elab Γ)}
    {bp : BodyPE Γ} {bx : BodyXE Γ} {mkX : ATm s → ATm ((s,c),x) → ATm s}
    (hb : ∀ r1 ∈ r1s, ∃ p, r1.split = .inl p ∧
      Lag (SameCands a2) (letBP Γ ps a2 p (letGoalE E)) (bp p (letGoalE E))) :
    Lag (SameCands (.let ann0 a1 a2))
      (mapL (Fu.firstSome (fun r1 => letOneF Γ annR E r1 (letBP Γ ps a2) (letBX Γ ps a2)) r1s) id)
      (Fu.bind (firstSomeR (fun c1 => letOneE Γ annR E c1 bp bx (fun f1 f2 => .let ann0 f1 f2) mkX)
        (r1s.map fun e => (⟨a1, e⟩ : ECand Γ))) fun r => Fu.ret (listR r)) := by
  rw [firstSomeR_map]
  unfold mapL
  refine lag_bind (lag_firstSome (h := fun e => (⟨.let ann0 a1 a2, e⟩ : ECand Γ)) r1s
    fun r1 hr1 => ?_) (fun _ => ret_framed _) fun _ o _ _ _ y hy => lag_ret ?_
  · obtain ⟨p, hs, hl⟩ := hb r1 hr1
    exact lag_letOne ps annR E hs hl
  · simp only [SameCands, listR, hy, listO_map, List.map_id]

/-- The clause of a `let` that synthesizes its body, over plain candidates of
the bound term. -/
theorem lag_letFallback (ps : CaptureSet s) (G : Option (ETy s)) {ann0 : Option (ETy s)}
    {a1 : ATm s} {a2 : ATm (s,x)} {r1s : List (Elab Γ)} {bp : BodyPE Γ} {bx : BodyXE Γ}
    {mkX : ATm s → ATm ((s,c),x) → ATm s}
    (hb : ∀ r1 ∈ r1s, ∃ p, r1.split = .inl p ∧
      Lag (SameCands a2) (letBP Γ ps a2 p none) (bp p none)) :
    Lag (SameCands (.let ann0 a1 a2))
      (Fu.bind (Fu.flatMapL (fun r1 => letBoundF Γ r1 (letBP Γ ps a2) (letBX Γ ps a2)) r1s)
        fun cs => finishF Γ G (dedupE cs))
      (Fu.bind (flatMapR (fun c1 => letBoundE Γ c1 bp bx (fun f1 f2 => .let ann0 f1 f2) mkX)
        (r1s.map fun e => (⟨a1, e⟩ : ECand Γ))) fun r =>
          Fu.bind (finishE Γ G (dedupEC r.1)) fun r' =>
            Fu.ret (r'.1, if r'.1.isEmpty then r.2 ++ r'.2 else [])) := by
  rw [flatMapR_map]
  refine lag_bind (lag_flatMap (h := fun e => (⟨.let ann0 a1 a2, e⟩ : ECand Γ))
    (fun _ => letBoundF_framed _ _ (letBP_framed ps a2) (letBX_framed ps a2)) r1s
    fun r1 hr1 => ?_) (fun _ => finishF_framed _ _ _) fun _ cs _ _ _ y hy => ?_
  · obtain ⟨p, hs, hl⟩ := hb r1 hr1
    unfold letBoundF letBoundE
    dsimp only
    rw [hs]
    exact lag_letPairs ps none p hl
  · rw [hy, dedupEC_map]
    exact lag_finishE G _ _ _

/-- **The `let` clause.**  When every candidate of the bound term is plain,
the typer's `let` lags behind the elaborator's, given lags of the bound term
and of the body at each goal the clause checks it against.  A `let` without a
type at a goal falls back to synthesizing its body.  There the bodies lag with
no goal, or the typer's check answers, so that neither falls back. -/
theorem lag_letE (ps : CaptureSet s) (ann : Option (ETy s)) (G : Option (ETy s)) {a1 : ATm s}
    {a2 : ATm (s,x)} {bound : Fu (Out Γ)} {bp : BodyPE Γ} {bx : BodyXE Γ}
    {mkX : ATm s → ATm ((s,c),x) → ATm s}
    (h1 : Lag (SameCands a1) (inferF Γ ps (sizeATm a1) a1 none) bound)
    (hb : ∀ t r1s t1, inferF Γ ps (sizeATm a1) a1 none t = (r1s, t1) → t1.out = false →
      ∀ r1 ∈ r1s, ∃ p, r1.split = .inl p ∧
        ∀ G' ∈ letGoals Γ ps ann G, Lag (SameCands a2) (letBP Γ ps a2 p G') (bp p G'))
    (hfb : ∀ t r1s t1, inferF Γ ps (sizeATm a1) a1 none t = (r1s, t1) → t1.out = false →
      ann = none → ∀ E, G = some E →
        (∀ r1 ∈ r1s, ∃ p, r1.split = .inl p ∧
          Lag (SameCands a2) (letBP Γ ps a2 p none) (bp p none)) ∨
        ∃ c, SettlesTo (Fu.firstSome (fun r1 => letOneF Γ none E r1 (letBP Γ ps a2)
          (letBX Γ ps a2)) r1s) (some c)) :
    Lag (SameCands (.let ann a1 a2)) (inferF Γ ps (sizeATm (.let ann a1 a2)) (.let ann a1 a2) G)
      (letE Γ ps ann G bound bp bx (fun f1 f2 => .let ann f1 f2) mkX) := by
  have hOne : ∀ (annR : Option (ETy s)) (E : ETy s) (r1s : List (Elab Γ)),
      Framed (mapL (Fu.firstSome (fun r1 => letOneF Γ annR E r1 (letBP Γ ps a2)
        (letBX Γ ps a2)) r1s) id) :=
    fun _ _ _ => mapL_framed _ (firstSome_framed (fun _ => letOneF_framed _ _ _ _
      (letBP_framed ps a2) (letBX_framed ps a2)) _)
  have hBound : ∀ (r1s : List (Elab Γ)), Framed (Fu.bind (Fu.flatMapL (fun r1 =>
      letBoundF Γ r1 (letBP Γ ps a2) (letBX Γ ps a2)) r1s) fun cs => finishF Γ G (dedupE cs)) :=
    fun _ => bind_framed (flatMapL_framed (fun _ => letBoundF_framed _ _ (letBP_framed ps a2)
      (letBX_framed ps a2)) _) fun _ => finishF_framed _ _ _
  rw [inferF_let]
  unfold letE
  refine lag_bind h1 (fun r1s => ?_) ?_
  · cases ann with
    | none =>
      refine orElseL_framed ?_ (hBound r1s)
      cases G with
      | none => exact ret_framed _
      | some E => exact hOne none E r1s
    | some A =>
      exact ite_framed (bind_framed (hOne _ _ r1s) fun _ => finishF_framed _ _ _) (ret_framed _)
  · intro t r1s t1 hrun ho y hy
    have hb' := hb t r1s t1 hrun ho
    have hfb' := hfb t r1s t1 hrun ho
    obtain ⟨l, rs⟩ := y
    simp only [SameCands] at hy
    subst hy
    dsimp only
    cases r1s with
    | nil =>
      intro t2 r t' h _
      have hr : r = [] := by
        cases ann with
        | none =>
          cases G <;>
            simp [orElseL, mapL, Fu.firstSome, Fu.flatMapL, finishF, Fu.bind, Fu.ret, listO,
              dedupE] at h <;> first | exact h.1 | exact h.1.symm
        | some A =>
          by_cases hw : (writtenAnsWhy A).isNone = true <;> cases G <;>
            simp [hw, mapL, Fu.firstSome, Fu.flatMapL, finishF, Fu.bind, Fu.ret, listO] at h <;>
            first | exact h.1 | exact h.1.symm
      subst hr
      refine ⟨([], rs), rfl, ?_⟩
      simp only [List.map_nil, List.isEmpty_nil, if_true]
      exact reaches_ret _
    | cons r0 rest =>
      rw [if_neg (by simp)]
      cases ann with
      | some A =>
        dsimp only
        cases hW : writtenAnsWhy A with
        | some rr =>
          simp only [Option.isNone_some, Bool.false_eq_true, if_false]
          exact lag_ret rfl
        | none =>
          simp only [Option.isNone_none, if_true]
          rw [firstSomeR_map]
          unfold mapL
          rw [bind_bind]
          simp only [bind_ret]
          refine lag_bind (lag_firstSome (h := fun e => (⟨.let (some A) a1 a2, e⟩ : ECand Γ))
            (r0 :: rest) fun r1 hr1 => ?_) (fun _ => finishF_framed _ _ _)
            fun _ o _ _ _ y hy => ?_
          · obtain ⟨p, hs, hl⟩ := hb' r1 hr1
            exact lag_letOne ps _ _ hs (hl _ (by simp [letGoals]))
          · rw [hy]
            simp only [listO_map, List.map_id]
            exact lag_finishE G _ _ _
      | none =>
        dsimp only
        cases G with
        | none =>
          refine lag_orElse (lag_ret rfl) (lag_letFallback ps none fun r1 hr1 => ?_) (hBound _)
          obtain ⟨p, hs, hl⟩ := hb' r1 hr1
          exact ⟨p, hs, hl none (by simp [letGoals])⟩
        | some E =>
          have hspec := lag_letSpecial ps none E (ann0 := none) (a1 := a1) (bp := bp) (bx := bx)
            (mkX := mkX) (r1s := r0 :: rest) fun r1 hr1 => by
              obtain ⟨p, hs, hl⟩ := hb' r1 hr1
              exact ⟨p, hs, hl _ (by simp [letGoals])⟩
          rcases hfb' rfl E rfl with hl | ⟨c, hc⟩
          · exact lag_orElse hspec (lag_letFallback ps (some E) hl) (hBound _)
          · refine lag_orElse_stop hspec (hOne _ _ _) (hBound _) (c := c) (l := []) ?_
            unfold mapL
            exact settles_bind (firstSome_framed (fun _ => letOneF_framed _ _ _ _
              (letBP_framed ps a2) (letBX_framed ps a2)) _) (fun _ => ret_framed _) hc ⟨0, 0, rfl⟩

end LetLag

/-! ### The canonical fill -/

/-- `r1` is a candidate of `a1` in a run of the typer with no goal that ends
unmarked. -/
def CandOf {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a1 : ATm s) (r1 : Elab Γ) : Prop :=
  ∃ t rs t', inferF Γ ps (sizeATm a1) a1 none t = (rs, t') ∧ t'.out = false ∧ r1 ∈ rs

/-- The typer checks the body `a` of `λ(x : Tw). a` against the codomain of
the function type `(∀(x : T1) T2) ^ C` and answers, so that it does not fall
back to synthesis. -/
def LamChecks {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (Tw : Dom s) (a : ATm (Sig.body s))
    (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s) : Prop :=
  ∀ hwf : Ty.Wf (readDom Tw), ∃ c l,
    SettlesTo (Fu.bind (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a
      (some (Cod.underRoot T2))) (lamCheckF Γ (readDom Tw) hwf C T1 T2)) (c :: l)

/-- Whether a `let` whose body has no empty slot fills its bound term against
a goal of its own: a call argument, or `let x : A = t in x`. -/
def letRoute {s : Sig} (tag : LetTag) (ann : Option (ETy s)) (u : PTm (s,x)) : Bool :=
  match argCallee? tag ann u, u.full? with
  | some _, some _ => true
  | none, some _ =>
      match ann with
      | some A => u.isHere && (writtenAnsWhy A).isNone
      | none => false
  | _, none => false

/-- `e` fills the definitions `d` against the self shape, written `Sw` and
read `Sr`, in lockstep, as `elabDefsF` fills them.  A type or capture member
stays.  A field whose written type, if any, is the shape's keeps its term when
that has no empty slot, and holds some term otherwise. -/
inductive DefsFill : {s : Sig} → PDefs s → Shape s → Shape s → ADefs s → Prop where
  | typ {s : Sig} {A : Label} {S0 Sw Sr : Shape s} : DefsFill (.typ A S0) Sw Sr (.typ A S0)
  | cap {s : Sig} {C : Label} {c : CaptureSet s} {Sw Sr : Shape s} :
      DefsFill (.cap C c) Sw Sr (.cap C c)
  | trmFull {s : Sig} {a c c' : Label} {o : Option (Ty s)} {t : PTm s} {Tw Tr : Ty s}
      {b : ATm s} :
      optAgree o Tw = true → t.full? = some b →
      DefsFill (.trm a o t) (.fld c Tw) (.fld c' Tr) (.trm a b)
  | trmSlot {s : Sig} {a c c' : Label} {o : Option (Ty s)} {t : PTm s} {Tw Tr : Ty s}
      {b : ATm s} :
      optAgree o Tw = true → t.full? = none →
      DefsFill (.trm a o t) (.fld c Tw) (.fld c' Tr) (.trm a b)
  | and {s : Sig} {d1 d2 : PDefs s} {S1 S2 R1 R2 : Shape s} {e1 e2 : ADefs s} :
      DefsFill d1 S1 R1 e1 → DefsFill d2 S2 R2 e2 →
      DefsFill (.and d1 d2) (.and S1 S2) (.and R1 R2) (.and e1 e2)

/-- `t`, at the read type `Tr` in the shape, filled by `b`, is a field of `d`
with an empty slot. -/
inductive SlotField : {s : Sig} → PDefs s → Shape s → Shape s → ADefs s → PTm s → Ty s →
    ATm s → Prop where
  | here {s : Sig} {a c c' : Label} {o : Option (Ty s)} {t : PTm s} {Tw Tr : Ty s} {b : ATm s} :
      t.full? = none → SlotField (.trm a o t) (.fld c Tw) (.fld c' Tr) (.trm a b) t Tr b
  | left {s : Sig} {d1 d2 : PDefs s} {S1 S2 R1 R2 : Shape s} {e1 e2 : ADefs s} {t : PTm s}
      {Tr : Ty s} {b : ATm s} :
      SlotField d1 S1 R1 e1 t Tr b →
      SlotField (.and d1 d2) (.and S1 S2) (.and R1 R2) (.and e1 e2) t Tr b
  | right {s : Sig} {d1 d2 : PDefs s} {S1 S2 R1 R2 : Shape s} {e1 e2 : ADefs s} {t : PTm s}
      {Tr : Ty s} {b : ATm s} :
      SlotField d2 S2 R2 e2 t Tr b →
      SlotField (.and d1 d2) (.and S1 S2) (.and R1 R2) (.and e1 e2) t Tr b

/-- `a` fills the partial term `p`, elaborated in `Γ` with the platform set
`ps` at the goal `G`, with the domains and self shapes the elaborator reads,
and every empty slot is at a direct site. -/
inductive Canon : {s : Sig} → Ctx s → CaptureSet s → PTm s → Option (ETy s) → ATm s → Prop where
  /-- Every slot written. -/
  | full {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {p : PTm s} {G : Option (ETy s)} {a : ATm s} :
      p.full? = some a → Canon Γ ps p G a
  /-- A lambda without a domain whose body has no empty slot: the domain of the
  goal's function part. -/
  | lamGoal {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)}
      {b : PTm (Sig.body s)} {b' : ATm (Sig.body s)} {D : Dom s} {fp : FunPart s} :
      b.full? = some b' → SettlesTo (funPartOf Γ G) fp → fp.dom? = some D →
      Canon Γ ps (.lam none b) G (.lam D b')
  /-- The body `g x` at a goal with no function part: the dominant formal of
  `g`. -/
  | callee {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {g : BVar s .var}
      {D : Dom s} :
      SettlesTo (funPartOf Γ G) .none → SettlesTo (argGoalF Γ g) (some D) →
      Canon Γ ps (.lam none (.app (.there (.there (.there g))) .here)) G
        (.lam D (.app (.there (.there (.there g))) .here))
  /-- A lambda whose body has an empty slot at a function type, with its
  written domain or the goal's: its body checked against the codomain, and
  synthesized. -/
  | lamFun {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {C : CaptureSet s} {T1 : Dom s}
      {T2 : Cod s} {Tw : Dom s} {o : Option (Dom s)} {t : PTm (Sig.body s)}
      {a : ATm (Sig.body s)} :
      t.full? = none → o.getD T1 = Tw →
      Canon (Γ.body (readDom Tw)) (psBody ps) t (some (Cod.underRoot T2)) a →
      Canon (Γ.body (readDom Tw)) (psBody ps) t none a →
      Canon Γ ps (.lam o t) (some (.ty ((Shape.all T1 T2) ^ C))) (.lam Tw a)
  /-- The same, where the typer's check of the body answers, so that neither
  synthesizes it. -/
  | lamFunChk {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {C : CaptureSet s} {T1 : Dom s}
      {T2 : Cod s} {Tw : Dom s} {o : Option (Dom s)} {t : PTm (Sig.body s)}
      {a : ATm (Sig.body s)} :
      t.full? = none → o.getD T1 = Tw →
      Canon (Γ.body (readDom Tw)) (psBody ps) t (some (Cod.underRoot T2)) a →
      LamChecks Γ ps Tw a C T1 T2 →
      Canon Γ ps (.lam o t) (some (.ty ((Shape.all T1 T2) ^ C))) (.lam Tw a)
  /-- A lambda whose body has an empty slot at a goal that is no function type
  and whose function part gives the body no goal: its written domain, or the
  domain of the function part, and its body synthesized. -/
  | lamSyn {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {Tw : Dom s}
      {o : Option (Dom s)} {t : PTm (Sig.body s)} {a : ATm (Sig.body s)} {fp : FunPart s} :
      t.full? = none → funGoal? G = none → SettlesTo (funPartOf Γ G) fp → fp.bodyGoal = none →
      (o = some Tw ∨ (o = none ∧ fp.dom? = some Tw)) →
      Canon (Γ.body (readDom Tw)) (psBody ps) t none a → Canon Γ ps (.lam o t) G (.lam Tw a)
  /-- A `let` that fills its bound term against no goal of its own: every
  candidate of the bound term plain, the body at each goal the clause checks
  it against, and synthesized when the clause falls back to that, in the
  context of every candidate of the bound term. -/
  | letGen {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {tag : LetTag}
      {ann : Option (ETy s)} {t : PTm s} {u : PTm (s,x)} {a1 : ATm s} {a2 : ATm (s,x)} :
      (PTm.let tag ann t u).full? = none → letRoute tag ann u = false → Canon Γ ps t none a1 →
      (∀ r1, CandOf Γ ps a1 r1 → ∃ p, r1.split = .inl p) →
      (∀ r1 p, CandOf Γ ps a1 r1 → r1.split = .inl p → ∀ G' ∈ letGoals Γ ps ann G,
        Canon (Γ.cons p.ty) (psVar ps) u G' a2) →
      (ann = none → G.isSome = true → ∀ r1 p, CandOf Γ ps a1 r1 → r1.split = .inl p →
        Canon (Γ.cons p.ty) (psVar ps) u none a2) →
      Canon Γ ps (.let tag ann t u) G (.let ann a1 a2)
  /-- A `let` without a type at a goal whose body the typer checks against the
  goal and answers, so that neither synthesizes the body. -/
  | letChk {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {E : ETy s} {tag : LetTag} {t : PTm s}
      {u : PTm (s,x)} {a1 : ATm s} {a2 : ATm (s,x)} {r1s : List (Elab Γ)} {c : Elab Γ} :
      (PTm.let tag none t u).full? = none → letRoute tag none u = false → Canon Γ ps t none a1 →
      (∀ r1, CandOf Γ ps a1 r1 → ∃ p, r1.split = .inl p) →
      (∀ r1 p, CandOf Γ ps a1 r1 → r1.split = .inl p →
        Canon (Γ.cons p.ty) (psVar ps) u (letGoalE E) a2) →
      SettlesTo (inferF Γ ps (sizeATm a1) a1 none) r1s →
      SettlesTo (Fu.firstSome (fun r1 => letOneF Γ none E r1 (letBP Γ ps a2) (letBX Γ ps a2))
        r1s) (some c) →
      Canon Γ ps (.let tag none t u) (some E) (.let none a1 a2)
  /-- A call argument `let z = t in g z`: `t` checked at the goal `T` of the
  dominant formal `F` of `g`.  The typer's check of the fill at `T` answers,
  and the typer accepts the filled `let`. -/
  | arg {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {g : BVar s .var}
      {t : PTm s} {F : Dom s} {T : Ty s} {a1 : ATm s} :
      t.full? = none → SettlesTo (argGoalF Γ g) (some F) → formalGoal Γ F = some T →
      Canon Γ ps t (some (.ty T)) a1 →
      (∃ c cs, SettlesTo (inferF Γ ps (sizeATm a1) a1 (some (.ty T))) (c :: cs)) →
      (∃ c cs, SettlesTo (inferF Γ ps (sizeATm (.let none a1 (.app (.there g) .here)))
        (.let none a1 (.app (.there g) .here)) G) (c :: cs)) →
      Canon Γ ps (.let .arg none t (.app (.there g) .here)) G (.let none a1 (.app (.there g) .here))
  /-- `let x : A = t in x`: `t` checked at `A` read at the context.  The
  typer's check of the fill there answers, and the typer accepts the filled
  `let`. -/
  | val {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {tag : LetTag}
      {A : ETy s} {t : PTm s} {T : Ty s} {a1 : ATm s} :
      t.full? = none → writtenAnsWhy A = none → readAns Γ ps A = .ty T →
      Canon Γ ps t (some (.ty T)) a1 →
      (∃ c cs, SettlesTo (inferF Γ ps (sizeATm a1) a1 (some (.ty T))) (c :: cs)) →
      (∃ c cs, SettlesTo (inferF Γ ps (sizeATm (.let (some A) a1 (.path (.var .here))))
        (.let (some A) a1 (.path (.var .here))) G) (c :: cs)) →
      Canon Γ ps (.let tag (some A) t (.path (.var .here))) G
        (.let (some A) a1 (.path (.var .here)))
  /-- An ascription `(t : T)`: `t` checked at `T` read at the context. -/
  | asc {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {t : PTm s} {T : Ty s}
      {a1 : ATm s} :
      t.full? = none → Canon Γ ps t (some (.ty (readAt Γ ps T))) a1 →
      Canon Γ ps (.asc t T) G (.asc a1 T)
  /-- A literal with a written self shape: each field with an empty slot
  checked at its type in the shape read at the context, in the probe context.
  The typer's check of each field's fill there answers. -/
  | obj {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {G : Option (ETy s)} {S : Shape (s,x)}
      {d : PDefs ((s,c),x)} {e : ADefs ((s,c),x)} :
      d.full? = none →
      DefsFill d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e →
      (∀ t Tr b, SlotField d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e t Tr b →
        Canon (probeCtx Γ ps S) (psObj ps) t (some (.ty Tr)) b) →
      (∀ t Tr b, SlotField d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e t Tr b →
        ∃ c cs, SettlesTo (inferF (probeCtx Γ ps S) (psObj ps) (sizeATm b) b (some (.ty Tr)))
          (c :: cs)) →
      Canon Γ ps (.obj (some S) d) G (.obj S e)
  /-- A literal without a self shape at a goal that dealiases to `μ` of a
  shape: that shape as the self shape, the fields as for a written one, and
  the typer accepts the filled literal at the goal. -/
  | objGoal {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {E : ETy s} {S : Shape (s,x)}
      {d : PDefs ((s,c),x)} {e : ADefs ((s,c),x)} :
      SettlesTo (selfGoalF Γ E) (some S) →
      DefsFill d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e →
      (∀ t Tr b, SlotField d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e t Tr b →
        Canon (probeCtx Γ ps S) (psObj ps) t (some (.ty Tr)) b) →
      (∀ t Tr b, SlotField d (Shape.underRoot S) (Shape.underRoot (readSelf Γ ps S)) e t Tr b →
        ∃ c cs, SettlesTo (inferF (probeCtx Γ ps S) (psObj ps) (sizeATm b) b (some (.ty Tr)))
          (c :: cs)) →
      (∃ c cs, SettlesTo (inferF Γ ps (sizeATm (.obj S e)) (.obj S e) (some E)) (c :: cs)) →
      Canon Γ ps (.obj none d) (some E) (.obj S e)

/-! ### Unfoldings -/

section Unfold

variable {s : Sig} {Γ : Ctx s} {ps : CaptureSet s}

/-- A lambda with a written domain and an empty slot in its body, unfolded. -/
theorem elabF_lam_some (k : Nat) {T : Dom s} {t : PTm (Sig.body s)} (ht : t.full? = none)
    (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.lam (some T) t) G =
      lamSomeF Γ T G (fun o => elabF (Γ.body (readDom T)) (psBody ps) k t o) := by
  rw [elabF]
  simp only [PTm.full?, ht, Option.map_none]

/-- A lambda whose body has an empty slot at a function type, unfolded to the
clause of a lambda with a domain. -/
theorem elabF_lam_fun (k : Nat) {o : Option (Dom s)} {t : PTm (Sig.body s)}
    (ht : t.full? = none) (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s) :
    elabF Γ ps (k + 1) (.lam o t) (some (.ty ((Shape.all T1 T2) ^ C))) =
      lamAtF Γ (o.getD T1) (some (.ty ((Shape.all T1 T2) ^ C))) (.direct C T1 T2)
        (fun o' => elabF (Γ.body (readDom (o.getD T1))) (psBody ps) k t o') := by
  cases o with
  | some T =>
    rw [elabF_lam_some k ht]
    simp only [lamSomeF, funPartOf, bind_ret]
    rfl
  | none =>
    rw [elabF_lam_none]
    simp only [lamNoneF, funPartOf, bind_ret, FunPart.dom?, ht]
    rfl

/-- A `let` with an empty slot, unfolded. -/
theorem elabF_let (k : Nat) {tag : LetTag} {ann : Option (ETy s)} {t : PTm s} {u : PTm (s,x)}
    (hp : (PTm.let tag ann t u).full? = none) (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.let tag ann t u) G =
      letF Γ ps tag ann u G (fun E => elabF Γ ps k t (some E))
        (fun _ => letE Γ ps ann G (elabF Γ ps k t none)
          (fun pe o => elabF (Γ.cons pe.ty) (psVar ps) k u o)
          (fun q o => elabF ((Γ.consC).cons q.body) (psObj ps) k
            (u.rename (Rename.succ (k := .cap)).lift) o)
          (fun f1 f2 => .let ann f1 f2) (letXFill ann u)) := by
  rw [elabF, hp]

/-- A `let` that fills its bound term against no goal of its own goes to the
clause of any `let`. -/
theorem letF_gen {tag : LetTag} {ann : Option (ETy s)} {u : PTm (s,x)} {G : Option (ETy s)}
    {arg : ETy s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)} (h : letRoute tag ann u = false) :
    letF Γ ps tag ann u G arg gen = gen () := by
  unfold letRoute at h
  unfold letF
  split at h
  · cases h
  · rename_i hA hU
    simp only [hA, hU]
    cases ann with
    | none => rfl
    | some A =>
      simp only at h
      simp only [h, Bool.false_eq_true, if_false]
  · rename_i hU
    simp only [hU]

/-- A literal with a written self shape and an empty slot, unfolded. -/
theorem elabF_obj_some (k : Nat) {S : Shape (s,x)} {d : PDefs ((s,c),x)} (hd : d.full? = none)
    (G : Option (ETy s)) :
    elabF Γ ps (k + 1) (.obj (some S) d) G =
      objSelfF Γ ps S G (elabDefsF (probeCtx Γ ps S) (psObj ps) k d (Shape.underRoot S)
        (Shape.underRoot (readSelf Γ ps S))) := by
  rw [elabF]
  simp only [PTm.full?, hd, Option.map_none]

/-- The typer on a literal whose self shape is outside the notation answers
nothing. -/
theorem inferF_obj_written {S : Shape (s,x)} {e : ADefs ((s,c),x)} {G : Option (ETy s)}
    {r : Reason} (h : writtenWhy ((Shape.mu S) ^ []) = some r) :
    inferF Γ ps (sizeATm (.obj S e)) (.obj S e) G = Fu.ret [] := by
  show inferF Γ ps (sizeADefs e + 1) (.obj S e) G = _
  rw [inferF]
  simp [h]

/-- The typer's clause of an ascription. -/
theorem inferF_asc (a1 : ATm s) (T : Ty s) (G : Option (ETy s)) :
    inferF Γ ps (sizeATm (.asc a1 T)) (.asc a1 T) G =
      if (writtenWhy T).isNone then
        Fu.bind (inferF Γ ps (sizeATm a1) a1 (some (.ty (readAt Γ ps T)))) fun rs =>
          finishF Γ G (listO ((firstChecked rs (.ty (readAt Γ ps T))).map fun r =>
            (⟨.asc r.tm (readAt Γ ps T), r.uses, .ty (readAt Γ ps T), r.deriv⟩ : Elab Γ)))
      else Fu.ret [] := by
  show inferF Γ ps (sizeATm a1 + 1) (.asc a1 T) G = _
  rw [inferF]

/-- The definitions of a literal filled in lockstep reach their fill when
the elaboration of every field with an empty slot reaches a first candidate
with the field's fill. -/
theorem elabDefsF_reaches {d : PDefs s} {Sw Sr : Shape s} {e : ADefs s}
    (hd : DefsFill d Sw Sr e) :
    (∀ t Tr b, SlotField d Sw Sr e t Tr b → ∀ k, sizePTm t ≤ k →
      ∃ y : Out Γ, (∃ c cs, y.1 = c :: cs ∧ c.fill = b) ∧
        Reaches (elabF Γ ps k t (some (.ty Tr))) y) →
    ∀ k, sizePDefs d ≤ k → ∃ rs, Reaches (elabDefsF Γ ps k d Sw Sr) (some e, rs) := by
  induction hd with
  | typ =>
    intro _ k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePDefs] at hk; omega⟩
    rw [elabDefsF]
    exact ⟨[], reaches_ret _⟩
  | cap =>
    intro _ k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePDefs] at hk; omega⟩
    rw [elabDefsF]
    exact ⟨[], reaches_ret _⟩
  | @trmFull a c c' o t Tw Tr b ho ht =>
    intro _ k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePDefs] at hk; omega⟩
    rw [elabDefsF]
    simp only [ho, ht, if_true]
    exact ⟨[], reaches_ret _⟩
  | @trmSlot a c c' o t Tw Tr b ho ht =>
    intro hf k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePDefs] at hk; omega⟩
    simp only [sizePDefs] at hk
    rw [elabDefsF]
    simp only [ho, ht, if_true]
    obtain ⟨y, ⟨c0, cs, hy, hc0⟩, hry⟩ := hf t Tr b (.here ht) k (by omega)
    refine ⟨y.2, reaches_bind hry ?_⟩
    rw [hy]
    simp only [List.head?_cons, Option.map_some, hc0]
    exact reaches_ret _
  | @and d1 d2 S1 S2 R1 R2 e1 e2 _ _ ih1 ih2 =>
    intro hf k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePDefs] at hk; omega⟩
    simp only [sizePDefs] at hk
    obtain ⟨rs1, h1⟩ := ih1 (fun t Tr b h => hf t Tr b (.left h)) k (by omega)
    obtain ⟨rs2, h2⟩ := ih2 (fun t Tr b h => hf t Tr b (.right h)) k (by omega)
    rw [elabDefsF]
    refine ⟨rs2, reaches_bind h1 ?_⟩
    exact reaches_bind h2 (reaches_ret _)

end Unfold

/-! ### The elaborator at the direct sites -/

/-- **The elaborator at the direct sites is the typer on the fill.**  When the
typer's run on the canonical fill ends unmarked, the elaborator, from any
index that covers the partial term, gives the same candidates in the same
order, each with the fill, with enough fuel. -/
theorem canon_lag {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {p : PTm s} {G : Option (ETy s)}
    {a : ATm s} (h : Canon Γ ps p G a) :
    ∀ k, sizePTm p ≤ k → Lag (SameCands a) (inferF Γ ps (sizeATm a) a G) (elabF Γ ps k p G) := by
  induction h with
  | @full s Γ ps p G a hp =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := sizePTm_pos p; omega⟩
    rw [elabF_full _ _ hp]
    exact lag_full _ _ _ _
  | @lamGoal s Γ ps G b b' D fp hb hs hd =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    rw [elabF_lam_none]
    unfold lamNoneF
    refine lag_prefix (reaches_settles (funPartOf_framed _ _) hs) ?_
    simp only [hd, hb]
    exact lag_full _ _ _ _
  | @callee s Γ ps G g D hf hg =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    rw [elabF_lam_none]
    unfold lamNoneF
    refine lag_prefix (reaches_settles (funPartOf_framed _ _) hf) ?_
    dsimp only [FunPart.dom?]
    unfold lamCalleeF
    rw [calleeOf?_app]
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hg) ?_
    simp only [PTm.full?]
    exact lag_full _ _ _ _
  | @lamFun s Γ ps C T1 T2 Tw o t a ht hT _ _ ih2 ih1 =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_lam_fun _ ht, hT]
    exact lag_lamDirect ps (ih2 k (by omega)) fun _ => .inl (ih1 k (by omega))
  | @lamFunChk s Γ ps C T1 T2 Tw o t a ht hT _ hchk ih2 =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_lam_fun _ ht, hT]
    exact lag_lamDirect ps (ih2 k (by omega)) fun hwf => .inr (hchk hwf)
  | @lamSyn s Γ ps G Tw o t a fp ht hG hs hfp ho _ ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rcases ho with rfl | ⟨rfl, hd⟩
    · rw [elabF_lam_some _ ht]
      unfold lamSomeF
      refine lag_prefix (reaches_settles (funPartOf_framed _ _) hs) ?_
      exact lag_lamSyn ps hG hfp (ih k (by omega))
    · rw [elabF_lam_none]
      unfold lamNoneF
      refine lag_prefix (reaches_settles (funPartOf_framed _ _) hs) ?_
      simp only [hd, ht]
      exact lag_lamSyn ps hG hfp (ih k (by omega))
  | @letGen s Γ ps G tag ann t u a1 a2 hp hr _ hpl _ _ ih1 ih2 ih3 =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_let _ hp, letF_gen hr]
    refine lag_letE ps ann G (ih1 k (by omega)) ?_ ?_
    · intro t0 r1s t1 hrun ho r1 hr1
      obtain ⟨p, hs⟩ := hpl r1 ⟨t0, r1s, t1, hrun, ho, hr1⟩
      exact ⟨p, hs, fun G' hG' =>
        ih2 r1 p ⟨t0, r1s, t1, hrun, ho, hr1⟩ hs G' hG' k (by omega)⟩
    · intro t0 r1s t1 hrun ho hann E hG
      refine .inl fun r1 hr1 => ?_
      obtain ⟨p, hs⟩ := hpl r1 ⟨t0, r1s, t1, hrun, ho, hr1⟩
      exact ⟨p, hs, ih3 hann (by simp [hG]) r1 p ⟨t0, r1s, t1, hrun, ho, hr1⟩ hs k (by omega)⟩
  | @letChk s Γ ps E tag t u a1 a2 r1s c hp hr _ hpl _ hcs hsp ih1 ih2 =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_let _ hp, letF_gen hr]
    refine lag_letE ps none (some E) (ih1 k (by omega)) ?_ ?_
    · intro t0 r1s' t1 hrun ho r1 hr1
      obtain ⟨p, hs⟩ := hpl r1 ⟨t0, r1s', t1, hrun, ho, hr1⟩
      refine ⟨p, hs, fun G' hG' => ?_⟩
      simp only [letGoals, List.mem_singleton] at hG'
      subst hG'
      exact ih2 r1 p ⟨t0, r1s', t1, hrun, ho, hr1⟩ hs k (by omega)
    · intro t0 r1s' t1 hrun ho _ E' hG
      cases hG
      have hr1 := settles_unique (inferF_framed _ _ _ _ _) hcs hrun ho
      subst hr1
      exact .inr ⟨c, hsp⟩
  | @arg s Γ ps G g t F T a1 ht hF hFT _ hchk hacc ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_arg _ _ _ ht]
    unfold argLetF
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hF) ?_
    simp only [Option.bind_some, hFT]
    obtain ⟨c, cs, hcs⟩ := hchk
    obtain ⟨y, hy, hry⟩ := settles_lag (ih k (by omega)) hcs
    unfold fillThenF orElseW
    rw [bind_bind]
    refine lag_prefix hry ?_
    simp only [SameCands] at hy
    simp only [hy, List.map_cons]
    obtain ⟨c', cs', hacc'⟩ := hacc
    refine lag_stop (ok := fun cs => !cs.isEmpty) (inferF_framed _ _ _ _ _) (lag_full _ _ _ _)
      hacc' ?_
    intro y hy
    simp only [SameCands] at hy
    simp [hy]
  | @val s Γ ps G tag A t T a1 ht hw hR _ hchk hacc ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_val _ _ _ _ hw ht]
    unfold valLetF
    simp only [hR]
    obtain ⟨c, cs, hcs⟩ := hchk
    obtain ⟨y, hy, hry⟩ := settles_lag (ih k (by omega)) hcs
    unfold fillThenF orElseW
    rw [bind_bind]
    refine lag_prefix hry ?_
    simp only [SameCands] at hy
    simp only [hy, List.map_cons]
    obtain ⟨c', cs', hacc'⟩ := hacc
    refine lag_stop (ok := fun cs => !cs.isEmpty) (inferF_framed _ _ _ _ _) (lag_full _ _ _ _)
      hacc' ?_
    intro y hy
    simp only [SameCands] at hy
    simp [hy]
  | @asc s Γ ps G t T a1 ht _ ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [inferF_asc]
    cases hW : writtenWhy T with
    | some r =>
      rw [elabF]
      simp only [PTm.full?, ht, Option.map_none, hW, Option.isNone_some, Bool.false_eq_true,
        if_false]
      exact lag_ret rfl
    | none =>
      rw [elabF_asc _ _ _ ht hW]
      simp only [Option.isNone_none, if_true]
      unfold ascE
      refine lag_bind (ih k (by omega)) (fun _ => finishF_framed _ _ _) fun _ rs _ _ _ y hy => ?_
      simp only [SameCands] at hy
      dsimp only
      rw [hy, firstCheckedE_map]
      cases firstChecked rs (.ty (readAt Γ ps T)) with
      | some c =>
        dsimp only [Option.map_some, listO]
        exact lag_mapsTo (finishF_framed _ _ _) (finishE_mapsTo Γ G (.asc a1 T) [_])
      | none => cases G <;> exact lag_ret rfl
  | @obj s Γ ps G S d e hd hfill _ hsettle ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF_obj_some _ hd]
    unfold objSelfF
    cases hW : writtenWhy ((Shape.mu S) ^ []) with
    | some r =>
      rw [inferF_obj_written hW]
      exact lag_ret rfl
    | none =>
      dsimp only
      obtain ⟨rs, hr⟩ := elabDefsF_reaches hfill (fun t Tr b hsf k hk => by
        obtain ⟨c, cs, hs⟩ := hsettle t Tr b hsf
        obtain ⟨y, hy, hry⟩ := settles_lag (ih t Tr b hsf k hk) hs
        exact ⟨y, ⟨⟨b, c⟩, cs.map fun e => ⟨b, e⟩, hy, rfl⟩, hry⟩) k (by omega)
      refine lag_prefix hr ?_
      exact lag_full _ _ _ _
  | @objGoal s Γ ps E S d e hS hfill _ hsettle hacc ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [sizePTm] at hk; omega⟩
    simp only [sizePTm] at hk
    rw [elabF]
    simp only [PTm.full?]
    refine lag_prefix (reaches_settles (selfGoalF_framed _ _) hS) ?_
    dsimp only
    unfold orElseW objSelfF
    cases hW : writtenWhy ((Shape.mu S) ^ []) with
    | some r =>
      exfalso
      obtain ⟨c, cs, hc⟩ := hacc
      rw [inferF_obj_written hW] at hc
      cases settles_ret_inv hc
    | none =>
      dsimp only
      rw [bind_bind]
      obtain ⟨rs, hr⟩ := elabDefsF_reaches hfill (fun t Tr b hsf k hk => by
        obtain ⟨c, cs, hs⟩ := hsettle t Tr b hsf
        obtain ⟨y, hy, hry⟩ := settles_lag (ih t Tr b hsf k hk) hs
        exact ⟨y, ⟨⟨b, c⟩, cs.map fun e => ⟨b, e⟩, hy, rfl⟩, hry⟩) k (by omega)
      refine lag_prefix hr ?_
      dsimp only
      obtain ⟨c, cs, hacc'⟩ := hacc
      refine lag_stop (ok := fun cs => !cs.isEmpty) (inferF_framed _ _ _ _ _) (lag_full _ _ _ _)
        hacc' ?_
      intro y hy
      simp only [SameCands] at hy
      simp [hy]

/-! ### At the top -/

/-- **Completeness at the direct sites, with the candidate, in a context.**
A partial term whose canonical fill the typer types in `Γ` elaborates there,
from some fuel on, to the typer's first candidate on that fill, with the
fill. -/
theorem elab_complete_first_fill {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {p : PTm s}
    {a : ATm s} {n : Nat} {c0 : Elab Γ} (hc : Canon Γ ps p none a)
    (hl : (synthInF Γ ps a n).1 = some c0) :
    ∃ n0, ∀ m, n0 ≤ m → (elabFirstF Γ ps p m).1 = .ok ⟨a, c0⟩ := by
  unfold synthInF synthF at hl
  cases hs : inferF Γ ps (sizeATm a) a none ⟨n, false⟩ with
  | mk cs t' =>
    rw [hs] at hl
    cases cs with
    | nil => simp [firstCand] at hl
    | cons c cs =>
      cases ho : t'.out with
      | true => simp [firstCand, ho] at hl
      | false =>
        simp only [firstCand, ho, Bool.false_eq_true, if_false, Option.some.injEq] at hl
        subst hl
        obtain ⟨r', hR, n1, m1, hk⟩ :=
          canon_lag hc (sizePTm p) (Nat.le_refl _) ⟨n, false⟩ (c :: cs) t' hs ho
        refine ⟨n1, fun m hm => ?_⟩
        have hrun := hk (m - n1)
        have htk : (⟨n1 + (m - n1), false⟩ : Tank) = ⟨m, false⟩ := by
          rw [Tank.mk.injEq]
          exact ⟨by omega, rfl⟩
        rw [htk] at hrun
        obtain ⟨es, rs⟩ := r'
        simp only [SameCands] at hR
        subst hR
        unfold elabFirstF elabInF
        rw [hrun]
        rfl

/-- **Completeness at the direct sites, with the candidate.**  A closed
program over a platform of plain binders whose canonical fill the typer types
elaborates, from some fuel on, to the typer's first candidate on that fill,
with the fill. -/
theorem elab_complete_direct_fill {π : PlatformNames} {p : PTm π.sig} {a : ATm π.sig} {n : Nat}
    {c0 : Elab π.plat.ctx} (hc : Canon π.plat.ctx π.set p none a)
    (hl : (synthTopF n π a).1 = some c0) :
    ∃ n0, ∀ m, n0 ≤ m → (elabTopF m π p).1 = .ok ⟨a, c0⟩ :=
  elab_complete_first_fill hc hl

/-- **Completeness at the direct sites.**  A closed program whose canonical
fill the typer types is accepted by the elaborator from some fuel on. -/
theorem elab_complete_direct {π : PlatformNames} {p : PTm π.sig} {a : ATm π.sig} {n : Nat}
    (hc : Canon π.plat.ctx π.set p none a) (hl : (synthTopF n π a).1.isSome = true) :
    ∃ n0, ∀ m, n0 ≤ m → (elabTopF m π p).1.isOk = true := by
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨n0, h⟩ := elab_complete_direct_fill hc hc0
  refine ⟨n0, fun m hm => ?_⟩
  rw [h m hm]
  rfl

/-- **Completeness at the direct sites, for a whole program, with the
candidate.**  A body whose canonical fill the typer types at the context of
the program's platform, over the platform set, elaborates there, from some
fuel on, to the typer's first candidate on that fill, with the fill. -/
theorem elab_complete_prog_fill {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a : ATm p.platNames.sig} {n : Nat} {c0 : Elab h.plat.ctx}
    (hc : Canon h.plat.ctx p.platNames.set q none a)
    (hl : (synthInF h.plat.ctx p.platNames.set a n).1 = some c0) :
    ∃ n0, ∀ m, n0 ≤ m → (elabProgF m p h q).1 = .ok ⟨a, c0⟩ :=
  elab_complete_first_fill hc hl

/-- **Completeness at the direct sites, for a whole program.**  A body whose
canonical fill the typer types is accepted by the elaborator from some fuel
on. -/
theorem elab_complete_prog {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a : ATm p.platNames.sig} {n : Nat}
    (hc : Canon h.plat.ctx p.platNames.set q none a)
    (hl : (synthInF h.plat.ctx p.platNames.set a n).1.isSome = true) :
    ∃ n0, ∀ m, n0 ≤ m → (elabProgF m p h q).1.isOk = true := by
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨n0, he⟩ := elab_complete_prog_fill hc hc0
  refine ⟨n0, fun m hm => ?_⟩
  rw [he m hm]
  rfl

/-- **Completeness at the direct sites, through the pipeline.**  A program
whose header resolves and whose body resolves to a partial term whose
canonical fill the typer types, and whose fill agrees with every slot the
body writes, compiles as the typer compiles the program with the fill as its
body, declared use set and record included, at every budget from some fuel
on. -/
theorem compile_complete_direct {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a : ATm p.platNames.sig} {n : Nat} {c0 : Elab h.plat.ctx}
    (hp : resolvePProg Λ p = some (h, q)) (hc : Canon h.plat.ctx p.platNames.set q none a)
    (hl : (synthInF h.plat.ctx p.platNames.set a n).1 = some c0) (hfa : q.fills a = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λ p = compileLanded b p (h.withBody a) := by
  obtain ⟨n0, he0⟩ := elab_complete_prog_fill hc hl
  refine ⟨max n0 n, fun b hb => ?_⟩
  have he := he0 b.fuel (Nat.le_trans (Nat.le_max_left _ _) hb)
  have hs := synthInF_mono hl (Nat.le_trans (Nat.le_max_right _ _) hb)
  have hsyn : synthIn? b h.plat.ctx p.platNames.set a = .ok c0 := by
    unfold synthIn?
    cases hq : synthInF h.plat.ctx p.platNames.set a b.fuel with
    | mk o t =>
      rw [hq] at hs
      simp only at hs
      subst hs
      rfl
  unfold compile compileE compileLanded typeAt synthPlat?
  rw [hp]
  dsimp only
  rw [he]
  dsimp only [ProgHeader.withBody]
  rw [hsyn]
  cases hq : c0.split with
  | inl e =>
    simp only [hfa, if_true, Verdict.bind]
    by_cases hk : ATm.skel e.tm = ATm.skel a
    · simp only [hk, dif_pos, verdictOf_exceptOf, hq]
    · simp only [hk, hq, dif_neg, not_false_eq_true]
      rfl
  | inr x =>
    simp only [hq, Verdict.bind]
    rfl

/-! ### Deciding the canonical fill -/

/-- The answer of a computation from a full tank of `n` units, when the tank
ends unmarked. -/
def settledAt {α : Type} (c : Fu α) (n : Nat) : Option α :=
  match c ⟨n, false⟩ with
  | (x, t) => if t.out then none else some x

/-- An answer read by `settledAt` is where the computation settles. -/
theorem settlesTo_of_settledAt {α : Type} {c : Fu α} {x : α} {n : Nat}
    (h : settledAt c n = some x) : SettlesTo c x := by
  unfold settledAt at h
  cases hc : c ⟨n, false⟩ with
  | mk y t =>
    rw [hc] at h
    cases ho : t.out with
    | true => simp [ho] at h
    | false =>
      simp only [ho, Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact ⟨n, t.left, by rw [hc]; exact Prod.ext rfl (tank_eq rfl ho)⟩

/-- Whether a computation settles at a nonempty list from a full tank of `n`
units. -/
def settlesNonempty {α : Type} (c : Fu (List α)) (n : Nat) : Bool :=
  match settledAt c n with
  | some (_ :: _) => true
  | _ => false

theorem settlesNonempty_sound {α : Type} {c : Fu (List α)} {n : Nat}
    (h : settlesNonempty c n = true) : ∃ x l, SettlesTo c (x :: l) := by
  unfold settlesNonempty at h
  split at h
  · rename_i x l hs
    exact ⟨x, l, settlesTo_of_settledAt hs⟩
  · cases h

/-- Whether a computation settles at an answer from a full tank of `n`
units. -/
def settlesSome {α : Type} (c : Fu (Option α)) (n : Nat) : Bool :=
  match settledAt c n with
  | some (some _) => true
  | _ => false

theorem settlesSome_sound {α : Type} {c : Fu (Option α)} {n : Nat}
    (h : settlesSome c n = true) : ∃ x, SettlesTo c (some x) := by
  unfold settlesSome at h
  split at h
  · rename_i x hs
    exact ⟨x, settlesTo_of_settledAt hs⟩
  · cases h

/-- Whether the typer's check of the body `a` of `λ(x : Tw). a` against the
codomain `T2` answers, from a full tank of `n` units. -/
def lamChecksB {s : Sig} (n : Nat) (Γ : Ctx s) (ps : CaptureSet s) (Tw : Dom s)
    (a : ATm (Sig.body s)) (C : CaptureSet s) (T1 : Dom s) (T2 : Cod s) : Bool :=
  if hwf : Ty.Wf (readDom Tw) then
    settlesNonempty (Fu.bind (inferF (Γ.body (readDom Tw)) (psBody ps) (sizeATm a) a
      (some (Cod.underRoot T2))) (lamCheckF Γ (readDom Tw) hwf C T1 T2)) n
  else true

theorem lamChecksB_sound {s : Sig} {n : Nat} {Γ : Ctx s} {ps : CaptureSet s} {Tw : Dom s}
    {a : ATm (Sig.body s)} {C : CaptureSet s} {T1 : Dom s} {T2 : Cod s}
    (h : lamChecksB n Γ ps Tw a C T1 T2 = true) : LamChecks Γ ps Tw a C T1 T2 := by
  intro hwf
  unfold lamChecksB at h
  rw [dif_pos hwf] at h
  exact settlesNonempty_sound h

/-- Whether every candidate of a run is plain and passes `f` at its plain
form. -/
def allPlain {s : Sig} {Γ : Ctx s} (r1s : List (Elab Γ)) (f : PElab Γ → Bool) : Bool :=
  r1s.all fun r1 =>
    match r1.split with
    | .inl p => f p
    | .inr _ => false

theorem allPlain_sound {s : Sig} {Γ : Ctx s} {r1s : List (Elab Γ)} {f : PElab Γ → Bool}
    (h : allPlain r1s f = true) : ∀ r1 ∈ r1s, ∃ p, r1.split = .inl p ∧ f p = true := by
  intro r1 hr1
  unfold allPlain at h
  rw [List.all_eq_true] at h
  have := h r1 hr1
  cases hs : r1.split with
  | inl p =>
    rw [hs] at this
    exact ⟨p, rfl, this⟩
  | inr q =>
    rw [hs] at this
    cases this

mutual
/-- Whether `a` is the canonical fill of `p` elaborated in `Γ` with the
platform set `ps` at the goal `G`, with the readings of the goal and the runs
of the typer taken from a full tank of `n` units. -/
def canonB {s : Sig} (n : Nat) (Γ : Ctx s) (ps : CaptureSet s) (p : PTm s) (G : Option (ETy s))
    (a : ATm s) : Bool :=
  if p.full? = some a then true
  else
    match p, a with
    | .lam o t, .lam Tw a' =>
        match o, t.full? with
        | none, some b =>
            decide (b = a') &&
              match settledAt (funPartOf Γ G) n with
              | some fp =>
                  match fp.dom? with
                  | some D => decide (D = Tw)
                  | none =>
                      match fp, calleeOf? t with
                      | .none, some g =>
                          decide (t = .app (.there (.there (.there g))) .here) &&
                            decide (settledAt (argGoalF Γ g) n = some (some Tw))
                      | _, _ => false
              | none => false
        | _, none =>
            match G with
            | some (.ty (.capt C (.all T1 T2))) =>
                decide (o.getD T1 = Tw) &&
                  canonB n (Γ.body (readDom Tw)) (psBody ps) t (some (Cod.underRoot T2)) a' &&
                  (canonB n (Γ.body (readDom Tw)) (psBody ps) t none a' ||
                    lamChecksB n Γ ps Tw a' C T1 T2)
            | _ =>
                (funGoal? G).isNone &&
                  canonB n (Γ.body (readDom Tw)) (psBody ps) t none a' &&
                  match settledAt (funPartOf Γ G) n with
                  | some fp =>
                      fp.bodyGoal.isNone &&
                        (decide (o = some Tw) || (o.isNone && decide (fp.dom? = some Tw)))
                  | none => false
        | some _, some _ => false
    | .let tag ann t u, .let ann' a1 a2 =>
        decide (ann = ann') && decide ((PTm.let tag ann t u).full? = none) &&
          if letRoute tag ann u then
            match argCallee? tag ann u with
            | some g =>
                decide (tag = .arg) && decide (ann = none) &&
                  decide (u = .app (.there g) .here) && decide (a2 = .app (.there g) .here) &&
                  decide (t.full? = none) &&
                  match settledAt (argGoalF Γ g) n with
                  | some (some F) =>
                      match formalGoal Γ F with
                      | some T =>
                          canonB n Γ ps t (some (.ty T)) a1 &&
                            settlesNonempty (inferF Γ ps (sizeATm a1) a1 (some (.ty T))) n &&
                            settlesNonempty (inferF Γ ps (sizeATm (.let none a1 a2))
                              (.let none a1 a2) G) n
                      | none => false
                  | _ => false
            | none =>
                match ann with
                | some A =>
                    decide (u = .path (.var .here)) && decide (a2 = .path (.var .here)) &&
                      decide (t.full? = none) && (writtenAnsWhy A).isNone &&
                      match readAns Γ ps A with
                      | .ty T =>
                          canonB n Γ ps t (some (.ty T)) a1 &&
                            settlesNonempty (inferF Γ ps (sizeATm a1) a1 (some (.ty T))) n &&
                            settlesNonempty (inferF Γ ps (sizeATm (.let (some A) a1 a2))
                              (.let (some A) a1 a2) G) n
                      | .ex _ _ => false
                | none => false
          else
            canonB n Γ ps t none a1 &&
              match settledAt (inferF Γ ps (sizeATm a1) a1 none) n with
              | some r1s =>
                  allPlain r1s (fun p =>
                    (letGoals Γ ps ann G).all fun G' => canonB n (Γ.cons p.ty) (psVar ps) u G' a2) &&
                  match ann, G with
                  | none, some E =>
                      allPlain r1s (fun p => canonB n (Γ.cons p.ty) (psVar ps) u none a2) ||
                        settlesSome (Fu.firstSome (fun r1 => letOneF Γ none E r1 (letBP Γ ps a2)
                          (letBX Γ ps a2)) r1s) n
                  | _, _ => true
              | none => false
    | .asc t T, .asc a1 T' =>
        decide (T = T') && decide (t.full? = none) &&
          canonB n Γ ps t (some (.ty (readAt Γ ps T))) a1
    | .obj (some S) d, .obj S' e =>
        decide (S = S') && decide (d.full? = none) &&
          canonDefsB n (probeCtx Γ ps S) (psObj ps) d (Shape.underRoot S)
            (Shape.underRoot (readSelf Γ ps S)) e
    | .obj none d, .obj S e =>
        match G with
        | some E =>
            decide (settledAt (selfGoalF Γ E) n = some (some S)) &&
              canonDefsB n (probeCtx Γ ps S) (psObj ps) d (Shape.underRoot S)
                (Shape.underRoot (readSelf Γ ps S)) e &&
              settlesNonempty (inferF Γ ps (sizeATm (.obj S e)) (.obj S e) (some E)) n
        | none => false
    | _, _ => false
termination_by structural p

/-- Whether `e` fills the definitions `d` against the self shape, written `Sw`
and read `Sr`, in lockstep, each field with an empty slot at a direct site
whose fill the typer's check answers, read from a full tank of `n` units. -/
def canonDefsB {s : Sig} (n : Nat) (Γ : Ctx s) (ps : CaptureSet s) (d : PDefs s)
    (Sw Sr : Shape s) (e : ADefs s) : Bool :=
  match d, Sw, Sr, e with
  | .typ A S0, _, _, .typ A' S0' => decide (A = A') && decide (S0 = S0')
  | .cap C c, _, _, .cap C' c' => decide (C = C') && decide (c = c')
  | .trm a o t, .fld _ Tw, .fld _ Tr, .trm a' b =>
      decide (a = a') && optAgree o Tw &&
        match t.full? with
        | some b' => decide (b' = b)
        | none =>
            canonB n Γ ps t (some (.ty Tr)) b &&
              settlesNonempty (inferF Γ ps (sizeATm b) b (some (.ty Tr))) n
  | .and d1 d2, .and S1 S2, .and R1 R2, .and e1 e2 =>
      canonDefsB n Γ ps d1 S1 R1 e1 && canonDefsB n Γ ps d2 S2 R2 e2
  | _, _, _, _ => false
termination_by structural d
end

/-- A candidate of a run that ends unmarked is one of the candidates any run
that ends unmarked gives. -/
theorem candOf_mem {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a1 : ATm s} {r1s : List (Elab Γ)}
    (hs : SettlesTo (inferF Γ ps (sizeATm a1) a1 none) r1s) {r1 : Elab Γ}
    (h : CandOf Γ ps a1 r1) : r1 ∈ r1s := by
  obtain ⟨t, rs, t', hrun, ho, hmem⟩ := h
  rw [settles_unique (inferF_framed _ _ _ _ _) hs hrun ho] at hmem
  exact hmem

/-- A goal that is no function type has no function goal. -/
theorem funGoal?_none_of {s : Sig} {G : Option (ETy s)} (h : (funGoal? G).isNone = true) :
    funGoal? G = none := Option.isNone_iff_eq_none.mp h

mutual
/-- `canonB` decides `Canon` soundly. -/
theorem canonB_sound {n : Nat} : {s : Sig} → {Γ : Ctx s} → {ps : CaptureSet s} → (p : PTm s) →
    (G : Option (ETy s)) → (a : ATm s) → canonB n Γ ps p G a = true → Canon Γ ps p G a
  | _, Γ, ps, .lam o t, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | lam Tw a' =>
        simp only at h
        cases htf : t.full? with
        | some b =>
          cases o with
          | some T => simp [htf] at h
          | none =>
            simp only [htf, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨rfl, h⟩ := h
            cases hset : settledAt (funPartOf Γ G) n with
            | none => simp [hset] at h
            | some fp =>
              simp only [hset] at h
              cases hd : fp.dom? with
              | some D =>
                simp only [hd, decide_eq_true_eq] at h
                subst h
                exact .lamGoal htf (settlesTo_of_settledAt hset) hd
              | none =>
                simp only [hd] at h
                cases fp with
                | none =>
                  cases hcal : calleeOf? t with
                  | none => simp [hcal] at h
                  | some g =>
                    simp only [hcal, Bool.and_eq_true, decide_eq_true_eq] at h
                    obtain ⟨ht, hA⟩ := h
                    subst ht
                    simp only [PTm.full?, Option.some.injEq] at htf
                    subst htf
                    exact .callee (settlesTo_of_settledAt hset) (settlesTo_of_settledAt hA)
                | bad => simp at h
                | direct => simp [FunPart.dom?] at hd
                | side => simp [FunPart.dom?] at hd
        | none =>
          have key : ∀ o' : Option (Dom _), o' = o →
              Canon Γ ps (.lam o t) G (.lam Tw a') := by
            intro o' ho'
            subst ho'
            simp only [htf] at h
            split at h
            · rename_i C T1 T2
              simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
              obtain ⟨⟨hT, h1⟩, h2 | h2⟩ := h
              · exact .lamFun htf hT (canonB_sound t _ a' h1) (canonB_sound t none a' h2)
              · exact .lamFunChk htf hT (canonB_sound t _ a' h1) (lamChecksB_sound h2)
            · rw [Bool.and_eq_true, Bool.and_eq_true] at h
              obtain ⟨⟨hG, h1⟩, h2⟩ := h
              cases hset : settledAt (funPartOf Γ G) n with
              | none => simp [hset] at h2
              | some fp =>
                simp only [hset, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
                  Option.isNone_iff_eq_none] at h2
                obtain ⟨hbg, ho⟩ := h2
                refine .lamSyn htf (funGoal?_none_of hG) (settlesTo_of_settledAt hset) hbg ?_
                  (canonB_sound t none a' h1)
                rcases ho with ho | ⟨ho, hd⟩
                · exact .inl ho
                · exact .inr ⟨ho, hd⟩
          exact key o rfl
      | _ => simp at h
  | _, Γ, ps, .let tag ann t u, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | «let» ann' a1 a2 =>
        simp only at h
        rw [Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨h0, hp⟩, h⟩ := h
        simp only [decide_eq_true_eq] at h0 hp
        subst h0
        split at h
        · split at h
          · rename_i g _
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ht⟩, h⟩ := h
            split at h
            · rename_i F hF
              split at h
              · rename_i T hT
                simp only [Bool.and_eq_true] at h
                obtain ⟨⟨h1, h2⟩, h3⟩ := h
                obtain ⟨c, l, hc⟩ := settlesNonempty_sound h2
                obtain ⟨c', l', hc'⟩ := settlesNonempty_sound h3
                exact .arg ht (settlesTo_of_settledAt hF) hT (canonB_sound t _ a1 h1)
                  ⟨c, l, hc⟩ ⟨c', l', hc'⟩
              · cases h
            · cases h
          · split at h
            · rename_i A
              simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
              obtain ⟨⟨⟨⟨rfl, rfl⟩, ht⟩, hw⟩, h⟩ := h
              split at h
              · rename_i T hR
                simp only [Bool.and_eq_true] at h
                obtain ⟨⟨h1, h2⟩, h3⟩ := h
                obtain ⟨c, l, hc⟩ := settlesNonempty_sound h2
                obtain ⟨c', l', hc'⟩ := settlesNonempty_sound h3
                exact .val ht hw hR (canonB_sound t _ a1 h1) ⟨c, l, hc⟩ ⟨c', l', hc'⟩
              · cases h
            · cases h
        · rename_i hroute
          have hr : letRoute tag ann u = false := by simpa using hroute
          rw [Bool.and_eq_true] at h
          obtain ⟨h1, h⟩ := h
          split at h
          · rename_i r1s hrs
            have hs := settlesTo_of_settledAt hrs
            rw [Bool.and_eq_true] at h
            obtain ⟨h3, h4⟩ := h
            have hpl := allPlain_sound h3
            have hplain : ∀ r1, CandOf Γ ps a1 r1 → ∃ p, r1.split = .inl p := fun r1 hc => by
              obtain ⟨p, hp, _⟩ := hpl r1 (candOf_mem hs hc)
              exact ⟨p, hp⟩
            have hbody : ∀ r1 p, CandOf Γ ps a1 r1 → r1.split = .inl p →
                ∀ G' ∈ letGoals Γ ps ann G, Canon (Γ.cons p.ty) (psVar ps) u G' a2 := by
              intro r1 p hc hsp G' hG'
              obtain ⟨p', hp', hf⟩ := hpl r1 (candOf_mem hs hc)
              rw [hsp] at hp'
              cases hp'
              rw [List.all_eq_true] at hf
              exact canonB_sound u G' a2 (hf G' hG')
            split at h4
            · rename_i E
              simp only [Bool.or_eq_true] at h4
              rcases h4 with h4 | h4
              · refine .letGen hp hr (canonB_sound t none a1 h1) hplain hbody ?_
                intro _ _ r1 p hc hsp
                obtain ⟨p', hp', hf⟩ := allPlain_sound h4 r1 (candOf_mem hs hc)
                rw [hsp] at hp'
                cases hp'
                exact canonB_sound u none a2 hf
              · obtain ⟨c, hc⟩ := settlesSome_sound h4
                exact .letChk hp hr (canonB_sound t none a1 h1) hplain
                  (fun r1 p hc hsp => hbody r1 p hc hsp _ (by simp [letGoals])) hs hc
            · rename_i hne
              refine .letGen hp hr (canonB_sound t none a1 h1) hplain hbody ?_
              intro hann hG
              cases G with
              | none => cases hG
              | some E => exact (hne E hann rfl).elim
          · cases h
      | _ => simp at h
  | _, Γ, ps, .asc t T, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | asc a1 T' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, ht⟩, h1⟩ := h
        exact .asc ht (canonB_sound t _ a1 h1)
      | _ => simp at h
  | _, Γ, ps, .obj o d, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases o with
      | none =>
        cases a with
        | obj S e =>
          simp only at h
          split at h
          · rename_i E
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hS, h1⟩, h2⟩ := h
            obtain ⟨hfill, hc, ht⟩ := canonDefsB_sound d _ _ e h1
            obtain ⟨c, cs, hacc⟩ := settlesNonempty_sound h2
            exact .objGoal (settlesTo_of_settledAt hS) hfill hc ht ⟨c, cs, hacc⟩
          · cases h
        | _ => simp at h
      | some S =>
        cases a with
        | obj S' e =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨rfl, hd⟩, h1⟩ := h
          obtain ⟨hfill, hc, ht⟩ := canonDefsB_sound d _ _ e h1
          exact .obj hd hfill hc ht
        | _ => simp at h
  | _, Γ, ps, .path _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, ps, .app _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, ps, .proj _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, ps, .letex _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, ps, .box _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, ps, .unbox _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
termination_by structural _ _ _ p => p

/-- `canonDefsB` decides the lockstep fill of a literal's definitions and the
premises of its fields soundly. -/
theorem canonDefsB_sound {n : Nat} : {s : Sig} → {Γ : Ctx s} → {ps : CaptureSet s} →
    (d : PDefs s) → (Sw Sr : Shape s) → (e : ADefs s) → canonDefsB n Γ ps d Sw Sr e = true →
    DefsFill d Sw Sr e ∧ (∀ t Tr b, SlotField d Sw Sr e t Tr b → Canon Γ ps t (some (.ty Tr)) b) ∧
      (∀ t Tr b, SlotField d Sw Sr e t Tr b →
        ∃ c cs, SettlesTo (inferF Γ ps (sizeATm b) b (some (.ty Tr))) (c :: cs))
  | _, Γ, ps, .typ A S0, Sw, Sr, e, h => by
    cases e with
    | typ A' S0' =>
      simp only [canonDefsB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.typ, ?_, ?_⟩ <;> intro _ _ _ hs <;> cases hs
    | _ => simp [canonDefsB] at h
  | _, Γ, ps, .cap C c, Sw, Sr, e, h => by
    cases e with
    | cap C' c' =>
      simp only [canonDefsB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.cap, ?_, ?_⟩ <;> intro _ _ _ hs <;> cases hs
    | _ => simp [canonDefsB] at h
  | _, Γ, ps, .trm a o t, Sw, Sr, e, h => by
    cases Sw with
    | fld c Tw =>
      cases Sr with
      | fld c' Tr =>
        cases e with
        | trm a' b =>
          unfold canonDefsB at h
          rw [Bool.and_eq_true, Bool.and_eq_true] at h
          obtain ⟨⟨h0, ho⟩, h1⟩ := h
          simp only [decide_eq_true_eq] at h0
          subst h0
          split at h1
          · rename_i b' hb
            simp only [decide_eq_true_eq] at h1
            subst h1
            refine ⟨.trmFull ho hb, fun _ _ _ hs => ?_, fun _ _ _ hs => ?_⟩
            · cases hs with
              | here ht => rw [hb] at ht; cases ht
            · cases hs with
              | here ht => rw [hb] at ht; cases ht
          · rename_i hb
            rw [Bool.and_eq_true] at h1
            obtain ⟨h2, h3⟩ := h1
            obtain ⟨c0, cs, hcs⟩ := settlesNonempty_sound h3
            refine ⟨.trmSlot ho hb, fun _ _ _ hs => ?_, fun _ _ _ hs => ?_⟩
            · cases hs with
              | here _ => exact canonB_sound t _ b h2
            · cases hs with
              | here _ => exact ⟨c0, cs, hcs⟩
        | _ => simp [canonDefsB] at h
      | _ => cases e <;> simp [canonDefsB] at h
    | _ => cases Sr <;> cases e <;> simp [canonDefsB] at h
  | _, Γ, ps, .and d1 d2, Sw, Sr, e, h => by
    cases Sw with
    | and S1 S2 =>
      cases Sr with
      | and R1 R2 =>
        cases e with
        | and e1 e2 =>
          simp only [canonDefsB, Bool.and_eq_true] at h
          obtain ⟨f1, c1, t1⟩ := canonDefsB_sound d1 S1 R1 e1 h.1
          obtain ⟨f2, c2, t2⟩ := canonDefsB_sound d2 S2 R2 e2 h.2
          refine ⟨.and f1 f2, fun t T b hs => ?_, fun t T b hs => ?_⟩
          · cases hs with
            | left hs => exact c1 t T b hs
            | right hs => exact c2 t T b hs
          · cases hs with
            | left hs => exact t1 t T b hs
            | right hs => exact t2 t T b hs
        | _ => simp [canonDefsB] at h
      | _ => cases e <;> simp [canonDefsB] at h
    | _ => cases Sr <;> cases e <;> simp [canonDefsB] at h
termination_by structural _ _ _ d => d
end

/-- Whether the written program `w` with its body replaced by the erased body
`e` resolves to a partial body whose canonical fill is the written body, the
typer types that body at the context of the platform, and the fill agrees
with every slot the erased body writes, all read from a full tank of `n`
units.  The header is the written program's, since a header has no slot. -/
def canonAt (Λ : LabelTable) (w : SProg) (e : STm) (n : Nat := defaultFuel) : Bool :=
  match resolveHeader Λ w with
  | none => false
  | some h =>
      match resolvePTop Λ h.table w.platNames e, resolvePTop Λ h.table w.platNames w.body with
      | some q, some qw =>
          match qw.full? with
          | some a =>
              canonB n h.plat.ctx w.platNames.set q none a &&
                (synthInF h.plat.ctx w.platNames.set a n).1.isSome && q.fills a
          | none => false
      | _, _ => false

/-- **Completeness at the direct sites, decided.**  A written program whose
body is erased compiles as the written program does, declared use set and
record included, at every budget from some fuel on, when `canonAt` relates
the two. -/
theorem compile_complete_canonAt {Λ : LabelTable} {w : SProg} {e : STm} {n : Nat}
    (h : canonAt Λ w e n = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λ { w with body := e } = compile b Λ w := by
  unfold canonAt at h
  split at h
  · cases h
  · rename_i hd hh
    split at h
    · rename_i q qw hq hqw
      split at h
      · rename_i a ha
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp h2
        have hp : resolvePProg Λ { w with body := e } = some (hd, q) := by
          unfold resolvePProg
          change (resolveHeader Λ w).bind _ = _
          rw [hh, Option.bind_some]
          show Option.map (fun x => (hd, x)) (resolvePTop Λ hd.table w.platNames e) = some (hd, q)
          rw [hq]
          rfl
        have hw : resolveProg Λ w = some (hd.withBody a) := by
          rw [resolveProg_eq]
          unfold resolvePProg
          rw [hh, Option.bind_some, hqw]
          simp only [Option.map_some, Option.bind_some, ha]
        obtain ⟨n0, h0⟩ := compile_complete_direct hp (canonB_sound q none a h1) hc0 h3
        exact ⟨n0, fun b hb => by rw [compile_full hw]; exact h0 b hb⟩
      · cases h
    · cases h

end Complete

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
