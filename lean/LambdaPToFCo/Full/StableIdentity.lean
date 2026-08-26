import LambdaPToFCo.Full.FunctionModel
import LambdaPToFCo.Full.ValueInterface

/-!
# Static stable-identity adapters

An adapter in this module is stronger than an arbitrary well-typed package
coercion. Its proof-relevant law records that every primitive conversion is
either identity or an unpack/repack whose target interface reuses the exact
hidden identity type and payload of the opened source interface. Composition
retains that law structurally.

This is deliberately a static law. Open target contexts may contain coercion
variables, so even a typed Bottom eliminator need not reduce. Operational
preservation belongs after closing/coherence hypotheses are available.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace StableIdentity

/-- Source plan under the adapter's input-package binder. -/
def sourceAtBinder (source : ValuePlan sig) : ValuePlan (sig ,, .var) :=
  source.rename (Rename.weaken .var)

/-- Target plan reindexed into the final scope of the opened source. -/
def targetAtSource (source target : ValuePlan sig) :
    ValuePlan (sourceAtBinder source).scope :=
  (target.rename (Rename.weaken .var)).rename
    (sourceAtBinder source).telescope.weaken

/-- Context in which the source package has been opened. -/
def openedContext (base : Ctx sig) (source : ValuePlan sig) :
    Ctx (sourceAtBinder source).scope :=
  (sourceAtBinder source).context (base.bindVar source.inputTy)

/-- Target observation fields after fixing their hidden identity and payload
to the exact projections of the opened source interface. -/
def observationTelescope (source target : ValuePlan sig) :
    Telescope (sourceAtBinder source).scope :=
  (((targetAtSource source target).observations.subst
    ((Subst.openTVar (sourceAtBinder source).identityTy).lift .var)).subst
      (Subst.openVar (sourceAtBinder source).payload))

/-- A primitive same-identity repack. Only target-specific observations are
supplied; the mandatory `I, i : I` prefix is fixed by construction. -/
structure Repack (base : Ctx sig) (source target : ValuePlan sig) : Type where
  observations : Telescope.Args (openedContext base source)
    (observationTelescope source target)

namespace Repack

/-- The target interface produced inside the opened source package. -/
noncomputable def interface (repack : Repack base source target) :
    ValueInterface (openedContext base source) :=
  { plan := targetAtSource source target
    identity := (sourceAtBinder source).identityTy
    payload := (sourceAtBinder source).payload
    payloadTyping :=
      (sourceAtBinder source).payload_hasType (base.bindVar source.inputTy)
    observations := repack.observations }

@[simp] theorem interface_plan (repack : Repack base source target) :
    repack.interface.plan = targetAtSource source target := by
  rfl

/-- The central stable-identity law: output and source use the same hidden
identity type, definitionally. -/
@[simp] theorem interface_identity (repack : Repack base source target) :
    repack.interface.identity = (sourceAtBinder source).identityTy := by
  rfl

/-- The central stable-payload law: output and source use the same payload
term, definitionally, with its original identity typing bridge. -/
@[simp] theorem interface_payload (repack : Repack base source target) :
    repack.interface.payload = (sourceAtBinder source).payload := by
  rfl

/-- The unchanged payload remains typed at the unchanged hidden identity. -/
noncomputable def interface_payloadTyping
    (repack : Repack base source target) :
    Exp.HasType (openedContext base source) repack.interface.payload
      repack.interface.identity :=
  repack.interface.payloadTyping

/-- The adapter-bound source package variable at its renamed input type. -/
noncomputable def packageTyping (base : Ctx sig)
    (source : ValuePlan sig) :
    Exp.HasType (base.bindVar source.inputTy) (.var .here)
      (sourceAtBinder source).inputTy := by
  have variableTyping :
      Exp.HasType (base.bindVar source.inputTy) (.var .here)
        (source.inputTy.weaken .var) :=
    .var Ctx.Lookup.here
  change Exp.HasType (base.bindVar source.inputTy) (.var .here)
    (source.inputTy.rename (Rename.weaken .var)) at variableTyping
  simpa only [sourceAtBinder, ValuePlan.inputTy_rename] using variableTyping

/-- The exact target package constructed under the opened source. -/
noncomputable def result (repack : Repack base source target) :
    Exp (sourceAtBinder source).scope :=
  repack.interface.package

noncomputable def result_hasType (repack : Repack base source target) :
    Exp.HasType (openedContext base source) repack.result
      ((target.inputTy.weaken .var).rename
        (sourceAtBinder source).telescope.weaken) := by
  have packed := repack.interface.package_hasType
  change Exp.HasType (openedContext base source) repack.result
    (targetAtSource source target).inputTy at packed
  change Exp.HasType (openedContext base source) repack.result
    (((target.rename (Rename.weaken .var)).rename
      (sourceAtBinder source).telescope.weaken).inputTy) at packed
  change Exp.HasType (openedContext base source) repack.result
    ((target.inputTy.rename (Rename.weaken .var)).rename
      (sourceAtBinder source).telescope.weaken)
  simpa only [ValuePlan.inputTy_rename] using packed

/-- Canonical computational body: unpack source, then run the exact-I/i
target repack. -/
noncomputable def body {sig : Sig} {base : Ctx sig}
    {source target : ValuePlan sig}
    (repack : Repack base source target) :
    Exp (sig ,, .var) :=
  (sourceAtBinder source).unpack (.var .here)
    (target.inputTy.weaken .var) repack.result

noncomputable def body_hasType {sig : Sig} {base : Ctx sig}
    {source target : ValuePlan sig}
    (repack : Repack base source target) :
    Exp.HasType (base.bindVar source.inputTy) repack.body
      (target.inputTy.weaken .var) :=
  (sourceAtBinder source).unpack_hasType
    (packageTyping base source) repack.result_hasType

end Repack

/-- Proof-relevant syntax law for stable identity preservation. Primitive
repack nodes expose the exact interface law above; composition retains the
two laws without pretending its nested cast is a single endpoint equality. -/
inductive Law (base : Ctx sig) :
    (source target : ValuePlan sig) -> Exp (sig ,, .var) -> Type where
  | identity (plan : ValuePlan sig) :
      Law base plan plan (.var .here)
  | repack (witness : Repack base source target) :
      Law base source target witness.body
  | compose
      (first : Law base source middle firstBody)
      (second : Law base middle target secondBody) :
      Law base source target
        (.cast firstBody
          ((.adapter middle.inputTy secondBody : Co sig).weaken .var))

/-- A typed computational adapter plus its stable-identity syntax law. -/
structure Adapter (base : Ctx sig) (source target : ValuePlan sig) : Type where
  body : Exp (sig ,, .var)
  bodyTyping : Exp.HasType (base.bindVar source.inputTy) body
    (target.inputTy.weaken .var)
  law : Law base source target body

namespace Adapter

def coercion {sig : Sig} {base : Ctx sig}
    {source target : ValuePlan sig}
    (adapter : Adapter base source target) : Co sig :=
  .adapter source.inputTy adapter.body

noncomputable def coercion_hasType
    {sig : Sig} {base : Ctx sig} {source target : ValuePlan sig}
    (adapter : Adapter base source target) :
    Co.HasType base adapter.coercion source.inputTy target.inputTy :=
  .adapter adapter.bodyTyping

def apply {sig : Sig} {base : Ctx sig}
    {source target : ValuePlan sig}
    (adapter : Adapter base source target) (package : Exp sig) :
    Exp sig :=
  .cast package adapter.coercion

noncomputable def apply_hasType
    {sig : Sig} {base : Ctx sig} {source target : ValuePlan sig}
    (adapter : Adapter base source target) {package : Exp sig}
    (packageTyping : Exp.HasType base package source.inputTy) :
    Exp.HasType base (adapter.apply package) target.inputTy :=
  .cast packageTyping adapter.coercion_hasType

/-- Identity returns the exact input package. -/
noncomputable def identity {sig : Sig}
    (base : Ctx sig) (plan : ValuePlan sig) :
    Adapter base plan plan where
  body := .var .here
  bodyTyping := .var Ctx.Lookup.here
  law := .identity plan

/-- Promote a canonical exact-I/i repack to an adapter. -/
noncomputable def ofRepack {sig : Sig} {base : Ctx sig}
    {source target : ValuePlan sig}
    (repack : Repack base source target) :
    Adapter base source target where
  body := repack.body
  bodyTyping := repack.body_hasType
  law := .repack repack

/-- Sequential adapter body. The intermediate package is passed to the
second adapter by an ordinary target cast. -/
def composeBody {sig : Sig} {base : Ctx sig}
    {source middle target : ValuePlan sig}
    (first : Adapter base source middle)
    (second : Adapter base middle target) : Exp (sig ,, .var) :=
  .cast first.body (second.coercion.weaken .var)

noncomputable def compose {sig : Sig} {base : Ctx sig}
    {source middle target : ValuePlan sig}
    (first : Adapter base source middle)
    (second : Adapter base middle target) : Adapter base source target where
  body := composeBody first second
  bodyTyping := by
    apply Exp.HasType.cast first.bodyTyping
    exact second.coercion_hasType.weaken (.var source.inputTy)
  law := by
    exact .compose first.law second.law

end Adapter

/-! ## Honest generic constructors -/

/-- Constructor used by Single, Selection, and Function translations: the
caller supplies precisely the observation spine justified in the opened
source context; stable identity and payload cannot be changed. -/
def Repack.ofObservations (base : Ctx sig)
    (source target : ValuePlan sig)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source target)) :
    Repack base source target :=
  ⟨observations⟩

/-- Promote a justified target observation spine directly to an adapter. -/
noncomputable def Adapter.ofObservations (base : Ctx sig)
    (source target : ValuePlan sig)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source target)) :
    Adapter base source target :=
  .ofRepack (Repack.ofObservations base source target observations)

/-- Forget every observation while retaining the exact hidden interface. -/
def Repack.toTop (base : Ctx sig) (source : ValuePlan sig) :
    Repack base source (Top.plan sig) where
  observations := .nil

noncomputable def Adapter.toTop (base : Ctx sig)
    (source : ValuePlan sig) : Adapter base source (Top.plan sig) :=
  .ofRepack (Repack.toTop base source)

/-- Build a Bottom demand from a justified retained eliminator observation. -/
noncomputable def Adapter.toBot (base : Ctx sig)
    (source : ValuePlan sig)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source (Bot.plan sig))) :
    Adapter base source (Bot.plan sig) :=
  .ofObservations base source (Bot.plan sig) observations

/-- Build a singleton demand from its two justified bridge observations. -/
noncomputable def Adapter.toSingle (base : Ctx sig)
    (source : ValuePlan sig) (referentIdentity : Ty sig)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source (Single.plan referentIdentity))) :
    Adapter base source (Single.plan referentIdentity) :=
  .ofObservations base source (Single.plan referentIdentity) observations

/-- Build a selection demand only from an explicitly justified opaque
witness bridge. Source path-origin evidence is supplied above this target-only
layer. -/
noncomputable def Adapter.toSelection (base : Ctx sig)
    (source : ValuePlan sig) (witnessIdentity : Ty sig)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source (Selection.plan witnessIdentity))) :
    Adapter base source (Selection.plan witnessIdentity) :=
  .ofObservations base source (Selection.plan witnessIdentity) observations

/-- Build a dependent-function demand from its justified implementation
observation. -/
noncomputable def Adapter.toFunction (base : Ctx sig)
    (source : ValuePlan sig) (domain : ValuePlan sig)
    (codomain : ValuePlan domain.scope)
    (observations : Telescope.Args (openedContext base source)
      (observationTelescope source (Function.plan domain codomain))) :
    Adapter base source (Function.plan domain codomain) :=
  .ofObservations base source (Function.plan domain codomain) observations

namespace BottomSynthesis

/-- Structural measure invariant under dependent substitution. -/
def fieldCount : Telescope sig -> Nat
  | .nil => 0
  | .var _ tail => fieldCount tail + 1
  | .tvar tail => fieldCount tail + 1
  | .cvar _ _ tail => fieldCount tail + 1

@[simp] theorem fieldCount_subst (tele : Telescope source)
    (substitution : Subst source target) :
    fieldCount (tele.subst substitution) = fieldCount tele := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [Telescope.subst, fieldCount]
      rw [ih (substitution.lift .var)]
  | tvar tail ih =>
      simp only [Telescope.subst, fieldCount]
      rw [ih (substitution.lift .tvar)]
  | cvar source target tail ih =>
      simp only [Telescope.subst, fieldCount]
      rw [ih (substitution.lift .cvar)]

/-- Populate any mixed observation telescope from target bottom. This is a
static construction: term fields need not be target values in an open
context. -/
noncomputable def arguments {sig : Sig} {base : Ctx sig}
    (bottom : Exp sig) (bottomTyping : Exp.HasType base bottom Ty.bottom) :
    (tele : Telescope sig) -> Telescope.Args base tele
  | .nil => .nil
  | .var type tail =>
      let argument : Exp sig := .cast bottom (.bottom type)
      let argumentTyping : Exp.HasType base argument type :=
        .cast bottomTyping Co.HasType.bottom
      .var argument argumentTyping
        (arguments bottom bottomTyping
          (tail.subst (Subst.openVar argument)))
  | .tvar tail =>
      .tvar Ty.bottom
        (arguments bottom bottomTyping
          (tail.subst (Subst.openTVar Ty.bottom)))
  | .cvar source target tail =>
      let body : Exp (sig ,, .var) :=
        .cast (bottom.weaken .var) (.bottom (target.weaken .var))
      let bodyTyping :
          Exp.HasType (base.bindVar source) body (target.weaken .var) := by
        apply Exp.HasType.cast
        · simpa only [Ty.bottom_rename] using
            bottomTyping.weaken (.var source)
        · exact Co.HasType.bottom
      let evidence : Co sig := .adapter source body
      let evidenceTyping : Co.HasType base evidence source target :=
        .adapter bodyTyping
      .cvar evidence evidenceTyping
        (arguments bottom bottomTyping
          (tail.subst (Subst.openCVar evidence)))
termination_by tele => fieldCount tele
decreasing_by
  all_goals
    rw [fieldCount_subst]
    simp only [fieldCount, Nat.lt_add_one_iff]
    exact Nat.le_refl _

end BottomSynthesis

/-- Bottom can statically synthesize every target observation while retaining
the exact hidden identity and payload. No open-context reduction claim is
made. -/
noncomputable def Repack.fromBottom (base : Ctx sig)
    (target : ValuePlan sig) : Repack base (Bot.plan sig) target where
  observations := by
    let bottom := Bot.eliminatePayload (sig ,, .var)
    have bottomTyping :
        Exp.HasType (openedContext base (Bot.plan sig)) bottom Ty.bottom := by
      simpa only [openedContext, sourceAtBinder] using
        Bot.eliminatePayload_hasType
          (base.bindVar (Bot.plan sig).inputTy)
    exact BottomSynthesis.arguments bottom bottomTyping _

noncomputable def Adapter.fromBottom (base : Ctx sig)
    (target : ValuePlan sig) : Adapter base (Bot.plan sig) target :=
  .ofRepack (Repack.fromBottom base target)

/-! Focused construction regressions. -/

noncomputable example (base : Ctx sig) (plan : ValuePlan sig) :
    Co.HasType base (Adapter.identity base plan).coercion
      plan.inputTy plan.inputTy :=
  (Adapter.identity base plan).coercion_hasType

noncomputable example (base : Ctx sig) (plan : ValuePlan sig) :
    Adapter base plan plan :=
  (Adapter.identity base plan).compose (Adapter.identity base plan)

noncomputable example (base : Ctx sig) (source : ValuePlan sig) :
    Adapter base source (Top.plan sig) :=
  Adapter.toTop base source

noncomputable example (base : Ctx sig) (target : ValuePlan sig) :
    Adapter base (Bot.plan sig) target :=
  Adapter.fromBottom base target

end StableIdentity

end LambdaPToFCo.Full
