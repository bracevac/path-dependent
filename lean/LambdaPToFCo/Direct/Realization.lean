import LambdaPToFCo.Direct.MaterialTermPath
import LambdaPToFCo.Direct.Relation
import LambdaPToFCo.Direct.TermIntroduction
import LambdaPToFCo.Direct.ValuePair

/-!
# Demand/value-indexed raw realization

This module defines the persistent raw compiler invariant. `demand` means
that a checked type has selected one exact raw representation.  `value`
additionally retains the exact `Shape.Interface`
of the compiled value, i.e. the information in a `Representation.Slot`.

The two modes deliberately share one family.  A function value can retain a
demand for its precise domain and a value realization for its compiled body.
Closure is admitted only through the exact representation/value closers
below; there is no constructor for an arbitrary `Rep.closed`.
-/

namespace LambdaPToFCo.Direct.Internal.Realization

open SystemFCo
open Representation

inductive Mode where
| demand
| value

/-- The mode payload.  In value mode this is exactly the missing field which
distinguishes a `Slot` from its bare `Rep`. -/
inductive Availability (base : Ctx sig) (shape : Shape sig) : Mode -> Type
| demand : Availability base shape .demand
| value (interface : Shape.Interface base shape) :
    Availability base shape .value

namespace Availability

def slot
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (rep : Rep base sourceType shape)
    (availability : Availability base shape .value) :
    Slot base sourceType := by
  cases availability with
  | value interface => exact { shape := shape, interface := interface, rep := rep }

noncomputable def targetRename
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {shape : Shape source} {mode : Mode}
    (availability : Availability sourceContext shape mode)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Availability targetContext (shape.rename mapping) mode := by
  cases availability with
  | demand => exact .demand
  | value interface => exact .value (interface.rename mapping typed)

noncomputable def targetSubst
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {shape : Shape source} {mode : Mode}
    (availability : Availability sourceContext shape mode)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Availability targetContext (shape.subst substitution) mode := by
  cases availability with
  | demand => exact .demand
  | value interface =>
      exact @Availability.value target targetContext
        (shape.subst substitution)
        (interface.targetSubst substitution typed)

end Availability

/-! ## Exact path identity retained by leaves -/

def IdentityAlignment
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {kind : LambdaPFC.Kind} {result : LambdaPFC.Tau n kind}
    (view : Path.View base result) (expected : Ty sig) : Prop := by
  cases view with
  | proper slot =>
      exact Nonempty (Conversion base slot.shape.inputTy expected)
  | @interval _ _ _ _ selected _ =>
      exact Nonempty (Conversion.Bridge base selected expected)

private def identityOfView
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {kind : LambdaPFC.Kind} {result : LambdaPFC.Tau n kind}
    (view : Path.View base result) : Ty sig := by
  cases view with
  | proper slot => exact slot.shape.inputTy
  | @interval _ _ _ _ selected _ => exact selected

private inductive Origin
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) :
    {kind : LambdaPFC.Kind} ->
    {path : LambdaPFC.Path n} ->
    {result : LambdaPFC.Tau n kind} ->
    (typing : LambdaPFC.Path.Ty sourceContext path result) ->
    Ty sig -> Type where
| aligned
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {identity : Ty sig}
    (alignment : MaterialTermPath.compileWith typing environment
      (fun focus _ view =>
        IdentityAlignment view (identity.rename focus.mapping))) :
    Origin environment typing identity
| exact
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    (view : Path.View base result) :
    Origin environment typing (identityOfView view)
| across
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    {typing : LambdaPFC.Path.Ty sourceContext path result}
    {left right : Ty sig}
    (origin : Origin environment typing left)
    (bridge : Conversion.Bridge base left right) :
    Origin environment typing right

/-- Sealed provenance for the hidden target identity chosen by one source
path.  The representation may be retargeted only through an explicit
bidirectional conversion; arbitrary interval identities cannot be minted. -/
structure PathIdentity
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    (identity : Ty sig) : Type where
  private mk ::
  origin : Origin environment typing identity

namespace PathIdentity

abbrev Consumer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (focus : MaterialTermPath.Focus rootContext currentContext) ->
    (currentEnvironment : Env sourceContext currentContext) ->
    (view : Path.View currentContext result) ->
    PathIdentity currentEnvironment typing (identityOfView view) -> answer

/-- Run one literal material path and seal its exact proper/interval identity
inside the rank-2 continuation. This carries provenance only: the current
raw environment is not claimed to be a `ValidEnv`; view realization belongs
to the later `RealizedPath` layer. -/
noncomputable def resolveWith
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    (environment : Env sourceContext base)
    {answer : Type}
    (continuation : Consumer base typing answer) : answer :=
  MaterialTermPath.compileWith typing environment
    (fun focus currentEnvironment view =>
      continuation focus currentEnvironment view
        (PathIdentity.mk (.exact typing view)))

private noncomputable def constantToInterface
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig) :
    Conversion base source shape.inputTy :=
  Conversion.ofFunction
    (Adapter.ofBody source
      (interface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken] using
        interface.package_hasType.weaken (.var source)))

/-- Tie a proper path to one exact retained value without replay.  The
reverse direction is value-specific: it returns that retained package. -/
noncomputable def retained
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (environment : Env sourceContext base)
    {selectedSource : LambdaPFC.Ty n}
    (selected : Slot base selectedSource) :
    PathIdentity environment typing selected.shape.inputTy := by
  refine PathIdentity.mk (.aligned typing ?_)
  exact MaterialTermPath.compileWith_fuse typing environment
    (fun _ _ _ => True)
    (fun _ _ _ => True)
    (fun focus _ view => IdentityAlignment view
      (selected.shape.inputTy.rename focus.mapping))
    (fun focus _ view _ _ => by
      cases view with
      | proper current =>
          refine ⟨?_⟩
          simpa only [Shape.inputTy_rename] using
            constantToInterface
              (selected.interface.rename focus.mapping focus.typed)
              current.shape.inputTy)
    (by exact True.intro)
    (by exact True.intro)

/-- The newest/older variable path resolves to the exact slot stored in the
raw environment. -/
noncomputable def lookup
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n) :
    PathIdentity environment
      (LambdaPFC.Path.Ty.var (Γ := sourceContext) (x := index))
      (environment.lookup index).shape.inputTy := by
  refine PathIdentity.mk (.aligned _ ?_)
  rw [MaterialTermPath.compileWith_var]
  refine ⟨?_⟩
  simpa only [MaterialTermPath.Focus.root, Ty.rename_id] using
    (Conversion.refl base (environment.lookup index).shape.inputTy)

/-- Transport sealed path provenance through one explicit identity bridge. -/
noncomputable def across
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {environment : Env sourceContext base}
    {kind : LambdaPFC.Kind} {path : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    {typing : LambdaPFC.Path.Ty sourceContext path result}
    {left right : Ty sig}
    (resolution : PathIdentity environment typing left)
    (bridge : Conversion.Bridge base left right) :
    PathIdentity environment typing right :=
  PathIdentity.mk (.across resolution.origin bridge)

end PathIdentity

/-! ## Exact compiler-produced value constructors -/

noncomputable def singletonSlot
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {referentSource : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n) (selected : Slot base referentSource) :
    Slot base (.Single path) where
  shape := .stable (Single.plan selected.shape.inputTy)
  interface := {
    arguments := Single.exactArguments selected.shape.inputTy
      selected.interface.package selected.interface.package_hasType
  }
  rep := .singleton base path selected.shape.inputTy

/-- Raw counterpart of the exact abstraction constructor: the body package
is the function payload, and its representation is the precise codomain
representation in the opened domain scope. -/
noncomputable def functionSlot
    {n : Nat}
    {sig : Sig} {base : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig}
    (domainRep : Rep base domainSource domain)
    (body : Slot (domain.context base) codomainSource) :
    Slot base (.Fun domainSource codomainSource) where
  shape := .stable (Function.plan domain body.shape)
  interface := {
    arguments := Function.exactArguments domain body.shape
      (domain.binders.lambda body.interface.package)
      (domain.binders.lambda_hasType body.interface.package_hasType)
  }
  rep := .function domainRep body.rep

/-- Fully structural proper-pair value built from the actual first/member
interfaces.  The member interface already lives after the actual first
substitution used by the material callback. -/
noncomputable def properPairSlotAt
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    (firstRep : Rep base firstSource first)
    (memberRep : Rep (first.context base) memberSource member)
    (firstInterface : Shape.Interface base first)
    (memberInterface : Shape.Interface base
      (member.subst firstInterface.substitution)) :
    Slot base (.Pair firstSource label (.ty memberSource)) where
  shape := .stable (Pair.Proper.plan first member)
  interface := {
    arguments := Pair.Proper.exactArguments first member
      firstInterface.arguments (by
        simpa only [Shape.binders_subst] using memberInterface.arguments)
  }
  rep := .properPair firstRep memberRep

/-- A fully structural interval-pair value assembled from the actual mapped
first interface and the actual selected interval witness.  There is no
arbitrary outer Interface premise: its package arguments are definitionally
the exact structural arguments consumed later by `MaterialTermPath`.-/
noncomputable def intervalPairSlot
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    (firstRep : Rep base firstSource first)
    (lowerRep : Rep (first.context base) lowerSource lower)
    (upperRep : Rep (first.context base) upperSource upper)
    (firstInterface : Shape.Interface base first)
    (witness : Conversion.Interval.Witness base
      (lower.subst firstInterface.substitution)
      (upper.subst firstInterface.substitution)) :
    Slot base (.Pair firstSource label (.intv lowerSource upperSource)) where
  shape := .stable (Pair.Interval.plan first lower upper)
  interface := {
    arguments := Pair.Interval.exactArguments first lower upper
      firstInterface witness.selected witness.lowerFunction
      witness.lowerTyping witness.upperFunction witness.upperTyping
  }
  rep := .intervalPair firstRep lowerRep upperRep

/-! ## Exact source-path values -/

/-- Sealed evidence that this exact source path currently denotes this exact
source-typed raw Slot.  The capability deliberately carries no
`Path.Ty`: checked application arguments can reach their demanded source
type only through subsumption, including ill-Wf instantiated results.

The constructor is private and fieldless.  Public operations below can only
mint lookup values or preserve an existing value through exact singleton and
target transports. -/
inductive PathValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (path : LambdaPFC.Path n) (sourceType : LambdaPFC.Ty n)
    (slot : Slot base sourceType) : Type where
| private seal : PathValue environment path sourceType slot

namespace PathValue

/-- A source variable denotes exactly the Slot retained at its environment
index. -/
def lookup
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n) :
    PathValue environment (.var index) (sourceContext.lookup index)
      (environment.lookup index) :=
  .seal

/-- Preserve one exact path value through a typed target renaming. -/
noncomputable def targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {environment : Env sourceContext sourceBase}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {slot : Slot sourceBase sourceType}
    (_value : PathValue environment path sourceType slot)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    PathValue (environment.targetRename mapping typed) path sourceType
      (slot.targetRename mapping typed) :=
  .seal

/-- Preserve one exact path value through a typed target substitution. -/
noncomputable def targetSubst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {environment : Env sourceContext sourceBase}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {slot : Slot sourceBase sourceType}
    (_value : PathValue environment path sourceType slot)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceBase targetBase substitution) :
    PathValue (environment.targetSubst substitution typed) path sourceType
      (slot.targetSubst substitution typed) :=
  .seal

/-- Retag the same precise path at the exact singleton Slot compiled from
its retained value. -/
noncomputable def singleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {environment : Env sourceContext base}
    {path : LambdaPFC.Path n} {selectedSource : LambdaPFC.Ty n}
    {selected : Slot base selectedSource}
    (_value : PathValue environment path selectedSource selected) :
    PathValue environment path (.Single path)
      (singletonSlot path selected) :=
  .seal

end PathValue

/-! ## One mode-indexed invariant -/

inductive Realizes :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {sig : Sig} -> {base : Ctx sig} ->
    (environment : Env sourceContext base) ->
    {sourceType : LambdaPFC.Ty n} -> {shape : Shape sig} ->
    (rep : Rep base sourceType shape) ->
    {mode : Mode} -> Availability base shape mode -> Type where
| absurdDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (sourceType : LambdaPFC.Ty n)
    (bottom : Exp sig)
    (bottomTyping : Exp.HasType base bottom Adapter.bottomTy) :
    Realizes environment
      (Slot.absurd (sourceType := sourceType) bottom bottomTyping).rep .demand
| absurdValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (sourceType : LambdaPFC.Ty n)
    (bottom : Exp sig)
    (bottomTyping : Exp.HasType base bottom Adapter.bottomTy) :
    Realizes environment
      (Slot.absurd (sourceType := sourceType) bottom bottomTyping).rep
      (.value
        (Slot.absurd (sourceType := sourceType) bottom bottomTyping).interface)
| exFalsoValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (rep : Rep base sourceType shape)
    (interface : Shape.Interface base shape)
    (bottom : Exp sig)
    (bottomTyping : Exp.HasType base bottom Adapter.bottomTy) :
    Realizes environment rep (.value interface)
| topDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) :
    @Realizes n sourceContext sig base environment .Top
      (.stable (Top.plan sig)) (@Rep.top n sig base) .demand .demand
| topValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (interface : Shape.Interface base (.stable (Top.plan sig))) :
    @Realizes n sourceContext sig base environment .Top
      (.stable (Top.plan sig)) (@Rep.top n sig base) .value (.value interface)
| bottomDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) :
    @Realizes n sourceContext sig base environment .Bot
      (.stable (Bot.plan sig)) (@Rep.bottom n sig base) .demand .demand
| bottomValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (interface : Shape.Interface base (.stable (Bot.plan sig))) :
    @Realizes n sourceContext sig base environment .Bot
      (.stable (Bot.plan sig)) (@Rep.bottom n sig base) .value
      (.value interface)
| singletonDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {identity : Ty sig}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (resolution : PathIdentity environment typing identity) :
    Realizes environment (.singleton base path identity) .demand
| singletonValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {selectedSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (selected : Slot base selectedSource)
    (resolution : PathIdentity environment typing selected.shape.inputTy) :
    Realizes environment (singletonSlot path selected).rep
      (.value (singletonSlot path selected).interface)
| selectionDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selected : Ty sig}
    {lowerRep : Rep base lowerSource lower}
    {upperRep : Rep base upperSource upper}
    {lowerFunction : Exp sig}
    {lowerTyping : Exp.HasType base lowerFunction
      (.arrow lower.inputTy selected)}
    {upperFunction : Exp sig}
    {upperTyping : Exp.HasType base upperFunction
      (.arrow selected upper.inputTy)}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (resolution : PathIdentity environment typing selected) :
    Realizes environment
      (@Rep.selection sig n base path label lowerSource upperSource lower upper
        selected lowerRep upperRep lowerFunction lowerTyping upperFunction
        upperTyping) .demand
| selectionValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selected : Ty sig}
    {lowerRep : Rep base lowerSource lower}
    {upperRep : Rep base upperSource upper}
    {lowerFunction : Exp sig}
    {lowerTyping : Exp.HasType base lowerFunction
      (.arrow lower.inputTy selected)}
    {upperFunction : Exp sig}
    {upperTyping : Exp.HasType base upperFunction
      (.arrow selected upper.inputTy)}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (resolution : PathIdentity environment typing selected)
    (interface : Shape.Interface base (.opaque selected)) :
    Realizes environment
      (@Rep.selection sig n base path label lowerSource upperSource lower upper
        selected lowerRep upperRep lowerFunction lowerTyping upperFunction
        upperTyping) (.value interface)
| functionDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig} {codomain : Shape domain.scope}
    {domainRep : Rep base domainSource domain}
    {codomainRep : Rep (domain.context base) codomainSource codomain}
    (domainRealizes : Realizes environment domainRep .demand)
    (codomainRealizes : Realizes
      (environment.enter domainSource domain domainRep)
      codomainRep .demand) :
    Realizes environment
      (@Rep.function sig n base domainSource codomainSource domain codomain
        domainRep codomainRep) .demand
| functionValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig} {codomain : Shape domain.scope}
    {domainRep : Rep base domainSource domain}
    (domainRealizes : Realizes environment domainRep .demand)
    (body : Slot (domain.context base) codomainSource)
    (bodyRealizes : Realizes
      (environment.enter domainSource domain domainRep)
      body.rep (.value body.interface)) :
    Realizes environment (functionSlot domainRep body).rep
      (.value (functionSlot domainRep body).interface)
| properPairDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    {firstRep : Rep base firstSource first}
    {memberRep : Rep (first.context base) memberSource member}
    (firstRealizes : Realizes environment firstRep .demand)
    (memberRealizes : Realizes
      (environment.enter firstSource first firstRep) memberRep .demand) :
    Realizes environment
      (@Rep.properPair sig n base firstSource memberSource label first member
        firstRep memberRep) .demand
| properPairValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    {firstRep : Rep base firstSource first}
    {memberRep : Rep (first.context base) memberSource member}
    (firstInterface : Shape.Interface base first)
    (firstRealizes : Realizes environment firstRep
      (.value firstInterface))
    (memberInterface : Shape.Interface base
      (member.subst firstInterface.substitution))
    (memberRealizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      (memberRep.targetSubst firstInterface.substitution
        firstInterface.arguments.substitution_typed)
      (.value memberInterface)) :
    Realizes environment
      (properPairSlotAt (label := label) firstRep memberRep firstInterface
        memberInterface).rep
      (.value
        (properPairSlotAt (label := label) firstRep memberRep firstInterface
          memberInterface).interface)
| intervalPairDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    {firstRep : Rep base firstSource first}
    {lowerRep : Rep (first.context base) lowerSource lower}
    {upperRep : Rep (first.context base) upperSource upper}
    (firstRealizes : Realizes environment firstRep .demand)
    (lowerRealizes : Realizes
      (environment.enter firstSource first firstRep) lowerRep .demand)
    (upperRealizes : Realizes
      (environment.enter firstSource first firstRep) upperRep .demand) :
    Realizes environment
      (@Rep.intervalPair sig n base firstSource lowerSource upperSource label
        first lower upper firstRep lowerRep upperRep) .demand
| intervalPairValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    {firstRep : Rep base firstSource first}
    {lowerRep : Rep (first.context base) lowerSource lower}
    {upperRep : Rep (first.context base) upperSource upper}
    (firstInterface : Shape.Interface base first)
    (firstRealizes : Realizes environment firstRep
      (.value firstInterface))
    (lowerRealizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      (lowerRep.targetSubst firstInterface.substitution
        firstInterface.arguments.substitution_typed) .demand)
    (upperRealizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      (upperRep.targetSubst firstInterface.substitution
        firstInterface.arguments.substitution_typed) .demand)
    (witness : Conversion.Interval.Witness base
      (lower.subst firstInterface.substitution)
      (upper.subst firstInterface.substitution)) :
    Realizes environment
      (intervalPairSlot (label := label) firstRep lowerRep upperRep
        firstInterface witness).rep
      (.value
        (intervalPairSlot (label := label) firstRep lowerRep upperRep
          firstInterface witness).interface)
| typePairValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpoint : Wf.Proper base endpointSource)
    (endpointDemand : Realizes environment endpoint.rep .demand) :
    Realizes environment
      (TermIntroduction.typePairSlot environment index label endpoint).rep
      (.value (TermIntroduction.typePairSlot environment index label
        endpoint).interface)
| valuePairValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    (firstIndex memberIndex : Fin n) (label : LambdaPFC.Name) :
    Realizes environment
      (ValuePair.slot environment firstIndex memberIndex label).rep
      (.value
        (ValuePair.slot environment firstIndex memberIndex label).interface)
| closeDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    {inner : Shape focus.scope}
    {innerRep : Rep (focus.context base) sourceType inner}
    (innerRealizes : Realizes
      (environment.targetRename focus.weaken
        (focus.weaken_typed base)) innerRep .demand) :
    Realizes environment (innerRep.close focus) .demand
| closeValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    (focusPackage : Exp sig)
    (focusTyping : Exp.HasType base focusPackage focus.existsTy)
    (inner : Slot (focus.context base) sourceType)
    (innerRealizes : Realizes
      (environment.targetRename focus.weaken
        (focus.weaken_typed base))
      inner.rep (.value inner.interface)) :
    Realizes environment
      (MaterialTermPath.SlotMaterializer.closeTelescope
        focus focusPackage focusTyping inner).rep
      (.value (MaterialTermPath.SlotMaterializer.closeTelescope
        focus focusPackage focusTyping inner).interface)
| closeShapeValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base)
    {sourceType : LambdaPFC.Ty n}
    (owner : Shape sig)
    (ownerPackage : Exp sig)
    (ownerTyping : Exp.HasType base ownerPackage owner.inputTy)
    (inner : Slot (owner.context base) sourceType)
    (innerRealizes : Realizes
      (environment.targetRename owner.binders.weaken
        (owner.binders.weaken_typed base))
      inner.rep (.value inner.interface)) :
    Realizes environment
      (MaterialTermPath.SlotMaterializer.closeShape
        owner ownerPackage ownerTyping inner).rep
      (.value (MaterialTermPath.SlotMaterializer.closeShape
        owner ownerPackage ownerTyping inner).interface)
| sourceExtendHead
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {environment : Env sourceContext base}
    (boundSource : LambdaPFC.Ty n)
    {boundShape : Shape sig}
    (boundInterface : Shape.Interface base boundShape)
    (boundRep : Rep base boundSource boundShape)
    (boundRealizes : Realizes environment boundRep
      (.value boundInterface)) :
    Realizes
      (extendAtInterface environment boundSource boundInterface boundRep)
      (boundRep.sourceRename LambdaPFC.FinFun.weaken)
      (.value boundInterface)
| sourceExtendAligned
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {environment : Env sourceContext base}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    {rep : Rep base sourceType shape}
    {mode : Mode} {availability : Availability base shape mode}
    (realizes : Realizes environment rep availability)
    (boundSource : LambdaPFC.Ty n)
    {boundShape : Shape sig}
    (boundInterface : Shape.Interface base boundShape)
    (boundRep : Rep base boundSource boundShape) :
    Realizes
      (extendAtInterface environment boundSource boundInterface boundRep)
      (rep.sourceRename LambdaPFC.FinFun.weaken)
      availability
/-- Contract one exact newest source binding along the path value which
actually denotes its retained Slot.  This is intentionally not a generic
source-substitution constructor. -/
| sourceOpenAt
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {path : LambdaPFC.Path n} {firstSource : LambdaPFC.Ty n}
    {firstShape : Shape sig}
    {firstRep : Rep base firstSource firstShape}
    {firstInterface : Shape.Interface base firstShape}
    (environment : Env sourceContext base)
    (pathValue : PathValue environment path firstSource
      { shape := firstShape, interface := firstInterface, rep := firstRep })
    (firstRealizes : Realizes environment firstRep
      (.value firstInterface))
    {dependentSource : LambdaPFC.Ty (n + 1)}
    {dependentShape : Shape sig}
    {dependentRep : Rep base dependentSource dependentShape}
    {mode : Mode}
    {availability : Availability base dependentShape mode}
    (dependentRealizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      dependentRep availability) :
    Realizes environment
      (dependentRep.sourceSubst (LambdaPFC.PathSubst.openAt path))
      availability
/-- Lift one exact path-value contraction beneath a retained dependent-pair
first component.  The source opening is literally lifted; no environment or
representation equality is accepted. -/
| sourceOpenUnderFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {path : LambdaPFC.Path n} {boundSource : LambdaPFC.Ty n}
    {boundShape : Shape sig}
    {boundRep : Rep base boundSource boundShape}
    {boundInterface : Shape.Interface base boundShape}
    (environment : Env sourceContext base)
    (pathValue : PathValue environment path boundSource
      { shape := boundShape, interface := boundInterface, rep := boundRep })
    (boundRealizes : Realizes environment boundRep
      (.value boundInterface))
    {firstSource : LambdaPFC.Ty (n + 1)}
    {firstShape : Shape sig}
    {firstRep : Rep base firstSource firstShape}
    (firstInterface : Shape.Interface base firstShape)
    {dependentSource : LambdaPFC.Ty (n + 2)}
    {dependentShape : Shape sig}
    {dependentRep : Rep base dependentSource dependentShape}
    {mode : Mode}
    {availability : Availability base dependentShape mode}
    (dependentRealizes : Realizes
      (extendAtInterface
        (extendAtInterface environment boundSource boundInterface boundRep)
        firstSource firstInterface firstRep)
      dependentRep availability) :
    Realizes
      (extendAtInterface environment
        (firstSource.subst (LambdaPFC.PathSubst.openAt path))
        firstInterface
        (firstRep.sourceSubst (LambdaPFC.PathSubst.openAt path)))
      (dependentRep.sourceSubst
        (LambdaPFC.PathSubst.openAt path).lift)
      availability
/-- Commute one lexical source extension beneath a retained dependent-pair
first component.  The family uses the literal `weaken.ext` source rename and
then the actual first-interface target substitution. -/
| sourceExtendUnderFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {firstSource outerSource : LambdaPFC.Ty n}
    {firstShape outerShape : Shape sig}
    {firstRep : Rep base firstSource firstShape}
    {outerRep : Rep base outerSource outerShape}
    {firstInterface : Shape.Interface base firstShape}
    {outerInterface : Shape.Interface base outerShape}
    (environment : Env sourceContext base)
    {endpointSource : LambdaPFC.Ty (n + 1)}
    {endpointShape : Shape firstShape.scope}
    {endpointRep : Rep (firstShape.context base) endpointSource endpointShape}
    {mode : Mode}
    {availability : Availability base
      (endpointShape.subst firstInterface.substitution) mode}
    (endpointRealizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      (endpointRep.targetSubst firstInterface.substitution
        firstInterface.arguments.substitution_typed)
      availability) :
    Realizes
      (extendAtInterface
        (extendAtInterface environment outerSource outerInterface outerRep)
        firstSource.weaken firstInterface
        (firstRep.sourceRename LambdaPFC.FinFun.weaken))
      ((endpointRep.sourceRename LambdaPFC.FinFun.weaken.ext).targetSubst
        firstInterface.substitution
        firstInterface.arguments.substitution_typed)
      availability
/-- Positive target renaming through one literal retained environment
extension.  The result is fixed to extend the renamed environment with the
renamed retained package; this is not an arbitrary environment rebase. -/
| targetRenameExtended
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : Env sourceContext sourceBase)
    {firstSource : LambdaPFC.Ty n}
    {firstShape : Shape sourceSig}
    (firstInterface : Shape.Interface sourceBase firstShape)
    (firstRep : Rep sourceBase firstSource firstShape)
    {endpointSource : LambdaPFC.Ty (n + 1)}
    {endpointShape : Shape sourceSig}
    {endpointRep : Rep sourceBase endpointSource endpointShape}
    {mode : Mode}
    {availability : Availability sourceBase endpointShape mode}
    (realizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      endpointRep availability)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Realizes
      (extendAtInterface (environment.targetRename mapping typed) firstSource
        (firstInterface.rename mapping typed)
        (firstRep.targetRename mapping typed))
      (endpointRep.targetRename mapping typed)
      (availability.targetRename mapping typed)
/-- Exact target-substitution dual of `targetRenameExtended`.  The retained
extension is transported as one positive realization constructor, without
an equality or a general reindexing law. -/
| targetSubstExtended
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : Env sourceContext sourceBase)
    {firstSource : LambdaPFC.Ty n}
    {firstShape : Shape sourceSig}
    (firstInterface : Shape.Interface sourceBase firstShape)
    (firstRep : Rep sourceBase firstSource firstShape)
    {endpointSource : LambdaPFC.Ty (n + 1)}
    {endpointShape : Shape sourceSig}
    {endpointRep : Rep sourceBase endpointSource endpointShape}
    {mode : Mode}
    {availability : Availability sourceBase endpointShape mode}
    (realizes : Realizes
      (extendAtInterface environment firstSource firstInterface firstRep)
      endpointRep availability)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceBase targetBase substitution) :
    Realizes
      (extendAtInterface (environment.targetSubst substitution typed)
        firstSource (firstInterface.targetSubst substitution typed)
        (firstRep.targetSubst substitution typed))
      (endpointRep.targetSubst substitution typed)
      (availability.targetSubst substitution typed)
| targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {environment : Env sourceContext sourceBase}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sourceSig}
    {rep : Rep sourceBase sourceType shape}
    {mode : Mode} {availability : Availability sourceBase shape mode}
    (realizes : Realizes environment rep availability)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Realizes (environment.targetRename mapping typed)
      (rep.targetRename mapping typed)
      (availability.targetRename mapping typed)
| targetSubst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {environment : Env sourceContext sourceBase}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sourceSig}
    {rep : Rep sourceBase sourceType shape}
    {mode : Mode} {availability : Availability sourceBase shape mode}
    (realizes : Realizes environment rep availability)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceBase targetBase substitution) :
    Realizes (environment.targetSubst substitution typed)
      (rep.targetSubst substitution typed)
      (availability.targetSubst substitution typed)

namespace Realizes

/-- A same-run consumer for the selected demand opened by one literal
interval path.  The interval and its sealed identity are created together in
the one material callback, rather than by replaying the path. -/
abbrev SelectionConsumer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    {receiver : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (_typing : LambdaPFC.Path.Ty sourceContext (.sel receiver label)
      (.intv lowerSource upperSource))
    (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (focus : MaterialTermPath.Focus rootContext currentContext) ->
    (currentEnvironment : Env sourceContext currentContext) ->
    {lower upper : Shape current} -> {selected : Ty current} ->
    (interval : IntervalRep (targetContext := currentContext)
      lowerSource upperSource lower selected upper) ->
    Realizes currentEnvironment
      (interval.selection receiver label) .demand ->
    answer

/-- Run the literal interval path once and give the resulting exact selected
demand to that same callback.  The API accepts no independently chosen
interval or selected identity. -/
noncomputable def withSelectionDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {receiver : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel receiver label)
      (.intv lowerSource upperSource))
    (environment : Env sourceContext base)
    {answer : Type}
    (continuation : SelectionConsumer base typing answer) : answer :=
  PathIdentity.resolveWith typing environment
    (fun focus currentEnvironment view resolution => by
      cases view with
      | interval interval =>
          exact continuation focus currentEnvironment interval
            (Realizes.selectionDemand currentEnvironment typing resolution))

end Realizes

/-! ## Pointwise environments contain values, never bare demands -/

structure ValidEnv
    {n : Nat} {sig : Sig}
    (sourceContext : LambdaPFC.Ctx n) (base : Ctx sig) : Type where
  raw : Env sourceContext base
  valid : (index : Fin n) ->
    Realizes raw (raw.lookup index).rep
      (.value (raw.lookup index).interface)

namespace ValidEnv

def empty (base : Ctx sig) :
    ValidEnv (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0) base where
  raw := Env.empty base
  valid index := Fin.elim0 index

def lookup
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : ValidEnv sourceContext base) (index : Fin n) :
    Realizes environment.raw (environment.raw.lookup index).rep
      (.value (environment.raw.lookup index).interface) :=
  environment.valid index

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : ValidEnv sourceContext sourceBase)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    ValidEnv sourceContext targetBase where
  raw := environment.raw.targetRename mapping typed
  valid index := by
    simpa only [Env.targetRename, Slot.targetRename] using
      Realizes.targetRename (environment.valid index) mapping typed

noncomputable def targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : ValidEnv sourceContext sourceBase)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceBase targetBase substitution) :
    ValidEnv sourceContext targetBase where
  raw := environment.raw.targetSubst substitution typed
  valid index := by
    simpa only [Env.targetSubst, Slot.targetSubst] using
      Realizes.targetSubst (environment.valid index) substitution typed

/-- Extend pointwise validity with one exact value already present in the
current target context.  Both the new head and every older witness are frozen
through the literal source weakening; no path is rerun. -/
noncomputable def extendAtInterface
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : ValidEnv sourceContext base)
    (sourceType : LambdaPFC.Ty n) {shape : Shape sig}
    (interface : Shape.Interface base shape)
    (rep : Rep base sourceType shape)
    (realizes : Realizes environment.raw rep (.value interface)) :
    ValidEnv (sourceContext.snoc sourceType) base where
  raw := LambdaPToFCo.Direct.Internal.extendAtInterface environment.raw
    sourceType interface rep
  valid index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa only [LambdaPFC.Ctx.lookup,
        LambdaPToFCo.Direct.Internal.extendAtInterface_here] using
        Realizes.sourceExtendHead sourceType interface rep realizes
    · simpa only [LambdaPFC.Ctx.lookup,
        LambdaPToFCo.Direct.Internal.extendAtInterface_there,
        Slot.sourceRename] using
        Realizes.sourceExtendAligned (environment.valid older) sourceType
          interface rep

end ValidEnv

end LambdaPToFCo.Direct.Internal.Realization
