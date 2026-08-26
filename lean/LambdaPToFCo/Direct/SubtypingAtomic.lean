import LambdaPToFCo.Direct.SubtypingScope
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
# Partial derivation-directed atomic subtyping

This is the compact polarity kernel used before the total `Tau.Sub`
dispatcher is available.  `Push` starts from the exact source formation;
`Pull` starts from the exact target formation.  Reflexivity reuses that
known formation, Top is therefore a Push rule, and Bottom is a Pull rule.
Transitivity feeds the exact intermediate formation chosen by one recursive
leg directly into the next; there is no independently synthesized shape or
comparison witness.

The two polarity runners are intentionally restricted to one source context.
Endpoint-divergent pair and function members instead use the sealed
`SubtypingScope.Scope`.  The contextual singleton-variable constructor below
is the first such atom and consumes that alignment directly.

Selected upper/lower rules run only after `Formation.expose` receives a real
interface.  This faithfully handles closed carriers without pretending that
a formation alone can reopen or populate one.  Widening, singleton symmetry,
structural function/pair rules, and a total derivation dispatcher remain
outside this leaf until their formed-path/member compilers are available.
All generated programs are ordinary System FCo terms.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingAtomic

open SystemFCo
open Representation
open Formation
open SubtypingScope

/-! ## Exact cuts and the two root polarities -/

namespace CutView

noncomputable def trans
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstDerivation : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty sourceType) (.ty middleType)}
    {secondDerivation : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty middleType) (.ty targetType)}
    {scope : Scope sourceContext targetContext side base}
    {source middle target : Shape sig}
    (first : CutView scope firstDerivation source middle)
    (second : CutView scope secondDerivation middle target) :
    CutView scope (.trans firstDerivation secondDerivation) source target :=
  CutView.ofRelation first.sourceFormation second.targetFormation
    (first.relation.trans second.relation)

end CutView

abbrev PushConsumer
    {n : Nat} {root : Sig} {context : LambdaPFC.Ctx n}
    {rootContext : Ctx root}
    (scope : Scope context context .source rootContext)
    (answer : Ty root)
    {sourceType targetType : LambdaPFC.Ty n}
    (derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType))
    (source : Shape root) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    (typed : Rename.Typed rootContext currentContext mapping) ->
    {target : Shape current} ->
    CutView (scope.targetRename mapping typed) derivation
      (source.rename mapping) target ->
    Path.Body currentContext (answer.rename mapping)

abbrev PullConsumer
    {n : Nat} {root : Sig} {context : LambdaPFC.Ctx n}
    {rootContext : Ctx root}
    (scope : Scope context context .source rootContext)
    (answer : Ty root)
    {sourceType targetType : LambdaPFC.Ty n}
    (derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType))
    (target : Shape root) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    (typed : Rename.Typed rootContext currentContext mapping) ->
    {source : Shape current} ->
    CutView (scope.targetRename mapping typed) derivation
      source (target.rename mapping) ->
    Path.Body currentContext (answer.rename mapping)

/-- Synthesize the target endpoint from one exact source formation. -/
structure Push
    {context : LambdaPFC.Ctx n}
    {sourceType targetType : LambdaPFC.Ty n}
    (derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType)) : Type where
  run : {sig : Sig} -> {base : Ctx sig} ->
    (scope : Scope context context .source base) ->
    {source : Shape sig} ->
    Formation context base sourceType source ->
    (answer : Ty sig) ->
    PushConsumer scope answer derivation source ->
    Path.Body base answer

/-- Synthesize the source endpoint from one exact target formation. -/
structure Pull
    {context : LambdaPFC.Ctx n}
    {sourceType targetType : LambdaPFC.Ty n}
    (derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType)) : Type where
  run : {sig : Sig} -> {base : Ctx sig} ->
    (scope : Scope context context .source base) ->
    {target : Shape sig} ->
    Formation context base targetType target ->
    (answer : Ty sig) ->
    PullConsumer scope answer derivation target ->
    Path.Body base answer

private noncomputable def pushHere
    {context : LambdaPFC.Ctx n}
    {sourceType targetType : LambdaPFC.Ty n}
    {derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType)}
    {base : Ctx sig} {source target : Shape sig}
    {scope : Scope context context .source base}
    (cut : CutView scope derivation source target)
    (answer : Ty sig)
    (consumer : PushConsumer scope answer derivation source) :
    Path.Body base answer := by
  have cutAt := cut.targetRename Rename.id (TypedRename.id base)
  simpa only [Shape.rename_id, Ty.rename_id] using
    consumer Rename.id (TypedRename.id base) cutAt

private noncomputable def pullHere
    {context : LambdaPFC.Ctx n}
    {sourceType targetType : LambdaPFC.Ty n}
    {derivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty targetType)}
    {base : Ctx sig} {source target : Shape sig}
    {scope : Scope context context .source base}
    (cut : CutView scope derivation source target)
    (answer : Ty sig)
    (consumer : PullConsumer scope answer derivation target) :
    Path.Body base answer := by
  have cutAt := cut.targetRename Rename.id (TypedRename.id base)
  simpa only [Shape.rename_id, Ty.rename_id] using
    consumer Rename.id (TypedRename.id base) cutAt

/-! ## Reflexivity, Top, and Bottom -/

private noncomputable def reflAt
    {context : LambdaPFC.Ctx n}
    {sourceType : LambdaPFC.Ty n}
    {base : Ctx sig} {shape : Shape sig}
    {scope : Scope context context .source base}
    (formation : Formation context base sourceType shape) :
    CutView scope (LambdaPFC.Tau.Sub.refl (Γ := context)
      (τ := .ty sourceType)) shape shape :=
  CutView.ofRelation formation formation (Relation.refl formation.rep)

private noncomputable def topFrom
    {context : LambdaPFC.Ctx n}
    {sourceType : LambdaPFC.Ty n}
    {base : Ctx sig} {source : Shape sig}
    {scope : Scope context context .source base}
    (sourceFormation : Formation context base sourceType source) :
    CutView scope (LambdaPFC.Tau.Sub.top (Γ := context)
      (T := sourceType)) source (.stable (Top.plan sig)) :=
  CutView.ofRelation sourceFormation .top
    (AtomicSubtyping.top {
      shape := source
      rep := sourceFormation.rep }).relation

private noncomputable def bottomTo
    {context : LambdaPFC.Ctx n}
    {targetType : LambdaPFC.Ty n}
    {base : Ctx sig} {target : Shape sig}
    {scope : Scope context context .source base}
    (targetFormation : Formation context base targetType target) :
    CutView scope (LambdaPFC.Tau.Sub.bot (Γ := context)
      (T := targetType)) (.stable (Bot.plan sig)) target :=
  CutView.ofRelation .bottom targetFormation
    (AtomicSubtyping.bot {
      shape := target
      rep := targetFormation.rep }).relation

noncomputable def pushRefl
    {context : LambdaPFC.Ctx n} {sourceType : LambdaPFC.Ty n} :
    Push (LambdaPFC.Tau.Sub.refl (Γ := context)
      (τ := .ty sourceType)) where
  run _scope _source sourceFormation answer consumer :=
    pushHere (reflAt sourceFormation) answer consumer

noncomputable def pullRefl
    {context : LambdaPFC.Ctx n} {sourceType : LambdaPFC.Ty n} :
    Pull (LambdaPFC.Tau.Sub.refl (Γ := context)
      (τ := .ty sourceType)) where
  run _scope _target targetFormation answer consumer :=
    pullHere (reflAt targetFormation) answer consumer

noncomputable def pushTop
    {context : LambdaPFC.Ctx n} {sourceType : LambdaPFC.Ty n} :
    Push (LambdaPFC.Tau.Sub.top (Γ := context)
      (T := sourceType)) where
  run _scope _source sourceFormation answer consumer :=
    pushHere (topFrom sourceFormation) answer consumer

noncomputable def pullBottom
    {context : LambdaPFC.Ctx n} {targetType : LambdaPFC.Ty n} :
    Pull (LambdaPFC.Tau.Sub.bot (Γ := context)
      (T := targetType)) where
  run _scope _target targetFormation answer consumer :=
    pullHere (bottomTo targetFormation) answer consumer

/-! ## Exact-middle transitivity -/

noncomputable def pushTrans
    {context : LambdaPFC.Ctx n}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstDerivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty middleType)}
    {secondDerivation : LambdaPFC.Tau.Sub context
      (.ty middleType) (.ty targetType)}
    (first : Push firstDerivation)
    (second : Push secondDerivation) :
    Push (.trans firstDerivation secondDerivation) where
  run scope _source sourceFormation answer consumer :=
    first.run scope sourceFormation answer
      (fun mapping typed _middle firstCut => by
        let scopeAt := scope.targetRename mapping typed
        let localConsumer : PushConsumer scopeAt (answer.rename mapping)
            secondDerivation _middle :=
          fun next nextTyped _target secondCut => by
            let combined := mapping.comp next
            let combinedTyped := TypedRename.comp typed nextTyped
            let firstAt := firstCut.targetRename next nextTyped
            let composed :=
              SubtypingAtomic.CutView.trans firstAt secondCut
            have combinedCut : CutView
                (scope.targetRename combined combinedTyped)
                (.trans firstDerivation secondDerivation)
                (_source.rename combined) _target := by
              simpa only [Shape.rename_comp] using
                CutView.ofRelation composed.sourceFormation
                  composed.targetFormation composed.relation
            have body := consumer combined combinedTyped combinedCut
            simpa only [Ty.rename_comp] using body
        exact second.run scopeAt firstCut.targetFormation
          (answer.rename mapping) localConsumer)

noncomputable def pullTrans
    {context : LambdaPFC.Ctx n}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstDerivation : LambdaPFC.Tau.Sub context
      (.ty sourceType) (.ty middleType)}
    {secondDerivation : LambdaPFC.Tau.Sub context
      (.ty middleType) (.ty targetType)}
    (first : Pull firstDerivation)
    (second : Pull secondDerivation) :
    Pull (.trans firstDerivation secondDerivation) where
  run scope _target targetFormation answer consumer :=
    second.run scope targetFormation answer
      (fun mapping typed _middle secondCut => by
        let scopeAt := scope.targetRename mapping typed
        let localConsumer : PullConsumer scopeAt (answer.rename mapping)
            firstDerivation _middle :=
          fun next nextTyped _source firstCut => by
            let combined := mapping.comp next
            let combinedTyped := TypedRename.comp typed nextTyped
            let secondAt := secondCut.targetRename next nextTyped
            let composed :=
              SubtypingAtomic.CutView.trans firstCut secondAt
            have combinedCut : CutView
                (scope.targetRename combined combinedTyped)
                (.trans firstDerivation secondDerivation)
                _source (_target.rename combined) := by
              simpa only [Shape.rename_comp] using
                CutView.ofRelation composed.sourceFormation
                  composed.targetFormation composed.relation
            have body := consumer combined combinedTyped combinedCut
            simpa only [Ty.rename_comp] using body
        exact first.run scopeAt secondCut.sourceFormation
          (answer.rename mapping) localConsumer)

/-! ## Formation-exposed selection atoms -/

private def pathResultHEq :
    {n : Nat} -> {context : LambdaPFC.Ctx n} ->
    {path : LambdaPFC.Path n} ->
    {firstKind secondKind : LambdaPFC.Kind} ->
    {first : LambdaPFC.Tau n firstKind} ->
    {second : LambdaPFC.Tau n secondKind} ->
    LambdaPFC.Path.Ty context path first ->
    LambdaPFC.Path.Ty context path second -> HEq first second
  | _, _, _, _, _, _, _, .var, .var => HEq.rfl
  | _, _, _, _, _, _, _, .fst first, .fst second => by
      have receiver := pathResultHEq first second
      cases receiver
      exact HEq.rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_r second => by
      have receiver := pathResultHEq first second
      cases receiver
      exact HEq.rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_l second _ labelsNe => by
      have receiver := pathResultHEq first second
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l first _ labelsNe, .sel_r second => by
      have receiver := pathResultHEq first second
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l _ first _, .sel_l _ second _ =>
      pathResultHEq first second

private theorem pathResultEq
    {context : LambdaPFC.Ctx n} {path : LambdaPFC.Path n}
    {first second : LambdaPFC.Tau n kind}
    (firstTyping : LambdaPFC.Path.Ty context path first)
    (secondTyping : LambdaPFC.Path.Ty context path second) :
    first = second :=
  eq_of_heq (pathResultHEq firstTyping secondTyping)

abbrev SelHiExposedConsumer
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    (source : Shape sig) (answer : Ty sig) : Type :=
  forall {target : Shape sig},
    CutView scope (.sel_hi typing nonempty) source target ->
    Rep.ExposeBody base answer

noncomputable def pushSelHiExposed
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    {source : Shape sig}
    (formation : Formation.Exposed context base
      (.TSel path label) source)
    (answer : Ty sig)
    (consumer : SelHiExposedConsumer scope typing nonempty source answer) :
    Rep.ExposeBody base answer := by
  cases formation with
  | selection storedTyping lowerFormation upperFormation lowerFunction
      lowerTyping upperFunction upperTyping =>
      have resultTypes := pathResultEq storedTyping typing
      cases resultTypes
      let interval : IntervalRep lowerSource upperSource _ _ _ := {
        lowerRep := lowerFormation.rep
        upperRep := upperFormation.rep
        lowerFunction := lowerFunction
        lowerTyping := lowerTyping
        upperFunction := upperFunction
        upperTyping := upperTyping
      }
      let result := AtomicSubtyping.selHiAt
        (path := path) (label := label) interval
      exact consumer
        (CutView.ofRelation
          (.selection storedTyping lowerFormation upperFormation
            lowerFunction lowerTyping upperFunction upperTyping)
          upperFormation
          result.relation)

abbrev SelLoExposedConsumer
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    (target : Shape sig) (answer : Ty sig) : Type :=
  forall {source : Shape sig},
    CutView scope (.sel_lo typing nonempty) source target ->
    Rep.ExposeBody base answer

noncomputable def pullSelLoExposed
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    {target : Shape sig}
    (formation : Formation.Exposed context base
      (.TSel path label) target)
    (answer : Ty sig)
    (consumer : SelLoExposedConsumer scope typing nonempty target answer) :
    Rep.ExposeBody base answer := by
  cases formation with
  | selection storedTyping lowerFormation upperFormation lowerFunction
      lowerTyping upperFunction upperTyping =>
      have resultTypes := pathResultEq storedTyping typing
      cases resultTypes
      let interval : IntervalRep lowerSource upperSource _ _ _ := {
        lowerRep := lowerFormation.rep
        upperRep := upperFormation.rep
        lowerFunction := lowerFunction
        lowerTyping := lowerTyping
        upperFunction := upperFunction
        upperTyping := upperTyping
      }
      let result := AtomicSubtyping.selLoAt
        (path := path) (label := label) interval
      exact consumer
        (CutView.ofRelation lowerFormation
          (.selection storedTyping lowerFormation upperFormation
            lowerFunction lowerTyping upperFunction upperTyping)
          result.relation)

/-- A selection-upper consumer natural in every carrier scope opened by the
exact source interface. -/
abbrev SelHiConsumer
    {n : Nat} {root : Sig} {context : LambdaPFC.Ctx n}
    {rootContext : Ctx root}
    (scope : Scope context context .source rootContext)
    (answer : Ty root)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource)) : Type :=
  forall {current : Sig} {currentContext : Ctx current}
    {source target : Shape current},
    (mapping : Rename root current) ->
    (typed : Rename.Typed rootContext currentContext mapping) ->
    Shape.Interface currentContext source ->
    CutView (scope.targetRename mapping typed)
      (.sel_hi typing nonempty) source target ->
    Rep.ExposeBody currentContext (answer.rename mapping)

/-- Expose a possibly closed selected source only under its real interface,
then run the literal upper-selection atom in that exact scope. -/
noncomputable def pushSelHiAtInterface
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    {source : Shape sig}
    (interface : Shape.Interface base source)
    (formation : Formation context base (.TSel path label) source)
    (answer : Ty sig)
    (consumer : SelHiConsumer scope answer typing nonempty) :
    Rep.ExposeBody base answer :=
  formation.expose interface answer
    (fun mapping typed exposedInterface exposedFormation =>
      pushSelHiExposed (scope.targetRename mapping typed)
        typing nonempty exposedFormation (answer.rename mapping)
        (fun cut =>
          consumer mapping typed exposedInterface cut))

/-- A selection-lower consumer natural in every carrier scope opened by the
exact target interface. -/
abbrev SelLoConsumer
    {n : Nat} {root : Sig} {context : LambdaPFC.Ctx n}
    {rootContext : Ctx root}
    (scope : Scope context context .source rootContext)
    (answer : Ty root)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource)) : Type :=
  forall {current : Sig} {currentContext : Ctx current}
    {source target : Shape current},
    (mapping : Rename root current) ->
    (typed : Rename.Typed rootContext currentContext mapping) ->
    Shape.Interface currentContext target ->
    CutView (scope.targetRename mapping typed)
      (.sel_lo typing nonempty) source target ->
    Rep.ExposeBody currentContext (answer.rename mapping)

/-- Expose a possibly closed selected target only under its real interface,
then run the literal lower-selection atom in that exact scope. -/
noncomputable def pullSelLoAtInterface
    {context : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (scope : Scope context context .source base)
    (typing : LambdaPFC.Path.Ty context (.sel path label)
      (.intv lowerSource upperSource))
    (nonempty : LambdaPFC.Tau.Sub context
      (.ty lowerSource) (.ty upperSource))
    {target : Shape sig}
    (interface : Shape.Interface base target)
    (formation : Formation context base (.TSel path label) target)
    (answer : Ty sig)
    (consumer : SelLoConsumer scope answer typing nonempty) :
    Rep.ExposeBody base answer :=
  formation.expose interface answer
    (fun mapping typed exposedInterface exposedFormation =>
      pullSelLoExposed (scope.targetRename mapping typed)
        typing nonempty exposedFormation (answer.rename mapping)
        (fun cut =>
          consumer mapping typed exposedInterface cut))

/-! ## Contextual singleton reflexivity -/

noncomputable def reflSingletonVariable
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) :
    CutView scope
      (LambdaPFC.Tau.Sub.refl
        (Γ := side.choose sourceContext targetContext)
        (τ := .ty (.Single (.var index))))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy))
      (.stable (Single.plan
        (scope.target.lookup index).shape.inputTy)) :=
  CutView.ofRelation
    (.singleton .var (scope.source.lookup index).interface
      (scope.source.lookup index).formation)
    (.singleton .var (scope.target.lookup index).interface
      (scope.target.lookup index).formation)
    (scope.reflSingletonVariable index)

end LambdaPToFCo.Direct.Internal.SubtypingAtomic
