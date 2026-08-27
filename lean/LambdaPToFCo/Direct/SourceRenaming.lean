import LambdaPFC.Typing

/-!
# Source typing renaming

The direct compiler extends source contexts while retaining actions for older
slots. This module supplies the minimal source metatheory required for that
lexical transport: context-preserving renaming for precise paths and literal
subtyping, plus its one-binder weakening specialization.
-/

namespace LambdaPFC

/-- A source-variable renaming that preserves the types synthesized by
context lookup. -/
abbrev ContextRenaming (source : Ctx n) (mapping : FinFun n m)
    (target : Ctx m) : Prop :=
  (index : Fin n) ->
    target.lookup (mapping index) = (source.lookup index).rename mapping

namespace ContextRenaming

theorem id (context : Ctx n) :
    ContextRenaming context FinFun.id context := by
  intro index
  simp only [FinFun.id_apply, Ty.rename_id]

theorem comp
    (first : ContextRenaming source firstMapping middle)
    (second : ContextRenaming middle secondMapping target) :
    ContextRenaming source (firstMapping.comp secondMapping) target := by
  intro index
  simp only [FinFun.comp_apply]
  rw [second (firstMapping index), first index]
  simp only [Ty.rename_rename]

theorem ext
    (rho : ContextRenaming source mapping target) :
    ContextRenaming (source.snoc bound)
      mapping.ext (target.snoc (bound.rename mapping)) := by
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · change (bound.rename mapping).weaken =
      bound.weaken.rename mapping.ext
    exact Ty.weaken_rename bound mapping
  · change (target.lookup (mapping older)).weaken =
      (source.lookup older).weaken.rename mapping.ext
    rw [rho older]
    exact Ty.weaken_rename (source.lookup older) mapping

theorem weaken :
    ContextRenaming context FinFun.weaken (context.snoc bound) := by
  intro index
  change (context.lookup index).weaken =
    (context.lookup index).rename FinFun.weaken
  rfl

end ContextRenaming

/-- Precise path typing is stable under a context-preserving renaming. -/
noncomputable def Path.Ty.sourceRename {context : Ctx n} {path : Path n}
    {type : Tau n kind} (typing : Path.Ty context path type) :
    forall {m} {mapping : FinFun n m} {target : Ctx m},
      ContextRenaming context mapping target ->
        Path.Ty target (path.rename mapping) (type.rename mapping) := by
  induction typing with
  | @var gamma index =>
      intro m mapping target rho
      simpa only [Path.rename, Tau.rename, rho index] using
        (Path.Ty.var (Γ := target) (x := mapping index))
  | fst receiver ih =>
      intro m mapping target rho
      simpa [Path.rename, Ty.rename, Tau.rename] using
        Path.Ty.fst (ih rho)
  | sel_r receiver ih =>
      intro m mapping target rho
      simpa [Path.rename, Ty.rename, Tau.rename, Tau.open_rename] using
        Path.Ty.sel_r (ih rho)
  | sel_l receiver member distinct ihReceiver ihMember =>
      intro m mapping target rho
      simpa [Path.rename, Ty.rename, Tau.rename] using
        Path.Ty.sel_l (ihReceiver rho) (ihMember rho) distinct

/-- Source subtyping is stable under a context-preserving renaming. -/
noncomputable def Tau.Sub.sourceRename {context : Ctx n}
    {source target : Tau n kind}
    (subtyping : Tau.Sub context source target) :
    forall {m} {mapping : FinFun n m} {targetContext : Ctx m},
      ContextRenaming context mapping targetContext ->
        Tau.Sub targetContext (source.rename mapping)
          (target.rename mapping) := by
  induction subtyping with
  | refl =>
      intro m mapping targetContext rho
      exact .refl
  | trans first second ihFirst ihSecond =>
      intro m mapping targetContext rho
      exact .trans (ihFirst rho) (ihSecond rho)
  | bot =>
      intro m mapping targetContext rho
      simp only [Tau.rename, Ty.rename]
      exact .bot
  | top =>
      intro m mapping targetContext rho
      simp only [Tau.rename, Ty.rename]
      exact .top
  | widen typing =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.widen (typing.sourceRename rho)
  | symm typing =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.symm (typing.sourceRename rho)
  | sel_hi typing nonempty ihNonempty =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.sel_hi (typing.sourceRename rho) (ihNonempty rho)
  | sel_lo typing nonempty ihNonempty =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.sel_lo (typing.sourceRename rho) (ihNonempty rho)
  | «fun» domain codomain ihDomain ihCodomain =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename] using
        Tau.Sub.fun (ihDomain rho)
          (ihCodomain (ContextRenaming.ext rho))
  | pair first member ihFirst ihMember =>
      intro m mapping targetContext rho
      simpa [Tau.rename, Ty.rename] using
        Tau.Sub.pair (ihFirst rho)
          (ihMember (ContextRenaming.ext rho))
  | bounds lower upper nonempty ihLower ihUpper ihNonempty =>
      intro m mapping targetContext rho
      simpa [Tau.rename] using
        Tau.Sub.bounds (ihLower rho) (ihUpper rho)
          (ihNonempty rho)

/-- Weakening below one new source binder. -/
noncomputable def Tau.Sub.weaken
    (subtyping : Tau.Sub context source target) :
    Tau.Sub (context.snoc bound) source.weaken target.weaken := by
  simpa [Tau.weaken] using
    subtyping.sourceRename (ContextRenaming.weaken (bound := bound))

end LambdaPFC
