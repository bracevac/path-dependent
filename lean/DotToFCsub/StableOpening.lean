import DotToFCsub.StableTranslation
import DotToFCsub.Elaboration
import DotToFCsub.LayoutMetatheory

/-!
# Stable dependent type opening

Source dependent application opens a codomain with an existing stable path.
For a plain parameter the generated target term binder is absent from types.
For a member parameter, opening substitutes the canonical abstract name of
the argument and discards the member telescope evidence and runtime payload.

This module records that correspondence entirely at the syntax level.  It
does not call either the source or target checker.
-/

namespace DotToFCsub.StableOpening

open DotFC
open DotFC.Source
open FCsub

private abbrev TargetSig {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) : FCsub.Sig :=
  Layout.sig (DotFC.Explicit.Ctx.ofSource context)

/-- A source-context opening together with the FCsub substitution induced by
the layout.  The lift constructors are the cases needed while descending
through nested dependent types. -/
inductive ContextOpening :
    {source target : DotFC.Sig} →
    (before : DotFC.Source.Ctx source) →
    (after : DotFC.Source.Ctx target) →
    DotFC.Rename source target →
    FCsub.Subst (TargetSig before) (TargetSig after) → Type where
  | top {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      (argument : DotFC.BVar source .term) :
      ContextOpening (context.snoc .top) context
        (DotFC.Source.Rename.openAt argument)
        (FCsub.Subst.id.instantiateTerm
          (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context)
            argument)))
  | bot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      (argument : DotFC.BVar source .term) :
      ContextOpening (context.snoc .bot) context
        (DotFC.Source.Rename.openAt argument)
        (FCsub.Subst.id.instantiateTerm
          (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context)
            argument)))
  | all {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      (domain : DotFC.Source.Ty source)
      (codomain : DotFC.Source.Ty (source ▹ .term))
      (argument : DotFC.BVar source .term) :
      ContextOpening (context.snoc (.all domain codomain)) context
        (DotFC.Source.Rename.openAt argument)
        (FCsub.Subst.id.instantiateTerm
          (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context)
            argument)))
  | selection {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      (path : DotFC.BVar source .term) (label : DotFC.Source.Name)
      (argument : DotFC.BVar source .term) :
      ContextOpening (context.snoc (.sel path label)) context
        (DotFC.Source.Rename.openAt argument)
        (FCsub.Subst.id.instantiateTerm
          (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context)
            argument)))
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} (lower upper : DotFC.Source.Ty source)
      (argument : DotFC.BVar source .term)
      (argumentRoot : StableFragment.StableRoot context argument label)
      (use : Elaboration.MemberUse (TargetSig context))
      (slotLookup : Layout.fullSlot?
        (DotFC.Explicit.Ctx.ofSource context) argument label = some use.slot) :
      ContextOpening (context.snoc (.member label lower upper)) context
        (DotFC.Source.Rename.openAt argument)
        ((FCsub.Subst.fromStaticArgs FCsub.Subst.id
          (MemberEncoding.witnessArgs (.tvar use.slot.name))
          (MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence)).instantiateTerm
            (.var use.slot.payload))
  | liftTop {source target : DotFC.Sig}
      {before : DotFC.Source.Ctx source}
      {after : DotFC.Source.Ctx target} {rho : DotFC.Rename source target}
      {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
      (opening : ContextOpening before after rho substitution) :
      ContextOpening (before.snoc .top) (after.snoc .top)
        rho.lift substitution.liftTerm
  | liftBot {source target : DotFC.Sig}
      {before : DotFC.Source.Ctx source}
      {after : DotFC.Source.Ctx target} {rho : DotFC.Rename source target}
      {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
      (opening : ContextOpening before after rho substitution) :
      ContextOpening (before.snoc .bot) (after.snoc .bot)
        rho.lift substitution.liftTerm
  | liftAll {source target : DotFC.Sig}
      {before : DotFC.Source.Ctx source}
      {after : DotFC.Source.Ctx target} {rho : DotFC.Rename source target}
      {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
      (domain : DotFC.Source.Ty source)
      (codomain : DotFC.Source.Ty (source ▹ .term))
      (opening : ContextOpening before after rho substitution) :
      ContextOpening (before.snoc (.all domain codomain))
        (after.snoc (DotFC.Source.Ty.all (domain.rename rho)
          (codomain.rename rho.lift)))
        rho.lift substitution.liftTerm
  | liftSelection {source target : DotFC.Sig}
      {before : DotFC.Source.Ctx source}
      {after : DotFC.Source.Ctx target} {rho : DotFC.Rename source target}
      {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
      (path : DotFC.BVar source .term) (label : DotFC.Source.Name)
      (opening : ContextOpening before after rho substitution) :
      ContextOpening (before.snoc (.sel path label))
        (after.snoc (DotFC.Source.Ty.sel (rho.var path) label))
        rho.lift substitution.liftTerm
  | liftMember {source target : DotFC.Sig}
      {before : DotFC.Source.Ctx source}
      {after : DotFC.Source.Ctx target} {rho : DotFC.Rename source target}
      {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
      (label : DotFC.Source.Name) (lower upper : DotFC.Source.Ty source)
      (opening : ContextOpening before after rho substitution) :
      ContextOpening (before.snoc (.member label lower upper))
        (after.snoc (DotFC.Source.Ty.member label
          (lower.rename rho) (upper.rename rho)))
        rho.lift (substitution.liftPayload
          MemberEncoding.names MemberEncoding.constraints)

namespace ContextOpening

private theorem map_bind₃ {A B C D A' B' C' D' : Type}
    (first : Option A) (second : Option B) (third : Option C)
    (first' : Option A') (second' : Option B') (third' : Option C')
    (firstMap : A → A') (secondMap : B → B') (thirdMap : C → C')
    (resultMap : D → D') (combine : A → B → C → D)
    (combine' : A' → B' → C' → D')
    (firstNatural : Option.map firstMap first = first')
    (secondNatural : Option.map secondMap second = second')
    (thirdNatural : Option.map thirdMap third = third')
    (combineNatural : ∀ firstValue secondValue thirdValue,
      resultMap (combine firstValue secondValue thirdValue) =
        combine' (firstMap firstValue) (secondMap secondValue)
          (thirdMap thirdValue)) :
    Option.map resultMap
        (first.bind fun firstValue =>
          second.bind fun secondValue =>
            third.bind fun thirdValue =>
              some (combine firstValue secondValue thirdValue)) =
      first'.bind fun firstValue =>
        second'.bind fun secondValue =>
          third'.bind fun thirdValue =>
            some (combine' firstValue secondValue thirdValue) := by
  cases first <;>
    cases second <;>
      cases third <;>
        subst first' <;>
          subst second' <;>
            subst third' <;>
              simp_all

private def previousRoot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableFragment.StableRoot (context.snoc bound)
      (.there path) label) :
    StableFragment.StableRoot context path label := by
  rcases root with ⟨lower, upper, lookup⟩
  generalize typeEq : (DotFC.Source.Ty.member label lower upper) = type at lookup
  cases lookup with
  | @there _ _ _ olderType _ older =>
      cases olderType with
      | top => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | bot => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | all domain codomain =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | sel selected selectedLabel =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | member olderLabel olderLower olderUpper =>
          simp only [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
          injection typeEq with labelEq lowerEq upperEq
          subst olderLabel
          exact ⟨olderLower, olderUpper, older⟩

private def weakenRoot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name} (bound : DotFC.Source.Ty source)
    (root : StableFragment.StableRoot context path label) :
    StableFragment.StableRoot (context.snoc bound) (.there path) label :=
  ⟨root.lower.weaken, root.upper.weaken, .there root.lookup⟩

private theorem noPlainHere {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    (plain : ∀ label lower upper,
      bound ≠ DotFC.Source.Ty.member label lower upper)
    {label : DotFC.Source.Name}
    (root : StableFragment.StableRoot (context.snoc bound)
      (.here : DotFC.BVar (source ▹ .term) .term) label) : False := by
  have equality := DotFC.Source.Lookup.functional root.lookup
    (DotFC.Source.Lookup.newest (context := context) (type := bound))
  cases bound with
  | top => cases equality
  | bot => cases equality
  | all domain codomain => cases equality
  | sel path selectedLabel => cases equality
  | member boundLabel lower upper => exact plain boundLabel lower upper rfl

private theorem memberHereLabel {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {boundLabel label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (root : StableFragment.StableRoot
      (context.snoc (.member boundLabel lower upper))
      (.here : DotFC.BVar (source ▹ .term) .term) label) :
    label = boundLabel := by
  have equality := DotFC.Source.Lookup.functional root.lookup
    (DotFC.Source.Lookup.newest (context := context)
      (type := DotFC.Source.Ty.member boundLabel lower upper))
  simp only [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at equality
  injection equality

private theorem substitute_weakenPayload {source target : FCsub.Sig}
    (type : FCsub.Ty source) (substitution : FCsub.Subst source target) :
    (type.rename (FCsub.Rename.weakenPayload
        MemberEncoding.names MemberEncoding.constraints)).substitute
        (substitution.liftPayload
          MemberEncoding.names MemberEncoding.constraints) =
      (type.substitute substitution).rename
        (FCsub.Rename.weakenPayload
          MemberEncoding.names MemberEncoding.constraints) := by
  unfold FCsub.Rename.weakenPayload FCsub.Subst.liftPayload
  rw [← FCsub.Ty.rename_comp]
  change ((type.rename (FCsub.Rename.weakenStatic
      MemberEncoding.names MemberEncoding.constraints)).weaken).substitute
    (substitution.liftStatic
      MemberEncoding.names MemberEncoding.constraints).liftTerm = _
  rw [FCsub.Ty.substitute_weakenTerm,
    FCsub.Ty.substitute_weakenStatic]
  exact FCsub.Ty.rename_comp _ _ _

private theorem liftTerm_slotName {source target : FCsub.Sig}
    (substitution : FCsub.Subst source target)
    {sourceName : FCsub.BVar source .type}
    {targetName : FCsub.BVar target .type}
    (nameEq : substitution.typeVar sourceName = .tvar targetName) :
    substitution.liftTerm.typeVar
        ((FCsub.Rename.succ (kind := .term)).var sourceName) =
      .tvar ((FCsub.Rename.succ (kind := .term)).var targetName) := by
  simpa only [FCsub.Ty.substitute, FCsub.Ty.weaken,
    FCsub.Ty.rename] using
    (FCsub.Ty.substitute_weakenTerm (.tvar sourceName) substitution).trans
      (congrArg (fun type => type.weaken (kind := .term)) nameEq)

private theorem liftPayload_slotName {source target : FCsub.Sig}
    (substitution : FCsub.Subst source target)
    {sourceName : FCsub.BVar source .type}
    {targetName : FCsub.BVar target .type}
    (nameEq : substitution.typeVar sourceName = .tvar targetName) :
    (substitution.liftPayload
        MemberEncoding.names MemberEncoding.constraints).typeVar
        (MemberEncoding.weakenPayload.var sourceName) =
      .tvar (MemberEncoding.weakenPayload.var targetName) := by
  simpa only [FCsub.Ty.substitute, FCsub.Ty.rename] using
    (substitute_weakenPayload (.tvar sourceName) substitution).trans
      (congrArg (fun type => type.rename MemberEncoding.weakenPayload) nameEq)

private theorem existsType_substitute {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source)
    (substitution : FCsub.Subst source target) :
    (MemberEncoding.existsType lower upper).substitute substitution =
      MemberEncoding.existsType (lower.substitute substitution)
        (upper.substitute substitution) := by
  have lowerWeak :
      (lower.rename FCsub.Rename.succ).substitute substitution.liftType =
        (lower.substitute substitution).rename FCsub.Rename.succ :=
    FCsub.Ty.substitute_weakenType lower substitution
  have upperWeak :
      (upper.rename FCsub.Rename.succ).substitute substitution.liftType =
        (upper.substitute substitution).rename FCsub.Rename.succ :=
    FCsub.Ty.substitute_weakenType upper substitution
  have nameFixed : substitution.liftType.typeVar
      (.here : FCsub.BVar (source ▹ .type) .type) = .tvar .here := rfl
  simp [MemberEncoding.existsType, MemberEncoding.telescope,
    FCsub.Ty.substitute, FCsub.Telescope.substitute,
    FCsub.Proposition.substitute, FCsub.Rename.weakenTypes,
    FCsub.Subst.liftTypes, FCsub.Rename.weakenN, FCsub.Subst.liftN,
    FCsub.Subst.lift, MemberEncoding.nameInTypes,
    lowerWeak, upperWeak, nameFixed]

private theorem forallType_substitute {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source)
    (result : FCsub.Ty (MemberEncoding.Payload source))
    (substitution : FCsub.Subst source target) :
    (MemberEncoding.forallType lower upper result).substitute substitution =
      MemberEncoding.forallType (lower.substitute substitution)
        (upper.substitute substitution)
        (result.substitute (substitution.liftPayload
          MemberEncoding.names MemberEncoding.constraints)) := by
  have lowerWeak :
      (lower.rename FCsub.Rename.succ).substitute substitution.liftType =
        (lower.substitute substitution).rename FCsub.Rename.succ :=
    FCsub.Ty.substitute_weakenType lower substitution
  have upperWeak :
      (upper.rename FCsub.Rename.succ).substitute substitution.liftType =
        (upper.substitute substitution).rename FCsub.Rename.succ :=
    FCsub.Ty.substitute_weakenType upper substitution
  have nameFixed : substitution.liftType.typeVar
      (.here : FCsub.BVar (source ▹ .type) .type) = .tvar .here := rfl
  simp [MemberEncoding.forallType, MemberEncoding.telescope,
    FCsub.Ty.substitute, FCsub.Telescope.substitute,
    FCsub.Proposition.substitute, FCsub.Rename.weakenTypes,
    FCsub.Subst.liftTypes, FCsub.Subst.liftPayload,
    FCsub.Rename.weakenN, FCsub.Subst.liftN,
    FCsub.Subst.lift, MemberEncoding.nameInTypes,
    lowerWeak, upperWeak, nameFixed]
  rfl

/-- Stable roots are preserved by a layout opening.  In the member base case
the newest source root is redirected to the stable root of the argument. -/
noncomputable def transportRoot {source target : DotFC.Sig}
    {before : DotFC.Source.Ctx source} {after : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
    (opening : ContextOpening before after rho substitution)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableFragment.StableRoot before path label) :
    StableFragment.StableRoot after (rho.var path) label := by
  induction opening with
  | top argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact previousRoot root
  | bot argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact previousRoot root
  | all domain codomain argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact previousRoot root
  | selection selected selectedLabel argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact previousRoot root
  | member lower upper argument argumentRoot use slotLookup =>
      cases path with
      | here =>
          have labelEq := memberHereLabel root
          subst label
          exact argumentRoot
      | there older => exact previousRoot root
  | liftTop opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact weakenRoot .top (induction (previousRoot root))
  | liftBot opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older => exact weakenRoot .bot (induction (previousRoot root))
  | liftAll domain codomain opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          exact weakenRoot _ (induction (previousRoot root))
  | liftSelection selected selectedLabel opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          exact weakenRoot _ (induction (previousRoot root))
  | liftMember boundLabel lower upper opening induction =>
      cases path with
      | here =>
          have labelEq := memberHereLabel root
          subst label
          exact ⟨(lower.rename _).weaken, (upper.rename _).weaken,
            DotFC.Source.Lookup.newest⟩
      | there older =>
          exact weakenRoot _ (induction (previousRoot root))

/-- The FCsub substitution attached to an opening sends every generated name
owned by a stable source root to the generated name of the opened root. -/
theorem fullSlot_substitute {source target : DotFC.Sig}
    {before : DotFC.Source.Ctx source} {after : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
    (opening : ContextOpening before after rho substitution)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableFragment.StableRoot before path label)
    {slot : Layout.Slot (TargetSig before)}
    (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource before)
      path label = some slot) :
    ∃ openedSlot : Layout.Slot (TargetSig after),
      Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
        (rho.var path) label = some openedSlot ∧
      substitution.typeVar slot.name = .tvar openedSlot.name := by
  induction opening with
  | top argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          exact ⟨olderSlot, olderLookup, rfl⟩
  | bot argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          exact ⟨olderSlot, olderLookup, rfl⟩
  | all domain codomain argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          exact ⟨olderSlot, olderLookup, rfl⟩
  | selection selected selectedLabel argument =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          exact ⟨olderSlot, olderLookup, rfl⟩
  | @member _ context label lower upper argument argumentRoot use argumentSlot =>
      cases path with
      | here =>
          have labelEq := memberHereLabel root
          subst label
          have canonicalLookup : Layout.fullSlot?
              (DotFC.Explicit.Ctx.ofSource
                (context.snoc (.member label lower upper))) .here label =
              some ⟨MemberEncoding.name, MemberEncoding.lower,
                MemberEncoding.upper, MemberEncoding.payload⟩ := by
            change Layout.fullSlot?
              ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                (.member label lower upper)) .here label = _
            exact Layout.fullSlot_here_member
              (DotFC.Explicit.Ctx.ofSource context) label lower upper
          have slotEq := Layout.FullSlotAt.functional slotLookup canonicalLookup
          subst slot
          exact ⟨use.slot, argumentSlot, rfl⟩
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          exact ⟨olderSlot, olderLookup, rfl⟩
  | @liftTop _ _ before after rho substitution opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
            induction (previousRoot root) olderLookup
          refine ⟨openedSlot.rename FCsub.Rename.succ, ?_, ?_⟩
          · change Option.map (fun found => found.rename FCsub.Rename.succ)
              (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
                (rho.var older) label) = _
            rw [openedLookup]
            rfl
          · simpa only [Layout.Slot.rename, Layout.extendRename] using
              liftTerm_slotName substitution nameEq
  | @liftBot _ _ before after rho substitution opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
            induction (previousRoot root) olderLookup
          refine ⟨openedSlot.rename FCsub.Rename.succ, ?_, ?_⟩
          · change Option.map (fun found => found.rename FCsub.Rename.succ)
              (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
                (rho.var older) label) = _
            rw [openedLookup]
            rfl
          · simpa only [Layout.Slot.rename, Layout.extendRename] using
              liftTerm_slotName substitution nameEq
  | @liftAll _ _ before after rho substitution domain codomain opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
            induction (previousRoot root) olderLookup
          refine ⟨openedSlot.rename FCsub.Rename.succ, ?_, ?_⟩
          · change Option.map (fun found => found.rename FCsub.Rename.succ)
              (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
                (rho.var older) label) = _
            rw [openedLookup]
            rfl
          · simpa only [Layout.Slot.rename, Layout.extendRename] using
              liftTerm_slotName substitution nameEq
  | @liftSelection _ _ before after rho substitution selected selectedLabel opening induction =>
      cases path with
      | here => exact False.elim (noPlainHere (fun _ _ _ => by intro impossible; cases impossible) root)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
            induction (previousRoot root) olderLookup
          refine ⟨openedSlot.rename FCsub.Rename.succ, ?_, ?_⟩
          · change Option.map (fun found => found.rename FCsub.Rename.succ)
              (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
                (rho.var older) label) = _
            rw [openedLookup]
            rfl
          · simpa only [Layout.Slot.rename, Layout.extendRename] using
              liftTerm_slotName substitution nameEq
  | @liftMember _ _ before after rho substitution boundLabel lower upper opening induction =>
      cases path with
      | here =>
          have labelEq := memberHereLabel root
          subst label
          have canonicalLookup : Layout.fullSlot?
              (DotFC.Explicit.Ctx.ofSource
                (before.snoc (.member boundLabel lower upper))) .here
                boundLabel =
              some ⟨MemberEncoding.name, MemberEncoding.lower,
                MemberEncoding.upper, MemberEncoding.payload⟩ := by
            change Layout.fullSlot?
              ((DotFC.Explicit.Ctx.ofSource before).extendTerm
                (.member boundLabel lower upper)) .here boundLabel = _
            exact Layout.fullSlot_here_member
              (DotFC.Explicit.Ctx.ofSource before) boundLabel lower upper
          have slotEq := Layout.FullSlotAt.functional slotLookup canonicalLookup
          subst slot
          refine ⟨⟨MemberEncoding.name, MemberEncoding.lower,
            MemberEncoding.upper, MemberEncoding.payload⟩, ?_, rfl⟩
          change Layout.fullSlot?
            ((DotFC.Explicit.Ctx.ofSource after).extendTerm
              (.member boundLabel (lower.rename rho) (upper.rename rho)))
              .here boundLabel = _
          exact Layout.fullSlot_here_member
            (DotFC.Explicit.Ctx.ofSource after) boundLabel
            (lower.rename rho) (upper.rename rho)
      | there older =>
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] at slotLookup
          obtain ⟨olderSlot, olderLookup, renamed⟩ :=
            Option.map_eq_some_iff.mp slotLookup
          subst slot
          obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
            induction (previousRoot root) olderLookup
          refine ⟨openedSlot.rename MemberEncoding.weakenPayload, ?_, ?_⟩
          · change Option.map
              (fun found => found.rename MemberEncoding.weakenPayload)
              (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource after)
                (rho.var older) label) = _
            rw [openedLookup]
            rfl
          · simpa only [Layout.Slot.rename, Layout.extendRename] using
              liftPayload_slotName substitution nameEq

set_option maxHeartbeats 1000000 in
/-- Stable translation commutes with every context opening recorded above. -/
theorem translateTy_substitute {source target : DotFC.Sig}
    {before : DotFC.Source.Ctx source} {after : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    {substitution : FCsub.Subst (TargetSig before) (TargetSig after)}
    (opening : ContextOpening before after rho substitution)
    {valid : before.Valid} {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf before type}
    (stable : StableFragment.StableWf valid formation) :
    Option.map (fun translated => translated.substitute substitution)
        (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource before) type) =
      Layout.translateTy? (DotFC.Explicit.Ctx.ofSource after)
        (type.rename rho) :=
  match stable with
  | .top => by rfl
  | .bot => by rfl
  | .member lowerStable upperStable => by
      have lowerNatural := translateTy_substitute opening lowerStable
      have upperNatural := translateTy_substitute opening upperStable
      simpa only [DotFC.Source.Ty.rename, Layout.translateTy?] using
        Option.map_bind₂
          (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource before) _)
          (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource before) _)
          (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource after) _)
          (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource after) _)
          (fun type => type.substitute substitution)
          (fun type => type.substitute substitution)
          (fun type => type.substitute substitution)
          MemberEncoding.existsType MemberEncoding.existsType
          lowerNatural upperNatural
          (fun lower upper => existsType_substitute lower upper substitution)
  | .sel stableHandle => by
      obtain ⟨slot, slotLookup⟩ := stableHandle.root.fullSlot_exists
      obtain ⟨openedSlot, openedLookup, nameEq⟩ :=
        fullSlot_substitute opening stableHandle.root slotLookup
      simp [Layout.translateTy?, Layout.slot?, slotLookup, openedLookup,
        FCsub.Ty.substitute, nameEq]
  | @StableFragment.StableWf.all _ _ _ domain codomain _ _
      domainStable codomainStable => by
      cases domain with
      | top =>
          have codomainNatural :=
            translateTy_substitute (.liftTop opening) codomainStable
          simp only [DotFC.Explicit.Ctx.ofSource_snoc] at codomainNatural
          cases codomainEquation : Layout.translateTy?
              ((DotFC.Explicit.Ctx.ofSource before).extendTerm .top) codomain <;>
            simp [DotFC.Source.Ty.rename, Layout.translateTy?,
              codomainEquation, FCsub.Ty.substitute] at codomainNatural ⊢
          all_goals rw [← codomainNatural]
          all_goals rfl
      | bot =>
          have codomainNatural :=
            translateTy_substitute (.liftBot opening) codomainStable
          simp only [DotFC.Explicit.Ctx.ofSource_snoc] at codomainNatural
          cases codomainEquation : Layout.translateTy?
              ((DotFC.Explicit.Ctx.ofSource before).extendTerm .bot) codomain <;>
            simp [DotFC.Source.Ty.rename, Layout.translateTy?,
              codomainEquation, FCsub.Ty.substitute] at codomainNatural ⊢
          all_goals rw [← codomainNatural]
          all_goals rfl
      | all nestedDomain nestedCodomain =>
          have domainNatural := translateTy_substitute opening domainStable
          have codomainNatural := translateTy_substitute
            (.liftAll nestedDomain nestedCodomain opening) codomainStable
          simpa only [DotFC.Source.Ty.rename, Layout.translateTy?] using
            Option.map_bind₂
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource before) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                (before.snoc (.all nestedDomain nestedCodomain))) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource after) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                (after.snoc (DotFC.Source.Ty.all
                  (nestedDomain.rename rho)
                  (nestedCodomain.rename rho.lift)))) _)
              (fun type => type.substitute substitution)
              (fun type => type.substitute substitution.liftTerm)
              (fun type => type.substitute substitution)
              FCsub.Ty.arr FCsub.Ty.arr domainNatural codomainNatural
              (fun _ _ => rfl)
      | sel selected selectedLabel =>
          have domainNatural := translateTy_substitute opening domainStable
          have codomainNatural := translateTy_substitute
            (.liftSelection selected selectedLabel opening) codomainStable
          simpa only [DotFC.Source.Ty.rename, Layout.translateTy?] using
            Option.map_bind₂
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource before) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                (before.snoc (.sel selected selectedLabel))) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource after) _)
              (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                (after.snoc (DotFC.Source.Ty.sel
                  (rho.var selected) selectedLabel))) _)
              (fun type => type.substitute substitution)
              (fun type => type.substitute substitution.liftTerm)
              (fun type => type.substitute substitution)
              FCsub.Ty.arr FCsub.Ty.arr domainNatural codomainNatural
              (fun _ _ => rfl)
      | member label lower upper =>
          match domainStable with
          | .member lowerStable upperStable =>
              have lowerNatural :=
                translateTy_substitute opening lowerStable
              have upperNatural :=
                translateTy_substitute opening upperStable
              have codomainNatural := translateTy_substitute
                (.liftMember label lower upper opening) codomainStable
              simpa only [DotFC.Source.Ty.rename, Layout.translateTy?] using
                map_bind₃
                  (Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource before) lower)
                  (Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource before) upper)
                  (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                    (before.snoc (.member label lower upper))) codomain)
                  (Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource after) (lower.rename rho))
                  (Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource after) (upper.rename rho))
                  (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
                    (after.snoc (.member label (lower.rename rho)
                      (upper.rename rho)))) (codomain.rename rho.lift))
                  (fun type => type.substitute substitution)
                  (fun type => type.substitute substitution)
                  (fun type => type.substitute (substitution.liftPayload
                    MemberEncoding.names MemberEncoding.constraints))
                  (fun type => type.substitute substitution)
                  MemberEncoding.forallType MemberEncoding.forallType
                  lowerNatural upperNatural codomainNatural
                  (fun lower upper result =>
                    forallType_substitute lower upper result substitution)

/-! ## Application-facing corollaries -/

/-- The target scope induced by a non-member source declaration is exactly
one ordinary term extension. -/
def plainExtensionSig {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) {domain : DotFC.Source.Ty source}
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper) :
    TargetSig (context.snoc domain) = TargetSig context ▹ .term :=
  match domain with
  | .top => rfl
  | .bot => rfl
  | .all _ _ => rfl
  | .sel _ _ => rfl
  | .member label lower upper =>
      False.elim (plain label lower upper rfl)

/-- View a type in the layout scope of a plain source declaration.  This
cast is definitionally the identity in each of the four plain cases. -/
def castPlainBody {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) {domain : DotFC.Source.Ty source}
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper)
    (type : FCsub.Ty (TargetSig context ▹ .term)) :
    FCsub.Ty (TargetSig (context.snoc domain)) :=
  Eq.mpr (congrArg FCsub.Ty (plainExtensionSig context plain)) type

private def instantiateTermSquare {scope : FCsub.Sig}
    (replacement : FCsub.Tm scope) :
    FCsub.PartialTypeRename.SubstSquare
      (FCsub.PartialTypeRename.dropTerm (scope := scope))
      (FCsub.Subst.id.instantiateTerm replacement) FCsub.Subst.id
      FCsub.PartialTypeRename.id where
  typeVar := fun name => by
    cases name with
    | there name => rfl

/-- Ordinary term strengthening is the partial-renaming presentation of
ordinary term instantiation.  FCsub types contain no term variables, so the
partial operation always succeeds. -/
theorem strengthenTerm_eq_instantiate {scope : FCsub.Sig}
    (type : FCsub.Ty (scope ▹ .term)) (replacement : FCsub.Tm scope) :
    type.strengthenTerm =
      some (type.substitute (FCsub.Subst.id.instantiateTerm replacement)) := by
  have natural := FCsub.Ty.rename?_substitute_square type
    (FCsub.PartialTypeRename.dropTerm (scope := scope))
    (FCsub.Subst.id.instantiateTerm replacement) FCsub.Subst.id
    FCsub.PartialTypeRename.id (instantiateTermSquare replacement)
  change type.rename? FCsub.PartialTypeRename.dropTerm = some _
  cases equation : type.rename? FCsub.PartialTypeRename.dropTerm with
  | none => simp [equation] at natural
  | some result =>
      simp only [equation, Option.map_some, FCsub.Ty.substitute_id,
        FCsub.Ty.rename?_id] at natural
      exact natural

private def liftTerm_comp_instantiateTerm_typeEq
    {source target : FCsub.Sig} (before : FCsub.Subst source target)
    (replacement : FCsub.Tm target) :
    FCsub.Subst.TypeEq
      (before.liftTerm.comp
        (FCsub.Subst.id.instantiateTerm replacement))
      (before.instantiateTerm replacement) where
  typeVar := fun index => by
    cases index with
    | there index =>
        simpa only [FCsub.Subst.comp, FCsub.Subst.liftTerm,
          FCsub.Subst.instantiateTerm, FCsub.Ty.substitute_id] using
          (FCsub.Ty.substitute_weaken_instantiateTerm
            (before.typeVar index) FCsub.Subst.id replacement)

/-- For a stable codomain below a plain binder, target substitution by the
layout image of the source argument produces exactly the translation of the
opened source codomain. -/
theorem openPlain_substitute {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainFormation : DotFC.Source.Wf context domain}
    {codomainFormation : DotFC.Source.Wf (context.snoc domain) codomain}
    (codomainStable : StableFragment.StableWf
      (valid.snoc domainFormation) codomainFormation)
    (argument : DotFC.BVar source .term)
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper)
    {bodyTarget : FCsub.Ty (TargetSig context ▹ .term)}
    {resultTarget : FCsub.Ty (TargetSig context)}
    (bodyTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc domain)) codomain
      (castPlainBody context plain bodyTarget))
    (resultTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (codomain.open argument)
      resultTarget) :
    bodyTarget.substitute
        (FCsub.Subst.id.instantiateTerm
          (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context)
            argument))) =
      resultTarget := by
  unfold Layout.Translates at bodyTranslation resultTranslation
  change Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context)
    (codomain.rename (DotFC.Source.Rename.openAt argument)) =
      some resultTarget at resultTranslation
  cases domain with
  | top =>
      have natural := translateTy_substitute (.top argument) codomainStable
      simp only [DotFC.Explicit.Ctx.ofSource_snoc] at natural
      change Layout.translateTy?
        ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top) codomain =
          some bodyTarget at bodyTranslation
      rw [bodyTranslation] at natural
      rw [resultTranslation] at natural
      exact Option.some.inj natural
  | bot =>
      have natural := translateTy_substitute (.bot argument) codomainStable
      simp only [DotFC.Explicit.Ctx.ofSource_snoc] at natural
      change Layout.translateTy?
        ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot) codomain =
          some bodyTarget at bodyTranslation
      rw [bodyTranslation] at natural
      rw [resultTranslation] at natural
      exact Option.some.inj natural
  | all nestedDomain nestedCodomain =>
      have natural := translateTy_substitute
        (.all nestedDomain nestedCodomain argument) codomainStable
      simp only [DotFC.Explicit.Ctx.ofSource_snoc] at natural
      change Layout.translateTy?
        ((DotFC.Explicit.Ctx.ofSource context).extendTerm
          (.all nestedDomain nestedCodomain)) codomain =
          some bodyTarget at bodyTranslation
      rw [bodyTranslation] at natural
      rw [resultTranslation] at natural
      exact Option.some.inj natural
  | sel path label =>
      have natural := translateTy_substitute
        (.selection path label argument) codomainStable
      simp only [DotFC.Explicit.Ctx.ofSource_snoc] at natural
      change Layout.translateTy?
        ((DotFC.Explicit.Ctx.ofSource context).extendTerm (.sel path label))
          codomain = some bodyTarget at bodyTranslation
      rw [bodyTranslation] at natural
      rw [resultTranslation] at natural
      exact Option.some.inj natural
  | member label lower upper =>
      exact False.elim (plain label lower upper rfl)

/-- Stable opening below a plain source binder gives the exact FCsub
nonescape premise required by ordinary target application. -/
theorem openPlain_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainFormation : DotFC.Source.Wf context domain}
    {codomainFormation : DotFC.Source.Wf (context.snoc domain) codomain}
    (codomainStable : StableFragment.StableWf
      (valid.snoc domainFormation) codomainFormation)
    (argument : DotFC.BVar source .term)
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper)
    {bodyTarget : FCsub.Ty (TargetSig context ▹ .term)}
    {resultTarget : FCsub.Ty (TargetSig context)}
    (bodyTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc domain)) codomain
      (castPlainBody context plain bodyTarget))
    (resultTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (codomain.open argument)
      resultTarget) :
    bodyTarget.strengthenTerm = some resultTarget := by
  rw [strengthenTerm_eq_instantiate]
  rw [openPlain_substitute codomainStable argument plain
    bodyTranslation resultTranslation]

/-- For a stable codomain below a member binder, the exact static witnesses,
evidence, and payload selected by a `MemberUse` produce the translation of
the opened source codomain. -/
theorem openMember_substitute {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainFormation : DotFC.Source.Wf context (.member label lower upper)}
    {codomainFormation : DotFC.Source.Wf
      (context.snoc (.member label lower upper)) codomain}
    (codomainStable : StableFragment.StableWf
      (valid.snoc domainFormation) codomainFormation)
    (argument : DotFC.BVar source .term)
    (argumentRoot : StableFragment.StableRoot context argument label)
    (use : Elaboration.MemberUse (TargetSig context))
    (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
      argument label = some use.slot)
    {bodyTarget : FCsub.Ty (MemberEncoding.Payload (TargetSig context))}
    {resultTarget : FCsub.Ty (TargetSig context)}
    (bodyTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower upper))) codomain bodyTarget)
    (resultTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (codomain.open argument)
      resultTarget) :
    bodyTarget.substitute
        ((FCsub.Subst.fromStaticArgs FCsub.Subst.id
          (MemberEncoding.witnessArgs (.tvar use.slot.name))
          (MemberEncoding.evidenceArgs use.lowerEvidence
            use.upperEvidence)).instantiateTerm (.var use.slot.payload)) =
      resultTarget := by
  have natural := translateTy_substitute
    (.member lower upper argument argumentRoot use slotLookup) codomainStable
  unfold Layout.Translates at bodyTranslation resultTranslation
  change Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context)
    (codomain.rename (DotFC.Source.Rename.openAt argument)) =
      some resultTarget at resultTranslation
  simp only [DotFC.Explicit.Ctx.ofSource_snoc] at bodyTranslation natural
  rw [bodyTranslation] at natural
  rw [resultTranslation] at natural
  exact Option.some.inj natural

/-- Stable member opening supplies both application obligations at once:
static instantiation exposes the ordinary unit payload arrow, and the
resulting codomain strengthens to the translation of source opening. -/
theorem openMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainFormation : DotFC.Source.Wf context (.member label lower upper)}
    {codomainFormation : DotFC.Source.Wf
      (context.snoc (.member label lower upper)) codomain}
    (codomainStable : StableFragment.StableWf
      (valid.snoc domainFormation) codomainFormation)
    (argument : DotFC.BVar source .term)
    (argumentRoot : StableFragment.StableRoot context argument label)
    (use : Elaboration.MemberUse (TargetSig context))
    (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
      argument label = some use.slot)
    {bodyTarget : FCsub.Ty (MemberEncoding.Payload (TargetSig context))}
    {resultTarget : FCsub.Ty (TargetSig context)}
    (bodyTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower upper))) codomain bodyTarget)
    (resultTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (codomain.open argument)
      resultTarget) :
    ∃ instantiatedCodomain : FCsub.Ty (TargetSig context ▹ .term),
      (FCsub.Ty.arr .one bodyTarget).instantiateStatic
          (MemberEncoding.witnessArgs (.tvar use.slot.name)) =
          FCsub.Ty.arr .one instantiatedCodomain ∧
        instantiatedCodomain.strengthenTerm = some resultTarget := by
  let staticSubstitution := FCsub.Subst.fromStaticArgs FCsub.Subst.id
    (MemberEncoding.witnessArgs (.tvar use.slot.name))
    (MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence)
  let instantiatedCodomain := bodyTarget.substitute staticSubstitution.liftTerm
  refine ⟨instantiatedCodomain, ?_, ?_⟩
  · rw [FCsub.Ty.instantiateStatic_as_substitute _ _
      (MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence)]
    rfl
  · have opened := openMember_substitute codomainStable argument argumentRoot
      use slotLookup bodyTranslation resultTranslation
    have composition :
        instantiatedCodomain.substitute
            (FCsub.Subst.id.instantiateTerm (.var use.slot.payload)) =
          bodyTarget.substitute
            (staticSubstitution.instantiateTerm (.var use.slot.payload)) := by
      unfold instantiatedCodomain
      rw [FCsub.Ty.substitute_comp]
      exact FCsub.Ty.substitute_congr bodyTarget
        (liftTerm_comp_instantiateTerm_typeEq staticSubstitution
          (.var use.slot.payload))
    rw [strengthenTerm_eq_instantiate, composition]
    simpa only [staticSubstitution] using congrArg some opened

end ContextOpening

end DotToFCsub.StableOpening
