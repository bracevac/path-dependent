import DotFC.Explicit.Elaboration
import DotFC.Explicit.Normalization
import DotFC.Explicit.Checker
import DotFC.Source.Examples

/-!
# Checked Stage-A regressions

These examples pin down the two proof-relevant behaviors that are easiest to
lose in refactoring: one bound member handle may be reused for both selection
directions, and ANF application carries independently checked function and
argument views.
-/

namespace DotFC.Explicit.Examples

open DotFC

/-! ## One reusable handle keeps bad-bound provenance visible -/

def sharedBadBoundsExposure : Exposure ([] ▹ .term) :=
  Elaboration.handle Source.Examples.badBoundsHandle

/-- Unlike the derivation-directed translation, which preserves each source
selection node literally, the target language can bind an exposure once and
reuse the resulting handle in a whole coercion body. -/
def sharedBadBoundsEvidence : LeCo ([] ▹ .term) :=
  .letHandle sharedBadBoundsExposure
    (.trans (.lower .here) (.upper .here))

theorem shared_bad_bounds_checks :
    synthLe (Ctx.ofSource Source.Examples.badBoundsContext)
      sharedBadBoundsEvidence = some (.top, .bot) := by
  native_decide

def sharedBadBoundsTyping :
    LeCo.HasType (Ctx.ofSource Source.Examples.badBoundsContext)
      sharedBadBoundsEvidence .top .bot :=
  synthLe_sound shared_bad_bounds_checks

/-- Normalization keeps the characteristic `lower ; upper` path explicit. -/
theorem shared_bad_bounds_normalizes_visibly :
    sharedBadBoundsEvidence.normalize = sharedBadBoundsEvidence := by
  native_decide

/-- The derivation-directed compiler also exposes both halves explicitly; it
does not replace the source transitivity node by an oracle. -/
theorem source_bad_bounds_compiles_structurally :
    Elaboration.sub Source.Examples.badBounds =
      .trans
        (.letHandle sharedBadBoundsExposure (.lower .here))
        (.letHandle sharedBadBoundsExposure (.upper .here)) := by
  native_decide

/-! ## Application carries both view coercions -/

def functionType : Source.Ty [] :=
  .all .top (.top : Source.Ty ([] ▹ .term))

def appContext : Source.Ctx (([] ▹ .term) ▹ .term) :=
  (Source.Ctx.nil.snoc functionType).snoc (.bot : Source.Ty ([] ▹ .term))

def functionLookup :
    Source.Lookup appContext (.there .here)
      (.all .top (.top : Source.Ty ((([] ▹ .term) ▹ .term) ▹ .term))) :=
  .there .here

def argumentLookup : Source.Lookup appContext .here .bot := .here

def argumentView : Source.HasTy appContext (.var .here) .top :=
  .sub (.var argumentLookup) (.top .bot) .top

def sourceApplication :
    Source.HasTy appContext (.app (.there .here) .here) .top :=
  @Source.HasTy.app _ appContext (.there .here) .here .top .top
    (.var functionLookup) argumentView .top

def explicitApplication : Tm (([] ▹ .term) ▹ .term) :=
  .app (.there .here) .here
    (.refl (.all .top .top))
    (.trans (.refl .bot) (.top .bot))

theorem application_compiles_both_views :
    Elaboration.term sourceApplication = explicitApplication := by
  native_decide

theorem application_checks :
    synthTm (Ctx.ofSource appContext) explicitApplication = some .top := by
  native_decide

def applicationTyping :
    Tm.HasType (Ctx.ofSource appContext) explicitApplication .top := by
  simpa [application_compiles_both_views] using
    Elaboration.termTyping sourceApplication

theorem application_erases_to_source :
    explicitApplication.erase = (.app (.there .here) .here : Source.Tm _).erase := by
  simpa [application_compiles_both_views] using
    Elaboration.term_erase sourceApplication

/-! ## Opaque selections do not grant bound elimination -/

/-- A context may contain a well-scoped selection annotation without any
member-handle binder.  The selection refers to the older term variable. -/
abbrev OpaqueSelectionSig : Sig := ([] ▹ .term) ▹ .term

def opaqueSelectionLabel : Name := 37

def opaqueSelectionContext : Ctx OpaqueSelectionSig :=
  (Ctx.nil.extendTerm (.top : Source.Ty [])).extendTerm
    (.sel (.here : BVar ([] ▹ .term) .term) opaqueSelectionLabel)

def opaqueSelection : Source.Ty OpaqueSelectionSig :=
  .sel (.there (.here : BVar ([] ▹ .term) .term)) opaqueSelectionLabel

/-- Scope formation accepts the annotation as an opaque, intrinsically
scoped atom. -/
theorem opaque_selection_is_scope_formed :
    checkTyScope opaqueSelection = true := by
  native_decide

theorem opaque_annotation_context_is_scope_formed :
    checkContextScope opaqueSelectionContext = true := by
  native_decide

/-- The term checker may return the opaque annotation for the newest
variable; doing so still grants no member elimination rule. -/
theorem opaque_annotation_types_variable :
    synthTm opaqueSelectionContext (.var .here) = some opaqueSelection := by
  native_decide

/-- Equality reflexivity may mention the opaque annotation; this proves no
member bounds. -/
theorem opaque_selection_refl_checks :
    synthLe opaqueSelectionContext (.refl opaqueSelection) =
      some (opaqueSelection, opaqueSelection) := by
  native_decide

/-- Merely presenting the opaque selection as the inclusion of an exposure
does not work: an exposure must end at the declared member interval. -/
def rejectedOpaqueExposure : Exposure OpaqueSelectionSig :=
  .view (.here : BVar OpaqueSelectionSig .term) opaqueSelectionLabel
    .bot .top (.refl opaqueSelection)

theorem unexposed_selection_is_rejected :
    synthExposure opaqueSelectionContext rejectedOpaqueExposure = none := by
  native_decide

/-- There is no member-handle variable in the term-only signature.  Since
`LeCo.lower` and `LeCo.upper` require such a variable, neither bound evidence
can even be formed until a checked `letHandle` introduces one. -/
def noOpaqueMemberHandle : BVar OpaqueSelectionSig .member → False
  | .there (.there handle) => nomatch handle

theorem opaque_context_has_no_member_handle
    (handle : BVar OpaqueSelectionSig .member) : False :=
  noOpaqueMemberHandle handle

end DotFC.Explicit.Examples
