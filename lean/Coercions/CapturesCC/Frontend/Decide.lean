import Coercions.CapturesCC.DotMNF.Typing
import Coercions.CapturesCC.FCdot.Checker
import Coercions.CapturesCC.DotToFCdot.EvidenceTyped
import Coercions.CapturesCC.DotMNF.Examples

/-!
# The decided side conditions

The typer of this front end discharges five kinds of side condition by
decision procedures, and computes capture sets and written types by a few
total functions.

- Well-formedness of a shape, a type and an answer, `shapeWf?`, `tyWf?` and
  `eTyWf?`.  The only premise of `Shape.Wf` that is not structural is the
  `Shape.Decl` of `Wf.mu`, which the frozen `Shape.isDecl` already decides.
  An arrow's domain sits under the arrow's capture binder and its codomain
  under that binder and the parameter, so the procedures are stated over
  every signature at once.
- Distinctness of the labels of a definition block, `defsDistinct?`, over
  the three definition kinds by the frozen `Defs.labels`.
- The two label facts a well-formed context asks of the self shape of an
  object literal, `literalShape?` and `distinctLabels?`.  A literal's shape
  has equal bounds at every member, and its member labels are pairwise
  distinct.
- Strengthening, the inverse of weakening, over capture sets, shapes, types
  and answers, past a binder of either kind.  The avoidance ladder of the
  typer climbs it, and the way out through an unpacking strengthens an
  answer past a capture binder and a term binder.
- `capJoin`, the union of two capture sets without repeated atoms, and the
  candidate sets a binder leaves behind when it goes out of scope.

Two total functions read contexts.  `ctxVars` and `ctxCaps` list the term
variables and the capture binders.  `readAt` gives a written type the
reading of `any` and `fresh` the version prescribes at the position it is
written at.

Strengthening reuses the target's partial renaming as it stands:
`PartialRename`, `PartialRename.lift`, `PartialRename.unshift`, `Inverts`,
`Inverts.lift`, `unshift_inverts` and `witness?` of
`lean/Coercions/CapturesCC/FCdot/Checker.lean`.  That machinery is generic
over `Sig`, `Kind` and `BVar`, which the two calculi share.  Only the
traversals over the source's capture atoms, shapes, types and answers are
new.  They copy the shape of the target's own `rename?` functions.

A candidate set is never trusted.  The typer follows each one with evidence,
a decided inclusion or a subcapturing derivation from the search, so the
functions that compute candidates carry no lemma.

Every name here is a plain name in `namespace CapturesCCFrontend`, never a
member of a namespace of the version, so the functions are written as
applications and not with dot notation.  Every recursive definition says
`termination_by structural`, so all of this reduces in the kernel and the
tests at the end are `by decide`.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx)

/-! ## Well-formedness of shapes, types and answers

`shapeWf?` mirrors `Shape.Wf` clause for clause.  A capture member is well
formed outright, a box is well formed when the type inside it is, and a
type when its shape is.  An arrow asks it of its domain and its codomain,
and an answer of the type it holds, under the witness binder for an
existential.  `Wf.typ` relates its two bounds not at all, so `{A : ⊤..⊥}` is
well formed. -/

mutual
/-- The decision procedure for `Shape.Wf`. -/
def shapeWf? {s : Sig} (S : Shape s) : Bool :=
  match S with
  | .top | .bot | .sel _ _ | .cap _ _ _ => true
  | .typ _ S T => shapeWf? S && shapeWf? T
  | .fld _ T => tyWf? T
  | .mu S => shapeWf? S && S.isDecl
  | .all T U => tyWf? T && eTyWf? U
  | .and S T => shapeWf? S && shapeWf? T
  | .box T => tyWf? T
termination_by structural S
/-- The decision procedure for `Ty.Wf`. -/
def tyWf? {s : Sig} (T : Ty s) : Bool :=
  match T with
  | .capt _ S => shapeWf? S
termination_by structural T
/-- The decision procedure for `ETy.Wf`. -/
def eTyWf? {s : Sig} (E : ETy s) : Bool :=
  match E with
  | .ty T => tyWf? T
  | .ex _ T => tyWf? T
termination_by structural E
end

mutual
theorem shapeWf?_iff : ∀ {s : Sig} (S : Shape s), shapeWf? S = true ↔ Shape.Wf S
  | _, .top => ⟨fun _ => .top, fun _ => by simp [shapeWf?]⟩
  | _, .bot => ⟨fun _ => .bot, fun _ => by simp [shapeWf?]⟩
  | _, .sel _ _ => ⟨fun _ => .sel, fun _ => by simp [shapeWf?]⟩
  | _, .cap _ _ _ => ⟨fun _ => .cap, fun _ => by simp [shapeWf?]⟩
  | _, .typ _ S T =>
      ⟨fun h => by
        simp only [shapeWf?, Bool.and_eq_true] at h
        exact .typ ((shapeWf?_iff S).mp h.1) ((shapeWf?_iff T).mp h.2),
       fun h => by
        cases h with
        | typ hS hT =>
            simp only [shapeWf?, Bool.and_eq_true]
            exact ⟨(shapeWf?_iff S).mpr hS, (shapeWf?_iff T).mpr hT⟩⟩
  | _, .fld _ T =>
      ⟨fun h => by
        simp only [shapeWf?] at h
        exact .fld ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | fld hT => simp only [shapeWf?]; exact (tyWf?_iff T).mpr hT⟩
  | _, .mu S =>
      ⟨fun h => by
        simp only [shapeWf?, Bool.and_eq_true] at h
        exact .mu ((shapeWf?_iff S).mp h.1) ((Shape.isDecl_iff S).mp h.2),
       fun h => by
        cases h with
        | mu hS hD =>
            simp only [shapeWf?, Bool.and_eq_true]
            exact ⟨(shapeWf?_iff S).mpr hS, (Shape.isDecl_iff S).mpr hD⟩⟩
  | _, .all T U =>
      ⟨fun h => by
        simp only [shapeWf?, Bool.and_eq_true] at h
        exact .all ((tyWf?_iff T).mp h.1) ((eTyWf?_iff U).mp h.2),
       fun h => by
        cases h with
        | all hT hU =>
            simp only [shapeWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff T).mpr hT, (eTyWf?_iff U).mpr hU⟩⟩
  | _, .and S T =>
      ⟨fun h => by
        simp only [shapeWf?, Bool.and_eq_true] at h
        exact .and ((shapeWf?_iff S).mp h.1) ((shapeWf?_iff T).mp h.2),
       fun h => by
        cases h with
        | and hS hT =>
            simp only [shapeWf?, Bool.and_eq_true]
            exact ⟨(shapeWf?_iff S).mpr hS, (shapeWf?_iff T).mpr hT⟩⟩
  | _, .box T =>
      ⟨fun h => by
        simp only [shapeWf?] at h
        exact .box ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | box hT => simp only [shapeWf?]; exact (tyWf?_iff T).mpr hT⟩

theorem tyWf?_iff : ∀ {s : Sig} (T : Ty s), tyWf? T = true ↔ Ty.Wf T
  | _, .capt _ S =>
      ⟨fun h => by
        simp only [tyWf?] at h
        exact .capt ((shapeWf?_iff S).mp h),
       fun h => by
        cases h with
        | capt hS => simp only [tyWf?]; exact (shapeWf?_iff S).mpr hS⟩

theorem eTyWf?_iff : ∀ {s : Sig} (E : ETy s), eTyWf? E = true ↔ ETy.Wf E
  | _, .ty T =>
      ⟨fun h => by
        simp only [eTyWf?] at h
        exact .ty ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | ty hT => simp only [eTyWf?]; exact (tyWf?_iff T).mpr hT⟩
  | _, .ex _ T =>
      ⟨fun h => by
        simp only [eTyWf?] at h
        exact .ex ((tyWf?_iff T).mp h),
       fun h => by
        cases h with
        | ex hT => simp only [eTyWf?]; exact (tyWf?_iff T).mpr hT⟩
end

instance instDecidableShapeWf {s : Sig} (S : Shape s) : Decidable (Shape.Wf S) :=
  decidable_of_iff _ (shapeWf?_iff S)

instance instDecidableTyWf {s : Sig} (T : Ty s) : Decidable (Ty.Wf T) :=
  decidable_of_iff _ (tyWf?_iff T)

instance instDecidableETyWf {s : Sig} (E : ETy s) : Decidable (ETy.Wf E) :=
  decidable_of_iff _ (eTyWf?_iff E)

/-! ## Distinctness of the labels of a definition block

`Defs.labels` is frozen and covers the three definition kinds, type, capture
and term.  `Label` has decidable equality, so the test is list membership. -/

/-- No label of the left block is a label of the right block. -/
def labelsDisjoint? (d e : Defs s) : Bool :=
  d.labels.all (fun l => ! e.labels.contains l)

theorem labelsDisjoint?_iff (d e : Defs s) :
    labelsDisjoint? d e = true ↔ ∀ l, l ∈ d.labels → l ∉ e.labels := by
  simp [labelsDisjoint?]

/-- The decision procedure for `Defs.Distinct`. -/
def defsDistinct? {s : Sig} (d : Defs s) : Bool :=
  match d with
  | .typ _ _ | .cap _ _ | .trm _ _ => true
  | .and d e => defsDistinct? d && defsDistinct? e && labelsDisjoint? d e
termination_by structural d

theorem defsDistinct?_iff : ∀ {s : Sig} (d : Defs s), defsDistinct? d = true ↔ Defs.Distinct d
  | _, .typ _ _ => ⟨fun _ => .typ, fun _ => by simp [defsDistinct?]⟩
  | _, .cap _ _ => ⟨fun _ => .cap, fun _ => by simp [defsDistinct?]⟩
  | _, .trm _ _ => ⟨fun _ => .trm, fun _ => by simp [defsDistinct?]⟩
  | _, .and d e =>
      ⟨fun h => by
        simp only [defsDistinct?, Bool.and_eq_true] at h
        exact .and ((defsDistinct?_iff d).mp h.1.1) ((defsDistinct?_iff e).mp h.1.2)
          ((labelsDisjoint?_iff d e).mp h.2),
       fun h => by
        cases h with
        | and hd he hdis =>
            simp only [defsDistinct?, Bool.and_eq_true]
            exact ⟨⟨(defsDistinct?_iff d).mpr hd, (defsDistinct?_iff e).mpr he⟩,
              (labelsDisjoint?_iff d e).mpr hdis⟩⟩

instance instDecidableDefsDistinct {s : Sig} (d : Defs s) : Decidable (Defs.Distinct d) :=
  decidable_of_iff _ (defsDistinct?_iff d)

/-! ## The self shape of an object literal

A context binds the self of an object literal at a shape that the
translation reads as the literal's own precise type.  So a well-formed
context asks two facts of that shape.  `Shape.LiteralShape`: every member
is a type member or a capture member with equal bounds, or a field, and
the members are joined by intersections.  `Shape.DistinctLabels`: the
member labels, read by the frozen `Shape.declLabels`, are pairwise
distinct.  Both are structural, so both are decided clause for clause. -/

/-- The decision procedure for `Shape.LiteralShape`.  The bounds of a member
are compared by the decidable equality of shapes and of capture sets. -/
def literalShape? {s : Sig} (S : Shape s) : Bool :=
  match S with
  | .typ _ T U => decide (T = U)
  | .cap _ c d => decide (c = d)
  | .fld _ _ => true
  | .and S T => literalShape? S && literalShape? T
  | .top | .bot | .sel _ _ | .mu _ | .all _ _ | .box _ => false
termination_by structural S

theorem literalShape?_iff : ∀ {s : Sig} (S : Shape s), literalShape? S = true ↔ S.LiteralShape
  | _, .typ _ T U =>
      ⟨fun h => by
        simp only [literalShape?, decide_eq_true_eq] at h
        subst h; exact .typ,
       fun h => by
        cases h
        simp [literalShape?]⟩
  | _, .cap _ c d =>
      ⟨fun h => by
        simp only [literalShape?, decide_eq_true_eq] at h
        subst h; exact .cap,
       fun h => by
        cases h
        simp [literalShape?]⟩
  | _, .fld _ _ => ⟨fun _ => .fld, fun _ => rfl⟩
  | _, .and S T =>
      ⟨fun h => by
        simp only [literalShape?, Bool.and_eq_true] at h
        exact .and ((literalShape?_iff S).mp h.1) ((literalShape?_iff T).mp h.2),
       fun h => by
        cases h with
        | and hS hT =>
            simp only [literalShape?, Bool.and_eq_true]
            exact ⟨(literalShape?_iff S).mpr hS, (literalShape?_iff T).mpr hT⟩⟩
  | _, .top => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩
  | _, .bot => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩
  | _, .sel _ _ => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩
  | _, .mu _ => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩
  | _, .all _ _ => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩
  | _, .box _ => ⟨fun h => by simp [literalShape?] at h, fun h => by cases h⟩

instance instDecidableLiteralShape {s : Sig} (S : Shape s) : Decidable S.LiteralShape :=
  decidable_of_iff _ (literalShape?_iff S)

/-- No member label of the left shape is a member label of the right shape. -/
def declLabelsDisjoint? (S T : Shape s) : Bool :=
  S.declLabels.all (fun l => ! T.declLabels.contains l)

theorem declLabelsDisjoint?_iff (S T : Shape s) :
    declLabelsDisjoint? S T = true ↔ ∀ l, l ∈ S.declLabels → l ∉ T.declLabels := by
  simp [declLabelsDisjoint?]

/-- The decision procedure for `Shape.DistinctLabels`.  A single member is
distinct outright, an intersection when both sides are and share no label,
and any other shape is not a declaration of members at all. -/
def distinctLabels? {s : Sig} (S : Shape s) : Bool :=
  match S with
  | .typ _ _ _ | .cap _ _ _ | .fld _ _ => true
  | .and S T => distinctLabels? S && distinctLabels? T && declLabelsDisjoint? S T
  | .top | .bot | .sel _ _ | .mu _ | .all _ _ | .box _ => false
termination_by structural S

theorem distinctLabels?_iff :
    ∀ {s : Sig} (S : Shape s), distinctLabels? S = true ↔ S.DistinctLabels
  | _, .typ _ _ _ => ⟨fun _ => .typ, fun _ => rfl⟩
  | _, .cap _ _ _ => ⟨fun _ => .cap, fun _ => rfl⟩
  | _, .fld _ _ => ⟨fun _ => .fld, fun _ => rfl⟩
  | _, .and S T =>
      ⟨fun h => by
        simp only [distinctLabels?, Bool.and_eq_true] at h
        exact .and ((distinctLabels?_iff S).mp h.1.1) ((distinctLabels?_iff T).mp h.1.2)
          ((declLabelsDisjoint?_iff S T).mp h.2),
       fun h => by
        cases h with
        | and hS hT hdis =>
            simp only [distinctLabels?, Bool.and_eq_true]
            exact ⟨⟨(distinctLabels?_iff S).mpr hS, (distinctLabels?_iff T).mpr hT⟩,
              (declLabelsDisjoint?_iff S T).mpr hdis⟩⟩
  | _, .top => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩
  | _, .bot => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩
  | _, .sel _ _ => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩
  | _, .mu _ => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩
  | _, .all _ _ => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩
  | _, .box _ => ⟨fun h => by simp [distinctLabels?] at h, fun h => by cases h⟩

instance instDecidableDistinctLabels {s : Sig} (S : Shape s) : Decidable S.DistinctLabels :=
  decidable_of_iff _ (distinctLabels?_iff S)

/-! ## Partial renaming of capture sets, paths, shapes, types and answers

Each traversal fails exactly when some variable it meets is outside the
domain of the renaming.  `any` and `fresh` hold no variable and are mapped
to themselves, as `CapAtom.rename` maps them.  An arrow lifts the renaming
once for its domain, past its capture binder, and twice for its codomain,
past that binder and the parameter.  An existential lifts it once for its
body, past the witness.  Soundness and completeness are stated against a
total renaming the partial one inverts, as the target states its own. -/

/-- A capture atom under a partial renaming. -/
def capAtomRename? {s1 s2 : Sig} : CapAtom s1 → PartialRename s1 s2 → Option (CapAtom s2)
  | .var x, ρ => (ρ.var x).map .var
  | .cvar κ, ρ => (ρ.var κ).map .cvar
  | .sel x ℓ, ρ => (ρ.var x).map (fun y => .sel y ℓ)
  | .any, _ => some .any
  | .fresh, _ => some .fresh

/-- A capture set under a partial renaming, atom by atom. -/
def capRename? {s1 s2 : Sig} (C : CaptureSet s1) (ρ : PartialRename s1 s2) :
    Option (CaptureSet s2) :=
  match C with
  | [] => some []
  | a :: C =>
      match capAtomRename? a ρ, capRename? C ρ with
      | some a', some C' => some (a' :: C')
      | _, _ => none
termination_by structural C

/-- A path under a partial renaming.  A path is a variable in this calculus. -/
def pathRename? {s1 s2 : Sig} : Path s1 → PartialRename s1 s2 → Option (Path s2)
  | .var x, ρ => (ρ.var x).map .var

mutual
/-- A shape under a partial renaming. -/
def shapeRename? {s1 s2 : Sig} (S : Shape s1) (ρ : PartialRename s1 s2) : Option (Shape s2) :=
  match S with
  | .top => some .top
  | .bot => some .bot
  | .typ A S T =>
      match shapeRename? S ρ, shapeRename? T ρ with
      | some S', some T' => some (.typ A S' T')
      | _, _ => none
  | .fld a T =>
      match tyRename? T ρ with
      | some T' => some (.fld a T')
      | none => none
  | .cap A c1 c2 =>
      match capRename? c1 ρ, capRename? c2 ρ with
      | some c1', some c2' => some (.cap A c1' c2')
      | _, _ => none
  | .sel p A => (pathRename? p ρ).map (fun q => .sel q A)
  | .mu S =>
      match shapeRename? S ρ.lift with
      | some S' => some (.mu S')
      | none => none
  | .all T U =>
      match tyRename? T ρ.lift, eTyRename? U ρ.lift.lift with
      | some T', some U' => some (.all T' U')
      | _, _ => none
  | .and S T =>
      match shapeRename? S ρ, shapeRename? T ρ with
      | some S', some T' => some (.and S' T')
      | _, _ => none
  | .box T =>
      match tyRename? T ρ with
      | some T' => some (.box T')
      | none => none
termination_by structural S
/-- A type under a partial renaming: its set and its shape. -/
def tyRename? {s1 s2 : Sig} (T : Ty s1) (ρ : PartialRename s1 s2) : Option (Ty s2) :=
  match T with
  | .capt C S =>
      match capRename? C ρ, shapeRename? S ρ with
      | some C', some S' => some (.capt C' S')
      | _, _ => none
termination_by structural T
/-- An answer under a partial renaming: the bound of an existential at the
renaming, its body past the witness binder. -/
def eTyRename? {s1 s2 : Sig} (E : ETy s1) (ρ : PartialRename s1 s2) : Option (ETy s2) :=
  match E with
  | .ty T =>
      match tyRename? T ρ with
      | some T' => some (.ty T')
      | none => none
  | .ex C T =>
      match capRename? C ρ, tyRename? T ρ.lift with
      | some C', some T' => some (.ex C' T')
      | _, _ => none
termination_by structural E
end

/-! ### Completeness: a renamed object comes back -/

theorem capAtomRename?_complete {s1 s2 : Sig} (a : CapAtom s2) (ρ : PartialRename s1 s2)
    (σ : Rename s2 s1) (h : ρ.Inverts σ) : capAtomRename? (a.rename σ) ρ = some a := by
  cases a with
  | var x =>
      simp only [CapAtom.rename, capAtomRename?]
      rw [(h (σ.var x) x).mpr rfl]; rfl
  | cvar κ =>
      simp only [CapAtom.rename, capAtomRename?]
      rw [(h (σ.var κ) κ).mpr rfl]; rfl
  | sel x ℓ =>
      simp only [CapAtom.rename, capAtomRename?]
      rw [(h (σ.var x) x).mpr rfl]; rfl
  | any => rfl
  | fresh => rfl

theorem capRename?_complete {s1 s2 : Sig} (C : CaptureSet s2) (ρ : PartialRename s1 s2)
    (σ : Rename s2 s1) (h : ρ.Inverts σ) : capRename? (CaptureSet.rename C σ) ρ = some C := by
  induction C with
  | nil => simp [capRename?]
  | cons a C ih =>
      simp only [CaptureSet.rename_cons, capRename?, capAtomRename?_complete a ρ σ h, ih]

theorem pathRename?_complete {s1 s2 : Sig} (q : Path s2) (ρ : PartialRename s1 s2)
    (σ : Rename s2 s1) (h : ρ.Inverts σ) : pathRename? (q.rename σ) ρ = some q := by
  cases q with
  | var x =>
      simp only [Path.rename, pathRename?]
      rw [(h (σ.var x) x).mpr rfl]; rfl

mutual
theorem shapeRename?_complete :
    ∀ {s1 s2 : Sig} (U : Shape s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → shapeRename? (U.rename σ) ρ = some U
  | _, _, .top, _, _, _ => by simp [Shape.rename, shapeRename?]
  | _, _, .bot, _, _, _ => by simp [Shape.rename, shapeRename?]
  | _, _, .typ A S T, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [shapeRename?_complete S ρ σ h, shapeRename?_complete T ρ σ h]
  | _, _, .fld a T, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [tyRename?_complete T ρ σ h]
  | _, _, .cap A c1 c2, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [capRename?_complete c1 ρ σ h, capRename?_complete c2 ρ σ h]
  | _, _, .sel p A, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [pathRename?_complete p ρ σ h]; rfl
  | _, _, .mu S, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [shapeRename?_complete S ρ.lift σ.lift h.lift]
  | _, _, .all T U, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [tyRename?_complete T ρ.lift σ.lift h.lift,
        eTyRename?_complete U ρ.lift.lift σ.lift.lift
          (PartialRename.Inverts.lift (PartialRename.Inverts.lift h))]
  | _, _, .and S T, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [shapeRename?_complete S ρ σ h, shapeRename?_complete T ρ σ h]
  | _, _, .box T, ρ, σ, h => by
      simp only [Shape.rename, shapeRename?]
      rw [tyRename?_complete T ρ σ h]

theorem tyRename?_complete :
    ∀ {s1 s2 : Sig} (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → tyRename? (U.rename σ) ρ = some U
  | _, _, .capt C S, ρ, σ, h => by
      simp only [Ty.rename, tyRename?]
      rw [capRename?_complete C ρ σ h, shapeRename?_complete S ρ σ h]

theorem eTyRename?_complete :
    ∀ {s1 s2 : Sig} (U : ETy s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → eTyRename? (U.rename σ) ρ = some U
  | _, _, .ty T, ρ, σ, h => by
      simp only [ETy.rename, eTyRename?]
      rw [tyRename?_complete T ρ σ h]
  | _, _, .ex C T, ρ, σ, h => by
      simp only [ETy.rename, eTyRename?]
      rw [capRename?_complete C ρ σ h, tyRename?_complete T ρ.lift σ.lift h.lift]
end

/-! ### Soundness: a result renames back to the input -/

theorem capAtomRename?_sound {s1 s2 : Sig} (a : CapAtom s1) (b : CapAtom s2)
    (ρ : PartialRename s1 s2) (σ : Rename s2 s1) (h : ρ.Inverts σ)
    (hb : capAtomRename? a ρ = some b) : a = b.rename σ := by
  cases a with
  | var x =>
      simp only [capAtomRename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h x y).mp hy]
  | cvar κ =>
      simp only [capAtomRename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h κ y).mp hy]
  | sel x ℓ =>
      simp only [capAtomRename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h x y).mp hy]
  | any =>
      simp only [capAtomRename?, Option.some.injEq] at hb
      subst hb; rfl
  | fresh =>
      simp only [capAtomRename?, Option.some.injEq] at hb
      subst hb; rfl

theorem capRename?_sound {s1 s2 : Sig} (C : CaptureSet s1) (D : CaptureSet s2)
    (ρ : PartialRename s1 s2) (σ : Rename s2 s1) (h : ρ.Inverts σ)
    (hD : capRename? C ρ = some D) : C = CaptureSet.rename D σ := by
  induction C generalizing D with
  | nil =>
      simp only [capRename?, Option.some.injEq] at hD
      subst hD; rfl
  | cons a C ih =>
      simp only [capRename?] at hD
      cases ha : capAtomRename? a ρ with
      | none => rw [ha] at hD; simp at hD
      | some b =>
        cases hC : capRename? C ρ with
        | none => rw [ha, hC] at hD; simp at hD
        | some D' =>
          rw [ha, hC] at hD
          simp only [Option.some.injEq] at hD
          subst hD
          rw [CaptureSet.rename_cons, ← capAtomRename?_sound a b ρ σ h ha, ← ih D' hC]

theorem pathRename?_sound {s1 s2 : Sig} (p : Path s1) (q : Path s2)
    (ρ : PartialRename s1 s2) (σ : Rename s2 s1) (h : ρ.Inverts σ)
    (hq : pathRename? p ρ = some q) : p = q.rename σ := by
  cases p with
  | var x =>
      simp only [pathRename?, Option.map_eq_some_iff] at hq
      obtain ⟨y, hy, hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [(h x y).mp hy]

mutual
theorem shapeRename?_sound :
    ∀ {s1 s2 : Sig} (S : Shape s1) (U : Shape s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → shapeRename? S ρ = some U → S = U.rename σ
  | _, _, .top, U, _, _, _, hU => by
      simp only [shapeRename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .bot, U, _, _, _, hU => by
      simp only [shapeRename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .typ A S T, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hS : shapeRename? S ρ with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : shapeRename? T ρ with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← shapeRename?_sound S S' ρ σ h hS, ← shapeRename?_sound T T' ρ σ h hT]
  | _, _, .fld a T, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hT : tyRename? T ρ with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Shape.rename]
        rw [← tyRename?_sound T T' ρ σ h hT]
  | _, _, .cap A c1 c2, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases h1 : capRename? c1 ρ with
      | none => rw [h1] at hU; simp at hU
      | some c1' =>
        cases h2 : capRename? c2 ρ with
        | none => rw [h1, h2] at hU; simp at hU
        | some c2' =>
          rw [h1, h2] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← capRename?_sound c1 c1' ρ σ h h1, ← capRename?_sound c2 c2' ρ σ h h2]
  | _, _, .sel p A, U, ρ, σ, h, hU => by
      simp only [shapeRename?, Option.map_eq_some_iff] at hU
      obtain ⟨q, hq, hU⟩ := hU
      subst hU
      simp only [Shape.rename]
      rw [← pathRename?_sound p q ρ σ h hq]
  | _, _, .mu S, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hS : shapeRename? S ρ.lift with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        rw [hS] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Shape.rename]
        rw [← shapeRename?_sound S S' ρ.lift σ.lift h.lift hS]
  | _, _, .all T V, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hT : tyRename? T ρ.lift with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        cases hV : eTyRename? V ρ.lift.lift with
        | none => rw [hT, hV] at hU; simp at hU
        | some V' =>
          rw [hT, hV] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← tyRename?_sound T T' ρ.lift σ.lift h.lift hT,
            ← eTyRename?_sound V V' ρ.lift.lift σ.lift.lift
              (PartialRename.Inverts.lift (PartialRename.Inverts.lift h)) hV]
  | _, _, .and S T, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hS : shapeRename? S ρ with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : shapeRename? T ρ with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← shapeRename?_sound S S' ρ σ h hS, ← shapeRename?_sound T T' ρ σ h hT]
  | _, _, .box T, U, ρ, σ, h, hU => by
      simp only [shapeRename?] at hU
      cases hT : tyRename? T ρ with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Shape.rename]
        rw [← tyRename?_sound T T' ρ σ h hT]

theorem tyRename?_sound :
    ∀ {s1 s2 : Sig} (T : Ty s1) (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → tyRename? T ρ = some U → T = U.rename σ
  | _, _, .capt C S, U, ρ, σ, h, hU => by
      simp only [tyRename?] at hU
      cases hC : capRename? C ρ with
      | none => rw [hC] at hU; simp at hU
      | some C' =>
        cases hS : shapeRename? S ρ with
        | none => rw [hC, hS] at hU; simp at hU
        | some S' =>
          rw [hC, hS] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← capRename?_sound C C' ρ σ h hC, ← shapeRename?_sound S S' ρ σ h hS]

theorem eTyRename?_sound :
    ∀ {s1 s2 : Sig} (E : ETy s1) (F : ETy s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → eTyRename? E ρ = some F → E = F.rename σ
  | _, _, .ty T, F, ρ, σ, h, hF => by
      simp only [eTyRename?] at hF
      cases hT : tyRename? T ρ with
      | none => rw [hT] at hF; simp at hF
      | some T' =>
        rw [hT] at hF
        simp only [Option.some.injEq] at hF
        subst hF
        simp only [ETy.rename]
        rw [← tyRename?_sound T T' ρ σ h hT]
  | _, _, .ex C T, F, ρ, σ, h, hF => by
      simp only [eTyRename?] at hF
      cases hC : capRename? C ρ with
      | none => rw [hC] at hF; simp at hF
      | some C' =>
        cases hT : tyRename? T ρ.lift with
        | none => rw [hC, hT] at hF; simp at hF
        | some T' =>
          rw [hC, hT] at hF
          simp only [Option.some.injEq] at hF
          subst hF
          simp only [ETy.rename]
          rw [← capRename?_sound C C' ρ σ h hC,
            ← tyRename?_sound T T' ρ.lift σ.lift h.lift hT]
end

/-! ## Strengthening

Strengthening is the action of `PartialRename.unshift`, the partial inverse
of `Rename.succ`.  It undoes one weakening exactly when the innermost binder
does not occur.  The binder may be of either kind: the avoidance ladder
strengthens past a term binder, and an unpacking leaves a capture binder
for its witness behind it as well. -/

/-- Undo one weakening of a capture set. -/
def capStrengthen? {s : Sig} {k : Kind} (C : CaptureSet (s,,k)) : Option (CaptureSet s) :=
  capRename? C PartialRename.unshift

/-- Undo one weakening of a shape. -/
def shapeStrengthen? {s : Sig} {k : Kind} (S : Shape (s,,k)) : Option (Shape s) :=
  shapeRename? S PartialRename.unshift

/-- Undo one weakening of a type. -/
def tyStrengthen? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option (Ty s) :=
  tyRename? T PartialRename.unshift

/-- Undo one weakening of an answer. -/
def eTyStrengthen? {s : Sig} {k : Kind} (E : ETy (s,,k)) : Option (ETy s) :=
  eTyRename? E PartialRename.unshift

theorem capStrengthen?_sound {s : Sig} {k : Kind} {C : CaptureSet (s,,k)} {D : CaptureSet s}
    (h : capStrengthen? C = some D) : C = CaptureSet.weaken D :=
  capRename?_sound C D PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem capStrengthen?_weaken {s : Sig} {k : Kind} (D : CaptureSet s) :
    capStrengthen? (CaptureSet.weaken D (k := k)) = some D :=
  capRename?_complete D PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Strengthening of a capture set inverts weakening, on the nose. -/
theorem capStrengthen?_iff {s : Sig} {k : Kind} {C : CaptureSet (s,,k)} {D : CaptureSet s} :
    capStrengthen? C = some D ↔ C = CaptureSet.weaken D := by
  constructor
  · exact capStrengthen?_sound
  · intro h; subst h; exact capStrengthen?_weaken D

theorem shapeStrengthen?_sound {s : Sig} {k : Kind} {S : Shape (s,,k)} {U : Shape s}
    (h : shapeStrengthen? S = some U) : S = U.weaken :=
  shapeRename?_sound S U PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem shapeStrengthen?_weaken {s : Sig} {k : Kind} (U : Shape s) :
    shapeStrengthen? (U.weaken (k := k)) = some U :=
  shapeRename?_complete U PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Strengthening of a shape inverts weakening, on the nose. -/
theorem shapeStrengthen?_iff {s : Sig} {k : Kind} {S : Shape (s,,k)} {U : Shape s} :
    shapeStrengthen? S = some U ↔ S = U.weaken := by
  constructor
  · exact shapeStrengthen?_sound
  · intro h; subst h; exact shapeStrengthen?_weaken U

theorem tyStrengthen?_sound {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s}
    (h : tyStrengthen? T = some U) : T = U.weaken :=
  tyRename?_sound T U PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem tyStrengthen?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthen? (U.weaken (k := k)) = some U :=
  tyRename?_complete U PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Strengthening of a type inverts weakening, on the nose. -/
theorem tyStrengthen?_iff {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s} :
    tyStrengthen? T = some U ↔ T = U.weaken := by
  constructor
  · exact tyStrengthen?_sound
  · intro h; subst h; exact tyStrengthen?_weaken U

theorem eTyStrengthen?_sound {s : Sig} {k : Kind} {E : ETy (s,,k)} {F : ETy s}
    (h : eTyStrengthen? E = some F) : E = F.weaken :=
  eTyRename?_sound E F PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem eTyStrengthen?_weaken {s : Sig} {k : Kind} (F : ETy s) :
    eTyStrengthen? (F.weaken (k := k)) = some F :=
  eTyRename?_complete F PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Strengthening of an answer inverts weakening, on the nose. -/
theorem eTyStrengthen?_iff {s : Sig} {k : Kind} {E : ETy (s,,k)} {F : ETy s} :
    eTyStrengthen? E = some F ↔ E = F.weaken := by
  constructor
  · exact eTyStrengthen?_sound
  · intro h; subst h; exact eTyStrengthen?_weaken F

/-! ### Strengthening with its equation

The second rung of the avoidance ladder rewrites the body's typing along the
equation, so the equation comes back with the result. -/

/-- Strengthening of a capture set, carrying the equation it establishes. -/
def capStrengthenW? {s : Sig} {k : Kind} (C : CaptureSet (s,,k)) :
    Option { D : CaptureSet s // C = CaptureSet.weaken D } :=
  match witness? (capStrengthen? C) with
  | some ⟨D, hD⟩ => some ⟨D, capStrengthen?_sound hD⟩
  | none => none

theorem capStrengthenW?_weaken {s : Sig} {k : Kind} (D : CaptureSet s) :
    capStrengthenW? (CaptureSet.weaken D (k := k)) = some ⟨D, rfl⟩ := by
  simp only [capStrengthenW?, CapturesCC.FCdot.witness?_eq_some (capStrengthen?_weaken (k := k) D)]

/-- Strengthening of a shape, carrying the equation it establishes. -/
def shapeStrengthenW? {s : Sig} {k : Kind} (S : Shape (s,,k)) :
    Option { U : Shape s // S = U.weaken } :=
  match witness? (shapeStrengthen? S) with
  | some ⟨U, hU⟩ => some ⟨U, shapeStrengthen?_sound hU⟩
  | none => none

theorem shapeStrengthenW?_weaken {s : Sig} {k : Kind} (U : Shape s) :
    shapeStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [shapeStrengthenW?,
    CapturesCC.FCdot.witness?_eq_some (shapeStrengthen?_weaken (k := k) U)]

/-- Strengthening of a type, carrying the equation it establishes. -/
def tyStrengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U.weaken } :=
  match witness? (tyStrengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, tyStrengthen?_sound hU⟩
  | none => none

theorem tyStrengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [tyStrengthenW?, CapturesCC.FCdot.witness?_eq_some (tyStrengthen?_weaken (k := k) U)]

/-- Strengthening of an answer, carrying the equation it establishes. -/
def eTyStrengthenW? {s : Sig} {k : Kind} (E : ETy (s,,k)) :
    Option { F : ETy s // E = F.weaken } :=
  match witness? (eTyStrengthen? E) with
  | some ⟨F, hF⟩ => some ⟨F, eTyStrengthen?_sound hF⟩
  | none => none

theorem eTyStrengthenW?_weaken {s : Sig} {k : Kind} (F : ETy s) :
    eTyStrengthenW? (F.weaken (k := k)) = some ⟨F, rfl⟩ := by
  simp only [eTyStrengthenW?,
    CapturesCC.FCdot.witness?_eq_some (eTyStrengthen?_weaken (k := k) F)]

/-- A weakened type is one that strengthens, decided by `tyStrengthen?`. -/
instance instDecidableIsWeakening {s : Sig} {k : Kind} (T : Ty (s,,k)) :
    Decidable (∃ U : Ty s, T = U.weaken) :=
  decidable_of_iff ((tyStrengthen? T).isSome = true)
    ⟨fun h => by
      cases hT : tyStrengthen? T with
      | none => rw [hT] at h; simp at h
      | some U => exact ⟨U, tyStrengthen?_sound hT⟩,
     fun h => by
      obtain ⟨U, hU⟩ := h
      subst hU
      rw [tyStrengthen?_weaken U]
      rfl⟩

/-! ## Joining capture sets

A capture set is a list read as a finite set, and `∪` is concatenation.
The typer joins the sets of the premises of a rule with `capJoin` instead,
which keeps the first set and adds the atoms of the second that the first
lacks, so that a set does not grow by repetition along a derivation.  Both
sets are included in the join, which is all a rule needs: each inclusion is
a `Subcap.elem`. -/

/-- `C` followed by the atoms of `D` that `C` lacks. -/
def capJoin {s : Sig} (C D : CaptureSet s) : CaptureSet s :=
  C ++ D.filter (fun a => !(CaptureSet.elem C a))

theorem capJoin_left {s : Sig} (C D : CaptureSet s) : CaptureSet.Subset C (capJoin C D) :=
  fun _ h => List.mem_append_left _ h

theorem capJoin_right {s : Sig} (C D : CaptureSet s) : CaptureSet.Subset D (capJoin C D) := by
  intro a ha
  cases hc : CaptureSet.elem C a with
  | true => exact List.mem_append_left _ ((CaptureSet.elem_iff C).mp hc)
  | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨ha, by simp [hc]⟩)

/-- The join of a list of sets, left to right. -/
def capJoinAll {s : Sig} (Cs : List (CaptureSet s)) : CaptureSet s :=
  match Cs with
  | [] => []
  | C :: Cs => capJoin C (capJoinAll Cs)
termination_by structural Cs

/-! ## Candidate sets for a binder that goes out of scope

Three rules drop a term binder `x` from a set over `(s,x)`.  `All-I` asks
the body's use set `V` to be below `U↑ ∪ {x}`, `{}-I` asks the same of the
definitions with the self, and `let` asks the body's use set and the
body's type to be below sets over `s`, weakened.  In each case the typer
builds a candidate over `s` and then proves the inclusion it needs.

`capReplaceHere R sel V` replaces the atom `{x}` of `V` by the set `R` and
each atom `{x.C}` by `sel C` when that is known.  For `All-I` and `{}-I`,
`R` is empty, since the rule adds `{x}` back itself.  For `let`, `R` is the
capture set of the bound term's type, which is what `sc-var` reads at the
binder.  `sel C` is the upper bound of the capture member `C` of `x`, which
`sc-sel-upper` reads.  An atom `{x.C}` with no known bound stays, and then
the candidate fails to strengthen.  `capAvoid?` strengthens the result. -/

/-- The image of one atom over `(s,x)` under the replacement of the binder. -/
def hereImage {s : Sig} (R : CaptureSet (s,x)) (sel : Label → Option (CaptureSet (s,x))) :
    CapAtom (s,x) → CaptureSet (s,x)
  | .var .here => R
  | .sel .here C => (sel C).getD [.sel .here C]
  | a => [a]

/-- Replace the atoms of the innermost term binder, joining the images. -/
def capReplaceHere {s : Sig} (R : CaptureSet (s,x)) (sel : Label → Option (CaptureSet (s,x)))
    (V : CaptureSet (s,x)) : CaptureSet (s,x) :=
  match V with
  | [] => []
  | a :: V => capJoin (hereImage R sel a) (capReplaceHere R sel V)
termination_by structural V

/-- The candidate set over `s` for a set over `(s,x)`: the binder's atoms
replaced, then the whole strengthened.  `none` when an atom of the binder
remains. -/
def capAvoid? {s : Sig} (R : CaptureSet (s,x)) (sel : Label → Option (CaptureSet (s,x)))
    (V : CaptureSet (s,x)) : Option (CaptureSet s) :=
  capStrengthen? (capReplaceHere R sel V)

/-- The candidate of `All-I` and `{}-I`: drop `{x}`, read `{x.C}` by `sel`,
strengthen the rest. -/
def capDropHere? {s : Sig} (sel : Label → Option (CaptureSet (s,x)))
    (V : CaptureSet (s,x)) : Option (CaptureSet s) :=
  capAvoid? [] sel V

/-- No member bound is known: every `{x.C}` stays. -/
def noSel {s : Sig} : Label → Option (CaptureSet s) := fun _ => none

/-! ## The binders of a context

`Ctx` has six constructors.  `cons` and `consSelf` bind a term variable.
`consSelf`, the binder of an object literal, is a term binder like `cons`,
so its variable is in the list of variables.  `consC` (a platform
capability), `consRoot` (a scope root) and `consInst` (the witness of a
pack) bind a capture variable, so each only shifts the term variables
below it. -/

/-- Every term variable of a context, newest binder first. -/
def ctxVars {s : Sig} (Γ : Ctx s) : List (BVar s .var) :=
  match Γ with
  | .nil => []
  | .cons Γ _ => .here :: (ctxVars Γ).map .there
  | .consSelf Γ _ _ _ => .here :: (ctxVars Γ).map .there
  | .consC Γ => (ctxVars Γ).map .there
  | .consRoot Γ => (ctxVars Γ).map .there
  | .consInst Γ _ => (ctxVars Γ).map .there
termination_by structural Γ

/-- Every capture binder of a context, newest binder first: the platform
capabilities, the scope roots and the witnesses alike. -/
def ctxCaps {s : Sig} (Γ : Ctx s) : List (BVar s .cap) :=
  match Γ with
  | .nil => []
  | .cons Γ _ => (ctxCaps Γ).map .there
  | .consSelf Γ _ _ _ => (ctxCaps Γ).map .there
  | .consC Γ => .here :: (ctxCaps Γ).map .there
  | .consRoot Γ => .here :: (ctxCaps Γ).map .there
  | .consInst Γ _ => .here :: (ctxCaps Γ).map .there
termination_by structural Γ

/-! ## Reading a written type

A program writes `any` and `fresh` and never a root or a witness.  The
version gives each a meaning by position, with two frozen functions applied
in a fixed order.  `Ty.expand` replaces every `any` by the reading of the
position, and `Ty.expandFresh` turns a `fresh` in the result of an arrow
into an existential.  `expandFresh` copies the arrow's own set into the
bound of that existential, so that set must be read first.  The reading of
a position is `Ctx.reading`: the innermost scope root of the context, or
the program's platform set where the context has no root. -/

/-- A written type read at a context: `any` at the reading of the context,
with `P` the platform set the outermost position reads, then `fresh`. -/
def readAt {s : Sig} (Γ : Ctx s) (P : CaptureSet s) (T : Ty s) : Ty s :=
  (T.expand (Γ.reading P)).expandFresh

/-! ## Tests

Every procedure of this module is structural, so each test below reduces in
the kernel. -/

section Tests

open CapturesCC.DotMNF.Examples (platCtx platSet k1 Z1TyF Z1Ty unitTy fileS)

/-- `{a : ⊤ ^ {}}` at label `trm 0`, a declaration shape. -/
private def fldTop {s : Sig} : Shape s := .fld (Label.trm 0) (Ty.capt [] .top)

/-- The arrow `∀(x : ⊤ ^ {}) ⊤ ^ {}`, at every signature. -/
private def arrTop {s : Sig} : Shape s := .all (Ty.capt [] .top) (.ty (Ty.capt [] .top))

example : tyWf? (Ty.capt [] (.mu fldTop) : Ty []) = true := by decide
/-- A box is not a declaration, so it cannot be the body of a `μ`. -/
example : tyWf? (Ty.capt [] (.mu (.box (Ty.capt [] .top))) : Ty []) = false := by decide
/-- A function shape is not a declaration either. -/
example : shapeWf? (.mu arrTop : Shape []) = false := by decide
/-- A capture member is a declaration and is well formed outright. -/
example : Shape.Wf (.mu (.cap (Label.typ 0) [] [.any]) : Shape []) := by decide
/-- Bad bounds are well formed. -/
example : Shape.Wf (.typ (Label.typ 0) .top .bot : Shape []) := by decide
/-- Well-formedness looks inside a box and inside a field. -/
example : ¬ Ty.Wf (Ty.capt [] (.box (Ty.capt [] (.mu .bot))) : Ty []) := by decide
example : ¬ Shape.Wf (.fld (Label.trm 0) (Ty.capt [] (.mu .bot)) : Shape []) := by decide
/-- An arrow's domain is checked under the arrow's capture binder. -/
example : ¬ Shape.Wf (.all (Ty.capt [.cvar .here] (.mu .bot)) (.ty (Ty.capt [] .top)) :
    Shape []) := by decide
/-- An arrow's codomain is an answer, checked under its binders. -/
example : Shape.Wf (.all (Ty.capt [] .top)
    (.ex [.var .here] (Ty.capt [.cvar .here] (.mu fldTop))) : Shape []) := by decide
example : ¬ Shape.Wf (.all (Ty.capt [] .top)
    (.ex [.var .here] (Ty.capt [.cvar .here] (.mu arrTop))) : Shape []) := by decide
/-- An answer is well formed when the type it holds is, for either former. -/
example : ETy.Wf (.ty (Ty.capt [] arrTop) : ETy []) := by decide
example : eTyWf? (.ex [] (Ty.capt [] (.mu (.box (Ty.capt [] .top)))) : ETy []) = false := by
  decide

example : Defs.Distinct
    (Defs.and (Defs.typ (Label.typ 0) .top) (Defs.cap (Label.typ 1) []) : Defs []) := by
  decide
/-- A capture member and a type member at one label clash. -/
example : ¬ Defs.Distinct
    (Defs.and (Defs.typ (Label.typ 0) .top) (Defs.cap (Label.typ 0) []) : Defs []) := by
  decide
example : defsDistinct?
    (Defs.and (Defs.cap (Label.typ 0) []) (Defs.and (Defs.typ (Label.typ 1) .top)
      (Defs.cap (Label.typ 0) [])) : Defs []) = false := by decide

/-- A literal's shape: equal bounds at a type member and at a capture member. -/
example : (Shape.and (.typ (Label.typ 0) fldTop fldTop)
    (.and (.cap (Label.typ 1) [.any] [.any]) fldTop) : Shape []).LiteralShape := by decide
/-- Unequal bounds are not a literal's shape, at either kind of member. -/
example : literalShape? (.typ (Label.typ 0) .bot .top : Shape []) = false := by decide
example : literalShape? (.cap (Label.typ 0) [] [.any] : Shape []) = false := by decide
/-- A shape that is not a member, or a `μ` of one, is not a literal's shape. -/
example : ¬ (Shape.mu fldTop : Shape []).LiteralShape := by decide
example : literalShape? (.and fldTop .top : Shape []) = false := by decide

/-- Distinct labels across a type member, a capture member and a field. -/
example : (Shape.and (.typ (Label.typ 0) .top .top)
    (.and (.cap (Label.typ 1) [] []) fldTop) : Shape []).DistinctLabels := by decide
/-- A capture member and a type member at one label clash here too. -/
example : distinctLabels? (.and (.typ (Label.typ 0) .top .top) (.cap (Label.typ 0) [] []) :
    Shape []) = false := by decide
/-- Two fields at one label, nested on the right. -/
example : ¬ (Shape.and fldTop (.and (.typ (Label.typ 0) .top .top) fldTop) :
    Shape []).DistinctLabels := by decide
example : distinctLabels? (.top : Shape []) = false := by decide

/-- The capture binder of a platform strengthens past a term binder, and
`any` and `fresh` strengthen to themselves. -/
example : capStrengthen? (s := ([] : Sig),c) (k := .var)
    [.cvar (.there .here), .any, .fresh] = some [.cvar .here, .any, .fresh] := by decide
/-- A set that names the binder does not strengthen, nor does one of its members. -/
example : capStrengthen? (s := ([] : Sig),c) (k := .var) [.var .here] = none := by decide
example : capStrengthen? (s := ([] : Sig),c) (k := .var)
    [.sel .here (Label.typ 0)] = none := by decide
/-- Strengthening past a capture binder. -/
example : capStrengthen? (s := ([] : Sig),x) (k := .cap) [.var (.there .here)]
    = some [.var .here] := by decide
example : capStrengthen? (s := ([] : Sig),x) (k := .cap) [.cvar .here] = none := by decide

example : tyStrengthen? (k := .var) ((Ty.capt [] fldTop : Ty []).weaken)
    = some (Ty.capt [] fldTop) := by decide
example : tyStrengthen? (s := []) (k := .var)
    (Ty.capt [] (.sel (.var .here) (Label.typ 0))) = none := by decide
/-- The set of a type is strengthened too. -/
example : tyStrengthen? (s := []) (k := .var) (Ty.capt [.var .here] .top) = none := by decide
/-- The traversal goes under `μ`, under a box and into a capture member. -/
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.capt [] (.mu (.and
      (.cap (Label.typ 0) [] [.var (.there (.there .here))])
      (.fld (Label.trm 0) (Ty.capt [] (.box (Ty.capt [.var .here] .top)))))))
    = some (Ty.capt [] (.mu (.and
      (.cap (Label.typ 0) [] [.var (.there .here)])
      (.fld (Label.trm 0) (Ty.capt [] (.box (Ty.capt [.var .here] .top))))))) := by
  decide
example : tyStrengthen? (s := ([] : Sig),x) (k := .var)
    (Ty.capt [] (.mu (.cap (Label.typ 0) [] [.var (.there .here)]))) = none := by
  decide
/-- An arrow's domain lives under its capture binder, its codomain under that
binder and the parameter.  Each lifts the strengthening past its own binders. -/
example : shapeStrengthen? (s := ([] : Sig),x) (k := .var)
    (.all (Ty.capt [.cvar .here, .var (.there (.there .here))] .top)
      (.ty (Ty.capt [.var .here, .cvar (.there .here), .var (.there (.there (.there .here)))]
        .top)))
    = some (.all (Ty.capt [.cvar .here, .var (.there .here)] .top)
      (.ty (Ty.capt [.var .here, .cvar (.there .here), .var (.there (.there .here))] .top))) := by
  decide
/-- The parameter of the arrow is not the dropped binder, but the binder
named from the domain is. -/
example : shapeStrengthen? (s := ([] : Sig),x) (k := .var)
    (.all (Ty.capt [.var (.there .here)] .top) (.ty (Ty.capt [] .top))) = none := by decide
/-- An existential lifts past its witness: the witness stays, the binder is dropped. -/
example : eTyStrengthen? (s := ([] : Sig),x) (k := .var)
    (.ex [.var (.there .here)] (Ty.capt [.cvar .here, .var (.there (.there .here))] .top))
    = some (.ex [.var .here] (Ty.capt [.cvar .here, .var (.there .here)] .top)) := by decide
example : eTyStrengthen? (s := ([] : Sig),x) (k := .var)
    (.ex [] (Ty.capt [.var (.there .here)] .top)) = none := by decide
/-- An answer strengthens past a capture binder and a term binder in turn, as
the way out through an unpacking needs. -/
example : ((eTyStrengthen? (s := ([] : Sig),c,c) (k := .var)
    (.ty (Ty.capt [.cvar (.there (.there .here))] .top))).bind
      (eTyStrengthen? (k := .cap))) = some (.ty (Ty.capt [.cvar .here] .top)) := by decide
example : (tyStrengthenW? (k := .var) ((Ty.capt [] fldTop : Ty []).weaken)).isSome = true := by
  decide
example : (tyStrengthenW? (k := .cap) ((Ty.capt [] arrTop : Ty []).weaken)).isSome = true := by
  decide
example : (eTyStrengthenW? (k := .cap)
    ((.ex [] (Ty.capt [.cvar .here] arrTop) : ETy []).weaken)).isSome = true := by decide

example : capJoin ([.any, .any] : CaptureSet []) [.any] = [.any, .any] := by decide
example : capJoin ([] : CaptureSet (([] : Sig),x)) [.var .here, .var .here] =
    [.var .here, .var .here] := by decide
example : capJoin ([.cvar (.there .here)] : CaptureSet (([] : Sig),c,x))
    [.var .here, .cvar (.there .here)] = [.cvar (.there .here), .var .here] := by decide
example : capJoinAll ([[.var .here], [.var .here, .fresh], []] : List (CaptureSet (([] : Sig),x)))
    = [.var .here, .fresh] := by decide

/-- `All-I`: the binder is dropped, the platform capability kept. -/
example : capDropHere? noSel ([.var .here, .cvar (.there .here)] : CaptureSet (([] : Sig),c,x))
    = some [.cvar .here] := by decide
/-- A member of the binder with no known bound blocks the candidate. -/
example : capDropHere? noSel ([.sel .here (Label.typ 0)] : CaptureSet (([] : Sig),c,x))
    = none := by decide
/-- A member of the binder is read at its upper bound. -/
example : capDropHere? (fun _ => some [.cvar (.there .here)])
    ([.sel .here (Label.typ 0)] : CaptureSet (([] : Sig),c,x)) = some [.cvar .here] := by decide
/-- `let`: `{x}` is replaced by the set of the bound term's type, without repetition. -/
example : capAvoid? [.cvar (.there .here)] noSel
    ([.var .here, .cvar (.there .here)] : CaptureSet (([] : Sig),c,x)) = some [.cvar .here] := by
  decide
/-- An upper bound that names the binder itself does not avoid it. -/
example : capAvoid? [] (fun _ => some [.var .here])
    ([.sel .here (Label.typ 0)] : CaptureSet (([] : Sig),x)) = none := by decide

/-- A lambda body over a platform: two capabilities, the body root, the
arrow's binder and the parameter.  Only the parameter is a term variable. -/
example : ctxVars (Ctx.body platCtx (Ty.capt [] .top)) = [.here] := by decide
example : ctxCaps (Ctx.body platCtx (Ty.capt [] .top))
    = [.there .here, .there (.there .here), .there (.there (.there .here)),
      .there (.there (.there (.there .here)))] := by decide
/-- An object body under a pack's scope: the self is a term variable, the
class root and the witness are capture binders. -/
example : ctxVars (Ctx.objBody (Ctx.scopeInst (Ctx.cons Ctx.nil (Ty.capt [] .top)) [.var .here])
    (Defs.typ (Label.typ 0) .top) (.typ (Label.typ 0) .top .top) [])
    = [.here, .there (.there (.there (.there .here)))] := by decide
example : ctxCaps (Ctx.objBody (Ctx.scopeInst (Ctx.cons Ctx.nil (Ty.capt [] .top)) [.var .here])
    (Defs.typ (Label.typ 0) .top) (.typ (Label.typ 0) .top .top) [])
    = [.there .here, .there (.there .here), .there (.there (.there .here))] := by decide

/-- `freshCell` written with `fresh`, read at the top of its program: no
`any` to read, and the result `fresh` becomes the existential the version
writes. -/
example : readAt platCtx platSet (Z1TyF k1) = Z1Ty k1 := by decide
/-- At the top of a program `any` reads as the platform set. -/
example : readAt platCtx platSet (Ty.capt [.any] fileS) = Ty.capt platSet fileS := by decide
/-- In a lambda body `any` reads as the body's root.  A parameter `any` reads
as the arrow's own binder, whatever the context. -/
example : readAt (Ctx.body platCtx unitTy) (CaptureSet.weaken (CaptureSet.weaken
      (CaptureSet.weaken platSet)))
    (Ty.capt [.any] (.all (Ty.capt [.any] .top) (.ty (Ty.capt [.any] .top))))
    = Ty.capt [.cvar (.there (.there .here))]
      (.all (Ty.capt [.cvar .here] .top)
        (.ty (Ty.capt [.cvar (.there (.there (.there (.there .here))))] .top))) := by decide
/-- The order is the version's: the arrow's set is read before `fresh` copies
it into the bound of the existential. -/
example : readAt platCtx platSet
    (Ty.capt [.any] (.all (Ty.capt [] .top) (.ty (Ty.capt [.fresh] fileS))))
    = Ty.capt platSet (.all (Ty.capt [] .top)
        (.ex [.cvar (.there (.there (.there .here))), .cvar (.there (.there .here)), .var .here]
          (Ty.capt [.cvar .here] fileS))) := by decide

end Tests

end CapturesCCFrontend
