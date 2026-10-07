import Coercions.Captures.DotMNF.Typing
import Coercions.Captures.FCdot.Checker

/-!
# The decided side conditions

The typer of this front end discharges four kinds of side condition by
decision procedures, and computes capture sets by a few total functions.

- Well-formedness of a shape and of a type, `shapeWf?` and `tyWf?`.  The
  only premise of `Shape.Wf` that is not structural is the `Shape.Decl` of
  `Wf.mu`, which the frozen `Shape.isDecl` already decides.
- Distinctness of the labels of a definition block, `defsDistinct?`, over
  the three definition kinds by the frozen `Defs.labels`.
- Strengthening, the inverse of weakening, over capture sets, shapes and
  types.  The avoidance ladder of the typer climbs it.
- `capJoin`, the union of two capture sets without repeated atoms, and the
  candidate sets a binder leaves behind when it goes out of scope.

Strengthening reuses the target's partial renaming as it stands:
`PartialRename`, `PartialRename.lift`, `PartialRename.unshift`, `Inverts`,
`Inverts.lift`, `unshift_inverts` and `witness?` of
`lean/Coercions/Captures/FCdot/Checker.lean`.  That machinery is generic over
`Sig`, `Kind` and `BVar`, which the two calculi share.  Only the traversals
over the source's capture atoms, shapes and types are new.  They copy the
shape of the target's own `rename?` functions.

A candidate set is never trusted.  The typer follows each one with evidence,
a decided inclusion or a subcapturing derivation from the search, so the
functions that compute candidates carry no lemma.

Every name here is a plain name in `namespace CapturesFrontend`, never a
member of a namespace of the version, so the functions are written as
applications and not with dot notation.  Every recursive definition says
`termination_by structural`, so all of this reduces in the kernel and the
tests at the end are `by decide`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx)

/-! ## Well-formedness of shapes and types

`shapeWf?` mirrors `Shape.Wf` clause for clause.  A capture member is well
formed outright, a box is well formed when the type inside it is, and a
type when its shape is.  `Wf.typ` relates its two bounds not at all, so
`{A : ⊤..⊥}` is well formed. -/

mutual
/-- The decision procedure for `Shape.Wf`. -/
def shapeWf? {s : Sig} (S : Shape s) : Bool :=
  match S with
  | .top | .bot | .sel _ _ | .cap _ _ _ => true
  | .typ _ S T => shapeWf? S && shapeWf? T
  | .fld _ T => tyWf? T
  | .mu S => shapeWf? S && S.isDecl
  | .all T U => tyWf? T && tyWf? U
  | .and S T => shapeWf? S && shapeWf? T
  | .box T => tyWf? T
termination_by structural S
/-- The decision procedure for `Ty.Wf`. -/
def tyWf? {s : Sig} (T : Ty s) : Bool :=
  match T with
  | .capt _ S => shapeWf? S
termination_by structural T
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
        exact .all ((tyWf?_iff T).mp h.1) ((tyWf?_iff U).mp h.2),
       fun h => by
        cases h with
        | all hT hU =>
            simp only [shapeWf?, Bool.and_eq_true]
            exact ⟨(tyWf?_iff T).mpr hT, (tyWf?_iff U).mpr hU⟩⟩
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
end

instance instDecidableShapeWf {s : Sig} (S : Shape s) : Decidable (Shape.Wf S) :=
  decidable_of_iff _ (shapeWf?_iff S)

instance instDecidableTyWf {s : Sig} (T : Ty s) : Decidable (Ty.Wf T) :=
  decidable_of_iff _ (tyWf?_iff T)

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

/-! ## Partial renaming of capture sets, paths, shapes and types

Each traversal fails exactly when some variable it meets is outside the
domain of the renaming.  `any` holds no variable and is mapped to itself, as
`CapAtom.rename` maps it.  Soundness and completeness are stated against a
total renaming the partial one inverts, as the target states its own. -/

/-- A capture atom under a partial renaming. -/
def capAtomRename? {s1 s2 : Sig} : CapAtom s1 → PartialRename s1 s2 → Option (CapAtom s2)
  | .var x, ρ => (ρ.var x).map .var
  | .cvar κ, ρ => (ρ.var κ).map .cvar
  | .sel x ℓ, ρ => (ρ.var x).map (fun y => .sel y ℓ)
  | .any, _ => some .any

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
      match tyRename? T ρ, tyRename? U ρ.lift with
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
      rw [tyRename?_complete T ρ σ h, tyRename?_complete U ρ.lift σ.lift h.lift]
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
      cases hT : tyRename? T ρ with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        cases hV : tyRename? V ρ.lift with
        | none => rw [hT, hV] at hU; simp at hU
        | some V' =>
          rw [hT, hV] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← tyRename?_sound T T' ρ σ h hT, ← tyRename?_sound V V' ρ.lift σ.lift h.lift hV]
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
end

/-! ## Strengthening

Strengthening is the action of `PartialRename.unshift`, the partial inverse
of `Rename.succ`.  It undoes one weakening exactly when the innermost binder
does not occur.  The binder may be of either kind: the avoidance ladder
strengthens past a term binder, and a capture binder of the platform is
passed the same way. -/

/-- Undo one weakening of a capture set. -/
def capStrengthen? {s : Sig} {k : Kind} (C : CaptureSet (s,,k)) : Option (CaptureSet s) :=
  capRename? C PartialRename.unshift

/-- Undo one weakening of a shape. -/
def shapeStrengthen? {s : Sig} {k : Kind} (S : Shape (s,,k)) : Option (Shape s) :=
  shapeRename? S PartialRename.unshift

/-- Undo one weakening of a type. -/
def tyStrengthen? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option (Ty s) :=
  tyRename? T PartialRename.unshift

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
  simp only [capStrengthenW?, Captures.FCdot.witness?_eq_some (capStrengthen?_weaken (k := k) D)]

/-- Strengthening of a shape, carrying the equation it establishes. -/
def shapeStrengthenW? {s : Sig} {k : Kind} (S : Shape (s,,k)) :
    Option { U : Shape s // S = U.weaken } :=
  match witness? (shapeStrengthen? S) with
  | some ⟨U, hU⟩ => some ⟨U, shapeStrengthen?_sound hU⟩
  | none => none

theorem shapeStrengthenW?_weaken {s : Sig} {k : Kind} (U : Shape s) :
    shapeStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [shapeStrengthenW?,
    Captures.FCdot.witness?_eq_some (shapeStrengthen?_weaken (k := k) U)]

/-- Strengthening of a type, carrying the equation it establishes. -/
def tyStrengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U.weaken } :=
  match witness? (tyStrengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, tyStrengthen?_sound hU⟩
  | none => none

theorem tyStrengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    tyStrengthenW? (U.weaken (k := k)) = some ⟨U, rfl⟩ := by
  simp only [tyStrengthenW?, Captures.FCdot.witness?_eq_some (tyStrengthen?_weaken (k := k) U)]

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

/-! ## The variables of a context

`Ctx` has four constructors.  `consSelf`, the binder of an object literal, is
a term binder like `cons`, so its variable is in the list.  `consC`, a
capture binder of the platform, binds no term variable, so it only shifts
the ones below it. -/

/-- Every term variable of a context, newest binder first. -/
def ctxVars {s : Sig} (Γ : Ctx s) : List (BVar s .var) :=
  match Γ with
  | .nil => []
  | .cons Γ _ => .here :: (ctxVars Γ).map .there
  | .consSelf Γ _ _ _ => .here :: (ctxVars Γ).map .there
  | .consC Γ => (ctxVars Γ).map .there
termination_by structural Γ

/-- Every capture binder of a context, newest binder first. -/
def ctxCaps {s : Sig} (Γ : Ctx s) : List (BVar s .cap) :=
  match Γ with
  | .nil => []
  | .cons Γ _ => (ctxCaps Γ).map .there
  | .consSelf Γ _ _ _ => (ctxCaps Γ).map .there
  | .consC Γ => .here :: (ctxCaps Γ).map .there
termination_by structural Γ

/-! ## Tests

Every procedure of this module is structural, so each test below reduces in
the kernel. -/

section Tests

/-- `{a : ⊤ ^ {}}` at label `trm 0`, a declaration shape. -/
private def fldTop {s : Sig} : Shape s := .fld (Label.trm 0) (Ty.capt [] .top)

example : tyWf? (Ty.capt [] (.mu fldTop) : Ty []) = true := by decide
/-- A box is not a declaration, so it cannot be the body of a `μ`. -/
example : tyWf? (Ty.capt [] (.mu (.box (Ty.capt [] .top))) : Ty []) = false := by decide
/-- A function shape is not a declaration either. -/
example : shapeWf? (.mu (.all (Ty.capt [] .top) (Ty.capt [] .top)) : Shape []) = false := by
  decide
/-- A capture member is a declaration and is well formed outright. -/
example : Shape.Wf (.mu (.cap (Label.typ 0) [] [.any]) : Shape []) := by decide
/-- Bad bounds are well formed. -/
example : Shape.Wf (.typ (Label.typ 0) .top .bot : Shape []) := by decide
/-- Well-formedness looks inside a box and inside a field. -/
example : ¬ Ty.Wf (Ty.capt [] (.box (Ty.capt [] (.mu .bot))) : Ty []) := by decide
example : ¬ Shape.Wf (.fld (Label.trm 0) (Ty.capt [] (.mu .bot)) : Shape []) := by decide

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

/-- The capture binder of a platform strengthens past a term binder. -/
example : capStrengthen? (s := ([] : Sig),c) (k := .var)
    [.cvar (.there .here), .any] = some [.cvar .here, .any] := by decide
/-- A set that names the binder does not strengthen, nor does one of its members. -/
example : capStrengthen? (s := ([] : Sig),c) (k := .var) [.var .here] = none := by decide
example : capStrengthen? (s := ([] : Sig),c) (k := .var)
    [.sel .here (Label.typ 0)] = none := by decide
/-- Strengthening past a capture binder. -/
example : capStrengthen? (s := ([] : Sig),x) (k := .cap) [.var (.there .here)]
    = some [.var .here] := by decide

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
/-- The codomain of a function lives under its parameter. -/
example : shapeStrengthen? (s := ([] : Sig),x) (k := .var)
    (.all (Ty.capt [.var (.there .here)] .top) (Ty.capt [.var .here, .var (.there (.there .here))] .top))
    = some (.all (Ty.capt [.var .here] .top) (Ty.capt [.var .here, .var (.there .here)] .top)) := by
  decide
example : (tyStrengthenW? (k := .var) ((Ty.capt [] fldTop : Ty []).weaken)).isSome = true := by
  decide

example : capJoin ([.any, .any] : CaptureSet []) [.any] = [.any, .any] := by decide
example : capJoin ([] : CaptureSet (([] : Sig),x)) [.var .here, .var .here] =
    [.var .here, .var .here] := by decide
example : capJoin ([.cvar (.there .here)] : CaptureSet (([] : Sig),c,x))
    [.var .here, .cvar (.there .here)] = [.cvar (.there .here), .var .here] := by decide
example : capJoinAll ([[.var .here], [.var .here, .any], []] : List (CaptureSet (([] : Sig),x)))
    = [.var .here, .any] := by decide

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

/-- The self binder of an object literal is a term variable, a capture binder is not. -/
example : ctxVars (Ctx.consSelf (Ctx.consC (Ctx.cons Ctx.nil (Ty.capt [] .top)))
    (Defs.typ (Label.typ 0) .top) .top [])
    = [.here, .there (.there .here)] := by decide
example : ctxCaps (Ctx.consSelf (Ctx.consC (Ctx.cons Ctx.nil (Ty.capt [] .top)))
    (Defs.typ (Label.typ 0) .top) .top [])
    = [.there .here] := by decide

end Tests

end CapturesFrontend
