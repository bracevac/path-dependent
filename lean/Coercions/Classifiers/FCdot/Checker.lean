import Coercions.Classifiers.FCdot.Typing

namespace Classifiers

/-!
# Executable structural checker for FCdot

The checker validates fully annotated evidence.  It never searches: every
directed step, and every field-presence proof, is already present in the
input.

Since `ShapeCo.obj` carries its source telescope, `ShapeCo.pair` and
`Atom.both` their target telescopes, and `Atom.foldSelf` its target
telescope, *every* judgement of the evidence layer synthesises its outputs.
A template `le pre h post` of a morphism is checked from its hole outwards:
the hole is read in the source telescope (`Hole.read?`), then each side is
checked against the endpoint next to the hole and synthesises the outer
endpoint.  The kernel is therefore a family of synthesising cores; the
checking modes are synthesis followed by a decidable comparison.

The capture family is synthesising too: `synthCap` returns the two capture
sets and decides the one syntactic inclusion, `CapCo.elem`.

The kernels return the typing derivation itself, so soundness holds by
construction.  Completeness lives in
`Coercions.Classifiers.FCdot.CheckerCompleteness`.
-/

namespace FCdot

/-! ## Telescope lookup

`Telescope.At` is the typing-side relation; `Telescope.get?` is its
executable counterpart. -/

theorem Telescope.At.lt_length {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P) : i < Tel.length := by
  induction h with
  | here => exact Nat.lt_succ_self _
  | there _ ih => exact Nat.lt_succ_of_lt ih

theorem Telescope.get?_At_mp {s : Sig} : ∀ (Tel : Telescope s) {i : Nat} {P : Proposition s},
    Tel.get? i = some P → Tel.At i P
  | .nil, _, _, h => by simp [Telescope.get?] at h
  | .cons Tel Q, i, P, h => by
      simp only [Telescope.get?] at h
      by_cases hi : i = Tel.length
      · subst hi
        rw [if_pos rfl] at h
        cases h
        exact .here
      · rw [if_neg hi] at h
        exact .there (Telescope.get?_At_mp Tel h)

theorem Telescope.get?_At_mpr {s : Sig} {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P) : Tel.get? i = some P := by
  induction h with
  | here => simp [Telescope.get?]
  | @there Tel i P Q hAt ih =>
      have hne : i ≠ Tel.length := Nat.ne_of_lt hAt.lt_length
      simp only [Telescope.get?, if_neg hne]
      exact ih

theorem Telescope.get?_At {Tel : Telescope s} {i : Nat} {P : Proposition s} :
    Tel.get? i = some P ↔ Tel.At i P :=
  ⟨Telescope.get?_At_mp Tel, Telescope.get?_At_mpr⟩

/-- Executable lookup and the `At` relation agree. -/
theorem Telescope.get?_eq_some_iff_At {Tel : Telescope s} {i : Nat} {P : Proposition s} :
    Tel.get? i = some P ↔ Tel.At i P :=
  Telescope.get?_At

/-! ### Lookups that carry their own evidence

The kernel needs the `At` proof, not just the proposition, so the executable
lookups below return a subtype.  Because they are defined by recursion on the
telescope — not through an auxiliary equation — they reduce definitionally,
which is what makes the completeness proofs one-liners. -/

/-- Indexed lookup, returning the membership proof. -/
def Telescope.getAt? : (Tel : Telescope s) → (i : Nat) → Option { P : Proposition s // Tel.At i P }
  | .nil, _ => none
  | .cons Tel P, i =>
      if h : i = Tel.length then some ⟨P, by rw [h]; exact .here⟩
      else
        match Telescope.getAt? Tel i with
        | some ⟨Q, hQ⟩ => some ⟨Q, .there hQ⟩
        | none => none

theorem Telescope.getAt?_of_At : ∀ {s : Sig} {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P), Tel.getAt? i = some ⟨P, h⟩
  | _, _, _, _, .here => by simp [Telescope.getAt?]
  | _, .cons Tel Q, i, P, .there hAt => by
      have hne : i ≠ Tel.length := Nat.ne_of_lt hAt.lt_length
      simp only [Telescope.getAt?, dif_neg hne, Telescope.getAt?_of_At hAt]

/-- `getAt?` refines `get?`: same lookup, with the membership proof attached. -/
theorem Telescope.getAt?_map_val : ∀ {s : Sig} (Tel : Telescope s) (i : Nat),
    (Tel.getAt? i).map Subtype.val = Tel.get? i
  | _, .nil, _ => rfl
  | _, .cons Tel P, i => by
      simp only [Telescope.getAt?, Telescope.get?]
      by_cases h : i = Tel.length
      · simp [h]
      · simp only [dif_neg h, if_neg h]
        rw [← Telescope.getAt?_map_val Tel i]
        cases Tel.getAt? i <;> simp

/-- First index carrying a given proposition, with the membership proof. -/
def Telescope.findAt? : (Tel : Telescope s) → (P : Proposition s) → Option { i : Nat // Tel.At i P }
  | .nil, _ => none
  | .cons Tel Q, P =>
      if h : Q = P then some ⟨Tel.length, by subst h; exact .here⟩
      else
        match Telescope.findAt? Tel P with
        | some ⟨i, hi⟩ => some ⟨i, .there hi⟩
        | none => none

/-- Attach the defining equation to a lookup result. -/
def witness? {α : Type} : (o : Option α) → Option { a : α // o = some a }
  | some a => some ⟨a, rfl⟩
  | none => none

@[simp] theorem witness?_some {α : Type} (a : α) : witness? (some a) = some ⟨a, rfl⟩ := rfl

@[simp] theorem witness?_none {α : Type} : witness? (none : Option α) = none := rfl

theorem witness?_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    witness? o = some ⟨a, h⟩ := by subst h; rfl

/-! ## Strengthening of shapes and types

`Shape.strengthen?` and `Ty.strengthen?` invert `weaken`.  Both are the
action of a partial renaming, which is what makes the traversal under
binders work. -/

/-- A renaming that may fail on some variables. -/
structure PartialRename (s1 s2 : Sig) where
  var : ∀ {k}, BVar s1 k → Option (BVar s2 k)

namespace PartialRename

def lift (ρ : PartialRename s1 s2) {k : Kind} : PartialRename (s1,,k) (s2,,k) where
  var := fun
    | .here => some .here
    | .there x => (ρ.var x).map .there

/-- The partial inverse of `Rename.succ`: drops the innermost binder. -/
def unshift {s : Sig} {k : Kind} : PartialRename (s,,k) s where
  var := fun
    | .here => none
    | .there x => some x

@[simp] theorem lift_here (ρ : PartialRename s1 s2) {k : Kind} :
    (ρ.lift (k := k)).var .here = some .here := rfl

@[simp] theorem lift_there (ρ : PartialRename s1 s2) {k k0 : Kind} (x : BVar s1 k) :
    (ρ.lift (k := k0)).var (.there x) = (ρ.var x).map .there := rfl

@[simp] theorem unshift_here {s : Sig} {k : Kind} :
    (unshift (s := s) (k := k)).var .here = none := rfl

@[simp] theorem unshift_there {s : Sig} {k k0 : Kind} (x : BVar s k) :
    (unshift (s := s) (k := k0)).var (.there x) = some x := rfl

/-- `ρ` is the partial inverse of the total renaming `σ`. -/
def Inverts (ρ : PartialRename s1 s2) (σ : Rename s2 s1) : Prop :=
  ∀ {k} (x : BVar s1 k) (y : BVar s2 k), ρ.var x = some y ↔ x = σ.var y

theorem Inverts.lift {ρ : PartialRename s1 s2} {σ : Rename s2 s1} (h : Inverts ρ σ)
    {k : Kind} : Inverts (ρ.lift (k := k)) (σ.lift) := by
  intro k' x y
  cases x with
  | here =>
      cases y with
      | here => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | there y => simp only [lift_here, Rename.lift_there]; simp
  | there x =>
      cases y with
      | here =>
          simp only [lift_there, Rename.lift_here]
          cases hxx : ρ.var x with
          | none => simp
          | some z => simp
      | there y =>
          simp only [lift_there, Rename.lift_there, BVar.there.injEq]
          cases hxx : ρ.var x with
          | none =>
              simp only [Option.map_none, reduceCtorEq, false_iff]
              intro hxy
              have := (h x y).mpr hxy
              rw [hxx] at this
              simp at this
          | some z =>
              simp only [Option.map_some, Option.some.injEq, BVar.there.injEq]
              constructor
              · intro hzy; subst hzy; exact (h x z).mp hxx
              · intro hxy
                have := (h x y).mpr hxy
                rw [hxx] at this
                simpa using this

theorem unshift_inverts {s : Sig} {k : Kind} :
    Inverts (unshift (s := s) (k := k)) Rename.succ := by
  intro k' x y
  cases x with
  | here => simp only [unshift_here, Rename.succ_var]; simp
  | there x => simp only [unshift_there, Rename.succ_var, Option.some.injEq, BVar.there.injEq]

end PartialRename

/-! ### Partial renaming of capture sets -/

def CapAtom.rename? : CapAtom s1 → PartialRename s1 s2 → Option (CapAtom s2)
  | .var x, ρ => (ρ.var x).map .var
  | .cvar κ, ρ => (ρ.var κ).map .cvar
  | .name x ℓ, ρ => (ρ.var x).map (fun y => .name y ℓ)
  -- the universal root is a constant, so it survives every partial renaming
  | .top, _ => some .top
  -- a kind mentions no binder, so a projection renames where its base does
  | .proj a φ, ρ => (a.rename? ρ).map (CapAtom.proj · φ)

def CaptureSet.rename? : CaptureSet s1 → PartialRename s1 s2 → Option (CaptureSet s2)
  | [], _ => some []
  | a :: C, ρ =>
      match a.rename? ρ, CaptureSet.rename? C ρ with
      | some a', some C' => some (a' :: C')
      | _, _ => none

theorem CapAtom.rename?_complete :
    ∀ {s1 s2 : Sig} (a : CapAtom s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (a.rename σ).rename? ρ = some a
  | _, _, .var x, ρ, σ, h => by
      simp only [CapAtom.rename, CapAtom.rename?]
      rw [(h (σ.var x) x).mpr rfl]; rfl
  | _, _, .cvar κ, ρ, σ, h => by
      simp only [CapAtom.rename, CapAtom.rename?]
      rw [(h (σ.var κ) κ).mpr rfl]; rfl
  | _, _, .name x ℓ, ρ, σ, h => by
      simp only [CapAtom.rename, CapAtom.rename?]
      rw [(h (σ.var x) x).mpr rfl]; rfl
  | _, _, .top, _, _, _ => rfl
  | _, _, .proj a φ, ρ, σ, h => by
      simp only [CapAtom.rename, CapAtom.rename?,
        CapAtom.rename?_complete a ρ σ h, Option.map_some]

theorem CaptureSet.rename?_complete :
    ∀ {s1 s2 : Sig} (C : CaptureSet s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → CaptureSet.rename? (CaptureSet.rename C σ) ρ = some C
  | _, _, [], _, _, _ => rfl
  | _, _, a :: C, ρ, σ, h => by
      show CaptureSet.rename? ((a.rename σ) :: (CaptureSet.rename C σ)) ρ = _
      simp only [CaptureSet.rename?, CapAtom.rename?_complete a ρ σ h,
        CaptureSet.rename?_complete C ρ σ h]

theorem CapAtom.rename?_sound :
    ∀ {s1 s2 : Sig} (a : CapAtom s1) (b : CapAtom s2) (ρ : PartialRename s1 s2)
      (σ : Rename s2 s1), ρ.Inverts σ → a.rename? ρ = some b → a = b.rename σ
  | _, _, .var x, b, ρ, σ, h, hb => by
      simp only [CapAtom.rename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h x y).mp hy]
  | _, _, .cvar x, b, ρ, σ, h, hb => by
      simp only [CapAtom.rename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h x y).mp hy]
  | _, _, .name x ℓ, b, ρ, σ, h, hb => by
      simp only [CapAtom.rename?, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [(h x y).mp hy]
  | _, _, .top, b, ρ, σ, h, hb => by
      simp only [CapAtom.rename?, Option.some.injEq] at hb
      subst hb
      rfl
  | _, _, .proj a φ, b, ρ, σ, h, hb => by
      simp only [CapAtom.rename?, Option.map_eq_some_iff] at hb
      obtain ⟨c, hc, hb⟩ := hb
      subst hb
      simp only [CapAtom.rename]
      rw [← CapAtom.rename?_sound a c ρ σ h hc]

theorem CaptureSet.rename?_sound :
    ∀ {s1 s2 : Sig} (C : CaptureSet s1) (D : CaptureSet s2) (ρ : PartialRename s1 s2)
      (σ : Rename s2 s1), ρ.Inverts σ → CaptureSet.rename? C ρ = some D →
        C = CaptureSet.rename D σ
  | _, _, [], D, _, _, _, hD => by
      simp only [CaptureSet.rename?, Option.some.injEq] at hD
      subst hD; rfl
  | _, _, a :: C, D, ρ, σ, h, hD => by
      simp only [CaptureSet.rename?] at hD
      cases ha : a.rename? ρ with
      | none => rw [ha] at hD; simp at hD
      | some b =>
        cases hC : CaptureSet.rename? C ρ with
        | none => rw [ha, hC] at hD; simp at hD
        | some D' =>
          rw [ha, hC] at hD
          simp only [Option.some.injEq] at hD
          subst hD
          show a :: C = (b :: D').map (fun c => c.rename σ)
          rw [List.map_cons, ← CapAtom.rename?_sound a b ρ σ h ha]
          have hCD : C = CaptureSet.rename D' σ := CaptureSet.rename?_sound C D' ρ σ h hC
          rw [hCD]
          rfl

/-! ### Partial renaming of shapes, types, propositions, telescopes -/

mutual

def Shape.rename? : Shape s1 → PartialRename s1 s2 → Option (Shape s2)
  | .bot, _ => some .bot
  | .sel x ℓ, ρ => (ρ.var x).map (fun y => .sel y ℓ)
  | .pi S T, ρ =>
      match S.rename? ρ.lift, T.rename? ρ.lift.lift with
      | some S', some T' => some (.pi S' T')
      | _, _ => none
  | .obj Tel, ρ =>
      match Tel.rename? ρ.lift with
      | some Tel' => some (.obj Tel')
      | none => none
  | .box T, ρ =>
      match T.rename? ρ with
      | some T' => some (.box T')
      | none => none

def Ty.rename? : Ty s1 → PartialRename s1 s2 → Option (Ty s2)
  | .capt C S, ρ =>
      match C.rename? ρ, S.rename? ρ with
      | some C', some S' => some (.capt C' S')
      | _, _ => none

def ETy.rename? : ETy s1 → PartialRename s1 s2 → Option (ETy s2)
  | .ty T, ρ =>
      match T.rename? ρ with
      | some T' => some (.ty T')
      | none => none
  | .ex C T, ρ =>
      match C.rename? ρ, T.rename? ρ.lift with
      | some C', some T' => some (.ex C' T')
      | _, _ => none

def Proposition.rename? : Proposition s1 → PartialRename s1 s2 → Option (Proposition s2)
  | .le S T, ρ =>
      match S.rename? ρ, T.rename? ρ with
      | some S', some T' => some (.le S' T')
      | _, _ => none
  | .eq S T, ρ =>
      match S.rename? ρ, T.rename? ρ with
      | some S', some T' => some (.eq S' T')
      | _, _ => none
  | .has ℓ, _ => some (.has ℓ)
  | .bnd T, ρ =>
      match T.rename? ρ with
      | some T' => some (.bnd T')
      | none => none
  | .leC C D, ρ =>
      match C.rename? ρ, D.rename? ρ with
      | some C', some D' => some (.leC C' D')
      | _, _ => none
  | .eqC C D, ρ =>
      match C.rename? ρ, D.rename? ρ with
      | some C', some D' => some (.eqC C' D')
      | _, _ => none
  | .kindC C φ, ρ =>
      match C.rename? ρ with
      | some C' => some (.kindC C' φ)
      | none => none

def Telescope.rename? : Telescope s1 → PartialRename s1 s2 → Option (Telescope s2)
  | .nil, _ => some .nil
  | .cons Tel P, ρ =>
      match Tel.rename? ρ, P.rename? ρ with
      | some Tel', some P' => some (.cons Tel' P')
      | _, _ => none

end

mutual

theorem Shape.rename?_complete :
    ∀ {s1 s2 : Sig} (U : Shape s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (U.rename σ).rename? ρ = some U
  | _, _, .bot, _, _, _ => by simp [Shape.rename, Shape.rename?]
  | _, _, .sel x ℓ, ρ, σ, h => by
      simp only [Shape.rename, Shape.rename?]
      rw [(h (σ.var x) x).mpr rfl]
      rfl
  | _, _, .pi S T, ρ, σ, h => by
      simp only [Shape.rename, Shape.rename?]
      rw [Ty.rename?_complete S ρ.lift σ.lift h.lift,
        ETy.rename?_complete T ρ.lift.lift σ.lift.lift
          (PartialRename.Inverts.lift (PartialRename.Inverts.lift h))]
  | _, _, .obj Tel, ρ, σ, h => by
      simp only [Shape.rename, Shape.rename?]
      rw [Telescope.rename?_complete Tel ρ.lift σ.lift h.lift]
  | _, _, .box T, ρ, σ, h => by
      simp only [Shape.rename, Shape.rename?]
      rw [Ty.rename?_complete T ρ σ h]

theorem Ty.rename?_complete :
    ∀ {s1 s2 : Sig} (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (U.rename σ).rename? ρ = some U
  | _, _, .capt C S, ρ, σ, h => by
      simp only [Ty.rename, Ty.rename?]
      rw [CaptureSet.rename?_complete C ρ σ h, Shape.rename?_complete S ρ σ h]

theorem ETy.rename?_complete :
    ∀ {s1 s2 : Sig} (E : ETy s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (E.rename σ).rename? ρ = some E
  | _, _, .ty T, ρ, σ, h => by
      simp only [ETy.rename, ETy.rename?]
      rw [Ty.rename?_complete T ρ σ h]
  | _, _, .ex C T, ρ, σ, h => by
      simp only [ETy.rename, ETy.rename?]
      rw [CaptureSet.rename?_complete C ρ σ h, Ty.rename?_complete T ρ.lift σ.lift h.lift]

theorem Proposition.rename?_complete :
    ∀ {s1 s2 : Sig} (P : Proposition s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (P.rename σ).rename? ρ = some P
  | _, _, .le S T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Shape.rename?_complete S ρ σ h, Shape.rename?_complete T ρ σ h]
  | _, _, .eq S T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Shape.rename?_complete S ρ σ h, Shape.rename?_complete T ρ σ h]
  | _, _, .has ℓ, _, _, _ => by simp [Proposition.rename, Proposition.rename?]
  | _, _, .bnd T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Shape.rename?_complete T ρ σ h]
  | _, _, .leC C D, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [CaptureSet.rename?_complete C ρ σ h, CaptureSet.rename?_complete D ρ σ h]
  | _, _, .eqC C D, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [CaptureSet.rename?_complete C ρ σ h, CaptureSet.rename?_complete D ρ σ h]
  | _, _, .kindC C φ, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [CaptureSet.rename?_complete C ρ σ h]

theorem Telescope.rename?_complete :
    ∀ {s1 s2 : Sig} (Tel : Telescope s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (Tel.rename σ).rename? ρ = some Tel
  | _, _, .nil, _, _, _ => by simp [Telescope.rename, Telescope.rename?]
  | _, _, .cons Tel P, ρ, σ, h => by
      simp only [Telescope.rename, Telescope.rename?]
      rw [Telescope.rename?_complete Tel ρ σ h, Proposition.rename?_complete P ρ σ h]

end


mutual

theorem Shape.rename?_sound :
    ∀ {s1 s2 : Sig} (T : Shape s1) (U : Shape s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → T.rename? ρ = some U → T = U.rename σ
  | _, _, .bot, U, _, _, _, hU => by
      simp only [Shape.rename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .sel x ℓ, U, ρ, σ, h, hU => by
      simp only [Shape.rename?, Option.map_eq_some_iff] at hU
      obtain ⟨y, hy, hU⟩ := hU
      subst hU
      simp only [Shape.rename]
      rw [(h x y).mp hy]
  | _, _, .pi S T, U, ρ, σ, h, hU => by
      simp only [Shape.rename?] at hU
      cases hS : S.rename? ρ.lift with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : T.rename? ρ.lift.lift with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Shape.rename]
          rw [← Ty.rename?_sound S S' ρ.lift σ.lift h.lift hS,
            ← ETy.rename?_sound T T' ρ.lift.lift σ.lift.lift
              (PartialRename.Inverts.lift (PartialRename.Inverts.lift h)) hT]
  | _, _, .obj Tel, U, ρ, σ, h, hU => by
      simp only [Shape.rename?] at hU
      cases hTel : Tel.rename? ρ.lift with
      | none => rw [hTel] at hU; simp at hU
      | some Tel' =>
        rw [hTel] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Shape.rename]
        rw [← Telescope.rename?_sound Tel Tel' ρ.lift σ.lift h.lift hTel]
  | _, _, .box T, U, ρ, σ, h, hU => by
      simp only [Shape.rename?] at hU
      cases hT : T.rename? ρ with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
        rw [hT] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Shape.rename]
        rw [← Ty.rename?_sound T T' ρ σ h hT]

theorem Ty.rename?_sound :
    ∀ {s1 s2 : Sig} (T : Ty s1) (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → T.rename? ρ = some U → T = U.rename σ
  | _, _, .capt C S, U, ρ, σ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hC : C.rename? ρ with
      | none => rw [hC] at hU; simp at hU
      | some C' =>
        cases hS : S.rename? ρ with
        | none => rw [hC, hS] at hU; simp at hU
        | some S' =>
          rw [hC, hS] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← CaptureSet.rename?_sound C C' ρ σ h hC, ← Shape.rename?_sound S S' ρ σ h hS]

theorem ETy.rename?_sound :
    ∀ {s1 s2 : Sig} (E : ETy s1) (F : ETy s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → E.rename? ρ = some F → E = F.rename σ
  | _, _, .ty T, F, ρ, σ, h, hF => by
      simp only [ETy.rename?] at hF
      cases hT : T.rename? ρ with
      | none => rw [hT] at hF; simp at hF
      | some T' =>
        rw [hT] at hF
        simp only [Option.some.injEq] at hF
        subst hF
        simp only [ETy.rename]
        rw [← Ty.rename?_sound T T' ρ σ h hT]
  | _, _, .ex C T, F, ρ, σ, h, hF => by
      simp only [ETy.rename?] at hF
      cases hC : C.rename? ρ with
      | none => rw [hC] at hF; simp at hF
      | some C' =>
        cases hT : T.rename? ρ.lift with
        | none => rw [hC, hT] at hF; simp at hF
        | some T' =>
          rw [hC, hT] at hF
          simp only [Option.some.injEq] at hF
          subst hF
          simp only [ETy.rename]
          rw [← CaptureSet.rename?_sound C C' ρ σ h hC,
            ← Ty.rename?_sound T T' ρ.lift σ.lift h.lift hT]

theorem Proposition.rename?_sound :
    ∀ {s1 s2 : Sig} (P : Proposition s1) (Q : Proposition s2) (ρ : PartialRename s1 s2)
      (σ : Rename s2 s1), ρ.Inverts σ → P.rename? ρ = some Q → P = Q.rename σ
  | _, _, .le S T, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hS : S.rename? ρ with
      | none => rw [hS] at hQ; simp at hQ
      | some S' =>
        cases hT : T.rename? ρ with
        | none => rw [hS, hT] at hQ; simp at hQ
        | some T' =>
          rw [hS, hT] at hQ
          simp only [Option.some.injEq] at hQ
          subst hQ
          simp only [Proposition.rename]
          rw [← Shape.rename?_sound S S' ρ σ h hS, ← Shape.rename?_sound T T' ρ σ h hT]
  | _, _, .eq S T, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hS : S.rename? ρ with
      | none => rw [hS] at hQ; simp at hQ
      | some S' =>
        cases hT : T.rename? ρ with
        | none => rw [hS, hT] at hQ; simp at hQ
        | some T' =>
          rw [hS, hT] at hQ
          simp only [Option.some.injEq] at hQ
          subst hQ
          simp only [Proposition.rename]
          rw [← Shape.rename?_sound S S' ρ σ h hS, ← Shape.rename?_sound T T' ρ σ h hT]
  | _, _, .has ℓ, Q, _, _, _, hQ => by
      simp only [Proposition.rename?, Option.some.injEq] at hQ
      subst hQ; rfl
  | _, _, .bnd T, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hT : T.rename? ρ with
      | none => rw [hT] at hQ; simp at hQ
      | some T' =>
        rw [hT] at hQ
        simp only [Option.some.injEq] at hQ
        subst hQ
        simp only [Proposition.rename]
        rw [← Shape.rename?_sound T T' ρ σ h hT]
  | _, _, .leC C D, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hC : C.rename? ρ with
      | none => rw [hC] at hQ; simp at hQ
      | some C' =>
        cases hD : D.rename? ρ with
        | none => rw [hC, hD] at hQ; simp at hQ
        | some D' =>
          rw [hC, hD] at hQ
          simp only [Option.some.injEq] at hQ
          subst hQ
          simp only [Proposition.rename]
          rw [← CaptureSet.rename?_sound C C' ρ σ h hC,
            ← CaptureSet.rename?_sound D D' ρ σ h hD]
  | _, _, .eqC C D, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hC : C.rename? ρ with
      | none => rw [hC] at hQ; simp at hQ
      | some C' =>
        cases hD : D.rename? ρ with
        | none => rw [hC, hD] at hQ; simp at hQ
        | some D' =>
          rw [hC, hD] at hQ
          simp only [Option.some.injEq] at hQ
          subst hQ
          simp only [Proposition.rename]
          rw [← CaptureSet.rename?_sound C C' ρ σ h hC,
            ← CaptureSet.rename?_sound D D' ρ σ h hD]
  | _, _, .kindC C φ, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?] at hQ
      cases hC : C.rename? ρ with
      | none => rw [hC] at hQ; simp at hQ
      | some C' =>
        rw [hC] at hQ
        simp only [Option.some.injEq] at hQ
        subst hQ
        simp only [Proposition.rename]
        rw [← CaptureSet.rename?_sound C C' ρ σ h hC]

theorem Telescope.rename?_sound :
    ∀ {s1 s2 : Sig} (Tel : Telescope s1) (Tel2 : Telescope s2) (ρ : PartialRename s1 s2)
      (σ : Rename s2 s1), ρ.Inverts σ → Tel.rename? ρ = some Tel2 → Tel = Tel2.rename σ
  | _, _, .nil, Tel2, _, _, _, hU => by
      simp only [Telescope.rename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .cons Tel P, Tel2, ρ, σ, h, hU => by
      simp only [Telescope.rename?] at hU
      cases hTel : Tel.rename? ρ with
      | none => rw [hTel] at hU; simp at hU
      | some Tel' =>
        cases hP : P.rename? ρ with
        | none => rw [hTel, hP] at hU; simp at hU
        | some P' =>
          rw [hTel, hP] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Telescope.rename]
          rw [← Telescope.rename?_sound Tel Tel' ρ σ h hTel,
            ← Proposition.rename?_sound P P' ρ σ h hP]

end

/-! ### Inverting the scope readings

`Dom.underRoot` and `Cod.underRoot` insert the body root under the arrow's
capture binder.  The checker recovers the domain and the codomain of an arrow
from the endpoints of its two component coercions, which is the same partial
renaming as a strengthening, one binder deeper. -/

/-- Invert the insertion of a body root into a domain. -/
def Dom.underRoot? {s : Sig} (T : Ty ((s,c),c)) : Option (Dom s) :=
  T.rename? PartialRename.unshift.lift

theorem Dom.underRoot?_sound {s : Sig} {T : Ty ((s,c),c)} {U : Dom s}
    (h : Dom.underRoot? T = some U) : T = Dom.underRoot U :=
  Ty.rename?_sound T U PartialRename.unshift.lift Rename.succ.lift
    (PartialRename.Inverts.lift PartialRename.unshift_inverts) h

theorem Dom.underRoot?_underRoot {s : Sig} (U : Dom s) :
    Dom.underRoot? (Dom.underRoot U) = some U :=
  Ty.rename?_complete U PartialRename.unshift.lift Rename.succ.lift
    (PartialRename.Inverts.lift PartialRename.unshift_inverts)

/-- Invert the insertion of a body root into a codomain.  The codomain is an
answer, so this is the same partial renaming one sort up. -/
def Cod.underRoot? {s : Sig} (E : ETy (Sig.body s)) : Option (Cod s) :=
  E.rename? PartialRename.unshift.lift.lift

theorem Cod.underRoot?_sound {s : Sig} {E : ETy (Sig.body s)} {U : Cod s}
    (h : Cod.underRoot? E = some U) : E = Cod.underRoot U :=
  ETy.rename?_sound E U PartialRename.unshift.lift.lift Rename.succ.lift.lift
    (PartialRename.Inverts.lift (PartialRename.Inverts.lift PartialRename.unshift_inverts)) h

theorem Cod.underRoot?_underRoot {s : Sig} (U : Cod s) :
    Cod.underRoot? (Cod.underRoot U) = some U :=
  ETy.rename?_complete U PartialRename.unshift.lift.lift Rename.succ.lift.lift
    (PartialRename.Inverts.lift (PartialRename.Inverts.lift PartialRename.unshift_inverts))

theorem witness_underRootDom {s : Sig} (U : Dom s) :
    witness? (Dom.underRoot? (Dom.underRoot U)) = some ⟨U, Dom.underRoot?_underRoot U⟩ :=
  witness?_eq_some (Dom.underRoot?_underRoot U)

theorem witness_underRootCod {s : Sig} (U : Cod s) :
    witness? (Cod.underRoot? (Cod.underRoot U)) = some ⟨U, Cod.underRoot?_underRoot U⟩ :=
  witness?_eq_some (Cod.underRoot?_underRoot U)

/-- Strengthening: undo one weakening, if the innermost binder does not occur. -/
def Shape.strengthen? {s : Sig} {k : Kind} (S : Shape (s,,k)) : Option (Shape s) :=
  S.rename? PartialRename.unshift

theorem Shape.strengthen?_sound {s : Sig} {k : Kind} {S : Shape (s,,k)} {U : Shape s}
    (h : S.strengthen? = some U) : S = U↑ :=
  Shape.rename?_sound S U PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem Shape.strengthen?_weaken {s : Sig} {k : Kind} (U : Shape s) :
    (U.weaken (k := k)).strengthen? = some U :=
  Shape.rename?_complete U PartialRename.unshift Rename.succ PartialRename.unshift_inverts

theorem Shape.strengthen?_eq_some_iff {s : Sig} {k : Kind} {S : Shape (s,,k)} {U : Shape s} :
    S.strengthen? = some U ↔ S = U↑ := by
  constructor
  · exact Shape.strengthen?_sound
  · intro h; subst h; exact Shape.strengthen?_weaken U

/-- Strengthening, carrying the equation it establishes. -/
def Shape.strengthenW? {s : Sig} {k : Kind} (S : Shape (s,,k)) :
    Option { U : Shape s // S = U↑ } :=
  match witness? S.strengthen? with
  | some ⟨U, hU⟩ => some ⟨U, Shape.strengthen?_sound hU⟩
  | none => none

theorem Shape.strengthenW?_weaken {s : Sig} {k : Kind} (U : Shape s) :
    (U.weaken (k := k)).strengthenW? = some ⟨U, rfl⟩ := by
  simp only [Shape.strengthenW?, witness?_eq_some (Shape.strengthen?_weaken (k := k) U)]

/-- Strengthening a capture set: undo one weakening, if the innermost binder
does not occur.  `Morphism.kindCle`'s kinding premise is closed at `s` while
the chain that reaches it ends at `E↑`, so the checker recovers `E` here, as
`Shape.strengthen?` recovers a closed shape from a weakened one. -/
def CaptureSet.strengthen? {s : Sig} {k : Kind} (C : CaptureSet (s,,k)) :
    Option (CaptureSet s) :=
  C.rename? PartialRename.unshift

theorem CaptureSet.strengthen?_sound {s : Sig} {k : Kind} {C : CaptureSet (s,,k)}
    {D : CaptureSet s} (h : C.strengthen? = some D) : C = D↑ :=
  CaptureSet.rename?_sound C D PartialRename.unshift Rename.succ
    PartialRename.unshift_inverts h

theorem CaptureSet.strengthen?_weaken {s : Sig} {k : Kind} (D : CaptureSet s) :
    (D.weaken (k := k)).strengthen? = some D :=
  CaptureSet.rename?_complete D PartialRename.unshift Rename.succ
    PartialRename.unshift_inverts

/-- Strengthening, carrying the equation it establishes. -/
def CaptureSet.strengthenW? {s : Sig} {k : Kind} (C : CaptureSet (s,,k)) :
    Option { D : CaptureSet s // C = D↑ } :=
  match witness? C.strengthen? with
  | some ⟨D, hD⟩ => some ⟨D, CaptureSet.strengthen?_sound hD⟩
  | none => none

theorem CaptureSet.strengthenW?_weaken {s : Sig} {k : Kind} (D : CaptureSet s) :
    (D.weaken (k := k)).strengthenW? = some ⟨D, rfl⟩ := by
  simp only [CaptureSet.strengthenW?, witness?_eq_some (CaptureSet.strengthen?_weaken (k := k) D)]

def Ty.strengthen? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option (Ty s) :=
  T.rename? PartialRename.unshift

theorem Ty.strengthen?_sound {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s}
    (h : T.strengthen? = some U) : T = U↑ :=
  Ty.rename?_sound T U PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem Ty.strengthen?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    (U.weaken (k := k)).strengthen? = some U :=
  Ty.rename?_complete U PartialRename.unshift Rename.succ PartialRename.unshift_inverts

theorem Ty.strengthen?_eq_some_iff {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s} :
    T.strengthen? = some U ↔ T = U↑ := by
  constructor
  · exact Ty.strengthen?_sound
  · intro h; subst h; exact Ty.strengthen?_weaken U

/-- Strengthening inverts weakening, on the nose. -/
theorem Ty.strengthen?_some_iff {s : Sig} {k : Kind} {T : Ty (s,,k)} {U : Ty s} :
    T.strengthen? = some U ↔ T = U↑ :=
  Ty.strengthen?_eq_some_iff

/-- Strengthening, carrying the equation it establishes. -/
def Ty.strengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U↑ } :=
  match witness? T.strengthen? with
  | some ⟨U, hU⟩ => some ⟨U, Ty.strengthen?_sound hU⟩
  | none => none

theorem Ty.strengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    (U.weaken (k := k)).strengthenW? = some ⟨U, rfl⟩ := by
  simp only [Ty.strengthenW?, witness?_eq_some (Ty.strengthen?_weaken (k := k) U)]

/-! ### Strengthening at the answer sort

The same three, one sort up, plus the two double strengthenings the pack rule
and the `letex` rule need: a pack's residual reads its source under the
pack's root and its witness binder, and a `letex` body's answer avoids both
opened binders. -/

def ETy.strengthen? {s : Sig} {k : Kind} (E : ETy (s,,k)) : Option (ETy s) :=
  E.rename? PartialRename.unshift

theorem ETy.strengthen?_sound {s : Sig} {k : Kind} {E : ETy (s,,k)} {F : ETy s}
    (h : E.strengthen? = some F) : E = F↑ :=
  ETy.rename?_sound E F PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem ETy.strengthen?_weaken {s : Sig} {k : Kind} (F : ETy s) :
    (F.weaken (k := k)).strengthen? = some F :=
  ETy.rename?_complete F PartialRename.unshift Rename.succ PartialRename.unshift_inverts

def ETy.strengthenW? {s : Sig} {k : Kind} (E : ETy (s,,k)) :
    Option { F : ETy s // E = F↑ } :=
  match witness? E.strengthen? with
  | some ⟨F, hF⟩ => some ⟨F, ETy.strengthen?_sound hF⟩
  | none => none

theorem ETy.strengthenW?_weaken {s : Sig} {k : Kind} (F : ETy s) :
    (F.weaken (k := k)).strengthenW? = some ⟨F, rfl⟩ := by
  simp only [ETy.strengthenW?, witness?_eq_some (ETy.strengthen?_weaken (k := k) F)]

/-- Undo two capture weakenings of a type: what a pack's residual source
is. -/
def Ty.strengthenC2? {s : Sig} (T : Ty (Sig.scope s)) :
    Option { U : Ty s // T = Ty.weaken (k := .cap) (Ty.weaken (k := .cap) U) } :=
  match Ty.strengthenW? (k := .cap) T with
  | some ⟨T1, h1⟩ =>
      match Ty.strengthenW? (k := .cap) T1 with
      | some ⟨U, h2⟩ => some ⟨U, by rw [h1, h2]⟩
      | none => none
  | none => none

theorem Ty.strengthenC2?_weaken {s : Sig} (U : Ty s) :
    Ty.strengthenC2? (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) U)) = some ⟨U, rfl⟩ := by
  simp only [Ty.strengthenC2?, Ty.strengthenW?_weaken]

/-- Undo a capture weakening and then a term weakening of an answer: what a
`letex` body's answer avoids. -/
def ETy.strengthenVC2? {s : Sig} (E : ETy ((s,c),x)) :
    Option { F : ETy s // E = ETy.weaken (k := .var) (ETy.weaken (k := .cap) F) } :=
  match ETy.strengthenW? (k := .var) E with
  | some ⟨E1, h1⟩ =>
      match ETy.strengthenW? (k := .cap) E1 with
      | some ⟨F, h2⟩ => some ⟨F, by rw [h1, h2]⟩
      | none => none
  | none => none

theorem ETy.strengthenVC2?_weaken {s : Sig} (F : ETy s) :
    ETy.strengthenVC2? (ETy.weaken (k := .var) (ETy.weaken (k := .cap) F))
      = some ⟨F, rfl⟩ := by
  simp only [ETy.strengthenVC2?, ETy.strengthenW?_weaken]

/-! ## Checked results

Every kernel synthesises the outputs of its judgement and returns the
derivation it validated, so soundness is by construction. -/

structure ShapeChecked {s : Sig} (Γ : Ctx s) (ev : ShapeCo s) where
  source : Shape s
  target : Shape s
  typing : Γ ⊢ˢ ev : source ≤ target

structure CapChecked {s : Sig} (Γ : Ctx s) (ev : CapCo s) where
  source : CaptureSet s
  target : CaptureSet s
  typing : Γ ⊢ᶜ ev : source ⊑ target

structure CapEqChecked {s : Sig} (Γ : Ctx s) (ev : CapEq s) where
  source : CaptureSet s
  target : CaptureSet s
  typing : Γ ⊢ᶜ ev : source ≡ target

/-- Kinding is the one evidence family of the tree that *checks* instead of
synthesising, and the reason is in the rules: `nil` holds at every kind,
`kproj` and `kcls` hold at every kind their premise admits, and `kvar` says
nothing about the kind its atom carries.  So both the set and the kind are
inputs, and the result carries only the derivation.  The structure lives in
`Type` so that `Option` can hold it; its single field is a proof, so two
results at the same inputs are equal. -/
structure KindChecked {s : Sig} (Γ : Ctx s) (ev : KindCo s)
    (C : CaptureSet s) (φ : Cls.Kind) : Type where
  typing : Γ ⊢ᵏ ev : C ⊑ᵏ φ

/-- A capture-template `pre` chain, checked against the endpoint next to its
hole: the chain's target is given and its source is synthesised. -/
structure PreCheckedC {s : Sig} (Γ : Ctx s) (q : SideC s) (X : CaptureSet (s,x)) where
  source : CaptureSet (s,x)
  typing : SideC.HasType Γ q source X

/-- A capture-template `post` chain: the chain's source is given and its
target is synthesised. -/
structure PostCheckedC {s : Sig} (Γ : Ctx s) (q : SideC s) (Y : CaptureSet (s,x)) where
  target : CaptureSet (s,x)
  typing : SideC.HasType Γ q Y target

structure LeChecked {s : Sig} (Γ : Ctx s) (ev : LeCo s) where
  source : Ty s
  target : Ty s
  typing : Γ ⊢ ev : source ≤ target

structure EqChecked {s : Sig} (Γ : Ctx s) (ev : EqCo s) where
  source : Shape s
  target : Shape s
  typing : Γ ⊢ ev : source ≡ target

structure HasChecked {s : Sig} (Γ : Ctx s) (ev : Has s) (y : BVar s .var) where
  label : Label
  typing : Γ ⊢ ev : y ∋ label

/-- A morphism is checked against its *source* telescope (closed, over the self
binder): holes and presence propositions are read from it by index.  The target
telescope is synthesised. -/
structure MorChecked {s : Sig} (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) where
  tel : Telescope (s,x)
  typing : Γ ⊢ m : src ⇒ tel

/-- A template side checked against the endpoint next to the hole: for a
`pre` side the hole's left endpoint `X` is given and the outer source is
synthesised. -/
structure PreChecked {s : Sig} (Γ : Ctx s) (side : Side s) (X : Shape (s,x)) where
  source : Shape (s,x)
  typing : Side.HasType Γ side source X

/-- A `post` side: the hole's right endpoint `Y` is given and the outer target
is synthesised. -/
structure PostChecked {s : Sig} (Γ : Ctx s) (side : Side s) (Y : Shape (s,x)) where
  target : Shape (s,x)
  typing : Side.HasType Γ side Y target

structure AtomChecked {s : Sig} (Γ : Ctx s) (a : Atom s) where
  type : Ty s
  typing : Γ ⊢ₐ a : type

structure TmChecked {s : Sig} (Γ : Ctx s) (t : Tm s) where
  type : ETy s
  typing : Γ ⊢ t :ᵉ type

structure ValueChecked {s : Sig} (Γ : Ctx s) (v : Value s) where
  type : Ty s
  typing : Γ ⊢ᵥ v : type

structure PAtomChecked {s : Sig} (Γ : Ctx s) (p : PAtom s) where
  type : ETy s
  typing : Γ ⊢ₚ p : type

structure ELeChecked {s : Sig} (Γ : Ctx s) (ev : ELeCo s) where
  source : ETy s
  target : ETy s
  typing : Γ ⊢ᵉ ev : source ≤ target

structure ValueEChecked {s : Sig} (Γ : Ctx s) (v : Value s) where
  type : ETy s
  typing : Γ ⊢ᵥᵉ v : type

/-- Endpoints of a type inclusion. -/
abbrev Endpoints (s : Sig) := Ty s × Ty s
/-- Endpoints of a shape inclusion or of an equality. -/
abbrev ShapeEndpoints (s : Sig) := Shape s × Shape s
/-- Endpoints of a capture inclusion. -/
abbrev CapEndpoints (s : Sig) := CaptureSet s × CaptureSet s

/-! ### Elimination at an atom

The three `member` rules share their premises.  Each is factored into a helper
that takes the *synthesised* data of the premises, so that the helper's only
case analyses are on plain variables and on a lookup that reduces
definitionally.  An atom synthesises a *type*, and the inner coercion relates
*shapes*, so the helper reads the shape of the atom's type. -/

/-- `ShapeCo.member`: the `i`-th proposition of the object shape `e` lands in,
when it is an inclusion. -/
def leMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} (i : Nat)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (ShapeChecked Γ (.member a e i)) :=
  match Ta, ha with
  | .capt _ Sa, ha =>
      if hs : Se = Sa then
        match Te, he with
        | .obj Tel, he =>
            match Telescope.getAt? Tel i with
            | some ⟨.le S' T', hAt⟩ =>
                some ⟨S'⟦a.root⟧, T'⟦a.root⟧,
                  .member ha (by subst hs; exact he) hAt⟩
            | _ => none
        | _, _ => none
      else none

/-- `EqCo.member`: the same, when the proposition is an equality. -/
def eqMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} (i : Nat)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (EqChecked Γ (.member a e i)) :=
  match Ta, ha with
  | .capt _ Sa, ha =>
      if hs : Se = Sa then
        match Te, he with
        | .obj Tel, he =>
            match Telescope.getAt? Tel i with
            | some ⟨.eq S' T', hAt⟩ =>
                some ⟨S'⟦a.root⟧, T'⟦a.root⟧,
                  .member ha (by subst hs; exact he) hAt⟩
            | _ => none
        | _, _ => none
      else none

/-- `CapCo.member`: the same, when the proposition is a subcapturing
proposition. -/
def capMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} (i : Nat)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (CapChecked Γ (.member a e i)) :=
  match Ta, ha with
  | .capt _ Sa, ha =>
      if hs : Se = Sa then
        match Te, he with
        | .obj Tel, he =>
            match Telescope.getAt? Tel i with
            | some ⟨.leC C₁ C₂, hAt⟩ =>
                some ⟨C₁⟦a.root⟧, C₂⟦a.root⟧, .member ha (by subst hs; exact he) hAt⟩
            | _ => none
        | _, _ => none
      else none

/-- `CapEq.member`: the same, when the proposition is a capture equality. -/
def capEqMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} (i : Nat)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (CapEqChecked Γ (.member a e i)) :=
  match Ta, ha with
  | .capt _ Sa, ha =>
      if hs : Se = Sa then
        match Te, he with
        | .obj Tel, he =>
            match Telescope.getAt? Tel i with
            | some ⟨.eqC C₁ C₂, hAt⟩ =>
                some ⟨C₁⟦a.root⟧, C₂⟦a.root⟧, .member ha (by subst hs; exact he) hAt⟩
            | _ => none
        | _, _ => none
      else none

/-- `KindCo.kmember`: the same, when the proposition is a kinding
proposition.  Both outputs are *checked* here, because the kinding family
checks, so the helper compares the telescope's proposition with the set and
the kind it is given. -/
def kindMember {s : Sig} {Γ : Ctx s} {b : Atom s} {e : ShapeCo s} (i : Nat)
    {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te)
    (C : CaptureSet s) (φ : Cls.Kind) : Option (KindChecked Γ (.kmember b e i) C φ) :=
  match Tb, hb with
  | .capt _ Sb, hb =>
      if hs : Se = Sb then
        match Te, he with
        | .obj Tel, he =>
            match Telescope.getAt? Tel i with
            | some ⟨.kindC C₀ φ₀, hAt⟩ =>
                if hC : C = C₀⟦b.root⟧ then
                  if hφ : φ = φ₀ then
                    some ⟨by
                      subst hC; subst hφ; subst hs
                      exact .kmember hb he (.kindC hAt)⟩
                  else none
                else none
            | _ => none
        | _, _ => none
      else none

/-- `Has.member`: the same, when the proposition is a field declaration.  The
subject variable is checked, the label synthesised. -/
def hasMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : ShapeCo s} (i : Nat) (y : BVar s .var)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (HasChecked Γ (.member a e i) y) :=
  if hx : a.root = y then
    match Ta, ha with
    | .capt _ Sa, ha =>
        if hs : Se = Sa then
          match Te, he with
          | .obj Tel, he =>
              match Telescope.getAt? Tel i with
              | some ⟨.has ℓ, hAt⟩ =>
                  some ⟨ℓ, by subst hx; subst hs; exact .member ha he hAt⟩
              | _ => none
          | _, _ => none
        else none
  else none

/-- `Morphism.has`: the target inherits the `j`-th proposition of the *source*
telescope, which must be a field declaration. -/
def morHas {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.has m j)) :=
  match Telescope.getAt? src j with
  | some ⟨.has ℓ, hAt⟩ => some ⟨Tel ▹ ∋ ℓ, .has hm hAt⟩
  | _ => none

/-- `ShapeCo.bound`: the annotated object shape is below the shape of its
`i`-th proposition, which must be a bound of a (weakened) closed shape. -/
def leBound {s : Sig} {Γ : Ctx s} (Tel : Telescope (s,x)) (i : Nat) :
    Option (ShapeChecked Γ (.bound Tel i)) :=
  match Telescope.getAt? Tel i with
  | some ⟨.bnd X, hAt⟩ =>
      match X.strengthenW? with
      | some ⟨T, hT⟩ => some ⟨μ Tel, T, .bound (by rw [hT] at hAt; exact hAt)⟩
      | none => none
  | _ => none

/-- `Morphism.bnd`: a target bound proven by a closed coercion out of the
source object shape. -/
def morBnd {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {e : ShapeCo s}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) {Se Te : Shape s}
    (he : Γ ⊢ˢ e : Se ≤ Te) :
    Option (MorChecked Γ src (.bnd m e)) :=
  if hs : Se = μ src then
    some ⟨Tel ▹ ⊑ Te↑, .bnd hm (by rw [← hs]; exact he)⟩
  else none

/-- `Morphism.eq`: the target repeats the `j`-th proposition of the source
telescope, which must be an equality, flipped when `b` is set. -/
def morEq {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat) (b : Bool)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.eq m j b)) :=
  match Telescope.getAt? src j with
  | some ⟨.eq X Y, hAt⟩ =>
      match b with
      | false => some ⟨Tel ▹ X ≐ Y, .eq hm hAt⟩
      | true => some ⟨Tel ▹ Y ≐ X, .eqSym hm hAt⟩
  | _ => none

/-! ### Holes

A hole names a proposition of the source telescope and reads it as an
inclusion `X ⊑ Y`: an inclusion as it is, an equality in either direction.
`Hole.Reads` is the typing-side relation, `Hole.read?` its executable
counterpart; the three `le` rules of `Morphism.HasType` are the three ways of
reading a hole. -/

/-- `Hole.Reads src h X Y`: in `src`, the hole `h` proves `X ⊑ Y`. -/
inductive Hole.Reads (src : Telescope (s,x)) : Hole → Shape (s,x) → Shape (s,x) → Prop where
  | le : src ∋ (j ↦ X ⊑ Y) → Hole.Reads src (.le j) X Y
  | eq : src ∋ (j ↦ X ≐ Y) → Hole.Reads src (.eq j) X Y
  | eqSym : src ∋ (j ↦ Y ≐ X) → Hole.Reads src (.eqSym j) X Y

/-- The template rule, uniformly over the reading of the hole. -/
theorem Morphism.HasType.leOfReads {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s}
    {pre post : Side s} {h : Hole} {S X Y T : Shape (s,x)}
    (hm : Γ ⊢ m : src ⇒ Tel) (hr : Hole.Reads src h X Y)
    (hpre : Side.HasType Γ pre S X) (hpost : Side.HasType Γ post Y T) :
    Γ ⊢ .le m pre h post : src ⇒ Tel ▹ S ⊑ T := by
  cases hr with
  | le hAt => exact .le hm hAt hpre hpost
  | eq hAt => exact .leEq hm hAt hpre hpost
  | eqSym hAt => exact .leEqSym hm hAt hpre hpost

/-- Read a hole in the source telescope, with the proof of what it proves. -/
def Hole.read? (src : Telescope (s,x)) :
    (h : Hole) → Option { XY : Shape (s,x) × Shape (s,x) // Hole.Reads src h XY.1 XY.2 }
  | .le j =>
      match Telescope.getAt? src j with
      | some ⟨.le X Y, hAt⟩ => some ⟨(X, Y), .le hAt⟩
      | _ => none
  | .eq j =>
      match Telescope.getAt? src j with
      | some ⟨.eq X Y, hAt⟩ => some ⟨(X, Y), .eq hAt⟩
      | _ => none
  | .eqSym j =>
      match Telescope.getAt? src j with
      | some ⟨.eq Y X, hAt⟩ => some ⟨(X, Y), .eqSym hAt⟩
      | _ => none

theorem Hole.read?_of_Reads {src : Telescope (s,x)} {h : Hole} {X Y : Shape (s,x)}
    (hr : Hole.Reads src h X Y) : Hole.read? src h = some ⟨(X, Y), hr⟩ := by
  cases hr with
  | le hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]
  | eq hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]
  | eqSym hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]

/-- `ShapeCo.pair`: two coercions with the same source, into the annotated
object shapes. -/
def lePair {s : Sig} {Γ : Ctx s} {e f : ShapeCo s} (Tel₁ Tel₂ : Telescope (s,x))
    {Se Te : Shape s} (he : Γ ⊢ˢ e : Se ≤ Te) {Sf Tf : Shape s} (hf : Γ ⊢ˢ f : Sf ≤ Tf) :
    Option (ShapeChecked Γ (.pair Tel₁ Tel₂ e f)) :=
  if hs : Sf = Se then
    if h1 : Te = μ Tel₁ then
      if h2 : Tf = μ Tel₂ then
        some ⟨Se, μ (Tel₁ ++ Tel₂), by subst hs; subst h1; subst h2; exact .pair he hf⟩
      else none
    else none
  else none

/-- `And-I`: two typings of the same root, at the annotated object shapes and
the same capture set. -/
def atomBoth {s : Sig} {Γ : Ctx s} {a b : Atom s} (Tel₁ Tel₂ : Telescope (s,x))
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) :
    Option (AtomChecked Γ (.both Tel₁ Tel₂ a b)) :=
  match Ta, ha with
  | .capt Ca Sa, ha =>
      match Tb, hb with
      | .capt Cb Sb, hb =>
          if h1 : Sa = μ Tel₁ then
            if h2 : Sb = μ Tel₂ then
              if hc : Cb = Ca then
                if hr : b.root = a.root then
                  some ⟨(μ (Tel₁ ++ Tel₂)) ^ Ca, by
                    subst h1; subst h2; subst hc; exact .both ha hb hr⟩
                else none
              else none
            else none
          else none

/-- `Rec-E`: the atom's shape must be an object shape. -/
def atomUnfold {s : Sig} {Γ : Ctx s} {b : Atom s} {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) :
    Option (AtomChecked Γ (.unfoldSelf b)) :=
  match Tb, hb with
  | .capt C (.obj Tel), hb => some ⟨(.obj (Tel⟦b.root⟧)↑) ^ C, .unfoldSelf hb⟩
  | _, _ => none

/-- `Rec-I`: the atom's shape must be the annotated telescope opened at its
own root. -/
def atomFold {s : Sig} {Γ : Ctx s} {b : Atom s} (Tel : Telescope (s,x))
    {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) :
    Option (AtomChecked Γ (.foldSelf Tel b)) :=
  match Tb, hb with
  | .capt C S, hb =>
      if h : S = .obj (Tel⟦b.root⟧)↑ then
        some ⟨(.obj Tel) ^ C, .foldSelf (by rw [← h]; exact hb)⟩
      else none

/-- Boxing: pure, and nothing to check.  A box is a value. -/
def valueBox {s : Sig} {Γ : Ctx s} {a : Atom s} {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) :
    ValueChecked Γ (.box a) :=
  ⟨(□ Ta) ^ [], .box ha⟩

/-- Unboxing: the atom's shape must be a box, its capture set must be the
source of the charge, and the charge must land in the declared use set `U`.
An unboxing is a term. -/
def tmUnbox {s : Sig} {Γ : Ctx s} {a : Atom s} {f : CapCo s} (U : CaptureSet s)
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {C D : CaptureSet s} (hf : Γ ⊢ᶜ f : C ⊑ D) :
    Option (TmChecked Γ (.unbox a U f)) :=
  if hD : D = U then
    match Ta, ha with
    | .capt _ (.box (.capt C' S')), ha =>
        if hC : C' = C then
          some ⟨.ty (S' ^ C), by subst hD; subst hC; exact .unbox ha hf⟩
        else none
    | _, _ => none
  else none

/-- `CapCo.elem`: the one decided step of the capture family. -/
def capElem {s : Sig} {Γ : Ctx s} (C D : CaptureSet s) : Option (CapChecked Γ (.elem C D)) :=
  if h : C.Subset D then some ⟨C, D, .elem h⟩ else none

/-- `CapCo.capvar`: nothing to check, the atom's type supplies the target. -/
def capVar {s : Sig} {Γ : Ctx s} {a : Atom s} {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) :
    CapChecked Γ (.capvar a) :=
  match Ta, ha with
  | .capt C _, ha => ⟨[CapAtom.var a.root], C, .capvar ha⟩

/-- Recapturing: the charge must start at the atom's own capture set. -/
def atomRecap {s : Sig} {Γ : Ctx s} {a : Atom s} {f : CapCo s}
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {C D : CaptureSet s} (hf : Γ ⊢ᶜ f : C ⊑ D) :
    Option (AtomChecked Γ (.recap a f)) :=
  match Ta, ha with
  | .capt _ Sa, ha =>
      if hc : C = [CapAtom.var a.root] then
        some ⟨Sa ^ D, .recap ha (by subst hc; exact hf)⟩
      else none

/-- Read a capture hole in the source telescope, with the proof of what it
proves. -/
def HoleC.read? (src : Telescope (s,x)) : (h : HoleC) →
    Option { CD : CaptureSet (s,x) × CaptureSet (s,x) // src.HoleAtC h CD.1 CD.2 }
  | .leC j =>
      match Telescope.getAt? src j with
      | some ⟨.leC C D, hAt⟩ => some ⟨(C, D), .leC hAt⟩
      | _ => none
  | .eqC j =>
      match Telescope.getAt? src j with
      | some ⟨.eqC C D, hAt⟩ => some ⟨(C, D), .eqC hAt⟩
      | _ => none
  | .eqSymC j =>
      match Telescope.getAt? src j with
      | some ⟨.eqC D C, hAt⟩ => some ⟨(C, D), .eqSymC hAt⟩
      | _ => none

theorem HoleC.read?_of_HoleAtC {src : Telescope (s,x)} {h : HoleC} {C D : CaptureSet (s,x)}
    (hr : src.HoleAtC h C D) : HoleC.read? src h = some ⟨(C, D), hr⟩ := by
  cases hr with
  | leC hAt => simp [HoleC.read?, Telescope.getAt?_of_At hAt]
  | eqC hAt => simp [HoleC.read?, Telescope.getAt?_of_At hAt]
  | eqSymC hAt => simp [HoleC.read?, Telescope.getAt?_of_At hAt]

/-- `Morphism.eqC`: the target repeats the `j`-th proposition of the source
telescope, which must be a capture equality, flipped when `b` is set. -/
def morEqC {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat) (b : Bool)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.eqC m j b)) :=
  match Telescope.getAt? src j with
  | some ⟨.eqC C D, hAt⟩ =>
      match b with
      | false => some ⟨Tel ▹ C ≐ᶜ D, .eqC hm hAt⟩
      | true => some ⟨Tel ▹ D ≐ᶜ C, .eqSymC hm hAt⟩
  | _ => none

/-- Application: the function's shape must be an arrow whose domain is the
argument's type. -/
def tmApp {s : Sig} {Γ : Ctx s} {a b : Atom s} {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta)
    {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) : Option (TmChecked Γ (.app a b)) :=
  match Ta, ha with
  | .capt _ (.pi T U), ha =>
      if h : Tb = T.subst (Subst.singleC (CapAtom.var b.root)) then
        some ⟨U.subst (Subst.arg b), .app ha (by subst h; exact hb)⟩
      else none
  | _, _ => none

/-! ## Evidence kernel

Every core synthesises: the endpoints of a coercion, the label of a
field-presence proof, the target telescope of a morphism, the type of an
atom. -/

mutual

/-- The capture family: synthesising, like the rest.  It mentions atoms, so it
belongs to the mutual kernel. -/
def synthCapCore {s : Sig} (Γ : Ctx s) (ev : CapCo s) : Option (CapChecked Γ ev) :=
  match ev with
  | .refl C => some ⟨C, C, .refl⟩
  | .elem C D => capElem C D
  | .trans f g => do
      let cf ← synthCapCore Γ f
      let cg ← synthCapCore Γ g
      if h : cf.target = cg.source then
        some ⟨cf.source, cg.target, .trans (by rw [← h]; exact cf.typing) cg.typing⟩
      else none
  | .union f g => do
      let cf ← synthCapCore Γ f
      let cg ← synthCapCore Γ g
      if h : cf.target = cg.target then
        some ⟨cf.source ∪ cg.source, cg.target,
          .union (by rw [← h]; exact cf.typing) cg.typing⟩
      else none
  | .capvar a => do
      let ca ← synthAtomCore Γ a
      some (capVar ca.typing)
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthShapeCore Γ e
      capMember i ca.typing ce.typing
  | .eqToLe φ => do
      let cφ ← synthCapEqCore Γ φ
      some ⟨cφ.source, cφ.target, .eqToLe cφ.typing⟩
  | .level e r =>
      if h₁ : Γ.isRootB r then
        if h₂ : Γ.lvlLeB e r then some ⟨[e], [r], .level h₁ h₂⟩ else none
      else none
  | .unprojC C φ => some ⟨C.proj φ, C, .unprojC⟩
  | .projC g C φ =>
      match checkKindCore Γ g C φ with
      | some cg => some ⟨C, C.proj φ, .projC cg.typing⟩
      | none => none
  | .projMono f ψ =>
      match synthCapCore Γ f with
      | some cf => some ⟨cf.source.proj ψ, cf.target.proj ψ, .projMono cf.typing⟩
      | none => none

/-- The kinding family: checking, not synthesising, for the reason
`KindChecked` records.  Every premise of every rule of `KindCo.HasType` is a
decidable proposition over functions the tree already has, so the body is one
structural match with no search. -/
def checkKindCore {s : Sig} (Γ : Ctx s) (ev : KindCo s) (C : CaptureSet s) (φ : Cls.Kind) :
    Option (KindChecked Γ ev C φ) :=
  match ev with
  | .nil => if hC : C = [] then some ⟨by subst hC; exact .nil⟩ else none
  | .cons g h =>
      match C with
      | [] => none
      | a :: C₀ =>
          match checkKindCore Γ g [a] φ, checkKindCore Γ h C₀ φ with
          | some cg, some ch => some ⟨.cons cg.typing ch.typing⟩
          | _, _ => none
  | .kproj a =>
      if hC : C = [a] then
        if hk : a.kindOf.Subkind φ then some ⟨by subst hC; exact .kproj hk⟩ else none
      else none
  | .kcls a =>
      if hC : C = [a] then
        match witness? (Γ.clsOf? a.base) with
        | some ⟨c, hc⟩ =>
            if hk : a.kindOf.Contains c → φ.Contains c then
              some ⟨by subst hC; exact .kcls hc hk⟩
            else none
        | none => none
      else none
  | .kvar b g =>
      match C with
      | [a] =>
          match synthAtomCore Γ b with
          | some cb =>
              match cb.type, cb.typing with
              | .capt C₀ _, hb =>
                  if hbase : a.base = CapAtom.var b.root then
                    match checkKindCore Γ g (C₀.proj a.kindOf) φ with
                    | some cg => some ⟨.kvar hb hbase cg.typing⟩
                    | none => none
                  else none
          | none => none
      | _ => none
  | .kcvar a g =>
      if hC : C = [a] then
        match witness? (Γ.setOf? a.base) with
        | some ⟨C₀, hb⟩ =>
            match checkKindCore Γ g (C₀.proj a.kindOf) φ with
            | some cg => some ⟨by subst hC; exact .kcvar hb cg.typing⟩
            | none => none
        | none => none
      else none
  | .kmember b e i =>
      match synthAtomCore Γ b, synthShapeCore Γ e with
      | some cb, some ce => kindMember i cb.typing ce.typing C φ
      | _, _ => none
  | .kprojS g C₀ ψ =>
      if hC : C = C₀.proj ψ then
        match checkKindCore Γ g C₀ φ with
        | some cg => some ⟨by subst hC; exact .kprojS cg.typing⟩
        | none => none
      else none
  | .ksub g φ₁ =>
      if hk : φ₁.Subkind φ then
        match checkKindCore Γ g C φ₁ with
        | some cg => some ⟨.ksub cg.typing hk⟩
        | none => none
      else none
  -- The evidence form of `Ctx.KindLe.mono`: the capture premise synthesises
  -- both of its sets, so the source set is checked against the input and the
  -- kinding premise is checked at the capture premise's target.
  | .kle f g =>
      match synthCapCore Γ f with
      | some cf =>
          if hC : C = cf.source then
            match checkKindCore Γ g cf.target φ with
            | some cg => some ⟨by subst hC; exact .kle cf.typing cg.typing⟩
            | none => none
          else none
      | none => none

def synthCapEqCore {s : Sig} (Γ : Ctx s) (ev : CapEq s) : Option (CapEqChecked Γ ev) :=
  match ev with
  | .refl C => some ⟨C, C, .refl⟩
  | .symm φ => do
      let c ← synthCapEqCore Γ φ
      some ⟨c.target, c.source, .symm c.typing⟩
  | .trans φ ψ => do
      let cφ ← synthCapEqCore Γ φ
      let cψ ← synthCapEqCore Γ ψ
      if h : cφ.target = cψ.source then
        some ⟨cφ.source, cψ.target, .trans (by rw [← h]; exact cφ.typing) cψ.typing⟩
      else none
  | .defC y ℓ =>
      match witness? (Γ.lookupDefC y ℓ) with
      | some ⟨C, hC⟩ => some ⟨[CapAtom.name y ℓ], C, .defC hC⟩
      | none => none
  | .instC a C =>
      if h : Γ.InstOf a C then some ⟨[a], C, .instC h⟩ else none
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthShapeCore Γ e
      capEqMember i ca.typing ce.typing

/-- A capture-template `pre` chain, checked backwards from the endpoint next
to the hole. -/
def checkPreCoreC {s : Sig} (Γ : Ctx s) (q : SideC s) (X : CaptureSet (s,x)) :
    Option (PreCheckedC Γ q X) :=
  match q with
  | .nil => some ⟨X, .nil⟩
  | .cons st q => do
      let cq ← checkPreCoreC Γ q X
      match st with
      | .closed f => do
          let cf ← synthCapCore Γ f
          if h : cq.source = cf.target↑ then
            some ⟨cf.source↑, .cons (by rw [h]; exact .closed cf.typing) cq.typing⟩
          else none
      | .incl C D =>
          if h : cq.source = D then
            if hs : C.Subset D then
              some ⟨C, .cons (by rw [h]; exact .incl hs) cq.typing⟩
            else none
          else none

/-- A capture-template `post` chain, checked forwards from the endpoint next
to the hole. -/
def checkPostCoreC {s : Sig} (Γ : Ctx s) (q : SideC s) (X : CaptureSet (s,x)) :
    Option (PostCheckedC Γ q X) :=
  match q with
  | .nil => some ⟨X, .nil⟩
  | .cons st q =>
      match st with
      | .closed f => do
          let cf ← synthCapCore Γ f
          if h : X = cf.source↑ then do
            let cq ← checkPostCoreC Γ q (cf.target↑)
            some ⟨cq.target, .cons (by rw [h]; exact .closed cf.typing) cq.typing⟩
          else none
      | .incl C D =>
          if h : X = C then
            if hs : C.Subset D then do
              let cq ← checkPostCoreC Γ q D
              some ⟨cq.target, .cons (by rw [h]; exact .incl hs) cq.typing⟩
            else none
          else none

def synthShapeCore {s : Sig} (Γ : Ctx s) (ev : ShapeCo s) : Option (ShapeChecked Γ ev) :=
  match ev with
  | .refl S => some ⟨S, S, .refl⟩
  | .top S => some ⟨S, .top, .top⟩
  | .bot S => some ⟨.bot, S, .bot⟩
  | .eqToLe φ => do
      let c ← synthEqCore Γ φ
      some ⟨c.source, c.target, .eqToLe c.typing⟩
  | .trans e f => do
      let ce ← synthShapeCore Γ e
      let cf ← synthShapeCore Γ f
      if h : ce.target = cf.source then
        some ⟨ce.source, cf.target, .trans ce.typing (by rw [h]; exact cf.typing)⟩
      else none
  | .pi e f => do
      let ce ← synthLeCore Γ.scope e
      let d2 ← witness? (Dom.underRoot? ce.source)
      let d1 ← witness? (Dom.underRoot? ce.target)
      let cf ← synthELeCore (Γ.body d2.val) f
      let u1 ← witness? (Cod.underRoot? cf.source)
      let u2 ← witness? (Cod.underRoot? cf.target)
      some ⟨.pi d1.val u1.val, .pi d2.val u2.val, by
        refine ShapeCo.HasType.pi ?_ ?_
        · rw [← Dom.underRoot?_sound d2.property, ← Dom.underRoot?_sound d1.property]
          exact ce.typing
        · rw [← Cod.underRoot?_sound u1.property, ← Cod.underRoot?_sound u2.property]
          exact cf.typing⟩
  | .obj Tel m => do
      let cm ← synthMorCore Γ Tel m
      some ⟨μ Tel, μ cm.tel, .obj cm.typing⟩
  | .pair Tel₁ Tel₂ e f => do
      let ce ← synthShapeCore Γ e
      let cf ← synthShapeCore Γ f
      lePair Tel₁ Tel₂ ce.typing cf.typing
  | .bound Tel i => leBound Tel i
  | .intoBnd e => do
      let ce ← synthShapeCore Γ e
      some ⟨ce.source, μ (.nil ▹ ⊑ ce.target↑), .intoBnd ce.typing⟩
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthShapeCore Γ e
      leMember i ca.typing ce.typing
  | .boxed d => do
      let cd ← synthLeCore Γ d
      some ⟨□ cd.source, □ cd.target, .boxed cd.typing⟩

def synthLeCore {s : Sig} (Γ : Ctx s) (ev : LeCo s) : Option (LeChecked Γ ev) :=
  match ev with
  | .capt e f => do
      let ce ← synthShapeCore Γ e
      let cf ← synthCapCore Γ f
      some ⟨ce.source ^ cf.source, ce.target ^ cf.target, .capt ce.typing cf.typing⟩

def synthEqCore {s : Sig} (Γ : Ctx s) (ev : EqCo s) : Option (EqChecked Γ ev) :=
  match ev with
  | .refl S => some ⟨S, S, .refl⟩
  | .symm φ => do
      let c ← synthEqCore Γ φ
      some ⟨c.target, c.source, .symm c.typing⟩
  | .trans φ ψ => do
      let cφ ← synthEqCore Γ φ
      let cψ ← synthEqCore Γ ψ
      if h : cφ.target = cψ.source then
        some ⟨cφ.source, cψ.target, .trans cφ.typing (by rw [h]; exact cψ.typing)⟩
      else none
  | .def y ℓ =>
      match witness? (Γ.lookupDef y ℓ) with
      | some ⟨W, hW⟩ => some ⟨.sel y ℓ, W, .def hW⟩
      | none => none
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthShapeCore Γ e
      eqMember i ca.typing ce.typing

def synthHasCore {s : Sig} (Γ : Ctx s) (ev : Has s) (y : BVar s .var) :
    Option (HasChecked Γ ev y) :=
  match ev with
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthShapeCore Γ e
      hasMember i y ca.typing ce.typing
  | .field ℓ =>
      match witness? (Γ.lookupFields y) with
      | some ⟨Fs, hF⟩ => if hm : ℓ ∈ Fs then some ⟨ℓ, .field hF hm⟩ else none
      | none => none

/-- A `pre` side, checked against the hole's left endpoint `X`: `none` leaves
it in place, `some e` needs `e` to land in the closed shape `X` weakens. -/
def checkPreCore {s : Sig} (Γ : Ctx s) (side : Side s) (X : Shape (s,x)) :
    Option (PreChecked Γ side X) :=
  match side with
  | .none => some ⟨X, .none⟩
  | .some e => do
      let ce ← synthShapeCore Γ e
      if h : X = ce.target↑ then some ⟨ce.source↑, by subst h; exact .some ce.typing⟩
      else none

/-- A `post` side, checked against the hole's right endpoint `Y`. -/
def checkPostCore {s : Sig} (Γ : Ctx s) (side : Side s) (Y : Shape (s,x)) :
    Option (PostChecked Γ side Y) :=
  match side with
  | .none => some ⟨Y, .none⟩
  | .some e => do
      let ce ← synthShapeCore Γ e
      if h : Y = ce.source↑ then some ⟨ce.target↑, by subst h; exact .some ce.typing⟩
      else none

def synthMorCore {s : Sig} (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) :
    Option (MorChecked Γ src m) :=
  match m with
  | .nil => some ⟨.nil, .nil⟩
  | .le m pre h post => do
      let cm ← synthMorCore Γ src m
      let r ← Hole.read? src h
      let cpre ← checkPreCore Γ pre r.val.1
      let cpost ← checkPostCore Γ post r.val.2
      some ⟨cm.tel ▹ cpre.source ⊑ cpost.target,
        cm.typing.leOfReads r.property cpre.typing cpost.typing⟩
  | .eq m j b => do
      let cm ← synthMorCore Γ src m
      morEq j b cm.typing
  | .has m j => do
      let cm ← synthMorCore Γ src m
      morHas j cm.typing
  | .bnd m e => do
      let cm ← synthMorCore Γ src m
      let ce ← synthShapeCore Γ e
      morBnd cm.typing ce.typing
  | .leC m q h q' => do
      let cm ← synthMorCore Γ src m
      let r ← HoleC.read? src h
      let cq ← checkPreCoreC Γ q r.val.1
      let cq' ← checkPostCoreC Γ q' r.val.2
      some ⟨cm.tel ▹ cq.source ⊑ᶜ cq'.target,
        .leC cm.typing r.property cq.typing cq'.typing⟩
  | .eqC m j b => do
      let cm ← synthMorCore Γ src m
      morEqC j b cm.typing
  | .kindC m q j φ₂ => do
      let cm ← synthMorCore Γ src m
      match Telescope.getAt? src j with
      | some ⟨.kindC C φ₁, hAt⟩ =>
          if hsub : φ₁.AdmitsStep φ₂ then do
            let cq ← checkPreCoreC Γ q C
            some ⟨cm.tel ▹ cq.source ⊑ᵏ φ₂, .kindC cm.typing hAt cq.typing hsub⟩
          else none
      | _ => none
  -- A kinding template over a capture hole: the hole and the two chains are
  -- read as for `leC`, the post chain's target is strengthened to the closed
  -- set the kinding premise is checked at, and the target kind rides on the
  -- term, as it does for `kindC`.
  | .kindCle m q h q' g φ₂ => do
      let cm ← synthMorCore Γ src m
      let r ← HoleC.read? src h
      let cq ← checkPreCoreC Γ q r.val.1
      let cq' ← checkPostCoreC Γ q' r.val.2
      let e ← CaptureSet.strengthenW? cq'.target
      let cg ← checkKindCore Γ g e.val φ₂
      some ⟨cm.tel ▹ cq.source ⊑ᵏ φ₂,
        .kindCle cm.typing r.property cq.typing (e.property ▸ cq'.typing) cg.typing⟩

def synthAtomCore {s : Sig} (Γ : Ctx s) (a : Atom s) : Option (AtomChecked Γ a) :=
  match a with
  | .var y => some ⟨Γ.lookupTy y, .var⟩
  | .cast b e => do
      let cb ← synthAtomCore Γ b
      let ce ← synthLeCore Γ e
      if h : ce.source = cb.type then
        some ⟨ce.target, .cast cb.typing (by rw [← h]; exact ce.typing)⟩
      else none
  | .unfoldSelf b => do
      let cb ← synthAtomCore Γ b
      atomUnfold cb.typing
  | .foldSelf Tel b => do
      let cb ← synthAtomCore Γ b
      atomFold Tel cb.typing
  | .both Tel₁ Tel₂ a b => do
      let ca ← synthAtomCore Γ a
      let cb ← synthAtomCore Γ b
      atomBoth Tel₁ Tel₂ ca.typing cb.typing
  | .recap b f => do
      let cb ← synthAtomCore Γ b
      let cf ← synthCapCore Γ f
      atomRecap cb.typing cf.typing

/-- The answer family: synthesising.  `ShapeCo.HasType.pi` premises it, so it
belongs to the block. -/
def synthELeCore {s : Sig} (Γ : Ctx s) (ev : ELeCo s) : Option (ELeChecked Γ ev) :=
  match ev with
  | .plain e => do
      let ce ← synthLeCore Γ e
      some ⟨.ty ce.source, .ty ce.target, .plain ce.typing⟩
  | .pack C h e => do
      let ch ← synthCapCore Γ h
      let ce ← synthLeCore (Γ.scopeInst C) e
      let wT ← witness? (Dom.underRoot? ce.target)
      let wS ← Ty.strengthenC2? ce.source
      if hC : ch.source = C then
        some ⟨.ty wS.val, ∃ᶜ[ch.target] wT.val,
          .pack (by rw [← hC]; exact ch.typing)
            (by rw [← wS.property, ← Dom.underRoot?_sound wT.property]; exact ce.typing)⟩
      else none
  | .cong h e => do
      let ch ← synthCapCore Γ h
      let ce ← synthLeCore Γ.scope e
      let w1 ← witness? (Dom.underRoot? ce.source)
      let w2 ← witness? (Dom.underRoot? ce.target)
      some ⟨∃ᶜ[ch.source] w1.val, ∃ᶜ[ch.target] w2.val,
        .cong ch.typing
          (by rw [← Dom.underRoot?_sound w1.property,
            ← Dom.underRoot?_sound w2.property]; exact ce.typing)⟩
  | .trans g h => do
      let cg ← synthELeCore Γ g
      let ch ← synthELeCore Γ h
      if hh : cg.target = ch.source then
        some ⟨cg.source, ch.target, .trans (by rw [← hh]; exact cg.typing) ch.typing⟩
      else none

end

/-- Packed atoms.  It premises only judgments of the block above, so it is
stated after it. -/
def synthPAtomCore {s : Sig} (Γ : Ctx s) (p : PAtom s) : Option (PAtomChecked Γ p) :=
  match p with
  | .plain a => do
      let ca ← synthAtomCore Γ a
      some ⟨.ty ca.type, .plain ca.typing⟩
  | .pack C h e a => do
      let ca ← synthAtomCore Γ a
      let ch ← synthCapCore Γ h
      let ce ← synthLeCore (Γ.scopeInst C) e
      let wT ← witness? (Dom.underRoot? ce.target)
      if hC : ch.source = C then
        if hS : ce.source = Ty.weaken (k := .cap) (Ty.weaken (k := .cap) ca.type) then
          some ⟨∃ᶜ[ch.target] wT.val,
            .pack ca.typing (by rw [← hC]; exact ch.typing)
              (by rw [← hS, ← Dom.underRoot?_sound wT.property]; exact ce.typing)⟩
        else none
      else none

/-! ## Term kernel -/

mutual

def synthTmCore {s : Sig} (Γ : Ctx s) (t : Tm s) : Option (TmChecked Γ t) :=
  match t with
  | .atom p => do
      let cp ← synthPAtomCore Γ p
      some ⟨cp.type, .atom cp.typing⟩
  | .val v =>
      match v with
      | .pack C h e v0 => do
          let cv ← synthValueCore Γ v0
          let ch ← synthCapCore Γ h
          let ce ← synthLeCore (Γ.scopeInst C) e
          let wT ← witness? (Dom.underRoot? ce.target)
          if hC : ch.source = C then
            if hS : ce.source = Ty.weaken (k := .cap) (Ty.weaken (k := .cap) cv.type) then
              some ⟨∃ᶜ[ch.target] wT.val,
                .val (.pack cv.typing (by rw [← hC]; exact ch.typing)
                  (by rw [← hS, ← Dom.underRoot?_sound wT.property]; exact ce.typing))⟩
            else none
          else none
      | v0 => do
          let cv ← synthValueCore Γ v0
          some ⟨.ty cv.type, .val (.plain cv.typing)⟩
  | .app a b => do
      let ca ← synthAtomCore Γ a
      let cb ← synthAtomCore Γ b
      tmApp ca.typing cb.typing
  | .proj a ℓ h => do
      let ca ← synthAtomCore Γ a
      let ch ← synthHasCore Γ h a.root
      if hl : ch.label = ℓ then
        some ⟨.ty (Ty.capt [CapAtom.name a.root ℓ] (Shape.sel a.root ℓ)),
          .proj ca.typing (by rw [← hl]; exact ch.typing)⟩
      else none
  | .let t u U' f => do
      let ct ← synthTmCore Γ t
      match ct.type, ct.typing with
      | .ty T, ht => do
          let cu ← synthTmCore (Γ.cons (.opaque T)) u
          let cf ← synthCapCore (Γ.cons (.opaque T)) f
          match cu.type.strengthenW? with
          | some ⟨E, hE⟩ =>
              if hs : cf.source = u.uses then
                if hg : cf.target = U'↑ then
                  some ⟨E, .let ht (by rw [← hE]; exact cu.typing)
                    (by rw [← hs, ← hg]; exact cf.typing)⟩
                else none
              else none
          | none => none
      | .ex _ _, _ => none
  | .cast t e => do
      let ct ← synthTmCore Γ t
      let ce ← synthLeCore Γ e
      match ct.type, ct.typing with
      | .ty T, ht =>
          if h : ce.source = T then
            some ⟨.ty ce.target, .cast ht (by rw [← h]; exact ce.typing)⟩
          else none
      | .ex _ _, _ => none
  | .castE t g => do
      let ct ← synthTmCore Γ t
      let cg ← synthELeCore Γ g
      if h : cg.source = ct.type then
        some ⟨cg.target, .castE ct.typing (by rw [← h]; exact cg.typing)⟩
      else none
  | .letex t u U' h f => do
      let ct ← synthTmCore Γ t
      match ct.type, ct.typing with
      | .ex C₀ T, ht => do
          let ch ← synthCapCore Γ h
          let cu ← synthTmCore ((Γ.consC .star).cons (.opaque T)) u
          let cf ← synthCapCore ((Γ.consC .star).cons (.opaque T)) f
          match ETy.strengthenVC2? cu.type with
          | some ⟨E, hE⟩ =>
              if h1 : ch.source = C₀ then
                if h2 : ch.target = U' then
                  if h3 : cf.source = u.uses then
                    if h4 : cf.target
                        = ((CaptureSet.weaken (k := .var)
                            (CaptureSet.weaken (k := .cap) U'))
                          ∪ [CapAtom.cvar (.there .here)]) then
                      some ⟨E, .letex ht (by rw [← h1, ← h2]; exact ch.typing)
                        (by rw [← hE]; exact cu.typing)
                        (by rw [← h3, ← h4]; exact cf.typing)⟩
                    else none
                  else none
                else none
              else none
          | none => none
      | .ty _, _ => none
  | .unbox a U f => do
      let ca ← synthAtomCore Γ a
      let cf ← synthCapCore Γ f
      tmUnbox U ca.typing cf.typing
termination_by sizeOf t


def synthValueCore {s : Sig} (Γ : Ctx s) (v : Value s) : Option (ValueChecked Γ v) :=
  match v with
  | .lam A T t g => do
      let ct ← synthTmCore (Γ.body T) t
      let U ← witness? (Cod.underRoot? ct.type)
      let cg ← synthCapCore (Γ.body T) g
      if hs : cg.source = t.uses then
        if ht : cg.target = (A↑↑↑ ∪ [CapAtom.var .here]) then
          some ⟨(.pi T U.val) ^ A,
            .lam (by rw [← Cod.underRoot?_sound U.property]; exact ct.typing)
              (by rw [← hs, ← ht]; exact cg.typing)⟩
        else none
      else none
  | .obj A W Wc F => do
      let Tel := Telescope.ofLiteral W Wc F.labels
      let pF ← checkFieldsCore A↑ (Γ.objBody ((.obj Tel) ^ A) W Wc F.labels) F
      some ⟨(.obj Tel) ^ A, .obj pF.down⟩
  | .box a => do
      let ca ← synthAtomCore Γ a
      some (valueBox ca.typing)
  | .cast v e => do
      let cv ← synthValueCore Γ v
      let ce ← synthLeCore Γ e
      if h : ce.source = cv.type then
        some ⟨ce.target, .cast cv.typing (by rw [← h]; exact ce.typing)⟩
      else none
  | .pack _ _ _ _ => none
termination_by sizeOf v

def checkFieldsCore {s : Sig} (A : CaptureSet s) (Γ : Ctx (s,x)) (F : Fields (s,x)) :
    Option (PLift (Γ ⊢ᶠ[A] F)) :=
  match F with
  | .nil => some ⟨.nil⟩
  | .cons F ℓ t g => do
      let pF ← checkFieldsCore A Γ F
      let ct ← synthTmCore Γ t
      let cg ← synthCapCore Γ g
      if h : ct.type = ETy.ty (Ty.capt [CapAtom.name .here ℓ] (Shape.sel .here ℓ)) then
        if hs : cg.source = t.uses then
          if ht : cg.target = (A↑ ∪ [CapAtom.var .here]) then
            some ⟨.cons pF.down (by rw [← h]; exact ct.typing)
              (by rw [← hs, ← ht]; exact cg.typing)⟩
          else none
        else none
      else none
termination_by sizeOf F

end

/-- Values at the answer sort.  `Value.HasType` has no `pack` rule, so a
packed value is never `plain`. -/
def synthValueECore {s : Sig} (Γ : Ctx s) (v : Value s) : Option (ValueEChecked Γ v) :=
  match v with
  | .pack C h e v0 => do
      let cv ← synthValueCore Γ v0
      let ch ← synthCapCore Γ h
      let ce ← synthLeCore (Γ.scopeInst C) e
      let wT ← witness? (Dom.underRoot? ce.target)
      if hC : ch.source = C then
        if hS : ce.source = Ty.weaken (k := .cap) (Ty.weaken (k := .cap) cv.type) then
          some ⟨∃ᶜ[ch.target] wT.val,
            .pack cv.typing (by rw [← hC]; exact ch.typing)
              (by rw [← hS, ← Dom.underRoot?_sound wT.property]; exact ce.typing)⟩
        else none
      else none
  | v0 => do
      let cv ← synthValueCore Γ v0
      some ⟨.ty cv.type, .plain cv.typing⟩

/-! ## Public interface

Each judgement has a synthesising mode and a checking mode; the checking mode
compares the synthesised outputs with the expected ones. -/

/-- Synthesise both endpoints of a shape inclusion. -/
def synthShape {s : Sig} (Γ : Ctx s) (ev : ShapeCo s) : Option (ShapeEndpoints s) :=
  (synthShapeCore Γ ev).map fun c => (c.source, c.target)

def checkShape {s : Sig} (Γ : Ctx s) (ev : ShapeCo s) (S T : Shape s) : Bool :=
  decide (synthShape Γ ev = some (S, T))

/-- Synthesise both capture sets of a capture inclusion. -/
def synthCap {s : Sig} (Γ : Ctx s) (ev : CapCo s) : Option (CapEndpoints s) :=
  (synthCapCore Γ ev).map fun c => (c.source, c.target)

def checkCap {s : Sig} (Γ : Ctx s) (ev : CapCo s) (C D : CaptureSet s) : Bool :=
  decide (synthCap Γ ev = some (C, D))

/-- Check a kinding derivation against the set and the kind it claims.  This
is the public form K1.5 names.  There is no `synthKindCo`: kinding evidence
determines neither of its two outputs, which is what `KindChecked` records. -/
def checkKindCo {s : Sig} (Γ : Ctx s) (ev : KindCo s) (C : CaptureSet s) (φ : Cls.Kind) :
    Bool :=
  (checkKindCore Γ ev C φ).isSome

/-- Synthesise both capture sets of a capture equality. -/
def synthCapEq {s : Sig} (Γ : Ctx s) (ev : CapEq s) : Option (CapEndpoints s) :=
  (synthCapEqCore Γ ev).map fun c => (c.source, c.target)

def checkCapEq {s : Sig} (Γ : Ctx s) (ev : CapEq s) (C D : CaptureSet s) : Bool :=
  decide (synthCapEq Γ ev = some (C, D))

/-- Synthesise both endpoints of a type inclusion. -/
def synthLe {s : Sig} (Γ : Ctx s) (ev : LeCo s) : Option (Endpoints s) :=
  (synthLeCore Γ ev).map fun c => (c.source, c.target)

def checkLe {s : Sig} (Γ : Ctx s) (ev : LeCo s) (S T : Ty s) : Bool :=
  decide (synthLe Γ ev = some (S, T))

def synthEq {s : Sig} (Γ : Ctx s) (ev : EqCo s) : Option (ShapeEndpoints s) :=
  (synthEqCore Γ ev).map fun c => (c.source, c.target)

def checkEq {s : Sig} (Γ : Ctx s) (ev : EqCo s) (S T : Shape s) : Bool :=
  decide (synthEq Γ ev = some (S, T))

/-- Synthesise the label a field-presence proof establishes for `y`. -/
def synthHas {s : Sig} (Γ : Ctx s) (ev : Has s) (y : BVar s .var) : Option Label :=
  (synthHasCore Γ ev y).map HasChecked.label

def checkHas {s : Sig} (Γ : Ctx s) (ev : Has s) (y : BVar s .var) (ℓ : Label) : Bool :=
  decide (synthHas Γ ev y = some ℓ)

/-- Synthesise the target telescope of a morphism, given its source telescope. -/
def synthMorphism {s : Sig} (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) :
    Option (Telescope (s,x)) :=
  (synthMorCore Γ src m).map MorChecked.tel

def checkMorphism {s : Sig} (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s)
    (Tel : Telescope (s,x)) : Bool :=
  decide (synthMorphism Γ src m = some Tel)

def synthAtom {s : Sig} (Γ : Ctx s) (a : Atom s) : Option (Ty s) :=
  (synthAtomCore Γ a).map AtomChecked.type

def checkAtom {s : Sig} (Γ : Ctx s) (a : Atom s) (T : Ty s) : Bool :=
  decide (synthAtom Γ a = some T)

/-- Synthesise the *answer* of a term. -/
def synthTmE {s : Sig} (Γ : Ctx s) (t : Tm s) : Option (ETy s) :=
  (synthTmCore Γ t).map TmChecked.type

def checkTmE {s : Sig} (Γ : Ctx s) (t : Tm s) (E : ETy s) : Bool :=
  decide (synthTmE Γ t = some E)

/-- Synthesise the type of a term whose answer is plain.  This is the mode
the rest of the tree uses, and `checkTm` is `checkTmE` at `.ty T`. -/
def synthTm {s : Sig} (Γ : Ctx s) (t : Tm s) : Option (Ty s) :=
  match synthTmE Γ t with
  | some (.ty T) => some T
  | _ => none

def checkTm {s : Sig} (Γ : Ctx s) (t : Tm s) (T : Ty s) : Bool :=
  checkTmE Γ t (.ty T)

/-- Synthesise the answer of a packed atom. -/
def synthPAtom {s : Sig} (Γ : Ctx s) (p : PAtom s) : Option (ETy s) :=
  (synthPAtomCore Γ p).map PAtomChecked.type

def checkPAtom {s : Sig} (Γ : Ctx s) (p : PAtom s) (E : ETy s) : Bool :=
  decide (synthPAtom Γ p = some E)

/-- Synthesise both endpoints of an answer inclusion. -/
def synthELe {s : Sig} (Γ : Ctx s) (ev : ELeCo s) : Option (ETy s × ETy s) :=
  (synthELeCore Γ ev).map fun c => (c.source, c.target)

def checkELe {s : Sig} (Γ : Ctx s) (ev : ELeCo s) (E E' : ETy s) : Bool :=
  decide (synthELe Γ ev = some (E, E'))

/-- Synthesise the answer of a value. -/
def synthValueE {s : Sig} (Γ : Ctx s) (v : Value s) : Option (ETy s) :=
  (synthValueECore Γ v).map ValueEChecked.type

def checkValueE {s : Sig} (Γ : Ctx s) (v : Value s) (E : ETy s) : Bool :=
  decide (synthValueE Γ v = some E)

def synthValue {s : Sig} (Γ : Ctx s) (v : Value s) : Option (Ty s) :=
  (synthValueCore Γ v).map ValueChecked.type

def checkValue {s : Sig} (Γ : Ctx s) (v : Value s) (T : Ty s) : Bool :=
  decide (synthValue Γ v = some T)

def checkFields {s : Sig} (A : CaptureSet s) (Γ : Ctx (s,x)) (F : Fields (s,x)) : Bool :=
  (checkFieldsCore A Γ F).isSome

/-! ## Soundness

Each kernel already carries the derivation, so soundness is extraction. -/

private theorem isSome_elim {α : Type} {o : Option α} (h : o.isSome = true) : ∃ v, o = some v := by
  cases o with
  | none => simp at h
  | some v => exact ⟨v, rfl⟩

theorem synthShape_sound {s : Sig} {Γ : Ctx s} {ev : ShapeCo s} {S T : Shape s}
    (h : synthShape Γ ev = some (S, T)) : Γ ⊢ˢ ev : S ≤ T := by
  unfold synthShape at h
  cases hc : synthShapeCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkShape_sound {s : Sig} {Γ : Ctx s} {ev : ShapeCo s} {S T : Shape s}
    (h : checkShape Γ ev S T = true) : Γ ⊢ˢ ev : S ≤ T :=
  synthShape_sound (of_decide_eq_true h)

theorem synthCap_sound {s : Sig} {Γ : Ctx s} {ev : CapCo s} {C D : CaptureSet s}
    (h : synthCap Γ ev = some (C, D)) : Γ ⊢ᶜ ev : C ⊑ D := by
  unfold synthCap at h
  cases hc : synthCapCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkCap_sound {s : Sig} {Γ : Ctx s} {ev : CapCo s} {C D : CaptureSet s}
    (h : checkCap Γ ev C D = true) : Γ ⊢ᶜ ev : C ⊑ D :=
  synthCap_sound (of_decide_eq_true h)

theorem checkKindCo_sound {s : Sig} {Γ : Ctx s} {ev : KindCo s} {C : CaptureSet s}
    {φ : Cls.Kind} (h : checkKindCo Γ ev C φ = true) : Γ ⊢ᵏ ev : C ⊑ᵏ φ := by
  unfold checkKindCo at h
  cases hc : checkKindCore Γ ev C φ with
  | none => rw [hc] at h; simp at h
  | some c => exact c.typing

theorem synthCapEq_sound {s : Sig} {Γ : Ctx s} {ev : CapEq s} {C D : CaptureSet s}
    (h : synthCapEq Γ ev = some (C, D)) : Γ ⊢ᶜ ev : C ≡ D := by
  unfold synthCapEq at h
  cases hc : synthCapEqCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkCapEq_sound {s : Sig} {Γ : Ctx s} {ev : CapEq s} {C D : CaptureSet s}
    (h : checkCapEq Γ ev C D = true) : Γ ⊢ᶜ ev : C ≡ D :=
  synthCapEq_sound (of_decide_eq_true h)

theorem synthLe_sound {s : Sig} {Γ : Ctx s} {ev : LeCo s} {S T : Ty s}
    (h : synthLe Γ ev = some (S, T)) : Γ ⊢ ev : S ≤ T := by
  unfold synthLe at h
  cases hc : synthLeCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkLe_sound {s : Sig} {Γ : Ctx s} {ev : LeCo s} {S T : Ty s}
    (h : checkLe Γ ev S T = true) : Γ ⊢ ev : S ≤ T :=
  synthLe_sound (of_decide_eq_true h)

theorem synthEq_sound {s : Sig} {Γ : Ctx s} {ev : EqCo s} {S T : Shape s}
    (h : synthEq Γ ev = some (S, T)) : Γ ⊢ ev : S ≡ T := by
  unfold synthEq at h
  cases hc : synthEqCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkEq_sound {s : Sig} {Γ : Ctx s} {ev : EqCo s} {S T : Shape s}
    (h : checkEq Γ ev S T = true) : Γ ⊢ ev : S ≡ T :=
  synthEq_sound (of_decide_eq_true h)

theorem synthHas_sound {s : Sig} {Γ : Ctx s} {ev : Has s} {y : BVar s .var} {ℓ : Label}
    (h : synthHas Γ ev y = some ℓ) : Has.HasType Γ ev y ℓ := by
  unfold synthHas at h
  cases hc : synthHasCore Γ ev y with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : HasChecked.label c = ℓ := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkHas_sound {s : Sig} {Γ : Ctx s} {ev : Has s} {y : BVar s .var} {ℓ : Label}
    (h : checkHas Γ ev y ℓ = true) : Has.HasType Γ ev y ℓ :=
  synthHas_sound (of_decide_eq_true h)

theorem synthMorphism_sound {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} (h : synthMorphism Γ src m = some Tel) :
    Γ ⊢ m : src ⇒ Tel := by
  unfold synthMorphism at h
  cases hc : synthMorCore Γ src m with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : MorChecked.tel c = Tel := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkMorphism_sound {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)} (h : checkMorphism Γ src m Tel = true) : Γ ⊢ m : src ⇒ Tel :=
  synthMorphism_sound (of_decide_eq_true h)

theorem synthAtom_sound {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : synthAtom Γ a = some T) : Γ ⊢ₐ a : T := by
  unfold synthAtom at h
  cases hc : synthAtomCore Γ a with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : AtomChecked.type c = T := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkAtom_sound {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : checkAtom Γ a T = true) : Γ ⊢ₐ a : T :=
  synthAtom_sound (of_decide_eq_true h)

theorem synthTmE_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {E : ETy s}
    (h : synthTmE Γ t = some E) : Γ ⊢ t :ᵉ E := by
  unfold synthTmE at h
  cases hc : synthTmCore Γ t with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : TmChecked.type c = E := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkTmE_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {E : ETy s}
    (h : checkTmE Γ t E = true) : Γ ⊢ t :ᵉ E :=
  synthTmE_sound (of_decide_eq_true h)

theorem synthTm_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : synthTm Γ t = some T) : Γ ⊢ t : T := by
  unfold synthTm at h
  cases hc : synthTmE Γ t with
  | none => rw [hc] at h; simp at h
  | some E =>
      cases E with
      | ty T0 =>
          rw [hc] at h
          have h2 : T0 = T := Option.some.inj h
          rw [← h2]
          exact synthTmE_sound hc
      | ex C0 T0 => rw [hc] at h; simp at h

theorem checkTm_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : checkTm Γ t T = true) : Γ ⊢ t : T :=
  checkTmE_sound h

theorem synthPAtom_sound {s : Sig} {Γ : Ctx s} {p : PAtom s} {E : ETy s}
    (h : synthPAtom Γ p = some E) : Γ ⊢ₚ p : E := by
  unfold synthPAtom at h
  cases hc : synthPAtomCore Γ p with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : PAtomChecked.type c = E := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkPAtom_sound {s : Sig} {Γ : Ctx s} {p : PAtom s} {E : ETy s}
    (h : checkPAtom Γ p E = true) : Γ ⊢ₚ p : E :=
  synthPAtom_sound (of_decide_eq_true h)

theorem synthELe_sound {s : Sig} {Γ : Ctx s} {ev : ELeCo s} {E E' : ETy s}
    (h : synthELe Γ ev = some (E, E')) : Γ ⊢ᵉ ev : E ≤ E' := by
  unfold synthELe at h
  cases hc : synthELeCore Γ ev with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact c.typing

theorem checkELe_sound {s : Sig} {Γ : Ctx s} {ev : ELeCo s} {E E' : ETy s}
    (h : checkELe Γ ev E E' = true) : Γ ⊢ᵉ ev : E ≤ E' :=
  synthELe_sound (of_decide_eq_true h)

theorem synthValueE_sound {s : Sig} {Γ : Ctx s} {v : Value s} {E : ETy s}
    (h : synthValueE Γ v = some E) : Γ ⊢ᵥᵉ v : E := by
  unfold synthValueE at h
  cases hc : synthValueECore Γ v with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : ValueEChecked.type c = E := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkValueE_sound {s : Sig} {Γ : Ctx s} {v : Value s} {E : ETy s}
    (h : checkValueE Γ v E = true) : Γ ⊢ᵥᵉ v : E :=
  synthValueE_sound (of_decide_eq_true h)

theorem synthValue_sound {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : synthValue Γ v = some T) : Γ ⊢ᵥ v : T := by
  unfold synthValue at h
  cases hc : synthValueCore Γ v with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : ValueChecked.type c = T := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkValue_sound {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : checkValue Γ v T = true) : Γ ⊢ᵥ v : T :=
  synthValue_sound (of_decide_eq_true h)

theorem checkFields_sound {s : Sig} {Γ : Ctx (s,x)} {F : Fields (s,x)} {A : CaptureSet s}
    (h : checkFields A Γ F = true) : Γ ⊢ᶠ[A] F := by
  obtain ⟨p, _⟩ := isSome_elim h
  exact p.down


/-! ## Smoke tests

The kernel is genuinely executable: these run in the kernel at elaboration
time. -/

section SmokeTests

private def smokeLabel : Label := .trm 0

/-- `λ(x : ⊤ ^ []). x`. -/
private def smokeId {s : Sig} : Tm (s,x) :=
  .val (.lam [] (⊤ ^ []) (.atom (.plain (.var .here))) (.refl [CapAtom.var .here]))

/-- The type of `smokeId`. -/
private def smokeIdTy {s : Sig} : Ty (s,x) := (Π(⊤ ^ []) (ETy.ty (⊤ ^ []))) ^ []

/-- A term of type `(self.ℓ) ^ []`, obtained by widening to `⊤` and then
unfolding the block definition. -/
private def smokeField {s : Sig} : Tm (s,x) :=
  .cast
    (.cast smokeId (.capt (.top (.pi (⊤ ^ []) (ETy.ty (⊤ ^ [])))) (.refl [])))
    (.capt (.eqToLe (.symm (.def .here smokeLabel)))
      (.elem [] [CapAtom.name .here smokeLabel]))

/-- Witnesses of the smoke literal: the single field is defined as `⊤`. -/
private def smokeW : Witnesses ([],x) := .cons .nil smokeLabel ⊤

/-- Capture witnesses of the smoke literal: none, so every label is `[]`. -/
private def smokeWc : CapWitnesses ([],x) := .nil

/-- An object literal with one witnessed field. -/
private def smokeObj : Value [] :=
  .obj [] smokeW smokeWc
    (.cons .nil smokeLabel smokeField (.elem [] [CapAtom.var .here]))

/-- The literal's precise type: one definition entry, one presence entry. -/
private def smokeObjTy : Ty [] := (μ (Telescope.ofLiteral smokeW smokeWc [smokeLabel])) ^ []

/-- A context whose only binder declares the field `ℓ`. -/
private def smokeCtx : Ctx ([],x) :=
  Ctx.nil.cons (.opaque ((μ (.cons .nil (.has smokeLabel))) ^ []))

/-- A context whose only binder has the empty object type. -/
private def smokeCtxNil : Ctx ([],x) := Ctx.nil.cons (.opaque ((μ .nil) ^ []))

/-- A context whose only binder holds a boxed object. -/
private def smokeCtxBox : Ctx ([],x) :=
  Ctx.nil.cons (.opaque ((□ ((μ (.cons .nil (.has smokeLabel))) ^ [])) ^ []))

example : checkValue Ctx.nil smokeObj smokeObjTy = true := by decide +kernel
example : synthValue Ctx.nil smokeObj = some smokeObjTy := by decide +kernel
example : checkValue Ctx.nil smokeObj ((μ .nil) ^ []) = false := by decide +kernel
example : checkValue Ctx.nil smokeObj ((μ (.cons .nil (.has smokeLabel))) ^ []) = false := by
  decide +kernel
example : checkTm smokeCtx smokeId smokeIdTy = true := by decide +kernel
example : checkTm smokeCtx smokeId ((Π(⊤ ^ []) (ETy.ty (⊥ ^ []))) ^ []) = false := by
  decide +kernel
example : checkShape Ctx.nil (.trans (.refl ⊤) (.top ⊤)) ⊤ ⊤ = true := by decide +kernel
example : checkLe Ctx.nil (.capt (.trans (.refl ⊤) (.top ⊤)) (.refl [])) (⊤ ^ []) (⊤ ^ []) = true := by
  decide +kernel

/-- Field evidence read off the binder's own object shape. -/
private def smokeHas : Has ([],x) :=
  .member (.var .here) (.refl (μ (.cons .nil (.has smokeLabel)))) 0

/-- A context whose only binder is transparent and declares the field. -/
private def smokeCtxTrans : Ctx ([],x) :=
  Ctx.nil.cons (.transparent (⊤ ^ []) (.cons .nil smokeLabel ⊤) .nil [smokeLabel])

/-- The type of `x.ℓ` at the binder `x = .here`. -/
private def smokeProjTy : Ty ([],x) :=
  (.sel .here smokeLabel) ^ [CapAtom.name .here smokeLabel]

example : checkTm smokeCtx (.proj (.var .here) smokeLabel smokeHas) smokeProjTy = true := by
  decide +kernel
example : checkTm smokeCtx (.proj (.var .here) (.trm 1) smokeHas)
    ((.sel .here (.trm 1)) ^ []) = false := by decide +kernel
example : checkTm smokeCtxTrans (.proj (.var .here) smokeLabel (.field smokeLabel))
    smokeProjTy = true := by decide +kernel
example : checkTm smokeCtx (.proj (.var .here) smokeLabel (.field smokeLabel))
    smokeProjTy = false := by decide +kernel
example : checkTm smokeCtx
    (.let (.atom (.plain (.var .here))) (.atom (.plain (.var (.there .here))))
      [CapAtom.var .here]
      (.refl [CapAtom.var (.there .here)]))
    ((μ (.cons .nil (.has smokeLabel))) ^ []) = true := by decide +kernel

-- The annotated object coercion synthesises both endpoints.
example : checkShape smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil)
    (μ (.cons .nil (.has smokeLabel))) (μ .nil) = true := by decide +kernel
example : synthShape smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil) =
    some (μ (.cons .nil (.has smokeLabel)), μ .nil) := by decide +kernel

-- A presence proposition is inherited from the source telescope by index.
example : synthShape smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 0)) =
    some (μ (.cons .nil (.has smokeLabel)), μ (.cons .nil (.has smokeLabel))) := by decide +kernel
example : synthShape smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 1)) = none := by
  decide +kernel

-- The annotated `Rec-I` synthesises its type.
example : checkAtom smokeCtxNil (.foldSelf .nil (.var .here)) ((μ .nil) ^ []) = true := by
  decide +kernel
example : synthAtom smokeCtxNil (.foldSelf .nil (.var .here)) = some ((μ .nil) ^ []) := by
  decide +kernel

/-- A source telescope with one inclusion and one equality. -/
private def smokeSrc : Telescope ([],x,x) := .nil ▹ ⊤ ⊑ ⊤ ▹ ⊤ ≐ ⊥

-- A template with empty sides copies the hole.
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊤)) := by decide +kernel
-- A hole must name an inclusion (`le`) or an equality (`eq`, `eqSym`).
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.le 1) .none)) = none := by
  decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.eq 0) .none)) = none := by
  decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.eq 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊥)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.le 2) .none)) = none := by
  decide +kernel
-- A closed side composes with the hole at a weakened closed shape.
example : synthShape smokeCtx (.obj smokeSrc (.le .nil (.some (.top ⊥)) (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) (.some (.top ⊤)))) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil (.some (.refl ⊥)) (.le 0) .none)) = none := by
  decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) (.some (.bot ⊤)))) = none := by
  decide +kernel
-- Equalities are copied, possibly flipped; inclusions are not equalities.
example : synthShape smokeCtx (.obj smokeSrc (.eq .nil 1 false)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ≐ ⊥)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.eq .nil 1 true)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤)) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrc (.eq .nil 0 false)) = none := by decide +kernel
-- Templates accumulate, oldest first.
example : synthShape smokeCtx (.obj smokeSrc (.le (.eq .nil 1 true) .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤ ▹ ⊤ ⊑ ⊤)) := by decide +kernel

/-- The smoke binder's telescope. -/
private def smokeTel : Telescope ([],x,x) := .nil ▹ ∋ smokeLabel

-- Pairing concatenates the targets of two coercions with the same source.
example : synthShape smokeCtx
    (.pair .nil smokeTel (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ smokeTel) := by decide +kernel
example : synthShape smokeCtx
    (.pair smokeTel smokeTel (.obj smokeTel (.has .nil 0)) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ (smokeTel ▹ ∋ smokeLabel)) := by decide +kernel
-- The annotations must match the targets, and the sources must agree.
example : synthShape smokeCtx
    (.pair smokeTel .nil (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) = none := by
  decide +kernel
example : synthShape smokeCtx
    (.pair .nil smokeTel (.obj .nil .nil) (.obj smokeTel (.has .nil 0))) = none := by decide +kernel

-- `And-I` concatenates two typings of the same root, at the same capture set.
example : synthAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here)) =
    some ((μ (smokeTel ▹ ∋ smokeLabel)) ^ []) := by decide +kernel
example : checkAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here))
    ((μ (smokeTel ▹ ∋ smokeLabel)) ^ []) = true := by decide +kernel
example : synthAtom smokeCtx (.both .nil smokeTel (.var .here) (.var .here)) = none := by
  decide +kernel

/-- Two binders of the same object type. -/
private def smokeCtx2 : Ctx ([],x,x) :=
  smokeCtx.cons (.opaque ((μ (.nil ▹ ∋ smokeLabel)) ^ []))

example : synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var .here)) =
    some ((μ (.nil ▹ ∋ smokeLabel ▹ ∋ smokeLabel)) ^ []) := by decide +kernel
example : synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var (.there .here))) =
    none := by decide +kernel

-- The capture family: `elem` is decided, `union` needs one target.
example : synthCap smokeCtx (.refl [.var .here]) = some ([.var .here], [.var .here]) := by
  decide +kernel
example : synthCap smokeCtx (.elem [] [.var .here]) = some ([], [.var .here]) := by decide +kernel
example : synthCap smokeCtx (.elem [.var .here] []) = none := by decide +kernel
example : synthCap smokeCtx (.union (.elem [] [.var .here]) (.refl [.var .here])) =
    some ([.var .here], [.var .here]) := by decide +kernel
example : synthCap smokeCtx (.union (.elem [] [.var .here]) (.refl [])) = none := by decide +kernel

-- The box former: `box` is a pure value, `unbox` a term that restores the
-- boxed capture set.
example : synthValue smokeCtx (.box (.var .here)) =
    some ((□ ((μ (.cons .nil (.has smokeLabel))) ^ [])) ^ []) := by decide +kernel
example : synthTm smokeCtxBox (.unbox (.var .here) [] (.refl [])) =
    some ((μ (.cons .nil (.has smokeLabel))) ^ []) := by decide +kernel
example : synthTm smokeCtxBox (.unbox (.var .here) [] (.elem [] [.var .here])) = none := by
  decide +kernel

-- The capture sort at an atom: `capvar` reads the atom's own capture set off
-- its type, and `recap` widens it.
example : synthCap smokeCtx (.capvar (.var .here)) = some ([CapAtom.var .here], []) := by
  decide +kernel
example : synthCap smokeCtx (.capvar (.recap (.var .here) (.refl [CapAtom.var .here]))) =
    some ([CapAtom.var .here], [CapAtom.var .here]) := by decide +kernel
example : synthAtom smokeCtx (.recap (.var .here) (.refl [CapAtom.var .here])) =
    some ((μ (.cons .nil (.has smokeLabel))) ^ [CapAtom.var .here]) := by decide +kernel
example : synthAtom smokeCtx (.recap (.var .here) (.refl [])) = none := by decide +kernel

-- A transparent binder's capture name resolves to its capture witness.
example : synthCapEq smokeCtxTrans (.defC .here smokeLabel) =
    some ([CapAtom.name .here smokeLabel], []) := by decide +kernel

/-- A source telescope with one subcapturing proposition and one capture
equality. -/
private def smokeSrcC : Telescope ([],x,x) :=
  .nil ▹ ([] ⊑ᶜ [CapAtom.var .here]) ▹ ([] ≐ᶜ [CapAtom.var .here])

-- A capture template with empty chains copies its hole.
example : synthShape smokeCtx (.obj smokeSrcC (.leC .nil .nil (.leC 0) .nil)) =
    some (μ smokeSrcC, μ (.nil ▹ ([] ⊑ᶜ [CapAtom.var .here]))) := by decide +kernel
-- A hole must name a capture proposition, in either direction for an equality.
example : synthShape smokeCtx (.obj smokeSrcC (.leC .nil .nil (.leC 1) .nil)) = none := by
  decide +kernel
example : synthShape smokeCtx (.obj smokeSrcC (.leC .nil .nil (.eqC 1) .nil)) =
    some (μ smokeSrcC, μ (.nil ▹ ([] ⊑ᶜ [CapAtom.var .here]))) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrcC (.leC .nil .nil (.eqSymC 1) .nil)) =
    some (μ smokeSrcC, μ (.nil ▹ ([CapAtom.var .here] ⊑ᶜ []))) := by decide +kernel
-- A capture equality is copied, possibly flipped.
example : synthShape smokeCtx (.obj smokeSrcC (.eqC .nil 1 false)) =
    some (μ smokeSrcC, μ (.nil ▹ ([] ≐ᶜ [CapAtom.var .here]))) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrcC (.eqC .nil 1 true)) =
    some (μ smokeSrcC, μ (.nil ▹ ([CapAtom.var .here] ≐ᶜ []))) := by decide +kernel
example : synthShape smokeCtx (.obj smokeSrcC (.eqC .nil 0 false)) = none := by decide +kernel
-- A side chain composes with the hole; an inclusion step may mention the self.
example : synthShape smokeCtx
    (.obj smokeSrcC (.leC .nil (.cons (.incl [] []) .nil) (.leC 0) .nil)) =
    some (μ smokeSrcC, μ (.nil ▹ ([] ⊑ᶜ [CapAtom.var .here]))) := by decide +kernel
example : synthShape smokeCtx
    (.obj smokeSrcC (.leC .nil .nil (.leC 0)
      (.cons (.incl [CapAtom.var .here] [CapAtom.var .here]) .nil))) =
    some (μ smokeSrcC, μ (.nil ▹ ([] ⊑ᶜ [CapAtom.var .here]))) := by decide +kernel
example : synthShape smokeCtx
    (.obj smokeSrcC (.leC .nil .nil (.leC 0) (.cons (.incl [] []) .nil))) = none := by
  decide +kernel

end SmokeTests

end FCdot

end Classifiers
