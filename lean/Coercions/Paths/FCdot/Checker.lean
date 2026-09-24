import Coercions.Paths.FCdot.Typing

namespace Paths

/-!
# Executable structural checker for FCdot

The checker validates fully annotated evidence.  It never searches: every
directed step, and every field-presence proof, is already present in the
input.

Since `LeCo.obj` carries its source telescope, `LeCo.pair` and `Atom.both`
their target telescopes, and `Atom.foldSelf` its target telescope, *every*
judgement of the evidence layer synthesises its outputs.  A template
`le pre h post` of a morphism is checked from its hole outwards: the hole is
read in the source telescope (`Hole.read?`), then each side is checked against
the endpoint next to the hole and synthesises the outer endpoint.  The kernel
is therefore a family of synthesising cores; the checking modes are synthesis
followed by a decidable comparison.

The kernels return the typing derivation itself, so soundness holds by
construction.  Completeness lives in `Coercions.FCdot.CheckerCompleteness`.
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

/-! ## Strengthening of types

`Ty.strengthen?` inverts `Ty.weaken`.  It is implemented as the action of a
partial renaming, which is what makes the traversal under binders work. -/

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

/-- A path under a partial renaming: every step survives or the path does
not. -/
def Path.rename? : Path s1 → PartialRename s1 s2 → Option (Path s2)
  | .var x, ρ => (ρ.var x).map Path.var
  | .sel p a, ρ => (p.rename? ρ).map (Path.sel · a)

theorem Path.rename?_complete :
    ∀ {s1 s2 : Sig} (p : Path s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (p.rename σ).rename? ρ = some p
  | _, _, .var x, ρ, σ, h => by
      simp only [Path.rename, Path.rename?]
      rw [(h (σ.var x) x).mpr rfl]
      rfl
  | _, _, .sel p a, ρ, σ, h => by
      simp only [Path.rename, Path.rename?, Path.rename?_complete p ρ σ h]
      rfl

theorem Path.rename?_sound :
    ∀ {s1 s2 : Sig} (p : Path s1) (q : Path s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → p.rename? ρ = some q → p = q.rename σ
  | _, _, .var x, q, ρ, σ, h, hq => by
      simp only [Path.rename?, Option.map_eq_some_iff] at hq
      obtain ⟨y, hy, hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [(h x y).mp hy]
  | _, _, .sel p a, q, ρ, σ, h, hq => by
      simp only [Path.rename?, Option.map_eq_some_iff] at hq
      obtain ⟨p', hp', hq⟩ := hq
      subst hq
      simp only [Path.rename]
      rw [← Path.rename?_sound p p' ρ σ h hp']

mutual

def Ty.rename? : Ty s1 → PartialRename s1 s2 → Option (Ty s2)
  | .bot, _ => some .bot
  | .sel p ℓ, ρ => (p.rename? ρ).map (fun q => .sel q ℓ)
  | .pi S T, ρ =>
      match S.rename? ρ, T.rename? ρ.lift with
      | some S', some T' => some (.pi S' T')
      | _, _ => none
  | .obj Tel, ρ =>
      match Tel.rename? ρ.lift with
      | some Tel' => some (.obj Tel')
      | none => none

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
  | .hasVal ℓ, _ => some (.hasVal ℓ)
  | .alias q, ρ => (q.rename? ρ).map Proposition.alias

def Telescope.rename? : Telescope s1 → PartialRename s1 s2 → Option (Telescope s2)
  | .nil, _ => some .nil
  | .cons Tel P, ρ =>
      match Tel.rename? ρ, P.rename? ρ with
      | some Tel', some P' => some (.cons Tel' P')
      | _, _ => none

end

mutual

theorem Ty.rename?_complete :
    ∀ {s1 s2 : Sig} (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (U.rename σ).rename? ρ = some U
  | _, _, .bot, _, _, _ => by simp [Ty.rename, Ty.rename?]
  | _, _, .sel p ℓ, ρ, σ, h => by
      simp only [Ty.rename, Ty.rename?, Path.rename?_complete p ρ σ h]
      rfl
  | _, _, .pi S T, ρ, σ, h => by
      simp only [Ty.rename, Ty.rename?]
      rw [Ty.rename?_complete S ρ σ h, Ty.rename?_complete T ρ.lift σ.lift h.lift]
  | _, _, .obj Tel, ρ, σ, h => by
      simp only [Ty.rename, Ty.rename?]
      rw [Telescope.rename?_complete Tel ρ.lift σ.lift h.lift]

theorem Proposition.rename?_complete :
    ∀ {s1 s2 : Sig} (P : Proposition s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (P.rename σ).rename? ρ = some P
  | _, _, .le S T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Ty.rename?_complete S ρ σ h, Ty.rename?_complete T ρ σ h]
  | _, _, .eq S T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Ty.rename?_complete S ρ σ h, Ty.rename?_complete T ρ σ h]
  | _, _, .has ℓ, _, _, _ => by simp [Proposition.rename, Proposition.rename?]
  | _, _, .bnd T, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?]
      rw [Ty.rename?_complete T ρ σ h]
  | _, _, .hasVal ℓ, _, _, _ => by simp [Proposition.rename, Proposition.rename?]
  | _, _, .alias q, ρ, σ, h => by
      simp only [Proposition.rename, Proposition.rename?, Path.rename?_complete q ρ σ h]
      rfl

theorem Telescope.rename?_complete :
    ∀ {s1 s2 : Sig} (Tel : Telescope s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → (Tel.rename σ).rename? ρ = some Tel
  | _, _, .nil, _, _, _ => by simp [Telescope.rename, Telescope.rename?]
  | _, _, .cons Tel P, ρ, σ, h => by
      simp only [Telescope.rename, Telescope.rename?]
      rw [Telescope.rename?_complete Tel ρ σ h, Proposition.rename?_complete P ρ σ h]

end


mutual

theorem Ty.rename?_sound :
    ∀ {s1 s2 : Sig} (T : Ty s1) (U : Ty s2) (ρ : PartialRename s1 s2) (σ : Rename s2 s1),
      ρ.Inverts σ → T.rename? ρ = some U → T = U.rename σ
  | _, _, .bot, U, _, _, _, hU => by
      simp only [Ty.rename?, Option.some.injEq] at hU
      subst hU; rfl
  | _, _, .sel p ℓ, U, ρ, σ, h, hU => by
      simp only [Ty.rename?, Option.map_eq_some_iff] at hU
      obtain ⟨q, hq, hU⟩ := hU
      subst hU
      simp only [Ty.rename]
      rw [← Path.rename?_sound p q ρ σ h hq]
  | _, _, .pi S T, U, ρ, σ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hS : S.rename? ρ with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hT : T.rename? ρ.lift with
        | none => rw [hS, hT] at hU; simp at hU
        | some T' =>
          rw [hS, hT] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          simp only [Ty.rename]
          rw [← Ty.rename?_sound S S' ρ σ h hS, ← Ty.rename?_sound T T' ρ.lift σ.lift h.lift hT]
  | _, _, .obj Tel, U, ρ, σ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hTel : Tel.rename? ρ.lift with
      | none => rw [hTel] at hU; simp at hU
      | some Tel' =>
        rw [hTel] at hU
        simp only [Option.some.injEq] at hU
        subst hU
        simp only [Ty.rename]
        rw [← Telescope.rename?_sound Tel Tel' ρ.lift σ.lift h.lift hTel]

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
          rw [← Ty.rename?_sound S S' ρ σ h hS, ← Ty.rename?_sound T T' ρ σ h hT]
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
          rw [← Ty.rename?_sound S S' ρ σ h hS, ← Ty.rename?_sound T T' ρ σ h hT]
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
        rw [← Ty.rename?_sound T T' ρ σ h hT]
  | _, _, .hasVal ℓ, Q, _, _, _, hQ => by
      simp only [Proposition.rename?, Option.some.injEq] at hQ
      subst hQ; rfl
  | _, _, .alias q, Q, ρ, σ, h, hQ => by
      simp only [Proposition.rename?, Option.map_eq_some_iff] at hQ
      obtain ⟨q', hq', hQ⟩ := hQ
      subst hQ
      simp only [Proposition.rename]
      rw [← Path.rename?_sound q q' ρ σ h hq']

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

/-- Strengthening: undo one weakening, if the innermost binder does not occur. -/
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

/-- Strengthening for paths: undo one weakening. -/
def Path.strengthen? {s : Sig} {k : Kind} (p : Path (s,,k)) : Option (Path s) :=
  p.rename? PartialRename.unshift

theorem Path.strengthen?_sound {s : Sig} {k : Kind} {p : Path (s,,k)} {q : Path s}
    (h : p.strengthen? = some q) : p = q.weaken :=
  Path.rename?_sound p q PartialRename.unshift Rename.succ PartialRename.unshift_inverts h

theorem Path.strengthen?_weaken {s : Sig} {k : Kind} (q : Path s) :
    (q.weaken (k := k)).strengthen? = some q :=
  Path.rename?_complete q PartialRename.unshift Rename.succ PartialRename.unshift_inverts

/-- Is this type the singleton object type of a path?  The checker asks it to
pick the binder a `let` introduces. -/
def Ty.sngl? {s : Sig} (T : Ty s) : Option (Path s) :=
  match T with
  | .obj (.cons .nil (.alias p)) => p.strengthen?
  | _ => none

theorem Ty.sngl?_sound {s : Sig} {T : Ty s} {q : Path s} (h : T.sngl? = some q) :
    T = Ty.snglOf q := by
  unfold Ty.sngl? at h
  split at h
  · next p =>
      rw [Ty.snglOf, ← Path.strengthen?_sound h]
  · exact absurd h (by simp)

@[simp] theorem Ty.sngl?_snglOf {s : Sig} (q : Path s) : (Ty.snglOf q).sngl? = some q := by
  simp [Ty.sngl?, Ty.snglOf, Path.strengthen?_weaken]

/-- The binder a `let` introduces: at a singleton the forwarding binder of the
let over a path, elsewhere the opaque binder.  `Tm.HasType.letPath` is the more
permissive of the two rules at a singleton, and `Tm.HasType.let` there is its
opaque twin through `Ctx.Refines.transparent`, so the checker always takes the
forwarding binder when it can. -/
def Binding.forLet {s : Sig} (T : Ty s) : Binding s :=
  match T.sngl? with
  | some q => Binding.fwdAt q
  | none => .opaque T

@[simp] theorem Binding.ty_forLet {s : Sig} (T : Ty s) : (Binding.forLet T).ty = T := by
  unfold Binding.forLet
  cases hq : T.sngl? with
  | none => rfl
  | some q =>
      simp only [Binding.fwdAt, Binding.ty]
      exact (Ty.sngl?_sound hq).symm

/-- Either `let` rule, read off the binder the checker picks. -/
theorem Tm.HasType.letOf {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} {u : Tm (s,x)}
    {U : Ty s} (ht : Γ ⊢ t : T) (hu : Γ.cons (Binding.forLet T) ⊢ u : U↑) :
    Γ ⊢ .let t u : U := by
  unfold Binding.forLet at hu
  cases hq : T.sngl? with
  | none => simp only [hq] at hu; exact .let ht hu
  | some q =>
      simp only [hq] at hu
      obtain rfl := Ty.sngl?_sound hq
      exact .letPath ht hu

/-- Strengthening, carrying the equation it establishes. -/
def Ty.strengthenW? {s : Sig} {k : Kind} (T : Ty (s,,k)) : Option { U : Ty s // T = U↑ } :=
  match witness? T.strengthen? with
  | some ⟨U, hU⟩ => some ⟨U, Ty.strengthen?_sound hU⟩
  | none => none

theorem Ty.strengthenW?_weaken {s : Sig} {k : Kind} (U : Ty s) :
    (U.weaken (k := k)).strengthenW? = some ⟨U, rfl⟩ := by
  simp only [Ty.strengthenW?, witness?_eq_some (Ty.strengthen?_weaken (k := k) U)]

/-! ## Checked results

Every kernel synthesises the outputs of its judgement and returns the
derivation it validated, so soundness is by construction. -/

structure LeChecked {s : Sig} (Γ : Ctx s) (ev : LeCo s) where
  source : Ty s
  target : Ty s
  typing : Γ ⊢ ev : source ≤ target

structure EqChecked {s : Sig} (Γ : Ctx s) (ev : EqCo s) where
  source : Ty s
  target : Ty s
  typing : Γ ⊢ ev : source ≡ target

structure HasChecked {s : Sig} (Γ : Ctx s) (ev : Has s) (p : Path s) where
  label : Label
  typing : Γ ⊢ ev : p ∋ label

/-- A morphism is checked against its *source* telescope (closed, over the self
binder): holes and presence propositions are read from it by index.  The target
telescope is synthesised. -/
structure MorChecked {s : Sig} (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) where
  tel : Telescope (s,x)
  typing : Γ ⊢ m : src ⇒ tel

/-- A template side checked against the endpoint next to the hole: for a
`pre` side the hole's left endpoint `X` is given and the outer source is
synthesised. -/
structure PreChecked {s : Sig} (Γ : Ctx s) (side : Side s) (X : Ty (s,x)) where
  source : Ty (s,x)
  typing : Side.HasType Γ side source X

/-- A `post` side: the hole's right endpoint `Y` is given and the outer target
is synthesised. -/
structure PostChecked {s : Sig} (Γ : Ctx s) (side : Side s) (Y : Ty (s,x)) where
  target : Ty (s,x)
  typing : Side.HasType Γ side Y target

structure AtomChecked {s : Sig} (Γ : Ctx s) (a : Atom s) where
  type : Ty s
  typing : Γ ⊢ₐ a : type

/-- A stable path synthesises its type, as an atom does. -/
structure PathChecked {s : Sig} (Γ : Ctx s) (P : PathCo s) where
  type : Ty s
  typing : Γ ⊢ᵖ P : type

/-- Alias evidence synthesises both of its paths. -/
structure AliasChecked {s : Sig} (Γ : Ctx s) (α : AliasCo s) where
  source : Path s
  target : Path s
  typing : Γ ⊢ α : source ≋ target

structure TmChecked {s : Sig} (Γ : Ctx s) (t : Tm s) where
  type : Ty s
  typing : Γ ⊢ t : type

structure ValueChecked {s : Sig} (Γ : Ctx s) (v : Value s) where
  type : Ty s
  typing : Γ ⊢ᵥ v : type

/-- Endpoints of a coercion. -/
abbrev Endpoints (s : Sig) := Ty s × Ty s

/-! ### Elimination at an atom

The three `member` rules share their premises.  Each is factored into a helper
that takes the *synthesised* data of the premises, so that the helper's only
case analyses are on plain variables and on a lookup that reduces
definitionally. -/

/-- `LeCo.member`: the `i`-th proposition of the object type `e` lands in, when
it is an inclusion. -/
def leMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : LeCo s} (i : Nat)
    {Sa : Ty s} (ha : Γ ⊢ₐ a : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (LeChecked Γ (.member a e i)) :=
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
def eqMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : LeCo s} (i : Nat)
    {Sa : Ty s} (ha : Γ ⊢ₐ a : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (EqChecked Γ (.member a e i)) :=
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

/-- `LeCo.memberP`: elimination at a stable path, at an inclusion. -/
def leMemberP {s : Sig} {Γ : Ctx s} {P : PathCo s} {e : LeCo s} (i : Nat)
    {Sa : Ty s} (hP : Γ ⊢ᵖ P : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (LeChecked Γ (.memberP P e i)) :=
  if hs : Se = Sa then
    match Te, he with
    | .obj Tel, he =>
        match Telescope.getAt? Tel i with
        | some ⟨.le S' T', hAt⟩ =>
            some ⟨S'.substPath P.path, T'.substPath P.path,
              .memberP hP (by subst hs; exact he) hAt⟩
        | _ => none
    | _, _ => none
  else none

/-- `EqCo.memberP`: the same, when the proposition is an equality. -/
def eqMemberP {s : Sig} {Γ : Ctx s} {P : PathCo s} {e : LeCo s} (i : Nat)
    {Sa : Ty s} (hP : Γ ⊢ᵖ P : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (EqChecked Γ (.memberP P e i)) :=
  if hs : Se = Sa then
    match Te, he with
    | .obj Tel, he =>
        match Telescope.getAt? Tel i with
        | some ⟨.eq S' T', hAt⟩ =>
            some ⟨S'.substPath P.path, T'.substPath P.path,
              .memberP hP (by subst hs; exact he) hAt⟩
        | _ => none
    | _, _ => none
  else none

/-- `Has.memberP`: the same, at a presence proposition. -/
def hasMemberP {s : Sig} {Γ : Ctx s} {P : PathCo s} {e : LeCo s} (i : Nat) (r : Path s)
    {Sa : Ty s} (hP : Γ ⊢ᵖ P : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (HasChecked Γ (.memberP P e i) r) :=
  if hx : P.path = r then
    if hs : Se = Sa then
      match Te, he with
      | .obj Tel, he =>
          match Telescope.getAt? Tel i with
          | some ⟨.has ℓ, hAt⟩ =>
              some ⟨ℓ, by subst hx; exact .memberP hP (by subst hs; exact he) hAt⟩
          | _ => none
      | _, _ => none
    else none
  else none

/-- `AliasCo.member`: the alias a view carries. -/
def aliasMember {s : Sig} {Γ : Ctx s} {P : PathCo s} {e : LeCo s} (i : Nat)
    {Sa : Ty s} (hP : Γ ⊢ᵖ P : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (AliasChecked Γ (.member P e i)) :=
  if hs : Se = Sa then
    match Te, he with
    | .obj Tel, he =>
        match Telescope.getAt? Tel i with
        | some ⟨.alias q, hAt⟩ =>
            some ⟨P.path, q.substPath P.path, .member hP (by subst hs; exact he) hAt⟩
        | _ => none
    | _, _ => none
  else none

/-- `PathCo.sel`: one field step, licensed by a stable presence. -/
def pathSel {s : Sig} {Γ : Ctx s} {P : PathCo s} (a : Label) (i : Nat)
    {Sa : Ty s} (hP : Γ ⊢ᵖ P : Sa) : Option (PathChecked Γ (.sel P a i)) :=
  match Sa, hP with
  | .obj Tel, hP =>
      match Telescope.getAt? Tel i with
      | some ⟨.hasVal a', hAt⟩ =>
          if h : a' = a then some ⟨P.path ∙ a, by subst h; exact .sel hP hAt⟩ else none
      | _ => none
  | _, _ => none

/-- `PathCo.node`: the premise is decided by reading `Ctx.nodeBlock` and
comparing the node's witnesses and labels, which blocks have decidable
equality for.  The path must be a field step. -/
def pathNode {s : Sig} (Γ : Ctx s) (p : Path s) (W : Witnesses (s,x)) (ls vls : List Label) :
    Option (PathChecked Γ (.node p W ls vls)) :=
  if hs : p.isSel = true then
    match h : Γ.nodeBlock p with
    | some (.obj W' ls' vls' ch) =>
        if hW : W' = W.substPath p ∧ ls' = ls ∧ vls' = vls then
          some ⟨μ (Telescope.ofLiteral W ls vls), .node (ch := ch) hs (by
            rw [h, hW.1, hW.2.1, hW.2.2])⟩
        else none
    | _ => none
  else none

/-- `Has.member`: the same, when the proposition is a field declaration.  The
subject path is checked, the label synthesised. -/
def hasMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : LeCo s} (i : Nat) (y : Path s)
    {Sa : Ty s} (ha : Γ ⊢ₐ a : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (HasChecked Γ (.member a e i) y) :=
  if hx : (Path.var a.root) = y then
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

/-- `LeCo.bound`: the annotated object type is below the type of its `i`-th
proposition, which must be a bound of a (weakened) closed type. -/
def leBound {s : Sig} {Γ : Ctx s} (Tel : Telescope (s,x)) (i : Nat) :
    Option (LeChecked Γ (.bound Tel i)) :=
  match Telescope.getAt? Tel i with
  | some ⟨.bnd X, hAt⟩ =>
      match X.strengthenW? with
      | some ⟨T, hT⟩ => some ⟨μ Tel, T, .bound (by rw [hT] at hAt; exact hAt)⟩
      | none => none
  | _ => none

/-- `Morphism.bnd`: a target bound proven by a closed coercion out of the
source object type. -/
def morBnd {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} {e : LeCo s}
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (MorChecked Γ src (.bnd m e)) :=
  if hs : Se = μ src then
    some ⟨Tel ▹ ⊑ Te↑, .bnd hm (by rw [← hs]; exact he)⟩
  else none

/-- `Morphism.hasVal`: a stable presence copied from the source by index. -/
def morHasVal {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.hasVal m j)) :=
  match Telescope.getAt? src j with
  | some ⟨.hasVal ℓ, hAt⟩ => some ⟨Tel ▹ ∋ᵛ ℓ, .hasVal hm hAt⟩
  | _ => none

/-- `Morphism.hasOfVal`: a presence read off a source stable presence. -/
def morHasOfVal {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.hasOfVal m j)) :=
  match Telescope.getAt? src j with
  | some ⟨.hasVal ℓ, hAt⟩ => some ⟨Tel ▹ ∋ ℓ, .hasOfVal hm hAt⟩
  | _ => none

/-- `Morphism.aliasCopy`: an alias copied from the source by index. -/
def morAliasCopy {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)} {m : Morphism s} (j : Nat)
    {Tel : Telescope (s,x)} (hm : Γ ⊢ m : src ⇒ Tel) :
    Option (MorChecked Γ src (.aliasCopy m j)) :=
  match Telescope.getAt? src j with
  | some ⟨.alias q, hAt⟩ => some ⟨Tel ▹ ≈ q, .aliasCopy hm hAt⟩
  | _ => none

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
inductive Hole.Reads (src : Telescope (s,x)) : Hole → Ty (s,x) → Ty (s,x) → Prop where
  | le : src ∋ (j ↦ X ⊑ Y) → Hole.Reads src (.le j) X Y
  | eq : src ∋ (j ↦ X ≐ Y) → Hole.Reads src (.eq j) X Y
  | eqSym : src ∋ (j ↦ Y ≐ X) → Hole.Reads src (.eqSym j) X Y

/-- The template rule, uniformly over the reading of the hole. -/
theorem Morphism.HasType.leOfReads {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s}
    {pre post : Side s} {h : Hole} {S X Y T : Ty (s,x)}
    (hm : Γ ⊢ m : src ⇒ Tel) (hr : Hole.Reads src h X Y)
    (hpre : Side.HasType Γ pre S X) (hpost : Side.HasType Γ post Y T) :
    Γ ⊢ .le m pre h post : src ⇒ Tel ▹ S ⊑ T := by
  cases hr with
  | le hAt => exact .le hm hAt hpre hpost
  | eq hAt => exact .leEq hm hAt hpre hpost
  | eqSym hAt => exact .leEqSym hm hAt hpre hpost

/-- Read a hole in the source telescope, with the proof of what it proves. -/
def Hole.read? (src : Telescope (s,x)) :
    (h : Hole) → Option { XY : Ty (s,x) × Ty (s,x) // Hole.Reads src h XY.1 XY.2 }
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

theorem Hole.read?_of_Reads {src : Telescope (s,x)} {h : Hole} {X Y : Ty (s,x)}
    (hr : Hole.Reads src h X Y) : Hole.read? src h = some ⟨(X, Y), hr⟩ := by
  cases hr with
  | le hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]
  | eq hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]
  | eqSym hAt => simp [Hole.read?, Telescope.getAt?_of_At hAt]

/-- `LeCo.pair`: two coercions with the same source, into the annotated object
types. -/
def lePair {s : Sig} {Γ : Ctx s} {e f : LeCo s} (Tel₁ Tel₂ : Telescope (s,x))
    {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) {Sf Tf : Ty s} (hf : Γ ⊢ f : Sf ≤ Tf) :
    Option (LeChecked Γ (.pair Tel₁ Tel₂ e f)) :=
  if hs : Sf = Se then
    if h1 : Te = μ Tel₁ then
      if h2 : Tf = μ Tel₂ then
        some ⟨Se, μ (Tel₁ ++ Tel₂), by subst hs; subst h1; subst h2; exact .pair he hf⟩
      else none
    else none
  else none

/-- `And-I`: two typings of the same root, at the annotated object types. -/
def atomBoth {s : Sig} {Γ : Ctx s} {a b : Atom s} (Tel₁ Tel₂ : Telescope (s,x))
    {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta) {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) :
    Option (AtomChecked Γ (.both Tel₁ Tel₂ a b)) :=
  if h1 : Ta = μ Tel₁ then
    if h2 : Tb = μ Tel₂ then
      if hr : b.root = a.root then
        some ⟨μ (Tel₁ ++ Tel₂), by subst h1; subst h2; exact .both ha hb hr⟩
      else none
    else none
  else none

/-- `Rec-E`: the atom's type must be an object type. -/
def atomUnfold {s : Sig} {Γ : Ctx s} {b : Atom s} {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) :
    Option (AtomChecked Γ (.unfoldSelf b)) :=
  match Tb, hb with
  | .obj Tel, hb => some ⟨.obj (Tel⟦b.root⟧)↑, .unfoldSelf hb⟩
  | _, _ => none

/-- Application: the function's type must be an arrow whose domain is the
argument's type. -/
def tmApp {s : Sig} {Γ : Ctx s} {a b : Atom s} {Ta : Ty s} (ha : Γ ⊢ₐ a : Ta)
    {Tb : Ty s} (hb : Γ ⊢ₐ b : Tb) : Option (TmChecked Γ (.app a b)) :=
  match Ta, ha with
  | .pi S T, ha =>
      if h : Tb = S then some ⟨T⟦b.root⟧, .app ha (by subst h; exact hb)⟩ else none
  | _, _ => none

/-! ## Evidence kernel

Every core synthesises: the source and target of a coercion, the label of a
field-presence proof, the target telescope of a morphism, the type of an atom. -/

mutual

def synthLeCore {s : Sig} (Γ : Ctx s) (ev : LeCo s) : Option (LeChecked Γ ev) :=
  match ev with
  | .refl T => some ⟨T, T, .refl⟩
  | .top T => some ⟨T, .top, .top⟩
  | .bot T => some ⟨.bot, T, .bot⟩
  | .eqToLe φ => do
      let c ← synthEqCore Γ φ
      some ⟨c.source, c.target, .eqToLe c.typing⟩
  | .trans e f => do
      let ce ← synthLeCore Γ e
      let cf ← synthLeCore Γ f
      if h : ce.target = cf.source then
        some ⟨ce.source, cf.target, .trans ce.typing (by rw [h]; exact cf.typing)⟩
      else none
  | .pi e f => do
      let ce ← synthLeCore Γ e
      let cf ← synthLeCore (Γ.cons (.opaque ce.source)) f
      some ⟨.pi ce.target cf.source, .pi ce.source cf.target, .pi ce.typing cf.typing⟩
  | .obj Tel m => do
      let cm ← synthMorCore Γ Tel m
      some ⟨μ Tel, μ cm.tel, .obj cm.typing⟩
  | .pair Tel₁ Tel₂ e f => do
      let ce ← synthLeCore Γ e
      let cf ← synthLeCore Γ f
      lePair Tel₁ Tel₂ ce.typing cf.typing
  | .bound Tel i => leBound Tel i
  | .intoBnd e => do
      let ce ← synthLeCore Γ e
      some ⟨ce.source, μ (.nil ▹ ⊑ ce.target↑), .intoBnd ce.typing⟩
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthLeCore Γ e
      leMember i ca.typing ce.typing
  | .memberP P e i => do
      let cP ← synthPathCore Γ P
      let ce ← synthLeCore Γ e
      leMemberP i cP.typing ce.typing

def synthEqCore {s : Sig} (Γ : Ctx s) (ev : EqCo s) : Option (EqChecked Γ ev) :=
  match ev with
  | .refl T => some ⟨T, T, .refl⟩
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
      let ce ← synthLeCore Γ e
      eqMember i ca.typing ce.typing
  | .defP p ℓ =>
      match witness? (Γ.lookupDefP p ℓ) with
      | some ⟨W, hW⟩ => some ⟨.sel p ℓ, W, .defP hW⟩
      | none => none
  | .memberP P e i => do
      let cP ← synthPathCore Γ P
      let ce ← synthLeCore Γ e
      eqMemberP i cP.typing ce.typing

def synthHasCore {s : Sig} (Γ : Ctx s) (ev : Has s) (y : Path s) :
    Option (HasChecked Γ ev y) :=
  match ev with
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthLeCore Γ e
      hasMember i y ca.typing ce.typing
  | .memberP P e i => do
      let cP ← synthPathCore Γ P
      let ce ← synthLeCore Γ e
      hasMemberP i y cP.typing ce.typing
  | .field ℓ =>
      match y with
      | .var z =>
          match witness? (Γ.lookupFields z) with
          | some ⟨Fs, hF⟩ => if hm : ℓ ∈ Fs then some ⟨ℓ, .field hF hm⟩ else none
          | none => none
      | .sel _ _ => none

/-- A `pre` side, checked against the hole's left endpoint `X`: `none` leaves
it in place, `some e` needs `e` to land in the closed type `X` weakens. -/
def checkPreCore {s : Sig} (Γ : Ctx s) (side : Side s) (X : Ty (s,x)) :
    Option (PreChecked Γ side X) :=
  match side with
  | .none => some ⟨X, .none⟩
  | .bot X' => if h : X = X' then some ⟨⊥, by subst h; exact .bot⟩ else none
  | .top X' => if h : X = ⊤ then some ⟨X', by subst h; exact .top⟩ else none
  | .some e => do
      let ce ← synthLeCore Γ e
      if h : X = ce.target↑ then some ⟨ce.source↑, by subst h; exact .some ce.typing⟩
      else none

/-- A `post` side, checked against the hole's right endpoint `Y`. -/
def checkPostCore {s : Sig} (Γ : Ctx s) (side : Side s) (Y : Ty (s,x)) :
    Option (PostChecked Γ side Y) :=
  match side with
  | .none => some ⟨Y, .none⟩
  | .bot X' => if h : Y = ⊥ then some ⟨X', by subst h; exact .bot⟩ else none
  | .top X' => if h : Y = X' then some ⟨⊤, by subst h; exact .top⟩ else none
  | .some e => do
      let ce ← synthLeCore Γ e
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
      let ce ← synthLeCore Γ e
      morBnd cm.typing ce.typing
  | .hasVal m j => do
      let cm ← synthMorCore Γ src m
      morHasVal j cm.typing
  | .hasOfVal m j => do
      let cm ← synthMorCore Γ src m
      morHasOfVal j cm.typing
  | .aliasCopy m j => do
      let cm ← synthMorCore Γ src m
      morAliasCopy j cm.typing

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
      if h : cb.type = .obj (Tel⟦b.root⟧)↑ then
        some ⟨.obj Tel, .foldSelf (by rw [← h]; exact cb.typing)⟩
      else none
  | .both Tel₁ Tel₂ a b => do
      let ca ← synthAtomCore Γ a
      let cb ← synthAtomCore Γ b
      atomBoth Tel₁ Tel₂ ca.typing cb.typing
  | .sngl b q α => do
      let cb ← synthAtomCore Γ b
      let cα ← synthAliasCore Γ α
      if h1 : cα.source = Path.var b.root then
        if h2 : cα.target = q then
          some ⟨Ty.snglOf q, .sngl cb.typing (by rw [← h1, ← h2]; exact cα.typing)⟩
        else none
      else none

def synthPathCore {s : Sig} (Γ : Ctx s) (P : PathCo s) : Option (PathChecked Γ P) :=
  match P with
  | .var y => some ⟨Γ.lookupTy y, .var⟩
  | .sel Q a i => do
      let cQ ← synthPathCore Γ Q
      pathSel a i cQ.typing
  | .cast Q e => do
      let cQ ← synthPathCore Γ Q
      let ce ← synthLeCore Γ e
      if h : ce.source = cQ.type then
        some ⟨ce.target, .cast cQ.typing (by rw [← h]; exact ce.typing)⟩
      else none
  | .alias α p Q => do
      let cα ← synthAliasCore Γ α
      let cQ ← synthPathCore Γ Q
      if h1 : cα.source = p then
        if h2 : cα.target = Q.path then
          some ⟨cQ.type, .alias (by rw [← h1, ← h2]; exact cα.typing) cQ.typing⟩
        else none
      else none
  | .unfoldSelf Q => do
      let cQ ← synthPathCore Γ Q
      match cQ.type, cQ.typing with
      | .obj Tel, hQ => some ⟨.obj ((Tel.substPath Q.path)↑), .unfoldSelf hQ⟩
      | _, _ => none
  | .foldSelf Tel Q => do
      let cQ ← synthPathCore Γ Q
      if h : cQ.type = .obj ((Tel.substPath Q.path)↑) then
        some ⟨.obj Tel, .foldSelf (by rw [← h]; exact cQ.typing)⟩
      else none
  | .both Tel₁ Tel₂ Q R => do
      let cQ ← synthPathCore Γ Q
      let cR ← synthPathCore Γ R
      if h1 : cQ.type = μ Tel₁ then
        if h2 : cR.type = μ Tel₂ then
          if hr : R.path = Q.path then
            some ⟨μ (Tel₁ ++ Tel₂), by
              exact .both (h1 ▸ cQ.typing) (h2 ▸ cR.typing) hr⟩
          else none
        else none
      else none
  | .sngl Q q α => do
      let cQ ← synthPathCore Γ Q
      let cα ← synthAliasCore Γ α
      if h1 : cα.source = Q.path then
        if h2 : cα.target = q then
          some ⟨Ty.snglOf q, .sngl cQ.typing (by rw [← h1, ← h2]; exact cα.typing)⟩
        else none
      else none
  | .node p W ls vls => pathNode Γ p W ls vls

def synthAliasCore {s : Sig} (Γ : Ctx s) (α : AliasCo s) : Option (AliasChecked Γ α) :=
  match α with
  | .refl p => some ⟨p, p, .refl⟩
  | .symm β => do
      let cβ ← synthAliasCore Γ β
      some ⟨cβ.target, cβ.source, .symm cβ.typing⟩
  | .trans β γ => do
      let cβ ← synthAliasCore Γ β
      let cγ ← synthAliasCore Γ γ
      if h : cβ.target = cγ.source then
        some ⟨cβ.source, cγ.target, .trans cβ.typing (by rw [h]; exact cγ.typing)⟩
      else none
  | .sel β a => do
      let cβ ← synthAliasCore Γ β
      some ⟨.sel cβ.source a, .sel cβ.target a, .sel cβ.typing⟩
  | .member P e i => do
      let cP ← synthPathCore Γ P
      let ce ← synthLeCore Γ e
      aliasMember i cP.typing ce.typing

end

/-! ## Term kernel -/

mutual

def synthTmCore {s : Sig} (Γ : Ctx s) (t : Tm s) : Option (TmChecked Γ t) :=
  match t with
  | .atom a => do
      let ca ← synthAtomCore Γ a
      some ⟨ca.type, .atom ca.typing⟩
  | .val v => do
      let cv ← synthValueCore Γ v
      some ⟨cv.type, .val cv.typing⟩
  | .app a b => do
      let ca ← synthAtomCore Γ a
      let cb ← synthAtomCore Γ b
      tmApp ca.typing cb.typing
  | .proj a ℓ h => do
      let ca ← synthAtomCore Γ a
      let ch ← synthHasCore Γ h (Path.var a.root)
      if hl : ch.label = ℓ then
        some ⟨.sel (Path.var a.root) ℓ, .proj ca.typing (by rw [← hl]; exact ch.typing)⟩
      else none
  | .let t u => do
      let ct ← synthTmCore Γ t
      let cu ← synthTmCore (Γ.cons (Binding.forLet ct.type)) u
      match cu.type.strengthenW? with
      | some ⟨U, hU⟩ => some ⟨U, .letOf ct.typing (by rw [← hU]; exact cu.typing)⟩
      | none => none
  | .cast t e => do
      let ct ← synthTmCore Γ t
      let ce ← synthLeCore Γ e
      if h : ce.source = ct.type then
        some ⟨ce.target, .cast ct.typing (by rw [← h]; exact ce.typing)⟩
      else none

def synthValueCore {s : Sig} (Γ : Ctx s) (v : Value s) : Option (ValueChecked Γ v) :=
  match v with
  | .lam S t => do
      let ct ← synthTmCore (Γ.cons (.opaque S)) t
      some ⟨.pi S ct.type, .lam ct.typing⟩
  | .obj W F => do
      let Tel := Telescope.ofLiteral W F.labels F.valLabels
      let pF ← checkFieldsCore
        (Γ.cons (.transparent (.obj Tel)
          (.obj W F.labels F.valLabels (F.children (.var .here))))) F
      some ⟨.obj Tel, .obj pF.down⟩
  | .cast v e => do
      let cv ← synthValueCore Γ v
      let ce ← synthLeCore Γ e
      if h : ce.source = cv.type then
        some ⟨ce.target, .cast cv.typing (by rw [← h]; exact ce.typing)⟩
      else none

def checkFieldsCore {s : Sig} (Γ : Ctx (s,x)) (F : Fields (s,x)) :
    Option (PLift (Γ ⊢ᶠ F)) :=
  match F with
  | .nil => some ⟨.nil⟩
  | .cons F ℓ t => do
      let pF ← checkFieldsCore Γ F
      let ct ← synthTmCore Γ t
      if h : ct.type = .sel (Path.var .here) ℓ then
        some ⟨.cons pF.down (by rw [← h]; exact ct.typing)⟩
      else none

end

/-! ## Public interface

Each judgement has a synthesising mode and a checking mode; the checking mode
compares the synthesised outputs with the expected ones. -/

/-- Synthesise both endpoints of an inclusion. -/
def synthLe {s : Sig} (Γ : Ctx s) (ev : LeCo s) : Option (Endpoints s) :=
  (synthLeCore Γ ev).map fun c => (c.source, c.target)

def checkLe {s : Sig} (Γ : Ctx s) (ev : LeCo s) (S T : Ty s) : Bool :=
  decide (synthLe Γ ev = some (S, T))

def synthEq {s : Sig} (Γ : Ctx s) (ev : EqCo s) : Option (Endpoints s) :=
  (synthEqCore Γ ev).map fun c => (c.source, c.target)

def checkEq {s : Sig} (Γ : Ctx s) (ev : EqCo s) (S T : Ty s) : Bool :=
  decide (synthEq Γ ev = some (S, T))

/-- Synthesise the label a field-presence proof establishes for `y`. -/
def synthHas {s : Sig} (Γ : Ctx s) (ev : Has s) (y : Path s) : Option Label :=
  (synthHasCore Γ ev y).map HasChecked.label

def checkHas {s : Sig} (Γ : Ctx s) (ev : Has s) (y : Path s) (ℓ : Label) : Bool :=
  decide (synthHas Γ ev y = some ℓ)

/-- Synthesise the type of a stable path. -/
def synthPath {s : Sig} (Γ : Ctx s) (P : PathCo s) : Option (Ty s) :=
  (synthPathCore Γ P).map PathChecked.type

def checkPath {s : Sig} (Γ : Ctx s) (P : PathCo s) (T : Ty s) : Bool :=
  decide (synthPath Γ P = some T)

/-- Synthesise both paths of an alias. -/
def synthAlias {s : Sig} (Γ : Ctx s) (α : AliasCo s) : Option (Path s × Path s) :=
  (synthAliasCore Γ α).map fun c => (c.source, c.target)

def checkAlias {s : Sig} (Γ : Ctx s) (α : AliasCo s) (p q : Path s) : Bool :=
  decide (synthAlias Γ α = some (p, q))

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

def synthTm {s : Sig} (Γ : Ctx s) (t : Tm s) : Option (Ty s) :=
  (synthTmCore Γ t).map TmChecked.type

def checkTm {s : Sig} (Γ : Ctx s) (t : Tm s) (T : Ty s) : Bool :=
  decide (synthTm Γ t = some T)

def synthValue {s : Sig} (Γ : Ctx s) (v : Value s) : Option (Ty s) :=
  (synthValueCore Γ v).map ValueChecked.type

def checkValue {s : Sig} (Γ : Ctx s) (v : Value s) (T : Ty s) : Bool :=
  decide (synthValue Γ v = some T)

def checkFields {s : Sig} (Γ : Ctx (s,x)) (F : Fields (s,x)) : Bool :=
  (checkFieldsCore Γ F).isSome

/-! ## Soundness

Each kernel already carries the derivation, so soundness is extraction. -/

private theorem isSome_elim {α : Type} {o : Option α} (h : o.isSome = true) : ∃ v, o = some v := by
  cases o with
  | none => simp at h
  | some v => exact ⟨v, rfl⟩

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

theorem synthEq_sound {s : Sig} {Γ : Ctx s} {ev : EqCo s} {S T : Ty s}
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

theorem checkEq_sound {s : Sig} {Γ : Ctx s} {ev : EqCo s} {S T : Ty s}
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

theorem synthTm_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : synthTm Γ t = some T) : Γ ⊢ t : T := by
  unfold synthTm at h
  cases hc : synthTmCore Γ t with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      have h2 : TmChecked.type c = T := Option.some.inj h
      rw [← h2]
      exact c.typing

theorem checkTm_sound {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : checkTm Γ t T = true) : Γ ⊢ t : T :=
  synthTm_sound (of_decide_eq_true h)

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

theorem checkFields_sound {s : Sig} {Γ : Ctx (s,x)} {F : Fields (s,x)}
    (h : checkFields Γ F = true) : Γ ⊢ᶠ F := by
  obtain ⟨p, _⟩ := isSome_elim h
  exact p.down


/-! ## Smoke tests

The kernel is genuinely executable: these run at elaboration time. -/

section SmokeTests

private def smokeLabel : Label := .trm 0

/-- `λ(x : ⊤). x`. -/
private def smokeId : Tm ([],x) := .val (.lam .top (.atom (.var .here)))

/-- A term of type `self.ℓ`, obtained by unfolding the block definition. -/
private def smokeField : Tm ([],x) :=
  .cast (.cast smokeId (.top (.pi .top .top))) (.eqToLe (.symm (.def .here smokeLabel)))

/-- Witnesses of the smoke literal: the single field is defined as `⊤`. -/
private def smokeW : Witnesses ([],x) := .cons .nil smokeLabel .top

/-- An object literal with one witnessed field. -/
private def smokeObj : Value [] := .obj smokeW (.cons .nil smokeLabel smokeField)

/-- The literal's precise type: one definition entry, one presence entry.  The field
holds a lambda, so it is not stable and there is no `∋ᵛ` entry (decision 24). -/
private def smokeObjTy : Ty [] := .obj (Telescope.ofLiteral smokeW [smokeLabel] [])

/-- A context whose only binder declares the field `ℓ`. -/
private def smokeCtx : Ctx ([],x) := Ctx.nil.cons (.opaque (.obj (.cons .nil (.has smokeLabel))))

/-- A context whose only binder has the empty object type. -/
private def smokeCtxNil : Ctx ([],x) := Ctx.nil.cons (.opaque (.obj .nil))

example : (checkValue Ctx.nil smokeObj smokeObjTy) = true := by decide +kernel
example : synthValue Ctx.nil smokeObj = some smokeObjTy := by decide +kernel
example : (checkValue Ctx.nil smokeObj (.obj .nil)) = false := by decide +kernel
example : (checkValue Ctx.nil smokeObj (.obj (.cons .nil (.has smokeLabel)))) = false := by decide +kernel
example : (checkTm smokeCtx smokeId (.pi .top .top)) = true := by decide +kernel
example : (checkTm smokeCtx smokeId (.pi .top .bot)) = false := by decide +kernel
example : (checkLe Ctx.nil (.trans (.refl .top) (.top .top)) .top .top) = true := by decide +kernel
/-- Field evidence read off the binder's own object type. -/
private def smokeHas : Has ([],x) :=
  .member (.var .here) (.refl (.obj (.cons .nil (.has smokeLabel)))) 0

/-- A context whose only binder is transparent and declares the field. -/
private def smokeCtxTrans : Ctx ([],x) :=
  Ctx.nil.cons (.transparent .top (.obj (.cons .nil smokeLabel .top) [smokeLabel] [] .nil))

example : checkTm smokeCtx (.proj (.var .here) smokeLabel smokeHas)
    (.sel (Path.var .here) smokeLabel) = true := by decide +kernel
example : checkTm smokeCtx (.proj (.var .here) (.trm 1) smokeHas)
    (.sel (Path.var .here) (.trm 1)) = false := by decide +kernel
example : (checkTm smokeCtxTrans (.proj (.var .here) smokeLabel (.field smokeLabel))
    (.sel (Path.var .here) smokeLabel)) = true := by decide +kernel
example : (checkTm smokeCtx (.proj (.var .here) smokeLabel (.field smokeLabel))
    (.sel (Path.var .here) smokeLabel)) = false := by decide +kernel
example : (checkTm smokeCtx (.let (.atom (.var .here)) (.atom (.var (.there .here))))
    (.obj (.cons .nil (.has smokeLabel)))) = true := by decide +kernel

-- The annotated object coercion synthesises both endpoints.
example : (checkLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil)
    (.obj (.cons .nil (.has smokeLabel))) (.obj .nil)) = true := by decide +kernel
example : synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil) =
    some (.obj (.cons .nil (.has smokeLabel)), .obj .nil) := by decide +kernel

-- A presence proposition is inherited from the source telescope by index.
example : synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 0)) =
    some (.obj (.cons .nil (.has smokeLabel)), .obj (.cons .nil (.has smokeLabel))) := by decide +kernel
example : synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 1)) = none := by decide +kernel

-- The annotated `Rec-I` synthesises its type.
example : (checkAtom smokeCtxNil (.foldSelf .nil (.var .here)) (.obj .nil)) = true := by decide +kernel
example : synthAtom smokeCtxNil (.foldSelf .nil (.var .here)) = some (.obj .nil) := by decide +kernel

/-- A source telescope with one inclusion and one equality. -/
private def smokeSrc : Telescope ([],x,x) := .nil ▹ ⊤ ⊑ ⊤ ▹ ⊤ ≐ ⊥

-- A template with empty sides copies the hole.
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊤)) := by decide +kernel
-- A hole must name an inclusion (`le`) or an equality (`eq`, `eqSym`).
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 1) .none)) = none := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eq 0) .none)) = none := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eq 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊥)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 2) .none)) = none := by decide +kernel
-- A closed side composes with the hole at a weakened closed type.
example : synthLe smokeCtx (.obj smokeSrc (.le .nil (.some (.top ⊥)) (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) (.some (.top ⊤)))) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil (.some (.refl ⊥)) (.le 0) .none)) = none := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) (.some (.bot ⊤)))) = none := by decide +kernel
-- Equalities are copied, possibly flipped; inclusions are not equalities.
example : synthLe smokeCtx (.obj smokeSrc (.eq .nil 1 false)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ≐ ⊥)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.eq .nil 1 true)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤)) := by decide +kernel
example : synthLe smokeCtx (.obj smokeSrc (.eq .nil 0 false)) = none := by decide +kernel
-- Templates accumulate, oldest first.
example : synthLe smokeCtx (.obj smokeSrc (.le (.eq .nil 1 true) .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤ ▹ ⊤ ⊑ ⊤)) := by decide +kernel

/-- The smoke binder's telescope. -/
private def smokeTel : Telescope ([],x,x) := .nil ▹ ∋ smokeLabel

-- Pairing concatenates the targets of two coercions with the same source.
example : synthLe smokeCtx
    (.pair .nil smokeTel (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ smokeTel) := by decide +kernel
example : synthLe smokeCtx
    (.pair smokeTel smokeTel (.obj smokeTel (.has .nil 0)) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ (smokeTel ▹ ∋ smokeLabel)) := by decide +kernel
-- The annotations must match the targets, and the sources must agree.
example : synthLe smokeCtx
    (.pair smokeTel .nil (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) = none := by decide +kernel
example : synthLe smokeCtx
    (.pair .nil smokeTel (.obj .nil .nil) (.obj smokeTel (.has .nil 0))) = none := by decide +kernel

-- `And-I` concatenates two typings of the same root.
example : synthAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here)) =
    some (μ (smokeTel ▹ ∋ smokeLabel)) := by decide +kernel
example : (checkAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here))
    (μ (smokeTel ▹ ∋ smokeLabel))) = true := by decide +kernel
example : synthAtom smokeCtx (.both .nil smokeTel (.var .here) (.var .here)) = none := by decide +kernel

/-- Two binders of the same object type. -/
private def smokeCtx2 : Ctx ([],x,x) :=
  smokeCtx.cons (.opaque (μ (.nil ▹ ∋ smokeLabel)))

example : synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var .here)) =
    some (μ (.nil ▹ ∋ smokeLabel ▹ ∋ smokeLabel)) := by decide +kernel
example : synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var (.there .here))) = none := by decide +kernel

end SmokeTests

end FCdot

end Paths
