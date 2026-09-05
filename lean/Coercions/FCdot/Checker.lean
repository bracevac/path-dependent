import Coercions.FCdot.Typing

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

mutual

def Ty.rename? : Ty s1 → PartialRename s1 s2 → Option (Ty s2)
  | .bot, _ => some .bot
  | .sel x ℓ, ρ => (ρ.var x).map (fun y => .sel y ℓ)
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
  | _, _, .sel x ℓ, ρ, σ, h => by
      simp only [Ty.rename, Ty.rename?]
      rw [(h (σ.var x) x).mpr rfl]
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
  | _, _, .sel x ℓ, U, ρ, σ, h, hU => by
      simp only [Ty.rename?, Option.map_eq_some_iff] at hU
      obtain ⟨y, hy, hU⟩ := hU
      subst hU
      simp only [Ty.rename]
      rw [(h x y).mp hy]
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

/-- `Has.member`: the same, when the proposition is a field declaration.  The
subject variable is checked, the label synthesised. -/
def hasMember {s : Sig} {Γ : Ctx s} {a : Atom s} {e : LeCo s} (i : Nat) (y : BVar s .var)
    {Sa : Ty s} (ha : Γ ⊢ₐ a : Sa) {Se Te : Ty s} (he : Γ ⊢ e : Se ≤ Te) :
    Option (HasChecked Γ (.member a e i) y) :=
  if hx : a.root = y then
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
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthLeCore Γ e
      leMember i ca.typing ce.typing

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

def synthHasCore {s : Sig} (Γ : Ctx s) (ev : Has s) (y : BVar s .var) :
    Option (HasChecked Γ ev y) :=
  match ev with
  | .member a e i => do
      let ca ← synthAtomCore Γ a
      let ce ← synthLeCore Γ e
      hasMember i y ca.typing ce.typing
  | .field ℓ =>
      match witness? (Γ.lookupFields y) with
      | some ⟨Fs, hF⟩ => if hm : ℓ ∈ Fs then some ⟨ℓ, .field hF hm⟩ else none
      | none => none

/-- A `pre` side, checked against the hole's left endpoint `X`: `none` leaves
it in place, `some e` needs `e` to land in the closed type `X` weakens. -/
def checkPreCore {s : Sig} (Γ : Ctx s) (side : Side s) (X : Ty (s,x)) :
    Option (PreChecked Γ side X) :=
  match side with
  | .none => some ⟨X, .none⟩
  | .some e => do
      let ce ← synthLeCore Γ e
      if h : X = ce.target↑ then some ⟨ce.source↑, by subst h; exact .some ce.typing⟩
      else none

/-- A `post` side, checked against the hole's right endpoint `Y`. -/
def checkPostCore {s : Sig} (Γ : Ctx s) (side : Side s) (Y : Ty (s,x)) :
    Option (PostChecked Γ side Y) :=
  match side with
  | .none => some ⟨Y, .none⟩
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
      let ch ← synthHasCore Γ h a.root
      if hl : ch.label = ℓ then
        some ⟨.sel a.root ℓ, .proj ca.typing (by rw [← hl]; exact ch.typing)⟩
      else none
  | .let t u => do
      let ct ← synthTmCore Γ t
      let cu ← synthTmCore (Γ.cons (.opaque ct.type)) u
      match cu.type.strengthenW? with
      | some ⟨U, hU⟩ => some ⟨U, .let ct.typing (by rw [← hU]; exact cu.typing)⟩
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
      let Tel := Telescope.ofLiteral W F.labels
      let pF ← checkFieldsCore (Γ.cons (.transparent (.obj Tel) W F.labels)) F
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
      if h : ct.type = .sel .here ℓ then
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

/-- The literal's precise type: one definition entry, one presence entry. -/
private def smokeObjTy : Ty [] := .obj (Telescope.ofLiteral smokeW [smokeLabel])

/-- A context whose only binder declares the field `ℓ`. -/
private def smokeCtx : Ctx ([],x) := Ctx.nil.cons (.opaque (.obj (.cons .nil (.has smokeLabel))))

/-- A context whose only binder has the empty object type. -/
private def smokeCtxNil : Ctx ([],x) := Ctx.nil.cons (.opaque (.obj .nil))

#guard checkValue Ctx.nil smokeObj smokeObjTy
#guard synthValue Ctx.nil smokeObj = some smokeObjTy
#guard !checkValue Ctx.nil smokeObj (.obj .nil)
#guard !checkValue Ctx.nil smokeObj (.obj (.cons .nil (.has smokeLabel)))
#guard checkTm smokeCtx smokeId (.pi .top .top)
#guard !checkTm smokeCtx smokeId (.pi .top .bot)
#guard checkLe Ctx.nil (.trans (.refl .top) (.top .top)) .top .top
/-- Field evidence read off the binder's own object type. -/
private def smokeHas : Has ([],x) :=
  .member (.var .here) (.refl (.obj (.cons .nil (.has smokeLabel)))) 0

/-- A context whose only binder is transparent and declares the field. -/
private def smokeCtxTrans : Ctx ([],x) :=
  Ctx.nil.cons (.transparent .top (.cons .nil smokeLabel .top) [smokeLabel])

#guard checkTm smokeCtx (.proj (.var .here) smokeLabel smokeHas) (.sel .here smokeLabel)
#guard !checkTm smokeCtx (.proj (.var .here) (.trm 1) smokeHas) (.sel .here (.trm 1))
#guard checkTm smokeCtxTrans (.proj (.var .here) smokeLabel (.field smokeLabel))
    (.sel .here smokeLabel)
#guard !checkTm smokeCtx (.proj (.var .here) smokeLabel (.field smokeLabel))
    (.sel .here smokeLabel)
#guard checkTm smokeCtx (.let (.atom (.var .here)) (.atom (.var (.there .here))))
    (.obj (.cons .nil (.has smokeLabel)))

-- The annotated object coercion synthesises both endpoints.
#guard checkLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil)
    (.obj (.cons .nil (.has smokeLabel))) (.obj .nil)
#guard synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) .nil) =
    some (.obj (.cons .nil (.has smokeLabel)), .obj .nil)

-- A presence proposition is inherited from the source telescope by index.
#guard synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 0)) =
    some (.obj (.cons .nil (.has smokeLabel)), .obj (.cons .nil (.has smokeLabel)))
#guard synthLe smokeCtx (.obj (.cons .nil (.has smokeLabel)) (.has .nil 1)) = none

-- The annotated `Rec-I` synthesises its type.
#guard checkAtom smokeCtxNil (.foldSelf .nil (.var .here)) (.obj .nil)
#guard synthAtom smokeCtxNil (.foldSelf .nil (.var .here)) = some (.obj .nil)

/-- A source telescope with one inclusion and one equality. -/
private def smokeSrc : Telescope ([],x,x) := .nil ▹ ⊤ ⊑ ⊤ ▹ ⊤ ≐ ⊥

-- A template with empty sides copies the hole.
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊤))
-- A hole must name an inclusion (`le`) or an equality (`eq`, `eqSym`).
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 1) .none)) = none
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eq 0) .none)) = none
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eq 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ⊑ ⊥))
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤))
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 2) .none)) = none
-- A closed side composes with the hole at a weakened closed type.
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil (.some (.top ⊥)) (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤))
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.eqSym 1) (.some (.top ⊤)))) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ⊑ ⊤))
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil (.some (.refl ⊥)) (.le 0) .none)) = none
#guard synthLe smokeCtx (.obj smokeSrc (.le .nil .none (.le 0) (.some (.bot ⊤)))) = none
-- Equalities are copied, possibly flipped; inclusions are not equalities.
#guard synthLe smokeCtx (.obj smokeSrc (.eq .nil 1 false)) =
    some (μ smokeSrc, μ (.nil ▹ ⊤ ≐ ⊥))
#guard synthLe smokeCtx (.obj smokeSrc (.eq .nil 1 true)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤))
#guard synthLe smokeCtx (.obj smokeSrc (.eq .nil 0 false)) = none
-- Templates accumulate, oldest first.
#guard synthLe smokeCtx (.obj smokeSrc (.le (.eq .nil 1 true) .none (.le 0) .none)) =
    some (μ smokeSrc, μ (.nil ▹ ⊥ ≐ ⊤ ▹ ⊤ ⊑ ⊤))

/-- The smoke binder's telescope. -/
private def smokeTel : Telescope ([],x,x) := .nil ▹ ∋ smokeLabel

-- Pairing concatenates the targets of two coercions with the same source.
#guard synthLe smokeCtx
    (.pair .nil smokeTel (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ smokeTel)
#guard synthLe smokeCtx
    (.pair smokeTel smokeTel (.obj smokeTel (.has .nil 0)) (.obj smokeTel (.has .nil 0))) =
    some (μ smokeTel, μ (smokeTel ▹ ∋ smokeLabel))
-- The annotations must match the targets, and the sources must agree.
#guard synthLe smokeCtx
    (.pair smokeTel .nil (.obj smokeTel .nil) (.obj smokeTel (.has .nil 0))) = none
#guard synthLe smokeCtx
    (.pair .nil smokeTel (.obj .nil .nil) (.obj smokeTel (.has .nil 0))) = none

-- `And-I` concatenates two typings of the same root.
#guard synthAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here)) =
    some (μ (smokeTel ▹ ∋ smokeLabel))
#guard checkAtom smokeCtx (.both smokeTel smokeTel (.var .here) (.var .here))
    (μ (smokeTel ▹ ∋ smokeLabel))
#guard synthAtom smokeCtx (.both .nil smokeTel (.var .here) (.var .here)) = none

/-- Two binders of the same object type. -/
private def smokeCtx2 : Ctx ([],x,x) :=
  smokeCtx.cons (.opaque (μ (.nil ▹ ∋ smokeLabel)))

#guard synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var .here)) =
    some (μ (.nil ▹ ∋ smokeLabel ▹ ∋ smokeLabel))
#guard synthAtom smokeCtx2
    (.both (.nil ▹ ∋ smokeLabel) (.nil ▹ ∋ smokeLabel) (.var .here) (.var (.there .here))) = none

end SmokeTests

end FCdot
