import Coercions.Frontend.Sub

/-!
# Avoidance at a `let`, on the tank

The type of `let z = t in u` may not mention `z`.  When the body's type does,
the compiler approximates it by a type free of `z` (`avoid`,
`TypeOps.scala:474-509,565-583`).  This module does the same for DOT-MNF.

`up` approximates a type from above and `down` from below.  Each returns the
new type with the `DotMNF.Sub` derivation that relates it to the old one.  A
selection `z.A` at a covariant position becomes the meet of the avoided upper
bounds of every member `A` that `z` has, as the compiler widens a selection
at the merged bounds of its members (`derivedSelect` and `tryWiden`,
`TypeOps.scala:519-522`).  The meet is an intersection, derived by `Sub.and`
of the `Sub.selUpper` steps.  At a contravariant position `z.A` becomes the
avoided lower bound of the first member.  DOT-MNF has no union, so the lower
bounds cannot be joined.  A member bound is the compiler's `expandBounds`
(`Types.scala:6640-6645`).  `∀` flips its domain, and `{A : L..U}` flips `L`.
DOT-MNF types have no invariant position, so the compiler's `Range`
(`Types.scala:6902`) never arises.  A selection already being expanded at
the same polarity becomes `⊤` or `⊥`, the compiler's `emptyRange`
(`Types.scala:6608`).  A `μ` that mentions `z` has no subtyping rule in
DOT-MNF and becomes `⊤` or `⊥`.  Under a `∀` the codomain is approximated in
the context extended by the domain that `Sub.all` asks for.

Both draw on the tank of `Fuel.lean`.  Each node of the traversal costs
`cost` of the number of selections being expanded, and the members of a
selection are read by `declsAt` on the same tank.  A short tank answers `⊤`
or `⊥` and is marked.  The structural index starts at the fuel left, and each
node draws at least one unit, so the index never runs out before the tank
does.

`avoidLet` runs `up` at the binder of a `let` and strengthens the result.  It
returns the type `U` with `Sub (Γ.cons T0) V U.weaken`, which `HasTy.let`
takes through `HasTy.sub`.  If the tank ends marked, it answers `none`, and
the caller reports the recursion limit.  A type that does not mention the
binder comes back as itself, strengthened (`avoidLet_strengthen`).  So
avoidance never loses what strengthening finds.

Every computation here is framed, so a run that ends unmarked does the same
with more fuel (`avoidLet_frame`).  Every definition is structural, so the
kernel evaluates avoidance.  The checks at the end run it on the examples by
`decide +kernel`.
-/

namespace Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Defs Ctx Sub HasTy)

/-! ## Mentions -/

/-- The type mentions the variable `z`. -/
def mentions {s : Sig} (z : BVar s .var) : Ty s → Bool
  | .sel (.var q) _ => decide (q = z)
  | .typ _ L H => mentions z L || mentions z H
  | .fld _ T => mentions z T
  | .mu B => mentions (.there z) B
  | .all S T => mentions z S || mentions (.there z) T
  | .and S T => mentions z S || mentions z T
  | .top => false
  | .bot => false

/-- A renaming that never hits `z` gives a type that does not mention `z`. -/
theorem mentions_rename : ∀ {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) (z : BVar s2 .var),
    (∀ y : BVar s1 .var, ρ.var y ≠ z) → mentions z (T.rename ρ) = false
  | _, _, .top, _, _, _ => rfl
  | _, _, .bot, _, _, _ => rfl
  | _, _, .typ _ L H, ρ, z, h => by
    simp only [Ty.rename, mentions, mentions_rename L ρ z h, mentions_rename H ρ z h, Bool.or_false]
  | _, _, .fld _ T, ρ, z, h => by
    simp only [Ty.rename, mentions, mentions_rename T ρ z h]
  | _, _, .sel (.var q) _, ρ, z, h => by
    simp only [Ty.rename, Path.rename, mentions, decide_eq_false_iff_not]
    exact h q
  | _, _, .mu B, ρ, z, h => by
    simp only [Ty.rename, mentions]
    exact mentions_rename B ρ.lift (.there z) (lift_avoids h)
  | _, _, .all S T, ρ, z, h => by
    simp only [Ty.rename, mentions, mentions_rename S ρ z h,
      mentions_rename T ρ.lift (.there z) (lift_avoids h), Bool.or_false]
  | _, _, .and S T, ρ, z, h => by
    simp only [Ty.rename, mentions, mentions_rename S ρ z h, mentions_rename T ρ z h, Bool.or_false]
where
  /-- Under a binder the lifted renaming never hits the shifted `z`. -/
  lift_avoids {s1 s2 : Sig} {ρ : Rename s1 s2} {z : BVar s2 .var}
      (h : ∀ y : BVar s1 .var, ρ.var y ≠ z) : ∀ y : BVar (s1,x) .var, ρ.lift.var y ≠ .there z
    | .here => by simp
    | .there y => by
      simp only [Rename.lift_there, ne_eq, BVar.there.injEq]
      exact h y

/-- A weakened type does not mention the new binder. -/
theorem mentions_weaken {s : Sig} (U : Ty s) : mentions .here (U.weaken (k := .var)) = false :=
  mentions_rename U Rename.succ .here fun y => by simp

/-! ## The approximations -/

/-- A type above `T`, with the derivation. -/
abbrev Above {s : Sig} (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × Sub Γ T U

/-- A type below `T`, with the derivation. -/
abbrev Below {s : Sig} (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × Sub Γ U T

/-- The meet of types above `T`: their intersection, by `Sub.and`.  One type
is itself, and no type is `⊤`. -/
def meetAll {s : Sig} {Γ : Ctx s} {T : Ty s} : List (Above Γ T) → Above Γ T
  | [] => ⟨.top, .top⟩
  | [a] => a
  | a :: b :: rest =>
      let r := meetAll (b :: rest)
      ⟨.and a.1 r.1, .and a.2 r.2⟩
termination_by structural l => l

mutual

/-- An approximation of `T` from above that does not mention `z`.  `P` holds
the selections being expanded, each with its polarity, `true` for an upper
bound.  The index `d` is structural. -/
def up {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List (Label × Bool) → (T : Ty s) →
    Fu (Above Γ T)
  | 0, _, _ => fun t => (⟨.top, .top⟩, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.top, .top⟩
        | true =>
          if !mentions z T then Fu.ret ⟨T, .refl⟩ else
          match T with
          | .sel (.var q) A =>
              if (A, true) ∈ P then Fu.ret ⟨.top, .top⟩ else
              Fu.bind (declsAt Γ q A) fun ms =>
                Fu.bind (Fu.flatMapL (fun m =>
                    Fu.bind (up Γ z d ((A, true) :: P) m.2.1) fun r =>
                      Fu.ret [⟨r.1, .trans (.selUpper m.2.2) r.2⟩]) ms) fun rs =>
                  Fu.ret (meetAll rs)
          | .fld a T' =>
              Fu.bind (up Γ z d P T') fun r => Fu.ret ⟨.fld a r.1, .fld r.2⟩
          | .typ A L H =>
              Fu.bind (down Γ z d P L) fun l =>
                Fu.bind (up Γ z d P H) fun h => Fu.ret ⟨.typ A l.1 h.1, .typ l.2 h.2⟩
          | .and T1 T2 =>
              Fu.bind (up Γ z d P T1) fun r1 =>
                Fu.bind (up Γ z d P T2) fun r2 =>
                  Fu.ret ⟨.and r1.1 r2.1, .and (.trans .and1 r1.2) (.trans .and2 r2.2)⟩
          | .all S T' =>
              Fu.bind (down Γ z d P S) fun l =>
                Fu.bind (up (Γ.cons l.1) (.there z) d P T') fun c => Fu.ret ⟨.all l.1 c.1, .all l.2 c.2⟩
          | _ => Fu.ret ⟨.top, .top⟩
termination_by structural d _ _ => d

/-- An approximation of `T` from below that does not mention `z`.  `P` is as
for `up`.  The index `d` is structural. -/
def down {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List (Label × Bool) → (T : Ty s) →
    Fu (Below Γ T)
  | 0, _, _ => fun t => (⟨.bot, .bot⟩, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.bot, .bot⟩
        | true =>
          if !mentions z T then Fu.ret ⟨T, .refl⟩ else
          match T with
          | .sel (.var q) A =>
              if (A, false) ∈ P then Fu.ret ⟨.bot, .bot⟩ else
              Fu.bind (declsAt Γ q A) fun
                | m :: _ =>
                    Fu.bind (down Γ z d ((A, false) :: P) m.1) fun r =>
                      Fu.ret ⟨r.1, .trans r.2 (.selLower m.2.2)⟩
                | [] => Fu.ret ⟨.bot, .bot⟩
          | .fld a T' =>
              Fu.bind (down Γ z d P T') fun r => Fu.ret ⟨.fld a r.1, .fld r.2⟩
          | .typ A L H =>
              Fu.bind (up Γ z d P L) fun l =>
                Fu.bind (down Γ z d P H) fun h => Fu.ret ⟨.typ A l.1 h.1, .typ l.2 h.2⟩
          | .and T1 T2 =>
              Fu.bind (down Γ z d P T1) fun r1 =>
                Fu.bind (down Γ z d P T2) fun r2 =>
                  Fu.ret ⟨.and r1.1 r2.1, .and (.trans .and1 r1.2) (.trans .and2 r2.2)⟩
          | .all S T' =>
              Fu.bind (up Γ z d P S) fun l =>
                Fu.bind (down (Γ.cons S) (.there z) d P T') fun c => Fu.ret ⟨.all l.1 c.1, .all l.2 c.2⟩
          | _ => Fu.ret ⟨.bot, .bot⟩
termination_by structural d _ _ => d

end

/-- `up` on the tank it is handed, with the fuel left as its index. -/
def upAt {s : Sig} (Γ : Ctx s) (z : BVar s .var) (T : Ty s) : Fu (Above Γ T) := fun t =>
  up Γ z t.left [] T t

/-- The type of a `let` body after avoidance, as `HasTy.let` asks for it. -/
abbrev LetTy {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) : Type :=
  (U : Ty s) × Sub (Γ.cons T0) V U.weaken

/-- Strengthen an approximation that no longer mentions the binder.  If it
still mentions it, the answer is `⊤`, which is always above. -/
def strengthenAbove {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} (r : Above (Γ.cons T0) V) :
    LetTy Γ T0 V :=
  match tyStrengthenW? r.1 with
  | some w => ⟨w.val, w.property ▸ r.2⟩
  | none => ⟨.top, .top⟩

/-- Answer `none` on a marked tank, and `some a` otherwise. -/
def unlessOut {α : Type} (a : α) : Fu (Option α) := fun t =>
  if t.out then (none, t) else (some a, t)

/-- The result type of a `let` without annotation: the body's type `V`,
approximated from above until it no longer mentions the binder, then
strengthened.  `none` if the tank ends marked. -/
def avoidLet {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) : Fu (Option (LetTy Γ T0 V)) :=
  Fu.bind (upAt (Γ.cons T0) .here V) fun r => unlessOut (strengthenAbove r)

/-! ## A type that strengthens comes back as itself -/

theorem avoidLet_strengthen {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} {U : Ty s} {t : Tank}
    (h : tyStrengthen? V = some U) (ho : t.out = false) (hl : 1 ≤ t.left) :
    (avoidLet Γ T0 V t).1.map (·.1) = some U := by
  have hV : V = U.weaken := tyStrengthen?_sound h
  subst hV
  obtain ⟨n, b⟩ := t
  simp only at ho hl
  subst ho
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hup : upAt (Γ.cons T0) .here (U.weaken (k := .var)) ⟨n + 1, false⟩ =
      (⟨U.weaken, .refl⟩, ⟨n, false⟩) := by
    show up (Γ.cons T0) .here (n + 1) [] U.weaken ⟨n + 1, false⟩ = _
    rw [up.eq_def]
    simp [Fu.bind, draw, cost, mentions_weaken, Fu.ret]
  simp only [avoidLet, Fu.bind]
  rw [hup]
  simp only [unlessOut, Bool.false_eq_true, if_false, Option.map_some, strengthenAbove]
  split
  · rename_i w hw
    rw [tyStrengthenW?_weaken] at hw
    cases hw
    rfl
  · rename_i hw
    rw [tyStrengthenW?_weaken] at hw
    cases hw

/-! ## The frame lemmas

Every computation of this module is framed: it keeps a marked tank, never adds
fuel, and does the same with more fuel.  `up` and `down` at a larger index do
what they do at a smaller one, as `look` does (`look_agree`).  So `upAt`,
whose index is the fuel left, is framed, as `declsAt` is. -/

/-- At index zero the approximation marks the tank. -/
theorem out_framed {α : Type} (a : α) : Framed (fun t : Tank => (a, { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

theorem meet_framed {s : Sig} {Γ : Ctx s} {T : Ty s} (rs : List (Above Γ T)) :
    Framed (Fu.ret (meetAll rs)) := ret_framed _

/-- `up` and `down` are framed at every index. -/
theorem upDown_framed : ∀ (d : Nat) {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List (Label × Bool))
    (T : Ty s), Framed (up Γ z d P T) ∧ Framed (down Γ z d P T)
  | 0, _, _, _, _, _ => ⟨out_framed _, out_framed _⟩
  | d + 1, s, Γ, z, P, T => by
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List (Label × Bool)) (T : Ty s),
        Framed (up Γ z d P T) ∧ Framed (down Γ z d P T) := fun Γ z P T => upDown_framed d Γ z P T
    constructor
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (declsAt_framed Γ q A) fun ms => ?_
            refine bind_framed (flatMapL_framed (fun m => ?_) ms) fun _ => ret_framed _
            exact bind_framed (ih Γ z _ _).1 fun _ => ret_framed _
        | fld a T' => exact bind_framed (ih Γ z P T').1 fun _ => ret_framed _
        | typ A L H =>
          exact bind_framed (ih Γ z P L).2 fun _ => bind_framed (ih Γ z P H).1 fun _ => ret_framed _
        | and T1 T2 =>
          exact bind_framed (ih Γ z P T1).1 fun _ => bind_framed (ih Γ z P T2).1 fun _ => ret_framed _
        | all S T' =>
          exact bind_framed (ih Γ z P S).2 fun l =>
            bind_framed (ih (Γ.cons l.1) (.there z) P T').1 fun _ => ret_framed _
        | mu _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (declsAt_framed Γ q A) fun ms => ?_
            cases ms with
            | nil => exact ret_framed _
            | cons m _ => exact bind_framed (ih Γ z _ _).2 fun _ => ret_framed _
        | fld a T' => exact bind_framed (ih Γ z P T').2 fun _ => ret_framed _
        | typ A L H =>
          exact bind_framed (ih Γ z P L).1 fun _ => bind_framed (ih Γ z P H).2 fun _ => ret_framed _
        | and T1 T2 =>
          exact bind_framed (ih Γ z P T1).2 fun _ => bind_framed (ih Γ z P T2).2 fun _ => ret_framed _
        | all S T' =>
          exact bind_framed (ih Γ z P S).1 fun _ =>
            bind_framed (ih (Γ.cons S) (.there z) P T').2 fun _ => ret_framed _
        | mu _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _

/-- `up` and `down` at a larger index do what they do at a smaller one. -/
theorem upDown_agree : ∀ (d d' : Nat), d ≤ d' → ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var)
    (P : List (Label × Bool)) (T : Ty s),
    Agree (up Γ z d P T) (up Γ z d' P T) ∧ Agree (down Γ z d P T) (down Γ z d' P T)
  | 0, d', _, s, Γ, z, P, T => by
    refine ⟨⟨(upDown_framed 0 Γ z P T).1, (upDown_framed d' Γ z P T).1, ?_⟩,
      ⟨(upDown_framed 0 Γ z P T).2, (upDown_framed d' Γ z P T).2, ?_⟩⟩ <;>
    · intro t r t' h ho _
      simp only [up, down, Prod.mk.injEq] at h
      rw [← h.2] at ho
      simp at ho
  | d + 1, d', hd, s, Γ, z, P, T => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List (Label × Bool)) (T : Ty s),
        Agree (up Γ z d P T) (up Γ z e P T) ∧ Agree (down Γ z d P T) (down Γ z e P T) :=
      fun Γ z P T => upDown_agree d e (by omega) Γ z P T
    constructor
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (declsAt_framed Γ q A)) fun ms => ?_
            refine bind_agree (flatMapL_agree (fun m => ?_) ms) fun _ => ret_agree _
            exact bind_agree (ih Γ z _ _).1 fun _ => ret_agree _
        | fld a T' => exact bind_agree (ih Γ z P T').1 fun _ => ret_agree _
        | typ A L H =>
          exact bind_agree (ih Γ z P L).2 fun _ => bind_agree (ih Γ z P H).1 fun _ => ret_agree _
        | and T1 T2 =>
          exact bind_agree (ih Γ z P T1).1 fun _ => bind_agree (ih Γ z P T2).1 fun _ => ret_agree _
        | all S T' =>
          exact bind_agree (ih Γ z P S).2 fun l =>
            bind_agree (ih (Γ.cons l.1) (.there z) P T').1 fun _ => ret_agree _
        | mu _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (declsAt_framed Γ q A)) fun ms => ?_
            cases ms with
            | nil => exact ret_agree _
            | cons m _ => exact bind_agree (ih Γ z _ _).2 fun _ => ret_agree _
        | fld a T' => exact bind_agree (ih Γ z P T').2 fun _ => ret_agree _
        | typ A L H =>
          exact bind_agree (ih Γ z P L).1 fun _ => bind_agree (ih Γ z P H).2 fun _ => ret_agree _
        | and T1 T2 =>
          exact bind_agree (ih Γ z P T1).2 fun _ => bind_agree (ih Γ z P T2).2 fun _ => ret_agree _
        | all S T' =>
          exact bind_agree (ih Γ z P S).1 fun _ =>
            bind_agree (ih (Γ.cons S) (.there z) P T').2 fun _ => ret_agree _
        | mu _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _

/-- `up` from the fuel left is framed. -/
theorem upAt_framed {s : Sig} (Γ : Ctx s) (z : BVar s .var) (T : Ty s) : Framed (upAt Γ z T) where
  absorbs t ht := (upDown_framed t.left Γ z [] T).1.absorbs t ht
  spends t := (upDown_framed t.left Γ z [] T).1.spends t
  shift := by
    intro t r t' h ho k
    have h1 := (upDown_framed t.left Γ z [] T).1.shift t r t' h ho k
    have hag := (upDown_agree t.left (t.left + k) (Nat.le_add_right _ _) Γ z [] T).1
    change up Γ z (t.left + k) [] T (t.add k) = _
    rw [hag.sim t r t' h ho k]

theorem unlessOut_framed {α : Type} (a : α) : Framed (unlessOut a) where
  absorbs t ht := by simp [unlessOut, ht]
  spends t := by
    unfold unlessOut
    cases t.out <;> exact Nat.le_refl _
  shift := by
    intro t r t' h ho k
    unfold unlessOut at h ⊢
    cases hto : t.out
    · simp only [hto, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hto]
    · simp only [hto, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hto] at ho

/-- Avoidance is framed: it keeps a marked tank, never adds fuel, and does the
same with more fuel. -/
theorem avoidLet_framed {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) :
    Framed (avoidLet Γ T0 V) :=
  bind_framed (upAt_framed _ _ _) fun _ => unlessOut_framed _

theorem avoidLet_frame {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} {t t' : Tank}
    {r : Option (LetTy Γ T0 V)} (h : avoidLet Γ T0 V t = (r, t')) (ho : t'.out = false) (k : Nat) :
    avoidLet Γ T0 V (t.add k) = (r, t'.add k) :=
  (avoidLet_framed Γ T0 V).shift t r t' h ho k

/-- Avoidance from a marked tank answers `none` and leaves the tank as it is. -/
theorem avoidLet_absorbs {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) {t : Tank}
    (h : t.out = true) : avoidLet Γ T0 V t = (none, t) := by
  have hu := (upAt_framed (Γ.cons T0) .here V).absorbs t h
  simp only [avoidLet, Fu.bind]
  cases hup : upAt (Γ.cons T0) .here V t with
  | mk a t1 =>
    rw [hup] at hu
    simp only at hu
    simp [hu, unlessOut, h]

/-! ## Checks

Each check runs in the kernel at the default fuel.  `avoidAt` starts a full
tank. -/

section AvoidChecks

open DotMNF.Examples

/-- Avoidance at a `let` from a full tank of `n` units, the type and the tank. -/
def avoidAt {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) (n : Nat := defaultFuel) :
    Option (Ty s) × Tank :=
  let r := avoidLet Γ T0 V ⟨n, false⟩
  (r.1.map (·.1), r.2)

-- E2: the outer `let` binds `x = ν(x. {A = ∀(y : x.A) x.A} ∧ {a = …})` and its body has the type
-- `x.A`.  The alias cycle is cut once at each polarity, so the avoided type is a function type
-- `∀(y : ∀(z : ⊤) ⊥) ⊤`.  Strengthening alone fails on `x.A`.  It uses 34 units.
example : avoidAt Ctx.nil (.mu E2Self) (.sel (.var .here) lA) =
    (some (.all (.all .top .bot) .top), ⟨defaultFuel - 34, false⟩) := by decide +kernel

/-- G's binder: `z : μ(s. ({A : ⊥..{a : ⊤}} ∧ {A : ⊥..{b : ⊤}}) ∧ {v : s.A})`. -/
def GSelf : Ty ([] : Sig) :=
  .mu (.and (.and (.typ lA .bot (.fld la .top)) (.typ lA .bot (.fld lb .top))) (.fld lv (.sel (.var .here) lA)))

-- G: the body `z.v` has the type `z.A`, and `z` has two members `A`.  Avoidance meets their upper
-- bounds, `{a : ⊤} ∧ {b : ⊤}`, as the compiler does.  It uses 22 units.
example : avoidAt Ctx.nil GSelf (.sel (.var .here) lA) =
    (some (.and (.fld la .top) (.fld lb .top)), ⟨defaultFuel - 22, false⟩) := by decide +kernel

-- E8: a body type that does not mention the binder is strengthened, at one unit.
example : avoidAt E8Ctx1 (E8Ref .here) (.sel (.var (.there .here)) lA) =
    (some (.sel (.var .here) lA), ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- A short tank is marked, and avoidance answers `none`: E2 at 4 units, and any type at 0.
example : avoidAt Ctx.nil (.mu E2Self) (.sel (.var .here) lA) 4 = (none, ⟨0, true⟩) := by
  decide +kernel
example : avoidAt E8Ctx1 (E8Ref .here) (.sel (.var (.there .here)) lA) 0 = (none, ⟨0, true⟩) := by
  decide +kernel

/-- E2's inner `let`, at `x.A`, as the vanilla examples derive it. -/
def E2inner : HasTy E2Ctx1 (.let (.proj .here la) (.app .here .here)) (.sel (.var .here) lA) :=
  .let E2proj E2app

/-- E2's avoidance, run at the default fuel. -/
def E2avoid : Option (LetTy Ctx.nil (.mu E2Self) (.sel (.var .here) lA)) :=
  (avoidLet Ctx.nil (.mu E2Self) (.sel (.var .here) lA) ⟨defaultFuel, false⟩).1

theorem E2avoid_ty : E2avoid.map (·.1) = some (.all (.all .top .bot) .top) := by decide +kernel

/-- E2 at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`, not at `⊤`: the
object, then the inner `let` taken to the avoided type by the derivation that
avoidance returns. -/
def E2avoided : HasTy Ctx.nil (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here)))
    (.all (.all .top .bot) .top) :=
  match h : E2avoid with
  | some r =>
      have hr : r.1 = .all (.all .top .bot) .top := by
        have := E2avoid_ty
        rw [h] at this
        exact Option.some.inj this
      hr ▸ .let (.obj E2DefsTy E2Distinct) (.sub E2inner r.2)
  | none => absurd E2avoid_ty (by rw [h]; simp)

end AvoidChecks

end Frontend.Core
