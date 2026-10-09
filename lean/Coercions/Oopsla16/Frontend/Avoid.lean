import Coercions.Oopsla16.Frontend.Sub

/-!
# Avoidance at a call

`Oopsla16` has no `let`.  A result type must not mention the parameter of a
method applied to an argument that is not a variable, because `T_App` asks for
a codomain that is a weakening.  The compiler skolemizes such an argument
(`safeSubstParam` in `typer/TypeAssigner.scala`) and approximates the skolem
away (`Type.deskolemized` in `core/Types.scala`).  This module does the same.

`up` approximates a type from above and `down` from below.  Each returns the
new type with the `Oopsla16.Stp` derivation that relates it to the old one.
A selection `z.L` becomes the meet of the upper bounds of the members `L` of
`z` when approximated from above, and the join of their lower bounds when
approximated from below.  The compiler widens a selection at the bounds of the
one denotation it merges from those members (`ApproximatingTypeMap.derivedSelect`
and `tryWiden` in `core/Types.scala`).  A method's domain and a type member's
lower bound flip the direction.  Under a method, the codomain is approximated
in the context extended by the new domain, as `stp_fun` asks.  A selection
already being expanded in the same direction becomes `⊤` or `⊥`, the compiler's
`emptyRange`.

A recursive type that mentions the parameter stays recursive, as in
`ApproximatingTypeMap.derivedRecType`.  `up` closes it with `stp_bindx`.
`down` approximates the body twice, because the premise of `stp_bindx` assumes
the new self.  The second pass must return the body of the first, and otherwise
the answer is `⊥`.  It does when the tank lasts, since a selection of the
parameter is looked up in the parameter's prefix, which no later self changes.

Both run on the tank of `Fuel.lean`.  A short tank answers `⊤` or `⊥` and marks
the tank.

`avoidCod` approximates a codomain from above, with the parameter assumed at
the argument's type, and strengthens the result.  `avoidArg` returns the method
type the receiver is widened to, by `stp_fun`.  Both answer `none` on a marked
tank, and the caller reports the recursion limit.  A codomain that does not
mention the parameter comes back unchanged (`avoidCod_strengthen`,
`avoidArg_weaken`).  Every computation is framed, so a run that ends unmarked
does the same with more fuel (`avoidCod_frame`, `avoidArg_frame`).  The checks
at the end run on the examples by `decide +kernel`.
-/

namespace Oopsla16Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Ctx Store Stp Htp HasType scopeUpTo renameUpTo varUpTo)

/-! ## Mentions -/

/-- The type mentions the abstract variable `z`.  A source type has no store
location, so a concrete variable never counts. -/
def mentions {s : Sig} (z : BVar s .var) : Ty [] s → Bool
  | .TSel (.abs q) _ => decide (q = z)
  | .TSel (.conc _) _ => false
  | .TFun _ S U => mentions z S || mentions (.there z) U
  | .TTyp _ L H => mentions z L || mentions z H
  | .TBind X => mentions (.there z) X
  | .TAnd A B => mentions z A || mentions z B
  | .TOr A B => mentions z A || mentions z B
  | .TTop => false
  | .TBot => false

/-- Under a binder the lifted substitution never hits the shifted `z`. -/
theorem lift_avoids {s1 s2 : Sig} {θ : Oopsla16.Subst [] s1 [] s2} {z : BVar s2 .var}
    (h : ∀ y, θ.abs y ≠ .abs z) : ∀ y, θ.lift.abs y ≠ .abs (.there z)
  | .here => by simp [Oopsla16.Subst.lift]
  | .there y => by
    simp only [Oopsla16.Subst.lift]
    have hy := h y
    cases hθ : θ.abs y with
    | conc c => exact nomatch c
    | abs w =>
      rw [hθ] at hy
      simp only [Oopsla16.Vr.weaken, ne_eq, Oopsla16.Vr.abs.injEq, BVar.there.injEq]
      intro hw
      exact hy (congrArg Vr.abs hw)

/-- A substitution that never hits `z` gives a type that does not mention `z`. -/
theorem mentions_subst : ∀ {s1 s2 : Sig} (T : Ty [] s1) (θ : Oopsla16.Subst [] s1 [] s2)
    (z : BVar s2 .var), (∀ y, θ.abs y ≠ .abs z) → mentions z (T.subst θ) = false
  | _, _, .TBot, _, _, _ => rfl
  | _, _, .TTop, _, _, _ => rfl
  | _, _, .TFun _ S U, θ, z, h => by
    simp only [Oopsla16.Ty.subst, mentions, mentions_subst S θ z h,
      mentions_subst U θ.lift (.there z) (lift_avoids h), Bool.or_false]
  | _, _, .TTyp _ L H, θ, z, h => by
    simp only [Oopsla16.Ty.subst, mentions, mentions_subst L θ z h, mentions_subst H θ z h,
      Bool.or_false]
  | _, _, .TSel p _, θ, z, h => by
    cases p with
    | conc c => exact nomatch c
    | abs y =>
      simp only [Oopsla16.Ty.subst, Oopsla16.Vr.subst]
      have hy := h y
      cases hθ : θ.abs y with
      | conc c => exact nomatch c
      | abs w =>
        rw [hθ] at hy
        simp only [mentions, decide_eq_false_iff_not]
        intro hw
        exact hy (congrArg Vr.abs hw)
  | _, _, .TBind X, θ, z, h => by
    simp only [Oopsla16.Ty.subst, mentions]
    exact mentions_subst X θ.lift (.there z) (lift_avoids h)
  | _, _, .TAnd A B, θ, z, h => by
    simp only [Oopsla16.Ty.subst, mentions, mentions_subst A θ z h, mentions_subst B θ z h,
      Bool.or_false]
  | _, _, .TOr A B, θ, z, h => by
    simp only [Oopsla16.Ty.subst, mentions, mentions_subst A θ z h, mentions_subst B θ z h,
      Bool.or_false]

/-- A weakened type does not mention the new binder. -/
theorem mentions_weaken {s : Sig} (U : Ty [] s) : mentions .here (U.weaken) = false :=
  mentions_subst U _ .here fun y => by simp [Oopsla16.Subst.ofRename]

/-! ## The approximations -/

/-- A type above `T`, with the derivation. -/
abbrev Above {s : Sig} (Γ : Ctx [] s) (T : Ty [] s) : Type := (U : Ty [] s) × SStp Γ T U

/-- A type below `T`, with the derivation. -/
abbrev Below {s : Sig} (Γ : Ctx [] s) (T : Ty [] s) : Type := (U : Ty [] s) × SStp Γ U T

/-- The meet of types above `T`: their intersection, by `stp_and2`.  One type
is itself, and no type is `⊤`. -/
def meetAll {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : List (Above Γ T) → Above Γ T
  | [] => ⟨.TTop, .stp_top⟩
  | [a] => a
  | a :: b :: rest =>
      let r := meetAll (b :: rest)
      ⟨.TAnd a.1 r.1, .stp_and2 a.2 r.2⟩
termination_by structural l => l

/-- The join of types below `T`: their union, by `stp_or1`.  One type is
itself, and no type is `⊥`. -/
def joinAll {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : List (Below Γ T) → Below Γ T
  | [] => ⟨.TBot, .stp_bot⟩
  | [a] => a
  | a :: b :: rest =>
      let r := joinAll (b :: rest)
      ⟨.TOr a.1 r.1, .stp_or1 a.2 r.2⟩
termination_by structural l => l

/-- A recursive type below `μ X`, from a body `Y'` approximated under the self
assumed at `Y`.  When `Y'` is `Y`, `stp_bindx` closes it at `μ Y`.  Otherwise
the answer is `⊥`. -/
def closeBelow {s : Sig} {Γ : Ctx [] s} {X Y Y' : Ty [] (s,x)} (e : SStp (Γ.cons Y) Y' X) :
    Below Γ (.TBind X) :=
  if h : Y' = Y then ⟨.TBind Y, .stp_bindx (by subst h; exact e)⟩ else ⟨.TBot, .stp_bot⟩

mutual

/-- An approximation of `T` from above that does not mention `z`.  `P` holds
the selections being expanded, each with its direction, `true` for an upper
bound.  The index `d` is the structural measure. -/
def up {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) :
    Nat → List (Lb × Bool) → (T : Ty [] s) → Fu (Above Γ T)
  | 0, _, _ => fun t => (⟨.TTop, .stp_top⟩, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.TTop, .stp_top⟩
        | true =>
          if !mentions z T then Fu.ret ⟨T, refl T⟩ else
          match T with
          | .TSel (.abs q) L =>
              if (L, true) ∈ P then Fu.ret ⟨.TTop, .stp_top⟩ else
              Fu.bind (members Γ q L) fun ms =>
                Fu.bind (Fu.flatMapL (fun m =>
                    Fu.bind (up Γ z d ((L, true) :: P) (m.2.1.rename (renameUpTo q))) fun r =>
                      Fu.ret [⟨r.1, .stp_trans (.stp_sel1 (lowerBot m.2.2)) r.2⟩]) ms) fun rs =>
                  Fu.ret (meetAll rs)
          | .TFun l S U =>
              Fu.bind (down Γ z d P S) fun a =>
                Fu.bind (up (Γ.cons a.1.weaken) (.there z) d P U) fun c =>
                  Fu.ret ⟨.TFun l a.1 c.1, .stp_fun a.2 c.2⟩
          | .TTyp l L H =>
              Fu.bind (down Γ z d P L) fun lo =>
                Fu.bind (up Γ z d P H) fun hi =>
                  Fu.ret ⟨.TTyp l lo.1 hi.1, .stp_typ lo.2 hi.2⟩
          | .TAnd A B =>
              Fu.bind (up Γ z d P A) fun a =>
                Fu.bind (up Γ z d P B) fun b =>
                  Fu.ret ⟨.TAnd a.1 b.1, .stp_and2 (.stp_and11 a.2) (.stp_and12 b.2)⟩
          | .TOr A B =>
              Fu.bind (up Γ z d P A) fun a =>
                Fu.bind (up Γ z d P B) fun b =>
                  Fu.ret ⟨.TOr a.1 b.1, .stp_or1 (.stp_or21 a.2) (.stp_or22 b.2)⟩
          | .TBind X =>
              Fu.bind (up (Γ.cons X) (.there z) d P X) fun c =>
                Fu.ret ⟨.TBind c.1, .stp_bindx c.2⟩
          | _ => Fu.ret ⟨.TTop, .stp_top⟩
termination_by structural d _ _ => d

/-- An approximation of `T` from below that does not mention `z`.  `P` is as
for `up`. -/
def down {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) :
    Nat → List (Lb × Bool) → (T : Ty [] s) → Fu (Below Γ T)
  | 0, _, _ => fun t => (⟨.TBot, .stp_bot⟩, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.TBot, .stp_bot⟩
        | true =>
          if !mentions z T then Fu.ret ⟨T, refl T⟩ else
          match T with
          | .TSel (.abs q) L =>
              if (L, false) ∈ P then Fu.ret ⟨.TBot, .stp_bot⟩ else
              Fu.bind (members Γ q L) fun ms =>
                Fu.bind (Fu.flatMapL (fun m =>
                    Fu.bind (down Γ z d ((L, false) :: P) (m.1.rename (renameUpTo q))) fun r =>
                      Fu.ret [⟨r.1, .stp_trans r.2 (.stp_sel2 (upperTop m.2.2))⟩]) ms) fun rs =>
                  Fu.ret (joinAll rs)
          | .TFun l S U =>
              Fu.bind (up Γ z d P S) fun a =>
                Fu.bind (down (Γ.cons S.weaken) (.there z) d P U) fun c =>
                  Fu.ret ⟨.TFun l a.1 c.1, .stp_fun a.2 c.2⟩
          | .TTyp l L H =>
              Fu.bind (up Γ z d P L) fun lo =>
                Fu.bind (down Γ z d P H) fun hi =>
                  Fu.ret ⟨.TTyp l lo.1 hi.1, .stp_typ lo.2 hi.2⟩
          | .TAnd A B =>
              Fu.bind (down Γ z d P A) fun a =>
                Fu.bind (down Γ z d P B) fun b =>
                  Fu.ret ⟨.TAnd a.1 b.1, .stp_and2 (.stp_and11 a.2) (.stp_and12 b.2)⟩
          | .TOr A B =>
              Fu.bind (down Γ z d P A) fun a =>
                Fu.bind (down Γ z d P B) fun b =>
                  Fu.ret ⟨.TOr a.1 b.1, .stp_or1 (.stp_or21 a.2) (.stp_or22 b.2)⟩
          | .TBind X =>
              Fu.bind (down (Γ.cons X) (.there z) d P X) fun c1 =>
                Fu.bind (down (Γ.cons c1.1) (.there z) d P X) fun c2 =>
                  Fu.ret (closeBelow c2.2)
          | _ => Fu.ret ⟨.TBot, .stp_bot⟩
termination_by structural d _ _ => d

end

/-- `up` indexed by the fuel left. -/
def upAt {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) : Fu (Above Γ T) := fun t =>
  up Γ z t.left [] T t

/-- `down` indexed by the fuel left. -/
def downAt {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) : Fu (Below Γ T) := fun t =>
  down Γ z t.left [] T t

/-! ## Avoidance at a call -/

/-- A codomain after avoidance: a type `U0` of the outer scope with the
subtyping from the codomain `U` to its weakening, under the parameter
assumed at `A`. -/
abbrev CodTy {s : Sig} (Γ : Ctx [] s) (A : Ty [] s) (U : Ty [] (s,x)) : Type :=
  (U0 : Ty [] s) × SStp (Γ.cons A.weaken) U U0.weaken

/-- The method type a receiver at `{def l(x : S) : U}` is widened to for an
argument at `A`: its codomain is a weakening, as `T_App` asks. -/
abbrev ArgTy {s : Sig} (Γ : Ctx [] s) (l : Lb) (S : Ty [] s) (U : Ty [] (s,x)) (A : Ty [] s) :
    Type :=
  (U0 : Ty [] s) × SStp Γ (.TFun l S U) (.TFun l A U0.weaken)

/-- Strengthen an approximation that does not mention the parameter.  If it
does, the answer is `⊤`. -/
def strengthenAbove {s : Sig} {Γ : Ctx [] s} {A : Ty [] s} {U : Ty [] (s,x)}
    (r : Above (Γ.cons A.weaken) U) : CodTy Γ A U :=
  match FCdotR.Ty.strengthenW? r.1 with
  | some w => ⟨w.val, w.property ▸ r.2⟩
  | none => ⟨.TTop, .stp_top⟩

/-- Answer `none` on a marked tank, and `some a` otherwise. -/
def unlessOut {α : Type} (a : α) : Fu (Option α) := fun t =>
  if t.out then (none, t) else (some a, t)

/-- The codomain `U` of a method applied to an argument at `A` that is not a
variable: approximated from above under the parameter assumed at `A`, then
strengthened.  `none` if the tank ends marked. -/
def avoidCod {s : Sig} (Γ : Ctx [] s) (A : Ty [] s) (U : Ty [] (s,x)) :
    Fu (Option (CodTy Γ A U)) :=
  Fu.bind (upAt (Γ.cons A.weaken) .here U) fun r => unlessOut (strengthenAbove r)

/-- The method type for a call: from `{def l(x : S) : U}` and `A <: S`,
`{def l(x : A) : U0}` with `U0` the avoided codomain, by `stp_fun`.  `none` if
the tank ends marked. -/
def avoidArg {s : Sig} (Γ : Ctx [] s) (l : Lb) (S : Ty [] s) (U : Ty [] (s,x)) (A : Ty [] s)
    (eA : SStp Γ A S) : Fu (Option (ArgTy Γ l S U A)) :=
  mapO (avoidCod Γ A U) fun c => ⟨c.1, .stp_fun eA c.2⟩

/-! ## A codomain that strengthens comes back as itself -/

theorem avoidCod_strengthen {s : Sig} {Γ : Ctx [] s} {A : Ty [] s} {U : Ty [] (s,x)} {U0 : Ty [] s}
    {t : Tank} (h : FCdotR.Ty.strengthen? U = some U0) (ho : t.out = false) (hl : 1 ≤ t.left) :
    (avoidCod Γ A U t).1.map (·.1) = some U0 := by
  have hU : U = U0.weaken := FCdotR.Ty.strengthen?_sound h
  subst hU
  obtain ⟨n, b⟩ := t
  simp only at ho hl
  subst ho
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hup : upAt (Γ.cons A.weaken) .here U0.weaken ⟨n + 1, false⟩ =
      (⟨U0.weaken, refl _⟩, ⟨n, false⟩) := by
    show up (Γ.cons A.weaken) .here (n + 1) [] U0.weaken ⟨n + 1, false⟩ = _
    rw [up.eq_def]
    simp [Fu.bind, draw, cost, mentions_weaken, Fu.ret]
  simp only [avoidCod, Fu.bind]
  rw [hup]
  simp only [unlessOut, Bool.false_eq_true, if_false, Option.map_some, strengthenAbove]
  split
  · rename_i w hw
    rw [FCdotR.Ty.strengthenW?_weaken] at hw
    cases hw
    rfl
  · rename_i hw
    rw [FCdotR.Ty.strengthenW?_weaken] at hw
    cases hw

/-- A codomain that does not mention the parameter is kept: the call's type is
the codomain itself. -/
theorem avoidArg_weaken {s : Sig} {Γ : Ctx [] s} {l : Lb} {S : Ty [] s} {U0 A : Ty [] s}
    {eA : SStp Γ A S} {t : Tank} (ho : t.out = false) (hl : 1 ≤ t.left) :
    (avoidArg Γ l S U0.weaken A eA t).1.map (·.1) = some U0 := by
  have h := avoidCod_strengthen (Γ := Γ) (A := A) (FCdotR.Ty.strengthen?_weaken U0) ho hl
  simp only [avoidArg, mapO, Fu.bind, Fu.ret]
  cases hc : (avoidCod Γ A U0.weaken t).1 with
  | none => rw [hc] at h; simp at h
  | some c => rw [hc] at h; simpa using h

/-! ## The frame lemmas

A framed computation keeps a marked tank, never adds fuel, and does the same
with more fuel.  `up` and `down` at a larger index agree with the smaller one,
as `look` does (`look_agree`). -/

/-- At index zero the approximation marks the tank. -/
theorem out_framed {α : Type} (a : α) : Framed (fun t : Tank => (a, { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

/-- `up` and `down` are framed at every index. -/
theorem upDown_framed : ∀ (d : Nat) {s : Sig} (Γ : Ctx [] s) (z : BVar s .var)
    (P : List (Lb × Bool)) (T : Ty [] s), Framed (up Γ z d P T) ∧ Framed (down Γ z d P T)
  | 0, _, _, _, _, _ => ⟨out_framed _, out_framed _⟩
  | d + 1, s, Γ, z, P, T => by
    have ih : ∀ {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (P : List (Lb × Bool)) (T : Ty [] s),
        Framed (up Γ z d P T) ∧ Framed (down Γ z d P T) :=
      fun Γ z P T => upDown_framed d Γ z P T
    constructor
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | TSel p L =>
          cases p with
          | abs q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (members_framed Γ q L) fun ms => ?_
            refine bind_framed (flatMapL_framed (fun m => ?_) ms) fun _ => ret_framed _
            exact bind_framed (ih Γ z _ _).1 fun _ => ret_framed _
          | conc _ => exact ret_framed _
        | TFun l S U =>
          exact bind_framed (ih Γ z P S).2 fun a =>
            bind_framed (ih (Γ.cons a.1.weaken) (.there z) P U).1 fun _ => ret_framed _
        | TTyp l L H =>
          exact bind_framed (ih Γ z P L).2 fun _ =>
            bind_framed (ih Γ z P H).1 fun _ => ret_framed _
        | TAnd A B =>
          exact bind_framed (ih Γ z P A).1 fun _ =>
            bind_framed (ih Γ z P B).1 fun _ => ret_framed _
        | TOr A B =>
          exact bind_framed (ih Γ z P A).1 fun _ =>
            bind_framed (ih Γ z P B).1 fun _ => ret_framed _
        | TBind X => exact bind_framed (ih (Γ.cons X) (.there z) P X).1 fun _ => ret_framed _
        | TTop => exact ret_framed _
        | TBot => exact ret_framed _
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | TSel p L =>
          cases p with
          | abs q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (members_framed Γ q L) fun ms => ?_
            refine bind_framed (flatMapL_framed (fun m => ?_) ms) fun _ => ret_framed _
            exact bind_framed (ih Γ z _ _).2 fun _ => ret_framed _
          | conc _ => exact ret_framed _
        | TFun l S U =>
          exact bind_framed (ih Γ z P S).1 fun _ =>
            bind_framed (ih (Γ.cons S.weaken) (.there z) P U).2 fun _ => ret_framed _
        | TTyp l L H =>
          exact bind_framed (ih Γ z P L).1 fun _ =>
            bind_framed (ih Γ z P H).2 fun _ => ret_framed _
        | TAnd A B =>
          exact bind_framed (ih Γ z P A).2 fun _ =>
            bind_framed (ih Γ z P B).2 fun _ => ret_framed _
        | TOr A B =>
          exact bind_framed (ih Γ z P A).2 fun _ =>
            bind_framed (ih Γ z P B).2 fun _ => ret_framed _
        | TBind X =>
          exact bind_framed (ih (Γ.cons X) (.there z) P X).2 fun c1 =>
            bind_framed (ih (Γ.cons c1.1) (.there z) P X).2 fun _ => ret_framed _
        | TTop => exact ret_framed _
        | TBot => exact ret_framed _

/-- `up` and `down` at a larger index do what they do at a smaller one. -/
theorem upDown_agree : ∀ (d d' : Nat), d ≤ d' → ∀ {s : Sig} (Γ : Ctx [] s)
    (z : BVar s .var) (P : List (Lb × Bool)) (T : Ty [] s),
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
    have ih : ∀ {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (P : List (Lb × Bool)) (T : Ty [] s),
        Agree (up Γ z d P T) (up Γ z e P T) ∧ Agree (down Γ z d P T) (down Γ z e P T) :=
      fun Γ z P T => upDown_agree d e (by omega) Γ z P T
    constructor
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | TSel p L =>
          cases p with
          | abs q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (members_framed Γ q L)) fun ms => ?_
            refine bind_agree (flatMapL_agree (fun m => ?_) ms) fun _ => ret_agree _
            exact bind_agree (ih Γ z _ _).1 fun _ => ret_agree _
          | conc _ => exact ret_agree _
        | TFun l S U =>
          exact bind_agree (ih Γ z P S).2 fun a =>
            bind_agree (ih (Γ.cons a.1.weaken) (.there z) P U).1 fun _ => ret_agree _
        | TTyp l L H =>
          exact bind_agree (ih Γ z P L).2 fun _ =>
            bind_agree (ih Γ z P H).1 fun _ => ret_agree _
        | TAnd A B =>
          exact bind_agree (ih Γ z P A).1 fun _ =>
            bind_agree (ih Γ z P B).1 fun _ => ret_agree _
        | TOr A B =>
          exact bind_agree (ih Γ z P A).1 fun _ =>
            bind_agree (ih Γ z P B).1 fun _ => ret_agree _
        | TBind X => exact bind_agree (ih (Γ.cons X) (.there z) P X).1 fun _ => ret_agree _
        | TTop => exact ret_agree _
        | TBot => exact ret_agree _
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | TSel p L =>
          cases p with
          | abs q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (members_framed Γ q L)) fun ms => ?_
            refine bind_agree (flatMapL_agree (fun m => ?_) ms) fun _ => ret_agree _
            exact bind_agree (ih Γ z _ _).2 fun _ => ret_agree _
          | conc _ => exact ret_agree _
        | TFun l S U =>
          exact bind_agree (ih Γ z P S).1 fun _ =>
            bind_agree (ih (Γ.cons S.weaken) (.there z) P U).2 fun _ => ret_agree _
        | TTyp l L H =>
          exact bind_agree (ih Γ z P L).1 fun _ =>
            bind_agree (ih Γ z P H).2 fun _ => ret_agree _
        | TAnd A B =>
          exact bind_agree (ih Γ z P A).2 fun _ =>
            bind_agree (ih Γ z P B).2 fun _ => ret_agree _
        | TOr A B =>
          exact bind_agree (ih Γ z P A).2 fun _ =>
            bind_agree (ih Γ z P B).2 fun _ => ret_agree _
        | TBind X =>
          exact bind_agree (ih (Γ.cons X) (.there z) P X).2 fun c1 =>
            bind_agree (ih (Γ.cons c1.1) (.there z) P X).2 fun _ => ret_agree _
        | TTop => exact ret_agree _
        | TBot => exact ret_agree _

/-- `up` from the fuel left is framed. -/
theorem upAt_framed {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) :
    Framed (upAt Γ z T) where
  absorbs t ht := (upDown_framed t.left Γ z [] T).1.absorbs t ht
  spends t := (upDown_framed t.left Γ z [] T).1.spends t
  shift := by
    intro t r t' h ho k
    have h1 := (upDown_framed t.left Γ z [] T).1.shift t r t' h ho k
    have hag := (upDown_agree t.left (t.left + k) (Nat.le_add_right _ _) Γ z [] T).1
    change up Γ z (t.left + k) [] T (t.add k) = _
    rw [hag.sim t r t' h ho k]

/-- `down` from the fuel left is framed. -/
theorem downAt_framed {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) :
    Framed (downAt Γ z T) where
  absorbs t ht := (upDown_framed t.left Γ z [] T).2.absorbs t ht
  spends t := (upDown_framed t.left Γ z [] T).2.spends t
  shift := by
    intro t r t' h ho k
    have hag := (upDown_agree t.left (t.left + k) (Nat.le_add_right _ _) Γ z [] T).2
    change down Γ z (t.left + k) [] T (t.add k) = _
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

/-- Avoidance of a codomain is framed. -/
theorem avoidCod_framed {s : Sig} (Γ : Ctx [] s) (A : Ty [] s) (U : Ty [] (s,x)) :
    Framed (avoidCod Γ A U) :=
  bind_framed (upAt_framed _ _ _) fun _ => unlessOut_framed _

/-- Avoidance at a call is framed. -/
theorem avoidArg_framed {s : Sig} (Γ : Ctx [] s) (l : Lb) (S : Ty [] s) (U : Ty [] (s,x))
    (A : Ty [] s) (eA : SStp Γ A S) : Framed (avoidArg Γ l S U A eA) :=
  mapO_framed _ (avoidCod_framed Γ A U)

theorem avoidCod_frame {s : Sig} {Γ : Ctx [] s} {A : Ty [] s} {U : Ty [] (s,x)} {t t' : Tank}
    {r : Option (CodTy Γ A U)} (h : avoidCod Γ A U t = (r, t')) (ho : t'.out = false) (k : Nat) :
    avoidCod Γ A U (t.add k) = (r, t'.add k) :=
  (avoidCod_framed Γ A U).shift t r t' h ho k

theorem avoidArg_frame {s : Sig} {Γ : Ctx [] s} {l : Lb} {S : Ty [] s} {U : Ty [] (s,x)}
    {A : Ty [] s} {eA : SStp Γ A S} {t t' : Tank} {r : Option (ArgTy Γ l S U A)}
    (h : avoidArg Γ l S U A eA t = (r, t')) (ho : t'.out = false) (k : Nat) :
    avoidArg Γ l S U A eA (t.add k) = (r, t'.add k) :=
  (avoidArg_framed Γ l S U A eA).shift t r t' h ho k

/-- Avoidance from a marked tank answers `none` and leaves the tank as it is. -/
theorem avoidCod_absorbs {s : Sig} (Γ : Ctx [] s) (A : Ty [] s) (U : Ty [] (s,x)) {t : Tank}
    (h : t.out = true) : avoidCod Γ A U t = (none, t) := by
  have hu := (upAt_framed (Γ.cons A.weaken) .here U).absorbs t h
  simp only [avoidCod, Fu.bind]
  cases hup : upAt (Γ.cons A.weaken) .here U t with
  | mk a t1 =>
    rw [hup] at hu
    simp only at hu
    simp [hu, unlessOut, h]

theorem avoidArg_absorbs {s : Sig} (Γ : Ctx [] s) (l : Lb) (S : Ty [] s) (U : Ty [] (s,x))
    (A : Ty [] s) (eA : SStp Γ A S) {t : Tank} (h : t.out = true) :
    avoidArg Γ l S U A eA t = (none, t) := by
  simp only [avoidArg, mapO, Fu.bind, avoidCod_absorbs Γ A U h, Fu.ret, Option.map_none]

/-! ## Checks

Each check runs in the kernel at the default fuel.  `argAt`, `upTyAt` and
`downTyAt` start from a full tank. -/

section AvoidChecks

/-- The type of a call after avoidance, from a full tank of `n` units, and the
tank left. -/
def argAt {s : Sig} (Γ : Ctx [] s) (l : Lb) (S : Ty [] s) (U : Ty [] (s,x)) (A : Ty [] s)
    (eA : SStp Γ A S) (n : Nat := defaultFuel) : Option (Ty [] s) × Tank :=
  let r := avoidArg Γ l S U A eA ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- The approximation from above of `T` at `z`, from a full tank. -/
def upTyAt {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) (n : Nat := defaultFuel) :
    Ty [] s × Tank :=
  let r := upAt Γ z T ⟨n, false⟩
  (r.1.1, r.2)

/-- The approximation from below of `T` at `z`, from a full tank. -/
def downTyAt {s : Sig} (Γ : Ctx [] s) (z : BVar s .var) (T : Ty [] s) (n : Nat := defaultFuel) :
    Ty [] s × Tank :=
  let r := downAt Γ z T ⟨n, false⟩
  (r.1.1, r.2)

section Ex2

open FCdotR.CheckerExamples.DotExs (Γy polyId)

/-- `polyId`'s domain, `{0 : ⊥..⊤}`. -/
abbrev polyDom : Ty [] ([],x) := .TTyp 0 .TBot .TTop

/-- `polyId`'s codomain under its parameter `t`, `{def 0(x : t.0) : t.0}`. -/
abbrev polyCod : Ty [] ([],x,x) :=
  .TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0)

/-- The literal `new { o ⇒ type 0 = ⊤ }` and its self type `{0 : ⊤..⊤} ∧ ⊤`. -/
abbrev ex2Lit : Oopsla16.Dms [] ([],x,x) := .dcons (.dty .TTop) .dnil
abbrev ex2Self : Ty [] ([],x,x) := .TAnd (.TTyp 0 .TTop .TTop) .TTop

example : Γy.lookup .here = .TFun 0 polyDom polyCod := by decide

/-- The literal below `polyId`'s domain, found by the subtyping algorithm. -/
def ex2Arg : SStp Γy (.TBind ex2Self) polyDom :=
  (sub? Γy (.TBind ex2Self) polyDom).1.get (by decide +kernel)

/-- `ex2`, `y.0(new { o ⇒ type 0 = ⊤ })` for `y : polyId`, at the default
fuel. -/
def ex2Avoid : Option (ArgTy Γy 0 polyDom polyCod (.TBind ex2Self)) :=
  (avoidArg Γy 0 polyDom polyCod (.TBind ex2Self) ex2Arg ⟨defaultFuel, false⟩).1

-- The parameter `t` is avoided: `{def 0(x : t.0) : t.0}` becomes
-- `{def 0(x : ⊤) : ⊤}`, with the literal's lower bound in the domain and its
-- upper bound in the codomain.
theorem ex2_avoided : ex2Avoid.map (·.1) = some (.TFun 0 .TTop .TTop) := by decide +kernel

example : argAt Γy 0 polyDom polyCod (.TBind ex2Self) ex2Arg =
    (some (.TFun 0 .TTop .TTop), ⟨defaultFuel - 25, false⟩) := by decide +kernel

/-- The whole call at the avoided type: `y` widened by the derivation that
avoidance returns, then `T_App` with the literal by `T_Obj`. -/
def ex2Typed : HasType Store.nil Γy (.tapp (.tvar (.abs .here)) 0 (.tobj ex2Lit))
    (.TFun 0 .TTop .TTop) :=
  match h : ex2Avoid with
  | some r =>
      have hr : r.1 = .TFun 0 .TTop .TTop := by
        have := ex2_avoided
        rw [h] at this
        exact Option.some.inj this
      hr ▸ .T_App (.T_Sub .T_Varz r.2) (.T_Obj (.D_Typ .D_Nil))
  | none => absurd ex2_avoided (by rw [h]; simp)

-- A short tank marks the tank and the answer is `none`.
example : argAt Γy 0 polyDom polyCod (.TBind ex2Self) ex2Arg 3 = (none, ⟨0, true⟩) := by
  decide +kernel

-- A codomain that does not mention the parameter is kept.
example : argAt Γy 0 polyDom (Ty.TFun 3 .TTop .TBot).weaken (.TBind ex2Self) ex2Arg =
    (some (.TFun 3 .TTop .TBot), ⟨defaultFuel - 1, false⟩) := by decide +kernel
-- Under a recursive type, `μ(w. t.0)` from above is `μ(w. ⊤)`, by `stp_bindx`.
example : (argAt Γy 0 polyDom (.TBind (.TSel (.abs (.there .here)) 0)) (.TBind ex2Self) ex2Arg).1 =
    some (.TBind .TTop) := by decide +kernel
-- An empty tank gives `none`.
example : (argAt Γy 0 polyDom (Ty.TFun 3 .TTop .TBot).weaken (.TBind ex2Self) ex2Arg 0) =
    (none, ⟨0, true⟩) := by decide +kernel

end Ex2

/-- The method type `{def 9(y : ⊤) : ⊤}`. -/
abbrev F9 {s : Sig} : Ty [] s := fnTop 9

/-- A parameter with two members `0`: `{0 : ⊥..F} ∧ {0 : ⊥..⊤ ∧ ⊤}`. -/
def twoUpCtx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TAnd (.TTyp 0 .TBot F9) (.TTyp 0 .TBot (.TAnd .TTop .TTop)))

/-- A parameter with two members `0`: `{0 : F..⊤} ∧ {0 : ⊤ ∧ ⊤..⊤}`. -/
def twoDownCtx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TAnd (.TTyp 0 F9 .TTop) (.TTyp 0 (.TAnd .TTop .TTop) .TTop))

-- Two members at one label: the upper bounds are met.
theorem meet_two_members :
    (upTyAt twoUpCtx .here (.TSel (.abs .here) 0)).1 = .TAnd F9 (.TAnd .TTop .TTop) := by
  decide +kernel
example : upTyAt twoUpCtx .here (.TSel (.abs .here) 0) =
    (.TAnd F9 (.TAnd .TTop .TTop), ⟨defaultFuel - 10, false⟩) := by decide +kernel
-- From below the lower bounds are joined.
theorem join_two_members :
    (downTyAt twoDownCtx .here (.TSel (.abs .here) 0)).1 = .TOr F9 (.TAnd .TTop .TTop) := by
  decide +kernel
-- A method's domain is approximated from below.
example : (upTyAt twoDownCtx .here (.TFun 1 (.TSel (.abs .here) 0) .TTop)).1 =
    .TFun 1 (.TOr F9 (.TAnd .TTop .TTop)) .TTop := by decide +kernel

/-- A self alias: `z : μ(w. {0 : w.0..w.0})`. -/
def selfAliasCtx : Ctx [] ([],x) := Ctx.nil.cons (.TBind (.TTyp 0 (.TSel (.abs .here) 0)
  (.TSel (.abs .here) 0)))

-- The alias is expanded once per direction, then cut to the empty range.  The
-- tank stays unmarked.
example : upTyAt selfAliasCtx .here (.TSel (.abs .here) 0) =
    (.TTop, ⟨defaultFuel - 6, false⟩) := by decide +kernel
example : downTyAt selfAliasCtx .here (.TSel (.abs .here) 0) =
    (.TBot, ⟨defaultFuel - 6, false⟩) := by decide +kernel

section P3

/-- The receiver `y : {def 1(t : {1 : ⊥..⊤}) : {def 0(a : μ(w. {1 : ⊥..t.1} ∧
{0 : ⊥..w.1})) : ⊤}}`.  The codomain mentions the parameter `t` in a method's
domain, under a recursive type. -/
def yAM : Ty [] ([],x) :=
  .TFun 1 (.TTyp 1 .TBot .TTop)
    (.TFun 0 (.TBind (.TAnd (.TTyp 1 .TBot (.TSel (.abs (.there .here)) 1))
      (.TAnd (.TTyp 0 .TBot (.TSel (.abs .here) 1)) .TTop))) .TTop)

/-- The context `y : yAM`. -/
def ΓAM : Ctx [] ([],x) := Ctx.nil.cons yAM

/-- The codomain of `y`'s method `1` under its parameter. -/
def codAM : Ty [] ([],x,x) :=
  .TFun 0 (.TBind (.TAnd (.TTyp 1 .TBot (.TSel (.abs (.there .here)) 1))
      (.TAnd (.TTyp 0 .TBot (.TSel (.abs .here) 1)) .TTop))) .TTop

example : ΓAM.lookup .here = .TFun 1 (.TTyp 1 .TBot .TTop) codAM := by decide

/-- The argument `new { o ⇒ type 1 = ⊤  type 0 = ⊤ }` and its self type. -/
abbrev litAM : Oopsla16.Dms [] ([],x,x) := .dcons (.dty .TTop) (.dcons (.dty .TTop) .dnil)
abbrev litAMSelf : Ty [] ([],x,x) := .TAnd (.TTyp 1 .TTop .TTop) (.TAnd (.TTyp 0 .TTop .TTop) .TTop)

/-- The argument below the domain. -/
def argAM : SStp ΓAM (.TBind litAMSelf) (.TTyp 1 .TBot .TTop) :=
  (sub? ΓAM (.TBind litAMSelf) (.TTyp 1 .TBot .TTop)).1.get (by decide +kernel)

/-- The type the receiver keeps: `{def 0(a : μ(w. {1 : ⊥..⊤} ∧ {0 : ⊥..w.1})) : ⊤}`. -/
def recvAM : Ty [] ([],x) :=
  .TFun 0 (.TBind (.TAnd (.TTyp 1 .TBot .TTop)
    (.TAnd (.TTyp 0 .TBot (.TSel (.abs .here) 1)) .TTop))) .TTop

/-- `y.1(new { o ⇒ type 1 = ⊤  type 0 = ⊤ })`, at the default fuel. -/
def p3Avoid : Option (ArgTy ΓAM 1 (.TTyp 1 .TBot .TTop) codAM (.TBind litAMSelf)) :=
  (avoidArg ΓAM 1 (.TTyp 1 .TBot .TTop) codAM (.TBind litAMSelf) argAM ⟨defaultFuel, false⟩).1

-- The recursive type in the domain of `0` is kept.  Its body is approximated
-- from below: `t.1` becomes the literal's lower bound `⊤` and `w.1` stays.
theorem p3_avoided : p3Avoid.map (·.1) = some recvAM := by decide +kernel

example : argAt ΓAM 1 (.TTyp 1 .TBot .TTop) codAM (.TBind litAMSelf) argAM =
    (some recvAM, ⟨defaultFuel - 51, false⟩) := by decide +kernel

/-- The receiver at the avoided type, by `T_App`. -/
def p3Typed : HasType Store.nil ΓAM (.tapp (.tvar (.abs .here)) 1 (.tobj litAM)) recvAM :=
  match h : p3Avoid with
  | some r =>
      have hr : r.1 = recvAM := by
        have := p3_avoided
        rw [h] at this
        exact Option.some.inj this
      hr ▸ .T_App (.T_Sub .T_Varz r.2) (.T_Obj (.D_Typ (.D_Typ .D_Nil)))
  | none => absurd p3_avoided (by rw [h]; simp)

end P3

end AvoidChecks

end Oopsla16Frontend.Core
