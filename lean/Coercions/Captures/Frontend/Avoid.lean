import Coercions.Captures.Frontend.Sub

/-!
# Avoidance at a `let`, on the tank

The type of `let z = t in u` may not mention `z`.  When the body's type does,
the compiler approximates it by a type free of `z` (`avoid`,
`TypeOps.scala:474-509,565-583`).  This module does the same for the
version's types, which are a shape with a capture set.

`up` approximates a shape from above and `down` from below.  `capUp` and
`capDown` do the same for capture sets, following `mappedSet`
(`cc/CaptureSet.scala:1361-1368`).  Each returns the new shape or set with the
`SubShape` or `Subcap` derivation that relates it to the old one.

- A selection `z.A` at a covariant position becomes the meet of the avoided
  upper bounds of every member `A` that `z` has, as the compiler widens a
  selection at the merged bounds of its members (`derivedSelect` and
  `tryWiden`, `TypeOps.scala:519-522`).  The meet is an intersection, derived
  by `SubShape.and` of the `SubShape.selUpper` steps.  At a contravariant
  position `z.A` becomes the avoided lower bound of the first member.  The
  version has no union, so the lower bounds cannot be joined.
- The atom `{z}` at a covariant position becomes the declared set of `z`,
  by `Subcap.var`.  The compiler maps an avoided variable to
  `range(Nothing, info)` (`TypeOps.scala:477-481`), and `mappedSet` takes the
  set of its info at a covariant position (`cc/CaptureSet.scala:1366`).  At a
  contravariant position `{z}` is dropped, as `mappedSet` gives the empty set
  there (`cc/CaptureSet.scala:1367`).
- The atom `{z.C}` becomes the avoided upper bound of the first capture member
  `C` of `z` at a covariant position and its lower bound at a contravariant
  one, by `Subcap.selUpper` and `Subcap.selLower`.  The version has no meet
  of capture sets, so one member is read.  The compiler gives the empty set at
  a contravariant position unless the image is exact.  The lower bound is as
  sound and more precise.  At a covariant position a `{z.C}` with no member
  found stays, and then the strengthening at the `let` fails.  At a
  contravariant position it is dropped.
- `∀` flips its domain, `{A : L..U}` flips `L`, and `{C^ : c₁..c₂}` flips
  `c₁`.  The version's types have no invariant position, so the compiler's
  `Range` (`Types.scala:6902`) never arises.  Under a `∀` the codomain is
  approximated in the context extended by the domain that `SubShape.all`
  asks for.
- A selection or capture member already being expanded at the same polarity
  becomes `⊤`, `⊥`, the atom itself or the empty set, the compiler's
  `emptyRange` (`Types.scala:6608`).  A `μ` that mentions `z` has no
  subtyping rule in the version and becomes `⊤` or `⊥`.

All four draw on the tank of `Fuel.lean`.  A shape node costs `cost` of the
number of members being expanded.  A capture set that mentions `z` costs the
same, and one that does not is left as it is at no cost.  The members of a
selection are read by `declsAt` and `capsAt` on the same tank.  A short tank
answers `⊤`, `⊥`, the set as it is or the empty set, and is marked.  The structural index
starts at the fuel left, and every step down the index follows a draw of at
least one unit, so the index never runs out before the tank does.

`avoidLet` runs `up` and `capUp` at the binder of a `let` and strengthens the
result.  It returns the type `U` with `Sub (Γ.cons T0) V U.weaken`, which
`HasTy.let` takes through `HasTy.sub`.  It answers `none` when the tank ends
marked, the recursion limit, and when the result still mentions the binder,
a rejection.  A type that does not mention the binder comes back as itself,
strengthened (`avoidLet_strengthen`).  So avoidance never loses what
strengthening finds.  `avoidUses` does the same for the use set of the body,
which `HasTy.let` asks to be a weakening too.

Every computation here is framed, so a run that ends unmarked does the same
with more fuel (`avoidLet_frame`, `avoidUses_frame`).  Every definition is
structural, so the kernel evaluates avoidance.  The checks at the end run it
on the examples by `decide +kernel`.
-/

namespace CapturesFrontend.Core

open Frontend.Fuel
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open scoped Captures.DotMNF

/-! ## Mentions -/

/-- The atom mentions the variable `z`, as itself or as the prefix of a
capture member. -/
def mentionsA {s : Sig} (z : BVar s .var) : CapAtom s → Bool
  | .var y => decide (y = z)
  | .sel y _ => decide (y = z)
  | .cvar _ => false
  | .any => false

/-- The capture set mentions the variable `z`. -/
def mentionsC {s : Sig} (z : BVar s .var) (C : CaptureSet s) : Bool :=
  C.any (mentionsA z)

mutual

/-- The shape mentions the variable `z`, shifted under `μ` and `∀`. -/
def mentionsS {s : Sig} (z : BVar s .var) : Shape s → Bool
  | .sel (.var q) _ => decide (q = z)
  | .typ _ L H => mentionsS z L || mentionsS z H
  | .fld _ T => mentionsT z T
  | .cap _ c1 c2 => mentionsC z c1 || mentionsC z c2
  | .mu B => mentionsS (.there z) B
  | .all S T => mentionsT z S || mentionsT (.there z) T
  | .and S T => mentionsS z S || mentionsS z T
  | .box T => mentionsT z T
  | .top => false
  | .bot => false
termination_by structural S => S

/-- The type mentions the variable `z`. -/
def mentionsT {s : Sig} (z : BVar s .var) : Ty s → Bool
  | .capt C S => mentionsC z C || mentionsS z S
termination_by structural T => T

end

/-- Under a binder the lifted renaming never hits the shifted `z`. -/
theorem lift_avoids {s1 s2 : Sig} {ρ : Rename s1 s2} {z : BVar s2 .var}
    (h : ∀ y : BVar s1 .var, ρ.var y ≠ z) : ∀ y : BVar (s1,x) .var, ρ.lift.var y ≠ .there z
  | .here => by simp
  | .there y => by
    simp only [Rename.lift_there, ne_eq, BVar.there.injEq]
    exact h y

/-- A renaming that never hits `z` gives an atom that does not mention `z`. -/
theorem mentionsA_rename {s1 s2 : Sig} (a : CapAtom s1) (ρ : Rename s1 s2) (z : BVar s2 .var)
    (h : ∀ y : BVar s1 .var, ρ.var y ≠ z) : mentionsA z (a.rename ρ) = false := by
  cases a with
  | var y => simp only [CapAtom.rename, mentionsA, decide_eq_false_iff_not]; exact h y
  | sel y A => simp only [CapAtom.rename, mentionsA, decide_eq_false_iff_not]; exact h y
  | cvar _ => rfl
  | any => rfl

/-- A renaming that never hits `z` gives a set that does not mention `z`. -/
theorem mentionsC_rename {s1 s2 : Sig} (C : CaptureSet s1) (ρ : Rename s1 s2) (z : BVar s2 .var)
    (h : ∀ y : BVar s1 .var, ρ.var y ≠ z) : mentionsC z (C.rename ρ) = false := by
  induction C with
  | nil => rfl
  | cons a C ih =>
    simp only [mentionsC] at ih ⊢
    simp only [CaptureSet.rename_cons, List.any_cons, mentionsA_rename a ρ z h, ih, Bool.or_false]

mutual

/-- A renaming that never hits `z` gives a shape that does not mention `z`. -/
theorem mentionsS_rename : ∀ {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2) (z : BVar s2 .var),
    (∀ y : BVar s1 .var, ρ.var y ≠ z) → mentionsS z (S.rename ρ) = false
  | _, _, .top, _, _, _ => rfl
  | _, _, .bot, _, _, _ => rfl
  | _, _, .typ _ L H, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsS_rename L ρ z h, mentionsS_rename H ρ z h,
      Bool.or_false]
  | _, _, .fld _ T, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsT_rename T ρ z h]
  | _, _, .cap _ c1 c2, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsC_rename c1 ρ z h, mentionsC_rename c2 ρ z h,
      Bool.or_false]
  | _, _, .sel (.var q) _, ρ, z, h => by
    simp only [Shape.rename, Path.rename, mentionsS, decide_eq_false_iff_not]
    exact h q
  | _, _, .mu B, ρ, z, h => by
    simp only [Shape.rename, mentionsS]
    exact mentionsS_rename B ρ.lift (.there z) (lift_avoids h)
  | _, _, .all S T, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsT_rename S ρ z h,
      mentionsT_rename T ρ.lift (.there z) (lift_avoids h), Bool.or_false]
  | _, _, .and S T, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsS_rename S ρ z h, mentionsS_rename T ρ z h,
      Bool.or_false]
  | _, _, .box T, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsT_rename T ρ z h]
termination_by structural _ _ S => S

/-- A renaming that never hits `z` gives a type that does not mention `z`. -/
theorem mentionsT_rename : ∀ {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) (z : BVar s2 .var),
    (∀ y : BVar s1 .var, ρ.var y ≠ z) → mentionsT z (T.rename ρ) = false
  | _, _, .capt C S, ρ, z, h => by
    simp only [Ty.rename, mentionsT, mentionsC_rename C ρ z h, mentionsS_rename S ρ z h,
      Bool.or_false]
termination_by structural _ _ T => T

end

/-- A weakened shape does not mention the new binder. -/
theorem mentionsS_weaken {s : Sig} (S : Shape s) : mentionsS .here (S.weaken (k := .var)) = false :=
  mentionsS_rename S Rename.succ .here fun y => by simp

/-- A weakened capture set does not mention the new binder. -/
theorem mentionsC_weaken {s : Sig} (C : CaptureSet s) :
    mentionsC .here (CaptureSet.weaken (k := .var) C) = false :=
  mentionsC_rename C Rename.succ .here fun y => by simp

/-! ## The approximations -/

/-- A shape above `S`, with the derivation. -/
abbrev Above {s : Sig} (Γ : Ctx s) (S : Shape s) : Type := (U : Shape s) × SubShape Γ S U

/-- A shape below `S`, with the derivation. -/
abbrev Below {s : Sig} (Γ : Ctx s) (S : Shape s) : Type := (U : Shape s) × SubShape Γ U S

/-- A capture set above `C`, with the derivation. -/
abbrev CapAbove {s : Sig} (Γ : Ctx s) (C : CaptureSet s) : Type :=
  (D : CaptureSet s) × Subcap Γ C D

/-- A capture set below `C`, with the derivation. -/
abbrev CapBelow {s : Sig} (Γ : Ctx s) (C : CaptureSet s) : Type :=
  (D : CaptureSet s) × Subcap Γ D C

/-- A type above `T`, with the derivation. -/
abbrev TyAbove {s : Sig} (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × Sub Γ T U

/-- A member being expanded: its kind and label, and the polarity, `true` for
an upper bound. -/
abbrev AKey := Key × Bool

/-- The meet of shapes above `S`: their intersection, by `SubShape.and`.  One
shape is itself, and no shape is `⊤`. -/
def meetAll {s : Sig} {Γ : Ctx s} {S : Shape s} : List (Above Γ S) → Above Γ S
  | [] => ⟨.top, .top⟩
  | [a] => a
  | a :: b :: rest =>
      let r := meetAll (b :: rest)
      ⟨.and a.1 r.1, .and a.2 r.2⟩
termination_by structural l => l

/-- `capJoin` is included in the concatenation. -/
theorem capJoin_sub_append {s : Sig} (C D : CaptureSet s) :
    CaptureSet.Subset (capJoin C D) (C ++ D) := by
  intro a h
  simp only [capJoin, List.mem_append, List.mem_filter] at h ⊢
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- An upper image per atom, joined over the set by `Subcap.union`. -/
def capMapUp {s : Sig} {Γ : Ctx s} (f : (a : CapAtom s) → Fu (CapAbove Γ [a])) :
    (C : CaptureSet s) → Fu (CapAbove Γ C)
  | [] => Fu.ret ⟨[], .refl⟩
  | a :: C =>
      Fu.bind (f a) fun r1 =>
        Fu.bind (capMapUp f C) fun r2 =>
          Fu.ret ⟨capJoin r1.1 r2.1, Subcap.union (C1 := [a]) (C2 := C)
            (.trans r1.2 (.elem (capJoin_left _ _))) (.trans r2.2 (.elem (capJoin_right _ _)))⟩
termination_by structural C => C

/-- A lower image per atom, joined over the set. -/
def capMapDown {s : Sig} {Γ : Ctx s} (f : (a : CapAtom s) → Fu (CapBelow Γ [a])) :
    (C : CaptureSet s) → Fu (CapBelow Γ C)
  | [] => Fu.ret ⟨[], .refl⟩
  | a :: C =>
      Fu.bind (f a) fun r1 =>
        Fu.bind (capMapDown f C) fun r2 =>
          Fu.ret ⟨capJoin r1.1 r2.1, Subcap.trans (.elem (capJoin_sub_append _ _)) <| Subcap.union
            (.trans r1.2 (.elem (fun _ h => by
              simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..)))
            (.trans r2.2 (.elem (fun _ h => List.mem_cons_of_mem _ h)))⟩
termination_by structural C => C

mutual

/-- An approximation of the shape `S` from above that does not mention `z`.
`P` holds the members being expanded, each with its polarity.  The index `d`
is structural. -/
def up {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List AKey → (S : Shape s) →
    Fu (Above Γ S)
  | 0, _, _ => fun t => (⟨.top, .top⟩, { t with out := true })
  | d + 1, P, S =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.top, .top⟩
        | true =>
          if !mentionsS z S then Fu.ret ⟨S, .refl⟩ else
          match S with
          | .sel (.var q) A =>
              if (Key.typ A, true) ∈ P then Fu.ret ⟨.top, .top⟩ else
              Fu.bind (declsAt Γ q A) fun ms =>
                Fu.bind (Fu.flatMapL (fun m =>
                    Fu.bind (up Γ z d ((Key.typ A, true) :: P) m.2.1) fun r =>
                      Fu.ret [⟨r.1, .trans (.selUpper m.2.2) r.2⟩]) ms) fun rs =>
                  Fu.ret (meetAll rs)
          | .fld a (.capt C S') =>
              Fu.bind (up Γ z d P S') fun r =>
                Fu.bind (capUp Γ z d P C) fun c => Fu.ret ⟨.fld a (r.1 ^ c.1), .fld (.capt r.2 c.2)⟩
          | .typ A L H =>
              Fu.bind (down Γ z d P L) fun l =>
                Fu.bind (up Γ z d P H) fun h => Fu.ret ⟨.typ A l.1 h.1, .typ l.2 h.2⟩
          | .cap A c1 c2 =>
              Fu.bind (capDown Γ z d P c1) fun l =>
                Fu.bind (capUp Γ z d P c2) fun h => Fu.ret ⟨.cap A l.1 h.1, .cap l.2 h.2⟩
          | .and S1 S2 =>
              Fu.bind (up Γ z d P S1) fun r1 =>
                Fu.bind (up Γ z d P S2) fun r2 =>
                  Fu.ret ⟨.and r1.1 r2.1, .and (.trans .and1 r1.2) (.trans .and2 r2.2)⟩
          | .box (.capt C S') =>
              Fu.bind (up Γ z d P S') fun r =>
                Fu.bind (capUp Γ z d P C) fun c => Fu.ret ⟨.box (r.1 ^ c.1), .box (.capt r.2 c.2)⟩
          | .all (.capt C1 S1) (.capt C2 S2) =>
              Fu.bind (down Γ z d P S1) fun l =>
                Fu.bind (capDown Γ z d P C1) fun lc =>
                  Fu.bind (up (Γ.cons (l.1 ^ lc.1)) (.there z) d P S2) fun r =>
                    Fu.bind (capUp (Γ.cons (l.1 ^ lc.1)) (.there z) d P C2) fun rc =>
                      Fu.ret ⟨.all (l.1 ^ lc.1) (r.1 ^ rc.1), .all (.capt l.2 lc.2) (.capt r.2 rc.2)⟩
          | _ => Fu.ret ⟨.top, .top⟩
termination_by structural d _ _ => d

/-- An approximation of the shape `S` from below that does not mention `z`.
`P` is as for `up`.  The index `d` is structural. -/
def down {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List AKey → (S : Shape s) →
    Fu (Below Γ S)
  | 0, _, _ => fun t => (⟨.bot, .bot⟩, { t with out := true })
  | d + 1, P, S =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.bot, .bot⟩
        | true =>
          if !mentionsS z S then Fu.ret ⟨S, .refl⟩ else
          match S with
          | .sel (.var q) A =>
              if (Key.typ A, false) ∈ P then Fu.ret ⟨.bot, .bot⟩ else
              Fu.bind (declsAt Γ q A) fun
                | m :: _ =>
                    Fu.bind (down Γ z d ((Key.typ A, false) :: P) m.1) fun r =>
                      Fu.ret ⟨r.1, .trans r.2 (.selLower m.2.2)⟩
                | [] => Fu.ret ⟨.bot, .bot⟩
          | .fld a (.capt C S') =>
              Fu.bind (down Γ z d P S') fun r =>
                Fu.bind (capDown Γ z d P C) fun c => Fu.ret ⟨.fld a (r.1 ^ c.1), .fld (.capt r.2 c.2)⟩
          | .typ A L H =>
              Fu.bind (up Γ z d P L) fun l =>
                Fu.bind (down Γ z d P H) fun h => Fu.ret ⟨.typ A l.1 h.1, .typ l.2 h.2⟩
          | .cap A c1 c2 =>
              Fu.bind (capUp Γ z d P c1) fun l =>
                Fu.bind (capDown Γ z d P c2) fun h => Fu.ret ⟨.cap A l.1 h.1, .cap l.2 h.2⟩
          | .and S1 S2 =>
              Fu.bind (down Γ z d P S1) fun r1 =>
                Fu.bind (down Γ z d P S2) fun r2 =>
                  Fu.ret ⟨.and r1.1 r2.1, .and (.trans .and1 r1.2) (.trans .and2 r2.2)⟩
          | .box (.capt C S') =>
              Fu.bind (down Γ z d P S') fun r =>
                Fu.bind (capDown Γ z d P C) fun c => Fu.ret ⟨.box (r.1 ^ c.1), .box (.capt r.2 c.2)⟩
          | .all (.capt C1 S1) (.capt C2 S2) =>
              Fu.bind (up Γ z d P S1) fun l =>
                Fu.bind (capUp Γ z d P C1) fun lc =>
                  Fu.bind (down (Γ.cons (S1 ^ C1)) (.there z) d P S2) fun r =>
                    Fu.bind (capDown (Γ.cons (S1 ^ C1)) (.there z) d P C2) fun rc =>
                      Fu.ret ⟨.all (l.1 ^ lc.1) (r.1 ^ rc.1), .all (.capt l.2 lc.2) (.capt r.2 rc.2)⟩
          | _ => Fu.ret ⟨.bot, .bot⟩
termination_by structural d _ _ => d

/-- An approximation of the capture set `C` from above that does not mention
`z`.  `{z}` becomes the declared set of `z`, and `{z.C}` the upper bound of
the first capture member `C` of `z`.  A set that does not mention `z` is left
as it is at no cost.  The index `d` is structural. -/
def capUp {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List AKey → (C : CaptureSet s) →
    Fu (CapAbove Γ C)
  | 0, _, C =>
      if !mentionsC z C then Fu.ret ⟨C, .refl⟩ else fun t => (⟨C, .refl⟩, { t with out := true })
  | d + 1, P, C =>
      if !mentionsC z C then Fu.ret ⟨C, .refl⟩ else
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨C, .refl⟩
        | true =>
          capMapUp (fun
            | .var y =>
                if y = z then
                  Fu.bind (capUp Γ z d P (Γ.lookup y).captureSet) fun r =>
                    Fu.ret ⟨r.1, .trans .var r.2⟩
                else Fu.ret ⟨[.var y], .refl⟩
            | .sel y A =>
                if y = z ∧ (Key.cap A, true) ∉ P then
                  Fu.bind (capsAt Γ y A) fun
                    | m :: _ =>
                        Fu.bind (capUp Γ z d ((Key.cap A, true) :: P) m.2.1) fun r =>
                          Fu.ret ⟨r.1, .trans (.selUpper m.2.2) r.2⟩
                    | [] => Fu.ret ⟨[.sel y A], .refl⟩
                else Fu.ret ⟨[.sel y A], .refl⟩
            | .cvar k => Fu.ret ⟨[.cvar k], .refl⟩
            | .any => Fu.ret ⟨[.any], .refl⟩) C
termination_by structural d _ _ => d

/-- An approximation of the capture set `C` from below that does not mention
`z`.  `{z}` is dropped, and `{z.C}` becomes the lower bound of the first
capture member `C` of `z`, or is dropped when there is none.  A set that does
not mention `z` is left as it is at no cost.  The index `d` is structural. -/
def capDown {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List AKey → (C : CaptureSet s) →
    Fu (CapBelow Γ C)
  | 0, _, C =>
      if !mentionsC z C then Fu.ret ⟨C, .refl⟩
      else fun t => (⟨[], .elem (CaptureSet.nil_subset C)⟩, { t with out := true })
  | d + 1, P, C =>
      if !mentionsC z C then Fu.ret ⟨C, .refl⟩ else
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨[], .elem (CaptureSet.nil_subset C)⟩
        | true =>
          capMapDown (fun
            | .var y =>
                if y = z then Fu.ret ⟨[], .elem (CaptureSet.nil_subset _)⟩
                else Fu.ret ⟨[.var y], .refl⟩
            | .sel y A =>
                if y = z then
                  if (Key.cap A, false) ∈ P then Fu.ret ⟨[], .elem (CaptureSet.nil_subset _)⟩ else
                  Fu.bind (capsAt Γ y A) fun
                    | m :: _ =>
                        Fu.bind (capDown Γ z d ((Key.cap A, false) :: P) m.1) fun r =>
                          Fu.ret ⟨r.1, .trans r.2 (.selLower m.2.2)⟩
                    | [] => Fu.ret ⟨[], .elem (CaptureSet.nil_subset _)⟩
                else Fu.ret ⟨[.sel y A], .refl⟩
            | .cvar k => Fu.ret ⟨[.cvar k], .refl⟩
            | .any => Fu.ret ⟨[.any], .refl⟩) C
termination_by structural d _ _ => d

end

/-- A type approximated from above: its shape by `up`, then its set by
`capUp`, at one index. -/
def tyUp {s : Sig} (Γ : Ctx s) (z : BVar s .var) (d : Nat) (P : List AKey) :
    (T : Ty s) → Fu (TyAbove Γ T)
  | .capt C S =>
      Fu.bind (up Γ z d P S) fun r =>
        Fu.bind (capUp Γ z d P C) fun c => Fu.ret ⟨r.1 ^ c.1, .capt r.2 c.2⟩

/-- `tyUp` on the tank it is handed, with the fuel left as its index. -/
def tyUpAt {s : Sig} (Γ : Ctx s) (z : BVar s .var) (T : Ty s) : Fu (TyAbove Γ T) := fun t =>
  tyUp Γ z t.left [] T t

/-- `capUp` on the tank it is handed, with the fuel left as its index. -/
def capUpAt {s : Sig} (Γ : Ctx s) (z : BVar s .var) (C : CaptureSet s) : Fu (CapAbove Γ C) :=
  fun t => capUp Γ z t.left [] C t

/-- The type of a `let` body after avoidance, as `HasTy.let` asks for it. -/
abbrev LetTy {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) : Type :=
  (U : Ty s) × Sub (Γ.cons T0) V U.weaken

/-- The use set of a `let` body after avoidance, as `HasTy.let` asks for it. -/
abbrev LetUses {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : CaptureSet (s,x)) : Type :=
  (U : CaptureSet s) × Subcap (Γ.cons T0) V (CaptureSet.weaken U)

/-- Strengthen an approximation that no longer mentions the binder.  If it
still mentions it, there is no answer. -/
def strengthenTy {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} (r : TyAbove (Γ.cons T0) V) :
    Option (LetTy Γ T0 V) :=
  match tyStrengthenW? r.1 with
  | some w => some ⟨w.val, w.property ▸ r.2⟩
  | none => none

/-- Strengthen an approximated set that no longer mentions the binder.  If it
still mentions it, there is no answer. -/
def strengthenSet {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : CaptureSet (s,x)}
    (r : CapAbove (Γ.cons T0) V) : Option (LetUses Γ T0 V) :=
  match capStrengthenW? r.1 with
  | some w => some ⟨w.val, w.property ▸ r.2⟩
  | none => none

/-- Answer `none` on a marked tank, and `o` otherwise. -/
def unlessOut {α : Type} (o : Option α) : Fu (Option α) := fun t =>
  if t.out then (none, t) else (o, t)

/-- The result type of a `let` without annotation: the body's type `V`,
approximated from above until it no longer mentions the binder, then
strengthened.  `none` if the tank ends marked, or if a capture member of the
binder has no bound to go to. -/
def avoidLet {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) : Fu (Option (LetTy Γ T0 V)) :=
  Fu.bind (tyUpAt (Γ.cons T0) .here V) fun r => unlessOut (strengthenTy r)

/-- The use set of a `let` without the binder: the body's use set `V`
approximated from above, `{x}` by the set of the bound term's type and
`{x.C}` by the upper bound of the member, then strengthened.  `none` if the
tank ends marked, or if a capture member of the binder has no bound to go
to. -/
def avoidUses {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : CaptureSet (s,x)) :
    Fu (Option (LetUses Γ T0 V)) :=
  Fu.bind (capUpAt (Γ.cons T0) .here V) fun r => unlessOut (strengthenSet r)

/-! ## A type that strengthens comes back as itself -/

/-- `capUp` leaves a set that does not mention `z` as it is, at no cost. -/
theorem capUp_free {s : Sig} {Γ : Ctx s} {z : BVar s .var} {C : CaptureSet s}
    (h : mentionsC z C = false) (d : Nat) (P : List AKey) (t : Tank) :
    capUp Γ z d P C t = (⟨C, .refl⟩, t) := by
  cases d <;> simp [capUp, h, Fu.ret]

theorem avoidLet_strengthen {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} {U : Ty s} {t : Tank}
    (h : tyStrengthen? V = some U) (ho : t.out = false) (hl : 1 ≤ t.left) :
    (avoidLet Γ T0 V t).1.map (·.1) = some U := by
  have hV : V = U.weaken := tyStrengthen?_sound h
  subst hV
  obtain ⟨n, b⟩ := t
  simp only at ho hl
  subst ho
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨C, S⟩ := U
  have hup : up (Γ.cons T0) .here (n + 1) [] (S.weaken (k := .var)) ⟨n + 1, false⟩ =
      (⟨S.weaken, .refl⟩, ⟨n, false⟩) := by
    rw [up.eq_def]
    simp [Fu.bind, draw, cost, mentionsS_weaken, Fu.ret]
  have hty : tyUpAt (Γ.cons T0) .here (Ty.weaken (k := .var) (S ^ C)) ⟨n + 1, false⟩ =
      (⟨S.weaken ^ CaptureSet.weaken C, .capt .refl .refl⟩, ⟨n, false⟩) := by
    show tyUp (Γ.cons T0) .here (n + 1) [] (Ty.capt (CaptureSet.weaken C) S.weaken) ⟨n + 1, false⟩ = _
    simp only [tyUp, Fu.bind]
    rw [hup]
    simp only
    rw [capUp_free (mentionsC_weaken C)]
    rfl
  simp only [avoidLet, Fu.bind]
  rw [hty]
  simp only [unlessOut, Bool.false_eq_true, if_false, strengthenTy]
  split
  · rename_i w hw
    have h2 : tyStrengthenW? (Ty.weaken (k := .var) (S ^ C)) = some w := hw
    rw [tyStrengthenW?_weaken] at h2
    cases h2
    rfl
  · rename_i hw
    have h2 : tyStrengthenW? (Ty.weaken (k := .var) (S ^ C)) = none := hw
    rw [tyStrengthenW?_weaken] at h2
    cases h2

/-- The same for a use set: one that strengthens comes back as itself, at no
cost. -/
theorem avoidUses_strengthen {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : CaptureSet (s,x)}
    {U : CaptureSet s} {t : Tank} (h : capStrengthen? V = some U) (ho : t.out = false) :
    (avoidUses Γ T0 V t).1.map (·.1) = some U := by
  have hV : V = CaptureSet.weaken U := capStrengthen?_sound h
  subst hV
  simp only [avoidUses, Fu.bind, capUpAt]
  rw [capUp_free (mentionsC_weaken U)]
  simp only [unlessOut, ho, Bool.false_eq_true, if_false, strengthenSet]
  split
  · rename_i w hw
    rw [capStrengthenW?_weaken] at hw
    cases hw
    rfl
  · rename_i hw
    rw [capStrengthenW?_weaken] at hw
    cases hw

/-! ## The frame lemmas

Every computation of this module is framed: it keeps a marked tank, never adds
fuel, and does the same with more fuel.  `up`, `down`, `capUp` and `capDown`
at a larger index do what they do at a smaller one, as `look` does
(`look_agree`).  So `tyUpAt` and `capUpAt`, whose index is the fuel left, are
framed, as `declsAt` is. -/

/-- At index zero an approximation marks the tank. -/
theorem out_framed {α : Type} (a : α) : Framed (fun t : Tank => (a, { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

/-- A computation that marks the tank agrees with any framed one, since it
never ends unmarked. -/
theorem out_agree {α : Type} (a : α) {c : Fu α} (hc : Framed c) :
    Agree (fun t : Tank => (a, { t with out := true })) c :=
  ⟨out_framed a, hc, by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho⟩

theorem meet_framed {s : Sig} {Γ : Ctx s} {S : Shape s} (rs : List (Above Γ S)) :
    Framed (Fu.ret (meetAll rs)) := ret_framed _

section MapFrames

variable {s : Sig} {Γ : Ctx s}

theorem capMapUp_framed {f : (a : CapAtom s) → Fu (CapAbove Γ [a])} (hf : ∀ a, Framed (f a)) :
    ∀ C, Framed (capMapUp f C)
  | [] => ret_framed _
  | a :: C => bind_framed (hf a) fun _ => bind_framed (capMapUp_framed hf C) fun _ => ret_framed _

theorem capMapUp_agree {f f' : (a : CapAtom s) → Fu (CapAbove Γ [a])}
    (hf : ∀ a, Agree (f a) (f' a)) : ∀ C, Agree (capMapUp f C) (capMapUp f' C)
  | [] => ret_agree _
  | a :: C => bind_agree (hf a) fun _ => bind_agree (capMapUp_agree hf C) fun _ => ret_agree _

theorem capMapDown_framed {f : (a : CapAtom s) → Fu (CapBelow Γ [a])} (hf : ∀ a, Framed (f a)) :
    ∀ C, Framed (capMapDown f C)
  | [] => ret_framed _
  | a :: C => bind_framed (hf a) fun _ => bind_framed (capMapDown_framed hf C) fun _ => ret_framed _

theorem capMapDown_agree {f f' : (a : CapAtom s) → Fu (CapBelow Γ [a])}
    (hf : ∀ a, Agree (f a) (f' a)) : ∀ C, Agree (capMapDown f C) (capMapDown f' C)
  | [] => ret_agree _
  | a :: C => bind_agree (hf a) fun _ => bind_agree (capMapDown_agree hf C) fun _ => ret_agree _

end MapFrames

/-- `capUp` leaves a set that does not mention `z` as it is, at every index. -/
theorem capUp_eq_free {s : Sig} {Γ : Ctx s} {z : BVar s .var} {C : CaptureSet s}
    (h : mentionsC z C = false) (d : Nat) (P : List AKey) :
    capUp Γ z d P C = Fu.ret ⟨C, .refl⟩ := by
  cases d <;> simp [capUp, h]

/-- `capDown` leaves a set that does not mention `z` as it is, at every index. -/
theorem capDown_eq_free {s : Sig} {Γ : Ctx s} {z : BVar s .var} {C : CaptureSet s}
    (h : mentionsC z C = false) (d : Nat) (P : List AKey) :
    capDown Γ z d P C = Fu.ret ⟨C, .refl⟩ := by
  cases d <;> simp [capDown, h]

/-- `up`, `down`, `capUp` and `capDown` are framed at every index. -/
theorem avoid_framed : ∀ (d : Nat) {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List AKey)
    (S : Shape s) (C : CaptureSet s),
    Framed (up Γ z d P S) ∧ Framed (down Γ z d P S) ∧ Framed (capUp Γ z d P C) ∧
      Framed (capDown Γ z d P C)
  | 0, _, _, _, _, _, _ =>
    ⟨out_framed _, out_framed _, ite_framed (ret_framed _) (out_framed _),
      ite_framed (ret_framed _) (out_framed _)⟩
  | d + 1, s, Γ, z, P, S, C => by
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List AKey) (S : Shape s)
        (C : CaptureSet s),
        Framed (up Γ z d P S) ∧ Framed (down Γ z d P S) ∧ Framed (capUp Γ z d P C) ∧
          Framed (capDown Γ z d P C) := fun Γ z P S C => avoid_framed d Γ z P S C
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (declsAt_framed Γ q A) fun ms => ?_
            refine bind_framed (flatMapL_framed (fun m => ?_) ms) fun _ => ret_framed _
            exact bind_framed (ih Γ z _ _ C).1 fun _ => ret_framed _
        | fld a T =>
          cases T with
          | capt C' S' =>
            exact bind_framed (ih Γ z P S' C).1 fun _ =>
              bind_framed (ih Γ z P S' C').2.2.1 fun _ => ret_framed _
        | typ A L H =>
          exact bind_framed (ih Γ z P L C).2.1 fun _ =>
            bind_framed (ih Γ z P H C).1 fun _ => ret_framed _
        | cap A c1 c2 =>
          exact bind_framed (ih Γ z P .top c1).2.2.2 fun _ =>
            bind_framed (ih Γ z P .top c2).2.2.1 fun _ => ret_framed _
        | and S1 S2 =>
          exact bind_framed (ih Γ z P S1 C).1 fun _ =>
            bind_framed (ih Γ z P S2 C).1 fun _ => ret_framed _
        | box T =>
          cases T with
          | capt C' S' =>
            exact bind_framed (ih Γ z P S' C).1 fun _ =>
              bind_framed (ih Γ z P S' C').2.2.1 fun _ => ret_framed _
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              exact bind_framed (ih Γ z P S1 C1).2.1 fun l =>
                bind_framed (ih Γ z P S1 C1).2.2.2 fun lc =>
                  bind_framed (ih (Γ.cons (l.1 ^ lc.1)) (.there z) P S2 C2).1 fun _ =>
                    bind_framed (ih (Γ.cons (l.1 ^ lc.1)) (.there z) P S2 C2).2.2.1 fun _ =>
                      ret_framed _
        | mu _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _
    · apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_framed (ret_framed _)
            refine bind_framed (declsAt_framed Γ q A) fun ms => ?_
            cases ms with
            | nil => exact ret_framed _
            | cons m _ => exact bind_framed (ih Γ z _ _ C).2.1 fun _ => ret_framed _
        | fld a T =>
          cases T with
          | capt C' S' =>
            exact bind_framed (ih Γ z P S' C).2.1 fun _ =>
              bind_framed (ih Γ z P S' C').2.2.2 fun _ => ret_framed _
        | typ A L H =>
          exact bind_framed (ih Γ z P L C).1 fun _ =>
            bind_framed (ih Γ z P H C).2.1 fun _ => ret_framed _
        | cap A c1 c2 =>
          exact bind_framed (ih Γ z P .top c1).2.2.1 fun _ =>
            bind_framed (ih Γ z P .top c2).2.2.2 fun _ => ret_framed _
        | and S1 S2 =>
          exact bind_framed (ih Γ z P S1 C).2.1 fun _ =>
            bind_framed (ih Γ z P S2 C).2.1 fun _ => ret_framed _
        | box T =>
          cases T with
          | capt C' S' =>
            exact bind_framed (ih Γ z P S' C).2.1 fun _ =>
              bind_framed (ih Γ z P S' C').2.2.2 fun _ => ret_framed _
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              exact bind_framed (ih Γ z P S1 C1).1 fun _ =>
                bind_framed (ih Γ z P S1 C1).2.2.1 fun _ =>
                  bind_framed (ih (Γ.cons (S1 ^ C1)) (.there z) P S2 C2).2.1 fun _ =>
                    bind_framed (ih (Γ.cons (S1 ^ C1)) (.there z) P S2 C2).2.2.2 fun _ =>
                      ret_framed _
        | mu _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _
    · apply ite_framed (ret_framed _)
      apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · refine capMapUp_framed (fun a => ?_) C
        cases a with
        | var y =>
          exact ite_framed (bind_framed (ih Γ z P S _).2.2.1 fun _ => ret_framed _) (ret_framed _)
        | sel y A =>
          refine ite_framed (bind_framed (capsAt_framed Γ y A) fun ms => ?_) (ret_framed _)
          cases ms with
          | nil => exact ret_framed _
          | cons m _ => exact bind_framed (ih Γ z _ S _).2.2.1 fun _ => ret_framed _
        | cvar _ => exact ret_framed _
        | any => exact ret_framed _
    · apply ite_framed (ret_framed _)
      apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · refine capMapDown_framed (fun a => ?_) C
        cases a with
        | var y => exact ite_framed (ret_framed _) (ret_framed _)
        | sel y A =>
          refine ite_framed (ite_framed (ret_framed _)
            (bind_framed (capsAt_framed Γ y A) fun ms => ?_)) (ret_framed _)
          cases ms with
          | nil => exact ret_framed _
          | cons m _ => exact bind_framed (ih Γ z _ S _).2.2.2 fun _ => ret_framed _
        | cvar _ => exact ret_framed _
        | any => exact ret_framed _

/-- `up`, `down`, `capUp` and `capDown` at a larger index do what they do at a
smaller one. -/
theorem avoid_agree : ∀ (d d' : Nat), d ≤ d' → ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var)
    (P : List AKey) (S : Shape s) (C : CaptureSet s),
    Agree (up Γ z d P S) (up Γ z d' P S) ∧ Agree (down Γ z d P S) (down Γ z d' P S) ∧
      Agree (capUp Γ z d P C) (capUp Γ z d' P C) ∧ Agree (capDown Γ z d P C) (capDown Γ z d' P C)
  | 0, d', _, s, Γ, z, P, S, C => by
    have hf := avoid_framed d' Γ z P S C
    refine ⟨out_agree _ hf.1, out_agree _ hf.2.1, ?_, ?_⟩
    · cases hm : mentionsC z C
      · rw [capUp_eq_free hm, capUp_eq_free hm]
        exact ret_agree _
      · have h0 : capUp Γ z 0 P C = fun t => (⟨C, .refl⟩, { t with out := true }) := by
          simp [capUp, hm]
        rw [h0]
        exact out_agree _ hf.2.2.1
    · cases hm : mentionsC z C
      · rw [capDown_eq_free hm, capDown_eq_free hm]
        exact ret_agree _
      · have h0 : capDown Γ z 0 P C =
            fun t => (⟨[], .elem (CaptureSet.nil_subset C)⟩, { t with out := true }) := by
          simp [capDown, hm]
        rw [h0]
        exact out_agree _ hf.2.2.2
  | d + 1, d', hd, s, Γ, z, P, S, C => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List AKey) (S : Shape s)
        (C : CaptureSet s),
        Agree (up Γ z d P S) (up Γ z e P S) ∧ Agree (down Γ z d P S) (down Γ z e P S) ∧
          Agree (capUp Γ z d P C) (capUp Γ z e P C) ∧
          Agree (capDown Γ z d P C) (capDown Γ z e P C) :=
      fun Γ z P S C => avoid_agree d e (by omega) Γ z P S C
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (declsAt_framed Γ q A)) fun ms => ?_
            refine bind_agree (flatMapL_agree (fun m => ?_) ms) fun _ => ret_agree _
            exact bind_agree (ih Γ z _ _ C).1 fun _ => ret_agree _
        | fld a T =>
          cases T with
          | capt C' S' =>
            exact bind_agree (ih Γ z P S' C).1 fun _ =>
              bind_agree (ih Γ z P S' C').2.2.1 fun _ => ret_agree _
        | typ A L H =>
          exact bind_agree (ih Γ z P L C).2.1 fun _ =>
            bind_agree (ih Γ z P H C).1 fun _ => ret_agree _
        | cap A c1 c2 =>
          exact bind_agree (ih Γ z P .top c1).2.2.2 fun _ =>
            bind_agree (ih Γ z P .top c2).2.2.1 fun _ => ret_agree _
        | and S1 S2 =>
          exact bind_agree (ih Γ z P S1 C).1 fun _ =>
            bind_agree (ih Γ z P S2 C).1 fun _ => ret_agree _
        | box T =>
          cases T with
          | capt C' S' =>
            exact bind_agree (ih Γ z P S' C).1 fun _ =>
              bind_agree (ih Γ z P S' C').2.2.1 fun _ => ret_agree _
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              exact bind_agree (ih Γ z P S1 C1).2.1 fun l =>
                bind_agree (ih Γ z P S1 C1).2.2.2 fun lc =>
                  bind_agree (ih (Γ.cons (l.1 ^ lc.1)) (.there z) P S2 C2).1 fun _ =>
                    bind_agree (ih (Γ.cons (l.1 ^ lc.1)) (.there z) P S2 C2).2.2.1 fun _ =>
                      ret_agree _
        | mu _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _
    · apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases S with
        | sel p A =>
          cases p with
          | var q =>
            apply ite_agree (ret_agree _)
            refine bind_agree (Agree.refl (declsAt_framed Γ q A)) fun ms => ?_
            cases ms with
            | nil => exact ret_agree _
            | cons m _ => exact bind_agree (ih Γ z _ _ C).2.1 fun _ => ret_agree _
        | fld a T =>
          cases T with
          | capt C' S' =>
            exact bind_agree (ih Γ z P S' C).2.1 fun _ =>
              bind_agree (ih Γ z P S' C').2.2.2 fun _ => ret_agree _
        | typ A L H =>
          exact bind_agree (ih Γ z P L C).1 fun _ =>
            bind_agree (ih Γ z P H C).2.1 fun _ => ret_agree _
        | cap A c1 c2 =>
          exact bind_agree (ih Γ z P .top c1).2.2.1 fun _ =>
            bind_agree (ih Γ z P .top c2).2.2.2 fun _ => ret_agree _
        | and S1 S2 =>
          exact bind_agree (ih Γ z P S1 C).2.1 fun _ =>
            bind_agree (ih Γ z P S2 C).2.1 fun _ => ret_agree _
        | box T =>
          cases T with
          | capt C' S' =>
            exact bind_agree (ih Γ z P S' C).2.1 fun _ =>
              bind_agree (ih Γ z P S' C').2.2.2 fun _ => ret_agree _
        | all T1 T2 =>
          cases T1 with
          | capt C1 S1 =>
            cases T2 with
            | capt C2 S2 =>
              exact bind_agree (ih Γ z P S1 C1).1 fun _ =>
                bind_agree (ih Γ z P S1 C1).2.2.1 fun _ =>
                  bind_agree (ih (Γ.cons (S1 ^ C1)) (.there z) P S2 C2).2.1 fun _ =>
                    bind_agree (ih (Γ.cons (S1 ^ C1)) (.there z) P S2 C2).2.2.2 fun _ =>
                      ret_agree _
        | mu _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · refine capMapUp_agree (fun a => ?_) C
        cases a with
        | var y =>
          exact ite_agree (bind_agree (ih Γ z P S _).2.2.1 fun _ => ret_agree _) (ret_agree _)
        | sel y A =>
          refine ite_agree (bind_agree (Agree.refl (capsAt_framed Γ y A)) fun ms => ?_)
            (ret_agree _)
          cases ms with
          | nil => exact ret_agree _
          | cons m _ => exact bind_agree (ih Γ z _ S _).2.2.1 fun _ => ret_agree _
        | cvar _ => exact ret_agree _
        | any => exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · refine capMapDown_agree (fun a => ?_) C
        cases a with
        | var y => exact ite_agree (ret_agree _) (ret_agree _)
        | sel y A =>
          refine ite_agree (ite_agree (ret_agree _)
            (bind_agree (Agree.refl (capsAt_framed Γ y A)) fun ms => ?_)) (ret_agree _)
          cases ms with
          | nil => exact ret_agree _
          | cons m _ => exact bind_agree (ih Γ z _ S _).2.2.2 fun _ => ret_agree _
        | cvar _ => exact ret_agree _
        | any => exact ret_agree _

/-- `tyUp` is framed at every index. -/
theorem tyUp_framed {s : Sig} (Γ : Ctx s) (z : BVar s .var) (d : Nat) (P : List AKey) :
    ∀ T : Ty s, Framed (tyUp Γ z d P T)
  | .capt C S => by
    unfold tyUp
    exact bind_framed (avoid_framed d Γ z P S C).1 fun _ =>
      bind_framed (avoid_framed d Γ z P S C).2.2.1 fun _ => ret_framed _

/-- `tyUp` at a larger index does what it does at a smaller one. -/
theorem tyUp_agree {s : Sig} (Γ : Ctx s) (z : BVar s .var) {d d' : Nat} (hd : d ≤ d')
    (P : List AKey) : ∀ T : Ty s, Agree (tyUp Γ z d P T) (tyUp Γ z d' P T)
  | .capt C S => by
    unfold tyUp
    exact bind_agree (avoid_agree d d' hd Γ z P S C).1 fun _ =>
      bind_agree (avoid_agree d d' hd Γ z P S C).2.2.1 fun _ => ret_agree _

/-- `tyUp` from the fuel left is framed. -/
theorem tyUpAt_framed {s : Sig} (Γ : Ctx s) (z : BVar s .var) (T : Ty s) :
    Framed (tyUpAt Γ z T) where
  absorbs t ht := (tyUp_framed Γ z t.left [] T).absorbs t ht
  spends t := (tyUp_framed Γ z t.left [] T).spends t
  shift := by
    intro t r t' h ho k
    have hag := tyUp_agree Γ z (Nat.le_add_right t.left k) [] T
    change tyUp Γ z (t.left + k) [] T (t.add k) = _
    rw [hag.sim t r t' h ho k]

/-- `capUp` from the fuel left is framed. -/
theorem capUpAt_framed {s : Sig} (Γ : Ctx s) (z : BVar s .var) (C : CaptureSet s) :
    Framed (capUpAt Γ z C) where
  absorbs t ht := (avoid_framed t.left Γ z [] .top C).2.2.1.absorbs t ht
  spends t := (avoid_framed t.left Γ z [] .top C).2.2.1.spends t
  shift := by
    intro t r t' h ho k
    have hag := (avoid_agree t.left (t.left + k) (Nat.le_add_right _ _) Γ z [] .top C).2.2.1
    change capUp Γ z (t.left + k) [] C (t.add k) = _
    rw [hag.sim t r t' h ho k]

theorem unlessOut_framed {α : Type} (o : Option α) : Framed (unlessOut o) where
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
  bind_framed (tyUpAt_framed _ _ _) fun _ => unlessOut_framed _

theorem avoidLet_frame {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} {t t' : Tank}
    {r : Option (LetTy Γ T0 V)} (h : avoidLet Γ T0 V t = (r, t')) (ho : t'.out = false) (k : Nat) :
    avoidLet Γ T0 V (t.add k) = (r, t'.add k) :=
  (avoidLet_framed Γ T0 V).shift t r t' h ho k

/-- Avoidance from a marked tank answers `none` and leaves the tank as it is. -/
theorem avoidLet_absorbs {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) {t : Tank}
    (h : t.out = true) : avoidLet Γ T0 V t = (none, t) := by
  have hu := (tyUpAt_framed (Γ.cons T0) .here V).absorbs t h
  simp only [avoidLet, Fu.bind]
  cases hup : tyUpAt (Γ.cons T0) .here V t with
  | mk a t1 =>
    rw [hup] at hu
    simp only at hu
    simp [hu, unlessOut, h]

/-- Avoidance of a use set is framed. -/
theorem avoidUses_framed {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : CaptureSet (s,x)) :
    Framed (avoidUses Γ T0 V) :=
  bind_framed (capUpAt_framed _ _ _) fun _ => unlessOut_framed _

theorem avoidUses_frame {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : CaptureSet (s,x)} {t t' : Tank}
    {r : Option (LetUses Γ T0 V)} (h : avoidUses Γ T0 V t = (r, t')) (ho : t'.out = false)
    (k : Nat) : avoidUses Γ T0 V (t.add k) = (r, t'.add k) :=
  (avoidUses_framed Γ T0 V).shift t r t' h ho k

/-- Avoidance of a use set from a marked tank answers `none` and leaves the
tank as it is. -/
theorem avoidUses_absorbs {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : CaptureSet (s,x)) {t : Tank}
    (h : t.out = true) : avoidUses Γ T0 V t = (none, t) := by
  have hu := (capUpAt_framed (Γ.cons T0) .here V).absorbs t h
  simp only [avoidUses, Fu.bind]
  cases hup : capUpAt (Γ.cons T0) .here V t with
  | mk a t1 =>
    rw [hup] at hu
    simp only at hu
    simp [hu, unlessOut, h]

/-! ## Checks

Each check runs in the kernel at the default fuel.  `avoidAt` and `usesAt`
start a full tank. -/

section AvoidChecks

open Captures.DotMNF.Examples

/-- Avoidance at a `let` from a full tank of `n` units, the type and the tank. -/
def avoidAt {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : Ty (s,x)) (n : Nat := defaultFuel) :
    Option (Ty s) × Tank :=
  let r := avoidLet Γ T0 V ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- Avoidance of a use set from a full tank of `n` units, the set and the
tank. -/
def usesAt {s : Sig} (Γ : Ctx s) (T0 : Ty s) (V : CaptureSet (s,x)) (n : Nat := defaultFuel) :
    Option (CaptureSet s) × Tank :=
  let r := avoidUses Γ T0 V ⟨n, false⟩
  (r.1.map (·.1), r.2)

-- E2: the outer `let` binds `x = ν(x. {A = ∀(y : x.A) x.A} ∧ {a = …})` and its body has the type
-- `x.A`.  The alias cycle is cut once at each polarity, so the avoided type is a function type
-- `∀(y : ∀(z : ⊤) ⊥) ⊤`.  Strengthening alone fails on `x.A`.  It uses 34 units.
example : avoidAt Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ []) =
    (some ((Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ []),
      ⟨defaultFuel - 34, false⟩) := by decide +kernel

-- S2: `let it = mk un in it.next`.  The body has the type `(∀(u : ⊤) ⊤ ^ {it.C}) ^ {it.C}`, and
-- `{it.C}` goes to the upper bound `{fs}` of the member `C` of `it`, at both positions and under
-- the binder `u`.  It uses 23 units.
example : avoidAt S2Ctx2 S2ITTy S2NTy =
    (some ((Shape.all unitTy (.top ^ [CapAtom.cvar (.there fs2)])) ^ [CapAtom.cvar fs2]),
      ⟨defaultFuel - 23, false⟩) := by decide +kernel

-- S2: the use set `{it, it.C}` of a body.  `{it}` goes to the declared set `{fs, un}` of `it`, and
-- `{it.C}` to the upper bound `{fs}` of its member.  It uses 10 units.
example : usesAt S2Ctx2 S2ITTy [CapAtom.var .here, CapAtom.sel .here lC] =
    (some [CapAtom.cvar fs2, CapAtom.var .here], ⟨defaultFuel - 10, false⟩) := by decide +kernel

/-- G's binder: `z : {A : ⊥..{a : ⊤}} ∧ {A : ⊥..{b : ⊤}}`, two members `A`. -/
def GTy : Ty ([] : Sig) :=
  (Shape.and (.typ lA .bot (.fld la (.top ^ []))) (.typ lA .bot (.fld lb (.top ^ [])))) ^ []

-- G: a body at `z.A`.  Avoidance meets the upper bounds of both members, `{a : ⊤} ∧ {b : ⊤}`, as
-- the compiler does.  It uses 10 units.
example : avoidAt Ctx.nil GTy ((Shape.sel (.var .here) lA) ^ []) =
    (some ((Shape.and (.fld la (.top ^ [])) (.fld lb (.top ^ []))) ^ []),
      ⟨defaultFuel - 10, false⟩) := by decide +kernel

-- E8: a body type that does not mention the binder is strengthened, at one unit.
example : avoidAt E8Ctx1 (E8Ref .here) ((Shape.sel (.var (.there .here)) lA) ^ []) =
    (some ((Shape.sel (.var .here) lA) ^ []), ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- A use set that does not mention the binder is strengthened at no cost.
example : usesAt E8Ctx1 (E8Ref .here) [CapAtom.var (.there .here)] =
    (some [CapAtom.var .here], ⟨defaultFuel, false⟩) := by decide +kernel

-- A capture member of the binder that the binder does not have has no bound to go to.  The answer
-- is `none` with the tank unmarked: a rejection, not the recursion limit.
-- It uses 7 units.
example : avoidAt Ctx.nil GTy (.top ^ [CapAtom.sel .here lC]) = (none, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

-- A short tank is marked, and avoidance answers `none`: E2 at 4 units, and any type at 0.
example : avoidAt Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ []) 4 =
    (none, ⟨0, true⟩) := by decide +kernel
example : avoidAt E8Ctx1 (E8Ref .here) ((Shape.sel (.var (.there .here)) lA) ^ []) 0 =
    (none, ⟨0, true⟩) := by decide +kernel
example : usesAt S2Ctx2 S2ITTy [CapAtom.var .here, CapAtom.sel .here lC] 1 =
    (none, ⟨0, true⟩) := by decide +kernel

/-- E2's inner `let`, at `x.A`, as the version's examples derive it. -/
def E2inner : HasTy [] E2Ctx1 (.let (.proj .here la) (.app .here .here))
    ((Shape.sel (.var .here) lA) ^ []) :=
  .let E2proj E2app (.capt .sel)

/-- E2's avoidance, run at the default fuel. -/
def E2avoid : Option (LetTy Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ [])) :=
  (avoidLet Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ [])
    ⟨defaultFuel, false⟩).1

theorem E2avoid_ty :
    E2avoid.map (·.1) = some ((Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ []) := by
  decide +kernel

/-- E2 at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`, not at `⊤`: the
object, then the inner `let` taken to the avoided type by the derivation that
avoidance returns. -/
def E2avoided : HasTy [] Ctx.nil (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here)))
    ((Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ []) :=
  match h : E2avoid with
  | some r =>
      have hr : r.1 = (Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ [] := by
        have := E2avoid_ty
        rw [h] at this
        exact Option.some.inj this
      hr ▸ HasTy.let (obj' E2DefsTy E2Distinct) (HasTy.sub E2inner r.2 Subcap.refl)
        (hr ▸ (.capt (.all (.capt (.all (.capt .top) (.capt .bot))) (.capt .top))))
  | none => absurd E2avoid_ty (by rw [h]; simp)

/-- The iterator's avoidance, run at the default fuel. -/
def S2iterAvoid : Option (LetTy S2Ctx2 S2ITTy S2NTy) :=
  (avoidLet S2Ctx2 S2ITTy S2NTy ⟨defaultFuel, false⟩).1

theorem S2iterAvoid_ty :
    S2iterAvoid.map (·.1) =
      some ((Shape.all unitTy (.top ^ [CapAtom.cvar (.there fs2)])) ^ [CapAtom.cvar fs2]) := by
  decide +kernel

/-- S2's `let it = mk un in it.next` at the type avoidance gives,
`(∀(u : ⊤) ⊤ ^ {fs}) ^ {fs}`: the call, then the projection taken to the
avoided type by the derivation that avoidance returns. -/
def S2iterAvoided : HasTy [CapAtom.cvar fs2] S2Ctx2
    (.let (.app (.there .here) .here) (.proj .here lnext))
    ((Shape.all unitTy (.top ^ [CapAtom.cvar (.there fs2)])) ^ [CapAtom.cvar fs2]) :=
  match h : S2iterAvoid with
  | some r =>
      have hr : r.1 = (Shape.all unitTy (.top ^ [CapAtom.cvar (.there fs2)])) ^ [CapAtom.cvar fs2] := by
        have := S2iterAvoid_ty
        rw [h] at this
        exact Option.some.inj this
      hr ▸ HasTy.let S2it (HasTy.sub S2n r.2 Subcap.refl)
        (hr ▸ (.capt (.all (.capt .top) (.capt .top))))
  | none => absurd S2iterAvoid_ty (by rw [h]; simp)

end AvoidChecks

end CapturesFrontend.Core
