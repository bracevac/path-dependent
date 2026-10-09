import Coercions.CapturesCC.Frontend.Sub

/-!
# Avoidance at a `let` and at an unpacking

The type of `let z = t in u` may not mention `z`.  When the type of the body
does, the typer approximates it by a type free of `z`, as `TypeOps.avoid` does
in the compiler (`core/TypeOps.scala`, its `AvoidMap`).  The types here are a
shape with a capture set.  The answers are a type or a type under a capture
binder.

`up` approximates a shape from above and `down` from below.  `capUp` and
`capDown` do the same for capture sets, following `CaptureSet.mappedSet`
(`cc/CaptureSet.scala`).  Each returns the new shape or set with the `SubShape`
or `Subcap` derivation that relates it to the old one.

- A selection `z.A` at a covariant position becomes the meet of the avoided
  upper bounds of every member `A` that `z` has.  The compiler widens a
  selection at the merged bounds of its members (`AvoidMap.derivedSelect` and
  `AvoidMap.tryWiden`, with `TypeBounds.&` in `core/Types.scala`).  The meet is
  an intersection, derived by `SubShape.and` of the `SubShape.selUpper` steps.
  At a contravariant position `z.A` becomes the avoided lower bound of the
  first member.  The version has no union, so lower bounds are not joined.
- The atom `{z}` at a covariant position becomes the declared set of `z`, by
  `Subcap.var`.  `AvoidMap.apply` maps an avoided variable to
  `range(Nothing, info)`, and `mappedSet` takes the set of the info at a
  covariant position.  At a contravariant position `{z}` is dropped, as
  `mappedSet` gives the empty set there.
- The atom `{z.C}` becomes the avoided upper bound of the first capture member
  `C` of `z` at a covariant position and its lower bound at a contravariant
  one, by `Subcap.selUpper` and `Subcap.selLower`.  The covariant case is the
  bound of a `CapSet` member in `Capability.subsumes` (`cc/Capability.scala`).
  The version has no meet of capture sets, so one member is read.  The compiler
  gives the empty set at a contravariant position unless the image is exact.
  The lower bound is as sound and more precise.  A `{z.C}` with no member found
  stays at a covariant position, and then strengthening at the `let` fails.  At
  a contravariant position it is dropped.
- `∀` flips its domain, `{A : L..U}` flips `L`, and `{C^ : c₁..c₂}` flips `c₁`.
  The version's types have no invariant position, so the compiler's `Range`
  (`core/Types.scala`) never arises.  An arrow's domain is approximated in the
  scope in which `SubShape.all` compares domains, and its codomain in the body
  of the arrow at the domain `SubShape.all` asks for.  Both are read back past
  the scope's root.  An arrow whose parts do not read back becomes `⊤` or `⊥`.
- An existential answer that mentions `z` is not approximated, and the arrow
  that holds it becomes `⊤` or `⊥`.
- A selection or capture member already being expanded at the same polarity
  becomes `⊤`, `⊥`, the atom itself or the empty set, as
  `ApproximatingTypeMap.emptyRange` does.  A `μ` that mentions `z` has no
  subtyping rule in the version and becomes `⊤` or `⊥`.

All four draw on the tank of `Fuel.lean`.  A shape node costs `cost` of the
number of members being expanded.  A capture set that mentions `z` costs the
same, and one that does not is left as it is at no cost.  `declsAt` and
`capsAt` read the members of a selection on the same tank.  A short tank
answers `⊤`, `⊥`, the set as it is or the empty set, and is marked.  The
structural index starts at the fuel left.  Every step down the index follows a
draw of at least one unit, so the index never runs out before the tank does.

`avoidLet` runs `up` and `capUp` at the binder of a `let` and strengthens the
result.  It returns the type `U` with `Sub (Γ.cons T0) V U.weaken`, which
`HasTy.let` takes through `HasTy.sub`.  It answers `none` when the tank ends
marked (the recursion limit) and when the result still mentions the binder (a
rejection).  A type that does not mention the binder comes back as itself,
strengthened (`avoidLet_strengthen`).  `avoidUses` does the same for the use
set of the body, which `HasTy.let` also asks to be a weakening.

`avoidEx` moves the answer of an unpacking's body past the witness binder and
the payload binder that `HasTy.letex` opens.  An answer that strengthens past
both comes back as itself.  Otherwise a plain answer whose shape strengthens
has its set read at the innermost root of the context.  The payload, its
capture members and the witness are at that root's level, and `subcapF` gives
the derivation by the level rule.  The compiler's local root absorbs a `fresh`
in the same way (`Capability.subsumes`, through `acceptsLevelOf`).

Every computation here is framed: a run that ends unmarked does the same with
more fuel (`avoidLet_frame`, `avoidUses_frame`, `avoidEx_frame`).  Every
definition is structural, so the kernel evaluates avoidance.  The checks at the
end run it on the examples by `decide +kernel`.
-/

namespace CapturesCCFrontend.Core

open Frontend.Fuel
open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy)
open scoped CapturesCC.DotMNF

/-! ## Mentions -/

/-- The atom mentions the variable `z`, as itself or as the prefix of a
capture member. -/
def mentionsA {s : Sig} (z : BVar s .var) : CapAtom s → Bool
  | .var y => decide (y = z)
  | .sel y _ => decide (y = z)
  | .cvar _ => false
  | .any => false
  | .fresh => false

/-- The capture set mentions the variable `z`. -/
def mentionsC {s : Sig} (z : BVar s .var) (C : CaptureSet s) : Bool :=
  C.any (mentionsA z)

mutual

/-- The shape mentions the variable `z`, shifted under `μ` and under the
binders of an arrow. -/
def mentionsS {s : Sig} (z : BVar s .var) : Shape s → Bool
  | .sel (.var q) _ => decide (q = z)
  | .typ _ L H => mentionsS z L || mentionsS z H
  | .fld _ T => mentionsT z T
  | .cap _ c1 c2 => mentionsC z c1 || mentionsC z c2
  | .mu B => mentionsS (.there z) B
  | .all T U => mentionsT (.there z) T || mentionsE (.there (.there z)) U
  | .and S T => mentionsS z S || mentionsS z T
  | .box T => mentionsT z T
  | .top => false
  | .bot => false
termination_by structural S => S

/-- The type mentions the variable `z`. -/
def mentionsT {s : Sig} (z : BVar s .var) : Ty s → Bool
  | .capt C S => mentionsC z C || mentionsS z S
termination_by structural T => T

/-- The answer mentions the variable `z`, shifted under the capture binder of
an existential. -/
def mentionsE {s : Sig} (z : BVar s .var) : ETy s → Bool
  | .ty T => mentionsT z T
  | .ex C T => mentionsC z C || mentionsT (.there z) T
termination_by structural E => E

end

/-- Under a binder of any kind the lifted renaming never hits the shifted
`z`. -/
theorem lift_avoids {s1 s2 : Sig} {k0 : Kind} {ρ : Rename s1 s2} {z : BVar s2 .var}
    (h : ∀ y : BVar s1 .var, ρ.var y ≠ z) :
    ∀ y : BVar (s1,,k0) .var, (ρ.lift (k := k0)).var y ≠ .there z := by
  intro y
  cases y with
  | here => simp
  | there y =>
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
  | fresh => rfl

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
  | _, _, .all T U, ρ, z, h => by
    simp only [Shape.rename, mentionsS, mentionsT_rename T ρ.lift (.there z) (lift_avoids h),
      mentionsE_rename U ρ.lift.lift (.there (.there z)) (lift_avoids (lift_avoids h)),
      Bool.or_false]
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

/-- A renaming that never hits `z` gives an answer that does not mention `z`. -/
theorem mentionsE_rename : ∀ {s1 s2 : Sig} (E : ETy s1) (ρ : Rename s1 s2) (z : BVar s2 .var),
    (∀ y : BVar s1 .var, ρ.var y ≠ z) → mentionsE z (E.rename ρ) = false
  | _, _, .ty T, ρ, z, h => by
    simp only [ETy.rename, mentionsE, mentionsT_rename T ρ z h]
  | _, _, .ex C T, ρ, z, h => by
    simp only [ETy.rename, mentionsE, mentionsC_rename C ρ z h,
      mentionsT_rename T ρ.lift (.there z) (lift_avoids h), Bool.or_false]
termination_by structural _ _ E => E

end

/-- A weakened shape does not mention the new binder. -/
theorem mentionsS_weaken {s : Sig} (S : Shape s) : mentionsS .here (S.weaken (k := .var)) = false :=
  mentionsS_rename S Rename.succ .here fun y => by simp [Rename.succ]

/-- A weakened capture set does not mention the new binder. -/
theorem mentionsC_weaken {s : Sig} (C : CaptureSet s) :
    mentionsC .here (CaptureSet.weaken (k := .var) C) = false :=
  mentionsC_rename C Rename.succ .here fun y => by simp [Rename.succ]

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

/-- A type below `T`, with the derivation. -/
abbrev TyBelow {s : Sig} (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × Sub Γ U T

/-- An answer above `E`, with the derivation. -/
abbrev EAbove {s : Sig} (Γ : Ctx s) (E : ETy s) : Type := (F : ETy s) × ESub Γ E F

/-- An answer below `E`, with the derivation. -/
abbrev EBelow {s : Sig} (Γ : Ctx s) (E : ETy s) : Type := (F : ETy s) × ESub Γ F E

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

/-- A type above `T`: its shape by `fS`, then its set by `fC`, by `Sub.capt`. -/
def tyAboveBy {s : Sig} {Γ : Ctx s} (fS : (S : Shape s) → Fu (Above Γ S))
    (fC : (C : CaptureSet s) → Fu (CapAbove Γ C)) : (T : Ty s) → Fu (TyAbove Γ T)
  | .capt C S =>
      Fu.bind (fS S) fun r => Fu.bind (fC C) fun c => Fu.ret ⟨r.1 ^ c.1, .capt r.2 c.2⟩

/-- A type below `T`: its shape by `fS`, then its set by `fC`. -/
def tyBelowBy {s : Sig} {Γ : Ctx s} (fS : (S : Shape s) → Fu (Below Γ S))
    (fC : (C : CaptureSet s) → Fu (CapBelow Γ C)) : (T : Ty s) → Fu (TyBelow Γ T)
  | .capt C S =>
      Fu.bind (fS S) fun r => Fu.bind (fC C) fun c => Fu.ret ⟨r.1 ^ c.1, .capt r.2 c.2⟩

/-- An answer above `E`.  A plain answer goes by `tyAboveBy`.  An existential
that does not mention `z` stays, and one that does has no approximation. -/
def eAboveBy {s : Sig} {Γ : Ctx s} (z : BVar s .var) (fS : (S : Shape s) → Fu (Above Γ S))
    (fC : (C : CaptureSet s) → Fu (CapAbove Γ C)) : (E : ETy s) → Fu (Option (EAbove Γ E))
  | .ty T => Fu.bind (tyAboveBy fS fC T) fun r => Fu.ret (some ⟨.ty r.1, .ty r.2⟩)
  | .ex C T => Fu.ret (if mentionsE z (.ex C T) then none else some ⟨.ex C T, ESub.refl _⟩)

/-- An answer below `E`, likewise. -/
def eBelowBy {s : Sig} {Γ : Ctx s} (z : BVar s .var) (fS : (S : Shape s) → Fu (Below Γ S))
    (fC : (C : CaptureSet s) → Fu (CapBelow Γ C)) : (E : ETy s) → Fu (Option (EBelow Γ E))
  | .ty T => Fu.bind (tyBelowBy fS fC T) fun r => Fu.ret (some ⟨.ty r.1, .ty r.2⟩)
  | .ex C T => Fu.ret (if mentionsE z (.ex C T) then none else some ⟨.ex C T, ESub.refl _⟩)

/-- An arrow's domain read back past the root of its scope. -/
def domPast? {s : Sig} (T : Ty ((s,c),c)) : Option { D : Dom s // T = Dom.underRoot D } :=
  match witness? (tyRename? T PartialRename.unshift.lift) with
  | some ⟨D, h⟩ =>
      some ⟨D, tyRename?_sound T D _ _ (PartialRename.Inverts.lift PartialRename.unshift_inverts) h⟩
  | none => none

/-- An arrow's codomain read back past the root of its body. -/
def codPast? {s : Sig} (E : ETy (Sig.body s)) : Option { U : Cod s // E = Cod.underRoot U } :=
  match witness? (eTyRename? E PartialRename.unshift.lift.lift) with
  | some ⟨U, h⟩ =>
      some ⟨U, eTyRename?_sound E U _ _
        (PartialRename.Inverts.lift (PartialRename.Inverts.lift PartialRename.unshift_inverts)) h⟩
  | none => none

/-- An arrow above `∀(T1) U1`, from a domain `T1'` below `T1` and a codomain
above `U1` in the body at `T1'`.  A codomain that does not read back, or none,
gives `⊤`. -/
def allAbove {s : Sig} {Γ : Ctx s} {T1 T1' : Dom s} {U1 : Cod s}
    (e1 : Sub Γ.scope (Dom.underRoot T1') (Dom.underRoot T1)) :
    Option (EAbove (Γ.body T1') (Cod.underRoot U1)) → Above Γ (.all T1 U1)
  | some ⟨E, e⟩ =>
      match codPast? E with
      | some ⟨U1', hE⟩ => ⟨.all T1' U1', .all e1 (hE ▸ e)⟩
      | none => ⟨.top, .top⟩
  | none => ⟨.top, .top⟩

/-- The arrow case of `up`: the domain approximated from below gives `l`.  If
it reads back as `T1'`, the codomain is approximated from above by `k T1'` in
the body at `T1'`. -/
def allUp {s : Sig} {Γ : Ctx s} (T1 : Dom s) (U1 : Cod s) (l : TyBelow Γ.scope (Dom.underRoot T1))
    (k : (T1' : Dom s) → Fu (Option (EAbove (Γ.body T1') (Cod.underRoot U1)))) :
    Fu (Above Γ (.all T1 U1)) :=
  match domPast? l.1 with
  | some ⟨T1', h⟩ => Fu.bind (k T1') fun o => Fu.ret (allAbove (h ▸ l.2) o)
  | none => Fu.ret ⟨.top, .top⟩

/-- An arrow below `∀(T1) U1`, from a domain above `T1` and a codomain below
`U1` in the body at `T1`.  A part that does not read back, or none, gives
`⊥`. -/
def allBelow {s : Sig} {Γ : Ctx s} {T1 : Dom s} {U1 : Cod s}
    (l : TyAbove Γ.scope (Dom.underRoot T1)) :
    Option (EBelow (Γ.body T1) (Cod.underRoot U1)) → Below Γ (.all T1 U1)
  | some ⟨E, e⟩ =>
      match domPast? l.1, codPast? E with
      | some ⟨T1', h⟩, some ⟨U1', hE⟩ => ⟨.all T1' U1', .all (h ▸ l.2) (hE ▸ e)⟩
      | _, _ => ⟨.bot, .bot⟩
  | none => ⟨.bot, .bot⟩

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
          | .all T1 U1 =>
              Fu.bind (tyBelowBy (down Γ.scope (.there (.there z)) d P)
                  (capDown Γ.scope (.there (.there z)) d P) (Dom.underRoot T1)) fun l =>
                allUp T1 U1 l fun T1' =>
                  eAboveBy (.there (.there (.there z))) (up (Γ.body T1') (.there (.there (.there z))) d P)
                    (capUp (Γ.body T1') (.there (.there (.there z))) d P) (Cod.underRoot U1)
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
          | .all T1 U1 =>
              Fu.bind (tyAboveBy (up Γ.scope (.there (.there z)) d P)
                  (capUp Γ.scope (.there (.there z)) d P) (Dom.underRoot T1)) fun l =>
                Fu.bind (eBelowBy (.there (.there (.there z)))
                    (down (Γ.body T1) (.there (.there (.there z))) d P)
                    (capDown (Γ.body T1) (.there (.there (.there z))) d P) (Cod.underRoot U1)) fun o =>
                  Fu.ret (allBelow l o)
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
            | .any => Fu.ret ⟨[.any], .refl⟩
            | .fresh => Fu.ret ⟨[.fresh], .refl⟩) C
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
            | .any => Fu.ret ⟨[.any], .refl⟩
            | .fresh => Fu.ret ⟨[.fresh], .refl⟩) C
termination_by structural d _ _ => d

end

/-- A type approximated from above: its shape by `up`, then its set by
`capUp`, at one index. -/
def tyUp {s : Sig} (Γ : Ctx s) (z : BVar s .var) (d : Nat) (P : List AKey) (T : Ty s) :
    Fu (TyAbove Γ T) :=
  tyAboveBy (up Γ z d P) (capUp Γ z d P) T

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

/-- Strengthen an approximation that does not mention the binder.  If it
still mentions it, there is no answer. -/
def strengthenTy {s : Sig} {Γ : Ctx s} {T0 : Ty s} {V : Ty (s,x)} (r : TyAbove (Γ.cons T0) V) :
    Option (LetTy Γ T0 V) :=
  match tyStrengthenW? r.1 with
  | some w => some ⟨w.val, w.property ▸ r.2⟩
  | none => none

/-- Strengthen an approximated set that does not mention the binder.  If it
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
approximated from above until it does not mention the binder, then
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

/-! ## Avoidance at an unpacking

`HasTy.letex` opens a witness binder `c` and a payload binder `x : T`, and
its answer must be a weakening past both. -/

/-- The answer of an unpacking's body after the witness and the payload
leave, as `HasTy.letex` asks for it. -/
abbrev ExAns {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) : Type :=
  (E' : ETy s) × ESub ((Γ.consC).cons T) E (ETy.weaken (ETy.weaken (k := .cap) E'))

/-- The answer strengthened past the payload and the witness. -/
def exStrengthen {s : Sig} {Γ : Ctx s} {T : Ty (s,c)} (E : ETy ((s,c),x)) : Option (ExAns Γ T E) :=
  match eTyStrengthenW? (k := .var) E with
  | some ⟨F, hF⟩ =>
      match eTyStrengthenW? (k := .cap) F with
      | some ⟨E', hE'⟩ => some ⟨E', by rw [hF, hE']; exact ESub.refl _⟩
      | none => none
  | none => none

/-- A shape strengthened past the payload and the witness, with its equation. -/
def exShape? {s : Sig} (S : Shape ((s,c),x)) :
    Option { S' : Shape s // S = (S'.weaken (k := .cap)).weaken (k := .var) } :=
  match shapeStrengthenW? (k := .var) S with
  | some ⟨S1, h1⟩ =>
      match shapeStrengthenW? (k := .cap) S1 with
      | some ⟨S', h2⟩ => some ⟨S', by rw [h1, h2]⟩
      | none => none
  | none => none

/-- The payload, its capture members and the witness, replaced by the root
`ρ`. -/
def absorbRoot {s : Sig} (ρ : CapAtom ((s,c),x)) (a : CapAtom ((s,c),x)) : CapAtom ((s,c),x) :=
  match a with
  | .var .here => ρ
  | .sel .here _ => ρ
  | .cvar (.there .here) => ρ
  | a => a

/-- A capture set read at the innermost root of `Γ`, then strengthened past
the payload and the witness.  A context with no root absorbs nothing. -/
def exSet? {s : Sig} (Γ : Ctx s) (C : CaptureSet ((s,c),x)) : Option (CaptureSet s) :=
  match Γ.root? with
  | some ρ =>
      match capStrengthen? (k := .var) (C.map (absorbRoot (CapAtom.cvar (.there (.there ρ))))) with
      | some C2 => capStrengthen? (k := .cap) C2
      | none => none
  | none => none

/-- A plain answer whose shape strengthens, with its set read at the
innermost root.  `subcapF` gives the derivation, by the level rule. -/
def exLevel {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) : (E : ETy ((s,c),x)) → Fu (Option (ExAns Γ T E))
  | .ty (.capt C S) =>
      match exShape? S, exSet? Γ C with
      | some ⟨S', h⟩, some C' =>
          mapO (subcapF ((Γ.consC).cons T) C (CaptureSet.weaken (CaptureSet.weaken (k := .cap) C')))
            fun e => ⟨.ty (S' ^ C'), ESub.ty (Sub.capt (h ▸ SubShape.refl) e)⟩
      | _, _ => Fu.ret none
  | .ex _ _ => Fu.ret none

/-- Strengthening if it applies, and the level rule otherwise. -/
def exTry {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) : Fu (Option (ExAns Γ T E)) :=
  match exStrengthen (Γ := Γ) (T := T) E with
  | some r => Fu.ret (some r)
  | none => exLevel Γ T E

/-- The answer of an unpacking's body, moved past the witness and the
payload: by strengthening, or else by the level rule.  `none` if neither
applies, or if the tank ends marked. -/
def avoidEx {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) :
    Fu (Option (ExAns Γ T E)) :=
  Fu.bind (exTry Γ T E) unlessOut

/-! ## A type that strengthens comes back as itself -/

/-- `capUp` leaves a set that does not mention `z` as it is, at no cost. -/
theorem capUp_free {s : Sig} {Γ : Ctx s} {z : BVar s .var} {C : CaptureSet s}
    (h : mentionsC z C = false) (d : Nat) (P : List AKey) (t : Tank) :
    capUp Γ z d P C t = (⟨C, .refl⟩, t) := by
  cases d <;> simp [capUp, h, Fu.ret]

/-- A body type that does not mention the binder comes back as itself,
strengthened, from any unmarked tank with one unit. -/
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
    show tyAboveBy (up (Γ.cons T0) .here (n + 1) []) (capUp (Γ.cons T0) .here (n + 1) [])
      (Ty.capt (CaptureSet.weaken C) S.weaken) ⟨n + 1, false⟩ = _
    simp only [tyAboveBy, Fu.bind]
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

/-- An unpacking's answer that is a weakening past the payload and the witness
comes back as itself, at no cost. -/
theorem avoidEx_strengthen {s : Sig} {Γ : Ctx s} {T : Ty (s,c)} (E' : ETy s) {t : Tank}
    (ho : t.out = false) :
    (avoidEx Γ T (ETy.weaken (ETy.weaken (k := .cap) E')) t).1.map (·.1) = some E' ∧
      (avoidEx Γ T (ETy.weaken (ETy.weaken (k := .cap) E')) t).2 = t := by
  simp [avoidEx, exTry, exStrengthen, eTyStrengthenW?_weaken, Fu.bind, Fu.ret, unlessOut, ho]

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

theorem tyAboveBy_framed {fS : (S : Shape s) → Fu (Above Γ S)}
    {fC : (C : CaptureSet s) → Fu (CapAbove Γ C)} (hS : ∀ S, Framed (fS S))
    (hC : ∀ C, Framed (fC C)) : ∀ T, Framed (tyAboveBy fS fC T)
  | .capt C S => by
    simp only [tyAboveBy]
    exact bind_framed (hS S) fun _ => bind_framed (hC C) fun _ => ret_framed _

theorem tyAboveBy_agree {fS fS' : (S : Shape s) → Fu (Above Γ S)}
    {fC fC' : (C : CaptureSet s) → Fu (CapAbove Γ C)} (hS : ∀ S, Agree (fS S) (fS' S))
    (hC : ∀ C, Agree (fC C) (fC' C)) : ∀ T, Agree (tyAboveBy fS fC T) (tyAboveBy fS' fC' T)
  | .capt C S => by
    simp only [tyAboveBy]
    exact bind_agree (hS S) fun _ => bind_agree (hC C) fun _ => ret_agree _

theorem tyBelowBy_framed {fS : (S : Shape s) → Fu (Below Γ S)}
    {fC : (C : CaptureSet s) → Fu (CapBelow Γ C)} (hS : ∀ S, Framed (fS S))
    (hC : ∀ C, Framed (fC C)) : ∀ T, Framed (tyBelowBy fS fC T)
  | .capt C S => by
    simp only [tyBelowBy]
    exact bind_framed (hS S) fun _ => bind_framed (hC C) fun _ => ret_framed _

theorem tyBelowBy_agree {fS fS' : (S : Shape s) → Fu (Below Γ S)}
    {fC fC' : (C : CaptureSet s) → Fu (CapBelow Γ C)} (hS : ∀ S, Agree (fS S) (fS' S))
    (hC : ∀ C, Agree (fC C) (fC' C)) : ∀ T, Agree (tyBelowBy fS fC T) (tyBelowBy fS' fC' T)
  | .capt C S => by
    simp only [tyBelowBy]
    exact bind_agree (hS S) fun _ => bind_agree (hC C) fun _ => ret_agree _

theorem eAboveBy_framed {z : BVar s .var} {fS : (S : Shape s) → Fu (Above Γ S)}
    {fC : (C : CaptureSet s) → Fu (CapAbove Γ C)} (hS : ∀ S, Framed (fS S))
    (hC : ∀ C, Framed (fC C)) : ∀ E, Framed (eAboveBy z fS fC E)
  | .ty T => by
    simp only [eAboveBy]
    exact bind_framed (tyAboveBy_framed hS hC T) fun _ => ret_framed _
  | .ex _ _ => ret_framed _

theorem eAboveBy_agree {z : BVar s .var} {fS fS' : (S : Shape s) → Fu (Above Γ S)}
    {fC fC' : (C : CaptureSet s) → Fu (CapAbove Γ C)} (hS : ∀ S, Agree (fS S) (fS' S))
    (hC : ∀ C, Agree (fC C) (fC' C)) : ∀ E, Agree (eAboveBy z fS fC E) (eAboveBy z fS' fC' E)
  | .ty T => by
    simp only [eAboveBy]
    exact bind_agree (tyAboveBy_agree hS hC T) fun _ => ret_agree _
  | .ex _ _ => ret_agree _

theorem eBelowBy_framed {z : BVar s .var} {fS : (S : Shape s) → Fu (Below Γ S)}
    {fC : (C : CaptureSet s) → Fu (CapBelow Γ C)} (hS : ∀ S, Framed (fS S))
    (hC : ∀ C, Framed (fC C)) : ∀ E, Framed (eBelowBy z fS fC E)
  | .ty T => by
    simp only [eBelowBy]
    exact bind_framed (tyBelowBy_framed hS hC T) fun _ => ret_framed _
  | .ex _ _ => ret_framed _

theorem eBelowBy_agree {z : BVar s .var} {fS fS' : (S : Shape s) → Fu (Below Γ S)}
    {fC fC' : (C : CaptureSet s) → Fu (CapBelow Γ C)} (hS : ∀ S, Agree (fS S) (fS' S))
    (hC : ∀ C, Agree (fC C) (fC' C)) : ∀ E, Agree (eBelowBy z fS fC E) (eBelowBy z fS' fC' E)
  | .ty T => by
    simp only [eBelowBy]
    exact bind_agree (tyBelowBy_agree hS hC T) fun _ => ret_agree _
  | .ex _ _ => ret_agree _

theorem allUp_framed {T1 : Dom s} {U1 : Cod s} {l : TyBelow Γ.scope (Dom.underRoot T1)}
    {k : (T1' : Dom s) → Fu (Option (EAbove (Γ.body T1') (Cod.underRoot U1)))}
    (hk : ∀ T1', Framed (k T1')) : Framed (allUp T1 U1 l k) := by
  unfold allUp
  generalize domPast? l.1 = o
  cases o with
  | none => exact ret_framed _
  | some p => exact bind_framed (hk _) fun _ => ret_framed _

theorem allUp_agree {T1 : Dom s} {U1 : Cod s} {l : TyBelow Γ.scope (Dom.underRoot T1)}
    {k k' : (T1' : Dom s) → Fu (Option (EAbove (Γ.body T1') (Cod.underRoot U1)))}
    (hk : ∀ T1', Agree (k T1') (k' T1')) : Agree (allUp T1 U1 l k) (allUp T1 U1 l k') := by
  unfold allUp
  generalize domPast? l.1 = o
  cases o with
  | none => exact ret_agree _
  | some p => exact bind_agree (hk _) fun _ => ret_agree _

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
        | all T1 U1 =>
          exact bind_framed (tyBelowBy_framed (fun S => (ih Γ.scope _ P S []).2.1)
            (fun C' => (ih Γ.scope _ P .top C').2.2.2) _) fun _ =>
              allUp_framed fun T1' => eAboveBy_framed (fun S => (ih (Γ.body T1') _ P S []).1)
                (fun C' => (ih (Γ.body T1') _ P .top C').2.2.1) _
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
        | all T1 U1 =>
          exact bind_framed (tyAboveBy_framed (fun S => (ih Γ.scope _ P S []).1)
            (fun C' => (ih Γ.scope _ P .top C').2.2.1) _) fun _ =>
              bind_framed (eBelowBy_framed (fun S => (ih (Γ.body T1) _ P S []).2.1)
                (fun C' => (ih (Γ.body T1) _ P .top C').2.2.2) _) fun _ => ret_framed _
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
        | fresh => exact ret_framed _
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
        | fresh => exact ret_framed _

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
        | all T1 U1 =>
          exact bind_agree (tyBelowBy_agree (fun S => (ih Γ.scope _ P S []).2.1)
            (fun C' => (ih Γ.scope _ P .top C').2.2.2) _) fun _ =>
              allUp_agree fun T1' => eAboveBy_agree (fun S => (ih (Γ.body T1') _ P S []).1)
                (fun C' => (ih (Γ.body T1') _ P .top C').2.2.1) _
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
        | all T1 U1 =>
          exact bind_agree (tyAboveBy_agree (fun S => (ih Γ.scope _ P S []).1)
            (fun C' => (ih Γ.scope _ P .top C').2.2.1) _) fun _ =>
              bind_agree (eBelowBy_agree (fun S => (ih (Γ.body T1) _ P S []).2.1)
                (fun C' => (ih (Γ.body T1) _ P .top C').2.2.2) _) fun _ => ret_agree _
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
        | fresh => exact ret_agree _
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
        | fresh => exact ret_agree _

/-- `tyUp` is framed at every index. -/
theorem tyUp_framed {s : Sig} (Γ : Ctx s) (z : BVar s .var) (d : Nat) (P : List AKey) (T : Ty s) :
    Framed (tyUp Γ z d P T) :=
  tyAboveBy_framed (fun S => (avoid_framed d Γ z P S []).1)
    (fun C => (avoid_framed d Γ z P .top C).2.2.1) T

/-- `tyUp` at a larger index does what it does at a smaller one. -/
theorem tyUp_agree {s : Sig} (Γ : Ctx s) (z : BVar s .var) {d d' : Nat} (hd : d ≤ d')
    (P : List AKey) (T : Ty s) : Agree (tyUp Γ z d P T) (tyUp Γ z d' P T) :=
  tyAboveBy_agree (fun S => (avoid_agree d d' hd Γ z P S []).1)
    (fun C => (avoid_agree d d' hd Γ z P .top C).2.2.1) T

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

/-- A computation followed by `unlessOut` answers `none` from a marked tank and
leaves the tank as it is. -/
theorem bind_unlessOut_absorbs {α β : Type} {c : Fu α} (hc : Framed c) (f : α → Option β)
    {t : Tank} (h : t.out = true) : Fu.bind c (fun a => unlessOut (f a)) t = (none, t) := by
  have hu := hc.absorbs t h
  simp only [Fu.bind]
  cases hup : c t with
  | mk a t1 =>
    rw [hup] at hu
    simp only at hu
    simp [hu, unlessOut, h]

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
    (h : t.out = true) : avoidLet Γ T0 V t = (none, t) :=
  bind_unlessOut_absorbs (tyUpAt_framed (Γ.cons T0) .here V) strengthenTy h

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
    (h : t.out = true) : avoidUses Γ T0 V t = (none, t) :=
  bind_unlessOut_absorbs (capUpAt_framed (Γ.cons T0) .here V) strengthenSet h

/-- The level rule at an unpacking is framed. -/
theorem exLevel_framed {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) :
    ∀ E : ETy ((s,c),x), Framed (exLevel Γ T E)
  | .ty (.capt C S) => by
    simp only [exLevel]
    split
    · exact mapO_framed _ (subcapF_framed _ _ _)
    · exact ret_framed _
  | .ex _ _ => ret_framed _

/-- Avoidance at an unpacking is framed. -/
theorem avoidEx_framed {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) :
    Framed (avoidEx Γ T E) := by
  refine bind_framed ?_ fun _ => unlessOut_framed _
  unfold exTry
  split
  · exact ret_framed _
  · exact exLevel_framed Γ T E

theorem avoidEx_frame {s : Sig} {Γ : Ctx s} {T : Ty (s,c)} {E : ETy ((s,c),x)} {t t' : Tank}
    {r : Option (ExAns Γ T E)} (h : avoidEx Γ T E t = (r, t')) (ho : t'.out = false) (k : Nat) :
    avoidEx Γ T E (t.add k) = (r, t'.add k) :=
  (avoidEx_framed Γ T E).shift t r t' h ho k

/-- Avoidance at an unpacking from a marked tank answers `none` and leaves the
tank as it is. -/
theorem avoidEx_absorbs {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) {t : Tank}
    (h : t.out = true) : avoidEx Γ T E t = (none, t) := by
  have hc : Framed (exTry Γ T E) := by
    unfold exTry
    split
    · exact ret_framed _
    · exact exLevel_framed Γ T E
  exact bind_unlessOut_absorbs hc id h

/-! ## Checks

Each check runs in the kernel at the default fuel.  `avoidAt`, `usesAt` and
`exAt` start a full tank. -/

section AvoidChecks

open CapturesCC.DotMNF.Examples

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

/-- Avoidance at an unpacking from a full tank of `n` units, the answer and the
tank. -/
def exAt {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (E : ETy ((s,c),x)) (n : Nat := defaultFuel) :
    Option (ETy s) × Tank :=
  let r := avoidEx Γ T E ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- E2's avoided type `∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`. -/
def E2AvoidedTy : Ty ([] : Sig) :=
  (Shape.all ((Shape.all (.top ^ []) (.ty (.bot ^ []))) ^ []) (.ty (.top ^ []))) ^ []

-- E2: the outer `let` binds `x = ν(x. {A = ∀(y : x.A) x.A} ∧ {a = …})` and its body has the type
-- `x.A`.  The alias cycle is cut once at each polarity, and the domain and the codomain of the
-- arrow are approximated in their scope and body, so the avoided type is a function type.
-- Strengthening alone fails on `x.A`.
example : avoidAt Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ []) =
    (some E2AvoidedTy, ⟨defaultFuel - 34, false⟩) := by decide +kernel

/-- L3's binder `o : μ(z. {A : ⊥..{a : ⊤ ^ {z}}}) ^ {k1}` over the platform. -/
def L3Ty : Ty ([],c,c) :=
  (Shape.mu (.typ lA .bot (.fld la (.top ^ [CapAtom.var .here])))) ^ [CapAtom.cvar k1]

-- L3: a body at `o.A ^ {o}`.  The selection goes to its upper bound opened at `o`, and `{o}` to
-- the set `o` is declared at, inside the field too.  The answer is `{a : ⊤ ^ {k1}} ^ {k1}`.
example : avoidAt platCtx L3Ty ((Shape.sel (.var .here) lA) ^ [CapAtom.var .here]) =
    (some ((Shape.fld la (.top ^ [CapAtom.cvar k1])) ^ [CapAtom.cvar k1]),
      ⟨defaultFuel - 11, false⟩) := by decide +kernel

-- C2's `run`: `o : C2PreTy k1`, a literal with `C = {k1}`, and the body `o.run` at
-- `(⊤ → ⊤) ^ {o.C}`.  The capture member goes to its upper bound `{k1}`.
example : avoidAt platCtx (C2PreTy k1) (arrowS ^ [CapAtom.sel .here lC]) =
    (some (arrowS ^ [CapAtom.cvar k1]), ⟨defaultFuel - 11, false⟩) := by decide +kernel

-- The use set `{o, o.C}` of a body under the same binder: `{o}` goes to the declared set `{}` of
-- `o`, and `{o.C}` to `{k1}`.
example : usesAt platCtx (C2PreTy k1) [CapAtom.var .here, CapAtom.sel .here lC] =
    (some [CapAtom.cvar k1], ⟨defaultFuel - 10, false⟩) := by decide +kernel

-- L3's use set `{o}` goes to `{k1}`.
example : usesAt platCtx L3Ty [CapAtom.var .here] =
    (some [CapAtom.cvar k1], ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- G's binder: `z : {A : ⊥..{a : ⊤}} ∧ {A : ⊥..{b : ⊤}}`, two members `A`. -/
def GTy : Ty ([] : Sig) :=
  (Shape.and (.typ lA .bot (.fld la (.top ^ []))) (.typ lA .bot (.fld lb (.top ^ [])))) ^ []

-- G: a body at `z.A`.  Avoidance meets the upper bounds of both members, `{a : ⊤} ∧ {b : ⊤}`, as
-- the compiler does.
example : avoidAt Ctx.nil GTy ((Shape.sel (.var .here) lA) ^ []) =
    (some ((Shape.and (.fld la (.top ^ [])) (.fld lb (.top ^ []))) ^ []),
      ⟨defaultFuel - 10, false⟩) := by decide +kernel

-- E8: a body type that does not mention the binder is strengthened.
example : avoidAt E8Ctx1 (E8Ref .here) ((Shape.sel (.var (.there .here)) lA) ^ []) =
    (some ((Shape.sel (.var .here) lA) ^ []), ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- A use set that does not mention the binder is strengthened at no cost.
example : usesAt E8Ctx1 (E8Ref .here) [CapAtom.var (.there .here)] =
    (some [CapAtom.var .here], ⟨defaultFuel, false⟩) := by decide +kernel

-- A capture member of the binder that the binder does not have has no bound to go to.  The answer
-- is `none` with the tank unmarked: a rejection, not the recursion limit.
example : avoidAt Ctx.nil GTy (.top ^ [CapAtom.sel .here lC]) = (none, ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

-- A short tank is marked and avoidance answers `none`, for E2 and for any type.
example : avoidAt Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ []) 4 =
    (none, ⟨0, true⟩) := by decide +kernel
example : avoidAt E8Ctx1 (E8Ref .here) ((Shape.sel (.var (.there .here)) lA) ^ []) 0 =
    (none, ⟨0, true⟩) := by decide +kernel
example : usesAt platCtx (C2PreTy k1) [CapAtom.var .here, CapAtom.sel .here lC] 1 =
    (none, ⟨0, true⟩) := by decide +kernel

/-- A lambda body over the platform, at a pure parameter.  Its innermost root
is the body's own. -/
def ExBodyCtx : Ctx (Sig.body ([],c,c)) := Ctx.body platCtx unitTy

-- An unpacking inside the body that hands back its payload `x`, a capability at the witness `c`.
-- `{x}` does not strengthen, and the level rule puts it at the body's root.
example : exAt ExBodyCtx (arrowS ^ [CapAtom.cvar .here]) (.ty (arrowS ^ [CapAtom.var .here])) =
    (some (.ty (arrowS ^ [CapAtom.cvar (.there (.there .here))])), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

-- The same with the witness `c` itself in the answer.
example : exAt ExBodyCtx (arrowS ^ [CapAtom.cvar .here]) (.ty (arrowS ^ [CapAtom.cvar (.there .here)])) =
    (some (.ty (arrowS ^ [CapAtom.cvar (.there (.there .here))])), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

-- An answer free of both binders is strengthened at no cost.
example : exAt ExBodyCtx (arrowS ^ [CapAtom.cvar .here]) (.ty (.top ^ [])) =
    (some (.ty (.top ^ [])), ⟨defaultFuel, false⟩) := by decide +kernel

-- At the top of the platform there is no root to absorb the payload.  The answer is `none` with the
-- tank unmarked.
example : exAt platCtx (arrowS ^ [CapAtom.cvar .here]) (.ty (arrowS ^ [CapAtom.var .here])) =
    (none, ⟨defaultFuel, false⟩) := by decide +kernel

-- From an empty tank the level rule marks it.
example : exAt ExBodyCtx (arrowS ^ [CapAtom.cvar .here]) (.ty (arrowS ^ [CapAtom.var .here])) 0 =
    (none, ⟨0, true⟩) := by decide +kernel

/-- E2's inner `let`, at `x.A`, as the version's examples derive it. -/
def E2inner : HasTy [] E2Ctx1 (.let (.proj .here la) (.app .here .here))
    (.ty ((Shape.sel (.var .here) lA) ^ [])) :=
  .let E2proj E2app (.capt .sel)

/-- E2's avoidance, run at the default fuel. -/
def E2avoid : Option (LetTy Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ [])) :=
  (avoidLet Ctx.nil ((Shape.mu E2Self) ^ []) ((Shape.sel (.var .here) lA) ^ [])
    ⟨defaultFuel, false⟩).1

theorem E2avoid_ty : E2avoid.map (·.1) = some E2AvoidedTy := by
  decide +kernel

/-- E2 at the type avoidance gives, not at `⊤`: the object, then the inner
`let` taken to the avoided type by the derivation that avoidance returns. -/
def E2avoided : HasTy [] Ctx.nil (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here)))
    (.ty E2AvoidedTy) :=
  match h : E2avoid with
  | some r =>
      have hr : r.1 = E2AvoidedTy := by
        have := E2avoid_ty
        rw [h] at this
        exact Option.some.inj this
      hr ▸ HasTy.let (obj' E2DefsTy E2Distinct) (HasTy.sub E2inner (.ty r.2) Subcap.refl)
        (hr ▸ (.capt (.all (.capt (.all (.capt .top) (.ty (.capt .bot)))) (.ty (.capt .top)))))
  | none => absurd E2avoid_ty (by rw [h]; simp)

end AvoidChecks

end CapturesCCFrontend.Core
