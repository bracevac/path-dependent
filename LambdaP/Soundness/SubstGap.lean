import LambdaP.Soundness.Embedding

/-!
V13: **the V9 refutation is an artefact of deviation 11** (the counterpart
of `EmbedGap.lean` for the substitution side; both are sorry-free and
independent of anything they refute).

Re-states the V9 refutation witness (`Soundness/quarantine/SubstRWitness.lean`)
against the LIVE tree, and shows that its "underivable image judgment"
`bad : Δ ⊢ ⌊0⌋.B <: ⌊1⌋` becomes DERIVABLE as soon as the `p.root.IsBound`
premise is dropped from `sel_hi` (deviation-11 reversal, V11-a).

The liberalized rules are taken as hypotheses (`LibSelHi`, `LibSelLo`), so
this file compiles against the UNMODIFIED `Typing.lean`.
-/

namespace LambdaP
namespace SubstGap

/-! ### V9's store, context and junk declaration (verbatim). -/

def Ent : Ty 0 := .arrow .top .top
def Thw : Sto := [Ent, Ent]

def A : Name := 0
def B : Name := 1

theorem lk0 : Sto.Lookup Thw 0 Ent := rfl
theorem lk1 : Sto.Lookup Thw 1 Ent := rfl

/-- `{ B : ⊥ .. ⌊1⌋ }`, at scope 1. -/
def Dcl1 : Ty 1 := .pairTy .top B .bot (.single (.var (.free 1)))

/-- `{ A : ⌊0⌋ .. { B : ⊥ .. ⌊1⌋ } }`, closed — V9's junk declaration. -/
def D0 : Ty 0 := .pairTy .top A (.single (.var (.free 0))) Dcl1

/-- V9's image context `Δ = ⟨x : D0⟩`. -/
def Dw : Ctx 1 := Ctx.empty.push D0

def xp : Path 1 := .var (.bound .here)
def p0 : Path 1 := .var (.free 0)

/-! ### The liberalized evidence rules, as hypotheses. -/

/-- `sel_hi` with `p.root.IsBound` deleted (V11-a). -/
def LibSelHi : Prop :=
  ∀ {s : Sig} {Θ : Sto} {Γ : Ctx s} {p : Path s} {S : Ty s} {Ax : Name}
    {T1 T2 : Ty (s+1)},
    Path.Wf Θ Γ p ->
    Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S Ax T1 T2)) ->
    Sub Θ Γ (.ty (T1.open p.fst)) (.ty (T2.open p.fst)) ->
    Sub Θ Γ (.ty (.tsel p Ax)) (.ty (T2.open p.fst))

/-- `skip_ty` with `p.root.IsBound` deleted (V11-a). -/
def LibSkipTy : Prop :=
  ∀ {s : Sig} {Θ : Sto} {Γ : Ctx s} {p : Path s} {S : Ty s} {Bx : Name}
    {T1 T2 : Ty (s+1)} {a : Name},
    Path.Wf Θ Γ p ->
    Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S Bx T1 T2)) ->
    Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a)))

/-! ### The junk chain at `Δ` (uses only the UNMODIFIED rules: the
subject `x` is bound-rooted, so `sel_lo`/`sel_hi` fire, and the interval
guards are discharged by `pair_ty`-widening exactly as in V8 §3). -/

theorem wfx : Path.Wf Thw Dw xp := .var_bound .here
theorem xb : (Path.root xp).IsBound := trivial

theorem declx : Sub Thw Dw (.ty (.single xp)) (.ty D0.weaken) :=
  Sub.var_bound .here

/-- `⌊0⌋ <: x.A` — the lower half of `x`'s junk interval. -/
theorem lo : Sub Thw Dw (.ty (.single p0)) (.ty (.tsel xp A)) := by
  have h := Sub.sel_lo (Θ := Thw) (Γ := Dw) (p := xp) xb wfx
    (declx.trans (Sub.pair_ty .refl .refl .top)) .top
  exact h

/-- `x.A <: { B : ⊥ .. ⌊1⌋ }` — the upper half. -/
theorem hi : Sub Thw Dw (.ty (.tsel xp A)) (.ty Dcl1) := by
  have h := Sub.sel_hi (Θ := Thw) (Γ := Dw) (p := xp) xb wfx
    (declx.trans (Sub.pair_ty .refl .bot .refl)) .bot
  exact h

/-- The junk fact about the LOCATION: `⌊0⌋ <: { B : ⊥ .. ⌊1⌋ }`.
This is what V9's `Δ` manufactures, and it is derivable with the
unmodified rules. -/
theorem ev0 : Sub Thw Dw (.ty (.single p0)) (.ty Dcl1) := lo.trans hi

theorem wf0 : Path.Wf Thw Dw p0 := .var_free lk0

/-! ### The punchline: V9's `bad` under the deviation-11 reversal. -/

/-- **V9's "underivable" image judgment, DERIVED** — from the liberalized
`sel_hi` alone. `Θ[0] = ⊤→⊤` has no member `B`, so `sel_hi_loc` cannot
fire and V9's enumeration is correct *for the unmodified rules*; the
liberalized rule needs no store anchor, only `Path.Wf Θ Δ ⌊0⌋`. -/
theorem bad_derivable (hlib : LibSelHi) :
    Sub Thw Dw (.ty (.tsel p0 B)) (.ty (.single (.var (.free 1)))) :=
  hlib wf0 ev0 .bot

/-- V9's second instance (`skip_ty`, no `tsel` anywhere), likewise. -/
theorem bad_skip_derivable (hlib : LibSkipTy) :
    Sub Thw Dw (.ty (.single (p0.sel 7))) (.ty (.single ((Path.fst p0).sel 7))) :=
  hlib wf0 ev0

/-! ### V9's substitution IS the preservation instance.

`σ = (z ↦ x, y ↦ ⌊0⌋)` is definitionally `(Subst.openPath ⌊0⌋).lift`:
opening ONE outer binder with a bare location, under one pushed binder.
So the V9 witness is not an exotic multi-variable substitution — it is
exactly the shape `HasType.open` hits at an `arrow`/`abs` push inside a
β-redex body. -/

def sg : Subst 2 1 where
  var := fun x => match x with
    | .here => xp
    | .there .here => p0

theorem sg_is_lifted_open : sg = (Subst.openPath (.var (.free 0) : Path 0)).lift := by
  apply Subst.funext
  intro x
  match x with
  | .here => rfl
  | .there .here => rfl

end SubstGap
end LambdaP

section
open LambdaP.SubstGap
#print axioms bad_derivable
#print axioms bad_skip_derivable
#print axioms sg_is_lifted_open
end
