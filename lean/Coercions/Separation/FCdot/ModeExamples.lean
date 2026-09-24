import Coercions.Separation.FCdot.CheckerCompleteness
import Coercions.Separation.FCdot.Resolution
import Coercions.Separation.FCdot.ModeBounds

namespace Separation

/-!
# Examples M1 to M3: modes

The mode examples of plan-5h S0.12.  They sit in a module of their own
because `FCdot/Examples.lean` imports the translation, which does not build
until S2.  Facts about `Ctx.rootsM` go through the equation lemmas of
resolution and then `decide`.  Facts about the checker are decided in the
kernel.

* M1, a read-only root: `{ro κ}` is read-only over a one-slot `∗` prefix.
* M2, a mode under a root: over a location prefix the moded roots of
  `{ro ⊤ᶜ}` hold `ro ℓ`.
* M3, no widening of a mode, and the meet: `{κ} ⊑ {ro κ}` fails as a moded
  inclusion, and `{consume (ro κ)}` is read-only.

The next section decides the names of S0.3 in the kernel: what a root, a
capture name and an heir stand for, the kill a head causes, possible
ownership, and the premise of the level rule.

The last section is the name half of C11 (decision 37): a parameter is a
plain leaf for mode bounds and is followed to its declared set for kills,
and over a one-location store no evidence widens `{y}` to `{ro y}`.
-/

namespace FCdot

namespace ModeExamples

/-- A one-slot platform prefix. -/
abbrev Γstar : Ctx ([] ,c) := Ctx.nil.consC .star

/-- A one-slot location prefix. -/
abbrev Γloc : Ctx ([] ,c) := Ctx.nil.consC (.loc true [])

/-- The binder of either prefix. -/
abbrev κ : BVar ([] ,c) .cap := .here

/-! ## M1, a read-only root -/

theorem M1_kindRo : Γstar.KindRo [.mode .ro (.cvar κ)] :=
  Ctx.kindRo_of_allRo _ (by decide)

/-! ## M2, a mode under a root

The universal root opens into itself and the location, and the second
expansion keeps the mode on both. -/

theorem M2_rootsM : Γloc.rootsM 0 [.mode .ro ⊤ᶜ] = [.mode .ro ⊤ᶜ, .mode .ro (.cvar κ)] := by
  rw [Ctx.rootsM, Ctx.caps_cons, Ctx.caps_nil, Ctx.capsAtom_mode, Ctx.capsAtom_top]
  decide

theorem M2_ro_loc : Γloc.RootM (.mode .ro (.cvar κ)) [.mode .ro ⊤ᶜ] :=
  ⟨0, by rw [M2_rootsM]; decide⟩

/-- The roots forget the mode: the location is a plain root of `{ro ⊤ᶜ}`. -/
theorem M2_root_loc : Γloc.Root (.cvar κ) [.mode .ro ⊤ᶜ] := M2_ro_loc.root_base

/-! ## M3, no widening of a mode, and the meet -/

theorem M3_rootM : Γstar.RootM (.cvar κ) [.cvar κ] := by
  refine ⟨0, ?_⟩
  rw [Ctx.rootsM, Ctx.caps_cons, Ctx.caps_nil, Ctx.capsAtom_cvar]
  decide

/-- `{κ} ⊑ {ro κ}` does not hold with modes: the moded roots of `{ro κ}` are
all read-only, and `ε` is not below `ro`. -/
theorem M3_noWiden : ¬ CapLeM Γstar [.cvar κ] [.mode .ro (.cvar κ)] := by
  intro h
  obtain ⟨b, hb, -, hle⟩ := h _ M3_rootM
  have hro := Ctx.kindRo_of_allRo Γstar (C := [.mode .ro (.cvar κ)]) (by decide) b hb
  rw [hro] at hle
  exact absurd hle (by decide)

/-- The meet: `consume (ro κ)` is read-only.  This is the case the
overwriting wrapper of the design broke (`kind_canon_fails`,
`Scratch_SepModes.lean.txt:148-152`). -/
theorem M3_meet : Γstar.KindRo [.mode .consume (.mode .ro (.cvar κ))] :=
  Ctx.kindRo_of_allRo _ (by decide)

/-! ## The two capture rules in the checker -/

/-- `{ro κ} ⊑ {κ}` by `modeLe`. -/
example : checkCap Γstar (.modeLe (.cvar κ) .ro .eps)
    [.mode .ro (.cvar κ)] [.cvar κ] = true := by decide +kernel

/-- `{κ} ⊑ {consume κ}` by `modeLe`. -/
example : checkCap Γstar (.modeLe (.cvar κ) .eps .consume)
    [.cvar κ] [.mode .consume (.cvar κ)] = true := by decide +kernel

/-- `modeLe` never widens a mode. -/
example : checkCap Γstar (.modeLe (.cvar κ) .eps .ro)
    [.cvar κ] [.mode .ro (.cvar κ)] = false := by decide +kernel

/-- The read-only view of reflexivity. -/
example : checkCap Γstar (.roMap (.refl [.cvar κ]))
    [.mode .ro (.cvar κ)] [.mode .ro (.cvar κ)] = true := by decide +kernel

/-! ## Names, kills and the side conditions (plan-5h S0.3)

Kernel `decide` facts on `Ctx.names`, the kill a head causes, possible
ownership and the two capture rules of S0.3.  They are the name half of the
examples C2, C5 and C8 of S0.12, whose terms arrive with cells in S0.4 and
S0.5.  A term binder `r` declared at `{ℓ}` stands in for a cell. -/

/-- A location `ℓ`, then a term binder `r` declared at `{ℓ}`. -/
abbrev Γr : Ctx (([] ,c) ,x) :=
  (Ctx.nil.consC (.loc true [])).cons (.opaque (Ty.capt [CapAtom.cvar .here] Shape.bot))

abbrev ℓ : BVar (([] ,c) ,x) .cap := .there .here
abbrev r : BVar (([] ,c) ,x) .var := .here

/-- The names of `r` are its location. -/
example : Γr.names [CapAtom.var r] = [CapAtom.cvar ℓ] := by decide +kernel

/-- The universal root opens into every capture binder at its level. -/
example : Γr.names [CapAtom.top] = [CapAtom.top, CapAtom.cvar ℓ] := by decide +kernel

example : Γr.AccessOnly [CapAtom.var r] := by decide +kernel
example : ¬ Γr.AccessOnly [CapAtom.mode .consume (CapAtom.cvar ℓ)] := by decide +kernel
example : Γr.consumedNames [CapAtom.mode .consume (CapAtom.cvar ℓ)] = [ℓ] := by decide +kernel
example : Γr.ConsumeOk [CapAtom.mode .consume (CapAtom.cvar ℓ)] := by decide +kernel

/-- `consume` on a term binder raises nothing (plan-5h decision 39): `consume r`
names `ℓ` plain, is access-only and consumes nothing.  Consumption is named on
the location. -/
example : Γr.names [CapAtom.mode .consume (CapAtom.var r)] = [CapAtom.cvar ℓ] := by
  decide +kernel
example : Γr.AccessOnly [CapAtom.mode .consume (CapAtom.var r)] := by decide +kernel
example : Γr.consumedNames [CapAtom.mode .consume (CapAtom.var r)] = [] := by decide +kernel

/-- C2, the name half: after a head consumes `ℓ`, the universal root is
inaccessible, because its names contain `ℓ`, and so is `r`, whose names are
`{ℓ}`. -/
example : ¬ (Γr.killFor [CapAtom.mode .consume (CapAtom.cvar ℓ)]).Accessible [CapAtom.top] := by
  decide +kernel

example : ¬ (Γr.killFor [CapAtom.mode .consume (CapAtom.cvar ℓ)]).Accessible
    [CapAtom.var r] := by
  decide +kernel

/-- C5, the name half: an argument `r` is not separated from a callee that
consumes `ℓ`, since the names of `r` are `{ℓ}`. -/
example : ¬ Γr.ArgSep [CapAtom.var r] [CapAtom.var r, CapAtom.mode .consume (CapAtom.cvar ℓ)] := by
  decide +kernel

/-- The level rule accepts `ℓ ⊑ ⊤ᶜ` and a read-only use of `r` below the root. -/
example : checkCap Γr (.level (.cvar ℓ) .top) [.cvar ℓ] [.top] = true := by decide +kernel
example : checkCap Γr (.level (.mode .ro (.var r)) .top)
    [.mode .ro (.var r)] [.top] = true := by decide +kernel

/-- Consumption never goes below a root. -/
example : checkCap Γr (.level (.mode .consume (.cvar ℓ)) .top)
    [.mode .consume (.cvar ℓ)] [.top] = false := by decide +kernel

/-- C8, the name half: the capture name of an opaque binder stands for its
level root, so its names contain `ℓ`. -/
example : Γr.names [CapAtom.name r (.typ 0)] = [CapAtom.top, CapAtom.cvar ℓ] := by decide +kernel

/-- Two locations, then an heir of both. -/
abbrev Γh : Ctx ((([] ,c) ,c) ,c) :=
  ((Ctx.nil.consC (.loc true [])).consC (.loc true [])).consC
    (.own true [CapAtom.cvar .here, CapAtom.cvar (.there .here)])

abbrev h : BVar ((([] ,c) ,c) ,c) .cap := .here
abbrev ℓ₁ : BVar ((([] ,c) ,c) ,c) .cap := .there .here
abbrev ℓ₂ : BVar ((([] ,c) ,c) ,c) .cap := .there (.there .here)

/-- Names stop at an heir. -/
example : Γh.names [CapAtom.cvar h] = [CapAtom.cvar h] := by decide +kernel

example : Γh.mayOwnB h ℓ₁ = true := by decide +kernel
example : Γh.MayOwn h ℓ₂ := by decide +kernel
example : ¬ Γh.MayOwn ℓ₁ h := by decide +kernel
example : Γh.Masked ℓ₁ := by decide +kernel
example : Γh.Consumable h := by decide +kernel
/-- A masked name is still consumable: term typing reads no mask (plan-5h
decision 38), and the clause of `State.TypedAt` refuses its consumption. -/
example : Γh.Consumable ℓ₁ := by decide +kernel
example : Γh.DistinctOk ℓ₁ ℓ₂ := by decide +kernel
example : ¬ Γh.DistinctOk h ℓ₁ := by decide +kernel

/-- Consuming the heir kills what it owns. -/
example : (Γh.killFor [CapAtom.mode .consume (CapAtom.cvar h)]).lookupCap ℓ₁ = .loc false [] := by
  decide +kernel

/-- `W ⊑ {h}` for the heir, and for nothing else. -/
example : checkCap Γh (.ownLe (.cvar h) [.cvar ℓ₁, .cvar ℓ₂])
    [.cvar ℓ₁, .cvar ℓ₂] [.cvar h] = true := by decide +kernel
example : checkCap Γh (.ownLe (.cvar ℓ₁) [.cvar ℓ₂]) [.cvar ℓ₂] [.cvar ℓ₁] = false := by
  decide +kernel

/-- A location, then a transparent binder whose capture name `a` reaches `b`
through a read-only self reference, and `b` names the location. -/
abbrev Wc : CapWitnesses (([] ,c) ,x) :=
  .cons (.cons .nil (.typ 0) [.mode .ro (.name .here (.typ 1))]) (.typ 1) [.cvar (.there .here)]

abbrev Γw : Ctx (([] ,c) ,x) :=
  (Ctx.nil.consC (.loc true [])).cons (.transparent (Ty.capt [] Shape.bot) .nil Wc [])

/-- The mode of the self reference rides on the name it reaches. -/
example : Γw.names [CapAtom.name .here (.typ 0)] =
    [CapAtom.mode .ro (CapAtom.cvar (.there .here))] := by decide +kernel
example : Γw.names [CapAtom.name .here (.typ 1)] = [CapAtom.cvar (.there .here)] := by
  decide +kernel

/-- So consuming `a` consumes nothing: the meet keeps the location read only. -/
example : Γw.AccessOnly [CapAtom.mode .consume (CapAtom.name .here (.typ 0))] := by
  decide +kernel

/-! ## C11, a parameter is a leaf for mode bounds and not for kills

A location `y`, then a scope, then its parameter (`Binding.formal`) or a let
binder in the same place.  The parameter stands for itself in the mode
reading, whatever its declared set, because the machine instantiates it only
by an argument that `app` made access-only.  Kills read the full names, which
follow the parameter to its declared set. -/

/-- A location, then a scope: its root, then the arrow binder. -/
abbrev Γy : Ctx ((([] ,c) ,c) ,c) := (Ctx.nil.consC (.loc true [])).scope

/-- The location, seen from the scope. -/
abbrev yy : BVar ((([] ,c) ,c) ,c) .cap := .there (.there .here)

/-- The location and the scope root, seen past one term binder. -/
abbrev yx : BVar (((([] ,c) ,c) ,c) ,x) .cap := .there yy
abbrev ρx : BVar (((([] ,c) ,c) ,c) ,x) .cap := .there (.there .here)

/-- g3's example as a parameter declared read-only at `y`. -/
abbrev Γp : Ctx (((([] ,c) ,c) ,c) ,x) :=
  Γy.cons (.formal (Ty.capt [CapAtom.mode .ro (CapAtom.cvar yy)] Shape.top))

/-- The same declared set at a let binder. -/
abbrev Γpl : Ctx (((([] ,c) ,c) ,c) ,x) :=
  Γy.cons (.opaque (Ty.capt [CapAtom.mode .ro (CapAtom.cvar yy)] Shape.top))

/-- The parameter is a plain leaf, and `consume x` on it raises nothing
(plan-5h decision 39), so `consume x` and `ro x` are access-only. -/
example : Γp.AccessOnly [CapAtom.mode .consume (CapAtom.var .here)] := by decide +kernel
example : Γp.AccessOnly [CapAtom.mode .ro (CapAtom.var .here)] := by decide +kernel
example : Γp.modeCaps (CapAtom.var .here) = [CapAtom.var .here] := by decide +kernel

/-- So the level rule accepts `consume x` below the scope root at the
parameter, since it consumes nothing, and at the let binder, whose names are
`{ro y}`. -/
example : checkCap Γp (.level (.mode .consume (.var .here)) (.cvar ρx))
    [.mode .consume (.var .here)] [.cvar ρx] = true := by decide +kernel
example : Γpl.AccessOnly [CapAtom.mode .consume (CapAtom.var .here)] := by decide +kernel
example : checkCap Γpl (.level (.mode .consume (.var .here)) (.cvar ρx))
    [.mode .consume (.var .here)] [.cvar ρx] = true := by decide +kernel

/-- A parameter declared at a consuming set. -/
abbrev Γq : Ctx (((([] ,c) ,c) ,c) ,x) :=
  Γy.cons (.formal (Ty.capt [CapAtom.mode .consume (CapAtom.cvar yy)] Shape.top))

/-- The same declared set at a let binder. -/
abbrev Γql : Ctx (((([] ,c) ,c) ,c) ,x) :=
  Γy.cons (.opaque (Ty.capt [CapAtom.mode .consume (CapAtom.cvar yy)] Shape.top))

/-- The parameter goes below the root plain: its argument consumes nothing.
The let binder does not, since its declared set consumes. -/
example : Γq.AccessOnly [CapAtom.var .here] := by decide +kernel
example : checkCap Γq (.level (.var .here) (.cvar ρx)) [.var .here] [.cvar ρx] = true := by
  decide +kernel
example : ¬ Γql.AccessOnly [CapAtom.var .here] := by decide +kernel

/-- Kills still read the full names: a use of the parameter consumes `y`. -/
example : Γq.consumedNames [CapAtom.var .here] = [yx] := by decide +kernel

/-- A parameter declared at the location names it in the full reading, and
after a consume of the location it is inaccessible.  In the mode reading it
names no capture binder, which is why only mode bounds read that reading. -/
abbrev Γk : Ctx (((([] ,c) ,c) ,c) ,x) :=
  Γy.cons (.formal (Ty.capt [CapAtom.cvar yy] Shape.top))

example : Γk.names [CapAtom.var .here] = [CapAtom.cvar yx] := by decide +kernel
example : ¬ (Γk.killFor [CapAtom.mode .consume (CapAtom.cvar yx)]).Accessible
    [CapAtom.var .here] := by decide +kernel
example : Γk.modeCaps (CapAtom.var .here) = [CapAtom.var .here] := by decide +kernel

/-- Over a store with a single location, closed capture evidence keeps every
mode bound: a signature with no term binder has no atom, so neither `member`
nor `capvar` nor `defC` can fire. -/
theorem Γloc_modeLe {f : CapCo ([] ,c)} {C D : CaptureSet ([] ,c)} (h : Γloc ⊢ᶜ f : C ⊑ D) :
    Γloc.ModeLe C D :=
  CapCo.HasType.namesModeLe (fun x => (BVar.no_var_cap x).elim)
    (fun a _ _ _ _ _ _ _ _ _ _ => (BVar.no_var_cap a.root).elim)
    (fun a _ _ _ _ _ _ _ _ _ _ => (BVar.no_var_cap a.root).elim)
    h

/-- **`{y} ⊑ {ro y}` is no closed evidence over the one-location store**
(`Γs_no_ro_widen` of the level round). -/
theorem Γs_no_ro_widen (f : CapCo ([] ,c)) :
    ¬ Γloc ⊢ᶜ f : [CapAtom.cvar .here] ⊑ [CapAtom.mode .ro (CapAtom.cvar .here)] := by
  intro h
  have hD : Γloc.SetBound [CapAtom.mode .ro (CapAtom.cvar .here)] .ro := by decide +kernel
  have hC : ¬ Γloc.SetBound [CapAtom.cvar .here] .ro := by decide +kernel
  exact hC (Γloc_modeLe h .ro hD)

end ModeExamples

end FCdot

end Separation
