import Coercions.PDot.FCp.Canon
import Coercions.PDot.FCp.Store
import Coercions.PDot.FCp.Checker
import Coercions.PDot.FCp.Resolution

/-!
# The recorded stores of gate C0 and E12, and their facts (plan X, T.6 amended)

Each configuration that gate C0 records is an FCp store in `namespace PDot.FCp.C0Ex`, with its
context and its store typing.  A typing is `synthValue_sound` over `decide +kernel`, or a store rule
over it.  A walk or resolution fact is checked by `decide +kernel`.  A runtime fact follows from
`canon_lookup` or `canon_cyclic`, and a lookup step is computed by `Runtime.lookPath`.

- R2 holds N1 and N3: the literal `ν(x. {C = ⊤} ∧ {A = Π(x∙C)⊤} ∧ {b = x})` and the lambda `y`
  stored after it.  `R2.n1_canon`: `x.b` names `x`.  `R2.n1_norm`: the two sides of the member at
  the alias have one normal type.
- S1 is an alias given its own block.  `S1.canon_xb`: the walk names `x.b` by `x`.
  `S1.defAt_xb`: `defAt` reads nothing at the alias.  `S1.res_xbA` and `S1.norm_xbA`: `x.b∙A`
  resolves through the walk to `x`'s definition `⊥`.
- N2 holds twin literals with one block value (`N2.twin_blocks`).  `N2.canon_apart`: the twins keep
  two names.  `N2.norm_apart`: the old equation `x∙A ≡ Π(x∙C)⊤` has two normal types.
- N4 holds a path of function type.  `N4.canon_xfa` and `N4.xfa_stuck`: `x.f` is a closure, so
  `x.f.a` names itself, and the runtime takes no step there.
- F1 holds a field two literals deep, at the path `x.a.b`.  `F1.node_xab`, `F1.canon_xab` and
  `F1.defAt_xab`: the inner literal is the node at its path, names itself, and holds its definition.
- Cyclic is the cyclic object E13.  `Cyclic.canon_xa`: `x.a` is named `none`.  `Cyclic.cyclic_xa`:
  `x.a` is cyclic on the runtime.
- RiskB holds a path field whose body is typed through another path field of the same literal.
- Growing holds lookup chains that grow with the path.  `Growing.budget`: the budget is three.
  `Growing.canon_long`: at that budget the walk names `x.a.c⁵` by `x.b`.  `Growing.res_long`: the
  member `F` at the end of `x.a.c⁴` resolves to `⊤`.
- TwoCycle holds a two-field forwarding cycle.  `TwoCycle.canon_xa` and `TwoCycle.canon_xb`: both
  fields are named `none`.  `TwoCycle.cyclic_xa` and `TwoCycle.cyclic_xb`: both are cyclic on the
  runtime.
- OlderCycle holds a newer literal forwarding into an older cycle, X3's named risk.
  `OlderCycle.canon_old_before` and `OlderCycle.canon_old_after`: the older path is named `none`
  before the newer literal is stored and after.  `OlderCycle.canon_new`: the newer field is named
  `none`.  `OlderCycle.cyclic_old` and `OlderCycle.cyclic_new`: the older path and the newer field
  are cyclic on the runtime.
- E12 is no store of gate C0.  It is the worked lookup of the paper, with the source's labels, so
  its store erases to the source's `γ12.erase`.  `E12.canon_xac`: `x.a.c` names `y.b.c`.
  `E12.lookup_xac`: lookup reaches that name.  `E12.lookup_lam`: one more step reaches the
  closure.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

abbrev lA : Label := .typ 0
abbrev lC : Label := .typ 1
abbrev lB : Label := .typ 2
abbrev lE : Label := .typ 3
abbrev lb : Label := .trm 0
abbrev la : Label := .trm 1
abbrev lf : Label := .trm 2
abbrev lc : Label := .trm 3

/-! ## N1 and N3: the R2 store `ν(x. {C = ⊤} ∧ {A = Π(x∙C)⊤} ∧ {b = x})`, `b` at `x.type` -/

namespace R2

def tel : Telescope ([],x) :=
  .cons (.cons (.cons (.cons (.cons .nil (.le .top (.sel (.var .here) lC))) (.le (.sel (.var .here) lC) .top))
    (.le (.pi (.sel (.var .here) lC) .top) (.sel (.var .here) lA)))
    (.le (.sel (.var .here) lA) (.pi (.sel (.var .here) lC) .top)))
    (.fld lb (Ty.sngl (.var .here)))
def ds : Defs ([],x) := .fld (.typ (.typ .nil lC .top) lA (.pi (.sel (.var .here) lC) .top)) lb (.path (.var .here))
def lit : Value [] := .obj tel ds
/-- `y = λ(w : x∙C). (w : ⊤)`, stored after `x`. -/
def lam : Value ([],x) := .lam (.sel (.var .here) lC) (.cast (.path (.var .here)) (.top (.sel (.var (.there .here)) lC)))
def Γx : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def Γ : Ctx (([],x),x) := Γx.cons (.opaque (.pi (.sel (.var .here) lC) .top))
def σ : Store (([],x),x) := (Store.nil.cons lit).cons lam

theorem lit_typed : Value.HasType .nil lit (.mu tel) := synthValue_sound (by decide +kernel)
theorem lam_typed : Value.HasType Γx lam (.pi (.sel (.var .here) lC) .top) := synthValue_sound (by decide +kernel)
theorem σ_typed : Store.Typed σ Γ := .lam (.obj .nil lit_typed) lam_typed

abbrev x' : Path (([],x),x) := .var (.there .here)
abbrev y' : Path (([],x),x) := .var .here
end R2

/-! ## S1: an alias given its own block read `⊤` (`facts.md:1255-1263`) -/

namespace S1
def tel : Telescope ([],x) :=
  .cons (.cons (.cons .nil (.le .bot (.sel (.var .here) lA))) (.le (.sel (.var .here) lA) .bot)) (.fld lb (Ty.sngl (.var .here)))
def ds : Defs ([],x) := .fld (.typ .nil lA .bot) lb (.path (.var .here))
def lit : Value [] := .obj tel ds
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def σ : Store ([],x) := Store.nil.cons lit
theorem lit_typed : Value.HasType .nil lit (.mu tel) := synthValue_sound (by decide +kernel)
theorem σ_typed : Store.Typed σ Γ := .obj .nil lit_typed
abbrev xp : Path ([],x) := .var .here
/-- `x.b` is no location: it names `x`. -/
theorem canon_xb : Γ.canon (xp.sel lb) = some xp := by decide +kernel
end S1

/-! ## N2: twin literals with one block value (`facts.md:1324-1327`) -/

namespace N2
def telY : Telescope ([],x) :=
  .cons (.cons (.cons (.cons .nil (.le .top (.sel (.var .here) lC))) (.le (.sel (.var .here) lC) .top))
    (.le (.pi (.sel (.var .here) lC) .top) (.sel (.var .here) lA))) (.le (.sel (.var .here) lA) (.pi (.sel (.var .here) lC) .top))
def dsY : Defs ([],x) := .typ (.typ .nil lC .top) lA (.pi (.sel (.var .here) lC) .top)
def telX : Telescope (([],x),x) :=
  .cons (.cons (.cons (.cons .nil (.le .top (.sel (.var .here) lC))) (.le (.sel (.var .here) lC) .top))
    (.le (.pi (.sel (.var (.there .here)) lC) .top) (.sel (.var .here) lA)))
    (.le (.sel (.var .here) lA) (.pi (.sel (.var (.there .here)) lC) .top))
def dsX : Defs (([],x),x) := .typ (.typ .nil lC .top) lA (.pi (.sel (.var (.there .here)) lC) .top)
def Γy : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telY) dsY.block)
def Γ : Ctx (([],x),x) := Γy.cons (.transparent (.mu telX) dsX.block)
def σ : Store (([],x),x) := (Store.nil.cons (.obj telY dsY)).cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ :=
  .obj (.obj .nil (synthValue_sound (by decide +kernel))) (synthValue_sound (by decide +kernel))
abbrev xp : Path (([],x),x) := .var .here
abbrev yp : Path (([],x),x) := .var (.there .here)
end N2

/-! ## N4: a path of function type (`facts.md:1334-1335`) -/

namespace N4
def tel : Telescope ([],x) := .cons .nil (.fld lf (.pi .top .top))
def ds : Defs ([],x) := .fld .nil lf (.fn (.lam .top (.path (.var .here))))
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def σ : Store ([],x) := Store.nil.cons (.obj tel ds)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
end N4

/-! ## F1: a field two literals deep (`facts.md:1336-1339`) -/

namespace F1
def telB : Telescope (s,x) := .cons (.cons .nil (.le .top (.sel (.var .here) lE))) (.le (.sel (.var .here) lE) .top)
def telA : Telescope (s,x) :=
  .cons (.cons (.cons .nil (.le .top (.sel (.var .here) lB))) (.le (.sel (.var .here) lB) .top)) (.fld lb (.mu telB))
def telX : Telescope ([],x) := .cons .nil (.fld la (.mu telA))
def dsB : Defs s := .typ .nil lE .top
def dsA : Defs s := .fld (.typ .nil lB .top) lb (.nest telB dsB)
def dsX : Defs ([],x) := .fld .nil la (.nest telA dsA)
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telX) dsX.block)
def σ : Store ([],x) := Store.nil.cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
abbrev xab : Path ([],x) := ((Path.var .here).sel la).sel lb
end F1

/-! ## E13: the cyclic object `ν(x : {a : (x.a).type}) {a = x.a}` -/

namespace Cyclic
def tel : Telescope ([],x) := .cons .nil (.fld la (Ty.sngl (.sel (.var .here) la)))
def ds : Defs ([],x) := .fld .nil la (.path (.sel (.var .here) la 0))
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def σ : Store ([],x) := Store.nil.cons (.obj tel ds)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
/-- The one name of a cyclic path. -/
theorem canon_xa : Γ.canon ((Path.var .here).sel la) = none := by decide +kernel
end Cyclic

/-! ## Risk (b): a path field whose body is typed through another path field of the same literal -/

namespace RiskB
def tel : Telescope ([],x) :=
  .cons (.cons (.cons .nil (.fld lc .top)) (.fld lb (Ty.sngl (.sel (.var .here) lc))))
    (.fld la (Ty.sngl (.sel (.var .here) lb)))
def ds : Defs ([],x) :=
  .fld (.fld (.fld .nil lc (.nest .nil .nil)) lb (.path (.sel (.var .here) lc 0))) la (.path (.sel (.var .here) lb 1))
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def σ : Store ([],x) := Store.nil.cons (.obj tel ds)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
end RiskB

/-! ## Lookup chains that grow with the path (`refute-d3.md:193-200`)

`x ↦ ν(x : {a : (x.b).type} ∧ {b : μ(w : {c : (x.a).type} ∧ {F : ⊤..⊤})}) {a = x.b, b = ν(w) {c = x.a, F = ⊤}}`.
The lookup of `x.a.cⁿ` reaches its nested literal after `2n + 2` steps.  The walk spends its fuel on
nested forwardings only, so the budget is three at every `n`. -/

namespace Growing
abbrev lF : Label := .typ 4
def telB : Telescope (([],x),x) :=
  .cons (.cons (.cons .nil (.fld lc (Ty.sngl ((Path.var (.there .here)).sel la))))
    (.le .top (.sel (.var .here) lF))) (.le (.sel (.var .here) lF) .top)
def telX : Telescope ([],x) :=
  .cons (.cons .nil (.fld la (Ty.sngl ((Path.var .here).sel lb)))) (.fld lb (.mu telB))
def dsB : Defs ([],x) := .typ (.fld .nil lc (.path (.sel (.var .here) la 0))) lF .top
def dsX : Defs ([],x) := .fld (.fld .nil la (.path (.sel (.var .here) lb 1))) lb (.nest telB dsB)
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telX) dsX.block)
def σ : Store ([],x) := Store.nil.cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
abbrev xp : Path ([],x) := .var .here
theorem budget : Γ.aliasBudget = 3 := by decide +kernel
theorem canon_long : Γ.canon (((((((xp.sel la).sel lc).sel lc).sel lc).sel lc).sel lc)) = some (xp.sel lb) := by
  decide +kernel
end Growing

/-! ## The refuter's R5 stores (`scratch-refute/R5_Cycles.lean`)

A two-field forwarding cycle, and a newer literal forwarding into an older cycle (X3's named
risk). -/

namespace TwoCycle
def tel : Telescope ([],x) :=
  .cons (.cons .nil (.fld la (Ty.sngl ((Path.var .here).sel lb)))) (.fld lb (Ty.sngl ((Path.var .here).sel la)))
def ds : Defs ([],x) := .fld (.fld .nil la (.path (.sel (.var .here) lb 1))) lb (.path (.sel (.var .here) la 0))
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu tel) ds.block)
def σ : Store ([],x) := Store.nil.cons (.obj tel ds)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))
theorem canon_xa : Γ.canon ((Path.var .here).sel la) = none := by decide +kernel
theorem canon_xb : Γ.canon ((Path.var .here).sel lb) = none := by decide +kernel
end TwoCycle

namespace OlderCycle
def telY : Telescope ([],x) := .cons .nil (.fld la (Ty.sngl ((Path.var .here).sel la)))
def dsY : Defs ([],x) := .fld .nil la (.path (.sel (.var .here) la 0))
def yp : Path (([],x),x) := .var (.there .here)
def telX : Telescope (([],x),x) := .cons .nil (.fld lc (Ty.sngl ((Path.var (.there .here)).sel la)))
def dsX : Defs (([],x),x) := .fld .nil lc (.path (.sel (.var (.there .here)) la 0))
def Γy : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telY) dsY.block)
def Γ : Ctx (([],x),x) := Γy.cons (.transparent (.mu telX) dsX.block)
def σ : Store (([],x),x) := (Store.nil.cons (.obj telY dsY)).cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ :=
  .obj (.obj .nil (synthValue_sound (by decide +kernel))) (synthValue_sound (by decide +kernel))
theorem canon_old_before : Γy.canon ((Path.var .here).sel la) = none := by decide +kernel
theorem canon_old_after : Γ.canon (yp.sel la) = none := by decide +kernel
theorem canon_new : Γ.canon ((Path.var .here).sel lc) = none := by decide +kernel
end OlderCycle

end C0Ex

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

namespace R2
/-- The old `EqConcl` failed here.  The closed reading gives the two sides one normal type. -/
theorem n1_norm : Γ.norm (.sel (x'.sel lb) lA) = Γ.norm (.pi (.sel (x'.sel lb) lC) .top) := by decide +kernel
/-- `x.b` names `x`, and the alias reads `x`'s definitions. -/
theorem n1_canon : Γ.canon (x'.sel lb) = some x' := by decide +kernel
end R2

namespace S1
/-- `defAt` reads nothing at the alias, where the old table read `⊤`. -/
theorem defAt_xb : Γ.defAt (xp.sel lb) lA = none := by decide +kernel
/-- `x.b∙A` resolves through `canon` to `x`'s definition `⊥`. -/
theorem res_xbA : Γ.res (.sel (xp.sel lb) lA) = .bot := by decide +kernel
theorem norm_xbA : Γ.norm (.sel (xp.sel lb) lA) = Γ.norm (.sel xp lA) := by decide +kernel
end S1

namespace N2
/-- The two blocks, read at their own variables, are one value. -/
theorem twin_blocks : Γ.blockAt .here = Γ.blockAt (.there .here) := by decide +kernel
/-- `canon` follows forwarding only, so the twins keep two names. -/
theorem canon_apart : Γ.canon xp ≠ Γ.canon yp := by decide +kernel
/-- The old `x∙A ≡ Π(x∙C)⊤` through `y`'s type has two normal types. -/
theorem norm_apart : Γ.norm (.sel xp lA) ≠ Γ.norm (.pi (.sel xp lC) .top) := by decide +kernel
end N2

namespace F1
/-- The inner literal is addressed by its path: no self binder, so no renaming of one. -/
theorem node_xab : Γ.nodeAt xab = some (.node (.cons .nil lE .top) .nil) := by decide +kernel
theorem canon_xab : Γ.canon xab = some xab := by decide +kernel
theorem defAt_xab : Γ.defAt xab lE = some .top := by decide +kernel
end F1

namespace Growing
theorem res_long : Γ.res (.sel (((((xp.sel la).sel lc).sel lc).sel lc).sel lc) lF) = .top := by decide +kernel
end Growing

end C0Ex

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace C0Ex

/-! ## E12: the worked lookup of the paper (`calculus.tex:284-305`)

`y ↦ ν(y : {b : μ(w : {c : Π(z : ⊤) ⊤})}) {b = nest {c = λ(z : ⊤) z}}`, then
`x ↦ ν(x : {a : (y.b).type}) {a = y.b}`.  The walk of `x.a.c` forwards once and lands at `y.b.c`,
whose block is a closure, and the runtime takes one more step to the closure.  The labels are the
source's (`Source/Lookup.lean:149-151`), so the erased store is the source's `γ12.erase`. -/

namespace E12
abbrev ea : Label := .trm 0
abbrev eb : Label := .trm 1
abbrev ec : Label := .trm 2
def telC : Telescope (s,x) := .cons .nil (.fld ec (.pi .top .top))
def dsC : Defs s := .fld .nil ec (.fn (.lam .top (.path (.var .here))))
def telY : Telescope ([],x) := .cons .nil (.fld eb (.mu telC))
def dsY : Defs ([],x) := .fld .nil eb (.nest telC dsC)
def telX : Telescope (([],x),x) := .cons .nil (.fld ea (Ty.sngl ((Path.var (.there .here)).sel eb)))
def dsX : Defs (([],x),x) := .fld .nil ea (.path (.sel (.var (.there .here)) eb 0))
def Γy : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telY) dsY.block)
def Γ : Ctx (([],x),x) := Γy.cons (.transparent (.mu telX) dsX.block)
def σ : Store (([],x),x) := (Store.nil.cons (.obj telY dsY)).cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ :=
  .obj (.obj .nil (synthValue_sound (by decide +kernel))) (synthValue_sound (by decide +kernel))
abbrev xp : Path (([],x),x) := .var .here
abbrev yp : Path (([],x),x) := .var (.there .here)
/-- `x.a.c` names `y.b.c`. -/
theorem canon_xac : Γ.canon ((xp.sel ea).sel ec) = some ((yp.sel eb).sel ec) := by decide +kernel
/-- `canon_lookup` at `x.a.c`. -/
theorem lookup_xac : Runtime.Lookups σ.erase (.defp ((xp.sel ea).sel ec)) (.defp ((yp.sel eb).sel ec)) :=
  canon_lookup σ_typed canon_xac
/-- One more step reaches the closure, as in the source. -/
theorem lookup_lam :
    Runtime.Lookups σ.erase (.defp ((xp.sel ea).sel ec)) (.defv (.lam (.path (.var .here)))) :=
  lookup_xac.trans (.single (Runtime.LStep.of_lookPath (by decide +kernel)))
end E12

/-! ## A name that is no location (`c0-final.md` 1.5, item 5)

`x.f` is a closure, so the walk of `x.f.a` lands at `x.f.a` with no block, and the runtime takes no
step there.  `canon_lookup` holds at it by reflexivity only, which is why it does not say that the
name is a location. -/

theorem N4.canon_xfa : N4.Γ.canon (((Path.var .here).sel lf).sel la) = some (((Path.var .here).sel lf).sel la) := by
  decide +kernel
theorem N4.xfa_stuck : ¬ ∃ k, Runtime.LStep N4.σ.erase (.defp (((Path.var .here).sel lf).sel la)) k := by
  intro ⟨k, h⟩
  have e := lookPath_complete h
  have e' : Runtime.lookPath N4.σ.erase (((Path.var .here).sel lf).sel la) = none := by decide +kernel
  rw [e'] at e
  cases e

/-! ## The cyclic paths of the recorded stores are cyclic on the runtime -/

theorem Cyclic.cyclic_xa : Runtime.CyclicPath Cyclic.σ.erase ((Path.var .here).sel la) :=
  canon_cyclic Cyclic.σ_typed Cyclic.canon_xa
theorem TwoCycle.cyclic_xa : Runtime.CyclicPath TwoCycle.σ.erase ((Path.var .here).sel la) :=
  canon_cyclic TwoCycle.σ_typed TwoCycle.canon_xa
theorem TwoCycle.cyclic_xb : Runtime.CyclicPath TwoCycle.σ.erase ((Path.var .here).sel lb) :=
  canon_cyclic TwoCycle.σ_typed TwoCycle.canon_xb
theorem OlderCycle.cyclic_old : Runtime.CyclicPath OlderCycle.σ.erase (OlderCycle.yp.sel la) :=
  canon_cyclic OlderCycle.σ_typed OlderCycle.canon_old_after
theorem OlderCycle.cyclic_new : Runtime.CyclicPath OlderCycle.σ.erase ((Path.var .here).sel lc) :=
  canon_cyclic OlderCycle.σ_typed OlderCycle.canon_new

end C0Ex

end PDot.FCp
