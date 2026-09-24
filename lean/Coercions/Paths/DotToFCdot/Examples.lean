import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.DotMNF.Examples

/-!
# The translation on concrete derivations (P2.9, Z1 to Z9)

Each example is a source derivation and a fact about its translation.  The
kernel decides every fact: a checker verdict `checkTm`, `checkLe`, `checkPath`
or `checkAtom` on the image, an equation between computed images, or an
erasure equation.  Nothing here is proved by a lemma about the translation,
except the typings read off a verdict by `FCdot.checkTm_sound` and the two
facts of Z9, which are proof terms over the target's templates.  So a fact
holds only if the translation unfolds in the kernel, which is decision 31.

The rows are the namespaces `Z1` to `Z9`.  The text is the design round's
Parts D, R, E and K (`Scratch_P2_Final.lean.txt`), stated on the real names.

* `Z1`: decision 26 on one literal body, declared plain by `trm` and stable
  by `trmObj`.
* `Z2`: a field that holds a variable, and a field that holds the literal's
  own self.
* `Z3`: the counters of `litMorphism` on three fields in one intersection,
  and two stable fields around a field that holds a variable.
* `Z4`: `Fld-E`, `Sel-<:` and the singleton rules at a path.
* `Z5`: `Sub.mu` through its template morphism, and the positions `SubDecl`
  reads.
* `Z6`: `Sub.vfld`, `Sub.vfldToFld`, a projection by `proj` and by `projP`,
  the derived `letSngl`.
* `Z7`: decision 28 on its images, and X3 of P0.
* `Z8`: the kernel evaluates the translations of X1 and X4 of P0 and of
  `And₁`.
* `Z9`: why decisions 28 and 29.  No template reads an inclusion out of a
  singleton, and none rewrites an alias.

Each term derivation of Z1, Z2, Z3 and Z7 has its erasure equation
`⌊h.translate⌋ = Tm.erase t`, by `decide +kernel`.  `HasTy.translate_erase`
states the same equation for every derivation.
-/

namespace Paths
namespace DotMNF
namespace TargetExamples

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

/-! ## Labels, variable typings, and the literal the rows share -/

def lA : Label := .typ 0
def lB : Label := .typ 1
def la : Label := .trm 0
def lb : Label := .trm 1
def lc : Label := .trm 2
def ld : Label := .trm 3

/-- `Var` at a path, with the variable given explicitly. -/
def pvar' {s : Sig} {Γ : Ctx s} (x : BVar s .var) {T : Ty s} (h : Γ.lookup x = T) :
    PathTy Γ (.var x) T := by
  subst h; exact .var

/-- `Var` as a term rule, with the variable given explicitly. -/
def var' {s : Sig} {Γ : Ctx s} (x : BVar s .var) {T : Ty s} (h : Γ.lookup x = T) :
    HasTy Γ (.path x) T := by
  subst h; exact .var

/-- `{A = ⊤}`, the inner literal's definitions. -/
def dIn : Defs (([],x),x) := .typ lA .top
/-- `{A : ⊤..⊤}`, its declaration type. -/
def TIn : Ty (([],x),x) := .typ lA .top .top
/-- `{val a : μ(y. {A : ⊤..⊤})}`, a stable field at the inner literal's type. -/
def TOutS : Ty ([],x) := .vfld la (.mu TIn)

/-- `z : ⊤`. -/
def Γz : Ctx ([],x) := Ctx.nil.cons .top

/-- `w : μ(x. {val a : μ(y. {A : ⊤..⊤})})`. -/
def Γw : Ctx ([],x) := Ctx.nil.cons (.mu TOutS)

def hw : PathTy Γw (.var .here) (Ty.mu TOutS).weaken := .var

/-- `Rec-E` at the path `w`: `w : {val a : μ(y. {A : ⊤..⊤})}`. -/
def hwOpen : PathTy Γw (.var .here) (.vfld la (.mu TIn)) :=
  (show (TOutS.rename FCdot.Rename.succ.lift).substPath (.var .here) = .vfld la (.mu TIn)
    from rfl) ▸ hw.recE (by decide)

/-! ## Z1.  Decision 26: a literal body, plain by `trm`, stable by `trmObj`

`ν(x. {a = ν(y. {A = ⊤})})`, declared `{a : μ(y. {A : ⊤..⊤})}` by `trm` and
`{val a : μ(y. {A : ⊤..⊤})}` by `trmObj`.  The image of the plain field ends in
the eliminating identity at the equality counter, so the target sees no stable
body.  The image of the stable field ends in the definition equality, which is
table-only, so the target lists `a` as stable and gives the inner literal's
block at `x.a`.  The uniform clause, `def here a` at both, would make the plain
field stable in the target, and then the two builders of the block disagree. -/

namespace Z1

/-- `{a = ν(y. {A = ⊤})}`. -/
def dOut : Defs ([],x) := .trm la (.val (.obj dIn))

/-- The field declared plain, `{a : μ(y. {A : ⊤..⊤})}`. -/
def TOutP : Ty ([],x) := .fld la (.mu TIn)

def defsP : DefsTy (Ctx.nil.consSelf dOut TOutP) dOut TOutP := .trm (.obj .typ .typ)
def defsS : DefsTy (Ctx.nil.consSelf dOut TOutS) dOut TOutS := .trmObj .typ .typ

def litP : HasTy Ctx.nil (.val (.obj dOut)) (.mu TOutP) := .obj defsP .trm
def litS : HasTy Ctx.nil (.val (.obj dOut)) (.mu TOutS) := .obj defsS .trm

def FP : FCdot.Fields ([],x) := defsP.translateFields .here TOutP.literalTy.weaken 0
def FS : FCdot.Fields ([],x) := defsS.translateFields .here TOutS.literalTy.weaken 0

/-- The inner literal, translated: `ν(y. {A = ⊤}) ▷ litCo`. -/
def innerImage : FCdot.Tm ([],x) :=
  .cast (.val (.obj TIn.witnesses .nil)) (litCo TIn)

/-- The image of a `trm` field whose body is a literal ends in the eliminating
identity `eqToLe (symm (member (var here) (refl Tself) 0))`. -/
theorem FP_image :
    FP = .cons .nil la (.cast innerImage
      (.eqToLe (.symm (.member (.var .here) (.refl TOutP.literalTy.weaken) 0)))) := by
  decide +kernel

/-- The image of a `trmObj` field: the literal cast by `litCo`, then by the
definition equality `def here a`, which is table-only. -/
theorem FS_image :
    FS = .cons .nil la (.cast innerImage (.eqToLe (.symm (.def .here la)))) := by
  decide +kernel

/-- The plain body is not stable. -/
theorem FP_body_plain :
    (FCdot.Tm.cast innerImage
      (.eqToLe (.symm (.member (.var .here) (.refl TOutP.literalTy.weaken) 0)))).isStable
      = false := by
  decide +kernel

/-- The stable body is stable. -/
theorem FS_body_stable :
    (FCdot.Tm.cast innerImage (.eqToLe (.symm (.def .here la)))).isStable = true := by
  decide +kernel

/-- `litCo` is table-only, which is why the `trmObj` body is stable. -/
theorem litCo_TIn_tableOnly : (litCo TIn).tableOnly = true := by decide +kernel

/-- The plain field lists no stable label and gives no child. -/
theorem FP_valLabels : FP.valLabels = [] := by decide +kernel
theorem FP_children : FP.children (.var .here) = .nil := by decide +kernel

/-- The stable field lists `a` and gives the inner literal's block at `x.a`. -/
theorem FS_valLabels : FS.valLabels = [la] := by decide +kernel
theorem FS_children :
    FS.children (.var .here)
      = .cons .nil la ((FCdot.Value.obj TIn.witnesses .nil).blockSelf.substPath
          (.sel (.var .here) la)) := by
  decide +kernel

/-- `Ty.blocks` agrees with the stored value's block, at both declarations. -/
theorem blocks_P : TOutP.blocks dOut = (FCdot.Value.obj TOutP.witnesses FP).blockSelf := by
  decide +kernel
theorem blocks_S : TOutS.blocks dOut = (FCdot.Value.obj TOutS.witnesses FS).blockSelf := by
  decide +kernel

/-- Without decision 26, the uniform clause `def here a` at a `trm` literal
body makes the field stable in the target while the source says `fld`, and
the two builders disagree. -/
def FPuniform : FCdot.Fields ([],x) :=
  .cons .nil la (.cast innerImage (.eqToLe (.symm (.def .here la))))
theorem FPuniform_disagrees :
    (FCdot.Value.obj TOutP.witnesses FPuniform).blockSelf ≠ TOutP.blocks dOut := by
  decide +kernel

/-- Both literals type in the P1 checker at the translated declared type. -/
theorem litP_checks :
    FCdot.checkTm FCdot.Ctx.nil litP.translate (Ty.mu TOutP).translate = true := by
  decide +kernel
theorem litS_checks :
    FCdot.checkTm FCdot.Ctx.nil litS.translate (Ty.mu TOutS).translate = true := by
  decide +kernel

theorem litP_typed :
    FCdot.Tm.HasType FCdot.Ctx.nil litP.translate (Ty.mu TOutP).translate :=
  FCdot.checkTm_sound litP_checks
theorem litS_typed :
    FCdot.Tm.HasType FCdot.Ctx.nil litS.translate (Ty.mu TOutS).translate :=
  FCdot.checkTm_sound litS_checks

/-- Both images erase to the source literal. -/
theorem litP_erase : ⌊litP.translate⌋ = Tm.erase (.val (.obj dOut)) := by decide +kernel
theorem litS_erase : ⌊litS.translate⌋ = Tm.erase (.val (.obj dOut)) := by decide +kernel

end Z1

/-! ## Z2.  A field that holds a variable, or the literal's own self

A field that holds a variable gets a forwarding child whatever type it is
declared at.  So `Ty.blocks` reads the definitions, not the declaration
(decision 30).  `ν(x. {a = z})` is declared `{a : ⊤}` and `{a : z.type}`, the
second by the derived `trmSngl`.  `ν(x. {a = x})` is declared at `{a : ⊤}` and
at `{a : x.type}`. -/

namespace Z2

/-- `{a = z}`. -/
def dZ : Defs (([],x),x) := .trm la (.path (.there .here))
/-- Declared `{a : ⊤}`: the type names no path. -/
def TZ : Ty (([],x),x) := .fld la .top
/-- Declared `{a : z.type}`, by the derived `trmSngl`. -/
def TZs : Ty (([],x),x) := .fld la (.sngl (.var (.there .here)))

def defsZ : DefsTy (Γz.consSelf dZ TZ) dZ TZ := .trm (.sub .var .top)
def defsZs : DefsTy (Γz.consSelf dZ TZs) dZ TZs := DefsTy.trmSngl .var

def litZ : HasTy Γz (.val (.obj dZ)) (.mu TZ) := .obj defsZ .trm
def litZs : HasTy Γz (.val (.obj dZ)) (.mu TZs) := .obj defsZs .trm

def FZ : FCdot.Fields (([],x),x) := defsZ.translateFields .here TZ.literalTy.weaken 0

theorem FZ_children :
    FZ.children (.var .here) = .cons .nil la (.fwd (.var (.there .here))) := by
  decide +kernel
theorem FZ_valLabels : FZ.valLabels = [] := by decide +kernel
theorem blocks_Z : TZ.blocks dZ = (FCdot.Value.obj TZ.witnesses FZ).blockSelf := by
  decide +kernel
theorem litZ_checks : FCdot.checkTm Γz.translate litZ.translate (Ty.mu TZ).translate = true := by
  decide +kernel
theorem litZs_checks :
    FCdot.checkTm Γz.translate litZs.translate (Ty.mu TZs).translate = true := by
  decide +kernel

/-- `{a = x}`, a field that holds the literal's own self. -/
def dS : Defs ([],x) := .trm la (.path .here)
def TS1 : Ty ([],x) := .fld la .top
def TS2 : Ty ([],x) := .fld la (.sngl (.var .here))
def defsS1 : DefsTy (Ctx.nil.consSelf dS TS1) dS TS1 := .trm (.sub .var .top)
def defsS2 : DefsTy (Ctx.nil.consSelf dS TS2) dS TS2 := DefsTy.trmSngl .var
def litS1 : HasTy Ctx.nil (.val (.obj dS)) (.mu TS1) := .obj defsS1 .trm
def litS2 : HasTy Ctx.nil (.val (.obj dS)) (.mu TS2) := .obj defsS2 .trm

theorem R2_blocks1 :
    TS1.blocks dS = (FCdot.Value.obj TS1.witnesses
      (defsS1.translateFields .here TS1.literalTy.weaken 0)).blockSelf := by decide +kernel
theorem R2_blocks2 :
    TS2.blocks dS = (FCdot.Value.obj TS2.witnesses
      (defsS2.translateFields .here TS2.literalTy.weaken 0)).blockSelf := by decide +kernel
theorem R2_checks1 :
    FCdot.checkTm FCdot.Ctx.nil litS1.translate (Ty.mu TS1).translate = true := by decide +kernel
theorem R2_checks2 :
    FCdot.checkTm FCdot.Ctx.nil litS2.translate (Ty.mu TS2).translate = true := by decide +kernel

/-- The four images erase to the source literals. -/
theorem litZ_erase : ⌊litZ.translate⌋ = Tm.erase (.val (.obj dZ)) := by decide +kernel
theorem litZs_erase : ⌊litZs.translate⌋ = Tm.erase (.val (.obj dZ)) := by decide +kernel
theorem litS1_erase : ⌊litS1.translate⌋ = Tm.erase (.val (.obj dS)) := by decide +kernel
theorem litS2_erase : ⌊litS2.translate⌋ = Tm.erase (.val (.obj dS)) := by decide +kernel

end Z2

/-! ## Z3.  The counters and the child order

`z : ⊤ ⊢ ν(x. {a = ν(y. {A = ⊤})} ∧ {b = z} ∧ {B = ⊤})`, declared
`{val a : μ(y. {A : ⊤..⊤})} ∧ {b : ⊤} ∧ {B : ⊤..⊤}`.  The field labels are
`[b, a]`, right conjunct first, the stable label list is `[a]`, and the
children are the object child at `a` and the forwarding at `b`.

Then two stable fields around a plain field that holds a variable, where the
second stable literal has a plain field that holds the outer self:
`z : ⊤ ⊢ ν(x. {val a = ν(y. {A = ⊤})} ∧ ({b = z} ∧ {val c = ν(y. {B = ⊤} ∧ {d = x})}))`.
The `∋ᵛ` counter of `litMorphism` gives `c` and `a` their positions, and the
image checks. -/

namespace Z3

def dIn3 : Defs ((([],x),x),x) := .typ lA .top
def TIn3 : Ty ((([],x),x),x) := .typ lA .top .top
def dM : Defs (([],x),x) :=
  .and (.and (.trm la (.val (.obj dIn3))) (.trm lb (.path (.there .here)))) (.typ lB .top)
def TM : Ty (([],x),x) :=
  .and (.and (.vfld la (.mu TIn3)) (.fld lb .top)) (.typ lB .top .top)

def defsM : DefsTy (Γz.consSelf dM TM) dM TM :=
  .and (.and (.trmObj .typ .typ) (.trm (.sub .var .top))) .typ

theorem dM_distinct : Defs.Distinct dM := by
  refine .and (.and .trm .trm ?_) .typ ?_
  · intro ℓ h h'
    simp only [Defs.labels, List.mem_singleton] at h h'
    subst h
    exact absurd h' (by decide)
  · intro ℓ h h'
    simp only [Defs.labels, List.mem_append, List.mem_singleton] at h h'
    subst h'
    rcases h with h | h <;> exact absurd h (by decide)

def litM : HasTy Γz (.val (.obj dM)) (.mu TM) := .obj defsM dM_distinct

def FM : FCdot.Fields (([],x),x) := defsM.translateFields .here TM.literalTy.weaken 0

theorem FM_labels : FM.labels = [lb, la] := by decide +kernel
theorem FM_valLabels : FM.valLabels = [la] := by decide +kernel
theorem TM_labels : TM.fieldLabels = [lb, la] ∧ TM.valLabels = [la] := by decide +kernel
theorem blocks_M : TM.blocks dM = (FCdot.Value.obj TM.witnesses FM).blockSelf := by
  decide +kernel
theorem litM_checks : FCdot.checkTm Γz.translate litM.translate (Ty.mu TM).translate = true := by
  decide +kernel

def dInC : Defs ((([],x),x),x) := .and (.typ lB .top) (.trm ld (.path (.there .here)))
def TInC : Ty ((([],x),x),x) := .and (.typ lB .top .top) (.fld ld .top)

def dL : Defs (([],x),x) :=
  .and (.trm la (.val (.obj dIn3)))
    (.and (.trm lb (.path (.there .here))) (.trm lc (.val (.obj dInC))))
def TL : Ty (([],x),x) :=
  .and (.vfld la (.mu TIn3)) (.and (.fld lb .top) (.vfld lc (.mu TInC)))

theorem dInC_distinct : Defs.Distinct dInC := by
  refine .and .typ .trm ?_
  intro ℓ h h'
  simp only [Defs.labels, List.mem_singleton] at h h'
  subst h
  exact absurd h' (by decide)

theorem dL_distinct : Defs.Distinct dL := by
  refine .and .trm (.and .trm .trm ?_) ?_
  · intro ℓ h h'
    simp only [Defs.labels, List.mem_singleton] at h h'
    subst h
    exact absurd h' (by decide)
  · intro ℓ h h'
    simp only [Defs.labels, List.mem_append, List.mem_singleton] at h h'
    subst h
    rcases h' with h | h <;> exact absurd h (by decide)

def defsL : DefsTy (Γz.consSelf dL TL) dL TL :=
  .and (.trmObj .typ .typ)
    (.and (.trm (.sub .var .top))
      (.trmObj (.and .typ (.trm (.sub .var .top))) dInC_distinct))

def litL : HasTy Γz (.val (.obj dL)) (.mu TL) := .obj defsL dL_distinct

def FL : FCdot.Fields (([],x),x) := defsL.translateFields .here TL.literalTy.weaken 0

theorem R1_labels : FL.labels = TL.fieldLabels := by decide +kernel
theorem R1_valLabels : FL.valLabels = TL.valLabels ∧ TL.valLabels = [lc, la] := by
  decide +kernel
theorem R1_blocks : TL.blocks dL = (FCdot.Value.obj TL.witnesses FL).blockSelf := by
  decide +kernel
theorem R1_checks : FCdot.checkTm Γz.translate litL.translate (Ty.mu TL).translate = true := by
  decide +kernel
theorem R1_typed : FCdot.Tm.HasType Γz.translate litL.translate (Ty.mu TL).translate :=
  FCdot.checkTm_sound R1_checks

/-- Both images erase to the source literals. -/
theorem litM_erase : ⌊litM.translate⌋ = Tm.erase (.val (.obj dM)) := by decide +kernel
theorem litL_erase : ⌊litL.translate⌋ = Tm.erase (.val (.obj dL)) := by decide +kernel

end Z3

/-! ## Z4.  `Fld-E`, `Sel-<:` and the singleton rules at a path

In `w : μ(x. {val a : μ(y. {A : ⊤..⊤})})`, `Fld-E` reads the stable member at
`w.a`, and `Sel-<:` reads the bound of `w.a.A`.  The singleton rules at the path
`w.a` go through `PathCo.sngl` and the alias rules, and `snglSym` at the
variable `w` through `Atom.sngl`. -/

namespace Z4

/-- `Fld-E`: `w.a : μ(y. {A : ⊤..⊤})`. -/
def hwa : PathTy Γw (.sel (.var .here) la) (.mu TIn) := hwOpen.sel

def hwaOpen : PathTy Γw (.sel (.var .here) la) (.typ lA .top .top) :=
  (show TIn.substPath (.sel (.var .here) la) = .typ lA .top .top from rfl) ▸
    hwa.recE (by decide)

/-- `Sel-<:` at the path `w.a`: `w.a.A <: ⊤`. -/
def upper : Sub Γw (.sel (.sel (.var .here) la) lA) .top := .selUpper hwaOpen

theorem hwa_checks :
    FCdot.checkPath Γw.translate hwa.translatePath
      (Ty.mu TIn).translate = true := by
  decide +kernel
theorem hwa_path : hwa.translatePath.path = (Path.sel (.var .here) la).translate := by
  decide +kernel
theorem upper_checks :
    FCdot.checkLe Γw.translate upper.translate (Ty.sel (.sel (.var .here) la) lA).translate
      Ty.top.translate = true := by
  decide +kernel

/-- `snglSel` after `snglRefl`: `w.a : (w.a).type`. -/
def hwaSngl : PathTy Γw (.sel (.var .here) la) (.sngl (.sel (.var .here) la)) :=
  .snglSel (.snglRefl hwOpen) hwOpen
theorem hwaSngl_checks :
    FCdot.checkPath Γw.translate hwaSngl.translatePath
      (Ty.sngl (.sel (.var .here) la)).translate = true := by
  decide +kernel

/-- `snglTrans` at a field step: `w.a` has the type of the path it names. -/
def hwaTrans : PathTy Γw (.sel (.var .here) la) (.typ lA .top .top) :=
  .snglTrans hwaSngl hwaOpen
theorem hwaTrans_checks :
    FCdot.checkPath Γw.translate hwaTrans.translatePath
      (Ty.typ lA .top .top).translate = true := by
  decide +kernel

/-- `snglSym` at a variable, as an atom: `w : w.type` by `Atom.sngl`. -/
def hwSym : PathTy Γw (.var .here) (.sngl (.var .here)) := .snglSym (.snglRefl hw) hw
theorem hwSym_checks :
    FCdot.checkAtom Γw.translate (HasTy.sngl hwSym).translateAtom
      (Ty.sngl (.var .here)).translate = true := by
  decide +kernel

/-- `snglInv` at a field step: the aliased path is typed `⊤`. -/
def hwaInv : PathTy Γw (.sel (.var .here) la) .top := .snglInv hwaSngl
theorem hwaInv_checks :
    FCdot.checkPath Γw.translate hwaInv.translatePath Ty.top.translate = true := by
  decide +kernel

end Z4

/-! ## Z5.  `Sub.mu` through its template morphism

`μ(x. {A : ⊤..⊤} ∧ {B : x.A..x.A} ∧ {a : ⊥})` is read abstractly as
`μ(x. {B : ⊥..x.A} ∧ {a : ⊤})`.  The lower side of `B` is by `SelfFree.bot`,
its upper side by `SelfFree.refl`, since it mentions the self, and the field
by `SelfFree.closed` over `⊥ <: ⊤`.  The positions come from `Ty.typIdx` and
`Ty.fldIdx`.  `B`'s bounds sit at 2 and 3, `a`'s presence and bound at 4 and 5.

Then a declaration body with a stable field, a singleton conjunct and a nested
`μ` before the member it reads.
`w : ⊤ ⊢ μ(x. {val a : ⊤} ∧ w.type ∧ μ(y. {A : ⊤..⊤}) ∧ {B : ⊥..⊤})
  <: μ(x. {B : ⊥..⊤} ∧ {a : ⊤})`.  `Ty.vfldIdx` finds `a` at 0 and `Ty.typIdx`
finds `B` at 6. -/

namespace Z5

def DExact : Ty ([],x) :=
  .and (.and (.typ lA .top .top) (.typ lB (.sel (.var .here) lA) (.sel (.var .here) lA)))
    (.fld la .bot)
def DAbs : Ty ([],x) :=
  .and (.typ lB .bot (.sel (.var .here) lA)) (.fld la .top)

def subDecl : SubDecl Ctx.nil DExact DAbs :=
  .and (.typ rfl .bot .refl) (.fld (T1 := (Ty.bot : Ty []).weaken) rfl (.closed .top))

def subMu : Sub Ctx.nil (.mu DExact) (.mu DAbs) := .mu subDecl (by decide) (by decide)

theorem idx_B : DExact.typIdx .here lB 0 = some 2 := by decide +kernel
theorem idx_a : DExact.fldIdx .here la 0 = some 4 := by decide +kernel
theorem subMu_checks :
    FCdot.checkLe FCdot.Ctx.nil subMu.translate (Ty.mu DExact).translate
      (Ty.mu DAbs).translate = true := by
  decide +kernel

def DMix : Ty (([],x),x) :=
  .and (.and (.and (.vfld la .top) (.sngl (.var (.there .here)))) (.mu (.typ lA .top .top)))
    (.typ lB .bot .top)
def DMix' : Ty (([],x),x) := .and (.typ lB .bot .top) (.fld la .top)

def sdMix : SubDecl Γz DMix DMix' := .and (.typ rfl .refl .refl) (.vfldToFld rfl .refl)
def smMix : Sub Γz (.mu DMix) (.mu DMix') := .mu sdMix (by decide) (by decide)

theorem R3_idx : DMix.typIdx .here lB 0 = some 6 ∧ DMix.vfldIdx .here la 0 = some 0 := by
  decide +kernel
theorem R3_checks :
    FCdot.checkLe Γz.translate smMix.translate (Ty.mu DMix).translate
      (Ty.mu DMix').translate = true := by
  decide +kernel

end Z5

/-! ## Z6.  Stable fields in subtyping, the two projections, the derived `letSngl`

`Sub.vfld` and `Sub.vfldToFld` translate to object coercions that check.  The
projection `w.a` types by `projP` from a path typing of the receiver and by the
base's `proj`.  The image of the second is vanilla's term, `member` at the
receiver's atom (decision 28 (c)).  The derived `letSngl` over a field declared
at a singleton translates to the opaque `let` (decision 32), and the checker
binds the forwarding binder by `Binding.forLet`. -/

namespace Z6

def subVfld : Sub (Ctx.nil : Ctx []) (.vfld la .bot) (.vfld la .top) := .vfld .top
def subV2F : Sub (Ctx.nil : Ctx []) (.vfld la .top) (.fld la .top) := .vfldToFld

theorem subVfld_checks :
    FCdot.checkLe FCdot.Ctx.nil subVfld.translate (Ty.vfld la .bot).translate
      (Ty.vfld la .top).translate = true := by
  decide +kernel
theorem subV2F_checks :
    FCdot.checkLe FCdot.Ctx.nil subV2F.translate (Ty.vfld la .top).translate
      (Ty.fld la .top).translate = true := by
  decide +kernel

/-- `w.a` as a term: the projection reads `∋ a` through `Sub.vfldToFld` on a
path typing of `w`. -/
def projWa : HasTy Γw (.proj .here la) (.mu TIn) := .projP (hwOpen.sub .vfldToFld)
theorem projWa_checks :
    FCdot.checkTm Γw.translate projWa.translate (Ty.mu TIn).translate = true := by
  decide +kernel

/-- The same projection with the base's premise: `Rec-E` at the variable as a
term rule, then `Sub.vfldToFld`. -/
def hwOpenV0 : HasTy Γw (.path .here) (.vfld la (.mu TIn)) :=
  (show (TOutS.rename FCdot.Rename.succ.lift).substVar .here = .vfld la (.mu TIn)
    from rfl) ▸ (HasTy.recE (T := TOutS.rename FCdot.Rename.succ.lift) .var (by decide))
def hwOpenV : HasTy Γw (.path .here) (.fld la (.mu TIn)) := hwOpenV0.sub .vfldToFld
def projWaV : HasTy Γw (.proj .here la) (.mu TIn) := .proj hwOpenV
theorem projWaV_checks :
    FCdot.checkTm Γw.translate projWaV.translate (Ty.mu TIn).translate = true := by
  decide +kernel

/-- A base derivation of a projection translates to the vanilla term:
`member` at the receiver's atom, indices 0 and 1. -/
theorem projWaV_image :
    projWaV.translate =
      .cast (.proj hwOpenV.translateAtom la
          (.member hwOpenV.translateAtom (.refl (Ty.translate (.fld la (.mu TIn)))) 0))
        (.member hwOpenV.translateAtom (.refl (Ty.translate (.fld la (.mu TIn)))) 1) := rfl

/-- `z : ⊤, x : {a : z.type} ⊢ let y = x.a in y : z.type`, the derived
`letSngl`. -/
def Γq : Ctx (([],x),x) := (Ctx.nil.cons .top).cons (.fld la (.sngl (.var .here)))
def letQ : HasTy Γq (.let (.proj .here la) (.path .here)) (.sngl (.var (.there .here))) :=
  HasTy.letSngl .var .var .sngl
theorem letQ_checks :
    FCdot.checkTm Γq.translate letQ.translate (Ty.sngl (.var (.there .here))).translate = true := by
  decide +kernel

/-- The derived `letSngl` over a field declared at the singleton of a field
path.  `w : {val b : ⊤}, x : {a : (w.b).type} ⊢ let y = x.a in y`. -/
def Γ6 : Ctx (([],x),x) :=
  (Ctx.nil.cons (.vfld lb .top)).cons (.fld la (.sngl (.sel (.var .here) lb)))
def let6 : HasTy Γ6 (.let (.proj .here la) (.path .here)) (.sngl (.sel (.var (.there .here)) lb)) :=
  HasTy.letSngl .var .var .sngl
theorem R4_checks :
    FCdot.checkTm Γ6.translate let6.translate
      (Ty.sngl (.sel (.var (.there .here)) lb)).translate = true := by
  decide +kernel

end Z6

/-! ## Z7.  Decision 28 on its images, and X3

Term typing keeps the base's variable rules, the bridge from path typing is
at a singleton, and a projection may read a path typing.  What that keeps is
checked here on the image.  The singleton at a variable through `snglTrans`.
Projection and bounds through a singleton-typed variable.  The self-free
replacement case at an opaque variable, with no `repl`.  E9's shape through the
derived `letSngl`.  The base's variable rules as atoms.  X3 of P0. -/

namespace Z7

/-- `z : ⊤, x : {val a : z.type}, y : z.type ⊢ y : (x.a).type`, by `snglTrans`
at the variable `y`. -/
def ΓE1 : Ctx ((([],x),x),x) :=
  ((Ctx.nil.cons .top).cons (.vfld la (.sngl (.var .here)))).cons (.sngl (.var (.there .here)))
def hxaE1 : PathTy ΓE1 (.sel (.var (.there .here)) la) (.sngl (.var (.there (.there .here)))) :=
  (pvar' (.there .here) rfl : PathTy ΓE1 _ (.vfld la (.sngl (.var (.there (.there .here)))))).sel
def hzxE1 : PathTy ΓE1 (.var (.there (.there .here))) (.sngl (.sel (.var (.there .here)) la)) :=
  .snglSym hxaE1 (.sub .var .top)
def hyE1 : PathTy ΓE1 (.var .here) (.sngl (.sel (.var (.there .here)) la)) :=
  .snglTrans (pvar' .here rfl) hzxE1
def tyE1 : HasTy ΓE1 (.path .here) (.sngl (.sel (.var (.there .here)) la)) := .sngl hyE1
theorem E1_term :
    FCdot.checkTm ΓE1.translate tyE1.translate
      (Ty.sngl (.sel (.var (.there .here)) la)).translate = true := by
  decide +kernel
theorem E1_root : tyE1.translateAtom.root = .here := by decide +kernel

/-- `w : {val a : {b : ⊤}}, y : (w.a).type ⊢ y.b : ⊤`. -/
def ΓE2 : Ctx (([],x),x) :=
  (Ctx.nil.cons (.vfld la (.fld lb .top))).cons (.sngl (.sel (.var .here) la))
def hwaE2 : PathTy ΓE2 (.sel (.var (.there .here)) la) (.fld lb .top) :=
  (pvar' (.there .here) rfl : PathTy ΓE2 _ (.vfld la (.fld lb .top))).sel
def hybE2 : PathTy ΓE2 (.var .here) (.fld lb .top) := .snglTrans (pvar' .here rfl) hwaE2
def projE2 : HasTy ΓE2 (.proj .here lb) .top := .projP hybE2
theorem E2_proj : FCdot.checkTm ΓE2.translate projE2.translate Ty.top.translate = true := by
  decide +kernel

/-- `w : {val a : {A : ⊤..⊤}}, y : (w.a).type ⊢ y.A <: ⊤`. -/
def ΓE2' : Ctx (([],x),x) :=
  (Ctx.nil.cons (.vfld la (.typ lA .top .top))).cons (.sngl (.sel (.var .here) la))
def hwaE2' : PathTy ΓE2' (.sel (.var (.there .here)) la) (.typ lA .top .top) :=
  (pvar' (.there .here) rfl : PathTy ΓE2' _ (.vfld la (.typ lA .top .top))).sel
def upperE2 : Sub ΓE2' (.sel (.var .here) lA) .top :=
  .selUpper (.snglTrans (pvar' .here rfl) hwaE2')
theorem E2_upper :
    FCdot.checkLe ΓE2'.translate upperE2.translate (Ty.sel (.var .here) lA).translate
      Ty.top.translate = true := by
  decide +kernel

/-- The self-free replacement case at an opaque variable, with no `repl`:
`q : {A : ⊤..⊤}, y : q.type ⊢ y.A <: q.A`. -/
def ΓE3 : Ctx (([],x),x) := (Ctx.nil.cons (.typ lA .top .top)).cons (.sngl (.var .here))
def hqE3 : PathTy ΓE3 (.var (.there .here)) (.typ lA .top .top) := pvar' (.there .here) rfl
def subE3 : Sub ΓE3 (.sel (.var .here) lA) (.sel (.var (.there .here)) lA) :=
  .trans (.selUpper (.snglTrans (pvar' .here rfl) hqE3)) (.selLower hqE3)
theorem E3_checks :
    FCdot.checkLe ΓE3.translate subE3.translate (Ty.sel (.var .here) lA).translate
      (Ty.sel (.var (.there .here)) lA).translate = true := by
  decide +kernel

/-- E9's shape through the derived `letSngl`:
`q : {b : ⊤}, x : {a : q.type} ⊢ let y = x.a in y.b : ⊤`.  The body reads
`y.b` through `snglTrans` at the binder. -/
def ΓE4 : Ctx (([],x),x) := (Ctx.nil.cons (.fld lb .top)).cons (.fld la (.sngl (.var .here)))
def bodyE4 : HasTy (ΓE4.cons (.sngl (.var (.there .here)))) (.proj .here lb) (Ty.top.weaken) :=
  .projP (.snglTrans (pvar' .here rfl) (pvar' (.there (.there .here)) rfl))
def letE4 : HasTy ΓE4 (.let (.proj .here la) (.proj .here lb)) .top :=
  HasTy.letSngl .var bodyE4 .top
theorem E4_checks : FCdot.checkTm ΓE4.translate letE4.translate Ty.top.translate = true := by
  decide +kernel

/-- `Rec-I` over `Rec-E` at a variable, as an atom. -/
def hwFoldE : HasTy Γw (.path .here) (.mu (TOutS.rename FCdot.Rename.succ.lift)) :=
  .recI ((show (TOutS.rename FCdot.Rename.succ.lift).substVar .here = .vfld la (.mu TIn)
    from rfl) ▸ (HasTy.recE (T := TOutS.rename FCdot.Rename.succ.lift) .var (by decide))) (by decide)
theorem E5_fold :
    FCdot.checkTm Γw.translate hwFoldE.translate
      (Ty.mu (TOutS.rename FCdot.Rename.succ.lift)).translate = true := by
  decide +kernel

/-- `And-I` at a variable, as an atom. -/
def hwBothE : HasTy Γw (.path .here) (.and (Ty.mu TOutS).weaken (Ty.mu TOutS).weaken) :=
  .andI .var .var
theorem E5_both :
    FCdot.checkTm Γw.translate hwBothE.translate
      (Ty.and (Ty.mu TOutS).weaken (Ty.mu TOutS).weaken).translate = true := by
  decide +kernel

/-- A singleton at a variable whose derivation passes a field path:
`z : ⊤, x : {val a : z.type} ⊢ z : (x.a).type`. -/
def ΓE5 : Ctx (([],x),x) := (Ctx.nil.cons .top).cons (.vfld la (.sngl (.var .here)))
def hzsE5 : PathTy ΓE5 (.var (.there .here)) (.sngl (.sel (.var .here) la)) :=
  .snglSym (pvar' .here rfl : PathTy ΓE5 _ (.vfld la (.sngl (.var (.there .here))))).sel
    (.sub .var .top)
def tzsE5 : HasTy ΓE5 (.path (.there .here)) (.sngl (.sel (.var .here) la)) := .sngl hzsE5
theorem E5_sngl :
    FCdot.checkTm ΓE5.translate tzsE5.translate (Ty.sngl (.sel (.var .here) la)).translate
      = true := by
  decide +kernel

/-- X3 of P0, `let y = x.a in y.b`, with its body under the singleton binder.
Both are the derivations of `DotMNF/Examples.lean`. -/
theorem X3E_body_checks :
    FCdot.checkTm Examples.X3_CtxY.translate Examples.X3_body.translate
      Ty.top.translate = true := by
  decide +kernel
theorem X3E_checks :
    FCdot.checkTm Examples.X3_Ctx.translate Examples.X3.translate Ty.top.translate = true := by
  decide +kernel

/-- The images erase to the source terms. -/
theorem tyE1_erase : ⌊tyE1.translate⌋ = Tm.erase (.path .here) := by decide +kernel
theorem projE2_erase : ⌊projE2.translate⌋ = Tm.erase (.proj .here lb) := by decide +kernel
theorem letE4_erase :
    ⌊letE4.translate⌋ = Tm.erase (.let (.proj .here la) (.proj .here lb)) := by
  decide +kernel
theorem hwFoldE_erase : ⌊hwFoldE.translate⌋ = Tm.erase (.path .here) := by decide +kernel
theorem hwBothE_erase : ⌊hwBothE.translate⌋ = Tm.erase (.path .here) := by decide +kernel
theorem tzsE5_erase : ⌊tzsE5.translate⌋ = Tm.erase (.path (.there .here)) := by decide +kernel
theorem X3_body_erase :
    ⌊Examples.X3_body.translate⌋ = Tm.erase (.proj .here Examples.lb) := by
  decide +kernel
theorem X3_erase :
    ⌊Examples.X3.translate⌋ = Tm.erase (.let (.proj .here Examples.la) (.proj .here Examples.lb)) := by
  decide +kernel

end Z7

/-! ## Z8.  The kernel evaluates translations

Every translation function is structural (decision 31), so `decide +kernel`
unfolds the image of `And₁`, which reads `identityMorphism`, and the images of
X1 and X4 of P0.  `And₁` and X4 are the probes on which the vanilla shapes
failed. -/

namespace Z8

def S0 : Ty [] := .typ lA .top .top
def T0 : Ty [] := .fld la .top

def and1Src : Sub (Ctx.nil : Ctx []) (.and S0 T0) S0 := .and1

/-- `And₁` through `identityMorphism`. -/
theorem K1_fixed :
    FCdot.checkLe FCdot.Ctx.nil and1Src.translate (Ty.and S0 T0).translate S0.translate = true := by
  decide +kernel

/-- X4 of P0, gDOT Fig. 2's `types` literal with its two lambda fields plain. -/
theorem K2_fixed :
    FCdot.checkTm Examples.X4_Ctx.translate Examples.X4_lit0.translate
      (Ty.mu Examples.X4_Body0).translate = true := by
  decide +kernel

/-- `Rec-E` as a term rule: `w : μ(x. {a : ⊤}) ⊢ w : {a : ⊤}`. -/
def Γk : Ctx ([],x) := Ctx.nil.cons (.mu (.fld la .top))
def recEk : HasTy Γk (.path .here) (.fld la .top) :=
  HasTy.recE (T := .fld la .top) (var' .here rfl) .fld
theorem K3_recE :
    FCdot.checkTm Γk.translate recEk.translate (Ty.fld la .top).translate = true := by
  decide +kernel

/-- X1 of P0, pDOT Sec. 2.2: the literal, and both routes between `x.c.A` and
`x.B`. -/
theorem KX1_lit :
    FCdot.checkTm FCdot.Ctx.nil (Examples.X1_lit (Γ := Ctx.nil)).translate
      (Ty.mu Examples.X1_Self).translate = true := by
  decide +kernel
theorem KX1_AC :
    FCdot.checkLe Examples.X1_Ctx.translate Examples.X1_ACfromA.translate
      (Ty.sel (.sel (.var .here) Examples.X1_lc) Examples.lA).translate
      (Ty.sel (.var .here) Examples.lB).translate = true := by
  decide +kernel
theorem KX1_BA :
    FCdot.checkLe Examples.X1_Ctx.translate Examples.X1_BAfromB.translate
      (Ty.sel (.var .here) Examples.lB).translate
      (Ty.sel (.sel (.var .here) Examples.X1_lc) Examples.lA).translate = true := by
  decide +kernel

end Z8

/-! ## Z9.  Why decisions 28 and 29

The image of a term at a variable is an atom rooted there.  A variable of
singleton type used at a type of its alias that is not a singleton would need
a template that reads an inclusion out of `[≈ q]`, and there is none.  A
coercion between two singletons would need a template that rewrites an alias,
and there is none. -/

namespace Z9

/-- No template proves an inclusion proposition out of the singleton
telescope.  Every `le` template names a source `⊑` or `≐` entry, and `[≈ q]`
has none (decision 28). -/
theorem no_le_out_of_sngl {s : Sig} {Γ : FCdot.Ctx s} {q : FCdot.Path (s,x)}
    {m : FCdot.Morphism s} {S T : FCdot.Ty (s,x)} :
    ¬ FCdot.Morphism.HasType Γ (.cons .nil (.alias q)) m (.cons .nil (.le S T)) := by
  intro h
  cases h with
  | le _ hj _ _ => cases hj with | there h' => cases h'
  | leEq _ hj _ _ => cases hj with | there h' => cases h'
  | leEqSym _ hj _ _ => cases hj with | there h' => cases h'

/-- A template copies an alias and never rewrites it.  Out of `[≈ q]` it
proves `≈ q'` only at `q' = q` (decision 29). -/
theorem alias_template_fixed {s : Sig} {Γ : FCdot.Ctx s} {q q' : FCdot.Path (s,x)}
    {m : FCdot.Morphism s}
    (h : FCdot.Morphism.HasType Γ (.cons .nil (.alias q)) m (.cons .nil (.alias q'))) :
    q' = q := by
  cases h with
  | aliasCopy _ hj =>
      cases hj with
      | here => rfl
      | there h' => cases h'

end Z9

end TargetExamples
end DotMNF
end Paths
