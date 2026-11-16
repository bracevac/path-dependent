import Coercions.Selective.FsubCompare.Measure
/-!
# Three discriminating examples, on both sides

Context `Y <: Top → Top, X <: Y` (`SelFsub.ctxYX`, `X = var 0`, `Y = var 1`); in FCsub
its image `ctxOf ctxYX` has the four binders `type Y, h₁ : Y <: Top→Top, type X, h₂ : X <: Y`.
-/
namespace Compare.Ex
open SelFsub (Ty Ctx Cert Sub synthC)

abbrev tt : Ty n := .arr .top .top
abbrev Γ := SelFsub.ctxYX
abbrev G := ctxOf Γ

/-- body of the universals in example 3: `Z → Top`, with `Z = var 0` in `Ty 3`. -/
abbrev C3 : Ty 3 := .arr (.var 0) .top

/-! ## Example 1: `X ⇒ Y ⇒ Top → Top` -/
def sel1 : Cert 2 := .seq (.step (.var 0) (.var 1)) (.step (.var 1) tt)
def sub1 : Sub Γ (.var 0) tt := .trans (.bound 0) (.bound 1)
def fc1 : FCsub.LeCo (Sg 2) := .trans (.var .here) (.var (.there (.there .here)))

/-! ## Example 2a: arrow domain, `(Top→Top) → Top ⇒ X → Top` -/
def sel2a : Cert 2 := .seq (.step (.arr tt .top) (.arr (.var 1) .top)) (.step (.arr (.var 1) .top) (.arr (.var 0) .top))
def sub2a : Sub Γ (.arr tt .top) (.arr (.var 0) .top) := .arr (.trans (.bound 0) (.bound 1)) .refl
def fc2a : FCsub.LeCo (Sg 2) := .arr (.trans (.var .here) (.var (.there (.there .here)))) (.refl .top)

/-! ## Example 2b: arrow codomain, `Top → X ⇒ Top → Top→Top` -/
def sel2b : Cert 2 := .seq (.step (.arr .top (.var 0)) (.arr .top (.var 1))) (.step (.arr .top (.var 1)) (.arr .top tt))
def sub2b : Sub Γ (.arr .top (.var 0)) (.arr .top tt) := .arr .refl (.trans (.bound 0) (.bound 1))
def fc2b : FCsub.LeCo (Sg 2) :=
  .arr (.refl .top)
    (FCsub.LeCo.trans (.var .here) (.var (.there (.there .here)))).weaken

/-! ## Example 3: bound change, `∀(Z <: Top→Top). Z→Top ⇒ ∀(Z <: Y). Z→Top` -/
def sel3 : Cert 2 := .step (.all tt C3) (.all (.var 1) C3)
def sub3 : Sub Γ (.all tt C3) (.all (.var 1) C3) := .all (.bound 1) .refl
def fc3 : FCsub.LeCo (Sg 2) :=
  .forallT
    (.map (telOf (SelFsub.Ty.var 1)) (telOf tt)
      (.snoc .nil (.tvar (.there .here)))
      (.snoc .nil (.trans (.var .here)
        (FCsub.LeCo.var (.there (.there .here))).weaken.weaken)))
    (.arr (.tvar (.there .here)) .top) (.arr (.tvar (.there .here)) .top)
    (.refl (.arr (.tvar (.there .here)) .top))

/-! ## Example 3b: the same with a chain `X ⇒ Y ⇒ Top→Top` as the bound change -/
def sel3b : Cert 2 :=
  .seq (.step (.all tt C3) (.all (.var 1) C3)) (.step (.all (.var 1) C3) (.all (.var 0) C3))
def sub3b : Sub Γ (.all tt C3) (.all (.var 0) C3) := .all (.trans (.bound 0) (.bound 1)) .refl
def fc3b : FCsub.LeCo (Sg 2) :=
  .forallT
    (.map (telOf (SelFsub.Ty.var 0)) (telOf tt)
      (.snoc .nil (.tvar (.there .here)))
      (.snoc .nil (.trans (.var .here)
        (FCsub.LeCo.trans (.var .here) (.var (.there (.there .here)))).weaken.weaken)))
    (.arr (.tvar (.there .here)) .top) (.arr (.tvar (.there .here)) .top)
    (.refl (.arr (.tvar (.there .here)) .top))

/-! ## Rows: (steps, seqs, nodes, stored type nodes, refl steps, dag, distinct endpoints) -/
#eval [("1 hand", Sel.row sel1), ("1 mech", Sel.row sub1.toCert),
  ("2a hand", Sel.row sel2a), ("2a mech", Sel.row sub2a.toCert),
  ("2b hand", Sel.row sel2b), ("2b mech", Sel.row sub2b.toCert),
  ("3 hand", Sel.row sel3), ("3 mech", Sel.row sub3.toCert),
  ("3b hand", Sel.row sel3b), ("3b mech", Sel.row sub3b.toCert)]
/-! ## FCsub rows: (LeCo nodes, vars, trans, refl, TelMor nodes, stored type nodes, equality tests) -/
#eval [("1", Fc.row (Fc.cnt fc1)), ("2a", Fc.row (Fc.cnt fc2a)), ("2b", Fc.row (Fc.cnt fc2b)),
  ("3", Fc.row (Fc.cnt fc3)), ("3b", Fc.row (Fc.cnt fc3b))]
#eval [("sel1 mech", repr sub1.toCert), ("2a", repr sub2a.toCert), ("2b", repr sub2b.toCert), ("3", repr sub3.toCert), ("3b", repr sub3b.toCert)]


/-! ## Kernel-checked statements -/

-- SelFsub checker accepts hand-minimal and mechanical certificates with the stated endpoints
theorem sel1_ok : synthC Γ sel1 = some (.var 0, tt) := by decide
theorem sel2a_ok : synthC Γ sel2a = some (.arr tt .top, .arr (.var 0) .top) := by decide
theorem sel2b_ok : synthC Γ sel2b = some (.arr .top (.var 0), .arr .top tt) := by decide
theorem sel3_ok : synthC Γ sel3 = some (.all tt C3, .all (.var 1) C3) := by decide
theorem sel3b_ok : synthC Γ sel3b = some (.all tt C3, .all (.var 0) C3) := by decide
theorem mech1_ok : synthC Γ sub1.toCert = some (.var 0, tt) := by decide
theorem mech2a_ok : synthC Γ sub2a.toCert = some (.arr tt .top, .arr (.var 0) .top) := by decide
theorem mech2b_ok : synthC Γ sub2b.toCert = some (.arr .top (.var 0), .arr .top tt) := by decide
theorem mech3_ok : synthC Γ sub3.toCert = some (.all tt C3, .all (.var 1) C3) := by decide
theorem mech3b_ok : synthC Γ sub3b.toCert = some (.all tt C3, .all (.var 0) C3) := by decide
-- the single step of the witness is not primitive
theorem sel1_single_rejected : synthC Γ (.step (.var 0) tt) = none := by decide
-- hand-minimal equals mechanical in example 1 only
theorem mech1_eq_hand : sub1.toCert = sel1 := rfl
theorem mech2a_ne_hand : sub2a.toCert ≠ sel2a := by decide
theorem mech3_ne_hand : sub3.toCert ≠ sel3 := by decide

-- FCsub checker (the repository's `synthLe`) accepts the evidence with the translated endpoints
theorem fc1_ok : FCsub.synthLe G fc1 = some (tyOf (.var 0), tyOf tt) := by decide +kernel
theorem fc2a_ok : FCsub.synthLe G fc2a = some (tyOf (.arr tt .top), tyOf (.arr (.var 0) .top)) := by decide +kernel
theorem fc2b_ok : FCsub.synthLe G fc2b = some (tyOf (.arr .top (.var 0)), tyOf (.arr .top tt)) := by decide +kernel
theorem fc3_ok : FCsub.synthLe G fc3 = some (tyOf (.all tt C3), tyOf (.all (.var 1) C3)) := by decide +kernel
theorem fc3b_ok : FCsub.synthLe G fc3b = some (tyOf (.all tt C3), tyOf (.all (.var 0) C3)) := by decide +kernel
-- the hand-written FCsub evidence is exactly the translation of the declarative derivation
theorem fc1_eq : leOf sub1 = fc1 := by decide +kernel
theorem fc2a_eq : leOf sub2a = fc2a := by decide +kernel
theorem fc2b_eq : leOf sub2b = fc2b := by decide +kernel
theorem fc3_eq : leOf sub3 = fc3 := by decide +kernel
theorem fc3b_eq : leOf sub3b = fc3b := by decide +kernel

-- measure rows
theorem sel_rows :
    [Sel.row sel1, Sel.row sub1.toCert, Sel.row sel2a, Sel.row sub2a.toCert, Sel.row sel2b,
     Sel.row sub2b.toCert, Sel.row sel3, Sel.row sub3.toCert, Sel.row sel3b, Sel.row sub3b.toCert] =
    [[2,1,3,6,0,3,3], [2,1,3,6,0,3,3], [2,1,3,14,0,3,3], [3,2,5,20,1,5,3], [2,1,3,14,0,3,3],
     [3,2,5,20,1,5,3], [1,0,1,12,0,1,2], [2,1,3,22,1,3,2], [2,1,3,22,0,3,3], [3,2,5,32,1,5,3]] := by
  decide +kernel
theorem fc_rows :
    [Fc.row (Fc.cnt fc1), Fc.row (Fc.cnt fc2a), Fc.row (Fc.cnt fc2b), Fc.row (Fc.cnt fc3),
     Fc.row (Fc.cnt fc3b)] =
    [[3,2,1,0,0,0,1], [5,2,1,1,0,1,1], [5,2,1,1,0,1,1], [5,2,1,1,1,16,5], [7,3,2,1,1,16,6]] := by
  decide +kernel

end Compare.Ex
