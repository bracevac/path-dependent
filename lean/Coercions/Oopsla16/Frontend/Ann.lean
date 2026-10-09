import Coercions.Oopsla16.Syntax

/-!
# Annotated Oopsla16 terms

`ATm` is `Oopsla16.Tm [] s` plus two annotations the calculus does not keep.

- The self type of an object literal, when it is written.  `T_Obj` types the
  members under the self type it concludes with, and `Tm.tobj` has no slot for
  it.  A literal whose methods are all annotated gets one from `selfOf?`.  A
  literal with a Curry style method and no written self type is not one the
  typer takes as it is (`ATm.landed`).  A fill writes a self type into the
  slot and changes nothing else (`ATm.fills`).
- An ascription `(t : T)`, a point where the typer checks at a stated type.

Members carry no label.  As in the calculus, a member's label is the length of
the list below it.  The store scope is empty throughout, since a source
program names no store location.

Every definition is structural, so `decide` and `rfl` reduce it.  Nothing here
is part of the metatheory.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Lb Ty Tm Dm Dms)

/-! ## The syntax -/

mutual
/-- Terms of Oopsla16 at the empty store scope, with a literal's optional
self type and an ascription. -/
inductive ATm : Sig → Type where
  /-- A variable of the local scope. -/
  | var : BVar s .var → ATm s
  /-- An object literal, with its self type if one was written.  Both live
  under the self binder. -/
  | obj : Option (Ty [] (s,x)) → ADms (s,x) → ATm s
  /-- `t.l(u)`, a call at a positional label. -/
  | app : ATm s → Lb → ATm s → ATm s
  /-- `(t : T)`, front end only. -/
  | asc : ATm s → Ty [] s → ATm s
/-- A member of an annotated literal.  It carries no label. -/
inductive ADm : Sig → Type where
  /-- `def (x [: S]) [: U] = t`.  The result type and the body live under the
  parameter. -/
  | dfun : Option (Ty [] s) → Option (Ty [] (s,x)) → ATm (s,x) → ADm s
  /-- `type = T`. -/
  | dty : Ty [] s → ADm s
/-- A member list, newest member first.  The label of a member is the length
of the list below it. -/
inductive ADms : Sig → Type where
  | dnil : ADms s
  | dcons : ADm s → ADms s → ADms s
end

/-! ## Erasure

The only bridge from `ATm` to `Oopsla16.Tm`.  It drops the self type and the
ascription. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase {s : Sig} (a : ATm s) : Tm [] s :=
  match a with
  | .var x => .tvar (.abs x)
  | .obj _ ds => .tobj ds.erase
  | .app t l u => .tapp t.erase l u.erase
  | .asc t _ => t.erase
termination_by structural a
/-- Drop the annotations of a member. -/
def ADm.erase {s : Sig} (d : ADm s) : Dm [] s :=
  match d with
  | .dfun S U t => .dfun S U t.erase
  | .dty T => .dty T
termination_by structural d
/-- Drop the annotations of a member list. -/
def ADms.erase {s : Sig} (ds : ADms s) : Dms [] s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.erase ds'.erase
termination_by structural ds
end

/-- The number of members, the label of a member consed onto the front. -/
def ADms.length {s : Sig} (ds : ADms s) : Nat :=
  match ds with
  | .dnil => 0
  | .dcons _ ds' => ds'.length + 1
termination_by structural ds

/-- Erasure keeps the number of members. -/
theorem ADms.length_erase {s : Sig} : (ds : ADms s) → ds.erase.length = ds.length
  | .dnil => rfl
  | .dcons d ds' => by
      show (Dms.dcons d.erase ds'.erase).length = ds'.length + 1
      rw [Oopsla16.Dms.length_dcons, ADms.length_erase ds']

/-! ## The self type of a fully annotated literal

When every method carries both annotations, `D_Nil`, `D_Typ` and `D_Fun`
(`Oopsla16.DmsHasType`) give a member list one type: a right nested
intersection ending in `⊤`, with the positions as labels.  `selfOf?` computes
it and answers `none` when an annotation is missing.  A wrong proposal only
fails to type, since the typer checks the members against it. -/

/-- The precise self type of a member list whose methods are all annotated. -/
def selfOf? {σ s : Sig} (ds : Dms σ s) : Option (Ty σ s) :=
  match ds with
  | .dnil => some .TTop
  | .dcons (.dty T) ds' => (selfOf? ds').map (.TAnd (.TTyp ds'.length T T))
  | .dcons (.dfun (some S) (some U) _) ds' => (selfOf? ds').map (.TAnd (.TFun ds'.length S U))
  | .dcons (.dfun _ _ _) _ => none
termination_by structural ds

/-! ## Sanity -/

/-- The empty list has the self type `⊤`. -/
example : selfOf? (Dms.dnil : Dms [] ([],x)) = some .TTop := by decide

/-- A type member at position `0`. -/
example : selfOf? (Dms.dcons (.dty .TBot) .dnil : Dms [] ([],x))
    = some (.TAnd (.TTyp 0 .TBot .TBot) .TTop) := by decide

/-- A Curry style method leaves the self type undetermined. -/
example : (selfOf? (Dms.dcons (.dfun none (some .TTop) (.tvar (.abs .here))) .dnil
    : Dms [] ([],x))).isSome = false := by decide

/-- Two members: the first written one is at position `1`. -/
example : selfOf? (Dms.dcons (.dfun (some .TTop) (some .TTop) (.tvar (.abs .here)))
      (.dcons (.dty .TTop) .dnil) : Dms [] ([],x))
    = some (.TAnd (.TFun 1 .TTop .TTop) (.TAnd (.TTyp 0 .TTop .TTop) .TTop)) := by decide

/-- An ascription and a written self type both erase. -/
example : (ATm.asc (.obj (some .TTop) (.dcons (.dty .TTop) .dnil)) .TTop : ATm []).erase
    = .tobj (.dcons (.dty .TTop) .dnil) := rfl

/-! ## Empty slots

`ATm` is its own partial term.  Every slot inference may fill is an `Option`
already: the self type of a literal, and the parameter type and the result
type of a method.  `none` is an empty slot.  An empty slot matters only where
the typer cannot do without it.  A Curry style method under a written self
type types as it is, since the typer reads its types off the self type.  A
literal without a written self type types as it is when `selfOf?` computes
one.  `ATm.landed` is that test, made on every literal of the term. -/

deriving instance DecidableEq for ATm, ADm, ADms

mutual
/-- The typer can take the term as it is: every literal has a written self
type or one that `selfOf?` computes.  This is the test `synthF` and `checkF`
make at a literal (`o <|> selfOf? ds.erase`). -/
def ATm.landed {s : Sig} (a : ATm s) : Bool :=
  match a with
  | .var _ => true
  | .obj o ds => (o.isSome || (selfOf? ds.erase).isSome) && ds.landed
  | .app t _ u => t.landed && u.landed
  | .asc t _ => t.landed
termination_by structural a
/-- Every literal inside the member is one the typer takes. -/
def ADm.landed {s : Sig} (d : ADm s) : Bool :=
  match d with
  | .dfun _ _ t => t.landed
  | .dty _ => true
termination_by structural d
/-- Every literal inside the member list is one the typer takes. -/
def ADms.landed {s : Sig} (ds : ADms s) : Bool :=
  match ds with
  | .dnil => true
  | .dcons d ds' => d.landed && ds'.landed
termination_by structural ds
end

/-- The typer takes a literal without a written self type when it takes every
member and every method is annotated. -/
theorem landed_of_selfOf {s : Sig} {ds : ADms (s,x)} {T : Ty [] (s,x)}
    (h : selfOf? ds.erase = some T) (hb : ds.landed = true) :
    (ATm.obj none ds : ATm s).landed = true := by
  simp only [ATm.landed, h, hb, Option.isSome_none, Option.isSome_some, Bool.false_or,
    Bool.and_self]

/-! ## Fills

`a.fills b` says that `b` agrees with every slot `a` writes and with every
part of `a` that is no slot.  The only slot a fill writes is the self type of a
literal.  A method keeps the annotations the programmer wrote, since the typer
reads an absent one off the self type.  So a filled term erases to the term it
fills (`fills_erase`).

An empty self type agrees with a written one and with an empty one.  A literal
that `selfOf?` types needs no fill, and the fill leaves it as it is.  So every
term fills itself (`fills_refl`). -/

/-- A slot of `b` agrees with the slot of `a`: an empty slot agrees with
anything, a written one with itself. -/
def slotAgrees {α : Type} [DecidableEq α] : Option α → Option α → Bool
  | none, _ => true
  | some T, o => decide (o = some T)

mutual
/-- `b` is `a` with self types written where `a` has none. -/
def ATm.fills {s : Sig} (a b : ATm s) : Bool :=
  match a, b with
  | .var x, .var y => decide (x = y)
  | .obj o ds, .obj o' ds' => slotAgrees o o' && ds.fills ds'
  | .app t l u, .app t' l' u' => t.fills t' && decide (l = l') && u.fills u'
  | .asc t T, .asc t' T' => t.fills t' && decide (T = T')
  | _, _ => false
termination_by structural a
/-- The members agree: the same annotations, and bodies that fill. -/
def ADm.fills {s : Sig} (d e : ADm s) : Bool :=
  match d, e with
  | .dfun o1 o2 t, .dfun o1' o2' t' => decide (o1 = o1') && decide (o2 = o2') && t.fills t'
  | .dty T, .dty T' => decide (T = T')
  | _, _ => false
termination_by structural d
/-- The member lists agree member by member. -/
def ADms.fills {s : Sig} (ds es : ADms s) : Bool :=
  match ds, es with
  | .dnil, .dnil => true
  | .dcons d ds', .dcons e es' => d.fills e && ds'.fills es'
  | _, _ => false
termination_by structural ds
end

/-- Every slot agrees with itself. -/
theorem slotAgrees_refl {α : Type} [DecidableEq α] : (o : Option α) → slotAgrees o o = true
  | none => rfl
  | some _ => by simp [slotAgrees]

/-- Agreement of slots is transitive. -/
theorem slotAgrees_trans {α : Type} [DecidableEq α] :
    (o1 o2 o3 : Option α) → slotAgrees o1 o2 = true → slotAgrees o2 o3 = true →
      slotAgrees o1 o3 = true
  | none, _, _, _, _ => rfl
  | some _, o2, o3, h12, h23 => by
      simp only [slotAgrees, decide_eq_true_eq] at h12
      subst h12
      exact h23

mutual
/-- A filled term erases to the term it fills. -/
theorem fills_erase {s : Sig} : (a b : ATm s) → a.fills b = true → b.erase = a.erase
  | .var x, .var y, h => by
      simp only [ATm.fills, decide_eq_true_eq] at h
      subst h
      rfl
  | .obj _ ds, .obj _ ds', h => by
      simp only [ATm.fills, Bool.and_eq_true] at h
      simp only [ATm.erase, fillsDms_erase ds ds' h.2]
  | .app t l u, .app t' l' u', h => by
      simp only [ATm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h2
      simp only [ATm.erase, fills_erase t t' h1, fills_erase u u' h3]
  | .asc t _, .asc t' _, h => by
      simp only [ATm.fills, Bool.and_eq_true] at h
      simp only [ATm.erase, fills_erase t t' h.1]
  | .var _, .obj _ _, h | .var _, .app _ _ _, h | .var _, .asc _ _, h
  | .obj _ _, .var _, h | .obj _ _, .app _ _ _, h | .obj _ _, .asc _ _, h
  | .app _ _ _, .var _, h | .app _ _ _, .obj _ _, h | .app _ _ _, .asc _ _, h
  | .asc _ _, .var _, h | .asc _ _, .obj _ _, h | .asc _ _, .app _ _ _, h => by
      simp [ATm.fills] at h
/-- A filled member erases to the member it fills. -/
theorem fillsDm_erase {s : Sig} : (d e : ADm s) → d.fills e = true → e.erase = d.erase
  | .dfun o1 o2 t, .dfun o1' o2' t', h => by
      simp only [ADm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h1 h2
      simp only [ADm.erase, fills_erase t t' h3]
  | .dty T, .dty T', h => by
      simp only [ADm.fills, decide_eq_true_eq] at h
      subst h
      rfl
  | .dfun _ _ _, .dty _, h | .dty _, .dfun _ _ _, h => by simp [ADm.fills] at h
/-- A filled member list erases to the list it fills. -/
theorem fillsDms_erase {s : Sig} : (ds es : ADms s) → ds.fills es = true → es.erase = ds.erase
  | .dnil, .dnil, _ => rfl
  | .dcons d ds', .dcons e es', h => by
      simp only [ADms.fills, Bool.and_eq_true] at h
      simp only [ADms.erase, fillsDm_erase d e h.1, fillsDms_erase ds' es' h.2]
  | .dnil, .dcons _ _, h | .dcons _ _, .dnil, h => by simp [ADms.fills] at h
end

mutual
/-- Every term fills itself. -/
theorem fills_refl {s : Sig} : (a : ATm s) → a.fills a = true
  | .var _ => by simp [ATm.fills]
  | .obj o ds => by simp only [ATm.fills, slotAgrees_refl, fillsDms_refl ds, Bool.and_self]
  | .app t _ u => by simp [ATm.fills, fills_refl t, fills_refl u]
  | .asc t _ => by simp [ATm.fills, fills_refl t]
/-- Every member fills itself. -/
theorem fillsDm_refl {s : Sig} : (d : ADm s) → d.fills d = true
  | .dfun _ _ t => by simp [ADm.fills, fills_refl t]
  | .dty _ => by simp [ADm.fills]
/-- Every member list fills itself. -/
theorem fillsDms_refl {s : Sig} : (ds : ADms s) → ds.fills ds = true
  | .dnil => rfl
  | .dcons d ds' => by simp only [ADms.fills, fillsDm_refl d, fillsDms_refl ds', Bool.and_self]
end

mutual
/-- A fill of a fill is a fill. -/
theorem fills_trans {s : Sig} :
    (a b c : ATm s) → a.fills b = true → b.fills c = true → a.fills c = true
  | .var _, .var _, .var _, h1, h2 => by
      simp only [ATm.fills, decide_eq_true_eq] at h1 h2 ⊢
      exact h1.trans h2
  | .obj o1 d1, .obj o2 d2, .obj o3 d3, h1, h2 => by
      simp only [ATm.fills, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨slotAgrees_trans o1 o2 o3 h1.1 h2.1, fillsDms_trans d1 d2 d3 h1.2 h2.2⟩
  | .app t1 l1 u1, .app t2 l2 u2, .app t3 l3 u3, h1, h2 => by
      simp only [ATm.fills, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
      exact ⟨⟨fills_trans t1 t2 t3 h1.1.1 h2.1.1, h1.1.2.trans h2.1.2⟩,
        fills_trans u1 u2 u3 h1.2 h2.2⟩
  | .asc t1 T1, .asc t2 T2, .asc t3 T3, h1, h2 => by
      simp only [ATm.fills, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
      exact ⟨fills_trans t1 t2 t3 h1.1 h2.1, h1.2.trans h2.2⟩
  | .var _, .obj _ _, _, h1, _ | .var _, .app _ _ _, _, h1, _ | .var _, .asc _ _, _, h1, _
  | .obj _ _, .var _, _, h1, _ | .obj _ _, .app _ _ _, _, h1, _ | .obj _ _, .asc _ _, _, h1, _
  | .app _ _ _, .var _, _, h1, _ | .app _ _ _, .obj _ _, _, h1, _
  | .app _ _ _, .asc _ _, _, h1, _
  | .asc _ _, .var _, _, h1, _ | .asc _ _, .obj _ _, _, h1, _ | .asc _ _, .app _ _ _, _, h1, _ => by
      simp [ATm.fills] at h1
  | .var _, .var _, .obj _ _, _, h2 | .var _, .var _, .app _ _ _, _, h2
  | .var _, .var _, .asc _ _, _, h2
  | .obj _ _, .obj _ _, .var _, _, h2 | .obj _ _, .obj _ _, .app _ _ _, _, h2
  | .obj _ _, .obj _ _, .asc _ _, _, h2
  | .app _ _ _, .app _ _ _, .var _, _, h2 | .app _ _ _, .app _ _ _, .obj _ _, _, h2
  | .app _ _ _, .app _ _ _, .asc _ _, _, h2
  | .asc _ _, .asc _ _, .var _, _, h2 | .asc _ _, .asc _ _, .obj _ _, _, h2
  | .asc _ _, .asc _ _, .app _ _ _, _, h2 => by
      simp [ATm.fills] at h2
/-- A fill of a fill of a member is a fill. -/
theorem fillsDm_trans {s : Sig} :
    (d e f : ADm s) → d.fills e = true → e.fills f = true → d.fills f = true
  | .dfun a1 b1 t1, .dfun a2 b2 t2, .dfun a3 b3 t3, h1, h2 => by
      simp only [ADm.fills, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
      exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩, fills_trans t1 t2 t3 h1.2 h2.2⟩
  | .dty _, .dty _, .dty _, h1, h2 => by
      simp only [ADm.fills, decide_eq_true_eq] at h1 h2 ⊢
      exact h1.trans h2
  | .dfun _ _ _, .dty _, _, h1, _ | .dty _, .dfun _ _ _, _, h1, _ => by simp [ADm.fills] at h1
  | .dfun _ _ _, .dfun _ _ _, .dty _, _, h2 | .dty _, .dty _, .dfun _ _ _, _, h2 => by
      simp [ADm.fills] at h2
/-- A fill of a fill of a member list is a fill. -/
theorem fillsDms_trans {s : Sig} :
    (ds es fs : ADms s) → ds.fills es = true → es.fills fs = true → ds.fills fs = true
  | .dnil, .dnil, .dnil, _, _ => rfl
  | .dcons d1 ds1, .dcons d2 ds2, .dcons d3 ds3, h1, h2 => by
      simp only [ADms.fills, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨fillsDm_trans d1 d2 d3 h1.1 h2.1, fillsDms_trans ds1 ds2 ds3 h1.2 h2.2⟩
  | .dnil, .dcons _ _, _, h1, _ | .dcons _ _, .dnil, _, h1, _ => by simp [ADms.fills] at h1
  | .dnil, .dnil, .dcons _ _, _, h2 | .dcons _ _, .dcons _ _, .dnil, _, h2 => by
      simp [ADms.fills] at h2
end

/-! ## Dependencies on the self

A literal without a written self type types the bodies of its methods on
demand, so it needs to know which methods a body calls on the self.
`a.deps v` reads them off: the labels of the calls whose receiver is the self
variable `v`, in body order, and a flag for any other use of `v`.

The self has aliases.  The version has no `let`, so an alias is the self under
ascriptions, `(v : T)`.  A call `(v : T).l(u)` depends on `l` as `v.l(u)` does,
and it also sets the flag, since checking `v` against `T` reads the type of
the self.  A type that selects a type member of `v` is no dependency, since
type members are known before any body is typed. -/

/-- Two dependency readings one after the other. -/
def mergeDeps (a b : List Lb × Bool) : List Lb × Bool := (a.1 ++ b.1, a.2 || b.2)

/-- `a` is the variable `v` under zero or more ascriptions. -/
def ATm.isAliasOf {s : Sig} (a : ATm s) (v : BVar s .var) : Bool :=
  match a with
  | .var y => decide (y = v)
  | .asc t _ => t.isAliasOf v
  | _ => false
termination_by structural a

/-- `a` is an ascription. -/
def ATm.isAsc {s : Sig} (a : ATm s) : Bool :=
  match a with
  | .asc _ _ => true
  | _ => false

mutual
/-- The labels a term calls on the self `v`, and whether it uses `v` any
other way. -/
def ATm.deps {s : Sig} (a : ATm s) (v : BVar s .var) : List Lb × Bool :=
  match a with
  | .var y => ([], decide (y = v))
  | .obj _ ds => ds.deps v.there
  | .app t l u =>
      if t.isAliasOf v then mergeDeps ([l], t.isAsc) (u.deps v)
      else mergeDeps (t.deps v) (u.deps v)
  | .asc t _ => t.deps v
termination_by structural a
/-- The dependencies of a member's body, under its parameter. -/
def ADm.deps {s : Sig} (d : ADm s) (v : BVar s .var) : List Lb × Bool :=
  match d with
  | .dfun _ _ t => t.deps v.there
  | .dty _ => ([], false)
termination_by structural d
/-- The dependencies of a member list, member by member, newest first. -/
def ADms.deps {s : Sig} (ds : ADms s) (v : BVar s .var) : List Lb × Bool :=
  match ds with
  | .dnil => ([], false)
  | .dcons d ds' => mergeDeps (d.deps v) (ds'.deps v)
termination_by structural ds
end

/-! ## Erasures

The programs of the examples with some of their annotations erased.  `S`
erases every self type, `R` every result type, `P` every parameter type, and
`A` the self type of every literal in argument position.  `SR` is the program
a Scala programmer writes: no self type and no result type, and every
parameter type written, taken from the written self type where the program
left it to the self type.  `S` and `A` erase only slots a fill writes, so the
program fills its erasure (`eraseSelf_fills`, `eraseArgSelf_fills`). -/

mutual
/-- Erase every self type. -/
def ATm.eraseSelf {s : Sig} (a : ATm s) : ATm s :=
  match a with
  | .var x => .var x
  | .obj _ ds => .obj none ds.eraseSelf
  | .app t l u => .app t.eraseSelf l u.eraseSelf
  | .asc t T => .asc t.eraseSelf T
termination_by structural a
/-- Erase every self type inside a member. -/
def ADm.eraseSelf {s : Sig} (d : ADm s) : ADm s :=
  match d with
  | .dfun o1 o2 t => .dfun o1 o2 t.eraseSelf
  | .dty T => .dty T
termination_by structural d
/-- Erase every self type inside a member list. -/
def ADms.eraseSelf {s : Sig} (ds : ADms s) : ADms s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.eraseSelf ds'.eraseSelf
termination_by structural ds
end

mutual
/-- Erase every method result type. -/
def ATm.eraseRes {s : Sig} (a : ATm s) : ATm s :=
  match a with
  | .var x => .var x
  | .obj o ds => .obj o ds.eraseRes
  | .app t l u => .app t.eraseRes l u.eraseRes
  | .asc t T => .asc t.eraseRes T
termination_by structural a
/-- Erase the result type of a method, and every one inside its body. -/
def ADm.eraseRes {s : Sig} (d : ADm s) : ADm s :=
  match d with
  | .dfun o1 _ t => .dfun o1 none t.eraseRes
  | .dty T => .dty T
termination_by structural d
/-- Erase every method result type inside a member list. -/
def ADms.eraseRes {s : Sig} (ds : ADms s) : ADms s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.eraseRes ds'.eraseRes
termination_by structural ds
end

mutual
/-- Erase every method parameter type. -/
def ATm.eraseParam {s : Sig} (a : ATm s) : ATm s :=
  match a with
  | .var x => .var x
  | .obj o ds => .obj o ds.eraseParam
  | .app t l u => .app t.eraseParam l u.eraseParam
  | .asc t T => .asc t.eraseParam T
termination_by structural a
/-- Erase the parameter type of a method, and every one inside its body. -/
def ADm.eraseParam {s : Sig} (d : ADm s) : ADm s :=
  match d with
  | .dfun _ o2 t => .dfun none o2 t.eraseParam
  | .dty T => .dty T
termination_by structural d
/-- Erase every method parameter type inside a member list. -/
def ADms.eraseParam {s : Sig} (ds : ADms s) : ADms s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.eraseParam ds'.eraseParam
termination_by structural ds
end

mutual
/-- Erase the self type of every literal in argument position.  `arg` says
whether `a` itself is the argument of a call. -/
def ATm.eraseArgSelfAt {s : Sig} (arg : Bool) (a : ATm s) : ATm s :=
  match a with
  | .var x => .var x
  | .obj o ds => .obj (if arg then none else o) ds.eraseArgSelf
  | .app t l u => .app (t.eraseArgSelfAt false) l (u.eraseArgSelfAt true)
  | .asc t T => .asc (t.eraseArgSelfAt false) T
termination_by structural a
/-- Erase the self type of every literal in argument position inside a
member. -/
def ADm.eraseArgSelf {s : Sig} (d : ADm s) : ADm s :=
  match d with
  | .dfun o1 o2 t => .dfun o1 o2 (t.eraseArgSelfAt false)
  | .dty T => .dty T
termination_by structural d
/-- Erase the self type of every literal in argument position inside a member
list. -/
def ADms.eraseArgSelf {s : Sig} (ds : ADms s) : ADms s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.eraseArgSelf ds'.eraseArgSelf
termination_by structural ds
end

/-- Erase the self type of every literal in argument position. -/
def ATm.eraseArgSelf {s : Sig} (a : ATm s) : ATm s := a.eraseArgSelfAt false

mutual
/-- The program a Scala programmer writes: no self type, no result type, and
every parameter type written.  A parameter left to the written self type
takes the domain the self type declares at its position. -/
def ATm.scalaForm {s : Sig} (a : ATm s) : ATm s :=
  match a with
  | .var x => .var x
  | .obj o ds => .obj none (ds.scalaForm o)
  | .app t l u => .app t.scalaForm l u.scalaForm
  | .asc t T => .asc t.scalaForm T
termination_by structural a
/-- A member in the Scala form, given the conjunct the written self type has
at its position. -/
def ADm.scalaForm {s : Sig} (d : ADm s) (H : Option (Ty [] s)) : ADm s :=
  match d, H with
  | .dfun o1 _ t, some (.TFun _ S _) => .dfun (o1.or (some S)) none t.scalaForm
  | .dfun o1 _ t, _ => .dfun o1 none t.scalaForm
  | .dty T, _ => .dty T
termination_by structural d
/-- A member list in the Scala form, read in lockstep with the written self
type. -/
def ADms.scalaForm {s : Sig} (ds : ADms s) (T : Option (Ty [] s)) : ADms s :=
  match ds, T with
  | .dnil, _ => .dnil
  | .dcons d ds', some (.TAnd H TS) => .dcons (d.scalaForm (some H)) (ds'.scalaForm (some TS))
  | .dcons d ds', _ => .dcons (d.scalaForm none) (ds'.scalaForm none)
termination_by structural ds
end

mutual
/-- A term fills its `S` erasure. -/
theorem eraseSelf_fills {s : Sig} : (a : ATm s) → a.eraseSelf.fills a = true
  | .var _ => by simp [ATm.eraseSelf, ATm.fills]
  | .obj _ ds => by
      simp only [ATm.eraseSelf, ATm.fills, slotAgrees, eraseSelfDms_fills ds, Bool.and_self]
  | .app t _ u => by simp [ATm.eraseSelf, ATm.fills, eraseSelf_fills t, eraseSelf_fills u]
  | .asc t _ => by simp [ATm.eraseSelf, ATm.fills, eraseSelf_fills t]
/-- A member fills its `S` erasure. -/
theorem eraseSelfDm_fills {s : Sig} : (d : ADm s) → d.eraseSelf.fills d = true
  | .dfun _ _ t => by simp [ADm.eraseSelf, ADm.fills, eraseSelf_fills t]
  | .dty _ => by simp [ADm.eraseSelf, ADm.fills]
/-- A member list fills its `S` erasure. -/
theorem eraseSelfDms_fills {s : Sig} : (ds : ADms s) → ds.eraseSelf.fills ds = true
  | .dnil => rfl
  | .dcons d ds' => by
      simp only [ADms.eraseSelf, ADms.fills, eraseSelfDm_fills d, eraseSelfDms_fills ds',
        Bool.and_self]
end

mutual
/-- A term fills its `A` erasure, wherever it stands. -/
theorem eraseArgSelfAt_fills {s : Sig} :
    (arg : Bool) → (a : ATm s) → (a.eraseArgSelfAt arg).fills a = true
  | _, .var _ => by simp [ATm.eraseArgSelfAt, ATm.fills]
  | arg, .obj o ds => by
      have ho : slotAgrees (if arg = true then none else o) o = true := by
        cases arg
        · exact slotAgrees_refl o
        · rfl
      simp only [ATm.eraseArgSelfAt, ATm.fills, ho, eraseArgSelfDms_fills ds, Bool.and_self]
  | _, .app t _ u => by
      simp [ATm.eraseArgSelfAt, ATm.fills, eraseArgSelfAt_fills false t,
        eraseArgSelfAt_fills true u]
  | _, .asc t _ => by simp [ATm.eraseArgSelfAt, ATm.fills, eraseArgSelfAt_fills false t]
/-- A member fills its `A` erasure. -/
theorem eraseArgSelfDm_fills {s : Sig} : (d : ADm s) → d.eraseArgSelf.fills d = true
  | .dfun _ _ t => by simp [ADm.eraseArgSelf, ADm.fills, eraseArgSelfAt_fills false t]
  | .dty _ => by simp [ADm.eraseArgSelf, ADm.fills]
/-- A member list fills its `A` erasure. -/
theorem eraseArgSelfDms_fills {s : Sig} : (ds : ADms s) → ds.eraseArgSelf.fills ds = true
  | .dnil => rfl
  | .dcons d ds' => by
      simp only [ADms.eraseArgSelf, ADms.fills, eraseArgSelfDm_fills d,
        eraseArgSelfDms_fills ds', Bool.and_self]
end

/-- A term fills its `A` erasure. -/
theorem eraseArgSelf_fills {s : Sig} (a : ATm s) : a.eraseArgSelf.fills a = true :=
  eraseArgSelfAt_fills false a

/-! ## Sanity of the slots -/

/-- The typer cannot take a literal with a Curry style method and no self type. -/
example : (ATm.obj none (.dcons (.dfun none none (.var .here)) .dnil) : ATm []).landed
    = false := by
  decide

/-- It takes the same literal with its self type written. -/
example : (ATm.obj (some (.TAnd (.TFun 0 .TTop .TTop) .TTop))
    (.dcons (.dfun none none (.var .here)) .dnil) : ATm []).landed = true := by
  decide

/-- The fill writes the self type and fills the literal. -/
example : (ATm.obj none (.dcons (.dfun none none (.var .here)) .dnil) : ATm []).fills
    (.obj (some (.TAnd (.TFun 0 .TTop .TTop) .TTop))
      (.dcons (.dfun none none (.var .here)) .dnil)) = true := by
  decide

/-- A fill writes no method annotation. -/
example : (ATm.obj none (.dcons (.dfun none none (.var .here)) .dnil) : ATm []).fills
    (.obj none (.dcons (.dfun (some .TTop) none (.var .here)) .dnil)) = false := by
  decide

/-- A written self type is kept. -/
example : (ATm.obj (some .TTop) .dnil : ATm []).fills
    (.obj (some (.TAnd .TTop .TTop)) .dnil) = false := by
  decide

/-- `new { o ⇒ def f(x : ⊤) = o.f(x) }`: the body of `f` calls `f` on the
self. -/
example : (ATm.app (.var (.there .here)) 0 (.var .here) : ATm (([],x),x)).deps
    (.there .here) = ([0], false) := by
  decide

/-- A body that returns the self uses it bare. -/
example : (ATm.var (.there .here) : ATm (([],x),x)).deps (.there .here) = ([], true) := by
  decide

/-- A call on the self through an ascription depends on the label and uses the
self bare. -/
example : (ATm.app (.asc (.var (.there .here)) .TTop) 2 (.var .here) : ATm (([],x),x)).deps
    (.there .here) = ([2], true) := by
  decide

/-- A call on the self from a nested literal's method, under two more
binders. -/
example : (ATm.obj none (.dcons (.dfun (some .TTop) none
      (.app (.var (.there (.there (.there .here)))) 0 (.var .here))) .dnil)
      : ATm (([],x),x)).deps (.there .here) = ([0], false) := by
  decide

/-- A call on another variable is no dependency. -/
example : (ATm.app (.var .here) 0 (.var .here) : ATm (([],x),x)).deps (.there .here)
    = ([], false) := by
  decide

end Oopsla16Frontend
