import Coercions.Paths.DotMNF.Typing
import Coercions.Paths.FCdot.Context

namespace Paths

/-!
# Translation of types (Plan III §8.1, M3, and stage P2.1 of plan-5g)

Paths translate by shape, and types translate homomorphically on paths.
Declaration-shaped types become object types over a fresh self block.  A type
member `{A : S..T}` is the pair of propositions `⟦S⟧ ⊑ self∙A` and
`self∙A ⊑ ⟦T⟧`.  A field `{a : T}` is the presence of `a` together with
`self∙a ⊑ ⟦T⟧`.  A stable field `{val a : T}` adds the stable presence
`∋ᵛ a`.  A singleton `q.type` is the alias `≈ q`.  An intersection
concatenates.  A recursive type `μ(x. T)` binds its own self, identified with
the block of the object.  `⊤` is the empty object type, so every
declaration-shaped type, `⊤` included, is `μ (tel T)`.

The other shapes are `⊥`, a type selection `p.A`, a function type, and a `μ`
whose body is not declaration-shaped.  Each is read as the single self-bound
proposition `[⊑ ⟦B⟧]` (plan §13 item 9), so that `tel` is total and an
intersection may have arbitrary operands.  `Ty.isObj` is the shape test that
separates the two.  `⟦T⟧ = μ (tel T)` when it holds, and `tel T = [⊑ ⟦T⟧↑]`
when it does not.  A bound proposition never mentions the self, which is why
the body of a `μ` is still restricted to `Ty.Decl`.

Two telescope functions.  `tel T` reads a type over `s` as propositions about
a fresh self.  `telSelfAt self T` reads a type over `s` whose self is the
variable `self`, and `telSelf T` is `telSelfAt .here T`.  They agree on
weakened types (`tel_eq_telSelf_weaken`).

Every function of this module is structural (decision 31), so that the kernel
unfolds a translation and `decide +kernel` evaluates it.  For that,
`Ty.translate` spells out one level of `Ty.tel` at an object shape, and the
self of `telSelfAt` is an explicit variable.  `Ty.translate_isObj` states the
agreement with `tel`.

The block a literal's self binder carries reads the literal's definitions,
not only its declaration type (decision 30).  A field that holds a variable
gives a forwarding child whatever type it is declared at.  `Ty.blocks` and
its three helpers build it, and `Ctx.translate` stays a function of the
source context, since `Ctx.consSelf` carries the definitions.
-/

namespace FCdot

/-- Concatenation of witnesses (second appended after the first). -/
def Witnesses.append : Witnesses s → Witnesses s → Witnesses s
  | W, .nil => W
  | W, .cons W' ℓ T => .cons (W.append W') ℓ T

def Witnesses.length : Witnesses s → Nat
  | .nil => 0
  | .cons W _ _ => W.length + 1

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- Paths translate by shape. -/
def Path.translate : Path s → FCdot.Path s
  | .var x => .var x
  | .sel p a => .sel p.translate a

/-- The types whose translation is the object type of their own telescope,
`⟦T⟧ = μ (tel T)` (`Ty.translate_isObj`).  For the others `tel T` is the
single self-bound `[⊑ ⟦T⟧↑]` (`Ty.tel_of_not_isObj`), and the two differ.
An intersection always passes, whatever its operands, while a `μ` passes
exactly when its body is declaration-shaped.  A stable field and a singleton
pass. -/
def Ty.isObj : Ty s → Bool
  | .bot => false
  | .sel _ _ => false
  | .all _ _ => false
  | .mu T => T.isDecl
  | .top => true
  | .typ _ _ _ => true
  | .fld _ _ => true
  | .vfld _ _ => true
  | .sngl _ => true
  | .and _ _ => true

mutual

/-- `⟦T⟧`.  An object shape spells out one level of `Ty.tel`, so that the
recursion is structural (`Ty.translate_isObj` states the agreement). -/
def Ty.translate : Ty s → FCdot.Ty s
  | .top => FCdot.Ty.obj .nil
  | .bot => .bot
  | .sel p A => .sel p.translate A
  | .all S T => .pi (Ty.translate S) (Ty.translate T)
  | .typ A S T =>
      .obj (.cons (.cons .nil (.le (Ty.translate S).weaken (.sel (.var .here) A)))
        (.le (.sel (.var .here) A) (Ty.translate T).weaken))
  | .fld a T =>
      .obj (.cons (.cons .nil (.has a)) (.le (.sel (.var .here) a) (Ty.translate T).weaken))
  | .vfld a T =>
      .obj (.cons (.cons (.cons .nil (.has a)) (.hasVal a))
        (.le (.sel (.var .here) a) (Ty.translate T).weaken))
  | .sngl q => .obj (.cons .nil (.alias q.translate.weaken))
  | .and S T => .obj ((Ty.tel S).append (Ty.tel T))
  | .mu T => .obj (Ty.telSelfAt .here T)

/-- A type over `s` as propositions about a fresh self block.  A shape that
is not an object type contributes the single self-bound `⊑ ⟦T⟧↑`.  The bodies
of those bounds are spelled out rather than written `Ty.translate _`, because
`Ty.translate` would not be applied to a smaller argument there. -/
def Ty.tel : Ty s → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translate S).weaken (.sel (.var .here) A)))
        (.le (.sel (.var .here) A) (Ty.translate T).weaken)
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel (.var .here) a) (Ty.translate T).weaken)
  | .vfld a T =>
      .cons (.cons (.cons .nil (.has a)) (.hasVal a))
        (.le (.sel (.var .here) a) (Ty.translate T).weaken)
  | .sngl q => .cons .nil (.alias q.translate.weaken)
  | .and S T => (Ty.tel S).append (Ty.tel T)
  | .mu T =>
      if T.isDecl then Ty.telSelfAt .here T
      else .cons .nil (.bnd (FCdot.Ty.obj (Ty.telSelfAt .here T)).weaken)
  | .top => .nil
  | .bot => .cons .nil (.bnd (FCdot.Ty.bot).weaken)
  | .sel p A => .cons .nil (.bnd (FCdot.Ty.sel p.translate A).weaken)
  | .all S T => .cons .nil (.bnd (FCdot.Ty.pi (Ty.translate S) (Ty.translate T)).weaken)

/-- A type whose self is the variable `self`, as propositions about it.  The
self-bound of a non-object shape is not weakened here and may therefore
mention the self.  `Wf.mu` keeps such bodies out of well-formed types, but the
function is total. -/
def Ty.telSelfAt (self : BVar s .var) : Ty s → FCdot.Telescope s
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translate S) (.sel (.var self) A)))
        (.le (.sel (.var self) A) (Ty.translate T))
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel (.var self) a) (Ty.translate T))
  | .vfld a T =>
      .cons (.cons (.cons .nil (.has a)) (.hasVal a)) (.le (.sel (.var self) a) (Ty.translate T))
  | .sngl q => .cons .nil (.alias q.translate)
  | .and S T => (Ty.telSelfAt self S).append (Ty.telSelfAt self T)
  | .mu T =>
      if T.isDecl then (Ty.telSelfAt .here T).substVar self
      else .cons .nil (.bnd (FCdot.Ty.obj (Ty.telSelfAt .here T)))
  | .top => .nil
  | .bot => .cons .nil (.bnd FCdot.Ty.bot)
  | .sel p A => .cons .nil (.bnd (FCdot.Ty.sel p.translate A))
  | .all S T => .cons .nil (.bnd (FCdot.Ty.pi (Ty.translate S) (Ty.translate T)))

end

/-- A type over `(s,x)` whose self is the innermost binder, as propositions
about that binder.  The vanilla function, now `Ty.telSelfAt` at `.here`. -/
def Ty.telSelf (T : Ty (s,x)) : FCdot.Telescope (s,x) := T.telSelfAt .here

/-! ## The two shapes of a telescope -/

/-- An object shape translates to the object type of its own telescope. -/
theorem Ty.translate_isObj {s : Sig} : ∀ {T : Ty s}, T.isObj = true → T.translate = .obj T.tel
  | .top, _ => by simp [Ty.translate, Ty.tel]
  | .typ _ _ _, _ => by simp [Ty.translate, Ty.tel]
  | .fld _ _, _ => by simp [Ty.translate, Ty.tel]
  | .vfld _ _, _ => by simp [Ty.translate, Ty.tel]
  | .sngl _, _ => by simp [Ty.translate, Ty.tel]
  | .and _ _, _ => by simp [Ty.translate, Ty.tel]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.tel, h]

/-- Every other shape is read as the single self-bound `⊑ ⟦T⟧↑`. -/
theorem Ty.tel_of_not_isObj {s : Sig} :
    ∀ {T : Ty s}, T.isObj = false → T.tel = .cons .nil (.bnd T.translate.weaken)
  | .bot, _ => by simp [Ty.translate, Ty.tel]
  | .sel _ _, _ => by simp [Ty.translate, Ty.tel]
  | .all _ _, _ => by simp [Ty.translate, Ty.tel]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.tel, h]

/-- The same with the self already bound: there the bound is not weakened. -/
theorem Ty.telSelf_of_not_isObj {s : Sig} :
    ∀ {T : Ty (s,x)}, T.isObj = false → T.telSelf = .cons .nil (.bnd T.translate)
  | .bot, _ => by simp [Ty.translate, Ty.telSelf, Ty.telSelfAt]
  | .sel _ _, _ => by simp [Ty.translate, Ty.telSelf, Ty.telSelfAt]
  | .all _ _, _ => by simp [Ty.translate, Ty.telSelf, Ty.telSelfAt]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.telSelf, Ty.telSelfAt, h]

/-! ## The literal's side -/

/-- The witnesses of a literal, read off its declaration type: the exact
bound of each type member and the declared type of each field, a stable field
included.  Stated at any scope, so that the recursion is structural. -/
def Ty.witnesses : Ty s → FCdot.Witnesses s
  | .typ A S _ => .cons .nil A S.translate
  | .fld a T => .cons .nil a T.translate
  | .vfld a T => .cons .nil a T.translate
  | .and S T => S.witnesses.append T.witnesses
  | _ => .nil

/-- The field labels of a declaration type, newest (outermost) first, a
stable field included.  `FCdot.Fields.labels` lists the outermost field first
and `FCdot.Fields.get?` lets the outermost field win.  In DOT the right
conjunct of an intersection shadows.  So the right conjunct's fields are the
outermost ones of the translated literal and come first here.  This is the
convention of `Ty.witnesses`, where `FCdot.Witnesses.append` puts the second
argument's witnesses outermost and `Witnesses.get` gives them priority. -/
def Ty.fieldLabels : Ty s → List Label
  | .fld a _ => [a]
  | .vfld a _ => [a]
  | .and S T => T.fieldLabels ++ S.fieldLabels
  | _ => []

/-- The stable field labels of a declaration type, right conjunct first, as
`Ty.fieldLabels`.  It is `[]` on a type with no `vfld`. -/
def Ty.valLabels : Ty s → List Label
  | .vfld a _ => [a]
  | .and S T => T.valLabels ++ S.valLabels
  | _ => []

/-- The precise target type of a literal whose declaration type is `T`. -/
def Ty.literalTy (T : Ty (s,x)) : FCdot.Ty s :=
  .obj (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels T.valLabels)

/-! ## The block of a literal (P2.2)

`Defs.childrenOver` mirrors `FCdot.Fields.children` on the translated fields.
The translation of `d₁ ∧ d₂` puts the fields of `d₂` outermost, so `d₂` is
processed over the children of `d₁`.  A field that gives no child drops its
label, as `Fields.children` does.  A field that holds a variable gives the
forwarding `.fwd (.var y)`, whatever type it is declared at.  A `trmObj`
field gives the inner literal's block written at `p.a`.  A `trm` field whose
body is a literal gives none, by decision 26. -/

mutual

/-- The children the fields of `d`, declared at `T`, add to `base` at the
block of `p`. -/
def Defs.childrenOver : Defs s → Ty s → FCdot.Children s → FCdot.Path s → FCdot.Children s
  | .typ _ _, _, base, _ => base
  | .trm a t, T, base, p =>
      match Tm.childOf t T (.sel p a) with
      | some b => .cons base a b
      | none => base.dropLabel a
  | .and d₁ d₂, .and T₁ T₂, base, p =>
      Defs.childrenOver d₂ T₂ (Defs.childrenOver d₁ T₁ base p) p
  | .and _ _, _, base, _ => base

/-- The child a field body declared at `T` gives at `p`.  A variable body
gives a forwarding, whatever `T` is.  A literal body declared stable gives its
block. -/
def Tm.childOf : Tm s → Ty s → FCdot.Path s → Option (FCdot.Block s)
  | .val v, T, p => Value.childOf v T p
  | .path y, _, _ => some (.fwd (.var y))
  | .app _ _, _, _ => none
  | .proj _ _, _, _ => none
  | .let _ _, _, _ => none

/-- The child a value declared at `T` gives at `p`: the block of an object
literal declared at a stable field, and nothing otherwise. -/
def Value.childOf : Value s → Ty s → FCdot.Path s → Option (FCdot.Block s)
  | .obj d', .vfld _ (.mu T'), p =>
      some ((FCdot.Block.obj T'.witnesses T'.fieldLabels T'.valLabels
        (Defs.childrenOver d' T' .nil (.var .here))).substPath p)
  | _, _, _ => none

end

/-- The block a literal's definitions `d` and declaration type `T` give its
self binder.  It reads the definitions, not only the type (decision 30).  The
block at a path `p` is `Block.substPath` of this one. -/
def Ty.blocks (T : Ty (s,x)) (d : Defs (s,x)) : FCdot.Block (s,x) :=
  .obj T.witnesses T.fieldLabels T.valLabels (Defs.childrenOver d T .nil (.var .here))

/-- Contexts translate binder by binder.  An ordinary binder is opaque at its
translated type.  A literal's self binder is transparent at the literal's
precise type, with the block its definitions give. -/
def Ctx.translate : Ctx s → FCdot.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.translate (.opaque T.translate)
  | .consSelf Γ d T => .cons Γ.translate (.transparent T.literalTy (T.blocks d))

end DotMNF

end Paths
