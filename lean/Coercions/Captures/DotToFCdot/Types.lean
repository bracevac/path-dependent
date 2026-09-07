import Coercions.Captures.DotMNF.Typing
import Coercions.Captures.FCdot.Context

namespace Captures

/-!
# Translation of types (Plan III §8.1, M3)

Types translate homomorphically.  Declaration-shaped types become object
types over a fresh self block: a type member `{A : S..T}` is the pair of
propositions `⟦S⟧ ⊑ self∙A`, `self∙A ⊑ ⟦T⟧`; a field `{a : T}` is presence of
`a` together with `self∙a ⊑ ⟦T⟧`; an intersection concatenates; a recursive
type `μ(x. T)` binds its own self, identified with the block of the object.
`⊤` is the empty object type, so every declaration-shaped type, `⊤`
included, is `μ (tel T)`.

Everything else — `⊥`, a type selection, a function type, and a `μ` whose
body is not declaration-shaped — is read as the *single self-bound
proposition* `[⊑ ⟦B⟧]` (plan §13 item 9), so that `tel` is total and an
intersection may have arbitrary operands.  `Ty.isObj` is the shape test that
separates the two: `⟦T⟧ = μ (tel T)` when it holds, and `tel T = [⊑ ⟦T⟧↑]`
when it does not.  A bound proposition never mentions the self, which is why
the body of a `μ` is still restricted to `Ty.Decl`.

Two telescope functions: `tel T` reads a type over `s` as propositions about
a fresh self, `telSelf T` reads a type over `(s,x)` whose self is already the
innermost binder.  They agree on weakened types (`tel_eq_telSelf_weaken`).

A target type is a shape with a capture set, so the recursion that mirrors
the source type is `Ty.translateShape`, and `⟦T⟧ = Ty.translate T` is that
shape at the empty capture set: `Ty.translate T = T.translateShape ^ []`
(stage A0 carries capture sets and never reads them, and every type the
translation produces is pure).  Positions that hold a shape — a proposition,
a witness, a self-bound — take `translateShape` directly; positions that
hold a type — the two sides of an arrow, the type of an atom or a term —
take `translate`.
-/

namespace FCdot

/-- Concatenation of witnesses (second appended after the first). -/
def Witnesses.append : Witnesses s → Witnesses s → Witnesses s
  | W, .nil => W
  | W, .cons W' ℓ T => .cons (W.append W') ℓ T

def Witnesses.length : Witnesses s → Nat
  | .nil => 0
  | .cons W _ _ => W.length + 1

/-- Length of a capture-witness list: the number of capture-definition
entries the literal's precise telescope carries between its type block and
its presence block (stage A1). -/
def CapWitnesses.length : CapWitnesses s → Nat
  | .nil => 0
  | .cons W _ _ => W.length + 1

/-- A shape inclusion read as a type inclusion at the empty capture set.
Every coercion the translation builds goes through this: stage A0 assigns
the empty capture set to every translated type, so the capture half of a
translated inclusion is always `refl []`. -/
def ShapeCo.pure (e : ShapeCo s) : LeCo s := .capt e (.refl [])

@[simp] theorem ShapeCo.pure_rename {s1 s2 : Sig} (e : ShapeCo s1) (ρ : Rename s1 s2) :
    (e.pure).rename ρ = (e.rename ρ).pure := rfl

@[simp] theorem Ty.pure_rename {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2) :
    (Ty.pure S).rename ρ = Ty.pure (S.rename ρ) := rfl

@[simp] theorem Ty.pure_weaken {s : Sig} {k : Kind} (S : Shape s) :
    ((Ty.pure S)↑ : Ty (s,,k)) = Ty.pure (S↑) := rfl

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- The types whose translation is the object type of their own telescope,
`⟦T⟧ = μ (tel T)` (`Ty.translate_isObj`).  For the others `tel T` is the
single self-bound `[⊑ ⟦T⟧↑]` (`Ty.tel_of_not_isObj`), and the two differ.
An intersection always passes, whatever its operands, while a `μ` passes
exactly when its body is declaration-shaped. -/
def Ty.isObj : Ty s → Bool
  | .bot => false
  | .sel _ _ => false
  | .all _ _ => false
  | .mu T => T.isDecl
  | .top => true
  | .typ _ _ _ => true
  | .fld _ _ => true
  | .and _ _ => true

mutual

/-- The shape of `⟦T⟧`: the vanilla translation, whose target sort is what
the vanilla line called a type and what is now a shape. -/
def Ty.translateShape : Ty s → FCdot.Shape s
  | .top => FCdot.Shape.obj .nil
  | .bot => .bot
  | .sel (.var x) A => .sel x A
  | .all S T => .pi (FCdot.Ty.pure (Ty.translateShape S)) (FCdot.Ty.pure (Ty.translateShape T))
  | .typ A S T => .obj (Ty.tel (.typ A S T))
  | .fld a T => .obj (Ty.tel (.fld a T))
  | .and S T => .obj (Ty.tel (.and S T))
  | .mu T => .obj (Ty.telSelf T)

/-- A type over `s` as propositions about a fresh self block.  A shape that
is not an object type contributes the single self-bound `⊑ ⟦T⟧↑`; the bodies
of those bounds are spelled out rather than written `Ty.translate _`, because
`Ty.translate` would not be applied to a smaller argument there. -/
def Ty.tel : Ty s → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translateShape S).weaken (.sel .here A)))
        (.le (.sel .here A) (Ty.translateShape T).weaken)
  | .fld a T =>
      .cons
        (.cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translateShape T).weaken))
        (.leC [FCdot.CapAtom.name .here a] [])
  | .and S T => (Ty.tel S).append (Ty.tel T)
  | .mu T =>
      if T.isDecl then Ty.telSelf T
      else .cons .nil (.bnd (FCdot.Shape.obj (Ty.telSelf T)).weaken)
  | .top => .nil
  | .bot => .cons .nil (.bnd (FCdot.Shape.bot).weaken)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Shape.sel y A).weaken)
  | .all S T =>
      .cons .nil
        (.bnd (FCdot.Shape.pi (FCdot.Ty.pure (Ty.translateShape S))
          (FCdot.Ty.pure (Ty.translateShape T))).weaken)

/-- A type over `(s,x)` whose self is the innermost binder, as propositions
about that binder.  The self-bound of a non-object shape is *not* weakened
here and may therefore mention the self; `Wf.mu` keeps such bodies out of
well-formed types, but the function is total. -/
def Ty.telSelf : Ty (s,x) → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translateShape S) (.sel .here A)))
        (.le (.sel .here A) (Ty.translateShape T))
  | .fld a T =>
      .cons (.cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translateShape T)))
        (.leC [FCdot.CapAtom.name .here a] [])
  | .and S T => (Ty.telSelf S).append (Ty.telSelf T)
  | .mu T =>
      if T.isDecl then (Ty.telSelf T).substVar .here
      else .cons .nil (.bnd (FCdot.Shape.obj (Ty.telSelf T)))
  | .top => .nil
  | .bot => .cons .nil (.bnd FCdot.Shape.bot)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Shape.sel y A))
  | .all S T =>
      .cons .nil
        (.bnd (FCdot.Shape.pi (FCdot.Ty.pure (Ty.translateShape S))
          (FCdot.Ty.pure (Ty.translateShape T))))

end

/-- `⟦T⟧`: the translated shape at the empty capture set. -/
def Ty.translate (T : Ty s) : FCdot.Ty s := FCdot.Ty.pure T.translateShape

@[simp] theorem Ty.translate_capt {s : Sig} (T : Ty s) :
    T.translate = FCdot.Ty.capt [] T.translateShape := rfl

@[simp] theorem Ty.translate_shape {s : Sig} (T : Ty s) :
    T.translate.shape = T.translateShape := rfl

/-! ## The two shapes of a telescope -/

/-- An object shape translates to the object shape of its own telescope. -/
theorem Ty.translateShape_isObj {s : Sig} :
    ∀ {T : Ty s}, T.isObj = true → T.translateShape = .obj T.tel
  | .top, _ => by simp [Ty.translateShape, Ty.tel]
  | .typ _ _ _, _ => by simp [Ty.translateShape]
  | .fld _ _, _ => by simp [Ty.translateShape]
  | .and _ _, _ => by simp [Ty.translateShape]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translateShape, Ty.tel, h]

/-- The same one layer up, at the empty capture set. -/
theorem Ty.translate_isObj {s : Sig} {T : Ty s} (h : T.isObj = true) :
    T.translate = FCdot.Ty.capt [] (.obj T.tel) := by
  rw [Ty.translate, Ty.translateShape_isObj h]

/-- Every other shape is read as the single self-bound `⊑ ⟦T⟧↑`. -/
theorem Ty.tel_of_not_isObj {s : Sig} :
    ∀ {T : Ty s}, T.isObj = false → T.tel = .cons .nil (.bnd T.translateShape.weaken)
  | .bot, _ => by simp [Ty.translateShape, Ty.tel]
  | .sel (.var _) _, _ => by simp [Ty.translateShape, Ty.tel]
  | .all _ _, _ => by simp [Ty.translateShape, Ty.tel]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translateShape, Ty.tel, h]

/-- The same with the self already bound: there the bound is not weakened. -/
theorem Ty.telSelf_of_not_isObj {s : Sig} :
    ∀ {T : Ty (s,x)}, T.isObj = false → T.telSelf = .cons .nil (.bnd T.translateShape)
  | .bot, _ => by simp [Ty.translateShape, Ty.telSelf]
  | .sel (.var _) _, _ => by simp [Ty.translateShape, Ty.telSelf]
  | .all _ _, _ => by simp [Ty.translateShape, Ty.telSelf]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translateShape, Ty.telSelf, h]

/-- The witnesses of a literal, read off its declaration type: the exact
bound of each type member and the declared type of each field. -/
def Ty.witnesses : Ty (s,x) → FCdot.Witnesses (s,x)
  | .typ A S _ => .cons .nil A S.translateShape
  | .fld a T => .cons .nil a T.translateShape
  | .and S T => S.witnesses.append T.witnesses
  | _ => .nil

/-- The field labels of a declaration type, newest (outermost) first.
`FCdot.Fields.labels` lists the outermost field first and `FCdot.Fields.get?`
lets the outermost field win, and in DOT the *right* conjunct of an
intersection shadows; so the right conjunct's fields are the outermost ones
of the translated literal and come first here.  This is the same convention
as `Ty.witnesses`, where `FCdot.Witnesses.append` puts the second argument's
witnesses outermost and `Witnesses.get` gives them priority. -/
def Ty.fieldLabels : Ty s → List Label
  | .fld a _ => [a]
  | .and S T => T.fieldLabels ++ S.fieldLabels
  | _ => []

/-- One capture witness per listed label, all of them the empty set,
appended to a capture-witness list.  The first label of the list is consed
first, so it sits at the lowest position of the capture block, which is the
order `Telescope.hasEntries` gives the presences.  (Stage A2.) -/
def _root_.Captures.FCdot.CapWitnesses.ofLabels :
    FCdot.CapWitnesses s → List Label → FCdot.CapWitnesses s
  | Wc, [] => Wc
  | Wc, ℓ :: ls => FCdot.CapWitnesses.ofLabels (.cons Wc ℓ []) ls

theorem _root_.Captures.FCdot.CapWitnesses.ofLabels_length {s : Sig} :
    ∀ (Wc : FCdot.CapWitnesses s) (ls : List Label),
      (FCdot.CapWitnesses.ofLabels Wc ls).length = Wc.length + ls.length
  | _, [] => by simp [FCdot.CapWitnesses.ofLabels]
  | Wc, ℓ :: ls => by
      rw [FCdot.CapWitnesses.ofLabels, FCdot.CapWitnesses.ofLabels_length (Wc.cons ℓ []) ls]
      simp [FCdot.CapWitnesses.length]
      omega

theorem _root_.Captures.FCdot.CapWitnesses.ofLabels_rename {s s' : Sig} (ρ : Rename s s') :
    ∀ (Wc : FCdot.CapWitnesses s) (ls : List Label),
      (FCdot.CapWitnesses.ofLabels Wc ls).rename ρ
        = FCdot.CapWitnesses.ofLabels (Wc.rename ρ) ls
  | _, [] => rfl
  | Wc, ℓ :: ls => by
      rw [FCdot.CapWitnesses.ofLabels, FCdot.CapWitnesses.ofLabels_rename ρ (Wc.cons ℓ []) ls,
        FCdot.CapWitnesses.ofLabels]
      rfl

/-- Every capture witness of `ofLabels` is empty, so its lookup at any label
is empty as soon as the base list has that property. -/
theorem _root_.Captures.FCdot.CapWitnesses.ofLabels_get {s : Sig} :
    ∀ (Wc : FCdot.CapWitnesses s), (∀ m, Wc.get m = []) → ∀ (ls : List Label) (ℓ : Label),
      (FCdot.CapWitnesses.ofLabels Wc ls).get ℓ = []
  | Wc, hWc, [], ℓ => hWc ℓ
  | Wc, hWc, ℓ' :: ls, ℓ => by
      refine FCdot.CapWitnesses.ofLabels_get (Wc.cons ℓ' []) (fun m => ?_) ls ℓ
      by_cases hm : m = ℓ'
      · simp [FCdot.CapWitnesses.get, hm]
      · simp [FCdot.CapWitnesses.get, hm]; exact hWc m

/-- The capture witnesses of a translated literal: one empty capture set per
field label.  The source of this stage has no capture members, so a field
holds a value of a pure type and its capture name is the empty set; that
declaration is what a `member` in the capture sort reads at a projection
(stage A2.6).  The order is `Ty.fieldLabels`, so the capture entry of a
label sits at the same offset inside the capture block as its presence does
inside the presence block. -/
def Ty.capWitnesses (T : Ty (s,x)) : FCdot.CapWitnesses (s,x) :=
  FCdot.CapWitnesses.ofLabels .nil T.fieldLabels

@[simp] theorem Ty.capWitnesses_length {s : Sig} (T : Ty (s,x)) :
    T.capWitnesses.length = T.fieldLabels.length := by
  rw [Ty.capWitnesses, FCdot.CapWitnesses.ofLabels_length]
  simp [FCdot.CapWitnesses.length]

@[simp] theorem Ty.capWitnesses_get {s : Sig} (T : Ty (s,x)) (ℓ : Label) :
    T.capWitnesses.get ℓ = [] :=
  FCdot.CapWitnesses.ofLabels_get .nil (fun _ => rfl) _ _


/-- The precise target type of a literal whose declaration type is `T`: its
type definitions, then its (empty) capture definitions, then its fields. -/
def Ty.literalTy (T : Ty (s,x)) : FCdot.Ty s :=
  FCdot.Ty.pure
    (.obj (FCdot.Telescope.ofLiteral T.witnesses T.capWitnesses T.fieldLabels))

@[simp] theorem Ty.literalTy_shape {s : Sig} (T : Ty (s,x)) :
    T.literalTy.shape =
      FCdot.Shape.obj (FCdot.Telescope.ofLiteral T.witnesses T.capWitnesses T.fieldLabels) :=
  rfl

/-- Contexts translate binder by binder: an ordinary binder is opaque at its
translated type; a literal's self binder is transparent at the literal's
precise type. -/
def Ctx.translate : Ctx s → FCdot.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.translate (.opaque T.translate)
  | .consSelf Γ _ T =>
      .cons Γ.translate (.transparent T.literalTy T.witnesses T.capWitnesses T.fieldLabels)

end DotMNF

end Captures
