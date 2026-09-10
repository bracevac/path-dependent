import Coercions.Captures.DotMNF.Typing
import Coercions.Captures.FCdot.Context

namespace Captures

/-!
# Translation of types (Plan III §8.1, M3; stage A3a)

Types translate homomorphically.  Declaration-shaped shapes become object
types over a fresh self block: a type member `{A : S..T}` is the pair of
propositions `⟦S⟧ ⊑ self∙A`, `self∙A ⊑ ⟦T⟧`; a field `{a : S ^ C}` is
presence of `a`, `self∙a ⊑ ⟦S⟧` and `{self∙a} ⊑ᶜ ⟦C⟧`; a capture member
`{A : c₁..c₂}` is the pair of inclusions `⟦c₁⟧ ⊑ᶜ {self∙A}`,
`{self∙A} ⊑ᶜ ⟦c₂⟧`; an intersection concatenates; a recursive shape
`μ(x. S)` binds its own self, identified with the block of the object.
`⊤` is the empty object type, so every declaration-shaped shape, `⊤`
included, is `μ (tel S)`.

Everything else, that is `⊥`, a type selection, a function shape, a box, and
a `μ` whose body is not declaration-shaped, is read as the *single self-bound
proposition* `[⊑ ⟦B⟧]` (plan §13 item 9), so that `tel` is total and an
intersection may have arbitrary operands.  `Shape.isObj` is the shape test
that separates the two: `⟦S⟧ = μ (tel S)` when it holds, and
`tel S = [⊑ ⟦S⟧↑]` when it does not.  A bound proposition never mentions the
self, which is why the body of a `μ` is still restricted to `Shape.Decl`.

Two telescope functions: `tel S` reads a shape over `s` as propositions about
a fresh self, `telSelf S` reads a shape over `(s,x)` whose self is already
the innermost binder.  They agree on weakened shapes
(`tel_eq_telSelf_weaken`).

A source type is a shape with a capture set, and so is a target type, so the
translation splits in the same way: `Shape.translate` is the vanilla
recursion, whose target sort is now the target's shape sort;
`CaptureSet.translate` maps capture atoms pointwise, the source's `sel x C`
to the target's name `x∙C`; and `⟦S ^ C⟧ = ⟦S⟧ ^ ⟦C⟧`.  Positions that hold
a shape, a proposition, a witness or a self-bound take `Shape.translate`;
positions that hold a type, the two sides of an arrow, the boxed type, the
type of an atom or a term, take `Ty.translate`.
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

/-- Concatenation of capture witnesses (second appended after the first),
the twin of `Witnesses.append`.  Stage A3a: a declaration shape now has
capture witnesses of its own, one per field and one per capture member, so
they are collected by the same structural recursion as the type
witnesses. -/
def CapWitnesses.append : CapWitnesses s → CapWitnesses s → CapWitnesses s
  | W, .nil => W
  | W, .cons W' ℓ C => .cons (W.append W') ℓ C

/-- A shape inclusion read as a type inclusion at a fixed capture set: the
two types have the same capture set and the capture half is `refl`. -/
def ShapeCo.atC (e : ShapeCo s) (C : CaptureSet s) : LeCo s := .capt e (.refl C)

/-- A shape inclusion read as a type inclusion at the empty capture set. -/
def ShapeCo.pure (e : ShapeCo s) : LeCo s := e.atC []

@[simp] theorem ShapeCo.atC_rename {s1 s2 : Sig} (e : ShapeCo s1) (C : CaptureSet s1)
    (ρ : Rename s1 s2) : (e.atC C).rename ρ = (e.rename ρ).atC (C.rename ρ) := rfl

@[simp] theorem ShapeCo.pure_rename {s1 s2 : Sig} (e : ShapeCo s1) (ρ : Rename s1 s2) :
    (e.pure).rename ρ = (e.rename ρ).pure := rfl

@[simp] theorem Ty.pure_rename {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2) :
    (Ty.pure S).rename ρ = Ty.pure (S.rename ρ) := rfl

@[simp] theorem Ty.pure_weaken {s : Sig} {k : Kind} (S : Shape s) :
    ((Ty.pure S)↑ : Ty (s,,k)) = Ty.pure (S↑) := rfl

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Capture sets

A source capture atom is a term binder, a capture binder, the capture member
of a term binder, or `any`; the target has the first three atoms, with `name`
for what the source calls `sel`, and no atom for `any`.  So `⟦C⟧` maps `C`
atom by atom and drops every `any` (stage A3b).  An unexpanded `any` is thus
read by the target as nothing at all, which is sound because the source
gives it no power: no rule mentions it.  The reading a program intends is
the one `CaptureSet.expand` puts in place before typing. -/

/-- `⟦a⟧` on capture atoms: the three variable forms have a target atom and
`any` has none. -/
def CapAtom.translate? : CapAtom s → Option (FCdot.CapAtom s)
  | .var x => some (.var x)
  | .cvar κ => some (.cvar κ)
  | .sel x A => some (.name x A)
  | .any => none

/-- `⟦C⟧` on capture sets: atom by atom, dropping `any`. -/
def CaptureSet.translate (C : CaptureSet s) : FCdot.CaptureSet s :=
  C.filterMap CapAtom.translate?

@[simp] theorem CaptureSet.translate_nil {s : Sig} :
    CaptureSet.translate ([] : CaptureSet s) = [] := rfl

@[simp] theorem CaptureSet.translate_cons_var {s : Sig} (x : BVar s .var) (C : CaptureSet s) :
    CaptureSet.translate (CapAtom.var x :: C) = .var x :: C.translate := rfl

@[simp] theorem CaptureSet.translate_cons_cvar {s : Sig} (κ : BVar s .cap) (C : CaptureSet s) :
    CaptureSet.translate (CapAtom.cvar κ :: C) = .cvar κ :: C.translate := rfl

@[simp] theorem CaptureSet.translate_cons_sel {s : Sig} (x : BVar s .var) (A : Label)
    (C : CaptureSet s) :
    CaptureSet.translate (CapAtom.sel x A :: C) = .name x A :: C.translate := rfl

@[simp] theorem CaptureSet.translate_cons_any {s : Sig} (C : CaptureSet s) :
    CaptureSet.translate (CapAtom.any :: C) = C.translate := rfl

/-- The A3a `translate_cons`, at an atom that has a target atom: the head is
translated and the tail follows. -/
theorem CaptureSet.translate_cons {s : Sig} {a : CapAtom s} {b : FCdot.CapAtom s}
    (h : a.translate? = some b) (C : CaptureSet s) :
    CaptureSet.translate (a :: C) = b :: C.translate := by
  simp [CaptureSet.translate, h]

@[simp] theorem CaptureSet.translate_append {s : Sig} (C D : CaptureSet s) :
    (C ++ D).translate = C.translate ++ D.translate := by
  simp [CaptureSet.translate]

@[simp] theorem CaptureSet.translate_union {s : Sig} (C D : CaptureSet s) :
    (C ∪ D).translate = C.translate ∪ D.translate := by
  simp [CaptureSet.translate]

/-- A syntactic inclusion is preserved by the translation: it is an atom by
atom map of lists, and the atoms it drops are dropped on both sides. -/
theorem CaptureSet.Subset.translate {s : Sig} {C D : CaptureSet s} (h : C.Subset D) :
    FCdot.CaptureSet.Subset C.translate D.translate := by
  intro b hb
  rw [CaptureSet.translate, List.mem_filterMap] at hb
  obtain ⟨a, ha, hb⟩ := hb
  rw [CaptureSet.translate, List.mem_filterMap]
  exact ⟨a, h a ha, hb⟩

theorem CapAtom.translate_rename {s s' : Sig} :
    ∀ (a : CapAtom s) (ρ : Rename s s'),
      (a.rename ρ).translate? = (a.translate?).map (fun b => b.rename ρ)
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .sel _ _, _ => rfl
  | .any, _ => rfl

@[simp] theorem CaptureSet.translate_rename {s s' : Sig} (C : CaptureSet s) (ρ : Rename s s') :
    (C.rename ρ).translate = C.translate.rename ρ := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      cases a <;>
        simp only [DotMNF.CaptureSet.rename_cons, CapAtom.rename,
          CaptureSet.translate_cons_var, CaptureSet.translate_cons_cvar,
          CaptureSet.translate_cons_sel, CaptureSet.translate_cons_any,
          FCdot.CaptureSet.rename, List.map_cons, ih] <;>
        rfl

@[simp] theorem CaptureSet.translate_weaken {s : Sig} {k : Kind} (C : CaptureSet s) :
    (C.weaken (k := k)).translate = FCdot.CaptureSet.weaken (k := k) C.translate :=
  CaptureSet.translate_rename C FCdot.Rename.succ

@[simp] theorem CaptureSet.translate_substVar {s : Sig} {k : Kind} (C : CaptureSet (s,,k))
    (y : BVar s k) :
    (C.substVar y).translate = FCdot.CaptureSet.substVar C.translate y :=
  CaptureSet.translate_rename C (FCdot.Rename.subst y)

/-! ## Shapes -/

/-- The shapes whose translation is the object type of their own telescope,
`⟦S⟧ = μ (tel S)` (`Shape.translate_isObj`).  For the others `tel S` is the
single self-bound `[⊑ ⟦S⟧↑]` (`Shape.tel_of_not_isObj`), and the two differ.
An intersection always passes, whatever its operands, while a `μ` passes
exactly when its body is declaration-shaped.  A capture member passes, a box
does not. -/
def Shape.isObj : Shape s → Bool
  | .bot => false
  | .sel _ _ => false
  | .all _ _ => false
  | .box _ => false
  | .mu S => S.isDecl
  | .top => true
  | .typ _ _ _ => true
  | .fld _ _ => true
  | .cap _ _ _ => true
  | .and _ _ => true

mutual

/-- `⟦S⟧` on shapes: the vanilla translation, whose source and target sorts
are what the vanilla line called types and are now shapes. -/
def Shape.translate : Shape s → FCdot.Shape s
  | .top => FCdot.Shape.obj .nil
  | .bot => .bot
  | .sel (.var x) A => .sel x A
  | .all (.capt C1 S1) (.capt C2 S2) =>
      .pi (.capt C1.translate S1.translate) (.capt C2.translate S2.translate)
  | .box (.capt C S) => .box (.capt C.translate S.translate)
  | .typ A S T => .obj (Shape.tel (.typ A S T))
  | .fld a T => .obj (Shape.tel (.fld a T))
  | .cap A c1 c2 => .obj (Shape.tel (.cap A c1 c2))
  | .and S T => .obj (Shape.tel (.and S T))
  | .mu S => .obj (Shape.telSelf S)

/-- A shape over `s` as propositions about a fresh self block.  A shape that
is not an object shape contributes the single self-bound `⊑ ⟦S⟧↑`; the bodies
of those bounds are spelled out rather than written `Shape.translate _`,
because `Shape.translate` would not be applied to a smaller argument there. -/
def Shape.tel : Shape s → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Shape.translate S).weaken (.sel .here A)))
        (.le (.sel .here A) (Shape.translate T).weaken)
  | .fld a (.capt C S) =>
      .cons
        (.cons (.cons .nil (.has a)) (.le (.sel .here a) (Shape.translate S).weaken))
        (.leC [FCdot.CapAtom.name .here a] (CaptureSet.translate C).weaken)
  | .cap A c1 c2 =>
      .cons (.cons .nil (.leC (CaptureSet.translate c1).weaken [FCdot.CapAtom.name .here A]))
        (.leC [FCdot.CapAtom.name .here A] (CaptureSet.translate c2).weaken)
  | .and S T => (Shape.tel S).append (Shape.tel T)
  | .mu S =>
      if S.isDecl then Shape.telSelf S
      else .cons .nil (.bnd (FCdot.Shape.obj (Shape.telSelf S)).weaken)
  | .top => .nil
  | .bot => .cons .nil (.bnd (FCdot.Shape.bot).weaken)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Shape.sel y A).weaken)
  | .all (.capt C1 S1) (.capt C2 S2) =>
      .cons .nil
        (.bnd (FCdot.Shape.pi (.capt C1.translate S1.translate)
          (.capt C2.translate S2.translate)).weaken)
  | .box (.capt C S) =>
      .cons .nil
        (.bnd (FCdot.Shape.box (.capt C.translate S.translate)).weaken)

/-- A shape over `(s,x)` whose self is the innermost binder, as propositions
about that binder.  The capture sets of a field and of a capture member are
already under the self here, so they are not weakened (plan-5a (c-1)).  The
self-bound of a non-object shape is *not* weakened either and may therefore
mention the self; `Wf.mu` keeps such bodies out of well-formed types, but the
function is total. -/
def Shape.telSelf : Shape (s,x) → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Shape.translate S) (.sel .here A)))
        (.le (.sel .here A) (Shape.translate T))
  | .fld a (.capt C S) =>
      .cons (.cons (.cons .nil (.has a)) (.le (.sel .here a) (Shape.translate S)))
        (.leC [FCdot.CapAtom.name .here a] (CaptureSet.translate C))
  | .cap A c1 c2 =>
      .cons (.cons .nil (.leC (CaptureSet.translate c1) [FCdot.CapAtom.name .here A]))
        (.leC [FCdot.CapAtom.name .here A] (CaptureSet.translate c2))
  | .and S T => (Shape.telSelf S).append (Shape.telSelf T)
  | .mu S =>
      if S.isDecl then (Shape.telSelf S).substVar .here
      else .cons .nil (.bnd (FCdot.Shape.obj (Shape.telSelf S)))
  | .top => .nil
  | .bot => .cons .nil (.bnd FCdot.Shape.bot)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Shape.sel y A))
  | .all (.capt C1 S1) (.capt C2 S2) =>
      .cons .nil
        (.bnd (FCdot.Shape.pi (.capt C1.translate S1.translate)
          (.capt C2.translate S2.translate)))
  | .box (.capt C S) =>
      .cons .nil (.bnd (FCdot.Shape.box (.capt C.translate S.translate)))

end

/-- `⟦S ^ C⟧ = ⟦S⟧ ^ ⟦C⟧`: the translated shape at the translated capture
set. -/
def Ty.translate : Ty s → FCdot.Ty s
  | .capt C S => FCdot.Ty.capt C.translate S.translate

@[simp] theorem Ty.translate_capt {s : Sig} (C : CaptureSet s) (S : Shape s) :
    (S ^ C).translate = FCdot.Ty.capt C.translate S.translate := rfl

@[simp] theorem Ty.translate_shape {s : Sig} (T : Ty s) :
    T.translate.shape = T.shape.translate := by cases T; rfl

@[simp] theorem Ty.translate_captureSet {s : Sig} (T : Ty s) :
    T.translate.captureSet = T.captureSet.translate := by cases T; rfl

/-- The arrow shape, one layer up: both sides are capturing types. -/
theorem Shape.translate_all_eq {s : Sig} (T1 : Ty s) (T2 : Ty (s,x)) :
    (Shape.all T1 T2).translate = FCdot.Shape.pi T1.translate T2.translate := by
  cases T1; cases T2; rw [Shape.translate]; rfl

theorem Shape.translate_box_eq {s : Sig} (T : Ty s) :
    (Shape.box T).translate = FCdot.Shape.box T.translate := by
  cases T; rw [Shape.translate]; rfl

/-! ## The two shapes of a telescope -/

/-- An object shape translates to the object shape of its own telescope. -/
theorem Shape.translate_isObj {s : Sig} :
    ∀ {S : Shape s}, S.isObj = true → S.translate = .obj S.tel
  | .top, _ => by simp [Shape.translate, Shape.tel]
  | .typ _ _ _, _ => by simp [Shape.translate]
  | .fld _ _, _ => by simp [Shape.translate]
  | .cap _ _ _, _ => by simp [Shape.translate]
  | .and _ _, _ => by simp [Shape.translate]
  | .mu S, h => by
      rw [Shape.isObj] at h
      simp [Shape.translate, Shape.tel, h]

/-- Every other shape is read as the single self-bound `⊑ ⟦S⟧↑`. -/
theorem Shape.tel_of_not_isObj {s : Sig} :
    ∀ {S : Shape s}, S.isObj = false → S.tel = .cons .nil (.bnd S.translate.weaken)
  | .bot, _ => by simp [Shape.translate, Shape.tel]
  | .sel (.var _) _, _ => by simp [Shape.translate, Shape.tel]
  | .all (.capt _ _) (.capt _ _), _ => by simp [Shape.translate, Shape.tel]
  | .box (.capt _ _), _ => by simp [Shape.translate, Shape.tel]
  | .mu S, h => by
      rw [Shape.isObj] at h
      simp [Shape.translate, Shape.tel, h]

/-- The same with the self already bound: there the bound is not weakened. -/
theorem Shape.telSelf_of_not_isObj {s : Sig} :
    ∀ {S : Shape (s,x)}, S.isObj = false → S.telSelf = .cons .nil (.bnd S.translate)
  | .bot, _ => by simp [Shape.translate, Shape.telSelf]
  | .sel (.var _) _, _ => by simp [Shape.translate, Shape.telSelf]
  | .all (.capt _ _) (.capt _ _), _ => by simp [Shape.translate, Shape.telSelf]
  | .box (.capt _ _), _ => by simp [Shape.translate, Shape.telSelf]
  | .mu S, h => by
      rw [Shape.isObj] at h
      simp [Shape.translate, Shape.telSelf, h]

/-! ## Witnesses of a literal -/

/-- The type witnesses of a literal, read off its declaration shape: the
exact bound of each type member and the declared shape of each field.  A
capture member has no type witness; it has a capture witness instead. -/
def Shape.witnesses : Shape (s,x) → FCdot.Witnesses (s,x)
  | .typ A S _ => .cons .nil A S.translate
  | .fld a (.capt _ S) => .cons .nil a S.translate
  | .and S T => S.witnesses.append T.witnesses
  | _ => .nil

/-- The capture witnesses of a literal, read off its declaration shape: the
*declared capture set* of each field and the *definition* of each capture
member.  This is the single place a translated literal's capture
declarations come from (stage A3a; stage A2 had one empty witness per field
label).  The order is the structural one, the left conjunct of an
intersection at the lower positions, as `Shape.witnesses` already is. -/
def Shape.capWitnesses : Shape (s,x) → FCdot.CapWitnesses (s,x)
  | .fld a (.capt C _) => .cons .nil a C.translate
  | .cap A c1 _ => .cons .nil A c1.translate
  | .and S T => S.capWitnesses.append T.capWitnesses
  | _ => .nil

/-- The field labels of a declaration shape, newest (outermost) first.
`FCdot.Fields.labels` lists the outermost field first and `FCdot.Fields.get?`
lets the outermost field win, and in DOT the *right* conjunct of an
intersection shadows; so the right conjunct's fields are the outermost ones
of the translated literal and come first here. -/
def Shape.fieldLabels : Shape s → List Label
  | .fld a _ => [a]
  | .and S T => T.fieldLabels ++ S.fieldLabels
  | _ => []

/-- The precise target shape of a literal whose declaration shape is `S`: its
type definitions, then its capture definitions, then its fields. -/
def Shape.literalShape (S : Shape (s,x)) : FCdot.Shape s :=
  .obj (FCdot.Telescope.ofLiteral S.witnesses S.capWitnesses S.fieldLabels)

/-- The precise target type of a literal whose declaration shape is `S` and
whose assigned capture set is `U`. -/
def Shape.literalTy (S : Shape (s,x)) (U : CaptureSet s) : FCdot.Ty s :=
  FCdot.Ty.capt U.translate S.literalShape

@[simp] theorem Shape.literalTy_shape {s : Sig} (S : Shape (s,x)) (U : CaptureSet s) :
    (S.literalTy U).shape = S.literalShape := rfl

@[simp] theorem Shape.literalTy_captureSet {s : Sig} (S : Shape (s,x)) (U : CaptureSet s) :
    (S.literalTy U).captureSet = U.translate := rfl

/-- Contexts translate binder by binder: an ordinary binder is opaque at its
translated type; a literal's self binder is transparent at the literal's
precise type, whose capture set is the translated use set the literal was
assigned; a platform capture binder is a rigid capture binder. -/
def Ctx.translate : Ctx s → FCdot.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.translate (.opaque T.translate)
  | .consSelf Γ _ S U =>
      .cons Γ.translate (.transparent (S.literalTy U) S.witnesses S.capWitnesses S.fieldLabels)
  | .consC Γ => .consC Γ.translate .star

end DotMNF

end Captures
