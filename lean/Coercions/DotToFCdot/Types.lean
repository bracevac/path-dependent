import Coercions.DotMNF.Typing
import Coercions.FCdot.Context

/-!
# Translation of types (Plan III §8.1, M3)

Types translate homomorphically.  Declaration-shaped types become object
types over a fresh self block: a type member `{A : S..T}` is the pair of
propositions `⟦S⟧ ⊑ self∙A`, `self∙A ⊑ ⟦T⟧`; a field `{a : T}` is presence of
`a` together with `self∙a ⊑ ⟦T⟧`; an intersection concatenates; a recursive
type `μ(x. T)` binds its own self, identified with the block of the object.
`⊤` is the empty object type, so every declaration-shaped type, `⊤`
included, is `μ (tel T)`.

Everything else is read as the *single self-bound proposition* `[⊑ ⟦B⟧]`.
These are `⊥`, a type selection, a function type, and a `μ` whose body is
not declaration-shaped. So `tel` is total and an intersection may have
arbitrary operands. `Ty.isObj` is the shape test that separates the two.
It holds exactly when `⟦T⟧ = μ (tel T)` (`Ty.isObj_iff_translate`). It
fails exactly when `tel T = [⊑ ⟦T⟧↑]` (`Ty.not_isObj_iff_tel`). This is a
translation classification, not a restriction on source recursive bodies.

Two telescope functions: `tel T` reads a type over `s` as propositions about
a fresh self, `telSelf T` reads a type over `(s,x)` whose self is already the
innermost binder.  They agree on weakened types (`tel_eq_telSelf_weaken`).
-/

namespace FCdot

/-- Concatenation of witnesses (second appended after the first). -/
def Witnesses.append : Witnesses s → Witnesses s → Witnesses s
  | W, .nil => W
  | W, .cons W' ℓ T => .cons (W.append W') ℓ T

def Witnesses.length : Witnesses s → Nat
  | .nil => 0
  | .cons W _ _ => W.length + 1

/-! ### Size up to renaming

The number of constructors of a type, proposition or telescope, with a
variable counted as one node whatever its index. Renaming keeps it, so a
telescope is never a proper part of a weakened copy of itself. The
converses of the two shape lemmas below rest on this. -/

mutual

/-- Constructor count of a type, a variable counted once. -/
def Ty.nodes : Ty s → Nat
  | .bot => 1
  | .sel _ _ => 1
  | .pi S T => S.nodes + T.nodes + 1
  | .obj Tel => Tel.nodes + 1

/-- Constructor count of a proposition. -/
def Proposition.nodes : Proposition s → Nat
  | .le S T => S.nodes + T.nodes + 1
  | .eq S T => S.nodes + T.nodes + 1
  | .has _ => 1
  | .bnd T => T.nodes + 1

/-- Constructor count of a telescope. -/
def Telescope.nodes : Telescope s → Nat
  | .nil => 1
  | .cons Tel P => Tel.nodes + P.nodes + 1

end

mutual

theorem Ty.nodes_rename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).nodes = T.nodes := by
  match T with
  | .bot => simp [Ty.rename, Ty.nodes]
  | .sel _ _ => simp [Ty.rename, Ty.nodes]
  | .pi S T => simp [Ty.rename, Ty.nodes, Ty.nodes_rename S, Ty.nodes_rename T]
  | .obj Tel => simp [Ty.rename, Ty.nodes, Telescope.nodes_rename Tel]

theorem Proposition.nodes_rename {s1 s2 : Sig} (P : Proposition s1) (ρ : Rename s1 s2) :
    (P.rename ρ).nodes = P.nodes := by
  match P with
  | .le S T => simp [Proposition.rename, Proposition.nodes, Ty.nodes_rename S, Ty.nodes_rename T]
  | .eq S T => simp [Proposition.rename, Proposition.nodes, Ty.nodes_rename S, Ty.nodes_rename T]
  | .has _ => simp [Proposition.rename, Proposition.nodes]
  | .bnd T => simp [Proposition.rename, Proposition.nodes, Ty.nodes_rename T]

theorem Telescope.nodes_rename {s1 s2 : Sig} (Tel : Telescope s1) (ρ : Rename s1 s2) :
    (Tel.rename ρ).nodes = Tel.nodes := by
  match Tel with
  | .nil => simp [Telescope.rename, Telescope.nodes]
  | .cons Tel P =>
      simp [Telescope.rename, Telescope.nodes, Telescope.nodes_rename Tel,
        Proposition.nodes_rename P]

end

/-- A telescope is not the one-bound telescope of its own object type: the
right side has more nodes. -/
theorem Telescope.ne_bnd_obj_weaken {s : Sig} (Tel : Telescope (s,x)) :
    Tel ≠ .cons .nil (.bnd (Ty.obj Tel).weaken) := by
  intro h
  have := congrArg Telescope.nodes h
  simp only [Telescope.nodes, Proposition.nodes, Ty.weaken, Ty.nodes_rename, Ty.nodes] at this
  omega

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- The types whose translation is the object type of their own telescope,
`⟦T⟧ = μ (tel T)` (`Ty.translate_isObj`).  For the others `tel T` is the
single self-bound `[⊑ ⟦T⟧↑]` (`Ty.tel_of_not_isObj`).  Both lemmas have
converses (`Ty.isObj_of_translate`, `Ty.not_isObj_of_tel`), so each equation
characterizes the test.  An intersection always passes, whatever its
operands, while a `μ` passes exactly when its body is declaration-shaped. -/
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

/-- `⟦T⟧`. -/
def Ty.translate : Ty s → FCdot.Ty s
  | .top => FCdot.Ty.obj .nil
  | .bot => .bot
  | .sel (.var x) A => .sel x A
  | .all S T => .pi (Ty.translate S) (Ty.translate T)
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
      .cons (.cons .nil (.le (Ty.translate S).weaken (.sel .here A)))
        (.le (.sel .here A) (Ty.translate T).weaken)
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translate T).weaken)
  | .and S T => (Ty.tel S).append (Ty.tel T)
  | .mu T =>
      if T.isDecl then Ty.telSelf T
      else .cons .nil (.bnd (FCdot.Ty.obj (Ty.telSelf T)).weaken)
  | .top => .nil
  | .bot => .cons .nil (.bnd (FCdot.Ty.bot).weaken)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Ty.sel y A).weaken)
  | .all S T => .cons .nil (.bnd (FCdot.Ty.pi (Ty.translate S) (Ty.translate T)).weaken)

/-- A type over `(s,x)` whose self is the innermost binder, as propositions
about that binder. The self-bound of a non-object shape is not weakened
here and may mention the self. Recursive elimination first opens this
telescope at the receiver, then extracts the opened bound. -/
def Ty.telSelf : Ty (s,x) → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translate S) (.sel .here A)))
        (.le (.sel .here A) (Ty.translate T))
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translate T))
  | .and S T => (Ty.telSelf S).append (Ty.telSelf T)
  | .mu T =>
      if T.isDecl then (Ty.telSelf T).substVar .here
      else .cons .nil (.bnd (FCdot.Ty.obj (Ty.telSelf T)))
  | .top => .nil
  | .bot => .cons .nil (.bnd FCdot.Ty.bot)
  | .sel (.var y) A => .cons .nil (.bnd (FCdot.Ty.sel y A))
  | .all S T => .cons .nil (.bnd (FCdot.Ty.pi (Ty.translate S) (Ty.translate T)))

end

/-! ## The two shapes of a telescope -/

/-- An object shape translates to the object type of its own telescope. -/
theorem Ty.translate_isObj {s : Sig} : ∀ {T : Ty s}, T.isObj = true → T.translate = .obj T.tel
  | .top, _ => by simp [Ty.translate, Ty.tel]
  | .typ _ _ _, _ => by simp [Ty.translate]
  | .fld _ _, _ => by simp [Ty.translate]
  | .and _ _, _ => by simp [Ty.translate]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.tel, h]

/-- Every other shape is read as the single self-bound `⊑ ⟦T⟧↑`. -/
theorem Ty.tel_of_not_isObj {s : Sig} :
    ∀ {T : Ty s}, T.isObj = false → T.tel = .cons .nil (.bnd T.translate.weaken)
  | .bot, _ => by simp [Ty.translate, Ty.tel]
  | .sel (.var _) _, _ => by simp [Ty.translate, Ty.tel]
  | .all _ _, _ => by simp [Ty.translate, Ty.tel]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.tel, h]

/-- The converse of `Ty.translate_isObj`: a type whose translation is the
object type of its own telescope is an object shape. -/
theorem Ty.isObj_of_translate {s : Sig} :
    ∀ {T : Ty s}, T.translate = .obj T.tel → T.isObj = true
  | .top, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .and _ _, _ => rfl
  | .bot, h => by simp [Ty.translate] at h
  | .sel (.var _) _, h => by simp [Ty.translate] at h
  | .all _ _, h => by simp [Ty.translate] at h
  | .mu T, h => by
      rw [Ty.isObj]
      cases hd : T.isDecl
      · simp only [Ty.translate, Ty.tel, hd, FCdot.Ty.obj.injEq] at h
        exact absurd h (FCdot.Telescope.ne_bnd_obj_weaken _)
      · rfl

/-- The converse of `Ty.tel_of_not_isObj`: a type whose telescope is the
single self-bound `⊑ ⟦T⟧↑` is not an object shape. -/
theorem Ty.not_isObj_of_tel {s : Sig} :
    ∀ {T : Ty s}, T.tel = .cons .nil (.bnd T.translate.weaken) → T.isObj = false
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .all _ _, _ => rfl
  | .top, h => by simp [Ty.tel] at h
  | .typ _ _ _, h => by simp [Ty.tel] at h
  | .fld _ _, h => by simp [Ty.tel] at h
  | .and S T, h => by
      simp only [Ty.translate] at h
      exact absurd h (FCdot.Telescope.ne_bnd_obj_weaken _)
  | .mu T, h => by
      rw [Ty.isObj]
      cases hd : T.isDecl
      · rfl
      · simp only [Ty.translate, Ty.tel, hd, if_true] at h
        exact absurd h (FCdot.Telescope.ne_bnd_obj_weaken _)

/-- `Ty.isObj` holds exactly when `⟦T⟧ = μ (tel T)`. -/
theorem Ty.isObj_iff_translate {s : Sig} {T : Ty s} :
    T.isObj = true ↔ T.translate = .obj T.tel :=
  ⟨Ty.translate_isObj, Ty.isObj_of_translate⟩

/-- `Ty.isObj` fails exactly when `tel T` is the single self-bound `⊑ ⟦T⟧↑`. -/
theorem Ty.not_isObj_iff_tel {s : Sig} {T : Ty s} :
    T.isObj = false ↔ T.tel = .cons .nil (.bnd T.translate.weaken) :=
  ⟨Ty.tel_of_not_isObj, Ty.not_isObj_of_tel⟩

/-- The same with the self already bound: there the bound is not weakened. -/
theorem Ty.telSelf_of_not_isObj {s : Sig} :
    ∀ {T : Ty (s,x)}, T.isObj = false → T.telSelf = .cons .nil (.bnd T.translate)
  | .bot, _ => by simp [Ty.translate, Ty.telSelf]
  | .sel (.var _) _, _ => by simp [Ty.translate, Ty.telSelf]
  | .all _ _, _ => by simp [Ty.translate, Ty.telSelf]
  | .mu T, h => by
      rw [Ty.isObj] at h
      simp [Ty.translate, Ty.telSelf, h]

/-- The witnesses of a literal, read off its declaration type: the exact
bound of each type member and the declared type of each field. -/
def Ty.witnesses : Ty (s,x) → FCdot.Witnesses (s,x)
  | .typ A S _ => .cons .nil A S.translate
  | .fld a T => .cons .nil a T.translate
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

/-- The precise target type of a literal whose declaration type is `T`. -/
def Ty.literalTy (T : Ty (s,x)) : FCdot.Ty s :=
  .obj (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels)

/-- Contexts translate binder by binder: an ordinary binder is opaque at its
translated type; a literal's self binder is transparent at the literal's
precise type. -/
def Ctx.translate : Ctx s → FCdot.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.translate (.opaque T.translate)
  | .consSelf Γ _ T =>
      .cons Γ.translate (.transparent T.literalTy T.witnesses T.fieldLabels)

end DotMNF
