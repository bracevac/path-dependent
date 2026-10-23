import Coercions.ScalaSyntax.Lex

/-!
# The syntax tree of the Scala subsets

The tree that the parser builds from the tokens of a `.scala` file.  It is the
union of the four subsets of plan IX (S-5): the vanilla one, and the capture
sets, `^`, `->`, capture members, `.only[K]`, the prelude lines and the
`def program` header of the capture front ends.  So a later front end adds no
constructor, and each front end's translation refuses what that front end
lacks.

Every node that a check can refuse carries its `Pos`.  A node that names
something sits at the name: a variable, a selected member, a declared member,
a parameter, a prelude class.  Any other node sits at the token that makes it:
`Any`, `this`, the `{` of a refinement or a block, the `new` of a literal, the
`^` of a capturing type, the arrow of a function type, the `:` of an
ascription.  scalac reports a selection at its member's name too (refute-d3
`NestRefThis`, `Undecl`).

Lists of recursive nodes are spines (`Decls`, `Stats`, `Defs`), so every walk
is structural.  `Program.erase` sets every position to `⟨0, 0⟩`, so checks and
round trips can compare trees up to positions.

This module imports the lexer, for `Pos`, and Lean core only.
-/

namespace ScalaSyntax

/-! ## Types -/

/-- The receiver of a type selection. -/
inductive Path where
  /-- `this`, the innermost refinement or literal. -/
  | this (p : Pos)
  /-- A variable, by name. -/
  | var (p : Pos) (x : String)
deriving DecidableEq, Repr

/-- A capture reference, at its first token. -/
inductive CapRef where
  /-- A variable, `k1` or `f`. -/
  | var (p : Pos) (x : String)
  /-- `caps.any`, the root capability. -/
  | any (p : Pos)
  /-- `x.only[K]`, or `caps.any.only[K]` when `x` is `none`. -/
  | only (p : Pos) (x : Option String) (k : String)
deriving DecidableEq, Repr

/-- A capture set, `{c1, …, cn}`. -/
abbrev CapSet := List CapRef

/-- The arrow of a function type. -/
inductive Arrow where
  /-- `=>`.  Under capture checking it may capture anything. -/
  | fat
  /-- `->`, a pure function, or `->{c}` with the capture set `c`. -/
  | thin (c : Option CapSet)
deriving DecidableEq, Repr

mutual
/-- Types. -/
inductive Ty where
  /-- `Any`. -/
  | any (p : Pos)
  /-- `Nothing`. -/
  | nothing (p : Pos)
  /-- `x.A` or `this.A`, at `A`. -/
  | sel (p : Pos) (q : Path) (A : String)
  /-- `{ d1; …; dn }`, a refinement of `Object`, at its `{`. -/
  | refine (p : Pos) (ds : Decls)
  /-- `S & T`.  Scala nests a chain of `&` to the left. -/
  | and (S T : Ty)
  /-- `(x: S) => T` when `x` is `some x`, else `S => T`, `S -> T` or
  `S ->{c} T`, at the arrow. -/
  | fn (p : Pos) (x : Option String) (S : Ty) (a : Arrow) (T : Ty)
  /-- `S^` when `c` is `none`, else `S^{c}`, at the `^`. -/
  | capt (p : Pos) (S : Ty) (c : Option CapSet)
/-- The declarations of a refinement, as a spine. -/
inductive Decls where
  /-- The end of the refinement. -/
  | nil
  /-- `type A >: S <: T`, each bound optional. -/
  | typ (p : Pos) (A : String) (lo hi : Option Ty) (rest : Decls)
  /-- `type A = T`. -/
  | alias (p : Pos) (A : String) (T : Ty) (rest : Decls)
  /-- `val a: T`. -/
  | val (p : Pos) (a : String) (T : Ty) (rest : Decls)
  /-- `type C^ >: {…} <: {…}`, a capture member, each bound optional. -/
  | cap (p : Pos) (C : String) (lo hi : Option CapSet) (rest : Decls)
  /-- `type C^ = {…}`. -/
  | capAlias (p : Pos) (C : String) (c : CapSet) (rest : Decls)
end

deriving instance Repr for Ty, Decls

/-! ### Equality of types

Lean v4.29.1 derives no `DecidableEq` for `Ty` and `Decls`.  `Decls.typ` holds
an `Option Ty`, a nested occurrence, and the deriving handler refuses nested
inductives.  So equality is a Boolean function, structural like the rest, and
two lemmas make it decide `=`.  Fields compare by `decide`, since the lawful
`==` of `String` depends on `Classical.choice`. -/

mutual
/-- Equality of types. -/
def Ty.beq (S T : Ty) : Bool :=
  match S, T with
  | .any p, .any q => decide (p = q)
  | .nothing p, .nothing q => decide (p = q)
  | .sel p x A, .sel q y B => decide (p = q) && decide (x = y) && decide (A = B)
  | .refine p ds, .refine q es => decide (p = q) && Decls.beq ds es
  | .and S₁ S₂, .and T₁ T₂ => Ty.beq S₁ T₁ && Ty.beq S₂ T₂
  | .fn p x S₁ a S₂, .fn q y T₁ b T₂ =>
    decide (p = q) && decide (x = y) && Ty.beq S₁ T₁ && decide (a = b) && Ty.beq S₂ T₂
  | .capt p S₁ c, .capt q T₁ d => decide (p = q) && Ty.beq S₁ T₁ && decide (c = d)
  | _, _ => false
termination_by structural S
/-- Equality of optional types. -/
def Ty.beqOpt (S T : Option Ty) : Bool :=
  match S, T with
  | none, none => true
  | some S₁, some T₁ => Ty.beq S₁ T₁
  | _, _ => false
termination_by structural S
/-- Equality of declarations. -/
def Decls.beq (ds es : Decls) : Bool :=
  match ds, es with
  | .nil, .nil => true
  | .typ p A lo hi r, .typ q B lo' hi' r' =>
    decide (p = q) && decide (A = B) && Ty.beqOpt lo lo' && Ty.beqOpt hi hi' && Decls.beq r r'
  | .alias p A T r, .alias q B T' r' =>
    decide (p = q) && decide (A = B) && Ty.beq T T' && Decls.beq r r'
  | .val p a T r, .val q b T' r' =>
    decide (p = q) && decide (a = b) && Ty.beq T T' && Decls.beq r r'
  | .cap p C lo hi r, .cap q D lo' hi' r' =>
    decide (p = q) && decide (C = D) && decide (lo = lo') && decide (hi = hi') && Decls.beq r r'
  | .capAlias p C c r, .capAlias q D d r' =>
    decide (p = q) && decide (C = D) && decide (c = d) && Decls.beq r r'
  | _, _ => false
termination_by structural ds
end

mutual
/-- A type equals itself. -/
theorem Ty.beq_refl (T : Ty) : Ty.beq T T = true := by
  match T with
  | .any _ | .nothing _ | .sel .. => simp only [Ty.beq, decide_true, Bool.and_self]
  | .refine _ ds => simp only [Ty.beq, decide_true, Decls.beq_refl ds, Bool.and_self]
  | .and S₁ S₂ => simp only [Ty.beq, Ty.beq_refl S₁, Ty.beq_refl S₂, Bool.and_self]
  | .fn _ _ S₁ _ S₂ =>
    simp only [Ty.beq, decide_true, Ty.beq_refl S₁, Ty.beq_refl S₂, Bool.and_self]
  | .capt _ S₁ _ => simp only [Ty.beq, decide_true, Ty.beq_refl S₁, Bool.and_self]
/-- An optional type equals itself. -/
theorem Ty.beqOpt_refl (T : Option Ty) : Ty.beqOpt T T = true := by
  match T with
  | none => simp only [Ty.beqOpt]
  | some T₁ => simp only [Ty.beqOpt, Ty.beq_refl T₁]
/-- Declarations equal themselves. -/
theorem Decls.beq_refl (ds : Decls) : Decls.beq ds ds = true := by
  match ds with
  | .nil => simp only [Decls.beq]
  | .typ _ _ lo hi r =>
    simp only [Decls.beq, decide_true, Ty.beqOpt_refl lo, Ty.beqOpt_refl hi, Decls.beq_refl r,
      Bool.and_self]
  | .alias _ _ T r | .val _ _ T r =>
    simp only [Decls.beq, decide_true, Ty.beq_refl T, Decls.beq_refl r, Bool.and_self]
  | .cap _ _ _ _ r | .capAlias _ _ _ r =>
    simp only [Decls.beq, decide_true, Decls.beq_refl r, Bool.and_self]
end

mutual
/-- Types that `Ty.beq` calls equal are equal. -/
theorem Ty.eq_of_beq (S T : Ty) (h : Ty.beq S T = true) : S = T := by
  match S with
  | .any _ | .nothing _ | .sel .. =>
    cases T <;> simp_all only [Ty.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true]
  | .refine _ ds =>
    cases T <;> simp only [Ty.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    rw [h.1, Decls.eq_of_beq ds _ h.2]
  | .and S₁ S₂ =>
    cases T <;> simp only [Ty.beq, Bool.and_eq_true, Bool.false_eq_true] at h
    rw [Ty.eq_of_beq S₁ _ h.1, Ty.eq_of_beq S₂ _ h.2]
  | .fn _ _ S₁ _ S₂ =>
    cases T <;> simp only [Ty.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, Ty.eq_of_beq S₁ _ h3, h4, Ty.eq_of_beq S₂ _ h5]
  | .capt _ S₁ _ =>
    cases T <;> simp only [Ty.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, Ty.eq_of_beq S₁ _ h2, h3]
/-- Optional types that `Ty.beqOpt` calls equal are equal. -/
theorem Ty.eq_of_beqOpt (S T : Option Ty) (h : Ty.beqOpt S T = true) : S = T := by
  match S with
  | none => cases T <;> simp_all only [Ty.beqOpt, Bool.false_eq_true]
  | some S₁ =>
    cases T <;> simp only [Ty.beqOpt, Bool.false_eq_true] at h
    rw [Ty.eq_of_beq S₁ _ h]
/-- Declarations that `Decls.beq` calls equal are equal. -/
theorem Decls.eq_of_beq (ds es : Decls) (h : Decls.beq ds es = true) : ds = es := by
  match ds with
  | .nil => cases es <;> simp_all only [Decls.beq, Bool.false_eq_true]
  | .typ _ _ lo hi r =>
    cases es <;> simp only [Decls.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, Ty.eq_of_beqOpt lo _ h3, Ty.eq_of_beqOpt hi _ h4, Decls.eq_of_beq r _ h5]
  | .alias _ _ T r =>
    cases es <;> simp only [Decls.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h2, Ty.eq_of_beq T _ h3, Decls.eq_of_beq r _ h4]
  | .val _ _ T r =>
    cases es <;> simp only [Decls.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h2, Ty.eq_of_beq T _ h3, Decls.eq_of_beq r _ h4]
  | .cap _ _ _ _ r =>
    cases es <;> simp only [Decls.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, h4, Decls.eq_of_beq r _ h5]
  | .capAlias _ _ _ r =>
    cases es <;> simp only [Decls.beq, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h2, h3, Decls.eq_of_beq r _ h4]
end

instance : DecidableEq Ty := fun S T =>
  decidable_of_iff (Ty.beq S T = true) ⟨Ty.eq_of_beq S T, fun h => h ▸ Ty.beq_refl S⟩

instance : DecidableEq Decls := fun ds es =>
  decidable_of_iff (Decls.beq ds es = true) ⟨Decls.eq_of_beq ds es, fun h => h ▸ Decls.beq_refl ds⟩

/-! ## Terms -/

mutual
/-- Terms. -/
inductive Tm where
  /-- A variable, by name. -/
  | var (p : Pos) (x : String)
  /-- `this`, the innermost literal. -/
  | this (p : Pos)
  /-- `t.a`, at `a`. -/
  | sel (t : Tm) (p : Pos) (a : String)
  /-- `t(u)`. -/
  | app (t u : Tm)
  /-- `(x: T) => e`, or `x => e` and `(x) => e` when `T` is `none`, at `x`. -/
  | lam (p : Pos) (x : String) (T : Option Ty) (body : Tm)
  /-- `(t: T)`, at the `:`. -/
  | asc (p : Pos) (t : Tm) (T : Ty)
  /-- `{ val …; e }`, a block, at its `{`. -/
  | block (p : Pos) (ss : Stats)
  /-- `new Object { s => ds }`, with the self name `s` if written, at `new`. -/
  | lit (p : Pos) (self : Option String) (ds : Defs)
/-- The statements of a block, as a spine that ends with its result. -/
inductive Stats where
  /-- The result of the block. -/
  | last (t : Tm)
  /-- `val x = e` or `val x: T = e`, then the rest of the block. -/
  | val (p : Pos) (x : String) (T : Option Ty) (rhs : Tm) (rest : Stats)
/-- The members of an object literal, as a spine. -/
inductive Defs where
  /-- The end of the literal. -/
  | nil
  /-- `type A = T`. -/
  | typ (p : Pos) (A : String) (T : Ty) (rest : Defs)
  /-- `val a = e` or `val a: T = e`. -/
  | val (p : Pos) (a : String) (T : Option Ty) (rhs : Tm) (rest : Defs)
  /-- `type C^ = {…}`, a capture member. -/
  | cap (p : Pos) (C : String) (c : CapSet) (rest : Defs)
end

deriving instance DecidableEq, Repr for Tm, Stats, Defs

/-! ## Files -/

/-- A line of the prelude of the capture front ends, at its class or trait
name. -/
inductive PreludeItem where
  /-- `class C extends caps.SharedCapability`. -/
  | capClass (p : Pos) (C : String)
  /-- `trait K extends caps.SharedCapability, caps.Classifier` when `parent` is
  `none`, else `trait K extends P, caps.Classifier`. -/
  | classifier (p : Pos) (K : String) (parent : Option String)
  /-- `class C extends K`, a platform class of the classifier `K`. -/
  | platClass (p : Pos) (C : String) (K : String)
deriving DecidableEq, Repr

/-- A file: the header imports, the wrapper object `object Name { … }`, its
prelude, and the one program. -/
structure Program where
  /-- The imports as dotted names, in order, each at its first name. -/
  imports : List (Pos × String)
  /-- The name of the wrapper object. -/
  name : String
  /-- The prelude lines, in order. -/
  prelude : List PreludeItem
  /-- `none` for `val program`.  For `def program(x: C^, …)`, the parameters,
  each at its name, with its class. -/
  params : Option (List (Pos × String × String))
  /-- The written type of the program, `: T`. -/
  ty : Option Ty
  /-- The right side of `program`. -/
  body : Tm
deriving DecidableEq, Repr

/-! ## Positions erased -/

/-- The position that `erase` writes everywhere. -/
def Pos.zero : Pos := ⟨0, 0⟩

/-- A path without positions. -/
def Path.erase : Path → Path
  | .this _ => .this Pos.zero
  | .var _ x => .var Pos.zero x

/-- A capture reference without positions. -/
def CapRef.erase : CapRef → CapRef
  | .var _ x => .var Pos.zero x
  | .any _ => .any Pos.zero
  | .only _ x k => .only Pos.zero x k

/-- A capture set without positions. -/
def eraseCaps (c : CapSet) : CapSet := c.map CapRef.erase

/-- An arrow without positions. -/
def Arrow.erase : Arrow → Arrow
  | .fat => .fat
  | .thin c => .thin (c.map eraseCaps)

mutual
/-- A type without positions. -/
def Ty.erase (T : Ty) : Ty :=
  match T with
  | .any _ => .any Pos.zero
  | .nothing _ => .nothing Pos.zero
  | .sel _ q A => .sel Pos.zero q.erase A
  | .refine _ ds => .refine Pos.zero (Decls.erase ds)
  | .and S U => .and (Ty.erase S) (Ty.erase U)
  | .fn _ x S a U => .fn Pos.zero x (Ty.erase S) a.erase (Ty.erase U)
  | .capt _ S c => .capt Pos.zero (Ty.erase S) (c.map eraseCaps)
termination_by structural T
/-- An optional type without positions. -/
def Ty.eraseOpt (T : Option Ty) : Option Ty :=
  match T with
  | none => none
  | some U => some (Ty.erase U)
termination_by structural T
/-- Declarations without positions. -/
def Decls.erase (ds : Decls) : Decls :=
  match ds with
  | .nil => .nil
  | .typ _ A lo hi r => .typ Pos.zero A (Ty.eraseOpt lo) (Ty.eraseOpt hi) (Decls.erase r)
  | .alias _ A T r => .alias Pos.zero A (Ty.erase T) (Decls.erase r)
  | .val _ a T r => .val Pos.zero a (Ty.erase T) (Decls.erase r)
  | .cap _ C lo hi r => .cap Pos.zero C (lo.map eraseCaps) (hi.map eraseCaps) (Decls.erase r)
  | .capAlias _ C c r => .capAlias Pos.zero C (eraseCaps c) (Decls.erase r)
termination_by structural ds
end

mutual
/-- A term without positions. -/
def Tm.erase (t : Tm) : Tm :=
  match t with
  | .var _ x => .var Pos.zero x
  | .this _ => .this Pos.zero
  | .sel u _ a => .sel (Tm.erase u) Pos.zero a
  | .app u v => .app (Tm.erase u) (Tm.erase v)
  | .lam _ x T b => .lam Pos.zero x (Ty.eraseOpt T) (Tm.erase b)
  | .asc _ u T => .asc Pos.zero (Tm.erase u) T.erase
  | .block _ ss => .block Pos.zero (Stats.erase ss)
  | .lit _ s ds => .lit Pos.zero s (Defs.erase ds)
termination_by structural t
/-- Statements without positions. -/
def Stats.erase (ss : Stats) : Stats :=
  match ss with
  | .last t => .last (Tm.erase t)
  | .val _ x T e r => .val Pos.zero x (Ty.eraseOpt T) (Tm.erase e) (Stats.erase r)
termination_by structural ss
/-- Literal members without positions. -/
def Defs.erase (ds : Defs) : Defs :=
  match ds with
  | .nil => .nil
  | .typ _ A T r => .typ Pos.zero A T.erase (Defs.erase r)
  | .val _ a T e r => .val Pos.zero a (Ty.eraseOpt T) (Tm.erase e) (Defs.erase r)
  | .cap _ C c r => .cap Pos.zero C (eraseCaps c) (Defs.erase r)
termination_by structural ds
end

/-- A prelude line without positions. -/
def PreludeItem.erase : PreludeItem → PreludeItem
  | .capClass _ C => .capClass Pos.zero C
  | .classifier _ K P => .classifier Pos.zero K P
  | .platClass _ C K => .platClass Pos.zero C K

/-- A file without positions: every `Pos` is `⟨0, 0⟩`. -/
def Program.erase (P : Program) : Program where
  imports := P.imports.map fun i => (Pos.zero, i.2)
  name := P.name
  prelude := P.prelude.map PreludeItem.erase
  params := P.params.map (·.map fun x => (Pos.zero, x.2))
  ty := Ty.eraseOpt P.ty
  body := P.body.erase

end ScalaSyntax
