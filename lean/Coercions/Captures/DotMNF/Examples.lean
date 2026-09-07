import Coercions.Captures.DotMNF.Machine

namespace Captures

/-!
# DOT-MNF^cc examples

The mandatory examples of Plan III §10, as `HasTy` derivations, restated on
the judgments of stage A3a.  The calculus has no base types, so `Int` and
`Nat` are replaced by distinct closed types; the point of each example is the
*shape* of the derivation, in particular which subtyping steps go through a
type selection.

Every type of E1 to E8 is pure and every use set of them is empty: they are
the vanilla examples, and the vanilla source has no capture set to speak of.
What was a vanilla `Ty` is a `Shape` wherever the vanilla derivation used it
as one (a bound of a type member, an operand of an intersection, the body of
a `μ`), and the pure type `S ^ {}` wherever the vanilla derivation used it as
a type (a field's result, a function's domain and result, a context entry).
Both forms of a name are kept, the shape carrying the suffix `S`.

Three further examples, S3, C2 and C7, are the capture examples of stage
A3a.  They live over the platform prefix of two rigid capture binders and
their use sets are not empty: a boxed capturing type in a type member (S3),
explicit capture polymorphism through a capture member (C2), and a pure
container of boxed capabilities whose elements charge their own set when
unboxed (C7).

Derivations are plain proof terms: `HasTy` is `Type`-valued, so a derivation
is data and is constructed, not decided (`native_decide` does not apply).
Each intermediate judgment is a named definition with its type spelled out,
which is also the readable form of the example.
-/

namespace DotMNF
namespace Examples

open FCdot (Kind Sig BVar Rename Label)

/-! ## Derivation helpers

Three abbreviations that make a pure derivation read exactly like the
vanilla one.  `var'` is `Var` followed by the two `sc-var` steps that take
the refined capture set `{x}` of a pure binder back down to `{}`; `subS` is
`sub` when only the shape changes; `lam'` and `obj'` are `All-I` and `{}-I`
with the body's use set widened from `{}` to the set the rule asks for. -/

/-- `Var` at a pure binder, with the variable given explicitly; the declared
type is read off the context by reduction. -/
def var' {s : Sig} {Γ : Ctx s} (x : BVar s .var) {S : Shape s}
    (h : Γ.lookup x = S ^ []) : HasTy [] Γ (.path (.var x)) (S ^ []) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  refine HasTy.sub HasTy.var (.capt ?_ hv) hv
  rw [h]
  exact SubShape.refl

/-- `sub` at a pure type and the empty use set: only the shape changes. -/
def subS {s : Sig} {Γ : Ctx s} {t : Tm s} {S S' : Shape s}
    (h : HasTy [] Γ t (S ^ [])) (d : SubShape Γ S S') : HasTy [] Γ t (S' ^ []) :=
  .sub h (.capt d .refl) .refl

/-- `All-I` at a pure lambda: the body is derived at the empty use set and
widened to the set the rule charges it at. -/
def lam' {s : Sig} {Γ : Ctx s} {T1 : Ty s} {t : Tm (s,x)} {T2 : Ty (s,x)}
    (h : HasTy [] (Γ.cons T1) t T2) (w : Ty.Wf T1) :
    HasTy [] Γ (.val (.lam T1 t)) ((Shape.all T1 T2) ^ []) :=
  .lam (h.widen _) w

/-- `{}-I` at a pure literal, likewise. -/
def obj' {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {S : Shape (s,x)}
    (h : DefsTy [] (Γ.consSelf d S []) d S) (hd : Defs.Distinct d) :
    HasTy [] Γ (.val (.obj d)) ((Shape.mu S) ^ []) :=
  .obj (h.widen _) hd

/-! ## Labels -/

/-- Type label `A`. -/
def lA : Label := .typ 0
/-- Type label `B`. -/
def lB : Label := .typ 1
/-- Term label `a`. -/
def la : Label := .trm 0
/-- Term label `b`. -/
def lb : Label := .trm 1
/-- Type label `T`. -/
def lT : Label := .typ 2
/-- Term label `v`. -/
def lv : Label := .trm 2

/-! ## E1: bad bounds under a lambda

`λ(x : {A : ⊤..⊥}). let y = x in y`, where the `let` retypes `x` at the
unrelated type `{B : {a : ⊤}..{a : ⊤}}` through `⊤ <: x.A <: ⊥`. -/

/-- `{A : ⊤..⊥}`: bad bounds. -/
def E1DomS : Shape s := .typ lA .top .bot
def E1Dom : Ty s := E1DomS ^ []
/-- `{B : {a : ⊤}..{a : ⊤}}`, unrelated to `E1Dom`. -/
def E1ResS : Shape s := .typ lB (.fld la (.top ^ [])) (.fld la (.top ^ []))
def E1Res : Ty s := E1ResS ^ []

/-- Under `x : {A : ⊤..⊥}` every shape is above every other. -/
def badBounds {s : Sig} {Γ : Ctx s} {x : BVar s .var} {U D : CaptureSet s}
    (hx : HasTy U Γ (.path (.var x)) ((Shape.typ lA .top .bot) ^ D)) (S : Shape s) :
    SubShape Γ E1DomS S :=
  .trans .top (.trans (.selLower hx) (.trans (.selUpper hx) .bot))

def E1Ctx : Ctx ([],x) := .cons .nil E1Dom

def E1x : HasTy [] E1Ctx (.path (.var .here)) E1Dom := var' .here rfl

def E1retype : HasTy [] E1Ctx (.path (.var .here)) E1Res := subS E1x (badBounds E1x E1ResS)

def E1body : HasTy [] E1Ctx (.let (.path (.var .here)) (.path (.var .here))) E1Res :=
  .let E1retype (var' .here rfl)
    (.capt (.typ (.fld (.capt .top)) (.fld (.capt .top))))

def E1 : HasTy [] Ctx.nil
    (.val (.lam E1Dom (.let (.path (.var .here)) (.path (.var .here)))))
    ((Shape.all E1Dom E1Res) ^ []) :=
  lam' E1body (.capt (.typ .top .bot))

/-! ## E2: recursive object with a self-referential member

`ν(x. {A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y})`, allocated by a `let`,
its term member selected and applied to itself.  The application typechecks
because the exact bounds of `A` give `∀(y : x.A) x.A <: x.A`. -/

/-- `∀(y : x.A) x.A`, under the object's self binder. -/
def E2AS : Shape (s,x) :=
  .all ((Shape.sel (.var .here) lA) ^ []) ((Shape.sel (.var (.there .here)) lA) ^ [])
def E2A : Ty (s,x) := E2AS ^ []
/-- The same shape one binder further out. -/
def E2AS' : Shape (s,x,x) :=
  .all ((Shape.sel (.var (.there .here)) lA) ^ [])
    ((Shape.sel (.var (.there (.there .here))) lA) ^ [])
def E2A' : Ty (s,x,x) := E2AS' ^ []
/-- The object's self shape `{A : E2A..E2A} ∧ {a : E2A}`. -/
def E2Self : Shape (s,x) := .and (.typ lA E2AS E2AS) (.fld la E2A)
/-- The object's definitions. -/
def E2Defs : Defs (s,x) :=
  .and (.typ lA E2AS)
    (.trm la (.val (.lam ((Shape.sel (.var .here) lA) ^ []) (.path (.var .here)))))

theorem E2Distinct : Defs.Distinct (E2Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self shape is declaration-shaped. -/
theorem E2SelfDecl : Shape.Decl (E2Self (s := s)) := .and .typ .fld

def E2DefsTy : DefsTy [] (Ctx.consSelf Γ E2Defs E2Self []) E2Defs E2Self :=
  .and .typ (.trm (lam' (var' .here rfl) (.capt .sel)))

def E2Ctx1 : Ctx ([],x) := .cons .nil ((Shape.mu E2Self) ^ [])

def E2xMu : HasTy [] E2Ctx1 (.path (.var .here)) ((Shape.mu E2Self) ^ []) := var' .here rfl
def E2xOpen : HasTy [] E2Ctx1 (.path (.var .here)) (E2Self ^ []) := .recE E2xMu E2SelfDecl
def E2xFld : HasTy [] E2Ctx1 (.path (.var .here)) ((Shape.fld la E2A) ^ []) :=
  subS E2xOpen .and2
def E2proj : HasTy [] E2Ctx1 (.proj .here la) E2A := .proj E2xFld

def E2Ctx2 : Ctx ([],x,x) := .cons E2Ctx1 E2A

def E2f : HasTy [] E2Ctx2 (.path (.var .here)) E2A' := var' .here rfl
def E2xMu2 : HasTy [] E2Ctx2 (.path (.var (.there .here))) ((Shape.mu E2Self) ^ []) :=
  var' (.there .here) rfl
def E2xOpen2 : HasTy [] E2Ctx2 (.path (.var (.there .here)))
    ((Shape.and (.typ lA E2AS' E2AS') (.fld la E2A')) ^ []) := .recE E2xMu2 E2SelfDecl
/-- `∀(y : x.A) x.A <: x.A`, by the lower bound of the exact member `A`. -/
def E2fArg : HasTy [] E2Ctx2 (.path (.var .here))
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  subS E2f (.selLower (subS E2xOpen2 .and1))
def E2app : HasTy [] E2Ctx2 (.app .here .here)
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  .app E2f E2fArg

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : HasTy [] Ctx.nil
    (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here))) (.top ^ []) :=
  .let (obj' E2DefsTy E2Distinct)
    (.let E2proj (subS E2app .top) (.capt .top))
    (.capt .top)

/-! ## E3: intersection with a shared member

`x : {A : ⊥..T₁} ∧ {A : T₂..⊤}` with `T₁ = {a : ⊤}` and `T₂ = {b : ⊤}`
unrelated: the two bounds of the single member `A` make `T₂ <: T₁`. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E3T1S : Shape s := .fld la (.top ^ [])
def E3T1 : Ty s := E3T1S ^ []
/-- `{b : ⊤}`, standing for `Nat`; unrelated to `E3T1`. -/
def E3T2S : Shape s := .fld lb (.top ^ [])
def E3T2 : Ty s := E3T2S ^ []
/-- `{A : ⊥..T₁} ∧ {A : T₂..⊤}`. -/
def E3DomS : Shape s := .and (.typ lA .bot E3T1S) (.typ lA E3T2S .top)
def E3Dom : Ty s := E3DomS ^ []

def E3Ctx1 : Ctx ([],x) := .cons .nil E3Dom
def E3Ctx2 : Ctx ([],x,x) := .cons E3Ctx1 E3T2

def E3xDom : HasTy [] E3Ctx2 (.path (.var (.there .here))) E3Dom := var' (.there .here) rfl
def E3xLo : HasTy [] E3Ctx2 (.path (.var (.there .here)))
    ((Shape.typ lA .bot E3T1S) ^ []) := subS E3xDom .and1
def E3xHi : HasTy [] E3Ctx2 (.path (.var (.there .here)))
    ((Shape.typ lA E3T2S .top) ^ []) := subS E3xDom .and2
/-- `T₂ <: x.A <: T₁`: the shared member, used at both bounds. -/
def E3sub : SubShape E3Ctx2 E3T2S E3T1S := .trans (.selLower E3xHi) (.selUpper E3xLo)
def E3z : HasTy [] E3Ctx2 (.path (.var .here)) E3T1 := subS (var' .here rfl) E3sub

def E3body : HasTy [] E3Ctx2 (.let (.path (.var .here)) (.path (.var .here))) E3T1 :=
  .let E3z (var' .here rfl) (.capt (.fld (.capt .top)))

def E3inner : HasTy [] E3Ctx1
    (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here)))))
    ((Shape.all E3T2 E3T1) ^ []) :=
  lam' E3body (.capt (.fld (.capt .top)))

/-- `λ(x : {A : ⊥..T₁} ∧ {A : T₂..⊤}). λ(z : T₂). let y = z in y`. -/
def E3 : HasTy [] Ctx.nil
    (.val (.lam E3Dom (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here)))))))
    ((Shape.all E3Dom ((Shape.all E3T2 E3T1) ^ [])) ^ []) :=
  lam' E3inner
    (.capt (.and (.typ .bot (.fld (.capt .top))) (.typ (.fld (.capt .top)) .top)))

/-! ## E4: the counterexample of §1

`Γ = x : {B : S..T}, w : S` with `S = {A : ⊥..⊤}` and `T = {A : Int..⊤}`.
`S <: x.B <: T` gives `w : T`, hence `Int <: w.A`, hence `g n : w.A` for
`g = λ(y : w.A). y` and `n : Int`.  No realizer for `x` exists, and the
derivation is nonetheless well formed: this is why the target of Plan III
needs `member` through `trans`. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E4IntS : Shape s := .fld la (.top ^ [])
def E4Int : Ty s := E4IntS ^ []
/-- `S = {A : ⊥..⊤}`. -/
def E4SS : Shape s := .typ lA .bot .top
def E4S : Ty s := E4SS ^ []
/-- `T = {A : Int..⊤}`. -/
def E4TS : Shape s := .typ lA E4IntS .top
def E4T : Ty s := E4TS ^ []
/-- `{B : S..T}`. -/
def E4XS : Shape s := .typ lB E4SS E4TS
def E4X : Ty s := E4XS ^ []

def E4Ctx1 : Ctx ([],x) := .cons .nil E4X
def E4Ctx2 : Ctx ([],x,x) := .cons E4Ctx1 E4S
def E4Ctx3 : Ctx ([],x,x,x) := .cons E4Ctx2 E4Int

/-- The type of `g = λ(y : w.A). y`, in the scope of `x`, `w`, `n`. -/
def E4GS : Shape (s,x,x,x) :=
  .all ((Shape.sel (.var (.there .here)) lA) ^ [])
    ((Shape.sel (.var (.there (.there .here))) lA) ^ [])
def E4G : Ty (s,x,x,x) := E4GS ^ []
/-- The same type one binder further out. -/
def E4GS' : Shape (s,x,x,x,x) :=
  .all ((Shape.sel (.var (.there (.there .here))) lA) ^ [])
    ((Shape.sel (.var (.there (.there (.there .here)))) lA) ^ [])
def E4G' : Ty (s,x,x,x,x) := E4GS' ^ []

def E4x : HasTy [] E4Ctx3 (.path (.var (.there (.there .here)))) E4X :=
  var' (.there (.there .here)) rfl
/-- `S <: x.B <: T`, the step with no realizer. -/
def E4ST : SubShape E4Ctx3 E4SS E4TS := .trans (.selLower E4x) (.selUpper E4x)
def E4wT : HasTy [] E4Ctx3 (.path (.var (.there .here))) E4T :=
  subS (var' (.there .here) rfl) E4ST
def E4g : HasTy [] E4Ctx3
    (.val (.lam ((Shape.sel (.var (.there .here)) lA) ^ []) (.path (.var .here)))) E4G :=
  lam' (var' .here rfl) (.capt .sel)

def E4Ctx4 : Ctx ([],x,x,x,x) := .cons E4Ctx3 E4G

def E4x4 : HasTy [] E4Ctx4 (.path (.var (.there (.there (.there .here))))) E4X :=
  var' (.there (.there (.there .here))) rfl
def E4ST4 : SubShape E4Ctx4 E4SS E4TS := .trans (.selLower E4x4) (.selUpper E4x4)
def E4wT4 : HasTy [] E4Ctx4 (.path (.var (.there (.there .here)))) E4T :=
  subS (var' (.there (.there .here)) rfl) E4ST4
/-- `n : Int <: w.A`. -/
def E4nA : HasTy [] E4Ctx4 (.path (.var (.there .here)))
    ((Shape.sel (.var (.there (.there .here))) lA) ^ []) :=
  subS (var' (.there .here) rfl) (.selLower E4wT4)
def E4gv : HasTy [] E4Ctx4 (.path (.var .here)) E4G' := var' .here rfl
def E4app : HasTy [] E4Ctx4 (.app .here (.there .here))
    ((Shape.sel (.var (.there (.there .here))) lA) ^ []) := .app E4gv E4nA

def E4let : HasTy [] E4Ctx3
    (.let (.val (.lam ((Shape.sel (.var (.there .here)) lA) ^ []) (.path (.var .here))))
      (.app .here (.there .here)))
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  .let E4g E4app (.capt .sel)

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : HasTy [] Ctx.nil
    (.val (.lam E4X (.val (.lam E4S (.val (.lam E4Int
      (.let (.val (.lam ((Shape.sel (.var (.there .here)) lA) ^ []) (.path (.var .here))))
        (.app .here (.there .here)))))))))
    ((Shape.all E4X
      ((Shape.all E4S
        ((Shape.all E4Int ((Shape.sel (.var (.there .here)) lA) ^ [])) ^ [])) ^ [])) ^ []) :=
  lam' (lam' (lam' E4let (.capt (.fld (.capt .top)))) (.capt (.typ .bot .top)))
    (.capt (.typ (.typ .bot .top) (.typ (.fld (.capt .top)) .top)))

/-! ## E5: an object returned from a function and selected after a `let`

`λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z. {a = v}) in
 let o = f w in o.a`.  The result type of `f` mentions the parameter's
member, so the application renames it to `w`; the result of the outer `let`
is `w.A`, which mentions neither `let` binder. -/

/-- `{A : ⊤..⊤}`. -/
def E5ATS : Shape s := .typ lA .top .top
def E5AT : Ty s := E5ATS ^ []
/-- `{a : v.A}` under the object's self binder, `v` the enclosing lambda's
parameter. -/
def E5Self : Shape (s,x,x) := .fld la ((Shape.sel (.var (.there .here)) lA) ^ [])
/-- The type of `f`: `∀(v : {A : ⊤..⊤}) μ(z. {a : v.A})`. -/
def E5F : Ty s := (Shape.all E5AT ((Shape.mu E5Self) ^ [])) ^ []
/-- `μ(z. {a : w.A})`, the type of `f w` in the scope of `w`, `f`. -/
def E5Owned : Ty (s,x,x) :=
  (Shape.mu (.fld la ((Shape.sel (.var (.there (.there .here))) lA) ^ []))) ^ []
/-- The same type one binder further out. -/
def E5Owned' : Ty (s,x,x,x) :=
  (Shape.mu (.fld la ((Shape.sel (.var (.there (.there (.there .here)))) lA) ^ []))) ^ []
/-- The body of `f`: `ν(z. {a = v})`. -/
def E5Obj : Tm (s,x) := .val (.obj (.trm la (.path (.var (.there .here)))))

def E5Ctx1 : Ctx ([],x) := .cons .nil E5AT
def E5Ctxv : Ctx ([],x,x) := .cons E5Ctx1 E5AT
/-- The definitions of the literal `ν(z. {a = v})`. -/
def E5Defs : Defs (s,x,x) := .trm la (.path (.var (.there .here)))
def E5Ctxz : Ctx ([],x,x,x) := .consSelf E5Ctxv E5Defs E5Self []

def E5v : HasTy [] E5Ctxz (.path (.var (.there .here))) E5AT := var' (.there .here) rfl
/-- The field body: `v : ⊤ <: v.A`, by the lower bound of `v`'s member. -/
def E5field : HasTy [] E5Ctxz (.path (.var (.there .here)))
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  subS (subS E5v .top) (.selLower E5v)
def E5DefsTy : DefsTy [] E5Ctxz E5Defs E5Self := .trm E5field

def E5ObjTy : HasTy [] E5Ctxv E5Obj ((Shape.mu E5Self) ^ []) :=
  obj' E5DefsTy .trm
def E5fVal : HasTy [] E5Ctx1 (.val (.lam E5AT E5Obj)) E5F :=
  lam' E5ObjTy (.capt (.typ .top .top))

def E5Ctxf : Ctx ([],x,x) := .cons E5Ctx1 E5F

def E5fv : HasTy [] E5Ctxf (.path (.var .here)) E5F := var' .here rfl
def E5w : HasTy [] E5Ctxf (.path (.var (.there .here))) E5AT := var' (.there .here) rfl
/-- `f w : μ(z. {a : w.A})`: the application renames `v`'s block to `w`. -/
def E5o : HasTy [] E5Ctxf (.app .here (.there .here)) E5Owned := .app E5fv E5w

def E5Ctxo : Ctx ([],x,x,x) := .cons E5Ctxf E5Owned

def E5oMu : HasTy [] E5Ctxo (.path (.var .here)) E5Owned' := var' .here rfl
def E5oOpen : HasTy [] E5Ctxo (.path (.var .here))
    ((Shape.fld la ((Shape.sel (.var (.there (.there .here))) lA) ^ [])) ^ []) :=
  .recE E5oMu .fld
def E5proj : HasTy [] E5Ctxo (.proj .here la)
    ((Shape.sel (.var (.there (.there .here))) lA) ^ []) :=
  .proj E5oOpen

def E5oLet : HasTy [] E5Ctxf (.let (.app .here (.there .here)) (.proj .here la))
    ((Shape.sel (.var (.there .here)) lA) ^ []) := .let E5o E5proj (.capt .sel)

def E5fLet : HasTy [] E5Ctx1
    (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))
    ((Shape.sel (.var .here) lA) ^ []) := .let E5fVal E5oLet (.capt .sel)

def E5 : HasTy [] Ctx.nil
    (.val (.lam E5AT
      (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))))
    ((Shape.all E5AT ((Shape.sel (.var .here) lA) ^ [])) ^ []) :=
  lam' E5fLet (.capt (.typ .top .top))

/-! ## E6: a field typed at its own literal's type member

`ν(x. {T = Int} ∧ {v = n})`, with `n : Int` from the enclosing scope, typed
at `μ(x. {T : Int..Int} ∧ {v : x.T})`.  The field `v` is declared at `x.T`, a
selection on the object's own self: the shape the self-alias restriction
used to forbid, now admitted by alias-tolerant resolution on the target
side. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E6IntS : Shape s := .fld la (.top ^ [])
def E6Int : Ty s := E6IntS ^ []
/-- The object's self shape `{T : Int..Int} ∧ {v : x.T}`. -/
def E6Self : Shape (s,x,x) :=
  .and (.typ lT E6IntS E6IntS) (.fld lv ((Shape.sel (.var .here) lT) ^ []))
/-- The object's definitions: `T = Int`, `v = n` (`n` the enclosing variable). -/
def E6Defs : Defs (s,x,x) := .and (.typ lT E6IntS) (.trm lv (.path (.var (.there .here))))

theorem E6Distinct : Defs.Distinct (E6Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self shape is declaration-shaped. -/
theorem E6SelfDecl : Shape.Decl (E6Self (s := s)) := .and .typ .fld

def E6Ctx1 : Ctx ([],x) := .cons .nil E6Int
def E6Ctxz : Ctx ([],x,x) := .consSelf E6Ctx1 E6Defs E6Self []

def E6xMu : HasTy [] E6Ctxz (.path (.var .here)) ((Shape.mu E6Self) ^ []) := var' .here rfl
def E6xOpen : HasTy [] E6Ctxz (.path (.var .here)) (E6Self ^ []) := .recE E6xMu E6SelfDecl
def E6xTyp : HasTy [] E6Ctxz (.path (.var .here)) ((Shape.typ lT E6IntS E6IntS) ^ []) :=
  subS E6xOpen .and1
/-- `n : Int <: x.T`, by the lower bound of the exact member `T`. -/
def E6nT : HasTy [] E6Ctxz (.path (.var (.there .here)))
    ((Shape.sel (.var .here) lT) ^ []) :=
  subS (var' (.there .here) rfl) (.selLower E6xTyp)

def E6DefsTy : DefsTy [] E6Ctxz E6Defs E6Self := .and .typ (.trm E6nT)

/-- `λ(n : Int). ν(x. {T = Int} ∧ {v = n})`. -/
def E6 : HasTy [] E6Ctx1 (.val (.obj E6Defs)) ((Shape.mu E6Self) ^ []) :=
  obj' E6DefsTy E6Distinct

/-! ## E7: a two-element alias cycle

`ν(x. {A = x.B} ∧ {B = x.A})`: both type members are bare selections on the
object's own self, and each other's.  Admitted now that alias-tolerant
resolution follows same-block aliases on the target side (a cyclic alias
resolves to `⊤`, `FCdot.Ctx.resolve`); the self-alias restriction that used
to forbid this shape on the definitions is gone. -/

def E7Self : Shape (s,x) :=
  .and (.typ lA (.sel (.var .here) lB) (.sel (.var .here) lB))
    (.typ lB (.sel (.var .here) lA) (.sel (.var .here) lA))
def E7Defs : Defs (s,x) :=
  .and (.typ lA (.sel (.var .here) lB)) (.typ lB (.sel (.var .here) lA))

theorem E7Distinct : Defs.Distinct (E7Defs (s := s)) := by
  refine .and .typ .typ ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

def E7DefsTy : DefsTy [] (Ctx.consSelf Γ E7Defs E7Self []) E7Defs E7Self := .and .typ .typ

/-- `ν(x. {A = x.B} ∧ {B = x.A})`. -/
def E7 : HasTy [] Ctx.nil (.val (.obj E7Defs)) ((Shape.mu E7Self) ^ []) :=
  obj' E7DefsTy E7Distinct

/-! ## E8: refining an abstract type

`λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`, at
`∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) ⊤`.  The left operand of the
intersection is a type selection, so the type is outside the declaration
fragment: this is the example the self-bound proposition of `FCdot` buys
(plan §13 item 9), and `Wf.and` accepts it because it no longer asks for
declaration-shaped operands.

Two derivations of the body, `y.a`: one reads `{a : ⊤}` off the refinement
by `And₂`, the other reads `x.A` off it by `And₁` and then goes through
`Sel-<:`.  `E8AndI` is the `And-I` direction, which puts the two typings of
`y` back together; it is a derivation, not a closed program. -/

/-- `{A : ⊥..{a : ⊤}}`, the declaration of the abstract type. -/
def E8DomS : Shape s := .typ lA .bot (.fld la (.top ^ []))
def E8Dom : Ty s := E8DomS ^ []

/-- `x.A ∧ {a : ⊤}`, the refinement of `x.A`. -/
def E8RefS (x : BVar s .var) : Shape s := .and (.sel (.var x) lA) (.fld la (.top ^ []))
def E8Ref (x : BVar s .var) : Ty s := E8RefS x ^ []

theorem E8DomWf : Ty.Wf (E8Dom (s := s)) := .capt (.typ .bot (.fld (.capt .top)))

/-- The refinement is well formed although its left operand is not
declaration-shaped: `Wf.and` has no `Shape.Decl` premises. -/
theorem E8RefWf {x : BVar s .var} : Ty.Wf (E8Ref x) := .capt (.and .sel (.fld (.capt .top)))

def E8Ctx1 : Ctx ([],x) := Ctx.nil.cons E8Dom
def E8Ctx2 : Ctx ([],x,x) := E8Ctx1.cons (E8Ref .here)

/-- `y : x.A ∧ {a : ⊤}`. -/
def E8y : HasTy [] E8Ctx2 (.path (.var .here)) (E8Ref (.there .here)) := var' .here rfl

/-- `x : {A : ⊥..{a : ⊤}}`. -/
def E8x : HasTy [] E8Ctx2 (.path (.var (.there .here))) E8Dom := var' (.there .here) rfl

/-- `And₂`: the declaration operand of the refinement. -/
def E8yFld2 : HasTy [] E8Ctx2 (.path (.var .here))
    ((Shape.fld la (.top ^ [])) ^ []) := subS E8y .and2

/-- `And₁`: the abstract type itself. -/
def E8yA : HasTy [] E8Ctx2 (.path (.var .here))
    ((Shape.sel (.var (.there .here)) lA) ^ []) := subS E8y .and1

/-- `Sel-<:`: the upper bound of `x`'s member `A`. -/
def E8Upper : SubShape E8Ctx2 (.sel (.var (.there .here)) lA) (.fld la (.top ^ [])) :=
  .selUpper E8x

/-- The same conclusion as `E8yFld2`, the other way round. -/
def E8yFld1 : HasTy [] E8Ctx2 (.path (.var .here))
    ((Shape.fld la (.top ^ [])) ^ []) := subS E8yA E8Upper

/-- `And-I`: the two views of `y` recombined into the refinement. -/
def E8AndI : HasTy [] E8Ctx2 (.path (.var .here)) (E8Ref (.there .here)) :=
  .andI E8yA E8yFld2

/-- `y.a`, through `And₂`. -/
def E8Body2 : HasTy [] E8Ctx2 (.proj .here la) (.top ^ []) := .proj E8yFld2

/-- `y.a`, through `And₁` and `Sel-<:`. -/
def E8Body1 : HasTy [] E8Ctx2 (.proj .here la) (.top ^ []) := .proj E8yFld1

/-- `λ(x). λ(y). y.a`, with the `And₂` derivation of the body. -/
def E8 : HasTy [] Ctx.nil
    (.val (.lam E8Dom (.val (.lam (E8Ref .here) (.proj .here la)))))
    ((Shape.all E8Dom ((Shape.all (E8Ref .here) (.top ^ [])) ^ [])) ^ []) :=
  lam' (lam' E8Body2 E8RefWf) E8DomWf

/-- The same term, with the `And₁`-then-`Sel-<:` derivation of the body. -/
def E8b : HasTy [] Ctx.nil
    (.val (.lam E8Dom (.val (.lam (E8Ref .here) (.proj .here la)))))
    ((Shape.all E8Dom ((Shape.all (E8Ref .here) (.top ^ [])) ^ [])) ^ []) :=
  lam' (lam' E8Body1 E8RefWf) E8DomWf

/-! ## The platform prefix of stage A3a

S3, C2 and C7 live over a prefix of two rigid capture binders, the platform
capabilities `κ₁` and `κ₂`.  The prefix is `Platform.cons (Platform.cons
Platform.nil)`; its context is two capture binders and its store two
data-free slots. -/

/-- The platform prefix of two capture binders. -/
def plat : Platform ([],c,c) := .cons (.cons .nil)

/-- The platform context: two rigid capture binders, no bound. -/
def platCtx : Ctx ([],c,c) := .consC (.consC .nil)

/-- The platform store: one data-free slot per binder. -/
theorem plat_store : plat.store = Store.consC (Store.consC .nil) := rfl

/-- `κ₁`, the outer platform capability. -/
def k1 : BVar ([],c,c) .cap := .there .here
/-- `κ₂`, the inner one. -/
def k2 : BVar ([],c,c) .cap := .here

/-! ## Further derivation helpers

`varAt` is `var'` at a binder whose declared capture set need not be empty:
`Var` followed by the one `sc-var` step that takes the refined set `{x}`
back down to the declared set.  `varSelf` is `Var` itself, at the refined
set `{x}`, with the shape read off the context.  `subC` is `subS` at a
capture set that is not empty, and `widenTo` is `sub` on the use set alone,
along a syntactic inclusion. -/

/-- `Var` at a binder, subsumed to the type the context declares, capture
set included. -/
def varAt {s : Sig} {Γ : Ctx s} (x : BVar s .var) {S : Shape s} {C : CaptureSet s}
    (h : Γ.lookup x = S ^ C) : HasTy [CapAtom.var x] Γ (.path (.var x)) (S ^ C) := by
  have hv : Subcap Γ [CapAtom.var x] C := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  refine HasTy.sub HasTy.var (.capt ?_ hv) .refl
  rw [h]
  exact SubShape.refl

/-- `Var` at a binder, at the refined capture set `{x}`: the shape is read
off the context. -/
def varSelf {s : Sig} {Γ : Ctx s} (x : BVar s .var) {S : Shape s}
    (h : (Γ.lookup x).shape = S) :
    HasTy [CapAtom.var x] Γ (.path (.var x)) (S ^ [CapAtom.var x]) := by
  subst h
  exact HasTy.var

/-- `sub` when only the shape changes, at an arbitrary capture set and use
set. -/
def subC {s : Sig} {Γ : Ctx s} {U C : CaptureSet s} {t : Tm s} {S S' : Shape s}
    (h : HasTy U Γ t (S ^ C)) (d : SubShape Γ S S') : HasTy U Γ t (S' ^ C) :=
  .sub h (.capt d .refl) .refl

/-- `sub` on the use set alone, along a syntactic inclusion. -/
def HasTy.widenTo {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {T : Ty s}
    (h : HasTy U Γ t T) (hs : CaptureSet.Subset U U') : HasTy U' Γ t T :=
  .sub h (Sub.refl T) (.elem hs)

/-- A one-atom set is included in every set that has the atom. -/
theorem sub_one {s : Sig} {a : CapAtom s} {C : CaptureSet s} (h : a ∈ C) :
    CaptureSet.Subset [a] C := by
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact h

/-- A set is included in its union with another. -/
theorem sub_union_left {s : Sig} (C D : CaptureSet s) : CaptureSet.Subset C (C ∪ D) :=
  fun _ h => List.mem_append_left _ h

/-! ## Types shared by the capture examples -/

/-- `Unit`, the pure `⊤`. -/
def unitTy : Ty s := .top ^ []
/-- `Unit → Unit`, the shape of a capability. -/
def arrowS : Shape s := .all unitTy unitTy
/-- The type of a capability over the capture binder `κ`. -/
def capTy (κ : BVar s .cap) : Ty s := arrowS ^ [CapAtom.cvar κ]

theorem arrowWf : Ty.Wf (arrowS ^ C : Ty s) := .capt (.all (.capt .top) (.capt .top))
theorem unitWf : Ty.Wf (unitTy : Ty s) := .capt .top

/-! ## Labels of the capture examples -/

/-- Type label `C`, a capture member. -/
def lC : Label := .typ 3
/-- Term label `elem`. -/
def lelem : Label := .trm 3
/-- Term label `run`. -/
def lrun : Label := .trm 4
/-- Term label `e₁`. -/
def le1 : Label := .trm 5
/-- Term label `e₂`. -/
def le2 : Label := .trm 6

/-! ## S3: a type member instantiated with a boxed capturing type

```text
λ(f : (Unit → Unit) ^ {κ₁}).
  let o = ν(z. {A = □((Unit → Unit) ^ {f})} ∧ {elem = □ f}) in
  let e = o.elem in
  {f} ⊸ e
```

The member `A` is instantiated with a *boxed* capturing type, which is how a
capturing type enters a type member at all: the bounds of a type member are
shapes, and `□ T` is the shape that carries a type.  The field `elem` is
declared at `z.A ^ {}`, so the literal is pure although the value it holds
captures `f`.  The client reads the field, opens the member by its upper
bound, and unboxes; the unboxing charges `{f}`, so the client's use set is
`{f}`. -/

/-- `□((Unit → Unit) ^ {f})`, the boxed capturing type the member `A`
holds. -/
def S3Box (f : BVar s .var) : Shape s := .box (arrowS ^ [CapAtom.var f])

/-- The literal's declaration shape, with the self at `z`:
`{A : □((Unit→Unit) ^ {f}) .. □((Unit→Unit) ^ {f})} ∧ {elem : z.A ^ {}}`. -/
def S3SelfAt (z f : BVar s .var) : Shape s :=
  .and (.typ lA (S3Box f) (S3Box f)) (.fld lelem ((Shape.sel (.var z) lA) ^ []))

/-- The literal's definitions: `A = □((Unit→Unit) ^ {f})` and `elem = □ f`. -/
def S3Defs (f : BVar (s,x) .var) : Defs (s,x) :=
  .and (.typ lA (S3Box f)) (.trm lelem (.val (.box f)))

theorem S3Distinct (f : BVar (s,x) .var) : Defs.Distinct (S3Defs f) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The declaration shape is declaration-shaped. -/
theorem S3SelfDecl {z f : BVar s .var} : Shape.Decl (S3SelfAt z f) := .and .typ .fld

/-- `κ₁, κ₂, f : (Unit → Unit) ^ {κ₁}`. -/
def S3Ctx1 : Ctx ([],c,c,x) := platCtx.cons (capTy (.there .here))

/-- The context inside the literal: the self binder `z` on top of `S3Ctx1`. -/
def S3Ctxz : Ctx ([],c,c,x,x) :=
  S3Ctx1.consSelf (S3Defs (.there .here)) (S3SelfAt .here (.there .here)) []

def S3zMu : HasTy [] S3Ctxz (.path (.var .here))
    ((Shape.mu (S3SelfAt .here (.there (.there .here)))) ^ []) := var' .here rfl

def S3zOpen : HasTy [] S3Ctxz (.path (.var .here))
    ((S3SelfAt .here (.there .here)) ^ []) := .recE S3zMu S3SelfDecl

def S3zTyp : HasTy [] S3Ctxz (.path (.var .here))
    ((Shape.typ lA (S3Box (.there .here)) (S3Box (.there .here))) ^ []) :=
  subS S3zOpen .and1

/-- `□ f : □((Unit → Unit) ^ {f})`, a pure value. -/
def S3boxf : HasTy [] S3Ctxz (.val (.box (.there .here)))
    ((S3Box (.there .here)) ^ []) := .box (varSelf (.there .here) rfl)

/-- The field body, brought to the declared type `z.A ^ {}` by the lower
bound of the exact member `A`. -/
def S3field : HasTy [] S3Ctxz (.val (.box (.there .here)))
    ((Shape.sel (.var .here) lA) ^ []) := subS S3boxf (.selLower S3zTyp)

def S3DefsTy : DefsTy [] S3Ctxz (S3Defs (.there .here)) (S3SelfAt .here (.there .here)) :=
  .and .typ (.trm S3field)

/-- The literal is pure: its capture set is `{}`. -/
def S3Lit : HasTy [] S3Ctx1 (.val (.obj (S3Defs (.there .here))))
    ((Shape.mu (S3SelfAt .here (.there .here))) ^ []) :=
  obj' S3DefsTy (S3Distinct _)

/-- The context after the literal's `let`. -/
def S3Ctxo : Ctx ([],c,c,x,x) :=
  S3Ctx1.cons ((Shape.mu (S3SelfAt .here (.there .here))) ^ [])

def S3oMu : HasTy [] S3Ctxo (.path (.var .here))
    ((Shape.mu (S3SelfAt .here (.there (.there .here)))) ^ []) := var' .here rfl

def S3oFld : HasTy [] S3Ctxo (.path (.var .here))
    ((Shape.fld lelem ((Shape.sel (.var .here) lA) ^ [])) ^ []) :=
  subS (.recE S3oMu S3SelfDecl) .and2

def S3proj : HasTy [] S3Ctxo (.proj .here lelem)
    ((Shape.sel (.var .here) lA) ^ []) := .proj S3oFld

/-- The context after the projection's `let`. -/
def S3Ctxe : Ctx ([],c,c,x,x,x) :=
  S3Ctxo.cons ((Shape.sel (.var .here) lA) ^ [])

def S3e : HasTy [] S3Ctxe (.path (.var .here))
    ((Shape.sel (.var (.there .here)) lA) ^ []) := var' .here rfl

def S3oTyp : HasTy [] S3Ctxe (.path (.var (.there .here)))
    ((Shape.typ lA (S3Box (.there (.there .here))) (S3Box (.there (.there .here)))) ^ []) :=
  subS (.recE (var' (.there .here) rfl) S3SelfDecl) .and1

/-- The element, opened by the upper bound of the member `A`. -/
def S3eBox : HasTy [] S3Ctxe (.path (.var .here))
    ((S3Box (.there (.there .here))) ^ []) := subS S3e (.selUpper S3oTyp)

/-- `{f} ⊸ e`: the unboxing charges the boxed set to the use set. -/
def S3unbox : HasTy [CapAtom.var (.there (.there .here))] S3Ctxe
    (.unbox [CapAtom.var (.there (.there .here))] .here)
    (arrowS ^ [CapAtom.var (.there (.there .here))]) :=
  .unbox (S3eBox.widen _) .refl

def S3innerLet : HasTy [CapAtom.var (.there .here)] S3Ctxo
    (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here))
    (arrowS ^ [CapAtom.var (.there .here)]) :=
  .let (S3proj.widen _) S3unbox arrowWf

/-- The client, typed with use set `{f}`. -/
def S3body : HasTy [CapAtom.var .here] S3Ctx1
    (.let (.val (.obj (S3Defs (.there .here))))
      (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here)))
    (arrowS ^ [CapAtom.var .here]) :=
  .let (S3Lit.widen _) S3innerLet arrowWf

/-- The term of S3. -/
def S3tm : Tm ([],c,c) :=
  .val (.lam (capTy k1)
    (.let (.val (.obj (S3Defs (.there .here))))
      (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here))))

/-- The type of S3. -/
def S3Ty : Ty ([],c,c) :=
  (Shape.all (capTy k1) (arrowS ^ [CapAtom.var .here])) ^ []

/-- **S3.**  A type member instantiated with a boxed capturing type, a field
declared at that member and defined by a box, and a client that projects and
unboxes at the use set `{f}`. -/
def S3_typed : HasTy [] platCtx S3tm S3Ty := .lam S3body arrowWf

/-! ## C7: a container of boxed capabilities is pure

```text
λ(f₁ : (Unit → Unit) ^ {κ₁}). λ(f₂ : (Unit → Unit) ^ {κ₂}).
  let o = ν(z. {e₁ = □ f₁} ∧ {e₂ = □ f₂}) in
  let e = o.e₁ in
  {κ₁} ⊸ e
```

Both fields are declared at a boxed type and at the empty capture set, so
the container is typed at `^ {}`: it is pure, although it holds two
capabilities.  Unboxing one element charges that element's set and no more:
the client's use set is `{κ₁}`, and `{κ₂}` never enters it.  The client does
not type with use set `{}`, since subcapturing over a platform prefix has no
rule that puts `{κ₁}` below the empty set. -/

/-- The container's declaration shape:
`{e₁ : □((Unit→Unit) ^ {κ₁}) ^ {}} ∧ {e₂ : □((Unit→Unit) ^ {κ₂}) ^ {}}`. -/
def C7SelfAt (κ1 κ2 : BVar s .cap) : Shape s :=
  .and (.fld le1 ((Shape.box (capTy κ1)) ^ [])) (.fld le2 ((Shape.box (capTy κ2)) ^ []))

/-- The container's definitions: `e₁ = □ f₁` and `e₂ = □ f₂`. -/
def C7Defs (f1 f2 : BVar s .var) : Defs s :=
  .and (.trm le1 (.val (.box f1))) (.trm le2 (.val (.box f2)))

theorem C7Distinct (f1 f2 : BVar s .var) : Defs.Distinct (C7Defs f1 f2) := by
  refine .and .trm .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

theorem C7SelfDecl {κ1 κ2 : BVar s .cap} : Shape.Decl (C7SelfAt κ1 κ2) := .and .fld .fld

/-- `κ₁, κ₂, f₁ : (Unit → Unit) ^ {κ₁}`. -/
def C7Ctx1 : Ctx ([],c,c,x) := platCtx.cons (capTy (.there .here))

/-- `κ₁, κ₂, f₁, f₂ : (Unit → Unit) ^ {κ₂}`. -/
def C7Ctx2 : Ctx ([],c,c,x,x) := C7Ctx1.cons (capTy (.there .here))

/-- The container's declaration shape under the self binder of the
literal. -/
def C7SelfZ : Shape ([],c,c,x,x,x) :=
  C7SelfAt (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))

/-- The container's definitions under its self binder. -/
def C7DefsZ : Defs ([],c,c,x,x,x) := C7Defs (.there (.there .here)) (.there .here)

/-- The context inside the container: the self binder `z` on top. -/
def C7Ctxz : Ctx ([],c,c,x,x,x) := C7Ctx2.consSelf C7DefsZ C7SelfZ []

/-- `□ f₁ : □((Unit → Unit) ^ {κ₁}) ^ {}`, at the field's declared type. -/
def C7box1 : HasTy [] C7Ctxz (.val (.box (.there (.there .here))))
    ((Shape.box (capTy (.there (.there (.there (.there .here)))))) ^ []) :=
  .box (varAt (.there (.there .here)) rfl)

/-- `□ f₂`, likewise. -/
def C7box2 : HasTy [] C7Ctxz (.val (.box (.there .here)))
    ((Shape.box (capTy (.there (.there (.there .here))))) ^ []) :=
  .box (varAt (.there .here) rfl)

def C7DefsTy : DefsTy [] C7Ctxz C7DefsZ C7SelfZ := .and (.trm C7box1) (.trm C7box2)

/-- **The container is pure.**  Its two fields hold capabilities, and its
capture set is `{}`. -/
def C7Lit : HasTy [] C7Ctx2 (.val (.obj C7DefsZ)) ((Shape.mu C7SelfZ) ^ []) :=
  obj' C7DefsTy (C7Distinct _ _)

/-- The context after the container's `let`. -/
def C7Ctxo : Ctx ([],c,c,x,x,x) := C7Ctx2.cons ((Shape.mu C7SelfZ) ^ [])

def C7oMu : HasTy [] C7Ctxo (.path (.var .here))
    ((Shape.mu (C7SelfAt (.there (.there (.there (.there (.there .here)))))
      (.there (.there (.there (.there .here)))))) ^ []) := var' .here rfl

def C7oFld : HasTy [] C7Ctxo (.path (.var .here))
    ((Shape.fld le1 ((Shape.box (capTy (.there (.there (.there (.there .here)))))) ^ [])) ^ []) :=
  subS (.recE C7oMu C7SelfDecl) .and1

def C7proj : HasTy [] C7Ctxo (.proj .here le1)
    ((Shape.box (capTy (.there (.there (.there (.there .here)))))) ^ []) := .proj C7oFld

/-- The context after the projection's `let`. -/
def C7Ctxe : Ctx ([],c,c,x,x,x,x) :=
  C7Ctxo.cons ((Shape.box (capTy (.there (.there (.there (.there .here)))))) ^ [])

def C7e : HasTy [] C7Ctxe (.path (.var .here))
    ((Shape.box (capTy (.there (.there (.there (.there (.there .here))))))) ^ []) :=
  var' .here rfl

/-- `{κ₁} ⊸ e`: unboxing the first element charges `{κ₁}` and nothing
else. -/
def C7unbox : HasTy [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] C7Ctxe
    (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] .here)
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]) :=
  .unbox (C7e.widen _) .refl

/-- The two `let`s and the unboxing, the client of C7. -/
def C7clientTm : Tm ([],c,c,x,x) :=
  .let (.val (.obj C7DefsZ))
    (.let (.proj .here le1)
      (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] .here))

def C7innerLet :
    HasTy [CapAtom.cvar (.there (.there (.there (.there .here))))] C7Ctxo
      (.let (.proj .here le1)
        (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))] .here))
      (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there .here))))]) :=
  .let (C7proj.widen _) C7unbox arrowWf

/-- The client, typed with use set `{κ₁}`. -/
def C7body : HasTy [CapAtom.cvar (.there (.there (.there .here)))] C7Ctx2 C7clientTm
    (arrowS ^ [CapAtom.cvar (.there (.there (.there .here)))]) :=
  .let (C7Lit.widen _) C7innerLet arrowWf

/-- The term of C7. -/
def C7tm : Tm ([],c,c) :=
  .val (.lam (capTy k1) (.val (.lam (capTy (.there .here)) C7clientTm)))

/-- The type of C7. -/
def C7Ty : Ty ([],c,c) :=
  (Shape.all (capTy k1)
    ((Shape.all (capTy (.there .here))
      (arrowS ^ [CapAtom.cvar (.there (.there (.there .here)))]))
      ^ [CapAtom.cvar (.there (.there .here))])) ^ []

/-- **C7.**  A pure container of two boxed capabilities, and a client that
unboxes the first element at the use set `{κ₁}`. -/
def C7_typed : HasTy [] platCtx C7tm C7Ty :=
  .lam ((HasTy.lam (HasTy.widenTo C7body (sub_union_left _ _)) arrowWf).widen _) arrowWf

/-! ## C2: explicit capture polymorphism

```text
let c  = λ(x : μ(z. {C : {}..{κ₁,κ₂}} ∧ {run : (Unit → Unit) ^ {z.C}}) ^ {κ₁,κ₂}).
           λ(u : Unit). let g = x.run in g u in
let a  = ν(z. {C = {κ₁}} ∧ {run = λ(u : Unit). u}) in
let b  = ν(z. {C = {κ₂}} ∧ {run = λ(u : Unit). u}) in
let ga = c a in
let gb = c b in
gb
```

The capture member `C` is a capture-set parameter, written at a type label
as the compiler desugars one.  The two literals define it as `{κ₁}` and as
`{κ₂}`; each is retyped at the abstract member `{C : {}..{κ₁,κ₂}}` on its
own variable, by `Rec-E`, `Cap` and `Rec-I`.  The client is typed once,
against the abstract member: the closure it reads has capture set `{x.C}`,
and `sc-var` followed by the upper bound of the abstract member
(`Subcap.selUpper`) charges its call to `{κ₁,κ₂}`.  The whole program has
use set `{κ₁,κ₂}`. -/

/-- The abstract declaration shape, with the self at `z`. -/
def C2AbsAt (z : BVar s .var) (κ1 κ2 : BVar s .cap) : Shape s :=
  .and (.cap lC [] [.cvar κ1, .cvar κ2]) (.fld lrun (arrowS ^ [CapAtom.sel z lC]))

/-- The precise declaration shape of a literal that defines `C` as `{κ}`. -/
def C2PreAt (z : BVar s .var) (κ : BVar s .cap) : Shape s :=
  .and (.cap lC [.cvar κ] [.cvar κ]) (.fld lrun (arrowS ^ [CapAtom.sel z lC]))

/-- A literal's definitions: `C = {κ}` and `run = λ(u : Unit). u`. -/
def C2Defs (κ : BVar s .cap) : Defs s :=
  .and (.cap lC [.cvar κ]) (.trm lrun (.val (.lam unitTy (.path (.var .here)))))

theorem C2Distinct (κ : BVar s .cap) : Defs.Distinct (C2Defs κ) := by
  refine .and .cap .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

theorem C2AbsDecl {z : BVar s .var} {κ1 κ2 : BVar s .cap} :
    Shape.Decl (C2AbsAt z κ1 κ2) := .and .cap .fld
theorem C2PreDecl {z : BVar s .var} {κ : BVar s .cap} :
    Shape.Decl (C2PreAt z κ) := .and .cap .fld

/-- The abstract type of the two objects. -/
def C2AbsTy (κ1 κ2 : BVar s .cap) : Ty s :=
  (Shape.mu (C2AbsAt .here (.there κ1) (.there κ2))) ^ [.cvar κ1, .cvar κ2]

theorem C2AbsWf {κ1 κ2 : BVar s .cap} : Ty.Wf (C2AbsTy κ1 κ2) :=
  .capt (.mu (.and .cap (.fld arrowWf)) (.and .cap .fld))

/-- The precise type of a literal that defines `C` as `{κ}`. -/
def C2PreTy (κ : BVar s .cap) : Ty s := (Shape.mu (C2PreAt .here (.there κ))) ^ []

/-- The field body of a literal: the identity closure, at the capture set
the member `C` names. -/
def C2run {s : Sig} {Γ : Ctx s} {κ : BVar (s,x) .cap} :
    HasTy [] (Γ.consSelf (C2Defs κ) (C2PreAt .here κ) [])
      (.val (.lam unitTy (.path (.var .here))))
      (arrowS ^ [CapAtom.sel .here lC]) :=
  .lam ((var' .here rfl).widen _) unitWf

/-- A literal, at its precise type: pure, with `C` defined as `{κ}`. -/
def C2Lit {s : Sig} {Γ : Ctx s} (κ : BVar s .cap) :
    HasTy [] Γ (.val (.obj (C2Defs (.there κ)))) (C2PreTy κ) :=
  obj' (.and .cap (.trm C2run)) (C2Distinct _)

/-- A literal's variable, retyped at the abstract type: `Rec-E`, then `Cap`
on the member, then `Rec-I`, then the declared capture set. -/
def C2abstract {s : Sig} {Γ : Ctx s} {U : CaptureSet s} (x : BVar s .var)
    (κ1 κ2 : BVar s .cap) {κ : BVar s .cap}
    (hm : CapAtom.cvar κ ∈ [CapAtom.cvar κ1, CapAtom.cvar κ2])
    (h : Γ.lookup x = C2PreTy κ) :
    HasTy U Γ (.path (.var x)) (C2AbsTy κ1 κ2) :=
  .sub
    (HasTy.recI
      (subS (.recE (var' x h) C2PreDecl)
        (.and (.trans .and1 (.cap (.elem (CaptureSet.nil_subset _)) (.elem (sub_one hm))))
          .and2))
      C2AbsDecl)
    (.capt .refl (.elem (CaptureSet.nil_subset _))) (Subcap.empty U)

/-! ### The client

Three contexts: the abstract object `x`, the unit argument `u`, and the
closure `g` the client reads off `x`. -/

def C2CtxX {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (s,x) :=
  Γ.cons (C2AbsTy κ1 κ2)
def C2CtxU {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (s,x,x) :=
  (C2CtxX Γ κ1 κ2).cons unitTy
def C2CtxG {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (s,x,x,x) :=
  (C2CtxU Γ κ1 κ2).cons (arrowS ^ [CapAtom.sel (.there .here) lC])

/-- `x`, opened at the abstract capture member, beside `g`. -/
def C2xCap {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTy [CapAtom.var (.there (.there .here))] (C2CtxG Γ κ1 κ2)
      (.path (.var (.there (.there .here))))
      ((Shape.cap lC [] [.cvar (.there (.there (.there κ1))),
        .cvar (.there (.there (.there κ2)))]) ^ [CapAtom.var (.there (.there .here))]) :=
  subC (.recE (varSelf (.there (.there .here)) rfl) C2AbsDecl) .and1

/-- `g u`, charged to `{κ₁,κ₂}` by `sc-var` and the upper bound of the
abstract member. -/
def C2call {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTy [CapAtom.cvar (.there (.there (.there κ1))),
        CapAtom.cvar (.there (.there (.there κ2)))]
      (C2CtxG Γ κ1 κ2) (.app .here (.there .here)) (.top ^ []) :=
  .app (T2 := unitTy)
    (.sub (varSelf .here rfl) (.capt .refl (.trans Subcap.var (.selUpper C2xCap)))
      (.trans Subcap.var (.selUpper C2xCap)))
    ((var' (.there .here) rfl).widen _)

/-- The client's body: read the closure off the abstract member and call
it. -/
def C2clientBody {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTy [CapAtom.cvar (.there (.there κ1)), CapAtom.cvar (.there (.there κ2))]
      (C2CtxU Γ κ1 κ2)
      (.let (.proj (.there .here) lrun) (.app .here (.there .here))) (.top ^ []) :=
  .let
    (.sub (.proj (subC (.recE (varSelf (.there .here) rfl) C2AbsDecl) .and2))
      (Sub.refl _) Subcap.var)
    C2call (.capt .top)

/-- The type of the client. -/
def C2ClientTy (κ1 κ2 : BVar s .cap) : Ty s :=
  (Shape.all (C2AbsTy κ1 κ2)
    (arrowS ^ [CapAtom.cvar (.there κ1), CapAtom.cvar (.there κ2)])) ^ []

/-- The client's term. -/
def C2clientTm (κ1 κ2 : BVar s .cap) : Tm s :=
  .val (.lam (C2AbsTy κ1 κ2)
    (.val (.lam unitTy (.let (.proj (.there .here) lrun) (.app .here (.there .here))))))

/-- The client, a value: capture polymorphic in the member `C`. -/
def C2ClientVal {s : Sig} {Γ : Ctx s} (κ1 κ2 : BVar s .cap) :
    HasTy [] Γ (C2clientTm κ1 κ2) (C2ClientTy κ1 κ2) :=
  .lam ((HasTy.lam (HasTy.widenTo C2clientBody (sub_union_left _ _)) unitWf).widen _) C2AbsWf

/-! ### The program -/

/-- `κ₁, κ₂, c`. -/
def C2Ctx1 : Ctx ([],c,c,x) := platCtx.cons (C2ClientTy k1 k2)
/-- … `a`. -/
def C2Ctx2 : Ctx ([],c,c,x,x) := C2Ctx1.cons (C2PreTy (.there (.there .here)))
/-- … `b`. -/
def C2Ctx3 : Ctx ([],c,c,x,x,x) := C2Ctx2.cons (C2PreTy (.there (.there .here)))
/-- … `ga = c a`. -/
def C2Ctx4 : Ctx ([],c,c,x,x,x,x) :=
  C2Ctx3.cons (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there .here)))),
    CapAtom.cvar (.there (.there (.there .here)))])
/-- … `gb = c b`. -/
def C2Ctx5 : Ctx ([],c,c,x,x,x,x,x) :=
  C2Ctx4.cons (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
    CapAtom.cvar (.there (.there (.there (.there .here))))])

/-- The answer: the second instantiation, at the platform's own capture
set. -/
def C2answer : HasTy
    [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]
    C2Ctx5 (.path (.var .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]) :=
  .sub HasTy.var (.capt .refl Subcap.var) Subcap.var

/-- `gb = c b`: the client at the second literal. -/
def C2gb : HasTy
    [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
      CapAtom.cvar (.there (.there (.there (.there .here))))]
    C2Ctx4 (.app (.there (.there (.there .here))) (.there .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
      CapAtom.cvar (.there (.there (.there (.there .here))))]) :=
  .app (T2 := arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))])
    ((var' (.there (.there (.there .here))) rfl).widen _)
    (C2abstract (.there .here) (.there (.there (.there (.there (.there .here)))))
      (.there (.there (.there (.there .here)))) (by simp) rfl)

/-- `ga = c a`: the client at the first literal. -/
def C2ga : HasTy
    [CapAtom.cvar (.there (.there (.there (.there .here)))),
      CapAtom.cvar (.there (.there (.there .here)))]
    C2Ctx3 (.app (.there (.there .here)) (.there .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there .here)))),
      CapAtom.cvar (.there (.there (.there .here)))]) :=
  .app (T2 := arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
      CapAtom.cvar (.there (.there (.there (.there .here))))])
    ((var' (.there (.there .here)) rfl).widen _)
    (C2abstract (.there .here) (.there (.there (.there (.there .here))))
      (.there (.there (.there .here))) (by simp) rfl)

/-- The term of C2. -/
def C2tm : Tm ([],c,c) :=
  .let (C2clientTm k1 k2)
    (.let (.val (.obj (C2Defs (.there (.there (.there .here))))))
      (.let (.val (.obj (C2Defs (.there (.there (.there .here))))))
        (.let (.app (.there (.there .here)) (.there .here))
          (.let (.app (.there (.there (.there .here))) (.there .here))
            (.path (.var .here))))))

/-- The type of C2. -/
def C2Ty : Ty ([],c,c) := arrowS ^ [CapAtom.cvar k1, CapAtom.cvar k2]

/-- **C2.**  One capture-polymorphic client, two literals that define the
capture member differently, and a program with use set `{κ₁,κ₂}`. -/
def C2_typed : HasTy [CapAtom.cvar k1, CapAtom.cvar k2] platCtx C2tm C2Ty :=
  .let ((C2ClientVal k1 k2).widen _)
    (.let ((C2Lit (.there (.there .here))).widen _)
      (.let ((C2Lit (.there (.there .here))).widen _)
        (.let C2ga (.let C2gb C2answer arrowWf) arrowWf) arrowWf) arrowWf) arrowWf

end Examples
end DotMNF

end Captures
