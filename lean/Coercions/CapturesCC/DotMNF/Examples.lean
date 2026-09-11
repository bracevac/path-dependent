import Coercions.CapturesCC.DotMNF.Machine

namespace CapturesCC

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
    (h : Γ.lookup x = S ^ []) : HasTyP [] Γ (.path (.var x)) (S ^ []) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  refine HasTy.sub HasTy.var (.ty (.capt ?_ hv)) hv
  rw [h]
  exact SubShape.refl

/-- `sub` at a pure type and the empty use set: only the shape changes. -/
def subS {s : Sig} {Γ : Ctx s} {t : Tm s} {S S' : Shape s}
    (h : HasTyP [] Γ t (S ^ [])) (d : SubShape Γ S S') : HasTyP [] Γ t (S' ^ []) :=
  .sub h (.ty (.capt d .refl)) .refl

/-! ### Reading an outer binder from inside a scope

A lambda body opens three binders, the body root, the arrow's capture binder
and the parameter, so an outer binder is three steps out.  A codomain and an
object body open two, so an outer binder is two steps out there. -/

/-- An outer binder, read inside a lambda body. -/
abbrev up {s : Sig} {k : Kind} (y : BVar s k) : BVar (Sig.body s) k :=
  .there (.there (.there y))

/-- An outer binder, read inside a codomain or an object body. -/
abbrev up2 {s : Sig} {k : Kind} (y : BVar s k) : BVar ((s,c),x) k := .there (.there y)

/-- `All-I` at a pure lambda: the body is derived at the empty use set and
widened to the set the rule charges it at. -/
def lam' {s : Sig} {Γ : Ctx s} {T1 : Dom s} {t : Tm (Sig.body s)} {T2 : Cod s}
    (h : HasTy [] (Γ.body T1) t T2.underRoot) (w : Ty.Wf T1) :
    HasTyP [] Γ (.val (.lam T1 t)) ((Shape.all T1 T2) ^ []) :=
  .lam (h.widen _) w

/-- `{}-I` at a pure literal, likewise. -/
def obj' {s : Sig} {Γ : Ctx s} {d : Defs ((s,c),x)} {S : Shape (s,x)}
    (h : DefsTy [] (Γ.objBody d S []) d S.underRoot) (hd : Defs.Distinct d) :
    HasTyP [] Γ (.val (.obj d)) ((Shape.mu S) ^ []) :=
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
    (hx : HasTyP U Γ (.path (.var x)) ((Shape.typ lA .top .bot) ^ D)) (S : Shape s) :
    SubShape Γ E1DomS S :=
  .trans .top (.trans (.selLower hx) (.trans (.selUpper hx) .bot))

def E1Ctx : Ctx (Sig.body ([] : Sig)) := Ctx.body .nil E1Dom

def E1x : HasTyP [] E1Ctx (.path (.var .here)) E1Dom := var' .here rfl

def E1retype : HasTyP [] E1Ctx (.path (.var .here)) E1Res := subS E1x (badBounds E1x E1ResS)

def E1body : HasTyP [] E1Ctx (.let (.path (.var .here)) (.path (.var .here))) E1Res :=
  .let E1retype (var' .here rfl)
    (.capt (.typ (.fld (.capt .top)) (.fld (.capt .top))))

def E1 : HasTyP [] Ctx.nil
    (.val (.lam E1Dom (.let (.path (.var .here)) (.path (.var .here)))))
    ((Shape.all E1Dom (.ty E1Res)) ^ []) :=
  lam' E1body (.capt (.typ .top .bot))

/-! ## E2: recursive object with a self-referential member

`ν(x. {A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y})`, allocated by a `let`,
its term member selected and applied to itself.  The application typechecks
because the exact bounds of `A` give `∀(y : x.A) x.A <: x.A`. -/

/-- `∀(y : x.A) x.A`, under the object's self binder.  The arrow's own
capture binder is between the self and the domain, so the self is one step
further out in the domain and two in the codomain. -/
def E2AS : Shape (s,x) :=
  .all ((Shape.sel (.var (.there .here)) lA) ^ [])
    (.ty ((Shape.sel (.var (.there (.there .here))) lA) ^ []))
def E2A : Ty (s,x) := E2AS ^ []
/-- The same shape one binder further out. -/
def E2AS' : Shape (s,x,x) :=
  .all ((Shape.sel (.var (.there (.there .here))) lA) ^ [])
    (.ty ((Shape.sel (.var (.there (.there (.there .here)))) lA) ^ []))
def E2A' : Ty (s,x,x) := E2AS' ^ []
/-- The object's self shape `{A : E2A..E2A} ∧ {a : E2A}`. -/
def E2Self : Shape (s,x) := .and (.typ lA E2AS E2AS) (.fld la E2A)
/-- The object's definitions. -/
def E2Defs : Defs (s,x) :=
  .and (.typ lA E2AS)
    (.trm la (.val (.lam ((Shape.sel (.var (.there .here)) lA) ^ []) (.path (.var .here)))))

theorem E2Distinct : Defs.Distinct (E2Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self shape is declaration-shaped. -/
theorem E2SelfDecl : Shape.Decl (E2Self (s := s)) := .and .typ .fld

def E2DefsTy : DefsTy [] (Ctx.objBody Γ E2Defs E2Self []) E2Defs E2Self.underRoot :=
  .and .typ (.trm (lam' (var' .here rfl) (.capt .sel)))

def E2Ctx1 : Ctx ([],x) := .cons .nil ((Shape.mu E2Self) ^ [])

def E2xMu : HasTyP [] E2Ctx1 (.path (.var .here)) ((Shape.mu E2Self) ^ []) := var' .here rfl
def E2xOpen : HasTyP [] E2Ctx1 (.path (.var .here)) (E2Self ^ []) := .recE E2xMu E2SelfDecl
def E2xFld : HasTyP [] E2Ctx1 (.path (.var .here)) ((Shape.fld la E2A) ^ []) :=
  subS E2xOpen .and2
def E2proj : HasTyP [] E2Ctx1 (.proj .here la) E2A := .proj E2xFld

def E2Ctx2 : Ctx ([],x,x) := .cons E2Ctx1 E2A

def E2f : HasTyP [] E2Ctx2 (.path (.var .here)) E2A' := var' .here rfl
def E2xMu2 : HasTyP [] E2Ctx2 (.path (.var (.there .here))) ((Shape.mu E2Self) ^ []) :=
  var' (.there .here) rfl
def E2xOpen2 : HasTyP [] E2Ctx2 (.path (.var (.there .here)))
    ((Shape.and (.typ lA E2AS' E2AS') (.fld la E2A')) ^ []) := .recE E2xMu2 E2SelfDecl
/-- `∀(y : x.A) x.A <: x.A`, by the lower bound of the exact member `A`. -/
def E2fArg : HasTyP [] E2Ctx2 (.path (.var .here))
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  subS E2f (.selLower (subS E2xOpen2 .and1))
def E2app : HasTyP [] E2Ctx2 (.app .here .here)
    ((Shape.sel (.var (.there .here)) lA) ^ []) :=
  .app E2f E2fArg

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : HasTyP [] Ctx.nil
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

def E3Ctx1 : Ctx (Sig.body ([] : Sig)) := Ctx.body .nil E3Dom
def E3Ctx2 : Ctx (Sig.body (Sig.body ([] : Sig))) := Ctx.body E3Ctx1 E3T2

def E3xDom : HasTyP [] E3Ctx2 (.path (.var (up .here))) E3Dom := var' (up .here) rfl
def E3xLo : HasTyP [] E3Ctx2 (.path (.var (up .here)))
    ((Shape.typ lA .bot E3T1S) ^ []) := subS E3xDom .and1
def E3xHi : HasTyP [] E3Ctx2 (.path (.var (up .here)))
    ((Shape.typ lA E3T2S .top) ^ []) := subS E3xDom .and2
/-- `T₂ <: x.A <: T₁`: the shared member, used at both bounds. -/
def E3sub : SubShape E3Ctx2 E3T2S E3T1S := .trans (.selLower E3xHi) (.selUpper E3xLo)
def E3z : HasTyP [] E3Ctx2 (.path (.var .here)) E3T1 := subS (var' .here rfl) E3sub

def E3body : HasTyP [] E3Ctx2 (.let (.path (.var .here)) (.path (.var .here))) E3T1 :=
  .let E3z (var' .here rfl) (.capt (.fld (.capt .top)))

def E3inner : HasTyP [] E3Ctx1
    (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here)))))
    ((Shape.all E3T2 (.ty E3T1)) ^ []) :=
  lam' E3body (.capt (.fld (.capt .top)))

/-- `λ(x : {A : ⊥..T₁} ∧ {A : T₂..⊤}). λ(z : T₂). let y = z in y`. -/
def E3 : HasTyP [] Ctx.nil
    (.val (.lam E3Dom (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here)))))))
    ((Shape.all E3Dom (.ty ((Shape.all E3T2 (.ty E3T1)) ^ []))) ^ []) :=
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

def E4Ctx1 : Ctx (Sig.body ([] : Sig)) := Ctx.body .nil E4X
def E4Ctx2 : Ctx (Sig.body (Sig.body ([] : Sig))) := Ctx.body E4Ctx1 E4S
def E4Ctx3 : Ctx (Sig.body (Sig.body (Sig.body ([] : Sig)))) := Ctx.body E4Ctx2 E4Int

/-- The type of `g = λ(y : w.A). y`, at the binder `w` it reads. -/
def E4GS (w : BVar s .var) : Shape s :=
  .all ((Shape.sel (.var (.there w)) lA) ^ [])
    (.ty ((Shape.sel (.var (.there (.there w))) lA) ^ []))
def E4G (w : BVar s .var) : Ty s := E4GS w ^ []

def E4x : HasTyP [] E4Ctx3 (.path (.var (up (up .here)))) E4X :=
  var' (up (up .here)) rfl
/-- `S <: x.B <: T`, the step with no realizer. -/
def E4ST : SubShape E4Ctx3 E4SS E4TS := .trans (.selLower E4x) (.selUpper E4x)
def E4wT : HasTyP [] E4Ctx3 (.path (.var (up .here))) E4T :=
  subS (var' (up .here) rfl) E4ST
def E4g : HasTyP [] E4Ctx3
    (.val (.lam ((Shape.sel (.var (.there (up .here))) lA) ^ []) (.path (.var .here))))
    (E4G (up .here)) :=
  lam' (var' .here rfl) (.capt .sel)

def E4Ctx4 : Ctx (Sig.body (Sig.body (Sig.body ([] : Sig))),x) :=
  .cons E4Ctx3 (E4G (up .here))

def E4x4 : HasTyP [] E4Ctx4 (.path (.var (.there (up (up .here))))) E4X :=
  var' (.there (up (up .here))) rfl
def E4ST4 : SubShape E4Ctx4 E4SS E4TS := .trans (.selLower E4x4) (.selUpper E4x4)
def E4wT4 : HasTyP [] E4Ctx4 (.path (.var (.there (up .here)))) E4T :=
  subS (var' (.there (up .here)) rfl) E4ST4
/-- `n : Int <: w.A`. -/
def E4nA : HasTyP [] E4Ctx4 (.path (.var (.there .here)))
    ((Shape.sel (.var (.there (up .here))) lA) ^ []) :=
  subS (var' (.there .here) rfl) (.selLower E4wT4)
def E4gv : HasTyP [] E4Ctx4 (.path (.var .here)) (E4G (.there (up .here))) := var' .here rfl
def E4app : HasTyP [] E4Ctx4 (.app .here (.there .here))
    ((Shape.sel (.var (.there (up .here))) lA) ^ []) := .app E4gv E4nA

def E4let : HasTyP [] E4Ctx3
    (.let (.val (.lam ((Shape.sel (.var (.there (up .here))) lA) ^ []) (.path (.var .here))))
      (.app .here (.there .here)))
    ((Shape.sel (.var (up .here)) lA) ^ []) :=
  .let E4g E4app (.capt .sel)

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : HasTyP [] Ctx.nil
    (.val (.lam E4X (.val (.lam E4S (.val (.lam E4Int
      (.let (.val (.lam ((Shape.sel (.var (.there (up .here))) lA) ^ []) (.path (.var .here))))
        (.app .here (.there .here)))))))))
    ((Shape.all E4X
      (.ty ((Shape.all E4S
        (.ty ((Shape.all E4Int (.ty ((Shape.sel (.var (up2 .here)) lA) ^ []))) ^ []))) ^ []))) ^ []) :=
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
def E5F : Ty s := (Shape.all E5AT (.ty ((Shape.mu E5Self) ^ []))) ^ []
/-- `μ(z. {a : w.A})`, the type of `f w` in the scope of `w`, `f`. -/
def E5Owned : Ty (s,x,x) :=
  (Shape.mu (.fld la ((Shape.sel (.var (.there (.there .here))) lA) ^ []))) ^ []
/-- The same type one binder further out. -/
def E5Owned' : Ty (s,x,x,x) :=
  (Shape.mu (.fld la ((Shape.sel (.var (.there (.there (.there .here)))) lA) ^ []))) ^ []
/-- The definitions of the literal `ν(z. {a = v})`, under the class root and
the self. -/
def E5Defs : Defs ((s,x,c),x) := .trm la (.path (.var (up2 .here)))
/-- The body of `f`: `ν(z. {a = v})`. -/
def E5Obj : Tm (Sig.body s) := .val (.obj E5Defs)

def E5Ctx1 : Ctx (Sig.body ([] : Sig)) := Ctx.body .nil E5AT
def E5Ctxv : Ctx (Sig.body (Sig.body ([] : Sig))) := Ctx.body E5Ctx1 E5AT
def E5Ctxz : Ctx ((Sig.body (Sig.body ([] : Sig)),c),x) :=
  Ctx.objBody E5Ctxv E5Defs E5Self []

def E5v : HasTyP [] E5Ctxz (.path (.var (up2 .here))) E5AT := var' (up2 .here) rfl
/-- The field body: `v : ⊤ <: v.A`, by the lower bound of `v`'s member. -/
def E5field : HasTyP [] E5Ctxz (.path (.var (up2 .here)))
    ((Shape.sel (.var (up2 .here)) lA) ^ []) :=
  subS (subS E5v .top) (.selLower E5v)
def E5DefsTy : DefsTy [] E5Ctxz E5Defs E5Self.underRoot := .trm E5field

def E5ObjTy : HasTyP [] E5Ctxv E5Obj ((Shape.mu E5Self) ^ []) :=
  obj' E5DefsTy .trm
def E5fVal : HasTyP [] E5Ctx1 (.val (.lam E5AT E5Obj)) E5F :=
  lam' E5ObjTy (.capt (.typ .top .top))

def E5Ctxf : Ctx (Sig.body ([] : Sig),x) := .cons E5Ctx1 E5F

def E5fv : HasTyP [] E5Ctxf (.path (.var .here)) E5F := var' .here rfl
def E5w : HasTyP [] E5Ctxf (.path (.var (.there .here))) E5AT := var' (.there .here) rfl
/-- `f w : μ(z. {a : w.A})`: the application renames `v`'s block to `w`. -/
def E5o : HasTyP [] E5Ctxf (.app .here (.there .here)) E5Owned := .app E5fv E5w

def E5Ctxo : Ctx (Sig.body ([] : Sig),x,x) := .cons E5Ctxf E5Owned

def E5oMu : HasTyP [] E5Ctxo (.path (.var .here)) E5Owned' := var' .here rfl
def E5oOpen : HasTyP [] E5Ctxo (.path (.var .here))
    ((Shape.fld la ((Shape.sel (.var (.there (.there .here))) lA) ^ [])) ^ []) :=
  .recE E5oMu .fld
def E5proj : HasTyP [] E5Ctxo (.proj .here la)
    ((Shape.sel (.var (.there (.there .here))) lA) ^ []) :=
  .proj E5oOpen

def E5oLet : HasTyP [] E5Ctxf (.let (.app .here (.there .here)) (.proj .here la))
    ((Shape.sel (.var (.there .here)) lA) ^ []) := .let E5o E5proj (.capt .sel)

def E5fLet : HasTyP [] E5Ctx1
    (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))
    ((Shape.sel (.var .here) lA) ^ []) := .let E5fVal E5oLet (.capt .sel)

def E5 : HasTyP [] Ctx.nil
    (.val (.lam E5AT
      (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))))
    ((Shape.all E5AT (.ty ((Shape.sel (.var .here) lA) ^ []))) ^ []) :=
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
def E6Defs : Defs ((s,x,c),x) :=
  .and (.typ lT E6IntS) (.trm lv (.path (.var (up2 .here))))

theorem E6Distinct : Defs.Distinct (E6Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self shape is declaration-shaped. -/
theorem E6SelfDecl : Shape.Decl (E6Self (s := s)) := .and .typ .fld

def E6Ctx1 : Ctx ([],x) := .cons .nil E6Int
def E6Ctxz : Ctx (([],x,c),x) := Ctx.objBody E6Ctx1 E6Defs E6Self []

def E6xMu : HasTyP [] E6Ctxz (.path (.var .here)) ((Shape.mu E6Self) ^ []) := var' .here rfl
def E6xOpen : HasTyP [] E6Ctxz (.path (.var .here)) (E6Self.underRoot ^ []) := .recE E6xMu E6SelfDecl
def E6xTyp : HasTyP [] E6Ctxz (.path (.var .here)) ((Shape.typ lT E6IntS E6IntS) ^ []) :=
  subS E6xOpen .and1
/-- `n : Int <: x.T`, by the lower bound of the exact member `T`. -/
def E6nT : HasTyP [] E6Ctxz (.path (.var (up2 .here)))
    ((Shape.sel (.var .here) lT) ^ []) :=
  subS (var' (up2 .here) rfl) (.selLower E6xTyp)

def E6DefsTy : DefsTy [] E6Ctxz E6Defs E6Self.underRoot := .and .typ (.trm E6nT)

/-- `λ(n : Int). ν(x. {T = Int} ∧ {v = n})`. -/
def E6 : HasTyP [] E6Ctx1 (.val (.obj E6Defs)) ((Shape.mu E6Self) ^ []) :=
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

def E7DefsTy : DefsTy [] (Ctx.objBody Γ E7Defs E7Self []) E7Defs E7Self.underRoot :=
  .and .typ .typ

/-- `ν(x. {A = x.B} ∧ {B = x.A})`. -/
def E7 : HasTyP [] Ctx.nil (.val (.obj E7Defs)) ((Shape.mu E7Self) ^ []) :=
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

def E8Ctx1 : Ctx (Sig.body ([] : Sig)) := Ctx.body Ctx.nil E8Dom
def E8Ctx2 : Ctx (Sig.body (Sig.body ([] : Sig))) := Ctx.body E8Ctx1 (E8Ref (.there .here))

/-- `y : x.A ∧ {a : ⊤}`. -/
def E8y : HasTyP [] E8Ctx2 (.path (.var .here)) (E8Ref (up .here)) := var' .here rfl

/-- `x : {A : ⊥..{a : ⊤}}`. -/
def E8x : HasTyP [] E8Ctx2 (.path (.var (up .here))) E8Dom := var' (up .here) rfl

/-- `And₂`: the declaration operand of the refinement. -/
def E8yFld2 : HasTyP [] E8Ctx2 (.path (.var .here))
    ((Shape.fld la (.top ^ [])) ^ []) := subS E8y .and2

/-- `And₁`: the abstract type itself. -/
def E8yA : HasTyP [] E8Ctx2 (.path (.var .here))
    ((Shape.sel (.var (up .here)) lA) ^ []) := subS E8y .and1

/-- `Sel-<:`: the upper bound of `x`'s member `A`. -/
def E8Upper : SubShape E8Ctx2 (.sel (.var (up .here)) lA) (.fld la (.top ^ [])) :=
  .selUpper E8x

/-- The same conclusion as `E8yFld2`, the other way round. -/
def E8yFld1 : HasTyP [] E8Ctx2 (.path (.var .here))
    ((Shape.fld la (.top ^ [])) ^ []) := subS E8yA E8Upper

/-- `And-I`: the two views of `y` recombined into the refinement. -/
def E8AndI : HasTyP [] E8Ctx2 (.path (.var .here)) (E8Ref (up .here)) :=
  .andI E8yA E8yFld2

/-- `y.a`, through `And₂`. -/
def E8Body2 : HasTyP [] E8Ctx2 (.proj .here la) (.top ^ []) := .proj E8yFld2

/-- `y.a`, through `And₁` and `Sel-<:`. -/
def E8Body1 : HasTyP [] E8Ctx2 (.proj .here la) (.top ^ []) := .proj E8yFld1

/-- `λ(x). λ(y). y.a`, with the `And₂` derivation of the body. -/
def E8 : HasTyP [] Ctx.nil
    (.val (.lam E8Dom (.val (.lam (E8Ref (.there .here)) (.proj .here la)))))
    ((Shape.all E8Dom (.ty ((Shape.all (E8Ref (.there .here)) (.ty (.top ^ []))) ^ []))) ^ []) :=
  lam' (lam' E8Body2 E8RefWf) E8DomWf

/-- The same term, with the `And₁`-then-`Sel-<:` derivation of the body. -/
def E8b : HasTyP [] Ctx.nil
    (.val (.lam E8Dom (.val (.lam (E8Ref (.there .here)) (.proj .here la)))))
    ((Shape.all E8Dom (.ty ((Shape.all (E8Ref (.there .here)) (.ty (.top ^ []))) ^ []))) ^ []) :=
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
    (h : Γ.lookup x = S ^ C) : HasTyP [CapAtom.var x] Γ (.path (.var x)) (S ^ C) := by
  have hv : Subcap Γ [CapAtom.var x] C := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  refine HasTy.sub HasTy.var (.ty (.capt ?_ hv)) .refl
  rw [h]
  exact SubShape.refl

/-- `Var` at a binder, at the refined capture set `{x}`: the shape is read
off the context. -/
def varSelf {s : Sig} {Γ : Ctx s} (x : BVar s .var) {S : Shape s}
    (h : (Γ.lookup x).shape = S) :
    HasTyP [CapAtom.var x] Γ (.path (.var x)) (S ^ [CapAtom.var x]) := by
  subst h
  exact HasTy.var

/-- `sub` when only the shape changes, at an arbitrary capture set and use
set. -/
def subC {s : Sig} {Γ : Ctx s} {U C : CaptureSet s} {t : Tm s} {S S' : Shape s}
    (h : HasTyP U Γ t (S ^ C)) (d : SubShape Γ S S') : HasTyP U Γ t (S' ^ C) :=
  .sub h (.ty (.capt d .refl)) .refl

/-- `sub` on the use set alone, along a syntactic inclusion. -/
def HasTy.widenTo {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {T : Ty s}
    (h : HasTyP U Γ t T) (hs : CaptureSet.Subset U U') : HasTyP U' Γ t T :=
  .sub h (ESub.refl (.ty T)) (.elem hs)

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
def arrowS : Shape s := .all unitTy (.ty unitTy)
/-- The type of a capability over the capture binder `κ`. -/
def capTy (κ : BVar s .cap) : Ty s := arrowS ^ [CapAtom.cvar κ]

theorem arrowWf : Ty.Wf (arrowS ^ C : Ty s) := .capt (.all (.capt .top) (.ty (.capt .top)))
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

/-- `κ₁, κ₂, f : (Unit → Unit) ^ {κ₁}`, the body of the outer lambda. -/
def S3Ctx1 : Ctx (Sig.body ([],c,c)) :=
  Ctx.body platCtx (capTy (.there (.there .here)))

/-- The context inside the literal: the class root and the self binder `z`
on top of `S3Ctx1`. -/
def S3Ctxz : Ctx ((Sig.body ([],c,c),c),x) :=
  Ctx.objBody S3Ctx1 (S3Defs (up2 .here)) (S3SelfAt .here (.there .here)) []

def S3zMu : HasTyP [] S3Ctxz (.path (.var .here))
    ((Shape.mu (S3SelfAt .here (.there (up2 .here)))) ^ []) := var' .here rfl

def S3zOpen : HasTyP [] S3Ctxz (.path (.var .here))
    ((S3SelfAt .here (up2 .here)) ^ []) := .recE S3zMu S3SelfDecl

def S3zTyp : HasTyP [] S3Ctxz (.path (.var .here))
    ((Shape.typ lA (S3Box (up2 .here)) (S3Box (up2 .here))) ^ []) :=
  subS S3zOpen .and1

/-- `□ f : □((Unit → Unit) ^ {f})`, a pure value. -/
def S3boxf : HasTyP [] S3Ctxz (.val (.box (up2 .here)))
    ((S3Box (up2 .here)) ^ []) := .box (varSelf (up2 .here) rfl)

/-- The field body, brought to the declared type `z.A ^ {}` by the lower
bound of the exact member `A`. -/
def S3field : HasTyP [] S3Ctxz (.val (.box (up2 .here)))
    ((Shape.sel (.var .here) lA) ^ []) := subS S3boxf (.selLower S3zTyp)

def S3DefsTy : DefsTy [] S3Ctxz (S3Defs (up2 .here))
    (S3SelfAt (.here : BVar (Sig.body ([],c,c),x) .var) (.there .here)).underRoot :=
  .and .typ (.trm S3field)

/-- The literal is pure: its capture set is `{}`. -/
def S3Lit : HasTyP [] S3Ctx1 (.val (.obj (S3Defs (up2 .here))))
    ((Shape.mu (S3SelfAt .here (.there .here))) ^ []) :=
  obj' S3DefsTy (S3Distinct _)

/-- The context after the literal's `let`. -/
def S3Ctxo : Ctx (Sig.body ([],c,c),x) :=
  S3Ctx1.cons ((Shape.mu (S3SelfAt .here (.there .here))) ^ [])

def S3oMu : HasTyP [] S3Ctxo (.path (.var .here))
    ((Shape.mu (S3SelfAt .here (.there (.there .here)))) ^ []) := var' .here rfl

def S3oFld : HasTyP [] S3Ctxo (.path (.var .here))
    ((Shape.fld lelem ((Shape.sel (.var .here) lA) ^ [])) ^ []) :=
  subS (.recE S3oMu S3SelfDecl) .and2

def S3proj : HasTyP [] S3Ctxo (.proj .here lelem)
    ((Shape.sel (.var .here) lA) ^ []) := .proj S3oFld

/-- The context after the projection's `let`. -/
def S3Ctxe : Ctx (Sig.body ([],c,c),x,x) :=
  S3Ctxo.cons ((Shape.sel (.var .here) lA) ^ [])

def S3e : HasTyP [] S3Ctxe (.path (.var .here))
    ((Shape.sel (.var (.there .here)) lA) ^ []) := var' .here rfl

def S3oTyp : HasTyP [] S3Ctxe (.path (.var (.there .here)))
    ((Shape.typ lA (S3Box (.there (.there .here))) (S3Box (.there (.there .here)))) ^ []) :=
  subS (.recE (var' (.there .here) rfl) S3SelfDecl) .and1

/-- The element, opened by the upper bound of the member `A`. -/
def S3eBox : HasTyP [] S3Ctxe (.path (.var .here))
    ((S3Box (.there (.there .here))) ^ []) := subS S3e (.selUpper S3oTyp)

/-- `{f} ⊸ e`: the unboxing charges the boxed set to the use set. -/
def S3unbox : HasTyP [CapAtom.var (.there (.there .here))] S3Ctxe
    (.unbox [CapAtom.var (.there (.there .here))] .here)
    (arrowS ^ [CapAtom.var (.there (.there .here))]) :=
  .unbox (S3eBox.widen _) .refl

def S3innerLet : HasTyP [CapAtom.var (.there .here)] S3Ctxo
    (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here))
    (arrowS ^ [CapAtom.var (.there .here)]) :=
  .let (S3proj.widen _) S3unbox arrowWf

/-- The client, typed with use set `{f}`. -/
def S3body : HasTyP [CapAtom.var .here] S3Ctx1
    (.let (.val (.obj (S3Defs (up2 .here))))
      (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here)))
    (arrowS ^ [CapAtom.var .here]) :=
  .let (S3Lit.widen _) S3innerLet arrowWf

/-- The term of S3. -/
def S3tm : Tm ([],c,c) :=
  .val (.lam (capTy (.there (.there .here)))
    (.let (.val (.obj (S3Defs (up2 .here))))
      (.let (.proj .here lelem) (.unbox [CapAtom.var (.there (.there .here))] .here))))

/-- The type of S3. -/
def S3Ty : Ty ([],c,c) :=
  (Shape.all (capTy (.there (.there .here))) (.ty (arrowS ^ [CapAtom.var .here]))) ^ []

/-- **S3.**  A type member instantiated with a boxed capturing type, a field
declared at that member and defined by a box, and a client that projects and
unboxes at the use set `{f}`. -/
def S3_typed : HasTyP [] platCtx S3tm S3Ty := .lam S3body arrowWf

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

/-- `κ₁, κ₂, f₁ : (Unit → Unit) ^ {κ₁}`, the body of the outer lambda. -/
def C7Ctx1 : Ctx (Sig.body ([],c,c)) := Ctx.body platCtx (capTy (.there (.there .here)))

/-- `κ₁, κ₂, f₁, f₂ : (Unit → Unit) ^ {κ₂}`, the body of the inner one. -/
def C7Ctx2 : Ctx (Sig.body (Sig.body ([],c,c))) := Ctx.body C7Ctx1 (capTy (.there (up .here)))

/-- `κ₁` and `κ₂` read inside the two lambdas. -/
abbrev C7k1 : BVar (Sig.body (Sig.body ([],c,c))) .cap := up (up (.there .here))
abbrev C7k2 : BVar (Sig.body (Sig.body ([],c,c))) .cap := up (up .here)

/-- The container's declaration shape under the self binder of the
literal. -/
def C7SelfZ : Shape (Sig.body (Sig.body ([],c,c)),x) :=
  C7SelfAt (.there C7k1) (.there C7k2)

/-- The container's definitions under the class root and the self binder. -/
def C7DefsZ : Defs ((Sig.body (Sig.body ([],c,c)),c),x) :=
  C7Defs (up2 (up .here)) (up2 .here)

/-- The context inside the container: the class root and the self binder `z`
on top. -/
def C7Ctxz : Ctx ((Sig.body (Sig.body ([],c,c)),c),x) :=
  Ctx.objBody C7Ctx2 C7DefsZ C7SelfZ []

/-- `□ f₁ : □((Unit → Unit) ^ {κ₁}) ^ {}`, at the field's declared type. -/
def C7box1 : HasTyP [] C7Ctxz (.val (.box (up2 (up .here))))
    ((Shape.box (capTy (up2 C7k1))) ^ []) :=
  .box (varAt (up2 (up .here)) rfl)

/-- `□ f₂`, likewise. -/
def C7box2 : HasTyP [] C7Ctxz (.val (.box (up2 .here)))
    ((Shape.box (capTy (up2 C7k2))) ^ []) :=
  .box (varAt (up2 .here) rfl)

def C7DefsTy : DefsTy [] C7Ctxz C7DefsZ C7SelfZ.underRoot :=
  .and (.trm C7box1) (.trm C7box2)

/-- **The container is pure.**  Its two fields hold capabilities, and its
capture set is `{}`. -/
def C7Lit : HasTyP [] C7Ctx2 (.val (.obj C7DefsZ)) ((Shape.mu C7SelfZ) ^ []) :=
  obj' C7DefsTy (C7Distinct _ _)

/-- The context after the container's `let`. -/
def C7Ctxo : Ctx (Sig.body (Sig.body ([],c,c)),x) :=
  C7Ctx2.cons ((Shape.mu C7SelfZ) ^ [])

def C7oMu : HasTyP [] C7Ctxo (.path (.var .here))
    ((Shape.mu (C7SelfAt (.there (.there C7k1)) (.there (.there C7k2)))) ^ []) :=
  var' .here rfl

def C7oFld : HasTyP [] C7Ctxo (.path (.var .here))
    ((Shape.fld le1 ((Shape.box (capTy (.there C7k1))) ^ [])) ^ []) :=
  subS (.recE C7oMu C7SelfDecl) .and1

def C7proj : HasTyP [] C7Ctxo (.proj .here le1)
    ((Shape.box (capTy (.there C7k1))) ^ []) := .proj C7oFld

/-- The context after the projection's `let`. -/
def C7Ctxe : Ctx (Sig.body (Sig.body ([],c,c)),x,x) :=
  C7Ctxo.cons ((Shape.box (capTy (.there C7k1))) ^ [])

def C7e : HasTyP [] C7Ctxe (.path (.var .here))
    ((Shape.box (capTy (.there (.there C7k1)))) ^ []) :=
  var' .here rfl

/-- `{κ₁} ⊸ e`: unboxing the first element charges `{κ₁}` and nothing
else. -/
def C7unbox : HasTyP [CapAtom.cvar (.there (.there C7k1))] C7Ctxe
    (.unbox [CapAtom.cvar (.there (.there C7k1))] .here)
    (arrowS ^ [CapAtom.cvar (.there (.there C7k1))]) :=
  .unbox (C7e.widen _) .refl

/-- The two `let`s and the unboxing, the client of C7. -/
def C7clientTm : Tm (Sig.body (Sig.body ([],c,c))) :=
  .let (.val (.obj C7DefsZ))
    (.let (.proj .here le1)
      (.unbox [CapAtom.cvar (.there (.there C7k1))] .here))

def C7innerLet :
    HasTyP [CapAtom.cvar (.there C7k1)] C7Ctxo
      (.let (.proj .here le1)
        (.unbox [CapAtom.cvar (.there (.there C7k1))] .here))
      (arrowS ^ [CapAtom.cvar (.there C7k1)]) :=
  .let (C7proj.widen _) C7unbox arrowWf

/-- The client, typed with use set `{κ₁}`. -/
def C7body : HasTyP [CapAtom.cvar C7k1] C7Ctx2 C7clientTm
    (arrowS ^ [CapAtom.cvar C7k1]) :=
  .let (C7Lit.widen _) C7innerLet arrowWf

/-- The term of C7. -/
def C7tm : Tm ([],c,c) :=
  .val (.lam (capTy (.there (.there .here)))
    (.val (.lam (capTy (.there (up .here))) C7clientTm)))

/-- The type of C7. -/
def C7Ty : Ty ([],c,c) :=
  (Shape.all (capTy (.there (.there .here)))
    (.ty ((Shape.all (capTy (.there (.there (.there .here))))
      (.ty (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))])))
      ^ [CapAtom.cvar (.there (.there (.there .here)))]))) ^ []

/-- **C7.**  A pure container of two boxed capabilities, and a client that
unboxes the first element at the use set `{κ₁}`. -/
def C7_typed : HasTyP [] platCtx C7tm C7Ty :=
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
def C2run {s : Sig} {Γ : Ctx s} {κ : BVar s .cap} :
    HasTyP [] (Γ.objBody (C2Defs (up2 κ)) (C2PreAt .here (.there κ)) [])
      (.val (.lam unitTy (.path (.var .here))))
      (arrowS ^ [CapAtom.sel .here lC]) :=
  .lam ((var' .here rfl).widen _) unitWf

/-- A literal, at its precise type: pure, with `C` defined as `{κ}`. -/
def C2Lit {s : Sig} {Γ : Ctx s} (κ : BVar s .cap) :
    HasTyP [] Γ (.val (.obj (C2Defs (up2 κ)))) (C2PreTy κ) :=
  obj' (.and .cap (.trm C2run)) (C2Distinct _)

/-- A literal's variable, retyped at the abstract type: `Rec-E`, then `Cap`
on the member, then `Rec-I`, then the declared capture set. -/
def C2abstract {s : Sig} {Γ : Ctx s} {U : CaptureSet s} (x : BVar s .var)
    (κ1 κ2 : BVar s .cap) {κ : BVar s .cap}
    (hm : CapAtom.cvar κ ∈ [CapAtom.cvar κ1, CapAtom.cvar κ2])
    (h : Γ.lookup x = C2PreTy κ) :
    HasTyP U Γ (.path (.var x)) (C2AbsTy κ1 κ2) :=
  .sub
    (HasTy.recI
      (subS (.recE (var' x h) C2PreDecl)
        (.and (.trans .and1 (.cap (.elem (CaptureSet.nil_subset _)) (.elem (sub_one hm))))
          .and2))
      C2AbsDecl)
    (.ty (.capt .refl (.elem (CaptureSet.nil_subset _)))) (Subcap.empty U)

/-! ### The client

Three contexts: the abstract object `x`, the unit argument `u`, and the
closure `g` the client reads off `x`. -/

def C2CtxX {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (Sig.body s) :=
  Ctx.body Γ (C2AbsTy (.there κ1) (.there κ2))
def C2CtxU {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (Sig.body (Sig.body s)) :=
  Ctx.body (C2CtxX Γ κ1 κ2) unitTy
def C2CtxG {s : Sig} (Γ : Ctx s) (κ1 κ2 : BVar s .cap) : Ctx (Sig.body (Sig.body s),x) :=
  (C2CtxU Γ κ1 κ2).cons (arrowS ^ [CapAtom.sel (up .here) lC])

/-- `x`, opened at the abstract capture member, beside `g`. -/
def C2xCap {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTyP [CapAtom.var (.there (up .here))] (C2CtxG Γ κ1 κ2)
      (.path (.var (.there (up .here))))
      ((Shape.cap lC [] [.cvar (.there (up (up κ1))),
        .cvar (.there (up (up κ2)))]) ^ [CapAtom.var (.there (up .here))]) :=
  subC (.recE (varSelf (.there (up .here)) rfl) C2AbsDecl) .and1

/-- `g u`, charged to `{κ₁,κ₂}` by `sc-var` and the upper bound of the
abstract member. -/
def C2call {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTyP [CapAtom.cvar (.there (up (up κ1))),
        CapAtom.cvar (.there (up (up κ2)))]
      (C2CtxG Γ κ1 κ2) (.app .here (.there .here)) (.top ^ []) :=
  .app (T2 := .ty unitTy)
    (.sub (varSelf .here rfl) (.ty (.capt .refl (.trans Subcap.var (.selUpper C2xCap))))
      (.trans Subcap.var (.selUpper C2xCap)))
    ((var' (.there .here) rfl).widen _)

/-- The client's body: read the closure off the abstract member and call
it. -/
def C2clientBody {s : Sig} {Γ : Ctx s} {κ1 κ2 : BVar s .cap} :
    HasTyP [CapAtom.cvar (up (up κ1)), CapAtom.cvar (up (up κ2))]
      (C2CtxU Γ κ1 κ2)
      (.let (.proj (up .here) lrun) (.app .here (.there .here))) (.top ^ []) :=
  .let
    (.sub (.proj (subC (.recE (varSelf (up .here) rfl) C2AbsDecl) .and2))
      (ESub.refl _) Subcap.var)
    C2call (.capt .top)

/-- The type of the client. -/
def C2ClientTy (κ1 κ2 : BVar s .cap) : Ty s :=
  (Shape.all (C2AbsTy (.there κ1) (.there κ2))
    (.ty (arrowS ^ [CapAtom.cvar (up2 κ1), CapAtom.cvar (up2 κ2)]))) ^ []

/-- The client's term. -/
def C2clientTm (κ1 κ2 : BVar s .cap) : Tm s :=
  .val (.lam (C2AbsTy (.there κ1) (.there κ2))
    (.val (.lam unitTy (.let (.proj (up .here) lrun) (.app .here (.there .here))))))

/-- The client, a value: capture polymorphic in the member `C`. -/
def C2ClientVal {s : Sig} {Γ : Ctx s} (κ1 κ2 : BVar s .cap) :
    HasTyP [] Γ (C2clientTm κ1 κ2) (C2ClientTy κ1 κ2) :=
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
def C2answer : HasTyP
    [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]
    C2Ctx5 (.path (.var .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]) :=
  .sub HasTy.var (.ty (.capt .refl Subcap.var)) Subcap.var

/-- `gb = c b`: the client at the second literal. -/
def C2gb : HasTyP
    [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
      CapAtom.cvar (.there (.there (.there (.there .here))))]
    C2Ctx4 (.app (.there (.there (.there .here))) (.there .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
      CapAtom.cvar (.there (.there (.there (.there .here))))]) :=
  .app (T2 := .ty (arrowS ^ [CapAtom.cvar
        (.there (.there (.there (.there (.there (.there (.there .here))))))),
      CapAtom.cvar (.there (.there (.there (.there (.there (.there .here))))))]))
    ((var' (.there (.there (.there .here))) rfl).widen _)
    (C2abstract (.there .here) (.there (.there (.there (.there (.there .here)))))
      (.there (.there (.there (.there .here)))) (by simp) rfl)

/-- `ga = c a`: the client at the first literal. -/
def C2ga : HasTyP
    [CapAtom.cvar (.there (.there (.there (.there .here)))),
      CapAtom.cvar (.there (.there (.there .here)))]
    C2Ctx3 (.app (.there (.there .here)) (.there .here))
    (arrowS ^ [CapAtom.cvar (.there (.there (.there (.there .here)))),
      CapAtom.cvar (.there (.there (.there .here)))]) :=
  .app (T2 := .ty (arrowS ^ [CapAtom.cvar
        (.there (.there (.there (.there (.there (.there .here)))))),
      CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]))
    ((var' (.there (.there .here)) rfl).widen _)
    (C2abstract (.there .here) (.there (.there (.there (.there .here))))
      (.there (.there (.there .here))) (by simp) rfl)

/-- The term of C2. -/
def C2tm : Tm ([],c,c) :=
  .let (C2clientTm k1 k2)
    (.let (.val (.obj (C2Defs (.there (.there (.there (.there .here)))))))
      (.let (.val (.obj (C2Defs (.there (.there (.there (.there .here)))))))
        (.let (.app (.there (.there .here)) (.there .here))
          (.let (.app (.there (.there (.there .here))) (.there .here))
            (.path (.var .here))))))

/-- The type of C2. -/
def C2Ty : Ty ([],c,c) := arrowS ^ [CapAtom.cvar k1, CapAtom.cvar k2]

/-- **C2.**  One capture-polymorphic client, two literals that define the
capture member differently, and a program with use set `{κ₁,κ₂}`. -/
def C2_typed : HasTyP [CapAtom.cvar k1, CapAtom.cvar k2] platCtx C2tm C2Ty :=
  .let ((C2ClientVal k1 k2).widen _)
    (.let ((C2Lit (.there (.there .here))).widen _)
      (.let ((C2Lit (.there (.there .here))).widen _)
        (.let C2ga (.let C2gb C2answer arrowWf) arrowWf) arrowWf) arrowWf) arrowWf

/-! ## Stage A3b: `any` by position

The examples below are written with `any` and expanded before they are
typed.  `any` is a notation: it stands for the capture set its position
reads, which is the set of the enclosing arrow or object together with that
former's own binder, and at the top of a program the platform's own set.
`AnyOk` is decided on the written type, `expand` at the platform set is
computed, and the derivation that follows is a derivation of stage A3a at
the expanded type. -/

/-- The platform set: the two rigid capture binders.  `fs`, the file system
of S1 and S2, is `κ₁`. -/
def platSet : CaptureSet ([],c,c) := [CapAtom.cvar k1, CapAtom.cvar k2]

/-- Subcapturing of a set from its head and its tail: `Subcap.union` at
`[a] ∪ C`, which is `a :: C`. -/
def Subcap.consAtom {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C D : CaptureSet s}
    (h : Subcap Γ [a] D) (hC : Subcap Γ C D) : Subcap Γ (a :: C) D :=
  Subcap.union (C1 := [a]) (C2 := C) h hC

/-- `sub` on the use set alone, along subcapturing. -/
def HasTy.useSub {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {T : Ty s}
    (h : HasTyP U Γ t T) (f : Subcap Γ U U') : HasTyP U' Γ t T :=
  .sub h (ESub.refl (.ty T)) f

/-- `sub` on the capture set of the type alone, along subcapturing. -/
def HasTy.captTo {s : Sig} {Γ : Ctx s} {U C C' : CaptureSet s} {t : Tm s} {S : Shape s}
    (h : HasTyP U Γ t (S ^ C)) (f : Subcap Γ C C') : HasTyP U Γ t (S ^ C') :=
  .sub h (.ty (.capt .refl f)) .refl

/-! ## Labels of the A3b examples -/

/-- Term label `read`. -/
def lread : Label := .trm 7
/-- Term label `next`. -/
def lnext : Label := .trm 8

/-! ## S1: `withFile` with an explicit capture parameter

```text
withFile : (∀(cp : (μ(c. {C : {}..{fs}})) ^ {})
             (∀(op : (∀(f : File ^ {fs}) ⊤) ^ {cp.C}) (⊤ ^ {any})) ^ {fs, cp}) ^ {fs}
```

with `File := μ(f. {read : (⊤ → ⊤) ^ {f}})`.  The member bound of the
capture parameter is written out: a member-bound `any` reads as the
parameter object's own set with its self, which is not what a pure parameter
object wants, and the user's design for reach capabilities prescribes the
explicit member here.  The result `any` reads as the inner arrow's own set
with its binder, `{fs, cp, op}`.

The caller allocates `ν(c. {C = {fs}})` at the precise member `{fs}..{fs}`,
passes it at the abstract member `{}..{fs}`, and passes an `op` declared at
`{fs}`, which the precise member's *lower* bound puts below `{cp.C}`.  The
program's use set is `{fs}`. -/

/-- `File := μ(f. {read : (⊤ → ⊤) ^ {f}})`. -/
def fileS : Shape s := .mu (.fld lread (arrowS ^ [CapAtom.var .here]))

theorem fileWf : Shape.Wf (fileS : Shape s) := .mu (.fld arrowWf) .fld

/-- `ν(f. {read = λ(u : ⊤). u})`. -/
def fileDefs : Defs s := .trm lread (.val (.lam unitTy (.path (.var .here))))

/-- A file literal, at any assigned capture set: the field is declared at
the self, so the literal carries whatever set it is allocated with. -/
def fileLit {s : Sig} {Γ : Ctx s} (U : CaptureSet s) :
    HasTyP [] Γ (.val (.obj fileDefs)) (fileS ^ U) :=
  .obj (.trm ((HasTy.lam ((var' .here rfl).widen _) unitWf).widen _)) .trm

/-- `μ(c. {C : {}..{fs}})`, the capture parameter as `withFile` declares it. -/
def S1CPS (fs : BVar s .cap) : Shape s := .mu (.cap lC [] [CapAtom.cvar (.there fs)])
/-- The type of the capture parameter: pure. -/
def S1CP (fs : BVar s .cap) : Ty s := S1CPS fs ^ []

/-- `μ(c. {C : {fs}..{fs}})`, the precise type of the object the caller
allocates. -/
def S1CPPreS (fs : BVar s .cap) : Shape s :=
  .mu (.cap lC [CapAtom.cvar (.there fs)] [CapAtom.cvar (.there fs)])
/-- The precise type of the caller's capture object. -/
def S1CPPre (fs : BVar s .cap) : Ty s := S1CPPreS fs ^ []

theorem S1CPWf {fs : BVar s .cap} : Ty.Wf (S1CP fs) := .capt (.mu .cap .cap)

/-- `(∀(f : File ^ {fs}) ⊤) ^ {cp.C}`, the operation's type. -/
def S1OP (fs : BVar s .cap) (cp : BVar s .var) : Ty s :=
  (Shape.all (fileS ^ [CapAtom.cvar (.there fs)]) (.ty unitTy)) ^ [CapAtom.sel cp lC]

theorem S1OPWf {fs : BVar s .cap} {cp : BVar s .var} : Ty.Wf (S1OP fs cp) :=
  .capt (.all (.capt fileWf) (.ty unitWf))

/-- The inner arrow as the program writes it: the result is `⊤ ^ {any}`. -/
def S1InnerAny (fs : BVar s .cap) : Ty (s,x) :=
  (Shape.all (S1OP (.there (.there fs)) (.there .here)) (.ty (.top ^ [CapAtom.any])))
    ^ [CapAtom.cvar (.there fs), CapAtom.var .here]

/-- The inner arrow at the reading `expand` gives it: the result is
`⊤ ^ {fs, cp, op}`. -/
def S1Inner (fs : BVar s .cap) : Ty (s,x) :=
  (Shape.all (S1OP (.there (.there fs)) (.there .here))
      (.ty (.top ^ [CapAtom.cvar (.there (.there (.there fs))), CapAtom.var (.there (.there .here)),
        CapAtom.var .here])))
    ^ [CapAtom.cvar (.there fs), CapAtom.var .here]

/-- The type of `withFile` as the program writes it. -/
def S1TyAny (fs : BVar s .cap) : Ty s :=
  (Shape.all (S1CP (.there fs)) (.ty (S1InnerAny (.there fs)))) ^ [CapAtom.cvar fs]

/-- The type of `withFile` at the reading `expand` gives it: a type of stage
A3a, with no `any` left. -/
def S1Ty (fs : BVar s .cap) : Ty s :=
  (Shape.all (S1CP (.there fs)) (.ty (S1Inner (.there fs)))) ^ [CapAtom.cvar fs]

/-- **S1, written.**  Every `any` of the written type is in a position
`expand` reads. -/
theorem S1_anyOk : (S1TyAny k1).AnyOk := by decide

/-- **S1, expanded.**  At the platform set the written type is the A3a type
`S1Ty`: the result `any` reads as `{fs, cp, op}`. -/
theorem S1_expand : (S1TyAny k1).expand platSet = S1Ty k1 := rfl

/-- The expanded type holds no `any`, so it is a type of stage A3a. -/
theorem S1_noAny : (S1Ty k1).NoAny := by decide

/-! ### `withFile` itself -/

/-- The body of `withFile`: allocate a file and hand it to the operation. -/
def S1bodyTm : Tm (Sig.body (Sig.body s)) :=
  .let (.val (.obj fileDefs)) (.app (.there .here) .here)

/-- The term of `withFile`. -/
def S1withFileTm (fs : BVar s .cap) : Tm s :=
  .val (.lam (S1CP (.there fs))
    (.val (.lam (S1OP (.there (up fs)) (.there .here)) S1bodyTm)))

/-- The operation applied to the fresh file.  The file's own use is charged
to `{fs}`, the set it is allocated at, by `sc-var`. -/
def S1call {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} :
    HasTyP [CapAtom.cvar (.there (up (up fs))), CapAtom.var (.there (up .here)),
        CapAtom.var (.there .here)]
      ((Ctx.body (Ctx.body Γ (S1CP (.there fs))) (S1OP (.there (up fs)) (.there .here))).cons
        (fileS ^ [CapAtom.cvar (up (up fs))]))
      (.app (.there .here) .here)
      (.top ^ [CapAtom.cvar (.there (up (up fs))),
        CapAtom.var (.there (up .here)), CapAtom.var (.there .here)]) :=
  HasTy.captTo
    (.app (T2 := .ty unitTy)
      (HasTy.useSub (varAt (.there .here) rfl) (.elem (sub_one (by simp))))
      (HasTy.useSub (varAt .here rfl)
        (Subcap.trans (C2 := [CapAtom.cvar (.there (up (up fs)))]) Subcap.var
          (.elem (sub_one (by simp))))))
    (Subcap.empty _)

/-- The body of `withFile`, at the use set the inner arrow charges it. -/
def S1body {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} :
    HasTyP [CapAtom.cvar (up (up fs)), CapAtom.var (up .here), CapAtom.var .here]
      (Ctx.body (Ctx.body Γ (S1CP (.there fs))) (S1OP (.there (up fs)) (.there .here)))
      S1bodyTm
      (.top ^ [CapAtom.cvar (up (up fs)), CapAtom.var (up .here),
        CapAtom.var .here]) :=
  .let ((fileLit _).widen _) S1call (.capt .top)

/-- The inner lambda: `λ(op : OP). <body>`, at `{fs, cp}`. -/
def S1innerVal {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} :
    HasTyP [] (Ctx.body Γ (S1CP (.there fs)))
      (.val (.lam (S1OP (.there (up fs)) (.there .here)) S1bodyTm))
      (S1Inner (.there (.there fs))) :=
  .lam S1body S1OPWf

/-- **`withFile`**, at the expanded type. -/
def S1withFile {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ (S1withFileTm fs) (S1Ty fs) :=
  .lam (S1innerVal.widen _) S1CPWf

/-! ### The caller of `withFile`

`fs₁` to `fs₅` are `κ₁` at the signatures the caller's five `let` binders
produce, one term binder at a time. -/

def fs1 : BVar ([],c,c,x) .cap := .there k1
def fs2 : BVar ([],c,c,x,x) .cap := .there fs1
def fs3 : BVar ([],c,c,x,x,x) .cap := .there fs2
def fs4 : BVar ([],c,c,x,x,x,x) .cap := .there fs3
def fs5 : BVar ([],c,c,x,x,x,x,x) .cap := .there fs4

/-- `ν(c. {C = {fs}})`, the caller's capture object. -/
def S1cpTm (fs : BVar s .cap) : Tm s := .val (.obj (.cap lC [CapAtom.cvar (up2 fs)]))

/-- Its type: the capture member is defined, so both bounds are `{fs}`. -/
def S1cpLit {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ (S1cpTm fs) (S1CPPre fs) := .obj .cap .cap

/-- The caller's capture object, opened at its precise capture member. -/
def S1cpOpen {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} (cp : BVar s .var)
    (h : Γ.lookup cp = S1CPPre fs) :
    HasTyP [] Γ (.path (.var cp))
      ((Shape.cap lC [CapAtom.cvar fs] [CapAtom.cvar fs]) ^ []) :=
  .recE (var' cp h) .cap

/-- The capture object at the abstract member `{}..{fs}`, which is what
`withFile` asks for: `Rec-E`, `Cap` on the member, `Rec-I`. -/
def S1cpAbs {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} (cp : BVar s .var)
    (h : Γ.lookup cp = S1CPPre fs) (U : CaptureSet s) :
    HasTyP U Γ (.path (.var cp)) (S1CP fs) :=
  (HasTy.recI (subC (S1cpOpen cp h) (.cap (Subcap.empty _) .refl)) .cap).widen U

/-- `λ(f : File ^ {fs}). λ(u : ⊤). u`, the operation the caller passes. -/
def S1opTm (fs : BVar s .cap) : Tm s :=
  .val (.lam (fileS ^ [CapAtom.cvar (.there fs)]) (.val (.lam unitTy (.path (.var .here)))))

/-- Its body, a pure closure read as `⊤`. -/
def S1opInner {s : Sig} {Γ : Ctx s} :
    HasTyP [] Γ (.val (.lam unitTy (.path (.var .here)))) (unitTy : Ty s) :=
  subC (HasTy.lam (T2 := .ty unitTy) ((var' .here rfl).widen _) unitWf) .top

/-- The operation, declared at `{fs}` and passed at `{cp.C}`: the *lower*
bound of the precise capture member is what puts `{fs}` below `{cp.C}`. -/
def S1op {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} (cp : BVar s .var)
    (h : Γ.lookup cp = S1CPPre fs) (U : CaptureSet s) :
    HasTyP U Γ (S1opTm fs) (S1OP fs cp) :=
  (HasTy.captTo (HasTy.lam (S1opInner.widen _) (.capt fileWf))
    (Subcap.selLower (S1cpOpen cp h))).widen U

/-! ### The caller's contexts and its five `let`s -/

/-- `κ₁, κ₂, wf`. -/
def S1Ctx1 : Ctx ([],c,c,x) := platCtx.cons (S1Ty k1)
/-- … `cp`. -/
def S1Ctx2 : Ctx ([],c,c,x,x) := S1Ctx1.cons (S1CPPre fs1)
/-- … `op`. -/
def S1Ctx3 : Ctx ([],c,c,x,x,x) := S1Ctx2.cons (S1OP fs2 .here)

/-- The type of `g = withFile cp`: the inner arrow at the caller's own
capture object. -/
def S1GTy : Ty ([],c,c,x,x,x) :=
  (Shape.all (S1OP (.there fs3) (.there (.there .here)))
      (.ty (.top ^ [CapAtom.cvar (.there (.there fs3)),
        CapAtom.var (.there (.there (.there .here))), CapAtom.var .here])))
    ^ [CapAtom.cvar fs3, CapAtom.var (.there .here)]

/-- … `g`. -/
def S1Ctx4 : Ctx ([],c,c,x,x,x,x) := S1Ctx3.cons S1GTy

/-- The type of `r = g op`: `⊤ ^ {fs, cp, op}`, the result `any` at its
reading. -/
def S1RTy : Ty ([],c,c,x,x,x,x) :=
  .top ^ [CapAtom.cvar fs4, CapAtom.var (.there (.there .here)),
    CapAtom.var (.there .here)]

/-- … `r`. -/
def S1Ctx5 : Ctx ([],c,c,x,x,x,x,x) := S1Ctx4.cons S1RTy

/-- `{fs, cp, op} ⊑ {fs}` at the innermost context: `cp` is pure, and `op`
is below `{cp.C}`, which the *upper* bound of the precise member puts below
`{fs}`. -/
def S1sub5 : Subcap S1Ctx5
    [CapAtom.cvar fs5, CapAtom.var (.there (.there (.there .here))),
      CapAtom.var (.there (.there .here))]
    [CapAtom.cvar fs5] :=
  Subcap.consAtom Subcap.refl
    (Subcap.consAtom (.trans Subcap.var (Subcap.empty _))
      (Subcap.consAtom
        (.trans Subcap.var (.selUpper (S1cpOpen (.there (.there (.there .here))) rfl)))
        (Subcap.empty _)))

/-- The answer: the result of the call, at the platform's own set. -/
def S1answer : HasTyP [CapAtom.cvar fs5] S1Ctx5 (.path (.var .here))
    (.top ^ [CapAtom.cvar fs5]) :=
  .sub (varAt .here rfl) (.ty (.capt .refl S1sub5)) (.trans Subcap.var S1sub5)

/-- `{fs, cp} ⊑ {fs}` at the context of `g`. -/
def S1sub4 : Subcap S1Ctx4
    [CapAtom.cvar fs4, CapAtom.var (.there (.there .here))] [CapAtom.cvar fs4] :=
  Subcap.consAtom Subcap.refl
    (Subcap.consAtom (.trans Subcap.var (Subcap.empty _)) (Subcap.empty _))

/-- `g` at its own type, its use charged to `{fs}`. -/
def S1gVar : HasTyP [CapAtom.cvar fs4] S1Ctx4 (.path (.var .here))
    ((Shape.all (S1OP (.there fs4) (.there (.there (.there .here))))
        (.ty (.top ^ [CapAtom.cvar (.there (.there fs4)),
          CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.var .here])))
      ^ [CapAtom.cvar fs4, CapAtom.var (.there (.there .here))]) :=
  HasTy.useSub (varAt .here rfl) (.trans Subcap.var S1sub4)

/-- `op` at its declared type, its use charged to `{fs}` through the upper
bound of the capture member. -/
def S1opVar : HasTyP [CapAtom.cvar fs4] S1Ctx4 (.path (.var (.there .here)))
    (S1OP fs4 (.there (.there .here))) :=
  HasTy.useSub (varAt (.there .here) rfl)
    (.trans Subcap.var (.selUpper (S1cpOpen (.there (.there .here)) rfl)))

/-- `r = g op`. -/
def S1r : HasTyP [CapAtom.cvar fs4] S1Ctx4 (.app .here (.there .here)) S1RTy :=
  .app S1gVar S1opVar

/-- `let r = g op in r`. -/
def S1letR : HasTyP [CapAtom.cvar fs4] S1Ctx4
    (.let (.app .here (.there .here)) (.path (.var .here)))
    (.top ^ [CapAtom.cvar fs4]) :=
  .let S1r S1answer (.capt .top)

/-- `withFile` itself, its use charged to `{fs}`, the set it is declared
at. -/
def S1wfVar : HasTyP [CapAtom.cvar fs3] S1Ctx3 (.path (.var (.there (.there .here))))
    (S1Ty fs3) :=
  HasTy.useSub (varAt (.there (.there .here)) rfl) Subcap.var

/-- `g = withFile cp`: the capture object is passed at the abstract
member. -/
def S1g : HasTyP [CapAtom.cvar fs3] S1Ctx3
    (.app (.there (.there .here)) (.there .here)) S1GTy :=
  .app S1wfVar (S1cpAbs (.there .here) rfl _)

/-- `let g = withFile cp in …`. -/
def S1letG : HasTyP [CapAtom.cvar fs3] S1Ctx3
    (.let (.app (.there (.there .here)) (.there .here))
      (.let (.app .here (.there .here)) (.path (.var .here))))
    (.top ^ [CapAtom.cvar fs3]) :=
  .let S1g S1letR (.capt .top)

/-- `let op = … in …`. -/
def S1letOp : HasTyP [CapAtom.cvar fs2] S1Ctx2
    (.let (S1opTm fs2)
      (.let (.app (.there (.there .here)) (.there .here))
        (.let (.app .here (.there .here)) (.path (.var .here)))))
    (.top ^ [CapAtom.cvar fs2]) :=
  .let (S1op .here rfl _) S1letG (.capt .top)

/-- `let cp = ν(c. {C = {fs}}) in …`. -/
def S1letCp : HasTyP [CapAtom.cvar fs1] S1Ctx1
    (.let (S1cpTm fs1)
      (.let (S1opTm fs2)
        (.let (.app (.there (.there .here)) (.there .here))
          (.let (.app .here (.there .here)) (.path (.var .here))))))
    (.top ^ [CapAtom.cvar fs1]) :=
  .let ((S1cpLit fs1).widen _) S1letOp (.capt .top)

/-- The term of S1. -/
def S1tm : Tm ([],c,c) :=
  .let (S1withFileTm k1)
    (.let (S1cpTm fs1)
      (.let (S1opTm fs2)
        (.let (.app (.there (.there .here)) (.there .here))
          (.let (.app .here (.there .here)) (.path (.var .here))))))

/-- The type of S1: the answer avoids `cp` and `op`, so it is `⊤ ^ {fs}`. -/
def S1ProgTy : Ty ([],c,c) := .top ^ [CapAtom.cvar k1]

/-- **S1.**  `withFile` with an explicit capture parameter, at the type
whose result `any` reads as `{fs, cp, op}`, and a caller whose use set is
`{fs}`. -/
def S1_typed : HasTyP [CapAtom.cvar k1] platCtx S1tm S1ProgTy :=
  .let ((S1withFile k1).widen _) S1letCp (.capt .top)

/-! ## S2: a class with a capture-set parameter and `any` in the result

```text
Iterator := μ(i. {C : {}..{fs}} ∧ {next : (∀(v : ⊤) (⊤ ^ {i.C})) ^ {i.C}})
mk : (∀(u : ⊤) (Iterator ^ {any})) ^ {fs}
```

The result `any` reads as the arrow's own set with its binder, `{fs, u}`.
The callee returns a literal that defines `C = {fs}`, retyped at the
abstract member on its own variable, which is the packing.  The caller types
`let it = mk unit in let n = it.next in n unit` against the abstract member:
its call is charged by `sc-var` and then by the member's *upper* bound, so
its use set is `{fs}` and `{fs}` is never named at the literal. -/

/-- The iterator's declaration shape at the self `i`, with the abstract
capture member. -/
def S2AbsAt (i : BVar s .var) (fs : BVar s .cap) : Shape s :=
  .and (.cap lC [] [CapAtom.cvar fs])
    (.fld lnext ((Shape.all unitTy (.ty (.top ^ [CapAtom.sel (up2 i) lC])))
      ^ [CapAtom.sel i lC]))

/-- The same with the member defined as `{fs}`, which is what the callee's
literal has. -/
def S2PreAt (i : BVar s .var) (fs : BVar s .cap) : Shape s :=
  .and (.cap lC [CapAtom.cvar fs] [CapAtom.cvar fs])
    (.fld lnext ((Shape.all unitTy (.ty (.top ^ [CapAtom.sel (up2 i) lC])))
      ^ [CapAtom.sel i lC]))

/-- `Iterator`, the abstract shape. -/
def S2IterS (fs : BVar s .cap) : Shape s := .mu (S2AbsAt .here (.there fs))
/-- The precise shape of the callee's literal. -/
def S2PreS (fs : BVar s .cap) : Shape s := .mu (S2PreAt .here (.there fs))

theorem S2AbsDecl {i : BVar s .var} {fs : BVar s .cap} : Shape.Decl (S2AbsAt i fs) :=
  .and .cap .fld
theorem S2PreDecl {i : BVar s .var} {fs : BVar s .cap} : Shape.Decl (S2PreAt i fs) :=
  .and .cap .fld

theorem S2AtWf {i : BVar s .var} {fs : BVar s .cap} : Shape.Wf (S2AbsAt i fs) :=
  .and .cap (.fld (.capt (.all unitWf (.ty (.capt .top)))))
theorem S2IterWf {fs : BVar s .cap} {D : CaptureSet s} : Ty.Wf ((S2IterS fs) ^ D) :=
  .capt (.mu S2AtWf S2AbsDecl)

/-- The type of `mk` as the program writes it. -/
def S2MkTyAny (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy (.ty ((S2IterS (up2 fs)) ^ [CapAtom.any]))) ^ [CapAtom.cvar fs]

/-- The type of `mk` at the reading `expand` gives it: the result `any` is
`{fs, u}`. -/
def S2MkTy (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy
      (.ty ((S2IterS (up2 fs)) ^ [CapAtom.cvar (up2 fs), CapAtom.var .here])))
    ^ [CapAtom.cvar fs]

/-- **S2, written.** -/
theorem S2_anyOk : (S2MkTyAny k1).AnyOk := by decide

/-- **S2, expanded.**  At the platform set the written type is the A3a type
`S2MkTy`: the result `any` reads as `{fs, u}`. -/
theorem S2_expand : (S2MkTyAny k1).expand platSet = S2MkTy k1 := rfl

/-- The expanded type holds no `any`. -/
theorem S2_noAny : (S2MkTy k1).NoAny := by decide

/-! ### The callee -/

/-- The literal's definitions: `C = {fs}` and the closure, declared at the
capture the member names. -/
def S2Defs (fs : BVar s .cap) : Defs s :=
  .and (.cap lC [CapAtom.cvar fs]) (.trm lnext (.val (.lam unitTy (.path (.var .here)))))

theorem S2Distinct (fs : BVar s .cap) : Defs.Distinct (S2Defs fs) := by
  refine .and .cap .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The callee's literal, at its precise type: pure, with `C` defined as
`{fs}` and `next` declared at `{i.C}`. -/
def S2Lit {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ (.val (.obj (S2Defs (up2 fs)))) ((S2PreS fs) ^ []) :=
  .obj
    (.and .cap
      (.trm ((HasTy.lam
        ((HasTy.captTo (var' .here rfl) (Subcap.empty _)).widen _) unitWf).widen _)))
    (S2Distinct _)

/-- **The packing.**  A literal's variable, retyped at the abstract member:
`Rec-E`, `Cap` on the member, `Rec-I`, and the capture set the result is
declared at.  The literal's own `{fs}` disappears into the member. -/
def S2abstract {s : Sig} {Γ : Ctx s} {U : CaptureSet s} (x : BVar s .var)
    {fs : BVar s .cap} (h : Γ.lookup x = (S2PreS fs) ^ []) (D : CaptureSet s) :
    HasTyP U Γ (.path (.var x)) ((S2IterS fs) ^ D) :=
  .sub
    (HasTy.recI
      (subS (.recE (var' x h) S2PreDecl)
        (.and (.trans .and1 (.cap (Subcap.empty _) .refl)) .and2))
      S2AbsDecl)
    (.ty (.capt .refl (Subcap.empty D))) (Subcap.empty U)

/-- The term of `mk`: allocate the iterator and hand it back at the abstract
member. -/
def S2mkTm (fs : BVar s .cap) : Tm s :=
  .val (.lam unitTy (.let (.val (.obj (S2Defs (up2 (up fs))))) (.path (.var .here))))

/-- **`mk`**, at the expanded type. -/
def S2mk {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ (S2mkTm fs) (S2MkTy fs) :=
  .lam
    (.let ((S2Lit (up fs)).widen _)
      (S2abstract .here rfl
        [CapAtom.cvar (.there (up fs)), CapAtom.var (.there .here)])
      S2IterWf)
    unitWf

/-! ### The caller

`unit` is a pure closure read as `⊤`. -/

/-- `λ(y : ⊤). y`, read as a value of `⊤`. -/
def unitTm : Tm s := .val (.lam unitTy (.path (.var .here)))

/-- Its typing: `All-I` and then `<:-⊤`. -/
def unitVal {s : Sig} {Γ : Ctx s} : HasTyP [] Γ (unitTm : Tm s) unitTy :=
  subC (HasTy.lam (T2 := .ty unitTy) ((var' .here rfl).widen _) unitWf) .top

/-- `κ₁, κ₂, mk`. -/
def S2Ctx1 : Ctx ([],c,c,x) := platCtx.cons (S2MkTy k1)
/-- … `un`. -/
def S2Ctx2 : Ctx ([],c,c,x,x) := S2Ctx1.cons unitTy

/-- The type of `it = mk un`: the iterator at `{fs, un}`. -/
def S2ITTy : Ty ([],c,c,x,x) :=
  (S2IterS fs2) ^ [CapAtom.cvar fs2, CapAtom.var .here]

/-- … `it`. -/
def S2Ctx3 : Ctx ([],c,c,x,x,x) := S2Ctx2.cons S2ITTy

/-- The type of `n = it.next`. -/
def S2NTy : Ty ([],c,c,x,x,x) :=
  (Shape.all unitTy (.ty (.top ^ [CapAtom.sel (.there (.there .here)) lC])))
    ^ [CapAtom.sel .here lC]

/-- … `n`. -/
def S2Ctx4 : Ctx ([],c,c,x,x,x,x) := S2Ctx3.cons S2NTy

/-- The type of `r = n un`. -/
def S2RTy : Ty ([],c,c,x,x,x,x) := .top ^ [CapAtom.sel (.there .here) lC]

/-- … `r`. -/
def S2Ctx5 : Ctx ([],c,c,x,x,x,x,x) := S2Ctx4.cons S2RTy

/-- The iterator, opened at its abstract capture member.  This is the only
place the caller reaches `{fs}`, and it reaches it through the member's
upper bound. -/
def S2itCap {s : Sig} {Γ : Ctx s} {fs : BVar s .cap} {D : CaptureSet s} (it : BVar s .var)
    (h : Γ.lookup it = (S2IterS fs) ^ D) :
    HasTyP [CapAtom.var it] Γ (.path (.var it))
      ((Shape.cap lC [] [CapAtom.cvar fs]) ^ [CapAtom.var it]) :=
  subC (.recE (varSelf (S := S2IterS fs) it (by rw [h]; rfl)) S2AbsDecl) .and1

/-- `{it} ⊑ {fs}` at the context of `it`: the iterator is declared at
`{fs, un}` and `un` is pure. -/
def S2subIt : Subcap S2Ctx3 [CapAtom.var .here] [CapAtom.cvar fs3] :=
  .trans Subcap.var
    (Subcap.consAtom Subcap.refl
      (Subcap.consAtom (.trans Subcap.var (Subcap.empty _)) (Subcap.empty _)))

/-- `n = it.next`, the closure read off the abstract member. -/
def S2n : HasTyP [CapAtom.cvar fs3] S2Ctx3 (.proj .here lnext) S2NTy :=
  HasTy.useSub (.proj (subC (.recE (varSelf .here rfl) S2AbsDecl) .and2)) S2subIt

/-- `n` at its own type, its use charged to `{fs}` by `sc-var` and the
member's upper bound. -/
def S2nVar : HasTyP [CapAtom.cvar fs4] S2Ctx4 (.path (.var .here))
    ((Shape.all unitTy (.ty (.top ^ [CapAtom.sel (.there (.there (.there .here))) lC])))
      ^ [CapAtom.sel (.there .here) lC]) :=
  HasTy.useSub (varAt .here rfl)
    (.trans Subcap.var (.selUpper (S2itCap (.there .here) rfl)))

/-- `un` at `⊤`, its use charged to `{fs}`: it is pure. -/
def S2unVar : HasTyP [CapAtom.cvar fs4] S2Ctx4 (.path (.var (.there (.there .here))))
    (unitTy : Ty ([],c,c,x,x,x,x)) :=
  HasTy.useSub (varAt (.there (.there .here)) rfl)
    (.trans Subcap.var (Subcap.empty _))

/-- `r = n un`. -/
def S2r : HasTyP [CapAtom.cvar fs4] S2Ctx4 (.app .here (.there (.there .here))) S2RTy :=
  .app S2nVar S2unVar

/-- The answer: the result of the call, brought to the platform's own set by
the member's upper bound. -/
def S2answer : HasTyP [CapAtom.cvar fs5] S2Ctx5 (.path (.var .here))
    (.top ^ [CapAtom.cvar fs5]) :=
  .sub (varAt .here rfl)
    (.ty (.capt .refl (.selUpper (S2itCap (.there (.there .here)) rfl))))
    (.trans Subcap.var (.selUpper (S2itCap (.there (.there .here)) rfl)))

/-- **C5, the existential result at the compiler's reading, on the source
side.**  The caller of `mk`, at the abstract member: `let n = it.next in
n un`.  Its use set is `{fs}`, and the only step that names `{fs}` is
`sc-sel-upper` at the member's upper bound, which is what the target reads
as `member` at the declared bound.  The callee's `{fs}` is never named
here. -/
def C5_typed : HasTyP [CapAtom.cvar fs3] S2Ctx3
    (.let (.proj .here lnext)
      (.let (.app .here (.there (.there .here))) (.path (.var .here))))
    (.top ^ [CapAtom.cvar fs3]) :=
  .let S2n (.let S2r S2answer (.capt .top)) (.capt .top)

/-- `mk` at its own type, its use charged to `{fs}`. -/
def S2mkVar : HasTyP [CapAtom.cvar fs2] S2Ctx2 (.path (.var (.there .here))) (S2MkTy fs2) :=
  HasTy.useSub (varAt (.there .here) rfl) Subcap.var

/-- The unit argument, pure. -/
def S2unArg : HasTyP [CapAtom.cvar fs2] S2Ctx2 (.path (.var .here))
    (unitTy : Ty ([],c,c,x,x)) :=
  HasTy.useSub (varAt .here rfl) (.trans Subcap.var (Subcap.empty _))

/-- `it = mk un`, at the codomain the result `any` reads as `{fs, un}`. -/
def S2it : HasTyP [CapAtom.cvar fs2] S2Ctx2 (.app (.there .here) .here) S2ITTy :=
  .app S2mkVar S2unArg

/-- The term of S2. -/
def S2tm : Tm ([],c,c) :=
  .let (S2mkTm k1)
    (.let unitTm
      (.let (.app (.there .here) .here)
        (.let (.proj .here lnext)
          (.let (.app .here (.there (.there .here))) (.path (.var .here))))))

/-- The type of S2. -/
def S2ProgTy : Ty ([],c,c) := .top ^ [CapAtom.cvar k1]

/-- **S2.**  A capture-set parameter as a capture member, a result `any`
read as `{fs, u}`, and a caller whose use set is `{fs}`. -/
def S2_typed : HasTyP [CapAtom.cvar k1] platCtx S2tm S2ProgTy :=
  .let ((S2mk k1).widen _)
    (.let (unitVal.widen _)
      (.let S2it C5_typed (.capt .top))
      (.capt .top))
    (.capt .top)

/-! ## Stage B2: `fresh` as an existential

The three source examples of B2.11, written with `fresh`, with `FreshOk`
decided and the expansion `expandFresh` gives them stated and checked by
`rfl`, then typed at the expanded type.  The expansion is decision 18: a
result `fresh` becomes an existential bounded by the callee's own assigned
capture set united with its parameter, which is exactly the bound the
callee's own closing evidence proves.

`Z1` is `freshCell`, with a caller that unpacks by `letex`.  `Z2` is
`makeLogger`, whose bound is the parameter alone because the callee is pure.
`Z3` is C5b, S2's `mk` with the result declared `fresh` instead of `any`.
Each pack reads the witness binder off its own instance binding, which is
`sc-inst`, the one new `Subcap` rule of the stage. -/

/-- `sc-var` with the declared capture set written out. -/
def subVarAt {s : Sig} {Γ : Ctx s} (x : BVar s .var) {C : CaptureSet s}
    (h : (Γ.lookup x).captureSet = C) : Subcap Γ [CapAtom.var x] C := by
  subst h; exact Subcap.var

/-! ## Z1: `freshCell` on the source side -/

/-- `freshCell` as the program writes it: the result is `fresh`. -/
def Z1TyF (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy (.ty (fileS ^ [CapAtom.fresh]))) ^ [CapAtom.cvar fs]

/-- Its reading: the result `fresh` becomes an existential bounded by the
callee's own assigned set united with its parameter. -/
def Z1Ty (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy
      (∃ᶜ[[CapAtom.cvar (up2 fs), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here])))
    ^ [CapAtom.cvar fs]

theorem Z1_freshOk : (Z1TyF k1).FreshOk := by decide

theorem Z1_expandFresh : (Z1TyF k1).expandFresh = Z1Ty k1 := rfl

theorem Z1_noFresh : (Z1Ty k1).NoFresh := by decide

/-! ### The callee -/

/-- The body of `freshCell`: allocate a cell at `{u}` and hand it back. -/
def Z1BodyTm : Tm (Sig.body s) := .let (.val (.obj fileDefs)) (.path (.var .here))

/-- The body at its plain type: the cell, at the parameter's own set. -/
def Z1Body {s : Sig} {Γ : Ctx s} {T1 : Dom s} :
    HasTyP [CapAtom.var .here] (Γ.body T1) Z1BodyTm (fileS ^ [CapAtom.var .here]) :=
  .let ((fileLit [CapAtom.var .here]).widen _)
    (HasTy.useSub (varAt .here rfl) Subcap.var)
    (.capt fileWf)

/-- The packing: the witness is the parameter, and the residual reads the
witness binder off its own instance binding, which is `sc-inst`. -/
def Z1Pack {s : Sig} {Γ : Ctx s} {T1 : Dom s} (fs : BVar s .cap) :
    HasTy (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken [CapAtom.cvar fs]))
        ∪ [CapAtom.var .here])
      (Γ.body T1) Z1BodyTm
      (∃ᶜ[[CapAtom.cvar (up fs), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here])) :=
  .sub Z1Body
    (.pack (C := [CapAtom.var .here]) (.elem (sub_one (by simp)))
      (.capt .refl (Subcap.inst rfl)))
    (.elem (sub_one (by simp)))

/-- The term of `freshCell`. -/
def Z1Tm : Tm s := .val (.lam unitTy Z1BodyTm)

/-- **Z1, `freshCell` on the source side**, at the type `expandFresh`
gives it. -/
def Z1_typed {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ Z1Tm (Z1Ty fs) :=
  .lam (Z1Pack fs) unitWf

/-! ### The caller of `freshCell`, with `letex` -/

/-- `κ₁, κ₂, fc : freshCell, un : ⊤`. -/
def Z1Ctx : Ctx ([],c,c,x,x) := (platCtx.cons (Z1Ty k1)).cons unitTy

/-- The declared use set of the caller's `letex`. -/
def Z1Use : CaptureSet ([],c,c,x,x) := [CapAtom.cvar fs2, CapAtom.var .here]

/-- `fc un`, at the codomain the result `fresh` reads as. -/
def Z1call : HasTy Z1Use Z1Ctx (.app (.there .here) .here)
    (∃ᶜ[Z1Use] (fileS ^ [CapAtom.cvar .here])) := by
  refine HasTy.app (U := Z1Use) (x := .there .here) (y := .here) (T1 := unitTy)
    (T2 := ∃ᶜ[[CapAtom.cvar (up2 fs2), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))
    (C := [CapAtom.cvar fs2])
    ?_ ?_
  · exact HasTy.useSub (varAt (.there .here) rfl)
      (.trans (subVarAt (.there .here) (C := [CapAtom.cvar fs2]) rfl)
        (.elem (sub_one (by decide))))
  · exact HasTy.useSub (varAt .here rfl) (.elem (sub_one (by decide)))

/-- The body of the `letex`: read the unpacked cell, then hand back a pure
closure.  The read is charged to the opened binder itself, which is what the
declared bound pays for. -/
def Z1letBody :
    HasTyP (CaptureSet.weaken (CaptureSet.weaken (k := .cap) Z1Use)
        ∪ [CapAtom.cvar (.there .here)])
      ((Z1Ctx.consC).cons (fileS ^ [CapAtom.cvar .here]))
      (.let (.path (.var .here)) unitTm) unitTy :=
  .let
    (HasTy.useSub (varAt .here rfl)
      (.trans (subVarAt .here (C := [CapAtom.cvar (.there .here)]) rfl)
        (.elem (sub_one (by decide)))))
    (unitVal.widen _) unitWf

/-- **Z1, the caller.**  Its use set is the declared set of the `letex`, and
no root is named anywhere. -/
def Z1_caller : HasTyP (Z1Use ∪ Z1Use) Z1Ctx
    (.letex (.app (.there .here) .here) (.let (.path (.var .here)) unitTm)) unitTy :=
  .letex Z1call Subcap.refl Z1letBody

/-! ## Z2: `makeLogger` on the source side -/

/-- `makeLogger` as the program writes it: a pure function whose parameter
is a capability at the arrow's own capture binder, and whose result is
`fresh`. -/
def Z2TyF : Ty s :=
  (Shape.all (arrowS ^ [CapAtom.cvar .here]) (.ty (fileS ^ [CapAtom.fresh]))) ^ []

/-- Its reading: the bound is the parameter, since the callee is pure. -/
def Z2Ty : Ty s :=
  (Shape.all (arrowS ^ [CapAtom.cvar .here])
      (∃ᶜ[[CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))) ^ []

theorem Z2_freshOk : (Z2TyF : Ty ([],c,c)).FreshOk := by decide

theorem Z2_expandFresh : (Z2TyF : Ty ([],c,c)).expandFresh = Z2Ty := rfl

theorem Z2_noFresh : (Z2Ty : Ty ([],c,c)).NoFresh := by decide

/-- The term of `makeLogger`: allocate a logger at `{fs}` and hand it
back.  It is `freshCell`'s body at a capability parameter. -/
def Z2Tm : Tm s := .val (.lam (arrowS ^ [CapAtom.cvar .here]) Z1BodyTm)

/-- **Z2, `makeLogger` on the source side.**  The witness is the parameter
and not a platform binder, and that is the example's point: the `fresh` of
the result has to be defined in a scope in which `fs` is visible. -/
def Z2_typed {s : Sig} {Γ : Ctx s} : HasTyP [] Γ (Z2Tm : Tm s) Z2Ty :=
  .lam
    (.sub Z1Body
      (.pack (C := [CapAtom.var .here]) Subcap.refl (.capt .refl (Subcap.inst rfl)))
      .refl)
    arrowWf

/-! ## Z3: C5b on the source side -/

/-- S2's `mk` with the result declared `fresh` instead of `any`. -/
def Z3TyF (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy (.ty ((S2IterS (up2 fs)) ^ [CapAtom.fresh]))) ^ [CapAtom.cvar fs]

/-- Its reading: the bound is `{fs, u}`, the callee's own set with its
parameter. -/
def Z3Ty (fs : BVar s .cap) : Ty s :=
  (Shape.all unitTy
      (∃ᶜ[[CapAtom.cvar (up2 fs), CapAtom.var .here]]
        ((S2IterS (.there (up2 fs))) ^ [CapAtom.cvar .here])))
    ^ [CapAtom.cvar fs]

theorem Z3_freshOk : (Z3TyF k1).FreshOk := by decide

theorem Z3_expandFresh : (Z3TyF k1).expandFresh = Z3Ty k1 := rfl

theorem Z3_noFresh : (Z3Ty k1).NoFresh := by decide

/-- The body of `mk`: allocate the iterator and hand it back at the abstract
member, which is S2's packing. -/
def Z3Body {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken [CapAtom.cvar fs]))
        ∪ [CapAtom.var .here])
      (Γ.body unitTy) (.let (.val (.obj (S2Defs (up2 (up fs))))) (.path (.var .here)))
      ((S2IterS (up fs)) ^ [CapAtom.cvar (up fs), CapAtom.var .here]) :=
  .let ((S2Lit (up fs)).widen _)
    (S2abstract .here rfl [CapAtom.cvar (.there (up fs)), CapAtom.var (.there .here)])
    S2IterWf

/-- **Z3, C5b's callee on the source side.**  The capture member packs the
literal's `{fs}`, and the existential packs the whole result. -/
def Z3_typed {s : Sig} {Γ : Ctx s} (fs : BVar s .cap) :
    HasTyP [] Γ (S2mkTm fs) (Z3Ty fs) :=
  .lam (.sub (Z3Body fs) (.pack Subcap.refl (.capt .refl (Subcap.inst rfl))) .refl) unitWf


/-! ## The three callees over the platform prefix -/

/-- `freshCell` over the platform prefix. -/
def Z1_plat : HasTyP [] platCtx Z1Tm (Z1Ty k1) := Z1_typed k1

/-- `makeLogger` over the platform prefix. -/
def Z2_plat : HasTyP [] platCtx (Z2Tm : Tm ([],c,c)) Z2Ty := Z2_typed

/-- C5b's callee over the platform prefix. -/
def Z3_plat : HasTyP [] platCtx (S2mkTm k1) (Z3Ty k1) := Z3_typed k1

end Examples
end DotMNF

end CapturesCC
