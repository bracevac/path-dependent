import Coercions.Paths.DotMNF.Typing

namespace Paths

/-!
# DOT-MNF examples

The five mandatory examples of Plan III §10, as `HasTy` derivations.  The
calculus has no base types, so `Int` and `Nat` are replaced by distinct
closed types; the point of each example is the *shape* of the derivation,
in particular which subtyping steps go through a type selection.

Derivations are plain proof terms: `HasTy` is `Type`-valued, so a derivation
is data and is constructed, not decided (`native_decide` does not apply).
Each intermediate judgment is a named definition with its type spelled out,
which is also the readable form of the example.
-/

namespace DotMNF
namespace Examples

open FCdot (Kind Sig BVar Rename Label)

/-- `Var`, with the variable given explicitly; the declared type is read off
the context by reduction. -/
def var' {s : Sig} {Γ : Ctx s} (x : BVar s .var) {T : Ty s} (h : Γ.lookup x = T) :
    HasTy Γ (.path x) T := by
  subst h; exact .var

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
def E1Dom : Ty s := .typ lA .top .bot
/-- `{B : {a : ⊤}..{a : ⊤}}`, unrelated to `E1Dom`. -/
def E1Res : Ty s := .typ lB (.fld la .top) (.fld la .top)

/-- Under `x : {A : ⊤..⊥}` every type is above every other. -/
def badBounds {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    (hx : HasTy Γ (.path x) (.typ lA .top .bot)) (T : Ty s) :
    Sub Γ E1Dom T :=
  .trans .top (.trans (.selLower hx.toPathTy) (.trans (.selUpper hx.toPathTy) .bot))

def E1Ctx : Ctx ([],x) := .cons .nil E1Dom

def E1x : HasTy E1Ctx (.path .here) E1Dom := var' .here rfl

def E1retype : HasTy E1Ctx (.path .here) E1Res := .sub E1x (badBounds E1x E1Res)

def E1body : HasTy E1Ctx (.let (.path .here) (.path .here)) E1Res :=
  .let E1retype (var' .here rfl) (.typ (.fld .top) (.fld .top))

def E1 : HasTy Ctx.nil
    (.val (.lam E1Dom (.let (.path .here) (.path .here))))
    (.all E1Dom E1Res) :=
  .lam E1body (.typ .top .bot)

/-! ## E2: recursive object with a self-referential member

`ν(x. {A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y})`, allocated by a `let`,
its term member selected and applied to itself.  The application typechecks
because the exact bounds of `A` give `∀(y : x.A) x.A <: x.A`. -/

/-- `∀(y : x.A) x.A`, under the object's self binder. -/
def E2A : Ty (s,x) := .all (.sel (.var .here) lA) (.sel (.var (.there .here)) lA)
/-- The same type one binder further out. -/
def E2A' : Ty (s,x,x) :=
  .all (.sel (.var (.there .here)) lA) (.sel (.var (.there (.there .here))) lA)
/-- The object's self type `{A : E2A..E2A} ∧ {a : E2A}`. -/
def E2Self : Ty (s,x) := .and (.typ lA E2A E2A) (.fld la E2A)
/-- The object's definitions. -/
def E2Defs : Defs (s,x) :=
  .and (.typ lA E2A) (.trm la (.val (.lam (.sel (.var .here) lA) (.path .here))))

theorem E2Distinct : Defs.Distinct (E2Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self type is declaration-shaped. -/
theorem E2SelfDecl : Ty.Decl (E2Self (s := s)) := .and .typ .fld

def E2DefsTy : DefsTy (Ctx.consSelf Γ E2Defs E2Self) E2Defs E2Self :=
  .and .typ (.trm (.lam (var' .here rfl) .sel))

def E2Ctx1 : Ctx ([],x) := .cons .nil (.mu E2Self)

def E2xMu : HasTy E2Ctx1 (.path .here) (.mu E2Self) := var' .here rfl
def E2xOpen : HasTy E2Ctx1 (.path .here) E2Self := .recE E2xMu E2SelfDecl
def E2xFld : HasTy E2Ctx1 (.path .here) (.fld la E2A) := .sub E2xOpen (.and2)
def E2proj : HasTy E2Ctx1 (.proj .here la) E2A := .proj E2xFld

def E2Ctx2 : Ctx ([],x,x) := .cons E2Ctx1 E2A

def E2f : HasTy E2Ctx2 (.path .here) E2A' := var' .here rfl
def E2xMu2 : HasTy E2Ctx2 (.path (.there .here)) (.mu E2Self) := var' (.there .here) rfl
def E2xOpen2 : HasTy E2Ctx2 (.path (.there .here))
    (.and (.typ lA E2A' E2A') (.fld la E2A')) := .recE E2xMu2 E2SelfDecl
/-- `∀(y : x.A) x.A <: x.A`, by the lower bound of the exact member `A`. -/
def E2fArg : HasTy E2Ctx2 (.path .here) (.sel (.var (.there .here)) lA) :=
  .sub E2f (.selLower (HasTy.toPathTy (.sub E2xOpen2 (.and1))))
def E2app : HasTy E2Ctx2 (.app .here .here) (.sel (.var (.there .here)) lA) :=
  .app E2f E2fArg

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : HasTy Ctx.nil
    (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here))) .top :=
  .let (.obj E2DefsTy E2Distinct)
    (.let E2proj (.sub E2app .top) .top)
    .top

/-! ## E3: intersection with a shared member

`x : {A : ⊥..T₁} ∧ {A : T₂..⊤}` with `T₁ = {a : ⊤}` and `T₂ = {b : ⊤}`
unrelated: the two bounds of the single member `A` make `T₂ <: T₁`. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E3T1 : Ty s := .fld la .top
/-- `{b : ⊤}`, standing for `Nat`; unrelated to `E3T1`. -/
def E3T2 : Ty s := .fld lb .top
/-- `{A : ⊥..T₁} ∧ {A : T₂..⊤}`. -/
def E3Dom : Ty s := .and (.typ lA .bot E3T1) (.typ lA E3T2 .top)

def E3Ctx1 : Ctx ([],x) := .cons .nil E3Dom
def E3Ctx2 : Ctx ([],x,x) := .cons E3Ctx1 E3T2

def E3xDom : HasTy E3Ctx2 (.path (.there .here)) E3Dom := var' (.there .here) rfl
def E3xLo : HasTy E3Ctx2 (.path (.there .here)) (.typ lA .bot E3T1) :=
  .sub E3xDom (.and1)
def E3xHi : HasTy E3Ctx2 (.path (.there .here)) (.typ lA E3T2 .top) :=
  .sub E3xDom (.and2)
/-- `T₂ <: x.A <: T₁`: the shared member, used at both bounds. -/
def E3sub : Sub E3Ctx2 E3T2 E3T1 := .trans (.selLower E3xHi.toPathTy) (.selUpper E3xLo.toPathTy)
def E3z : HasTy E3Ctx2 (.path .here) E3T1 := .sub (var' .here rfl) E3sub

def E3body : HasTy E3Ctx2 (.let (.path .here) (.path .here)) E3T1 :=
  .let E3z (var' .here rfl) (.fld .top)

def E3inner : HasTy E3Ctx1
    (.val (.lam E3T2 (.let (.path .here) (.path .here)))) (.all E3T2 E3T1) :=
  .lam E3body (.fld .top)

/-- `λ(x : {A : ⊥..T₁} ∧ {A : T₂..⊤}). λ(z : T₂). let y = z in y`. -/
def E3 : HasTy Ctx.nil
    (.val (.lam E3Dom (.val (.lam E3T2 (.let (.path .here) (.path .here))))))
    (.all E3Dom (.all E3T2 E3T1)) :=
  .lam E3inner (.and (.typ .bot (.fld .top)) (.typ (.fld .top) .top))

/-! ## E4: the counterexample of §1

`Γ = x : {B : S..T}, w : S` with `S = {A : ⊥..⊤}` and `T = {A : Int..⊤}`.
`S <: x.B <: T` gives `w : T`, hence `Int <: w.A`, hence `g n : w.A` for
`g = λ(y : w.A). y` and `n : Int`.  No realizer for `x` exists, and the
derivation is nonetheless well formed: this is why the target of Plan III
needs `member` through `trans`. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E4Int : Ty s := .fld la .top
/-- `S = {A : ⊥..⊤}`. -/
def E4S : Ty s := .typ lA .bot .top
/-- `T = {A : Int..⊤}`. -/
def E4T : Ty s := .typ lA E4Int .top
/-- `{B : S..T}`. -/
def E4X : Ty s := .typ lB E4S E4T

def E4Ctx1 : Ctx ([],x) := .cons .nil E4X
def E4Ctx2 : Ctx ([],x,x) := .cons E4Ctx1 E4S
def E4Ctx3 : Ctx ([],x,x,x) := .cons E4Ctx2 E4Int

/-- The type of `g = λ(y : w.A). y`, in the scope of `x`, `w`, `n`. -/
def E4G : Ty (s,x,x,x) :=
  .all (.sel (.var (.there .here)) lA) (.sel (.var (.there (.there .here))) lA)
/-- The same type one binder further out. -/
def E4G' : Ty (s,x,x,x,x) :=
  .all (.sel (.var (.there (.there .here))) lA)
    (.sel (.var (.there (.there (.there .here)))) lA)

def E4x : HasTy E4Ctx3 (.path (.there (.there .here))) E4X :=
  var' (.there (.there .here)) rfl
/-- `S <: x.B <: T`, the step with no realizer. -/
def E4ST : Sub E4Ctx3 E4S E4T := .trans (.selLower E4x.toPathTy) (.selUpper E4x.toPathTy)
def E4wT : HasTy E4Ctx3 (.path (.there .here)) E4T :=
  .sub (var' (.there .here) rfl) E4ST
def E4g : HasTy E4Ctx3
    (.val (.lam (.sel (.var (.there .here)) lA) (.path .here))) E4G :=
  .lam (var' .here rfl) .sel

def E4Ctx4 : Ctx ([],x,x,x,x) := .cons E4Ctx3 E4G

def E4x4 : HasTy E4Ctx4 (.path (.there (.there (.there .here)))) E4X :=
  var' (.there (.there (.there .here))) rfl
def E4ST4 : Sub E4Ctx4 E4S E4T := .trans (.selLower E4x4.toPathTy) (.selUpper E4x4.toPathTy)
def E4wT4 : HasTy E4Ctx4 (.path (.there (.there .here))) E4T :=
  .sub (var' (.there (.there .here)) rfl) E4ST4
/-- `n : Int <: w.A`. -/
def E4nA : HasTy E4Ctx4 (.path (.there .here))
    (.sel (.var (.there (.there .here))) lA) :=
  .sub (var' (.there .here) rfl) (.selLower E4wT4.toPathTy)
def E4gv : HasTy E4Ctx4 (.path .here) E4G' := var' .here rfl
def E4app : HasTy E4Ctx4 (.app .here (.there .here))
    (.sel (.var (.there (.there .here))) lA) := .app E4gv E4nA

def E4let : HasTy E4Ctx3
    (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path .here)))
      (.app .here (.there .here)))
    (.sel (.var (.there .here)) lA) :=
  .let E4g E4app .sel

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : HasTy Ctx.nil
    (.val (.lam E4X (.val (.lam E4S (.val (.lam E4Int
      (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path .here)))
        (.app .here (.there .here)))))))))
    (.all E4X (.all E4S (.all E4Int (.sel (.var (.there .here)) lA)))) :=
  .lam (.lam (.lam E4let (.fld .top)) (.typ .bot .top))
    (.typ (.typ .bot .top) (.typ (.fld .top) .top))

/-! ## E5: an object returned from a function and selected after a `let`

`λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z. {a = v}) in
 let o = f w in o.a`.  The result type of `f` mentions the parameter's
member, so the application renames it to `w`; the result of the outer `let`
is `w.A`, which mentions neither `let` binder. -/

/-- `{A : ⊤..⊤}`. -/
def E5AT : Ty s := .typ lA .top .top
/-- `{a : v.A}` under the object's self binder, `v` the enclosing lambda's
parameter. -/
def E5Self : Ty (s,x,x) := .fld la (.sel (.var (.there .here)) lA)
/-- The type of `f`: `∀(v : {A : ⊤..⊤}) μ(z. {a : v.A})`. -/
def E5F : Ty s := .all E5AT (.mu E5Self)
/-- `μ(z. {a : w.A})`, the type of `f w` in the scope of `w`, `f`. -/
def E5Owned : Ty (s,x,x) := .mu (.fld la (.sel (.var (.there (.there .here))) lA))
/-- The same type one binder further out. -/
def E5Owned' : Ty (s,x,x,x) :=
  .mu (.fld la (.sel (.var (.there (.there (.there .here)))) lA))
/-- The body of `f`: `ν(z. {a = v})`. -/
def E5Obj : Tm (s,x) := .val (.obj (.trm la (.path (.there .here))))

def E5Ctx1 : Ctx ([],x) := .cons .nil E5AT
def E5Ctxv : Ctx ([],x,x) := .cons E5Ctx1 E5AT
/-- The definitions of the literal `ν(z. {a = v})`. -/
def E5Defs : Defs (s,x,x) := .trm la (.path (.there .here))
def E5Ctxz : Ctx ([],x,x,x) := .consSelf E5Ctxv E5Defs E5Self

def E5v : HasTy E5Ctxz (.path (.there .here)) E5AT := var' (.there .here) rfl
/-- The field body: `v : ⊤ <: v.A`, by the lower bound of `v`'s member. -/
def E5field : HasTy E5Ctxz (.path (.there .here)) (.sel (.var (.there .here)) lA) :=
  .sub (.sub E5v .top) (.selLower E5v.toPathTy)
def E5DefsTy : DefsTy E5Ctxz E5Defs E5Self := .trm E5field

def E5ObjTy : HasTy E5Ctxv E5Obj (.mu E5Self) :=
  .obj E5DefsTy .trm
def E5fVal : HasTy E5Ctx1 (.val (.lam E5AT E5Obj)) E5F := .lam E5ObjTy (.typ .top .top)

def E5Ctxf : Ctx ([],x,x) := .cons E5Ctx1 E5F

def E5fv : HasTy E5Ctxf (.path .here) E5F := var' .here rfl
def E5w : HasTy E5Ctxf (.path (.there .here)) E5AT := var' (.there .here) rfl
/-- `f w : μ(z. {a : w.A})`: the application renames `v`'s block to `w`. -/
def E5o : HasTy E5Ctxf (.app .here (.there .here)) E5Owned := .app E5fv E5w

def E5Ctxo : Ctx ([],x,x,x) := .cons E5Ctxf E5Owned

def E5oMu : HasTy E5Ctxo (.path .here) E5Owned' := var' .here rfl
def E5oOpen : HasTy E5Ctxo (.path .here)
    (.fld la (.sel (.var (.there (.there .here))) lA)) := .recE E5oMu .fld
def E5proj : HasTy E5Ctxo (.proj .here la) (.sel (.var (.there (.there .here))) lA) :=
  .proj E5oOpen

def E5oLet : HasTy E5Ctxf (.let (.app .here (.there .here)) (.proj .here la))
    (.sel (.var (.there .here)) lA) := .let E5o E5proj .sel

def E5fLet : HasTy E5Ctx1
    (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))
    (.sel (.var .here) lA) := .let E5fVal E5oLet .sel

def E5 : HasTy Ctx.nil
    (.val (.lam E5AT
      (.let (.val (.lam E5AT E5Obj)) (.let (.app .here (.there .here)) (.proj .here la)))))
    (.all E5AT (.sel (.var .here) lA)) :=
  .lam E5fLet (.typ .top .top)

/-! ## E6: a field typed at its own literal's type member

`ν(x. {T = Int} ∧ {v = n})`, with `n : Int` from the enclosing scope, typed
at `μ(x. {T : Int..Int} ∧ {v : x.T})`.  The field `v` is declared at `x.T`, a
selection on the object's own self: the shape the self-alias restriction
used to forbid, now admitted by alias-tolerant resolution on the target
side. -/

/-- `{a : ⊤}`, standing for `Int`. -/
def E6Int : Ty s := .fld la .top
/-- The object's self type `{T : Int..Int} ∧ {v : x.T}`. -/
def E6Self : Ty (s,x,x) := .and (.typ lT E6Int E6Int) (.fld lv (.sel (.var .here) lT))
/-- The object's definitions: `T = Int`, `v = n` (`n` the enclosing variable). -/
def E6Defs : Defs (s,x,x) := .and (.typ lT E6Int) (.trm lv (.path (.there .here)))

theorem E6Distinct : Defs.Distinct (E6Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The self type is declaration-shaped. -/
theorem E6SelfDecl : Ty.Decl (E6Self (s := s)) := .and .typ .fld

def E6Ctx1 : Ctx ([],x) := .cons .nil E6Int
def E6Ctxz : Ctx ([],x,x) := .consSelf E6Ctx1 E6Defs E6Self

def E6xMu : HasTy E6Ctxz (.path .here) (.mu E6Self) := var' .here rfl
def E6xOpen : HasTy E6Ctxz (.path .here) E6Self := .recE E6xMu E6SelfDecl
def E6xTyp : HasTy E6Ctxz (.path .here) (.typ lT E6Int E6Int) :=
  .sub E6xOpen (.and1)
/-- `n : Int <: x.T`, by the lower bound of the exact member `T`. -/
def E6nT : HasTy E6Ctxz (.path (.there .here)) (.sel (.var .here) lT) :=
  .sub (var' (.there .here) rfl) (.selLower E6xTyp.toPathTy)

def E6DefsTy : DefsTy E6Ctxz E6Defs E6Self := .and .typ (.trm E6nT)

/-- `λ(n : Int). ν(x. {T = Int} ∧ {v = n})`. -/
def E6 : HasTy E6Ctx1 (.val (.obj E6Defs)) (.mu E6Self) :=
  .obj E6DefsTy E6Distinct

/-! ## E7: a two-element alias cycle

`ν(x. {A = x.B} ∧ {B = x.A})`: both type members are bare selections on the
object's own self, and each other's.  Admitted now that alias-tolerant
resolution follows same-block aliases on the target side (a cyclic alias
resolves to `⊤`, `FCdot.Ctx.resolve`); the self-alias restriction that used
to forbid this shape on the definitions is gone. -/

def E7Self : Ty (s,x) :=
  .and (.typ lA (.sel (.var .here) lB) (.sel (.var .here) lB))
    (.typ lB (.sel (.var .here) lA) (.sel (.var .here) lA))
def E7Defs : Defs (s,x) := .and (.typ lA (.sel (.var .here) lB)) (.typ lB (.sel (.var .here) lA))

theorem E7Distinct : Defs.Distinct (E7Defs (s := s)) := by
  refine .and .typ .typ ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

def E7DefsTy : DefsTy (Ctx.consSelf Γ E7Defs E7Self) E7Defs E7Self := .and .typ .typ

/-- `ν(x. {A = x.B} ∧ {B = x.A})`. -/
def E7 : HasTy Ctx.nil (.val (.obj E7Defs)) (.mu E7Self) := .obj E7DefsTy E7Distinct

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
def E8Dom : Ty s := .typ lA .bot (.fld la .top)

/-- `x.A ∧ {a : ⊤}`, the refinement of `x.A`. -/
def E8Ref (x : BVar s .var) : Ty s := .and (.sel (.var x) lA) (.fld la .top)

theorem E8DomWf : Ty.Wf (E8Dom (s := s)) := .typ .bot (.fld .top)

/-- The refinement is well formed although its left operand is not
declaration-shaped: `Wf.and` has no `Ty.Decl` premises. -/
theorem E8RefWf {x : BVar s .var} : Ty.Wf (E8Ref x) := .and .sel (.fld .top)

def E8Ctx1 : Ctx ([],x) := Ctx.nil.cons E8Dom
def E8Ctx2 : Ctx ([],x,x) := E8Ctx1.cons (E8Ref .here)

/-- `y : x.A ∧ {a : ⊤}`. -/
def E8y : HasTy E8Ctx2 (.path .here) (E8Ref (.there .here)) := var' .here rfl

/-- `x : {A : ⊥..{a : ⊤}}`. -/
def E8x : HasTy E8Ctx2 (.path (.there .here)) E8Dom := var' (.there .here) rfl

/-- `And₂`: the declaration operand of the refinement. -/
def E8yFld2 : HasTy E8Ctx2 (.path .here) (.fld la .top) := .sub E8y .and2

/-- `And₁`: the abstract type itself. -/
def E8yA : HasTy E8Ctx2 (.path .here) (.sel (.var (.there .here)) lA) :=
  .sub E8y .and1

/-- `Sel-<:`: the upper bound of `x`'s member `A`. -/
def E8Upper : Sub E8Ctx2 (.sel (.var (.there .here)) lA) (.fld la .top) := .selUpper E8x.toPathTy

/-- The same conclusion as `E8yFld2`, the other way round. -/
def E8yFld1 : HasTy E8Ctx2 (.path .here) (.fld la .top) := .sub E8yA E8Upper

/-- `And-I`: the two views of `y` recombined into the refinement. -/
def E8AndI : HasTy E8Ctx2 (.path .here) (E8Ref (.there .here)) := .andI E8yA E8yFld2

/-- `y.a`, through `And₂`. -/
def E8Body2 : HasTy E8Ctx2 (.proj .here la) .top := .proj E8yFld2

/-- `y.a`, through `And₁` and `Sel-<:`. -/
def E8Body1 : HasTy E8Ctx2 (.proj .here la) .top := .proj E8yFld1

/-- `λ(x). λ(y). y.a`, with the `And₂` derivation of the body. -/
def E8 : HasTy Ctx.nil (.val (.lam E8Dom (.val (.lam (E8Ref .here) (.proj .here la)))))
    (.all E8Dom (.all (E8Ref .here) .top)) :=
  .lam (.lam E8Body2 E8RefWf) E8DomWf

/-- The same term, with the `And₁`-then-`Sel-<:` derivation of the body. -/
def E8b : HasTy Ctx.nil (.val (.lam E8Dom (.val (.lam (E8Ref .here) (.proj .here la)))))
    (.all E8Dom (.all (E8Ref .here) .top)) :=
  .lam (.lam E8Body1 E8RefWf) E8DomWf


/-! ## The path pages X1 to X4

Four pages for the path extension, added by P0 g5.  The eight examples above
are the regression: the extension weakens nothing, and each of them keeps its
name, its statement and its derivation.  `.path (.var x)` reads `.path x`
there, because a term carries a variable, and `.sel (.var x) A` is the base's
type selection at a path of length one. -/

/-- `Var` at a path, the path-typing twin of `var'`. -/
def pvar' {s : Sig} {Γ : Ctx s} (x : BVar s .var) {T : Ty s} (h : Γ.lookup x = T) :
    PathTy Γ (.var x) T := by
  subst h; exact .var

/-! ## X1: pDOT Sec. 2.2, the length-two path

`ν(z. {val c = ν(w. {A = z.B})} ∧ {B = z.c.A})`, the example pDOT Sec. 2.2
names as the shape WadlerFest DOT cannot write (`survey-pdot.md` §3).  The
field `c` holds a nested literal whose type member `A` is the outer self's
`B`, and the outer self's `B` is the nested literal's `A`, read through the
path `z.c` of length two.

The field `c` is stable, `{val c : μ(w. {A : z.B..z.B})}`, by `DefsTy.trmObj`:
that is what lets `Fld-E` read a member at `x.c` at all.  The page closes with
the two type selections `x.c.A` and `x.B` shown mutually below one another, by
two independent routes, which is the mutual recursion of the example. -/

/-- Term label `c`. -/
def X1_lc : Label := .trm 3

/-- The nested literal's definitions, `{A = z.B}`, under `w` inside `z`. -/
def X1_Inner : Defs ((s,x),x) := .typ lA (.sel (.var (.there .here)) lB)

/-- The nested literal's declared type, `{A : z.B..z.B}`.  Exact, as every
type definition is. -/
def X1_InnerSelf : Ty ((s,x),x) :=
  .typ lA (.sel (.var (.there .here)) lB) (.sel (.var (.there .here)) lB)

theorem X1_InnerDistinct : Defs.Distinct (X1_Inner (s := s)) := .typ

def X1_InnerDefsTy {Γ : Ctx (s,x)} :
    DefsTy (Γ.consSelf X1_Inner X1_InnerSelf) X1_Inner X1_InnerSelf := .typ

/-- `z.c.A`, the selection through a path of length two. -/
def X1_B : Ty (s,x) := .sel (.sel (.var .here) X1_lc) lA

/-- The outer literal's definitions, `{c = ν(w. {A = z.B})} ∧ {B = z.c.A}`. -/
def X1_Defs : Defs (s,x) :=
  .and (.trm X1_lc (.val (.obj X1_Inner))) (.typ lB X1_B)

/-- The outer literal's declared type,
`{val c : μ(w. {A : z.B..z.B})} ∧ {B : z.c.A..z.c.A}`. -/
def X1_Self : Ty (s,x) :=
  .and (.vfld X1_lc (.mu X1_InnerSelf)) (.typ lB X1_B X1_B)

theorem X1_Distinct : Defs.Distinct (X1_Defs (s := s)) := by
  refine .and .trm .typ ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

/-- The declared type is declaration-shaped, so `Rec-I` and `Rec-E` apply. -/
theorem X1_SelfDecl : Ty.Decl (X1_Self (s := ([],x))) := by decide

/-- The nested literal's type is declaration-shaped as well. -/
theorem X1_InnerSelfDecl : Ty.Decl (X1_InnerSelf (s := [])) := by decide

def X1_DefsTy {Γ : Ctx s} :
    DefsTy (Γ.consSelf X1_Defs X1_Self) X1_Defs X1_Self :=
  .and (.trmObj X1_InnerDefsTy X1_InnerDistinct) .typ

/-- The literal, `ν(z. {c = ν(w. {A = z.B})} ∧ {B = z.c.A})`. -/
def X1_lit {Γ : Ctx s} : HasTy Γ (.val (.obj X1_Defs)) (.mu X1_Self) :=
  .obj X1_DefsTy X1_Distinct

/-- The literal allocated and bound to `x`. -/
def X1_Ctx : Ctx ([],x) := .cons .nil (.mu X1_Self)

def X1_x : PathTy X1_Ctx (.var .here) (.mu X1_Self) := pvar' .here rfl

/-- `Rec-E` at the variable: the self is instantiated at `x`. -/
def X1_xOpen : PathTy X1_Ctx (.var .here) X1_Self := X1_x.recE X1_SelfDecl

/-- The stable field, read off the left conjunct. -/
def X1_xc : PathTy X1_Ctx (.var .here) (.vfld X1_lc (.mu X1_InnerSelf)) :=
  X1_xOpen.sub .and1

/-- `Fld-E` at the stable field: the path `x.c`, of length two, has a type. -/
def X1_c : PathTy X1_Ctx (.sel (.var .here) X1_lc) (.mu X1_InnerSelf) := X1_xc.sel

/-- `Rec-E` at the path `x.c`: the nested self is instantiated at `x.c`, and
the member `A` reads `{A : x.B..x.B}`. -/
def X1_cOpen : PathTy X1_Ctx (.sel (.var .here) X1_lc)
    (.typ lA (.sel (.var .here) lB) (.sel (.var .here) lB)) :=
  X1_c.recE X1_InnerSelfDecl

/-- The outer member `B`, read off the right conjunct: `{B : x.c.A..x.c.A}`. -/
def X1_xB : PathTy X1_Ctx (.var .here) (.typ lB X1_B X1_B) := X1_xOpen.sub .and2

/-- `x.c.A <: x.B`, by the upper bound of the nested member `A`. -/
def X1_ACfromA : Sub X1_Ctx (.sel (.sel (.var .here) X1_lc) lA) (.sel (.var .here) lB) :=
  .selUpper X1_cOpen

/-- `x.B <: x.c.A`, by the lower bound of the same member. -/
def X1_BAfromA : Sub X1_Ctx (.sel (.var .here) lB) (.sel (.sel (.var .here) X1_lc) lA) :=
  .selLower X1_cOpen

/-- `x.B <: x.c.A`, the other route: the upper bound of the outer member `B`. -/
def X1_BAfromB : Sub X1_Ctx (.sel (.var .here) lB) (.sel (.sel (.var .here) X1_lc) lA) :=
  .selUpper X1_xB

/-- `x.c.A <: x.B`, the lower bound of the outer member `B`. -/
def X1_ACfromB : Sub X1_Ctx (.sel (.sel (.var .here) X1_lc) lA) (.sel (.var .here) lB) :=
  .selLower X1_xB

/-! ## X2: E10, a computation field is not a prefix

`ν(x. {a = x.a})`, the literal Fact 2 of the plan machine checks as
`DotMNF.badLit`: it types at `μ(x. {a : {A : ⊤..⊥}})`, whose field `a` holds a
computation with bad bounds.  A rule eliminating the members of `x.a` at the
path `x.a`, with no premise about the field, would read `⊤ <: ⊥` off a store
that has allocated nothing at `x.a`.

`Fld-E` is stated on a stable member, `PathTy.sel`, and this literal declares
no stable member.  The page proves that by inversion, twice.  `X2_defsShape`
inverts definition typing: the three stable rules ask for an object literal, a
lambda or a variable body, the body here is the projection `x.a`, so every
derivation of these definitions types `a` as a computation member.
`X2_noVfld` reads the declaration type with `Ty.lookupVfldDecl` and gets
`none`.  `X2_noSubDecl` inverts the abstract view: `Typ-Abs` cannot widen the
literal's type to one with a stable member at `a` either.

What is left unproved is the unqualified sentence "for every `T` there is no
derivation of `PathTy Γ x.a T`".  Its remaining cases go through `PathTy.sub`
and `PathTy.snglInv`, and refuting those is an inversion of `Sub`, which P0
does not have. -/

/-- `{A : ⊤..⊥}`, the bad bounds the field holds. -/
def X2_Bad : Ty s := .typ lA .top .bot

/-- The definitions `{a = x.a}`. -/
def X2_Defs : Defs (s,x) := .trm la (.proj .here la)

/-- The declared type `{a : {A : ⊤..⊥}}`.  The member is a computation
member, `Ty.fld`, and not a stable one. -/
def X2_Self : Ty (s,x) := .fld la X2_Bad

/-- The declared type, one binder further out. -/
def X2_SelfW : Ty ((s,x),x) := .fld la X2_Bad

theorem X2_SelfDecl : Ty.Decl (X2_SelfW (s := s)) := .fld

def X2_Ctx {Γ : Ctx s} : Ctx (s,x) := Γ.consSelf X2_Defs X2_Self

/-- The self, opened: `x : {a : {A : ⊤..⊥}}`. -/
def X2_xOpen {Γ : Ctx s} : HasTy (X2_Ctx (Γ := Γ)) (.path .here) X2_Self :=
  HasTy.recE (var' .here rfl) X2_SelfDecl

/-- The field body, `x.a`, typed by `{}-E`. -/
def X2_body {Γ : Ctx s} : HasTy (X2_Ctx (Γ := Γ)) (.proj .here la) X2_Bad :=
  .proj X2_xOpen

/-- The definitions type by `DefsTy.trm`, at a computation member. -/
def X2_DefsTy {Γ : Ctx s} : DefsTy (X2_Ctx (Γ := Γ)) X2_Defs X2_Self := .trm X2_body

/-- `ν(x. {a = x.a})` at `μ(x. {a : {A : ⊤..⊥}})`, the vanilla derivation of
Fact 2. -/
def X2_lit {Γ : Ctx s} : HasTy Γ (.val (.obj X2_Defs)) (.mu X2_Self) :=
  .obj X2_DefsTy .trm

/-- Inversion of definition typing at this body: every type these definitions
can be given declares `a` as a computation member.  `trmObj`, `trmLam` and
`trmSngl` ask for an object literal, a lambda and a variable body, and the
body is the projection `x.a`, so `trm` is the only rule that applies. -/
def X2_defsShape {Γ : Ctx (s,x)} {U : Ty (s,x)} (h : DefsTy Γ X2_Defs U) :
    (T : Ty (s,x)) × PLift (U = .fld la T) := by
  cases h with
  | trm _ => exact ⟨_, .up rfl⟩

/-- The declaration type has no stable member at `a`, so `Fld-E` has no
premise to read at `x.a`. -/
theorem X2_noVfld {Γ : Ctx (s,x)} {U : Ty (s,x)} (h : DefsTy Γ X2_Defs U) :
    U.lookupVfldDecl la = none := by
  obtain ⟨T, hU⟩ := X2_defsShape h
  rw [hU.down, Ty.lookupVfldDecl]

/-- The abstract view does not manufacture the premise either: `SubDecl` into
a stable member reads `Ty.lookupVfldDecl`, which is `none` here, so `Typ-Abs`
cannot widen `μ(x. {a : {A : ⊤..⊥}})` to a type with a stable member at `a`. -/
theorem X2_noSubDecl {Γ : Ctx s} {T : Ty (s,x)}
    (h : SubDecl Γ X2_Self (.vfld la T)) : False := by
  cases h with
  | vfld hr _ => exact absurd hr (by rw [X2_Self, Ty.lookupVfldDecl]; exact fun h => by cases h)

/-! ## X3: `let y = x.a in y.b`, the two-hop program

Decision 2 keeps term position in monadic normal form, so a path of length
two is written with a `let`.  `HasTy.letSngl` binds `y` at the singleton
`(x.a).type` rather than opaquely, and that is what relates the binder to the
prefix it names: under the singleton, `Sngl-Trans` carries `x.a`'s stable
member to `y`, and `Fld-E` then reads `y.b`.

`x : {val a : {val b : ⊤}}`, both members stable, since `Fld-E` reads stable
members only (X2). -/

/-- `{val b : ⊤}`, the type of `x.a`. -/
def X3_B : Ty s := .vfld lb .top

/-- `{val a : {val b : ⊤}}`, the type of `x`. -/
def X3_A : Ty s := .vfld la X3_B

def X3_Ctx : Ctx ([],x) := .cons .nil X3_A

def X3_x : PathTy X3_Ctx (.var .here) X3_A := pvar' .here rfl

/-- `Fld-E` at the stable field: `x.a : {val b : ⊤}`. -/
def X3_xa : PathTy X3_Ctx (.sel (.var .here) la) X3_B := X3_x.sel

/-- The body's context: `y` bound at the singleton of the path it names. -/
def X3_CtxY : Ctx (([],x),x) := X3_Ctx.cons (.sngl (.sel (.var .here) la))

/-- `y : (x.a).type`. -/
def X3_y : PathTy X3_CtxY (.var .here) (.sngl (.sel (.var (.there .here)) la)) :=
  pvar' .here rfl

/-- `x.a : {val b : ⊤}` again, one binder further in. -/
def X3_xaW : PathTy X3_CtxY (.sel (.var (.there .here)) la) X3_B :=
  (pvar' (.there .here) rfl).sel

/-- `Sngl-Trans`: under the singleton, `y` has every type `x.a` has. -/
def X3_yB : PathTy X3_CtxY (.var .here) X3_B := X3_y.snglTrans X3_xaW

/-- `Fld-E` under the singleton: `y.b : ⊤`, the second hop. -/
def X3_yb : PathTy X3_CtxY (.sel (.var .here) lb) .top := X3_yB.sel

/-- The body as a term, `y.b`, through `Fld` on the stable member. -/
def X3_body : HasTy X3_CtxY (.proj .here lb) .top :=
  .proj (.path (X3_yB.sub .vfldToFld))

/-- `let y = x.a in y.b`, typed by `letSngl`. -/
def X3 : HasTy X3_Ctx (.let (.proj .here la) (.proj .here lb)) .top :=
  .letSngl X3_xa X3_body .top

/-- The same program with the opaque `let`: `HasTy.let` stands beside
`letSngl`, and it also types this term, since `⊤` needs no singleton. -/
def X3_opaque : HasTy X3_Ctx (.let (.proj .here la) (.proj .here lb)) .top :=
  .let (.proj (.path (X3_x.sub .vfldToFld)))
    (.proj (.path ((pvar' (.here) rfl).sub .vfldToFld))) .top

/-! ## X4: gDOT Fig. 2, the `types` literal, and T9

gDOT Fig. 2 (`survey-gdot.md` §2) writes the Dotty fragment of Fig. 1 in pDOT
syntax.  Its `types` literal is

```text
types = νtypes. {
  Type       >: ⊥ = ⊤
  TypeTop    >: ⊥ = types.Type
  newTypeTop : ⊤ → types.TypeTop            = λ_. …
  TypeRef    >: ⊥ = types.Type ∧ {symb : pcore.symbols.Symbol}
  newTypeRef : pcore.symbols.Symbol → types.TypeRef = λs. …
}
```

The page is that literal, with the enclosing module `pcore` a context binder
rather than a second literal, since nothing here eliminates a member of
`pcore`.  `pcore.symbols.Symbol` is the length-two path selection, the shape
WadlerFest DOT cannot write.  The two lambda fields are stable, by
`DefsTy.trmLam`, and `newTypeRef` allocates `ν(_. {symb = s})`, binds it with
a `let` and returns it at `types.TypeRef`.

T9, `DefsTy.typ_exact`, is the statement that replaces pDOT's `tight_bounds`:
every bound this literal's declaration type gives a type member is an
equality.  The three members are read with `Ty.lookupTypDecl` by `decide` and
each is exact.  `X4_abs` is the other half: the abstract view of Fig. 2,
`TypeRef >: ⊥ <: …`, which `Typ-Abs` derives from the exact declaration, and
which is what pDOT's precise self types refuse. -/

/-- Type label `Type`. -/
def X4_lType : Label := .typ 3
/-- Type label `TypeTop`. -/
def X4_lTypeTop : Label := .typ 4
/-- Type label `TypeRef`. -/
def X4_lTypeRef : Label := .typ 5
/-- Type label `Symbol`. -/
def X4_lSymbol : Label := .typ 6
/-- Term label `newTypeTop`. -/
def X4_lnewTypeTop : Label := .trm 4
/-- Term label `newTypeRef`. -/
def X4_lnewTypeRef : Label := .trm 5
/-- Term label `symbols`. -/
def X4_lsymbols : Label := .trm 6
/-- Term label `symb`. -/
def X4_lsymb : Label := .trm 7

/-- `pcore.symbols.Symbol`, the selection through a path of length two. -/
def X4_Sym (p : BVar s .var) : Ty s := .sel (.sel (.var p) X4_lsymbols) X4_lSymbol
/-- `types.Type`. -/
def X4_TypeSel (t : BVar s .var) : Ty s := .sel (.var t) X4_lType
/-- `types.TypeTop`. -/
def X4_TopSel (t : BVar s .var) : Ty s := .sel (.var t) X4_lTypeTop
/-- `types.TypeRef`. -/
def X4_RefSel (t : BVar s .var) : Ty s := .sel (.var t) X4_lTypeRef
/-- `types.Type ∧ {symb : pcore.symbols.Symbol}`, what `TypeRef` is defined
as. -/
def X4_RefBody (t p : BVar s .var) : Ty s := .and (X4_TypeSel t) (.fld X4_lsymb (X4_Sym p))

/-- The declared type of the `types` literal, with the self at `t` and the
enclosing module at `p`.  Both lambda fields are stable members. -/
def X4_Body (t p : BVar s .var) : Ty s :=
  .and (.and (.and (.and
    (.typ X4_lType .top .top)
    (.typ X4_lTypeTop (X4_TypeSel t) (X4_TypeSel t)))
    (.vfld X4_lnewTypeTop (.all .top (X4_TopSel (.there t)))))
    (.typ X4_lTypeRef (X4_RefBody t p) (X4_RefBody t p)))
    (.vfld X4_lnewTypeRef (.all (X4_Sym p) (X4_RefSel (.there t))))

/-- The declaration type is declaration-shaped. -/
theorem X4_BodyDecl (t p : BVar s .var) : Ty.Decl (X4_Body t p) :=
  .and (.and (.and (.and .typ .typ) .vfld) .typ) .vfld

/-- The literal's definitions.  `newTypeTop` returns its own argument, which
is `⊤` and therefore below `types.Type` and below `types.TypeTop`;
`newTypeRef` allocates `ν(_. {symb = s})` and lets it out at
`types.TypeRef`. -/
def X4_Defs (t p : BVar s .var) : Defs s :=
  .and (.and (.and (.and
    (.typ X4_lType .top)
    (.typ X4_lTypeTop (X4_TypeSel t)))
    (.trm X4_lnewTypeTop (.val (.lam .top (.path .here)))))
    (.typ X4_lTypeRef (X4_RefBody t p)))
    (.trm X4_lnewTypeRef (.val (.lam (X4_Sym p)
      (.let (.val (.obj (.trm X4_lsymb (.path (.there .here))))) (.path .here)))))

theorem X4_Distinct (t p : BVar s .var) : Defs.Distinct (X4_Defs t p) := by
  refine .and (.and (.and (.and .typ .typ ?_) .trm ?_) .typ ?_) .trm ?_ <;>
    (intro ℓ h
     simp only [Defs.labels, List.mem_append, List.mem_singleton] at h ⊢
     rintro rfl
     revert h
     decide)

/-- `Rec-E` at the self, with the declaration type opened at the variable the
self is bound to. -/
def X4_openSelf {Γ : Ctx s} {t p : BVar s .var}
    (h : PathTy Γ (.var t) (.mu (X4_Body .here (.there p)))) :
    PathTy Γ (.var t) (X4_Body t p) :=
  h.recE (X4_BodyDecl _ _)

/-- The member `Type`, read off the opened self. -/
def X4_mType {Γ : Ctx s} {t p : BVar s .var} (h : PathTy Γ (.var t) (X4_Body t p)) :
    PathTy Γ (.var t) (.typ X4_lType .top .top) :=
  h.sub (.trans .and1 (.trans .and1 (.trans .and1 .and1)))

/-- The member `TypeTop`. -/
def X4_mTypeTop {Γ : Ctx s} {t p : BVar s .var} (h : PathTy Γ (.var t) (X4_Body t p)) :
    PathTy Γ (.var t) (.typ X4_lTypeTop (X4_TypeSel t) (X4_TypeSel t)) :=
  h.sub (.trans .and1 (.trans .and1 (.trans .and1 .and2)))

/-- The member `TypeRef`. -/
def X4_mTypeRef {Γ : Ctx s} {t p : BVar s .var} (h : PathTy Γ (.var t) (X4_Body t p)) :
    PathTy Γ (.var t) (.typ X4_lTypeRef (X4_RefBody t p) (X4_RefBody t p)) :=
  h.sub (.trans .and1 .and2)

/-- The context of the literal's self binder. -/
def X4_CtxSelf {Γ : Ctx s} (p : BVar s .var) : Ctx (s,x) :=
  Γ.consSelf (X4_Defs .here (.there p)) (X4_Body .here (.there p))

/-- `newTypeTop = λ(u : ⊤). u` at `∀(u : ⊤) types.TypeTop`.  The body is the
argument, and `⊤ <: types.Type <: types.TypeTop` by the two lower bounds. -/
def X4_newTypeTop {Γ : Ctx s} (p : BVar s .var) :
    HasTy (X4_CtxSelf (Γ := Γ) p) (.val (.lam .top (.path .here)))
      (.all .top (X4_TopSel (.there .here))) := by
  refine .lam ?_ .top
  have hopen : PathTy ((X4_CtxSelf (Γ := Γ) p).cons .top) (.var (.there .here))
      (X4_Body (.there .here) (.there (.there p))) :=
    X4_openSelf (pvar' (.there .here) rfl)
  exact .sub (.sub (var' .here rfl) .top)
    (.trans (.selLower (X4_mType hopen)) (.selLower (X4_mTypeTop hopen)))

/-- `newTypeRef = λ(s : pcore.symbols.Symbol). let o = ν(_. {symb = s}) in o`
at `∀(s : pcore.symbols.Symbol) types.TypeRef`.  The nested literal is bound
by a `let`, opened by `Rec-E` at the binder, widened to
`types.Type ∧ {symb : pcore.symbols.Symbol}` and let out at
`types.TypeRef`. -/
def X4_newTypeRef {Γ : Ctx s} (p : BVar s .var) :
    HasTy (X4_CtxSelf (Γ := Γ) p) (.val (.lam (X4_Sym (.there p))
      (.let (.val (.obj (.trm X4_lsymb (.path (.there .here))))) (.path .here))))
      (.all (X4_Sym (.there p)) (X4_RefSel (.there .here))) := by
  refine .lam ?_ .sel
  have hObj : HasTy ((X4_CtxSelf (Γ := Γ) p).cons (X4_Sym (.there p)))
      (.val (.obj (.trm X4_lsymb (.path (.there .here)))))
      (.mu (.fld X4_lsymb (X4_Sym (.there (.there (.there p)))))) :=
    .obj (.trm (var' (.there .here) rfl)) .trm
  refine .let hObj ?_ .sel
  have hopen : PathTy
      (((X4_CtxSelf (Γ := Γ) p).cons (X4_Sym (.there p))).cons
        (.mu (.fld X4_lsymb (X4_Sym (.there (.there (.there p)))))))
      (.var (.there (.there .here)))
      (X4_Body (.there (.there .here)) (.there (.there (.there p)))) :=
    X4_openSelf (pvar' (.there (.there .here)) rfl)
  exact .sub (HasTy.recE (var' .here rfl) .fld)
    (.trans (.and (.trans .top (.selLower (X4_mType hopen))) .refl)
      (.selLower (X4_mTypeRef hopen)))

/-- The five members of the `types` literal. -/
def X4_DefsTy {Γ : Ctx s} (p : BVar s .var) :
    DefsTy (X4_CtxSelf (Γ := Γ) p) (X4_Defs .here (.there p)) (X4_Body .here (.there p)) :=
  .and (.and (.and (.and .typ .typ) (.trmLam (X4_newTypeTop p))) .typ)
    (.trmLam (X4_newTypeRef p))

/-- The `types` literal of gDOT Fig. 2. -/
def X4_lit {Γ : Ctx s} (p : BVar s .var) :
    HasTy Γ (.val (.obj (X4_Defs .here (.there p)))) (.mu (X4_Body .here (.there p))) :=
  .obj (X4_DefsTy p) (X4_Distinct _ _)

/-! ### T9 on the `types` literal

The literal at a concrete context: `pcore` is one binder, typed `⊤`, since
nothing eliminates a member of it.  Everything below is closed, so the reader
runs by `decide`. -/

/-- `pcore : ⊤`, the enclosing module as a context binder. -/
def X4_Ctx : Ctx ([],x) := .cons .nil .top

/-- The declaration type of `types`, at that context. -/
def X4_Body0 : Ty (([],x),x) := X4_Body .here (.there .here)

def X4_DefsTy0 :
    DefsTy (X4_CtxSelf (Γ := X4_Ctx) .here) (X4_Defs .here (.there .here)) X4_Body0 :=
  X4_DefsTy .here

/-- The literal, at that context. -/
def X4_lit0 : HasTy X4_Ctx (.val (.obj (X4_Defs .here (.there .here)))) (.mu X4_Body0) :=
  X4_lit .here

/-- T9 on gDOT Fig. 2's `types`: every type member of the literal's
declaration type has equal bounds.  It is the statement that replaces pDOT's
`tight_bounds`, and it is what makes the literal's own self usable. -/
theorem X4_exact {A : Label} {S U : Ty (([],x),x)}
    (hA : X4_Body0.lookupTypDecl A = some (S, U)) : S = U :=
  DefsTy.typ_exact X4_DefsTy0 hA

/-- The reader finds `Type`. -/
theorem X4_lookupType : X4_Body0.lookupTypDecl X4_lType = some (.top, .top) := by decide
/-- The reader finds `TypeTop`. -/
theorem X4_lookupTypeTop :
    X4_Body0.lookupTypDecl X4_lTypeTop = some (X4_TypeSel .here, X4_TypeSel .here) := by decide
/-- The reader finds `TypeRef`, the member pDOT's precise self types refuse. -/
theorem X4_lookupTypeRef :
    X4_Body0.lookupTypDecl X4_lTypeRef
      = some (X4_RefBody .here (.there .here), X4_RefBody .here (.there .here)) := by decide
/-- `Symbol` is declared by the other module, not by this literal. -/
theorem X4_lookupSymbol : X4_Body0.lookupTypDecl X4_lSymbol = none := by decide

/-- T9 at `Type`. -/
theorem X4_exactType : (Ty.top : Ty (([],x),x)) = .top := X4_exact X4_lookupType
/-- T9 at `TypeTop`. -/
theorem X4_exactTypeTop :
    X4_TypeSel (.here : BVar (([],x),x) .var) = X4_TypeSel .here := X4_exact X4_lookupTypeTop
/-- T9 at `TypeRef`. -/
theorem X4_exactTypeRef :
    X4_RefBody (.here : BVar (([],x),x) .var) (.there .here)
      = X4_RefBody .here (.there .here) := X4_exact X4_lookupTypeRef

/-! ### The abstract view of Fig. 2

Fig. 2 writes `TypeRef >: ⊥ = …`, and reads it abstractly as
`TypeRef >: ⊥ <: …`.  `Typ-Abs` is that reading: the abstract view drops the
lower bound to `⊥` by a self-free step and keeps the upper bound.  pDOT
rejects this object because it asks the self type to be precise; here the
precise type is derived and the abstract one is reached by `Sub.mu`. -/

/-- The abstract view of the member `TypeRef`. -/
def X4_abs {Γ : Ctx s} {p : BVar s .var} :
    SubDecl Γ (X4_Body .here (.there p))
      (.typ X4_lTypeRef .bot (X4_RefBody .here (.there p))) :=
  .typ rfl .bot .refl

/-- The whole literal's type, read abstractly. -/
def X4_muAbs {Γ : Ctx s} {p : BVar s .var} :
    Sub Γ (.mu (X4_Body .here (.there p)))
      (.mu (.typ X4_lTypeRef .bot (X4_RefBody .here (.there p)))) :=
  .mu X4_abs (X4_BodyDecl _ _) .typ

end Examples
end DotMNF

end Paths
