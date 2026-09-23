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
inverts definition typing: the one stable rule, `trmObj`, asks for an object
literal body (P2 g0, decision 27), the body here is the projection `x.a`, so
every derivation of these definitions types `a` as a computation member.
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
can be given declares `a` as a computation member.  `trmObj` asks for an
object literal body, and the body is the projection `x.a`, so `trm` is the
only rule that applies. -/
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
two is written with a `let`.  `x : {val a : {val b : ⊤}}`, both members stable,
since `Fld-E` reads stable members only (X2).

After P2 g0 the derived `HasTy.letSngl` applies only over a field declared at a
singleton (decision 23), and `a` is declared at `{val b : ⊤}`.  So `X3` types
the program with the opaque `let`, and both projections read a path typing of
the receiver through `HasTy.projP` (decision 28).  The body keeps its
derivation under the singleton binder: in `X3_CtxY` the binder `y` is bound at
`(x.a).type`, `Sngl-Trans` carries `x.a`'s stable member to `y`, and `Fld-E`
then reads `y.b`.  That is `X3_body` and `X3_yb`. -/

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

/-- The body as a term, `y.b`, under the singleton binder: `HasTy.projP` reads
the stable member of `y` as a member (decision 28). -/
def X3_body : HasTy X3_CtxY (.proj .here lb) .top :=
  .projP (X3_yB.sub .vfldToFld)

/-- `let y = x.a in y.b`, typed by the opaque `let` (decision 23): the field
`a` is declared at `{val b : ⊤}`, not at a singleton, so the derived
`letSngl` does not apply.  This is the former `X3_opaque`. -/
def X3 : HasTy X3_Ctx (.let (.proj .here la) (.proj .here lb)) .top :=
  .let (.projP (X3_x.sub .vfldToFld))
    (.projP ((pvar' (.here) rfl).sub .vfldToFld)) .top

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
WadlerFest DOT cannot write.  The two lambda fields are plain, typed by
`DefsTy.trm`, since after P2 g0 only an object literal body makes a field
stable (decision 27).  `newTypeRef` allocates `ν(_. {symb = s})`, binds it with
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
enclosing module at `p`.  Both lambda fields are plain members (decision
27). -/
def X4_Body (t p : BVar s .var) : Ty s :=
  .and (.and (.and (.and
    (.typ X4_lType .top .top)
    (.typ X4_lTypeTop (X4_TypeSel t) (X4_TypeSel t)))
    (.fld X4_lnewTypeTop (.all .top (X4_TopSel (.there t)))))
    (.typ X4_lTypeRef (X4_RefBody t p) (X4_RefBody t p)))
    (.fld X4_lnewTypeRef (.all (X4_Sym p) (X4_RefSel (.there t))))

/-- The declaration type is declaration-shaped. -/
theorem X4_BodyDecl (t p : BVar s .var) : Ty.Decl (X4_Body t p) :=
  .and (.and (.and (.and .typ .typ) .fld) .typ) .fld

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
  .and (.and (.and (.and .typ .typ) (.trm (X4_newTypeTop p))) .typ)
    (.trm (X4_newTypeRef p))

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

/-! ## The P3 pages: labels

The P3 pages reuse the labels of E1 to E8 above and declare the rest once,
here.  `lf` and `lc` serve the hop pages, `lC` serves E11 and P3e, and the
`Fig2_` labels serve Fig. 2 in X4's naming.  Two names may share a value, since a label is
compared only inside one literal.  `lC` and `X4_lType` are both `.typ 3`, and
`lf` and `X4_lnewTypeTop` are both `.trm 4`. -/

/-- Term label `f`, the stable field of the hop pages. -/
def lf : Label := .trm 4
/-- Term label `c`, the stable field of E2p, E6p and E7p. -/
def lc : Label := .trm 3
/-- Type label `C`. -/
def lC : Label := .typ 3
/-- Type label `Option`. -/
def Fig2_lOption : Label := .typ 7
/-- Term label `types`. -/
def Fig2_ltypes : Label := .trm 8
/-- Term label `tpe`. -/
def Fig2_ltpe : Label := .trm 9
/-- Term label `id`. -/
def Fig2_lid : Label := .trm 10
/-- Term label `newSymbol`. -/
def Fig2_lnewSymbol : Label := .trm 11
/-- Term label `n`, the member of the stand-in for `Nat`. -/
def Fig2_ln : Label := .trm 12

/-! ## E1p: bad bounds under a lambda, at a path

`λ(w : {val f : {A : ⊤..⊥}}). let y = w in y` at `∀(w : …) {B : {a : ⊤}..{a : ⊤}}`.
E1 with the receiver one hop deeper.  `f` is `val` in a binder's declared
type, which decision 27 (a) keeps.  The bounds are read at the path `w.f`
through `Fld-E` at the parameter, whose root is opaque.  So the context has no
block for `w.f`, and the target reads the `∋ᵛ f` off the declared type. -/

/-- `{val f : {A : ⊤..⊥}}`. -/
def E1p_Dom : Ty s := .vfld lf (.typ lA .top .bot)
/-- `{B : {a : ⊤}..{a : ⊤}}`, E1's unrelated result type. -/
def E1p_Res : Ty s := E1Res

def E1p_Ctx1 : Ctx ([],x) := Ctx.nil.cons E1p_Dom

/-- `Fld-E` at the parameter's stable field: `w.f : {A : ⊤..⊥}`. -/
def E1p_hwf : PathTy E1p_Ctx1 (.sel (.var .here) lf) (.typ lA .top .bot) := (pvar' .here rfl).sel

/-- `Dom <: ⊤ <: w.f.A <: ⊥ <: Res`: bad bounds at a path of length two. -/
def E1p_badBounds : Sub E1p_Ctx1 E1p_Dom E1p_Res :=
  .trans .top (.trans (.selLower E1p_hwf) (.trans (.selUpper E1p_hwf) .bot))

def E1p_body : HasTy E1p_Ctx1 (.let (.path .here) (.path .here)) E1p_Res :=
  .let (.sub (var' .here rfl) E1p_badBounds) (var' .here rfl) (.typ (.fld .top) (.fld .top))

def E1p_term : Tm [] := .val (.lam E1p_Dom (.let (.path .here) (.path .here)))

def E1p : HasTy Ctx.nil E1p_term (.all E1p_Dom E1p_Res) := .lam E1p_body (.vfld (.typ .top .bot))

/-! ## E2p: a path-keyed block that mentions itself

`let x = ν(x. {val c = ν(z. {A = ∀(y : x.c.A) x.c.A} ∧ {a = λ(y : x.c.A). y})})
in let c = x.c in let f = c.a in f f` at `⊤`.  E2 with the literal one hop
deeper.  `c` is `val`, `a` plain.  The child block at `x.c` has a witness that
names `x.c`, and a function projected through a stable field is applied to
itself.  The argument goes by `<:-Sel` at the path `x.c`. -/

/-- `x.c.A`, in the inner literal's scope (`z` at `.here`, `x` at `.there .here`). -/
def E2p_xcA (x : BVar s .var) : Ty s := .sel (.sel (.var x) lc) lA
/-- `∀(y : x.c.A) x.c.A`. -/
def E2p_AT (x : BVar s .var) : Ty s := .all (E2p_xcA x) (E2p_xcA (.there x))
/-- `{A : AT..AT} ∧ {a : AT}`. -/
def E2p_innerT (x : BVar s .var) : Ty s := .and (.typ lA (E2p_AT x) (E2p_AT x)) (.fld la (E2p_AT x))
/-- `{A = AT} ∧ {a = λ(y : x.c.A). y}`. -/
def E2p_innerD (x : BVar s .var) : Defs s :=
  .and (.typ lA (E2p_AT x)) (.trm la (.val (.lam (E2p_xcA x) (.path .here))))

theorem E2p_innerDistinct (x : BVar s .var) : Defs.Distinct (E2p_innerD x) := by
  refine .and .typ .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def E2p_outerD : Defs ([],x) := .trm lc (.val (.obj (E2p_innerD (.there .here))))
def E2p_outerT : Ty ([],x) := .vfld lc (.mu (E2p_innerT (.there .here)))

def E2p_innerDefsTy {Γ : Ctx ([],x)} :
    DefsTy (Γ.consSelf (E2p_innerD (.there .here)) (E2p_innerT (.there .here)))
      (E2p_innerD (.there .here)) (E2p_innerT (.there .here)) :=
  .and .typ (.trm (.lam (var' .here rfl) .sel))

def E2p_lit : HasTy Ctx.nil (.val (.obj E2p_outerD)) (.mu E2p_outerT) :=
  .obj (.trmObj E2p_innerDefsTy (E2p_innerDistinct _)) .trm

def E2p_Γ1 : Ctx ([],x) := Ctx.nil.cons (.mu E2p_outerT)

/-- `x : {val c : μ(z. …)}`. -/
def E2p_hx1 : PathTy E2p_Γ1 (.var .here) (.vfld lc (.mu (E2p_innerT (.there .here)))) :=
  (pvar' .here rfl).recE (T := E2p_outerT.rename FCdot.Rename.succ.lift) .vfld

def E2p_Γ2 : Ctx (([],x),x) := E2p_Γ1.cons (.mu (E2p_innerT (.there .here)))

/-- `c.a : AT`, by `Rec-E` at `c`. -/
def E2p_ca : HasTy E2p_Γ2 (.proj .here la) (E2p_AT (.there .here)) :=
  .proj (.sub (HasTy.recE (T := (E2p_innerT (.there .here)).rename FCdot.Rename.succ.lift)
    (var' .here rfl) (.and .typ .fld)) .and2)

def E2p_Γ3 : Ctx ((([],x),x),x) := E2p_Γ2.cons (E2p_AT (.there .here))

/-- `x.c : {A : AT..AT}`, by `Fld-E` and `Rec-E` at the path. -/
def E2p_xcTyp : PathTy E2p_Γ3 (.sel (.var (.there (.there .here))) lc)
    (.typ lA (E2p_AT (.there (.there .here))) (E2p_AT (.there (.there .here)))) :=
  ((((pvar' (.there (.there .here)) rfl).recE
    (T := ((E2p_outerT.rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift).rename
      FCdot.Rename.succ.lift) (by decide)).sel).recE (.and .typ .fld)).sub .and1

/-- `f f`: the argument by `<:-Sel` at `x.c`. -/
def E2p_app : HasTy E2p_Γ3 (.app .here .here) (E2p_xcA (.there (.there .here))) :=
  .app (var' .here rfl : HasTy E2p_Γ3 (.path .here)
      (.all (E2p_xcA (.there (.there .here))) (E2p_xcA (.there (.there (.there .here))))))
    (.sub (var' .here rfl) (.selLower E2p_xcTyp))

def E2p_term : Tm [] :=
  .let (.val (.obj E2p_outerD)) (.let (.proj .here lc) (.let (.proj .here la) (.app .here .here)))

def E2p : HasTy Ctx.nil E2p_term .top :=
  .let E2p_lit (.let (.projP (E2p_hx1.sub .vfldToFld)) (.let E2p_ca (.sub E2p_app .top) .top) .top) .top

/-! ## E3p: one block name, two propositions

`λ(w : {val f : {A : ⊥..T₁} ∧ {A : T₂..⊤}}). λ(z : T₂). let y = z in y` at
`∀ ∀ T₁`.  E3 with the receiver one hop deeper.  Two propositions about the
one name `w.f ∙ A`, each read at the same path. -/

def E3p_Dom : Ty s := .vfld lf E3Dom
def E3p_Ctx2 : Ctx (([],x),x) := (Ctx.nil.cons E3p_Dom).cons E3T2

def E3p_wf : PathTy E3p_Ctx2 (.sel (.var (.there .here)) lf) E3Dom := (pvar' (.there .here) rfl).sel

/-- `T₂ <: w.f.A <: T₁`. -/
def E3p_sub : Sub E3p_Ctx2 E3T2 E3T1 :=
  .trans (.selLower (E3p_wf.sub .and2)) (.selUpper (E3p_wf.sub .and1))

def E3p_term : Tm [] :=
  .val (.lam E3p_Dom (.val (.lam E3T2 (.let (.path .here) (.path .here)))))

def E3p : HasTy Ctx.nil E3p_term (.all E3p_Dom (.all E3T2 E3T1)) :=
  .lam (.lam (.let (.sub (var' .here rfl) E3p_sub) (var' .here rfl) (.fld .top)) (.fld .top))
    (.vfld (.and (.typ .bot (.fld .top)) (.typ (.fld .top) .top)))

/-! ## E4p: the counterexample of §1, the receiver of the two bounds at `x.f`

`λ(x : {val f : {B : S..T}}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`
at `∀ ∀ ∀ w.A`, with `S <: x.f.B <: T` the step with no realizer.  E4's
derivation with `Fld-E` at `x.f` in place of the variable `x`. -/

def E4p_X : Ty s := .vfld lf E4X
def E4p_Ctx1 : Ctx ([],x) := .cons .nil E4p_X
def E4p_Ctx2 : Ctx ([],x,x) := .cons E4p_Ctx1 E4S
def E4p_Ctx3 : Ctx ([],x,x,x) := .cons E4p_Ctx2 E4Int
def E4p_Ctx4 : Ctx ([],x,x,x,x) := .cons E4p_Ctx3 E4G

def E4p_xf3 : PathTy E4p_Ctx3 (.sel (.var (.there (.there .here))) lf) E4X :=
  (pvar' (.there (.there .here)) rfl).sel
def E4p_xf4 : PathTy E4p_Ctx4 (.sel (.var (.there (.there (.there .here)))) lf) E4X :=
  (pvar' (.there (.there (.there .here))) rfl).sel

/-- `S <: x.f.B <: T`, the step with no realizer, at a path. -/
def E4p_ST4 : Sub E4p_Ctx4 E4S E4T := .trans (.selLower E4p_xf4) (.selUpper E4p_xf4)

def E4p_g : HasTy E4p_Ctx3 (.val (.lam (.sel (.var (.there .here)) lA) (.path .here))) E4G :=
  .lam (var' .here rfl) .sel
def E4p_wT4 : HasTy E4p_Ctx4 (.path (.there (.there .here))) E4T :=
  .sub (var' (.there (.there .here)) rfl) E4p_ST4
def E4p_nA : HasTy E4p_Ctx4 (.path (.there .here)) (.sel (.var (.there (.there .here))) lA) :=
  .sub (var' (.there .here) rfl) (.selLower E4p_wT4.toPathTy)
def E4p_app : HasTy E4p_Ctx4 (.app .here (.there .here)) (.sel (.var (.there (.there .here))) lA) :=
  .app (var' .here rfl : HasTy E4p_Ctx4 (.path .here) E4G') E4p_nA
def E4p_letG : HasTy E4p_Ctx3 (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path .here)))
    (.app .here (.there .here))) (.sel (.var (.there .here)) lA) := .let E4p_g E4p_app .sel

def E4p_term : Tm [] :=
  .val (.lam E4p_X (.val (.lam E4S (.val (.lam E4Int
    (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path .here))) (.app .here (.there .here))))))))

def E4p_ty : Ty [] := .all E4p_X (.all E4S (.all E4Int (.sel (.var (.there .here)) lA)))

def E4p : HasTy Ctx.nil E4p_term E4p_ty :=
  .lam (.lam (.lam E4p_letG (.fld .top)) (.typ .bot .top))
    (.vfld (.typ (.typ .bot .top) (.typ (.fld .top) .top)))

/-! ## E5p: an object returned and selected through a stable field

`λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z. {val o = ν(u. {a = v})})
in let r = f w in let o = r.o in o.a` at `∀(w) w.A`.  `o` is `val`, `a` plain.
`App` renames `v` to `w` inside a nested `μ` under a stable field, and `r.o` is
a stable path at an opaque binder.  The label `o` is `lb`. -/

/-- `{a : v.A}` under the inner self, `v` at `.there (.there .here)`. -/
def E5p_innerT (v : BVar s .var) : Ty s := .fld la (.sel (.var v) lA)
def E5p_innerD (v : BVar s .var) : Defs s := .trm la (.path v)
/-- `{val o : μ(u. {a : v.A})}` under the outer self, `v` at `.there .here`. -/
def E5p_outerT (v : BVar s .var) : Ty s := .vfld lb (.mu (E5p_innerT (.there v)))
def E5p_outerD : Defs ((([],x),x),x) := .trm lb (.val (.obj (E5p_innerD (.there (.there .here)))))

def E5p_Ctx1 : Ctx ([],x) := Ctx.nil.cons E5AT
def E5p_Ctxv : Ctx (([],x),x) := E5p_Ctx1.cons E5AT
def E5p_Ctxz : Ctx ((([],x),x),x) := E5p_Ctxv.consSelf E5p_outerD (E5p_outerT (.there .here))
def E5p_Ctxu : Ctx (((([],x),x),x),x) :=
  E5p_Ctxz.consSelf (E5p_innerD (.there (.there .here))) (E5p_innerT (.there (.there .here)))

/-- The field `a = v`, at `v.A` by `<:-Sel`. -/
def E5p_fieldA :
    HasTy E5p_Ctxu (.path (.there (.there .here))) (.sel (.var (.there (.there .here))) lA) :=
  .sub (.sub (var' (.there (.there .here)) rfl) .top) (.selLower (pvar' (.there (.there .here)) rfl))

def E5p_objTy : HasTy E5p_Ctxv (.val (.obj E5p_outerD)) (.mu (E5p_outerT (.there .here))) :=
  .obj (.trmObj (.trm E5p_fieldA) .trm) .trm

def E5p_FT : Ty ([],x) := .all E5AT (.mu (E5p_outerT (.there .here)))
def E5p_fVal : HasTy E5p_Ctx1 (.val (.lam E5AT (.val (.obj E5p_outerD)))) E5p_FT :=
  .lam E5p_objTy (.typ .top .top)

def E5p_Ctxf : Ctx (([],x),x) := E5p_Ctx1.cons E5p_FT
/-- `f w : μ(z. {val o : μ(u. {a : w.A})})`. -/
def E5p_rTy : Ty (([],x),x) := .mu (E5p_outerT (.there (.there .here)))
def E5p_app : HasTy E5p_Ctxf (.app .here (.there .here)) E5p_rTy :=
  .app (var' .here rfl : HasTy E5p_Ctxf (.path .here) (.all E5AT (.mu (E5p_outerT (.there .here)))))
    (var' (.there .here) rfl)

def E5p_Ctxr : Ctx ((([],x),x),x) := E5p_Ctxf.cons E5p_rTy
/-- `r.o`, by `projP` through `Fld-E`'s premise at `r`. -/
def E5p_oTy : Ty ((([],x),x),x) := .mu (E5p_innerT (.there (.there (.there .here))))
def E5p_ro : HasTy E5p_Ctxr (.proj .here lb) E5p_oTy :=
  .projP (((pvar' .here rfl).recE (T := (E5p_outerT (.there (.there .here)) : Ty ((([],x),x),x)).rename
    (FCdot.Rename.succ (k := .var)).lift) .vfld).sub .vfldToFld)

def E5p_Ctxo : Ctx (((([],x),x),x),x) := E5p_Ctxr.cons E5p_oTy
def E5p_oa : HasTy E5p_Ctxo (.proj .here la) (.sel (.var (.there (.there (.there .here)))) lA) :=
  .proj (HasTy.recE (T := (E5p_innerT (.there (.there (.there .here))) : Ty (((([],x),x),x),x)).rename
    (FCdot.Rename.succ (k := .var)).lift) (var' .here rfl) .fld)

def E5p_term : Tm [] :=
  .val (.lam E5AT (.let (.val (.lam E5AT (.val (.obj E5p_outerD))))
    (.let (.app .here (.there .here)) (.let (.proj .here lb) (.proj .here la)))))

def E5p : HasTy Ctx.nil E5p_term (.all E5AT (.sel (.var .here) lA)) :=
  .lam (.let E5p_fVal (.let E5p_app (.let E5p_ro E5p_oa .sel) .sel) .sel) (.typ .top .top)

/-- `r.o` is a stable path in the client: `Fld-E` at `r`. -/
def E5p_roPath : PathTy E5p_Ctxr (.sel (.var .here) lb) E5p_oTy :=
  ((pvar' .here rfl).recE (T := (E5p_outerT (.there (.there .here)) : Ty ((([],x),x),x)).rename
    (FCdot.Rename.succ (k := .var)).lift) .vfld).sel

/-! ## E6p: a field typed at a member of its own literal's stable field

`λ(n : Int). ν(x. {val c = ν(z. {T = Int})} ∧ {v = n})` at
`∀(n) μ(x. {val c : μ(z. {T : Int..Int})} ∧ {v : x.c.T})`.  `c` is `val`, `v`
plain.  After decision 27 the sketch's `{val v : x.c.T}` is `{v : x.c.T}`,
since `v` holds a variable.  `Fld-E` at the self while its own fields are
typed. -/

def E6p_innerT : Ty s := .typ lT E6Int E6Int
def E6p_innerD : Defs s := .typ lT E6Int
/-- `{val c : μ(z. {T : Int..Int})} ∧ {v : x.c.T}`. -/
def E6p_outerT : Ty (([],x),x) :=
  .and (.vfld lc (.mu E6p_innerT)) (.fld lv (.sel (.sel (.var .here) lc) lT))
def E6p_outerD : Defs (([],x),x) :=
  .and (.trm lc (.val (.obj E6p_innerD))) (.trm lv (.path (.there .here)))

theorem E6p_outerDistinct : Defs.Distinct E6p_outerD := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def E6p_Ctx1 : Ctx ([],x) := Ctx.nil.cons E6Int
def E6p_Ctxx : Ctx (([],x),x) := E6p_Ctx1.consSelf E6p_outerD E6p_outerT

/-- `x.c : {T : Int..Int}`: `Fld-E` at the self's stable field, `Rec-E` at the path. -/
def E6p_xcT : PathTy E6p_Ctxx (.sel (.var .here) lc) (.typ lT E6Int E6Int) :=
  ((((pvar' .here rfl).recE (T := E6p_outerT.rename (FCdot.Rename.succ (k := .var)).lift)
    (.and .vfld .fld)).sub .and1).sel).recE .typ

/-- `n : Int <: x.c.T`. -/
def E6p_nT : HasTy E6p_Ctxx (.path (.there .here)) (.sel (.sel (.var .here) lc) lT) :=
  .sub (var' (.there .here) rfl) (.selLower E6p_xcT)

def E6p_lit : HasTy E6p_Ctx1 (.val (.obj E6p_outerD)) (.mu E6p_outerT) :=
  .obj (.and (.trmObj .typ .typ) (.trm E6p_nT)) E6p_outerDistinct

def E6p_term : Tm [] := .val (.lam E6Int (.val (.obj E6p_outerD)))
def E6p : HasTy Ctx.nil E6p_term (.all E6Int (.mu E6p_outerT)) := .lam E6p_lit (.fld .top)

/-! ## E7p: an alias cycle below a field

`ν(x. {val c = ν(z. {A = x.c.B} ∧ {B = x.c.A})})`.  `c` is `val`.  Y3 is the
hand-written store of the same cycle.  Here the literal is a translation, and
the cycle is resolved in the translated self context. -/

def E7p_xcX (X : Label) : Ty (([],x),x) := .sel (.sel (.var (.there .here)) lc) X
def E7p_innerT : Ty (([],x),x) :=
  .and (.typ lA (E7p_xcX lB) (E7p_xcX lB)) (.typ lB (E7p_xcX lA) (E7p_xcX lA))
def E7p_innerD : Defs (([],x),x) := .and (.typ lA (E7p_xcX lB)) (.typ lB (E7p_xcX lA))
theorem E7p_innerDistinct : Defs.Distinct E7p_innerD := by
  refine .and .typ .typ ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide
def E7p_outerD : Defs ([],x) := .trm lc (.val (.obj E7p_innerD))
def E7p_outerT : Ty ([],x) := .vfld lc (.mu E7p_innerT)

def E7p_lit : HasTy Ctx.nil (.val (.obj E7p_outerD)) (.mu E7p_outerT) :=
  .obj (.trmObj (.and .typ .typ) E7p_innerDistinct) .trm

/-! ## E8p: refining an abstract type at a path

`λ(x : {val f : {A : ⊥..{a : ⊤}}}). λ(y : x.f.A ∧ {a : ⊤}). y.a` at `∀ ∀ ⊤`,
by two routes.  `E8p` goes by `And₁` then `Sel-<:` at the path `x.f`, and
`E8p2` by `And₂`.  A self-bound proposition whose bound is a selection
through a stable field. -/

def E8p_Dom : Ty s := .vfld lf E8Dom
def E8p_Ref (x : BVar s .var) : Ty s := .and (.sel (.sel (.var x) lf) lA) (.fld la .top)
def E8p_Ctx2 : Ctx ([],x,x) := (Ctx.nil.cons E8p_Dom).cons (E8p_Ref .here)

def E8p_xf : PathTy E8p_Ctx2 (.sel (.var (.there .here)) lf) E8Dom := (pvar' (.there .here) rfl).sel

/-- `y.a` through `And₁` and `Sel-<:` at `x.f`. -/
def E8p_body1 : HasTy E8p_Ctx2 (.proj .here la) .top :=
  .proj (.sub (.sub (var' .here rfl : HasTy E8p_Ctx2 _ (E8p_Ref (.there .here))) .and1)
    (.selUpper E8p_xf))

def E8p_term : Tm [] := .val (.lam E8p_Dom (.val (.lam (E8p_Ref .here) (.proj .here la))))
def E8p_ty : Ty [] := .all E8p_Dom (.all (E8p_Ref .here) .top)

def E8p : HasTy Ctx.nil E8p_term E8p_ty :=
  .lam (.lam E8p_body1 (.and .sel (.fld .top))) (.vfld (.typ .bot (.fld .top)))

/-- The `And₂` route: `y : x.f.A ∧ {a : ⊤}` gives `{a : ⊤}`. -/
def E8p_body2 : HasTy E8p_Ctx2 (.proj .here la) .top :=
  .proj (.sub (var' .here rfl : HasTy E8p_Ctx2 _ (E8p_Ref (.there .here))) .and2)

def E8p2 : HasTy Ctx.nil E8p_term E8p_ty :=
  .lam (.lam E8p_body2 (.and .sel (.fld .top))) (.vfld (.typ .bot (.fld .top)))

/-! ## E9: a singleton at a let

`let q = ν(q. {B = N}) in let x = ν(x. {a = q}) in let y = x.a in λ(z : y.B). let w = z in w`
at `⊤`, with `N = {b : ⊤}`.  `a` is plain, declared `{a : q.type}` by the
derived `DefsTy.trmSngl`.  The `let y = x.a` is the derived `HasTy.letSngl`,
whose premise is `PathTy.var` and `recE` at `x`, and whose binder is
`y : q.type`.  The body reads `y.B <: N` by `Sel-<:` over `Sngl-Trans` at `y`
and `Rec-E` at `q`.  That is decision 28's kept case. -/

/-- `N`, the closed stand-in `{b : ⊤}`. -/
def E9_N : Ty s := .fld lb .top

/-- `q = ν(q. {B = N})`. -/
def E9_qDefs : Defs ([],x) := .typ lB E9_N
def E9_qBody : Ty ([],x) := .typ lB E9_N E9_N
def E9_qDefsTy : DefsTy (Ctx.nil.consSelf E9_qDefs E9_qBody) E9_qDefs E9_qBody := .typ
def E9_qLit : HasTy Ctx.nil (.val (.obj E9_qDefs)) (.mu E9_qBody) := .obj E9_qDefsTy .typ

def E9_Γ1 : Ctx ([],x) := Ctx.nil.cons (.mu E9_qBody)

/-- `x = ν(x. {a = q})`, at `μ(x. {a : q.type})` by the derived `trmSngl`. -/
def E9_xDefs : Defs (([],x),x) := .trm la (.path (.there .here))
def E9_xBody : Ty (([],x),x) := .fld la (.sngl (.var (.there .here)))
def E9_xDefsTy : DefsTy (E9_Γ1.consSelf E9_xDefs E9_xBody) E9_xDefs E9_xBody := DefsTy.trmSngl .var
def E9_xLit : HasTy E9_Γ1 (.val (.obj E9_xDefs)) (.mu E9_xBody) := .obj E9_xDefsTy .trm

def E9_Γ2 : Ctx (([],x),x) := E9_Γ1.cons (.mu E9_xBody)

/-- `x : {a : q.type}`, by `Rec-E` at `x`. -/
def E9_hx : PathTy E9_Γ2 (.var .here) (.fld la (.sngl (.var (.there .here)))) :=
  (pvar' .here rfl).recE (T := E9_xBody.rename FCdot.Rename.succ.lift) .fld

/-- The body's context: `y : q.type`, then `z : y.B`. -/
def E9_Γ3 : Ctx ((([],x),x),x) := E9_Γ2.cons (.sngl (.var (.there .here)))
def E9_Γ4 : Ctx (((([],x),x),x),x) := E9_Γ3.cons (.sel (.var .here) lB)

/-- `q : {B : N..N}` in the body. -/
def E9_hqB : PathTy E9_Γ4 (.var (.there (.there (.there .here)))) (.typ lB E9_N E9_N) :=
  (pvar' (.there (.there (.there .here))) rfl).recE (T := ((((E9_qBody.rename FCdot.Rename.succ.lift).rename
    FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift)) .typ

/-- `Sngl-Trans` at `y`: `y : {B : N..N}`. -/
def E9_hyB : PathTy E9_Γ4 (.var (.there .here)) (.typ lB E9_N E9_N) :=
  .snglTrans (pvar' (.there .here) rfl) E9_hqB

/-- `z : y.B <: N`, by `Sel-<:` at `y`. -/
def E9_zN : HasTy E9_Γ4 (.path .here) E9_N := .sub (var' .here rfl) (.selUpper E9_hyB)

def E9_lamTy : Ty ((([],x),x),x) := .all (.sel (.var .here) lB) E9_N

/-- `λ(z : y.B). let w = z in w` at `∀(z : y.B) N`. -/
def E9_lamY : HasTy E9_Γ3 (.val (.lam (.sel (.var .here) lB) (.let (.path .here) (.path .here))))
    E9_lamTy :=
  .lam (.let E9_zN (var' .here rfl) (.fld .top)) .sel

/-- `let y = x.a in λ(z : y.B). …`, by the derived `letSngl`. -/
def E9_letY : HasTy E9_Γ2 (.let (.proj .here la)
    (.val (.lam (.sel (.var .here) lB) (.let (.path .here) (.path .here))))) .top :=
  HasTy.letSngl E9_hx (.sub E9_lamY .top) .top

def E9_term : Tm [] :=
  .let (.val (.obj E9_qDefs)) (.let (.val (.obj E9_xDefs)) (.let (.proj .here la)
    (.val (.lam (.sel (.var .here) lB) (.let (.path .here) (.path .here))))))

def E9 : HasTy Ctx.nil E9_term .top := .let E9_qLit (.let E9_xLit E9_letY .top) .top

/-! ## E10 and P2e

E10 is X2 and P2e is X1, read on the target side.  Neither gets a second
source page.  Their target facts are in `DotToFCdot/Pages.lean`. -/

/-! ## E11: a singleton field

`let z = ν(z. {C = ⊤}) in ν(x. {val a = ν(_. {A = ⊤})} ∧ {b = z})` at `⊤`, the
inner literal declared `{val a : μ(_. {A : ⊤..⊤})} ∧ {b : z.type}`.  `a` is
`val` by `trmObj`.  `b` is plain by the derived `trmSngl`, at `{b : z.type}`
and not at `{val b : z.type}` (decision 27).  A stable field and a forwarding
field in one literal. -/

/-- `z = ν(z. {C = ⊤})`, the outer literal the singleton field names. -/
def E11_zDefs : Defs ([],x) := .typ lC .top
def E11_zBody : Ty ([],x) := .typ lC .top .top
def E11_zDefsTy : DefsTy (Ctx.nil.consSelf E11_zDefs E11_zBody) E11_zDefs E11_zBody := .typ
def E11_zLit : HasTy Ctx.nil (.val (.obj E11_zDefs)) (.mu E11_zBody) := .obj E11_zDefsTy .typ

def E11_Γz : Ctx ([],x) := Ctx.nil.cons (.mu E11_zBody)

/-- `{a = ν(_. {A = ⊤})} ∧ {b = z}`. -/
def E11_xDefs : Defs (([],x),x) :=
  .and (.trm la (.val (.obj (.typ lA .top)))) (.trm lb (.path (.there .here)))
/-- `{val a : μ(_. {A : ⊤..⊤})} ∧ {b : z.type}`. -/
def E11_xBody : Ty (([],x),x) :=
  .and (.vfld la (.mu (.typ lA .top .top))) (.fld lb (.sngl (.var (.there .here))))

theorem E11_xDistinct : Defs.Distinct E11_xDefs := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def E11_xDefsTy : DefsTy (E11_Γz.consSelf E11_xDefs E11_xBody) E11_xDefs E11_xBody :=
  .and (.trmObj .typ .typ) (DefsTy.trmSngl .var)

def E11_xLit : HasTy E11_Γz (.val (.obj E11_xDefs)) (.mu E11_xBody) := .obj E11_xDefsTy E11_xDistinct

def E11_term : Tm [] := .let (.val (.obj E11_zDefs)) (.val (.obj E11_xDefs))

/-- The closed program, at `⊤`. -/
def E11 : HasTy Ctx.nil E11_term .top := .let E11_zLit (.sub E11_xLit .top) .top

/-! ## P3e: pDOT Sec. 2.3, bad bounds through a computation field

`ν(x. {a = x.a} ∧ {b = λ(y : ⊤). y})`, declared
`{a : {C : ∀(y : ⊤)⊤..{c : ⊤}}} ∧ {b : ∀(y : ⊤)⊤}`.  Both fields are plain.
`a` holds a projection and `b` a lambda.  pDOT declares `b : {c : ⊤}` and
types the lambda there through `x.a.C`.  Here the literal types at the honest
declaration by `DefsTy.trm` with `HasTy.proj` over `HasTy.recE` and
`Sub.and1`, and by `HasTy.lam`.  The elimination is refused.  `a` is plain, so
`Fld-E` has no premise at `x.a`.  `P3e_noVfld` proves that by the inversion of
`X2_noVfld`: the one stable rule, `trmObj`, asks for an object literal body,
and the bodies are a projection and a lambda. -/

/-- Term label `c`, the member of the upper bound `{c : ⊤}`. -/
def P3e_lc : Label := .trm 2

/-- `{C : ∀(y : ⊤) ⊤ .. {c : ⊤}}`, the bad bounds `x.a` would carry. -/
def P3e_Cbad : Ty s := .typ lC (.all .top .top) (.fld P3e_lc .top)
/-- `{a : {C : …}} ∧ {b : ∀(y : ⊤) ⊤}`: `a` is a computation member. -/
def P3e_TP : Ty ([],x) := .and (.fld la P3e_Cbad) (.fld lb (.all .top .top))
/-- `{a = x.a} ∧ {b = λ(y : ⊤). y}`. -/
def P3e_dP : Defs ([],x) := .and (.trm la (.proj .here la)) (.trm lb (.val (.lam .top (.path .here))))

theorem P3e_dP_distinct : Defs.Distinct P3e_dP := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def P3e_Γs : Ctx ([],x) := Ctx.nil.consSelf P3e_dP P3e_TP

def P3e_xa : HasTy P3e_Γs (.proj .here la) P3e_Cbad :=
  .proj (.sub (HasTy.recE (T := P3e_TP.rename FCdot.Rename.succ.lift) (var' .here rfl) (.and .fld .fld)) .and1)

def P3e_defsTy : DefsTy P3e_Γs P3e_dP P3e_TP := .and (.trm P3e_xa) (.trm (.lam (var' .here rfl) .top))

def P3e_lit : HasTy Ctx.nil (.val (.obj P3e_dP)) (.mu P3e_TP) := .obj P3e_defsTy P3e_dP_distinct

/-- Inversion of definition typing at these bodies: every type these
definitions can be given declares `a` and `b` as computation members.
`trmObj` asks for an object literal body, and the bodies are the projection
`x.a` and a lambda, so `trm` is the only rule that applies to either. -/
def P3e_defsShape {Γ : Ctx ([],x)} {U : Ty ([],x)} (h : DefsTy Γ P3e_dP U) :
    (T1 : Ty ([],x)) × (T2 : Ty ([],x)) × PLift (U = .and (.fld la T1) (.fld lb T2)) := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | trm _ =>
      cases h2 with
      | trm _ => exact ⟨_, _, .up rfl⟩

/-- No `DefsTy` of these definitions declares `{val a : _}`, so `Fld-E` has no
premise to read at `x.a`. -/
theorem P3e_noVfld {Γ : Ctx ([],x)} {U : Ty ([],x)} (h : DefsTy Γ P3e_dP U) :
    U.lookupVfldDecl la = none := by
  obtain ⟨T1, T2, hU⟩ := P3e_defsShape h
  rw [hU.down, Ty.lookupVfldDecl, Ty.lookupVfldDecl, Ty.lookupVfldDecl]
  rfl

/-! ## Fig2: acceptance test A, gDOT Fig. 2 with the `Option` encoding

```text
let options = ν(o. {Option = ⊤}) in
let pcore = ν(p. {val types   = ν(t. {Type = ⊤} ∧ {TypeTop = t.Type}
                                     ∧ {newTypeTop = λ(u : ⊤). u}
                                     ∧ {TypeRef = t.Type ∧ {symb : p.symbols.Symbol}}
                                     ∧ {newTypeRef = λ(s : p.symbols.Symbol).
                                                       let r = ν(_. {symb = s}) in r})}
                ∧ {val symbols = ν(y. {Symbol = {tpe : o.Option ∧ {A : ⊥..p.types.Type}}
                                                 ∧ {id : Nat}}
                                     ∧ {newSymbol = λ(u : o.Option ∧ {A : ⊥..p.types.Type}).
                                                      λ(i : Nat).
                                                        let r = ν(_. {tpe = u} ∧ {id = i}) in r})}) in
pcore
```

`types` and `symbols` are `val`, by `DefsTy.trmObj`.  `newTypeTop`,
`newTypeRef` and `newSymbol` hold lambdas, and `symb`, `tpe` and `id` hold
variables, so all six are plain (decision 27).  The `types` literal is X4,
reused unchanged.  The two modules refer to each other through the outer self
`p`: `p.symbols.Symbol` inside `types`, and `p.types.Type` inside `symbols`.

Four changes against Fig. 2 (decision 37).  `Nat` is the closed stand-in
`{n : ⊤}`.  `options` is the closed literal `ν(o. {Option = ⊤})`, which Fig. 2
elides.  `newTypeTop` returns its argument, as in X4, since `Defs` has no empty
list for `ν_. {}`.  The two constructors let-bind their literal, since `Rec-E`
is the only rule that opens a `μ`.  Left out: Fig. 1's unchecked cast from a
`TypeRef` to a `Type` with its assertion, which Fig. 2 drops as well, and
Fig. 12.

What it exercises that no earlier example does.  Two stable nested literals
whose declared types refer to each other through the outer self, the
elimination through a stable field of the outer self from inside a sibling
(`Fig2_crossUpperT`), and the abstract view of a nested literal after
allocation.  The view is taken at the selection per module
(`Fig2_pcTypesAbs`, `Fig2_pcSymbolsAbs`) and at the let-bound `pcore` for both
(`Fig2_pcAbs`), never at the value (decision 36).  The target facts are in
`DotToFCdot/Acceptance.lean`. -/

/-! ### The `options` module -/

def Fig2_oDefs : Defs ([],x) := .typ Fig2_lOption .top
def Fig2_oBody : Ty ([],x) := .typ Fig2_lOption .top .top
def Fig2_oLit : HasTy Ctx.nil (.val (.obj Fig2_oDefs)) (.mu Fig2_oBody) := .obj .typ .typ

/-! ### The `symbols` module -/

/-- `Nat`, the closed stand-in `{n : ⊤}`. -/
def Fig2_NatT : Ty s := .fld Fig2_ln .top
/-- `o.Option ∧ {A : ⊥..p.types.Type}`, Fig. 2's encoding of `Option[p.types.Type]`. -/
def Fig2_OptT (o p : BVar s .var) : Ty s :=
  .and (.sel (.var o) Fig2_lOption) (.typ lA .bot (.sel (.sel (.var p) Fig2_ltypes) X4_lType))
/-- `{tpe : Option[p.types.Type]} ∧ {id : Nat}`, both members plain. -/
def Fig2_SymT (o p : BVar s .var) : Ty s :=
  .and (.fld Fig2_ltpe (Fig2_OptT o p)) (.fld Fig2_lid Fig2_NatT)

/-- The declared type of `symbols`, self `y`. -/
def Fig2_YBody (y p o : BVar s .var) : Ty s :=
  .and (.typ X4_lSymbol (Fig2_SymT o p) (Fig2_SymT o p))
    (.fld Fig2_lnewSymbol
      (.all (Fig2_OptT o p) (.all Fig2_NatT (.sel (.var (.there (.there y))) X4_lSymbol))))

theorem Fig2_YBodyDecl (y p o : BVar s .var) : Ty.Decl (Fig2_YBody y p o) := .and .typ .fld

/-- The inner literal `{tpe = u} ∧ {id = i}`, under `u`, `i` and its own self. -/
def Fig2_SymLitDefs : Defs (s,x,x,x) :=
  .and (.trm Fig2_ltpe (.path (.there (.there .here)))) (.trm Fig2_lid (.path (.there .here)))

theorem Fig2_SymLitDistinct : Defs.Distinct (Fig2_SymLitDefs (s := s)) := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

/-- The definitions of `symbols`. -/
def Fig2_YDefs (p o : BVar s .var) : Defs s :=
  .and (.typ X4_lSymbol (Fig2_SymT o p))
    (.trm Fig2_lnewSymbol (.val (.lam (Fig2_OptT o p) (.val (.lam Fig2_NatT
      (.let (.val (.obj Fig2_SymLitDefs)) (.path .here)))))))

theorem Fig2_YDistinct (p o : BVar s .var) : Defs.Distinct (Fig2_YDefs p o) := by
  refine .and .typ .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def Fig2_Y_CtxSelf {Γ : Ctx s} (p o : BVar s .var) : Ctx (s,x) :=
  Γ.consSelf (Fig2_YDefs (.there p) (.there o)) (Fig2_YBody .here (.there p) (.there o))

theorem Fig2_OptTWf (o p : BVar s .var) : Ty.Wf (Fig2_OptT o p) := .and .sel (.typ .bot .sel)

/-- `newSymbol = λ(u). λ(i). let r = ν(_. {tpe = u} ∧ {id = i}) in r`, at
`∀(u : Option[…]) ∀(i : Nat) y.Symbol`.  The literal is bound, opened by `Rec-E`
at `r`, and let out at `y.Symbol` by `<:-Sel` off `y`'s exact member. -/
def Fig2_Y_newSymbol {Γ : Ctx s} (p o : BVar s .var) :
    HasTy (Fig2_Y_CtxSelf (Γ := Γ) p o)
      (.val (.lam (Fig2_OptT (.there o) (.there p)) (.val (.lam Fig2_NatT
        (.let (.val (.obj Fig2_SymLitDefs)) (.path .here))))))
      (.all (Fig2_OptT (.there o) (.there p))
        (.all Fig2_NatT (.sel (.var (.there (.there .here))) X4_lSymbol))) := by
  refine .lam ?_ (Fig2_OptTWf _ _)
  refine .lam ?_ (.fld .top)
  have hObj : HasTy
      (((Fig2_Y_CtxSelf (Γ := Γ) p o).cons (Fig2_OptT (.there o) (.there p))).cons Fig2_NatT)
      (.val (.obj Fig2_SymLitDefs))
      (.mu (Fig2_SymT (.there (.there (.there (.there o)))) (.there (.there (.there (.there p)))))) :=
    .obj (.and (.trm (var' (.there (.there .here)) rfl)) (.trm (var' (.there .here) rfl)))
      Fig2_SymLitDistinct
  refine .let hObj ?_ .sel
  have hy : PathTy
      ((((Fig2_Y_CtxSelf (Γ := Γ) p o).cons (Fig2_OptT (.there o) (.there p))).cons Fig2_NatT).cons
        (.mu (Fig2_SymT (.there (.there (.there (.there o)))) (.there (.there (.there (.there p)))))))
      (.var (.there (.there (.there .here))))
      (Fig2_YBody (.there (.there (.there .here))) (.there (.there (.there (.there p))))
        (.there (.there (.there (.there o))))) :=
    (pvar' (.there (.there (.there .here))) rfl).recE
      (T := (((((Fig2_YBody .here (.there p) (.there o)).rename FCdot.Rename.succ.lift).rename
        FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift))
      (Fig2_YBodyDecl _ _ _)
  exact .sub (HasTy.recE (var' .here rfl) (.and .fld .fld)) (.selLower (hy.sub .and1))

def Fig2_YDefsTy {Γ : Ctx s} (p o : BVar s .var) :
    DefsTy (Fig2_Y_CtxSelf (Γ := Γ) p o) (Fig2_YDefs (.there p) (.there o))
      (Fig2_YBody .here (.there p) (.there o)) :=
  .and .typ (.trm (Fig2_Y_newSymbol p o))

/-! ### The `pcore` module, under `o` -/

/-- `{types = ν(t. …)} ∧ {symbols = ν(y. …)}`, self `p` at `.here`, `o` at `.there .here`. -/
def Fig2_pDefs : Defs (([],x),x) :=
  .and (.trm Fig2_ltypes (.val (.obj (X4_Defs .here (.there .here)))))
    (.trm X4_lsymbols (.val (.obj (Fig2_YDefs (.there .here) (.there (.there .here))))))

/-- `{val types : μ(t. …)} ∧ {val symbols : μ(y. …)}`, both stable. -/
def Fig2_pBody : Ty (([],x),x) :=
  .and (.vfld Fig2_ltypes (.mu (X4_Body .here (.there .here))))
    (.vfld X4_lsymbols (.mu (Fig2_YBody .here (.there .here) (.there (.there .here)))))

theorem Fig2_pDistinct : Defs.Distinct Fig2_pDefs := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def Fig2_Γo : Ctx ([],x) := Ctx.nil.cons (.mu Fig2_oBody)
def Fig2_Γp : Ctx (([],x),x) := Fig2_Γo.consSelf Fig2_pDefs Fig2_pBody

def Fig2_pDefsTy : DefsTy Fig2_Γp Fig2_pDefs Fig2_pBody :=
  .and (.trmObj (X4_DefsTy (Γ := Fig2_Γp) .here) (X4_Distinct _ _))
    (.trmObj (Fig2_YDefsTy (Γ := Fig2_Γp) .here (.there .here)) (Fig2_YDistinct _ _))

def Fig2_pLit : HasTy Fig2_Γo (.val (.obj Fig2_pDefs)) (.mu Fig2_pBody) :=
  .obj Fig2_pDefsTy Fig2_pDistinct

/-! ### Step 5: the cross-field reference, eliminated inside `types`

Inside `types`, with the self `p` at its declared type, `p.symbols.Symbol` has
the bounds `Symbol` declares.  `Var`, `Rec-E`, `And₂`, `Fld-E` at the stable
field `symbols`, `Rec-E` at the path `p.symbols`, `And₁`, `Sel-<:`. -/

def Fig2_Γt : Ctx ((([],x),x),x) := X4_CtxSelf (Γ := Fig2_Γp) .here

def Fig2_pOpenT : PathTy Fig2_Γt (.var (.there .here))
    (.and (.vfld Fig2_ltypes (.mu (X4_Body .here (.there (.there .here)))))
      (.vfld X4_lsymbols
        (.mu (Fig2_YBody .here (.there (.there .here)) (.there (.there (.there .here))))))) :=
  (pvar' (.there .here) rfl).recE
    (T := (Fig2_pBody.rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift) (.and .vfld .vfld)

/-- `Fld-E` at the stable field: the path `p.symbols`. -/
def Fig2_pSymbolsT : PathTy Fig2_Γt (.sel (.var (.there .here)) X4_lsymbols)
    (.mu (Fig2_YBody .here (.there (.there .here)) (.there (.there (.there .here))))) :=
  (Fig2_pOpenT.sub .and2).sel

/-- `Rec-E` at `p.symbols`, then `And₁`: `{Symbol : SymT..SymT}`. -/
def Fig2_pSymbolT : PathTy Fig2_Γt (.sel (.var (.there .here)) X4_lsymbols)
    (.typ X4_lSymbol (Fig2_SymT (.there (.there .here)) (.there .here))
      (Fig2_SymT (.there (.there .here)) (.there .here))) :=
  (Fig2_pSymbolsT.recE (Fig2_YBodyDecl _ _ _)).sub .and1

/-- `p.symbols.Symbol <: {tpe : o.Option ∧ {A : ⊥..p.types.Type}} ∧ {id : Nat}`. -/
def Fig2_crossUpperT :
    Sub Fig2_Γt (X4_Sym (.there .here)) (Fig2_SymT (.there (.there .here)) (.there .here)) :=
  .selUpper Fig2_pSymbolT

/-! ### Step 7: the abstract view, at the let-bound `pcore` and at the selection -/

/-- dot-iris's `fromPDotPaperAbsTypesTBody`. -/
def Fig2_TAbs (t p : BVar s .var) : Ty s :=
  .and (.and (.and (.and
    (.typ X4_lType .bot .top)
    (.typ X4_lTypeTop .bot (X4_TypeSel t)))
    (.fld X4_lnewTypeTop (.all .top (X4_TopSel (.there t)))))
    (.typ X4_lTypeRef .bot (X4_RefBody t p)))
    (.fld X4_lnewTypeRef (.all (X4_Sym p) (X4_RefSel (.there t))))

/-- dot-iris's `fromPDotPaperAbsSymbolsTBody`. -/
def Fig2_YAbs (y p o : BVar s .var) : Ty s :=
  .and (.typ X4_lSymbol .bot (Fig2_SymT o p))
    (.fld Fig2_lnewSymbol
      (.all (Fig2_OptT o p) (.all Fig2_NatT (.sel (.var (.there (.there y))) X4_lSymbol))))

theorem Fig2_TAbsDecl (t p : BVar s .var) : Ty.Decl (Fig2_TAbs t p) :=
  .and (.and (.and (.and .typ .typ) .fld) .typ) .fld
theorem Fig2_YAbsDecl (y p o : BVar s .var) : Ty.Decl (Fig2_YAbs y p o) := .and .typ .fld

/-- `Typ-Abs` on `types`: every lower bound to `⊥`, every upper bound kept. -/
def Fig2_sdTypes {Γ : Ctx s} {p : BVar s .var} :
    SubDecl Γ (X4_Body .here (.there p)) (Fig2_TAbs .here (.there p)) :=
  .and (.and (.and (.and (.typ rfl .bot .refl) (.typ rfl .bot .refl)) (.fld rfl .refl))
    (.typ rfl .bot .refl)) (.fld rfl .refl)

/-- `Typ-Abs` on `symbols`. -/
def Fig2_sdSymbols {Γ : Ctx s} {p o : BVar s .var} :
    SubDecl Γ (Fig2_YBody .here (.there p) (.there o)) (Fig2_YAbs .here (.there p) (.there o)) :=
  .and (.typ rfl .bot .refl) (.fld rfl .refl)

/-- The context of the client: `o`, then `pcore` bound opaquely at `μ pBody`. -/
def Fig2_Γc : Ctx (([],x),x) := Fig2_Γo.cons (.mu Fig2_pBody)

/-- The abstract body of `pcore`, dot-iris's `fromPDotPaperAbsTBody`. -/
def Fig2_pAbs : Ty ((([],x),x),x) :=
  .and (.vfld Fig2_ltypes (.mu (Fig2_TAbs .here (.there .here))))
    (.vfld X4_lsymbols (.mu (Fig2_YAbs .here (.there .here) (.there (.there (.there .here))))))

/-- `Rec-E` at `pcore`, a term rule. -/
def Fig2_pcOpen : HasTy Fig2_Γc (.path .here) Fig2_pBody :=
  HasTy.recE (T := Fig2_pBody.rename FCdot.Rename.succ.lift) (var' .here rfl) (.and .vfld .vfld)

/-- The abstract view of each module, by `Sub.mu` under `Sub.vfld`. -/
def Fig2_pcAbsSub : Sub Fig2_Γc Fig2_pBody (Fig2_pAbs.substVar .here) :=
  .and (.trans .and1 (.vfld (.mu Fig2_sdTypes (X4_BodyDecl _ _) (Fig2_TAbsDecl _ _))))
    (.trans .and2 (.vfld (.mu Fig2_sdSymbols (Fig2_YBodyDecl _ _ _) (Fig2_YAbsDecl _ _ _))))

/-- `pcore : μ(p. {val types : μ AbsTypes} ∧ {val symbols : μ AbsSymbols})`, by `Rec-I`. -/
def Fig2_pcAbs : HasTy Fig2_Γc (.path .here) (.mu Fig2_pAbs) :=
  .recI (Fig2_pcOpen.sub Fig2_pcAbsSub) (.and .vfld .vfld)

/-- `pcore.symbols : μ(y. exact)`, by `Var`, `Rec-E`, `And₂`, `Fld-E`. -/
def Fig2_pcSymbols : PathTy Fig2_Γc (.sel (.var .here) X4_lsymbols)
    (.mu (Fig2_YBody .here (.there .here) (.there (.there .here)))) :=
  ((pvar' .here rfl : PathTy Fig2_Γc _ (Ty.mu Fig2_pBody).weaken).recE
    (T := Fig2_pBody.rename FCdot.Rename.succ.lift) (.and .vfld .vfld) |>.sub .and2).sel

/-- The same bound as step 5, at `pcore.symbols.Symbol` in the client. -/
def Fig2_crossUpperC : Sub Fig2_Γc (X4_Sym .here) (Fig2_SymT (.there .here) .here) :=
  .selUpper ((Fig2_pcSymbols.recE (Fig2_YBodyDecl _ _ _)).sub .and1)

/-- `pcore.types : μ(t. exact)`, by `Var`, `Rec-E`, `And₁`, `Fld-E`. -/
def Fig2_pcTypes : PathTy Fig2_Γc (.sel (.var .here) Fig2_ltypes)
    (.mu (X4_Body .here (.there .here))) :=
  ((pvar' .here rfl : PathTy Fig2_Γc _ (Ty.mu Fig2_pBody).weaken).recE
    (T := Fig2_pBody.rename FCdot.Rename.succ.lift) (.and .vfld .vfld) |>.sub .and1).sel

/-- The abstract view at the selection, `PathTy.sub` with `Sub.mu`. -/
def Fig2_pcTypesAbs : PathTy Fig2_Γc (.sel (.var .here) Fig2_ltypes)
    (.mu (Fig2_TAbs .here (.there .here))) :=
  Fig2_pcTypes.sub (.mu Fig2_sdTypes (X4_BodyDecl _ _) (Fig2_TAbsDecl _ _))

/-- The same for `symbols`. -/
def Fig2_pcSymbolsAbs : PathTy Fig2_Γc (.sel (.var .here) X4_lsymbols)
    (.mu (Fig2_YAbs .here (.there .here) (.there (.there .here)))) :=
  Fig2_pcSymbols.sub (.mu Fig2_sdSymbols (Fig2_YBodyDecl _ _ _) (Fig2_YAbsDecl _ _ _))

/-! ### The program -/

/-- The program of Fig. 2, with the four changes. -/
def Fig2_prog : Tm [] :=
  .let (.val (.obj Fig2_oDefs)) (.let (.val (.obj Fig2_pDefs)) (.path .here))

/-- **Acceptance test A, source.**  The program types at `⊤` in the empty context. -/
def Fig2_prog_ty : HasTy Ctx.nil Fig2_prog .top :=
  .let Fig2_oLit (.let Fig2_pLit (.sub Fig2_pcAbs .top) .top) .top

/-! ## Fig1: pDOT Fig. 1, the Dotty modules (P1e)

Fig2 with `Symbol = {tpe : p.types.Type} ∧ {id : Nat}`, the Scala of Fig. 1
without the `Option`.  The derivation is Fig2's with the `tpe` type replaced.
Its point, that `pcore.symbols.Symbol` is a path of length two, is Fig2's
step 5.  This page is a second copy of Fig2's `symbols` module, `pcore` and
program (decision 41).  It shares Fig2's labels, the `options` module,
`Fig2_NatT`, the inner literal `Fig2_SymLitDefs`, and the view of `types`
(`Fig2_TAbs`, `Fig2_sdTypes`), none of which mention the `tpe` type.  `o` is
then unused in `Fig1_OptT`, so two steps give it as `.here` by hand. -/

/-- `p.types.Type`, the `tpe` type of Fig. 1.  The module `o` is unused. -/
def Fig1_OptT (_o p : BVar s .var) : Ty s :=
  .sel (.sel (.var p) Fig2_ltypes) X4_lType
/-- `{tpe : p.types.Type} ∧ {id : Nat}`, both members plain. -/
def Fig1_SymT (o p : BVar s .var) : Ty s :=
  .and (.fld Fig2_ltpe (Fig1_OptT o p)) (.fld Fig2_lid Fig2_NatT)

/-- The declared type of `symbols`, self `y`. -/
def Fig1_YBody (y p o : BVar s .var) : Ty s :=
  .and (.typ X4_lSymbol (Fig1_SymT o p) (Fig1_SymT o p))
    (.fld Fig2_lnewSymbol
      (.all (Fig1_OptT o p) (.all Fig2_NatT (.sel (.var (.there (.there y))) X4_lSymbol))))

theorem Fig1_YBodyDecl (y p o : BVar s .var) : Ty.Decl (Fig1_YBody y p o) := .and .typ .fld

/-- The definitions of `symbols`. -/
def Fig1_YDefs (p o : BVar s .var) : Defs s :=
  .and (.typ X4_lSymbol (Fig1_SymT o p))
    (.trm Fig2_lnewSymbol (.val (.lam (Fig1_OptT o p) (.val (.lam Fig2_NatT
      (.let (.val (.obj Fig2_SymLitDefs)) (.path .here)))))))

theorem Fig1_YDistinct (p o : BVar s .var) : Defs.Distinct (Fig1_YDefs p o) := by
  refine .and .typ .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def Fig1_Y_CtxSelf {Γ : Ctx s} (p o : BVar s .var) : Ctx (s,x) :=
  Γ.consSelf (Fig1_YDefs (.there p) (.there o)) (Fig1_YBody .here (.there p) (.there o))

theorem Fig1_OptTWf (o p : BVar s .var) : Ty.Wf (Fig1_OptT o p) := .sel

/-- `newSymbol = λ(u). λ(i). let r = ν(_. {tpe = u} ∧ {id = i}) in r`, at
`∀(u : p.types.Type) ∀(i : Nat) y.Symbol`. -/
def Fig1_Y_newSymbol {Γ : Ctx s} (p o : BVar s .var) :
    HasTy (Fig1_Y_CtxSelf (Γ := Γ) p o)
      (.val (.lam (Fig1_OptT (.there o) (.there p)) (.val (.lam Fig2_NatT
        (.let (.val (.obj Fig2_SymLitDefs)) (.path .here))))))
      (.all (Fig1_OptT (.there o) (.there p))
        (.all Fig2_NatT (.sel (.var (.there (.there .here))) X4_lSymbol))) := by
  refine .lam ?_ (Fig1_OptTWf _ _)
  refine .lam ?_ (.fld .top)
  have hObj : HasTy
      (((Fig1_Y_CtxSelf (Γ := Γ) p o).cons (Fig1_OptT (.there o) (.there p))).cons Fig2_NatT)
      (.val (.obj Fig2_SymLitDefs))
      (.mu (Fig1_SymT (.there (.there (.there (.there o)))) (.there (.there (.there (.there p)))))) :=
    .obj (.and (.trm (var' (.there (.there .here)) rfl)) (.trm (var' (.there .here) rfl)))
      Fig2_SymLitDistinct
  refine .let hObj ?_ .sel
  have hy : PathTy
      ((((Fig1_Y_CtxSelf (Γ := Γ) p o).cons (Fig1_OptT (.there o) (.there p))).cons Fig2_NatT).cons
        (.mu (Fig1_SymT (.there (.there (.there (.there o)))) (.there (.there (.there (.there p)))))))
      (.var (.there (.there (.there .here))))
      (Fig1_YBody (.there (.there (.there .here))) (.there (.there (.there (.there p))))
        (.there (.there (.there (.there o))))) :=
    (pvar' (.there (.there (.there .here))) rfl).recE
      (T := (((((Fig1_YBody .here (.there p) (.there o)).rename FCdot.Rename.succ.lift).rename
        FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift))
      (Fig1_YBodyDecl _ _ .here)
  exact .sub (HasTy.recE (var' .here rfl) (.and .fld .fld)) (.selLower (hy.sub .and1))

def Fig1_YDefsTy {Γ : Ctx s} (p o : BVar s .var) :
    DefsTy (Fig1_Y_CtxSelf (Γ := Γ) p o) (Fig1_YDefs (.there p) (.there o))
      (Fig1_YBody .here (.there p) (.there o)) :=
  .and .typ (.trm (Fig1_Y_newSymbol p o))

/-- `{types = ν(t. …)} ∧ {symbols = ν(y. …)}`, self `p` at `.here`, `o` at `.there .here`. -/
def Fig1_pDefs : Defs (([],x),x) :=
  .and (.trm Fig2_ltypes (.val (.obj (X4_Defs .here (.there .here)))))
    (.trm X4_lsymbols (.val (.obj (Fig1_YDefs (.there .here) (.there (.there .here))))))

/-- `{val types : μ(t. …)} ∧ {val symbols : μ(y. …)}`, both stable. -/
def Fig1_pBody : Ty (([],x),x) :=
  .and (.vfld Fig2_ltypes (.mu (X4_Body .here (.there .here))))
    (.vfld X4_lsymbols (.mu (Fig1_YBody .here (.there .here) (.there (.there .here)))))

theorem Fig1_pDistinct : Defs.Distinct Fig1_pDefs := by
  refine .and .trm .trm ?_
  intro ℓ h; simp only [Defs.labels, List.mem_singleton] at h ⊢; subst h; decide

def Fig1_Γp : Ctx (([],x),x) := Fig2_Γo.consSelf Fig1_pDefs Fig1_pBody

def Fig1_pDefsTy : DefsTy Fig1_Γp Fig1_pDefs Fig1_pBody :=
  .and (.trmObj (X4_DefsTy (Γ := Fig1_Γp) .here) (X4_Distinct _ _))
    (.trmObj (Fig1_YDefsTy (Γ := Fig1_Γp) .here (.there .here)) (Fig1_YDistinct _ _))

def Fig1_pLit : HasTy Fig2_Γo (.val (.obj Fig1_pDefs)) (.mu Fig1_pBody) :=
  .obj Fig1_pDefsTy Fig1_pDistinct

def Fig1_Γt : Ctx ((([],x),x),x) := X4_CtxSelf (Γ := Fig1_Γp) .here

def Fig1_pOpenT : PathTy Fig1_Γt (.var (.there .here))
    (.and (.vfld Fig2_ltypes (.mu (X4_Body .here (.there (.there .here)))))
      (.vfld X4_lsymbols
        (.mu (Fig1_YBody .here (.there (.there .here)) (.there (.there (.there .here))))))) :=
  (pvar' (.there .here) rfl).recE
    (T := (Fig1_pBody.rename FCdot.Rename.succ.lift).rename FCdot.Rename.succ.lift) (.and .vfld .vfld)

/-- `Fld-E` at the stable field: the path `p.symbols`. -/
def Fig1_pSymbolsT : PathTy Fig1_Γt (.sel (.var (.there .here)) X4_lsymbols)
    (.mu (Fig1_YBody .here (.there (.there .here)) (.there (.there (.there .here))))) :=
  (Fig1_pOpenT.sub .and2).sel

/-- `Rec-E` at `p.symbols`, then `And₁`: `{Symbol : SymT..SymT}`. -/
def Fig1_pSymbolT : PathTy Fig1_Γt (.sel (.var (.there .here)) X4_lsymbols)
    (.typ X4_lSymbol (Fig1_SymT (.there (.there .here)) (.there .here))
      (Fig1_SymT (.there (.there .here)) (.there .here))) :=
  (Fig1_pSymbolsT.recE (Fig1_YBodyDecl _ _ _)).sub .and1

/-- `p.symbols.Symbol <: {tpe : p.types.Type} ∧ {id : Nat}`, inside `types`. -/
def Fig1_crossUpperT :
    Sub Fig1_Γt (X4_Sym (.there .here)) (Fig1_SymT (.there (.there .here)) (.there .here)) :=
  .selUpper Fig1_pSymbolT

/-- dot-iris's `fromPDotPaperAbsSymbolsTBody`, with Fig. 1's `tpe`. -/
def Fig1_YAbs (y p o : BVar s .var) : Ty s :=
  .and (.typ X4_lSymbol .bot (Fig1_SymT o p))
    (.fld Fig2_lnewSymbol
      (.all (Fig1_OptT o p) (.all Fig2_NatT (.sel (.var (.there (.there y))) X4_lSymbol))))

theorem Fig1_YAbsDecl (y p o : BVar s .var) : Ty.Decl (Fig1_YAbs y p o) := .and .typ .fld

/-- `Typ-Abs` on `symbols`. -/
def Fig1_sdSymbols {Γ : Ctx s} {p o : BVar s .var} :
    SubDecl Γ (Fig1_YBody .here (.there p) (.there o)) (Fig1_YAbs .here (.there p) (.there o)) :=
  .and (.typ rfl .bot .refl) (.fld rfl .refl)

/-- The context of the client: `o`, then `pcore` bound opaquely at `μ pBody`. -/
def Fig1_Γc : Ctx (([],x),x) := Fig2_Γo.cons (.mu Fig1_pBody)

/-- The abstract body of `pcore`. -/
def Fig1_pAbs : Ty ((([],x),x),x) :=
  .and (.vfld Fig2_ltypes (.mu (Fig2_TAbs .here (.there .here))))
    (.vfld X4_lsymbols (.mu (Fig1_YAbs .here (.there .here) (.there (.there (.there .here))))))

/-- `Rec-E` at `pcore`, a term rule. -/
def Fig1_pcOpen : HasTy Fig1_Γc (.path .here) Fig1_pBody :=
  HasTy.recE (T := Fig1_pBody.rename FCdot.Rename.succ.lift) (var' .here rfl) (.and .vfld .vfld)

/-- The abstract view of each module, by `Sub.mu` under `Sub.vfld`. -/
def Fig1_pcAbsSub : Sub Fig1_Γc Fig1_pBody (Fig1_pAbs.substVar .here) :=
  .and (.trans .and1 (.vfld (.mu Fig2_sdTypes (X4_BodyDecl _ _) (Fig2_TAbsDecl _ _))))
    (.trans .and2
      (.vfld (.mu (Fig1_sdSymbols (o := .here)) (Fig1_YBodyDecl _ _ .here) (Fig1_YAbsDecl _ _ .here))))

/-- `pcore : μ(p. {val types : μ AbsTypes} ∧ {val symbols : μ AbsSymbols})`, by `Rec-I`. -/
def Fig1_pcAbs : HasTy Fig1_Γc (.path .here) (.mu Fig1_pAbs) :=
  .recI (Fig1_pcOpen.sub Fig1_pcAbsSub) (.and .vfld .vfld)

/-- `pcore.symbols : μ(y. exact)`, by `Var`, `Rec-E`, `And₂`, `Fld-E`. -/
def Fig1_pcSymbols : PathTy Fig1_Γc (.sel (.var .here) X4_lsymbols)
    (.mu (Fig1_YBody .here (.there .here) (.there (.there .here)))) :=
  ((pvar' .here rfl : PathTy Fig1_Γc _ (Ty.mu Fig1_pBody).weaken).recE
    (T := Fig1_pBody.rename FCdot.Rename.succ.lift) (.and .vfld .vfld) |>.sub .and2).sel

/-- The same bound, at `pcore.symbols.Symbol` in the client. -/
def Fig1_crossUpperC : Sub Fig1_Γc (X4_Sym .here) (Fig1_SymT (.there .here) .here) :=
  .selUpper ((Fig1_pcSymbols.recE (Fig1_YBodyDecl _ _ _)).sub .and1)

/-- `pcore.types : μ(t. exact)`, by `Var`, `Rec-E`, `And₁`, `Fld-E`. -/
def Fig1_pcTypes : PathTy Fig1_Γc (.sel (.var .here) Fig2_ltypes)
    (.mu (X4_Body .here (.there .here))) :=
  ((pvar' .here rfl : PathTy Fig1_Γc _ (Ty.mu Fig1_pBody).weaken).recE
    (T := Fig1_pBody.rename FCdot.Rename.succ.lift) (.and .vfld .vfld) |>.sub .and1).sel

/-- The abstract view at the selection, `PathTy.sub` with `Sub.mu`. -/
def Fig1_pcTypesAbs : PathTy Fig1_Γc (.sel (.var .here) Fig2_ltypes)
    (.mu (Fig2_TAbs .here (.there .here))) :=
  Fig1_pcTypes.sub (.mu Fig2_sdTypes (X4_BodyDecl _ _) (Fig2_TAbsDecl _ _))

/-- The same for `symbols`. -/
def Fig1_pcSymbolsAbs : PathTy Fig1_Γc (.sel (.var .here) X4_lsymbols)
    (.mu (Fig1_YAbs .here (.there .here) (.there (.there .here)))) :=
  Fig1_pcSymbols.sub (.mu (Fig1_sdSymbols (o := .here)) (Fig1_YBodyDecl _ _ .here)
    (Fig1_YAbsDecl _ _ .here))

/-- The program of Fig. 1, with Fig2's changes. -/
def Fig1_prog : Tm [] :=
  .let (.val (.obj Fig2_oDefs)) (.let (.val (.obj Fig1_pDefs)) (.path .here))

/-- P1e, source.  The program types at `⊤` in the empty context. -/
def Fig1_prog_ty : HasTy Ctx.nil Fig1_prog .top :=
  .let Fig2_oLit (.let Fig1_pLit (.sub Fig1_pcAbs .top) .top) .top

end Examples
end DotMNF

end Paths
