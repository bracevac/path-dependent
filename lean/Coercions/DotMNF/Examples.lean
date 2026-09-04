import Coercions.DotMNF.Typing

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
    HasTy Γ (.path (.var x)) T := by
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

/-! ## E1: bad bounds under a lambda

`λ(x : {A : ⊤..⊥}). let y = x in y`, where the `let` retypes `x` at the
unrelated type `{B : {a : ⊤}..{a : ⊤}}` through `⊤ <: x.A <: ⊥`. -/

/-- `{A : ⊤..⊥}`: bad bounds. -/
def E1Dom : Ty s := .typ lA .top .bot
/-- `{B : {a : ⊤}..{a : ⊤}}`, unrelated to `E1Dom`. -/
def E1Res : Ty s := .typ lB (.fld la .top) (.fld la .top)

/-- Under `x : {A : ⊤..⊥}` every type is above every other. -/
def badBounds {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    (hx : HasTy Γ (.path (.var x)) (.typ lA .top .bot)) (T : Ty s) :
    Sub Γ E1Dom T :=
  .trans .top (.trans (.selLower hx) (.trans (.selUpper hx) .bot))

def E1Ctx : Ctx ([],x) := .cons .nil E1Dom

def E1x : HasTy E1Ctx (.path (.var .here)) E1Dom := var' .here rfl

def E1retype : HasTy E1Ctx (.path (.var .here)) E1Res := .sub E1x (badBounds E1x E1Res)

def E1body : HasTy E1Ctx (.let (.path (.var .here)) (.path (.var .here))) E1Res :=
  .let E1retype (var' .here rfl) (.typ (.fld .top) (.fld .top))

def E1 : HasTy Ctx.nil
    (.val (.lam E1Dom (.let (.path (.var .here)) (.path (.var .here)))))
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
  .and (.typ lA E2A) (.trm la (.val (.lam (.sel (.var .here) lA) (.path (.var .here)))))

theorem E2Distinct : Defs.Distinct (E2Defs (s := s)) := by
  refine .and .typ .trm ?_
  intro ℓ h
  simp only [Defs.labels, List.mem_singleton] at h ⊢
  subst h
  decide

theorem E2Guarded : Defs.Guarded (E2Defs (s := s)) := .and (.typ rfl) .trm

/-- The self type is declaration-shaped. -/
theorem E2SelfDecl : Ty.Decl (E2Self (s := s)) := .and .typ .fld

def E2DefsTy : DefsTy (Ctx.consSelf Γ E2Defs E2Self) E2Defs E2Self :=
  .and .typ (.trm (.lam (var' .here rfl) .sel))

def E2Ctx1 : Ctx ([],x) := .cons .nil (.mu E2Self)

def E2xMu : HasTy E2Ctx1 (.path (.var .here)) (.mu E2Self) := var' .here rfl
def E2xOpen : HasTy E2Ctx1 (.path (.var .here)) E2Self := .recE E2xMu E2SelfDecl
def E2xFld : HasTy E2Ctx1 (.path (.var .here)) (.fld la E2A) := .sub E2xOpen (.and2 .typ .fld)
def E2proj : HasTy E2Ctx1 (.proj .here la) E2A := .proj E2xFld

def E2Ctx2 : Ctx ([],x,x) := .cons E2Ctx1 E2A

def E2f : HasTy E2Ctx2 (.path (.var .here)) E2A' := var' .here rfl
def E2xMu2 : HasTy E2Ctx2 (.path (.var (.there .here))) (.mu E2Self) := var' (.there .here) rfl
def E2xOpen2 : HasTy E2Ctx2 (.path (.var (.there .here)))
    (.and (.typ lA E2A' E2A') (.fld la E2A')) := .recE E2xMu2 E2SelfDecl
/-- `∀(y : x.A) x.A <: x.A`, by the lower bound of the exact member `A`. -/
def E2fArg : HasTy E2Ctx2 (.path (.var .here)) (.sel (.var (.there .here)) lA) :=
  .sub E2f (.selLower (.sub E2xOpen2 (.and1 .typ .fld)))
def E2app : HasTy E2Ctx2 (.app .here .here) (.sel (.var (.there .here)) lA) :=
  .app E2f E2fArg

/-- `let x = ν(…) in let f = x.a in f f`, at type `⊤`: the type of `f f` is
`x.A`, which may not escape the `let`. -/
def E2 : HasTy Ctx.nil
    (.let (.val (.obj E2Defs)) (.let (.proj .here la) (.app .here .here))) .top :=
  .let (.obj E2DefsTy E2Distinct E2Guarded)
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

def E3xDom : HasTy E3Ctx2 (.path (.var (.there .here))) E3Dom := var' (.there .here) rfl
def E3xLo : HasTy E3Ctx2 (.path (.var (.there .here))) (.typ lA .bot E3T1) :=
  .sub E3xDom (.and1 .typ .typ)
def E3xHi : HasTy E3Ctx2 (.path (.var (.there .here))) (.typ lA E3T2 .top) :=
  .sub E3xDom (.and2 .typ .typ)
/-- `T₂ <: x.A <: T₁`: the shared member, used at both bounds. -/
def E3sub : Sub E3Ctx2 E3T2 E3T1 := .trans (.selLower E3xHi) (.selUpper E3xLo)
def E3z : HasTy E3Ctx2 (.path (.var .here)) E3T1 := .sub (var' .here rfl) E3sub

def E3body : HasTy E3Ctx2 (.let (.path (.var .here)) (.path (.var .here))) E3T1 :=
  .let E3z (var' .here rfl) (.fld .top)

def E3inner : HasTy E3Ctx1
    (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here))))) (.all E3T2 E3T1) :=
  .lam E3body (.fld .top)

/-- `λ(x : {A : ⊥..T₁} ∧ {A : T₂..⊤}). λ(z : T₂). let y = z in y`. -/
def E3 : HasTy Ctx.nil
    (.val (.lam E3Dom (.val (.lam E3T2 (.let (.path (.var .here)) (.path (.var .here)))))))
    (.all E3Dom (.all E3T2 E3T1)) :=
  .lam E3inner (.and (.typ .bot (.fld .top)) (.typ (.fld .top) .top) .typ .typ)

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

def E4x : HasTy E4Ctx3 (.path (.var (.there (.there .here)))) E4X :=
  var' (.there (.there .here)) rfl
/-- `S <: x.B <: T`, the step with no realizer. -/
def E4ST : Sub E4Ctx3 E4S E4T := .trans (.selLower E4x) (.selUpper E4x)
def E4wT : HasTy E4Ctx3 (.path (.var (.there .here))) E4T :=
  .sub (var' (.there .here) rfl) E4ST
def E4g : HasTy E4Ctx3
    (.val (.lam (.sel (.var (.there .here)) lA) (.path (.var .here)))) E4G :=
  .lam (var' .here rfl) .sel

def E4Ctx4 : Ctx ([],x,x,x,x) := .cons E4Ctx3 E4G

def E4x4 : HasTy E4Ctx4 (.path (.var (.there (.there (.there .here))))) E4X :=
  var' (.there (.there (.there .here))) rfl
def E4ST4 : Sub E4Ctx4 E4S E4T := .trans (.selLower E4x4) (.selUpper E4x4)
def E4wT4 : HasTy E4Ctx4 (.path (.var (.there (.there .here)))) E4T :=
  .sub (var' (.there (.there .here)) rfl) E4ST4
/-- `n : Int <: w.A`. -/
def E4nA : HasTy E4Ctx4 (.path (.var (.there .here)))
    (.sel (.var (.there (.there .here))) lA) :=
  .sub (var' (.there .here) rfl) (.selLower E4wT4)
def E4gv : HasTy E4Ctx4 (.path (.var .here)) E4G' := var' .here rfl
def E4app : HasTy E4Ctx4 (.app .here (.there .here))
    (.sel (.var (.there (.there .here))) lA) := .app E4gv E4nA

def E4let : HasTy E4Ctx3
    (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path (.var .here))))
      (.app .here (.there .here)))
    (.sel (.var (.there .here)) lA) :=
  .let E4g E4app .sel

/-- `λ(x : {B : S..T}). λ(w : S). λ(n : Int). let g = λ(y : w.A). y in g n`. -/
def E4 : HasTy Ctx.nil
    (.val (.lam E4X (.val (.lam E4S (.val (.lam E4Int
      (.let (.val (.lam (.sel (.var (.there .here)) lA) (.path (.var .here))))
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
def E5Obj : Tm (s,x) := .val (.obj (.trm la (.path (.var (.there .here)))))

def E5Ctx1 : Ctx ([],x) := .cons .nil E5AT
def E5Ctxv : Ctx ([],x,x) := .cons E5Ctx1 E5AT
/-- The definitions of the literal `ν(z. {a = v})`. -/
def E5Defs : Defs (s,x,x) := .trm la (.path (.var (.there .here)))
def E5Ctxz : Ctx ([],x,x,x) := .consSelf E5Ctxv E5Defs E5Self

def E5v : HasTy E5Ctxz (.path (.var (.there .here))) E5AT := var' (.there .here) rfl
/-- The field body: `v : ⊤ <: v.A`, by the lower bound of `v`'s member. -/
def E5field : HasTy E5Ctxz (.path (.var (.there .here))) (.sel (.var (.there .here)) lA) :=
  .sub (.sub E5v .top) (.selLower E5v)
def E5DefsTy : DefsTy E5Ctxz E5Defs E5Self := .trm E5field
def E5ObjTy : HasTy E5Ctxv E5Obj (.mu E5Self) := .obj E5DefsTy .trm .trm
def E5fVal : HasTy E5Ctx1 (.val (.lam E5AT E5Obj)) E5F := .lam E5ObjTy (.typ .top .top)

def E5Ctxf : Ctx ([],x,x) := .cons E5Ctx1 E5F

def E5fv : HasTy E5Ctxf (.path (.var .here)) E5F := var' .here rfl
def E5w : HasTy E5Ctxf (.path (.var (.there .here))) E5AT := var' (.there .here) rfl
/-- `f w : μ(z. {a : w.A})`: the application renames `v`'s block to `w`. -/
def E5o : HasTy E5Ctxf (.app .here (.there .here)) E5Owned := .app E5fv E5w

def E5Ctxo : Ctx ([],x,x,x) := .cons E5Ctxf E5Owned

def E5oMu : HasTy E5Ctxo (.path (.var .here)) E5Owned' := var' .here rfl
def E5oOpen : HasTy E5Ctxo (.path (.var .here))
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

end Examples
end DotMNF
