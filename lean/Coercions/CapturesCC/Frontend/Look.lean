import Coercions.Frontend.Fuel
import Coercions.CapturesCC.Frontend.Decide
import Coercions.CapturesCC.DotMNF.Examples

/-!
# Member lookup on the tank

The lookup asks which shapes a variable has that carry a given member.  It
follows the compiler's `findMember` (`Types.scala:820-870`).  A recursive
shape is opened at the variable (`goRec`, `Types.scala:875-896`).  Both
operands of an intersection are searched (`goAnd`, `Types.scala:994-995`).  A
selection continues in the upper bounds of the members of its prefix
(`Types.scala:5720`).  An atom that fits the key is an answer.  `⊥` has no
members (`Types.scala:827-829`).

A type of the version is a shape with a capture set, and a variable is typed
at a plain answer `.ty (S ^ C)`.  The lookup walks the shape and leaves the
capture set alone.  The compiler strips a capturing type before it looks a
member up, and the variable rules `Rec-E` and `sub` with `ESub.ty`,
`Sub.capt` and `Subcap.refl` keep the set.  So each answer carries a map from
the variable at the view to the variable at the shape found, at every use set
and every capture set.  The view a lookup starts from is the declared shape,
which `HasTy.var` gives at the use set and capture set `{x}`.

The keys are a type member, a capture member, a field, a function type and a
box.  `decls` reads the type members of a variable off its declared shape,
each with the premise that `SubShape.selUpper` and `SubShape.selLower` ask
for.  `capDecls` does the same for capture members and the premise of
`Subcap.selUpper` and `Subcap.selLower`.

The lookup draws on the tank of `Fuel.lean`.  Each key costs `cost` of the
number of keys pending along the branch.  It keeps its own pending keys, and a
key that repeats along a branch has no answer, which is the compiler's cyclic
reference.  The compiler merges two members of one name (`Types.scala:5759`).
The version has no rule for that merge, so the lookup returns every member it
finds, in the order it finds them, and the caller tries each.

Each answer carries its derivation, so the lookup has no soundness theorem to
prove.  What it has is the frame lemma of the tank: a lookup that ends with
the tank unmarked gives the same answers with more fuel.

Every definition is structural, so the kernel evaluates a lookup.  The checks
at the end of the module run the lookups of six examples and a run out of
fuel by `decide +kernel`.
-/

namespace CapturesCCFrontend.Core

open Frontend.Fuel
open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open scoped CapturesCC.DotMNF

/-- The cost of a goal at depth `k`.  It grows with the depth, so the fuel
also bounds the depth of a branch, as the stack does in the compiler. -/
def cost (k : Nat) : Nat := k + 1

theorem costOk : CostOk cost := costOk_succ

/-- The fuel every entry point starts from. -/
def defaultFuel : Nat := 2 ^ 15

/-- The variable `x` at the shape `V` and the capture set `C`, used at `U`. -/
abbrev Var {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U C : CaptureSet s) (V : Shape s) : Type :=
  HasTy U Γ (.path (.var x)) (.ty (V ^ C))

/-- A map from the variable at the shape `V` to the variable at the shape
`T`, at every use set and capture set.  The rules `Rec-E` and `sub` with
`Subcap.refl` on both sets keep them, so a walk over the shape never touches
them. -/
abbrev VarFn {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Shape s) : Type :=
  (U C : CaptureSet s) → Var Γ x U C V → Var Γ x U C T

/-- What a lookup looks for: a type member, a capture member, a field, a
function type or a box. -/
inductive Key where
  | typ (A : Label)
  | cap (A : Label)
  | fld (a : Label)
  | fn
  | box
deriving DecidableEq

/-- The key fits an atom of a shape. -/
def Key.fits {s : Sig} : Key → Shape s → Bool
  | .typ A, .typ B _ _ => decide (A = B)
  | .cap A, .cap B _ _ => decide (A = B)
  | .fld a, .fld b _ => decide (a = b)
  | .fn, .all _ _ => true
  | .box, .box _ => true
  | _, _ => false

/-- A shape the variable has, reached from the view `V`, with the map that
takes the variable at the view to the variable at that shape. -/
structure Found {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V : Shape s) where
  ty : Shape s
  f : VarFn Γ x V ty

/-- Read a type member at `A` off a found shape. -/
def Found.typ? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (A : Label)
    (e : Found Γ x V) : Option ((lo : Shape s) × (hi : Shape s) × VarFn Γ x V (.typ A lo hi)) :=
  match h : e.ty with
  | .typ B lo hi => if hB : B = A then some ⟨lo, hi, fun U C d => hB ▸ h ▸ e.f U C d⟩ else none
  | _ => none

/-- Read a capture member at `A` off a found shape. -/
def Found.cap? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (A : Label)
    (e : Found Γ x V) :
    Option ((c1 : CaptureSet s) × (c2 : CaptureSet s) × VarFn Γ x V (.cap A c1 c2)) :=
  match h : e.ty with
  | .cap B c1 c2 => if hB : B = A then some ⟨c1, c2, fun U C d => hB ▸ h ▸ e.f U C d⟩ else none
  | _ => none

/-- A lookup key in full: the variable, the shape it is searched at, the key. -/
abbrev LKey (s : Sig) := BVar s .var × Shape s × Key

/-- Member lookup on demand, the cases of `findMember`'s `go`
(`Types.scala:820-870`).  `μ` is opened at the variable when its body is a
declaration shape, as `Rec-E` asks (`goRec`, `Types.scala:875-896`).  Both
operands of `∧` are searched, the left one first (`goAnd`,
`Types.scala:994-995`).  A selection continues in the upper bounds of the
prefix's members (`Types.scala:5720`).  A key that repeats along a branch has
no answer, the compiler's cyclic reference.  `⊥` has no members
(`Types.scala:827-829`).  A key costs `cost` of the number of keys pending.
A short tank answers `[]` and is marked.  Every recursive call starts from the
tank the previous one left.  An answer that ends with the tank marked is
returned as it is, and the caller treats it as a failure. -/
def look {s : Sig} (Γ : Ctx s) : Nat → List (LKey s) → (x : BVar s .var) → (V : Shape s) → Key →
    Fu (List (Found Γ x V))
  | 0, _, _, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, x, V, k =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true =>
          if (x, V, k) ∈ P then Fu.ret [] else
          if k.fits V then Fu.ret [⟨V, fun _ _ e => e⟩] else
          match V with
          | .mu B =>
              if hB : Shape.Decl B then
                Fu.bind (look Γ d ((x, .mu B, k) :: P) x (B.substVar x) k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun U C v => e.f U C (.recE v hB)⟩)
              else Fu.ret []
          | .and V1 V2 =>
              Fu.bind (look Γ d ((x, .and V1 V2, k) :: P) x V1 k) fun es1 =>
                Fu.bind (look Γ d ((x, .and V1 V2, k) :: P) x V2 k) fun es2 =>
                  Fu.ret (es1.map (fun e => ⟨e.ty, fun U C v =>
                      e.f U C (.sub v (.ty (.capt .and1 .refl)) .refl)⟩) ++
                    es2.map (fun e => ⟨e.ty, fun U C v =>
                      e.f U C (.sub v (.ty (.capt .and2 .refl)) .refl)⟩))
          | .sel (.var q) B =>
              Fu.bind (look Γ d ((x, .sel (.var q) B, k) :: P) q (Γ.lookup q).shape (.typ B)) fun es =>
                Fu.flatMapL (fun e =>
                  match e.typ? B with
                  | some ⟨_, hi, g⟩ =>
                      Fu.bind (look Γ d ((x, .sel (.var q) B, k) :: P) x hi k) fun es2 =>
                        Fu.ret (es2.map fun e2 => ⟨e2.ty, fun U C v =>
                          e2.f U C (.sub v (.ty (.capt (.selUpper (g _ _ .var)) .refl)) .refl)⟩)
                  | none => Fu.ret []) es
          | _ => Fu.ret []
termination_by structural d _ _ _ _ => d

/-- A type member of `p` at `A`: its bounds, and `p` at the member, the
premise of `SubShape.selUpper` and `SubShape.selLower`.  The use set and the
capture set are `{p}`, as `HasTy.var` gives them. -/
abbrev TMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (lo : Shape s) × (hi : Shape s) × Var Γ p [.var p] [.var p] (.typ A lo hi)

/-- A capture member of `p` at `A`: its bounds, and `p` at the member, the
premise of `Subcap.selUpper` and `Subcap.selLower`. -/
abbrev CMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (c1 : CaptureSet s) × (c2 : CaptureSet s) × Var Γ p [.var p] [.var p] (.cap A c1 c2)

/-- The type members of `p` at `A`, from its declared shape. -/
def decls {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Fu (List (TMem Γ p A)) :=
  Fu.bind (look Γ d [] p (Γ.lookup p).shape (.typ A)) fun es =>
    Fu.ret (es.filterMap fun e => (e.typ? A).map fun ⟨lo, hi, g⟩ => ⟨lo, hi, g _ _ .var⟩)

/-- The capture members of `p` at `A`, from its declared shape. -/
def capDecls {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Fu (List (CMem Γ p A)) :=
  Fu.bind (look Γ d [] p (Γ.lookup p).shape (.cap A)) fun es =>
    Fu.ret (es.filterMap fun e => (e.cap? A).map fun ⟨c1, c2, g⟩ => ⟨c1, c2, g _ _ .var⟩)

/-! ## The frame lemmas -/

/-- Either branch of a test is framed, so the test is.  The proof takes the
`Decidable` instance apart, so it needs no choice. -/
theorem ite_framed {α : Type} {p : Prop} [hp : Decidable p] {a b : Fu α} (ha : Framed a)
    (hb : Framed b) : Framed (if p then a else b) := by
  cases hp
  · exact hb
  · exact ha

/-- The same for a test whose branches use its proof. -/
theorem dite_framed {α : Type} {p : Prop} [hp : Decidable p] {a : p → Fu α} {b : ¬p → Fu α}
    (ha : ∀ h, Framed (a h)) (hb : ∀ h, Framed (b h)) : Framed (if h : p then a h else b h) := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-- At index zero the lookup marks the tank and answers `[]`. -/
theorem nil_framed (β : Type) : Framed (fun t : Tank => (([] : List β), { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

/-- Every lookup is framed: it keeps a marked tank, never adds fuel, and does
the same with more fuel. -/
theorem look_framed {s : Sig} (Γ : Ctx s) (d : Nat) :
    ∀ (P : List (LKey s)) (x : BVar s .var) (V : Shape s) (k : Key), Framed (look Γ d P x V k) := by
  induction d with
  | zero =>
    intro P x V k
    exact nil_framed (Found Γ x V)
  | succ d ih =>
    intro P x V k
    apply bind_framed (draw_framed _)
    intro ok
    cases ok
    · exact ret_framed _
    · apply ite_framed (ret_framed _)
      apply ite_framed (ret_framed _)
      cases V with
      | mu B =>
        exact dite_framed (fun _ => bind_framed (ih _ _ _ _) fun _ => ret_framed _)
          (fun _ => ret_framed _)
      | and V1 V2 =>
        exact bind_framed (ih _ _ _ _) fun _ => bind_framed (ih _ _ _ _) fun _ => ret_framed _
      | sel p B =>
        cases p with
        | var q =>
          refine bind_framed (ih _ _ _ _) fun es => flatMapL_framed ?_ es
          intro e
          split
          · exact bind_framed (ih _ _ _ _) fun _ => ret_framed _
          · exact ret_framed _
      | top => exact ret_framed _
      | bot => exact ret_framed _
      | typ _ _ _ => exact ret_framed _
      | fld _ _ => exact ret_framed _
      | cap _ _ _ => exact ret_framed _
      | all _ _ => exact ret_framed _
      | box _ => exact ret_framed _

theorem look_frame {s : Sig} {Γ : Ctx s} {d : Nat} {P : List (LKey s)} {x : BVar s .var}
    {V : Shape s} {k : Key} {t t' : Tank} {es : List (Found Γ x V)} (h : look Γ d P x V k t = (es, t'))
    (ho : t'.out = false) (j : Nat) :
    look Γ d P x V k (t.add j) = (es, t'.add j) :=
  (look_framed Γ d P x V k).shift t es t' h ho j

/-- A lookup from a marked tank answers `[]` and leaves the tank as it is. -/
theorem look_absorbs {s : Sig} (Γ : Ctx s) (d : Nat) (P : List (LKey s)) (x : BVar s .var)
    (V : Shape s) (k : Key) {t : Tank} (h : t.out = true) : look Γ d P x V k t = ([], t) := by
  cases d with
  | zero => cases t; simp_all [look]
  | succ d =>
    change Fu.bind (draw (cost P.length)) _ t = _
    simp only [Fu.bind, draw_out h]
    rfl

theorem decls_framed {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Framed (decls Γ d p A) :=
  bind_framed (look_framed Γ d _ _ _ _) fun _ => ret_framed _

theorem decls_frame {s : Sig} {Γ : Ctx s} {d : Nat} {p : BVar s .var} {A : Label} {t t' : Tank}
    {ds : List (TMem Γ p A)}
    (h : decls Γ d p A t = (ds, t')) (ho : t'.out = false) (j : Nat) :
    decls Γ d p A (t.add j) = (ds, t'.add j) :=
  (decls_framed Γ d p A).shift t ds t' h ho j

theorem capDecls_framed {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Framed (capDecls Γ d p A) :=
  bind_framed (look_framed Γ d _ _ _ _) fun _ => ret_framed _

theorem capDecls_frame {s : Sig} {Γ : Ctx s} {d : Nat} {p : BVar s .var} {A : Label} {t t' : Tank}
    {ds : List (CMem Γ p A)}
    (h : capDecls Γ d p A t = (ds, t')) (ho : t'.out = false) (j : Nat) :
    capDecls Γ d p A (t.add j) = (ds, t'.add j) :=
  (capDecls_framed Γ d p A).shift t ds t' h ho j

/-! ## Checks

Each check runs in the kernel.  E6's `z` is the self binder of a literal
whose type member `T` is `Int` and whose field `v` is declared at `z.T`.
E8's `y` is declared at `x.A ∧ {a : ⊤}`.  `P4Ctx` puts a field four steps
down a selection's upper bound.  `E7Ctx` is an alias cycle.  C2's `x` is an
abstract object whose capture member `C` lies between `{}` and `{κ₁, κ₂}`.
`CycCtx` has a capture member bounded by itself. -/

section LookChecks

open CapturesCC.DotMNF.Examples

/-- The start of a lookup at `x`'s declared shape, from a full tank. -/
def lookAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) (n : Nat := defaultFuel) :
    List (Shape s) × Tank :=
  let r := look Γ n [] x (Γ.lookup x).shape k ⟨n, false⟩
  (r.1.map (·.ty), r.2)

/-- The type members of `p` at `A`, with the tank left. -/
def declsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (n : Nat := defaultFuel) :
    List (Shape s × Shape s) × Tank :=
  let r := decls Γ n p A ⟨n, false⟩
  (r.1.map fun d => (d.1, d.2.1), r.2)

/-- The capture members of `p` at `A`, with the tank left. -/
def capDeclsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (n : Nat := defaultFuel) :
    List (CaptureSet s × CaptureSet s) × Tank :=
  let r := capDecls Γ n p A ⟨n, false⟩
  (r.1.map fun d => (d.1, d.2.1), r.2)

/-- `x : {A : ⊥..μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : ⊤}))}`, `y : x.A`. -/
def P4Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot (.mu (.and (.fld lb (.top ^ [])) (.and (.fld lv (.top ^ []))
    (.fld la (.top ^ [])))))) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `x : μ(x. {A = x.B} ∧ {B = x.A})`. -/
def E7Ctx : Ctx ([],x) := Ctx.nil.cons ((Shape.mu E7Self) ^ [])

/-- `z : μ(z. {C : {}..{z.C}})`, a capture member bounded by itself. -/
def CycCtx : Ctx ([],c,c,x) := platCtx.cons ((Shape.mu (.cap lC [] [CapAtom.sel .here lC])) ^ [])

-- E6: the type member `T` of the self binder, through `μ` and the left operand.
example : (declsAt E6Ctxz .here lT).1 = [(E6IntS, E6IntS)] := by decide +kernel
example : (declsAt E6Ctxz .here lT).2.out = false := by decide +kernel
-- E6: the field `v`, declared at the self's own member `z.T`.
example : (lookAt E6Ctxz .here (.fld lv)).1 = [.fld lv ((Shape.sel (.var .here) lT) ^ [])] := by
  decide +kernel
-- E8: the field `a` of `y` through `x.A`'s upper bound, then the written one.
example : (lookAt E8Ctx2 .here (.fld la)).1 = [.fld la (.top ^ []), .fld la (.top ^ [])] := by
  decide +kernel
example : (lookAt E8Ctx2 .here (.fld la)).2.out = false := by decide +kernel
-- E8: the members of `x` at `A`, one, `⊥ .. {a : ⊤}`.
example : (declsAt E8Ctx2 (up .here) lA).1 = [(.bot, .fld la (.top ^ []))] := by decide +kernel
-- P4: the field `a` four steps down `x.A`'s upper bound.
example : (lookAt P4Ctx .here (.fld la)).1 = [.fld la (.top ^ [])] := by decide +kernel
example : (lookAt P4Ctx .here (.fld la)).2.out = false := by decide +kernel
-- A lookup at fuel 1 runs out on P4.
example : (lookAt P4Ctx .here (.fld la) 1).2.out = true := by decide +kernel
-- E7: the field `a` through the alias cycle `x.A = x.B`, `x.B = x.A`.  The key repeats, so there
-- is no answer, and the tank stays unmarked.
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
-- C2: the capture member `C` of the abstract object `x`, through `μ` and the left operand.
example : (capDeclsAt (C2CtxG platCtx k1 k2) (.there (up .here)) lC).1 =
    [([], [.cvar (.there (up (up k1))), .cvar (.there (up (up k2)))])] := by decide +kernel
example : (capDeclsAt (C2CtxG platCtx k1 k2) (.there (up .here)) lC).2.out = false := by
  decide +kernel
-- The capture member cycle: the member is found once, with its own selection as the upper
-- bound, and the lookup ends.
example : (capDeclsAt CycCtx .here lC).1 = [([], [CapAtom.sel .here lC])] := by decide +kernel
example : (capDeclsAt CycCtx .here lC).2.out = false := by decide +kernel
-- `C` of `z` is a capture member, so `z` has no type member `C`.
example : (declsAt CycCtx .here lC).1.length = 0 := by decide +kernel

end LookChecks

end CapturesCCFrontend.Core
