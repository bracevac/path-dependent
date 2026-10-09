import Coercions.Frontend.Fuel
import Coercions.Frontend.Decide
import Coercions.DotMNF.Examples

/-!
# Member lookup on the tank

The lookup asks which types a variable has that carry a given member.  It
follows `Type.findMember` in core/Types.scala, in these cases.

* A recursive type is opened at the variable (`goRec`).
* Both operands of an intersection are searched (`goAnd`).
* A selection continues in the upper bounds of the members of its prefix
  (`TypeBounds.underlying`).
* An atom that fits the key is an answer.
* `⊥` has no members.

The lookup draws on the tank of `Fuel.lean`.  Each key costs `cost` of the
number of keys pending along the branch.  A key that repeats along a branch has
no answer, which is the compiler's cyclic reference.  The compiler merges two
members of one name (`TypeBounds.&`).  DOT-MNF has no rule for that merge, so
the lookup returns every member it finds, in the order it finds them, and the
caller tries each.

Each answer carries the derivation that takes the variable from the view it
started at to the type found.  So the lookup has no soundness theorem to
prove.  What it has is the frame lemma of the tank: a lookup that ends with the
tank unmarked gives the same answers with more fuel.  `decls` reads the type
members of a variable off its declared type, each with the premise that
`Sub.selUpper` and `Sub.selLower` ask for.

Every definition is structural, so the kernel evaluates a lookup.  The checks
at the end of the module run the lookups of four examples and a run out of
fuel by `decide +kernel`.
-/

namespace Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Defs Ctx Sub HasTy)

/-- The cost of a goal at depth `k`.  It grows with the depth, so the fuel
also bounds the depth of a branch, as the stack does in the compiler. -/
def cost (k : Nat) : Nat := k + 1

theorem costOk : CostOk cost := costOk_succ

/-- The fuel every entry point starts from.  It is the largest power of two at
which the interpreter runs every divergent goal of `Limit.lean` to the end. -/
def defaultFuel : Nat := 2 ^ 15

/-- A variable at a type. -/
abbrev Var {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Type :=
  HasTy Γ (.path (.var x)) T

/-- What a lookup looks for: a type member, a field, or a function type. -/
inductive Key where
  | typ (A : Label)
  | fld (a : Label)
  | fn
deriving DecidableEq

/-- The key fits an atom of a type. -/
def Key.fits {s : Sig} : Key → Ty s → Bool
  | .typ A, .typ B _ _ => decide (A = B)
  | .fld a, .fld b _ => decide (a = b)
  | .fn, .all _ _ => true
  | _, _ => false

/-- A type the variable has, reached from the view `V`, with the map that
takes the view's derivation to the derivation at that type. -/
structure Found {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V : Ty s) where
  ty : Ty s
  f : Var Γ x V → Var Γ x ty

/-- Read a type member at `A` off a found type. -/
def Found.typ? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} (A : Label)
    (e : Found Γ x V) : Option ((lo : Ty s) × (hi : Ty s) × (Var Γ x V → Var Γ x (.typ A lo hi))) :=
  match h : e.ty with
  | .typ B lo hi => if hB : B = A then some ⟨lo, hi, fun d => hB ▸ h ▸ e.f d⟩ else none
  | _ => none

/-- A lookup key in full: the variable, the view it is searched at, the key. -/
abbrev LKey (s : Sig) := BVar s .var × Ty s × Key

/-- Member lookup on demand, the cases of `findMember`'s `go`.  `μ` is opened
at the variable (`goRec`).  Both operands of `∧` are searched, the left one
first (`goAnd`).  A selection continues in the upper bounds of the prefix's members.
A key that repeats along a branch has no answer, the compiler's cyclic
reference.  `⊥` has no members.  A key costs `cost` of the number of keys
pending.  A short tank answers `[]` and is marked.  Every recursive call starts
from the tank the previous one left.  An answer that ends with the tank marked
is returned as it is, and the caller treats it as a failure. -/
def look {s : Sig} (Γ : Ctx s) : Nat → List (LKey s) → (x : BVar s .var) → (V : Ty s) → Key →
    Fu (List (Found Γ x V))
  | 0, _, _, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, x, V, k =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true =>
          if (x, V, k) ∈ P then Fu.ret [] else
          if k.fits V then Fu.ret [⟨V, id⟩] else
          match V with
          | .mu B =>
              Fu.bind (look Γ d ((x, .mu B, k) :: P) x (B.substVar x) k) fun es =>
                Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.recE v)⟩)
          | .and V1 V2 =>
              Fu.bind (look Γ d ((x, .and V1 V2, k) :: P) x V1 k) fun es1 =>
                Fu.bind (look Γ d ((x, .and V1 V2, k) :: P) x V2 k) fun es2 =>
                  Fu.ret (es1.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and1)⟩) ++
                    es2.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and2)⟩))
          | .sel (.var q) B =>
              Fu.bind (look Γ d ((x, .sel (.var q) B, k) :: P) q (Γ.lookup q) (.typ B)) fun es =>
                Fu.flatMapL (fun e =>
                  match e.typ? B with
                  | some ⟨_, hi, g⟩ =>
                      Fu.bind (look Γ d ((x, .sel (.var q) B, k) :: P) x hi k) fun es2 =>
                        Fu.ret (es2.map fun e2 => ⟨e2.ty, fun v => e2.f (.sub v (.selUpper (g .var)))⟩)
                  | none => Fu.ret []) es
          | _ => Fu.ret []
termination_by structural d _ _ _ _ => d

/-- The type members of `p` at `A`, from its declared type, each with the
premise of `Sub.selUpper` and `Sub.selLower`. -/
def decls {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Fu (List ((lo : Ty s) × (hi : Ty s) × Var Γ p (.typ A lo hi))) :=
  Fu.bind (look Γ d [] p (Γ.lookup p) (.typ A)) fun es =>
    Fu.ret (es.filterMap fun e => (e.typ? A).map fun ⟨lo, hi, g⟩ => ⟨lo, hi, g .var⟩)

/-! ## The frame lemmas -/

/-- Either branch of a test is framed, so the test is.  The proof takes the
`Decidable` instance apart, so it needs no choice. -/
theorem ite_framed {α : Type} {p : Prop} [hp : Decidable p] {a b : Fu α} (ha : Framed a)
    (hb : Framed b) : Framed (if p then a else b) := by
  cases hp
  · exact hb
  · exact ha

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
    ∀ (P : List (LKey s)) (x : BVar s .var) (V : Ty s) (k : Key), Framed (look Γ d P x V k) := by
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
        exact bind_framed (ih _ _ _ _) fun _ => ret_framed _
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
      | all _ _ => exact ret_framed _

theorem look_frame {s : Sig} {Γ : Ctx s} {d : Nat} {P : List (LKey s)} {x : BVar s .var} {V : Ty s}
    {k : Key} {t t' : Tank} {es : List (Found Γ x V)} (h : look Γ d P x V k t = (es, t'))
    (ho : t'.out = false) (j : Nat) :
    look Γ d P x V k (t.add j) = (es, t'.add j) :=
  (look_framed Γ d P x V k).shift t es t' h ho j

/-- A lookup from a marked tank answers `[]` and leaves the tank as it is. -/
theorem look_absorbs {s : Sig} (Γ : Ctx s) (d : Nat) (P : List (LKey s)) (x : BVar s .var) (V : Ty s)
    (k : Key) {t : Tank} (h : t.out = true) : look Γ d P x V k t = ([], t) := by
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
    {ds : List ((lo : Ty s) × (hi : Ty s) × Var Γ p (.typ A lo hi))}
    (h : decls Γ d p A t = (ds, t')) (ho : t'.out = false) (j : Nat) :
    decls Γ d p A (t.add j) = (ds, t'.add j) :=
  (decls_framed Γ d p A).shift t ds t' h ho j

/-! ## Checks

Each check runs in the kernel.  `P4Ctx` puts a field four steps down a
selection's upper bound.  `E7Ctx` is an alias cycle. -/

section LookChecks

open DotMNF.Examples

/-- The start of a lookup at `x`'s declared type, from a full tank. -/
def lookAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) (n : Nat := defaultFuel) :
    List (Ty s) × Tank :=
  let r := look Γ n [] x (Γ.lookup x) k ⟨n, false⟩
  (r.1.map (·.ty), r.2)

/-- `x : {A : ⊥..μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : s.B}))}`, `y : x.A`. -/
def P4Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.typ lA .bot (.mu (.and (.fld lb .top) (.and (.fld lv .top)
    (.fld la (.sel (.var .here) lB))))))).cons (.sel (.var .here) lA)

/-- `x : μ(x. {A = x.B} ∧ {B = x.A})`. -/
def E7Ctx : Ctx ([],x) := .cons .nil (.mu E7Self)

-- E8: `y : x.A ∧ {a : ⊤}`, the field `a` through `x.A`'s upper bound, then the written one.
example : (lookAt E8Ctx2 .here (.fld la)).1 = [.fld la .top, .fld la .top] := by decide +kernel
example : (lookAt E8Ctx2 .here (.fld la)).2.out = false := by decide +kernel
-- E9: `g : μ(∀(x : ⊤) ⊤)`, its function type through `μ`.
example : (lookAt E9CtxG .here .fn).1 = [.all .top .top] := by decide +kernel
example : (lookAt E9CtxG .here .fn).2.out = false := by decide +kernel
-- P4: the field `a` four steps down `x.A`'s upper bound.
example : (lookAt P4Ctx .here (.fld la)).1 = [.fld la (.sel (.var .here) lB)] := by decide +kernel
example : (lookAt P4Ctx .here (.fld la)).2.out = false := by decide +kernel
-- E7: the field `a` through the alias cycle `x.A = x.B`, `x.B = x.A`.  The key repeats, so
-- there is no answer and the tank stays unmarked.
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
-- P4 at fuel 1: the tank is marked.
example : (lookAt P4Ctx .here (.fld la) 1).2.out = true := by decide +kernel
-- The members of `x` at `A` in E8: one, `⊥ .. {a : ⊤}`.
example : ((decls E8Ctx2 defaultFuel (.there .here) lA ⟨defaultFuel, false⟩).1.map
    fun d => (d.1, d.2.1)) = [(.bot, .fld la .top)] := by decide +kernel

end LookChecks

end Frontend.Core
