import Coercions.Frontend.Fuel
import Coercions.Classifiers.Frontend.Decide
import Coercions.Classifiers.DotMNF.Examples

/-!
# Member lookup on the tank

The lookup asks which shapes a variable has that carry a given member.  It
follows `Types.findMember` (core/Types.scala).  A recursive shape is opened at
the variable (`goRec`).  Both operands of an intersection are searched
(`goAnd`).  A selection continues in the upper bounds of the members of its
prefix (`TypeBounds.underlying`).  An atom that fits the key is an answer.
`⊥` has no members.

A type is a shape with a capture set, and a variable is typed at a plain
answer `.ty (S ^ C)`.  The lookup walks the shape and leaves the capture set
alone, as the compiler strips a capturing type before it looks a member up.
So each answer carries a map from the variable at the view to the variable at
the shape found, at every use set and capture set.  The rules `Rec-E` and
`sub` with `ESub.ty`, `Sub.capt` and `Subcap.refl` keep the sets.  The view a
lookup starts from is the declared shape, which `HasTy.var` gives at `{x}`.

The keys are a type member, a capture member bounded by sets, a capture member
bounded by a kind, a field, a function type and a box.  A capture member
bounded by a kind is `{C : φ}`.  The compiler reads it as a type member whose
upper bound is `{any.only[φ]}`, and finds it like any other member.

`members` reads one kind of member of a variable off its declared shape.  It
does the lookup at a key, then applies a reader that takes a found shape
apart.  `typs` reads the type members, with the premise of `SubShape.selUpper`
and `SubShape.selLower`.  `caps` reads the capture members bounded by sets,
with the premise of `Subcap.selUpper` and `Subcap.selLower`.  `capks` reads
those bounded by a kind, with the premise of `CapKind.ksel`.

The lookup draws on the tank of `Fuel.lean`.  Each key costs `cost` of the
number of keys pending along the branch.  A key that repeats along a branch
has no answer, which is the compiler's cyclic reference.  The compiler merges
two members of one name (`TypeBounds.&`).  There is no rule for that merge, so
the lookup returns every member it finds, in the order it finds them, and the
caller tries each.

Each answer carries its derivation, so there is no soundness theorem.  What
it has is the frame lemma of the tank: a lookup that ends with the tank
unmarked gives the same answers with more fuel.

Every definition is structural, so the kernel evaluates a lookup.  The checks
at the end run the lookups of nine examples and a run out of fuel by
`decide +kernel`.
-/

namespace ClassifiersFrontend.Core

open Frontend.Fuel
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open Classifiers
open scoped Classifiers.DotMNF

/-- The cost of a goal at depth `k`.  It grows with the depth, so the fuel also
bounds the depth of a branch, as the stack does in the compiler. -/
def cost (k : Nat) : Nat := k + 1

theorem costOk : CostOk cost := costOk_succ

/-- The fuel every entry point starts from. -/
def defaultFuel : Nat := 2 ^ 15

/-- The variable `x` at the shape `V` and the capture set `C`, used at `U`. -/
abbrev Var {s : Sig} (Γ : Ctx s) (x : BVar s .var) (U C : CaptureSet s) (V : Shape s) : Type :=
  HasTy U Γ (.path (.var x)) (.ty (V ^ C))

/-- A map from the variable at the shape `V` to the variable at the shape
`T`, at every use set and capture set. -/
abbrev VarFn {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Shape s) : Type :=
  (U C : CaptureSet s) → Var Γ x U C V → Var Γ x U C T

/-- What a lookup looks for: a type member, a capture member bounded by sets,
a capture member bounded by a kind, a field, a function type or a box. -/
inductive Key where
  | typ (A : Label)
  | cap (A : Label)
  | capk (A : Label)
  | fld (a : Label)
  | fn
  | box
deriving DecidableEq

/-- The key fits an atom of a shape. -/
def Key.fits {s : Sig} : Key → Shape s → Bool
  | .typ A, .typ B _ _ => decide (A = B)
  | .cap A, .cap B _ _ => decide (A = B)
  | .capk A, .capk B _ => decide (A = B)
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

/-- Read a capture member bounded by sets at `A` off a found shape. -/
def Found.cap? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (A : Label)
    (e : Found Γ x V) :
    Option ((c1 : CaptureSet s) × (c2 : CaptureSet s) × VarFn Γ x V (.cap A c1 c2)) :=
  match h : e.ty with
  | .cap B c1 c2 => if hB : B = A then some ⟨c1, c2, fun U C d => hB ▸ h ▸ e.f U C d⟩ else none
  | _ => none

/-- Read a capture member bounded by a kind at `A` off a found shape. -/
def Found.capk? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (A : Label)
    (e : Found Γ x V) : Option ((φ : Cls.Kind) × VarFn Γ x V (.capk A φ)) :=
  match h : e.ty with
  | .capk B φ => if hB : B = A then some ⟨φ, fun U C d => hB ▸ h ▸ e.f U C d⟩ else none
  | _ => none

/-- A lookup key in full: the variable, the shape it is searched at, the key. -/
abbrev LKey (s : Sig) := BVar s .var × Shape s × Key

/-- Member lookup, the cases of `findMember`'s `go`.  `μ` is opened at the
variable when its body is a declaration shape, as `Rec-E` asks (`goRec`).  Both
operands of `∧` are searched, the left one first (`goAnd`).  A selection
continues in the upper bounds of the prefix's members.  A key that repeats
along a branch has no answer.  A key costs `cost` of the number of keys
pending.  A short tank answers `[]` and is marked.  Each recursive call starts
from the tank the previous one left.  An answer that ends with the tank marked
is returned as it is, and the caller treats it as a failure. -/
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

/-- The members of `p` at the key `k`, from its declared shape.  The reader
`pick` takes a found shape apart and drops one it does not read. -/
def members {s : Sig} {β : Type} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (k : Key)
    (pick : Found Γ p (Γ.lookup p).shape → Option β) : Fu (List β) :=
  Fu.bind (look Γ d [] p (Γ.lookup p).shape k) fun es => Fu.ret (es.filterMap pick)

/-- A type member of `p` at `A`: its bounds, and `p` at the member, the
premise of `SubShape.selUpper` and `SubShape.selLower`.  The use set and the
capture set are `{p}`, as `HasTy.var` gives them. -/
abbrev TMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (lo : Shape s) × (hi : Shape s) × Var Γ p [.var p] [.var p] (.typ A lo hi)

/-- A capture member of `p` at `A` bounded by sets: its bounds, and `p` at the
member, the premise of `Subcap.selUpper` and `Subcap.selLower`. -/
abbrev CMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (c1 : CaptureSet s) × (c2 : CaptureSet s) × Var Γ p [.var p] [.var p] (.cap A c1 c2)

/-- A capture member of `p` at `A` bounded by a kind: the kind, and `p` at
the member, the premise of `CapKind.ksel`. -/
abbrev KMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (φ : Cls.Kind) × Var Γ p [.var p] [.var p] (.capk A φ)

/-- The type members of `p` at `A`. -/
def typs {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) : Fu (List (TMem Γ p A)) :=
  members Γ d p (.typ A) fun e => (e.typ? A).map fun ⟨lo, hi, g⟩ => ⟨lo, hi, g _ _ .var⟩

/-- The capture members of `p` at `A` bounded by sets. -/
def caps {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) : Fu (List (CMem Γ p A)) :=
  members Γ d p (.cap A) fun e => (e.cap? A).map fun ⟨c1, c2, g⟩ => ⟨c1, c2, g _ _ .var⟩

/-- The capture members of `p` at `A` bounded by a kind. -/
def capks {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) : Fu (List (KMem Γ p A)) :=
  members Γ d p (.capk A) fun e => (e.capk? A).map fun ⟨φ, g⟩ => ⟨φ, g _ _ .var⟩

/-! ## The frame lemmas -/

/-- Either branch of a test is framed, so the test is. -/
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
      | capk _ _ => exact ret_framed _
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

theorem members_framed {s : Sig} {β : Type} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (k : Key)
    (pick : Found Γ p (Γ.lookup p).shape → Option β) : Framed (members Γ d p k pick) :=
  bind_framed (look_framed Γ d _ _ _ _) fun _ => ret_framed _

theorem members_frame {s : Sig} {β : Type} {Γ : Ctx s} {d : Nat} {p : BVar s .var} {k : Key}
    {pick : Found Γ p (Γ.lookup p).shape → Option β} {t t' : Tank} {ms : List β}
    (h : members Γ d p k pick t = (ms, t')) (ho : t'.out = false) (j : Nat) :
    members Γ d p k pick (t.add j) = (ms, t'.add j) :=
  (members_framed Γ d p k pick).shift t ms t' h ho j

theorem typs_framed {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Framed (typs Γ d p A) :=
  members_framed _ _ _ _ _

theorem caps_framed {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Framed (caps Γ d p A) :=
  members_framed _ _ _ _ _

theorem capks_framed {s : Sig} (Γ : Ctx s) (d : Nat) (p : BVar s .var) (A : Label) :
    Framed (capks Γ d p A) :=
  members_framed _ _ _ _ _

/-! ## Checks

P4's `y` is declared at `x.A`, whose upper bound puts the field `a` four steps
down.  R1's `y` is declared at `x.A ∧ {a : {b : ⊤}}`, so it has two fields `a`.  P5's `f` is an
intersection of two function types.  B1's `n` has a field `a` and no field
`b`.  E6's `z` is the self binder of a literal whose type member `T` is
`Int`.  E8's `y` is declared at `x.A ∧ {a : ⊤}`.  `E7Ctx` is an alias cycle.
C2's `x` is an abstract object whose capture member `C` lies between `{}` and
`{κ₁, κ₂}`.  CE4's `x` has the capture member `C` bounded by the kind
`only[Control]`. -/

section LookChecks

open Classifiers.DotMNF.Examples

/-- The start of a lookup at `x`'s declared shape, from a full tank. -/
def lookAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) (n : Nat := defaultFuel) :
    List (Shape s) × Tank :=
  let r := look Γ n [] x (Γ.lookup x).shape k ⟨n, false⟩
  (r.1.map (·.ty), r.2)

/-- The type members of `p` at `A`, with the tank left. -/
def typsFull {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (n : Nat := defaultFuel) :
    List (Shape s × Shape s) × Tank :=
  let r := typs Γ n p A ⟨n, false⟩
  (r.1.map fun d => (d.1, d.2.1), r.2)

/-- The capture members of `p` at `A` bounded by sets, with the tank left. -/
def capsFull {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (n : Nat := defaultFuel) :
    List (CaptureSet s × CaptureSet s) × Tank :=
  let r := caps Γ n p A ⟨n, false⟩
  (r.1.map fun d => (d.1, d.2.1), r.2)

/-- The capture members of `p` at `A` bounded by a kind, with the tank left. -/
def capksFull {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (n : Nat := defaultFuel) :
    List Cls.Kind × Tank :=
  let r := capks Γ n p A ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- `x : {A : ⊥..μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : s.B}))}`, `y : x.A`. -/
def P4Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot (.mu (.and (.fld lb (.top ^ [])) (.and (.fld lv (.top ^ []))
    (.fld la ((Shape.sel (.var .here) lB) ^ [])))))) ^ [])).cons ((Shape.sel (.var .here) lA) ^ [])

/-- `x : {A : ⊥..{a : ⊤}}`, `y : x.A ∧ {a : {b : ⊤}}`. -/
def R1Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA .bot (.fld la (.top ^ []))) ^ [])).cons
    ((Shape.and (.sel (.var .here) lA) (.fld la ((Shape.fld lb (.top ^ [])) ^ []))) ^ [])

/-- `f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)`, `y : ⊤`. -/
def P5Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.and (.all ((Shape.fld la (.top ^ [])) ^ []) (.ty (.top ^ [])))
    (.all (.top ^ []) (.ty (.top ^ [])))) ^ [])).cons (.top ^ [])

/-- `x : {A : {a : ⊤}..{b : ⊤}}`, `n : {a : ⊤}`. -/
def B1Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA (.fld la (.top ^ [])) (.fld lb (.top ^ []))) ^ [])).cons
    ((Shape.fld la (.top ^ [])) ^ [])

/-- `x : μ(x. {A = x.B} ∧ {B = x.A})`. -/
def E7Ctx : Ctx ([],x) := Ctx.nil.cons ((Shape.mu E7Self) ^ [])

-- P4: the field `a` four steps down `x.A`'s upper bound, read at `y`'s own `B`.
example : (lookAt P4Ctx .here (.fld la)).1 = [.fld la ((Shape.sel (.var .here) lB) ^ [])] := by
  decide +kernel
example : (lookAt P4Ctx .here (.fld la)).2.out = false := by decide +kernel
-- Fuel 1 runs out on P4.
example : (lookAt P4Ctx .here (.fld la) 1).2.out = true := by decide +kernel
-- R1: both fields `a` of `y`, the one through `x.A` first.
example : (lookAt R1Ctx .here (.fld la)).1 =
    [.fld la (.top ^ []), .fld la ((Shape.fld lb (.top ^ [])) ^ [])] := by decide +kernel
example : (lookAt R1Ctx .here (.fld la)).2.out = false := by decide +kernel
-- P5: both function types of `f`, the left operand's first.
example : (lookAt P5Ctx (.there .here) .fn).1 =
    [.all ((Shape.fld la (.top ^ [])) ^ []) (.ty (.top ^ [])), .all (.top ^ []) (.ty (.top ^ []))] := by
  decide +kernel
example : (lookAt P5Ctx (.there .here) .fn).2.out = false := by decide +kernel
-- B1: `n` has no field `b`.  The lookup does not widen through `x.A`'s lower bound.
example : (lookAt B1Ctx .here (.fld lb)).1.length = 0 := by decide +kernel
example : (lookAt B1Ctx .here (.fld lb)).2.out = false := by decide +kernel
-- E6: the type member `T` of the self binder, through `μ` and the left operand.
example : (typsFull E6Ctxz .here lT).1 = [(E6IntS, E6IntS)] := by decide +kernel
example : (typsFull E6Ctxz .here lT).2.out = false := by decide +kernel
-- E8: the field `a` of `y` through `x.A`'s upper bound, then the written one.
example : (lookAt E8Ctx2 .here (.fld la)).1 = [.fld la (.top ^ []), .fld la (.top ^ [])] := by
  decide +kernel
example : (typsFull E8Ctx2 (up .here) lA).1 = [(.bot, .fld la (.top ^ []))] := by decide +kernel
-- E7: the field `a` through the alias cycle `x.A = x.B`, `x.B = x.A`.  The key repeats, so
-- there is no answer and the tank stays unmarked.
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : (look E7Ctx defaultFuel [] .here (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
-- C2: the capture member `C` of the abstract object `x`, bounded by sets.
example : (capsFull (C2CtxG E3PlatCtx E3k1 E3k2) (.there (up .here)) lC).1 =
    [([], [.cvar (.there (up (up E3k1))), .cvar (.there (up (up E3k2)))])] := by decide +kernel
example : (capsFull (C2CtxG E3PlatCtx E3k1 E3k2) (.there (up .here)) lC).2.out = false := by
  decide +kernel
-- C2's member is bounded by sets, so it is no member bounded by a kind.
example : (capksFull (C2CtxG E3PlatCtx E3k1 E3k2) (.there (up .here)) lC).1.length = 0 := by
  decide +kernel
-- CE4: the capture member `C` of `x`, bounded by `only[Control]`, the premise of `ksel`.
example : (capksFull E3ClientCtx (.there (up .here)) lC).1 = [Cls.only Cls.Control] := by
  decide +kernel
example : (capksFull E3ClientCtx (.there (up .here)) lC).2.out = false := by decide +kernel
-- CE4's member is bounded by a kind, so it is no member bounded by sets.
example : (capsFull E3ClientCtx (.there (up .here)) lC).1.length = 0 := by decide +kernel

end LookChecks

end ClassifiersFrontend.Core
