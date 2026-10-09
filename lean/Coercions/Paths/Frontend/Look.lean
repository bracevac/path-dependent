import Coercions.Frontend.Fuel
import Coercions.Paths.DotMNF.Examples
import Coercions.Paths.Frontend.Decide

/-!
# Member lookup on paths

`lookP` finds the types a path has that carry a given member.  It follows
`Types.findMember` and its `go`.  A recursive type is opened at the path
(`goRec`).  Both operands of an intersection are searched (`goAnd`).  A
selection continues in the upper bounds of the members of its prefix
(`TypeBounds.underlying`).  An atom that fits the key is an answer.  `⊥` has
no members.

A singleton `q.type` is the case paths add.  The compiler's `go` follows the
underlying type of a `TermRef` and keeps the prefix of the original lookup.
So `goRec` opens a recursive type reached through the singleton at the original
path.  `lookP` does the same.  At a path `p` seen at `q.type` it continues at
`p`, seen at each declared type of `q`, with `PathTy.snglTrans`.  A recursive
type found there is opened at `p` by `PathTy.recE`, not at `q`.

The declared types of a path follow `TermRef.underlying`.  A variable has its
context entry.  A path `r.a` has every stable field `a` that the lookup finds
on a declared type of `r`.  So a deep path is reached by one lookup per field,
on demand.

`HasTy` has no rule that follows a singleton.  So `lookV`, the lookup at a
variable as a term, is `lookP` without the singleton case.  Application needs
it, since `HasTy.app` asks for a term typing of the function.

The lookups draw on the tank of `Fuel.lean`.  Each key costs `cost` of the
number of keys pending along the branch.  The pending keys belong to the
lookup.  A key that repeats along a branch has no answer, as in the compiler's
cyclic reference.  The compiler merges two members of one name
(`TypeBounds.&`).  The calculus has no rule for that merge.  So a lookup
returns every member it finds, in the order it finds them, and the caller tries
each.

Each answer carries the derivation that takes the path from the view it
started at to the type found.  So there is no soundness theorem.  The frame
lemma of the tank says that a lookup that ends with the tank unmarked gives the
same answers with more fuel.

The module also holds the walker of the abstract view (`subDecl?`), which
`Sub.mu` needs to compare two recursive types.  It reads the members of one
body off the other and asks a subtyping only where a bound widens to a type
that does not mention the self.  That subtyping is an argument on the tank, so
the walker is framed when its argument is.

Every definition is structural, so the kernel evaluates lookups and walks.  The
checks at the end are `decide +kernel` facts.  They run lookups through a
singleton chain, a deep path, the programs E9, MuS and MuP, an alias cycle, the
term lookup and a run out of fuel.  They run the walker on the bodies of MuS,
MuP and E7, and on bounds whose subtyping the lookup answers through a
singleton.  The last check applies the frame lemma of the walker to the oracle
of the lookup.
-/

namespace PathsFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Ctx Sub PathTy HasTy SelfFree SubDecl)

/-- The cost of a goal at depth `k`.  It grows with the depth, so the fuel
also bounds the depth of a branch, as the stack does in the compiler. -/
def cost (k : Nat) : Nat := k + 1

theorem costOk : CostOk cost := costOk_succ

/-- The fuel every entry point starts from. -/
def defaultFuel : Nat := 2 ^ 15

/-- What a lookup looks for: a type member, a field, a stable field, a
function type, or a singleton. -/
inductive Key where
  | typ (A : Label)
  | fld (a : Label)
  | vfld (a : Label)
  | fn
  | sngl
deriving DecidableEq

/-- The key fits an atom of a type.  A stable field answers a field key,
since `Sub.vfldToFld` reads it as one. -/
def Key.fits {s : Sig} : Key → Ty s → Bool
  | .typ A, .typ B _ _ => decide (A = B)
  | .fld a, .fld b _ => decide (a = b)
  | .fld a, .vfld b _ => decide (a = b)
  | .vfld a, .vfld b _ => decide (a = b)
  | .fn, .all _ _ => true
  | .sngl, .sngl _ => true
  | _, _ => false

/-- A type the path has, reached from the view `V`, with the map that takes
the view's derivation to the derivation at that type. -/
structure FoundP {s : Sig} (Γ : Ctx s) (p : Path s) (V : Ty s) where
  ty : Ty s
  f : PathTy Γ p V → PathTy Γ p ty

/-- A type the path has, with its derivation. -/
structure PV {s : Sig} (Γ : Ctx s) (p : Path s) where
  ty : Ty s
  d : PathTy Γ p ty

/-- A member `A : lo..hi` of a path, with the premise of `Sub.selUpper` and
`Sub.selLower`. -/
structure Mem {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) where
  lo : Ty s
  hi : Ty s
  d : PathTy Γ q (.typ A lo hi)

/-- Read a type member at `A` off a found type. -/
def FoundP.typ? {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} (A : Label) (e : FoundP Γ p V) :
    Option ((lo : Ty s) × (hi : Ty s) × (PathTy Γ p V → PathTy Γ p (.typ A lo hi))) :=
  match h : e.ty with
  | .typ B lo hi => if hB : B = A then some ⟨lo, hi, fun d => hB ▸ h ▸ e.f d⟩ else none
  | _ => none

/-- Read a stable field at `a` off a found type. -/
def FoundP.vfld? {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} (a : Label) (e : FoundP Γ p V) :
    Option ((T : Ty s) × (PathTy Γ p V → PathTy Γ p (.vfld a T))) :=
  match h : e.ty with
  | .vfld b T => if hb : b = a then some ⟨T, fun d => hb ▸ h ▸ e.f d⟩ else none
  | _ => none

/-- Read a singleton off a found type. -/
def FoundP.sngl? {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} (e : FoundP Γ p V) :
    Option ((r : Path s) × (PathTy Γ p V → PathTy Γ p (.sngl r))) :=
  match h : e.ty with
  | .sngl r => some ⟨r, fun d => h ▸ e.f d⟩
  | _ => none

/-- Read a field at `a` off a found type, a stable field through
`Sub.vfldToFld`. -/
def FoundP.fld? {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} (a : Label) (e : FoundP Γ p V) :
    Option ((T : Ty s) × (PathTy Γ p V → PathTy Γ p (.fld a T))) :=
  match h : e.ty with
  | .fld b T => if hb : b = a then some ⟨T, fun d => hb ▸ h ▸ e.f d⟩ else none
  | .vfld b T => if hb : b = a then some ⟨T, fun d => .sub (hb ▸ h ▸ e.f d) .vfldToFld⟩ else none
  | _ => none

/-- A lookup key in full: the path, the view it is searched at, the key. -/
abbrev LKey (s : Sig) := Path s × Ty s × Key

/-- A lookup at one index and one list of pending keys. -/
abbrev Lk {s : Sig} (Γ : Ctx s) := (p : Path s) → (V : Ty s) → Key → Fu (List (FoundP Γ p V))

/-- The declared types of a path (`TermRef.underlying`).  A variable has its
context entry (`PathTy.var`).  `r.a` has every stable field `a` that the lookup
finds on a declared type of `r` (`PathTy.sel`).  The lookup is an argument, so
that the lookup itself can call this function one index down. -/
def startOf {s : Sig} {Γ : Ctx s} (lk : Lk Γ) : (q : Path s) → Fu (List (PV Γ q))
  | .var x => Fu.ret [⟨Γ.lookup x, .var⟩]
  | .sel r a =>
      Fu.bind (startOf lk r) (Fu.flatMapL fun w =>
        Fu.bind (lk r w.ty (.vfld a)) fun es =>
          Fu.ret (es.filterMap fun e => (e.vfld? a).map fun ⟨T, g⟩ => ⟨T, PathTy.sel (g w.d)⟩))
termination_by structural q => q

/-- The type members of a path at a label, from its declared types. -/
def declsAt {s : Sig} {Γ : Ctx s} (lk : Lk Γ) (q : Path s) (A : Label) : Fu (List (Mem Γ q A)) :=
  Fu.bind (startOf lk q) (Fu.flatMapL fun w =>
    Fu.bind (lk q w.ty (.typ A)) fun es =>
      Fu.ret (es.filterMap fun e => (e.typ? A).map fun ⟨lo, hi, g⟩ => ⟨lo, hi, g w.d⟩))

/-- Member lookup at a path, with the cases of `go` in `Types.findMember`.  `μ` is
opened at the path (`goRec`).  Both operands of `∧` are searched, the left one
first (`goAnd`).  A selection continues in the upper bounds of the prefix's
members.  A singleton `q.type` continues at the same path, seen at each
declared type of `q`, as `go` keeps the prefix.  A key that repeats along a
branch has no answer.  `⊥` has no members.  A key costs `cost` of the number of
keys pending.  A short tank answers `[]` and is marked. -/
def lookP {s : Sig} (Γ : Ctx s) : Nat → List (LKey s) → (p : Path s) → (V : Ty s) → Key →
    Fu (List (FoundP Γ p V))
  | 0, _, _, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, p, V, k =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true =>
          if (p, V, k) ∈ P then Fu.ret [] else
          if k.fits V then Fu.ret [⟨V, id⟩] else
          match V with
          | .mu B =>
              if hd : Ty.Decl B then
                Fu.bind (lookP Γ d ((p, .mu B, k) :: P) p (B.substPath p) k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.recE v hd)⟩)
              else Fu.ret []
          | .and V1 V2 =>
              Fu.bind (lookP Γ d ((p, .and V1 V2, k) :: P) p V1 k) fun es1 =>
                Fu.bind (lookP Γ d ((p, .and V1 V2, k) :: P) p V2 k) fun es2 =>
                  Fu.ret (es1.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and1)⟩) ++
                    es2.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and2)⟩))
          | .sel q B =>
              Fu.bind (declsAt (lookP Γ d ((p, .sel q B, k) :: P)) q B) (Fu.flatMapL fun m =>
                Fu.bind (lookP Γ d ((p, .sel q B, k) :: P) p m.hi k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.sub v (.selUpper m.d))⟩))
          | .sngl q =>
              Fu.bind (startOf (lookP Γ d ((p, .sngl q, k) :: P)) q) (Fu.flatMapL fun w =>
                Fu.bind (lookP Γ d ((p, .sngl q, k) :: P) p w.ty k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.snglTrans v w.d)⟩))
          | _ => Fu.ret []
termination_by structural d _ _ _ _ => d

/-- The declared types of a path, from an empty list of pending keys. -/
def startP {s : Sig} (Γ : Ctx s) (d : Nat) (q : Path s) : Fu (List (PV Γ q)) :=
  startOf (lookP Γ d []) q

/-- The type members of a path at a label, from an empty list of pending
keys. -/
def declsP {s : Sig} (Γ : Ctx s) (d : Nat) (q : Path s) (A : Label) : Fu (List (Mem Γ q A)) :=
  declsAt (lookP Γ d []) q A

/-- A type the variable has as a term, reached from the view `V`. -/
structure FoundV {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V : Ty s) where
  ty : Ty s
  f : HasTy Γ (.path x) V → HasTy Γ (.path x) ty

/-- Read a function type off a found type. -/
def FoundV.all? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} (e : FoundV Γ x V) :
    Option ((S : Ty s) × (T : Ty (s,x)) × (HasTy Γ (.path x) V → HasTy Γ (.path x) (.all S T))) :=
  match h : e.ty with
  | .all S T => some ⟨S, T, fun d => h ▸ e.f d⟩
  | _ => none

/-- Member lookup at a variable as a term.  The cases of `lookP` without the
singleton, since `HasTy` has no rule that follows one.  The members of a
selection's prefix come from the path lookup, which continues the same list
of pending keys. -/
def lookV {s : Sig} (Γ : Ctx s) : Nat → List (LKey s) → (x : BVar s .var) → (V : Ty s) → Key →
    Fu (List (FoundV Γ x V))
  | 0, _, _, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, x, V, k =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true =>
          if (.var x, V, k) ∈ P then Fu.ret [] else
          if k.fits V then Fu.ret [⟨V, id⟩] else
          match V with
          | .mu B =>
              if hd : Ty.Decl B then
                Fu.bind (lookV Γ d ((.var x, .mu B, k) :: P) x (B.substVar x) k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.recE v hd)⟩)
              else Fu.ret []
          | .and V1 V2 =>
              Fu.bind (lookV Γ d ((.var x, .and V1 V2, k) :: P) x V1 k) fun es1 =>
                Fu.bind (lookV Γ d ((.var x, .and V1 V2, k) :: P) x V2 k) fun es2 =>
                  Fu.ret (es1.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and1)⟩) ++
                    es2.map (fun e => ⟨e.ty, fun v => e.f (.sub v .and2)⟩))
          | .sel q B =>
              Fu.bind (declsAt (lookP Γ d ((.var x, .sel q B, k) :: P)) q B) (Fu.flatMapL fun m =>
                Fu.bind (lookV Γ d ((.var x, .sel q B, k) :: P) x m.hi k) fun es =>
                  Fu.ret (es.map fun e => ⟨e.ty, fun v => e.f (.sub v (.selUpper m.d))⟩))
          | _ => Fu.ret []
termination_by structural d _ _ _ _ => d

/-! ## The frame lemmas -/

/-- Either branch of a test is framed, so the test is.  The proof takes the
`Decidable` instance apart, so it needs no choice. -/
theorem ite_framed {α : Type} {c : Prop} [hc : Decidable c] {a b : Fu α} (ha : Framed a)
    (hb : Framed b) : Framed (if c then a else b) := by
  cases hc
  · exact hb
  · exact ha

/-- The dependent test, as `ite_framed`. -/
theorem dite_framed {α : Type} {c : Prop} [hc : Decidable c] {a : c → Fu α} {b : ¬c → Fu α}
    (ha : ∀ h, Framed (a h)) (hb : ∀ h, Framed (b h)) : Framed (if h : c then a h else b h) := by
  cases hc with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-- At index zero a lookup marks the tank and answers `[]`. -/
theorem nil_framed (β : Type) : Framed (fun t : Tank => (([] : List β), { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

/-- The declared types of a path are framed when the lookup they call is. -/
theorem startOf_framed {s : Sig} {Γ : Ctx s} {lk : Lk Γ} (hlk : ∀ p V k, Framed (lk p V k)) :
    ∀ q, Framed (startOf lk q)
  | .var _ => ret_framed _
  | .sel r _ =>
    bind_framed (startOf_framed hlk r) (flatMapL_framed fun _ =>
      bind_framed (hlk _ _ _) fun _ => ret_framed _)

/-- The members of a path are framed when the lookup they call is. -/
theorem declsAt_framed {s : Sig} {Γ : Ctx s} {lk : Lk Γ} (hlk : ∀ p V k, Framed (lk p V k))
    (q : Path s) (A : Label) : Framed (declsAt lk q A) :=
  bind_framed (startOf_framed hlk q) (flatMapL_framed fun _ =>
    bind_framed (hlk _ _ _) fun _ => ret_framed _)

/-- Every path lookup is framed: it keeps a marked tank, never adds fuel, and
does the same with more fuel. -/
theorem lookP_framed {s : Sig} (Γ : Ctx s) (d : Nat) :
    ∀ (P : List (LKey s)) (p : Path s) (V : Ty s) (k : Key), Framed (lookP Γ d P p V k) := by
  induction d with
  | zero =>
    intro P p V k
    exact nil_framed (FoundP Γ p V)
  | succ d ih =>
    intro P p V k
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
      | sel q B =>
        exact bind_framed (declsAt_framed (ih _) _ _) (flatMapL_framed fun _ =>
          bind_framed (ih _ _ _ _) fun _ => ret_framed _)
      | sngl q =>
        exact bind_framed (startOf_framed (ih _) _) (flatMapL_framed fun _ =>
          bind_framed (ih _ _ _ _) fun _ => ret_framed _)
      | top => exact ret_framed _
      | bot => exact ret_framed _
      | typ _ _ _ => exact ret_framed _
      | fld _ _ => exact ret_framed _
      | vfld _ _ => exact ret_framed _
      | all _ _ => exact ret_framed _

theorem lookP_frame {s : Sig} {Γ : Ctx s} {d : Nat} {P : List (LKey s)} {p : Path s} {V : Ty s}
    {k : Key} {t t' : Tank} {es : List (FoundP Γ p V)} (h : lookP Γ d P p V k t = (es, t'))
    (ho : t'.out = false) (j : Nat) :
    lookP Γ d P p V k (t.add j) = (es, t'.add j) :=
  (lookP_framed Γ d P p V k).shift t es t' h ho j

/-- A path lookup from a marked tank answers `[]` and leaves the tank as it
is. -/
theorem lookP_absorbs {s : Sig} (Γ : Ctx s) (d : Nat) (P : List (LKey s)) (p : Path s) (V : Ty s)
    (k : Key) {t : Tank} (h : t.out = true) : lookP Γ d P p V k t = ([], t) := by
  cases d with
  | zero => cases t; simp_all [lookP]
  | succ d =>
    change Fu.bind (draw (cost P.length)) _ t = _
    simp only [Fu.bind, draw_out h]
    rfl

theorem startP_framed {s : Sig} (Γ : Ctx s) (d : Nat) (q : Path s) : Framed (startP Γ d q) :=
  startOf_framed (lookP_framed Γ d []) q

theorem startP_frame {s : Sig} {Γ : Ctx s} {d : Nat} {q : Path s} {t t' : Tank}
    {ws : List (PV Γ q)} (h : startP Γ d q t = (ws, t')) (ho : t'.out = false) (j : Nat) :
    startP Γ d q (t.add j) = (ws, t'.add j) :=
  (startP_framed Γ d q).shift t ws t' h ho j

theorem declsP_framed {s : Sig} (Γ : Ctx s) (d : Nat) (q : Path s) (A : Label) :
    Framed (declsP Γ d q A) :=
  declsAt_framed (lookP_framed Γ d []) q A

theorem declsP_frame {s : Sig} {Γ : Ctx s} {d : Nat} {q : Path s} {A : Label} {t t' : Tank}
    {ms : List (Mem Γ q A)} (h : declsP Γ d q A t = (ms, t')) (ho : t'.out = false) (j : Nat) :
    declsP Γ d q A (t.add j) = (ms, t'.add j) :=
  (declsP_framed Γ d q A).shift t ms t' h ho j

/-- Every term lookup is framed. -/
theorem lookV_framed {s : Sig} (Γ : Ctx s) (d : Nat) :
    ∀ (P : List (LKey s)) (x : BVar s .var) (V : Ty s) (k : Key), Framed (lookV Γ d P x V k) := by
  induction d with
  | zero =>
    intro P x V k
    exact nil_framed (FoundV Γ x V)
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
      | sel q B =>
        exact bind_framed (declsAt_framed (lookP_framed Γ d _) _ _) (flatMapL_framed fun _ =>
          bind_framed (ih _ _ _ _) fun _ => ret_framed _)
      | sngl _ => exact ret_framed _
      | top => exact ret_framed _
      | bot => exact ret_framed _
      | typ _ _ _ => exact ret_framed _
      | fld _ _ => exact ret_framed _
      | vfld _ _ => exact ret_framed _
      | all _ _ => exact ret_framed _

theorem lookV_frame {s : Sig} {Γ : Ctx s} {d : Nat} {P : List (LKey s)} {x : BVar s .var}
    {V : Ty s} {k : Key} {t t' : Tank} {es : List (FoundV Γ x V)}
    (h : lookV Γ d P x V k t = (es, t')) (ho : t'.out = false) (j : Nat) :
    lookV Γ d P x V k (t.add j) = (es, t'.add j) :=
  (lookV_framed Γ d P x V k).shift t es t' h ho j

/-- A term lookup from a marked tank answers `[]` and leaves the tank as it
is. -/
theorem lookV_absorbs {s : Sig} (Γ : Ctx s) (d : Nat) (P : List (LKey s)) (x : BVar s .var)
    (V : Ty s) (k : Key) {t : Tank} (h : t.out = true) : lookV Γ d P x V k t = ([], t) := by
  cases d with
  | zero => cases t; simp_all [lookV]
  | succ d =>
    change Fu.bind (draw (cost P.length)) _ t = _
    simp only [Fu.bind, draw_out h]
    rfl

/-! ## The abstract view of a declaration

`Sub.mu` relates two recursive types through `SubDecl Γ L R`.  The body `L`
has every member that the body `R` declares, each widened by a self-free step.
The walker below searches for that view.  It asks a subtyping only at the step
`SelfFree.closed`, whose two sides do not mention the self.  The subtyping is
an argument on the tank, so the search that calls the walker hands it its own
oracle, and the walker spends what the oracle spends.

In `TypeComparer.thirdTry`, `compareRec` compares the two parents with the self
identified.  The calculus relates less, and the walker follows the calculus.

The bodies have type `Ty (s,x)`.  Structural recursion does not apply to a type
whose index is not a variable.  So the descent through the intersections of `R`
runs on the index `andDepth R`. -/

/-- A subtyping search on the tank, the argument of the walker. -/
abbrev SubO {s : Sig} (Γ : Ctx s) := (S T : Ty s) → Fu (Option (Sub Γ S T))

/-- Run `c`, and on a success run `f` on its value.  A failure answers `none`
and asks nothing more. -/
def bindO {α β : Type} (c : Fu (Option α)) (f : α → Fu (Option β)) : Fu (Option β) :=
  Fu.bind c fun
    | none => Fu.ret none
    | some a => f a

/-- A self-free step from `X` to `Y`.  The syntactic rules come first: `refl`
at equal sides, `bot` at a lower side `⊥`, `top` at an upper side `⊤`.  Then
`closed`: both sides are strengthened to the outer context, and `sub` is asked
for the subtyping between them.  It is `selfFree?` of `Decide.lean` with the
subtyping on the tank. -/
def selfFree? {s : Sig} {Γ : Ctx s} (sub : SubO Γ) (X Y : Ty (s,x)) :
    Fu (Option (SelfFree Γ X Y)) :=
  if h : X = Y then Fu.ret (some (h ▸ .refl))
  else if hb : X = .bot then Fu.ret (some (hb ▸ .bot))
  else if ht : Y = .top then Fu.ret (some (ht ▸ .top))
  else
    match tyStrengthenW? X, tyStrengthenW? Y with
    | some ⟨X', hX⟩, some ⟨Y', hY⟩ =>
        Fu.bind (sub X' Y') fun r => Fu.ret (r.map (selfFreeClosedOf hX hY))
    | _, _ => Fu.ret none

/-- The nesting depth of intersections in a type. -/
def andDepth {s : Sig} : Ty s → Nat
  | .and S T => max (andDepth S) (andDepth T) + 1
  | _ => 0
termination_by structural T => T

/-- The abstract view at one member of `R`, not an intersection.  Each member
is looked up in `L`.  A plain field of `R` is matched by a plain field of `L`
first, then by a stable field. -/
def subDeclLeaf? {s : Sig} {Γ : Ctx s} (sub : SubO Γ) (L : Ty (s,x)) :
    (R : Ty (s,x)) → Fu (Option (SubDecl Γ L R))
  | .top => Fu.ret (some .top)
  | .typ A S2 T2 =>
      match h : L.lookupTypDecl A with
      | some (S1, T1) =>
          bindO (selfFree? sub S2 S1) fun e1 =>
            bindO (selfFree? sub T1 T2) fun e2 => Fu.ret (some (.typ h e1 e2))
      | none => Fu.ret none
  | .fld a T2 =>
      Fu.orElse
        (match h : L.lookupFldDecl a with
         | some T1 => bindO (selfFree? sub T1 T2) fun e => Fu.ret (some (.fld h e))
         | none => Fu.ret none)
        fun _ =>
          match h : L.lookupVfldDecl a with
          | some T1 => bindO (selfFree? sub T1 T2) fun e => Fu.ret (some (.vfldToFld h e))
          | none => Fu.ret none
  | .vfld a T2 =>
      match h : L.lookupVfldDecl a with
      | some T1 => bindO (selfFree? sub T1 T2) fun e => Fu.ret (some (.vfld h e))
      | none => Fu.ret none
  | _ => Fu.ret none

/-- The abstract view, descending at most `n` intersections of `R`, the left
operand first. -/
def subDeclAt {s : Sig} {Γ : Ctx s} (sub : SubO Γ) (L : Ty (s,x)) :
    Nat → (R : Ty (s,x)) → Fu (Option (SubDecl Γ L R))
  | n + 1, .and R1 R2 =>
      bindO (subDeclAt sub L n R1) fun e1 =>
        bindO (subDeclAt sub L n R2) fun e2 => Fu.ret (some (.and e1 e2))
  | _, R => subDeclLeaf? sub L R
termination_by structural n => n

/-- Search the abstract view of `L` at `R`, with `sub` answering the subtyping
that a self-free step needs. -/
def subDecl? {s : Sig} {Γ : Ctx s} (sub : SubO Γ) (L R : Ty (s,x)) :
    Fu (Option (SubDecl Γ L R)) :=
  subDeclAt sub L (andDepth R) R

/-! ## The walker on the tank

The walker is framed when its oracle is.  Two oracles that agree give walkers
that agree, and two oracles that dominate give walkers that dominate.  The
step of a search in `Sub.lean` needs these facts.  The index of the descent
changes nothing once it reaches the depth of `R`. -/

theorem bindO_agree {α β : Type} {c c' : Fu (Option α)} {f f' : α → Fu (Option β)}
    (hc : Agree c c') (hf : ∀ a, Agree (f a) (f' a)) : Agree (bindO c f) (bindO c' f') :=
  bind_agree hc fun r => by
    cases r
    · exact ret_agree _
    · exact hf _

theorem bindO_framed {α β : Type} {c : Fu (Option α)} {f : α → Fu (Option β)}
    (hc : Framed c) (hf : ∀ a, Framed (f a)) : Framed (bindO c f) :=
  bind_framed hc fun r => by
    cases r
    · exact ret_framed _
    · exact hf _

theorem bindO_dom {α β : Type} {m : Nat} {c c' : Fu (Option α)} {f f' : α → Fu (Option β)}
    (hc : Framed c) (hf : ∀ a, Framed (f a)) (hd : Dom m c c')
    (hfd : ∀ a, Dom m (f a) (f' a)) : Dom m (bindO c f) (bindO c' f') :=
  bind_dom hc
    (fun r => by
      cases r
      · exact ret_framed _
      · exact hf _)
    hd fun r => by
      cases r
      · exact ret_dom _ m
      · exact hfd _

section Walker

variable {s : Sig} {Γ : Ctx s}

theorem selfFree?_agree {o o' : SubO Γ} (ho : ∀ S T, Agree (o S T) (o' S T))
    (X Y : Ty (s,x)) : Agree (selfFree? o X Y) (selfFree? o' X Y) := by
  unfold selfFree?
  split
  · exact ret_agree _
  · split
    · exact ret_agree _
    · split
      · exact ret_agree _
      · split
        · exact bind_agree (ho _ _) fun _ => ret_agree _
        · exact ret_agree _

theorem selfFree?_framed {o : SubO Γ} (ho : ∀ S T, Framed (o S T)) (X Y : Ty (s,x)) :
    Framed (selfFree? o X Y) :=
  (selfFree?_agree (fun S T => Agree.refl (ho S T)) X Y).left

theorem selfFree?_dom {m : Nat} {o o' : SubO Γ} (ho : ∀ S T, Framed (o S T))
    (hd : ∀ S T, Dom m (o S T) (o' S T)) (X Y : Ty (s,x)) :
    Dom m (selfFree? o X Y) (selfFree? o' X Y) := by
  unfold selfFree?
  split
  · exact ret_dom _ m
  · split
    · exact ret_dom _ m
    · split
      · exact ret_dom _ m
      · split
        · exact bind_dom (ho _ _) (fun _ => ret_framed _) (hd _ _) fun _ => ret_dom _ m
        · exact ret_dom _ m

theorem subDeclLeaf?_agree {o o' : SubO Γ} (ho : ∀ S T, Agree (o S T) (o' S T))
    (L R : Ty (s,x)) : Agree (subDeclLeaf? o L R) (subDeclLeaf? o' L R) := by
  have hsf := selfFree?_agree ho
  cases R with
  | typ A S2 T2 =>
    simp only [subDeclLeaf?]
    split
    · exact bindO_agree (hsf _ _) fun _ => bindO_agree (hsf _ _) fun _ => ret_agree _
    · exact ret_agree _
  | fld a T2 =>
    simp only [subDeclLeaf?]
    apply orElse_agree
    · split
      · exact bindO_agree (hsf _ _) fun _ => ret_agree _
      · exact ret_agree _
    · split
      · exact bindO_agree (hsf _ _) fun _ => ret_agree _
      · exact ret_agree _
  | vfld a T2 =>
    simp only [subDeclLeaf?]
    split
    · exact bindO_agree (hsf _ _) fun _ => ret_agree _
    · exact ret_agree _
  | _ => simp only [subDeclLeaf?]; exact ret_agree _

theorem subDeclLeaf?_framed {o : SubO Γ} (ho : ∀ S T, Framed (o S T)) (L R : Ty (s,x)) :
    Framed (subDeclLeaf? o L R) :=
  (subDeclLeaf?_agree (fun S T => Agree.refl (ho S T)) L R).left

theorem subDeclLeaf?_dom {m : Nat} {o o' : SubO Γ} (ho : ∀ S T, Framed (o S T))
    (hd : ∀ S T, Dom m (o S T) (o' S T)) (L R : Ty (s,x)) :
    Dom m (subDeclLeaf? o L R) (subDeclLeaf? o' L R) := by
  have hf := selfFree?_framed ho
  have hsd := selfFree?_dom ho hd
  cases R with
  | typ A S2 T2 =>
    simp only [subDeclLeaf?]
    split
    · exact bindO_dom (hf _ _) (fun _ => bindO_framed (hf _ _) fun _ => ret_framed _) (hsd _ _)
        fun _ => bindO_dom (hf _ _) (fun _ => ret_framed _) (hsd _ _) fun _ => ret_dom _ m
    · exact ret_dom _ m
  | fld a T2 =>
    simp only [subDeclLeaf?]
    apply orElse_dom
    · split
      · exact bindO_framed (hf _ _) fun _ => ret_framed _
      · exact ret_framed _
    · split
      · exact bindO_dom (hf _ _) (fun _ => ret_framed _) (hsd _ _) fun _ => ret_dom _ m
      · exact ret_dom _ m
    · split
      · exact bindO_dom (hf _ _) (fun _ => ret_framed _) (hsd _ _) fun _ => ret_dom _ m
      · exact ret_dom _ m
  | vfld a T2 =>
    simp only [subDeclLeaf?]
    split
    · exact bindO_dom (hf _ _) (fun _ => ret_framed _) (hsd _ _) fun _ => ret_dom _ m
    · exact ret_dom _ m
  | _ => simp only [subDeclLeaf?]; exact ret_dom _ m

/-- Off an intersection the walker reads the leaf, at every index. -/
theorem subDeclAt_leaf {o : SubO Γ} {L R : Ty (s,x)} (hR : ∀ R1 R2, R ≠ .and R1 R2)
    (n : Nat) : subDeclAt o L n R = subDeclLeaf? o L R := by
  cases n with
  | zero => simp only [subDeclAt]
  | succ n =>
    cases R with
    | and R1 R2 => exact absurd rfl (hR R1 R2)
    | _ => simp only [subDeclAt]

theorem subDeclAt_agree {o o' : SubO Γ} (ho : ∀ S T, Agree (o S T) (o' S T)) (L : Ty (s,x)) :
    ∀ (n : Nat) (R : Ty (s,x)), Agree (subDeclAt o L n R) (subDeclAt o' L n R) := by
  intro n
  induction n with
  | zero => intro R; simp only [subDeclAt]; exact subDeclLeaf?_agree ho L R
  | succ n ih =>
    intro R
    cases R with
    | and R1 R2 =>
      simp only [subDeclAt]
      exact bindO_agree (ih R1) fun _ => bindO_agree (ih R2) fun _ => ret_agree _
    | _ => simp only [subDeclAt]; exact subDeclLeaf?_agree ho L _

theorem subDeclAt_framed {o : SubO Γ} (ho : ∀ S T, Framed (o S T)) (L : Ty (s,x)) (n : Nat)
    (R : Ty (s,x)) : Framed (subDeclAt o L n R) :=
  (subDeclAt_agree (fun S T => Agree.refl (ho S T)) L n R).left

theorem subDeclAt_dom {m : Nat} {o o' : SubO Γ} (ho : ∀ S T, Framed (o S T))
    (hd : ∀ S T, Dom m (o S T) (o' S T)) (L : Ty (s,x)) :
    ∀ (n : Nat) (R : Ty (s,x)), Dom m (subDeclAt o L n R) (subDeclAt o' L n R) := by
  intro n
  induction n with
  | zero => intro R; simp only [subDeclAt]; exact subDeclLeaf?_dom ho hd L R
  | succ n ih =>
    intro R
    cases R with
    | and R1 R2 =>
      simp only [subDeclAt]
      exact bindO_dom (subDeclAt_framed ho L n R1)
        (fun _ => bindO_framed (subDeclAt_framed ho L n R2) fun _ => ret_framed _) (ih R1)
        fun _ => bindO_dom (subDeclAt_framed ho L n R2) (fun _ => ret_framed _) (ih R2)
          fun _ => ret_dom _ m
    | _ => simp only [subDeclAt]; exact subDeclLeaf?_dom ho hd L _

theorem subDecl?_agree {o o' : SubO Γ} (ho : ∀ S T, Agree (o S T) (o' S T)) (L R : Ty (s,x)) :
    Agree (subDecl? o L R) (subDecl? o' L R) :=
  subDeclAt_agree ho L _ R

theorem subDecl?_framed {o : SubO Γ} (ho : ∀ S T, Framed (o S T)) (L R : Ty (s,x)) :
    Framed (subDecl? o L R) :=
  subDeclAt_framed ho L _ R

theorem subDecl?_dom {m : Nat} {o o' : SubO Γ} (ho : ∀ S T, Framed (o S T))
    (hd : ∀ S T, Dom m (o S T) (o' S T)) (L R : Ty (s,x)) :
    Dom m (subDecl? o L R) (subDecl? o' L R) :=
  subDeclAt_dom ho hd L _ R

/-- Two indices at or above the depth of `R` give the same walker. -/
theorem subDeclAt_depth {o : SubO Γ} {L : Ty (s,x)} :
    ∀ (d : Nat) (R : Ty (s,x)), andDepth R ≤ d → ∀ j k, andDepth R ≤ j → andDepth R ≤ k →
      subDeclAt o L j R = subDeclAt o L k R := by
  intro d
  induction d with
  | zero =>
    intro R hR j k _ _
    have hR' : ∀ R1 R2, R ≠ .and R1 R2 := by
      intro R1 R2 h
      subst h
      exact absurd hR (Nat.not_succ_le_zero _)
    rw [subDeclAt_leaf hR', subDeclAt_leaf hR']
  | succ d ih =>
    intro R hR j k hj hk
    cases R with
    | and R1 R2 =>
      have h1 : andDepth R1 ≤ max (andDepth R1) (andDepth R2) := Nat.le_max_left _ _
      have h2 : andDepth R2 ≤ max (andDepth R1) (andDepth R2) := Nat.le_max_right _ _
      have hR : max (andDepth R1) (andDepth R2) ≤ d := Nat.le_of_succ_le_succ hR
      cases j with
      | zero => exact absurd hj (Nat.not_succ_le_zero _)
      | succ j =>
      cases k with
      | zero => exact absurd hk (Nat.not_succ_le_zero _)
      | succ k =>
      have hj : max (andDepth R1) (andDepth R2) ≤ j := Nat.le_of_succ_le_succ hj
      have hk : max (andDepth R1) (andDepth R2) ≤ k := Nat.le_of_succ_le_succ hk
      simp only [subDeclAt]
      rw [ih R1 (Nat.le_trans h1 hR) j k (Nat.le_trans h1 hj) (Nat.le_trans h1 hk),
        ih R2 (Nat.le_trans h2 hR) j k (Nat.le_trans h2 hj) (Nat.le_trans h2 hk)]
    | _ =>
      rw [subDeclAt_leaf (fun _ _ h => by cases h), subDeclAt_leaf (fun _ _ h => by cases h)]

/-- At any index from the depth of `R` on, the walker is `subDecl?`. -/
theorem subDeclAt_eq {o : SubO Γ} {L R : Ty (s,x)} {k : Nat} (hk : andDepth R ≤ k) :
    subDeclAt o L k R = subDecl? o L R :=
  subDeclAt_depth _ R (Nat.le_refl _) k _ hk (Nat.le_refl _)

end Walker

/-! ## Checks

Each check runs in the kernel at the default fuel, from a full tank.
`aliasCtx 6` reaches a member through six singletons.  `deepTy 6` puts a member
six stable fields down.  `MuSCtx` has a singleton to a recursive type, whose
member must be opened at the singleton's path.  `E7Ctx` is an alias cycle.
The walker runs on the bodies of MuS, MuP and E7 with no oracle, and in
`MuSCtx` and `aliasCtx 6` with the oracle `memSub`, which answers a selection
below a member's upper bound from the lookup. -/

section LookChecks

open Paths.DotMNF.Examples

/-- The members of `q` at `A` as pairs of bounds, and the tank left. -/
def declsAtFuel {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) (n : Nat := defaultFuel) :
    List (Ty s × Ty s) × Tank :=
  let r := declsP Γ n q A ⟨n, false⟩
  (r.1.map fun m => (m.lo, m.hi), r.2)

/-- The types a path has that fit a key, from its declared types, and the tank
left. -/
def lookPAt {s : Sig} (Γ : Ctx s) (q : Path s) (k : Key) (n : Nat := defaultFuel) :
    List (Ty s) × Tank :=
  Fu.bind (startP Γ n q) (Fu.flatMapL fun w =>
    Fu.bind (lookP Γ n [] q w.ty k) fun es => Fu.ret (es.map (·.ty))) ⟨n, false⟩

/-- A signature of `k` variables. -/
def sigN : Nat → Sig
  | 0 => []
  | n + 1 => Sig.extend (sigN n) .var

/-- `x : {A : ⊥..{a : ⊤}}`, then `y1 : x.type`, …, `yk : y(k-1).type`. -/
def aliasCtx : (k : Nat) → Ctx (sigN (k + 1))
  | 0 => Ctx.nil.cons (.typ lA .bot (.fld la .top))
  | k + 1 => (aliasCtx k).cons (.sngl (.var .here))

/-- `{val b : … {val b : {A : ⊥..{a : ⊤}}}}`, `k` stable fields deep. -/
def deepTy {s : Sig} : Nat → Ty s
  | 0 => .typ lA .bot (.fld la .top)
  | k + 1 => .vfld lb (deepTy k)

/-- `x.b.b…b`, `k` steps. -/
def deepPath {s : Sig} (x : BVar s .var) : Nat → Path s
  | 0 => .var x
  | k + 1 => .sel (deepPath x k) lb

/-- `q : μ(s. {A : ⊥ .. {B : s.C .. s.C}} ∧ {C : ⊥ .. ⊤})`, `p : q.type`. -/
def MuSCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.mu (.and (.typ lA .bot (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC)))
    (.typ lC .bot .top)))).cons (.sngl (.var .here))

/-- `q : μ(s. {A : ⊥ .. ⊤} ∧ {a : s.A})`, `p : q.type`. -/
def MuPCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.mu (.and (.typ lA .bot .top) (.fld la (.sel (.var .here) lA))))).cons
    (.sngl (.var .here))

/-- `x : μ(x. {A = x.B} ∧ {B = x.A})`. -/
def E7Ctx : Ctx ([],x) := .cons .nil (.mu E7Self)

-- The member `A` of `y6`, read through six singletons.
example : (declsAtFuel (aliasCtx 6) (.var .here) lA).1 = [(.bot, .fld la .top)] := by
  decide +kernel
example : (declsAtFuel (aliasCtx 6) (.var .here) lA).2.out = false := by decide +kernel
-- The member `A` of `x.b.b.b.b.b.b`, six stable fields down.
example : (declsAtFuel (Ctx.nil.cons (deepTy 6)) (deepPath .here 6) lA).1 =
    [(.bot, .fld la .top)] := by decide +kernel
example : (declsAtFuel (Ctx.nil.cons (deepTy 6)) (deepPath .here 6) lA).2.out = false := by
  decide +kernel
-- E9: `y : q.type`, the member `B = {b : ⊤}` of `q` read at `y`.
example : (declsAtFuel E9_Γ3 (.var .here) lB).1 = [(E9_N, E9_N)] := by decide +kernel
example : (declsAtFuel E9_Γ3 (.var .here) lB).2.out = false := by decide +kernel
-- MuS: the member `A` of `p`, with `q`'s self type opened at `p`, so its upper bound is
-- `{B : p.C .. p.C}` and not `{B : q.C .. q.C}`.
example : (declsAtFuel MuSCtx (.var .here) lA).1 =
    [(.bot, .typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))] := by decide +kernel
example : (declsAtFuel MuSCtx (.var .here) lA).2.out = false := by decide +kernel
-- MuP: the field `a` of `p` at `p.A`, opened at `p`.
example : (lookPAt MuPCtx (.var .here) (.fld la)).1 = [.fld la (.sel (.var .here) lA)] := by
  decide +kernel
-- The path `y6` has the singleton it is declared at, and through it `x`'s member.
example : (lookPAt (aliasCtx 6) (.var .here) .sngl).1 = [.sngl (.var (.there .here))] := by
  decide +kernel
-- The declared types of `x.b.b.b.b.b.b`: one, the member `A`.
example : ((startP (Ctx.nil.cons (deepTy 6)) defaultFuel (deepPath .here 6)
    ⟨defaultFuel, false⟩).1.map (·.ty)) = [deepTy 0] := by decide +kernel
-- E7: the field `a` through the alias cycle `x.A = x.B`, `x.B = x.A`.  The key repeats, so there
-- is no answer, and the tank stays unmarked.
example : (lookP E7Ctx defaultFuel [] (.var .here) (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
example : (lookP E7Ctx defaultFuel [] (.var .here) (.sel (.var .here) lA) (.fld la)
    ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
-- The term lookup does not follow a singleton: `y6` as a term has no member `A`.
example : (lookV (aliasCtx 6) defaultFuel [] .here (.sngl (.var (.there .here))) (.typ lA)
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
-- The term lookup opens `μ` at the variable: `p` of MuP, seen at `q`'s self type.
example : ((lookV MuPCtx defaultFuel [] .here
    (.mu (.and (.typ lA .bot .top) (.fld la (.sel (.var .here) lA)))) (.fld la)
    ⟨defaultFuel, false⟩).1.map (·.ty)) = [.fld la (.sel (.var .here) lA)] := by decide +kernel
-- A lookup at fuel 1 runs out on the singleton chain.
example : (declsAtFuel (aliasCtx 6) (.var .here) lA 1).2.out = true := by decide +kernel

/-- An oracle that answers no subtyping. -/
def noSub {s : Sig} {Γ : Ctx s} : SubO Γ := fun _ _ => Fu.ret none

/-- An oracle from the lookup: a selection `q.A` is below the upper bound of each
member of `q` at `A`, by `Sub.selUpper`.  Each question draws one unit. -/
def memSub {s : Sig} (Γ : Ctx s) (n : Nat := defaultFuel) : SubO Γ := fun S T =>
  Fu.bind (draw 1) fun
    | false => Fu.ret none
    | true =>
      match S with
      | .sel q A =>
          Fu.bind (declsP Γ n q A) fun ms =>
            Fu.ret (ms.findSome? fun m => if h : m.hi = T then some (h ▸ .selUpper m.d) else none)
      | _ => Fu.ret none

theorem memSub_framed {s : Sig} (Γ : Ctx s) (n : Nat) (S T : Ty s) : Framed (memSub Γ n S T) := by
  apply bind_framed (draw_framed 1)
  intro ok
  cases ok
  · exact ret_framed _
  · cases S with
    | sel q A => exact bind_framed (declsP_framed Γ n q A) fun _ => ret_framed _
    | _ => exact ret_framed _

/-- Whether the walker finds the view of `L` at `R`, and the tank left. -/
def subDeclFuel {s : Sig} {Γ : Ctx s} (o : SubO Γ) (L R : Ty (s,x)) (n : Nat := defaultFuel) :
    Bool × Tank :=
  let r := subDecl? o L R ⟨n, false⟩
  (r.1.isSome, r.2)

/-- MuS's body `{A : ⊥ .. {B : s.C .. s.C}} ∧ {C : ⊥ .. ⊤}`. -/
def MuSBody : Ty ([],x) :=
  .and (.typ lA .bot (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))) (.typ lC .bot .top)

/-- MuP's body `{A : ⊥ .. ⊤} ∧ {a : s.A}`. -/
def MuPBody : Ty ([],x) := .and (.typ lA .bot .top) (.fld la (.sel (.var .here) lA))

/-- `{T : ⊥ .. U}` under a self binder, with `U` written in the outer context. -/
def memberT {s : Sig} (U : Ty s) : Ty (s,x) := .typ lT .bot U.weaken

-- MuS's body against itself, and against a weaker body in the other order.  Each step is
-- syntactic, so no oracle is asked and the tank stays full.
example : subDeclFuel (Γ := .nil) noSub MuSBody MuSBody = (true, ⟨defaultFuel, false⟩) := by
  decide +kernel
example : subDeclFuel (Γ := .nil) noSub MuSBody
    (.and (.typ lC .bot .top) (.typ lA .bot .top)) = (true, ⟨defaultFuel, false⟩) := by
  decide +kernel
-- The upper bound `{B : s.C .. s.C}` mentions the self, so it is not below `⊥`.
example : (subDeclFuel (Γ := .nil) noSub MuSBody (.typ lA .bot .bot)).1 = false := by
  decide +kernel
-- MuP's body: the field `a` at `s.A`, and at `⊤`, beside the member `A`.
example : (subDeclFuel (Γ := .nil) noSub MuPBody (.fld la (.sel (.var .here) lA))).1 = true := by
  decide +kernel
example : (subDeclFuel (Γ := .nil) noSub MuPBody (.and (.fld la .top) (.typ lA .bot .top))).1 =
    true := by decide +kernel
-- A stable field answers a plain field.
example : (subDeclFuel (Γ := .nil) noSub (.vfld lb .top) (.fld lb .top)).1 = true := by
  decide +kernel
-- E7's body against itself, the alias cycle of its bounds left alone.
example : (subDeclFuel (Γ := .nil) noSub E7Self E7Self).1 = true := by decide +kernel
-- In MuS's context, `{T : ⊥ .. p.A}` against `{T : ⊥ .. {B : p.C .. p.C}}`.  The upper bounds
-- do not mention the self, so the oracle is asked `p.A <: {B : p.C .. p.C}`.  It finds the
-- member `A` of `p` opened at `p`, by the lookup.
example : subDeclFuel (memSub MuSCtx) (memberT (.sel (.var .here) lA))
    (memberT (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))) =
    (true, ⟨defaultFuel - 15, false⟩) := by decide +kernel
-- The same against `{B : q.C .. q.C}` fails: the member is not opened at `q`.
example : (subDeclFuel (memSub MuSCtx) (memberT (.sel (.var .here) lA))
    (memberT (.typ lB (.sel (.var (.there .here)) lC) (.sel (.var (.there .here)) lC)))).1 =
    false := by decide +kernel
-- Without the oracle the closed step fails.
example : (subDeclFuel noSub (Γ := MuSCtx) (memberT (.sel (.var .here) lA))
    (memberT (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC)))).1 = false := by
  decide +kernel
-- Six singletons down, `{T : ⊥ .. y6.A}` against `{T : ⊥ .. {a : ⊤}}`.
example : (subDeclFuel (memSub (aliasCtx 6)) (memberT (.sel (.var .here) lA))
    (memberT (.fld la .top))).1 = true := by decide +kernel
-- An empty tank: the oracle marks it, and the walker answers nothing.
example : subDeclFuel (memSub MuSCtx) (memberT (.sel (.var .here) lA))
    (memberT (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))) 0 =
    (false, ⟨0, true⟩) := by decide +kernel
-- The lookup oracle is framed, so the walker on it is.
example (L R : Ty ([],x,x,x)) : Framed (subDecl? (memSub MuSCtx) L R) :=
  subDecl?_framed (memSub_framed MuSCtx defaultFuel) L R

end LookChecks

end PathsFrontend.Core
