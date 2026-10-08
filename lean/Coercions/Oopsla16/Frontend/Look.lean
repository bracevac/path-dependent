import Coercions.Frontend.Fuel
import Coercions.Oopsla16.Frontend.Decide

/-!
# Member lookup on the tank

The lookup asks which types carry a given member.  It follows the compiler's
`findMember` (`Types.scala:820-870`).  There are two queries.

* `h s Γ x V k` asks for the types the variable `x`, seen at `V`, has at the
  key `k`, each with an `Oopsla16.Htp` step.  `Htp` types `x` in its own
  prefix, the context cut off at `x`, and has no packing rule.  A recursive
  type is opened at `x` by `htp_unpack` (`goRec`, `Types.scala:875-896`).
  Both operands of an intersection are searched (`goAnd`,
  `Types.scala:994-995`).  A selection `y.L` asks the members of `y` in the
  prefix of `x`, as `htp_sub` demands, and goes on in their upper bounds by
  `stp_sel1` (`Types.scala:5720`).
* `st s Γ V k` asks for the types `V` is below at the key, each with an
  `Oopsla16.Stp` step.  It serves a receiver that is not a variable, where no
  opening is possible.  It searches intersections and selections as `h` does.

An atom that fits the key is an answer.  `⊥` has no members
(`Types.scala:827-829`).  A union has none either.  The compiler looks a
member up in the join of a union, and the join of two structural types keeps
no member (`TypeOps.scala:383-389`).  The compiler merges two members of one
name (`Types.scala:5759`).  Oopsla16 has no rule for that merge, so the lookup
returns every member it finds, in the order it finds them, and the caller
tries each.

The lookup draws on the tank of `Fuel.lean`.  A query costs `cost` of the
number of queries pending along the branch.  A query that repeats along a
branch has no answer, which is the compiler's cyclic reference.  The pending
list holds keys, not queries.  The key of an `h` query keeps only the prefix
of `x`, its type there and the key.  An `Htp` derivation depends on nothing
else, so two queries with one key ask the same question, whatever binders
follow `x`.  So a lookup has one answer at every binder depth.

Each answer carries the derivation that takes the query's start to the type
found.  So the lookup has no soundness theorem to prove.  What it has is the
frame lemma of the tank: a lookup that ends with the tank unmarked gives the
same answers with more fuel.  `hdecls` reads the type members of a variable
off its recorded type, each with the premise that `stp_sel1` and `stp_sel2`
ask for after `lowerBot` or `upperTop`.

Every definition is structural, so the kernel evaluates a lookup.  The checks
at the end of the module run lookups by `decide +kernel`.
-/

namespace Oopsla16Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Ctx Store Stp Htp HasType scopeUpTo renameUpTo varUpTo)

-- Contexts are compared in the pending list of the lookup and of the run.
deriving instance DecidableEq for Oopsla16.Ctx

/-- The cost of a goal at depth `k`.  It grows with the depth, so the fuel
also bounds the depth of a branch, as the stack does in the compiler. -/
def cost (k : Nat) : Nat := k + 1

theorem costOk : CostOk cost := costOk_succ

/-- The fuel every entry point starts from. -/
def defaultFuel : Nat := 2 ^ 15

/-- Subtyping at the empty store.  Source programs have no store location. -/
abbrev SStp {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Type := Stp Store.nil Γ S T

/-- A variable at a type of its prefix, at the empty store. -/
abbrev SHtp {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (T : Ty [] (scopeUpTo x)) : Type :=
  Htp Store.nil Γ x T

/-- Reflexivity, a derived rule of Oopsla16 (`Oopsla16/Lemmas.lean`). -/
abbrev refl {s : Sig} {Γ : Ctx [] s} (T : Ty [] s) : SStp Γ T T := Oopsla16.Stp.refl T

/-- A type member with its lower bound moved to `⊥`, as `stp_sel1` asks.  When
the bound is already `⊥` the derivation is the one given. -/
def lowerBot {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {l : Lb} {lo hi : Ty [] (scopeUpTo x)}
    (d : SHtp Γ x (.TTyp l lo hi)) : SHtp Γ x (.TTyp l .TBot hi) :=
  if h : lo = .TBot then h ▸ d else .htp_sub d (.stp_typ .stp_bot (Oopsla16.Stp.refl hi))

/-- A type member with its upper bound moved to `⊤`, as `stp_sel2` asks.  When
the bound is already `⊤` the derivation is the one given. -/
def upperTop {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {l : Lb} {lo hi : Ty [] (scopeUpTo x)}
    (d : SHtp Γ x (.TTyp l lo hi)) : SHtp Γ x (.TTyp l lo .TTop) :=
  if h : hi = .TTop then h ▸ d else .htp_sub d (.stp_typ (Oopsla16.Stp.refl lo) .stp_top)

/-! ## Queries and keys -/

/-- What a lookup looks for: a type member or a method, at a label. -/
inductive Key where
  | typ (l : Lb)
  | fn (l : Lb)
deriving DecidableEq

/-- The key fits an atom of a type. -/
def Key.fits {s : Sig} : Key → Ty [] s → Bool
  | .typ l, .TTyp l' _ _ => decide (l = l')
  | .fn l, .TFun l' _ _ => decide (l = l')
  | _, _ => false

/-- A lookup query.  `h s Γ x V k`: the types `x`, seen at `V` in its prefix,
has at the key.  `st s Γ V k`: the types `V` is below at the key. -/
inductive LQ where
  | h (s : Sig) (Γ : Ctx [] s) (x : BVar s .var) (V : Ty [] (scopeUpTo x)) (k : Key)
  | st (s : Sig) (Γ : Ctx [] s) (V : Ty [] s) (k : Key)

/-- The scope of the types an answer is about. -/
def LQ.scope : LQ → Sig
  | .h _ _ x _ _ => scopeUpTo x
  | .st s _ _ _ => s

/-- An answer: a type and the step from the query's start to it. -/
def LQ.R : LQ → Type
  | .h _ Γ x V _ => (ty : Ty [] (scopeUpTo x)) × (SHtp Γ x V → SHtp Γ x ty)
  | .st _ Γ V _ => (ty : Ty [] _) × SStp Γ V ty

/-- The type an answer found. -/
def LQ.ty : (q : LQ) → q.R → Ty [] q.scope
  | .h .., e => e.1
  | .st .., e => e.1

/-- The key of a query in the pending list.  An `h` query is keyed by the
prefix of its variable, which is all an `Htp` derivation sees.  In that prefix
the variable is the newest binder, so it needs no name. -/
inductive LKey where
  | h (s : Sig) (Δ : Ctx [] s) (V : Ty [] s) (k : Key)
  | st (s : Sig) (Γ : Ctx [] s) (V : Ty [] s) (k : Key)
deriving DecidableEq

/-- The key of a query.  An `h` query at `x` is keyed in the prefix at `x`. -/
def LQ.key : LQ → LKey
  | .h _ Γ x V k => .h (scopeUpTo x) (Γ.upTo x) V k
  | .st s Γ V k => .st s Γ V k

/-- A type member read off an `h` answer. -/
def typ? {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V : Ty [] (scopeUpTo x)} (L : Lb) :
    ((ty : Ty [] (scopeUpTo x)) × (SHtp Γ x V → SHtp Γ x ty)) →
    Option ((lo : Ty [] (scopeUpTo x)) × (hi : Ty [] (scopeUpTo x)) ×
      (SHtp Γ x V → SHtp Γ x (.TTyp L lo hi)))
  | ⟨.TTyp l lo hi, f⟩ => if h : l = L then some ⟨lo, hi, h ▸ f⟩ else none
  | _ => none

/-! ## The lookup -/

/-- One level of the lookup, the cases of `findMember`'s `go`
(`Types.scala:820-870`).  `rec` is the lookup one level down, with the query
pending.  At an `h` query a recursive type is opened at the variable (`goRec`,
`Types.scala:875-896`, `htp_unpack`).  At both queries an intersection is
searched in both operands, the left one first (`goAnd`,
`Types.scala:994-995`), and a selection goes on in the upper bounds of its
receiver's members (`Types.scala:5720`, `stp_sel1`).  The members of the
receiver are asked in the prefix that `htp_sub` allows.  A union, `⊥` and
every other atom that does not fit have no answer.  Every call to `rec`
starts from the tank the previous one left. -/
def lookBody (rec : (q : LQ) → Fu (List q.R)) : (q : LQ) → Fu (List q.R)
  | .h s Γ x V k =>
      if k.fits V then Fu.ret [⟨V, id⟩] else
      match V with
      | .TBind X =>
          Fu.bind (rec (.h s Γ x (X.substVr (.abs (varUpTo x))) k)) fun es =>
            Fu.ret (es.map fun e => ⟨e.1, fun d => e.2 (.htp_unpack d)⟩)
      | .TAnd A B =>
          Fu.bind (rec (.h s Γ x A k)) fun es1 =>
            Fu.bind (rec (.h s Γ x B k)) fun es2 =>
              Fu.ret (es1.map (fun e => ⟨e.1, fun d => e.2 (.htp_sub d (.stp_and11 (refl A)))⟩) ++
                es2.map (fun e => ⟨e.1, fun d => e.2 (.htp_sub d (.stp_and12 (refl B)))⟩))
      | .TSel (.abs y) L =>
          Fu.bind (rec (.h _ (Γ.upTo x) y ((Γ.upTo x).lookupAt y) (.typ L))) fun es =>
            Fu.flatMapL (fun e =>
              match typ? L e with
              | some ⟨_, hi, g⟩ =>
                  Fu.bind (rec (.h s Γ x (hi.rename (renameUpTo y)) k)) fun es2 =>
                    Fu.ret (es2.map fun e2 =>
                      ⟨e2.1, fun d => e2.2 (.htp_sub d (.stp_sel1 (lowerBot (g .htp_var))))⟩)
              | none => Fu.ret []) es
      | _ => Fu.ret []
  | .st s Γ V k =>
      if k.fits V then Fu.ret [⟨V, refl V⟩] else
      match V with
      | .TAnd A B =>
          Fu.bind (rec (.st s Γ A k)) fun es1 =>
            Fu.bind (rec (.st s Γ B k)) fun es2 =>
              Fu.ret (es1.map (fun e => ⟨e.1, .stp_and11 e.2⟩) ++
                es2.map (fun e => ⟨e.1, .stp_and12 e.2⟩))
      | .TSel (.abs y) L =>
          Fu.bind (rec (.h s Γ y (Γ.lookupAt y) (.typ L))) fun es =>
            Fu.flatMapL (fun e =>
              match typ? L e with
              | some ⟨_, hi, g⟩ =>
                  Fu.bind (rec (.st s Γ (hi.rename (renameUpTo y)) k)) fun es2 =>
                    Fu.ret (es2.map fun e2 =>
                      ⟨e2.1, .stp_trans (.stp_sel1 (lowerBot (g .htp_var))) e2.2⟩)
              | none => Fu.ret []) es
      | _ => Fu.ret []

/-- Member lookup on demand.  `d` is the structural index, `P` the keys pending
along the branch.  A query costs `cost` of the number of keys pending.  A short
tank answers `[]` and is marked.  A query whose key is pending answers `[]`,
the compiler's cyclic reference.  An answer that ends with the tank marked is
returned as it is, and the caller treats it as a failure. -/
def look : Nat → List LKey → (q : LQ) → Fu (List q.R)
  | 0, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, q =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true => if q.key ∈ P then Fu.ret [] else lookBody (look d (q.key :: P)) q

/-- The type members of `x` at `L`, from its recorded type, each with the
premise of `stp_sel1` and `stp_sel2`. -/
def hdecls {s : Sig} (Γ : Ctx [] s) (d : Nat) (x : BVar s .var) (L : Lb) :
    Fu (List ((lo : Ty [] (scopeUpTo x)) × (hi : Ty [] (scopeUpTo x)) × SHtp Γ x (.TTyp L lo hi))) :=
  Fu.bind (look d [] (.h s Γ x (Γ.lookupAt x) (.typ L))) fun es =>
    Fu.ret (es.filterMap fun e => (typ? L e).map fun ⟨lo, hi, g⟩ => ⟨lo, hi, g .htp_var⟩)

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

/-- One level of the lookup is framed when the level below is. -/
theorem lookBody_framed {rec : (q : LQ) → Fu (List q.R)} (hr : ∀ q, Framed (rec q)) :
    ∀ q, Framed (lookBody rec q) := by
  intro q
  cases q with
  | h s Γ x V k =>
    apply ite_framed (ret_framed _)
    cases V with
    | TBind X => exact bind_framed (hr _) fun _ => ret_framed _
    | TAnd A B => exact bind_framed (hr _) fun _ => bind_framed (hr _) fun _ => ret_framed _
    | TSel p L =>
      cases p with
      | abs y =>
        refine bind_framed (hr _) fun es => flatMapL_framed ?_ es
        intro e
        split
        · exact bind_framed (hr _) fun _ => ret_framed _
        · exact ret_framed _
      | conc _ => exact ret_framed _
    | TBot => exact ret_framed _
    | TTop => exact ret_framed _
    | TFun _ _ _ => exact ret_framed _
    | TTyp _ _ _ => exact ret_framed _
    | TOr _ _ => exact ret_framed _
  | st s Γ V k =>
    apply ite_framed (ret_framed _)
    cases V with
    | TAnd A B => exact bind_framed (hr _) fun _ => bind_framed (hr _) fun _ => ret_framed _
    | TSel p L =>
      cases p with
      | abs y =>
        refine bind_framed (hr _) fun es => flatMapL_framed ?_ es
        intro e
        split
        · exact bind_framed (hr _) fun _ => ret_framed _
        · exact ret_framed _
      | conc _ => exact ret_framed _
    | TBot => exact ret_framed _
    | TTop => exact ret_framed _
    | TFun _ _ _ => exact ret_framed _
    | TTyp _ _ _ => exact ret_framed _
    | TBind _ => exact ret_framed _
    | TOr _ _ => exact ret_framed _

/-- Every lookup is framed: it keeps a marked tank, never adds fuel, and does
the same with more fuel. -/
theorem look_framed (d : Nat) : ∀ (P : List LKey) (q : LQ), Framed (look d P q) := by
  induction d with
  | zero =>
    intro P q
    exact nil_framed q.R
  | succ d ih =>
    intro P q
    apply bind_framed (draw_framed _)
    intro ok
    cases ok
    · exact ret_framed _
    · exact ite_framed (ret_framed _) (lookBody_framed (ih _) q)

theorem look_frame {d : Nat} {P : List LKey} {q : LQ} {t t' : Tank} {es : List q.R}
    (h : look d P q t = (es, t')) (ho : t'.out = false) (j : Nat) :
    look d P q (t.add j) = (es, t'.add j) :=
  (look_framed d P q).shift t es t' h ho j

/-- A lookup from a marked tank answers `[]` and leaves the tank as it is. -/
theorem look_absorbs (d : Nat) (P : List LKey) (q : LQ) {t : Tank} (h : t.out = true) :
    look d P q t = ([], t) := by
  cases d with
  | zero => cases t; simp_all [look]
  | succ d =>
    change Fu.bind (draw (cost P.length)) _ t = _
    simp only [Fu.bind, draw_out h]
    rfl

theorem hdecls_framed {s : Sig} (Γ : Ctx [] s) (d : Nat) (x : BVar s .var) (L : Lb) :
    Framed (hdecls Γ d x L) :=
  bind_framed (look_framed d _ _) fun _ => ret_framed _

theorem hdecls_frame {s : Sig} {Γ : Ctx [] s} {d : Nat} {x : BVar s .var} {L : Lb} {t t' : Tank}
    {ds : List ((lo : Ty [] (scopeUpTo x)) × (hi : Ty [] (scopeUpTo x)) × SHtp Γ x (.TTyp L lo hi))}
    (h : hdecls Γ d x L t = (ds, t')) (ho : t'.out = false) (j : Nat) :
    hdecls Γ d x L (t.add j) = (ds, t'.add j) :=
  (hdecls_framed Γ d x L).shift t ds t' h ho j

/-! ## Checks

Each check runs in the kernel at `defaultFuel`.  `F` is the method type
`{def 9(y : ⊤) : ⊤}`. -/

section LookChecks

/-- The method type `{def l(y : ⊤) : ⊤}`. -/
abbrev fnTop {s : Sig} (l : Lb) : Ty [] s := .TFun l .TTop .TTop

/-- The `h` lookup of `x` at its recorded type, from a full tank: the types
found and the tank left. -/
def lookAt {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (k : Key) (n : Nat := defaultFuel) :
    List (Ty [] (scopeUpTo x)) × Tank :=
  let r := look n [] (.h s Γ x (Γ.lookupAt x) k) ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- The `st` lookup of a type, from a full tank. -/
def stAt {s : Sig} (Γ : Ctx [] s) (V : Ty [] s) (k : Key) (n : Nat := defaultFuel) :
    List (Ty [] s) × Tank :=
  let r := look n [] (.st s Γ V k) ⟨n, false⟩
  (r.1.map (·.1), r.2)

/-- The bounds of the members `hdecls` finds, from a full tank. -/
def hdeclsAt {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (L : Lb) (n : Nat := defaultFuel) :
    List (Ty [] (scopeUpTo x) × Ty [] (scopeUpTo x)) × Tank :=
  let r := hdecls Γ n x L ⟨n, false⟩
  (r.1.map fun d => (d.1, d.2.1), r.2)

/-- `z : {5 : ⊥..⊤} ∧ … ∧ {1 : ⊥..⊤} ∧ {0 : ⊥..F} ∧ ⊤`, a self with six members. -/
def deepCtx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TAnd (.TTyp 5 .TBot .TTop) (.TAnd (.TTyp 4 .TBot .TTop)
    (.TAnd (.TTyp 3 .TBot .TTop) (.TAnd (.TTyp 2 .TBot .TTop) (.TAnd (.TTyp 1 .TBot .TTop)
      (.TAnd (.TTyp 0 .TBot (fnTop 9)) .TTop))))))

/-- The scope of `x0, …, x(n-1)`. -/
def chainBase : Nat → Sig
  | 0 => []
  | n + 1 => (chainBase n),x

/-- The scope of `x0, …, xn`. -/
abbrev chainSig (n : Nat) : Sig := (chainBase n),x

/-- A chain of aliases: `x0 : {0 : ⊥..F}`, `xk : {0 : x(k-1).0 .. x(k-1).0}`. -/
def chainCtx : (n : Nat) → Ctx [] (chainSig n)
  | 0 => Ctx.nil.cons (.TTyp 0 .TBot (fnTop 9))
  | n + 1 => (chainCtx n).cons (.TTyp 0 (.TSel (.abs (.there .here)) 0) (.TSel (.abs (.there .here)) 0))

/-- The chain with `y : xn.0` after it. -/
def chainVar (n : Nat) : Ctx [] ((chainSig n),x) :=
  (chainCtx n).cons (.TSel (.abs (.there .here)) 0)

/-- A self that selects its own member, the parameter of a method:
`c : ⊤`, `p : μ(z. {0 : ⊥..{0 : ⊥..{def 0(y : ⊤) : ⊤}}} ∧ z.0)`. -/
def selfSelCtx : Ctx [] ([],x,x) :=
  (Ctx.nil.cons .TTop).cons
    (.TBind (.TAnd (.TTyp 0 .TBot (.TTyp 0 .TBot (fnTop 0))) (.TSel (.abs .here) 0)))

/-- The same one binder deeper. -/
def selfSelDeep : Ctx [] ([],x,x,x) := selfSelCtx.cons .TTop

/-- An alias cycle: `x : {1 = x.0} ∧ {0 = x.1} ∧ ⊤`. -/
def cycCtx : Ctx [] ([],x) :=
  Ctx.nil.cons (.TAnd (.TTyp 1 (.TSel (.abs .here) 0) (.TSel (.abs .here) 0))
    (.TAnd (.TTyp 0 (.TSel (.abs .here) 1) (.TSel (.abs .here) 1)) .TTop))

/-- A union of two method types of one label: `u : F ∨ F`. -/
def unionCtx : Ctx [] ([],x) := Ctx.nil.cons (.TOr (fnTop 9) (fnTop 9))

-- The member `0` of the self with six members, through six intersections.
example : (hdeclsAt deepCtx .here 0).1 = [(.TBot, fnTop 9)] := by decide +kernel
example : (hdeclsAt deepCtx .here 0).2.out = false := by decide +kernel
-- The chain at ten links.  The member of `x10` is the alias of `x9.0`.  `F` is
-- found at `y : x10.0` through ten selections, by `h` and by `st`.
example : (hdeclsAt (chainCtx 10) .here 0).1 =
    [(.TSel (.abs (.there .here)) 0, .TSel (.abs (.there .here)) 0)] := by decide +kernel
example : (lookAt (chainVar 10) .here (.fn 9)).1 = [fnTop 9] := by decide +kernel
example : (lookAt (chainVar 10) .here (.fn 9)).2.out = false := by decide +kernel
example : (stAt (chainCtx 10) (.TSel (.abs .here) 0) (.fn 9)).1 = [fnTop 9] := by decide +kernel
example : (stAt (chainCtx 10) (.TSel (.abs .here) 0) (.fn 9)).2.out = false := by decide +kernel
-- A self that selects its own member.  The inner query of `p.0` has the key of
-- the outer one, at every binder depth, so the member reached through `p.0` is
-- cut and one member is found.  One binder deeper the answers and the tank are
-- the same.  The method `0` is not found.
example : (hdeclsAt selfSelCtx .here 0).1 = [(.TBot, .TTyp 0 .TBot (fnTop 0))] := by decide +kernel
example : (hdeclsAt selfSelCtx .here 0).2.out = false := by decide +kernel
example : hdeclsAt selfSelDeep (.there .here) 0 = hdeclsAt selfSelCtx .here 0 := by decide +kernel
example : lookAt selfSelDeep (.there .here) (.fn 0) = lookAt selfSelCtx .here (.fn 0) := by
  decide +kernel
example : (lookAt selfSelCtx .here (.fn 0)).1 = [] := by decide +kernel
example : (lookAt selfSelCtx .here (.fn 0)).2.out = false := by decide +kernel
-- The alias cycle: `F` at `x.1` has no answer, and the tank stays unmarked.
example : (look defaultFuel [] (.h _ cycCtx .here (.TSel (.abs .here) 1) (.fn 9))
    ⟨defaultFuel, false⟩).1.length = 0 := by decide +kernel
example : (look defaultFuel [] (.h _ cycCtx .here (.TSel (.abs .here) 1) (.fn 9))
    ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
-- A union has no members, by `h` and by `st`.
example : lookAt unionCtx .here (.fn 9) = ([], ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : (stAt Ctx.nil (.TOr (fnTop 9) (fnTop 9)) (.fn 9)).1 = [] := by decide +kernel
-- `⊥` has no members.
example : (stAt Ctx.nil .TBot (.fn 9)).1 = [] := by decide +kernel
-- A lookup at fuel 1 runs out on the chain.
example : (lookAt (chainVar 10) .here (.fn 9) 1).2.out = true := by decide +kernel

end LookChecks

end Oopsla16Frontend.Core
