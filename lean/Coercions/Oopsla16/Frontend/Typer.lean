import Coercions.Oopsla16.Frontend.Resolve
import Coercions.Oopsla16.Frontend.Avoid

/-!
# The typer

The typer reads a type off an annotated term of Oopsla16 and returns the
`Oopsla16.HasType` derivation with it.  The derivation is a field of the
result, so soundness is the result type and there is no soundness theorem to
prove.

It runs on the tank of `Fuel.lean`.  One tank is threaded through every goal
it asks: each subtyping goal and each variable goal of `Sub.lean`, each member
lookup of `Look.lean`, and each avoidance of `Avoid.lean`.  So the fuel counts
the work of the whole typing, and a goal that finds the tank short marks it.
A marked tank is the recursion limit.  It is never a rejection by the rules.

## Candidates

Synthesis returns a list of candidates, each a type with its derivation, with
no two of one type.  Oopsla16 has no rule that merges two members of one
name, which the compiler does (`Types.scala:5759`).  So the typer keeps every
choice instead.

- A variable has the type its context records, by `T_Varz`.
- A literal has `μ T` for its written self type `T`, or else the one
  `selfOf?` computes, by `T_Obj`.  The members are checked against `T` in
  lockstep, as `DmsHasType` does.
- `(t : T)` has the type `T`.  The ascription binds and `t` is checked
  against it.
- A call `t.l(u)` tries every method type at `l` that the receiver has, for
  every candidate of `t`, and returns the answer of each.

The method types of a variable receiver are looked up on demand in its type
(`tlook`).  A recursive type is opened at the variable by `T_VarUnpack`, as
the compiler's `findMember` opens it with the variable as prefix (`goRec`,
`Types.scala:875-896`).  Both operands of an intersection are searched, and a
selection goes on in the upper bounds of its members by `stp_sel1`.  A union
and `⊥` have no members, as in the compiler (`TypeOps.scala:383-389`,
`Types.scala:827-829`).  A receiver that is not a variable is looked up in its
type by the `st` query of `Look.lean`.  At a recursive type the method is
looked up in the body under the self, and the self is approximated away
(`recvCands`).  This is the compiler's skolemized prefix (`Types.scala:5001`)
followed by `deskolemized` (`Types.scala:1611-1619`).

An argument that is a variable `y` goes in by `T_AppVar`, and the result is
the codomain opened at `y`.  Any other argument takes the first of its
candidates that is below the domain.  The codomain then may not mention the
parameter, so it is approximated by a type free of it (`avoidArg`), as the
compiler approximates a skolem when it infers a type.

## Checking

Checking a variable asks the variable goal of `Sub.lean`, which packs and
unpacks.  A literal and an ascription are compared with the goal by the
subtyping goal.  A call compares each candidate's codomain with the goal.  At
a variable argument the codomain is opened at the argument.  At any other
argument the codomain is compared under the parameter, assumed at the
argument's type, as the compiler compares a skolem with the expected type.
The first candidate that meets the goal is taken.

## The theorems

Every computation here is framed: it keeps a marked tank, never adds fuel,
and does the same with more fuel (`synthF_frame`, `checkF_frame`).  So a
typing that ends unmarked gives the same answer at every larger fuel
(`synthTop?_mono`, `synthTop?_stable`).  A rejection that ends unmarked is a
rejection at every fuel.  The typer has no completeness theorem.  It does not
find a derivation through a middle type the program does not write, as the
compiler does not.  It does not merge two members, since the calculus has no
rule for that, so a call tries each.  It does not find a judgment whose search
needs more than the fuel.  And a lookup through a cyclic member is cut, as the
compiler's cyclic reference.

Every definition is structural on the term, so the kernel evaluates the
typer.  The checks at the end of the module type the example programs at
`defaultFuel` by `decide +kernel`.

Nothing here is part of the metatheory.
-/

namespace Oopsla16Frontend

open Frontend.Fuel Oopsla16Frontend.Core
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Tm Dm Dms Ctx Store Stp Htp HasType DmsHasType EqSome
  scopeUpTo renameUpTo varUpTo)

/-- The fuel of a typing.  One field, the size of the tank every entry point
starts from. -/
structure Budget where
  fuel : Nat := defaultFuel
deriving Repr, Inhabited, DecidableEq

/-- A type a term has, with the derivation. -/
structure Cand {s : Sig} (Γ : Ctx [] s) (t : Tm [] s) where
  /-- The type. -/
  ty : Ty [] s
  /-- The derivation. -/
  deriv : HasType Store.nil Γ t ty

/-! ## Pieces the clauses use -/

/-- Keep the first candidate of each type. -/
def dedupTy {s : Sig} {Γ : Ctx [] s} {t : Tm [] s} : List (Cand Γ t) → List (Cand Γ t)
  | [] => []
  | c :: cs => c :: (dedupTy cs).filter fun c' => !decide (c'.ty = c.ty)

/-- An optional answer as a list of at most one. -/
def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

/-- A type the variable `x` has, reached from a type `V` of it, with the map
from a derivation at `V` to one at the type reached. -/
abbrev VFound {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (V : Ty [] s) : Type :=
  (ty : Ty [] s) × VarFn Γ x V ty

/-- The types the variable `x`, seen at `V`, has at the key, with `HasType`
steps.  A type that fits the key is an answer.  A recursive type is opened at
`x` by `T_VarUnpack`, both operands of an intersection are searched, and a
selection goes on in the upper bounds of its members by `stp_sel1`.  `P` holds
the types visited along the branch, and a type that repeats has no answer.
Each node draws `cost P.length` from the tank.  The index `d` is
structural. -/
def tlook {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) :
    Nat → List (Ty [] s) → (V : Ty [] s) → Key → Fu (List (VFound Γ x V))
  | 0, _, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, V, k =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret []
        | true =>
          if V ∈ P then Fu.ret [] else
          if k.fits V then Fu.ret [⟨V, id⟩] else
          match V with
          | .TBind B =>
              Fu.bind (tlook Γ x d (.TBind B :: P) (B.substVr (.abs x)) k) fun es =>
                Fu.ret (es.map fun e => ⟨e.1, fun h => e.2 (.T_VarUnpack h)⟩)
          | .TAnd A B =>
              Fu.bind (tlook Γ x d (.TAnd A B :: P) A k) fun es1 =>
                Fu.bind (tlook Γ x d (.TAnd A B :: P) B k) fun es2 =>
                  Fu.ret (es1.map (fun e => ⟨e.1, fun h => e.2 (.T_Sub h (.stp_and11 (refl A)))⟩) ++
                    es2.map (fun e => ⟨e.1, fun h => e.2 (.T_Sub h (.stp_and12 (refl B)))⟩))
          | .TSel (.abs q) L =>
              Fu.bind (members Γ q L) fun ms =>
                Fu.flatMapL (fun m =>
                  Fu.bind (tlook Γ x d (.TSel (.abs q) L :: P) (m.2.1.rename (renameUpTo q)) k)
                    fun es => Fu.ret (es.map fun e =>
                      ⟨e.1, fun h => e.2 (.T_Sub h (.stp_sel1 (lowerBot m.2.2)))⟩)) ms
          | _ => Fu.ret []
termination_by structural d _ _ _ => d

/-- `tlook` on the tank it is handed, with the fuel left as its index. -/
def tlookAt {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (V : Ty [] s) (k : Key) :
    Fu (List (VFound Γ x V)) := fun t =>
  tlook Γ x t.left [] V k t

/-- The `st` lookup of `Look.lean` on the tank it is handed: the types `V` is
below at the key, each with the derivation.  The index is the fuel left. -/
def stLook {s : Sig} (Γ : Ctx [] s) (V : Ty [] s) (k : Key) :
    Fu (List ((ty : Ty [] s) × SStp Γ V ty)) := fun t =>
  look t.left [] (.st s Γ V k) t

/-- A method type of a receiver `te` at the label `l`, with the receiver at
it. -/
structure MethCand {s : Sig} (Γ : Ctx [] s) (te : Tm [] s) (l : Lb) where
  /-- The domain. -/
  dom : Ty [] s
  /-- The codomain, under the parameter. -/
  cod : Ty [] (s,x)
  /-- The receiver at the method type. -/
  recv : HasType Store.nil Γ te (.TFun l dom cod)

/-- Read a method type at `l` off a typing of the receiver. -/
def asFun? {s : Sig} {Γ : Ctx [] s} {te : Tm [] s} (l : Lb) :
    (T : Ty [] s) → HasType Store.nil Γ te T → Option (MethCand Γ te l)
  | .TFun l' S U, d => if h : l' = l then some ⟨S, U, h ▸ d⟩ else none
  | _, _ => none

/-- The method types of a receiver that is not a variable, from its type `V`.
At a recursive type `μ X` the method is looked up in `X` under the self, the
self is approximated away from above, and `stp_bind1` closes it. -/
def recvCands {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (l : Lb) :
    (V : Ty [] s) → HasType Store.nil Γ te V → Fu (List (MethCand Γ te l))
  | .TBind X, hV =>
      Fu.bind (stLook (Γ.cons X) X (.fn l)) fun es =>
        Fu.flatMapL (fun e =>
          Fu.bind (upAt (Γ.cons X) .here e.1) fun r =>
            Fu.ret (match FCdotR.Ty.strengthenW? r.1 with
              | some w => listO (asFun? l w.val
                  (.T_Sub hV (.stp_bind1 (w.property ▸ .stp_trans e.2 r.2))))
              | none => [])) es
  | V, hV =>
      Fu.bind (stLook Γ V (.fn l)) fun es =>
        Fu.ret (es.filterMap fun e => asFun? l e.1 (.T_Sub hV e.2))

/-- The method types of a call's receiver at `l`, from one of its candidates:
looked up on demand in the type of a variable, or read off the type of any
other term. -/
def cands {s : Sig} (Γ : Ctx [] s) (l : Lb) :
    (t : ATm s) → Cand Γ t.erase → Fu (List (MethCand Γ t.erase l))
  | .var x, ct =>
      Fu.bind (tlookAt Γ x ct.ty (.fn l)) fun es =>
        Fu.ret (es.filterMap fun e => asFun? l e.1 (e.2 ct.deriv))
  | _, ct => recvCands Γ l ct.ty ct.deriv

/-- The answer of a call in synthesis, for one method type.  A variable
argument goes in by `T_AppVar`.  Any other argument takes its first candidate
below the domain, and the codomain is approximated by a type free of the
parameter, by `T_App`. -/
def argSynth {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} {l : Lb} :
    (u : ATm s) → List (Cand Γ u.erase) → MethCand Γ te l →
      Fu (Option (Cand Γ (.tapp te l u.erase)))
  | .var y, _, c =>
      mapO (varF Γ y c.dom) fun hy => ⟨c.cod.substVr (.abs y), .T_AppVar c.recv hy⟩
  | _, cus, c =>
      Fu.firstSome (fun cu =>
        bindO (subF Γ cu.ty c.dom) fun eA =>
          mapO (avoidArg Γ l c.dom c.cod cu.ty eA) fun r =>
            ⟨r.1, .T_App (.T_Sub c.recv r.2) cu.deriv⟩) cus

/-- A call checked at the goal `G`, for one method type.  At a variable
argument the codomain opened at it is compared with `G`.  At any other
argument the codomain is compared with `G` under the parameter, assumed at the
argument's type, and `stp_fun` widens the receiver. -/
def argCheck {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} {l : Lb} :
    (u : ATm s) → List (Cand Γ u.erase) → MethCand Γ te l → (G : Ty [] s) →
      Fu (Option (HasType Store.nil Γ (.tapp te l u.erase) G))
  | .var y, _, c, G =>
      bindO (varF Γ y c.dom) fun hy =>
        mapO (subF Γ (c.cod.substVr (.abs y)) G) fun e => .T_Sub (.T_AppVar c.recv hy) e
  | _, cus, c, G =>
      Fu.firstSome (fun cu =>
        bindO (subF Γ cu.ty c.dom) fun eA =>
          mapO (subF (Γ.cons cu.ty.weaken) c.cod G.weaken) fun e =>
            .T_App (.T_Sub c.recv (.stp_fun eA e)) cu.deriv) cus

/-! ## Synthesis and checking

Three functions, structural on the term.  `synthF` returns the candidates of a
term.  `checkF` checks a term against a type.  `checkDmsF` matches a member
list against a self type in lockstep, as `DmsHasType` does: `D_Nil`, `D_Typ`
and `D_Fun`.  A method's types come from the self type, so a Curry style
method checks. -/

mutual

/-- The candidates of a term, each with its derivation, on the tank. -/
def synthF {s : Sig} (Γ : Ctx [] s) : (a : ATm s) → Fu (List (Cand Γ a.erase))
  | .var x => Fu.ret [⟨Γ.lookup x, .T_Varz⟩]
  | .obj o ds =>
      match o <|> selfOf? ds.erase with
      | some T =>
          Fu.bind (checkDmsF (Γ.cons T) ds T) fun od =>
            Fu.ret (listO (od.map fun d => (⟨.TBind T, .T_Obj d⟩ : Cand Γ (ATm.obj o ds).erase)))
      | none => Fu.ret []
  | .app t l u =>
      Fu.bind (synthF Γ t) fun cts =>
        Fu.bind (synthF Γ u) fun cus =>
          Fu.bind (Fu.flatMapL (fun ct =>
              Fu.bind (cands Γ l t ct) fun cs =>
                Fu.flatMapL (fun c => Fu.bind (argSynth Γ u cus c) fun o => Fu.ret (listO o)) cs)
              cts) fun rs =>
            Fu.ret (dedupTy rs)
  | .asc a T =>
      Fu.bind (checkF Γ a T) fun o =>
        Fu.ret (listO (o.map fun h => (⟨T, h⟩ : Cand Γ (ATm.asc a T).erase)))

/-- Check a term against `T`, on the tank. -/
def checkF {s : Sig} (Γ : Ctx [] s) : (a : ATm s) → (T : Ty [] s) →
    Fu (Option (HasType Store.nil Γ a.erase T))
  | .var x, T => varF Γ x T
  | .obj o ds, T =>
      match o <|> selfOf? ds.erase with
      | some S =>
          bindO (checkDmsF (Γ.cons S) ds S) fun d =>
            mapO (subF Γ (.TBind S) T) fun e => .T_Sub (.T_Obj d) e
      | none => Fu.ret none
  | .app t l u, T =>
      Fu.bind (synthF Γ t) fun cts =>
        Fu.bind (synthF Γ u) fun cus =>
          Fu.firstSome (fun ct =>
            Fu.bind (cands Γ l t ct) fun cs =>
              Fu.firstSome (fun c => argCheck Γ u cus c T) cs) cts
  | .asc a T', T =>
      bindO (checkF Γ a T') fun h => mapO (subF Γ T' T) fun e => .T_Sub h e

/-- A member list against a self type, in lockstep.  The label of a member is
its position, a type member has its own type on both bounds, and a method's
annotations agree with the self type and its body checks at the codomain
under the parameter. -/
def checkDmsF {s : Sig} (Γ : Ctx [] s) : (ds : ADms s) → (T : Ty [] s) →
    Fu (Option (DmsHasType Store.nil Γ ds.erase T))
  | .dnil, .TTop => Fu.ret (some .D_Nil)
  | .dcons (.dty T') ds', .TAnd (.TTyp l T1 T2) TS =>
      if h : l = ds'.erase.length ∧ T1 = T' ∧ T2 = T' then
        mapO (checkDmsF Γ ds' TS) fun d => by
          obtain ⟨h1, h2, h3⟩ := h
          subst h1 h2 h3
          exact .D_Typ d
      else Fu.ret none
  | .dcons (.dfun o1 o2 t) ds', .TAnd (.TFun l T11 T12) TS =>
      if h : l = ds'.erase.length ∧ EqSome o1 T11 ∧ EqSome o2 T12 then
        bindO (checkDmsF Γ ds' TS) fun d =>
          mapO (checkF (Γ.cons T11.weaken) t T12) fun hb => by
            obtain ⟨h1, e1, e2⟩ := h
            subst h1
            exact .D_Fun d hb e1 e2
      else Fu.ret none
  | _, _ => Fu.ret none

end

/-! ## The entry points -/

/-- The first candidate, and `none` if the tank ended marked. -/
def firstCand {α : Type} : List α × Tank → Option α × Tank
  | (c :: _, t) => if t.out then (none, t) else (some c, t)
  | ([], t) => (none, t)

/-- An answer, and `none` if the tank ended marked. -/
def answerUnmarked {α : Type} : Option α × Tank → Option α × Tank
  | (some a, t) => if t.out then (none, t) else (some a, t)
  | (none, t) => (none, t)

/-- The first candidate of a term in `Γ`, from a full tank of `n` units, with
the tank left. -/
def synthInF {s : Sig} (Γ : Ctx [] s) (a : ATm s) (n : Nat) : Option (Cand Γ a.erase) × Tank :=
  firstCand (synthF Γ a ⟨n, false⟩)

/-- The first candidate of a closed term, from a full tank of `n` units, with
the tank left. -/
def synthTopF (n : Nat) (a : ATm []) : Option (Cand Ctx.nil a.erase) × Tank :=
  synthInF Ctx.nil a n

/-- A check of a term in `Γ`, from a full tank of `n` units, with the tank
left. -/
def checkInF {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) (n : Nat) :
    Option (HasType Store.nil Γ a.erase T) × Tank :=
  answerUnmarked (checkF Γ a T ⟨n, false⟩)

/-- A type of a term in `Γ`, at the budget's fuel. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx [] s) (a : ATm s) : Option (Cand Γ a.erase) :=
  (synthInF Γ a b.fuel).1

/-- A type of a closed term, at the budget's fuel. -/
def synthTop? (b : Budget) (a : ATm []) : Option (Cand Ctx.nil a.erase) :=
  (synthTopF b.fuel a).1

/-- A check of a term in `Γ`, at the budget's fuel. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) :
    Option (HasType Store.nil Γ a.erase T) :=
  (checkInF Γ a T b.fuel).1

/-- The synthesized type alone. -/
def typeIn? {s : Sig} (b : Budget) (Γ : Ctx [] s) (a : ATm s) : Option (Ty [] s) :=
  (synthIn? b Γ a).map (·.ty)

/-- Whether checking succeeds. -/
def checksIn {s : Sig} (b : Budget) (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) : Bool :=
  (checkIn? b Γ a T).isSome

/-! ## The frame lemmas

Each clause is built from the combinators of `Fuel.lean` and from framed
computations of the other modules: `varF`, `subF`, `members`, `look`, `upAt`
and `avoidArg`.  So each clause is framed, by induction on the term. -/

/-- `tlook` is framed at every index. -/
theorem tlook_framed {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) :
    ∀ (d : Nat) (P : List (Ty [] s)) (V : Ty [] s) (k : Key), Framed (tlook Γ x d P V k)
  | 0, _, _, _ => nil_framed _
  | d + 1, P, V, k => by
    apply bind_framed (draw_framed _)
    intro ok
    cases ok
    · exact ret_framed _
    · apply ite_framed (ret_framed _)
      apply ite_framed (ret_framed _)
      cases V with
      | TBind B => exact bind_framed (tlook_framed Γ x d _ _ _) fun _ => ret_framed _
      | TAnd A B =>
        exact bind_framed (tlook_framed Γ x d _ _ _) fun _ =>
          bind_framed (tlook_framed Γ x d _ _ _) fun _ => ret_framed _
      | TSel p L =>
        cases p with
        | abs q =>
          refine bind_framed (members_framed Γ q L) fun ms => flatMapL_framed (fun m => ?_) ms
          exact bind_framed (tlook_framed Γ x d _ _ _) fun _ => ret_framed _
        | conc _ => exact ret_framed _
      | TBot => exact ret_framed _
      | TTop => exact ret_framed _
      | TFun _ _ _ => exact ret_framed _
      | TTyp _ _ _ => exact ret_framed _
      | TOr _ _ => exact ret_framed _

/-- `tlook` at a larger index does what it does at a smaller one. -/
theorem tlook_agree {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) :
    ∀ (d d' : Nat), d ≤ d' → ∀ (P : List (Ty [] s)) (V : Ty [] s) (k : Key),
      Agree (tlook Γ x d P V k) (tlook Γ x d' P V k)
  | 0, d', _, P, V, k => by
    refine ⟨tlook_framed Γ x 0 P V k, tlook_framed Γ x d' P V k, ?_⟩
    intro t r t' h ho _
    simp only [tlook, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, V, k => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := tlook_agree Γ x d e (by omega)
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply ite_agree (ret_agree _)
      cases V with
      | TBind B => exact bind_agree (ih _ _ _) fun _ => ret_agree _
      | TAnd A B => exact bind_agree (ih _ _ _) fun _ => bind_agree (ih _ _ _) fun _ => ret_agree _
      | TSel p L =>
        cases p with
        | abs q =>
          refine bind_agree (Agree.refl (members_framed Γ q L)) fun ms =>
            flatMapL_agree (fun m => ?_) ms
          exact bind_agree (ih _ _ _) fun _ => ret_agree _
        | conc _ => exact ret_agree _
      | TBot => exact ret_agree _
      | TTop => exact ret_agree _
      | TFun _ _ _ => exact ret_agree _
      | TTyp _ _ _ => exact ret_agree _
      | TOr _ _ => exact ret_agree _

/-- `tlook` from the fuel left is framed. -/
theorem tlookAt_framed {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (V : Ty [] s) (k : Key) :
    Framed (tlookAt Γ x V k) where
  absorbs t ht := (tlook_framed Γ x t.left [] V k).absorbs t ht
  spends t := (tlook_framed Γ x t.left [] V k).spends t
  shift := by
    intro t r t' h ho j
    exact (tlook_agree Γ x t.left (t.left + j) (Nat.le_add_right _ _) [] V k).sim t r t' h ho j

/-- A lookup from the fuel left is framed, as `members` is. -/
theorem lookLeft_framed (q : LQ) : Framed (fun t => look t.left [] q t) where
  absorbs t ht := (look_framed t.left [] q).absorbs t ht
  spends t := (look_framed t.left [] q).spends t
  shift := by
    intro t r t' h ho j
    exact (look_agree t.left (t.left + j) (Nat.le_add_right _ _) [] q).sim t r t' h ho j

theorem stLook_framed {s : Sig} (Γ : Ctx [] s) (V : Ty [] s) (k : Key) :
    Framed (stLook Γ V k) :=
  lookLeft_framed (.st s Γ V k)

theorem recvCands_framed {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} (l : Lb) (V : Ty [] s)
    (hV : HasType Store.nil Γ te V) : Framed (recvCands Γ l V hV) := by
  cases V with
  | TBind X =>
    exact bind_framed (stLook_framed _ _ _) fun es =>
      flatMapL_framed (fun _ => bind_framed (upAt_framed _ _ _) fun _ => ret_framed _) es
  | TBot => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TTop => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TFun _ _ _ => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TTyp _ _ _ => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TSel _ _ => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TAnd _ _ => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _
  | TOr _ _ => exact bind_framed (stLook_framed _ _ _) fun _ => ret_framed _

theorem cands_framed {s : Sig} (Γ : Ctx [] s) (l : Lb) (t : ATm s) (ct : Cand Γ t.erase) :
    Framed (cands Γ l t ct) := by
  cases t with
  | var x => exact bind_framed (tlookAt_framed _ _ _ _) fun _ => ret_framed _
  | obj _ _ => exact recvCands_framed _ _ _ _
  | app _ _ _ => exact recvCands_framed _ _ _ _
  | asc _ _ => exact recvCands_framed _ _ _ _

theorem argSynth_framed {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} {l : Lb} (u : ATm s)
    (cus : List (Cand Γ u.erase)) (c : MethCand Γ te l) : Framed (argSynth Γ u cus c) := by
  cases u with
  | var y => exact mapO_framed _ (varF_framed _ _ _)
  | obj _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (avoidArg_framed _ _ _ _ _ _)) cus
  | app _ _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (avoidArg_framed _ _ _ _ _ _)) cus
  | asc _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (avoidArg_framed _ _ _ _ _ _)) cus

theorem argCheck_framed {s : Sig} (Γ : Ctx [] s) {te : Tm [] s} {l : Lb} (u : ATm s)
    (cus : List (Cand Γ u.erase)) (c : MethCand Γ te l) (G : Ty [] s) :
    Framed (argCheck Γ u cus c G) := by
  cases u with
  | var y => exact bindO_framed (varF_framed _ _ _) fun _ => mapO_framed _ (subF_framed _ _ _)
  | obj _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (subF_framed _ _ _)) cus
  | app _ _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (subF_framed _ _ _)) cus
  | asc _ _ =>
    exact firstSome_framed (fun _ => bindO_framed (subF_framed _ _ _) fun _ =>
      mapO_framed _ (subF_framed _ _ _)) cus

mutual

theorem synthF_framed {s : Sig} (Γ : Ctx [] s) : (a : ATm s) → Framed (synthF Γ a)
  | .var x => by
    rw [synthF]
    exact ret_framed _
  | .obj o ds => by
    rw [synthF]
    split
    · exact bind_framed (checkDmsF_framed _ ds _) fun _ => ret_framed _
    · exact ret_framed _
  | .app t l u => by
    rw [synthF]
    exact bind_framed (synthF_framed Γ t) fun cts => bind_framed (synthF_framed Γ u) fun cus =>
      bind_framed (flatMapL_framed (fun ct => bind_framed (cands_framed Γ l t ct) fun cs =>
        flatMapL_framed (fun c => bind_framed (argSynth_framed Γ u cus c) fun _ => ret_framed _) cs)
        cts) fun _ => ret_framed _
  | .asc a T => by
    rw [synthF]
    exact bind_framed (checkF_framed Γ a T) fun _ => ret_framed _

theorem checkF_framed {s : Sig} (Γ : Ctx [] s) : (a : ATm s) → (T : Ty [] s) →
    Framed (checkF Γ a T)
  | .var x, T => by
    rw [checkF]
    exact varF_framed _ _ _
  | .obj o ds, T => by
    rw [checkF]
    split
    · exact bindO_framed (checkDmsF_framed _ ds _) fun _ => mapO_framed _ (subF_framed _ _ _)
    · exact ret_framed _
  | .app t l u, T => by
    rw [checkF]
    exact bind_framed (synthF_framed Γ t) fun cts => bind_framed (synthF_framed Γ u) fun cus =>
      firstSome_framed (fun ct => bind_framed (cands_framed Γ l t ct) fun cs =>
        firstSome_framed (fun c => argCheck_framed Γ u cus c T) cs) cts
  | .asc a T', T => by
    rw [checkF]
    exact bindO_framed (checkF_framed Γ a T') fun _ => mapO_framed _ (subF_framed _ _ _)

theorem checkDmsF_framed {s : Sig} (Γ : Ctx [] s) : (ds : ADms s) → (T : Ty [] s) →
    Framed (checkDmsF Γ ds T)
  | .dnil, T => by
    cases T <;> exact ret_framed _
  | .dcons (.dty T') ds', T => by
    cases T with
    | TAnd A TS =>
      cases A with
      | TTyp l T1 T2 =>
        rw [checkDmsF]
        exact (dite_agree (fun _ => Agree.refl (mapO_framed _ (checkDmsF_framed Γ ds' TS)))
          (fun _ => ret_agree _)).left
      | _ => exact ret_framed _
    | _ => exact ret_framed _
  | .dcons (.dfun o1 o2 t) ds', T => by
    cases T with
    | TAnd A TS =>
      cases A with
      | TFun l T11 T12 =>
        rw [checkDmsF]
        exact (dite_agree (fun _ => Agree.refl (bindO_framed (checkDmsF_framed Γ ds' TS) fun _ =>
          mapO_framed _ (checkF_framed (Γ.cons T11.weaken) t T12))) (fun _ => ret_agree _)).left
      | _ => exact ret_framed _
    | _ => exact ret_framed _

end

/-- A synthesis that ends unmarked does the same with more fuel. -/
theorem synthF_frame {s : Sig} {Γ : Ctx [] s} {a : ATm s} {t t' : Tank}
    {r : List (Cand Γ a.erase)} (h : synthF Γ a t = (r, t')) (ho : t'.out = false) (k : Nat) :
    synthF Γ a (t.add k) = (r, t'.add k) :=
  (synthF_framed Γ a).shift t r t' h ho k

/-- A check that ends unmarked does the same with more fuel. -/
theorem checkF_frame {s : Sig} {Γ : Ctx [] s} {a : ATm s} {T : Ty [] s} {t t' : Tank}
    {r : Option (HasType Store.nil Γ a.erase T)} (h : checkF Γ a T t = (r, t'))
    (ho : t'.out = false) (k : Nat) : checkF Γ a T (t.add k) = (r, t'.add k) :=
  (checkF_framed Γ a T).shift t r t' h ho k

/-- A first candidate leaves the tank unmarked. -/
theorem firstCand_some {α : Type} {r : List α × Tank} {c : α} (h : (firstCand r).1 = some c) :
    (firstCand r).2.out = false := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => simp [firstCand] at h
  | cons c' l =>
    cases ht : t.out with
    | false => simp [firstCand, ht]
    | true => simp [firstCand, ht] at h

theorem firstCand_add {α : Type} (l : List α) (t : Tank) (k : Nat) :
    firstCand (l, t.add k) = ((firstCand (l, t)).1, (firstCand (l, t)).2.add k) := by
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, ht]

/-- The tank `firstCand` leaves is the one it is handed. -/
theorem firstCand_snd {α : Type} (r : List α × Tank) : (firstCand r).2 = r.2 := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, ht]

theorem synthInF_stable {s : Sig} {Γ : Ctx [] s} {a : ATm s} {n k : Nat}
    {r : Option (Cand Γ a.erase)} (h : synthInF Γ a n = (r, ⟨k, false⟩)) (m : Nat) :
    (synthInF Γ a (n + m)).1 = r := by
  unfold synthInF at h ⊢
  cases hs : synthF Γ a ⟨n, false⟩ with
  | mk l t' =>
    have ht' : t' = ⟨k, false⟩ := by
      have := firstCand_snd (synthF Γ a ⟨n, false⟩)
      rw [h, hs] at this
      exact this.symm
    have hf := synthF_frame hs (by rw [ht']) m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf, firstCand_add]
    rw [hs] at h
    rw [h]

theorem synthInF_mono {s : Sig} {Γ : Ctx [] s} {a : ATm s} {n m : Nat} {c : Cand Γ a.erase}
    (h : (synthInF Γ a n).1 = some c) (hnm : n ≤ m) : (synthInF Γ a m).1 = some c := by
  have ho : (synthInF Γ a n).2.out = false := firstCand_some h
  have he : synthInF Γ a n = (some c, ⟨(synthInF Γ a n).2.left, false⟩) := by
    rw [← h, ← ho]
  have := synthInF_stable he (m - n)
  rw [Nat.add_sub_cancel' hnm] at this
  exact this

/-- More fuel keeps the answer of a closed typing. -/
theorem synthTop?_mono {n m : Nat} {a : ATm []} {c : Cand Ctx.nil a.erase}
    (h : (synthTopF n a).1 = some c) (hnm : n ≤ m) : (synthTopF m a).1 = some c :=
  synthInF_mono h hnm

/-- A closed typing that ends unmarked gives the same verdict at every larger
fuel.  So a rejection that ends unmarked is a rejection by the rules. -/
theorem synthTop?_stable {n k : Nat} {a : ATm []} {r : Option (Cand Ctx.nil a.erase)}
    (h : synthTopF n a = (r, ⟨k, false⟩)) (m : Nat) : (synthTopF (n + m) a).1 = r :=
  synthInF_stable h m

/-- The tank `answerUnmarked` leaves is the one it is handed. -/
theorem answerUnmarked_snd {α : Type} (r : Option α × Tank) : (answerUnmarked r).2 = r.2 := by
  obtain ⟨o, t⟩ := r
  cases o with
  | none => rfl
  | some a => cases ht : t.out <;> simp [answerUnmarked, ht]

theorem answerUnmarked_add {α : Type} (o : Option α) (t : Tank) (k : Nat) :
    answerUnmarked (o, t.add k) = ((answerUnmarked (o, t)).1, (answerUnmarked (o, t)).2.add k) := by
  cases o with
  | none => rfl
  | some a => cases ht : t.out <;> simp [answerUnmarked, ht]

/-- A check that ends unmarked gives the same verdict at every larger fuel. -/
theorem checkInF_stable {s : Sig} {Γ : Ctx [] s} {a : ATm s} {T : Ty [] s} {n k : Nat}
    {r : Option (HasType Store.nil Γ a.erase T)} (h : checkInF Γ a T n = (r, ⟨k, false⟩))
    (m : Nat) : (checkInF Γ a T (n + m)).1 = r := by
  unfold checkInF at h ⊢
  cases hs : checkF Γ a T ⟨n, false⟩ with
  | mk o t' =>
    have ht' : t' = ⟨k, false⟩ := by
      have := answerUnmarked_snd (checkF Γ a T ⟨n, false⟩)
      rw [h, hs] at this
      exact this.symm
    have hf := checkF_frame hs (by rw [ht']) m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf, answerUnmarked_add]
    rw [hs] at h
    rw [h]

/-! ## Checks

Each check types a surface program of `Notation.lean`, or one written here,
at `defaultFuel` in the kernel.  It states the type, or that there is none,
and the tank left.  An unmarked tank says that the fuel played no part in the
verdict.  A rejection with the tank unmarked holds at every fuel
(`synthTop?_stable`). -/

namespace TyperChecks

/-- The type of a closed program after resolution, from a full tank of `n`
units, and the tank left.  A program that does not resolve leaves the tank
full. -/
def typeAt (Λ : LabelTable) (e : STm) (n : Nat := defaultFuel) : Option (Ty [] []) × Tank :=
  match resolve Λ e with
  | some a => let r := synthTopF n a
      (r.1.map (·.ty), r.2)
  | none => (none, ⟨n, false⟩)

/-- The type of a term in `Γ`, from a full tank of `n` units, and the tank
left. -/
def typeInAt {s : Sig} (Γ : Ctx [] s) (a : ATm s) (n : Nat := defaultFuel) :
    Option (Ty [] s) × Tank :=
  let r := synthInF Γ a n
  (r.1.map (·.ty), r.2)

/-- Whether a term checks in `Γ`, from a full tank of `n` units, and the tank
left. -/
def checkAt {s : Sig} (Γ : Ctx [] s) (a : ATm s) (T : Ty [] s) (n : Nat := defaultFuel) :
    Bool × Tank :=
  let r := checkInF Γ a T n
  (r.1.isSome, r.2)

/-! ### The calculus's programs -/

/-- `ex0` at `μ(z. ⊤)`, the type of `Oopsla16.Examples.ex0_precise`. -/
example : typeAt [] ex0src = (some (.TBind .TTop), ⟨defaultFuel, false⟩) := by decide +kernel

/-- `ex0` ascribed, at `⊤`, the type of `Oopsla16.Examples.ex0`. -/
example : typeAt [] ex0AscSrc = (some .TTop, ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- `RecursiveArg.prog` at `⊤`, the type of
`FCdotR.SourceSafety.RecursiveArg.progTy`.  The receiver is a literal, so its
method is read off its type under the self, and the argument's type is below
the domain by `stp_bindx` with two `stp_sel2`. -/
example : typeAt recArgTable recArgSrc = (some .TTop, ⟨defaultFuel - 117, false⟩) := by
  decide +kernel

/-- `CurryCall.prog` at `⊤`, the type of `FCdotR.CurryCall.progTy`. -/
example : typeAt curryCallTable curryCallSrc = (some .TTop, ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

/-- `ex1` synthesizes the self type `selfOf?` computes. -/
example : typeAt ex1Table ex1src
    = (some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- `ex1` checks at `polyId`, the type of `FCdotR.CheckerExamples.DotExs.ex1`. -/
example : ((resolve ex1Table ex1src).map fun a =>
    checkAt Ctx.nil a FCdotR.CheckerExamples.DotExs.polyId)
    = some (true, ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

/-- `ex2`, open in `y : polyId`, synthesizes `{def apply(x : ⊤) : ⊤}`, the type
of `FCdotR.CheckerExamples.DotExs.ex2`.  The parameter is avoided: the
codomain `{def apply(x : t.T) : t.T}` takes the literal's bounds of `T`. -/
example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map
    (typeInAt FCdotR.CheckerExamples.DotExs.Γy)
    = some (some (.TFun 0 .TTop .TTop), ⟨defaultFuel - 40, false⟩) := by
  decide +kernel

/-- `paper_lst` at its module type, the type of
`FCdotR.CheckerExamples.PaperLst.paper_lst`. -/
example : typeAt paperLstTable paperLstSrc
    = (some (.TBind FCdotR.CheckerExamples.PaperLst.DeclBody), ⟨defaultFuel - 1229, false⟩) := by
  decide +kernel

/-- An alias cycle among three literals has no label table, and resolution
rejects it under the table the first literal suggests. -/
example : typeAt [("a", 1), ("b", 0), ("c", 0)] cyclicSrc = (none, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-! ### Open examples

The context `Γz` of `Oopsla16.Examples.FunctionField` holds the self
`z : S(z)`. -/

section FunctionField
open Oopsla16.Examples.FunctionField (Γz A B f)

/-- A call on the self under the parameter: `z.f(x)` with `x : ⊤` has the result
`z.A`, by `T_AppVar`. -/
example : typeInAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    = (some (.TSel (.abs (.there .here)) A), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- `methodCovariant`: `z.f(x)` checks at `z.B`, by `selUnder` from the result
`z.A`. -/
example : checkAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    (.TSel (.abs (.there .here)) B) = (true, ⟨defaultFuel - 37, false⟩) := by
  decide +kernel

end FunctionField

/-! ### Opening below an intersection and a selection

In `paper_lst`, the innermost parameter of `cons` is
`tl : m.List ∧ {Elem : ⊥..t.T}`.  The lookup of `head` splits the
intersection, widens `m.List` to the list type, opens it and splits again.
So `tl.head(tl)` answers `tl.Elem`. -/

section PaperLst
open FCdotR.CheckerExamples.PaperLst (Γ2t)

example : typeInAt Γ2t (.app (.var .here) 2 (.var .here))
    = (some (.TSel (.abs .here) 0), ⟨defaultFuel - 93, false⟩) := by
  decide +kernel

end PaperLst

/-! ### A call on a literal whose method type mentions its self

`f`'s codomain `z.A` mentions the receiver's self.  The method is looked up
under the self, and the self is approximated away: `z.A` becomes the upper
bound `⊤` of the member `A`.  `stp_bind1` closes it, and the call types at
`⊤`, as scalac infers `Any`. -/

/-- The program. -/
def selfCallSrc : STm := o16% (new { z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤ }).f(new { w ⇒ })

/-- Its label table. -/
def selfCallTable : LabelTable := [("f", 1), ("A", 0)]

example : labelsOfProgram [] selfCallSrc = some selfCallTable := by decide

example : typeAt selfCallTable selfCallSrc = (some .TTop, ⟨defaultFuel - 43, false⟩) := by
  decide +kernel

/-! ### A call on a variable whose type is a selection

`x : c.L` reaches `c.L`'s upper bound `{def f(y : ⊤) : ⊤}` by `stp_sel1`. -/

/-- The method type `{def 0(y : ⊤) : ⊤}`. -/
abbrev F {s : Sig} : Ty [] s := .TFun 0 .TTop .TTop

/-- `c`'s self: `{L : F..F} ∧ {def 0(x : c.L) : ⊤} ∧ ⊤`. -/
abbrev selfC : Ty [] ([],x) :=
  .TAnd (.TTyp 1 F F) (.TAnd (.TFun 0 (.TSel (.abs .here) 1) .TTop) .TTop)

/-- The program.  `f` names a method of a type, so its label is an explicit
entry. -/
def selCallSrc : STm := o16% new { c ⇒ type L = { def f(y : ⊤) : ⊤ }   def g(x : c.L) : ⊤ = x.f(x) }

/-- Its label table. -/
def selCallTable : LabelTable := [("f", 0), ("L", 1), ("g", 0)]

example : labelsOfProgram [("f", 0)] selCallSrc = some selCallTable := by decide

example : typeAt selCallTable selCallSrc = (some (.TBind selfC), ⟨defaultFuel - 32, false⟩) := by
  decide +kernel

/-! ### The first candidate's answer fails the goal

`x` has two method types at `f`.  The first answers `⊤`, which is not below
the goal `{A : ⊥..⊤}`, so checking moves on to the second. -/

/-- The program. -/
def twoCandSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤ ∧ ⊤ ∧ ⊤ ∧ ⊤) : ⊤ } ∧ { def f(y : ⊤) : { type A : ⊥ .. ⊤ } })
                   : { type A : ⊥ .. ⊤ } = x.f(x) }

/-- Its label table. -/
def twoCandTable : LabelTable := [("f", 0), ("A", 0), ("g", 0)]

example : labelsOfProgram [("f", 0), ("A", 0)] twoCandSrc = some twoCandTable := by decide

/-- `{A : ⊥..⊤}`. -/
abbrev memberA {s : Sig} : Ty [] s := .TTyp 0 .TBot .TTop
/-- `x`'s type. -/
abbrev twoMethods {s : Sig} : Ty [] s :=
  .TAnd (.TFun 0 (.TAnd .TTop (.TAnd .TTop (.TAnd .TTop .TTop))) .TTop) (.TFun 0 .TTop memberA)
/-- The literal's self type. -/
abbrev twoCandSelf : Ty [] ([],x) := .TAnd (.TFun 0 twoMethods memberA) .TTop

example : typeAt twoCandTable twoCandSrc = (some (.TBind twoCandSelf), ⟨defaultFuel - 49, false⟩) := by
  decide +kernel

/-! ### A receiver at a union and a receiver at `⊥`

Neither has a method type.  A union has no members, as the compiler's join
of two structural types keeps none.  `⊥` has no members either, as in the
compiler.  Both are rejected with the tank unmarked, so at every fuel. -/

/-- A union receiver. -/
def unionCallSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : ⊤ } ∨ { def f(y : ⊤) : ⊤ }) : ⊤ = x.f(x) }

/-- A receiver at `⊥`. -/
def botCallSrc : STm := o16% new { c ⇒ def g(x : ⊥) : ⊤ = x.f(x) }

/-- The label table of both. -/
def unionCallTable : LabelTable := [("f", 0), ("g", 0)]

example : labelsOfProgram [("f", 0)] unionCallSrc = some unionCallTable := by decide
example : labelsOfProgram [("f", 0)] botCallSrc = some unionCallTable := by decide

example : typeAt unionCallTable unionCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

example : typeAt unionCallTable botCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

theorem unionCall_resolves : (resolve unionCallTable unionCallSrc).isSome = true := by decide

theorem botCall_resolves : (resolve unionCallTable botCallSrc).isSome = true := by decide

/-- The union receiver, resolved. -/
def unionCallAnn : ATm [] := (resolve unionCallTable unionCallSrc).get unionCall_resolves

/-- The receiver at `⊥`, resolved. -/
def botCallAnn : ATm [] := (resolve unionCallTable botCallSrc).get botCall_resolves

/-- The union receiver is rejected at every fuel from the default up. -/
theorem unionCall_rejected (m : Nat) : (synthTopF (defaultFuel + m) unionCallAnn).1 = none := by
  have h1 : (synthTopF defaultFuel unionCallAnn).1.isNone = true := by decide +kernel
  have h2 : (synthTopF defaultFuel unionCallAnn).2 = ⟨defaultFuel - 1, false⟩ := by
    decide +kernel
  exact synthTop?_stable (Prod.ext (Option.isNone_iff_eq_none.mp h1) h2) m

/-- The receiver at `⊥` is rejected at every fuel from the default up. -/
theorem botCall_rejected (m : Nat) : (synthTopF (defaultFuel + m) botCallAnn).1 = none := by
  have h1 : (synthTopF defaultFuel botCallAnn).1.isNone = true := by decide +kernel
  have h2 : (synthTopF defaultFuel botCallAnn).2 = ⟨defaultFuel - 1, false⟩ := by
    decide +kernel
  exact synthTop?_stable (Prod.ext (Option.isNone_iff_eq_none.mp h1) h2) m

/-! ### Packing below a selection and below an intersection -/

/-- The goal is the selection `m.L`, whose lower bound is a recursive type. -/
def packSelSrc : STm :=
  o16% new { m ⇒ type L = μ(w. { type A : ⊤ .. ⊤ })   def g(x : { type A : ⊤ .. ⊤ }) : m.L = x }

/-- The goal is an intersection with a recursive type on its left. -/
def packAndSrc : STm :=
  o16% new { m ⇒ def g(x : { type A : ⊤ .. ⊤ }) : μ(w. { type A : ⊤ .. ⊤ }) ∧ ⊤ = x }

/-- The label table of the first. -/
def packSelTable : LabelTable := [("A", 0), ("L", 1), ("g", 0)]

example : labelsOfProgram [("A", 0)] packSelSrc = some packSelTable := by decide

/-- Below a selection, at the self type `selfP` of `Sub.lean`. -/
example : typeAt packSelTable packSelSrc = (some (.TBind selfP), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- Below an intersection. -/
example : typeAt [("A", 0), ("g", 0)] packAndSrc
    = (some (.TBind (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop))
        .TTop)), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-! ### A call whose codomain keeps a recursive type

`y : {def 1(t : {1 : ⊥..⊤}) : {def 0(a : μ(w. {1 : ⊥..t.1} ∧ {0 : ⊥..w.1})) : ⊤}}`
applied to a literal.  The codomain mentions the parameter `t` under a
recursive type in a method's domain.  The recursive type is kept, and `t.1`
becomes the literal's lower bound `⊤` (`p3_avoided` of `Avoid.lean`). -/

/-- `y.1(new { o ⇒ type 1 = ⊤  type 0 = ⊤ })`, resolved. -/
def p3Call : ATm ([],x) :=
  .app (.var .here) 1 (.obj none (.dcons (.dty .TTop) (.dcons (.dty .TTop) .dnil)))

example : typeInAt ΓAM p3Call = (some recvAM, ⟨defaultFuel - 66, false⟩) := by decide +kernel

end TyperChecks

end Oopsla16Frontend
