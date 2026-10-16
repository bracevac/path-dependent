import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.Frontend.Avoid

/-!
# The typer

The typer reads a type off an annotated term of the calculus and returns the
`Paths.DotMNF.HasTy` derivation with it.  The derivation is a field of the
result, so soundness is the result type and there is no soundness theorem.

It runs on the tank of `Fuel.lean`.  One tank is threaded through every goal
it asks: each goal of `Sub.lean`, each lookup of `Look.lean` and each
avoidance of `Avoid.lean`.  So the fuel counts the work of the whole typing,
and a goal that finds the tank short marks it.  A marked tank is the recursion
limit.  It is never a rejection by the rules.

## Candidates

Synthesis returns a list of candidates, each a type with its derivation, with
no two of one type.  The calculus has no rule that merges two members of one
name, which the compiler does (`TypeBounds.&`).  So the typer keeps every
choice.

- A variable has the type its context declares.
- `λ(x : S). t` has `∀(x : S) T` for every candidate `T` of the body, if `S`
  is well formed.
- `ν(x : T. d)` checks the definitions against `T` under the self binder.
- `x y` tries every function type the term lookup finds in `x`'s declared
  type, and keeps each one whose domain `y` meets.
- `x.a` returns every field at `a` the path lookup finds at `x`, by
  `HasTy.projP`.  The path lookup follows singletons, so a field of `q` is a
  field of `p : q.type`.
- `let x = t in u` without annotation returns every pair of a candidate of
  `t` and a candidate of `u`.  The body's type is approximated by a type free
  of `x` (`avoidLet`), as `TypeOps.avoid` does.  If the result is not well
  formed, the pair takes `⊤`.
- `let x : U = t in u` has the type `U`.  The annotation binds.  The body is
  checked against it and is never approximated.

## Checking

Checking a variable asks the `var` goal of `Sub.lean`, which reaches the rules
that subsumption does not: `HasTy.andI`, `HasTy.recI` and `HasTy.sngl`.  Two
terms pass the type asked for inward, as the compiler passes the expected type
to a closure and to the last expression of a block.  A lambda against a
function type with the same domain checks its body against the codomain.  A
`let` without annotation checks its body against the type asked for, under
the binder at each candidate of the bound term.  Every term, those two
included when their clause fails, takes the first candidate that the
subtyping goal takes to the type asked for.

## The theorems

Every computation here is framed: it keeps a marked tank, never adds fuel,
and does the same with more fuel (`synthF_frame`).  So a typing that ends
unmarked gives the same answer at every larger fuel (`synthTop?_mono`,
`synthTop?_stable`).  A rejection that ends unmarked is a rejection at every
fuel.

The typer has no completeness theorem.  It misses these cases.

- A derivation through a middle type the program does not write.  The compiler
  does not find one either.
- A projection that needs two fields merged.  The calculus has no rule for
  that, so a projection tries each field.
- A widening of a singleton to the type of its alias at a term.  `HasTy` has no
  rule for that.
- A judgment whose search needs more than the fuel.
- A lookup through a cyclic member, which is cut as the compiler's cyclic
  reference.

Every definition is structural on the term, so the kernel evaluates the
typer.  The checks at the end of the module type the example programs at
`defaultFuel` by `decide +kernel`.
-/

namespace PathsFrontend

open Frontend.Fuel PathsFrontend.Core
open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Tm Defs Ctx Sub PathTy HasTy DefsTy)

/-- The fuel of a typing.  One field, the size of the tank every entry point
starts from. -/
structure Budget where
  fuel : Nat := defaultFuel

/-- A type a term has, with the derivation. -/
structure Cand {s : Sig} (Γ : Ctx s) (t : Tm s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ t ty

/-! ## Casts across a decided equality

These use `cases` and not `▸`, because a label occurs twice in the conclusion
of the rule and a rewrite would hit both. -/

/-- A type member definition against a declaration whose two bounds are the
definition's type, as `DefsTy.typ` requires. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {A B : Label} {S L U : Ty s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy Γ (.typ A S) (.typ B L U) := by
  cases hA
  cases hL
  cases hU
  exact .typ

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld c T) := by
  cases h
  exact .trm ht

/-- A member whose body is an object literal against a stable field declared at
the literal's self type, by `DefsTy.trmObj`. -/
def defsObjAt {s : Sig} {Γ : Ctx s} {a c : Label} {d : Defs (s,x)} {T U : Ty (s,x)}
    (h : a = c) (hT : T = U) (hd : DefsTy (Γ.consSelf d T) d T) (hdist : Defs.Distinct d) :
    DefsTy Γ (.trm a (.val (.obj d))) (.vfld c (.mu U)) := by
  cases h
  cases hT
  exact .trmObj hd hdist

/-- A lambda checked against a function type with the same domain. -/
def lamAt {s : Sig} {Γ : Ctx s} {S S' : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (h : S = S') (ht : HasTy (Γ.cons S) t T) (hwf : Ty.Wf S) :
    HasTy Γ (.val (.lam S t)) (.all S' T) := by
  cases h
  exact .lam ht hwf

/-- `⊤` is its own weakening.  The fallback of a `let` whose avoided type is
not well formed needs this. -/
theorem weaken_top {s : Sig} {k : Kind} : (Ty.top : Ty s).weaken (k := k) = .top := rfl

/-! ## Pieces the clauses use -/

/-- Keep the first candidate of each type. -/
def dedupTy {s : Sig} {Γ : Ctx s} {t : Tm s} : List (Cand Γ t) → List (Cand Γ t)
  | [] => []
  | c :: cs => c :: (dedupTy cs).filter fun c' => !decide (c'.ty = c.ty)

/-- An optional answer as a list of at most one. -/
def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

/-- The types of a variable as a term that carry the key, looked up from its
declared type.  The index of the lookup is the fuel left. -/
def lookVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Fu (List (FoundV Γ x (Γ.lookup x))) :=
  fun t => lookV Γ t.left [] x (Γ.lookup x) k t

/-- The candidates of a lambda, from the candidates of its body.  The domain
must be well formed, as `HasTy.lam` asks. -/
def lamC {s : Sig} {Γ : Ctx s} (S : Ty s) {t : Tm (s,x)} (cs : Fu (List (Cand (Γ.cons S) t))) :
    Fu (List (Cand Γ (.val (.lam S t)))) :=
  if hwf : Ty.Wf S then
    Fu.bind cs fun l => Fu.ret (l.map fun c => ⟨.all S c.ty, .lam c.deriv hwf⟩)
  else Fu.ret []

/-- The candidate of an object literal, from the check of its definitions.
The labels must be distinct, as `HasTy.obj` asks. -/
def objC {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {T : Ty (s,x)}
    (hd : Fu (Option (DefsTy (Γ.consSelf d T) d T))) : Fu (List (Cand Γ (.val (.obj d)))) :=
  Fu.bind hd fun
    | some hd => Fu.ret (if hdist : Defs.Distinct d then [⟨.mu T, .obj hd hdist⟩] else [])
    | none => Fu.ret []

/-- The candidates of `x y`: every function type the term lookup finds at `x`
whose domain `y` meets. -/
def appC {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Fu (List (Cand Γ (.app x y))) :=
  Fu.bind (lookVar Γ x .fn) fun es =>
    Fu.bind (Fu.flatMapL (fun e =>
        match e.all? with
        | some ⟨S, T, f⟩ =>
            Fu.bind (varF Γ y S) fun o =>
              Fu.ret (listO (o.map fun hy => (⟨T.substVar y, .app (f .var) hy⟩ : Cand Γ (.app x y))))
        | none => Fu.ret []) es) fun cs =>
      Fu.ret (dedupTy cs)

/-- The candidates of `x.a`: every field at `a` the path lookup finds at `x`,
by `HasTy.projP`. -/
def projC {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) : Fu (List (Cand Γ (.proj x a))) :=
  Fu.bind (lookF Γ (.var x) (Γ.lookup x) (.fld a)) fun es =>
    Fu.ret (dedupTy (es.filterMap fun e =>
      (e.fld? a).map fun r => (⟨r.1, .projP (r.2 .var)⟩ : Cand Γ (.proj x a))))

/-- The candidate of a `let` without annotation, from one candidate of the
bound term and one of the body: the body's type avoided.  If the avoided type
is not well formed, the candidate is `⊤`.  None if the tank ends marked. -/
def letAvoidC {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1 : Cand Γ t)
    (c2 : Cand (Γ.cons c1.ty) u) : Fu (List (Cand Γ (.let t u))) :=
  Fu.bind (avoidLet Γ c1.ty c2.ty) fun
    | some r =>
        Fu.ret [if hwf : Ty.Wf r.1 then ⟨r.1, r.hasTy c1.deriv c2.deriv hwf⟩
          else ⟨.top, .let c1.deriv (weaken_top ▸ HasTy.sub c2.deriv Sub.top) .top⟩]
    | none => Fu.ret []

/-- The candidates of a `let` without annotation: every pair of a candidate of
the bound term and a candidate of the body, the body typed under the binder at
the first one. -/
def letNoneC {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1s : List (Cand Γ t))
    (synthU : (T0 : Ty s) → Fu (List (Cand (Γ.cons T0) u))) : Fu (List (Cand Γ (.let t u))) :=
  Fu.bind (Fu.flatMapL (fun c1 => Fu.bind (synthU c1.ty) (Fu.flatMapL (letAvoidC c1))) c1s)
    fun cs => Fu.ret (dedupTy cs)

/-- The candidate of a `let` with annotation `U`: the first candidate of the
bound term under which the body checks against `U`.  `U` must be well formed,
as `HasTy.let` asks. -/
def letAnnC {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (U : Ty s) (c1s : List (Cand Γ t))
    (checkU : (T0 : Ty s) → Fu (Option (HasTy (Γ.cons T0) u U.weaken))) :
    Fu (List (Cand Γ (.let t u))) :=
  if hwf : Ty.Wf U then
    Fu.bind (Fu.firstSome (fun c1 =>
        mapO (checkU c1.ty) fun h2 => (⟨U, .let c1.deriv h2 hwf⟩ : Cand Γ (.let t u))) c1s) fun o =>
      Fu.ret (listO o)
  else Fu.ret []

/-- A lambda against a function type with the same domain: the body checked
against the codomain.  The domain must be well formed, as `HasTy.lam` asks. -/
def lamCheckC {s : Sig} {Γ : Ctx s} (S : Ty s) {t : Tm (s,x)} (T : Ty s)
    (checkB : (T' : Ty (s,x)) → Fu (Option (HasTy (Γ.cons S) t T'))) :
    Fu (Option (HasTy Γ (.val (.lam S t)) T)) :=
  match T with
  | .all S' T' =>
      if h : S = S' then
        if hwf : Ty.Wf S then mapO (checkB T') fun ht => lamAt h ht hwf else Fu.ret none
      else Fu.ret none
  | _ => Fu.ret none

/-- A `let` without annotation against `T`: the body checked against `T` under
the binder at the first candidate of the bound term for which it checks.  `T`
must be well formed, as `HasTy.let` asks. -/
def letCheckC {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (T : Ty s) (c1s : List (Cand Γ t))
    (checkU : (T0 : Ty s) → Fu (Option (HasTy (Γ.cons T0) u T.weaken))) :
    Fu (Option (HasTy Γ (.let t u) T)) :=
  if hwf : Ty.Wf T then
    Fu.firstSome (fun c1 => mapO (checkU c1.ty) fun h2 => HasTy.let c1.deriv h2 hwf) c1s
  else Fu.ret none

/-- The first candidate that the subtyping goal takes to `T`, through
`HasTy.sub`. -/
def toGoalC {s : Sig} {Γ : Ctx s} {t : Tm s} (T : Ty s) (cs : Fu (List (Cand Γ t))) :
    Fu (Option (HasTy Γ t T)) :=
  Fu.bind cs fun l => Fu.firstSome (fun c => mapO (subF Γ c.ty T) fun e => HasTy.sub c.deriv e) l

/-! ## Synthesis and checking

Three functions, structural on the term.  `synthF` returns the candidates of a
term.  `checkF` checks a term against a type.  `checkDefsF` matches a
definition list against a type in lockstep, as `DefsTy` does: a type member
against a declaration with its type on both bounds, a member whose body is an
object literal against a stable field at the literal's self type, a term
member against a field at the same label, an intersection against an
intersection.  Each clause that needs the candidates of its own term builds
them from its subterms, so every call is on a subterm. -/

mutual

/-- The candidates of a term, each with its derivation, on the tank. -/
def synthF {s : Sig} (Γ : Ctx s) : (a : ATm s) → Fu (List (Cand Γ a.erase))
  | .path x => Fu.ret [⟨Γ.lookup x, .var⟩]
  | .lam S t => lamC S (synthF (Γ.cons S) t)
  | .obj T d => objC (checkDefsF (Γ.consSelf d.erase T) d T)
  | .app x y => appC Γ x y
  | .proj x a => projC Γ x a
  | .let (some U) t u =>
      Fu.bind (synthF Γ t) fun c1s => letAnnC U c1s fun T0 => checkF (Γ.cons T0) u U.weaken
  | .let none t u =>
      Fu.bind (synthF Γ t) fun c1s => letNoneC c1s fun T0 => synthF (Γ.cons T0) u

/-- A term checked against `T`, on the tank. -/
def checkF {s : Sig} (Γ : Ctx s) : (a : ATm s) → (T : Ty s) → Fu (Option (HasTy Γ a.erase T))
  | .path x, T => varF Γ x T
  | .lam S t, T =>
      Fu.orElse (lamCheckC S T fun T' => checkF (Γ.cons S) t T') fun _ =>
        toGoalC T (lamC S (synthF (Γ.cons S) t))
  | .obj T0 d, T => toGoalC T (objC (checkDefsF (Γ.consSelf d.erase T0) d T0))
  | .app x y, T => toGoalC T (appC Γ x y)
  | .proj x a, T => toGoalC T (projC Γ x a)
  | .let (some U) t u, T =>
      toGoalC T (Fu.bind (synthF Γ t) fun c1s =>
        letAnnC U c1s fun T0 => checkF (Γ.cons T0) u U.weaken)
  | .let none t u, T =>
      Fu.bind (synthF Γ t) fun c1s =>
        Fu.orElse (letCheckC T c1s fun T0 => checkF (Γ.cons T0) u T.weaken) fun _ =>
          toGoalC T (letNoneC c1s fun T0 => synthF (Γ.cons T0) u)

/-- A definition list against a type, in lockstep. -/
def checkDefsF {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (T : Ty s) →
    Fu (Option (DefsTy Γ d.erase T))
  | .typ A S, .typ B L U =>
      Fu.ret (if hA : A = B then
        if hL : S = L then
          if hU : S = U then some (defsTypAt hA hL hU) else none
        else none
      else none)
  | .trm a t, .vfld c V =>
      match t, V with
      | .obj T' d', .mu U =>
          if h : a = c then
            if hT : T' = U then
              bindO (checkDefsF (Γ.consSelf d'.erase T') d' T') fun hd =>
                Fu.ret (if hdist : Defs.Distinct d'.erase then some (defsObjAt h hT hd hdist)
                  else none)
            else Fu.ret none
          else Fu.ret none
      | _, _ => Fu.ret none
  | .trm a t, .fld c U =>
      if h : a = c then mapO (checkF Γ t U) (defsTrmAt h) else Fu.ret none
  | .and d1 d2, .and T1 T2 =>
      bindO (checkDefsF Γ d1 T1) fun h1 =>
        mapO (checkDefsF Γ d2 T2) fun h2 => DefsTy.and h1 h2
  | _, _ => Fu.ret none

end

/-! ## The entry points -/

/-- The first candidate, and `none` if the tank ended marked. -/
def firstCand {α : Type} : List α × Tank → Option α × Tank
  | (c :: _, t) => if t.out then (none, t) else (some c, t)
  | ([], t) => (none, t)

/-- The first candidate of a term in `Γ`, from a full tank of `n` units, with
the tank left. -/
def synthInF {s : Sig} (Γ : Ctx s) (a : ATm s) (n : Nat) : Option (Cand Γ a.erase) × Tank :=
  firstCand (synthF Γ a ⟨n, false⟩)

/-- The first candidate of a closed term, from a full tank of `n` units, with
the tank left. -/
def synthTopF (n : Nat) (a : ATm []) : Option (Cand Ctx.nil a.erase) × Tank :=
  synthInF Ctx.nil a n

/-- A type of a term in `Γ`, at the budget's fuel. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Cand Γ a.erase) :=
  (synthInF Γ a b.fuel).1

/-- A type of a closed term, at the budget's fuel. -/
def synthTop? (b : Budget) (a : ATm []) : Option (Cand Ctx.nil a.erase) :=
  (synthTopF b.fuel a).1

/-! ## The frame lemmas

Each clause is built from the combinators of `Fuel.lean` and from framed
computations of the other modules: `subF`, `varF`, `avoidLet` and the
lookups.  So each clause is framed, by induction on the term. -/

/-- A term lookup at a larger index does what the lookup at a smaller one
does. -/
theorem lookV_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ (P : List (LKey s)) (x : BVar s .var) (V : Ty s) (k : Key),
      Agree (lookV Γ d P x V k) (lookV Γ d' P x V k)
  | 0, d', _, P, x, V, k => by
    refine ⟨lookV_framed Γ 0 P x V k, lookV_framed Γ d' P x V k, ?_⟩
    intro t r t' h ho _
    simp only [lookV, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, x, V, k => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := lookV_agree Γ d e (by omega)
    have ihP := lookP_agree Γ d e (by omega)
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply ite_agree (ret_agree _)
      cases V with
      | mu B =>
        exact dite_agree (fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _)
          (fun _ => ret_agree _)
      | and V1 V2 =>
        exact bind_agree (ih _ _ _ _) fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _
      | sel q B =>
        exact bind_agree (declsAt_agree (ihP _) _ _) (flatMapL_agree fun _ =>
          bind_agree (ih _ _ _ _) fun _ => ret_agree _)
      | sngl _ => exact ret_agree _
      | top => exact ret_agree _
      | bot => exact ret_agree _
      | typ _ _ _ => exact ret_agree _
      | fld _ _ => exact ret_agree _
      | vfld _ _ => exact ret_agree _
      | all _ _ => exact ret_agree _

/-- The term lookup from the fuel left is framed. -/
theorem lookVar_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Framed (lookVar Γ x k) :=
  atLeft_framed fun d d' hd => lookV_agree Γ d d' hd [] x (Γ.lookup x) k

theorem lamC_framed {s : Sig} {Γ : Ctx s} (S : Ty s) {t : Tm (s,x)}
    {cs : Fu (List (Cand (Γ.cons S) t))} (hcs : Framed cs) : Framed (lamC S cs) :=
  dite_framed (fun _ => bind_framed hcs fun _ => ret_framed _) (fun _ => ret_framed _)

theorem objC_framed {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {T : Ty (s,x)}
    {hd : Fu (Option (DefsTy (Γ.consSelf d T) d T))} (h : Framed hd) : Framed (objC hd) :=
  bind_framed h fun
    | some _ => ret_framed _
    | none => ret_framed _

theorem appC_framed {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Framed (appC Γ x y) := by
  refine bind_framed (lookVar_framed _ _ _) fun es => bind_framed (flatMapL_framed ?_ es)
    fun _ => ret_framed _
  intro e
  dsimp only
  split
  · exact bind_framed (varF_framed _ _ _) fun _ => ret_framed _
  · exact ret_framed _

theorem projC_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) :
    Framed (projC Γ x a) :=
  bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _

theorem letAvoidC_framed {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1 : Cand Γ t)
    (c2 : Cand (Γ.cons c1.ty) u) : Framed (letAvoidC c1 c2) :=
  bind_framed (avoidLet_framed _ _ _) fun
    | some _ => ret_framed _
    | none => ret_framed _

theorem letNoneC_framed {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1s : List (Cand Γ t))
    {synthU : (T0 : Ty s) → Fu (List (Cand (Γ.cons T0) u))} (h : ∀ T0, Framed (synthU T0)) :
    Framed (letNoneC c1s synthU) :=
  bind_framed (flatMapL_framed (fun c1 =>
    bind_framed (h _) (flatMapL_framed (letAvoidC_framed c1))) c1s) fun _ => ret_framed _

theorem letAnnC_framed {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (U : Ty s)
    (c1s : List (Cand Γ t)) {checkU : (T0 : Ty s) → Fu (Option (HasTy (Γ.cons T0) u U.weaken))}
    (h : ∀ T0, Framed (checkU T0)) : Framed (letAnnC U c1s checkU) :=
  dite_framed (fun _ => bind_framed (firstSome_framed (fun _ => mapO_framed _ (h _)) c1s)
    fun _ => ret_framed _) (fun _ => ret_framed _)

theorem lamCheckC_framed {s : Sig} {Γ : Ctx s} (S : Ty s) {t : Tm (s,x)} (T : Ty s)
    {checkB : (T' : Ty (s,x)) → Fu (Option (HasTy (Γ.cons S) t T'))}
    (h : ∀ T', Framed (checkB T')) : Framed (lamCheckC S T checkB) := by
  cases T with
  | all S' T' =>
    exact dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (h _)) (fun _ => ret_framed _))
      (fun _ => ret_framed _)
  | _ => exact ret_framed _

theorem letCheckC_framed {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (T : Ty s)
    (c1s : List (Cand Γ t)) {checkU : (T0 : Ty s) → Fu (Option (HasTy (Γ.cons T0) u T.weaken))}
    (h : ∀ T0, Framed (checkU T0)) : Framed (letCheckC T c1s checkU) :=
  dite_framed (fun _ => firstSome_framed (fun _ => mapO_framed _ (h _)) c1s) (fun _ => ret_framed _)

theorem toGoalC_framed {s : Sig} {Γ : Ctx s} {t : Tm s} (T : Ty s) {cs : Fu (List (Cand Γ t))}
    (hcs : Framed cs) : Framed (toGoalC T cs) :=
  bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l

mutual

theorem synthF_framed {s : Sig} (Γ : Ctx s) : (a : ATm s) → Framed (synthF Γ a)
  | .path x => by
    rw [synthF]
    exact ret_framed _
  | .lam S t => by
    rw [synthF]
    exact lamC_framed S (synthF_framed _ t)
  | .obj T d => by
    rw [synthF]
    exact objC_framed (checkDefsF_framed _ d T)
  | .app x y => by
    rw [synthF]
    exact appC_framed Γ x y
  | .proj x a => by
    rw [synthF]
    exact projC_framed Γ x a
  | .let (some U) t u => by
    rw [synthF]
    exact bind_framed (synthF_framed Γ t) fun c1s =>
      letAnnC_framed U c1s fun _ => checkF_framed _ u _
  | .let none t u => by
    rw [synthF]
    exact bind_framed (synthF_framed Γ t) fun c1s =>
      letNoneC_framed c1s fun _ => synthF_framed _ u

theorem checkF_framed {s : Sig} (Γ : Ctx s) : (a : ATm s) → (T : Ty s) → Framed (checkF Γ a T)
  | .path x, T => by
    rw [checkF]
    exact varF_framed Γ x T
  | .lam S t, T => by
    rw [checkF]
    exact orElse_framed (lamCheckC_framed S T fun T' => checkF_framed _ t T')
      (toGoalC_framed T (lamC_framed S (synthF_framed _ t)))
  | .obj T0 d, T => by
    rw [checkF]
    exact toGoalC_framed T (objC_framed (checkDefsF_framed _ d T0))
  | .app x y, T => by
    rw [checkF]
    exact toGoalC_framed T (appC_framed Γ x y)
  | .proj x a, T => by
    rw [checkF]
    exact toGoalC_framed T (projC_framed Γ x a)
  | .let (some U) t u, T => by
    rw [checkF]
    exact toGoalC_framed T (bind_framed (synthF_framed Γ t) fun c1s =>
      letAnnC_framed U c1s fun _ => checkF_framed _ u _)
  | .let none t u, T => by
    rw [checkF]
    exact bind_framed (synthF_framed Γ t) fun c1s =>
      orElse_framed (letCheckC_framed T c1s fun _ => checkF_framed _ u _)
        (toGoalC_framed T (letNoneC_framed c1s fun _ => synthF_framed _ u))

theorem checkDefsF_framed {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (T : Ty s) →
    Framed (checkDefsF Γ d T)
  | .typ A S, T => by
    cases T with
    | typ B L U =>
      rw [checkDefsF]
      exact ret_framed _
    | _ => exact ret_framed _
  | .trm a t, T => by
    cases T with
    | vfld c V =>
      cases t with
      | obj T' d' =>
        cases V with
        | mu U =>
          rw [checkDefsF]
          exact dite_framed (fun _ => dite_framed
            (fun _ => bindO_framed (checkDefsF_framed _ d' T') fun _ => ret_framed _)
            (fun _ => ret_framed _)) (fun _ => ret_framed _)
        | _ => exact ret_framed _
      | _ => exact ret_framed _
    | fld c U =>
      rw [checkDefsF]
      exact dite_framed (fun _ => mapO_framed _ (checkF_framed _ t U)) (fun _ => ret_framed _)
    | _ => exact ret_framed _
  | .and d1 d2, T => by
    cases T with
    | and T1 T2 =>
      rw [checkDefsF]
      exact bindO_framed (checkDefsF_framed _ d1 T1) fun _ => mapO_framed _ (checkDefsF_framed _ d2 T2)
    | _ => exact ret_framed _

end

/-- A typing that ends unmarked does the same with more fuel. -/
theorem synthF_frame {s : Sig} {Γ : Ctx s} {a : ATm s} {t t' : Tank}
    {r : List (Cand Γ a.erase)} (h : synthF Γ a t = (r, t')) (ho : t'.out = false) (k : Nat) :
    synthF Γ a (t.add k) = (r, t'.add k) :=
  (synthF_framed Γ a).shift t r t' h ho k

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
  | cons c l => cases ht : t.out <;> simp [firstCand, ht, Tank.add]

/-- The tank `firstCand` leaves is the one it is handed. -/
theorem firstCand_snd {α : Type} (r : List α × Tank) : (firstCand r).2 = r.2 := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, ht]

theorem synthInF_stable {s : Sig} {Γ : Ctx s} {a : ATm s} {n k : Nat} {r : Option (Cand Γ a.erase)}
    (h : synthInF Γ a n = (r, ⟨k, false⟩)) (m : Nat) : (synthInF Γ a (n + m)).1 = r := by
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

theorem synthInF_mono {s : Sig} {Γ : Ctx s} {a : ATm s} {n m : Nat} {c : Cand Γ a.erase}
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
fuel.  So a rejection of the typer's search that ends unmarked stays a
rejection at every larger fuel. -/
theorem synthTop?_stable {n k : Nat} {a : ATm []} {r : Option (Cand Ctx.nil a.erase)}
    (h : synthTopF n a = (r, ⟨k, false⟩)) (m : Nat) : (synthTopF (n + m) a).1 = r :=
  synthInF_stable h m

/-! ## Checks

Each check types a surface program at `defaultFuel` in the kernel.  It states
the type, or that there is none, and the tank left.  An unmarked tank says
that the fuel played no part in the verdict.  A rejection with the tank
unmarked holds at every fuel (`synthTop?_stable`).

X3, E6 and X4 are typed in `Paths.DotMNF.Examples` under a context.  Here they
are written closed, the context entry becomes a lambda, and the expected type
is the original type under one `∀`. -/

section TyperChecks

open Paths.DotMNF.Examples

/-- The type a derivation concludes. -/
def versionTy {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Ty s := T

/-- The type of a closed program after resolution, from a full tank of `n`
units, with the tank left. -/
def typeAt (e : STm) (n : Nat := defaultFuel) : Option (Ty []) × Tank :=
  match resolve pathsTable e with
  | some a => ((synthTopF n a).1.map (·.ty), (synthTopF n a).2)
  | none => (none, ⟨n, true⟩)

/-- The type Fig. 1 synthesizes: the self type of `pcore`, strengthened past the
binder of `o`. -/
def Fig1_ty : Ty [] := (tyStrengthen? (Ty.mu Fig1_pBody)).getD .bot

/-- `∀(f : ⊤) ∀(g : ⊤) ∀(m : {A : f.type..g.type}) ∀(x : f.type) g.type`. -/
def R1_ty : Ty [] :=
  .all .top (.all .top (.all (.typ lA (.sngl (.var (.there .here))) (.sngl (.var .here)))
    (.all (.sngl (.var (.there (.there .here)))) (.sngl (.var (.there (.there .here)))))))

/-- `∀(z : ⊤) ⊤`, the function type R2 aliases. -/
def R2_F {s : Sig} : Ty s := .all .top .top

/-- `∀(f : F) ∀(p : {A : f.type..F}) ∀(x : f.type) ∀(h : ∀(k : F) ⊤) ⊤`. -/
def R2_ty : Ty [] :=
  .all R2_F (.all (.typ lA (.sngl (.var .here)) R2_F)
    (.all (.sngl (.var (.there .here))) (.all (.all R2_F .top) .top)))

/-- E2 and E2p after avoidance: `∀(y : ∀(z : ⊤) ⊥) ⊤`. -/
def E2_avoided : Ty [] := .all (.all .top .bot) .top

/-- E11 after avoidance through the abstract view:
`μ(x. {val a : μ(y. {A : ⊤..⊤})} ∧ {b : ⊤})`. -/
def E11_avoided : Ty [] := .mu (.and (.vfld la (.mu (.typ lA .top .top))) (.fld lb .top))

/-- Fig. 2 after avoidance through the abstract view: the member `symbols`
mentions `o` and is widened to `⊤`, the member `types` is kept. -/
def Fig2_avoided : Ty [] :=
  .mu (.and (.vfld Fig2_ltypes (.mu (X4_Body .here (.there .here)))) (.vfld X4_lsymbols .top))

/-- E1 with the middle written.  A `let` annotation types the whole `let`, so
`let t : T = x in t` ascribes `T` to `x`. -/
def E1s_src : STm :=
  pdot% λ(x : {A : ⊤..⊥}).
    let y : {B : {a : ⊤} .. {a : ⊤}} = (let u : x.A = (let t : ⊤ = x in t) in u) in y

/-- E3 with the middle written, by the same ascription. -/
def E3s_src : STm :=
  pdot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}). λ(z : {b : ⊤}).
    let y : {a : ⊤} = (let u : x.A = z in u) in y

/-- E1p with the middle `w.f.A` written. -/
def E1ps_src : STm :=
  pdot% λ(w : {val f : {A : ⊤..⊥}}).
    let y : {B : {a : ⊤} .. {a : ⊤}} = (let u : w.f.A = (let t : ⊤ = w in t) in u) in y

/-- R1 with the middle `m.A` written. -/
def R1s_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
    let y : g.type = (let u : m.A = x in u) in y

/-- R2 with the middle `p.A` written. -/
def R2s_src : STm :=
  pdot% λ(f : ∀(z : ⊤) ⊤). λ(p : {A : f.type .. ∀(z : ⊤) ⊤}). λ(x : f.type).
    λ(h : ∀(k : ∀(z : ⊤) ⊤) ⊤). h (let u : p.A = x in u)

/-- A member six stable fields down. -/
def PD6_src : STm :=
  pdot% λ(x : {val b : {val b : {val b : {val b : {val b : {val b : {A : ⊥ .. {a : ⊤}}}}}}}}).
    λ(y : x.b.b.b.b.b.b.A). y.a

/-- A member three stable fields down, in a codomain, at a `let` annotation. -/
def PF3_src : STm :=
  pdot% λ(f : ∀(y : {val b : {val b : {val b : {A : ⊥ .. {a : ⊤}}}}}) y.b.b.b.A).
    let g : ∀(y : {val b : {val b : {val b : {A : ⊥ .. {a : ⊤}}}}}) {a : ⊤} = f in g

/-- The subtyping of PF3 at an argument. -/
def PF3h_src : STm :=
  pdot% λ(f : ∀(y : {val b : {val b : {val b : {A : ⊥ .. {a : ⊤}}}}}) y.b.b.b.A).
    λ(h : ∀(k : ∀(y : {val b : {val b : {val b : {A : ⊥ .. {a : ⊤}}}}}) {a : ⊤}) ⊤). h f

/-- A function at an intersection of two function types, applied to an
argument only the second accepts. -/
def P5_src : STm := pdot% λ(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). λ(y : ⊤). f y

/-- A projection with two fields, the first through `x.A`'s upper bound.  Only
the second has the member `b`. -/
def PR_src : STm :=
  pdot% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A projection with two written fields.  Only the second has the member `b`. -/
def PR2_src : STm := pdot% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A written `let` annotation that the bound value does not meet. -/
def A1_src : STm := pdot% λ(x : ⊤). let y : {a : ⊤} = x in y

/-- A field reached only through a middle the program does not write:
`n : {a : ⊤}` below `x.A`, and `x.A` below `{b : ⊤}`. -/
def B1_src : STm := pdot% λ(x : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}). n.b

/-- The inner `let` of G: `z.v` has the type `z.A`, which avoidance replaces by
the meet of the upper bounds of `z`'s two members `A`. -/
def Gin_src : STm :=
  pdot% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})).
    λ(w : ⊤). let z = f w in z.v

/-- G: the inner `let`, then the member `b` of its type. -/
def G_src : STm :=
  pdot% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})).
    λ(w : ⊤). let r = (let z = f w in z.v) in r.b

/-- Ga: the inner `let`, then the member `a` of its type. -/
def Ga_src : STm :=
  pdot% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})).
    λ(w : ⊤). let r = (let z = f w in z.v) in r.a

/-- Avoidance of `y : q.type` where `q.B` is abstract. -/
def AVp_src : STm :=
  pdot% λ(q : {B : ⊥ .. ⊤}). let x = ν(x : {a : q.type}. {a = q}) in let y = x.a in λ(z : y.B). z

/-- `p : q.type` and `x : p.A` used at `q.A`, `A` abstract.  The calculus has no
rule that compares the two prefixes. -/
def PQ_src : STm :=
  pdot% λ(q : {A : ⊥ .. ⊤}). λ(p : q.type). λ(x : p.A). let y : q.A = x in y

/-- A field of `q`'s self type read at `p : q.type`, at a written annotation. -/
def MuP_src : STm :=
  pdot% λ(q : μ(s. {A : ⊥ .. ⊤} ∧ {a : s.A})). λ(p : q.type). let z : p.A = p.a in z

/-- The same field passed to a function that asks for `p.A`. -/
def MuPh_src : STm :=
  pdot% λ(q : μ(s. {A : ⊥ .. ⊤} ∧ {a : s.A})). λ(p : q.type). λ(h : ∀(w : p.A) ⊤).
    let z = p.a in h z

/-- A member of `q`'s self type read at `p : q.type`, at a written annotation
that names `p`. -/
def MuS_src : STm :=
  pdot% λ(q : μ(s. {A : ⊥ .. {B : s.C .. s.C}} ∧ {C : ⊥ .. ⊤})). λ(p : q.type). λ(x : p.A).
    let y : {B : p.C .. p.C} = x in y

/-- A check through `∀` bodies that never ends: `x : p.A` against `q.B`. -/
def LPt_src : STm :=
  pdot% λ(p : μ(s. {A : ⊥ .. ∀(y : ⊤) s.A})). λ(q : μ(s. {B : ∀(y : ⊤) s.B .. ⊤})).
    λ(x : p.A). let y : q.B = x in y

/-- `{val b : … {val b : T}}`, `n` stable fields deep. -/
def bChain {s : Sig} : Nat → Ty s → Ty s
  | 0, T => T
  | n + 1, T => .vfld lb (bChain n T)

/-- `p.b.b…b`, `n` selections of `b` after `p`. -/
def bPath {s : Sig} : Nat → Path s → Path s
  | 0, p => p
  | n + 1, p => .sel (bPath n p) lb

/-- `{A : ⊥..{a : ⊤}}`, the member at the bottom of the chains. -/
def AMem {s : Sig} : Ty s := .typ lA .bot (.fld la .top)

/-- The domain of PF3: the member `A` three stable fields down. -/
def PF3Dom {s : Sig} : Ty s := bChain 3 AMem

/-- The function of PF3: `∀(y : PF3Dom) y.b.b.b.A`. -/
def PF3Fun {s : Sig} : Ty s := .all PF3Dom (.sel (bPath 3 (.var .here)) lA)

/-- The function type of G: its result has two members `A` and a field at one
of them. -/
def GFun : Ty [] :=
  .all .top (.mu (.and (.and (.typ lA .bot (.fld la .top)) (.typ lA .bot (.fld lb .top)))
    (.fld lv (.sel (.var .here) lA))))

-- The programs of `Notation.lean`.  E1, E3, E4 and their path twins need a middle the program does
-- not write, and the typer chooses none.  E2, E2p, E9, E11 and Fig. 2 come out at their avoided
-- types.  R1 and R2 need a middle too, and R7 loses the singleton at its inserted `let`.
example : typeAt E1_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E2_src = (some E2_avoided, ⟨defaultFuel - 58, false⟩) := by decide +kernel
example : typeAt E3_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E4_src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel
example : typeAt E5_src = (some (versionTy E5), ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt E6_src = (some (.all E6Int (versionTy E6)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel
example : typeAt E7_src = (some (versionTy E7), ⟨defaultFuel, false⟩) := by decide +kernel
example : typeAt E8_src = (some (versionTy E8), ⟨defaultFuel - 11, false⟩) := by decide +kernel
example : typeAt E1p_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E2p_src = (some E2_avoided, ⟨defaultFuel - 71, false⟩) := by decide +kernel
example : typeAt E3p_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E4p_src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel
example : typeAt E5p_src = (some (versionTy E5p), ⟨defaultFuel - 18, false⟩) := by decide +kernel
example : typeAt E6p_src = (some (versionTy E6p), ⟨defaultFuel - 15, false⟩) := by decide +kernel
example : typeAt E7p_src = (some (versionTy E7p_lit), ⟨defaultFuel, false⟩) := by decide +kernel
example : typeAt E8p_src = (some (versionTy E8p), ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt X1_src = (some (versionTy (X1_lit (Γ := Ctx.nil))), ⟨defaultFuel, false⟩) := by
  decide +kernel
example : typeAt X2_src = (some (versionTy (X2_lit (Γ := Ctx.nil))), ⟨defaultFuel - 4, false⟩) := by
  decide +kernel
example : typeAt X3_src = (some (.all X3_A (versionTy X3)), ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : typeAt X4_src = (some (.all .top (versionTy X4_lit0)), ⟨defaultFuel - 191, false⟩) := by
  decide +kernel
example : typeAt E9_src = (some (.all E9_N E9_N), ⟨defaultFuel - 28, false⟩) := by decide +kernel
example : typeAt E11_src = (some E11_avoided, ⟨defaultFuel - 4, false⟩) := by decide +kernel
example : typeAt P3e_src = (some (versionTy P3e_lit), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : typeAt Fig1_src = (some Fig1_ty, ⟨defaultFuel - 242, false⟩) := by decide +kernel
example : typeAt Fig2_src = (some Fig2_avoided, ⟨defaultFuel - 242, false⟩) := by decide +kernel
example : typeAt R1_src = (none, ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt R2_src = (none, ⟨defaultFuel - 4, false⟩) := by decide +kernel
example : typeAt R7_src = (none, ⟨defaultFuel - 46, false⟩) := by decide +kernel

/-- The body of a closed program under its outer lambda, typed at a context,
from a full tank of `n` units, with the tank left. -/
def bodyTypeAt (Γ : Ctx ([],x)) (e : STm) (n : Nat := defaultFuel) : Option (Ty ([],x)) × Tank :=
  match resolve pathsTable e with
  | some (.lam _ a) => ((synthInF Γ a n).1.map (·.ty), (synthInF Γ a n).2)
  | _ => (none, ⟨n, true⟩)

-- X3, E6 and X4 at the contexts of `Paths.DotMNF.Examples`, through `synthInF`.
example : bodyTypeAt X3_Ctx X3_src = (some (versionTy X3), ⟨defaultFuel - 3, false⟩) := by
  decide +kernel
example : bodyTypeAt E6Ctx1 E6_src = (some (versionTy E6), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel
example : bodyTypeAt X4_Ctx X4_src = (some (versionTy X4_lit0), ⟨defaultFuel - 191, false⟩) := by
  decide +kernel

-- The middles written.
example : typeAt E1s_src = (some (versionTy E1), ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt E3s_src = (some (versionTy E3), ⟨defaultFuel - 16, false⟩) := by decide +kernel
example : typeAt E1ps_src = (some (versionTy E1p), ⟨defaultFuel - 16, false⟩) := by decide +kernel
example : typeAt R1s_src = (some R1_ty, ⟨defaultFuel - 12, false⟩) := by decide +kernel
example : typeAt R2s_src = (some R2_ty, ⟨defaultFuel - 10, false⟩) := by decide +kernel

-- Deep paths, and every function type and every field a candidate.
example : typeAt PD6_src =
    (some (.all (bChain 6 AMem) (.all (.sel (bPath 6 (.var .here)) lA) .top)),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : typeAt PF3_src =
    (some (.all PF3Fun (.all PF3Dom (.fld la .top))), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : typeAt PF3h_src =
    (some (.all PF3Fun (.all (.all (.all PF3Dom (.fld la .top)) .top) .top)),
      ⟨defaultFuel - 18, false⟩) := by
  decide +kernel
example : typeAt P5_src =
    (some (.all (.and (.all (.fld la .top) .top) (.all .top .top)) (.all .top .top)),
      ⟨defaultFuel - 9, false⟩) := by
  decide +kernel
example : typeAt PR_src =
    (some (.all AMem (.all (.and (.sel (.var .here) lA) (.fld la (.fld lb .top))) .top)),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel
example : typeAt PR2_src =
    (some (.all (.and (.fld la .top) (.fld la (.fld lb .top))) .top), ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

-- A written annotation binds, and the middle of B1 is not written.
example : typeAt A1_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt B1_src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- G and Ga: avoidance meets the two upper bounds, and each member is found in the meet.
example : typeAt Gin_src =
    (some (.all GFun (.all .top (.and (.fld la .top) (.fld lb .top)))), ⟨defaultFuel - 41, false⟩) := by
  decide +kernel
example : typeAt G_src = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel
example : typeAt Ga_src = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

-- AVp: the member of `q` is abstract, so the domain takes its lower bound and the codomain its
-- upper bound.  PQ needs a rule the calculus does not have.
example : typeAt AVp_src =
    (some (.all (.typ lB .bot .top) (.all .bot .top)), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel
example : typeAt PQ_src = (none, ⟨defaultFuel - 12, false⟩) := by decide +kernel

-- MuP, MuPh and MuS: a member of `q`'s self type read through `p : q.type` keeps the path `p`.
example : typeAt MuP_src =
    (some (.all (.mu MuPBody) (.all (.sngl (.var .here)) (.sel (.var .here) lA))),
      ⟨defaultFuel - 15, false⟩) := by
  decide +kernel
example : typeAt MuPh_src =
    (some (.all (.mu MuPBody) (.all (.sngl (.var .here))
      (.all (.all (.sel (.var .here) lA) .top) .top))),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel
example : typeAt MuS_src =
    (some (.all (.mu MuSBody) (.all (.sngl (.var .here)) (.all (.sel (.var .here) lA)
      (.typ lB (.sel (.var (.there .here)) lC) (.sel (.var (.there .here)) lC))))),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

-- LPt ends with the tank marked: the recursion limit.
example : (typeAt LPt_src).1 = none := by decide +kernel
example : (typeAt LPt_src).2.out = true := by decide +kernel

end TyperChecks

end PathsFrontend
