import Coercions.Frontend.Resolve
import Coercions.Frontend.Avoid

/-!
# The typer

The typer reads a type off an annotated term of DOT-MNF and returns the
`DotMNF.HasTy` derivation with it.  The derivation is a field of the result,
so soundness is the result type.

It runs on the tank of `Fuel.lean`.  One tank is threaded through every
subtyping goal of `Sub.lean`, every member lookup of `Look.lean` and every
avoidance of `Avoid.lean`.  A goal that finds the tank short marks it, and a
marked tank is the recursion limit, not a rejection by the rules.

## Candidates

Synthesis returns a list of candidates, each a type with its derivation, with
no two of one type.  The compiler merges two members of one name
(`TypeBounds.&` in core/Types.scala).  DOT-MNF has no rule for that, so the
typer keeps every choice.

- A variable has the type its context declares.
- `λ(x : S). t` has `∀(x : S) T` for every candidate `T` of the body.
- `ν(x : T. d)` checks the definitions against `T` under the self binder.
- `x y` tries every function type the lookup finds in the declared type of
  `x`, and keeps each one whose domain `y` meets.
- `x.a` returns every field at `a` the lookup finds.
- `let x = t in u` returns every pair of a candidate of `t` and a candidate of
  `u`.  The type of the body is approximated by one free of `x` (`avoidLet`),
  as `TypeOps.avoid` does.
- `let x : U = t in u` has the type `U`.  The annotation binds, and the body is
  checked against it.

Checking a variable asks the `var` goal of `Sub.lean`, which reaches the rules
`HasTy.andI` and `HasTy.recI` that subsumption does not.  Checking any other
term takes the first candidate that the subtyping goal takes to the type asked
for.

## The theorems

Every computation is framed (`synthF_framed`): it keeps a marked tank, never
adds fuel, and does the same with more fuel.  So a typing that ends unmarked
gives the same answer at every larger fuel (`synthTop?_mono`,
`synthTop?_stable`), and an unmarked rejection is a rejection at every fuel.

The typer has no completeness theorem.  It finds no derivation through a middle
type the program does not write, as the compiler does not.  It does not merge
two fields, so a projection tries each.  It does not find a judgment whose
search needs more than the fuel.  A lookup through a cyclic member is cut.

All definitions are structural on the term, so the kernel evaluates the typer.
The checks at the end type the example programs at `defaultFuel`.
-/

namespace Frontend

open Frontend.Fuel Frontend.Core
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Value Defs Ctx Sub HasTy DefsTy)

/-- The fuel of a typing: the size of the tank every entry point starts from. -/
structure Budget where
  fuel : Nat := defaultFuel

/-- A type a term has, with the derivation. -/
structure Cand {s : Sig} (Γ : Ctx s) (t : Tm s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ t ty

/-! ## Pieces the clauses use -/

/-- Keep the first candidate of each type. -/
def dedupTy {s : Sig} {Γ : Ctx s} {t : Tm s} : List (Cand Γ t) → List (Cand Γ t)
  | [] => []
  | c :: cs => c :: (dedupTy cs).filter fun c' => !decide (c'.ty = c.ty)

/-- The types of a variable that carry the key, looked up from its declared
type.  The index of the lookup is the fuel left. -/
def lookVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Fu (List (Found Γ x (Γ.lookup x))) :=
  fun t => look Γ t.left [] x (Γ.lookup x) k t

/-- Read a function type off a found type. -/
def Core.Found.all? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} (e : Found Γ x V) :
    Option ((S : Ty s) × (T : Ty (s,x)) × (Var Γ x V → Var Γ x (.all S T))) :=
  match h : e.ty with
  | .all S T => some ⟨S, T, fun d => h ▸ e.f d⟩
  | _ => none

/-- Read a field at `a` off a found type. -/
def Core.Found.fld? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} (a : Label) (e : Found Γ x V) :
    Option ((T : Ty s) × (Var Γ x V → Var Γ x (.fld a T))) :=
  match h : e.ty with
  | .fld b T => if hb : b = a then some ⟨T, fun d => hb ▸ h ▸ e.f d⟩ else none
  | _ => none

/-- A type member definition against a declaration whose two bounds are the
definition's own type, as `DefsTy.typ` concludes.  The proof takes the
equalities apart, since a label occurs twice in the conclusion. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {A B : Label} {S L U : Ty s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- Check a term against `T`, given the computation of its candidates.  A
variable asks the `var` goal.  Any other term takes the first candidate that
the subtyping goal takes to `T`, through `HasTy.sub`. -/
def checkOf {s : Sig} (Γ : Ctx s) (t : ATm s) (T : Ty s) (cs : Fu (List (Cand Γ t.erase))) :
    Fu (Option (HasTy Γ t.erase T)) :=
  match t, cs with
  | .path (.var x), _ => varF Γ x T
  | _, cs => Fu.bind cs fun l =>
      Fu.firstSome (fun c => mapO (subF Γ c.ty T) fun e => HasTy.sub c.deriv e) l

/-- The candidate of a `let` with annotation `U`, from a candidate of the
bound term and the body checked against `U` under the binder at its type. -/
def letAnn {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (U : Ty s) (c1 : Cand Γ t)
    (h2 : HasTy (Γ.cons c1.ty) u U.weaken) : Cand Γ (.let t u) :=
  ⟨U, .let c1.deriv h2⟩

/-- The candidate of a `let` without annotation: the body's type avoided. -/
def letAvoid {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1 : Cand Γ t)
    (c2 : Cand (Γ.cons c1.ty) u) (r : LetTy Γ c1.ty c2.ty) : Cand Γ (.let t u) :=
  ⟨r.1, .let c1.deriv (.sub c2.deriv r.2)⟩

/-- An optional answer as a list of at most one. -/
def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

/-! ## Synthesis and checking

`synthF` returns the candidates of a term.  `checkDefsF` matches a definition
list against a type in lockstep, as `DefsTy` does.  A field body is checked by
`checkOf` from the candidates of `synthF`.  Both are structural on the term. -/

mutual

/-- The candidates of a term, each with its derivation, on the tank. -/
def synthF {s : Sig} (Γ : Ctx s) : (a : ATm s) → Fu (List (Cand Γ a.erase))
  | .path (.var x) => Fu.ret [⟨Γ.lookup x, .var⟩]
  | .lam S t =>
      Fu.bind (synthF (Γ.cons S) t) fun cs =>
        Fu.ret (cs.map fun c => ⟨.all S c.ty, .lam c.deriv⟩)
  | .obj T d =>
      Fu.bind (checkDefsF (Γ.consSelf d.erase T) d T) fun
        | some hd =>
            if hdist : Defs.Distinct d.erase then Fu.ret [⟨.mu T, .obj hd hdist⟩]
            else Fu.ret []
        | none => Fu.ret []
  | .app x y =>
      Fu.bind (lookVar Γ x .fn) fun es =>
        Fu.bind (Fu.flatMapL (fun e =>
            match e.all? with
            | some ⟨S, T, f⟩ =>
                Fu.bind (varF Γ y S) fun o =>
                  Fu.ret (listO (o.map fun hy => (⟨T.substVar y, .app (f .var) hy⟩ :
                    Cand Γ (.app x y))))
            | none => Fu.ret []) es) fun cs =>
          Fu.ret (dedupTy cs)
  | .proj x a =>
      Fu.bind (lookVar Γ x (.fld a)) fun es =>
        Fu.ret (dedupTy (es.filterMap fun e =>
          (e.fld? a).map fun r => (⟨r.1, .proj (r.2 .var)⟩ : Cand Γ (.proj x a))))
  | .let (some U) t u =>
      Fu.bind (synthF Γ t) fun c1s =>
        Fu.bind (Fu.firstSome (fun c1 =>
            mapO (checkOf (Γ.cons c1.ty) u U.weaken (synthF (Γ.cons c1.ty) u))
              (letAnn U c1)) c1s) fun o =>
          Fu.ret (listO o)
  | .let none t u =>
      Fu.bind (synthF Γ t) fun c1s =>
        Fu.bind (Fu.flatMapL (fun c1 =>
            Fu.bind (synthF (Γ.cons c1.ty) u) fun c2s =>
              Fu.flatMapL (fun c2 =>
                Fu.bind (avoidLet Γ c1.ty c2.ty) fun o =>
                  Fu.ret (listO (o.map (letAvoid c1 c2)))) c2s) c1s) fun cs =>
          Fu.ret (dedupTy cs)

/-- A definition list against a type, in lockstep: a type member against a
declaration with its own type on both bounds, a term member against a field
at the same label, an intersection against an intersection. -/
def checkDefsF {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (T : Ty s) →
    Fu (Option (DefsTy Γ d.erase T))
  | .typ A S, .typ B L U =>
      Fu.ret (if hA : A = B then
        if hL : S = L then
          if hU : S = U then some (defsTypAt hA hL hU) else none
        else none
      else none)
  | .trm a t, .fld c U =>
      if h : a = c then mapO (checkOf Γ t U (synthF Γ t)) (defsTrmAt h) else Fu.ret none
  | .and d1 d2, .and T1 T2 =>
      bindO (checkDefsF Γ d1 T1) fun h1 =>
        mapO (checkDefsF Γ d2 T2) fun h2 => DefsTy.and h1 h2
  | _, _ => Fu.ret none

end

/-- Checking a term against a type on the tank. -/
def checkF {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Fu (Option (HasTy Γ a.erase T)) :=
  checkOf Γ a T (synthF Γ a)

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

Each clause is built from the combinators of `Fuel.lean` and from the framed
`varF`, `subF`, `avoidLet` and lookup.  So each clause is framed, by induction
on the term. -/

/-- The lookup from the fuel left is framed, as `declsAt` is. -/
theorem lookVar_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Framed (lookVar Γ x k) where
  absorbs t ht := (look_framed Γ t.left [] x _ k).absorbs t ht
  spends t := (look_framed Γ t.left [] x _ k).spends t
  shift := by
    intro t r t' h ho j
    exact (look_agree Γ t.left (t.left + j) (Nat.le_add_right _ _) [] x (Γ.lookup x) k).sim
      t r t' h ho j

theorem checkOf_framed {s : Sig} (Γ : Ctx s) (t : ATm s) (T : Ty s)
    {cs : Fu (List (Cand Γ t.erase))} (hcs : Framed cs) : Framed (checkOf Γ t T cs) := by
  cases t with
  | path p =>
    cases p with
    | var x => exact varF_framed Γ x T
  | lam _ _ =>
    exact bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l
  | obj _ _ =>
    exact bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l
  | app _ _ =>
    exact bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l
  | proj _ _ =>
    exact bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l
  | «let» _ _ _ =>
    exact bind_framed hcs fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _)) l

mutual

theorem synthF_framed {s : Sig} (Γ : Ctx s) : (a : ATm s) → Framed (synthF Γ a)
  | .path (.var x) => by
    rw [synthF]
    exact ret_framed _
  | .lam S t => by
    rw [synthF]
    exact bind_framed (synthF_framed _ t) fun _ => ret_framed _
  | .obj T d => by
    rw [synthF]
    refine bind_framed (checkDefsF_framed _ d T) fun o => ?_
    cases o with
    | none => exact ret_framed _
    | some _ => exact (dite_agree (fun _ => ret_agree _) (fun _ => ret_agree _)).left
  | .app x y => by
    rw [synthF]
    refine bind_framed (lookVar_framed _ _ _) fun es => bind_framed (flatMapL_framed ?_ es)
      fun _ => ret_framed _
    intro e
    dsimp only
    split
    · exact bind_framed (varF_framed _ _ _) fun _ => ret_framed _
    · exact ret_framed _
  | .proj x a => by
    rw [synthF]
    exact bind_framed (lookVar_framed _ _ _) fun _ => ret_framed _
  | .let (some U) t u => by
    rw [synthF]
    refine bind_framed (synthF_framed Γ t) fun c1s =>
      bind_framed (firstSome_framed (fun c1 => ?_) c1s) fun _ => ret_framed _
    exact mapO_framed _ (checkOf_framed _ u _ (synthF_framed _ u))
  | .let none t u => by
    rw [synthF]
    refine bind_framed (synthF_framed Γ t) fun c1s =>
      bind_framed (flatMapL_framed (fun c1 => ?_) c1s) fun _ => ret_framed _
    exact bind_framed (synthF_framed _ u) fun c2s =>
      flatMapL_framed (fun _ => bind_framed (avoidLet_framed _ _ _) fun _ => ret_framed _) c2s

theorem checkDefsF_framed {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (T : Ty s) →
    Framed (checkDefsF Γ d T)
  | .typ A S, T => by
    cases T with
    | typ B L U => rw [checkDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | .trm a t, T => by
    cases T with
    | fld c U =>
      rw [checkDefsF]
      exact (dite_agree (fun _ => Agree.refl (mapO_framed _ (checkOf_framed _ t _ (synthF_framed _ t))))
        (fun _ => ret_agree _)).left
    | _ => exact ret_framed _
  | .and d1 d2, T => by
    cases T with
    | and T1 T2 =>
      rw [checkDefsF]
      exact bind_framed (checkDefsF_framed _ d1 T1) fun
        | some _ => mapO_framed _ (checkDefsF_framed _ d2 T2)
        | none => ret_framed _
    | _ => exact ret_framed _

end

/-- A typing that ends unmarked does the same with more fuel. -/
theorem synthF_frame {s : Sig} {Γ : Ctx s} {a : ATm s} {t t' : Tank}
    {r : List (Cand Γ a.erase)} (h : synthF Γ a t = (r, t')) (ho : t'.out = false) (k : Nat) :
    synthF Γ a (t.add k) = (r, t'.add k) :=
  (synthF_framed Γ a).shift t r t' h ho k

theorem checkF_framed {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Framed (checkF Γ a T) :=
  checkOf_framed Γ a T (synthF_framed Γ a)

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

Each check types a surface program of `Resolve.lean`, or one written here, at
`defaultFuel`.  It states the type, or that there is none, and the tank left.
An unmarked tank means the fuel played no part in the verdict. -/

section TyperChecks

open DotMNF.Examples

/-- The type of a closed program after resolution, with the tank left. -/
def typeAt (e : STm) (n : Nat := defaultFuel) : Option (Ty []) × Tank :=
  match resolve exampleTable e with
  | some a => ((synthTopF n a).1.map (·.ty), (synthTopF n a).2)
  | none => (none, ⟨n, true⟩)

/-- E1 with the middle written.  A `let` annotation ascribes its type. -/
def E1ssrc : STm :=
  dot% λ(x : {A : ⊤..⊥}).
         let y : {B : {a : ⊤} .. {a : ⊤}} = (let u : x.A = (let t : ⊤ = x in t) in u) in y

/-- E3 with the middle written. -/
def E3ssrc : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = (let u : x.A = z in u) in y

/-- `λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)`, E10 with a function type at
its binders. -/
def E10tsrc : STm :=
  dot% λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)

/-- `let i = λ(x : ⊤). x in (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i`. -/
def E11src : STm :=
  dot% let i = λ(x : ⊤). x in
       (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i

/-- A function at an intersection of two function types, applied to an
argument only the second accepts. -/
def P5src : STm :=
  dot% λ(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). λ(y : ⊤). f y

/-- A projection with two fields, the first through `x.A`'s upper bound.  Only
the second has the member `b`. -/
def R1src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A projection with two written fields.  Only the second has the member `b`. -/
def R2src : STm :=
  dot% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A written `let` annotation that the bound value does not meet. -/
def A1src : STm :=
  dot% λ(x : ⊤). let y : {a : ⊤} = x in y

/-- A field reached only through a middle the program does not write:
`n : {a : ⊤}` below `x.A`, and `x.A` below `{b : ⊤}`. -/
def B1src : STm :=
  dot% λ(x : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}). n.b

/-- The function type of G: its result has two members `A` and a field at one
of them. -/
def GFun : Ty [] :=
  .all .top (.mu (.and (.and (.typ lA .bot (.fld la .top)) (.typ lA .bot (.fld lb .top)))
    (.fld lv (.sel (.var .here) lA))))

/-- The inner `let` of G: `z.v` has the type `z.A`, which avoidance replaces
by the meet of the upper bounds of `z`'s two members `A`. -/
def Ginsrc : STm :=
  dot% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})). λ(w : ⊤).
         let z = f w in z.v

/-- G: the inner `let`, then the member `b` of its type. -/
def Gsrc : STm :=
  dot% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})). λ(w : ⊤).
         let r = (let z = f w in z.v) in r.b

/-- A check through `∀` bodies that never ends: `x : p.A` against `q.B`. -/
def LPsrc : STm :=
  dot% λ(p : μ(s. {A : ⊥ .. ∀(y : ⊤) s.A})). λ(q : μ(s. {B : ∀(y : ⊤) s.B .. ⊤})).
         λ(x : p.A). let r : q.B = x in r

-- The ten programs of `Resolve.lean`.  E1, E3 and E4 need a middle the program does
-- not write.  E10 applies a variable at `⊤`.
example : typeAt E1src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E2src = (some (.all (.all .top .bot) .top), ⟨defaultFuel - 58, false⟩) := by
  decide +kernel
example : typeAt E3src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt E4src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel
example : typeAt E5src = (some (.all E5AT (.sel (.var .here) lA)), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel
example : typeAt E6src = (some (.all E6Int (.mu E6Self)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel
example : typeAt E7src = (some (.mu E7Self), ⟨defaultFuel, false⟩) := by decide +kernel
example : typeAt E8src = (some (.all E8Dom (.all (E8Ref .here) .top)), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel
example : typeAt E9src =
    (some (.all E8Dom (.all (.sel (.var .here) lA) .top)), ⟨defaultFuel - 5, false⟩) := by
  decide +kernel
example : typeAt E10src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- The middles written, E10t, E11 and P5.
example : typeAt E1ssrc = (some (.all E1Dom E1Res), ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt E3ssrc = (some (.all E3Dom (.all E3T2 E3T1)), ⟨defaultFuel - 16, false⟩) := by
  decide +kernel
example : typeAt E10tsrc =
    (some (.all (.all .top .top) (.all (.all .top .top) .top)), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel
example : typeAt E11src = (some .top, ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : typeAt P5src =
    (some (.all (.and (.all (.fld la .top) .top) (.all .top .top)) (.all .top .top)),
      ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

-- The projection reaches the field that has `b`.
example : typeAt R1src =
    (some (.all (.typ lA .bot (.fld la .top))
      (.all (.and (.sel (.var .here) lA) (.fld la (.fld lb .top))) .top)),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel
example : typeAt R2src =
    (some (.all (.and (.fld la .top) (.fld la (.fld lb .top))) .top), ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

-- A written annotation binds (A1), and the middle of B1 is not written.
example : typeAt A1src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : typeAt B1src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

-- G: avoidance meets the two upper bounds, so the member `b` is found.
example : typeAt Ginsrc =
    (some (.all GFun (.all .top (.and (.fld la .top) (.fld lb .top)))), ⟨defaultFuel - 41, false⟩) := by
  decide +kernel
example : typeAt Gsrc = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

-- LP ends with the tank marked.
example : (typeAt LPsrc).1 = none := by decide +kernel
example : (typeAt LPsrc).2.out = true := by decide +kernel

end TyperChecks

end Frontend
