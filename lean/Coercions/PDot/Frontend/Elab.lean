import Coercions.PDot.Frontend.Typer
import Coercions.Frontend.Reason

/-!
# The elaborator

The elaborator of the pDOT front end fills the three slots of a partial term
(`PTm`, `Ann.lean`) and types the result with the typer of `Typer.lean`, on the
same tank.  This is plan XI (`plan-11-pdot-frontends.md`), its part "Annotation
inference", with D-17.  The model is the elaborator of the Paths front end
(`Paths/Frontend/Elab.lean`).

## The rule of empty slots

Each clause first asks `PTm.full?`.  A term with no empty slot goes to the typer
as it is (`fullSynthAt`, `fullCheckAt`).  So a program with every slot written
elaborates as the typer types it (`elabN_full`, `Pipeline.lean`).  Every result
carries `p.fills a = true`, the agreement with every slot the program writes.

## Where a goal reaches a term

A written `let` type is the goal of the bound term, and an ascription is a `let`
tagged `asc` with a type.  The goal of a checked `let` passes to its body.  A
call argument `let z = t in f z`, the `let` resolution inserts, gives `t` the
dominant formal of `f` (`argGoalF`).  A field of a literal with a self type gets
its declaration.  A lambda's body gets the result part of the goal.

## Slot 1, a lambda's domain

The domain comes from the function part of the goal (`funPartAt`).  A function
type gives its domain.  An intersection meets its sides.  A singleton goes to
the views of its path, a `μ` whose body does not mention its self to its body,
a selection to its upper bounds.  With no goal, a body `f z` gives the dominant
formal of `f` (`lamCalleeSynF`).  Otherwise the reason is `missingParamType`.  A
goal site that fails with the tank unmarked falls back to the typer's route,
synthesis then subsumption.

## Slot 3, a literal's self type

The self type is formed from the definitions and never taken from a goal
(`formN`), since no `Sub` rule relates two `μ` types.  A type definition gives
`{A : U..U}`, a path field `{b : q.type}`, a nested literal `{b : μ(z. U)}`
with `U` formed in turn, a lambda field `{b : T}` once slot 2 has `T`.  The
declarations are in definition order, left nested.  The literal with its formed
type is typed again by the typer, which gives the derivation `ty_new_intro`
needs.  One site is a declaration and not a goal: a nested literal at a field
that a written self type declares `{b : μ(y. U)}` is filled at `U` first
(`defW`), since `ty_def_new` asks that declaration to carry the self type.

## Slot 2, a lambda field's declared type

A definition whose declaration is not known at once is a job (`PDefs.jobs`).
The jobs are typed in rounds in the order of their dependencies (`PTm.deps`),
closed over the declarations known at once (`closeHeads`), so that a job which
reaches a pending field through a path field waits for it.  Each round runs
against a snapshot of the self type with every declaration known so
far (`roundsF`).  A lambda field takes its least candidate (`leastE`), which the
typer widens in the Scala mode.  No least one is `ambiguous`.  A round that
picks no job is `cyclicRef` at a label on a cycle.

## Reasons and the index

`PReason` is `Frontend.Reason.Reason Label TReason`.  A failed typing of a
filled term gives its syntactic causes (`ATm.why`) as `landed`, then `mismatch`.
`elabN`, `chkN` and `formN` are one mutual block on an index, since the
elaborator hands the typer terms it builds.  The entry point `elabTopF` starts
the index at `p.size`, and each call is on a part of smaller size.  Every
function is framed (`elab_framed`), which gives the stability of `elabTopF` in
the fuel.
-/

namespace PDotFrontend

open Frontend.Fuel PDotFrontend.Core Frontend.Reason
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open PDot.Source (Ty Dec Tm Ctx HasTy Sub)

/-! ## Reasons -/

/-- The reasons of the pDOT typer's own, carried by `Reason.landed`. -/
inductive TReason where
  | selfSingleton (p : List Label)
  | notTight (b : Label)
  | dupLabel (l : Label)
  | fieldNotFun (l : Label)
  | noField (a : Label)
  | notFunction
  | argMismatch
  | literalGoal
deriving DecidableEq, Repr

abbrev PReason := Reason Label TReason

/-! ## Sizes, the elaborator's index -/

mutual
def PTm.size : {s : Sig} → PTm s → Nat
  | _, .path _ => 1
  | _, .app _ _ => 1
  | _, .lam _ t => t.size + 1
  | _, .new _ ds => ds.size + 1
  | _, .«let» _ _ t u => t.size + u.size + 1
termination_by structural _ t => t
def PDef.size : {s : Sig} → PDef s → Nat
  | _, .typ _ _ => 1
  | _, .path _ _ => 1
  | _, .lam _ _ _ t => t.size + 1
  | _, .new _ _ ds => ds.size + 1
termination_by structural _ d => d
def PDefs.size : {s : Sig} → PDefs s → Nat
  | _, .nil => 1
  | _, .cons ds d => ds.size + d.size + 1
termination_by structural _ ds => ds
end

/-! ## Agreement lemmas -/

mutual
theorem PTm.fills_of_full? : ∀ {s : Sig} {p : PTm s} {a : ATm s}, p.full? = some a → p.fills a = true
  | _, .path _, a, h => by simp [PTm.full?] at h; subst h; simp [PTm.fills]
  | _, .app _ _, a, h => by simp [PTm.full?] at h; subst h; simp [PTm.fills]
  | _, .lam (some S) t, a, h => by
      simp only [PTm.full?, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rfl⟩ := h
      simp [PTm.fills, slotAgrees, PTm.fills_of_full? hb]
  | _, .lam none _, _, h => by simp [PTm.full?] at h
  | _, .new (some T) ds, a, h => by
      simp only [PTm.full?, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rfl⟩ := h
      simp [PTm.fills, slotAgrees, PDefs.fills_of_full? T hb]
  | _, .new none _, _, h => by simp [PTm.full?] at h
  | _, .«let» g ann t u, a, h => by
      simp only [PTm.full?] at h
      split at h
      · rename_i a' b' ht hu
        simp only [Option.some.injEq] at h
        subst h
        simp [PTm.fills, PTm.fills_of_full? ht, PTm.fills_of_full? hu]
      · cases h
theorem PDef.fills_of_full? : ∀ {s : Sig} {d : PDef s} {e : ADef s} (U : Ty s), d.full? = some e → d.fills U e = true
  | _, .typ _ _, e, _, h => by simp [PDef.full?] at h; subst h; simp [PDef.fills]
  | _, .path _ _, e, _, h => by simp [PDef.full?] at h; subst h; simp [PDef.fills]
  | _, .lam a none (some S) t, e, U, h => by
      simp only [PDef.full?, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rfl⟩ := h
      simp [PDef.fills, declAgrees, slotAgrees, PTm.fills_of_full? hb]
  | _, .lam _ none none _, _, _, h => by simp [PDef.full?] at h
  | _, .lam _ (some _) _ _, _, _, h => by simp [PDef.full?] at h
  | _, .new a (some T) ds, e, _, h => by
      simp only [PDef.full?, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rfl⟩ := h
      simp [PDef.fills, slotAgrees, PDefs.fills_of_full? T hb]
  | _, .new _ none _, _, _, h => by simp [PDef.full?] at h
theorem PDefs.fills_of_full? : ∀ {s : Sig} {d : PDefs s} {e : ADefs s} (U : Ty s), d.full? = some e → d.fills U e = true
  | _, .nil, e, _, h => by simp [PDefs.full?] at h; subst h; simp [PDefs.fills]
  | _, .cons ds d, e, U, h => by
      simp only [PDefs.full?] at h
      split at h
      · rename_i a b hds hd
        simp only [Option.some.injEq] at h
        subst h
        cases ds with
        | nil =>
          simp [PDefs.full?] at hds
          subst hds
          simp [PDefs.fills, PDef.fills_of_full? U hd]
        | cons ds0 d0 =>
          cases a with
          | nil => simp [PDefs.full?] at hds; split at hds <;> simp at hds
          | cons a0 b0 =>
            simp [PDefs.fills, PDefs.fills_of_full? (andLeft U) hds, PDef.fills_of_full? (andRight U) hd]
      · cases h
end

theorem PTm.size_pos : ∀ {s : Sig} (p : PTm s), 0 < p.size
  | _, .path _ => by simp [PTm.size]
  | _, .app _ _ => by simp [PTm.size]
  | _, .lam _ _ => by simp [PTm.size]
  | _, .new _ _ => by simp [PTm.size]
  | _, .«let» _ _ _ _ => by simp [PTm.size]

/-! ## Results -/

structure ECand {s : Sig} (Γ : Ctx s) (p : PTm s) where
  a : ATm s
  ty : Ty s
  ann : AHasTy Γ a ty
  fills : p.fills a = true

structure EChk {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s) where
  a : ATm s
  ann : AHasTy Γ a G
  fills : p.fills a = true

structure EDefs {s : Sig} (ds : PDefs s) (T : Ty s) where
  defs : ADefs s
  fills : ds.fills T defs = true

structure EDef {s : Sig} (d : PDef s) (U : Ty s) where
  ad : ADef s
  fills : d.fills U ad = true

structure Formed {s : Sig} (ds : PDefs s) where
  ty : Ty s
  defs : EDefs ds ty

abbrev ESynth {s : Sig} (Γ : Ctx s) (p : PTm s) := List (ECand Γ p) × List PReason
abbrev ECheck {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s) := Option (EChk Γ p G) × List PReason
abbrev EDefsR {s : Sig} (ds : PDefs s) (T : Ty s) := Option (EDefs ds T) × List PReason
abbrev EDefR {s : Sig} (d : PDef s) (U : Ty s) := Option (EDef d U) × List PReason
abbrev EForm {s : Sig} (ds : PDefs s) := Except (List PReason) (Formed ds)

/-! ## Combinators with reasons -/

def stopOr {β : Type} (stop : Bool) (a : β) (c : Fu β) : Fu β := fun t =>
  if stop || t.out then (a, t) else c t

def orElseW {α ρ : Type} (ok : α → Bool) (a : Fu (α × List ρ)) (b : Unit → Fu (α × List ρ)) :
    Fu (α × List ρ) :=
  Fu.bind a fun r => stopOr (ok r.1) r (Fu.bind (b ()) fun r' => Fu.ret (r'.1, r.2 ++ r'.2))

def firstSomeR {α β ρ : Type} (f : α → Fu (Option β × List ρ)) : List α → Fu (Option β × List ρ)
  | [] => Fu.ret (none, [])
  | x :: xs => orElseW Option.isSome (f x) (fun _ => firstSomeR f xs)

def flatMapR {α β ρ : Type} (f : α → Fu (List β × List ρ)) : List α → Fu (List β × List ρ)
  | [] => Fu.ret ([], [])
  | x :: xs =>
      Fu.bind (f x) fun r1 => Fu.bind (flatMapR f xs) fun r2 => Fu.ret (r1.1 ++ r2.1, r1.2 ++ r2.2)

def dedupE {s : Sig} {Γ : Ctx s} {p : PTm s} : List (ECand Γ p) → List (ECand Γ p)
  | [] => []
  | c :: cs => c :: (dedupE cs).filter fun c' => !decide (c'.ty = c.ty)

def markAs {α : Type} (a : α) : Fu α := fun t => (a, { t with out := true })

/-! ## Syntactic causes of a failure (`why`) -/

def firstDup : List Label → Option Label
  | [] => none
  | l :: ls => if ls.contains l then some l else firstDup ls

def ADef.label {s : Sig} : ADef s → Label
  | .typ A _ => A
  | .path a _ => a
  | .lam a _ _ => a
  | .new a _ _ => a

def ADefs.labels {s : Sig} : ADefs s → List Label
  | .nil => []
  | .cons ds d => ds.labels ++ [d.label]

/-- The cause of a check of `a` against `W`: a path at its own singleton (N4), a literal at a goal
that is neither its `μ` type nor `⊤`. -/
def whyAt {s : Sig} : ATm s → Ty s → List TReason
  | .path p, W => if W = .sngl p then [.selfSingleton (sels p)] else []
  | .new T _, W => if W = .mu T ∨ W = .top then [] else [.literalGoal]
  | _, _ => []

mutual
def ATm.why : {s : Sig} → ATm s → List TReason
  | _, .path _ => []
  | _, .app _ _ => []
  | _, .lam _ t => t.why
  | _, .new T ds => (ds.labels |> firstDup |>.toList.map .dupLabel) ++ ds.why T
  | _, .«let» _ (some W) t u => whyAt t W ++ t.why ++ u.why
  | _, .«let» _ none t u => t.why ++ u.why
termination_by structural _ a => a
def ADef.why : {s : Sig} → ADef s → Ty s → List TReason
  | _, .typ _ _, _ => []
  | _, .path _ _, _ => []
  | _, .lam b _ t, U => (match U with
      | .rcd (.trm _ (.all _ _)) => []
      | _ => [.fieldNotFun b]) ++ t.why
  | _, .new b T ds, _ => (if (Ty.mu T).tight then [] else [.notTight b]) ++
      (ds.labels |> firstDup |>.toList.map .dupLabel) ++ ds.why T
termination_by structural _ d => d
def ADefs.why : {s : Sig} → ADefs s → Ty s → List TReason
  | _, .nil, _ => []
  | _, .cons .nil d, U => d.why U
  | _, .cons ds d, U => ds.why (andLeft U) ++ d.why (andRight U)
termination_by structural _ ds => ds
end

/-- The reasons of a failed typing of `a`: its causes as `landed`, then `mismatch`. -/
def whyR {s : Sig} (a : ATm s) : List PReason := a.why.map .landed ++ [.mismatch]
def whyChkR {s : Sig} (a : ATm s) (G : Ty s) : List PReason := (whyAt a G ++ a.why).map .landed ++ [.mismatch]

/-! ## The typer on a filled term -/

section Typer
variable (md : Mode) (ms : List (List Label))

def fullSynthAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) : Fu (ESynth Γ p) :=
  Fu.bind (synthF md ms Γ a) fun cs =>
    Fu.ret (cs.map fun c => ⟨a, c.ty, c.deriv, h⟩, if cs.isEmpty then whyR a else [])

def fullCheckAt {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) (G : Ty s) :
    Fu (ECheck Γ p G) :=
  Fu.bind (checkF md ms Γ a G) fun o =>
    Fu.ret (o.map fun d => ⟨a, d, h⟩, if o.isSome then [] else whyChkR a G)

end Typer

def toGoalE {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (c : ECand Γ p) : Fu (ECheck Γ p G) :=
  if h : c.ty = G then Fu.ret (some ⟨c.a, h ▸ c.ann, c.fills⟩, [])
  else
    Fu.bind (subF Γ c.ty G) fun o =>
      Fu.ret (o.map (fun e => ⟨c.a, .asub c.ann e, c.fills⟩), if o.isSome then [] else [.mismatch])

def subsumeE {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) : Fu (ECheck Γ p G) :=
  Fu.bind (firstSomeR (toGoalE Γ G) r.1) fun r' => Fu.ret (r'.1, r.2 ++ r'.2)

/-- A literal moved to a goal: as `subsumeE`, with `literalGoal` when no candidate meets it. -/
def subsumeLit {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) : Fu (ECheck Γ p G) :=
  Fu.bind (firstSomeR (toGoalE Γ G) r.1) fun r' =>
    Fu.ret (r'.1, r.2 ++ if r'.1.isSome || r.1.isEmpty then [] else [.landed .literalGoal])

/-! ## Slot 1: the function part of a goal -/

inductive FunPart (s : Sig) where
  | none
  | one (S : Ty s) (V : Ty (s,x))
  | bad
deriving DecidableEq

def meetPart {s : Sig} (Γ : Ctx s) : FunPart s → FunPart s → Fu (FunPart s)
  | .bad, _ => Fu.ret .bad
  | _, .bad => Fu.ret .bad
  | .none, f => Fu.ret f
  | f, .none => Fu.ret f
  | .one S1 V1, .one S2 V2 =>
      Fu.bind (subF Γ S2 S1) fun o2 =>
        match o2 with
        | some _ => Fu.ret (.one S1 (.and V1 V2))
        | none =>
            Fu.bind (subF Γ S1 S2) fun o1 =>
              match o1 with
              | some _ => Fu.ret (.one S2 (.and V1 V2))
              | none => Fu.ret .bad

def isSngl {s : Sig} : Ty s → Bool
  | .sngl _ => true
  | _ => false

def firstPart {s : Sig} (rec : Ty s → Fu (FunPart s)) : List (Ty s) → Fu (FunPart s)
  | [] => Fu.ret .none
  | T :: Ts => Fu.bind (rec T) fun f =>
      match f with
      | .none => firstPart rec Ts
      | f => Fu.ret f

def funPartTy {s : Sig} (Γ : Ctx s) (rec : Ty s → Fu (FunPart s)) : Ty s → Fu (FunPart s)
  | .all S V => Fu.ret (.one S V)
  | .and G1 G2 =>
      Fu.bind (funPartTy Γ rec G1) fun f1 => Fu.bind (funPartTy Γ rec G2) fun f2 => meetPart Γ f1 f2
  | .sel q A => Fu.bind (bounds Γ q A) fun bs => firstPart rec (bs.map (·.hi))
  | .sngl q => Fu.bind (views Γ q) fun vs => firstPart rec ((vs.map (·.1)).filter fun T => !isSngl T)
  | .mu T =>
      match Ty.unweaken T with
      | some T' => rec T'
      | none => Fu.ret .none
  | .top => Fu.ret .none
  | .bot => Fu.ret .none
  | .rcd _ => Fu.ret .none

def funPartF {s : Sig} (Γ : Ctx s) : Nat → Ty s → Fu (FunPart s)
  | 0, G => funPartTy Γ (fun _ => markAs .none) G
  | d + 1, G => funPartTy Γ (funPartF Γ d) G

def funPartAt {s : Sig} (Γ : Ctx s) (G : Ty s) : Fu (FunPart s) := fun t => funPartF Γ t.left G t

/-! ## The goal of a call argument -/

def formalsF {s : Sig} (Γ : Ctx s) (f : Path s) : Fu (List (Ty s)) :=
  Fu.bind (views Γ f) fun vs => Fu.ret (vs.filterMap fun v => match v.1 with
    | .all S _ => some S
    | _ => none)

def allBelowF {s : Sig} (Γ : Ctx s) (F : Ty s) : List (Ty s) → Fu Bool
  | [] => Fu.ret true
  | F' :: Fs =>
      if F' = F then allBelowF Γ F Fs
      else
        Fu.bind (subF Γ F' F) fun o =>
          match o with
          | some _ => allBelowF Γ F Fs
          | none => Fu.ret false

def dominantF {s : Sig} (Γ : Ctx s) (Fs : List (Ty s)) : List (Ty s) → Fu (Option (Ty s))
  | [] => Fu.ret none
  | F :: rest =>
      Fu.bind (allBelowF Γ F Fs) fun b => if b then Fu.ret (some F) else dominantF Γ Fs rest

def argGoalF {s : Sig} (Γ : Ctx s) (f : Path s) : Fu (Option (Ty s)) :=
  Fu.bind (formalsF Γ f) fun Fs => dominantF Γ Fs Fs

/-- The callee `f` of a body `f z`, `z` the lambda's parameter, `f` free of it. -/
def calleeOf? {s : Sig} : PTm (s,x) → Option (Path s)
  | .app f (.var .here) => PDot.FCp.Path.unweaken f
  | _ => none

/-- The callee of a call argument `let z = t in f z`, the `let` resolution inserts. -/
def argCallee? {s : Sig} : LetTag → Option (Ty s) → PTm (s,x) → Option (Path s)
  | .arg, none, .app f (.var .here) => PDot.FCp.Path.unweaken f
  | _, _, _ => none

/-! ## Lambdas -/

theorem PTm.fills_lam' {s : Sig} {o : Option (Ty s)} {t : PTm (s,x)} {S : Ty s} {a : ATm (s,x)}
    (ho : slotAgrees o S = true) (h : t.fills a = true) : (PTm.lam o t).fills (.lam S a) = true := by
  simp [PTm.fills, ho, h]

theorem slotAgrees_some {α : Type} [DecidableEq α] (x : α) : slotAgrees (some x) x = true := by
  simp [slotAgrees]

theorem PTm.fills_let' {s : Sig} {g : LetTag} {o : Option (Ty s)} {t : PTm s} {u : PTm (s,x)}
    {a : ATm s} {b : ATm (s,x)} (ht : t.fills a = true) (hu : u.fills b = true) :
    (PTm.«let» g o t u).fills (.«let» g o a b) = true := by
  simp [PTm.fills, ht, hu]

def lamCands {s : Sig} {Γ : Ctx s} {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s)
    (ho : slotAgrees o S = true) (r : ESynth (Γ.cons S) t) : ESynth Γ (.lam o t) :=
  (r.1.map fun c => ⟨.lam S c.a, .all S c.ty, .alam c.ann, PTm.fills_lam' ho c.fills⟩, r.2)


section Clauses
variable (md : Mode) (ms : List (List Label))

def lamGoalF {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s) (V : Ty (s,x))
    (G : Ty s) (ho : slotAgrees o S = true) (chk : Fu (ECheck (Γ.cons S) t V))
    (syn : Unit → Fu (ESynth (Γ.cons S) t)) : Fu (ECheck Γ (.lam o t) G) :=
  orElseW Option.isSome
    (Fu.bind chk fun r =>
      match r.1 with
      | some e => toGoalE Γ G ⟨.lam S e.a, .all S V, .alam e.ann, PTm.fills_lam' ho e.fills⟩
      | none => Fu.ret (none, r.2))
    (fun _ => Fu.bind (syn ()) fun r => subsumeE Γ G (lamCands S ho r))

def lamCalleeSynF {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) : Fu (ESynth Γ (.lam none t)) :=
  match calleeOf? t with
  | some f =>
      Fu.bind (argGoalF Γ f) fun oS =>
        match oS with
        | some S =>
            match ht : t.full? with
            | some b => fullSynthAt md ms Γ _ (.lam S b) (PTm.fills_lam' rfl (PTm.fills_of_full? ht))
            | none => Fu.ret ([], [.missingParamType none])
        | none => Fu.ret ([], [.missingParamType none])
  | none => Fu.ret ([], [.missingParamType none])

def lamCalleeChkF {s : Sig} (Γ : Ctx s) (G : Ty s) (t : PTm (s,x)) : Fu (ECheck Γ (.lam none t) G) :=
  match calleeOf? t with
  | some f =>
      Fu.bind (argGoalF Γ f) fun oS =>
        match oS with
        | some S =>
            match ht : t.full? with
            | some b => fullCheckAt md ms Γ _ (.lam S b) (PTm.fills_lam' rfl (PTm.fills_of_full? ht)) G
            | none => Fu.ret (none, [.missingParamType none])
        | none => Fu.ret (none, [.missingParamType none])
  | none => Fu.ret (none, [.missingParamType none])


/-! ## `let` -/

/-- The binder of an untyped `let`: the first candidate, widened as the typer's `binderC`. -/
def binderE {s : Sig} {Γ : Ctx s} {p : PTm s} (g : LetTag) : List (ECand Γ p) → Fu (Option (ECand Γ p))
  | [] => Fu.ret none
  | c :: _ => Fu.bind (binderC md ms g [(⟨c.ty, c.ann⟩ : Cand Γ c.a)]) fun o =>
      Fu.ret (o.map fun c' => ⟨c.a, c'.ty, c'.deriv, c.fills⟩)

def avoidE {s : Sig} {Γ : Ctx s} {g : LetTag} {W : Option (Ty s)} {t : PTm s} {u : PTm (s,x)}
    {a : ATm s} {V : Ty s} (ht : t.fills a = true)
    (mk : {U : Ty s} → {b : ATm (s,x)} → AHasTy (Γ.cons V) b U.weaken → AHasTy Γ (.«let» g W a b) U)
    (c : ECand (Γ.cons V) u) : Fu (List (ECand Γ (.«let» g W t u))) :=
  Fu.bind (avoidLet Γ V c.ty) fun
    | some r => Fu.ret [⟨.«let» g W a c.a, r.1, mk (.asub c.ann r.2), PTm.fills_let' ht c.fills⟩]
    | none => Fu.ret []

end Clauses

/-! ## The untyped `let` -/

section Lets
variable (md : Mode) (ms : List (List Label))
variable (syn : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s), Fu (ESynth Γ p))
variable (chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G))

/-- An untyped `let` synthesized: the binder is the first candidate of the bound term, widened as
the typer's `binderC`, and every candidate of the body is avoided. -/
def letNoneSynF {s : Sig} (Γ : Ctx s) (g : LetTag) (t : PTm s) (u : PTm (s,x)) :
    Fu (ESynth Γ (.«let» g none t u)) :=
  Fu.bind (syn Γ t) fun r1 =>
    Fu.bind (binderE md ms g r1.1) fun o =>
      match o with
      | none => Fu.ret ([], r1.2)
      | some c1 =>
          Fu.bind (syn (Γ.cons c1.ty) u) fun r2 =>
            Fu.bind (Fu.flatMapL (avoidE c1.fills (fun d => .aletN c1.ann d)) r2.1) fun cs =>
              Fu.ret (dedupE cs, r1.2 ++ r2.2)

/-- An untyped `let` checked at `G`: the body checked at `G` under the binder, else synthesized,
avoided and subsumed, as the typer's `checkN`. -/
def letNoneChkF {s : Sig} (Γ : Ctx s) (g : LetTag) (t : PTm s) (u : PTm (s,x)) (G : Ty s) :
    Fu (ECheck Γ (.«let» g none t u) G) :=
  Fu.bind (syn Γ t) fun r1 =>
    Fu.bind (binderE md ms g r1.1) fun o =>
      match o with
      | none => Fu.ret (none, r1.2)
      | some c1 =>
          orElseW Option.isSome
            (Fu.bind (chk (Γ.cons c1.ty) u G.weaken) fun r2 =>
              Fu.ret (r2.1.map (fun e2 => ⟨.«let» g none c1.a e2.a, .aletN c1.ann e2.ann,
                PTm.fills_let' c1.fills e2.fills⟩), r1.2 ++ r2.2))
            (fun _ => Fu.bind (syn (Γ.cons c1.ty) u) fun r2 =>
              Fu.bind (Fu.flatMapL (avoidE c1.fills (fun d => .aletN c1.ann d)) r2.1) fun cs =>
                subsumeE Γ G (dedupE cs, r2.2))

end Lets

/-! ## Frame facts of the combinators -/

section CombinatorFrames

variable {α β ρ : Type}

theorem stopOr_framed {stop : Bool} {a : β} {c : Fu β} (hc : Framed c) :
    Framed (stopOr stop a c) where
  absorbs t ht := by simp [stopOr, ht]
  spends t := by
    unfold stopOr
    split
    · exact Nat.le_refl _
    · exact hc.spends t
  shift := by
    intro t r t' h ho k
    unfold stopOr at h ⊢
    by_cases hs : (stop || t.out) = true
    · rw [if_pos hs] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (by simpa using hs)]
    · rw [if_neg hs] at h
      rw [if_neg (by simpa using hs)]
      exact hc.shift t r t' h ho k

theorem orElseW_framed {ok : α → Bool} {a : Fu (α × List ρ)} {b : Unit → Fu (α × List ρ)}
    (ha : Framed a) (hb : Framed (b ())) : Framed (orElseW ok a b) :=
  bind_framed ha fun _ => stopOr_framed (bind_framed hb fun _ => ret_framed _)

theorem firstSomeR_framed {f : α → Fu (Option β × List ρ)} (hf : ∀ x, Framed (f x)) :
    ∀ l, Framed (firstSomeR f l)
  | [] => ret_framed _
  | x :: xs => orElseW_framed (hf x) (firstSomeR_framed hf xs)

theorem markAs_framed (a : α) : Framed (markAs a) where
  absorbs t ht := by cases t; simp_all [markAs]
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [markAs, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

theorem markAs_agree (a : α) {c : Fu α} (hc : Framed c) : Agree (markAs a) c := by
  refine ⟨markAs_framed a, hc, ?_⟩
  intro t r t' h ho _
  simp only [markAs, Prod.mk.injEq] at h
  rw [← h.2] at ho
  simp at ho

end CombinatorFrames

/-! ## Frame facts of the slot 1 functions -/

section Frames1
variable (md : Mode) (ms : List (List Label))

theorem toGoalE_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (c : ECand Γ p) :
    Framed (toGoalE Γ G c) := by
  unfold toGoalE
  split
  · exact ret_framed _
  · exact bind_framed (subF_framed _ _ _) fun _ => ret_framed _

theorem subsumeE_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) :
    Framed (subsumeE Γ G r) :=
  bind_framed (firstSomeR_framed (toGoalE_framed Γ G) r.1) fun _ => ret_framed _

theorem subsumeLit_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (G : Ty s) (r : ESynth Γ p) :
    Framed (subsumeLit Γ G r) :=
  bind_framed (firstSomeR_framed (toGoalE_framed Γ G) r.1) fun _ => ret_framed _

theorem fullSynthAt_framed {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true) :
    Framed (fullSynthAt md ms Γ p a h) :=
  bind_framed (synthF_framed md ms Γ a) fun _ => ret_framed _

theorem fullCheckAt_framed {s : Sig} (Γ : Ctx s) (p : PTm s) (a : ATm s) (h : p.fills a = true)
    (G : Ty s) : Framed (fullCheckAt md ms Γ p a h G) :=
  bind_framed (checkF_framed md ms Γ a G) fun _ => ret_framed _

/-! ## Frame facts of the goal readers -/

theorem meetPart_framed {s : Sig} (Γ : Ctx s) (f1 f2 : FunPart s) : Framed (meetPart Γ f1 f2) := by
  cases f1 <;> cases f2 <;> simp only [meetPart] <;> try exact ret_framed _
  refine bind_framed (subF_framed _ _ _) fun o2 => ?_
  cases o2 with
  | some _ => exact ret_framed _
  | none =>
    refine bind_framed (subF_framed _ _ _) fun o1 => ?_
    cases o1 with
    | some _ => exact ret_framed _
    | none => exact ret_framed _

theorem firstPart_agree {s : Sig} {rec rec' : Ty s → Fu (FunPart s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ Ts, Agree (firstPart rec Ts) (firstPart rec' Ts)
  | [] => ret_agree _
  | T :: Ts => by
    refine bind_agree (hr T) fun f => ?_
    cases f with
    | none => exact firstPart_agree hr Ts
    | one _ _ => exact ret_agree _
    | bad => exact ret_agree _

theorem funPartTy_agree {s : Sig} (Γ : Ctx s) {rec rec' : Ty s → Fu (FunPart s)}
    (hr : ∀ T, Agree (rec T) (rec' T)) : ∀ G, Agree (funPartTy Γ rec G) (funPartTy Γ rec' G)
  | .all _ _ => ret_agree _
  | .and G1 G2 =>
    bind_agree (funPartTy_agree Γ hr G1) fun _ =>
      bind_agree (funPartTy_agree Γ hr G2) fun _ => Agree.refl (meetPart_framed _ _ _)
  | .sel q A => bind_agree (Agree.refl (bounds_framed _ _ _)) fun _ => firstPart_agree hr _
  | .sngl q => bind_agree (Agree.refl (views_framed _ _)) fun _ => firstPart_agree hr _
  | .mu T => by
    simp only [funPartTy]
    split
    · exact hr _
    · exact ret_agree _
  | .top => ret_agree _
  | .bot => ret_agree _
  | .rcd _ => ret_agree _

theorem funPartF_framed {s : Sig} (Γ : Ctx s) : ∀ d G, Framed (funPartF Γ d G)
  | 0, G => (funPartTy_agree Γ (fun _ => Agree.refl (markAs_framed _)) G).left
  | d + 1, G => (funPartTy_agree Γ (fun T => Agree.refl (funPartF_framed Γ d T)) G).left

theorem funPartF_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ G, Agree (funPartF Γ d G) (funPartF Γ d' G)
  | 0, d', _, G => by
    cases d' with
    | zero => exact Agree.refl (funPartF_framed Γ 0 G)
    | succ e => exact funPartTy_agree Γ (fun T => markAs_agree _ (funPartF_framed Γ e T)) G
  | d + 1, d', hd, G => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact funPartTy_agree Γ (fun T => funPartF_agree Γ d e (by omega) T) G

theorem funPartAt_framed {s : Sig} (Γ : Ctx s) (G : Ty s) : Framed (funPartAt Γ G) :=
  atLeft_framed (c := fun d => funPartF Γ d G) fun d d' h => funPartF_agree Γ d d' h G

theorem formalsF_framed {s : Sig} (Γ : Ctx s) (f : Path s) : Framed (formalsF Γ f) :=
  bind_framed (views_framed _ _) fun _ => ret_framed _

theorem allBelowF_framed' {s : Sig} (Γ : Ctx s) (F : Ty s) : ∀ Fs, Framed (allBelowF Γ F Fs)
  | [] => ret_framed _
  | F' :: Fs => by
    unfold allBelowF
    split
    · exact allBelowF_framed' Γ F Fs
    · refine bind_framed (subF_framed _ _ _) fun o => ?_
      cases o with
      | some _ => exact allBelowF_framed' Γ F Fs
      | none => exact ret_framed _

theorem dominantF_framed {s : Sig} (Γ : Ctx s) (Fs : List (Ty s)) :
    ∀ cands, Framed (dominantF Γ Fs cands)
  | [] => ret_framed _
  | F :: rest => by
    refine bind_framed (allBelowF_framed' Γ F Fs) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact dominantF_framed Γ Fs rest

theorem argGoalF_framed {s : Sig} (Γ : Ctx s) (f : Path s) : Framed (argGoalF Γ f) :=
  bind_framed (formalsF_framed Γ f) fun Fs => dominantF_framed Γ Fs Fs

theorem lamGoalF_framed {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)} (S : Ty s) (V : Ty (s,x))
    (G : Ty s) (ho : slotAgrees o S = true) {chk : Fu (ECheck (Γ.cons S) t V)}
    {syn : Unit → Fu (ESynth (Γ.cons S) t)} (hc : Framed chk) (hs : Framed (syn ())) :
    Framed (lamGoalF Γ S V G ho chk syn) :=
  orElseW_framed (bind_framed hc fun r => by
      split
      · exact toGoalE_framed _ _ _
      · exact ret_framed _)
    (bind_framed hs fun _ => subsumeE_framed _ _ _)

theorem lamCalleeSynF_framed {s : Sig} (Γ : Ctx s) (t : PTm (s,x)) : Framed (lamCalleeSynF md ms Γ t) := by
  unfold lamCalleeSynF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oS => ?_
    split
    · split
      · exact fullSynthAt_framed md ms _ _ _ _
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem lamCalleeChkF_framed {s : Sig} (Γ : Ctx s) (G : Ty s) (t : PTm (s,x)) :
    Framed (lamCalleeChkF md ms Γ G t) := by
  unfold lamCalleeChkF
  split
  · refine bind_framed (argGoalF_framed _ _) fun oS => ?_
    split
    · split
      · exact fullCheckAt_framed md ms _ _ _ _ _
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem binderE_framed {s : Sig} {Γ : Ctx s} {p : PTm s} (g : LetTag) :
    ∀ cs : List (ECand Γ p), Framed (binderE md ms g cs)
  | [] => ret_framed _
  | c :: _ => by
    unfold binderE
    exact bind_framed (binderC_framed md ms g _) fun _ => ret_framed _

theorem avoidE_framed {s : Sig} {Γ : Ctx s} {g : LetTag} {W : Option (Ty s)} {t : PTm s} {u : PTm (s,x)}
    {a : ATm s} {V : Ty s} (ht : t.fills a = true)
    (mk : {U : Ty s} → {b : ATm (s,x)} → AHasTy (Γ.cons V) b U.weaken → AHasTy Γ (.«let» g W a b) U)
    (c : ECand (Γ.cons V) u) : Framed (avoidE ht mk c) :=
  bind_framed (avoidLet_framed _ _ _) fun o => by
    cases o
    · exact ret_framed _
    · exact ret_framed _

theorem letNoneSynF_framed {syn : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s), Fu (ESynth Γ p)}
    (hs : ∀ {s : Sig} (Γ : Ctx s) p, Framed (syn Γ p)) {s : Sig} (Γ : Ctx s) (g : LetTag) (t : PTm s)
    (u : PTm (s,x)) : Framed (letNoneSynF md ms syn Γ g t u) := by
  refine bind_framed (hs _ _) fun r1 => bind_framed (binderE_framed md ms g _) fun o => ?_
  cases o with
  | none => exact ret_framed _
  | some c1 =>
    exact bind_framed (hs _ _) fun r2 =>
      bind_framed (flatMapL_framed (avoidE_framed _ _) _) fun _ => ret_framed _

theorem letNoneChkF_framed {syn : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s), Fu (ESynth Γ p)}
    {chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G)}
    (hs : ∀ {s : Sig} (Γ : Ctx s) p, Framed (syn Γ p)) (hc : ∀ {s : Sig} (Γ : Ctx s) p G, Framed (chk Γ p G))
    {s : Sig} (Γ : Ctx s) (g : LetTag) (t : PTm s) (u : PTm (s,x)) (G : Ty s) :
    Framed (letNoneChkF md ms syn chk Γ g t u G) := by
  refine bind_framed (hs _ _) fun r1 => bind_framed (binderE_framed md ms g _) fun o => ?_
  cases o with
  | none => exact ret_framed _
  | some c1 =>
    exact orElseW_framed (bind_framed (hc _ _ _) fun _ => ret_framed _)
      (bind_framed (hs _ _) fun r2 =>
        bind_framed (flatMapL_framed (avoidE_framed _ _) _) fun _ => subsumeE_framed _ _ _)

end Frames1

/-! ## Tests of slot 1 -/

section TestsSlot1

private abbrev ta : Label := .trm 0
private abbrev tb : Label := .trm 1
private abbrev tF : Label := .typ 0

/-- The function part of a goal, from a full tank. -/
private def partOf {s : Sig} (Γ : Ctx s) (G : Ty s) : FunPart s := (funPartAt Γ G ⟨defaultFuel, false⟩).1

/-- A function type is its own function part. -/
example : partOf .nil (.all .top .top) = .one .top .top := by decide +kernel

/-- Two sides with comparable domains: the larger domain and the meet of the results. -/
example : partOf .nil (.and (.all (.rcd (.trm ta .top)) .top) (.all .top .top)) = .one .top (.and .top .top) := by
  decide +kernel

/-- Two sides with incomparable domains are a mismatch. -/
example : partOf .nil (.and (.all (.rcd (.trm ta .top)) .top) (.all (.rcd (.trm tb .top)) .top)) = .bad := by
  decide +kernel

/-- A singleton goes to the views of its path: `f.type` under `f : ∀(z : ⊤) ⊤`. -/
example : partOf (Ctx.nil.cons (.all .top .top)) (.sngl (.var .here)) = .one .top .top := by decide +kernel

/-- A selection goes to its upper bounds: `x.F` under `x : {F : ⊥..∀(z : ⊤) ⊤}`. -/
example : partOf (Ctx.nil.cons (.rcd (.typ tF .bot (.all .top .top)))) (.sel (.var .here) tF) = .one .top .top := by
  decide +kernel

/-- A `μ` whose body does not mention its self goes to its body. -/
example : partOf .nil (.mu (.all .top .top)) = .one .top .top := by decide +kernel

/-- `⊤` has no function part. -/
example : partOf .nil .top = .none := by decide +kernel

/-- The dominant formal of `g : ∀(z : {a : ⊤}) ⊤` is its domain. -/
example : (argGoalF (Ctx.nil.cons (.all (.rcd (.trm ta .top)) .top)) (.var .here) ⟨defaultFuel, false⟩).1 =
    some (.rcd (.trm ta .top)) := by
  decide +kernel

/-- With no goal, `λx. g x` takes its domain from the callee `g`. -/
example : ((lamCalleeSynF .dot [] (Ctx.nil.cons (.all (.rcd (.trm ta .top)) .top))
    (.app (.var (.there .here)) (.var .here)) ⟨defaultFuel, false⟩).1.1.map (·.ty)) =
    [.all (.rcd (.trm ta .top)) .top] := by
  decide +kernel

/-- `λx. x` has no goal and no callee. -/
example : (lamCalleeSynF .dot [] (Ctx.nil : Ctx []) (.path (.var .here)) ⟨defaultFuel, false⟩).1.2 =
    [.missingParamType none] := by
  decide +kernel

/-- A path checked at its own singleton has no pDOT derivation (N4). -/
example : whyChkR (.path (.var .here) : ATm ([],x)) (.sngl (.var .here)) =
    [.landed (.selfSingleton []), .mismatch] := by
  decide +kernel

end TestsSlot1


/-! ## Dependencies on the self -/

def lookupL {β : Type} : List (Label × β) → Label → Option β
  | [], _ => none
  | (b, v) :: l, a => if a = b then some v else lookupL l a

def Path.headIn {s : Sig} : Path s → List (BVar s .var) → Option Label
  | .var _, _ => none
  | .sel (.var y) a, vs => if vs.contains y then some a else none
  | .sel p _, vs => Path.headIn p vs

def Path.isSelfIn {s : Sig} : Path s → List (BVar s .var) → Bool
  | .var y, vs => vs.contains y
  | .sel _ _, _ => false

mutual
def Ty.heads {s : Sig} (ms : List (Label × List Label)) : Ty s → List (BVar s .var) → List Label
  | .top, _ => []
  | .bot, _ => []
  | .rcd D, vs => Dec.heads ms D vs
  | .and S T, vs => Ty.heads ms S vs ++ Ty.heads ms T vs
  | .sel (.var y) A, vs => if vs.contains y then (lookupL ms A).getD [] else []
  | .sel p _, vs => (Path.headIn p vs).toList
  | .mu T, vs => Ty.heads ms T (vs.map .there)
  | .all S T, vs => Ty.heads ms S vs ++ Ty.heads ms T (vs.map .there)
  | .sngl p, vs => (Path.headIn p vs).toList
def Dec.heads {s : Sig} (ms : List (Label × List Label)) : Dec s → List (BVar s .var) → List Label
  | .typ _ L U, vs => Ty.heads ms L vs ++ Ty.heads ms U vs
  | .trm _ T, vs => Ty.heads ms T vs
end

def optHeads {s : Sig} (ms : List (Label × List Label)) : Option (Ty s) → List (BVar s .var) → List Label
  | some T, vs => Ty.heads ms T vs
  | none, _ => []

def PTm.isAlias {s : Sig} (vs : List (BVar s .var)) : Option (Ty s) → PTm s → Bool
  | none, .path (.var y) => vs.contains y
  | _, _ => false

mutual
def PTm.deps : {s : Sig} → PTm s → List (Label × List Label) → List (BVar s .var) → List Label × Bool
  | _, .path p, _, vs => ((Path.headIn p vs).toList, Path.isSelfIn p vs)
  | _, .app p q, _, vs =>
      ((Path.headIn p vs).toList ++ (Path.headIn q vs).toList, Path.isSelfIn p vs || Path.isSelfIn q vs)
  | _, .lam o t, ms, vs =>
      match t.deps ms (vs.map .there) with
      | (l, b) => (optHeads ms o vs ++ l, b)
  | _, .new o ds, ms, vs =>
      match ds.deps ms (vs.map .there) with
      | (l, b) => (optHeads ms o (vs.map .there) ++ l, b)
  | _, .«let» _ ann t u, ms, vs =>
      if PTm.isAlias vs ann t then u.deps ms (.here :: vs.map .there)
      else
        match t.deps ms vs, u.deps ms (vs.map .there) with
        | (l1, b1), (l2, b2) => (optHeads ms ann vs ++ l1 ++ l2, b1 || b2)
termination_by structural _ t => t
def PDef.deps : {s : Sig} → PDef s → List (Label × List Label) → List (BVar s .var) → List Label × Bool
  | _, .typ _ T, _, vs => (Ty.heads [] T vs, false)
  | _, .path _ q, _, vs => ((Path.headIn q vs).toList, false)
  | _, .lam _ o D t, ms, vs =>
      match t.deps ms (vs.map .there) with
      | (l, b) => (optHeads ms o vs ++ optHeads ms D vs ++ l, b)
  | _, .new _ o es, ms, vs =>
      match es.deps ms (vs.map .there) with
      | (l, b) => (optHeads ms o (vs.map .there) ++ l, b)
termination_by structural _ d => d
def PDefs.deps : {s : Sig} → PDefs s → List (Label × List Label) → List (BVar s .var) → List Label × Bool
  | _, .nil, _, _ => ([], false)
  | _, .cons ds d, ms, vs =>
      match ds.deps ms vs, d.deps ms vs with
      | (l1, b1), (l2, b2) => (l1 ++ l2, b1 || b2)
termination_by structural _ ds => ds
end

def PDefs.typeMembers {s : Sig} : PDefs s → List (Label × Ty s)
  | .nil => []
  | .cons ds (.typ A T) => ds.typeMembers ++ [(A, T)]
  | .cons ds _ => ds.typeMembers

def memberHeadsUpTo {s : Sig} (ts : List (Label × Ty s)) (v : BVar s .var) :
    Nat → List (Label × List Label)
  | 0 => ts.map fun m => (m.1, [])
  | n + 1 => ts.map fun m => (m.1, Ty.heads (memberHeadsUpTo ts v n) m.2 [v])

def PDefs.memberHeads {s : Sig} (d : PDefs s) (v : BVar s .var) : List (Label × List Label) :=
  memberHeadsUpTo d.typeMembers v d.typeMembers.length

/-! ## Slot 3: declarations known at once -/

def PDef.label {s : Sig} : PDef s → Label
  | .typ A _ => A
  | .path a _ => a
  | .lam a _ _ _ => a
  | .new a _ _ => a

mutual
/-- The declaration a definition has without typing anything. -/
def PDef.atOnce? : {s : Sig} → PDef s → Option (Dec s)
  | _, .typ A T => some (.typ A T T)
  | _, .path a q => some (.trm a (.sngl q))
  | _, .lam a (some U) _ _ => some (.trm a U)
  | _, .lam _ none _ _ => none
  | _, .new a (some T) _ => some (.trm a (.mu T))
  | _, .new a none es => (PDefs.atOnce? es).map fun U => .trm a (.mu U)
termination_by structural _ d => d
/-- The self type, in definition order, left nested, when every declaration is known at once. -/
def PDefs.atOnce? : {s : Sig} → PDefs s → Option (Ty s)
  | _, .nil => none
  | _, .cons .nil d => (PDef.atOnce? d).map .rcd
  | _, .cons ds d =>
      match PDefs.atOnce? ds, PDef.atOnce? d with
      | some T, some D => some (.and T (.rcd D))
      | _, _ => none
termination_by structural _ ds => ds
end

/-! ## Slot 2: jobs, rounds -/

structure Job (s : Sig) where
  lbl : Label
  pd : PDef s
  deps : List Label × Bool

structure Done (s : Sig) where
  lbl : Label
  pd : PDef s
  ad : ADef s
  decl : Dec s

def Done.known {s : Sig} (ds : List (Done s)) : List (Label × Dec s) :=
  ds.map fun e => (e.lbl, e.decl)

def lookupDone {s : Sig} : List (Done s) → Label → Option (Done s)
  | [], _ => none
  | e :: es, a => if e.lbl = a then some e else lookupDone es a

def PDef.declIn {s : Sig} (known : List (Label × Dec s)) (d : PDef s) : Option (Dec s) :=
  match PDef.atOnce? d with
  | some D => some D
  | none => lookupL known d.label

/-- The self type known so far, left nested, a pending definition left out. -/
def PDefs.snapshot {s : Sig} (known : List (Label × Dec s)) : PDefs s → Option (Ty s)
  | .nil => none
  | .cons ds d =>
      match PDefs.snapshot known ds, d.declIn known with
      | some T, some D => some (.and T (.rcd D))
      | none, some D => some (.rcd D)
      | o, none => o

/-- The self type in lockstep with the definitions, once every declaration is known. -/
def PDefs.formed {s : Sig} (known : List (Label × Dec s)) : PDefs s → Option (Ty s)
  | .nil => none
  | .cons .nil d => (d.declIn known).map .rcd
  | .cons ds d =>
      match PDefs.formed known ds, d.declIn known with
      | some T, some D => some (.and T (.rcd D))
      | _, _ => none

/-- The heads of the declarations known at once, by label. -/
def PDefs.knownHeads {s : Sig} (ms : List (Label × List Label)) (v : BVar s .var) :
    PDefs s → List (Label × List Label)
  | .nil => []
  | .cons ds d =>
      PDefs.knownHeads ms v ds ++
        match PDef.atOnce? d with
        | some D => [(d.label, Dec.heads ms D [v])]
        | none => []

/-- Labels closed over the heads of the declarations known at once, `n` steps. -/
def closeHeads (tbl : List (Label × List Label)) : Nat → List Label → List Label
  | 0, ls => ls
  | n + 1, ls => ls ++ closeHeads tbl n (ls.flatMap fun l => (lookupL tbl l).getD [])

def PDefs.jobsIn {s : Sig} (tbl : List (Label × List Label)) (ms : List (Label × List Label)) (v : BVar s .var) :
    PDefs s → List (Job s)
  | .nil => []
  | .cons ds d =>
      PDefs.jobsIn tbl ms v ds ++
        match PDef.atOnce? d with
        | some _ => []
        | none =>
            match d.deps ms [v] with
            | (l, b) => [⟨d.label, d, (closeHeads tbl tbl.length l, b)⟩]

/-- The jobs, each with its dependencies closed over the declarations known at once. -/
def PDefs.jobs {s : Sig} (ms : List (Label × List Label)) (v : BVar s .var) (ds : PDefs s) : List (Job s) :=
  ds.jobsIn (ds.knownHeads ms v) ms v

def readyIn {s : Sig} (pend : List Label) (j : Job s) : Bool :=
  j.deps.1.all fun a => !pend.contains a

def bareRound {s : Sig} (js : List (Job s)) : Bool :=
  !(js.any fun j => readyIn (js.map (·.lbl)) j && !j.deps.2)

def picks {s : Sig} (js : List (Job s)) (j : Job s) : Bool :=
  readyIn (js.map (·.lbl)) j && decide (j.deps.2 = bareRound js)

def waitsFor {s : Sig} (js : List (Job s)) (j : Job s) : List Label :=
  j.deps.1.filter fun a => (js.map (·.lbl)).contains a

def nextL {s : Sig} (js : List (Job s)) (l : Label) : Option Label :=
  match js.find? (fun j => decide (j.lbl = l)) with
  | some j => (waitsFor js j).head?
  | none => none

def cycleFrom {s : Sig} (js : List (Job s)) : Nat → List Label → Label → Option Label
  | 0, _, _ => none
  | n + 1, seen, l =>
      if seen.contains l then some l
      else
        match nextL js l with
        | some l' => cycleFrom js n (l :: seen) l'
        | none => none

def cycleAt {s : Sig} (js : List (Job s)) (n : Nat) : Option Label :=
  match js with
  | [] => none
  | j :: _ => cycleFrom js n [] j.lbl

def stallReason {s : Sig} (js : List (Job s)) : PReason :=
  match cycleAt js (js.length + 1) with
  | some l => .cyclicRef l
  | none => .mismatch

/-- One round over the picked jobs, against one snapshot.  The first failure stops it. -/
def roundF {s : Sig} (run : Job s → Fu (Except (List PReason) (Done s))) :
    List (Job s) → Fu (Except (List PReason) (List (Done s)))
  | [] => Fu.ret (.ok [])
  | j :: js =>
      Fu.bind (run j) fun r =>
        match r with
        | .ok e =>
            Fu.bind (roundF run js) fun r' =>
              match r' with
              | .ok es => Fu.ret (.ok (e :: es))
              | .error rs => Fu.ret (.error rs)
        | .error rs => Fu.ret (.error rs)

/-- Rounds until every job is done, at most `n`.  `run P j` types `j` against the snapshot `P`
of the fields done so far. -/
def roundsF {s : Sig} (snap : List (Label × Dec s) → Ty s)
    (run : Ty s → Job s → Fu (Except (List PReason) (Done s))) :
    Nat → List (Job s) → List (Done s) → Fu (Except (List PReason) (List (Done s)))
  | _, [], done => Fu.ret (.ok done)
  | 0, j :: js, _ => Fu.ret (.error [stallReason (j :: js)])
  | n + 1, j :: js, done =>
      if ((j :: js).filter (picks (j :: js))).isEmpty then Fu.ret (.error [stallReason (j :: js)])
      else
        Fu.bind (roundF (run (snap (Done.known done))) ((j :: js).filter (picks (j :: js)))) fun r =>
          match r with
          | .ok new => roundsF snap run n ((j :: js).filter fun k => !picks (j :: js) k) (done ++ new)
          | .error rs => Fu.ret (.error rs)

/-! ## The least candidate -/

def leastFromE {s : Sig} (Γ : Ctx s) {p : PTm s} (Ts : List (Ty s)) :
    List (ECand Γ p) → Fu (Option (ECand Γ p))
  | [] => Fu.ret none
  | c :: rest => Fu.bind (belowAllF Γ c.ty Ts) fun b => if b then Fu.ret (some c) else leastFromE Γ Ts rest

def leastE {s : Sig} (Γ : Ctx s) {p : PTm s} (cs : List (ECand Γ p)) : Fu (Option (ECand Γ p)) :=
  leastFromE Γ (cs.map (·.ty)) cs

/-! ## Running a job -/

/-- The done lambda field of a least candidate of `.lam oD t`. -/
def lamDone {s : Sig} {Γ : Ctx s} (a : Label) (oD : Option (Ty s)) (t : PTm (s,x)) :
    ECand Γ (.lam oD t) → Option (Done s)
  | ⟨.lam S b, T, _, _⟩ => some ⟨a, .lam a none oD t, .lam a S b, .trm a T⟩
  | _ => none

/-- A job against the snapshot `P`: a lambda field by synthesis with the self at `P` and its least
candidate, a nested literal by forming its self type with the self at `P`. -/
def runJobF {s : Sig} (Γ : Ctx s)
    (syn : (Γ' : Ctx (s,x)) → (p : PTm (s,x)) → Fu (ESynth Γ' p))
    (form : (Γ' : Ctx (s,x)) → (es : PDefs ((s,x),x)) → Fu (EForm es))
    (P : Ty (s,x)) (j : Job (s,x)) : Fu (Except (List PReason) (Done (s,x))) :=
  match j.pd with
  | .lam a none oD t =>
      Fu.bind (syn (Γ.consSelf P) (.lam oD t)) fun r =>
        match r.1 with
        | [] => Fu.ret (.error r.2)
        | c :: cs =>
            Fu.bind (leastE (Γ.consSelf P) (c :: cs)) fun o =>
              match o with
              | some e =>
                  match lamDone a oD t e with
                  | some d => Fu.ret (.ok d)
                  | none => Fu.ret (.error [.mismatch])
              | none => Fu.ret (.error [.ambiguous a])
  | .new a none es =>
      Fu.bind (form (Γ.consSelf P) es) fun r =>
        match r with
        | .ok f =>
            if (Ty.mu f.ty).tight then Fu.ret (.ok ⟨a, .new a none es, .new a f.ty f.defs.defs, .trm a (.mu f.ty)⟩)
            else Fu.ret (.error [.landed (.notTight a)])
        | .error rs => Fu.ret (.error rs)
  | _ => Fu.ret (.error [.mismatch])

/-! ## Filling definitions at a self type -/

theorem PDefs.fills_one {s : Sig} {d : PDef s} {D : Dec s} {e : ADef s} (h : d.fills (.rcd D) e = true) :
    (PDefs.cons .nil d).fills (.rcd D) (.cons .nil e) = true := by
  simp [PDefs.fills, h]

theorem PDefs.fills_cons {s : Sig} {ds0 : PDefs s} {d0 d : PDef s} {T : Ty s} {D : Dec s} {es : ADefs s} {e : ADef s}
    (h1 : (PDefs.cons ds0 d0).fills T es = true) (h2 : d.fills (.rcd D) e = true) :
    (PDefs.cons (.cons ds0 d0) d).fills (.and T (.rcd D)) (.cons es e) = true := by
  cases es with
  | nil => simp [PDefs.fills] at h1
  | cons es0 e0 => simp [PDefs.fills, andLeft, andRight, h1, h2]

/- The definitions `ds` filled at the self type `T` in lockstep, the self bound in `Γ`.  A field the
rounds typed holds what they elaborated.  A lambda field is checked at its declaration, which gives
its domain.  A nested literal with a self type has its definitions filled at it, one level down.  A
nested literal without one has its self type formed by `form`. -/
mutual
def defsW (chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G))
    (form : ∀ {s : Sig}, Ctx s → (es : PDefs (s,x)) → Fu (EForm es)) :
    {s : Sig} → (Γ : Ctx s) → List (Done s) → (ds : PDefs s) → (T : Ty s) → Fu (EDefsR ds T)
  | _, Γ, done, .cons .nil d, .rcd D =>
      Fu.bind (defW chk form Γ done d D) fun r =>
        Fu.ret (r.1.map fun e => ⟨.cons .nil e.ad, PDefs.fills_one e.fills⟩, r.2)
  | _, Γ, done, .cons (.cons ds0 d0) d, .and T (.rcd D) =>
      Fu.bind (defsW chk form Γ done (.cons ds0 d0) T) fun r1 =>
        match r1.1 with
        | some e1 =>
            Fu.bind (defW chk form Γ done d D) fun r2 =>
              Fu.ret (r2.1.map fun e2 => ⟨.cons e1.defs e2.ad, PDefs.fills_cons e1.fills e2.fills⟩, r1.2 ++ r2.2)
        | none => Fu.ret (none, r1.2)
  | _, _, _, _, _ => Fu.ret (none, [.mismatch])
termination_by structural _ _ _ ds => ds
def defW (chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G))
    (form : ∀ {s : Sig}, Ctx s → (es : PDefs (s,x)) → Fu (EForm es)) :
    {s : Sig} → (Γ : Ctx s) → List (Done s) → (d : PDef s) → (D : Dec s) → Fu (EDefR d (.rcd D))
  | _, _, _, .typ A T, _ => Fu.ret (some ⟨.typ A T, by simp [PDef.fills]⟩, [])
  | _, _, _, .path a q, _ => Fu.ret (some ⟨.path a q, by simp [PDef.fills]⟩, [])
  | _, Γ, done, .lam a o oD t, D =>
      match lookupDone done a with
      | some e =>
          if h : (PDef.lam a o oD t).fills (.rcd D) e.ad = true then Fu.ret (some ⟨e.ad, h⟩, [])
          else Fu.ret (none, [.mismatch])
      | none =>
          match D with
          | .trm c (.all U V) =>
              Fu.bind (chk Γ (.lam oD t) (.all U V)) fun r =>
                Fu.ret ((r.1.bind fun e => match e with
                  | ⟨.lam S b, _, h⟩ =>
                      if h' : (PDef.lam a o oD t).fills (.rcd (.trm c (.all U V))) (.lam a S b) = true
                      then some ⟨.lam a S b, h'⟩ else none
                  | _ => none), r.2)
          | _ => Fu.ret (none, [.landed (.fieldNotFun a)])
  | _, Γ, done, .new a (some T') es, _ =>
      Fu.bind (defsW chk form (Γ.consSelf T') [] es T') fun r =>
        Fu.ret (r.1.map fun e => ⟨.new a T' e.defs, by simp [PDef.fills, slotAgrees, e.fills]⟩, r.2)
  | _, Γ, done, .new a none es, D =>
      match lookupDone done a with
      | some e =>
          if h : (PDef.new a none es).fills (.rcd D) e.ad = true then Fu.ret (some ⟨e.ad, h⟩, [])
          else Fu.ret (none, [.mismatch])
      | none =>
          match D with
          | .trm _ (.mu U) =>
              orElseW Option.isSome
                (Fu.bind (defsW chk form (Γ.consSelf U) [] es U) fun r =>
                  Fu.ret (r.1.map fun e => ⟨.new a U e.defs, by simp [PDef.fills, slotAgrees, e.fills]⟩, r.2))
                (fun _ => Fu.bind (form Γ es) fun r =>
                  match r with
                  | .ok f => Fu.ret (some ⟨.new a f.ty f.defs.defs, by simp [PDef.fills, slotAgrees, f.defs.fills]⟩, [])
                  | .error rs => Fu.ret (none, rs))
          | _ =>
              Fu.bind (form Γ es) fun r =>
                match r with
                | .ok f => Fu.ret (some ⟨.new a f.ty f.defs.defs, by simp [PDef.fills, slotAgrees, f.defs.fills]⟩, [])
                | .error rs => Fu.ret (none, rs)
termination_by structural _ _ _ d => d
end


/-! ## Literals -/

section Literals
variable (md : Mode) (ms : List (List Label))

def newSynF {s : Sig} (Γ : Ctx s) (ds : PDefs (s,x)) (form : Fu (EForm ds)) : Fu (ESynth Γ (.new none ds)) :=
  Fu.bind form fun r =>
    match r with
    | .ok f => fullSynthAt md ms Γ (.new none ds) (.new f.ty f.defs.defs)
        (by simp [PTm.fills, slotAgrees, f.defs.fills])
    | .error rs => Fu.ret ([], rs)

def newWSynF {s : Sig} (Γ : Ctx s) (T : Ty (s,x)) (ds : PDefs (s,x)) (defs : Fu (EDefsR ds T)) :
    Fu (ESynth Γ (.new (some T) ds)) :=
  Fu.bind defs fun r =>
    match r.1 with
    | some e => fullSynthAt md ms Γ (.new (some T) ds) (.new T e.defs) (by simp [PTm.fills, slotAgrees, e.fills])
    | none => Fu.ret ([], r.2)

end Literals

/-! ## The elaborator

`elabN`, `chkN` and `formN` are one mutual block on an index, as the typer's.  A clause at `k + 1`
calls index `k`.  The entry point starts the index at the size of the term, and each call is on a
part of smaller size, so the index does not run out. -/

mutual
def elabN (md : Mode) (ms : List (List Label)) : Nat → {s : Sig} → (Γ : Ctx s) → (p : PTm s) →
    Fu (ESynth Γ p)
  | 0, _, _, _ => markAs ([], [])
  | k + 1, _, Γ, p =>
      match hp : p.full? with
      | some a => fullSynthAt md ms Γ p a (PTm.fills_of_full? hp)
      | none =>
          match p with
          | .lam (some S) t =>
              Fu.bind (elabN md ms k (Γ.cons S) t) fun r => Fu.ret (lamCands S (slotAgrees_some S) r)
          | .lam none t => lamCalleeSynF md ms Γ t
          | .new (some T) ds =>
              newWSynF md ms Γ T ds (defsW (chkN md ms k) (formN md ms k) (Γ.consSelf T) [] ds T)
          | .new none ds => newSynF md ms Γ ds (formN md ms k Γ ds)
          | .«let» g none t u =>
              match argCallee? g none u, hu : u.full? with
              | some f, some b =>
                  orElseW (fun l => !l.isEmpty)
                    (Fu.bind (argGoalF Γ f) fun oF =>
                      match oF with
                      | some F =>
                          Fu.bind (chkN md ms k Γ t F) fun r =>
                            match r.1 with
                            | some e => fullSynthAt md ms Γ _ (.«let» g none e.a b)
                                (PTm.fills_let' e.fills (PTm.fills_of_full? hu))
                            | none => Fu.ret ([], r.2)
                      | none => Fu.ret ([], []))
                    (fun _ => letNoneSynF md ms (elabN md ms k) Γ g t u)
              | _, _ => letNoneSynF md ms (elabN md ms k) Γ g t u
          | .«let» _ (some W) t u =>
              Fu.bind (chkN md ms k Γ t W) fun r1 =>
                match r1.1 with
                | none => Fu.ret ([], r1.2)
                | some e1 =>
                    Fu.bind (elabN md ms k (Γ.cons W) u) fun r2 =>
                      Fu.bind (Fu.flatMapL (avoidE e1.fills (fun d => .aletS e1.ann d)) r2.1) fun cs =>
                        Fu.ret (dedupE cs, r1.2 ++ r2.2)
          | .path _ => Fu.ret ([], [.mismatch])
          | .app _ _ => Fu.ret ([], [.mismatch])
termination_by structural k => k
def chkN (md : Mode) (ms : List (List Label)) : Nat → {s : Sig} → (Γ : Ctx s) → (p : PTm s) → (G : Ty s) →
    Fu (ECheck Γ p G)
  | 0, _, _, _, _ => markAs (none, [])
  | k + 1, _, Γ, p, G =>
      match hp : p.full? with
      | some a => fullCheckAt md ms Γ p a (PTm.fills_of_full? hp) G
      | none =>
          match p with
          | .lam none t =>
              Fu.bind (funPartAt Γ G) fun fp =>
                match fp with
                | .one S V =>
                    match ht : t.full? with
                    | some b => fullCheckAt md ms Γ _ (.lam S b) (PTm.fills_lam' rfl (PTm.fills_of_full? ht)) G
                    | none => lamGoalF Γ S V G rfl (chkN md ms k (Γ.cons S) t V) (fun _ => elabN md ms k (Γ.cons S) t)
                | .none => lamCalleeChkF md ms Γ G t
                | .bad => Fu.ret (none, [.mismatch])
          | .lam (some S) t =>
              Fu.bind (funPartAt Γ G) fun fp =>
                match fp with
                | .one _ V =>
                    lamGoalF Γ S V G (slotAgrees_some S) (chkN md ms k (Γ.cons S) t V)
                      (fun _ => elabN md ms k (Γ.cons S) t)
                | _ => Fu.bind (elabN md ms k (Γ.cons S) t) fun r => subsumeE Γ G (lamCands S (slotAgrees_some S) r)
          | .new (some T) ds =>
              Fu.bind (newWSynF md ms Γ T ds (defsW (chkN md ms k) (formN md ms k) (Γ.consSelf T) [] ds T))
                (subsumeLit Γ G)
          | .new none ds => Fu.bind (newSynF md ms Γ ds (formN md ms k Γ ds)) (subsumeLit Γ G)
          | .«let» g none t u =>
              match argCallee? g none u, hu : u.full? with
              | some f, some b =>
                  orElseW Option.isSome
                    (Fu.bind (argGoalF Γ f) fun oF =>
                      match oF with
                      | some F =>
                          Fu.bind (chkN md ms k Γ t F) fun r =>
                            match r.1 with
                            | some e => fullCheckAt md ms Γ _ (.«let» g none e.a b)
                                (PTm.fills_let' e.fills (PTm.fills_of_full? hu)) G
                            | none => Fu.ret (none, r.2)
                      | none => Fu.ret (none, []))
                    (fun _ => letNoneChkF md ms (elabN md ms k) (chkN md ms k) Γ g t u G)
              | _, _ => letNoneChkF md ms (elabN md ms k) (chkN md ms k) Γ g t u G
          | .«let» g (some W) t u =>
              Fu.bind (chkN md ms k Γ t W) fun r1 =>
                match r1.1 with
                | none => Fu.ret (none, r1.2)
                | some e1 =>
                    Fu.bind (chkN md ms k (Γ.cons W) u G.weaken) fun r2 =>
                      Fu.ret (r2.1.map (fun e2 => ⟨.«let» g (some W) e1.a e2.a, .aletS e1.ann e2.ann,
                        PTm.fills_let' e1.fills e2.fills⟩), r1.2 ++ r2.2)
          | .path _ => Fu.ret (none, [.mismatch])
          | .app _ _ => Fu.ret (none, [.mismatch])
termination_by structural k => k
def formN (md : Mode) (ms : List (List Label)) : Nat → {s : Sig} → (Γ : Ctx s) → (ds : PDefs (s,x)) →
    Fu (EForm ds)
  | 0, _, _, _ => markAs (.error [])
  | k + 1, _, Γ, ds =>
      let js := ds.jobs (ds.memberHeads .here) .here
      Fu.bind (roundsF (fun known => (ds.snapshot known).getD .top)
          (runJobF Γ (fun Γ' p => elabN md ms k Γ' p) (fun Γ' es => formN md ms k Γ' es))
          (js.length + 1) js []) fun r =>
        match r with
        | .ok done =>
            match ds.formed (Done.known done) with
            | some T =>
                Fu.bind (defsW (chkN md ms k) (formN md ms k) (Γ.consSelf T) done ds T) fun r' =>
                  match r'.1 with
                  | some e => Fu.ret (.ok ⟨T, e⟩)
                  | none => Fu.ret (.error r'.2)
            | none => Fu.ret (.error [.mismatch])
        | .error rs => Fu.ret (.error rs)
termination_by structural k => k
end

/-! ## The entry point -/

def elabTopF (md : Mode) (ms : List (List Label)) (n : Nat) (p : PTm []) :
    Except PReason (ECand Ctx.nil p) × Tank :=
  match elabN md ms p.size Ctx.nil p ⟨n, false⟩ with
  | ((c :: _, _), t) => (if t.out then .error .limit else .ok c, t)
  | (([], rs), t) => (.error (Reason.top t.out rs), t)

/-! ## Frame facts of slots 2 and 3 -/

section Frames2
variable (md : Mode) (ms : List (List Label))

/-! ## Frame facts of the rounds -/

theorem leastFromE_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (Ts : List (Ty s)) :
    ∀ cs : List (ECand Γ p), Framed (leastFromE Γ Ts cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed Γ c.ty Ts) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromE_framed Γ Ts rest

theorem leastE_framed {s : Sig} (Γ : Ctx s) {p : PTm s} (cs : List (ECand Γ p)) :
    Framed (leastE Γ cs) :=
  leastFromE_framed Γ _ cs

theorem runJobF_framed {s : Sig} (Γ : Ctx s)
    {syn : (Γ' : Ctx (s,x)) → (p : PTm (s,x)) → Fu (ESynth Γ' p)}
    {form : (Γ' : Ctx (s,x)) → (es : PDefs ((s,x),x)) → Fu (EForm es)}
    (hs : ∀ Γ' p, Framed (syn Γ' p)) (hf : ∀ Γ' es, Framed (form Γ' es)) (P : Ty (s,x)) (j : Job (s,x)) :
    Framed (runJobF Γ syn form P j) := by
  unfold runJobF
  split
  · refine bind_framed (hs _ _) fun r => ?_
    split
    · exact ret_framed _
    · refine bind_framed (leastE_framed _ _) fun o => ?_
      split
      · split
        · exact ret_framed _
        · exact ret_framed _
      · exact ret_framed _
  · refine bind_framed (hf _ _) fun r => ?_
    split
    · split
      · exact ret_framed _
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem roundF_framed {s : Sig} {run : Job s → Fu (Except (List PReason) (Done s))}
    (hr : ∀ j, Framed (run j)) : ∀ js, Framed (roundF run js)
  | [] => ret_framed _
  | j :: js => by
    refine bind_framed (hr j) fun r => ?_
    cases r with
    | ok e =>
      refine bind_framed (roundF_framed hr js) fun r' => ?_
      cases r' with
      | ok _ => exact ret_framed _
      | error _ => exact ret_framed _
    | error _ => exact ret_framed _

theorem roundsF_framed {s : Sig} (snap : List (Label × Dec s) → Ty s)
    {run : Ty s → Job s → Fu (Except (List PReason) (Done s))} (hr : ∀ P j, Framed (run P j)) :
    ∀ (n : Nat) (js : List (Job s)) (done : List (Done s)), Framed (roundsF snap run n js done)
  | _, [], _ => by
    unfold roundsF
    exact ret_framed _
  | 0, j :: js, _ => by
    unfold roundsF
    exact ret_framed _
  | n + 1, j :: js, done => by
    unfold roundsF
    split
    · exact ret_framed _
    · refine bind_framed (roundF_framed (hr _) _) fun r => ?_
      cases r with
      | ok new => exact roundsF_framed snap hr n _ _
      | error _ => exact ret_framed _

/-! ## Frame facts of the filling -/

mutual
theorem defsW_framed {chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G)}
    {form : ∀ {s : Sig}, Ctx s → (es : PDefs (s,x)) → Fu (EForm es)}
    (hc : ∀ {s : Sig} (Γ : Ctx s) p G, Framed (chk Γ p G)) (hf : ∀ {s : Sig} (Γ : Ctx s) es, Framed (form Γ es)) :
    ∀ {s : Sig} (Γ : Ctx s) (done : List (Done s)) (ds : PDefs s) (T : Ty s),
      Framed (defsW chk form Γ done ds T)
  | _, Γ, done, .cons .nil d, .rcd D => by
      simp only [defsW]
      exact bind_framed (defW_framed hc hf Γ done d D) fun _ => ret_framed _
  | _, Γ, done, .cons (.cons ds0 d0) d, .and T (.rcd D) => by
      simp only [defsW]
      refine bind_framed (defsW_framed hc hf Γ done _ T) fun r1 => ?_
      split
      · exact bind_framed (defW_framed hc hf Γ done d D) fun _ => ret_framed _
      · exact ret_framed _
  | _, _, _, .nil, _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .top => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .bot => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .and _ _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .sel _ _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .mu _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .all _ _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons .nil _, .sngl _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .top => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .bot => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .rcd _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ .top => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ .bot => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ (.and _ _) => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ (.sel _ _) => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ (.mu _) => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ (.all _ _) => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .and _ (.sngl _) => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .sel _ _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .mu _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .all _ _ => by simp only [defsW]; exact ret_framed _
  | _, _, _, .cons (.cons _ _) _, .sngl _ => by simp only [defsW]; exact ret_framed _
theorem defW_framed {chk : ∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Fu (ECheck Γ p G)}
    {form : ∀ {s : Sig}, Ctx s → (es : PDefs (s,x)) → Fu (EForm es)}
    (hc : ∀ {s : Sig} (Γ : Ctx s) p G, Framed (chk Γ p G)) (hf : ∀ {s : Sig} (Γ : Ctx s) es, Framed (form Γ es)) :
    ∀ {s : Sig} (Γ : Ctx s) (done : List (Done s)) (d : PDef s) (D : Dec s),
      Framed (defW chk form Γ done d D)
  | _, _, _, .typ _ _, _ => by simp only [defW]; exact ret_framed _
  | _, _, _, .path _ _, _ => by simp only [defW]; exact ret_framed _
  | _, Γ, done, .lam a o oD t, D => by
      simp only [defW]
      split
      · split
        · exact ret_framed _
        · exact ret_framed _
      · split
        · exact bind_framed (hc _ _ _) fun _ => ret_framed _
        · exact ret_framed _
  | _, Γ, done, .new a (some T') es, _ => by
      simp only [defW]
      exact bind_framed (defsW_framed hc hf _ _ es T') fun _ => ret_framed _
  | _, Γ, done, .new a none es, D => by
      simp only [defW]
      split
      · split
        · exact ret_framed _
        · exact ret_framed _
      · split
        · refine orElseW_framed (bind_framed (defsW_framed hc hf _ _ es _) fun _ => ret_framed _) ?_
          refine bind_framed (hf _ _) fun r => ?_
          cases r with
          | ok _ => exact ret_framed _
          | error _ => exact ret_framed _
        · refine bind_framed (hf _ _) fun r => ?_
          cases r with
          | ok _ => exact ret_framed _
          | error _ => exact ret_framed _
end

theorem newSynF_framed {s : Sig} (Γ : Ctx s) (ds : PDefs (s,x)) {form : Fu (EForm ds)} (hf : Framed form) :
    Framed (newSynF md ms Γ ds form) := by
  refine bind_framed hf fun r => ?_
  cases r with
  | ok _ => exact fullSynthAt_framed md ms _ _ _ _
  | error _ => exact ret_framed _

theorem newWSynF_framed {s : Sig} (Γ : Ctx s) (T : Ty (s,x)) (ds : PDefs (s,x)) {defs : Fu (EDefsR ds T)}
    (hd : Framed defs) : Framed (newWSynF md ms Γ T ds defs) := by
  refine bind_framed hd fun r => ?_
  split
  · exact fullSynthAt_framed md ms _ _ _ _
  · exact ret_framed _

end Frames2

/-! ## The elaborator is framed -/

theorem elab_framed (md : Mode) (ms : List (List Label)) : ∀ (k : Nat),
    (∀ {s : Sig} (Γ : Ctx s) (p : PTm s), Framed (elabN md ms k Γ p)) ∧
    (∀ {s : Sig} (Γ : Ctx s) (p : PTm s) (G : Ty s), Framed (chkN md ms k Γ p G)) ∧
    (∀ {s : Sig} (Γ : Ctx s) (ds : PDefs (s,x)), Framed (formN md ms k Γ ds))
  | 0 => ⟨fun _ _ => markAs_framed _, fun _ _ _ => markAs_framed _, fun _ _ => markAs_framed _⟩
  | k + 1 => by
    obtain ⟨hE, hC, hF⟩ := elab_framed md ms k
    refine ⟨fun Γ p => ?_, fun Γ p G => ?_, fun Γ ds => ?_⟩
    · simp only [elabN]
      split
      · exact fullSynthAt_framed md ms _ _ _ _
      · split
        · exact bind_framed (hE _ _) fun _ => ret_framed _
        · exact lamCalleeSynF_framed md ms _ _
        · exact newWSynF_framed md ms _ _ _ (defsW_framed hC hF _ _ _ _)
        · exact newSynF_framed md ms _ _ (hF _ _)
        · split
          · refine orElseW_framed (bind_framed (argGoalF_framed _ _) fun oF => ?_)
              (letNoneSynF_framed md ms hE _ _ _ _)
            split
            · refine bind_framed (hC _ _ _) fun r => ?_
              split
              · exact fullSynthAt_framed md ms _ _ _ _
              · exact ret_framed _
            · exact ret_framed _
          · exact letNoneSynF_framed md ms hE _ _ _ _
        · refine bind_framed (hC _ _ _) fun r1 => ?_
          split
          · exact ret_framed _
          · exact bind_framed (hE _ _) fun _ =>
              bind_framed (flatMapL_framed (avoidE_framed _ _) _) fun _ => ret_framed _
        · exact ret_framed _
        · exact ret_framed _
    · simp only [chkN]
      split
      · exact fullCheckAt_framed md ms _ _ _ _ _
      · split
        · refine bind_framed (funPartAt_framed _ _) fun fp => ?_
          split
          · split
            · exact fullCheckAt_framed md ms _ _ _ _ _
            · exact lamGoalF_framed _ _ _ _ _ (hC _ _ _) (hE _ _)
          · exact lamCalleeChkF_framed md ms _ _ _
          · exact ret_framed _
        · refine bind_framed (funPartAt_framed _ _) fun fp => ?_
          split
          · exact lamGoalF_framed _ _ _ _ _ (hC _ _ _) (hE _ _)
          · exact bind_framed (hE _ _) fun _ => subsumeE_framed _ _ _
        · exact bind_framed (newWSynF_framed md ms _ _ _ (defsW_framed hC hF _ _ _ _)) fun _ =>
            subsumeLit_framed _ _ _
        · exact bind_framed (newSynF_framed md ms _ _ (hF _ _)) fun _ => subsumeLit_framed _ _ _
        · split
          · refine orElseW_framed (bind_framed (argGoalF_framed _ _) fun oF => ?_)
              (letNoneChkF_framed md ms hE hC _ _ _ _ _)
            split
            · refine bind_framed (hC _ _ _) fun r => ?_
              split
              · exact fullCheckAt_framed md ms _ _ _ _ _
              · exact ret_framed _
            · exact ret_framed _
          · exact letNoneChkF_framed md ms hE hC _ _ _ _ _
        · refine bind_framed (hC _ _ _) fun r1 => ?_
          split
          · exact ret_framed _
          · exact bind_framed (hC _ _ _) fun _ => ret_framed _
        · exact ret_framed _
        · exact ret_framed _
    · simp only [formN]
      refine bind_framed (roundsF_framed _ (fun P j => runJobF_framed _ (fun Γ' p => hE Γ' p)
        (fun Γ' es => hF Γ' es) P j) _ _ _) fun r => ?_
      split
      · split
        · refine bind_framed (defsW_framed hC hF _ _ _ _) fun r' => ?_
          split
          · exact ret_framed _
          · exact ret_framed _
        · exact ret_framed _
      · exact ret_framed _

theorem elabN_framed (md : Mode) (ms : List (List Label)) (k : Nat) {s : Sig} (Γ : Ctx s) (p : PTm s) :
    Framed (elabN md ms k Γ p) :=
  (elab_framed md ms k).1 Γ p

/-! ## Tests of slots 2 and 3 -/

section TestsSlot23

private abbrev lo : Label := .trm 0
private abbrev lp : Label := .trm 1
private abbrev lg : Label := .trm 2
private abbrev lf : Label := .trm 3
private abbrev lh : Label := .trm 4
private abbrev lm : Label := .trm 5
private abbrev la : Label := .trm 6
private abbrev tA : Label := .typ 0

/-- The type of a closed elaboration, from a full tank. -/
private def elabTy? (md : Mode) (p : PTm []) : Option (Ty []) :=
  match (elabTopF md [] defaultFuel p).1 with
  | .ok c => some c.ty
  | .error _ => none

/-- The reason of a closed elaboration, from a full tank. -/
private def elabWhy? (md : Mode) (p : PTm []) : Option PReason :=
  match (elabTopF md [] defaultFuel p).1 with
  | .ok _ => none
  | .error r => some r

/-- `ν(x) {g = λ(u : ⊤). x.f u, f = λ(u : ⊤). u}`: `g` waits for `f`. -/
private def ordP : PTm [] := .new none (.cons (.cons .nil
  (.lam lg none (some .top) (.app (.sel (.var (.there .here)) lf) (.var .here))))
  (.lam lf none (some .top) (.path (.var .here))))

/-- The rounds type `f` first, and the self type is in definition order. -/
example : elabTy? .dot ordP =
    some (.mu (.and (.rcd (.trm lg (.all .top .top))) (.rcd (.trm lf (.all .top .top))))) := by
  decide +kernel

/-- `ν(x) {f = λ(u : ⊤). x.f u}`: a field that waits for itself. -/
private def recP : PTm [] := .new none (.cons .nil
  (.lam lf none (some .top) (.app (.sel (.var (.there .here)) lf) (.var .here))))

example : elabWhy? .dot recP = some (.cyclicRef lf) := by decide +kernel

/-- `ν(x) {o = λ(u : ⊤). x.h u, h = λ(u : ⊤). x.o u}`: two fields that wait for each other. -/
private def cycP : PTm [] := .new none (.cons (.cons .nil
  (.lam lo none (some .top) (.app (.sel (.var (.there .here)) lh) (.var .here))))
  (.lam lh none (some .top) (.app (.sel (.var (.there .here)) lo) (.var .here))))

example : elabWhy? .dot cycP = some (.cyclicRef lo) := by decide +kernel

/-- `λ(r : {a : ⊤}). ν(x) {m = r, f = λ(u : ⊤). x.m}`: `x.m` is at `r.type` and at `{a : ⊤}`,
which pDOT does not compare. -/
private def ambP : PTm [] := .lam (some (.rcd (.trm la .top))) (.new none (.cons (.cons .nil
  (.path lm (.var (.there .here))))
  (.lam lf none (some .top) (.path (.sel (.var (.there .here)) lm)))))

/-- No least candidate in the `.dot` mode. -/
example : elabWhy? .dot ambP = some (.ambiguous lf) := by decide +kernel

/-- The `.scala` mode widens the codomain, and the least candidate exists. -/
example : (elabTy? .scala ambP).isSome = true := by decide +kernel

/-- `ν(x : {f : ∀(u : ⊤) ⊤}) {f = λu. u}`: the domain from the written self type. -/
private def declP : PTm [] := .new (some (.rcd (.trm lf (.all .top .top)))) (.cons .nil
  (.lam lf none none (.path (.var .here))))

example : elabTy? .dot declP = some (.mu (.rcd (.trm lf (.all .top .top)))) := by decide +kernel

/-- The plan's risk: `ν(x) {o = ν(y) {p = ν(z) {g = λ(w : ⊤). x.f w}}, f = λ(u : ⊤). u}`.  The
inner field `g` waits for the outer field `f`, two levels up. -/
private def riskP : PTm [] := .new none (.cons (.cons .nil
  (.new lo none (.cons .nil
    (.new lp none (.cons .nil
      (.lam lg none (some .top) (.app (.sel (.var (.there (.there (.there .here)))) lf) (.var .here))))))))
  (.lam lf none (some .top) (.path (.var .here))))

example : elabTy? .dot riskP = some (.mu (.and
    (.rcd (.trm lo (.mu (.rcd (.trm lp (.mu (.rcd (.trm lg (.all .top .top)))))))))
    (.rcd (.trm lf (.all .top .top))))) := by
  decide +kernel

/-- `ν(x) {o = ν(y) {h = λ(u : ⊤). u, g = λ(w : ⊤). x.f w}, f = λ(u : ⊤). x.o.h u}`: the nested
literal is one job, so `o` and `f` wait for each other (limit L9). -/
private def crossP : PTm [] := .new none (.cons (.cons .nil
  (.new lo none (.cons (.cons .nil
      (.lam lh none (some .top) (.path (.var .here))))
      (.lam lg none (some .top) (.app (.sel (.var (.there (.there .here))) lf) (.var .here))))))
  (.lam lf none (some .top) (.app (.sel (.sel (.var (.there .here)) lo) lh) (.var .here))))

example : elabWhy? .dot crossP = some (.cyclicRef lo) := by decide +kernel

/-- `ν(x) {o = ν(y : {A : ⊥..⊤}) {type A = ⊤}}`: a nested self type that is not tight. -/
private def tightP : PTm [] := .new none (.cons .nil
  (.new lo (some (.rcd (.typ tA .bot .top))) (.cons .nil (.typ tA .top))))

example : elabWhy? .dot tightP = some (.landed (.notTight lo)) := by decide +kernel

/-- `ν(x) {o = x, o = x}`: two definitions at one label. -/
private def dupP : PTm [] := .new none (.cons (.cons .nil (.path lo (.var .here))) (.path lo (.var .here)))

example : elabWhy? .dot dupP = some (.landed (.dupLabel lo)) := by decide +kernel

/-- `ν(x : {f : ⊤}) {f = λ(u : ⊤). u}`: a lambda field declared at a type that is no `∀`. -/
private def notFunP : PTm [] := .new (some (.rcd (.trm lf .top))) (.cons .nil
  (.lam lf none (some .top) (.path (.var .here))))

example : elabWhy? .dot notFunP = some (.landed (.fieldNotFun lf)) := by decide +kernel

/-- `let z : {f : ⊤} = ν(x) {f = x} in z`: a literal checked against a goal it cannot meet. -/
private def litGoalP : PTm [] := .«let» .asc (some (.rcd (.trm lf .top)))
  (.new none (.cons .nil (.path lf (.var .here)))) (.path (.var .here))

example : elabWhy? .dot litGoalP = some (.landed .literalGoal) := by decide +kernel

end TestsSlot23

end PDotFrontend
