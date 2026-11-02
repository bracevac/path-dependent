import Coercions.Nominal.Frontend.Judgment
import Coercions.Nominal.Frontend.Avoid

/-!
# The typer

The typer of the pDOT front end over the annotated terms `ATm`.  This is plan XI
(`plan-11-pdot-frontends.md`), its part "The typer": "Terms and definitions",
"Widening in Scala mode" and D-13, with D-17's least candidate.  The model is the
typer of the Paths front end (`Paths/Frontend/Typer.lean`).

- An answer is a candidate `Cand Γ a`, a type with its derivation `AHasTy Γ a T`.
  So soundness is the result type, and no theorem states it.
- One tank is threaded through every view, search and avoidance the typer calls.
  The typer draws no unit of its own.  A clause at index zero marks the tank.
- `synthN`, `checkN`, `defsN` and `defN` are one mutual block, one clause per
  former in the plan's order.  They recurse on an index, not on the term, since
  `ty_def_new` types the opened definitions, which are no subterm.  The entry
  points `synthF` and `checkF` start the index at `a.size`, which substitution
  keeps, so the index does not run out.
- Two modes.  In `.dot` nothing widens.  In `.scala` the binder of an untyped
  `let` tagged `written` or `widen` is widened by `wideC`, and so is each
  candidate of a lambda's codomain when the body is a path.  A singleton of a
  module path (`Budget.modules`) stays.  A candidate of a term that is not a path
  at the singleton of a non-module path has no widening in pDOT and is dropped.
- The binder of an untyped `let` is the first candidate of the bound term.  The
  body of a `let` is avoided by `avoidLet`.  A check of a `let` first checks the
  body against the weakened goal, then falls back to avoidance and subsumption.
- `leastF` picks the least candidate, below every other by `subF`, for the rounds
  of XF3a (`leastF_least`).
- The frame facts: every function is `Framed` (`typer_framed`), and the entry
  points `synthTopF` and `checkTopF` are stable and monotone in the fuel.

Plan XII N3 g1: `Budget` gains the class labels `classes`, empty by default, so
every budget of plan XI keeps its meaning.  `adnew` reads `tightC`, and `defN`
types `{class C = T}` at `{C : ⊥..T}` by `adclsAt` when `T.clsBody`.  No search
changes.

Plan XII N3 g4 (P10): the typer runs at the class labels `K` and carries the
certificates of D-17.  A candidate `Cand K tg st Γ a` holds `AHasTy.NomAt` and
`AHasTy.SealsAt` under the tags `tg` and the self tag `st`, and the view it comes
from when the term is a path, which `wideC` reads.  `checkN` answers a `CHasTy`.
The tags grow at each binder (plan P2): a lambda's binder is untagged, a
literal's definitions are typed under `push st`, and a `let` types its bound term
at `g.self` and its body under `push g.self`.  A `let` whose tag is `inst p C` and
whose bound term is no literal is refused before any unit is drawn (departure
15).  At `K = []` and no tag, every answer and unit count is plan XI's.
-/

namespace NominalFrontend

open Frontend.Fuel NominalFrontend.Core
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Tm Ctx HasTy Sub IsView)

inductive Mode where
  | dot
  | scala
deriving DecidableEq, Repr

structure Budget where
  fuel : Nat := defaultFuel
  mode : Mode := .dot
  modules : List (List Label) := []
  classes : List Label := []

/-- The bound term is a literal: the only `let` whose tag the typer reads (plan XII P2). -/
def ATm.isNew {s : Sig} : ATm s → Bool
  | .new _ _ => true
  | _ => false

/-- A path term's candidate is a view of the path. -/
def ATm.Viewed {s : Sig} (Γ : Ctx s) : ATm s → Ty s → Prop
  | .path p, T => IsView Γ p T
  | _, _ => True
/-- A candidate: a type with its derivation, its certificates under the tags `tg` and the self tag `st`, and
the view it comes from when the term is a path. -/
structure Cand (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s) where
  ty : Ty s
  deriv : AHasTy Γ a ty
  nom : AHasTy.NomAt K tg st deriv
  ss : AHasTy.SealsAt tg st deriv
  vw : ATm.Viewed Γ a ty
/-- The candidate as a certified derivation. -/
def Cand.toC {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s}
    (c : Cand K tg st Γ a) : CHasTy K tg st Γ a c.ty := ⟨c.deriv, c.nom, c.ss⟩

def dedupC {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s} :
    List (Cand K tg st Γ a) → List (Cand K tg st Γ a)
  | [] => []
  | c :: cs => c :: (dedupC cs).filter fun c' => !decide (c'.ty = c.ty)

def BVar.idx : {s : Sig} → {k : Kind} → BVar s k → Nat
  | _, _, .here => 0
  | _, _, .there y => BVar.idx y + 1

/-- The labels after the stem, when the path is rooted at the oldest variable. -/
def Path.stemLabels? {s : Sig} : Path s → Option (List Label)
  | .var y => if BVar.idx y + 1 = s.length then some [] else none
  | .sel q a => (Path.stemLabels? q).map (· ++ [a])

def isModule (ms : List (List Label)) (q : Path s) : Bool :=
  match Path.stemLabels? q with
  | some ls => ms.contains ls
  | none => false

def keepWide (ms : List (List Label)) : Ty s → Bool
  | .sngl q => isModule ms q
  | _ => true

/-- `wide`: a candidate of a path follows singletons to the first view that is no singleton
or the singleton of a module path.  A candidate of another term at a singleton of a non-module
path has no widening in pDOT and is dropped. -/
def wideC (ms : List (List Label)) {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} :
    {a : ATm s} → Cand K tg st Γ a → Fu (Option (Cand K tg st Γ a))
  | .path _, ⟨.sngl q, d, nom, ss, vw⟩ =>
      if isModule ms q then Fu.ret (some ⟨.sngl q, d, nom, ss, vw⟩) else
      Fu.bind (views Γ q) fun ws =>
        Fu.ret ((ws.find? fun w => keepWide ms w.1).map fun w =>
          ⟨w.1, .apath (.ty_sngl d.erase w.2.d), by exact NomPath.ofView (.sngl vw w.2.iv),
            by exact ⟨AHasTy.sealsAt_erase d ss, HasTy.sealsAt_of_sealFree tg w.2.d w.2.sf⟩, .sngl vw w.2.iv⟩)
  | _, c => Fu.ret (if keepWide ms c.ty then some c else none)

def widens (md : Mode) (g : LetTag s) : Bool :=
  md == .scala && (g == .written || g == .widen)

def binderC (md : Mode) (ms : List (List Label)) (g : LetTag s) {K : List Label} {tg : Tags s}
    {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s} : List (Cand K tg st Γ a) → Fu (Option (Cand K tg st Γ a))
  | [] => Fu.ret none
  | c :: _ => if widens md g then wideC ms c else Fu.ret (some c)

def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

def appC (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (p q : Path s) :
    Fu (List (Cand K tg st Γ (.app p q))) :=
  Fu.bind (views Γ p) fun vs =>
    Fu.bind (Fu.flatMapL (fun v => match v with
        | ⟨.all S T, d⟩ => Fu.bind (pathF K tg Γ q S) fun o =>
            Fu.ret (listO (o.map fun e => (⟨T.substPath q, .aapp (.ty_all_elim d.d e.d), by exact trivial,
              by exact ⟨HasTy.sealsAt_of_sealFree tg d.d d.sf, e.ss⟩, trivial⟩ : Cand K tg st Γ (.app p q))))
        | _ => Fu.ret []) vs) fun cs => Fu.ret (dedupC cs)

def toGoal (K : List Label) {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s} (T : Ty s)
    (cs : Fu (List (Cand K tg st Γ a))) : Fu (Option (CHasTy K tg st Γ a T)) :=
  Fu.bind cs fun l => Fu.firstSome (fun c => mapO (subF K Γ c.ty T) fun e => c.toC.asub e) l

def letAvoidC {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {g : LetTag s}
    {W : Option (Ty s)} {t : ATm s} {u : ATm (s,x)} {V : Ty s} {tgu : Tags (s,x)}
    (mk : {U : Ty s} → CHasTy K tgu none (Γ.cons V) u U.weaken → CHasTy K tg st Γ (.«let» g W t u) U)
    (c : Cand K tgu none (Γ.cons V) u) : Fu (List (Cand K tg st Γ (.«let» g W t u))) :=
  Fu.bind (avoidLet K Γ V c.ty) fun
    | some r =>
        let D := mk (c.toC.asub r.2)
        Fu.ret [⟨r.1, D.d, D.nom, D.ss, trivial⟩]
    | none => Fu.ret []

def lamWide (md : Mode) (ms : List (List Label)) {K : List Label} {tg : Tags (s,x)} {st : Option (Path (s,x) × Label)}
    {Γ : Ctx s} {S : Ty s} {t : ATm (s,x)} (cs : List (Cand K tg st (Γ.cons S) t)) : Fu (List (Cand K tg st (Γ.cons S) t)) :=
  match t with
  | .path _ => if md == .scala then
      Fu.bind (Fu.flatMapL (fun c => Fu.bind (wideC ms c) fun o => Fu.ret (listO o)) cs) fun l => Fu.ret (dedupC l)
    else Fu.ret cs
  | _ => Fu.ret cs

/-- The lambda clause: `∀(z : S) U` for each candidate `U` of the body, widened in Scala mode
when the body is a path. -/
def lamC (md : Mode) (ms : List (List Label)) {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s}
    {S : Ty s} {t : ATm (s,x)} (cs : Fu (List (Cand K (tg.push none) none (Γ.cons S) t))) : Fu (List (Cand K tg st Γ (.lam S t))) :=
  Fu.bind cs fun cs => Fu.bind (lamWide md ms cs) fun cs => Fu.ret (cs.map fun c => ⟨.all S c.ty, .alam c.deriv, c.nom, c.ss, trivial⟩)

section At
variable {K : List Label} {s : Sig} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s}
/-- `alam` at a domain equal to the goal's. -/
def alamAt {S S' : Ty s} {t : ATm (s,x)} {U : Ty (s,x)} (h : S = S') (d : CHasTy K (tg.push none) none (Γ.cons S) t U) :
    CHasTy K tg st Γ (.lam S t) (.all S' U) := by
  cases h
  exact d.alam
/-- `adtyp` at a declaration whose label and bounds are decided equal. -/
def adtypAt {r : Path s} {A B : Label} {T L U : Ty s} (hA : A = B) (hL : T = L) (hU : T = U) :
    CDefTy K tg Γ r (.typ A T) (.typ B L U) := by
  cases hA; cases hL; cases hU
  exact ⟨.adtyp, trivial, trivial⟩
/-- `adpath` at a declaration whose label and path are decided equal. -/
def adpathAt {r : Path s} {b c : Label} {q q' : Path s} {T : Ty s} (hb : b = c) (hq : q = q')
    (d : HasTy Γ (.path q) T) (h : HasTy.SealsAt tg d) : CDefTy K tg Γ r (.path b q) (.trm c (.sngl q')) := by
  cases hb; cases hq
  exact ⟨.adpath d, trivial, h⟩
/-- `adlam` at a declaration whose label is decided equal. -/
def adlamAt {r : Path s} {b c : Label} {S U : Ty s} {t : ATm (s,x)} {V : Ty (s,x)} (hb : b = c)
    (d : CHasTy K tg none Γ (.lam S t) (.all U V)) : CDefTy K tg Γ r (.lam b S t) (.trm c (.all U V)) := by
  cases hb
  exact ⟨.adlam d.d, d.nom, d.ss⟩
/-- `adnew` at a declaration whose label and self type are decided equal. -/
def adnewAt {r : Path s} {b c : Label} {T T' : Ty (s,x)} {ds : ADefs (s,x)} (hb : b = c) (hT : T = T')
    (ht : (Ty.mu T).tightC = true)
    (d : CDefsTy K tg Γ (r.sel b) (ADefs.substPath ds (r.sel b)) (T.substPath (r.sel b))) :
    CDefTy K tg Γ r (.new b T ds) (.trm c (.mu T')) := by
  cases hb; cases hT
  exact ⟨.adnew ht d.d, d.nom, d.ss⟩
/-- `adcls` at a declaration `{B : L..U}` with `C = B`, `L = ⊥` and `T = U` decided, when `T.clsBody`. -/
def adclsAt {r : Path s} {C B : Label} {T L U : Ty s} (hC : C = B) (hL : L = .bot) (hU : T = U) (hb : T.clsBody = true) :
    CDefTy K tg Γ r (.cls C T) (.typ B L U) := by
  cases hC; cases hL; cases hU
  exact ⟨.adcls hb, trivial, trivial⟩
end At


mutual
def synthN (md : Mode) (ms : List (List Label)) (K : List Label) : Nat → {s : Sig} → (tg : Tags s) →
    (st : Option (Path s × Label)) → (Γ : Ctx s) → (a : ATm s) → Fu (List (Cand K tg st Γ a))
  | 0, _, _, _, _, _ => fun t => ([], { t with out := true })
  | _ + 1, _, tg, _, Γ, .path p =>
      Fu.bind (views Γ p) fun vs => Fu.ret (dedupC (vs.map fun v =>
        ⟨v.1, .apath v.2.d, by exact NomPath.ofView v.2.iv, by exact HasTy.sealsAt_of_sealFree tg v.2.d v.2.sf, v.2.iv⟩))
  | _ + 1, _, tg, st, Γ, .app p q => appC K tg st Γ p q
  | k + 1, _, tg, _, Γ, .lam S t => lamC md ms (synthN md ms K k (tg.push none) none (Γ.cons S) t)
  | k + 1, _, tg, st, Γ, .new T ds =>
      Fu.bind (defsN md ms K k (tg.push st) (Γ.consSelf T) (.var .here) ds T) fun
        | some d => Fu.ret [⟨.mu T, .anew d.d, d.nom, d.ss, trivial⟩]
        | none => Fu.ret []
  | k + 1, _, tg, _, Γ, .«let» g none t u =>
      if g.self.isSome && !t.isNew then Fu.ret [] else
      Fu.bind (synthN md ms K k tg g.self Γ t) fun cs => Fu.bind (binderC md ms g cs) fun
        | none => Fu.ret []
        | some c₁ => Fu.bind (synthN md ms K k (tg.push g.self) none (Γ.cons c₁.ty) u) fun cus =>
            Fu.bind (Fu.flatMapL (letAvoidC (fun d => CHasTy.aletN c₁.toC d)) cus) fun l => Fu.ret (dedupC l)
  | k + 1, _, tg, _, Γ, .«let» g (some W) t u =>
      if g.self.isSome && !t.isNew then Fu.ret [] else
      Fu.bind (checkN md ms K k tg g.self Γ t W) fun
        | none => Fu.ret []
        | some d₁ => Fu.bind (synthN md ms K k (tg.push g.self) none (Γ.cons W) u) fun cus =>
            Fu.bind (Fu.flatMapL (letAvoidC (fun d => CHasTy.aletS d₁ d)) cus) fun l => Fu.ret (dedupC l)
termination_by structural k _ _ _ _ => k
def checkN (md : Mode) (ms : List (List Label)) (K : List Label) : Nat → {s : Sig} → (tg : Tags s) →
    (st : Option (Path s × Label)) → (Γ : Ctx s) → (a : ATm s) → (T : Ty s) → Fu (Option (CHasTy K tg st Γ a T))
  | 0, _, _, _, _, _, _ => fun t => (none, { t with out := true })
  | _ + 1, _, tg, _, Γ, .path p, T => mapO (pathF K tg Γ p T) fun d => ⟨.apath d.d, d.nom, d.ss⟩
  | _ + 1, _, tg, st, Γ, .app p q, T => toGoal K T (appC K tg st Γ p q)
  | k + 1, _, tg, _, Γ, .lam S t, T =>
      Fu.orElse (match T with
        | .all S' U => if h : S = S' then mapO (checkN md ms K k (tg.push none) none (Γ.cons S) t U) (alamAt h) else Fu.ret none
        | _ => Fu.ret none) fun _ =>
      toGoal K T (lamC md ms (synthN md ms K k (tg.push none) none (Γ.cons S) t))
  | k + 1, _, tg, st, Γ, .new T₀ ds, T =>
      toGoal K T (Fu.bind (defsN md ms K k (tg.push st) (Γ.consSelf T₀) (.var .here) ds T₀) fun
        | some d => Fu.ret [⟨.mu T₀, .anew d.d, d.nom, d.ss, trivial⟩]
        | none => Fu.ret [])
  | k + 1, _, tg, _, Γ, .«let» g none t u, T =>
      if g.self.isSome && !t.isNew then Fu.ret none else
      Fu.bind (synthN md ms K k tg g.self Γ t) fun cs => Fu.bind (binderC md ms g cs) fun
        | none => Fu.ret none
        | some c₁ =>
            Fu.orElse (mapO (checkN md ms K k (tg.push g.self) none (Γ.cons c₁.ty) u T.weaken) fun d => CHasTy.aletN c₁.toC d) fun _ =>
              toGoal K T (Fu.bind (synthN md ms K k (tg.push g.self) none (Γ.cons c₁.ty) u) fun cus =>
                Fu.bind (Fu.flatMapL (letAvoidC (fun d => CHasTy.aletN c₁.toC d)) cus) fun l => Fu.ret (dedupC l))
  | k + 1, _, tg, _, Γ, .«let» g (some W) t u, T =>
      if g.self.isSome && !t.isNew then Fu.ret none else
      bindO (checkN md ms K k tg g.self Γ t W) fun d₁ =>
        mapO (checkN md ms K k (tg.push g.self) none (Γ.cons W) u T.weaken) fun d => CHasTy.aletS d₁ d
termination_by structural k _ _ _ _ _ => k
def defsN (md : Mode) (ms : List (List Label)) (K : List Label) : Nat → {s : Sig} → (tg : Tags s) → (Γ : Ctx s) →
    (r : Path s) → (ds : ADefs s) → (T : Ty s) → Fu (Option (CDefsTy K tg Γ r ds T))
  | 0, _, _, _, _, _, _ => fun t => (none, { t with out := true })
  | k + 1, _, tg, Γ, r, .cons .nil d, .rcd D => mapO (defN md ms K k tg Γ r d D) fun d => ⟨.adone d.d, d.nom, d.ss⟩
  | k + 1, _, tg, Γ, r, .cons ds d, .and T (.rcd D) =>
      if h : ds.erase.hasnt d.erase.label then
        bindO (defsN md ms K k tg Γ r ds T) fun d₁ => mapO (defN md ms K k tg Γ r d D) fun d₂ =>
          ⟨.adcons d₁.d d₂.d h, by exact ⟨d₁.nom, d₂.nom⟩, by exact ⟨d₁.ss, d₂.ss⟩⟩
      else Fu.ret none
  | _ + 1, _, _, _, _, _, _ => Fu.ret none
termination_by structural k _ _ _ _ _ _ => k
def defN (md : Mode) (ms : List (List Label)) (K : List Label) : Nat → {s : Sig} → (tg : Tags s) → (Γ : Ctx s) →
    (r : Path s) → (d : ADef s) → (D : Dec s) → Fu (Option (CDefTy K tg Γ r d D))
  | 0, _, _, _, _, _, _ => fun t => (none, { t with out := true })
  | _ + 1, _, _, _, _, .typ A T, .typ B L U =>
      Fu.ret (if hA : A = B then if hL : T = L then if hU : T = U then some (adtypAt hA hL hU)
        else none else none else none)
  | _ + 1, _, tg, Γ, _, .path b q, .trm c (.sngl q') =>
      if hb : b = c then if hq : q = q' then
        mapO (firstView Γ q) fun w => adpathAt hb hq w.2.d (HasTy.sealsAt_of_sealFree tg w.2.d w.2.sf)
        else Fu.ret none else Fu.ret none
  | k + 1, _, tg, Γ, _, .lam b S t, .trm c (.all U V) =>
      if hb : b = c then
        mapO (Fu.orElse (if h : S = U then mapO (checkN md ms K k (tg.push none) none (Γ.cons S) t V) (alamAt h) else Fu.ret none)
          fun _ => toGoal K (.all U V) (lamC md ms (synthN md ms K k (tg.push none) none (Γ.cons S) t))) (adlamAt hb)
      else Fu.ret none
  | k + 1, _, tg, Γ, r, .new b T ds, .trm c (.mu T') =>
      if hb : b = c then if hT : T = T' then if ht : (Ty.mu T).tightC = true then
        mapO (defsN md ms K k tg Γ (r.sel b) (ADefs.substPath ds (r.sel b)) (T.substPath (r.sel b))) (adnewAt hb hT ht)
        else Fu.ret none else Fu.ret none else Fu.ret none
  | _ + 1, _, _, _, _, .cls C T, .typ B L U =>
      Fu.ret (if hC : C = B then if hL : L = .bot then if hU : T = U then if hb : T.clsBody = true then
        some (adclsAt hC hL hU hb) else none else none else none else none)
  | _ + 1, _, _, _, _, _, _ => Fu.ret none
termination_by structural k _ _ _ _ _ _ => k
end

/-- `synth Γ a` of the plan: the candidates of `a`, at the index `a.size`. -/
def synthF (md : Mode) (ms : List (List Label)) (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s)
    (a : ATm s) : Fu (List (Cand K tg st Γ a)) := synthN md ms K a.size tg st Γ a
/-- `check Γ a T` of the plan, at the index `a.size`. -/
def checkF (md : Mode) (ms : List (List Label)) (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s)
    (a : ATm s) (T : Ty s) : Fu (Option (CHasTy K tg st Γ a T)) := checkN md ms K a.size tg st Γ a T

/-! ## Frame facts -/

theorem wideC_framed (ms : List (List Label)) {K : List Label} {tg : Tags s} {st : Option (Path s × Label)}
    {Γ : Ctx s} : ∀ {a : ATm s} (c : Cand K tg st Γ a), Framed (wideC ms c)
  | .path _, ⟨.sngl q, d, _, _, _⟩ => by
      unfold wideC
      exact ite_framed (ret_framed _) (bind_framed (views_framed _ _) fun _ => ret_framed _)
  | .path _, ⟨.top, _, _, _, _⟩ | .path _, ⟨.bot, _, _, _, _⟩ | .path _, ⟨.rcd _, _, _, _, _⟩
  | .path _, ⟨.and _ _, _, _, _, _⟩ | .path _, ⟨.sel _ _, _, _, _, _⟩ | .path _, ⟨.mu _, _, _, _, _⟩
  | .path _, ⟨.all _ _, _, _, _, _⟩ => ret_framed _
  | .app _ _, _ | .lam _ _, _ | .new _ _, _ | .«let» _ _ _ _, _ => ret_framed _

theorem binderC_framed (md : Mode) (ms : List (List Label)) (g : LetTag s) {K : List Label} {tg : Tags s}
    {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s} :
    ∀ cs : List (Cand K tg st Γ a), Framed (binderC md ms g cs)
  | [] => ret_framed _
  | c :: _ => by
      unfold binderC
      exact ite_framed (wideC_framed ms c) (ret_framed _)

theorem appC_framed (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (p q : Path s) :
    Framed (appC K tg st Γ p q) := by
  unfold appC
  refine bind_framed (views_framed _ _) fun vs => bind_framed (flatMapL_framed (fun v => ?_) vs) fun _ => ret_framed _
  rcases v with ⟨T, d⟩
  cases T <;> first
    | exact ret_framed _
    | exact bind_framed (pathF_framed _ _ _ _ _) fun _ => ret_framed _

theorem toGoal_framed (K : List Label) {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {a : ATm s}
    (T : Ty s) {cs : Fu (List (Cand K tg st Γ a))} (h : Framed cs) : Framed (toGoal K T cs) :=
  bind_framed h fun l => firstSome_framed (fun _ => mapO_framed _ (subF_framed _ _ _ _)) l

theorem letAvoidC_framed {K : List Label} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} {g : LetTag s}
    {W : Option (Ty s)} {t : ATm s} {u : ATm (s,x)} {V : Ty s} {tgu : Tags (s,x)}
    (mk : {U : Ty s} → CHasTy K tgu none (Γ.cons V) u U.weaken → CHasTy K tg st Γ (.«let» g W t u) U)
    (c : Cand K tgu none (Γ.cons V) u) : Framed (letAvoidC mk c) :=
  bind_framed (avoidLet_framed _ _ _ _) fun o => by
    cases o
    · exact ret_framed _
    · exact ret_framed _

theorem lamWide_framed (md : Mode) (ms : List (List Label)) {K : List Label} {tg : Tags (s,x)}
    {st : Option (Path (s,x) × Label)} {Γ : Ctx s} {S : Ty s} {t : ATm (s,x)}
    (cs : List (Cand K tg st (Γ.cons S) t)) : Framed (lamWide md ms cs) := by
  cases t <;> simp only [lamWide]
  case path p => exact ite_framed (bind_framed (flatMapL_framed (fun c => bind_framed (wideC_framed ms c) fun _ => ret_framed _) cs)
      fun _ => ret_framed _) (ret_framed _)
  all_goals exact ret_framed _

theorem lamC_framed (md : Mode) (ms : List (List Label)) {K : List Label} {tg : Tags s}
    {st : Option (Path s × Label)} {Γ : Ctx s} {S : Ty s} {t : ATm (s,x)}
    {cs : Fu (List (Cand K (tg.push none) none (Γ.cons S) t))} (h : Framed cs) :
    Framed (lamC (st := st) md ms cs) :=
  bind_framed h fun cs => bind_framed (lamWide_framed md ms cs) fun _ => ret_framed _

theorem typer_framed (md : Mode) (ms : List (List Label)) (K : List Label) : ∀ (k : Nat),
    (∀ {s : Sig} (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s),
      Framed (synthN md ms K k tg st Γ a)) ∧
    (∀ {s : Sig} (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s) (T : Ty s),
      Framed (checkN md ms K k tg st Γ a T)) ∧
    (∀ {s : Sig} (tg : Tags s) (Γ : Ctx s) (r : Path s) (ds : ADefs s) (T : Ty s),
      Framed (defsN md ms K k tg Γ r ds T)) ∧
    (∀ {s : Sig} (tg : Tags s) (Γ : Ctx s) (r : Path s) (d : ADef s) (D : Dec s),
      Framed (defN md ms K k tg Γ r d D))
  | 0 => ⟨fun _ _ _ _ => mark_framed _, fun _ _ _ _ _ => mark_framed _, fun _ _ _ _ _ => mark_framed _,
      fun _ _ _ _ _ => mark_framed _⟩
  | k + 1 => by
    obtain ⟨hS, hC, hDs, hD⟩ := typer_framed md ms K k
    refine ⟨fun tg st Γ a => ?_, fun tg st Γ a T => ?_, fun tg Γ r ds T => ?_, fun tg Γ r d D => ?_⟩
    · cases a with
      | path p => simp only [synthN]; exact bind_framed (views_framed _ _) fun _ => ret_framed _
      | app p q => simp only [synthN]; exact appC_framed _ _ _ _ _ _
      | lam S t => simp only [synthN]; exact lamC_framed md ms (hS _ _ _ _)
      | new T ds => simp only [synthN]; exact bind_framed (hDs _ _ _ _ _) fun o => by cases o <;> exact ret_framed _
      | «let» g W t u =>
        cases W with
        | none =>
          simp only [synthN]
          refine ite_framed (ret_framed _) ?_
          exact bind_framed (hS _ _ _ _) fun cs => bind_framed (binderC_framed md ms g cs) fun o => by
            cases o
            · exact ret_framed _
            · exact bind_framed (hS _ _ _ _) fun cus => bind_framed (flatMapL_framed (letAvoidC_framed _) cus) fun _ => ret_framed _
        | some W =>
          simp only [synthN]
          refine ite_framed (ret_framed _) ?_
          exact bind_framed (hC _ _ _ _ _) fun o => by
            cases o
            · exact ret_framed _
            · exact bind_framed (hS _ _ _ _) fun cus => bind_framed (flatMapL_framed (letAvoidC_framed _) cus) fun _ => ret_framed _
    · cases a with
      | path p => simp only [checkN]; exact mapO_framed _ (pathF_framed _ _ _ _ _)
      | app p q => simp only [checkN]; exact toGoal_framed _ _ (appC_framed _ _ _ _ _ _)
      | lam S t =>
        simp only [checkN]
        refine orElse_framed ?_ (toGoal_framed _ _ (lamC_framed md ms (hS _ _ _ _)))
        split
        · exact dite_framed (fun _ => mapO_framed _ (hC _ _ _ _ _)) (fun _ => ret_framed _)
        · exact ret_framed _
      | new T₀ ds => simp only [checkN]; exact toGoal_framed _ _ (bind_framed (hDs _ _ _ _ _) fun o => by cases o <;> exact ret_framed _)
      | «let» g W t u =>
        cases W with
        | none =>
          simp only [checkN]
          refine ite_framed (ret_framed _) ?_
          exact bind_framed (hS _ _ _ _) fun cs => bind_framed (binderC_framed md ms g cs) fun o => by
            cases o
            · exact ret_framed _
            · exact orElse_framed (mapO_framed _ (hC _ _ _ _ _)) (toGoal_framed _ _ (bind_framed (hS _ _ _ _) fun cus =>
                bind_framed (flatMapL_framed (letAvoidC_framed _) cus) fun _ => ret_framed _))
        | some W =>
          simp only [checkN]
          refine ite_framed (ret_framed _) ?_
          exact bindO_framed (hC _ _ _ _ _) fun _ => mapO_framed _ (hC _ _ _ _ _)
    · cases ds with
      | nil => simp only [defsN]; exact ret_framed _
      | cons ds₀ d₀ =>
        cases T with
        | rcd D =>
          cases ds₀ with
          | nil => simp only [defsN]; exact mapO_framed _ (hD _ _ _ _ _)
          | cons _ _ => simp only [defsN]; exact ret_framed _
        | and T₁ T₂ =>
          cases T₂ with
          | rcd D =>
            simp only [defsN]
            exact dite_framed (fun _ => bindO_framed (hDs _ _ _ _ _) fun _ => mapO_framed _ (hD _ _ _ _ _)) fun _ => ret_framed _
          | _ => simp only [defsN]; exact ret_framed _
        | _ => simp only [defsN]; exact ret_framed _
    · cases d with
      | typ A T =>
        cases D with
        | typ B L U => simp only [defN]; exact ret_framed _
        | trm _ _ => simp only [defN]; exact ret_framed _
      | path b q =>
        cases D with
        | trm c V =>
          cases V with
          | sngl q' =>
            simp only [defN]
            exact dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (firstView_framed _ _)) fun _ => ret_framed _)
              fun _ => ret_framed _
          | _ => simp only [defN]; exact ret_framed _
        | typ _ _ _ => simp only [defN]; exact ret_framed _
      | lam b S t =>
        cases D with
        | trm c V =>
          cases V with
          | all U V =>
            simp only [defN]
            exact dite_framed (fun _ => mapO_framed _ (orElse_framed
              (dite_framed (fun _ => mapO_framed _ (hC _ _ _ _ _)) fun _ => ret_framed _)
              (toGoal_framed _ _ (lamC_framed md ms (hS _ _ _ _))))) fun _ => ret_framed _
          | _ => simp only [defN]; exact ret_framed _
        | typ _ _ _ => simp only [defN]; exact ret_framed _
      | new b T ds =>
        cases D with
        | trm c V =>
          cases V with
          | mu T' =>
            simp only [defN]
            exact dite_framed (fun _ => dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (hDs _ _ _ _ _))
              fun _ => ret_framed _) fun _ => ret_framed _) fun _ => ret_framed _
          | _ => simp only [defN]; exact ret_framed _
        | typ _ _ _ => simp only [defN]; exact ret_framed _
      | cls C T =>
        cases D with
        | typ B L U => simp only [defN]; exact ret_framed _
        | trm _ _ => simp only [defN]; exact ret_framed _

theorem synthF_framed (md : Mode) (ms : List (List Label)) (K : List Label) (tg : Tags s)
    (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s) : Framed (synthF md ms K tg st Γ a) :=
  (typer_framed md ms K a.size).1 tg st Γ a
theorem checkF_framed (md : Mode) (ms : List (List Label)) (K : List Label) (tg : Tags s)
    (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s) (T : Ty s) : Framed (checkF md ms K tg st Γ a T) :=
  (typer_framed md ms K a.size).2.1 tg st Γ a T

/-! ## Entry points -/

def firstCand {α : Type} : List α × Tank → Option α × Tank
  | (c :: _, t) => if t.out then (none, t) else (some c, t)
  | ([], t) => (none, t)

def unlessMarked {α : Type} : Option α × Tank → Option α × Tank
  | (o, t) => (if t.out then none else o, t)

def synthTopF (md : Mode) (ms : List (List Label)) (K : List Label) (n : Nat) (a : ATm []) :
    Option (Cand K [] none .nil a) × Tank :=
  firstCand (synthF md ms K [] none Ctx.nil a ⟨n, false⟩)

def checkTopF (md : Mode) (ms : List (List Label)) (K : List Label) (n : Nat) (a : ATm []) (T : Ty []) :
    Option (CHasTy K [] none .nil a T) × Tank :=
  unlessMarked (checkF md ms K [] none Ctx.nil a T ⟨n, false⟩)

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

theorem firstCand_snd {α : Type} (r : List α × Tank) : (firstCand r).2 = r.2 := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, ht]

theorem synthTopF_stable {md : Mode} {ms : List (List Label)} {K : List Label} {n k : Nat} {a : ATm []}
    {r : Option (Cand K [] none .nil a)} (h : synthTopF md ms K n a = (r, ⟨k, false⟩)) (m : Nat) :
    (synthTopF md ms K (n + m) a).1 = r := by
  unfold synthTopF at h ⊢
  cases hs : synthF md ms K [] none Ctx.nil a ⟨n, false⟩ with
  | mk l t' =>
    have ht' : t' = ⟨k, false⟩ := by
      have := firstCand_snd (synthF md ms K [] none Ctx.nil a ⟨n, false⟩)
      rw [h, hs] at this
      exact this.symm
    have hf := (synthF_framed md ms K [] none Ctx.nil a).shift _ _ _ hs (by rw [ht']) m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf, firstCand_add]
    rw [hs] at h
    rw [h]

theorem synthTopF_mono {md : Mode} {ms : List (List Label)} {K : List Label} {n m : Nat} {a : ATm []}
    {c : Cand K [] none .nil a} (h : (synthTopF md ms K n a).1 = some c) (hnm : n ≤ m) :
    (synthTopF md ms K m a).1 = some c := by
  have ho : (synthTopF md ms K n a).2.out = false := firstCand_some h
  have he : synthTopF md ms K n a = (some c, ⟨(synthTopF md ms K n a).2.left, false⟩) := by
    rw [← h, ← ho]
  have := synthTopF_stable he (m - n)
  rw [Nat.add_sub_cancel' hnm] at this
  exact this

theorem checkTopF_stable {md : Mode} {ms : List (List Label)} {K : List Label} {n k : Nat} {a : ATm []}
    {T : Ty []} {r : Option (CHasTy K [] none .nil a T)} (h : checkTopF md ms K n a T = (r, ⟨k, false⟩)) (m : Nat) :
    (checkTopF md ms K (n + m) a T).1 = r := by
  unfold checkTopF unlessMarked at h ⊢
  cases hs : checkF md ms K [] none Ctx.nil a T ⟨n, false⟩ with
  | mk o t' =>
    rw [hs] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    have hf := (checkF_framed md ms K [] none Ctx.nil a T).shift _ _ _ hs rfl m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf]
    simpa [Tank.add] using h1

theorem checkTopF_mono {md : Mode} {ms : List (List Label)} {K : List Label} {n m : Nat} {a : ATm []} {T : Ty []}
    {d : CHasTy K [] none .nil a T} (h : (checkTopF md ms K n a T).1 = some d) (hnm : n ≤ m) :
    (checkTopF md ms K m a T).1 = some d := by
  have ho : (checkTopF md ms K n a T).2.out = false := by
    unfold checkTopF unlessMarked at h ⊢
    cases ht : (checkF md ms K [] none Ctx.nil a T ⟨n, false⟩).2.out <;> simp_all
  have he : checkTopF md ms K n a T = (some d, ⟨(checkTopF md ms K n a T).2.left, false⟩) := by
    rw [← h, ← ho]
  have := checkTopF_stable he (m - n)
  rw [Nat.add_sub_cancel' hnm] at this
  exact this
/-! ## The least candidate (D-17's part) -/

def belowAllF (K : List Label) (Γ : Ctx s) (T : Ty s) : List (Ty s) → Fu Bool
  | [] => Fu.ret true
  | U :: Us =>
      if T = U then belowAllF K Γ T Us
      else Fu.bind (subF K Γ T U) fun
        | some _ => belowAllF K Γ T Us
        | none => Fu.ret false

def leastFromF (K : List Label) (Γ : Ctx s) {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    (Ts : List (Ty s)) : List (Cand K tg st Γ a) → Fu (Option (Cand K tg st Γ a))
  | [] => Fu.ret none
  | c :: rest => Fu.bind (belowAllF K Γ c.ty Ts) fun b => if b then Fu.ret (some c) else leastFromF K Γ Ts rest

def leastF (K : List Label) (Γ : Ctx s) {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    (cs : List (Cand K tg st Γ a)) : Fu (Option (Cand K tg st Γ a)) :=
  leastFromF K Γ (cs.map (·.ty)) cs

theorem belowAllF_sub {K : List Label} {Γ : Ctx s} {T : Ty s} :
    ∀ {Us : List (Ty s)} {t t' : Tank}, belowAllF K Γ T Us t = (true, t') → ∀ U ∈ Us, Nonempty (Sub Γ T U)
  | [], _, _, _, U, hU => absurd hU List.not_mem_nil
  | U' :: Us, t, t', h, U, hU => by
    unfold belowAllF at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hU with rfl | hm
      · exact ⟨heq ▸ .subtyp_refl⟩
      · exact belowAllF_sub h U hm
    · cases hs : subF K Γ T U' t with
      | mk o t1 =>
        simp only [Fu.bind, hs] at h
        cases o with
        | some e =>
          rcases List.mem_cons.mp hU with rfl | hm
          · exact ⟨e.d⟩
          · exact belowAllF_sub h U hm
        | none => simp [Fu.ret] at h

theorem leastFromF_sub {K : List Label} {Γ : Ctx s} {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    {Ts : List (Ty s)} :
    ∀ {cs : List (Cand K tg st Γ a)} {t : Tank} {c : Cand K tg st Γ a} {t' : Tank},
      leastFromF K Γ Ts cs t = (some c, t') → c ∈ cs ∧ ∀ T ∈ Ts, Nonempty (Sub Γ c.ty T)
  | [], _, _, _, h => by simp [leastFromF, Fu.ret] at h
  | c0 :: rest, t, c, t', h => by
    unfold leastFromF at h
    cases hb : belowAllF K Γ c0.ty Ts t with
    | mk b t1 =>
      simp only [Fu.bind, hb] at h
      cases b with
      | true =>
        simp only [if_true, Fu.ret, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self .., belowAllF_sub hb⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨hm, hs⟩ := leastFromF_sub h
        exact ⟨List.mem_cons_of_mem _ hm, hs⟩

theorem leastF_least {K : List Label} {Γ : Ctx s} {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    {cs : List (Cand K tg st Γ a)} {t : Tank} {c : Cand K tg st Γ a} {t' : Tank}
    (h : leastF K Γ cs t = (some c, t')) : c ∈ cs ∧ ∀ c' ∈ cs, Nonempty (Sub Γ c.ty c'.ty) := by
  obtain ⟨hm, hs⟩ := leastFromF_sub h
  exact ⟨hm, fun c' hc' => hs c'.ty (List.mem_map_of_mem hc')⟩

theorem belowAllF_framed (K : List Label) (Γ : Ctx s) (T : Ty s) : ∀ Us, Framed (belowAllF K Γ T Us)
  | [] => ret_framed _
  | U :: Us => by
    unfold belowAllF
    split
    · exact belowAllF_framed K Γ T Us
    · refine bind_framed (subF_framed _ _ _ _) fun o => ?_
      cases o with
      | some _ => exact belowAllF_framed K Γ T Us
      | none => exact ret_framed _

theorem leastFromF_framed (K : List Label) (Γ : Ctx s) {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    (Ts : List (Ty s)) : ∀ cs : List (Cand K tg st Γ a), Framed (leastFromF K Γ Ts cs)
  | [] => ret_framed _
  | c :: rest => by
    refine bind_framed (belowAllF_framed K Γ c.ty Ts) fun b => ?_
    cases b with
    | true => exact ret_framed _
    | false => exact leastFromF_framed K Γ Ts rest

theorem leastF_framed (K : List Label) (Γ : Ctx s) {tg : Tags s} {st : Option (Path s × Label)} {a : ATm s}
    (cs : List (Cand K tg st Γ a)) : Framed (leastF K Γ cs) :=
  leastFromF_framed K Γ _ cs
/-! ## Tests -/

section Tests

/-- The types of a term's candidates in `Γ` from a full tank. -/
def synthTys (b : Budget) (Γ : Ctx s) (a : ATm s) : List (Ty s) × Bool :=
  let r := synthF b.mode b.modules b.classes [] none Γ a ⟨b.fuel, false⟩
  (r.1.map (·.ty), r.2.out)

abbrev tyA : Label := .trm 0
abbrev tyB : Label := .trm 1
/-- `[q : {a : ⊤}, x : q.type]`. -/
abbrev tyG : Ctx (([],x),x) := (Ctx.nil.cons (.rcd (.trm tyA .top))).cons (.sngl (.var .here))
/-- `let y = x in y`, with a tag. -/
abbrev tyLet (g : LetTag (([],x),x)) : ATm (([],x),x) := .«let» g none (.path (.var .here)) (.path (.var .here))

example : ((synthTys {} tyG (tyLet .written)).1.head?) = some (.sngl (.var (.there .here))) := by decide +kernel
example : ((synthTys { mode := .scala } tyG (tyLet .written)).1.head?) = some (.rcd (.trm tyA .top)) := by decide +kernel
example : ((synthTys { mode := .scala } tyG (tyLet .arg)).1.head?) = some (.sngl (.var (.there .here))) := by decide +kernel
example : ((synthTys { mode := .scala, modules := [[]] } tyG (tyLet .widen)).1.head?) =
    some (.sngl (.var (.there .here))) := by decide +kernel
/-- `λ(u : ⊤). x`: the codomain widened in Scala mode only. -/
example : ((synthTys {} tyG (.lam .top (.path (.var (.there .here))))).1.head?) =
    some (.all .top (.sngl (.var (.there (.there .here))))) := by decide +kernel
example : ((synthTys { mode := .scala } tyG (.lam .top (.path (.var (.there .here))))).1.head?) =
    some (.all .top (.rcd (.trm tyA .top))) := by decide +kernel
/-- The least candidate of `y` under `y : {a : ⊤} ∧ {b : ⊤}` is the intersection. -/
abbrev lstG : Ctx ([],x) := Ctx.nil.cons (.and (.rcd (.trm tyA .top)) (.rcd (.trm tyB .top)))
example : ((Fu.bind (synthF .dot [] [] [] none lstG (.path (.var .here))) (leastF [] lstG)) ⟨defaultFuel, false⟩).1.map (·.ty) =
    some (.and (.rcd (.trm tyA .top)) (.rcd (.trm tyB .top))) := by decide +kernel
abbrev mA : Label := .typ 0
abbrev mc : Label := .trm 0
/-- `{A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}`: two upper bounds of `A`, the loose one first. -/
abbrev mX {s : Sig} : Ty s := .and (.rcd (.typ mA .bot .top)) (.rcd (.typ mA .bot (.rcd (.trm mc .top))))
/-- `λ(f : ∀(z : X) z.A). λ(x : X). let y = x in f y`. -/
def mProg : ATm [] :=
  .lam (.all mX (.sel (.var .here) mA)) (.lam mX (.«let» .written none (.path (.var .here))
    (.app (.var (.there (.there .here))) (.var .here))))
/-- The goal with the inner domain `X ∧ ⊤`, so `checkN` synthesizes the inner lambda and avoids `y.A`. -/
def mGoal : Ty [] := .all (.all mX (.sel (.var .here) mA)) (.all (.and mX .top) (.rcd (.trm mc .top)))
example : (checkTopF .dot [] [] defaultFuel mProg mGoal).1.isSome = true := by decide +kernel
/-- A literal meets a goal only through subsumption of its `μ`. -/
example : (checkTopF .dot [] [] defaultFuel (.new (.rcd (.trm tyA (.sngl (.var .here)))) (.cons .nil (.path tyA (.var .here))))
    (.mu (.rcd (.trm tyA (.sngl (.var .here)))))).1.isSome = true := by decide +kernel

end Tests

end NominalFrontend
