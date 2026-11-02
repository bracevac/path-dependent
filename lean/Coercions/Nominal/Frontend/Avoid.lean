import Coercions.Nominal.Frontend.Sub

/-!
# Avoidance at a `let`

A `let x = t in u` whose body has the type `U'` under the binder `x : V` needs a
type `U` of the outer context with `U'` below `U↑`.  `avoidLet` finds one, by the
steps of `plan-11-pdot-frontends.md` ("Avoidance"), in this order.

1. `str`: `U'` is a weakening, read back by `Ty.unweaken`.  The derivation is
   `subtyp_refl`, and no unit is spent.
2. The alias steps: the first singleton view `m.type` of the binder whose path
   `m` is free of it, and the first view of `m`.  Each step reroots one path at
   `m` by `subtyp_sngl_pq`, with the replacement found by `Repl.find?`, and the
   steps are chained by `subtyp_trans`, at most `Ty.nodes U'` of them.
3. `up` and `down` follow the types.  Under `up` a selection rooted at the binder
   goes to the meet of `up` of every upper bound, each by `subtyp_sel1`, the meet
   by `subtyp_and2`.  Under `down` it goes to `down` of its first lower bound by
   `subtyp_sel2`.  A singleton rooted at the binder and a `μ` that mentions it go
   to `⊤` or `⊥`.  Records go by `subtyp_fld` and `subtyp_typ`, `∀` by
   `subtyp_all` with the codomain under the approximated domain, `∧` by
   `subtyp_and2` over `subtyp_and11` and `subtyp_and12`.  A selection met again
   at the same polarity, keyed by its labels after the root, is cut.
4. Strengthening of the result of `up`, failing which `⊤`.

`up` and `down` draw `cost` of the number of pending selections from the tank of
XF1, with the fuel left as the index.  A short tank answers `none`.

The frame facts: `up`, `down`, the alias step and `avoidLet` are `Framed`, `up`
and `down` agree across indices, and `avoidLet` never loses what strengthening
finds (`avoidLet_strengthen`).

Plan XII N3 g4 (P9): every step carries its certificates (D-17).  `up` returns
`Above K Γ T`, a type with a `SubAns K Γ T U`: the selection case is Up-Upper
(`NomSub.upper`), every other former gives no class selection.  `down` returns
`Below Γ T` with seal-freedom only, since its results sit under `subtyp_typ`
and `subtyp_all`, where no certificate is asked.  The alias steps return
`Aliased Γ T`, the `UpStar` path itself, one Up-ReplPQ step each, and
`avoidLet K` composes it with `up`'s result by `NomSub.ofUpStar`.  `down` reads
a first lower bound only at a label outside `K`, and returns `⊥` at a class
label (departure 12).  D-21 needs no code: `up` at an escaping class selection
`z.C` reads the upper bound, which at a class is its body.
-/

namespace NominalFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Ctx HasTy Sub Repl UpStar)
open Nominal.FCn (PRename)

mutual
def Ty.mentions : {s : Sig} → BVar s .var → Ty s → Bool
  | _, _, .top => false
  | _, _, .bot => false
  | _, z, .rcd D => Dec.mentions z D
  | _, z, .and T U => Ty.mentions z T || Ty.mentions z U
  | _, z, .sel p _ => decide (p.root = z)
  | _, z, .mu T => Ty.mentions (.there z) T
  | _, z, .all S T => Ty.mentions z S || Ty.mentions (.there z) T
  | _, z, .sngl p => decide (p.root = z)
termination_by structural _ _ T => T
def Dec.mentions : {s : Sig} → BVar s .var → Dec s → Bool
  | _, z, .typ _ L U => Ty.mentions z L || Ty.mentions z U
  | _, z, .trm _ T => Ty.mentions z T
termination_by structural _ _ D => D
end

/-- The path with its root replaced by `m`: `(z.nomExt bs)` becomes `m.nomExt bs`. -/
def Path.reroot : Path s → Path s → Path s
  | .var _, m => m
  | .sel l a, m => .sel (Path.reroot l m) a

mutual
/-- The type with its first path rooted at `z` rerooted at `m`. -/
def Ty.replFirst : {s : Sig} → BVar s .var → Path s → Ty s → Option (Ty s)
  | _, _, _, .top => none
  | _, _, _, .bot => none
  | _, z, m, .rcd D => (Dec.replFirst z m D).map .rcd
  | _, z, m, .and T U => match Ty.replFirst z m T with
      | some T' => some (.and T' U)
      | none => (Ty.replFirst z m U).map (.and T)
  | _, z, m, .sel l A => if l.root = z then some (.sel (Path.reroot l m) A) else none
  | _, z, m, .mu T => (Ty.replFirst (.there z) m.weaken T).map .mu
  | _, z, m, .all S T => match Ty.replFirst z m S with
      | some S' => some (.all S' T)
      | none => (Ty.replFirst (.there z) m.weaken T).map (.all S)
  | _, z, m, .sngl l => if l.root = z then some (.sngl (Path.reroot l m)) else none
termination_by structural _ _ _ T => T
def Dec.replFirst : {s : Sig} → BVar s .var → Path s → Dec s → Option (Dec s)
  | _, z, m, .typ A L U => match Ty.replFirst z m L with
      | some L' => some (.typ A L' U)
      | none => (Ty.replFirst z m U).map (.typ A L)
  | _, z, m, .trm a T => (Ty.replFirst z m T).map (.trm a)
termination_by structural _ _ _ D => D
end

/-- A type above `T`, with the derivation and its certificates: `NomSub`, no seal. -/
abbrev Above (K : List Label) (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × SubAns K Γ T U
/-- A type below `T`, with the derivation, no seal. -/
abbrev Below (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × (e : Sub Γ U T) ×' Sub.SealFree e
/-- A type reached from `T` by alias steps: the derivation, the `Up` path, no seal. -/
abbrev Aliased (Γ : Ctx s) (T : Ty s) : Type := (U : Ty s) × (e : Sub Γ T U) ×' (UpStar Γ T U ∧ Sub.SealFree e)

/-- Every occurrence rooted at `z` rerooted at `m`, one `subtyp_sngl_pq` step at a time, each an Up-ReplPQ step. -/
def aliasAll {Γ : Ctx s} {z : BVar s .var} {m : Path s} (w : Viewed Γ (.var z) (.sngl m)) (wm : View Γ m) :
    Nat → (T : Ty s) → Aliased Γ T
  | 0, T => ⟨T, .subtyp_refl, .refl, trivial⟩
  | k + 1, T =>
      match Ty.replFirst z m T with
      | none => ⟨T, .subtyp_refl, .refl, trivial⟩
      | some T₁ =>
          match Repl.find? (.var z) m T T₁ with
          | none => ⟨T, .subtyp_refl, .refl, trivial⟩
          | some r =>
              let rest := aliasAll w wm k T₁
              ⟨rest.1, .subtyp_trans (.subtyp_sngl_pq w.d wm.2.d r) rest.2.1,
                .step (.replPQ w.iv ⟨wm.2.d⟩ ⟨r⟩) rest.2.2.1, by exact ⟨⟨w.sf, wm.2.sf⟩, rest.2.2.2⟩⟩

def Ty.nodes : Ty s → Nat
  | .rcd (.typ _ L U) => Ty.nodes L + Ty.nodes U + 1
  | .rcd (.trm _ T) => Ty.nodes T + 1
  | .and T U => Ty.nodes T + Ty.nodes U + 1
  | .mu T => Ty.nodes T + 1
  | .all S T => Ty.nodes S + Ty.nodes T + 1
  | _ => 1

/-- The alias step: the first singleton view `m↑.type` of the binder, `m` free of it. -/
def aliasStep (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) : Fu (Aliased (Γ.cons V) U') :=
  Fu.bind (views (Γ.cons V) (.var .here)) fun vs =>
    let cands := (sngls vs).filter fun e => (Nominal.FCn.Path.unrename e.1 PRename.unsucc).isSome
    match cands with
    | [] => Fu.ret ⟨U', .subtyp_refl, .refl, trivial⟩
    | e :: _ => Fu.bind (firstView (Γ.cons V) e.1) fun
        | none => Fu.ret ⟨U', .subtyp_refl, .refl, trivial⟩
        | some wm => Fu.ret (aliasAll e.2 wm (Ty.nodes U') U')

def sels : Path s → List Label
  | .var _ => []
  | .sel p a => sels p ++ [a]

abbrev SelKey := List Label × Label × Bool

/-- `⊤` above any type. -/
def Above.top {K : List Label} {Γ : Ctx s} {T : Ty s} : Above K Γ T := ⟨.top, .subtyp_top, NomSub.top, trivial⟩
/-- `T` above itself. -/
def Above.refl {K : List Label} {Γ : Ctx s} {T : Ty s} : Above K Γ T := ⟨T, .subtyp_refl, NomSub.refl, trivial⟩

/-- The meet of types above `T`: their intersection, by `subtyp_and2`.  One type is itself,
and no type is `⊤`. -/
def meetAll {K : List Label} {s : Sig} {Γ : Ctx s} {T : Ty s} : List (Above K Γ T) → Above K Γ T
  | [] => Above.top
  | [a] => a
  | a :: b :: rest =>
      let r := meetAll (b :: rest)
      ⟨.and a.1 r.1, .subtyp_and2 a.2.d r.2.d, NomSub.and, by exact ⟨a.2.sf, r.2.sf⟩⟩
termination_by structural l => l

/-- The types above `T` with a repeated type left out, the first kept. -/
def dedupA {K : List Label} {s : Sig} {Γ : Ctx s} {T : Ty s} : List (Above K Γ T) → List (Above K Γ T)
  | [] => []
  | a :: rest => a :: (dedupA rest).filter fun a' => !decide (a'.1 = a.1)

mutual
def up (K : List Label) {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List SelKey → (T : Ty s) → Fu (Above K Γ T)
  | 0, _, _ => fun t => (Above.top, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret Above.top
        | true =>
          if !Ty.mentions z T then Fu.ret Above.refl else
          match T with
          | .sel q A =>
              if (sels q, A, true) ∈ P then Fu.ret Above.top else
              Fu.bind (bounds Γ q A) fun bs =>
                Fu.bind (Fu.flatMapL (fun b =>
                    Fu.bind (up K Γ z d ((sels q, A, true) :: P) b.hi) fun r =>
                      Fu.ret [⟨r.1, .subtyp_trans (.subtyp_sel1 b.d) r.2.d, NomSub.upper b.iv r.2.nom,
                        by exact ⟨b.sf, r.2.sf⟩⟩]) bs) fun rs =>
                  Fu.ret (meetAll (dedupA rs))
          | .rcd (.trm a U) => Fu.bind (up K Γ z d P U) fun r =>
              Fu.ret ⟨.rcd (.trm a r.1), .subtyp_fld r.2.d, NomSub.rcd, r.2.sf⟩
          | .rcd (.typ A L U) =>
              Fu.bind (down K Γ z d P L) fun l =>
                Fu.bind (up K Γ z d P U) fun h =>
                  Fu.ret ⟨.rcd (.typ A l.1 h.1), .subtyp_typ l.2.1 h.2.d, NomSub.rcd, by exact ⟨l.2.2, h.2.sf⟩⟩
          | .and T₁ T₂ =>
              Fu.bind (up K Γ z d P T₁) fun r₁ =>
                Fu.bind (up K Γ z d P T₂) fun r₂ =>
                  Fu.ret ⟨.and r₁.1 r₂.1,
                    .subtyp_and2 (.subtyp_trans .subtyp_and11 r₁.2.d) (.subtyp_trans .subtyp_and12 r₂.2.d), NomSub.and,
                    by exact ⟨⟨trivial, r₁.2.sf⟩, ⟨trivial, r₂.2.sf⟩⟩⟩
          | .all S T' =>
              Fu.bind (down K Γ z d P S) fun l =>
                Fu.bind (up K (Γ.cons l.1) (.there z) d P T') fun c =>
                  Fu.ret ⟨.all l.1 c.1, .subtyp_all l.2.1 c.2.d, NomSub.all, by exact ⟨l.2.2, c.2.sf⟩⟩
          | _ => Fu.ret Above.top
termination_by structural d _ _ => d
def down (K : List Label) {s : Sig} (Γ : Ctx s) (z : BVar s .var) : Nat → List SelKey → (T : Ty s) → Fu (Below Γ T)
  | 0, _, _ => fun t => (⟨.bot, .subtyp_bot, trivial⟩, { t with out := true })
  | d + 1, P, T =>
      Fu.bind (draw (cost P.length)) fun
        | false => Fu.ret ⟨.bot, .subtyp_bot, trivial⟩
        | true =>
          if !Ty.mentions z T then Fu.ret ⟨T, .subtyp_refl, trivial⟩ else
          match T with
          | .sel q A =>
              if (sels q, A, false) ∈ P then Fu.ret ⟨.bot, .subtyp_bot, trivial⟩ else
              if A ∈ K then Fu.ret ⟨.bot, .subtyp_bot, trivial⟩ else
              Fu.bind (bounds Γ q A) fun
                | b :: _ => Fu.bind (down K Γ z d ((sels q, A, false) :: P) b.lo) fun r =>
                    Fu.ret ⟨r.1, .subtyp_trans r.2.1 (.subtyp_sel2 b.d), by exact ⟨r.2.2, b.sf⟩⟩
                | [] => Fu.ret ⟨.bot, .subtyp_bot, trivial⟩
          | .rcd (.trm a U) => Fu.bind (down K Γ z d P U) fun r => Fu.ret ⟨.rcd (.trm a r.1), .subtyp_fld r.2.1, r.2.2⟩
          | .rcd (.typ A L U) =>
              Fu.bind (up K Γ z d P L) fun l =>
                Fu.bind (down K Γ z d P U) fun h =>
                  Fu.ret ⟨.rcd (.typ A l.1 h.1), .subtyp_typ l.2.d h.2.1, by exact ⟨l.2.sf, h.2.2⟩⟩
          | .and T₁ T₂ =>
              Fu.bind (down K Γ z d P T₁) fun r₁ =>
                Fu.bind (down K Γ z d P T₂) fun r₂ =>
                  Fu.ret ⟨.and r₁.1 r₂.1,
                    .subtyp_and2 (.subtyp_trans .subtyp_and11 r₁.2.1) (.subtyp_trans .subtyp_and12 r₂.2.1),
                    by exact ⟨⟨trivial, r₁.2.2⟩, ⟨trivial, r₂.2.2⟩⟩⟩
          | .all S T' =>
              Fu.bind (up K Γ z d P S) fun l =>
                Fu.bind (down K (Γ.cons S) (.there z) d P T') fun c =>
                  Fu.ret ⟨.all l.1 c.1, .subtyp_all l.2.d c.2.1, by exact ⟨l.2.sf, c.2.2⟩⟩
          | _ => Fu.ret ⟨.bot, .subtyp_bot, trivial⟩
termination_by structural d _ _ => d
end

/-- The result type of a `let`: `U` with `U'` below `U↑`, certified. -/
abbrev LetTy (K : List Label) (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) : Type := (U : Ty s) × SubAns K (Γ.cons V) U' U.weaken

def strengthen {K : List Label} {Γ : Ctx s} {V : Ty s} {U' : Ty (s,x)} (r : Above K (Γ.cons V) U') : LetTy K Γ V U' :=
  match h : NominalFrontend.Ty.unweaken r.1 with
  | some U => ⟨U, (NominalFrontend.Ty.unweaken_iff.mp h) ▸ r.2⟩
  | none => ⟨.top, .subtyp_top, NomSub.top, trivial⟩

def unlessOut {α : Type} (a : α) : Fu (Option α) := fun t => if t.out then (none, t) else (some a, t)

/-- The step `str`: `U'` is a weakening, read back by `Ty.unweaken`. -/
def strengthen? {K : List Label} {Γ : Ctx s} {V : Ty s} (U' : Ty (s,x)) : Option (LetTy K Γ V U') :=
  if h : (NominalFrontend.Ty.unweaken U').isSome then
    some ⟨(NominalFrontend.Ty.unweaken U').get h,
      (NominalFrontend.Ty.unweaken_iff.mp (Option.some_get h).symm) ▸ ⟨.subtyp_refl, NomSub.refl, trivial⟩⟩
  else none

/-- Avoidance at a `let`: strengthening, else the alias steps, then `up`, then strengthening, else `⊤`. -/
def avoidLet (K : List Label) (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) : Fu (Option (LetTy K Γ V U')) :=
  match strengthen? U' with
  | some r => Fu.ret (some r)
  | none =>
      Fu.bind (aliasStep Γ V U') fun a =>
        Fu.bind (fun t => up K (Γ.cons V) .here t.left [] a.1 t) fun r =>
          unlessOut (strengthen ⟨r.1, .subtyp_trans a.2.1 r.2.d, NomSub.ofUpStar a.2.2.1 r.2.nom, by exact ⟨a.2.2.2, r.2.sf⟩⟩)

/-! ## Frame facts -/

theorem ite_framed {α : Type} {p : Prop} [hp : Decidable p] {a b : Fu α} (ha : Framed a)
    (hb : Framed b) : Framed (if p then a else b) := by
  cases hp
  · exact hb
  · exact ha
theorem dite_framed {α : Type} {p : Prop} [hp : Decidable p] {a : p → Fu α} {b : ¬p → Fu α}
    (ha : ∀ h, Framed (a h)) (hb : ∀ h, Framed (b h)) : Framed (dite p a b) := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

theorem upDown_framed (K : List Label) : ∀ (d : Nat) {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List SelKey)
    (T : Ty s), Framed (up K Γ z d P T) ∧ Framed (down K Γ z d P T)
  | 0, _, _, _, _, _ => ⟨mark_framed _, mark_framed _⟩
  | d + 1, s, Γ, z, P, T => by
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List SelKey) (T : Ty s),
        Framed (up K Γ z d P T) ∧ Framed (down K Γ z d P T) := fun Γ z P T => upDown_framed K d Γ z P T
    constructor
    · simp only [up]
      apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | sel q A =>
          apply ite_framed (ret_framed _)
          refine bind_framed (bounds_framed Γ q A) fun bs => ?_
          refine bind_framed (flatMapL_framed (fun b => ?_) bs) fun _ => ret_framed _
          exact bind_framed (ih Γ z _ _).1 fun _ => ret_framed _
        | rcd D =>
          cases D with
          | trm a U => exact bind_framed (ih Γ z P U).1 fun _ => ret_framed _
          | typ A L U => exact bind_framed (ih Γ z P L).2 fun _ => bind_framed (ih Γ z P U).1 fun _ => ret_framed _
        | and T₁ T₂ => exact bind_framed (ih Γ z P T₁).1 fun _ => bind_framed (ih Γ z P T₂).1 fun _ => ret_framed _
        | all S T' => exact bind_framed (ih Γ z P S).2 fun l => bind_framed (ih (Γ.cons l.1) (.there z) P T').1 fun _ => ret_framed _
        | mu _ => exact ret_framed _
        | sngl _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _
    · simp only [down]
      apply bind_framed (draw_framed _)
      intro ok
      cases ok
      · exact ret_framed _
      · apply ite_framed (ret_framed _)
        cases T with
        | sel q A =>
          apply ite_framed (ret_framed _)
          apply ite_framed (ret_framed _)
          refine bind_framed (bounds_framed Γ q A) fun bs => ?_
          cases bs with
          | nil => exact ret_framed _
          | cons b _ => exact bind_framed (ih Γ z _ _).2 fun _ => ret_framed _
        | rcd D =>
          cases D with
          | trm a U => exact bind_framed (ih Γ z P U).2 fun _ => ret_framed _
          | typ A L U => exact bind_framed (ih Γ z P L).1 fun _ => bind_framed (ih Γ z P U).2 fun _ => ret_framed _
        | and T₁ T₂ => exact bind_framed (ih Γ z P T₁).2 fun _ => bind_framed (ih Γ z P T₂).2 fun _ => ret_framed _
        | all S T' => exact bind_framed (ih Γ z P S).1 fun _ => bind_framed (ih (Γ.cons S) (.there z) P T').2 fun _ => ret_framed _
        | mu _ => exact ret_framed _
        | sngl _ => exact ret_framed _
        | top => exact ret_framed _
        | bot => exact ret_framed _

theorem upDown_agree (K : List Label) : ∀ (d d' : Nat), d ≤ d' → ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var)
    (P : List SelKey) (T : Ty s),
    Agree (up K Γ z d P T) (up K Γ z d' P T) ∧ Agree (down K Γ z d P T) (down K Γ z d' P T)
  | 0, d', _, s, Γ, z, P, T => by
    refine ⟨⟨(upDown_framed K 0 Γ z P T).1, (upDown_framed K d' Γ z P T).1, ?_⟩,
      ⟨(upDown_framed K 0 Γ z P T).2, (upDown_framed K d' Γ z P T).2, ?_⟩⟩
    · intro t r t' h ho _
      simp only [up, Prod.mk.injEq] at h
      rw [← h.2] at ho
      simp at ho
    · intro t r t' h ho _
      simp only [down, Prod.mk.injEq] at h
      rw [← h.2] at ho
      simp at ho
  | d + 1, d', hd, s, Γ, z, P, T => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih : ∀ {s : Sig} (Γ : Ctx s) (z : BVar s .var) (P : List SelKey) (T : Ty s),
        Agree (up K Γ z d P T) (up K Γ z e P T) ∧ Agree (down K Γ z d P T) (down K Γ z e P T) :=
      fun Γ z P T => upDown_agree K d e (by omega) Γ z P T
    constructor
    · simp only [up]
      apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | sel q A =>
          apply ite_agree (ret_agree _)
          refine bind_agree (Agree.refl (bounds_framed Γ q A)) fun bs => ?_
          refine bind_agree (flatMapL_agree (fun b => ?_) bs) fun _ => ret_agree _
          exact bind_agree (ih Γ z _ _).1 fun _ => ret_agree _
        | rcd D =>
          cases D with
          | trm a U => exact bind_agree (ih Γ z P U).1 fun _ => ret_agree _
          | typ A L U => exact bind_agree (ih Γ z P L).2 fun _ => bind_agree (ih Γ z P U).1 fun _ => ret_agree _
        | and T₁ T₂ => exact bind_agree (ih Γ z P T₁).1 fun _ => bind_agree (ih Γ z P T₂).1 fun _ => ret_agree _
        | all S T' => exact bind_agree (ih Γ z P S).2 fun l => bind_agree (ih (Γ.cons l.1) (.there z) P T').1 fun _ => ret_agree _
        | mu _ => exact ret_agree _
        | sngl _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _
    · simp only [down]
      apply bind_agree (draw_agree _)
      intro ok
      cases ok
      · exact ret_agree _
      · apply ite_agree (ret_agree _)
        cases T with
        | sel q A =>
          apply ite_agree (ret_agree _)
          apply ite_agree (ret_agree _)
          refine bind_agree (Agree.refl (bounds_framed Γ q A)) fun bs => ?_
          cases bs with
          | nil => exact ret_agree _
          | cons b _ => exact bind_agree (ih Γ z _ _).2 fun _ => ret_agree _
        | rcd D =>
          cases D with
          | trm a U => exact bind_agree (ih Γ z P U).2 fun _ => ret_agree _
          | typ A L U => exact bind_agree (ih Γ z P L).1 fun _ => bind_agree (ih Γ z P U).2 fun _ => ret_agree _
        | and T₁ T₂ => exact bind_agree (ih Γ z P T₁).2 fun _ => bind_agree (ih Γ z P T₂).2 fun _ => ret_agree _
        | all S T' => exact bind_agree (ih Γ z P S).1 fun _ => bind_agree (ih (Γ.cons S) (.there z) P T').2 fun _ => ret_agree _
        | mu _ => exact ret_agree _
        | sngl _ => exact ret_agree _
        | top => exact ret_agree _
        | bot => exact ret_agree _

theorem aliasStep_framed (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) : Framed (aliasStep Γ V U') := by
  unfold aliasStep
  refine bind_framed (views_framed _ _) fun vs => ?_
  dsimp only
  split
  · exact ret_framed _
  · exact bind_framed (firstView_framed _ _) fun o => by
      cases o
      · exact ret_framed _
      · exact ret_framed _

theorem unlessOut_framed {α : Type} (a : α) : Framed (unlessOut a) where
  absorbs t ht := by simp [unlessOut, ht]
  spends t := by
    unfold unlessOut
    cases t.out <;> exact Nat.le_refl _
  shift := by
    intro t r t' h ho k
    unfold unlessOut at h ⊢
    cases hto : t.out
    · simp only [hto, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Tank.add, hto]
    · simp only [hto, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hto] at ho

theorem avoidLet_framed (K : List Label) (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) : Framed (avoidLet K Γ V U') := by
  unfold avoidLet
  cases strengthen? (K := K) (Γ := Γ) (V := V) U' with
  | some _ => exact ret_framed _
  | none =>
    refine bind_framed (aliasStep_framed _ _ _) fun a => bind_framed ?_ fun _ => unlessOut_framed _
    exact atLeft_framed fun d d' hd => (upDown_agree K d d' hd (Γ.cons V) .here [] a.1).1

theorem strengthen?_fst {K : List Label} {Γ : Ctx s} {V : Ty s} (U' : Ty (s,x)) :
    (strengthen? (K := K) (Γ := Γ) (V := V) U').map (·.1) = NominalFrontend.Ty.unweaken U' := by
  unfold strengthen?
  split
  · rename_i h
    simp only [Option.map_some, Option.some_get]
  · rename_i h
    simp only [Option.map_none]
    cases hu : NominalFrontend.Ty.unweaken U' with
    | none => rfl
    | some _ => rw [hu] at h; simp at h
theorem avoidLet_strengthen {K : List Label} {Γ : Ctx s} {V : Ty s} {U' : Ty (s,x)} {U : Ty s}
    (h : NominalFrontend.Ty.unweaken U' = some U) (t : Tank) : (avoidLet K Γ V U' t).1.map (·.1) = some U := by
  have hs := strengthen?_fst (K := K) (Γ := Γ) (V := V) U'
  rw [h] at hs
  unfold avoidLet
  cases hr : strengthen? (K := K) (Γ := Γ) (V := V) U' with
  | some r =>
    rw [hr] at hs
    simpa [Fu.ret] using hs
  | none =>
    rw [hr] at hs
    simp at hs

section Checks

def avoidAt (K : List Label) (Γ : Ctx s) (V : Ty s) (U' : Ty (s,x)) (n : Nat := defaultFuel) :
    Option (Ty s) × Tank :=
  let r := avoidLet K Γ V U' ⟨n, false⟩
  (r.1.map (·.1), r.2)

abbrev avA : Label := .typ 0
abbrev ava : Label := .trm 0
abbrev avG : Ctx ([],x) := Ctx.nil.cons (.rcd (.typ avA .top .top))
abbrev avMu : Ty [] := .mu (.rcd (.typ avA .bot (.rcd (.trm ava .top))))
/-- `{A : ⊥..⊤} ∧ {A : ⊥..{a : ⊤}}`: two upper bounds of `A`, the loose one first. -/
abbrev avTwo : Ty [] := .and (.rcd (.typ avA .bot .top)) (.rcd (.typ avA .bot (.rcd (.trm ava .top))))

example : avoidAt (s := []) [] Ctx.nil .top (Ty.weaken (.rcd (.trm ava .top))) =
    (some (.rcd (.trm ava .top)), ⟨defaultFuel, false⟩) := by decide +kernel
example : (avoidAt [] avG (.sngl (.var .here)) (.sel (.var .here) avA)).1 = some (.sel (.var .here) avA) := by
  decide +kernel
example : (avoidAt [] avG (.sngl (.var .here)) (.sel (.var .here) avA)).2.out = false := by decide +kernel
example : (avoidAt [] Ctx.nil avMu (.sel (.var .here) avA)).1 = some (.rcd (.trm ava .top)) := by decide +kernel
example : (avoidAt [] Ctx.nil avTwo (.sel (.var .here) avA)).1 = some (.and .top (.rcd (.trm ava .top))) := by
  decide +kernel
example : (avoidAt [] Ctx.nil avMu (.all (.sel (.var .here) avA) .top)).1 = some (.all .bot .top) := by decide +kernel
example : (avoidAt [] Ctx.nil avMu (.sngl (.var .here))).1 = some .top := by decide +kernel
example : (avoidAt [] Ctx.nil avMu (.mu (.sngl (.var (.there .here))))).1 = some .top := by decide +kernel
example : avoidAt [] Ctx.nil avMu (.sel (.var .here) avA) 0 = (none, ⟨0, true⟩) := by decide +kernel

/-- A class label of the D-21 check. -/
abbrev avC : Label := .typ 1
/-- The body of the D-21 check, `μ(y. {a : ⊤}) ∧ ⊤`. -/
abbrev avBody : Ty [] := .and (.mu (.rcd (.trm ava .top))) .top
/-- D-21: an escaping class selection `z.C`, `C` a class label, widens to its body `μ(y. {a : ⊤}) ∧ ⊤`. -/
example : (avoidAt [avC] Ctx.nil (.mu (.rcd (.typ avC .bot avBody.weaken))) (.sel (.var .here) avC)).1 = some avBody := by
  decide +kernel

end Checks

end NominalFrontend.Core
