import LambdaP.Soundness.RealizedSubst

/-!
The Δ-level facts table (`DOut`), version 2 — the declarative twin of
`SOut`, carried by the realized substitution motive. Version 1's
anchor-tight residue slots were refuted by a machine-checked
counterexample (high-low anchor alternation); v2 stores every
recursive residue at the cell's own bound, keeps member/interval/
codomain legs in push-context lazy form (the `SOut` mirror, composing
by narrowing and transitivity), and carries mutual lazy legs on the
tsel-congruence cells. Instantiation of push legs happens only inside
the realized substitution, at bare component images, with the
image-location descent.
-/

namespace LambdaP

def CapturedTok (Θ : Sto) {s : Sig} (Δ : Ctx s) (p : Path s) : Prop :=
  ∃ r : Path s, r.root.IsBound ∧ Path.Wf Θ Δ r ∧
    Sub Θ Δ (.ty (.single p)) (.ty (.single r))

/-- Δ-level runtime path equivalence: the singles-cell content, the
scope-generic twin of `PEq` (matrix verdict correction 6: it carries
the CHAINS, not just mutual subs — dcompose needs the targets).
Skip-generated non-Wf aliases stay here (they are never emitted as
capture mediators). `congr` is the repl-template generator; its `Wf`
premises live at Δ, hence the context index. -/
inductive CoChain (Θ : Sto) : {s : Sig} → Ctx s → Path s → Path s → Prop where
| refl {s : Sig} {Δ : Ctx s} {p : Path s} :
    CoChain Θ Δ p p
| symm {s : Sig} {Δ : Ctx s} {p q : Path s} :
    CoChain Θ Δ p q → CoChain Θ Δ q p
| trans {s : Sig} {Δ : Ctx s} {p q r : Path s} :
    CoChain Θ Δ p q → CoChain Θ Δ q r → CoChain Θ Δ p r
| cochain {s : Sig} {Δ : Ctx s} {p q : Path s} {ℓ0 : Nat} :
    Chains Θ p ℓ0 → Chains Θ q ℓ0 → CoChain Θ Δ p q
| skip_tm {s : Sig} {Δ : Ctx s} {p : Path s} {ℓ : Nat} {S : Ty 0}
    {b : Name} {Tc : Ty 1} {a : Name} :
    Chains Θ p ℓ → Sto.Lookup Θ ℓ (.pairTm S b Tc) → a ≠ b →
    CoChain Θ Δ (p.sel a) ((Path.fst p).sel a)
| skip_ty {s : Sig} {Δ : Ctx s} {p : Path s} {ℓ : Nat} {S : Ty 0}
    {B : Name} {T1 T2 : Ty 1} {a : Name} :
    Chains Θ p ℓ → Sto.Lookup Θ ℓ (.pairTy S B T1 T2) →
    CoChain Θ Δ (p.sel a) ((Path.fst p).sel a)
| congr {s : Sig} {Δ : Ctx s} {p q : Path s} {r : Path (s+1)} :
    Path.Wf Θ Δ p → Path.Wf Θ Δ q → CoChain Θ Δ p q →
    CoChain Θ Δ (Path.subst r (Subst.openPath p)) (Path.subst r (Subst.openPath q))

/-- The production guard of the substR motive: a cell is owed for every
substituted conclusion except those whose subject is a bound-rooted
SINGLE (those re-derive directly, and trans skips their cells via
captured-transfer). Bound-rooted tsel subjects DO get cells (the
re-application rows below). -/
def Ty.CellDue : Ty s → Prop
| .single p => ¬ p.root.IsBound
| _ => True

/-- The Δ-level facts table, v2. -/
inductive DOut (Θ : Sto) : {s : Sig} → Ctx s → Nat → Ty s → Ty s → Prop where
| refl {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} :
    DOut Θ Δ n T T
| captured {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s} {T2 : Ty s} :
    CapturedTok Θ Δ p →
    DOut Θ Δ n (.single p) T2
| bot_tok {s : Sig} {Δ : Ctx s} {n : Nat} {T1 T2 : Ty s} :
    Sub Θ Δ (.ty T1) (.ty .bot) →
    DOut Θ Δ n T1 T2
| botL {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} :
    DOut Θ Δ n .bot T
| topR {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} :
    DOut Θ Δ n T .top
| single {s : Sig} {Δ : Ctx s} {n : Nat} {p q : Path s} :
    CoChain Θ Δ p q →
    DOut Θ Δ n (.single p) (.single q)
/-- Uniform unfold: a chaining single subject reads off through its
entry; the residual cell lives at the SAME bound (the v2 fix), the
lazy leg composes with raw premises in trans. -/
| sngl_unfold {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s}
    {ℓ0 : Nat} {E : Ty 0} {X : Ty s} :
    Chains Θ p ℓ0 →
    Sto.Lookup Θ ℓ0 E →
    ℓ0 < n →
    DOut Θ Δ n (Ty.fromClosed E) X →
    Sub Θ Δ (.ty (Ty.fromClosed E)) (.ty X) →
    DOut Θ Δ n (.single p) X
/-- Tsel on the right, RHS-anchored; residue at the cell bound. -/
| tsel_r {s : Sig} {Δ : Ctx s} {n : Nat} {X : Ty s} {q : Path s}
    {mq ℓ1 : Nat} {A : Name} {W : Ty 0} :
    Chains Θ q mq →
    Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
      (Ty.weaken W) (Ty.weaken W)) →
    mq < n →
    DOut Θ Δ n X (Ty.fromClosed W) →
    Sub Θ Δ (.ty X) (.ty (Ty.fromClosed W)) →
    DOut Θ Δ n X (.tsel q A)
/-- Tsel on the left, subject-anchored; residue at the cell bound. -/
| tsel_l {s : Sig} {Δ : Ctx s} {n : Nat} {Y : Ty s} {q : Path s}
    {mq ℓ1 : Nat} {A : Name} {W : Ty 0} :
    Chains Θ q mq →
    Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
      (Ty.weaken W) (Ty.weaken W)) →
    mq < n →
    DOut Θ Δ n (Ty.fromClosed W) Y →
    Sub Θ Δ (.ty (Ty.fromClosed W)) (.ty Y) →
    DOut Θ Δ n (.tsel q A) Y
/-- Tsel congruence with CARRIED mutual lazy legs (closes the
tsel_co∘reapp corner: producers — repl, refl, trans — always have
them; skip-generated co-chains never make tsel cells). -/
| tsel_co {s : Sig} {Δ : Ctx s} {n : Nat} {p q : Path s} {A : Name} :
    CoChain Θ Δ p q →
    Sub Θ Δ (.ty (.single p)) (.ty (.single q)) →
    Sub Θ Δ (.ty (.single q)) (.ty (.single p)) →
    DOut Θ Δ n (.tsel p A) (.tsel q A)
/-- Re-application through a bound-rooted wellformed mediator,
tsel-subject orientation. -/
| reapp_l {s : Sig} {Δ : Ctx s} {n : Nat} {q r : Path s}
    {S : Ty s} {A : Name} {T1 T2 : Ty (s+1)} {Y : Ty s} :
    r.root.IsBound →
    Path.Wf Θ Δ r →
    Path.Wf Θ Δ q →
    Sub Θ Δ (.ty (.single q)) (.ty (.single r)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) →
    Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) →
    DOut Θ Δ n (T2.open r.fst) Y →
    Sub Θ Δ (.ty (T2.open r.fst)) (.ty Y) →
    DOut Θ Δ n (.tsel q A) Y
/-- Re-application, tsel-RHS orientation. -/
| reapp_r {s : Sig} {Δ : Ctx s} {n : Nat} {q r : Path s}
    {S : Ty s} {A : Name} {T1 T2 : Ty (s+1)} {X : Ty s} :
    r.root.IsBound →
    Path.Wf Θ Δ r →
    Path.Wf Θ Δ q →
    Sub Θ Δ (.ty (.single q)) (.ty (.single r)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) →
    Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) →
    DOut Θ Δ n X (T1.open r.fst) →
    Sub Θ Δ (.ty X) (.ty (T1.open r.fst)) →
    DOut Θ Δ n X (.tsel q A)
/-- Arrow diagonal: recursive contravariant first component (+ lazy),
lazy codomain at the push context. -/
| arrow {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {T T' : Ty (s+1)} :
    DOut Θ Δ n S' S →
    Sub Θ Δ (.ty S') (.ty S) →
    Sub Θ (Δ.push S') (.ty T) (.ty T') →
    DOut Θ Δ n (.arrow S T) (.arrow S' T')
/-- pairTm diagonal. -/
| pair_tm {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {a : Name}
    {T T' : Ty (s+1)} :
    DOut Θ Δ n S S' →
    Sub Θ Δ (.ty S) (.ty S') →
    Sub Θ (Δ.push S) (.ty T) (.ty T') →
    DOut Θ Δ n (.pairTm S a T) (.pairTm S' a T')
/-- pairTy diagonal. -/
| pair_ty {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {A : Name}
    {T1 T2 T1' T2' : Ty (s+1)} :
    DOut Θ Δ n S S' →
    Sub Θ Δ (.ty S) (.ty S') →
    Sub Θ (Δ.push S) (.ty T1') (.ty T1) →
    Sub Θ (Δ.push S) (.ty T2) (.ty T2') →
    DOut Θ Δ n (.pairTy S A T1 T2) (.pairTy S' A T1' T2')

/-- Monotone in the location bound. -/
theorem DOut.mono {s : Sig} {Θ : Sto} {Δ : Ctx s} {n n' : Nat} {T1 T2 : Ty s}
    (h : DOut Θ Δ n T1 T2) (hle : n ≤ n') : DOut Θ Δ n' T1 T2 := by
  induction h with
  | refl => exact .refl
  | captured hc => exact .captured hc
  | bot_tok hb => exact .bot_tok hb
  | botL => exact .botL
  | topR => exact .topR
  | single hco => exact .single hco
  | sngl_unfold hc hE hm d1 l1 ih =>
    exact .sngl_unfold hc hE (by omega) ih l1
  | tsel_r hc hE hm d1 l1 ih =>
    exact .tsel_r hc hE (by omega) ih l1
  | tsel_l hc hE hm d1 l1 ih =>
    exact .tsel_l hc hE (by omega) ih l1
  | tsel_co hco l1 l2 => exact .tsel_co hco l1 l2
  | reapp_l hrb hwr hwq hlk hev hgd d1 l1 ih =>
    exact .reapp_l hrb hwr hwq hlk hev hgd ih l1
  | reapp_r hrb hwr hwq hlk hev hgd d1 l1 ih =>
    exact .reapp_r hrb hwr hwq hlk hev hgd ih l1
  | arrow d1 l1 l2 ih => exact .arrow ih l1 l2
  | pair_tm d1 l1 l2 ih => exact .pair_tm ih l1 l2
  | pair_ty d1 l1 l2 l3 ih => exact .pair_ty ih l1 l2 l3

end LambdaP
