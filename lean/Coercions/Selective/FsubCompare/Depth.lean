import Coercions.Selective.FsubCompare.Family
/-!
# Narrowing at arrow depth, and a stress family for `Cert.allInv`

Part A: a bound step `X ≤₀ Z` sitting `d` arrow codomains deep, narrowed along
`dYZ : Y ⇒ Z`. SelFsub: `Cert.narrow`. FCsub: the substitution `LeCo.substitute` of the
inclusion-evidence variable `h : X <: Z` by `h' ; (Y <: Z)`.

Part B: `Cert.allInv` on a chain of `n` universal bound changes whose first body step uses
the bound rule of the bound variable `Z` at arrow depth `d` (the body step is the only one
that `narrow` has to rewrite), in both associations of `;`.
-/
namespace Compare.Depth
open SelFsub (Ty Ctx Cert Sub synthC)
open Compare.Fam (chainCtx tt)

def arrPow : Nat → Ty n → Ty n
  | 0, T => T
  | d+1, T => .arr .top (arrPow d T)

/-! ## Part A -/

/-- `Z <: Top→Top, Y <: Z`. -/
def Γ2 : Ctx 2 := .snoc (.snoc .nil tt) (.var 0)
/-- original `X <: Z` and narrowed `X <: Y` -/
def ΓZ : Ctx 3 := Γ2.snoc (.var 1)
def ΓY : Ctx 3 := Γ2.snoc (.var 0)
def dYZ : Cert 2 := .step (.var 0) (.var 1)
def stepD (d : Nat) : Cert 3 := .step (arrPow d (.var 0)) (arrPow d (.var 2))

theorem stepD_ok (d : Nat) (h : d ≤ 8) : synthC ΓZ (stepD d) = some (arrPow d (.var 0), arrPow d (.var 2)) := by
  revert d; decide
theorem narrowD_ok (d : Nat) (h : d ≤ 8) :
    synthC ΓY ((stepD d).narrow 0 dYZ) = some (arrPow d (.var 0), arrPow d (.var 2)) := by
  revert d; decide

def selNarrow (d : Nat) : List Nat := Sel.row ((stepD d).narrow 0 dYZ)

/-- FCsub evidence for the same step: `arr (refl top) (… (var h))`. -/
def deepEv : (d : Nat) → {s : FCsub.Sig} → FCsub.LeCo s → FCsub.LeCo s
  | 0, _, e => e
  | d+1, _, e => .arr (.refl .top) (deepEv d e.weaken)

def fcStep (d : Nat) : FCsub.LeCo (Sg 3) := deepEv d (.var .here)

/-- Narrowing as a substitution of the inclusion variable of `X`. -/
def narrowSubst : FCsub.Subst (Sg 3) (Sg 3) :=
  { FCsub.Subst.id with
    inclusionVar := fun v =>
      if v = (.here : FCsub.BVar (Sg 3) (.evidence .inclusion)) then
        .trans (.var .here) (.var (evOf 3 1))
      else .var v }

def fcNarrow (d : Nat) : FCsub.LeCo (Sg 3) := (fcStep d).substitute narrowSubst

theorem fcStep_ok (d : Nat) (h : d ≤ 8) :
    FCsub.synthLe (ctxOf ΓZ) (fcStep d) = some (tyOf (arrPow d (.var 0)), tyOf (arrPow d (.var 2))) := by
  revert d; decide +kernel
theorem fcNarrow_ok (d : Nat) (h : d ≤ 8) :
    FCsub.synthLe (ctxOf ΓY) (fcNarrow d) = some (tyOf (arrPow d (.var 0)), tyOf (arrPow d (.var 2))) := by
  revert d; decide +kernel

def fcRow (d : Nat) : List Nat := Fc.row (Fc.cnt (fcNarrow d))
def fcRow0 (d : Nat) : List Nat := Fc.row (Fc.cnt (fcStep d))
def selRow0 (d : Nat) : List Nat := Sel.row (stepD d)

def partA : List (Nat × List Nat × List Nat × List Nat × List Nat) :=
  (List.range 9).map fun d => (d, selRow0 d, selNarrow d, fcRow0 d, fcRow d)
#eval partA

/-! ## Part B -/

/-- `Sᵢ`: `S₀ = ∀(Z <: X₀). Z^d`, `Sᵢ = ∀(Z <: Xᵢ). X₁^d` for `i ≥ 1` (`Zᵈ` = `Top → … → Z`). -/
def sTy (n d i : Nat) : Ty (n+1) :=
  .all (.var (Fin.ofNat (n+1) (n - i)))
    (arrPow d (if i = 0 then .var 0 else .var (Fin.ofNat (n+2) n)))

def sLinks (n d : Nat) : Nat → Nat → Cert (n+1)
  | _, 0 => .step (sTy n d 0) (sTy n d 0)
  | i, 1 => .step (sTy n d i) (sTy n d (i+1))
  | i, m+2 => .seq (.step (sTy n d i) (sTy n d (i+1))) (sLinks n d (i+1) (m+1))

/-- Right-nested `l₁ ; (l₂ ; (… ; lₙ))`. -/
def sCertR (n d : Nat) : Cert (n+1) := sLinks n d 0 n

/-- Left-nested `((l₁ ; l₂) ; …) ; lₙ`. -/
def sCertL (n d : Nat) : Cert (n+1) :=
  (List.range n).foldl
    (fun acc i => if i = 0 then .step (sTy n d 0) (sTy n d 1)
                  else .seq acc (.step (sTy n d i) (sTy n d (i+1))))
    (.step (sTy n d 0) (sTy n d 0))

theorem sOk : ∀ n ∈ [1,2,3,4], ∀ d ∈ [0,1,2,3],
    synthC (chainCtx n) (sCertR n d) = some (sTy n d 0, sTy n d n) ∧
    synthC (chainCtx n) (sCertL n d) = some (sTy n d 0, sTy n d n) := by decide

/-- (steps, stored type nodes, refl steps): no DAG count, which is slow in the kernel. -/
def lite (c : Cert n) : List Nat := [Sel.steps c, Sel.stored c, Sel.refls c]
def invRow (c : Cert (n+1)) : List Nat × List Nat := (lite c.allInv.1, lite c.allInv.2)


-- (n, d, hand size [steps, stored], allInv.1 [steps], allInv.2 [steps, stored, refl, dag]) for n = 1..8, d ∈ {0,2,4,8}
def stressRows : List (Nat × Nat × List Nat × (List Nat × List Nat) × List Nat × (List Nat × List Nat)) := [
  (1, 0, lite (sCertR 1 0), invRow (sCertR 1 0), lite (sCertL 1 0), invRow (sCertL 1 0)),
  (1, 2, lite (sCertR 1 2), invRow (sCertR 1 2), lite (sCertL 1 2), invRow (sCertL 1 2)),
  (1, 4, lite (sCertR 1 4), invRow (sCertR 1 4), lite (sCertL 1 4), invRow (sCertL 1 4)),
  (1, 8, lite (sCertR 1 8), invRow (sCertR 1 8), lite (sCertL 1 8), invRow (sCertL 1 8)),
  (2, 0, lite (sCertR 2 0), invRow (sCertR 2 0), lite (sCertL 2 0), invRow (sCertL 2 0)),
  (2, 2, lite (sCertR 2 2), invRow (sCertR 2 2), lite (sCertL 2 2), invRow (sCertL 2 2)),
  (2, 4, lite (sCertR 2 4), invRow (sCertR 2 4), lite (sCertL 2 4), invRow (sCertL 2 4)),
  (2, 8, lite (sCertR 2 8), invRow (sCertR 2 8), lite (sCertL 2 8), invRow (sCertL 2 8)),
  (3, 0, lite (sCertR 3 0), invRow (sCertR 3 0), lite (sCertL 3 0), invRow (sCertL 3 0)),
  (3, 2, lite (sCertR 3 2), invRow (sCertR 3 2), lite (sCertL 3 2), invRow (sCertL 3 2)),
  (3, 4, lite (sCertR 3 4), invRow (sCertR 3 4), lite (sCertL 3 4), invRow (sCertL 3 4)),
  (3, 8, lite (sCertR 3 8), invRow (sCertR 3 8), lite (sCertL 3 8), invRow (sCertL 3 8)),
  (4, 0, lite (sCertR 4 0), invRow (sCertR 4 0), lite (sCertL 4 0), invRow (sCertL 4 0)),
  (4, 2, lite (sCertR 4 2), invRow (sCertR 4 2), lite (sCertL 4 2), invRow (sCertL 4 2)),
  (4, 4, lite (sCertR 4 4), invRow (sCertR 4 4), lite (sCertL 4 4), invRow (sCertL 4 4)),
  (4, 8, lite (sCertR 4 8), invRow (sCertR 4 8), lite (sCertL 4 8), invRow (sCertL 4 8)),
  (5, 0, lite (sCertR 5 0), invRow (sCertR 5 0), lite (sCertL 5 0), invRow (sCertL 5 0)),
  (5, 2, lite (sCertR 5 2), invRow (sCertR 5 2), lite (sCertL 5 2), invRow (sCertL 5 2)),
  (5, 4, lite (sCertR 5 4), invRow (sCertR 5 4), lite (sCertL 5 4), invRow (sCertL 5 4)),
  (5, 8, lite (sCertR 5 8), invRow (sCertR 5 8), lite (sCertL 5 8), invRow (sCertL 5 8)),
  (6, 0, lite (sCertR 6 0), invRow (sCertR 6 0), lite (sCertL 6 0), invRow (sCertL 6 0)),
  (6, 2, lite (sCertR 6 2), invRow (sCertR 6 2), lite (sCertL 6 2), invRow (sCertL 6 2)),
  (6, 4, lite (sCertR 6 4), invRow (sCertR 6 4), lite (sCertL 6 4), invRow (sCertL 6 4)),
  (6, 8, lite (sCertR 6 8), invRow (sCertR 6 8), lite (sCertL 6 8), invRow (sCertL 6 8)),
  (7, 0, lite (sCertR 7 0), invRow (sCertR 7 0), lite (sCertL 7 0), invRow (sCertL 7 0)),
  (7, 2, lite (sCertR 7 2), invRow (sCertR 7 2), lite (sCertL 7 2), invRow (sCertL 7 2)),
  (7, 4, lite (sCertR 7 4), invRow (sCertR 7 4), lite (sCertL 7 4), invRow (sCertL 7 4)),
  (7, 8, lite (sCertR 7 8), invRow (sCertR 7 8), lite (sCertL 7 8), invRow (sCertL 7 8)),
  (8, 0, lite (sCertR 8 0), invRow (sCertR 8 0), lite (sCertL 8 0), invRow (sCertL 8 0)),
  (8, 2, lite (sCertR 8 2), invRow (sCertR 8 2), lite (sCertL 8 2), invRow (sCertL 8 2)),
  (8, 4, lite (sCertR 8 4), invRow (sCertR 8 4), lite (sCertL 8 4), invRow (sCertL 8 4)),
  (8, 8, lite (sCertR 8 8), invRow (sCertR 8 8), lite (sCertL 8 8), invRow (sCertL 8 8))]
/-- Flattened: `[n, d] ++ hand row ++ allInv bound row ++ allInv body row` for the right-nested
hand certificate, then the same three for the left-nested one. -/
def stressFlat : List (List Nat) := stressRows.map fun (n, d, r1, (b1, c1), r2, (b2, c2)) =>
  [n, d] ++ r1 ++ b1 ++ c1 ++ r2 ++ b2 ++ c2
#eval stressFlat

end Compare.Depth
