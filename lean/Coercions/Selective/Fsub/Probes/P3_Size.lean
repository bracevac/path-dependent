import Coercions.Selective.Fsub
/-!
# Probe P3: size of the certificate operations

`nsteps` counts `step` leaves, `tsize` the type nodes stored in them.
-/
namespace SelFsub


def Ty.size : Ty n → Nat
  | .top => 1
  | .var _ => 1
  | .arr A B => A.size + B.size + 1
  | .all A B => A.size + B.size + 1

def Cert.nsteps : Cert n → Nat
  | .step _ _ => 1
  | .seq c d => c.nsteps + d.nsteps

def Cert.tsize : Cert n → Nat
  | .step S T => Ty.size S + Ty.size T
  | .seq c d => c.tsize + d.tsize

/-! ## E1: narrowing a variable that does not occur expands a single structural step

`W <: Top, X <: Top` (`X = var 0`, `W = var 1`); the step
`Top → … → Top → W ≤₀ Top → … → Top → Top` (`m` arrows) does not mention `X`. Narrowing
`X <: Top` to `X <: W` along `step[W, Top]` should leave it alone. -/

def arrN : Nat → Ty n → Ty n
  | 0, A => A
  | m+1, A => .arr .top (arrN m A)

def ctxW : Ctx 1 := .snoc .nil .top
def e1 (m : Nat) : Cert 2 := .step (arrN m (.var 1)) (arrN m .top)
def dW : Cert 1 := .step (.var 0) .top

theorem e1_typed : CTy (ctxW.snoc .top) (e1 4) (arrN 4 (.var 1)) (arrN 4 .top) := by decide
theorem e1_narrow_typed :
    CTy (ctxW.snoc (.var 0)) ((e1 4).narrow 0 dW) (arrN 4 (.var 1)) (arrN 4 .top) := by decide
/-- One step of 18 type nodes becomes five steps of 90 type nodes. -/
theorem e1_narrow_size :
    ((e1 4).nsteps, (e1 4).tsize, ((e1 4).narrow 0 dW).nsteps, ((e1 4).narrow 0 dW).tsize) =
      (1, 18, 5, 90) := by decide
/-- The same with every entry `none` and the identity substitution. -/
theorem e1_id_size : (((e1 4).subst .var (fun _ => none)).nsteps) = 5 := by decide

/-!  Each row: `m`, input typed, output typed (by the verified checker `checkC`), input type
nodes, output steps, output type nodes. -/
#eval (List.range 9).map fun k => let m := 4 * k
  (m, checkC (ctxW.snoc .top) (e1 m) (arrN m (.var 1)) (arrN m .top),
     checkC (ctxW.snoc (.var 0)) ((e1 m).narrow 0 dW) (arrN m (.var 1)) (arrN m .top),
     (e1 m).tsize, ((e1 m).narrow 0 dW).nsteps, ((e1 m).narrow 0 dW).tsize)

/-- Iterated narrowing (`k` passes) of the same step. The output never mentions `X`, so each
pass is applied to a certificate typed under the pass's premise `X <: Top` (checked in the row). -/
def iterNarrow : Nat → Cert 2 → Cert 2
  | 0, c => c
  | k+1, c => iterNarrow k (c.narrow 0 dW)

theorem iterNarrow_typed :
    CTy (ctxW.snoc .top) (iterNarrow 2 (e1 3)) (arrN 3 (.var 1)) (arrN 3 .top) ∧
    CTy (ctxW.snoc (.var 0)) ((iterNarrow 2 (e1 3)).narrow 0 dW) (arrN 3 (.var 1)) (arrN 3 .top) ∧
    ((iterNarrow 2 (e1 3)).narrow 0 dW).nsteps = 10 := by decide

#eval (List.range 6).map fun k =>
  (k, checkC (ctxW.snoc .top) (iterNarrow k (e1 8)) (arrN 8 (.var 1)) (arrN 8 .top),
      checkC (ctxW.snoc (.var 0)) (iterNarrow (k+1) (e1 8)) (arrN 8 (.var 1)) (arrN 8 .top),
      (iterNarrow (k+1) (e1 8)).nsteps, (iterNarrow (k+1) (e1 8)).tsize)

/-! ## E2: inversion of a chain of `N+1` universal steps, left versus right association

`Y₀ <: Top, Y₁ <: Y₀, …, Y_N <: Y_{N-1}`, bounds `Aᵢ = Top → Yᵢ`. Links
`L₀ = step[∀(X <: A₀). X, ∀(X <: A₀). A₀]` (a bound step on `X` in the body) and
`Lᵢ = step[∀(X <: A_{i-1}). A₀, ∀(X <: Aᵢ). A₀]` (a structural bound step `Aᵢ ≤₀ A_{i-1}`). -/

def ctxY : (N : Nat) → Ctx (N+1)
  | 0 => .snoc .nil .top
  | N+1 => .snoc (ctxY N) (.var 0)

def yv (N i : Nat) : Ty (N+1) := .var ⟨(N - i) % (N+1), Nat.mod_lt _ (Nat.succ_pos N)⟩
def bA (N i : Nat) : Ty (N+1) := .arr .top (yv N i)

def link0 (N : Nat) : Cert (N+1) := .step (.all (bA N 0) (.var 0)) (.all (bA N 0) (bA N 0).weaken)
def linkI (N i : Nat) : Cert (N+1) :=
  .step (.all (bA N (i-1)) (bA N 0).weaken) (.all (bA N i) (bA N 0).weaken)

def chainLeft (N : Nat) : Cert (N+1) :=
  (List.range N).foldl (fun c i => .seq c (linkI N (i+1))) (link0 N)
def chainRight (N : Nat) : Cert (N+1) :=
  .seq (link0 N) ((List.range (N-1)).foldr (fun i c => .seq (linkI N (i+1)) c) (linkI N N))

theorem chains_typed :
    CTy (ctxY 3) (chainLeft 3) (.all (bA 3 0) (.var 0)) (.all (bA 3 3) (bA 3 0).weaken) ∧
    CTy (ctxY 3) (chainRight 3) (.all (bA 3 0) (.var 0)) (.all (bA 3 3) (bA 3 0).weaken) := by
  decide
theorem allInv_bodies_typed :
    CTy ((ctxY 3).snoc (bA 3 3)) (chainLeft 3).allInv.2 (.var 0) (bA 3 0).weaken ∧
    CTy ((ctxY 3).snoc (bA 3 3)) (chainRight 3).allInv.2 (.var 0) (bA 3 0).weaken := by decide
/-- Left: `(N+1)(N+2)/2` body steps; right: `2N+1`. -/
theorem allInv_sizes_3 :
    ((chainLeft 3).allInv.2.nsteps, (chainRight 3).allInv.2.nsteps) = (10, 7) := by decide
theorem allInv_sizes_10 :
    ((chainLeft 10).allInv.2.nsteps, (chainRight 10).allInv.2.nsteps) = (66, 21) := by decide +kernel
theorem allInv_bodies_typed_6 :
    CTy ((ctxY 6).snoc (bA 6 6)) (chainLeft 6).allInv.2 (.var 0) (bA 6 0).weaken := by decide

/-- The `N = 31` instance, typed by the kernel (lazy evaluation avoids the `Fin.cases` cost, E4). -/
theorem chain31_typed :
    CTy (ctxY 31) (chainLeft 31) (.all (bA 31 0) (.var 0)) (.all (bA 31 31) (bA 31 0).weaken) ∧
    CTy (ctxY 31) (chainRight 31) (.all (bA 31 0) (.var 0)) (.all (bA 31 31) (bA 31 0).weaken) ∧
    CTy ((ctxY 31).snoc (bA 31 31)) (chainLeft 31).allInv.2 (.var 0) (bA 31 0).weaken ∧
    CTy ((ctxY 31).snoc (bA 31 31)) (chainRight 31).allInv.2 (.var 0) (bA 31 0).weaken ∧
    ((chainLeft 31).allInv.2.nsteps, (chainRight 31).allInv.2.nsteps) = (528, 63) := by
  decide +kernel

/-!  Sizes at `N = 21, 26, 31` (typing kernel-checked for `N = 31` by `chain31_typed`). -/
#eval [21, 26, 31].map fun N =>
  (N, (chainLeft N).allInv.2.nsteps, (chainRight N).allInv.2.nsteps,
     (chainLeft N).allInv.2.tsize, (chainRight N).allInv.2.tsize)

/-!  Each row: `N`, both chains typed, both bodies typed (`checkC`), left body steps, right body
steps, left body type nodes, right body type nodes, bound composite steps. -/
#eval (List.range 6).map fun k => let N := 3 * k + 1
  (N, checkC (ctxY N) (chainLeft N) (.all (bA N 0) (.var 0)) (.all (bA N N) (bA N 0).weaken) &&
      checkC (ctxY N) (chainRight N) (.all (bA N 0) (.var 0)) (.all (bA N N) (bA N 0).weaken),
     checkC ((ctxY N).snoc (bA N N)) (chainLeft N).allInv.2 (.var 0) (bA N 0).weaken &&
      checkC ((ctxY N).snoc (bA N N)) (chainRight N).allInv.2 (.var 0) (bA N 0).weaken,
     (chainLeft N).allInv.2.nsteps, (chainRight N).allInv.2.nsteps,
     (chainLeft N).allInv.2.tsize, (chainRight N).allInv.2.tsize,
     (chainLeft N).allInv.1.nsteps)

/-! ## E3: narrowing and instantiation of a chain of `N+1` bound steps through the variable

`Γ = ctxY (N+1)` (`Y_{N+1} = var 0`, `Y_N = var 1`, `Y₀ = var (N+1)`), binder `X <: Y_N` on top:
`X = var 0`, `Y_j = var (N+2-j)`. The certificate is `X ⇒ Y_N ⇒ … ⇒ Y₀`; `X <: Y_N` is narrowed
to `X <: Y_{N+1}`, or `X` instantiated with `Y_{N+1}`, along `d = step[Y_{N+1}, Y_N]`. -/

def ctxE3 (N : Nat) : Ctx (N+3) := (ctxY (N+1)).snoc (.var 1)
def vE3 (N k : Nat) : Ty (N+3) := .var ⟨k % (N+3), Nat.mod_lt _ (by omega)⟩
def boundChain (N : Nat) : Cert (N+3) :=
  (List.range N).foldl (fun c i => .seq c (.step (vE3 N (i+2)) (vE3 N (i+3)))) (.step (.var 0) (.var 2))
def dE3 (N : Nat) : Cert (N+2) := .step (.var 0) (.var 1)
def top2 (N : Nat) : Ty (N+2) := .var ⟨N+1, by omega⟩

theorem boundChain_typed_3 :
    CTy (ctxE3 3) (boundChain 3) (.var 0) (vE3 3 5) ∧
    CTy (ctxY 4) (dE3 3) (.var 0) (.var 1) ∧
    CTy ((ctxY 4).snoc (.var 0)) ((boundChain 3).narrow 0 (dE3 3)) (.var 0) (vE3 3 5) ∧
    CTy (ctxY 4) ((boundChain 3).inst 0 (.var 0) (dE3 3)) (.var 0) (top2 3) := by decide
theorem boundChain_sizes_3 :
    ((boundChain 3).nsteps, ((boundChain 3).narrow 0 (dE3 3)).nsteps,
      ((boundChain 3).inst 0 (.var 0) (dE3 3)).nsteps) = (4, 5, 4) := by decide

/-!  Each row: `N`, input typed, narrowed typed, instantiated typed (`checkC`), input steps,
narrowed steps, instantiated steps. -/
#eval (List.range 5).map fun k => let N := 3 * k
  (N, checkC (ctxE3 N) (boundChain N) (.var 0) (vE3 N (N+2)),
     checkC ((ctxY (N+1)).snoc (.var 0)) ((boundChain N).narrow 0 (dE3 N)) (.var 0) (vE3 N (N+2)),
     checkC (ctxY (N+1)) ((boundChain N).inst 0 (.var 0) (dE3 N)) (.var 0) (top2 N),
     (boundChain N).nsteps, ((boundChain N).narrow 0 (dE3 N)).nsteps,
     ((boundChain N).inst 0 (.var 0) (dE3 N)).nsteps)

#print axioms e1_narrow_typed
#print axioms e1_narrow_size
#print axioms iterNarrow_typed
#print axioms chains_typed
#print axioms allInv_bodies_typed
#print axioms allInv_sizes_3
#print axioms allInv_sizes_10
#print axioms allInv_bodies_typed_6
#print axioms boundChain_typed_3
#print axioms boundChain_sizes_3

/-! ## E4: compiled evaluation of `Ctx.lookup` is exponential in the de Bruijn index

`Ctx.lookup` uses `Fin.cases`, which core defines through `Fin.induction`; compiled code
evaluates the unused induction hypothesis, so looking up index `k` evaluates the lookups of all
smaller indices one level down. The kernel (`decide`) is not affected. `lk` is the same
function by pattern matching. -/

def lk : Ctx n → Fin n → Ty n
  | .nil, x => Fin.elim0 x
  | .snoc _ A, ⟨0, _⟩ => A.weaken
  | .snoc Γ _, ⟨i+1, h⟩ => (lk Γ ⟨i, by omega⟩).weaken

theorem lk_eq : ∀ (Γ : Ctx n) (x : Fin n), lk Γ x = Γ.lookup x
  | .nil, x => x.elim0
  | .snoc _ _, ⟨0, _⟩ => rfl
  | .snoc Γ _, ⟨i+1, h⟩ => by rw [lk, lk_eq Γ]; rfl

/-! Timing (shell, `lake env lean` on a file with the single command
`#eval decide ((ctxY N).lookup ⟨N, by omega⟩ = .top)`, whole process): N = 18: 0.33 s,
N = 20: 0.68 s, N = 22: 2.09 s; with `lk` in place of `Ctx.lookup`: N = 22: 0.21 s,
N = 200: 0.21 s (the import alone takes about 0.2 s). -/

#print axioms lk_eq
#print axioms chain31_typed

end SelFsub

