import Coercions.Selective.FsubCompare.Translate
/-!
# Size measures

SelFsub side: nodes of stored certificates, stored type nodes, distinct subterms.
FCsub side: counters over `LeCo` mirroring the case split of `FCsub.checkLeCore`
(`lean/Coercions/FCsub/Checker.lean:86-146`), `checkArgsCore` (148-168) and
`checkMorCore` (170-192). The counters are structural functions on the evidence, not a
re-implementation of the checker; the checker itself is run by `synthLe`.
-/
namespace Compare

/-! ## SelFsub -/
namespace Sel
open SelFsub

def tyNodes : Ty n → Nat
  | .top => 1
  | .var _ => 1
  | .arr A B => 1 + tyNodes A + tyNodes B
  | .all A B => 1 + tyNodes A + tyNodes B

/-- Steps of a certificate (`prim?` calls made by `Cert.valid`). -/
def steps : Cert n → Nat
  | .step _ _ => 1
  | .seq c d => steps c + steps d

/-- `;` nodes (endpoint equality tests made by `Cert.valid`). -/
def seqs : Cert n → Nat
  | .step _ _ => 0
  | .seq c d => 1 + seqs c + seqs d

/-- Type nodes stored in the steps (both endpoints of every step). -/
def stored : Cert n → Nat
  | .step S T => tyNodes S + tyNodes T
  | .seq c d => stored c + stored d

/-- Reflexive steps `step[S, S]` (padding). -/
def refls : Cert n → Nat
  | .step S T => if S = T then 1 else 0
  | .seq c d => refls c + refls d

def subterms : Cert n → List (Cert n)
  | c@(.step _ _) => [c]
  | c@(.seq a b) => c :: (subterms a ++ subterms b)

/-- Distinct subterms of the certificate (DAG size of the certificate tree). -/
def dag (c : Cert n) : Nat := (subterms c).eraseDups.length

/-- Distinct stored endpoint types (as whole types) of the steps. -/
def endpoints : Cert n → List (Ty n)
  | .step S T => [S, T]
  | .seq c d => endpoints c ++ endpoints d
def distinctEndpoints (c : Cert n) : Nat := (endpoints c).eraseDups.length

/-- The measure row: (steps, seqs, nodes, stored type nodes, refl steps, dag, distinct endpoints). -/
def row (c : Cert n) : List Nat :=
  [steps c, seqs c, steps c + seqs c, stored c, refls c, dag c, distinctEndpoints c]

end Sel

/-! ## FCsub -/
namespace Fc
open FCsub

mutual
def tyN : Ty s → Nat
  | .top => 1 | .bot => 1 | .one => 1 | .tvar _ => 1
  | .arr d c => 1 + tyN d + tyN c
  | .existsT t p => 1 + telN t + tyN p
  | .forallT t b => 1 + telN t + tyN b
  | .recProj _ _ => 1
def telN : Telescope s n m → Nat
  | .nil => 0
  | .snoc t (.inclusion a b) => telN t + tyN a + tyN b
end

def argsN : TypeArgs s n → Nat
  | .nil => 0
  | .snoc t a => argsN t + tyN a

/-- Counters: LeCo nodes, evidence variables, `trans` nodes, other nodes, TelMor nodes,
stored type nodes, middle-equality tests of the checker. -/
structure C where
  le : Nat := 0       -- every LeCo node (one `checkLeCore` call each)
  vars : Nat := 0    -- `var` nodes (one `Ctx.lookup` each)
  trans : Nat := 0   -- `LeCo.trans` nodes
  refl : Nat := 0    -- `LeCo.refl` nodes
  mor : Nat := 0     -- TelMor nodes (one `checkMorCore` call each)
  tys : Nat := 0     -- Ty nodes stored inside the evidence
  eqs : Nat := 0     -- equality tests between synthesised and stored/expected types
  deriving Repr

instance : Add C := ⟨fun a b => ⟨a.le+b.le, a.vars+b.vars, a.trans+b.trans, a.refl+b.refl, a.mor+b.mor, a.tys+b.tys, a.eqs+b.eqs⟩⟩

mutual
def cnt : LeCo s → C
  | .var _ => { le := 1, vars := 1 }
  | .refl t => { le := 1, refl := 1, tys := tyN t }
  | .trans a b => { le := 1, trans := 1, eqs := 1 } + cnt a + cnt b
  | .top t => { le := 1, tys := tyN t }
  | .bot t => { le := 1, tys := tyN t }
  | .eqToLe _ => { le := 1 }
  | .arr d c => { le := 1 } + cnt d + cnt c
  | .existsT m sp tp p => { le := 1, tys := tyN sp + tyN tp, eqs := 2 } + cntM m + cnt p
  | .forallT m sb tb b => { le := 1, tys := tyN sb + tyN tb, eqs := 2 } + cntM m + cnt b
def cntA : LeArgs s n → C
  | .nil => {}
  | .snoc t e => { eqs := 2 } + cntA t + cnt e   -- source and target against `instantiateNames`
def cntM : TelMor s a b c d → C
  | .refl t => { mor := 1, tys := telN t }
  | .map src tgt names ev =>
      { mor := 1, tys := telN src + telN tgt + argsN names } + cntA ev
  | .trans a b => { mor := 1, eqs := 1 } + cntM a + cntM b
end

/-- The row: nodes, vars, trans, refl, TelMor nodes, stored type nodes, equality tests. -/
def row (c : C) : List Nat := [c.le, c.vars, c.trans, c.refl, c.mor, c.tys, c.eqs]

def subterms : LeCo s → List (LeCo s)
  | e@(.trans a b) => e :: (subterms a ++ subterms b)
  | e => [e]
def dag (e : LeCo s) : Nat := (subterms e).eraseDups.length

end Fc
end Compare
