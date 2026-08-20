import LambdaPFCI.Runtime

/-!
The append-only store orders locations by allocation time.  This order is
used to justify semantic interpretation of a dependent pair member at the
older locations stored in the pair value.
-/

namespace LambdaPFCI

/-- Remaining allocation depth of a runtime referent.  Stored type
definitions have no value-location depth. -/
def Path.Referent.stratum {n : Nat} : Path.Referent n -> Nat
| .loc x => n - x.val
| .type _ => 0

@[simp] theorem Path.Referent.stratum_weaken
    (referent : Path.Referent n) :
    referent.weaken.stratum = referent.stratum := by
  cases referent with
  | loc x =>
      simp only [Path.Referent.weaken, Path.Referent.stratum, Fin.val_succ]
      omega
  | type T => rfl

@[simp] theorem Path.Referent.stratum_loc_succ (x : Fin n) :
    (Path.Referent.loc x.succ : Path.Referent (n + 1)).stratum =
      (Path.Referent.loc x : Path.Referent n).stratum := by
  simp only [Path.Referent.stratum, Fin.val_succ]
  omega

/-- A definition stored in a fresh cell has lower stratum than that cell. -/
theorem Def.referent_weaken_stratum_lt (d : Def n k) :
    d.referent.weaken.stratum <
      (Path.Referent.loc (0 : Fin (n + 1))).stratum := by
  cases d with
  | val x =>
      simp only [Def.referent, Path.Referent.weaken,
        Path.Referent.stratum, Fin.val_succ, Fin.val_zero]
      omega
  | type T =>
      simp [Def.referent, Path.Referent.weaken, Path.Referent.stratum]

/-- Both referents mentioned by a stored pair are older than the pair cell:
its first component and the referent of its member definition. -/
private theorem Store.Binds.pair_strata_lt_aux
    (binding : Store.Binds sigma x term)
    (equation : term = .pair y a d) :
    (Path.Referent.loc y).stratum < (Path.Referent.loc x).stratum /\
      d.referent.stratum < (Path.Referent.loc x).stratum := by
  induction binding with
  | @here n sigma value isValue =>
      cases value <;> try { cases equation }
      case pair memberKind first label definition =>
        cases equation
        refine ⟨?_, ?_⟩
        · rw [FinFun.weaken_apply, Path.Referent.stratum_loc_succ]
          simpa only [Path.Referent.stratum, Fin.val_zero] using
            Nat.lt_succ_of_le (Nat.sub_le n label.val)
        · simpa only [Def.referent_weaken] using
            Def.referent_weaken_stratum_lt definition
  | @there n sigma x value older fresh freshValue ih =>
      cases value <;> try { cases equation }
      case pair memberKind first label definition =>
        cases equation
        obtain ⟨firstLt, memberLt⟩ := ih rfl
        refine ⟨?_, ?_⟩
        · simpa only [FinFun.weaken_apply,
            Path.Referent.stratum_loc_succ] using firstLt
        · simpa only [Def.referent_weaken,
            Path.Referent.stratum_weaken,
            Path.Referent.stratum_loc_succ] using memberLt

theorem Store.Binds.pair_first_stratum_lt
    (binding : Store.Binds sigma x (.pair y a d)) :
    (Path.Referent.loc y).stratum <
      (Path.Referent.loc x).stratum :=
  (binding.pair_strata_lt_aux rfl).1

theorem Store.Binds.pair_referent_stratum_lt
    (binding : Store.Binds sigma x (.pair y a d)) :
    d.referent.stratum < (Path.Referent.loc x).stratum :=
  (binding.pair_strata_lt_aux rfl).2

end LambdaPFCI
