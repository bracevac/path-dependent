import LambdaPFC.Runtime

/-!
The append-only store orders locations by allocation time.  This order is
used to justify semantic interpretation of a dependent pair member at the
older locations stored in the pair value.
-/

namespace LambdaPFC

/-- Remaining allocation depth of a runtime endpoint.  Stored type
definitions have no value-location depth. -/
def Path.Endpoint.stratum {n : Nat} : Path.Endpoint n -> Nat
| .val x => n - x.val
| .type _ => 0

@[simp] theorem Path.Endpoint.stratum_weaken
    (endpoint : Path.Endpoint n) :
    endpoint.weaken.stratum = endpoint.stratum := by
  cases endpoint with
  | val x =>
      simp only [Path.Endpoint.weaken, Path.Endpoint.stratum, Fin.val_succ]
      omega
  | type T => rfl

@[simp] theorem Path.Endpoint.stratum_val_succ (x : Fin n) :
    (Path.Endpoint.val x.succ : Path.Endpoint (n + 1)).stratum =
      (Path.Endpoint.val x : Path.Endpoint n).stratum := by
  simp only [Path.Endpoint.stratum, Fin.val_succ]
  omega

@[simp] theorem Def.endpoint_rename_weaken (d : Def n k) :
    (d.rename FinFun.weaken).endpoint = d.endpoint.weaken := by
  cases d <;> rfl

/-- A definition stored in a fresh cell has lower stratum than that cell. -/
theorem Def.endpoint_weaken_stratum_lt (d : Def n k) :
    d.endpoint.weaken.stratum <
      (Path.Endpoint.val (0 : Fin (n + 1))).stratum := by
  cases d with
  | val x =>
      simp only [Def.endpoint, Path.Endpoint.weaken,
        Path.Endpoint.stratum, Fin.val_succ, Fin.val_zero]
      omega
  | type T =>
      simp [Def.endpoint, Path.Endpoint.weaken, Path.Endpoint.stratum]

/-- Every endpoint mentioned by a stored pair is older than the pair cell. -/
private theorem Store.Binds.pair_endpoint_stratum_lt_aux
    (binding : Store.Binds sigma x term)
    (equation : term = .pair y a d) :
    d.endpoint.stratum < (Path.Endpoint.val x).stratum := by
  induction binding with
  | @here n sigma value isValue =>
      cases value <;> try { cases equation }
      case pair first label definition =>
        cases equation
        simpa only [Def.endpoint_rename_weaken] using
          Def.endpoint_weaken_stratum_lt definition
  | @there n sigma x value older fresh freshValue ih =>
      cases value <;> try { cases equation }
      case pair first label definition =>
        cases equation
        simpa only [Def.endpoint_rename_weaken,
          Path.Endpoint.stratum_weaken,
          Path.Endpoint.stratum_val_succ] using ih rfl

theorem Store.Binds.pair_endpoint_stratum_lt
    (binding : Store.Binds sigma x (.pair y a d)) :
    d.endpoint.stratum < (Path.Endpoint.val x).stratum :=
  binding.pair_endpoint_stratum_lt_aux rfl

private def Tm.pairFirst? : Tm n -> Option (Fin n)
| .pair y _ _ => some y
| _ => none

@[simp] private theorem Tm.pairFirst?_weaken (term : Tm n) :
    term.weaken.pairFirst? = term.pairFirst?.map Fin.succ := by
  cases term <;> rfl

private theorem Store.Binds.pair_first_stratum_lt_aux
    (binding : Store.Binds sigma x term)
    (equation : term.pairFirst? = some y) :
    (Path.Endpoint.val y).stratum <
      (Path.Endpoint.val x).stratum := by
  induction binding with
  | @here n sigma value isValue =>
      rw [Tm.pairFirst?_weaken] at equation
      cases hfirst : value.pairFirst? with
      | none => simp [hfirst] at equation
      | some first =>
          simp only [hfirst, Option.map_some, Option.some.injEq] at equation
          subst y
          rw [Path.Endpoint.stratum_val_succ]
          simpa only [Path.Endpoint.stratum, Fin.val_zero] using
            Nat.lt_succ_of_le (Nat.sub_le n first.val)
  | @there n sigma x value fresh freshValue older ih =>
      rw [Tm.pairFirst?_weaken] at equation
      cases hfirst : value.pairFirst? with
      | none => simp [hfirst] at equation
      | some first =>
          simp only [hfirst, Option.map_some, Option.some.injEq] at equation
          subst y
          simpa only [Path.Endpoint.stratum_val_succ] using ih hfirst

theorem Store.Binds.pair_first_stratum_lt
    (binding : Store.Binds sigma x (.pair y a d)) :
    (Path.Endpoint.val y).stratum <
      (Path.Endpoint.val x).stratum :=
  binding.pair_first_stratum_lt_aux rfl

end LambdaPFC
