import LambdaPFC.Typing

namespace LambdaPToFCo.Full

open LambdaPFC

/-- Precise typing assigns one kind and one generalized result to a fixed
context/path. `HEq` states both kind and result uniqueness at once. -/
def PathTyping.result_heq :
    {n : Nat} -> {context : Ctx n} -> {path : Path n} ->
    {firstKind secondKind : Kind} ->
    {first : Tau n firstKind} -> {second : Tau n secondKind} ->
    Path.Ty context path first -> Path.Ty context path second ->
    HEq first second
  | _, _, _, _, _, _, _, .var, .var => HEq.rfl
  | _, _, _, _, _, _, _, .fst first, .fst second => by
      have receiver := result_heq first second
      cases receiver
      exact HEq.rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_r second => by
      have receiver := result_heq first second
      cases receiver
      exact HEq.rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_l second _ labelsNe => by
      have receiver := result_heq first second
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l first _ labelsNe, .sel_r second => by
      have receiver := result_heq first second
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l _ first _, .sel_l _ second _ =>
      result_heq first second

/-- The result kind of precise path typing is unique. -/
def PathTyping.kind_eq :
    {n : Nat} -> {context : Ctx n} -> {path : Path n} ->
    {firstKind secondKind : Kind} ->
    {first : Tau n firstKind} -> {second : Tau n secondKind} ->
    Path.Ty context path first -> Path.Ty context path second ->
    firstKind = secondKind
  | _, _, _, _, _, _, _, .var, .var => rfl
  | _, _, _, _, _, _, _, .fst _, .fst _ => rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_r second => by
      have receiver := eq_of_heq (result_heq first second)
      cases receiver
      rfl
  | _, _, _, _, _, _, _, .sel_r first, .sel_l second _ labelsNe => by
      have receiver := eq_of_heq (result_heq first second)
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l first _ labelsNe, .sel_r second => by
      have receiver := eq_of_heq (result_heq first second)
      cases receiver
      exact (labelsNe rfl).elim
  | _, _, _, _, _, _, _, .sel_l _ first _, .sel_l _ second _ =>
      kind_eq first second

/-- Homogeneous result uniqueness, convenient after the kind has been fixed. -/
theorem PathTyping.result_eq
    {n : Nat} {context : Ctx n} {path : Path n} {kind : Kind}
    {firstResult secondResult : Tau n kind}
    (first : Path.Ty context path firstResult)
    (second : Path.Ty context path secondResult) :
    firstResult = secondResult := by
  exact eq_of_heq (result_heq first second)

end LambdaPToFCo.Full
