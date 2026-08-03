import LambdaPFC.SemanticEvidence

/-!
Store-local typing evidence for runtime terms and machine configurations.

Subsumption is normalized into a final semantic coercion at each surface
constructor.  Consequently, inversion follows the runtime syntax directly;
there is no separate structural typing relation and no coercion term in the
surface language.
-/

namespace LambdaPFC

noncomputable section

/-! ## Values and terms -/

/-- Typing evidence for a syntactic value.  Each constructor records its
syntax-directed introduction data and a coercion to the advertised type. -/
inductive ValueEvidence :
    {n : Nat} -> Store n -> Tm n -> Ty n -> Type 1 where
| abs {n : Nat} {sigma : Store n} {A T : Ty n}
    {body : Tm (n + 1)} {B : Ty (n + 1)} :
    BodyClosure sigma A body B ->
    Coercion sigma (.ty (.Fun A B)) (.ty T) ->
    ValueEvidence sigma (.abs A body) T
| pair {n : Nat} {sigma : Store n} {y z : Fin n}
    {a : Name} {T : Ty n} :
    Coercion sigma
      (.ty (.Pair (.Single (Path.var y)) a
        (Tau.ty (.Single (Path.var z).weaken))))
      (.ty T) ->
    ValueEvidence sigma (.pair y a (.val z)) T
| tpair {n : Nat} {sigma : Store n} {y : Fin n}
    {A : Name} {W T : Ty n} :
    Coercion sigma
      (.ty (.Pair (.Single (Path.var y)) A (Tau.intv W W).weaken))
      (.ty T) ->
    ValueEvidence sigma (.pair y A (.type W)) T

/-- Runtime typing evidence, normalized by the outer term constructor. -/
inductive TermEvidence :
    {n : Nat} -> Store n -> Tm n -> Ty n -> Type 1 where
| path {n : Nat} {sigma : Store n} {p : Path n}
    {x : Fin n} {T : Ty n} :
    Path.Resolve p sigma (.loc x) ->
    Coercion sigma (.ty (.Single p)) (.ty T) ->
    TermEvidence sigma (.path p) T
| value {n : Nat} {sigma : Store n} {v : Tm n} {T : Ty n} :
    ValueEvidence sigma v T ->
    TermEvidence sigma v T
| app {n : Nat} {sigma : Store n} {p q : Path n}
    {S T : Ty n} {U : Ty (n + 1)} :
    TermEvidence sigma (.path p) (.Fun S U) ->
    TermEvidence sigma (.path q) S ->
    Coercion sigma (.ty (U.open q)) (.ty T) ->
    TermEvidence sigma (.app p q) T
| «let» {n : Nat} {sigma : Store n} {s : Tm n}
    {body : Tm (n + 1)} {S T U : Ty n} :
    TermEvidence sigma s S ->
    BodyClosure sigma S body U.weaken ->
    Coercion sigma (.ty U) (.ty T) ->
    TermEvidence sigma (.let s body) T

/-- A value-evidence derivation supplies the runtime value classifier. -/
def ValueEvidence.isValue : ValueEvidence sigma v T -> v.IsValue
| .abs _ _ => .abs
| .pair _ => .pair
| .tpair _ => .pair

/-- Compose a further coercion with the suffix already stored by a value. -/
def ValueEvidence.cast
    (evidence : ValueEvidence sigma v S)
    (suffix : Coercion sigma (.ty S) (.ty T)) :
    ValueEvidence sigma v T :=
  match evidence with
  | .abs body old => .abs body (old.comp suffix)
  | .pair old => .pair (old.comp suffix)
  | .tpair old => .tpair (old.comp suffix)

/-- Compose a further coercion with the suffix at a term constructor. -/
def TermEvidence.cast
    (evidence : TermEvidence sigma t S)
    (suffix : Coercion sigma (.ty S) (.ty T)) :
    TermEvidence sigma t T :=
  match evidence with
  | .path resolution old => .path resolution (old.comp suffix)
  | .value valueEvidence => .value (valueEvidence.cast suffix)
  | .app function argument old =>
      .app function argument (old.comp suffix)
  | .let bound body old => .let bound body (old.comp suffix)

/-! ## Syntax-directed views -/

structure PathEvidenceView (sigma : Store n) (p : Path n)
    (T : Ty n) : Type 1 where
  location : Fin n
  resolution : Path.Resolve p sigma (.loc location)
  suffix : Coercion sigma (.ty (.Single p)) (.ty T)

def TermEvidence.pathView
    (evidence : TermEvidence sigma (.path p) T) :
    PathEvidenceView sigma p T := by
  cases evidence with
  | path resolution suffix => exact ⟨_, resolution, suffix⟩
  | value valueEvidence => cases valueEvidence

structure AppEvidenceView (sigma : Store n) (p q : Path n)
    (T : Ty n) : Type 1 where
  argumentType : Ty n
  codomain : Ty (n + 1)
  function :
    TermEvidence sigma (.path p) (.Fun argumentType codomain)
  argument : TermEvidence sigma (.path q) argumentType
  suffix : Coercion sigma (.ty (codomain.open q)) (.ty T)

def TermEvidence.appView
    (evidence : TermEvidence sigma (.app p q) T) :
    AppEvidenceView sigma p q T := by
  cases evidence with
  | value valueEvidence => cases valueEvidence
  | app function argument suffix =>
      exact ⟨_, _, function, argument, suffix⟩

structure LetEvidenceView (sigma : Store n) (s : Tm n)
    (body : Tm (n + 1)) (T : Ty n) : Type 1 where
  boundType : Ty n
  resultType : Ty n
  bound : TermEvidence sigma s boundType
  closure : BodyClosure sigma boundType body resultType.weaken
  suffix : Coercion sigma (.ty resultType) (.ty T)

def TermEvidence.letView
    (evidence : TermEvidence sigma (.let s body) T) :
    LetEvidenceView sigma s body T := by
  cases evidence with
  | value valueEvidence => cases valueEvidence
  | «let» bound closure suffix =>
      exact ⟨_, _, bound, closure, suffix⟩

/-- Value inversion is propositionally truncated because `Tm.IsValue` lives
in `Prop` while the resulting evidence lives in `Type`. -/
theorem TermEvidence.nonemptyValueView
    (evidence : TermEvidence sigma v T) (value : v.IsValue) :
    Nonempty (ValueEvidence sigma v T) := by
  cases evidence with
  | path resolution suffix => cases value
  | value valueEvidence => exact ⟨valueEvidence⟩
  | app function argument suffix => cases value
  | «let» bound closure suffix => cases value

/-! ## Continuations and states -/

/-- Evidence that a continuation maps the current type to its final type. -/
inductive Tm.Cont.Evidence :
    {n : Nat} -> Store n -> LambdaPFC.Ty n -> Tm.Cont n ->
      LambdaPFC.Ty n -> Type 1 where
| hole {n : Nat} {sigma : Store n} {S T : LambdaPFC.Ty n} :
    Coercion sigma (.ty S) (.ty T) ->
    Tm.Cont.Evidence sigma S [] T
| cons {n : Nat} {sigma : Store n} {S U V T : LambdaPFC.Ty n}
    {body : Tm (n + 1)} {cont : Tm.Cont n} :
    Tm.Cont.Evidence sigma U cont T ->
    BodyClosure sigma S body V.weaken ->
    Coercion sigma (.ty V) (.ty U) ->
    Tm.Cont.Evidence sigma S (body :: cont) T

/-- The store-local invariant for a complete machine state. -/
inductive State.Evidence :
    {n : Nat} -> State n -> LambdaPFC.Ty n -> Type 1 where
| ok {n : Nat} {sigma : Store n} {cont : Tm.Cont n}
    {term : Tm n} {S T : LambdaPFC.Ty n} :
    Tm.Cont.Evidence sigma S cont T ->
    TermEvidence sigma term S ->
    State.Evidence (State.mk sigma cont term) T

end
end LambdaPFC
