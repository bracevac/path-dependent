import LambdaPCC.RuntimeEquality
import LambdaPCC.Valuation

/-!
A capture-aware semantic interpretation.

These evidence families retain the capture set assigned by each value rule.
Location evidence carries both the assigned shape type and a proof from the
capture set assigned at introduction to the capture set of the assigned type.
The same capture-aware evidence is used recursively in function, pair, and
member coercions.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-- Allocation metadata for a body and its source-level use set. `World.Valid`
relates this immutable syntax and capture set to semantic value evidence. -/
inductive ExactBody :
    {n : Nat} -> Store n -> Ty n -> Tm (n + 1) -> Ty (n + 1) ->
      CaptureSet (n + 1) -> Type 1 where
| source {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {S : Ty n} {body : Tm (n + 1)}
    {T : Ty (n + 1)} {C : CaptureSet (n + 1)} :
    Tm.Ty (Gamma.snoc S) body T C ->
    ExactBody sigma (S.rename rho) (body.rename rho.ext)
      (T.rename rho.ext) (C.rename rho.ext)

/-- Allocation-time evidence for the capture set assigned to a value by its
introduction rule. This family is independent of the capture-aware world, so
the world stores that capture set. -/
inductive ExactValue :
    {n : Nat} -> Store n -> Tm n -> CaptureSet n -> Type 1 where
| abs {n : Nat} {sigma : Store n} {A : Ty n} {body : Tm (n + 1)}
    {B : Ty (n + 1)} {Q : CaptureSet n} :
    ExactBody sigma A body B
      (.union Q.weaken (.singleton (.var 0))) ->
    ExactValue sigma (.abs A body) Q
| pair {n : Nat} {sigma : Store n} {y z : Fin n} {a : Name} :
    ExactValue sigma (.pair y a (.val z))
      (.union (.singleton (.var y)) (.singleton (.var z)))
| typePair {n : Nat} {sigma : Store n} {y : Fin n} {a : Name}
    {W : Shape n} :
    ExactValue sigma (.pair y a (.type W)) (.singleton (.var y))
| capturePair {n : Nat} {sigma : Store n} {y : Fin n} {a : Name}
    {W : CaptureSet n} :
    ExactValue sigma (.pair y a (.capture W)) (.singleton (.var y))

/-- A store together with an introduction capture-set witness for every
allocated value. -/
inductive World : {n : Nat} -> Store n -> Type 1 where
| empty : World Store.empty
| val {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue}
    {Q : CaptureSet n} (world : Cap.World sigma)
    (exact : ExactValue sigma v Q) :
    World (Store.val sigma v vv)

/-- Lookup retains the capture set assigned to a stored value at introduction
while transporting it through later allocations. -/
inductive Lookup :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Fin n -> Tm n -> CaptureSet n -> Type 1 where
| here {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue}
    {Q : CaptureSet n} {world : Cap.World sigma}
    {exact : ExactValue sigma v Q} :
    Lookup (Cap.World.val world exact (vv := vv)) 0
      v.weaken Q.weaken
| there {n : Nat} {sigma : Store n} {x : Fin n} {v u : Tm n}
    {uv : u.IsValue} {Q R : CaptureSet n}
    {world : Cap.World sigma} {exact : ExactValue sigma u R}
    (old : Lookup world x v Q) :
    Lookup (Cap.World.val world exact (vv := uv)) x.succ
      v.weaken Q.weaken

mutual

/-- A source context interpreted in a capture-aware world. -/
inductive Environment :
    {n m : Nat} -> {sigma : Store m} -> (world : Cap.World sigma) ->
      Ctx n -> Valuation n m -> Type 1 where
| intro {n m : Nat} {sigma : Store m} {world : Cap.World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} :
    (lookup : forall x : Fin n,
      LocationEvidence world (rho x) ((Gamma.lookup x).rename rho)) ->
    Environment world Gamma rho

/-- A location has an assigned capturing type and remains tied to the capture
set stored for its value introduction. -/
inductive LocationEvidence :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Fin n -> Ty n -> Type 1 where
| top {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n} :
    Lookup world x v Q -> Relation world Q C ->
    LocationEvidence world x (.capt C .Top)
| fun {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {x : Fin n} {Q C : CaptureSet n} {A S : Ty n}
    {body : Tm (n + 1)} {B U : Ty (n + 1)} :
    Lookup world x (.abs A body) Q ->
    Body world A body B (.union Q.weaken (.singleton (.var 0))) ->
    TyCoercion world S A ->
    DeferredCoercion world S B U ->
    Relation world Q C ->
    LocationEvidence world x (.capt C (.Fun S U))
| pair {n : Nat} {k : Kind} {sigma : Store n} {world : Cap.World sigma}
    {x y : Fin n} {Q C : CaptureSet n}
    {a : Name} {delta : Def n k} {S : Ty n} {d : Tau (n + 1) k} :
    Lookup world x (.pair y a delta) Q ->
    LocationEvidence world y S ->
    Realizes world delta.referent (d.open (.var y)) ->
    Relation world Q C ->
    LocationEvidence world x (.capt C (.Pair S a d))
| single {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n}
    {p : Path n} :
    Lookup world x v Q ->
    Path.Resolve p sigma (.loc x) -> Relation world Q C ->
    LocationEvidence world x (.capt C (.Single p))
| selection {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {x : Fin n} {v : Tm n} {Q C E : CaptureSet n}
    {p : Path n} {a : Name} {W : Shape n} :
    Lookup world x v Q ->
    Path.Resolve (p.sel a) sigma (.type W) ->
    LocationEvidence world x (.capt E W) -> Relation world Q C ->
    LocationEvidence world x (.capt C (.TSel p a))

/-- Capture-aware realization of term, type, and capture-set members. -/
inductive Realizes :
    {n : Nat} -> {k : Kind} -> {sigma : Store n} ->
      (world : Cap.World sigma) -> Path.Referent n -> Tau n k -> Type 1 where
| loc {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {x : Fin n} {T : Ty n} :
    LocationEvidence world x T -> Realizes world (.loc x) (.term T)
| type {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {L W U : Shape n} :
    ShapeCoercion world L W -> ShapeCoercion world W U ->
    Realizes world (.type W) (.type L U)
| capture {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {L W U : CaptureSet n} :
    Relation world L W -> Relation world W U ->
    Realizes world (.capture W) (.capture L U)

/-- Subcapturing evidence whose static leaves retain a capture-aware source
environment. -/
inductive Relation :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      CaptureSet n -> CaptureSet n -> Type 1 where
| source {n m : Nat} {sigma : Store m} {world : Cap.World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {C D : CaptureSet n} :
    Environment world Gamma rho -> CaptureSet.Sub Gamma C D ->
    Relation world (C.rename rho) (D.rename rho)
| refl {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C : CaptureSet n} : Relation world C C
| trans {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D E : CaptureSet n} :
    Relation world C D -> Relation world D E -> Relation world C E
| runtime {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D : CaptureSet n} :
    CaptureSet.RuntimeConv (Path.RuntimeEq sigma) C D ->
    Relation world C D
| empty {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C : CaptureSet n} : Relation world .empty C
| unionLeft {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D : CaptureSet n} : Relation world C (.union C D)
| unionRight {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D : CaptureSet n} : Relation world D (.union C D)
| unionElim {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D E : CaptureSet n} :
    Relation world C E -> Relation world D E ->
    Relation world (.union C D) E
| alias {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p q : Path n} {x : Fin n} :
    Path.Resolve p sigma (.loc x) -> Path.Resolve q sigma (.loc x) ->
    Relation world (.singleton q) (.singleton p)
| fold {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {x : Fin n} {v : Tm n} {Q : CaptureSet n} :
    Path.Resolve p sigma (.loc x) -> Lookup world x v Q ->
    Relation world Q (.singleton p)
| fstRoot {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {x : Fin n} :
    Path.Resolve p.fst sigma (.loc x) ->
    Relation world (.singleton p.fst) (.singleton p)
| selRoot {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {a : Name} {x : Fin n} :
    Path.Resolve (p.sel a) sigma (.loc x) ->
    Relation world (.singleton (p.sel a)) (.singleton p)
| selectLower {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {a : Name} {L W : CaptureSet n} :
    Path.Resolve (p.sel a) sigma (.capture W) -> Relation world L W ->
    Relation world L (.select p a)
| selectUpper {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {a : Name} {W U : CaptureSet n} :
    Path.Resolve (p.sel a) sigma (.capture W) -> Relation world W U ->
    Relation world (.select p a) U
/-- Capture-aware coercions between capturing types. -/
inductive TyCoercion :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Ty n -> Ty n -> Type 1 where
| refl {n : Nat} {sigma : Store n} {world : Cap.World sigma} {T : Ty n} :
    TyCoercion world T T
| trans {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {T U V : Ty n} :
    TyCoercion world T U -> TyCoercion world U V ->
    TyCoercion world T V
| runtime {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {T U : Ty n} :
    Ty.RuntimeConv (Path.RuntimeEq sigma) T U -> TyCoercion world T U
| capt {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {C D : CaptureSet n} {S T : Shape n} :
    Relation world C D -> ShapeCoercion world S T ->
    TyCoercion world (.capt C S) (.capt D T)

/-- Capture-aware coercions between shapes. -/
inductive ShapeCoercion :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Shape n -> Shape n -> Type 1 where
| refl {n : Nat} {sigma : Store n} {world : Cap.World sigma} {S : Shape n} :
    ShapeCoercion world S S
| trans {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S T U : Shape n} :
    ShapeCoercion world S T -> ShapeCoercion world T U ->
    ShapeCoercion world S U
| runtime {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S T : Shape n} :
    Shape.RuntimeConv (Path.RuntimeEq sigma) S T ->
    ShapeCoercion world S T
| bot {n : Nat} {sigma : Store n} {world : Cap.World sigma} {S : Shape n} :
    ShapeCoercion world .Bot S
| top {n : Nat} {sigma : Store n} {world : Cap.World sigma} {S : Shape n} :
    ShapeCoercion world S .Top
| widen {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {x : Fin n} {C : CaptureSet n} {S : Shape n} :
    Path.Resolve p sigma (.loc x) -> LocationEvidence world x (.capt C S) ->
    ShapeCoercion world (.Single p) S
| alias {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p q : Path n} {x : Fin n} :
    Path.Resolve p sigma (.loc x) -> Path.Resolve q sigma (.loc x) ->
    ShapeCoercion world (.Single q) (.Single p)
| selectLower {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {a : Name} {L W : Shape n} :
    Path.Resolve (p.sel a) sigma (.type W) ->
    ShapeCoercion world L W -> ShapeCoercion world L (.TSel p a)
| selectUpper {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {p : Path n} {a : Name} {W U : Shape n} :
    Path.Resolve (p.sel a) sigma (.type W) ->
    ShapeCoercion world W U -> ShapeCoercion world (.TSel p a) U
| fun {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S S' : Ty n} {T T' : Ty (n + 1)} :
    TyCoercion world S' S -> DeferredCoercion world S' T T' ->
    ShapeCoercion world (.Fun S T) (.Fun S' T')
| pair {n : Nat} {k : Kind} {sigma : Store n} {world : Cap.World sigma}
    {S S' : Ty n} {a : Name} {d d' : Tau (n + 1) k} :
    TyCoercion world S S' -> MemberClosure world S d d' ->
    ShapeCoercion world (.Pair S a d) (.Pair S' a d')

/-- Capture-aware coercions between member signatures. -/
inductive Coercion :
    {n : Nat} -> {k : Kind} -> {sigma : Store n} ->
      (world : Cap.World sigma) -> Tau n k -> Tau n k -> Type 1 where
| refl {n : Nat} {k : Kind} {sigma : Store n} {world : Cap.World sigma}
    {d : Tau n k} : Coercion world d d
| trans {n : Nat} {k : Kind} {sigma : Store n} {world : Cap.World sigma}
    {d e f : Tau n k} :
    Coercion world d e -> Coercion world e f -> Coercion world d f
| runtime {n : Nat} {k : Kind} {sigma : Store n} {world : Cap.World sigma}
    {d e : Tau n k} :
    Tau.RuntimeConv (Path.RuntimeEq sigma) d e -> Coercion world d e
| term {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {T U : Ty n} : TyCoercion world T U ->
    Coercion world (.term T) (.term U)
| type {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {L U L' U' : Shape n} :
    ShapeCoercion world L' L -> ShapeCoercion world U U' ->
    Coercion world (.type L U) (.type L' U')
| capture {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {L U L' U' : CaptureSet n} :
    Relation world L' L -> Relation world U U' ->
    Coercion world (.capture L U) (.capture L' U')

/-- A capture-aware function-result coercion waiting for an argument. -/
inductive DeferredCoercion :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Ty n -> Ty (n + 1) -> Ty (n + 1) -> Type 1 where
| refl {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S : Ty n} {T : Ty (n + 1)} : DeferredCoercion world S T T
| trans {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S : Ty n} {T U V : Ty (n + 1)} :
    DeferredCoercion world S T U -> DeferredCoercion world S U V ->
    DeferredCoercion world S T V
| runtime {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S : Ty n} {T U : Ty (n + 1)} :
    Ty.RuntimeConv (Path.ScopedLift (Path.RuntimeEq sigma)) T U ->
    DeferredCoercion world S T U
| narrow {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {S S' : Ty n} {T U : Ty (n + 1)} :
    TyCoercion world S' S -> DeferredCoercion world S T U ->
    DeferredCoercion world S' T U
| source {n m : Nat} {sigma : Store m} {world : Cap.World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S : Ty n}
    {T U : Ty (n + 1)} :
    Environment world Gamma rho -> Ty.Sub (Gamma.snoc S) T U ->
    DeferredCoercion world (S.rename rho)
      (T.rename rho.ext) (U.rename rho.ext)

/-- A capture-aware dependent-member coercion waiting for a first component. -/
inductive MemberClosure :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Ty n -> {k : Kind} -> Tau (n + 1) k -> Tau (n + 1) k -> Type 1 where
| source {n m : Nat} {k : Kind} {sigma : Store m} {world : Cap.World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S : Ty n}
    {d e : Tau (n + 1) k} :
    Environment world Gamma rho -> Tau.Sub (Gamma.snoc S) d e ->
    MemberClosure world (S.rename rho) (d.rename rho.ext) (e.rename rho.ext)

/-- A source body whose result type and use set share one derivation. -/
inductive Body :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Ty n -> Tm (n + 1) -> Ty (n + 1) ->
      CaptureSet (n + 1) -> Type 1 where
| source {n m : Nat} {sigma : Store m} {world : Cap.World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S : Ty n}
    {body : Tm (n + 1)} {T : Ty (n + 1)}
    {C : CaptureSet (n + 1)} :
    Environment world Gamma rho -> Tm.Ty (Gamma.snoc S) body T C ->
    Body world (S.rename rho) (body.rename rho.ext)
      (T.rename rho.ext) (C.rename rho.ext)

/-- Joint value evidence, indexed by its assigned capture set. -/
inductive Value :
    {n : Nat} -> {sigma : Store n} -> (world : Cap.World sigma) ->
      Tm n -> Ty n -> CaptureSet n -> Type 1 where
| abs {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {A T : Ty n} {body : Tm (n + 1)} {B : Ty (n + 1)}
    {Q : CaptureSet n} :
    Body world A body B (.union Q.weaken (.singleton (.var 0))) ->
    TyCoercion world (.capt Q (.Fun A B)) T ->
    Value world (.abs A body) T Q
| pair {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {y z : Fin n} {a : Name} {T : Ty n}
    {Q : CaptureSet n} :
    Q = .union (.singleton (.var y)) (.singleton (.var z)) ->
    TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.term
            (.capt (.singleton (Path.var z).weaken)
              (.Single (Path.var z).weaken))))) T ->
    Value world (.pair y a (.val z)) T Q
| typePair {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {y : Fin n} {a : Name} {W : Shape n} {T : Ty n}
    {Q : CaptureSet n} :
    Q = .singleton (.var y) ->
    TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.type W.weaken W.weaken))) T ->
    Value world (.pair y a (.type W)) T Q
| capturePair {n : Nat} {sigma : Store n} {world : Cap.World sigma}
    {y : Fin n} {a : Name} {W : CaptureSet n} {T : Ty n}
    {Q : CaptureSet n} :
    Q = .singleton (.var y) ->
    TyCoercion world
      (.capt Q
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y))) a
          (.capture W.weaken W.weaken))) T ->
    Value world (.pair y a (.capture W)) T Q

end

/-! ## Valid worlds -/

/-- Every assigned capture set stored in a world is justified by the same
value evidence used by the capture-aware interpretation. -/
inductive World.Valid : {n : Nat} -> {sigma : Store n} ->
    World sigma -> Type 1 where
| empty : World.Valid World.empty
| val {n : Nat} {sigma : Store n} {world : World sigma}
    {v : Tm n} {vv : v.IsValue} {T : Ty n} {Q : CaptureSet n}
    {exact : ExactValue sigma v Q} :
    World.Valid world -> Value world v T Q ->
    World.Valid (World.val world exact (vv := vv))

end
end Cap
end LambdaPCC
