import LambdaPFC.RuntimeEquality
import LambdaPFC.Valuation
import LambdaPFC.Derivations

/-!
Finite semantic evidence for source derivations instantiated in a runtime
store.  Source variables are interpreted by a valuation into the store
scope.  Types appearing in `Possible`, `Realizes`, and `Coercion` have already
been renamed into that scope, so these families do not carry a target typing
context.

Ordinary coercions are executable finite trees.  Source subtyping below a
function binder remains deferred until an argument location is known; the
deferred constructor retains the source code and its outer environment.
Likewise, a function body is retained as a source typing code closed by its
outer environment.
-/

namespace LambdaPFC

noncomputable section

/-! ## Mutually positive semantic evidence -/

mutual

/-- A source context interpreted by concrete locations in a target store.
Functional context lookup avoids eliminating a proposition-valued binding
derivation into semantic data. -/
inductive Environment :
    {n m : Nat} -> Ctx n -> Valuation n m -> Store m -> Type 1 where
| intro {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} :
    (lookup : forall x : Fin n,
      Store.Possible sigma (rho x) ((Gamma.lookup x).rename rho)) ->
    Environment Gamma rho sigma

/-- A store location realizing a proper type in the store scope. -/
inductive Store.Possible :
    {m : Nat} -> Store m -> Fin m -> Ty m -> Type 1 where
| top {m : Nat} {sigma : Store m} {x : Fin m} :
    Store.Possible sigma x .Top
| fun {m : Nat} {sigma : Store m} {x : Fin m}
    {A S : Ty m} {body : Tm (m + 1)} {B U : Ty (m + 1)} :
    Store.Binds sigma x (.abs A body) ->
    BodyClosure sigma A body B ->
    Coercion sigma (.ty S) (.ty A) ->
    DeferredCoercion sigma S B U ->
    Store.Possible sigma x (.Fun S U)
| pair {m : Nat} {sigma : Store m} {x y : Fin m}
    {a : Name} {k : Kind} {delta : Def m k}
    {S : Ty m} {d : Tau (m + 1) k} :
    Store.Binds sigma x (Tm.pair y a delta) ->
    Store.Possible sigma y S ->
    Path.Endpoint.Realizes sigma delta.endpoint (d.open (.var y)) ->
    Store.Possible sigma x (.Pair S a d)
| single {m : Nat} {sigma : Store m} {x : Fin m} {p : Path m} :
    Path.Resolve p sigma (.val x) ->
    Store.Possible sigma x (.Single p)
| selection {m : Nat} {sigma : Store m} {x : Fin m}
    {p : Path m} {A : Name} {W : Ty m} :
    Path.Resolve (p.sel A) sigma (.type W) ->
    Store.Possible sigma x W ->
    Store.Possible sigma x (.TSel p A)

/-- A generalized runtime endpoint realizing an instantiated generalized
type.  Interval endpoints retain finite coercions for both advertised
bounds. -/
inductive Path.Endpoint.Realizes :
    {m : Nat} -> {k : Kind} -> Store m ->
    Path.Endpoint m -> Tau m k -> Type 1 where
| val {m : Nat} {sigma : Store m} {x : Fin m} {T : Ty m} :
    Store.Possible sigma x T ->
    Path.Endpoint.Realizes sigma (.val x) (.ty T)
| type {m : Nat} {sigma : Store m} {L W U : Ty m} :
    Coercion sigma (.ty L) (.ty W) ->
    Coercion sigma (.ty W) (.ty U) ->
    Path.Endpoint.Realizes sigma (.type W) (.intv L U)

/-- Executable semantic coercions in one store scope.  Selection coercions
contain the concrete selected witness and the finite coercion retrieved from
its realized interval. -/
inductive Coercion :
    {m : Nat} -> {k : Kind} -> Store m ->
    Tau m k -> Tau m k -> Type 1 where
| refl {m : Nat} {k : Kind} {sigma : Store m} {d : Tau m k} :
    Coercion sigma d d
| trans {m : Nat} {k : Kind} {sigma : Store m}
    {d1 d2 d3 : Tau m k} :
    Coercion sigma d1 d2 ->
    Coercion sigma d2 d3 ->
    Coercion sigma d1 d3
| runtime {m : Nat} {k : Kind} {sigma : Store m}
    {d1 d2 : Tau m k} :
    Tau.RuntimeConv (Path.RuntimeEq sigma) d1 d2 ->
    Coercion sigma d1 d2
| bot {m : Nat} {sigma : Store m} {T : Ty m} :
    Coercion sigma (.ty .Bot) (.ty T)
| top {m : Nat} {sigma : Store m} {T : Ty m} :
    Coercion sigma (.ty T) (.ty .Top)
| widen {m : Nat} {sigma : Store m} {p : Path m}
    {x : Fin m} {T : Ty m} :
    Path.Resolve p sigma (.val x) ->
    Store.Possible sigma x T ->
    Coercion sigma (.ty (.Single p)) (.ty T)
| alias {m : Nat} {sigma : Store m} {p q : Path m}
    {x : Fin m} :
    Path.Resolve p sigma (.val x) ->
    Path.Resolve q sigma (.val x) ->
    Coercion sigma (.ty (.Single q)) (.ty (.Single p))
| selLo {m : Nat} {sigma : Store m} {p : Path m}
    {A : Name} {L W : Ty m} :
    Path.Resolve (p.sel A) sigma (.type W) ->
    Coercion sigma (.ty L) (.ty W) ->
    Coercion sigma (.ty L) (.ty (.TSel p A))
| selHi {m : Nat} {sigma : Store m} {p : Path m}
    {A : Name} {W U : Ty m} :
    Path.Resolve (p.sel A) sigma (.type W) ->
    Coercion sigma (.ty W) (.ty U) ->
    Coercion sigma (.ty (.TSel p A)) (.ty U)
| fun {m : Nat} {sigma : Store m} {S S' : Ty m}
    {T T' : Ty (m + 1)} :
    Coercion sigma (.ty S') (.ty S) ->
    DeferredCoercion sigma S' T T' ->
    Coercion sigma (.ty (.Fun S T)) (.ty (.Fun S' T'))
| pairFst {m : Nat} {sigma : Store m} {S S' : Ty m}
    {a : Name} {k : Kind} {d : Tau (m + 1) k} :
    Coercion sigma (.ty S) (.ty S') ->
    Coercion sigma
      (.ty (.Pair S a d)) (.ty (.Pair S' a d))
| pairMember {m : Nat} {sigma : Store m} {p : Path m}
    {x : Fin m} {a : Name} {k : Kind} {d d' : Tau (m + 1) k} :
    Path.Resolve p sigma (.val x) ->
    Coercion sigma (d.open p) (d'.open p) ->
    Coercion sigma
      (.ty (.Pair (.Single p) a d))
      (.ty (.Pair (.Single p) a d'))
| bounds {m : Nat} {sigma : Store m} {S S' T T' : Ty m} :
    Coercion sigma (.ty S') (.ty S) ->
    Coercion sigma (.ty T) (.ty T') ->
    Coercion sigma (.ty S) (.ty T) ->
    Coercion sigma (.intv S T) (.intv S' T')

/-- A function-codomain coercion waiting for a concrete argument.  Only this
family retains source subtyping directly: forcing `source` first extends its
environment with the argument and then compiles the stored code. -/
inductive DeferredCoercion :
    {m : Nat} -> Store m -> Ty m ->
    Ty (m + 1) -> Ty (m + 1) -> Type 1 where
| refl {m : Nat} {sigma : Store m} {S : Ty m} {T : Ty (m + 1)} :
    DeferredCoercion sigma S T T
| trans {m : Nat} {sigma : Store m} {S : Ty m}
    {T U V : Ty (m + 1)} :
    DeferredCoercion sigma S T U ->
    DeferredCoercion sigma S U V ->
    DeferredCoercion sigma S T V
| runtime {m : Nat} {sigma : Store m} {S : Ty m}
    {T U : Ty (m + 1)} :
    Tau.RuntimeConv (Path.ScopedLift (Path.RuntimeEq sigma))
      (.ty T) (.ty U) ->
    DeferredCoercion sigma S T U
| narrow {m : Nat} {sigma : Store m} {S S' : Ty m}
    {T U : Ty (m + 1)} :
    Coercion sigma (.ty S') (.ty S) ->
    DeferredCoercion sigma S T U ->
    DeferredCoercion sigma S' T U
| source {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {S : Ty n} {T U : Ty (n + 1)} :
    Environment Gamma rho sigma ->
    SubCode (Gamma.snoc S) (.ty T) (.ty U) ->
    DeferredCoercion sigma (S.rename rho)
      (T.rename rho.ext) (U.rename rho.ext)

/-- A source function body paired with the semantic environment for its free
variables.  Its formal argument is deliberately absent from the environment
until application supplies a concrete location. -/
inductive BodyClosure :
    {m : Nat} -> Store m -> Ty m ->
    Tm (m + 1) -> Ty (m + 1) -> Type 1 where
| source {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {S : Ty n} {body : Tm (n + 1)}
    {T : Ty (n + 1)} :
    Environment Gamma rho sigma ->
    TermCode (Gamma.snoc S) body T ->
    BodyClosure sigma (S.rename rho)
      (body.rename rho.ext) (T.rename rho.ext)

end

/-! ## Environment operations -/

def Environment.lookup
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m}
    (environment : Environment Gamma rho sigma) (x : Fin n) :
    Store.Possible sigma (rho x) ((Gamma.lookup x).rename rho) := by
  cases environment with
  | intro lookup => exact lookup x

/-- The empty source context has a semantic environment in every store. -/
def Environment.empty (sigma : Store m) :
    Environment Ctx.nil (fun x => Fin.elim0 x) sigma :=
  .intro (fun x => Fin.elim0 x)

/-- Extend an environment with a concrete realization of the newest source
binding. -/
def Environment.snoc
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {S : Ty n} {y : Fin m}
    (environment : Environment Gamma rho sigma)
    (argument : Store.Possible sigma y (S.rename rho)) :
    Environment (Gamma.snoc S) (Valuation.snoc rho y) sigma := by
  apply Environment.intro
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · simpa [Ctx.lookup, Ty.weaken, Ty.rename_rename] using argument
  · simpa [Ctx.lookup, Ty.weaken, Ty.rename_rename] using
      Environment.lookup environment i

def Coercion.comp
    (first : Coercion sigma d1 d2)
    (second : Coercion sigma d2 d3) :
    Coercion sigma d1 d3 :=
  .trans first second

def DeferredCoercion.comp
    (first : DeferredCoercion sigma S T U)
    (second : DeferredCoercion sigma S U V) :
    DeferredCoercion sigma S T V :=
  .trans first second

end
end LambdaPFC
