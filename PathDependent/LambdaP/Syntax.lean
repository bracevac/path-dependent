import PathDependent.FinFun.Basic

namespace LambdaP.Syntax

    abbrev Name: Type := Nat -- Label names for fields and types

    inductive Kind: Type
    | star -- types
    | iota -- intervals

    -- Syntax is intrinsically scoped, i.e., it is usually indexed by the length of the typing context binding the free variables (deBruijn indices).

    inductive Path: Nat -> Type
    | var : Fin n  -> Path n         -- term variable
    | fst : Path n -> Path n         -- select the "first" component of the pair pointed to by the given path
    | sel : Path n -> Name -> Path n -- select the named component of the pair pointed to by the given path

    mutual

      inductive Tau : Nat -> Kind -> Type -- classifies the dependent second component of a pair _type_
      | ty  : Ty n -> Tau n Kind.star            -- field member of type T
      | intv: Ty n -> Ty n -> Tau n Kind.iota    -- type member with interval S .. T

      inductive Def: Nat -> Kind -> Type -- classifies the second component of a pair _term_
      | val  : Fin n -> Def n Kind.star          -- field member definition (in MNF this can only be a variable)
      | type : Ty n -> Def n Kind.iota           -- type member definition

      inductive Ty: Nat -> Type
      | Top    : Ty n                                   -- ⊤
      | Bot    : Ty n                                   -- ⊥
      | Fun    : Ty n -> Ty (n + 1) -> Ty n             -- (x: S) -> T[x]
      | Pair   : Ty n -> Name -> Tau (n + 1) κ -> Ty n  -- ⟨x: S, a: Tau[x]⟩, dependent pair with named term member or type interval
      | Single : Path n -> Ty n                         -- Singleton denoted by the given path p

      -- terms are in monadic normal form (MNF)
      inductive Tm: Nat -> Type
      | path   : Path n -> Tm n                         -- paths p subsume the variable case
      | abs    : Ty n -> Tm (n + 1) -> Tm n             -- λ(x: T) t
      | pair   : Fin n -> Name -> Def n κ -> Tm n       -- ⟨y, a = z⟩ | <y, A = T>
      | app    : Path n -> Path n -> Tm n               -- p q
      | let    : Tm n -> Tm (n + 1) -> Tm n             -- let x = s in t
      | typed  : Tm n -> Ty n -> Tm n                   -- type ascription t : T

    end

    instance : Coe (Path n) (Ty n) where
      coe p := Ty.Single p

    instance : Coe (Path n) (Tm n) where
      coe p := Tm.path p

    -- FIXME: these appear to have no effect?
    instance : Coe (Ty n) (Tau n Kind.star) where
      coe T := Tau.ty T

    instance : Coe (Ty n) (Def n Kind.iota) where
      coe T := Def.type T

    abbrev Interval (n: Nat) := Ty n × Ty n

    def Tau.interval {n} (sig : Tau n Kind.iota): Interval n :=
      match sig with
      | Tau.intv S T => (S, T)

    def Path.rename: Path n -> FinFun n m -> Path m
    | Path.var n,   f => Path.var (f n)
    | Path.fst p,   f => Path.fst (p.rename f)
    | Path.sel p α, f => Path.sel (p.rename f) α

    mutual

      def Ty.rename: Ty n -> FinFun n m -> Ty m
      | Ty.Top       , _ => Ty.Top
      | Ty.Bot       , _ => Ty.Bot
      | Ty.Fun S T   , f => Ty.Fun (S.rename f) (T.rename f.ext)
      | Ty.Pair S α τ, f => Ty.Pair (S.rename f) α (τ.rename f.ext)
      | Ty.Single p' , f => Ty.Single (p'.rename f)

      def Tau.rename: Tau n κ -> FinFun n m -> Tau m κ
      | Tau.ty T,     f => Tau.ty (T.rename f)
      | Tau.intv S T, f => Tau.intv (S.rename f) (T.rename f)

      def Tm.rename: Tm n -> FinFun n m -> Tm m
      | Tm.path p,     f => Tm.path (p.rename f)
      | Tm.abs T t,    f => Tm.abs (T.rename f) (t.rename f.ext)
      | Tm.pair x α d, f => Tm.pair (f x) α (d.rename f)
      | Tm.app p q,    f => Tm.app (p.rename f) (q.rename f)
      | Tm.let t1 t2,  f => Tm.let (t1.rename f) (t2.rename f.ext)
      | Tm.typed t T,  f => Tm.typed (t.rename f) (T.rename f)

      def Def.rename: Def n κ -> FinFun n m -> Def m κ
      | Def.val x,  f => Def.val (f x)
      | Def.type T, f => Def.type (T.rename f)

    end

    def Path.weaken (p: Path n): Path (n + 1) := p.rename FinFun.weaken

    def Ty.weaken (T: Ty n): Ty (n + 1) := T.rename FinFun.weaken

    def Tau.weaken (τ: Tau n κ): Tau (n + 1) κ := τ.rename FinFun.weaken

    def Tm.weaken (t: Tm n): Tm (n + 1) := t.rename FinFun.weaken

    def Path.open: Path (n + 1) -> Path n -> Path n := sorry

    mutual

      def Ty.open:  Ty (n + 1) -> Path n -> Ty n
      | Ty.Top       , _ => Ty.Top
      | Ty.Bot       , _ => Ty.Bot
      | Ty.Fun S T   , p => Ty.Fun (S.open p) (T.open p.weaken)
      | Ty.Pair S α τ, p => Ty.Pair (S.open p) α (τ.open p.weaken)
      | Ty.Single p' , p => Ty.Single (p'.open p)

      def Tau.open: Tau (n + 1) κ -> Path n -> Tau n κ
      | Tau.ty T,     p => Tau.ty (T.open p)
      | Tau.intv S T, p => Tau.intv (S.open p) (T.open p)

    end

end LambdaP.Syntax
