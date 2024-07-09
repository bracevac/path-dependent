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

      inductive Tau: Nat -> Kind -> Type -- classifies the dependent second component of a pair _type_
      | ty  : Ty n -> Tau n star            -- field member of type T
      | intv: Ty n -> Ty n -> Tau n iota    -- type member with interval S .. T

      inductive Def: Nat -> Kind -> Type -- classifies the second component of a pair _term_
      | val  : Tm n -> Def n star           -- field member definition
      | type : Ty n -> Def n iota           -- type member definition

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

    -- FIXME: these appear to have no effect?
    instance : Coe (Path n) (Ty n) where
      coe p := Ty.Single p

    instance : Coe (Path n) (Tm n) where
      coe p := Tm.path p

    instance : Coe (Ty n) (Tau n Kind.star) where
      coe T := Tau.ty T

    instance : Coe (Ty n) (Def n Kind.iota) where
      coe T := Def.type T

    abbrev Interval (n: Nat) := Ty n × Ty n

    def Tau.interval {n} (sig : Tau n iota): Interval n :=
      match sig with
      | Tau.intv S T => (S, T)
      | _ => sorry -- TODO impossible

    def Ty.open: Ty (n + 1) -> Path n -> Ty n := sorry -- TODO

    def Tau.open: Tau (n + 1) mκ -> Path n -> Tau n mκ -- TODO
    | ty T  => sorry
    | intv S T => sorry

    def Tm.weaken: Tm n -> Tm (n + 1) := sorry

    def Ty.weaken: Ty n -> Ty (n + 1) := sorry

    def Tau.weaken: Tau n mκ -> Tau (n + 1) mκ := sorry -- TODO

end LambdaP.Syntax
