namespace LambdaP.Syntax

    abbrev Name: Type := Nat -- Label names for fields and types

    inductive MemKind: Type -- classifies names/members
    | field -- names of term members
    | type  -- names of type members

    -- Syntax is intrinsically scoped, i.e., it is usually indexed by the length of the typing context binding the free variables (deBruijn indices).

    inductive Path: Nat -> Type
    | var : Fin n  -> Path n          -- term variable
    | fst : Path n -> Path n          -- select the "first" component of the pair pointed to by the given path
    | sel : Path n -> Name -> Path n -- select the named component of the pair pointed to by the given path

    mutual

      -- TODO: we could aim for a more PTS-style version without term/type stratification, and fuse ComponentSig and ComponentDef into one
      inductive ComponentSig: Nat -> MemKind -> Type -- classifies the dependent second component of a pair _type_
      | field : Ty n -> ComponentSig n field         -- field member of type T
      | type  : Ty n -> Ty n -> ComponentSig n type  -- type member with interval S .. T

      inductive ComponentDef: Nat -> MemKind -> Type -- classifies the second component of a pair _term_
      | field : Tm n -> ComponentDef n field         -- field member definition
      | type  : Ty n -> ComponentDef n type          -- type member definition

      inductive Ty: Nat -> Type
      | Top    : Ty n                                              -- ⊤
      | Bot    : Ty n                                              -- ⊥
      | Fun    : Ty n -> Ty (n + 1) -> Ty n                        -- (x: S) -> T[x]
      | Pair   : Ty n -> Name -> ComponentSig (n + 1) mκ -> Ty n   -- ⟨x: S, a: CompSig[x]⟩, dependent pair with named term member or type interval
      | Single : Path n -> Ty n                                    -- Singleton denoted by the given path p

      -- terms are in monadic normal form (MNF)
      inductive Tm: Nat -> Type
      | path   : Path n -> Tm n                             -- paths p subsume the variable case
      | abs    : Ty n -> Tm (n + 1) -> Tm n                 -- λ(x: T) t
      | pair   : Fin n -> Name -> ComponentDef n mκ -> Tm n -- ⟨y, a = z⟩ | <y, A = T>
      | app    : Path n -> Path n -> Tm n                   -- p q
      | let    : Tm n -> Tm (n + 1) -> Tm n                 -- let x = s in t
      | typed  : Tm n -> Ty n -> Tm n                       -- type ascription t : T

    end

    abbrev Interval (n: Nat) := Ty n × Ty n

    def ComponentSig.interval {n} (sig : ComponentSig n MemKind.type): Interval n :=
      match sig with
      | @ComponentSig.type _ _ S T => (S, T)
      | @ComponentSig.field _ _ x => sorry -- TODO impossible case

    def Ty.open: Ty (n + 1) -> Path n -> Ty n := sorry -- TODO

    def ComponentSig.open: ComponentSig (n + 1) mκ -> Path n -> ComponentSig n mκ -- TODO
    | field T  => sorry
    | type S T => sorry

    def Tm.weaken: Tm n -> Tm (n + 1) := sorry

    def Ty.weaken: Ty n -> Ty (n + 1) := sorry

    def ComponentSig.weaken: ComponentSig n mκ -> ComponentSig (n + 1) mκ := sorry -- TODO

end LambdaP.Syntax
