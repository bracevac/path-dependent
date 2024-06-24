namespace LambdaP.Syntax

    -- Global symbolic names for type members
    def TyName := Nat
    -- Global symbolic names for term members
    def TmName := Nat -- TODO: is it better to wrap those in inductives to make them truly different sorts?

    -- Syntax is intrinsically scoped, i.e., it is usually indexed by the length of the typing context binding the free variables (deBruijn indices).

    inductive Path: Nat -> Type where
    | pvar  : Fin n  -> Path n           -- term variable
    | pself : Path n -> Path n           -- select the "first" component of the pair pointed to by the given path
    | psel  : TmName -> Path n -> Path n -- select the named "second" term component of the pair pointed to by the given path

    mutual

      -- For ranges/type intervals, we can't do the straightforward structure definition in a mutual block:
      -- structure Range (n: Nat) where
      --   lower : Ty n
      --   upper : Ty n
      -- Instead, we need to define an inductive type here, along with explicit destructors outside of the mutual block.
      inductive Range: Nat -> Type where
      | RRange : Ty n -> Ty n -> Range n

      inductive Ty: Nat -> Type where
      | TTop    : Ty n                                    -- ⊤
      | TBot    : Ty n                                    -- ⊥
      | TFun    : Ty n -> Ty (n + 1) -> Ty n              -- (x: S) -> T[x]
      | TPairTm : Ty n -> TmName -> Ty (n + 1) -> Ty n    -- ⟨x: S, a: T[x]⟩, dependent pair with term member
      | TPairTy : Ty n -> TyName -> Range (n + 1) -> Ty n -- ⟨x: S, A: Range[x]⟩, dependent pair with type member
      | TSingle : Path n -> Ty n                          -- Singleton denoted by the given path p
      | TSel    : TyName -> Path n -> Ty n                -- Type member named A of the given path p

      -- terms are in monadic normal form (MNF)
      inductive Tm: Nat -> Type where
      | tpath   : Path n -> Tm n                   -- paths p subsume the variable case
      | tabs    : Ty n -> Tm (n + 1) -> Tm n       -- λ(x: T) t
      | tpairtm : Fin n -> TmName -> Fin n -> Tm n -- ⟨y, a = z⟩
      | tpairty : Fin n -> TyName -> Ty n -> Tm n  -- ⟨y, A = T⟩ TODO: not entirely clear: should the dependent component be a Ty n or a Ty (n + 1)?
      | tapp    : Fin n -> Fin n -> Tm n           -- x y
      | tlet    : Tm n -> Tm (n + 1) -> Tm n       -- let x = s in t
      | tasc    : Tm n -> Ty n -> Tm n             -- t : T

    end

    def Range.lower: Range n -> Ty n
    | RRange l _ => l

    def Range.upper: Range n -> Ty n
    | RRange _ u => u

end LambdaP.Syntax
