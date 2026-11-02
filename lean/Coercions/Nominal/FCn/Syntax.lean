import Coercions.Paths.FCdot.TypingPathSubst

/-!
# FCn syntax (plan T.1, T.2)

The families of the target FCn, in the order of plan T.1, with renaming, path substitution and
evidence substitution, and the functions of T.2 that live in the syntax.  Every binder is a de
Bruijn binder of the Paths target: a family is indexed by a signature `s`, and `(s,x)` adds one
variable, `.here`.  Paths, signatures, labels, renamings and path substitutions are the Paths
target's, imported and not copied.

Binders are named in comments.  `Π(z : S) T` binds `z` in `T`.  `μ(w : Tel)` binds `w` in `Tel`.
`lift (h. T) π` binds `h` in `T`.  `pi e (z. f)` binds `z` in `f`.  The telescopes of `fold`, `both`,
`obj`, `pair` and `bound` are under their self.  `Side.bot X` and `Side.top X` carry `X` under the
self.  `let z = t in u` binds `z` in `u`.  `lam (z : S) t` binds `z` in `t`.  `obj (z : Tel) ds`
binds `z` in `Tel` and in `ds`.  `nest (v : Tel) ds` binds `v` in `Tel` only, and `ds` is addressed
by its path.

There are two substitutions (decision D6 of the groups file).  The type-level families `Ty`, `Pr`,
`Telescope`, `TyDefs`, `Block` and `Kids` take a `PathSubst`, one path per variable.  The evidence
and term families `PEq`, `PathCo`, `LeCo`, `EqCo`, `Morphism`, `Side`, `Tm`, `Value`, `Defs` and
`Rhs` take a `CoSubst`, one path evidence per variable, and act on the types inside them through
`CoSubst.paths`.  `X.weaken` is `X.rename Rename.succ` for every family.  `X.substPath p`
instantiates `.here` by the path `p` on a type-level family, and `X.substCo Q` instantiates it by the
path evidence `Q` on an evidence or term family.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The families of T.1 -/

mutual
inductive Ty : Sig → Type where
  | bot : Ty s                                              -- ⊥
  | sel : Path s → Label → Ty s                             -- p∙A
  | pi : Ty s → Ty (s,x) → Ty s                             -- Π(z : S) T, z the .here of T
  | mu : Telescope (s,x) → Ty s                             -- μ(w : Tel), w the .here of Tel
inductive Pr : Sig → Type where
  | le : Ty s → Ty s → Pr s                                 -- S ⊑ T
  | fld : Label → Ty s → Pr s                               -- fld a T
  | alias : Path s → Pr s                                   -- ≈ q
  | is : Ty s → Pr s                                        -- is T
inductive Telescope : Sig → Type where
  | nil : Telescope s                                       -- []
  | cons : Telescope s → Pr s → Telescope s                 -- Tel ▹ pr
end

mutual
inductive PEq : Sig → Type where
  | refl : Path s → PEq s                                   -- refl p
  | symm : PEq s → PEq s                                    -- symm π
  | trans : PEq s → PEq s → PEq s                           -- trans π π'
  | sel : PEq s → Label → PEq s                             -- sel π a
  | member : PathCo s → LeCo s → Nat → PEq s                -- member P e i
inductive PathCo : Sig → Type where
  | var : BVar s .var → PathCo s                            -- var x
  | sel : PathCo s → Label → Nat → PathCo s                 -- sel P a i
  | cast : PathCo s → LeCo s → PathCo s                     -- cast P e
  | alias : PathCo s → PEq s → PathCo s → PathCo s          -- alias P₀ π Q
  | sngl : PathCo s → Path s → PEq s → PathCo s             -- sngl P q π
  | fldI : Path s → Label → PathCo s → PathCo s             -- fldI p a Q
  | fold : Telescope (s,x) → PathCo s → PathCo s            -- fold Tel P, w the .here of Tel
  | unfold : PathCo s → PathCo s                            -- unfold P
  | both : Telescope (s,x) → Telescope (s,x) → PathCo s → PathCo s → PathCo s   -- both Tel Tel' P Q
inductive LeCo : Sig → Type where
  | refl : Ty s → LeCo s                                    -- refl T
  | trans : LeCo s → LeCo s → LeCo s                        -- trans e f
  | top : Ty s → LeCo s                                     -- top T
  | bot : Ty s → LeCo s                                     -- bot T
  | eqToLe : EqCo s → LeCo s                                -- eqToLe φ
  | pi : LeCo s → LeCo (s,x) → LeCo s                       -- pi e (z. f)
  | obj : Telescope (s,x) → Morphism s → LeCo s             -- obj Tel m
  | pair : Telescope (s,x) → Telescope (s,x) → LeCo s → LeCo s → LeCo s          -- pair Tel Tel' e f
  | bound : Telescope (s,x) → Nat → LeCo s                  -- bound Tel i
  | intoBnd : LeCo s → LeCo s                               -- intoBnd e
  | member : PathCo s → LeCo s → Nat → LeCo s               -- member P e i
  | seal : Path s → Label → LeCo s                          -- seal p C
inductive EqCo : Sig → Type where
  | refl : Ty s → EqCo s                                    -- refl T
  | symm : EqCo s → EqCo s                                  -- symm φ
  | trans : EqCo s → EqCo s → EqCo s                        -- trans φ ψ
  | defP : Path s → Label → EqCo s                          -- defP p A
  | lift : Ty (s,x) → PEq s → EqCo s                        -- lift (h. T) π, h the .here of T
  | dom : EqCo s → EqCo s                                   -- dom φ
  | cod : EqCo s → Path s → EqCo s                          -- cod φ p
inductive Morphism : Sig → Type where
  | nil : Morphism s                                        -- nil
  | le : Morphism s → Side s → Nat → Side s → Morphism s    -- le m pre j post
  | fld : Morphism s → Nat → Side s → Morphism s            -- fld m j sd
  | alias : Morphism s → Nat → Morphism s                   -- alias m j
  | is : Morphism s → LeCo s → Morphism s                   -- is m e
inductive Side : Sig → Type where
  | none : Side s                                           -- none
  | some : LeCo s → Side s                                  -- some e
  | bot : Ty (s,x) → Side s                                 -- bot X, X under the self
  | top : Ty (s,x) → Side s                                 -- top X, X under the self
end

mutual
inductive Tm : Sig → Type where
  | path : PathCo s → Tm s                                  -- path P
  | val : Value s → Tm s                                    -- val v
  | app : PathCo s → PathCo s → Tm s                        -- app P Q
  | lett : Tm s → Tm (s,x) → Tm s                           -- let z = t in u, z the .here of u
  | cast : Tm s → LeCo s → Tm s                             -- cast t e
inductive Value : Sig → Type where
  | lam : Ty s → Tm (s,x) → Value s                         -- lam (z : S) t, z the .here of t
  | obj : Telescope (s,x) → Defs (s,x) → Value s            -- obj (z : Tel) ds, z the .here of Tel and of ds
  | cast : Value s → LeCo s → Value s                       -- cast v e
inductive Defs : Sig → Type where
  | nil : Defs s                                            -- []
  | typ : Defs s → Label → Ty s → Defs s                    -- ds ▹ {A = U}
  | fld : Defs s → Label → Rhs s → Defs s                   -- ds ▹ {a = rhs}
  | cls : Defs s → Label → Ty s → Defs s                    -- ds ▹ {class C = U}
inductive Rhs : Sig → Type where
  | path : PathCo s → Rhs s                                 -- path P
  | fn : Value s → Rhs s                                    -- fun v
  | nest : Telescope (s,x) → Defs s → Rhs s                 -- nest (v : Tel) ds, v the .here of Tel only
end

inductive TyDefs : Sig → Type where                        -- W, type labels to types, newest last
  | nil : TyDefs s
  | cons : TyDefs s → Label → Ty s → TyDefs s               -- W[A ↦ U]
  | cls : TyDefs s → Label → Ty s → TyDefs s                -- W[class C ↦ U]

mutual
inductive Block : Sig → Type where
  | node : TyDefs s → Kids s → Block s                      -- node W C
  | fwd : Path s → Block s                                  -- fwd q
  | clo : Block s                                          -- clo
inductive Kids : Sig → Type where                          -- C, field labels to blocks, newest last
  | nil : Kids s
  | cons : Kids s → Label → Block s → Kids s                -- C[a ↦ B]
end

inductive Store : Sig → Type where
  | nil : Store []                                          -- []
  | cons : Store s → Value s → Store (s,x)                  -- σ, x ↦ v, x the new .here

inductive Frame : Sig → Type where
  | lett : Tm (s,x) → Frame s                               -- let z. u, z the .here of u
  | cast : LeCo s → Frame s                                 -- cast e

inductive Cont : Sig → Type where
  | nil : Cont s                                            -- []
  | cons : Cont s → Frame s → Cont s                        -- K ▹ fr, the newest frame last

deriving instance DecidableEq for Ty, Pr, Telescope
deriving instance DecidableEq for PEq, PathCo, LeCo, EqCo, Morphism, Side
deriving instance DecidableEq for Tm, Value, Defs, Rhs
deriving instance DecidableEq for TyDefs, Block, Kids

@[match_pattern] abbrev Ty.top : Ty s := .mu .nil                                     -- ⊤ := μ(w : [])
def Ty.sngl (q : Path s) : Ty s := .mu (.cons .nil (.alias q.weaken))                 -- μ(w : [≈ q↑])
def Telescope.length : Telescope s → Nat
  | .nil => 0
  | .cons Tel _ => Tel.length + 1
def Telescope.append : Telescope s → Telescope s → Telescope s                       -- Tel ++ Tel', the second after
  | Tel, .nil => Tel
  | Tel, .cons Tel' pr => .cons (Tel.append Tel') pr
instance : Append (Telescope s) := ⟨Telescope.append⟩
inductive Telescope.At : Telescope s → Nat → Pr s → Prop where                         -- Tel ∋ (i ↦ pr), from the oldest
  | here : Telescope.At (.cons Tel pr) Tel.length pr
  | there : Telescope.At Tel i pr → Telescope.At (.cons Tel pr') i pr

/-! ## Renaming of the type-level families -/

mutual
def Ty.rename : Ty s₁ → Rename s₁ s₂ → Ty s₂
  | .bot, _ => .bot
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .pi S T, ρ => .pi (S.rename ρ) (T.rename ρ.lift)         -- under z of Π(z : S) T
  | .mu Tel, ρ => .mu (Tel.rename ρ.lift)                    -- under w of μ(w : Tel)
def Pr.rename : Pr s₁ → Rename s₁ s₂ → Pr s₂
  | .le S T, ρ => .le (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .alias q, ρ => .alias (q.rename ρ)
  | .is T, ρ => .is (T.rename ρ)
def Telescope.rename : Telescope s₁ → Rename s₁ s₂ → Telescope s₂
  | .nil, _ => .nil
  | .cons Tel pr, ρ => .cons (Tel.rename ρ) (pr.rename ρ)
end

def TyDefs.rename : TyDefs s₁ → Rename s₁ s₂ → TyDefs s₂
  | .nil, _ => .nil
  | .cons W A U, ρ => .cons (W.rename ρ) A (U.rename ρ)
  | .cls W C U, ρ => .cls (W.rename ρ) C (U.rename ρ)

mutual
def Block.rename : Block s₁ → Rename s₁ s₂ → Block s₂
  | .node W C, ρ => .node (W.rename ρ) (C.rename ρ)
  | .fwd q, ρ => .fwd (q.rename ρ)
  | .clo, _ => .clo
def Kids.rename : Kids s₁ → Rename s₁ s₂ → Kids s₂
  | .nil, _ => .nil
  | .cons C a B, ρ => .cons (C.rename ρ) a (B.rename ρ)
end

/-! ## Path substitution of the type-level families -/

mutual
def Ty.subst : Ty s₁ → PathSubst s₁ s₂ → Ty s₂
  | .bot, _ => .bot
  | .sel p A, σ => .sel (p.subst σ) A
  | .pi S T, σ => .pi (S.subst σ) (T.subst σ.lift)           -- under z of Π(z : S) T
  | .mu Tel, σ => .mu (Tel.subst σ.lift)                     -- under w of μ(w : Tel)
def Pr.subst : Pr s₁ → PathSubst s₁ s₂ → Pr s₂
  | .le S T, σ => .le (S.subst σ) (T.subst σ)
  | .fld a T, σ => .fld a (T.subst σ)
  | .alias q, σ => .alias (q.subst σ)
  | .is T, σ => .is (T.subst σ)
def Telescope.subst : Telescope s₁ → PathSubst s₁ s₂ → Telescope s₂
  | .nil, _ => .nil
  | .cons Tel pr, σ => .cons (Tel.subst σ) (pr.subst σ)
end

def TyDefs.subst : TyDefs s₁ → PathSubst s₁ s₂ → TyDefs s₂
  | .nil, _ => .nil
  | .cons W A U, σ => .cons (W.subst σ) A (U.subst σ)
  | .cls W C U, σ => .cls (W.subst σ) C (U.subst σ)

mutual
def Block.subst : Block s₁ → PathSubst s₁ s₂ → Block s₂
  | .node W C, σ => .node (W.subst σ) (C.subst σ)
  | .fwd q, σ => .fwd (q.subst σ)
  | .clo, _ => .clo
def Kids.subst : Kids s₁ → PathSubst s₁ s₂ → Kids s₂
  | .nil, _ => .nil
  | .cons C a B, σ => .cons (C.subst σ) a (B.subst σ)
end

/-! ## Renaming of the evidence and term families -/

mutual
def PEq.rename : PEq s₁ → Rename s₁ s₂ → PEq s₂
  | .refl p, ρ => .refl (p.rename ρ)
  | .symm π, ρ => .symm (π.rename ρ)
  | .trans π π', ρ => .trans (π.rename ρ) (π'.rename ρ)
  | .sel π a, ρ => .sel (π.rename ρ) a
  | .member P e i, ρ => .member (P.rename ρ) (e.rename ρ) i
def PathCo.rename : PathCo s₁ → Rename s₁ s₂ → PathCo s₂
  | .var x, ρ => .var (ρ.var x)
  | .sel P a i, ρ => .sel (P.rename ρ) a i
  | .cast P e, ρ => .cast (P.rename ρ) (e.rename ρ)
  | .alias P₀ π Q, ρ => .alias (P₀.rename ρ) (π.rename ρ) (Q.rename ρ)
  | .sngl P q π, ρ => .sngl (P.rename ρ) (q.rename ρ) (π.rename ρ)
  | .fldI p a Q, ρ => .fldI (p.rename ρ) a (Q.rename ρ)
  | .fold Tel P, ρ => .fold (Tel.rename ρ.lift) (P.rename ρ)                    -- Tel under w
  | .unfold P, ρ => .unfold (P.rename ρ)
  | .both Tel Tel' P Q, ρ =>
      .both (Tel.rename ρ.lift) (Tel'.rename ρ.lift) (P.rename ρ) (Q.rename ρ)  -- Tel, Tel' under w
def LeCo.rename : LeCo s₁ → Rename s₁ s₂ → LeCo s₂
  | .refl T, ρ => .refl (T.rename ρ)
  | .trans e f, ρ => .trans (e.rename ρ) (f.rename ρ)
  | .top T, ρ => .top (T.rename ρ)
  | .bot T, ρ => .bot (T.rename ρ)
  | .eqToLe φ, ρ => .eqToLe (φ.rename ρ)
  | .pi e f, ρ => .pi (e.rename ρ) (f.rename ρ.lift)                            -- f under z
  | .obj Tel m, ρ => .obj (Tel.rename ρ.lift) (m.rename ρ)                       -- Tel under w
  | .pair Tel Tel' e f, ρ =>
      .pair (Tel.rename ρ.lift) (Tel'.rename ρ.lift) (e.rename ρ) (f.rename ρ)  -- Tel, Tel' under w
  | .bound Tel i, ρ => .bound (Tel.rename ρ.lift) i                             -- Tel under w
  | .intoBnd e, ρ => .intoBnd (e.rename ρ)
  | .member P e i, ρ => .member (P.rename ρ) (e.rename ρ) i
  | .seal p C, ρ => .seal (p.rename ρ) C
def EqCo.rename : EqCo s₁ → Rename s₁ s₂ → EqCo s₂
  | .refl T, ρ => .refl (T.rename ρ)
  | .symm φ, ρ => .symm (φ.rename ρ)
  | .trans φ ψ, ρ => .trans (φ.rename ρ) (ψ.rename ρ)
  | .defP p A, ρ => .defP (p.rename ρ) A
  | .lift T π, ρ => .lift (T.rename ρ.lift) (π.rename ρ)                         -- T under h
  | .dom φ, ρ => .dom (φ.rename ρ)
  | .cod φ p, ρ => .cod (φ.rename ρ) (p.rename ρ)
def Morphism.rename : Morphism s₁ → Rename s₁ s₂ → Morphism s₂
  | .nil, _ => .nil
  | .le m pre j post, ρ => .le (m.rename ρ) (pre.rename ρ) j (post.rename ρ)
  | .fld m j sd, ρ => .fld (m.rename ρ) j (sd.rename ρ)
  | .alias m j, ρ => .alias (m.rename ρ) j
  | .is m e, ρ => .is (m.rename ρ) (e.rename ρ)
def Side.rename : Side s₁ → Rename s₁ s₂ → Side s₂
  | .none, _ => .none
  | .some e, ρ => .some (e.rename ρ)
  | .bot X, ρ => .bot (X.rename ρ.lift)                                         -- X under the self
  | .top X, ρ => .top (X.rename ρ.lift)                                         -- X under the self
end

mutual
def Tm.rename : Tm s₁ → Rename s₁ s₂ → Tm s₂
  | .path P, ρ => .path (P.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app P Q, ρ => .app (P.rename ρ) (Q.rename ρ)
  | .lett t u, ρ => .lett (t.rename ρ) (u.rename ρ.lift)                         -- u under z
  | .cast t e, ρ => .cast (t.rename ρ) (e.rename ρ)
def Value.rename : Value s₁ → Rename s₁ s₂ → Value s₂
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)                           -- t under z
  | .obj Tel ds, ρ => .obj (Tel.rename ρ.lift) (ds.rename ρ.lift)                -- Tel and ds under z
  | .cast v e, ρ => .cast (v.rename ρ) (e.rename ρ)
def Defs.rename : Defs s₁ → Rename s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .typ ds A U, ρ => .typ (ds.rename ρ) A (U.rename ρ)
  | .fld ds a rhs, ρ => .fld (ds.rename ρ) a (rhs.rename ρ)
  | .cls ds C U, ρ => .cls (ds.rename ρ) C (U.rename ρ)
def Rhs.rename : Rhs s₁ → Rename s₁ s₂ → Rhs s₂
  | .path P, ρ => .path (P.rename ρ)
  | .fn v, ρ => .fn (v.rename ρ)
  | .nest Tel ds, ρ => .nest (Tel.rename ρ.lift) (ds.rename ρ)                   -- Tel under v, ds not
end

def Frame.rename : Frame s₁ → Rename s₁ s₂ → Frame s₂
  | .lett u, ρ => .lett (u.rename ρ.lift)                                        -- u under z
  | .cast e, ρ => .cast (e.rename ρ)

def Cont.rename : Cont s₁ → Rename s₁ s₂ → Cont s₂
  | .nil, _ => .nil
  | .cons K fr, ρ => .cons (K.rename ρ) (fr.rename ρ)

/-! ## Weakening, and instantiation by a path -/

def Ty.weaken (T : Ty s) : Ty (s,x) := T.rename Rename.succ
def Pr.weaken (pr : Pr s) : Pr (s,x) := pr.rename Rename.succ
def Telescope.weaken (Tel : Telescope s) : Telescope (s,x) := Tel.rename Rename.succ
def TyDefs.weaken (W : TyDefs s) : TyDefs (s,x) := W.rename Rename.succ
def Block.weaken (B : Block s) : Block (s,x) := B.rename Rename.succ
def Kids.weaken (C : Kids s) : Kids (s,x) := C.rename Rename.succ
def PEq.weaken (π : PEq s) : PEq (s,x) := π.rename Rename.succ
def PathCo.weaken (P : PathCo s) : PathCo (s,x) := P.rename Rename.succ
def LeCo.weaken (e : LeCo s) : LeCo (s,x) := e.rename Rename.succ
def EqCo.weaken (φ : EqCo s) : EqCo (s,x) := φ.rename Rename.succ
def Morphism.weaken (m : Morphism s) : Morphism (s,x) := m.rename Rename.succ
def Side.weaken (sd : Side s) : Side (s,x) := sd.rename Rename.succ
def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,x) := v.rename Rename.succ
def Defs.weaken (ds : Defs s) : Defs (s,x) := ds.rename Rename.succ
def Rhs.weaken (rhs : Rhs s) : Rhs (s,x) := rhs.rename Rename.succ
def Frame.weaken (fr : Frame s) : Frame (s,x) := fr.rename Rename.succ
def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

def Ty.substPath (T : Ty (s,x)) (p : Path s) : Ty s := T.subst (PathSubst.one p)
def Pr.substPath (pr : Pr (s,x)) (p : Path s) : Pr s := pr.subst (PathSubst.one p)
def Telescope.substPath (Tel : Telescope (s,x)) (p : Path s) : Telescope s := Tel.subst (PathSubst.one p)
def TyDefs.substPath (W : TyDefs (s,x)) (p : Path s) : TyDefs s := W.subst (PathSubst.one p)
def Block.substPath (B : Block (s,x)) (p : Path s) : Block s := B.subst (PathSubst.one p)
def Kids.substPath (C : Kids (s,x)) (p : Path s) : Kids s := C.subst (PathSubst.one p)

/-! ## The path of path evidence, and evidence substitutions -/

def PathCo.path : PathCo s → Path s                        -- T.2, plan-10-pdot.md:391-393
  | .var x => .var x
  | .sel P a _ => .sel P.path a
  | .cast P _ => P.path
  | .alias P₀ _ _ => P₀.path
  | .sngl P _ _ => P.path
  | .fldI p _ _ => p
  | .fold _ P => P.path
  | .unfold P => P.path
  | .both _ _ P _ => P.path

structure CoSubst (s₁ s₂ : Sig) where                      -- one path evidence per variable
  var : BVar s₁ .var → PathCo s₂
def CoSubst.paths (σ : CoSubst s₁ s₂) : PathSubst s₁ s₂ := ⟨fun x => (σ.var x).path⟩
def CoSubst.id : CoSubst s s := ⟨fun x => .var x⟩
def CoSubst.ofRename (ρ : Rename s₁ s₂) : CoSubst s₁ s₂ := ⟨fun x => .var (ρ.var x)⟩
def CoSubst.lift (σ : CoSubst s₁ s₂) : CoSubst (s₁,x) (s₂,x) where
  var := fun
    | .here => .var .here                                   -- the new binder to itself
    | .there y => (σ.var y).rename Rename.succ              -- the others weakened
def CoSubst.one (Q : PathCo s) : CoSubst (s,x) s where
  var := fun
    | .here => Q                                            -- z := Q
    | .there y => .var y
def CoSubst.selfCast (E : LeCo s) : CoSubst (s,x) (s,x) where
  var := fun
    | .here => .cast (.var .here) (E.rename Rename.succ)     -- z := cast (var z) E↑
    | .there y => .var (.there y)

mutual
def PEq.subst : PEq s₁ → CoSubst s₁ s₂ → PEq s₂
  | .refl p, σ => .refl (p.subst σ.paths)
  | .symm π, σ => .symm (π.subst σ)
  | .trans π π', σ => .trans (π.subst σ) (π'.subst σ)
  | .sel π a, σ => .sel (π.subst σ) a
  | .member P e i, σ => .member (P.subst σ) (e.subst σ) i
def PathCo.subst : PathCo s₁ → CoSubst s₁ s₂ → PathCo s₂
  | .var x, σ => σ.var x
  | .sel P a i, σ => .sel (P.subst σ) a i
  | .cast P e, σ => .cast (P.subst σ) (e.subst σ)
  | .alias P₀ π Q, σ => .alias (P₀.subst σ) (π.subst σ) (Q.subst σ)
  | .sngl P q π, σ => .sngl (P.subst σ) (q.subst σ.paths) (π.subst σ)
  | .fldI p a Q, σ => .fldI (p.subst σ.paths) a (Q.subst σ)
  | .fold Tel P, σ => .fold (Tel.subst σ.paths.lift) (P.subst σ)                -- Tel under w
  | .unfold P, σ => .unfold (P.subst σ)
  | .both Tel Tel' P Q, σ =>
      .both (Tel.subst σ.paths.lift) (Tel'.subst σ.paths.lift) (P.subst σ) (Q.subst σ)   -- Tel, Tel' under w
def LeCo.subst : LeCo s₁ → CoSubst s₁ s₂ → LeCo s₂
  | .refl T, σ => .refl (T.subst σ.paths)
  | .trans e f, σ => .trans (e.subst σ) (f.subst σ)
  | .top T, σ => .top (T.subst σ.paths)
  | .bot T, σ => .bot (T.subst σ.paths)
  | .eqToLe φ, σ => .eqToLe (φ.subst σ)
  | .pi e f, σ => .pi (e.subst σ) (f.subst σ.lift)                              -- f under z
  | .obj Tel m, σ => .obj (Tel.subst σ.paths.lift) (m.subst σ)                   -- Tel under w
  | .pair Tel Tel' e f, σ =>
      .pair (Tel.subst σ.paths.lift) (Tel'.subst σ.paths.lift) (e.subst σ) (f.subst σ)   -- Tel, Tel' under w
  | .bound Tel i, σ => .bound (Tel.subst σ.paths.lift) i                        -- Tel under w
  | .intoBnd e, σ => .intoBnd (e.subst σ)
  | .member P e i, σ => .member (P.subst σ) (e.subst σ) i
  | .seal p C, σ => .seal (p.subst σ.paths) C
def EqCo.subst : EqCo s₁ → CoSubst s₁ s₂ → EqCo s₂
  | .refl T, σ => .refl (T.subst σ.paths)
  | .symm φ, σ => .symm (φ.subst σ)
  | .trans φ ψ, σ => .trans (φ.subst σ) (ψ.subst σ)
  | .defP p A, σ => .defP (p.subst σ.paths) A
  | .lift T π, σ => .lift (T.subst σ.paths.lift) (π.subst σ)                     -- T under h
  | .dom φ, σ => .dom (φ.subst σ)
  | .cod φ p, σ => .cod (φ.subst σ) (p.subst σ.paths)
def Morphism.subst : Morphism s₁ → CoSubst s₁ s₂ → Morphism s₂
  | .nil, _ => .nil
  | .le m pre j post, σ => .le (m.subst σ) (pre.subst σ) j (post.subst σ)
  | .fld m j sd, σ => .fld (m.subst σ) j (sd.subst σ)
  | .alias m j, σ => .alias (m.subst σ) j
  | .is m e, σ => .is (m.subst σ) (e.subst σ)
def Side.subst : Side s₁ → CoSubst s₁ s₂ → Side s₂
  | .none, _ => .none
  | .some e, σ => .some (e.subst σ)
  | .bot X, σ => .bot (X.subst σ.paths.lift)                                    -- X under the self
  | .top X, σ => .top (X.subst σ.paths.lift)                                    -- X under the self
end

mutual
def Tm.subst : Tm s₁ → CoSubst s₁ s₂ → Tm s₂
  | .path P, σ => .path (P.subst σ)
  | .val v, σ => .val (v.subst σ)
  | .app P Q, σ => .app (P.subst σ) (Q.subst σ)
  | .lett t u, σ => .lett (t.subst σ) (u.subst σ.lift)                           -- u under z
  | .cast t e, σ => .cast (t.subst σ) (e.subst σ)
def Value.subst : Value s₁ → CoSubst s₁ s₂ → Value s₂
  | .lam S t, σ => .lam (S.subst σ.paths) (t.subst σ.lift)                       -- t under z
  | .obj Tel ds, σ => .obj (Tel.subst σ.paths.lift) (ds.subst σ.lift)            -- Tel and ds under z
  | .cast v e, σ => .cast (v.subst σ) (e.subst σ)
def Defs.subst : Defs s₁ → CoSubst s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .typ ds A U, σ => .typ (ds.subst σ) A (U.subst σ.paths)
  | .fld ds a rhs, σ => .fld (ds.subst σ) a (rhs.subst σ)
  | .cls ds C U, σ => .cls (ds.subst σ) C (U.subst σ.paths)
def Rhs.subst : Rhs s₁ → CoSubst s₁ s₂ → Rhs s₂
  | .path P, σ => .path (P.subst σ)
  | .fn v, σ => .fn (v.subst σ)
  | .nest Tel ds, σ => .nest (Tel.subst σ.paths.lift) (ds.subst σ)               -- Tel under v, ds not
end

def CoSubst.comp (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃) : CoSubst s₁ s₃ := ⟨fun x => (σ.var x).subst τ⟩
def CoSubst.compRename (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃) : CoSubst s₁ s₃ := ⟨fun x => (σ.var x).rename ρ⟩
def Rename.coComp (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃) : CoSubst s₁ s₃ := ⟨fun x => σ.var (ρ.var x)⟩

def PEq.substCo (π : PEq (s,x)) (Q : PathCo s) : PEq s := π.subst (CoSubst.one Q)
def PathCo.substCo (P : PathCo (s,x)) (Q : PathCo s) : PathCo s := P.subst (CoSubst.one Q)
def LeCo.substCo (e : LeCo (s,x)) (Q : PathCo s) : LeCo s := e.subst (CoSubst.one Q)
def EqCo.substCo (φ : EqCo (s,x)) (Q : PathCo s) : EqCo s := φ.subst (CoSubst.one Q)
def Morphism.substCo (m : Morphism (s,x)) (Q : PathCo s) : Morphism s := m.subst (CoSubst.one Q)
def Side.substCo (sd : Side (s,x)) (Q : PathCo s) : Side s := sd.subst (CoSubst.one Q)
def Tm.substCo (t : Tm (s,x)) (Q : PathCo s) : Tm s := t.subst (CoSubst.one Q)
def Value.substCo (v : Value (s,x)) (Q : PathCo s) : Value s := v.subst (CoSubst.one Q)
def Defs.substCo (ds : Defs (s,x)) (Q : PathCo s) : Defs s := ds.subst (CoSubst.one Q)
def Rhs.substCo (rhs : Rhs (s,x)) (Q : PathCo s) : Rhs s := rhs.subst (CoSubst.one Q)

/-! ## The functions of T.2 that live in the syntax -/

def Value.isLam : Value s → Bool                           -- T.2, plan-10-pdot.md:394
  | .lam _ _ => true
  | .obj _ _ => false
  | .cast v _ => v.isLam
def Value.core : Value s → Value s                          -- plan-10-pdot.md:395
  | .lam S t => .lam S t
  | .obj Tel ds => .obj Tel ds
  | .cast v _ => v.core
def Value.composite : Value s → Option (LeCo s)            -- plan-10-pdot.md:408-409
  | .lam _ _ => none
  | .obj _ _ => none
  | .cast v e => some (match v.composite with | none => e | some E => .trans E e)
def Defs.labels : Defs s → List Label                      -- plan-10-pdot.md:396
  | .nil => []
  | .typ ds A _ => A :: ds.labels
  | .fld ds a _ => a :: ds.labels
  | .cls ds C _ => C :: ds.labels
def Tm.adjust (u : Tm (s,x)) (v : Value s) : Tm (s,x) :=   -- plan-10-pdot.md:410
  match v.composite with
  | none => u
  | some E => u.subst (CoSubst.selfCast E)

/-! ## Tests of the class clauses

Each clause of a class constructor at `Rename.succ`, and at `PathSubst.one` or `CoSubst.one`, on a
term whose one free variable is `.here`.  The substituted path is `z∙a`, `z` the one variable left. -/

namespace ClsSyntaxTests

private def pz : Path ([],x) := .var .here                                      -- z
private def pza : Path ([],x) := .sel (.var .here) (.trm 0)                     -- z∙a
private def Qza : PathCo ([],x) := .sel (.var .here) (.trm 0) 0                 -- sel z a 0

example : (TyDefs.cls .nil (.typ 0) (.sel pz (.typ 1))).rename Rename.succ
    = TyDefs.cls (.nil : TyDefs (([],x),x)) (.typ 0) (.sel (.var (.there .here)) (.typ 1)) := by rfl
example : (LeCo.seal pz (.typ 0)).rename Rename.succ
    = (LeCo.seal (.var (.there .here)) (.typ 0) : LeCo (([],x),x)) := by rfl
example : (Defs.cls .nil (.typ 0) (.sel pz (.typ 1))).rename Rename.succ
    = Defs.cls (.nil : Defs (([],x),x)) (.typ 0) (.sel (.var (.there .here)) (.typ 1)) := by rfl
example : (TyDefs.cls .nil (.typ 0) (.sel (.var .here) (.typ 1)) : TyDefs (([],x),x)).subst (PathSubst.one pza)
    = TyDefs.cls .nil (.typ 0) (.sel pza (.typ 1)) := by rfl
example : (LeCo.seal (.var .here) (.typ 0) : LeCo (([],x),x)).subst (CoSubst.one Qza)
    = LeCo.seal pza (.typ 0) := by rfl
example : (Defs.cls .nil (.typ 0) (.sel (.var .here) (.typ 1)) : Defs (([],x),x)).subst (CoSubst.one Qza)
    = Defs.cls .nil (.typ 0) (.sel pza (.typ 1)) := by rfl

end ClsSyntaxTests

end Nominal.FCn
