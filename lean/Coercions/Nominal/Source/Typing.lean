import Coercions.Nominal.Source.Repl

/-!
# Typing

The four judgments of pDOT, as `Definitions.v:585-948` of the Coq formalization states them, in one
mutual block of `Type`-valued families.

* `HasTy G t T` is `G ⊢ t : T`, Coq's `ty_trm` (`:585-734`), 13 constructors.
* `DefTy G r d D` is `G ⊢[r] d : D`, Coq's `ty_def` (`:740-781`), 4 constructors.  Coq indexes it by
  a variable `x` and a field list `bs`.  Here the index is the path `r = x.bs` itself.
* `DefsTy G r ds T` is `G ⊢[r] ds :: T`, Coq's `ty_defs` (`:783-808`), 2 constructors.
* `Sub G S T` is `G ⊢ S <: T`, Coq's `subtyp` (`:810-948`), 14 constructors.

Each constructor carries its Coq name, and its premises come in Coq's order.  A Coq premise in a
context extended by a fresh name, `∀ z ∉ L, G & z ~ T ⊢ J^z`, is one premise in `G.cons T`, whose
newest variable `.here` is `z`.  The self of a literal is bound by `G.consSelf T`, since its type `T`
mentions it (`ty_new_intro`, Coq's `G & z ~ open_typ z T`).  Coq's `ty_def_new` has the premise
`p = p_sel (avar_f x) bs`, which the path index states.  So `ty_def_new` has two premises here.

Binders are named in comments only.  `.here` is the newest variable of a signature.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

mutual
/-- `G ⊢ t : T`, Coq's `ty_trm` (`Definitions.v:585`). -/
inductive HasTy : Ctx s → Tm s → Ty s → Type where
  -- :593  G.lookup x = T  ⟹  G ⊢ path x : T
  | ty_var : G.lookup x = T → HasTy G (.path (.var x)) T
  -- :604  G, z : S ⊢ t : U  ⟹  G ⊢ val λ(z : S) t : ∀(z : S) U
  | ty_all_intro : HasTy (G.cons S) t U → HasTy G (.val (.lam S t)) (.all S U)
  -- :616  G ⊢ path p : ∀(z : S) T,  G ⊢ path q : S  ⟹  G ⊢ app p q : T⟨q⟩
  | ty_all_elim : HasTy G (.path p) (.all S T) → HasTy G (.path q) S → HasTy G (.app p q) (T.substPath q)
  -- :628  G, z :ˢ T ⊢[z] ds :: T  ⟹  G ⊢ val ν(z : T) ds : μ(z. T)
  | ty_new_intro : DefsTy (G.consSelf T) (.var .here) ds T → HasTy G (.val (.new T ds)) (.mu T)
  -- :639  G ⊢ path p : {a : T}  ⟹  G ⊢ path p.a : T
  | ty_new_elim : HasTy G (.path p) (.rcd (.trm a T)) → HasTy G (.path (p.sel a)) T
  -- :649  G ⊢ path p.a : T  ⟹  G ⊢ path p : {a : T}
  | ty_rcd_intro : HasTy G (.path (p.sel a)) T → HasTy G (.path p) (.rcd (.trm a T))
  -- :661  G ⊢ t : T,  G, z : T ⊢ u : U↑  ⟹  G ⊢ let z = t in u : U
  | ty_let : HasTy G t T → HasTy (G.cons T) u U.weaken → HasTy G (.lett t u) U
  -- :674  G ⊢ path p : q.type,  G ⊢ path q : T  ⟹  G ⊢ path p : T
  | ty_sngl : HasTy G (.path p) (.sngl q) → HasTy G (.path q) T → HasTy G (.path p) T
  -- :686  G ⊢ path p : q.type,  G ⊢ path q.a : T  ⟹  G ⊢ path p.a : (q.a).type
  | ty_path_elim : HasTy G (.path p) (.sngl q) → HasTy G (.path (q.sel a)) T →
      HasTy G (.path (p.sel a)) (.sngl (q.sel a))
  -- :697  G ⊢ path p : T⟨p⟩  ⟹  G ⊢ path p : μ(z. T)
  | ty_rec_intro : HasTy G (.path p) (T.substPath p) → HasTy G (.path p) (.mu T)
  -- :707  G ⊢ path p : μ(z. T)  ⟹  G ⊢ path p : T⟨p⟩
  | ty_rec_elim : HasTy G (.path p) (.mu T) → HasTy G (.path p) (T.substPath p)
  -- :718  G ⊢ path p : T,  G ⊢ path p : U  ⟹  G ⊢ path p : T ∧ U
  | ty_and_intro : HasTy G (.path p) T → HasTy G (.path p) U → HasTy G (.path p) (.and T U)
  -- :730  G ⊢ t : T,  G ⊢ T <: U  ⟹  G ⊢ t : U
  | ty_sub : HasTy G t T → Sub G T U → HasTy G t U
/-- `G ⊢[r] d : D`, Coq's `ty_def` (`Definitions.v:740`), with `r` the path Coq writes `x.bs`. -/
inductive DefTy : Ctx s → Path s → Def s → Dec s → Type where
  -- :742  G ⊢[r] {A = T} : {A : T..T}
  | ty_def_typ : DefTy G r (.typ A T) (.typ A T T)
  -- :751  G ⊢ val λ(z : T) t : ∀(z : U) V  ⟹  G ⊢[r] {b = defv λ(z : T) t} : {b : ∀(z : U) V}
  | ty_def_all : HasTy G (.val (.lam T t)) (.all U V) → DefTy G r (.trm b (.defv (.lam T t))) (.trm b (.all U V))
  -- :761  (μ(z. T)).tight,  G ⊢[r.b] ds⟨r.b⟩ :: T⟨r.b⟩  ⟹  G ⊢[r] {b = defv ν(z : T) ds} : {b : μ(z. T)}
  | ty_def_new : (Ty.mu T).tight = true →
      DefsTy G (r.sel b) (ds.substPath (r.sel b)) (T.substPath (r.sel b)) →
      DefTy G r (.trm b (.defv (.new T ds))) (.trm b (.mu T))
  -- :773  G ⊢ path q : T  ⟹  G ⊢[r] {b = defp q} : {b : q.type}
  | ty_def_path : HasTy G (.path q) T → DefTy G r (.trm b (.defp q)) (.trm b (.sngl q))
/-- `G ⊢[r] ds :: T`, Coq's `ty_defs` (`Definitions.v:783`).  The last definition is on the right. -/
inductive DefsTy : Ctx s → Path s → Defs s → Ty s → Type where
  -- :790  G ⊢[r] d : D  ⟹  G ⊢[r] [] ▹ d :: {D}
  | ty_defs_one : DefTy G r d D → DefsTy G r (.cons .nil d) (.rcd D)
  -- :802  G ⊢[r] ds :: T,  G ⊢[r] d : D,  ds.hasnt d.label  ⟹  G ⊢[r] ds ▹ d :: T ∧ {D}
  | ty_defs_cons : DefsTy G r ds T → DefTy G r d D → ds.hasnt d.label → DefsTy G r (.cons ds d) (.and T (.rcd D))
/-- `G ⊢ S <: T`, Coq's `subtyp` (`Definitions.v:810`). -/
inductive Sub : Ctx s → Ty s → Ty s → Type where
  -- :816  G ⊢ T <: ⊤
  | subtyp_top : Sub G T .top
  -- :823  G ⊢ ⊥ <: T
  | subtyp_bot : Sub G .bot T
  -- :830  G ⊢ T <: T
  | subtyp_refl : Sub G T T
  -- :840  G ⊢ S <: T,  G ⊢ T <: U  ⟹  G ⊢ S <: U
  | subtyp_trans : Sub G S T → Sub G T U → Sub G S U
  -- :849  G ⊢ T ∧ U <: T
  | subtyp_and11 : Sub G (.and T U) T
  -- :853  G ⊢ T ∧ U <: U
  | subtyp_and12 : Sub G (.and T U) U
  -- :863  G ⊢ S <: T,  G ⊢ S <: U  ⟹  G ⊢ S <: T ∧ U
  | subtyp_and2 : Sub G S T → Sub G S U → Sub G S (.and T U)
  -- :874  G ⊢ T <: U  ⟹  G ⊢ {a : T} <: {a : U}
  | subtyp_fld : Sub G T U → Sub G (.rcd (.trm a T)) (.rcd (.trm a U))
  -- :885  G ⊢ S₂ <: S₁,  G ⊢ T₁ <: T₂  ⟹  G ⊢ {A : S₁..T₁} <: {A : S₂..T₂}
  | subtyp_typ : Sub G S₂ S₁ → Sub G T₁ T₂ → Sub G (.rcd (.typ A S₁ T₁)) (.rcd (.typ A S₂ T₂))
  -- :897  G ⊢ path p : q.type,  G ⊢ path q : U,  p ↦ q ⊢ T ⇝ T'  ⟹  G ⊢ T <: T'
  | subtyp_sngl_pq : HasTy G (.path p) (.sngl q) → HasTy G (.path q) U → Repl p q T T' → Sub G T T'
  -- :910  G ⊢ path p : q.type,  G ⊢ path q : U,  q ↦ p ⊢ T ⇝ T'  ⟹  G ⊢ T <: T'
  | subtyp_sngl_qp : HasTy G (.path p) (.sngl q) → HasTy G (.path q) U → Repl q p T T' → Sub G T T'
  -- :922  G ⊢ path p : {A : S..T}  ⟹  G ⊢ S <: p.A
  | subtyp_sel2 : HasTy G (.path p) (.rcd (.typ A S T)) → Sub G S (.sel p A)
  -- :932  G ⊢ path p : {A : S..T}  ⟹  G ⊢ p.A <: T
  | subtyp_sel1 : HasTy G (.path p) (.rcd (.typ A S T)) → Sub G (.sel p A) T
  -- :944  G ⊢ S₂ <: S₁,  G, z : S₂ ⊢ T₁ <: T₂  ⟹  G ⊢ ∀(z : S₁) T₁ <: ∀(z : S₂) T₂
  | subtyp_all : Sub G S₂ S₁ → Sub (G.cons S₂) T₁ T₂ → Sub G (.all S₁ T₁) (.all S₂ T₂)
end

end Nominal.Source
