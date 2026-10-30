import Coercions.Nominal.Translation.Defs

/-!
# Terms and definitions (plan X, Parts TR.5 and TR.6, stage X6 group g3)

A source typing derivation translates to an FCn term, a definition typing to one FCn definition
appended to the definitions translated so far, and a definition list typing to an FCn definition
list.  `HasTy.translate`, `DefTy.translate` and `DefsTy.translate` are one structural recursion over
three of the four families of `Source/Typing.lean`, one equation per source rule (decision D1 of the
groups file).  The term of `ty_new_intro` calls the definitions, and the definition of `ty_def_all`
calls the term.  The path images of `Evidence` are an earlier function, called and never recursed
into.

A derivation at a path term translates to `path ⟦d⟧`, with `⟦d⟧` the path image `translatePath`.
`ty_sub` at a path term is one of them, and `ty_sub` at any other term is a cast.

FCn's definitions are a list with the newest last (`FCp/Syntax.lean:111-114`), so `DefTy.translate`
takes the list so far and appends one (decision D8).  At `ty_def_all` the value is the lambda under
the casts of the `ty_sub` steps that end the derivation, read by `Translation.toValue`, with a
fallback that no derivation reaches (`HasTy.translate_lam_of_eq`).  At `ty_def_new` the nested
literal's telescope is `tel` of its own annotation, the `T` of `.new T ds`.  The plan writes the outer
annotation's `tel` opened under the binder (`plan-10-pdot.md:790`), equal by `Ty.tel_subst_lift`.

Plan XII adds `ty_def_cls`: a class definition `{class C = T}` appends the class definition
`{class C = ⟦T⟧}` of FCn, typed by DF-Cls.

`E3_translate_isVal` runs the translation of E3's whole derivation in the kernel.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

mutual
/-- The image `⟦d⟧` of a typing derivation, one equation per source rule of TR.6.  A derivation at
a path term is `path ⟦d⟧`. -/
def HasTy.translate : {G : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy G t T → FCn.Tm s
  | _, _, _, d@(.ty_var _) => .path d.translatePath                           -- a path term ↦ path ⟦d⟧
  | _, _, _, .ty_all_intro (S := S) dt => .val (.lam S.translate dt.translate)  -- z of dt : t : U ↦ val (lam (z : ⟦S⟧) ⟦dt⟧)
  | _, _, _, .ty_all_elim dp dq => .app dp.translatePath dq.translatePath      -- dp : p : ∀(z : S) T, dq : q : S ↦ app ⟦dp⟧ ⟦dq⟧
  | _, _, _, .ty_new_intro (T := T) dds => .val (.obj T.tel dds.translate)     -- z of dds ↦ val (obj (z : tel T) ⟦dds⟧)
  | _, _, _, d@(.ty_new_elim _) => .path d.translatePath                     -- d : p.a : T, a path term ↦ path ⟦d⟧
  | _, _, _, d@(.ty_rcd_intro _) => .path d.translatePath                    -- d : p : {a : T}, a path term ↦ path ⟦d⟧
  | _, _, _, .ty_let dt du => .lett dt.translate du.translate                  -- dt : t : T, z of du : u : U↑ ↦ let z = ⟦dt⟧ in ⟦du⟧
  | _, _, _, d@(.ty_sngl _ _) => .path d.translatePath                       -- d : p : T, a path term ↦ path ⟦d⟧
  | _, _, _, d@(.ty_path_elim _ _) => .path d.translatePath                  -- d : p.a : (q.a).type, a path term ↦ path ⟦d⟧
  | _, _, _, d@(.ty_rec_intro _) => .path d.translatePath                    -- d : p : μ(z. T), a path term ↦ path ⟦d⟧
  | _, _, _, d@(.ty_rec_elim _) => .path d.translatePath                     -- d : p : T⟨p⟩, a path term ↦ path ⟦d⟧
  | _, _, _, d@(.ty_and_intro _ _) => .path d.translatePath                  -- d : p : T ∧ U, a path term ↦ path ⟦d⟧
  | _, .path _, _, d@(.ty_sub _ _) => .path d.translatePath                  -- ty_sub at a path term
  | _, _, _, .ty_sub d e => .cast d.translate e.translate                     -- ty_sub at any other term ↦ cast ⟦d⟧ ⟦e⟧
/-- The image of one definition typing, appended to the definitions `ds` translated so far, one
equation per source rule of TR.5. -/
def DefTy.translate : {G : Ctx s} → {r : Path s} → {d : Def s} → {D : Dec s} → DefTy G r d D → FCn.Defs s → FCn.Defs s
  | _, _, _, _, .ty_def_typ (A := A) (T := T), ds => .typ ds A T.translate      -- {A = T} ↦ ds ▹ {A = ⟦T⟧}
  | _, _, _, _, .ty_def_all (b := b) (T := T) dl, ds =>                          -- dl : λ(z : T) t : ∀(z : U) V ↦ ds ▹ {b = fun ⟦dl⟧ᵥ}
      .fld ds b (.fn ((Translation.toValue dl.translate).getD (.lam T.translate (.path (.var .here)))))
  | _, _, _, _, .ty_def_new (b := b) (T := T) _ dds, ds => .fld ds b (.nest T.tel dds.translate)   -- T over (s,v) ↦ ds ▹ {b = nest (v : tel T) ⟦dds⟧} (D8)
  | _, _, _, _, .ty_def_path (b := b) dq, ds => .fld ds b (.path dq.translatePath)                 -- dq : q : T ↦ ds ▹ {b = path ⟦dq⟧}
  | _, _, _, _, .ty_def_cls (C := C) (T := T) _, ds => .cls ds C T.translate    -- {class C = T} ↦ ds ▹ {class C = ⟦T⟧} (DF-Cls)
/-- The image of a definition list typing, the oldest definition first. -/
def DefsTy.translate : {G : Ctx s} → {r : Path s} → {ds : Defs s} → {T : Ty s} → DefsTy G r ds T → FCn.Defs s
  | _, _, _, _, .ty_defs_one d => d.translate .nil                            -- [] ▹ d ↦ [] ▹ ⟦d⟧
  | _, _, _, _, .ty_defs_cons dds d _ => d.translate dds.translate            -- ds ▹ d ↦ ⟦ds⟧ ▹ ⟦d⟧
end

/-- The kernel runs the translation of E3's whole derivation, and its image is a value under casts. -/
theorem E3_translate_isVal : (Translation.toValue CP_d.translate).isSome = true := by decide +kernel   -- decide +kernel, E3's whole derivation

end Nominal.Source
