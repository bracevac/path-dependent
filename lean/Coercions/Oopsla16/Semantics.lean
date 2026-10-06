import Coercions.Oopsla16.Structural

/-!
# Operational semantics

`step` of `dot.v:197-212`: a substitution machine with congruence rules, over
a store that only grows.  It is not the store-and-continuation machine of
`Coercions.DotMNF.Machine`; the reference is not in normal form, so reduction
needs `ST_App1` and `ST_App2`.

Allocation substitutes the object's own new location into its definitions, so
a stored definition list is closed in the local scope and may mention its own
location.  Method invocation then substitutes only the argument.  The only
answers are concrete variables.

The reference's concrete identifiers are absolute positions and therefore
survive allocation untouched (`dot.v:21-22`).  Here the same fact is the
explicit store weakening `Grows.rename`, which the two congruence rules apply
to the operand they do not reduce.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-! ## Store growth -/

/-- `σ'` is `σ` with some locations allocated on top.  The reference writes
this as `G' ++ G1` (`dot_soundness.v:1134`). -/
inductive Grows : Sig → Sig → Type where
  /-- No allocation. -/
  | refl : Grows σ σ
  /-- One more location. -/
  | snoc : Grows σ σ' → Grows σ (σ',x)

/-- Growth is a store renaming. -/
def Grows.rename : Grows σ1 σ2 → Rename σ1 σ2
  | .refl => Rename.id
  | .snoc g => g.rename.comp Rename.succ

/-- Growth composes. -/
def Grows.comp : Grows σ1 σ2 → Grows σ2 σ3 → Grows σ1 σ3
  | g, .refl => g
  | g, .snoc h => .snoc (g.comp h)

/-! ## Reduction -/

/-- `step`, `dot.v:197-212`.  The `Grows` index records the allocation the
step performs, which the reference leaves implicit. -/
inductive Step : {σ1 σ2 : Sig} → Grows σ1 σ2 → Store σ1 σ1 → Tm σ1 [] →
    Store σ2 σ2 → Tm σ2 [] → Prop where
  /-- `ST_Obj`, `dot.v:199-200`: allocate, substituting the object's own new
  location for its self. -/
  | ST_Obj {σ : Sig} {G : Store σ σ} {D : Dms σ ([],x)} :
      Step (.snoc .refl) G (.tobj D)
        (G.weakenStore.cons (D.weakenStore.substVr (.conc .here)))
        (.tvar (.conc .here))
  /-- `ST_AppAbs`, `dot.v:201-204`: invoke a method of a stored object.  The
  self was substituted at allocation, so only the argument is substituted. -/
  | ST_AppAbs {σ : Sig} {G : Store σ σ} {f y : BVar σ .var} {l : Lb}
      {OT1 : Option (Ty σ [])} {OT2 : Option (Ty σ ([],x))} {t12 : Tm σ ([],x)} :
      (G.lookup f).get? l = some (.dfun OT1 OT2 t12) →
      Step .refl G (.tapp (.tvar (.conc f)) l (.tvar (.conc y))) G
        (t12.substVr (.conc y))
  /-- `ST_App1`, `dot.v:206-208`: reduce the receiver, weakening the
  argument. -/
  | ST_App1 {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {G' : Store σ2 σ2}
      {t1 : Tm σ1 []} {t1' : Tm σ2 []} {l : Lb} {t2 : Tm σ1 []} :
      Step g G t1 G' t1' →
      Step g G (.tapp t1 l t2) G' (.tapp t1' l (t2.renameStore g.rename))
  /-- `ST_App2`, `dot.v:209-211`: reduce the argument once the receiver is a
  concrete variable, weakening the receiver. -/
  | ST_App2 {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1} {G' : Store σ2 σ2}
      {f : BVar σ1 .var} {l : Lb} {t2 : Tm σ1 []} {t2' : Tm σ2 []} :
      Step g G t2 G' t2' →
      Step g G (.tapp (.tvar (.conc f)) l t2) G'
        (.tapp (.tvar (.conc (g.rename.var f))) l t2')

/-- Reflexive transitive closure, across store scopes. -/
inductive Steps : {σ1 σ2 : Sig} → Grows σ1 σ2 → Store σ1 σ1 → Tm σ1 [] →
    Store σ2 σ2 → Tm σ2 [] → Prop where
  | refl {σ : Sig} {G : Store σ σ} {t : Tm σ []} : Steps .refl G t G t
  | tail {σ1 σ2 σ3 : Sig} {g : Grows σ1 σ2} {h : Grows σ2 σ3}
      {G : Store σ1 σ1} {G' : Store σ2 σ2} {G'' : Store σ3 σ3}
      {t : Tm σ1 []} {t' : Tm σ2 []} {t'' : Tm σ3 []} :
      Steps g G t G' t' → Step h G' t' G'' t'' → Steps (g.comp h) G t G'' t''

/-- The answers of the reference: concrete variables.  `dot_soundness.v:1133`. -/
def Tm.IsAnswer : Tm σ [] → Prop
  | .tvar (.conc _) => True
  | _ => False

end Oopsla16
