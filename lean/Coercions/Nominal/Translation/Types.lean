import Coercions.Nominal.FCn.TypingSubst
import Coercions.Nominal.Source.Repl

/-!
# Translation of types (plan X, Part TR.2, stage X6 group g1)

A source type translates to an FCn type.  The tel-like types are `⊤`, a record `{D}` and an
intersection.  A tel-like `T` translates to the object type `μ(w : tel⁺ T)`, where `tel⁺ T` reads
`T` as propositions about a fresh self `w`.  Every other type contributes the one proposition
`[is ⟦T⟧]` to a telescope.

The plan writes `tel⁺ T := tel (T↑)`.  A recursion on `T↑` is not structural.  So this module
spells out one level of `tel⁺`.  `Dec.telP` and `Ty.telP` give `tel⁺` directly, with the self the
`.here` of `(s,x)`.  `Dec.telAt` and `Ty.telAt` give `tel` with the self passed as a variable, as the
Paths translation does (`Paths/DotToFCdot/Types.lean`).  `Ty.tel T` is `T.telAt .here` for
`T : Ty (s,x)`.  The plan's definition of `tel⁺` is the theorem `Ty.telP_eq_tel_weaken` of
`TypesLemmas.lean`.

`Ty.translate` and the four telescope functions are one mutual block.  Every call is on a subterm,
so the block is structural and `decide +kernel` evaluates a translation.

A type member `{A : S..U}` gives two propositions, the lower bound first.  `FCn.Telescope.At` counts
from the oldest proposition (`FCp/Syntax.lean:161-163`), so index 0 is the lower bound
`⟦S⟧ ⊑ w∙A` and index 1 is the upper bound `w∙A ⊑ ⟦U⟧`.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The tel-like types of TR.2: `⊤`, a record and an intersection.  `⟦T⟧ = μ(w : tel⁺ T)` exactly at
these. -/
def Ty.telLike : Ty s → Bool                                  -- the tel-like types of TR.2
  | .top => true                                              -- ⊤
  | .rcd _ => true                                            -- {D}
  | .and _ _ => true                                          -- T ∧ U
  | .bot => false                                             -- ⊥
  | .sel _ _ => false                                         -- p.A
  | .mu _ => false                                            -- μ(z. T)
  | .all _ _ => false                                         -- ∀(z : S) T
  | .sngl _ => false                                          -- p.type

mutual
/-- The type translation `⟦T⟧` of TR.2.  A tel-like type becomes an object type over the telescope
`tel⁺ T`, a recursive type `μ(z. T)` an object type over `tel T` with its own self, and every other
type its FCn counterpart. -/
def Ty.translate : Ty s → FCn.Ty s                            -- ⟦T⟧
  | .top => .mu .nil                                          -- ⟦⊤⟧ = μ(w : [])
  | .bot => .bot                                              -- ⟦⊥⟧ = ⊥
  | .rcd D => .mu D.telP                                      -- ⟦{D}⟧ = μ(w : tel⁺ {D})
  | .and T U => .mu (T.telP ++ U.telP)                        -- ⟦T ∧ U⟧ = μ(w : tel⁺ T ++ tel⁺ U)
  | .sel p A => .sel p A                                      -- ⟦p.A⟧ = p∙A
  | .mu T => .mu (T.telAt .here)                              -- ⟦μ(z. T)⟧ = μ(z : tel T), z the .here of T
  | .all S T => .pi S.translate T.translate                   -- ⟦∀(z : S) T⟧ = Π(z : ⟦S⟧) ⟦T⟧, z the .here of T
  | .sngl p => FCn.Ty.sngl p                                  -- ⟦p.type⟧ = μ(w : [≈ p↑])
/-- `tel⁺ {D}`: the propositions a declaration contributes about a fresh self `w`, the `.here` of
`(s,x)`.  A type member gives its lower bound, then its upper bound.  A field gives its field
proposition. -/
def Dec.telP : Dec s → FCn.Telescope (s,x)                    -- tel⁺ {D}, w the .here
  | .typ A S U => .cons (.cons .nil (.le S.translate.weaken (.sel (.var .here) A))) (.le (.sel (.var .here) A) U.translate.weaken)   -- [⟦S⟧↑ ⊑ w∙A, w∙A ⊑ ⟦U⟧↑]
  | .trm a T => .cons .nil (.fld a T.translate.weaken)        -- [fld a ⟦T⟧↑]
/-- `tel⁺ T`: the propositions a type contributes about a fresh self `w`, the `.here` of `(s,x)`.  A
tel-like type gives its declarations, any other type the one proposition `is ⟦T⟧↑`. -/
def Ty.telP : Ty s → FCn.Telescope (s,x)                      -- tel⁺ T, w the .here
  | .top => .nil                                              -- tel⁺ ⊤ = []
  | .rcd D => D.telP                                          -- tel⁺ {D}
  | .and T U => T.telP ++ U.telP                              -- tel⁺ (T ∧ U) = tel⁺ T ++ tel⁺ U
  | .bot => .cons .nil (.is (FCn.Ty.bot).weaken)              -- [is ⊥↑]
  | .sel p A => .cons .nil (.is (FCn.Ty.sel p A).weaken)      -- [is (p∙A)↑]
  | .mu T => .cons .nil (.is (FCn.Ty.mu (T.telAt .here)).weaken)               -- [is ⟦μ(z. T)⟧↑]
  | .all S T => .cons .nil (.is (FCn.Ty.pi S.translate T.translate).weaken)    -- [is ⟦∀(z : S) T⟧↑]
  | .sngl p => .cons .nil (.is (FCn.Ty.sngl p).weaken)        -- [is ⟦p.type⟧↑]
/-- `tel {D}` with the self read as the variable `self`: the propositions a declaration contributes
about a self already in scope. -/
def Dec.telAt (self : BVar s .var) : Dec s → FCn.Telescope s -- tel {D} with the self read as `self`
  | .typ A S U => .cons (.cons .nil (.le S.translate (.sel (.var self) A))) (.le (.sel (.var self) A) U.translate)   -- [⟦S⟧ ⊑ self∙A, self∙A ⊑ ⟦U⟧]
  | .trm a T => .cons .nil (.fld a T.translate)               -- [fld a ⟦T⟧]
/-- `tel T` with the self read as the variable `self`: the propositions a type contributes about a
self already in scope.  A tel-like type gives its declarations, any other type `is ⟦T⟧`. -/
def Ty.telAt (self : BVar s .var) : Ty s → FCn.Telescope s   -- tel T with the self read as `self`
  | .top => .nil                                              -- tel ⊤ = []
  | .rcd D => D.telAt self                                    -- tel {D}
  | .and T U => T.telAt self ++ U.telAt self                  -- tel (T ∧ U) = tel T ++ tel U
  | .bot => .cons .nil (.is .bot)                             -- [is ⊥]
  | .sel p A => .cons .nil (.is (.sel p A))                   -- [is p∙A]
  | .mu T => .cons .nil (.is (.mu (T.telAt .here)))           -- [is ⟦μ(z. T)⟧], z the .here of T
  | .all S T => .cons .nil (.is (.pi S.translate T.translate))   -- [is ⟦∀(z : S) T⟧]
  | .sngl p => .cons .nil (.is (FCn.Ty.sngl p))               -- [is ⟦p.type⟧]
end

/-- `tel T` of TR.2 for `T : Ty (s,x)`, whose self `w` is the `.here` of its signature. -/
def Ty.tel (T : Ty (s,x)) : FCn.Telescope (s,x) := T.telAt .here   -- tel T, the self w is the .here of T

-- structural, not well-founded

end Nominal.Source
