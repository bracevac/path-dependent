
8. **S4: closed object coercions with template morphisms; `pair`; `both`;
   source side conditions (2026-09-04, decided with the author before M3).**
   Starting M3 showed that S3 (item 6) is too strict for the translation:
   `Sub.typ`, `Sub.fld`, `Sub.and*` are *closed* subtypings between
   declaration types in DOT (they occur as the domain premise of `Sub.all`,
   nested in bounds, and under `sub` on non-variable terms), and their
   translations are coercions between object types whose telescopes mention
   the self (`S↑ ⊑ y∙A`, `y∙A ⊑ T↑`).  S3 has no closed coercion between
   such types.  What S3 got right is kept: the *morphisms the DOT rules
   generate are linear templates* — every target proposition is proven as
   `pre ∘ (source proposition j) ∘ post` with `pre`, `post` closed coercions
   typed in Γ, or is a presence inherited by index, or is read off a
   definition equality of a literal — and never eliminate through the
   self's members.  So:
   - `obj Tel m : μ Tel ≤ μ Tel'` between *closed* telescopes
     (`Telescope (s,x)`), with `m : Morphism s` whose entries are
     `le pre h post` (`pre post : Option (LeCo s)`, hole `h ∈ {le j, eq j,
     eqSym j}` naming the `j`-th source proposition), `eq j sym`, `has j`.
     Typing: a target `S' ⊑ T'` from source `X ⊑ Y` (or `X ≐ Y`) needs
     `pre = none ∧ S' = X` or `pre = some e ∧ S' = A↑ ∧ X = B↑ ∧ Γ ⊢ e : A ≤ B`,
     and symmetrically for `post`.  Normal forms carry `pre`/`post` *forms*
     (`id` for `none`); composition substitutes templates into templates,
     instantiation at an atom looks the hole up in the view and combines.
     Both structural: the normalizer, fuel monotonicity, canonical forms,
     and the chain typedness at opened shapes carry over unchanged in
     shape.  An `eq` hole instantiates to the form `id` (equal resolutions
     in the transparent store context).
   - `pair Tel₁ Tel₂ e₁ e₂ : S ≤ μ (Tel₁ ++ Tel₂)` from `e₁ : S ≤ μ Tel₁`,
     `e₂ : S ≤ μ Tel₂` (the translation of `Sub.and`); normal form:
     concatenated entries, an `id`/`eqv` component contributing identity
     templates generated from its telescope, a `bot` component making the
     whole `bot`.
   - `both Tel₁ Tel₂ a₁ a₂ : μ (Tel₁ ++ Tel₂)` from `a₁ : μ Tel₁`,
     `a₂ : μ Tel₂` with the same root (the translation of `And-I` on
     variables): view = concatenation, chain form = pairing of the chain
     forms, erasure = the root.
   - Source side conditions, all in the fragment of §3.2 but missing from
     the rules: `Ty.Decl` premises on `Sub.and1/and2/and`, `HasTy.andI`,
     `HasTy.recI/recE`, and `Wf.mu` (`⊥ ∧ T <: ⊥` and `μ(z. z.A)` have no
     translation); `Defs.Guarded` on `HasTy.obj` (no `{A = x.B}` alias, cf.
     §12 risk 2); and a context binder that remembers being a literal's
     self (`Ctx.consSelf Γ d T`, `lookup` unchanged), because the target
     types fields under the transparent precise type and every `var x` in
     the literal needs the coercion from the precise type to `⟦μ(x.T)⟧`.
