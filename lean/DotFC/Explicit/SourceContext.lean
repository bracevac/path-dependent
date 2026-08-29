import DotFC.Source.Context
import DotFC.Explicit.Context

/-!
# Translating source telescopes to Stage A contexts

Stage A keeps the source type language and introduces no ambient evidence
binders, so context translation is the homomorphic embedding of each source
term declaration into the single heterogeneous target telescope.
-/

namespace DotFC.Explicit

open DotFC

namespace Ctx

/-- Homomorphic translation of an acyclic source term context. -/
def ofSource : {s : Sig} → Source.Ctx s → Ctx s
  | _, .nil => .nil
  | _, .snoc outer type => (ofSource outer).extendTerm type

@[simp]
theorem ofSource_nil : ofSource Source.Ctx.nil = Ctx.nil := rfl

@[simp]
theorem ofSource_snoc {s : Sig} (context : Source.Ctx s)
    (type : Source.Ty s) :
    ofSource (context.snoc type) = (ofSource context).extendTerm type := rfl

/-- Source lookup is preserved exactly; in particular, both context
implementations apply the same weakening while crossing newer bindings. -/
theorem lookup_ofSource {s : Sig} {context : Source.Ctx s}
    {path : BVar s .term} {type : Source.Ty s}
    (lookup : Source.Lookup context path type) :
    (ofSource context).lookup path = Binding.term type := by
  induction lookup with
  | here => rfl
  | there lookup ih =>
      simp only [ofSource_snoc, extendTerm, lookup_there, ih,
        Binding.weaken, Binding.rename]
      rfl

end Ctx

end DotFC.Explicit
