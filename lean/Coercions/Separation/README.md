# Separation

Separation on the compiler's way: the last capture project of plan V (`plan-5-extensions.md` §6,
`plan-5h-separation-stages.md`), namespace `Separation`.  The tree is a verbatim copy of
`lean/Coercions/CapturesCC/` at the commit in `BASE`, and will grow modes on capture elements, a
mutable and consumable store with its invariant, read-only kinding, the separation judgment with its
proposition sort in the target, consume and fresh in the source, and the translation.  Until its
first stage lands, every module here is the compiler's-way module of the same name under the new
namespace, and the three directory READMEs describe that state.
