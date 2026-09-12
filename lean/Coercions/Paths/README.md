# Paths

Paths on the vanilla line: the path project of plan V (`plan-5-extensions.md` §4, `plan-5g-paths-stages.md`),
namespace `Paths`.  The tree is a verbatim copy of `lean/Coercions/{DotMNF,FCdot,DotToFCdot,Runtime.lean}` at the
commit in `BASE`, and will grow source paths with stable fields and singleton types, the transparent self of a
literal, path-keyed blocks with a forwarding forest in the target, and a translation that keeps the safety
corollary.  Until its first stage lands, every module here is the vanilla module of the same name under the new
namespace, and the three directory READMEs describe that state.
