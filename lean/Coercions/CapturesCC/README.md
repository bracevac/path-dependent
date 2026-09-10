# CapturesCC

Captures, the compiler's way: the second capture project of plan V (`plan-5-extensions.md` §3,
`plan-5b-captures-cc-note.md`), namespace `CapturesCC`.  The tree is a verbatim copy of `lean/Coercions/Captures/` at
the commit in `BASE`, the end of captures the DOT way, and will grow the compiler's scope roots, levels, the capture
binder on the arrow, and `fresh` as a per-call existential.  Until its first stage lands, every module here is the
captures module of the same name under the new namespace, and the three directory READMEs describe that state.
