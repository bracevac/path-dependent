import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing

/-!
# Embedding the value-MNF core into general expressions

The general-expression language contains a typing-preserving embedding of the
earlier value-MNF captured-DOT core.  A core value embeds homomorphically.  A core
application embeds its two value operands as pure returned computations;
all other core term constructors keep their computational spine.

The embedding is established at two mutually recursive levels:

* mutually recursive source syntax;
* mutually recursive declarative typing derivations, with exactly the same
  type and capture indices.

Runtime and compiler conservativity live in the translation layer, keeping
this semantic embedding independent of both the shared runtime and FCsub.
-/

namespace DOTCapture.Acyclic.GeneralExpression.Embedding

namespace Core

abbrev Scope := DOTCapture.Acyclic.Scope
abbrev Var := DOTCapture.Acyclic.Var
abbrev Path := DOTCapture.Acyclic.Path
abbrev Capture := DOTCapture.Acyclic.Capture
abbrev Ty := DOTCapture.Acyclic.Ty
abbrev ObjectSig := DOTCapture.Acyclic.ObjectSig
abbrev ValueLabel := DOTCapture.Acyclic.ValueLabel
abbrev Ctx := DOTCapture.Acyclic.Ctx
abbrev Value := DOTCapture.Acyclic.Value
abbrev Term := DOTCapture.Acyclic.Term

end Core

namespace Surface

abbrev Value := DOTCapture.Acyclic.GeneralExpression.Value
abbrev Term := DOTCapture.Acyclic.GeneralExpression.Term

end Surface

mutual

/-- Embed a value-MNF core value into the general-expression surface. -/
def embedValue {scope : Core.Scope} : Core.Value scope → Surface.Value scope
  | .var name => .var name
  | .unit => .unit
  | .lam domain codomain body =>
      .lam domain codomain (embedTerm body)
  | .object signature typeWitness captureWitness payload =>
      .object signature typeWitness captureWitness (embedValue payload)

/-- Embed a value-MNF computation.  The only non-homomorphic case is
application: its value operands become pure computations. -/
def embedTerm {scope : Core.Scope} : Core.Term scope → Surface.Term scope
  | .ret value => .ret (embedValue value)
  | .select receiver label => .select receiver label
  | .app function argument =>
      .app (.ret (embedValue function)) (.ret (embedValue argument))
  | .let' result rhs body =>
      .let' result (embedTerm rhs) (embedTerm body)

end

mutual

/-- Every core value-typing derivation embeds without changing its type. -/
def embedValueTyping {scope : Core.Scope} {context : Core.Ctx scope}
    {value : Core.Value scope} {type : Core.Ty scope}
    (typing : DOTCapture.Acyclic.Value.HasType context value type) :
    DOTCapture.Acyclic.GeneralExpression.Value.HasType context
      (embedValue value) type :=
  match typing with
  | .var => .var
  | .unit => .unit
  | .lam domainPlain bodyTyping captures =>
      .lam domainPlain (embedTermTyping bodyTyping) captures
  | .object typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture =>
      .object typeLower typeUpper captureLower captureUpper
        (embedValueTyping payloadTyping) payloadShape payloadCapture
  | .adapt valueTyping inclusion =>
      .adapt (embedValueTyping valueTyping) inclusion

/-- Every core term-typing derivation embeds with exactly the same immediate
capture and result type.  `Capture.seq` removes the newly inserted pure
operands definitionally, including the canonical core object-let RHS. -/
def embedTermTyping {scope : Core.Scope} {context : Core.Ctx scope}
    {term : Core.Term scope} {use : Core.Capture scope}
    {type : Core.Ty scope}
    (typing : DOTCapture.Acyclic.Term.HasType context term use type) :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType context
      (embedTerm term) use type :=
  match typing with
  | .ret valueTyping => .ret (embedValueTyping valueTyping)
  | .select exposes => .select exposes
  | .app functionTyping functionShape argumentTyping =>
      .app (.ret (embedValueTyping functionTyping)) functionShape
        (.ret (embedValueTyping argumentTyping))
  | .letPlain boundPlain rhsTyping bodyTyping discharge =>
      .letPlain boundPlain (embedTermTyping rhsTyping)
        (embedTermTyping bodyTyping) discharge
  | .letObject rhsTyping bodyTyping discharge =>
      .letObject (.ret (embedValueTyping rhsTyping))
        (embedTermTyping bodyTyping) discharge
  | .use termTyping inclusion =>
      .use (embedTermTyping termTyping) inclusion

end

end DOTCapture.Acyclic.GeneralExpression.Embedding
