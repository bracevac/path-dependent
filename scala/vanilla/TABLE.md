# The vanilla corpus against scalac

Written by `lake env lean --run scripts/scala/Agree.lean vanilla scala/vanilla`.  Do not edit it by hand.
CI runs the same command and fails when the file it writes differs from this one.

- scalac 3.8.4, default flags, 120 s per run.
- Files: 169.  pos 74, neg 31, disagree 10, outside 54.
- Classes (plan S-21): agree-accept 74, ours-stricter 4, ours-looser 6, agree-reject 29, refuse-differently 2, agree-giveup 0, broken 0, outside 54.
- Fills of the pos files (F): 74.  agree-accept 73, agree-reject 1.  21 print a written self type as an ascribed literal (XV1 D-12).  F admits a fill of another class than agree-accept only with that cause, and its row says (D-12).
- Round trips (R): 116 files the reader takes, same 116.  131 example programs, same 77, gap 54.

## Files

| file | folder | scalac | warnings | ours | ours in Scala | class | cause or rule | fill | round trip |
|---|---|---|---|---|---|---|---|---|---|
| Alias | pos | ok |  | ok : ∀(x : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}) x.A | (x0: { type A = Any => Any }) => x0.A | agree-accept |  | agree-accept | same |
| AliasD | pos | ok |  | ok : ∀(x : {A : ∀(x : ⊤) ⊤ .. ∀(x : ⊤) ⊤}) x.A | (x0: { type A = Any => Any }) => x0.A | agree-accept |  | agree-accept | same |
| AndInc | pos | ok |  | ok : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤) | ({ val a: Any } => Any) & ({ val b: Any } => Any) | agree-accept |  | agree-accept | same |
| AndTop | pos | ok |  | ok : (∀(x : ⊤) ⊤) ∧ ⊤ | (Any => Any) & Any | agree-accept |  | agree-accept | same |
| AndTopD | pos | ok |  | ok : (∀(x : ⊤) ⊤) ∧ ⊤ | (Any => Any) & Any | agree-accept |  | agree-accept | same |
| AndTwo | pos | ok |  | ok : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤) | ({ val a: Any } => Any) & (Any => Any) | agree-accept |  | agree-accept | same |
| AndTwoD | pos | ok |  | ok : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤) | ({ val a: Any } => Any) & (Any => Any) | agree-accept |  | agree-accept | same |
| Asc | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| AscD | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| Body | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ⊤) ⊤ | (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| BodyD | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ⊤) ⊤ | (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| Callee | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ⊤) ⊤ | (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| CalleeAnd | pos | ok |  | ok : ∀(x : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)) ∀(y : ⊤) ⊤ | ({ val a: Any } => Any) & (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| CalleeAndD | pos | ok |  | ok : ∀(x : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)) ∀(y : ⊤) ⊤ | ({ val a: Any } => Any) & (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| CalleeArg | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ∀(y : ⊤) ⊤) ⊤ | (Any => Any) => (Any => Any) => Any | agree-accept |  | agree-accept | same |
| CalleeArgD | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ∀(y : ⊤) ⊤) ⊤ | (Any => Any) => (Any => Any) => Any | agree-accept |  | agree-accept | same |
| CalleeD | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ⊤) ⊤ | (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| CalleeFunGoal | pos | ok |  | ok : ∀(x : ∀(x : {a : ⊤}) ⊤) ∀(y : {a : ⊤} ∧ {b : ⊤}) ⊤ | ({ val a: Any } => Any) => { val a: Any; val b: Any } => Any | agree-accept |  | agree-accept | same |
| CalleeFunGoalD | pos | ok |  | ok : ∀(x : ∀(x : {a : ⊤}) ⊤) ∀(y : {a : ⊤} ∧ {b : ⊤}) ⊤ | ({ val a: Any } => Any) => { val a: Any; val b: Any } => Any | agree-accept |  | agree-accept | same |
| CalleeLet | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| CalleeLetD | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| CalleeTopGoal | pos | ok |  | ok : ∀(x : ∀(x : {a : ⊤}) ⊤) ⊤ | ({ val a: Any } => Any) => Any | agree-accept |  | agree-accept | same |
| CalleeTopGoalD | pos | ok |  | ok : ∀(x : ∀(x : {a : ⊤}) ⊤) ⊤ | ({ val a: Any } => Any) => Any | agree-accept |  | agree-accept | same |
| DeclVal | pos | ok |  | ok : ∀(x : {A : ⊥ .. ⊤}) ∀(y : ⊥) ⊤ | { type A } => Nothing => Any | agree-accept |  | agree-accept | same |
| Dom | pos | ok |  | ok : ∀(x : (∀(x : ∀(x : {a : ⊤}) {a : ⊤}) {a : ⊤}) ∧ (∀(x : ∀(x : {a : ⊤}) {a : ⊤}) ⊤)) {a : ⊤} | (({ val a: Any } => { val a: Any }) => { val a: Any }) & (({ val a: Any } => { val a: Any }) => Any) => { val a: Any } | agree-accept |  | agree-accept | same |
| DomD | pos | ok |  | ok : ∀(x : (∀(x : ∀(x : {a : ⊤}) {a : ⊤}) {a : ⊤}) ∧ (∀(x : ∀(x : {a : ⊤}) {a : ⊤}) ⊤)) {a : ⊤} | (({ val a: Any } => { val a: Any }) => { val a: Any }) & (({ val a: Any } => { val a: Any }) => Any) => { val a: Any } | agree-accept |  | agree-accept | same |
| E10t | pos | ok |  | ok : ∀(x : ∀(x : ⊤) ⊤) ∀(y : ∀(y : ⊤) ⊤) ⊤ | (Any => Any) => (Any => Any) => Any | agree-accept |  | agree-accept | same |
| E11 | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| E11a | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| E11aA | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| E1s | pos | ok |  | ok : ∀(x : {A : ⊤ .. ⊥}) {B : {a : ⊤} .. {a : ⊤}} | { type A >: Any <: Nothing } => { type B = { val a: Any } } | agree-accept |  | agree-accept | same |
| E3s | pos | ok |  | ok : ∀(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}) ∀(y : {b : ⊤}) {a : ⊤} | { type A <: { val a: Any } } & { type A >: { val b: Any } } => { val b: Any } => { val a: Any } | agree-accept |  | agree-accept | same |
| E5 | pos | ok |  | ok : ∀(x : {A : ⊤ .. ⊤}) x.A | (x0: { type A = Any }) => x0.A | agree-accept |  | agree-accept | same |
| E5W | pos | ok |  | ok : ∀(x : {A : ⊤ .. ⊤}) {A : ⊤ .. ⊤} | { type A = Any } => { type A = Any } | agree-accept |  | agree-accept | same |
| E6 | pos | ok |  | ok : ∀(x : {a : ⊤}) μ(y. {T : {a : ⊤} .. {a : ⊤}} ∧ {v : y.T}) | { val a: Any } => { type T = { val a: Any }; val v: this.T } | agree-accept |  | agree-accept | same |
| E6W | pos | ok |  | ok : ∀(x : {a : ⊤}) {T : {a : ⊤} .. {a : ⊤}} ∧ {v : {a : ⊤}} | { val a: Any } => { type T = { val a: Any }; val v: { val a: Any } } | agree-accept |  | agree-accept | same |
| E8 | pos | ok |  | ok : ∀(x : {A : ⊥ .. {a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) ⊤ | (x0: { type A <: { val a: Any } }) => x0.A & { val a: Any } => Any | agree-accept |  | agree-accept | same |
| E9 | pos | ok |  | ok : ∀(x : {A : ⊥ .. {a : ⊤}}) ∀(y : x.A) ⊤ | (x0: { type A <: { val a: Any } }) => x0.A => Any | agree-accept |  | agree-accept | same |
| Fwd | pos | ok |  | ok : {a : ∀(x : ⊤) ⊤} ∧ {b : ∀(x : ⊤) ⊤} | { val a: Any => Any; val b: Any => Any } | agree-accept |  | agree-accept | same |
| Id0 | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| IdAsc | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| IdAscD | pos | ok |  | ok : ∀(x : ⊤) ⊤ | Any => Any | agree-accept |  | agree-accept | same |
| IdTop | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| Inc | pos | ok |  | ok : ∀(x : (∀(x : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(x : ∀(x : {b : ⊤}) ⊤) ⊤)) ⊤ | (({ val a: Any } => Any) => Any) & (({ val b: Any } => Any) => Any) => Any | agree-accept |  | agree-accept | same |
| J1Lit | pos | ok |  | ok : ∀(x : {b : ⊤}) {a : {b : ⊤}} | { val b: Any } => { val a: { val b: Any } } | agree-accept |  | agree-accept | same |
| J1LitTyped | pos | ok |  | ok : ∀(x : {b : ⊤}) {a : {b : ⊤}} | { val b: Any } => { val a: { val b: Any } } | agree-accept |  | agree-accept | same |
| J1SelfSel | pos | ok |  | ok : ∀(x : ⊤) μ(y. {A : ⊥ .. ⊤} ∧ {a : y.A}) | Any => { type A; val a: this.A } | agree-accept |  | agree-accept | same |
| J1ValLast | pos | ok |  | ok : ∀(x : {a : ⊤}) {a : ⊤} | { val a: Any } => { val a: Any } | agree-accept |  | agree-accept | same |
| J1ValSel | pos | ok |  | ok : ∀(x : {a : ⊤}) ⊤ | { val a: Any } => Any | agree-accept |  | agree-accept | same |
| J1X1 | pos | ok |  | ok : ∀(x : ⊤) {a : ⊤} | Any => { val a: Any } | agree-accept |  | agree-accept | same |
| J2RecTyped | pos | ok |  | ok : {a : ⊤} | { val a: Any } | agree-accept |  | agree-reject (D-12): scalac error: E045 at 8, ours rejected: Recursive value a needs type | same |
| J2ValLit | pos | ok |  | ok : ∀(x : {b : ⊤}) {b : ⊤} | { val b: Any } => { val b: Any } | agree-accept |  | agree-accept | same |
| J4E5 | pos | ok |  | ok : ∀(x : {A : ⊤ .. ⊤}) x.A | (x0: { type A = Any }) => x0.A | agree-accept |  | agree-accept | same |
| J4E6Typed | pos | ok |  | ok : ∀(x : {a : ⊤}) μ(y. {T : {a : ⊤} .. {a : ⊤}} ∧ {v : y.T}) | { val a: Any } => { type T = { val a: Any }; val v: this.T } | agree-accept |  | agree-accept | same |
| J4E6Untyped | pos | ok |  | ok : ∀(x : {a : ⊤}) μ(y. {T : {a : ⊤} .. {a : ⊤}} ∧ {v : y.T}) | { val a: Any } => { type T = { val a: Any }; val v: this.T } | agree-accept |  | agree-accept | same |
| K1 | pos | ok |  | ok : ∀(x : ∀(x : ∀(x : {a : ⊤}) ⊤) ⊤) ⊤ | (({ val a: Any } => Any) => Any) => Any | agree-accept |  | agree-accept | same |
| K1A | pos | ok |  | ok : ∀(x : ∀(x : ∀(x : {a : ⊤}) ⊤) ⊤) ⊤ | (({ val a: Any } => Any) => Any) => Any | agree-accept |  | agree-accept | same |
| LetArg | pos | ok |  | ok : ∀(x : ∀(x : ∀(x : ⊤) ⊤) ⊤) ⊤ | ((Any => Any) => Any) => Any | agree-accept |  | agree-accept | same |
| Lower | pos | ok |  | ok : ∀(x : {A : ∀(x : ⊤) ⊤ .. ⊤}) x.A | (x0: { type A >: Any => Any }) => x0.A | agree-accept |  | agree-accept | same |
| NoDom | pos | ok |  | ok : {a : ∀(x : ⊤) ⊤} | { val a: Any => Any } | agree-accept |  | agree-accept | same |
| P1 | pos | ok |  | ok : ∀(x : ∀(x : {b : ⊤} ∧ {v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}) x.A) ∀(y : {b : ⊤} ∧ {v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}) {a : ⊤} | ((x0: { val b: Any; val v: Any; type A <: { val a: Any } }) => x0.A) => { val b: Any; val v: Any; type A <: { val a: Any } } => { val a: Any } | agree-accept |  | agree-accept | same |
| P5 | pos | ok |  | ok : ∀(x : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)) ∀(y : ⊤) ⊤ | ({ val a: Any } => Any) & (Any => Any) => Any => Any | agree-accept |  | agree-accept | same |
| R1 | pos | ok |  | ok : ∀(x : {A : ⊥ .. {a : ⊤}}) ∀(y : x.A ∧ {a : {b : ⊤}}) ⊤ | (x0: { type A <: { val a: Any } }) => x0.A & { val a: { val b: Any } } => Any | agree-accept |  | agree-accept | same |
| R2 | pos | ok |  | ok : ∀(x : {a : ⊤} ∧ {a : {b : ⊤}}) ⊤ | { val a: Any } & { val a: { val b: Any } } => Any | agree-accept |  | agree-accept | same |
| Rd1Struct2 | pos | ok |  | ok : {a : ∀(x : ⊤) ⊤} | { val a: Any => Any } | agree-accept |  | agree-accept | same |
| Rd1X1 | pos | ok |  | ok : ∀(x : ⊤) {a : ⊤} | Any => { val a: Any } | agree-accept |  | agree-accept | same |
| Rd1X2 | pos | ok |  | ok : ∀(x : ⊤) {a : ⊤} | Any => { val a: Any } | agree-accept |  | agree-accept | same |
| Struct | pos | ok |  | ok : {a : ∀(x : ⊤) ⊤} | { val a: Any => Any } | agree-accept |  | agree-accept | same |
| X1 | pos | ok |  | ok : ∀(x : (∀(x : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(x : ∀(x : ⊤) {a : ⊤}) ⊤)) ⊤ | ((Any => Any) => Any) & ((Any => { val a: Any }) => Any) => Any | agree-accept |  | agree-accept | same |
| X1A | pos | ok |  | ok : ∀(x : (∀(x : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(x : ∀(x : ⊤) {a : ⊤}) ⊤)) ⊤ | ((Any => Any) => Any) & ((Any => { val a: Any }) => Any) => Any | agree-accept |  | agree-accept | same |
| X2 | pos | ok |  | ok : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) | ({ val a: Any } => { val a: Any }) & ({ val a: Any } => Any) | agree-accept |  | agree-accept | same |
| X2D | pos | ok |  | ok : (∀(x : {a : ⊤}) {a : ⊤}) ∧ (∀(x : {a : ⊤}) ⊤) | ({ val a: Any } => { val a: Any }) & ({ val a: Any } => Any) | agree-accept |  | agree-accept | same |
| X51 | pos | ok |  | ok : ∀(x : {a : ⊤} ∧ {a : {b : ⊤}}) {a : {b : ⊤}} ∧ {v : ⊤} | { val a: Any } & { val a: { val b: Any } } => { val a: { val b: Any }; val v: Any } | agree-accept |  | agree-accept | same |
| X52 | pos | ok |  | ok : ∀(x : {a : {b : ⊤}} ∧ {a : ⊤}) {a : {b : ⊤}} ∧ {v : ⊤} | { val a: { val b: Any } } & { val a: Any } => { val a: { val b: Any }; val v: Any } | agree-accept |  | agree-accept | same |
| A1 | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| AliasRec | neg | error: E045 at 12 |  | rejected: Recursive value a needs type |  | agree-reject |  |  | same |
| AndOne | neg | error: E007 at 7 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| AndOneD | neg | error: E007 at 7 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| B1 | neg | error: E008 at 6 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| CalleeBlockD | neg | error: E081 at 9 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| CalleeOtherD | neg | error: E081 at 9 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| CalleeSelfD | neg | error: E081 at 7 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| CalleeTopD | neg | error: E081 at 8, E050 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| Cyc | neg | error: E045 at 10 |  | rejected: Recursive value a needs type |  | agree-reject |  |  | same |
| Cyc3 | neg | error: E045 at 11 |  | rejected: Recursive value b needs type |  | agree-reject |  |  | same |
| Doubled12 | neg | error: E007 at 21 |  | limit: Recursion limit exceeded |  | refuse-differently |  |  | same |
| E1 | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| E10 | neg | error: E050 at 6, E050 at 6 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| E11D | neg | error: E081 at 7, E081 at 8, E081 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| E3 | neg | error: E007 at 9 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| E4 | neg | error: E007 at 11 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| E8D | neg | error: E081 at 6, E081 at 6 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| Id0D | neg | error: E081 at 7 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| IdTopD | neg | error: E081 at 7 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| IncD | neg | error: E081 at 6 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| J1SA1 | neg | error: E081 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| J2RecUntyped | neg | error: E045 at 8 |  | rejected: Recursive value a needs type |  | agree-reject |  |  | same |
| LetArgD | neg | error: E081 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| LowerD | neg | error: E081 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| MidA | neg | error: E007 at 6 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| PF | neg | error: E007 at 11 |  | limit: Recursion limit exceeded |  | refuse-differently |  |  | same |
| Rd1SA1 | neg | error: E081 at 8 |  | rejected: Missing parameter type |  | agree-reject |  |  | same |
| RecW | neg | error: E045 at 11 |  | rejected: Recursive value a needs type |  | agree-reject |  |  | same |
| Upper | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| UpperD | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| Amb | disagree | ok |  | rejected: The types of a have no least one |  | ours-stricter | scalac types y.a on an intersection as the intersection of the two member types, our typer asks for one least type of a |  | same |
| AndIncD | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | scalac gives the parameter of y => y the union of the two domains of the intersection, our typer checks y => y against the intersection and answers Type mismatch (Gaps: a union of two domains, d2 AndIncD) |  | same |
| CalleeIncD | disagree | ok |  | rejected: Missing parameter type |  | ours-stricter | scalac infers the parameter of x => g(x) from the call in its body, the union of the two domains of g, our typer asks for its type |  | same |
| CalleeProjD | disagree | ok |  | rejected: Missing parameter type |  | ours-stricter | scalac infers the parameter of x => o.a(x) from the call in its body, our typer asks for its type |  | same |
| DepCo | disagree | error: E007 at 10 |  | ok : ∀(x : ∀(x : {A : ⊥ .. ⊤}) x.A) ∀(y : {A : ⊥ .. ⊤} ∧ {a : ⊤}) y.A | ((x0: { type A }) => x0.A) => (x1: { type A; val a: Any }) => x1.A | ours-looser | scalac compares the domain of a dependent function type by equality, DOT contravariantly (Gaps, d3 DepCo) |  | same |
| Mid | disagree | error: E007 at 8 |  | ok : ∀(x : {A : {a : ⊤} .. {b : ⊤}}) ∀(y : {a : ⊤}) ∀(z : (∀(z : ∀(z : ⊤) x.A) ⊤) ∧ (∀(z : ∀(z : ⊤) {b : ⊤}) ⊤)) ⊤ | (x0: { type A >: { val a: Any } <: { val b: Any } }) => { val a: Any } => ((Any => x0.A) => Any) & ((Any => { val b: Any }) => Any) => Any | ours-looser | scalac checks the argument against Any => { val b: Any }, one function type of the intersection, DOT against Any => y.A, the other (Gaps: an argument at a non-dominant formal, d2 Mid) |  | same |
| Rd1V1 | disagree | error: E007 at 9 |  | ok : ∀(x : ∀(x : {A : ⊥ .. ⊤}) x.A) ∀(y : {A : ⊥ .. ⊤} ∧ {b : ⊤}) y.A | ((x0: { type A }) => x0.A) => (x1: { type A; val b: Any }) => x1.A | ours-looser | scalac compares the domain of a dependent function type by equality, DOT contravariantly (Gaps, refute-d1 V1) |  | same |
| X3 | disagree | error: E007 at 10 |  | ok : ∀(x : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}) (∀(y : {a : ⊤}) ⊤) ∧ x.A | (x0: { type A >: { val a: Any } => { val a: Any } }) => ({ val a: Any } => Any) & x0.A | ours-looser | scalac types the closure at the function part of the expected type, { val a: Any } => Any, which is no y.A, DOT types it { val a: Any } => { val a: Any }, the lower bound of y.A (Gaps: a closure typed at an expected result, d2 X3) |  | same |
| X3D | disagree | error: E007 at 10 |  | ok : ∀(x : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}) (∀(y : {a : ⊤}) ⊤) ∧ x.A | (x0: { type A >: { val a: Any } => { val a: Any } }) => ({ val a: Any } => Any) & x0.A | ours-looser | as X3, for x => x (Gaps: a closure typed at an expected result, d2 X3) |  | same |
| X4 | disagree | error: E007 at 11 |  | ok : ∀(x : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}) (∀(y : {a : ⊤}) ⊤) ∧ x.A | (x0: { type A >: { val a: Any } => { val a: Any } }) => ({ val a: Any } => Any) & x0.A | ours-looser | as X3, for a closure whose body is a block (Gaps: a closure typed at an expected result, d2 X4) |  | same |
| CapsName | outside | ok |  | outside 8:6: `caps` names the package of `caps.any` in Scala: rename it |  | outside | S-13, `caps` as a name, which Scala reads as the package of `caps.any` (rule 7) |  |  |
| CycAlias | outside | error: E140 at 8 | no code at 8 | outside 8:16: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | S-16, two aliases on a cycle (rule 11) |  |  |
| CycUpper | outside | error: E140 at 8 | no code at 8 | outside 8:16: illegal cyclic type reference: the upper bound of `A` refers back to `A` (scalac E140) |  | outside | S-16, upper bounds on a cycle outside function types (rule 11) |  |  |
| DepUnused | outside | error: E051 at 10 |  | outside 8:30: the parameter `x` does not occur in the result: write `S => T` |  | outside | S-14, a dependent binder the result does not use (rule 6) |  |  |
| DollarName | outside | ok |  | outside 8:6: names with `$` are outside the subset |  | outside | S-13, a name with `$` (the lexer) |  |  |
| DupBlock | outside | error: E161 at 10 |  | outside 10:11: `y` is already defined in this block (scalac E161) |  | outside | S-13, two vals of one name in one block (rule 8) |  |  |
| DupLit | outside | error: E120 at 11 |  | outside 11:13: conflicting definitions of `a` in one object literal (scalac E120) |  | outside | S-13, two members of one name in one literal (rule 8) |  |  |
| DupRef | outside | error: E120 at 8 |  | outside 8:27: conflicting definitions of `a` in one refinement (scalac E120) |  | outside | S-13, two fields of one name in one refinement (rule 8) |  |  |
| DupRefType | outside | error: E161 at 8, E007 at 10 |  | outside 8:42: `A` is already defined in this refinement (scalac E161) |  | outside | S-13, two type members of one name in one refinement (rule 8) |  |  |
| E2 | outside | error: E140 at 11, E140 at 13 | no code at 13, no code at 13 | outside 11:14: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | S-16, a type alias on a cycle (the reader's rule 11) |  |  |
| E2D | outside | error: E140 at 11, E081 at 12, E140 at 13 | no code at 13, no code at 13 | outside 11:14: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | S-16, a type alias on a cycle (the reader's rule 11) |  |  |
| E2obj | outside | error: E140 at 10, E140 at 12 | no code at 12, no code at 12 | outside 10:12: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | S-16, a type alias on a cycle (the reader's rule 11) |  |  |
| E7 | outside | error: E140 at 10, E140 at 12 | no code at 12 | outside 10:12: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | S-16, a type alias on a cycle (the reader's rule 11) |  |  |
| KwDo | outside | error: no code at 8, E018 at 8, E040 at 8, no code at 9 |  | outside 8:6: `do` is outside the subset |  | outside | S-13, a hard keyword as a name (the parser) |  |  |
| KwTrue | outside | error: no code at 9 |  | outside 9:8: `true` is outside the subset |  | outside | S-10 (XV0), `true`, `false` and `macro` are reserved |  |  |
| LP | outside | error: E140 at 9 | no code at 8, no code at 9 | outside 9:18: illegal cyclic type reference: the lower bound of `B` refers back to `B` (scalac E140) |  | outside | S-16, a lower bound on a cycle (the reader's rule 11) |  |  |
| LayB | outside | ok |  | outside 9:7: a continuation line must follow one of = => -> ( { , : & <: >: |  | outside | S-10 rule 2, a continuation line after a line that can end a statement |  |  |
| LayD | outside | ok | no code at 9 | outside 9:5: line is indented too far to the left |  | outside | S-10 rule 1, a statement left of the block's column |  |  |
| LayE | outside | ok | E129 at 9 | outside 9:7: a continuation line must follow one of = => -> ( { , : & <: >: |  | outside | S-10 rule 2, a more indented name after a statement |  |  |
| LayF | outside | ok |  | outside 9:7: a continuation line must follow one of = => -> ( { , : & <: >: |  | outside | S-10 rule 2, a leading `.` on a more indented line |  |  |
| LayG | outside | ok | no code at 9 | outside 9:7: a comment before the first token of a line is outside the subset |  | outside | S-10 (XV0), a comment before the first token of a line |  |  |
| LayI | outside | error: E006 at 10 |  | outside 10:7: a continuation line must be indented at least as far as the continuation line before it |  | outside | S-10 (XV0), a continuation line left of the one before |  |  |
| LayN | outside | ok | E129 at 9 | outside 9:8: `;` on a continuation line is outside the subset: start the next statement on its own line |  | outside | S-10 (XV0), `;` on a continuation line |  |  |
| LayR | outside | ok |  | outside 7:31: the first statement after `{` goes on the next line, indented |  | outside | S-10 rule 1, a statement on the line of its `{` |  |  |
| LitArg | outside | ok |  | outside 9:9: an object literal needs a written type: write `(new Object { … }: T)` |  | outside | S-12, a literal as an argument (rule 10) |  |  |
| LitOuterBare | outside | ok |  | outside 10:20: `a` is a member of an enclosing object literal: members are named through a path |  | outside | S-13, a bare name of a member of an enclosing literal, in an inner one (rule 3) |  |  |
| LowerType | outside | ok |  | outside 8:16: the type member `a` starts lower case: type members start upper case |  | outside | S-13, a type member that starts lower case (rule 7) |  |  |
| M1 | outside | error: E007 at 12 |  | outside 12:29: `a` names the member of the enclosing object here, as in Scala: rename the variable |  | outside | S-13, a variable hidden by a member of an enclosing object (rule 2) |  |  |
| M2 | outside | ok |  | outside 13:15: `a` is a member: members are named through a path, write `this.a` |  | outside | S-13, a bare member name in a literal (rule 3) |  |  |
| N3 | outside | error: E007 at 9 |  | outside 8:16: a member named `Nothing` hides the type `Nothing` in Scala: rename it |  | outside | S-13, a member that hides `Any`, `Nothing` or `Object` (rule 7) |  |  |
| NestLitThis | outside | error: E008 at 10 |  | outside 10:62: value b is not a member of the object literal (scalac E008) |  | outside | S-13, `this.b` where the inner literal declares no b (rule 5) |  |  |
| NestRefThis | outside | error: E008 at 8 |  | outside 8:62: type C is not a member of the refinement (scalac E008) |  | outside | S-13, `this.C` where the inner refinement declares no C (rule 5) |  |  |
| NotFound | outside | error: E006 at 9 |  | outside 9:7: `y` is not in scope |  | outside | S-13, a name bound nowhere (rule 1) |  |  |
| ObjMember | outside | error: E164 at 9 |  | outside 9:11: `toString` is a member of every Scala object: rename it |  | outside | S-13, a member of every Scala object as a name (rule 7) |  |  |
| P4 | outside | error: E008 at 7 |  | outside 7:71: type B is not a member of the refinement (scalac E008) |  | outside | S-13, this.B where the refinement declares no B (the reader's rule 5, before the member check of S-17) |  |  |
| RefBare | outside | ok |  | outside 8:39: `a` is a member of the enclosing refinement: members are named through a path |  | outside | S-13, a bare member name in a refinement (rule 3) |  |  |
| RefMember | outside | error: E008 at 9 |  | outside 9:34: `a` names the member of the enclosing refinement here, as in Scala: rename the variable |  | outside | S-13, a variable hidden by a member of an enclosing refinement (rule 2) |  |  |
| RefOuterBare | outside | ok |  | outside 8:46: `a` is a member of an enclosing refinement: members are named through a path |  | outside | S-13, a bare name of a member of an enclosing refinement, in an inner one (rule 3) |  |  |
| SelfBare | outside | ok |  | outside 13:24: `a` is a member: members are named through a path, write `s.a` |  | outside | S-13, a bare name of a member of an enclosing literal with a self name (rule 3) |  |  |
| SelfMember | outside | error: E120 at 10 |  | outside 11:13: conflicting definitions of the self name and the member `a` (scalac E120) |  | outside | S-13, a self name that is a member's name (rule 8) |  |  |
| SelfTyped | outside | error: E039 at 9 |  | outside 9:20: forward reference: the right side of `y` names it (scalac E039) |  | outside | S-13, a typed val whose right side names it (rule 9) |  |  |
| SoftKw | outside | ok |  | outside 8:6: `open` is outside the subset |  | outside | S-13, a soft keyword as a name (the parser) |  |  |
| ThisProbe | outside | error: E008 at 8 |  | outside 8:38: inside `(x: S) => T` scalac reads `this` as the enclosing object |  | outside | S-13, `this` inside a dependent function type (rule 4) |  |  |
| ThisTop | outside | error: E008 at 8 |  | outside 8:9: `this` outside every refinement and object literal names the wrapper object in Scala |  | outside | S-13, `this` outside every template (rule 4) |  |  |
| TodayProbe | outside | error: E008 at 13 |  | outside 10:9: an object literal needs a written type: scalac types it as Object |  | outside | S-12, a literal as the right side of an untyped val (rule 10) |  |  |
| TopSep | outside | error: no code at 1 |  | outside 1:54: expected a line break or `;`, found `object` |  | outside | S-10 (XV0), the top level takes separators |  |  |
| Undecl | outside | error: E008 at 9 |  | outside 9:13: type B is not a member of the type of x (scalac E008) |  | outside | S-17, a written selection of an undeclared member, found after elaboration |  | same |
| UnderName | outside | ok |  | outside 8:6: names that start with `_` are outside the subset |  | outside | S-13, a name that starts with `_` (the lexer) |  |  |
| UnderOp | outside | error: E081 at 8, E040 at 8, E006 at 9 |  | outside 8:6: a name ending in `_` takes the operator after it in Scala: put a space between them |  | outside | S-13, a name ending in `_` before an operator (the lexer) |  |  |
| UpFun2 | outside | error: no code at 8 | no code at 8 | outside 8:16: illegal cyclic type reference: the upper bound of `A` refers back to `A` (scalac exceeds its recursion limit) |  | outside | S-16, two upper F-bounds on a cycle (rule 11) |  |  |
| UpperField | outside | ok |  | outside 8:15: the field `A` starts upper case: fields start lower case |  | outside | S-13, a field that starts upper case (rule 7) |  |  |
| V08 | outside | error: E045 at 9 |  | outside 9:15: recursive value `x` needs a type: its right side names it (scalac E045) |  | outside | S-13, a val whose right side names it (rule 9) |  |  |
| V18 | outside | error: E039 at 9 |  | outside 9:20: forward reference: `b` is defined later in this block (scalac E039) |  | outside | S-13, a val whose right side names a later val (rule 9) |  |  |
| Wild2 | outside | error: E017 at 9 |  | outside 8:6: placeholders are outside the subset |  | outside | S-13, `_` as a name (the lexer) |  |  |

## Example programs

- same (77): E10src, E1src, E3src, E4src, E8src, E8srcD, E9src, K1src, K1srcA, A1src, B1src, E10tsrc, E11src, E1ssrc, E3ssrc, P5src, R1src, R2src, AliasSrc, AliasSrcD, AndIncSrcD, AndOneSrcD, AndTopSrc, AndTopSrcD, AndTwoSrc, AndTwoSrcD, AscSrc, AscSrcD, CalleeAndSrc, CalleeAndSrcD, CalleeArgSrc, CalleeArgSrcD, CalleeBlockSrcD, CalleeFunGoalSrc, CalleeFunGoalSrcD, CalleeIncSrcD, CalleeLetSrc, CalleeLetSrcD, CalleeOtherSrcD, CalleeProjSrcD, CalleeSelfSrcD, CalleeSrc, CalleeSrcD, CalleeTopGoalSrc, CalleeTopGoalSrcD, CalleeTopSrcD, DomSrc, DomSrcD, E11asrc, E11asrcA, E11srcD, Id0SrcD, IdAscSrc, IdAscSrcD, IdTopSrcD, IncSrcD, LetArgSrcD, LowerSrcD, UpperSrcD, X1src, X1srcA, X2src, X2srcD, X3src, X3srcD, AndIncSrc, AndOneSrc, Doubled12src, Id0Src, IdTopSrc, IncSrc, LetArgSrc, LowerSrc, MidSrc, MidSrcA, PFsrc, UpperSrc
- gap, a written self type has no Scala form: scalac never writes one (plan S-12) (22): E2src, E2srcD, E5src, E6src, E7src, BareProjSrc, BareSrc, E2objSrc, E5srcW, E6srcW, FwdSelfSrc, FwdSrc, RecWSrc, X5Src1, X5Src2, AliasRecSrc, AmbSrc, Cyc3Src, CycSrc, NoDomSrc, StructSrc, X4src
- gap, an object literal needs a written type: scalac types it as Object (plan S-12) (19): E2srcS, E5srcS, E6srcS, E7srcS, AliasRecSrcS, AmbSrcS, BareProjSrcS, BareSrcS, Cyc3SrcS, CycSrcS, E2objSrcS, FwdSelfSrcS, FwdSrcS, NoDomSrcS, RecUSrcS, RecWSrcS, X5SrcS1, X5SrcS2, StructSrcDS
- gap, a μ whose body is not one refinement has no Scala form (plan S-15) (4): Ginsrc, Gsrc, AscMuSrc, AscMuSrcD
- gap, reader: illegal cyclic type reference: the lower bound of `B` refers back to `B` (scalac E140) (1): LPsrc
- gap, a literal ascribed directly reads back as `let ℓ = ν(s. d) in (ℓ : T)` (plan S-12) (4): AscObjSrc, AscObjSrcS, AscTopSrc, AscTopSrcS
- gap, `let x : U = t in u` with `u` not `x` has no Scala form: it would print as `({ val x = t; u }: U)` (plan S-11) (2): BodySrc, BodySrcD
- gap, a μ whose binder does not occur has no Scala form: it would print as its body (plan S-15) (1): P1src
- gap, reader: type B is not a member of the refinement (scalac E008) (1): P4src
