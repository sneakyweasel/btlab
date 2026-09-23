# Formalization architecture

Lean 4 and Mathlib live under `formal/`; the Lake package is
`balanced-ternary-formal`. The retained source consists of Juggler, signed
Collatz and shared mathematics reached by their imports or current ledger claims.

| Source | Role |
|---|---|
| `formal/Problems/Juggler/` | Juggler dynamics, words, cycles, certificates and production |
| `formal/Problems/Collatz/` | Signed maps, cylinders, cycles, ancestor counts and fibre mass |
| `formal/BTCalculus/` | Shared algebra, analysis, counting and dynamical results |
| `formal/Core/`, `Representation/`, `Operators/` | Retained exact arithmetic and representation dependencies |
| `formal/Problems/Engine/` | Shared formal dependencies still used by the applications |

Use the [Juggler registration guide](../../attacks/juggler/AGENT.md),
[Collatz module map](../../formal/Problems/Collatz/README.md), and
[naming/discovery policy](lean_discovery.md). The full local source catalogue
is queried through formalpedia; avoid maintaining another declaration inventory here.

`python tools/lab.py build` builds all retained application modules,
ledger-cited results, their dependencies and library barrels. Direct `lake build`
inside `formal/` also builds the library's default targets. Use a targeted
`lake env lean <file>` while developing a proof.

No `sorry` or `admit` is allowed. Exact claim coverage, source-level trust markers,
successful compilation and executable axiom audits are distinct evidence.
Keep the English hypotheses aligned with the Lean statements and update relevant
paper audits when their theorem surface changes.
