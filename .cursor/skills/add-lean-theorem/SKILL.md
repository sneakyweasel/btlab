---
name: add-lean-theorem
description: Add, reuse or package a Lean theorem supporting current Juggler or signed Collatz research, with exact claim coverage, namespace placement and registration.
---

# Add a Lean theorem

Search formalpedia before adding a result. Inspect the complete statement and
hypotheses, then use Lean or the Lean LSP to check applicability. A source match
is not compilation or axiom-audit evidence. Follow the
[naming policy](../../../docs/architecture/lean_discovery.md).

| Mathematics | Placement and registration |
|---|---|
| Juggler-specific | `formal/Problems/Juggler/`; follow the [Juggler guide](../../../attacks/juggler/AGENT.md) for barrel, layer and paper registration |
| Signed Collatz-specific | `formal/Problems/Collatz/`; import in `formal/Problems.lean` and update its [module map](../../../formal/Problems/Collatz/README.md) |
| Shared dependency | The appropriate retained `BTCalculus`, `Core`, `Representation` or `Operators` module |

Reuse general lemmas rather than duplicating their proof. Keep namespaces
mathematical, temporary helpers private, and document public declarations.
Do not restore unrelated historical libraries to obtain a convenient name.

Compile the changed module first, then `python tools/lab.py build`. Run
`python tools/lean_style.py` and the relevant paper axiom audit when its public
surface changes. Do not silence new violations through the legacy baseline.
No `sorry` or `admit` is permitted; an unfinished proof keeps its earlier
evidence label and explicit remaining obligation.

Use the [ledger workflow](../add-ledger-row/SKILL.md) to record the exact
declarations covering a claim. Preserve publication-pinned paths and rebuild
affected publication kits through their builders, rather than hand-editing mirrors.
