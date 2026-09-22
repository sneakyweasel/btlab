# Juggler–Collatz Mathematical Laboratory

Exact arithmetic, Lean proofs and reproducible research on the Juggler map and
the signed Collatz maps. The active programme is Papers A–E and the mathematical
questions supporting them.

Start with the [paper and research map](docs/README.md),
[agent guide](AGENTS.md), and [negative knowledge](docs/negative_knowledge.md).
Published versions and local revisions are distinguished in the
[publication record](docs/theory/paper_deposits.md).

## Working in the lab

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
pytest
python tools/lab.py build
python tools/formalpedia.py search "preimage mass"
python tools/oeis_catalog.py search "surviving Collatz residues"
btlab status
```

The default test collection and theorem search cover Juggler, Collatz and shared
dependencies. `tools/lab.py build` builds every active application Lean module,
including results outside the paper barrels. Use `pytest -n auto --dist loadfile`
for a parallel full run of the active fast suite and `pytest --runslow` to include
long computations.

Research runs the documented loop: explore, distill, prove or refute, decide.
Finite computations and exact theorems have distinct evidence labels. The
[method](docs/methodology.md) and [claim vocabulary](docs/README.md) govern both
applications. A closed direction remains searchable before another attempt.

## Source map

| Location | Purpose |
|---|---|
| `src/research/juggler_sequence/` | Juggler probes, exact arithmetic and certificates |
| `src/research/collatz/` | Collatz arithmetic, codes, cylinders and cycles |
| `src/research/syracuse/`, `collatz_finite_descent/` | Related Collatz implementations and retained negative results |
| `formal/Problems/Juggler/`, `formal/Problems/Collatz/` | Formal research results |
| `bt`, `research_engine`, shared Lean modules | Supporting mathematics and experiment infrastructure |
| `docs/theory/`, `attacks/juggler/` | Papers, claim ledger and research decisions |
| `juggler_review/` | Generated reviewer and publication exports |
| `tools/formalpedia_mcp.py`, `tools/oeis_mcp.py` | Local theorem and prior-art discovery |

Balanced ternary is a supporting library. It is no longer a competing research
programme. Existing package names (`balanced-ternary`, `bt`, `btlab`) and Lean
namespaces remain stable for paper reproducibility.

## Historical work

Independent projects are frozen in the [archive](archive/README.md), outside
the active research scope. Their cited source paths remain available. Use
`--include-archive` for historical CLI commands, tests and builds, or
`--scope archive` for formalpedia search. The original laboratory is recoverable
from the archive revision; no proof or negative result is discarded.

The [architecture](docs/architecture/overview.md) explains dependency boundaries.
The optional UI remains available with `pip install -e ".[ui]"` and `btlab ui`;
its historical explorers are compatibility tools, not a second research agenda.
