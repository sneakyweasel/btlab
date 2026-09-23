# Juggler–Collatz Mathematical Laboratory

Exact computation, Lean proofs and reproducible research on the Juggler map and
the signed Collatz maps. Start with the [research map](docs/README.md),
[agent guide](AGENTS.md) and [negative knowledge](docs/negative_knowledge.md).

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
python tools/lab.py test
python tools/lab.py build
python tools/formalpedia.py search "preimage mass"
python tools/oeis_catalog.py search "surviving Collatz residues"
btlab status
btlab collatz --help
juggler-atlas --help
```

Juggler probes run as `python tools/lab.py run research.juggler_sequence.<branch>`.
Use `python tools/lab.py test -- --runslow` for long checks and
`python tools/lab.py test -- -n 8 --dist loadfile` for parallel runs.
These commands select this checkout even when another worktree is installed. Direct `lake build` in `formal/` also builds the retained library.

| Location | Purpose |
|---|---|
| `src/research/juggler_sequence/` | Juggler computations, probes and certificates |
| `src/research/collatz/`, `syracuse/`, `collatz_finite_descent/` | Collatz mathematics and experiments |
| `src/bt/`, `src/research_engine/` | Shared dependencies used by these applications |
| `formal/` | The active Lean results and their transitive dependencies |
| `docs/theory/`, `attacks/juggler/` | Papers, claim ledger and research decisions |
| `juggler_review/` | Publication kits and reviewer exports |
| `web/juggler-companion/` | Juggler companion website |
| `tools/` | Paper builders, theorem discovery and local OEIS MCP |

The Python UI and independent research projects have been removed.
Earlier work is recoverable from [Git history](docs/history.md).
Package names and mathematical namespaces remain stable.
