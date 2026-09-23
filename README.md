# Juggler–Collatz Mathematical Laboratory

A mathematical research laboratory for the **Juggler map** and the **signed
Collatz maps**. It brings together research papers, exact Python experiments,
Lean 4 proofs, computational certificates, and tools for finding and checking
the results behind a claim.

The work follows questions from exploration through proof or counterexample.
Successful results, conditional reductions, and failed approaches are recorded
with their hypotheses and evidence, so both people and research agents can
continue from what is already known.

## Research

**Juggler.** For a positive integer, the next value is the floor of its square
root when it is even, and the floor of its three-halves power when it is odd:

$$
J(n)=\begin{cases}
\lfloor\sqrt n\rfloor & n\text{ even},\\
\lfloor n\sqrt n\rfloor & n\text{ odd}.
\end{cases}
$$

The programme studies cycle-length bounds, descent certificates, parity
statistics of nested floor powers, and how possible orbit fates propagate
through inverse images. The [Juggler guide](attacks/juggler/AGENT.md) maps the
current results, open inputs, and closed directions.

**Signed Collatz.** The $3n+1$ and $3n-1$ maps are studied through accelerated
odd orbits, valuation itineraries, finite cylinders, and inverse trees. Current
work includes cycle exclusions, ancestor counts, reciprocal mass, and
obstructions to proposed growth arguments. The
[Collatz guide](attacks/collatz/AGENT.md) and
[Lean module map](formal/Problems/Collatz/README.md) lead to the exact statements.

Balanced ternary, exact arithmetic, and shared dynamical machinery support
these two programmes. The [theorem ledger](docs/theory/theorem_ledger.md)
distinguishes written proofs, Lean proofs, finite computations, conjectures,
observations, refutations, and reparameterizations. Conditional results retain
their open assumptions; finite checks establish their stated range.

## Papers and research record

| Paper | Subject |
|---|---|
| [A — Juggler cycle lengths](docs/theory/juggler_finite_dynamics_note.md) | Lower bounds for nontrivial cycles |
| [B — Juggler descent certificates](docs/theory/juggler_parity_discrepancy_note.md) | Five-step descent and parity statistics of nested floor powers |
| [C — Juggler fate contagion](docs/theory/juggler_fate_almost_all_note.md) | Inverse production, contagion, and termination criteria |
| [D — Negative Collatz cycles](docs/theory/collatz_3n_minus_1_m_cycles_note.md) | Exclusion of $m$-cycles for the $3n-1$ map |
| [E — Juggler and signed Collatz](docs/theory/juggler_signed_collatz_note.md) | Exact coding and arithmetic obstructions to transferring results |

These links point to the working manuscripts. The
[publication record](docs/theory/paper_deposits.md) tracks deposited editions,
DOIs, and local revisions separately. Paper sources live in `docs/theory/`;
PDFs and publication kits live in [preprints](preprints/README.md).
Run `python tools/preprints.py --check` to verify the full publication inventory.

For the wider record, start with the [research map](docs/README.md).
[Problem dossiers](docs/problems/) record individual investigations and their
decisions. [Negative knowledge](docs/negative_knowledge.md) records why a route
failed and what would be needed to revisit it.

## Run and verify

From the repository root, with **Python 3.11 or later**:

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
python tools/lab.py run cli.main status
python tools/lab.py run cli.main collatz --help
python tools/lab.py run research.juggler_sequence.branch_index search "contagion"
```

Run a Juggler probe with
`python tools/lab.py run research.juggler_sequence.<branch>` after consulting
its dossier. The Collatz CLI exposes bounded trajectories, inverse trees,
itinerary calculations, and experiment commands.

```powershell
python tools/lab.py test                       # fast Python suite
python tools/lab.py test -- --runslow          # include long checks
python tools/lab.py build                      # retained Lean library
python tools/lean_style.py                     # public Lean names and documentation
python tools/render_theorem_ledger.py --check  # claim ledger consistency
python tools/lab.py doctor                     # local prerequisites
python tools/lab.py verify --changed --plan    # inspect change-aware checks
python tools/lab.py verify --changed           # execute the selected gates
```

The Lean build requires **Lean and Lake through elan**; the versions are pinned
under `formal/`. See the [formalization guide](formal/README.md) for compilation
and axiom audits. Paper-specific build guides and release manifests under
`docs/theory/` describe the additional publication checks.

`lab.py run` and `lab.py test` use this checkout's sources even when another
worktree is installed in editable mode. To parallelize tests, use
`python tools/lab.py test -- -n 8 --dist loadfile`.

The [agent workflow](docs/architecture/agent_workflow.md) explains change impact,
verification scope, and the corresponding read-only Formalpedia MCP tools.

## Find the mathematics

Start with a bounded research lookup across Juggler and Collatz:

```powershell
python tools/lab.py search "mixed descent"
python tools/lab.py context collatz/fibre_sign_coupling --section obstructions
python tools/lab.py check
```

The [research catalogue](docs/architecture/research_catalogue.md) connects
dossiers, claims, source files and output provenance. Its read-only tools are
also available through the existing Formalpedia MCP.

**Formalpedia** searches the current Lean sources by names, statements,
documentation, and linked claims. It also exposes exact declaration lookup
and module dependency inspection through a CLI and a local read-only MCP:

```powershell
python tools/formalpedia.py search "preimage mass" --limit 10
python tools/formalpedia.py status
```

See [Lean discovery](docs/architecture/lean_discovery.md) for naming policy,
search filters, and MCP setup. Proof validation uses Lean and the executable
axiom audits.

The **local OEIS MCP** searches sequence terms, published comments, formulas,
and references, and connects entries to mentions in the laboratory. Its corpus
and index are installed separately; follow the
[OEIS setup guide](docs/architecture/oeis_discovery.md). Once indexed:

```powershell
python tools/oeis_catalog.py get A094683
python tools/oeis_catalog.py search "Collatz"
```

Agents should start with [AGENTS.md](AGENTS.md), choose the relevant application
guide, and search the existing results before opening a new direction. The
[research method](docs/methodology.md) defines the exploration and decision process.

## Repository map

| Location | Purpose |
|---|---|
| `src/research/juggler_sequence/` | Juggler computations, probes and certificates |
| `src/research/collatz/`, `src/research/syracuse/`, `src/research/collatz_finite_descent/` | Collatz mathematics and experiments |
| `src/bt/`, `src/research_engine/` | Shared arithmetic and experimental dynamics |
| `formal/` | Lean proofs, supporting libraries, and axiom audits |
| `tests/`, `data/research/` | Executable checks, certificates, and research data |
| `docs/`, `attacks/` | Papers, proof maps, claims, decisions, and agent guides |
| `tools/` | Verification, paper builders, formalpedia, and OEIS discovery |
| `preprints/`, `web/juggler-companion/` | Current PDFs, publication kits, and the Juggler companion website |

See the [architecture guide](docs/architecture/overview.md) for dependency
boundaries. The repository retains its historical `balanced_ternary` name and
`bt` namespaces. Earlier independent projects and the old Python UI are
recoverable from [Git history](docs/history.md).
