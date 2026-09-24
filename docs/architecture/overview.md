# Laboratory architecture

The laboratory contains Juggler and signed Collatz research, their mathematical
dependencies, and publication/discovery tooling.

```text
cli                         Collatz commands and laboratory status
research.juggler_sequence    Juggler research
research.collatz            signed Collatz research
research.syracuse            Syracuse experiments
research.collatz_finite_descent  finite descent experiments
research_engine             shared exact experimental dynamics
bt                          shared balanced-ternary arithmetic
```

`bt` must not import `research` or `research_engine`. Mathematical research must
not import a UI. The Streamlit UI, unrelated applications and their entry points
are removed. The Juggler companion website remains in `web/juggler-companion/`.

`research.experiments` provides shared table schemas and writers;
`research.open_problems` lists the four applications. `research.conjectures`
and `research.literature` read their supporting registries. These are infrastructure,
not additional research programmes.

`research.repository` owns checkout-bound, read-only Git queries and batched
committed-blob reads for discovery, provenance and validation. Callers keep their
own error semantics: an unavailable revision cannot become a clean audit.
Git mutations remain explicit in preparation and other authorized workflows.

The [research catalogue](research_catalogue.md) connects canonical dossiers,
claims, source files, data, obstructions, and verification commands across both
programmes. It is a live derived view, not another manually maintained ledger.
New outputs use versioned provenance sidecars; `python tools/lab.py check`
validates references and metadata without running mathematical computations.

The [agent workflow](agent_workflow.md) prepares each checkout independently.
`tools/lab_prepare.py` owns the Python lock and readiness receipt;
`tools/lab_dependencies.py` materializes pinned Lean packages and copies caches.
`tools/lab_verify.py` runs checks against recorded source, Git and runtime state.
`tools/lab_selection.py` selects explicit focused iteration tests from import and
claim associations, with conservative full-suite fallbacks. The default full
verification profile remains the acceptance gate.
Managed environments, build outputs and scratch files remain in `.build/`.

[Certified numerics](certified_numerics.md) uses FLINT/Arb through
`research_engine.intervals` for rigorous real enclosures, definite comparisons,
and positive-production root brackets. The Paper C audit records exact rational
endpoints and run provenance; its finite numerical guarantees do not establish
the open analytic hypotheses.

The [Arb MCP](arb_mcp.md) separates the bounded AST language in
`research_engine.arb_expressions`, one-request computation in `tools/arb_worker.py`,
and stdio transport / worker deadlines in `tools/arb_mcp.py`. Workers bind this
checkout, isolate global FLINT precision, and reuse the canonical Paper C formulas.

`research.claims` loads and validates canonical topic files in `docs/claims/`.
The reader preserves each row, reports its file and JSON pointer, and shares
proof-route validation from `research.claim_dependencies` across CLI, MCP and gates.
The combined JSON and Markdown ledger are generated exports; discovery reads
topic sources directly. See [claim storage](../claims/README.md).

`research.knowledge` reads the canonical obstruction records in
`docs/negative_knowledge/` for the catalogue and branch discovery. The compact
Markdown directory is derived with `tools/research_memory.py`; full arguments
are stored once in those records. The journal contains at most twelve recent
decisions, with older chronology recoverable from Git.

The [agent workflow](agent_workflow.md) adds checkout-scoped diagnostics,
static change impact, and explicit verification through the same lab CLI and
read-only MCP. Juggler's stable directory constants live in `lean_paths.py`;
changing module registrations and layer order live in `lean_registry.py`.

Formalpedia's entry point is `tools/formalpedia.py`. Its implementation lives in
`tools/formalpedia_core/`, split by responsibility:

| Modules | Responsibility |
|---|---|
| `workspace`, `identities`, `source` | Checkout paths, exact identities and live source inventory |
| `graph` | Lean imports and paper-root reachability |
| `matching`, `verdicts`, `reports` | Local claim matching, recorded advisory evidence and reports |
| `advisory` | Explicit optional external review clients and jobs |
| `semantic_common`, `semantic_store`, `semantic_query` | Freshness, immutable module storage and read-only compiled queries |
| `semantic_build` | Explicit Lean compilation/export and atomic publication |
| `cli` | Command dispatch and explicit artifact writers |

`tools/formalpedia_catalog.py` joins live source discovery to compiled records;
`tools/formalpedia_mcp.py` exposes the read-only services. MCP import paths do not
load compiler orchestration or external review clients. The small `build`,
`reachable` and `paper_surface` exports on `formalpedia.py` preserve the current
publication probe interface. New internal consumers import the owning module.
See [semantic discovery](lean_semantics.md) for storage and migration details.

The retained historical Paper B numerical audit has a small public entry point,
`research.juggler_sequence.paper_b_audit`. Its implementation is in
`paper_b_audit_core/`; it checks the dated 2026-09-04 manuscript, not the current
conditional publication. Existing probe names and the explicit CLI still work.
New internal consumers should import the module that owns their calculation:

| Audit modules | Responsibility |
|---|---|
| `numeric_objects`, `identities`, `interpolation` | Numerical objects and exact identity instruments |
| `censuses`, `precision_bounds`, `standing` | Finite samples, precision bounds and standing estimates |
| `exponents`, `budgets`, `block_ranges` | Exact exponent bookkeeping and operating budgets |
| `kernels`, `derivatives`, `operating_caps` | Kernel measurements, derivatives and admissible ranges |
| `remainders`, `sharpness` | Remainder bounds and constant sharpness |
| `provenance`, `printed_thresholds`, `manuscript_bounds` | Source consistency and printed claim checks |
| `report` | Explicit aggregate run and report writer |

These numerical checks retain their original evidence limits. Importing the
public API does not run the aggregate probe or regenerate research artifacts.

The prefix-count companion keeps its public API and CLI at
`research.juggler_sequence.paper_b_prefix_count`. Its implementation lives in
`paper_b_prefix_count_core/`, with one-way imports between these responsibilities:

| Prefix-count modules | Responsibility |
|---|---|
| `rates`, `counting` | Rates, exact integer counts, biased measures and density ceilings |
| `barrier_profiles`, `barrier_operators` | Finite profiles, rational barriers and update operators |
| `killed_walk`, `quasi_stationary` | Harmonic transforms, relaxation, tail spectra and prefactors |
| `staircase` | Least-peak staircase and its jumps |
| `word_geometry`, `screening` | Exact defect exponents, branching and screening conditions |
| `analytic_bounds`, `carry` | Differencing budgets, composite phases and exact carry identities |

The corresponding regression suite is in
`tests/research/juggler_sequence/paper_b_prefix_count/`, split by mathematical
topic. `test_publication.py` checks the historical manuscript and ledger links;
the numerical and exact-identity checks live beside their topic. Individual
expensive experiments retain `slow` markers and run in CI with `--runslow`.
Small identities and metadata checks run in the default fast suite. No experiment
range or evidence label changes as a result of this split.
The branch index accepts an owned test directory and follows its individual
test files when associating claims, so splitting a suite retains discovery links.

Collatz outputs live in `data/research/collatz/`, including finite-descent and
Syracuse records. CLI writers resolve this location from their source checkout,
so running a command elsewhere does not create another output tree. Generated
`raw/`, `derived/`, and `reports/` subdirectories are ignored; curated evidence
and archived YAML records remain tracked.

Lean modules are retained through Juggler/Collatz imports and current ledger
citations, including their transitive dependencies. The library barrels contain
only retained imports. Build with
`python tools/lab.py build` or `lake build` in `formal/`; test with `pytest`.
Paper-pinned mathematical sources and the Lake package configuration remain stable.

Earlier sources are recoverable from [Git history](../history.md).

Local generated state belongs in the ignored `.cache/` (Formalpedia and Python
tool caches) and `.build/` (paper builds and other disposable build output).
Pytest, Hypothesis, Ruff, and mypy use subdirectories of `.cache/`; ordinary
pytest temporary files use the system temporary directory.

The hidden configuration directories remain part of the working laboratory:
`.github/` holds CI, `.cursor/` holds research rules and skills, and `.claude/`
holds research skills and the companion website launcher. Local Git worktrees
can also live under `.claude/worktrees/`; manage them with Git rather than
deleting that directory. `.vscode/` contains optional local Lean editor settings.
