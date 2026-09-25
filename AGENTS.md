# Agent guide

This is the **Juggler–Collatz Mathematical Laboratory**. Keep the two research
programmes, their shared mathematics, and reproducible publication/discovery tools.
The old UI and independent applications are removed; [Git recovery](docs/history.md)
is their home. Do not recreate compatibility packages or a parallel research area.

## Start with the relevant map

| Task | Read first |
|---|---|
| Maintenance, change impact or verification | [Agent workflow](docs/architecture/agent_workflow.md); use `lab.py doctor`, `impact`, and `verify --changed --plan` |
| Research context or dataset provenance | [Research catalogue](docs/architecture/research_catalogue.md); use `lab.py search` and `context` |
| Juggler research or a new branch | [Juggler guide](attacks/juggler/AGENT.md), then the selected dossier |
| Signed Collatz research | [Collatz guide](attacks/collatz/AGENT.md), then its proof map |
| Papers and evidence labels | [Research map](docs/README.md) and [publication record](docs/theory/paper_deposits.md) |
| English-proof dependencies | [Claim graph](docs/architecture/claim_dependencies.md); use `formalpedia.py claim-graph` |
| Lean discovery and names | [Lean guide](docs/architecture/lean_discovery.md); use formalpedia before adding a theorem |
| Sequences and prior art | [OEIS guide](docs/architecture/oeis_discovery.md); use the local OEIS MCP |
| Certified numerical bounds | [FLINT/Arb guide](docs/architecture/certified_numerics.md) and [Arb MCP](docs/architecture/arb_mcp.md); start with `arb_capabilities`, or use `research_engine.intervals` and the paper-specific audit |
| Shared Python code | [Architecture](docs/architecture/overview.md) |

Do not read entire generated indexes, theorem ledgers or journals to find one item.
Use `python tools/lab.py search` and `context` for either programme, `search --kind
obstruction` for negative knowledge, formalpedia's
`search`, `claim`, `show`, and `impact` for Lean, and the branch CLI for Juggler
scaffolding. Search [negative knowledge](docs/negative_knowledge.md) before proposing
a direction. Current mathematical thresholds belong in the application guide and
its canonical proof sources, not in duplicated instructions.

## Working rules

- `bt.*` must never import `research.*` or `research_engine`. Application imports
  are `research.juggler_sequence`, `research.collatz`, `research.syracuse`, and
  `research.collatz_finite_descent`. Shared machinery lives in `research_engine`.
- Preserve concurrent work. Work in your own worktree (`lab.py worktree new`) and
  reach `main` only through `lab.py land`; see the agent workflow. In a shared
  checkout, inspect Git status and the latest commit before editing or staging.
  Commit bounded changes; do not stage unrelated files.
- Tests read committed research evidence. Tests that exercise artifact writers
  must use explicit `tmp_path` destinations; pytest rejects canonical output writes.
- Use the seven evidence labels in `docs/README.md`. A Lean statement must cover
  the English claim before retagging it; finite checks do not prove termination.
- For certified real bounds, use FLINT/Arb with exact integer, rational or string
  inputs; retain exact integer/rational checks where available. Preserve outward
  bounds, treat unresolved comparisons as failures, and scope precision locally.
  High-precision point values are not interval certificates. Numerical bounds
  do not discharge analytic hypotheses or become Lean proofs.
- For a new mathematical direction, emit the triage block in
  [.cursor/rules/methodology.mdc](.cursor/rules/methodology.mdc), including
  `Already killed by?`, and end with `PROMOTE | PARK | CLOSE`. Do not auto-open
  the next branch. This research protocol does not prevent authorized maintenance.
- Edit claims in `docs/claims/<programme>/<topic>.json`; use `formalpedia.py claim <ID>`
  for the source location. Read through `research.claims.load_claims`, then regenerate
  both aggregate ledger views with `tools/render_theorem_ledger.py`. Keep IDs and
  evidence fields unchanged when moving rows. See [claim storage](docs/claims/README.md).
- Keep durable results in dossiers, proof maps, obstruction records and the claim
  ledger. The journal holds at most twelve short decisions; earlier chronology is
  recoverable from Git. Regenerate the obstruction directory with
  `python tools/research_memory.py`; `lab.py check` validates both boundaries.
- Lean names and documentation follow the [Lean guide](docs/architecture/lean_discovery.md).
  No `sorry` or `admit`. Search existing results, compile changes, and check their
  public interfaces. Do not expand the style baseline to excuse new violations.

## Commands from the checkout root

```powershell
python tools/lab.py prepare                              # plan checkout-local setup
python tools/lab.py prepare --apply                       # pinned Python + Lean setup
python tools/lab.py prepare --check                       # verify readiness receipt
python tools/lab.py test                                  # fast suite
python tools/lab.py test -- -n 8 --dist loadfile           # parallel fast suite
python tools/lab.py test -- --runslow                     # long checks, when needed
python tools/lab.py run research.juggler_sequence.branch_index search "contagion"
python tools/lab.py run research.juggler_sequence.branch_index --check
python tools/lab.py run cli.main collatz --help
python tools/formalpedia.py search "preimage mass" --limit 10
python tools/oeis_catalog.py get A094683
python tools/check_paper_c_intervals.py                   # certified numerics; prints only
python tools/render_theorem_ledger.py --check
python tools/lean_style.py
python tools/lab.py build
python tools/lab.py check                                 # references, metadata, manifests
python tools/lab.py doctor                                # local prerequisites
python tools/lab.py verify --changed --plan               # inspect planned gates
python tools/lab.py verify --changed --profile focused --plan  # iteration test selection
python tools/lab.py verify --changed --workers 8          # execute them
python tools/lab.py worktree new <name>                  # own worktree + branch agent/<name>
python tools/lab.py land agent/<name>                    # the only way onto main
```

`lab.py run` and `lab.py test` bind imports and output paths to this checkout,
even when Python has another worktree installed in editable mode. Use these
commands in worktrees. `lab.py build` uses this checkout's `formal/` directory.
Put `--` before pytest options. Target checks to the change before running wider gates.
Use `verify --changed --profile focused` for iteration; inspect its selected tests
and fallback reasons. Run the default full profile before committing or handing off.
Fresh worktrees use `prepare --apply --from <ready-checkout>` to copy compatible
caches as independent files. Install Python, uv, Git and the pinned Lean compiler
first; details and the Python-only profile are in the agent workflow. Refresh the
Python lock explicitly after dependency edits; do not share writable build trees.
Windows commands use PowerShell; environment and registration details are in
[.cursor/rules/environment.mdc](.cursor/rules/environment.mdc).

For new probe outputs, write a `*.research.json` manifest using
`research.experiments.provenance.write_manifest` (included in the Juggler scaffold).
Record the actual scope, parameters and input files after computation; never
invent provenance for historical data. `lab.py check --hashes` verifies file
integrity separately from tests or proof checking.
For producers with explicit output destinations, prefer
[artifact staging](docs/architecture/artifact_staging.md): `lab.py artifacts stage`,
then `inspect` and explicit local `promote`. Source or destination drift blocks
promotion; pending journals require `recover`. Promote before committing.

## Local services and external publication

Formalpedia and the local OEIS MCP are read-only discovery services. The OEIS
corpus stays global; its published comments are available, but pending editorial
discussion and most LFS b-file contents are not. Use `oeis_status` for current
coverage. The [Juggler neighbourhood](docs/problems/juggler_oeis_neighbourhood.md)
has already been swept; do not repeat that search without a new question.

Formalpedia's `formalpedia_mathlib_search` sends the supplied query to public
Loogle. Other discovery tools stay local. Its source matches are not Lean
elaboration; confirm applicability against the installed pinned Mathlib.

The local Arb MCP performs bounded numerical computations in isolated workers.
Use `arb_compare` for tri-state decisions, `arb_production_root` for positive
production sums, `arb_continued_fraction` for certified partial quotients,
`arb_best_approximation` for finite-range Diophantine minima, and
`arb_paper_c_models` / `arb_paper_c_rate` for canonical paper formulas. Keep
exact endpoints and scope; `holds=null` is unresolved. It writes no research
artifacts and never upgrades a claim or Lean proof.

The alphaXiv connector searches and reads arXiv. It is an external service tied
to the owner's claude.ai account, not a repository server: never send it
unpublished results or correspondence, and ask before library or follow changes.
A search miss is not novelty. Record what was read in the
[literature registry](docs/architecture/literature.md#reading-arxiv-through-alphaxiv).

Use Lean LSP or Lean itself for elaboration and proof checking; a source catalogue
is not an axiom audit. External [prove2.me](.claude/skills/prove2me/SKILL.md) is
separate from formalpedia. Ask before public submit or verify.
