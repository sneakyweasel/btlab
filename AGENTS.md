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
| Lean discovery and names | [Lean guide](docs/architecture/lean_discovery.md); use formalpedia before adding a theorem |
| Sequences and prior art | [OEIS guide](docs/architecture/oeis_discovery.md); use the local OEIS MCP |
| Certified numerical bounds | [FLINT/Arb guide](docs/architecture/certified_numerics.md); use `research_engine.intervals` and the paper-specific audit |
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
- Preserve concurrent work. Inspect Git status and the latest commit before
  editing or staging. Commit bounded changes; do not stage unrelated files.
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
- Keep durable results in dossiers, proof maps, obstruction records and the claim
  ledger. The journal holds at most twelve short decisions; earlier chronology is
  recoverable from Git. Regenerate the obstruction directory with
  `python tools/research_memory.py`; `lab.py check` validates both boundaries.
- Lean names and documentation follow the [Lean guide](docs/architecture/lean_discovery.md).
  No `sorry` or `admit`. Search existing results, compile changes, and check their
  public interfaces. Do not expand the style baseline to excuse new violations.

## Commands from the checkout root

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
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
python tools/lab.py verify --changed --workers 8          # execute them
```

`lab.py run` and `lab.py test` bind imports and output paths to this checkout,
even when Python has another worktree installed in editable mode. Use these
commands in worktrees. `lab.py build` uses this checkout's `formal/` directory.
Put `--` before pytest options. Target checks to the change before running wider gates.
Windows commands use PowerShell; environment and registration details are in
[.cursor/rules/environment.mdc](.cursor/rules/environment.mdc).

For new probe outputs, write a `*.research.json` manifest using
`research.experiments.provenance.write_manifest` (included in the Juggler scaffold).
Record the actual scope, parameters and input files after computation; never
invent provenance for historical data. `lab.py check --hashes` verifies file
integrity separately from tests or proof checking.

## Local services and external publication

Formalpedia and the local OEIS MCP are read-only discovery services. The OEIS
corpus stays global; its published comments are available, but pending editorial
discussion and most LFS b-file contents are not. Use `oeis_status` for current
coverage. The [Juggler neighbourhood](docs/problems/juggler_oeis_neighbourhood.md)
has already been swept; do not repeat that search without a new question.

Use Lean LSP or Lean itself for elaboration and proof checking; a source catalogue
is not an axiom audit. External [prove2.me](.claude/skills/prove2me/SKILL.md) is
separate from formalpedia. Ask before public submit or verify.
