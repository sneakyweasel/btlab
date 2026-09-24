# Change-aware agent workflow

Start with the programme guide and a bounded catalogue lookup. Before editing,
inspect Git status so another agent's work remains separate. The existing lab
CLI connects environment discovery, change impact, and executable checks:

```powershell
python tools/lab.py doctor
python tools/lab.py doctor --probe
python tools/lab.py impact --path src/research/juggler_sequence/lean_registry.py
python tools/lab.py verify --changed --plan
python tools/lab.py verify --changed --workers 8
```

## Prepare an isolated checkout

Python 3.11 or newer, `uv`, Git 2.45 or newer, and the compiler named in
`formal/lean-toolchain` must already be installed. Preparation does not select a
different compiler or modify global Python packages. Start inside the checkout:

```powershell
python tools/lab.py prepare                            # read-only plan
python tools/lab.py prepare --apply --from C:/path/to/another/checkout
python tools/lab.py prepare --check                     # probe readiness
```

`--apply` creates `.build/python`, installs the hash-pinned
`tools/requirements-lab.lock`, checks out exact Lake package revisions, builds
the active Lean graph and refreshes compiled Formalpedia records. Later
`lab.py` commands select that environment and bind imports to this checkout.
Use `--profile python` for Python-only setup; it does not certify Lean readiness.
`--offline` forbids package downloads; cached Python archives and compatible
local Lean dependencies must already be available. Without `--from`, full
preparation fetches the repositories recorded in the Lake lock.

A donor must have the same Lean toolchain and Lake lock. Compatible caches are
copied as ordinary independent files; neither build trees nor Git object stores
are shared through writable links. Lake still validates/rebuilds local targets.
Dirty or incorrectly pinned destination packages cause a failure, never a reset.
Cache copies can require several GB. A failed copy remains unpromoted in the
selected checkout's `.build/preparation/`; logs explain the failure.

The readiness receipt records the Python package inventory, lock digest, Lean
source inventory and local object hashes. `prepare --check` probes actual package
revisions and Python inventory, and rejects changed sources or objects. `doctor`
includes the same preparation report (`--probe` checks installed state). The
reported MCP command uses this environment and an explicit checkout root; setup
does not change app configuration. Readiness is separate from tests and theorem
axiom audits. It never upgrades mathematical evidence.

Dependency changes require an explicit `python tools/lab.py prepare --refresh-lock`,
review of both lock files, and another `prepare --apply`. Ordinary preparation
never updates dependency versions. CI uses this lock too. Per-run logs and
receipts stay in `.build/preparation/`, with download archives in `.cache/uv/`.

## Inspect and verify changes

`doctor` discovers this interpreter's packages, the locally installed pinned
Lean toolchain, publication executables, and the optional OEIS database. `--probe`
also tries bounded version commands. Neither installs anything or changes global
configuration. Directory presence and executable discovery do not establish a
successful build. The runner binds Python imports, Lean binaries, and temporary
Git ownership exceptions to the selected checkout and its local packages.

Discovery, provenance, publication checks and dependency probes share
`research.repository` for Git reads. Queries remove inherited repository/index
selectors, bind the requested directory (including linked worktrees and bare
mirrors), and disable optional index refresh, filesystem-monitor helpers,
external diff/text conversion and lazy fetching of missing objects. `doctor --probe`
checks Git's no-lazy-fetch capability. Queries do not edit global Git configuration.
Explicit preparation still performs its requested clones/checkouts with normal
mandatory Git locks; the shared child environment removes inherited selectors.

Impact uses content comparisons so timestamp-only changes do not become false
source edits when index refresh is disabled. Historical source reads use exact
committed blobs, unaffected by archive exclusion/substitution attributes. Missing
local history is an error, not an empty successful scan or permission to fetch.
The query API serves fixed internal calls; it is not a sandbox for arbitrary Git
arguments or executable/configuration changes. Use `GIT_OPTIONAL_LOCKS=0` and
`-c diff.autoRefreshIndex=false` for separate read-only Git shell inspections.

`impact` compares HEAD with the working tree, including staged changes,
unstaged changes, deletions, and untracked files. Use `--since <commit>` to
include committed work since a base revision. Repeat `--path` to inspect an
explicit file or directory scope instead. Static imports include both old and
new edges, so deleting a dependency still identifies its consumers. The report
links affected modules to recorded claims, candidate tests, release inventories,
and v1/v2 research manifests. It does not infer theorem-level proof dependencies.
Ignored files are outside Git-based impact; select a specific ignored artifact
with `--path` when investigating it.

Results are paginated with `--limit`, `--offset`, and `--snapshot`. Passing the
previous snapshot rejects pagination across source changes. File lists inside
an item have labelled bounded previews. Snapshots use paths, sizes, and change
times to detect ordinary concurrent edits. Executed verification additionally
compares SHA-256 contents before and after running checks, allowing identical
test-generated report rewrites. It also records Git HEAD and the Python package
inventory, and marks changes to either as stale. A drifted prepared environment
is rejected before gates run. It lists changed paths when a run is stale.
Neither comparison is an atomic execution certificate.

`verify --changed --plan` constructs commands but does not execute them.
`verify --changed` runs the trusted gates generated by that command. It never
executes commands obtained from dossiers, manifests, or saved JSON reports.
The default `--profile full` is the acceptance profile. Use it before committing
or handing off work. To shorten the edit/test loop, explicitly select iteration:

```powershell
python tools/lab.py verify --changed --profile focused --plan
python tools/lab.py verify --changed --profile focused --workers 8
python tools/lab.py verify --changed --workers 8
```

Focused plans report `purpose: iteration`, selected test paths, selection basis
and any full-suite fallback reasons. Each changed file must have a known role or
its own static/recorded test association; a tested file cannot hide an unrelated
untested change. Claim references to test directories include their test modules.
Documentation and claim edits retain structural evidence tests. All research,
publication, lint and Lean gates remain in place. Focused selection is advisory:
unrecorded dynamic imports and file reads can still escape its candidate set.

Changes to shared machinery, package initialization, pytest fixtures, verification
tools, dependencies or configuration use the full suite even when focused mode
was requested. Deletions, parsing uncertainty, unclassified inputs, missing test
associations, empty selections and excessive command lengths also fall back.
Focused test skips make the result incomplete. A passing focused run is feedback
on its selected checks; it does not replace the full acceptance profile.

Checks include research structure and registered artifact hashes, branch
registration, ledger rendering, publication freshness, and appropriate tests.
In the default profile, executable, data, configuration and unknown changes run the full
fast Python suite: static imports cannot account for dynamic imports and file
reads. Documentation-only changes under `docs/` and `attacks/` use integration
and ledger tests. Slow experiments remain excluded. Python changes also run
Ruff; Lean changes add style, affected compilation, and public Juggler consumer
checks with exact allowed axiom sets. Successful Lean build gates also refresh
the selected modules' compiled Formalpedia records through `lab.py build`.
Refresh errors fail the gate; other verification results remain independent.
Ordinary `lab.py build` refreshes the full active graph, while `--module` selects
a smaller scope. Queries and verification plans never build or write these records.
See [semantic discovery](lean_semantics.md) for module freshness and coverage.
Those checks cover their named interfaces,
not every theorem in the library. Paper-specific audits remain authoritative
for each paper's trust boundary.

Each executed check records `passed`, `failed`, or `not_checked`. Missing
prerequisites never pass. The full Python suite also preflights the pinned Lean
compiler and exact, clean dependency revisions because it includes Lean consumers.
Pytest results include skipped counts and reasons;
skipped required consumer checks make verification incomplete. `doctor` uses
`skipped` for absent optional prerequisites. Overall `passed` means the selected
gates completed successfully within their documented scope. `no_changes` means
there was nothing to check. `failed`, `incomplete`, and `stale` exit nonzero;
`stale` means inputs, Git HEAD or the Python environment changed during checks. Details and logs
remain available after failure. Reports and per-run pytest scratch/cache files
live in ignored `.build/lab/<run>/`;
`--timeout` sets the limit for each check.

No command rebuilds a paper, publishes externally, or promotes an evidence label.
If a release gate reports stale inputs, use its canonical build guide. Do not
repair freshness by editing hashes. Run full paper audits and long experiments
when mathematical changes require them.

## Existing MCP, additional read-only tools

Formalpedia exposes `formalpedia_lab_doctor`, `formalpedia_change_impact`, and
`formalpedia_verification_plan`, plus `formalpedia://workflow-guide`.
Discovery does not run version commands through MCP. Plans are paginated,
every check starts `not_checked`, and long command previews are explicitly
truncated. The planner accepts `profile: full` (default) or `profile: focused`;
its pagination snapshot includes the profile and explicit path scope. Selection
lists and fallback reasons have labelled bounded previews. Obtain and execute
complete plans through the CLI. The existing
theorem `formalpedia_impact` remains the Lean import graph API.

## Certified numerical work

For new reports, use [artifact staging](artifact_staging.md) to run a producer
into scratch space, validate its manifests, and explicitly promote a sealed
candidate. Source and destination changes block promotion; backups and a recovery
journal protect interrupted writes. This local workflow does not change evidence
labels or publish externally.

`python-flint` is a required dependency reported by `lab.py doctor` and the
existing `formalpedia_lab_doctor` MCP tool. Use
[the FLINT/Arb guide](certified_numerics.md) for `research_engine.intervals`,
exact inputs, scoped precision, certified comparisons and outward root brackets.
Use separate processes when parallel calculations change FLINT's global context.

`python tools/check_paper_c_intervals.py` runs the current Paper C certificate
without writing files. Add `--output <path>` only when deliberately producing a
new report and its provenance sidecar. The existing `formalpedia_claim` tool can
read ledger ID `J-paper-c-arb-certificates`; the recorded evidence does not rerun
the audit. The dedicated [Arb MCP](arb_mcp.md) exposes bounded expression
evaluation, adaptive comparisons, production roots and canonical Paper C
models/rates. Start with `arb_capabilities`; preserve exact endpoints and never
treat an unresolved comparison as false. Formalpedia remains read-only discovery.
The guides record which expressions are covered and which hypotheses remain open.

A server started before a tooling update may retain its earlier Python code;
restart that server to pick up new dependency checks. The CLI doctor reads the
current checkout immediately. Recorded claims are read from `docs/claims/` through `research.claims.load_claims`.
Claim queries and impact reports include the owning topic file and JSON pointer.
After editing topics, regenerate both ledger exports with
`python tools/render_theorem_ledger.py`; its `--check` gate rejects stale views.

## Stable paths and changing registries

`research.juggler_sequence.lean_paths` contains repository directory constants.
`research.juggler_sequence.lean_registry` contains module registration, layer
order, aliases, and source-inspection helpers. Import only what a consumer needs.
Adding a theorem to the registry therefore does not invalidate a publication
that only uses stable directory paths. Consumers that actually inspect the
registry still depend on it and must record it in their provenance.

See the [research catalogue](research_catalogue.md) for evidence associations
and manifests, and [Lean discovery](lean_discovery.md) for names and proof reuse.

## Test output isolation

Formalpedia tests are divided into `test_formalpedia_source.py`, `graph`,
`matching`, `reports`, and `advisory` in `tests/tools/`. Paper trust assertions
remain in `test_formalpedia.py`, the path cited by the claim ledger. The scoped
`conftest.py` builds a corpus snapshot once per worker and gives each test an
independent copy; it never caches the production source reader. Cache mutation
and CLI writer tests use temporary catalogues. Run the module matching a change
first, then the full affected verification gates.

For independent concurrent tasks, prefer separate Git worktrees. Inspect the
latest commit and status before editing or staging in a shared checkout; commit
only the files belonging to the task. Build outputs, semantic snapshots and test
scratch directories belong to the selected checkout. A worktree must set up its
own pinned dependencies using `prepare --apply` before compiling; do not assume another checkout's build
results establish freshness here.

Formalpedia accepts `python tools/formalpedia_mcp.py --root <checkout>` to bind
one server process to a worktree. The default is the checkout containing the
script. Never switch roots within a serving process. Check the root reported by
`formalpedia_capabilities` when several checkouts are in use.

Tests that mutate Git history or refs create their own temporary repositories.
The MCP transport regression uses an independent fixture checkout and verifies
that queries leave it unchanged. Live catalogue smoke checks are a separate
integration action, so concurrent research edits cannot change test fixtures.

Artifact-writing tests pass `output_root=tmp_path`. The destination retains the
checkout-relative `docs/research/` and `data/research/` layout; mathematical and
Lean inputs still come from the checkout. Omitting the override in an explicitly
invoked probe regenerates canonical artifacts.

Pytest installs a process-local write guard for canonical research reports and
Juggler/Collatz datasets. Reading committed evidence is allowed. Writing it,
even with identical bytes, fails immediately. Child processes do not inherit
Python audit hooks; any subprocess test that generates artifacts must also use
an explicit temporary destination. Regeneration belongs in a deliberate probe
command, outside pytest.

`lab.py test` allocates a unique `.build/tests/<run>/` scratch directory unless
`--basetemp` is supplied explicitly. It does not depend on shared system-temp
ownership or reuse another test run's temporary directory.

Atlas query connections use `read_only=True`, which opens an existing SQLite
store in read-only mode without schema initialization. Atlas builders retain
write access to their explicitly selected data directory. GPU tests pass a
temporary report path to the verifier. New branch scaffolds also support
`output_root` when recording provenance.
