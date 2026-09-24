# Lean naming and theorem discovery

Public declarations are interfaces used by proofs, papers, humans and agents.
Use mathematical names that remain meaningful when a paper is reorganized.
The catalogue and MCP serve the same local discovery API; Lean remains the
authority for elaboration, applicability and proof checking.

Search defaults to Juggler, Collatz and the transitive shared import graph.
Discovery reads only files present in the current checkout; the scope parameter
does not search Git history. Removed mathematics requires a
[historical checkout](../history.md). Exact `show`, claim lookup and dependency
inspection cover the retained library. Build with `python tools/lab.py build`.

## Names and namespaces

Follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
and [Lean namespace guidance](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md).

| Entity | Convention | Example |
|---|---|---|
| Type, class, structure or predicate | UpperCamelCase | `FailureMassLowerBound` |
| Function or value | lowerCamelCase | `logMass` |
| Theorem | Descriptive underscore-separated words, preserving object names | `logMass_growth_of_ooee` |

Name a theorem by its conclusion, adding distinguishing assumptions with
`_of_...`; use established tokens such as `eq`, `le`, `lt`, `iff`, `exists`,
`mem`, and `injective`. A theorem mentioning `logMass` keeps that camel-case
token. Do not apply an all-lowercase regex to every theorem name.

Choose the namespace of the mathematical object or subject. A module is a
physical import unit, not a declaration namespace: `FateScaleAverage.lean`
declares into `Problems.Juggler.ScaleAverage`. Keep implementation helpers
`private` when they do not form a reusable interface. Explicitly justify
exceptions needed for conventional notation, compatibility or publication APIs.

Every new public declaration needs a docstring describing its role. For a
theorem, explain the conclusion and important hypotheses or limitations;
for a specialized result, explain how it differs from its general version.
This documentation requirement is laboratory policy, stricter than requiring
documentation only for selected declarations. Use a `/-! ... -/` module
overview to identify main results and the intended import path.

Avoid canonical public names such as `main`, `helper`, `lemma17`, or
`theorem41`. Paper numbering belongs in documentation and the theorem ledger.
Existing publication wrappers remain valid. Rename one public family at a
time, preserve deprecated aliases while consumers migrate, and recheck the
paper references and Lean build. A name change alone never changes a claim's
proof status.

## Enforced policy

Run `python tools/lean_style.py` before submitting changes. The same check runs
in pytest and CI. It checks public documentation, namespaces, readily decidable
capitalization rules, and generic stage/number names. Naming meaning, theorem
generality and proof quality still need review. Inferred types and escaped
notation are not guessed by an ASCII source linter.

The [baseline](../../data/research/formalpedia/style_baseline.json) records
individual violations at a committed revision, keyed by declaration, file, rule and
statement fingerprint. It does not exempt future declarations or whole files.
Existing debt is visible without requiring a destabilizing bulk rename. Remove
an exemption when its declaration is repaired. Baseline additions require an
explicit review; `--write-baseline COMMIT` is a maintenance operation, never a
routine way to make a failing check pass.

## Search and exact statements

```powershell
python tools/formalpedia.py search "contagion logarithmic mass" --limit 10
python tools/formalpedia.py search "growth" --namespace Problems.Juggler --json
python tools/formalpedia.py show Problems.Juggler.ScaleAverage.FailureMassLowerBound
python tools/formalpedia.py claim J-pressure-scale-average-contagion-transfer
python tools/formalpedia.py impact Problems.Juggler.FateScaleAverage
python tools/formalpedia.py status
python tools/formalpedia.py build --check
```

`claim` returns `claim_location`, the canonical topic path and JSON pointer.
Edit that row and regenerate the combined ledger with
`python tools/render_theorem_ledger.py`. See [claim storage](../claims/README.md).

Search, show, claim, impact and status read the current working tree without
rewriting artifacts. Search combines names, complete source statements,
docstrings and explicitly linked ledger claims. Use namespace, exact module,
kind or ledger filters to narrow results. Private helpers and deprecated names
are hidden from default search but remain available through explicit flags.
Pagination is stable within the returned snapshot; restart if it changes.

The canonical public identity is its fully qualified name. `show` returns all
candidates when a short name is ambiguous and exits nonzero; it never selects
the first file. Independent source modules can declare the same full name;
in that case the catalogue ID includes the module. Use that ID or `--module`
to choose the intended source. A private declaration has a source ID, not an invented public
Lean name. Search excerpts disclose truncation; `show` returns the complete
source header, including default binders and late hypotheses.

`ledger_exact` records only unique declaration references in a row's stated
file. The legacy `ledger` field is a file association, not evidence that every
declaration proves that claim. Even an exact reference is not a new coverage
review. Module import dependencies are likewise labelled as module-level.

Source parsing is not elaboration: macro-generated names, resolved notation,
which section variables a statement actually uses, and private compiler names
require Lean or the Lean language server. A declaration with `variable`,
`include` or `omit` commands in scope lists them in `signature_context` and has
`signature_complete: false`; its header alone omits those binders. The source
`trust` field detects direct markers only: `unmarked` means no `sorry`, `admit`,
`axiom` or `native_decide` in the declaration's text, `compiler` means
`native_decide`, and `open` means an incomplete marker or an axiom. It does not
certify compilation or transitive axiom dependencies.

Executed axiom evidence comes from the committed `formal/AxiomCheck*.lean`
checks and their recorded `.expected` output. `show` attaches a declaration's
recorded answers as `axiom_audits`, `claim` reports `axiom_audit_coverage` for
its declarations, and `python tools/formalpedia.py audits` (MCP
`formalpedia_axiom_audits`) lists missing or stale artifacts and how many exact
ledger declarations no artifact covers. A recorded answer describes the commit
that recorded it; `python tools/axiom_audit.py --check` verifies statically that
each artifact still answers its check, and `--run` reruns every check with Lean
(CI's Lean job does both). To audit a new cited result, add a `#print axioms`
line to the relevant check and record its output with
`python tools/axiom_audit.py --run --write --only <check>.lean`.

`python tools/formalpedia.py ledger-check` (MCP `formalpedia_ledger_check`)
tests the ledger's strongest label. Every `EXACT — LEAN VERIFIED` row must name
its declarations in `decl`; rows that named none on 24 September 2026 are held
in `data/research/formalpedia/lean_verified_without_declarations.json`, which
may only shrink. When a current semantic export exists, each named
declaration's recorded Lean axioms must be the ones the row's `lean_trust`
allows: Mathlib's three for `kernel`, plus `Lean.ofReduceBool`,
`Lean.trustCompiler` and per-use `native_decide` axioms only for declarations
a `mixed` or `compiler` row permits,
and never `sorryAx`. CI's Lean job builds the export and runs the check with
`--require-compiled`. Neither part judges whether a declaration states the
English claim.

The source catalogue indexes this repository only, not Mathlib. Before proving
a general lemma, search Mathlib too. `python tools/formalpedia.py mathlib
"<query>"` (MCP `formalpedia_mathlib_search`) sends a Loogle query (a name, a
type pattern such as `_ * (_ ^ _)`, or a conclusion `|- _`) to the public
Loogle service and checks every hit against the Mathlib pinned in
`formal/lake-manifest.json`: `declared` when the pinned source declares it,
`module_missing` or `not_declared_literally` when it may be absent or generated
at that revision, `unchecked` when the packages are not installed. Loogle
indexes a recent Mathlib, so confirm a hit with `#check` before relying on it.
Only the query text leaves the machine; the service must be reachable
(`loogle.lean-lang.org`). Inside Lean, the pinned `LeanSearchClient` package
provides `#loogle` and `#leansearch`, and `exact?` and `apply?` search the
imported environment offline.
Use the executable Lean audits for those claims. No metadata silently promotes
a theorem or discharges an assumption.

## Optional local reports

For dependencies between English claims, use the [claim dependency guide](claim_dependencies.md):
`python tools/formalpedia.py claim-graph J-paper-b-five-step-density-127 --format markdown`
prints a review graph from the ledger. The read-only MCP equivalent is
`formalpedia_claim_dependencies`. Written routes, open assumptions, incomplete
annotations and optional compiler associations stay distinct. `dag` remains the
module/import graph; neither view certifies English statement coverage.

`build`, `dag`, `propose`, and `review` write reproducible exports under ignored
`.cache/formalpedia/`. Reports read the current sources and ledger, never an older
saved inventory. A fresh clone therefore needs no generated catalogue committed
alongside its Lean sources. `build --check` checks an explicitly generated local
index; it is not a prerequisite for discovery or a freshness gate on Git history.
Status distinguishes a missing, unreadable, stale or current optional export;
none of these changes the live source catalogue.

`jev-coverage --limit 0` writes `.cache/formalpedia/coverage_review.md` and the
proposal digest from retained advice without sending requests or modifying that
evidence. Original verdicts and the reviewed style baseline remain versioned in
`data/research/formalpedia/`; deterministic report copies do not.

## MCP

For compiler-derived types, structural type search, proof dependencies and
snapshot comparisons, use the [semantic discovery guide](lean_semantics.md).
`python tools/lab.py build` and successful verification build gates refresh this
index; `python tools/formalpedia.py semantic build --module <Module>` refreshes a
selected scope. Semantic queries exclude stale modules and disclose coverage while
unrelated current modules stay searchable. `show` combines source and available
compiled records. Live source discovery does not require an export.

Maintenance also uses the [agent workflow](agent_workflow.md): the same MCP
offers `formalpedia_lab_doctor`, `formalpedia_change_impact`, and
`formalpedia_verification_plan`. These are read-only; execute tests and builds
through `python tools/lab.py verify --changed`.

Install `python -m pip install -r tools/requirements-formalpedia.txt` and run
`python tools/formalpedia_mcp.py`. The server uses the official MCP SDK's
stdio transport. Use `--root <checkout>` to read another worktree explicitly;
the root reported by `formalpedia_capabilities` identifies its data source.
The SDK dependency stays on the supported v1 line. Configure a `formalpedia` entry alongside the
existing `lean-lsp` entry in a machine-local `.mcp.json` (it is gitignored).
[The server configuration template](../../tools/formalpedia_mcp.example.json)
uses repository-relative script paths, which work for clients that launch
servers from the checkout root, such as Claude Code's project scope: copy it to
`.mcp.json`. For clients that launch elsewhere, use absolute interpreter and
script paths.
For Codex, register the server using `codex mcp add btlab-formalpedia --env
PYTHONUTF8=1 -- <absolute-python> <absolute-server-script>`; this is a separate
client configuration from `.mcp.json`. See the
[official Codex MCP guide](https://developers.openai.com/codex/mcp).

The eight local Lean tools are `formalpedia_search`, `formalpedia_show`,
`formalpedia_claim`, `formalpedia_impact`, `formalpedia_status`,
`formalpedia_lint`, `formalpedia_axiom_audits` and `formalpedia_ledger_check`; `formalpedia_mathlib_search`
queries Loogle. They return
structured objects, bounded search pages, full statements on demand, explicit
ambiguities, and snapshot identifiers. Guide and status resources and the
`find_existing_result` prompt provide the discovery workflow.

Three additional tools, `formalpedia_research_search`,
`formalpedia_research_context`, and `formalpedia_research_check`, connect both
research programmes to dossiers, data, decisions, and known obstructions. See
the [research catalogue guide](research_catalogue.md). The existing server
configuration is shared; reconnect once to discover newly added tools.

All server tools are read-only and none edits proofs or invokes an external
advisory service. All are local except `formalpedia_mathlib_search`, which
sends its query text to the public Loogle service and is annotated as such. Source-catalogue queries refresh their in-memory
snapshot when files change. Semantic queries use fresh modules from explicitly built
compiler snapshots and never start a build. Use `lean-lsp` to
inspect goals, check a candidate in context, and verify a proof. Reconnect an
MCP client after changing its server configuration.

The companion `tools/lean_lsp_launcher.py` starts the pinned
[Lean LSP MCP](https://github.com/oOo0oOo/lean-lsp-mcp) in uv's isolated tool
environment. The requirements file above also installs `uv`. The launcher
sets this repository's `formal/` project and adds elan's bin directory to the
inherited PATH. Set `ELAN_HOME` when the toolchain lives elsewhere. In Codex,
register it with `codex mcp add btlab-lean-lsp -- <absolute-python>
<absolute-launcher-script>`. It provides goals, hover information, diagnostics,
proof checking, references and Mathlib search alongside formalpedia's local
claim catalogue. Search providers exposed by Lean LSP can be external services;
formalpedia's discovery tools remain local.
