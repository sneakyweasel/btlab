# Research discovery and output provenance

The research catalogue derives its records from canonical Juggler and Collatz
dossiers, [canonical topic claims](../claims/README.md), current source paths, existing Juggler aliases, and
negative knowledge. It reads the working tree and never rewrites an index.
The existing Juggler branch CLI remains available for probe scaffolding and
its more detailed source inventory, including support modules without dossiers.

## Find a question before reading broadly

```powershell
python tools/lab.py search "mixed descent" --programme juggler
python tools/lab.py search "harmonic divergence" --kind obstruction
python tools/lab.py context collatz/fibre_sign_coupling
python tools/lab.py context collatz/fibre_sign_coupling --section obstructions
python tools/lab.py context collatz/fibre_sign_coupling --section claims
python tools/lab.py context juggler/modified_juggler_descent --section commands
```

IDs are programme-qualified dossier stems, such as `juggler/cycle_word` and
`collatz/fibre_mass`. The main Collatz dossier is `collatz/overview`.
Juggler probe aliases resolve to their canonical dossiers. An ambiguous short
name returns candidates; a missing decision stays null. A decision is copied
from the dossier's Decision section, or an explicitly labelled introductory
decision, with its source line and bounded excerpt.

Claim records include `claim_location` (topic path and JSON pointer) so an agent
can edit the owning source directly. Moving a row leaves its ID unchanged.

Context sections are `overview`, `claims`, `sources`, `data`, `obstructions`,
`questions`, `commands`, and `papers`. The overview supplies section counts.
Search includes dossier text and associated claim statements, prioritizing
IDs and titles. Follow `next_offset` and supply `--snapshot` on subsequent
pages; a changed source snapshot is rejected. Limits are 1–30 items per page.
Excerpts disclose truncation; read the cited file for the complete argument.

Negative knowledge lives in individual records under `docs/negative_knowledge/`.
The compact `docs/negative_knowledge.md` directory preserves the previous anchors;
regenerate it with `python tools/research_memory.py` after adding or renaming a
record. `lab.py check` rejects a stale directory and a journal longer than twelve
entries. Keep durable results in their dossiers, proof maps and obstruction
records; use Git for older journal chronology.

`search --kind obstruction` searches every obstruction, including records without
a dossier. Read its `obstruction/<id>` using `context`, with `--section obstructions`
for the argument or `--section sources` for its references. Programme filtering
uses explicit source links; an unclassified record stays visible without that
filter. No decision is inferred from incidental CLOSE/PARK/PROMOTE words.
Ordinary research search also includes the obstructions linked to each dossier.
The MCP search tool exposes the same `kind="obstruction"` option. Both readers
watch record additions, changes and removals when checking pagination snapshots.
The branch index likewise stores every associated heading in `nk_clusters`;
branch search no longer drops additional obstructions after its first match.

Associations disclose their basis: dossier references, filename conventions,
or claim-ledger source/test references. Theory links include both papers and
proof notes. These links do not establish theorem coverage or dependence.
Use `formalpedia_claim` and `formalpedia_show` to inspect exact declaration
references, and Lean to check them. Suggested commands are never executed by
discovery. A missing search result is not evidence of novelty.

## MCP

The existing Formalpedia server also exposes three local, read-only tools:

- `formalpedia_research_search`: bounded research discovery across both programmes.
- `formalpedia_research_context`: one section of one research record.
- `formalpedia_research_check`: paginated structural findings and coverage.

The `formalpedia://research-guide` resource contains this guide. Reconnect an
already-running Formalpedia client once after upgrading the server to discover
the added tools; its configuration and interpreter remain the same.

## New output manifests

The [v2 JSON schema](../../data/schemas/research-output-v2.schema.json) defines
`*.research.json` sidecars. New shared Collatz table writers, report writers,
and finite-descent/Syracuse record writers emit them automatically. New Juggler
probe scaffolds include a `record_outputs` helper; call it after closing files.
Existing Juggler generators can adopt the shared helper incrementally.

Each manifest records the programme and optional canonical research ID, the
actual finite scope, parameters, generation time, Python version, argv, Git
revision and dirty state, and SHA-256/size descriptors for outputs and explicitly
supplied inputs. Source fingerprints cover loaded local Python, project
configuration, and explicitly supplied source files at manifest creation. They
do not attest that already-imported code was unchanged throughout execution.
This is not a complete dependency or environment audit. An empty input list means no additional input
files were declared; it does not establish that there are no dependencies.

Paths are portable and relative to the recorded artifact root or repository.
Raw hashes identify exact bytes. V2 additionally records an explicit UTF-8 text
identity for supported text inputs and sources: only CRLF becomes LF; whitespace,
BOMs, and lone CR bytes are preserved. A representation change is reported, and a
changed text identity still fails input integrity. Outputs always remain byte-exact.
The [v1 schema](../../data/schemas/research-output-v1.schema.json) remains supported
with its original strict byte semantics. Existing hashes are never repinned just
because a checkout uses different line endings. Reproduce an affected computation
deliberately before replacing its record. New shared text writers emit LF.

Neither kind of hash establishes a theorem, a successful
test, or a Lean trust boundary. Missing invocation or Git information is null,
never guessed from the latest commit. CLI runs supply argv; library callers can
use `recording_run` or pass `command` explicitly. Never store secrets in argv.

For a generator that does not yet use the helper, record a **newly completed**
run immediately using `python tools/lab.py manifest --help`, or call:

```python
from pathlib import Path
from research.experiments.provenance import write_manifest

write_manifest(
    Path("data/research/juggler/my_branch/run.research.json"),
    programme="juggler", research_id="juggler/my_branch",
    scope="Exact integer check for starts 1 through 1000; finite verification only.",
    parameters={"limit": 1000},
    command=["python", "tools/lab.py", "run", "research.juggler_sequence.my_branch", "--limit", "1000"],
    outputs=[Path("data/research/juggler/my_branch/result.json")],
    sources=[Path("src/research/juggler_sequence/my_branch.py")],
)
```

The example presupposes an existing dossier and a just-completed generator.
Do not attach today's revision to an old result. Legacy datasets keep their
original metadata and are reported as legacy or unrecorded. Migrate paper
evidence through deliberate reproduction or a documented historical audit.

## One structural validation command

```powershell
python tools/lab.py check
python tools/lab.py check --hashes
```

The first checks duplicate research/claim IDs, evidence tags, referenced claim
files, bibliography fields, standard manifest schemas, artifact existence and
sizes, and canonical research IDs. It reports unresolved dossier links and
missing provenance fields separately. Output is paginated and exit status is
nonzero if any error exists, including errors beyond the displayed page.

`--hashes` additionally streams input, output and source files. Changed input
or output bytes are errors; changed or missing source fingerprints are warnings
about reproducibility. A different repository HEAD alone does not invalidate
an unchanged dataset. Legacy formats are not silently upgraded or certified.

CI runs the structural gate. Tests, compilation, publication release checks,
and mathematical statement review retain their own commands and authority.

For change-aware orchestration, see the [agent workflow](agent_workflow.md).
`lab.py impact` connects Git changes with recorded dependencies;
`lab.py verify --changed --plan` selects trusted checks and exposes its scope.
Execution remains in the CLI. The existing MCP exposes read-only diagnostics,
impact, and verification plans.
