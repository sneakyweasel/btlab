# Research discovery and output provenance

The research catalogue derives its records from canonical Juggler and Collatz
dossiers, the claim ledger, current source paths, existing Juggler aliases, and
negative knowledge. It reads the working tree and never rewrites an index.
The existing Juggler branch CLI remains available for probe scaffolding and
its more detailed source inventory, including support modules without dossiers.

## Find a question before reading broadly

```powershell
python tools/lab.py search "mixed descent" --programme juggler
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

Context sections are `overview`, `claims`, `sources`, `data`, `obstructions`,
`questions`, `commands`, and `papers`. The overview supplies section counts.
Search includes dossier text and associated claim statements, prioritizing
IDs and titles. Follow `next_offset` and supply `--snapshot` on subsequent
pages; a changed source snapshot is rejected. Limits are 1–30 items per page.
Excerpts disclose truncation; read the cited file for the complete argument.

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

The [v1 JSON schema](../../data/schemas/research-output-v1.schema.json) defines
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
Hashes identify exact bytes. They do not establish a theorem, a successful
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
