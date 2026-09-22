# Local OEIS discovery

The OEIS MCP provides local prior-art search over a dated export of the OEIS.
It searches published comments, formulas, references, programs and names, and
matches exact stored integer terms. It also finds references in the laboratory's
papers, dossiers, theorem ledger and Lean declaration docstrings.

## Sources and provenance

The primary input is the committed `seq/` tree of the local `oeis/oeisdata`
mirror. Each A-number retains its tagged fields, source-line numbers, entry
revision, content hash, OEIS URL and link to the exact Git snapshot.
The initial index covers **399,397 full entries and 17,755,028 stored terms**
from export `2026-09-20T03:00:19-04:00`, commit
`9cee00061c60192aafbc74726ce4a83ca7040d81`. Rebuilding may change those counts;
`oeis_status` reports the actual indexed snapshot.

The bulk `names.gz` and `stripped.gz` downloads remain available separately.
They are not silently mixed with the full-record snapshot. This avoids joining
content from different export times without recording that distinction.
The index covers `%S`, `%T` and `%U` terms, not the additional terms in b-files.
`oeis_bfile` identifies missing files and Git LFS pointers and reads locally
available content. It never downloads a file. Supplementary working files have
separate provenance from the committed entry snapshot.

Published `%C` comments are present. Pending edits and editorial discussions
are not part of this export. Programs and HTML links are retained as source
data; the service never runs a program or follows a link.

OEIS content is copyright the OEIS Foundation and licensed under CC BY-SA 4.0.
Results carry attribution and source links. The generated SQLite database stays
in ignored `data/external/`; it is not vendored into the laboratory's Git history.
See the upstream [format description](https://oeis.org/eishelp1.html) and
[mirror documentation](https://github.com/oeis/oeisdata).

## Install and build

```powershell
python -m pip install -r tools/requirements-formalpedia.txt
python tools/oeis_index.py --mirror C:/Users/phili/Desktop/oeisdata
python tools/oeis_catalog.py status
python tools/oeis_mcp.py
```

Defaults are `../oeisdata` for the mirror and
`data/external/oeis/catalog.sqlite3` for the index. `OEIS_MIRROR` and
`OEIS_DATABASE` override those paths. The builder also accepts `--database`
and `--revision`. It streams a Git archive without extracting it, writes a
temporary database, validates both search indexes and SQLite integrity, then
atomically publishes it. A failed build preserves the previous database.
Source files and Git refs are never changed. Updating the local mirror is a
separate, deliberate operation; rebuilding itself needs no network.

The MCP opens SQLite in read-only mode. It does not rebuild on startup or query,
and a missing index produces an actionable error. Query connections are short
lived, so a replaced index is picked up on the next request. On a platform that
blocks replacement while a reader is active, let the request finish and retry
the build. Pagination must restart if the returned snapshot changes.

The initial full index occupies about 2 GB. Building indexes signed decimal
tokens using FTS5 and verifies every numerical candidate against its original
integer strings; hash collisions cannot create a reported numerical match.
Text retrieval uses [SQLite FTS5](https://www.sqlite.org/fts5.html) with ranked
results, field filters, phrases, Boolean queries and proximity queries.

## MCP tools

| Tool | Purpose |
|---|---|
| `oeis_get` | Full entry fields, published comments and exact source provenance |
| `oeis_search` | Ranked text search across names, comments, formulas and references |
| `oeis_terms` | Stored terms with exact decimal values and original OEIS indices |
| `oeis_match_terms` | Verified prefix, contiguous-run or ordered-subsequence matches |
| `oeis_neighbors` | Incoming and outgoing cross-references or wider textual mentions |
| `oeis_lab_links` | Live paper, dossier, ledger and Lean references |
| `oeis_bfile` | Local supplementary content or explicit missing/LFS-pointer status |
| `oeis_status` | Coverage, parse issues, export date and local snapshot freshness |

All eight tools have structured outputs and read-only annotations. Resources
`oeis://guide` and `oeis://status`, plus the `investigate_sequence` prompt,
provide the discovery workflow. Tools use bounded pages and SQL time budgets.
Large entry fields are split into numbered chunks without dropping text.
Follow the returned continuation rather than assuming the first page is all
the evidence. Numerical continuations validate both the query and the snapshot.

Register a stdio server using an absolute Python interpreter and an absolute
path to `tools/oeis_mcp.py`. A portable template is provided in
[oeis_mcp.example.json](../../tools/oeis_mcp.example.json). For Codex:

```text
codex mcp add btlab-oeis --env PYTHONUTF8=1 -- <absolute-python> <absolute-server-script>
```

Reconnect the client after configuration changes. This uses the same installed
MCP SDK as formalpedia and needs no API key or remote OEIS endpoint.

## Matching accurately

Supply terms as decimal **strings**, including their signs. This preserves
integers above JavaScript's exact numeric range. Floating point, exponent
notation and fractional inputs are rejected.

- `prefix` begins at the first stored term, which need not have index zero.
- `contiguous` finds consecutive stored terms and reports their positions.
- `subsequence` permits gaps but preserves order and repeated-term multiplicity.

Every result reports the first matching positions and, when known, their OEIS
indices using the entry's first offset. This is a finite data comparison.
Read the definition and compare further independently computed terms before
asserting a mathematical identity. Missing longer b-files limit a negative
search result. A miss cannot establish novelty.

Transformations are explicit: identity, differences, partial sums or negation,
followed by an optional integer multiplier and additive constant. The returned
searched terms and operation order make it clear what actually matched. The
service never guesses a transformation and silently presents it as identity.

For example, the first six Juggler-map terms match both A094683 and A094685;
the short prefix does not distinguish their definitions. Likewise, the lab's
selected odd counts match positions within A206788 rather than a contiguous
run. These are regression examples, not new mathematical discoveries.

## Connect to laboratory knowledge

`oeis_lab_links` searches the live working tree. Its references have a separate
snapshot from OEIS. Declaration links come from their own docstrings or source
headers and include a namespace and module for `formalpedia_show`. An arbitrary
mention elsewhere in the same Lean file is not attributed to a theorem.
Ledger references preserve the recorded claim tag without upgrading it.

Before exploring a direction, inspect matching dossiers and negative knowledge.
The [Juggler OEIS neighbourhood](../problems/juggler_oeis_neighbourhood.md) has
already been swept. Use formalpedia and Lean to inspect hypotheses and verify
proofs; OEIS references do not discharge those obligations.

CLI examples:

```powershell
python tools/oeis_catalog.py search "surviving Collatz residues"
python tools/oeis_catalog.py get A076227
python tools/oeis_catalog.py terms A094683
python tools/oeis_catalog.py match "0,1,1,5,2,11" --mode prefix
python tools/oeis_catalog.py neighbors A076227
python tools/oeis_catalog.py bfile A094683
```
