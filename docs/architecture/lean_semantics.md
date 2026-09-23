# Compiler-derived Lean discovery

Formalpedia has two complementary catalogues. Source discovery reads live files
and links declarations to recorded claims. Semantic discovery reads an explicit
export from Lean's compiled environment: fully elaborated types, explicit and
implicit binders, generated/private names, dependencies, and transitive axioms.
Neither catalogue changes an evidence label or judges an English claim's coverage.

## Build and freshness

```powershell
python tools/formalpedia.py semantic build
python tools/formalpedia.py semantic status
# Refresh selected modules while preserving existing coverage:
python tools/formalpedia.py semantic build --module Problems.Juggler.ReturnWordLoss
python tools/lab.py build --module Problems.Juggler.ReturnWordLoss
```

The builder uses the installed pinned compiler, first builds the selected local
modules with Lake, then exports their declarations using Lean itself. The default
selects every retained library source, including standalone application modules.
After compilation, only missing or outdated selected modules are exported. A
current selection skips the exporter. `lab.py build` uses this same workflow for
the active graph; the Lean build gate in `lab.py verify` refreshes the affected
modules and import consumers after successful compilation. A refresh failure
fails that gate. This does not assert that the other verification gates passed.
Plans and every MCP tool remain read-only.
Missing compiler/packages fail with setup instructions. It does not install tools
or change the project configuration. Normal Lake build hooks still run, so this
is an explicit trusted-checkout CLI action, never an MCP query.

Complete snapshots live in ignored `.cache/formalpedia/semantic/`; logs and raw
exports live in `.build/formalpedia/`. A content-addressed immutable snapshot is
published through an atomic `current` pointer. Publication takes a short OS lock
and merges against the latest snapshot, preserving other exporters' coverage.
Deleted modules are pruned on the next refresh; historical snapshots remain.
A failed build or a detected
concurrent edit leaves the previous snapshot intact. Keep a snapshot identifier
before rebuilding if you want a historical comparison.

Local Lean sources, the toolchain pin, Lake configuration/manifest, and exporter
Lean code are hashed. The snapshot schema versions the Python representation;
query-only changes do not invalidate compiled data. Imported compiled object regions are checked by size and
modification time before/after export and on queries. This detects ordinary
concurrent rebuilds; it is not a cryptographic audit of the toolchain or external
packages, nor an atomic certificate of the filesystem. External source edits
require rebuilding those packages. Lean exports the actual module import graph.
Source and object changes invalidate their module and transitive import consumers,
while unrelated modules stay current. Toolchain, configuration and exporter changes
invalidate all recorded modules. New local modules are explicitly unindexed until
selected for export. Changed imports are caught through the importing source.
Missing dependency sources reject builds. Refreshing a dependency alone does not
make its old consumer records current: select the consumers too, or build the full
active graph. Version-1 snapshots remain readable for historical comparisons and
use conservative whole-export freshness until their modules are re-exported.

Status is `current`, `partial` (a mixture of current and stale modules), `stale`,
`missing`, or `unreadable`. Search and dependency queries use only current modules
and report stale/unindexed coverage. A requested stale module or declaration is
rejected with the rebuild command; a stale candidate never makes an ambiguous
short name look unique. Missing, corrupt, and entirely stale indexes reject
semantic queries. Source search remains usable independently. These records are
local discovery artifacts, not a publication prerequisite or a Git artifact.

## Research workflow

1. Use source `search`, `show`, and `claim` to find a result and its recorded role.
   `show` joins source location/docs, exact ledger claims, paper-root reachability,
   and available compiled type/binders/axioms/dependencies, with separate freshness.
   Its canonical public ID is `Module.Name::Fully.qualified.name`.
2. Use `formalpedia_semantic_show` for the optional full AST. Generated declarations
   also resolve through `show`, with explicit absent source records. Private source
   names are never guessed into compiler-generated private identities. Short names
   must be unique. File-level claims and import reachability do not establish that
   a theorem proves a claim or appears in a paper.
3. Use `formalpedia_type_search` with exact constants, a `like` declaration, or an
   AST pattern. Inspect every hypothesis before using a conclusion match.
4. Use Lean LSP to elaborate a proposed application in the actual proof context.
5. Use `formalpedia_dependencies` before changing a definition or theorem.

```powershell
python tools/formalpedia.py semantic search --constant Nat.sqrt --kind theorem
python tools/formalpedia.py semantic show Problems.Juggler.ReturnWordLoss.step --include-ast
python tools/formalpedia.py semantic dependencies Problems.Juggler.ReturnWordLoss.step --direction used_by --depth 2
python tools/formalpedia.py semantic diff <previous-snapshot-id>
```

Names in examples may require the module-qualified ID returned by search.
Search pages default to 20 results, cap at 100, and disclose shortened type
previews. `show` returns the complete statement. Pass the snapshot on later pages
to reject changes during pagination. Query `snapshot` tokens cover both the export
and live module freshness/coverage; they differ from immutable `export_snapshot`
IDs. Use `semantic status`'s `snapshot` or a query's `export_snapshot` for diffs,
and use the query's `snapshot` when fetching its next page.

### Structural patterns

`include_ast=True` exposes a JSON expression tree derived from Lean `Expr`.
Binder names and source metadata are omitted; bound variables use de Bruijn
indices and universe parameters use their positions. The representation retains
binder kinds, constants, universes, applications, lambdas, lets, and projections.
For example, a constant is `["const", "Nat", []]` and an application is
`["app", function, argument]`.

Replace a subtree with `{"hole":"x"}` to match any subtree. Repeating the name
requires the identical subtree. `like` compares an existing elaborated type;
`part="conclusion"` drops its leading binders before comparison. Neither mode
unifies metavariables, unfolds definitions, shifts variables across binders, or
proves applicability. Conclusion matches can have completely different premises.
This is a local structural search, not a replacement for Lean's elaborator.

### Dependencies, axioms, and differences

Type and value edges are separate. Value edges include proof bodies for theorems
and defining expressions for definitions. Reverse traversal finds recorded local
users among current modules; bounded traversal stops at unindexed constants, includes private/generated
helpers, and reports truncation at 10,000 edges. Module imports remain available
through the original `formalpedia_impact` tool.

Lean's `collectAxioms` supplies transitive axiom dependencies. These can include
standard axioms such as `Classical.choice`, `propext`, and `Quot.sound`, as well as
custom axioms. Metadata does not imply axiom-freedom. Imported compiled modules
are trusted as Lean normally trusts imports; the exporter is not an independent
kernel replay audit.

Snapshot differences report alpha-normalized type SHA-256, value hash64,
universe arity, dependency, kind, and axiom changes. The value hash is Lean's noncryptographic
expression hash: a change hint, not proof equivalence or a collision-free digest.
Users of changed local definitions are flagged transitively even when their own
types are unchanged. Coverage changes are explicit, since entries can disappear
when adding or deleting modules. A smaller refresh preserves other modules.
Historical comparisons work even if current sources
are stale; their output says so. A changed statement is never automatically
classified as stronger or weaker.

## MCP connection checks

Protocol version 3 advertises 18 read-only tools. The compiler tools are
`formalpedia_capabilities`, `formalpedia_semantic_status`,
`formalpedia_semantic_show`, `formalpedia_type_search`,
`formalpedia_dependencies`, and `formalpedia_semantic_diff`.

`capabilities` reports the loaded server entry-point fingerprint, checkout path,
tool groups, and semantic status. Use it to detect clients still connected to an
older process. Editing Python files does not reload that process. Reconnect the
client to rediscover tools; do not duplicate a correct server registration.

The first implementation provides the compiler index, structural search, proof
graph, and mathematical change metadata. It does not generate corollaries,
execute counterexample searches, or infer new obstruction records. Existing Lean
LSP proof attempts/minimal-hypothesis checks, research-engine attacks, and research
catalogue obstruction sections remain the tools for those tasks. A future
corollary workbench should build on these semantic records and report candidates,
remaining obligations, and actual Lean checks separately.
