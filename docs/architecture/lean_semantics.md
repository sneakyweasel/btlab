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
# A smaller export contains exactly the requested modules, excluding their imports:
python tools/formalpedia.py semantic build --module Problems.Juggler.ReturnWordLoss
```

The builder uses the installed pinned compiler, first builds the selected local
modules with Lake, then exports their declarations using Lean itself. The default
selects every retained library source, including standalone application modules.
Missing compiler/packages fail with setup instructions. It does not install tools
or change the project configuration. Normal Lake build hooks still run, so this
is an explicit trusted-checkout CLI action, never an MCP query.

Complete snapshots live in ignored `.cache/formalpedia/semantic/`; logs and raw
exports live in `.build/formalpedia/`. A content-addressed immutable snapshot is
published through an atomic `current` pointer. A failed build or a detected
concurrent edit leaves the previous snapshot intact. Keep a snapshot identifier
before rebuilding if you want a historical comparison.

Local Lean sources, the toolchain pin, Lake configuration/manifest, and exporter
Lean code are hashed. The snapshot schema versions the Python representation;
query-only changes do not invalidate compiled data. Imported compiled object regions are checked by size and
modification time before/after export and on queries. This detects ordinary
concurrent rebuilds; it is not a cryptographic audit of the toolchain or external
packages, nor an atomic certificate of the filesystem. External source edits
require rebuilding those packages. Full exports track all local sources and
their inventory. Partial exports track the selected modules and their actual
compiler-reported local import closure, so unrelated research can continue.
Edits/deletions within that closure invalidate the snapshot; changed imports are
caught through their importing source. Missing dependency sources reject builds.

Semantic queries reject missing, corrupt, or stale snapshots and return the
rebuild command. Source search remains usable independently. Semantic builds are
optional and are not a new publication prerequisite or a generated Git artifact.

## Research workflow

1. Use source `search`, `show`, and `claim` to find a result and its recorded role.
2. Use `formalpedia_semantic_show` to inspect its compiled type and all binders.
   Exact IDs are `Module.Name::Fully.qualified.name`; short names must be unique.
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
to reject changes during pagination.

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
users; bounded traversal stops at external constants, includes private/generated
helpers, and reports truncation at 10,000 edges. Module imports remain available
through the original `formalpedia_impact` tool.

Lean's `collectAxioms` supplies transitive axiom dependencies. These can include
standard axioms such as `Classical.choice`, `propext`, and `Quot.sound`, as well as
custom axioms. Metadata does not imply axiom-freedom. Imported compiled modules
are trusted as Lean normally trusts imports; the exporter is not an independent
kernel replay audit.

Snapshot differences report alpha-normalized type SHA-256, value hash64,
dependency, kind, and axiom changes. The value hash is Lean's noncryptographic
expression hash: a change hint, not proof equivalence or a collision-free digest.
Users of changed local definitions are flagged transitively even when their own
types are unchanged. Coverage changes are explicit, since entries can disappear
when exporting fewer modules. Historical comparisons work even if current sources
are stale; their output says so. A changed statement is never automatically
classified as stronger or weaker.

## MCP connection checks

The existing server now advertises 18 read-only tools. The six additions are
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
