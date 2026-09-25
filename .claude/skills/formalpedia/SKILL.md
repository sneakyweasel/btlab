---
name: formalpedia
description: Search the laboratory's local Lean declarations, inspect complete hypotheses and exact ledger links, and check module impact before adding or changing a proof. Use the formalpedia MCP or tools/formalpedia.py. This is distinct from the public prove2.me platform.
---

# Formalpedia

Use the local catalogue before proving a lemma that may already exist, renaming
an interface, or identifying the Lean statement behind a paper or ledger row.
The CLI and MCP share a live, read-only catalogue. Search does not need a saved
index rebuild. A source scan is not Lean elaboration or an executed proof audit.

## Find and inspect

1. Search by mathematical objects and conclusion words. Narrow by namespace,
   exact module, declaration kind or ledger ID as needed. Search includes
   complete source headers, documentation and explicitly linked claim text.
2. Use the fully qualified identity from the result with `show`. Read every
   hypothesis and the actual conclusion. Ambiguous short names return
   alternatives; never choose one by file order. Separate source modules can
   declare the same full name: use the module filter or returned catalogue ID.
3. Before editing, use `impact`. Its dependencies are module imports, not
   theorem-level proof dependencies. Keep paper references and pinned release
   inputs in mind before renaming anything.
4. Use Lean or `lean-lsp` to check applicability, implicit section variables,
   notation and proof obligations. A search miss is weak evidence of absence.
   In Codex, the servers are registered as `btlab-formalpedia` and
   `btlab-lean-lsp`; see the policy's setup instructions on a new machine.

```powershell
python tools/formalpedia.py search "contagion mass" --limit 10
python tools/formalpedia.py search "bound" --namespace Problems.Juggler --json
python tools/formalpedia.py show Problems.Juggler.ScaleAverage.FailureMassLowerBound
python tools/formalpedia.py claim J-pressure-scale-average-contagion-transfer
python tools/formalpedia.py impact Problems.Juggler.FateScaleAverage
python tools/formalpedia.py status
python tools/formalpedia.py audits
python tools/formalpedia.py ledger-check
python tools/formalpedia.py mathlib "Real.sqrt, _ * _"
```

To choose what to formalize, run `python tools/formalpedia.py frontier` (MCP
`formalpedia_frontier`). `ready` claims have a complete written route whose
inputs are all Lean verified. `python tools/formalpedia.py frontier --task <ID>`
prints a self-contained task (`agent_prompt`) to follow or hand to another agent;
read its input coverage warnings before relying on an input. Pin a route passage
with `python tools/formalpedia.py passage-pin`. `unlocks` ranks the missing
inputs that would make most claims ready. `blueprint` writes the same data as a
browsable HTML page under `.cache/formalpedia/`. See the
[frontier guide](../../../docs/architecture/claim_dependencies.md#formalization-frontier-and-blueprint-view).

The MCP equivalents are `formalpedia_search`, `formalpedia_show`,
`formalpedia_claim`, `formalpedia_impact`, `formalpedia_status`, and
`formalpedia_lint`. Restart paginated searches if the snapshot changes.
Private helpers and deprecated names are hidden from default search; include
them explicitly when investigating implementation or compatibility.

## Identity, claims and trust

`qualified_name` is the public source identity; `module` is the import unit.
Private compiler names and generated declarations require Lean. Search excerpts
are bounded; `show` returns the full source header without the old line limit.

`ledger_exact` lists unique explicit declaration references. The legacy
`ledger` field is only a file association. An explicit reference is not proof
that a declaration covers the entire English claim. Check statements together.

The source `trust` marker detects direct `native_decide` or incomplete proof
markers; `unmarked` only means none was found in the declaration's text. It does
not establish compilation, transitive trust, or kernel axiom dependencies.
Use the executable Lean audits for those claims. Do not infer an unconditional
result from a conditional theorem's name or documentation.

When `signature_complete` is false, read `signature_context`: section `variable`,
`include` and `omit` commands add binders the header does not show.

`axiom_audits` on `show`, and `axiom_audit_coverage` on `claim`, quote committed
`#print axioms` output from `formal/AxiomCheck*.expected`. That is executed Lean
evidence as of the recording commit; an empty list means no check covers the
declaration. `python tools/formalpedia.py audits` lists missing and stale
artifacts.

Before retagging a ledger row `EXACT — LEAN VERIFIED`, name its declarations in
`decl` and run `python tools/formalpedia.py ledger-check`; with a semantic
export present it also checks each declaration's compiled axioms against the
row's `lean_trust`. The CLI keeps its index in `.cache/formalpedia/` and
rebuilds it whenever a source, the ledger or an axiom artifact changes.

Formalpedia's catalogue covers this repository only. Search Mathlib with
`python tools/formalpedia.py mathlib "<Loogle query>"` (MCP
`formalpedia_mathlib_search`), which queries the public Loogle service and marks
each hit `declared` in the pinned Mathlib, `module_missing`,
`not_declared_literally` or `unchecked`. Loogle tracks a newer Mathlib: confirm
a hit with `#check` through lean-lsp. Inside Lean, `#loogle`, `#leansearch` and
`exact?` work too.

## Public interface policy

Follow [the naming and discovery policy](../../../docs/architecture/lean_discovery.md).
Use mathematical namespaces, Mathlib naming, and docstrings for new public
declarations. Preserve object-name tokens such as `logMass` inside theorem
names. Keep temporary helpers private and paper numbers in metadata.

Run `python tools/lean_style.py`. Existing individual violations are recorded
in a reviewed baseline; new names and changed statements are checked. Do not
expand that baseline to silence a new violation. Migrate public families with
deprecated aliases when needed and preserve published references.

## Generated records and concurrent work

`build`, `dag`, `propose`, `review`, and cached coverage review write reproducible
exports under ignored `.cache/formalpedia/`. Every report reads current Lean
sources and ledger claims; an old exported index is never its input. Exports are
optional and should not be committed. `build --check` only checks whether the
last local index export still matches the source tree.

The reviewed style baseline and original advisory verdicts remain versioned
under `data/research/formalpedia/`. `jev-coverage --limit 0` refreshes only local
reports; it neither sends a request nor rewrites the retained advisory evidence.

## Advisory statement coverage

The ledger's retag workflow requires asking Jev about the row before ruling;
its answer is advisory. External requests share unpublished statements and need
the authorization applicable to the session. This skill and the read-only MCP
do not independently authorize sending them.

For an authorized check: `python tools/formalpedia.py jev-coverage --rows ID`.
Compare the English claim with every named declaration, particularly when the
coverage score is below 0.5. Extend the declaration set, narrow the claim, or
retain `EXACT — HUMAN PROOF` when appropriate. Never automatically retag rows.
`jev-coverage --limit 0` refreshes the digest from cached opinions without a
request. Changed statement keys become stale rather than inheriting old advice.
