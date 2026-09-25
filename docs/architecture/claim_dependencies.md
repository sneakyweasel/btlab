# Claim dependency graphs

The canonical [topic claims](../claims/README.md) can record which
claims a written proof uses. This complements Formalpedia's module/import graph
and its [compiled declaration graph](lean_semantics.md). It introduces no new
evidence label and does not certify that a proof is correct.

## Review a result

```powershell
python tools/formalpedia.py claim-graph J-paper-b-five-step-density-127 --format markdown
python tools/formalpedia.py claim-graph J-paper-b-density-one-under-fd
python tools/formalpedia.py claim-graph J-ooee-contagion-five-eighths --compiled --limit 50
python tools/render_theorem_ledger.py --check
```

The command prints a bounded view and writes nothing. Markdown includes a Mermaid
diagram, evidence labels, local conditions and the remaining review boundary.
JSON and the read-only MCP tool `formalpedia_claim_dependencies` provide paginated
nodes and edges. Start with `ledger_id`; optionally set `include_compiled=true`.
Return the same `snapshot` with subsequent `offset` pages. A ledger, relevant prose
or semantic snapshot change rejects old pagination. These are change detectors,
not an atomic proof certificate.

`max_nodes` defaults to 100 (maximum 200); pages have at most 100 items. Omitted
claims are explicit and make annotation coverage incomplete. `--require-complete`
exits nonzero for unknown/partial coverage, stale sources or omitted claims. It
checks **dependency annotation coverage**, not correctness, formalization or
unconditionality: a fully annotated conditional theorem can still have open
assumptions. Every response retains its evidence and assumption summary.

## Initial scope

| Root claim | Scope and review boundary |
|---|---|
| `J-paper-b-five-step-density-127` | Unconditional five-step descent density 7/8. No Hypothesis FD edge. The main proof chain is recorded; several analytic and external inputs remain partial. |
| `J-paper-b-density-one-under-fd` | Paper B Theorem 6.1, explicitly conditional on FD. A density-one conclusion does not establish termination for every start. |
| `J-ooee-contagion-five-eighths` | Unconditional 5/8 contagion in the current OOEE follow-up, under the stated set conditions. The actual production proof and its analytic boundaries are visible. |
| `J-ooee-tao-rate-termination` | Separate implication from an actual failure-count rate above 3/8; existence of that rate remains a hypothesis. |
| `J-ooee-pressure-rate-termination` | Separate implication from the stopped-pressure estimate and the recorded parameter/finite-base conditions. The estimate remains a hypothesis. |

The original Paper C row bundled the last three conclusions. It now names only
contagion; the two conditional conclusions have separate IDs. Their existing
human-proof status remains unchanged, including the pending English-to-Lean
coverage review. A kernel-trusted declaration does not establish that its linked
English statement is covered. Frozen deposited manuscripts are not modified by
this graph.

The first slice has deliberately incomplete leaves. In particular, Paper B's
OOOEE mixed-sum theorem needs its Appendix C/A/B proof inventory expanded; the
Fourier transfer still has an external discrepancy reference. Paper C's
count-poor tail, resonance and older assembly records retain explicit boundaries.
Other unannotated rows have unknown coverage, not a reviewed empty dependency list.

## Ledger format

Optional `conditions` is a list of local mathematical premises. An open input
has `claim_kind: "hypothesis"` and retains the `CONJECTURE` evidence tag. Ordinary
results default to `claim_kind: "result"`.

Each annotated claim has a nonempty `proof_routes` list. A route contains:

| Field | Meaning |
|---|---|
| `id` | Stable lowercase route ID, unique within this claim. |
| `method` | `written`; compiler edges are derived and never stored here. |
| `coverage` | `complete`, `partial`, or `unknown` enumeration of immediate dependencies at the named claim granularity. |
| `source` | Checkout-relative POSIX `path`, unique exact `start` and `end` delimiters, and `sha256` of the selected passage. |
| `uses` | Explicit list of objects with `claim` (ledger ID) and `kind`. |
| `notes` | Scope, justification and any unexpanded boundary. |

Edge kinds are `proof` (a result used in an argument), `statement` (an input to
formulating it), `assumption` (a premise not discharged by this route), and
`computation` (a finite computational claim). Edges pointing to hypothesis nodes
must be assumptions. Computational edges must point to `COMPUTATIONALLY VERIFIED`
rows; the row's statement retains its finite range. A dependency graph does not
turn that range into a universal result.

A missing `proof_routes` field means unknown. An explicit `uses: []` means no
dependencies only when its route has `coverage: "complete"` and explanatory notes.
Do not add empty lists to every historical row. Do not mark a route complete
until its proof passage's immediate mathematical inputs have been enumerated.

Multiple routes are alternatives. Select them using repeatable CLI
`--choose CLAIM=ROUTE`, or the MCP `choices` object mapping claim IDs to route IDs.
Without a selection, traversal stops at that claim and reports
`route_selection_required`. Assumptions from different alternatives are never
combined. The validator conservatively rejects circular support even across
routes; record proved implications separately when describing equivalences.

## Source freshness and maintenance

The source passage starts with `start` and ends immediately before `end`. Both
delimiters must occur exactly once and in order. SHA-256 hashes UTF-8 text after
universal newline normalization, so CRLF and LF produce the same pin. Paths must
remain inside the checkout. Delimiters avoid dependence on shifting line numbers;
queries return the current start line for navigation.

After editing a cited passage, reread it and review its dependencies, conditions,
scope and evidence. Only then update its pin and regenerate the ledger Markdown.
Do not bulk-refresh pins to silence a failing check. `render_theorem_ledger.py
--check` validates IDs, routes, edge types, acyclicity and source pins. Queries
retain stale edges with a warning rather than hiding their claims or treating
them as established. A current hash establishes only that the passage is unchanged.

To compute the pin after review, use `claim_graph.source_passage(root, source)`
from `tools/formalpedia_core`, then SHA-256 of the returned text encoded as UTF-8.
There is no automatic command that attests a review or promotes an evidence tag.

## Optional compiler associations

`--compiled` adds a separate projection from exact, unambiguous ledger `decl`
references in their recorded Lean file to current compiled dependencies. Each
edge retains `origin: "compiled"`, its type/value kind, declaration endpoints,
the path through intermediate declarations, and export/query snapshots. These
associations do not replace the written edges or affect annotation completeness.

The projection queries at most 20 declarations from the selected written graph,
to depth 3 and at most 100 declaration edges per root. It reports missing or
ambiguous declaration links, claims without declarations, unmapped helpers,
truncation and semantic freshness. The roots share one corpus read and graph
construction. Missing or stale exports contribute no trusted
edges; current modules in a partial export remain usable. Targets can name claims
outside the selected written graph. Use `formalpedia_claim` to inspect them.

A proof can mention a helper with no ledger row. A linked declaration can cover
only part of an English claim. Local binders can leave essential assumptions.
Accordingly, the projection neither proves English implication nor discharges
premises, runs an axiom audit, or changes evidence labels. No Lean build is needed
for written graphs; current compiled exports are needed for the optional overlay.

The ledger remains the single source of truth. The frontier and Blueprint view
below read these annotations; neither is a second manually maintained graph.

## Formalization frontier and Blueprint view

Following Tao's [PFR Blueprint](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/),
the frontier turns the written graph into a work queue. Each claim receives one status:

| Status | Meaning |
|---|---|
| `formalized` | `EXACT — LEAN VERIFIED`. |
| `ready` | Human-proved; a complete, current route whose proof and statement inputs are all Lean verified. |
| `ready_conditional` | As `ready`, with assumption edges kept as explicit hypotheses. |
| `blocked` | A complete route still has inputs outside Lean. Computation edges block until the finite claim is formalized. |
| `stale` | The chosen route's source pin no longer matches. |
| `needs_annotation` | Only partial or unknown routes: enumerate the dependencies first. |
| `unannotated` | No route: dependencies are unknown, never empty. |
| `open`, `finite`, `not_a_target` | Hypotheses and conjectures; `COMPUTATIONALLY VERIFIED` rows; `REFUTED` and `OBSERVATION` rows. |

Lists rank by downstream reach (claims that transitively use the item). `almost_ready`
has one missing input; `unlocks` ranks missing inputs by the claims they would make
ready; `unannotated_boundary` lists unannotated claims that an annotated proof uses.
Every item carries `next_action`, the proof passage with its current line, Lean inputs
with their declarations, and warnings. Inputs report the cached Jev English-coverage
band (`covered`, `doubtful`, `not_covered`, `stale`, `unasked` or `no_declaration`).
The band is advisory and never gates readiness. It does not replace review before a
retag. Alternative routes are evaluated separately; the best one is reported.

```powershell
python tools/formalpedia.py frontier                          # Markdown work queue
python tools/formalpedia.py frontier --format json --list ready --list unlocks
python tools/formalpedia.py frontier --scope J-paper-b-five-step-density-127
python tools/formalpedia.py blueprint                         # .cache/formalpedia/blueprint.html
```

The MCP tool `formalpedia_frontier` returns the JSON form. `blueprint` writes one
self-contained, git-ignored HTML page: status filters, the frontier lists, the
written graph (arrows point to inputs), a detail panel and a table of every claim.
It embeds the frontier JSON in its `#frontier-data` block and makes no network
requests. Open it directly, or serve it with the `blueprint` entry in
`.claude/launch.json`. Pass `--out` for another destination. Do not commit it.
