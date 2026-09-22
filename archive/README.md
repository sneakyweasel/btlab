# Frozen laboratory archive

The active laboratory is dedicated to Juggler and Collatz. Independent earlier
projects are archived as of 23 September 2026. Their mathematical results and
negative knowledge remain available; archival status is not an evidence label.

The complete pre-cleanup repository is preserved at Git revision
`464d2d14b1e8d93263540c9f6d8175dd463276ae`, tagged locally as
`archive/balanced-ternary-2026-09-23`. No uncommitted research edits were included
in that snapshot or overwritten by the cleanup.

## What is retained and why

The [scope policy](../data/lab_scope.json) identifies 51 historical research
packages, four active applications and nine supporting packages. Supporting
packages include the old benchmark seeds that current planners still import.
The [inventory](inventory.json) records the Lean classification and the exact
files removed from Git tracking.

Historical research and Lean source remain at their original paths because
paper citations, theorem-ledger references, imports and reproduction tests use
those paths. They are excluded from default research listings, scoped theorem
search and active application tests. They are frozen, not a second agenda.
Do not develop them without an explicit request to reopen their scope.

Large temporary checkouts and visual-review scratch output are removed from
Git tracking and ignored, with local working copies preserved. Publication
packages, certificate inputs and existing `.build` audit material remain intact.

## Explicit historical access

```powershell
python tools/formalpedia.py search "Newton" --scope archive
btlab --include-archive status
pytest --include-archive
python tools/lab.py build --include-archive
rg --no-ignore-dot "Newton" src/research
git worktree add --detach ../btlab-historical archive/balanced-ternary-2026-09-23
```

The last command restores the complete old laboratory in a separate checkout.
If the local tag is unavailable, use the full commit above. The archive scope
is also available on formalpedia MCP search and OEIS laboratory links.

See the [historical documentation map](../docs/archive/legacy_documentation.md)
and the [active research map](../docs/README.md). Negative knowledge relevant to
Juggler or Collatz remains part of the active reading path.

The [cleanup record](../docs/architecture/lab_focus_cleanup.md) records validation
and the remaining issues in concurrent research work.
