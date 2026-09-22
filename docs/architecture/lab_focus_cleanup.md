# Juggler–Collatz consolidation — 23 September 2026

The active lab now covers Juggler, Collatz, their shared mathematical dependencies
and Papers A–E. The [scope policy](../../data/lab_scope.json) classifies four
application packages, nine supporting packages and 51 archived research packages.

Historical sources remain at their original paths to preserve citations, imports,
paper reproduction and negative knowledge. They are excluded from default project
listings, research tests and theorem discovery. The [archive](../../archive/README.md)
records the pre-cleanup Git snapshot and restoration commands.

## Default workflows

- `pytest` collects active and shared tests; `--include-archive` restores historical tests.
- `python tools/lab.py build` selects all Juggler/Collatz Lean modules, including
  results outside paper barrels, and builds their dependencies.
- Formalpedia CLI/MCP search and OEIS laboratory links default to `scope=active`.
  Both expose `archive` and `all`; exact theorem lookup remains global.
- OEIS sequence searches still cover the entire local OEIS database.
- `btlab --include-archive` exposes historical commands and research listings.
- Source search omits archived research directories. `rg --no-ignore-dot` includes
  them while retaining Git ignore rules, including private-file exclusions.

The original Lake and package configurations remain stable because publication
manifests pin them. Direct `lake build` retains its historical full-library targets.
The optional UI retains its existing historical explorers.

## Inventory and preservation

The live Lean inventory at consolidation contains 305 active modules and 85
archived modules, with 7,578 and 1,682 declarations respectively. This includes
concurrent working-tree research; it is not the contents of the frozen Git tag.
Classification follows the transitive import graph rather than directory names
alone. Associated dossiers are retained through the Juggler index and claim ledger.

798 temporary files were removed from Git tracking, including duplicate checkouts
and rendered review images. All local copies were preserved. The inventory records
their paths and SHA-256 hashes. The 162 tracked `.build` publication/audit files
were retained, as were publication kits and certificate inputs.

## Verification and remaining workspace issues

The active Lean build completed successfully (9,010 build jobs). Scope, catalogue,
MCP protocol, historical CLI and OEIS paper checks passed. Repository-wide Ruff,
the ledger renderer and the refreshed branch/formalpedia index checks passed.

The full active fast test run initially reported 5,719 passed, 315 skipped and
15 failed. Follow-up checks resolved 12 failures: five historical CLI calls now
use the explicit archive flag, five Lean/Git checks passed with the host environment
configured, and two generated-index checks passed after refresh.

Three test failures remain in two areas of concurrent research/publication work:

- The Collatz generation-mass draft links to missing
  `formal/AxiomCheckCollatzGenerationMass.lean` and
  `formal/AxiomCheckCollatzGenerationMass.expected`.
- Two Paper E release gates detect a stale `Sources_and_certificate.zip`.

These files were already under independent work. The cleanup does not supply
placeholder audits or replace that publication package. Consequently this report
does not claim that every repository gate is green. The complete fast suite was
not rerun after the targeted fixes.
