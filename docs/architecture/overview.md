# Architecture overview

The Juggler–Collatz Mathematical Laboratory has two research applications and
shared mathematical infrastructure. The active programme is Papers A–E and
their supporting results. Independent earlier projects are frozen historical
work; see the [archive](../../archive/README.md).

## Dependency boundaries

```text
cli, visualization          application interfaces
research.juggler_sequence   Juggler mathematics
research.collatz           Collatz mathematics, with related Syracuse/descent modules
research_engine            shared experimental dynamics
bt                         supporting exact arithmetic and representations
```

`bt` imports only itself and the standard library. `research_engine` does not
import problem applications. Applications may use these libraries and shared
experiment, conjecture and literature utilities. Generic reusable Lean results
retain their existing modules; a theorem's mathematical role is more useful than
renaming it to match the current project branding.

Package/import names remain `balanced-ternary`, `btlab`, `bt`, `research` and
`balanced-ternary-formal`. Paper-pinned package files, namespaces and proof source
paths are preserved. This avoids invalidating publication provenance merely to
change the working scope.

## Active scope

[data/lab_scope.json](../../data/lab_scope.json) records active applications,
retained support packages and historical projects. Python tests exclude the
archived applications by default; `pytest --include-archive` restores the full
historical suite. Specific archived test files remain explicitly runnable.

`python tools/lab.py build` follows the live Lean import graph from every
Juggler and Collatz module, not just the paper barrels. It therefore retains
Fourier analysis, derivative estimates, counting and other shared results
actually imported by the applications. `--include-archive` invokes the original
full Lake targets. Direct `cd formal; lake build` retains its historical meaning
because that Lake file is a pinned publication input.

Formalpedia search defaults to this same active Lean graph. `scope=archive` or
`scope=all` makes the historical library available; exact lookups and claim
inspection remain global. The OEIS database is always searched in full. Only its
laboratory-link tool applies the local scope, with an explicit archive option.
Claim tags and source attribution are independent of scope.

## Verification

After structural changes run the active Python suite and `python tools/lab.py
build`, plus relevant paper release gates. Archive classification must not change
mathematical definitions, erase prior negative knowledge, or omit a dependency
of an active result. New active imports are included automatically in the Lean
build and discovery closure.

Use the [Lean interface policy](lean_discovery.md),
[OEIS guide](oeis_discovery.md), [module map](research_modules.md) and
[research method](../methodology.md).
