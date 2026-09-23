# Lean formalization

This is the formal library for Juggler, signed Collatz and their shared
mathematics. The package remains `balanced-ternary-formal`; its exact Lean and
Mathlib versions are pinned in [lean-toolchain](lean-toolchain) and
[lake-manifest.json](lake-manifest.json).

## Find a result

- [Juggler guide](../attacks/juggler/AGENT.md): layered modules, paper barrels,
  trust boundaries and registration.
- [Collatz module map](Problems/Collatz/README.md): signed maps, cylinders,
  cycles, ancestor counts and fibre mass.
- [Architecture](../docs/architecture/formalization.md): retained shared
  dependencies in `BTCalculus`, `Core`, `Representation`, `Operators` and Engine.
- [Lean naming and discovery](../docs/architecture/lean_discovery.md): public
  names, documentation, formalpedia search and the local MCP.
- [Research map](../docs/README.md): papers and evidence labels.

Query current sources from the repository root:

```powershell
python tools/formalpedia.py search "preimage mass" --limit 10
python tools/lab.py build --list
```

Use the linked proof maps and theorem ledger for exact hypotheses and claim
coverage. This README does not duplicate their evolving theorem inventory.

## Compile and check

From the repository root, `python tools/lab.py build` builds every retained
application module, ledger-cited result and transitive dependency. From this
directory, `lake build` builds the configured default libraries and paper barrels.
During development, use `lake env lean <file.lean>` for the edited module.

No `sorry` or `admit` is allowed. Compilation, theorem-to-claim coverage and
axiom audits are separate checks; catalogue search is source discovery, not
proof validation. Follow the relevant application guide when adding modules or
changing a public theorem. Earlier independent projects are in
[Git history](../docs/history.md).
