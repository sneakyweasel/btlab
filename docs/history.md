# Recovering earlier work

The old Python UI, independent research applications and unused mathematical
modules were removed from the working tree on 23 September 2026. They are not
loaded by hidden archive modes. The complete pre-removal revision is
`f038c8526134cdaabd10857b23a87520c7cebc4f`.

Recover the earlier laboratory in a separate directory:

```powershell
git worktree add --detach ../btlab-history f038c8526134cdaabd10857b23a87520c7cebc4f
```

The older tag `archive/balanced-ternary-2026-09-23` also remains available.
Current papers, proofs, certificates, relevant negative knowledge and their
shared dependencies stay in this checkout. Historical citations use Git permalinks.

The long agent guide and research journal were subsequently compacted. Their
earlier full-length versions are in `6512810cf65a4dd092a962a9c535e45b5f74614f`.
Current decisions belong in the application guides, dossiers and proof maps;
the journal keeps recent entries for orientation.
