# Recovering earlier work

## September 2026 privacy cleanup

The 23 September cleanup rewrites history from the first retrieved source upload
on 2 September. It removes private correspondence and two retrieved source
copies, preserving the mathematical files. The earlier public release tags
`v0.2.1` and `v0.2.3` are unchanged.

The [commit translation table](history/2026-09-23-commit-map.json) maps earlier
identifiers to the corresponding cleaned commits. For an old citation, run:

```powershell
python tools/paper_pin.py --resolve OLD_COMMIT_ID
```

Use the returned ID in a GitHub commit or file URL. Paper provenance checks use
this table explicitly and still verify ancestry and every recorded input digest.
Deposited papers and their checksums remain unchanged; their printed commit IDs
identify the historical, pre-cleanup repository. The translation does not claim
that a deposit was regenerated or republished.

An old clone must be replaced or carefully migrated before pushing. Preserve
uncommitted work privately and reapply reviewed patches to a fresh clone; do not
merge old history back into the public branch. Recovery bundles are private and
must stay offline. See [publication safety](publication_safety.md).

## Earlier research programmes

The old Python UI, independent research applications and unused mathematical
modules were removed from the working tree on 23 September 2026. They are not
loaded by hidden archive modes. The complete pre-removal revision is
`2deed21498fe0392fbb8ebb8c9e57df18164f471`.

Recover the earlier laboratory in a separate directory:

```powershell
git worktree add --detach ../btlab-history 2deed21498fe0392fbb8ebb8c9e57df18164f471
```

The older tag `archive/balanced-ternary-2026-09-23` also remains available.
Current papers, proofs, certificates, relevant negative knowledge and their
shared dependencies stay in this checkout. Historical citations use Git permalinks.

The long agent guide and research journal were subsequently compacted. Their
earlier full-length versions are in `d4df022acacf4e3e7f3cbc6b0bce4d10e31f3630`.
Current decisions belong in the application guides, dossiers and proof maps;
the journal keeps recent entries for orientation.
