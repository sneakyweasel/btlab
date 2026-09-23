# Canonical claims

Edit the topic JSON arrays under `juggler/`, `collatz/` and `shared/`.
Each claim belongs to exactly one file. Existing files follow their primary proof
note or dossier; placement is editorial and does not assert a proof dependency.
Stable claim IDs are independent of filenames. A result used by several papers
is recorded once. New topics need no central file-registration list.

Use `python tools/formalpedia.py claim <ID>` to find the canonical `claim_location`
(file plus zero-based JSON pointer). Use `lab.py search` and `context` for the
mathematical background. Do not read every topic to find one claim.

The shared reader is `research.claims.load_claims(root)`. It supplies caller-owned
records, locations and a content snapshot, and rejects malformed records,
duplicate IDs, missing proof dependencies and circular written support. It reads
only canonical topic files, so a stale generated view cannot hide a recent edit.
Source-pin freshness is an additional audit option; discovery can still report
stale annotations explicitly. None of these checks establish mathematical truth.

Keep all seven evidence labels, hypotheses and proof-route fields intact when
moving a row. A missing proof route means unknown dependency coverage, not an
empty dependency list. See [proof dependencies](../architecture/claim_dependencies.md).
Source paths should be repository-relative. Existing relative Markdown citations
retain their meaning relative to the generated table in `docs/theory/`, even when
a row moves to another topic. Proof-route `source.path` is repository-relative.

After editing:

```powershell
python tools/render_theorem_ledger.py
python tools/render_theorem_ledger.py --check
python tools/lab.py check
```

The combined [JSON](../theory/theorem_ledger.json) and
[Markdown](../theory/theorem_ledger.md) are generated, sorted by claim ID. They
remain portable exports for readers and historical publication tooling. Edit
topic sources rather than these views. `--check` checks both views and every
recorded proof-source pin. Do not refresh a proof pin without reviewing its route.
