# Publishing this laboratory

This is a public repository. Keep retrieved articles, book scans, webpage
captures and correspondence in the ignored `literature/sources/` directory or
outside the checkout. Private literature records use `*.private.json`.
Recovery bundles are private backups and must never be uploaded.

Public literature records contain bibliographic facts, source links and original
summaries. A citation does not establish permission to redistribute a source.
For reused code, retain the applicable license and attribution; the notices in
`literature/licenses/` and the adapted Lean modules must remain. Author contacts
intentionally published in papers are distinct from private correspondence.

Before committing, inspect the staged diff and run:

```powershell
python tools/check_publication.py
```

The publication-safety workflow checks every ancestor of the proposed revision,
so merging old history containing a removed source fails even if the current
tree is clean. It also runs the pinned Gitleaks scanner with fully redacted
output. Its only extra exception is for 16-digit hexadecimal cache IDs in the
historical formalpedia verdict file; other values and paths remain scanned.
GitHub secret scanning and push protection provide an additional credential
check. CI detects problems after upload; inspect and scan locally first.

With Gitleaks installed, check staged changes before committing and the branch
before pushing:

```powershell
gitleaks git . --staged --config .gitleaks.toml --redact=100 --ignore-gitleaks-allow
python tools/check_publication.py --history HEAD
gitleaks git . --log-opts="--full-history HEAD" --config .gitleaks.toml --redact=100 --ignore-gitleaks-allow --max-archive-depth=4
```

Path and credential checks do not determine copyright permission or recognise
all personal information. Review new source material before publication.

## History cleanup

The September 2026 cleanup removes three retrieved/private source files from
reachable Git history. Keep private recovery backups offline. Published paper
deposits remain historical records; do not silently replace their files or
claimed checksums. Commit mappings and recovery instructions belong in
[the history guide](history.md).

For an older clone, preserve uncommitted work privately, then clone the cleaned
repository again and reapply only reviewed changes. Do not merge an old branch
into cleaned history or push a private backup. A deletion commit or ignore rule
does not erase earlier versions. Cached GitHub objects and external copies may
require separate cleanup; see
[GitHub's removal guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository).
