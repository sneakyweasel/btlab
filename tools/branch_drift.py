"""Which branches hold laboratory results that ``main`` does not?

Three times in September 2026 a finding was made on a branch, never merged,
and then rediscovered weeks later from a different direction: the Python 3.11
f-string repair (7 September, redone 14 September), the ``itinerary`` rename
restoration (same), and all three Section 11 constant corrections. Nothing
noticed, because nothing was looking. This is the thing that looks.

It is a *report*, not a verdict. A branch holding work is normal; a branch
holding work that nobody has looked at for weeks is the failure mode. The
test that consumes this enforces acknowledgement, not emptiness.

Two ways to measure this wrong, both found by calibration and both avoided
here:

* **Ledger ids alone miss whole modules.** ``information-field-dynamics``
  carries a 938-line Lean module and adds no ledger row at all; by ids it
  scores zero. Files are counted too.
* **"On the branch, not on main" counts what main deleted.** Two August
  ``cursor/*`` branches scored 17 Lean files and 102 sources against main --
  every one of them a file main had since removed in the ``src/bt``
  restructure, none of them the branch's work. Files are therefore counted
  against the *merge base*: what the branch added, not what main dropped.
"""

from __future__ import annotations

import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

LEDGER = "docs/theory/theorem_ledger.json"

#: Artifact classes worth noticing. A branch that adds none of these and no
#: ledger row is carrying prose or configuration, which merges or rots
#: harmlessly; one that adds any of them is carrying mathematics.
ARTIFACTS = {
    "lean": ("formal/", ".lean"),
    "probe": ("src/", ".py"),
    "test": ("tests/", ".py"),
    "dossier": ("docs/problems/", ".md"),
}


def _git(repo: Path, *args: str) -> str:
    out = subprocess.run(
        ["git", *args], capture_output=True, cwd=repo, check=False
    )
    return out.stdout.decode("utf-8", "replace")


def branch_refs(repo: Path, base: str = "main") -> list[str]:
    """Every local and remote branch except the base and symbolic HEADs."""

    raw = _git(repo, "for-each-ref", "--format=%(refname:short)", "refs/heads", "refs/remotes")
    skip = {base, f"origin/{base}", "origin/HEAD"}
    return sorted(r for r in raw.splitlines() if r.strip() and r not in skip and "->" not in r)


def _ledger_ids(repo: Path, ref: str) -> set[str]:
    raw = _git(repo, "show", f"{ref}:{LEDGER}")
    if not raw.strip():
        return set()
    try:
        rows = json.loads(raw)
    except json.JSONDecodeError:
        return set()
    return {r["id"] for r in rows if isinstance(r, dict) and r.get("id")}


@dataclass
class Drift:
    ref: str
    ahead: int
    behind: int
    last_commit: str
    ledger_ids: list[str] = field(default_factory=list)
    files: dict[str, list[str]] = field(default_factory=dict)

    @property
    def carries_work(self) -> bool:
        return bool(self.ledger_ids) or any(self.files.values())

    def as_dict(self) -> dict[str, Any]:
        return {
            "ref": self.ref,
            "ahead": self.ahead,
            "behind": self.behind,
            "last_commit": self.last_commit,
            "ledger_ids": self.ledger_ids,
            "files": {k: v for k, v in self.files.items() if v},
        }


def drift_for(repo: Path, ref: str, base: str = "main") -> Drift:
    ahead = _git(repo, "rev-list", "--count", f"{base}..{ref}").strip() or "0"
    behind = _git(repo, "rev-list", "--count", f"{ref}..{base}").strip() or "0"
    last = _git(repo, "log", "-1", "--format=%ad", "--date=short", ref).strip()
    d = Drift(ref=ref, ahead=int(ahead), behind=int(behind), last_commit=last)
    if d.ahead == 0:
        return d

    d.ledger_ids = sorted(_ledger_ids(repo, ref) - _ledger_ids(repo, base))

    merge_base = _git(repo, "merge-base", base, ref).strip()
    added = {
        line
        for line in _git(
            repo, "diff", "--name-only", "--diff-filter=A", merge_base, ref
        ).splitlines()
        if line.strip()
    }
    on_base = set(_git(repo, "ls-tree", "-r", "--name-only", base).splitlines())
    for kind, (prefix, suffix) in ARTIFACTS.items():
        d.files[kind] = sorted(
            f for f in added
            if f.startswith(prefix) and f.endswith(suffix) and f not in on_base
        )
    return d


def report(repo: Path, base: str = "main") -> list[Drift]:
    """Branches carrying ledger rows or artifacts the base does not have."""

    return [
        d
        for d in (drift_for(repo, ref, base) for ref in branch_refs(repo, base))
        if d.carries_work
    ]


def render(drifts: list[Drift]) -> str:
    if not drifts:
        return "No branch carries a ledger row or artifact that main lacks."
    lines = []
    for d in drifts:
        lines.append(
            f"{d.ref}  (+{d.ahead}/-{d.behind}, last commit {d.last_commit})"
        )
        if d.ledger_ids:
            lines.append(f"    {len(d.ledger_ids)} ledger row(s) main lacks:")
            lines.extend(f"        {i}" for i in d.ledger_ids)
        for kind, fs in d.files.items():
            if fs:
                lines.append(f"    {len(fs)} {kind} file(s) added on the branch:")
                lines.extend(f"        {f}" for f in fs)
    return "\n".join(lines)


def main() -> None:
    repo = Path(__file__).resolve().parents[1]
    print(render(report(repo)))


if __name__ == "__main__":
    main()
