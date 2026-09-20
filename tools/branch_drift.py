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
    "literature": ("literature/", ".json"),
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


def refs_are_visible(repo: Path) -> bool:
    """Can this checkout see remote refs at all?

    ``branch_refs`` returning nothing has two very different causes: a shallow or
    single-branch clone, where drift cannot be measured, and a repository whose
    branches have all been merged and deleted, where it can be and the answer is
    none. Distinguish them by asking whether *any* remote ref exists -- a normal
    clone always has ``origin/main`` -- so that a tidy repository runs the gate
    instead of skipping it, and stale acknowledgements still surface.
    """

    return bool(_git(repo, "for-each-ref", "--format=%(refname:short)", "refs/remotes").strip())


def _ledger_rows(repo: Path, ref: str) -> dict[str, str]:
    """Map row id to statement at ``ref``; empty if the ledger is unreadable."""

    raw = _git(repo, "show", f"{ref}:{LEDGER}")
    if not raw.strip():
        return {}
    try:
        rows = json.loads(raw)
    except json.JSONDecodeError:
        return {}
    return {
        r["id"]: r.get("statement") or ""
        for r in rows
        if isinstance(r, dict) and r.get("id")
    }


def _ledger_ids(repo: Path, ref: str) -> set[str]:
    return set(_ledger_rows(repo, ref))


@dataclass
class Drift:
    ref: str
    ahead: int
    behind: int
    last_commit: str
    ledger_ids: list[str] = field(default_factory=list)
    ledger_edits: list[str] = field(default_factory=list)
    files: dict[str, list[str]] = field(default_factory=dict)

    @property
    def carries_work(self) -> bool:
        return (
            bool(self.ledger_ids)
            or bool(self.ledger_edits)
            or any(self.files.values())
        )

    def as_dict(self) -> dict[str, Any]:
        return {
            "ref": self.ref,
            "ahead": self.ahead,
            "behind": self.behind,
            "last_commit": self.last_commit,
            "ledger_ids": self.ledger_ids,
            "ledger_edits": self.ledger_edits,
            "files": {k: v for k, v in self.files.items() if v},
        }


def drift_for(repo: Path, ref: str, base: str = "main") -> Drift:
    ahead = _git(repo, "rev-list", "--count", f"{base}..{ref}").strip() or "0"
    behind = _git(repo, "rev-list", "--count", f"{ref}..{base}").strip() or "0"
    last = _git(repo, "log", "-1", "--format=%ad", "--date=short", ref).strip()
    d = Drift(ref=ref, ahead=int(ahead), behind=int(behind), last_commit=last)
    if d.ahead == 0:
        return d

    merge_base = _git(repo, "merge-base", base, ref).strip()

    here = _ledger_rows(repo, ref)
    on_main = _ledger_rows(repo, base)
    at_fork = _ledger_rows(repo, merge_base)
    d.ledger_ids = sorted(set(here) - set(on_main))
    # A row the BRANCH changed since the fork, and that main has not already
    # changed the same way. Comparing against main instead of the fork would
    # report every row main has edited since -- the same calibration error
    # test_files_are_counted_against_the_merge_base_not_main was written for,
    # and it was made here first.
    d.ledger_edits = sorted(
        i
        for i in set(here) & set(at_fork) & set(on_main)
        if here[i] != at_fork[i] and here[i] != on_main[i]
    )
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
        if d.ledger_edits:
            lines.append(
                f"    {len(d.ledger_edits)} ledger row(s) the branch CORRECTS:"
            )
            lines.extend(f"        {i}" for i in d.ledger_edits)
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
