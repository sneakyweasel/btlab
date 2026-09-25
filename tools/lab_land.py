"""Land an agent's branch on main, one branch at a time, with the shared views regenerated.

    python tools/lab.py worktree new <name>      create .build/worktrees/<name> on branch agent/<name>
    python tools/lab.py land <branch>            rebase, regenerate, check, fast-forward main
    python tools/lab.py land <branch> --dry-run  do everything except move main

Agents work in their own worktree and branch and never commit to main. Landing happens
in a temporary worktree, so neither main's checkout nor the agent's is touched until the
result is ready. The shared views (the theorem ledger, the Juggler branch index and the
preprint index) are regenerated there from committed files only, so they never pick up
another session's unfinished rows. A conflict in a shared view is resolved by taking the
branch's version and regenerating; a conflict anywhere else stops the landing with main
unchanged. Main moves only by fast-forward, in the checkout that has it, so uncommitted
work there is never overwritten: git refuses, and the landed result waits on a branch.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
#: Written only by landing, from committed claim files, dossiers and paper metadata.
SHARED_VIEWS = ("docs/theory/theorem_ledger.md", "docs/theory/theorem_ledger.json",
                "attacks/juggler/index.json", "preprints/README.md")
#: How to regenerate them, run from the landing worktree.
REGENERATE = (["tools/render_theorem_ledger.py"],
              ["-m", "research.juggler_sequence.branch_index"],
              ["tools/preprints.py", "--write-index"])
#: Checks every landing must pass. They are fast and need no Lean build; the agent runs
#: `lab.py verify --changed` in its own worktree before asking to land.
CHECKS = (["tools/render_theorem_ledger.py", "--check"],
          ["-m", "research.juggler_sequence.branch_index", "--check"],
          ["tools/preprints.py", "--check"],
          ["tools/paper_pin.py"])


class LandingError(RuntimeError):
    pass


def git(root: Path, *args: str, check: bool = True) -> str:
    run = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, encoding="utf-8")
    if check and run.returncode:
        raise LandingError(f"git {' '.join(args)}: {(run.stderr or run.stdout).strip()}")
    return run.stdout.strip()


def python(root: Path, argv: list[str]) -> subprocess.CompletedProcess:
    env = {**os.environ, "PYTHONPATH": str(root / "src") + os.pathsep + str(root / "tools")}
    return subprocess.run([sys.executable, *argv], cwd=root, capture_output=True, text=True,
                          encoding="utf-8", errors="replace", env=env)


def checkout_of(root: Path, branch: str) -> Path | None:
    """The worktree that has `branch` checked out, if any."""
    current = None
    for line in git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line[len("worktree "):])
        elif line == f"branch refs/heads/{branch}":
            return current
    return None


def rebase(work: Path, onto: str) -> list[str]:
    """Replay the branch onto `onto`; shared views resolve to the branch's side and are
    regenerated afterwards. Returns the shared views that conflicted."""
    resolved: list[str] = []
    run = subprocess.run(["git", "-c", "core.editor=true", "rebase", onto], cwd=work,
                         capture_output=True, text=True, encoding="utf-8")
    while run.returncode:
        conflicted = git(work, "diff", "--name-only", "--diff-filter=U").splitlines()
        if not conflicted:
            git(work, "rebase", "--abort", check=False)
            raise LandingError(f"rebase failed: {(run.stderr or run.stdout).strip()[-400:]}")
        other = [p for p in conflicted if p not in SHARED_VIEWS]
        if other:
            git(work, "rebase", "--abort", check=False)
            raise LandingError("conflict outside the shared views; rebase the branch on main "
                               f"yourself and land again: {other}")
        # During a rebase "theirs" is the commit being replayed, the branch's side.
        git(work, "checkout", "--theirs", "--", *conflicted)
        git(work, "add", "--", *conflicted)
        resolved += conflicted
        run = subprocess.run(["git", "-c", "core.editor=true", "rebase", "--continue"], cwd=work,
                             capture_output=True, text=True, encoding="utf-8")
    return sorted(set(resolved))


def land(root: Path, branch: str, onto: str = "main", dry_run: bool = False,
         regenerate=REGENERATE, checks=CHECKS) -> dict:
    tip = git(root, "rev-parse", "--verify", f"{branch}^{{commit}}")
    base = git(root, "rev-parse", "--verify", f"{onto}^{{commit}}")
    if subprocess.run(["git", "merge-base", "--is-ancestor", tip, base], cwd=root).returncode == 0:
        return {"status": "nothing to land", "branch": branch, "onto": onto, "head": base}
    work = root / ".build/land" / uuid.uuid4().hex[:12]
    work.parent.mkdir(parents=True, exist_ok=True)
    git(root, "worktree", "add", "--detach", str(work), tip)
    report = {"branch": branch, "onto": onto, "old_head": base, "worktree": str(work)}
    try:
        report["resolved_shared_views"] = rebase(work, base)
        report["commits"] = git(work, "rev-list", "--reverse", f"{base}..HEAD").splitlines()
        failures = []
        for argv in regenerate:
            run = python(work, argv)
            if run.returncode:
                failures.append({"command": argv, "output": (run.stdout + run.stderr)[-800:]})
        if failures:
            raise LandingError(f"regeneration failed: {failures}")
        # NUL-separated and unstripped: a porcelain line starts with a status column that
        # may be a space, and stripping the output would eat it from the first path.
        status = subprocess.run(["git", "status", "--porcelain", "-z"], cwd=work, capture_output=True,
                                text=True, encoding="utf-8").stdout
        changed = [entry[3:] for entry in status.split("\0") if entry]
        if changed:
            stray = [path for path in changed if path not in SHARED_VIEWS]
            if stray:
                raise LandingError(f"regeneration wrote files outside the shared views: {stray}")
            git(work, "add", "--", *changed)
            # A regenerated view can differ only in line endings, which git normalises
            # away on `add`; commit only a real change.
            staged = git(work, "diff", "--cached", "--name-only").splitlines()
            if staged:
                git(work, "commit", "-q", "-m", f"Regenerate the shared views after landing {branch}")
            report["regenerated"] = staged
        results = []
        for argv in checks:
            run = python(work, argv)
            results.append({"command": " ".join(argv), "ok": run.returncode == 0,
                            "output": (run.stdout + run.stderr).strip()[-600:]})
        report["checks"] = results
        if not all(r["ok"] for r in results):
            raise LandingError("a landing check failed; see checks")
        new = git(work, "rev-parse", "HEAD")
        report["new_head"] = new
        if dry_run:
            report["status"] = "ready (dry run; main unchanged)"
            return report
        holder = checkout_of(root, onto)
        if holder is None:
            git(root, "update-ref", f"refs/heads/{onto}", new, base)
        else:
            moved = subprocess.run(["git", "merge", "--ff-only", "-q", new], cwd=holder,
                                   capture_output=True, text=True, encoding="utf-8")
            if moved.returncode:
                parked = f"land/{branch.replace('/', '-')}"
                git(root, "branch", "-f", parked, new)
                raise LandingError(f"{onto} could not fast-forward in {holder} "
                                   f"({(moved.stderr or moved.stdout).strip()}); the landed "
                                   f"result waits on {parked}")
        report["status"] = "landed"
        return report
    finally:
        git(root, "worktree", "remove", "--force", str(work), check=False)


def new_worktree(root: Path, name: str, onto: str = "main", prepare: bool = True) -> dict:
    path = root / ".build/worktrees" / name
    branch = f"agent/{name}"
    git(root, "worktree", "add", "-b", branch, str(path), onto)
    report = {"status": "created", "worktree": str(path), "branch": branch}
    if prepare:
        run = subprocess.run([sys.executable, "tools/lab.py", "prepare", "--apply", "--from", str(root)],
                             cwd=path, capture_output=True, text=True, encoding="utf-8", errors="replace")
        report["prepare"] = "ok" if run.returncode == 0 else (run.stdout + run.stderr)[-600:]
    return report


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="lab.py", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    landing = commands.add_parser("land", help="land a branch on main")
    landing.add_argument("branch")
    landing.add_argument("--onto", default="main")
    landing.add_argument("--dry-run", action="store_true")
    tree = commands.add_parser("worktree", help="create an agent worktree")
    tree.add_argument("action", choices=["new"])
    tree.add_argument("name")
    tree.add_argument("--onto", default="main")
    tree.add_argument("--no-prepare", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.command == "land":
            report = land(ROOT, args.branch, args.onto, args.dry_run)
        else:
            report = new_worktree(ROOT, args.name, args.onto, not args.no_prepare)
    except LandingError as exc:
        print(json.dumps({"status": "failed", "reason": str(exc)}, indent=2))
        return 1
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
