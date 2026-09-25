"""Land an agent's branch on main, one branch at a time, with the shared views regenerated.

    python tools/lab.py worktree new <name>      create .build/worktrees/<name> on branch agent/<name>
    python tools/lab.py worktree new <name> --profile python   the same, Python setup only
    python tools/lab.py land <branch>            rebase, regenerate, check, fast-forward main
    python tools/lab.py land <branch> --dry-run  do everything except move main
    python tools/lab.py worktree list            each agent branch, its worktree and landed verdict
    python tools/lab.py worktree remove <name>   remove a clean, landed worktree and its branch

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


def checkouts(root: Path) -> dict[str, Path]:
    """Each checked-out branch and the worktree that has it."""
    found, current = {}, None
    for line in git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line[len("worktree "):])
        elif line.startswith("branch refs/heads/"):
            found[line[len("branch refs/heads/"):]] = current
    return found


def checkout_of(root: Path, branch: str) -> Path | None:
    """The worktree that has `branch` checked out, if any."""
    return checkouts(root).get(branch)


def changes(work: Path) -> list[str]:
    """Uncommitted and untracked changes, without refreshing the index."""
    return git(work, "--no-optional-locks", "status", "--porcelain", "--untracked-files=all").splitlines()


def landed(root: Path, branch: str, onto: str = "main") -> dict:
    """Whether every commit of `branch` is on `onto`. Landing rebases, so an ancestor test
    alone misses landed work; a branch whose commits all have a patch-equivalent commit on
    `onto` (`git cherry` reports only `-`) is landed too. A commit whose shared views were
    regenerated during landing changes its patch, and is reported as not landed."""
    if subprocess.run(["git", "merge-base", "--is-ancestor", branch, onto], cwd=root).returncode == 0:
        return {"landed": True, "test": "ancestor", "detail": f"{branch} is an ancestor of {onto}"}
    cherry = git(root, "cherry", "-v", onto, branch).splitlines()
    pending = [line[2:] for line in cherry if line.startswith("+")]
    if not pending:
        return {"landed": True, "test": "cherry",
                "detail": f"all {len(cherry)} commits are patch-equivalent to commits on {onto}"}
    return {"landed": False, "test": None, "unlanded": pending}


def agent_branches(root: Path, onto: str = "main") -> list[dict]:
    """Every agent/* branch, its worktree, whether that is dirty, and the landed verdict."""
    held = checkouts(root)
    rows = []
    for branch in git(root, "for-each-ref", "--format=%(refname:short)", "refs/heads/agent/").splitlines():
        path = held.get(branch)
        rows.append({"name": branch[len("agent/"):], "branch": branch,
                     "worktree": str(path) if path else None,
                     "dirty": bool(changes(path)) if path else None, **landed(root, branch, onto)})
    return rows


def remove_worktree(root: Path, name: str, onto: str = "main", dry_run: bool = False) -> dict:
    """Remove agent/<name> and its worktree, only when clean and fully on `onto`."""
    branch = f"agent/{name}"
    if subprocess.run(["git", "rev-parse", "--verify", "-q", f"refs/heads/{branch}"], cwd=root,
                      capture_output=True).returncode:
        raise LandingError(f"no branch {branch}")
    path = checkout_of(root, branch)
    verdict = landed(root, branch, onto)
    report = {"name": name, "branch": branch, "worktree": str(path) if path else None, "onto": onto,
              "verdict": verdict}
    refusals = []
    if path is not None:
        dirty = changes(path)
        if dirty:
            refusals.append(f"the worktree has uncommitted or untracked changes: {dirty[:20]}")
        if path.resolve() == root.resolve():
            refusals.append("this is the checkout running the command; run it from another checkout")
    if not verdict["landed"]:
        refusals.append(f"{len(verdict['unlanded'])} commit(s) of {branch} are not on {onto}: "
                        f"{verdict['unlanded'][:20]}")
    if refusals:
        return report | {"status": "refused", "reasons": refusals}
    if dry_run:
        return report | {"status": "removable (dry run; nothing changed)"}
    if path is not None:
        # A prepared worktree holds Lake packages beyond Windows' 260-character limit.
        git(root, "-c", "core.longpaths=true", "worktree", "remove", str(path))
    git(root, "branch", "-D", branch)
    git(root, "worktree", "prune")
    return report | {"status": "removed"}


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


def commit_views(work: Path, message: str) -> list[str]:
    """Commit what regeneration changed, which must be shared views only; return the paths.

    The status is read NUL-separated and unstripped: a porcelain entry starts with a
    status column that may be a space. A view can also differ only in line endings,
    which git reports as modified and then normalises away on `add`; that is no change,
    so the commit happens only when the staged diff is real.
    """
    status = subprocess.run(["git", "status", "--porcelain", "-z"], cwd=work, capture_output=True,
                            text=True, encoding="utf-8").stdout
    changed = [entry[3:] for entry in status.split("\0") if entry]
    if not changed:
        return []
    stray = [path for path in changed if path not in SHARED_VIEWS]
    if stray:
        raise LandingError(f"regeneration wrote files outside the shared views: {stray}")
    git(work, "add", "--", *changed)
    staged = git(work, "diff", "--cached", "--name-only").splitlines()
    if staged:
        git(work, "commit", "-q", "-m", message)
    return staged


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
        report["regenerated"] = commit_views(work, f"Regenerate the shared views after landing {branch}")
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


def new_worktree(root: Path, name: str, onto: str = "main", prepare: bool = True,
                 profile: str = "full") -> dict:
    """Create the worktree and prepare it from this checkout. Use the python profile for
    changes outside formal/: it installs the pinned Python environment only."""
    path = root / ".build/worktrees" / name
    branch = f"agent/{name}"
    git(root, "worktree", "add", "-b", branch, str(path), onto)
    report = {"status": "created", "worktree": str(path), "branch": branch, "profile": profile}
    if prepare:
        run = subprocess.run([sys.executable, "tools/lab.py", "prepare", "--apply", "--profile", profile,
                              "--from", str(root)],
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
    tree = commands.add_parser("worktree", help="create, list or remove agent worktrees")
    tree.add_argument("action", choices=["new", "list", "remove"])
    tree.add_argument("name", nargs="?")
    tree.add_argument("--onto", default="main")
    tree.add_argument("--no-prepare", action="store_true")
    tree.add_argument("--profile", choices=["python", "full"], default="full",
                      help="new: python prepares only the pinned Python environment (changes outside formal/)")
    tree.add_argument("--dry-run", action="store_true", help="remove: print the verdict only")
    args = parser.parse_args(argv)
    if args.command == "worktree" and args.action != "list" and not args.name:
        parser.error(f"worktree {args.action} needs a name")
    try:
        if args.command == "land":
            report = land(ROOT, args.branch, args.onto, args.dry_run)
        elif args.action == "new":
            report = new_worktree(ROOT, args.name, args.onto, not args.no_prepare, args.profile)
        elif args.action == "list":
            report = {"onto": args.onto, "agents": agent_branches(ROOT, args.onto)}
        else:
            report = remove_worktree(ROOT, args.name, args.onto, args.dry_run)
    except LandingError as exc:
        print(json.dumps({"status": "failed", "reason": str(exc)}, indent=2))
        return 1
    print(json.dumps(report, indent=2))
    return int(report.get("status") == "refused")


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
