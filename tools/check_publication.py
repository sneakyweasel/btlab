"""Reject local-only material in the index and, optionally, reachable history.

Run before committing; CI also uses --history HEAD to catch deleted files and
merges of pre-cleanup history. This path policy complements Gitleaks; it cannot
decide whether arbitrary prose has permission to be redistributed.
"""

from __future__ import annotations

import argparse
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from research.repository import query as git_query


def prohibited(path: str) -> bool:
    """Keep retrieved sources, private records and credential files local."""
    name = PurePosixPath(path).name.lower()
    return (
        path.lower().startswith("literature/sources/")
        or name.endswith((".private.json", ".bundle"))
        or name in {"credentials.json", ".mcp.json", "id_rsa", "id_ed25519"}
        or (name.startswith(".env") and (name == ".env" or name.startswith(".env."))
            and name not in {".env.example", ".env.template", ".env.sample"})
    )


def git(root: Path, *args: str) -> bytes:
    result = git_query(root, *args)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", "replace").strip())
    return result.stdout


def violations(root: Path, history: str | None = None) -> list[str]:
    indexed = git(root, "ls-files", "-z").split(b"\0")
    paths = set(indexed)
    if history is not None:
        if git(root, "rev-parse", "--is-shallow-repository").strip() != b"false":
            raise RuntimeError("History check needs a full clone (fetch-depth: 0).")
        # Resolve first so a revision cannot be interpreted as another log option.
        revision = git(root, "rev-parse", "--verify", "--end-of-options",
                       f"{history}^{{commit}}").decode().strip()
        historical = git(root, "log", "--format=", "--name-only", "-z",
                         "--no-renames", "--full-history", revision, "--")
        paths.update(p.lstrip(b"\n") for p in historical.split(b"\0"))
    return sorted({p.decode("utf-8", "surrogateescape") for p in paths if p
                   and prohibited(p.decode("utf-8", "surrogateescape"))})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", metavar="REV", help="also inspect all ancestors of REV")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        found = violations(args.root, args.history)
    except RuntimeError as exc:
        print(f"Publication check failed: {exc}")
        return 2
    if found:
        print("Local-only paths found (contents withheld):")
        for path in found:
            print(f"  {path}")
        print("See docs/publication_safety.md. Deleting a file does not clean its history.")
        return 1
    print("Publication path check passed" + (" (including history)." if args.history else "."))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
