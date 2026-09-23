"""Hold every paper's provenance pin to the history it names.

A paper prints a block like

    Repository:  https://github.com/sneakyweasel/btlab
    Commit:      bf018a78f4f8981899d5927015cc47056e8e3e22

and then tells its reader that the commit is the repository state that produced
its tables.  Nothing checked that.  `build_paper_*.py --check` compares the live
files against the digests in the paper's own release manifest, and the builder
writes that manifest from those same live files, so the manifest and the tree
agree by construction and the commit is never consulted at all.

Paper A carried the consequence into a deposit.  Its pin named a commit of
31 August 2026; `exceptions_parity.json` and `budget_opt.json`, the two files
Appendix B sends the reader to for the 141 exceptional lengths and the run-type
table, were both added after it.  The line was already false on 9 September 2026,
the day version 1.0.0 went to Zenodo, and stayed false for twelve days.  Paper D
reached the same state twice (b5fed743, d3df4e85) and was repinned by hand both
times, because a hand is all there was.

This module asks the question the gate was missing.  Is every file the release
manifest records as an input byte-identical at the commit the paper names, and is
that commit an ancestor of HEAD?  The editorial texts are exempt and only they:
the manuscript is where the pin line is written, so it cannot precede itself.
Text is compared line-ending normalised, the way the manifests hash it, so a CRLF
checkout does not change the verdict.

A paper that prints no `Repository:` line makes no commit-level claim and is
reported as such rather than passing quietly -- Papers B and C are in that state.
A paper that prints one must print a `Commit:` line that verifies.

    python tools/paper_pin.py            # every paper with a build tool
    python tools/paper_pin.py a d        # named papers
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_RE = re.compile(r"^Repository:\s+(\S+)\s*$", re.M)
COMMIT_RE = re.compile(r"^Commit:\s+([0-9a-f]{7,40})\s*$", re.M)
HISTORY_MAP = "docs/history/2026-09-23-commit-map.json"


def resolve_revision(root: Path, revision: str) -> str:
    """Translate a pre-cleanup identifier without changing a deposited paper.

    The subsequent ancestry and input-digest checks still apply to the mapped
    commit. The map is an explicit alias, never a substitute for those checks.
    """
    if not re.fullmatch(r"[0-9a-f]{7,40}", revision):
        raise ValueError("revision must be a hexadecimal commit ID (7 to 40 digits)")
    path = root / HISTORY_MAP
    if not path.exists():
        return revision
    record = json.loads(path.read_text(encoding="utf-8"))
    if record.get("schema_version") != 1:
        raise ValueError("unsupported history-map version")
    matches = [new for old, new in record["commits"].items() if old.startswith(revision)]
    if len(matches) > 1:
        raise ValueError(f"ambiguous historical revision: {revision}; use its full ID")
    if not matches:
        return revision
    if not re.fullmatch(r"[0-9a-f]{40}", matches[0]) or matches[0] == "0" * 40:
        raise ValueError(f"invalid replacement for historical revision {revision}")
    return matches[0]


class PinUnavailable(RuntimeError):
    """The history needed to answer is not here: no git, or a shallow clone.

    Distinct from a failure on purpose.  A shallow checkout cannot tell a wrong
    pin from an absent one, and answering `pass` there would be the same kind of
    green-for-nothing this module exists to remove.
    """


class NoPinClaimed(RuntimeError):
    """The paper prints no repository block, so there is no claim to falsify."""


def _git(root: Path, *args: str) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", "-C", str(root), *args],
                              capture_output=True, text=True,
                              encoding="utf-8", errors="replace")
    except OSError as exc:                                   # git not installed
        raise PinUnavailable(f"git is not runnable here: {exc}") from exc


def _shallow(root: Path) -> bool:
    out = _git(root, "rev-parse", "--is-shallow-repository")
    if out.returncode:
        raise PinUnavailable("not a git checkout; the pin cannot be verified here")
    return out.stdout.strip() == "true"


def normalise(data: bytes) -> bytes:
    return data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")


def digest(data: bytes) -> str:
    return hashlib.sha256(normalise(data)).hexdigest()


def manuscript_of(module) -> str:
    """The canonical Markdown a build tool works from.

    Papers A, C and D name it `SOURCE`; Paper B's two tools carry only `STEM` and
    build the path where they need it.  Both spellings are read here so that a
    tool is never skipped merely for naming its own manuscript differently.
    """
    source = getattr(module, "SOURCE", None)
    if source:
        return source
    stem = getattr(module, "STEM", None)
    if stem:
        return f"docs/theory/{stem}.md"
    raise NoPinClaimed(f"{module.__name__} names no manuscript to read a pin from")


def read_pin(root: Path, source: str) -> tuple[str, str]:
    """The repository and commit the manuscript prints, or a reason there is none."""
    text = (root / source).read_text(encoding="utf-8")
    repository = REPOSITORY_RE.search(text)
    if not repository:
        raise NoPinClaimed(f"{source} prints no `Repository:` line; no commit is claimed")
    commit = COMMIT_RE.search(text)
    if not commit:
        raise ValueError(
            f"{source} names a repository but no commit; a provenance block without a "
            "`Commit:` line tells the reader nothing it can be held to")
    return repository.group(1), commit.group(1)


def pinned_inputs(root: Path, module) -> list[str]:
    """Everything the release manifest calls an input, less the editorial texts.

    Taken from the builder rather than from the manifest file, so that a manifest
    which has itself gone stale cannot narrow what the pin is held to.
    """
    for attribute in ("input_files", "EDITORIAL"):
        if not hasattr(module, attribute):
            raise ValueError(
                f"{module.__name__} prints a provenance pin but has no {attribute}; "
                "the pin cannot be held to an input list that does not exist")
    return sorted(set(module.input_files(root)) - set(module.EDITORIAL))


def _blobs(root: Path, commit: str, paths: list[str]) -> dict[str, bytes | None]:
    """One git process for the whole input list.  None means absent at that commit."""
    specs = [f"{commit}:{name}" for name in paths]
    proc = subprocess.run(["git", "-C", str(root), "cat-file", "--batch"],
                          input=("\n".join(specs) + "\n").encode("utf-8"),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, pos, found = proc.stdout, 0, {}
    for name, spec in zip(paths, specs):
        end = out.find(b"\n", pos)
        if end < 0:
            raise PinUnavailable("git cat-file stopped early; the history looks truncated")
        header = out[pos:end].decode("utf-8", "replace")
        pos = end + 1
        if header.endswith((" missing", " ambiguous")):
            found[name] = None
            continue
        size = int(header.rsplit(" ", 1)[1])
        found[name] = out[pos:pos + size]
        pos += size + 1
    return found


def verify(root: Path, module) -> str:
    """Raise ValueError if the pin is not what the paper says it is.

    Returns a one-line summary on success, so a caller can print what was checked
    rather than only that nothing complained.
    """
    source = manuscript_of(module)
    _, printed_pin = read_pin(root, source)
    pin = resolve_revision(root, printed_pin)
    shallow = _shallow(root)
    resolved = _git(root, "rev-parse", "--verify", "--quiet", f"{pin}^{{commit}}")
    if resolved.returncode:
        if shallow:
            raise PinUnavailable(
                f"shallow checkout: commit {pin} is not present, so {source}'s pin "
                "cannot be verified here.  Check out with fetch-depth 0.")
        raise ValueError(
            f"{source} pins commit {pin}, which is not in this repository")
    full = resolved.stdout.strip()

    if shallow:
        raise PinUnavailable(
            f"shallow checkout: {source}'s pin {full[:12]} cannot be placed in "
            "history here.  Check out with fetch-depth 0.")
    if _git(root, "merge-base", "--is-ancestor", full, "HEAD").returncode:
        raise ValueError(
            f"{source} pins {full[:12]}, which is not an ancestor of HEAD; a "
            "reader at this revision cannot reach the state the paper names")

    paths = pinned_inputs(root, module)
    blobs = _blobs(root, full, paths)
    wrong = []
    for name in paths:
        live = root / name
        if not live.is_file():
            wrong.append(f"{name}: absent from the working tree")
        elif blobs[name] is None:
            wrong.append(f"{name}: absent at {full[:12]}")
        elif digest(blobs[name]) != digest(live.read_bytes()):
            wrong.append(f"{name}: differs at {full[:12]}")
    if wrong:
        # A wrong pin is usually wrong about most of the tree at once -- Paper A's was
        # wrong about 123 files of 124 -- and printing all of them buries the count that
        # actually tells you what happened.  Twelve is enough to recognise the shape.
        shown = wrong[:12]
        if len(wrong) > len(shown):
            shown.append(f"... and {len(wrong) - len(shown)} more")
        raise ValueError(
            f"{source} pins {full[:12]}, but {len(wrong)} of its {len(paths)} inputs "
            + ("is" if len(wrong) == 1 else "are")
            + " not the version" + ("" if len(wrong) == 1 else "s")
            + " the paper reports:\n  "
            + "\n  ".join(shown)
            + "\nPin a commit that carries them, or rebuild and commit the inputs "
              "first.  The pin must name a commit that PRECEDES the editorial commit "
              "writing the line, so commit the inputs, then the manuscript.")
    alias = f" (printed pre-cleanup ID {printed_pin[:12]})" if pin != printed_pin else ""
    return f"{source}: {len(paths)} inputs byte-identical at {full[:12]}{alias}"


def main() -> int:
    import argparse

    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("papers", nargs="*", help="paper letters; default is all of them")
    ap.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    ap.add_argument("--resolve", metavar="COMMIT", help="translate an older commit ID")
    args = ap.parse_args()

    if args.resolve:
        try:
            print(resolve_revision(args.root, args.resolve))
        except (ValueError, OSError) as exc:
            ap.error(str(exc))
        return 0

    import importlib.util

    builders = ([args.root / f"tools/build_paper_{letter}.py" for letter in args.papers]
                or sorted(args.root.glob("tools/build_paper_*.py")))
    failed = False
    for builder in builders:
        if not builder.is_file() or builder.name.endswith("_kit.py"):
            continue
        spec = importlib.util.spec_from_file_location(f"pin_{builder.stem}", builder)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        try:
            print("ok      " + verify(args.root, module))
        except NoPinClaimed as exc:
            print(f"no pin  {builder.name}: {exc}")
        except PinUnavailable as exc:
            print(f"skipped {builder.name}: {exc}")
        except (ValueError, OSError) as exc:
            failed = True
            print(f"FAILED  {builder.name}: {exc}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
