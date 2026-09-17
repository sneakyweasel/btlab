"""Build the seed dataset for the local prover from the kernel-trusted theorems.

Reads ``data/research/formalpedia/index.json``, slices every ``theorem`` or
``lemma`` whose trust is ``kernel`` out of its source file, records the header
context active at that line (imports, opens, namespaces, sections, variables,
set_options), and splits the declaration into statement and proof at the first
top-level ``:=``.

Outputs, under ``data/seed/``:

* ``seed.jsonl``        tactic-mode proofs (statement ends in ``:= by``)
* ``seed_term.jsonl``   term-mode and pattern-matching proofs
* ``seed_summary.json`` counts and the failures, if any

Declarations whose trust is ``compiler`` are excluded on purpose. The seed must
never teach ``native_decide``. ``--check N`` splices N random tactic records
back into their own files through ``tools/seed/verify.py`` and reports whether
the slicing reproduces proofs the kernel accepts.

A record's ``context`` holds only header lines (imports, opens, variables). A
proof that uses a definition made earlier in the same file needs that file
prefix too; ``file`` and ``span`` locate it, and the trainer decides how much
of it to show.
"""
from __future__ import annotations

import argparse
import collections
import json
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "data" / "research" / "formalpedia" / "index.json"
OUT_DIR = ROOT / "data" / "seed"

SCOPE_OPEN = re.compile(r"^(noncomputable\s+section|namespace|section|mutual)\b\s*(\S*)")
SCOPE_CLOSE = re.compile(r"^end\b\s*(\S*)")
HEADER = re.compile(
    r"^(open|variable|set_option|universe|attribute|local notation|local infix|"
    r"local prefix|local postfix|scoped notation|scoped infix|omit|include|"
    r"noncomputable|macro_rules|syntax|notation|infix|prefix|postfix)\b"
)
ATTR = re.compile(r"^@\[")
DECL_KEYWORD = re.compile(
    r"^(?:(?:private|protected|nonrec|noncomputable|unsafe|partial)\s+)*(theorem|lemma)\b"
)
BODY_CONTINUATION = re.compile(r"^(\||termination_by\b|decreasing_by\b|where\b)")
OPENERS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
CLOSERS = set(OPENERS.values())


def header_context(lines: list[str], upto: int) -> tuple[list[str], list[str]]:
    """Imports and the header lines still in scope just before line ``upto``.

    Walks the file with a stack of namespace/section openings. Closing a scope
    discards every header line captured inside it. Block comments are skipped
    so a ``namespace`` mentioned in a module docstring is not mistaken for one.
    """
    imports: list[str] = []
    ctx: list[str] = []
    stack: list[int] = []
    in_comment = False
    i = 0
    while i < upto:
        line = lines[i]
        s = line.strip()
        if in_comment:
            if "-/" in s:
                in_comment = False
            i += 1
            continue
        if s.startswith("/-"):
            if "-/" not in s[2:]:
                in_comment = True
            i += 1
            continue
        if line.startswith("import "):
            imports.append(line.rstrip())
        elif SCOPE_OPEN.match(line):
            stack.append(len(ctx))
            ctx.append(line.rstrip())
        elif SCOPE_CLOSE.match(line):
            if stack:
                del ctx[stack.pop():]
        elif HEADER.match(line) and not line.rstrip().endswith(" in"):
            block = [line.rstrip()]
            while i + 1 < upto and lines[i + 1].strip() and lines[i + 1][0].isspace():
                i += 1
                block.append(lines[i].rstrip())
            ctx.append("\n".join(block))
        i += 1
    return imports, ctx


def slice_decl(lines: list[str], start: int) -> tuple[int, int, str]:
    """Return (first_line, last_line, docstring) of the declaration at ``start``.

    Attribute lines, the docstring and ``open ... in`` prefixes directly above
    are included, in that order upward, so ``statement`` reproduces the whole
    command as Lean read it. The body ends before the next non-empty line that starts at column zero
    and is not a pattern alternative, ``termination_by``, ``decreasing_by`` or
    ``where``.
    """
    first = start
    while first > 0 and ATTR.match(lines[first - 1]):
        first -= 1
    doc = ""
    if first > 0 and lines[first - 1].rstrip().endswith("-/"):
        j = first - 1
        while j >= 0 and not lines[j].lstrip().startswith("/--"):
            j -= 1
        if j >= 0:
            doc = "\n".join(lines[j:first])
            first = j
    while first > 0 and lines[first - 1].rstrip().endswith(" in"):
        first -= 1
    last = start
    k = start + 1
    while k < len(lines):
        line = lines[k]
        if line.strip() == "" or line[0].isspace() or BODY_CONTINUATION.match(line):
            if line.strip():
                last = k
            k += 1
            continue
        break
    return first, last, doc


def split_body(text: str) -> tuple[str, str, str] | None:
    """Split a declaration at its first top-level ``:=``.

    Returns (statement, proof, mode). In tactic mode the statement ends with
    ``:= by`` and the proof is everything after that ``by``; in term mode the
    statement ends with ``:=``; a declaration proved by pattern matching has no
    ``:=`` at all, so it splits before its first ``|`` alternative and is tagged
    ``equations``. Brackets, string literals and comments are
    skipped so a ``:=`` inside a binder or a comment is not taken for the body.
    """
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            head = text[: i + 2]
            body = text[i + 2:]
            stripped = body.lstrip()
            if stripped.startswith("by") and (
                len(stripped) == 2 or not (stripped[2].isalnum() or stripped[2] == "_")
            ):
                return head + " by", stripped[2:], "tactic"
            return head, body, "term"
        i += 1
    parts = text.splitlines(keepends=True)
    for k, line in enumerate(parts):
        if line.lstrip().startswith("|"):
            return "".join(parts[:k]).rstrip("\n"), "\n" + "".join(parts[k:]), "equations"
    return None


def first_tactic(proof: str) -> str:
    for raw in proof.splitlines():
        s = raw.strip()
        if s and not s.startswith("--"):
            return s.split()[0]
    return ""


def build(index_path: Path, out_dir: Path, limit: int | None = None) -> dict:
    index = json.loads(index_path.read_text(encoding="utf-8"))
    decls = [
        d for d in index["declarations"]
        if d["kind"] in ("theorem", "lemma") and d["trust"] == "kernel"
    ]
    if limit:
        decls = decls[:limit]
    out_dir.mkdir(parents=True, exist_ok=True)
    tactic_f = (out_dir / "seed.jsonl").open("w", encoding="utf-8")
    term_f = (out_dir / "seed_term.jsonl").open("w", encoding="utf-8")
    summary: dict = {
        "source_index": index_path.relative_to(ROOT).as_posix(),
        "kernel_theorems": len(decls),
        "excluded_compiler_trust": sum(
            1 for d in index["declarations"]
            if d["kind"] in ("theorem", "lemma") and d["trust"] != "kernel"
        ),
        "tactic": 0,
        "term": 0,
        "equations": 0,
        "failed": [],
        "by_library": collections.Counter(),
        "first_tactic": collections.Counter(),
    }
    cache: dict[str, list[str]] = {}
    seen: set[str] = set()
    for d in decls:
        if d["name"] in seen:
            continue
        seen.add(d["name"])
        path = ROOT / d["file"]
        if d["file"] not in cache:
            cache[d["file"]] = path.read_text(encoding="utf-8").splitlines()
        lines = cache[d["file"]]
        start = d["line"] - 1
        if start >= len(lines) or not DECL_KEYWORD.match(lines[start]):
            summary["failed"].append({"name": d["name"], "why": "keyword not at indexed line"})
            continue
        first, last, doc = slice_decl(lines, start)
        text = "\n".join(lines[first:last + 1])
        parts = split_body(text)
        if parts is None:
            summary["failed"].append({"name": d["name"], "why": "no top-level :="})
            continue
        statement, proof, mode = parts
        imports, ctx = header_context(lines, first)
        record = {
            "name": d["name"],
            "module": d["module"],
            "file": d["file"],
            "line": d["line"],
            "span": [first + 1, last + 1],
            "kind": d["kind"],
            "ledger": d.get("ledger", []),
            "doc": doc,
            "mode": mode,
            "imports": "\n".join(imports),
            "context": "\n".join(ctx),
            "statement": statement,
            "proof": proof,
            "full": text,
            "proof_lines": sum(1 for line in proof.splitlines() if line.strip()),
            "first_tactic": first_tactic(proof) if mode == "tactic" else "",
        }
        (tactic_f if mode == "tactic" else term_f).write(json.dumps(record, ensure_ascii=False) + "\n")
        summary[mode] += 1
        summary["by_library"][d["module"].split(".")[0]] += 1
        if mode == "tactic":
            summary["first_tactic"][record["first_tactic"]] += 1
    tactic_f.close()
    term_f.close()
    summary["by_library"] = dict(summary["by_library"].most_common())
    summary["first_tactic"] = dict(summary["first_tactic"].most_common(25))
    (out_dir / "seed_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return summary


def check_sample(out_dir: Path, n: int, seed: int) -> int:
    """Recompile ``n`` random tactic records through the kernel gate."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from verify import verify_in_place  # noqa: E402

    records = [json.loads(line) for line in (out_dir / "seed.jsonl").open(encoding="utf-8")]
    random.Random(seed).shuffle(records)
    failures = 0
    for r in records[:n]:
        ok, why, _ = verify_in_place(r, r["proof"])
        print(f"{'ok  ' if ok else 'FAIL'} {r['name']}  {'' if ok else why[:160]}")
        failures += not ok
    print(f"{n - failures}/{n} records recompile under the axiom gate")
    return failures


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--index", type=Path, default=INDEX)
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    ap.add_argument("--limit", type=int, default=None, help="only the first N theorems")
    ap.add_argument("--check", type=int, default=0, metavar="N", help="recompile N random records")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    summary = build(args.index, args.out_dir, args.limit)
    print(json.dumps({k: v for k, v in summary.items() if k != "first_tactic"}, indent=2, ensure_ascii=False))
    print("first tactics:", summary["first_tactic"])
    if args.check:
        return 1 if check_sample(args.out_dir, args.check, args.seed) else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
