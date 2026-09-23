"""Read-only Lean source inventory and deterministic JSON rendering."""
from __future__ import annotations

import collections
import io
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any
import lean_source
from . import identities as _fp_identities
from . import workspace as _fp_workspace


_ATTR = r"@\[[^\]]*\][ \t]*"

"""An attribute block in front of a declaration, on the declaration's own line.

Same line, deliberately.  An attribute written on the line *above* leaves the keyword at the
start of its own line, where the pattern already finds it; letting this group cross a newline
would move the match back onto the attribute and report every such declaration one line early.
"""


_MODIFIER = r"(?:private\s+|protected\s+|noncomputable\s+)*"


DECL = re.compile(
    rf"^[ \t]*(?:{_ATTR})*{_MODIFIER}"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'!?.]*)",
    re.MULTILINE,
)

"""Every declaration a file opens.  Run against :func:`blank_comments` output, never raw text.

Three forms were invisible here and each failed silently, which is the only way this index
fails.  ``@[simp] theorem foo`` -- 70 of them -- had no room for the attribute and were absent
from the index outright.  An indented declaration was unreachable because the pattern anchored
at ``^`` with nothing after it.  And the ``^`` anchor was simultaneously the only guard against
prose: ``formal/`` writes long docstrings, and a line wrapping so that ``theorem`` lands at
column 0 put six English words -- ``of``, ``at``, ``needs``, ``nothing`` -- into the index as
declarations.  Allowing indentation without blanking comments first adds a seventh.  So the two
changes are one change: the anchor stops carrying a job it was never doing on purpose, and
:func:`blank_comments` takes it over.
"""


IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.']*)", re.MULTILINE)


IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+")

"""A bare Lean identifier in prose.  Ledger rows name their theorems this way -- not in
backticks, which is why an early search for backticked names found none at all."""


def sources() -> list[Path]:
    """Every Lean file of the laboratory itself -- never the 12 GB of .lake build output."""
    out: list[Path] = []
    for lib in _fp_workspace.LIBRARIES:
        out.extend(sorted((_fp_workspace.FORMAL / lib).rglob("*.lean")))
        top = _fp_workspace.FORMAL / f"{lib}.lean"
        if top.is_file():
            out.append(top)
    return out


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(_fp_workspace.FORMAL).with_suffix("").parts)


def blank_comments(text: str) -> str:
    """Replace every comment byte with a space, keeping all offsets and newlines in place.

    Offsets are the point.  The declaration scan runs on this, while each declaration's
    docstring and trust are sliced out of the original text at the positions this reports,
    so a blanker that shortened anything would misreport every line after the first comment.

    Lean block comments nest -- ``/- outer /- inner -/ still outer -/`` -- so this scans
    rather than running the non-greedy ``/-.*?-/`` used elsewhere in this file, which closes
    such a comment at the inner ``-/`` and hands the tail back as if it were code.  String
    literals are honoured too, so a ``--`` inside one opens nothing.
    """
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end == -1 else end
            out[i:end] = " " * (end - i)
            i = end
        else:
            i += 1
    return "".join(out)


def _docstring(text: str, start: int) -> str:
    """The ``/-- ... -/`` block immediately above a declaration, if there is one.

    Immediately: nothing but whitespace may sit between the closing ``-/`` and the
    declaration, and the block must be the last one opened.  A regex reaching backwards for
    any earlier ``/--`` attaches one theorem's prose to every theorem below it.
    """
    head = text[:start].rstrip()
    if not head.endswith("-/"):
        return ""
    opened = head.rfind("/--")
    if opened == -1:
        return ""
    body = head[opened + 3: -2]
    if "-/" in body:
        return ""
    return " ".join(body.split())


_DOCSTRING = re.compile(r"/--.*?-/", re.S)


def _trust(body: str) -> str:
    """Trust from the proof, not from the prose around it.

    Docstrings are stripped first.  A body runs to the next declaration, so a docstring
    that *mentions* the compiled-runtime tactic -- one recording that a scan was replaced
    by a structural proof, say -- used to mark the declaration above it compiler-trusted.
    That mislabels in both directions, and this field must not do that.
    """
    body = _DOCSTRING.sub(" ", body)
    if re.search(r"\bsorry\b", body):
        return "open"
    if "native_decide" in body:
        return "compiler"
    return "kernel"


def declares(text: str, name: str, kind: str = "theorem") -> bool:
    """Does `text` declare exactly `name` -- not merely something starting with it?

    519 of the 4,528 declaration names in this corpus are a proper prefix of another, because
    helper lemmas are named by extending their main theorem: `power_bound_compensated_contracts`
    and `power_bound_compensated_contracts_follows`, `power_bound_word` and
    `power_bound_word_strict`.  A guard written as ``f"theorem {name}" in text`` therefore still
    passes after its theorem is deleted, as long as one of those neighbours survives -- which is
    precisely the event such a guard exists to catch.

    It reads the same forms :data:`DECL` does, and for the same reason: this answers "is the
    theorem still here", so every form it cannot read reports a live theorem deleted.  It took
    a bare ``kind`` with room for neither an attribute nor a modifier, so ``@[simp] theorem f``
    and ``private theorem f`` both answered False.  The tail rejects ``!`` and ``?`` as well as
    word characters, since Lean admits all three in a name and ``foo`` must not match ``foo!``.
    """
    return re.search(
        rf"(?:^|\n)[ \t]*(?:{_ATTR})*{_MODIFIER}{kind}\s+{re.escape(name)}(?![A-Za-z0-9_'!?])",
        text,
    ) is not None


def declarations(path: Path) -> list[dict[str, Any]]:
    """Every declaration in one file: what it is called, where it sits, what checks it.

    The scan runs on comment-blanked text and the docstring and trust of each hit are sliced
    from the original at the same offsets -- so prose cannot be read as a declaration, while
    the prose *belonging* to a declaration is still read.
    """
    return lean_source.scan(path.read_text(encoding="utf-8"), module_of(path),
                            path.relative_to(_fp_workspace.ROOT).as_posix())


def imports(path: Path, known: set[str]) -> list[str]:
    """Internal imports only: an edge to a module this repository actually defines."""
    text = io.open(path, encoding="utf-8").read()
    return sorted({m.group(1) for m in IMPORT.finditer(text) if m.group(1) in known})


def ledger_by_file() -> dict[str, list[dict[str, str]]]:
    """Ledger rows keyed by the file their ``lean`` field names, normalised to repo paths."""
    if not _fp_workspace.LEDGER.is_file():
        return {}
    rows = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
    out: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        ref = row.get("lean")
        if not isinstance(ref, str) or not ref.endswith(".lean"):
            continue
        key = _fp_identities.lean_key(ref)
        out[key].append(
            {"id": row["id"], "tag": row["tag"], "statement": row.get("statement", "")}
        )
    return dict(out)


def build() -> dict[str, Any]:
    paths = sources()
    known = {module_of(p) for p in paths}
    by_file = ledger_by_file()
    decls: list[dict[str, Any]] = []
    modules: dict[str, dict[str, Any]] = {}
    for path in paths:
        rel = str(path.relative_to(_fp_workspace.ROOT)).replace("\\", "/")
        found = declarations(path)
        for d in found:
            d["ledger"] = [r["id"] for r in by_file.get(rel, [])]
        decls.extend(found)
        modules[module_of(path)] = {
            "file": rel,
            "imports": imports(path, known),
            "declarations": len(found),
            "ledger": by_file.get(rel, []),
        }
    trust: dict[str, int] = defaultdict(int)
    identities = collections.Counter(d['qualified_name'] for d in decls if d['qualified_name'])
    for d in decls:
        trust[d["trust"]] += 1
        if d['qualified_name'] and identities[d['qualified_name']] > 1:
            d['id'] = f"{d['module']}::{d['qualified_name']}"
    result = {
        "schema": 2,
        "identity_basis": "scoped source; generated/private compiler names require Lean export",
        "modules": modules,
        "declarations": decls,
        "totals": {
            "modules": len(modules),
            "declarations": len(decls),
            "trust": dict(trust),
            "declarations_with_a_ledger_row": sum(1 for d in decls if d["ledger"]),
            "ledger_rows_naming_a_file": sum(len(v) for v in by_file.values()),
        },
    }
    ledger = json.loads(_fp_workspace.LEDGER.read_text(encoding="utf-8")) if _fp_workspace.LEDGER.is_file() else []
    for d in decls:
        d["ledger_exact"] = []
    for row in ledger:
        for name in _fp_identities.row_decls(row):
            matches = _fp_identities.resolve_declarations(result, name, file=_fp_identities.lean_key(row.get("lean")))
            if len(matches) == 1:
                matches[0]["ledger_exact"].append(row["id"])
    for d in decls:
        d["ledger_exact"] = sorted(set(d["ledger_exact"]))
    return result


def render(payload: Any) -> str:
    """The exact bytes every generated artifact here is written as.

    The staleness gate in tests compares the committed file to a fresh
    build through this function, so the two sides cannot drift apart by
    someone changing an indent or a sort on one of them alone.
    """
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def load() -> dict[str, Any]:
    """Reports use current sources; a saved export is never an implicit input."""
    return build()


def _resolve(index: dict[str, Any], target: str) -> str | None:
    """Accept a module name, a repo path, or a path fragment."""
    if target in index["modules"]:
        return target
    needle = target.replace("\\", "/")
    for name, data in index["modules"].items():
        if data["file"] == needle or data["file"].endswith("/" + needle.lstrip("/")):
            return name
    return None
