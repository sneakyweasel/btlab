"""Exact declaration and ledger identities, and source statement excerpts."""
from __future__ import annotations

import io
from typing import Any
from . import workspace as _fp_workspace


def lean_key(ref: object) -> str:
    """Repo-relative key for a ledger row's `lean` field, however it is spelled.

    The ledger spells it both ways: 421 rows give a path relative to `formal/`
    ("Problems/Juggler/X.lean") and 43 give it from the repository root
    ("formal/Problems/Juggler/X.lean"). Prepending "formal/" unconditionally turned the
    second spelling into "formal/formal/...", which matches no file, so those 43 rows
    resolved to zero declarations while every gate stayed green -- the index simply
    reported a smaller surface than the repository has.
    """
    text = str(ref or "").lstrip("/")
    return text if text.startswith("formal/") else "formal/" + text


def resolve_declarations(index: dict[str, Any], name: str, *, module: str | None = None,
                         file: str | None = None, include_private: bool = False) -> list[dict]:
    """Resolve exact identities, then namespace suffixes, preserving every ambiguity."""
    name = name.removeprefix('_root_.')
    candidates = [d for d in index['declarations']
                  if (include_private or d.get('visibility') != 'private')
                  and (module is None or d['module'] == module)
                  and (file is None or d['file'] == file)]
    exact = [d for d in candidates if name in (d.get('qualified_name'), d.get('id'))]
    if exact:
        return exact
    return [d for d in candidates
            if d.get('source_name', d['name']) == name
            or d.get('source_name', d['name']).endswith('.' + name)]


def row_decls(row: dict[str, Any]) -> list[str]:
    """The declarations a ledger row names, as a list, whether it names one or many.

    Most rows resolve to a single theorem and carry ``decl`` as a string. Some do not:
    ``J-cyclemin-walk-ostrowski-arithmetic`` is Paper A's certified-arithmetic inventory and
    names eighteen declarations, seventeen kernel-checked and one (``window_digit_scan``)
    compiler-trusted. A single string cannot describe that row without misreporting one side
    of the kernel boundary, so ``decl`` accepts a list and every consumer reads it through
    here.
    """
    decl = row.get("decl")
    if not decl:
        return []
    return [decl] if isinstance(decl, str) else list(decl)


def signature(decl: dict[str, Any], limit: int = 8) -> str:
    """A declaration's statement, from its header down to the `:=` that starts the proof.

    Nine of the queue's confident candidates carry no docstring, and an entry that offers
    only a name is not answerable: deciding "is this row that theorem?" needs the theorem.
    The signature is what the docstring would have paraphrased.
    """
    if "signature" in decl:
        return decl["signature"]
    try:
        lines = io.open(_fp_workspace.ROOT / decl["file"], encoding="utf-8").read().splitlines()
    except OSError:
        return ""
    out: list[str] = []
    for line in lines[decl["line"] - 1: decl["line"] - 1 + limit]:
        out.append(line.rstrip())
        if ":=" in line or line.rstrip().endswith("by"):
            break
    text = "\n".join(out)
    return text.split(":=")[0].rstrip() if ":=" in text else text
