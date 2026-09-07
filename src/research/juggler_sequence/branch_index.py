"""Generate and check ``attacks/juggler/index.json``.

Do not hand-edit the JSON. Rebuild with
``python -m research.juggler_sequence.branch_index``.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    BRANCHES_ROOT,
    CONJECTURES_ROOT,
    DATA_ROOT,
    DOCS_ROOT,
    INDEX_PATH,
    JUGGLER_DIR,
    LAYERS,
    REPO_ROOT,
)

PACKAGE = REPO_ROOT / "src" / "research" / "juggler_sequence"
TESTS = REPO_ROOT / "tests" / "research" / "juggler_sequence"
LEDGER_PATH = DOCS_ROOT / "theory" / "theorem_ledger.json"

INFRASTRUCTURE = frozenset(
    {
        "__init__",
        "adapter",
        "branch_index",
        "discovery",
        "lean_export",
        "lean_paths",
        "notation_audit",
        "p0_certificate",
        "paper_a_audit",
        "paper_b_audit",
        "paper_b_constants_sweep",
        "paper_b_prefix_count",
        "paper_c_audit",
        "planner",
        "power_itineraries",
        "problem",
        "runner",
        "scout",
        "spec",
    }
)

SUPPORT = frozenset(
    {
        "cycle_floor_hard_seeds",
        "cycle_floor_sensitivity",
        "cycle_run_extremum",
        "cycle_walk_charge_gpu",
        "even_count_five",
        "floor_preimages",
        "hug_realizability",
        "run_suffix_law",
        "s2_window_costing",
        "stage2_mode_accounting",
        "uniform_superquadratic",
        "walk_kbest",
        "walk_kbest_gpu",
        "walk_realizability",
        "walk_runs",
    }
)

# slogan -> branch id. Seeded from the live do-not-reopen list; not 361 slogans.
SLOGAN_ALIASES: dict[str, str] = {
    "baker": "cycle_gap_baker",
    "sdw": "cycle_gap_baker",
    "simons-de weger": "cycle_gap_baker",
    "floor-hardy": "rate_free_floor_hardy",
    "floor hardy": "rate_free_floor_hardy",
    "harvest counting": "harvest_counting",
    "collision factorization": "first_collision",
    "paper a×b merge": "cycle_gap_baker",
    "paper a x b merge": "cycle_gap_baker",
    "dk-arch": "cycle_walk_arch",
    "dk arch": "cycle_walk_arch",
    "kernel localize": "kernel_localize",
    "three-halves": "three_halves_mod_one",
    "k3": "k3_rate_free",
}

# probe stem -> dossier stem (without the ``juggler_`` prefix)
DOSSIER_ALIASES: dict[str, str] = {
    "cycle_itinerary": "cycle_word",
    "cycle_itinerary_functional": "cycle_word_functional",
    "cycle_itinerary_order": "cycle_word_order",
    "cycle_length_eight": "length_eight_cycles",
    "cycle_length_nine": "length_nine_three_even",
    "cycle_length_seven": "length_seven_cycles",
    "gapped_cycle_itinerary": "gapped_cycle_word",
    "itinerary_language": "word_language",
    "odd_odd_residuals": "odd_odd_residual",
    "oeoee_audit": "oeoee_production",
    "tao_reduction": "tao_almost_bounded",
    "two_adic_bridge": "2adic_integer_bridge",
    "v3_audit": "v3_production",
    "v4_audit": "v4_production",
    "v5_audit": "v5_production",
    "v6_audit": "v6_production",
}

_DECISIONS = ("PROMOTE", "PARK", "CLOSE")
_LEAN_FILE = re.compile(r"\b([A-Za-z][A-Za-z0-9]*)\.lean\b")
_JUGGLE_STEM = re.compile(r"(?:problems/)?juggler_([a-z0-9_]+)")
_NK_SKIP = frozenset({"Kinds", "Source inventory", "Agent filter"})
NK_PATH = DOCS_ROOT / "negative_knowledge.md"


def _aliases_for(stem: str) -> list[str]:
    return sorted(slogan for slogan, target in SLOGAN_ALIASES.items() if target == stem)


def parse_nk_clusters(text: str | None = None) -> dict[str, str]:
    """Map dossier/probe stem -> ``##`` heading in ``negative_knowledge.md``."""
    body = text if text is not None else (
        NK_PATH.read_text(encoding="utf-8") if NK_PATH.is_file() else ""
    )
    mapping: dict[str, str] = {}
    for part in re.split(r"^## ", body, flags=re.M)[1:]:
        heading, _, _rest = part.partition("\n")
        heading = heading.strip()
        if heading in _NK_SKIP:
            continue
        for stem in _JUGGLE_STEM.findall(part):
            mapping.setdefault(stem, heading)
    return mapping


def _nk_cluster_for(stem: str, dossier_stem: str, nk_map: dict[str, str]) -> str | None:
    for key in (stem, dossier_stem):
        if key and key in nk_map:
            return nk_map[key]
    return None


def _rel(path: Path | None) -> str | None:
    if path is None:
        return None
    return path.relative_to(REPO_ROOT).as_posix()


def _decision(text: str) -> str | None:
    parts = re.split(r"^## Decision$", text, flags=re.M)
    if len(parts) < 2:
        return None
    section = re.split(r"^## ", parts[1], flags=re.M)[0]
    found = [word for word in _DECISIONS if word in section]
    if not found:
        return None
    return found[0]


def _snake_to_camel(stem: str) -> str:
    return "".join(part.capitalize() for part in stem.split("_"))


def _dossier_for(stem: str) -> Path | None:
    name = DOSSIER_ALIASES.get(stem, stem)
    path = BRANCHES_ROOT / f"juggler_{name}.md"
    return path if path.is_file() else None


def _test_for(stem: str) -> Path | None:
    path = TESTS / f"test_{stem}.py"
    return path if path.is_file() else None


def _data_for(*stems: str) -> Path | None:
    for stem in stems:
        if not stem:
            continue
        path = DATA_ROOT / stem
        if path.is_dir():
            return path
    return None


def _lean_for(stem: str, probe: Path | None) -> list[str]:
    hits: list[str] = []
    camel = _snake_to_camel(stem)
    if camel in LAYERS:
        hits.append(_rel(LAYERS[camel]) or "")
    if probe is not None and probe.is_file():
        body = probe.read_text(encoding="utf-8")
        for name in _LEAN_FILE.findall(body):
            layer = JUGGLER_DIR / f"{name}.lean"
            rel = _rel(layer)
            if layer.is_file() and rel and rel not in hits:
                hits.append(rel)
    return [h for h in hits if h]


def _conjectures_for(*stems: str) -> list[str]:
    ids: list[str] = []
    seen: set[str] = set()
    for folder in ("active", "refuted", "proved", "archived"):
        root = CONJECTURES_ROOT / folder
        if not root.is_dir():
            continue
        for path in root.glob("*.json"):
            key = path.stem
            if any(stem and (key == f"juggler_{stem}" or key.endswith(f"_{stem}")) for stem in stems):
                if key not in seen:
                    seen.add(key)
                    ids.append(key)
    return ids


def _ledger_ids(source_paths: list[str], rows: list[dict[str, Any]]) -> list[str]:
    if not source_paths:
        return []
    found: list[str] = []
    for row in rows:
        src = str(row.get("source") or "").replace("\\", "/")
        tests = [str(t).replace("\\", "/") for t in (row.get("tests") or [])]
        if any(src.endswith(p) or p in src for p in source_paths):
            found.append(row["id"])
            continue
        if any(any(t.endswith(p) or p in t for p in source_paths) for t in tests):
            found.append(row["id"])
    return found


def _kind(stem: str, probe: Path | None, test: Path | None, dossier: Path | None) -> str:
    if stem in INFRASTRUCTURE:
        return "infrastructure"
    if stem in SUPPORT:
        return "support"
    if probe is not None and test is not None and dossier is not None:
        return "branch"
    if probe is None and dossier is not None:
        return "dossier_only"
    return "support"


def _row(
    *,
    stem: str,
    probe: Path | None,
    test: Path | None,
    dossier: Path | None,
    ledger_rows: list[dict[str, Any]],
    nk_map: dict[str, str],
) -> dict[str, Any]:
    dossier_stem = ""
    if dossier is not None:
        dossier_stem = dossier.stem.removeprefix("juggler_")
    decision = _decision(dossier.read_text(encoding="utf-8")) if dossier else None
    sources = [p for p in (_rel(probe), _rel(test), _rel(dossier)) if p]
    return {
        "id": stem,
        "kind": _kind(stem, probe, test, dossier),
        "probe": _rel(probe),
        "test": _rel(test),
        "dossier": _rel(dossier),
        "data_dir": _rel(_data_for(stem, dossier_stem)),
        "lean": _lean_for(stem, probe),
        "conjecture": _conjectures_for(stem, dossier_stem),
        "decision": decision,
        "ledger_ids": _ledger_ids(sources, ledger_rows),
        "aliases": _aliases_for(stem),
        "nk_cluster": _nk_cluster_for(stem, dossier_stem, nk_map),
    }


def build_index() -> dict[str, Any]:
    ledger_rows: list[dict[str, Any]] = []
    if LEDGER_PATH.is_file():
        ledger_rows = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))

    probes = {p.stem: p for p in sorted(PACKAGE.glob("*.py"))}
    dossiers = {
        p.stem.removeprefix("juggler_"): p
        for p in sorted(BRANCHES_ROOT.glob("juggler_*.md"))
    }
    nk_map = parse_nk_clusters()
    used_dossiers: set[str] = set()
    rows: list[dict[str, Any]] = []

    for stem, probe in probes.items():
        dossier = _dossier_for(stem)
        if dossier is not None:
            used_dossiers.add(dossier.stem.removeprefix("juggler_"))
        rows.append(
            _row(
                stem=stem,
                probe=probe,
                test=_test_for(stem),
                dossier=dossier,
                ledger_rows=ledger_rows,
                nk_map=nk_map,
            )
        )

    for stem, dossier in dossiers.items():
        if stem in used_dossiers:
            continue
        rows.append(
            _row(
                stem=stem,
                probe=None,
                test=None,
                dossier=dossier,
                ledger_rows=ledger_rows,
                nk_map=nk_map,
            )
        )

    rows.sort(key=lambda row: (row["kind"], row["id"]))
    return {"branches": rows}


def dumps(index: dict[str, Any]) -> str:
    return json.dumps(index, indent=2, ensure_ascii=False) + "\n"


def write_index(index: dict[str, Any] | None = None) -> Path:
    payload = dumps(index if index is not None else build_index())
    INDEX_PATH.parent.mkdir(parents=True, exist_ok=True)
    INDEX_PATH.write_text(payload, encoding="utf-8")
    return INDEX_PATH


def check_index() -> list[str]:
    """Return human-readable problems; empty means the committed file is current."""
    problems: list[str] = []
    built = build_index()
    if not INDEX_PATH.is_file():
        return [f"missing {INDEX_PATH.relative_to(REPO_ROOT).as_posix()}"]
    committed = INDEX_PATH.read_text(encoding="utf-8")
    if committed != dumps(built):
        problems.append("attacks/juggler/index.json is stale; rebuild with python -m research.juggler_sequence.branch_index")

    by_id = {row["id"]: row for row in built["branches"]}
    if len(by_id) != len(built["branches"]):
        problems.append("duplicate branch ids")

    for row in built["branches"]:
        if row["kind"] != "branch":
            continue
        for key in ("probe", "test", "dossier", "decision"):
            if not row.get(key):
                problems.append(f"{row['id']}: branch missing {key}")

    for path in PACKAGE.glob("*.py"):
        if path.stem not in by_id:
            problems.append(f"probe not indexed: {path.name}")
    for path in BRANCHES_ROOT.glob("juggler_*.md"):
        stem = path.stem.removeprefix("juggler_")
        if stem not in by_id and stem not in {DOSSIER_ALIASES.get(s, s) for s in by_id}:
            aliased = any(DOSSIER_ALIASES.get(s) == stem for s in by_id)
            if not aliased:
                problems.append(f"dossier not indexed: {path.name}")
    return problems


def _rows_by_id(index: dict[str, Any] | None = None) -> dict[str, dict[str, Any]]:
    payload = index if index is not None else build_index()
    return {row["id"]: row for row in payload["branches"]}


def show_row(stem: str, index: dict[str, Any] | None = None) -> dict[str, Any] | None:
    return _rows_by_id(index).get(stem)


def format_show(row: dict[str, Any]) -> str:
    aliases = ", ".join(row.get("aliases") or []) or "—"
    lean = ", ".join(row.get("lean") or []) or "—"
    ledger = ", ".join(row.get("ledger_ids") or []) or "—"
    lines = [
        f"id: {row['id']}",
        f"kind: {row['kind']}",
        f"probe: {row.get('probe') or '—'}",
        f"test: {row.get('test') or '—'}",
        f"dossier: {row.get('dossier') or '—'}",
        f"decision: {row.get('decision') or '—'}",
        f"data_dir: {row.get('data_dir') or '—'}",
        f"lean: {lean}",
        f"ledger_ids: {ledger}",
        f"aliases: {aliases}",
        f"nk_cluster: {row.get('nk_cluster') or '—'}",
    ]
    return "\n".join(lines)


def search_rows(query: str, index: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    needle = query.casefold()
    payload = index if index is not None else build_index()
    hits: list[dict[str, Any]] = []
    for row in payload["branches"]:
        dossier_stem = ""
        if row.get("dossier"):
            dossier_stem = Path(row["dossier"]).stem.removeprefix("juggler_")
        hay = " ".join(
            [
                row["id"],
                dossier_stem,
                " ".join(row.get("aliases") or []),
                row.get("nk_cluster") or "",
            ]
        ).casefold()
        if needle in hay:
            hits.append(row)
    return hits


_STEM = re.compile(r"^[a-z][a-z0-9_]*$")

_PROBE_STUB = '''"""Phase-0 probe for ``{stem}``.

Fill the mathematical question. Not a halt theorem.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "{stem}"
'''

_TEST_STUB = '''"""Tests for ``{stem}``."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_{stem}.md").is_file()
'''


def render_new_branch(stem: str) -> dict[str, str]:
    """Return probe / test / dossier texts. Does not write."""
    if not _STEM.fullmatch(stem):
        raise ValueError(f"invalid branch id: {stem}")
    template = (BRANCHES_ROOT / "TEMPLATE.md").read_text(encoding="utf-8")
    dossier = template.replace("# Problem template", f"# Juggler `{stem}`", 1)
    dossier = dossier.replace(
        "Copy this page to `docs/problems/<id>.md` and add `src/research/<id>/` without\n"
        "editing `bt.*`.",
        f"Phase-0 dossier for `{stem}`. Fill `Already killed by?` before implementation.",
        1,
    )
    return {
        "probe": _PROBE_STUB.format(stem=stem),
        "test": _TEST_STUB.format(stem=stem),
        "dossier": dossier,
    }


def new_branch_paths(stem: str) -> dict[str, Path]:
    return {
        "probe": PACKAGE / f"{stem}.py",
        "test": TESTS / f"test_{stem}.py",
        "dossier": BRANCHES_ROOT / f"juggler_{stem}.md",
    }


def write_new_branch(stem: str) -> list[Path]:
    texts = render_new_branch(stem)
    paths = new_branch_paths(stem)
    existing = [p for p in paths.values() if p.exists()]
    if existing:
        shown = ", ".join(p.relative_to(REPO_ROOT).as_posix() for p in existing)
        raise FileExistsError(f"already exists: {shown}")
    written: list[Path] = []
    for key, path in paths.items():
        path.write_text(texts[key], encoding="utf-8", newline="\n")
        written.append(path)
    write_index()
    return written


def format_search(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "no matches"
    lines = [f"{'id':<32} {'decision':<8} nk_cluster"]
    for row in rows:
        cluster = row.get("nk_cluster") or "—"
        decision = row.get("decision") or "—"
        lines.append(f"{row['id']:<32} {decision:<8} {cluster}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the committed index is stale")
    sub = parser.add_subparsers(dest="cmd")
    show_p = sub.add_parser("show", help="print one branch row")
    show_p.add_argument("id")
    search_p = sub.add_parser("search", help="match id, aliases, or nk_cluster")
    search_p.add_argument("query")
    new_p = sub.add_parser("new", help="write probe, test, and dossier stubs")
    new_p.add_argument("stem")
    args = parser.parse_args(argv)
    if args.check or args.cmd == "check":
        problems = check_index()
        if problems:
            print("\n".join(problems))
            return 1
        return 0
    if args.cmd == "show":
        row = show_row(args.id)
        if row is None:
            print(f"unknown id: {args.id}")
            return 1
        print(format_show(row))
        return 0
    if args.cmd == "search":
        hits = search_rows(args.query)
        print(format_search(hits))
        return 0 if hits else 1
    if args.cmd == "new":
        try:
            written = write_new_branch(args.stem)
        except (ValueError, FileExistsError) as exc:
            print(exc)
            return 1
        for path in written:
            print(path.relative_to(REPO_ROOT).as_posix())
        print("remaining gates: fill Already killed by?; ledger only if named;")
        print("CLOSE/REFUTED -> docs/negative_knowledge.md; rebuild is done")
        return 0
    path = write_index()
    print(path.relative_to(REPO_ROOT).as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
