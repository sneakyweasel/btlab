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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the committed index is stale")
    args = parser.parse_args(argv)
    if args.check:
        problems = check_index()
        if problems:
            print("\n".join(problems))
            return 1
        return 0
    path = write_index()
    print(path.relative_to(REPO_ROOT).as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
