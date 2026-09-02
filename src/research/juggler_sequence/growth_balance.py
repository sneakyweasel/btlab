"""Prefix growth / retention balance on AboveAnchor orbits.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a new cell, not a Q-descriptor, not Amplify, not sum-rho.

The proposed survival laws are

    3^{O_k} >= 2^k
    F_k >= n^{2^k - 3^{O_k}}

where x_k^{2^k} = n^{3^{O_k}} F_k. Phase 0 asks whether either
law is independent of power_bound_word and x_k >= n.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_growth_balance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_growth_balance.md"

CLASS_CLOSED = "GROWTH_BALANCE_CLOSED"
CLASS_GREEN = "GROWTH_BALANCE_GREEN"
CLASS_INCOMPLETE = "GROWTH_BALANCE_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
WINDOW_HI = 201
EXACT_POW_K_MAX = 8

EXISTING_LEAN = (
    "power_bound_word",
    "aboveAnchor_not_envelope_drop",
    "global_defect_identity",
    "power_bound_compensated_contracts",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "GrowthBalance",
    "PrefixBalance",
    "SurvivalBudget",
    "RetentionBudget",
    "EscapeBudget",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "GrowthBalance.lean",
    JUGGLER_DIR / "PrefixBalance.lean",
    JUGGLER_DIR / "SurvivalBudget.lean",
)


def gamma_noncontracting(odd_count: int, length: int) -> bool:
    """Ideal exponent balance 3^O >= 2^k. Integer compare only."""

    return 3**odd_count >= 2**length


def retention_required_holds(n: int, x: int) -> bool:
    """F_k >= n^{2^k - 3^{O_k}} is exactly x >= n."""

    return x >= n


def exact_retention_compare(n: int, x: int, k: int) -> bool:
    """x^{2^k} >= n^{2^k}. Same as x >= n for n, x >= 0."""

    return x ** (2**k) >= n ** (2**k)


def word_and_counts(
    path: tuple[int, ...],
) -> tuple[str, list[dict[str, Any]], list[int]]:
    if len(path) < 2:
        return "", []
    letters: list[str] = []
    rows: list[dict[str, Any]] = []
    odd_count = 0
    even_count = 0
    run_len = 0
    runs: list[int] = []
    in_odd = False
    for k in range(1, len(path)):
        prev = path[k - 1]
        x = path[k]
        if prev % 2 == 1:
            letters.append("O")
            odd_count += 1
            if in_odd:
                run_len += 1
            else:
                in_odd = True
                run_len = 1
        else:
            letters.append("E")
            even_count += 1
            if in_odd:
                runs.append(run_len)
                in_odd = False
                run_len = 0
        above = x >= path[0]
        gamma_ok = gamma_noncontracting(odd_count, k)
        rows.append(
            {
                "k": k,
                "x": x,
                "O": odd_count,
                "E": even_count,
                "above": above,
                "gamma_ok": gamma_ok,
                "three_pow_O": 3**odd_count,
                "two_pow_k": 2**k,
                "retention_required_holds": retention_required_holds(path[0], x),
                "identity_ok": retention_required_holds(path[0], x) == above,
            }
        )
    if in_odd:
        runs.append(run_len)
    return "".join(letters), rows, runs


def prefix_table(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    word, rows, runs = word_and_counts(path)
    drop = rows[-1]
    last_above = next(row for row in reversed(rows) if row["above"])
    above_gamma_fail = [
        row["k"] for row in rows if row["above"] and not row["gamma_ok"]
    ]
    identity_fail = [row["k"] for row in rows if not row["identity_ok"]]
    mean_run = (sum(runs) / len(runs)) if runs else None
    return {
        "n": n,
        "drop_k": drop["k"],
        "x_drop": drop["x"],
        "word": word,
        "runs": runs,
        "mean_run": mean_run,
        "last_above": last_above,
        "drop": drop,
        "drop_formally_contracting": drop["three_pow_O"] < drop["two_pow_k"],
        "above_gamma_fail": above_gamma_fail,
        "identity_fail": identity_fail,
        "prefixes": rows,
    }


def leftover_tables() -> dict[str, dict[str, Any]]:
    return {str(n): prefix_table(n) for n in CONTROLS}


def contrast_tables() -> dict[str, dict[str, Any]]:
    return {str(n): prefix_table(n) for n in CONTRAST}


def window_scan(hi: int = WINDOW_HI) -> dict[str, Any]:
    """Odd n < hi: AboveAnchor prefixes never violate 3^O >= 2^k."""

    checked = 0
    above_gamma_fail = 0
    identity_fail = 0
    formal_drop = 0
    compensated_drop = 0
    for n in range(3, hi, 2):
        table = prefix_table(n)
        checked += 1
        if table["above_gamma_fail"]:
            above_gamma_fail += 1
        if table["identity_fail"]:
            identity_fail += 1
        if table["drop_formally_contracting"]:
            formal_drop += 1
        else:
            compensated_drop += 1
    return {
        "hi": hi,
        "checked": checked,
        "above_gamma_fail": above_gamma_fail,
        "identity_fail": identity_fail,
        "formal_drop": formal_drop,
        "compensated_drop": compensated_drop,
    }


def identity_samples() -> list[dict[str, Any]]:
    """Small exact-power checks: F >= F_min iff x >= n."""

    samples: list[dict[str, Any]] = []
    for n in (3, 9, 15, 37, 365):
        current = n
        odd_count = 0
        for k in range(1, EXACT_POW_K_MAX + 1):
            if current % 2 == 1:
                odd_count += 1
            nxt = floor_power(current)
            samples.append(
                {
                    "n": n,
                    "k": k,
                    "x": nxt,
                    "O": odd_count,
                    "exact_compare": exact_retention_compare(n, nxt, k),
                    "above": nxt >= n,
                    "match": exact_retention_compare(n, nxt, k) == (nxt >= n),
                }
            )
            current = nxt
    return samples


def run_probe() -> dict[str, Any]:
    leftovers = leftover_tables()
    contrast = contrast_tables()
    window = window_scan()
    samples = identity_samples()
    leftover_gamma_fail = any(row["above_gamma_fail"] for row in leftovers.values())
    leftover_identity_fail = any(row["identity_fail"] for row in leftovers.values())
    leftover_formal_drop = all(
        row["drop_formally_contracting"] for row in leftovers.values()
    )
    sample_ok = all(item["match"] for item in samples)
    return {
        "basin": "ordinary_integers",
        "leftovers": leftovers,
        "contrast": contrast,
        "window": window,
        "identity_samples": samples,
        "leftover_gamma_fail": leftover_gamma_fail,
        "leftover_identity_fail": leftover_identity_fail,
        "leftover_formal_drop": leftover_formal_drop,
        "sample_identity_ok": sample_ok,
        "window_identity_ok": window["identity_fail"] == 0,
        "window_gamma_ok": window["above_gamma_fail"] == 0,
        "letter_chain": False,
        "q_descriptor_reopen": False,
        "amplify_reopen": False,
        "growth_balance_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "GrowthBalance" not in paper
        and "PrefixBalance" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["q_descriptor_reopen"]
        or scan["amplify_reopen"]
        or scan["halt_theorem"]
        or scan["growth_balance_lean"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    identity_ok = (
        scan["sample_identity_ok"]
        and scan["window_identity_ok"]
        and not scan["leftover_identity_fail"]
        and scan["window_gamma_ok"]
        and not scan["leftover_gamma_fail"]
    )
    if identity_ok:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "F_k >= n^{2^k-3^{O_k}} is x_k >= n; "
                "3^{O_k} >= 2^k is the word envelope plus AboveAnchor"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": "identity failed; the budget would be independent",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "independent_retention_budget": False,
            "q_descriptor_reopen": False,
            "amplify_reopen": False,
            "growth_balance_lean": False,
            "letter_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_growth_balance",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact 3^O vs 2^k; F >= F_min iff x >= n; "
            "leftovers 365/501/1517/6187; odd n<201"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler prefix growth / retention balance",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Prefix-level growth and floor-retention on AboveAnchor orbits.",
        "Not a halt theorem. Not a new cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     independent prefix growth/retention law",
        "Novelty hypothesis      F_k >= n^{2^k-3^{O_k}} is a new budget",
        "Maximum Phase-0 scope   leftovers; odd n<201; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- leftover identity fail: `{scan['leftover_identity_fail']}`",
        f"- leftover gamma fail: `{scan['leftover_gamma_fail']}`",
        f"- leftover formal drop: `{scan['leftover_formal_drop']}`",
        f"- window identity ok: `{scan['window_identity_ok']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Leftovers",
        "",
    ]
    for n in CONTROLS:
        row = scan["leftovers"][str(n)]
        last = row["last_above"]
        drop = row["drop"]
        lines.append(
            f"- `{n}`: word=`{row['word']}` runs=`{row['runs']}` "
            f"last_above k=`{last['k']}` x=`{last['x']}` "
            f"3^O=`{last['three_pow_O']}` 2^k=`{last['two_pow_k']}`; "
            f"drop k=`{drop['k']}` x=`{drop['x']}` "
            f"3^O=`{drop['three_pow_O']}` 2^k=`{drop['two_pow_k']}` "
            f"formal=`{row['drop_formally_contracting']}`"
        )
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    for n in CONTROLS:
        row = payload["scan"]["leftovers"][str(n)]
        print(n, row["word"], row["runs"], row["drop_formally_contracting"])


if __name__ == "__main__":
    main()
