"""First-even freeze and primitive one-step-preimage geometry.

Not a Research Engine control-layer experiment. The first even step
freezes every suffix on the square-root one-step preimage. Odd
one-step preimages contain at most one integer. Not a halt theorem
and not a preimage-tree calculus.
"""

from __future__ import annotations

import json
from itertools import product
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_floor_cells.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_floor_cells.md"

CLASS_FREEZE = "FIRST_E_FREEZE_GREEN"
CLASS_CALC = "CELL_CALCULUS_GREEN"
CLASS_FAMILY = "CELL_FAMILY_FOUND"
CLASS_EXPENSIVE = "CELL_GEOMETRY_TOO_EXPENSIVE"
CLASS_DUAL = "CELL_DUALITY_COUNTEREXAMPLE"

Q_MAX = 80
K_MAX = 6
ODD_M_MAX = 500

LEAN_THEOREMS = (
    "even_preimage_iff",
    "odd_preimage_iff",
    "preimage_same_next_state",
    "iterate_cons_even",
    "iterate_cons_odd",
    "first_even_freeze",
    "first_odd_freeze",
    "suffix_same_output_on_preimage",
    "first_even_contracts_iff",
    "eoo_from_first_even",
    "constant_cell_trichotomy",
    "odd_preimage_unique",
    "floorPower_eoo_contracts_iff",
    "eoo_contracts_on_preimage",
    "power_bound_compensated_contracts",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "power_bound_compensated_contracts_follows",
)


def even_preimage(q: int) -> tuple[int, int]:
    if q < 0:
        raise ValueError("even_preimage requires a nonnegative integer")
    return q * q, (q + 1) * (q + 1)


def even_preimage_width(q: int) -> int:
    lo, hi = even_preimage(q)
    return hi - lo


def odd_preimage_integers(m: int) -> list[int]:
    """Integers n with m^2 ≤ n^3 < (m+1)^2. At most one by odd_preimage_unique."""

    if m < 0:
        raise ValueError("odd_preimage_integers requires a nonnegative integer")
    lo2, hi2 = m * m, (m + 1) * (m + 1)
    lo, hi = 0, m + 3
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < lo2:
            lo = mid + 1
        else:
            hi = mid
    n_min = lo
    lo, hi = 0, 2 * m + 5
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < hi2:
            lo = mid + 1
        else:
            hi = mid
    n_max = lo - 1
    return list(range(n_min, n_max + 1)) if n_max >= n_min else []


def cell_regime(q: int, output: int) -> str:
    lo, hi = even_preimage(q)
    if output < lo:
        return "all_contract"
    if output >= hi:
        return "all_expand"
    return "mixed"


def first_even_image(n: int, suffix: str) -> int:
    """T_{E v}(n) via the freeze: T_v(⌊√n⌋)."""

    if n < 1 or n % 2 == 1:
        raise ValueError("first_even_image requires a positive even integer")
    return image_after(isqrt(n), suffix)


def scan_odd_preimage_widths(*, m_max: int = ODD_M_MAX) -> dict[str, Any]:
    empty = 0
    singleton = 0
    multi = 0
    examples = []
    for m in range(0, m_max + 1):
        ns = odd_preimage_integers(m)
        if len(ns) == 0:
            empty += 1
        elif len(ns) == 1:
            singleton += 1
        else:
            multi += 1
            if len(examples) < 4:
                examples.append({"m": m, "n": ns})
    return {
        "m_max": m_max,
        "empty": empty,
        "singleton": singleton,
        "multi": multi,
        "multi_examples": examples,
        "even_widths": {str(q): even_preimage_width(q) for q in (1, 3, 10, 100)},
    }


def scan_first_even_freeze(*, q_max: int = Q_MAX) -> dict[str, Any]:
    words = ("EOO", "EOOO", "EEOO", "EOEO", "EEOOOO")
    rows = []
    failures = []
    for word in words:
        ok = 0
        suffix = word[1:]
        for n in range(2, (q_max + 1) ** 2, 2):
            if not follows_itinerary(n, word):
                continue
            left = image_after(n, word)
            right = first_even_image(n, suffix)
            if left != right:
                failures.append({"word": word, "n": n, "left": left, "right": right})
            else:
                ok += 1
        rows.append({"word": word, "checked": ok})
    return {"q_max": q_max, "rows": rows, "failures": failures}


def scan_first_odd_freeze(*, n_max: int = 400) -> dict[str, Any]:
    words = ("OOE", "OEO", "OOOE")
    rows = []
    failures = []
    for word in words:
        ok = 0
        suffix = word[1:]
        for n in range(1, n_max + 1, 2):
            if not follows_itinerary(n, word):
                continue
            left = image_after(n, word)
            right = image_after(isqrt(n * n * n), suffix)
            if left != right:
                failures.append({"word": word, "n": n})
            else:
                ok += 1
        rows.append({"word": word, "checked": ok})
    return {"n_max": n_max, "rows": rows, "failures": failures}


def positive_drift(word: str) -> bool:
    return 3 ** word.count("O") > 2 ** len(word)


def scan_first_even_cells(*, q_max: int = Q_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    words = []
    for k in range(3, k_max + 1):
        for letters in product("EO", repeat=k - 1):
            word = "E" + "".join(letters)
            if positive_drift(word):
                words.append(word)
    records = []
    interesting = []
    for word in words:
        suffix = word[1:]
        regimes = {"all_contract": 0, "all_expand": 0, "mixed": 0, "realized_q": 0}
        starts: list[int] = []
        notes = []
        for q in range(1, q_max + 1):
            if suffix and not follows_itinerary(q, suffix):
                continue
            regimes["realized_q"] += 1
            output = image_after(q, suffix)
            regime = cell_regime(q, output)
            regimes[regime] += 1
            lo, hi = even_preimage(q)
            cell_starts = [
                n
                for n in range(max(lo, 2), hi)
                if n % 2 == 0 and follows_itinerary(n, word) and n > output
            ]
            if regime != "all_expand":
                notes.append(
                    {
                        "q": q,
                        "regime": regime,
                        "output": output,
                        "cell": [lo, hi],
                        "starts": cell_starts,
                    }
                )
                starts.extend(cell_starts)
        record = {
            "word": word,
            "k": len(word),
            "odd_count": word.count("O"),
            "regimes": regimes,
            "contracting_starts": starts,
            "non_expanding_cells": notes,
        }
        records.append(record)
        if notes:
            interesting.append(record)
    return {
        "q_max": q_max,
        "k_max": k_max,
        "word_count": len(words),
        "words": records,
        "interesting": interesting,
    }


def eeo_oooo_witnesses() -> list[dict[str, Any]]:
    rows = []
    for n in (4, 6, 8):
        q = isqrt(n)
        rows.append(
            {
                "n": n,
                "q": q,
                "word": "EEOOOO",
                "image": image_after(n, "EEOOOO"),
                "frozen": first_even_image(n, "EOOOO"),
                "regime": cell_regime(q, image_after(q, "EOOOO")),
                "follows": follows_itinerary(n, "EEOOOO"),
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "certificate_present": all(
            f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "no_cell_tree": "inductive FloorCell" not in text and "structure CellTree" not in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    freeze = scan["first_even_freeze"]
    odd_freeze = scan["first_odd_freeze"]
    widths = scan["odd_cell_widths"]
    cells = scan["first_even_cells"]
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if freeze["failures"] or odd_freeze["failures"]:
        return {
            "classification": CLASS_DUAL,
            "reason": "a freeze identity failed on a realized start",
        }
    if widths["multi"]:
        return {
            "classification": CLASS_DUAL,
            "reason": "an odd floor cell contained two integers",
        }
    family = [
        rec
        for rec in cells["interesting"]
        if len({note["q"] for note in rec["non_expanding_cells"]}) >= 4
    ]
    if family:
        return {
            "classification": CLASS_FAMILY,
            "reason": (
                "a positive-drift first-even word had four or more "
                "non-expanding square-root cells"
            ),
        }
    if not lean_ok:
        return {
            "classification": CLASS_EXPENSIVE,
            "reason": "the geometry is visible computationally but the Lean API is incomplete",
        }
    eoo = next(rec for rec in cells["words"] if rec["word"] == "EOO")
    eeo = next((rec for rec in cells["words"] if rec["word"] == "EEOOOO"), None)
    if eoo["contracting_starts"] == [2, 12, 14] and eeo and eeo["contracting_starts"] == [4, 6, 8]:
        return {
            "classification": CLASS_FREEZE,
            "secondary": CLASS_CALC,
            "reason": (
                "T_Ev(n)=T_v(⌊√n⌋) on every square-root cell; odd cells "
                "are unique so an initial O does not freeze a range; EOO "
                "is the mixed-cell case and EEOOOO is an entire-cell case"
            ),
        }
    return {
        "classification": CLASS_FREEZE,
        "reason": (
            "the first-even freeze and odd-cell uniqueness hold; EOO is "
            "the calibration mixed cell"
        ),
    }


def run_probe(*, q_max: int = Q_MAX, k_max: int = K_MAX, m_max: int = ODD_M_MAX) -> dict[str, Any]:
    return {
        "q_max": q_max,
        "k_max": k_max,
        "m_max": m_max,
        "odd_cell_widths": scan_odd_preimage_widths(m_max=m_max),
        "first_even_freeze": scan_first_even_freeze(q_max=q_max),
        "first_odd_freeze": scan_first_odd_freeze(),
        "first_even_cells": scan_first_even_cells(q_max=q_max, k_max=k_max),
        "eeoooo_witnesses": eeo_oooo_witnesses(),
        "eoo_recovered": [2, 12, 14],
    }


def probe_payload(*, q_max: int = Q_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(q_max=q_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_floor_cells",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "suffix evaluation at q only; odd-cell cardinalities by exact "
            "integer cubes; no huge envelope powers"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    widths = scan["odd_cell_widths"]
    cells = scan["first_even_cells"]
    lines = [
        "# Juggler floor-cell geometry",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. The first even letter freezes every",
        "suffix on the square-root cell. Odd cells are singletons.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Is T_Ev(n)=T_v(⌊√n⌋) reusable, and do",
        "                        positive-drift Ev words have infinitely",
        "                        many contraction cells?",
        "Novelty hypothesis      First-even freeze plus a threshold",
        "                        trichotomy; odd cells are too thin",
        "Falsifier               Freeze fails, or odd cells are wide",
        "Existing machinery      inverse-floor iff, EOO cell threshold",
        "Maximum Phase-0 scope   Generic freeze; recover EOO; Ev scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- q domain: `q <= {scan['q_max']}`",
        f"- word length: `k <= {scan['k_max']}`",
        f"- odd-cell m domain: `m <= {scan['m_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Primitive cells",
        "",
        f"- even widths q=1,3,10,100: `{widths['even_widths']}`",
        f"- odd cells: empty `{widths['empty']}`, singleton `{widths['singleton']}`, multi `{widths['multi']}`",
        "",
        "## Freeze checks",
        "",
        f"- first-even failures: `{len(scan['first_even_freeze']['failures'])}`",
        f"- first-odd failures: `{len(scan['first_odd_freeze']['failures'])}`",
        "",
        "## Positive-drift first-even cells",
        "",
    ]
    for rec in cells["interesting"]:
        lines.append(
            f"- `{rec['word']}` starts `{rec['contracting_starts']}` "
            f"non-expanding cells `{rec['non_expanding_cells']}`"
        )
    lines.extend(
        [
            "",
            "## EEOOOO entire-cell witnesses",
            "",
        ]
    )
    for row in scan["eeoooo_witnesses"]:
        lines.append(
            f"- n=`{row['n']}` q=`{row['q']}` T^6=`{row['image']}` "
            f"regime=`{row['regime']}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no cell tree: `{lean.get('no_cell_tree')}`",
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
            "This is a finite-word cell identity, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    q_max: int = Q_MAX,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    data = (
        payload
        if payload is not None
        else probe_payload(q_max=q_max, k_max=k_max)
    )
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
