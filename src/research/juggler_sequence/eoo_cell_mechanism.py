"""EOO square-root cell classification of compensated contraction.

Not a Research Engine control-layer experiment. The first even step
freezes the remaining OO computation on the cell [q^2, (q+1)^2).
Contraction is the threshold n > eoo_cell_output(q). Not a halt theorem.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import (
    follows_itinerary,
    formal_gap,
    image_after,
    word_row,
)
from research.juggler_sequence.envelope_defect import tiny_deficit
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_eoo_cell_mechanism.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_eoo_cell_mechanism.md"

CLASS_GREEN = "EOO_CELL_MECHANISM_GREEN"
CLASS_COUNTER = "EOO_CELL_COUNTEREXAMPLE"
CLASS_PATTERN = "COMPENSATED_PATTERN_FOUND"
CLASS_ISOLATED = "COMPENSATED_EOO_ISOLATED"
CLASS_FAMILY = "POSITIVE_DRIFT_CONTRACTION_FAMILY"

Q_MAX = 80
LENGTH4_N_MAX = 20_000
LENGTH3_ODD_N_MAX = 20_000

LENGTH4_MIXED = ("OOOE", "OOEO", "OEOO", "EOOO")

LEAN_THEOREMS = (
    "sqrt_preimage_iff",
    "follows_eoo_sqrt_iff",
    "eoo_output_eq_preimage",
    "eoo_output_constant_on_sqrt_preimage",
    "eoo_contracts_on_preimage",
    "eoo_preimage_output_one",
    "eoo_preimage_output_three",
    "eoo_preimage_output_ge_succ_sq",
    "floorPower_eoo_contracts_iff",
    "power_bound_compensated_contracts",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "power_bound_compensated_contracts_follows",
)


def eoo_cell_output(q: int) -> int:
    """c(q) = ⌊(⌊q^{3/2}⌋)^{3/2}⌋. Constant on the square-root cell of q."""

    if q < 0:
        raise ValueError("eoo_cell_output requires a nonnegative integer")
    return isqrt(isqrt(q * q * q) ** 3)


def sqrt_cell(q: int) -> tuple[int, int]:
    """Half-open interval [q^2, (q+1)^2)."""

    if q < 0:
        raise ValueError("sqrt_cell requires a nonnegative integer")
    return q * q, (q + 1) * (q + 1)


def residue(n: int) -> tuple[int, int]:
    if n < 1:
        raise ValueError("residue requires a positive integer")
    q = isqrt(n)
    return q, n - q * q


def follows_eoo_sqrt(n: int) -> bool:
    """Python form of follows_eoo_sqrt_iff."""

    if n < 1 or n % 2 == 1:
        return False
    q = isqrt(n)
    if q % 2 == 0:
        return False
    return isqrt(q * q * q) % 2 == 1


def eoo_witness_table() -> list[dict[str, Any]]:
    rows = []
    for n in (2, 10, 12, 14):
        q, r = residue(n)
        path = [n, floor_power(n), floor_power(floor_power(n)), image_after(n, "EOO")]
        gap = formal_gap(n, 3, 2)
        deficit = tiny_deficit(n, path[3], 3, 2)
        rows.append(
            {
                "n": n,
                "q": q,
                "r": r,
                "q_parity": "odd" if q % 2 else "even",
                "T_q": path[2],
                "T2_q": path[3],
                "T3_n": path[3],
                "Delta": deficit,
                "G": gap,
                "contracts": path[3] < n,
            }
        )
    return rows


def scan_eoo_cells(*, q_max: int = Q_MAX) -> dict[str, Any]:
    if q_max < 1:
        raise ValueError("scan_eoo_cells requires q_max ≥ 1")
    cells = []
    constancy_failures = []
    threshold_failures = []
    contracting_cells = []
    for q in range(1, q_max + 1, 2):
        lo, hi = sqrt_cell(q)
        output = eoo_cell_output(q)
        realized = [n for n in range(lo, hi) if n % 2 == 0 and follows_itinerary(n, "EOO")]
        images = {n: image_after(n, "EOO") for n in realized}
        distinct = set(images.values())
        constant = len(distinct) <= 1
        if realized and not constant:
            constancy_failures.append({"q": q, "images": images})
        contracts = [n for n in realized if n > output]
        predicted = [n for n in realized if image_after(n, "EOO") < n]
        if contracts != predicted:
            threshold_failures.append(
                {"q": q, "contracts": contracts, "predicted": predicted}
            )
        if contracts:
            contracting_cells.append(
                {"q": q, "output": output, "cell": [lo, hi], "contracts": contracts}
            )
        cells.append(
            {
                "q": q,
                "cell": [lo, hi],
                "output": output,
                "realized": realized,
                "contracts": contracts,
                "constant": constant,
                "output_lt_cell_end": output < hi,
            }
        )
    return {
        "q_max": q_max,
        "cells": cells,
        "constancy_failures": constancy_failures,
        "threshold_failures": threshold_failures,
        "contracting_cells": contracting_cells,
        "contracting_starts": [
            n for cell in contracting_cells for n in cell["contracts"]
        ],
    }


def scan_word_sqrt_cells(
    word: str,
    *,
    q_max: int = Q_MAX,
    n_parity: int | None = None,
) -> dict[str, Any]:
    varying = 0
    constant = 0
    constant_examples = []
    varying_examples = []
    for q in range(1, q_max + 1):
        lo, hi = sqrt_cell(q)
        realized = []
        for n in range(max(lo, 2), hi):
            if n_parity is not None and n % 2 != n_parity:
                continue
            if follows_itinerary(n, word):
                realized.append(n)
        if len(realized) < 2:
            continue
        images = {n: image_after(n, word) for n in realized}
        if len(set(images.values())) == 1:
            constant += 1
            if len(constant_examples) < 3:
                constant_examples.append({"q": q, "images": images})
        else:
            varying += 1
            if len(varying_examples) < 3:
                varying_examples.append({"q": q, "images": images})
    return {
        "word": word,
        "q_max": q_max,
        "varying_cells": varying,
        "constant_cells": constant,
        "constant_examples": constant_examples,
        "varying_examples": varying_examples,
    }


def scan_first_even_cells(word: str, *, q_max: int = Q_MAX) -> dict[str, Any]:
    """First-even words have constant suffix output on the start sqrt cell."""

    if not word or word[0] != "E":
        raise ValueError("scan_first_even_cells requires a first-even word")
    cells = []
    constancy_failures = []
    contracting = []
    for q in range(1, q_max + 1, 2):
        lo, hi = sqrt_cell(q)
        realized = [n for n in range(max(lo, 2), hi) if n % 2 == 0 and follows_itinerary(n, word)]
        if not realized:
            continue
        images = {n: image_after(n, word) for n in realized}
        distinct = set(images.values())
        if len(distinct) != 1:
            constancy_failures.append({"q": q, "images": images})
            continue
        output = next(iter(distinct))
        contracts = [n for n in realized if n > output]
        if contracts:
            contracting.append(
                {"q": q, "output": output, "cell": [lo, hi], "contracts": contracts}
            )
        cells.append(
            {
                "q": q,
                "output": output,
                "cell": [lo, hi],
                "realized": realized,
                "contracts": contracts,
                "output_lt_cell_end": output < hi,
            }
        )
    return {
        "word": word,
        "q_max": q_max,
        "cells": cells,
        "constancy_failures": constancy_failures,
        "contracting_cells": contracting,
        "contracting_starts": [n for cell in contracting for n in cell["contracts"]],
    }


def scan_length4(*, n_max: int = LENGTH4_N_MAX) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for word in LENGTH4_MIXED:
        contracts = []
        realized = 0
        for n in range(2, n_max + 1):
            if not follows_itinerary(n, word):
                continue
            realized += 1
            image = image_after(n, word)
            if image < n:
                contracts.append({"n": n, "image": image})
        out[word] = {
            "realized": realized,
            "contract_count": len(contracts),
            "contracts": contracts,
        }
    return out


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "eooCellOutput_present": "def eooPreimageOutput" in text,
        "certificate_present": all(
            f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "ooe_not_contracts": "theorem floorPower_ooe_not_contracts" in text,
        "oeo_not_contracts": "theorem floorPower_oeo_not_contracts" in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    eoo = scan["eoo_cells"]
    ooe = scan["ooe_cells"]
    oeo = scan["oeo_cells"]
    eooo = scan["eooo_cells"]
    length4 = scan["length4"]
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if eoo["constancy_failures"] or eoo["threshold_failures"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": (
                "EOO output was not constant on a square-root cell, or "
                "contraction failed the threshold n > c(q)"
            ),
        }
    if eoo["contracting_starts"] != [2, 12, 14]:
        return {
            "classification": CLASS_COUNTER,
            "reason": (
                "EOO cell scan did not recover exactly the contraction "
                "starts {2, 12, 14}"
            ),
        }
    if not lean_ok:
        return {
            "classification": CLASS_ISOLATED,
            "reason": (
                "the cell/threshold description matches the three starts, "
                "but the Lean cell API is incomplete"
            ),
        }
    pattern = (
        not eooo["constancy_failures"]
        and eooo["contracting_starts"] == [2]
        and length4["EOOO"]["contracts"] == [{"n": 2, "image": 1}]
        and all(length4[word]["contract_count"] == 0 for word in ("OOOE", "OOEO", "OEOO"))
    )
    if ooe["varying_cells"] == 0 and oeo["varying_cells"] == 0:
        return {
            "classification": CLASS_FAMILY,
            "reason": (
                "OOE and OEO also froze on n-sqrt cells; that would be a "
                "broader cell calculus, not just first-even freeze"
            ),
        }
    if pattern:
        return {
            "classification": CLASS_GREEN,
            "secondary": CLASS_PATTERN,
            "reason": (
                "EOO contracts exactly on the cells q=1,3 by the threshold "
                "n > c(q); q≥5 has c(q) ≥ (q+1)^2. The same first-even "
                "freeze appears for EOOO, but only n=2 meets the threshold"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "EOO contracts exactly when a realized start in the square-root "
            "cell of q satisfies n > eooPreimageOutput q"
        ),
    }


def run_probe(
    *,
    q_max: int = Q_MAX,
    length4_n_max: int = LENGTH4_N_MAX,
    odd_n_max: int = LENGTH3_ODD_N_MAX,
) -> dict[str, Any]:
    del odd_n_max
    eoo_cells = scan_eoo_cells(q_max=q_max)
    return {
        "q_max": q_max,
        "length4_n_max": length4_n_max,
        "eoo_cells": eoo_cells,
        "eoo_witness_table": eoo_witness_table(),
        "ooe_cells": scan_word_sqrt_cells("OOE", q_max=q_max, n_parity=1),
        "oeo_cells": scan_word_sqrt_cells("OEO", q_max=q_max, n_parity=1),
        "eooo_cells": scan_first_even_cells("EOOO", q_max=q_max),
        "length4": scan_length4(n_max=length4_n_max),
        "ten_eoo_expands": word_row(10, "EOO"),
    }


def probe_payload(
    *,
    q_max: int = Q_MAX,
    length4_n_max: int = LENGTH4_N_MAX,
) -> dict[str, Any]:
    scan = run_probe(q_max=q_max, length4_n_max=length4_n_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_eoo_cell_mechanism",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact square-root cells and floor_power images; no floats; "
            "no huge envelope powers except the four recorded starts"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    eoo = scan["eoo_cells"]
    lines = [
        "# Juggler EOO square-root cell mechanism",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. The first even step freezes the remaining",
        "`OO` computation on the square-root cell `[q^2, (q+1)^2)`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Why does EOO contract exactly at 2, 12, 14?",
        "Novelty hypothesis      Cell constancy plus the threshold n > c(q)",
        "Falsifier               Output varies on a cell, or n>c fails",
        "Existing machinery      PowerBound, floorPower_eoo_contracts_iff",
        "Maximum Phase-0 scope   EOO cells; OOE/OEO contrast; length-4 scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- odd-q cell domain: `q <= {scan['q_max']}`",
        f"- length-4 domain: `n <= {scan['length4_n_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## EOO cells",
        "",
        f"- constancy failures: `{len(eoo['constancy_failures'])}`",
        f"- threshold failures: `{len(eoo['threshold_failures'])}`",
        f"- contracting starts: `{eoo['contracting_starts']}`",
        "",
    ]
    for cell in eoo["cells"]:
        if cell["q"] > 9 and not cell["contracts"]:
            continue
        lines.append(
            f"- q=`{cell['q']}` cell=`{cell['cell']}` c=`{cell['output']}` "
            f"realized=`{cell['realized']}` contracts=`{cell['contracts']}` "
            f"c < (q+1)^2: `{cell['output_lt_cell_end']}`"
        )
    lines.extend(
        [
            "",
            "## Witness table",
            "",
        ]
    )
    for row in scan["eoo_witness_table"]:
        lines.append(
            f"- n=`{row['n']}` q=`{row['q']}` r=`{row['r']}` "
            f"T(q)=`{row['T_q']}` T^3=`{row['T3_n']}` "
            f"Δ=`{row['Delta']}` G=`{row['G']}` contracts=`{row['contracts']}`"
        )
    ooe = scan["ooe_cells"]
    oeo = scan["oeo_cells"]
    eooo = scan["eooo_cells"]
    lines.extend(
        [
            "",
            "## OOE / OEO on n-sqrt cells",
            "",
            f"- `OOE`: varying `{ooe['varying_cells']}`, constant `{ooe['constant_cells']}`",
            f"- `OEO`: varying `{oeo['varying_cells']}`, constant `{oeo['constant_cells']}`",
            "",
            "The first letter is odd, so T(n) = ⌊n^{3/2}⌋ varies inside the",
            "n-sqrt cell. EOO is special because the first even step freezes",
            "the remaining word.",
            "",
            "## Length-4 mixed o=3",
            "",
            f"- `EOOO` first-even constancy failures: `{len(eooo['constancy_failures'])}`",
            f"- `EOOO` contracting starts: `{eooo['contracting_starts']}`",
            "",
        ]
    )
    for word in LENGTH4_MIXED:
        item = scan["length4"][word]
        lines.append(
            f"- `{word}`: realized `{item['realized']}`, "
            f"contractions `{item['contract_count']}`"
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
            f"- `eooPreimageOutput` present: `{lean.get('eooCellOutput_present')}`",
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- `mixed_word_power_lt` absent: `{lean.get('mixed_word_power_lt_absent')}`",
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
            "This is a finite-word cell classification, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    q_max: int = Q_MAX,
    length4_n_max: int = LENGTH4_N_MAX,
) -> dict[str, Any]:
    data = (
        payload
        if payload is not None
        else probe_payload(q_max=q_max, length4_n_max=length4_n_max)
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
