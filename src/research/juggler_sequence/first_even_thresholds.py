"""First-even suffix thresholds and finiteness of Q_v.

Not a Research Engine control-layer experiment. For a suffix v,
Q_v = {q : T_v(q) < (q+1)^2} among q that realize v. Positive-drift
Ev means α_v > 2. Not a halt theorem.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_even_thresholds.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_even_thresholds.md"

CLASS_THRESHOLD = "FIRST_E_THRESHOLD_GREEN"
CLASS_FINITE = "FIRST_E_FINITE_GREEN"
CLASS_INFINITE = "FIRST_E_INFINITE_FAMILY"
CLASS_COUNTER = "FIRST_E_THRESHOLD_COUNTEREXAMPLE"
CLASS_LOCAL = "FIRST_E_MECHANISM_TOO_LOCAL"

Q_MAX = 120
PRIORITY = ("O", "OO", "OOO", "EO", "EOO", "EOOO", "EOOOO", "OOOO")

LEAN_THEOREMS = (
    "cell_any_contracts_iff",
    "cell_all_contracts_iff",
    "first_even_any_contracts_iff",
    "first_even_all_contracts_iff",
    "first_even_contracts_iff",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "floorPower_odd_ge",
    "eoo_cell_output_ge_succ_sq",
    "floorPower_eoo_contracts_iff",
    "power_bound_compensated_contracts",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "power_bound_compensated_contracts_follows",
)


def formal_alpha(word: str) -> dict[str, Any]:
    odds = word.count("O")
    length = len(word)
    num = 3**odds
    den = 1 << length
    return {
        "word": word,
        "odd_count": odds,
        "length": length,
        "num": num,
        "den": den,
        "gt_two": num > 2 * den,
        "ev_positive_drift": num > 2 * den,
    }


def cell_bounds(q: int) -> tuple[int, int]:
    return q * q, (q + 1) * (q + 1)


def regime(q: int, output: int) -> str:
    lo, hi = cell_bounds(q)
    if output < lo:
        return "all_contract"
    if output + 1 < hi:
        return "mixed"
    return "all_expand"


def scan_suffix(v: str, *, q_max: int = Q_MAX) -> dict[str, Any]:
    any_q: list[int] = []
    all_q: list[int] = []
    realized: list[dict[str, Any]] = []
    mono_breaks: list[dict[str, Any]] = []
    seen_expand_q: int | None = None
    for q in range(1, q_max + 1):
        if not follows_itinerary(q, v):
            continue
        output = image_after(q, v)
        lo, hi = cell_bounds(q)
        any_c = output + 1 < hi
        all_c = output < lo
        row = {
            "q": q,
            "output": output,
            "cell": [lo, hi],
            "regime": regime(q, output),
            "any": any_c,
            "all_cell": all_c,
        }
        realized.append(row)
        if any_c:
            any_q.append(q)
            if all_c:
                all_q.append(q)
            if seen_expand_q is not None:
                mono_breaks.append(
                    {"after": seen_expand_q, "later_contract": q, "output": output}
                )
        else:
            if seen_expand_q is None:
                seen_expand_q = q
    return {
        "v": v,
        "alpha": formal_alpha(v),
        "q_max": q_max,
        "realized": len(realized),
        "Q": any_q,
        "Q_all": all_q,
        "first_expand": seen_expand_q,
        "mono_breaks": mono_breaks,
        "rows": [row for row in realized if row["any"] or row["q"] < 8],
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "certificate_present": all(
            f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_cell_tree": "inductive FloorCell" not in text,
        "no_lower_envelope": "structure LowerEnvelope" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    by_v = {item["v"]: item for item in scan["suffixes"]}
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if any(item["mono_breaks"] for item in scan["suffixes"]):
        return {
            "classification": CLASS_COUNTER,
            "reason": "threshold monotonicity failed for a scanned suffix",
        }
    oo = by_v["OO"]
    ooo = by_v["OOO"]
    odd = by_v["O"]
    if oo["Q"] != [1, 3] or ooo["Q"] != [1]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "OO or OOO did not recover the known finite Q_v",
        }
    if lean_ok and odd["alpha"]["gt_two"] is False and len(odd["Q"]) == odd["realized"]:
        return {
            "classification": CLASS_FINITE,
            "secondary": CLASS_THRESHOLD,
            "reason": (
                "Q_OO = {1,3} and Q_OOO = {1} with Lean eventual thresholds; "
                "Q_O is all realized odd q because α=3/2<2, which is formal "
                "contraction of EO, not compensated positive drift"
            ),
        }
    if lean_ok:
        return {
            "classification": CLASS_FINITE,
            "reason": "OO and OOO have Lean eventual thresholds, so those Q_v are finite",
        }
    return {
        "classification": CLASS_LOCAL,
        "reason": "the finite Q_v are visible computationally but the Lean API is incomplete",
    }


def run_probe(*, q_max: int = Q_MAX) -> dict[str, Any]:
    suffixes = [scan_suffix(v, q_max=q_max) for v in PRIORITY]
    return {
        "q_max": q_max,
        "suffixes": suffixes,
        "off_by_one": (
            "any contraction on [q^2,(q+1)^2) is c+1 < (q+1)^2, "
            "not merely c < (q+1)^2"
        ),
    }


def probe_payload(*, q_max: int = Q_MAX) -> dict[str, Any]:
    scan = run_probe(q_max=q_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_first_even_thresholds",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "suffix image at realized q only; integer cell comparison; "
            "no huge envelope powers"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler first-even thresholds",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Q_v is the set of realized q with",
        "`T_v(q) + 1 < (q+1)^2`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     For α_v > 2, is Q_v finite?",
        "Novelty hypothesis      OO and OOO have eventual thresholds",
        "Falsifier               Large Q_v for OO/OOO, or a mono break",
        "Existing machinery      first_even_freeze, eoo_cell_output_ge_succ_sq",
        "Maximum Phase-0 scope   Cell-interval API; Q_v for short suffixes",
        "```",
        "",
        "## Metadata",
        "",
        f"- q domain: `q <= {scan['q_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        f"Exact any-contraction: `{scan['off_by_one']}`.",
        "",
        "## Suffix scans",
        "",
    ]
    for item in scan["suffixes"]:
        alpha = item["alpha"]
        lines.append(
            f"- `{item['v']}` α=`{alpha['num']}/{alpha['den']}` "
            f"drift>2=`{alpha['gt_two']}` Q=`{item['Q']}` "
            f"Q_all=`{item['Q_all']}` first_expand=`{item['first_expand']}` "
            f"mono_breaks=`{len(item['mono_breaks'])}`"
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
            "This is a finite-word threshold statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    q_max: int = Q_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(q_max=q_max)
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
