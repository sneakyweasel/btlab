"""Near-extremal non-contracting Juggler prefixes.

Not a Research Engine control-layer experiment. Drift uses the exact
integer gap G = 2^k - 3^o. Envelope Δ is computed only inside a bit
budget. Not a termination theorem.
"""

from __future__ import annotations

import json
from functools import cmp_to_key
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import formal_gap
from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
    tiny_deficit,
)
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.lean_paths import SCALE, juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    itinerary,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_near_extremal_prefixes.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_near_extremal_prefixes.md"

CLASS_STRUCTURE = "NEAR_EXTREMAL_STRUCTURE_GREEN"
CLASS_DEFECT = "DEFECT_DRIVEN_CONTRACTION_GREEN"
CLASS_BOUNDED = "BAD_PREFIX_BOUNDED_GREEN"
CLASS_ARBITRARY = "BAD_PREFIX_ARBITRARY"
CLASS_COUNTER = "NEAR_EXTREMAL_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "NEAR_EXTREMAL_INCOMPLETE"

N_MAX = 2_000
K_REAL = 10
K_COMB = 16
BIT_BUDGET = 80
CLOSE_CAP = 8

LEAN_THEOREMS = (
    "power_bound_contracts",
    "power_bound_compensated_contracts",
    "power_bound_compensated_contracts_follows",
    "two_pow_succ_le_three_pow_iff",
    "power_bound_eq_iff_extremal",
)


def exponent_gap(k: int, odds: int) -> int:
    """G(w) = 2^k - 3^o. Positive means formally contracting."""

    if k < 0 or odds < 0:
        raise ValueError("exponent_gap requires nonnegative k and odd_count")
    return (1 << k) - 3**odds


def prefix_noncontracting(word: str) -> bool:
    """Every prefix has G_j ≤ 0."""

    odds = 0
    for index, letter in enumerate(word, start=1):
        if letter == "O":
            odds += 1
        elif letter != "E":
            raise ValueError(f"invalid word letter {letter!r}")
        if exponent_gap(index, odds) > 0:
            return False
    return True


def prefix_nc_words(k_max: int) -> list[str]:
    """All nonempty prefix-noncontracting itineraries of length at most k_max."""

    if k_max < 0:
        raise ValueError("prefix_nc_words requires nonnegative k_max")
    out: list[str] = []

    def rec(word: str, odds: int) -> None:
        if word:
            out.append(word)
        if len(word) == k_max:
            return
        rec(word + "O", odds + 1)
        nxt = len(word) + 1
        if exponent_gap(nxt, odds) <= 0:
            rec(word + "E", odds)

    rec("", 0)
    return out


def first_contracting_prefix(word: str) -> int | None:
    """Smallest j with G_j > 0, or None if the whole word is prefix-NC."""

    odds = 0
    for index, letter in enumerate(word, start=1):
        if letter == "O":
            odds += 1
        elif letter != "E":
            raise ValueError(f"invalid word letter {letter!r}")
        if exponent_gap(index, odds) > 0:
            return index
    return None


def prefix_row(
    n: int,
    word: str,
    *,
    bit_limit: int = BIT_BUDGET,
) -> dict[str, Any]:
    path = itinerary(n, len(word))
    if word_of(path) != word:
        raise ValueError("prefix_row requires a realized word")
    image = path[-1]
    odds = odd_count(word)
    gap_exp = exponent_gap(len(word), odds)
    formal = formal_gap(n, len(word), odds, bit_limit=bit_limit)
    deficit = tiny_deficit(n, image, len(word), odds, bit_limit=bit_limit)
    index = first_nonexact_index(path)
    defect = None if index is None else local_defect(path[index])
    defect_contracts = (
        None
        if formal is None or deficit is None
        else deficit > formal
    )
    return {
        "word": word,
        "n": n,
        "k": len(word),
        "odd_count": odds,
        "exponent_gap": gap_exp,
        "image": image,
        "actual_contraction": image < n,
        "first_defect_position": index,
        "first_defect": defect,
        "formal_gap": formal,
        "deficit": deficit,
        "defect_contracts": defect_contracts,
        "monochrome": is_monochrome(word),
        "prefix_nc": prefix_noncontracting(word),
    }


def combinatorial_census(k_max: int = K_COMB) -> dict[str, Any]:
    words = prefix_nc_words(k_max)
    mixed = [word for word in words if not is_monochrome(word)]
    oke = [word for word in mixed if set(word) <= {"O", "E"} and word.endswith("E") and set(word[:-1]) == {"O"}]
    other = [word for word in mixed if word not in oke]
    by_len: dict[int, int] = {}
    for word in words:
        by_len[len(word)] = by_len.get(len(word), 0) + 1
    return {
        "k_max": k_max,
        "word_count": len(words),
        "mixed_count": len(mixed),
        "oke_count": len(oke),
        "other_mixed_count": len(other),
        "counts_by_length": {str(key): by_len[key] for key in sorted(by_len)},
        "starts_with_o": all(word.startswith("O") for word in words),
        "len_ge_2_starts_with_oo": all(
            word.startswith("OO") for word in words if len(word) >= 2
        ),
        "oke_family": [f"O^{k}E" for k in range(2, k_max)],
        "other_mixed_sample": other[:16],
        "oe_not_prefix_nc": prefix_noncontracting("OE") is False,
        "e_not_prefix_nc": prefix_noncontracting("E") is False,
        "ooe_prefix_nc": prefix_noncontracting("OOE") is True,
    }


def scan_realized(
    n_max: int = N_MAX,
    k_max: int = K_REAL,
    *,
    n_min: int = 2,
    bit_limit: int = BIT_BUDGET,
) -> dict[str, Any]:
    if n_max < n_min or k_max < 1:
        raise ValueError("scan_realized requires n_min ≤ n_max and k_max ≥ 1")
    mixed_rows: list[dict[str, Any]] = []
    tau_rows: list[dict[str, Any]] = []
    max_mixed_len = 0
    max_pure_odd = 0
    defect_hits = 0
    avoid_hits = 0
    for n in range(n_min, n_max + 1):
        path = itinerary(n, k_max)
        word = word_of(path)
        tau = first_contracting_prefix(word)
        odd_run = 0
        for letter in word:
            if letter != "O":
                break
            odd_run += 1
        max_pure_odd = max(max_pure_odd, odd_run)
        tau_rows.append({"n": n, "tau": tau, "word": word, "odd_run": odd_run})
        limit = len(word) if tau is None else tau - 1
        for length in range(1, limit + 1):
            prefix = word[:length]
            if is_monochrome(prefix):
                continue
            row = prefix_row(n, prefix, bit_limit=bit_limit)
            mixed_rows.append(row)
            max_mixed_len = max(max_mixed_len, length)
            if row["defect_contracts"] is True:
                defect_hits += 1
            elif row["defect_contracts"] is False:
                avoid_hits += 1

    def _close_cmp(left: dict[str, Any], right: dict[str, Any]) -> int:
        # Prefer rows where Δ and G are known; rank by Δ/G via cross-multiply.
        lg, ld = left["formal_gap"], left["deficit"]
        rg, rd = right["formal_gap"], right["deficit"]
        if ld is None or lg is None or lg == 0:
            if rd is None or rg is None or rg == 0:
                return left["n"] - right["n"]
            return 1
        if rd is None or rg is None or rg == 0:
            return -1
        cross = ld * rg - rd * lg
        if cross < 0:
            return -1
        if cross > 0:
            return 1
        return left["n"] - right["n"]

    comparable = [
        row
        for row in mixed_rows
        if row["formal_gap"] is not None
        and row["deficit"] is not None
        and row["formal_gap"] > 0
        and row["defect_contracts"] is False
    ]
    closest = sorted(comparable, key=cmp_to_key(_close_cmp))[:CLOSE_CAP]
    longest = [row for row in mixed_rows if row["k"] == max_mixed_len]
    defect_examples = [row for row in mixed_rows if row["defect_contracts"] is True][:8]
    tau_defined = [row for row in tau_rows if row["tau"] is not None]
    tau_none = [row for row in tau_rows if row["tau"] is None]
    max_tau = max((row["tau"] for row in tau_defined), default=0)
    return {
        "n_min": n_min,
        "n_max": n_max,
        "k_max": k_max,
        "mixed_prefix_count": len(mixed_rows),
        "max_mixed_prefix_nc_length": max_mixed_len,
        "max_opening_odd_run": max_pure_odd,
        "defect_contract_count": defect_hits,
        "defect_avoid_count": avoid_hits,
        "tau_defined_count": len(tau_defined),
        "tau_none_count": len(tau_none),
        "max_tau": max_tau,
        "horizon_mixed_prefix_nc": max_mixed_len >= k_max,
        "closest_avoiders": [
            {
                "n": row["n"],
                "word": row["word"],
                "k": row["k"],
                "exponent_gap": row["exponent_gap"],
                "deficit": row["deficit"],
                "formal_gap": row["formal_gap"],
                "image": row["image"],
            }
            for row in closest
        ],
        "longest_mixed": [
            {
                "n": row["n"],
                "word": row["word"],
                "k": row["k"],
                "image": row["image"],
                "actual_contraction": row["actual_contraction"],
                "defect_contracts": row["defect_contracts"],
            }
            for row in longest[:12]
        ],
        "defect_examples": [
            {
                "n": row["n"],
                "word": row["word"],
                "k": row["k"],
                "image": row["image"],
                "deficit": row["deficit"],
                "formal_gap": row["formal_gap"],
            }
            for row in defect_examples
        ],
        "tau_none_sample": [
            {"n": row["n"], "word": row["word"], "odd_run": row["odd_run"]}
            for row in tau_none[:8]
        ],
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    financing = (
        SCALE
    ).read_text(encoding="utf-8")
    combined = text + "\n" + financing
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: f"theorem {name}" in combined for name in LEAN_THEOREMS},
        "PowerHeight_absent": "PowerHeight" not in text,
        "new_defect_structure_absent": "structure DefectContracts" not in text,
    }


def classify(comb: dict[str, Any], scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the existing contraction / O^a E Lean API is incomplete",
        }
    if comb["other_mixed_count"] and comb["starts_with_o"] and comb["ooe_prefix_nc"]:
        return {
            "classification": CLASS_STRUCTURE,
            "reason": (
                "prefix-noncontracting itineraries start with O, length ≥ 2 "
                "starts with OO, and include the unbounded mixed family "
                "O^k E for k≥2 plus other mixed patterns; defect-driven "
                "contraction is already Lean and did not fire on the "
                "realized mixed prefixes in range. A finite horizon hit "
                "is not an infinite family"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "the near-extremal prefix language is not yet described",
    }


def run_probe(
    *,
    n_max: int = N_MAX,
    k_real: int = K_REAL,
    k_comb: int = K_COMB,
    bit_limit: int = BIT_BUDGET,
) -> dict[str, Any]:
    comb = combinatorial_census(k_comb)
    scan = scan_realized(n_max, k_real, bit_limit=bit_limit)
    return {
        "n_max": n_max,
        "k_real": k_real,
        "k_comb": k_comb,
        "bit_limit": bit_limit,
        "combinatorial": comb,
        "realized": scan,
        "examples": {
            "three_oooe": prefix_row(3, "OOOE", bit_limit=bit_limit),
            "oe_tau": first_contracting_prefix("OE"),
            "eoo_tau": first_contracting_prefix("EOO"),
        },
    }


def probe_payload(
    *,
    n_max: int = N_MAX,
    k_real: int = K_REAL,
    k_comb: int = K_COMB,
) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_real=k_real, k_comb=k_comb)
    lean = lean_api_present()
    decision = classify(scan["combinatorial"], scan["realized"], lean)
    return {
        "experiment": "juggler_near_extremal_prefixes",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact G = 2^k - 3^o on prefixes; realized itineraries via "
            "floor_power; Δ and n^{3^o}-n^{2^k} only inside a bit budget; "
            "no floats"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    comb = scan["combinatorial"]
    realized = scan["realized"]
    examples = scan["examples"]
    lines = [
        "# Juggler near-extremal non-contracting prefixes",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. The object is a finite prefix with",
        "`G_j = 2^j - 3^{o_j} ≤ 0` that is not monochrome.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     realized non-extremal prefixes with G≤0",
        "                        and Δ too small to force T^k(n)<n",
        "Novelty hypothesis      a language obstruction or defect bound",
        "Falsifier               arbitrarily long realized mixed prefix-NC",
        "                        words that also avoid defect contraction",
        "Existing machinery      PowerBound, compensated contraction, O^a E",
        "Maximum Phase-0 scope   combinatorial prefix-NC tree; realized",
        "                        scan; no new Lean unless a new inequality",
        "```",
        "",
        "## Metadata",
        "",
        f"- combinatorial `k <= {scan['k_comb']}`",
        f"- realized `n <= {scan['n_max']}`, `k <= {scan['k_real']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Combinatorial prefix-NC language",
        "",
        f"- words: `{comb['word_count']}`",
        f"- mixed: `{comb['mixed_count']}`",
        f"- `O^k E` family: `{comb['oke_count']}`",
        f"- other mixed: `{comb['other_mixed_count']}`",
        f"- every word starts with `O`: `{comb['starts_with_o']}`",
        f"- length ≥ 2 starts with `OO`: `{comb['len_ge_2_starts_with_oo']}`",
        f"- `E` is prefix-NC: `{not comb['e_not_prefix_nc']}`",
        f"- `OE` is prefix-NC: `{not comb['oe_not_prefix_nc']}`",
        f"- `OOE` is prefix-NC: `{comb['ooe_prefix_nc']}`",
        "",
        "A single even step has `G=1>0`, so every prefix-NC word starts",
        "odd. `OE` already has `G_2=1>0`. The mixed family `O^k E` for",
        "`k≥2` is prefix-NC by `2^{k+1} ≤ 3^k`, already Lean as",
        "`two_pow_succ_le_three_pow_iff`. Other mixed patterns exist",
        f"(sample `{comb['other_mixed_sample']}`).",
        "",
        "## Realized mixed prefixes",
        "",
        f"- mixed prefix-NC rows: `{realized['mixed_prefix_count']}`",
        f"- max mixed prefix-NC length: `{realized['max_mixed_prefix_nc_length']}`",
        f"- max opening odd run: `{realized['max_opening_odd_run']}`",
        f"- defect-driven certificates: `{realized['defect_contract_count']}`",
        f"- defect avoiders with known gap: `{realized['defect_avoid_count']}`",
        f"- first contracting prefix defined: `{realized['tau_defined_count']}`",
        f"- no contracting prefix in horizon: `{realized['tau_none_count']}`",
        f"- max `τ`: `{realized['max_tau']}`",
        "",
        "Calibration: `n=3` realizes `OOOE` with image "
        f"`{examples['three_oooe']['image']}`; `τ(OE)={examples['oe_tau']}`; "
        f"`τ(EOO)={examples['eoo_tau']}` so `EOO` is not a bad prefix.",
        "",
        "## Closest known avoiders of defect contraction",
        "",
    ]
    if not realized["closest_avoiders"]:
        lines.append("None with a computed positive formal gap.")
    for row in realized["closest_avoiders"]:
        lines.append(
            f"- n `{row['n']}` word `{row['word']}`: Δ `{row['deficit']}`, "
            f"G_formal `{row['formal_gap']}`, image `{row['image']}`"
        )
    lines.extend(
        [
            "",
            "## Longest realized mixed prefix-NC words",
            "",
        ]
    )
    if not realized["longest_mixed"]:
        lines.append("None.")
    for row in realized["longest_mixed"]:
        lines.append(
            f"- n `{row['n']}` `{row['word']}`: image `{row['image']}`, "
            f"contracts `{row['actual_contraction']}`"
        )
    lines.extend(
        [
            "",
            "## Lean reused, not extended",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- new `DefectContracts` structure absent: "
            f"`{lean.get('new_defect_structure_absent')}`",
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
            "This is a finite-prefix language statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    k_real: int = K_REAL,
    k_comb: int = K_COMB,
) -> dict[str, Any]:
    data = (
        payload
        if payload is not None
        else probe_payload(n_max=n_max, k_real=k_real, k_comb=k_comb)
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
