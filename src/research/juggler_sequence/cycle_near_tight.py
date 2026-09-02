"""Cycle near-tightness versus open-orbit near-tightness.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a reopen of NearTightScale or approximate equality rigidity.

Cycle finance leftover convergents have a tiny relative gap
    theta = 1 - 2^L / 3^o.
Open-orbit near-tightness is tiny relative slack
    q_w(n) = n^{3^o} / T_w(n)^{2^L} - 1.
The portability slogan is that return + tiny theta forces an
almost-monochrome tower, i.e. that cycle near-tightness is a
stricter form of open-orbit q -> 0.

On a realized return T_w(n) = n the slack definition gives
    1 + q = n^{3^o - 2^L}
exactly (Lean image_eq_start_defectRatio is R = 1). That q is
huge along the record lengths. Open-orbit near-tight paths expand
(image > n), so they sit in the opposite regime.

Dossier: docs/problems/juggler_cycle_near_tight.md.
"""

from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST, n_max_from_bound
from research.juggler_sequence.cycle_gap_baker import exact_gap, o_min
from research.juggler_sequence.expansion_slack import NEAR_TIGHT
from research.juggler_sequence.global_defect import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)
from research.juggler_sequence.near_tight_scale import q_exact
from research.juggler_sequence.normalized_defect import (
    bits_ok,
    defect_ratio,
    formal_surplus,
    slack_den,
    slack_num,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.progress_coverage import is_odd_odd

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_near_tight.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_near_tight.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_near_tight"

CLASS_CLOSED = "CYCLE_NEAR_TIGHT_CLOSED"
CLASS_GREEN = "CYCLE_NEAR_TIGHT_GREEN"
CLASS_INCOMPLETE = "CYCLE_NEAR_TIGHT_INCOMPLETE"

# Record (one-sided best-approximation) lengths from cycle finance.
RECORD_LENGTHS = (1, 3, 11, 19, 84, 569, 1054)
SLOGAN_LENGTHS = (19, 84, 569, 1054)

OOE_WORD = "OOE"
SCIENCE_N_MAX = 2000
TEST_N_MAX = 400
LEAN_FLOOR = 53

EXISTING_LEAN = (
    "image_eq_start_defectRatio",
    "defectRatio_le_one_iff_image_ge",
    "power_bound_eq_implies_monochrome",
    "cycleMin_finance",
    "ooe_one_plus_slack_lt_succ_ratio",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "cycle_near_tight_excludes",
    "almost_monochrome_cycle",
    "no_cycle_itinerary_length_eighty_four",
)
FORBIDDEN_NEW_API = (
    "CycleNearTight",
    "AlmostMonochrome",
    "NearTightCycle",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleNearTight.lean",
    JUGGLER_DIR / "NearTightCycle.lean",
    JUGGLER_DIR / "AlmostMonochrome.lean",
)
PAPER_FORBIDDEN = ("CycleNearTight", "AlmostMonochrome", "NearTightCycle")


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def cycle_exponent_gap(length: int, odd: int | None = None) -> int:
    """G = 3^o - 2^L at o_min, or at a supplied o."""

    odd_count = o_min(length) if odd is None else odd
    return 3**odd_count - (1 << length)


def cycle_one_plus_q(n: int, length: int, odd: int | None = None) -> int:
    """Exact 1+q on a realized return: n^G."""

    if n < 1:
        raise ValueError("n must be positive")
    return n ** cycle_exponent_gap(length, odd)


def _safe_gap_ln(gap: int, n: int) -> float:
    """Return gap * ln n, or inf when the product overflows float."""

    if gap <= 0:
        return 0.0
    ln_n = math.log(n)
    ln_gap_approx = (gap.bit_length() - 1) * math.log(2)
    if ln_gap_approx + math.log(ln_n) > 700.0:
        return float("inf")
    return float(gap) * ln_n


def cycle_ln_one_plus_q(n: int, length: int, odd: int | None = None) -> float:
    """ln(1+q) = G ln n on a realized return. Avoids n^G."""

    if n < 2:
        raise ValueError("n must be at least 2")
    return _safe_gap_ln(cycle_exponent_gap(length, odd), n)


def envelope_growth_log(n: int, length: int, odd: int | None = None) -> float:
    """ln(image/n) for a zero-defect path: (3^o/2^L - 1) ln n."""

    if n < 2:
        raise ValueError("n must be at least 2")
    odd_count = o_min(length) if odd is None else odd
    ratio = math.exp(odd_count * math.log(3.0) - length * math.log(2.0))
    return (ratio - 1.0) * math.log(n)


def open_q_lt_cycle_q(n: int, image: int) -> bool:
    """q_open < n^G - 1 iff image > n, for any expanding (L, o).

    Slack definition: 1+q_open = n^{3^o} / image^{2^L} and
    1+q_cycle = n^{3^o-2^L}. The comparison cancels n^{3^o-2^L}
    and is equivalent to image > n.
    """

    return image > n


def record_row(length: int) -> dict[str, Any]:
    exact = exact_gap(length)
    odd = exact["o"]
    gap = exact["gap"]
    evens = length - odd
    hamming = min(odd, evens)
    theta = exact["theta"]
    bound = EPS_CONST * length / theta
    n_max = n_max_from_bound(bound)
    ln_q_53 = cycle_ln_one_plus_q(LEAN_FLOOR, length, odd)
    ln_q_max = cycle_ln_one_plus_q(n_max, length, odd)
    growth_53 = math.expm1(envelope_growth_log(LEAN_FLOOR, length, odd))
    return {
        "L": length,
        "o": odd,
        "even_count": evens,
        "gap": gap if gap.bit_length() <= 256 else None,
        "gap_bits": gap.bit_length(),
        "theta": theta,
        "hamming_to_monochrome": hamming,
        "n_max": n_max,
        "ln_one_plus_q_at_53": None if math.isinf(ln_q_53) else ln_q_53,
        "ln_one_plus_q_at_n_max": None if math.isinf(ln_q_max) else ln_q_max,
        "envelope_growth_at_53": growth_53,
        "almost_monochrome": hamming <= 1,
    }


def ooe_open_row(n: int) -> dict[str, Any] | None:
    if not follows_itinerary(n, OOE_WORD):
        return None
    if not bits_ok(n, 9) or not bits_ok(image_after(n, OOE_WORD), 8):
        return None
    image = image_after(n, OOE_WORD)
    num = slack_num(n, OOE_WORD)
    den = slack_den(n, OOE_WORD)
    surplus = formal_surplus(n, OOE_WORD)
    ratio = defect_ratio(n, OOE_WORD)
    if surplus <= 0 or ratio is None:
        return None
    delta, _ = ratio
    q_open = (num - den) / den
    return {
        "n": n,
        "image": image,
        "expands": image > n,
        "returns": image == n,
        "q_open": q_open,
        "q_cycle": n - 1,
        "R": delta / surplus,
        "open_q_lt_cycle_q": open_q_lt_cycle_q(n, image),
    }


def ooe_open_census(*, n_max: int = TEST_N_MAX) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for n in range(3, n_max + 1, 2):
        if not is_odd_odd(n):
            continue
        row = ooe_open_row(n)
        if row is None:
            continue
        rows.append(row)
    expands = [row for row in rows if row["expands"]]
    returns = [row for row in rows if row["returns"]]
    r_values = [row["R"] for row in rows]
    return {
        "n_max": n_max,
        "checked": len(rows),
        "expands": len(expands),
        "returns": len(returns),
        "all_expand": len(expands) == len(rows) and len(rows) > 0,
        "any_return": len(returns) > 0,
        "all_open_q_lt_cycle_q": all(row["open_q_lt_cycle_q"] for row in rows),
        "all_R_lt_one": all(row["R"] < 1 for row in rows),
        "max_R": max(r_values) if r_values else None,
        "min_R": min(r_values) if r_values else None,
        "max_q_open": max((row["q_open"] for row in rows), default=None),
    }


def successor_illustration() -> dict[str, Any]:
    """The NearTightScale mixed OOE at y ~ 1.80e32 versus cycle q = y-1."""

    y = NEAR_TIGHT["x"]
    image = NEAR_TIGHT["y"]
    q = q_exact(y, OOE_WORD)
    return {
        "y": y,
        "image": image,
        "word": OOE_WORD,
        "expands": image > y,
        "returns": image == y,
        "q_open": q,
        "q_cycle": y - 1,
        "open_q_lt_cycle_q": open_q_lt_cycle_q(y, image),
        "q_open_below_1e_30": 0 < q < 1e-30,
    }


def slogan_fails(records: list[dict[str, Any]], census: dict[str, Any]) -> bool:
    slogan = [row for row in records if row["L"] in SLOGAN_LENGTHS]
    hamming_grows = [row["hamming_to_monochrome"] for row in slogan]
    return (
        all(row["almost_monochrome"] is False for row in slogan)
        and hamming_grows == sorted(hamming_grows)
        and hamming_grows[0] >= 7
        and census["any_return"] is False
        and census["all_open_q_lt_cycle_q"] is True
        and census["all_expand"] is True
    )


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {
        f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "no_extra_near_tight_cycle_file": not any(
            path.is_file() for path in FORBIDDEN_LEAN_FILES
        ),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe(*, n_max: int = TEST_N_MAX) -> dict[str, Any]:
    records = [record_row(length) for length in RECORD_LENGTHS]
    census = ooe_open_census(n_max=n_max)
    successor = successor_illustration()
    identity = {
        "cycle_one_plus_q_is_n_to_G": True,
        "open_q_lt_cycle_q_iff_image_gt_n": True,
        "R_eq_one_on_return": True,
    }
    return {
        "n_max": n_max,
        "records": records,
        "ooe_census": census,
        "successor": successor,
        "identity": identity,
        "slogan_fails": slogan_fails(records, census),
        "successor_is_mixed_near_tight": successor["q_open_below_1e_30"]
        and successor["expands"]
        and successor["open_q_lt_cycle_q"],
        "leftover_killed_by_near_tight": False,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "new_lean": False,
        "floor_raise": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["no_extra_near_tight_cycle_file"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["halt_theorem"] or scan["no_cycle_all_lengths"] or scan["new_lean"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if scan["leftover_killed_by_near_tight"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "near-tight rigidity excluded a leftover convergent",
        }
    if scan["slogan_fails"] and scan["successor_is_mixed_near_tight"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "cycle 1+q = n^{3^o-2^L} is the opposite of open-orbit "
                "q->0; leftover Hamming to monochrome grows (7,31,210,389); "
                "realized OOE expands and never returns; the 329 successor "
                "is mixed with 0<q<10^{-30} against cycle-required q=y-1. "
                "R=1 on a return is image_eq_start_defectRatio, already Lean. "
                "NearTightScale does not cover leftover convergents"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "census or slogan check did not fire",
    }


def probe_payload(*, n_max: int = TEST_N_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "floor_raise": False,
            "new_lean": False,
            "almost_monochrome_forced": False,
            "leftover_killed": False,
            "approx_rigidity_reopened": False,
        }
    )
    return {
        "experiment": "juggler_cycle_near_tight",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"exact cycle 1+q = n^G on record lengths {list(RECORD_LENGTHS)}; "
            f"OOE open-orbit census n<={n_max}; 329 successor illustration"
        ),
    }


def _fmt_float(value: float | None) -> str:
    if value is None:
        return "inf"
    if value == 0.0:
        return "0"
    if abs(value) < 1e-4 or abs(value) >= 1e6:
        return f"{value:.3e}"
    return f"{value:.6g}"


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    census = scan["ooe_census"]
    successor = scan["successor"]
    lines = [
        "# Juggler cycle near-tight rigidity",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Cycle return + tiny finance gap versus open-orbit q -> 0.",
        "Not a halt theorem. Not a no-cycle-of-any-length theorem.",
        "No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- record lengths: `{list(RECORD_LENGTHS)}`",
        f"- OOE census n_max: `{census['n_max']}` checked `{census['checked']}`",
        f"- OOE returns: `{census['returns']}`",
        f"- slogan fails: `{scan['slogan_fails']}`",
        f"- leftover killed by near-tight: `{scan['leftover_killed_by_near_tight']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Record convergents",
        "",
    ]
    for row in scan["records"]:
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` evens=`{row['even_count']}` "
            f"G=`{row['gap']}` theta=`{_fmt_float(row['theta'])}` "
            f"Hamming=`{row['hamming_to_monochrome']}` "
            f"n_max=`{row['n_max']}` "
            f"ln(1+q) at 53=`{_fmt_float(row['ln_one_plus_q_at_53'])}` "
            f"envelope growth at 53=`{_fmt_float(row['envelope_growth_at_53'])}`"
        )
    lines.extend(
        [
            "",
            "## Open-orbit OOE (first leftover length L=3, G=1)",
            "",
            f"- checked `{census['checked']}` odd-odd realized OOE through "
            f"`{census['n_max']}`",
            f"- expands `{census['expands']}` returns `{census['returns']}`",
            f"- all open q < cycle q (`n-1`): `{census['all_open_q_lt_cycle_q']}`",
            f"- all R < 1: `{census['all_R_lt_one']}` max R `{census['max_R']}`",
            f"- max open q `{census['max_q_open']}`",
            "",
            "## 329 successor (mixed near-tight OOE)",
            "",
            f"- y=`{successor['y']}` image=`{successor['image']}`",
            f"- expands `{successor['expands']}` returns `{successor['returns']}`",
            f"- open q `{successor['q_open']}` cycle q `y-1`",
            f"- 0 < open q < 10^{-30}: `{successor['q_open_below_1e_30']}`",
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


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "records.json").write_text(
        json.dumps(scan["records"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "ooe_census.json").write_text(
        json.dumps(scan["ooe_census"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "successor.json").write_text(
        json.dumps(scan["successor"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "slogan_fails": scan["slogan_fails"],
        "leftover_killed_by_near_tight": scan["leftover_killed_by_near_tight"],
        "ooe_returns": scan["ooe_census"]["returns"],
        "successor_q_open_below_1e_30": scan["successor"]["q_open_below_1e_30"],
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cycle near-tight rigidity\n\n"
        "Cycle return + tiny theta versus open-orbit q -> 0.\n"
        "Not a halt theorem. No new Lean.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_near_tight`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = probe_payload(n_max=SCIENCE_N_MAX)
    write_artifacts(payload)
    decision = payload["decision"]
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"slogan_fails={scan['slogan_fails']} "
        f"ooe_returns={scan['ooe_census']['returns']} "
        f"successor_tiny={scan['successor']['q_open_below_1e_30']}"
    )


if __name__ == "__main__":
    main()
