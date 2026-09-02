"""Cumulative floor loss versus EnvelopeState / globalDefect.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a local-defect reopen, not a modulus search, not a corridor, not
p-adic, and not an irrational-approximation attack.

Phase 0 asks whether the exact floor remainders discarded by
EnvelopeState accumulate into a survival-margin obstruction that is
not already globalDefect, 1+q, Amplify, or generic OE. Paper A is
unchanged.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.global_defect import (
    global_defect,
    image_after,
    local_defect,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.normalized_defect import (
    BIT_LIMIT,
    bits_ok,
    defect_ratio,
    measurable,
)
from research.juggler_sequence.minimal_anchor_closure import WORD_L
from research.juggler_sequence.odd_chain_minimality import L_LAB, LONG_ODD_STARTS
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cumulative_floor_loss.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cumulative_floor_loss.md"

CLASS_CLOSED = "CUMULATIVE_FLOOR_LOSS_CLOSED"
CLASS_PARK = "CUMULATIVE_FLOOR_LOSS_PARK"
CLASS_GREEN = "CUMULATIVE_FLOOR_LOSS_GREEN"
CLASS_INCOMPLETE = "CUMULATIVE_FLOOR_LOSS_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
LONG_LABS = (*LONG_ODD_STARTS, L_LAB)
ZERO_DEFECT = 9
WINDOW_HI = 201

EXISTING_LEAN = (
    "localDefectOdd",
    "localDefectEven",
    "globalDefect",
    "global_defect_identity",
    "globalDefect_eq_powerDeficit",
    "onePlusSlack_concat",
    "defectRatio_le_one_iff_image_ge",
    "amplifyDefect",
    "sequentialDefect",
    "oddMordellStep",
    "EnvelopeState",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "FloorLoss",
    "CumulativeLoss",
    "odd_run_cumulative_defect",
    "odd_run_loss_bound",
    "LossBudget",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "FloorLoss.lean",
    JUGGLER_DIR / "CumulativeLoss.lean",
    JUGGLER_DIR / "LossBudget.lean",
)


def first_odd_run(n: int) -> dict[str, Any]:
    """Initial odd states, then the even reset and post-even image."""

    if n < 2 or n % 2 == 0:
        raise ValueError("first_odd_run requires an odd start")
    odds = [n]
    current = n
    while current % 2 == 1:
        current = floor_power(current)
        if current % 2 == 1:
            odds.append(current)
        else:
            even = current
            break
    else:
        raise ValueError(f"{n} never left the odd integers")
    post = floor_power(even)
    steps = []
    chain = odds + [even]
    for x, y in zip(chain, chain[1:]):
        delta = local_defect(x)
        width = 2 * y + 1
        steps.append(
            {
                "x": x,
                "y": y,
                "delta": delta,
                "width": width,
                "eps": str(Fraction(delta, width)),
                "eps_float": delta / width,
                "zero": delta == 0,
            }
        )
    return {
        "n": n,
        "odds": odds,
        "odd_count": len(odds),
        "even": even,
        "post": post,
        "word": "O" * len(odds),
        "steps": steps,
    }


def proposed_product_holds(n: int, word: str) -> bool:
    """The Phase-0 candidate x_r^{2^r}/x_0^{3^r} = prod ρ_i^{2^{r-1-i}}.

    This omits the cubic lift of running slack. It holds for r=1, and
    for r>=2 only when every earlier odd step is tight.
    """

    if not word or set(word) != {"O"}:
        raise ValueError("proposed_product_holds expects a nonempty odd word")
    states = [n]
    current = n
    for _ in word:
        current = floor_power(current)
        states.append(current)
    r = len(word)
    left = states[-1] ** (1 << r)
    right = n ** (3**r)
    for i, letter_state in enumerate(states[:-1]):
        y = states[i + 1]
        weight = 1 << (r - 1 - i)
        left *= letter_state ** (3 * weight)
        right *= (y * y) ** weight
    return left == right


def global_identity_holds(n: int, word: str) -> bool:
    """n^{3^{#O}} = T_w(n)^{2^{|w|}} + globalDefect(n,w)."""

    if not measurable(n, word):
        return True
    end = image_after(n, word)
    return n ** (3 ** word.count("O")) == end ** (1 << len(word)) + global_defect(
        n, word
    )


def run_budget(n: int, word: str) -> dict[str, Any]:
    """Exact Δ, surplus, and R when the powers stay inside the bit budget."""

    end = image_after(n, word)
    ok = measurable(n, word)
    row: dict[str, Any] = {
        "n": n,
        "word": word,
        "image": end,
        "image_ge_n": end >= n,
        "measurable": ok,
    }
    if not ok:
        return row
    delta = global_defect(n, word)
    ratio = defect_ratio(n, word)
    surplus = None if ratio is None else ratio[1]
    r_gt_one = None if ratio is None else ratio[0] > ratio[1]
    row.update(
        {
            "Delta": delta,
            "surplus": surplus,
            "R_gt_1": r_gt_one,
            "mechanism_A": bool(r_gt_one),
            "ratio_matches_survival": (r_gt_one is False and end >= n)
            or (r_gt_one is True and end < n)
            or (ratio is None),
        }
    )
    return row


def two_step_amplification(n: int) -> dict[str, Any] | None:
    if n % 2 == 0 or floor_power(n) % 2 == 0:
        return None
    word = "OO"
    if not measurable(n, word):
        return None
    y = floor_power(n)
    z = floor_power(y)
    d0 = local_defect(n)
    d1 = local_defect(y)
    d2 = global_defect(n, word)
    naive = d0 + d1
    return {
        "n": n,
        "d0": d0,
        "d1": d1,
        "D2": d2,
        "naive": naive,
        "amplified": d2 > naive,
        "identity": d2 == n**9 - z**4,
    }


def long_run_local(n: int) -> dict[str, Any]:
    source = n
    if n == L_LAB:
        # 33391 follows L to 67709; the long odd run starts there.
        current = n
        for _ in WORD_L:
            current = floor_power(current)
        source = current
    run = first_odd_run(source)
    eps = [step["eps_float"] for step in run["steps"]]
    return {
        "n": n,
        "source": source,
        "odd_count": run["odd_count"],
        "min_eps": min(eps),
        "max_eps": max(eps),
        "any_zero": any(step["zero"] for step in run["steps"]),
        "post_ge_source": run["post"] >= source,
        "even_ge_source": run["even"] >= source,
        "word": run["word"],
        "measurable": bits_ok(source, 3 ** run["odd_count"]),
    }


def run_probe() -> dict[str, Any]:
    runs = {n: first_odd_run(n) for n in STARTS}
    budgets = {}
    proposed = {}
    identities = {}
    amplifications = {}
    for n, run in runs.items():
        word = run["word"]
        budgets[n] = run_budget(n, word)
        proposed[n] = proposed_product_holds(n, word)
        identities[n] = global_identity_holds(n, word)
        amp = two_step_amplification(n)
        if amp is not None:
            amplifications[n] = amp
    zero = first_odd_run(ZERO_DEFECT)
    long_rows = {n: long_run_local(n) for n in LONG_LABS}
    window_zero = []
    window_tiny = []
    for n in range(3, WINDOW_HI, 2):
        y = floor_power(n)
        delta = local_defect(n)
        if delta == 0:
            window_zero.append(n)
        if delta / (2 * y + 1) < 0.01:
            window_tiny.append(n)
    leftover_r = {n: runs[n]["odd_count"] for n in CONTROLS}
    return {
        "basin": "ordinary_integers",
        "runs": {str(n): runs[n] for n in STARTS},
        "budgets": {str(n): budgets[n] for n in STARTS},
        "proposed_products": {str(n): proposed[n] for n in STARTS},
        "global_identities": {str(n): identities[n] for n in STARTS},
        "amplifications": {str(n): amplifications[n] for n in amplifications},
        "zero_defect": {
            "n": ZERO_DEFECT,
            "first_delta_zero": zero["steps"][0]["zero"],
            "odd_count": zero["odd_count"],
        },
        "long_runs": {str(n): long_rows[n] for n in LONG_LABS},
        "window_zero": window_zero,
        "window_tiny_eps": window_tiny,
        "dictionary_ok": all(identities.values())
        and all(amp["identity"] for amp in amplifications.values()),
        "proposed_product_false": not any(proposed.values()),
        "global_identity_true": all(identities.values()),
        "leftover_first_ooe": all(leftover_r[n] == 2 for n in CONTROLS),
        "no_mechanism_A": all(
            not row.get("mechanism_A") for row in budgets.values() if row["measurable"]
        ),
        "ratio_is_survival": all(
            row.get("ratio_matches_survival", True)
            for row in budgets.values()
            if row["measurable"]
        ),
        "amplification_exists": all(
            amp["amplified"] for amp in amplifications.values()
        ),
        "zero_first_defect": zero["steps"][0]["zero"],
        "long_runs_survive": all(
            row["post_ge_source"] and row["even_ge_source"] for row in long_rows.values()
        ),
        "long_runs_not_measurable": all(
            not row["measurable"] for row in long_rows.values() if row["odd_count"] >= 8
        ),
        "letter_chain": False,
        "padic": False,
        "analytic_nt": False,
        "floor_loss_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "gap_reopen": False,
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
        "not_in_paper_barrel": "FloorLoss" not in paper
        and "CumulativeLoss" not in paper
        and "LossBudget" not in paper,
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
        or scan["padic"]
        or scan["analytic_nt"]
        or scan["floor_loss_lean"]
        or scan["halt_theorem"]
        or scan["gap_reopen"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["no_mechanism_A"] is False:
        return {
            "classification": CLASS_GREEN,
            "reason": "an AboveAnchor odd run has R>1 without dropping",
        }
    if (
        scan["dictionary_ok"]
        and scan["proposed_product_false"]
        and scan["global_identity_true"]
        and scan["no_mechanism_A"]
        and scan["ratio_is_survival"]
        and scan["zero_first_defect"]
        and scan["leftover_first_ooe"]
        and scan["long_runs_survive"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "the proposed rho-product omits the cubic slack lift; "
                "Delta_r is globalDefect; R>1 is T<n; delta_0 vanishes "
                "on odd squares; leftovers are OOE; long runs survive"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "dictionary matched only in part",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "new_cumulative_obstruction": False,
            "floor_loss_lean": False,
            "padic": False,
            "analytic_nt": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_cumulative_floor_loss",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "map Delta_r / product / R to globalDefect and 1+q; "
            "named first odd runs; 9; 329/33391 local eps; no huge powers"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cumulative floor loss",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Exact floor remainders versus the existing global-defect spine.",
        "Not a halt theorem. Not a new `FloorLoss` layer.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     does discarded floor loss accumulate",
        "                        past the survival margin?",
        "Novelty hypothesis      amplified Delta exceeds slack",
        "                        independently of T<n",
        "Maximum Phase-0 scope   named first runs; 9; 329/33391;",
        "                        no Lean; no p-adic",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- dictionary ok: `{scan['dictionary_ok']}`",
        f"- leftover first OOE: `{scan['leftover_first_ooe']}`",
        f"- proposed product false: `{scan['proposed_product_false']}`",
        f"- global identity: `{scan['global_identity_true']}`",
        f"- mechanism A: `{not scan['no_mechanism_A']}`",
        f"- zero first defect: `{scan['zero_first_defect']}`",
        f"- window zero: `{scan['window_zero']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Named first odd runs",
        "",
    ]
    for n in STARTS:
        run = scan["runs"][str(n)]
        budget = scan["budgets"][str(n)]
        lines.append(
            f"- `{n}`: odds=`{run['odd_count']}` word=`{run['word']}` "
            f"image_ge_n=`{budget['image_ge_n']}` "
            f"measurable=`{budget['measurable']}` "
            f"R_gt_1=`{budget.get('R_gt_1')}`"
        )
        for step in run["steps"]:
            lines.append(
                f"  - x=`{step['x']}` y=`{step['y']}` "
                f"delta=`{step['delta']}` eps=`{step['eps']}`"
            )
    lines.extend(["", "## Amplification D2 vs d0+d1", ""])
    for n, amp in scan["amplifications"].items():
        lines.append(
            f"- `{n}`: d0=`{amp['d0']}` d1=`{amp['d1']}` "
            f"D2=`{amp['D2']}` naive=`{amp['naive']}` "
            f"amplified=`{amp['amplified']}`"
        )
    lines.extend(["", "## Long runs (local only)", ""])
    for n, row in scan["long_runs"].items():
        lines.append(
            f"- `{n}` source=`{row['source']}` odds=`{row['odd_count']}` "
            f"min_eps=`{row['min_eps']}` max_eps=`{row['max_eps']}` "
            f"survive=`{row['post_ge_source']}` "
            f"measurable=`{row['measurable']}`"
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
    scan = payload["scan"]
    print("leftover_ooe", scan["leftover_first_ooe"])
    print("mechanism_A", not scan["no_mechanism_A"])
    print("zero", scan["window_zero"])
    print("long", scan["long_runs"])


if __name__ == "__main__":
    main()
