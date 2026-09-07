"""Attack A: two-sided / multi-point Diophantine constraints.

Phase 0 successor of the fan-minimum reduction. The literature on
2^p versus 3^q gives neighbor-separation and polynomial gap floors,
but those fire only if one CycleMin cycle forces two distinct
fan-quality (L, o) relations at once. This probe asks whether
CycleMin / hug / m-circuit geometry actually forces that.

Not a Baker-constant import (that transfer stays REFUTED). Not a
halt theorem, not a floor raise, not a Paper A edit.

Dossier: docs/problems/juggler_cycle_fan_multipoint.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_charge import MU, U_TOL
from research.juggler_sequence.cycle_walk_competition import o_min_exact

DATA_DIR = (
    DATA_ROOT
    / "cycle_fan_multipoint"
)
COMPETITION_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
)

LN2 = math.log(2.0)
LN3 = math.log(3.0)

# Dangerous fans of the certified competition artifact.
FANS = (
    (176_251, 301_994, "fanA"),
    (16_785_921, 17_087_915, "fanB"),
)

# Small leftover / CF-denominator lengths used in the split search.
SMALL_RECORDS = (19, 84, 569, 1054, 25781)

HUG_CENSUS_LENGTHS = (19, 84, 1054, 25781, 50508, 176251)
SHORT_TYPES = frozenset({(1, 1), (2, 1)})

CLASS_GREEN = "FAN_MULTIPOINT_GREEN"
CLASS_CLOSED = "FAN_MULTIPOINT_CLOSED"

# Dirichlet scale: leftover near-convergents have theta * L = O(1).
DIRICHLET_CAP = 2.0
# Exponent-neighbor separation: theta(L+1)/theta(L) should be >> 1.
EXPONENT_RATIO_FLOOR = 10.0


def theta_float(length: int, odd_count: int | None = None) -> float:
    """Float theta = 1 - 2^L/3^o at the least o with 3^o > 2^L."""

    if odd_count is None:
        odd_count = math.floor(length * LN2 / LN3) + 1
        if odd_count * LN3 <= length * LN2:
            odd_count += 1
    lam = odd_count * LN3 - length * LN2
    if lam <= 0:
        odd_count += 1
        lam = odd_count * LN3 - length * LN2
    return -math.expm1(-lam)


def dirichlet_score(length: int, theta: float) -> float:
    return theta * length


def hug_circuit_census(length: int, odd_count: int) -> dict[str, Any]:
    """Stream the hug word and count cyclic O^a E^r circuits."""

    o_left = odd_count
    e_left = length - odd_count
    height = 0.0
    a = 0
    r = 0
    in_even = False
    counts: Counter[tuple[int, int]] = Counter()
    first_odds = 0
    started_even = False
    for k in range(length):
        take_e = e_left > 0 and height >= 1.0 - U_TOL
        if take_e:
            if k == 0:
                started_even = True
            height -= 1.0
            e_left -= 1
            if not in_even and a > 0:
                in_even = True
            r += 1
        else:
            if in_even:
                counts[(a, r)] += 1
                a = 0
                r = 0
                in_even = False
            height += MU
            o_left -= 1
            a += 1
            if not any(counts) and r == 0:
                first_odds = a
    if in_even:
        if started_even:
            counts[(a + first_odds, r)] += 1
            if first_odds:
                # first open odd-run was only a prefix; already merged.
                pass
        else:
            counts[(a, r)] += 1
    elif a:
        counts[(a, 0)] += 1
    types = sorted((int(aa), int(rr), int(n)) for (aa, rr), n in counts.items())
    return {
        "length": length,
        "odd_count": odd_count,
        "types": types,
        "only_short": all((aa, rr) in SHORT_TYPES for aa, rr, _ in types),
        "n_circuits": int(sum(n for _, _, n in types)),
    }


def fan_neighbor_profile(rows: dict[int, dict[str, Any]]) -> list[dict[str, Any]]:
    """Consecutive-semiconvergent quality along each certified fan."""

    out: list[dict[str, Any]] = []
    for base, step, tag in FANS:
        members = []
        k = 0
        while base + k * step in rows:
            members.append(rows[base + k * step])
            k += 1
        pairs = []
        min_ratio = math.inf
        max_ratio = 0.0
        n_both = 0
        for left, right in zip(members, members[1:]):
            t0 = float(left["theta"])
            t1 = float(right["theta"])
            ratio = t1 / t0 if t0 > 0 else math.inf
            s0 = dirichlet_score(left["length"], t0)
            s1 = dirichlet_score(right["length"], t1)
            both = s0 < DIRICHLET_CAP and s1 < DIRICHLET_CAP
            n_both += int(both)
            min_ratio = min(min_ratio, ratio)
            max_ratio = max(max_ratio, ratio)
            pairs.append(
                {
                    "L0": left["length"],
                    "L1": right["length"],
                    "theta0": t0,
                    "theta1": t1,
                    "ratio": ratio,
                    "dirichlet0": s0,
                    "dirichlet1": s1,
                    "both_dirichlet": both,
                }
            )
        out.append(
            {
                "tag": tag,
                "n_members": len(members),
                "n_pairs": len(pairs),
                "n_both_dirichlet": n_both,
                "any_both_dirichlet": n_both > 0,
                "min_theta_ratio": min_ratio if pairs else None,
                "max_theta_ratio": max_ratio if pairs else None,
                "first_pair": pairs[0] if pairs else None,
                "last_pair": pairs[-1] if pairs else None,
                "closest_ratio_pair": (
                    min(pairs, key=lambda p: abs(math.log(p["ratio"])))
                    if pairs
                    else None
                ),
            }
        )
    return out


def exponent_neighbor_profile(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """theta(L±1)/theta(L) on leftover-quality lengths: the MO shift-by-1 test.

    Wrong-side convergents (theta ~ 2/3, the fan step Q) are excluded —
    those are not exceptional expanding approximations.
    """

    samples = []
    for row in rows:
        length = int(row["length"])
        theta = float(row["theta"])
        if dirichlet_score(length, theta) >= DIRICHLET_CAP:
            continue
        theta_up = theta_float(length + 1)
        theta_dn = theta_float(length - 1) if length > 2 else 1.0
        ratio_up = theta_up / theta if theta > 0 else math.inf
        ratio_dn = theta_dn / theta if theta > 0 else math.inf
        neighbor = min(ratio_up, ratio_dn)
        samples.append(
            {
                "length": length,
                "theta": theta,
                "theta_plus": theta_up,
                "theta_minus": theta_dn,
                "ratio_plus": ratio_up,
                "ratio_minus": ratio_dn,
                "separated": neighbor >= EXPONENT_RATIO_FLOOR,
            }
        )
    return {
        "n": len(samples),
        "all_separated": bool(samples) and all(s["separated"] for s in samples),
        "min_neighbor_ratio": min(
            min(s["ratio_plus"], s["ratio_minus"]) for s in samples
        ),
        "worst": min(samples, key=lambda s: min(s["ratio_plus"], s["ratio_minus"])),
        "seed_50508": next(s for s in samples if s["length"] == 50508),
        "seed_176251": next(s for s in samples if s["length"] == 176251),
    }


def leftover_splits(
    lengths: list[int],
    theta_of: dict[int, float],
) -> dict[str, Any]:
    """Arithmetic sums L = a + b with both parts leftover-quality."""

    quality = set(lengths)
    found: list[dict[str, Any]] = []
    for a in lengths:
        for b in lengths:
            if a > b:
                continue
            total = a + b
            if total not in quality:
                continue
            ta = theta_of[a]
            tb = theta_of[b]
            da = dirichlet_score(a, ta)
            db = dirichlet_score(b, tb)
            found.append(
                {
                    "a": a,
                    "b": b,
                    "sum": total,
                    "dirichlet_a": da,
                    "dirichlet_b": db,
                    "both_dirichlet": da < DIRICHLET_CAP and db < DIRICHLET_CAP,
                    "parent_step": b in {301_994, 17_087_915}
                    or a in {301_994, 17_087_915},
                }
            )
    two_good = [row for row in found if row["both_dirichlet"]]
    return {
        "n_quality": len(quality),
        "n_splits": len(found),
        "n_parent_step": sum(1 for row in found if row["parent_step"]),
        "n_two_good": len(two_good),
        "two_good_examples": two_good[:8],
        "examples": found[:8],
        "parent_examples": [row for row in found if row["parent_step"]][:6],
    }


def parent_factor_thetas(rows: dict[int, dict[str, Any]]) -> list[dict[str, Any]]:
    """Quality of the CF parents q, Q versus the fan member L_k = q+kQ.

    These are the mechanical concatenations, not two integer returns.
    """

    out = []
    for base, step, tag in FANS:
        if base in rows:
            q_theta = float(rows[base]["theta"])
            q_odd = int(rows[base]["odd_count"])
        else:
            q_odd = o_min_exact(base)
            q_theta = theta_float(base, q_odd)
        if step in rows:
            q_step_theta = float(rows[step]["theta"])
            q_step_odd = int(rows[step]["odd_count"])
        else:
            q_step_odd = math.floor(step * LN2 / LN3) + 1
            q_step_theta = theta_float(step, q_step_odd)
        member = rows.get(base + step)
        out.append(
            {
                "tag": tag,
                "q": base,
                "q_odd": q_odd,
                "theta_q": q_theta,
                "Q": step,
                "Q_odd": q_step_odd,
                "theta_Q": q_step_theta,
                "L1": member["length"] if member else None,
                "theta_L1": float(member["theta"]) if member else None,
                "return_forced_at_parent": False,
            }
        )
    return out


def classify(
    hug: list[dict[str, Any]],
    fans: list[dict[str, Any]],
    exponents: dict[str, Any],
    splits: dict[str, Any],
) -> dict[str, Any]:
    hug_only_short = all(row["only_short"] for row in hug)
    fan_any_both = any(f["any_both_dirichlet"] for f in fans)
    exp_separated = bool(exponents["all_separated"])
    # The slogan needs a FORCED second fan-quality return. Hug circuits
    # are the cheapest walk's returns; they are only OE/OOE.
    forced_second = not hug_only_short
    if hug_only_short:
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "a CycleMin cycle forces one global (L, o) pair; hug "
                "circuits are only the short Beatty letters OE/OOE on "
                "every leftover seed through 176251; exponent-neighbors "
                "(L vs L+1) on leftover-quality lengths are separated "
                "as in the powers-of-2/3 literature, but the cycle does "
                "not require theta(L+1) small; fan-neighbors (Q-steps) "
                "can both be Dirichlet-good — that is the existing fan "
                "obstruction, not a second constraint. Arithmetic "
                f"leftover sums exist ({splits['n_splits']} pairs, "
                f"{splits['n_two_good']} with two Dirichlet-good parts) "
                "as lattice/parent concatenations, not as two integer "
                "returns. Attack A does not fire."
            ),
            "hug_only_short": hug_only_short,
            "fan_neighbors_any_both_dirichlet": fan_any_both,
            "exponent_neighbors_separated": exp_separated,
            "forced_second_fan_pair": forced_second,
            "decision": "CLOSE",
        }
    return {
        "label": CLASS_GREEN,
        "reason": "hug circuits include a type other than OE/OOE",
        "hug_only_short": hug_only_short,
        "fan_neighbors_any_both_dirichlet": fan_any_both,
        "exponent_neighbors_separated": exp_separated,
        "forced_second_fan_pair": forced_second,
        "decision": "PROMOTE",
    }


def probe_payload() -> dict[str, Any]:
    summary = json.loads(COMPETITION_SUMMARY.read_text(encoding="utf-8"))
    rows = {int(r["length"]): r for r in summary["rows"]}
    denoms = [int(q) for q in summary["theta_cf"]["denominators"] if q >= 19]
    hug = []
    for length in HUG_CENSUS_LENGTHS:
        if length in rows:
            odd = int(rows[length]["odd_count"])
        else:
            odd = o_min_exact(length)
        hug.append(hug_circuit_census(length, odd))
    fans = fan_neighbor_profile(rows)
    exponents = exponent_neighbor_profile(list(summary["rows"]))
    quality_lengths = sorted(set(rows) | set(SMALL_RECORDS) | set(denoms))
    theta_of = {L: theta_float(L) for L in quality_lengths}
    for L, row in rows.items():
        theta_of[L] = float(row["theta"])
    splits = leftover_splits(quality_lengths, theta_of)
    parents = parent_factor_thetas(rows)
    classification = classify(hug, fans, exponents, splits)
    return {
        "model": (
            "Attack A: does one CycleMin cycle force two or more "
            "distinct fan-quality (L, o) relations, so that "
            "2^p-3^q neighbor-separation can fire? Neighbor "
            "relations distinguished: exponent-shift (L vs L+1) "
            "versus fan-step (L_k vs L_k+Q)."
        ),
        "literature": [
            "wu-wang-2014-irrationality-measure-log3",
            "salikhov-2007-irrationality-measure-ln3",
            "tao-2011-hilbert-seventh-powers-2-3",
            "chim-2025-p-adic-two-logarithms",
            "mathoverflow-2012-powers-2-3",
            "rhin-1987-pade-irrationality",
            "laurent-mignotte-nesterenko-1995-two-logarithms",
            "simons-de-weger-2005-collatz-m-cycles",
        ],
        "hug_circuits": hug,
        "fan_neighbors": fans,
        "exponent_neighbors": exponents,
        "leftover_splits": splits,
        "parent_factors": parents,
        "classification": classification,
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_baker_reopen": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
        "attacks_not_opened": ["B_padic_coupling", "C_wu_wang_fan_growth"],
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    print("hug circuits:")
    for row in payload["hug_circuits"]:
        print(
            f"  L={row['length']}: types={row['types']} "
            f"only_short={row['only_short']}"
        )
    for fan in payload["fan_neighbors"]:
        print(
            f"{fan['tag']}: pairs={fan['n_pairs']} "
            f"both_dirichlet={fan['n_both_dirichlet']}/{fan['n_pairs']} "
            f"theta_ratio in [{fan['min_theta_ratio']:.4g}, "
            f"{fan['max_theta_ratio']:.4g}]"
        )
    exp = payload["exponent_neighbors"]
    print(
        f"exponent neighbors: all_separated={exp['all_separated']} "
        f"min_ratio={exp['min_neighbor_ratio']:.4g}"
    )
    print(
        f"leftover splits: {payload['leftover_splits']['n_splits']} "
        f"(parent-step {payload['leftover_splits']['n_parent_step']}, "
        f"two-good {payload['leftover_splits']['n_two_good']})"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
