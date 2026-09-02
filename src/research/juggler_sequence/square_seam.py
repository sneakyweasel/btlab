"""Square-seam cycle lemma. Phase 0 only.

If a nontrivial cycle contains an isolated perfect square, the
zero-defect step is an algebraic junction. Split the map:

- odd isolated: s odd, not a square, J(s^2) = s^3, increment log2(3/2)
- even isolated: k even, not a square, J(k^2) = k, increment -1

Ask whether the two-sided constraints around those seams are a new
word factor, a strictly stronger finance identity, or a Diophantine
restriction on s — or whether they reduce to even_preimage_iff,
odd_preimage_unique, CycleMin square-scale, and a vanishing local defect.

Not a halt theorem, not an exact-floor-impact recensus, not a
cyclic-seam reopen, and not a leftover-killer campaign.
"""

from __future__ import annotations

import json
import math
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import even_preimage, even_preimage_width, odd_preimage_integers
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import JUGGLER_DIR, has_named, juggler_text
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "square_seam"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_square_seam.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_square_seam.md"

CLASS_REPARAM = "SQUARE_SEAM_REPARAMETERIZATION"
CLASS_NEW = "SQUARE_SEAM_NEW_CONSTRAINT"

N0 = 162_849_448
EPS_CONST = 1.2
PARENT_MAX = 200
SHORT_ROOT_MAX = 30
SHORT_LEN = 3
LEFTOVER_L = 25_781
BLOCKER_L = 478_245

LOG2_3_2 = math.log2(1.5)

EXISTING_LEAN = (
    "even_preimage_iff",
    "odd_preimage_unique",
    "localDefectEven_eq_zero_iff",
    "localDefectOdd_eq_zero_iff",
    "power_bound_eq_implies_monochrome",
    "cycleMin_start_odd",
    "cycleMin_even_ge_sq",
    "even_tower_to_one",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)
NEW_LEAN_FILES = (
    JUGGLER_DIR / "SquareSeam.lean",
    JUGGLER_DIR / "SquareSeamCycle.lean",
)


def letter_of(n: int) -> str:
    return "O" if n % 2 else "E"


def odd_parents(q: int) -> list[int]:
    return [z for z in odd_preimage_integers(q) if z % 2 == 1 and floor_power(z) == q]


def even_parent_count(q: int) -> int:
    lo, hi = even_preimage(q)
    start = lo if lo % 2 == 0 else lo + 1
    if start >= hi:
        return 0
    return (hi - 1 - start) // 2 + 1


def odd_isolated_seam(s: int) -> dict[str, Any]:
    if s < 1 or s % 2 == 0:
        raise ValueError("odd_isolated_seam requires a positive odd integer")
    state = s * s
    image = floor_power(state)
    cube = s * s * s
    isolated = not is_square(s)
    return {
        "kind": "odd",
        "root": s,
        "state": state,
        "image": image,
        "expected": cube,
        "exact": image == cube and local_tight(state),
        "crumb": local_defect(state),
        "isolated": isolated,
        "next_letter": letter_of(image),
        "local_word": "*" + letter_of(state) + letter_of(image),
        "log_increment": LOG2_3_2,
        "odd_parents": odd_parents(state),
        "even_width": even_preimage_width(state),
        "even_parent_count": even_parent_count(state),
    }


def even_isolated_seam(k: int) -> dict[str, Any]:
    if k < 2 or k % 2 == 1:
        raise ValueError("even_isolated_seam requires an even integer >= 2")
    state = k * k
    image = floor_power(state)
    isolated = not is_square(k)
    return {
        "kind": "even",
        "root": k,
        "state": state,
        "image": image,
        "expected": k,
        "exact": image == k and local_tight(state),
        "crumb": local_defect(state),
        "isolated": isolated,
        "next_letter": letter_of(image),
        "local_word": "*" + letter_of(state) + letter_of(image),
        "log_increment": -1.0,
        "odd_parents": odd_parents(state),
        "even_width": even_preimage_width(state),
        "even_parent_count": even_parent_count(state),
        "tower_square": is_square(k),
    }


def fixture_nine() -> dict[str, Any]:
    return odd_isolated_seam(3)


def fixture_thirty_six() -> dict[str, Any]:
    return even_isolated_seam(6)


def fixture_one_hundred() -> dict[str, Any]:
    return even_isolated_seam(10)


def _odd_roots(max_root: int) -> list[int]:
    return [s for s in range(3, max_root + 1, 2) if not is_square(s)]


def _even_roots(max_root: int) -> list[int]:
    return [k for k in range(2, max_root + 1, 2) if not is_square(k)]


def parent_census(*, max_root: int = PARENT_MAX) -> dict[str, Any]:
    odd_rows = []
    even_rows = []
    odd_multi = 0
    odd_occupied = 0
    even_width_ok = True
    for s in _odd_roots(max_root):
        row = odd_isolated_seam(s)
        n_odd = len(row["odd_parents"])
        if n_odd > 1:
            odd_multi += 1
        if n_odd == 1:
            odd_occupied += 1
        expected_width = 2 * row["state"] + 1
        even_width_ok = even_width_ok and row["even_width"] == expected_width
        if s <= 15 or n_odd:
            odd_rows.append(
                {
                    "s": s,
                    "state": row["state"],
                    "n_odd_parents": n_odd,
                    "odd_parents": row["odd_parents"],
                    "even_width": row["even_width"],
                    "exact": row["exact"],
                    "isolated": row["isolated"],
                    "local_word": row["local_word"],
                }
            )
    for k in _even_roots(max_root):
        row = even_isolated_seam(k)
        expected_width = 2 * row["state"] + 1
        even_width_ok = even_width_ok and row["even_width"] == expected_width
        if k <= 16 or row["odd_parents"]:
            even_rows.append(
                {
                    "k": k,
                    "state": row["state"],
                    "n_odd_parents": len(row["odd_parents"]),
                    "odd_parents": row["odd_parents"],
                    "even_width": row["even_width"],
                    "exact": row["exact"],
                    "isolated": row["isolated"],
                    "local_word": row["local_word"],
                }
            )
    n_odd = len(_odd_roots(max_root))
    n_even = len(_even_roots(max_root))
    all_exact = all(odd_isolated_seam(s)["exact"] for s in _odd_roots(max_root))
    all_exact = all_exact and all(even_isolated_seam(k)["exact"] for k in _even_roots(max_root))
    all_star_oo = all(odd_isolated_seam(s)["local_word"] == "*OO" for s in _odd_roots(max_root))
    all_star_ee = all(even_isolated_seam(k)["local_word"] == "*EE" for k in _even_roots(max_root))
    return {
        "max_root": max_root,
        "n_odd_isolated": n_odd,
        "n_even_isolated": n_even,
        "odd_parent_multi": odd_multi,
        "odd_parent_occupied": odd_occupied,
        "odd_parent_unique": odd_multi == 0,
        "even_width_is_cell": even_width_ok,
        "all_exact": all_exact,
        "all_odd_star_oo": all_star_oo,
        "all_even_star_ee": all_star_ee,
        "odd_samples": odd_rows,
        "even_samples": even_rows,
    }


def cyclemin_square_algebra(*, max_s: int = PARENT_MAX) -> dict[str, Any]:
    """CycleMin n = s^2 adds d_0 = 0; OO launch and last-even cell stay the same."""

    rows = []
    oo_suffix_ok = True
    last_even_is_cell = True
    first_even_scale = True
    for s in _odd_roots(max_s):
        n = s * s
        image = s * s * s
        t2 = floor_power(image)
        next_sq = (n + 1) * (n + 1)
        oo_ok = t2 >= next_sq
        oo_suffix_ok = oo_suffix_ok and oo_ok
        last_lo, last_hi = even_preimage(n)
        last_even_is_cell = last_even_is_cell and last_lo == n * n and last_hi == next_sq
        first_even_scale = first_even_scale and last_lo == n * n
        if s <= 15 or not oo_ok:
            rows.append(
                {
                    "s": s,
                    "n": n,
                    "T": image,
                    "T2": t2,
                    "next_square": next_sq,
                    "oo_suffix": oo_ok,
                    "last_even_cell": [last_lo, last_hi],
                }
            )
    return {
        "oo_suffix_holds": oo_suffix_ok,
        "last_even_is_standard_cell": last_even_is_cell,
        "first_even_ge_n2": first_even_scale,
        "extra_beyond_d0": not (oo_suffix_ok and last_even_is_cell and first_even_scale),
        "samples": rows,
    }


def finance_saving() -> dict[str, Any]:
    """One vanishing crumb vs leftover scale. States on a cycle exceed N0."""

    s0 = isqrt(N0) + 1
    if s0 % 2 == 0:
        s0 += 1
    while is_square(s0):
        s0 += 2
    k0 = isqrt(N0) + 1
    if k0 % 2 == 1:
        k0 += 1
    while is_square(k0):
        k0 += 2
    odd_save = EPS_CONST / float(s0**3)
    even_save = EPS_CONST / float(k0)
    even_save_cyclemin = EPS_CONST / float(N0)
    return {
        "N0": N0,
        "s0": s0,
        "k0": k0,
        "odd_save": odd_save,
        "even_save": even_save,
        "even_save_if_cyclemin_bound": even_save_cyclemin,
        "rel_L_leftover": 1.0 / LEFTOVER_L,
        "rel_L_blocker": 1.0 / BLOCKER_L,
        "leftover_mover": odd_save > 1e-6 or even_save_cyclemin > 1e-6,
    }


def _words_upto(max_len: int) -> list[str]:
    words = []
    for length in range(1, max_len + 1):
        for mask in range(1 << length):
            word = "".join("O" if (mask >> i) & 1 else "E" for i in range(length))
            words.append(word)
    return words


def short_closure(*, max_root: int = SHORT_ROOT_MAX, max_len: int = SHORT_LEN) -> dict[str, Any]:
    """|W+/-| <= 3 through an isolated square is a short cycle, already killed."""

    words = _words_upto(max_len)
    odd_hits = []
    even_hits = []
    for s in _odd_roots(max_root):
        state = s * s
        image = s * s * s
        for w_plus in words:
            if not follows_itinerary(image, w_plus):
                continue
            y = image_after(image, w_plus)
            for w_minus in words:
                if not follows_itinerary(y, w_minus):
                    continue
                if image_after(y, w_minus) == state:
                    odd_hits.append(
                        {
                            "s": s,
                            "w_plus": w_plus,
                            "w_minus": w_minus,
                            "y": y,
                            "period": 1 + len(w_plus) + len(w_minus),
                        }
                    )
    for k in _even_roots(max_root):
        state = k * k
        image = k
        for w_plus in words:
            if not follows_itinerary(image, w_plus):
                continue
            y = image_after(image, w_plus)
            for w_minus in words:
                if not follows_itinerary(y, w_minus):
                    continue
                if image_after(y, w_minus) == state:
                    even_hits.append(
                        {
                            "k": k,
                            "w_plus": w_plus,
                            "w_minus": w_minus,
                            "y": y,
                            "period": 1 + len(w_plus) + len(w_minus),
                        }
                    )
    return {
        "max_root": max_root,
        "max_len": max_len,
        "n_odd_hits": len(odd_hits),
        "n_even_hits": len(even_hits),
        "no_short_cycle": not odd_hits and not even_hits,
        "odd_hits": odd_hits[:10],
        "even_hits": even_hits[:10],
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    return {
        **{name: has_named(text, name) for name in EXISTING_LEAN},
        "sorry_free": "sorry" not in text and "admit" not in text,
        "new_lean_file": any(path.exists() for path in NEW_LEAN_FILES),
        **{f"has_{name}": has_named(text, name) for name in FORBIDDEN_THEOREMS},
    }


def anti_overclaim() -> dict[str, Any]:
    return {
        "halt_theorem": False,
        "paper_a_modified": False,
        "n0_raised": False,
        "atlas_recensus": False,
        "exact_floor_impact_reopened": False,
        "cyclic_seam_reopened": False,
        "leftover_killer": False,
        "dk_tightened": False,
        "new_lean_file": False,
        "global_termination": dict(ANTI_OVERCLAIM)["global_termination"],
    }


def classify(summary: dict[str, Any]) -> str:
    parents = summary["parents"]
    cyc = summary["cyclemin_square"]
    fin = summary["finance"]
    short = summary["short_closure"]
    lean = summary["lean"]
    word_ok = parents["all_odd_star_oo"] and parents["all_even_star_ee"]
    cell_ok = parents["odd_parent_unique"] and parents["even_width_is_cell"] and parents["all_exact"]
    cyc_ok = not cyc["extra_beyond_d0"]
    fin_ok = not fin["leftover_mover"]
    short_ok = short["no_short_cycle"]
    lean_ok = lean["odd_preimage_unique"] and lean["even_preimage_iff"] and not lean["new_lean_file"]
    if word_ok and cell_ok and cyc_ok and fin_ok and short_ok and lean_ok:
        return CLASS_REPARAM
    return CLASS_NEW


def build_summary() -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_square_seam",
        "anti_overclaim": anti_overclaim(),
        "fixtures": {
            "nine": fixture_nine(),
            "thirty_six": fixture_thirty_six(),
            "one_hundred": fixture_one_hundred(),
        },
        "parents": parent_census(),
        "cyclemin_square": cyclemin_square_algebra(),
        "finance": finance_saving(),
        "short_closure": short_closure(),
        "lean": lean_api_present(),
    }
    summary["classification"] = classify(summary)
    return summary


def write_research_note(summary: dict[str, Any]) -> None:
    p = summary["parents"]
    c = summary["cyclemin_square"]
    f = summary["finance"]
    s = summary["short_closure"]
    lines = [
        "# Juggler square-seam cycle lemma",
        "",
        "Phase-0 structural check: isolated odd seam s^2 -> s^3 and",
        "isolated even seam k^2 -> k as junctions on a hypothetical cycle.",
        "",
        f"Classification **{summary['classification']}**.",
        "",
        "## Local identities",
        "",
        "- 9 -> 27: odd isolated, crumb 0, local word `*OO`.",
        "- 36 -> 6: even isolated, crumb 0, local word `*EE`.",
        "- 100 -> 10: even isolated, then 10 -> 3 (inexact E).",
        f"- Isolated roots s,k <= {p['max_root']}: exact `{p['all_exact']}`,",
        f"  all odd `*OO` `{p['all_odd_star_oo']}`, all even `*EE` `{p['all_even_star_ee']}`.",
        "",
        "## Entrance cells",
        "",
        f"- Odd-parent uniqueness: `{p['odd_parent_unique']}` (occupied `{p['odd_parent_occupied']}` of `{p['n_odd_isolated']}`).",
        f"- Even width is 2q+1: `{p['even_width_is_cell']}`.",
        "",
        "## CycleMin = odd square",
        "",
        f"- OO suffix T^2(n) >= (n+1)^2: `{c['oo_suffix_holds']}`.",
        f"- Last even is the standard cell [n^2, (n+1)^2): `{c['last_even_is_standard_cell']}`.",
        f"- Extra beyond d_0 = 0: `{c['extra_beyond_d0']}`.",
        "",
        "## Finance saving (cycle states > N0)",
        "",
        f"- Odd save at s0={f['s0']}: `{f['odd_save']:.3e}`.",
        f"- Even save at CycleMin bound: `{f['even_save_if_cyclemin_bound']:.3e}`.",
        f"- 1/L leftover {LEFTOVER_L}: `{f['rel_L_leftover']:.3e}`; blocker: `{f['rel_L_blocker']:.3e}`.",
        f"- Leftover mover: `{f['leftover_mover']}`.",
        "",
        "## Short W+/- closure",
        "",
        f"- Roots <= {s['max_root']}, |W+/-| <= {s['max_len']}: odd hits `{s['n_odd_hits']}`, even hits `{s['n_even_hits']}`.",
        f"- No short cycle through an isolated square: `{s['no_short_cycle']}`.",
        "",
    ]
    DOC_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    write_research_note(summary)
    print(summary["classification"])
    p = summary["parents"]
    print("exact", p["all_exact"], "star_oo", p["all_odd_star_oo"], "star_ee", p["all_even_star_ee"])
    print("odd_unique", p["odd_parent_unique"], "even_width", p["even_width_is_cell"])
    print("cyclemin extra", summary["cyclemin_square"]["extra_beyond_d0"])
    print("finance mover", summary["finance"]["leftover_mover"], "odd_save", summary["finance"]["odd_save"])
    print("short", summary["short_closure"]["no_short_cycle"])
    return summary


if __name__ == "__main__":
    main()
