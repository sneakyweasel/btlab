"""Christoffel / mechanical words on leftover Juggler cycle lengths.

Not a halt theorem, not a leftover-word census, not a floor raise,
not Lebel modular sieving, and not a reopen of the closed
almost-monochrome near-tight branch.

Fernández–Ibáñez use Christoffel words as unique maximizers of a
Collatz Terras / affine functional. Juggler has no affine equation.
The transferable slogan is combinatorial: a cycle at leftover
near-convergent L (worst finance o = o_min(L)) is close to the
Christoffel word of slope o/L, so leftover-word cells apply to a
one-parameter necklace instead of C(L, o) words.

This probe defines the Juggler ceiling-Christoffel word, identifies
leftover L with Beatty / continued-fraction approximations of
log 2 / log 3, and measures cyclic Hamming distance of leftover-word
and CycleMin-legal candidates to that necklace. Lebel modular
sieving is not implemented.

Dossier: docs/problems/juggler_cycle_christoffel.md.
"""

from __future__ import annotations

import json
import math
import subprocess
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_gap_baker import o_min
from research.juggler_sequence.first_e_e4 import (
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.lean_paths import (
    CYCLE_FINANCE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_christoffel.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_christoffel.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_christoffel"

CLASS_CLOSED = "CYCLE_CHRISTOFFEL_CLOSED"
CLASS_GREEN = "CYCLE_CHRISTOFFEL_GREEN"
CLASS_PARK = "CYCLE_CHRISTOFFEL_PARK"
CLASS_INCOMPLETE = "CYCLE_CHRISTOFFEL_INCOMPLETE"

# Killed near-convergents used for leftover-word / CycleMin censuses,
# then the live leftover records the user named.
CENSUS_LENGTHS = (11, 19)
LEFTOVER_RECORDS = (38, 84, 569, 1054)
ALL_PROBE_LENGTHS = (11, 19, 38, 84, 569, 1054)

# Farey / continued-fraction identification of o_min / L.
# Principal convergents of log 2 / log 3 include 12/19, 53/84, 665/1054.
# 7/11 = 2/3 ⊕ 5/8 and 359/569 = 53/84 ⊕ 306/485 are intermediates.
# 24/38 is the double of 12/19.
IDENTIFICATIONS: dict[int, dict[str, Any]] = {
    11: {"kind": "intermediate", "ratio": (7, 11), "parents": ((2, 3), (5, 8))},
    19: {"kind": "principal", "ratio": (12, 19)},
    38: {
        "kind": "double",
        "ratio": (24, 38),
        "reduced": (12, 19),
        "base": 19,
    },
    84: {"kind": "principal", "ratio": (53, 84)},
    569: {
        "kind": "intermediate",
        "ratio": (359, 569),
        "parents": ((53, 84), (306, 485)),
    },
    1054: {"kind": "principal", "ratio": (665, 1054)},
}

EXISTING_LEAN = (
    "cycleMin_finance",
    "no_cycle_itinerary_length_le_nineteen",
    "cycle_itinerary_length_thirty_eight_or_ge_thirty_nine",
    "power_bound_eq_implies_monochrome",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "no_cycle_itinerary_christoffel",
    "cycle_near_christoffel",
    "christoffel_excludes_length",
)
FORBIDDEN_NEW_API = (
    "CycleChristoffel",
    "MechanicalWord",
    "ChristoffelCycle",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleChristoffel.lean",
    JUGGLER_DIR / "MechanicalWord.lean",
    JUGGLER_DIR / "Christoffel.lean",
)
PAPER_FORBIDDEN = ("CycleChristoffel", "MechanicalWord", "ChristoffelCycle")

WORD_PREFIX = 80


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


def christoffel_bits(length: int, odd: int) -> tuple[int, ...]:
    """Ceiling Christoffel / mechanical word of slope odd/length.

    Same formula as the Fernández–Ibáñez / Collatz adapter
    ``research.collatz.cycle_divisibility.christoffel_binary``.
    """

    if length < 1:
        raise ValueError("length must be positive")
    if odd < 0 or odd > length:
        raise ValueError("odd count must lie in [0, length]")
    return tuple(
        math.ceil(index * odd / length) - math.ceil((index - 1) * odd / length)
        for index in range(1, length + 1)
    )


def bits_to_word(bits: tuple[int, ...]) -> str:
    return "".join("O" if bit else "E" for bit in bits)


def christoffel_word(length: int, odd: int | None = None) -> str:
    """Juggler O/E Christoffel word of slope o_min(L)/L, or a supplied o."""

    odd_count = o_min(length) if odd is None else odd
    return bits_to_word(christoffel_bits(length, odd_count))


def cyclic_hamming(left: str, right: str) -> int:
    """Minimum Hamming distance over cyclic rotations of ``right``."""

    if len(left) != len(right):
        raise ValueError("cyclic Hamming requires equal lengths")
    n = len(left)
    best = n
    doubled = right + right
    for shift in range(n):
        dist = sum(a != b for a, b in zip(left, doubled[shift : shift + n]))
        if dist < best:
            best = dist
    return best


def cyclemin_rotations(word: str) -> list[str]:
    """Rotations that start at a local minimum: start O, end E."""

    n = len(word)
    doubled = word + word
    return [
        doubled[i : i + n]
        for i in range(n)
        if doubled[i] == "O" and doubled[i + n - 1] == "E"
    ]


def is_balanced_oe(word: str) -> bool:
    """Classical finite balance: equal-length factors differ by at most 1."""

    n = len(word)
    doubled = word + word
    for length in range(1, n + 1):
        starts = n if length < n else 1
        counts = [doubled[start : start + length].count("O") for start in range(starts)]
        if counts and max(counts) - min(counts) > 1:
            return False
    return True


def max_run(word: str, letter: str) -> int:
    best = current = 0
    for char in word + word:
        if char == letter:
            current += 1
            if current > best:
                best = current
        else:
            current = 0
    return min(best, len(word))


def block_signature(word: str) -> list[tuple[int, int]]:
    """Cyclic O^k E^l blocks in a CycleMin orientation."""

    oriented = cyclemin_rotations(word)
    text = oriented[0] if oriented else word
    blocks: list[tuple[int, int]] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] != "O":
            i += 1
            continue
        odd = 0
        while i + odd < n and text[i + odd] == "O":
            odd += 1
        even = 0
        while i + odd + even < n and text[i + odd + even] == "E":
            even += 1
        blocks.append((odd, even))
        i += odd + even
    return blocks


def farey_neighbor(left: tuple[int, int], right: tuple[int, int]) -> bool:
    return abs(left[0] * right[1] - left[1] * right[0]) == 1


def farey_sum(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return (left[0] + right[0], left[1] + right[1])


def identification_holds(length: int) -> bool:
    spec = IDENTIFICATIONS[length]
    odd = o_min(length)
    ratio = tuple(spec["ratio"])
    if (odd, length) != ratio:
        return False
    kind = spec["kind"]
    if kind == "principal":
        return True
    if kind == "double":
        reduced = tuple(spec["reduced"])
        return (odd // 2, length // 2) == reduced and length == 2 * spec["base"]
    if kind == "intermediate":
        parents = spec["parents"]
        return farey_neighbor(*parents) and farey_sum(*parents) == ratio
    return False


def christoffel_row(length: int) -> dict[str, Any]:
    odd = o_min(length)
    word = christoffel_word(length, odd)
    oriented = cyclemin_rotations(word)
    start = oriented[0] if oriented else word
    blocks = block_signature(start)
    spec = IDENTIFICATIONS[length]
    return {
        "L": length,
        "o": odd,
        "even": length - odd,
        "word": word if length <= 84 else None,
        "word_prefix": start[:WORD_PREFIX],
        "cyclemin_start": start if length <= 84 else None,
        "necklace": len(set(oriented)),
        "balanced": is_balanced_oe(word),
        "max_odd_run": max_run(word, "O"),
        "max_even_run": max_run(word, "E"),
        "m_blocks": len(blocks),
        "identification": spec["kind"],
        "identification_ok": identification_holds(length),
        "is_square_of_nineteen": (
            length == 38 and word == christoffel_word(19) * 2
        ),
    }


def iter_cyclemin_weight_words(length: int, odd: int):
    """CycleMin orientations of weight ``odd``: start O, end E."""

    if odd < 1 or length - odd < 1:
        return
    need = odd - 1
    middle = length - 2
    if need < 0 or need > middle:
        return
    for combo in combinations(range(middle), need):
        letters = ["E"] * middle
        for index in combo:
            letters[index] = "O"
        yield "O" + "".join(letters) + "E"


def histogram_from_distances(distances: list[int]) -> dict[str, int]:
    return {str(key): value for key, value in sorted(Counter(distances).items())}


def census_stats(distances: list[int]) -> dict[str, Any]:
    if not distances:
        return {
            "count": 0,
            "histogram": {},
            "radius_0": 0,
            "radius_le_2": 0,
            "median": None,
            "mean": None,
            "max": None,
        }
    ordered = sorted(distances)
    mid = ordered[len(ordered) // 2]
    return {
        "count": len(distances),
        "histogram": histogram_from_distances(distances),
        "radius_0": sum(1 for dist in distances if dist == 0),
        "radius_le_2": sum(1 for dist in distances if dist <= 2),
        "median": mid,
        "mean": sum(distances) / len(distances),
        "max": ordered[-1],
    }


def leftover11_distances() -> dict[str, Any]:
    """The thirty first-expanding short-gap leftovers versus Christoffel 7/11."""

    target = christoffel_word(11, 7)
    rows = []
    for shape in remainder_shapes():
        a0 = first_expanding_a0(shape["a1"], shape["a2"], shape["a3"])
        word = word_e4(a0, shape["a1"], shape["a2"], shape["a3"])
        dist = cyclic_hamming(word, target) if len(word) == 11 else None
        rows.append(
            {
                "word": word,
                "length": len(word),
                "kind": shape["kind"],
                "distance": dist,
            }
        )
    length11 = [row["distance"] for row in rows if row["length"] == 11]
    stats = census_stats(length11)
    return {
        "christoffel": target,
        "family_size": len(rows),
        "length_11_count": len(length11),
        "contains_christoffel": any(row["distance"] == 0 for row in rows),
        **stats,
        "far_words": [
            row["word"]
            for row in rows
            if row["distance"] is not None and row["distance"] >= 4
        ],
    }


def cyclemin_census(length: int) -> dict[str, Any]:
    odd = o_min(length)
    target = christoffel_word(length, odd)
    distances: list[int] = []
    isolated: list[int] = []
    max_odd_two = 0
    for word in iter_cyclemin_weight_words(length, odd):
        dist = cyclic_hamming(word, target)
        distances.append(dist)
        if max_run(word, "E") == 1:
            isolated.append(dist)
        if max_run(word, "O") == 2:
            max_odd_two += 1
    stats = census_stats(distances)
    isolated_stats = census_stats(isolated)
    necklace = len(cyclemin_rotations(target))
    return {
        "L": length,
        "o": odd,
        "christoffel": target,
        "necklace": necklace,
        **stats,
        "isolated_even": isolated_stats,
        "max_odd_run_two": max_odd_two,
        "one_parameter": stats["radius_0"] == necklace
        and stats["count"] == necklace,
    }


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
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_christoffel_lean": not any(path.is_file() for path in FORBIDDEN_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe() -> dict[str, Any]:
    rows = [christoffel_row(length) for length in ALL_PROBE_LENGTHS]
    leftover11 = leftover11_distances()
    census11 = cyclemin_census(11)
    census19 = cyclemin_census(19)
    ident_ok = all(row["identification_ok"] for row in rows)
    square38 = next(row for row in rows if row["L"] == 38)["is_square_of_nineteen"]
    slogan_false = (
        leftover11["family_size"] > leftover11["radius_0"]
        and leftover11["max"] is not None
        and leftover11["max"] >= 4
        and census19["median"] is not None
        and census19["median"] >= 4
        and census19["isolated_even"]["count"] > census19["necklace"]
        and not census19["one_parameter"]
    )
    return {
        "rows": rows,
        "identifications_hold": ident_ok,
        "square_of_nineteen": square38,
        "leftover11": leftover11,
        "census11": census11,
        "census19": census19,
        "slogan_false": slogan_false,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "new_lean": False,
        "lebel_modular_sieving": False,
        "monochrome_reopened": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_finance_present"]
        and lean["no_christoffel_lean"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["halt_theorem"]
        or scan["no_cycle_all_lengths"]
        or scan["new_lean"]
        or scan["lebel_modular_sieving"]
        or scan["monochrome_reopened"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if not scan["identifications_hold"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a leftover length failed its Beatty / Farey identification",
        }
    leftover11 = scan["leftover11"]
    census19 = scan["census19"]
    if scan["slogan_false"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "leftover-word / CycleMin candidates are not a one-parameter "
                f"Christoffel necklace: the thirty L=11 leftovers include "
                f"Christoffel and {leftover11['max']} Hamming, family "
                f"{leftover11['family_size']} versus necklace "
                f"{scan['census11']['necklace']}; L=19 CycleMin weight-12 "
                f"has {census19['count']} words, median cyclic Hamming "
                f"{census19['median']}, radius 0 only {census19['radius_0']}; "
                f"the isolated-even worst-m family has "
                f"{census19['isolated_even']['count']} words. "
                "Finance is word-order-independent. Lebel sieving was not used. "
                "Cycle-only near-Christoffel rigidity is not claimed refuted"
            ),
        }
    if census19["one_parameter"] and leftover11["family_size"] == leftover11["radius_0"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "leftover-word / CycleMin candidates concentrate on the Christoffel necklace",
        }
    return {
        "classification": CLASS_PARK,
        "reason": "Christoffel identification holds but the one-parameter slogan is inconclusive",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "new_lean": False,
            "lebel_modular_sieving": False,
            "monochrome_reopened": False,
            "affine_equation": False,
            "leftover_word_census": False,
        }
    )
    return {
        "experiment": "juggler_cycle_christoffel",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "ceiling Christoffel O/E words at leftover L; Farey identification "
            "of o_min/L; cyclic Hamming of the thirty L=11 leftovers and all "
            "CycleMin weight-o_min words at L=11,19; isolated-even worst-m "
            "family at L=19; no Lebel walk"
        ),
    }


def _fmt_hist(histogram: dict[str, int]) -> str:
    return ", ".join(f"{key}:{value}" for key, value in histogram.items())


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    leftover11 = scan["leftover11"]
    census11 = scan["census11"]
    census19 = scan["census19"]
    lines = [
        "# Juggler cycle Christoffel maximizers",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Fernández–Ibáñez unique-maximizer combinatorics, without Lebel",
        "modular sieving and without the Collatz affine equation.",
        "Not a halt theorem. Not a leftover-word census. No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- identifications hold: `{scan['identifications_hold']}`",
        f"- L=38 is the square of L=19: `{scan['square_of_nineteen']}`",
        f"- slogan false: `{scan['slogan_false']}`",
        f"- L=11 leftover family: `{leftover11['family_size']}` "
        f"contains Christoffel `{leftover11['contains_christoffel']}` "
        f"histogram `{_fmt_hist(leftover11['histogram'])}`",
        f"- L=19 CycleMin count: `{census19['count']}` median Hamming "
        f"`{census19['median']}` radius 0 `{census19['radius_0']}` "
        f"radius <= 2 `{census19['radius_le_2']}`",
        f"- L=19 isolated-even family: `{census19['isolated_even']['count']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Christoffel words at leftover lengths",
        "",
    ]
    for row in scan["rows"]:
        word = row["cyclemin_start"] or row["word_prefix"]
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` even=`{row['even']}` "
            f"kind=`{row['identification']}` balanced=`{row['balanced']}` "
            f"maxO=`{row['max_odd_run']}` maxE=`{row['max_even_run']}` "
            f"m=`{row['m_blocks']}` necklace=`{row['necklace']}` "
            f"start=`{word}`"
        )
    lines.extend(
        [
            "",
            "## L=11 leftover-word cells versus Christoffel 7/11",
            "",
            f"- Christoffel: `{leftover11['christoffel']}`",
            f"- thirty first-expanding short-gap leftovers, all length 11",
            f"- cyclic Hamming histogram: `{_fmt_hist(leftover11['histogram'])}`",
            f"- contains the Christoffel word: `{leftover11['contains_christoffel']}`",
            f"- CycleMin weight-7 census: `{census11['count']}` "
            f"histogram `{_fmt_hist(census11['histogram'])}`",
            "",
            "## L=19 CycleMin weight-12 versus Christoffel 12/19",
            "",
            f"- Christoffel: `{census19['christoffel']}`",
            f"- CycleMin orientations: `{census19['count']}` "
            f"histogram `{_fmt_hist(census19['histogram'])}`",
            f"- median cyclic Hamming: `{census19['median']}`",
            f"- isolated-even (max E-run 1, worst m): "
            f"`{census19['isolated_even']['count']}` "
            f"histogram `{_fmt_hist(census19['isolated_even']['histogram'])}`",
            f"- words with max O-run 2: `{census19['max_odd_run_two']}`",
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
    (DATA_DIR / "rows.json").write_text(
        json.dumps(scan["rows"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "leftover11.json").write_text(
        json.dumps(scan["leftover11"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "census19.json").write_text(
        json.dumps(scan["census19"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "identifications_hold": scan["identifications_hold"],
        "square_of_nineteen": scan["square_of_nineteen"],
        "slogan_false": scan["slogan_false"],
        "leftover11_family": scan["leftover11"]["family_size"],
        "leftover11_max_distance": scan["leftover11"]["max"],
        "census19_count": scan["census19"]["count"],
        "census19_median": scan["census19"]["median"],
        "census19_radius_0": scan["census19"]["radius_0"],
        "isolated_even_19": scan["census19"]["isolated_even"]["count"],
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cycle Christoffel maximizers\n\n"
        "Ceiling Christoffel O/E words versus leftover-word / CycleMin "
        "candidates at near-convergent lengths.\n"
        "Not a halt theorem. No Lebel sieving. No new Lean.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_christoffel`.\n",
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
    payload = write_artifacts()
    decision = payload["decision"]
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"ident={scan['identifications_hold']} "
        f"square38={scan['square_of_nineteen']} "
        f"L11fam={scan['leftover11']['family_size']} "
        f"L19med={scan['census19']['median']} "
        f"slogan_false={scan['slogan_false']}"
    )


if __name__ == "__main__":
    main()
