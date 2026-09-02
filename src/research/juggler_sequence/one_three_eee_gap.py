"""+1-chain gap: the five (1,3) leftovers sit above the EEE cell.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not a twenty-three-word scan.

The five first-expanding short-gap words with even-run signature (1,3)
are O^{a} E O^{7-a} EEE for a = 6,5,4,3,2. A cycle is the prefix
image in [n^8, (n+1)^8). Exact mixed +1-chains reduce to the family
identity 3^7 > 2^{11}. Leftover 4-fudge N0 values are 10^9 to 10^12
and are not used.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_e_e4 import word_e4
from research.juggler_sequence.four_even_short_gap import tail_holds_log
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_one_three_eee_gap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_one_three_eee_gap.md"

CLASS_PROVED = "ONE_THREE_EEE_GAP_PROVED"
CLASS_REFUTED = "ONE_THREE_EEE_GAP_REFUTED"
CLASS_INCOMPLETE = "ONE_THREE_EEE_GAP_INCOMPLETE"

FAMILY_ODDS = 7
FAMILY_EVENS = 4
SURPLUS = 3**FAMILY_ODDS
CELL_BITS = 2 ** (FAMILY_ODDS + FAMILY_EVENS)
SLACK = SURPLUS - CELL_BITS  # 2187 - 2048 = 139
PIN_MAX = 10_000

LEAN_THEOREMS = (
    "cycle_trailing_evens_lt",
    "odd_preimage_unique",
    "o7_image_ge_succ_pow16",
    "no_cycle_itinerary_oooooooeeee",
    "no_cycle_itinerary_even_count_le_three",
    "no_cycle_itinerary_ooooooeoeee",
    "no_cycleMin_ooooooeoeee",
    "no_cycleMin_oooooeooeee",
    "no_cycleMin_ooooeoooeee",
    "no_cycleMin_oooeooooeee",
    "no_cycleMin_ooeoooooeee",
    "no_cycleMin_one_three_eee",
)

FORBIDDEN_CORE = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "juggler_reaches_one",
)


@dataclass(frozen=True)
class FamilyMember:
    a0: int
    a1: int
    first: int
    leftover_n0: int
    v_lb: int
    pin_count: int
    min_ratio_floor: float
    min_n: int


# v_lb is a convenient integer with n^{L} > (n+1)^{P} v_lb^{2^{a0+1}}
# at the first prefix start, hence v = isqrt(T^{a0}) >= v_lb.
FAMILY: tuple[FamilyMember, ...] = (
    FamilyMember(6, 1, 163, 1_568_526_333, 10**12, 46, 15.13, 163),
    FamilyMember(5, 2, 241, 4_086_043_903, 10**9, 48, 19.00, 241),
    FamilyMember(4, 3, 37, 17_179_869_199, 8_000, 47, 5.72, 37),
    FamilyMember(3, 4, 113, 148_113_652_199, 2_000, 32, 12.10, 113),
    FamilyMember(2, 5, 173, 3_749_366_963_330, 200, 36, 15.50, 173),
)

FORBIDDEN_THEOREMS = FORBIDDEN_CORE + tuple(
    f"no_cycle_itinerary_{word_e4(member.a0, member.a1, 0, 0).lower()}"
    for member in FAMILY
    if (member.a0, member.a1) != (6, 1)
)


def itinerary(a0: int, a1: int) -> str:
    return word_e4(a0, a1, 0, 0)


def prefix(a0: int, a1: int) -> str:
    return "O" * a0 + "E" + "O" * a1


def left_plus(odds: int) -> tuple[int, int, int]:
    left = 3 ** (odds + 1) - 3 * (2**odds)
    plus = left - 3**odds
    return left, plus, 2**odds


def fudge_exp(a0: int, a1: int) -> int:
    return (2 ** (a0 + 1)) * 3 * (3**a1 - 2**a1)


def follows_itinerary(n: int, letters: str) -> int | None:
    x = n
    for letter in letters:
        if letter == "O" and x % 2 == 0:
            return None
        if letter == "E" and x % 2 == 1:
            return None
        x = isqrt(x) if letter == "E" else isqrt(x * x * x)
    return x


def eee_cell_hi(n: int) -> int:
    return (n + 1) ** 8


def leading_beats_v(n: int, a0: int, v_lb: int) -> bool:
    if n < 2 or v_lb < 1:
        return False
    left, plus, _tail = left_plus(a0)
    return n**left > (n + 1) ** plus * v_lb ** (2 ** (a0 + 1))


def master_beats(n: int, v_lb: int, fudge: int) -> bool:
    if n < 2 or v_lb < 1 or fudge < 0:
        return False
    return n**SURPLUS * v_lb**fudge > (n + 1) ** CELL_BITS * (v_lb + 1) ** fudge


def leftover_n0_certified(a0: int, a1: int, n0: int) -> bool:
    return n0 >= 3 and (not tail_holds_log(n0 - 1, a0, a1, 0, 0)) and tail_holds_log(
        n0, a0, a1, 0, 0
    )


def first_prefix_start(a0: int, a1: int, cap: int = 300) -> int | None:
    letters = prefix(a0, a1)
    n = 3
    while n < cap:
        if follows_itinerary(n, letters) is not None:
            return n
        n += 2
    return None


def pin_member(member: FamilyMember, n_hi: int = PIN_MAX) -> dict[str, Any]:
    letters = prefix(member.a0, member.a1)
    first = None
    count = 0
    above = 0
    misses: list[int] = []
    min_ratio = None
    min_n = None
    n = 3
    while n < n_hi:
        z = follows_itinerary(n, letters)
        if z is not None:
            count += 1
            if first is None:
                first = n
            hi = eee_cell_hi(n)
            if z >= hi:
                above += 1
            else:
                misses.append(n)
            ratio = z / hi
            if min_ratio is None or ratio < min_ratio:
                min_ratio = ratio
                min_n = n
        n += 2
    return {
        "a0": member.a0,
        "a1": member.a1,
        "word": itinerary(member.a0, member.a1),
        "prefix": letters,
        "n_hi": n_hi,
        "first": first,
        "count": count,
        "above_cell": above,
        "misses": misses,
        "min_ratio": min_ratio,
        "min_n": min_n,
        "leftover_n0": member.leftover_n0,
        "v_lb": member.v_lb,
        "fudge_exp": fudge_exp(member.a0, member.a1),
        "left_plus": list(left_plus(member.a0)),
    }


def pin_family(n_hi: int = PIN_MAX) -> list[dict[str, Any]]:
    return [pin_member(member, n_hi) for member in FAMILY]


def elementary_comparisons() -> dict[str, bool]:
    checks: dict[str, bool] = {
        "three7_gt_two11": SURPLUS > CELL_BITS,
        "slack139": SLACK == 139,
        "five_words": len(FAMILY) == 5,
        "a0_plus_a1": all(m.a0 + m.a1 == FAMILY_ODDS for m in FAMILY),
        "words_are_eee": all(itinerary(m.a0, m.a1).endswith("EEE") for m in FAMILY),
        "o6_left": left_plus(6) == (1995, 1266, 64),
        "o2_left": left_plus(2) == (15, 6, 4),
        "fudge_61": fudge_exp(6, 1) == 384,
        "fudge_25": fudge_exp(2, 5) == 5064,
        "o6_coroll_k": 12 * 163 >= 3 * 164,
        "isqrt164": isqrt(164) == 12,
        "first_starts": all(
            first_prefix_start(m.a0, m.a1) == m.first for m in FAMILY
        ),
        "leftover_n0": all(
            leftover_n0_certified(m.a0, m.a1, m.leftover_n0) for m in FAMILY
        ),
    }
    for member in FAMILY:
        key = f"{member.a0}_{member.a1}"
        checks[f"lead_{key}"] = leading_beats_v(member.first, member.a0, member.v_lb)
        checks[f"master_{key}"] = master_beats(
            member.first, member.v_lb, fudge_exp(member.a0, member.a1)
        )
        checks[f"no_leftover_at_first_{key}"] = not tail_holds_log(
            member.first, member.a0, member.a1, 0, 0
        )
    return checks


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    paper_l = paper.lower()
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_family": all(
            itinerary(m.a0, m.a1).lower() not in paper_l for m in FAMILY
        ),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "one_three_eee" not in engine_floor_text(),
        "no_nonunique_family_cycle_itinerary": all(
            f"theorem no_cycle_itinerary_{itinerary(m.a0, m.a1).lower()}" not in combined
            for m in FAMILY
            if (m.a0, m.a1) != (6, 1)
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    pins = scan["pin"]
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_trailing_evens_lt"]
        and lean["no_cycle_itinerary_oooooooeeee"]
        and lean["no_cycle_itinerary_even_count_le_three"]
        and lean["no_cycle_itinerary_ooooooeoeee"]
        and lean["no_cycleMin_one_three_eee"]
        and lean["no_nonunique_family_cycle_itinerary"]
        and lean["no_cycle_itinerary_length_eleven"]
        and lean["paper_a_has_no_family"]
    )
    if not lean_ok or not all(elem.values()):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean or arithmetic incomplete lean_ok={lean_ok}",
        }
    for row, member in zip(pins, FAMILY, strict=True):
        if row["misses"]:
            return {
                "classification": CLASS_REFUTED,
                "reason": f"{row['word']} prefix below EEE cell at {row['misses'][:6]}",
            }
        if row["first"] != member.first:
            return {
                "classification": CLASS_INCOMPLETE,
                "reason": f"{row['word']} first start {row['first']} vs {member.first}",
            }
        if row["count"] != member.pin_count or row["min_n"] != member.min_n:
            return {
                "classification": CLASS_INCOMPLETE,
                "reason": f"{row['word']} pin drift count={row['count']} min_n={row['min_n']}",
            }
        if row["min_ratio"] is None or row["min_ratio"] < member.min_ratio_floor:
            return {
                "classification": CLASS_INCOMPLETE,
                "reason": f"{row['word']} min ratio {row['min_ratio']}",
            }
    closest = min(pins, key=lambda row: row["min_ratio"])
    return {
        "classification": CLASS_PROVED,
        "reason": (
            f"five (1,3) words O^a E O^{{7-a}} EEE; family identity "
            f"3^7={SURPLUS} > 2^{{11}}={CELL_BITS} with slack {SLACK}; "
            f"exact mixed +1-chain n^{SURPLUS} < (n+1)^{CELL_BITS} "
            f"(1+1/v)^E contradicts the leading-chain lower bound on v "
            f"at each first prefix start; leftover N0 unused "
            f"(1.57e9 to 3.75e12); pin n<{PIN_MAX} empty, closest ratio "
            f"{closest['min_ratio']} at n={closest['min_n']} on {closest['word']}"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "family_odds": FAMILY_ODDS,
        "family_evens": FAMILY_EVENS,
        "surplus": SURPLUS,
        "cell_bits": CELL_BITS,
        "slack": SLACK,
        "words": [itinerary(m.a0, m.a1) for m in FAMILY],
        "elementary": elementary_comparisons(),
        "pin": pin_family(),
        "length_eleven_census": False,
        "z5_cell": False,
        "twenty_three_word_scan": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["twenty_three_word_scan"] = False
    return {
        "experiment": "juggler_one_three_eee_gap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact mixed +1-chain on O^a E O^{7-a} versus the EEE "
            "cell z < (n+1)^8; family identity 3^7 > 2^{11}; leftover "
            "N0 unused; CycleMinFudge Lean; no (2,2) scan"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    elem = scan["elementary"]
    lines = [
        "# Juggler (1,3) EEE +1-chain gap",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The five first-expanding (1,3)",
        "leftovers are O^a E O^{7-a} EEE. Each prefix image sits at or",
        "above the EEE inverse cell of n, so none is a cycle word.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do all five (1,3) leftovers die by",
        "                        prefix image versus (n+1)^8?",
        "Novelty hypothesis      the same exact +1-chain that killed",
        "                        O^7 EEEE / O^6 EEEOE, now mixed",
        "                        through one internal E, fires at",
        "                        the first prefix start, not leftover N0",
        "Falsifier               a prefix image inside the EEE cell,",
        "                        or the chain only at leftover-scale N0",
        "Existing machinery      O^6 / O^7 +1-chain; cycle_trailing_evens",
        "                        r=3; leftover Z4 PARK",
        "Maximum Phase-0 scope   five named (1,3) words; CycleMin",
        "                        Lean; no (2,2) family, no 23-word scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- words: `{scan['words']}`",
        f"- family slack: `3^{scan['family_odds']} - 2^{11} = {scan['slack']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Arithmetic",
        "",
        f"- surplus `3^7 = {scan['surplus']}` versus cell bits `2^{11} = {scan['cell_bits']}`",
        f"- elementary checks: `{elem}`",
        "",
        "## Pin",
        "",
    ]
    for row in scan["pin"]:
        lines.append(
            f"- `{row['word']}` n<{row['n_hi']}: first=`{row['first']}` "
            f"count=`{row['count']}` above=`{row['above_cell']}` "
            f"misses=`{row['misses']}` min_ratio=`{row['min_ratio']}` "
            f"at n=`{row['min_n']}` leftover_N0=`{row['leftover_n0']}` "
            f"v_lb=`{row['v_lb']}` fudge=`{row['fudge_exp']}`"
        )
    lines.extend(
        [
            "",
            "## Proof",
            "",
            "A cycle word O^a E O^{7-a} EEE is the prefix image z in",
            "[n^8, (n+1)^8) by cycle_trailing_evens r=3. Write",
            "u = T^a(n) and v = isqrt(u), and assume z < (n+1)^8.",
            "",
            "On the leading O^a run the exact cells x_k^3 < (x_{k+1}+1)^2",
            "with x_k >= n compose to",
            "",
            "    n^{3^{a+1}-3·2^a} < (n+1)^{2·3^a-3·2^a} (u+1)^{2^a}.",
            "",
            "The even step is u < (v+1)^2, so u+1 <= (v+1)^2. On the",
            "suffix O^{7-a} from v one has x_k >= v and the same",
            "+1-chain, hence",
            "",
            "    v^{L'} < (v+1)^{P'} (z+1)^{2^{7-a}} <= (v+1)^{P'} (n+1)^{2^{10-a}}.",
            "",
            "Eliminating v produces the family comparison",
            "",
            f"    n^{SURPLUS} < (n+1)^{CELL_BITS} (1+1/v)^E,",
            "",
            "where E = 2^{a+1}·3·(3^{7-a}-2^{7-a}). This is 3^7 versus",
            "2^{11} with a (1+1/v) fudge. A convenient lower bound V",
            "on v comes from the leading chain at the first prefix",
            "start: n^L > (n+1)^P V^{2^{a+1}} forces u+1 > V^2, so",
            "v >= V. That bound is monotone in n. Integer checks at",
            "the five first starts (37, 113, 163, 173, 241) give",
            "",
            f"    n^{SURPLUS} V^E > (n+1)^{CELL_BITS} (V+1)^E.",
            "",
            "Contradiction. No smaller odd n follows the corresponding",
            "prefix (pin). Leftover 4-fudge cells first fire at",
            "1.57e9 through 3.75e12 and are not used.",
            "",
            "Independently, OOOOOOEOEEE is a corollary of the O^6",
            "+1-chain T^6(n) >= (n+1)^{11}: v >= (n+1)^5 isqrt(n+1),",
            "and isqrt(n+1)*(n) >= 3(n+1) at n=163 already forces",
            "isqrt(v^3) >= (n+1)^8.",
            "",
            "This is not a length-11 census. The (2,2) and isolated-E",
            "signatures are a separate job.",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    for name in FORBIDDEN_THEOREMS:
        lines.append(f"- no `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no non-unique family CycleItinerary: `{lean.get('no_nonunique_family_cycle_itinerary')}`",
            f"- Paper A has no family word: `{lean.get('paper_a_has_no_family')}`",
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
            "This is not a halt result and not a length-11 census.",
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


if __name__ == "__main__":
    main()
