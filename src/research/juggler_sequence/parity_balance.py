"""Shared AboveAnchor parity-balance language.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a new cell, not a CycleMin census, not an invented automaton.

Phase 0 asks whether already-proved shared exclusions force
2^{|w|} > 3^{oddCount(w)} on long surviving prefixes. All verdicts
are integer comparisons of 2^ell against 3^o.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.growth_balance import CONTROLS, prefix_table
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_balance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_balance.md"

CLASS_CLOSED = "PARITY_BALANCE_CLOSED"
CLASS_GREEN = "PARITY_BALANCE_GREEN"
CLASS_INCOMPLETE = "PARITY_BALANCE_INCOMPLETE"

N_OPT = 18
ISOLATED_A_MAX = 12
BLOCK_SAMPLES = (
    "O",
    "E",
    "OE",
    "OO",
    "OOE",
    "OOO",
    "OOEE",
    "OOOE",
    "OOOEE",
    "OOOOE",
    "OOOOEE",
    "OE" * 2,
)

EXISTING_LEAN = (
    "aboveAnchor_not_envelope_drop",
    "aboveAnchor_not_odd_even",
    "isolatedOddSurvival_bound",
    "isolatedOESurvives",
    "power_bound_word",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "ParityBalance",
    "SurvivalLanguage",
    "OddDensity",
    "EnvelopeBudget",
    "WordSurvivalBudget",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "ParityBalance.lean",
    JUGGLER_DIR / "SurvivalLanguage.lean",
    JUGGLER_DIR / "OddDensity.lean",
)

SHARED_PATTERNS = (
    "every prefix obeys 2^|u| <= 3^oddCount(u)",
    "initial OE: instance of the prefix envelope",
    "isolated O^a E (OE)^r: same exponents as the prefix envelope",
)

CYCLE_ONLY_PATTERNS = (
    "no_cycle_itinerary_* leftover cells",
    "even_count_le_three",
    "leftover_prefix_preimage",
    "small-cycle census",
)

TERMINATION_PATTERNS = (
    "aboveAnchor_of_minimalNonTerm",
    "minimal_ooeooe_forces_oo",
    "minimal_isolated_two",
)


def two_pow_le_three_pow(length: int, odd_count: int) -> bool:
    """Exact survival comparison 2^ell <= 3^o."""

    if length < 0 or odd_count < 0:
        raise ValueError("length and odd_count must be nonnegative")
    return (1 << length) <= 3**odd_count


def prefix_survives(word: str) -> bool:
    """Every prefix satisfies the shared envelope lower bound."""

    odd_count = 0
    for index, letter in enumerate(word, start=1):
        if letter == "O":
            odd_count += 1
        elif letter != "E":
            raise ValueError(f"non-letter {letter!r}")
        if not two_pow_le_three_pow(index, odd_count):
            return False
    return True


def isolated_exponents(a: int, r: int) -> tuple[int, int]:
    """Length and odd count of isolatedPrefix(a, r)."""

    if a < 0 or r < 0:
        raise ValueError("a and r must be nonnegative")
    return a + 1 + 2 * r, a + r


def isolated_equals_prefix_envelope(a: int, r: int) -> bool:
    """2^{a+2r+1} <= 3^{a+r} is the prefix envelope on that shape."""

    length, odd_count = isolated_exponents(a, r)
    return isolated_oe_exponent_ok(a, r) == two_pow_le_three_pow(length, odd_count)


def odd_count_of(word: str) -> int:
    return word.count("O")


def ratio_pair(word: str) -> dict[str, Any]:
    length = len(word)
    odds = odd_count_of(word)
    two_pow = 1 << length
    three_pow = 3**odds
    return {
        "word": word,
        "length": length,
        "odd_count": odds,
        "two_pow": two_pow,
        "three_pow": three_pow,
        "survives": two_pow <= three_pow,
        "prefix_survives": prefix_survives(word),
        "two_over_three": str(Fraction(two_pow, three_pow)),
    }


def o_star(length: int) -> str:
    return "O" * length


def o_then_e(length: int) -> str:
    if length <= 0:
        return ""
    if length == 1:
        return "O"
    return "O" * (length - 1) + "E"


def ooe_repeat(length: int) -> str:
    blocks, rem = divmod(length, 3)
    return "OOE" * blocks + "O" * rem


def optimize(length: int) -> dict[str, Any]:
    """Max and min odd count among prefix-surviving words of exact length."""

    if length < 0:
        raise ValueError("length must be nonnegative")
    if length == 0:
        return {
            "length": 0,
            "max_odd": 0,
            "min_odd": 0,
            "max_word": "",
            "min_word": "",
            "max_mixed_odd": None,
            "max_mixed_word": None,
        }

    # After k letters, reachable odd counts with one max-word and one min-word.
    reachable: dict[int, tuple[str, str]] = {0: ("", "")}
    for _ in range(length):
        nxt: dict[int, tuple[str, str]] = {}
        for odds, (max_word, min_word) in reachable.items():
            for letter, new_odds in (("O", odds + 1), ("E", odds)):
                if not two_pow_le_three_pow(len(max_word) + 1, new_odds):
                    continue
                cand_max = max_word + letter
                cand_min = min_word + letter
                if new_odds not in nxt:
                    nxt[new_odds] = (cand_max, cand_min)
                    continue
                old_max, old_min = nxt[new_odds]
                keep_max = cand_max if cand_max > old_max else old_max
                keep_min = cand_min if cand_min < old_min else old_min
                nxt[new_odds] = (keep_max, keep_min)
        reachable = nxt
        if not reachable:
            raise RuntimeError(f"no surviving itineraries of length {length}")

    max_odd = max(reachable)
    min_odd = min(reachable)
    mixed = {odds: words for odds, words in reachable.items() if "E" in words[0]}
    if mixed:
        mixed_odd = max(mixed)
        mixed_word = mixed[mixed_odd][0]
    else:
        mixed_odd = None
        mixed_word = None
    return {
        "length": length,
        "max_odd": max_odd,
        "min_odd": min_odd,
        "max_word": reachable[max_odd][0],
        "min_word": reachable[min_odd][1],
        "max_mixed_odd": mixed_odd,
        "max_mixed_word": mixed_word,
        "admissible_odd_counts": sorted(reachable),
    }


def family_table(length: int) -> dict[str, Any]:
    families = {
        "O*": o_star(length),
        "O^{N-1}E": o_then_e(length),
        "(OOE)*": ooe_repeat(length),
    }
    rows = {name: ratio_pair(word) for name, word in families.items()}
    opt = optimize(length)
    rows["optimizer_max"] = ratio_pair(opt["max_word"])
    rows["optimizer_min"] = ratio_pair(opt["min_word"])
    if opt["max_mixed_word"] is not None:
        rows["optimizer_max_mixed"] = ratio_pair(opt["max_mixed_word"])
    return {"length": length, "optimizer": opt, "families": rows}


def isolated_identity_scan(a_max: int = ISOLATED_A_MAX) -> dict[str, Any]:
    mismatches = []
    rows = []
    for a in range(0, a_max + 1):
        for r in range(0, a_max + 1):
            length, odd_count = isolated_exponents(a, r)
            equal = isolated_equals_prefix_envelope(a, r)
            if not equal:
                mismatches.append({"a": a, "r": r})
            rows.append(
                {
                    "a": a,
                    "r": r,
                    "length": length,
                    "odd_count": odd_count,
                    "ok": isolated_oe_exponent_ok(a, r),
                }
            )
    return {
        "a_max": a_max,
        "checked": (a_max + 1) ** 2,
        "mismatches": mismatches,
        "identity_holds": not mismatches,
        "sample": [row for row in rows if row["a"] in (1, 2, 3) and row["r"] <= 2],
    }


def block_cycle_table(blocks: tuple[str, ...] = BLOCK_SAMPLES) -> list[dict[str, Any]]:
    rows = []
    for block in blocks:
        row = ratio_pair(block)
        row["nonnegative_cycle"] = row["survives"]
        row["positive_cycle"] = row["three_pow"] > row["two_pow"]
        rows.append(row)
    return rows


def leftover_survival() -> dict[str, Any]:
    tables = {}
    for n in CONTROLS:
        table = prefix_table(n)
        last = table["last_above"]
        drop = table["drop"]
        tables[str(n)] = {
            "word": table["word"],
            "last_above_k": last["k"],
            "last_above_O": last["O"],
            "last_two_pow": last["two_pow_k"],
            "last_three_pow": last["three_pow_O"],
            "last_survives": last["two_pow_k"] <= last["three_pow_O"],
            "drop_k": drop["k"],
            "drop_two_pow": drop["two_pow_k"],
            "drop_three_pow": drop["three_pow_O"],
            "drop_contracts": drop["three_pow_O"] < drop["two_pow_k"],
        }
    return tables


def run_probe() -> dict[str, Any]:
    lengths = list(range(1, N_OPT + 1))
    by_length = {str(n): family_table(n) for n in lengths}
    max_at_n = [by_length[str(n)]["optimizer"]["max_odd"] for n in lengths]
    mixed_at_n = [by_length[str(n)]["optimizer"]["max_mixed_odd"] for n in lengths]
    isolated = isolated_identity_scan()
    cycles = block_cycle_table()
    leftovers = leftover_survival()
    ooe = ratio_pair("OOE")
    o_star_n = ratio_pair(o_star(N_OPT))
    mixed_n = ratio_pair(o_then_e(N_OPT))
    rho_max_is_one = max_at_n == lengths
    mixed_reaches_n_minus_one = mixed_at_n[2:] == [n - 1 for n in lengths[2:]]
    positive_mixed_cycle = ooe["three_pow"] > ooe["two_pow"]
    leftover_ok = all(row["last_survives"] and row["drop_contracts"] for row in leftovers.values())
    return {
        "basin": "ordinary_integers",
        "n_opt": N_OPT,
        "by_length": by_length,
        "max_odd_equals_length": rho_max_is_one,
        "mixed_max_is_n_minus_one": mixed_reaches_n_minus_one,
        "isolated": isolated,
        "cycles": cycles,
        "leftovers": leftovers,
        "leftover_envelope_ok": leftover_ok,
        "o_star": o_star_n,
        "o_then_e": mixed_n,
        "ooe": ooe,
        "ooe_positive": positive_mixed_cycle,
        "shared_patterns": list(SHARED_PATTERNS),
        "cycle_only_patterns": list(CYCLE_ONLY_PATTERNS),
        "termination_patterns": list(TERMINATION_PATTERNS),
        "falsifier_a": rho_max_is_one and ooe["survives"],
        "falsifier_c": positive_mixed_cycle,
        "letter_chain": False,
        "cyclemin_in_language": False,
        "parity_balance_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
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
        "not_in_paper_barrel": "ParityBalance" not in paper
        and "OddDensity" not in paper,
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
        or scan["cyclemin_in_language"]
        or scan["halt_theorem"]
        or scan["parity_balance_lean"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if (
        scan["falsifier_a"]
        and scan["falsifier_c"]
        and scan["isolated"]["identity_holds"]
        and scan["leftover_envelope_ok"]
        and scan["max_odd_equals_length"]
        and scan["mixed_max_is_n_minus_one"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "shared language is the prefix envelope 2^|w| <= 3^oddCount(w); "
                "rho_max = 1 via O* and (N-1)/N via O^{N-1}E; "
                "OOE has 9 > 8 so the cycle mean is positive"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": "shared exclusions would force a density gap",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "independent_odd_density_upper_bound": False,
            "universal_odd_density": False,
            "numerical_parity_contradiction": False,
            "cyclemin_in_language": False,
            "parity_balance_lean": False,
            "letter_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_parity_balance",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "integer 2^ell vs 3^o on every prefix; "
            f"optimizer N<= {N_OPT}; isolated identity a,r<= {ISOLATED_A_MAX}; "
            "leftovers 365/501/1517/6187; no CycleMin words"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    ooe = scan["ooe"]
    lines = [
        "# Juggler infinite AboveAnchor parity balance",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Shared finite-prefix language of AboveAnchor words.",
        "Not a halt theorem. Not a CycleMin census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     opposite envelope 2^|w| > 3^oddCount(w)",
        "Novelty hypothesis      shared exclusions cap odd density",
        "Maximum Phase-0 scope   integer optimizer; no Lean; no automaton",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- rho_max = 1 (O*): `{scan['max_odd_equals_length']}`",
        f"- mixed max = N-1 (O^{{N-1}}E): `{scan['mixed_max_is_n_minus_one']}`",
        f"- isolated = prefix envelope: `{scan['isolated']['identity_holds']}`",
        f"- OOE 3^2 vs 2^3: `{ooe['three_pow']}` vs `{ooe['two_pow']}`",
        f"- leftover last-above survives: `{scan['leftover_envelope_ok']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Maximizing families",
        "",
        f"- `O*`: length `{scan['o_star']['length']}` odd `{scan['o_star']['odd_count']}` "
        f"2^N=`{scan['o_star']['two_pow']}` 3^o=`{scan['o_star']['three_pow']}` "
        f"ratio=`{scan['o_star']['two_over_three']}`",
        f"- `O^{{N-1}}E`: length `{scan['o_then_e']['length']}` odd "
        f"`{scan['o_then_e']['odd_count']}` 2^N=`{scan['o_then_e']['two_pow']}` "
        f"3^o=`{scan['o_then_e']['three_pow']}` ratio=`{scan['o_then_e']['two_over_three']}`",
        f"- `(OOE)*` block: 2^3=`{ooe['two_pow']}` 3^2=`{ooe['three_pow']}` "
        f"ratio=`{ooe['two_over_three']}`",
        "",
        "## Isolated prefix vs envelope",
        "",
        "The isolated comparison `2^{a+2r+1} <= 3^{a+r}` is the same pair of",
        "exponents as the shared prefix envelope on `O^a E (OE)^r`.",
        f"Checked `a,r <= {scan['isolated']['a_max']}`; mismatches "
        f"`{scan['isolated']['mismatches']}`.",
        "",
        "## Leftovers",
        "",
    ]
    for n in CONTROLS:
        row = scan["leftovers"][str(n)]
        lines.append(
            f"- `{n}`: word=`{row['word']}` last_above k=`{row['last_above_k']}` "
            f"O=`{row['last_above_O']}` 2^k=`{row['last_two_pow']}` "
            f"3^O=`{row['last_three_pow']}` drop_contracts=`{row['drop_contracts']}`"
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
    print("O*", scan["o_star"]["two_over_three"])
    print("O^{N-1}E", scan["o_then_e"]["two_over_three"])
    print("OOE", scan["ooe"]["two_over_three"])


if __name__ == "__main__":
    main()
