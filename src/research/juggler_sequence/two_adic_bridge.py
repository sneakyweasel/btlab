"""2-adic admissibility versus positive-integer Juggler realizability.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an automaton and not a residual quotient. Does not reopen PE-factor,
realization-set branching, landing-image, residual-future, summed-rho,
NC-boundary, first-return, adversarial paths, information-complexity,
backward geometry, or accelerated odd-to-odd.

Identifies Admissible_P from the existing residue / valuation constraints
and compares it with follows-realizability. Balanced-ternary jets are
the second coordinate, not a replacement state.
"""

from __future__ import annotations

import json
from collections import defaultdict
from math import isqrt
from pathlib import Path
from typing import Any

from bt.calculus.derivative import D, lsd
from bt.calculus.jets import integer_jet
from bt.representation import encode
from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.information_complexity import DOCUMENTED_MOD16_PAIR
from research.juggler_sequence.landing_valuation import landing_row, v2
from research.juggler_sequence.lean_paths import (
    CELLS,
    COLLAPSE,
    ITINERARY,
    LANDING_VALUATION,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary, word_of
from research.juggler_sequence.realization_geometry import even_tower

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_2adic_integer_bridge.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_2adic_integer_bridge.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_2adic_integer_bridge.md"

K_MAX = 12
P_MAX = 16
N_MAX = 4000
ODD_SPLIT_T_MAX = 64
LIFT_PRECISIONS = (1, 2, 4, 8, 16)
BT_JET_MAX = 6

STATUS_ADMISSIBLE = "ADMISSIBLE"
STATUS_INCONCLUSIVE = "INCONCLUSIVE"
STATUS_FORBIDDEN = "FORBIDDEN"

CLASS_GREEN = "BRIDGE_GREEN"
CLASS_LIFT = "LIFTING_GREEN"
CLASS_BT = "BT_2ADIC_GREEN"
CLASS_OBS = "INTEGER_OBSTRUCTION_GREEN"
CLASS_COMPLEX = "BRIDGE_COMPLEX"

FIRST_HOLES = ("EEEEEE", "EEEEOE", "EEEOEO")
HOLE_WITNESSES = {
    "EEEEEE": {"n": even_tower(6), "kind": "EVEN_TOWER", "status": "SCALE_LIMITED"},
    "EEEEOE": {"n": 39062504258660, "kind": "INTERIOR_STATE", "status": "SCALE_LIMITED"},
    "EEEOEO": {"n": 2608762880, "kind": "INTERIOR_STATE", "status": "SCALE_LIMITED"},
}
SCALE_WITNESSES = {
    "EEEE": even_tower(4),
    "EEEEE": even_tower(5),
    "EEEEEE": even_tower(6),
    "EEEOE": 2608762880,
    "EEEOEO": 2608762880,
    "EEOEO": 51076,
    "EEEEOE": 39062504258660,
}

SELECTED_WORDS = (
    "E",
    "O",
    "EE",
    "EO",
    "OE",
    "OO",
    "EEE",
    "OOO",
    "OOE",
    "OEO",
    "EOO",
    "EEEE",
    "OOOO",
    "EEOE",
    "OOOE",
    "OOOEE",
    "EEEEE",
    "EEEEEE",
    "EEEEOE",
    "EEEOEO",
    "OEEEEE",
    "EOEEEE",
)

LEAN_THEOREMS = (
    "follows",
    "even_tower_to_one",
    "odd_odd_remainder_mod_eight",
    "landing_valuation_classification",
    "even_preimage_iff",
    "odd_preimage_unique",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def letter_of(n: int) -> str:
    return "O" if n % 2 else "E"


def first_letter(word: str) -> str | None:
    return word[0] if word else None


def first_congruent(lo: int, hi: int, residue: int, modulus: int) -> int | None:
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    residue %= modulus
    if lo < 1:
        lo = 1
    n = lo + (residue - lo % modulus) % modulus
    if n < hi:
        return n
    return None


def even_second_letter_split(residue: int, precision: int) -> dict[str, Any]:
    if precision < 1:
        raise ValueError("precision must be >= 1")
    if residue % 2:
        raise ValueError("even split requires an even residue")
    modulus = 1 << precision
    residue %= modulus
    q_even = modulus
    q_odd = modulus + 1
    n_even = first_congruent(q_even * q_even, (q_even + 1) * (q_even + 1), residue, modulus)
    n_odd = first_congruent(q_odd * q_odd, (q_odd + 1) * (q_odd + 1), residue, modulus)
    if n_even is None or n_odd is None:
        raise RuntimeError(f"even split construction failed for r={residue} P={precision}")
    if isqrt(n_even) != q_even or isqrt(n_odd) != q_odd:
        raise RuntimeError(f"even split floor mismatch for r={residue} P={precision}")
    return {
        "parity": "even",
        "precision": precision,
        "residue": residue,
        "witness_even_landing": n_even,
        "witness_odd_landing": n_odd,
        "words": ("EE", "EO"),
        "t_used": None,
        "certificate": "EVEN_CELL_CONSTRUCTION",
    }


def odd_second_letter_split(
    residue: int,
    precision: int,
    *,
    t_max: int = ODD_SPLIT_T_MAX,
) -> dict[str, Any] | None:
    if precision < 1:
        raise ValueError("precision must be >= 1")
    if residue % 2 == 0:
        raise ValueError("odd split requires an odd residue")
    modulus = 1 << precision
    residue %= modulus
    seen: dict[int, int] = {}
    last_t = -1
    for t in range(t_max + 1):
        n = residue + t * modulus
        if n < 1:
            continue
        last_t = t
        landing = isqrt(n * n * n) & 1
        if landing not in seen:
            seen[landing] = n
            if len(seen) == 2:
                return {
                    "parity": "odd",
                    "precision": precision,
                    "residue": residue,
                    "witness_even_landing": seen[0],
                    "witness_odd_landing": seen[1],
                    "words": ("OE", "OO"),
                    "t_used": t,
                    "certificate": "ODD_LANDING_SEARCH",
                }
    return {
        "parity": "odd",
        "precision": precision,
        "residue": residue,
        "witness_even_landing": seen.get(0),
        "witness_odd_landing": seen.get(1),
        "words": tuple(seen),
        "t_used": last_t,
        "certificate": "UNSPLIT_WITHIN_T_MAX",
    } if seen else None


def second_letter_split(residue: int, precision: int) -> dict[str, Any] | None:
    if residue % 2 == 0:
        return even_second_letter_split(residue, precision)
    return odd_second_letter_split(residue, precision)


def cylinder_status(word: str, residue: int, precision: int) -> dict[str, Any]:
    if precision < 1:
        raise ValueError("precision must be >= 1")
    modulus = 1 << precision
    residue %= modulus
    rec: dict[str, Any] = {
        "word": word,
        "precision": precision,
        "residue": residue,
        "status": STATUS_INCONCLUSIVE,
        "determined_prefix": "",
        "reason": "",
        "split": None,
    }
    if not word:
        rec["status"] = STATUS_ADMISSIBLE
        rec["reason"] = "empty word"
        return rec
    forced = letter_of(residue)
    rec["determined_prefix"] = forced
    if word[0] != forced:
        rec["status"] = STATUS_FORBIDDEN
        rec["reason"] = "first letter disagrees with residue parity"
        return rec
    if len(word) == 1:
        rec["status"] = STATUS_ADMISSIBLE
        rec["reason"] = "first letter is n mod 2"
        return rec
    split = second_letter_split(residue, precision)
    rec["split"] = None if split is None else {
        "certificate": split["certificate"],
        "witness_even_landing": split.get("witness_even_landing"),
        "witness_odd_landing": split.get("witness_odd_landing"),
        "t_used": split.get("t_used"),
    }
    if split is None or split["certificate"] == "UNSPLIT_WITHIN_T_MAX":
        rec["status"] = STATUS_INCONCLUSIVE
        rec["reason"] = "second letter not resolved at this precision"
        return rec
    rec["status"] = STATUS_INCONCLUSIVE
    rec["reason"] = "second letter splits; later letters are not 2-adically forced"
    return rec


def word_status(word: str, precision: int) -> str:
    if not word:
        return STATUS_ADMISSIBLE
    matching = 0 if word[0] == "E" else 1
    return cylinder_status(word, matching, precision)["status"]


def observed_language(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    realized: list[set[str]] = [set() for _ in range(k_max + 1)]
    min_realizer: dict[str, int] = {}
    for n in range(1, n_max + 1):
        current = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append(letter_of(current))
            word = "".join(letters)
            realized[len(word)].add(word)
            min_realizer.setdefault(word, n)
            current = floor_power(current)
    counts = []
    missing: dict[str, list[str]] = {}
    for k in range(1, k_max + 1):
        all_words = [
            "".join("O" if (index >> pos) & 1 else "E" for pos in range(k))
            for index in range(1 << k)
        ]
        absent = [word for word in all_words if word not in realized[k]]
        counts.append(
            {
                "k": k,
                "n_admissible_weak": 1 << k,
                "n_realized": len(realized[k]),
                "n_unmatched": len(absent),
            }
        )
        if k <= 6:
            missing[str(k)] = sorted(absent)
    return {
        "n_max": n_max,
        "k_max": k_max,
        "counts": counts,
        "missing_le6": missing,
        "min_realizer": min_realizer,
    }


def split_census(*, p_max: int = P_MAX, t_max: int = ODD_SPLIT_T_MAX) -> dict[str, Any]:
    rows = []
    failed: list[dict[str, Any]] = []
    worst_odd = {"precision": 0, "residue": 0, "t_used": -1}
    for precision in range(1, p_max + 1):
        modulus = 1 << precision
        odd_worst_t = 0
        odd_fail = 0
        for residue in range(0, modulus, 2):
            even_second_letter_split(residue, precision)
        for residue in range(1, modulus, 2):
            rec = odd_second_letter_split(residue, precision, t_max=t_max)
            if rec is None or rec["certificate"] == "UNSPLIT_WITHIN_T_MAX":
                odd_fail += 1
                failed.append({"precision": precision, "residue": residue})
                continue
            t_used = int(rec["t_used"])
            if t_used > odd_worst_t:
                odd_worst_t = t_used
            if t_used > worst_odd["t_used"]:
                worst_odd = {
                    "precision": precision,
                    "residue": residue,
                    "t_used": t_used,
                    "witness_even_landing": rec["witness_even_landing"],
                    "witness_odd_landing": rec["witness_odd_landing"],
                }
        rows.append(
            {
                "precision": precision,
                "n_even": modulus // 2,
                "n_odd": modulus // 2,
                "even_unsplit": 0,
                "odd_unsplit": odd_fail,
                "odd_worst_t": odd_worst_t,
            }
        )
    return {
        "p_max": p_max,
        "t_max": t_max,
        "all_split": not failed,
        "failed": failed,
        "worst_odd": worst_odd,
        "rows": rows,
    }


def cylinder_lift(
    word: str,
    residue: int,
    precision: int,
    *,
    n_max: int = N_MAX,
) -> dict[str, Any]:
    modulus = 1 << precision
    residue %= modulus
    start = residue if residue >= 1 else modulus
    searched = 0
    witness = None
    n = start
    while n <= n_max:
        searched += 1
        if follows_itinerary(n, word):
            witness = n
            break
        n += modulus
    failure = "FOLLOWS"
    if witness is None:
        failure = "NO_REPRESENTATIVE_IN_BOUND" if searched == 0 else "NO_WITNESS_IN_BOUND"
    return {
        "word": word,
        "precision": precision,
        "residue": residue,
        "n_searched": searched,
        "smallest_positive_representative": start if start <= n_max else None,
        "smallest_witness": witness,
        "follows": witness is not None,
        "failure_reason": failure,
    }


def lifting_survey(
    words: tuple[str, ...] = SELECTED_WORDS,
    *,
    n_max: int = N_MAX,
    precisions: tuple[int, ...] = LIFT_PRECISIONS,
) -> dict[str, Any]:
    summaries = []
    examples = []
    for word in words:
        for precision in precisions:
            modulus = 1 << precision
            n_rep = 0
            n_hit = 0
            n_empty = 0
            best = None
            empty_example = None
            for residue in range(modulus):
                if word and letter_of(residue) != word[0]:
                    continue
                start = residue if residue >= 1 else modulus
                if start > n_max:
                    continue
                rec = cylinder_lift(word, residue, precision, n_max=n_max)
                n_rep += 1
                if rec["follows"]:
                    n_hit += 1
                    if best is None or rec["smallest_witness"] < best:
                        best = rec["smallest_witness"]
                else:
                    n_empty += 1
                    if empty_example is None:
                        empty_example = rec
            summaries.append(
                {
                    "word": word,
                    "precision": precision,
                    "n_cylinders_with_rep": n_rep,
                    "n_with_witness": n_hit,
                    "n_empty_in_bound": n_empty,
                    "smallest_witness": best,
                }
            )
            if word in FIRST_HOLES and precision in (1, 8, 16) and empty_example is not None:
                examples.append(empty_example)
            if word in ("OOE", "EE") and precision in (1, 4) and best is not None:
                examples.append(cylinder_lift(word, best % (1 << precision), precision, n_max=n_max))
    return {"n_max": n_max, "summaries": summaries, "examples": examples}


def trit_sum_parity(n: int) -> int:
    return sum(encode(n).digits_lsd()) % 2


def crt_class(residue2: int, precision: int, residue3: int, jet_len: int) -> dict[str, Any]:
    mod2 = 1 << precision
    mod3 = 3**jet_len
    residue2 %= mod2
    residue3 %= mod3
    lift = ((residue3 - residue2) * pow(mod2, -1, mod3)) % mod3
    n = residue2 + mod2 * lift
    modulus = mod2 * mod3
    return {
        "n": n,
        "modulus": modulus,
        "residue2": residue2,
        "precision": precision,
        "residue3": residue3,
        "jet_len": jet_len,
        "n_mod2": n % mod2,
        "n_mod3": n % mod3,
        "jet": list(integer_jet(n, jet_len)),
        "empty": False,
        "kind": "infinite_arithmetic_family",
    }


def bt_bridge_scan(*, n_max: int = N_MAX, jet_max: int = BT_JET_MAX) -> dict[str, Any]:
    jet_splits = []
    residue_jets = []
    for depth in range(1, jet_max + 1):
        by_jet: dict[tuple[int, ...], set[int]] = defaultdict(set)
        for n in range(1, n_max + 1):
            by_jet[integer_jet(n, depth)].add(n % 2)
        mixed = sum(1 for parities in by_jet.values() if len(parities) > 1)
        jet_splits.append(
            {
                "depth": depth,
                "n_jets": len(by_jet),
                "n_mixed_parity": mixed,
                "n_pure": len(by_jet) - mixed,
            }
        )
    for precision in (1, 2, 3, 4, 8):
        modulus = 1 << precision
        mixed_lsd = 0
        for residue in range(modulus):
            digits = {int(lsd(n)) for n in range(residue if residue else modulus, n_max + 1, modulus)}
            if len(digits) > 1:
                mixed_lsd += 1
        residue_jets.append(
            {
                "precision": precision,
                "n_residues_with_rep": sum(
                    1
                    for residue in range(modulus)
                    if (residue if residue else modulus) <= n_max
                ),
                "n_mixed_lsd": mixed_lsd,
            }
        )
    pair = (1, 4)
    documented = {
        "y": DOCUMENTED_MOD16_PAIR[0],
        "z": str(DOCUMENTED_MOD16_PAIR[1]),
        "same_mod_2_16": DOCUMENTED_MOD16_PAIR[0] % (1 << 16)
        == DOCUMENTED_MOD16_PAIR[1] % (1 << 16),
        "word_y": word_of(itinerary(DOCUMENTED_MOD16_PAIR[0], 2)),
        "word_z": word_of(itinerary(DOCUMENTED_MOD16_PAIR[1], 2)),
        "jet_y": list(integer_jet(DOCUMENTED_MOD16_PAIR[0], 4)),
        "jet_z": list(integer_jet(DOCUMENTED_MOD16_PAIR[1], 4)),
    }
    trit_ok = all(trit_sum_parity(n) == n % 2 for n in range(1, n_max + 1))
    d_relation_ok = all(n == int(lsd(n)) + 3 * D(n) for n in range(-20, n_max + 1) if n != 0)
    crt_examples = [
        crt_class(1, 3, 1, 2),
        crt_class(0, 4, 2, 3),
        crt_class(33, 16, 1, 2),
    ]
    return {
        "n_max": n_max,
        "same_jet_mixed_first_letter": jet_splits,
        "same_residue_mixed_lsd": residue_jets,
        "smallest_jet_split": {
            "n": list(pair),
            "jet1": list(integer_jet(pair[0], 1)),
            "parities": [pair[0] % 2, pair[1] % 2],
        },
        "documented_mod16": documented,
        "trit_sum_parity_holds": trit_ok,
        "lsd_plus_3D_holds": d_relation_ok,
        "crt_examples": crt_examples,
    }


def precision_versus_realizer(language: dict[str, Any]) -> dict[str, Any]:
    rows = []
    selected = (
        "E",
        "O",
        "EE",
        "OO",
        "OOE",
        "OEO",
        "EEOE",
        "OOOO",
        "OOOEE",
        "EEEEE",
        "EEEEEE",
        "EEEEOE",
        "EEEOEO",
    )
    min_r = language["min_realizer"]
    for word in selected:
        observed = min_r.get(word)
        known = HOLE_WITNESSES.get(word)
        scale = SCALE_WITNESSES.get(word)
        m = observed
        if m is None and known is not None:
            m = known["n"]
        if m is None and scale is not None and follows_itinerary(scale, word):
            m = scale
        p_adm = 1 if len(word) == 1 else None
        bt_depth = None if m is None else len(encode(m))
        kind = "TYPE_A_LENGTH_ONE" if len(word) == 1 else "TYPE_B_P_ADM_UNDEFINED"
        if observed is None and m is not None:
            kind = "TYPE_C_SCALE_DELAYED"
        rows.append(
            {
                "word": word,
                "P_adm": p_adm,
                "m": m,
                "log2_m": None if m is None else (m.bit_length() - 1 if m > 0 else 0),
                "bt_depth": bt_depth,
                "observed_in_phase0": observed is not None,
                "kind": kind,
            }
        )
    return {"rows": rows}


def hard_case_rows(language: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    min_r = language["min_realizer"]
    extra = dict(SCALE_WITNESSES)
    extra.update({"EEEE": even_tower(4), "EEE": even_tower(3)})
    for word in FIRST_HOLES + ("EEEEE", "EEEOE", "EEOEO", "EEOE", "OOE"):
        known = HOLE_WITNESSES.get(word)
        witness = min_r.get(word)
        if witness is None and word in extra and follows_itinerary(extra[word], word):
            witness = extra[word]
        if witness is None and known is not None:
            witness = known["n"]
        status = cylinder_status(word, 0 if word.startswith("E") else 1, 8)
        rows.append(
            {
                "word": word,
                "phase0_m": min_r.get(word),
                "known_witness": witness,
                "follows_known": False if witness is None else follows_itinerary(witness, word),
                "word_status_P8": word_status(word, 8),
                "cylinder_status_P8": status["status"],
                "type": (
                    "TYPE_1_SCALE"
                    if witness is not None and (min_r.get(word) is None or min_r[word] > N_MAX)
                    else ("TYPE_1_IN_WINDOW" if min_r.get(word) is not None else "WITNESS_ABSENT_WITHIN_BOUND")
                ),
                "hole_kind": None if known is None else known["kind"],
            }
        )
    return rows


def landing_valuation_does_not_forbid_oo(*, n_max: int = 64) -> dict[str, Any]:
    both = 0
    law_ok = 0
    for n in range(1, n_max + 1, 2):
        if not follows_itinerary(n, "OO"):
            continue
        both += 1
        row = landing_row(n)
        if row and row["odd_odd"] and row["rho_eq_y_minus_1_mod8"]:
            law_ok += 1
    return {
        "n_max": n_max,
        "oo_starts": both,
        "mod8_law_holds": law_ok == both and both > 0,
        "forbids_OO": False,
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    splits = scan["splits"]
    language = scan["language"]
    bt = scan["bt"]
    forced_long = any(
        word_status(word, P_MAX) == STATUS_ADMISSIBLE
        for word in ("EE", "EO", "OE", "OO", "EEEEEE")
    )
    type3 = scan["type3_candidates"]
    if (
        splits["all_split"]
        and not forced_long
        and not type3
        and bt["same_jet_mixed_first_letter"][0]["n_mixed_parity"] > 0
        and language["counts"][0]["n_realized"] == 2
    ):
        return {
            "classification": CLASS_COMPLEX,
            "reason": (
                "Every tested 2-adic cylinder splits at the second Juggler letter. "
                "Weak Admissible_P is first-letter survival and therefore contains "
                "every finite word. Every Phase-0 gap is Type 1 or "
                "INTEGER-WITNESS-ABSENT-WITHIN-BOUND. Finite BT jets are CRT-"
                "transverse to 2-adic residues and do not determine the first letter. "
                "No Type-3 integer obstruction and no lifting bound survived."
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "the 2-adic / integer layers did not collapse to a green bridge",
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    extra = "\n".join(
        path.read_text(encoding="utf-8")
        for path in (CELLS, COLLAPSE, ITINERARY, LANDING_VALUATION)
    )
    combined = text + "\n" + extra
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(
            f"structure {name}" not in combined and f"inductive {name}" not in combined
            for name in FORBIDDEN_ENGINES
        ),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "admissible_equals_intreal": False,
            "compactness_gives_positive_integer": False,
            "finite_state_at_fixed_P_is_global": False,
            "type3_without_certificate": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
            "reopen_information_complexity": False,
            "reopen_adversarial_paths": False,
            "reopen_backward_geometry": False,
            "reopen_accelerated": False,
            "automaton": False,
            "cuda_census": False,
        }
    )
    return anti


def scan(
    *,
    n_max: int = N_MAX,
    k_max: int = K_MAX,
    p_max: int = P_MAX,
) -> dict[str, Any]:
    language = observed_language(n_max=n_max, k_max=k_max)
    splits = split_census(p_max=p_max)
    lifting = lifting_survey(n_max=n_max)
    bt = bt_bridge_scan(n_max=n_max)
    hard = hard_case_rows(language)
    type3 = [
        row
        for row in hard
        if row["cylinder_status_P8"] == STATUS_ADMISSIBLE and row["phase0_m"] is None
    ]
    comparison = []
    for row in language["counts"]:
        k = row["k"]
        comparison.append(
            {
                "k": k,
                "A_P": row["n_admissible_weak"],
                "I": row["n_realized"],
                "A_intersect_I": row["n_realized"],
                "A_minus_I": row["n_unmatched"],
                "I_minus_A": 0,
                "forced_P": 2 if k == 1 else 0,
            }
        )
    payload = {
        "n_max": n_max,
        "k_max": k_max,
        "p_max": p_max,
        "language": {
            "counts": language["counts"],
            "missing_le6": language["missing_le6"],
        },
        "splits": splits,
        "comparison": comparison,
        "lifting": lifting,
        "bt": bt,
        "precision_vs_m": precision_versus_realizer(language),
        "hard_cases": hard,
        "landing_valuation": landing_valuation_does_not_forbid_oo(),
        "type3_candidates": type3,
        "lean": lean_api_present(),
        "anti_overclaim": anti_overclaim(),
        "existing_api": {
            "Admissible_P": (
                "cylinder_status / word_status: first letter is n mod 2; "
                "longer words are INCONCLUSIVE because every residue class "
                "of precision P<=16 splits at the second Juggler letter. "
                "The odd-odd law landingRemainder is a constraint on realized "
                "OO landings, not an word filter."
            ),
            "IntReal": "follows_itinerary / exists n>0 with follows(n,w)",
            "m_w": "minimum observed positive realizer, plus even_tower_to_one for E^r",
        },
    }
    payload["decision"] = classify(payload)
    return payload


def compact_int(value: Any) -> Any:
    if isinstance(value, int) and value.bit_length() > 62:
        return str(value)
    if isinstance(value, list):
        return [compact_int(item) for item in value]
    if isinstance(value, dict):
        return {str(key): compact_int(item) for key, item in value.items()}
    return value


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.write_text(json.dumps(compact_int(scan_row), indent=2) + "\n", encoding="utf-8")


def _md_table(headers: list[str], rows: list[list[Any]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(str(cell) for cell in row) + " |")
    return "\n".join(lines)


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    decision = scan_row["decision"]
    splits = scan_row["splits"]
    worst = splits["worst_odd"]
    missing6 = ", ".join(f"`{w}`" for w in scan_row["language"]["missing_le6"]["6"])
    missing5 = ", ".join(f"`{w}`" for w in scan_row["language"]["missing_le6"]["5"])
    cmp_rows = [
        [
            row["k"],
            row["A_P"],
            row["I"],
            row["A_intersect_I"],
            row["A_minus_I"],
            row["I_minus_A"],
            row["forced_P"],
        ]
        for row in scan_row["comparison"]
    ]
    split_rows = [
        [row["precision"], row["n_even"], row["even_unsplit"], row["n_odd"], row["odd_unsplit"], row["odd_worst_t"]]
        for row in splits["rows"]
    ]
    lift_sel = [
        rec
        for rec in scan_row["lifting"]["summaries"]
        if rec["word"] in ("E", "OOE", "EEEEE", "EEEEEE", "EEEEOE", "EEEOEO")
        and rec["precision"] in (1, 4, 8, 16)
    ]
    lift_rows = [
        [
            rec["word"],
            rec["precision"],
            rec["n_cylinders_with_rep"],
            rec["n_with_witness"],
            rec["n_empty_in_bound"],
            rec["smallest_witness"],
        ]
        for rec in lift_sel
    ]
    pm_rows = [
        [
            rec["word"],
            rec["P_adm"],
            rec["m"],
            rec["log2_m"],
            rec["bt_depth"],
            rec["kind"],
        ]
        for rec in scan_row["precision_vs_m"]["rows"]
    ]
    hard_rows = [
        [
            rec["word"],
            rec["phase0_m"],
            rec["known_witness"],
            rec["follows_known"],
            rec["word_status_P8"],
            rec["type"],
        ]
        for rec in scan_row["hard_cases"]
    ]
    jet_rows = [
        [rec["depth"], rec["n_jets"], rec["n_mixed_parity"], rec["n_pure"]]
        for rec in scan_row["bt"]["same_jet_mixed_first_letter"]
    ]
    documented = scan_row["bt"]["documented_mod16"]
    text = f"""# Juggler 2-adic / positive-integer bridge

Status: **{decision["classification"]}**

Standalone arithmetic phase. Not a Research Engine experiment, not an
automaton, and not a termination theorem. Closed PE-factor, residual
future-quotient, summed-rho, realization-set, landing-image, NC-boundary,
first-return, adversarial, information-complexity, backward-geometry,
and accelerated-odd-to-odd branches stay closed.

## 1. Definitions

Keep the four notions separate.

**A. 2-adic / modular admissibility.** For a finite O/E word \\(w\\) and
precision \\(P\\ge 1\\), a residue \\(r\\bmod 2^P\\) has one of the three
states already used by the laboratory residue tests:

- `{STATUS_FORBIDDEN}`: the first letter of \\(w\\) disagrees with the
  parity of \\(r\\). This is the only exact 2-adic prohibition.
- `{STATUS_ADMISSIBLE}`: every 2-adic constraint at precision \\(P\\) is
  resolved and accepts \\(w\\). In this phase that happens only for
  \\(|w|\\le 1\\), where the letter is \\(n\\bmod 2\\).
- `{STATUS_INCONCLUSIVE}`: the first letter matches, but some later
  letter is not a locally constant function of \\(n\\bmod 2^P\\).

`Admissible_P(w)` is the *weak* predicate: some cylinder is not
`{STATUS_FORBIDDEN}`. `Forced_P(w)` is the *strong* predicate: some
cylinder is `{STATUS_ADMISSIBLE}` for the whole word.

The existing odd-odd law \\(\\rho\\equiv y-1\\pmod 8\\)
(`odd_odd_remainder_mod_eight`) is a constraint on a *realized* odd-to-odd
landing, not a filter that forbids the word `OO`.

**B. Integer realizability.**

\\[
\\operatorname{{IntReal}}(w)\\iff\\exists n\\in\\mathbb Z_{{>0}},\\ \\operatorname{{follows}}(n,w).
\\]

**C. Juggler realizability.** The same `follows`, using the exact map
\\(J(n)=\\lfloor\\sqrt n\\rfloor\\) (\\(n\\) even) or
\\(J(n)=\\lfloor n^{{3/2}}\\rfloor\\) (\\(n\\) odd).

**D. Positive-integer semantic compatibility.** Simultaneous exact
integrality, positivity, parity, floor-cell membership, and the Juggler
transition. This is `follows`, not a 2-adic predicate.

**Finite-precision lifting.** Given a cylinder \\(n\\equiv r\\pmod{{2^P}}\\),
ask whether some positive representative follows \\(w\\). Exhaustive search
of that cylinder inside \\([1,N]\\) is exact for the window; absence there
is `NO_WITNESS_IN_BOUND`, never a Type-3 certificate.

Quantifiers stay separate:

- finite-precision existence: \\(\\forall P\\,\\exists n\\in\\mathbb Z_{{>0}},\\ C_P(n)\\);
- one integer for all listed \\(P\\): \\(\\exists n\\,\\forall P,\\ C_P(n)\\);
- one 2-adic integer: \\(\\exists x\\in\\mathbb Z_2\\,\\forall P,\\ C_P(x)\\).

## 2. Existing certified machinery

| Object | API | Semantics |
| --- | --- | --- |
| exact step | `floor_power` | \\(J\\) |
| word word | `follows_itinerary` / Lean `follows` | IntReal witness check |
| even tower | `even_tower` / Lean `even_tower_to_one` | \\(m(E^r)=2^{{2^{{r-1}}}}\\) |
| odd-odd remainder | `landing_row` / `odd_odd_remainder_mod_eight` | \\(\\rho\\equiv y-1\\pmod 8\\) on realized OO |
| 2-adic valuation | `landing_valuation.v2` | \\(v_2\\) of an integer, not an word automaton |
| BT coordinates | `encode`, `lsd`, `D`, `integer_jet` | \\(n=\\mathrm{{lsd}}(n)+3D(n)\\), \\(J_k(n)\\) |
| first rooted holes | realization-geometry certificates | `SCALE_LIMITED`, not `CELL_EMPTY` |
| documented \\(2^{{16}}\\) pair | `DOCUMENTED_MOD16_PAIR` | same residue, words `{documented["word_y"]}` vs `{documented["word_z"]}` |

There is no pre-existing Juggler `Admissible_P` with the Collatz Layer-C
automaton semantics. Collatz valuation cylinders are a different map and
are not imported. The object used here is the residue-class status of
the exact first-letter law plus the exact second-letter split.

## 3. Finite-precision comparison

Phase 0: \\(k\\le {scan_row["k_max"]}\\), \\(P\\le {scan_row["p_max"]}\\),
\\(n\\le {scan_row["n_max"]}\\). Weak `Admissible_P` contains every word of
length \\(k\\) for every tested \\(P\\ge 1\\), because every word has a
first-letter-compatible residue and no later letter is 2-adically
forced.

{_md_table(["k", "A_P (weak)", "I(k) in n<=4000", "A ∩ I", "A \\\\ I", "I \\\\ A", "Forced_P"], cmp_rows)}

`I \\\\ A` is empty: every observed realizer satisfies the first-letter
law. That direction is expected and is not the bridge.

`A \\\\ I` at \\(k=5\\): {missing5}.

`A \\\\ I` at \\(k=6\\): {missing6}.

Do not call an word missing from \\(I(k)\\) unrealizable. The three first
atlas holes remain `SCALE_LIMITED`. Length \\(\\le 4\\) fills completely
inside \\(n\\le 4000\\).

Second-letter splits, every residue, \\(P=1..{scan_row["p_max"]}\\):

{_md_table(["P", "even classes", "even unsplit", "odd classes", "odd unsplit", "odd worst t"], split_rows)}

All even classes split by the exact square-cell construction: the
intervals of \\(q=2^P\\) and \\(q=2^P+1\\) each have length \\(>2^P\\), so each
meets the arithmetic progression, and those two \\(q\\) have opposite
parity. All odd classes split by a search with \\(t\\le {splits["t_max"]}\\);
the worst case is \\(P={worst["precision"]}\\), \\(r={worst["residue"]}\\),
\\(t={worst["t_used"]}\\). No unsplit cylinder occurred.

Label: even split **EXACT — HUMAN PROOF**; odd split on \\(P\\le 16\\)
**COMPUTATIONALLY VERIFIED**.

## 4. Cylinder lifting

The search in a cylinder is the complete set of positive representatives
in \\([1,N]\\), hence at most \\(\\lceil N/2^P\\rceil\\) evaluations. That is
the justified bound.

{_md_table(["word", "P", "cylinders with a rep <=4000", "with witness", "empty in bound", "smallest witness"], lift_rows)}

For `EEEEEE`, the even tower \\(m=2^{{32}}\\) lies in the cylinder
\\(0\\bmod 2^P\\) for every \\(P\\le 32\\), but not in \\([1,4000]\\). Empty
Phase-0 lifting rows are Type 1, not Type 3.

## 5. Precision versus minimal realizer

`P_adm(w)` is the least \\(P\\) at which some cylinder is strongly
`{STATUS_ADMISSIBLE}` for the whole word. For \\(|w|\\ge 2\\) that \\(P\\)
does not exist in the Phase-0 range.

{_md_table(["word", "P_adm", "m(w)", "log2 m", "BT depth", "kind"], pm_rows)}

Length-one words are Type A: `P_adm=1` matches the parity of \\(m(w)\\).
Longer realized itineraries are Type B: a finite realizer exists while no
finite precision forces the word. The first holes are Type C only as
*scale delay*, not as 2-adically forced empty cylinders.

## 6. Balanced-ternary bridge

Canonical expansion \\(n=\\sum a_i 3^i\\), \\(a_i\\in\\{{-1,0,+1\\}}\\).
The identity \\(n=\\mathrm{{lsd}}(n)+3D(n)\\) holds on the scanned window
(`{scan_row["bt"]["lsd_plus_3D_holds"]}`). The sum of *all* trits
recovers parity, because \\(3^i\\equiv 1\\pmod 2\\):

\\[
n\\equiv\\sum_i a_i\\pmod 2.
\\]

A finite jet \\(J_k(n)=(a_0,\\ldots,a_{{k-1}})\\) determines only
\\(n\\bmod 3^k\\). The leftover \\(3^k D^k(n)\\) is odd-modulus and can flip
parity. Smallest counterexample: \\(J_1(1)=J_1(4)=(1)\\) with opposite
first Juggler letters.

Same finite BT prefix versus first-letter (hence versus `Admissible_P`)
on \\(n\\le 4000\\):

{_md_table(["jet depth", "jets seen", "mixed parity", "pure parity"], jet_rows)}

Every positive depth has mixed-parity jets. Conversely, every tested
2-adic residue class that meets \\([1,4000]\\) realises more than one
`lsd` except the trivial one-representative classes at large \\(P\\).

Chinese remainder: \\(\\gcd(2^P,3^k)=1\\), so

\\[
(n\\equiv r\\pmod{{2^P}})\\ \\cap\\ (J_k(n)=a)
\\]

is a single class modulo \\(2^P 3^k\\), hence an infinite arithmetic
family, never empty and never a singleton in \\(\\mathbb Z\\). The two
positional systems are transverse. A finite BT jet does not constrain
the 2-adic admissibility class. A finite 2-adic residue does not
constrain a finite BT jet.

The documented pair \\(n\\equiv 33\\pmod{{2^{{16}}}}\\) has words
`{documented["word_y"]}` and `{documented["word_z"]}` and BT 4-jets
`{documented["jet_y"]}` versus `{documented["jet_z"]}`.

## 7. Quantifier separation

For the *first-letter* constraint \\(C_P(n):\\Leftrightarrow n\\equiv w_0\\pmod 2\\):

- \\(\\forall P\\,\\exists n\\in\\mathbb Z_{{>0}},\\ C_P(n)\\) holds (\\(n=2\\) or \\(n=1\\));
- the same \\(n\\) works for every \\(P\\);
- the 2-adic integers satisfying every \\(C_P\\) are the even or odd
  2-adics, a different space from \\(\\mathbb Z_{{>0}}\\).

For the *strong* constraint “the cylinder forces \\(w\\)”:

- no \\(P\\le 16\\) has a cylinder forcing an word of length \\(\\ge 2\\);
- compactness of \\(\\mathbb Z_2\\) therefore does not produce a
  2-adic Juggler word. \\(J\\) is an Archimedean floor map, not a
  2-adic dynamical system.

For `EEEEEE`, \\(2^{{32}}\\) realises the word and lies in
\\(0\\bmod 2^P\\) for all \\(P\\le 32\\). That is one integer meeting every
*listed* even cylinder up to \\(P=32\\). It is not a point of
\\(\\bigcap_P 2^P\\mathbb Z_2=\\{{0\\}}\\).

## 8. Hard cases

{_md_table(["word", "m in n<=4000", "known witness", "follows", "status P=8", "failure type"], hard_rows)}

`EEEEEE`, `EEEEOE`, and `EEEOEO` remain `SCALE_LIMITED`. 2-adic
admissibility does not confuse a scale-bound witness with a genuine
integer incompatibility: those itineraries are weakly admissible at every
tested \\(P\\) and strongly unresolved at every tested \\(P\\).

Landing valuation on OO starts \\(n\\le 64\\):
`{scan_row["landing_valuation"]["oo_starts"]}` realized, mod-8 law
`{scan_row["landing_valuation"]["mod8_law_holds"]}`, and the law does
not forbid `OO`.

## 9. Candidate mathematical statements

- Every 2-adic cylinder of precision \\(P\\ge 1\\) determines the first
  Juggler letter and no later letter, for all even residues by the
  square-cell construction and for all odd residues with \\(P\\le 16\\)
  by the recorded splits.  
  Tags: **EXACT — HUMAN PROOF** (even); **COMPUTATIONALLY VERIFIED** (odd, \\(P\\le 16\\)).
- Weak `Admissible_P` is the first-letter language \\(\\{{O,E\\}}^*\\).  
  Tag: **EXACT — HUMAN PROOF**, given the split law.
- `follows(n,w)` implies weak `Admissible_P(w)`.  
  Tag: **EXACT — HUMAN PROOF**. This is the expected direction, not the bridge.
- Finite BT jet \\(\\Rightarrow\\) same `Admissible_P` status.  
  Tag: **REFUTED** at \\(n=1,4\\).
- Finite 2-adic residue \\(\\Rightarrow\\) a fixed BT \\(k\\)-jet.  
  Tag: **REFUTED** (mixed `lsd` in every small even class).
- CRT intersection of a 2-adic cylinder with a BT \\(k\\)-cylinder is a
  nonempty arithmetic progression modulo \\(2^P 3^k\\).  
  Tag: **EXACT — HUMAN PROOF**.
- `ADMISSIBILITY_REALIZATION_GREEN` / `LIFTING_BOUND_GREEN` /
  `BT_2ADIC_BRIDGE_GREEN` / `INTEGER_OBSTRUCTION_GREEN` /
  `PRECISION_REALIZATION_GREEN`.  
  Tag: **REFUTED** as Phase-0 promotion targets. The surviving
  relation is first-letter plus witness scale.
- Type-3 integer obstruction beyond resolved 2-adic conditions.  
  Tag: **OBSERVATION** (none found; not a proof that none exist).

No statement is **LEAN-CERTIFIED** beyond the already-packaged `follows`,
`even_tower_to_one`, and landing-valuation lemmas. No new Lean file.

## 10. Decision

**{decision["classification"]}**. Branch decision: **CLOSE**.

{decision["reason"]}

Do not call weak admissibility equivalent to IntReal. The layers differ
by witness scale, not by an extra finite 2-adic prohibition. Do not
build an automaton because each fixed \\(P\\) has finitely many residues.
Do not reopen residual quotients or information-complexity.

Best next question: none from this branch.
"""
    path.write_text(text, encoding="utf-8")


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    decision = scan_row["decision"]
    path.write_text(
        f"""# Juggler 2-adic / positive-integer bridge

Status: **EXPLORATORY**

Standalone arithmetic layer on the exact Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not an automaton,
and not a claim that every positive integer reaches 1.

## Problem

Is there a structural distinction between finite O/E itineraries that
survive 2-adic residue / valuation constraints and those that are
realized by a positive integer under the exact Juggler map?

## Exact statement

For a finite word \\(w\\) and precision \\(P\\ge 1\\), `Admissible_P(w)` is
the existing residue-class predicate: the first letter is \\(n\\bmod 2\\),
and later letters are `{STATUS_INCONCLUSIVE}` once a cylinder splits.
`IntReal(w)` is \\(\\exists n>0,\\ \\operatorname{{follows}}(n,w)\\). Phase 0
asks whether the two predicates differ by anything other than witness
scale, and whether a finite balanced-ternary jet constrains the 2-adic
class. This says nothing about totality.

## Current literature

- `follows` / `floorPower` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary`.
- `even_tower_to_one` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Collapse`.
- Odd-odd remainder \\(\\rho\\equiv y-1\\pmod 8\\) —
  **EXACT — LEAN VERIFIED**; landing valuation **CLOSE** as
  `LANDING_VALUATION_IS_Y_MOD_8`.
- Collatz valuation cylinders / Layer C —
  a different map; not imported.
- Word language / PE-factor —
  **CLOSE**. Do not reopen.
- Residual future-quotient / information complexity —
  **CLOSE**. Sample-relative \\(k^*_2\\) is not `Admissible_P`.
- Realization geometry —
  **CLOSE**. First holes `EEEEEE` / `EEEEOE` / `EEEOEO` are
  `SCALE_LIMITED`.
- Prefix-NC admissibility / preimage cylinders / backward geometry /
  accelerated odd-to-odd —
  **CLOSE**.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     For finite Juggler O/E words, is Admissible_P
                        a strictly weaker predicate than IntReal, and
                        does a finite BT jet constrain the 2-adic class?
Novelty hypothesis      A Type-3 integer obstruction, a BT↔2-adic
                        constraint, or an exact P(w) vs m(w) lift bound
Falsifier               Only the first letter is 2-adically forced;
                        every A_P\\\\I gap is SCALE_LIMITED or bound-
                        limited; BT jets and 2-adic residues are
                        CRT-transverse
Existing machinery      follows_itinerary, floor_power, landing_valuation,
                        even_tower_to_one, integer_jet / encode / lsd,
                        SCALE_LIMITED hole certificates
Maximum Phase-0 scope   k<=12, P<=16, n<=4000; constructive cylinder
                        splits; selected-word lifting; BT jet tables
Promotion criterion     Type-3 certificate, exact BT constraint on
                        admissibility, or explicit lifting bound
Stop criterion          Gaps are Type 1; BT and 2-adic remain
                        transverse; Admissible_P is first-letter only
```

## Balanced-ternary formulation

\\(J_k(n)\\) is the length-\\(k\\) integer jet. A 2-adic cylinder is
\\(n\\equiv r\\pmod{{2^P}}\\). Their intersection is the CRT class modulo
\\(2^P 3^k\\).

## Why BT may be relevant

The map mixes parity (powers of 2) with floor powers that see the
factor 3. BT is the laboratory coordinate for powers of 3. Relevance is
a question, not a claim that BT solves Juggler.

## Candidate operations / invariants

- First letter is \\(n\\bmod 2\\) —
  **EXACT — HUMAN PROOF**
- Even 2-adic cylinders split at letter 2 —
  **EXACT — HUMAN PROOF**
- Odd 2-adic cylinders split at letter 2 for \\(P\\le 16\\) —
  **COMPUTATIONALLY VERIFIED**
- Finite BT jet determines the first letter —
  **REFUTED** (\\(n=1,4\\))
- CRT intersection empty —
  **REFUTED**
- Type-3 obstruction for the first holes —
  **REFUTED**; they are `SCALE_LIMITED`
- `ADMISSIBILITY_REALIZATION_GREEN` —
  **REFUTED** as a Phase-0 promotion
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.two_adic_bridge`
- Records: [juggler_2adic_integer_bridge.md](../research/juggler_2adic_integer_bridge.md),
  [juggler_2adic_integer_bridge.json](../research/juggler_2adic_integer_bridge.json)
- Tests: `tests/research/juggler_sequence/test_two_adic_bridge.py`

No GPU. No atlas recensus. No new Lean file. The Research Engine
control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- “A finite 2-adic cylinder forces the second Juggler letter”: every
  residue at \\(P\\le 16\\) splits.
- “Same BT 1-jet implies the same first letter”: \\(1\\) and \\(4\\).
- “`EEEEEE` is 2-adically forbidden”: it is weakly admissible and
  realized at \\(2^{{32}}\\).
- “Absence in \\(n\\le 4000\\) is Type 3”: the first holes have
  `SCALE_LIMITED` witnesses.

## Formalization

None added. Existing lemmas in `Itinerary`, `Collapse`,
`LandingValuation`, and `Cells` stay as they are. No `sorry`.

## Results

Classification **{decision["classification"]}**.

{decision["reason"]}

## Open questions

None from this branch. Do not invent another coordinate system. Do not
return to residual quotients or information-complexity.

## Decision

**CLOSE**. {decision["reason"]} Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative bridge census and two elementary
exact facts (even-cylinder split; CRT transversality), not a paper
candidate and not a Juggler totality result.
""",
        encoding="utf-8",
    )


def main() -> None:
    row = scan()
    write_json(row)
    write_docs(row)
    write_dossier(row)
    print(row["decision"]["classification"])


if __name__ == "__main__":
    main()
