"""View-model for the finite-dynamics note companion.

Instantiates existing Juggler maps. Does not prove anything: Lean remains
the authority for exact claims; Theorem 4.6 and Corollary 5.10 are
verified computations. Bit caps keep Streamlit reruns bounded.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR, parity_finance_rows
from research.juggler_sequence.cycle_walk_charge import DATA_DIR as WALK_DATA_DIR
from research.juggler_sequence.bunched_last_cluster import FAMILIES
from research.juggler_sequence.cycle_length_seven import (
    THRESHOLD_BY_SUFFIX,
    cycle_itinerary_hits,
    orbit_until_fail,
    suffix_after_last_internal_e,
)
from research.juggler_sequence.cycle_ooo_scale import cyclemin_orientation
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.envelope_defect import BIT_LIMIT, tiny_deficit
from research.juggler_sequence.expansion_slack import FOUR_BLOCK
from research.juggler_sequence.first_e_e4 import (
    FAMILY_NAME,
    GAPPED_EE_MIN,
    GAPPED_EOE_MIN,
    classify_leftover,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.global_defect import (
    compose_formula,
    is_monochrome,
    local_defect,
    pow_gap,
)
from research.juggler_sequence.length11_nonpullback import (
    BEST_V,
    EEEE_WORD,
    SPOT_WITNESS,
)
from research.juggler_sequence.length8_bootstrap import named_length8_filter
from research.juggler_sequence.power_itineraries import floor_power, odd_count, regime_of
from research.juggler_sequence.progress_coverage import coverage_bucket, first_even_residual

TRAJECTORY_STEPS_MAX = 80
DISPLAY_BITS_MAX = 256
DEFECT_BITS = BIT_LIMIT
WORD_MAX = 8
CYCLE_WORD_MAX = 16
LEFTOVER_REPLAY_MAX = 256
DESCENT_WINDOW_MAX = 500
EVEN_PREIMAGE_LIST_MAX = 40

N_PRESETS: dict[str, int] = {
    "3 (note trajectory)": 3,
    "37 (note peak)": 37,
    "1999 (four-block)": 1999,
}

WORD_PRESETS: tuple[str, ...] = (
    "OOE",
    "OOOEE",
    "OOOEOE",
    "OOOOEE",
    "OOOOEOE",
    "OOOOOEE",
)

CYCLE_WORD_PRESETS: tuple[str, ...] = (
    "OEO",
    "OOE",
    "EOOOOE",
    "OEOOOE",
    "OOOEOE",
    "OOOOEE",
    "OOEOOE",
    "OOOOOOEE",
    "OOOOOOEEE",
    "OOEOOOOEE",
    "OOOOOOOEEEE",
    "OOEOOOOOEEE",
    "OOEOOOOE",
    "OOOOOO",
)

THREE_EVEN_LEFTOVER = "OOOOOOEEE"

_EXCLUDING_KINDS = frozenset(
    {
        "all-odd",
        "all-even",
        "not expanding",
        "odd-run",
        "threshold",
        "bootstrap",
        "leftover",
        "two-even leftover",
        "three-even leftover",
        "gapped leftover",
        "bunched leftover",
        "four-even gapped",
        "four-even bunched",
        "excluded",
    }
)

_THREE_EVEN_RE = re.compile(r"^(O+)E(O*)E(O*)E$")
_FOUR_EVEN_RE = re.compile(r"^(O+)E(O*)E(O*)E(O*)E$")
_BUNCHED_META = {(int(row["b"]), int(row["c"])): row for row in FAMILIES}
_BUNCHED_LEDGER = {
    "EEE": "J-three-even-eee",
    "EOEE": "J-three-even-eoee",
    "EOOEE": "J-three-even-eooee",
    "EOOOEE": "J-three-even-eoooee",
    "EEOE": "J-three-even-eeoe",
    "EOEOE": "J-three-even-eoeoe",
    "EOOEOE": "J-three-even-eooeoe",
}

EEEE_THRESHOLD = "n^{139} > 2^{4118}"
EEEE_N0 = 828_484_394
INTERNAL_E_MARGIN = "243/256"
INTERNAL_E_WORD = "OOEOOOOOEEE"

NOTE_PEAK_37 = 24_906_114_455_136
NOTE_TRAJECTORY_3: tuple[int, ...] = (3, 5, 11, 36, 6, 2, 1)

LEFTOVER_CUTOFF: dict[str, int] = {
    "OOOEOE": 256,
    "OOOOEE": 256,
    "OOOOEOE": 14,
    "OOOOOEE": 14,
}

# Note classifications for even-terminating expanding words of length ≤ 8.
# Periods ≤ 25780 are excluded separately by Theorem 4.6 at the verified
# descent floor 10^6; these rows name the local obstruction when there is one.
_WORD_CLASS: dict[str, tuple[str, str]] = {
    "OOE": ("threshold", "Lemma 3.4(i): OO next-square vs last-even one-step preimage"),
    "OOOE": ("odd-run", "Lemma 3.4(v)"),
    "OOOOE": ("odd-run", "Lemma 3.4(v)"),
    "OOOOOE": ("odd-run", "Lemma 3.4(v)"),
    "EOOOOE": ("rotation", "rotates onto OOOOEE"),
    "OEOOOE": ("rotation", "rotates onto OOOEOE"),
    "OOEOOE": ("bootstrap", "Theorem 3.6: cycle-min + OO threshold"),
    "OOOEOE": ("leftover", "Lemma 3.5"),
    "OOOOEE": ("leftover", "Lemma 3.5"),
    "OOOOOOE": ("odd-run", "Lemma 3.4(v)"),
    "EOOOOOE": ("rotation", "rotates onto OOOOOEE"),
    "OEOOOOE": ("rotation", "rotates onto OOOOEOE"),
    "OOEOOOE": ("bootstrap", "Lemma 3.4(ii) at threshold 3"),
    "OOOEOOE": ("bootstrap", "Lemma 3.4(i) at threshold 5"),
    "OOOOEOE": ("leftover", "Lemma 3.7"),
    "OOOOOEE": ("leftover", "Lemma 3.7"),
    "OOOOOOOE": ("odd-run", "Lemma 3.4(v) at a=7"),
    "EOOOOOOE": ("rotation", "rotates onto OOOOOOEE"),
    "OEOOOOOE": ("rotation", "rotates onto OOOOOEOE"),
    "OOOOEOOE": ("bootstrap", "internal E plus OO next-square"),
    "OOOEOOOE": ("bootstrap", "internal E plus OOO next-square"),
    "OOEOOOOE": ("bootstrap", "internal E plus O^4 odd-run threshold"),
    "OOOOOEOE": ("two-even leftover", "Theorem 3.12 at k=8"),
    "OOOOOOEE": ("two-even leftover", "Theorem 3.12 at k=8"),
}

CLAIM_ROWS: tuple[dict[str, str], ...] = (
    {
        "text": "Theorem 2.1 fixed-word monotonicity",
        "lean": "image_monotone_of_follows",
        "ledger": "J-fixed-word-image-monotone",
    },
    {
        "text": "Theorem 2.2 / Corollary 2.3 power envelope",
        "lean": "power_bound_word / power_bound_contracts",
        "ledger": "J-power-envelope-contraction",
    },
    {
        "text": "Theorems 2.4–2.6 global defect",
        "lean": "global_defect_identity / global_defect_append",
        "ledger": "J-global-defect-identity",
    },
    {
        "text": "Lemma 3.1 odd cells unique",
        "lean": "odd_preimage_unique",
        "ledger": "J-inverse-preimage-asymmetry",
    },
    {
        "text": "Theorem 3.2 cycle restrictions",
        "lean": "cycle_itinerary_formally_expanding",
        "ledger": "J-cycle-finite-structure",
    },
    {
        "text": "Lemma 3.5 leftovers OOOEOE, OOOOEE",
        "lean": "no_cycle_itinerary_oooeoe / no_cycle_itinerary_ooooee",
        "ledger": "J-leftover-length-six-orientations",
    },
    {
        "text": "Theorem 3.6 census length ≤ 6",
        "lean": "no_cycle_itinerary_length_le_six",
        "ledger": "J-small-cycle-census",
    },
    {
        "text": "Lemma 3.7 leftovers OOOOEOE, OOOOOEE",
        "lean": "no_cycle_itinerary_ooooeoe / no_cycle_itinerary_oooooee",
        "ledger": "J-leftover-length-seven-orientations",
    },
    {
        "text": "Theorem 3.8 census length ≤ 7",
        "lean": "no_cycle_itinerary_length_le_seven",
        "ledger": "J-small-cycle-census-seven",
    },
    {
        "text": "Laboratory census length ≤ 8",
        "lean": "no_cycle_itinerary_length_le_eight",
        "ledger": "J-small-cycle-census-eight",
    },
    {
        "text": "Theorem 3.12 two-even leftovers",
        "lean": "no_cycle_itinerary_two_even_ee / no_cycle_itinerary_two_even_eoe",
        "ledger": "J-two-even-leftover-ee",
    },
    {
        "text": "Theorem 3.13 gapped three-even CycleMin",
        "lean": "no_cycleMin_gapped_three_even_ee / _eoe",
        "ledger": "J-first-e-transport-ee",
    },
    {
        "text": "Theorems 3.14–3.20 bunched last-cluster",
        "lean": "no_cycle_itinerary_three_even_*",
        "ledger": "J-three-even-eee",
    },
    {
        "text": "Theorem 3.21 gapped three-even CycleWord",
        "lean": "no_cycle_itinerary_gapped_three_even_ee / _eoe",
        "ledger": "J-gapped-cycle-word-ee",
    },
    {
        "text": "Theorem 3.22 even-count; Corollary 3.23 period ≥ 11",
        "lean": "no_cycle_itinerary_even_count_le_three / cycle_itinerary_length_ge_eleven",
        "ledger": "J-even-count-le-three",
    },
    {
        "text": "Theorem 4.4 cycle-minimum finance",
        "lean": "cycleMin_finance",
        "ledger": "J-cycle-finance-inequality",
    },
    {
        "text": "Theorem 4.6 verified computation: L ≥ 25781 at N0 = 10^6",
        "lean": "named computation; not Lean",
        "ledger": "J-cycle-word-eliahou-leftover-instance",
    },
    {
        "text": "Theorem 5.2: L ≥ 50508 at the laboratory floor 26254995",
        "lean": "named computation; not Lean",
        "ledger": "J-cycle-period-fifty-thousand",
    },
    {
        "text": "Theorem 5.9: walk charge raises the laboratory bound to L ≥ 176251",
        "lean": "cycleMin_hug_kill_criterion; evaluation is computation",
        "ledger": "J-cyclemin-walk-charge-instance",
    },
    {
        "text": "Corollary 5.10: L ≥ 478245 at N0 = 162849448",
        "lean": "named computation; not Lean",
        "ledger": "J-cycle-period-four-hundred-seventy-eight-thousand",
    },
    {
        "text": "Section 6 descent certificates (not a halt theorem)",
        "lean": "even_finiteProgress / odd_even_finiteProgress",
        "ledger": "J-finite-progress-boundary",
    },
)

CENSUS_LEDGER_IDS: tuple[str, ...] = (
    "J-small-cycle-census",
    "J-small-cycle-census-seven",
    "J-small-cycle-census-eight",
    "J-leftover-length-six-orientations",
    "J-leftover-length-seven-orientations",
)

LEFTOVER_FAMILY_LEDGER_IDS: tuple[str, ...] = (
    "J-two-even-leftover-ee",
    "J-two-even-leftover-eoe",
    "J-first-e-transport-ee",
    "J-gapped-cycle-word-ee",
    "J-three-even-eee",
)

LAB_LEFTOVER_DECISIONS: tuple[dict[str, str], ...] = (
    {
        "branch": "First-E at four evens",
        "decision": "CLOSE",
        "tag": "REPARAMETERIZATION",
        "note": "Gapped last-cluster restates 3.13; long-a1 bunched restates 3.14–3.20 at y",
    },
    {
        "branch": "Four-even short-gap Z4",
        "decision": "PARK",
        "tag": "OBSERVATION",
        "note": "One pullback cell fires at a0+1 with N0≤180; leaks at the 30 length-11 words",
    },
    {
        "branch": "EEEE tight pullback",
        "decision": "CLOSE",
        "tag": "REFUTED",
        "note": f"{EEEE_WORD} already uses r=4 trailing evens; {EEEE_THRESHOLD} first at n={EEEE_N0}",
    },
    {
        "branch": "Length-11 non-pullback",
        "decision": "CLOSE",
        "tag": "REFUTED",
        "note": f"Rotation cannot kill an open CycleMin; internal-E closest {INTERNAL_E_MARGIN} on {BEST_V}",
    },
    {
        "branch": "Lean leftover merge",
        "decision": "PROMOTE",
        "tag": "packaging",
        "note": "leftover_prefix_preimage; families in LeftoverFamilies; Paper A census ≤7",
    },
    {
        "branch": "Length-8 two-even squares",
        "decision": "CLOSE",
        "tag": "REPARAMETERIZATION",
        "note": "OOOOEOOE=OO(OOE)^2 and OOOEOOOE=(OOOE)^2 are OO/OOO bootstrap, not leftovers",
    },
    {
        "branch": "Length-8 census",
        "decision": "PROMOTE",
        "tag": "EXACT — LEAN VERIFIED",
        "note": "no_cycle_itinerary_length_le_eight; implied by Paper A period ≥11; not a halt theorem",
    },
)

PAPER_FLOOR = 1_000_000
PAPER_PERIOD = 25_781
PAPER_L_CAP = 100_000
PAPER_EXCEPTION_COUNT = 141
LAB_FLOOR = 26_254_995
LAB_PARITY_PERIOD = 50_508
LAB_WALK_PERIOD = 176_251
PRINTED_FLOOR = 162_849_448
PRINTED_PERIOD = 478_245
WALK_WINDOW_LO = 50_508
WALK_WINDOW_HI = 301_994
BLOCKER_FAN = 301_994
DK_BREAKEVEN_FLOOR = 348_000_000
PRINTED_KILL_COUNT = 15
FINANCE_UI_L_MAX = 2_000
FINANCE_CHART_L_MAX = 400
RECORD_LENGTHS: tuple[int, ...] = (1, 3, 11, 19, 84, 569, 1054, 25781, 50508)

WALK_CHARGE_LEDGER_IDS: tuple[str, ...] = (
    "J-cyclemin-walk-charge-instance",
    "J-residual-floor-one-hundred-sixty-two-million",
    "J-cycle-period-four-hundred-seventy-eight-thousand",
)

INSTANCE_ROWS: tuple[dict[str, Any], ...] = (
    {
        "theorem": "Theorem 4.6",
        "floor": PAPER_FLOOR,
        "period": PAPER_PERIOD,
        "mechanism": "parity 6/5 table",
        "ledger": "J-cycle-word-eliahou-leftover-instance",
    },
    {
        "theorem": "Theorem 5.2",
        "floor": LAB_FLOOR,
        "period": LAB_PARITY_PERIOD,
        "mechanism": "same parity table",
        "ledger": "J-cycle-period-fifty-thousand",
    },
    {
        "theorem": "Theorem 5.9",
        "floor": LAB_FLOOR,
        "period": LAB_WALK_PERIOD,
        "mechanism": "walk-charge envelope",
        "ledger": "J-cyclemin-walk-charge-instance",
    },
    {
        "theorem": "Corollary 5.10",
        "floor": PRINTED_FLOOR,
        "period": PRINTED_PERIOD,
        "mechanism": "same kill criterion at the second floor",
        "ledger": "J-cycle-period-four-hundred-seventy-eight-thousand",
    },
)


@lru_cache(maxsize=1)
def _parity_artifact() -> dict[str, Any]:
    payload = json.loads(
        (DATA_DIR / "exceptions_parity.json").read_text(encoding="utf-8")
    )
    if int(payload["floor"]) != PAPER_FLOOR:
        raise ValueError("exceptions_parity.json is not the Theorem 4.6 floor 10^6")
    if int(payload["first_exception"]) != PAPER_PERIOD:
        raise ValueError("exceptions_parity.json first survivor is not 25781")
    if int(payload["count"]) != PAPER_EXCEPTION_COUNT:
        raise ValueError("exceptions_parity.json count is not 141")
    return payload


@lru_cache(maxsize=1)
def _parity_records() -> dict[int, dict[str, Any]]:
    return {int(row["L"]): dict(row) for row in _parity_artifact()["records"]}


@lru_cache(maxsize=1)
def paper_exception_lengths() -> tuple[int, ...]:
    """Admissible lengths ℰ at the Theorem 4.6 descent floor 10^6."""

    payload = _parity_artifact()
    lengths = tuple(int(length) for length in payload["lengths"])
    if len(lengths) != int(payload["count"]):
        raise ValueError("exceptions_parity.json count does not match lengths")
    return lengths


@lru_cache(maxsize=1)
def paper_exception_set() -> frozenset[int]:
    return frozenset(paper_exception_lengths())


@lru_cache(maxsize=4)
def _finance_table(l_max: int) -> tuple[dict[str, Any], ...]:
    return tuple(parity_finance_rows(l_max))


def finance_row_of(length: int) -> dict[str, Any] | None:
    """One parity-finance row, or None when n_max is not computed here."""

    if length < 1:
        return None
    if length <= FINANCE_UI_L_MAX:
        return dict(_finance_table(FINANCE_UI_L_MAX)[length - 1])
    record = _parity_records().get(length)
    if record is not None:
        return {
            "L": length,
            "o": int(record["o"]),
            "theta": record.get("theta"),
            "bound": "parity_6/5",
            "n_max": int(record["n_max"]),
            "record": True,
        }
    return None


@dataclass(frozen=True)
class FinanceView:
    length: int
    o_min: int | None
    n_max: int | None
    record: bool
    in_exception_set: bool
    excluded_by_floor: bool
    admissible: bool
    beyond_table: bool
    status: str


def finance_view(length: int) -> FinanceView:
    """Paper A Theorem 4.6 status of one period at the descent floor 10^6."""

    if length < 1:
        raise ValueError("finance_view requires L ≥ 1")
    in_set = length in paper_exception_set()
    beyond = length > PAPER_L_CAP
    row = finance_row_of(length)
    o_min = None if row is None else int(row["o"])
    n_max = None if row is None else int(row["n_max"])
    record = bool(row["record"]) if row is not None else length in RECORD_LENGTHS
    if beyond:
        status = "beyond table"
        excluded = False
        admissible = False
    elif in_set:
        status = "admissible"
        excluded = False
        admissible = True
    else:
        status = "excluded"
        excluded = True
        admissible = False
    return FinanceView(
        length=length,
        o_min=o_min,
        n_max=n_max,
        record=record,
        in_exception_set=in_set,
        excluded_by_floor=excluded,
        admissible=admissible,
        beyond_table=beyond,
        status=status,
    )


def finance_chart_rows() -> tuple[dict[str, Any], ...]:
    """Cached parity n_max(L) for the finance chart (L ≤ 400)."""

    return tuple(
        {
            "L": row["L"],
            "n_max": row["n_max"],
            "record": row["record"],
        }
        for row in _finance_table(FINANCE_CHART_L_MAX)
    )


@dataclass(frozen=True)
class WalkKillRow:
    length: int
    odd_count: int
    required_improvement: float
    kill_margin: float | None
    excluded: bool
    status: str


@lru_cache(maxsize=1)
def lab_walk_survey() -> dict[str, Any]:
    """Theorem 5.9 survey at the laboratory floor 26254995."""

    return json.loads((WALK_DATA_DIR / "survey.json").read_text(encoding="utf-8"))


@lru_cache(maxsize=1)
def printed_floor_leftovers() -> tuple[dict[str, Any], ...]:
    payload = json.loads(
        (WALK_DATA_DIR / "new_floor_parity_leftovers.json").read_text(
            encoding="utf-8"
        )
    )
    if int(payload["floor"]) != PRINTED_FLOOR:
        raise ValueError("new_floor leftovers are not the Corollary 5.10 floor")
    return tuple(dict(row) for row in payload["leftovers"])


@lru_cache(maxsize=1)
def printed_floor_kills() -> dict[int, dict[str, Any]]:
    kills: dict[int, dict[str, Any]] = {}
    for path in (WALK_DATA_DIR / "new_floor_kills").glob("L*.json"):
        row = json.loads(path.read_text(encoding="utf-8"))
        kills[int(row["length"])] = row
    return kills


def printed_floor_kill_rows() -> tuple[WalkKillRow, ...]:
    """Corollary 5.10 leftovers joined to the certified kill records."""

    kills = printed_floor_kills()
    rows: list[WalkKillRow] = []
    for leftover in printed_floor_leftovers():
        length = int(leftover["L"])
        kill = kills.get(length)
        if kill is not None:
            excluded = bool(kill["certified_excludes"])
            margin = float(kill["kill_margin"])
            if excluded:
                status = "walk-killed"
            elif length == PRINTED_PERIOD:
                status = "blocker"
            else:
                status = "finance survivor"
            rows.append(
                WalkKillRow(
                    length=length,
                    odd_count=int(leftover["o"]),
                    required_improvement=float(leftover["required_improvement"]),
                    kill_margin=margin,
                    excluded=excluded,
                    status=status,
                )
            )
            continue
        rows.append(
            WalkKillRow(
                length=length,
                odd_count=int(leftover["o"]),
                required_improvement=float(leftover["required_improvement"]),
                kill_margin=None,
                excluded=False,
                status="beyond printed cutoff",
            )
        )
    return tuple(rows)


def parse_word(raw: str) -> str | None:
    """Return a canonical O/E word, or None if the spelling is invalid."""

    word = "".join(raw.split()).upper()
    if len(word) > WORD_MAX:
        return None
    if word and any(letter not in {"O", "E"} for letter in word):
        return None
    return word


def parse_cycle_word(raw: str) -> str | None:
    """Return a canonical O/E cycle word, allowing the two-even lengths."""

    word = "".join(raw.split()).upper()
    if len(word) > CYCLE_WORD_MAX:
        return None
    if word and any(letter not in {"O", "E"} for letter in word):
        return None
    return word


def rotate_cycle_word(word: str, shift: int = 1) -> str:
    """Rotate `word` left by `shift` letters."""

    if not word:
        return word
    step = shift % len(word)
    return word[step:] + word[:step]


def cycle_rotations(word: str) -> tuple[str, ...]:
    if not word:
        return ("",)
    return tuple(rotate_cycle_word(word, index) for index in range(len(word)))


def two_even_family(word: str) -> str | None:
    length = len(word)
    if length < 6:
        return None
    if word == "O" * (length - 2) + "EE":
        return "EE"
    if word == "O" * (length - 3) + "EOE":
        return "EOE"
    return None


def two_even_bootstrap_kind(word: str) -> tuple[str, str] | None:
    """Name an internal-E next-square two-even spelling, or None."""

    suffix = suffix_after_last_internal_e(word)
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    if threshold is None:
        return None
    if not cyclemin_orientation(word)["legal_cyclemin"]:
        return None
    name, n0 = threshold
    return (
        "bootstrap",
        f"internal E plus {suffix} next-square ({name} at N={n0}); "
        "not a leftover cell",
    )


def leftover_family_kind(word: str) -> tuple[str, str] | None:
    """Name a recorded leftover family, or None if the spelling is not one."""

    three = _THREE_EVEN_RE.fullmatch(word)
    if three:
        a0, a1, a2 = (len(group) for group in three.groups())
        if a0 < 2:
            return None
        if a2 >= 2:
            return (
                "bootstrap",
                f"last odd-run {a2} is the OO/OOO bootstrap of Theorem 3.21",
            )
        if a2 == 0 and a1 >= GAPPED_EE_MIN:
            return (
                "gapped leftover",
                f"O^{a0}EO^{a1}EE is a CycleWord exclusion (Theorem 3.21)",
            )
        if a2 == 1 and a1 >= GAPPED_EOE_MIN:
            return (
                "gapped leftover",
                f"O^{a0}EO^{a1}EOE is a CycleWord exclusion (Theorem 3.21)",
            )
        meta = _BUNCHED_META.get((a1, a2))
        if meta is not None and a0 >= int(meta["a_min"]):
            name = str(meta["name"])
            return (
                "bunched leftover",
                f"O^{a0}{name} is excluded (Theorems 3.14–3.20)",
            )
        return None
    four = _FOUR_EVEN_RE.fullmatch(word)
    if four:
        a0, a1, a2, a3 = (len(group) for group in four.groups())
        if a0 < 2 or a3 not in {0, 1}:
            return None
        slice_kind = classify_leftover(a0, a1, a2, a3)
        family = FAMILY_NAME.get((a2, a3), "last cluster")
        if slice_kind == "gapped_last_cluster":
            return (
                "four-even gapped",
                f"last cluster of {family} is Theorem 3.13 as CycleMin",
            )
        if slice_kind == "bunched_remainder":
            return (
                "four-even bunched",
                f"first-E of bunched {family} at y (Theorems 3.14–3.20)",
            )
        return (
            "four-even short-gap",
            "short first gap: a laboratory leftover spelling; "
            "period 11 is excluded by finance at the verified descent floor",
        )
    return None


@lru_cache(maxsize=1)
def length11_inventory() -> tuple[dict[str, Any], ...]:
    rows = []
    for shape in remainder_shapes():
        a0 = int(shape["first_expanding_a0"])
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        word = word_e4(a0, a1, a2, a3)
        rows.append(
            {
                "word": word,
                "family": shape["family"],
                "a0": a0,
                "a1": a1,
                "kind": shape["kind"],
                "Z4 at first expanding": "misses n≤800",
                "toolkit": "closed",
            }
        )
    return tuple(rows)


def length_eight_status_rows() -> tuple[dict[str, str], ...]:
    notes = {
        "odd_run": "odd-run O^7E; laboratory census ≤ 8",
        "two_even_ee": "Theorem 3.12 two-even EE",
        "two_even_eoe": "Theorem 3.12 two-even EOE",
        "bootstrap_oo_suffix_threshold": "internal E plus OO next-square; not a leftover",
        "bootstrap_ooo_suffix_threshold": "internal E plus OOO next-square; not a leftover",
        "bootstrap_odd_run_suffix_threshold": "internal E plus O^4 odd-run threshold",
        "cycleMin_not_odd_even": "starts OE; rotates onto OOOOOEOE",
        "rotate_start_even": "starts even; rotates onto OOOOOOEE",
    }
    rows = []
    for word in length_eight_open_words():
        named = named_length8_filter(word)
        rows.append(
            {
                "word": word,
                "status": "census ≤ 8",
                "note": notes.get(named, named),
            }
        )
    return tuple(rows)


def format_int(value: int) -> str:
    text = str(value)
    if len(text) <= 18:
        return text
    return f"{text[:6]}…{text[-4:]} ({len(text)} digits)"


def _pow_bits(base: int, exp: int) -> int:
    if exp <= 0 or base <= 1:
        return 1
    return max(1, abs(base).bit_length() * exp)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** odd_count(word)


def length_eight_open_words() -> tuple[str, ...]:
    found: list[str] = []
    for prefix in product("OE", repeat=7):
        word = "".join(prefix) + "E"
        if expanding(word):
            found.append(word)
    return tuple(found)


@dataclass(frozen=True)
class TrajectoryView:
    n: int
    steps_asked: int
    states: tuple[int, ...]
    word: str
    reached_one: bool
    bit_capped: bool
    too_large: bool
    rows: tuple[dict[str, Any], ...]


def walk_trajectory(n: int, steps: int) -> TrajectoryView:
    if n < 1:
        raise ValueError("walk_trajectory requires n ≥ 1")
    cap = min(max(steps, 0), TRAJECTORY_STEPS_MAX)
    if n.bit_length() > DISPLAY_BITS_MAX:
        return TrajectoryView(
            n=n,
            steps_asked=cap,
            states=(n,),
            word="",
            reached_one=n == 1,
            bit_capped=True,
            too_large=True,
            rows=({"step": 0, "state": n, "letter": "", "parity": "odd" if n % 2 else "even", "bits": n.bit_length()},),
        )
    path = [n]
    letters: list[str] = []
    bit_capped = False
    current = n
    for _ in range(cap):
        if current.bit_length() > DISPLAY_BITS_MAX:
            bit_capped = True
            break
        letter = "O" if current % 2 else "E"
        nxt = floor_power(current)
        if nxt.bit_length() > DISPLAY_BITS_MAX:
            bit_capped = True
            letters.append(letter)
            path.append(nxt)
            break
        letters.append(letter)
        path.append(nxt)
        current = nxt
        if current == 1:
            break
    rows = []
    for index, state in enumerate(path):
        letter = letters[index] if index < len(letters) else ""
        rows.append(
            {
                "step": index,
                "state": state,
                "letter": letter,
                "parity": "odd" if state % 2 else "even",
                "bits": state.bit_length(),
            }
        )
    return TrajectoryView(
        n=n,
        steps_asked=cap,
        states=tuple(path),
        word="".join(letters),
        reached_one=path[-1] == 1,
        bit_capped=bit_capped,
        too_large=False,
        rows=tuple(rows),
    )


@dataclass(frozen=True)
class EnvelopeView:
    n: int
    word: str
    odd: int
    length: int
    regime: str
    follows: bool
    fail_index: int | None
    fail_state: int | None
    image: int | None
    compared: str
    slack: int | None
    slack_too_large: bool
    delta: int | None
    delta_too_large: bool
    monochrome: bool
    vanishing: str
    steps: tuple[dict[str, Any], ...]


def _defect_steps(n: int, word: str) -> tuple[tuple[dict[str, Any], ...], int | None, bool]:
    current = n
    running = 0
    ok = True
    rows: list[dict[str, Any]] = []
    for index, letter in enumerate(word):
        parity_ok = (letter == "O" and current % 2 == 1) or (
            letter == "E" and current % 2 == 0
        )
        rho = local_defect(current) if parity_ok else None
        nxt = floor_power(current) if parity_ok else None
        d_out: int | None = None
        if parity_ok and ok and nxt is not None and rho is not None:
            exp = 2**index
            if letter == "E":
                if _pow_bits(nxt * nxt + rho, exp) > DEFECT_BITS:
                    ok = False
                else:
                    running = running + pow_gap(nxt * nxt, rho, exp)
                    d_out = running
            else:
                if (
                    _pow_bits(nxt * nxt + rho, exp) > DEFECT_BITS
                    or _pow_bits(current, exp) > DEFECT_BITS
                ):
                    ok = False
                else:
                    lifted = current**exp
                    running = pow_gap(nxt * nxt, rho, exp) + pow_gap(lifted, running, 3)
                    d_out = running
        rows.append(
            {
                "index": index,
                "state": current,
                "letter": letter,
                "parity_ok": parity_ok,
                "rho": rho,
                "image": nxt,
                "D": d_out if parity_ok else None,
            }
        )
        if not parity_ok:
            break
        assert nxt is not None
        current = nxt
    delta = running if ok and (not word or rows[-1]["parity_ok"]) else None
    return tuple(rows), delta, not ok


def envelope_view(n: int, word: str) -> EnvelopeView:
    if n < 1:
        raise ValueError("envelope_view requires n ≥ 1")
    parsed = parse_word(word)
    if parsed is None:
        raise ValueError("envelope_view requires an O/E word of length ≤ 8")
    word = parsed
    odds = odd_count(word)
    follows = follows_itinerary(n, word) if word else True
    fail_index = None
    fail_state = None
    if word and not follows:
        failed = next((row for row in orbit_until_fail(n, word) if not row["parity_ok"]), None)
        if failed is not None:
            fail_index = int(failed["index"])
            fail_state = int(failed["state"])
    image = image_after(n, word) if follows else None
    compared = "—"
    if image is not None:
        if image < n:
            compared = "<"
        elif image > n:
            compared = ">"
        else:
            compared = "="
    slack = None
    slack_too_large = False
    if image is not None:
        slack = tiny_deficit(n, image, len(word), odds, bit_limit=DEFECT_BITS)
        slack_too_large = slack is None
    steps, delta, delta_too_large = _defect_steps(n, word) if follows else ((), None, False)
    if follows and word and delta is None and not delta_too_large:
        delta_too_large = slack_too_large
    mixed = bool(word) and not is_monochrome(word)
    if not follows:
        vanishing = "word not realized"
    elif not word:
        vanishing = "empty word, Δ = 0"
    elif mixed:
        vanishing = "mixed word, Δ > 0"
    elif delta == 0:
        vanishing = "monochrome tower, Δ = 0"
    elif any(row["rho"] for row in steps):
        vanishing = "monochrome but a local remainder is positive"
    else:
        vanishing = "monochrome; Δ not instantiated"
    return EnvelopeView(
        n=n,
        word=word,
        odd=odds,
        length=len(word),
        regime=regime_of(len(word), odds) if word else "empty",
        follows=follows,
        fail_index=fail_index,
        fail_state=fail_state,
        image=image,
        compared=compared,
        slack=slack,
        slack_too_large=slack_too_large,
        delta=delta,
        delta_too_large=delta_too_large,
        monochrome=is_monochrome(word),
        vanishing=vanishing,
        steps=steps,
    )


@dataclass(frozen=True)
class ComposeView:
    n: int
    u: str
    v: str
    follows: bool
    mid: int | None
    end: int | None
    delta_u: int | None
    delta_v: int | None
    delta_uv: int | None
    composed: int | None
    too_large: bool


def compose_view(n: int, u: str, v: str) -> ComposeView:
    if n < 1:
        raise ValueError("compose_view requires n ≥ 1")
    left = parse_word(u)
    right = parse_word(v)
    if left is None or right is None:
        raise ValueError("compose_view requires O/E factors of total length ≤ 8")
    if len(left) + len(right) > WORD_MAX:
        raise ValueError("compose_view requires |uv| ≤ 8")
    word = left + right
    follows = follows_itinerary(n, word) if word else True
    if not follows:
        return ComposeView(n, left, right, False, None, None, None, None, None, None, False)
    mid = image_after(n, left) if left else n
    end = image_after(mid, right) if right else mid
    slack_u = tiny_deficit(n, mid, len(left), odd_count(left), bit_limit=DEFECT_BITS)
    slack_v = tiny_deficit(mid, end, len(right), odd_count(right), bit_limit=DEFECT_BITS)
    slack_uv = tiny_deficit(n, end, len(word), odd_count(word), bit_limit=DEFECT_BITS)
    too_large = slack_u is None or slack_v is None or slack_uv is None
    composed = None
    if not too_large:
        u_bits = _pow_bits(mid, 2 ** len(left)) if left else 1
        v_bits = _pow_bits(end, 2 ** len(right)) if right else 1
        if u_bits <= DEFECT_BITS and v_bits <= DEFECT_BITS:
            composed = compose_formula(n, left, right)
    return ComposeView(
        n=n,
        u=left,
        v=right,
        follows=True,
        mid=mid,
        end=end,
        delta_u=slack_u,
        delta_v=slack_v,
        delta_uv=slack_uv,
        composed=composed,
        too_large=too_large,
    )


@dataclass(frozen=True)
class EvenPreimageView:
    q: int
    lo: int
    hi: int
    even_count: int
    evens: tuple[int, ...]
    truncated: bool


def even_preimage_view(q: int) -> EvenPreimageView:
    if q < 0:
        raise ValueError("even_preimage_view requires q ≥ 0")
    lo, hi = even_preimage(q)
    evens = tuple(range(lo + (lo % 2), hi, 2))
    truncated = len(evens) > EVEN_PREIMAGE_LIST_MAX
    shown = evens[:EVEN_PREIMAGE_LIST_MAX] if truncated else evens
    return EvenPreimageView(
        q=q,
        lo=lo,
        hi=hi,
        even_count=len(evens),
        evens=shown,
        truncated=truncated,
    )


@dataclass(frozen=True)
class OddPreimageView:
    m: int
    integers: tuple[int, ...]


def odd_preimage_view(m: int) -> OddPreimageView:
    if m < 0:
        raise ValueError("odd_preimage_view requires m ≥ 0")
    return OddPreimageView(m=m, integers=tuple(odd_preimage_integers(m)))


@dataclass(frozen=True)
class WordClass:
    word: str
    length: int
    odd: int
    expanding: bool
    even_terminating: bool
    kind: str
    reason: str


def classify_word(word: str) -> WordClass:
    parsed = parse_word(word)
    if parsed is None:
        raise ValueError("classify_word requires an O/E word of length ≤ 8")
    word = parsed
    is_exp = expanding(word) if word else False
    even_term = bool(word) and word.endswith("E")
    if not word:
        kind, reason = "empty", "empty word"
    elif not even_term:
        kind, reason = "odd-terminating", "census reduces to an even-terminating rotation"
    elif not is_exp:
        kind, reason = "not expanding", "Theorem 3.2(i): a cycle word is formally expanding"
    elif word in _WORD_CLASS:
        kind, reason = _WORD_CLASS[word]
    elif two_even_family(word) is not None:
        family = two_even_family(word)
        kind, reason = (
            "two-even leftover",
            f"Theorem 3.12 excludes O^*{family} for every k ≥ 6",
        )
    elif two_even_bootstrap_kind(word) is not None:
        kind, reason = two_even_bootstrap_kind(word)
    elif len(word) <= 8:
        kind, reason = "excluded", "laboratory census of length ≤ 8"
    else:
        kind, reason = "open", "length nine is the first open even-terminating expanding length"
    return WordClass(
        word=word,
        length=len(word),
        odd=odd_count(word),
        expanding=is_exp,
        even_terminating=even_term,
        kind=kind,
        reason=reason,
    )


def census_inventory(*, max_len: int = 8) -> tuple[dict[str, Any], ...]:
    rows: list[dict[str, Any]] = []
    for length in range(3, max_len + 1):
        for prefix in product("OE", repeat=length - 1):
            word = "".join(prefix) + "E"
            if not expanding(word):
                continue
            info = classify_word(word)
            rows.append(
                {
                    "word": info.word,
                    "k": info.length,
                    "o": info.odd,
                    "kind": info.kind,
                    "reason": info.reason,
                }
            )
    return tuple(rows)


@dataclass(frozen=True)
class LeftoverTable:
    word: str
    n_lo: int
    n_hi: int
    checked: int
    follows: int
    hits: tuple[int, ...]
    rows: tuple[dict[str, Any], ...]


@lru_cache(maxsize=8)
def leftover_table(word: str, n_hi: int | None = None) -> LeftoverTable:
    parsed = parse_word(word)
    if parsed is None or parsed not in LEFTOVER_CUTOFF:
        raise ValueError("leftover_table requires a note leftover word")
    cutoff = LEFTOVER_CUTOFF[parsed]
    hi = cutoff if n_hi is None else min(n_hi, cutoff, LEFTOVER_REPLAY_MAX)
    summary = cycle_itinerary_hits(parsed, 2, hi)
    rows: list[dict[str, Any]] = []
    for n in range(2, hi):
        ok = follows_itinerary(n, parsed)
        image = image_after(n, parsed) if ok else None
        rows.append(
            {
                "n": n,
                "realized": ok,
                "image": image,
                "returned": bool(ok and image == n),
            }
        )
    return LeftoverTable(
        word=parsed,
        n_lo=2,
        n_hi=hi,
        checked=int(summary["checked"]),
        follows=int(summary["follows"]),
        hits=tuple(summary["hits"]),
        rows=tuple(rows),
    )


@dataclass(frozen=True)
class NextSquareView:
    n: int
    prefix: str
    follows: bool
    image: int | None
    threshold: int
    met: bool | None


def next_square_view(n: int, prefix: str) -> NextSquareView:
    if n < 1:
        raise ValueError("next_square_view requires n ≥ 1")
    parsed = parse_word(prefix)
    if parsed not in {"OO", "OOO"}:
        raise ValueError("next_square_view requires prefix OO or OOO")
    threshold = (n + 1) ** 2
    ok = follows_itinerary(n, parsed)
    image = image_after(n, parsed) if ok else None
    met = None if image is None else image >= threshold
    return NextSquareView(
        n=n,
        prefix=parsed,
        follows=ok,
        image=image,
        threshold=threshold,
        met=met,
    )


@dataclass(frozen=True)
class DescentView:
    n: int
    bucket: str
    certificate: str
    residual: dict[str, Any] | None


def descent_view(n: int) -> DescentView:
    if n < 1:
        raise ValueError("descent_view requires n ≥ 1")
    bucket = coverage_bucket(n)
    if bucket == "EVEN_PROGRESS":
        certificate = "E"
    elif bucket == "OE_PROGRESS":
        certificate = "OE"
    elif bucket == "ODD_ODD":
        certificate = "none of length ≤ 2"
    else:
        certificate = "—"
    residual = first_even_residual(n) if n >= 2 else None
    return DescentView(n=n, bucket=bucket, certificate=certificate, residual=residual)


def descent_window(n_max: int) -> dict[str, int]:
    cap = min(max(n_max, 2), DESCENT_WINDOW_MAX)
    counts = {"EVEN_PROGRESS": 0, "OE_PROGRESS": 0, "ODD_ODD": 0, "EXCLUDED": 0}
    for n in range(2, cap + 1):
        counts[coverage_bucket(n)] += 1
    counts["n_max"] = cap
    return counts


@dataclass(frozen=True)
class ChainStep:
    start: int
    word: str
    image: int
    follows: bool
    matches: bool


def four_block_replay() -> tuple[ChainStep, ...]:
    starts = FOUR_BLOCK["xs"]
    words = FOUR_BLOCK["words"]
    steps: list[ChainStep] = []
    for index, word in enumerate(words):
        start = int(starts[index])
        expected = int(starts[index + 1])
        ok = follows_itinerary(start, word)
        image = image_after(start, word) if ok else -1
        steps.append(
            ChainStep(
                start=start,
                word=word,
                image=image,
                follows=ok,
                matches=ok and image == expected,
            )
        )
    return tuple(steps)


def leftover_words() -> tuple[str, ...]:
    return tuple(LEFTOVER_CUTOFF)


@dataclass(frozen=True)
class ArgumentStep:
    title: str
    body: str
    status: str
    ledger: str | None = None


@dataclass(frozen=True)
class RotationRow:
    shift: int
    word: str
    even_terminating: bool
    expanding: bool
    legal_cyclemin: bool
    blocked_by: str | None
    kind: str
    reason: str
    selected: bool


@dataclass(frozen=True)
class CycleTryView:
    n: int
    word: str
    follows: bool
    fail_index: int | None
    fail_state: int | None
    image: int | None
    returned: bool | None
    bit_capped: bool


@dataclass(frozen=True)
class CycleClassView:
    word: str
    current: str
    shift: int
    length: int
    odd: int
    even: int
    expanding: bool
    verdict: str
    verdict_reason: str
    ledger: str | None
    steps: tuple[ArgumentStep, ...]
    rotations: tuple[RotationRow, ...]
    legal_reps: tuple[str, ...]
    current_kind: str
    current_reason: str
    current_legal: bool
    current_blocked_by: str | None


def _is_odd_run(word: str) -> bool:
    return (
        len(word) >= 4
        and word.endswith("E")
        and word[:-1] == "O" * (len(word) - 1)
    )


def _orientation_ledger(kind: str, word: str) -> str | None:
    if kind in {"all-odd", "all-even", "not expanding", "odd-terminating"}:
        return "J-cycle-finite-structure"
    if kind == "odd-run":
        return "J-small-cycle-census-seven" if len(word) <= 7 else "J-cycle-finite-structure"
    if kind == "leftover":
        if word in {"OOOEOE", "OOOOEE"}:
            return "J-leftover-length-six-orientations"
        if word in {"OOOOEOE", "OOOOOEE"}:
            return "J-leftover-length-seven-orientations"
        return "J-small-cycle-census-seven"
    if kind == "two-even leftover":
        return "J-two-even-leftover-ee" if word.endswith("EE") else "J-two-even-leftover-eoe"
    if kind == "three-even leftover":
        return "J-leftover-ooooooeee"
    if kind == "gapped leftover":
        return "J-gapped-cycle-word-eoe" if word.endswith("OE") else "J-gapped-cycle-word-ee"
    if kind == "bunched leftover":
        three = _THREE_EVEN_RE.fullmatch(word)
        if three:
            _a0, a1, a2 = (len(group) for group in three.groups())
            meta = _BUNCHED_META.get((a1, a2))
            if meta is not None:
                return _BUNCHED_LEDGER.get(str(meta["name"]))
        return "J-three-even-eee"
    if kind == "four-even gapped":
        return "J-first-e-transport-eoe" if word.endswith("OE") else "J-first-e-transport-ee"
    if kind == "four-even bunched":
        four = _FOUR_EVEN_RE.fullmatch(word)
        if four:
            _a0, _a1, a2, a3 = (len(group) for group in four.groups())
            name = FAMILY_NAME.get((a2, a3))
            if name is not None:
                return _BUNCHED_LEDGER.get(name)
        return "J-three-even-eee"
    if kind in {"threshold", "bootstrap", "rotation", "excluded", "not CycleMin"}:
        if len(word) <= 7:
            return "J-small-cycle-census-seven"
        if len(word) <= 8:
            return "J-small-cycle-census-eight"
        return "J-cycle-finite-structure"
    return None


def _base_kind(word: str) -> tuple[str, str]:
    """Classify one spelling without chasing a rotation target."""

    if not word:
        return "empty", "empty word"
    if all(letter == "O" for letter in word):
        return "all-odd", "an all-odd word is a strict ascent and cannot close"
    if all(letter == "E" for letter in word):
        return "all-even", "Theorem 3.2(i): a cycle word is formally expanding"
    if not expanding(word):
        return "not expanding", "Theorem 3.2(i): a cycle word is formally expanding"
    if not word.endswith("E"):
        return "odd-terminating", "census reduces to an even-terminating rotation"
    if _is_odd_run(word):
        odds = len(word) - 1
        return "odd-run", f"no_cycle_odd_run_append_even for O^{odds}E, a ≥ 3"
    if word == THREE_EVEN_LEFTOVER:
        return "three-even leftover", "OOOOOOEEE is excluded (no_cycle_itinerary_ooooooeee)"
    named = _WORD_CLASS.get(word)
    if named is not None and named[0] != "rotation":
        return named
    leftover = leftover_family_kind(word)
    if leftover is not None:
        return leftover
    bootstrap = two_even_bootstrap_kind(word)
    if bootstrap is not None:
        return bootstrap
    family = two_even_family(word)
    if family == "EE":
        return (
            "two-even leftover",
            f"O^{len(word) - 2}EE is excluded for every k ≥ 6 "
            "(no_cycle_itinerary_two_even_ee)",
        )
    if family == "EOE":
        return (
            "two-even leftover",
            f"O^{len(word) - 3}EOE is excluded for every k ≥ 6 "
            "(no_cycle_itinerary_two_even_eoe)",
        )
    if word.startswith("E"):
        return "rotation", "rotate the leading evens onto an even-terminating spelling"
    if word.startswith("OE"):
        return "not CycleMin", "cycleMin_not_odd_even"
    if named is not None:
        return named
    if len(word) <= 8:
        return "excluded", "laboratory census of length ≤ 8"
    return "open", "not excluded by the recorded census"


def _preferred_target(word: str) -> str | None:
    named: list[str] = []
    legal: list[str] = []
    even_term: list[str] = []
    for rotated in cycle_rotations(word):
        kind, _reason = _base_kind(rotated)
        if rotated.endswith("E") and kind in _EXCLUDING_KINDS:
            named.append(rotated)
        if rotated and cyclemin_orientation(rotated)["legal_cyclemin"] and expanding(rotated):
            legal.append(rotated)
        if rotated.endswith("E"):
            even_term.append(rotated)
    if named:
        return named[0]
    if legal:
        return legal[0]
    if even_term:
        return even_term[0]
    return None


def _with_target(kind: str, reason: str, word: str) -> tuple[str, str]:
    if kind not in {"odd-terminating", "rotation", "not CycleMin"}:
        return kind, reason
    target = _preferred_target(word)
    if not target or target == word:
        return kind, reason
    if kind == "odd-terminating":
        return kind, f"rotate onto the even-terminating spelling {target}"
    if kind == "rotation":
        return kind, f"rotates onto {target}"
    return kind, f"cycleMin_not_odd_even; the even-terminating target is {target}"


def _orientation_kind(word: str) -> tuple[str, str]:
    kind, reason = _base_kind(word)
    return _with_target(kind, reason, word)


def orientation_obstruction(word: str) -> tuple[str, str, str | None]:
    parsed = parse_cycle_word(word)
    if parsed is None:
        raise ValueError("orientation_obstruction requires an O/E word of length ≤ 16")
    kind, reason = _orientation_kind(parsed)
    return kind, reason, _orientation_ledger(kind, parsed)


def try_cycle_word(n: int, word: str) -> CycleTryView:
    if n < 1:
        raise ValueError("try_cycle_word requires n ≥ 1")
    parsed = parse_cycle_word(word)
    if parsed is None:
        raise ValueError("try_cycle_word requires an O/E word of length ≤ 16")
    if n.bit_length() > DISPLAY_BITS_MAX:
        return CycleTryView(n, parsed, False, None, None, None, None, True)
    current = n
    for index, letter in enumerate(parsed):
        if current.bit_length() > DISPLAY_BITS_MAX:
            return CycleTryView(n, parsed, False, index, current, None, None, True)
        parity_ok = (letter == "O" and current % 2 == 1) or (
            letter == "E" and current % 2 == 0
        )
        if not parity_ok:
            return CycleTryView(n, parsed, False, index, current, None, None, False)
        nxt = floor_power(current)
        if nxt.bit_length() > DISPLAY_BITS_MAX:
            return CycleTryView(n, parsed, False, index, current, None, None, True)
        current = nxt
    return CycleTryView(
        n=n,
        word=parsed,
        follows=True,
        fail_index=None,
        fail_state=None,
        image=current,
        returned=bool(parsed) and current == n,
        bit_capped=False,
    )


def _class_verdict(
    word: str,
    legal: tuple[str, ...],
) -> tuple[str, str, str | None]:
    if not word:
        return "empty", "empty word", None
    kind, reason = _orientation_kind(word)
    if kind in {"all-odd", "all-even", "not expanding"}:
        return "excluded", reason, _orientation_ledger(kind, word)
    if not legal:
        return (
            "excluded",
            "no legal CycleMin orientation exists in this rotation class",
            "J-cycle-finite-structure",
        )
    open_reps = []
    excluded_reps = []
    for rep in legal:
        rep_kind, rep_reason = _orientation_kind(rep)
        if rep_kind == "open":
            open_reps.append((rep, rep_reason))
        elif rep_kind in _EXCLUDING_KINDS:
            excluded_reps.append((rep, rep_kind, rep_reason))
        else:
            open_reps.append((rep, rep_reason))
    if open_reps:
        sample, _sample_reason = open_reps[0]
        leftover = leftover_family_kind(sample)
        evens = word.count("E")
        if evens < 4:
            return (
                "excluded",
                "Theorem 3.22: a nontrivial cycle word has at least four even letters",
                "J-even-count-le-three",
            )
        if len(word) <= PAPER_PERIOD - 1:
            extra = ""
            if leftover is not None and leftover[0] == "four-even short-gap":
                extra = " The local leftover cells miss this spelling, but "
            return (
                "excluded",
                f"{extra}Theorem 4.6: the parity table at the verified "
                f"descent floor 10^6 excludes every period at most "
                f"{PAPER_PERIOD - 1} (this length is {len(word)}).",
                "J-cycle-word-eliahou-leftover-instance",
            )
        if leftover is not None and leftover[0] == "four-even short-gap":
            return "open", leftover[1], None
        return (
            "open",
            f"{sample} is a legal CycleMin spelling that Lean does not exclude",
            None,
        )
    if not excluded_reps:
        return "open", "not excluded by the recorded census", None
    first = excluded_reps[0]
    return "excluded", first[2], _orientation_ledger(first[1], first[0])


def cycle_class_view(word: str, shift: int = 0) -> CycleClassView:
    parsed = parse_cycle_word(word)
    if parsed is None:
        raise ValueError("cycle_class_view requires an O/E word of length ≤ 16")
    word = parsed
    current = rotate_cycle_word(word, shift) if word else ""
    current_kind, current_reason = _orientation_kind(current)
    current_orient = (
        cyclemin_orientation(current)
        if current
        else {
            "legal_cyclemin": False,
            "blocked_by": None,
        }
    )
    rows: list[RotationRow] = []
    legal: list[str] = []
    for index, rotated in enumerate(cycle_rotations(word)):
        kind, reason = _orientation_kind(rotated)
        orientation = (
            cyclemin_orientation(rotated)
            if rotated
            else {"legal_cyclemin": False, "blocked_by": None}
        )
        if orientation["legal_cyclemin"] and expanding(rotated):
            legal.append(rotated)
        rows.append(
            RotationRow(
                shift=index,
                word=rotated,
                even_terminating=bool(rotated) and rotated.endswith("E"),
                expanding=expanding(rotated) if rotated else False,
                legal_cyclemin=bool(orientation["legal_cyclemin"]),
                blocked_by=orientation["blocked_by"],
                kind=kind,
                reason=reason,
                selected=rotated == current,
            )
        )
    legal_reps = tuple(dict.fromkeys(legal))
    verdict, verdict_reason, ledger = _class_verdict(word, legal_reps)
    odds = odd_count(word)
    evens = word.count("E")
    is_exp = expanding(word) if word else False
    mixed = bool(word) and not (odds in {0, len(word)})
    even_term_reps = tuple(row.word for row in rows if row.even_terminating)
    steps = (
        ArgumentStep(
            title="Formal expansion",
            body=(
                f"2^{len(word)} = {2 ** len(word)} compared with "
                f"3^{odds} = {3 ** odds}. A nontrivial cycle word is "
                "formally expanding."
                if word
                else "Enter a nonempty word."
            ),
            status="blocks" if word and not is_exp else "ok" if word else "info",
            ledger="J-cycle-finite-structure" if word and not is_exp else None,
        ),
        ArgumentStep(
            title="Mixed word",
            body=(
                "An all-odd word is a strict ascent and cannot return. "
                "An all-even word is not expanding. A cycle word is mixed."
                if word
                else "Empty word."
            ),
            status=(
                "blocks"
                if word and not mixed
                else "ok"
                if mixed
                else "info"
            ),
            ledger="J-cycle-finite-structure" if word and not mixed else None,
        ),
        ArgumentStep(
            title="Rotate to even-terminating",
            body=(
                "Cycle words are cyclic: if n follows w and returns, every "
                "rotation is a cycle word at a rotated start. The even-"
                f"terminating spellings are {', '.join(even_term_reps) or '—'}."
            ),
            status="ok" if even_term_reps else "info",
            ledger="J-cycle-finite-structure",
        ),
        ArgumentStep(
            title="CycleMin filter",
            body=(
                "A cycle-minimum orientation cannot start even, start OE, "
                "or end odd. Legal CycleMin spellings in this class: "
                f"{', '.join(legal_reps) or 'none'}."
            ),
            status="blocks" if word and mixed and is_exp and not legal_reps else "ok",
            ledger="J-cycle-finite-structure",
        ),
        ArgumentStep(
            title="Even-count",
            body=(
                f"This word has {evens} even letter(s). Theorem 3.22: a "
                "nontrivial cycle word has at least four even letters, so "
                "the period is at least eleven."
            ),
            status="blocks" if word and evens < 4 else "ok" if word else "info",
            ledger="J-even-count-le-three" if word and evens < 4 else None,
        ),
        ArgumentStep(
            title="Finance at the verified descent floor",
            body=(
                f"Length {len(word)}. Theorem 4.6: the parity table plus "
                f"the floor {PAPER_FLOOR:,} excludes every period at most "
                f"{PAPER_PERIOD - 1}. The first length not excluded is "
                f"{PAPER_PERIOD}."
            ),
            status=(
                "blocks"
                if word and len(word) <= PAPER_PERIOD - 1
                else "ok"
                if word
                else "info"
            ),
            ledger=(
                "J-cycle-word-eliahou-leftover-instance"
                if word and len(word) <= PAPER_PERIOD - 1
                else None
            ),
        ),
        ArgumentStep(
            title="Named obstruction",
            body=verdict_reason,
            status="blocks" if verdict == "excluded" else "open" if verdict == "open" else "info",
            ledger=ledger,
        ),
    )
    return CycleClassView(
        word=word,
        current=current,
        shift=(shift % len(word)) if word else 0,
        length=len(word),
        odd=odds,
        even=evens,
        expanding=is_exp,
        verdict=verdict,
        verdict_reason=verdict_reason,
        ledger=ledger,
        steps=steps,
        rotations=tuple(rows),
        legal_reps=legal_reps,
        current_kind=current_kind,
        current_reason=current_reason,
        current_legal=bool(current_orient["legal_cyclemin"]),
        current_blocked_by=current_orient["blocked_by"],
    )
