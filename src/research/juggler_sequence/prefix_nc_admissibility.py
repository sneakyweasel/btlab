"""Backward arithmetic admissibility of mixed prefix-NC Juggler words.

Not a Research Engine control-layer experiment. Not a halt theorem.
Asks whether exact floor-cell pullback empties, shrinks, or structures
the realizing set of a mixed prefix-noncontracting word. ResidualStep
is not extended. A search-horizon emptiness is not a bound L.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import (
    follows_itinerary,
    formal_gap,
    image_after,
)
from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
    tiny_deficit,
)
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import (
    exponent_gap,
    prefix_nc_words,
    prefix_noncontracting,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary, odd_count, word_of
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    RESIDUALS,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_nc_admissibility.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_nc_admissibility.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "PrefixNCAdmissibility.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "prefix_nc_admissibility"

CLASS_GREEN = "PREFIX_NC_ADMISSIBILITY_GREEN"
CLASS_SHRINKS = "PREFIX_NC_ESCAPE_SET_SHRINKS"
CLASS_NEAR = "PREFIX_NC_NEAR_EXTREMAL_GREEN"
CLASS_COUNTER = "PREFIX_NC_COUNTEREXAMPLE"
CLASS_COMPLEX = "PREFIX_NC_ARITHMETIC_COMPLEX"
CLASS_INCOMPLETE = "PREFIX_NC_ADMISSIBILITY_INCOMPLETE"

K_COMB = 8
IMAGE_CAP = 24
FORWARD_N_MAX = 800
INTERVAL_CAP = 800
CUBE_CAP = 4000
BIT_LIMIT = 80
CHAIN_CAP = 8
ALGORITHM_VERSION = "prefix-nc-admissibility-v1"
SEARCH_ID = "prefix-nc-admissibility-phase0"

KNOWN_WITNESSES = (
    ("OOE", 5),
    ("OOOOEE", 271),
    ("OOOOEOOOEE", 37),
    ("OOEOOOOOOO", 173),
    ("OOOOEOEOOO", 103),
    ("OOOEOOOOOE", 113),
    ("OOOOOOEOEE", 163),
    ("OOOOEOOOOEE", 2127),
)
IMAGE_BIT_CAP = 40

FORBIDDEN_ENGINES = (
    "CycleEngine",
    "ResidualGraph",
    "RemainderDynamics",
    "PowerHeight",
    "ResidualStep",
)

FLOOR_LEMMAS = (
    "floor_sqrt_eq_iff_sq_interval",
    "floorPower_even_eq_iff_sq_interval",
    "floorPower_odd_eq_iff_cube_interval",
    "odd_preimage_unique",
    "power_bound_compensated_contracts",
)


class Ival:
    __slots__ = ("lo", "hi", "parity")

    def __init__(self, lo: int, hi: int, parity: int | None) -> None:
        self.lo = lo
        self.hi = hi
        self.parity = parity

    def count(self) -> int:
        if self.lo > self.hi:
            return 0
        if self.parity is None:
            return self.hi - self.lo + 1
        first = self.lo if self.lo % 2 == self.parity else self.lo + 1
        last = self.hi if self.hi % 2 == self.parity else self.hi - 1
        if first > last:
            return 0
        return (last - first) // 2 + 1

    def first(self) -> int | None:
        if self.count() == 0:
            return None
        if self.parity is None:
            return self.lo
        return self.lo if self.lo % 2 == self.parity else self.lo + 1

    def last(self) -> int | None:
        if self.count() == 0:
            return None
        if self.parity is None:
            return self.hi
        return self.hi if self.hi % 2 == self.parity else self.hi - 1

    def to_json(self) -> dict[str, int | None]:
        return {"lo": self.lo, "hi": self.hi, "parity": self.parity}


def merge_ivals(ivals: list[Ival]) -> list[Ival]:
    if not ivals:
        return []
    ordered = sorted(
        (iv for iv in ivals if iv.count() > 0),
        key=lambda iv: (iv.parity is not None, iv.parity if iv.parity is not None else -1, iv.lo),
    )
    out: list[Ival] = []
    for iv in ordered:
        step = 2 if iv.parity is not None else 1
        if out and out[-1].parity == iv.parity and iv.lo <= out[-1].hi + step:
            out[-1].hi = max(out[-1].hi, iv.hi)
        else:
            out.append(Ival(iv.lo, iv.hi, iv.parity))
    return out


def ceil_cbrt(n: int) -> int:
    if n <= 0:
        return 0
    lo = 0
    hi = 1 << ((n.bit_length() + 2) // 3)
    while hi * hi * hi < n:
        hi <<= 1
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < n:
            lo = mid + 1
        else:
            hi = mid
    return lo


def floor_cbrt(n: int) -> int:
    if n < 0:
        raise ValueError("floor_cbrt requires a nonnegative integer")
    if n < 2:
        return n
    lo = 0
    hi = 1 << ((n.bit_length() + 2) // 3)
    while hi * hi * hi < n:
        hi <<= 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def contains_image(ivals: list[Ival], q: int) -> bool:
    for iv in ivals:
        if q < iv.lo or q > iv.hi:
            continue
        if iv.parity is None or q % 2 == iv.parity:
            return True
    return False


def pullback_even(ivals: list[Ival], *, cap: int = INTERVAL_CAP) -> tuple[list[Ival], bool]:
    out: list[Ival] = []
    truncated = False
    for iv in ivals:
        if iv.count() == 0:
            continue
        if iv.parity is None:
            out.append(Ival(iv.lo * iv.lo, (iv.hi + 1) * (iv.hi + 1) - 1, 0))
            continue
        first = iv.first()
        last = iv.last()
        if first is None or last is None:
            continue
        steps = (last - first) // 2 + 1
        if steps > cap:
            truncated = True
            last = first + 2 * (cap - 1)
        q = first
        while q <= last:
            out.append(Ival(q * q, (q + 1) * (q + 1) - 1, 0))
            q += 2
        if len(out) > cap:
            truncated = True
            break
    return merge_ivals(out), truncated


def pullback_odd(ivals: list[Ival], *, cap: int = CUBE_CAP) -> tuple[list[Ival], bool]:
    out: list[Ival] = []
    truncated = False
    for iv in ivals:
        if iv.count() == 0:
            continue
        first = iv.lo
        last = iv.hi
        n_min = ceil_cbrt(first * first)
        n_max = floor_cbrt((last + 1) * (last + 1) - 1)
        if n_min > n_max:
            continue
        if n_max - n_min + 1 > cap:
            truncated = True
            n_max = n_min + cap - 1
        lo_keep: int | None = None
        hi_keep: int | None = None
        for n in range(n_min, n_max + 1):
            if n % 2 == 0:
                continue
            image = floor_power(n)
            if contains_image(ivals, image):
                if lo_keep is None:
                    lo_keep = n
                hi_keep = n
        if lo_keep is not None and hi_keep is not None:
            out.append(Ival(lo_keep, hi_keep, 1))
    return merge_ivals(out), truncated


def pullback_word(
    word: str,
    image: Ival,
    *,
    interval_cap: int = INTERVAL_CAP,
    cube_cap: int = CUBE_CAP,
) -> dict[str, Any]:
    if not word:
        raise ValueError("pullback_word requires a nonempty word")
    ivals = [image]
    truncated = False
    layers: list[dict[str, Any]] = []
    for letter in reversed(word):
        if letter == "E":
            ivals, trunc = pullback_even(ivals, cap=interval_cap)
        elif letter == "O":
            ivals, trunc = pullback_odd(ivals, cap=cube_cap)
        else:
            raise ValueError(f"invalid word letter {letter!r}")
        truncated = truncated or trunc
        measure = sum(iv.count() for iv in ivals)
        layers.append(
            {
                "letter": letter,
                "components": len(ivals),
                "measure": measure,
            }
        )
        if not ivals or truncated:
            break
    measure = sum(iv.count() for iv in ivals)
    minimum = ivals[0].first() if ivals else None
    maximum = ivals[-1].last() if ivals else None
    return {
        "empty": not ivals,
        "truncated": truncated,
        "components": len(ivals),
        "measure": measure,
        "min_start": minimum,
        "max_start": maximum,
        "width": None if minimum is None or maximum is None else maximum - minimum + 1,
        "layers": list(reversed(layers)),
        "unbounded": False,
    }


def drift_profile(word: str) -> list[int]:
    odds = 0
    gaps: list[int] = []
    for index, letter in enumerate(word, start=1):
        if letter == "O":
            odds += 1
        gaps.append(exponent_gap(index, odds))
    return gaps


def extremal_deviation(word: str) -> dict[str, Any]:
    e_count = word.count("E")
    first_e = word.find("E")
    oke = first_e >= 2 and set(word[:first_e]) == {"O"} and set(word[first_e:]) <= {"E"}
    return {
        "e_count": e_count,
        "first_e": first_e,
        "oke_shadow": bool(oke and e_count == 1),
        "oke_then_e": bool(oke and e_count >= 1),
    }


def defect_row(n: int, word: str) -> dict[str, Any] | None:
    if n < 1 or not follows_itinerary(n, word):
        return None
    path = itinerary(n, len(word))
    image = path[-1]
    odds = odd_count(word)
    index = first_nonexact_index(path)
    deficit = tiny_deficit(n, image, len(word), odds, bit_limit=BIT_LIMIT)
    formal = formal_gap(n, len(word), odds, bit_limit=BIT_LIMIT)
    return {
        "n": n,
        "image": image,
        "first_defect_position": index,
        "first_defect": None if index is None else local_defect(path[index]),
        "global_defect": deficit,
        "formal_gap": formal,
        "compensated_contraction": None
        if deficit is None or formal is None
        else deficit > formal,
        "actual_contraction": image < n,
    }


def word_payload(word: str, image: Ival, *, known_n: int | None = None) -> dict[str, Any]:
    back = pullback_word(word, image)
    min_start = None if back["truncated"] else back["min_start"]
    realizable = False
    defect = None
    if known_n is not None and follows_itinerary(known_n, word):
        realizable = True
        defect = defect_row(known_n, word)
        if min_start is None or known_n < min_start:
            min_start = known_n
    elif min_start is not None and follows_itinerary(min_start, word):
        realizable = True
        defect = defect_row(min_start, word)
    return {
        "word": word,
        "length": len(word),
        "odd_count": odd_count(word),
        "prefix_nc": prefix_noncontracting(word),
        "monochrome": is_monochrome(word),
        "prefix_drift_profile": drift_profile(word),
        "exponent_gap": exponent_gap(len(word), odd_count(word)),
        "deviation": extremal_deviation(word),
        "realizable": realizable or (not back["empty"] and not back["truncated"]),
        "minimum_start": min_start,
        "maximum_start_or_unbounded": None if back["truncated"] else back["max_start"],
        "admissibility_width": None if back["truncated"] else back["width"],
        "components": None if back["truncated"] else back["components"],
        "measure": None if back["truncated"] else back["measure"],
        "empty_over_image": back["empty"],
        "truncated": back["truncated"],
        "layers": back["layers"],
        "first_defect": None if defect is None else defect["first_defect"],
        "global_defect": None if defect is None else defect["global_defect"],
        "compensated_contraction": None if defect is None else defect["compensated_contraction"],
        "known_n": known_n,
    }


def mixed_prefix_nc(k_max: int = K_COMB) -> list[str]:
    return [word for word in prefix_nc_words(k_max) if not is_monochrome(word)]


def forward_realized(*, n_max: int = FORWARD_N_MAX, k_max: int = K_COMB) -> dict[str, int]:
    hits: dict[str, int] = {}
    target = set(mixed_prefix_nc(k_max))
    for n in range(2, n_max + 1):
        path = itinerary(n, k_max)
        word = word_of(path)
        for length in range(1, k_max + 1):
            prefix = word[:length]
            if prefix in target and prefix not in hits:
                hits[prefix] = n
        if len(hits) == len(target):
            break
    return hits


def extension_rows(words: list[str], image: Ival) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for word in words:
        if len(word) < 2:
            continue
        parent = word[:-1]
        if is_monochrome(parent) or not prefix_noncontracting(parent):
            continue
        before = pullback_word(parent, image)
        after = pullback_word(word, image)
        if before["truncated"] or after["truncated"]:
            continue
        rows.append(
            {
                "word": word,
                "letter": word[-1],
                "parent_measure": before["measure"],
                "measure": after["measure"],
                "parent_components": before["components"],
                "components": after["components"],
                "parent_empty": before["empty"],
                "empty": after["empty"],
                "widens": after["measure"] > before["measure"],
                "shrinks": after["measure"] < before["measure"],
                "empties": after["empty"] and not before["empty"],
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8")
    combined = floor + residual
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: f"theorem {name}" in floor or f"def {name}" in floor for name in FLOOR_LEMMAS},
        "PrefixNCAdmissibility_absent": not LEAN_NEW.is_file(),
        "no_prefix_nc_admissible": "prefix_nc_admissible" not in floor
        and "prefix_nc_admissible" not in residual,
        "ResidualStep_not_extended": "prefix_nc_admissible" not in residual
        and "escape_admissible" not in residual,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_forbidden_engine": all(
            name not in residual or name == "ResidualStep" for name in FORBIDDEN_ENGINES
        ),
        "no_new_recurrence": "inductive PrefixNC" not in residual
        and "def RemainderDynamics" not in residual,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["PrefixNCAdmissibility_absent"]
        and lean["floorPower_odd_eq_iff_cube_interval"]
        and lean["odd_preimage_unique"]
        and lean["no_global_termination_theorem"]
        and lean["ResidualStep_not_extended"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    census = scan["census"]
    if census["unrealizable_mixed"] and census["empty_law"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a mixed prefix-NC family has empty exact pullback",
        }
    if census["arbitrarily_extendable"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "an explicit extendable arithmetic family survived",
        }
    if census["only_oke_survives"] and census["max_realized_length"] >= 6:
        return {
            "classification": CLASS_NEAR,
            "secondary": [],
            "reason": "long surviving mixed itineraries are O^k E shadows",
        }
    if census["o_shrinks"] and census["e_widens"] and not census["empty_law"]:
        return {
            "classification": CLASS_SHRINKS,
            "reason": (
                "O-pullback thins small-image fibers and E-pullback widens them; "
                "no emptiness law; horizon realizations are not an infinite family"
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": (
            "backward constraints are the existing even/odd cells; "
            "long mixed prefix-NC words remain realizable; "
            f"empty-over-image-{IMAGE_CAP} is not unrealizable; "
            "no jointly preserved obstruction"
        ),
    }


def run_probe() -> dict[str, Any]:
    image = Ival(1, IMAGE_CAP, None)
    mixed = mixed_prefix_nc(K_COMB)
    forward = forward_realized()
    comb_rows = []
    empty_over_image = 0
    truncated = 0
    realized_forward = 0
    oke_only = True
    for word in mixed:
        row = word_payload(word, image, known_n=forward.get(word))
        comb_rows.append(row)
        if row["empty_over_image"]:
            empty_over_image += 1
        if row["truncated"]:
            truncated += 1
        if word in forward:
            realized_forward += 1
            if not row["deviation"]["oke_then_e"]:
                oke_only = False
        elif not row["deviation"]["oke_then_e"]:
            oke_only = False
    extensions = extension_rows([w for w in mixed if len(w) <= 6], image)
    o_shrinks = any(row["shrinks"] and row["letter"] == "O" for row in extensions)
    e_widens = any(row["widens"] and row["letter"] == "E" for row in extensions)
    e_empties = any(row["empties"] and row["letter"] == "E" for row in extensions)
    known = []
    for word, n in KNOWN_WITNESSES:
        if not prefix_noncontracting(word) or is_monochrome(word):
            known.append({"word": word, "skipped": True, "reason": "not mixed prefix-NC"})
            continue
        if n is not None:
            image_n = image_after(n, word)
            if image_n.bit_length() > IMAGE_BIT_CAP:
                fiber = word_payload(word, image, known_n=n)
            else:
                fiber = word_payload(
                    word, Ival(image_n, image_n, image_n % 2), known_n=n
                )
        else:
            fiber = word_payload(word, image, known_n=None)
        known.append(fiber)
    unrealizable = [word for word in mixed if word not in forward]
    census = {
        "mixed_count": len(mixed),
        "k_max": K_COMB,
        "image_cap": IMAGE_CAP,
        "forward_n_max": FORWARD_N_MAX,
        "realized_forward": realized_forward,
        "unrealized_in_forward": len(unrealizable),
        "unrealizable_mixed": False,
        "empty_over_image": empty_over_image,
        "truncated": truncated,
        "empty_law": False,
        "o_shrinks": o_shrinks,
        "e_widens": e_widens,
        "e_empties": e_empties,
        "only_oke_survives": oke_only and realized_forward > 0,
        "realized_horizon": realized_forward > 0,
        "arbitrarily_extendable": False,
        "max_realized_length": max((len(w) for w in forward), default=0),
        "search_horizon_is_not_L": True,
        "unrealized_sample": unrealizable[:12],
    }
    return {
        "k_comb": K_COMB,
        "image_cap": IMAGE_CAP,
        "forward_n_max": FORWARD_N_MAX,
        "combinatorial": comb_rows,
        "extensions": extensions,
        "known": known,
        "forward": forward,
        "census": census,
        "basin": [1],
        "n_search": False,
        "residual_step_extended": False,
        "explicit_L": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["finite_progress_for_all"] = False
    anti["search_horizon_is_L"] = False
    anti["odd_odd_chains_bounded"] = False
    anti["prefix_nc_words_unrealizable"] = False
    anti["scalar_must_grow"] = False
    return {
        "experiment": "juggler_prefix_nc_admissibility",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "backward even/odd floor-cell pullback on mixed prefix-NC "
            f"words k<={K_COMB} with image 1..{IMAGE_CAP}; forward "
            f"realization n<={FORWARD_N_MAX}; known horizon witnesses; "
            "no ResidualStep; no inferred L"
        ),
        "algorithm_version": ALGORITHM_VERSION,
        "search_id": SEARCH_ID,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler prefix-NC arithmetic admissibility",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. A prefix-NC word has every",
        "prefix exponent gap `G_j = 2^j - 3^{o_j} ≤ 0`. The question is",
        "whether exact floor-cell pullback empties the realizing set.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does arithmetic realizability eliminate",
        "                        long mixed prefix-NC words?",
        "Novelty hypothesis      backward floor cells empty or shrink A_NC",
        "Falsifier               existing cells rewritten; horizon ≠ L;",
        "                        realized mixed itineraries survive",
        "Existing machinery      inverse-floor iff, odd_preimage_unique,",
        "                        prefix_nc_words, compensated contraction",
        "Maximum Phase-0 scope   pullback on mixed k<=8 plus known witnesses",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- algorithm: `{payload['algorithm_version']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window",
        "",
        f"- mixed prefix-NC words `k<={census['k_max']}`: `{census['mixed_count']}`",
        f"- realized with `n<={census['forward_n_max']}`: `{census['realized_forward']}`",
        f"- unrealized in that forward window: `{census['unrealized_in_forward']}`",
        f"- empty over images `1..{census['image_cap']}`: `{census['empty_over_image']}`",
        f"- truncated pullbacks: `{census['truncated']}`",
        f"- O-extension shrinks: `{census['o_shrinks']}`",
        f"- E-extension widens: `{census['e_widens']}`",
        f"- only O^k E shadows survive: `{census['only_oke_survives']}`",
        f"- search horizon is not L: `{census['search_horizon_is_not_L']}`",
        "",
        "## Known witnesses",
        "",
    ]
    for row in scan["known"]:
        if row.get("skipped"):
            lines.append(f"- `{row['word']}` skipped: {row.get('reason')}")
            continue
        lines.append(
            f"- `{row['word']}` min=`{row['minimum_start']}` "
            f"empty_over_image=`{row['empty_over_image']}` "
            f"truncated=`{row['truncated']}` "
            f"compensated=`{row['compensated_contraction']}` "
            f"E-count=`{row['deviation']['e_count']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new PrefixNCAdmissibility file absent: `{lean.get('PrefixNCAdmissibility_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "A dangerous finite word is not a dangerous infinite",
            "trajectory. A search-horizon depth is not a bound L.",
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


def search_config() -> dict[str, Any]:
    return {
        "search_id": SEARCH_ID,
        "algorithm_version": ALGORITHM_VERSION,
        "k_comb": K_COMB,
        "image_cap": IMAGE_CAP,
        "forward_n_max": FORWARD_N_MAX,
        "interval_cap": INTERVAL_CAP,
        "cube_cap": CUBE_CAP,
        "arithmetic": "python-int",
    }


def init(data_dir: Path | None = None) -> Path:
    root = DATA_DIR if data_dir is None else data_dir
    (root / "summaries").mkdir(parents=True, exist_ok=True)
    (root / "analysis").mkdir(parents=True, exist_ok=True)
    (root / "words").mkdir(parents=True, exist_ok=True)
    (root / "config.json").write_text(
        json.dumps(search_config(), indent=2) + "\n", encoding="utf-8"
    )
    manifest_path = root / "manifest.json"
    if not manifest_path.is_file():
        manifest_path.write_text(
            json.dumps(
                {
                    "search_id": SEARCH_ID,
                    "algorithm_version": ALGORITHM_VERSION,
                    "completed": False,
                    "git_commit": git_commit(),
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
    readme = root / "README.md"
    if not readme.is_file():
        readme.write_text(
            "# Prefix-NC arithmetic admissibility\n\n"
            "Backward floor-cell pullback of mixed prefix-noncontracting "
            "Juggler words. JSON under `summaries/`, `analysis/`, and "
            "`words/` is the source of truth. A finite empty fiber is "
            "not a bound L and not a termination theorem.\n",
            encoding="utf-8",
        )
    return root


def _write_data_tree(payload: dict[str, Any], root: Path, runtime_ms: int) -> None:
    scan = payload["scan"]
    census = scan["census"]
    phase0 = {
        "search_id": SEARCH_ID,
        "algorithm_version": ALGORITHM_VERSION,
        "decision": payload["decision"],
        "census": census,
        "known": [
            {
                "word": row.get("word"),
                "minimum_start": row.get("minimum_start"),
                "empty_over_image": row.get("empty_over_image"),
                "truncated": row.get("truncated"),
                "compensated_contraction": row.get("compensated_contraction"),
                "skipped": row.get("skipped", False),
            }
            for row in scan["known"]
        ],
        "unrealized_sample": census["unrealized_sample"],
    }
    phase_text = json.dumps(phase0, indent=2) + "\n"
    (root / "summaries" / "phase0.json").write_text(phase_text, encoding="utf-8")
    checksum = hashlib.sha256(phase_text.encode("utf-8")).hexdigest()
    (root / "analysis" / "census.json").write_text(
        json.dumps(census, indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "extensions.json").write_text(
        json.dumps(scan["extensions"], indent=2) + "\n", encoding="utf-8"
    )
    slim = [
        {
            "word": row["word"],
            "length": row["length"],
            "realizable": row["realizable"],
            "minimum_start": row["minimum_start"],
            "empty_over_image": row["empty_over_image"],
            "truncated": row["truncated"],
            "measure": row["measure"],
            "components": row["components"],
            "deviation": row["deviation"],
        }
        for row in scan["combinatorial"]
    ]
    (root / "analysis" / "words_k8.json").write_text(
        json.dumps(slim, indent=2) + "\n", encoding="utf-8"
    )
    words_dir = root / "words"
    for row in scan["known"]:
        if row.get("skipped"):
            continue
        (words_dir / f"{row['word']}.json").write_text(
            json.dumps(row, indent=2) + "\n", encoding="utf-8"
        )
    (root / "summaries" / "summary.md").write_text(render_markdown(payload), encoding="utf-8")
    (root / "config.json").write_text(
        json.dumps(search_config(), indent=2) + "\n", encoding="utf-8"
    )
    (root / "manifest.json").write_text(
        json.dumps(
            {
                "search_id": SEARCH_ID,
                "algorithm_version": ALGORITHM_VERSION,
                "git_commit": git_commit(),
                "k_comb": K_COMB,
                "image_cap": IMAGE_CAP,
                "forward_n_max": FORWARD_N_MAX,
                "completed": True,
                "checksum_sha256": checksum,
                "runtime_ms": runtime_ms,
                "mixed_count": census["mixed_count"],
                "classification": payload["decision"]["classification"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def load_manifest(data_dir: Path | None = None) -> dict[str, Any] | None:
    path = (DATA_DIR if data_dir is None else data_dir) / "manifest.json"
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def run(data_dir: Path | None = None) -> dict[str, Any]:
    root = init(data_dir)
    started = time.perf_counter()
    payload = probe_payload()
    runtime_ms = int((time.perf_counter() - started) * 1000)
    _write_data_tree(payload, root, runtime_ms)
    if root.resolve() == DATA_DIR.resolve():
        write_artifacts(payload)
    return payload


def resume(data_dir: Path | None = None) -> dict[str, Any] | None:
    root = DATA_DIR if data_dir is None else data_dir
    manifest = load_manifest(root)
    phase = root / "summaries" / "phase0.json"
    if manifest and manifest.get("completed") and phase.is_file():
        return None
    return run(root)


def status(data_dir: Path | None = None) -> dict[str, Any]:
    manifest = load_manifest(data_dir)
    if manifest is None:
        return {"completed": False, "reason": "no manifest"}
    return manifest


def summarize(data_dir: Path | None = None) -> dict[str, Any]:
    root = DATA_DIR if data_dir is None else data_dir
    phase = root / "summaries" / "phase0.json"
    if not phase.is_file():
        payload = run(root)
        return payload["decision"]
    payload = write_artifacts()
    (root / "summaries" / "summary.md").write_text(render_markdown(payload), encoding="utf-8")
    return payload["decision"]


def main() -> None:
    parser = argparse.ArgumentParser(description="Prefix-NC arithmetic admissibility probe")
    parser.add_argument(
        "command",
        nargs="?",
        default="run",
        choices=("init", "run", "resume", "status", "summarize"),
    )
    parser.add_argument("--data-dir", type=Path, default=None)
    args = parser.parse_args()
    if args.command == "init":
        print(init(args.data_dir))
        return
    if args.command == "run":
        payload = run(args.data_dir)
        print(payload["decision"]["classification"])
        print(payload["decision"]["reason"])
        return
    if args.command == "resume":
        payload = resume(args.data_dir)
        if payload is None:
            print("already complete")
            return
        print(payload["decision"]["classification"])
        return
    if args.command == "status":
        print(json.dumps(status(args.data_dir), indent=2))
        return
    decision = summarize(args.data_dir)
    print(decision["classification"])


if __name__ == "__main__":
    main()
