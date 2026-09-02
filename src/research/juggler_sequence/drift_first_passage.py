"""Drift-first-passage tree: nested realizing sets of prefix-NC words.

Not a Research Engine control-layer experiment. Not a halt theorem.
Attaches A_w to each actual prefix-NC word and asks whether nested
continuation thins in a named arithmetic way. Word realizability is
not reopened. Endpoint filtration is not reopened. ResidualStep is
not extended. A window-empty child is not A_w empty. A cardinality
drop in a fixed window is tautological, not a pruning rule.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
from collections import defaultdict
from math import gcd
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.drift_crossing import crossing_window
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import (
    exponent_gap,
    prefix_nc_words,
    prefix_noncontracting,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, odd_count
from research.juggler_sequence.prefix_nc_admissibility import Ival, pullback_word
from research.juggler_sequence.lean_paths import (
    CYCLE_DIOPHANTINE,
    ENVELOPE,
    MINIMAL,
    RESIDUALS,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_drift_first_passage.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_drift_first_passage.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "DriftFirstPassage.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
MIN_PATH = MINIMAL
CYCLE_PATH = CYCLE_DIOPHANTINE
PREFIX_PATH = REPO_ROOT / "formal" / "Problems" / "Engine" / "PrefixNc.lean"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "drift_first_passage"

CLASS_PRUNING = "DRIFT_TREE_PRUNING_GREEN"
CLASS_UNBOUNDED = "DRIFT_FIRST_PASSAGE_UNBOUNDED"
CLASS_COMPLEX = "DRIFT_FIRST_PASSAGE_COMPLEX"
CLASS_COUNTER = "DRIFT_FIRST_PASSAGE_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "DRIFT_FIRST_PASSAGE_INCOMPLETE"
CLASS_GREEN = "DRIFT_FIRST_PASSAGE_GREEN"
CLASS_BOUNDED = "DRIFT_FIRST_PASSAGE_BOUNDED"

STATUS_CROSSED = "CROSSED"
STATUS_ABSORBED = "ABSORBED_NC"
STATUS_HORIZON = "HORIZON_EXCEEDED"
STATUS_BIT_CAP = "BIT_CAP"

NESTED_MIN = 2
NESTED_MAX = 2000
HUNT_MIN = 2
HUNT_MAX = 100_000
HORIZON = 10_000
BIT_CAP = 4096
HUNT_BIT_CAP = 2_000_000
PRED_BITS_KEEP = 256
K_PULLBACK = 8
IMAGE_CAP = 24
SAMPLE_CAP = 12
START_KEEP = 24
ALGORITHM_VERSION = "drift-first-passage-v1"
CLASSIFICATION_VERSION = "drift-first-passage-class-v1"
SEARCH_PREFIX = "juggler-drift-first-passage-phase0"
CROSSING_POLICY = "stop at first G_k>0; absorb if T^k=1 still NC"

HARD_STARTS = (9, 37, 49, 69, 77, 173)
TALL_STARTS = (193, 557, 761)
RECORD_STARTS = HARD_STARTS + TALL_STARTS + (1181, 1721, 1773)
KNOWN_RECORD = {
    "n": 193,
    "tau_plus": 70,
    "last_nc": 6498,
    "word": (
        "OOOEOOOOOOOEOOOEEOEEOOOOOOEEEOOOEOOEEOOOOOEOOOOEEOOEOOEOEEOOEOOEEOEEEE"
    ),
}

FORBIDDEN_ENGINES = (
    "CycleEngine",
    "ResidualGraph",
    "RemainderDynamics",
    "PowerHeight",
    "ResidualStep",
    "CycleDiophantine",
)

FLOOR_LEMMAS = (
    "power_bound_word",
    "power_bound_contracts",
    "power_bound_eq_iff_extremal",
    "power_bound_compensated_contracts",
)

RESIDUE_MODULI = (8, 9, 16, 27)


def search_id_for(n_start: int, n_end: int, hunt_end: int) -> str:
    return f"{SEARCH_PREFIX}-n{n_start}-{n_end}-hunt{hunt_end}"


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


def letter_keeps_nc(word: str, letter: str) -> bool:
    """Whether w+letter stays prefix-NC, given that w is prefix-NC or empty."""

    if letter not in ("E", "O"):
        raise ValueError(f"invalid letter {letter!r}")
    if word and not prefix_noncontracting(word):
        return False
    odds = word.count("O") + (1 if letter == "O" else 0)
    return exponent_gap(len(word) + 1, odds) <= 0


def slim_crossing(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    keep_word: bool = True,
) -> dict[str, Any]:
    """Walk until the first positive G_k. No endpoint metrics."""

    if n < 1:
        raise ValueError("slim_crossing requires n >= 1")
    current = n
    odds = 0
    three = 1
    two = 1
    letters: list[str] = []
    last_letter = None
    peak = n
    status = STATUS_HORIZON
    tau = None
    pred = None
    image = None
    crossing_o = None
    crossing_gap = None
    steps = 0

    for _k in range(1, horizon + 1):
        if current.bit_length() > bit_cap:
            status = STATUS_BIT_CAP
            break
        letter = "O" if current % 2 else "E"
        last_letter = letter
        if letter == "O":
            odds += 1
            three *= 3
        two <<= 1
        gap = two - three
        nxt = floor_power(current)
        steps += 1
        if keep_word:
            letters.append(letter)
        if nxt > peak:
            peak = nxt
        if gap > 0:
            status = STATUS_CROSSED
            tau = steps
            pred = current
            image = nxt
            crossing_o = odds
            crossing_gap = gap
            break
        if nxt == 1:
            status = STATUS_ABSORBED
            pred = current
            image = nxt
            crossing_o = odds
            crossing_gap = gap
            break
        current = nxt

    word = "".join(letters) if keep_word else ""
    nc_word = word[:-1] if status == STATUS_CROSSED and word else word
    return {
        "n": n,
        "status": status,
        "tau_plus": tau,
        "word": word,
        "nc_word": nc_word,
        "odd_count": crossing_o if crossing_o is not None else odds,
        "G_tau": crossing_gap,
        "pred": pred if pred is None or pred.bit_length() <= PRED_BITS_KEEP else None,
        "pred_bits": None if pred is None else pred.bit_length(),
        "pred_even": None if pred is None else pred % 2 == 0,
        "image": image if image is None or image.bit_length() <= PRED_BITS_KEEP else None,
        "image_lt_n": None if image is None else image < n,
        "crossing_letter": last_letter,
        "crossing_window": (
            crossing_window(tau, crossing_o)
            if status == STATUS_CROSSED and tau is not None and crossing_o is not None
            else None
        ),
        "peak_bits": peak.bit_length(),
        "prefix_nc_until_pred": prefix_noncontracting(nc_word) if nc_word else True,
    }


def _identity_failure(walked: dict[str, Any]) -> dict[str, Any] | None:
    if walked["status"] != STATUS_CROSSED:
        return None
    tau = walked["tau_plus"]
    letter = walked["crossing_letter"]
    if letter != "E":
        return {"kind": "crossing_letter", "n": walked["n"], "tau": tau, "letter": letter}
    if walked["pred_even"] is not True:
        return {"kind": "pred_odd", "n": walked["n"], "tau": tau}
    if not walked["crossing_window"]:
        return {
            "kind": "crossing_window",
            "n": walked["n"],
            "tau": tau,
            "odd_count": walked["odd_count"],
            "G": walked["G_tau"],
        }
    if walked["image_lt_n"] is not True:
        return {"kind": "image_not_lt", "n": walked["n"], "tau": tau}
    if tau >= 2 and not walked["prefix_nc_until_pred"]:
        return {"kind": "prefix_nc", "n": walked["n"], "word": walked["word"]}
    if tau == 1 and walked["n"] % 2 != 0:
        return {"kind": "odd_tau_one", "n": walked["n"]}
    if walked["n"] % 2 == 0 and tau != 1:
        return {"kind": "even_tau", "n": walked["n"], "tau": tau}
    if walked["G_tau"] == 0:
        return {"kind": "gap_zero", "n": walked["n"], "tau": tau}
    return None


def set_signature(starts: list[int], n_end: int) -> dict[str, Any]:
    """Structural signature of a window-exact realizing set."""

    values = sorted(set(starts))
    if not values:
        return {
            "count": 0,
            "min": None,
            "max": None,
            "density": 0.0,
            "modulus": 0,
            "singleton": False,
            "residues": {str(mod): [] for mod in RESIDUE_MODULI},
            "residue_sizes": {str(mod): 0 for mod in RESIDUE_MODULI},
        }
    modulus = 0
    prev = values[0]
    for item in values[1:]:
        modulus = gcd(modulus, item - prev)
        prev = item
        if modulus == 1:
            break
    residues = {mod: sorted({item % mod for item in values}) for mod in RESIDUE_MODULI}
    span = max(n_end - 1, 1)
    return {
        "count": len(values),
        "min": values[0],
        "max": values[-1],
        "density": len(values) / span,
        "modulus": modulus,
        "singleton": len(values) == 1,
        "residues": {str(mod): residues[mod] for mod in RESIDUE_MODULI},
        "residue_sizes": {str(mod): len(residues[mod]) for mod in RESIDUE_MODULI},
    }


def signature_key(sig: dict[str, Any]) -> tuple[Any, ...]:
    """Hashable structural class, not the identity of the start set."""

    residues = sig.get("residues") or {}
    return (
        sig.get("modulus"),
        bool(sig.get("singleton")),
        tuple((mod, tuple(residues.get(str(mod), []))) for mod in RESIDUE_MODULI),
    )


def extension_tag(parent_sig: dict[str, Any], child_sig: dict[str, Any]) -> str:
    """Classify A_child relative to A_parent. Cardinality drop is not named."""

    if child_sig["count"] == 0:
        return "empty"
    if child_sig["count"] == parent_sig["count"]:
        return "same"
    named = False
    parent_mod = parent_sig.get("modulus") or 0
    child_mod = child_sig.get("modulus") or 0
    if parent_mod > 0 and child_mod > parent_mod and child_mod % parent_mod == 0:
        named = True
    parent_res = parent_sig.get("residues") or {}
    child_res = child_sig.get("residues") or {}
    for mod in RESIDUE_MODULI:
        parent_set = set(parent_res.get(str(mod), []))
        child_set = set(child_res.get(str(mod), []))
        if child_set and child_set < parent_set:
            named = True
    if named:
        return "named_thinner"
    return "strict_subset"


def _node_row(word: str, starts: list[int], n_end: int) -> dict[str, Any]:
    values = sorted(set(starts))
    sig = set_signature(values, n_end)
    odds = odd_count(word) if word else 0
    return {
        "word": word,
        "length": len(word),
        "odd_count": odds,
        "G": exponent_gap(len(word), odds) if word else 0,
        "mixed": (not is_monochrome(word)) if word else False,
        "prefix_nc": prefix_noncontracting(word) if word else True,
        "starts": values[:START_KEEP],
        "start_count": len(values),
        "signature": sig,
        "signature_key": [sig.get("modulus"), bool(sig.get("singleton"))],
    }


def collect_nested(
    n_start: int,
    n_end: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    realizing: dict[str, list[int]] = defaultdict(list)
    crossings: list[dict[str, Any]] = []
    unfinished: list[dict[str, Any]] = []
    absorbed: list[int] = []
    identity_failures: list[dict[str, Any]] = []
    even_tau_failures: list[int] = []
    max_tau = 0
    max_peak_bits = 0
    crossed = 0

    for n in range(n_start, n_end + 1):
        walked = slim_crossing(n, horizon=horizon, bit_cap=bit_cap)
        max_peak_bits = max(max_peak_bits, walked["peak_bits"])
        if walked["status"] == STATUS_CROSSED:
            crossed += 1
            max_tau = max(max_tau, walked["tau_plus"] or 0)
            fail = _identity_failure(walked)
            if fail is not None and len(identity_failures) < SAMPLE_CAP:
                identity_failures.append(fail)
            if n % 2 == 0 and walked["tau_plus"] != 1:
                even_tau_failures.append(n)
            crossings.append(
                {
                    "n": n,
                    "tau_plus": walked["tau_plus"],
                    "odd_count": walked["odd_count"],
                    "word": walked["word"],
                    "pred": walked["pred"],
                    "pred_even": walked["pred_even"],
                    "G_tau": walked["G_tau"],
                }
            )
        elif walked["status"] == STATUS_ABSORBED:
            absorbed.append(n)
        else:
            unfinished.append({"n": n, "status": walked["status"], "word": walked["word"]})
        nc_word = walked["nc_word"]
        for length in range(1, len(nc_word) + 1):
            realizing[nc_word[:length]].append(n)

    nodes = {word: _node_row(word, starts, n_end) for word, starts in realizing.items()}
    extensions: list[dict[str, Any]] = []
    tag_counts = {"empty": 0, "same": 0, "strict_subset": 0, "named_thinner": 0}
    named_examples: list[dict[str, Any]] = []
    empty_examples: list[dict[str, Any]] = []

    for word, node in nodes.items():
        parent_starts = set(realizing[word])
        parent_sig = node["signature"]
        for letter in ("O", "E"):
            keeps = letter_keeps_nc(word, letter)
            child = word + letter
            child_starts = realizing.get(child, [])
            if not keeps:
                continue
            child_sig = (
                nodes[child]["signature"]
                if child in nodes
                else set_signature(child_starts, n_end)
            )
            tag = extension_tag(parent_sig, child_sig)
            tag_counts[tag] += 1
            row = {
                "parent": word,
                "letter": letter,
                "child": child,
                "keeps_nc": True,
                "tag": tag,
                "parent_count": node["start_count"],
                "child_count": child_sig["count"],
                "parent_modulus": parent_sig["modulus"],
                "child_modulus": child_sig["modulus"],
            }
            extensions.append(row)
            if tag == "named_thinner" and len(named_examples) < SAMPLE_CAP:
                named_examples.append(row)
            if tag == "empty" and len(empty_examples) < SAMPLE_CAP:
                empty_examples.append(row)
        del parent_starts

    depth: dict[int, dict[str, Any]] = {}
    for word, node in nodes.items():
        bucket = depth.setdefault(
            node["length"],
            {"words": 0, "mixed_words": 0, "keys": set(), "max_count": 0},
        )
        bucket["words"] += 1
        if node["mixed"]:
            bucket["mixed_words"] += 1
        bucket["keys"].add(signature_key(node["signature"]))
        bucket["max_count"] = max(bucket["max_count"], node["start_count"])

    depth_census = []
    for length in sorted(depth):
        bucket = depth[length]
        words = bucket["words"]
        classes = len(bucket["keys"])
        depth_census.append(
            {
                "length": length,
                "words": words,
                "mixed_words": bucket["mixed_words"],
                "signatures": classes,
                "compression": None if words == 0 else round(classes / words, 6),
                "max_start_count": bucket["max_count"],
            }
        )

    least_constrained = sorted(
        (
            {
                "word": node["word"],
                "length": node["length"],
                "start_count": node["start_count"],
                "G": node["G"],
                "mixed": node["mixed"],
                "modulus": node["signature"]["modulus"],
            }
            for node in nodes.values()
            if node["mixed"]
        ),
        key=lambda item: (-item["start_count"], -item["length"], item["word"]),
    )[:SAMPLE_CAP]

    return {
        "n_start": n_start,
        "n_end": n_end,
        "start_count": n_end - n_start + 1,
        "crossed": crossed,
        "absorbed": absorbed,
        "absorbed_count": len(absorbed),
        "unfinished": unfinished,
        "unfinished_count": len(unfinished),
        "identity_failures": identity_failures,
        "identity_failure_count": len(identity_failures),
        "even_tau_failures": even_tau_failures,
        "max_tau": max_tau,
        "max_peak_bits": max_peak_bits,
        "prefix_count": len(nodes),
        "mixed_prefix_count": sum(1 for node in nodes.values() if node["mixed"]),
        "nodes": nodes,
        "extensions": extensions,
        "tag_counts": tag_counts,
        "named_examples": named_examples,
        "empty_examples": empty_examples,
        "depth_census": depth_census,
        "least_constrained": least_constrained,
        "crossings": crossings,
    }


def first_passage_classes(
    crossings: list[dict[str, Any]],
    n_end: int,
) -> list[dict[str, Any]]:
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in crossings:
        tau = row["tau_plus"]
        odds = row["odd_count"]
        if tau is None:
            continue
        groups[(tau, odds)].append(row)

    out: list[dict[str, Any]] = []
    for (tau, odds), rows in sorted(groups.items(), key=lambda item: (-len(item[1]), item[0])):
        starts = [row["n"] for row in rows]
        preds = [row["pred"] for row in rows if row["pred"] is not None]
        pred_even = sum(1 for row in rows if row["pred_even"])
        out.append(
            {
                "k": tau,
                "o": odds,
                "count": len(rows),
                "crossing_window": crossing_window(tau, odds),
                "start_signature": set_signature(starts, n_end),
                "pred_signature": set_signature(preds, n_end) if preds else set_signature([], n_end),
                "pred_even_count": pred_even,
                "sample_starts": starts[:SAMPLE_CAP],
            }
        )
    return out


def short_word_signatures(*, k_max: int = K_PULLBACK) -> list[dict[str, Any]]:
    image = Ival(1, IMAGE_CAP, None)
    rows: list[dict[str, Any]] = []
    for word in prefix_nc_words(k_max):
        if is_monochrome(word):
            continue
        back = pullback_word(word, image)
        rows.append(
            {
                "word": word,
                "length": len(word),
                "G": exponent_gap(len(word), odd_count(word)),
                "pullback_empty_over_image": back["empty"],
                "pullback_truncated": back["truncated"],
                "pullback_components": back["components"],
                "pullback_measure": back["measure"],
                "pullback_is_not_emptiness": True,
            }
        )
    return rows


def hunt_tau(
    n_start: int,
    n_end: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = HUNT_BIT_CAP,
) -> dict[str, Any]:
    max_tau = 0
    max_n = None
    unfinished: list[dict[str, Any]] = []
    absorbed: list[int] = []
    identity_failures: list[dict[str, Any]] = []
    even_tau_failures: list[int] = []
    tau_hist: dict[str, int] = defaultdict(int)
    longest: list[dict[str, Any]] = []
    crossed = 0
    max_peak_bits = 0

    for n in range(n_start, n_end + 1):
        keep = n in RECORD_STARTS or n <= 2000
        walked = slim_crossing(n, horizon=horizon, bit_cap=bit_cap, keep_word=keep)
        max_peak_bits = max(max_peak_bits, walked["peak_bits"])
        if walked["status"] == STATUS_CROSSED:
            crossed += 1
            tau = walked["tau_plus"] or 0
            tau_hist[str(tau)] += 1
            if tau > max_tau:
                max_tau = tau
                max_n = n
            fail = _identity_failure(walked)
            if fail is not None and len(identity_failures) < SAMPLE_CAP:
                identity_failures.append(fail)
            if n % 2 == 0 and tau != 1:
                even_tau_failures.append(n)
            slim = {
                "n": n,
                "tau_plus": tau,
                "odd_count": walked["odd_count"],
                "word": walked["word"] if keep else None,
                "pred": walked["pred"] if keep else None,
                "pred_bits": walked.get("pred_bits"),
                "G_tau": walked["G_tau"],
                "peak_bits": walked["peak_bits"],
                "crossing_letter": walked["crossing_letter"],
            }
            longest.append(slim)
            longest.sort(key=lambda item: (-(item["tau_plus"] or 0), item["n"]))
            if len(longest) > SAMPLE_CAP:
                longest.pop()
        elif walked["status"] == STATUS_ABSORBED:
            absorbed.append(n)
        else:
            unfinished.append({"n": n, "status": walked["status"]})

    filled: list[dict[str, Any]] = []
    for row in longest:
        if row.get("word"):
            filled.append(row)
            continue
        replay = slim_crossing(
            row["n"],
            horizon=horizon,
            bit_cap=bit_cap,
            keep_word=True,
        )
        row = dict(row)
        row["word"] = replay["word"]
        row["pred"] = replay["pred"]
        row["pred_bits"] = replay.get("pred_bits")
        row["crossing_letter"] = replay["crossing_letter"]
        filled.append(row)
    longest = filled
    beats_record = [
        row for row in longest if (row["tau_plus"] or 0) > KNOWN_RECORD["tau_plus"]
    ]
    return {
        "n_start": n_start,
        "n_end": n_end,
        "start_count": n_end - n_start + 1,
        "crossed": crossed,
        "absorbed_count": len(absorbed),
        "unfinished": unfinished,
        "unfinished_count": len(unfinished),
        "identity_failures": identity_failures,
        "identity_failure_count": len(identity_failures),
        "even_tau_failures": even_tau_failures,
        "max_tau": max_tau,
        "max_tau_n": max_n,
        "max_peak_bits": max_peak_bits,
        "tau_histogram": dict(sorted(tau_hist.items(), key=lambda item: int(item[0]))),
        "longest": longest,
        "beats_known_record": beats_record,
        "known_record_n": KNOWN_RECORD["n"],
        "known_record_tau": KNOWN_RECORD["tau_plus"],
        "search_horizon_is_not_L": True,
        "finite_max_is_not_a_bound": True,
    }


def record_trajectories(
    nodes: dict[str, dict[str, Any]],
    n_end: int,
    *,
    starts: tuple[int, ...] = RECORD_STARTS,
    bit_cap: int = HUNT_BIT_CAP,
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for n in starts:
        walked = slim_crossing(n, bit_cap=bit_cap)
        nc_word = walked["nc_word"]
        chain = []
        for length in range(1, len(nc_word) + 1):
            prefix = nc_word[:length]
            node = nodes.get(prefix)
            if node is None:
                continue
            chain.append(
                {
                    "k": length,
                    "word": prefix,
                    "G": node["G"],
                    "start_count": node["start_count"],
                    "modulus": node["signature"]["modulus"],
                    "singleton": node["signature"]["singleton"],
                    "residues_mod8": node["signature"]["residues"]["8"],
                    "tag_from_parent": None,
                }
            )
            if length >= 2:
                parent = nodes.get(prefix[:-1])
                if parent is not None:
                    chain[-1]["tag_from_parent"] = extension_tag(
                        parent["signature"],
                        node["signature"],
                    )
        last_nc = None
        if walked["status"] == STATUS_CROSSED and walked["pred"] is not None:
            last_nc = walked["pred"]
        out.append(
            {
                "n": n,
                "status": walked["status"],
                "tau_plus": walked["tau_plus"],
                "word": walked["word"],
                "nc_word": nc_word,
                "odd_count": walked["odd_count"],
                "G_tau": walked["G_tau"],
                "last_nc": last_nc,
                "peak_bits": walked["peak_bits"],
                "chain": chain,
                "unique_after": next(
                    (row["k"] for row in chain if row["singleton"]),
                    None,
                ),
            }
        )
    return out


def lean_api_present() -> dict[str, Any]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8") if RESIDUAL_PATH.is_file() else ""
    minimum = MIN_PATH.read_text(encoding="utf-8") if MIN_PATH.is_file() else ""
    cycle = CYCLE_PATH.read_text(encoding="utf-8") if CYCLE_PATH.is_file() else ""
    prefix = PREFIX_PATH.read_text(encoding="utf-8") if PREFIX_PATH.is_file() else ""
    new_text = LEAN_NEW.read_text(encoding="utf-8") if LEAN_NEW.is_file() else ""
    combined = floor + residual + minimum + cycle + prefix + new_text
    out: dict[str, Any] = {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "DriftFirstPassage_absent": not LEAN_NEW.is_file(),
        "DriftFirstPassage_present": LEAN_NEW.is_file(),
        "ResidualStep_not_extended": "def ResidualStep" in residual
        and "DriftFirstPassage" not in residual
        and "A_w" not in residual
        and "tau_plus" not in residual,
        "CycleDiophantine_not_rewritten": "drift_first_passage" not in cycle.lower(),
        "PrefixNc_not_reopened": "drift_first_passage" not in prefix.lower()
        if prefix
        else True,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined
        and "theorem tau_plus_finite" not in combined
        and "theorem drift_first_passage" not in floor,
        "no_forbidden_engine": "PowerHeight" not in floor,
        "forbidden_engines": list(FORBIDDEN_ENGINES),
    }
    for name in FLOOR_LEMMAS:
        out[name] = f"theorem {name}" in floor or f"def {name}" in floor
    return out


def _uniform_pruning_rule(nested: dict[str, Any]) -> bool:
    """A law, not a long-word window-empty artefact."""

    short_empty = [
        row
        for row in nested["extensions"]
        if row["tag"] == "empty" and len(row["parent"]) <= 4 and row["parent_count"] >= 4
    ]
    if not short_empty:
        return False
    letters = {row["letter"] for row in short_empty}
    return len(letters) == 1 and len(short_empty) >= 3


def _signature_compression(nested: dict[str, Any]) -> bool:
    rows = [row for row in nested["depth_census"] if row["length"] >= 4 and row["words"] >= 8]
    if not rows:
        return False
    return all((row["compression"] or 1) <= 0.5 for row in rows)


def classify(
    nested: dict[str, Any],
    hunt: dict[str, Any],
    lean: dict[str, Any],
) -> dict[str, Any]:
    lean_ok = (
        lean.get("sorry_free")
        and lean.get("DriftFirstPassage_absent")
        and lean.get("power_bound_word")
        and lean.get("power_bound_contracts")
        and lean.get("ResidualStep_not_extended")
        and lean.get("no_global_termination_theorem")
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": "Lean gate failed: new file, missing lemma, or sorry",
        }
    if nested.get("unfinished_count"):
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": (
                "nested-window starts missed the horizon or bit cap; "
                "that cutoff is not a bound L"
            ),
        }
    if (
        nested.get("identity_failures")
        or nested.get("even_tau_failures")
        or hunt.get("identity_failures")
        or hunt.get("even_tau_failures")
    ):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": (
                "a realized crossing violated the even-letter G-recurrence "
                "or an even start failed tau_+=1"
            ),
        }
    if nested.get("absorbed_count") or hunt.get("absorbed_count"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": "a start reached 1 along a prefix-NC word",
        }
    if _uniform_pruning_rule(nested):
        return {
            "classification": CLASS_PRUNING,
            "secondary": [],
            "reason": (
                "short NC-preserving extensions with large parent sets "
                "are uniformly empty for one letter"
            ),
        }
    if hunt.get("beats_known_record") and _signature_compression(nested):
        return {
            "classification": CLASS_UNBOUNDED,
            "secondary": [],
            "reason": (
                "a structured family postponed first passage past the known "
                "record and signatures compressed"
            ),
        }
    tags = nested.get("tag_counts") or {}
    named = tags.get("named_thinner", 0)
    taut = tags.get("strict_subset", 0)
    hunt_left = hunt.get("unfinished_count") or 0
    hunt_max = hunt.get("max_tau")
    return {
        "classification": CLASS_COMPLEX,
        "secondary": [],
        "reason": (
            "nested A_w signatures do not compress below the itineraries themselves; "
            f"{taut} extensions are tautological window subsets and {named} "
            "named-thinner hits are residue/modulus artefacts of longer prefixes, "
            "not a pruning rule; hunt max "
            f"tau_+={hunt_max} is a larger record, not a structured unbounded "
            f"family; {hunt_left} hunt bit-cap leftovers are not a bound L"
        ),
    }


def run_probe(
    *,
    n_start: int = NESTED_MIN,
    n_end: int = NESTED_MAX,
    hunt_start: int = HUNT_MIN,
    hunt_end: int = HUNT_MAX,
) -> dict[str, Any]:
    nested = collect_nested(n_start, n_end)
    hunt = hunt_tau(hunt_start, hunt_end)
    classes = first_passage_classes(nested["crossings"], n_end)
    extra = tuple(row["n"] for row in hunt.get("longest") or [] if row["n"] not in RECORD_STARTS)
    records = record_trajectories(
        nested["nodes"],
        n_end,
        starts=RECORD_STARTS + extra,
    )
    short = short_word_signatures()
    return {
        "nested": nested,
        "hunt": hunt,
        "first_passage": classes,
        "records": records,
        "short_words": short,
        "residual_step_extended": False,
        "explicit_L": False,
        "adversarial_engine": False,
        "cycle_diophantine_reopened": False,
        "prefix_nc_admissibility_reopened": False,
        "corridor_reopened": False,
        "endpoint_filtration_reopened": False,
        "odd_fourth_power_reopened": False,
    }


def _public_nested(nested: dict[str, Any]) -> dict[str, Any]:
    return {
        key: nested[key]
        for key in (
            "n_start",
            "n_end",
            "start_count",
            "crossed",
            "absorbed_count",
            "unfinished_count",
            "identity_failure_count",
            "even_tau_failures",
            "max_tau",
            "max_peak_bits",
            "prefix_count",
            "mixed_prefix_count",
            "tag_counts",
            "named_examples",
            "empty_examples",
            "depth_census",
            "least_constrained",
        )
    }


def probe_payload(
    *,
    n_start: int = NESTED_MIN,
    n_end: int = NESTED_MAX,
    hunt_start: int = HUNT_MIN,
    hunt_end: int = HUNT_MAX,
) -> dict[str, Any]:
    scan = run_probe(
        n_start=n_start,
        n_end=n_end,
        hunt_start=hunt_start,
        hunt_end=hunt_end,
    )
    lean = lean_api_present()
    decision = classify(scan["nested"], scan["hunt"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "search_horizon_is_L": False,
            "tau_plus_finite": False,
            "tau_plus_bounded": False,
            "parity_frequency_theorem": False,
            "global_termination": False,
            "floating_point_verdict": False,
            "window_empty_is_A_w_empty": False,
            "cardinality_drop_is_named": False,
            "finite_max_is_unbounded_family": False,
            "endpoint_filtration_reopened": False,
        }
    )
    return {
        "experiment": "juggler_drift_first_passage",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "window": {
            "n_start": n_start,
            "n_end": n_end,
            "hunt_start": hunt_start,
            "hunt_end": hunt_end,
            "horizon": HORIZON,
            "bit_cap": BIT_CAP,
            "hunt_bit_cap": HUNT_BIT_CAP,
            "hard_starts": list(HARD_STARTS),
            "tall_starts": list(TALL_STARTS),
            "record_starts": list(RECORD_STARTS),
            "algorithm_version": ALGORITHM_VERSION,
            "classification_version": CLASSIFICATION_VERSION,
            "search_id": search_id_for(n_start, n_end, hunt_end),
            "crossing_policy": CROSSING_POLICY,
        },
        "scan": {
            "nested": _public_nested(scan["nested"]),
            "hunt": scan["hunt"],
            "first_passage": scan["first_passage"][:40],
            "records": scan["records"],
            "short_words": scan["short_words"],
            "residual_step_extended": False,
            "explicit_L": False,
            "adversarial_engine": False,
            "cycle_diophantine_reopened": False,
            "prefix_nc_admissibility_reopened": False,
            "corridor_reopened": False,
            "endpoint_filtration_reopened": False,
            "odd_fourth_power_reopened": False,
        },
        "lean": lean,
        "decision": decision,
        "search_method": (
            "actual prefix-NC realizing sets A_w ∩ [2,N]; structural "
            "signatures (AP modulus, residues); NC-preserving extension "
            "tags; first-passage start classes C_{k,o}; short-word Ival "
            "pullback as signature only; tau_+ hunt "
            f"n={hunt_start}..{hunt_end}; nested n={n_start}..{n_end}; "
            f"horizon {HORIZON} is not L"
        ),
        "_nodes": scan["nested"]["nodes"],
        "_extensions": scan["nested"]["extensions"],
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    nested = payload["scan"]["nested"]
    hunt = payload["scan"]["hunt"]
    lean = payload["lean"]
    window = payload["window"]
    lines = [
        "# Juggler drift-first-passage tree",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Studies nested realizing sets",
        "A_w of actual prefix-NC words. Does not claim tau_+ < infinity.",
        "Does not reopen prefix-NC word admissibility, endpoint",
        "filtration, the corridor, escape-state, ResidualStep, or",
        "odd-fourth-power.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Along actual prefix-NC chains, does A_w^{NC}",
        "                        acquire a named arithmetic constraint that",
        "                        forbids indefinite NC continuation?",
        "Novelty hypothesis      the nested start-set thins or prunes",
        "Falsifier               only tautological |A_w ∩ window| decrease",
        "Existing machinery      slim crossing, exponent_gap, Ival pullback",
        "Maximum Phase-0 scope   one probe; nested signatures; hunt; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- search_id: `{window['search_id']}`",
        f"- algorithm_version: `{window['algorithm_version']}`",
        f"- classification_version: `{window['classification_version']}`",
        f"- nested window: `n={window['n_start']}..{window['n_end']}`",
        f"- hunt window: `n={window['hunt_start']}..{window['hunt_end']}`",
        f"- horizon: `{window['horizon']}` (not L)",
        f"- nested bit_cap: `{window['bit_cap']}`",
        f"- hunt bit_cap: `{window.get('hunt_bit_cap', HUNT_BIT_CAP)}`",
        f"- crossing_policy: `{window['crossing_policy']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Nested census",
        "",
        f"- starts: `{nested['start_count']}`",
        f"- crossed: `{nested['crossed']}`",
        f"- absorbed at 1 still NC: `{nested['absorbed_count']}`",
        f"- unfinished: `{nested['unfinished_count']}`",
        f"- identity failures: `{nested['identity_failure_count']}`",
        f"- even tau_+ failures: `{len(nested['even_tau_failures'])}`",
        f"- unique prefix-NC words: `{nested['prefix_count']}`",
        f"- mixed prefix-NC words: `{nested['mixed_prefix_count']}`",
        f"- max tau_+ in nested window: `{nested['max_tau']}`",
        f"- max peak bits: `{nested['max_peak_bits']}`",
        "",
        "## Extension tags",
        "",
    ]
    tags = nested.get("tag_counts") or {}
    for key in ("empty", "same", "strict_subset", "named_thinner"):
        lines.append(f"- `{key}`: `{tags.get(key, 0)}`")
    lines.extend(["", "## Named-thinner examples", ""])
    if not nested.get("named_examples"):
        lines.append("- none")
    for row in nested.get("named_examples") or []:
        lines.append(
            f"- `{row['parent']}` + `{row['letter']}` → `{row['child']}` "
            f"counts `{row['parent_count']}`→`{row['child_count']}` "
            f"mod `{row['parent_modulus']}`→`{row['child_modulus']}`"
        )
    lines.extend(["", "## Depth census (words vs signatures)", ""])
    for row in nested.get("depth_census") or []:
        lines.append(
            f"- k=`{row['length']}` words=`{row['words']}` mixed=`{row['mixed_words']}` "
            f"signatures=`{row['signatures']}` compression=`{row['compression']}` "
            f"max_|A|=`{row['max_start_count']}`"
        )
    lines.extend(["", "## Least-constrained mixed prefixes", ""])
    for row in (nested.get("least_constrained") or [])[:8]:
        lines.append(
            f"- `{row['word']}` k=`{row['length']}` |A|=`{row['start_count']}` "
            f"G=`{row['G']}` modulus=`{row['modulus']}`"
        )
    lines.extend(["", "## tau_+ hunt", ""])
    lines.append(f"- starts: `{hunt['start_count']}`")
    lines.append(f"- crossed: `{hunt['crossed']}`")
    lines.append(f"- unfinished: `{hunt['unfinished_count']}`")
    lines.append(f"- max tau_+: `{hunt['max_tau']}` at n=`{hunt['max_tau_n']}`")
    lines.append(f"- known record: n=`{hunt['known_record_n']}` tau_+=`{hunt['known_record_tau']}`")
    lines.append(f"- beats known record: `{len(hunt.get('beats_known_record') or [])}`")
    lines.append(f"- finite max is not a bound: `{hunt['finite_max_is_not_a_bound']}`")
    lines.extend(["", "## Longest crossings in the hunt", ""])
    for row in (hunt.get("longest") or [])[:12]:
        word = row.get("word") or ""
        lines.append(
            f"- n=`{row['n']}` tau_+=`{row['tau_plus']}` o=`{row['odd_count']}` "
            f"peak_bits=`{row['peak_bits']}` word=`{word}`"
        )
    lines.extend(["", "## Record trajectories", ""])
    for row in payload["scan"]["records"]:
        lines.append(
            f"- n=`{row['n']}` tau_+=`{row['tau_plus']}` last_nc=`{row['last_nc']}` "
            f"unique_after=`{row['unique_after']}` peak_bits=`{row['peak_bits']}`"
        )
    lines.extend(["", "## First-passage classes (largest)", ""])
    for row in (payload["scan"]["first_passage"] or [])[:12]:
        sig = row["start_signature"]
        lines.append(
            f"- C_`{row['k']}`,`{row['o']}` count=`{row['count']}` "
            f"modulus=`{sig['modulus']}` residues8=`{sig['residues']['8']}` "
            f"window=`{row['crossing_window']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new DriftFirstPassage file absent: `{lean.get('DriftFirstPassage_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- CycleDiophantine not rewritten: `{lean.get('CycleDiophantine_not_rewritten')}`",
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
            "A finite tau_+ on this window is not tau_+ < infinity.",
            "A search-horizon miss is not a bound L.",
            "A window-empty child is not A_w empty.",
            "Do not claim termination.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _checksum(nested: dict[str, Any], hunt: dict[str, Any], classification: str) -> str:
    blob = json.dumps(
        {
            "classification": classification,
            "prefix_count": nested["prefix_count"],
            "tag_counts": nested["tag_counts"],
            "hunt_max_tau": hunt["max_tau"],
            "hunt_max_n": hunt["max_tau_n"],
            "crossed": nested["crossed"],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def _config(window: dict[str, Any]) -> dict[str, Any]:
    return {
        "search_id": window["search_id"],
        "algorithm_version": ALGORITHM_VERSION,
        "classification_version": CLASSIFICATION_VERSION,
        "n_start": window["n_start"],
        "n_end": window["n_end"],
        "hunt_start": window["hunt_start"],
        "hunt_end": window["hunt_end"],
        "horizon": HORIZON,
        "bit_cap": BIT_CAP,
        "hunt_bit_cap": HUNT_BIT_CAP,
        "crossing_policy": CROSSING_POLICY,
        "hard_starts": list(HARD_STARTS),
        "tall_starts": list(TALL_STARTS),
        "record_starts": list(RECORD_STARTS),
        "arithmetic": "python-int",
    }


def _manifest(payload: dict[str, Any]) -> dict[str, Any]:
    window = payload["window"]
    nested = payload["scan"]["nested"]
    hunt = payload["scan"]["hunt"]
    unfinished = nested["unfinished_count"]
    return {
        "search_id": window["search_id"],
        "git_commit": git_commit(),
        "algorithm_version": ALGORITHM_VERSION,
        "n_range": [window["n_start"], window["n_end"]],
        "maximum_horizon": window["horizon"],
        "hunt_range": [window["hunt_start"], window["hunt_end"]],
        "classification_version": CLASSIFICATION_VERSION,
        "crossing_policy": window["crossing_policy"],
        "completion_status": "COMPLETE" if unfinished == 0 else "INCOMPLETE",
        "checksum": _checksum(nested, hunt, payload["decision"]["classification"]),
        "classification": payload["decision"]["classification"],
        "runtime_note": "in-memory Phase-0 census; no sqlite",
    }


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_start: int = NESTED_MIN,
    n_end: int = NESTED_MAX,
    hunt_start: int = HUNT_MIN,
    hunt_end: int = HUNT_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(
        n_start=n_start,
        n_end=n_end,
        hunt_start=hunt_start,
        hunt_end=hunt_end,
    )
    public = {key: value for key, value in data.items() if not key.startswith("_")}
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(public, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(public), encoding="utf-8")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    for name in (
        "summaries",
        "analysis",
        "ranges",
        "prefixes",
        "classes",
        "record_trajectories",
    ):
        (DATA_DIR / name).mkdir(exist_ok=True)
    (DATA_DIR / "README.md").write_text(
        "# Juggler drift-first-passage tree\n\n"
        "Phase-0 census of nested realizing sets A_w of actual\n"
        "prefix-NC words, plus a modest tau_+ hunt. This is not a\n"
        "proof that tau_+ is finite and not a termination theorem.\n"
        "A window-empty child is not A_w empty.\n\n"
        "```text\n"
        "README.md\n"
        "manifest.json\n"
        "config.json\n"
        "ranges/\n"
        "prefixes/\n"
        "classes/\n"
        "record_trajectories/\n"
        "summaries/\n"
        "analysis/\n"
        "```\n\n"
        "From the repository root:\n\n"
        "```text\n"
        "python -m research.juggler_sequence.drift_first_passage\n"
        "```\n\n"
        "The Research Engine control layer is not used. ResidualStep is\n"
        "not extended. Prefix-NC word admissibility is not reopened.\n"
        "Endpoint filtration is not reopened.\n",
        encoding="utf-8",
    )
    window = data["window"]
    (DATA_DIR / "config.json").write_text(
        json.dumps(_config(window), indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(_manifest(public), indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "summaries" / "summary.md").write_text(
        render_markdown(public), encoding="utf-8"
    )
    nested = public["scan"]["nested"]
    hunt = public["scan"]["hunt"]
    (DATA_DIR / "summaries" / "phase0.json").write_text(
        json.dumps(
            {
                "decision": public["decision"],
                "window": window,
                "nested": nested,
                "hunt": {
                    "max_tau": hunt["max_tau"],
                    "max_tau_n": hunt["max_tau_n"],
                    "crossed": hunt["crossed"],
                    "unfinished_count": hunt["unfinished_count"],
                    "beats_known_record": hunt["beats_known_record"],
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "ranges" / f"n{window['n_start']}_{window['n_end']}.json").write_text(
        json.dumps(
            {
                "n_start": window["n_start"],
                "n_end": window["n_end"],
                "prefix_count": nested["prefix_count"],
                "tag_counts": nested["tag_counts"],
                "max_tau": nested["max_tau"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "ranges" / f"hunt_{window['hunt_start']}_{window['hunt_end']}.json").write_text(
        json.dumps(
            {
                "n_start": window["hunt_start"],
                "n_end": window["hunt_end"],
                "max_tau": hunt["max_tau"],
                "max_tau_n": hunt["max_tau_n"],
                "tau_histogram": hunt["tau_histogram"],
                "longest": hunt["longest"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    nodes = data.get("_nodes") or {}
    compact_nodes = []
    for word, node in sorted(nodes.items(), key=lambda item: (len(item[0]), item[0])):
        compact_nodes.append(
            {
                "word": word,
                "G": node["G"],
                "start_count": node["start_count"],
                "starts": node["starts"],
                "modulus": node["signature"]["modulus"],
                "singleton": node["signature"]["singleton"],
                "residues": node["signature"]["residues"],
            }
        )
    (DATA_DIR / "prefixes" / "nodes.json").write_text(
        json.dumps(compact_nodes, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "prefixes" / "extensions.json").write_text(
        json.dumps(data.get("_extensions") or public["scan"]["nested"].get("named_examples") or [], indent=2)
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "classes" / "first_passage.json").write_text(
        json.dumps(public["scan"]["first_passage"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "classes" / "depth_census.json").write_text(
        json.dumps(nested["depth_census"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "analysis" / "census.json").write_text(
        json.dumps(
            {
                "nested": nested,
                "hunt_max_tau": hunt["max_tau"],
                "hunt_max_tau_n": hunt["max_tau_n"],
                "tag_counts": nested["tag_counts"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "analysis" / "least_constrained.json").write_text(
        json.dumps(nested["least_constrained"], indent=2) + "\n", encoding="utf-8"
    )
    for row in public["scan"]["records"]:
        (DATA_DIR / "record_trajectories" / f"n_{row['n']}.json").write_text(
            json.dumps(row, indent=2) + "\n", encoding="utf-8"
        )
    return public


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
