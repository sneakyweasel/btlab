"""Three-way atlas validation. No floating-point map."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.cpu_census import census
from research.juggler_sequence.atlas.fixtures import (
    EEOE_AT_2500,
    FLOOR_POWER_SEEDS,
    OOE_AT_FIVE,
    PE_CHAIN_1999,
    PE_CHAIN_365,
    image_after_steps,
    itinerary_symbols,
)
from research.juggler_sequence.atlas.packed import (
    pack_word,
    run_signature,
    word_metadata,
)
from research.juggler_sequence.atlas.pe_adapter import classify_persistent_expanding
from research.juggler_sequence.atlas.schema import CLAIM_CPU, CLAIM_LEAN, STATUS_FOUND
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import floor_power


def check_floor_power_fixtures() -> list[str]:
    errors: list[str] = []
    for n, expected in FLOOR_POWER_SEEDS:
        got = floor_power(n)
        if got != expected:
            errors.append(f"floor_power({n})={got} expected {expected}")
    return errors


def check_lean_word_fixtures() -> list[str]:
    errors: list[str] = []
    n, word, image = OOE_AT_FIVE["n"], OOE_AT_FIVE["word"], OOE_AT_FIVE["image"]
    if itinerary_symbols(n, len(word)) != word:
        errors.append(f"itinerary({n},{len(word)}) != {word}")
    if not follows_itinerary(n, word):
        errors.append(f"follows_itinerary({n},{word}) is false")
    if image_after(n, word) != image:
        errors.append(f"image_after({n},{word}) != {image}")
    if image_after_steps(n, len(word)) != image:
        errors.append(f"image_after_steps({n},{len(word)}) != {image}")
    if n >= image:
        errors.append("OOE at 5 should expand")
    if follows_itinerary(EEOE_AT_2500["n"], EEOE_AT_2500["word"]) is False:
        errors.append("EEOE at 2500 should be realized")
    for chain in (PE_CHAIN_365, PE_CHAIN_1999):
        for start, w, img in zip(chain["starts"], chain["words"], chain["images"], strict=True):
            if not follows_itinerary(start, w):
                errors.append(f"follows_itinerary({start},{w}) is false")
            if image_after(start, w) != img:
                errors.append(f"image({start},{w})={image_after(start, w)} != {img}")
            row = classify_persistent_expanding(start)
            if row is None:
                errors.append(f"PE missing at {start}")
            elif row["word"] != w or row["y"] != img:
                errors.append(f"PE row mismatch at {start}: {row}")
    return errors


def check_cpu_census_fixtures() -> list[str]:
    errors: list[str] = []
    min_n, min_exp, end_at = census(k_max=3, n_max=5)
    length, packed = pack_word("OOE")
    from research.juggler_sequence.atlas.packed import dense_index

    idx = dense_index(length, packed)
    if min_n[idx] != 5:
        errors.append(f"min realizer of OOE is {min_n[idx]}, expected 5")
    if end_at[idx] != 6:
        errors.append(f"OOE end state is {end_at[idx]}, expected 6")
    if min_exp[idx] != 5:
        errors.append(f"OOE expanding realizer is {min_exp[idx]}, expected 5")
    min_n4, _, _ = census(k_max=4, n_max=2500)
    length, packed = pack_word("EEOE")
    idx = dense_index(length, packed)
    if min_n4[idx] is None or min_n4[idx] > 2500:
        errors.append(f"EEOE not observed by n=2500: {min_n4[idx]}")
    return errors


def check_metadata_recompute(k_max: int = 6) -> list[str]:
    errors: list[str] = []
    for length in range(1, k_max + 1):
        for packed in range(1 << length):
            meta = word_metadata(length, packed)
            again = word_metadata(length, packed)
            if meta != again:
                errors.append(f"metadata unstable for {length}/{packed}")
            if meta["run_signature"] != run_signature(length, packed):
                errors.append(f"run_signature mismatch {length}/{packed}")
            if meta["odd_count"] + meta["even_count"] != length:
                errors.append(f"odd+even != length for {length}/{packed}")
            if meta["exponent_surplus"] + meta["exponent_deficit"] != 0:
                errors.append(f"surplus+deficit != 0 for {length}/{packed}")
    return errors


def compare_dense_allow_overflow(
    python_min: list[int | None],
    native_min: list[int | None],
    *,
    overflow_count: int,
    label: str,
) -> list[str]:
    """Native may omit later prefixes after a wide-int overflow.

    Every filled native slot must match Python. Missing native slots are
    allowed only when the native run reported overflow.
    """

    errors: list[str] = []
    if len(python_min) != len(native_min):
        return [f"{label}: length {len(native_min)} != python {len(python_min)}"]
    missing = 0
    for i, (py, nat) in enumerate(zip(python_min, native_min, strict=True)):
        if nat is None:
            if py is not None:
                missing += 1
            continue
        if nat != py:
            errors.append(f"{label}[{i}]: native {nat} != python {py}")
            if len(errors) >= 12:
                errors.append(f"{label}: further mismatches omitted")
                break
    if missing and overflow_count == 0:
        errors.append(f"{label}: {missing} native gaps with overflow_count=0")
    return errors


def compare_dense(
    left: list[int | None],
    right: list[int | None],
    *,
    label: str,
) -> list[str]:
    errors: list[str] = []
    if len(left) != len(right):
        return [f"{label}: length {len(left)} != {len(right)}"]
    for i, (a, b) in enumerate(zip(left, right, strict=True)):
        if a != b:
            errors.append(f"{label}[{i}]: {a} != {b}")
            if len(errors) >= 12:
                errors.append(f"{label}: further mismatches omitted")
                break
    return errors


def validate_suite(
    *,
    native_min_n: list[int | None] | None = None,
    native_label: str = "native",
) -> dict[str, Any]:
    errors = []
    errors.extend(check_floor_power_fixtures())
    errors.extend(check_lean_word_fixtures())
    errors.extend(check_cpu_census_fixtures())
    errors.extend(check_metadata_recompute())
    if native_min_n is not None:
        py_min, _, _ = census(k_max=6, n_max=1000)
        if len(native_min_n) == len(py_min):
            errors.extend(compare_dense(py_min, native_min_n, label=native_label))
        else:
            errors.append(
                f"{native_label} table size {len(native_min_n)} != python {len(py_min)}"
            )
    ok = not errors
    return {
        "ok": ok,
        "errors": errors,
        "claims": [CLAIM_LEAN, CLAIM_CPU],
        "cpu_eq_lean": not check_floor_power_fixtures() and not check_lean_word_fixtures(),
        "metadata_recomputed": not check_metadata_recompute(),
    }


def stored_metadata_matches(
    data_dir: Path,
    experiment_id: str,
    *,
    sample: int = 64,
) -> list[str]:
    from research.juggler_sequence.atlas.storage import connect

    errors: list[str] = []
    con = connect(data_dir)
    try:
        rows = con.execute(
            """
            SELECT word_id, length, packed, odd_count, even_count, run_signature,
                   exponent_surplus, exponent_deficit, beta_num, beta_den
            FROM words
            ORDER BY word_id
            LIMIT ?
            """,
            (sample,),
        ).fetchall()
        for row in rows:
            meta = word_metadata(row[1], row[2])
            fields = (
                "word_id",
                "length",
                "packed",
                "odd_count",
                "even_count",
                "run_signature",
                "exponent_surplus",
                "exponent_deficit",
                "beta_num",
                "beta_den",
            )
            for name, got in zip(fields, row, strict=True):
                if got != meta[name]:
                    errors.append(f"stored {name}={got} != {meta[name]}")
    finally:
        con.close()
    return errors
