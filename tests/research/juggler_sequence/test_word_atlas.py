"""Juggler word atlas Milestone 1. Not a termination test."""

from __future__ import annotations

from pathlib import Path

import pytest

from research.juggler_sequence.atlas import (
    build,
    continuation_mask,
    continuations,
    experiment_manifest,
    factor_complexity,
    factor_set,
    find_min_realizer,
    pe_records,
    validate,
    word_record,
)
from research.juggler_sequence.atlas.cli import main as atlas_main
from research.juggler_sequence.atlas.cpu_census import census, merge_starts
from research.juggler_sequence.atlas.native import find_binary, parse_census_tsv, run_census
from research.juggler_sequence.atlas.fixtures import (
    EEOE_AT_2500,
    FLOOR_POWER_SEEDS,
    OOE_AT_FIVE,
    PE_CHAIN_365,
)
from research.juggler_sequence.atlas.packed import (
    pack_word,
    run_signature,
    unpack_word,
    word_metadata,
)
from research.juggler_sequence.atlas.pe_adapter import (
    classify_persistent_expanding,
    pe_certified_records,
)
from research.juggler_sequence.atlas.schema import (
    LANG_PE_CERTIFIED,
    LANG_REALIZABLE,
    PE_CERTIFIED,
    PE_PROXY,
    STATUS_FOUND,
    STATUS_NOT_FOUND,
)
from research.juggler_sequence.atlas.validate import (
    compare_dense,
    compare_dense_allow_overflow,
    validate_suite,
)
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import floor_power


def test_packed_word_roundtrip():
    length, packed = pack_word("OOE")
    assert length == 3
    assert unpack_word(length, packed) == "OOE"
    assert run_signature(length, packed) == "O2,E1"
    meta = word_metadata(length, packed)
    assert meta["odd_count"] == 2
    assert meta["exponent_surplus"] == 3**2 - 2**3
    assert meta["beta_num"] == 9
    assert meta["beta_den"] == 8


def test_floor_power_and_lean_word_fixtures():
    for n, expected in FLOOR_POWER_SEEDS:
        assert floor_power(n) == expected
    assert follows_itinerary(OOE_AT_FIVE["n"], OOE_AT_FIVE["word"])
    assert image_after(OOE_AT_FIVE["n"], OOE_AT_FIVE["word"]) == OOE_AT_FIVE["image"]
    assert follows_itinerary(EEOE_AT_2500["n"], EEOE_AT_2500["word"])
    start, word, image = (
        PE_CHAIN_365["starts"][0],
        PE_CHAIN_365["words"][0],
        PE_CHAIN_365["images"][0],
    )
    assert follows_itinerary(start, word)
    assert image_after(start, word) == image


def test_cpu_census_ooe_and_eeoe():
    min_n, min_exp, end_at = census(k_max=3, n_max=5)
    from research.juggler_sequence.atlas.packed import dense_index

    length, packed = pack_word("OOE")
    idx = dense_index(length, packed)
    assert min_n[idx] == 5
    assert end_at[idx] == 6
    assert min_exp[idx] == 5
    min_n4, _, _ = census(k_max=4, n_max=2500)
    length, packed = pack_word("EEOE")
    idx = dense_index(length, packed)
    assert min_n4[idx] is not None
    assert min_n4[idx] <= 2500


def test_pe_adapter_rejects_proxy_and_certifies_365():
    row = classify_persistent_expanding(365)
    assert row is not None
    assert row["word"] == "OOE"
    assert row["y"] == 763
    assert row["persistent"] and row["expanding"]
    recs = pe_certified_records(n_max=400, search_id="t", pe_definition=PE_CERTIFIED)
    words = {r["word"] for r in recs["pe_certified"]}
    assert "OOE" in words
    starts = {r["min_n"] for r in recs["pe_certified"]}
    assert 365 in starts
    with pytest.raises(ValueError, match="PE_PROXY"):
        pe_certified_records(n_max=10, search_id="t", pe_definition=PE_PROXY)


def test_three_way_validate_suite():
    report = validate_suite()
    assert report["ok"], report["errors"]
    assert report["cpu_eq_lean"]
    assert report["metadata_recomputed"]


def test_build_query_manifest(tmp_path: Path):
    payload = build(k_max=4, n_max=400, backend="cpu", data_dir=tmp_path)
    eid = payload["experiment_id"]
    assert payload["record_counts"]["realized"] > 0
    assert payload["checksums"]
    assert (tmp_path / "experiments" / eid / "manifest.json").is_file()
    assert payload["pe_definition"] == PE_CERTIFIED

    ooe = find_min_realizer("OOE", experiment_id=eid, data_dir=tmp_path)
    assert ooe["realization_status"] == STATUS_FOUND
    assert ooe["min_realizer"] == 5
    rec = word_record("OOE", experiment_id=eid, data_dir=tmp_path)
    assert rec["run_signature"] == "O2,E1"

    p = factor_complexity(LANG_REALIZABLE, 3, experiment_id=eid, data_dir=tmp_path)
    words = factor_set(LANG_REALIZABLE, 3, experiment_id=eid, data_dir=tmp_path)
    assert p == len(words)
    assert "OOE" in words

    mask = continuation_mask("OO", LANG_REALIZABLE, experiment_id=eid, data_dir=tmp_path)
    assert mask["successor_mask"] is not None
    assert mask["continuation_count"] in (0, 1, 2)

    hist = continuations(LANG_REALIZABLE, experiment_id=eid, data_dir=tmp_path)
    assert hist
    pe = pe_records(experiment_id=eid, data_dir=tmp_path, language_id=LANG_PE_CERTIFIED)
    assert any(row["min_n"] == 365 for row in pe)
    assert all(row["pe_definition"] == PE_CERTIFIED for row in pe)

    man = experiment_manifest(eid, data_dir=tmp_path)
    assert man["experiment_id"] == eid
    assert man["schema_version"] == payload["schema_version"]

    report = validate(experiment_id=eid, data_dir=tmp_path)
    assert report["ok"], report


def test_not_found_within_bound(tmp_path: Path):
    payload = build(k_max=4, n_max=10, backend="cpu", data_dir=tmp_path)
    rec = find_min_realizer("EEOE", experiment_id=payload["experiment_id"], data_dir=tmp_path)
    assert rec["realization_status"] == STATUS_NOT_FOUND
    assert rec["min_realizer"] is None


def test_cli_validate_and_build(tmp_path: Path):
    assert atlas_main(["--data-dir", str(tmp_path), "validate"]) == 0
    assert (
        atlas_main(
            [
                "--data-dir",
                str(tmp_path),
                "build",
                "--k-max",
                "3",
                "--n-max",
                "20",
                "--backend",
                "cpu",
            ]
        )
        == 0
    )
    assert (
        atlas_main(
            [
                "--data-dir",
                str(tmp_path),
                "factors",
                "--language",
                LANG_REALIZABLE,
                "--r",
                "2",
            ]
        )
        == 0
    )
    assert (
        atlas_main(
            [
                "--data-dir",
                str(tmp_path),
                "continuations",
                "--language",
                LANG_REALIZABLE,
            ]
        )
        == 0
    )
    assert atlas_main(["--data-dir", str(tmp_path), "benchmark", "--k-max", "3", "--n-max", "50"]) == 0


def test_overflow_merge_does_not_worsen_minima():
    min_n, min_exp, _ = census(k_max=3, n_max=5)
    before = list(min_n)
    merge_starts(min_n, min_exp, [365], k_max=3)
    from research.juggler_sequence.atlas.packed import dense_index, pack_word

    idx = dense_index(*pack_word("OOE"))
    assert min_n[idx] == 5
    assert min_n[idx] == before[idx]


def test_gpu_equals_cpu_k6(tmp_path: Path):
    binary = find_binary()
    if binary is None:
        pytest.skip("juggler-atlas-census is not built")
    dump = tmp_path / "gpu.tsv"
    run_census(
        k_max=6,
        n_max=1000,
        n_begin=1,
        backend="cuda",
        output=dump,
        binary=binary,
    )
    parsed = parse_census_tsv(dump)
    py_min, _, _ = census(k_max=6, n_max=1000)
    errors = compare_dense_allow_overflow(
        py_min,
        parsed["min_n"],
        overflow_count=int(parsed["overflow_count"]),
        label="cuda",
    )
    assert errors == [], errors
    if parsed["overflow_count"] == 0:
        assert compare_dense(py_min, parsed["min_n"], label="cuda") == []


@pytest.mark.slow
def test_milestone1_window_cpu(tmp_path: Path):
    payload = build(k_max=12, n_max=1_000_000, backend="cpu", data_dir=tmp_path)
    assert payload["record_counts"]["realizers"] == (1 << 13) - 2
    ooe = find_min_realizer("OOE", experiment_id=payload["experiment_id"], data_dir=tmp_path)
    assert ooe["min_realizer"] == 5
