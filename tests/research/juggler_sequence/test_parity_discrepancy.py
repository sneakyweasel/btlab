"""One-step Juggler image-parity discrepancy. Not a halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.parity_discrepancy import (
    CLASS_PARK,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    anti_overclaim,
    even_count_inclusive,
    even_discrepancy,
    even_discrepancy_bound,
    even_image_odd_count,
    image_odd,
    lean_api_present,
    prefix_census,
    scan,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_even_count_inclusive():
    assert even_count_inclusive(1, 3) == 1
    assert even_count_inclusive(4, 8) == 3
    assert even_count_inclusive(9, 10) == 1
    assert even_count_inclusive(5, 4) == 0


def test_even_closed_form_matches_brute():
    even_odd = 0
    for n in range(1, 501):
        if n % 2 == 0 and image_odd(n):
            even_odd += 1
        assert even_image_odd_count(n) == even_odd
        assert abs(even_discrepancy(n)) <= even_discrepancy_bound(n)


def test_image_odd_is_floor_power_parity():
    for n in (1, 2, 3, 7, 9, 10, 16, 365, 3889):
        assert image_odd(n) is (floor_power(n) % 2 == 1)


def test_odd_two_step_follows_image_parity():
    for n in range(3, 200, 2):
        nxt = floor_power(n)
        two = floor_power(nxt)
        if nxt % 2 == 0:
            assert two < n
        else:
            assert two > n


def test_prefix_split_and_even_bound():
    census = prefix_census(2000)
    assert census["even_bound_holds"] is True
    assert census["closed_matches"] is True
    final = census["final"]
    assert final["O"] == final["O_E"] + final["O_O"]
    assert abs(final["D"] - (final["D_E"] + final["D_O"])) < 1e-9
    assert abs(final["D_O"]) < 0.01 * 2000
    assert even_image_odd_count(2000) == final["O_E"]


def test_scan_parks_without_flipping_frequency():
    row = scan(n_max=4000, n_spot=None)
    assert row["decision"]["classification"] == CLASS_PARK
    assert row["decision"]["branch"] == "PARK"
    assert row["decision"]["odd_start_proof"] is False
    assert row["anti_overclaim"]["parity_frequency_theorem"] is False
    assert row["anti_overclaim"]["iterate_counting_estimates"] is False
    assert row["census"]["even_bound_holds"] is True


def test_lean_and_anti_overclaim():
    lean = lean_api_present()
    assert lean["sorry_free"]
    assert lean["even_preimage_iff"]
    assert lean["odd_preimage_unique"]
    assert lean["floorPower_odd_macro_direction"]
    assert lean["landingParity_odd_iff"]
    assert lean["ooe_cylinder_both_next_parities"]
    assert lean["no_forbidden_engines"]
    anti = anti_overclaim()
    assert anti["parity_frequency_theorem"] is False
    assert anti["reopen_landing_theta"] is False
    assert anti["reopen_2adic_bridge"] is False
    assert anti["odd_start_bound_is_theorem"] is False


def test_records_park():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["census"]["closed_matches"] is True
    assert data["census"]["even_bound_holds"] is True
    assert data["anti_overclaim"]["parity_frequency_theorem"] is False
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "PARK" in text.split("## Decision", 1)[1]
    assert "## Publication assessment" in text
    assert (DATA_DIR / "manifest.json").is_file()
    assert (DATA_DIR / "checkpoints.csv").is_file()
    assert (DATA_DIR / "odd_start_spot.csv").is_file()
