"""Odd-start sharp even-tower suffixes. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

import json

from research.juggler_sequence.odd_sharp_suffix import (
    ANALYSIS_DIR,
    CLASS_INCOMPLETE,
    CLASS_WITNESS,
    HITS_DIR,
    LEAN_THEOREMS,
    analyze_even_cbrt_moduli,
    analyze_even_cbrt_near_misses,
    analyze_diophantine_gap,
    analyze_near_power_gap,
    analyze_persisted_hits,
    classify,
    cube_in_sq_interval,
    eighth_in_exact_family_cell,
    even_cbrt_surplus_record,
    even_start_contrast,
    example_records,
    hit_record,
    integer_cbrt,
    is_cube,
    lean_api_present,
    near_power_record,
    nearest_cube_record,
    window_scale_record,
    nearest_cube_signed,
    odd_floor_cube_interval,
    render_markdown,
    run_probe,
    scan_fourth_powers,
    scan_odd_starts,
    write_nearest_cube_analysis,
)
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power
from research.juggler_sequence.saturation_budget import has_pow_two_depth, square_depth


def test_integer_cbrt_and_interval_iff():
    assert integer_cbrt(0) == 0
    assert integer_cbrt(1) == 1
    assert integer_cbrt(26) == 2
    assert integer_cbrt(27) == 3
    assert integer_cbrt(28) == 3
    for n in range(1, 200, 2):
        image = floor_power(n)
        assert odd_floor_cube_interval(n, image) is True
        assert odd_floor_cube_interval(n, image + 1) is False
        if image:
            assert odd_floor_cube_interval(n, image - 1) is False


def test_eleven_is_sharp_oe_not_oe2():
    rec = hit_record(11)
    assert rec["T"] == 36
    assert rec["s"] == 1
    assert rec["base"] == 6
    assert rec["square_depth"] == 1
    assert rec["parity"] == "odd"
    assert rec["first_defect"] is True
    assert rec["sharp_suffix_length"] == 1
    assert has_pow_two_depth(36, 1) is True
    assert has_pow_two_depth(36, 2) is False
    assert local_tight(11) is False
    assert odd_floor_cube_interval(11, 36) is True
    assert 6**4 <= 11**3 < (6**2 + 1) ** 2


def test_no_odd_depth_two_on_small_window():
    scan = scan_odd_starts(2000)
    assert scan["first_defect_depth_ge_two_count"] == 0
    assert scan["s1_base_square_count"] == 0
    assert scan["max_s"] == 1
    ns = [row["n"] for row in scan["first_defect_depth_ge_one"]]
    assert 11 in ns
    assert 37 in ns
    for row in scan["first_defect_depth_ge_one"]:
        assert row["parity"] == "odd"
        assert row["first_defect"] is True
        assert row["s"] == 1
        assert not is_square(row["base"])


def test_fourth_power_even_hit_is_not_odd():
    fourth = scan_fourth_powers(120)
    assert fourth["odd_hit_count"] == 0
    ns = [hit["n"] for hit in fourth["even_hits"]]
    assert 198636 in ns
    b97 = next(hit for hit in fourth["even_hits"] if hit["b"] == 97)
    assert b97["n"] % 2 == 0
    assert cube_in_sq_interval(97**4) == 198636
    assert 198636**3 - (97**4) ** 2 < 2 * (97**4) + 1


def test_even_start_depths_grow():
    contrast = even_start_contrast()
    assert contrast["all_even"] is True
    assert contrast["all_first_defect"] is True
    assert contrast["depths"] == [1, 2, 3]
    eighteen = hit_record(18)
    assert eighteen["parity"] == "even"
    assert eighteen["T"] == 4
    assert square_depth(4) == 1


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["oe_eleven"]["n"] == 11
    assert examples["oe_eleven"]["sharp_suffix_length"] == 1
    assert examples["eleven_interval"] is True
    assert examples["even_fourth_b97_n"] == 198636
    assert examples["even_fourth_b97_parity"] == "even"
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["impossible_theorem"] is False
    assert lean["PowerHeight_absent"] is True
    assert lean["PowerBoundStrict_absent"] is True
    assert lean["mixed_word_power_lt_absent"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "theorem mixed_word_power_lt" not in text


def test_classify_incomplete_without_witness():
    scan = run_probe(n_max=400, b_max=120, a8_max=20)
    assert scan["odd_scan"]["first_defect_depth_ge_two_count"] == 0
    assert scan["fourth_powers"]["odd_hit_count"] == 0
    lean = lean_api_present()
    decision = classify(
        scan["odd_scan"], scan["fourth_powers"], scan["eighth_powers"], lean
    )
    assert decision["classification"] == CLASS_INCOMPLETE
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_INCOMPLETE in text
    assert CLASS_WITNESS not in text or "ODD_SHARP_SUFFIX_WITNESS" not in (
        decision["classification"],
    )
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_nearest_cube_exact_family_and_a97():
    for k, a, n in ((3, 27, 6561), (5, 125, 390625), (7, 343, 5764801)):
        rec = nearest_cube_record(a, n)
        assert rec["r"] == 0
        assert rec["n_eq_m"] is True
        assert rec["a_is_cube"] is True
        assert rec["n"] == k**8
        assert rec["n_is_odd"] is True
        assert rec["n_is_square"] is True
    rec97 = nearest_cube_record(97, 198636)
    assert rec97["a_is_cube"] is False
    assert rec97["n_eq_m_plus_1"] is True
    assert rec97["n"] == rec97["m"] + 1
    assert rec97["n_is_odd"] is False
    assert rec97["gap"] <= rec97["width"]
    assert rec97["m_odd"] is True
    assert is_cube(27) is True
    assert is_cube(97) is False
    surplus97 = even_cbrt_surplus_record(97)
    assert surplus97["m_even"] is False
    assert surplus97["in_window"] is True
    assert surplus97["surplus"] < 0
    rec3 = even_cbrt_surplus_record(3)
    assert rec3["m"] == 18
    assert rec3["m_even"] is True
    assert rec3["in_window"] is False
    assert rec3["surplus"] > 0


def test_even_cbrt_discovery_has_no_window_hit():
    analysis = analyze_even_cbrt_near_misses(a_max=200)
    assert analysis["even_m_in_window_count"] == 0
    assert analysis["a97"]["in_window"] is True
    assert analysis["a97"]["m_even"] is False
    assert analysis["a3"]["m_even"] is True
    assert analysis["a3"]["in_window"] is False
    assert analysis["high_position_example"]["m_even"] is True
    assert analysis["high_position_example"]["in_window"] is False
    assert analysis["trivial_cbrt_bound_cannot_threshold"] is True
    min_s = analysis["min_surplus"]
    assert min_s is not None
    assert min_s["a"] == 2
    assert min_s["surplus"] > 0


def test_committed_even_cbrt_analysis():
    path = ANALYSIS_DIR / "even_cbrt.json"
    assert path.is_file()
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["even_m_in_window_count"] == 0
    assert data["a97"]["in_window"] is True
    assert data["a3"]["m_even"] is True
    assert data["high_position_example"]["in_window"] is False
    md = (ANALYSIS_DIR / "even_cbrt.md").read_text(encoding="utf-8")
    assert "a = 97 must survive" in md
    assert "10^8" in md
    assert "not a theorem" in md


def test_even_cbrt_moduli_parity_and_a97():
    rec2 = even_cbrt_surplus_record(2)
    rec3 = even_cbrt_surplus_record(3)
    rec97 = even_cbrt_surplus_record(97)
    assert rec2["m_even"] is True and rec2["a_odd"] is False
    assert rec2["gap"] % 2 == 1
    assert rec3["m_even"] is True and rec3["a_odd"] is True
    assert rec3["gap"] % 2 == 0
    assert rec97["m_even"] is False and rec97["in_window"] is True
    assert rec97["gap"] % 2 == 1
    analysis = analyze_even_cbrt_moduli(a_max=200)
    assert analysis["even_m_window_count"] == 0
    assert analysis["a97_survives"] is True
    assert analysis["parity"]["m_even_a_even_implies_D_odd"] is True
    assert analysis["parity"]["m_even_a_odd_implies_D_even"] is True
    assert analysis["odd_a_eighth_mod32"] == [1]
    assert analysis["odd_a_two_a4_mod32"] == [2]
    assert analysis["candidates"]["A_pure_parity"] is False
    assert analysis["candidates"]["B_pow2_empty_even_m"] is False
    assert analysis["candidates"]["C_mixed_empty_even_m"] is False
    assert analysis["candidates"]["D_modular_plus_size"] is False
    assert analysis["candidates"]["E_not_modular"] is True
    assert analysis["classification"] == "OBSTRUCTION_NOT_MODULAR"
    for row in analysis["modulus_tables"]:
        assert row["even_m_empty"] is False
    for residue in analysis["r_mod32_odd_a_even_m"]:
        assert int(residue) in (1, 9, 25)


def test_committed_even_cbrt_moduli_analysis():
    path = ANALYSIS_DIR / "even_cbrt_moduli.json"
    assert path.is_file()
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["classification"] == "OBSTRUCTION_NOT_MODULAR"
    assert data["a97_survives"] is True
    assert data["even_m_window_count"] == 0
    assert data["candidates"]["E_not_modular"] is True
    md = (ANALYSIS_DIR / "even_cbrt_moduli.md").read_text(encoding="utf-8")
    assert "a = 97 regression" in md
    assert "OBSTRUCTION_NOT_MODULAR" in md


def test_near_power_exact_cell_and_a97():
    assert nearest_cube_signed(27) == (3, 0)
    assert nearest_cube_signed(97) == (5, -28)
    assert nearest_cube_signed(3) == (1, 2)
    rec97 = near_power_record(97)
    assert rec97["a_is_cube"] is False
    assert rec97["m_even"] is False
    assert rec97["in_window"] is True
    assert rec97["leaves_exact_cell"] is True
    assert rec97["same_sign_uv"] is True
    rec3 = near_power_record(3)
    assert rec3["m_even"] is True
    assert rec3["in_window"] is False
    assert rec3["u"] == 2
    rec27 = near_power_record(27)
    assert rec27["a_is_cube"] is True
    assert rec27["u"] == 0
    assert rec27["v"] == 0
    assert rec27["leaves_exact_cell"] is False
    for k in range(1, 12):
        assert eighth_in_exact_family_cell(k**3, k) is True
        assert eighth_in_exact_family_cell(k**3 + 1, k) is False
        if k**3 > 1:
            assert eighth_in_exact_family_cell(k**3 - 1, k) is False
    analysis = analyze_near_power_gap(a_max=200, k_max=8, u_radius=3)
    assert analysis["even_m_in_window_count"] == 0
    assert analysis["a97_survives"] is True
    assert analysis["routes"]["A_unrestricted_noncube_gap"] is False
    assert analysis["routes"]["B_exact_family_cell_exclusive"] is True
    assert analysis["routes"]["B_leaves_cell_implies_miss"] is False
    assert analysis["routes"]["C_fourth_power_rigidity_elementary"] is False
    assert analysis["routes"]["D_trivial_gap_threshold"] is False
    assert analysis["classification"] == "DIOPHANTINE_ESCALATION_REQUIRED"
    assert analysis["u1_window_count"] == 0
    assert analysis["u1_stays_in_ref_cell"] == 0


def test_committed_near_power_analysis():
    path = ANALYSIS_DIR / "near_power.json"
    assert path.is_file()
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["classification"] == "DIOPHANTINE_ESCALATION_REQUIRED"
    assert data["a97_survives"] is True
    assert data["even_m_in_window_count"] == 0
    assert data["routes"]["A_unrestricted_noncube_gap"] is False
    assert data["routes"]["B_exact_family_cell_exclusive"] is True
    assert data["routes"]["B_leaves_cell_implies_miss"] is False
    md = (ANALYSIS_DIR / "near_power.md").read_text(encoding="utf-8")
    assert "a = 97 must survive" in md
    assert "DIOPHANTINE_ESCALATION_REQUIRED" in md
    assert "10^8" in md


def test_diophantine_gap_scale_and_a97():
    rec27 = window_scale_record(27, 6561)
    assert rec27["r"] == 0
    assert rec27["b"] == 27**2
    rec97 = window_scale_record(97, 198636)
    assert rec97["r_positive"] is True
    assert rec97["r_le_two_b2"] is True
    assert rec97["n_odd"] is False
    rec3 = window_scale_record(3)
    assert rec3["r_le_two_b2"] is False
    assert rec3["m_even"] is True
    analysis = analyze_diophantine_gap()
    assert analysis["odd_nonsquare_hit_count"] == 0
    assert analysis["positive_r_count"] == 1
    assert analysis["a97_survives"] is True
    assert analysis["any_theorem_beats_2b2"] is False
    assert analysis["classification"] == "DIOPHANTINE_ESCALATION_REQUIRED"
    assert all(not row["beats_2b2"] for row in analysis["theorems"])
    assert all(row["a97_legal"] for row in analysis["theorems"])


def test_committed_diophantine_gap_analysis():
    path = ANALYSIS_DIR / "diophantine_gap.json"
    assert path.is_file()
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["classification"] == "DIOPHANTINE_ESCALATION_REQUIRED"
    assert data["a97_survives"] is True
    assert data["any_theorem_beats_2b2"] is False
    assert data["odd_nonsquare_hit_count"] == 0
    md = (ANALYSIS_DIR / "diophantine_gap.md").read_text(encoding="utf-8")
    assert "a = 97 must survive" in md
    assert "Hall" in md
    assert "DIOPHANTINE_ESCALATION_REQUIRED" in md


def test_persisted_hits_nearest_cube_split():
    analysis = analyze_persisted_hits()
    assert analysis["hit_count"] == 465
    assert analysis["exact_cube_count"] == 464
    assert analysis["a97_count"] == 1
    assert analysis["other_count"] == 0
    assert analysis["odd_non_square_count"] == 0
    assert analysis["inexact_is_succ_cbrt"] is True
    assert analysis["odd_cbrt_inexact_even_n"] is True
    assert analysis["odd_a_need_not_force_m_odd"] is True
    assert analysis["exact_left_endpoint"] is True
    assert integer_cbrt(3**8) == 18
    assert analysis["a97"]["n"] == 198636
    assert HITS_DIR.is_dir()
    committed = json.loads((ANALYSIS_DIR / "nearest_cube.json").read_text(encoding="utf-8"))
    assert committed["odd_a_need_not_force_m_odd"] is True
    assert committed["inexact_is_succ_cbrt"] is True
    assert "odd_a_forces_m_odd" not in committed
    md = (ANALYSIS_DIR / "nearest_cube.md").read_text(encoding="utf-8")
    assert "odd `a` need not force odd `m`" in md
    assert "odd a forces m odd" not in md.lower()


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.odd_sharp_suffix import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_INCOMPLETE
    assert data["scan"]["odd_scan"]["first_defect_depth_ge_two_count"] == 0
    assert data["scan"]["fourth_powers"]["odd_hit_count"] == 0
    assert data["lean"]["floorPower_odd_eq_iff_cube_interval"] is True
    assert data["lean"]["odd_cube_interval_of_odd_cbrt_implies_square"] is True
    assert data["lean"]["odd_first_defect_not_pow_two_depth_ge_two_of_odd_cbrt"] is True
    assert data["lean"]["impossible_theorem"] is False
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["oe_eleven"]["n"] == 11
