"""Finite-dynamics companion instantiates the note; it does not halt."""

from visualization.juggler_finite_dynamics import (
    CYCLE_WORD_MAX,
    EEEE_WORD,
    LAB_WALK_PERIOD,
    LEFTOVER_CUTOFF,
    NOTE_TRAJECTORY_3,
    NOTE_PEAK_37,
    PAPER_EXCEPTION_COUNT,
    PAPER_PERIOD,
    PRINTED_FLOOR,
    PRINTED_KILL_COUNT,
    PRINTED_PERIOD,
    WORD_MAX,
    lab_walk_survey,
    printed_floor_kill_rows,
    classify_word,
    compose_view,
    cycle_class_view,
    descent_view,
    descent_window,
    envelope_view,
    even_preimage_view,
    finance_view,
    four_block_replay,
    leftover_table,
    leftover_words,
    length11_inventory,
    length_eight_open_words,
    length_eight_status_rows,
    next_square_view,
    odd_preimage_view,
    paper_exception_lengths,
    parse_cycle_word,
    parse_word,
    rotate_cycle_word,
    try_cycle_word,
    walk_trajectory,
)


def test_orbit_of_three_matches_the_note():
    view = walk_trajectory(3, 20)
    assert view.states == NOTE_TRAJECTORY_3
    assert view.word == "OOOEEE"
    assert view.reached_one
    assert not view.too_large


def test_orbit_of_thirty_seven_records_the_note_peak():
    view = walk_trajectory(37, 80)
    assert NOTE_PEAK_37 in view.states
    assert view.reached_one
    assert not view.bit_capped


def test_envelope_identity_on_one_odd_letter():
    view = envelope_view(3, "O")
    assert view.follows
    assert view.image == 5
    assert view.slack == 2
    assert view.delta == 2
    assert view.regime == "expanding"
    assert view.vanishing == "monochrome but a local remainder is positive"


def test_mixed_word_is_strictly_positive():
    view = envelope_view(5, "OOE")
    assert view.follows
    assert view.image == 6
    assert not view.monochrome
    assert view.vanishing == "mixed word, Δ > 0"
    if view.slack is not None:
        assert view.slack > 0


def test_compose_matches_when_budget_allows():
    view = compose_view(3, "O", "O")
    assert view.follows
    assert view.mid == 5
    assert view.end == 11
    if not view.too_large and view.composed is not None:
        assert view.composed == view.delta_uv


def test_leftover_tables_have_no_returns():
    for word, cutoff in LEFTOVER_CUTOFF.items():
        table = leftover_table(word)
        assert table.n_hi == cutoff
        assert table.checked == cutoff - 2
        assert table.hits == ()
        assert not any(row["returned"] for row in table.rows)


def test_leftover_words_are_the_note_four():
    assert leftover_words() == ("OOOEOE", "OOOOEE", "OOOOEOE", "OOOOOEE")


def test_classify_leftovers_and_open_length_nine():
    assert classify_word("OOOEOE").kind == "leftover"
    assert classify_word("OOOOEE").kind == "leftover"
    assert classify_word("OOOOEOE").kind == "leftover"
    assert classify_word("OOOOOEE").kind == "leftover"
    assert classify_word("OOOOOE").kind == "odd-run"
    assert classify_word("OOE").kind == "threshold"
    for word in length_eight_open_words():
        info = classify_word(word)
        assert info.kind != "open", word
        assert "open" not in info.reason
    length11 = cycle_class_view(EEEE_WORD, 0)
    assert length11.verdict == "excluded"
    assert "25780" in length11.verdict_reason or "4.6" in length11.verdict_reason


def test_length_eight_open_list_is_expanding_and_even_terminating():
    words = length_eight_open_words()
    assert words
    assert all(len(word) == 8 and word.endswith("E") for word in words)
    assert all(2 ** 8 < 3 ** word.count("O") for word in words)


def test_descent_buckets_of_note_starts():
    even = descent_view(2)
    assert even.bucket == "EVEN_PROGRESS"
    assert even.certificate == "E"
    odd_odd = descent_view(3)
    assert odd_odd.bucket == "ODD_ODD"
    oe = descent_view(7)
    assert oe.bucket == "OE_PROGRESS"
    assert oe.certificate == "OE"


def test_descent_window_is_a_count_not_a_density():
    counts = descent_window(80)
    assert counts["n_max"] == 80
    assert counts["EVEN_PROGRESS"] + counts["OE_PROGRESS"] + counts["ODD_ODD"] == 79
    assert counts["EVEN_PROGRESS"] > 0
    assert counts["ODD_ODD"] > 0


def test_four_block_chain_replays_the_note():
    chain = four_block_replay()
    assert [step.start for step in chain] == [1999, 5169, 50093, 193753]
    assert [step.word for step in chain] == ["OOE", "OOOOEE", "OOE", "OOE"]
    assert [step.image for step in chain] == [5169, 50093, 193753, 887471]
    assert all(step.matches for step in chain)


def test_next_square_on_three_and_five():
    at_three = next_square_view(3, "OO")
    assert at_three.follows
    assert at_three.image == 11
    assert at_three.met is False
    at_five = next_square_view(5, "OO")
    assert at_five.follows
    assert at_five.met is True


def test_cells_match_floor_geometry():
    even = even_preimage_view(6)
    assert even.lo == 36
    assert even.hi == 49
    assert 36 in even.evens
    assert 48 in even.evens
    odd = odd_preimage_view(11)
    assert odd.integers == (5,)


def test_parse_word_rejects_overlong_and_junk():
    assert parse_word("ooe") == "OOE"
    assert parse_word("O O E") == "OOE"
    assert parse_word("") == ""
    assert parse_word("OX") is None
    assert parse_word("O" * (WORD_MAX + 1)) is None


def test_parse_cycle_word_allows_two_even_lengths():
    assert parse_cycle_word("ooooooee") == "OOOOOOEE"
    assert parse_cycle_word("O" * CYCLE_WORD_MAX) == "O" * CYCLE_WORD_MAX
    assert parse_cycle_word("O" * (CYCLE_WORD_MAX + 1)) is None
    assert parse_cycle_word("OX") is None


def test_oeo_rotates_onto_ooe_and_is_excluded():
    assert rotate_cycle_word("OEO", 1) == "EOO"
    assert rotate_cycle_word("OEO", 2) == "OOE"
    view = cycle_class_view("OEO", 0)
    assert view.current == "OEO"
    assert view.current_kind == "odd-terminating"
    assert "OOE" in view.current_reason
    assert view.legal_reps == ("OOE",)
    assert view.verdict == "excluded"
    assert view.steps[-1].status == "blocks"
    rotated = cycle_class_view("OEO", 2)
    assert rotated.current == "OOE"
    assert rotated.current_kind == "threshold"
    assert rotated.current_legal
    assert rotated.verdict == "excluded"


def test_eooooe_rotates_onto_leftover():
    view = cycle_class_view("EOOOOE", 0)
    assert view.current_kind == "rotation"
    assert "OOOOEE" in view.current_reason
    assert view.verdict == "excluded"
    leftover = cycle_class_view("EOOOOE", 1)
    assert leftover.current == "OOOOEE"
    assert leftover.current_kind == "leftover"
    assert leftover.current_legal


def test_oeoooe_rotates_onto_eoe_leftover():
    view = cycle_class_view("OEOOOE", 0)
    assert view.current_kind == "not CycleMin"
    assert "OOOEOE" in view.current_reason
    assert view.verdict == "excluded"


def test_two_even_length_eight_is_excluded():
    view = cycle_class_view("OOOOOOEE", 0)
    assert view.verdict == "excluded"
    assert view.current_kind == "two-even leftover"
    assert view.ledger == "J-two-even-leftover-ee"


def test_length_eight_bootstrap_shapes_are_excluded():
    view = cycle_class_view("OOEOOOOE", 0)
    assert view.verdict == "excluded"
    assert view.current_kind == "bootstrap"
    assert view.steps[-1].status == "blocks"


def test_gapped_and_bunched_three_even_are_excluded():
    gapped = cycle_class_view("OOEOOOOEE", 0)
    assert gapped.verdict == "excluded"
    assert gapped.current_kind == "gapped leftover"
    assert gapped.ledger == "J-gapped-cycle-word-ee"
    bunched = cycle_class_view("OOOOOOOEEE", 0)
    assert bunched.verdict == "excluded"
    assert bunched.current_kind == "bunched leftover"
    assert bunched.ledger == "J-three-even-eee"


def test_length11_short_gap_is_excluded_by_finance():
    view = cycle_class_view(EEEE_WORD, 0)
    assert view.current_kind == "four-even short-gap"
    assert view.verdict == "excluded"
    assert view.current_legal
    assert view.ledger == "J-cycle-word-eliahou-leftover-instance"
    mixed = cycle_class_view("OOEOOOOOEEE", 0)
    assert mixed.current_kind == "four-even short-gap"
    assert mixed.verdict == "excluded"


def test_paper_finance_table_matches_theorem_4_6():
    lengths = paper_exception_lengths()
    assert len(lengths) == PAPER_EXCEPTION_COUNT
    assert lengths[0] == PAPER_PERIOD
    eleven = finance_view(11)
    assert eleven.excluded_by_floor
    assert eleven.n_max == 25
    old_record = finance_view(1054)
    assert old_record.excluded_by_floor
    assert old_record.n_max == 788_014
    first = finance_view(PAPER_PERIOD)
    assert first.admissible
    assert first.n_max == 26_254_995
    assert not first.excluded_by_floor


def test_printed_walk_charge_matches_corollary_5_10():
    survey = lab_walk_survey()
    assert survey["floor"] == 26_254_995
    assert survey["combined_first_survivor"] == LAB_WALK_PERIOD
    rows = printed_floor_kill_rows()
    below = [row for row in rows if row.length < PRINTED_PERIOD]
    assert len(below) == PRINTED_KILL_COUNT
    assert all(row.excluded for row in below)
    blocker = next(row for row in rows if row.length == PRINTED_PERIOD)
    assert blocker.status == "blocker"
    assert not blocker.excluded
    assert rows[0].length == LAB_WALK_PERIOD
    leftovers = [row for row in rows if row.length > PRINTED_PERIOD]
    assert leftovers
    assert all(not row.excluded for row in leftovers)
    assert PRINTED_FLOOR == 350_000_000
    assert PRINTED_PERIOD == 780_239


def test_length11_inventory_is_thirty_first_expanding_words():
    rows = length11_inventory()
    assert len(rows) == 30
    words = {row["word"] for row in rows}
    assert EEEE_WORD in words
    assert "OOEOOOOOEEE" in words
    assert all(len(row["word"]) == 11 for row in rows)


def test_classify_word_marks_two_even_length_eight():
    info = classify_word("OOOOOOEE")
    assert info.kind == "two-even leftover"
    rows = {row["word"]: row for row in length_eight_status_rows()}
    assert rows["OOOOOOEE"]["note"].startswith("Theorem 3.12")
    assert "odd-run threshold" in rows["OOEOOOOE"]["note"]
    assert "not a leftover" in rows["OOOOEOOE"]["note"]
    assert "not a leftover" in rows["OOOEOOOE"]["note"]
    squares = cycle_class_view("OOOOEOOE", 0)
    assert squares.current_kind == "bootstrap"
    assert squares.verdict == "excluded"
    copy = cycle_class_view("OOOEOOOE", 0)
    assert copy.current_kind == "bootstrap"
    assert copy.verdict == "excluded"


def test_all_odd_cannot_close():
    view = cycle_class_view("OOOOOO", 0)
    assert view.verdict == "excluded"
    assert view.current_kind == "all-odd"


def test_try_cycle_word_records_a_miss_and_a_nonreturn():
    miss = try_cycle_word(3, "OEO")
    assert not miss.follows
    assert miss.fail_index == 1
    walk = try_cycle_word(3, "OOOEEE")
    assert walk.follows
    assert walk.returned is False
    assert walk.image == 1
    empty = try_cycle_word(3, "")
    assert empty.follows
    assert empty.returned is False


def test_bit_cap_refuses_a_huge_start():
    huge = 1 << 300
    view = walk_trajectory(huge, 4)
    assert view.too_large
    slack = envelope_view(10**12 + 1, "O")
    assert slack.follows
    assert slack.slack_too_large
