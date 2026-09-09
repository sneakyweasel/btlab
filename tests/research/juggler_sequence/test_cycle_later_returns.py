"""Exact fixed-word and archived terminal checks; no expanded census."""
import json
from fractions import Fraction

import pytest

from research.juggler_sequence import cycle_later_returns as later


@pytest.fixture(scope="module")
def data():
    return later.report()


def test_archive_matches_recomputed_report(data):
    path = later.DATA_ROOT / "cycle_later_returns/summary.json"
    assert json.loads(path.read_text(encoding="utf-8")) == data


def test_fixed_words_prefixes_and_all_64_dyadic_terms(data):
    records = data["constant_checks"]["words"]
    assert {name: (row["length"], row["odd_count"]) for name, row in records.items()} == {
        "A": (3, 2), "C": (8, 5), "D": (19, 12), "W": (65, 41), "V": (84, 53)}
    for row in records.values():
        value = Fraction(1)
        for letter, recorded in zip(row["word"], row["nonempty_prefix_exponents"]):
            value *= Fraction(3, 2) if letter == "O" else Fraction(1, 2)
            assert value == Fraction(recorded)
        assert value == Fraction(3**row["odd_count"], 2**row["length"])
    constants = data["constant_checks"]
    tails = list(map(Fraction, constants["W_proper_tail_exponents"]))
    majorants = list(map(Fraction, constants["W_dyadic_majorants"]))
    assert len(tails) == len(majorants) == 64
    for q, bound in zip(tails, majorants):
        exponent = 128*(1-q)
        k = exponent.numerator//exponent.denominator
        assert 0 < q < 1 and k <= exponent < k+1
        assert bound == q/Fraction(2**k)
    assert sum(majorants) == Fraction(constants["W_tail_sum"]) < Fraction(1, 5)


def test_three_transfer_constants_and_clean_certificate_are_distinguished(data):
    constants = data["constant_checks"]
    gamma = Fraction(constants["words"]["C"]["ideal_exponent"])
    rho = Fraction(constants["words"]["W"]["ideal_exponent"])
    numerator = Fraction(4, 5)-Fraction(9, 8)*Fraction(3, 8)*Fraction(65, 64)
    assert numerator == Fraction(7609, 20480)
    assert Fraction(constants["sharp_gap_coefficient_C0"]) == numerator/(gamma**2*rho) > Fraction(2, 5)
    sigma = Fraction(constants["sharp_gap_exponent_sigma"])
    theta = Fraction(constants["sharp_written_height_exponent_theta"])
    assert sigma == Fraction(13, 128)+1-rho and Fraction(7, 64) < sigma < Fraction(1, 8)
    assert theta == Fraction(15, 8)+sigma == Fraction(381, 128)-rho
    assert Fraction(127, 64) < theta < 2
    assert constants["clean_height_strip_exponent"] == "127/64"
    assert not data["conditional_ceiling"]["sharp_rational_power_evaluated"]


def test_stage_exponent_and_exact_word_factorizations(data):
    for row in data["archived_cycles"]:
        expected = Fraction(row["total_ideal_exponent"])
        for stage in row["stages"]:
            assert Fraction(stage["lower_exponent"])**stage["a"]*Fraction(stage["upper_exponent"])**stage["b"] == expected
            if stage["a"] and stage["b"]:
                U, V = stage["lower_word"], stage["upper_word"]
                P, Q = stage["common_prefix_P"], stage["common_suffix_Q"]
                assert U+V == P+"OE"+Q and V+U == P+"EO"+Q
        assert row["wrong_parity_sources"] and not row["actual_juggler_cycle"]
        assert not row["off_domain_lower_guard_asserted"]


def test_terminal_traces_use_only_the_archived_cells(data):
    excluded = []
    for row in data["archived_cycles"]:
        terminal = row["terminal"]
        if terminal is None:
            excluded.append(row["minimum"])
            continue
        cells = {cell["source"]: cell for cell in row["original_cells"]}
        m, v = terminal["states"]
        P, Q = terminal["common_prefix_P"], terminal["common_suffix_Q"]
        groups = ((terminal["prefix_traces"], (P, P)),
                  (terminal["mixed_traces"], ("OE", "EO")),
                  (terminal["suffix_traces"], (Q, Q)))
        for traces, words in groups:
            for trace, word in zip(traces, words):
                assert len(trace) == len(word)+1 <= len(cells)+1
                for x, y, letter in zip(trace, trace[1:], word):
                    assert cells[x]["image"] == y and cells[x]["branch"] == letter
                    N = x**3 if letter == "O" else x
                    assert y*y <= N < (y+1)**2
        p, h = (trace[-1] for trace in terminal["prefix_traces"])
        assert p == max(x for x, cell in cells.items() if cell["branch"] == "O")
        assert h == min(x for x, cell in cells.items() if cell["branch"] == "E")
        assert terminal["suffix_traces"][0][-1] == m
        assert terminal["suffix_traces"][1][-1] == v
        if terminal["mixed_actual_parity_hypotheses"]:
            assert terminal["mixed_image_gap"] < terminal["mixed_source_gap"]
        assert terminal["terminal_section_size"] == 1
        assert not terminal["extra_seam_transfer"] and not terminal["off_domain_lower_guard_asserted"]
    assert excluded == [3, 4]


def test_one_conditional_ceiling_is_exact_and_stronger(data):
    row = data["conditional_ceiling"]
    m, G, z, T = (row[key] for key in ("minimum", "least_even_gap", "odd_projected_return", "max_retained_odd_base"))
    assert m == 2**128+1 and G >= 8 and G % 2 == 0
    assert (5*(G-2))**64 <= 2**64*m**7 < (5*G)**64
    assert z % 2 == T % 2 == 1 and z**8 <= m**9 < (z+2)**8
    assert T**3+2 <= ((z-G)*(z-G+2))**2 < (T+2)**3+2
    cap = row["new_maximum_ceiling"]
    assert cap == (T+1)**2-2 < row["previous_direction_change_ceiling"] < m**3
    assert (2*(m**3-cap))**64 > m**127
    assert row["periodicity"].startswith("not asserted")


def test_scope_forbids_all_reports_and_new_searches(monkeypatch):
    from research.juggler_sequence import cycle_cubic_band as cubic
    from research.juggler_sequence import cycle_cubic_induction as induction
    from research.juggler_sequence import cycle_direction_change as direction
    def forbidden(*args, **kwargs):
        raise AssertionError("later-return controls must not expand a report, source census or cycle search")
    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    monkeypatch.setattr(induction, "report", forbidden)
    monkeypatch.setattr(direction, "report", forbidden)
    replay, ceiling = direction.archived_cycle_record, direction.ceiling_record
    cycle_calls, minimum_calls = [], []
    def bounded_replay(b, states):
        cycle_calls.append((b, states))
        return replay(b, states)
    def bounded_ceiling(m):
        minimum_calls.append(m)
        return ceiling(m)
    monkeypatch.setattr(direction, "archived_cycle_record", bounded_replay)
    monkeypatch.setattr(direction, "ceiling_record", bounded_ceiling)
    got = later.report()
    assert cycle_calls == list(later.ABSOLUTE_CELL_THRESHOLD_CYCLES)
    assert minimum_calls == [2**128+1]
    assert got["scope"]["ceiling_minima"] == [2**128+1]
    for key in ("cycle_search", "source_census", "rank_pair_scan", "trajectory_extension", "descent_floor_increase"):
        assert not got["scope"][key]
    for key in ("uniform_fixed_minimum_certificate", "new_theorem_formalized_in_lean",
                "uniform_gap_propagation_proved", "universal_wrong_parity_proved", "tall_cycles_excluded",
                "new_period_bound", "no_cycle_proved"):
        assert not got[key]


def test_domain_and_explicit_output_path(tmp_path, capsys, data):
    for m in (-1, 2**128-1, 2**128):
        with pytest.raises(ValueError):
            later.ceiling_record(m)
    with pytest.raises(ValueError):
        later.least_even_gap(2**128-1)
    with pytest.raises(ValueError):
        later.exponent("X")
    with pytest.raises(ValueError):
        later.follow_archived(3, "OO", {3: {"branch": "O", "image": 3}})
    path = tmp_path / "later.json"
    later.main(["--output", str(path)])
    assert json.loads(path.read_text(encoding="utf-8")) == data
    assert not json.loads(capsys.readouterr().out)["no_cycle_proved"]
