"""Guards for the external-input audit."""

from __future__ import annotations

import math

from research.juggler_sequence.external_input_audit import (
    ALPHA,
    TRANSCENDENCE_CHAIN,
    closure_exponent,
    concentration_audit,
    first_passage_gap,
    kl_exponent,
    least_C_kl,
    linear_form_exponent,
    report,
    transcendence_audit,
    transcendence_checks,
)
from research.juggler_sequence.tao_reduction import (
    chernoff_exponent,
    least_C,
    least_C_biased,
)


def test_closure_exponent_is_the_irrationality_measure() -> None:
    """The identity the whole audit turns on.

    `|Lambda| = L log3 |alpha - o/L| >= c L^(1-mu)` and `n log n <= 2L/Lambda`,
    so the exponent a minimum lower bound must beat is `mu` itself.
    """
    for mu in (2.0, 5.1163051, 14.3):
        assert closure_exponent(mu) == mu
        assert linear_form_exponent(mu) == mu - 1.0


def test_the_committed_wuwang_exponent_sits_in_the_chain() -> None:
    rows = {r["source"]: r for r in TRANSCENDENCE_CHAIN}
    assert rows["wu-wang-2014-irrationality-measure-log3"]["mu"] == 5.1163051
    assert math.isclose(
        1 / rows["wu-wang-2014-irrationality-measure-log3"]["mu"], 0.19545355, rel_tol=1e-6
    )


def test_all_transcendence_checks_pass() -> None:
    for row in transcendence_checks():
        assert row["ok"], row["check"]


def test_chain_is_ordered_and_dirichlet_is_the_floor() -> None:
    chain = transcendence_audit()
    mus = [r["mu"] for r in chain]
    assert mus == sorted(mus)
    assert mus[0] == 2.0, "Dirichlet must be the strongest entry and unbeatable"
    assert all(r["mu"] >= 2.0 for r in chain)


def test_paper_a_printed_exponent_is_beaten_by_its_own_citation() -> None:
    """The audit's finding: a sharper statement one equation further down.

    Paper A cites Rhin p.160 eq.(7) through Simons-de Weger and prints 14.3.
    Eq.(8) of the same Proposition is reported as mu <= 8.616.
    """
    rows = [r for r in TRANSCENDENCE_CHAIN if r["source"].startswith("rhin")]
    assert len(rows) == 2
    printed = max(rows, key=lambda r: r["mu"])
    ratio = min(rows, key=lambda r: r["mu"])
    assert printed["mu"] == 14.3 and ratio["mu"] == 8.616
    assert printed["verified_against_primary"] is True
    assert ratio["verified_against_primary"] is False, (
        "8.616 is a third-party report; it must not be used before someone "
        "reads Rhin p.160 eq.(8)"
    )


def test_unverified_rows_are_never_the_one_in_use() -> None:
    """An audit must not let an unchecked citation become load-bearing."""
    for row in TRANSCENDENCE_CHAIN:
        if not row["verified_against_primary"]:
            assert row["used_by"].startswith("nothing"), row["source"]


def test_kl_reproduces_chernoff_at_the_unbiased_point() -> None:
    """Confirms the reconstruction of the argument behind azuma_exponent."""
    for C in (19, 25, 41):
        assert math.isclose(kl_exponent(C, 0.5), chernoff_exponent(C), rel_tol=1e-12)


def test_azuma_is_lossy_but_the_integers_do_not_move() -> None:
    """The negative finding. Azuma is strictly weaker; C(0.5) and C(0.55) stand."""
    assert kl_exponent(19, 0.5) > 0  # sanity
    from research.juggler_sequence.tao_reduction import azuma_exponent

    assert azuma_exponent(19, 0.5) < kl_exponent(19, 0.5), "Azuma should be lossy"
    assert least_C_biased(0.5) == least_C_kl(0.5) == 19
    assert least_C_biased(0.55) == least_C_kl(0.55) == 41
    assert least_C() == 19


def test_the_only_place_the_sharper_bound_moves_anything_is_q_06() -> None:
    rows = {r["q"]: r for r in concentration_audit()}
    assert rows[0.5]["moves"] is False
    assert rows[0.55]["moves"] is False
    assert rows[0.6]["moves"] is True
    assert rows[0.6]["azuma_least_C"] == 223 and rows[0.6]["kl_least_C"] == 214


def test_first_passage_surplus_over_chernoff_vanishes() -> None:
    """The second negative finding: Chernoff already has the true rate.

    The excess is positive at every finite depth but shrinks, and
    `excess * L` grows rather than staying bounded, which is the signature of
    an `O(log L / L)` correction rather than an `O(1/L)` one. So no
    first-passage refinement can lower `least_C = 19`.
    """
    rows = first_passage_gap()
    excess = [r["excess"] for r in rows]
    assert all(e > 0 for e in excess)
    assert excess == sorted(excess, reverse=True), "the surplus must shrink"
    scaled = [r["excess_times_L"] for r in rows]
    assert scaled == sorted(scaled), "excess*L grows: the correction is log L / L"
    assert all(r["exact_exponent"] > r["chernoff_bound"] for r in rows)


def test_report_is_self_consistent() -> None:
    data = report()
    assert data["all_transcendence_checks_ok"]
    assert data["concentration_constants_move"] is False
    assert data["first_passage_excess_shrinks"] is True
    assert data["unverified_candidate_mu"] == 8.616
    assert data["is_halt_theorem"] is False
    assert data["new_mathematics"] is False
    assert math.isclose(data["alpha"], ALPHA)
