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


def test_wuwang_is_effective_but_uncomputed_not_ineffective() -> None:
    """`J-wuwang-import-verified-at-source`, the one refinement it asks for.

    Theorem 1, p. 266, asserts that `H_0(eps)` is effectively computable, so
    the bound IS effective in the technical sense; what the paper never does is
    compute `H_0(eps)`. The audit first recorded this row as `effective: no`,
    which is a different claim and a wrong one. The accurate entry is
    "effective but uncomputed", and it needs two fields to say it.
    """
    ww = next(
        r
        for r in TRANSCENDENCE_CHAIN
        if r["source"] == "wu-wang-2014-irrationality-measure-log3"
    )
    assert ww["verified_against_primary"] is True
    assert ww["effective"] is True, "Theorem 1 asserts H_0(eps) is effectively computable"
    assert ww["constant_computed"] is False, "and never computes it"
    assert "H_0" in ww["uncomputed_threshold"]


def test_all_transcendence_checks_pass() -> None:
    for row in transcendence_checks():
        assert row["ok"], row["check"]


def test_chain_is_ordered_and_dirichlet_is_the_floor() -> None:
    chain = transcendence_audit()
    mus = [r["mu"] for r in chain]
    assert mus == sorted(mus)
    assert mus[0] == 2.0, "Dirichlet must be the strongest entry and unbeatable"
    assert all(r["mu"] >= 2.0 for r in chain)


def test_rhin_equation_eight_is_read_at_source_and_has_no_threshold() -> None:
    """The finding this branch opened with, closed by reading p. 160.

    `J-rhin-eight-has-no-computed-threshold`: the Proposition gives (7)
    `|Lambda| >= H^(-13.3)` for `H >= 2`, then (8) `|Lambda| >= H^(-7.616)`
    only *pour H >= H_0 (H_0 effectivement calculable)* -- and `H_0` is never
    computed. So Paper A's printed 14.3 is not in fact beaten by its own
    citation: 8.616 is sharper and unreachable. The row is verified and dead
    rather than unverified and hopeful.
    """
    rows = [r for r in TRANSCENDENCE_CHAIN if r["source"].startswith("rhin")]
    assert len(rows) == 2
    printed = max(rows, key=lambda r: r["mu"])
    sharper = min(rows, key=lambda r: r["mu"])
    assert printed["mu"] == 14.3 and sharper["mu"] == 8.616
    assert printed["verified_against_primary"] is True
    assert sharper["verified_against_primary"] is True, "p.160 read at source 16 Sep 2026"
    assert printed["constant_computed"] is True
    assert sharper["effective"] is True, "Rhin declares H_0 effectivement calculable"
    assert sharper["constant_computed"] is False, "and never computes it"
    assert "H_0" in sharper["uncomputed_threshold"]
    assert sharper["used_by"].startswith("nothing")


def test_the_915_is_simons_de_weger_lemma_12_not_rhin() -> None:
    """The attribution correction in `J-rhin-eight-has-no-computed-threshold`.

    Rhin's (7) is `H^(-13.3)` outright for `H >= 2` and carries no constant at
    all. The chain is unaffected; the table's attribution was loose.
    """
    printed = next(r for r in TRANSCENDENCE_CHAIN if r["mu"] == 14.3)
    assert "915" in printed["constant"]
    assert "Simons-de Weger" in printed["constant"]
    assert "Rhin prints no constant" in printed["constant"]


def test_the_two_readings_of_equation_eight_are_recorded_as_one_theorem() -> None:
    """`J-rhin-eight-readings-are-one-theorem`: the dichotomy was false.

    Spiegelhofer's ratio bound and Zudilin's `Q log2 + Q log3` bound are two
    corollaries of one linear independence measure -- Rhin approximates
    `log(2/3)` and `log(4/3)`, an integral basis change from `log2, log3`, so
    the same lattice and the same exponent. p. 160 confirms it at source: both
    (7) and (8) are the three-term form. The chain must not still carry the
    dispute.
    """
    eight = next(r for r in TRANSCENDENCE_CHAIN if r["mu"] == 8.616)
    assert "disputed_by" not in eight, "the dispute was resolved on 16 September 2026"
    assert eight["reading_resolved_by"] == "J-rhin-eight-readings-are-one-theorem"
    assert eight["reported_by"].startswith("spiegelhofer")
    for row in (eight, next(r for r in TRANSCENDENCE_CHAIN if r["mu"] == 14.3)):
        assert "three-term" in row["route"], row["route"]


def test_effective_and_computed_are_kept_apart() -> None:
    """The distinction the 16 September readings forced into the data.

    Wu-Wang Theorem 1 and Rhin eq.(8) both assert an effectively computable
    threshold and neither computes it, so a bare `effective: True` would read
    as a printed constant. Those two rows and no others are effective but
    uncomputed, each says what is missing, and neither is the deposited
    effective statement.
    """
    for row in TRANSCENDENCE_CHAIN:
        assert row["verified_against_primary"] is True, row["source"]
        if row["effective"] and not row["constant_computed"]:
            assert row.get("uncomputed_threshold"), row["source"]
            assert not row["used_by"].startswith("Paper A"), (
                f"{row['source']}: an uncomputed threshold cannot be the "
                "deposited effective statement"
            )
    assert {
        r["source"] for r in TRANSCENDENCE_CHAIN if r["effective"] and not r["constant_computed"]
    } == {"rhin-1987-pade-irrationality", "wu-wang-2014-irrationality-measure-log3"}


def test_the_effective_statement_and_the_asymptotic_one_are_different_rows() -> None:
    """`J-wuwang-effectivity-is-a-saddle-point-cost`, as a property of the chain.

    `H_0 = exp(Theta(n_0))` -- about `1e3500` at `eps = 0.05` -- so Wu-Wang
    supplies nothing at any `L` a cycle search reaches, and Rhin eq.(7) with
    the Simons-de Weger constant is what actually applies. `L^14.3` is the
    effective statement and `L^5.1163051` the asymptotic one; the audit must
    not let the sharper number pass for the usable one.
    """
    data = report()
    assert data["sharpest_computed_mu"] == 14.3
    assert data["asymptotic_mu_in_use"] == 5.1163051
    assert data["sharpest_computed_mu"] > data["asymptotic_mu_in_use"]
    assert data["sharpest_computed_mu"] > data["sharpest_verified_mu"]


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
    assert data["chain_is_read_at_source"] is True
    assert data["is_halt_theorem"] is False
    assert data["new_mathematics"] is False
    assert math.isclose(data["alpha"], ALPHA)
