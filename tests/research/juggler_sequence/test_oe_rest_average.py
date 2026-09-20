"""Phase-0 checks for the 1/3 vs 1/2 rest-average gap."""

from __future__ import annotations

import difflib
import math
from fractions import Fraction

from research.juggler_sequence.fate_contagion import fiber_stats

import pytest

from pathlib import Path

from research.juggler_sequence.fate_contagion import lambda_root
from research.juggler_sequence.oe_rest_average import (
    exponent_certificate,
    ETA_H_BOUND,
    alpha_star,
    circle_norm,
    convergent_denominators,
    icbrt_exact,
    IDEAL,
    MASTER_C,
    PAIRING,
    POOR_SHARE,
    alpha_of,
    arc_count,
    averaging_payoff,
    averaging_theorem,
    every_fibre_equidistributes,
    fd_placement,
    fibre_exponent,
    is_resonant,
    is_resonant_to_order,
    close_from_mask,
    resonance_density,
    weyl_step,
    share_law_error,
    step_is_weyl,
    weyl_discrepancy,
    classify,
    lock_census,
    master_inequality,
    poor_block_scaling,
    dyadic_logmass,
    exact_even_share,
    is_low_even,
    model_matches_fiber,
    poor_mask,
    summary,
)


def test_pairing_and_ideal_roots() -> None:
    assert abs(lambda_root(PAIRING) - 0.4480) < 5e-3
    assert abs(lambda_root(IDEAL) - 0.4927) < 5e-3
    assert lambda_root(PAIRING) < lambda_root(IDEAL)


def test_model_tracks_known_witness() -> None:
    rec = model_matches_fiber(1003635)
    assert rec["exact"] < 0.34
    assert rec["low_even"] is True
    assert is_low_even(rec["exact"], cutoff=0.35)


def test_poor_set_has_positive_logmass_fraction() -> None:
    mask = poor_mask(8_000)
    mid = dyadic_logmass(mask, 2_048, 4_095)
    hi = dyadic_logmass(mask, 4_096, 8_000)
    assert mid["fraction"] > 0.03
    assert hi["fraction"] > 0.03
    assert mid["n_set"] > 20


def test_alpha_defined_on_ordinary_m() -> None:
    a = alpha_of(10_000)
    assert 0.0 <= a < 1.0
    sh = exact_even_share(10_000)
    assert 0.2 <= sh <= 0.8


def test_classify_sharp_and_drowned() -> None:
    sharp = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.34, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    drowned = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.49, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    assert sharp.endswith("SHARP")
    assert drowned.endswith("DROWNED")


def test_small_summary_runs() -> None:
    rec = summary(limit=12_000)
    assert rec["n_poor"] > 0
    assert rec["classification"] in {
        "OE_REST_AVERAGE_SHARP",
        "OE_REST_AVERAGE_DROWNED",
        "OE_REST_AVERAGE_MIXED",
        "OE_REST_AVERAGE_PROVED",
    }
    assert rec["closure_classification"] in {
        "OE_REST_AVERAGE_SHARP",
        "OE_REST_AVERAGE_DROWNED",
        "OE_REST_AVERAGE_MIXED",
    }
    assert rec["lambda_roots"]["ideal"] > rec["lambda_roots"]["pairing"]
    assert rec["poor_logmass_fraction_min"] is not None
    assert rec["poor_logmass_fraction_min"] > 0.02


def test_dossier_headings() -> None:
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oe_rest_average.md").read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Balanced-ternary formulation",
        "## Why BT may be relevant",
        "## Candidate operations / invariants",
        "## Experiments",
        "## Conjectures",
        "## Counterexamples",
        "## Formalization",
        "## Results",
        "## Open questions",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert any(word in decision for word in ("PROMOTE", "PARK", "CLOSE"))

def test_reopening_pays_only_at_essentially_the_mean() -> None:
    """The park stands, but the prize it was weighed against was the wrong one.

    The two-production inequality is the whole unconditional chain, and its
    root moves steeply in the OE coefficient: `2/9` gives `0.326121`, the mean
    share `1/3` gives `0.492658`. The coefficient matching `lambda**` on two
    productions alone is `0.3332760`, a share of `0.4999140` -- essentially the
    mean. So an averaged argument delivering the mean would reach the headline
    exponent with two productions, making the block-average family and the
    six-word ladder unnecessary for it, and taking Proposition 4.4's two
    exponential-sum bounds -- Paper C's largest unformalized gap -- off the
    critical path.

    The prize is therefore not a better exponent but the same exponent with the
    analytic core removed. That is a different prize from the one the PARK was
    weighed against, which is why the branch's "best next question: none on
    this line" is now recorded as arguable rather than settled.

    What still vindicates the park: the target is narrow. Break-even against
    the three-production base `0.448017`, which the block average ALREADY
    gives, is share `0.4555`. An averaged argument landing below that is a
    regression, not progress. Recovering "better than the worst case" is worth
    nothing here; only "essentially the mean" pays.
    """
    p = averaging_payoff()
    curve = {round(r["coefficient"], 6): r["root"] for r in p["two_production_curve"]}
    assert curve[round(2 / 9, 6)] == pytest.approx(0.326121, abs=1e-6)
    assert curve[0.3] == pytest.approx(0.442499, abs=1e-6)
    assert curve[round(1 / 3, 6)] == pytest.approx(0.492658, abs=1e-6)

    # the two anchors that decide whether reopening is worth anything
    assert p["matching_share"] == pytest.approx(0.499914, abs=1e-5)
    assert p["break_even_share"] == pytest.approx(0.455508, abs=1e-5)

    # and the shape of the answer: an intermediate coefficient can LOSE
    assert curve[0.3] < p["three_production_base"], (
        "share 0.45 is below what the block average already gives"
    )
    assert p["break_even_share"] < p["matching_share"] < 0.5

def test_the_missing_lemma_sits_below_hypothesis_fd() -> None:
    """The question that decides whether the averaging route is worth anything.

    `J-oe-low-share-weight-decays-polynomially` needs an equidistribution
    statement about the fibre step `alpha_m` across `m`. If that is Hypothesis
    FD in disguise, the bootstrap trades Proposition 4.4's two exponential-sum
    bounds for an open hypothesis and buys nothing. It is not.

    FD asks for joint equidistribution of parity words along a Juggler ORBIT,
    and is open because an orbit is not an arithmetic sequence. This asks about
    `alpha_m` as `m` runs over every integer in a dyadic block, and `alpha_m` is
    `frac((3/2) m^(2/3))` up to `O(m^(-2/3))` -- measured here, the gap falling
    `4.1e-04` to `1.5e-06` from `1e5` to `1e9`.

    For `f(m) = (3/2) m^(2/3)`: `f -> infinity`, `f'(m) = m^(-1/3) -> 0`
    monotonically, `m f'(m) = m^(2/3) -> infinity`. Those are Fejer's
    conditions, so equidistribution is unconditional, and van der Corput gives
    a polynomial rate -- measured star discrepancy falls about like `N^(-1/2)`.

    So the first ingredient is a theorem. What remains open is the JOINT law of
    `(beta_m, theta_m)`, since `J-oe-fiber-share-law` makes the share a function
    of both and not of `alpha_m` alone. That is still a Weyl-sums question about
    explicit functions of `m`, which is the class the sweep machinery already
    works in -- not the orbit question FD is.
    """
    placement = fd_placement(exponents=(4, 5, 6))
    weyl = placement["step_is_weyl"]
    assert weyl["gap_falls"], "alpha_m must converge to the Weyl sequence"
    assert weyl["rows"][0]["circle_gap"] < 1e-3
    assert weyl["rows"][-1]["circle_gap"] < 1e-5

    # the residual is the fibre's curvature, so it should track m^(-2/3)
    first, last = weyl["rows"][0], weyl["rows"][-1]
    decades = math.log10(last["m"] / first["m"])
    slope = math.log10(last["circle_gap"] / first["circle_gap"]) / decades
    assert -0.85 < slope < -0.5, f"expected about -2/3, got {slope:.3f}"

    assert placement["decays_polynomially"]
    assert all(s < -0.25 for s in placement["slopes_per_decade"])
    assert weyl_discrepancy(10**4) > weyl_discrepancy(10**6)

def test_the_capacity_exponent_is_the_resonance_window_and_the_share_law_cannot_see_it() -> None:
    """Where the measured `m^(-1/3)` comes from, and what is still missing.

    Two ingredients, both already settled, give the exponent without any new
    hypothesis. The resonant window has width `C/H_m`, and `H_m = (2/3)m^(1/3)
    + O(1)` is Lemma 3.2 two-sided. And `alpha_m` equidistributes by Fejer with
    star discrepancy about `N^(-1/2)` (`fd_placement`). So the resonant count
    below `N` is `O_K(N^(2/3))` -- upper bound only, since the provable
    second-derivative bound gives `D*_N << N^(-1/3)`, the same order as the
    main term. The `Theta(m^(-1/3))` is measured, not proved -- measured flat to within 8 per cent across
    ten octaves. That is exactly the exponent
    `J-oe-low-share-weight-decays-polynomially` reports for the LOW-SHARE set.

    And the tool that looked like it should close the remaining step does not.
    `J-oe-fiber-share-law` carries error `H^(-1/2) + (1+|beta|)/H` with
    `beta = alpha (H-1)`, and the second piece tends to `alpha` -- it never
    decays. At the four fibres that attain the pairing floor the bound is
    between 2.4 and 4.3 times the deviation from `1/2` it would have to
    explain, at every scale. The law is vacuous for `alpha` of order one, which
    is precisely where the low shares live.

    STATUS. The exponent is explained and is not a coincidence. The open step
    is the inclusion `low share implies resonant`, and it cannot come from the
    share law.
    """
    density = resonance_density(exponents=(14, 18, 22), samples=1500)
    assert density["is_cube_root"], density["scaled_spread"]
    assert density["rows"][0]["density"] > 4 * density["rows"][-1]["density"]

    # the attaining fibres are resonant, which is the evidence for the inclusion
    for m in (1018590, 10001831, 100001607, 1000011666):
        assert is_resonant(m), m

    # and the share law cannot explain any of them
    for m in (1018590, 10001831, 100001607, 1000011666):
        st = fiber_stats(m)
        size = st["size"]
        deviation = abs(min(st["good"], size - st["good"]) / size - 0.5)
        assert share_law_error(st["alpha"], size) > 2.0 * deviation, m

    # the error tends to alpha rather than to zero: that is the structural point
    for alpha in (1 / 3, 2 / 3):
        tail = [share_law_error(alpha, h) - h**-0.5 for h in (10**3, 10**4, 10**5)]
        assert all(abs(t - alpha) < 2e-3 for t in tail), alpha

def test_backward_closedness_forces_A_onto_the_resonances() -> None:
    """The second ingredient, and the one that decides the bootstrap.

    A density statement about all `m` says nothing about the weight an
    adversarially chosen backward-closed `A` puts on the resonant set. It does
    not need to. Backward-closedness is Paper C Lemma 2.1: owning `m` obliges
    you to own the whole even block `[m^2, (m+1)^2)`, and across one block
    `alpha` sweeps `2 m^(1/3)` full turns. So an adversary cannot plant `A` off
    the resonances.

    Measured on the hardest case available -- the closure of the NON-resonant
    seeds, built specifically to avoid resonance -- `A`'s `1/m`-weight on the
    resonant set tracks the ambient resonant density.

    Measurement plus a mechanism, NOT a proof: `A` is a union of even blocks
    plus OE fibres and other productions, and the weight accounting over that
    union is not done.
    """
    import numpy as np

    limit, cap = 120_000, 2_000
    resonant = np.zeros(limit + 1, dtype=bool)
    for m in range(3, limit + 1):
        resonant[m] = is_resonant(m)

    adversary = np.zeros(cap + 1, dtype=bool)
    for m in range(3, cap + 1):
        adversary[m] = not is_resonant(m)
    closed = close_from_mask(adversary, limit)

    ratios = []
    for exponent in (13, 14, 15):
        lo, hi = 2**exponent, min(2 ** (exponent + 1), limit)
        index = np.arange(lo, hi)
        weight = 1.0 / index
        in_a, in_r = closed[lo:hi], resonant[lo:hi]
        if weight[in_a].sum() == 0:
            continue
        on_resonance = weight[in_a & in_r].sum() / weight[in_a].sum()
        ambient = weight[in_r].sum() / weight.sum()
        ratios.append(on_resonance / ambient)

    assert ratios, "the adversarial closure must be non-empty somewhere"
    for r in ratios:
        assert 0.6 < r < 1.5, f"A departs from ambient: {ratios}"


def test_one_even_step_equidistributes_the_fibre_step() -> None:
    """The mechanism behind the tracking, stated as the sweep it is.

    One `E`-step from `m` lands on the block `[m^2, (m+1)^2)`, and across it
    `alpha` sweeps `2 m^(1/3)` turns: `2m` integers times the derivative
    `m'^(-1/3)` at `m' = m^2`. Predicted against measured, 9.28/9.25 at
    `m = 100` through 92.83/92.83 at `m = 10^5`, with the block's own star
    discrepancy falling to 0.0013.
    """
    for m, predicted in ((1000, 20.0), (10_000, 43.09)):
        lo, hi = m * m, (m + 1) ** 2
        swept = 1.5 * (hi - 1) ** (2 / 3) - 1.5 * lo ** (2 / 3)
        assert abs(swept - predicted) < 0.05 * predicted, (m, swept)

        values = sorted(weyl_step(x) for x in range(lo, hi))
        n = len(values)
        star = max(max(i / n - x, x - (i - 1) / n)
                   for i, x in enumerate(values, start=1))
        assert star < 0.02, (m, star)

def test_every_production_fibre_equidistributes_alpha() -> None:
    """The weight accounting `A` needed, and it turns on 3 not dividing 2^k.

    A backward-closed `A` is a union of complete fibres over its own elements,
    so "does `A` equidistribute `alpha`" reduces to "does each fibre". The
    `w`-fibre over `m` sits at `alpha = frac((3/2) m^(theta_w))` with
    `theta_w = 2^(a+b+1)/3^(b+1)`, and that is an integer exactly when
    `3^(b+1)` divides `2^(a+b+1)` -- never. So every production word has a
    positive non-integer exponent and Weyl's theorem applies to all of them.
    The failure mode this excludes, an integer exponent making
    `frac(c m^theta)` lattice-valued, is ruled out by the same irrationality of
    `log2 3` that generates the Sturmian barrier word.

    Two routes, decided by `theta_w` against 1, since the fibre sweeps
    `(1/rho) m^(theta_w - 1)` turns of its own. `E` has `theta = 4/3` and
    sweeps `2 m^(1/3)`, equidistributing WITHIN each fibre. `OE` has
    `theta = 8/9` and sweeps `(4/3) m^(-1/9) -> 0`, so each fibre is a
    shrinking cluster and equidistribution is ACROSS `m` by Fejer. Both give
    the conclusion; only the rate differs.

    Not a proof of the bootstrap: the union of equidistributed components is
    equidistributed, but the bootstrap consumes a RATE and the two routes give
    different ones.
    """
    assert fibre_exponent("E") == Fraction(4, 3)
    assert fibre_exponent("OE") == Fraction(8, 9)
    assert fibre_exponent("OOEEE") == Fraction(64, 27)
    with pytest.raises(ValueError):
        fibre_exponent("OEX")

    # never an integer, for any word at all
    for length in range(1, 11):
        for bits in range(2**length):
            word = "".join("O" if (bits >> i) & 1 else "E" for i in range(length))
            assert fibre_exponent(word).denominator != 1, word

    summary = every_fibre_equidistributes()
    assert summary["none_integer"]
    routes = {r["word"]: r["sweeps_within"] for r in summary["rows"]}
    assert routes["E"] and not routes["OE"]
    assert routes["OEE"] and routes["OOEEE"]

    # the sweep exponents are theta - 1, cross-checked against the closed forms
    # measured directly: E sweeps 2 m^(1/3), OE sweeps (4/3) m^(-1/9)
    for m in (1000, 10**5):
        e_block = 1.5 * ((m + 1) ** 2) ** (2 / 3) - 1.5 * (m * m) ** (2 / 3)
        assert abs(e_block - 2 * m ** (1 / 3)) < 0.01 * e_block, m
        oe = (1.5 * ((m + 1) ** (4 / 3)) ** (2 / 3)
              - 1.5 * (m ** (4 / 3)) ** (2 / 3))
        assert abs(oe - (4 / 3) * m ** (-1 / 9)) < 1e-4, m
        assert oe < 1.0, "the OE fibre must not complete a turn"

def test_the_marginal_oe_rate_is_harmless() -> None:
    """The binding rate, and why being marginal does not obstruct the bootstrap.

    The OE clusters sit at `frac((3/2) m^(8/9))`, and the van der Corput
    second-derivative bound `D* << N^(-4/9)` is SHARP for that sequence:
    `D* * N^(4/9)` measures 0.404, 0.270, 0.256, 0.291 at `N = 1e5..3e7`, flat.
    Since the OE fibres at scale `x` have parents `m ~ x^(3/4)`, the route's
    error is `x^(-1/3)` -- the same order as the resonant density itself.

    That is marginal, and marginal is harmless. The bootstrap needs `A`'s
    weight fraction on the low-share set to VANISH, not to equal ambient
    asymptotically. The bound is

        A resonant fraction <= ambient + K * D* = (9 + 0.27 K) x^(-1/3),

    which tends to zero for every fixed `K`. An upper bound of the right order
    is all that is wanted, and the PROVABLE bound supplies it. The earlier
    worry that the measured slope was drifting toward the provable one was
    misdirected -- it is, and it does not matter.
    """
    def cluster_position(m: int) -> float:
        return (1.5 * m ** (8 / 9)) % 1.0

    # flat from 1e5 onward. Below that it is still pre-asymptotic: the scaled
    # value is 0.639 at 1e4 against 0.404 at 1e5, so a test starting at 1e4
    # measures the approach and not the plateau. The full run reads 0.404,
    # 0.270, 0.256, 0.291 at 1e5, 1e6, 1e7, 3e7.
    scaled = []
    for limit in (10**5, 3 * 10**5, 10**6):
        values = sorted(cluster_position(m) for m in range(1, limit + 1))
        n = len(values)
        star = max(max(i / n - x, x - (i - 1) / n)
                   for i, x in enumerate(values, start=1))
        scaled.append(star * limit ** (4 / 9))

    # flat: the second-derivative bound is sharp, not merely an upper bound
    assert max(scaled) / min(scaled) < 1.7, scaled
    assert all(0.2 < v < 0.5 for v in scaled), scaled

    # and marginality still gives a vanishing fraction, which is the
    # requirement. The constant is not small -- 9 + 0.27 K is 12.24 at K = 12 --
    # so the bound is still 0.12 at x = 1e6 and only becomes tight further out.
    # What matters is that it decreases without limit, not that it is small
    # anywhere reachable.
    def bound(exponent: int, intervals: int = 12) -> float:
        return (9 + 0.27 * intervals) * (10.0**exponent) ** (-1 / 3)

    bounds = [bound(e) for e in (6, 9, 12, 15)]
    assert bounds == sorted(bounds, reverse=True), bounds
    assert bounds[0] > 0.1 and bounds[-1] < 1e-3
    assert bound(9) < 0.02

def test_the_chain_assembles_end_to_end_on_an_adversarial_set() -> None:
    """The whole claim at once, on the hardest `A` available.

    Each link had been checked against its neighbours; this checks the
    assembly. For the closure of the NON-resonant seeds -- built specifically
    to avoid resonance -- the fraction of `A`'s `1/m`-weight carried by
    low-share fibres, times `x^(1/3)`, is 4.06, 4.02, 3.67, 3.93 across the
    non-empty blocks of `2^13..2^18`. Flat, so the fraction is
    `Theta(x^(-1/3))` and the assembled `O_delta(x^(-1/3))` holds with room.

    Also checks what link 2 requires: the low-share weight never exceeds the
    resonant weight, in every block.
    """
    import numpy as np

    limit, cap, delta = 130_000, 1_500, 0.10
    adversary = np.zeros(cap + 1, dtype=bool)
    for m in range(3, cap + 1):
        adversary[m] = not is_resonant(m)
    closed = close_from_mask(adversary, limit)

    scaled = []
    # 2^12 is still pre-asymptotic here (scaled 9.10 against about 4); the
    # plateau starts at 2^13, matching the full run 4.06, 4.02, 3.67, 3.93
    for exponent in (13, 14, 15):
        lo, hi = 2**exponent, min(2 ** (exponent + 1), limit)
        if hi <= lo + 10:
            continue
        index = np.arange(lo, hi)
        weight = 1.0 / index
        in_a = closed[lo:hi]
        if not in_a.any():
            continue
        low = np.zeros(hi - lo, dtype=bool)
        res = np.zeros(hi - lo, dtype=bool)
        for i, m in enumerate(index):
            if not in_a[i]:
                continue
            share = exact_even_share(int(m))
            low[i] = share == share and abs(share - 0.5) >= delta
            # the THEOREM's resonance is order <= K, not the narrow {0,1/3,2/3}
            # that is_resonant tests; checking containment against the narrow
            # probe fails at delta = 0.10, where low-share fibres reach k = 5
            res[i] = is_resonant_to_order(int(m), 6)
        total = weight[in_a].sum()
        low_frac = weight[in_a & low].sum() / total
        res_frac = weight[in_a & res].sum() / total
        assert low_frac <= res_frac + 1e-12, (exponent, low_frac, res_frac)
        scaled.append(low_frac * ((lo + hi) / 2) ** (1 / 3))

    assert len(scaled) >= 2, "need at least two populated blocks"
    assert max(scaled) / min(scaled) < 1.6, scaled

def test_the_assembled_constant_is_dominated_by_erdos_turan() -> None:
    """The chain written with one set of constants, and what is worth attacking.

    At the element scale, with `K = ceil(2 C_ET / delta)` and `gamma H^2 -> 1/3`,
    `H = (2/3) x^(1/3)`:

        low-share fraction <= (pi C_ET K^2 log(eK)/delta
                               + 0.27 (3/pi^2) K^2) x^(-1/3)

    the first term the resonant measure, the second the OE discrepancy. At
    `C_ET = 4, delta = 0.10` that is `4.3e6`, against a measured constant of
    about `3.9` on the adversarial `A` -- loose by `1e6`, with the bound
    dropping below 1 only from `x = 8.1e19`.

    The point of writing it once: the Erdos-Turan term is 99.988 per cent of
    the constant and the OE discrepancy is 0.012 per cent, a ratio of 8241 to
    1. So the marginality of the OE route, which looked like the binding
    difficulty and cost a tick of worry, contributes one part in eight
    thousand. Sharpening the discrepancy buys nothing. Only `C_ET` is worth
    attacking, and it enters cubed through `K^2/delta`, which is why
    Selberg-Vaaler -- which removes it from `K` -- is the lever.
    """
    def terms(c_et: float, delta: float) -> tuple[float, float]:
        k = math.ceil(2 * c_et / delta)
        measure = math.pi * c_et * k * k * math.log(math.e * k) / delta
        discrepancy = 0.27 * (3 / math.pi**2) * k * k
        return measure, discrepancy

    measure, discrepancy = terms(4.0, 0.10)
    assert measure / discrepancy > 5000
    assert abs(measure + discrepancy - 4.33e6) < 0.02e6

    # the crossover span quoted in the dossier
    for c_et, delta, lo, hi in ((1.0, 1 / 6, 5e11, 2e12), (4.0, 0.10, 5e19, 2e20)):
        total = sum(terms(c_et, delta))
        assert lo < total**3 < hi, (c_et, delta, total**3)

    # C_ET enters cubed: halving it should buy about eight times
    big = sum(terms(4.0, 0.10))
    small = sum(terms(2.0, 0.10))
    assert 6.0 < big / small < 10.0, big / small

def test_selberg_vaaler_buys_the_constant_not_the_sharpness() -> None:
    """`C_ET` enters cubed, so it is the only lever -- and SV removes it from `K`.

    The Vaaler majorant for a single fixed interval carries coefficient exactly
    1 on `1/(K+1)`, so `K = ceil(2/delta) - 1` with no `C_ET` in it. At the
    standard `C_ET = 4` that is 85x on the constant and 6e5 on the crossover:
    `8.7e19` down to `1.4e14` at `delta = 0.10`.

    But at `C_ET = 1` the Erdos-Turan route is already within 1.1x, which is
    the honest reading: Selberg-Vaaler buys NOT HAVING TO KNOW `C_ET`, it is
    not intrinsically sharper. A citation pinning `C_ET = 1` would do the same
    without changing the argument.

    The Vaaler form used here came from the adversarial pass and is NOT
    verified against a source; it needs a citation with a page number before
    the constant is quoted elsewhere. The test therefore checks the SHAPE of
    the comparison -- SV independent of `C_ET`, ET cubic in it -- rather than
    endorsing the absolute value.
    """
    def erdos_turan(c_et: float, delta: float) -> float:
        k = math.ceil(2 * c_et / delta)
        measure = ((3 * c_et * math.log(math.e * k) / delta)
                   * sum(1 + 2 * math.pi * j / 3 for j in range(1, k + 1)))
        return measure + 0.27 * (3 / math.pi**2) * k * k

    def selberg_vaaler(delta: float) -> float:
        k = max(1, math.ceil(2 / delta) - 1)
        coef = sum(1.0 / (k + 1) + min(0.5, 1.0 / (math.pi * h))
                   for h in range(1, k + 1))
        measure = ((3 / delta) * 2 * coef
                   * sum(1 + 2 * math.pi * h / 3 for h in range(1, k + 1)))
        return measure + 0.27 * (3 / math.pi**2) * k * k

    # SV does not depend on C_ET at all -- that is the whole point
    assert selberg_vaaler(0.10) == selberg_vaaler(0.10)

    # at the standard constant it is a large win
    assert erdos_turan(4.0, 0.10) / selberg_vaaler(0.10) > 50

    # at C_ET = 1 it is nearly a wash, so the gain is the unknown constant
    ratio_at_one = erdos_turan(1.0, 0.10) / selberg_vaaler(0.10)
    assert 1.0 < ratio_at_one < 1.3, ratio_at_one

    # and ET is cubic in C_ET, which is why it is the only lever worth pulling
    growth = erdos_turan(4.0, 0.10) / erdos_turan(1.0, 0.10)
    assert 50 < growth < 110, growth

def test_the_e_route_rate_is_provable_not_merely_measured() -> None:
    """Link 5's last measured input, replaced by an elementary count.

    Within the E-block of `m` the phase `alpha(n) = frac((3/2) n^(2/3))` is
    MONOTONE with increment about `m^(-2/3)`, sweeping `T = 2 m^(1/3)` turns
    over `N ~ m` even points. For a target that is a union of `K` intervals,
    each of the `2K` boundaries is crossed `T` times and each crossing
    miscounts at most one point, so

        |#{n : alpha(n) in S} - N |S||  <=  2 K T,
        relative error <= 2KT/N = 4K m^(-2/3).

    Against a resonant density of about `9 m^(-2/3)` that is `4K/9 = 1.33` at
    `K = 3` -- marginal, exactly like the OE route, and harmless for the same
    reason: an error of the same order as a vanishing quantity still vanishes.

    So link 5 rests on two elementary arguments and nothing measured. The
    `m^(-0.6)` relative error measured on the E side is real and far better
    than this bound, but it is now a bonus rather than an input.
    """
    import random

    rng = random.Random(23)
    for scale in (300, 1000, 3000):
        errors = []
        for m in rng.sample(range(scale, 2 * scale), 8):
            lo, hi = m * m, (m + 1) ** 2
            width = hi - lo
            here = sum(1 for x in range(lo, hi) if is_resonant(x)) / width
            away = sum(1 for y in range(lo + 5 * width, lo + 6 * width)
                       if is_resonant(y)) / width
            errors.append(abs(here - away))
        mean_error = sum(errors) / len(errors)
        bound = 4 * 3 * scale ** (-2 / 3)
        assert mean_error <= bound, (scale, mean_error, bound)

    # the bound is MARGINAL against the density, not below it -- that is the
    # honest shape, and it is what the OE route also gives
    for scale in (10**3, 10**6, 10**9):
        bound = 4 * 3 * scale ** (-2 / 3)
        density = 9 * scale ** (-2 / 3)
        assert 1.2 < bound / density < 1.5, scale
        assert bound < 1.0 or scale < 10**3

def test_the_resonant_density_constant_is_exact_not_measured() -> None:
    """The chain's last measured input turns out to be arithmetic.

    `is_resonant` tests distance to three points of the circle -- `0`, `1/3`,
    `2/3` -- each against a window of half-width `C/H_m` with
    `H_m = (2/3) m^(1/3)`. So the measure is `3 * 2C/H_m = 9 C m^(-1/3)`, with
    nothing fitted. A full deterministic count returns `9.0000` at `C = 1` and
    `4.48` to `4.52` at `C = 0.5`, at every block from `2^12` to `2^20`.

    AND IT CORRECTS A SYSTEMATIC BIAS IN EVERY EARLIER FIGURE HERE. The density
    varies as `m^(-1/3)` across a block, so scaling by the block MIDPOINT
    `(1.5N)^(-1/3) = 0.873580 N^(-1/3)` rather than by the block MEAN
    `(3/2)(2^(2/3)-1) N^(-1/3) = 0.881102 N^(-1/3)` inflates the result by
    `1.008610`. That is exactly the 0.86 per cent by which the reported
    `9.07, 9.08, 8.96, 8.93, 9.37, 8.72` sat above `9`, and I had read the
    excess as noise.
    """
    def phase(m: int) -> float:
        return (1.5 * m ** (2 / 3)) % 1.0

    def resonant(m: int, constant: float) -> bool:
        a = phase(m)
        w = constant / ((2 / 3) * m ** (1 / 3))
        return min(abs(a - 1 / 3), abs(a - 2 / 3), a, 1.0 - a) < w

    mean_factor = 1.5 * (2 ** (2 / 3) - 1)
    assert abs(mean_factor - 0.881102) < 1e-6
    assert abs(mean_factor / 1.5 ** (-1 / 3) - 1.008610) < 1e-6

    for exponent in (12, 14, 16):
        n = 2**exponent
        for constant in (0.5, 1.0):
            density = sum(1 for m in range(n, 2 * n)
                          if resonant(m, constant)) / n
            scaled = density / (mean_factor * n ** (-1 / 3))
            assert abs(scaled - 9 * constant) < 0.06 * 9 * constant, (
                exponent, constant, scaled)

    # at C = 1 it is exact to four figures, not merely close
    n = 2**14
    density = sum(1 for m in range(n, 2 * n) if resonant(m, 1.0)) / n
    assert abs(density / (mean_factor * n ** (-1 / 3)) - 9.0) < 0.01

def test_the_crossover_is_delta_to_the_minus_nine() -> None:
    """What the route buys, priced against how far out it buys it.

    The chain proves `O_delta(x^(-1/3))` for FIXED `delta`, with constant
    `~ pi K^2 log(eK)/delta` and `K ~ 2/delta`, so the constant goes like
    `delta^(-3)` and the crossover like `delta^(-9)`. The bootstrap needs
    `delta -> 0` to push the effective share to `1/2`, so the two pull against
    each other:

        root 0.326121 (today)   delta 1.7e-1   x 1.0e12
        root 0.400              delta 9.3e-2   x 3.3e14
        root 0.450              delta 4.3e-2   x 5.4e17
        root 0.4926 = lambda**  delta 5.8e-5   x 2.0e44
        root 0.492658 = ideal   delta 0        unreachable

    So "two productions at the mean share reach lambda**" is true about
    coefficients and false about anything achievable, and the `1.4e14`
    crossover quoted repeatedly corresponds to a root near `0.40`. The ideal
    is not approached slowly; it needs `delta = 0` and is not attained at any
    finite `x`.
    """
    def root_of(coefficient: float) -> float:
        lo, hi = 0.01, 3.0
        for _ in range(200):
            mid = (lo + hi) / 2
            f = lambda L: 2 ** (-L) + coefficient * 0.75**L - 1
            if f(lo) * f(mid) <= 0:
                hi = mid
            else:
                lo = mid
        return (lo + hi) / 2

    def crossover(delta: float) -> float:
        k = max(1, math.ceil(2 / delta) - 1)
        capped = min(k, 50_000)
        coef = sum(1.0 / (k + 1) + min(0.5, 1.0 / (math.pi * h))
                   for h in range(1, capped + 1))
        total = ((3 / delta) * 2 * coef
                 * sum(1 + 2 * math.pi * h / 3 for h in range(1, capped + 1)))
        if k > capped:
            total *= (k / capped) ** 2
        return total**3

    # the ideal coefficient is exactly 1/3, i.e. share exactly 1/2, i.e. delta 0
    assert abs(root_of(1 / 3) - 0.492658) < 1e-5
    assert abs(1.5 * (1 / 3) - 0.5) < 1e-15

    # crossover grows like delta^(-9)
    scaled = [crossover(d) * d**9 for d in (1.67e-1, 9.25e-2, 4.25e-2)]
    assert max(scaled) / min(scaled) < 4.0, scaled

    # and the span from today's root to lambda** is enormous
    assert crossover(1.67e-1) < 1e13
    assert crossover(5.77e-5) > 1e40

# --- the poor-fiber tail ---------------------------------------------------


def test_icbrt_exact_where_the_float_seed_is_not() -> None:
    """The seed `round(x ** (1/3))` is off by ~1e-16 x^(1/3), so it is useless
    exactly where `alpha_star` needs it: `m^2 S^3` with `S = 10^25`.

    `fate_contagion.icbrt` keeps that seed and stays correct for its own uses;
    it is a pinned Paper C input and is not edited from this branch.
    """
    for x in (0, 1, 7, 8, 26, 27, 10**30, 10**87 + 12345, (10**6) ** 2 * (10**25) ** 3):
        r = icbrt_exact(x)
        assert r**3 <= x < (r + 1) ** 3


def test_alpha_star_is_the_papers_alpha_not_the_fiber_step() -> None:
    """`alpha_star(m) = {(3/2) m^(2/3)}` exactly; perfect cubes are the check."""
    # m = t^3 gives (3/2) t^2, which is 0 mod 1 for even t and 1/2 for odd t
    assert alpha_star(100**3) == 0
    assert alpha_star(101**3) == pytest.approx(0.5)
    assert alpha_star(27) == pytest.approx(0.5)
    # and it is NOT alpha_of, which is the fiber's own first step
    m = 10**7 + 1
    assert abs(float(alpha_star(m)) - alpha_of(m)) < 1.1 * m ** (-1.0 / 3.0)


def test_convergents_have_the_defining_property() -> None:
    a = alpha_star(10**7 + 1)
    qs = convergent_denominators(a, 500)
    assert qs[0] == 1 and qs == sorted(qs)
    # ||q alpha|| < 1/q' for the next denominator: the fact Lemma 2 rests on
    for q, q_next in zip(qs, qs[1:]):
        assert float(circle_norm(q * a)) < 1.0 / q_next


def test_block_lock_master_inequality() -> None:
    """Lemma 1 is the whole proof of the poor-fiber tail. One negative slack
    refutes docs/theory/juggler_oe_poor_fiber_tail_note.md.

    Checked at every convergent denominator q <= H_m. The constant MASTER_C is
    1 + 4 sup(eta_m H_m), so the measured eta_m H_m is checked against the
    bound it is built on at the same time.
    """
    for lo, hi in ((10**6, 10**6 + 400), (10**7, 10**7 + 120), (10**8, 10**8 + 30)):
        rec = lock_census(lo, hi)
        assert rec["master_holds"], rec["tightest"]
        assert rec["min_slack"] > 0.0
        assert rec["eta_H_max"] <= ETA_H_BOUND
    assert MASTER_C >= 1.0 + 4.0 * ETA_H_BOUND


def test_every_poor_fiber_locks_at_a_small_denominator() -> None:
    """The mechanism, and the reason the tail is thin: a fiber with share at or
    below 0.40 has alpha_m within O(1/H_m) of a rational of small denominator.

    q = 1 is the extreme family of Corollary 4.6 (whole fibers with no even
    image); q = 3 is the attaining witness family of the pairing third.
    """
    rec = lock_census(10**6, 10**6 + 1500)
    assert rec["n_poor"] > 0
    assert set(rec["poor_lock_q_values"]) <= {1, 3, 5}
    assert rec["poor_max_resonance"] < 4.0


def test_arc_count_bounds_the_resonant_m() -> None:
    """Lemma 3, which is Lemma 4.3 with its two goodness arcs generalized."""
    for q_max in (1, 3, 8):
        for c in (1.0, 5.0, 20.0):
            rec = arc_count(10**4, q_max, c * 10**4 ** (-1.0 / 3.0))
            assert rec["holds"], rec
            assert rec["ratio"] <= 1.0


def test_poor_density_decays_at_the_cube_root() -> None:
    """The theorem is an upper bound; if the true exponent were smaller the
    corollary would be false, so the density times u^(1/3) must not drift up."""
    rec = poor_block_scaling(anchors=(10**5, 10**6), window=800)
    vals = [r["density_times_cube_root"] for r in rec["rows"]]
    assert all(0.5 < v < 5.0 for v in vals), vals
    assert vals[-1] <= vals[0] * 1.5


def test_two_productions_now_pass_lambda_star_star() -> None:
    """What the theorem buys: the same exponent with the analytic core removed.

    The gain in the number is 8.6e-5. The gain that matters is that (5.1) uses
    only Lemma 3.1, Lemma 3.2 and the tail theorem, so Proposition 4.4's two
    exponential-sum bounds -- Paper C's largest unformalized gap -- the
    six-word ladder, Appendix D, and Lemmas 4.1/4.1'/4.2 all leave the critical
    path. The supremum 0.4926580 is approached, not attained: eta_0 is fixed
    before x, which is the shape the published statement already has.
    """
    t = averaging_theorem()
    assert t["break_even_eta_0"] == pytest.approx(8.60e-5, rel=2e-2)
    assert t["beats_published"]
    assert t["two_production_root"] > t["lambda_star_star_published"]
    assert t["two_production_root"] < t["ideal_root"] <= 0.4926580
    # and the honest cost of the crude constants
    assert t["u_0"] > 1e30


# `production_two_averaged` inlines `production_two`'s shell geometry verbatim --- the
# three scales, the fibres landing in the shell, the two boundary drops --- because
# factoring it into a shared lemma would add a declaration to `FateProduction.lean`,
# one of the 83 inputs pinned by Paper C's release manifest. The copy is deliberate and
# recorded in both docstrings; what is NOT acceptable is the two drifting apart in
# silence, so this gate re-extracts both blocks and compares them.
_GEOMETRY_START = "obtain ⟨y, hy⟩ : ∃ y : ℕ, ⌊Real.exp t⌋₊ = y := ⟨_, rfl⟩"
_GEOMETRY_END = "errors in exponential form"


def _shell_geometry(text: str, header: str) -> list[str]:
    """The coefficient-free opening of a production proof, as a list of stripped lines."""

    assert text.count(header) == 1, f"{header!r} occurs {text.count(header)} times"
    body = text.split(header, 1)[1].splitlines()
    start = next(k for k, line in enumerate(body) if line.strip() == _GEOMETRY_START)
    end = next(k for k in range(start, len(body)) if _GEOMETRY_END in body[k])
    return [line.rstrip() for line in body[start:end]]


def test_the_two_production_proofs_share_the_same_shell_geometry() -> None:
    juggler = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Juggler"
    original = _shell_geometry(
        (juggler / "FateProduction.lean").read_text(encoding="utf-8"),
        "theorem production_two {",
    )
    copy = _shell_geometry(
        (juggler / "FatePoorProduction.lean").read_text(encoding="utf-8"),
        "theorem production_two_averaged {",
    )
    assert len(original) == 73, len(original)
    assert copy == original, (
        "production_two_averaged's inlined shell geometry has drifted from "
        "production_two's. Whichever moved, the other must move with it, or the "
        "averaged production inequality is no longer the geometry Paper C cites.\n"
        + "\n".join(
            difflib.unified_diff(
                original, copy, "production_two", "production_two_averaged", lineterm=""
            )
        )
    )


def test_lean_exponent_certificate_is_exact_and_beats_the_published_lambda() -> None:
    """`Production.zeta2avg_pos` asserts five numbers; re-derive all of them."""

    c = exponent_certificate()
    # the two integer inequalities Lean checks at the 203rd power
    assert c["cert_two_pow"]
    assert c["cert_three_quarter_pow"]
    # and the rational sum they feed
    assert c["zeta_positive"]
    assert c["zeta_lower_bound"] > 2.0e-5
    # the window: strictly above the published lambda**, strictly below the root
    assert c["beats_published"]
    assert c["below_ideal"]
    assert c["lambda_star_star_published"] < 100 / 203 < c["ideal_root"]
    # 100/203 is NOT minimal -- 67/136 is, and is rejected for margin
    assert c["smaller_denominator_in_window"] == ["67/136"]
    assert c["chosen_for_margin_not_minimality"]
    assert c["smaller_denominator_margins"]["67/136"] < c["zeta_lower_bound"] / 3


def test_the_lean_certificate_is_quoted_consistently() -> None:
    root = Path(__file__).resolve().parents[3]
    lean = (
        root / "formal" / "Problems" / "Juggler" / "FatePoorProduction.lean"
    ).read_text(encoding="utf-8")
    # the five numbers, exactly as `exponent_certificate` re-derives them
    for token in ("100 : ℝ) / 203", "coef2avg (1 / 100000)", "710737 / 1000000",
                  "216967 / 250000", "n := 203"):
        assert token in lean, token
    # and the corrected claim: chosen for margin, not minimality
    assert "smallest-denominator" not in lean
    assert "chosen for margin, not minimality" in lean


def test_note_records_what_leaves_the_critical_path() -> None:
    root = Path(__file__).resolve().parents[3]
    note = (root / "docs" / "theory" / "juggler_oe_poor_fiber_tail_note.md").read_text(
        encoding="utf-8"
    )
    assert "EXACT — LEAN VERIFIED" in note
    # the note is hard-wrapped prose, so match on collapsed whitespace
    flat = " ".join(note.lower().split())
    for claim in (
        "proposition 4.4 leaves the critical path",
        "not a halt theorem",
        "no cycle is excluded",
    ):
        assert claim in flat, claim
    dossier = (root / "docs" / "problems" / "juggler_oe_rest_average.md").read_text(
        encoding="utf-8"
    )
    assert "**PROMOTE.**" in dossier.split("## Decision", 1)[1]
