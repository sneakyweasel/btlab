"""Pairing check for the OE-fiber constant 1/7 -> 1/3."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.fate_contagion import (
    fiber_stats,
    is_good_fiber,
    lambda_root,
)
from research.juggler_sequence.oe_fiber_constant import (
    PAIRING_SLACK,
    extremal_scan,
    poor_fiber_decay,
    THIRD_RECURSION,
    adversarial_three_one_lock,
    pairing_ok,
    scarcer_count,
    summary,
    synthetic_census,
    synthetic_orbit,
)


def test_period_three_split_is_one_third() -> None:
    fracs = synthetic_orbit(1.0 / 3.0, 0.0, 66, 0.0)
    h, n_lo, n_hi = scarcer_count(fracs)
    assert h == 66
    assert min(n_lo, n_hi) / h > 0.32
    assert pairing_ok(n_lo, n_hi, h)


def test_pairing_slack_covers_known_witness() -> None:
    st = fiber_stats(1003635)
    assert st["size"] == 67
    assert st["good"] == 22
    assert pairing_ok(st["good"], st["size"] - st["good"], st["size"])
    assert min(st["good"], st["size"] - st["good"]) + PAIRING_SLACK >= st["size"] / 3.0


def test_third_recursion_root_is_near_448() -> None:
    root = lambda_root(THIRD_RECURSION)
    assert abs(root - 0.448) < 5e-3
    sweep = lambda_root([(1.0, 0.5), (5.0 / 21.0, 3.0 / 8.0), (2.0 / 21.0, 0.75)])
    ideal = lambda_root([(1.0, 0.5), (1.0 / 3.0, 0.75)])
    assert sweep < root < ideal


def test_adversarial_three_one_is_not_monotone() -> None:
    adv = adversarial_three_one_lock()
    assert adv["steps_in_lemma_31"]
    assert not adv["monotone"]
    assert adv["proportion"] < 0.30
    assert not adv["pairing_ok"]


def test_synthetic_and_spot_census_obey_pairing() -> None:
    syn = synthetic_census()
    assert syn["n_fail"] == 0
    assert syn["n_ok"] > 100
    result = summary()
    assert result["classification"] == "OE_FIBER_PAIRING_CONSISTENT"
    spot = result["fibers"]["spot_1e6"]
    assert spot["n_below_pairing"] == 0
    assert spot["min_scarcer_on_good"] > 0.32
    assert abs(result["lambda_roots"]["block_average_plus_third"] - 0.448) < 5e-3


def test_dossier_headings_and_promote() -> None:
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oe_fiber_constant.md").read_text(
        encoding="utf-8"
    )
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
    assert "PROMOTE" in decision

# the four scales at which the pairing floor is attained exactly, with the fibre
# size and the scarcer-colour count; `scarcer == H // 3` at every one of them
ATTAINING = ((1018590, 68, 22), (10001831, 143, 47),
             (100001607, 310, 103), (1000011666, 667, 222))


def test_the_pairing_one_third_is_attained_not_merely_bounded() -> None:
    """`2/9` is sharp as a pointwise coefficient, because `1/3` is reached.

    `J-fate-fiber-sweep` records "min on good fibers 0.328 at alpha_m ~ 1/3"
    from a 4000-wide spot at `1e6`. That says the minimum is *near* a third. It
    does not say the bound is sharp, and sharpness is what decides whether any
    pointwise argument can raise `2/9 = (2/3)(1/3)`.

    It is sharp. At four scales the minimising good fibre has scarcer colour
    exactly `floor(H_m/3)` -- so the `-2` in `G_m >= H_m/3 - 2` is pure slack --
    and the attained share rises to `1/3` FROM BELOW as `H` grows. No pointwise
    per-fibre constant above `1/3` can therefore hold, and `0.3261209621`, the
    root of `2^-L + (2/9)(3/4)^L = 1`, is a real ceiling for the two-production
    route rather than an artifact of a lossy lemma.

    What is NOT shown: that the truth is `1/3`. The mean share is `1/2`
    (`J-fate-fiber-sweep` census) and the attaining fibres are log-thin. The
    constant is sharp; the map is not adversarial.
    """
    shares = []
    for m, h, scarcer in ATTAINING:
        st = fiber_stats(m)
        assert st["size"] == h, m
        assert min(st["good"], st["size"] - st["good"]) == scarcer, m
        assert scarcer == h // 3, f"m={m}: floor(H/3) is the attained value"
        assert is_good_fiber(m, st["alpha"]), f"m={m} must satisfy the sweep hypothesis"
        shares.append(scarcer / h)

    assert all(s < 1 / 3 for s in shares), "the floor is approached from below"
    assert shares == sorted(shares), f"the share must rise toward 1/3: {shares}"
    assert shares[-1] > 0.3328 and 1 / 3 - shares[-1] < 6e-4


def test_the_minimiser_sits_where_the_detune_cancels_the_curvature() -> None:
    """Not an accident of search: the extremal fibre has `alpha` just below `p/3`.

    The fibre phase carries a quadratic term, so a persistent three-cycle needs
    the linear detune to cancel the curvature across the fibre. That predicts
    the minimiser at `alpha ~ p/3 - 1/(3(H-1))`, i.e. `detune * (H-1) ~ -1/3`,
    rather than at the resonance itself.
    """
    for m, h, _ in ATTAINING:
        alpha = fiber_stats(m)["alpha"]
        p = 1 / 3 if alpha < 0.5 else 2 / 3
        detune = (alpha - p) * (h - 1)
        assert -0.7 < detune < -0.1, f"m={m}: detune*(H-1) = {detune:.3f}, want ~ -1/3"


def test_a_narrow_scan_still_finds_the_witness() -> None:
    """The scan machinery agrees with the hand-checked witness."""
    scan = extremal_scan(1_018_000, 1_019_000)
    w = scan["witness"]
    assert w["m"] == 1018590 and w["attains_floor_third"]
    assert w["scarcer"] == w["floor_third"] == 22


def test_the_poor_fibre_set_decays_so_the_dossier_parenthetical_was_wrong() -> None:
    """`juggler_oe_rest_average.md` observation (1) reads `P` as "not `O(U^(-1/3))`".

    That was inferred from `[2^8, 2^16]`, where `H_m <= 27` and binomial noise
    alone predicts about fourteen per cent of fibres below share `0.40`. Carried
    four more octaves the `1/m`-weighted fraction falls by about the cube-root
    factor, so the parenthetical is an artifact of where the scan stopped.

    This does NOT unpark that branch. Its PARK rests on observations (2) to (4),
    and the quantity Theorem 5.3 needs is poor-set mass relative to `A`, not to
    all integers, so an adversarial backward-closed `A` is untouched by this.
    """
    # the sample is seeded, so these numbers are reproducible; the threshold is
    # set for 500 samples, where a fraction near 0.04 carries about 20 per cent
    # Poisson noise. The probe's default run (1200 samples, five octaves) gives
    # 0.0508 -> 0.0072, a factor 7.1 against the cube-root prediction 6.35.
    decay = poor_fiber_decay(exponents=(16, 20), samples=500)
    first, last = (r["poor_log_fraction"] for r in decay["rows"])
    assert decay["decays"] and first > last
    assert first > 0.03, "the dossier's regime should reproduce at 2^16"
    assert last < 0.6 * first, "and it must be clearly down four octaves later"
