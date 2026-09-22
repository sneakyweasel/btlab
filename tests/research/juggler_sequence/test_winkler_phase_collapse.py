"""Winkler's normalised count R+_r is a function of the phase {r log2 3} alone.

Measured at depth 5000, orders r = 1..3154, with c_r = M_(m_r + 1) from the survivor
counts of ``jump_spectrum``:

- c_r reproduces A100982; R+_r stays inside Winkler's Corollary 12 envelope,
  1 <= R+_r < alpha/(alpha - 1) = 2.7095112914, reaching 1.000000 and 2.708934.
- Binned by delta_r into 20 bins, the across-bin range is 1.685, 1.686, 1.687 and the
  within-bin spread 0.033, 0.032, 0.033 in the windows r in [395, 788], [789, 1577],
  [1578, 3154]: a signal of x50.5, x52.0, x51.7. The per-bin shape drifts by 0.0069 and
  then 0.0011 between successive windows, so it converges.
- Shuffling delta_r among the orders drops the signal to x0.39: the collapse is the
  pairing of R+_r with its own phase, not the binning.
- R+ jumps upward across the orbit points {n log2 3}: +0.633, +0.148, +0.188, +0.066,
  +0.098, +0.039, +0.023, +0.042 for n = 1..8, while the six control points at the
  midpoints of the widest gaps between the first 40 orbit points show +0.0017 to +0.0045.

Computationally verified, not proved. The delta-side counterpart of psi's jump
spectrum; see J-winkler-ratio-collapses-onto-the-phase.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence import winkler_phase_collapse as W

A100982_HEAD = [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637,
                51033, 108950, 312455, 663535, 1900470, 5936673, 13472296]


@pytest.fixture(scope="module")
def payload() -> dict:
    return W.probe_payload(W.DEPTH)


def test_counts_are_a100982(payload: dict) -> None:
    assert payload["orders"] == 3154
    assert payload["head"] == A100982_HEAD


def test_ratio_stays_in_winklers_envelope(payload: dict) -> None:
    assert payload["ratio_min"] == pytest.approx(1.0, abs=1e-12)
    assert payload["ratio_max"] < W.UPPER
    assert payload["ratio_max"] > W.UPPER - 0.01


def test_ratio_collapses_onto_the_phase(payload: dict) -> None:
    for w in payload["windows"]:
        assert w["signal"] > 45
        assert 1.6 < w["range"] < 1.75
    first, second = payload["shape_drift"]
    assert second < first < 0.01
    means = payload["windows"][-1]["means"]
    assert means[0] < 1.02 and means[-1] > 2.69


def test_shuffling_the_phase_destroys_the_collapse(payload: dict) -> None:
    assert payload["control_signal"] < 1.0


def test_jumps_sit_on_the_orbit(payload: dict) -> None:
    jumps = payload["orbit_jumps"]
    controls = payload["control_jumps"].values()
    assert jumps[1] > 0.6
    assert min(jumps.values()) > 0.02
    assert max(abs(c) for c in controls) < 0.005
    assert min(jumps.values()) > 4 * max(abs(c) for c in controls)


def test_control_points_are_off_the_orbit() -> None:
    """The control must itself be checked: two hand-picked controls once sat on the orbit."""
    orbit = [W.orbit_point(n) for n in range(1, 41)]
    for x in W.control_points():
        assert min(abs(x - o) for o in orbit) > 0.015
