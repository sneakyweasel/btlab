"""Check the actual Gamma-normalized empirical law and its absolute continuity."""
from fractions import Fraction
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyPassageLawChecks.original_count_gamma_empirical_limit",
    "Problems.Juggler.BeattyPassageLawChecks.explicit_amplitude_law_absolutelyContinuous",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "volume_eq_zero_of_nonzero_deriv_image_null",
            "ae_hasDerivAt_zero_of_monotone_null_range",
            "map_restrict_absolutelyContinuous_of_ae_nonzero_deriv",
            "certificateProfile_ae_hasDerivAt_zero",
            "certificatePhaseAmplitude_ae_nonzero_deriv",
            "certificatePhaseAmplitude_bounds",
            "certificatePassageLaw_absolutelyContinuous_volume",
            "certificateLaw_mutuallySingular_passageLaw",
            "certificatePassageLaw_cdf_continuous",
            "certificateGammaRatio_threshold_frequency",
            "certificateGammaRatio_average_tendsto",
        )
    },
}


def test_original_count_passage_law_consumers():
    """Check the exact count interface and reject any nonstandard proof input."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyPassageLaw.lean"],
        cwd=ROOT / "formal", capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=600,
    )
    assert result.returncode == 0, (result.stdout + result.stderr)[-12000:]
    assert not result.stderr.strip(), result.stderr
    pattern = re.compile(
        r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]\s*$", re.MULTILINE,
    )
    records = pattern.findall(result.stdout)
    assert len(records) == len(EXPECTED), result.stdout
    assert {name for name, _ in records} == EXPECTED
    for name, dependencies in records:
        assert {value.strip() for value in dependencies.split(",")} <= STANDARD, name
    assert not pattern.sub("", result.stdout).strip(), result.stdout


def test_finite_occupation_identity_endpoint_and_multiplicity():
    """Check the written cutoff formula exactly, not its infinite-series limit.

    For q=1/16 and quarter phases all rescaled endpoints are rational.
    Compare phase-interval integration with value-interval integration for
    positive and negative power observables. The unfinished cutoff has a
    nonzero endpoint term; several value intervals overlap in both cases.
    """
    q = Fraction(1, 16)
    phase_factors = [Fraction(1), Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), q]
    for weights in ([2, 3, 1], [2, 3, 10]):
        heights = [Fraction(1)]
        for weight in weights:
            heights.append(heights[-1] + weight)
        intervals = [
            (phase_factors[i + 1] * heights[i], phase_factors[i + 1] * heights[i + 1])
            for i in range(3)
        ]
        assert max(intervals[0][0], intervals[1][0]) < min(intervals[0][1], intervals[1][1])
        endpoints = sorted({point for interval in intervals for point in interval})
        for power in (-2, -1, 1, 2, 3):
            # This is a times the phase integral, where a=-log(q).
            phase_integral = sum(
                height**power * (phase_factors[i]**power - phase_factors[i + 1]**power) / power
                for i, height in enumerate(heights)
            )
            gap_integral = sum((upper**power - lower**power) / power for lower, upper in intervals)
            endpoint_term = (1 - (q * heights[-1])**power) / power
            assert phase_integral == gap_integral + endpoint_term
            assert (endpoint_term == 0) == (sum(weights) == 15)
            multiplicity_integral = Fraction(0)
            union_integral = Fraction(0)
            for left, right in zip(endpoints, endpoints[1:]):
                midpoint = (left + right) / 2
                multiplicity = sum(lower < midpoint < upper for lower, upper in intervals)
                cell_integral = (right**power - left**power) / power
                multiplicity_integral += multiplicity * cell_integral
                union_integral += bool(multiplicity) * cell_integral
            assert gap_integral == multiplicity_integral
            assert union_integral < gap_integral
        # Exponentiated logarithmic mass identity: the q factors cancel.
        product = Fraction(1)
        for lower, upper in intervals:
            product *= upper / lower
        assert product == heights[-1]
        assert (product == 1 / q) == (sum(weights) == 15)
