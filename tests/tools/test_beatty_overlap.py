"""Independent interval examples and truncation-bound checks for the overlap audit."""
from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx
import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
SPEC = importlib.util.spec_from_file_location("beatty_overlap_audit", ROOT / "tools/check_beatty_overlap.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


def contains(box, value):
    return Fraction(box["lower"]) <= value <= Fraction(box["upper"])


def test_exact_pair_energy_and_logarithmic_kernel():
    """The intersection term occurs twice; integrating 1/y^2 is not length."""
    with ctx.workprec(192):
        result = AUDIT.sweep_energy([(arb(1), arb(2)), (arb("1.5"), arb(3))], arb(1))
    assert contains(result["multiplicity_square_integral"], Fraction(7, 2))
    assert contains(result["density_square_integral"], Fraction(7, 6))
    assert result["maximum_multiplicity"] == 2
    boxes = [(2, 2, 4, 4, 2, 2), (3, 3, 6, 6, 3, 3)]
    exact = AUDIT.overlap_bounds(boxes, 2)
    assert Fraction(exact["lower"]) == Fraction(exact["upper"]) == Fraction(7, 2)


def test_position_uncertainty_preserves_known_widths():
    """All translations inside the boxes are enclosed, including containment."""
    boxes = [(0, 4, 2, 6, 2, 2), (1, 5, 4, 8, 3, 3)]
    result = AUDIT.overlap_bounds(boxes, 1)
    for x in range(5):
        for y in range(1, 6):
            actual = 5 + 2*max(0, min(x+2, y+3)-max(x, y))
            assert contains(result, actual)
    assert Fraction(result["upper"]) == 9  # Expanding the widths would overestimate this.


def test_unresolved_event_order_fails():
    with ctx.workprec(192), pytest.raises(ArithmeticError, match="order is unresolved"):
        AUDIT.sweep_energy([(arb(1), arb(2)), (arb("2 +/- 0.1"), arb(3))], arb(1))


def test_finite_models_are_separate_from_true_head_bounds():
    """The same exact finite expressions agree at two independent precisions."""
    low = AUDIT.compute(32, 192)
    high = AUDIT.compute(32, 256)
    assert low["counts_sha256_hex_lines"] == high["counts_sha256_hex_lines"]
    for lm, hm in zip(low["models"], high["models"]):
        for lh, hh in zip(lm["heads"], hm["heads"]):
            for key in ("multiplicity_square_integral", "density_square_integral",
                        "density_three_halves_integral"):
                assert Fraction(lh[key]["lower"]) <= Fraction(hh[key]["upper"])
                assert Fraction(hh[key]["lower"]) <= Fraction(lh[key]["upper"])
            if "true_head_overlap_energy" in lh:
                assert Fraction(lh["true_head_overlap_energy"]["lower"]) >= 0
                assert Fraction(lh["true_head_overlap_energy"]["upper"]) >= Fraction(
                    lh["true_head_overlap_energy"]["lower"])
    assert "No bound on the infinite overlap sum" in low["scope"]


@pytest.mark.parametrize("orders,bits", [(8, 192), (17, 192), (16384, 192), (16, 128)])
def test_reject_unplanned_scope(orders, bits):
    with pytest.raises(ValueError):
        AUDIT.compute(orders, bits)
