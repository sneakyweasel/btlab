"""Exact controls for an artificial coherent density, not Collatz coefficients.

The formula uses the first differing ternary digit. Lean instead defines the
density recursively on words; the two representations provide independent controls.
"""

from fractions import Fraction


def cylinder_density(root: int, residue: int, level: int, *, syracuse: bool = False) -> Fraction:
    """Density at a residue cylinder, with unit or Syracuse first-row normalization."""
    if root < 1 or root % 3 == 0:
        raise ValueError("root must be a positive integer coprime to three")
    if level < 1 or not 0 <= residue < 3**level:
        raise ValueError("require level >= 1 and a residue in [0, 3**level)")
    first = residue % 3
    if first == 0:
        return Fraction()
    if first != root % 3:
        value = Fraction(1)
    else:
        difference = (root - residue) % 3**level
        if difference == 0:
            value = Fraction(1, 3 ** (level - 1))
        else:
            power = 1
            while difference % (3 * power) == 0:
                power *= 3
            value = Fraction(4, power)
    return first * value if syracuse else value


def diagnostic() -> dict:
    """Small fixed-root examples and a check separating the actual signed operator."""
    from research.collatz.fibre_mass import residue_transfer

    result = {"model": "artificial coherent densities", "roots": [], "actual_spikes": []}
    for root in (7, 47):
        result["roots"].append({
            "root": root,
            "unit_path": [str(cylinder_density(root, root % 3**level, level))
                          for level in range(1, 7)],
            "syracuse_path": [str(cylinder_density(root, root % 3**level, level, syracuse=True))
                              for level in range(1, 7)],
        })
    for sign, target in ((1, 17), (-1, 1)):
        table = residue_transfer((0, 1, 1), sign)
        result["actual_spikes"].append({
            "sign": sign, "target": target, "coefficient": str(table[target % 9]),
            "model_upper_bound": "4/3",
        })
    return result


if __name__ == "__main__":
    import json

    print(json.dumps(diagnostic(), indent=2))
