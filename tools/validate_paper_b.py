"""Exact finite checks for Paper B; no analytic estimates are tested.

Run with Python 3.10+ using only the standard library:
    python validate_paper_b.py --output paper_b_validation.json
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from math import isqrt
from pathlib import Path


def step(n: int, letter: str | None = None) -> int:
    odd = (n % 2 == 1) if letter is None else letter == 'O'
    return isqrt(n**3 if odd else n)


def contracting(w: str) -> bool:
    return 3**w.count('O') < 2**len(w)


def minimal_words(depth: int) -> list[str]:
    out = []
    for length in range(1, depth + 1):
        for letters in product('EO', repeat=length):
            w = ''.join(letters)
            if contracting(w) and not any(contracting(w[:j]) for j in range(1, length)):
                out.append(w)
    return out


def check() -> dict:
    words = minimal_words(5)
    expected = {'E', 'OE', 'OOEE', 'OOOEE', 'OOEOE'}
    assert set(words) == expected
    assert sum((Fraction(1, 2**len(w)) for w in words if len(w) <= 4), Fraction()) == Fraction(13, 16)
    assert sum((Fraction(1, 2**len(w)) for w in words), Fraction()) == Fraction(7, 8)

    envelope_cases = 0
    for n in range(1, 2001):
        x, odds = n, 0
        for d in range(1, 9):
            odds += x % 2
            x = step(x)
            assert x ** (2**d) <= n ** (3**odds)
            if n >= 2 and 3**odds < 2**d:
                assert x < n
            envelope_cases += 1

    indicator_cases = 0
    for n in range(1, 402, 2):
        x, actual = n, ''
        for _ in range(5):
            actual += 'O' if x % 2 else 'E'
            x = step(x)
        for length in range(1, 6):
            for suffix in product('EO', repeat=length - 1):
                w = 'O' + ''.join(suffix)
                x, indicator = n, 1
                for t in range(length - 1):
                    x = step(x, w[t])
                    sign = -1 if x % 2 else 1
                    eps = 1 if w[t + 1] == 'E' else -1
                    indicator *= (1 + eps * sign) // 2
                assert indicator == int(actual[:length] == w)
                indicator_cases += 1

    # Identity and upper bound of Lemma 7.1 after substituting rational square roots.
    factorization_cases = 0
    for denominator in (1, 3, 7):
        for ai in range(1, 51):
            for bi in range(ai, ai + 21):
                a, b = Fraction(ai, denominator), Fraction(bi, denominator)
                theta = b*b - a*a
                error = a**3 - Fraction(3, 2)*a*a*b + Fraction(1, 2)*b**3
                assert error == Fraction(1, 2)*(a-b)**2*(2*a+b)
                assert 0 <= error*a <= Fraction(3, 8)*theta**2
                factorization_cases += 1

    # General carry identity, including exact integer and threshold endpoints.
    carry_cases = 0
    for ai in range(101):
        for bi in range(101):
            a, b = Fraction(ai, 10), Fraction(bi, 13)
            fa, fb = a.numerator // a.denominator, b.numerator // b.denominator
            ab = a+b
            fab = ab.numerator // ab.denominator
            assert fab-fa == fb + int((a-fa)+(b-fb) >= 1)
            carry_cases += 1

    # Exact proportions of words with no contracting prefix, not empirical orbit densities.
    surviving = {'O': 1}
    tail = []
    for depth in range(1, 17):
        if depth > 1:
            surviving = {w+c: 1 for w in surviving for c in 'EO' if not contracting(w+c)}
        tail.append({'depth': depth, 'surviving_odd_rooted_words': len(surviving),
                     'fair_share_among_all_starts': str(Fraction(len(surviving), 2**depth))})
    assert tail[3]['fair_share_among_all_starts'] == '3/16'
    assert tail[4]['fair_share_among_all_starts'] == '1/8'

    return {'status': 'PASS', 'scope': 'Exact finite checks only; no asymptotic, kernel, or Lean certification.',
            'minimal_certificates_through_five': words,
            'four_step_density_arithmetic': '13/16', 'conditional_five_step_density': '7/8',
            'envelope_cases': envelope_cases, 'branch_indicator_cases': indicator_cases,
            'factorization_cases': factorization_cases, 'carry_cases': carry_cases,
            'word_survivor_counts': tail}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload, encoding='utf-8')
    print(payload)
