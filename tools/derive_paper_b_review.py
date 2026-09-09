"""Optional CAS audit: derive leading terms from exact four-corner powers.

Requires SymPy. This checks symbolic algebra, not asymptotic cancellation.
All offsets and frequency centers are held fixed during differentiation.
"""
from pathlib import Path
import argparse
import json
import sympy as s


def derive():
    x, z, eps = s.symbols('x z eps', positive=True)
    k, p, h1, h2 = s.symbols('k p h1 h2', positive=True)
    b, b1, b2, nstar, jf, a1, a2 = s.symbols('b b1 b2 nstar jf a1 a2', real=True)
    X = x**s.Rational(3, 2)
    c = s.Rational(3, 4)*k*x**s.Rational(9, 8)

    def corner(a, offset):
        return ((z+eps*(b1+b2+offset))**a-(z+eps*b1)**a
                -(z+eps*b2)**a+z**a)

    leading = {}
    for a in (s.Rational(3, 2), s.Rational(9, 4), s.Rational(9, 8)):
        offset = s.simplify(s.diff(corner(a, b), eps).subs(eps, 0))
        zero = s.simplify(s.diff(corner(a, 0), eps, 2).subs(eps, 0)/2)
        leading[a] = (offset, zero)
    rows = {}
    for label, index in (('nonzero_offset', 0), ('zero_offset', 1)):
        G = leading[s.Rational(3, 2)][index].subs(z, X)
        pure = k*leading[s.Rational(9, 4)][index].subs(z, X)/2
        # Only after differentiation does jf = G - bounded fractional part.
        anchor = s.diff(-c*(G-jf), x, 2).subs(jf, G)
        if index == 0:
            scale = k*b*x**s.Rational(-1, 8)
            center_coefficient = s.diff(k*leading[s.Rational(9, 4)][0]/2
                                       -c*leading[s.Rational(3, 2)][0], z).subs(z, X)
            center = s.diff(-nstar*X, x, 2).subs(nstar, center_coefficient)
            pieces = [s.diff(pure, x, 2), anchor, center]
        else:
            scale = k*p*x**s.Rational(-5, 8)
            wave = s.Rational(3, 2)*(a1*b1+a2*b2)*x**s.Rational(3, 4)
            wave_curvature = s.diff(wave, x, 2)
            center_subs = {a1: -2*h2*s.diff(c, x), a2: -2*h1*s.diff(c, x),
                           b1: 3*h1*s.sqrt(x), b2: 3*h2*s.sqrt(x)}
            wave_curvature = s.simplify(wave_curvature.subs(center_subs, simultaneous=True).subs(h1*h2, p))
            pieces = [s.diff(pure, x, 2).subs(b1*b2, 9*p*x),
                      anchor.subs(b1*b2, 9*p*x), wave_curvature]
        values = [s.simplify(v/scale) for v in pieces]
        rows[label] = {'pieces': [str(v) for v in values], 'sum': str(sum(values))}
    assert rows['nonzero_offset']['sum'] == '-243/512'
    assert rows['zero_offset']['sum'] == '3645/2048'
    # Fresh derivation of the k=0 fifth-coordinate curvature.
    a = s.Rational(9, 8)
    L, N = s.symbols('L N', real=True)
    f = L*x**(s.Rational(3, 2)*a)/2-N*X
    result = s.simplify(s.diff(f,x,2).subs(N,L*a*x**(s.Rational(3,2)*(a-1))/2)
                        /(L*x**s.Rational(-5,16)))
    assert result == s.Rational(81,512)
    return {'status':'PASS', 'sympy_version':s.__version__,
            'method':'Differentiate exact four-corner powers in an auxiliary shift; compose with X; freeze labels while differentiating; substitute moving values afterwards.',
            'curvatures':rows, 'k_zero_fifth_curvature':str(result),
            'scope':'Symbolic leading coefficients only. Remainder uniformity and analytic bounds require the written proofs.',
            'independent_mathematical_review':False}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    rendered=json.dumps(derive(),indent=2)+'\n'
    if args.output: args.output.write_text(rendered,encoding='utf-8')
    print(rendered,end='')
