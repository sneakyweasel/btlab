"""Independent interval check of Paper A's displayed exclusion inequalities.

Does not recompute or assume a proof of the supplied descent floor.
The all-length screening uses rational lower bounds for logarithms.
The remaining comparisons use mpmath interval arithmetic at 60 digits.
"""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import json
from mpmath import iv

iv.dps=60
S=10**60
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path('paper_a_numeric_check.json'))
parser.add_argument('--include-conditional', action='store_true', help='Also check Corollary 5.14, assuming its unverified 554000000 floor')
args=parser.parse_args()

def log_bounds(n):
    k=n.bit_length()-1
    a=Fraction(n,2**k)
    def series(x):
        z=(x-1)/(x+1)
        terms=160
        v=2*sum((z**(2*j+1)/ (2*j+1) for j in range(terms)),Fraction())
        rem=2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
        return v,v+rem
    lo2,hi2=series(Fraction(2))
    lo,hi=series(a)
    lo+=k*lo2
    hi+=k*hi2
    return lo.numerator*S//lo.denominator, -((-hi.numerator*S)//hi.denominator)

l2,h2=log_bounds(2)
l3,h3=log_bounds(3)
ln2,ln3=iv.log(2),iv.log(3)
q=[1,2,3,8,19,65,84,485,1054,24727,50508,125743,176251,301994]

def digits(L):
    r=L;s=0
    for d in q[::-1]:
        b,r=divmod(r,d);s+=b
    assert r==0
    return s

def values(L,N):
    n=N+1
    ol=L*l2//h3+1
    oh=L*h2//l3+1
    assert ol==oh
    o=ol;e=L-o
    theta=1-iv.exp(L*ln2-o*ln3)
    ni=iv.mpf(n);ln=iv.log(ni);t=iv.mpf(isqrt(n**3))
    parity=iv.mpf(6)/5*(e/(ni*ln)+(o-e)/(t*iv.log(t))+e/(2*ni**2*ln))
    D=iv.mpf(21)/20*e/ni+iv.mpf(7)/10*o/(ni*iv.sqrt(ni))
    nu=ln-D
    np=iv.exp(nu)
    # A sharper rigorous version of the paper's quadratic Laplace majorant.
    # For x >= 0, P4=1-2x+3x²-4x³+5x⁴ >= (1+x)^(-2), since
    # (1+x)^2 P4-1=6x^5+5x^6 >= 0. P4 is positive, so its integral
    # against exp(-s) may be extended to infinity. Factorial moments give:
    c_upper=(1-2/nu+6/nu**2-24/nu**3+120/nu**4)/(ln3*nu)
    err=iv.mpf(2*digits(L))/L
    walk=iv.mpf(6)/5*L/(np*nu)*(c_upper+err)
    def bounds(v): return [str(v.a),str(v.b)]
    return {'L':L,'o':o,'s':digits(L),'parity_excludes':bool(theta.a>parity.b),
            'walk_excludes':bool(theta.a>walk.b),'theta':bounds(theta),
            'walk_margin':bounds(theta/walk),'nu':bounds(nu)}

reports=[]
floors=[(10**6,25781),(26254995,176251),(162849448,478245),(350000000,780239)]
if args.include_conditional: floors.append((554000000,1082233))
for N,cap in floors:
    n=N+1;ln,_=log_bounds(n)
    rest=[];parity_count=0;crude_count=0;walk_count=0
    for L in range(1,cap+1):
        o=L*l2//h3+1
        assert o==L*h2//l3+1
        lam=o*l3-L*h2
        assert lam>0
        # theta >= Lambda/(1+Lambda), n log n theta > L.
        if n*ln*lam > L*S*(S+lam):
            crude_count+=1;continue
        r=values(L,N)
        if r['parity_excludes']:
            parity_count+=1;continue
        rest.append(r)
        if r['walk_excludes']:walk_count+=1
    alive=[r['L'] for r in rest if not r['walk_excludes']]
    reports.append({'floor_assumed':N,'lengths_checked':cap,'crude_exclusions':crude_count,
                    'parity_exclusions':parity_count,'walk_exclusions':walk_count,
                    'not_excluded':alive,'walk_rows':rest})
    assert alive == [cap], (N, cap, alive)
    print(N,cap,'not excluded:',alive,flush=True)

bound_examples={str(L):values(L,26254995) for L in [50508,301994,780239,16785920]}
args.output.write_text(json.dumps({'arithmetic':'rational log bounds + 60-digit mpmath intervals','floor_verification':'not rerun; conditional on archived descent-floor computations','results':reports,'window_examples':bound_examples},indent=2),encoding='utf-8')
