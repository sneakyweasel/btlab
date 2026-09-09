"""Exact checks supporting the Paper B proof repairs, not asymptotic verification."""
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path


def check():
    # The differenced linearization is an algebraic identity in two endpoint pairs.
    identity_cases=0
    for a0 in range(1,21):
        for a1 in range(a0,a0+6):
            for s0 in (0,1,5,20):
                for s1 in (0,1,5,20):
                    b0=Q(a0)+Q(s0,100*a0)
                    b1=Q(a1)+Q(s1,100*a1)
                    x0,x1=b0*b0,b1*b1
                    m0,m1=a0*a0,a1*a1
                    assert 0<=x0-m0<1 and 0<=x1-m1<1
                    e0=a0**3-Q(3,2)*m0*b0+Q(1,2)*b0**3
                    e1=a1**3-Q(3,2)*m1*b1+Q(1,2)*b1**3
                    ah=Q(3,2)*x0*(b1-b0)-Q(1,2)*(b1**3-b0**3)
                    rhs=ah+Q(3,2)*(m1-m0)*b1-Q(3,2)*(x0-m0)*(b1-b0)+e1-e0
                    assert rhs==a1**3-a0**3
                    identity_cases+=1

    # Exact carry expansion as a polynomial identity in the exponential value.
    carry_cases=0
    for theta in [Q(i,20) for i in range(20)]:
        for z in [Q(i,20) for i in range(20)]:
            kappa=int(theta+z>=1)
            b0=theta-Q(1,2)
            b1=theta+z-kappa-Q(1,2)
            assert z+b0-b1==kappa
            for value in (Q(-2),Q(-1,3),Q(0),Q(1),Q(7,4)):
                assert 1-z+z*value+(b0-b1)*(value-1)==value**kappa
                carry_cases+=1

    # Linear exponent comparisons attain their extrema at the four corners.
    exponent_cases=0
    for alpha in (Q(0),Q(1,24)):
        for beta in (Q(0),Q(1,12)):
            target=Q(7,8)+beta/2
            costs={
                'zero_mode_length':Q(5,8)+(alpha+beta)/2,
                'zero_mode_cells':Q(7,8)+(beta-alpha)/2,
                'nonzero_mode_length':Q(3,4)+Q(1,4)/2,
                'nonzero_mode_cells':Q(3,4)+beta,
                'deleted_sawtooth':Q(3,4)+alpha+beta,
                'linearization_remainder':Q(1,4)+alpha,
                'carry_discrepancy':Q(5,6),
                'carry_fourier_tail_base':Q(3,4)}
            for label,cost in costs.items():
                assert cost<=target,(label,alpha,beta,cost,target)
                exponent_cases+=1
            assert alpha+beta-Q(1,4)<=-Q(1,8)
            exponent_cases+=1
    assert Q(2)-Q(1,12)==Q(15,8)+Q(1,24)==Q(23,12)
    assert (Q(23,12))/2==Q(23,24)
    assert Q(1,24)+Q(5,8)==Q(2,3)
    assert Q(3,4)+Q(1,12)==Q(5,6)
    exponent_cases+=4
    return {
        'status':'PASS',
        'scope':'Exact finite identity and exponent checks; the asymptotic claims are supported by written proofs, not these tests.',
        'differenced_identity_cases':identity_cases,
        'carry_expansion_cases':carry_cases,
        'exponent_comparisons':exponent_cases,
        'restored_four_step_density':'13/16, by Corollary 4.6 and Theorem 5.2 of the repaired manuscript',
        'remaining_open':'General decorated kernel, its short-interval version, and the OOOEE correlation hypothesis.'
    }


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    payload=json.dumps(check(),indent=2)+'\n'
    if args.output: args.output.write_text(payload,encoding='utf-8')
    print(payload)
