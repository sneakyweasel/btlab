"""Exact finite checks for the OOEOE repair; no asymptotic or Lean certification."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json

def validate():
    count=0
    for q in (F(1),F(3,2),F(7,3),F(11,4),F(101,7)):
        for k in (-7,-1,1,2,9):
            B=F(3,4)*k*q**3
            N=B.numerator//B.denominator
            beta=B-N
            assert 0<=beta<1
            for ell in (-5,0,3):
                for r in range(-8,9):
                    R=r-N+F(ell,2)
                    assert F(9,16)*k*q+F(3,4)*R/q**2==F(3,4)*(r+beta+F(ell,2))/q**2
                    count+=1
    curvature=F(1,2)*F(27,16)*F(11,16)-F(3,4)*F(9,8)*F(1,8)
    assert curvature==F(243,512)
    H=F(1,12); J=F(1,48); T=F(1,8)
    costs={
        'squared_diagonal':2-H,
        'squared_gap_boundary':F(15,8)+H/2,
        'squared_frequency_boundary':J+F(31,16)-H/2,
        'squared_floor_deletion':J+H+F(7,4),
        'squared_nonzero_carry':F(15,8),
    }
    assert all(x<=F(23,12) for x in costs.values())
    checks={
        'intervals_longer_than_shift':F(7,16)-J>H,
        'R_center_dominates_cutoff':F(9,16)>T,
        'residual_floor_error':F(5,8)+T<F(23,24),
        'Taylor_error':J+F(7,16)<F(23,24),
        'nonzero_carry_curvature':J+H<F(1,4),
        'smooth_passenger_curvature':J<F(9,16),
        'pure_mode_curvature':J<F(3,16),
        'pure_mode_sum':J/2+F(27,32)<F(23,24),
        'Fourier_error':F(7,8)<F(23,24),
        'ETK_log_absorption':F(23,24)<F(47,48),
    }
    assert all(checks.values())
    assert F(1,2)+F(1,4)+F(1,16)+F(1,32)==F(27,32)
    assert F(27,32)+F(1,32)==F(7,8)
    return {
        'status':'PASS',
        'scope':'Exact centering identities and exponent bookkeeping; the asymptotic results depend on the printed proofs.',
        'centering_identity_cases':count,
        'frozen_frequency_curvature':str(curvature),
        'squared_sum_exponents':{k:str(v) for k,v in costs.items()},
        'strict_exponent_checks':checks,
        'certificate_subfamily_density':'27/32',
        'full_five_step_density':'7/8 remains conditional on H_0(OOOEE)',
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.dumps(validate(),indent=2,ensure_ascii=False)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(result,encoding='utf-8')
    print(result)
