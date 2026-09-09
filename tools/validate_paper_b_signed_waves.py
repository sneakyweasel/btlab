"""Exact controls for the signed zero-offset supplement, not an analytic proof."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json

def validate():
    counts={}
    # Leading frozen coefficients: never differentiate moving beta values.
    gp=F(-9,16)
    gpp=gp*F(-7,4)
    cp=F(3,4)*F(9,8)
    anchor=2*cp*gp+F(3,4)*gpp
    assert gpp==F(63,64)
    assert anchor==F(-27,128)
    assert 9*anchor==F(-243,128)
    assert F(3,2)*F(3,4)*F(-1,4)*3==F(-27,32)
    assert F(3,2)*2*F(3,4)==F(9,4)
    # The anchor part must remain in the bounded Fourier coefficient.
    anchor_theta=F(3,4)*F(-3,8)*9
    assert anchor_theta==F(-81,32)
    assert 9*anchor-anchor_theta*F(3,4)==0
    assert F(9,4)+F(9,8)==F(27,8)
    counts["curvature_and_centering_coefficients"]=8

    cases=0
    for y0 in range(-7,8):
        for y1 in range(-7,8):
            for y2 in range(-7,8):
                for u in (-8,-2,0,2,8):
                    assert u*(y1-y0)-u*(y1-y0)==0
                    assert u*(y1-y0)-F(u,2)*(y2-y0)==-F(u,2)*(y2-2*y1+y0)
                cases+=1
    counts["signed_cancellation_triples"]=cases

    cases=0
    for bw_num in range(-21,22):
        bw=F(bw_num,5)
        n=bw//1
        for ba_num in range(-12,13):
            ba=F(ba_num,4)
            d=bw-n+ba
            for x_num in (-13,0,5,17):
                x=F(x_num,7)
                theta=x-x//1
                phase=-(bw+ba)*theta-(-n*x-d*theta)
                assert phase==n*(x//1)
                assert phase.denominator==1
                cases+=1
    counts["wave_only_centering_cases"]=cases

    nodes=[F(1),F(33,32),F(17,16)]
    probes=[F(1),F(65,64),F(33,32),F(67,64),F(17,16)]
    cases=0
    for a in range(-3,4):
        for b in range(-3,4):
            for c in range(-3,4):
                if a==b==c==0:
                    continue
                for t in probes:
                    q=a+b*t+c*t*t
                    interp=F(0)
                    for i,ti in enumerate(nodes):
                        li=F(1)
                        for j,tj in enumerate(nodes):
                            if i!=j:
                                li*= (t-tj)/(ti-tj)
                        interp+=(a+b*ti+c*ti*ti)*li
                    assert interp==q
                    # Curvature under x/P=t^8, including the t^6 multiplier.
                    curved=a*t**(-6)+b*t**(-5)+c*t**(-4)
                    assert curved*t**6==q
                    cases+=1
    counts["quadratic_interpolation_and_change_cases"]=cases

    # Truncated convolution is bounded by the explicit infinite-tail envelope.
    cases=0
    for radius in (8,16,32,64):
        for ell in range(-24,25):
            mass=sum((F(1,(1+abs(r))*(1+abs(ell-r)))
                      for r in range(-radius,radius+1)
                      if abs(ell-r)<=radius),F(0))
            m=abs(ell)
            harmonic=sum((F(1,j) for j in range(1,m+2)),F(0))
            assert mass<=4*harmonic/(1+m)
            cases+=1
    counts["coefficient_convolution_controls"]=cases

    errors={
      "wave_floor_value_error":F(1,2)+F(1,4),
      "zero_offset_floor_exceptions":F(1,24)+F(1,2),
      "bounded_fourier_error":F(5,6),
      "wave_curvature_rounding":F(1,2)-F(5,4),
      "wave_shift_remainder":F(1,2)+F(1,24)-F(7,4),
      "anchor_gap_rounding":F(1,24)+F(1,24)-F(9,8),
      "anchor_shift_remainder":F(1,8)+F(1,24)-F(13,8),
      "anchor_floor_curvature":F(1,24)-F(7,8),
      "shifted_indicator_curvature":F(1,4)+F(1,24)-F(3,2),
      "wave_center_value_remainder":F(1,2)+F(1,24)-F(5,4),
      "wave_center_derivative_remainder":F(1,2)+F(1,24)-F(9,4),
      "D2_largest_curvature":F(5,16)-F(5,4),
      "D2_largest_run_density":F(1,24)-F(1,2),
      "D2_coefficient_window_density":F(1,24)+F(1,8)-F(7,8)
    }
    for key in (
      "wave_curvature_rounding","wave_shift_remainder","anchor_gap_rounding",
      "anchor_shift_remainder","anchor_floor_curvature","shifted_indicator_curvature"):
        assert errors[key]<=F(-3,4)
    assert errors["wave_center_value_remainder"]==F(-17,24)
    assert errors["wave_center_derivative_remainder"]==F(-41,24)
    assert errors["D2_largest_curvature"]<F(-3,4)
    assert errors["D2_largest_run_density"]<F(-3,8)
    assert errors["D2_coefficient_window_density"]<F(-3,8)

    costs={
      "model_length":1-F(3,32),
      "model_boundaries":F(5,8)+F(5,16),
      "model_balanced_transition":F(1,2)+F(5,32),
      "model_curvature_error":1-F(1,16),
      "small_combination":F(15,16)+F(1,32),
      "large_resonant":1-F(1,32),
      "large_length":F(3,4)+F(5,32),
      "large_boundaries":F(5,8)+F(1,4)-F(1,64)
    }
    assert costs["model_length"]==F(29,32)
    assert costs["model_boundaries"]==F(15,16)
    assert costs["model_balanced_transition"]==F(21,32)
    assert costs["small_combination"]==costs["large_resonant"]==F(31,32)
    assert all(v<=F(31,32) for v in costs.values())
    counts["error_and_partition_exponents"]=len(errors)
    counts["model_and_regime_exponents"]=len(costs)

    return {
      "status":"PASS",
      "scope":"Finite exact algebra and exponent controls; no independent proof of analytic cancellation.",
      "counts":counts,
      "error_exponents":{k:str(v) for k,v in errors.items()},
      "cost_exponents":{k:str(v) for k,v in costs.items()},
      "written_family_bound":"O_epsilon(P^(31/32+epsilon)) under (S1) and the stated twist conditions",
      "kernel_status":"UNPROVED",
      "oooee_status":"UNPROVED",
      "independent_mathematical_review":False
    }

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=validate()
    rendered=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(rendered,encoding="utf-8")
    print(rendered,end="")

