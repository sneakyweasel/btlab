# Juggler: the certificate increment is not a rotation function

`INCREMENT_NOT_A_ROTATION_FUNCTION`

Is r_d = M_d / (2 N_(d-1)) a function of frac(d * beta) alone, as an almost-periodic prefactor would require?

Answer: **no**.

Within one residue class mod 485 the rotation coordinate is fixed to 9.3e-04. Were r_d a function of that coordinate alone, a class would hold one value and its four or five members would scatter. They do not scatter: every class is strictly monotone in d, which scattered values would be about two to eight percent of the time, and in most classes the spread is more than ten times what the residual coordinate motion can explain. So r_d is not a function of frac(d*beta) alone. Separately and more weakly: the fitted slope b does not match the 3*theta/2 that the measured exponent -3/2 predicts. Its VALUE is not determined -- adding a 1/d^2 term moves it several percent while leaving the limit a alone, so it is not a constant to read anything into. That is a tension in the shape, not a refutation of it, and no closed form is claimed. RESOLVED 18 September 2026, and against this method rather than for it: a class fixes the coordinate to delta but psi is a jump function on a dense orbit and varies across the class by about 17 sqrt(delta), which at period 485 is 4.8 percent of psi -- larger than the signal. Across finer convergents the spread of b/(1-a) collapses and its median converges toward the parameter-free 3/2 the shape predicts. So b was never measured here and b/a class-independence was the contamination, not a fact about the increment. See J-paper-b-increment-tension-is-the-class-method.

## Numbers

- `beta = 0.6309297536`, `theta(beta) = 0.96590655`
- period `485`, `frac(period * beta) = 9.304822e-04`
- depths to `3000`, fits on `d >= 1000`, `306` classes
- within-class spread `5.080e-04` to `1.914e-02`
- residual of the `a + b/d` fit `6.97e-07` to `7.98e-03`
- fitted `b` from `1.5049` to `30.6411`, against a predicted `3*theta/2 = 1.4489`
- `b/a` from `40.17` to `898.05`
- **every** one of `306` classes is strictly monotone in `d` (`100.0%`); scattered values would be monotone about 2-8% of the time
- control: the class fixes the coordinate only to `9.30e-04`, which explains at most `6.53e-05` of spread, which `264` classes exceed tenfold

## What this does not say

Exact integer counts; the fits are the only floating point. This refutes one reading of the increment and neither proves nor refutes the meander shape.
