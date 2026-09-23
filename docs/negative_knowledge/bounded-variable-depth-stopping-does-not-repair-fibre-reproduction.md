# Bounded variable-depth stopping does not repair fibre reproduction

The [signed stopping-envelope proof](../problems/collatz_bounded_fibre_stopping.md)
extends the finite periodic weight obstruction to arbitrary branch-specific
stopping decisions under a common finite depth budget. With U_0=h and
U_(d+1)=max(h,L_s U_d), universal forced-step reproduction L_s U_d>=h
would imply L_s U_d>=U_d, which the existing mean/spike argument forbids.
`FibreStopping.lean` proves the deficit for both signs, actual integer
representatives, and every bounded policy; the envelope is attained.

**CLOSE** this bounded-stopping repair. The deficient residue may change
with the budget, so no fixed integer with a summable coefficient series
is produced. The result concerns homogeneous terminal coefficients;
unbounded stopping, nonperiodic terminal weights, fate-specific growth and
actual Juggler pressure remain open. Ledger: C-fibre-bounded-stopping-obstruction.
