# Actual signed coefficients admit no depth-independent local Harnack comparison

The [transported-peak theorem](../problems/collatz_fibre_local_bounds.md),
23 September 2026, puts unbounded actual K and C coefficients in every fixed
unit cylinder modulo a power of three, for both signs. A fixed exponent branch
transports the one-halving spike, retaining a constant times (3/2)^d. Lean
checks all unit cylinders, arbitrarily large depths and positive odd heights.
Unlike the artificial mixing counterexample, this uses the actual recurrence.

**CLOSE** a depth-independent comparison between all values in a fixed unit
neighborhood: its average is bounded, so such a comparison would bound every
peak. The local-average and Harnack deductions are written corollaries of the
checked peak and existing mean identities. Targets vary with depth; this does
not refute fixed-integer series divergence or a lower bound by itself.
Ledger: C-fibre-local-unboundedness.

The subsequent [fixed-root run bound](../problems/collatz_fibre_run_tail.md)
shows that all words with one free exponent followed by d one-halving
steps contribute at most 3a/2^(d+1) at a fixed positive root a, for both
signs except the negative fixed point one. Their total is at most 3a.
Thus the transported peaks cannot themselves witness fixed-root divergence.
This is a summable-family reduction, not a bound for general exponent words.
