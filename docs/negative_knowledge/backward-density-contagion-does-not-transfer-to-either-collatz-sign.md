# Backward-density contagion does not transfer to either Collatz sign

The existing comparison is now formalized in
`Problems/Collatz/BackwardMass.lean`: the infinite ray {3*2^k} is
backward-closed for both shortcut signs, with reciprocal sum 2/3
and that same bound on every finite subset. Every multiple of
three has only its double as a predecessor. The ray is not
forward-closed, so it is not a counterexample to a claim restricted
to fate classes. General backward-density transfer stays **CLOSE**;
no fate-specific almost-all-to-all implication is refuted here.

The [bridge comparison](../problems/juggler_collatz_bridge.md) previously
overstated the Juggler even-block mass as exactly 1/m and never below
it. At m=3 the mass is 107/420<1/3. The existing kernel-checked
lower bound is m/(m+1)^2; the current Paper C manuscript already
uses the correct bound. The former regression only sampled even
targets and could not detect this error. Both target parities are
now included. Collatz's finite normalized mean is also not exactly
one: the optional odd predecessor contributes 3m/(2m-1), approaching
3/2. No termination threshold changes.

