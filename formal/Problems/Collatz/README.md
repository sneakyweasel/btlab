# Problems.Collatz

Collatz-only formalization. Generic balanced-ternary operator identities
live under `Operators/` and `Representation/`.

[BackwardMass.lean](BackwardMass.lean) proves that the same infinite
dyadic ray is backward-closed for both shortcut signs and has finite
reciprocal mass. It records the obstruction to transferring Juggler's
general backward-density theorem; the ray is not a fate class.

[PreimageScale.lean](PreimageScale.lean) proves that residue negation
reverses the odd-predecessor height comparison. It records the exact
minus-map scale correction and an actual ancestor excluded by the
parent cutoff, at a target proved nonperiodic. It does not establish
or refute the proposed asymptotic preimage-density exponent.
