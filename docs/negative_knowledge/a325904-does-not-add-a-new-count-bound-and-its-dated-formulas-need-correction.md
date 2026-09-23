# A325904 does not add a new count bound, and its dated formulas need correction

The [bounded generator audit](../problems/juggler_oeis_generator_check.md) is
**CLOSE** as a new counting/asymptotic method. Its useful result is an exact
independent check, with two source discrepancies recorded permanently.
`J-oeis-generator-published-transform-fails` refutes the A100982 summation
limit printed in the 20 September 2026 export: at n=2 the sum is empty
but the OOEE certificate count is one. `J-oeis-generator-repaired-finite-comparison`
checks the repaired upper limit through order 256 and recovers survivor
counts through depth 406; it does not prove an all-orders identity.

The A325904 stored terms first disagree with its exact recurrence at index
21, by one, and also disagree at indices 22..26. Feeding them into the
repaired transform first corrupts the certificate count at order 37.
Use exact integer binomials and independently check the transform's offsets.
Do not treat either the printed formula or stored coefficient list as an
unquestioned oracle, and do not replace the paper's working path DP on this
evidence. No stronger density estimate or phase-profile result follows.

