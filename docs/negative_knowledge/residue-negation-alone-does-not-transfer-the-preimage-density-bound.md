# Residue negation alone does not transfer the preimage-density bound

The [negative preimage density](../problems/juggler_negative_preimage_density.md)
claim formerly promoted x^0.84 from the equality of two formal residue
programs. Its actual height comparison was missing. The minus odd
predecessor c=(2a+1)/3 is above 2a/3, whereas the plus predecessor is
below it. The normalized minus child scale must be divided by
1+1/(2a). At nonperiodic target 19 and cutoff 103, the uncorrected
child cutoff 4017/38 includes 104 -> 52 -> 26 -> 13, above 103.
`Problems/Collatz/PreimageScale.lean` proves these facts.

**CLOSE** automatic analytic transfer from residue relabelling;
the density claim was returned to `CONJECTURE` in
`J-kl-preimage-density-transposes-to-3n-1`. The subsequent strict-grid
repair now proves that exponent and is **PROMOTE**. The counterexample
still refutes the original pointwise height comparison, not every possible
compensated residue-infimum inequality. Any use of the older elimination
still needs its height and minimization/deletion steps. Matching programs
and a larger k supply neither. The previous wrong-sign identity test
was vacuous; its guard never held on fertile minus classes.

Follow-up: `finite_expanding_shift` now bounds the accumulated height
correction for any finite family of expanding inverse blocks, including
internal prefixes with one fixed extra factor. This does not prove that
the derived residue counting system is valid. `no_elementary_shift`
rules out absorbing both individual inverse letters with one translation
and their unchanged multipliers. For the old exact-shift route the open
premise is the class-infimum system and its minimum/deletion steps, not accumulation of the
offset in an already justified finite expanding family. A subsequent
strict-grid route now proves actual counting recurrences and a decreasing
root/scale measure in `PreimageGrid.lean`, for nonperiodic roots at least
4096. This bypasses deletion inside minima. The bare threshold is not
closed: 4096 has predecessor 2731. `PreimageDomain.lean` now repairs that
boundary using a finite orbit barrier and a nonperiodic fertile ancestor
above it, for every positive target coprime to 3. Its selected ancestor
domain stays above 4096 and transfers counts to the target after a fixed
cutoff. `PreimageGrowth.lean` now proves the induction and an independent
level-12 integer certificate checks all 177147 rows for the exact grid
shifts. Cutoff interpolation gives
`PreimageCertificate12.ancestor_density_21_25`: eventually X^21 is at most
the 25th power of the ordinary positive ancestor count for every positive
target prime to 3. The original floating-point model supplied none of
these missing proof steps. No Juggler termination estimate follows.
