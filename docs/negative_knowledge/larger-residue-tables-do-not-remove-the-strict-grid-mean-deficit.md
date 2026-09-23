# Larger residue tables do not remove the strict-grid mean deficit

The [signed-density follow-up](../problems/juggler_negative_preimage_density.md)
proves a necessary inequality for every finite table of positive weights
in the current 1/50 grid, for both 3n+1 and 3n-1:
1 <= mu^(-100)+(mu^29+mu^(-21))/3. The affine index maps are permutations,
and the sum of three-lift minima is at most one third of the full weight
sum. At mu^50=2 the inequality contradicts 2^79<3^50. Among rates with
mu^50<=2, every feasible positive table must have mu<5069/5000; the exact
bound mu^5000<2^99 is kernel-checked in `PreimageBalance.lean` at every level.

**CLOSE** reaching the harmonic exponent merely by increasing the residue
level with these unchanged grid shifts. This is not an upper bound on
actual preimage density, not an obstruction for every grid, and not a
proof that a fate class has finite harmonic mass. A direct harmonic lower
bound could be weaker than linear counting. The signed 21/25 theorem is
unchanged. Fate-specific harmonic growth and Juggler's arithmetic pressure
estimate remain open. Ledger: J-signed-grid-mean-ceiling.
