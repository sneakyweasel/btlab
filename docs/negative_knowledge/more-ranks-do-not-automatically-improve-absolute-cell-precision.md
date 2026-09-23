# More ranks do not automatically improve absolute-cell precision

[Rank-curvature Result 16](../problems/juggler_cycle_rank_curvature.md)
closes the tested rank-polynomial determinant and rearrangement-only
inferences. The determinant with columns 1,j,...,j^(r-1),z_j is
the product of factorials times the r-th finite difference. Its lattice
divisibility and its independent error radius acquire the same factor.
It therefore adds no precision to the previous grid test; this is not
a claim about every determinant involving actual source/target cells.

The existing Lean theorem cube_fiber_sqrt_odd already gives the exact
parallel OO edges k^4+4j -> k^6+6k^2j for odd k>=3 and 0<=3j<=k.
All states are odd and every higher rank difference vanishes on a long
enough window. These are arbitrarily long finite collections of single
edges, not consecutive orbit times or a full-grid cycle realization.
Do not repackage this known affine-cell mechanism as a new family result.

The squared matching cost has the wrong global Monge sign across the
cubic branch cut. Putting even-source radicands before odd-source cubes
restores the inequality, whose optimum is exactly the known rank rotation.
The log-log state moment is the existing finance identity. No other
useful moment comparison is established by this audit.

Nor do wrong-parity points next to a periodic edge imply cycle coverage.
For an even periodic upper source x with odd target y in a threshold map,
both x-1 and y^2 are wrong upper states in the same square cell. Periodic
injectivity forces them to be transient. A compatible cycle would have
at least e distinct wrong transients of the first form. This is conditional
and supplies no compatible cycle. The full shared absolute-cell problem
remains open; no new restriction, census, Lean module, or PDF work follows.
Members: cycle_rank_curvature.
