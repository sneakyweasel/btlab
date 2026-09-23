# Quartic target holes do not force a selected-cell deficit

The [shared-cell continuation](../problems/juggler_cycle_quartic_band.md),
Results 8--11, is **PROMOTE**. Unlike arbitrary local guards, common
cyclic injectivity does strengthen the order theorem: inversions are
exactly earlier-F/later-G pairs in the same auxiliary OE cell. At most
one actual G uses each cell, so I<=c and gcd(L,o)<=c+1. The permitted
shuffle consists of disjoint cell-prefix rotations, whose active cuts
must connect the underlying rotation residue classes.

The local hole-to-deficit shortcut remains **CLOSE**. For a cell with
G valley v, selected F targets are odd values in (O(v),O(v+1)] and
have no odd O predecessor. Their actual predecessors are even, so
that exclusion agrees with the F guards. For v>=64, the number of
free odd target slots exceeds the number of all free odd source
candidates in the cell. This compares available parity slots, not
proved guarded F support, and yields no selected-state deficit.
Do not infer that every F must invert, that a generic missing
preimage removes an actual selected F, or that I must be zero.

The genuine open inversion family remains compatible with the
same-cell theorem. The new permutation and height restrictions
exclude neither the entire taller slab nor all d=1 possibilities.
A useful further deficit must constrain the number of actual F
sources failing to precede a G in their own cell, while retaining
the common cyclic equations. No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-return-order.


