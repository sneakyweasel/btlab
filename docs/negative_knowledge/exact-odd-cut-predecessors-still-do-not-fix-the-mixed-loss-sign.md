# Exact odd cut predecessors still do not fix the mixed-loss sign

The [cut-predecessor gate](../problems/juggler_cycle_cut_predecessors.md) is
**CLOSE** for its predecessor-only sign obstruction. Nonpositive loss
requires the odd integer ceiling of m^(4/3) in a shrinking O(m^(-1/6))
upper window; cube minima force positive loss. This is a conditional
sign statement, not exclusion of cycles with cube minima.

For every r>=67,r=3 mod16, the recorded polynomial family has actual
guarded paths a->O h->O M->E t and b±->O s±->E m->O q, with the same
m,h,M,t,q and b+=b-+2. It gives Delta-<-3/4 and Delta+>2r-1, while
m^3-M>2m^2 survives all current smooth height strips at their cutoffs.
The negative face realizes the thin noncube predecessor alignment.
Thus neither independent parity faces nor the two exact O predecessors
force a universal mixed-loss sign.

Do not infer full cyclic placement: no adjacency in an actual periodic
set, complete original A/B return seam, or common terminal P/Q closure
is constructed. The missing initial seam is B(t),A(m)=B(q), with all
guards and quantitative cycle constraints. Any further finite rectangle
test must either supply a new coupled restriction or record its surviving
family and stop local-prefix stacking; deleting this one parameterization
would not prove the general obstruction.
Members: cycle_cut_predecessors, J-cycle-cut-predecessor-alignment,
J-cycle-cut-predecessor-two-signs.


