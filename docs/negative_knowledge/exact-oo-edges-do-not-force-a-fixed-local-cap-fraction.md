# Exact OO edges do not force a fixed local cap fraction

[Rank-curvature Result 17](../problems/juggler_cycle_rank_curvature.md)
closes a positive universal local compensation fraction, even for genuine
OOE first returns with zero initial OO loss. For every c>0 and height H,
there are square starts x=t^2>H with actual guarded chain
t^2 -> t^3 -> floor(t^(9/2)) -> floor(t^(9/4)), parities O,O,E,O,
and x<z<u<x^2<=v<x^3. The first loss is zero; each later log-log loss
is positive and less than c times its own target cap. The total loss is
therefore less than c times the sum of all three caps.

The construction uses joint equidistribution of two smooth powers along
odd t and an exact nested-square-root identity. Epsilon is fixed before
t tends to infinity; no shrinking-target rate is established. The
explicit genuine OE family b^4+2 -> b^6+3b^2 -> b^3, for odd b>=3,
also has both cap-normalized losses tending to zero.

These are individual finite blocks at arbitrarily large heights, not a
cycle, a concatenation theorem, or an escaping orbit. This result does
not refute the smaller height-dependent integer charges or a bound that
requires simultaneous selection by a complete cycle. Positivity at the
parity changes cannot alone be promoted to a fixed fraction of the caps.

ReturnCells formally verifies the square-start fourth-power cell and
its guarded actual-chain adapter. Equidistribution, infinitude, and the
analytic loss bounds remain a written AI-assisted proof with independent
human review outstanding. Two fixed integer controls, found by bounded
parameter searches and replayed exactly, illustrate rather than prove
infinitude. No orbit census or certified-floor increase follows.
Members: cycle_rank_curvature.

