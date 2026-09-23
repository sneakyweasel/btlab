# The fourth odd phase is the already closed K3 extension route

The 22 September [predecessor-transfer follow-up](../problems/juggler_predecessor_weight_transfer.md)
corrects its previous next-step recommendation. Locating the first
unsupported phase at three predecessors does not provide a new route to it.
The repaired Paper B estimates do not cover another nesting level.

The fixed-first-gap obstruction now has a uniform written proof:
for P>=256, integer 1<=h<=P/2, and odd P<n<n'<=2P with the same
O(n+2h)-O(n), the second gap G_h(n)=O^2(n+2h)-O^2(n) satisfies
G_h(n')-G_h(n)>h*(n'-n)*P^(1/4)/2-2>=2. Partitioning such a branch
by its second gap leaves at most one source per cell. This is stronger
evidence than the old run scans, but does not assert monotonicity across
different first gaps. A two-layer expansion of the fourth odd phase also
retains a P^(9/16) quadratic second-floor term and the already recorded
P^(45/16) linear coefficient. Neither can be erased as a small error.

Decision: **CLOSE** the direct Paper B extension, not the fourth-phase
cancellation question. No new analytic saving or termination implication.
Member: `J-fixed-first-gap-separation`; connects to
`J-scale-invariant-R-extension` and `J-increment-first-K3` below.

