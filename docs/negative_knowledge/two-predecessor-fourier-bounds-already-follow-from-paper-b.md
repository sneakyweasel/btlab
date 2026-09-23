# Two-predecessor Fourier bounds already follow from Paper B

[Exact transfer audit](../problems/juggler_predecessor_weight_transfer.md),
22 September 2026. **CLOSE** the proposed new frequency-averaging campaign
at two odd predecessors as redundant. Paper B 4.11 gives the needed
twisted sum after retaining the X and Y parity masks. Exact finite fibre
transport, kernel-checked in `OddPredecessorTransport.lean`, converts its
source rate to O_epsilon(M^(127/288+epsilon)+|h|^24). Prefix subtraction
keeps arbitrary endpoints and the frequency-dependent dyadic tail.
This is an inherited written analytic corollary, not a new proof of
Paper B or a growing-depth result. The next unsupported next-odd-phase
weight is at three predecessors. The earlier shrinking-target warning
remains valid: qualitative equidistribution supplies no such rate.
Members: `J-two-predecessor-paper-b-transfer`, `J-odd-predecessor-exact-transport`.
