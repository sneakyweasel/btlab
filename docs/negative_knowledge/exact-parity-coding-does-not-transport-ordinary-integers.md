# Exact parity coding does not transport ordinary integers

Recorded 22 September 2026. The Juggler does admit an exact semiconjugacy
into the 2-adic \(3n-1\) map: if \(d_j\) are its odd times, then
\(H(n)=\sum_j2^{d_j}/3^{j+1}\) satisfies \(H(J(n))=C_-(H(n))\).
This is Bernstein--Lagarias parity coding, a **REPARAMETERIZATION** available
for any binary-labelled deterministic system. It is not an integer conjugacy:
\(H(3)=83/27\), and it is not injective, since \(H(4)=H(6)=4\).
The periodic code is \(A(w)/(3^o-2^K)\); ordinary integrality still requires
the word divisibility. FD becomes equidistribution of the codes in
\(\mathbb Z_2\), which is equivalent to the original hypothesis and proves
nothing further. Do not reopen the existence of this coding as a cycle
exclusion or a proof of FD. A new constraint from actual floor realizations
would be needed. Derivation and exact checks:
[Collatz bridge review](../problems/juggler_collatz_bridge.md#review-of-22-september-2026-an-exact-orbit-map-into-the-2-adics).

The full code is now formalized in `CollatzPadic.lean`, without a
termination hypothesis: `orbit_bridge` gives both signed step identities,
actual parity, finite residue/itinerary equivalence, and agreement with
`CollatzRational.terminatingCode` on terminating starts. The exact finite
set identity `code_cylinder_eq` transfers the counting problem without
estimating it. `code_three_not_integer` and `code_not_injective` retain
the two obstructions for the unconditional map itself. This supplies
the 2-adic construction, not integer transport or a new termination input.

The subsequent `periodic_bridge` theorem removes a possible period-loss
ambiguity: on an actual periodic Juggler orbit the code preserves every
return time and the least period, for both signs. Equal-code fibers
are ordered under iteration, so a periodic return inside one fiber is
fixed. The theorem also proves H=A/(3^o-2^L) and the exact equivalence
between ordinary integrality and the word divisibility. If integrality
is supplied, the corresponding ordinary signed Collatz cycle has the
same return times. The divisibility remains unproved for Juggler cycles;
neither global code injectivity nor periodicity of a start from periodicity
of its code follows. No new cycle is excluded.

