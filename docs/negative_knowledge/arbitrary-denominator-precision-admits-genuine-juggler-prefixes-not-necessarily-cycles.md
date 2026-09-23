# Arbitrary denominator precision admits genuine Juggler prefixes, not necessarily cycles

Recorded 22 September 2026. The automatic claim that actual floor equations
plus return modulo the rational cycle denominator force an integer Collatz
code is **REFUTED**. The genuine prefix at 350002553, word OOOEOEOOOEE,
ends at 1330352317, congruent to its start modulo \(2\cdot139\), while its
code is \(3187/139\).

More strongly, for every fixed expanding word \(O^aE^b\), every modulus
\(M\), and every lower bound, infinitely many actual Juggler prefixes
stay above their start and return to its residue modulo \(2M\).
Their code denominator is
\((3^a-2^{a+b})/\gcd(3^a-2^a,2^b-1)\), unbounded at fixed \(b\).
One may take \(M=q^r\) for any fixed precision \(r\).
The proof uses an exact perfect-power family and classical joint
equidistribution of distinct nonintegral powers, not FD or an ambient-to-orbit
transfer. See [denominator coupling](../problems/juggler_cycle_denominator_coupling.md),
J-cycle-denominator-modular-return-obstruction.

The algebra explains the failed inference: the denominator is the order
of the parity vector in a cyclic integer cokernel, whereas the floor
equations put a different vector, containing quadratic and cubic terms,
in its zero class. Discarding those terms is not a transfer.

Scope: these paths grow. The proof supplies no common start at all precisions and
no assertion that the witnesses lie in a cycle's finance window.
The route is **CLOSE**; a denominator restriction for true cycles remains
unresolved. Do not repackage congruence precision alone as exact closure.

