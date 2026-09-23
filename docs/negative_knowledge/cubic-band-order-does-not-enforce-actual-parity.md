# Cubic-band order does not enforce actual parity

**Structural restriction retained; cycle exclusion PARK (9 September 2026).**
A primitive actual cycle with minimum m>1 and maximum M<m^3 has sorted
rank increment e, gcd(L,o)=1, and odd prefix counts ceil(k o/L).
This conditional global-order result is proved in
[cubic-band order](../problems/juggler_cycle_cubic_band.md),
`J-cycle-cubic-band-order`. It does not revive the withdrawn R<27/8
alphabet or the unconditional Christoffel reduction.

**Refuted extension:** exact prescribed-branch integer closure,
coprime counts, mechanical word, extrema parity and formal expansion
are mutually inconsistent, or suffice for full parity compatibility.
At threshold b=9, the exact size-switched
loop 9,27,140,11,36,216,14,52,374,19,82,9 satisfies these listed properties
and has M<m^3, but uses the odd branch at even states 36,14,52.
It is not a Juggler cycle. The size-switched map on [b,b^3), with its
branch cut at b^2, preserves that finite interval without fixed points
for every b>=3 (`J-cycle-threshold-relaxation`), so closed integer
orbits of this relaxed map occur at arbitrarily high minima.
Full parity compatibility is absent in this example. The desired
uniform theorem that every threshold cycle has a wrong-parity state
remains unproved: this example neither proves nor refutes it. This
corrects the earlier logically reversed wording about a "parity
contradiction". The same example's 3/11 mismatch fraction also defeats
an unconditional one-third bound.

Do not infer a no-cycle theorem or parity independence from the finite
threshold survey, and do not treat the four capped large runs as escape.
The parked question is uniform intersection of every threshold cycle
with its wrong-parity set. Even that would leave actual cycles with
M>=m^3 unresolved. Members: `cycle_cubic_band`,
`J-cycle-cubic-band-order`, `J-cycle-threshold-relaxation`.


