# Finite growing power blocks do not form an invariant escape family

Recorded 22 September 2026. In the
[power-family continuation](../problems/juggler_power_family_reentry.md),
an expanding \(O^aE^b\) block starts at \(s^{2^{a-1}}\) and ends at
\(\lfloor s^\beta\rfloor\), \(\beta=3^a/2^{b+1}>2\).
Re-entry into any of the construction's starting families requires a
square endpoint, hence
\(0\le\{s^{\beta/2}\}<s^{-\beta/2}\). These parameters have density zero
on every fixed odd progression. Positive-density phase hits do not
supply a closed domain, and summability of shrinking windows does not
prove deterministic finiteness.

For a guarded square return \(t^2\), the gap
\(R=s^{3^a}-t^{2^{b+2}}\) is positive and
\(R\ll s^{3^a-\beta}\). Zero gap forces an odd first E source, so is
not an actual block. **Assuming abc**, normalizing by the full gcd gives
finitely many such returns for each fixed block type: the radical
exponent is \(3^a+1-\beta/2<3^a\).
Thus **assuming abc**, no infinite concatenation from a finite collection
of these types can keep returning to their perfect-power start forms.
For OOE, an infinite re-entry family would instead give abc triples of
asymptotic quality at least \(72/71\).

The bounded checks found no guarded square exits for OOE, OOOE and
OOOOEE on 25,000 odd parameters apiece. Those checks are not a
finiteness theorem. The direct construction route is **CLOSE**.
Unconditionally, a zero-density invariant subset remains unresolved;
general nonsquare trajectories and unbounded variation of block types
are not excluded. No escape or universal termination theorem.
Member: J-power-family-square-reentry-obstruction.
