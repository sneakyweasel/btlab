# Local quartic returns need not preserve merged order

The [quartic-band order theorem](../problems/juggler_cycle_quartic_band.md)
is **PROMOTE** for its actual-cycle restrictions. Only the local
merged-monotonicity shortcut is **CLOSE**.

For every odd t>=3, at free anchor \(m_0=t^5\), the actual guarded
first returns \(F=OOE\) from \(x=t^8+8\) and \(G=OEO\) from
\(x'=t^8+10\) to the same interval
\([\lceil m_0^{4/3}\rceil,m_0^2)\) have outputs
\(t^9+9t-1>t^9\), reversing source order. All intermediate states
lie in \([m_0,m_0^4)\), with the exact floor cells and guards.
These are open paths; the anchor is not an asserted cycle minimum.
Do not infer a common cyclic matching or an unbounded orbit.

An actual cycle with m>=16 and M<m^4 instead admits an oriented
rank shuffle of displacement at most \(D=\lceil\ell^{1/4}\rceil\),
\(\ell=\lceil\lceil m^{4/3}\rceil^{4/3}\rceil\). Its inversion count
I satisfies \(d-1\le I\le\min(c,r-c)D\) and
\(I\equiv d-1\pmod2\), where d=gcd(L,o), r=o-e, and c counts high
odd states. This gives new structural and height/count restrictions,
but does not force I=0; when d=1 it only forces I even. Do not
extrapolate exact cubic rotation, a period-independent numerical
displacement, or error D after arbitrarily many iterations.

The short quartic return alphabet here is proved using an exact
lower floor margin. It does not restore the withdrawn derivation
of a factor-free alphabet from an upper power envelope.
Further restrictions would have to use shared cyclic integer cells.
No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-return-order.


