# Juggler square-seam cycle lemma

Phase-0 structural check: isolated odd seam s^2 -> s^3 and
isolated even seam k^2 -> k as junctions on a hypothetical cycle.

Classification **SQUARE_SEAM_REPARAMETERIZATION**.

## Local identities

- 9 -> 27: odd isolated, crumb 0, local word `*OO`.
- 36 -> 6: even isolated, crumb 0, local word `*EE`.
- 100 -> 10: even isolated, then 10 -> 3 (inexact E).
- Isolated roots s,k <= 200: exact `True`,
  all odd `*OO` `True`, all even `*EE` `True`.

## Entrance cells

- Odd-parent uniqueness: `True` (occupied `5` of `93`).
- Even width is 2q+1: `True`.

## CycleMin = odd square

- OO suffix T^2(n) >= (n+1)^2: `True`.
- Last even is the standard cell [n^2, (n+1)^2): `True`.
- Extra beyond d_0 = 0: `False`.

## Finance saving (cycle states > N0)

- Odd save at s0=12763: `5.772e-13`.
- Even save at CycleMin bound: `7.369e-09`.
- 1/L leftover 25781: `3.879e-05`; blocker: `2.091e-06`.
- Leftover mover: `False`.

## Short W+/- closure

- Roots <= 30, |W+/-| <= 3: odd hits `0`, even hits `0`.
- No short cycle through an isolated square: `True`.

