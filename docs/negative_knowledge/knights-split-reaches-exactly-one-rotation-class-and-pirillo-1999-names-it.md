# Knight's split reaches exactly one rotation class, and Pirillo 1999 names it

Killed claim (20 September 2026): "some other named extremal word of this
laboratory -- the hug word, the bunched word, a CycleMin shape word -- is
reverse-closed and so falls to Knight's contradiction directly".

Kind: `KNOWN`. Knight's split consumes a word `w = 1u0` of length `k` with `x`
ones whose endpoint swap `0u1` is a rotation of `w`. That hypothesis forces
`gcd(k, x) = 1`, and for each coprime `(k, x)` there is EXACTLY ONE such word:
the upper Christoffel word of slope `x/k`, with the splitting representative
unique inside its class as well. That is Pirillo's theorem (1999). So the
mechanism reaches one rotation class per aperiodic `(k, x)` -- the high cycle --
on either sign of `2^k - 3^x`, and no non-Christoffel class whatever.

Reverse-closure is necessary and wildly insufficient. The reverse-closed classes
are the symmetric words (products of two palindromes, the achiral necklaces),
counted by `C((k-1)/2, floor(x/2))` for odd `k` and `C(k/2 - 1, (x-1)/2)` for
even `k`; at `(19, 12)` that is 84 classes against 2652 in total, of which
Knight's split reaches 1. Cohn permits the other 83; Pirillo forbids them.

AND AT THE LABORATORY'S OWN SIGNATURE LENGTH THE TWO CLASSES ARE DISJOINT. Verified
here at `(k,x) = (11,7)`, gap `2^11 - 3^7 = -139`, over all 330 words and 30 rotation
classes: 10 classes are reverse-closed, exactly ONE admits the Knight split (the
Christoffel class, canonical `01011011011`, whose `f`-values all carry denominator 139
-- precisely what Knight proves), and exactly ONE carries an integer `f` (canonical
`00011110111`, `f = -136`). They are NOT the same class. The integer class is the
`-17` cycle: its orbit `-17, -25, -37, -55, -82, -41, -61, -91, -136, -68, -34` has
parity word `11110111000`, whose reversal is not among its eleven rotations -- so it is
not reverse-closed, and Knight's mechanism cannot touch it even in principle.

That is the cleanest statement of the method's reach. Knight's contradiction is aimed
by construction at the HIGH cycle, the word-extremal class; the class that actually
realizes an integer sits elsewhere. At `k = 11` -- the length this laboratory carries in
Lean as `neg_seventeen_inhabits_cycleMinShape`, and the third convergent length of the
cycle problem -- the method kills the extremal class correctly and misses the only real
object at that length by construction, not by weakness. It is a further instance of the
cluster's own diagnosis: word-extremal data does not reach realizations.

This closes the follow-up left open by `J-multiplicative-knight-residual-is-the-state-dependence`
and by the REFUTED concentration half of `J-christoffel-one-parameter`. Do not
reopen as: a Knight-style cancellation on the hug word, on a bunched word, on a
CycleMin shape word, or on any reverse-closed non-Christoffel class.
