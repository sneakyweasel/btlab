# Cycle height forces a run alphabet

## Problem

A nontrivial Juggler cycle has a minimum \(m\) and a maximum \(M\). How much does the
height ratio \(R=\log M/\log m\) constrain the cycle's itinerary? The question is whether
a bound on how far a cycle ranges is enough, on its own, to pin the shape of its parity
word.

## Exact statement

Let \(C\) be a nontrivial cycle with minimum \(m\) and maximum \(M\), and
\(R=\log M/\log m\).

1. **Run bounds.** Every odd run has length \(r\) with \((3/2)^r\le R\); every even run
   has length \(g\) with \(2^g\le R\). Both are the same bookkeeping: an odd run
   multiplies the logarithm by \((3/2)^r\) and an even run divides it by \(2^g\), while
   every cycle value lies in \([m,M]\).
2. **A long odd run is forced.** Closure gives \(o\log(3/2)=e\log 2\), so
   \(o/e=\log 2/\log(3/2)=1.7095\). A cyclic word with no two adjacent odd letters has
   \(o\le e\). Since \(1.7095>1\), some odd run has length at least two, and therefore
   \(M\ge m^{9/4}\).
3. **The band alphabet.** If \(R<27/8\) then odd runs have length at most two and even
   runs exactly one, so the itinerary is a cyclic word over \(\{OE,OOE\}\). Only \(OOE\)
   climbs, with exponent \(9/8\); \(OE\) falls with \(3/4\). Closure pins the mix: the
   \(OOE\) fraction of blocks is \(\log(4/3)/(\log(4/3)+\log(9/8))=0.709511\).

4. **Height is discrepancy.** Write \(s=o/L\) and \(D_t=o_t-ts\). Under closure
   the walk height is exactly \(u_t=(\alpha+\beta)D_t\) with \(\alpha=\log(3/2)\),
   \(\beta=\log 2\), so \(\log R=\log 3\cdot\Delta\) for \(\Delta=\max D-\min D\).
   Balanced (mechanical) words are \(\Delta<1\), i.e. \(R<3\); the band is
   \(\Delta<\log(27/8)/\log 3=1.107\). A run of \(k\) consecutive \(OOE\) blocks
   climbs exactly \(k(2-3s)+s\); a run of \(j\) consecutive \(OE\) spans
   \((1-s)+j(2s-1)\). At the forced slope: \(OOE\)-runs are at most \(3\) if
   mechanical and \(4\) in the band, \(OE\)-runs at most \(2\) for both.
5. **No double even step below the fourth power.** Two consecutive even steps land at
   the fourth root, so \(M\ge m^4\). Below \(N_0^4=1.5\cdot10^{34}\) no cycle contains
   \(EE\).

With the certified floor \(m>N_0=3.5\cdot10^8\), part 2 reads \(M>1.6\cdot10^{19}\) and
the band of part 3 runs up to \(N_0^{27/8}=6.9\cdot10^{28}\).

## Current literature

Nothing external. The Juggler cycle question is this laboratory's, and the run-length and
financing bookkeeping is Paper A's. Not a known-results branch.

## Branch budget

Phase 0 only: the two run bounds, the letter-count argument, and the band alphabet, with
the integer content in Lean. No census, no new corridor, no attempt to kill the alphabet.

## Balanced-ternary formulation

None. The statement is about the exponent walk in \(\log\log\), where the two letters are
additive steps \(+\log(3/2)\) and \(-\log 2\); no ternary digit structure enters.

## Why BT may be relevant

It is not. This branch is recorded here because it is a Juggler cycle constraint, not
because balanced ternary bears on it.

## Candidate operations / invariants

The invariant is the exponent walk in \(\log\log\), read on runs rather than letters: an
odd run is a single \(+r\log(3/2)\) and an even run a single \(-g\log 2\), and the walk is
confined to the band \([\log\log m,\log\log M]\). The bound on each run is the statement
that one step cannot exceed the band width.

## Experiments

`python -m research.juggler_sequence.cycle_run_alphabet` computes the run bounds at the
key ratios, the admissible block set, the two-block mix, the floor-defect size, and checks
the integer chain for two odd steps on concrete odd starts.

It also runs an exact necklace census in the band. For \((a,b)\) copies of
\((OE,OOE)\) near the forced mix \(a/b=0.4094\), every cyclic arrangement is
classified by its discrepancy: balanced (\(\Delta<1\)), sliver
(\(1\le\Delta<1.107\)), or above the band.

| \((a,b)\) | \(L\) | necklaces | balanced | sliver | above |
|---|---|---|---|---|---|
| (2,5) | 19 | 3 | 1 | 1 | 1 |
| (3,7) | 27 | 12 | 1 | 3 | 8 |
| (4,10) | 38 | 73 | 1 | 10 | 62 |
| (5,12) | 46 | 364 | 1 | 15 | 348 |
| (7,17) | 65 | 14421 | 1 | 63 | 14357 |
| (9,22) | 84 | about 650000 | 1 | 255 | the rest |

Exactly one balanced necklace per pair, which is the Christoffel word. Every sliver word
has \(OOE\)-runs of length three or four and \(OE\)-runs of length one; no balanced or
sliver word has five \(OOE\) or three \(OE\) in a row, as the climb formulas predict.

## Conjectures

None opened. The natural continuation, killing every cyclic word over \(\{OE,OOE\}\), is
the already-refuted `J-cyclemin-ooo-inevitable`: the laboratory tried to force a first
\(OOO\) inside exactly this alphabet and found a witness against it.

## Counterexamples

None to the statements above. The relevant negative result is the refutation just named,
which says the band alphabet cannot be emptied by forcing a longer odd run.

## Formalization

`formal/Problems/Juggler/CycleRunAlphabet.lean`, kernel-checked, axioms `propext`,
`Classical.choice`, `Quot.sound` only. `odd_step_sq_le` and `odd_step_le_sq_add` are the
two sides of one odd step; `odd_run_upper` is the odd-run bound
\(y^{2^r}\le v^{3^r}\); `even_run_contracts` is the even-run bound \(z^{2^g}\le w\), read
off the tower-absorption iff; `oo_step_lower` is the integer form of part 2,
\(x^9<2(z+1)^4\), whose slack is `cube_shift_le_two`; `oddCount_le_of_noAdjOdd` is the
combinatorial half of part 2, that a word with no two adjacent odd letters is at most half
odd; `walk_eq_discrepancy` is the identity of part 4, \(u_t=(\alpha+\beta)D_t\) under
closure; and `ee_forces_fourth_power` is part 5.

The closure equation itself is not formalized here. Part 2 therefore combines a Lean
inequality with the human-proof financing of Paper A, and the dossier says so rather than
claiming the whole of it.

## Results

The bookkeeping is exact and the band is narrow. Two things came out of writing it that
were not the target. Below \(R=2\) the admissible block set is empty, because there is no
room for even a single even letter, which recovers the laboratory's existing
superquadratic result as a degenerate case of the same computation. And the mix forced in
the band reproduces the letter ratio exactly, which is a consistency check on both.

The improvement over what was already proved is modest: `cycleMin_to_max_superquadratic`
gives \(M>m^2\) and this gives \(M\ge m^{9/4}\). The band alphabet is the part with no
prior analogue.

The discrepancy identity places the result against Paper A. The band walk of
`band_successor_unique` is the letter-level version of the same bookkeeping, and below
\(R=3\) the two coincide: a band-confined cycle is mechanical. What the run-level
coordinate adds is the sliver between \(R=3\) and \(R=27/8\), where the word is still
over two blocks but is no longer balanced. The census shows the sliver is real and thin,
and the climb formulas say exactly how a word gets there: an \(OOE\)-run of length four,
or an accumulated drift that puts an \(OOE\) start more than \(1-2(1-s)=0.262\) above
the boundary minimum. So a cycle in the band is one of two things, mechanical or a
one-violation two-block word, and nothing else.

**Climbing against certified, corrected.** An earlier version of this dossier reported the
mismatch as the fraction of cycle elements beginning an \(OOE\), \(26.2\%\) against a
fair \(12.5\%\), a ratio of \(2.1\). That number is arithmetically right but measures the
wrong thing: beginning an \(OOE\) is not the same as being uncertified, and most \(OOE\)
starts in the band *are* certified, through \(OOEOE\).

The correct statement is sharper in one direction and much weaker in the other. A band word
has even runs of length one and odd runs of at most two, so \(OOEE\) and \(OOOEE\) can
never occur: **a band cycle can use only three of the five descent certificates**, namely
\(E\), \(OE\) and \(OOEOE\). Reading every depth-5 cyclic prefix that occurs, exactly one
is uncertified, \(OOEOO\), the start of an \(OOE\) immediately followed by another
\(OOE\). So the uncertified count is exactly \(b-R\) with \(R\) the number of
\(OOE\)-runs, verified against every necklace at \((3,7)\) and \((5,12)\).

Since \(OE\)-runs have length at most two, \(R\ge a/2\), and \(OOE\)-runs at most four
gives \(R\ge b/4\). At the forced mix the uncertified fraction therefore lies in
\([0.155,0.196]\), a ratio to the fair \(1/8\) of only \([1.24,1.57]\). The crowding is
mild, not the factor of several the earlier framing suggested.

What does survive is qualitative and was not stated before: at the position where the walk
attains its cyclic minimum no certificate can hold, since a certificate forces a strict drop
within five steps and there is nothing below the minimum to drop to. So **every cycle has at
least one uncertified position**, and in a band cycle it carries the prefix \(OOEOO\).
Checked on every necklace at \((3,7)\) and \((5,12)\) with no exception.

Block-level defect count: tower absorption makes \(OE\) one floor and \(OOE\)
two, so a band cycle has \(a+2b\) effective floors against \(2a+3b\) letters, about
\(1.6\) times fewer, which is marginal since the per-step finance is already exact at
leading order.

## Open questions

Whether a cyclic word over \(\{OE,OOE\}\) with the forced mix can be excluded. That is the
question the refuted `J-cyclemin-ooo-inevitable` failed to settle from the other side, and
nothing here changes its difficulty.

Whether any sliver word closes at cycle scale. The census is exact but small; at the
certified period the necklace count is astronomical and the sliver is a vanishing fraction
of it, yet nothing excludes a sliver cycle. Its word would have \(OOE\)-runs of exactly
three or four and \(OE\)-runs of one.

Whether any result forces \(EE\) into every cycle. None does; if one did, part 5 would
give \(M\ge m^4\) at once.

## Decision

**CLOSE.** The stated theorem is delivered and the branch has no promotion criterion left:
it is not a halt theorem, it does not open an attack, and its natural continuation is a
direction the laboratory has already refuted. The result stands as a shape constraint.

## Publication assessment

Not publishable alone. Part 3 would be a useful paragraph inside Paper A's cycle section,
where the financing and the run bookkeeping already live, and where the exponent
improvement from \(2\) to \(9/4\) belongs next to the existing superquadratic statement.
