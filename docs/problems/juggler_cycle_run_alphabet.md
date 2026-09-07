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
\(x^9<2(z+1)^4\), whose slack is `cube_shift_le_two`; and `oddCount_le_of_noAdjOdd` is the
combinatorial half of part 2, that a word with no two adjacent odd letters is at most half
odd.

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

## Open questions

Whether a cyclic word over \(\{OE,OOE\}\) with the forced mix can be excluded. That is the
question the refuted `J-cyclemin-ooo-inevitable` failed to settle from the other side, and
nothing here changes its difficulty.

## Decision

**CLOSE.** The stated theorem is delivered and the branch has no promotion criterion left:
it is not a halt theorem, it does not open an attack, and its natural continuation is a
direction the laboratory has already refuted. The result stands as a shape constraint.

## Publication assessment

Not publishable alone. Part 3 would be a useful paragraph inside Paper A's cycle section,
where the financing and the run bookkeeping already live, and where the exponent
improvement from \(2\) to \(9/4\) belongs next to the existing superquadratic statement.
