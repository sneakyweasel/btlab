# Paper B's recursion in its OEIS neighbourhood

Status: **CLOSE** (one new sequence, a closed form for the plateau
lengths, and three names the laboratory already had)

Bookkeeping phase on Paper B's survivor recursion. Not a bound, not a
cycle exclusion, not a floor raise, and not a new theorem in either
Lean or prose.

## Problem

`J-paper-b-survivors-are-oeis-a076227` identifies the survivor count
\(N_d\) with OEIS A076227 and checks it to 3508 terms. That entry's
formula section carries a recurrence in terms of further sequences, and
the laboratory's kernel-checked `neverNegCount_succ_sub_onBarrier` —
\(N_{d+1} + M_{d+1} = 2N_d\) — is exactly that recurrence's shape. Which
sequences are they, in the laboratory's own terms, and is any of them
new here?

## Exact statement

\(M_d\) counts the minimal certificates of length \(d\); the recursion
doubles exactly when \(M_d = 0\), which by
`minimalCertCount_eq_zero_of_window_empty` is exactly when no power of
three lies in \([2^{d-1}, 2^d)\). Those lengths and their complement are

\[
M_d \neq 0 \iff d \in \mathrm{A020914} = \{\lfloor n\log_2 3\rfloor + 1\},
\qquad
M_d = 0 \iff d \in \mathrm{A054414}\setminus\{1\},
\]

with \(\mathrm{A054414}(n) = 1 + \lfloor n/(1 - \log 2/\log 3)\rfloor\),
and the two partition the positive integers. Verified to \(d = 200\)
against both closed forms by an independent dynamic program, which also
reproduces the Lean recursion at every depth.

The exception is \(d = 1\): A054414 contains 1, but the one-letter word
\(E\) contracts at once, so \(M_1 = 1\) and 1 is a stalling length. The
exclusion is stated rather than absorbed.

## What is new, and what is not

| sequence | status |
| --- | --- |
| A076227 | already `J-paper-b-survivors-are-oeis-a076227` |
| A020914 | already used throughout Papers A and B |
| A100982 | already named in `CollatzBridgeLab.lean`, "read by length" |
| **A054414** | **new; absent from the repository before this** |

Reading \(M_d\) along the stalling lengths only, rather than by length
with its zeros, gives A100982 with one extra leading term. That is the
same content re-indexed, not a second identification, and the shift is
recorded because an unstated offset produced this branch's A034887 error
earlier the same day.

So the single mathematical gain is the closed form: the plateau law
previously carried three verified instances, at \(d = 6, 9, 11\), and now
has a description of where all of its plateaus are — the next being
\(14, 17, 19, 22, 25, 28, 30\).

## Current literature

- OEIS A076227, A020914, A054414, A100982, read from a local clone of
  `github.com/oeis/oeisdata`, export stamped 2026-09-20. **known** for
  the first, second and fourth; A054414 **extended** into the repository
  here. OEIS content is CC BY-SA 4.0, copyright the OEIS Foundation;
  nothing from it is vendored, only A-numbers and the arithmetic they
  name.
- Laboratory: `neverNegCount_succ_sub_onBarrier`,
  `minimalCertCount_eq_zero_of_window_empty`, `density_flat_of_window_empty`
  and its three instances, all kernel-checked and unchanged.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     The OEIS entry for Paper B's survivor count carries a
                        recurrence; the laboratory's Lean recursion is its
                        shape. Which sequences index its plateaus, and is any
                        of them new here?
Novelty hypothesis      The plateau lengths have a closed form the laboratory
                        does not use, and it is the Beatty complement of the
                        length it uses everywhere.
Falsifier               The plateau set is not a Beatty sequence, or it is one
                        the repository already names.
Already killed by?      Partly, and checked first: A076227, A020914 and A100982
                        are all already the laboratory's, the last of them in
                        Lean. A054414 returns no hit anywhere in docs/, src/,
                        literature/ or formal/.
Existing machinery      the Lean recursion and window-empty law; a dynamic
                        program on (length, odd count) to reach depth 200.
Maximum Phase-0 scope   reproduce the recursion, compare the two closed forms,
                        state the d = 1 exception, record the names.
Promotion criterion     a plateau statement the Lean layer does not have.
Stop criterion          the closed form is bookkeeping and changes no bound.
```

The stop criterion fired. **CLOSE.**

## Decision

**CLOSE.** The branch answers its target and the answer is bookkeeping.
The mathematics was already kernel-checked; what is added is a closed
form for the location of the plateaus and one sequence name. Three of
the four sequences were the laboratory's already, which is recorded here
rather than quietly omitted — the session that produced this probe made
seven prior-art misses in a day, and the count is part of the result.

No Lean proof changed. The identifications went into docstrings, because
the container that ran this probe has no Lean toolchain — `elan` installs
but the toolchain download is refused by the egress policy — and
unverifiable Lean has no business in a corpus whose claim is that it is
kernel-checked. `lake build` has **not** been run against these edits;
they are comment text only, and the rebuilt index reports the same 6917
kernel and 56 compiler declarations as before.

Best next question: none from this branch.

## Addendum: the Juggler corner of OEIS, swept

The same mirror answers a second question the laboratory had never put:
what else is catalogued about its own map. OEIS carries **30 sequences**
naming the Juggler; the repository cites **five** (A094683, A007320,
A094670, A094679, A094716) and had never mentioned the other 25.

The one that matters is **A094778**, the Juggler's *dropping time* at
\(2n+1\) — the number of steps before the orbit first falls below its
start. That is Paper B's object exactly: the non-contracting-prefix
census counts precisely the words whose dropping time exceeds the word
length. Checked against an independent walker here: **agreement on all
100 defined terms**. The only difference is at \(n = 0\), where
\(2n+1 = 1\) is the Juggler's fixed point and the orbit never drops;
the entry records 0 by convention. Stated because it is an endpoint
convention, not a disagreement.

Four more bear on live frontiers and are uncited: A094819 (steps from
\(10^n\), the verification frontier), A094698 (record step counts),
A094804 (primes along a trajectory — the direction the 20 September
prime fan-out killed is catalogued), and four sequences added in 2025–26
(A380891, A381246, A389383, A396851) that postdate the laboratory's
reading.

There is also a **variant family** the laboratory has never considered:
A095396–A095401, A094685, A094725, A007321, the "modified juggler" maps
using \(\lfloor n^{2/3}\rfloor\) on evens, and `round` in place of
`floor`. In the exponent coordinates of
`J-lemma-eight-is-the-exponent-valuation` that changes the transport from
\(e\mapsto e/2,\,3e/2\) to \(e\mapsto 2e/3,\,3e/2\) — a different
log ratio, hence a free test of whether this laboratory's machinery is
about the Juggler or about the exponent pair. Not attempted here.

### The three "unlisted" sequences, re-examined

An exact-run probe first reported the leftover lengths, their odd counts
and the repunit floor powers as absent from OEIS. That was an artefact of
searching for contiguous runs; two of the three are **selections** from
catalogued families, which no run search can find. Pointwise transforms
were tested and none matches: \(a\pm1\), \(a\pm2\), \(2a\), \(2a\pm1\),
\(a/2\), \(a\pm n\), first differences and partial sums, on all three.

**The odd counts are catalogued.** Every one of the ten values inside
A206788's stored range — 1, 2, 7, 12, 53, 359, 665, 16266, 31867, 111202 —
is a term of **A206788**, *denominators of semiconvergents to*
\(\log_2 3\). The remaining three (190538, 301739, 492276) lie beyond what
that entry stores, which is a storage limit and not a divergence.

**The lengths straddle two families and match neither.** Nine of the
thirteen are terms of **A254351**, *numerators of increasingly better
rational approximations to* \(\log 3/\log 2\): 3, 11, 19, 84, 569, 1054,
50508, 176251, 301994. Four are not: 1, 25781, 478245, 780239. A scan of
the whole database finds **no sequence containing all thirteen**. The
reason is structural: A254351 keeps only record approximations, while the
laboratory's list keeps every semiconvergent the finance bound still
admits, so it sits strictly between the convergents (A005663) and the full
semiconvergent numerators.

**One apparent off-by-one, resolved.** The laboratory pairs length 301994
with odd count 190538, while that convergent's denominator is 190537. The
difference is exactly 1 and it is not an error:
\(190538 = \lceil 301994\log_3 2\rceil\), the laboratory's own pinning
\(o(K)\), which exceeds the convergent denominator by one when the
approximation falls on the other side. Recorded because it reads as a
transcription slip and is not one.

**The repunit floor powers are genuinely absent, in both halves.**
\(\lfloor(2^a-1)^{3/2}\rfloor\) has different closed forms for even and
odd \(a\), so the bisections were searched separately. The even-\(a\) half
is \(8^m - 3\cdot 2^{m-1} = 5, 58, 500, 4072, 32720,\dots\) — verified
against `J-repunit-floor-power-is-closed-form` — and the odd-\(a\) half is
the Beatty form \(\lfloor\sqrt2\,K\rfloor\). Neither half, nor the
interleaving, returns a hit.

### What the entries' own notes say

Reading the comment and link fields, rather than only the terms, turned up
four things.

**The plateau law has a base-three restatement, and it is striking.** A
comment of Mohammed Bouayoun (April 2006) characterises A054414 as the
exponents \(n\) for which \(2^n\) begins with digit **2** in base three.
Verified here on \(1..399\), and against the recursion: Paper B's
survivor count doubles at length \(d\) **exactly when \(2^d\) starts with
a ternary 2**, the one exception being \(d = 1\) as above. That is the
same fact as "no power of three lies in \([2^{d-1}, 2^d)\)" — if the
leading ternary digit is 2 there is no room for a power of three in the
cell — but it is a reading of the plateau law in digits rather than in
inequalities, and the laboratory did not have it.

**The Beatty complementarity is not ours.** A comment of Robert G. Wilson v
(May 2014) on A054414 states that, except for 1, it is the complement of
A020914 and the two form a Beatty pair — the same statement derived
independently here today, exception included. The identification of that
pair with the plateaus of `density_flat_of_window_empty` is the
laboratory's; the complementarity itself was in print eleven years ago,
and A054414 has carried "these numbers appear in connection with the 3x+1
problem" since 2006.

**The odd counts are equal temperaments.** A206788 and A060528 describe
their terms as equal divisions of the octave giving good approximations to
the perfect fifth and fourth — so the laboratory's leftover odd counts 12,
53, 665 are 12-tone equal temperament, the 53-tone Pythagorean temperament
and its successors. The cycle-length obstruction and musical temperament
are the same Diophantine problem about \(\log_2 3\), approached from the
two sides. The chain is \(\mathrm{A005664}\subset\mathrm{A060528}\subset
\mathrm{A206788}\), and the laboratory's counts sit across all three: 16266
is in A206788 alone, which is the same irregularity A060528's own note
records as its "self-accumulating nature" failing at particular terms.

**The even-run cap constant has a name.** `J-even-run-dual-of-lemma-eight-is-capped-by-the-shape`
caps the even-run gcd at \(\lfloor(\log_2 3 - 1)a\rfloor\). A comment on
A020857 records \(\log_2 3 - 1 = 0.5849625\ldots\) as the exponent
governing the count of odd coefficients in \((1+x)^n \bmod 2\), and as the
Hausdorff dimension of the Sierpiński triangle. The cap's slope and the
separation exponent \(2 - \log_2 3 = 0.4150375\) are that constant and its
complement; nothing follows from the coincidence, but the constant should
be called by its name.

**Two adjacent items, neither pursued.** A054414's comment records a
conjecture of N. J. A. Sloane that for every \(n \ge 15\), \(2^n\) has a 0
in its ternary expansion — an open question about ternary digits of powers
of two, which is the laboratory's \(2^L\) against \(3^o\) comparison in
another costume. And A020857 links an expository piece by Eliahou on
non-trivial \(3n+1\) cycles (CNRS, *Images des Mathématiques*, 2011) by the
author of `eliahou-1993-collatz-cycle-lengths`, which the registry does not
carry.


### The two adjacent items, searched

**Sloane's ternary-zero conjecture, resolved as a citation.** A054414's
comment paraphrases it as "for any integer \(n \ge 15\), \(2^n\) always
has a 0 in its ternary expansion". That paraphrase is wrong at its
endpoint: \(2^{15} = 1122221122_3\) has no zero. The canonical entry
**A104320** (number of zeros in the ternary representation of \(2^n\))
states it correctly as \(a(n) > 0\) for \(n > 15\), and **A102483** is the
exception set. Computed here: the only \(n\) for which \(2^n\) has no
ternary zero are \(1, 2, 3, 4, 15\), checked to \(n = 3000\); b-files by
Robert Israel on A104320 and Rémy Sigrist on A117970 carry it to
\(n = 10^4\), so the published check is stronger than ours.

The conjecture is genuinely adjacent — it is a statement about the ternary
digits of powers of two, which is the laboratory's \(2^L\) against
\(3^o\) comparison — and none of A102483, A104320, A117970 or A020915
appeared anywhere in the repository. It is recorded, not opened: an open
problem about digits of \(2^n\) is not a cycle bound, and the laboratory's
own base-three reading of the plateau law is the part that pays.

**The Eliahou 2011 exposition, found but unread.** The article exists —
*Le problème 3n+1 : y a-t-il des cycles non triviaux ? (III)*, Images des
Mathématiques, CNRS, 2011 — and is registered as
`eliahou-2011-cycles-non-triviaux-iii`. Every CNRS host, its page-freeze
mirror and the author's institutional page are refused by this
environment's egress policy, so it was not read.

A figure \(17{,}026{,}679{,}261\) circulates as a lower bound on nontrivial
cycle length and appears independently in several sources, so the number is
real; but the attribution of it to *this* article is **not** established —
one of those sources is T. Ian Martiny's *New Lower Bound on Cycle Length
for the 3n+1 Problem*, whose title suggests the bound may be his. The
number is recorded as circulating and unattributed and is **not** entered
into any laboratory table. The laboratory reproduces Eliahou 1993 exactly
at floor \(2^{40}\) (least period 17087915, on the lattice
\(301994a + 17087915b + 85137581c\)), so whichever floor yields
\(17{,}026{,}679{,}261\) is checkable here once the source is in hand.


### The circulating bound, located — and it is in the other convention

The figure \(17{,}026{,}679{,}261\) is not attributable from here, but it is
**structurally identified**, and the identification carries a correction to
the first version of this section.

\[
17{,}026{,}679{,}261 \;=\; 6{,}586{,}818{,}670 + 10{,}439{,}860{,}591,
\]

the numerator plus denominator of a convergent of \(\log 2/\log 3\). The
first version read that as "the cycle length", and that was wrong, because
**there are two conventions and the laboratory uses the other one.**

In the *shortcut* map every step halves, so a cycle with \(o\) odd steps and
length \(K\) has \(3^o\approx 2^K\), i.e. \(o/K\approx\log 2/\log 3\): the
period is the **denominator** \(q\). Every anchor here is such a \(q\) —
Eliahou 1993's 17087915, the leftovers 19, 84, 1054, 301994, and the floor
table's 103768467013. In the *unaccelerated* map an odd step does not halve,
so a cycle there has length \(o+h = p+q\); that sum is A355512. The two
differ by exactly \(p\), the odd-step count, and they coincide only on the
degenerate head \(\{1,2,3\}\).

So \(17{,}026{,}679{,}261\) is a \(p+q\) and is **not commensurable** with
this laboratory's \(q\) periods without conversion. It is a genuine object
of the convergent machinery and was never a search artefact; which paper
first stated it, and in which convention it was meant, both remain
unsettled.

`convergent_cycle_lengths` in `collatz_finance_mirror` now returns both
readings side by side for each convergent, and a test asserts the two sets
meet only at \(\{1,2,3\}\) — so a period imported from the literature has to
be placed in its convention before it is compared with anything here.


That sequence is catalogued: **A355512**, *sum of numerator and denominator
in the convergents of the approximation of \(\log(2)/\log(3)\)*. The
laboratory's leftover apparatus lives on precisely these quantities — of
its own `LEFTOVERS`, the values 3, 19, 84 and 1054 are convergent
denominators — and A355512 had **zero mentions** in the repository.

### A falling-time paper the registry was missing

Tracing that bound through the Eliahou citations in OEIS turned up
`eliahou-fromentin-simonetto-2021-falling-time`, *Is the Syracuse falling
time bounded by 12?* (hal-03294829, 2021), surfaced from the link fields of
**A368877** (the paper's jump function \(jp\)) and **A368878** (its falling
time \(ft\), the least \(k\) with \(jp^k(n) < n\)), both carrying b-files to
\(n = 10^4\).

Falling time is this laboratory's **dropping time**. Paper B's census counts
the words whose dropping time exceeds the word length, and A094778 is the
Juggler analogue registered the same day. A paper asking whether the falling
time is bounded by 12 asks, in the laboratory's vocabulary, whether the
non-contracting prefix length is bounded — the sharpest form of what the
survivor census measures. It is registered NOT CONSULTED; `hal.science` is
blocked here, and whether its answer is a theorem, a conditional or an open
question is not established. The laboratory already cites this author twice,
in `eliahou-1993-collatz-cycle-lengths` and `eliahou-verger-gaugry-2025`,
without carrying it.


## What this does not say

No bound moves, no cycle is excluded, no floor is raised,
\(N_0 = 3.5\cdot 10^8\) is untouched, and neither map is claimed to halt.
The dynamic program reproduces the laboratory's own kernel-checked
recursion as an arithmetic check, not as a proof of it.
