# Hercher's Lemma 8 on the exponent

Status: **CLOSE** (the mirror exists, is exact, is already half in Lean,
and is inert for cycles; three corollaries recorded)

Standalone arithmetic phase on the Collatz bridge. Not a Research Engine
experiment, not a cycle exclusion, not a termination theorem, and not a
reopen of the closed 2-adic integer bridge, the refuted p-adic cycle
coupling, or the odd-tower fragment.

## Problem

`J-juggler-is-collatz-one-exponential-up` records that the exponential
conjugacy keeps the word combinatorics and *removes the 2-adic
rigidity*: Collatz's length-\(d\) parity word is a function of
\(x \bmod 2^d\) and the map onto \(\{O,E\}^d\) is a bijection, Terras
1976, while the Juggler's word is a function of \(\{n^{3/2}\}\) and equal
densities are Hypothesis FD. Which part of the rigidity is *not*
removed, where does it live, and what does it buy?

## Exact statement

Write \(e(n)=\max\{e : n=a^e\}\) for \(n\ge 2\), and let
\(\mathrm{exactRun}(n)\) be the number of consecutive states from \(n\)
at which the Juggler floor is not charged, that is at which the state is
a perfect square. Let \(\mathrm{run}(x)\) be the number of consecutive
odd states of the accelerated Collatz map \(x\mapsto (3x+1)/2\).

Claim: \(\mathrm{run}(x)=v_2(x+1)\) and
\(\mathrm{exactRun}(n)=v_2 e(n)\) are the same statement at the two ends
of \(x=2^y\), with the same pointwise consequence by the same
product-formula step, and with the counting function conjugated by the
exponential.

## Current literature

- `hercher-2023-collatz-m-cycles`, Lemma 8: \(k\) consecutive odd steps
  force \(x\equiv -1 \pmod{2^k}\), hence \(x\ge 2^k-1\). **known**;
  quoted, not reproved. It is the pointwise input behind Steiner 1977,
  Simons-de Weger 2005, and the \(m\le 91\) theorem.
- `terras-1976-stopping-time` circle: the parity word is a bijection on
  \(\mathbb Z/2^d\). **known**; recorded in
  [juggler_collatz_bridge.md](juggler_collatz_bridge.md).
- Laboratory: [juggler_saturation_budget.md](juggler_saturation_budget.md)
  proved the Juggler half in Lean already, as `HasPowTwoDepth` with the
  two depth-drop lemmas and `power_bound_eq_implies_pow_two_depth`, and
  called it a local arithmetic question. **extended** here: it is
  Lemma 8, and the extension is the price.
- [juggler_2adic_integer_bridge.md](juggler_2adic_integer_bridge.md)
  **CLOSE**: every 2-adic cylinder splits at the second Juggler letter,
  so weak admissibility is first-letter survival. Not contradicted; that
  branch asked whether a *congruence* on \(n\) forces a letter, this one
  asks where a *valuation* still acts, and the answer is disjoint from
  it because the perfect powers are not a union of cylinders.
- [juggler_odd_tower_fragment.md](juggler_odd_tower_fragment.md)
  **CLOSE**: the pointwise inexact odd-run question. Untouched; this
  branch explains why it cannot be reached from the 2-adic side.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Where does the 2-adic rigidity of 3n+1 go under the
                        exponential conjugacy, and what does the surviving
                        part cost?
Novelty hypothesis      It is not removed but relocated: from the value
                        u = x+1 to the exponent e(n), where it is exactly
                        HasPowTwoDepth; the relocation converts a density
                        2^(-k) into a log-density 2^(-k).
Falsifier               exactRun(n) != v_2(e(n)) at some n, or a depth-k
                        fibre carrying more than the two monochrome words,
                        or a counting row off the predicted root.
Already killed by?      No. The 2-adic integer bridge asked about cylinders
                        and closed on the second-letter split; the p-adic
                        cycle coupling asked about 3^o - 2^L and refuted;
                        the Mahler cluster forbids {(3/2)^n} transfers. None
                        of the three is a valuation on the exponent, and no
                        claim here is a cycle, a density, or a transfer.
Existing machinery      HasPowTwoDepth and the two depth-drop lemmas;
                        power_bound_eq_implies_pow_two_depth;
                        isSquare_pow_three_iff; floor_power; the Collatz
                        bridge dictionary.
Maximum Phase-0 scope   One probe: the two run laws exhaustively to 10^6,
                        the counting laws, the minimal realizers, the fibre
                        word counts, the hand-over digit. No Lean file.
Promotion criterion     A pointwise statement that survives off the
                        perfect-power locus.
Stop criterion          The surviving locus is density zero and monochrome,
                        which is a CLOSE with corollaries.
```

## Balanced-ternary formulation

None required. The objects are the 2-adic valuation of an ordinary
integer exponent and the perfect-power locus of \(\mathbb Z_{>0}\).

## Why BT may be relevant

It is not. The prime here is 2 at one end and the real place at the
other; the ternary side enters only as the unit \(3\in\mathbb Z_2^\times\)
that makes each step cost exactly one unit of valuation.

## Candidate operations / invariants

- \(u=x+1\) conjugates the Collatz odd step to \(u\mapsto 3u/2\), and the
  Juggler exact odd step on \(a^e\) is \(e\mapsto 3e/2\): the same map
  on the same prime — **EXACT — HUMAN PROOF**
- \(\mathrm{exactRun}(n)=v_2 e(n)\), the exact form of the depth-drop
  lemmas, with the converse supplied by `isSquare_pow_three_iff` —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED** to \(10^6\)
- \(\mathrm{run}(x)=v_2(x+1)\) — **KNOWN**, Hercher Lemma 8
- pointwise floors \(x\ge 2^k-1\) and \(n\ge 2^{2^k}\), odd
  \(n\ge 3^{2^k}\), all attained — **EXACT — HUMAN PROOF**; the Juggler
  half is the laboratory's own `power_bound_eq_implies_pow_two_depth`
- counting \(\lfloor N^{2^{-k}}\rfloor-1\) against
  \(\lfloor (N+1)/2^{k}\rfloor\) — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
- an exact run is monochrome, so a depth-\(k\) fibre carries two words
  where Terras carries \(2^k\) — **EXACT — HUMAN PROOF**
- hand-over: for odd \(e\) the image of \(2^e\) has the parity of the
  \(\tfrac{e-1}{2}\)-th binary digit of \(\sqrt 2\) —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
- on a prime power the exponent is a valuation: \(n=p^e\) has
  \(v_p n=e\) and the Juggler sends \(v_p\) to \(3v_p/2\) or
  \(v_p/2\), where Collatz sends \(v_2\) to \(v_2-1\) and the value
  \(u=x+1\) to \(3u/2\) — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED** on five primes to exponent 40

## Experiments

`python -m research.juggler_sequence.exponent_valuation_mirror` writes
`data/research/juggler/exponent_valuation_mirror/summary.json` and
[juggler_exponent_valuation_mirror.md](../research/juggler_exponent_valuation_mirror.md).
Exhaustive to \(N=10^6\) on both run laws, both counting laws, the
monochrome check and the fibre word counts; 201 odd exponents to 401 on
the hand-over digit.

## Conjectures

None. Every statement is proved or quoted.

## Counterexamples

None. The falsifiers did not fire: 999 square states and 19859
non-square states agree with the run law, every counting row is exact,
no mixed exact word occurs, and no hand-over parity disagrees.

## Formalization

No new Lean module. The Juggler half of the mirror is already
kernel-checked in `Problems/Juggler/Equality.lean` as
`hasPowTwoDepth_even_exact`, `hasPowTwoDepth_odd_exact`,
`hasPowTwoDepth_of_cube` and `power_bound_eq_implies_pow_two_depth`;
what this branch adds is the identification and the price, neither of
which is a new theorem to formalize. Writing \(v_2 e(n)\) in Lean would
need a perfect-power-exponent function and would restate the depth
lemmas in another notation.

## Results

- **The relocation.** Collatz carries the 2-adic integer in the value,
  the Juggler in the exponent, and the map is \(u\mapsto 3u/2\) on both
  sides. Each step costs exactly one unit of \(v_2\) because 3 is a
  2-adic unit; the Juggler's even branch \(e\mapsto e/2\) costs the same
  unit, so the valuation drops by one per step whatever the letter.
- **The run laws are one law.** \(\mathrm{run}(x)=v_2(x+1)\) and
  \(\mathrm{exactRun}(n)=v_2 e(n)\), both exhaustively verified.
- **The floor is the exponential of the floor.** \(x\ge 2^k-1\) becomes
  \(n\ge 3^{2^k}\) on odd starts, so the logarithm of the Juggler floor
  is \(2^k\log 3\): the walk-level dictionary, now pointwise. Both are
  attained, at \(2^k-1\) and at \(3^{2^k}\) with word \(O^k\).
- **The price is one logarithm, and it is fatal.** Collatz pays
  \(2^{-k}\) in the density, the Juggler pays \(2^{-k}\) in the exponent
  of the density: \(\lfloor N^{2^{-k}}\rfloor-1\) against
  \(\lfloor (N+1)/2^{k}\rfloor\), exact at every row to \(10^6\). At
  \(N=10^6\) that is 999, 30, 4, 1, 0 against 500000, 250000, 125000,
  62500, 31250.
- **The surviving fibre is empty of information.** An exact run is
  monochrome, the letter being the parity of the base, so the depth-\(k\)
  locus carries the two words \(O^k\) and \(E^k\) where Terras's
  bijection carries all \(2^k\). The exponential does not remove the
  2-adic rigidity; it turns a bijection onto \(2^k\) words into a
  constant map onto two.
- **The fibre, without limits.** On a prime power the exponent *is* a
  valuation, so the statement needs no conjugacy to make: \(n=p^e\) has
  \(v_p n=e\), the Juggler sends \(v_p\) to \(3v_p/2\) on an odd
  prime and to \(v_p/2\) at \(p=2\), and Collatz sends \(v_2 x\) to
  \(v_2 x-1\) and \(u=x+1\) to \(3u/2\). The Juggler does to
  valuations what Collatz does to values.
- **The hand-over is named.** The valuation runs out at the first odd
  exponent and the first inexact image is \(\lfloor m^N\sqrt m\rfloor\);
  on the powers of two that parity is a binary digit of \(\sqrt 2\).
  The 2-adic fibre hands the itinerary to an Archimedean digit of a
  quadratic irrational, with no congruence available at the seam.
- **Why the mirror is inert for cycles.** Hercher's hypothesis is
  \(k\) consecutive odd *letters*, a condition on the word that any
  cycle with a long run supplies for free. The mirror's hypothesis is
  \(k\) consecutive *exact* steps, a condition on the integer that no
  word implies. The exponential moves the hypothesis from the word to
  the arithmetic, which is the mechanism behind the 19 September
  negative-knowledge entry rather than a repair of it.

## Open questions

The pointwise odd-run bound \(\mathrm{run}(n)\le C\log n\) for *inexact*
odd runs — the odd-tower fragment — stays open and stays Archimedean.
This branch adds a reason rather than a route. On a prime power the
exponent *is* a valuation — \(n=p^e\) has \(v_p n=e\), and the Juggler
sends \(v_p\) to \(3v_p/2\) on an odd prime and to \(v_p/2\) at
\(p=2\), where Collatz sends the value \(u=x+1\) to \(3u/2\) and
\(v_2 x\) to \(v_2 x-1\); the Juggler does to valuations what Collatz
does to values. Off the perfect powers there is no exponent at all, and
the conjugacy that produced one does not extend: \(|2^y-2^z|_2 =
2^{-\min(y,z)}\) depends on the Archimedean size of the exponents and not
on \(y-z\) in the 2-adic metric, so \(y\mapsto 2^y\) is not uniformly
continuous for that metric and has no extension to \(\mathbb Z_2\).

## Decision

**CLOSE**. The mirror exists, is exact, and was already half in Lean
under another name; the identification is new and the price is decisive.
Every surviving statement is **KNOWN**, **EXACT — HUMAN PROOF** of a
relocation, or a **COMPUTATIONALLY VERIFIED** count, and the locus it
lives on is density zero and monochrome. No promotion criterion is met
because nothing survives off the perfect powers.

Best next question: none from this branch. The odd-tower fragment keeps
its own placement.

## Publication assessment

Status: `STRUCTURAL`. The relocation and its price are a clean paragraph
for any future exposition of the Collatz bridge, and they belong next to
`J-juggler-is-collatz-one-exponential-up` rather than in a paper of
their own.
