# Juggler: does Paper A's finance, transposed to Collatz, reproduce the published cycle bounds?

Status: **PROMOTE** (a validator, not a new bound). Not a halt theorem, not a
no-cycle theorem, not a new Collatz result, and not a reopen of the Baker
transfer at floors ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)).

## Problem

The bridge dossier ([juggler_collatz_bridge.md](juggler_collatz_bridge.md))
claims that cycle results transfer both ways because the obstruction is the
Diophantine approximation of `|3^o - 2^L|`, with no 2-adics and no
equidistribution involved, and records Collatz as "a free validator" that the
laboratory did not use. This branch uses it: the finance inequality of Paper A
Theorem 4.4 (`cycleMin_finance`), read on the Collatz side, should reproduce
Eliahou's 1993 period bound and lattice, and Hercher's 2018 bound at Barina's
floor. Does it?

## Exact statement

Write `x = log 2 / log 3`. For a shortcut Collatz cycle of length `K` with `p`
odd steps, the exact identity `K log 2 - p log 3 = sum_{odd} log(1 + 1/(3 x_j))`
(Eliahou's inequality (2); Hercher's Theorem 16) gives

```text
Lambda_C(K) := K log 2 - p log 3 = log 3 * frac(K x),   p = floor(K x),
x_min <= p / (3 Lambda_C(K)).
```

For a Juggler cycle, Theorem 4.4 at constant 1 gives

```text
Lambda_J(L) := o log 3 - L log 2 = log 3 * (1 - frac(L x)),   o = ceil(L x),
n log n <= L / (1 - exp(-Lambda_J(L))) = L 3^o / (3^o - 2^L).
```

**Mirror identity (EXACT — HUMAN PROOF, one line).**
`Lambda_J(L) = log 3 - Lambda_C(L)` for every length. Collatz-dangerous lengths
have `frac(L x)` just above `0`, Juggler-dangerous ones just below `1`, and the
convergent denominators of `x` alternate between the two sides (the classical
alternation of convergents). The two admissible sets are disjoint by sign,
which the laboratory already carries internally as
`J-the-cycle-staircase-split-is-a-sign-condition`; here it acquires its Collatz
name.

**Cycle-level dictionary.** The quantity that plays Collatz's `x_min` is
Juggler's `n log n` (per valley: `1/x_i` exact against `1/(n_i log n_i)` as a
majorant), because a Collatz odd step moves `log x` by `log(1 + 1/(3x))` while
a Juggler step moves `log log n` by about `1/(n log n)`. This is a different map
from the walk-level `log x <-> log log n` of the bridge dossier; the two differ
by a factor `n` and must not be substituted for one another.

**Question.** With `x_min <-> n log n`, do the finance survivors on the Collatz
side at the historical floors coincide with the published period bounds?

## Current literature

- Eliahou 1993 — period `p = 301994 A + 17087915 B + 85137581 C`, `B >= 1`,
  `A C = 0`, hence `p >= 17087915`, from the continued fraction of `log_2 3`
  and the verification `n < 2^40` — **KNOWN** (`eliahou-1993-collatz-cycle-lengths`;
  wording from Lagarias's annotated bibliography, entry 53). Project
  relationship: **reproduced**.
- Halbeisen–Hungerbühler 1997 — the next bound `102225496` would need
  verification to `2.1e14` — **KNOWN**
  (`halbeisen-hungerbuehler-1997-collatz-cycles`).
- Two Hercher papers, and the cluster names them by year. **Hercher 2018**
  (`hercher-2018-collatz-cycle-length`: Die Wurzel 6 and 7, with Puchert's
  note in Die Wurzel 11) is the period bound, "more than `7.2e10` odd
  numbers", as quoted in the 2023 paper's introduction — **KNOWN**, project
  relationship **reproduced**. **Hercher 2023** (`hercher-2023-collatz-m-cycles`:
  JIS 26, Article 23.3.5, read from the PDF) is the `m <= 91` theorem, Lemma 8
  (the 2-adic run congruence), Theorem 27 (the `3/4` constant), Corollary 29,
  and the floor `X_0 = 695 * 2^60` of its Definition 4 — **KNOWN**. Barina 2025
  (`217976794617` at `2^71`, from a sharper averaging) — **KNOWN**; no
  `literature/` entry yet, quoted through the Wikipedia Collatz article's
  cycle-length section; project relationship **one fraction short**.
- Simons–de Weger 2005 financing-versus-gap — **KNOWN**
  (`simons-de-weger-2005-collatz-m-cycles`); the laboratory's finance branch
  is its floor-power adaptation ([juggler_cycle_finance.md](juggler_cycle_finance.md)).
- Steiner 1977, no Collatz 1-cycles — **KNOWN** (through Simons–de Weger and
  Hercher). The Juggler counterpart does not exist; see Results.
- Paper A Theorem 4.4 / Corollary 4.11 / Corollary 5.11 —
  **EXACT — LEAN VERIFIED** / **COMPUTATIONALLY VERIFIED**
  ([juggler_finite_dynamics_note.md](../theory/juggler_finite_dynamics_note.md)).

## Branch budget

- **Target:** whether the Collatz reading of Theorem 4.4 reproduces Eliahou
  1993 at `2^40` and Hercher 2018 at `2^68`, and whether the Juggler reading
  reproduces the laboratory's own survivor table.
- **Novelty hypothesis:** none for Collatz. The value is a numerical
  confirmation of the bridge's cycle claim and an exact statement of the
  cycle-level dictionary.
- **Falsifier:** a Collatz survivor list at `2^40` whose minimum is not
  `17087915` or which leaves Eliahou's lattice; a Paper A survivor
  (`paper_a_audit.survivors`) missing from the constant-1 list.
- **Already killed by?:** none. The Diophantine wall kills Baker-type
  transfers as *kills* at floors; this branch kills nothing and competes with
  nothing. `J-the-cycle-staircase-split-is-a-sign-condition` already records
  the sign disjointness internally; this is its Collatz reading, not a reopen.
- **Existing machinery:** `paper_a_audit.o_min`, `theta`, `convergents`,
  `survivors`; `cycle_finance.eliahou_packaging`; `OstrowskiSandwich.lean`'s
  certified convergents.
- **Maximum Phase-0 scope:** one probe (exact three-gap enumeration of the
  one-sided Bohr sets plus a brute-force cross-check), its test, this dossier,
  ledger rows, a journal entry. No Lean, no floor, no GPU.
- **Promotion criterion:** both published Collatz bounds reproduced from the
  transposed inequality, and the Juggler side consistent with Paper A's table.
- **Stop criterion:** any disagreement — then the bridge's cycle claim is
  wrong and the dossier says so.

## Balanced-ternary formulation

None required. The objects are the linear form `o log 3 - L log 2`, its two
one-sided Bohr sets, and the continued fraction of `log 2 / log 3`.

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- `Lambda_C(K) = log 3 * frac(K x)`, `Lambda_J(L) = log 3 * (1 - frac(L x))`,
  `Lambda_J = log 3 - Lambda_C` — **EXACT — HUMAN PROOF**
- `x_min <= p / (3 Lambda_C)` on a Collatz cycle — **KNOWN** (Eliahou (2);
  Hercher Theorem 16)
- Convergent denominators alternate sides; every laboratory cycle length
  (`19, 84, 1054, 25781, 50508, 176251, 478245, 780239, 16785921, 85137581`)
  is Juggler-side, `301994` and `17087915` Collatz-side — **COMPUTATIONALLY
  VERIFIED** by comparing the integers `3^p` and `2^q` below `2e7`, by `frac`
  at 80 digits above
- Eliahou 1993 reproduced at `2^40`; Hercher 2018 reproduced at `695 * 2^60`
  and `2^68`; Barina 2025 is the second survivor at `2^71` —
  **COMPUTATIONALLY VERIFIED**
- The three-gap walk agrees with brute force below `3e7` —
  **COMPUTATIONALLY VERIFIED**
- Juggler survivors at constant 1: `1054` (floor `10^6`) and `50508` (floor
  `3.5e8`) first; Paper A's certified comparison is sharper and leaves `25781`
  and `176251`, every one of its survivors being a constant-1 survivor —
  **COMPUTATIONALLY VERIFIED**
- The 1-cycle length `9809721694` survives Juggler finance at `N_0 = 3.5e8`
  by ten orders of magnitude — **OBSERVATION** (finance only; the walk charge
  of Paper A Section 5 was not applied)
- No cycle of any length, in either problem — not claimed

## Experiments

`python -m research.juggler_sequence.collatz_finance_mirror`, writing
`data/research/juggler/collatz_finance_mirror/summary.json` and
[juggler_collatz_finance_mirror.md](../research/juggler_collatz_finance_mirror.md).
Survivors are enumerated exactly: the set `{K : frac(K x) < eps}` (or its
mirror) is walked from the two one-sided return times of the rotation, and the
finance test is applied to each member at 80 digits. A float-filtered
exhaustive scan cross-checks the walk below `3e7`.

## Conjectures

None.

## Counterexamples

None. The anti-overclaim witness is `9809721694`: a Juggler-side convergent
numerator whose 1-cycle word survives finance at the certified floor with room
to spare, recorded so that nobody reads "the finance layers are at parity" as
"Juggler has Steiner's theorem".

## Formalization

None new here. The Collatz sign theorem `cycle_contracting` and the Juggler
`cycle_itinerary_formally_expanding` sit side by side in
`formal/Problems/Juggler/CollatzBridge.lean` (bridge dossier); the finance
inequalities are `cycleMin_finance` (Juggler) and, on the Collatz side,
classical and not formalised.

## Results

Classification **FINANCE_MIRROR_REPRODUCES_ELIAHOU_HERCHER**.

`J-paper-a-finance-transposed-reproduces-eliahou-and-hercher` —
**COMPUTATIONALLY VERIFIED**.

| floor | smallest Collatz survivor | published |
|---|---|---|
| `2^40` | `17087915` (`10781274` odd) | Eliahou 1993: `17087915` |
| `695 * 2^60` | `114208327604` (`72057431991` odd) | Hercher 2018: "more than `7.2e10` odd" |
| `2^68` | `114208327604` | same |
| `2^71` | `114208327604`, then `217976794617` | Barina 2025: `217976794617` |

At `2^40` all `13869` survivors below `4e8` lie in Eliahou's lattice with
`B >= 1` and `A C = 0`, and every pure multiple of `301994` is excluded — the
bound for `301994 a` is `9.85e11 < 2^40 = 1.10e12` for every `a`, which is
why Eliahou's minimum is `17087915` and not `301994`. Barina's sharper
averaging removes `114208327604` at `2^71`; this inequality does not.

`J-cycle-gaps-are-mirror-images` — **EXACT — HUMAN PROOF** for the identity,
**COMPUTATIONALLY VERIFIED** for the sides: `Lambda_J(L) = log 3 - Lambda_C(L)`;
the two admissible sets are the two one-sided Bohr sets of the rotation by `x`
and are disjoint; Paper D's dangerous fans (`176251 + k * 301994`, closed by
the partial quotient `55`; `16785921 + k * 17087915`, closed by `4`) are the
Juggler-side set between consecutive convergents, and Eliahou's lattice is
the Collatz-side set. Each Juggler fan closes exactly at the next Collatz
bound: `176251 + 56 * 301994 = 17087915`.

**The Juggler side.** Constant-1 finance leaves `1054` and its multiples first
at floor `10^6` and `50508` first at `3.5e8`. Paper A's certified comparison
(Lemma 4.4b: evens charged at `n^2`, climb interiors at `n^(3/2)`) is sharper
and leaves `25781` and `176251`, the printed finance floors of Theorem 4.6
and Corollary 5.11; the walk charge of Section 5 then pushes the laboratory
to `780239`. So the inequality that reproduces the published Collatz bounds
is the *weaker* of the two Juggler forms: the Collatz literature's finance
layer sits at the level of Theorem 4.4, and Paper A's refinements have no
counterpart there.

**Calibration.** `N_0 = 3.5e8` corresponds, under `x_min <-> n log n`, to a
Collatz floor `6.9e9 = 2^32.7`, the verification frontier of the early 1980s.

**What the mirror says about the missing piece.** The two finance layers are
at parity under the dictionary. What Collatz has beyond finance is not a
sharper inequality but the 2-adic run congruence — `k` consecutive odd steps
force `x = -1 mod 2^k`, so `x >= 2^k - 1` (Hercher's Lemma 8) — which bounds
cycle minima below in terms of run lengths and, with Baker, excludes `m`-cycles
for bounded `m` (Steiner 1977 for `m = 1`, Hercher 2023 for `m <= 91`). That is
precisely the missing hypothesis of the closure threshold
`J-cyclemin-closure-threshold`, "a lower bound on the cycle minimum in terms
of the period". Its Juggler twin is a pointwise bound on odd-run lengths,
`run(n) <= C log n`, the odd-tower fragment — an open digit problem, not an
equidistribution problem.

**The walk charge transfers, and it is worth four percent on Hercher's
constant** (`J-collatz-walk-charge-constant`, **EXACT — HUMAN PROOF** for the
inequality, **COMPUTATIONALLY VERIFIED** for the constants; the integer
identities behind it are **EXACT — LEAN VERIFIED**,
`J-collatz-even-step-charge-identity`). Conjugating the odd step by
`z = x + 1` gives, for every start and depth,

```text
2^d (C^d(x) + 1) = 3^o (x + 1) + evenCharge w,      evenCharge w >= 0,
```

(`two_pow_mul_iter_add_one` in `CollatzBridge.lean`), so on a cycle
`(x_0 + 1)(2^K - 3^p) = evenCharge w` exactly (`cycle_even_charge`) and
`x_j + 1 >= 2^(h_j) (x_0 + 1)` with `h_j = a_j alpha - e_j` the walk height,
`alpha = log2(3/2)`. At the cycle minimum `x_j >= x_0` forces
`h_j >= -delta`, `delta = log2(1 + K/(x_0 + 1 - K))`, hence the height before
the `a`-th odd step is at least `frac(a alpha)` unless `frac(a alpha) >= 1 -
delta`. Therefore, effectively and independently of `m`,

```text
sum over odd cycle elements of 1/x  <=  (H(p) + N_delta(p)) / (x_0 + 1 - 2^delta),
H(p) = sum_{a<p} 2^(-frac(a alpha)),   N_delta(p) = #{a < p : frac(a alpha) >= 1 - delta},
```

and `Lambda_C <= (H(p) + N_delta(p)) / (3 (x_0 + 1 - 2^delta))`. This is Paper
A's Theorem 5.4 on the Collatz side: the hug word, whose odd steps sit at
the heights `frac(a alpha)`, is extremal, and the transport deficit of
Theorem 5.3 is zero because the `+1` only pushes up. Hercher 2023, Theorem
27, bounds the same sum by `(3/4) K / X_0` (`K` his odd count, `X_0` his
floor) through Lemma 26's averaging over at most three consecutive runs.

| constant on `sum 1/x <= c p / x_0` | value |
|---|---|
| trivial (Eliahou, Simons–de Weger) | `1` |
| Hercher 2023, Theorem 27 | `3/4 = 0.75` |
| walk charge, `H(p)/p` | `0.7284` at `p = 121` (sup for `p >= 100`), `0.72157` (sup for `p >= 10^4`), `0.72135` in the limit `1/(2 log 2)` |

`H(p)/p = 0.72134755` at Eliahou's `p = 10781274`; by Koksma the deviation
from `1/(2 log 2)` is below `10^-9` at Hercher's `p = 72057431991` (the
partial quotients of `alpha` sum to `150` through `q = 5.4e12`). The
exceptional count is `N_delta(p) <= p delta + 151`, and at Hercher's floor
`delta = 2.06e-10`, so `p delta < 15`. On the non-dropping prefixes of
sampled orbits the height inequality has no violation and the odd-step sum
stays below `H + N_delta`. What it changes: Hercher's Remark 28 threshold
for the next period record, `2836 * 2^60`, becomes `2728 * 2^60`. What it
does not change: the smallest survivor at `2^68` and at `2^71` is still
`114208327604` (margin `1.33` at `2^71`), so the period bound is untouched;
Hercher's Corollary 29 (`1536 * 2^60`, five weeks of computation tracking
residue classes modulo powers of two) and Barina 2025 remain far stronger,
because they use the 2-adic information this bound ignores. Priority checked
against Hercher 2023 only, which averages locally and does not take the
rotation-orbit average; earlier works were not read for it.

**The height-only bound is sharp, so composition with Hercher's averaging
gains nothing** (`J-collatz-walk-charge-is-sharp`, **EXACT — HUMAN PROOF**
for the argument, **COMPUTATIONALLY VERIFIED** for the ratios). The hug word
with `p` odd letters has its odd steps exactly at the heights `frac(a alpha)`,
so its odd-step sum of `2^(-h)` is `H(p)` by construction; Terras's bijection
(`exists_residue_of_word` in `CollatzBridge.lean`) realises it in a residue
class modulo `2^K`, and along a member `x_0` with `300` more bits than `K`
the orbit stays above `x_0` and `x_0 * sum_{odd} 1/x_j / H(p) = 1` to twelve
digits at `p = 12, 53, 300, 665`. Any bound that uses only
`x_j + 1 >= 2^(h_j)(x_0 + 1)` and `x_j >= x_0` -- Hercher's Lemma 26 included
-- is therefore capped at `H(p)`; the `3/4` of Theorem 27 is a weaker
evaluation of the same slack, not a different source of it, and the
rotation-orbit average is its sharp reading. Further gains need information
the heights do not carry: the 2-adic residue tracking of Corollary 29, or the
exact closure `(x_0 + 1)(2^K - 3^p) = evenCharge w`, which requires
`2^K - 3^p` to divide the even-step charge of the word.

## Open questions

What the residue-class tracking of Hercher's Corollary 29 and Barina's
averaging read as on the word side: the divisibility `2^K - 3^p |
evenCharge w` is a condition on the word alone, and the laboratory's
survivor machinery counts words by height, not by residue. Not attempted.

Whether the odd-run bound `run(n) <= C log n` for `n -> floor(n^(3/2))` is
provable; it would give the Juggler 1-cycle theorem through Baker.

## Decision

**PROMOTE.** The bridge's cycle claim now has numbers behind it three times
over: the same inequality reproduces Eliahou 1993 exactly and Hercher 2018
exactly, the Juggler side agrees with Paper A's table, and Paper A's walk
charge transfers as an effective bound that improves Hercher's Theorem 27
constant by four percent without moving the period. Nothing is excluded, and
the branch records what Collatz has that Juggler lacks in the form of a
concrete unexcluded object. The composition question is answered: the
height-only bound is sharp on the hug word, so Hercher's averaging and the
rotation average read the same slack. Best next question: what does the
divisibility `2^K - 3^p | evenCharge w` -- the exact cycle condition as a
word problem -- look like on the survivor words, and is any of it visible
to the transfer operator of `PaperBJumpTransposition`?

## Publication assessment

Status: `STRUCTURAL`. A validation of a transposition, with one exact
bookkeeping identity. It belongs as a paragraph in the bridge section of a
Paper A or Paper B revision, not as a paper.
