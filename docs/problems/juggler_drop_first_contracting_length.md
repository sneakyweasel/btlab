# Juggler `drop_first_contracting_length`

Status: **PARK**. One exact theorem (a necessary condition for a drop before the
first contracting length, and the excursion length it forces), the computation
to \(10^7\), and a precise statement of why the equality itself is out of reach
of loss accounting. Not a halt theorem.

## Problem

Does the Juggler map ever drop below its start *before* the first contracting
length of its own parity word? The parity word of the orbit of \(m\) is
\(w=w_0w_1\cdots\), and \(\tau(w)\) is the least \(t\) with
\(3^{o_t}<2^t\), \(o_t\) the number of odd letters among the first \(t\).
`power_bound_contracts` gives \(J^{\tau}(m)<m\), so the dropping time is at
most \(\tau\). The question is whether the floors can make it smaller.

## Exact statement

For \(m\ge2\) with orbit \(x_0=m\), \(x_{i+1}=J(x_i)\), prefix ratios
\(\rho_i=3^{o_i}/2^i\), and \(k\) the least index with \(x_k<m\): is
\(\rho_k<1\), equivalently \(k=\tau(w)\)? An **uncertified drop** is a
\(k\) with \(x_k<m\) and \(\rho_k>1\).

## Current literature

- `terras-1976-stopping-time` (**known**): the Collatz mirror. The coefficient
  stopping time \(\tau(x)\) is defined by the same inequality and is at most the
  dropping time, the \(+1\) delaying the drop; equality for \(x\ge2\) is his
  Conjecture 2.9, open, recorded at OEIS A126241.
- Paper B, Proposition 2.1 (**reproduced**): \(J^d(n)^{2^d}\le n^{3^{o}}\)
  along any realised word, so a contracting prefix certifies the drop. In Lean as
  `power_bound_word` and `power_bound_contracts`
  ([Envelope.lean](../../formal/Problems/Juggler/Envelope.lean)), kernel. The
  paper says in so many words that flooring can cause descent the envelope does
  not certify; it does not claim equality.
- `rhin-1987-pade-irrationality` (**known**): \(|O\ln3-p\ln2|\ge H^{-13.3}\),
  used only for the tail of the excursion bound.
- OEIS A094778 (dropping time of \(2n+1\)), A020914 (the possible values),
  A260590 (the Collatz counterpart): none states the question. The comments
  drafted on 21 September 2026 state the bound and the computation, not the
  equality.

## Branch budget

- **Target:** prove that the dropping time equals the first contracting length
  for every \(m\ge2\), or say exactly what stops the proof.
- **Novelty hypothesis:** an exact accounting of the floor losses might give a
  margin that no realised word can exhaust.
- **Falsifier:** an uncertified drop below \(10^6\), or a realised word whose
  accumulated losses exceed the criterion's right-hand side.
- **Already killed by?:** none. The Collatz side of the bridge dossier has the
  mirror statements in Lean (`le_iter_of_prefixNoncontracting`,
  `iter_lt_of_exponentGap`); nothing in the repository addresses the Juggler
  drop step.
- **Existing machinery:** `power_bound_contracts`; `collatz_bridge.juggler`;
  the convergents of \(\log_2 3\); the sweep of 21 September 2026.
- **Maximum Phase-0 scope:** the loss identity by hand, one probe (the sweep
  with the accounting, the convergents, the \(O_{\min}\) table), its test, this
  dossier, a ledger row, a journal entry. No Lean for the identity, no GPU.
- **Promotion criterion:** a proof for all \(m\), or a criterion that a finite
  computation closes.
- **Stop criterion:** the criterion's right-hand side cannot be bounded below
  without bounding the excursion length. That is what happened.

## Balanced-ternary formulation

Not used. The objects are the binary parity word and the integers
\(3^o-2^k\); nothing here reads a balanced-ternary digit.

## Why BT may be relevant

It is not, for this branch. The obstruction is Diophantine, in the convergents
of \(\log_2 3\).

## Candidate operations / invariants

- The floor-free chain \(\xi_i=m^{\rho_i}\) and the deficit
  \(d_i=\ln\xi_i-\ln x_i\ge0\). **EXACT — HUMAN PROOF**: with
  \(p_i=\rho_{i+1}/\rho_i\in\{3/2,1/2\}\),
  \(d_{i+1}=p_i d_i+\eta_i\) and \(0\le\eta_i<\ln(1+1/x_{i+1})\), because
  \(x_{i+1}\le x_i^{p_i}<x_{i+1}+1\). Unrolled:
  \(d_k\le\rho_k\sum_{j\le k}\ln(1+1/x_j)/\rho_j\).
- **Drop criterion, EXACT — HUMAN PROOF.** If \(\rho_k>1\), no drop occurred
  before \(k\), and \(x_k\le m-1\), then
  \(\sum_{j=1}^{k-1}1/(\rho_j x_j)\ge(1-1/\rho_k)\ln m\). Proof: the
  \(j=k\) term is \(\ln(x_k+1)-\ln x_k\); move it left, use
  \(\ln(x_k+1)\le\ln m\), divide by \(\rho_k\).
- **Excursion bound, EXACT — HUMAN PROOF.** \(x_j\ge m\) for \(j<k\), and
  \(\sum_{j<k}1/\rho_j<2O\): the indices with a given odd count \(o\) form a
  run whose reciprocals \(2^j/3^o\) sum below \(2/\rho\) at its last index,
  where \(\rho>1\); the run of \(o=O\) has \(\rho>2\rho_k>2\). So
  \(S_{k-1}<2O/m\). Also \(k\le\lfloor O\log_23\rfloor\) gives
  \(\rho_k\ge2^{f_O}\), \(f_O=\{O\log_23\}\ge\delta(O):=\min_{o\le O}\|o\log_23\|\).
  An uncertified drop with \(O\) odd letters therefore needs
  \(2O/m>(1-2^{-\delta(O)})\ln m\).
- **Refined excursion bound, EXACT — HUMAN PROOF.** If moreover
  \(2O/m\le\ln2\), so that \(S\le\ln2\) by the crude bound, then
  \(\ln x_j=\rho_j\ln m-d_j\ge\rho_j(\ln m-S)\) gives
  \(x_j\ge(m/2)^{\rho_j}\), hence \(1/(\rho_jx_j)\le(2/m)^{\rho_j}/\rho_j\).
  Within the run of an odd count \(o\) these terms grow by a factor at least
  \(m/2\) per step back from the run's last index, where \(\rho\ge2^{f_o}\);
  the run of \(o=O\) has \(\rho>2\). So
  \(S_{k-1}\le(1+2/m)\bigl(\sum_{o<O}(2/m)^{2^{f_o}}+2/m^2\bigr)\), and an
  uncertified drop needs this to exceed \((1-2^{-f_O})\ln m\). Both sides are
  monotone in \(m\) the right way, so a failure at \(m=M\) is a failure for
  every \(m\ge M\); the \(f_o=\{o\log_23\}\) are exact (integer arithmetic on
  a 50-digit \(\log_23\)), so the admissible \(O\) at each \(M\) are a
  finite computation. Least admissible: 16266 at \(10^6\), 31867 at
  \(10^7\), 111202 at \(10^8\), none below 300000 at \(10^{10}\); the
  admissible \(O\) sit at the dangerous denominators plus multiples of 665
  (963 of the first 300000 at \(10^6\), 68 at \(10^7\), 5 at \(10^8\)).

## Experiments

`python -m research.juggler_sequence.drop_first_contracting_length` writes
[juggler_drop_first_contracting_length.md](../research/juggler_drop_first_contracting_length.md)
and `data/research/juggler/drop_first_contracting_length/summary.json`: every odd
start below \(10^6\) run to its drop in exact integers with the loss accounting
(a first pass caps at 400000 digits and a second pass runs the five capped
starts without a cap), the convergents of \(\log_2 3\) to \(10^{13}\), the
table \(O_{\min}(m)\), and the refined scan to \(O=300000\). Chunk mode,
`--start A --limit B`, sweeps \([A,B)\) alone and writes `sweep_A_B.json`;
`--backend gmp` does the dropping-time check on GMP integers through gmpy2,
without the loss accounting, for ranges whose excursions stall pure Python.
The five chunks to \(10^7\) and their merge, `sweep_merged.json`, sit beside
`summary.json`.

## Conjectures

None filed. The equality is a computational observation with a proved margin,
not a conjecture of this laboratory; it is the Juggler mirror of Terras's
Conjecture 2.9 and is recorded as such.

## Counterexamples

None. No uncertified drop below \(10^7\).

## Formalization

`power_bound_contracts` and `power_bound_word` (Envelope.lean, kernel) carry the
proved direction. The deficit identity and the drop criterion are not
formalised: they live in real logarithms, and their integer form
\(\prod_j(1+1/x_j)^{\rho_k/\rho_j}\) has rational exponents. A formalisable
integer statement is open: see the best next question.

## Results

- **EXACT — HUMAN PROOF**: the loss identity, the drop criterion and the
  excursion bound above. Consequences, with the convergents of \(\log_2 3\)
  (dangerous side \(3^q>2^p\): \(q=12,53,665,31867,111202,10590737,\ldots\)):

  | \(m\) | crude: \(O\ge\) | refined: \(O\ge\) |
  |---|---|---|
  | \(10^4\) | 97 | — |
  | \(10^6\) | 665 | 16266 |
  | \(10^7\) | 665 | 31867 |
  | \(10^8\) | 16758 | 111202 |
  | \(10^{10}\) | 190537 | above 300000 (scan limit) |
  | \(10^{12}\) | 891205 | above 300000 (scan limit) |
  | \(10^{16}\) | 310088705 | — |
  | \(10^{20}\) | 23309355709 | — |

  \(O_{\min}(m)\) is nondecreasing, and Rhin's bound makes it unbounded.
- **COMPUTATIONALLY VERIFIED**: for every odd \(m<10^6\) the drop is at
  \(\tau(w)\), so every A094778 term in range lies in A020914. Five starts pass
  400000 digits and were run without a cap: 48443 (972462 digits, drop at 149),
  113097 (518467, 183), 275485 (1909409, 213), 412027 (719279, 153), 463157
  (734154, 81). Extended the same day in five chunks to every odd
  \(m<10^7\): 4999999 starts, no uncertified drop, no numerical failure of
  the identity where it was measured, which is every range but
  \([7\cdot10^6,9\cdot10^6)\); that range ran on GMP integers through gmpy2,
  an independent implementation of the same check, after the pure-Python
  pass stalled on 7110201, whose excursion peaks near \(9\cdot10^7\) digits.
  In all, 42 starts past the cap and run without it, the largest
  excursion 89981517 digits at \(m=7110201\), the longest dropping time
  303 at \(m=5947165\); 1426.5 s of CPU
  (`data/research/juggler/drop_first_contracting_length/sweep_*.json`, merged in
  `sweep_merged.json`). Along all excursions the identity \(d_i\le\rho_iS_i\) never
  failed numerically; the floors keep at least 73% of the ideal margin
  (\(m=9\), word OOE) and at least 90% for \(m\ge11\); the loss-accounting
  bound uses at most 41% of the slack (\(m=5\) and \(m=3\)), 11% at \(m=9\),
  and at most 1.8% for \(m\ge11\) (\(m=4229\), at the near miss \(o=53\)).
- **Combined**: every orbit whose excursion has fewer than 31867 odd letters
  drops exactly at its first contracting length (computation below \(10^7\),
  the refined bound above it; 16266 already from the \(10^6\) sweep). Test:
  [test_drop_first_contracting_length.py](../../tests/research/juggler_sequence/test_drop_first_contracting_length.py),
  with a control that fails on a weakened floor.
- **The obstruction, stated.** An uncertified drop from \(m\) needs an
  excursion of \(O_{\min}(m)\) odd letters that ends at (or just past) a
  convergent denominator of \(\log_2 3\) on the side \(3^O>2^p\), where the
  slack is \((1-2^{-f_O})\ln m\approx\|O\log_23\|\ln m\), with the near-drop
  losses, of order \(O/(m\ln m)\), aligned against it. Nothing known bounds the
  excursion of a Juggler orbit; the heuristic probability of one that long is
  about \(0.9659^{1.58\,O}\), so the event is unreachable by computation and
  unexcluded by accounting. Terras's Conjecture 2.9 is the same statement with
  the perturbation's sign flipped, and has stood open since 1976.
- **The near-drops, measured.** The question as first posed here was backwards:
  a counterexample does not need a near-drop value within one floor of its
  ideal \(m^{2^{f_o}}\), it needs one about \(0.69f_Om\ln m\) units *below*
  it, an accumulated shortfall (605 units at \(m=10^6\), \(O=665\)). Single
  floors lose under one unit, so the shortfall is a count of earlier
  near-drops at values near \(m\), a Diophantine count over
  \(\{o\log_23\}\), which is what the refined bound does exactly. Measured:
  below \(10^6\) the relative shortfall at a near-drop never exceeds 1.4e-05
  for \(m\ge10^5\) and 2.0e-04 for \(10^4\le m<10^5\), against the
  \(6\cdot10^{-4}\) a counterexample at \(O=665\) would need at \(10^6\).
  The arithmetic of nested powers enters only through the sub-unit losses,
  which are bounded by one anyway; Paper B's machinery has nothing to add to a
  proof here.

## Open questions

- The refined scan past \(O=300000\): the next dangerous denominators are
  10590737 and 53715833, and the scan is linear in \(O\); the sweep to
  \(10^8\) (about three hours) would lift the frontier to 111202.
- An integer statement equivalent to the drop criterion, for Lean.
- Whether the near-drop structure (successive record lows, each a certified
  drop of a larger start) forces the near-drop values off the near misses.

## Decision

**PARK.** The loss accounting is exact and complete for what it can say: an
uncertified drop needs an excursion of at least \(O_{\min}(m)\) odd letters,
\(16266\) for \(m\ge10^6\) and \(31867\) for \(m\ge10^7\), and none exists
below \(10^7\). It cannot say more,
because the criterion's right-hand side is a near-miss distance and nothing
bounds how long an orbit stays above its start. The equality is therefore the
Juggler mirror of Terras's Conjecture 2.9, and this branch records it as an
observation with a proved margin, not as a theorem. Best next question: an
integer form of the drop criterion that Lean can carry, so that the proved
margin joins `power_bound_contracts` in the kernel; the sweep to \(10^8\) is
the cheap mechanical alternative.

## Publication assessment

Status: `STRUCTURAL`. One exact criterion and a table. It belongs in Paper B's
Section 7 (exact floor defects) or beside the bridge as the mirror of
Conjecture 2.9; not a paper, and not an OEIS claim beyond the bound and the
computation already drafted.
