# Juggler cycle finance inequality

Status: **THEOREM** (absorbed into Paper A §4)

Writeup:
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md)
(laboratory extract). Publication text: Paper A
[juggler_finite_dynamics_note.md](../theory/juggler_finite_dynamics_note.md)
Section 4.

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It is not a halt
theorem, not an escape/divergence statement, not a corridor
extension past depth 13, not a reopen of any windowed population
census, and not a claim that every positive integer reaches 1.

The census line (`no_cycle_itinerary_length_le_nineteen`) excludes cycle
words length by length through \(19\). This phase asks a
transversal question:
does the exact defect bookkeeping around a hypothetical cycle bound
the cycle **minimum** as a function of the cycle **length**, so that
one verified floor kills every length at once outside an explicit
exceptional set?

## Problem

For a hypothetical Juggler cycle of length \(L\) with \(o\) odd
letters, the itinerary is formally expanding
(\(2^L<3^o\), `cycle_itinerary_formally_expanding`), yet the orbit
returns exactly. The multiplicative surplus must be financed
entirely by the floor defects, which are relatively tiny. How much
does that force?

## Exact statement

**Cycle finance inequality (EXACT — LEAN VERIFIED,
`cycleMin_finance`).**
Let \(x_0\to x_1\to\cdots\to x_L=x_0\) be a cycle of the Juggler map
\(T\) taken at a `CycleMin` start \(n\ge 2\), word length \(L\ge 1\),
and \(o\) odd letters. Then

\[
n\log n\cdot(3^o-2^L)\;\le\;L\cdot 3^o.
\]

The Lean form uses the dyadic-cell bound \(\log z\le 2\log y+2/y\)
(\(\log(1+1/y)\le 1/y\)) and has constant \(1\). This is Paper A
Theorem 4.4. The inv-sum form
`cycleMin_finance_inv_sum` (Paper A Corollary 4.4c) keeps each
cell defect as \(1/x_{i+1}\). Corollary 4.5 is the convenient
length-only statewise bound. The Phase-0 computational table
uses the weaker constant \(6/5\) below as a certification
majorant, not as a replacement for Theorem 4.4; the cutoff
\(25781\) is not an artifact of that majorant.

**Weaker computational form (EXACT — HUMAN PROOF, proof below).**
Let \(x_0\to x_1\to\cdots\to x_L=x_0\) be a cycle of the Juggler map
\(T\) with every state \(\ge 12\), word length \(L\ge 1\), and
\(o\) odd letters. Let \(n=\min_i x_i\). Then

\[
1-\frac{2^L}{3^o}
\;\le\;\frac65\sum_{i=1}^{L}\frac{1}{x_i\ln x_i}
\;\le\;\frac65\cdot\frac{L}{n\ln n},
\qquad\text{i.e.}\qquad
n\ln n\;\le\;\frac65\cdot\frac{L\cdot 3^{o}}{3^{o}-2^{L}}.
\]

The right side is worst (largest) at the minimal admissible
\(o_{\min}(L)=\min\{o:3^o>2^L\}\). Define

\[
B(L)=\frac65\cdot\frac{L\cdot 3^{o_{\min}}}{3^{o_{\min}}-2^{L}},
\qquad
n_{\max}(L)=\max\{n\in\mathbb N: n\ln n\le B(L)\}.
\]

**Length-only parity finance (EXACT — HUMAN PROOF).**
On a `CycleMin` start \(n\ge 12\), write \(e=L-o\) and
\(t=\lfloor n^{3/2}\rfloor\). Then

\[
\sum_{i=1}^{L}\frac1{x_i\ln x_i}
\;\le\;
\frac{e}{n\ln n}
+\frac{o-e}{t\ln t}
+\frac{e}{2n^2\ln n}.
\]

Combined with the \(6/5\) unroll this is the computational table
used by Paper A Theorem 4.6. It is the joint-minima bound at the
adversarial circuit count \(m=e\), not a reparameterization of
\(B(L)=(6/5)L/\theta\). Proof below.

**Per-length exclusion corollary.** If every \(2\le n\le N_0\)
reaches \(1\), then no state of a cycle can be \(\le N_0\) (a
periodic state never reaches 1), so no Juggler cycle of length
\(L\) exists whenever \(n_{\max}(L)\le N_0\). The crude
\(n_{\max}\) uses \(B(L)\). The parity \(n_{\max}^{\mathrm{par}}\)
uses the length-only sum. At the published floor \(N_0=10^6\),
every \(L<25781\) is excluded by \(n_{\max}^{\mathrm{par}}\).

**Eliahou leftover (EXACT — LEAN VERIFIED implication
`cycle_itinerary_eliahou_leftover`; instance COMPUTATIONALLY
VERIFIED).** If a nontrivial cycle itinerary exists at \(n\ge 2\), and
every length in \([30,10^5)\) outside a named list of
near-convergents is already excluded, then the period is \(84\),
or belongs to that list, or is at least \(10^5\). This is
bookkeeping on `cycle_itinerary_length_eighty_four_or_ge_eighty_five`
plus the finance table: not a new inequality. The instance at the
Python floor \(N_0=2\cdot 10^6\) is the existing family of \(166\)
near-convergent lengths. Length \(84\) is the Lean-named leftover
and is computationally already excluded; height finance further
requires at least three odd-runs
(`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`).
Lengths \(19\), \(38\), \(57\), and \(76\) die at the Lean
residual floor \(261\).

### Proof of the finance inequality

Every state satisfies \(x_{i+1}=\lfloor\sqrt{x_i^{e_i}}\rfloor\)
with \(e_i=1\) (even) or \(e_i=3\) (odd). Hence the exact step
identity

\[
x_{i+1}^2=x_i^{e_i}-d_i,\qquad 0\le d_i\le 2x_{i+1},
\]

because \(x_i^{e_i}<(x_{i+1}+1)^2=x_{i+1}^2+2x_{i+1}+1\). (This is
the local defect of `Defect.lean`; composing it around an itinerary is the
Lean `global_defect_identity`.) The relative defect

\[
\delta_i=\frac{d_i}{x_i^{e_i}}\le\frac{2x_{i+1}}{x_{i+1}^2}
=\frac{2}{x_{i+1}}\le\frac16
\]

using \(x_i^{e_i}\ge x_{i+1}^2\) and \(x_{i+1}\ge 12\). Write
\(t_i=\ln x_i\) and \(\varepsilon_i=-\tfrac12\ln(1-\delta_i)\ge0\);
taking logarithms of the step identity,

\[
t_{i+1}=\frac{e_i}{2}\,t_i-\varepsilon_i .
\]

On \([0,\tfrac16]\) the function
\(g(\delta)=\tfrac65\delta+\ln(1-\delta)\) has \(g(0)=0\) and
\(g'(\delta)=\tfrac65-\tfrac1{1-\delta}\ge0\), so
\(-\ln(1-\delta)\le\tfrac65\delta\) and

\[
\varepsilon_i\le\frac35\,\delta_i\le\frac{6/5}{x_{i+1}} .
\]

Let \(P_k=\prod_{j<k}(e_j/2)\), so \(P_L=3^o/2^L\). Unrolling the
recursion,

\[
t_L=P_L\,t_0-\sum_{i=0}^{L-1}\frac{P_L}{P_{i+1}}\,\varepsilon_i,
\]

and periodicity \(t_L=t_0\) gives the financing identity

\[
t_0\,(P_L-1)=\sum_{i=0}^{L-1}\frac{P_L}{P_{i+1}}\,\varepsilon_i .
\]

Since every \(\varepsilon_j\ge0\), dropping them in the unroll gives
\(t_{i+1}\le P_{i+1}t_0\), i.e. \(P_{i+1}\ge t_{i+1}/t_0\), so
\(P_L/P_{i+1}\le P_L\,t_0/t_{i+1}\). Dividing the financing identity
by \(P_L\,t_0\):

\[
1-\frac1{P_L}
\;\le\;\sum_{i=0}^{L-1}\frac{\varepsilon_i}{t_{i+1}}
\;\le\;\frac65\sum_{i=0}^{L-1}\frac1{x_{i+1}\ln x_{i+1}}
\;\le\;\frac65\cdot\frac{L}{n\ln n}. \qquad\blacksquare
\]

The state floor \(x_i\ge12\) is available: every \(n\le11\) reaches
\(1\) (Lean `reachesOne_of_lt_twelve`), and a periodic state never
reaches \(1\).

### Proof of the length-only parity bound

Take a `CycleMin` start \(n\ge 12\). The last letter is even
(`cycleMin_not_end_odd`), so \(e=L-o\ge 1\). In a circular word
with at least one even letter, every odd-run is preceded by an
even letter, hence the number \(m\) of odd-run starts satisfies
\(m\le e\). The start itself is an odd-run start
(`cycleMin_start_odd`).

Classify the \(L\) states.

- If \(x_i\) is even, then \(\lfloor\sqrt{x_i}\rfloor\ge n\), so
  \(x_i\ge n^2\) (`cycleMin_even_ge_sq`). There are exactly \(e\)
  such states, and
  \(1/(x_i\ln x_i)\le 1/(n^2\ln(n^2))=1/(2n^2\ln n)\).
- If \(x_i\) is odd and preceded by an even state, then \(x_i\)
  is an odd-run start and \(x_i\ge n\). There are \(m\le e\) such
  states.
- If \(x_i\) is odd and preceded by an odd state, then
  \(x_i=\lfloor x_{i-1}^{3/2}\rfloor\) with \(x_{i-1}\ge n\) odd,
  so \(x_i\ge t=\lfloor n^{3/2}\rfloor\)
  (`floorPower_odd_mono`). There are \(o-m\ge o-e\) such states.

The worst-case (largest) sum is therefore at \(m=e\):

\[
\sum_{i=1}^{L}\frac1{x_i\ln x_i}
\;\le\;
\frac{e}{n\ln n}
+\frac{o-e}{t\ln t}
+\frac{e}{2n^2\ln n}.
\]

For \(n\ge 12\) one has \(t=\mathrm{isqrt}(n^3)\ge 41\), so every
logarithm is positive. Substituting into the \(6/5\) financing
identity of the previous proof yields

\[
n\ln n\cdot\theta
\;\le\;
\frac65\left(
e+(o-e)\frac{n\ln n}{t\ln t}+\frac{e}{2n}
\right).
\]

The right-hand side decreases in \(n\). At the least admissible
\(o=o_{\min}(L)\) one has \(o-e<e\), so every internal odd can
sit at \(t\); a finer run-height packing does not improve this
length-only bound. The optimal uniform coefficient
\(-\ln(1-\delta)\le c_*\delta\) on \([0,1/6]\) is
\(c_*=6\ln(6/5)\). The published table keeps \(6/5\). \(\blacksquare\)

### Prefix-weight comparison (EXACT — HUMAN PROOF)

The exact unroll without converting the suffix weights is

\[
\theta
=\sum_{i=0}^{L-1}\frac{\varepsilon_i}{t_0\,P_{i+1}}
\le
\frac65\sum_{i=0}^{L-1}\frac1{P_{i+1}\,x_{i+1}\ln n}.
\]

Dropping future \(\varepsilon\ge 0\) gives the envelope
\(t_{i+1}\le P_{i+1}t_0\), i.e.
\(P_{i+1}\ge\ln x_{i+1}/\ln n\). On a `CycleMin` one has
\(x\ge n\), so \(\ln x/\ln n\ge 1\). Therefore

\[
\frac1{P\,x\ln n}
\le
\frac1{x\ln x}
\qquad\text{whenever }P\ge\frac{\ln x}{\ln n}.
\]

The published \(6/5\) identity already uses that conversion.
The CycleMin prefix law \(P_k\ge 1\) (`cycleMin_prefix_pow_le`)
is a weaker lower bound on \(P\) than the envelope whenever
\(x>n\). On the ideal trajectory \(x=n^{P}\) the two forms
coincide. Charging every state at \(P\equiv 1\) therefore does
not improve the parity sum; it enlarges the internal and even
terms (\(1/(t\ln n)\) versus \(1/(t\ln t)\), and
\(1/(n^2\ln n)\) versus \(1/(2n^2\ln n)\)). A leftover-killing
gain would require a length-only lower bound on \(P\) that
beats \(\ln x/\ln n\) on the expensive states. Those states
are the valleys (\(x=n\)). The start has \(P=0\)-prefix \(1\);
later valleys on a near-convergent word can keep \(P\)
arbitrarily close to \(1\). \(\blacksquare\)

## Current literature

- Collatz m-cycle exclusion by financing-versus-gap plus bounds on
  \(|2^L-3^o|\) — **known**
  (`simons-de-weger-2005-collatz-m-cycles`); this branch is the
  floor-power adaptation, **independent** of that proof's details.
  The structural difference: Juggler per-step defects are relatively
  \(O(1/x)\) in logarithms, versus \(O(1)\) for Collatz, so the
  financing constraint is far more lopsided here.
- Eliahou leftover packaging for Collatz — **known** (period
  \(\ge X\), or one of a named convergent family). The Juggler
  analogue is `cycle_itinerary_eliahou_leftover`: period \(84\), or a
  listed near-convergent, or \(\ge 10^5\).
- Small-cycle census — **EXACT — LEAN VERIFIED**
  (`no_cycle_itinerary_length_le_eight`,
  [juggler_length_eight_cycles.md](juggler_length_eight_cycles.md))
- Formal expansion of cycle itineraries — **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_formally_expanding`)
- Global defect identity — **EXACT — LEAN VERIFIED**
  (`global_defect_identity`,
  [juggler_global_defect.md](juggler_global_defect.md))
- Peak-block financing at the cycle maximum — **EXACT — LEAN
  VERIFIED** (`cycle_peak_finance`); local to the peak, distinct
  from the whole-cycle log financing used here
- Residual landing class \(\{1,\dots,11\}\) reaches 1 — **EXACT —
  LEAN VERIFIED** (`reachesOne_of_lt_twelve`)
- Every start reaches 1 — not claimed

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Does the exact defect-financing identity around a cycle force
                        n·ln n <= (6/5)·L·3^o/(3^o − 2^L), and does this, combined with
                        exact min|3^o − 2^L|, the length-<=8 census, and a verified
                        floor, exclude all Juggler cycles outside a finite set of
                        near-convergent lengths?
Novelty hypothesis      A Simons–de Weger-style cycle elimination for the Juggler map.
                        Nothing in the ledger combines the global defect identity with
                        two-power/three-power gap lower bounds.
Falsifier               Financing slack measured on real orbit segments violates the
                        per-step bound eps_i <= (6/5)/x_{i+1}, or the min bound stays
                        above any reachable floor for infinitely many lengths in a way
                        that is not confined to near-convergent L.
Existing machinery      globalDefect identity, pathDefectSum/pathPows, cycle_itinerary_
                        formally_expanding, cycle_peak_finance, CycleDiophantine, census
                        <= 8, reachesOne_of_lt_twelve, Python juggler tooling.
Maximum Phase-0 scope   Derivation note + one computational probe: exact gap table
                        L <= 10^5, min-bound tabulation, floor verification by descent
                        induction to 10^6, per-step slack stress test. No new Lean.
Promotion criterion     Inequality verified with clean L-independent constants AND the
                        exceptional-length set is finite/structured so that finance +
                        census + a realistic floor raise covers all L -> PROMOTE to Lean.
Stop criterion          Constant degrades with L, or exceptional lengths require floors
                        beyond feasible computation -> PARK with the quantitative
                        frontier recorded. Inequality falsified on orbit data -> CLOSE.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Step identity \(x_{i+1}^2=x_i^{e_i}-d_i\), \(0\le d_i\le
  2x_{i+1}\) — **KNOWN** (integer form of `Defect.lean`)
- Whole-cycle log financing identity
  \(t_0(P_L-1)=\sum_i(P_L/P_{i+1})\varepsilon_i\) — **EXACT — HUMAN
  PROOF** (this dossier; Lean uses the equivalent cell unroll
  `cycleMin_log_envelope`)
- Finance inequality \(n\log n\cdot(3^o-2^L)\le L\cdot 3^o\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_finance`)
- Weaker form \(n\ln n\le\frac65 L\,3^o/(3^o-2^L)\) —
  **EXACT — HUMAN PROOF** (crude Phase-0 computational table)
- Length-only parity finance
  \(\sum 1/(x_i\ln x_i)\le e/(n\ln n)+(o-e)/(t\ln t)+e/(2n^2\ln n)\) —
  **EXACT — HUMAN PROOF** (this dossier; joint-minima at \(m=e\))
- Prefix-weight comparison: \(P\ge\ln x/\ln n\ge 1\) on a
  `CycleMin`, so the naive \(P\equiv 1\) unroll is weaker than the
  published \(1/(x\ln x)\) form —
  **EXACT — HUMAN PROOF** (this dossier)
- Run-type packing: \(o-e\) copies of `OOE` from \(n\) and
  \(2e-o\) copies of `OE` from \(n^{4/3}\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- No cycle itinerary of length \(\le 19\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_length_le_nineteen`)
- Period is \(84\) or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_or_ge_eighty_five`);
  the cheap leftovers \(57\) and \(76\) die at the floor \(261\);
  \(L=84\) is the next record near-convergent
- Period is \(84\) with at least three odd-runs, or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Period is \(57\) or \(\ge 58\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_fifty_seven_or_ge_fifty_eight`), the
  weaker leftover before the two extra odd seeds
- Period is \(38\) or \(\ge 39\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_thirty_eight_or_ge_thirty_nine`), the
  weaker leftover before the \(61/11\) certificate
- Period is \(19\) or \(\ge 30\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_nineteen_or_ge_thirty`), the weaker
  floor-\(53\) leftover
- Eliahou leftover: period \(84\), or a listed near-convergent, or
  \(\ge 10^5\) —
  **EXACT — LEAN VERIFIED** as the implication
  `cycle_itinerary_eliahou_leftover`; the laboratory \(166\)-family
  instance at floor \(2\cdot 10^6\) is **COMPUTATIONALLY VERIFIED**
  (Paper A Theorem 4.6 prints the parity table at floor \(10^6\):
  prefix \(25780\), \(141\) exceptions)
- Period is \(\ge 14\) —
  **EXACT — LEAN VERIFIED** (`cycle_itinerary_length_ge_fourteen`),
  a corollary of the stronger leftover
- Residual floor \(n<261\) reaches \(1\) —
  **EXACT — LEAN VERIFIED**
  (`reachesOne_of_lt_two_hundred_sixty_one`)
- Residual floor \(n<257\) reaches \(1\) —
  **EXACT — LEAN VERIFIED**
  (`reachesOne_of_lt_two_hundred_fifty_seven`)
- Residual floor \(n<53\) reaches \(1\) —
  **EXACT — LEAN VERIFIED** (`reachesOne_of_lt_fifty_three`)
- Per-length exclusion given a verified floor —
  **COMPUTATIONALLY VERIFIED** at the Phase-0 window (below)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_finance`
- Records: [juggler_cycle_finance.md](../research/juggler_cycle_finance.md),
  [juggler_cycle_finance.json](../research/juggler_cycle_finance.json)
- Dataset: `data/research/juggler/cycle_finance/`
  (`exceptions.json` crude table;
  `exceptions_parity.json` length-only parity table;
  `prefix_weights.json` leftover-weight scan;
  `budget_opt.json` run-type leftover scan;
  `run_extremum.json` cyclic run-extremum scan)
- Tests: `tests/research/juggler_sequence/test_cycle_finance.py`

Science window: gap table \(L\le 10^5\) with exact bignum
arithmetic; floor verification by first-passage descent induction
for all \(2\le n\le 2\cdot 10^6\); slack stress on named hard seeds
(including \(30817\)). Tests use \(L\le 400\) and floor \(2000\).
No CLI. Lean: `CycleFinance.lean` (`cycleMin_finance`,
`cycle_finance_min_two_hundred_fifty_seven`) with the census
companion `CycleFinanceLeftovers.lean`
(`no_cycle_itinerary_length_le_nineteen`,
`cycle_itinerary_length_eighty_four_or_ge_eighty_five`,
`cycle_itinerary_eliahou_leftover`; table-driven length exclusions over
`financeRows53` / `financeRows257` / `financeRows261`),
`CycleHeightFinance.lean`
(`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`),
`TerminationFloor257.lean`
(`reachesOne_of_lt_two_hundred_fifty_seven`), and
`Termination.lean` (`reachesOne_of_lt_fifty_three`). Writeup:
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).
Paper A Section 4 is this inequality, the length-only parity
refinement, and the floor-\(10^6\) leftover (prefix \(25780\)).

## Conjectures

None opened. (The statement "no Juggler cycle of any length" is a
target, not a conjecture entered in `conjectures/`.)

## Counterexamples

The per-step bound \(\varepsilon_i\le(6/5)/x_{i+1}\) held at
every measured step; see Results.

The hypothesis that exact unrolling weights \(1/P_i\) exclude a
parity leftover at \(N_0=10^6\) is **REFUTED**
(`conjectures/refuted/juggler_cycle_prefix_weight_leftover_killer.json`):
\(P\equiv 1\) is weaker than parity on all \(141\) leftovers;
later-valley \(P\ge 9/8\) is not a length-only law, and even
under that diagnostic \(L=25781\) survives.

## Formalization

`CycleFinance.lean` sits on `CycleCore` alone and carries only the
paper inequality: the cell logarithm bound is `log_le_two_log_add`;
the unrolled envelope is `cycleMin_log_envelope`; the inequality is
`cycleMin_finance` (with `cycleMin_finance_inv_sum` as Corollary
4.4c). The census lives in the laboratory companion
`CycleFinanceLeftovers.lean`, so the walk layer no longer compiles
it: the residual floor `257`
(`reachesOne_of_lt_two_hundred_fifty_seven`) gives
`cycle_finance_min_two_hundred_sixty_one`, hence
`no_cycle_itinerary_length_le_nineteen` and the length leftover
`cycle_itinerary_length_eighty_four_or_ge_eighty_five`. Lengths `19`
and `30`–`83` die by finance at floors `257` and `261`, encoded as
the row tables `financeRows53` / `financeRows257` / `financeRows261`
with one membership lemma each. The
floor-`261` comparison uses \(261\log 257>15921/11\); \(L=84\)
survives the uniform bound. `CycleHeightFinance.lean` keeps the
inv-sum defects and excludes every length-`84` word with at most
two odd-runs, so the laboratory leftover is
`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`.
Eliahou packaging `cycle_itinerary_eliahou_leftover` still rewrites
the length leftover plus the finance table as period `84`, or
a listed near-convergent, or at least `10^5`. There is no theorem named
`no_cycle_itinerary_length_eleven`: that name is reserved by the
parked leftover-itinerary probes. No `sorry`. Paper A imports
`CycleFinance` for Theorem 4.4 and Corollary 4.4c and does not
import `CycleHeightFinance`.
Not a halt theorem and not `no_cycle_itinerary_any_length`.
The Python floor \(N_0=2\cdot 10^6\) is
**COMPUTATIONALLY VERIFIED**, not Lean. Paper A Theorem 4.6
prints the length-only parity table at the published floor
\(10^6\) (prefix \(25780\), \(141\) exceptions). The compiled
leftover and exclusions are written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).
The refined lemma is not Lean.

## Results

Classification **CYCLE_FINANCE_GREEN**. Regenerate with
`python -m research.juggler_sequence.cycle_finance`; records in
[juggler_cycle_finance.md](../research/juggler_cycle_finance.md)
and `data/research/juggler/cycle_finance/`.

- **Finance inequality** — **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`, Paper A Theorem 4.4, constant \(1\)):
  \(n\log n\cdot(3^o-2^L)\le L\cdot 3^o\).
  Inv-sum form `cycleMin_finance_inv_sum` is Paper A
  Corollary 4.4c and now lives in `CycleFinance.lean`.
  The Phase-0 per-step ingredient \(\varepsilon_i\le(6/5)/x_{i+1}\)
  held at every measured orbit step with relative margin
  \(\ge 0.17\); the unrolled log identity reproduced every orbit
  exactly (relative error \(\le 2\cdot10^{-16}\)); real orbits use
  only \(0.22\)–\(0.47\) of the financing budget (mean defect
  ratio \(d/(2x')\approx 0.5\)).
- **Lean residual floor \(261\)** — **EXACT — LEAN VERIFIED**
  (`reachesOne_of_lt_two_hundred_sixty_one`): two extra odd
  seeds \(257\) and \(259\) (five steps, \(13\)-bit peaks)
  raise the floor past the exact-log barrier at \(257\)
  (\(257\ln 257\approx1426<1430.8=n_{\mathrm{need}}(57)\)).
  Combined with \(261\log 257>15921/11\) this excludes the
  cheap leftovers \(57\) and \(76\).
- **Lean residual floor \(257\)** — **EXACT — LEAN VERIFIED**
  (`reachesOne_of_lt_two_hundred_fifty_seven`): every
  \(1\le n<257\) reaches \(1\). Evens below \(2809\) already
  reduce to \(\{1,\dots,52\}\); the odd seeds \(53,55,\dots,255\)
  are finite orbit certificates (the longest is \(193\),
  seventy-three steps). Combined with `cycleMin_finance` this
  excludes length \(19\). The tighter certificate
  \(\log 257>61/11\) also excludes length \(38\). The Python
  \(6/5\) table has \(n_{\max}(19)=297\); the Lean constant
  \(1\) only needs \(n\ln n>1411.63\), so the smallest such
  \(n\) is \(255\).
- **Lean residual floor \(53\)** — **EXACT — LEAN VERIFIED**
  (`reachesOne_of_lt_fifty_three`): every \(1\le n<53\) reaches
  \(1\). Evens below \(144\) already reduce to \(\{1,\dots,11\}\);
  the odd seeds \(13,15,\dots,51\) are finite orbit certificates
  (the longest is \(37\), seventeen steps, peak
  \(\approx 2.5\cdot10^{13}\)).
- **Lean census extension** — **EXACT — LEAN VERIFIED**: no cycle
  itinerary of length \(\le 19\); lengths \(30\)–\(83\) die at floors
  \(257\) and \(261\); any remaining cycle has period \(84\) with
  at least three odd-runs, or \(\ge 85\). The cheap leftovers
  \(57\) and \(76\) die at floor \(261\)
  (`finance_excludes_length_fiftyseven`,
  `finance_excludes_length_seventysix`). Uniform finance leaves
  \(L=84\) open (\(\tfrac{15921}{11}\), need \(\approx 40269\));
  height finance kills \(m\le 2\).
- **Floor** — **COMPUTATIONALLY VERIFIED**: every
  \(2\le n\le 2\cdot 10^6\) has a finite first passage below its
  start, hence by strong induction reaches \(1\). Max first-passage
  length \(257\) steps (seed \(1122603\)); peak intermediate
  value \(6{,}485{,}496\) bits. Evens drop in one square-root
  step, so only odds are walked. Exact integer arithmetic
  throughout. The previous floor \(10^6\) (seed \(78901\),
  \(253\) steps) remains a valid weaker certificate and is what
  Paper A Theorem 4.6 prints.
- **Length-only parity table** — **COMPUTATIONALLY VERIFIED**
  (`exceptions_parity.json`): at the published floor
  \(N_0=10^6\), the parity bound excludes every \(L\le 25780\)
  and every \(L\le 10^5\) outside \(141\) lengths. No comparison
  is uncertain. First survivor \(L=25781\) with
  \(n_{\max}^{\mathrm{par}}=26254995\). Length \(1054\) dies at
  this floor (\(n_{\max}^{\mathrm{par}}=788014\)). This is not
  the crude table at floor \(2\cdot 10^6\)
  (`J-residual-floor-two-million`): same prefix, different
  inequality. SHA-256 of the length list
  `dd71aa1527656ba51cb031bafa5497f7bfdbbc43151ffba2c595793326bf7944`.
- **Per-length exclusion (crude table)** — **COMPUTATIONALLY
  VERIFIED** (exact gap table \(L\le10^5\), conservative
  rounding): with the floor \(N_0=2\cdot 10^6\), the *crude*
  \(6/5\) bound also excludes every \(L\le 25780\), with
  \(166\) exceptions through \(10^5\). Length \(1054\) dies
  there by raising the floor
  (\(n_{\max}\approx 1.997\cdot 10^6\)), not by the parity sum.
- **Eliahou leftover** — **EXACT — LEAN VERIFIED** implication
  (`cycle_itinerary_eliahou_leftover`): period \(84\), or a listed
  near-convergent, or \(\ge 10^5\). The laboratory instance at
  floor \(2\cdot 10^6\) of the crude table is
  **COMPUTATIONALLY VERIFIED** (the existing \(166\)
  near-convergents). Paper A Theorem 4.6 prints the parity
  instance at floor \(10^6\) (\(141\) exceptions, prefix
  \(25780\)). Length \(84\) is kept as the Lean-named leftover;
  both tables already exclude it. Lengths \(19\), \(38\),
  \(57\), and \(76\) are no longer Lean leftovers. Not a new
  inequality.
- **Prefix-weight leftover scan** — **COMPUTATIONALLY VERIFIED**
  (`prefix_weights.json`): at \(n=10^6+1\), none of the \(141\)
  parity leftovers is excluded by parity or by the naive
  \(P\equiv 1\) weight form. The \(P\equiv 1\) right-hand side is
  at least the parity right-hand side on every leftover (weaker,
  as the comparison lemma requires). An optimistic later-valley
  constraint \(P\ge 9/8\) (least expanding even-terminating
  circuit `OOE`) would exclude the eighteen lengths
  \(81643+1054k\) for \(k=0,\ldots,17\); the frontier leftover
  \(L=25781\) still fails
  (\(\theta\approx 2.55\cdot 10^{-5}\) versus
  \(\mathrm{RHS}_{9/8}\approx 7.35\cdot 10^{-4}\)). Those
  eighteen kills are not certified: later valleys on a
  near-convergent word can keep \(P\) closer to \(1\) than
  \(9/8\).
- **Run-type budget packing** — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  (`budget_opt.json`,
  [juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md)):
  an \(n\)-circuit cannot start `OE` and an `OO`-circuit from
  \(n\) takes only one even. The leftover set shrinks from
  \(141\) to \(99\) (\(56347+1054k\), \(k=0,\ldots,41\) die).
  First survivor remains \(25781\). Unique visit and
  \(M\to\infty\) do not bind. Paper A prints the parity table
  as Theorem 4.6 and the run-type leftover with the lattice as
  Theorems 4.7--4.8 and Proposition 4.9.
- **Exceptional structure**: the \(166\) exceptions are exactly the
  near-convergent lengths — multiples of \(25781\) plus
  combinations with earlier convergents. The record
  (one-sided best-approximation) lengths in range are
  \(L=1,3,11,19,84,569,1054,25781,50508\) with
  \(n_{\max}=3,13,52,297,5599,58398,\approx2.0\cdot10^6,
  \approx6.7\cdot10^7,\approx4.2\cdot10^8\); they track the
  continued-fraction convergents of \(\ln 2/\ln 3\). The
  run-type \(99\)-set at floor \(10^6\) is the surplus
  intermediate lattice on the unimodular basis
  \((25781,16266)\), \((1054,665)\), cut by packing on \(F_1\)
  after \(L=55293\)
  ([juggler_run_survivor_lattice_note.md](../theory/juggler_run_survivor_lattice_note.md)).
  That organization explains the list and does not constrain
  actual cycles.
- **Floor sensitivity**: a floor of \(10^9\) would leave **zero**
  exceptions below \(L=10^5\) (the worst requirement in range is
  \(n_{\max}(50508)\approx4.2\cdot10^8\)).
- **Census cross-check**: at \(L\le 8\) the finance bound plus the
  Lean residual floor (\(n\le11\) reaches 1) independently kill
  \(L\in\{1,2,4,5,7,8\}\); \(L\in\{3,6\}\) (the near-tight
  \(2^3<3^2\) and its double) remain census-only — consistent with
  and transversal to `no_cycle_itinerary_length_le_eight`.

## Open questions

- The Lean leftover is \(L=84\) with at least three odd-runs, or
  \(L\ge 85\); Eliahou packaging still names the length leftover
  as \(84\), or a listed near-convergent, or \(\ge 10^5\).
  Cheap \(19\)-gap cousins \(95,114,\ldots\) sit in the
  \(\ge 85\) bucket. Global finance kills \(L=84\) only at residual
  floor \(4756\) (constant \(1\); Python \(n_{\max}=5599\)). That
  campaign is **PARK**: \(2247\) new odd certificates, peak
  \(19694\) bits at \(n=2183\), and \(4756>53^2\). Joint-minima
  and the height law kill every \(m\) first, at floor \(1981\)
  (constant \(1\)), still \(859\) odds with a \(900\)-bit peak.
  Height kills \(L=84\) as a 1-cycle or 2-cycle at the live floor
  \(261\), now **EXACT — LEAN VERIFIED**. The hypothesis that
  \(4756\) is the cheapest kill is **REFUTED**
  (`conjectures/refuted/juggler_cycle_finance_l84_floor_4756.json`).
  Length \(84\) with \(m\ge 3\) is the remaining named leftover;
  excluding it at floor \(261\) is **REFUTED**
  (`juggler_l84_m_ge_three_floor_261`). The upper cell
  \((p+1)^{2^r}\) is also **REFUTED** as a leftover-killer
  ([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md)):
  the adversarial peak run \(k=24\) lands at \(304\).
  A second-valley bound \(\ge 281\) is also **REFUTED**
  ([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)):
  the adversarial triple is \(261,281,303\).
- The exceptional near-convergent lengths need a larger verified
  floor (each factor of \(10^3\) in floor pushes the frontier
  roughly one convergent out). The finance inequality bounds the
  minimum per length, not the length itself. A Baker / Rhin lower
  bound on \(\lvert 3^o-2^L\rvert\) does **not** kill leftover
  near-convergents
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md),
  **CLOSE**). Near-tight rigidity (`NearTightScale.lean`) does
  **not** cover leftover \(L\) simultaneously
  ([juggler_cycle_near_tight.md](juggler_cycle_near_tight.md),
  **CLOSE**): cycle \(1+q=n^{3^o-2^L}\) is the opposite of
  open-orbit \(q\to 0\). Christoffel / mechanical-word unique
  maximizers do **not** reduce leftover-itinerary or CycleMin
  candidates to a one-parameter necklace
  ([juggler_cycle_christoffel.md](juggler_cycle_christoffel.md),
  **CLOSE**). Prefix-weight finance
  (\(P\equiv 1\), or optimistic later-valley \(P\ge 9/8\)) is
  **CLOSE** as a leftover-killer
  (`juggler_cycle_prefix_weight_leftover_killer`): the naive
  weight form is weaker than parity and excludes nothing; the
  \(9/8\) diagnostic is not a length-only theorem. Run-type
  packing is **PROMOTE**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md)):
  it shrinks \(\mathcal E_{\mathrm{par}}(10^6)\) to \(99\)
  leftovers without moving the first survivor. Closed peak–valley
  Fourier and exact pair-level floor closure are both **CLOSE**
  leftover-killers
  (`juggler_cycle_fourier_leftover_killer`,
  `juggler_cycle_closure_leftover_killer`).
  Exact modular floor-cell closure is also **CLOSE**
  (`juggler_cycle_mod_closure_leftover_killer`).
  Finance-conditioned exact closure is also **CLOSE**
  (`juggler_cycle_conditioned_closure_leftover_killer`).
  Ordered excursion closure is also **CLOSE**
  (`juggler_cycle_ordered_excursion_leftover_killer`).
  Correlated floor-defect finance is also **CLOSE**
  (`juggler_cycle_defect_correlation_leftover_killer`).
  Cross-excursion usable-loss persistence is also **CLOSE**
  (`juggler_cycle_loss_persistence_leftover_killer`).
  Near-top defect anti-clustering is also **CLOSE**
  (`juggler_cycle_defect_anticluster`).
  Exact almost-cycle search at \(L=25781\) is also **CLOSE**
  (`juggler_cycle_almost_search`).
  The finance-to-cell bridge is also **CLOSE**
  (`juggler_cycle_finance_cell_bridge`).
- The named future program is the state-distribution bound of
  Paper A Section 5:
  \(\max\sum 1/(x_i\log x_i)\) over realizable cycle geometry.
  Return-cost coupling is **CLOSE**
  ([juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md)).
  Cheap-band descent next-run type is also **CLOSE**
  ([juggler_cycle_descent_next_run.md](juggler_cycle_descent_next_run.md)).
  Cheap-cluster Amplify versus surplus is also **CLOSE**
  ([juggler_cycle_cluster_amplify.md](juggler_cycle_cluster_amplify.md)).
  Global orbit-budget coupling is also **CLOSE**
  ([juggler_cycle_trajectory_budget.md](juggler_cycle_trajectory_budget.md)).
  The program stays **PARK**.

## Decision

**PROMOTE**. Paper A now states the finance hierarchy:
Theorem 4.4 is the conceptual sharp inequality (constant \(1\));
Corollary 4.5 is the convenient statewise bound; Theorem 4.6
certifies the table with the conservative coefficient \(6/5\).
The inv-sum form is Corollary 4.4c in `CycleFinance.lean`.
The length-only parity bound is not a
reparameterization of \(B(L)=(6/5)L/\theta\): it charges \(e\)
valleys at \(n\), \(o-e\) internals at \(\lfloor n^{3/2}\rfloor\),
and \(e\) evens at \(n^2\). The certified scan at \(N_0=10^6\)
excludes every \(L\le 25780\) with \(141\) survivors and no
uncertain comparisons. Paper A Theorem 4.6 prints that
table. The cutoff \(25781\) is not an artifact of \(6/5\). The crude table at floor \(2\cdot 10^6\) remains a
separate laboratory certificate (same prefix, weaker
inequality). Leftover \(84\) with \(m\ge 3\) is unchanged as the
Lean companion. This is not a leftover-itinerary census and not a
halt theorem.

The residual-floor campaign past \(\approx 4756\) is **PARK**.
Joint/height kill every \(m\) at \(1981\), still machinery
gravity.

The prefix-weight leftover-killer is **CLOSE**. The exact
unroll with \(P\ge 1\) is weaker than the published envelope
conversion and excludes none of the \(141\) leftovers. An
optimistic later-valley \(P\ge 9/8\) would drop eighteen large
members of the \(1054\)-family; it is not a theorem, and
\(L=25781\) still lives. Keep the comparison lemma as negative
knowledge. No Paper A edit.

The cyclic run-type leftover-killer is **CLOSE**
(`juggler_cycle_run_extremum_leftover_killer`): two-type is
already the relaxed maximum; cheap-`OOE` adjacency does not
prove \(N_{\mathrm{cheap}}<o-e\).

The prefix-expansion leftover-killer is **CLOSE**
(`juggler_cycle_prefix_feasibility_leftover_killer`): the
extremal path \(o_k=r(k)\) and the ceiling Christoffel word
are admissible for every one of the \(99\) leftovers.

The Fourier leftover-killer is **CLOSE**
(`juggler_cycle_fourier_leftover_killer`): the spectral moment
is the O/E increment law.

The exact pair-level floor-closure leftover-killer is **CLOSE**
(`juggler_cycle_closure_leftover_killer`): word-independent
intervals reduce to the exponent envelope.

The exact modular floor-cell leftover-killer is **CLOSE**
(`juggler_cycle_mod_closure_leftover_killer`): at CycleMin
scale \(R_{\mathrm{nec}}\) is first-letter parity and every
listed modulus has a diagonal on both spotlight leftovers.

The finance-conditioned exact-closure leftover-killer is **CLOSE**
(`juggler_cycle_conditioned_closure_leftover_killer`): leftover
\(\theta\) does not force near-extremal run structure. Deepening
every `OE` still leaves packed \(>\theta\).

The ordered-excursion leftover-killer is **CLOSE**
(`juggler_cycle_ordered_excursion_leftover_killer`): \((2,2,1)\)
at a CycleMin start is the composed OOE envelope \(81/64<4/3\).
\((2,2,2)\) is realized near \(n\), and \((2,2,1)\) becomes
legal at scale \(n^{9/8}\). Retaining the exact landings
\(4447\) versus \(33811\) still yields no region \(C_{a,b}\).

The correlated floor-defect leftover-killer is **CLOSE**
(`juggler_cycle_defect_correlation_leftover_killer`): realized
`OE`/`OO` pairs occupy both cheap and finance-maximal cell
corners. Pair-eps ratio \(0.9999\); pair-finance gap \(0\).
The non-additive recurrence is `global_defect_append`.

The cross-excursion usable-loss leftover-killer is **CLOSE**
(`juggler_cycle_loss_persistence_leftover_killer`): CycleMin-scale
pairs reach \(\max\min(U_0,U_1)=0.9767\) and
\(\max(U_0+U_1)=1.968\). `OOE` near-top events cluster.
Finance weighting does not create an anti-correlation.

The near-top defect anti-clustering leftover-killer is **CLOSE**
(`juggler_cycle_defect_anticluster`): same-pair
\((u,u')=(0.99759,0.99989)\) at \(x=2745367\); twelve `OO`
pairs have both coordinates \(\ge 0.995\); \(f(0.995)=0.99996\).

The exact almost-cycle leftover-killer is **CLOSE**
(`juggler_cycle_almost_search`): no \(E_{25781}\) on the
run-type window; max packed-legal first-passage \(257\);
the distinguished word is not followed past depth \(11\);
exact backward dies at the first `OOE` cell.

The finance-to-cell leftover-killer is **CLOSE**
(`juggler_cycle_finance_cell_bridge`): terminal \((2,1)\)
is forced by Sturmian isolation plus expanding last `OOE`,
and is commonly realized; follow death is the shared `OOE`
prefix; empty \((2,2,1)\) is \(243<256\).

The return-cost leftover-killer is **CLOSE**
(`juggler_cycle_valley_coupling_leftover_killer`):
`OOE` lands at \(n^{9/8}\), not \(n+2\); the shortest
envelope descent is \(O^5E^3\); \(O^{53}E^{31}\) restores
\(n^{1.002}\). No certified leftover dies.

The cheap-band descent leftover-killer is **CLOSE**
(`juggler_cycle_descent_next_run`): a descent onto
\([n,19n]\) can start \(a=2\). One-even witness
\(p=1000057\); post-`OOE` witness
\(1000057\to 5623773\). \(297\) of \(1210\) cheap-band
`OOE` landings in the \(20\,000\)-window start \(a=2\).

The cheap-cluster Amplify leftover-killer is **CLOSE**
(`juggler_cycle_cluster_amplify`): on \((\mathtt{OOE})^k\)
the linear Amplify exponent is \(9^k-3\), so the \(n^3\)
gap is invariant under appending `OOE`. Optimistic
\(\rho\asymp n^{3/2}\) leaves gap \(3/2\). Cubics stay
\(n^{-3}\) behind the linear term. Realized `OOE` at
\(365\), \(1517\), \(1000057\) has Amplify \(<G\).

Best next question: none from cheap-cluster Amplify. The
state-distribution program of Paper A Section 5 stays **PARK**.
Option B is closed as a finance input on cheap `OOE`
clusters. Global orbit-budget coupling is **CLOSE**
(`juggler_cycle_trajectory_budget`): \(C_{\max}^{\mathrm{ub}}\)
at \(n=10^6+1\) equals `budget_rhs`; the tree dies at
archived `OOE` / CycleMin tags after at most one circuit.
The factor-\(23\) valley gap at \(L=25781\) is
unchanged as a certified charge.

Length \(84\) at \(m\ge 3\) at floor \(261\) is **REFUTED** as a
leftover-killer
([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md)). The
upper cell \((p+1)^{2^r}\) is also **REFUTED**
([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md)).
A second-valley bound \(\ge 281\) is also **REFUTED**
([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)).
Prefix weights \(1/P_i\) are also **REFUTED** as a leftover-killer
(`juggler_cycle_prefix_weight_leftover_killer`).
Cyclic run-depth / adjacency is also **REFUTED** as a leftover-killer
(`juggler_cycle_run_extremum_leftover_killer`).
Prefix expansion of near-convergents is also **REFUTED** as a
leftover-killer
(`juggler_cycle_prefix_feasibility_leftover_killer`).
Closed peak–valley Fourier is also **REFUTED** as a leftover-killer
(`juggler_cycle_fourier_leftover_killer`).
Exact pair-level floor closure is also **REFUTED** as a leftover-killer
(`juggler_cycle_closure_leftover_killer`).
Exact modular floor-cell closure is also **REFUTED** as a leftover-killer
(`juggler_cycle_mod_closure_leftover_killer`).
Finance-conditioned exact closure is also **REFUTED** as a leftover-killer
(`juggler_cycle_conditioned_closure_leftover_killer`).
Ordered excursion closure is also **REFUTED** as a leftover-killer
(`juggler_cycle_ordered_excursion_leftover_killer`).
Exact almost-cycle search at \(L=25781\) is also **REFUTED**
as a leftover-killer
(`juggler_cycle_almost_search`).
The finance-to-cell bridge is also **REFUTED** as a
leftover-killer
(`juggler_cycle_finance_cell_bridge`).
Return-cost valley coupling is also **REFUTED** as a
leftover-killer
(`juggler_cycle_valley_coupling_leftover_killer`).
Cheap-band descent next-run type is also **REFUTED** as a
leftover-killer
(`juggler_cycle_descent_next_run`).
Cheap-cluster Amplify versus surplus is also **REFUTED** as a
leftover-killer
(`juggler_cycle_cluster_amplify`).
The cyclic valley-necklace leftover-killer is also **REFUTED**
(`juggler_cycle_cyclic_valley`): on a two-type CycleMin
necklace \(N_{\mathrm{cheap}}\le N_{\mathrm{OE}}=2764<6751\),
but the charged RHS stays a factor \(11.94\) above \(\theta\)
and the wrap-around is not a privileged extra tax.
Run-height packing does not improve the length-only
\(n_{\max}\) at \(o_{\min}\).

## Publication assessment

Status: absorbed into Paper A as Section 4. Laboratory extract
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md);
not a second manuscript. One exact inequality (`cycleMin_finance`,
Paper A Theorem 4.4, **EXACT — LEAN VERIFIED**) with a genuinely
new consequence (wholesale cycle-length exclusion: printed leftover
Theorem 4.6, no period \(\le 25780\) by the length-only parity
table at floor \(10^6\), \(141\) exceptions; laboratory crude
table at floor \(2\cdot 10^6\) has the same prefix and \(166\)
exceptions; Lean leftover \(84\) with \(m\ge 3\) or \(\ge 85\) is
Appendix A companion) and
a clear
literature distinction: the Simons–de Weger financing-versus-gap
template transferred to a floor-power map where defects are
relatively \(O(1/x)\) in logarithms. Not a totality result; the
escape half is untouched.
