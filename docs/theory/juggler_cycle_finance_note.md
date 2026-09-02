# Cycle finance for the Juggler map

Status: laboratory extract, absorbed into Paper A. Date: 31 August 2026.

This is the laboratory writeup of the finance theorem after the
leftover refinements. The publication text is Paper A
([juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md)),
Section 4. This page is not a second manuscript, not Paper B, not
a leftover-itinerary census, and not a halt theorem. It does not claim
that every positive integer reaches 1. Height leftover and residual
floor \(261\) remain laboratory companions, not Paper A theorems.

The compiled Lean is `Problems/Juggler/CycleFinance.lean` and
`Problems/Juggler/CycleHeightFinance.lean`. Dossier:
[juggler_cycle_finance.md](../problems/juggler_cycle_finance.md).
Ledger: `J-cycle-finance-inequality`,
`J-cycle-parity-finance`,
`J-cycle-parity-finance-instance`,
`J-cycle-budget-opt-finance`,
`J-cycle-budget-opt-instance`,
`J-residual-floor-two-hundred-sixty-one`,
`J-residual-floor-two-million`,
`J-cycle-itinerary-length-eighty-four-or-ge-eighty-five`,
`J-cycle-itinerary-length-eighty-four-m-ge-three-or-ge-eighty-five`,
`J-cycle-itinerary-eliahou-leftover`.

## The map

Let \(J\) be the Juggler map
\[
J(n)=\begin{cases}
\lfloor\sqrt n\rfloor,&n\text{ even},\\
\lfloor n^{3/2}\rfloor,&n\text{ odd}.
\end{cases}
\]
A *cycle itinerary* of length \(L\) at \(n\ge 2\) is a parity itinerary
\(w\) with \(J_w(n)=n\). Write \(o\) for the number of odd
letters and \(m\) for the number of odd-runs on a `CycleMin`
rotation (local minima). The itinerary is formally expanding:
\(2^L<3^o\) (`cycle_itinerary_formally_expanding`).

A periodic state never reaches \(1\). Combined with a residual
floor, that is the only totality input used below.

## Theorem

**Finance inequality (EXACT — LEAN VERIFIED,
`cycleMin_finance`).**
On a `CycleMin` start \(n\ge 2\),

\[
n\log n\cdot(3^o-2^L)\;\le\;L\cdot 3^o.
\]

The only analytic input is \(\log(1+u)\le u\), via the dyadic
cell bound \(\log z\le 2\log y+2/y\). The Lean constant is \(1\),
not \(6/5\). The unrolled envelope is `cycleMin_log_envelope`.
Paper A Theorem 4.4. The inv-sum form below is Paper A
Corollary 4.4c and lives in `CycleFinance.lean`.

**Inv-sum form (EXACT — LEAN VERIFIED,
`cycleMin_finance_inv_sum`).**
The same unroll, keeping each cell defect as \(1/x_i\),

\[
(3^o-2^L)\log n\;\le\;3^o\sum_{i=1}^{L}\frac1{x_i}.
\]

**Residual floor (EXACT — LEAN VERIFIED,
`reachesOne_of_lt_two_hundred_sixty_one`).**
Every positive integer strictly below \(261\) reaches \(1\).
Hence every cycle state is at least \(261\). Combined with
\(\log 257>61/11\) (`log_two_hundred_fifty_seven_gt`), one has
\(n\log n>15921/11\) on a `CycleMin`.

**Length leftover (EXACT — LEAN VERIFIED,
`cycle_itinerary_length_eighty_four_or_ge_eighty_five`).**
If a nontrivial cycle itinerary exists at \(n\ge 2\), its period is
\(84\) or at least \(85\). Lengths \(\le 19\) are the census
through `no_cycle_itinerary_length_le_nineteen`. Lengths \(20\)–\(83\)
die by the finance comparison at floors \(257\) and \(261\).
The cheap leftovers \(19\), \(38\), \(57\), and \(76\) are not
Lean leftovers.

**Height leftover (EXACT — LEAN VERIFIED,
`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`).**
If a nontrivial cycle itinerary exists at \(n\ge 2\), then either its
period is \(84\) and some `CycleMin` rotation has at least three
odd-runs, or its period is at least \(85\). Length \(84\) with
at most two odd-runs is impossible at floor \(261\): the inv-sum
form plus the two-level height cap (valleys \(\le 1/n\), first
odds \(\le 1/4217\), later odds \(\le 1/273845\), evens
\(\le 1/n^2\)) is strictly below \(\theta\cdot 61/11\) for
\(o\ge 53\) and \(m\le 2\). Certificates: \(J(261)=4216\),
\(J(4217)=273845\). The wrapper is
`no_cycleMin_length_eighty_four_of_circuit_le_two`.

That is the laboratory leftover. It is not an exclusion of
length \(84\) at \(m\ge 3\).

## Proof of the finance inequality

The only analytic input is \(\log(1+u)\le u\). If
\(z<(y+1)^2\) and \(y,z\ge 1\), then
\[
\log z\le 2\log(y+1)=2\log y+2\log\bigl(1+\tfrac1y\bigr)
\le 2\log y+\tfrac2y
\]
(`log_le_two_log_add`). An even step has \(x<(T(x)+1)^2\), so
\(\log x\le 2\log T(x)+2/T(x)\). An odd step has
\(x^3<(T(x)+1)^2\), so \(3\log x\le 2\log T(x)+2/T(x)\).

On a `CycleMin`, every prefix is non-contracting:
\(2^k\le 3^{o_k}\). Otherwise the power envelope would land
strictly below the cycle minimum. Combined with
\(x_k\ge n\), this gives \(2^k/x_k\le 3^{o_k}/n\).

Unrolling those two facts by induction on the prefix
(`cycleMin_log_envelope`) yields
\[
3^{o_k}\log n\;\le\;2^k\log x_k+\frac{k\cdot 3^{o_k}}{n}.
\]
At a full period, \(x_L=n\) and \(o_L=o\), so
\[
3^o\log n\;\le\;2^L\log n+\frac{L\cdot 3^o}{n}.
\]
Multiplying through by \(n\) is `cycleMin_finance`. \(\blacksquare\)

The inv-sum form is the same induction with each cell defect
kept as \(1/x_{i+1}\) instead of being charged at \(1/n\)
(`cycleMin_log_envelope_inv`).

## Computational companion

The Phase-0 table uses the weaker constant \(6/5\), valid on
states \(\ge 12\). Paper A states the hierarchy explicitly:
Theorem 4.4 is the conceptual sharp inequality; Corollary 4.5
is the convenient statewise bound; Theorem 4.6 certifies the
table with this conservative majorant. The cutoff \(25781\) is
not an artifact of \(6/5\). The identity is:

\[
\theta:=1-\frac{2^L}{3^o}
\;\le\;\frac65\sum_i\frac1{x_i\ln x_i}
\;\le\;\frac65\cdot\frac{L}{n\ln n}.
\]

The \(6/5\) is \(-\ln(1-\delta)\le(6/5)\delta\) on
\([0,1/6]\). At the minimal admissible \(o\), the crude bound
defines \(n_{\max}(L)\). The length-only parity refinement
(**EXACT — HUMAN PROOF**) keeps the same unroll and replaces
the last step \(x_i\ge n\) by the CycleMin classification
\(m\le e=L-o\), evens \(\ge n^2\), internal odds
\(\ge t=\lfloor n^{3/2}\rfloor\):

\[
\sum_i\frac1{x_i\ln x_i}
\;\le\;
\frac{e}{n\ln n}
+\frac{o-e}{t\ln t}
+\frac{e}{2n^2\ln n}.
\]

This is joint-minima finance at the adversarial circuit count
\(m=e\), not a rewriting of \(B(L)=(6/5)L/\theta\). With the
published floor \(N_0=10^6\), the certified parity scan excludes
every \(L\le 25780\) and every \(L\le 10^5\) outside \(141\)
lengths (`exceptions_parity.json`). First survivor \(L=25781\),
\(n_{\max}^{\mathrm{par}}(1054)=788014\),
\(n_{\max}^{\mathrm{par}}(25781)=26254995\). The optimal
uniform coefficient \(c_*=6\ln(6/5)\) does not change that
cutoff. Paper A Theorem 4.6 prints this table.

The crude table at the laboratory floor \(N_0=2\cdot 10^6\)
still excludes every \(L\le 25780\) with \(166\) exceptions:
length \(1054\) dies there by raising the floor
(\(n_{\max}\approx 1.997\cdot 10^6\)), not by the parity sum.
Length \(84\) is the first record convergent that survives the
Lean floor (\(n_{\max}(84)=5599\)).

**Eliahou leftover (EXACT — LEAN VERIFIED implication
`cycle_itinerary_eliahou_leftover`; instance COMPUTATIONALLY
VERIFIED).**
If every length in \([30,10^5)\) outside a named list is already
excluded, then the period is \(84\), or belongs to that list, or
is at least \(10^5\). This is bookkeeping on the length leftover
plus the finance table, not a new inequality. Eliahou packaging
does not use the height leftover: it stays length-only. The
laboratory instance at floor \(2\cdot 10^6\) is the \(166\)-family.

## Human-proof refinements that are not the leftover

Joint-minima finance and the \(6/5\) greedy height packing are
**EXACT — HUMAN PROOF**
([juggler_cycle_m_finance.md](../problems/juggler_cycle_m_finance.md),
[juggler_cycle_position_finance.md](../problems/juggler_cycle_position_finance.md)).
They exclude further \((L,m)\) pairs (every length-\(38\) cycle
at floor \(257\); length \(84\) at \(m=1,2\) already in Lean at
constant \(1\)). The length-only special case \(m=e\) is the
parity table of Paper A Theorem 4.6. Finer run-height packing
does not improve that length-only \(n_{\max}\) at \(o_{\min}\).
Run-type packing
([juggler_cycle_budget_opt.md](../problems/juggler_cycle_budget_opt.md))
is strictly stronger than parity: an \(n\)-circuit cannot start
`OE`, and an `OO`-circuit from \(n\) takes only one even. At
\(N_0=10^6\) it excludes \(42\) of the \(141\) leftovers
(\(56347+1054k\), \(k=0,\ldots,41\)) and leaves \(99\). First
survivor remains \(25781\). Unique visit and the cycle maximum
do not bind. Cyclic run-depth / adjacency does not shrink the
\(99\): two-type is already the relaxed maximum
(`juggler_cycle_run_extremum_leftover_killer`). The \(99\) are
three surplus intermediate families of \(\ln 2/\ln 3\) on the
unimodular basis \((25781,16266)\), \((1054,665)\); packing
cuts only \(F_1\) after \(L=55293\). That organization does
not constrain actual cycles
([juggler_run_survivor_lattice_note.md](juggler_run_survivor_lattice_note.md)).
Paper A prints the parity table as Theorem 4.6 and the run-type
refinement with the lattice as Theorems 4.7--4.8 and
Proposition 4.9.

## Attacks that stop

These were run. None of them changes the leftover.

- Length \(84\) at \(m\ge 3\) at floor \(261\) —
  **REFUTED** (`juggler_l84_m_ge_three_floor_261`).
  Height constant \(1\) RHS \(\approx 0.002193>\theta\approx 0.002086\);
  Lean inv-sum \(S\approx 0.012672>0.011568\). Height first kills
  \(m=3\) at \(273\) and every \(m\) at \(1981\).
- Residual-floor campaigns to \(1981\) (all \(m\)) and \(4756\)
  (global finance) — **PARK**. The hypothesis that \(4756\) is
  the cheapest kill is **REFUTED**
  (`juggler_cycle_finance_l84_floor_4756`).
- Equal-valleys \(n+2\) — **REFUTED** as a leftover-killer.
  Unique visit of the `CycleMin` start on a leftover length is
  first-return (**REPARAMETERIZATION**).
- Second-valley bound \(\ge 281\) — **REFUTED** as a leftover-killer
  (`juggler_second_valley_leftover_killer`). Height-split
  constant \(1\) first kills at \(281\), but Lean inv-sum
  misses even \(261,281,281\). The adversarial triple is
  \(261,281,303\) (\(6/5\) RHS \(\approx 0.002429\); inv-sum
  \(S\approx 0.011868\)). A later `OE` landing at \(263\)
  requires a start valley \(\ge 1687\) and dies. The \(281\)
  landing is `even_iter_lt_succ_pow`.
- Upper cell \((p+1)^{2^r}\) — **REFUTED** as a leftover-killer
  (`juggler_ceiling_finance_leftover_killer`). The landing
  \(p\ge\operatorname{isqrt}^{r}(M_{\min})\) is
  `even_iter_lt_succ_pow` (**REPARAMETERIZATION**). Pigeonhole
  \(k=18\) lands at \(3075\) and would kill \(m=3\); the
  adversarial peak run \(k=24\) lands at \(304\), below both
  proved thresholds (\(6/5\) needs \(659\); inv-sum needs
  \(367\)).
- Baker / Rhin transfer onto \(\lvert 3^o-2^L\rvert\) —
  **REFUTED** as a leftover-killer.
- Near-tight monochrome rigidity — **REFUTED**.
- Christoffel / mechanical-word one-parameter reduction —
  **REFUTED**.
- Cyclic run-type leftover-killer — **CLOSE**
  (`juggler_cycle_run_extremum_leftover_killer`). The `OOE`/`OE`
  packing is already the relaxed finance maximum on the \(99\)
  survivors. Cheap-`OOE` adjacency is `power_bound_word` and does
  not prove \(N_{\mathrm{cheap}}<o-e\).
- Closed peak–valley Fourier leftover-killer — **CLOSE**
  (`juggler_cycle_fourier_leftover_killer`). Parseval plus the
  O/E increment law is the spectral moment \(1/16\), achieved by
  every cyclic wave with \(|\Delta t|\approx t/2\), including both
  the bunched word and the mechanical `OOE`/`OE` necklace. None
  of the \(99\) leftovers dies. Band-limit \(m\le L/12\) fails
  (tail \(\ge 0.05\)).
- Exact pair-level floor-closure leftover-killer — **CLOSE**
  (`juggler_cycle_closure_leftover_killer`). Word-independent
  forward/backward intervals are the exponent envelope
  \(T\le n^{P_L}\). Local OE is the cell \(z^4\le x^3<(z+1)^4\).
  The cycle remainder is `global_defect_identity`. Neither
  \(L=25781\) nor \(L=55293\) dies as a pair.
- Finance-conditioned exact-closure leftover-killer — **CLOSE**
  (`juggler_cycle_conditioned_closure_leftover_killer`). Leftover
  \(\theta\) does not force near-extremal run structure.
  Deepening every `OE` still leaves packed \(>\theta\) at
  \(L=25781\) and \(L=55293\). The residual lose-class is
  exponentially large. The finance-restricted hull is the
  existing envelope.
- Single-point lattice coordinates \((a,b)\) and
  generator-as-word rigidity — **CLOSE**. The \(99\) are a
  unimodular slice of the \(\ln 2/\ln 3\) intermediate lattice;
  \((a,b)\leftrightarrow(L,o)\) is a change of basis, and the
  \(1054\)-block is the already admissible Christoffel /
  extremal insertion
  ([juggler_run_survivor_lattice_note.md](juggler_run_survivor_lattice_note.md)).
- Ordered excursion leftover-killer — **CLOSE**
  (`juggler_cycle_ordered_excursion_leftover_killer`). The
  two-block persistence \((2,2,1)\) at a CycleMin start is the
  composed OOE envelope \(81/64<4/3\). Floor loss is
  \(7\) on \(39244728\). \((2,2,2)\) is realized near \(n\), and
  \((2,2,1)\) becomes legal at scale \(n^{9/8}\). Retaining the
  exact landings \(4447\) versus \(33811\) does not create a
  region \(C_{a,b}\): both sit in \([n^{4/3},n^{3/2})\) just
  below \(n^{729/512}\), with next runs \(2\) and \(1\), and
  two-block signs match \(\mu(a)\mu(b)\). Neither
  \(L=25781\) nor \(L=55293\) dies as a pair.
- Correlated floor-defect leftover-killer — **CLOSE**
  (`juggler_cycle_defect_correlation_leftover_killer`).
  Realized `OE`/`OO` pairs occupy both cheap and finance-maximal
  cell corners. Pair-eps ratio \(0.9999\); pair-finance gap
  \(0\). The non-additive recurrence is `global_defect_append`.
  Neither leftover dies.
- Cross-excursion usable-loss leftover-killer — **CLOSE**
  (`juggler_cycle_loss_persistence_leftover_killer`).
  CycleMin-scale pairs reach \(\max\min(U_0,U_1)=0.9767\) and
  \(\max(U_0+U_1)=1.968\). `OOE` near-top events are positively
  persistent. Finance weighting does not create an
  anti-correlation. Neither leftover dies as a theorem.
- Prefix-weight leftover-killer (\(P\equiv 1\), or optimistic
  later-valley \(P\ge 9/8\)) — **CLOSE**
  (`juggler_cycle_prefix_weight_leftover_killer`). The published
  \(1/(x\log x)\) form already uses the envelope
  \(P\ge\log x/\log n\ge 1\); charging \(P\equiv 1\) is weaker
  and excludes none of the \(141\) leftovers at \(n=10^6+1\).
  Later-valley \(P\ge 9/8\) would drop
  \(81643+1054k\) (\(k=0,\ldots,17\)) but is not a theorem, and
  \(L=25781\) still lives.

## What this theorem is not

- Not `juggler_reaches_one`, not `no_cycle_itinerary_any_length`, and
  not `no_cycle_itinerary_length_eleven`.
- Not a leftover-itinerary census of the length-\(11\) short-gap
  families. Paper A prints Theorem 4.4, the floor-\(10^6\)
  parity leftover (prefix \(25780\), Theorem 4.6), the run-type
  leftover of \(99\) lengths (Theorems 4.7--4.8), and the
  survivor lattice (Proposition 4.9); Lean leftover \(84\) is an
  Appendix A companion.
- Not a second manuscript.

## Literature

The financing-versus-gap template is Simons–de Weger on Collatz
\(m\)-cycles (`simons-de-weger-2005-collatz-m-cycles`). The
Juggler form is independent of that proof. The structural
difference is that floor-power defects are relatively \(O(1/x)\)
in logarithms, so one verified residual floor excludes every
length outside a near-convergent set. The Eliahou leftover shape
(period \(\ge X\), or a named convergent family) is the same
packaging, on a different map.

## Formalization

| Claim | Lean |
|---|---|
| Finance inequality | `cycleMin_finance` |
| Inv-sum form | `cycleMin_finance_inv_sum` |
| Floor \(261\) | `reachesOne_of_lt_two_hundred_sixty_one` |
| \(\log 257>61/11\) | `log_two_hundred_fifty_seven_gt` |
| Census through \(19\) | `no_cycle_itinerary_length_le_nineteen` |
| Length leftover | `cycle_itinerary_length_eighty_four_or_ge_eighty_five` |
| Height leftover | `cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five` |
| Eliahou packaging | `cycle_itinerary_eliahou_leftover` |
| Survivor lattice | `run_survivor_unimodular`, `runSurvivors_length` |

No `sorry`. `Problems.JugglerPaper` imports `CycleFinance` for
Theorem 4.4 and `RunSurvivorLattice` for Proposition 4.9. It does
not import `CycleHeightFinance`. Leftover refinements stop.
