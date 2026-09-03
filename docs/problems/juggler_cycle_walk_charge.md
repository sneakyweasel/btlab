# Juggler coupled exponent-walk charge

Status: **PROMOTE** (transport lemma proved; certified survey
complete — period bound 176251 at floor 26254995; consolidated
into Paper A Section 5 on 1 September 2026; new-floor instance
complete — period bound 478245 at certified floor 162849448,
`J-cycle-period-four-hundred-seventy-eight-thousand`;
third-floor instance complete — period bound 780239 at
certified floor 350000000,
`J-cycle-period-seven-hundred-eighty-thousand`)

Refinement of the Paper A Section 5 state-distribution program
([juggler_cycle_finance.md](juggler_cycle_finance.md)), answering
the coupling question left open by the necklace phase
([juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md)):
a coupling that forbids \(o-e\) independent \(n\)-valleys. Not a
halt theorem, not a no-cycle-of-any-length claim, not a floor
raise, and not a Paper A edit.

## Problem

The length-only parity and run-pack tables price valleys
independently. On a real CycleMin cycle every state is coupled
through one closed exponent walk: with
\(u_k = \log_2(3/2)\cdot\#O_k - \#E_k\), the defect-free upper
envelope (\(\lfloor x^{3/2}\rfloor\le x^{3/2}\),
\(\lfloor\sqrt x\rfloor\le\sqrt x\)) gives \(x_k\le n^{2^{u_k}}\),
and CycleMin forces \(u_k\ge 0\) exactly. Does the exact optimum of
\(\sum_k 1/(x_k\ln x_k)\) over all nonnegative closed walks with
\(o\) up-steps and \(e\) down-steps fall below \(\theta(L)\) at the
certified floor — killing \(L=50508\) without a
\(1.63\cdot 10^8\) campaign?

## Exact statement

**Walk pricing.** At step \(k\) with \(a\) odd letters used,
\(u=(1+\mu)a-k\) with \(\mu=\log_2(3/2)\); the DP over \((k,a)\) is
exact on the lattice (no grid rounding).

**Transport lemma (EXACT — HUMAN PROOF, reduced-base form).**
On a CycleMin cycle with minimum \(n\ge 400\), write
\(\ln x_k\ge w_k\ln n-E_k\). The floor losses give
\(E'\le\tfrac32E+1.05\,x^{-3/2}\) (odd) and
\(E'\le\tfrac12E+1.05\,x^{-1/2}\) (even), using
\(-\ln(1-t)\le 1.05\,t\) on \(t\le 0.05\). Unrolling, the
amplification from injection \(j\) to state \(k\) is exactly
\(w_k/w_{j+1}\); odd injections have \(x_j\ge n\),
\(w_{j+1}\ge\tfrac32\) (\(\le 0.7\,n^{-3/2}\) each), even
injections have \(x_j\ge n^2\) (`cycleMin_even_ge_sq`) and
\(w_{j+1}\ge 1\) (\(\le 1.05/n\) each). Hence \(E_k\le w_k D\) with

\[
D \;=\; \frac{1.05\,e}{n}+\frac{0.7\,o}{n^{3/2}},
\qquad
x_k \;\ge\; \bigl(n\,e^{-D}\bigr)^{w_k}.
\]

The entire transport collapses to running the same exact DP at the
reduced base \(n'=n e^{-D}\): no free parameter remains.

**Certified kill at the target (COMPUTATIONALLY VERIFIED).**
At \(L=50508\), \(o=31867\), floor \(N_0=26254995\):
\(D=7.4566\cdot 10^{-4}\), certified walk RHS
\(6.4844\cdot 10^{-6}<\theta=7.2649\cdot 10^{-6}\), kill margin
\(\mathbf{1.1204}\). Survival would require
\(\theta\le\tfrac65\sum_i 1/(x_i\ln x_i)\) (Theorem 4.4 unroll,
implemented \(6/5\) architecture); the DP maximum at base \(n'\)
upper-bounds the sum over all CycleMin words with \((o,e)\). Same
trust boundary as Theorem 4.6: exact human inequality plus a float
comparison with the standard outward guards.

**Kill at the target (COMPUTATIONALLY VERIFIED numbers; theorem
pending the transport lemma).** At \(L=50508\), \(o=31867\),
floor \(N_0=26254995\) (`J-residual-floor-twenty-six-million`):
\(\theta=7.2649\cdot 10^{-6}\), parity RHS
\(4.9878\cdot 10^{-5}\), walk RHS \(6.4790\cdot 10^{-6}\) at
\(\eta=0\) — improvement \(7.70\) over parity against the required
\(6.87\). Kill margin \(1.121\) at \(\eta=0\), \(1.120\) at the
transport bound \(\eta^*=4.2\cdot 10^{-5}\), \(1.113\) at
\(10\eta^*\), \(1.042\) at \(100\eta^*\). Classification
**WALK_CHARGE_GREEN**.

**Calibration (COMPUTATIONALLY VERIFIED).** At \(L=25781\), floor
\(10^6\): walk RHS \(1.2984\cdot 10^{-4}\), matching the archived
necklace height-walk value \(1.30\cdot 10^{-4}\) to three digits;
margin \(0.196\) — correctly no kill (required \(32.5\), walk gives
\(6.37\)). The 2026 merge-assessment conclusion (constants cannot
kill the seeds at \(10^6\)) is reproduced, not contradicted.

**Structure.** Cheap valleys need excursion exponents
\((3/2)^a/2^r\) near \(1\), forcing \((a,r)\) onto near-convergents
of \(\log_2(3/2)\): the cheapest return is \(O^{12}E^7\)
(19 letters, valley at \(n^{2^{0.0195}}\)); \(O^{29}E^{17}\),
\(O^{41}E^{24}\), \(O^{53}E^{31}\) are the drift-compensating
types. The walk optimum realizes roughly one cheap valley per 19
letters instead of the parity table's one per \(L/e\approx 2.7\).

No cycle of any length — not claimed.

## Current literature

- Length-only parity \(6/5\) table — **COMPUTATIONALLY VERIFIED**
  (`J-cycle-parity-finance-instance`); run-pack Theorems 4.7--4.8
- Certified floor \(26254995\) and period bound \(50507\) —
  **COMPUTATIONALLY VERIFIED** (`J-residual-floor-twenty-six-million`,
  `J-cycle-period-fifty-thousand`)
- Two-type cheap cap \(N_{\mathrm{cheap}}\le 2e-o\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md));
  its open question (full coupling) is what this branch computes
- Valley-coupling excursion table (\(O^{12}E^7\) below \(9/8\),
  \(O^{53}E^{31}\) at \(n^{1.002}\)) — **CLOSE**
  ([juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md));
  leftover-killer refuted at \(25781\)/\(10^6\), consistent with the
  calibration here
- Paper A × Paper B merge — CLOSE (`juggler_cycle_paper_merge`):
  constant-factor refinements cannot kill seeds at \(10^6\); this
  branch targets \(50508\) at \(26254995\) where the requirement is
  \(6.87\), not \(223\)
- Every start reaches 1 — not claimed

Project relationship: **extended** (the Section 5 program's first
quantitative success at a live target).

## Branch budget

```text
Mathematical target     Does the exact optimum of the cyclic
                        exponent-walk charge fall below θ(50508) at
                        the certified floor 26254995?
Novelty hypothesis      The walk DP over (step, odd-count) is exact
                        on the lattice and is the valley coupling
                        named open by the Section-5 PARK; the
                        required factor is now 6.87, not 32.5
Falsifier               DP optimum ≥ θ, or the defect-transport
                        band erases a sub-1.5 kill margin
Existing machinery      o_min_and_theta / EPS_CONST; Lean power
                        envelope; valley-coupling excursion table;
                        necklace cheap cap as calibration
Maximum Phase-0 scope   One probe: exact DP at (50508,31867)
                        n=26254995, calibration (25781,16266) at
                        10^6, kill table for the 19 leftovers,
                        eta-sensitivity band. No Lean, no Paper A
                        edit, no floor raise, no CLI
Promotion criterion     Budget < θ at 50508 with margin surviving
                        the eta band
Stop criterion          Budget ≥ θ, or margin inside the eta band
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a - b\); the map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exponent walk \(u_k=(1+\mu)a-k\), exact lattice DP —
  **COMPUTATIONALLY VERIFIED** (matches brute force through
  \(L=14\))
- Upper envelope \(x_k\le n^{2^{u_k}}\), hence \(u_k\ge 0\) —
  **EXACT — HUMAN PROOF** (defect-free floors)
- Transport lemma \(x_k\ge(ne^{-D})^{w_k}\),
  \(D=1.05e/n+0.7o/n^{3/2}\) — **EXACT — HUMAN PROOF**
  (`deficit_D`; supersedes the earlier numerical \(\eta^*\) band)
- Even-state constraint \(u\ge 1\) before a down-step — automatic
  (\(u\ge 0\) after the unit down-step), consistent with
  `cycleMin_even_ge_sq`
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_charge`
- Artifacts: `data/research/juggler/cycle_walk_charge/summary.json`
  (target + calibration), `survey.json` (19-leftover kill table)
- Tests: `tests/research/juggler_sequence/test_cycle_walk_charge.py`

## Conjectures

`juggler_cycle_walk_charge`: the coupled exponent-walk charge
excludes \(L=50508\) as a CycleMin length at the certified floor
\(26254995\) — **resolved positively** by the transport lemma plus
the certified DP comparison (margin \(1.1204\)); record moved to
`conjectures/proved/`.

## Counterexamples

None against the walk model. The calibration point
\((25781, 10^6)\) is a deliberate non-kill: margin \(0.196\),
reproducing the archived necklace value and the merge-assessment
conclusion.

## Formalization

The human-proof layer is complete: (i) upper envelope \(u\ge 0\)
(defect-free floors); (ii) transport lemma \(E_k\le w_k D\)
(the \(E\)-recursion with amplification \(w_k/w_{j+1}\), even
states \(\ge n^2\) by `cycleMin_even_ge_sq`); (iii) the DP value
as a maximum over the relaxation (any binary word with \(o\) odds,
\(e\) evens, \(u\ge 0\)); (iv) the existing \(6/5\) unroll
interface. Lean packaging of (i)–(ii) is optional future work;
the DP table stays computational, as in Theorem 4.6. No `sorry`.

## Results

Classification **WALK_CHARGE_GREEN**.

- **Certified kill** at \(L=50508\), floor \(26254995\): reduced
  base \(D=7.4566\cdot 10^{-4}\), walk RHS
  \(6.4844\cdot 10^{-6}<\theta=7.2649\cdot 10^{-6}\), margin
  \(1.1204\) — **COMPUTATIONALLY VERIFIED** on the proved lemma
- Sensitivity (superseded by the lemma): margins
  \(1.121/1.120/1.113/1.042\) at
  \(\eta\in\{0,\eta^*,10\eta^*,100\eta^*\}\),
  \(\eta^*=4.2\cdot 10^{-5}\)
- Improvement over parity \(7.70\) (required \(6.87\)); the
  necklace phase's best at \(25781\) was \(6.37\) against a
  required \(32.5\) — the mechanism did not change, the target did
- Calibration \(1.2984\cdot 10^{-4}\) vs archived \(1.30\cdot 10^{-4}\)
- DP is exact on the lattice and matches brute force on all tested
  tiny lengths
- **Certified survey (COMPUTATIONALLY VERIFIED,
  `J-cyclemin-walk-charge-instance`).** All 19 parity leftovers
  through \(2\cdot 10^5\) DP-priced at the certified floor
  \(26254995\): 18 killed (margins 1.1204 at 50508; 1.1195 at
  101016; 1.1187 at 151524; up to 7.69 at the parity-marginal
  lengths), sole walk survivor \(L=176251\) (margin 0.159,
  required 48). Combined parity + walk contiguous prefix
  **176250**: any nontrivial cycle has period \(\ge 176251\) —
  a \(3.49\times\) extension of `J-cycle-period-fifty-thousand`
  with no new floor verification. `survey.json`, SHA-256 of the
  walk-alive list `225d76ad…8942ec`.
- **New-floor instance (1 Sep 2026, completing the parked
  extension).** The descent floor \(162849448>
  n_{\max}^{\mathrm{par}}(50508)\) is certified
  (`J-residual-floor-one-hundred-sixty-two-million`: 547 chunks,
  zero failures, peak \(463362780\) bits; the interrupted
  campaigns all stalled on seed \(56261531\), \(351395163\)
  bits). Parity there kills the F2 cluster and leaves \(25\)
  leftovers through \(6\cdot 10^5\)
  (`new_floor_parity_leftovers.json`); the walk kills all \(15\)
  below the blocker (margins \(1.198\) at \(176251\) and
  \(352502\) up to \(8.437\) at \(202032\);
  `new_floor_kills/`, SHA-256 of the 15 kill records
  `148180cb…5aeda0`). Combined contiguous prefix **478244**: any
  nontrivial cycle has period \(\ge 478245\)
  (`J-cycle-period-four-hundred-seventy-eight-thousand`), a
  \(2.71\times\) extension. Sole survivor
  \(478245=176251+301994\) (\(k=1\) semiconvergent fan):
  required improvement \(19.46\), walk supplies \(\approx 7.7\),
  direct DP non-kill margin \(0.4334\)
  (`new_floor_kills/L478245.json`, GPU fp64 DP cross-checked
  against the stored CPU record at \(176251\) to
  \(3.6\cdot 10^{-14}\)), DK break-even floor \(3.48\cdot 10^8\)
  — Diophantine, not computational.
- **Third-floor instance (3 Sep 2026, executing the parked
  \(3.48\cdot 10^8\) campaign).** The descent floor
  \(350000000>n^*(478245)\) is certified
  (`J-residual-floor-three-hundred-fifty-million`: 749 chunks,
  two bit-cap seeds resolved at \(3\cdot 10^9\), peak
  \(1493770145\) bits). Parity there leaves \(17\) leftovers
  through \(8\cdot 10^5\)
  (`N350000000_parity_leftovers.json`); the five leftovers
  below \(478245\) carry by monotonicity, and the walk kills
  all \(10\) in \([478245,755512]\) (margins \(1.00555\) at
  \(478245\) up to \(7.824\) at \(504026\);
  `N350000000_kills/`, SHA-256 of the 10 kill records
  `d16ccfed…b854ab`). Combined contiguous prefix **780238**:
  any nontrivial cycle has period \(\ge 780239\)
  (`J-cycle-period-seven-hundred-eighty-thousand`), a
  \(1.63\times\) extension. Sole survivor
  \(780239=176251+2\cdot 301994\) (\(k=2\) semiconvergent fan):
  required improvement \(14.46\), walk margin \(0.6049\)
  (`N350000000_kills/L780239.json`), DK break-even floor
  \(5.54\cdot 10^8\) — Diophantine, not computational.
- GPU port performance (repository record; the paper now cites
  this dossier instead of printing figures):
  `cycle_walk_charge_gpu` (CuPy fp64 raw kernel) reproduces the
  stored CPU kill records to relative error below \(10^{-13}\)
  at roughly \(450\times\) speed; the full second-floor kill
  table recomputes in minutes on one consumer GPU.

## Open questions

- The blocker \(L=780239\) needs floor \(\approx 5.54\cdot 10^8\)
  (DK break-even, `J-cyclemin-walk-competition-law`) before the
  walk can kill it; further \(N_0\) campaigns are PARK. The
  next *seed* \(16785921\) waits at \(4.54\cdot 10^{11}\). The
  asymptotic frontier stays the fan-minimum reduction
  (`juggler_walk_fan_minimum_law`)
- Whether the walk charge plus run-pack composition tightens the
  thin \(1.12\) margin
- Lean packaging of the envelope is complete as of 1 Sep 2026:
  transport (`WalkTransport.lean`), hug charge maximality
  (`WalkChargeMax.lean`), defect finance and the kill template
  (`DefectFinance.lean`), DK block hypotheses and the rotation
  average Laplace bound (`OstrowskiSandwich.lean`,
  `RotationAverage.lean`), on top of the itinerary identity and
  quotient arithmetic (`WalkChargeItineraries.lean`,
  `OstrowskiSandwich.lean`)
- **Kill-table numerics in Lean: PARK (1 Sep 2026,
  certificate-size obstruction).** Making the 15 per-length kill
  evaluations Lean-checked rational arithmetic fails Phase-0
  triage: the tightest margins are \(1.198\) (\(\le 20\%\) total
  headroom), each evaluation sums \(1.8\)–\(4.5\cdot 10^5\)
  transcendental terms \(g(\nu,W_k)\) with \(W_k\nu\in[17,52]\),
  and the provable rational bound
  \(e^x\ge(1+1/m)^{\lfloor mx\rfloor}\) needs \(m\approx 10^3\)
  for margin-compatible precision — one \(\sim 150{,}000\)-digit
  rational power *per term*, far beyond any kernel or
  `native_decide` budget (the float DP already takes
  \(10^3\)–\(10^4\) s per length). The exact weights
  \(3^{a_k}/2^k\) are themselves \(\tfrac13\)-million-bit ratios;
  compressing them certifiably is the PARKED DK route. Positive
  side-finding: `hug_charge_maximal` (Lean) proves the hug itinerary
  dominates every admissible walk, so a future certified
  evaluation needs only the straight hug-profile sum — the DP
  layer of the kill table is already subsumed by a Lean theorem.

## Decision

**PROMOTE.** The Phase-0 promotion criterion is met, the transport
lemma is proved in reduced-base form, and the certified comparison
kills \(L=50508\) at the laboratory floor with margin \(1.1204\).
The certified survey fixed the combined contiguous cutoff at
\(176250\): period \(\ge 176251\)
(`J-cyclemin-walk-charge-instance`); the completed second-floor
instance raised it to \(478244\): period \(\ge 478245\)
(`J-cycle-period-four-hundred-seventy-eight-thousand`); the
third-floor instance raised it to \(780238\): period
\(\ge 780239\)
(`J-cycle-period-seven-hundred-eighty-thousand`). Ledger
rows `J-cyclemin-walk-transport` (the lemma),
`J-cyclemin-walk-charge-instance` (the first kill table),
`J-cycle-period-four-hundred-seventy-eight-thousand` (the
second-floor instance), and
`J-cycle-period-seven-hundred-eighty-thousand` (the
third-floor instance) are in. Further floors are PARK.

## Publication assessment

Published. The transport lemma is exact
(`J-cyclemin-walk-transport`, **EXACT — HUMAN PROOF**) and the
certified survey is the period bound \(176251\)
(`J-cyclemin-walk-charge-instance`, **COMPUTATIONALLY
VERIFIED**). The 1 September 2026 consolidation absorbed the
walk-charge program into Paper A Section 5
([juggler_finite_dynamics_note.md](../theory/juggler_finite_dynamics_note.md)):
transport is Theorem 5.3, the hug adversary Theorem 5.4, the
itinerary identity Lemma 5.6, the DK/Ostrowski envelope Theorem 5.7,
the window theorem Theorem 5.8, and the kill table / period
bound Theorem 5.9; since the same-day second-floor pass the
paper also prints Corollary 5.10 (floor \(162849448\), period
\(\ge 478245\), the \(478245\) fan blocker, and the Appendix B
hashes for that certificate and the 15-kill table) and
Corollary 5.11 (floor \(350000000\), period \(\ge 780239\),
the \(780239\) fan blocker, and the Appendix B hashes for the
third-floor certificate and the 10-kill table, plus the
GPU reproducibility remark). The discrete word layer and the
quotient arithmetic are Lean (`WalkChargeItineraries.lean`,
`OstrowskiSandwich.lean`). The first length-only charge that
kills a survivor-lattice seed below its parity ceiling.
