# Juggler: the Wu-Wang instance of the floor-free gap transfer

Status: **PROMOTE** (the sharpened reduction, the period lower bound, and
the closure threshold are stated and Lean-verified as conditionals).

Not a halt theorem, not a floor raise, not a kill, not a reopen of the
REFUTED Baker/Rhin transfer at floors
([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)), and not a
reopen of the CLOSE laboratory kill past 780239
([juggler_cycle_diophantine_survivors.md](juggler_cycle_diophantine_survivors.md)).
Nothing new is excluded. What changes is the size of the target.

## Problem

Paper A Corollary 4.11 substitutes \(\(a,b,c\)=\(0,-L,o\)\) into Rhin's
effective measure and reports
\(n\log n\le 915\,L^{14.3}\). The laboratory already imports a sharper
measure for a different purpose:
[juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md)
cites Wu-Wang 2014 and uses it only to cap fan widths. Does that measure
apply to Corollary 4.11's own substitution, and if so what does the
sharpened reduction change?

## Exact statement

Write \(\Lambda=o\log 3-L\log 2\) for a cycle itinerary of length \(L\)
with \(o\) odd letters based at a cycle minimum \(n\ge 2\).

**Power-budget gap transfer (EXACT — LEAN VERIFIED,
`cycleMin_length_of_gap_power`).** For \(0<C\le 1\) and \(p\ge 0\), if
\(C\,L^{-p}\le\Lambda\) then
\[
n\log n\ \le\ \frac2C\,L^{p+1}.
\]
The proof is `cycleMin_length_of_gap` at \(\varepsilon=C L^{-p}\); the
transcendence input is a hypothesis, exactly as Rhin is in
`GapTransfer.lean`.

**Wu-Wang instance (EXACT — HUMAN PROOF; Wu-Wang is classical).**
Wu-Wang give, for every \(\varepsilon>0\) and all large
\(H=\max(\lvert b\rvert,\lvert c\rvert)\),
\(\lvert a+b\log 2+c\log 3\rvert\ge H^{-4.1163051-\varepsilon}\)
(`wu-wang-2014-irrationality-measure-log3`). Corollary 4.11's
substitution has \(a=0\), \(H=\max(L,o)=L\), so
\(\Lambda\ge C_\varepsilon L^{-4.1163051-\varepsilon}\) and
\[
n\log n\ \ll_\varepsilon\ L^{5.1163051+\varepsilon}
\]
against the printed \(L^{14.3}\). Lean form
`cycleMin_length_of_wuWang`.

**Period lower bound (EXACT — LEAN VERIFIED, `cycleMin_period_ge`).**
The same inequality read the other way:
\[
L\ \ge\ \Bigl(\tfrac{C}{2}\,n\log n\Bigr)^{1/(p+1)} ,
\]
floor-free. The exponent in \(n\) rises from \(1/14.3=0.0699\) to
\(1/5.1163051=0.1954\). This is the only proved statement in which a
cycle's period grows with its minimum; the descent floor is a constant.
Wu-Wang form `cycleMin_period_ge_wuWang`.

**Closure threshold (EXACT — LEAN VERIFIED,
`no_cycleMin_of_gap_and_minimum`).** If the budget holds on every
nontrivial cycle and cycle minima satisfy the matching lower bound
\(n\log n>\frac2C L^{p+1}\), then every cycle word based at a minimum
\(n\ge 2\) is empty. Neither hypothesis is proved. At
\(p=4.1163051\) the required lower bound is \(n\gg L^{5.1163051}\); at
\(p=13.3\) it was \(n\gg L^{14.3}\). Dirichlet gives \(p\ge 1\) for
every irrational, so \(n\gg L^{2}\) is a hard floor no improvement of
the measure can go below.

**What is not claimed.** No cycle of any length. No new exclusion of any
length. No raise of \(N_0\). No bound on \(\psi_F\). No proof of either
hypothesis of the closure threshold.

## Current literature

- Wu-Wang effective measure
  \(\lvert a+b\log2+c\log3\rvert\ge H^{-4.1163051-\varepsilon}\) —
  **KNOWN** (`wu-wang-2014-irrationality-measure-log3`). Project
  relationship: **extended** — the laboratory already used the \(p=0\)
  corollary as a fan-width cap
  ([juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md));
  this branch carries the same measure back to Corollary 4.11's own
  substitution, which is a different consequence.
- Bondareva-Luchin-Salikhov 2018 sharpen the exponent to
  \(4.116201\) — **KNOWN**. In the noise here (\(10^{-4}\) on the length
  exponent); do not open it as a branch.
- Rhin's effective two-logarithm measure through Simons-de Weger
  Lemma 12 — **KNOWN** (`rhin-1987-pade-irrationality`,
  `simons-de-weger-2005-collatz-m-cycles`). Stays the *effective*
  companion: Wu-Wang's \(C_\varepsilon\) is implied, Rhin's
  \(e^{-6.1256}\) is printed.
- Paper A Theorem 4.10 / Corollary 4.11 and the gap-transfer Lean layer
  — **EXACT — LEAN VERIFIED** (`J-cyclemin-gap-transfer`,
  `J-cyclemin-short-cycle-rhin`)
  ([juggler_cycle_mechanical_window.md](juggler_cycle_mechanical_window.md)).
- Baker/Rhin/Simons-de Weger transfer *at floors* — **REFUTED**
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)). Untouched:
  that refutation is about competing with the exact finance gap at a
  fixed floor, and this branch competes with nothing.
- Laboratory kill of the near-convergents past \(780239\) — **CLOSE**
  ([juggler_cycle_diophantine_survivors.md](juggler_cycle_diophantine_survivors.md)).
  Untouched: the family leftover is the CF-quotient question, and
  Wu-Wang does not give \(a_{j+1}=O(1)\).
- Boundedness of the dangerous-position CF quotients of
  \(\log2/\log3\) — **OPEN**.

## Branch budget

```text
Target                  Does Wu-Wang apply to Corollary 4.11's own
                        substitution (a,b,c) = (0,-L,o), and what does
                        the sharpened exponent change?
Novelty hypothesis      The laboratory imports Wu-Wang only as a fan-width
                        cap and still runs Corollary 4.11 on Rhin. If the
                        same measure applies to the corollary's own linear
                        form, the floor-free reduction and the closure
                        target both improve by a factor 2.8 in the
                        exponent, for the price of a citation.
Falsifier               Wu-Wang does not cover a = 0, or covers it with a
                        worse effective exponent than Rhin on the cycle
                        height range, or the sharpened bound excludes a
                        length the finance table keeps (which would make
                        this a kill and put it behind the REFUTED wall).
Already killed by?      No. The Diophantine wall in negative_knowledge
                        kills (i) Baker/Rhin/SdW as a *floor-level kill*
                        competing with the exact gap, (ii) the laboratory
                        kill of the near-convergents, (iii) inhomogeneous
                        Wu-Wang with a nonzero third coefficient. This is
                        none of the three: it is the floor-free complement
                        that negative_knowledge itself records as "Complement,
                        not a kill", at a better exponent. It also satisfies
                        the standing prohibition of
                        juggler_cycle_method_ceilings -- "do not open a
                        direction whose kill criterion is a function of the
                        surplus": there is no kill criterion here, and the
                        statement is a period bound in n, which is measured
                        by the Diophantine exponent and not by theta.
Existing machinery      cycleMin_gap_transfer, cycleMin_length_of_gap,
                        cycleMin_length_of_rhin; paper_a_audit
                        (o_min, n_max, convergents, survivor_exponent);
                        the Wu-Wang literature entry.
Maximum Phase-0 scope   One Lean module stating the transfer parametrically
                        in p plus the three consequences, one probe pricing
                        the swap, one dossier, ledger rows. No floor, no
                        GPU, no manuscript edit, no Paper A/B/C theorem
                        change, no new conjecture.
Promotion criterion     The substitution is legitimate, the exponent
                        improves, the closure target acquires a number,
                        and nothing is killed.
Stop criterion          If the swap either kills a length or fails to
                        apply, CLOSE and record it behind the Diophantine
                        wall.
```

## Balanced-ternary formulation

None required. The objects are the linear form \(o\log3-L\log2\), the
finance inequality, and the continued fraction of \(\log2/\log3\).

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- Power-budget transfer \(n\log n\le (2/C)L^{p+1}\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_length_of_gap_power`)
- Period lower bound \(L\ge (Cn\log n/2)^{1/(p+1)}\), floor-free —
  **EXACT — LEAN VERIFIED** (`cycleMin_period_ge`)
- Closure threshold under a matching minimum lower bound —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_of_gap_and_minimum`)
- Wu-Wang instance \(p=4.1163051\), length exponent \(5.1163051\) —
  **EXACT — HUMAN PROOF** (Wu-Wang classical; \(C_\varepsilon\) implied)
- Dirichlet hard floor \(p\ge 1\), so the closure target never falls
  below \(L^2\) — **EXACT — HUMAN PROOF**
- Every finance survivor stays inside the sharpened allowance —
  **COMPUTATIONALLY VERIFIED** (`survivor_band`)
- Certified quotients sit at most \(1.9\cdot10^{-5}\) of the Wu-Wang cap
  — **COMPUTATIONALLY VERIFIED** (`quotient_cap_consistency`)
- Section 6.2's \(n\approx L^{1.7}\) is \(n\log n\asymp L^2\) at the
  tested scale, not an exponent below two —
  **COMPUTATIONALLY VERIFIED** (`survivor_band`)
- No cycle of any length — not claimed
- A proof of either closure hypothesis — not claimed

## Experiments

`python -m research.juggler_sequence.cycle_wuwang_reduction`, writing
`data/research/juggler/cycle_finance/wuwang_reduction.json`. Schema:
`exponents` (one row per Diophantine input: \(p\), length exponent,
period exponent in \(n\), forced period at \(N_0\), whether the constant
is effective), `checks`, `survivor_band`, `quotient_cap`,
`closure_threshold`. No GPU, no scan, no floor.

## Conjectures

None new. `juggler_walk_fan_minimum_law` is **PROVED** (20 September
2026, exact form) and is
untouched: Wu-Wang caps the fan width, not the quotients themselves.

## Counterexamples

None. The anti-overclaim witnesses are the five finance survivors
\(25781,50508,176251,478245,780239\), every one of which satisfies the
sharpened bound with room to spare, and the forced period at
\(N_0=3.5\cdot10^8\): \(4\) with Rhin, \(74\) with Wu-Wang, \(58676\)
even at the Dirichlet floor \(p=1\) — all far below the table's
\(780239\). No improvement of the Diophantine input makes the floor-free
route compete with the finance table at this floor.

## Formalization

`formal/Problems/Juggler/GapTransferWW.lean`, registered in `LAYERS` and
imported by `formal/Problems/Juggler.lean`. No `sorry`, no `admit`, no
`axiom`. Declarations: `gapBudget`, `gapBudget_pos`, `gapBudget_le_one`,
`cycleMin_length_of_gap_power`, `cycleMin_period_ge`,
`no_cycleMin_of_gap_and_minimum`, `cycleMin_length_of_wuWang`,
`cycleMin_period_ge_wuWang`. Compiles with `lake env lean`; the whole
`Problems.Juggler` target builds.

Deliberately **not** added to `PAPER_MODULES` or
`formal/Problems/JugglerPaper.lean`: Paper A is deposited
([doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453))
and its abstract prints the \(14.3\) bound. That record is externally
cited — OEIS A007320 and A094683 both carry a LINKS entry to it — so the
sharpened exponent is a laboratory result standing beside the deposited
manuscript, not inside it. Any propagation into Corollary 4.11's printed
text is a Zenodo new-version operation
(`juggler_review/zenodo_paper_a/AFTER_ZENODO.md`), not a local rebuild,
and is a separate decision.

## Results

Classification **GAP_TRANSFER_SHARPENED**.

| input | \(p\) | \(n\log n\le\) | period in \(n\) | forced \(L\) at \(N_0\) |
|---|---|---|---|---|
| Rhin (printed, effective) | \(13.3\) | \(915\,L^{14.3}\) | \(n^{0.0699}\) | \(4\) |
| Wu-Wang (asymptotic) | \(4.1163051\) | \(\ll_\varepsilon L^{5.1163051+\varepsilon}\) | \(n^{0.1954}\) | \(74\) |
| BLS 2018 | \(4.116201\) | same to \(10^{-4}\) | \(n^{0.1954}\) | \(74\) |
| Dirichlet floor | \(1\) | \(L^{2}\) | \(n^{0.5}\) | \(58676\) |

- The swap is legitimate: Corollary 4.11's substitution has \(a=0\) and
  \(H=L\), which is the shape Wu-Wang bounds. Factor \(2.795\) in the
  exponent.
- The closure threshold acquires a number. The standing reopen condition
  of [juggler_cycle_method_ceilings.md](juggler_cycle_method_ceilings.md)
  — "a lower bound on the cycle minimum in terms of the period" — is
  \(n\gg L^{5.1163051}\) unconditionally, and never less than
  \(n\gg L^{2}\) under any measure.
- Section 6.2's \(n\approx L^{1.7}\) is corrected: \(n\log n/L^2\) lies
  in \([0.164,1.207]\) across all five survivors, so the survivors sit at
  \(L^2/\log n\) and the exponent \(0.59\) is the logarithm, not a gap
  below two. The honest variable is \(q_{k+1}/q_k\), which is exactly
  the unbounded quantity the near-convergents leftover exports.
- Nothing is killed. Every survivor is inside the allowance; the largest
  certified quotient sits at \(1.9\cdot10^{-5}\) of the Wu-Wang cap; and
  even a perfect measure forces only \(58676\) at the certified floor
  against the table's \(780239\). The floor-free route cannot compete
  with finance at any floor the laboratory owns, which is the recorded
  reason the floor-level Baker transfer is REFUTED and is unchanged.

## Open questions

The two hypotheses of the closure threshold, neither proved:

1. A lower bound \(n\gg L^{5.1163051}\) on cycle minima. No mechanism is
   known; counting the \(L\) distinct states gives no window
   ([juggler_cycle_method_ceilings.md](juggler_cycle_method_ceilings.md)).
   This branch does not supply one and does not open a successor.
2. Whether the dangerous-position partial quotients of \(\log2/\log3\)
   are unbounded — **OPEN**, exported as the near-convergents leftover
   ([juggler_near_convergent_diophantine_note.md](../theory/juggler_near_convergent_diophantine_note.md)).

Do not reopen a kill, do not raise \(N_0\), and do not import a further
sharpening of the same polynomial shape as a new branch.

## Decision

**PROMOTE.** The substitution is legitimate, the exponent improves by a
factor \(2.795\), the floor-free period lower bound rises from
\(n^{0.0699}\) to \(n^{0.1954}\), and the standing reopen condition
acquires the number it never had — with a Dirichlet floor showing that
\(L^2\) is the best any Diophantine input could ever ask for. The
sharpening kills nothing, so it sits on the complement side of the
Diophantine wall, not behind it. Best next question: none in this branch.
The two open questions above are already owned elsewhere.

## Publication assessment

Status: `STRUCTURAL`. A sharpened instance and a re-reading of an
existing theorem, plus one correction to Paper A Section 6.2's exponent
prose. Belongs in a Paper A revision as an improved Corollary 4.11 with
Rhin retained as the effective companion, should a new Zenodo version
ever be cut. Not a fourth review object, not a theorem of its own, and
not a halt theorem.
