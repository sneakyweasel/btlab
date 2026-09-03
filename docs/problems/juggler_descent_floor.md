# Juggler verified descent floor versus period cutoff

Status: **THEOREM** (computational instance of Paper A Theorem 4.6)

Writeup:
[juggler_descent_floor_note.md](../theory/juggler_descent_floor_note.md).
Parent inequality:
[juggler_cycle_finance.md](juggler_cycle_finance.md).

Standalone application phase on the **cycle half** of the Juggler
map. It is not a halt theorem, not an escape statement, not a
leftover-itinerary census, and not a claim that a larger finite search
found no cycles.

The published Theorem 4.6 instance uses a verified descent floor
\(N_0=10^6\) and the implemented length-only \(6/5\) parity table
to exclude every period \(L\le 25780\). This phase asks only:

> How much stronger a Theorem 4.6 cutoff does each extra order of
> magnitude of verified \(N_0\) buy?

## Problem

The finance argument converts a verified floor into a period
lower bound. Raising \(N_0\) is not automatically a stronger
theorem: leftovers are near-convergents of \(\ln 2/\ln 3\), and
the cutoff jumps only when \(N_0\) crosses \(n_{\max}(L)\) of
the current first survivor.

## Exact statement

**Sensitivity (COMPUTATIONALLY VERIFIED, implemented
`parity_scan` / `parity_excludes`).**
Let \(L_{\max}(N_0)\) be the contiguous prefix of the published
parity-\(6/5\) table (Paper A Theorem 4.6 architecture): the
largest \(L\) such that every length \(1,\ldots,L\) is
`certified_exclude` at floor \(N_0\). Then, on the implemented
padded comparison, through \(L\le 2\cdot 10^5\):

| \(N_0\) | \(L_{\max}\) | first survivor | leftovers |
|--------:|-------------:|---------------:|----------:|
| \(10^6\) | \(25780\) | \(25781\) | \(141\) through \(10^5\) |
| \(10^7\) | \(25780\) | \(25781\) | \(48\) through \(2\cdot 10^5\) |
| \(26254995\) | \(50507\) | \(50508\) | \(19\) through \(2\cdot 10^5\) |
| \(10^8\) | \(50507\) | \(50508\) | \(4\) through \(2\cdot 10^5\) |
| \(162848325\) | \(101015\) | \(101016\) | \(3\) |
| \(10^9\) | \(176250\) | \(176251\) | \(1\) |

Implemented spotlight \(n_{\max}\) (parity \(6/5\), padded):

- \(n_{\max}(25781)=26254995\)
- \(n_{\max}(50508)=162848325\)
- \(n_{\max}(101016)=162848886\)
- \(n_{\max}(176251)=1044093214\)

The \(10^7\) and \(10^8\) decades do not move the Theorem 4.6
cutoff. The cheapest floor that raises the cutoff is exactly
\(n_{\max}(25781)\). This is numerical evaluation of the existing
padded comparison, not a new inequality.

**Period bound at the new floor (COMPUTATIONALLY VERIFIED,
`J-cycle-period-fifty-thousand`).**
The certified first-passage run is complete
(`J-residual-floor-twenty-six-million`): every
\(2\le n\le 26254995\) reaches \(1\). Hence no nontrivial
Juggler cycle has length at most \(50507\). First survivor
\(L=50508\). Not a termination proof.

No cycle of any length — not claimed.

## Current literature

- Paper A Theorem 4.6 at \(N_0=10^6\) — **COMPUTATIONALLY
  VERIFIED** (`J-cycle-parity-finance-instance`)
- Laboratory floor \(2\cdot 10^6\) — **COMPUTATIONALLY
  VERIFIED** (`J-residual-floor-two-million`); same parity
  prefix \(25780\)
- Weisstein / OEIS A007320 first-passage through \(10^6\) —
  **known**; this phase recomputes a larger floor by the same
  descent induction
- Run-type packing (Theorems 4.7--4.8) — does **not** move
  \(L=25781\) at the published floor
- Every start reaches 1 — not claimed

Project relationship: **extended** (new computational instance
of an existing theorem).

## Branch budget

```text
Mathematical target     What is L_max(N0) for the implemented
                        Theorem 4.6 architecture, and what is
                        the cheapest N0 that raises 25780?
Novelty hypothesis      Decade-by-decade verification is not
                        monotone in theorem strength; the first
                        leftover n_max is the only cheap jump
Falsifier               L_max(N0) stays 25780 past every
                        feasible floor, or 10^7 already raises it
Existing machinery      parity_scan, budget_scan, verify_floor,
                        SCIENCE_FLOOR=68e6, BIT_CAP (raised to
                        128e6 after an 82e6-bit peak)
Maximum Phase-0 scope   Exact N0 |-> L_max table; bottleneck
                        note; one certified run at the cheapest
                        useful N0. No new Lean, no paper rewrite
Promotion criterion     A reproducible L_max table and a
                        stronger Theorem 4.6 instance, or a
                        proof that further N0 is worthless
Stop criterion          Next useful N0 is a later convergent
                        whose cost exceeds the last jump's
                        theorem gain, or finance is the limiter
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(N_0\mapsto L_{\max}(N_0)\) on the implemented parity \(6/5\)
  table — **COMPUTATIONALLY VERIFIED** (this dossier)
- First-passage descent induction — **COMPUTATIONALLY
  VERIFIED** at the chosen floor; **KNOWN** as a method
- Run-pack \(n_{\max}\) — **COMPUTATIONALLY VERIFIED**
  diagnostic; does not change the first jump
- Constant-\(1\) parity \(n_{\max}(25781)=22102111\) —
  **COMPUTATIONALLY VERIFIED** diagnostic; the published table
  keeps \(6/5\)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_floor_sensitivity`
- Records: [juggler_descent_floor.md](../research/juggler_descent_floor.md),
  `data/research/juggler/cycle_finance/floor_sensitivity/`
- Certificate: `data/research/juggler/cycle_finance/floor_verify/`
- Tests: `tests/research/juggler_sequence/test_cycle_floor_sensitivity.py`

Science window: hypothetical floors
\(10^6,10^7,26254995,6.8\cdot 10^7,10^8,10^9\) on
\(L\le 2\cdot 10^5\); one exact first-passage run at
\(N_0=26254995\) with bit cap \(128\cdot 10^6\), plus exact
resolution of the three bit-cap seeds at \(512\cdot 10^6\)
(`cycle_floor_hard_seeds`). No CLI. No new Lean.

## Conjectures

None opened.

## Counterexamples

The hypothesis that \(N_0=10^7\) or \(N_0=10^8\) raises the
published cutoff is **REFUTED** by the implemented table:
both keep first survivor \(25781\) and \(50508\) respectively.

The hypothesis that the previous \(80\)M-bit cap is enough
for a \(68\)M science floor is **REFUTED** by the unfinished
progress log (`max_bits=82265352`, two bit-cap failures).

## Formalization

None. The inequality is already `cycleMin_finance`. This phase
is a computational instance and a sensitivity table. No `sorry`.
Not a halt theorem.

## Results

Classification **DESCENT_FLOOR_GREEN** before the certified
run, then the post-run decision in the writeup.

- **Sensitivity table** — **COMPUTATIONALLY VERIFIED** on the
  implemented padded parity / run-pack / crude comparisons.
  Separated from the exact Lean inequality (constant \(1\))
  and from heuristic cost estimates.
- **Cheapest useful floor** — \(N_0=26254995=n_{\max}^{\mathrm{par}}(25781)\).
  Theorem 4.6 cutoff becomes \(50507\). Gain \(+24727\).
- **Worthless decades** — \(10^7\) and \(10^8\) do not move
  \(L_{\max}\).
- **Next structural jump** — \(N_0\ge 162849448\) kills the
  \(50508\)-cluster \(\{50508,101016,151524\}\) and raises
  the cutoff to \(176250\). \(N_0\ge 1044093214\) is needed
  for \(176251\).
- **Verifier** — exact integer `isqrt`; odds only; embarrassingly
  parallel; no memoization gain (already stop at \(x<n\));
  bottleneck is rare million-bit intermediates, not the
  per-start step count. Bit cap raised to \(128\cdot 10^6\).
- **Certified run** — \(N_0=26254995\) complete
  (`J-residual-floor-twenty-six-million`): \(13127497\) odd
  starts, \(106\) contiguous chunks, three bit-cap seeds
  \(7110201,13184021,13782577\) resolved exactly at
  \(512\cdot 10^6\) bits (largest intermediate \(298912128\)
  bits at \(7110201\); max first passage \(325\) at
  \(15909091\)); all three independently re-walked with
  identical step counts, peaks, and landings. Period bound:
  **no nontrivial cycle of length \(\le 50507\)**
  (`J-cycle-period-fifty-thousand`); \(19\) parity leftovers
  through \(2\cdot 10^5\).
- **Second certified run** — \(N_0=162849448\) complete
  (`J-residual-floor-one-hundred-sixty-two-million`, 1 Sep
  2026): extension segment from \(26254996\), \(68297226\) odd
  starts over \(547\) contiguous chunks, **zero** step-cap,
  bit-cap, or other failures; max first passage \(433\) at
  \(78641579\); largest intermediate \(463362780\) bits at
  \(92502777\); the chunk \([56254997,56504996]\) holds the
  campaign's hardest orbit (seed \(56261531\), \(351395163\)
  bits — the two interrupted campaigns both stalled on it; a
  23-worker attempt died of memory exhaustion at \(99.6\%\), the
  4-worker retry finished it). Parity at this floor kills the
  \(50508\)-cluster and leaves \(25\) leftovers through
  \(6\cdot 10^5\); the walk charge kills the \(15\) below
  \(478245\), so the combined period bound is **no nontrivial
  cycle of length \(\le 478244\)**
  (`J-cycle-period-four-hundred-seventy-eight-thousand`).
- **Third certified run** — \(N_0=350000000\) complete
  (`J-residual-floor-three-hundred-fifty-million`, 3 Sep
  2026): extension segment from \(162849449\), \(93575276\) odd
  starts over \(749\) contiguous chunks; two bit-cap seeds
  \(172376627\) and \(240154767\) resolved exactly at a
  \(3\cdot 10^9\)-bit cap (largest intermediate \(1493770145\)
  bits at \(172376627\); \(240154767\) peaked at \(1096792314\)
  bits); max first passage \(466\) at \(198424189\); zero
  unresolved failures. The floor sits above the DK break-even
  \(n^*(478245)=348306663.43\). Combined with the walk charge
  the period bound is **no nontrivial cycle of length
  \(\le 780238\)**
  (`J-cycle-period-seven-hundred-eighty-thousand`).

## Open questions

- Whether a stronger length-only charge than parity \(6/5\)
  (the Section 5 state-distribution program) can kill \(50508\)
  without a \(1.6\cdot 10^8\) floor — answered YES by the walk
  charge at the old floor
  (`J-cyclemin-walk-charge-instance`); the \(1.63\cdot 10^8\)
  floor was then certified anyway and its instance is
  `J-cycle-period-four-hundred-seventy-eight-thousand`.
- Paper A still prints the \(10^6\) instance in Section 4.
  Corollary 5.11 prints the \(350000000\) floor. Updating the
  printed Theorem 4.6 is a publication decision, not a new
  inequality.

## Decision

**PROMOTE** the sensitivity table and the Theorem 4.6 instances
at \(N_0=26254995\), \(N_0=162849448\), and \(N_0=350000000\).
Then **stop scaling the computation**.

The three certified floors were the cheap jumps. The next useful
floor is the DK break-even of the fan blocker \(780239\) at
\(n^*=5.54\cdot 10^8\); the next *seed* \(16785921\) waits at
\(4.54\cdot 10^{11}\) (`J-cyclemin-walk-competition-law`).
Further \(N_0\) campaigns are **PARK**. Finance and the
Diophantine fan, not the verifier, are the limiters.

## Publication assessment

Status: `THEOREM` (computational instance). Laboratory extract
[juggler_descent_floor_note.md](../theory/juggler_descent_floor_note.md);
not a second manuscript. The inequality is unchanged
(`cycleMin_finance`). The new statements are the Theorem 4.6
instance at \(N_0=26254995\) (no period \(\le 50507\)) and,
combined with the walk charge, the \(N_0=162849448\) instance
(no period \(\le 478244\)) and the \(N_0=350000000\) instance
(no period \(\le 780238\)). Not a totality result.
