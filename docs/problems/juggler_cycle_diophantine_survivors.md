# Juggler Diophantine survivors past the walk-charge blocker

Status: **CLOSE** (the laboratory-kill slogan is a method
obstruction; the remaining mathematics is exported). Distill of
Paper A's leftover after Corollary 5.11. Not a halt theorem, not a
floor raise, not a Baker reopen, and not a Paper C edit. The
peak-pair dossier
([juggler_cycle_diophantine.md](juggler_cycle_diophantine.md)) is
a different object (`DIOPHANTINE_REPACKAGING`).

## Problem

Paper A stops at the \(k=2\) fan member \(780239=176251+2\cdot 301994\):
killing the remaining near-convergents of \(\log 2/\log 3\) “is a
Diophantine question about \(\lvert 3^o-2^L\rvert\); neither is
attempted here.” After Baker is REFUTED and further \(N_0\)
campaigns are PARK, is that leftover still a Juggler construction,
or is it the already-named classical continued-fraction question
plus a recorded per-orbit leftover?

## Exact statement

At the certified floor \(N_0=350000000\), the walk charge excludes
every length below \(780239\)
(`J-cycle-period-seven-hundred-eighty-thousand`). The stored
non-kill
([L780239.json](../../data/research/juggler/cycle_walk_charge/N350000000_kills/L780239.json))
has \(\theta=3.471\cdot 10^{-6}\), walk margin \(0.6049\), required
improvement \(14.46\), and `certified_excludes: false`. A
finance/walk kill at a fixed floor is determined by the exact gap
\(\theta(L)\), the walk envelope \(B\), and the floor \(N_0\).

**Trichotomy (EXACT — HUMAN PROOF as an exhaustion).** The slogan
“kill the near-convergents past \(780239\)” splits into three
inequivalent questions.

1. **Instance.** Exclude this one length at the frozen floor.
   Equivalent to a constraint that is not a gap lower bound, not a
   smaller \(B\), and not a larger \(N_0\). Dominance
   ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)) says
   any correct \(\delta\le 3^o-2^L\) produces an \(n_{\max}\) at
   least as large as the exact-gap \(n_{\max}\); the exact gap at
   \(L=780239\) is already known and does not kill. The hug DP
   *is* \(C_L\)
   ([juggler_cycle_walk_arch.md](juggler_cycle_walk_arch.md)). The
   DK break-even \(n^*=5.54\cdot 10^8\) is PARK
   ([juggler_descent_floor.md](juggler_descent_floor.md)).
2. **Family.** Drive the walk-finance required-improvement infimum
   over all dangerous fans away from \(1\). Already reduced:
   \(\ln R_{\min}\approx 4/(A+B)\) and
   \(e^{4/(a+2)}\le R_{\min}\lesssim e^{4/a}\), so fan sharpness
   along a subsequence iff the dangerous-position partial quotients
   of \(\log 2/\log 3\) are unbounded
   ([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md),
   conjecture `juggler_walk_fan_minimum_law`). Boundedness of those
   quotients is classical **OPEN**.
3. **Long cycles.** Floor-free gap transfer plus Rhin excludes only
   the short regime \(L^{14.3}\le n\log n/915\) (Paper A Theorem
   4.10 / Corollary 4.11, `cycleMin_gap_transfer`). Survivors live
   at \(L\approx n^{0.64}\). Paper A §6 records this as the open
   problem and not as a program. The mechanical window is CLOSE
   ([juggler_cycle_mechanical_window.md](juggler_cycle_mechanical_window.md)).

None of the three is the free term \(\psi_F\) of Paper C. A better
period bound does not touch the \(OO\) cylinder.

No unused laboratory mechanism is on the books. No cycle of any
length — not claimed.

## Current literature

- Paper A Corollary 5.11 (period \(\ge 780239\) at
  \(N_0=350000000\)) — **COMPUTATIONALLY VERIFIED**
  ([juggler_finite_dynamics_note.md](../theory/juggler_finite_dynamics_note.md))
- Baker / Rhin / Simons–de Weger transfer —
  **REFUTED**
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md);
  `juggler_baker_kills_near_convergents`;
  `rhin-1987-pade-irrationality`;
  `simons-de-weger-2005-collatz-m-cycles`)
- DK-arch free-kill — **REFUTED**
  ([juggler_cycle_walk_arch.md](juggler_cycle_walk_arch.md))
- Further \(N_0\) campaigns — **PARK**
  ([juggler_descent_floor.md](juggler_descent_floor.md))
- Fan-minimum law / CF reduction — **PROMOTE** (instances
  **COMPUTATIONALLY VERIFIED**; asymptotic law **CONJECTURE**)
  ([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md))
- Wu–Wang width cap — **PROMOTE** as width only; cannot give
  \(a=O(1)\) or kill a leftover
  ([juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md);
  `wu-wang-2014-irrationality-measure-log3`)
- Gap transfer + Rhin short-cycle reduction —
  **EXACT — LEAN VERIFIED** / **EXACT — HUMAN PROOF**
  (`J-cyclemin-gap-transfer`, `J-cyclemin-short-cycle-rhin`)
- Boundedness of the CF quotients of \(\log 2/\log 3\) — **OPEN**
  (Gauss–Kuzmin expects unbounded;
  `kuipers-niederreiter-1974-uniform-distribution`)
- Paper C §6.3: Papers A and B constrain cycle states and
  descending branches; neither touches \(\psi_F\) —
  **KNOWN**
  ([juggler_fate_almost_all_note.md](../theory/juggler_fate_almost_all_note.md))
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a laboratory kill;
**exported** as an external leftover (same role as
[exponent_pair_two_monomial.md](../theory/exponent_pair_two_monomial.md)).

## Branch budget

```text
Mathematical target     After Baker and N0 are forbidden, is "kill
                        near-convergents past 780239" still a Juggler
                        construction, or is it the already-named
                        classical CF question plus a recorded
                        per-orbit leftover?
Novelty hypothesis      The slogan hides a trichotomy. Writing it
                        as an exported problem is the remaining
                        mathematical act; there is no unused
                        laboratory kill.
Falsifier               An unused mechanism that excludes L=780239
                        at N0=3.5e8 without a gap lower bound, a
                        tighter B, or a larger floor.
Existing machinery      L780239.json; dominance lemma; fan-minimum
                        law; negative_knowledge Diophantine wall;
                        Paper A Cor 5.11 and §6; Paper C §6.3
Maximum Phase-0 scope   One dossier + one short export note +
                        journal / branch-ledger / AGENTS pointer.
                        No probe, no GPU, no Lean, no N0, no Baker
                        re-run, no Paper A/B/C theorem edits, no
                        psi_F.
Promotion criterion     The trichotomy is exact and the leftover
                        is cleanly exported (as exponent_pair_two_monomial
                        is). PROMOTE the note as external mathematics.
Stop criterion          Any proposed kill reduces to a closed wall
                        member, to the CF-quotient question, or to
                        the recorded long-cycle leftover. Then CLOSE
                        the lab-kill slogan and do not open a
                        successor branch.
```

## Balanced-ternary formulation

None required. The objects are ordinary positive integers and the
continued fraction of \(\log 2/\log 3\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact gap \(\theta=(3^{o_{\min}}-2^L)/3^{o_{\min}}\) at
  \(L=780239\) — **COMPUTATIONALLY VERIFIED** (stored kill row)
- Dominance of the exact gap over any correct lower bound —
  **EXACT — HUMAN PROOF**
- Hug DP is \(C_L\) — **EXACT — HUMAN PROOF**
- Fan-minimum balance \(\ln R_{\min}\approx 4/(A+B)\) —
  **COMPUTATIONALLY VERIFIED** on both certified fans;
  asymptotic equivalence **CONJECTURE**
- Boundedness of dangerous-position partial quotients of
  \(\log 2/\log 3\) — **OPEN**
- Laboratory kill of \(L=780239\) at \(N_0=3.5\cdot 10^8\) —
  **REFUTED** as a method (exhaustion of \(\theta\), \(B\), \(N_0\))
- No cycle of any length — not claimed
- A bound on \(\psi_F\) — not claimed

## Experiments

None. This Phase-0 is a distill. No probe, no GPU, no new
artifact, no CLI.

## Conjectures

None new. `juggler_walk_fan_minimum_law` stays **ACTIVE**.
`juggler_baker_kills_near_convergents` stays **REFUTED**.

## Counterexamples

None new. The instance numbers are the stored non-kill at
\(L=780239\) (margin \(0.6049\)) and the already-recorded
dominance witness \(L=19\), \(n_{\max}=297>53\).

## Formalization

None. No new Lean, no `sorry`. `GapTransfer.lean` and the
walk-charge layers already own the imported theorems.

## Results

Classification **NEAR_CONVERGENT_KILL_CLOSED**.

- The slogan hides a trichotomy (instance / family / long-cycle).
  The three questions are not interchangeable.
- Instance: no unused mechanism. Gap lower bounds lose to
  dominance; the envelope cannot be tightened below the hug DP;
  the next useful floor \(5.54\cdot 10^8\) is PARK and buys one
  fan member.
- Family: already reduced to unbounded dangerous-position partial
  quotients of \(\log 2/\log 3\). The walk-competition program
  terminated at that reduction.
- Long cycles: recorded in Paper A §6 as open and not as a
  program. The mechanical window stays CLOSE.
- Firewall: this constrains cycle states (Lachesis from the
  inside). It does not bound \(\psi_F\).
- Export:
  [juggler_near_convergent_diophantine_note.md](../theory/juggler_near_convergent_diophantine_note.md).
  No new ledger row.

## Open questions

None actionable in the laboratory. The classical question —
whether the dangerous-position partial quotients of
\(\log 2/\log 3\) are unbounded — is **OPEN**; no finite
computation decides it, and the Baker-type effective routes stay
REFUTED for this application. Do not reopen a kill. Do not
certify deeper CF quotients past \(q_{13}=301994\) as a
substitute kill. Do not open the long-cycle band as a program.

## Decision

**CLOSE.** The stop criterion fired: every proposed laboratory
kill of the near-convergents past \(780239\) reduces to a closed
Diophantine-wall member, to a tighter walk envelope that the hug
DP already computes, to a PARK floor, to the already-named
CF-quotient question, or to the recorded long-cycle leftover.
The laboratory-kill slogan is a method obstruction. The remaining
mathematics is the family leftover, written as the Paper D
working draft
[juggler_near_convergent_diophantine_note.md](../theory/juggler_near_convergent_diophantine_note.md)
(not a fourth review object). The laboratory-kill slogan stays
closed. The write-up of the already-proved family theorem is a
**PROMOTE** of that manuscript, not a reopen of the kill. Best
next question: none in the laboratory. The classical question is
whether the dangerous-position partial quotients of
\(\log 2/\log 3\) are unbounded.

## Publication assessment

Status: `STRUCTURAL`. The laboratory-kill slogan is closed. The
family leftover is the Paper D working draft
[juggler_near_convergent_diophantine_note.md](../theory/juggler_near_convergent_diophantine_note.md)
(not a fourth review object). Not a halt theorem.
