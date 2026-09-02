# Juggler Denjoy–Koksma / Ostrowski envelope

Status: **ACTIVE** (Phase 0 decided)

Successor of
([juggler_cycle_walk_envelope.md](juggler_cycle_walk_envelope.md)),
answering its open question. Not a halt theorem, not a floor
raise, not a uniform \(B/\theta\) claim, and not a reopen of the
REFUTED Koksma \(+1/L\) slogan: the correct constant is
\(2s(L)\), not \(1\).

## Problem

The crude envelope killed 18 leftovers DP-free but needed a
19-row occupancy census \(h\le 4\). Is there a census-free human
bound \(|C_L-C_*(n')|\le 2\,s(L)/L\), with \(s(L)\) the Ostrowski
digit sum of \(L\) over the convergent denominators of
\(\theta=\log(3/2)/\log 3\)?

## Exact statement

**Var bound (EXACT — HUMAN PROOF).** On the circle
\(\mathbb R/(1+\alpha)\mathbb Z\), the charge density
\(F(u)=n^{1-2^u}/2^u\) is strictly decreasing with \(F(0)=1\) and
\(F((1+\alpha)^-)=n^{-2}/3>0\), so its total variation including
the wrap jump is \(2(F(0)-F(1+\alpha))<2\).

**DK per block (KNOWN + EXACT certification).** For every
convergent denominator \(q\) of \(\theta=\alpha/(1+\alpha)\) and
every start \(x\), Denjoy–Koksma gives
\(\bigl|\sum_{k<q}F(\{x+k\theta\})-q\,C_*\bigr|
\le\mathrm{Var}(F)\le 2\).
The \(q\) list \(1,2,3,8,19,65,84,485,1054,24727,50508,125743,
176251\) is certified by an interval continued fraction on
rational bounds of \(x=\log 2/\log 3\) that come from two pure
big-integer comparisons: \(2^{17087915}>3^{10781274}\) and
\(2^{16785921}<3^{10590737}\) (consecutive convergents of \(x\);
interval width \(3.5\cdot 10^{-15}\), which survives the twelve
Gauss inversions needed at level \(176251\)).

**Ostrowski split (EXACT — HUMAN PROOF).** Any decomposition
\(L=\sum_j b_jq_j\) into convergent denominators cuts the
length-\(L\) orbit into \(s(L)=\sum_j b_j\) consecutive blocks,
each a DK block, so \(|C_L-C_*|\le 2\,s(L)/L\) for the exact
IET/hug prefix.

**Itinerary identity (COMPUTATIONALLY VERIFIED, exact integers).**
On all 19 leftovers the budgeted hug itinerary equals the exact
infinite-hug prefix letter for letter (E at step \(k\) iff
\(3^a\ge 2^{k+1}\), decided by the certified rational sandwich),
and the exact prefix uses exactly \(o_{\min}\) odds. So \(C_L\)
of the leftover **is** the Birkhoff average the theorem bounds.

**Kill envelope (COMPUTATIONALLY VERIFIED).** Greedy digits of
all 19 leftovers are exact with \(s\in[1,6]\); measured
excess\(\cdot L\le 1.868\le 2s\) everywhere;
\(2s/L\le 1.03\cdot 10^{-4}\ll\) the \(J\)-gap \(0.0051\). Via
the \(6/5\) unroll the DK margins are essentially the DP margins:
\(1.1196\) at \(L=50508\), 18 kills, \(L=176251\) still survives
(\(0.1588\)). Period bound unchanged: \(176251\).

No cycle of any length — not claimed.

## Current literature

- Denjoy–Koksma over convergent blocks — **KNOWN**
  (Herman; Kuipers–Niederreiter)
- Ostrowski representation — **KNOWN**
- Crude envelope (Riemann + occupancy \(h\le 4\)) —
  **PROMOTE** ([juggler_cycle_walk_envelope.md](juggler_cycle_walk_envelope.md))
- Koksma \(+1/L\) at constant \(1\) — **REFUTED**
  ([juggler_cycle_walk_koksma.md](juggler_cycle_walk_koksma.md))
- Hug exchange and explicit \(C_*\) — **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md))
- Every start reaches 1 — not claimed

Project relationship: **extended** (the census-free constant
\(2s(L)\) explains both the six \(+1/L\) failures — exactly the
rows with excess\(\cdot L>1\) — and the crude occupancy cap).

## Branch budget

```text
Mathematical target     Prove |C_L − C_*(n')| ≤ 2·s(L)/L, where s(L)
                        is the Ostrowski digit sum of L in the
                        convergent denominators of θ = log(3/2)/log 3,
                        and conclude C_L < 1/(ln 3 ln n') census-free
Novelty hypothesis      DK per convergent block with Var(F) ≤ 2
                        (F(u) = n^(1−2^u)/2^u, F(0)=1) gives constant
                        2s(L), not the REFUTED constant 1; leftover
                        digit sums are 1..6, and 12/50508 ≪ J-gap 0.0052
Falsifier               measured excess·L > 2s on a leftover; or the
                        q_j certification fails; or the claim is judged
                        a REPARAMETERIZATION of the refuted walk_koksma
Existing machinery      c_star_integral / gap_lower (cycle_walk_envelope),
                        hug C table (cycle_walk_greedy summary),
                        koksma excess table, exact integer 2^a vs 3^b
Maximum Phase-0 scope   one probe + dossier + conjecture + ledger rows;
                        no Lean, no Paper A, no N0, no new DP,
                        no new certified period bound
Promotion criterion     2s/L covers all 19 excesses AND the human
                        write-up (DK + blocks + Var ≤ 2 + J-gap) is
                        complete with exact q_j certification
Stop criterion          an excess above 2s, or a hole in the block
                        decomposition, or reparameterization
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\mathrm{Var}(F)\le 2\) on the wrapped circle —
  **EXACT — HUMAN PROOF**
- DK block bound at every certified \(q_j\) — **KNOWN**,
  applied with exact \(q_j\) certification
- \(|C_L-C_*|\le 2\,s(L)/L\) for the exact IET prefix —
  **EXACT — HUMAN PROOF**
- Budgeted hug = exact IET prefix on the 19 leftovers —
  **COMPUTATIONALLY VERIFIED** (integer-exact letters)
- Excess\(\cdot L\le 2s\) and \(2s/L<\) \(J\)-gap, 18 DP-free
  kills — **COMPUTATIONALLY VERIFIED**
- Koksma constant \(1\) — stays **REFUTED**
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_ostrowski`
- Artifacts: `data/research/juggler/cycle_walk_ostrowski/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_ostrowski.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_dk_envelope` — **EXACT — HUMAN PROOF**.
\(|C_L-C_*(n')|\le 2\,s(L)/L\) for the exact hug/IET prefix,
by Denjoy–Koksma per Ostrowski block with \(\mathrm{Var}(F)\le 2\).

`juggler_walk_koksma_one_over_L` — stays **REFUTED** (constant
\(1\); the six failures are exactly the rows with \(s\ge 4\) or
excess\(\cdot L>1\)).

## Counterexamples

None for the \(2s(L)\) constant. The constant-\(1\) counterexamples
(six leftover offsets, worst \(1.868\) at \(L=180467\)) are
recorded in `juggler_walk_koksma_one_over_L` and now sit strictly
inside \(2s\in\{8,8,12,6,8,10\}\).

## Formalization

Since the 1 September 2026 consolidation the quotient arithmetic
is Lean: `OstrowskiSandwich.lean` (`theta_sandwich_upper`,
`theta_sandwich_lower`, `lower_lt_walkTheta`, `walkTheta_lt_upper`,
`cf_lower_prefix`, `cf_upper_prefix`,
`theta_convergent_denominators`; ledger row
`J-cyclemin-walk-ostrowski-arithmetic`, **EXACT — LEAN
VERIFIED**). Denjoy–Koksma and the cylinder-interval bridge stay
KNOWN prose. Paper A Section 5 now prints the block envelope
(Theorem 5.7). No `sorry`. Not a halt theorem.

## Results

Classification **WALK_OSTROWSKI_GREEN**.

- \(x\)-bounds certified by two big-int comparisons; interval CF
  reproduces \(\theta=[0;2,1,2,2,3,1,5,2,23,2,2,1,\dots]\) with
  certified denominators up to \(176251\)
- All 19 leftovers decompose exactly with greedy digit sums
  \(s\in[1,6]\)
- Budgeted hug = exact IET prefix (letters and odd counts) on
  all 19
- Excess\(\cdot L\le 1.868\le 2s\) everywhere;
  \(2s/L\le 1.03\cdot 10^{-4}<0.0051\le\) \(J\)-gap
- DK envelope margins: \(1.1196\) at \(50508\), 18 kills,
  \(176251\) survives at \(0.1588\)
- Period bound unchanged

## Open questions

Is \(s(L)\) uniformly bounded on the survivor-lattice lengths
(the 99-length lattice and its leftover families), so the DK
envelope prices every future leftover census-free? Do not raise
\(N_0\) and do not claim a uniform \(B/\theta\) gap.

## Decision

**PROMOTE.** The DK/Ostrowski envelope is the human bound the
crude-envelope branch asked for: \(\mathrm{Var}\le 2\) and the
Ostrowski split are one-line human proofs, DK per convergent
block is classical, and the only computational content left is
exact integer arithmetic (the \(q_j\) sandwich, greedy digits,
letter-for-letter itinerary identity) plus the guarded float
comparison shared with Theorem 4.6. It replaces both the walk
DP and the 19-row occupancy census for the 18 kills, and it
explains the refuted constant \(1\): the correct constant is
\(2s(L)\). Not a reparameterization — walk_koksma asserted a
false inequality; this branch proves a true one with the right
constant.

Best next question: is \(s(L)\) uniformly bounded on the
survivor-lattice lengths, so the DK envelope prices every
future leftover census-free?

## Publication assessment

Status: `THEOREM`.

A census-free human envelope that retires the walk DP and the
occupancy census for the 18 kills at this floor. Together with
the exchange/\(C_*\) note this is a coherent short section for
Paper A's successor. Not a halt theorem.
