# Juggler greedy hug-itinerary as walk-charge maximizer

Status: **ACTIVE** (Phase 0 decided)

Refinement of
([juggler_cycle_walk_mechanical.md](juggler_cycle_walk_mechanical.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the REFUTED Christoffel prefix-dominance
or leftover-cell slogans.

## Problem

Mechanical CLOSE left the charge maximizer as greedy
\(E\)-at-first-legal-time, which equals Christoffel only near the
critical slope. Does that hug itinerary prefix-minimize \(a_k\) (hence
\(u_k\)) among all admissible \(u\ge 0\) walks with fixed
\((L,o)\), and does its charge equal the certified survey \(B\)
— including the \(1054\)-family offsets where Christoffel lost?

## Exact statement

**Hug itinerary (definition).** On a feasible pair
(\(\mathrm{STEP}\cdot o\ge L\)) take \(E\) iff \(u\ge 1\) and an
even remains, else \(O\). The completable table is redundant: when
only evens remain, \(u=\mathrm{surplus}+e_{\mathrm{left}}\ge
e_{\mathrm{left}}\), so the stream cannot strand. This is \(O(L)\).

**Hug is prefix-minimal (COMPUTATIONALLY VERIFIED).** On every
feasible pair with \(L\le 24\) (\(123/123\)) and at leftover
\(L=19,84,1054\), the hug odd-count \(a_k\) equals the pointwise
minimum among all completable admissible walks. The \(O(Lo)\)
table-greedy word of
[juggler_cycle_walk_mechanical.md](juggler_cycle_walk_mechanical.md)
equals the streamed hug on the same set.

**Hug charge is the certified survey DP
(COMPUTATIONALLY VERIFIED).** At the certified reduced base
\(n'=ne^{-D}\), streamed hug \(B\) matches the committed 19-row
walk-charge survey (max relative error \(8.15\cdot 10^{-11}\)),
including every \(1054\)-family offset. That is the gap
Christoffel lost (up to \(1.50\cdot 10^{-3}\)).

**Leftover \(C\) is the mechanical average
(COMPUTATIONALLY VERIFIED).** Hug densities on the 19 leftovers
lie in \([0.047946,0.047957]\). The existing \(10^5\)-letter
mechanical prefix at the \(50508\) reduced base has
\(C_*=0.047947\); relative spread against that average is
\(2.12\cdot 10^{-4}\). The plateau is the hugging walk, on seeds
and offsets.

**Uniform \(B/\theta<1\) at fixed \(N_0\) remains false.**
Hug \(B/\theta=5.25\) at \(L=176251\). Do not reopen Baker.

No cycle of any length — not claimed.

## Current literature

- Mechanical extremizer —
  **CLOSE** / **REFUTED** Christoffel prefix-dominance
  ([juggler_cycle_walk_mechanical.md](juggler_cycle_walk_mechanical.md))
- Walk-excursion maximizer identification —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md))
- Coupled walk charge / certified survey —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md))
- Christoffel leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Mechanical / Christoffel discrepancy —
  **KNOWN** (Borel–Laubie / Berstel–de Luca)
- Every start reaches 1 — not claimed

Project relationship: **extended** (identifies the already
certified walk DP with an \(O(L)\) hugging word; does not reopen
leftover-cell rigidity).

## Branch budget

```text
Mathematical target     Does greedy E-when-legal prefix-minimize
                        a_k (hence u_k) among admissible u≥0 walks
                        with fixed (L,o), and does its charge equal
                        certified survey B (and C_* at this floor)?
Novelty hypothesis      g decreasing + pointwise min u identifies
                        the DP maximizer as an O(L) word; C_* is
                        then the ergodic average of that hugging
                        walk, including family offsets.
Falsifier               greedy a_k > prefix-min a_k; or greedy B
                        disagrees with survey B
Existing machinery      prefix_min_odds / greedy_word;
                        charge_row / deficit_D; survey.json;
                        mechanical_average
Maximum Phase-0 scope   L≤24 prefix-min vs greedy; O(L) streamed
                        greedy charge vs all 19 survey rows;
                        greedy C vs existing mechanical C_*.
                        No Lean, no Paper A, no N0, no new DP
Promotion criterion     greedy = prefix-min on the census AND
                        greedy B = survey B on all 19 leftovers
Stop criterion          a prefix-min miss; survey mismatch; or
                        the claim is a tautology with no survey hit
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Hug \(E\)-when-legal prefix-minimizes \(a_k\) among admissible
  walks — **COMPUTATIONALLY VERIFIED** on \(L\le 24\) and at
  leftover \(19,84,1054\)
- Streamed hug equals table-greedy (completable DP) —
  **COMPUTATIONALLY VERIFIED** on the same set
- Hug \(B\) equals certified survey \(B\) —
  **COMPUTATIONALLY VERIFIED** on all 19 leftovers
- Leftover \(C\) equals mechanical \(C_*\) —
  **COMPUTATIONALLY VERIFIED** (relative spread \(2.12\cdot 10^{-4}\))
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** (already; confirmed on hug \(B\))
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_greedy`
- Artifacts: `data/research/juggler/cycle_walk_greedy/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_greedy.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_greedy_prefix` — **ACTIVE**. The hug itinerary
prefix-minimizes \(u_k\) among admissible walks of a given
\((L,o)\) and therefore attains the walk-charge maximum; leftover
\(C\) is the mechanical average of that walk.

## Counterexamples

None for the hug identification. The Christoffel counterexamples
of the parent branch stand: \((4,3)\) is `OOEO` (hug), not
`OOOE`; survey offsets match hug and beat Christoffel.

## Formalization

None. No `WalkGreedy.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem.

## Results

Classification **WALK_GREEDY_GREEN**.

- Prefix-min / table-greedy \(=\) hug on \(123/123\) feasible
  pairs with \(L\le 24\)
- Holds at leftover \(19,84,1054\)
- Survey hug \(B\) matches certified \(B\) on all 19 leftovers
  (max relative error \(8.15\cdot 10^{-11}\))
- Leftover \(C\in[0.047946,0.047957]\) vs mechanical
  \(C_*=0.047947\)
- Uniform \(B/\theta\) at floor \(26254995\) is false
  (\(B/\theta=5.25\) at \(176251\))

## Open questions

A human exchange lemma for the hug itinerary — not for ceiling
Christoffel — together with an explicit bound or integral for
\(C_*(n')\). Do not raise \(N_0\) and do not claim a uniform
\(B/\theta\) gap.

## Decision

**PROMOTE.** The Phase-0 promotion criterion fired: hug
\(E\)-when-legal stays on the prefix-min path through the census
and at the leftover CF lengths, and its streamed charge equals
the certified survey DP on every leftover, including the offsets
where Christoffel failed. Leftover \(C\) is the already-computed
mechanical average of that same hugging policy. This identifies
the adversary of the certified walk charge as an \(O(L)\) word.
It is not a leftover-cell reopen, not a Baker reopen, and not a
reparameterization of the exponential DP: the DP is no longer
needed to price a leftover.

Best next question: a human exchange lemma for the hug itinerary,
together with an explicit bound or integral for \(C_*(n')\)?

## Publication assessment

Status: `STRUCTURAL`.

A laboratory identification of the walk-charge maximizer as the
hug itinerary, now matching the certified survey on seeds and offsets.
Not a paper candidate until the exchange lemma and the density
bound are human proofs. Not a halt theorem.
