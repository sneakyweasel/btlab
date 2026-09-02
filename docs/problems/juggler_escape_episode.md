# Juggler escape-episode descent via the minimal bad anchor

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
`PredClosure`-from-`{1}` reopen, not Paper A, not a terminal-cluster
census, and not a claim that every positive integer reaches 1.

After shared `AboveAnchor` obstructions, a hypothetical minimal
nonterminating start occupies an odd-landing escape corridor. This
phase asks whether a completed escape episode in that corridor
lowers a well-founded quantity or exactly recurs. It does **not**
re-test smaller-bad descent or short
\(\operatorname{Pred}_{E,OE,OOE,OOOE}\), already **REFUTED** in
[juggler_minimal_anchor_closure.md](juggler_minimal_anchor_closure.md).

## Problem

Does every completed leftover escape episode produce a strictly
smaller episode state, or an exact recurrent entrance?

## Exact statement

Let \(G=\{m:m\text{ reaches }1\}\). For a least \(n_\ast>1\) outside
\(G\), every finite prefix of the orbit is `AboveAnchor`. Partition
that prefix by one of

- even-reset: first later even state whose image has smaller
  corridor rank \(\rho(x)=\min\{r:x<n^r\}\);
- rank-return: first later strict rank drop;
- first-below-anchor: \(\tau=\min\{k:T^k(n)<n\}\).

On a completed episode from \(x\) to a landing \(y\), decide whether

\[
\rho(y)<\rho(x)
\qquad\text{or}\qquad
y<x
\qquad\text{or}\qquad
(x,\text{reset state})\text{ already occurred}.
\]

The global running minimum \(L_k=\min_{j\le k}T^j(n)\) is recorded
separately. Do not demand that every high integer is good.

## Current literature

- `AboveAnchor` shared by `CycleMin` and `MinimalNonTerm` —
  **EXACT — LEAN VERIFIED** (`J-above-anchor`).
- Cycle or escape —
  **EXACT — LEAN VERIFIED** (`J-trajectory-cycle-or-escape`).
- `ReturnBelow` and `HasFiniteStop` name a later drop below the
  start — **EXACT — LEAN VERIFIED**.
- Even \(x<n^{2k}\) gives \(T(x)<n^k\) —
  **EXACT — LEAN VERIFIED** (`even_below_anchor_pow`).
- Unique leftover odd spine; no smaller-bad predecessor; short
  structured return and whole-path rank potential —
  **REFUTED** (`J-minimal-anchor-closure`).
- Every start reaches 1 — not claimed.

Project relationship: **independent** as an episode-partition
question on the leftover corridor. The first-overshoot closure
experiment is already parked.

## Branch budget

```text
Mathematical target     leftover completed escape episode
                        lowers a well-founded quantity or
                        exactly recurs
Novelty hypothesis      episode first-passage / record min,
                        not whole-path rank or first-overshoot Pred
Falsifier               landings climb or oscillate; L frozen
                        at n; no recurrence; rank-return =
                        even-reset; 69/89 show the same pattern
Existing machinery      AboveAnchor; ReturnBelow; HasFiniteStop;
                        even_below_anchor_pow; FiniteProgress;
                        cycles_or_escapes; trajectory_until_drop
Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast;
                        three episode cuts; no new Lean
Promotion criterion     a finite-progress episode theorem, or
                        a record-min law that is not the already
                        refuted whole-path rank potential
Stop criterion          episode minima climb/oscillate and no
                        recurrence; first-below is HasFiniteStop;
                        generic trajectory pattern; PredClosure
                        reopen; cell census; Z5; length-11
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. A sparse description of PE landings would have
been a BT observation. None appeared.

## Candidate operations / invariants

- `AboveAnchor` on every leftover prefix before the drop —
  **EXACT — LEAN VERIFIED**
- even-reset and rank-return cuts coincide on the laboratories —
  **COMPUTATIONALLY VERIFIED**
- rank-2 episodes return to rank 2, or to a still-high even that
  then resets by `even_below_anchor_pow` —
  **COMPUTATIONALLY VERIFIED**
- PE landings of `365` climb `763, 1749, 4447, 12707` —
  **COMPUTATIONALLY VERIFIED**
- PE landings of `1517` oscillate
  `3789, 10613, 33811, 2493, 539470` —
  **COMPUTATIONALLY VERIFIED**
- global record min equals \(n\) on the whole `AboveAnchor`
  prefix — **COMPUTATIONALLY VERIFIED**
- first-below-anchor is the existing terminal drop —
  **COMPUTATIONALLY VERIFIED**. **REPARAMETERIZATION** of
  `HasFiniteStop` / `ReturnBelow`
- `69` and `89` have the same rank-2 return-then-drop —
  **COMPUTATIONALLY VERIFIED**
- every completed escape episode lowers the anchor-relative
  complexity or exactly recurs —
  **REFUTED**
- if successive episode record mins stay equal then the orbit is
  recurrent — **REFUTED** (they stay equal to \(n\) without a cycle)
- even reset lowers the rank-2 return rank —
  **REFUTED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.escape_episode`
- Records: [juggler_escape_episode.md](../research/juggler_escape_episode.md),
  [juggler_escape_episode.json](../research/juggler_escape_episode.json)
- Tests: `tests/research/juggler_sequence/test_escape_episode.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating leftovers, not `MinimalNonTerm` witnesses.

- “completed rank-2 episode returns at a smaller rank” — every
  rank-2 leftover episode returns at rank 2, or lands on a
  still-high even (`501`: `133347 \to 582916`; `6187`:
  `15771571 \to 125201440`).
- “episode landings decrease” — `365` climbs
  `763 < 1749 < 4447 < 12707`; `1517` drops to `2493` and then
  rises to `539470`.
- “equal successive record mins imply recurrence” — \(L_k=n\)
  throughout the prefix, and the path is not periodic.
- “exact episode signature repeats” — no
  \((\text{start},\text{reset})\) pair repeats.
- `69` and `89` already show rank-2 return then drop, so the
  pattern is not leftover-specific.

## Formalization

No new Lean module. `AboveAnchor`, `ReturnBelow`,
`even_below_anchor_pow`, and `finiteProgress_of_aboveAnchor_returnBelow`
stay in `MinimumRelative.lean` / `Residuals.lean`. `HasFiniteStop`
stays in `FirstPassage.lean`. `trajectoryExponentGap` stays in
`Drift.lean`. `collapse_on_pow_two` stays in `Collapse.lean`.
Not imported by `Problems.JugglerPaper`. No `sorry`. No
`EscapeEpisode` API. No `juggler_reaches_one`.

A later `ReturnBelow` / `HasFiniteStop` is the terminal drop, not
a mid-corridor episode law. Drift and Collapse are word-exponent
and even-tower identities, not PE-landing ranks.

## Results

Classification **ESCAPE_EPISODE_PARK**.

On the leftover laboratories, even-reset and rank-return are the
same cut. Rank-2 episodes do not lower return rank. Their landings
climb or oscillate while staying at least \(n\). The global record
minimum is frozen at the anchor, so it cannot detect recurrence.
First-below-anchor is exactly the existing finite-stop certificate.
No exact episode signature repeats. The shared-trap controls `69`
and `89` show the same rank-2 return.

The proposed escape-versus-descent dichotomy therefore fails for
every tested completed-episode definition that is not the terminal
drop. The strong definition (first \(y<n\)) is a restatement of
`HasFiniteStop`. The weak definition (even-reset / rank-return)
produces many completed `AboveAnchor` episodes that neither descend
nor recur. High-even chains (`582916 \to 763`, `125201440 \to 11189`)
are the existing parameterized square trap, not a new potential.

This is not a halt theorem and not a cycle-exclusion theorem.

## Open questions

The leftover generator remains a unique odd spine into PE landings.
Is there a Diophantine constraint on those landings that forces a
later even-below-square, without an episode hierarchy and without
reopening interval closure? Do not hunt a fourth episode cut.

## Decision

**PARK**. The episode-descent attack does not give a well-founded
quantity on the residual odd-escape corridor. Weak episodes return
to the same rank-2 band with growing or oscillating PE landings.
Strong episodes are the already-named terminal `HasFiniteStop`.
Minimality still adds nothing beyond `AboveAnchor`. The pattern is
already visible on `69` and `89`, so a generic trajectory theorem
would not be leftover-specific.

Best next question: is there a Diophantine obstruction at an
empty-odd-preimage PE landing that forces a later even-below-square,
without a new episode rank?

## Publication assessment

Status: `EXPLORATORY`. A negative episode-partition fragment on
four finite-escape controls, not a paper candidate and not a
Juggler totality result.
