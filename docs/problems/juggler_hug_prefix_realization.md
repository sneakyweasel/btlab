# Juggler hug-cylinder realization (equidistribution vs descent-free flight)

Status: **EXPLORATORY**

Follow-up to the above-anchor walk branch's best next question. It is
**not** a \(K_3\) attack, not a reopen of the refuted
ambient-discrepancy transfer, the closed formal-realized-gap branch
(generic prefix-NC fills), the closed survival-set branch, or the
closed mechanical-lift branch (inverse cycle lifts of hug itineraries), and
not a claim that every positive integer reaches 1.

## Problem

Can Paper B's fixed-depth parity equidistribution contradict the
extremal odd density that hug domination
(`J-above-anchor-hug-domination`) forces on a hypothetical
descent-free flight?

## Exact statement

Hug domination makes the exact hug itinerary the pointwise-minimal
descent-free word. Its depth-\(L\) cylinder is

\[
C_L=\{n:\text{the orbit word of } n \text{ starts with the hug } L\text{-prefix}\}.
\]

A fixed-depth kill of extremal flights would require some admissible
depth-\(d\) cylinder to be empty above a scale. Quantitative core: is
the minimal witness \(m(L)=\min C_L\) at the cylinder-predicted scale
\(2^L\) (slope \(1\) in \(\log_2\), count ratio \(2\)), with
witnesses staying above their anchor, or does realization die at a
finite depth \(L^\ast\)?

## Current literature

- Depth-\(\le 4\) parity equidistribution with power savings —
  **EXACT — HUMAN PROOF** (Paper B); all sixteen depth-\(4\)
  cylinders have positive density.
- Conditional Terras: all-depth equidistribution \(\Rightarrow\)
  density-one certificates — **EXACT — HUMAN PROOF**
  (`J-equidistribution-implies-density-one`); yields density-one,
  never pointwise emptiness.
- Prefix-NC words fill through length \(20\) on the atlas, through
  length \(16\) as `AboveAnchor` for \(n\le 10^6\) —
  **COMPUTATIONALLY VERIFIED** (formal-realized-gap, CLOSE).
- Ambient discrepancy does not transfer to single orbits —
  **REFUTED** (parity-discrepancy-transfer). Windowed rarity does
  not give survival-set emptiness — CLOSE (survival sets).
- Hug domination on open prefixes — **EXACT — LEAN VERIFIED**
  (`J-above-anchor-hug-domination`, `AboveAnchorWalk.lean`).

Project relationship: **independent** as a targeted single-cylinder
measurement; the structural close assembles **KNOWN** ledger facts.

## Branch budget

```text
Mathematical target     can fixed-depth equidistribution contradict
                        a descent-free flight - concretely: is the
                        extremal hug cylinder realized at every
                        depth with m(L) ~ 2^L, or does realization
                        die at a finite depth L*?
Novelty hypothesis      the hug prefix is one specific extremal
                        cylinder; witness scaling and above-anchor
                        verification beyond generic prefix-NC fills
                        were never measured
Falsifier               (for the close) an anomalously early empty
                        depth or an anchor-violating witness;
                        (for the obstruction) m(L) tracking 2^L
Existing machinery      hugOdds/hugWord (Lean + probe), gmpy2 scan,
                        prefix-NC fills, hug domination lemma
Maximum Phase-0 scope   one probe: scan n <= 2e8, witness table
                        m(L), cylinder counts vs 2^{-L}, exact
                        above-anchor checks; no Lean, no Paper edits
Promotion criterion     an empty admissible depth or any provable
                        fixed-depth kill mechanism
Stop criterion          filled cylinder at the predicted scale:
                        record the structural close and CLOSE
```

## Balanced-ternary formulation

Not BT-specific; the cylinder is a parity condition on nested floor
powers, the same \(2\)–\(3\) data as the walk layer.

## Why BT may be relevant

Only through the shared multiplicative \(2\)–\(3\) structure; no
representation claim.

## Candidate operations / invariants

- Minimal witness \(m(L)\) and cylinder counts
  \(|C_L\cap[3,N]|\) versus the \(2^{-L}\) prediction
  (**OBSERVATION**).
- Exact above-anchor verdict on every witness (integer arithmetic;
  a hug-matching prefix keeps \(u\in[0,1+\alpha)\), so states stay
  below \(n^3\)).

## Experiments

Runner: `python -m research.juggler_sequence.hug_prefix_realization`
(probe `src/research/juggler_sequence/hug_prefix_realization.py`).
Artifact: `data/research/juggler/hug_prefix_realization/summary.json`.
Fast suite:
`tests/research/juggler_sequence/test_hug_prefix_realization.py`.

Scan of all odd \(n\le 2\cdot 10^8\): longest hug-prefix match,
first witness per depth, cylinder counts, above-anchor verdicts,
least-squares slope of \(\log_2 m(L)\).

## Conjectures

None new. The branch prices the recorded question; the standing
targets stay `juggler_asymptotic_descent` and
`juggler_descent_time_log`.

## Counterexamples

None. The falsifier for the close (an early empty depth) did not
fire.

## Formalization

None new. The Lean inputs are `AboveAnchorWalk.lean` (hug
domination) and `WalkChargeItineraries.lean` (exact hug rule); this branch
adds measurements only.

## Results

- **The hug cylinder is filled at the predicted scale
  (COMPUTATIONALLY VERIFIED):** on \([3,2\cdot 10^8]\) the minimal
  witness \(m(L)\) tracks \(2^L\) (least-squares slope \(0.946\) in
  \(\log_2\) over \(21\) depths \(L\ge 8\)) and cylinder counts
  halve per depth (mean ratio \(2.022\)); maximal realized depth
  \(28\) at \(n=48427569\) (\(\log_2\approx 25.5\), horizon
  \(\log_2 N\approx 27.6\)); every witness stays above its anchor
  exactly. The laboratories are literally hug-hugging orbits:
  \(365\) realizes the hug prefix through depth \(10\), \(1517\)
  through \(13\).
- **Structural close of the recorded question (KNOWN facts
  assembled):** fixed-depth equidistribution *fills* admissible
  cylinders (proved at depth \(\le 4\), measured here on the
  extremal cylinder to depth \(27\)); a fixed-depth kill would need
  an empty admissible cylinder, contradicting the fills. The
  transfer of ambient statistics onto one sparse orbit is refuted,
  and a flight's states form a zero-density set that fits inside
  the exceptional set of every power-savings statement. Even
  all-depth equidistribution yields only density-one certificates
  (`J-equidistribution-implies-density-one`), never pointwise
  survival-set emptiness (survival-set branch, CLOSE). Hence **no
  fixed-depth equidistribution statement can contradict the
  extremal odd density of a descent-free flight**; the only
  remaining route is infinite-depth control — the parked
  \(K_3\)/BB/GG/JJ wall.

## Open questions

- Constructive nonemptiness: is there a preimage-cylinder
  construction certifying \(C_L\ne\emptyset\) for **every** \(L\)
  (a theorem that would permanently close all fixed-depth kills,
  beyond scan horizons)?

## Decision

**CLOSE.** The measured extremal cylinder is filled at exactly the
equidistribution-predicted scale, every witness is above-anchor, and
the assembled ledger facts show a fixed-depth kill is structurally
impossible: equidistribution populates the cylinders a descent-free
flight needs rather than emptying them, and its exceptional sets
swallow any single orbit. The recorded next question of the
above-anchor walk branch is answered **no**. The statements are
KNOWN ledger facts plus a confirming measurement; no new theorem, no
new obstruction.

Best next question: is hug-cylinder nonemptiness provable at every
depth by an explicit preimage-cylinder construction (existence, not
density) — turning the fixed-depth close from a scan into a theorem?

## Publication assessment

Status: **EXPLORATORY**. Negative knowledge with a clean
measurement; a paragraph of context for any future termination note,
not a paper candidate.
