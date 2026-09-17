# Juggler survivor-count decay (the Theorem 6.1 count, kernel-checked)

Status: **PROMOTE** (the survivor count is identified with a binomial
tail, decays, and the conditional Theorem 6.1 is assembled end-to-end;
FD stays open).

Child of [juggler_k3_rate_free.md](juggler_k3_rate_free.md). Not a
Paper B edit; the manuscript's Theorem 6.1 stays conditional on FD, and
this branch changes no manuscript sentence. Not a \(K_3\) attack and
not a harvest.

## Problem

The rate-free density-one reduction
(`J-equidistribution-implies-density-one`, `J-rate-free-density-one`)
bounds the uncertified starts at depth \(d\) by \(N_d/2^d\) plus error
terms, where \(N_d\) counts the parity words of length \(d\) with no
contracting prefix. The decay \(N_d/2^d \to 0\) was quoted from
Hoeffding as written mathematics; `PaperBMarkov`'s header explicitly
listed "the identification of the surviving words as a binomial count"
as unformalised. Can that link be kernel-checked, and with it the whole
conditional Theorem 6.1?

## Exact statement

With \(\beta = \log 2 / \log 3\): every prefix-noncontracting word of
length \(d\) has at least \(\lceil d\beta \rceil\) odd letters; words of
length \(d\) with at least \(a\) odd letters number exactly
\(\sum_{k=a}^{d} \binom{d}{k}\); hence
\(N_d/2^d \le \theta(\beta)^d \to 0\) with \(\theta(\beta) < 1\). Under
FD (per-class fairness at each fixed depth), the never-certified starts
have natural density zero, with the limit order \(N \to \infty\) before
\(d \to \infty\).

## Current literature

- Paper B Theorem 6.1 (`J-fd-step-is-formal-and-theorem-six-one-stays-conditional`)
  — **EXACT — LEAN VERIFIED** as an inference from FD; the union
  identification and the decay stayed written. Project relationship:
  **extended**.
- `J-rate-free-density-one` (Lemma A) — **EXACT — HUMAN PROOF**;
  Lean home `RateFreeDensity.lean`. **extended**.
- `PaperBMarkov.chernoff_density`, `tilt_gives_theta`;
  `PaperBChernoff.theta_lt_one`; `PaperBThreshold.beta` —
  **EXACT — LEAN VERIFIED**. **reproduced** as lemmas.

## Branch budget

- **Target:** kernel-check \(N_d/2^d \to 0\) and assemble the
  conditional density-one statement around it.
- **Novelty hypothesis:** no new mathematics; the new content is the
  machine-checked binomial-tail identification and the exact
  small-depth counts.
- **Falsifier:** a prefix-noncontracting word below the endpoint
  barrier (blocked by `neverNeg_endpoint`), or \(\theta(\beta) \ge 1\)
  (blocked by `theta_lt_one`, \(\beta \neq 1/2\)).
- **Already killed by?:** none — the termination kill test targets
  Juggler constructions of \(e(uw^{3/2})\); this branch is the
  combinatorial count behind Theorem 6.1, not an analytic attack.
  `harvest_counting` (CLOSE) is the analytic leftover, unrelated.
- **Existing machinery:** `RateFreeDensity` (`neverNegWords`,
  `neverNeg_endpoint`, `extend_fiber_disjoint`,
  `uncertifiedCount_eq_sum`, `neverCertifiedCount_le_uncertified`,
  `allOdd_prefixNoncontracting`), `PaperBMarkov`, `PaperBChernoff`,
  `PaperBDensity.exceptional_density_zero`.
- **Maximum Phase-0 scope:** one auxiliary module
  `PaperBSurvivorDecay.lean`; the tail-count formula, the tilted bound,
  the decay, the conditional assembly, and the kernel-decided values
  \(N_1, \dots, N_8\).
- **Promotion criterion:** `lake build` green, kernel trust only, all
  registration gates pass.
- **Stop criterion:** if the tail formula needed choice-heavy API, cut
  to the decay theorem alone. Did not fire.

## Balanced-ternary formulation

Not a BT statement; parity words over \(\{O, E\}\) as in the rest of the
Juggler layer.

## Why BT may be relevant

None beyond the shared itinerary encoding.

## Candidate operations / invariants

The odd-count walk \(o_t\) against the barrier \(\lceil t\beta \rceil\);
the Pascal recurrence of the binomial tail.

## Experiments

No probe. The dynamic-program values \(N_d\) (4 at \(d=5\), 2114 at
\(d=16\)) were recomputed in Python during exploration and match
`tests/research/juggler_sequence/test_paper_b_prefix_count.py`; the
kernel-checked values cover \(d \le 8\).

## Conjectures

`juggler_tower_rate_free_equidistribution` (ACTIVE) is exactly the
`FairClasses` hypothesis of the assembled theorem; this branch neither
proves nor disproves it.

## Counterexamples

None found; the falsifiers did not fire.

## Formalization

`formal/Problems/Juggler/PaperBSurvivorDecay.lean`. Kernel-trusted
throughout (`decide +kernel` for the small-depth values; no
`native_decide`).

## Results

**EXACT — LEAN VERIFIED** (`PaperBSurvivorDecay.lean`):

- `count_oddCount_ge`: the binomial tail count, exactly.
- `oddCount_ge_of_mem_neverNeg`,
  `neverNegCount_le_choose_tail`: \(N_d\) sits under the tail above
  \(\lceil d\beta \rceil\).
- `neverNegCount_div_pow_le_theta`:
  \(N_d/2^d \le \theta(\beta)^d\), endpoint tilt \(q = \beta\) (the
  published proof tilts at the midpoint; the upper bound needs no
  threshold admissibility).
- `neverNegCount_div_pow_tendsto_zero`: \(N_d/2^d \to 0\).
- `neverCertified_density_zero`: under `FairClasses`, the
  never-certified starts have natural density zero — the conditional
  Theorem 6.1 assembled end-to-end, using
  `uncertifiedCount_eq_sum` for the union step and
  `exceptional_density_zero` for the limit order.
- Kernel values: \(N_1..N_8 = 1, 1, 2, 3, 4, 8, 13, 19\); the depth-5
  survivors are exactly \(\{OOOOO, OOOOE, OOOEO, OOEOO\}\)
  (`neverNegWords_five`), the word count behind Corollary 6.4's
  \(7/8\) (`uncertified_fraction_depth_five`); \(N_6 = 8\) is the
  ledger's "all eight children survive".

## Open questions

FD itself: `juggler_tower_rate_free_equidistribution`. The exact
exponential rate of \(N_d/2^d\) (the tilted walk sits at
\(-\log \rho = 0.034688\), one part in eighty sharper than the Hoeffding
majorant) is recorded in `J-equidistribution-implies-density-one` and
not formalised here; neither is the \(d^{-3/2}\) prefactor.

## Decision

**PROMOTE.** The last unformalised link of the rate-free density-one
reduction is now kernel-checked, and the conditional Theorem 6.1 is a
single Lean theorem with FD as its only hypothesis. Best next question:
the exact rate — can the tilted-walk sharp value
\(-\log \rho = 0.034688\) (large deviations for the barrier walk, not
the endpoint-only Hoeffding) be brought into Lean, replacing
\(\theta(\beta)\) by the true rate? Do not continue automatically.

## Publication assessment

Status: `THEOREM` (kernel-verified combinatorics and a conditional
assembly). No manuscript edit: Paper B's Theorem 6.1 already prints the
conditional statement and the \(7/8\) figure; this branch machine-checks
what the manuscript asserts, it does not extend it.
