# Juggler cycle Fourier / peak–valley spectrum

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md), not a new
paper. It asks whether the closed peak–valley wave of a hypothetical
Juggler cycle imposes a spectral constraint strong enough to reduce
the finance error budget below the current 99-survivor run-type
packing. Not a halt theorem, not a leftover-itinerary census, not a
residue / \(p\)-adic system, not a \(Q\)-return section, and not a
terminal-cluster reopen.

## Problem

A `CycleMin` orbit is a closed log-state sequence
\(t_{j+1}=a_j t_j-\varepsilon_j\) with \(a_j\in\{1/2,3/2\}\) and
\(\varepsilon_j\ge 0\). Valleys are the cyclic even-to-odd landings.
Does the discrete Fourier transform of \(t\) or of the valley
indicator forbid a finance-expensive valley occupancy that the
run-type packing still allows?

## Exact statement

Write \(\hat t(k)=\sum_{j=0}^{L-1}t_j e^{-2\pi i jk/L}\) and
\(\Delta t_j=t_{j+1}-t_j\). On any real \(L\)-periodic sequence,

\[
\sum_j(\Delta t_j)^2
=\frac4L\sum_{k=0}^{L-1}\sin^2\frac{\pi k}L\,|\hat t(k)|^2.
\]

This is the classical Parseval increment identity.

On any Juggler orbit or abstract wave
\(t_{j+1}=a_j t_j-\varepsilon_j\) with \(a_j=1+s_j/2\) and
\(s_j=\pm 1\),

\[
\sum_j(\Delta t_j)^2
=\frac14\sum_j t_j^2-\sum_j s_j t_j\varepsilon_j+\sum_j\varepsilon_j^2.
\]

Combining and using \(\sum_k|\hat t(k)|^2=L\sum_j t_j^2\),

\[
\frac{\sum_k\sin^2(\pi k/L)\,|\hat t(k)|^2}{\sum_k|\hat t(k)|^2}
=\frac{\sum_j(\Delta t_j)^2}{4\sum_j t_j^2}.
\]

When \(\varepsilon\ll t/2\) the right side is \(1/16\) plus an
explicit defect remainder. Every cyclic sequence with
\(|\Delta t_j|\approx t_j/2\) achieves this moment, independently of
how the valleys sit. The identity is a **REPARAMETERIZATION** of the
one-step O/E law.

For \(n\ge 12\) one has \(\varepsilon_j\le(6/5)/x_{j+1}<t_j/2\), so
\(\mathrm{sign}(\Delta t_j)=s_j\). The number of cyclic sign changes
of \(\Delta t\) equals the number of O/E transitions, which is
\(2m\). This is time-domain combinatorics, not a spectral bound on
\(m\).

The power spectrum of \(t\) weights large log-states (peaks). The
finance sum \(\sum 1/(x\ln x)\) weights small states (valleys). A
bound that only uses \(|\hat t|\) therefore cannot cut valley
occupancy below the run-type packing
\(o-e\) copies of `OOE` and \(2e-o\) copies of `OE`.

A band-limit argument \(m\le K\) would need the tail
\(\sum_{\min(k,L-k)>L/12}|\hat t(k)|^2\) to be negligible. It is
not: on every short closed wave and every control excursion the tail
fraction is at least \(0.05\). High modes of \(\Delta t\) are
amplified by \(|\omega^{-k}-1|\).

No cycle of any length — not claimed.

## Current literature

- Length-only parity finance and run-type packing —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_finance.md](juggler_cycle_finance.md),
  [juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md));
  \(\mathcal E_{\mathrm{run}}(10^6)\) has \(99\) leftovers
- Cyclic run-type leftover-killer — **REFUTED**
  (`juggler_cycle_run_extremum_leftover_killer`)
- Christoffel / mechanical unique maximizers — **REFUTED**
  (`juggler_christoffel_one_parameter`)
- Prefix-weight leftover-killer — **REFUTED**
  (`juggler_cycle_prefix_weight_leftover_killer`)
- Discrete Parseval / Wirtinger on periodic sequences — **known**
- Collatz \(m\)-cycle financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover killer; the spectral
moment is **known** Fourier calculus applied to the existing
increment law.

## Branch budget

```text
Mathematical target     Does the closed peak–valley wave of a hypothetical
                        Juggler cycle impose a spectral constraint strong
                        enough to reduce the finance error budget?
Novelty hypothesis      Peak/valley recurrence cannot be arranged arbitrarily.
                        A cycle with many finance-expensive valleys requires
                        spectral energy/high-frequency content that is
                        incompatible with the exact O/E transition law.
Falsifier               Fourier representation is merely cosmetic; every
                        relevant spectral bound is achievable by abstract
                        cyclic waves satisfying the known transition
                        inequalities; or the resulting spectral estimate
                        is weaker than the current 99-survivor run-type
                        finance bound.
Existing machinery      CycleMin; AboveAnchor; run-type finance;
                        parity/run RHS; odd/even one-step log bounds;
                        power_bound_word; peak/valley decomposition;
                        365 / 1517 / 501 / 6187 controls
Maximum Phase-0 scope   Fourier discovery only; cycle lengths in the
                        99-survivor set plus controls; log-state and
                        valley-state spectra; exact algebraic inequalities;
                        no Lean initially; no residue/p-adic system;
                        no Q-return section; no terminal-cluster reopen
Promotion criterion     A reusable spectral inequality that constrains
                        finance-expensive valley occupancy and produces
                        a strictly smaller exact finance RHS than the
                        current run-type packing.
Stop criterion          spectra show no forbidden structure; all spectral
                        bounds follow from arbitrary periodic sequences;
                        only numerical correlations; Fourier merely
                        re-expresses closure; or the result is weaker than
                        run-type finance.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Parseval increment identity —
  **REPARAMETERIZATION** (classical DFT)
- O/E increment identity
  \(\sum(\Delta t)^2=\tfrac14\sum t^2-\sum s t\varepsilon+\sum\varepsilon^2\) —
  **EXACT — HUMAN PROOF** (this dossier; one-step law rewritten)
- Spectral moment \(1/16\) —
  **REPARAMETERIZATION** of the two identities
- \(\mathrm{sign}(\Delta t)=s\) and \(\#\)sign-changes \(=2m\) for
  \(n\ge 12\) — **EXACT — HUMAN PROOF**
- Band-limit \(m\le L/12\) — **REFUTED** (tail \(\ge 0.05\))
- Spectral leftover-killer on \(\mathcal E_{\mathrm{run}}(10^6)\) —
  **REFUTED** (`juggler_cycle_fourier_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_fourier`
- Dataset: `data/research/juggler/cycle_finance/cycle_fourier/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_fourier.py`
- Window: the \(99\) run-type leftovers at \(n=10^6+1\); controls
  \(365,501,1517,6187\); bunched witness \(L=19\); identity word
  `OOEOOE`. Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_fourier_leftover_killer` — **REFUTED**.

## Counterexamples

- Closed increment waves of a mechanical `OOE`/`OE` necklace and of
  the bunched word \(O^o E^e\) both have spectral moment \(1/16\) at
  \(L=19\), with \(m=7\) versus \(m=1\). Many valleys are not
  spectrally forbidden.
- On every one of the \(99\) leftovers the closed run-type wave
  hits moment \(1/16\), sign-changes equal \(2m\), and the packed
  height assignment reproduces `budget_rhs`. None is excluded.
- Controls \(365,501,1517,6187\) have cyclic moment in
  \([0.0618,0.0628]\) and tail past \(L/12\) at least \(0.095\).
- Valley-indicator tails at \(L=19\) and \(L=84\) are \(\approx 0.63\):
  the \(0\)-\(1\) spike train is high-frequency, not a constraint.

## Formalization

None. No `CycleFourier.lean`. Paper A is unchanged.

## Results

- **Spectral moment** — **REPARAMETERIZATION**. On the expanding
  identity word `OOEOOE` both exact identities hold. At
  \(n=10^6+1\), every one of the \(99\) closed run-type waves has
  moment \(1/16\) to \(10^{-8}\) or better; sign-changes equal
  \(2m\); packed heights reproduce `budget_rhs`.
- **Arrangement independence** — **COMPUTATIONALLY VERIFIED**.
  At \(L=19\) the bunched wave (\(m=1\)) and the mechanical
  run-type wave (\(m=7\)) both hit moment \(1/16\). Bunched
  prefix-powers overflow the float window on leftover lengths, which
  is peak-scale, not a spectral prohibition of valleys.
- **No leftover dies** — **COMPUTATIONALLY VERIFIED**
  (`cycle_fourier/summary.json`): spectral_killed is empty. First
  survivor remains \(25781\)
  (\(\theta\approx 2.55\cdot 10^{-5}\) versus packed/budget RHS
  \(\approx 5.89\cdot 10^{-4}\)). \(L=55293\) still lives.
- **Controls** — **OBSERVATION**. The four leftover seeds drop
  after \(13\)–\(23\) steps. Wrapped log-spectra sit at the same
  moment and do not band-limit.
- **Band-limit** — **REFUTED**. Tail past \(k=L/12\) is
  \(0.088\) on the \(L=84\) closed wave, \(0.088\) on the \(L=19\)
  closed wave, and \(0.095\)–\(0.125\) on the controls. Valley
  indicators carry \(\approx 0.63\) of their energy in that tail.

## Open questions

None from Fourier. The moment is the increment law. Valley
occupancy remains a time-domain packing question, already decided
by run-type finance and the cyclic-run extremum.

## Decision

**CLOSE**. Fourier re-expresses the O/E increment law as a spectral
moment \(1/16\). Every abstract cyclic wave with \(|\Delta t|\approx t/2\)
achieves it, including both the finance-expensive mechanical
`OOE`/`OE` necklace and the finance-cheap bunched word. The
log-state \(L^2\) mass sees peaks; finance sees valleys. No
certified RHS beats `budget_rhs` on any of the \(99\) leftovers.
Keep the two identities as negative knowledge. No Paper A edit, no
ledger row, no Lean.

Best next question: none from Fourier.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
