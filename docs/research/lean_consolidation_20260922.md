# Lean and publication consolidation — 22 September 2026

The recent formal developments are integrated, the paper releases have been
rebuilt, and their different proof boundaries remain explicit. This pass
adds a reusable conditional corollary, not an unconditional termination theorem.

## Mathematical consolidation

[FateScaleAverage.lean](../../formal/Problems/Juggler/FateScaleAverage.lean)
now accepts a precise failure-mass lower bound at any exponent
`0 < lambda <= 1`. The scale-average reduction then needs
`r - eta > 1 - lambda`. Its existing public declarations keep their signatures
and specialize to the unconditional contagion exponent `100/203`.

The new `pressure_average_conjecture_of_ooee` composes that same proof with
the existing OOEE transfer. Its threshold is `r - eta > 3/8`, with both
`OOEEProductionBound` and the actual cumulative pressure `Bound` explicit.
The generalization removes duplicate argument structure and makes a future
contagion improvement usable without rewriting the pressure proof.
The scale-average dependency audit now covers fourteen theorems, all using
only `propext`, `Classical.choice`, and `Quot.sound`.

The new ledger row is temporarily `EXACT — HUMAN PROOF`. Its compiled Lean
statements were compared directly with the English claim, but the repository's
separate advisory coverage step awaits permission to send the unpublished
statement and declarations to Jev. No old advisory verdict is attributed to
the new row.

## Publication state

| Paper | Local version | Consolidated change |
|---|---|---|
| A | 1.2.0 | Wu–Wang asymptotic transfer is included in the actual paper barrel and dependency audit; explicit finite bounds and the verified floor are unchanged. |
| B | 1.1.1 | Attribution and provenance corrected; its extracted source archive reproduces the canonical TeX and PDF byte for byte. |
| C | 1.2.0 | Written 5/8 contagion, complete poor-fibre appendix, scale-average criterion, and its conditional Lean corollary are stated separately from the unconditional 100/203 Lean baseline. |
| D | 1.1.0 | Checked and retained; no mathematical rewrite was needed. |
| E | 0.6.0 | Effective OOE theorem and detailed quantitative appendix are included, while the remaining Lean counting and witness assembly are identified. |

These are local releases. Deposited version history was preserved. All five
PDFs were rendered and inspected, including the revised mathematical passages.
Paper C is now 69 pages after the final explanatory paragraph.

Paper A's 126 non-editorial inputs are pinned to commit
`07482692b91ee8a6f5a0d2d6f4562a71f9dab8a9`. The pin covers its expanded audit
and the repaired publisher. Its metadata and manifest now use atomic writes,
so a Windows sharing violation cannot truncate the previous record.

## Verification and maintenance

- Full default Lean build: **9,082 jobs, successful**, with no compiler warnings.
- The 33 recently changed dependency-audit scripts produced **790 reports**
  without failures. The subsequent scale-average and expanded Paper A audits
  also passed; Paper C's historical 473-report audit was independently rerun.
- Paper C's numerical/certificate checker passed all **83 checks**.
  Paper A's published period-floor table and Paper E's finite checks passed.
- The module inventory now checks the exact auxiliary-module registry rather
  than a stale numerical allowance. Temporary builds and dependency copies
  no longer masquerade as consumers in the Lean hygiene scan.
- The ledger, branch index, theorem index, dependency graph, publication
  manifests, and reviewer mirrors were regenerated and checked together.
- Python validation covers all **6,949 collected tests**: **6,612 passed,
  337 skipped, no remaining failures or collection errors**. These are the
  combined latest results of the broad run and the focused corrective run
  (541 passed, 20 skipped). The latter reran the release/index checks after
  publication stabilized and collected the omitted files with the repository's
  required `--import-mode=importlib`. This was not a single clean full-suite run.

The machine-readable [validation record](../../data/research/consolidation_20260922/validation.json)
retains both runs and the subsequent clean outcomes.

## Most useful next theorems

1. **Paper C: complete the actual OOEE production bound.** The joint parity
   theorem is already available on its stated source windows. The remaining
   work is exact target-fibre geometry, poor-target inclusion, reciprocal-tail
   conversion, and physical cutoffs. Completing those steps would connect the
   written 5/8 result to an unconditional Lean contagion theorem.
2. **Paper E: finish Q4 and Q5.** Uniform effective OOE Fourier modes are
   proved. The next assembly is the effective box count and bounded witness,
   with the advertised constants and modulus dependence preserved.
3. **Termination: the actual pressure estimate.** The reusable reduction now
   makes the required input precise. The estimate remains open; neither fixed
   depth parity counts nor this refactor supplies it.

Decision: **PROMOTE** the formal consolidation and conditional corollary;
**PARK** the outstanding arithmetic estimates. No new attack was opened and
the verified floor remains `N_0 = 350000000`.
