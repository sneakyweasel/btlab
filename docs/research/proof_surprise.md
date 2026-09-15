# Proof surprise: a language model's view of the checked proofs

Status: **PARK**

Tooling on the seed, not a Juggler claim. Scores every kernel-checked
tactic-mode proof in `formal/` by how surprising a language model finds
it given its statement and the file before it. No training. The kernel
had already accepted every record; this asks only how far each proof was
from obvious. Scorer: [tools/seed/score_proofs.py](../../tools/seed/score_proofs.py).
Output: `data/seed/proof_scores.csv` and
[data/seed/proof_scores.summary.txt](../../data/seed/proof_scores.summary.txt).

## Branch budget

```text
Mathematical target     Does a model's surprise at a kernel-checked proof, given its
                        statement, separate routine proofs from ones worth a second look?
Novelty hypothesis      "Elegance" as surprise given the statement plus kernel acceptance
                        may surface lemmas that deserve a docstring, a generalization,
                        or a cheaper proof.
Falsifier               The ranking is length, slicing artefacts, or unpredictable numerals
                        rather than mathematics.
Already killed by?      none: no prior branch scores proofs with a language model.
Existing machinery      tools/seed/extract_seed.py and data/seed/seed.jsonl (peer session,
                        untracked), formalpedia trust tags, Qwen3-8B-Base, .venv-seed.
Maximum Phase-0 scope   Score every tactic record once; one CSV; one note; no training.
Promotion criterion     Top twenty are non-obvious to a reader and the ranking is not
                        explained by length (rank correlation below 0.5).
Stop criterion          Ranking explained by length or artefacts, or nothing in the top
                        twenty a reader would call interesting.
```

## Metadata

- model: `Qwen/Qwen3-8B-Base`, bfloat16, one RTX 5090, about twenty minutes
- records: 4280 tactic-mode proofs from 5622 kernel-trust theorems; the 56
  `compiler`-trust declarations are excluded by the extractor
- setup: the last 1536 tokens of the source file before the declaration, then
  the statement up to `:= by`; the proof is cut at 1024 tokens (562 records
  truncated or shorter than 12 tokens are excluded from the rankings)
- per record: surprise given the setup (total and per token), surprise with no
  setup, their difference, max of surprise minus entropy, surprise of the
  first tactic word, rank of the least expected token

## Results

**The confounds named in the falsifier are absent.** Rank correlation of
per-token surprise with proof length is -0.08, and with the fraction of digit
characters in the proof is -0.12; the twenty most surprising proofs carry
fewer numerals than the corpus average. Per-token PMI, by contrast, is almost
pure length (-0.95 with length) and is reported but not used to rank.

**Proofs are predictable.** Median surprise is 0.64 nats per token; the
10th and 90th percentiles are 0.13 and 1.20. Given the file before it, a
proof in this repository is mostly foreseeable to an 8B model.

**The bottom of the ranking is a copy map, and that is the useful output.**
278 proofs (6.5%) score under 0.05 nats per token, which means the proof is
a near-verbatim copy of one earlier in the same file. They total 17715 proof
tokens. Where they live:

| file | near-copy proofs | proof tokens |
|---|---:|---:|
| `Problems/Juggler/LeftoverFamilies.lean` | 25 | 3714 |
| `Problems/Juggler/LeftoverEval.lean` | 24 | 112 |
| `Problems/Juggler/DepthFourFive.lean` | 13 | 183 |
| `BTCalculus/Trit.lean` | 12 | 161 |
| `Problems/Juggler/FateSweepMonotone.lean` | 8 | 922 |
| `Problems/Juggler/CycleFinanceLeftovers.lean` | 6 | 1309 |

The largest copies are 300 to 560 tokens each: `eoee_tail_six_succ`,
`localDefectOdd_seven_mod_eight`, and the `no_cycle_itinerary_*` family
spread over `SmallCycleCensus`, `LengthEightCensus`, `CycleObstructions`,
`LeftoverFamilies` and `CycleFinanceLeftovers`. Each family is a candidate
for one parametrised lemma in place of its copies. That refactor is not
opened here.

**The top of the ranking is mixed.** The twenty most surprising proofs (2.1
to 3.1 nats per token) are of three kinds: the first lemma of a family whose
later members then score near zero (`follows_eoo_two` at 2.66 against
`follows_eoo_twelve` and `_fourteen` at 0.001), short certificate lemmas
whose content is a specific computation (`exponent_A`, `c_certificate`), and
proofs whose route is genuinely unusual for their statement (`height_strip`,
`cycle_remainders_project_to_envelope`, `guard_int_sqrt_cell`,
`cycleMin_finance_inv_sum`, `low_odd`). The metric does not separate the
three kinds; a reader does.

**Opening moves.** Surprise of the first tactic word ranks the proofs that
begin unusually: `symm` in `cube_fiber_sqrt_even` (9.3 nats), `interval_cases`
in `eoo_sqrt_cube_pow_of_small`, `wlog` in `fourth_window_occupancy`,
`three_zpow_inj` and `three_pow_inj_of_dvd`, `generalize` in
`RankedReturn.primitive_terminal` and `any_word_separation`. By first tactic,
`omega` and `decide` proofs are the most surprising per token (1.64, 1.19)
and `cases` and `ext` the least (0.56, 0.55).

## Decision

**PARK.** Half the promotion criterion holds: the ranking is not length and
not numerals. The other half, that the top twenty are non-obvious to a
reader, is a judgment this session cannot make alone, and the top is visibly
a mixture. What the scorer does establish is a map of copied proofs, which
is a maintenance result rather than a mathematical one.

Priced next steps, none opened here:

- A reader rates the twenty most surprising proofs; if most are the third
  kind, the elegance reading is worth a second pass with the first-of-family
  and certificate cases filtered out.
- The header-only setup (`--header-only`) measures how much of each proof
  needed names the statement does not give; one more twenty-minute run.
- In the local-prover loop, keep per-token surprise as an information column
  next to proof length. The kernel stays the only reward.
- The copy families are refactor candidates for whoever next works those
  files; the list is in the summary file.
