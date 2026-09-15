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

**The three kinds, separated.** `tools/seed/rank_unusual.py` tags every proof:
`copy` (mean surprise under 0.05), `template` (an earlier proof that a later
near-copy in the same file resembles at difflib ratio 0.8 or more),
`certificate` (short `decide` or `norm_num` proofs, or a digit fraction above
0.12), and `unusual` for the rest. Counts: 3651 unusual, 278 copies, 155
templates, 196 certificates. The filter matters less at the top than feared:
of the twenty most surprising proofs, 16 are unusual, 2 templates, 2
certificates. The twenty most surprising unusual proofs, with statements and
proofs, are in `data/seed/rating_sheet.md` for a reader to mark routine, neat,
or wrong-list. Reading the first six: their surprise sits on which lemma is
called (`exact_return_seam`, `cubic_return_height_algebra`,
`power_bound_word` through `image_eq_iterate`) and on which simp set is fed,
not on tactic structure. Short proofs by a well-chosen lemma are the good
kind of surprising in a library; `tools/seed/surprise_by_token.py` is written
to test that reading by splitting surprise across identifier, tactic, numeral
and structure tokens.

**Header-only versus file-prefix.** The same 3718 proofs scored with only the
header context (`--header-only`, `data/seed/proof_scores_header.csv`):
mean surprise 1.24 nats per token against 0.67 with the file prefix, and the
two rankings agree only weakly (Spearman 0.38). The file explains 42% of the
surprise of unusual proofs, 48% of templates, 59% of certificates and 99% of
copies. Without the prefix a length confound appears (Spearman with length
-0.45), so the prefix setup is the right one and stays the default. The
proofs that remain surprising with the prefix and barely change without it
(`height_strip`, `cubicResid_one_neg`, `succIdx_val_of_lt`,
`warp_wordThree`, `guard_int_sqrt_cell`, `low_odd`) are the residue: their
surprise is not about the file they sit in.

**Where the surprise sits.** `tools/seed/surprise_by_token.py` on the 200
most surprising unusual proofs against 200 from the middle of the ranking:

| token class | top 200: share of surprise, nats per token | middle 200: share, nats per token |
|---|---:|---:|
| identifier | 63.6%, 2.08 | 50.5%, 0.82 |
| tactic keyword | 10.2%, 2.00 | 13.6%, 1.26 |
| structure | 22.2%, 1.36 | 27.8%, 0.58 |
| numeral | 1.8%, 0.80 | 3.9%, 0.42 |

The top proofs are surprising because of which names they call, two and a
half times more surprising per identifier than the middle, while tactic
keywords are only modestly more surprising. Read plainly: what the model
cannot foresee in this repository is premise selection, the choice of
lemma, not tactic structure. That is the direct design consequence for the
local-prover loop: the hard part is retrieval of lemma names, so the loop
should show the prover candidate premises (the formalpedia index is already
the retrieval surface) rather than rely on the model to guess them.

**Incongruity is a different list.** Ranking unusual proofs by the largest
surprise-minus-entropy token gives `cell_eq`, `carry_eq_floor_shifted`,
`carry_identity`, `balWidth_mul_pow`, `mem_oeFiber`: long proofs with one
token the model was confident about and wrong. Not yet inspected.

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
reader, is a judgment this session cannot make alone; the rating sheet is
ready for it. What the scorer does establish is two things short of an
elegance measure: a map of copied proofs, which is a maintenance result, and
the finding that the model's surprise in this repository is mostly about
which lemma is called. The second is the one that changes the local-prover
design, and it transfers to the loop as a retrieval requirement rather than
as a reward.

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
