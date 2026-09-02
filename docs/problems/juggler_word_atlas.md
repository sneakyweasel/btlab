# Juggler word atlas

Status: **EXPLORATORY**

Standalone computational microscope for the finite Juggler \(O/E\)
word language. It is **not** a Research Engine control-layer
experiment, not a reopening of the closed word-language attack, and
not a claim that every positive integer reaches 1.

## Problem

Build a reusable, exact, GPU-first census of finite \(O/E\) words:
which words are observed under a configured bound, with minimum
witnesses and separate language tags.

## Exact statement

Keep the quantifiers existential. An itinerary is experimentally realized
when some scanned \(n\) follows it. Failure to find a realizer is

\[
\texttt{NOT\_FOUND\_WITHIN\_BOUND},
\]

never global non-realizability. Persistent-expanding rows use the
repository predicate `PersistentExpandingResidual` and are stored as
`PE_CERTIFIED`. The GPU does not classify PE in Milestone 1.

This says nothing about totality.

## Current literature

- `follows` / `image` / `floorPower` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary` and
  `Dynamics`.
- `PersistentExpandingResidual` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- Existential languages `jugglerLanguage` /
  `expandingLanguage` / `persistentExpandingLanguage` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.ItineraryLanguage`.
- Word-language arrangement attack —
  **CLOSE** as `JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`. This atlas does
  not reopen that claim.

Project relationship: **extended** (infrastructure on existing
predicates).

## Branch budget

```text
Mathematical target     Build a reusable, exact, GPU-first census of
                        finite O/E words: which words are observed
                        under a bound, with min witnesses and
                        separate language tags.
Novelty hypothesis      None in M1. This is infrastructure for later
                        questions, not a new forbidden-factor law.
Falsifier               GPU itinerary disagrees with the CPU/Lean
                        floorPower/follows fixtures, or PE_PROXY is
                        written as PE_CERTIFIED.
Existing machinery      floor_power, follows_itinerary, classify_step,
                        walk_pe_run, ItineraryLanguage.lean, closed
                        itinerary_language.py prototype
Maximum Phase-0 scope   Milestone 1 only: k<=12, n<=10^6, Kernel A,
                        compact tables, validation, manifest
Promotion criterion     Not applicable in M1. Default is PARK as
                        machinery after the validation suite passes.
Stop criterion          Machinery gravity (Kernel B, Nsight campaign,
                        automata, new conjecture); any claim that
                        absence under a bound is global prohibition
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Packed \(O/E\) words, LSB = first symbol, `0=E`, `1=O` —
  **OBSERVATION** (encoding only)
- Observed `min_realizer` under a scan bound —
  **COMPUTATIONALLY VERIFIED**, not a global minimum theorem
- `PE_CERTIFIED` via `classify_step` / `walk_pe_run` —
  **COMPUTATIONALLY VERIFIED** against Lean fixtures
- `PE_PROXY` — unused in Milestone 1; must not be mixed with
  `PE_CERTIFIED`
- Factor complexity \(p(r)\) as a query over observed words —
  **OBSERVATION**; absence is `NOT OBSERVED WITHIN SEARCH BOUND`

## Experiments

- Engine: `atlas/` CUDA/C++ census (`juggler-atlas-census`)
- Python API: `research.juggler_sequence.atlas`
- CLI: `juggler-atlas build|validate|factors|continuations|benchmark|science`
- Data: [word_atlas](../../data/research/juggler/word_atlas/)
- Graph reading: [juggler_atlas_graph.md](../research/juggler_atlas_graph.md)
- Milestone 1 window: word length \(\le 12\), \(n\le 10^6\)
- Scientific census (2026-08-27): \(k\le 20\), \(n\le 10^8\),
  `PE_CERTIFIED` scan \(n\le 10^7\), experiment
  `wa-20260827T200310Z-cuda-k20-n100000000`
- Tests: `tests/research/juggler_sequence/test_word_atlas.py`

## Conjectures

None opened in `conjectures/`.

## Counterexamples

None. This branch is infrastructure. Closed-branch counterexamples
stay in `juggler_word_language.md`.

## Formalization

None added. Certification uses existing
`formal/Problems/Juggler/` lemmas and hard-coded fixtures. No Lean
FFI. No `sorry`.

## Results

Milestone 1 ships a deterministic trajectory census, compact
Parquet/SQLite tables, a `PE_CERTIFIED` host post-pass, and a
three-way validation gate. On this machine Kernel A matched the
Python exact reference on every filled slot for `k<=12`,
`n<=10^6` (`GPU VERIFIED`; wide intermediates overflow to the
CPU reference). Fixtures `floorPower`, `OOE` at 5, and the 365 /
1999 PE chains match Lean (`CPU VERIFIED` / `LEAN-CERTIFIED`).
Stored word metadata recomputes from packed bits. No new
language law is claimed.

Scientific census `wa-20260827T200310Z-cuda-k20-n100000000`
(`COMPUTATIONALLY VERIFIED` as a bounded observation, not a
theorem):

- Realizable words fill every binary string for \(k\le 5\). First
  prefix gap at \(k=6\): `EEEEEE`, `EEEEOE`, `EEEOEO` are
  `NOT OBSERVED WITHIN SEARCH BOUND` as rooted prefixes. They
  are the three lost children of the first unary nodes
  `EEEEE`, `EEEEO`, `EEEOE`. As interior factors of stored
  length-\(20\) realized prefixes they are common (`EEEEEE`
  occurs \(3948\) times, never at position \(0\)). The
  REALIZABLE `factors` table stores prefixes, not substrings.
  Graph reading: [juggler_atlas_graph.md](../research/juggler_atlas_graph.md).
  At \(k=20\), 132398 of 1048576 words are realized under
  \(n\le 10^8\).
- `p_{\mathrm{PE}}(r)=r+1` for \(r\le 8\), the single-block
  \(O^a E^b\) factor count.
- Every grammar-legal PE-run factor for \(r\le 8\) is
  `COMPUTATIONALLY OBSERVED`. Known late window factors
  `EEEEEE` (14237) and `OEEEEO` (9157) appear in `PE_RUN`.
- Binary PE-run absences begin at `EOEO` (\(r=4\)) and are the
  known \(a\ge 2\) block grammar, not a new law.
- Host PE scan to \(10^7\) found 715855 `PE_CERTIFIED` blocks
  and 9832 distinct PE-run words. GPU overflow merge: 5491117
  starts.

## Open questions

The PE-factor scale-up question is answered inside the stated
bound: no extra PE-run constraint beyond the known \(O^a E^b\)
grammar survived. The leftover mathematical question is unchanged:
is there any arithmetic, other than the integer \(y\) itself, that
decides whether a persistent residual landing stays odd-to-odd?
The atlas does not answer it. Do not reopen
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.

## Decision

**PARK** as reusable machinery. The \(k\le 20\), \(n\le 10^8\)
census is a bounded observation. It does not promote a new
forbidden-factor law, does not reopen
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`, and does not prove totality.
Absence remains `NOT OBSERVED WITHIN SEARCH BOUND`.

Best next question: is there any arithmetic, other than the
integer \(y\) itself, that decides whether a persistent residual
landing stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. A computational census pipeline, not a paper
candidate and not a Juggler totality result.
