# Paper D: build, and what it rests on

**No m-cycles of the 3n−1 map for m ≤ 61.** The Simons–de Weger template transposed to the
negative side, from this laboratory's own verification floor.

Canonical source: [collatz_3n_minus_1_m_cycles_note.md](collatz_3n_minus_1_m_cycles_note.md).
Edit that file, never a generated copy.

```
python tools/build_paper_d.py            # rebuild the PDF, the TeX, the metadata and the kit
python tools/build_paper_d.py --check    # verify every generated copy against the manifest
python tools/build_paper_d.py --sync     # refresh the exports without recompiling
```

The build needs Pandoc and XeLaTeX; `--check` and `--sync` need only the standard library.
The release gate `tests/integration/test_paper_release_gates.py` discovers this builder and
calls `check()` on the live repository, so a source change that stales the PDF fails the
suite rather than going quiet.

Outputs: `juggler_review/collatz_3n_minus_1_m_cycles_note.pdf` (the one copy in the
repository), `docs/theory/cochin-3n-minus-1-m-cycles.tex`,
`docs/theory/paper_d_zenodo.json`, the manifest `docs/theory/paper_d_release.json`, and the
deposit kit `juggler_review/zenodo_paper_d/`. Logs and the working TeX go to
`.build/paper_d/`.

## The trust boundary

Three different kinds of claim sit in this paper, and the manifest checks none of them. It
checks that the files agree with each other.

**Proved here, by hand.** Lemmas 1 to 6, Proposition 7 and Theorem 8. Lemma 2's bound on
\(\Lambda\) and Lemma 5, the sieve the verification floor rests on, are the two whose
proofs a referee should read first.

**Proved here, and machine-checked.** Lemmas 1 and 3, as
`Problems.Collatz.NegativeMCycles`: twenty declarations, in the `Problems` barrel, thirteen
on Mathlib's three standard axioms and five on none at all, no `sorry` and nothing off the
kernel. `lake build Problems` covers it;
`tests/research/juggler_sequence/test_negative_m_cycles_lean.py` holds it to that standard.
Lemma 2 is **not** in Lean: its content is real-analytic.

**External, and taken on trust.** Rhin's effective measure, [R87, p. 160, (7)]. Nothing here
re-proves it and no Lean statement carries it. Theorem 8 is conditional on it and says so.

**Computed, not proved.** The verification floor: every \(1 \le y < 2^{51}\) reaches 1, 5 or
17. Below \(2^{44}\) that is the CPU certificate of 19–20 September 2026, above it the GPU
sweep of 21 September 2026. It is this laboratory's computation, not a result from the
literature; no published floor for this map was found. The certificate, its chunk reports,
the calibration against the CPU walker and the three spot-check windows are archived under
`data/research/juggler/negative_floor_3x1/`.

**Computed, and recomputed.** Every number in Tables 1 and 2. The probe
`src/research/juggler_sequence/negative_m_cycles.py` produces them by a three-gap walk;
`tools/check_3n_minus_1_note_numeric.py` recomputes them from scratch by an integer sieve,
re-derives every ceiling, margin and killing floor at 120 digits, and compares the result
with the manuscript's own tables. It passes, and it fails on a copy of the manuscript with a
single wrong digit.

## What the paper does not claim

It does not settle the \(3n-1\) cycle question: \(m\) is bounded, not the cycle count. It
says nothing about divergence, on either map. It excludes no Juggler cycle. It does not
improve the \(3n+1\) results it transposes; run on that side it reproduces Simons–de Weger's
Lemma 18, which is the calibration, not a new result.

## Version and the floor

Version 1.1.0 carries the floor \(2^{51}\) and the theorem \(m \le 61\); version 1.0.0 proved
the same theorem for \(m \le 58\) and lacked Lemma 6. The floor is the only moving part:
\(2^{56}\) gives \(m \le 68\) and \(2^{60}\) gives \(m \le 74\), at about 32 hours and about
21 days of one RTX 5090 respectively. Raising it is a new version of the
record, not a correction, and the build's `SOURCE_DATE_EPOCH` and the `VERSION` constant in
`tools/build_paper_d.py` both move with it.

## Deposit

The kit is `juggler_review/zenodo_paper_d/`: the PDF under its deposit name, the field sheet
`ZENODO_FIELDS.txt` generated from `paper_d_zenodo.json`, the checksums, and a README. A
build prepares local metadata only; it never creates or updates an external record.

**Deposited 21 September 2026**, version 1.0.0: version DOI
[10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190), concept DOI
[10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189), record
[zenodo.org/records/22876190](https://zenodo.org/records/22876190), with the author's ORCID
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382) attached. The deposited file has
md5 `c6f6f662016ca30a859bf57b0cc81793` and was byte-identical to the kit copy and to the
repository's single PDF on the day it was deposited, checked against the record.

That identity has ended: the repository now holds version 1.1.0, so the kit PDF is a different
file. While it held, the manuscript deliberately did **not** carry its own DOI, because editing
the text to add one would have broken it. The DOIs entered the text at 1.1.0, as planned. A rebuild from an unchanged source reproduces the deposited bytes, since
`SOURCE_DATE_EPOCH` is pinned; a rebuild after any source edit does not, and at that point
the kit stops being the deposited file and `AFTER_ZENODO.md` should say so.
