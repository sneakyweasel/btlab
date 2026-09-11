# Paper A reviewer packet

**Lower Bounds for Cycle Lengths in the Juggler Map**

Philippe Cochin; no affiliation. Local preprint revision: 11 September 2026.

This packet accompanies Paper A. Its purpose is to identify the claims,
their evidence, and the questions requiring mathematical review. The
revision has not been uploaded as a new Zenodo version. AI tools were used
throughout the prose, proof development, Lean code, and computations.
AI review is not independent human mathematical review.

## Canonical sources and review object

The editorial source is
[the manuscript](juggler_finite_dynamics_note.md), with
[the formalization map](juggler_finite_dynamics_formalization.md) and this
packet as supporting inputs. Edit these files only in `docs/theory/`.
The corresponding files in `juggler_review/` and all distributed PDFs are
generated copies. The [build guide](PAPER_A_BUILD.md) gives the commands.

The Lean review object is `formal/Problems/JugglerPaper.lean`:
run `lake build Problems.JugglerPaper` from `formal/`.
The laboratory barrel `Problems.Juggler` contains additional research and
is not the paper's review object. Appendix A maps each printed formal
claim to its declaration. The accompanying cited-declaration dependency
audit checks that the paper cites exactly the declarations it audits.

## Main conclusions

The financing inequality is
\[
n\log n\,(3^o-2^L)\le L3^o
\]
for a hypothetical nontrivial cycle with minimum n, period L and odd count o.
The four published period lower bounds remain
\(25781,176251,478245,780239\), at the respective certified descent
floors \(10^6,26254995,162849448,350000000\).
Those descent computations are inputs, not consequences of a checksum.
Neither universal termination nor exclusion of every nontrivial cycle is
claimed.

For a primitive cycle with minimum m and maximum \(M<m^3\), the paper
also proves exact rank rotation and mechanical itinerary, the sorted
log-log grid, and successively stronger height restrictions. The latest
consolidation adds the upper-cell charge bound and the count-specific
minimum interval \(350000000<m<520000000\) for
\((L,o,e)=(780239,492276,287963)\). This does not exclude that period
or change the descent floor.

## Evidence and its limits

| Claim | Evidence | Scope |
|---|---|---|
| Envelope, elementary cycle structure, and finance (Sections 2--4) | Lean proofs of the named core statements | Realized itineraries and explicit cycle hypotheses |
| At least four even steps, period at least eleven (Theorem 3.22) | Lean | No descent-floor input |
| At least eight even steps, period at least twenty-two at minima at least 300 (Theorem 3.31) | Lean arithmetic plus enumeration of 353044 canonical forms | The enumeration is verified computation; it is not a fully Lean-certified census |
| Run-type table (Theorem 4.8) | Finite computation | The 99-entry form assumes primitivity and no EE; without no EE the refined list has 117 entries |
| Transport, hug domination, and block estimates (Section 5) | Lean kernels with the analytic identifications listed in Appendix A remaining written | Named constants and quantified hypotheses must be retained |
| Four finite period bounds | Verified descent inputs and per-length comparisons | A bound on a hypothetical cycle's length, not a global no-cycle result |
| Rank order and sorted grid (Section 3.10) | Lean-supported exact statements | Cubic height or the explicitly defined threshold map |
| Altered-map examples (Propositions 3.37--3.38) | Exact constructions | Their closed orbits are not Juggler cycles |
| Periodic height restrictions (Sections 3.11--3.12) | Lean endpoint theorems and written proof details identified in Appendix A | The minimum thresholds and cubic-height assumption are essential |
| Terminal passage (Section 3.13, Appendix F.5) | Lean primitive termination, full actual-orbit construction, original-set adjacency, cut/extrema identification and strict mixed gap | Minimum at least 3 and cubic height; common-prefix amplification remains uncontrolled |
| Upper-square gap (Lemma 6.3a) | Lean | Only the local inequality on an odd-to-odd edge |
| Upper-cell/grid charge (Proposition 6.3b) | Lean finite and closed bounds, including the scaled scalar consequence; asymptotic (UC3) remains written | Also holds for wrong-parity threshold cycles; not a parity obstruction |
| Fixed minimum interval (Corollary 6.3c) | Written monotonicity argument and outward scalar interval computation | Exact counts (780239,492276,287963), cubic height |
| Signed-loss criterion and cap comparison (Section 6.3) | Written identities and outward interval controls | Does not establish the desired sign or simultaneous feasibility of all integer cells |
| Full residue and single-polynomial domain obstructions (Appendix E.7) | AI-assisted written proofs | Full eventual domains; sparse trajectories remain unexcluded |

The formalized height conclusions include
\(M<m^3-\tfrac12m^{253/128}\) for \(m\ge2^{24}\), and
\(M<m^3-\tfrac12m^{127/64}\) for \(m\ge2^{128}\).
The latter has the sharper exponent \(381/128-3^{41}/2^{65}\).
Do not replace the second cutoff by the first. The stronger auxiliary
error constants and optional lower cutoffs in the written derivation are
not all formalized; the stated height theorems are.

Theorem 5.8's full half-open window is \([50508,16785921)\).
The named Lean cap and constant-window instance stop at
\(L<q_{13}=301994\). The extension uses the written decomposition
\(L=bq_{13}+r\) and \(s(L)\le b+47\). It covers
\(L_0,\ldots,L_{54}\), not \(L_{55}=q_{14}\).
The full window uses \(16.41<\nu<17.084\) and the scan-free bound
\(2s(L)/L<0.001862<0.00514212\). It bounds the charge; the
comparison that excludes each surviving length remains per-length.
Observation 5.13 is a finite fit, not an asymptotic law.

Most formal proofs use Lean's kernel and standard logical foundations.
The one documented compiled-decision exception is `window_digit_scan`,
inherited by `window_digit_cap`. The exact list is checked by
`formal/AxiomCheckPaperA.lean` against its recorded output. The new
upper-square, upper-cell charge and terminal-construction proofs introduce
no additional exception.

## Questions for mathematical review

1. Are the envelope, run-form and financing arguments correct at their
   stated quantifiers, with the no-EE and minimum-based hypotheses kept
   where required?
2. Does the walk-charge chain retain every floor loss, use the correct
   rotation coordinate, and distinguish a uniform charge bound from
   the per-length exclusion comparison?
3. Do the periodic height proofs use genuine adjacent return pairs,
   the correct two minimum thresholds, and all intermediate guards?
4. Does Proposition 6.3b correctly transfer the sorted grid into a
   geometric charge sum? Does the fixed cutoff use only the counts
   specified in Corollary 6.3c?
5. Is the signed condition in Section 6.3 kept as an unresolved estimate,
   and are the relaxed cap controls kept distinct from actual integer
   cycle states?
6. Do the family obstructions in Appendix E apply only to their full
   proposed domains, with no inference about a sparse escaping orbit?

## Companion manuscripts

Paper A's cycle bounds do not depend on the analytic results of the
companions. Their current statements and status belong to their canonical
manuscripts, rather than a second claim inventory in this packet:
[Paper B](juggler_parity_discrepancy_note.md) and
[Paper C](juggler_fate_almost_all_note.md).
Section 6.1 cites Paper C's basin lower bound with exponent below
\(0.4926\); this supplies no contradictory basin upper bound and
excludes no cycle here. Unrestricted all-word cylinder hypotheses are
not assumed. The live-start stopped-pressure input remains open.

## Reproduction and release checks

From the repository root:

```text
python tools/build_paper_a.py
python tools/build_paper_a.py --check
python tools/render_theorem_ledger.py --check
python -m research.juggler_sequence.branch_index --check
python tools/check_paper_a_numeric.py --output paper_a_numeric_check.json
python -m pytest tests/research/juggler_sequence/test_paper_a_audit.py tests/research/juggler_sequence/test_paper_a_trust_boundary.py
```

From `formal/`:

```text
lake build Problems.JugglerPaper
lake env lean AxiomCheckPaperA.lean
```

The release manifest hashes the editorial inputs, renderer, cited Lean
sources and their audit, and the numerical sources and control artifact
used by the new comparison. The build checks LaTeX overflow, references,
glyphs and agreement of the generated copies. These establish provenance
and reproducibility; independent mathematical review remains necessary.
