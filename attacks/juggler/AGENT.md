# Juggler agent guide

Canonical reading path, state of the problem, file map, and
registration for the Juggler attack. Always-on [AGENTS.md](../../AGENTS.md)
keeps a short pointer only. Do not copy this page into
`.cursor/rules/` or `AGENTS.md`.

The map is \(T(n)=\lfloor\sqrt n\rfloor\) (\(n\) even),
\(\lfloor n\sqrt n\rfloor\) (\(n\) odd). Not a halt theorem.

Branch lookup: [index.json](index.json) (generated; do not hand-edit).
Rebuild: `python -m research.juggler_sequence.branch_index`.

## Reading path

1. [juggler_finite_dynamics_note.md](../../docs/theory/juggler_finite_dynamics_note.md) — Paper A: cycle-length lower bounds ([doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453)). Audit: `research.juggler_sequence.paper_a_audit`. Extracts: [juggler_walk_charge_note.md](../../docs/theory/juggler_walk_charge_note.md), [juggler_cycle_itinerary_structure_note.md](../../docs/theory/juggler_cycle_itinerary_structure_note.md). Near-convergents leftover, not a review object and not Paper D: [juggler_near_convergent_diophantine_note.md](../../docs/theory/juggler_near_convergent_diophantine_note.md).
2. [juggler_parity_discrepancy_note.md](../../docs/theory/juggler_parity_discrepancy_note.md) — Paper B, *Five-Step Descent Certificates for the Juggler Map* (edition of 20 September 2026; Zenodo record 22864934, [doi:10.5281/zenodo.22864934](https://doi.org/10.5281/zenodo.22864934)): Theorem 4.11 and Appendices A-C prove the OOOEE mixed modes with exponent 127/128; Theorem 5.4 proves full five-step power-envelope certificate density 7/8 with error O_epsilon(N^(127/128+epsilon)). The four-step and OOEOE proofs remain included. Lemma 5.1 (minimal certificates E, OE, OOEE, OOOEE, OOEOE) is Lean-verified in `PaperBCertificates.lean`. This is an AI-assisted written proof for the analytic core; independent mathematical review and complete Lean verification of the exponential-sum estimates are outstanding. The historical 95/96 target, arbitrary decorations, short-interval localization, and all-depth fair-share hypotheses remain open. [Fresh proof audit](../../docs/theory/paper_b_proof_review.md) and [build guide](../../docs/theory/PAPER_B_BUILD.md). Historical repair notes remain research records, not manuscript dependencies.
3. [juggler_flight_note.md](../../docs/theory/juggler_flight_note.md) — descent-free flights. Not a paper; the flight program is descriptively terminal.
4. [juggler_branch_ledger.md](../../docs/juggler_branch_ledger.md) — every branch, decision, and strongest evidence.
5. [negative_knowledge.md](../../docs/negative_knowledge.md) — every recorded failure. Search before reopening.
6. [juggler_cycle_finance_note.md](../../docs/theory/juggler_cycle_finance_note.md) and [juggler_run_survivor_lattice_note.md](../../docs/theory/juggler_run_survivor_lattice_note.md) — cycle frontier.
7. [juggler_fate_contagion_note.md](../../docs/theory/juggler_fate_contagion_note.md) — fate contagion (Atropos / Lachesis / Clotho). Not a halt theorem; no fate excluded.
8. [collatz_3n_minus_1_m_cycles_note.md](../../docs/theory/collatz_3n_minus_1_m_cycles_note.md) — **Paper D**, *No m-cycles of the 3n−1 map for m ≤ 61* (version 1.1.0, built and not yet deposited; the record [doi:10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190) is version 1.0.0 of 21 September 2026 and reads m ≤ 58, concept [10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189)). The only one of the four about the Collatz side rather than the Juggler map: the Simons–de Weger m-cycle template transposed to 3n−1 from this laboratory's own verification floor 2^51. Conditional on Rhin's measure; Lemmas 1 and 3 are Lean (`Problems.Collatz.NegativeMCycles`), Lemmas 2 and 6 are written proofs, and every table number is recomputed independently. Version 1.1.0 adds Lemma 6, the valley count, which is Hercher's Main Theorem 21 arrangement transposed; at his own floor the same six lemmas give m ≤ 90 against his published 91. Build: `python tools/build_paper_d.py`, then `--check`; guide [PAPER_D_BUILD.md](../../docs/theory/PAPER_D_BUILD.md). Earlier records use "Paper D" for the near-convergents leftover; the published note owns the letter.
8. [juggler_tao_reduction_note.md](../../docs/theory/juggler_tao_reduction_note.md) — Tao-type reduction. Conditional; do not read as evidence for termination.
9. [juggler_fate_almost_all_note.md](../../docs/theory/juggler_fate_almost_all_note.md) — Paper C ([doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165)). The 9 September 2026 publication revision contains the corrected proofs and constants, including the finite production proof in Appendix D; notes 7–8 remain historical. Build and synchronization: `python tools/build_paper_c.py`, then `--check`; details: [PAPER_C_BUILD.md](../../docs/theory/PAPER_C_BUILD.md). Published DOIs: [paper_deposits.md](../../docs/theory/paper_deposits.md).

Claim labels: [docs/README.md](../../docs/README.md).
Method: [docs/methodology.md](../../docs/methodology.md).

## Paper E: living comparative manuscript

[The Juggler Map and the 3n±1 Maps](../../docs/theory/juggler_signed_collatz_note.md)
is Paper E, version 0.5.0 of 22 September 2026, prepared locally and not
deposited. It consolidates the exact orbit code, preservation of actual
cycle periods, the signed 21/25 ancestor theorem, the fixed-grid ceiling,
and the recorded transfer obstructions. Edit the canonical source and
follow [PAPER_E_BUILD.md](../../docs/theory/PAPER_E_BUILD.md); verify with
python tools/build_paper_e.py --check. The [review record](../../docs/theory/paper_e_review.md)
tracks independent review and priority questions. New results enter only
with explicit scope and proof mapping; publication work opens no new attack.
PaperECompletion closes the series, frequency, exponent, and word-sum
notation gaps. PaperEModularReturn verifies Theorem 4.1's exact construction
and denominator growth. PaperECorollaries adds exact sparse-start counts,
fixed relative intervals, and prescribed even-run residues (4.2-4.3).
PaperERecurrence proves BoxRecurrence and the
unconditional Theorem 4.1, using the derivative and Fourier proofs in
BTCalculus. The combined paper audit selects 49 declarations.

The [effective OOE follow-up](../../docs/problems/juggler_effective_modular_return.md)
now gives a written uniform error 2^14*M^(1/4)*T^(127/128) and first-witness
parameter bound 2^2176*M^160. It uses a cited explicit derivative estimate
and a proved Fejer box bound. Its quantitative argument is not yet in Lean
or the version 0.5.0 manuscript. The constants are not practical search limits.

## State of the problem

- **Cycles.** No nontrivial cycle of period \(<780239\) at the certified
  floor \(N_0=350000000\)
  (`J-residual-floor-three-hundred-fifty-million`,
  `J-cycle-period-seven-hundred-eighty-thousand`). Previous floor
  \(N_0=162849448\) gives period \(\ge 478245\). Paper A prints the
  \(26254995\) floor (period \(\ge 176251\)), then Corollaries 5.10–5.11.
  The floor-free Lean bound is still \(e\ge 4\), \(L\ge 11\)
  (Theorem 3.22); the printed computational strengthening is
  Theorem 3.31 (\(e\ge 8\), \(L\ge 22\) at minima \(\ge 300\)).
  Walk program is terminal (`juggler_walk_fan_minimum_law`, **PROVED**
  20 September 2026: `R_min = ((A+B+1)/(A+B-1))^2` exactly, hence
  `((a+3)/(a+1))^2 < R_k` -- the leftover is the classical question
  whether the dangerous-position quotients of \(\log2/\log3\) are
  unbounded, and nothing else).
  Laboratory-kill of remaining near-convergents is **CLOSE**
  (`juggler_cycle_diophantine_survivors`). Baker/SdW **REFUTED**
  (`juggler_cycle_gap_baker`). Paper A × Paper B merge CLOSE.
  DK-arch free-kill of \(478245\) **REFUTED**. Further \(N_0\) campaigns
  are PARK (next useful floor \(5.54\cdot 10^8\); next seed
  \(4.54\cdot 10^{11}\)). Do not raise \(N_0\). Gap transfer + Rhin
  excludes short cycles (`J-cyclemin-short-cycle-rhin`); the leftover
  is the long regime \(L\approx n^{0.59}\). Wu-Wang applies to that
  same substitution and sharpens the exponent \(14.3\to 5.1163051\),
  so the floor-free period bound is \(L\gg n^{0.1954}\) and the
  closure threshold is a minimum lower bound \(n\gg L^{5.1163051}\),
  never below \(L^{2}\) by Dirichlet
  (`J-cyclemin-period-lower-bound`, `J-cyclemin-closure-threshold`,
  [juggler_cycle_wuwang_reduction.md](../../docs/problems/juggler_cycle_wuwang_reduction.md)).
  Kills nothing; the deposited Corollary 4.11 text still prints
  \(14.3\). Mechanical window CLOSE.
  Do not reopen as a short-interval Paper B, two-copy Sturmian rigidity,
  or a longer band scan.
- **Flights.** Descriptively terminal. Extract:
  [juggler_flight_note.md](../../docs/theory/juggler_flight_note.md).
  Every flight has unbounded walk; bounded-walk flights from
  \(n\ge 3.5\cdot 10^8\) have eventual period \(\ge 780239\).
  Do not reopen composition, odd-tower placement, DK-as-kill,
  \(\{(3/2)^n\}\) as a Juggler successor
  ([juggler_three_halves_mod_one.md](../../docs/problems/juggler_three_halves_mod_one.md)),
  valley-composition, or a bounded walk coboundary. Hug-cylinder
  stays PARK. Exclusion of divergent orbits is not claimed.
- **Termination.** Paper B Theorem 5.4 proves full five-step
  power-envelope certificate density \(7/8\), with count error
  \(O_\varepsilon(N^{127/128+\varepsilon})\). Its complete proof is
  in the consolidated manuscript (J-paper-b-five-step-density-127).
  This is an AI-assisted written result, pending independent review;
  no universal termination theorem follows.
  Densities \(57/64\) and \(29/32\) remain CONJECTURE. Harvest
  counting is laboratory-terminal (`J-harvest-counting-terminal`).
  The rate-free reduction's decay half is kernel-checked in
  `PaperBSurvivorDecay.lean` (`J-survivor-count-decay`):
  \(N_d/2^d\to 0\), exact values \(N_5=4\) … \(N_8=19\), and the
  conditional Theorem 6.1 assembled under FD alone. FD stays open.
  Remaining problem is external:
  [exponent_pair_two_monomial.md](../../docs/theory/exponent_pair_two_monomial.md).
  Do not wrap a nested-floor bound as a Juggler construction.
  `juggler_tower_rate_free_equidistribution` stays ACTIVE. PS
  inversion and Bombieri–Iwaniec follow-ups are CLOSE. Do not
  reopen the composition door, the \(\beta\)-fallback, PET,
  Theorem R, \(\lambda=0\), or pairing / sweep / defect
  normalisation as a Lemma B feed (\(1/3<\beta_*\) because
  \(8<9\)).
- **Fates.** Every realized fate class has
  \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for
  \(\lambda<\lambda^{**}=0.4926\) (`J-fate-log-density`), and
  **unconditionally** for \(\lambda\le100/203=0.4926108\)
  (`J-oe-averaged-two-productions-reach-the-depth-two-ceiling`,
  `Production.logMass_contagion_averaged`): the poor-fibre tail takes
  Proposition 4.4's exponential sums off the critical path. Rest-average
  is no longer PARK --- it is proved, Lean, and PROMOTE. Log-log clock
  PARK. The E/OE-only ceiling \(\lambda=0.4927\) is approached to
  within \(5\times10^{-5}\). Tao-type bound with \(e>0.5074\) implies
  the conjecture (`J-tao-rate-implies-conjecture`), and now with no
  contagion hypothesis at all
  (`Production.conjecture_of_tao_rate_averaged`, \(e>103/203\)). Pressure form is
  the weakest displayed per-scale hypothesis. The existing scale average
  also suffices: [corrected implication](../../docs/problems/juggler_pressure_external_average.md),
  `J-pressure-scale-average-suffices`, now Lean in `FateScaleAverage.lean`
  (`ScaleAverage.pressure_average_conjecture`) at `r-eta>103/203`;
  its arithmetic bound is open.
  The [actual OOEE poor-fibre probe](../../docs/problems/juggler_ooee_poor_fibres.md)
  now has a **PROMOTE** [written poor-fibre tail](../../docs/theory/juggler_ooee_poor_fibre_tail_note.md):
  fixed mixed modes save 1/32 on the P^(7/16) source interval, and only
  pure slow modes need resonance exclusions. Every fixed mass deficit has
  reciprocal tail O_eta(U^(-7/9)), giving an actual averaged OOEE coefficient
  arbitrarily close to 1/9. Independent review and analytic Lean verification
  remain outstanding. The subsequent
  [E/OE/OOEE assembly](../../docs/theory/juggler_ooee_contagion_note.md)
  gives written contagion at 5/8 and a sufficient Tao-rate threshold e>3/8.
  `FateOOEEAssembly.lean` checks that implication with the two actual
  odd-production inequalities explicit; it does not certify the analytic
  input. `FateOEWeighted.lean` now discharges the OE inequality, including
  physical cutoffs and a uniform mass-conversion error at most 6. Only
  `OOEEProductionBound` remains in its strengthened contagion implication.
  The classical [finite differencing input](../../docs/theory/finite_weyl_differencing_note.md)
  is now kernel-checked in `BTCalculus.WeylDifferencing`, including exact
  overlap correlations and the odd-lattice specialization. The first-derivative
  bound and the [quantitative second-derivative test](../../docs/theory/second_derivative_cancellation_note.md)
  are also proved, with explicit constants and either curvature sign.
  [Actual carry-cell curvature](../../docs/theory/juggler_ooee_curvature_note.md)
  and its unweighted O(P^(3/8)) cell sum are now proved in `OOEECurvature`,
  uniformly for 1<=h<=P^(1/16), with explicit floor and size conditions.
  [Weighted smooth carry sums](../../docs/theory/juggler_ooee_carry_cells_note.md)
  are now proved in `OOEECarryCells`: at most 3L+2 carry levels, sampled
  endpoint control, monotone partial summation, and a complete O(P^(3/8))
  bound for the smooth contribution. The exact identity isolates the
  sawtooth term. Its Fourier errors and finite discrepancy remain open
  in Lean.
  The unconditional Lean exponent remains 100/203, and the actual
  failure-rate estimate remains open.
  Kernel localize CLOSE. Do not open a
  third formulation. Not a halt theorem; no fate excluded.
  The inverse-cell Hardy shortcut is also CLOSE: its shrinking
  cells need a quantitative count, not qualitative equidistribution.
  The earlier claimed rate-free peel through depth two is withdrawn;
  Paper B's separate rated short counts are unchanged.
  The [odd-image discrepancy](../../docs/problems/juggler_odd_image_discrepancy.md)
  now has a written O_epsilon(N^(1/2+epsilon)) bound, improving 5/6:
  the rational cubic dual has zero odd-harmonic mean, while even
  resonances satisfy the required average. Exact phase identities
  are Lean in `OddCubicPhase.lean`; the analytic proof awaits
  independent review. This supplies no iterated-image or pressure bound.
  Its [inverse-cell continuation](../../docs/theory/juggler_cubic_inverse_cell_note.md)
  now controls the mixed nonzero frequency through j<=M^(1/3+1/50000)
  with error M^(2/3-1/25000), hence one actual predecessor weight.
  `CubicInverseCell.lean` checks its algebra and exponent budget;
  the analytic proof awaits review. Its mixed sum is the retained object;
  Paper B already implies stronger weighted corollaries. The
  [exact predecessor transfer](../../docs/problems/juggler_predecessor_weight_transfer.md)
  now gives a two-odd-predecessor Fourier bound
  O_epsilon(M^(127/288+epsilon)+|h|^24), hence a saving from M^(4/9)
  for 1<=|h|<=M^(1/60). `OddPredecessorTransport.lean` verifies the
  exact reindexing and scale bounds; the estimate inherits Paper B's
  outstanding analytic review. The next odd phase at three predecessors
  is the existing K3 frontier, not a fresh direct extension of Paper B.
  The same dossier now proves uniform separation of the second gap on
  each fixed first-gap branch for P>=256 (`J-fixed-first-gap-separation`,
  written proof, not Lean). Direct freezing remains closed; fourth-phase
  cancellation and growing-depth stopped pressure remain open.
  Direct extension to longer smooth polynomial duals is **CLOSE**:
  [the exact classification](../../docs/problems/juggler_polynomial_dual.md)
  identifies their degree denominator with the signed Collatz gap.
  `PolynomialDual.lean` proves that only (o,L)=(1,1),(2,3) give
  integral degree, namely 3 and 9. The ninth-degree complete cancellation
  does not control OOE guards or deeper predecessor weights.
  The former unrestricted H/H_q statements are now **REFUTED** by
  [absorbed cylinders](../../docs/problems/juggler_absorbed_cylinder.md):
  one terminating cylinder has at least y/(216 log y) starts on infinitely
  many dyadic blocks. H is restricted to bad words, H_q to bad prefixes;
  the stopped live-pressure question is unchanged. Do not reopen the
  all-word version as an averaging target.
- **Local attacks are closed.** Fibres are parity + interval only.
  Seam / ancestry / collision-pair / word-order drops reduce to
  Collision Factorization or \(T^L(t)=c\ge n\). Do not reopen.
- **Signed Collatz orbit code.** `CollatzPadic.orbit_bridge` constructs
  the 2-adic code for every actual Juggler start, with both signed step
  identities, exact finite residue/cylinder equivalence, and agreement
  with `CollatzRational.terminatingCode` on terminating inputs.
  `code_cylinder_eq` transfers counts exactly without estimating them.
  H(3) is nonintegral and H(4)=H(6)=4; no integer-orbit or termination
  transfer follows automatically. `periodic_bridge` preserves exact
  least periods on actual Juggler cycles and characterizes ordinary
  integrality by the word divisibility; under that additional condition,
  ordinary signed Collatz return times agree exactly. The divisibility
  is not proved for Juggler cycles. Ledger coverage review remains pending.
  `CodeMassTransport.lean` now checks the exact positive even-fibre weight,
  conservation through all even generations, and finite source cutoffs for
  both signed codes. Supremum over those cutoffs gives nu(2B)=nu(B), with
  infinite mass allowed. The same module proves that 16 and 18 share a code
  but have different odd-predecessor production. Uniqueness and sharp
  reciprocal comparison remain written; no odd-production rate follows.
  `Problems.Collatz.BackwardMass.backward_mass_counterexample` proves
  the finite-mass backward ray for both shortcut signs. General
  backward-density transfer is CLOSE; the ray is not a fate class.
  Juggler's even-block mass has lower bound m/(m+1)^2, not exact value 1/m.
  `CollatzMoments.complete_family_moment_loss` closes the unqualified
  stopping-time moment transfer: all minimal descent certificates have
  fair mass one but tilted mass at most 3/4. The coefficient shift and
  fixed-depth identities remain valid; Kraft equality alone does not
  justify an unbounded stopped expectation.
  The original automatic Krasikov–Lagarias x^0.84 transfer was incomplete:
  residue negation preserves the formal program but reverses the odd
  predecessor's height comparison. `PreimageScale.lean` proves the
  missing correction and an excluded ancestor. Matching residue solvers
  alone do not supply the height argument.
  `finite_expanding_shift` now controls height corrections through any
  finite expanding inverse-block family, including internal prefixes.
  `PreimageGrid.lean` now proves actual signed counting inequalities on
  a strict 1/50 grid for nonperiodic roots at least 4096, and a decreasing
  scale/root measure. `PreimageDomain.lean` now supplies a closed root
  domain for every positive target coprime to 3, including cycle targets:
  a finite orbit barrier keeps its ancestors above 4096, and a fixed path
  transfers counts to the target. The complete strict-grid proof is now
  **PROMOTE**: `PreimageCertificate12.ancestor_density_21_25` proves
  X^21<=ancestorCount(a,X)^25 for every positive a prime to 3 and every
  sufficiently large natural X. The root induction, all 177147 integer
  certificate rows at rate 5059/5000, and cutoff interpolation are kernel
  checked. This route avoids the old minimum/deletion step. The ledger
  retains the human-proof tag pending advisory coverage. No Juggler
  pressure bound or termination theorem follows from this density result.
  `PreimageBalance.lean` now checks a common mean obstruction at every
  finite level for both signs. With the unchanged grid, the harmonic
  rate mu^50=2 is impossible; rates with mu^50<=2 satisfy mu^5000<2^99.
  Increasing the table size alone toward harmonic growth is **CLOSE**.
  This is not an upper bound on actual ancestor counts or a resolution
  of the fate-specific harmonic-mass question.
  Automatic transfer of Collatz orbit packing is also **CLOSE**:
  equal-time injectivity transfers, but the exact binomial source count
  does not. Paper B's five certificates give upper density at most 1/8
  for a hypothetical unbounded orbit (inheriting the written analytic
  proof's review status); this does not exclude a sparse orbit. The code
  provides no new growing-depth live-pressure or height estimate.
- **Anti-overclaim.** Finite checks, period floors, densities, and
  leftover censuses are not a halt theorem and not "no cycle of any
  length". State the theorem with quantifiers, Lean name, and ledger
  tag. See [docs/README.md](../../docs/README.md).

## File map

| Artifact | Home |
|----------|------|
| This guide | `attacks/juggler/AGENT.md` |
| Branch index | `attacks/juggler/index.json` |
| Path constants | `src/research/juggler_sequence/lean_paths.py` (`REPO_ROOT`, `DATA_ROOT`, `DOCS_ROOT`, `BRANCHES_ROOT`, `FORMAL_DIR`) |
| Manuscript audits | `src/research/juggler_sequence/paper_{a,b,c}_audit.py` |
| Probes | `src/research/juggler_sequence/<branch>.py` |
| Tests | `tests/research/juggler_sequence/test_<branch>.py` |
| Data | `data/research/juggler/<branch>/` (`DATA_ROOT`) |
| Lean | `formal/Problems/Juggler/` (`LAYERS` in `lean_paths.py`) |
| Dossiers | `docs/problems/juggler_<id>.md` |
| Negative knowledge | [negative_knowledge.md](../../docs/negative_knowledge.md) |
| Conjectures | `conjectures/{active,refuted,proved,archived}/<id>.json` |
| Journal | `docs/research_journal.md` |
| Theorem ledger | `docs/theory/theorem_ledger.json`, then render |
| External leftover | [exponent_pair_two_monomial.md](../../docs/theory/exponent_pair_two_monomial.md); near-convergents leftover [juggler_near_convergent_diophantine_note.md](../../docs/theory/juggler_near_convergent_diophantine_note.md) |
| Streamlit | `src/visualization/app_pages/juggler_finite_dynamics.py` |
| Companion | `web/juggler-companion/` |
| Review bundle | `juggler_review/` |

Imports stay `research.juggler_sequence` and `Problems.Juggler`. File
path equals import path. `research_engine` Juggler-named probes are
specimens; they must not import this package.

## Registration (new Lean module)

1. File under `formal/Problems/Juggler/`.
2. Import it in `formal/Problems/Juggler.lean`.
3. Register in `LAYERS` of `lean_paths.py` (imports only lower-ranked
   entries). Paper A review object: also `PAPER_MODULES` and
   `formal/Problems/JugglerPaper.lean`.
4. The words `sorry`, `admit`, `axiom` may not appear anywhere in a
   registered file, not even in comments.
   `tests/research/juggler_sequence/test_layer_architecture.py`.
   `Seam.lean` already owns `OnCycle`.
5. Compile with `lake env lean <file>` (about 40 s) before
   `lake build Problems.Juggler`.

**Which decision tactic.** The choice is what the goal *is*, not how
big the numbers are.

- Literal `Nat`/`Int` arithmetic → `norm_num` (GMP-backed). Exponents
  above 256 need `set_option exponentiation.threshold <n> in`.
- Closed computation over a definition (`floorPower^[k] n = 1`,
  itinerary tables, list folds) → `decide +kernel`. Plain `decide`
  gets stuck on `Nat.sqrt`.
- Scans over \(\gtrsim 10^5\) values → `native_decide` only. Prefer
  the first two. Layer counts: 305 `decide +kernel`, 20 `norm_num`,
  2 `native_decide`.

## Registration (new probe)

1. `src/research/juggler_sequence/<branch>.py`
2. `tests/research/juggler_sequence/test_<branch>.py`
3. `docs/problems/juggler_<branch>.md` with every TEMPLATE heading and
   one of `PROMOTE | PARK | CLOSE`
4. Path suffixes through `lean_paths` (`DATA_ROOT`, `DOCS_RESEARCH`,
   `BRANCHES_ROOT`, `FORMAL_DIR`). Do not invent a new `parents[N]`.
5. Ledger rows if a named theorem exists (`indent=1`, UTF-8, literal
   `—`); `python tools/render_theorem_ledger.py --check`
6. Journal entry and a [branch-ledger](../../docs/juggler_branch_ledger.md) row
7. Rebuild `attacks/juggler/index.json`
8. CLOSE / REFUTED → [negative_knowledge.md](../../docs/negative_knowledge.md)
9. `tests/integration/test_docs_links.py` treats every markdown link as
   a filesystem path; keep bracket-then-paren math out of prose

## Commands

```powershell
python -m pip install -e ".[dev,ui]"
pytest tests/research/juggler_sequence -q
python -m research.juggler_sequence.<branch>
python -m research.juggler_sequence.branch_index
python -m research.juggler_sequence.branch_index --check
python -m research.juggler_sequence.branch_index show <id>
python -m research.juggler_sequence.branch_index search <query>
python -m research.juggler_sequence.branch_index new <id>
python tools/render_theorem_ledger.py --check
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd formal; lake env lean Problems/Juggler/<Module>.lean
cd formal; lake build Problems.Juggler
```

**Worktrees do not isolate these commands.** `pip install -e` resolves
`research.juggler_sequence` from the main checkout, so `REPO_ROOT` and
everything derived from it -- `BRANCHES_ROOT`, `DATA_ROOT`, `FORMAL_DIR`,
the branch index path -- name the main checkout whatever worktree you run
from. `branch_index` run from a worktree rewrites the *main* checkout's
`attacks/juggler/index.json` and leaves the worktree copy stale, and
`--check` then passes against main's copy rather than yours. Several
sessions each regenerating "their own" index are writing one shared file.

Probes are the case that will actually bite: any
`python -m research.juggler_sequence.<branch>` writes its output under
main's `data/research/juggler/`, never the worktree's. Confirmed
2026-09-14 -- the `cyclic_feasibility` cluster and
`twin_flight/summary.json`, last committed 2026-09-08 and 2026-08-31,
were both rewritten from a worktree with byte-identical content, so no
`git status` anywhere showed a thing. That was benign only because the
content matched. A probe whose worktree code differs from main
overwrites main's data silently, and the diff is then attributed to
whoever next commits in main.

Prefix the command, and verify before trusting it:

```powershell
$env:PYTHONPATH = "<worktree>\src"
python -c "from research.juggler_sequence.lean_paths import BRANCHES_ROOT; print(BRANCHES_ROOT)"
python -m research.juggler_sequence.branch_index
```

## Do not

- Raise \(N_0\), reopen finance, or edit Paper A from a Phase-0 branch.
- Generate nearby reformulations of the floor-Hardy composition.
- Move Lean out of `formal/Problems/Juggler` or remap
  `research.juggler_sequence` onto another directory.
- Treat a period floor or a density as a Collatz/Juggler solution.
