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

1. [juggler_finite_dynamics_note.md](../../docs/theory/juggler_finite_dynamics_note.md) — Paper A: cycle-length lower bounds. Audit: `research.juggler_sequence.paper_a_audit`. Extracts: [juggler_walk_charge_note.md](../../docs/theory/juggler_walk_charge_note.md), [juggler_cycle_itinerary_structure_note.md](../../docs/theory/juggler_cycle_itinerary_structure_note.md). Paper D draft (not a review object): [juggler_near_convergent_diophantine_note.md](../../docs/theory/juggler_near_convergent_diophantine_note.md).
2. [juggler_parity_discrepancy_note.md](../../docs/theory/juggler_parity_discrepancy_note.md) — Paper B: parity discrepancy of nested floor powers. Audit ledger: [paper_b_audit_ledger.md](../../docs/theory/paper_b_audit_ledger.md) + `paper_b_audit`.
3. [juggler_flight_note.md](../../docs/theory/juggler_flight_note.md) — descent-free flights. Not a paper; the flight program is descriptively terminal.
4. [juggler_branch_ledger.md](../../docs/juggler_branch_ledger.md) — every branch, decision, and strongest evidence.
5. [negative_knowledge.md](../../docs/negative_knowledge.md) — every recorded failure. Search before reopening.
6. [juggler_cycle_finance_note.md](../../docs/theory/juggler_cycle_finance_note.md) and [juggler_run_survivor_lattice_note.md](../../docs/theory/juggler_run_survivor_lattice_note.md) — cycle frontier.
7. [juggler_fate_contagion_note.md](../../docs/theory/juggler_fate_contagion_note.md) — fate contagion (Atropos / Lachesis / Clotho). Not a halt theorem; no fate excluded.
8. [juggler_tao_reduction_note.md](../../docs/theory/juggler_tao_reduction_note.md) — Tao-type reduction. Conditional; do not read as evidence for termination.
9. [juggler_fate_almost_all_note.md](../../docs/theory/juggler_fate_almost_all_note.md) — Paper C. Notes 7–8 remain the source of the proofs and constants. Review PDF: `pandoc -f markdown+tex_math_single_backslash --pdf-engine=xelatex -V geometry:margin=1in --resource-path=docs/theory` into `juggler_review/`; figures: `python docs/theory/figures/render_paper_c_figures.py`.

Claim labels: [docs/README.md](../../docs/README.md).
Method: [docs/methodology.md](../../docs/methodology.md).

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
  Walk program is terminal (`juggler_walk_fan_minimum_law`, CONJECTURE).
  Laboratory-kill of remaining near-convergents is **CLOSE**
  (`juggler_cycle_diophantine_survivors`). Baker/SdW **REFUTED**
  (`juggler_cycle_gap_baker`). Paper A × Paper B merge CLOSE.
  DK-arch free-kill of \(478245\) **REFUTED**. Further \(N_0\) campaigns
  are PARK (next useful floor \(5.54\cdot 10^8\); next seed
  \(4.54\cdot 10^{11}\)). Do not raise \(N_0\). Gap transfer + Rhin
  excludes short cycles (`J-cyclemin-short-cycle-rhin`); the leftover
  is the long regime \(L\approx n^{0.59}\). Mechanical window CLOSE.
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
- **Termination.** Certified descent density \(7/8\)
  (`J-five-step-descent-density`). Four-step class \(13/16\).
  Densities \(57/64\) and \(29/32\) remain CONJECTURE. Harvest
  counting is laboratory-terminal (`J-harvest-counting-terminal`).
  Remaining problem is external:
  [exponent_pair_two_monomial.md](../../docs/theory/exponent_pair_two_monomial.md).
  Do not wrap a nested-floor bound as a Juggler construction.
  `juggler_tower_rate_free_equidistribution` stays ACTIVE. PS
  inversion and Bombieri–Iwaniec follow-ups are CLOSE. Do not
  reopen the composition door, the \(\beta\)-fallback, PET,
  Theorem R, or \(\lambda=0\).
- **Fates.** Every realized fate class has
  \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for
  \(\lambda<\lambda^{**}=0.4926\) (`J-fate-log-density`).
  Rest-average PARK. Log-log clock PARK. Contagion method ceiling
  \(\lambda=0.4927\). Tao-type bound with \(e>0.5074\) implies the
  conjecture (`J-tao-rate-implies-conjecture`). Pressure form is
  the weakest hypothesis. Kernel localize CLOSE. Do not open a
  third formulation. Not a halt theorem; no fate excluded.
  The former unrestricted H/H_q statements are now **REFUTED** by
  [absorbed cylinders](../../docs/problems/juggler_absorbed_cylinder.md):
  one terminating cylinder has at least y/(216 log y) starts on infinitely
  many dyadic blocks. H is restricted to bad words, H_q to bad prefixes;
  the stopped live-pressure question is unchanged. Do not reopen the
  all-word version as an averaging target.
- **Local attacks are closed.** Fibres are parity + interval only.
  Seam / ancestry / collision-pair / word-order drops reduce to
  Collision Factorization or \(T^L(t)=c\ge n\). Do not reopen.
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
| External leftover | [exponent_pair_two_monomial.md](../../docs/theory/exponent_pair_two_monomial.md); Paper D draft [juggler_near_convergent_diophantine_note.md](../../docs/theory/juggler_near_convergent_diophantine_note.md) |
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

## Do not

- Raise \(N_0\), reopen finance, or edit Paper A from a Phase-0 branch.
- Generate nearby reformulations of the floor-Hardy composition.
- Move Lean out of `formal/Problems/Juggler` or remap
  `research.juggler_sequence` onto another directory.
- Treat a period floor or a density as a Collatz/Juggler solution.
