# Agent guide

This is the **Balanced Ternary Mathematical Laboratory**: a
problem-independent core (`bt`) plus independent research applications
(`research.*`). The active application is the **Juggler map**
\(T(n)=\lfloor\sqrt n\rfloor\) (\(n\) even), \(\lfloor n\sqrt n\rfloor\)
(\(n\) odd).

```text
cli, visualization          application edges
research.*                  problem-specific mathematics
research_engine             problem-independent experimental dynamics
bt.*                        problem-independent BT mathematics
```

`bt.*` must never import `research.*` or `research_engine`. Architecture:
[docs/architecture/overview.md](docs/architecture/overview.md).

## Juggler reading path

1. [docs/theory/juggler_finite_dynamics_note.md](docs/theory/juggler_finite_dynamics_note.md) — Paper A: cycle-length lower bounds (itinerary obstructions + finance + the §5 walk-charge envelope; lab extracts [juggler_walk_charge_note.md](docs/theory/juggler_walk_charge_note.md) and [juggler_cycle_itinerary_structure_note.md](docs/theory/juggler_cycle_itinerary_structure_note.md) — word geometry for termination, cycles, and escape)
2. [docs/theory/juggler_parity_discrepancy_note.md](docs/theory/juggler_parity_discrepancy_note.md) — Paper B: parity discrepancy of nested floor powers
3. [docs/theory/juggler_flight_note.md](docs/theory/juggler_flight_note.md) — laboratory extract: descent-free flights (envelope, dichotomy, anchor-period, divergent structure, shared lattice). Not a paper; the flight program is descriptively terminal.
4. [docs/juggler_branch_ledger.md](docs/juggler_branch_ledger.md) — every branch, decision, and strongest evidence
5. [docs/negative_knowledge.md](docs/negative_knowledge.md) — every recorded failure (`REFUTED` / CLOSE / method wall); search before reopening
6. [docs/theory/juggler_cycle_finance_note.md](docs/theory/juggler_cycle_finance_note.md) and [docs/theory/juggler_run_survivor_lattice_note.md](docs/theory/juggler_run_survivor_lattice_note.md) — the cycle frontier

Claim labels: [docs/README.md](docs/README.md).
Research method: [docs/methodology.md](docs/methodology.md).
BT-core theory (STRUCTURAL, parked): `docs/theory/balanced_ternary_calculus.md`,
`cubic_newton_stratum.md`; the rewrite-calculus note remains ready to send
for external review.

## Juggler state of the problem

- **Cycles:** no nontrivial cycle of period \(<478245\) at the
 laboratory certified descent floor \(N_0=162849448\)
 (`J-residual-floor-one-hundred-sixty-two-million`,
 `J-cycle-period-four-hundred-seventy-eight-thousand`): the floor
 certificate is complete (547 chunks, zero failures, peak
 \(463362780\) bits) and the walk charge kills all \(15\) parity
 leftovers below the blocker \(478245=176251+301994\) (\(k=1\)
 semiconvergent fan, required \(19.46\), DK break-even
 \(3.48\cdot 10^8\) — Diophantine, not computational).
 Since the 1 Sep 2026 consolidation Paper A prints the
 \(26254995\) floor: parity cutoff \(50507\) (§5.1), then the
 walk-charge envelope — transport, hug adversary, itinerary identity,
 Denjoy–Koksma over certified Ostrowski blocks, window theorem on
 \([50508,301994)\) — gives period \(\ge 176251\) (§5.2–5.7,
 `J-cyclemin-walk-charge-instance`), and Corollary 5.10 prints the
 second floor \(162849448\) with period \(\ge 478245\); the
 \(10^6\) base instance and
 the \(99\)-length survivor lattice on \((25781,16266),(1054,665)\)
 (`RunSurvivorLattice.lean`) stay in §4. Discrete word layer,
 quotient arithmetic with the DK block hypotheses
 (\(|\theta-p/q|<1/q^2\) for all certified convergents plus block
 permutations, `theta_convergent_quality`,
 `theta_block_permutations`), general Ostrowski numeration
 (window digit cap \(s(L)\le 47\) structural), the transport
 inequality of Thm 5.3, the defect-to-hug-charge chain
 (§5.2 + Thm 5.4 analytic half), the Prop 5.5 Laplace bound
 (`rotationAverage_gap`, quadratic-majorant FTC, no quadrature),
 the Thm 4.6 certified identity
 (`cycleMin_defect_finance`), and the Thm 5.9 kill template
 (`cycleMin_hug_kill_criterion`) are Lean (`WalkChargeItineraries.lean`,
 `OstrowskiSandwich.lean`, `OstrowskiNumeration.lean`,
 `RotationAverage.lean`, `WalkTransport.lean`, `WalkChargeMax.lean`,
 `DefectFinance.lean`); of the §5 envelope chain only the
 ergodic identification of \(C_*\), DK's
 variation-versus-integral inequality
 (both classical, PARK), and the
 per-length kill evaluations remain analytic prose / verified
 computation. The walk program is terminal: the
 fan-minimum reduction (`juggler_walk_fan_minimum_law`, CONJECTURE)
 ties further asymptotic progress to unbounded partial quotients of
 \(\log 2/\log 3\) — classical OPEN. Killing the
 remaining near-convergents (first \(478245\)) is Diophantine; the
 direct Baker/SdW transfer is **REFUTED** (`juggler_cycle_gap_baker`),
 the Paper A × Paper B merge is CLOSE (`juggler_cycle_paper_merge`),
 the DK-arch free-kill of \(478245\) is **REFUTED**
 (`juggler_walk_arch_kills_blocker`: any valid tightening of
 \(2s(L)\) sits above the already-computed hug DP, which loses
 at margin \(0.433\)),
 and further \(N_0\) campaigns are PARK (the next useful floor is
 \(3.48\cdot 10^8\)).
- **Flights:** the descent-free (open-orbit) program is descriptively
  terminal. Extract: [juggler_flight_note.md](docs/theory/juggler_flight_note.md).
  Lean envelope and walk-height law on `AboveAnchor`; every flight has
  unbounded walk (hug-hugging is cycle-exclusive); bounded-walk flights
  from \(n\ge 3.5\cdot 10^8\) have eventual period \(\ge 780239\)
  (conditional, no new floor); divergent flights diverge pointwise with
  recurrent hug domination and record jumps quantized to the
  \(\log_2 3\)-lattice (shortest near-return \(19\)).   Do not reopen
  composition (`REPARAMETERIZATION`), odd-tower placement, DK-as-kill,
  valley-composition exclusion (`CLOSE`: occupancy is the existing
  pigeonhole), or a bounded walk coboundary
  (`juggler_walk_phase_correction`: even-square tower kills every
  bounded \(\psi\); the fan margin is smaller than the collapse). The terminating-side height-law PARK is not an exclusion
  mechanism. Hug-cylinder construction stays PARK
  (`juggler_hug_flow_window`): depth \(1\) is
  `J-hug-flow-window-depth-one`. Interval-ET depth \(2\) is CLOSE
  (`J-hug-flow-image-gap`): the image is \(3\sqrt X\)-separated.
  Mechanical lift, prefix realization, and formal-versus-realized
  do not say hug prefixes cannot be realized. Exclusion of
  divergent orbits is not claimed.
- **Termination:** certified descent density \(7/8\)
  (length-5 repair, `J-five-step-descent-density`, Paper B
  Corollary 6.4). The four-step class remains \(13/16\)
  (Corollary 4.9). Densities \(57/64\) and \(29/32\) remain
  **CONJECTURE** (Phase-26 holes: length-7 chirps miss
  Stage 2, `J-length7-passenger-theorem-t` **REFUTED** as a
  method; isolated \(e(un^{27/16})\) and \(e(Cn^{3/2})\)
  close by one \(A\)-process plus Lemma 3.3,
  `J-length7-vdc3-chirps`, but the inventory object is
  \(e(uw^{3/2})\) and the reduction is not a decoration;
  X3 plus Q/R3 is **REFUTED** (`J-length7-x3-qr3-carry`);
  the integer-\(w\) block at \(\xi\asymp n^{45/32}\) is
  the Phase-5 wall (`J-length7-integer-w-block`);
  the length-8 remainder decays
  (`J-length8-remainder-discard`: \(\lvert E\rvert\ll
  n^{-45/128}\), discard \(\ll P^{131/192}\); crude
  \(\lvert E\rvert<1\) discard stays dead); the growing
  remainder is now an engine,
  `J-length7-remainder-engine`; the harvest counting
  program is laboratory-terminal
  (`J-harvest-counting-terminal`: every reading of
  \(e(uw^{3/2})\) is a killed route or not a Juggler
  construction — do not wrap a nested-floor bound as
  one). Corollary R′ is still a
  family-CONJECTURE, but the instance \(\alpha=33/32\) is
  **EXACT — HUMAN PROOF**,
  `J-w-family-thirty-three-thirty-seconds`). The rated
  pointwise route is parked behind the \(K_3\) obstruction
  ladder BB/GG/JJ. The rate-free line is laboratory-terminal:
  nearby reformulations of the floor-Hardy composition are
  closed (`juggler_v94_rate_free`, `juggler_v94_hardy_lift`,
  `juggler_nil_pet_reentry`, `juggler_rate_free_floor_hardy`).
  The remaining problem is external mathematics, exported at
  [docs/theory/exponent_pair_two_monomial.md](docs/theory/exponent_pair_two_monomial.md):
  prove \(\tfrac54 p+q<\tfrac23\) for an exponent pair
  applicable to \(cm^{9/4}-jm^{2/3}\). It is not a Juggler
  construction and must not be wrapped as one. The conjecture
  `juggler_tower_rate_free_equidistribution` stays ACTIVE; a
  completely different route to the node-wise E-share
  \(\beta>\beta_*=1-\log 2/\log 3\approx 0.36907\) would also
  suffice. The m-variable PS inversion is recorded and closed
  (`juggler_ps_inversion_barrier`): the fixed harmonic
  reduces exactly to those two-monomial sums, needing
  sub-density \(o(M^{2/3})\) versus the known hull minimum
  \(95/112\); main-term saving \(N^{13/16}\) and the
  bias-mass relaxation of Lemma B are recorded there. Do not
  re-run it. The Bombieri–Iwaniec follow-up is also closed
  (`juggler_bi_resonance_limit`): sub-density needs \(p<2/27\)
  on the BI line, while the method's ceiling under perfect
  spacing is \(3/20\) — a factor \(81/40\) short even
  conjecturally-within-method. Do not reopen the composition door, the
  \(\beta\)-fallback as a weaker species, PET, Theorem R,
  \(\lambda=0\), or further literature-name audits. Not
  claimed.
- **Local attacks are closed.** Fibres are parity + interval only
  (`even_preimage_iff`, `odd_preimage_unique`, `preimage_same_next_state`): no finite
  local configuration around a hypothetical cycle is contradictory. Seam,
  ancestry, provenance, collision-pair, word-order, error-transport, and
  cycle-lift drops all reduce to Collision Factorization (first meeting iff
  the parent is off-cycle) or the lift identity \(T^L(t)=c\ge n\). The
  integer-edge interface is `Seam.lean` (`SeamData`); it packages that
  factorization and does not reopen the kill. Do not reopen them; the
  ledger, `conjectures/refuted/`, and
  [docs/negative_knowledge.md](docs/negative_knowledge.md) list each kill.
- **Anti-overclaim:** do not treat a finite check, a period floor, a
  density, a leftover census, or any weaker compiled lemma as a halt
  theorem, as "no cycle of any length", or as a Collatz/Juggler
  solution. Finite checks are not proofs. Slogan language ("we solved
  Juggler / Collatz") is forbidden even if a theorem exists: state the
  theorem with its quantifiers, Lean name, and ledger tag. If Lean
  compiles a `sorry`-free statement that matches the English (every
  orbit reaches the trivial cycle, or there is no nontrivial cycle),
  say that statement, tag it `EXACT — LEAN VERIFIED`, and record it.
  Do not refuse to name a matching theorem, and do not hide it under
  "this is not a halt theorem." Until that gate, those phrases are
  overclaim. See [docs/README.md](docs/README.md).

## Juggler file map

| Artifact | Home |
|----------|------|
| Probes / censuses | `src/research/juggler_sequence/<branch>.py` |
| Tests (fast suite) | `tests/research/juggler_sequence/test_<branch>.py` |
| Data artifacts | `data/research/juggler/.../summary.json` |
| Lean (itineraries, cells, CycleMin, finance, lattice, seam) | `formal/Problems/Juggler/` (`WalkChargeItineraries.lean`, `Seam.lean`) |
| Branch dossier | `docs/problems/juggler_<id>.md` (all TEMPLATE headings; enforced by `tests/integration/test_problem_dossiers.py`) |
| Negative knowledge | [docs/negative_knowledge.md](docs/negative_knowledge.md) (completeness: `tests/integration/test_negative_knowledge.py`) |
| Conjecture record | `conjectures/{active,refuted,proved,archived}/<id>.json` |
| Journal entry | `docs/research_journal.md` (consolidations allowed; no auto-milestones) |
| Named theorem metadata | `docs/theory/theorem_ledger.json`, then render |
| External leftover (not a Juggler branch) | [docs/theory/exponent_pair_two_monomial.md](docs/theory/exponent_pair_two_monomial.md) |

## How a direction runs

`explore → distill → prove/refute → decide`. Before substantial
implementation, output a triage block:

```text
Mathematical target     one precise question
Novelty hypothesis      what could possibly be new
Falsifier               the observation that kills the idea
Existing machinery      what the platform already provides
Maximum Phase-0 scope   the smallest experiment that answers the target
Promotion criterion     what would justify PROMOTE
Stop criterion          what forces PARK or CLOSE
```

Implement only that scope. Search [docs/negative_knowledge.md](docs/negative_knowledge.md), `conjectures/refuted/`, the branch
ledger, and the `REFUTED` ledger rows before re-testing a hypothesis.

At the end of a phase, report:

```text
What was learned      3–7 concise points
Strongest theorem     one statement
Strongest refutation  one false hypothesis or counterexample, if any
Reusable machinery    what enters the platform
Branch status         PROMOTE | PARK | CLOSE
Why                   one short paragraph
Best next question    exactly one
```

Then stop. Machinery gravity — new structure, new CLI, new visualization,
no new mathematical consequence — means stop implementing, find the
invariant or obstruction, and decide. Every branch ends in `PROMOTE`,
`PARK`, or `CLOSE`; do not auto-open the next one. Do not raise \(N_0\),
reopen finance, or edit Paper A from a Phase-0 branch. Do not
generate nearby reformulations of the floor-Hardy composition.

## Where non-Juggler math goes

Trit / `D` / jets / `≡_k` → `src/bt/calculus/`; cubic strata →
`src/research/residuals/`; Collatz → `src/research/collatz/`; generic Lean
→ `formal/BTCalculus/`. No `bt.calculus` shims, no compatibility packages.
New research area: [docs/problems/TEMPLATE.md](docs/problems/TEMPLATE.md)
plus `src/research/<id>/`.

## Commands

```powershell
python -m pip install -e ".[dev,ui]"
pytest                                              # fast suite
pytest tests/research/juggler_sequence -q           # Juggler only
pytest --runslow
python -m research.juggler_sequence.<branch>        # run a probe
python tools/render_theorem_ledger.py --check
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd formal; lake build                               # no sorry / admit
```
## Remarks

If you're Fable don't spend ages fixing tests - focus on the math.

You have access to a Windows 11 machine with an AMD Ryzen 9 3900X (12C/24T), 64 GB RAM, and an RTX 5090 (32 GB VRAM, CUDA 13.3), so don't be afraid to use it.

Persistent policy lives in [.cursor/rules/](.cursor/rules/). Streamlit work uses
[.agents/skills/developing-with-streamlit/SKILL.md](.agents/skills/developing-with-streamlit/SKILL.md).
