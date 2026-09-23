# Juggler agent guide

The map is \(T(n)=\lfloor\sqrt n\rfloor\) for even \(n\), and
\(T(n)=\lfloor n\sqrt n\rfloor\) for odd \(n\). This guide routes work to
current results; detailed proofs and earlier attempts belong in their linked records.

## Find the branch before reading broadly

```powershell
python tools/lab.py run research.juggler_sequence.branch_index search "your question"
python tools/lab.py run research.juggler_sequence.branch_index show <id>
python tools/formalpedia.py search "mathematical statement" --namespace Problems.Juggler
```

The generated [branch index](index.json) connects probes, tests, dossiers,
claims, Lean modules and negative-knowledge clusters. Read the selected dossier
and its `## Decision`, then search [negative knowledge](../../docs/negative_knowledge.md).
Do not consume the entire index or [branch ledger](../../docs/juggler_branch_ledger.md)
as startup context.

## Current frontiers and boundaries

| Direction | Current result and next boundary |
|---|---|
| Cycles | Certified minimum floor \(N_0=350000000\) excludes nontrivial periods \(<780239\). **Do not raise the floor.** The next useful \(5.54\cdot10^8\) campaign is PARK. Near-convergent exclusion is laboratory-CLOSE. The Wu–Wang reduction gives a closure threshold \(n\gg L^{5.1163051}\), a lower bound on the minimum, never below \(L^2\). |
| Termination | Paper B's written five-step density is \(7/8\), with error \(O_\varepsilon(N^{127/128+\varepsilon})\), pending independent review. The survivor-decay and conditional assembly are Lean; the required floor-distribution input remains open. The remaining analytic problem is external. |
| Fates | Actual E/OE/OOEE production gives unconditional logarithmic contagion at \(\lambda=5/8\), with the needed production input in Lean. A Tao rate \(e>3/8\), or the corresponding stopped-pressure rate, suffices conditionally; those arithmetic rates remain open. No fate is excluded by contagion alone. |
| Flights | Descriptively terminal. Flight laws do not rule out divergent trajectories. |
| Signed codes | The 2-adic orbit code and finite cylinders are exact. Ordinary integrality, orbit realization, density and termination require separate hypotheses. See the [Collatz guide](../collatz/AGENT.md). |

Canonical details:

- Cycles: [Paper A](../../docs/theory/juggler_finite_dynamics_note.md),
  [near-convergent leftover](../../docs/theory/juggler_near_convergent_diophantine_note.md),
  [Wu–Wang reduction](../../docs/problems/juggler_cycle_wuwang_reduction.md).
- Termination: [Paper B](../../docs/theory/juggler_parity_discrepancy_note.md),
  [exported two-monomial problem](../../docs/theory/exponent_pair_two_monomial.md).
- Fates: [Paper C](../../docs/theory/juggler_fate_almost_all_note.md),
  [OOEE production](../../docs/theory/juggler_ooee_weighted_production_note.md),
  [contagion assembly](../../docs/theory/juggler_ooee_contagion_note.md),
  [pressure scale average](../../docs/problems/juggler_pressure_external_average.md).
- Flights: [flight note](../../docs/theory/juggler_flight_note.md).
- Comparative results: [Paper E](../../docs/theory/juggler_signed_collatz_note.md).
  Use the [publication record](../../docs/theory/paper_deposits.md) for deposited
  versions and the paper's release manifest for reproducibility.

Closed directions include Collision Factorization and local leftover killers,
Baker/Simons–de Weger, Paper A×B merging, DK-arch free kills, floor-Hardy
composition, kernel localization, harvest counting, and unrestricted all-word
pressure. Consult the branch's exact obstruction before reopening it. A renamed
formulation does not create a new input. Do not edit a paper from an exploratory
Phase-0 branch or treat a density/period bound as a solution.

## File map

| Artifact | Home |
|---|---|
| Probes and tests | `src/research/juggler_sequence/<branch>.py`, `tests/research/juggler_sequence/test_<branch>.py` |
| Dossier and decision | `docs/problems/juggler_<branch>.md` |
| Durable claim | `docs/theory/theorem_ledger.json`, then render its Markdown sibling |
| Lean module | `formal/Problems/Juggler/`; barrel `formal/Problems/Juggler.lean` |
| Path constants and layer order | `src/research/juggler_sequence/lean_paths.py` |
| Probe data | `data/research/juggler/<branch>/` |
| Reproducible reports | `docs/research/`; regenerate only reports needed by the task |
| Publications | `juggler_review/`; canonical sources under `docs/theory/` |
| Companion website | `web/juggler-companion/` |

Imports remain `research.juggler_sequence` and `Problems.Juggler`. Use the
existing `lean_paths` constants for repository paths, not new `parents[N]`
calculations. The shared engine must not import this application.

## Register a Lean module

1. Search formalpedia for reusable results and read the complete hypotheses.
2. Add the module under `formal/Problems/Juggler/`, in its mathematical namespace.
   `Seam.lean` owns `OnCycle`. Document public declarations.
3. Add its import to `formal/Problems/Juggler.lean` and register it in `LAYERS`
   in `lean_paths.py`; imports must be lower-ranked. A Paper A review module also
   belongs in `PAPER_MODULES` and `formal/Problems/JugglerPaper.lean`.
4. Compile the individual module, then run `python tools/lab.py build`.
   The layer architecture gate forbids `sorry`, `admit` and `axiom` even in comments.
5. Register exact claim/declaration references, render the ledger, rebuild the
   branch index and check public naming with `python tools/lean_style.py`.

Use `norm_num` for literal arithmetic, and `decide +kernel` for closed
computation when possible. `native_decide` changes the trust boundary; use it
only deliberately, with the paper's audit updated. Do not infer trust from catalogue labels.

## Register a probe

Scaffold with `python tools/lab.py run research.juggler_sequence.branch_index new <id>`.
Complete the probe, its targeted test, and a dossier with every
[TEMPLATE](../../docs/problems/TEMPLATE.md) heading and a `PROMOTE | PARK | CLOSE`
decision. Add a ledger row for a named result, a brief recent journal entry,
and a branch-ledger row. CLOSE/REFUTED results must enter negative knowledge.
Rebuild the index, then check:

```powershell
python tools/lab.py test tests/research/juggler_sequence/test_<branch>.py
python tools/lab.py run research.juggler_sequence.branch_index --check
python tools/render_theorem_ledger.py --check
python tools/lab.py test tests/integration/test_docs_links.py
```

`lab.py run` and `lab.py test` select the checkout's own `src/` and working
directory. They prevent an editable installation of another worktree from
redirecting imports or probe outputs to that other checkout.
