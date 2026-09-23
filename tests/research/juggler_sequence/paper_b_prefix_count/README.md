# Prefix-count regressions

These checks retain the original exact identities, finite experimental ranges,
and checks against the historical 2026-09-04 Paper B manuscript. They do not
establish termination or change a claim's evidence label.

| Topic | Test files |
|---|---|
| Counts, bias, density ceilings | `test_counting.py`, `test_ceilings.py` |
| Manuscript and ledger consistency | `test_publication.py` |
| Defects, exponents, screens, actual orbits | `test_word_geometry.py`, `test_defect_classification.py`, `test_screening.py`, `test_orbits.py` |
| Analytic estimates and carries | `test_analytic_bounds.py`, `test_carry.py`, `test_rates.py` |
| Meanders and Diophantine structure | `test_meander.py`, `test_staircase.py` |
| Phase dependence and recursions | `test_phase_profile.py`, `test_phase_cocycle.py`, `test_phase_resonances.py`, `test_sturmian_recursion.py`, `test_sturmian_amplitudes.py`, `test_jump_reconstruction.py` |
| Boundary fractions and convergence | `test_boundary_fraction.py`, `test_boundary_rotation.py`, `test_boundary_memory.py`, `test_boundary_convergence.py` |
| Rational barriers and killed walks | `test_rational_barriers.py`, `test_killed_walk.py` |
| Limiting shapes and weight coordinates | `test_quasi_stationary.py`, `test_weight_profile.py` |

Run a relevant file first. To include its expensive experiments, add `--runslow`.
The full suite can distribute topics across workers:

```powershell
python tools/lab.py test -- tests/research/juggler_sequence/paper_b_prefix_count/test_word_geometry.py
python tools/lab.py test -- tests/research/juggler_sequence/paper_b_prefix_count --runslow -n 8 --dist loadfile
```

Slow markers belong to measured expensive numerical tests, not whole topic files.
Keep metadata and small exact identities available in the fast suite. CI includes
all slow tests. `helpers.py` holds shared manuscript paths and independent
enumerators; expected answers must not be replaced with calls to the code under
test. Tests continue to exercise the public `paper_b_prefix_count` API; new
application code imports the owning `paper_b_prefix_count_core` module.
