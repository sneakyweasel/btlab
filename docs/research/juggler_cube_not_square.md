# Juggler cube-not-square cell

Status: **CUBE_NOT_SQUARE_GREEN**

Parity split of `n^2 <= x < n^3`. Not a halt theorem.

## Branch budget

```text
Mathematical target     cube-not-square certificate
Novelty hypothesis      even reset / odd lift / EE drop
Maximum Phase-0 scope   generic Lean dichotomy; no letter chain
```

## Metadata

- classification: **CUBE_NOT_SQUARE_GREEN**
- even reset: `True`
- odd lift: `True`

cube-not-square splits by parity: even resets into [n, n^2) and EE is FiniteProgress; odd lifts to n^3; 1517 takes the odd branch.

## Lean

- `even_below_cube_preimage`: `True`
- `even_cube_not_square`: `True`
- `odd_ge_sq_floor_ge_cube`: `True`
- `finiteProgress_of_cube_even_even`: `True`
- `minimal_cube_even_forces_odd_image`: `True`
- `envelope_lt_pow`: `True`
- `even_below_fourth`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cube_even_is_finite_progress: `False`
- letter_chain: `False`

## Decision

**CUBE_NOT_SQUARE_GREEN**

cube-not-square splits by parity: even resets into [n, n^2) and EE is FiniteProgress; odd lifts to n^3; 1517 takes the odd branch.

