# Architecture overview

This repository is the **Balanced Ternary Mathematical Laboratory**: a
problem-independent balanced-ternary core (`bt`) plus independent research
applications (`research.*`).

Balanced ternary mathematics is **core**. Research problems are
**applications**. The live application is `research.juggler_sequence`.
Core modules must never import research modules.

This page is the architectural contract. It does not change any
mathematical definition.

## Layers

```text
cli, visualization          application edges
research.*                  problem-specific mathematics
research_engine             problem-independent experimental dynamics
bt.*                        problem-independent BT mathematics
```

- `bt.*` may import only `bt.*` (and the Python standard library). It must not import `research_engine`.
- `research_engine` may import only the Python standard library. It must not import `bt.*` or `research.*`.
- Optional engine layers (not required on `ProblemSpec`): observation, raw-contribution factorization, invariant envelope vs exact reachability, pair-state separation, Mealy quotient, complexity profiles, evidence `CertificateKind`, session prior-art status, the diagnosis loop (`RegimeFingerprint`, family saturation, `ResearchDecision`), the piecewise-affine census (`AffineBranch`, `LatentControl`), parameter-domain certificates (`AffineFamily`, `DomainCertificate`), control-word composition (`ControlWord`, `ComposedAffineRelation`), control-word obstruction (`ControlObstructionCertificate`), vector-affine census (`VectorAffineCensus`), matrix-word recursive invariants (`MatrixWordInvariant`), optional v2.2 research memory (`ResearchMemory`, failure taxonomy, grey loot, target board; post-run only; not an attack), and optional v2.4 research control (`research_engine.control`: immutable v2.3 baseline, CLOSE taxonomy, non-executable Top-3 attack proposals, v2.2 replay; not an attack). The cheap-attack order is frozen after `matrix_word_invariant`. These wrap existing attacks. They are not a second theorem ledger.
- `research.*` may import `bt.*`, `research_engine`, and explicitly shared utilities
  (`research.experiments`, conjecture/literature registries).
- `cli` and `visualization` may import both layers.

## Package names

| Role | Import | Notes |
|------|--------|-------|
| Distribution | `balanced-ternary` | `pip install -e ".[dev,ui]"` |
| Command | `btlab` | CLI entry |
| Core | `bt` | problem-independent BT mathematics |
| Experimental dynamics | `research_engine` | integer affine/block/trajectory, R/K/L, algebra, attacks (including spectral companion classification, piecewise-affine census, parameter-domain certificates, control-word composition, control-word obstruction, vector-affine census, matrix-word recursive invariants, optional observation/factorization/separation/quotient), planner, synthetic benchmarks, theorem targets (not proofs), engine-only `CertificateKind`, optional v2.2 `research_engine.memory`, and optional v2.4 `research_engine.control`; `btlab research` is the CLI wrapper; symbolic deferred; **attack architecture frozen** |
| Research | `research` | problem-specific applications |
| CLI | `cli` | `btlab` implementation |
| Formal | `balanced-ternary-formal` | Lake package under `formal/` |
| UI | `visualization` | optional extra; not part of the math core |

## Canonical imports

| Import | Role |
|--------|------|
| `bt.representation` | encode / decode / words |
| `bt.metrics` | weight, length, digit sums |
| `bt.arithmetic` | word arithmetic |
| `bt.operators` | `S`, `N`, `D`, `W`, … |
| `bt.sequences` | canonical sequences |
| `bt.polynomials` | core `P_n` |
| `bt.support` | support-set operations |
| `bt.calculus` | trit calculus |
| `bt.automata` | residue automata, DFA minimization |
| `bt.transducers` | generic sequential transducers |
| `research.collatz` | Collatz application |
| `research.residuals` | cubic fibres / Newton stratum API |
| `research.experiments` | shared experiment schema and table I/O |
| `cli.main` | `btlab` |

Do not add top-level compatibility packages (`balanced_ternary`, `collatz`, `automata`).

## Verification

After a structural change:

1. `pytest` (fast suite; `pytest --runslow` before a release)
2. `cd formal && lake build`

Do not continue past a red gate. Mathematical behaviour must not change.

## Related pages

- [Research Engine diagnosis loop](research_engine_loop.md)
- [Core](core.md)
- [Research modules](research_modules.md)
- [Experiments](experiments.md)
- [Conjectures](conjectures.md)
- [Formalization](formalization.md)
- [Juggler Lean spine](juggler_lean_spine.md)
- [Literature](literature.md)
