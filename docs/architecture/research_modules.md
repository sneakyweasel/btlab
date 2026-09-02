# Research modules

Research problems are applications of the `bt` core. Each area is
independent and may import `bt.*` plus shared experiment/registry
utilities.

## Status labels

| Status | Meaning |
|--------|---------|
| `EXPLORATORY` | early computational or structural work |
| `STRUCTURAL` | exact theorems or a stable exact dictionary, no solution claim |
| `THEOREM` | a named exact result is the centre of the module |
| `PAPER_CANDIDATE` | at least one exact theorem or genuinely nontrivial computational result with a clear literature distinction |
| `ARCHIVED` | retained for history, not an active programme |

Do not mark a module `PAPER_CANDIDATE` merely because a census is large.

The live publication task is `research.juggler_sequence` (Papers A and
B). The rewrite-calculus note remains a parked `PAPER_CANDIDATE`,
ready to send. The cubic Newton stratum is the last promoted BT-core
theory; it is not a new-math frontier.

## Seeded modules

| Module | Status | Contents |
|--------|--------|----------|
| `research.juggler_sequence` | `PAPER_CANDIDATE` | Juggler map \(T\); Papers A/B; cycle floor \(N_0=162849448\), period \(\ge 478245\); not a halt theorem |
| `research.rewrite_calculus` | `PAPER_CANDIDATE` | unary `{D,I_a,S,N}`; `add_not_DLocal`; parked, ready to send |
| `research.residuals` | `STRUCTURAL` | cubic Newton-stratum fibres; \(x^4\) visibility `CLOSE` |
| `research.collatz` | `STRUCTURAL` | accelerated `T`, cylinders, dual codes, affine geometry, cycles, warp |
| `research.collatz_finite_descent` | `ARCHIVED` | shortcut `C`; uniform 2-adic `L`-descent `CLOSE` |
| `research.ostrowski` | `STRUCTURAL` | order-3 \(B_{\min}\); NP \(K\) unbounded; \(L_0\) PARK; `OstrowskiSpec` adapter |
| `research.balanced_ternary` | `STRUCTURAL` | doubled-trit; expanding `T` jets; `D(x+y)` residual |
| `research.signed_digit_residual` | `STRUCTURAL` | `F_{λ,U}=λ·D(s+u)` finite iff `λ≤2` or `max|u|≤1` |
| `research.signed_digit_residual_geometry` | `STRUCTURAL` | `U_m` fills the lattice-in-box; one-sided `U` does not |
| `research.signed_digit_residual_minimality` | `STRUCTURAL` | `λ` coprime to 3 ⇒ distinct residuals are Mealy-minimal |
| `research.signed_digit_constrained_controls` | `STRUCTURAL` | any word of length `v_3(s-t)+1` separates; cyclic letter not required |
| `research.signed_digit_short_horizon` | `STRUCTURAL` | streams agree iff `|w|≤v_3(s-t)`; proper subsets add no extra merges |
| `research.multiplicative_residual` | `STRUCTURAL` | product controls factor through raw `h`; trit products match `U_1` |
| `research.regular_output_preimages` | `STRUCTURAL` | regular output of \(x^2\); sofic obstruction |
| `research.residual_complexity` | `STRUCTURAL` | unrestricted \(C_F(m,r)\); superdiagonal band |
| `research.monna_endpoint_spectra` | `STRUCTURAL` | balanced-Monna endpoint spectra; gate closed |
| `research.lifting` | `EXPLORATORY` | lifting trees; lifting-state / \(k_0\) lines closed |
| `research.additive_combinatorics` | `EXPLORATORY` | `A_k`, `B_k`, `C_k`, sumsets |
| `research.perfect_powers` | `EXPLORATORY` | sparse squares and cubes |
| `research.primes` | `EXPLORATORY` | sparse-prime helpers already in the repo |
| `research.prime_residual_complexity` | `ARCHIVED` | Prime vs sieve residuals under `I_a`; `CLOSE` |
| `research.sparse_polynomials` | `EXPLORATORY` | Mahler / factor scans |
| `research.operator_dynamics` | `ARCHIVED` | {S,N,D,W} identities; length-≤4 close |
| `research.operator_dynamics.signed_p0` | `ARCHIVED` | v2 benchmark \(N\circ I_0\circ D\); \(F^2=P_0\); `CLOSE` |
| `research.balanced_ternary_digit_sum_dynamics` | `ARCHIVED` | v2 benchmark \(T=s\); digital root; `CLOSE` |
| `research.balanced_ternary_weight_dynamics` | `ARCHIVED` | v2 control \(T=W\); regime replication; `CLOSE` |
| `research.balanced_ternary_weight_drift` | `ARCHIVED` | v2 increment \(T=n+W\); Kaprekar-class drift; `CLOSE` |
| `research.syracuse` | `EXPLORATORY` | v2 diagnosis of accelerated odd-only \(S\); census, domain certificates, control-word composition, and generic obstruction; not a Collatz solver |
| `research.balanced_digit_sum_polynomials` | `EXPLORATORY` | nonlinear \(s_{\mathrm{bal}}\); `CLOSE` as reparameterization |
| `research.erdos_distinct_subset_sums` | `EXPLORATORY` | Erdős #1 signed-relation gate |
| `research.kabelian_complexity` | `ARCHIVED` | k-abelian residual signatures; block-coding close |
| `research.stabilization` | `ARCHIVED` | local \(\Phi_r\) versus global \(k_0\); literature close |
| `research.padic_dynamics` | `ARCHIVED` | cycle-lift residual quotient; classical return-map close |
| `research.cerny_bt` | `ARCHIVED` | transition-closed residual quotient; linear/nonlinear close |
| `research.misere_quotients` | `ARCHIVED` | finite-context misere signatures; Plambeck–Siegel close |
| `research.open_problems` | registry | pointers, not a dumping ground |
| `research.engine_campaign` | `EXPLORATORY` | first real-problem frozen-loop campaign |
| `research.engine_memory` | `EXPLORATORY` | v2.2 research-memory descriptor; implementation in `research_engine.memory` |
| `research.research_control` | `EXPLORATORY` | v2.4 research-control descriptor; ranking Phase-0/1, symbolic-composition Phase-2, gated Phase-3 restricted composition, reverse-add Phase-4–8 falsifiers, Phase-9 frontier re-ranking, Phase-10 Juggler odd-odd falsifier, Phase-11 Juggler macro-grammar falsifier, Phase-12 Juggler parity-drift falsifier |
| `research.lychrel_dynamics` | `EXPLORATORY` | Lychrel / Reverse-and-Add pipeline candidate; registration only; PARK; not a reopening of `reverse_and_add_base3` |

The piecewise-affine census, domain-certificate, control-word, and
control-obstruction layers are engine attacks
(`research_engine.attacks.piecewise_affine`,
`research_engine.attacks.parameter_domain`,
`research_engine.attacks.control_word`,
`research_engine.attacks.control_obstruction`, hidden maps in
`research_engine.benchmarks.hidden_piecewise`), not a `research.*`
solver. Dossiers: [piecewise_affine_census.md](../problems/piecewise_affine_census.md),
[control_word_composition.md](../problems/control_word_composition.md),
[control_obstruction.md](../problems/control_obstruction.md).

Each module exposes a lightweight `problem.py` descriptor
(`id`, `title`, `status`, `statement`, `bt_relevance`, `docs`, `lean`,
`conjectures`). Collatz keeps its existing modules; they are not forced
into a deep framework.

The exploratory modules above are parked. They are not a second frontier
and are not developed in the laboratory consolidation. Do not delete them.

## Adding a problem

See [docs/problems/TEMPLATE.md](../problems/TEMPLATE.md). A new problem
must not edit core arithmetic.
