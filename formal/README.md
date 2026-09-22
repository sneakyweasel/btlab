# Formalization

Lean 4.33 + Mathlib for the Balanced Ternary Mathematical Laboratory.
Sources live under `BTCalculus/`, `Core/`, `Representation/`,
`Operators/`, and `Problems/`. The Lake package name is
`balanced-ternary-formal`.

Build from this directory:

```powershell
lake build
```

The project contains no `sorry` or `admit`.

| Path | Role |
|------|------|
| `BTCalculus/` | trit algebra, rewrite, jets, residuals, Newton stratum |
| `Core/`, `Representation/`, `Operators/` | generic BT facts used by several problems |
| `Problems/Collatz/` | Collatz-only theorems |
| `Problems/Engine/` | problem-independent engine layers: control words, companion maps, information-field dynamics |
| `Problems/Juggler/` | one-way Juggler layers; Engine copies deleted |
| `Problems/Ostrowski/` | Ostrowski adder theorems |
| `Automata/` | placeholder; do not invent proofs |

Compiled theorem groups:

- actual OOEE production with conserved-weight coefficient 11/100, a single
  bounded loss for every backward-closed class, and the physical source cutoff.
  This discharges the last odd-production input and proves unconditional
  contagion at 5/8. The Tao and cumulative-pressure reductions need only their
  rate hypotheses, now at e>3/8 and r-eta>3/8. See the
  [proof map](../docs/theory/juggler_ooee_weighted_production_note.md);
- every positive real exponent below one admits an infinite set with
  count at least floor(X^kappa) at every nonnegative real cutoff and
  finite reciprocal mass (`BTCalculus.SublinearCountingMass`). Paper E's
  full rational-value table and terminating positive rational code are
  covered by `PaperECompletion`; all eleven added theorems are checked in
  `AxiomCheckPaperEExamples.lean`;
- fixed OOEE count deviations force a fixed family of slow resonances;
  their dyadic count is O(u^(2/9)) and their reciprocal tail is
  O_eta(U^(-7/9)), including summability and the infinite-series bound.
  The following weighted-production theorem supplies the required cutoff. See the
  [proof map](../docs/theory/juggler_ooee_count_poor_tail_note.md);
- exact OOEE target fibres, including both inverse ceilings, candidate-count
  error at most 3, and the nonresonant parity estimate with every source-window
  condition discharged. Its normalized target errors decay as m^(-1/18),
  m^(-2/3), and m^(-7/9). The following count-poor tail supplies resonance
  inclusion; the weighted-production follow-up completes the application. See the
  [proof map](../docs/theory/juggler_ooee_fibre_parity_note.md);
- uniform effective OOE Fourier cancellation for every nonzero integer
  cutoff mode: normalized error at most 128*M^(1/4)*H^(1/30)*T^(-1/60),
  for M,H,T>=1 and H<=T^(1/4). Actual derivative chains, both signs and
  coordinate axes, real dyadic endpoints, discarded initial segments,
  and endpoint corrections are proved. This closes Q1's OOE application
  and Q2. OOEEffectiveReturn now closes Q4/Q5 with the exact floor-residue
  count, both uniform errors, positive count and strict bounded actual
  witness. See the [mode proof map](../docs/theory/juggler_ooe_effective_modes_note.md)
  and [complete assembly](../docs/theory/juggler_ooe_effective_return_lean_note.md);
- actual OOEE joint parity outside explicit slow resonance windows,
  including the last square-root comparison, three-coordinate finite
  Fejer discrepancy and the exact natural-map guard identity. The
  count theorem supplies its Fourier bounds from the proved modes;
  the subsequent fibre and count-poor theorems supply the geometry,
  resonance inclusion and count-deviation tail; weighted production is now
  supplied by FateOOEEWeighted. See
  the [proof map](../docs/theory/juggler_ooee_joint_parity_note.md);
- original OOEE mixed-mode cancellation O(P^(13/32)) on source intervals
  with N<=L*P^(7/16), for every fixed integer mode with (i,j) not both
  zero and uniformly over fixed finite frequency families. The actual
  nested-floor comparison costs at most 10*pi*abs(u)*L*P^(1/4);
  exact-overlap differencing, negative coefficients and short sums are
  included. The subsequent joint-parity theorem supplies slow modes
  outside explicit resonance windows and the actual three-guard count. See the
  [proof map](../docs/theory/juggler_ooee_mixed_modes_note.md);
- explicit third- and fifth-derivative tests, with constants 12 and 7,
  proved from finite differencing and the second-derivative estimate.
  Derivative chains, both signs, actual overlap intervals, rounded
  automatic cutoffs, and floor-difference real-endpoint sums are proved.
  The OOE phase specialization and comparison with its required uniform
  constants remain open. See the
  [proof map](../docs/theory/higher_derivative_finite_note.md) and
  [dependency audit](AxiomCheckHigherDerivative.lean);
- the complete retained OOEE carry correlation O(P^(3/8)), with its
  fractional-part contribution bounded by O(P^(5/16)*log(P)). Centered
  weighted Fejer smoothing at cutoff P^(1/4), actual perturbed curvatures,
  boundary hits, all cells, and logarithm absorption are proved. The
  original nested-floor linearization comparison and mixed-mode
  differencing are supplied by OOEEPhaseComparison and OOEEMixedModes;
- finite two-dimensional Fejer discrepancy for arbitrary samples and
  half-open circular boxes, with error 5/sqrt(H+1)+(3+2*log(H))^2*E.
  The actual kernel, tail, saturated arcs, pointwise sandwich, Fourier
  coefficients and finite count are proved, including empty/full and
  wrapped arcs. This closes Q3 of the effective OOE audit; the specific
  OOE mode rate and final assembly remain open. See
  [the proof map](../docs/theory/finite_fejer_box_note.md) and
  [the 72-theorem dependency audit](AxiomCheckFejerBox.lean);
- actual weighted smooth OOEE carry contribution O(P^(3/8)), with at most
  3L+2 carry levels, exact sampled-cell partition, endpoint losses, and
  monotone partial summation. The exact carry identity isolates the
  sawtooth term, whose estimate is now supplied by OOEECarryFourier;
- actual OOEE carry-cell curvature with explicit size and floor conditions,
  uniform in 1<=h<=P^(1/16), and the resulting unweighted cell bound
  (64*L*sqrt(u)+16/sqrt(u))*P^(3/8). Full joint discrepancy and complete
  production remain separate obligations;
- quantitative second-derivative cancellation with explicit constants,
  including negative curvature and the lattice of spacing two. The proof
  counts resonant terms and applies the proved first-derivative estimate
  on each remaining block; OOEE carry Fourier and discrepancy estimates
  remain separate obligations;
- half-open box frequencies from the Fourier criterion, including zero
  endpoints; frequencies for distinct noninteger powers; exact passage
  from parameter density to counts of starts (1+q*t)^d. Paper E
  Corollaries 4.2-4.3 give the constant 1/(2^(b+2)*M^2), witnesses in
  every sufficiently large fixed relative interval, and every admissible
  residue vector throughout the even run;

- cancellation for every nonzero finite combination of distinct positive
  noninteger real powers on any progression A*n+B with A>0. The proof
  controls actual shifted differences through derivative asymptotics,
  applies qualitative differencing by induction, and removes zero
  coefficients before selecting the top exponent;
- a qualitative Weyl criterion on every finite-dimensional unit torus,
  derived from uniform density of Fourier monomials; nonnegative
  continuous functions inside open sets prove arbitrarily late box
  visits. The exact power-vector specialization discharges BoxRecurrence
  and makes Paper E Theorem 4.1 unconditional;
- the Kusmin--Landau first-derivative estimate with explicit endpoint
  terms: monotone increments in [delta,1-delta] give a 1/delta bound.
  The continuous derivative form and varying-gap consequence are proved.
  For every real c!=0 and 0<theta<1, the averages of exp(2*pi*i*c*n^theta)
  tend to zero, including negative coefficients and finite-prefix removal;
- qualitative van der Corput cancellation for any bounded complex sequence
  whose positive fixed-shift correlation averages tend to zero. The proof
  includes the full-sum/overlap boundary error, normalization, and the
  exponential phase-difference specialization;
- finite van der Corput differencing for bounded complex sequences, with
  exact overlap correlations and constants 2 and 4; the odd-lattice
  exponential-sum specialization includes its unit-modulus and phase
  subtraction proofs. Derivative tests and discrepancy are not assumed
  by this theorem and are still separate formalization obligations;
- unconditional actual OE production at conserved-weight coefficient 33/100,
  using the proved poor-fibre tail and a uniform mass-conversion error at
  most 6 for every predicate and cutoff. FateOOEEWeighted now supplies the
  second odd-production input and the unconditional 5/8 contagion theorem;
- the actual E/OE/OOEE source partition, positive reciprocal comparison
  for the conserved weight, exact even cutoff, removal of shifted and
  additive losses, and the exponent 5/8 certificate. The resulting
  conditional assembly keeps the two actual odd-source production inequalities
  explicit; FateOEWeighted and FateOOEEWeighted now discharge both in Lean;
- exact positive logarithmic mass on every even Juggler fibre and every
  complete even generation; finite source-cutoff transport and infinite
  nonnegative mass conservation for both signed Collatz codes. The 16/18
  code collision has different odd-predecessor production. Uniqueness
  and the sharp reciprocal-error bounds remain written proofs;
- exact stationary-point phase and curvature for odd-source Juggler
  Fourier sums; odd harmonics have zero complete cubic mean.
  The resulting square-root-plus-epsilon discrepancy bound is a
  written analytic proof, not a compiled theorem;
- rational cubic removal for an inverse-cell perturbation, normalized
  third/fourth derivative quotients, their sign factors, and an exact
  exponent budget. The mixed-sum and weighted estimates remain written;
- the smooth word dual degree is integral exactly at the signed Collatz
  unit gap: only degrees 3 and 9 occur. The ninth-degree odd harmonics
  have zero complete mean; no actual itinerary-weight estimate follows;
- exact all-depth odd-predecessor weight transport to the original
  guarded source sum, including injectivity and depth-two scale bounds.
  Its quantitative two-cell application is inherited from written Paper B;
- bounded monotone natural sequences are eventually constant;
- exact lift equations imply monotonicity;
- eventual stabilization iff lift digits are eventually zero;
- boundedness iff eventual zero lift;
- mixed-radix reconstruction;
- positive-integer nested-cylinder realization iff stabilization;
- realization iff eventual zero lift;
- unique zero-lift child from the exact zero-lift law;
- direct residue and lift-digit algebra from an explicit modular inverse;
- odd-endpoint congruence modulo `2^(K+1)`, including a `ZMod` form;
- Kramer's endpoint congruence `2^K x = C` in `ZMod (3^m)`;
- affine-center start/endpoint numerators and cross-multiplied scaling;
- signed inverse-word affine formulas, one uniform height shift for any
  finite expanding block family, internal-prefix bounds, and the
  obstruction to a common shift for both individual inverse letters;
- actual capped minus-shortcut tree inequalities on a strict 1/50 grid,
  with a decreasing scale/root measure above 4096;
- a finite orbit barrier and a closed signed root domain for every positive
  target coprime to 3, including cycle targets, with eventual count transfer;
- the signed grid growth induction, a 177147-row integer weight certificate,
  and cutoff interpolation: every positive 3n-1 target prime to 3 has at
  least X^(21/25) positive ancestors up to every sufficiently large natural X;
- an all-level mean constraint for either sign's strict-grid certificate:
  the harmonic rate is impossible, and rates with mu^50<=2 satisfy
  mu^5000<2^99, independently of the residue-table size;
- `M ≤ X` from the nonnegative `3^m` endpoint lift;
- the fixed-integer affine gap `G = 2^K (n - x)`, its exact recurrence,
  the periodic-code identity `n(2^K - 3^p) = C`, and `2^K ≠ 3^m` for `m ≥ 1`;
- primitive lists, expanding-period exclusion, rotation of an affine block,
  and even additive amplitude of odd states;
- exact endpoint change under refinement and signed successor drift;
- lift blocks as the mixed-radix expansion of `(R_m - 1) / 2`;
- boundedness iff the mixed-radix lift blocks are eventually zero;
- balanced-ternary digit lists: MSD evaluation, digit-sum after append-plus,
  `W(-n) = -W(n)`, `W(3^m n) = W(n)` after canonicalization, and
  `W(W(n)) = n` when the LSD is nonzero;
- shift `S(n)=3n` as appending a trailing zero, digitwise negation as an
  involution commuting with `S`, `D ∘ S = id` on words, `n = lsd + 3 D(n)`
  on nonempty words, `W ∘ S = W`, the witness `W(3)=1`, and
  `P(3)=evalMSD` for the LSD polynomial of an MSD word.

The `BTCalculus` library (built with the same `lake build`) adds trit
Kleene laws, integer `lsdZ`/`DZ` decomposition, `D ∘ I_a = id`, the
projection band `P_a ∘ P_b = P_a`, the twisted product rule, the
LSD-carry sum rule, `cmp3`/`select3` identities, rewrite soundness for
the operator fragment, word/integer semantic agreement for `D` and
`I_a`, coefficient-vector normalization (value preservation, LSD
normal form, lex rank, carry bound), the normalized coefficient
derivative `hatDRaw`, the `ℤ[X]` section derivative with product and
composition laws, finite-depth function-jet reconstruction, finite-horizon
residual equivalence `≡_k`, cascade `outputAlong` for polynomial composition,
global confluence of the stripped coefficient rewrite, Newman confluence
of the enlarged operator-fragment tree TRS `{D, I_a, S, N}`
(including `N(D)→D(N)`), semantic canonicity of that NF grammar
as integer operator functions, Newman unique syntactic NF of the
simplifying word fragment `WORD_SIMP_RULES` (no semantic canonicity),
the restricted Add locality boundary
(`D(x+y)` is not determined by `(D(x),D(y))`; constructor-sum
classification; named push-in peak), and polynomial
function congruence modulo `3^k` (the Myhill–Nerode bridge, the degree-`≤2`
and cubic vanishing criteria, and the first `x^3`/`x^4` residual merges),
and the cubic residual closed form with Newton-coordinate equivalence,
the fibre criteria for `F_k`, the deepest-layer Newton
simplification, square/cubic fibre criterion, and zero-fibre theorem,
the first intermediate layer `m=k-2` (Newton simplification,
`N2`/`N1` criteria, complete fibre criterion, horizon refinement),
and the depth-deficit visibility law
`N2` iff `p ≡ q (mod 3^r)` together with the `r=2` fibre criterion,
and the general `N1` valuation-stratification theorem
(`v3(p)<r` is separated after `N2`),
and the two-regime `N0` scaling `D^m((3^r u)^3)`,
and the mismatched-width cubic quotient
`Q_{t,K,W}=D^t(u^3) mod 3^K` with exact reconstruction criterion,
the one-family obstruction `Q(1+3^t b)=Q(1+3^t c)` iff `3^{K-1}|b-c`,
the packaged Newton-stratum theorems, well-definedness of the
accelerated map `T` on positive odd naturals, and the section-derivative
degree law `deg 𝔇_a f = deg f` with leading coefficient `3^{d-1} LC(f)`
for `d ≥ 1`.

These are labelled **EXACT — LEAN VERIFIED**. The Python cylinder
implementation remains the executable instantiation; this Lean project
formalizes the exact abstract cylinder and lift interfaces and their
arithmetic consequences, together with the digit-list algebra of OEIS
reversal and the operator identities above. Orbit statistics of `W` and `T`
are not formalized.
