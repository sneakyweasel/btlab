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

- unconditional actual OE production at conserved-weight coefficient 33/100,
  using the proved poor-fibre tail and a uniform mass-conversion error at
  most 6 for every predicate and cutoff. The 5/8 contagion and e>3/8 Tao
  implications now retain only the OOEE production as an analytic input;
- the actual E/OE/OOEE source partition, positive reciprocal comparison
  for the conserved weight, exact even cutoff, removal of shifted and
  additive losses, and the exponent 5/8 certificate. The resulting
  contagion and Tao implication at e>3/8 keep the two actual odd-source
  production inequalities explicit; their analytic discharge is written;
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
