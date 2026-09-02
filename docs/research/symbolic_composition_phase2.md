# Symbolic-composition Phase-2 falsifier

Status: **PHASE_2_SYMBOLIC_COMPOSITION_FALSIFIER**

This is not a composition engine and not a termination proof.
Phase 1 left a juggler `T^2` ranking signal. Phase 2 asks whether that
signal is an exact two-step identity, and whether the same probe
helps reverse-add and home-prime.

## Branch budget

```text
Mathematical target     Does T^2 have an exact inequality/identity on a
                        natural domain that explains the Phase-1 ranking?
Novelty hypothesis      For juggler, T^2(n) < n on odd n with T(n) even.
Falsifier               An odd-to-even n >= 2 with T^2(n) >= n, or a proof
                        that the inequality is only a finite-table artifact.
Existing machinery      floorPower / isqrt; bt_reverse; factor_trial concat.
Maximum Phase-2 scope   k=2 only; frozen windows plus a small juggler check;
                        one Lean lemma if the integer obstruction is short.
Promotion criterion     Exact statement, natural domain, explains Phase-1,
                        not a census restatement, Lean path.
Stop criterion          k>2, general CAS, new residual state, termination claim.
```

## Metadata

- engine_control_version: `0.2.7`
- source_engine: `v2.3`
- experimental_status: `PHASE_2_SYMBOLIC_COMPOSITION_FALSIFIER`
- family decision: **MIXED**
- promoted concept: `odd_even_symbolic_composition`
- decision reason: odd-even T^2 < n is an exact juggler lemma; reverse-add and home-prime do not share it

## Target `juggler_sequence`

- Composition depth: 2
- Exact domain: odd n >= 3 with T(n) even (equivalently isqrt(n^3) even)
- Candidate statement: For integers n >= 2 with n odd and isqrt(n^3) even, T^2(n) = isqrt(isqrt(n^3)) < n.
- Derivation: Let m = isqrt(n^3) and k = isqrt(m). Then k^2 <= m and m^2 <= n^3, so k^4 <= n^3. If k >= n then n^4 <= n^3, hence n <= 1, contradicting n >= 2. The evenness of m identifies T^2 with isqrt o isqrt on n^3; it is not used in the inequality.
- Classification: **SYMBOLIC_COMPOSITION_PROMISING**
- Lean: `PROVED`
- Relation to Phase 1: Phase-1 bounded T^2 ranking survived because the composed map is strictly smaller than n on the same odd-to-even domain, not because of a new ranking template.
- Next proposal: `odd_even_symbolic_composition`

### Checks

- `t2_lt` (survived, n=43): For integers n >= 2 with n odd and isqrt(n^3) even, T^2(n) = isqrt(isqrt(n^3)) < n.

### Counterexamples

None on the stated domain.

### Mechanism

T^2(n) < n on the odd-to-even domain; Phase-1 V=log_bit is a downstream size consequence

- k=2 only. Odd-to-odd one-step states such as 3->5 are outside this composition.
- The inequality does not imply termination of the full floor-power map.

## Target `reverse_and_add_base3`

- Composition depth: 2
- Exact domain: frozen reverse-add window/orbit; T(x)=x+bt_reverse(x); k=2
- Candidate statement: Neither T^2(x) < |x| nor |T^2(x)| > |x| holds on the frozen two-step sample.
- Derivation: T^2(x) = x + W(x) + W(x+W(x)). One-step reverse_gap pointed at palindromes, but two-step composition both collapses some palindromes and expands other seeds. A window-local length inequality is not a two-step identity.
- Classification: **REVERSE_COMPOSITION_NEEDS_RICHER_STRUCTURE**
- Lean: `NOT_YET_FORMALIZATION_READY`
- Relation to Phase 1: Phase-1 reverse_gap failed because palindromes are not attractors. Two-step composition confirms mixed collapse and growth rather than a Lyapunov law.
- Next proposal: `symbolic_nonlinear_composition`

### Checks

- `t2_lt` (failed, n=3): T^2(x) < |x| for x != 0 with a two-step successor
  counterexample `3 -> 4 -> 8` (two-step reverse-plus-add is not a global descent; composition can grow)
- `t2_gt` (failed, n=1): |T^2(x)| > |x| for x != 0 with a two-step successor
  counterexample `1 -> 2 -> 0` (two-step reverse-plus-add is not a global ascent; small palindromes can collapse)
- `t2_length_ge` (failed, n=2): bt_length(T^2(x)) >= bt_length(x) whenever T^2 is defined
  counterexample `2 -> 0 -> 0` (canonical BT length can drop under T^2)

### Counterexamples

- `3 -> 4 -> 8`
- `1 -> 2 -> 0`
- `2 -> 0 -> 0`

### Mechanism

descent fails at 3->8; ascent fails at 1->0

- k=2 only. No palindrome-language engine. Length uses existing bt_length.

## Target `home_prime_49`

- Composition depth: 2
- Exact domain: frozen home-prime window/orbit; factor-concat word; k=2; primes are terminal
- Candidate statement: decimal_length(T^2(x)) >= decimal_length(x) on composite two-step samples
- Derivation: A weak two-step length inequality may survive while the one-step concat-length law already fails. Aggregate Omega/omega/length still miss the factor-word rewrite.
- Classification: **HOME_COMPOSITION_NEEDS_RICHER_STRUCTURE**
- Lean: `NOT_YET_FORMALIZATION_READY`
- Relation to Phase 1: Phase-1 V_C failed on 4->22 and 10->25. Two-step composition still sees concat as an itinerary rewrite, not as a scalar descent on (length, Omega, omega).
- Next proposal: `concat_word_composition`

### Checks

- `t2_decimal_length_ge` (survived, n=37): decimal_length(T^2(x)) >= decimal_length(x) on composite two-step samples
- `t_decimal_length_gt` (failed, n=5): decimal_length(T(x)) > decimal_length(x) whenever T(x) is still composite
  counterexample `10 -> 25 -> 55` (concatenation need not increase decimal length (e.g. 10->25))
- `t2_omega_ge` (failed, n=9): Omega(T^2(x)) >= Omega(x) on composite two-step samples
  counterexample `16 -> 2222 -> 211101` (total factor count can fall on a composite two-step, or is not a descent coordinate)

### Counterexamples

- `10 -> 25 -> 55`
- `16 -> 2222 -> 211101`

### Mechanism

concatenation need not increase decimal length (e.g. 10->25)

- k=2 only. No new factorization engine. Terminal primes are not ranked.
- Factorization cap is not mathematical evidence.
- Two-step decimal-length nondecrease on this window is a BOUNDED_SYMBOLIC_SURVIVOR, not a theorem.

## Cross-target comparison

| Target | Classification | Statement / failure | Lean |
| --- | --- | --- | --- |
| Juggler | SYMBOLIC_COMPOSITION_PROMISING | T^2(n) < n on the odd-to-even domain; Phase-1 V=log_bit is a downstream size consequence | PROVED |
| Reverse-add | REVERSE_COMPOSITION_NEEDS_RICHER_STRUCTURE | descent fails at 3->8; ascent fails at 1->0 | NOT_YET_FORMALIZATION_READY |
| Home Prime | HOME_COMPOSITION_NEEDS_RICHER_STRUCTURE | concatenation need not increase decimal length (e.g. 10->25) | NOT_YET_FORMALIZATION_READY |

## Ranking versus symbolic explanation

Phase-1 recorded a juggler ranking signal: `V = log_bit` decreases on odd-to-even `T^2`.
Phase-2 explains that signal: on the same domain, `T^2(n) < n` is an exact integer lemma,
so the ranking survivor is a downstream size consequence, not a new template.
Reverse-add and home-prime have no such explanation: composition produces mixed collapse/growth
and a factor-word rewrite, not a simpler exact bound.

## Cross-target mechanism

Juggler: composition → simpler state → exact bound (`T^2(n) < n`).
Reverse-add: composition → new complexity (collapse at `1→2→0`, growth at `3→4→8`).
Home Prime: composition → new complexity (concat is an itinerary rewrite; `10→25` keeps length,
`16→2222→211101` drops `Omega`).
There is no shared three-target composition theory.

## Decision

**MIXED**

odd-even T^2 < n is an exact juggler lemma; reverse-add and home-prime do not share it.

Promoted concept (not an executable attack): `odd_even_symbolic_composition`.
Not a universal symbolic-composition engine. Frozen v2.3 files unchanged.
Laboratory decision: **PARK** specifying any new attack.

## Best next question

Should odd-even T^2 < n be specified as a tiny juggler attack, while reverse-add and home-prime move to target-specific rewrite composition?
