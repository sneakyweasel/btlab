# Ranking-function Phase-0 falsifier

Status: **PHASE_0_FALSIFIER**

This is not a ranking synthesizer and not a termination proof.
It asks whether frozen v2.3 transition data already contain enough
monotone information for a tiny explicit template family to survive
exact bounded falsification.

## Branch budget

```text
Mathematical target     Do existing v2.3 transitions admit a simple
                        scalar ranking V outside a finite exceptional set E?
Novelty hypothesis      A tiny integer template family might already be
                        visible on the frozen campaigns that stalled at
                        global_inductive with no ranking attack.
Falsifier               Every canonical candidate fails on an exact
                        transition outside E, without a shared richer
                        ranking language; or the only survivors are
                        expansion anti-rankings / known halt restatements.
Existing machinery      Frozen v2.3 discovery windows/orbits; integer
                        bit_length, bt_length, decimal length, parity,
                        word_length; AttackProposalDossier.
Maximum Phase-0 scope   7^3 coefficient grid with gcd/sign canonicalization,
                        K<=8 known cores, exact integer comparisons,
                        four existing targets, no new state representation.
Promotion criterion     A coherent exact survivor on a primary target,
                        not a restatement of an existing invariant.
Stop criterion          Silent grid enlargement, SMT/neural search, a new
                        residual state, or thawing DEFAULT_ATTACK_ORDER.
```

## Metadata

- engine_control_version: `0.2.7`
- source_engine: `v2.3`
- experimental_status: `PHASE_0_FALSIFIER`
- attack_family: `ranking_function_synthesis`
- family decision: **REFINE**
- decision reason: scalar templates fail on multiple primary targets with structured branch/digit growth
- formalization: `not_yet_formalization_ready`

## Template family

```text
V(x) = a * log_bit(x) + b * d(x) + c * r(x)
a, b, c in {-3,-2,-1,0,1,2,3}, q = 0
log_bit(x) = bit_length(1+|x|)   # exact discrete stand-in for log(1+|x|)
```

Equivalent tuples are identified by positive scaling and sign reversal.
A coherent termination ranking requires a+b > 0 so that V has a net
positive size tilt. Expansion anti-rankings are rejected.
Decrease is exact integer comparison. No floating-point verdict.

## Target `juggler_sequence`

- Available features: log_bit=bit_length(1+|x|), digit=bit_length(|x|), residue=n mod 2
- Candidate count: 145
- Transitions tested: 40
- Exceptional set: 1
- Exactness: V is an integer linear form in (bit_length(1+|x|), digit, residue); decrease is exact integer comparison. Discrete bit_length stands in for log(1+|x|) as the already-available exact log-class statistic.
- Classification: **RANKING_NEEDS_RICHER_STATE**
- Formalization: `not_yet_formalization_ready`

### Survivors

None (no coherent scalar survivor).

### Strongest candidate

None.

### Phase-1 lexicographic proposal (not executed)

composed odd-then-even ranking: size of the current state is not enough because odd-to-odd floor-power can grow

### First counterexamples

- `V=(3,3,2)` fails at `3 -> 5` (GROWTH_BURST: odd floor-power branch increases magnitude, including odd-to-odd)
- `V=(1,1,1)` fails at `2 -> 1` (PARITY_SWITCH: residue/parity changes without a compensating size drop)
- `V=(2,-2,-3)` fails at `4 -> 2` (OTHER: V fails to decrease on this exact transition)

### Failure mechanisms

- odd floor-power branch increases magnitude, including odd-to-odd
- residue/parity changes without a compensating size drop
- V fails to decrease on this exact transition
- E={1} is the observed fixed point; T(x)=x already excludes it.

## Target `reverse_and_add_base3`

- Available features: log_bit=bit_length(1+|x|), digit=bt_length, residue=n mod 2
- Candidate count: 145
- Transitions tested: 48
- Exceptional set: 0
- Exactness: V is an integer linear form in (bit_length(1+|x|), digit, residue); decrease is exact integer comparison. Discrete bit_length stands in for log(1+|x|) as the already-available exact log-class statistic.
- Classification: **RANKING_NEEDS_RICHER_STATE**
- Formalization: `not_yet_formalization_ready`

### Survivors

None (no coherent scalar survivor).

### Strongest candidate

None.

### Phase-1 lexicographic proposal (not executed)

reverse-gap / palindrome-defect ranking; bt_length is unavailable as a descent coordinate because reverse-plus-add typically grows

### First counterexamples

- `V=(1,1,1)` fails at `1 -> 2` (DIGIT_REVERSAL: digit reverse-plus-add increases magnitude or length)
- `V=(0,0,1)` fails at `2 -> 0` (FEATURE_INSUFFICIENT: residue-only ranking cannot separate these states)
- `V=(1,-1,1)` fails at `2 -> 0` (OTHER: V fails to decrease on this exact transition)

### Failure mechanisms

- digit reverse-plus-add increases magnitude or length
- residue-only ranking cannot separate these states
- V fails to decrease on this exact transition
- E={0} is the reverse-fixed halt; T(0)=0.

## Target `home_prime_49`

- Available features: log_bit=bit_length(1+|x|), digit=decimal_length, residue=n mod 2
- Candidate count: 145
- Transitions tested: 36
- Exceptional set: (empty; fixed points already excluded by T(x)!=x)
- Exactness: V is an integer linear form in (bit_length(1+|x|), digit, residue); decrease is exact integer comparison. Discrete bit_length stands in for log(1+|x|) as the already-available exact log-class statistic.
- Classification: **RANKING_NEEDS_RICHER_STATE**
- Formalization: `not_yet_formalization_ready`

### Survivors

None (no coherent scalar survivor).

### Strongest candidate

None.

### Phase-1 lexicographic proposal (not executed)

piecewise composite-versus-prime ranking; decimal length grows on factor concatenation and primes are an infinite halt set

### First counterexamples

- `V=(1,1,1)` fails at `4 -> 22` (GROWTH_BURST: factor concatenation increases decimal length)

### Failure mechanisms

- factor concatenation increases decimal length
- Fixed primes already excluded by T(x)!=x; no extra exceptional states.

## Target `cyclic_tag_bit`

- Available features: log_bit=bit_length(1+|encoding|), digit=word_length, residue=leading bit
- Candidate count: 145
- Transitions tested: 44
- Exceptional set: 2
- Exactness: V is an integer linear form in (bit_length(1+|x|), digit, residue); decrease is exact integer comparison. Discrete bit_length stands in for log(1+|x|) as the already-available exact log-class statistic.
- Classification: **RANKING_IMPLAUSIBLE**
- Formalization: `not_yet_formalization_ready`

### Survivors

None (no coherent scalar survivor).

### Strongest candidate

None.

### First counterexamples

- `V=(1,1,1)` fails at `3 -> 7` (LENGTH_NONDECREASE: rewrite length does not decrease)

### Failure mechanisms

- rewrite length does not decrease
- Negative control: |T(w)| >= |w| whenever a successor exists.

## Aggregate falsifier report

### Target matrix

| Target | Best result | Failure mechanism | Classification |
| --- | --- | --- | --- |
| Juggler | composed odd-then-even ranking: size of the current state is not enough because odd-to-odd floor-power can grow | odd floor-power branch increases magnitude, including odd-to-odd | RANKING_NEEDS_RICHER_STATE |
| Reverse-add | reverse-gap / palindrome-defect ranking; bt_length is unavailable as a descent coordinate because reverse-plus-add typically grows | digit reverse-plus-add increases magnitude or length | RANKING_NEEDS_RICHER_STATE |
| Home Prime 49 | piecewise composite-versus-prime ranking; decimal length grows on factor concatenation and primes are an infinite halt set | factor concatenation increases decimal length | RANKING_NEEDS_RICHER_STATE |
| Cyclic tag | length ranking refuted (negative control) | rewrite length does not decrease | RANKING_IMPLAUSIBLE |

### Cross-target evidence

- digit-length jumps
- lack of sufficient state variables

## Decision

**REFINE** ranking-function synthesis as the first
executable v2.4 attack family.

scalar templates fail on multiple primary targets with structured branch/digit growth.

This does not thaw `DEFAULT_ATTACK_ORDER`. It does not prove termination.
Updated Top-3 proposals live in the machine-readable record and are not
executed. Frozen v2.3 campaign files are unchanged.

## Best next question

Can a deliberately small richer family — odd-even composition, reverse-gap/palindrome defect, and composite-versus-prime piecewise ranking — be falsified on the same exact transition tables without enlarging the coefficient grid?
