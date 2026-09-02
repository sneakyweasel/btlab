# Juggler O^7 EEEE +1-chain gap

Status: **O7EEEE_GAP_PROVED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. If n follows O^7, then
T^7(n) >= (n+1)^16, so the EEEE inverse cell is empty.

## Branch budget

```text
Mathematical target     Prove T^7(n) >= (n+1)^16 on O^7 starts
Novelty hypothesis      the leftover 4-fudge is the slack;
                        the exact +1 cell fires at 256
Falsifier               an O^7 image below (n+1)^16, or the
                        +1-chain still needs n ~ 10^8
Existing machinery      (T+1)^2 > x^3; x_k >= n on odd runs;
                        no_follows_seven_odds_of_lt256;
                        leftover_prefix_preimage at N0=828484409
Maximum Phase-0 scope   one-word +1-chain; no Lean, no Z5,
                        no thirty-itinerary census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **O7EEEE_GAP_PROVED**
- sorry-free: `True`

no O^7 below 256; +1-chain gives T^7(n) >= (n+1)^16 for n>=256; pin n<10000 has 84 O^7 starts, first=289, zero cell hits, min ratio 445.01033356279396 at n=289.

## Arithmetic

- step exponents: `[1458, 972, 648, 432, 288, 192, 128]`
- plus exponent: `3990`
- comparison n^6177 > (n+1)^6038
- seven-odd cutoff: `256`
- leftover-cell N0: `828484409`
- elementary checks: `{'exponents_match': True, 'plus_exp': True, 'left_exp': True, 'right_exp': True, 'three_mul_pow256': True, 'three_pow24_lt_two_pow40': True, 'split_6038': True, 'cutoff_is_256': True}`

## Pin

- n<10000: first_o7=`289` o7=`84` above=`84` misses=`[]` min_ratio=`445.01033356279396` at n=`289`

## Proof

Write x_0 = n and x_{k+1} = floor(x_k^{3/2}) along an O^7
run, so each x_0,...,x_6 is odd and x_7 = T^7(n). The exact
odd cell is x_k^3 < (x_{k+1}+1)^2. Also x_1 = isqrt(n^3) >= n
and the odd run is nondecreasing, so x_k >= n for every k.

Raising n^3 < (x_1+1)^2 to the 3^6 gives n^{2187} < (x_1+1)^{1458}.
Cross-multiply by n^{1458} and use n(x_1+1) <= (n+1) x_1, then
replace x_1^{1458} = (x_1^3)^{486} < (x_2+1)^{972}. Repeating
through x_6 produces

    n^{6177} < (n+1)^{3990} (x_7+1)^{128}.

The exponents 1458,972,648,432,288,192,128 are 2^k 3^{7-k}.
The first six sum to 3990; 2187+3990=6177.

If n^{6177} > (n+1)^{6038} = (n+1)^{3990+2048}, then
x_7+1 > (n+1)^{16}, so x_7 >= (n+1)^{16}. For n >= 256 this
comparison reduces to 256^{6177} > 257^{6038}:

- (n+1)/n <= 257/256, because 256(n+1) <= 257 n iff n >= 256;
- (257/256)^{6038} = (257/256)^{256*23+150} < 3^{24}, because
  257^{256} < 3 * 256^{256};
- 3^{24} < 2^{40}, because 27^8 < 32^8;
- 256^{139} = 2^{1112} > 2^{40}.

Thus 256^{139} > (257/256)^{6038}, hence 256^{6177} > 257^{6038},
and the same holds for every larger n. Lean has
no_follows_seven_odds_of_lt256, o7_image_ge_succ_pow16, and
no_cycle_itinerary_oooooooeeee. The EEEE inverse cell
[n^{16}, (n+1)^{16}) is empty, and O^7 EEEE is not a cycle itinerary.

This is not leftover_prefix_preimage: that comparison uses the
factor 2^{4118} and first fires at n = 828484409. The +1-chain
replaces the 4-fudge by the exact successor cell.

Paper A does not import these theorems. This is not a
length-11 census.

## Lean

- `no_follows_seven_odds_of_lt256`: `True`
- `leftover_prefix_preimage`: `True`
- `cycle_trailing_evens_lt`: `True`
- `odd_preimage_unique`: `True`
- `o7_image_ge_succ_pow16`: `True`
- `no_cycle_itinerary_oooooooeeee`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `juggler_reaches_one`: `True`
- Paper A has no O^7 EEEE theorem: `True`
- FloorPower not rewritten: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycle_impossible: `False`
- length_eleven_census: `False`
- four_even_impossible: `False`
- finite_progress_for_all: `False`

## Decision

**O7EEEE_GAP_PROVED**

no O^7 below 256; +1-chain gives T^7(n) >= (n+1)^16 for n>=256; pin n<10000 has 84 O^7 starts, first=289, zero cell hits, min ratio 445.01033356279396 at n=289.

This is not a halt result and not a length-11 census.
The other twenty-nine leftovers are a separate job.

