# Juggler cyclic word feasibility

Closed-word question `CycReal(w)`: some `n>=2` realises `w` and `T^k(n)=n`. Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. Not a halt theorem.

- classification: `CYCLIC_FEASIBILITY_CLOSED`
- reason: cheap cyclic filters are the existing CycleItinerary layer (envelope, odd_itinerary_expands, even-count <= 3, length >= 11); interval and phi-product never fire; the residue is the already-studied e>=4 leftover family
- k_max: `8`
- n_max: `160`
- claim: `NOT OBSERVED WITHIN SEARCH BOUND`

## Primitive necklaces

| k | primitive | exponent-ok | mixed expanding | e<=3 expanding | leftover e>=4 |
|---|---|---|---|---|---|
| 1 | 2 | 1 | 0 | 0 | 0 |
| 2 | 1 | 0 | 0 | 0 | 0 |
| 3 | 2 | 1 | 1 | 1 | 0 |
| 4 | 3 | 1 | 1 | 1 | 0 |
| 5 | 6 | 1 | 1 | 1 | 0 |
| 6 | 9 | 3 | 3 | 3 | 0 |
| 7 | 18 | 4 | 4 | 4 | 0 |
| 8 | 30 | 4 | 4 | 4 | 0 |

A001037 match: `True`.

## Filter survival

`{'power_bound_contracts': 55, 'no_cycle_itinerary_even_count_le_three': 14}`

known CycleItinerary deaths: `69`. new joint (interval/phi): `0`. plus-one m=2 scans: `0`. leftover residue: `0` unresolved `0`.

## Direct cycles

n<=`160` exact cycles: `0`.

## Near-cycles

No leftover-shaped near-cycle in the window.

## Strongest global closure inequality

The unweighted cell product

`prod_O x^3/(x+1)^2 * prod_E x/(x+1)^2 < 1`

is necessary on any integer cycle. It kills all-odd itineraries with states `>=3`, already excluded by `odd_itinerary_expands`. On mixed leftover itineraries the even factors can be arbitrarily small, so the product does not fire from interval hulls.

## Relation to CycleMin

After the existing CycleItinerary layer the only expanding mixed necklaces have `e>=4` and length `>=11`. That is `cycle_itinerary_length_ge_eleven`. Joint interval / phi-product constraints did not shrink this residue.

## Anti-overclaim

Not a no-cycle theorem. Not a halt theorem. Finite search is not emptiness.

