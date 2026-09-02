# Juggler cycle equal valleys

Status: **EQUAL_VALLEYS_CLOSED**

Can every local minimum equal the CycleMin start n?
Not a halt theorem. Not a leftover-length exclusion. No new Lean.

## Metadata

- classification: **EQUAL_VALLEYS_CLOSED**
- floor: `261`
- leftover L: `84` o=`53` even=`31`
- unique visit of n: `True`
- all-equal only if m=1 or a shorter cycle: `True`
- second valley ≥ n+2: `True`
- n+2 leftover-killer slogan false: `True`

all m valleys equal n is impossible for m≥2 on a leftover length (intermediate return is a shorter CycleItinerary). The next odd n+2 does not exclude L=84 at m=3: split RHS 0.003515 > θ=0.002086 at floor 261, Lean constant 1. Height plus n+2 is 0.002180. Height-split killing n2 is 281

## Split-valley finance at leftover L=84

- m=`3` const=`1.0` θ=`0.00208595` all-n RHS=`0.0035274` split n+2 RHS=`0.00351506` height RHS=`0.00219263` height+n+2 RHS=`0.00218028` n+2 kills=`False` height+n+2 kills=`False` height-split n2=`281`
- m=`3` const=`1.2` θ=`0.00208595` all-n RHS=`0.00423288` split n+2 RHS=`0.00421807` height RHS=`0.00263115` height+n+2 RHS=`0.00261634` n+2 kills=`False` height+n+2 kills=`False` height-split n2=`369`
- m=`4` const=`1.0` θ=`0.00208595` all-n RHS=`0.00418753` split n+2 RHS=`0.00416901` height RHS=`0.00290988` height+n+2 RHS=`0.00289136` n+2 kills=`False` height+n+2 kills=`False` height-split n2=`403`
- m=`31` const=`1.0` θ=`0.00208595` all-n RHS=`0.0220109` split n+2 RHS=`0.0218258` height RHS=`0.0220108` height+n+2 RHS=`0.0218256` n+2 kills=`False` height+n+2 kills=`False` height-split n2=`4835`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- halt_theorem: `False`
- no_cycle_all_lengths: `False`
- new_lean: `False`
- floor_raise: `False`
- height_law_formalized: `False`
- leftover_word_census: `False`

## Decision

**EQUAL_VALLEYS_CLOSED**

all m valleys equal n is impossible for m≥2 on a leftover length (intermediate return is a shorter CycleItinerary). The next odd n+2 does not exclude L=84 at m=3: split RHS 0.003515 > θ=0.002086 at floor 261, Lean constant 1. Height plus n+2 is 0.002180. Height-split killing n2 is 281

