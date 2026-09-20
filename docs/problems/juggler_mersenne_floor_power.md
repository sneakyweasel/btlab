# The floor power of a base-2 repunit

Status: **CLOSE** (two closed forms, one base-two restatement, and a
primality verdict; one family of density zero)

Standalone arithmetic phase. Not a termination theorem, not a cycle
statement, and not a change to any floor.

## Problem

Every exact floor-power value this laboratory owns sits on the
perfect-power locus, where the floor is not charged. Is there a family
off that locus where the charge is exactly computable, and does the
Mersenne appearance in the Lemma 8 floor carry prime content?

## Exact statement

Write \(M_a=2^a-1\). Three questions. (i) In base two, what does
\(x\equiv -1\pmod{2^a}\) say, and which \(x\) attain the Lemma 8 floor
\(x\ge 2^a-1\)? (ii) Is there a closed form for
\(\lfloor M_a^{3/2}\rfloor\)? (iii) Does the primality of \(M_a\) enter
the dynamics of either map?

## Current literature

- `hercher-2023-collatz-m-cycles`, Lemma 8. **known**; the base-two
  reading is an elementary restatement of its congruence.
- `mihailescu-2004-catalan`: Catalan, so \(2^a-c^k=1\) has no
  solution with \(c,k\ge 2\). **known**; used to show \(M_a\) is never a
  perfect power. The registry already applies Mihailescu to the
  different equation \(n^3-b^4\) in
  [odd_sharp_suffix](juggler_odd_sharp_suffix.md).
- The repository's exact floor-power values — `floorPower_of_even_sq`,
  `floorPower_of_odd_sq`, the `pow_two_depth` family in
  `Problems/Juggler/Equality.lean`. **extended**: all of them are on the
  perfect-power locus; this family is not.
- Search terms run and returning nothing anywhere in `docs/`, `src/`,
  `formal/`: `Mersenne`, `repunit`, `repdigit`, `trailing ones`,
  `3^a - 1`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     An exact floor-power value off the perfect-power locus,
                        and a verdict on the Mersenne primality.
Novelty hypothesis      2^a - 1 is just below a power of two, so the binomial
                        tail truncates and the floor is closed form for even a;
                        for odd a it becomes a Beatty value in sqrt 2.
Falsifier               A mismatch at any a, or the pattern failing to be the
                        stated bit string.
Already killed by?      No. The 2-adic integer bridge closed on cylinders, the
                        exact-floor-impact branch forbids another exact-step
                        census, and this is neither: it is a closed form on a
                        named family, and the family is never exact.
Existing machinery      floorPower, the Lemma 8 congruence, the exponent bridge.
Maximum Phase-0 scope   Closed forms verified to a = 400 (even) and 200 (odd);
                        the base-two run law; the LTE continuation; the
                        perfect-power exclusion.
Promotion criterion     A closed form that extends off the family, or prime
                        content that survives the bridge.
Stop criterion          The family has density zero and the primality is
                        decorative, which is a CLOSE.
```

## Balanced-ternary formulation

The landing point \(3^a-1\) is the all-twos string in base three, which
is the balanced-ternary neighbour of \(-1\); no further BT structure is
used.

## Why BT may be relevant

Only as the base-three reading of the landing point.

## Candidate operations / invariants

- \(\mathrm{run}(x)\) is the trailing-one count of \(x\); the floor is
  attained exactly at the repunits — **EXACT — HUMAN PROOF**
- \(M_a=(1^a)_2\) maps in \(a\) steps to \(3^a-1=(2^a)_3\) —
  **EXACT — HUMAN PROOF**
- the continuation is \(v_2(3^a-1)\) halvings, \(1\) for odd \(a\) and
  \(2+v_2(a)\) for even \(a\) — **KNOWN**, lifting the exponent
- \(\lfloor M_a^{3/2}\rfloor = 2^{3a/2}-3\cdot 2^{a/2-1}\) for even
  \(a\), bits \(1^{a-1}01 0^{a/2-1}\) — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED** to \(a=400\)
- \(\lfloor M_a^{3/2}\rfloor=\lfloor \sqrt2\,K\rfloor\) for odd \(a\) —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED** to \(a=200\)
- \(M_a\) is never a perfect power for \(a\ge 2\) — **KNOWN**, Catalan
- the primality is decorative — **EXACT — HUMAN PROOF**

## Experiments

`python -m research.juggler_sequence.mersenne_floor_power` writes
`data/research/juggler/mersenne_floor_power/summary.json` and
[juggler_mersenne_floor_power.md](../research/juggler_mersenne_floor_power.md).

## Conjectures

None.

## Counterexamples

None fired.

## Formalization

No new Lean module. The even closed form is a candidate for one — it is
a `Nat.sqrt` identity on an explicit family and would sit beside
`floorPower_of_odd_sq` — but it is not required by any result.

## Results

- **Lemma 8 is a statement about trailing bits.** \(\mathrm{run}(x)\) is
  the number of trailing one-bits of \(x\), and the floor \(x\ge 2^a-1\)
  is attained iff every bit is one, i.e. exactly at the base-2 repunits
  \(1,3,7,15,\ldots\).
- **Repunit to repdigit.** \(M_a=(1^a)_2\) maps in exactly \(a\)
  shortcut steps to \(3^a-1=(2^a)_3\), then takes exactly
  \(v_2(3^a-1)\) halvings, so the word opens \(O^aE^1\) for odd \(a\)
  and \(O^aE^{2+v_2(a)}\) for even \(a\).
- **The Juggler image is closed form.** For even \(a\ge 2\),
  \(\lfloor M_a^{3/2}\rfloor = 2^{3a/2}-3\cdot 2^{a/2-1}\), binary
  \(1^{a-1}0 1 0^{a/2-1}\), so the floor charge against the top of the
  cell is exactly \(3\cdot 2^{a/2-1}\). One binomial tail:
  \((1-x)^{3/2}=1-\tfrac32 x+\tfrac38x^2+\cdots\) at \(x=2^{-a}\)
  leaves a remainder in \((0,1)\) once both leading terms are integers.
- **For odd \(a\) it is a Beatty value in \(\sqrt2\).**
  \(\lfloor M_a^{3/2}\rfloor=\lfloor\sqrt2\,K\rfloor\) with
  \(K=2^{(3a-1)/2}-3\cdot 2^{(a-3)/2}\): the same
  2-adic-to-Archimedean seam the exponent bridge found at the end of an
  exact even tower, here off the perfect-power locus.
- **The primality is decorative.** The floor is attained at \(2^a-1\)
  for every \(a\): \(15=3\cdot5\), \(63=7\cdot9\), \(255\),
  \(511=7\cdot73\) all have \(\mathrm{run}=a\). What is structural is
  \(u=x+1=2^a\); "Mersenne" is \(u-1\), an artifact of that coordinate.
  Under the exponential bridge the extremal transports to the exponent
  \(e=2^r\) — one one-bit, not a repunit — so the all-ones pattern does
  not survive the transport and carries no prime content in either
  problem.
- **The family is the right contrast.** By Catalan, \(M_a\) is never a
  perfect power for \(a\ge 2\), so \(\mathrm{exactRun}(M_a)=0\): the
  repunits are maximally inexact starts, and the charge is still exact.

## Open questions

Whether the closed form extends to \(2^a-c\) for small \(c\), which is
the same binomial truncation with \(c\) leading terms, and whether any
such family is dense enough to matter. The laboratory's own answer to
the second is presumably no.

## Decision

**CLOSE**. Two new closed forms on a density-zero family, one
elementary restatement, and a primality verdict. Nothing moves; the
value is that the floor charge is exactly computable away from perfect
powers, which the repository's existing exact-value theorems did not
show.

Best next question: none from this branch.

## Publication assessment

Status: `STRUCTURAL`.
