# A325904: exact generator audit for Paper B

Status: **CLOSE** as a new counting or asymptotic method. The finite check is
useful: it exposes two discrepancies in the dated OEIS records and supplies
an independent arithmetic check. It changes no paper theorem.

## Problem

Can the signed generator A325904 simplify or independently verify Paper B's
survivor and minimal-certificate counts?

## Exact statement

Write \(L(r)=\lfloor r\log_2 3\rfloor+1\), \(A(n)=M_{L(n)}\) for \(n\ge1\),
where \(M_d\) is the minimal-certificate count. Thus \(A\) is A100982.
The separate \(M_1=1\) is the extra leading term in A186009.

Put \(c(j)=\lfloor j/(\log_2 3-1)\rfloor\), the sequence A325913, and define
\(G_0=1,G_1=0\) by the recurrence printed in A325904:
\[
G_j=-\sum_{k=0}^{j-1}G_k {c(j)+j-k-2\choose c(j)-2}\qquad(j\ge2).
\]
All calculations use integers. The index \(c(j)\) is obtained by finding
the last \(m\) with \(3^m<2^{m+j}\), without floating-point logarithms.

The candidate repaired transform is
\[
A(1)=1,\qquad
A(n)=\sum_{k=0}^{L(n-1)-n}G_k{L(n-1)-k-2\choose n-2}\quad(n\ge2).
\]
Its upper limit includes all potentially nonzero binomial terms. The
published limit is \(L(n-1)-n-2\), two terms shorter.

**COMPUTATIONALLY VERIFIED**, not an all-orders identity: the repaired
transform agrees with the independent prefix dynamic program at every
order \(1\le n\le256\). Reinserting zeros by length and using
\(N_d=2N_{d-1}-M_d\) recovers every survivor count \(0\le d\le406\).

## Current literature

- [A325904](https://oeis.org/A325904): generator and recurrence, revision
  #33, 17 October 2019.
- [A325913](https://oeis.org/A325913): exact boundary indices.
- [A100982](https://oeis.org/A100982): Lombardo's transform of 18 October
  2019; the local record is revision #258, 17 September 2026.
- [A076227](https://oeis.org/A076227): survivor counts.
- The original two-index recursion is already attributed to Terras 1976;
  see [Paper B's prior-art record](../theory/paper_b_prior_art_and_names.md).

Source: local OEIS MCP, export 20 September 2026, Git revision
`9cee00061c60192aafbc74726ce4a83ca7040d81`.
OEIS Foundation, CC BY-SA 4.0. The web retrieval of A100982/internal on
23 September returned an older revision (#243) with the same faulty
summation limit; it is not evidence of the site's current editorial state.
No OEIS program was executed and no external correction was submitted.

Project relationship: **reproduced**, with arithmetic discrepancies documented.
No novelty is claimed for the transform or its underlying counting objects.

## Branch budget

```text
Mathematical target     Check the signed generator against Paper B's exact counts.
Novelty hypothesis      A simpler identity or independent computational check.
Falsifier               Only the known counts are reproduced.
Already killed by?      No recorded A325904 check; the counts themselves are known.
Existing machinery      Integer prefix DP, OEIS MCP, exact binomial arithmetic.
Maximum Phase-0 scope   256 certificate orders and the needed generator coefficients.
Promotion criterion     A consequence beyond reproducing the known formulas.
Stop criterion          No stronger bound, asymptotic input, or demonstrated advantage.
```

## Balanced-ternary formulation

The objects are ordinary integer counts. Changing their numeral representation
does not change the recurrence.

## Why BT may be relevant

No role is used or claimed.

## Candidate operations / invariants

The repaired transform is an independent finite check, not a replacement for
the nonnegative path DP. The generator has signed terms and cancellation.
No speed comparison or numerical-stability improvement is claimed.

## Experiments

Runner: `python tools/lab.py run research.juggler_sequence.oeis_generator_check --write`.

[Probe](../../src/research/juggler_sequence/oeis_generator_check.py),
[tests](../../tests/research/juggler_sequence/test_oeis_generator_check.py), and
[exact report](../../data/research/juggler/oeis_generator_check/verification.json).

The report records the source revision, six stored-term discrepancies,
the printed-formula counterexample, the checked ranges and every mismatch.
A separate test inverts the transform from the path DP to recover more than
50 generator coefficients, independently of the stated generator recurrence.

## Conjectures

None registered. The repaired all-orders formula remains unproved here;
finite agreement is not silently promoted to a theorem.

## Counterexamples

**REFUTED (as printed):** at \(n=2\), the A100982 sum has upper limit
\(L(1)-2-2=-2\), so it is empty and equals zero. But \(A(2)=1\):
OOEE is the unique order-two minimal certificate.

The stored A325904 terms match its exact recurrence through index 20, then
disagree at every stored index 21 through 26:

| Index | Stored term | Exact recurrence |
|---|---:|---:|
| 21 | -517564939540551 | -517564939540550 |
| 22 | 1890772860334557 | 1890772860334508 |
| 23 | 3323588929061820 | 3323588929063104 |
| 24 | -104547561696315008 | -104547561696337925 |
| 25 | 907385094824827328 | 907385094825133652 |
| 26 | -6313246535826877248 | -6313246535830021678 |

Even with the summation limit repaired, using the stored coefficients first
fails at order 37: it produces 123110229387833 instead of 123110229387834.
The entry's Python example uses floating-point factorial division; this is
a reason to avoid that arithmetic, not a verified account of the table's origin.

These regressions live in the branch test file linked above.

## Formalization

No new Lean module. The existing Paper B recursion is already formalized.
The repaired transform and the generator computation have only the finite
verification stated here.

## Results

- **REFUTED:** the printed A100982 summation limit, by the exact order-two witness.
- **COMPUTATIONALLY VERIFIED:** the repaired transform at orders 1 through 256,
  reconstruction through depth 406, and the six stored-coefficient discrepancies.
- **REPARAMETERIZATION:** the generator expresses existing path counts; no new
  density, phase-profile limit or Juggler termination result follows.

## Open questions

An all-orders proof of the repaired transform and a review of the OEIS
discrepancies remain possible. Neither is needed to retain Paper B's independently
verified counts. No external submission is authorized by this local check.

## Decision

**CLOSE.** Retain the arithmetic regressions and source corrections. The bounded
check yields no stronger count bound or new input for Paper B's open analytic
problem. This is not a reason to replace the existing DP.

Best next question: can the repaired transform be proved for all orders directly
from the gated Pascal recursion? Recorded only; no continuation is opened.

## Publication assessment

Status: **ARCHIVED**. Useful reproducibility and attribution work, not a new
paper theorem. Existing manuscript claims and release artifacts are unchanged.
