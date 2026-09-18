# Paper B: survivors and minimal certificates are one recursion (Lean)

## Problem

Whether the minimal-certificate count `M_d` and the survivor count `N_d` are two
readings of one quantity, and whether the link proves the certificate-density
plateaus in general rather than at listed depths.

## Exact statement

Let `N_d = neverNegCount d` count the length-`d` parity words no prefix of which
contracts, and `M_d = minimalCertCount d` count the minimal certificates of
length `d`. Then for every `d`:

1. `neverNegCount_add_minimalCertCount`: `N_{d+1} + M_{d+1} = 2 * N_d`.
2. `certifiedWordCount_succ`:
   `#C_{d+1} = 2 * #C_d + M_{d+1}`.
3. `density_succ`: `#C_{d+1} / 2^(d+1) = #C_d / 2^d + M_{d+1} / 2^(d+1)`, so the
   certificate density gains exactly the cylinder measure of the new minimal
   certificates.
4. `minimalCertCount_eq_zero_of_window_empty`: an empty odd-count window leaves
   no minimal certificate of that length.
5. `density_flat_of_window_empty`: hence when no power of three lies in
   `[2^d, 2^(d+1))`, the density at depth `d+1` equals the density at depth `d`.

The proof of (1) is one extension step. A word `w ++ [b]` of length `d+1` has a
contracting prefix iff `w` does or `w ++ [b]` itself contracts; so the extensions
of the survivors of length `d` split, disjointly and exhaustively, into the
survivors of length `d+1` and the minimal certificates of length `d+1`. Each
survivor has two extensions, giving `2 * N_d`.

## Current literature

`extended`. Paper B's
[note](../theory/juggler_parity_discrepancy_note.md) proves density statements at
fixed small depths and does not state a recursion. The recursion is elementary
once the decomposition is seen; nothing here claims a literature priority. The
`N_d` values are already in
[juggler_k3_rate_free.md](juggler_k3_rate_free.md) and `PaperBSurvivorDecay`.

## Branch budget

- **Target:** is `M_d` the same constrained-walk quantity as `N_d`, and does the
  link prove the plateau law for all `d`?
- **Novelty hypothesis:** the exact density increment `M_{d+1}/2^(d+1)`, which
  generalises `PaperBFiveStepDensity.five_cylinders_card_sum` from depth five to
  every depth.
- **Falsifier:** a depth where the recursion fails, or where `M_d = 0` but the
  density moves. None to `d = 14`.
- **Already killed by?:** none. Same reasoning as
  [juggler_paper_b_certificate_lengths.md](juggler_paper_b_certificate_lengths.md):
  a finite-word identity, to which none of the three tests applies.
- **Existing machinery:** `RateFreeDensity` (`allWords_succ`,
  `extend_fiber_disjoint`, `neverNegWords`), `PaperBFiveStepDensity`
  (`certifiedWordCount`, `certifiedWordCount_add_neverNegCount`),
  `PaperBCertificateLengths` (`CertWindow`, `minimalCert_window`).
- **Maximum Phase-0 scope:** one Lean module and the ceremony. The size of `M_d`
  stays open.
- **Promotion criterion:** the recursion and the density increment proved for all
  `d`, not by `decide` at listed depths.
- **Stop criterion:** if the partition needs a bijection `Finset` cannot express,
  `PARK` with the numeric evidence.

## Balanced-ternary formulation

Not used; parity words and powers of two and three.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

The one-letter extension; `prefixNoncontracting` and `IsMinimalCertificate` as
the two outcomes of extending a survivor.

## Experiments

Enumeration for `d = 1..14` confirms `N_d = 2 N_{d-1} - M_d` at every depth, and
confirms `M_d = 0` exactly when the density is flat from `d-1` to `d`. Measured
`M_d` for `d = 1..16` is `1, 1, 0, 1, 2, 0, 3, 7, 0, 12, 0, 30, 85, 0, 173, 476`.
The survival ratio `M_d / (2 N_{d-1})` is `0.500, 0.250, 0.333, 0.188, 0.269,
0.158, 0.117, 0.188, 0.118, 0.184` at the carrying depths and oscillates without
converging. It is zero exactly when `frac(d * beta) > beta`, `beta = log2/log3`,
which is the rotation criterion of the length branch seen in its own coordinate.

## Conjectures

None. The size of `M_d` is recorded as open, not conjectured.

## Counterexamples

None; the falsifier did not fire, and (1)-(5) are proved for all `d`.

## Formalization

`formal/Problems/Juggler/PaperBCertificateRecursion.lean`, imported by the
umbrella `Problems.Juggler`, registered in `AUXILIARY_MODULES`, outside the Paper
B barrel like both modules it imports.

Sixteen declarations, no `sorry`. The two characterisation lemmas
`prefixNoncontracting_concat` and `isMinimalCertificate_concat` carry the whole
argument; `extensions_eq_survivors_union_certs` is the partition and
`neverNegCount_add_minimalCertCount` the count. The named plateaus
`density_flat_five_to_six`, `density_flat_eight_to_nine` and
`density_flat_ten_to_eleven` are corollaries, not separate computations.

## Results

`J-paper-b-survivor-certificate-recursion` — `EXACT — LEAN VERIFIED`.

The plateaus are now proved rather than enumerated: `7/8` at both `d = 5` and
`d = 6`, `237/256` at both `d = 8` and `d = 9`, `15/16` at both `d = 10` and
`d = 11`.

## Open questions

The size of `M_d` at a carrying depth. By the recursion this is equivalent to the
asymptotics of `N_d`, so `PaperBSurvivorAsymptotic`'s `MeanderShape` hypothesis
can now be stated either way: as the shape of the survivor count, or as the
behaviour of the increment `M_d / 2^d`. That is a reformulation and not a proof,
and the missing local limit theorem for a walk against a Sturmian barrier remains
missing. What the recursion does supply is that the oscillation measured in
`J-paper-b-meander-prefactor-is-almost-periodic` has an exact finite meaning at
every depth, rather than only an asymptotic one.

## Decision

`PROMOTE` — the recursion, the density increment and the plateau law hold for all
`d`, and the falsifier did not fire. Nothing analytic was proved. Best next
question: the recursion makes `N_d` a product `2^d * prod (1 - M_k / (2 N_{k-1}))`;
is the factor `M_k / (2 N_{k-1})` a function of `frac(k * beta)` alone, which is
what the almost-periodic prefactor would require?

## Publication assessment

Status: `THEOREM`. Proves a law Paper B's Section 5 only instantiates, and
explains the plateaus, but moves no density and proves no estimate.
