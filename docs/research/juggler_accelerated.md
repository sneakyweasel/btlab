# Juggler accelerated odd-to-odd map

Status: **ACCELERATION_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Defines the first-return-to-odd
map A as a derived object and compares it with one-step J and
the existing ResidualStep. Does not reopen PE-factor, residual
future-quotient, sum-rho, realization geometry, information
complexity, first-return scalars, or backward-geometry censuses.

## Branch budget

```text
Mathematical target     Does first-return-to-odd A have a simpler
                        exact law than one-step J or ResidualStep?
Novelty hypothesis      Even-tail collapse exposes a new odd-to-odd law
Falsifier               every identity is T_w / ResidualStep / cells
Existing machinery      floor_power, residual_excursion, globalDefect,
                        image_monotone_of_follows, floor cells
Maximum Phase-0 scope   odd n<=4000; algebraic comparison; decide
```

## Metadata

- window: odd `n=3..4000`
- engine control layer modified: `False`
- classification: **ACCELERATION_COMPLEX**
- sorry-free: `True`
- algorithm: `accelerated-odd-return-v1`

## A. Definition

For odd n>1

\[
r(n)=\min\{r\ge 1:J^r(n)\text{ is odd}\},\qquad A(n)=J^{r(n)}(n).
\]

The first letter from an odd start is always O, so the branch is
`(1,0)` when J(n) is odd and `(1,b)` when J(n) is even and
exactly b subsequent even steps reach the next odd. This is
not ResidualStep: ResidualStep consumes a full odd run before the
even tail and forbids b=0.

- starts: `1999` ok `1999` failed `[]`
- `a` identically 1: `True`
- domain complete in window: `True`
- J(n) odd (branch `(1,0)`): `1009`
- J(n) even (branch `(1,b)`): `990`
- odd image is one-step J: `True`
- even image equals ResidualStep with `a=1`: `True`
- odd image differs from ResidualStep landing: `True`

Definitional rows:

`[{'n': 3, 'target': 5, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 5, 'j_image_parity': 1, 'residual_a': 3, 'residual_b': 3, 'residual_y': 1, 'peak': 5, 'validation_status': 'OK'}, {'n': 5, 'target': 11, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 11, 'j_image_parity': 1, 'residual_a': 2, 'residual_b': 3, 'residual_y': 1, 'peak': 11, 'validation_status': 'OK'}, {'n': 7, 'target': 1, 'a': 1, 'b': 3, 'r': 4, 'word': 'OEEE', 'j_image': 18, 'j_image_parity': 0, 'residual_a': 1, 'residual_b': 3, 'residual_y': 1, 'peak': 18, 'validation_status': 'OK'}, {'n': 9, 'target': 27, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 27, 'j_image_parity': 1, 'residual_a': 2, 'residual_b': 1, 'residual_y': 11, 'peak': 27, 'validation_status': 'OK'}, {'n': 11, 'target': 1, 'a': 1, 'b': 3, 'r': 4, 'word': 'OEEE', 'j_image': 36, 'j_image_parity': 0, 'residual_a': 1, 'residual_b': 3, 'residual_y': 1, 'peak': 36, 'validation_status': 'OK'}, {'n': 15, 'target': 7, 'a': 1, 'b': 1, 'r': 2, 'word': 'OE', 'j_image': 58, 'j_image_parity': 0, 'residual_a': 1, 'residual_b': 1, 'residual_y': 7, 'peak': 58, 'validation_status': 'OK'}, {'n': 21, 'target': 9, 'a': 1, 'b': 1, 'r': 2, 'word': 'OE', 'j_image': 96, 'j_image_parity': 0, 'residual_a': 1, 'residual_b': 1, 'residual_y': 9, 'peak': 96, 'validation_status': 'OK'}, {'n': 25, 'target': 125, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 125, 'j_image_parity': 1, 'residual_a': 3, 'residual_b': 2, 'residual_y': 15, 'peak': 125, 'validation_status': 'OK'}, {'n': 37, 'target': 225, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 225, 'j_image_parity': 1, 'residual_a': 4, 'residual_b': 1, 'residual_y': 9317, 'peak': 225, 'validation_status': 'OK'}, {'n': 49, 'target': 343, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 343, 'j_image_parity': 1, 'residual_a': 2, 'residual_b': 1, 'residual_y': 79, 'peak': 343, 'validation_status': 'OK'}, {'n': 63, 'target': 1, 'a': 1, 'b': 4, 'r': 5, 'word': 'OEEEE', 'j_image': 500, 'j_image_parity': 0, 'residual_a': 1, 'residual_b': 4, 'residual_y': 1, 'peak': 500, 'validation_status': 'OK'}, {'n': 69, 'target': 573, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 573, 'j_image_parity': 1, 'residual_a': 2, 'residual_b': 1, 'residual_y': 117, 'peak': 573, 'validation_status': 'OK'}, {'n': 77, 'target': 675, 'a': 1, 'b': 0, 'r': 1, 'word': 'O', 'j_image': 675, 'j_image_parity': 1, 'residual_a': 3, 'residual_b': 1, 'residual_y': 1523, 'peak': 675, 'validation_status': 'OK'}]`

Label: `COMPUTATIONALLY VERIFIED`. The Collatz analogy fails
uniformly: 3n+1 is always even for odd n; floor(n^(3/2)) is not.

## B. Branch distribution

- observed `(a,b)` counts: `{'1,0': 1009, '1,1': 482, '1,2': 243, '1,3': 70, '1,4': 30, '1,5': 165}`
- `b` range: `0` … `5`

Frequencies are not a theorem. `a` cannot vary under first-return-to-odd.
Examples such as `(3,2)` are ResidualStep labels, already implemented
as `residual_excursion`.

Label: `OBSERVATION`.

## C. Macro compression

- distinct first branches: `6`
- distinct first words: `6`
- selected letter savings: `[(3, 6, 3, 3), (9, 7, 3, 4), (15, 2, 1, 1), (37, 17, 9, 8), (49, 6, 3, 3), (63, 5, 1, 4), (69, 8, 4, 4), (77, 10, 6, 4), (173, 26, 16, 10), (193, 22, 16, 6), (365, 16, 9, 7), (425, 23, 16, 7)]`

Replacing O by (1,0) and OE^b by (1,b) is run-length of an even tail. It does not compress odd runs.

Label: `OBSERVATION`. Compression is not a discovery.

## D. Exact macro equations

On a realized branch `(1,b)` the identity A(n)=J^{1+b}(n)=T_w(n)
with w=OE^b (or w=O) is `image_eq_iterate`. The envelope
\(A(n)^{2^{1+b}}\le n^{3}\) is the existing finite-itinerary bound, not a
new result. The exact defect

\[
\Delta_{1,b}(n)=n^{3}-A(n)^{2^{1+b}}
\]

matches `global_defect` on every formable word: `True`.
On `(1,0)` it is the local odd defect: `True`.

There is no simpler O-run / E-run / transition decomposition than
`global_defect_append` / `residualStep_global_defect`.

Label: `REPACKAGING`.

## E. Macro contraction

- `A<n` `990` `A=n` `0` `A>n` `1009`
- dictionary `A<n` iff `J(n)` even: `True`
- odd-image contractions: `0`
- even-image expansions: `0`

A(n)<n iff J(n) is even; A(n)>=n iff J(n) is odd. Odd case is floorPower_odd_ge. Even case is floor(n^{3/2})<n^2 then strictly decreasing isqrt, i.e. OE^b and power_bound_contracts.

This is not stronger than `power_bound_contracts` on `OE^b` plus
`floorPower_odd_ge` on `O`. Not `MACRO_CONTRACTION_GREEN`.

Label: `EXACT — HUMAN PROOF`, novelty `REPARAMETERIZATION`.

## F. Macro peaks

- max peak: `{'n': 3999, 'peak': 252887, 'word': 'O'}`
- max peak/n: `{'n': 3999, 'ratio': '252887/3999', 'peak': 252887, 'word': 'O'}`
- O-run peak: `{'n': 3999, 'peak': 252887}`
- E-run peak: `{'n': 3995, 'peak': 252508}`

One-step peak of A is J(n) or the start; not a nontermination signal

Label: `OBSERVATION`.

## G. Macro inverse geometry

Fixed `(1,0)`: `Pred_O(m)`, at most one integer (`odd_preimage_unique`).
Fixed `(1,b)`: one odd cell then `b` even square cells. This is the
closed backward-geometry conclusion, not a new inverse law.

- starts lie in the cell fiber: `True`
- new inverse formula: `False`
- examples: `[{'m': 5, 'a': 1, 'b': 0, 'ok': True, 'predecessors': [3], 'count': 1, 'truncated': False, 'cell': 'Pred_O(m)', 'n': 3, 'contains_start': True, 'word': 'O'}, {'m': 11, 'a': 1, 'b': 0, 'ok': True, 'predecessors': [5], 'count': 1, 'truncated': False, 'cell': 'Pred_O(m)', 'n': 5, 'contains_start': True, 'word': 'O'}, {'m': 1, 'a': 1, 'b': 3, 'ok': True, 'predecessors': [7, 11, 13, 17], 'count': 4, 'truncated': False, 'cell': 'Pred_O then Pred_E^3', 'even_fiber': 21, 'n': 7, 'contains_start': True, 'word': 'OEEE'}, {'m': 27, 'a': 1, 'b': 0, 'ok': True, 'predecessors': [9], 'count': 1, 'truncated': False, 'cell': 'Pred_O(m)', 'n': 9, 'contains_start': True, 'word': 'O'}, {'m': 1, 'a': 1, 'b': 3, 'ok': True, 'predecessors': [7, 11, 13, 17], 'count': 4, 'truncated': False, 'cell': 'Pred_O then Pred_E^3', 'even_fiber': 21, 'n': 11, 'contains_start': True, 'word': 'OEEE'}, {'m': 7, 'a': 1, 'b': 1, 'ok': True, 'predecessors': [15], 'count': 1, 'truncated': False, 'cell': 'Pred_O then Pred_E^1', 'even_fiber': 7, 'n': 15, 'contains_start': True, 'word': 'OE'}, {'m': 225, 'a': 1, 'b': 0, 'ok': True, 'predecessors': [37], 'count': 1, 'truncated': False, 'cell': 'Pred_O(m)', 'n': 37, 'contains_start': True, 'word': 'O'}, {'m': 1, 'a': 1, 'b': 4, 'ok': True, 'predecessors': [41, 57, 63, 65, 71, 119, 123, 139, 141, 147, 149, 159, 167, 177, 179, 257, 259, 261, 267, 279, 281, 283, 291, 301, 303, 305, 311, 315, 337, 345], 'count': 30, 'truncated': False, 'cell': 'Pred_O then Pred_E^4', 'even_fiber': 1063, 'n': 63, 'contains_start': True, 'word': 'OEEEE'}]`

Label: `REPACKAGING`. Not `MACRO_INVERSE_GREEN`.

## H. Repeated macro behavior

An A-orbit is the odd subsequence of the J-orbit. Consecutive
`(1,0)` steps are an ordinary odd run. A terminal `(1,b)` is the
existing ResidualStep even tail. Selected trajectories:

`[{'n': 3, 'end': 1, 'macro_word': [(1, 0), (1, 0), (1, 3)], 'word': 'OOOEEE', 'macro_count': 3, 'oe_len': 6, 'status': 'CAPTURE'}, {'n': 9, 'end': 1, 'macro_word': [(1, 0), (1, 1), (1, 3)], 'word': 'OOEOEEE', 'macro_count': 3, 'oe_len': 7, 'status': 'CAPTURE'}, {'n': 15, 'end': 7, 'macro_word': [(1, 1)], 'word': 'OE', 'macro_count': 1, 'oe_len': 2, 'status': 'RETURNED'}, {'n': 37, 'end': 1, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 2), (1, 0), (1, 5)], 'word': 'OOOOEOOOEEOOEEEEE', 'macro_count': 9, 'oe_len': 17, 'status': 'CAPTURE'}, {'n': 49, 'end': 5, 'macro_word': [(1, 0), (1, 1), (1, 2)], 'word': 'OOEOEE', 'macro_count': 3, 'oe_len': 6, 'status': 'RETURNED'}, {'n': 63, 'end': 1, 'macro_word': [(1, 4)], 'word': 'OEEEE', 'macro_count': 1, 'oe_len': 5, 'status': 'CAPTURE'}, {'n': 69, 'end': 3, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 3)], 'word': 'OOEOOEEE', 'macro_count': 4, 'oe_len': 8, 'status': 'RETURNED'}, {'n': 77, 'end': 21, 'macro_word': [(1, 0), (1, 0), (1, 1), (1, 1), (1, 0), (1, 2)], 'word': 'OOOEOEOOEE', 'macro_count': 6, 'oe_len': 10, 'status': 'RETURNED'}, {'n': 173, 'end': 27, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 2), (1, 2), (1, 3)], 'word': 'OOEOOOOOOOOEOOEOOEEOEEOEEE', 'macro_count': 16, 'oe_len': 26, 'status': 'RETURNED'}, {'n': 193, 'end': {'bits': 78, 'hex_head': '0x3c931c6607bb955b'}, 'macro_word': [(1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 2), (1, 2), (1, 0), (1, 0)], 'word': 'OOOEOOOOOOOEOOOEEOEEOO', 'macro_count': 16, 'oe_len': 22, 'status': 'CAPPED'}, {'n': 365, 'end': 5, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'word': 'OOEOOEOOEOOEOEEE', 'macro_count': 9, 'oe_len': 16, 'status': 'RETURNED'}, {'n': 425, 'end': 30736682958089, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 2), (1, 0), (1, 0), (1, 1), (1, 2), (1, 0), (1, 1), (1, 0)], 'word': 'OOOOOOOEOOEEOOOEOEEOOEO', 'macro_count': 16, 'oe_len': 23, 'status': 'CAPPED'}, {'n': 763, 'end': 5, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'word': 'OOEOOEOOEOEEE', 'macro_count': 7, 'oe_len': 13, 'status': 'RETURNED'}, {'n': 1749, 'end': 5, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'word': 'OOEOOEOEEE', 'macro_count': 5, 'oe_len': 10, 'status': 'RETURNED'}, {'n': 2183, 'end': {'bits': 911, 'hex_head': '0x68c2dc8e841c296e'}, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0)], 'word': 'OOEOOOOEOOOOOOOOEOO', 'macro_count': 16, 'oe_len': 19, 'status': 'CAPPED'}, {'n': 3889, 'end': {'bits': 123, 'hex_head': '0x53da71bf52ee30ac'}, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 1), (1, 0), (1, 0), (1, 1), (1, 0), (1, 1), (1, 1), (1, 1), (1, 0), (1, 0), (1, 0)], 'word': 'OOOOOEOEOOOEOOEOEOEOOO', 'macro_count': 16, 'oe_len': 22, 'status': 'CAPPED'}, {'n': 4447, 'end': 5, 'macro_word': [(1, 0), (1, 1), (1, 3)], 'word': 'OOEOEEE', 'macro_count': 3, 'oe_len': 7, 'status': 'RETURNED'}]`

- consecutive pair counts: `{'(1, 0)->(1, 0)': 112, '(1, 0)->(1, 1)': 81, '(1, 1)->(1, 0)': 52, '(1, 0)->(1, 2)': 27, '(1, 1)->(1, 1)': 18, '(1, 0)->(1, 3)': 10, '(1, 1)->(1, 3)': 10, '(1, 2)->(1, 0)': 9, '(1, 1)->(1, 2)': 8, '(1, 0)->(1, 5)': 7, '(1, 2)->(1, 2)': 5, '(1, 1)->(1, 4)': 4}`
- new consecutive law: `False`

Consecutive (1,0) then (1,b) is the existing ResidualStep O^a E^b

Hard / PE / first-return records remain ResidualStep blocks written
as several `(1,0)` plus one even tail:

`[{'n': 9, 'macro_word': [(1, 0), (1, 1), (1, 3)], 'oe': 'OOEOEEE', 'macro_count': 3, 'status': 'CAPTURE'}, {'n': 37, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 2), (1, 0), (1, 5)], 'oe': 'OOOOEOOOEEOOEEEEE', 'macro_count': 9, 'status': 'CAPTURE'}, {'n': 49, 'macro_word': [(1, 0), (1, 1), (1, 2)], 'oe': 'OOEOEE', 'macro_count': 3, 'status': 'RETURNED'}, {'n': 69, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 3)], 'oe': 'OOEOOEEE', 'macro_count': 4, 'status': 'RETURNED'}, {'n': 77, 'macro_word': [(1, 0), (1, 0), (1, 1), (1, 1), (1, 0), (1, 2)], 'oe': 'OOOEOEOOEE', 'macro_count': 6, 'status': 'RETURNED'}, {'n': 193, 'macro_word': [(1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 2), (1, 2), (1, 0), (1, 0)], 'oe': 'OOOEOOOOOOOEOOOEEOEEOO', 'macro_count': 16, 'status': 'CAPPED'}, {'n': 365, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'oe': 'OOEOOEOOEOOEOEEE', 'macro_count': 9, 'status': 'RETURNED'}, {'n': 425, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 2), (1, 0), (1, 0), (1, 1), (1, 2), (1, 0), (1, 1), (1, 0)], 'oe': 'OOOOOOOEOOEEOOOEOEEOOEO', 'macro_count': 16, 'status': 'CAPPED'}, {'n': 763, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'oe': 'OOEOOEOOEOEEE', 'macro_count': 7, 'status': 'RETURNED'}, {'n': 1749, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 1), (1, 3)], 'oe': 'OOEOOEOEEE', 'macro_count': 5, 'status': 'RETURNED'}, {'n': 2183, 'macro_word': [(1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (1, 0)], 'oe': 'OOEOOOOEOOOOOOOOEOO', 'macro_count': 16, 'status': 'CAPPED'}, {'n': 3889, 'macro_word': [(1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 1), (1, 0), (1, 0), (1, 1), (1, 0), (1, 1), (1, 1), (1, 1), (1, 0), (1, 0), (1, 0)], 'oe': 'OOOOOEOEOOOEOOEOEOEOOO', 'macro_count': 16, 'status': 'CAPPED'}, {'n': 4447, 'macro_word': [(1, 0), (1, 1), (1, 3)], 'oe': 'OOEOEEE', 'macro_count': 3, 'status': 'RETURNED'}]`

Hard starts still carry the long odd run as a sequence of (1,0) steps. ResidualStep already named that block.

Label: `REPACKAGING`. Not `MACRO_STRUCTURE_GREEN` or `MACRO_HARDNESS_GREEN`.

## I. New versus repackaged mathematics

- A is first-return-to-odd with a identically 1 — `COMPUTATIONALLY VERIFIED` novelty `PROJECT-SPECIFIC` repackaging `False`
- J(n) odd implies A(n)=J(n); J(n) even implies A=ResidualStep with a=1 — `COMPUTATIONALLY VERIFIED` novelty `REPARAMETERIZATION` repackaging `True`
- Delta_{a,b} equals global_defect on the realizing word — `REPARAMETERIZATION` novelty `REPARAMETERIZATION` repackaging `True`
- A is monotone on each fixed (a,b) — `REPARAMETERIZATION` novelty `REPARAMETERIZATION` repackaging `True`
- A(n)<n iff J(n) is even — `EXACT — HUMAN PROOF` novelty `REPARAMETERIZATION` repackaging `True`
- beta(a,b) is the finite-itinerary exponent — `REPARAMETERIZATION` novelty `REPARAMETERIZATION` repackaging `True`
- A_{1,b}^{-1} is nested floor cells — `REPARAMETERIZATION` novelty `REPARAMETERIZATION` repackaging `True`
- first J-return below n can occur on an even state before A(n) — `EXACT — HUMAN PROOF` novelty `PROJECT-SPECIFIC` repackaging `False`
- macro itinerary (1,0),(1,b) is a shorter encoding of the same O/E word — `OBSERVATION` novelty `REPARAMETERIZATION` repackaging `True`
- consecutive macro branches are ResidualStep blocks — `REPARAMETERIZATION` novelty `REPARAMETERIZATION` repackaging `True`

The only statement that is not an immediate rewrite of an itinerary /
floor-power theorem is the first-return distinction: a J-return
below n may land on an even intermediate before A(n).
That is a warning against replacing J by A, not a simpler law.

## J. Counterexamples

- smallest even-intermediate J-return before A(n): `7`
- return-before-odd count: `508` examples `[7, 11, 13, 17, 23, 29, 41, 57]`
- return at the odd landing: `482`
- no return inside the first macro step: `1009`
- “A is ResidualStep”: false when J(n) is odd (e.g. `n=3`, `A=5`, ResidualStep lands at `1` after `OOOEEE`).
- “A is a new transition law”: false when J(n) is odd, `A=J`.
- “macro contraction is stronger than the envelope”: false; it is the envelope on `O` / `OE^b`.
- “fixed `(a,b)` inverse is cleaner than cells”: false; it is the cells.
- “every A-orbit return equals the first J-return”: false whenever the J-return state is even.

## K. Decision

**CLOSE** — `ACCELERATION_COMPLEX`

A is the odd subsequence of J: A(n)=J(n) when J(n) is odd, and A(n) is the a=1 ResidualStep landing when J(n) is even. Defect, monotonicity, contraction, beta, and inverse reduce to global_defect_identity, image_monotone_of_follows, power_bound_contracts / floorPower_odd_ge, the itinerary exponent, and the floor cells. Acceleration removes only even tails.

This is not a halt result and not a proof that every odd start
has a next odd landing outside the scanned window. A does not
replace J.

## Lean

- sorry-free: `True`
- `floorPower_odd_ge`: `True`
- `power_bound_contracts`: `True`
- `image_monotone_of_follows`: `True`
- `global_defect_identity`: `True`
- `residualStep_global_defect`: `True`
- `odd_preimage_unique`: `True`
- `image_eq_iterate`: `True`
- no forbidden engines: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- tau_always_finite: `False`
- A_replaces_J: `False`
- new_lyapunov_scalar: `False`
- reopen_pe_factors: `False`
- reopen_residual_quotient: `False`
- reopen_sum_rho: `False`
- reopen_realization_geometry: `False`
- reopen_landing_image: `False`
- reopen_nc_boundary: `False`
- reopen_first_return: `False`
- reopen_information_complexity: `False`
- reopen_prefix_nc: `False`
- reopen_preimage_cylinders: `False`
- reopen_adversarial_paths: `False`
- reopen_backward_geometry: `False`
- second_acceleration: `False`
- cuda_census: `False`
- automaton: `False`

## Artifacts

`{'dir': 'data/research/juggler/accelerated', 'manifest': 'manifest.json', 'parquet': 'data/research/juggler/accelerated/macro_trajectories.parquet', 'edge_rows': 1999, 'trajectory_rows': 340}`

