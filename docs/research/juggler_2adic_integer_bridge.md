# Juggler 2-adic / positive-integer bridge

Status: **BRIDGE_COMPLEX**

Standalone arithmetic phase. Not a Research Engine experiment, not an
automaton, and not a termination theorem. Closed PE-factor, residual
future-quotient, summed-rho, realization-set, landing-image, NC-boundary,
first-return, adversarial, information-complexity, backward-geometry,
and accelerated-odd-to-odd branches stay closed.

## 1. Definitions

Keep the four notions separate.

**A. 2-adic / modular admissibility.** For a finite O/E word \(w\) and
precision \(P\ge 1\), a residue \(r\bmod 2^P\) has one of the three
states already used by the laboratory residue tests:

- `FORBIDDEN`: the first letter of \(w\) disagrees with the
  parity of \(r\). This is the only exact 2-adic prohibition.
- `ADMISSIBLE`: every 2-adic constraint at precision \(P\) is
  resolved and accepts \(w\). In this phase that happens only for
  \(|w|\le 1\), where the letter is \(n\bmod 2\).
- `INCONCLUSIVE`: the first letter matches, but some later
  letter is not a locally constant function of \(n\bmod 2^P\).

`Admissible_P(w)` is the *weak* predicate: some cylinder is not
`FORBIDDEN`. `Forced_P(w)` is the *strong* predicate: some
cylinder is `ADMISSIBLE` for the whole word.

The existing odd-odd law \(\rho\equiv y-1\pmod 8\)
(`odd_odd_remainder_mod_eight`) is a constraint on a *realized* odd-to-odd
landing, not a filter that forbids the itinerary `OO`.

**B. Integer realizability.**

\[
\operatorname{IntReal}(w)\iff\exists n\in\mathbb Z_{>0},\ \operatorname{follows}(n,w).
\]

**C. Juggler realizability.** The same `follows`, using the exact map
\(J(n)=\lfloor\sqrt n\rfloor\) (\(n\) even) or
\(J(n)=\lfloor n^{3/2}\rfloor\) (\(n\) odd).

**D. Positive-integer semantic compatibility.** Simultaneous exact
integrality, positivity, parity, floor-cell membership, and the Juggler
transition. This is `follows`, not a 2-adic predicate.

**Finite-precision lifting.** Given a cylinder \(n\equiv r\pmod{2^P}\),
ask whether some positive representative follows \(w\). Exhaustive search
of that cylinder inside \([1,N]\) is exact for the window; absence there
is `NO_WITNESS_IN_BOUND`, never a Type-3 certificate.

Quantifiers stay separate:

- finite-precision existence: \(\forall P\,\exists n\in\mathbb Z_{>0},\ C_P(n)\);
- one integer for all listed \(P\): \(\exists n\,\forall P,\ C_P(n)\);
- one 2-adic integer: \(\exists x\in\mathbb Z_2\,\forall P,\ C_P(x)\).

## 2. Existing certified machinery

| Object | API | Semantics |
| --- | --- | --- |
| exact step | `floor_power` | \(J\) |
| itinerary word | `follows_itinerary` / Lean `follows` | IntReal witness check |
| even tower | `even_tower` / Lean `even_tower_to_one` | \(m(E^r)=2^{2^{r-1}}\) |
| odd-odd remainder | `landing_row` / `odd_odd_remainder_mod_eight` | \(\rho\equiv y-1\pmod 8\) on realized OO |
| 2-adic valuation | `landing_valuation.v2` | \(v_2\) of an integer, not an itinerary automaton |
| BT coordinates | `encode`, `lsd`, `D`, `integer_jet` | \(n=\mathrm{lsd}(n)+3D(n)\), \(J_k(n)\) |
| first rooted holes | realization-geometry certificates | `SCALE_LIMITED`, not `CELL_EMPTY` |
| documented \(2^{16}\) pair | `DOCUMENTED_MOD16_PAIR` | same residue, words `OO` vs `OE` |

There is no pre-existing Juggler `Admissible_P` with the Collatz Layer-C
automaton semantics. Collatz valuation cylinders are a different map and
are not imported. The object used here is the residue-class status of
the exact first-letter law plus the exact second-letter split.

## 3. Finite-precision comparison

Phase 0: \(k\le 12\), \(P\le 16\),
\(n\le 4000\). Weak `Admissible_P` contains every itinerary of
length \(k\) for every tested \(P\ge 1\), because every itinerary has a
first-letter-compatible residue and no later letter is 2-adically
forced.

| k | A_P (weak) | I(k) in n<=4000 | A ∩ I | A \\ I | I \\ A | Forced_P |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 2 | 2 | 2 | 0 | 0 | 2 |
| 2 | 4 | 4 | 4 | 0 | 0 | 0 |
| 3 | 8 | 8 | 8 | 0 | 0 | 0 |
| 4 | 16 | 16 | 16 | 0 | 0 | 0 |
| 5 | 32 | 29 | 29 | 3 | 0 | 0 |
| 6 | 64 | 49 | 49 | 15 | 0 | 0 |
| 7 | 128 | 78 | 78 | 50 | 0 | 0 |
| 8 | 256 | 121 | 121 | 135 | 0 | 0 |
| 9 | 512 | 194 | 194 | 318 | 0 | 0 |
| 10 | 1024 | 320 | 320 | 704 | 0 | 0 |
| 11 | 2048 | 447 | 447 | 1601 | 0 | 0 |
| 12 | 4096 | 568 | 568 | 3528 | 0 | 0 |

`I \\ A` is empty: every observed realizer satisfies the first-letter
law. That direction is expected and is not the bridge.

`A \\ I` at \(k=5\): `EEEEE`, `EEEOE`, `EEOEO`.

`A \\ I` at \(k=6\): `EEEEEE`, `EEEEEO`, `EEEEOE`, `EEEOEE`, `EEEOEO`, `EEEOOE`, `EEOEEO`, `EEOEOE`, `EEOEOO`, `EEOOEO`, `EOEEOE`, `EOEOOO`, `EOOEOO`, `EOOOEO`, `OEEEOE`.

Do not call an itinerary missing from \(I(k)\) unrealizable. The three first
atlas holes remain `SCALE_LIMITED`. Length \(\le 4\) fills completely
inside \(n\le 4000\).

Second-letter splits, every residue, \(P=1..16\):

| P | even classes | even unsplit | odd classes | odd unsplit | odd worst t |
| --- | --- | --- | --- | --- | --- |
| 1 | 1 | 0 | 1 | 0 | 3 |
| 2 | 2 | 0 | 2 | 0 | 3 |
| 3 | 4 | 0 | 4 | 0 | 4 |
| 4 | 8 | 0 | 8 | 0 | 5 |
| 5 | 16 | 0 | 16 | 0 | 8 |
| 6 | 32 | 0 | 32 | 0 | 6 |
| 7 | 64 | 0 | 64 | 0 | 7 |
| 8 | 128 | 0 | 128 | 0 | 11 |
| 9 | 256 | 0 | 256 | 0 | 12 |
| 10 | 512 | 0 | 512 | 0 | 12 |
| 11 | 1024 | 0 | 1024 | 0 | 12 |
| 12 | 2048 | 0 | 2048 | 0 | 12 |
| 13 | 4096 | 0 | 4096 | 0 | 12 |
| 14 | 8192 | 0 | 8192 | 0 | 14 |
| 15 | 16384 | 0 | 16384 | 0 | 14 |
| 16 | 32768 | 0 | 32768 | 0 | 16 |

All even classes split by the exact square-cell construction: the
intervals of \(q=2^P\) and \(q=2^P+1\) each have length \(>2^P\), so each
meets the arithmetic progression, and those two \(q\) have opposite
parity. All odd classes split by a search with \(t\le 64\);
the worst case is \(P=16\), \(r=38921\),
\(t=16\). No unsplit cylinder occurred.

Label: even split **EXACT — HUMAN PROOF**; odd split on \(P\le 16\)
**COMPUTATIONALLY VERIFIED**.

## 4. Cylinder lifting

The search in a cylinder is the complete set of positive representatives
in \([1,N]\), hence at most \(\lceil N/2^P\rceil\) evaluations. That is
the justified bound.

| word | P | cylinders with a rep <=4000 | with witness | empty in bound | smallest witness |
| --- | --- | --- | --- | --- | --- |
| E | 1 | 1 | 1 | 0 | 2 |
| E | 4 | 8 | 8 | 0 | 2 |
| E | 8 | 128 | 128 | 0 | 2 |
| E | 16 | 2000 | 2000 | 0 | 2 |
| OOE | 1 | 1 | 1 | 0 | 5 |
| OOE | 4 | 8 | 8 | 0 | 5 |
| OOE | 8 | 128 | 126 | 2 | 5 |
| OOE | 16 | 2000 | 500 | 1500 | 5 |
| EEEEE | 1 | 1 | 0 | 1 | None |
| EEEEE | 4 | 8 | 0 | 8 | None |
| EEEEE | 8 | 128 | 0 | 128 | None |
| EEEEE | 16 | 2000 | 0 | 2000 | None |
| EEEEEE | 1 | 1 | 0 | 1 | None |
| EEEEEE | 4 | 8 | 0 | 8 | None |
| EEEEEE | 8 | 128 | 0 | 128 | None |
| EEEEEE | 16 | 2000 | 0 | 2000 | None |
| EEEEOE | 1 | 1 | 0 | 1 | None |
| EEEEOE | 4 | 8 | 0 | 8 | None |
| EEEEOE | 8 | 128 | 0 | 128 | None |
| EEEEOE | 16 | 2000 | 0 | 2000 | None |
| EEEOEO | 1 | 1 | 0 | 1 | None |
| EEEOEO | 4 | 8 | 0 | 8 | None |
| EEEOEO | 8 | 128 | 0 | 128 | None |
| EEEOEO | 16 | 2000 | 0 | 2000 | None |

For `EEEEEE`, the even tower \(m=2^{32}\) lies in the cylinder
\(0\bmod 2^P\) for every \(P\le 32\), but not in \([1,4000]\). Empty
Phase-0 lifting rows are Type 1, not Type 3.

## 5. Precision versus minimal realizer

`P_adm(w)` is the least \(P\) at which some cylinder is strongly
`ADMISSIBLE` for the whole word. For \(|w|\ge 2\) that \(P\)
does not exist in the Phase-0 range.

| word | P_adm | m(w) | log2 m | BT depth | kind |
| --- | --- | --- | --- | --- | --- |
| E | 1 | 2 | 1 | 2 | TYPE_A_LENGTH_ONE |
| O | 1 | 1 | 0 | 1 | TYPE_A_LENGTH_ONE |
| EE | None | 4 | 2 | 2 | TYPE_B_P_ADM_UNDEFINED |
| OO | None | 1 | 0 | 1 | TYPE_B_P_ADM_UNDEFINED |
| OOE | None | 5 | 2 | 3 | TYPE_B_P_ADM_UNDEFINED |
| OEO | None | 15 | 3 | 4 | TYPE_B_P_ADM_UNDEFINED |
| EEOE | None | 2500 | 11 | 8 | TYPE_B_P_ADM_UNDEFINED |
| OOOO | None | 1 | 0 | 1 | TYPE_B_P_ADM_UNDEFINED |
| OOOEE | None | 3 | 1 | 2 | TYPE_B_P_ADM_UNDEFINED |
| EEEEE | None | 65536 | 16 | 11 | TYPE_C_SCALE_DELAYED |
| EEEEEE | None | 4294967296 | 32 | 21 | TYPE_C_SCALE_DELAYED |
| EEEEOE | None | 39062504258660 | 45 | 30 | TYPE_C_SCALE_DELAYED |
| EEEOEO | None | 2608762880 | 31 | 21 | TYPE_C_SCALE_DELAYED |

Length-one words are Type A: `P_adm=1` matches the parity of \(m(w)\).
Longer realized itineraries are Type B: a finite realizer exists while no
finite precision forces the itinerary. The first holes are Type C only as
*scale delay*, not as 2-adically forced empty cylinders.

## 6. Balanced-ternary bridge

Canonical expansion \(n=\sum a_i 3^i\), \(a_i\in\{-1,0,+1\}\).
The identity \(n=\mathrm{lsd}(n)+3D(n)\) holds on the scanned window
(`True`). The sum of *all* trits
recovers parity, because \(3^i\equiv 1\pmod 2\):

\[
n\equiv\sum_i a_i\pmod 2.
\]

A finite jet \(J_k(n)=(a_0,\ldots,a_{k-1})\) determines only
\(n\bmod 3^k\). The leftover \(3^k D^k(n)\) is odd-modulus and can flip
parity. Smallest counterexample: \(J_1(1)=J_1(4)=(1)\) with opposite
first Juggler letters.

Same finite BT prefix versus first-letter (hence versus `Admissible_P`)
on \(n\le 4000\):

| jet depth | jets seen | mixed parity | pure parity |
| --- | --- | --- | --- |
| 1 | 3 | 3 | 0 |
| 2 | 9 | 9 | 0 |
| 3 | 27 | 27 | 0 |
| 4 | 81 | 81 | 0 |
| 5 | 243 | 243 | 0 |
| 6 | 729 | 729 | 0 |

Every positive depth has mixed-parity jets. Conversely, every tested
2-adic residue class that meets \([1,4000]\) realises more than one
`lsd` except the trivial one-representative classes at large \(P\).

Chinese remainder: \(\gcd(2^P,3^k)=1\), so

\[
(n\equiv r\pmod{2^P})\ \cap\ (J_k(n)=a)
\]

is a single class modulo \(2^P 3^k\), hence an infinite arithmetic
family, never empty and never a singleton in \(\mathbb Z\). The two
positional systems are transverse. A finite BT jet does not constrain
the 2-adic admissibility class. A finite 2-adic residue does not
constrain a finite BT jet.

The documented pair \(n\equiv 33\pmod{2^{16}}\) has words
`OO` and `OE` and BT 4-jets
`[0, -1, 1, 1]` versus `[-1, 1, 1, 0]`.

## 7. Quantifier separation

For the *first-letter* constraint \(C_P(n):\Leftrightarrow n\equiv w_0\pmod 2\):

- \(\forall P\,\exists n\in\mathbb Z_{>0},\ C_P(n)\) holds (\(n=2\) or \(n=1\));
- the same \(n\) works for every \(P\);
- the 2-adic integers satisfying every \(C_P\) are the even or odd
  2-adics, a different space from \(\mathbb Z_{>0}\).

For the *strong* constraint “the cylinder forces \(w\)”:

- no \(P\le 16\) has a cylinder forcing an itinerary of length \(\ge 2\);
- compactness of \(\mathbb Z_2\) therefore does not produce a
  2-adic Juggler itinerary. \(J\) is an Archimedean floor map, not a
  2-adic dynamical system.

For `EEEEEE`, \(2^{32}\) realises the itinerary and lies in
\(0\bmod 2^P\) for all \(P\le 32\). That is one integer meeting every
*listed* even cylinder up to \(P=32\). It is not a point of
\(\bigcap_P 2^P\mathbb Z_2=\{0\}\).

## 8. Hard cases

| word | m in n<=4000 | known witness | follows | status P=8 | failure type |
| --- | --- | --- | --- | --- | --- |
| EEEEEE | None | 4294967296 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEEEOE | None | 39062504258660 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEEOEO | None | 2608762880 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEEEE | None | 65536 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEEOE | None | 2608762880 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEOEO | None | 51076 | True | INCONCLUSIVE | TYPE_1_SCALE |
| EEOE | 2500 | 2500 | True | INCONCLUSIVE | TYPE_1_IN_WINDOW |
| OOE | 5 | 5 | True | INCONCLUSIVE | TYPE_1_IN_WINDOW |

`EEEEEE`, `EEEEOE`, and `EEEOEO` remain `SCALE_LIMITED`. 2-adic
admissibility does not confuse a scale-bound witness with a genuine
integer incompatibility: those itineraries are weakly admissible at every
tested \(P\) and strongly unresolved at every tested \(P\).

Landing valuation on OO starts \(n\le 64\):
`15` realized, mod-8 law
`True`, and the law does
not forbid `OO`.

## 9. Candidate mathematical statements

- Every 2-adic cylinder of precision \(P\ge 1\) determines the first
  Juggler letter and no later letter, for all even residues by the
  square-cell construction and for all odd residues with \(P\le 16\)
  by the recorded splits.  
  Tags: **EXACT — HUMAN PROOF** (even); **COMPUTATIONALLY VERIFIED** (odd, \(P\le 16\)).
- Weak `Admissible_P` is the first-letter language \(\{O,E\}^*\).  
  Tag: **EXACT — HUMAN PROOF**, given the split law.
- `follows(n,w)` implies weak `Admissible_P(w)`.  
  Tag: **EXACT — HUMAN PROOF**. This is the expected direction, not the bridge.
- Finite BT jet \(\Rightarrow\) same `Admissible_P` status.  
  Tag: **REFUTED** at \(n=1,4\).
- Finite 2-adic residue \(\Rightarrow\) a fixed BT \(k\)-jet.  
  Tag: **REFUTED** (mixed `lsd` in every small even class).
- CRT intersection of a 2-adic cylinder with a BT \(k\)-cylinder is a
  nonempty arithmetic progression modulo \(2^P 3^k\).  
  Tag: **EXACT — HUMAN PROOF**.
- `ADMISSIBILITY_REALIZATION_GREEN` / `LIFTING_BOUND_GREEN` /
  `BT_2ADIC_BRIDGE_GREEN` / `INTEGER_OBSTRUCTION_GREEN` /
  `PRECISION_REALIZATION_GREEN`.  
  Tag: **REFUTED** as Phase-0 promotion targets. The surviving
  relation is first-letter plus witness scale.
- Type-3 integer obstruction beyond resolved 2-adic conditions.  
  Tag: **OBSERVATION** (none found; not a proof that none exist).

No statement is **LEAN-CERTIFIED** beyond the already-packaged `follows`,
`even_tower_to_one`, and landing-valuation lemmas. No new Lean file.

## 10. Decision

**BRIDGE_COMPLEX**. Branch decision: **CLOSE**.

Every tested 2-adic cylinder splits at the second Juggler letter. Weak Admissible_P is first-letter survival and therefore contains every finite itinerary. Every Phase-0 gap is Type 1 or INTEGER-WITNESS-ABSENT-WITHIN-BOUND. Finite BT jets are CRT-transverse to 2-adic residues and do not determine the first letter. No Type-3 integer obstruction and no lifting bound survived.

Do not call weak admissibility equivalent to IntReal. The layers differ
by witness scale, not by an extra finite 2-adic prohibition. Do not
build an automaton because each fixed \(P\) has finitely many residues.
Do not reopen residual quotients or information-complexity.

Best next question: none from this branch.
