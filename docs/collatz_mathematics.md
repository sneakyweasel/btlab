# Collatz module — consolidated mathematics

This document records **exactly** what the Collatz research module implements
and how each claim is classified. It does **not** claim progress on solving
the Collatz conjecture.

Claim labels are the seven ledger tags from [README.md](README.md):

| Label | Meaning |
| --- | --- |
| **EXACT — HUMAN PROOF** | A complete mathematical argument is given here (or is the standard theorem cited). |
| **EXACT — LEAN VERIFIED** | The same English claim has a compiled Lean proof. |
| **COMPUTATIONALLY VERIFIED** | An identity was checked on a finite set. This is not a proof. |
| **CONJECTURE** | An explicit unproved statement, required to carry a counterexample search. |
| **OBSERVATION** | Empirical, with no claim of necessity. |
| **REFUTED** | A counterexample is recorded. |
| **REPARAMETERIZATION** | A classical construction under a local name. |

Finite verification is never presented as a proof.

The primary map is the **accelerated odd-only** map, not the standard
Hailstone map.

---

## 1. Two Collatz maps

### Standard map `C` (implemented as `standard_collatz_step`)

For a positive integer \(n\):

\[
C(n)=\begin{cases}
n/2 & \text{if }n\text{ is even},\\
3n+1 & \text{if }n\text{ is odd}.
\end{cases}
\]

### Accelerated map `T` (primary; `collatz_step`)

For a positive odd integer \(n\):

\[
T(n)=\frac{3n+1}{2^{v_2(3n+1)}}.
\]

**EXACT — HUMAN PROOF.** If \(n\) is odd then \(3n\) is odd, so \(3n+1\) is even, hence
\(v_2(3n+1)\ge 1\). Dividing out all factors of \(2\) leaves an odd integer,
so \(T(n)\) is a positive odd integer.

All implementations use Python arbitrary-precision integers. The division is
an exact right shift by \(v_2(3n+1)\).

---

## 2. The \(2\)-adic valuation

`v2(n)` is the largest \(k\) such that \(2^k\) divides \(n\). For \(n=0\)
the value is \(+\infty\), returned as `None` (same convention as `v3`).

**EXACT — HUMAN PROOF.** \(v_2\) is the standard \(2\)-adic valuation on \(\mathbb{Z}\).

---

## 3. Balanced ternary and \(3n+1\)

Canonical balanced ternary is the existing unique expansion

\[
n=\sum_i a_i 3^i,\qquad a_i\in\{-1,0,+1\},
\]

displayed most-significant digit first with `-` / `0` / `+`.

### Multiplication by 3 is a shift

**EXACT — HUMAN PROOF.** \(3n=\sum_i a_i 3^{i+1}\), so the coefficients of \(3n\) are
those of \(n\) with a new least-significant digit \(0\). In display form
this appends a trailing `0` (except \(n=0\)).

Implemented as `multiply_by_three` and checked against `encode(3n)`.

### Adding \(+1\) is not a binary carry

Digits live in \(\{-1,0,+1\}\). A local sum \(s\in\{-3,\ldots,3\}\) is
rewritten as \(s = d + 3c\) with \(d\in\{-1,0,+1\}\):

- \(s\ge 2\) \(\Rightarrow\) \(d=s-3\), carry \(+1\) (uses \(2=3-1\));
- \(s\le -2\) \(\Rightarrow\) \(d=s+3\), carry \(-1\) (uses \(-2=-3+1\));
- otherwise \(d=s\), carry \(0\).

**EXACT — HUMAN PROOF** as an identity of integers: the rewrite preserves value. The
implementation `add` is therefore exact balanced ternary addition.

### Local LSD cases of \(+1\)

Let \(a_0\) be the least-significant digit.

| Trailing digit | Local rewrite | Carry |
| --- | --- | --- |
| `0` | becomes `+` | none |
| `+` | becomes `-` | \(+1\) (may propagate) |
| `-` | becomes `0` | none |

**EXACT — HUMAN PROOF** by the rewrite rule on a single digit. Propagation when the
trailing run is `+` is handled by the full adder, not by the local table.

### Decomposition used in this module

\[
n \;\longrightarrow\; 3n \text{ (shift)} \;\longrightarrow\; 3n+1 \text{ (append +)}
\;\longrightarrow\; T(n)=\frac{3n+1}{2^{v_2(3n+1)}}.
\]

The first two operations are native to balanced ternary. The third is
the odd-part map (Layer B). `three_n_plus_one_word` (shift-then-add-one)
is an independent check of the append-plus theorem (Layer A).

---

## 4. Parity / weight bridge

The existing theorem (see `docs/mathematics.md`) is:

**EXACT — HUMAN PROOF.** \(n \equiv w(n)\pmod{2}\), because \(3^i\equiv 1\pmod{2}\) and
\(-1\equiv 1\pmod{2}\). So \(n\) is odd if and only if the balanced ternary
weight is odd.

Corollaries used here, both **EXACT — HUMAN PROOF**:

1. Every positive odd Collatz state \(n\) has odd weight.
2. \(3n+1\) is even, so `weight(BT(3n+1))` is even.
3. \(T(n)\) is odd, so `weight(BT(T(n)))` is odd.

These are re-checked exhaustively on configurable odd ranges
(`btlab collatz test-invariants`). Range success is
**COMPUTATIONALLY VERIFIED**; the identity itself is **EXACT — HUMAN PROOF**.

This is the first exact bridge between balanced ternary combinatorics and
Collatz parity. It does not constrain orbits beyond parity.

---

## 5. Images of \(T\) and inverse exponents

**EXACT — HUMAN PROOF.** \(T(n)\not\equiv 0\pmod{3}\) for every positive odd \(n\),
because \(3n+1\equiv 1\pmod{3}\) and \(2^k\) is invertible modulo \(3\).

If \(m=T(n)\) then \(n=(2^k m-1)/3\) with \(k=v_2(3n+1)\ge 1\). Integrality
is \(2^k m\equiv 1\pmod{3}\). Since \(2\equiv -1\pmod{3}\),

\[
(-1)^k m \equiv 1\pmod{3}.
\]

**EXACT — HUMAN PROOF** characterization of admissible \(k\):

- \(m\equiv 0\pmod{3}\): no \(k\) (and such \(m\) are not in the image of \(T\));
- \(m\equiv 1\pmod{3}\): \(k\) even;
- \(m\equiv 2\pmod{3}\): \(k\) odd.

`collatz_predecessors(m, k_max)` enumerates those \(k\le k_{\max}\) and
returns \(n\). Every generated pair is required to satisfy \(T(n)=m\) and
\(v_2(3n+1)=k\).

**EXACT — HUMAN PROOF.** The only positive odd fixed point of \(T\) is \(T(1)=1\), given
by \(k=2\): \((4\cdot 1-1)/3=1\). Inverse trees record this as a cycle and
do not expand it (a computational bound against uncontrolled unrolling).

**EXACT — HUMAN PROOF.** Odd multiples of 3 can appear as Collatz *states* (for example
\(21=(2^6-1)/3\) satisfies \(T(21)=1\)) but never as *values* of \(T\).
Their predecessor lists are empty. This is not a contradiction: the inverse
of \(T\) can land on a multiple of 3, after which no further preimage
exists.

Least-significant balanced ternary digit `0` characterises divisibility by
\(3\) (**EXACT — HUMAN PROOF**, existing \(v_3\) theorem). The numerator \(2^k m-1\)
still requires arithmetic before that test; this module does not claim that
predecessors are visible from a fixed suffix of \(m\) alone.

---

## 6. Stopping times

On the accelerated map:

- **Stopping time** of \(n>1\): smallest \(k\ge 1\) with \(T^k(n)<n\).
  For \(n=1\) the value is \(0\) by convention.
- **Total stopping time**: smallest \(k\ge 0\) with \(T^k(n)=1\).

If `max_steps` is exhausted first, the functions return `None`. That is a
**computational bound**, not a statement that the orbit diverges.

No claim is made that every orbit reaches \(1\).

---

## 7. Two-adic digit automaton

`TwoAdicDigitAutomaton(K)` is `ModularAutomaton(2^K)`: states
\(\{0,\ldots,2^K-1\}\), alphabet \(\{-,0,+\}\),

\[
\delta(r,a)=(3r+a)\bmod 2^K.
\]

**EXACT — HUMAN PROOF** (existing modular recurrence / Horner's rule):

\[
\texttt{automaton.residue}(w)=\operatorname{decode}(w)\bmod 2^K.
\]

### Valuation classification from a residue

Given \(n\equiv r\pmod{2^K}\) let \(y=(3r+1)\bmod 2^K\).

- If \(y\neq 0\), then \(v_2(3n+1)=v_2(y)\) is **exact** and
  \(0\le v_2(y)<K\). For odd \(r\), this exact value satisfies \(k\ge 1\).
- If \(y=0\), then \(v_2(3n+1)\ge K\). Returned as `AT_LEAST_K`.

**EXACT — HUMAN PROOF** as a fact about congruences: \(3n+1\equiv y\pmod{2^K}\), so the
valuation is exact precisely when it is strictly less than \(K\). The cases
\(v_2=K\) and \(v_2>K\) are indistinguishable modulo \(2^K\). There is
**no exact-\(K\) class at precision \(K\)**.

This is the off-by-one / precision convention of the implementation.
Example: \(n=1\), \(3n+1=4\), \(v_2=2\). At \(K=2\), \(y\equiv 0\pmod{4}\),
so the classifier returns `AT_LEAST_K`, not \(2\). At \(K=3\), \(y=4\),
\(v_2(4)=2\) is exact.

### What this automaton is not

The automaton classifies the **valuation step** of \(T\) from \(n\bmod 2^K\).
It is **not** a finite-state model of the map \(n\mapsto T(n)\) on residues
modulo \(2^K\). See the next section.

A few small-\(K\) partitions are standard and **EXACT — HUMAN PROOF** from the odd
classes modulo \(4\) and \(8\):

- \(n\equiv 3\pmod{4}\) \(\Rightarrow\) \(v_2(3n+1)=1\);
- \(n\equiv 1\pmod{4}\) \(\Rightarrow\) \(v_2(3n+1)\ge 2\);
- \(n\equiv 1\pmod{8}\) \(\Rightarrow\) \(v_2(3n+1)=2\);
- \(n\equiv 5\pmod{8}\) \(\Rightarrow\) \(v_2(3n+1)\ge 3\).

These match `TwoAdicDigitAutomaton(2)` and `(3)`.

---

## 8. State precision: why Collatz is not a map modulo \(2^K\)

Suppose \(n\equiv r\pmod{2^K}\) and \(k=v_2(3n+1)\) is known and \(k<K\).
Then \(3n+1=2^k\cdot T(n)\) and

\[
2^k\cdot T(n)\equiv y\pmod{2^K},\qquad y=(3r+1)\bmod 2^K.
\]

Dividing a congruence by \(2^k\) is valid only after lowering the modulus:

\[
T(n)\equiv y/2^k \pmod{2^{K-k}}.
\]

\(T(n)\) is determined modulo \(2^{K-k}\), **not** modulo \(2^K\).
Implementing \((3r+1)/2^k \bmod 2^K\) would be an invalid modular division.

Possible exact constructions (Milestone 2 implements the precision-drop
form in Layer C):

- lift \(r\) to modulus \(2^{K+k}\) (or larger) before dividing;
- let the tracked precision drop from \(K\) to \(K-k\) after the step;
- keep a residue pair with enough extra \(2\)-adic digits.

If a finite-state exact Collatz transition requires more precision than
\(K\), that fact must be preserved. Milestone 1 stopped at valuation
classification. Layer C implements the precision-drop transition.

---

## 9. Feature transitions

For each odd \(n\) the record `CollatzFeatureTransition` stores

\[
n,\; 3n+1,\; v_2(3n+1),\; T(n)
\]

with canonical balanced ternary words and features of all three integers,
plus

\[
\Delta F = F(T(n))-F(n)
\]

for numeric features (length, weight, signed digit sum, run counts, …).

Column names are the schema in `collatz.transitions.ROW_COLUMNS`.

Deltas \(F(T(n))-F(n)\) are the composition of the **EXACT — HUMAN PROOF** Layer A map
\(n\to 3n+1\) and the odd-part step. They are not Lyapunov decreases.
Milestone 2 does not search for a Lyapunov function.

---

## 10. Experiment A

`run_exhaustive_experiment(limit)` scans every odd \(n\le\text{limit}\),
builds the feature-transition row, and re-checks the weight-parity bridge
and the shift-then-add-one / append-plus identities.

Metadata records experiment name, parameters, integer range, UTC timestamp,
and package version when available.

Status of that scan: **COMPUTATIONALLY VERIFIED** on the chosen range.
The weight-parity and append-plus identities remain **EXACT — HUMAN PROOF** independently
of the scan.

---

## 11. Layer A — Append-plus theorem

**EXACT — HUMAN PROOF** for every integer \(n\neq 0\):

\[
\mathrm{BT}(3n+1)=\mathrm{BT}(n)\,+.
\]

Display concatenation: a trailing `+` (new LSD \(a_0=+1\)).

Proof: \(3n\) is the digit shift of \(n\), so the LSD of \(3n\) is `0`.
Adding \(+1\) to LSD `0` yields `+` and **no carry**. The digits of \(n\)
are copied unchanged.

Exception: \(n=0\), because \(\mathrm{BT}(1)=+\) not `0+`. Implemented as
`append_plus` (rejects `0`) and `three_n_plus_one_from_word` (special-cases
zero).

The adder `add_one(multiply_by_three(w))` is an independent check, not the
definition.

### Closed-form features \(n\to 3n+1\) (EXACT — HUMAN PROOF)

Write \(y=3n+1\). Then \(a_0(y)=+1\) and \(a_{i+1}(y)=a_i(n)\).

- length\((y)=\) length\((n)+1\)
- weight\((y)=\) weight\((n)+1\) (parity flips)
- signed digit sum increases by \(1\)
- positive count \(+1\); negative and zero counts unchanged
- period-\(t\) position-class sums:
  \(S_0(y)=1+S_{t-1}(n)\) and \(S_j(y)=S_{j-1}(n)\) for \(j=1,\ldots,t-1\)

`predicted_features_after_append_plus` implements these identities.
Run/gap statistics are taken from the constructed word `BT(n)+`, which
equals `encode(3n+1)`.

---

## 12. Layer B — Odd-part transducer

Reading direction: **LSD-first**, dual to the MSD Horner automaton.

### Doubling is sequential (EXACT — HUMAN PROOF)

LSD doubling is a 3-state Mealy machine with carry in \(\{-1,0,+1\}\):
\(s=2a+c=d+3c'\). The rewrite alphabet is closed.

### Division by 2 is sequential on \(\mathbb{Z}_3\) (EXACT — HUMAN PROOF)

Because \(2\) is a unit in the 3-adics, doubling has a sequential inverse:
given input digit \(d\) and carry \(c\), there is a unique output \(a\) and
next carry \(c'\) with \(2a+c=d+3c'\). Solve \(a\equiv 2(d-c)\pmod{3}\)
lifted to \(\{-1,0,+1\}\).

On **even integers** the output is a finite canonical word and the final
carry is \(0\). On odd integers \(n/2\) has an infinite 3-adic expansion
(example: \(1/2=\sum_i(-1)3^i\)). `apply_even` raises `LeftoverCarryError`
rather than inventing an integer.

### Fixed \(k\) (EXACT — HUMAN PROOF as a composition; sizes computational)

`/2^k` is the \(k\)-fold product of `/2`. Naive state bound \(3^k\).
Reachable and minimized sizes are **COMPUTATIONALLY VERIFIED**.

### Valuation classes \(L_k\) (EXACT — HUMAN PROOF regular for each fixed \(k\))

\(L_k=\{\mathrm{BT}(n):v_2(n)=k\}\) is recognized by
`ModularAutomaton(2^{k+1})` with accept states those residues of exact
valuation \(k\). \(L_0\) coincides with odd weight.

### Unrestricted odd-part is not a single rational transduction (EXACT — HUMAN PROOF)

The machines in `src/bt/transducers/` and `src/research/collatz/transducers/` are deterministic
letter-to-letter **Mealy** transducers (LSD-first, carry in
\(\{-1,0,+1\}\)). On a finite word the `/2` machine is **subsequential**:
it may reject with leftover carry rather than emit a canonical integer.
Canonicalisation (strip leading zeros) is a subsequent length-changing
map. The **unrestricted** odd-part is the countable union of the
fixed-\(k\) machines. The following four steps show it is not a *single*
rational (hence not subsequential) function.

**1. Model.** A *rational function* is a partial function whose graph is a
rational relation (recognised by a finite-state transducer, possibly with
\(\varepsilon\)-transitions). Sequential and subsequential functions are
special cases. The implemented `/2^k` maps, with leftover-carry rejection,
are partial subsequential functions. The claim below is for the broader
class of rational functions, which includes every FST model used in this
repository.

**2. Closure.** If \(f\) is a rational function (or a sequential /
subsequential function) and \(L\) is a regular language, then
\(f^{-1}(L)\) is regular. In particular the preimage of a singleton word
language is regular. This is the standard image/preimage theorem for
rational relations (Eilenberg / Nivat).

**3. Non-regularity of \(\{\mathrm{BT}(2^j):j\ge 0\}\).** Let
\(L=\{w:\mathrm{decode}(w)=2^j\text{ for some }j\ge 0\text{ and }w\text{ is canonical}\}\).
Canonical balanced ternary is unique, so \(L\) is exactly the set of
displayed words of nonnegative powers of two.

Assume for contradiction that \(L\) is regular, with pumping length \(p\).
Choose \(N\) large enough that \(w=\mathrm{BT}(2^N)\) has length at least
\(p\), and write \(w=xyz\) with \(\lvert xy\rvert\le p\) and
\(\lvert y\rvert\ge 1\). For \(t\ge 0\) let \(w_t=xy^tz\) and
\(n_t=\mathrm{decode}(w_t)\). MSD evaluation gives

\[
n_t=\mathrm{decode}(xy^t)\,3^{\lvert z\rvert}+\mathrm{decode}(z),
\]

and \(\mathrm{decode}(xy^t)\) is a geometric polynomial in \(3^{t\lvert y\rvert}\),
so \(n_t=\alpha\,3^{t m}+\beta\) with \(m=\lvert y\rvert\ge 1\) and rationals
\(\alpha,\beta\) whose denominator divides \(3^m-1\).

- If \(\alpha=0\), then \(n_t\) is constant while \(\lvert w_t\rvert\) is
  strictly increasing. Uniqueness of canonical words implies at most one
  \(w_t\) lies in \(L\), contradicting the pumping lemma.
- If \(\alpha\neq 0\), then \(\lvert n_t\rvert\to\infty\) and
  \(n_{t+1}/n_t\to 3^m\ge 3\). The first digit of \(\mathrm{BT}(2^N)\) is
  \(+\), and \(\lvert xy\rvert\le p\) so that digit lies in \(x\) or in
  \(y\); for \(t\ge 1\), \(w_t\) still begins with \(+\), hence
  \(n_t>0\). If every \(w_t\) were in \(L\), we would have
  \(n_t=2^{j(t)}\) and the ratios \(n_{t+1}/n_t\) would be integer powers
  of \(2\) for large \(t\). A sequence of integer powers of two cannot
  converge to \(3^m\notin\{2^\ell:\ell\ge 0\}\). Contradiction.

Therefore \(L\) is not regular. The padded language \(0^\ast L\) is not
regular either: intersecting with the regular set of words that do not
start with \(0\) recovers \(L\).

The same pumping applies to \(\{\mathrm{BT}(-2^j)\}\) (first digit
\(-\)). The union \(\{\mathrm{BT}(\pm 2^j)\}\) is likewise non-regular.

**4. Contradiction.** Restrict odd-part to canonical words. Then
\(\mathrm{odd\_part}^{-1}(\{+\})=\{\mathrm{BT}(2^j):j\ge 0\}\), because
\(\mathrm{odd\_part}(2^j)=1\) and \(\mathrm{odd\_part}(-2^j)=-1\). The
singleton \(\{+\}\) is regular. If unrestricted odd-part were a rational
function, its preimage of \(\{+\}\) would be regular, contradicting
step 3.

**Boundary (EXACT — HUMAN PROOF).** Each *fixed* valuation branch is finite-state: \(L_k\)
is regular and `/2^k` is a 3-adic sequential Mealy machine. Unbounded
odd-part normalisation is not a single rational transduction. Detecting
unbounded \(k\) requires unbounded 2-adic precision.

On words, the Collatz step is exact:

\[
\mathrm{BT}(T(n))=\mathrm{odd\_part}(\mathrm{BT}(n)\,+).
\]

Residues still lose \(k\) bits of precision (Layer C).

---

## 13. Layer C — Valuation symbolic dynamics

State \((r,P)\) means \(n\equiv r\pmod{2^P}\), \(r\) odd. If
\(v_2(3r+1)=k\) is exact (\(k<P\)),

\[
T(n)\equiv\bigl((3r+1)\bmod 2^P\bigr)/2^k \pmod{2^{P-k}}.
\]

Next state: \(\bigl(((3r+1)\bmod 2^P)\gg k,\;P-k\bigr)\). Never divide
modulo \(2^P\). **EXACT — HUMAN PROOF** as a congruence. Implemented as
`exact_collatz_residue_step`.

A word \(k_1\ldots k_m\) at starting precision \(P\):

- **ADMISSIBLE**: some residue completes every exact-\(k\) test
- **INCONCLUSIVE**: every attempt hits `AT_LEAST_K` before the word ends
- **FORBIDDEN**: the prefix is fully testable and no residue matches it

Absence from a too-small \(P\) is not a global prohibition.

### Growth budget (EXACT — HUMAN PROOF comparison; not a Lyapunov function)

\[
\operatorname{sign}\Bigl(\sum k_i-m\log_2 3\Bigr)
=\operatorname{sign}(2^{\sum k_i}-3^m).
\]

Integer comparison, no floats. Equality is impossible for \(m>0\) because
\(\log_2 3\) is irrational (**EXACT — HUMAN PROOF**). This is the *homogeneous* size
estimate; the affine \(+1\) terms of \(T\) are omitted. Contraction of the
budget is **not** a Lyapunov function and **not** a proof of Collatz.

---

## 14. Layer D — Joint graph \(w\xrightarrow{k}w'\)

Exact edge:

\[
k=v_2(3n+1),\qquad w'=\mathrm{odd\_part}(w\cdot +)=\mathrm{BT}(T(n)).
\]

The graph on odd \(n\le N\) is a **sample**, not the Collatz dynamics.

- Forbidden valuation words: Layer C FORBIDDEN strings (**EXACT — HUMAN PROOF** relative
  to that 2-adic automaton).
- Synchronizing digit contexts: right-strings sending every odd state of
  `TwoAdicDigitAutomaton(K)` to one valuation class. Finite search:
  **COMPUTATIONALLY VERIFIED** / **OBSERVATION**.
- Images are never \(0\bmod 3\): **EXACT — HUMAN PROOF** (Milestone 1).

---

## 15. Milestone 3 — Valuation cylinders

For a valuation prefix \(\mathbf{k}=(k_0,\ldots,k_{m-1})\) with each
\(k_i\ge 1\),

\[
C_{\mathbf{k}}
=\{n\text{ odd}:v_2(3T^i(n)+1)=k_i,\;0\le i<m\}.
\]

Write \(K=\sum k_i\). The *minimum* precision that makes every test exact
is \(P=1+K\) (leftover \(Q=1\)).

### Unique residue / density \(2^{-K}\) (EXACT — HUMAN PROOF)

Work backwards from the unique odd residue \(1\pmod{2}\). If
\(T(n)\equiv r\pmod{2^P}\), invert with exponent \(k\):

\[
3n+1\equiv r\cdot 2^k\pmod{2^{P+k}},
\qquad
n\equiv(r\cdot 2^k-1)\,3^{-1}\pmod{2^{P+k}}.
\]

Three is odd, hence invertible modulo every \(2^{P+k}\). The candidate is
unique. Because \(r\) is odd, \(v_2(r\cdot 2^k)=k\), and the modulus
\(2^{P+k}\) with leftover \(P\ge 1\) is high enough to certify that the
valuation is *exactly* \(k\). Induction on \(m\) therefore gives:

- every finite word over \(\{1,2,\ldots\}\) is admissible at precision
  \(P=1+K\);
- there is a unique residue class modulo \(2^{1+K}\);
- among the \(2^{K}\) odd residues at that modulus, the density is
  exactly \(2^{-K}\).

Layer C `FORBIDDEN` labels are relative to a *fixed* starting precision
that may be smaller than \(1+K\). They are not global prohibitions of a
valuation word.

With leftover \(Q>1\) there are exactly \(2^{Q-1}\) classes modulo
\(2^{Q+K}\). The density among odd residues remains \(2^{-K}\).

`precision_cost(ks, leftover_Q) = leftover_Q + K` is the 2-adic
information budget: each Collatz step consumes \(k\) bits of known
precision. Relating \(2^K\) to \(3^m\) is the homogeneous size estimate
already in Layer C. It is **not** a Lyapunov function. The interpretation
“size contraction \(\leftrightarrow\) precision consumption” is a
dictionary between two exact integer quantities, not a descent proof.

Implemented as `valuation_cylinder` / `cylinder_residues`. Cross-checked
against `follow_path` on every composition with \(K\le 6\)
(**COMPUTATIONALLY VERIFIED**, redundant with the proof).

## 16. Milestone 3 — Cylinder languages and entropy

The balanced-ternary language of \(C_{\mathbf{k}}\) is the residue DFA
`ModularAutomaton(2^P)` with accept states equal to the cylinder residues
(MSD Horner \(r\mapsto 3r+a\bmod q\)).

**Convention.** Length-\(L\) counts are over *all* strings of length \(L\)
on \(\{-,0,+\}\), including leading zeros. That is the regular language of
the residue automaton. Canonical counts (first digit not `0`) are a
separate column and are not mixed into \(H_L\).

\[
H_L(\mathbf{k})
=\frac1L\log_3\#\{w:\lvert w\rvert=L,\;\mathrm{decode}(w)\in C_{\mathbf{k}}\}.
\]

Finite-\(L\) values and minimized state counts \(S(\mathbf{k})\) are
**COMPUTATIONALLY VERIFIED**. No spectral radius is claimed as a theorem.

Conditioning on a longer valuation prefix cannot increase the padded
word count, because the residue class modulo \(2^{1+K}\) refines the
class modulo \(2\). This is the Collatz analogue of “language of
surviving strings”: surviving means “prescribed future valuations”.

## 17. Milestone 3 — Transducer complexity spectrum

For each \(k\ge 1\):

- \(N_k\): minimized state count of the LSD `/2^k` Mealy product
  (naive bound \(3^k\) **EXACT — HUMAN PROOF**; reachable / minimized
  **COMPUTATIONALLY VERIFIED**);
- \(A_k\): minimized DFA size of \(L_k=\{w:v_2(\mathrm{decode}(w))=k\}\);
- \(\mathcal{C}_k=(A_k,N_k)\), with product \(A_k N_k\) recorded only as a
  crude bound on “recognise \(k\) then divide by \(2^k\)”.

On \(k=1,\ldots,4\) one has \(N_k=3,5,9,17=2^k+1\) and
\(A_k=4,8,16,32=2^{k+1}\) (the unminimised modulus). The statement
\(N_k=2^k+1\) for all \(k\) is a **CONJECTURE** (counterexample search
is `btlab collatz complexity`). It is not a theorem. \(A_k=2^{k+1}\)
on the same range is **COMPUTATIONALLY VERIFIED**, not proved.

Comparing \(N_k\) to the geometric weight \(2^{-k}\) is an
**OBSERVATION** only: rare branches may be computationally heavier.
That is not a Collatz theorem.

## 18. Milestone 3 — Symbolic futures graph

Nodes are \((\mathbf{k},\,r\bmod 2^P,\,P)\) with \(P=Q+K\). Edges append
one valuation symbol by recomputing the longer cylinder (equivalently:
lifting the residue, never dividing modulo \(2^P\)). This is a graph of
**symbolic Collatz futures**, not of sampled odd integers \(n\le N\).
The truncated word graph of Layer D remains a sample.

Nodes with nonempty prefix are classified by \(2^K\) vs \(3^m\)
(contracting / expanding). Equality is impossible for \(m>0\).

## 19. Implemented foundations

Milestone 1: exact \(T\), inverse tree, feature rows, weight parity,
`TwoAdicDigitAutomaton(K)`, experiment A.

Milestone 2: append-plus theorem and closed-form \(n\to 3n+1\) features;
LSD `/2` and `/2^k` transducers; regular \(L_k\); odd-part on words;
precision-drop Collatz residue step; admissible valuation prefixes and
exact growth budget; truncated joint graph \(w\xrightarrow{k}w'\).

Milestone 3: unique valuation cylinders of density \(2^{-K}\); cylinder
DFAs, \(H_L\), and \(A_k,N_k\) spectra; symbolic futures graph; rigorous
rational-function boundary for unbounded odd-part.

CLI: `theorems`, `odd-part`, `transducer`, `valuation-shift`, `joint`,
`cylinder`, `entropy`, `complexity`, `symbolic-graph`.

## 21. Milestone 4 — Affine itineraries (pointer)

Exact \(T^m(n)=(3^m n+C)/2^K\), minimum realizers, order-sensitive \(C\),
and nested-cylinder versus integer realizability are recorded in
[collatz_itinerary_compatibility.md](collatz_itinerary_compatibility.md).
Residue moduli are unchanged: leftover \(Q=1\), class modulo \(2^{K+1}\).

CLI: `itinerary`, `realizer`, `enumerate-itineraries`, `fixed-budget`,
`permutations`, `exceptional-search`.

## 22. Explicitly not implemented

Lyapunov / drift search, machine learning, unconstrained suffix statistics
as theorems, product with the prime sieve, and any claim of a route to
solving the Collatz conjecture.

## 23. Milestone 5 — zero-lift dynamics (pointer)

For nested minima \(R_m\), define the exact nonnegative lift

\[
t_m=(R_{m+1}-R_m)/2^{K_m+1}.
\]

Positive-integer realization of an infinite itinerary, eventual
stabilization of \(R_m\), and eventual vanishing of \(t_m\) are
equivalent. Every prefix has one unique zero-lift successor. Periodic
and eventually periodic words have exact affine compatibility tests.
These statements are **EXACT — HUMAN PROOF** in
[collatz_zero_lift.md](collatz_zero_lift.md).

Finite canonical-state residues provide exact immediate certificates
for many positive-lift extensions. No theorem connects sustained low
\(K_m/m\) to infinitely many positive lifts.

## 24. Milestone 6 — dual coding (pointer)

The exact direct realizer formula, closed lift-digit congruence,
mixed-radix reconstruction, bounded paired precision model, balanced-
ternary counterexample, permutation residue law, periodic traces, and
non-contracting censuses are recorded in
[collatz_dual_coding.md](collatz_dual_coding.md).

The stabilization, lift, mixed-radix, and abstract residue arithmetic
theorems compile under Lean 4 + Mathlib in `formal/`.

## 25. Four-coordinate compatibility and literature

For a finite exponent code, \(B=C\) in Kramer's notation,
\(r=R\bmod2^K\), and the least-positive endpoint representative is

\[
M\equiv C\,2^{-K}\pmod {3^m},\qquad1\le M\le3^m.
\]

The real diagnostic rates use natural logarithms. The exact state exposes
\(R\), \(M\), \(\operatorname{BT}(R)\), and \((3^m,2^K)\), but these are
coupled functions of the code: in particular, \(\operatorname{BT}(R)\) is
deterministic from \(R\), so it is not an information-theoretically
independent coordinate. Lossy balanced-ternary features can still be
useful finite search partitions. **EXACT — HUMAN PROOF** at the exact interface;
empirical utility is **COMPUTATIONAL**.

The comparison with Kramer, rational base \(3/2\), Dhiman--Pandey, and
Rozier--Terracol is in
[literature_comparison.md](literature_comparison.md). The balanced-ternary
scope is in
[balanced_ternary_vs_collatz_literature.md](balanced_ternary_vs_collatz_literature.md).
Cerdá's local formulas and the apparent defects in the preprints' global
non-reuse/convergence arguments are audited in
[cerda_comparison.md](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/cerda_comparison.md). All repository claims retain
the Milestone 6 verified baseline and do not depend on those global claims.

## 26. Affine-center geometry

For every nonempty exponent code, let

\[
D=2^K-3^m,\qquad n_*=\frac{C}{D}.
\]

Then \(D\ne0\), \(n_*\) is the rational fixed point of the code's affine
map, and the canonical start/end pair obeys

\[
DR-C=2^K(R-X),\qquad DX-C=3^m(R-X),
\]

\[
X-n_*=\frac{3^m}{2^K}(R-n_*).
\]

These are **EXACT — LEAN VERIFIED** in cross-multiplied form.
Expanding codes have \(n_*<0<M,R<X\); contracting codes move toward their
positive center. Kramer's representative satisfies \(X=M+q3^m\) for
\(q\ge0\), hence \(M\le X\). Simple total orders among \(R,M,C,n_*\) fail
in bounded exact censuses. See
[collatz_affine_center.md](collatz_affine_center.md).

## 27. Balanced-ternary word maps

Canonical reversal \(W\) is OEIS A134028, not an involution:
\(W(W(n))=n\) if and only if \(n=0\) or \(3\nmid n\). Companion maps
\(W_z\) (A160652) and \(W_{\mathrm{tail}}\) (A351702) are involutions.
The commutator \(W(T(n))-T(W(n))\) is defined only when both \(n\) and
\(W(n)\) are positive odd, and fails already at \(n=3\). Digit-sum
transition laws beyond append-plus were not obtained. Details, censuses,
and Q1–Q7 are in [collatz_bt_warp.md](collatz_bt_warp.md).

## 28. Fixed-integer affine-center geometry

For an actual trajectory the start is constant. The integer gap
\(G_m=2^{K_m}(n-T^m(n))\) is **EXACT — HUMAN PROOF**, as is the recurrence
\(G_{m+1}=3G_m+2^{K_m}(n(2^{k_m}-3)-1)\). The inequality \(n_{*m}\le n\)
is equivalent to \(T^m(n)\le n\) when \(2^{K_m}>3^m\), and is
**REFUTED EXACTLY** at \(n=165\), \(m=17\). The normalized series
\(A_m=C_m/3^m\) is not a new coordinate. No non-contracting obstruction
for a single fixed \(n\) was found. See
[collatz_fixed_integer_asymptotics.md](collatz_fixed_integer_asymptotics.md).

## 29. Periodic exponent-code languages

Primitive accelerated words are tested as cycle candidates. Expanding
periods are excluded. In the recorded enumeration \(1\le p\le 6\),
\(1\le k_i\le 4\), the only primitive exact cycle is \((2)\) at \(n=1\).
Additive amplitude of odd states is even. See
[collatz_cycle_languages.md](collatz_cycle_languages.md) and
[cycle_literature_replication.md](cycle_literature_replication.md).

