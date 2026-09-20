# The even-run dual of Lemma 8

Status: **CLOSE** (the dual floor is real, correct, and capped below
Lemma 8 by the very shape condition that defines the family)

Standalone arithmetic phase on the Collatz bridge, and the complement of
[the negative Lemma 8 window](juggler_negative_lemma_eight_window.md).
Not a cycle exclusion, not a termination theorem, not a floor raise, not
a reopen of Paper A, of the finance mirror, or of the near-convergent
Diophantine branch.

## Problem

`2` acts on the odd part of \(\mathbb Z\) in two ways: by its valuation
and by its multiplicative order. Hercher's Lemma 8 — the laboratory's
pointwise floor, priced on the mirror side by the window branch — uses
only the valuation, and reads it off the *odd*-run structure. The even
runs are then unused. Does the order give a second floor off them, and
if so is it independent of Lemma 8 or subordinate to it?

## Exact statement

Let \(C\) be a cycle of the shortcut map \(T(x)=x/2\) (even),
\((3x+1)/2\) (odd) on \(\mathbb Z\) carrying at least one even step, with
odd elements \(x_1,\dots,x_o\) in cyclic order and \(r_i\) halvings
between the odd step at \(x_i\) and \(x_{i+1}\), so
\(2^{r_i+1}x_{i+1}=3x_i+1\). Let \(R=\gcd\{r_i:r_i>0\}\) and let \(m\) be
any divisor of \(2^R-1\) with \(\gcd(m,2^o-3^o)=1\). Then

\[
x\equiv -1 \pmod m \quad\text{for every odd } x\in C,
\qquad\text{hence}\qquad |x|\ge m-1 .
\]

*Proof.* In \(u=x+1\) the passage is
\(2^{r_i+1}u_{i+1}=3u_i-2+2^{r_i+1}\). If \(\operatorname{ord}_m(2)\mid
R\mid r_i\) then \(2^{r_i+1}\equiv 2\), the correction
\(2^{r_i+1}-2\) vanishes, and \(2u_{i+1}\equiv 3u_i\). Composing once
around the cycle gives \(u_1(2^o-3^o)\equiv 0\), and the coprimality
forces \(m\mid u_1\); the starting label is arbitrary. \(C\) has an even
step so \(C\neq\{-1\}\), hence \(u_i\neq 0\). \(\square\)

Equivalently, through the block expansion of the charge — **which is
Brox's, not ours** (`brox-2000-collatz-cycles-few-descents`, Acta Arith. 92
(2000) 181–188, equations (3.1) and (3.2)) — for **every** word, with \(r_j\) the E-run lengths from the right and
\(A_j=(o-j)+\sum_{l>j}r_l\),

\[
\operatorname{evenCharge}(w)=\sum_{j=0}^{o}3^{j}2^{A_j}\bigl(2^{r_j}-1\bigr),
\]

so every term carries a Mersenne factor and \((2^R-1)\mid
\operatorname{evenCharge}(w)\); the cycle equation
\((x+1)(2^d-3^o)=\operatorname{evenCharge}(w)\) then reduces to the same
congruence.

**Priority, corrected 20 September 2026.** That expansion is in print.
Brox's (3.2) is \(\tilde F_i = M(x_i+1)\), the same \(u=x+1\)
conjugation applied to the cycle constant, and his (3.1) is
\(2\sum_{l}3^{\,n-1-l}2^{\,k_1+\cdots+k_l}(2^{\,k_{l+1}-1}-1)\) —
term for term the display above, with the Mersenne factor on the
*extra*-halving exponent, verified here against
\(\operatorname{evenCharge}\) on all 16382 words of length \(\le 14\)
beginning with \(O\), zero differences. What Brox does **not** do is take
a gcd: he uses the brackets only as a size bound, replacing them by
\(2^{h}\) to feed a Baker–Feldman argument for his Theorem 1.1. So the
identity is his; the gcd step and the congruence are what this branch
adds, and a sweep found no one taking that step. The bookkeeping matters
and is not interchangeable: the same statement with the **full** halving
counts \(k_i\) in place of the extra halvings \(r_i=k_i-1\) is
**false** — \(OE\) has \(k=(2)\), \(\gcd=2\), \(u=2\) and
\(3\nmid 2\); 79 failures against 0 holds over words to length 12. It is
Brox's exponent, not Simons–de Weger's matrix equation, that carries it.

Lemma 8 reads \(v_2\) off the odd runs and gives \(|x|\ge 2^a-1\); this
reads \(\operatorname{ord}(2)\) off the even runs and gives \(|x|\ge
2^R-1\). Same congruence \(x\equiv -1\), two different moduli.

## What the reduction is

Modulo \(2^R-1\) the even steps become **invisible** and the orbit is the
free recursion \(u\mapsto 3u/2\). That recursion is this laboratory's own
object: it is the Juggler's exponent transport
(`J-lemma-eight-is-the-exponent-valuation`), where on the perfect-power
locus \(n=a^e\) the exact step acts as \(e\mapsto 3e/2\) on an odd base
and \(e\mapsto e/2\) on an even one, with no floor loss whatever. So the
Mersenne modulus is precisely the reduction under which Collatz *becomes*
the Juggler's exponent dynamics — and on the Juggler side the no-cycle
argument is a pure exponent count, \(3^o\neq 2^o\), needing neither
Catalan nor Baker.

The price of the transport is exactly measurable: pulled back through
the congruence, \(3^o\neq 2^o\) degrades from a contradiction into
\(m\mid u\). **An impossibility becomes a floor.** That is the answer, on
the cycle side, to why the Juggler's free argument does not come back
across the bridge.

## Where it stops, and why it must

On a word all of whose proper prefixes are non-contracting — Paper A's
CycleMin shape, which by `neg_cycle_word_is_juggler_shape` is the shape
of a negative Collatz cycle word at its minimum and of a Juggler cycle
word, and by `prefix_bound_of_min` of a positive one too — the leading
run of \(a\) odd letters is followed by an E-run of length \(r_1\ge 1\),
and non-contraction at the end of that run reads \(3^a\ge 2^{a+r_1}\).
Since \(R\mid r_1\),

\[
R\;\le\;r_1\;\le\;\bigl\lfloor(\log_2 3-1)\,a\bigr\rfloor
=\lfloor 0.58496\,a\rfloor ,
\]

so the dual floor \(2^R\) sits below Lemma 8's \(2^a\) by the factor
\(2^{(2-\log_2 3)a}=2^{0.41504\,a}\) and can never bind. The single
exception to the cap is the word whose first E-run is also its last,
\(O^aE^r\) — the circuit, whose nontrivial case Steiner 1977 excludes —
and there the dual still does not win.

The two floors are anti-correlated by the condition that defines the
family: prefix non-contraction forces the word to bunch its odd letters,
which lengthens odd runs and shortens even runs. The dual is not an
opportunity the laboratory missed; it is structurally excluded from the
side the Juggler lives on.

## Measured

| check | scope | result |
| --- | --- | --- |
| block expansion | all \(2^{13}-2\) words to length 12 | 0 violations |
| \((2^R-1)\mid\) charge | words to length 14 with \(R\ge 2\) | 0 violations |
| congruence at odd elements | rational cycles, words to length 13 | 0 violations |
| vacuous at known cycles | \(1,-1,-5,-17\) | all four, \(R\le 1\) |
| cap | expanding shape words to length 22 | 0 exceptions, attained |
| cap | contracting shape words to length 22 | 12 exceptions, all circuits |
| dual beats Lemma 8 | both families | 0 words |
| dual-only kills vs `neg_cycle_finance` | 198891 shape words | **0** |

Extended separately in the session scratchpad to length 26
(2 264 815 shape words): the dual kills 2180 against the finance
ceiling, every one already dead by Lemma 8, dual-only kills still 0.

Every known cycle of the \(\mathbb Z\) map has an E-run of length 1, so
\(R=1\) and the dual says nothing about any of them — the exact opposite
of Lemma 8, which all three attain with equality
(`J-lemma-eight-floor-is-tight-at-every-known-cycle`).

## Current literature

- `hercher-2023-collatz-m-cycles`, Lemma 8. **known**; the dual uses the
  same \(u=x+1\) conjugation, read through the order instead of the
  valuation.
- `brox-2000-collatz-cycles-few-descents`, Acta Arith. 92 (2000) 181–188,
  equations (3.1), (3.2), (3.7). **known**, and it owns the block
  expansion; read this session from a public GitHub mirror, not at the
  publisher. He takes no gcd and derives no congruence.
- `simons-de-weger-2005-collatz-m-cycles`, §2.1–2.2. A Mersenne-factored
  expansion of the cycle constant with the **full** halving counts, and
  \(x_i\equiv -1 \pmod{2^{k_i}}\) on the same page; no gcd is taken, and
  the naive full-count reading is false (above). **known**.
- `halbeisen-hungerbuehler-1997-collatz-cycles`, §5 Lemma 9: a gcd over
  cyclic shifts of the numerator, a different object — and they state
  explicitly that size estimates cannot settle the cycle question and that
  number-theoretic arguments would be needed. **known**.
- `eliahou-1993-collatz-cycle-lengths`. **not read at source**; inferred
  from Lagarias's annotated bibliography entry 53 and from
  Halbeisen–Hungerbühler §4.2, which reproduce his criterion as a pure
  size / continued-fraction criterion.
- Laboratory: `cycle_divisibility.py` handles the complementary case
  \(q\mid D=2^K-3^p\) by the finite-field walk; the dual lives in the case
  \(q\nmid D\) and is not implied by it. **extended**.
- Steiner 1977 for the circuit exception. **known**.

Project relationship: **extended**.

**Novelty, settled 20 September 2026 — and the earlier caveat here was
wrong.** It read that the primary sources were unreachable and the
question therefore unknown. They were reached: Hercher 2023,
Simons–de Weger 2005, Halbeisen–Hungerbühler 1997, Brox 2000 and
Lagarias's two annotated bibliographies were read in full through a public
GitHub mirror. The result splits three ways.

- The **block expansion is KNOWN** and is Brox's (3.1)/(3.2). It was
  presented here as ours; it is not. Corrected above.
- **Hercher's Lemma 8 uses no multiplicative order and no Mersenne
  number**, now verified at source rather than inferred — grep over the
  full text returns zero hits for either, and every \(\equiv -1\) in the
  corpus has a power of two as modulus.
- The **gcd step and the congruence were searched hard and not found** —
  but they are one line from a printed identity, and saying so is part of
  the claim. A reader who knows Brox sees the corollary immediately.

What stands as this branch's own content is not the congruence but the
**subordination**: \(R\le\lfloor(\log_2 3-1)a\rfloor\) on the CycleMin
shape, zero dual-only kills over 2.26 million words. Nothing resembling it
was found. Post-2009 coverage rests on search snippets, so absence is a
failure to find, not a proof.

## Branch budget

```text
Mathematical target     2 acts by valuation and by order; Lemma 8 uses only
                        the valuation, off the odd runs. Does the order give
                        a second floor off the even runs, and is it
                        independent of Lemma 8 or subordinate to it?
Novelty hypothesis      The gcd of the even runs supplies a Mersenne modulus
                        in which the even steps vanish and Collatz becomes
                        the Juggler's free exponent recursion, so the
                        Juggler's no-cycle count pulls back as a floor.
Falsifier               The dual is vacuous on the shared word shape, or it
                        is dominated by Lemma 8 there, or it contradicts a
                        known cycle.
Already killed by?      No. The window branch priced the valuation and did
                        not touch the order; cycle_divisibility.py covers
                        q | D and this is q not dividing D; the p-adic
                        coupling branch is about v_2 and v_3 of the gap, a
                        different object. Searched docs/negative_knowledge.md
                        for Mersenne, order, even-run and gcd clusters.
Existing machinery      even_charge, shape_words and window from the window
                        branch; cycle_from / word_of for the Z map; the
                        kernel-checked neg_cycle_finance ceiling.
Maximum Phase-0 scope   verify the identity and the congruence by census,
                        compute R against the leading odd run on both cycle
                        families, and sieve against the finance ceiling.
Promotion criterion     one shape word killed by the dual and not by Lemma 8.
Stop criterion          a proved cap putting the dual below Lemma 8 on the
                        shared shape.
```

The stop criterion fired. **CLOSE.**

## Decision

**CLOSE**. The branch answers its target with a proof in each direction.
The dual floor exists and is correct: the multiplicative order of 2, read
off the even runs, gives the same congruence \(x\equiv -1\) that Lemma 8
gets from the valuation of 2 read off the odd runs. And it is subordinate
wherever this laboratory works: the CycleMin shape caps \(R\) at
\(\lfloor(\log_2 3-1)a\rfloor\), putting the dual below Lemma 8 by
\(2^{0.41504\,a}\), with the circuits as the only exception and zero
dual-only kills in a census of 2.26 million shape words. The two floors
are anti-correlated by the shape condition itself, so this is a structural
exclusion, not a census accident.

What the branch adds beyond the kill is the reduction: modulo \(2^R-1\)
the even steps vanish and Collatz *is* the Juggler's free exponent
recursion, where no-cycle is the pure count \(3^o\neq 2^o\). The price
of pulling that back is exactly that the impossibility becomes a floor —
which is the cycle-side answer to the session's bridge question.

Best next question: none from this branch. Do not re-derive a floor from
the even-run structure on any prefix-noncontracting family; the cap
forecloses it.

## What this does not say

No Juggler cycle is excluded, no floor is raised, \(N_0=3.5\cdot10^8\) is
untouched, and no negative Collatz cycle is newly excluded. The dual is a
theorem about cycles of the \(\mathbb Z\) shortcut map; its laboratory
content is that the CycleMin shape caps it below the floor this
laboratory already has, so it closes a direction rather than opening one.
Neither map is claimed to halt.

## Publication assessment

Status: `EXPLORATORY`.

Not a paper candidate and not a Juggler bound. The dual floor is correct and
subordinate: the CycleMin shape caps the even-run exponent, so wherever this
laboratory works the dual sits below Lemma 8, with zero dual-only kills in a
census of 2.26 million shape words. Its value is that the subordination is
structural rather than a census accident, which is worth recording and is not
worth a manuscript.
