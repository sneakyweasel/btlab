# Juggler atlas continuation graph

Status: **EXPLORATORY**

A reading of the parked word-atlas census
`wa-20260827T200310Z-cuda-k20-n100000000` (\(k\le 20\), \(n\le 10^8\)).
It is not a new language law, not a residual graph, and not a
termination theorem. Do not reopen
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.

The GPU walks the integer map \(n\mapsto\texttt{floorPower}(n)\). The
object that appears is a different directed graph: the
language-filtered prefix trie on finite \(O/E\) words, stored as
`successor_mask` in [`storage.py`](../../src/research/juggler_sequence/atlas/storage.py).

## Branch budget

```text
Mathematical target     What directed graph does the atlas census
                        actually make appear, and which of its
                        features are structural rather than window
                        artefacts?
Novelty hypothesis      None. Distillation of an existing census.
Falsifier               A stored adjacency of integers, or a new
                        forbidden-factor law read from pruning
Existing machinery      Kernel A, continuations, ItineraryLanguage.lean,
                        even-run scale barrier / even tower
Maximum Phase-0 scope   Read the SQLite continuation and realizer
                        tables; write the observations; no new kernel
Promotion criterion     Not applicable. Default PARK with the atlas.
Stop criterion          Any linguistic rewrite of a>=2 or 3^{#O}>2^{|w|}
```

## The graph

Vertices are observed finite itineraries. Edges are one-letter extensions
that remain in the same language. For REALIZABLE this is a binary
tree layered by length: in-degree is \(0\) or \(1\), out-degree is
\(0\), \(1\), or \(2\), and every edge increases length by \(1\).

The integer map is only the generating dynamics. It is a functional
graph (out-degree \(1\)) and is not stored.

Lean already fixes the infinite-language geometry
([`ItineraryLanguage.lean`](../../formal/Problems/Juggler/ItineraryLanguage.lean)):
`jugglerLanguage` is prefix-, suffix-, and factor-closed, and
\(T\) is total, so the true REALIZABLE trie is right-extendable.
`expandingLanguage` is not factor-closed: `OOE` expands at \(5\),
`OE` never expands.

What follows is a **COMPUTATIONALLY VERIFIED** reading of one
bounded experiment, except where a statement is elementary or
already Lean-tagged.

## 1. The first holes are three lost children of the even square-tower

The REALIZABLE trie is the complete binary ball of radius \(5\).
The first unary nodes appear at length \(5\), and they are exactly
three even-heavy prefixes:

| word | min realizer | kept child | lost child | missing length-6 word |
|------|-------------:|------------|------------|------------------------|
| `EEEEE` | \(65536=2^{16}\) | `O` | `E` | `EEEEEE` |
| `EEEEO` | \(256=2^{8}\) | `O` | `E` | `EEEEOE` |
| `EEEOE` | \(6250000=2500^{2}\) | `E` | `O` | `EEEOEO` |

There are \(32\) itineraries of length \(5\) and \(61\) of length \(6\).
Three unary parents, each losing one child, account for all three
missing length-6 words. Because the stored REALIZABLE graph is a
tree, later holes are accumulated lost children, not a second
mechanism.

The exact even words follow the power-of-two tower

\[
\min\mathrm{realizer}(E^{r})=2^{2^{r-1}}\qquad(r=1,\ldots,5):
\]

\(2,4,16,256,65536\). This is **EXACT — HUMAN PROOF**, not a census
accident: if \(m\) is the least realizer of \(E^{r-1}\), then the
least \(n\) with \(\lfloor\sqrt{n}\rfloor=m\) is \(m^{2}\), and any
larger even image \(m'>m\) forces \(n\ge (m')^{2}>m^{2}\). The same
tower is already excluded from a minimal non-1 orbit
(`even_tower_not_on_minimal` in the even-run scale barrier).

\(E^{6}\) would start at \(2^{32}=4294967296>10^{8}\). Under this
bound the rooted even ray stops at `EEEEE`. That is scale, not a
forbidden factor.

## 2. The same three words are abundant as interior factors

The atlas `factors` table for REALIZABLE is the set of realized
*prefixes*, not the set of substrings. Read as prefixes, the three
length-6 words are `NOT OBSERVED WITHIN SEARCH BOUND`.

Read as actual factors of stored length-\(20\) realized prefixes,
they are common, and they never sit at position \(0\):

| word | occurrences as a substring of a length-20 realized prefix | earliest position |
|------|----------------------------------------------------------:|------------------:|
| `EEEEEE` | \(3948\) | \(1\) |
| `EEEEOE` | \(6167\) | \(2\) |
| `EEEOEO` | \(11357\) | \(1\) |

Example: \(1571189\) realizes `OOOOOOOOOOEEEEEEEEEE`, which contains
`EEEEEE` from position \(10\). After an odd letter, a long even run
is an ordinary collapse. As a *root*, the same run is a square
tower past the scan bound.

This is the single most useful graph fact in the census. The rooted
trie and the factor language describe the same infinite
`jugglerLanguage`, but they have wildly different witnesses. A hole
in the prefix table is not a hole in the trajectory.

## 3. The even-prefix corridor freezes; the odd-prefix tree keeps branching

Among all realized prefixes of length \(\le 20\), the longest
leading even run is \(5\). From length \(12\) through \(19\) there
are exactly **\(37\)** words that start with `EE`, and every one of
them is unary. The even-start subtree has become \(37\) rays.

Unary rate at length \(19\):

| leading run | nodes | unary fraction |
|-------------|------:|---------------:|
| starts odd | \(76332\) | \(0.285\) |
| `E` then mixed | \(1476\) | \(0.996\) |
| `EE` or longer | \(37\) | \(1.000\) |
| `O^{10}` or longer | \(512\) | \(0.000\) |

Leading odds do the opposite of leading evens: a long opening odd
run is almost surely binary. Formally expanding letter-count
(\(\texttt{exponent_surplus}>0\)) is also protective: unary rate
\(0.118\) versus \(0.526\) on the contracting side, still at
length \(19\).

The observed REALIZABLE graph is therefore not a uniform random
subtree. It is **odd-branching and even-freezing**. That matches
the dynamics: an even step is a floor square-root and destroys
scale; an odd step is a floor \(3/2\)-power and creates room for
both later parities.

The \(37\) frozen `EE…` itineraries of length \(12\) are listed in
[juggler_atlas_graph.json](juggler_atlas_graph.json). Almost all
keep `O` and lose `E`. Several min-realizers are themselves
squares (\(4,16,100,256,676,2500,10000,65536,131044,\ldots\)).
The itinerary-language pullback witness \(131044\) is one of these rays
(`EEOEOOEOEEEO`), not a rooted `EEEEEE`.

## 4. Stable exponential growth, no internal sinks

The census identity of a tree holds exactly:
\(N(k+1)\) equals the sum of out-degrees at length \(k\). In
particular \(23292\cdot 1+54553\cdot 2=132398\).

Mean branching \(N(k+1)/N(k)\) stays in \([1.65,1.91]\) after the
complete ball. About \(30\%\) of internal nodes are unary from
length \(8\) onward; that fraction is not marching toward \(1\).
Under this bound the process is a stable pruning, not a collapse.

Density in the full binary tree still goes to \(0\):
\(N(20)/2^{20}=132398/1048576\approx 0.126\), consistent with
\((\lambda/2)^{k}\) for \(\lambda\approx 1.7\). The realized
prefix language is an exponentially thin subset of \(\{O,E\}^{*}\)
inside the window. That does not imply
\(\mathcal L\neq\{O,E\}^{*}\) in the infinite language. Short
missing prefixes are even-scale, and the closed word-language
branch already produced later witnesses for several of them.

REALIZABLE has **no** out-degree-\(0\) node before the horizon.
That is forced by Kernel A: a realized prefix of a length-\(20\)
trajectory automatically owns its next letter. It is also the
bounded shadow of right-extendability of `jugglerLanguage`.

Lost-child bias is mild. Among unary nodes, the fraction that lose
`O` (keep only `E`) oscillates between about \(0.29\) and \(0.53\).
There is no one-sided letter prohibition.

## 5. EXPANDING is a different subgraph, not a thinner copy

Expanding itineraries are a proper subset: the ratio
\(N_{\uparrow}(k)/N(k)\) oscillates between \(0.17\) and \(0.55\)
and is not monotone (\(0.188\) at \(k=5\), \(0.553\) at \(k=19\),
\(0.482\) at \(k=20\)).

Unlike REALIZABLE, the EXPANDING continuation graph has dead ends.
The first is `EEOOOO` at length \(6\). This is structural: a start
may expand on \(w\) and fail to expand on both one-letter
extensions. Existential expansion is not right-extendable. Combined
with the Lean fact that it is not factor-closed, EXPANDING is not
“REALIZABLE with a density.” It is a different directed graph on
the same alphabet.

## 6. PE_CERTIFIED is a thin regular spine; PE_RUN is the grammar corridor

Single-block `PE_CERTIFIED` has very few distinct words per length
(\(1\) to \(7\)). Its extracted factor counts are

\[
p_{\mathrm{PE}}(r)=r+1\qquad(r\le 8),
\]

then **freeze at \(9\)** from \(r=8\) through \(r=20\). The
continuation masks are almost purely “keep `E`”: from length \(8\)
onward the graph is nine vertices, seven of them unary-`E`, one
binary, one dead. That is the \(O^{a}E^{b}\) block language drawn
as a graph — a narrow band of odd-then-even splits, not a second
binary tree.

`PE_RUN` is thicker (concatenations of those blocks) and does have
internal sinks. Binary absences such as `EOEO` remain the known
\(a\ge 2\) grammar. No extra PE-run factor constraint survived
inside the stated bound.

## 7. The graph does not compress the leftover arithmetic

Prefix futures still do not determine the next PE block. On the
closed word-language scan, `OOE` continued as `OOE`, `OOOOE`,
`OOOOEE`, or stopped. The symbolic Myhill–Nerode quotient is
strictly coarser than the landing integer
(`RESIDUAL_STATE_NEEDS_X`). The continuation mask is a census
index, not a finite automaton for odd-to-odd continuation.

## What this does not say

- The three length-6 prefix holes are not forbidden factors.
  `EEEEEE` is a known interior factor of the PE run at \(14237\),
  and it is a common substring of length-\(20\) realized prefixes.
- Branching less than \(2\) is not a new arrangement law.
- The frozen `EE` rays are a window picture of even-scale, already
  constrained on minimal orbits by the even-run scale barrier.
- Nothing here decides whether every positive integer reaches \(1\).

## Decision

**PARK** with the atlas. The interesting object is the prefix trie
and the split between rooted even-scale and interior even-runs.
That is a reading of existing tables. It does not promote a
theorem and does not reopen the closed language branch.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?
