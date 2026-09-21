# Preimage density for the 3n−1 map: Krasikov–Lagarias transposed

Status: **PROMOTE** (a theorem, by transposition; the proof is a symmetry and the work was
reading the source, not inventing a method)

Branch of the Collatz bridge, beside
[juggler_negative_m_cycles](juggler_negative_m_cycles.md), which is Paper D. Opened and
closed the same day, 21 September 2026, because the transposition turned out to be exact.

## Problem

How many integers below \(x\) reach a given target under the \(3n-1\) map? Paper C's
Section 1.3 names Krasikov–Lagarias as the Collatz-side counterpart of its fate-contagion
theorem; nothing in print states the corresponding bound for \(3n-1\).

## Exact statement

Let \(g(y)=y/2\) for even \(y\) and \(g(y)=(3y-1)/2\) for odd \(y\). For a positive integer
\(a\) write
\[
\pi_a(x)=\#\{n\le x:\ g^{(j)}(n)=a\ \text{for some}\ j\ge0\}.
\]
**Claim.** For every fixed \(a\) not divisible by \(3\) there is an \(x_0(a)\) with
\(\pi_a(x)\ge x^{0.84}\) for all \(x\ge x_0(a)\).

## Current literature

- `krasikov-lagarias-2003-difference-inequalities` — **extended**. Their theorem is this
  statement for the \(3x+1\) shortcut map \(T(n)=n/2\), \((3n+1)/2\), read from the arXiv
  PDF on 21 September 2026. Their route is Krasikov's 1989 system \(I_k\) of difference
  inequalities on the residue classes mod \(3^k\), turned into a linear program whose
  largest feasible \(\lambda\) certifies the exponent \(\log_2\lambda\).
- `tao-2019-almost-all-collatz` — **known**. A different and stronger kind of statement,
  about logarithmic density rather than preimage counts, and not transposed here.
- Paper C, `juggler_fate_almost_all_note.md` Section 1.3 — the reason this branch exists.
  It explains why a counting bound of this shape is *not* a substitute for fate contagion:
  a set with counting function \(O(x^{0.84})\) has a convergent reciprocal sum, so the
  bound does not force a divergent logarithmic count.

## Branch budget

- **Target:** does the Krasikov–Lagarias exponent transpose to \(3n-1\), and at what value?
- **Novelty hypothesis:** nothing in print states a preimage density bound for \(3n-1\).
- **Falsifier:** the inequality system for \(3n-1\) differs structurally from theirs, so the
  linear program is a different program with a worse optimum.
- **Already killed by?:** `none`. `docs/negative_knowledge.md` carries no entry on preimage
  counting for either map, and the Hercher entry beside it concerns cycle bounds.
- **Existing machinery:** the \(3n-1\) map, its three cycles and its verified floor are all
  in `negative_m_cycles`; only the residue bookkeeping is new.
- **Maximum Phase-0 scope:** write both systems, check whether one is a relabelling of the
  other, and solve both.
- **Promotion criterion:** an exponent for \(3n-1\) with the derivation checked.
- **Stop criterion:** a strictly worse exponent with no structural reason would be a PARK.

## Balanced-ternary formulation

The whole argument lives on residues mod \(3^k\), so the natural coordinate is the base-3
expansion of the target. The fertile classes are a condition on the last trit, and the
mod-9 trichotomy a condition on the last two. No balanced-ternary machinery is used.

## Why BT may be relevant

Only through base 3. The productions move a class by \(m\mapsto4m\) and
\(m\mapsto(4m\pm2)/3\), the second a trit shift; a balanced reading might make the
three-way split look like a single carry rule, but nothing here needs it.

## Candidate operations / invariants

The two backward branches, \(a\mapsto2a\) and \(a\mapsto(2a+1)/3\), and the invariant that
divisibility by 3 is absorbing backwards: a multiple of three has no odd preimage and
neither does any of its doublings, so its tree is a single chain.

## Experiments

`python -m research.juggler_sequence.negative_preimage_density` writes
`data/research/juggler/negative_preimage_density/summary.json` and
[the report](../research/juggler_negative_preimage_density.md). It checks the negation
bijection exactly, solves both systems, and brute-forces the tree identity.

The exponents at \(k=9,10,11\) are too slow for a probe (\(3^{10}=59049\) classes) and were
solved once with a vectorised Collatz–Wielandt iteration, recorded as `HIGH_K` in the probe.

## Conjectures

None raised. The statement was settled in the direction expected.

## Counterexamples

None. Two known-bad inputs were run and both behaved:

- substituting the \(3x+1\) odd preimage \((2a-1)/3\) into the \(3n-1\) tree identity
  satisfies it in \(0\) of \(396\) cases;
- the identity fails on every fertile cycle member, which is why the "not in a cycle"
  hypothesis is carried rather than dropped. This matters more here than in the source: the
  \(3n-1\) map has three cycles where \(3x+1\) has one.

## Formalization

None. The content is a relabelling of residues and a linear program; neither is a good
Lean target, and the source's own computation is not formalized either.

## Results

- **Theorem (EXACT — HUMAN PROOF, one external input), \(m\not\equiv0\bmod3\).** Given
  Krasikov–Lagarias, for every fixed \(a\) not divisible by \(3\) and all large \(x\),
  at least \(x^{0.84}\) of the integers below \(x\) have \(a\) in their forward orbit
  under \(g\).
- **The proof is that negation is an isomorphism.** The map \(m\mapsto-m\bmod3^k\) carries
  the \(3x+1\) system onto the \(3n-1\) system coefficient for coefficient. Fertile classes
  \(2\bmod3\) go to \(1\bmod3\); the mod-9 split \(2,5,8\) goes to \(7,4,1\); the index
  \(4m\) is preserved; \((4m-2)/3\) goes to \((4m+2)/3\) and \((2m-1)/3\) to \((2m+1)/3\);
  the three lifts of \(m\) go to the three lifts of \(-m\); and \(\alpha=\log_23\) is
  untouched. Checked as exact integer arithmetic over every class for \(k\le10\).
- **Independent confirmation by solving both.** The exponents agree to the solver's
  tolerance at every \(k\):

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|
| exponent, both maps | 0.4366 | 0.6113 | 0.6891 | 0.7336 | 0.7608 | 0.7826 | 0.8032 | 0.8168 | 0.8295 | 0.8418 |

- **The solver reproduces both published anchors.** Krasikov 1989 reports \(0.43\) from
  \(k=2\) and Krasikov–Lagarias \(0.84\) from \(k=11\); the computed values are \(0.4366\)
  and \(0.8418\), and a published exponent is the computed one truncated downward, since it
  has to be a valid lower bound. Reproducing their headline at their own \(k\) is what says
  the system solved here is theirs.
- **Two solvers, independently written.** A scipy linear program written directly from their
  \(L^{NT}_k(\lambda)\), and the dependency-free Collatz–Wielandt iteration the probe ships,
  agree at every \(k\le8\). The laboratory does not depend on scipy, so only the second is
  committed.
- **The underlying identity, brute-forced.** For fertile \(a\) not on a cycle,
  \(\pi^*_a(x)=2+\pi^*_{4a}(x)+\pi^*_c(x)\) with \(c=(2a+1)/3\), because \(2a\) is then
  \(2\bmod3\) and has \(4a\) as its only preimage. Checked on \(366\) cases with no failure.

## Open questions

- The exponent is \(0.84\) because that is where Krasikov–Lagarias stopped, not because
  anything obstructs \(k=12\) or beyond. Their own hope is \(x^{1-\epsilon}\). Running
  \(k=12\) or \(13\) here would raise both maps together, and would be a statement about
  their method rather than about \(3n-1\).
- Whether the \(3n-1\) side admits a *divergent logarithmic* lower bound, of the kind
  Paper C proves for the Juggler map, is untouched by this. The measured obstruction is
  recorded with the fate-contagion comparison: the branch that carries backward mass upward
  in scale preserves it for the Juggler and halves it here.

## Decision

**PROMOTE.** The statement is a theorem for \(3n-1\) and appears to be new, and the
supporting apparatus is checked from both directions. It is one paragraph of mathematics,
not a paper: the honest description is a corollary of Krasikov–Lagarias obtained by
observing that their method never looks at the sign of the added constant. It belongs as a
remark beside Paper D rather than as a deposit of its own.

## Publication assessment

Not a paper. If Paper D takes a further version, this is a short section or an appendix
remark: it answers the obvious question of what is known about preimage density on the
negative side, and it costs half a page. It should be stated with the attribution in the
first sentence, because the method is entirely theirs and the transposition is a symmetry
anyone would accept on sight once it is pointed out.
