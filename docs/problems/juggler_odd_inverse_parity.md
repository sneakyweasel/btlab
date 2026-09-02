# Juggler odd-inverse parity (cube-block lanes)

Status: **CLOSE** (the inverse candidate is the Type-2 occupant
of `J-odd-pred-empty-cube`; cube-block Type-2 sets are
\(T\) of the odd square annulus; nested cubic conditions are
either a finite descent or forward landing parity)

Not a halt theorem, not a divergence exclusion, not a reopen of
odd-inverse width, empty-odd-cell forward laws, odd-landing
residues, odd towers, hug-cylinders, or fan-concat. Not a Paper A
edit and not a forward census of \(\lfloor x^{3/2}\rfloor\bmod 2\).

## Problem

For odd \(x\), \(T(x)=\lfloor x^{3/2}\rfloor=\operatorname{isqrt}(x^3)\).
The unique large-scale inverse candidate of an image \(y\) is
\(k=\lceil y^{2/3}\rceil\). Is the parity of this candidate a law
of the position of \(y\) in the cube block
\([m^3,(m+1)^3)\), and do nested cube-lane hits reformulate an
infinite flight?

## Exact statement

Write \(m=\mathrm{icbrt}(y)\) so \(y\in B_m=[m^3,(m+1)^3)\) and
\(r=y-m^3\). The candidate is \(k=\lceil y^{2/3}\rceil\), the
least integer with \(k^3\ge y^2\). Admissibility means Type 2:
the cell is occupied and \(k\) is odd (`J-odd-pred-empty-cube`).

**Cube-block identity (EXACT — HUMAN PROOF; COMPUTATIONALLY
VERIFIED on the Phase-0 grid).** For \(m\ge 1\),

\[
\{y\in B_m:\mathrm{Type}(y)=2\}
=\{T(x):x\text{ odd},\; m^2\le x<(m+1)^2\}.
\]

The occupant of each such \(y\) is that unique odd \(x\).
*Proof.* If \(x\) is odd in \(S_m=[m^2,(m+1)^2)\), then
\(m^3\le x^{3/2}<(m+1)^3\), so \(y=T(x)\in B_m\), and Type 2
with occupant \(x\) is Type 2-from-odd. Conversely, if
\(\mathrm{Type}(y)=2\) and \(y\in B_m\), the occupant \(k\)
satisfies \(k^3\ge y^2\ge m^6\) and
\(k^3<(y+1)^2\le(m+1)^6\), hence \(k\in S_m\). \(\square\)

**No \(T\)-free lane law (COMPUTATIONALLY VERIFIED).** Type-2
offsets in \(B_m\) are not an arithmetic progression for any
tested \(m\) with at least three hits. No residue class modulo
\(2,3,4,8,16,m,2m+1\) equals the Type-2 set once two-point
blocks are excluded. Gaps cluster near \(3m\) (binomial /
MVT), with four distinct gaps on large \(m\).

**Nested cubic conditions are a direction error (KNOWN /
REPARAMETERIZATION).** Odd inverse edges descend except
\(1\to 1\). A backward Type-2 spine is finite and dies at a
Type 0/1 cell (already [backward geometry](juggler_backward_geometry.md)).
Forward, each image is automatically Type 2, and continuation
requires the image itself to be odd — landing parity, the
closed odd-landing / odd-tower object.

No cycle of any length — not claimed. No divergent orbit — not
claimed.

## Current literature

- Type 0/1/2 emptiness — **EXACT — HUMAN PROOF**
  (`J-odd-pred-empty-cube`); **PARK** as a forward law
  ([juggler_empty_odd_cell.md](juggler_empty_odd_cell.md))
- Odd cell uniqueness — **EXACT — LEAN VERIFIED**
  (`odd_cell_unique`)
- Odd-inverse width as a hit obstruction — **REFUTED**
  ([juggler_odd_inverse_width.md](juggler_odd_inverse_width.md))
- Repeated inversion — **CLOSE**
  ([juggler_backward_geometry.md](juggler_backward_geometry.md));
  odd letters form a unique descending spine
- Iterated odd-landing sets — **CLOSE**
  ([juggler_odd_landing_sets.md](juggler_odd_landing_sets.md));
  residues / \(\theta\) / cylinders **REFUTED**
- Odd-tower fragment — **CLOSE**
  ([juggler_odd_tower_fragment.md](juggler_odd_tower_fragment.md));
  do not recensus \(\mathcal P_r\)

Project relationship: **refuted** as a new invariant;
**reparameterization** of Type 2 and the closed nest records.

## Branch budget

```text
Mathematical target     For integer y, is the parity of the unique
                        inverse candidate k=ceil(y^{2/3}) a law of
                        the cube-block residue r=y-m^3
                        (m=icbrt(y)), and do nested cube-lane
                        hits reformulate an infinite flight?
Novelty hypothesis      cube-block lanes give a modular/Diophantine
                        description of admissibility that does not
                        name T and is invisible from
                        floor(x^{3/2}) mod 2
Falsifier               Type-2 y in block m are exactly
                        {T(x): x odd in [m^2,(m+1)^2)}; offsets
                        have no simpler residue/AP/polynomial law;
                        backward odd nesting is finite; forward
                        nesting is landing parity
Existing machinery      odd_cell_unique; J-odd-pred-empty-cube
                        (k=ceil(y^{2/3}), Types 0/1/2);
                        empty_odd_cell.icbrt/ceil_cbrt/odd_cell_kind;
                        backward_geometry (odd inverse descends);
                        odd_landing_sets / odd_tower CLOSE
Maximum Phase-0 scope   prove or refute the cube-block identity;
                        lane census on small m; residue/AP hunt
                        on offsets; cite (do not rerun) backward
                        spines and P_r; no Lean, no CLI, no
                        companion, no Paper A, no floor raise
Promotion criterion     a (m,r) law that is not Type 0/1/2 and
                        not "y=T(x) for odd x in the square annulus"
Stop criterion          statements are KNOWN or REPARAMETERIZATION
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Inverse candidate \(k=\lceil y^{2/3}\rceil\) —
  **KNOWN** (`J-odd-pred-empty-cube`)
- Type 2 iff occupied and \(k\) odd —
  **EXACT — HUMAN PROOF** (existing)
- Cube-block Type-2 set equals \(T\) of the odd annulus —
  **EXACT — HUMAN PROOF**; **COMPUTATIONALLY VERIFIED**
  on \(m\le 40\) and \(\{50,80,100\}\)
- Type-2 offsets form an AP, or a deciding residue class —
  **REFUTED** on the Phase-0 grid (two-point \(m=1\)
  congruence \(r\equiv 0\pmod 4\) excluded)
- Single-residue occupancy on tiny blocks —
  **OBSERVATION** at \(m=1\) (mod 4) and \(m=4\) (mod 2);
  not deciding and not uniform (named image \(T(3)=5\) is odd)
- Backward Type-2 spines are infinite —
  **false**; they descend and die
- Nested cubic conditions reformulate an infinite flight —
  **REFUTED** (`juggler_odd_inverse_parity`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_inverse_parity`
- Artifact:
  `data/research/juggler/odd_inverse_parity/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_odd_inverse_parity.py`

Identity on every \(m\le 40\) and on \(\{50,80,100\}\). Offset
residue/AP hunt on those blocks. Named odd hits
\(\{3,37,365,761\}\). Backward nest sanity on Type-2 \(y\le 200\)
and on the named hits. No \(\mathcal P_r\) rerun. No CLI. No
Lean. No \(n_{\max}\) raise.

## Conjectures

- `juggler_odd_inverse_parity` — **REFUTED**.

## Counterexamples

- “Cube-block lanes are a positive-length admissibility
  interval” — Type-2 \(y\) in \(B_m\) are the discrete image
  of the odds in \(S_m\), density \(\sim 1/(3m)\). At \(m=10\),
  ten hits in a block of length \(331\); at \(m=100\), one
  hundred hits in a block of length \(30301\).
- “Offsets obey a residue law” — no deciding class on
  \(m\ge 2\). The \(m=1\) pair \(\{1,5\}\) is \(r\equiv 0\pmod 4\)
  in a seven-point block and is not a law.
- “Offsets form an AP” — \(m=5\) offsets
  \(0,15,31,47,64,82\) have four gaps; large \(m\) keep four
  distinct gaps near \(3m\).
- “Infinite nested cubic conditions” — backward spines
  descend (max depth \(3\) on Type-2 \(y\le 200\)); named
  images \(T(3),T(37),T(365),T(761)\) have depth \(1\) and
  die at a Type 0 occupant. Forward continuation is landing
  parity.

## Formalization

None new. `odd_cell_unique` stays in `Cells.lean`. No
`OddInverseParity.lean`. The cube-block identity is a
one-line corollary of `J-odd-pred-empty-cube` and is not
a ledger row. Paper A is unchanged. No `sorry`.

## Results

Classification **ODD_INVERSE_PARITY_REPARAMETERIZATION**.

- Identity holds on every tested \(m\): occupant list equals
  the odd annulus, Type-2 set equals \(\{T(x)\}\).
- \(|B_m\cap\mathrm{Type\,2}|=|S_m\cap\mathrm{odd}|\), which
  is \(m\) or \(m+1\) according to the parity of \(m^2\).
- Offset hunt: no AP at \(n_{\mathrm{type2}}\ge 3\); no
  deciding residue. Gaps at large \(m\) lie in
  \(\{3m,3m+1,3m+2,3m+3\}\).
- Named hits are Type 2 self-preimages with
  \((m,r,k)=(1,4,3)\), \((6,9,37)\), \((19,114,365)\),
  \((27,1310,761)\). Images \(5\) and \(225\) are odd;
  \(6973\) and \(20993\) are even — cube-block position
  does not hide a new parity invariant.
- Nest: \(17\) Type-2 values in \(y\le 200\), all spines
  descend, max depth \(3\).

## Open questions

None from inverse-candidate parity. Do not reopen odd-inverse
width, empty-odd-cell forward laws, odd-landing residues, odd
towers, hug-cylinders, or a new \(n\)-window for fan-concat.
The fan-follower stays a coherent surviving failure mode; this
door does not kill it and does not construct it.

## Decision

**CLOSE.** The unique inverse candidate is the existing Type-2
occupant. Its “admissibility interval” inside a cube block is
the discrete odd-annulus image, not a modular lane. Nested
cubic conditions split into a finite backward descent (already
CLOSE) and forward landing parity (already CLOSE). Every
Phase-0 statement is `KNOWN` or `REPARAMETERIZATION`. That is
the stop criterion. Best next question: none from this door;
do not start another inverse-cell census.

## Publication assessment

Status: `EXPLORATORY`. A calibration, an identity corollary,
and a slogan refutation. Not a paper candidate. No Paper A/B
edit. No flight-note rewrite.
