# The Juggler corner of OEIS is swept, and three of its four sequences were already ours

OEIS names 30 sequences after the Juggler. This laboratory cited five ---
A094683, A007320, A094670, A094679, A094716 --- and had never mentioned the
other 25. The sweep that established this is in the dossier; what belongs here
is what it closed.

**A094778 is Paper B's object and it agrees.** The Juggler's dropping time at
\(2n+1\) is the non-contracting-prefix census read pointwise, and an
independent walker reproduces it on every defined term. The only difference is
the endpoint convention at \(n=0\), where \(1\) is the fixed point and nothing
drops. This was checked twice on 20 September, by two sessions that did not
know of each other: once against 100 terms from the branch, once against the
40 terms of the bulk snapshot in exact integer arithmetic. Neither found a
disagreement, and the second was redundant.

**The sequence identifications are not novelty.** The mathematics was
kernel-checked before the sweep; the sweep adds a closed form for the plateau
locations and one name. Do not open a branch to "identify" these sequences
again, and do not write a manuscript sentence claiming any of them.

**What the sweep does not close.** The variant family A095396--A095401 and the
2025--26 additions A380891, A381246, A389383, A396851 are uncited and
untouched. The variant family is a real test --- it moves the exponent pair
while keeping the shape --- and it is open, not killed.

Update, 23 September 2026: the bounded A095396 mixed-pair question is now
settled in [modified-map descent](../problems/juggler_modified_juggler_descent.md).
Actual OE pairs drop by exactly one; formal equalities at squares do not
realize OE. This does not settle the other variants or longer trajectories.

**The lesson, and it cost a second sweep to learn.** The whole of this was
sitting in `juggler_oeis_neighbourhood.md` on an unmerged branch while a second
session ran the same search from scratch against the same mirror. Reading the
branch's dossier takes a minute; the sweep took an afternoon. Before searching
a database for what the laboratory already knows, read what the unmerged
branches already say --- `python tools/branch_drift.py` names them.

Kind: `CLOSE`. Dossier:
[oeis_neighbourhood](../problems/juggler_oeis_neighbourhood.md).
