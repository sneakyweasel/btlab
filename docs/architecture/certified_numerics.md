# Certified numerical arithmetic

The lab requires `python-flint>=0.9,<0.10`. Its Arb real balls enclose exact
values and propagate rounding error through arithmetic and transcendental
functions. Install with the normal editable-install command; `lab.py doctor`
checks the dependency. The first integration was run with python-flint 0.9.0
on Windows / Python 3.13.9.

The shared implementation is
[research_engine.intervals](../../src/research_engine/intervals.py).
It has no application imports. The
[Paper C audit](../../tools/check_paper_c_intervals.py) supplies the actual
production equations and rate formulas.

## Use and trust boundary

```python
from research_engine.intervals import ball, signed_evaluation, production_root

decision, evidence = signed_evaluation(lambda: ball(2).sqrt() - ball("7/5"))
assert decision == 1
root = production_root([(2, "1/3")])  # 2 * (1/3)**lambda = 1
print(root.as_dict())
```

- Supply integers, `Fraction`, or exact decimal/rational strings. Floats are
  rejected: the binary approximation to `0.1` is not the rational `1/10`.
- Construct every rounded intermediate inside the precision callback. The
  helper retries at 128, 256, ... up to 4096 bits and restores the previous
  context on success and failure. A zero-containing interval is unknown unless
  it is exactly zero. Nonfinite or unresolved results raise; they cannot pass.
- Reports preserve outward rational endpoints and a decimal display with its
  radius. Midpoints alone and decimal formatting are not certificates.
- Root certification requires positive coefficients and bases strictly between
  zero and one. This supplies continuity and strict decrease; certified signs
  at rational endpoints establish the unique root. Default width is at most
  `10^-24`. This helper is not a general-purpose root finder.
- FLINT uses a global precision context. Use separate processes for parallel
  evaluations that change it, rather than simultaneous Python threads.

Arb's arithmetic guarantee relies on its implementation and the expression
supplied. It is not a Lean kernel certificate. An interval evaluation does not
prove a distribution law, validate a model, bound an omitted infinite tail, or
justify replacing a global optimization by a sample grid. Existing evidence
labels remain in use: these finite expression checks are
**COMPUTATIONALLY VERIFIED**, with their exact domain stated.

API references: [python-flint's arithmetic and comparisons](https://python-flint.readthedocs.io/en/stable/general.html),
[Arb endpoints and error bounds](https://python-flint.readthedocs.io/en/stable/arb.html).

## Reproduce the Paper C certificate

```powershell
python tools/check_paper_c_intervals.py
python tools/check_paper_c_intervals.py --output data/research/juggler/paper_c_audit/intervals.json
python tools/lab.py test -- tests/research_engine/test_intervals.py tests/tools/test_paper_c_intervals.py
python tools/lab.py check --hashes
```

The first command prints without writing. The second explicitly writes a
[certificate](../../data/research/juggler/paper_c_audit/intervals.json) and its
[run provenance](../../data/research/juggler/paper_c_audit/intervals.research.json).
Provenance records the actual interpreter, dependency version, source hashes,
input manuscripts and Lean coefficient table. Tests independently compare the
V6 coefficients with Lean and enclose the paper's printed rounding intervals.
These are source consistency checks, not fresh Lean elaboration or axiom audits.

The certificate covers twelve finite production equations, the OOEE slack at
`5/8`, and forty integer rate crossings: five contagion regimes, two rate
formulas, and four odd-share caps. Every integer from `C=5` up to the first
crossing is checked. Root uncertainty is propagated into `1-lambda` in the
historical root-based regimes. An undecidable candidate stops the run.

## Effect on Paper C and its companions

The [current manuscript](../theory/juggler_fate_almost_all_note.md) and
[OOEE companion](../theory/juggler_ooee_contagion_note.md) retain their stated
theorems and review boundaries. The prepared paper is not revised by this audit.

| Expression | Certified value, shown approximately | Consequence |
|---|---|---|
| V6 root, lambda** | 0.492571544725 | Confirms the printed 0.4926 |
| Ideal E/OE root | 0.492657980115 | Confirms the printed 0.4927 |
| OOEE fixed-coefficient root, coefficients 1, 33/100, 11/100 | 0.626551756401 | Measures modest numerical headroom above 5/8; does not change the theorem |
| Limiting E/OE/OOEE model root, coefficients 1, 1/3, 1/9 | 0.632767141802 | Certifies the diagnostic model value; not an attained exponent |
| Fixed OOEE recurrence slack at 5/8 | 0.000888624213 | Independently confirms positivity; Lean already has the rational lower bound 11/50000 |

Using the written contagion exponent `lambda=5/8`, the required rate is strictly
greater than `3/8`. The certified least **integer** depth constants `C>=5` are:

| Odd-share cap q | KL / optimized pressure | Azuma |
|---|---:|---:|
| 1/2 | 16 | 16 |
| 11/20 | 34 | 34 |
| 3/5 | 168 | 175 |
| 31/50 | 1135 | 1201 |

Thus the sufficient examples `19` and `41` retained from the older V6 regime
can become `16` and `34` in a future Paper C revision using the written OOEE
result. These are stronger numerical instantiations of existing conditional
criteria. They still require the appropriate cylinder, one-sided, or pressure
hypothesis, its admissible error exponent, and the written OOEE theorem. They
do not establish any of those inputs. The fully formal baseline `100/203`
retains its existing constants, including `19` and `41`.

The audit does not certify the older transfer-matrix eigenvalue outputs such
as `0.8414`, infinite tails, uniform analytic error estimates, or the missing
arithmetic rates. No termination, cycle-exclusion, or fate-exclusion theorem
changes. Paper A already uses separate rational/interval checks; Papers B, D
and E gain access to the shared tool but have no results retagged by this run.

The next useful extension is a justified uniform error or tail bound needed by
an analytic argument, followed by interval evaluation of its constants. Merely
raising precision or certifying another model eigenvalue does not supply that
mathematical input.
