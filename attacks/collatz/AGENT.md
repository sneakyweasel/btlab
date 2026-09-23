# Signed Collatz agent guide

Collatz and Juggler are both active research programmes. The Python packages
`research.collatz`, `research.syracuse` and `research.collatz_finite_descent`
cover different formulations of the Collatz work; they are not independent labs.

## Start at the exact object

- [Collatz mathematics](../../docs/collatz_mathematics.md) maps the basic objects.
- [Lean module map](../../formal/Problems/Collatz/README.md) identifies the current
  formal statements and their import paths.
- [Paper D](../../docs/theory/collatz_3n_minus_1_m_cycles_note.md) treats negative
  Collatz m-cycles; [Paper E](../../docs/theory/juggler_signed_collatz_note.md)
  compares Juggler with the signed maps.
- [Fibre-mass dossier](../../docs/problems/collatz_fibre_mass.md),
  [coefficient proof map](../../docs/theory/collatz_fibre_mass_lean_note.md),
  [actual-mass proof map](../../docs/theory/collatz_actual_fibre_mass_lean_note.md),
  [generation criterion](../../docs/theory/collatz_generation_mass_lean_note.md),
  and [negative continuation](../../docs/theory/collatz_negative_generation_mass_lean_note.md)
  distinguish coefficient identities, actual reciprocal mass and conditional
  generation-series conclusions. Follow their latest continuation links.

Use formalpedia to locate a declaration and inspect its full hypotheses:

```powershell
python tools/formalpedia.py search "generation mass" --namespace Problems.Collatz
python tools/formalpedia.py show Problems.Collatz.PreimageCertificate12.ancestor_density_21_25
python tools/lab.py run cli.main collatz --help
```

## Scope and mathematical boundaries

Specify the sign and whether a result concerns the one-step shortcut or the
odd accelerated map. Use the source definition for valuation, divisibility and
domain conventions. Keep the exact distinction between natural integers,
2-adic codes, finite words, and realized orbits.

The strict-grid ancestor theorem and fibre/generation results do not prove
termination. An exact coefficient identity does not remove an open coefficient
divergence premise. A Juggler coding identity does not automatically transfer
integer realization, backward density or reciprocal-mass growth.
Search [negative knowledge](../../docs/negative_knowledge.md) before attempting
those transfers; read the chosen proof map rather than relying on an older
journal entry. Do not reopen uniform finite-weight reproduction or the
uncorrected residue-negation height argument.

## Files and verification

| Work | Source and tests |
|---|---|
| Signed Collatz Python | `src/research/collatz/`, `tests/research/collatz/` |
| Syracuse experiments | `src/research/syracuse/`, `tests/research/syracuse/` |
| Finite descent | `src/research/collatz_finite_descent/`, `tests/research/collatz_finite_descent/` |
| Formal results | `formal/Problems/Collatz/`, imported by `formal/Problems.lean` |
| Shared formal results | `formal/BTCalculus/` and the retained arithmetic libraries |
| Claims and failed routes | `docs/theory/theorem_ledger.json`, `docs/negative_knowledge.md` |

Keep application imports under `research.*`; do not add a top-level `collatz`
package or compatibility re-export. Register a named result in the claim ledger
and its proof map. Document public Lean names and keep exact hypotheses visible.
For a new research direction use the laboratory triage and dossier template.

```powershell
python tools/lab.py test tests/research/collatz tests/research/syracuse tests/research/collatz_finite_descent
python tools/lab.py build
python tools/lean_style.py
python tools/render_theorem_ledger.py --check
```

Finite certificates and bounded searches establish only their stated range.
Update executable axiom audits when a paper's public theorem surface changes.
Keep publication kits synchronized through their builders and release gates.
