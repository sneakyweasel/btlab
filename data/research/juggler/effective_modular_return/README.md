# Effective OOE modular-return checks

Regenerate summary.json with:

    python -m research.juggler_sequence.effective_modular_return

The report contains 22 exact scalar checks and a comparison of the selected
root-floor predicate with actual Juggler iteration for 32768 prefixes.
The test range is t=0,...,4095 for M=1,2,3,4,8,16,31,64.

No floating-point root or parity computation is used. The enormous analytic
bound is vacuous over this finite range; the report makes no experimental
rate claim. The universal analytic argument is the separate
[written proof](../../../../docs/theory/juggler_effective_modular_return_note.md),
not a consequence of these numerical checks.
