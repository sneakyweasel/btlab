# The cylinder bias energy is collapse-dominated at every computable scale

**CLOSE (the energy route of Paper C Section 10(d) as a numerical
hypothesis).** The bias energy `sum_w D(w)^2`, `D(w) = #[wO] - #[w]/2`,
over the odd starts of `(y, 2y]`, computed exactly by enumeration to
depth 30 at `y = 10^4..10^7`
([cylinder energy, measured](../problems/juggler_cylinder_energy_measure.md)),
reaches its
worst-case value `sum_w #[w]^2 / 4` by depth 16-22 over all words (the
absorbed cylinders of `J-absorbed-cylinder`, in numbers) and by depth
16-20 over the `L(y)`-bad words as well, on cylinders of up to 11939
members. The mechanism inside the bad words is collapse: a bad word
whose walk dips near `-L(y)` has contracted the whole scale onto a
bounded value above the floor (three even letters take `n` to about
`n^{27/64}`), and its cylinder's later letters are the deterministic
orbit of that value; at depth 20 the largest bad cylinders are single
fibers of one value (`243` consecutive odd starts with
`J^20 = 2119345842` at `10^6`). The second moment is dominated by a few
such atoms while the violating mass is small in the dense window
(`0.05` of the bad mass at depth 10, `10^7`) and a constant `0.42-0.49`
in the collapse regime. The Lean reduction `Energy.energy_implies_conjecture`
(`FateEnergyAtoms.lean`) stands; its hypothesis `Energy.EnergyBound`
has no numerical support and, with the constants of the reduction, is
met by fair splitting only beyond `10^{124}`. Do not reopen as a larger
enumeration, a sampled run at `10^{20}`, a different normalisation of
the second moment, or an all-word energy. The collapsed-fiber
construction (a bad word of depth `d(y)` whose cylinder is one fiber
of a bounded value) was assessed at triage and does not refute
`H(C, A)` or `H_q(C, A)` for large `y`: an early dip cannot stay bad
to depth `d(y)` because entrance times are bounded on bounded sets of
values, and a late dip's fiber is shared among the many backward paths
of its value, whose parity words are diverse, so each bad word sees
many values of both parities. What that leaves is the equidistribution
of backward-path parity words at growing depth, Appendix C's question;
do not reopen the construction as a refutation route, and do not open
a branch for it without a new analytic idea.
Members: cylinder_energy_measure.

