# Coded source mass is not ordinary reciprocal Collatz mass

The [exact code mass transport](../problems/juggler_code_mass_transport.md)
constructs the unique even-fibre conserved weight w(n) with n*w(n)->2.
Its minus-code pushforward nu satisfies nu(2B)=nu(B), but
nu({2^(d+1)})>=log(3) for every d>=0: the complete d-th even inverse
generation of 2 already contributes that much. Hence there is no finite
constant K with nu({q})<=K/q on all positive integer codes. This is a
concrete obstruction to substituting ordinary reciprocal code weights,
not a refutation of weighted transport or a fate-specific method.
Also H(16)=H(18)=8, but 16 has no odd Juggler predecessor while 18 has 7;
the code alone does not determine a physical target's odd production.
The source cutoff and the distribution within the code fibre must be
retained for such an argument. Written proofs and exact regression controls
are in the dossier; no termination or pressure bound is asserted.
The conservation law, both signed cutoff identities, and the 16/18
odd-production counterexample are now kernel-checked in
`CodeMassTransport.lean`. Infinite mass is handled as a supremum of
nonnegative finite cutoffs. This verifies the distinction without adding
an odd-production estimate. The sharp reciprocal comparison and uniqueness
remain written proofs (`J-code-mass-kernel-foundation`).

