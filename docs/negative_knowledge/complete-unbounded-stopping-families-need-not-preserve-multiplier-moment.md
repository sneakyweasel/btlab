# Complete unbounded stopping families need not preserve multiplier moment

The former Section 5.7 sentence in Paper C extended both fixed-depth
moment identities to every complete prefix-free family. The second
identity is false at unbounded stopping. All minimal descent certificates
form a prefix-free family with fair mass one, while their multiplier
moment is at most 3/4. The E certificate alone loses 1/4. This is
kernel-checked in `Problems/Juggler/CollatzMoments.lean`, using the
existing certificate recursion and survivor decay.
The [bridge dossier](../problems/juggler_collatz_bridge.md) gives the proof.
The coefficient shift and fixed-depth identities remain valid.
**CLOSE** the unqualified complete-family second-root claim;
do not infer a stopped expectation from Kraft equality alone.
The manuscript is corrected; Proposition 5.12 and the termination
thresholds are unchanged. Ledger: `J-collatz-complete-stopping-loses-moment`.

