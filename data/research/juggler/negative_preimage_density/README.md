# Signed preimage-density certificate

`grid_k12_certificate.json` contains one positive integer weight for each
residue `3*i+1` modulo `3^12`, in increasing order. The exact grid rate is
`5059/5000`; weights lie between `7307142888` and `1000000000000`.
The recorded floating-point exponent and slack are diagnostics only.

The weights were found independently by a damped Collatz–Wielandt iteration
of the strict-grid production operator, starting from all ones, normalizing
the maximum to one after each step, and rounding at scale `10^12`. The first
successful table occurred after 62 iterations. Every final inequality is
checked using integers, so the solver and rounding are outside the proof.

`verify_grid_certificate` in the existing probe checks all 177147 rows
independently. `python tools/generate_signed_grid_certificate.py --check`
verifies that the five generated Lean files reproduce this exact table and
its finite checks. Omitting `--check` regenerates those files.

Lean stores the table in a balanced tree with short lists at its leaves.
Four check modules divide the 177147 rows into blocks of 256; all use kernel
reduction. `PreimageCertificate12.lean` assembles the checks with the actual
signed inverse-tree induction. Its `ancestor_density_21_25` proves, for
every positive target a not divisible by 3, that eventually
`X^21 <= ancestorCount(a,X)^25` for every natural cutoff X.

`summary.json` also retains the old homogeneous residue-model comparison.
Those numerical model values are not the certificate. The proof uses the
exact grid shifts 100, 79, and 129 and includes the signed height correction.
