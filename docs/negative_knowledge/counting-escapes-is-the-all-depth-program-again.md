# Counting escapes is the all-depth program again

Killed claim: counting escaping starts gives a premise for excluding divergent
orbits that is weaker and more reachable than the failure rate, because escapes
must grow while failures may sit in large-cycle basins.
Kill: escape can be arbitrarily slow. An escaping start above the verified floor
never enters it, so at every fixed depth it is a live start, and the only
depth-bounded premise is the existing live pressure. The natural quantitative
form, Ville's maximal inequality for the fair multiplier martingale
(`P(ever reach H) <= log y / log H`), needs fair parity counts at every depth an
orbit may use before climbing. A uniform first-moment bound on log-height is
equivalent to no escape and restates the target. The reduction itself is
kernel-checked: an escape rate above `3/8` excludes divergent orbits
(`no_escape_of_escape_rate`).
Kind: `REPARAMETERIZATION`.
Branch: [juggler_escape_rate](../problems/juggler_escape_rate.md).

Do not reopen as an escape-rate, hitting-height or log-height-moment premise, or
as a Ville bound at fixed depth. Reopen only with a growth invariant of escaping
orbits that is visible at bounded depth.
