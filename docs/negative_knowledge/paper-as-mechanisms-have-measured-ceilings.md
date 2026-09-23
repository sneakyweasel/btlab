# Paper A's mechanisms have measured ceilings

Killed claim: a bigger descent floor, a sharper per-length charge, or a
longer shape enumeration reaches "no nontrivial cycle".

**The floor route diverges.** Finance excludes \(L\) when
\(n_{\max}(L)\le N_0\), and along the convergents
\(n_{\max}(q_k)\log n_{\max}\approx 0.45\,q_k q_{k+1}\) — flat to within
a factor \(1.3\) over \(q_k=19\ldots176251\). \(q_{k+1}\) is unbounded,
so \(n_{\max}\) is. Every length needs its own floor. Raising \(N_0\)
buys \(\text{period}\asymp\sqrt{N_0\log N_0}\) (finance) or
\(\asymp\sqrt{N_0}\log N_0\) (walk charge) — square roots, not the
powers \(N_0^{0.59}\)/\(N_0^{0.69}\) a narrow fit suggests. Doubling the
period costs roughly quadrupling the floor, and no exponent helps,
because the target recedes. Any result that
fixes \(L\) and asks for a floor is a period bound, never a cycle
theorem.

**The shape route is exponential, and its law is empty where it
matters.** Section 3's exclusions are the only floor-free *and*
length-free family. Admissible shapes at the least odd count grow about
\(6\times\) per even letter: \(2651\) at \(e=7\) (Theorem 3.31's
frontier), \(1.1\cdot10^{13}\) at \(e=20\), against \(e=9515\) for the
first surviving length. But feasibility is not the real obstruction.
Theorem 3.26's law — the whole word expands, no proper odd-starting tail
does — is, after complementing tail to prefix, the anchor
\(3^{o_p}\ge2^{\lvert p\rvert}\) raised to \(1+\theta\). Its whole
strength over the anchor is the surplus. It kills \(41\%\) of shapes at
\(e=10\) (\(\Lambda\approx0.37\)) and **exactly none** at \(e=31\),
\(210\), \(389\) (\(\Lambda\le2.1\cdot10^{-3}\)) — at \(e=389\) the two
counts agree in all \(300\) digits. Surviving lengths have
\(\Lambda\in [3.6\cdot10^{-6},6.9\cdot10^{-5}]\).

**So finance and the run--suffix law fail for one reason.** Finance weakens as
\(\theta\to0\) because \(n_{\max}\sim1/\theta\); the run--suffix law
weakens as \(\theta\to0\) because it is the anchor tightened by
\(1+\theta\). They cannot be played against each other: the lengths where
one is weak are exactly the lengths where the other is. **Any method
whose strength is measured by the surplus is empty where a cycle could
be.** Do not open a direction whose kill criterion is a function of
\(\theta\).

**What is actually missing.** The only proved relation between minimum
and period runs one way: finance bounds \(n\log n\lesssim L^{\mu}\), and
\(\mu\ge2\) for every irrational, so even a perfect irrationality measure
leaves \(n\lesssim L^{2}\). Nothing bounds \(n\) *below* in terms of
\(L\) — the descent floor is a constant, and counting the \(L\) distinct
states gives no window, since a cycle's states are not confined to one.
Survivors sit at \(n\log n\asymp L^{2}\) — the ratio
\(n\log n/L^{2}\) lies in \([0.164,1.207]\) across all five certified
survivors, so the quoted \(n\approx L^{1.7}\) is the logarithm, not an
exponent below two — inside the band a one-sided bound cannot empty.
Reopen only on a lower bound for the minimum in terms of the period, or
an argument uniform over shapes. That first condition now carries a
number: \(n\gg L^{5.1163051}\) suffices unconditionally, and Dirichlet
makes \(n\gg L^{2}\) a hard floor no Diophantine input can go below
([juggler_cycle_wuwang_reduction](../problems/juggler_cycle_wuwang_reduction.md),
`J-cyclemin-closure-threshold`).
Kind: `REPARAMETERIZATION` / `PARK_STOP`.
Branch: [juggler_cycle_method_ceilings](../problems/juggler_cycle_method_ceilings.md).
