# The Erdős--Turán route to the averaging lemma closes, and is thirty orders from useful

Built 19 September 2026 over most of a day, then superseded the same night
by a branch, `claude/latest-progress-summary-s011un`, merged into main on
20 September 2026. Recorded because it is re-derivable, it looks
like progress at every step, and nothing in the chain announces the problem.

**What it proves.** For every nonempty backward-closed \(A\) and fixed
\(\delta>0\), the fraction of \(A\)'s \(1/m\)-weight carried by fibres with
\(\lvert\sigma_m-\tfrac12\rvert\ge\delta\) is \(O_\delta(x^{-1/3})\). Five
links, all proved, no measured input: Paper C Lemma 2.1 gives that \(A\) is a
union of complete fibres; Lemma 4.2 gives low-share \(\Rightarrow\) resonant
for \(\delta\ge1/6\) and an Erdős--Turán plus Abel argument extends it below;
the resonant measure is exactly \(9C\,m^{-1/3}\); every production fibre
equidistributes \(\alpha\) because \(\theta_w=2^{a+b+1}/3^{b+1}\) is never an
integer; and both routes' rates are provably marginal, which suffices.

**Why it does not pay.** The constant is
\(\pi C_{ET}K^2\log(eK)/\delta\) with \(K\sim2/\delta\), so it goes like
\(\delta^{-3}\) and the crossover like \(\delta^{-9}\) --- fitted,
\(x\approx10^{5}\delta^{-9}\). But the bootstrap needs \(\delta\to0\) to push
the effective share to \(1/2\), and the two pull against each other:

| target two-production root | \(\delta\) | crossover \(x\) |
|---|---|---|
| \(0.326121\), unconditional today | \(1.7\times10^{-1}\) | \(1.0\times10^{12}\) |
| \(0.400\) | \(9.3\times10^{-2}\) | \(3.3\times10^{14}\) |
| \(0.4926=\lambda^{**}\) | \(5.8\times10^{-5}\) | \(2.0\times10^{44}\) |
| \(0.492658=\lambda_{\text{ideal}}\) | \(0\) | not attainable at any \(x\) |

So "two productions at the mean share reach \(\lambda^{**}\)" is true about
coefficients and false about anything achievable. Selberg--Vaaler removes
\(C_{ET}\) from \(K\) and buys \(85\times\) on the constant at
\(C_{ET}=4\) --- but only \(1.1\times\) at \(C_{ET}=1\), so what it buys is
not having to know the constant, not sharpness.

**And the question dissolves, which is the part worth carrying.** The route
that replaced this one --- merged into main from
`claude/latest-progress-summary-s011un` on 20 September 2026, and recorded as
`J-oe-poor-fiber-tail` --- proves the decay by one inequality at
every convergent denominator,
\(\lvert G_m/H_m-\tfrac12\rvert\le4\lVert q\alpha_m\rVert+\tfrac5{2q}+3.77q/H_m\),
with no exponential sum. Its observation is that \(P\) has **finite total
logarithmic mass** --- verified independently, density \(\sim m^{-1/3}\) and
the sum converges to about \(1.3\). So there is nothing to plant: any set's
weight on \(P\) is bounded by a constant while its own weight grows, and the
conclusion holds for **every set of integers**, with no backward closure, no
fibre equidistribution and no rate combination.

**The lesson for the next attempt.** The adversarial framing --- "could a
backward-closed \(A\) concentrate where the argument is silent?" --- is what
sent this route through Erdős--Turán. It is the wrong question, and the
measurements that answer it were in hand from the first hour: a density
falling like \(m^{-1/3}\) is a convergent sum, and a convergent sum cannot be
concentrated on. Before building machinery to bound a set's weight somewhere,
integrate the density and see whether the somewhere has any room in it.
