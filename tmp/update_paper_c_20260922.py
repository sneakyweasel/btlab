from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def read(name):
    return (ROOT / name).read_text(encoding="utf-8")

def put(name, text):
    (ROOT / name).write_text(text, encoding="utf-8", newline="\n")

def sub(s, old, new):
    assert s.count(old) == 1, (old[:90], s.count(old))
    return s.replace(old, new)

name = "docs/theory/juggler_fate_almost_all_note.md"
s = read(name).replace("date: 21 September 2026", "date: 22 September 2026")
abstract = r"""The Juggler map sends an even positive integer to the integer part of
its square root and an odd positive integer to the integer part of
its three-halves power. We prove that every nonempty set \(A\) of
positive integers closed under taking preimages satisfies
\(\sum_{n\in A,\,n\le x}1/n\ge c(\log x)^{5/8}\) for all sufficiently
large \(x\). Thus any realized cycle basin or nonempty class of
unbounded orbits must have this divergent logarithmic mass. Three
disjoint actual predecessor families, with initial words E, OE and
OOEE, supply the recursion. The OOEE input is an AI-assisted written
analytic proof, included in Appendix E, pending independent review
and complete Lean verification.

The earlier two-production argument remains a separate, fully
machine-checked baseline for every \(0<\lambda\le100/203\). Its
poor-fiber tail needs no exponential sums. For the stronger exponent
\(5/8\), Lean checks the recurrence assembly with the actual OOEE
production bound explicit; OE and the main mixed-frequency estimates
are proved separately. We distinguish that conditional formal result
from the complete written argument.

For a fixed verified target \([1,N_0]\), universal termination is
equivalent to an eventual-entry statement: all but
\(O(y(\log y)^{-e})\) odd starts in \((y,2y]\) enter that target,
for some \(e>3/8\). The rate itself remains unproved. Parity-cylinder,
live-pressure and scale-averaged pressure bounds are sufficient
arithmetic inputs; none is established here. The unconditional Lean
baseline gives the rate threshold \(103/203\). Earlier finite-production
and localized-discrepancy arguments are retained with their original
scope, and the numerical experiments remain observations. Neither
universal termination nor exclusion of every nontrivial cycle or
unbounded orbit is established.

"""
a = s.index("## Abstract\n") + len("## Abstract\n\n")
b = s.index("**2020 Mathematics Subject Classification:")
s = s[:a] + abstract + s[b:]
s = sub(s, "explicit exponent, by a downward recursion over two exact\nproductions and the finite composites in Appendix D.", "explicit exponent, by a downward recursion over the three actual\nproductions E, OE and OOEE (Section 5.9 and Appendix E). The\ntwo-production proof of Section 5.8 supplies the fully formal baseline.")
s = sub(s, r"\(0<\lambda<\lambda_{\mathrm{ideal}}\). This excludes no fate; it fixes the", r"\(0<\lambda\le5/8\). This excludes no fate; it fixes the")
s = sub(s, r"\([1,N_0]\), for some \(e>1-\lambda_{\mathrm{ideal}}\approx0.5073\) (Theorem 3). The", r"\([1,N_0]\), for some \(e>3/8\) (Theorem 3). The")
s = sub(s, r"and backward-closed, and let \(0<\lambda<\lambda_{\mathrm{ideal}}\approx0.4927\)," + "\n" + r"the root of \(2^{-\lambda}+\tfrac13(\tfrac34)^\lambda=1\).", r"and backward-closed, and let \(0<\lambda\le5/8\).")
s = sub(s, "(Theorems 5.3 and 5.18,\nCorollaries 5.4, 5.5.)\n\nThe exponent has two proofs.", "(Theorem 5.19 and its dyadic consequence.)\n\nThe new endpoint uses Appendix E's written OOEE estimate. Its complete\nanalytic formalization and independent review remain outstanding. The\nfully machine-checked baseline remains 100/203. The two earlier routes\nare retained with their original exponents, as follows.")
# The surviving paragraph needs the old limiting root defined locally.
s = sub(s, r"reaches every \(\lambda<\lambda_{\mathrm{ideal}}\). That route is formalized", r"reaches every \(\lambda<\lambda_{\mathrm{ideal}}\), where" + "\n" + r"\(2^{-\lambda_{\mathrm{ideal}}}+\tfrac13(3/4)^{\lambda_{\mathrm{ideal}}}=1\)" + "\n" + r"and \(\lambda_{\mathrm{ideal}}\approx0.4927\). That route is formalized")
s = sub(s, r"(ii) for some \(0<\lambda<\lambda_{\mathrm{ideal}}\), the starts", r"(ii) for some \(0<\lambda\le5/8\), the starts")
s = sub(s, r"\(o((\log x)^{\lambda})\); (iii) for some \(e>1-\lambda_{\mathrm{ideal}}\approx0.5073\)" + "\n(the threshold \\(103/203\\) is machine-checked)", r"\(o((\log x)^{\lambda})\); (iii) for some \(e>3/8\)" + "\n(the unconditional Lean baseline is \\(103/203\\))")
s = sub(s, r"whenever its displayed rate exceeds \(1-\lambda_{\mathrm{ideal}}\); the" + "\n" + r"constants \(C\) below are those of the threshold \(1-\lambda^{**}\)," + "\nwhich the new threshold leaves unchanged:", r"whenever its displayed rate exceeds \(3/8\), using the written" + "\n" + r"Theorem 5.19. The constants \(C\) below are retained sufficient" + "\n" + r"choices from the earlier threshold \(1-\lambda^{**}\); they are" + "\nnot asserted to be optimal for the stronger theorem:")
s = sub(s, "needs among its open questions — the exponent of Theorem 1 improves to", "needs among its open questions — the earlier two-production exponent improves to")
s = sub(s, "Nothing in Sections 2--12 depends on Appendix C.", "This conditional comparison is now weaker than the written Theorem 5.19.\nNothing in Sections 2--12 depends on Appendix C.")
s = sub(s, r"for every \(0<\lambda<\lambda_{\mathrm{ideal}}\).", r"for every \(0<\lambda\le5/8\), with the review boundary of Appendix E.")

section = r"""### 5.9 Three actual productions and exponent 5/8

This section gives the strongest written contagion result. The
analytic poor-fiber estimate used here is proved in Appendix E;
independent review and complete formal verification of that estimate
remain outstanding. The earlier Section 5.8 supplies the unconditional
Lean baseline and the positive seed needed below.

**Theorem 5.19 (three-production contagion).** Every nonempty
backward-closed set \(A\) of positive integers satisfies
\[
\sum_{n\le X,\ n\in A}\frac1n\ge K(\log X)^{5/8}
\qquad(X\ge X_0)
\tag{5.11}
\]
for some \(K>0,X_0\). The same conclusion holds for each realized
fate class. The theorem is a written proof; its formal assembly
retains the actual OOEE production inequality as a hypothesis.

*Proof.* Put
\[
a(n)=n+(n\bmod2),\quad w(n)=\log\frac{a(n)+1}{a(n)-1},\quad
F(t)=\sum_{n\le\lfloor e^t\rfloor,\ n\in A}w(n).
\]
For positive integers, \(1/n\le w(n)\le4/n\). Let
\(S_E(t),S_{OE}(t),S_{OOEE}(t)\) be the corresponding weighted
masses of starts in \(A\), below \(\lfloor e^t\rfloor\), with
the indicated actual initial words. The three families are disjoint.
Exact even-fiber conservation gives, for \(t\ge8\),
\[
F(t/2-4)\le S_E(t).
\]
The OE poor-fiber theorem of Section 5.8, converted to this weight,
and Appendix E's OOEE theorem give constants \(C,T\) such that
\[
\frac{33}{100}F(3t/4-4)\le S_{OE}(t)+C,\qquad
\frac{11}{100}F(9t/16-4)\le S_{OOEE}(t)+C
\quad(t\ge T).
\tag{5.12}
\]
Here all cutoffs concern actual starts. An OE predecessor of \(m\)
has \(n^3<(m+1)^4\); an OOEE predecessor has
\(n^9<64(m+1)^{16}\). Since \(m+1\le2m\), the target
cutoffs \(m\le e^{3t/4-4}\) and \(m\le e^{9t/16-4}\)
place their sources below \(e^t\). Distinct target fibers are
disjoint, and backward closure puts their sources in \(A\).

For completeness, the weighted OE coefficient follows from
\(H_m=(2/3)m^{1/3}+O(1)\), source weight
\(2m^{-4/3}(1+O(1/m))\), and target weight
\(2m^{-1}(1+O(1/m))\). The actual fiber ratio is
\((2/3)\sigma_m+O(m^{-1/3})\). Outside a poor set of finite
reciprocal mass it exceeds \(33/100\), after a finite initial
segment is removed. The removed target weight is bounded independently
of \(A\) and the cutoff. The OOEE coefficient is Appendix E's
arbitrary-target consequence with \(\eta=1/900\), since
\(1/9-1/900=11/100\). This proves (5.12), including its uniform
additive loss. The weighted OE step also has a separate Lean proof.

Disjointness now yields
\[
F(t)\ge F(t/2-4)+\frac{33}{100}F(3t/4-4)
                  +\frac{11}{100}F(9t/16-4)-2C.
\]
Let \(G(t)=F(t-16)-5C\). For each
\(r\in\{1/2,3/4,9/16\}\),
\(rt-16\le r(t-16)-4\). Monotonicity, and the coefficient
sum \(36/25\), therefore give eventually
\[
G(t)\ge G(t/2)+\frac{33}{100}G(3t/4)
                  +\frac{11}{100}G(9t/16).
\tag{5.13}
\]
The constant remainder is \(5C(36/25-1)-2C=C/5\ge0\).
Section 5.8 implies \(F(t)\to\infty\), so \(G\) has a
positive seed on a sufficiently late compact interval. Exact rational
comparisons, obtained by taking eighth powers, give
\[
2^{-5/8}\ge\frac{648}{1000},\quad
(3/4)^{5/8}\ge\frac{835}{1000},\quad
(9/16)^{5/8}\ge\frac{697}{1000}.
\]
Their weighted sum is at least \(50011/50000>1\).
The recursion lemma with zero errors gives \(G(t)\ge Kt^{5/8}\).
Evaluate at \(t=\log X\) and use the weight comparison to
obtain (5.11). \(\square\)

**Dyadic consequence.** There is \(c>0\) such that infinitely
many dyadic intervals \((y,2y]\) contain at least
\(cy(\log y)^{-3/8}\) members of \(A\). Otherwise their
reciprocal masses are eventually at most
\(c(\log y)^{-3/8}\). Summing over \(y=2^k\) up to \(X\)
bounds the total by a constant times \(c(\log X)^{5/8}\),
plus a fixed initial mass. Choosing \(c\) below the constant in
(5.11) is a contradiction. Smaller positive exponents follow by
weakening (5.11). This proves all clauses of Theorem 1; the dyadic
consequence at this new exponent is written, not separately audited in Lean.

**Formal boundary.** `FateOOEEAssembly` proves disjointness, the
even cutoff, the shifted recursion, the rational certificate and the
contagion and Tao implications. `FateOEWeighted` proves the OE input,
including a uniform error at most 6 when converting its finite
weighted sums to twice reciprocal mass. The strengthened implication
still assumes `OOEEProductionBound`. The original mixed-mode
cancellation is proved in `OOEEMixedModes`; a fixed finite frequency
family has uniform constants. The remaining analytic assembly in
Appendix E is not thereby certified. These supplementary modules have
their own audits; the historical Paper C barrel and its 473 recorded
reports retain their earlier scope.

"""
s = sub(s, "## 6. Odd generation and the exact first-letter decomposition", section + "## 6. Odd generation and the exact first-letter decomposition")
# Strengthen Section 7 by the new total-mass theorem, preserving its proof.
a, b = s.index("## 7."), s.index("## 8.")
part = s[a:b]
part = part.replace(r"1-\lambda_{\mathrm{ideal}}\approx0.5073", "3/8")
part = part.replace(r"1-\lambda_{\mathrm{ideal}}", "3/8")
part = part.replace(r"\lambda_{\mathrm{ideal}}", "5/8")
part = part.replace("Theorem 5.3", "Theorem 5.19")
part = part.replace("Theorem 5.18", "Theorem 5.19")
part = part.replace("## 7.", "## 7.", 1)
part += "\nThe strengthened conclusions of this section use Appendix E's written\nanalytic proof. The unconditional Lean specialization remains at\n100/203 for contagion and at rates greater than 103/203; the 5/8\nassembly retains its actual OOEE production hypothesis.\n\n"
s = s[:a] + part + s[b:]
s = sub(s, "| Numerical experiments (Section 11) | observation |", "| Theorem 5.19, Theorem 1 at 5/8, and Theorems 3 and 7.2--7.3 at e > 3/8 | written proof using Appendix E; Lean assembly conditional on the actual OOEE production bound; independent analytic review outstanding |\n| OOEE mixed modes on the actual short source interval | separate Lean proof in OOEEMixedModes; pure slow modes and final poor-target assembly are outside that result |\n| Numerical experiments (Section 11) | observation |")
# Recast the conclusion without removing the still useful baseline argument.
a, b = s.index("## 12. Conclusions and open estimates"), s.index("## Appendix A.")
s = s[:a] + r"""## 12. Conclusions and open estimates

The strongest written contagion exponent is now \(5/8\), from
the three actual productions E, OE and OOEE. Appendix E contains the
new analytic proof; Section 5.9 proves its weighted assembly and
physical cutoffs. Independent review and complete analytic Lean
verification remain outstanding. The two-production exponent
\(100/203\) remains the fully machine-checked baseline.

One sufficient remaining target is
\[
\#\{n\text{ odd in }(y,2y]:\tau(n)>\lceil CL(y)\rceil\}
 \ll y(\log y)^{-e},\qquad e>3/8,
\]
for a fixed \(C\) and all sufficiently large \(y\). This would
imply universal termination by Theorem 7.2. The unconditional Lean
baseline gives the same implication for \(e>103/203\). No such
arithmetic rate is proved. Universal termination alone gives no
uniform stopping-time bound here: Theorem 7.3 concerns eventual entry.

Live pressure and its scale-averaged form are sufficient routes to
the missing rate. The no-momentum hypothesis supplies a sufficient
condition for the pressure bound. The earlier localized Appendix C
and ideal-production models retain their stated hypotheses; they
do not limit the new written exponent or establish further production
inequalities. No nontrivial cycle or unbounded orbit is excluded.

""" + s[b:]
# Include the complete written short-interval proof in the paper itself.
extra = read("docs/theory/juggler_ooee_poor_fibre_tail_note.md").split("## 1. Statement and exact objects", 1)[1].split("## 7. Audit and formalization boundary", 1)[0]
extra = "## 1. Statement and exact objects" + extra
extra = re.sub(r"^## (\d+)\. (.+)$", lambda m: f"### E.{m[1]} {m[2]}", extra, flags=re.M)
extra = re.sub(r"^### (\d+)\.(\d+) (.+)$", lambda m: f"#### E.{m[1]}.{m[2]} {m[3]}", extra, flags=re.M)
extra = re.sub(r"\\tag\{(\d+)\}", lambda m: r"\tag{E." + m[1] + "}", extra)
extra = re.sub(r"\((\d+)\)", lambda m: "(E." + m[1] + ")", extra)
extra = extra.replace("**Theorem 1 (poor-fibre tail).**", "**Theorem E.1 (poor-fiber tail).**").replace("Theorem 1 and", "Theorem E.1 and")
extra = extra.split("This is an actual two-consecutive-odd production", 1)[0]
extra += "The physical source cutoffs and three-production recursion are proved\nin Section 5.9. This analytic input is a written proof pending independent\nreview. Its main mixed-mode estimate has a separate Lean proof, but the\ncomplete poor-target and production conclusions remain outside the\nunconditional formalization.\n\n"
s = sub(s, "## Acknowledgments and use of AI", "## Appendix E. Actual OOEE poor-fiber tail\n\nThis appendix supplies the written analytic input to Theorem 5.19.\nIt derives the short-interval estimate needed for the actual nested\nfloors, with all four parity guards. It does not invoke Paper B's\nglobal estimate as an unproved localization.\n\n" + extra + "## Acknowledgments and use of AI")
s = sub(s, "This is version 1.1.1 of Paper C, of 21 September 2026. It is a preprint, it has\nnot been refereed, and it is not deposited; it revises the acknowledgments and the\nreference DOIs of version 1.1.0 and changes nothing mathematical.", "This is version 1.2.0 of Paper C, of 22 September 2026. It is a preprint,\nhas not been refereed, and is not deposited. It adds the written OOEE\npoor-fiber proof, contagion at 5/8, the sufficient rate threshold 3/8,\nand an updated proof-status map. The fully machine-checked baseline\nremains 100/203. It also retains the corrected distinction between\nfinite and unbounded stopping-word moments in Section 5.7.")
put(name, s)
print("Updated Paper C's main statements, full OOEE proof, assembly, and scope.")
