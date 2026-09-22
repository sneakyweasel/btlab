"""Bounded editorial migration; exact source replacements prevent silent drift."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def read(name):
    return (ROOT / name).read_text(encoding="utf-8")


def write(name, text):
    (ROOT / name).write_text(text, encoding="utf-8", newline="\n")


def replace(text, old, new):
    assert text.count(old) == 1, (old[:100], text.count(old))
    return text.replace(old, new)


def appendix(note, start, end, letter):
    text = read(note).split(start, 1)[1].split(end, 1)[0]
    text = start + text
    text = re.sub(r"^## (\d+)\. (.+)$", lambda m: f"### {letter}.{m[1]} {m[2]}", text, flags=re.M)
    text = re.sub(r"^### (\d+)\.(\d+) (.+)$", lambda m: f"#### {letter}.{m[1]}.{m[2]} {m[3]}", text, flags=re.M)
    text = re.sub(r"\\tag\{(\d+)\}", lambda m: r"\tag{" + letter + "." + m[1] + "}", text)
    # Parenthesized numbers in these excerpts refer to their numbered equations.
    text = re.sub(r"\((\d+)\)", lambda m: "(" + letter + "." + m[1] + ")", text)
    return text


# Paper E: preserve the completed qualitative theorem and add a distinct
# quantitative theorem, explicitly outside the selected 49-declaration audit.
name = "docs/theory/juggler_signed_collatz_note.md"
s = read(name).replace("Version 0.5.0", "Version 0.6.0").replace("version 0.5.0", "version 0.6.0")
s = replace(s, "On the positive integers, we prove that every", "For the fixed word OOE, we also give an explicit counting error and a\nuniform polynomial first-witness bound in the modulus; this quantitative\nextension is a written proof pending independent review and full Lean\nverification. On the positive integers, we prove that every")
s = replace(s, "The finite certificate is checked with exact integers", "Theorem 4.4 and Appendix C are a separate quantitative extension with a\nwritten proof. They use the explicitly cited derivative estimate [AR24];\ntheir complete counting and witness conclusions are not in the selected\nLean audit. The finite certificate is checked with exact integers")
quant = r"""### 4.1. Effective returns for the word OOE

The preceding results fix the modulus before taking a limit. The next
result retains its dependence explicitly, for one fixed word.
For integers \(M,T\ge1\), put \(s_t=1+2Mt\) and
\[
A_M(T)=\#\{0\le t<T:s_t\ge16,\quad
 \lfloor s_t^{9/2}\rfloor\equiv0\pmod2,\quad
 \lfloor s_t^{9/4}\rfloor\equiv1\pmod{2M}\}.
\]

**Theorem 4.4 (effective OOE returns; written proof).** For every
\(M,T\ge1\),
\[
\begin{split}
\left|A_M(T)-\frac{T}{4M}\right|
&\le\left[5+128M^{1/4}\left(3+\frac{\log T}{16}\right)^2\right]T^{63/64}+8\\
&\le2^{14}M^{1/4}T^{127/128}.
\end{split}
\tag{4.6}
\]
In particular, some \(0\le t<2^{2176}M^{160}\) gives a start
\(n=s_t^2<2^{4354}M^{322}\) whose actual three-step itinerary is
OOE, whose intermediate states are at least \(n\), and whose exit
is greater than \(n\) and congruent to \(n\equiv1\pmod{2M}\).
At \(T=2^{2176}M^{160}\), there are at least \(T/(8M)\)
such parameters.

*Proof.* Appendix C proves the uniform Fourier estimates, the finite
half-open box bound, their dyadic assembly, and the witness extraction.
The box is \([0,1/2)\times[1/(2M),1/M)\); its area is \(1/(4M)\),
including when \(M=1\). The exact construction of Theorem 4.1 with
\(a=2,b=1\) converts these parameter conditions into the asserted
orbit conditions. \(\square\)

The constants are theoretical bounds, not practical search budgets.
This OOE word has periodic-word denominator one; Theorem 4.4 does
not make the large-denominator family of Theorem 4.1 effective.
Its written analytic proof has passed an internal audit, but independent
review and complete quantitative Lean verification remain outstanding.

"""
s = replace(s, "## 5. A signed ancestor-count theorem", quant + "## 5. A signed ancestor-count theorem")
extra = appendix("docs/theory/juggler_effective_modular_return_note.md", "## 2. Explicit analytic input", "## 6. Verification and value", "C")
extra = extra.replace("(C.1)", "(4.6)").replace("(C.2)", "the parameter bound in Theorem 4.4").replace("(C.3)", "the start bound in Theorem 4.4")
extra = extra.replace("J. Arias de Reyna,\n[*Explicit van der Corput's d-th derivative estimate*, v1](https://arxiv.org/html/2407.02094v1),", "J. Arias de Reyna [AR24],")
s = replace(s, "## References", "## Appendix C. Quantitative OOE proof\n\nThis appendix proves Theorem 4.4. Its analytic proof is written mathematics;\nthe selected 49-declaration audit covers the earlier qualitative results.\nThe finite Fejer estimate has a separate kernel-checked proof, but that\ndoes not certify the complete quantitative theorem.\n\n" + extra + "\n## References")
s += "\n[AR24] J. Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*,\npreprint, version 1, 2024, Theorem 11 and Table 1.\n[arXiv:2407.02094v1](https://arxiv.org/abs/2407.02094v1).\n"
write(name, s)

# Version facts are local release facts; existing external deposit facts survive.
for paper, version in [("a", "1.2.0"), ("b", "1.1.1"), ("c", "1.2.0"), ("e", "0.6.0")]:
    name = f"docs/theory/paper_{paper}_zenodo.json"
    data = json.loads(read(name))
    data["version"] = version
    write(name, json.dumps(data, ensure_ascii=False, indent=2) + "\n")

for paper in "abce":
    name = f"tools/build_paper_{paper}.py"
    s = read(name)
    s = re.sub(r'^_SOURCE_DATE_EPOCH = "\d+".*$', '_SOURCE_DATE_EPOCH = "1790035200"  # Local revision, 22 September 2026', s, flags=re.M)
    if paper == "e":
        s = s.replace('VERSION = "0.5.0"', 'VERSION = "0.6.0"')
        s = s.replace('    "docs/theory/paper_e_counting_corollaries_note.md",', '    "docs/theory/paper_e_counting_corollaries_note.md",\n    "docs/theory/juggler_effective_modular_return_note.md",\n    "docs/theory/juggler_effective_modular_return_audit.md",\n    "docs/theory/finite_fejer_box_note.md",\n    "literature/arias-de-reyna-2024-explicit-derivative-estimate.json",')
    write(name, s)
name = "tools/build_paper_b_kit.py"
write(name, read(name).replace("STAMP = (2026, 9, 20, 0, 0, 0)", "STAMP = (2026, 9, 22, 0, 0, 0)"))
print("Updated E manuscript and local version metadata/build epochs.")
