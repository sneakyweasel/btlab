from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]

def update(path, replacements):
    p = root / path
    s = p.read_text(encoding="utf-8")
    for old, new in replacements:
        if old in s:
            assert s.count(old) == 1, old[:100]
            s = s.replace(old, new)
        else:
            assert new in s, old[:100]
    temporary = p.with_name(p.name + ".publication-tmp")
    temporary.write_text(s, encoding="utf-8", newline="\n")
    temporary.replace(p)

update("docs/theory/juggler_fate_almost_all_note.md", [
    ("## Appendix C. A conditional strengthening", "## Appendix C. An earlier conditional strengthening"),
    ("*Depth constants.* The least integer values below use the three", "Theorem 5.19 additionally attains the written exponent 5/8, from\ncoefficients 1, 33/100 and 11/100 at scales 1/2, 3/4 and 9/16.\nIts exact certificate is in Section 5.9; the OOEE analytic input is\nnot yet completely formalized.\n\n*Depth constants.* The historical least integer values below use the three"),
    (r"(\lambda^{**}\), Theorem 1; elementary, audited)", r"(\lambda^{**}\), earlier finite-production route; elementary, audited)"),
])
# The quantitative theorem is separate from the selected qualitative audit.
update("docs/theory/juggler_signed_collatz_note.md", [
    ("This appendix proves Theorem 4.4. Its analytic proof is written mathematics;", r"This appendix proves Theorem 4.4. Write \(e(x)=\exp(2\pi i x)\)," + "\n" + r"\(s=1+2Mt\), \(u=\lfloor s^{9/2}\rfloor\), and" + "\n" + r"\(v=\lfloor s^{9/4}\rfloor\). Its analytic proof is written mathematics;"),
])
print("Finished historical-scope labels and quantitative notation.")
