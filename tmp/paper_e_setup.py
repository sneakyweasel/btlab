"""One-time Paper E setup; canonical tools remain under tools/."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
builder = root / "tools/build_paper_e.py"
s = builder.read_text(encoding="utf-8")
s = s.replace("Paper D", "Paper E").replace("paper_d", "paper_e").replace("PAPER_D", "PAPER_E")
s = s.replace('"src/research/juggler_sequence/cycle_denominator_coupling.py",',
              '"src/research/__init__.py", "src/research/juggler_sequence/__init__.py",\n'
              '    "src/research/juggler_sequence/lean_paths.py",')
s = s.replace("    _pin_build_date()\n", "    _pin_build_date()\n    check_mathematics(root)\n")
s = s.replace('"status": "preprint; no external deposit performed",',
              '"status": "living preprint; independent review pending; no external deposit",')
builder.write_text(s, encoding="utf-8", newline="")
# Use the existing one-inch paper typography, retaining the subtitle.
template = (root / "tools/paper_c/article.tex").read_text(encoding="utf-8")
template = template.replace(r"\title{$title$}", r"\title{$title$\\[0.5em]{\large $subtitle$}}")
template = template.replace("pdftitle={$title$}", "pdftitle={$title$: $subtitle$}")
(root / "tools/paper_e/article.tex").write_text(template, encoding="utf-8", newline="")
# Paths and declaration names need breakable monospace in prose and table cells.
paper = root / "docs/theory/juggler_signed_collatz_note.md"
s = paper.read_text(encoding="utf-8")
tick = chr(96)
lines = s.splitlines()
inside = False
for i, line in enumerate(lines):
    if line.startswith("~~~"):
        inside = not inside
    if inside or line.startswith("~~~"):
        continue
    line = re.sub(r"(?<![\w/])(?:docs|data)/[\w/.-]+\.(?:md|json)", lambda m: tick+m[0]+tick, line)
    line = re.sub(r"\b(?:Problems\.)?(?:CollatzPadic|PreimageGrid|PreimageDomain|PreimageGrowth|"
                  r"PreimageCertificate12|PreimageBalance|BackwardMass|CollatzMoments)\.[A-Za-z0-9_]+",
                  lambda m: tick+m[0]+tick, line)
    # Short subsequent declaration names, such as a second table entry.
    line = re.sub(r"\b[a-z]+(?:_[a-z0-9]+)+\b",
                  lambda m: m[0] if (m.start() and line[m.start()-1] in "/"+tick)
                  else tick+m[0]+tick, line)
    lines[i] = line
paper.write_text("\n".join(lines)+"\n", encoding="utf-8", newline="")
