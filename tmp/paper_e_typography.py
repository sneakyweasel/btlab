from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
path = root / "docs/theory/juggler_signed_collatz_note.md"
tick = chr(96)
s = path.read_text(encoding="utf-8").replace(tick, "")
lines = s.splitlines()
inside = False
for i, line in enumerate(lines):
    if line.startswith("~~~"):
        inside = not inside
    if inside or line.startswith("~~~"):
        continue
    line = re.sub(r"(?<![\w/])(?:docs|data)/[\w/.-]+\.(?:md|json)", lambda m: tick+m[0]+tick, line)
    if line.startswith("|"):
        line = re.sub(r"\b(?:[A-Z][A-Za-z0-9]*\.)?[a-z]+(?:_[a-z0-9]+)+\b",
                      lambda m: tick+m[0]+tick, line)
    lines[i] = line
path.write_text("\n".join(lines)+"\n", encoding="utf-8", newline="")
