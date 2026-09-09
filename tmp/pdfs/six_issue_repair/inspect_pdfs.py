"""Locate repaired passages in generated review PDFs for visual QA."""

import json
import sys
from pathlib import Path

from pypdf import PdfReader

pdf = Path(sys.argv[1])
needles = sys.argv[2:]
reader = PdfReader(pdf)
matches = {needle: [] for needle in needles}
for number, page in enumerate(reader.pages, 1):
    content = " ".join((page.extract_text() or "").split())
    for needle in needles:
        position = content.casefold().find(needle.casefold())
        if position >= 0:
            matches[needle].append({"page": number, "excerpt": content[position:position + 260]})
print(json.dumps({"pdf": str(pdf), "pages": len(reader.pages), "matches": matches}, indent=2))
if not all(matches.values()):
    raise SystemExit("A requested repaired passage was not found in the PDF")
