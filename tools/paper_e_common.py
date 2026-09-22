"""Shared dependency inventory for the living Paper E release and its audit."""
from __future__ import annotations

import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "docs/theory/juggler_signed_collatz_note.md"
BARREL = "formal/Problems/JugglerCollatzPaper.lean"
AXIOMS = "formal/AxiomCheckJugglerCollatzPaper.lean"
REPORT = "docs/theory/paper_e_validation.json"
CERTIFICATE = "data/research/juggler/negative_preimage_density/grid_k12_certificate.json"


def digest(path: Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def lean_inputs(root: Path) -> list[str]:
    """All repository-local transitive imports; Mathlib is pinned by Lake."""
    found: set[str] = set()
    pending = [BARREL, AXIOMS]
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        text = (root / path).read_text(encoding="utf-8")
        for name in re.findall(r"^import\s+([\w.]+)", text, re.M):
            candidate = "formal/" + name.replace(".", "/") + ".lean"
            if (root / candidate).is_file():
                pending.append(candidate)
    return sorted(found | {"formal/lean-toolchain", "formal/lakefile.toml",
                           "formal/lake-manifest.json"})


def declarations(root: Path) -> list[str]:
    return re.findall(r"^#print axioms (\S+)", (root / AXIOMS).read_text(encoding="utf-8"), re.M)


def lean_hashes(root: Path) -> dict[str, str]:
    return {name: digest(root / name) for name in lean_inputs(root)}
