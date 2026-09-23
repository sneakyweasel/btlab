"""Render or check the negative-knowledge directory without changing its evidence."""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from research.knowledge import INDEX, negative_errors, negative_paths, render_negative_index


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        (ROOT / INDEX).write_text(render_negative_index(ROOT), encoding="utf-8", newline="\n")
    texts = {p.relative_to(ROOT).as_posix(): p.read_text(encoding="utf-8") for p in negative_paths(ROOT)}
    errors = negative_errors(ROOT, texts)
    for error in errors:
        print(f'{error["path"]}: {error["error"]}')
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
