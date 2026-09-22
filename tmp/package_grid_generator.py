from pathlib import Path
root = Path(__file__).resolve().parents[1]
w = (root/'tmp/generate_signed_grid_weights.py').read_text(encoding='utf-8')
w = w[w.index("weights = d['weights']"):]
w = w[:w.index("print('Wrote weights:")]
w = w.replace("(root/'formal/Problems/Collatz/PreimageWeights12.lean').write_text(text,encoding='utf-8')",
              "outputs[root/'formal/Problems/Collatz/PreimageWeights12.lean'] = text")
c = (root/'tmp/generate_signed_grid_checks.py').read_text(encoding='utf-8')
c = c[c.index('parts = 4'):c.index("lines = [f'import Problems.Collatz.PreimageCheck12Part")]
c = c.replace("(root/f'formal/Problems/Collatz/PreimageCheck12Part{part}.lean').write_text('\\n'.join(lines), encoding='utf-8')",
              "outputs[root/f'formal/Problems/Collatz/PreimageCheck12Part{part}.lean'] = '\\n'.join(lines)")
prefix = '''"""Render the kernel certificate table and its bounded check blocks.

The committed JSON is the input; the assembled density theorem is maintained
separately. Run with --check to verify exact reproducibility without writes.
The mathematical checker uses only exact integer arithmetic.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from research.juggler_sequence.negative_preimage_density import verify_grid_certificate


def render_sources(root: Path, d: dict) -> dict[Path, str]:
    if (d["k"], d["p"], d["q"], d["maximum"]) != (12, 5059, 5000, 10**12):
        raise ValueError("this Lean certificate uses the fixed level-12 parameters")
    report = verify_grid_certificate(d)
    if not report["all_integer_inequalities_hold"]:
        raise ValueError("the integer certificate fails")
    outputs: dict[Path, str] = {}
'''
body = '\n'.join('    '+line if line else '' for line in (w+'\n'+c).splitlines())
suffix = '''
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = root / "data/research/juggler/negative_preimage_density/grid_k12_certificate.json"
    outputs = render_sources(root, json.loads(source.read_text(encoding="utf-8")))
    for path, text in outputs.items():
        if args.check:
            if path.read_text(encoding="utf-8") != text:
                raise SystemExit(f"generated certificate differs: {path.relative_to(root)}")
        else:
            path.write_text(text, encoding="utf-8")
    print(f"{'Checked' if args.check else 'Wrote'} {len(outputs)} Lean certificate files")


if __name__ == "__main__":
    main()
'''
# Indenting Python source also indents its multiline Lean string literals.
# Keep their contents exactly as generated in the original scripts.
import tokenize, io
combined = prefix+body+'\n'+suffix
tokens = list(tokenize.generate_tokens(io.StringIO(combined).readline))
lines = combined.splitlines(keepends=True)
for token in reversed(tokens):
    if token.type == tokenize.STRING and token.start[0] != token.end[0]:
        for i in range(token.start[0], token.end[0]):
            if lines[i].startswith('    '):
                lines[i] = lines[i][4:]
combined = ''.join(lines)
compile(combined, '<generator>', 'exec')
(root/'tools/generate_signed_grid_certificate.py').write_text(combined,encoding='utf-8')
