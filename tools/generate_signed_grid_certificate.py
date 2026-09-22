"""Render the kernel certificate table and its bounded check blocks.

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
    weights = d['weights']
    def tree(v):
        if len(v) <= 32:
            return '(.leaf [' + ', '.join(map(str,v)) + '])'
        cut = len(v)//2
        return f'(.branch {cut}\n{tree(v[:cut])}\n{tree(v[cut:])})'
    shards = []
    def outer(v):
        if len(v) <= 4096:
            name = f'shard{len(shards)}'
            shards.append(f'private noncomputable def {name} : WeightTree :=\n{tree(v)}\n')
            return name
        cut = len(v)//2
        return f'(.branch {cut} {outer(v[:cut])} {outer(v[cut:])})'
    root_tree = outer(weights)
    text = '''import Mathlib.Tactic

/-! An independently generated integer certificate for the signed strict grid.
The table has one weight for each fertile residue modulo 3^12.
The balanced tree keeps kernel evaluation of table lookup logarithmic.
-/
namespace Problems.Collatz.PreimageWeights12

inductive WeightTree where
  | leaf (values : List ℕ)
  | branch (cut : ℕ) (left right : WeightTree)

def lookup : WeightTree → ℕ → ℕ
  | .leaf values, i => values.getD i 0
  | .branch cut left right, i =>
      if i < cut then lookup left i else lookup right (i - cut)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''+ '\n'.join(shards) + '''

noncomputable def weights : WeightTree :=
'''+root_tree+'''

noncomputable def c (m : ℕ) : ℕ := lookup weights (m / 3)

def row (i : ℕ) : Prop :=
  let m := 3 * i + 1
  let c4 := c (4 * m % 531441)
  let b := (2 * m + 1) / 3 % 177147
  let d := (4 * m + 2) / 3 % 177147
  let cb := min (c b) (min (c (b + 177147)) (c (b + 354294)))
  let cd := min (c d) (min (c (d + 177147)) (c (d + 354294)))
  1 ≤ c m ∧ c m ≤ 1000000000000 ∧
    (m % 9 = 4 → c m * 5059^100 ≤ c4 * 5000^100) ∧
    (m % 9 = 7 → c m * 5059^100 ≤ c4 * 5000^100 + cd * (5059^79 * 5000^21)) ∧
    (m % 9 = 1 → c m * 5059^100 * 5000^29 ≤ c4 * 5000^129 + cb * 5059^129)

noncomputable instance (i : ℕ) : Decidable (row i) := by unfold row; infer_instance

theorem first_chunk : ∀ i < 256, row i := by decide +kernel

end Problems.Collatz.PreimageWeights12
'''
    outputs[root/'formal/Problems/Collatz/PreimageWeights12.lean'] = text

    parts = 4
    blocks_per_part = 173
    for part in range(parts):
        low = part * blocks_per_part * 256
        high = min(177147, low + blocks_per_part * 256)
        lines = ['import Problems.Collatz.PreimageWeights12', '',
                 f'namespace Problems.Collatz.PreimageCheck12Part{part}',
                 'open PreimageWeights12',
                 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
        for j in range(blocks_per_part):
            offset = low + 256*j
            lines += [f'private theorem chunk{j} : ∀ n < 256, {offset} + n < 177147 →',
                      f'    row ({offset} + n) := by decide +kernel', '']
        lines += [f'theorem checked : ∀ i, {low} ≤ i → i < {high} → row i := by',
                  f'  have hc : ∀ j < {blocks_per_part}, ∀ n < 256,',
                  f'      {low} + 256*j + n < 177147 → row ({low} + 256*j + n) := by',
                  '    intro j hj', '    interval_cases j']
        lines += [f'    · exact chunk{j}' for j in range(blocks_per_part)]
        lines += ['  intro i hlo hhi',
                  f'  have h := hc ((i-{low})/256) (by omega) ((i-{low})%256) (by omega) (by omega)',
                  f'  have he : {low} + 256*((i-{low})/256) + (i-{low})%256 = i := by omega',
                  '  simpa only [he] using h', '',
                  f'end Problems.Collatz.PreimageCheck12Part{part}', '']
        outputs[root/f'formal/Problems/Collatz/PreimageCheck12Part{part}.lean'] = '\n'.join(lines)


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
