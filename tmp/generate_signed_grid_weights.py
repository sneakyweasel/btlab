import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
d = json.loads((root/'tmp/signed_grid_k12_certificate.json').read_text())
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
(root/'formal/Problems/Collatz/PreimageWeights12.lean').write_text(text,encoding='utf-8')
print('Wrote weights:',len(weights),'bytes:',len(text.encode()))
