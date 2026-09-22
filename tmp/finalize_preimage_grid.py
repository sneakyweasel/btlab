from pathlib import Path

path = Path('docs/theory/theorem_ledger.json')
raw = path.read_text(encoding='utf-8')
old = 'Krasikov-Lagarias 2003 remains the external positive 3x+1 result.'
new = old + (' The subsequent J-signed-preimage-grid-counting proves actual strict-grid '
             'count inequalities and a decreasing induction measure above root 4096; '
             'a closed root domain and a checked growth certificate remain open.')
assert raw.count(old) == 1
path.write_text(raw.replace(old, new), encoding='utf-8', newline='\n')

path = Path('literature/krasikov-lagarias-2003-difference-inequalities.json')
raw = path.read_text(encoding='utf-8')
old = ('Any repair must justify the inequalities for actual minus-map counting functions, '
       'including the minimization/deletion steps.')
new = ('A repair using the original elimination must justify its minimization/deletion '
       'steps for actual signed counting functions. The subsequent strict-grid adaptation '
       'of M. Sharpe\'s root-induction method bypasses that elimination: PreimageGrid.lean '
       'checks actual counts and measure decreases above root 4096, while a closed root '
       'domain and growth certificate remain open.')
assert raw.count(old) == 1
path.write_text(raw.replace(old, new), encoding='utf-8', newline='\n')
