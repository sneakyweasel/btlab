import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / 'docs/theory/theorem_ledger.json'
raw = path.read_text(encoding='utf-8')
row_id = 'J-signed-preimage-grid-counting'
assert f'"id": "{row_id}"' not in raw
row = {
    'id': row_id,
    'tag': 'EXACT — HUMAN PROOF',
    'statement': (
        'Let N(a,X) count positive integers whose minus-shortcut orbit reaches '
        'a while every intervening state stays at most X. Let C(t) be the '
        'explicit 50-rung integer cap defined in PreimageGrid.lean. For every '
        'nonperiodic a>=4096 with a=1 mod 3, b=(2*a+1)/3, and every natural t, '
        'N(a,C(t+100)*a)>=N(4*a,C(t)*4*a)+N(b,C(t+129)*b), and separately '
        'N(a,C(t+100)*a)>=N(4*a,C(t)*4*a)+N(2*b,C(t+79)*2*b). The single '
        '4*a term is bounded without nonperiodicity or a lower root threshold. '
        'The cap inequalities retain the signed offset: 12288*b<=8193*a, '
        '8193*C(t+29)<=12288*C(t), and 16386*C(t)<=12288*C(t+21). For '
        'M(t,a)=10*t+floor(log2(a^498)), the three calls satisfy '
        'M(t,4*a)+4<=M(t+100,a), M(t+79,2*b)+3<=M(t+100,a), and '
        'M(t+129,b)+1<=M(t+100,a). The fertile residue choices are the '
        'direct odd child at a=1 mod 9, doubled odd child at a=7 mod 9, '
        'and just 4*a at a=4 mod 9. All these statements are kernel-checked '
        'for actual capped integer trees. The root threshold alone is not '
        'backward closed, and a closed-domain growth induction and numerical '
        'certificate remain unproved here. No density exponent or termination '
        'theorem follows yet. This adapts M. Sharpe\'s strict-grid root-induction '
        'method to the signed correction. Ledger label awaits advisory coverage.'
    ),
    'source': 'docs/problems/juggler_negative_preimage_density.md',
    'lean': 'Problems/Collatz/PreimageGrid.lean',
    'decl': ['TreeMem', 'tree', 'count', 'Nonperiodic', 'table', 'rung', 'cap',
             'rootSize', 'measure', 'cap_quad', 'signed_child_ratio',
             'cap_signed_advance', 'cap_signed_retard', 'count_four',
             'count_odd', 'count_doubled_odd', 'signed_power_slack',
             'measure_children', 'fertile_children'],
    'lean_trust': 'kernel',
    'tests': ['tests/research/juggler_sequence/test_negative_preimage_density.py'],
    'related_conjectures': [],
}
marker = raw.index('"id": "J-signed-preimage-expanding-block-height"')
start = raw.rfind('{', 0, marker)
_, size = json.JSONDecoder().raw_decode(raw[start:])
end = start + size
entry = '\n'.join(' ' + line for line in json.dumps(row, indent=1, ensure_ascii=False).splitlines())
raw = raw[:end] + ',\n' + entry + raw[end:]
json.loads(raw)
path.write_text(raw, encoding='utf-8', newline='\n')

path = root / 'docs/juggler_branch_ledger.md'
lines = path.read_text(encoding='utf-8').splitlines()
matches = [i for i, line in enumerate(lines) if line.startswith('| Signed Collatz preimages |')]
assert len(matches) == 1
lines[matches[0]] = (
    '| Signed Collatz preimages | [Preimage density and height correction]'
    '(problems/juggler_negative_preimage_density.md) | PARK | '
    '`PreimageGrid.lean` proves actual strict-grid counting recurrences '
    'for nonperiodic fertile roots at least 4096, with measure drops 4, 3, 1 | '
    'The grid slack absorbs the signed offset and avoids deletion inside '
    'residue minima; the earlier expanding-block bound is retained | '
    'A closed root domain or boundary argument and a checked growth '
    'certificate remain. The x^0.84 row stays CONJECTURE; no Juggler '
    'termination bound follows |'
)
path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
