import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / 'docs/theory/theorem_ledger.json'
raw = path.read_text(encoding='utf-8')
row_id = 'J-signed-preimage-expanding-block-height'
assert f'"id": "{row_id}"' not in raw
row = {
    'id': row_id,
    'tag': 'EXACT — HUMAN PROOF',
    'statement': (
        'For formal real inverse words in E(x)=2*x and O(x)=(2*x+1)/3, '
        'write f_w(x)=R_w*x+B_w. The affine identity, R_w>0 and B_w>=0 '
        'are kernel-checked. For every finite family F with R_w>1 for '
        'each w in F, K=1+sum_{w in F} B_w/(R_w-1) is at least 1 and '
        'every finite concatenation W of blocks from F satisfies '
        'f_W(x)+K<=R_W*(x+K), for every real x. More generally the '
        'block condition B_w<=(R_w-1)*K suffices. For K>=1 satisfying '
        'that condition, x>=0, and any subsequent inverse prefix u of '
        'length at most L, f_{Wu}(x)+1<=2^L*R_W*(x+K). Thus the height '
        'constants do not grow with the number of blocks. For EE and '
        'OE, K=2 suffices; at every natural a=1 mod 3, 2*(2*a+1)/3 is '
        'an actual two-step minus-shortcut predecessor and its shifted '
        'height equals (4/3)*(a+2). No real translation K absorbs both '
        'elementary inverse branches with their exact factors 2 and 2/3. '
        'This is the standard affine-shift principle instantiated for '
        'signed inverse words, not a density or termination theorem. '
        'Integrality, valid counting inequalities, disjointness and '
        'residue-minimum/deletion operations are not supplied by the '
        'real-word bound. Ledger label awaits advisory coverage review.'
    ),
    'source': 'docs/problems/juggler_negative_preimage_density.md',
    'lean': 'Problems/Collatz/PreimageScale.lean',
    'decl': [
        'inverseWord', 'inverseFactor', 'inverseFactor_pos',
        'inverseWord_affine', 'inverseWord_nonneg', 'inverseWord_append',
        'inverseFactor_append', 'shifted_block_iff', 'shifted_blocks',
        'finite_expanding_shift', 'inverseWord_height', 'internal_prefix_height',
        'two_block_shift', 'two_step_preimage', 'no_elementary_shift',
    ],
    'lean_trust': 'kernel',
    'tests': [],
    'related_conjectures': [],
}
# Insert immediately after the existing signed-height row, preserving all
# other byte-level JSON formatting, including the mixed Unicode escapes.
marker = raw.index('"id": "J-kl-signed-preimage-height-gap"')
start = raw.rfind('{', 0, marker)
_, size = json.JSONDecoder().raw_decode(raw[start:])
end = start + size
entry = '\n'.join(' ' + line for line in json.dumps(row, indent=1, ensure_ascii=False).splitlines())
raw = raw[:end] + ',\n' + entry + raw[end:]
json.loads(raw)
path.write_text(raw, encoding='utf-8', newline='\n')

path = root / 'docs/juggler_branch_ledger.md'
text = path.read_text(encoding='utf-8')
lines = text.splitlines()
matches = [i for i, line in enumerate(lines) if line.startswith('| Signed Collatz preimages |')]
assert len(matches) == 1
lines[matches[0]] = (
    '| Signed Collatz preimages | [Preimage density and height correction]'
    '(problems/juggler_negative_preimage_density.md) | PARK | '
    'Exact scale comparison, nonperiodic witness, and uniform expanding-block '
    'height bound compiled in `PreimageScale.lean`; density row remains '
    '**CONJECTURE** | One shift absorbs all offsets in any finite expanding '
    'inverse-block family, with an internal-prefix bound; no common shift '
    'works for both elementary letters | A valid signed counting system '
    'and its minimum/deletion steps remain open. No density exponent or '
    'Juggler termination bound follows |'
)
path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
