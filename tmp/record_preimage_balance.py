import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / 'docs/theory/theorem_ledger.json'
text = path.read_text(encoding='utf-8')
rows = json.loads(text)
row = {
    'id': 'J-signed-grid-mean-ceiling',
    'tag': 'EXACT — HUMAN PROOF',
    'statement': 'At every finite residue level ell>=2, a strictly positive weight table satisfying either the normalized 3n-1 rows or the normalized 3n+1 rows of the fixed 1/50 grid must satisfy 1<=mu^(-100)+(mu^29+mu^(-21))/3 for every positive real grid rate mu used in those rows. The fourfold map and both child index maps are affine permutations; the three-lift minima sum to at most one third of the total weight. Equivalently, 3*mu^100<=3+mu^129+mu^79. In the explicitly stated at-most-linear rate range mu^50<=2, every such table has mu<5069/5000 and mu^5000<2^99, hence exponent 50*log_2(mu)<99/100. The harmonic rate mu^50=2 is impossible, since it would imply 2^79>=3^50, contradicting the strict integer inequality. These are all-level restrictions on this finite certificate scheme, not upper bounds on actual ancestor counts, not restrictions for every grid, and not a resolution of harmonic divergence for fate classes. Larger residue tables alone cannot remove this fixed-grid obstruction. The local Lean proof is complete; the ledger label awaits advisory statement-coverage review.',
    'source': 'docs/problems/juggler_negative_preimage_density.md',
    'lean': 'Problems/Collatz/PreimageBalance.lean',
    'decl': ['signed_index_formulas', 'balanced_mean_bound', 'strict_grid_mean',
             'strict_grid_plus_mean', 'cleared_mean_bound', 'rate_lt_of_rows',
             'rate_lt_of_plus_rows', 'certificate_power_ceiling', 'harmonic_rate_excluded'],
    'lean_trust': 'kernel',
    'tests': ['tests/research/juggler_sequence/test_negative_preimage_density.py'],
    'related_conjectures': [],
}
assert not any(r['id'] == row['id'] for r in rows)
end = text.rfind('\n]')
assert end >= 0 and text[end:].strip() == ']'
rendered = '\n'.join(' ' + line for line in json.dumps(row, ensure_ascii=False, indent=1).splitlines())
path.write_text(text[:end].rstrip() + ',\n' + rendered + '\n]\n', encoding='utf-8')

path = root / 'docs/juggler_branch_ledger.md'
text = path.read_text(encoding='utf-8')
old = '| Signed exponent 21/25 established for all large natural cutoffs, including cycle targets; no Juggler termination bound follows |'
new = '| Signed exponent 21/25 established, including cycle targets. The fixed grid has an all-level mean ceiling below 0.99 in the at-most-linear rate range; increasing table size alone to harmonic growth is closed. No Juggler termination bound follows |'
assert text.count(old) == 1
path.write_text(text.replace(old, new), encoding='utf-8')

path = root / 'docs/theory/collatz_bridge_lean_plan.md'
text = path.read_text(encoding='utf-8')
text += '\nThe finite-grid mean audit is now compiled in `Problems/Collatz/PreimageBalance.lean`.\n'
text += 'Both signs share the all-level necessary inequality\n1<=mu^(-100)+(mu^29+mu^(-21))/3. In the at-most-linear rate range,\n'
text += 'mu^5000<2^99; the harmonic rate contradicts 2^79<3^50.\n'
text += 'This closes table-size growth alone in the current fixed grid, while\nactual fate-specific harmonic growth and Juggler pressure remain open.\n'
path.write_text(text, encoding='utf-8')

source = (root / 'tmp/index_preimage_domain.py').read_text(encoding='utf-8')
start = source.index("for rel in ('formal/Problems.lean'")
end = source.index('    target = snapshot / rel', start)
paths = ('formal/Problems.lean', 'formal/Problems/Collatz/PreimageBalance.lean')
source = source[:start] + 'for rel in ' + repr(paths) + ':\n' + source[end:]
source = source.replace('the three scoped Lean files', 'the scoped preimage-balance files')
(root / 'tmp/index_preimage_balance.py').write_text(source, encoding='utf-8')
print('Recorded the mean-ceiling row and scoped index script.')
