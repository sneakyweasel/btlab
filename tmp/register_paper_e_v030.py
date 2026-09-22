from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]
for name in ['docs/README.md', 'juggler_review/README.md', 'juggler_review/zenodo_paper_e/README.md']:
    path = root/name
    text = path.read_text(encoding='utf-8')
    lines = text.splitlines(True)
    hits = 0
    for i, line in enumerate(lines):
        if '0.2.0' in line:
            assert ('Paper E' in line or 'signed' in line or 'Version' in line or 'version' in line), line
            lines[i] = line.replace('0.2.0', '0.3.0')
            hits += 1
    assert hits == 1, (name, hits)
    path.write_text(''.join(lines), encoding='utf-8', newline='\n')

path = root/'docs/theory/paper_e_zenodo.json'
metadata = json.loads(path.read_text(encoding='utf-8'))
assert metadata['version'] == '0.2.0'
metadata['version'] = '0.3.0'
path.write_text(json.dumps(metadata, indent=2, ensure_ascii=False)+'\n', encoding='utf-8', newline='\n')

path = root/'docs/theory/theorem_ledger.json'
original = path.read_text(encoding='utf-8')
row = {
 'id': 'J-paper-e-modular-return-exact-construction',
 'tag': 'EXACT — HUMAN PROOF',
 'statement': 'For a=k+1, M>0 and 2^(a+b)<3^a, every visit of s=1+2Mt to the specified simultaneous fractional-part box with s>=2^(2^(b+1)) yields a genuine odd-start Juggler O^a E^b prefix: every state is at least its start, the endpoint is strictly larger, and start and endpoint are 1 modulo 2M. The rational periodic-word code has reduced denominator (3^a-2^(a+b))/gcd(3^a-2^a,2^b-1). For b>0 and every Q, every a>=2*(2^b+(Q+1)*(2^b-1)) is expanding and has denominator greater than Q. The infinitude of distinct starts above every bound is proved CONDITIONAL on BoxRecurrence, the explicitly quantified assertion of arbitrarily large simultaneous-box visits. BoxRecurrence itself is not proved in Lean: this is partial coverage of Theorem 4.1, not an unconditional formalization. All listed results compile with standard logical dependencies; advisory statement-coverage review is pending.',
 'source': 'docs/problems/juggler_signed_collatz_paper.md',
 'lean': 'Problems/Juggler/PaperEModularReturn.lean',
 'decl': ['modular_return_of_box', 'runCode_den', 'runCode_den_gt', 'theorem41_of_box_recurrence'],
 'lean_trust': 'kernel',
 'tests': ['tests/unit/test_paper_e_release.py', 'tests/research/juggler_sequence/test_layer_architecture.py'],
 'related_conjectures': []
}
assert not any(r['id']==row['id'] for r in json.loads(original))
block = '\n'.join(' '+line for line in json.dumps(row,indent=1,ensure_ascii=False).splitlines())
assert original.startswith('[\n')
result = '[\n'+block+',\n'+original[2:]
assert json.loads(result)[1:] == json.loads(original)
path.write_text(result,encoding='utf-8',newline='\n')
print('Updated Paper E versions and inserted only the scoped construction ledger row.')
