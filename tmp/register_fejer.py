from pathlib import Path
import json
p=Path('docs/theory/theorem_ledger.json')
rows=json.loads(p.read_text(encoding='utf-8'))
row={
 'id':'BTA-finite-fejer-box-discrepancy',
 'tag':'EXACT — HUMAN PROOF',
 'statement':'For integers H,N>=1, E>=0, and arbitrary points z_0,...,z_(N-1) on the product of two unit circles, suppose every nonzero integer pair (k,l) with abs(k),abs(l)<=H has normalized Fourier sum norm at most E. For real endpoints a<=b<=a+1 and c<=d<=c+1, the product B of the images of [a,b) and [c,d) then satisfies abs(count(z_n in B)/N-(b-a)*(d-c)) <= 5/sqrt(H+1)+(3+2*log(H))^2*E. Empty, full, wrapped arcs and sample boundary hits are included. The actual Fejer kernel, tails, saturated smoothing, coefficient mass and finite count transfer are proved; no smoothing estimate is assumed. This is the complete finite discrepancy obligation Q3, not the specific OOE Fourier rate or effective modular-return assembly.',
 'source':'docs/theory/finite_fejer_box_note.md',
 'lean':'BTCalculus/FejerBox.lean',
 'decl':['finite_box_discrepancy'],
 'lean_trust':'kernel',
 'tests':['tests/unit/test_theorem_ledger.py','tests/tools/test_formalpedia.py'],
 'related_conjectures':[]
}
assert not any(r['id']==row['id'] for r in rows)
rows.append(row)
p.write_text(json.dumps(rows,ensure_ascii=False,indent=1)+'\n',encoding='utf-8')
helper=Path('tmp/lean_paper_e.ps1').read_text(encoding='utf-8')
helper=helper[:helper.index('if($Build)')]+'& lake build\nexit $LASTEXITCODE\n'
Path('tmp/build_fejer.ps1').write_text(helper,encoding='utf-8')
