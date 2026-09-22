from pathlib import Path
import json,subprocess
p=Path('docs/theory/theorem_ledger.json')
raw=subprocess.check_output(['git','-c','safe.directory=C:/Users/phili/Desktop/balanced_ternary','show','HEAD:docs/theory/theorem_ledger.json']).decode('utf-8')
old=json.loads(raw)
current=json.loads(p.read_text(encoding='utf-8'))
row=next(r for r in current if r['id']=='BTA-finite-fejer-box-discrepancy')
assert [r for r in current if r['id']!=row['id']]==old, 'Other ledger work appeared; do not overwrite.'
addition=json.dumps(row,ensure_ascii=False,indent=1)
p.write_text(raw.rstrip()[:-1].rstrip()+',\n '+addition.replace('\n','\n ')+'\n]\n',encoding='utf-8')
