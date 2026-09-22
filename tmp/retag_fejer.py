from pathlib import Path
import json
p=Path('docs/theory/theorem_ledger.json')
rows=json.loads(p.read_text(encoding='utf-8'))
row=next(r for r in rows if r['id']=='BTA-finite-fejer-box-discrepancy')
row['tag']='EXACT — LEAN VERIFIED'
p.write_text(json.dumps(rows,ensure_ascii=False,indent=1)+'\n',encoding='utf-8')
