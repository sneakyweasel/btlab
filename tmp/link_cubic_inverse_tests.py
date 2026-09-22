"""Add the independent symbolic-calculus test to the two new ledger rows."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
path=root/'docs/theory/theorem_ledger.json'
raw=path.read_text(encoding='utf-8')
for row_id in ('J-first-inverse-cell-mixed-bound','J-cubic-inverse-cell-algebra'):
    pos=raw.index('"id": "'+row_id+'"')
    start=raw.rfind('\n {',0,pos)+2
    assert raw[start]=='{'
    obj,used=json.JSONDecoder().raw_decode(raw[start:])
    assert obj['id']==row_id
    test='tests/research/juggler_sequence/test_cubic_inverse_cell.py'
    if test not in obj['tests']:
        obj['tests'].append(test)
    replacement=json.dumps(obj,ensure_ascii=False,indent=1).replace('\n','\n ')
    raw=raw[:start]+replacement+raw[start+used:]
path.write_text(raw,encoding='utf-8')
