"""CI policy: new public interfaces cannot silently inherit legacy naming debt."""
import json
from pathlib import Path
import sys

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import formalpedia as fp
import lean_style


def test_committed_public_lean_interfaces_follow_the_reviewed_policy():
    baseline = json.loads(lean_style.BASELINE.read_text(encoding='utf-8'))
    # CI checks the revision being submitted. The CLI additionally checks the live
    # working tree, including concurrently edited/untracked research drafts.
    _, index = lean_style.committed_index('HEAD')
    result = lean_style.report(index, baseline)
    assert not result['new_violations'], '\n'.join(
        f"{r['file']}:{r['line']}: {r['id']} [{r['rule']}] {r['message']}"
        for r in result['new_violations'])


def test_baseline_exemptions_are_specific_and_unique():
    baseline = json.loads(lean_style.BASELINE.read_text(encoding='utf-8'))
    keys = [lean_style.key(row) for row in baseline['violations']]
    assert len(keys) == len(set(keys))
    assert len(baseline['revision']) == 40
    assert all('*' not in row['id'] and row['rule'] in lean_style.RULES
               for row in baseline['violations'])
