"""Conservative test selection for explicit iteration; full verification stays the default.

Imports and recorded claim links identify candidates, not complete dynamic coverage.
The selection never changes the research, publication or Lean gates.
"""
from pathlib import Path

PROFILES = ('full', 'focused')
EVIDENCE_TESTS = ('tests/unit/test_claims.py', 'tests/unit/test_theorem_ledger.py')
GLOBAL_PATHS = {'conftest.py', 'pyproject.toml', 'pytest.ini', 'setup.cfg', 'tox.ini',
                'src/research/__init__.py', 'src/research/claims.py', 'src/research/claim_dependencies.py',
                'src/research/knowledge.py', 'src/research/literature.py'}
GLOBAL_PREFIXES = ('src/research_engine/', 'src/bt/', 'src/research/experiments/', '.github/')


def compact_paths(paths):
    """Do not pass a test twice when an explicitly selected directory contains it."""
    result = []
    for path in sorted(set(paths)):
        if not any(path.startswith(parent.rstrip('/') + '/') for parent in result):
            result.append(path)
    return result


def select_tests(root: Path, change: dict, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError('Verification profile must be full or focused')
    changed = change['changed_files']
    documentation = all(Path(p).suffix == '.md' and p.startswith(('docs/', 'attacks/')) for p in changed)
    default = ['tests/integration', 'tests/unit/test_theorem_ledger.py'] if documentation else ['tests']
    if profile == 'full' or not changed:
        return {'mode': 'documentation' if documentation else 'full', 'paths': default,
                'fallback_reasons': [], 'basis': 'Default verification policy.'}

    reasons = list(change['uncertainties'])
    selected = set(change['affected_tests'])
    for path in changed:
        name = Path(path).name
        if not (root / path).is_file():
            reasons.append(f'Deleted or unavailable input: {path}')
        elif (path in GLOBAL_PATHS or path.startswith(GLOBAL_PREFIXES) or name in {'conftest.py', '__init__.py'}
              or path.startswith('tools/lab') or path.startswith('tools/requirements')
              or name in {'lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json'}):
            reasons.append(f'Shared infrastructure or configuration: {path}')
        elif path.endswith('.md') and path.startswith(('docs/', 'attacks/')):
            selected.update(p for p in ('tests/integration', *EVIDENCE_TESTS) if (root / p).exists())
        elif (path.startswith('docs/claims/') or path.startswith('formal/') and path.endswith('.lean') or path in {
                'docs/theory/theorem_ledger.json', 'attacks/juggler/index.json'}):
            selected.update(p for p in EVIDENCE_TESTS if (root / p).is_file())
        elif (path.endswith('.py') and path.startswith(('src/', 'tools/', 'tests/'))
              or path.startswith('data/research/')):
            if not change['test_links'].get(path):
                reasons.append(f'No static or recorded test association: {path}')
        else:
            reasons.append(f'Unclassified input: {path}')
    selected = compact_paths(selected)
    if not selected:
        reasons.append('No focused Python tests were identified.')
    if sum(len(p) + 3 for p in selected) > 12000:
        reasons.append('Focused test arguments exceed the portable command-line budget.')
    if reasons:
        return {'mode': 'full', 'paths': ['tests'], 'fallback_reasons': sorted(set(reasons)),
                'basis': 'Full fast suite fallback; focused coverage is insufficient.'}
    return {'mode': 'affected', 'paths': selected, 'fallback_reasons': [],
            'basis': 'Static import dependents, explicit claim test links and structural evidence tests. '
                     'Iteration only: unrecorded dynamic and file dependencies may be missed.'}
