from pathlib import Path
root = Path(__file__).resolve().parents[1]
changes = {
    'literature/sharpe-2026-collatz-grid-root-induction.json': (
        'The signed growth induction still needs a closed root domain or boundary treatment and a checked certificate.',
        'PreimageDomain.lean now supplies a closed domain for every positive target prime to 3, including cycle targets, using a finite orbit barrier and a large nonperiodic ancestor. The growth induction and its checked certificate remain open.'),
    'literature/krasikov-lagarias-2003-difference-inequalities.json': (
        'while a closed root domain and growth certificate remain open.',
        'and PreimageDomain.lean supplies a closed domain for every positive target prime to 3; the growth induction and its checked certificate remain open.'),
}
for rel, (old, new) in changes.items():
    path = root / rel
    text = path.read_text(encoding='utf-8')
    assert text.count(old) == 1, rel
    path.write_text(text.replace(old, new), encoding='utf-8')
