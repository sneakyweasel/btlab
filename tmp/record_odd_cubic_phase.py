"""Append scoped theorem rows without rewriting the existing ledger."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / 'docs/theory/theorem_ledger.json'
raw = path.read_text(encoding='utf-8')
rows = json.loads(raw)
new_rows = [
    {
        'id': 'J-odd-source-square-root-discrepancy',
        'tag': 'EXACT — HUMAN PROOF',
        'statement': 'For every epsilon>0 there is C_epsilon such that for every real P>=2 and every interval I contained in (P,2P], the absolute value of the sum of (-1)^floor(n^(3/2)) over odd natural n in I is at most C_epsilon*P^(1/2+epsilon). Dyadic summation gives the same bound for odd n<=N, hence the actual OO prefix count is N/4+O_epsilon(N^(1/2+epsilon)). The proof uses the C4 van der Corput transform, rational cubic complete-sum bounds, Fourier completion, an averaged bound on the even-harmonic resonant means, and paired Vaaler majorants including integer endpoints. This is an AI-assisted written proof, pending independent review. Only the exact phase algebra is kernel-checked in the separate row J-odd-cubic-phase-cancellation. The interval estimate is in the ambient scale, not interval length; it asserts no bound on iterated images, growing-depth stopped pressure, infinite escape, or termination.',
        'source': 'docs/problems/juggler_odd_image_discrepancy.md',
        'lean': '',
        'tests': ['tests/research/juggler_sequence/test_odd_image_discrepancy.py'],
        'related_conjectures': [],
    },
    {
        'id': 'J-odd-cubic-phase-cancellation',
        'tag': 'EXACT — HUMAN PROOF',
        'statement': 'For positive reals h,r put s=((2*r/(3*h))^2-1)/2. Then sqrt(2*s+1)=2*r/(3*h), (3*h/2)*sqrt(2*s+1)=r, (h/2)*(2*s+1)*sqrt(2*s+1)-r*s=r/2-2*r^3/(27*h^2), and (3*h/2)/sqrt(2*s+1)=9*h^2/(4*r). For every odd natural q and every natural r, e((r+q)/2-2*(r+q)^3/q)=-e(r/2-2*r^3/q), where e(x)=exp(2*pi*i*x). Consequently every odd natural h gives zero sum of e(r/2-2*r^3/(27*h^2)) over 0<=r<54*h^2. All these exact identities are kernel-checked; the ledger label awaits advisory statement coverage. They do not themselves prove the analytic transform, incomplete-sum bounds, or the discrepancy estimate.',
        'source': 'docs/problems/juggler_odd_image_discrepancy.md',
        'lean': 'Problems/Juggler/OddCubicPhase.lean',
        'decl': ['wave', 'dualPhase', 'stationaryPoint', 'stationary_sqrt',
                 'stationary_derivative', 'stationary_phase', 'stationary_curvature',
                 'halfCubic', 'halfCubic_shift', 'halfCubic_antiperiodic',
                 'odd_complete_mean_zero', 'dual_odd_antiperiodic',
                 'dual_odd_complete_mean_zero'],
        'lean_trust': 'kernel',
        'tests': ['tests/research/juggler_sequence/test_odd_image_discrepancy.py'],
        'related_conjectures': [],
    },
]
assert not ({r['id'] for r in rows} & {r['id'] for r in new_rows})
assert raw.rstrip().endswith(']')
addition = ',\n'.join(' ' + json.dumps(row, ensure_ascii=False, indent=1).replace('\n', '\n ') for row in new_rows)
path.write_text(raw.rstrip()[:-1].rstrip() + ',\n' + addition + '\n]\n', encoding='utf-8')
print('Appended two scoped rows.')
