import json
from math import log2
from pathlib import Path
from time import perf_counter
import numpy as np

k, p, q, scale = 12, 5059, 5000, 10**12
modulus, third = 3**k, 3**(k-1)
m = np.arange(1, modulus, 3, dtype=np.int64)
four = ((4*m) % modulus - 1)//3
odd = (m % 9 != 4)
w = np.where(m % 9 == 1, (2*m+1)//3, (4*m+2)//3) % third
w = np.where(odd, w, 1)
lifts = np.array([(w + j*third - 1)//3 for j in range(3)])
mu = p/q
factor = np.where(m % 9 == 1, mu**29, np.where(m % 9 == 7, mu**-21, 0))
c = np.ones(len(m))
t0 = perf_counter()
for i in range(5000):
    f = mu**-100*c[four] + factor*np.min(c[lifts], axis=0)
    ratios = f/c
    lo, hi = float(ratios.min()), float(ratios.max())
    if i % 200 == 0:
        print(i, lo, hi, perf_counter()-t0, flush=True)
    if lo > 1.00000001:
        break
    c = (c + f)/2
    c /= c.max()
else:
    raise RuntimeError(('no certificate found', lo, hi))
weights = [round(float(v)*scale) for v in c]
p100, q100, p79q21 = p**100, q**100, p**79*q**21
q29, q129, p129 = q**29, q**129, p**129
failures = []
min_relative_slack = 1.0
for j, mj in enumerate(range(1, modulus, 3)):
    c4 = weights[(4*mj % modulus - 1)//3]
    lhs = weights[j]*p100
    rhs = c4*q100
    if mj % 9 != 4:
        child = (((2*mj+1)//3) if mj % 9 == 1 else ((4*mj+2)//3)) % third
        cb = min(weights[(child+d*third-1)//3] for d in range(3))
        if mj % 9 == 1:
            lhs *= q29
            rhs = c4*q129 + cb*p129
        else:
            rhs += cb*p79q21
    if lhs > rhs:
        failures.append(mj)
    min_relative_slack = min(min_relative_slack, (rhs-lhs)/lhs)
assert not failures, failures[:10]
payload = dict(k=k,p=p,q=q,exponent=50*log2(mu),minimum=min(weights),maximum=max(weights),
               exact_inequalities_checked=len(weights), minimum_relative_slack=min_relative_slack,
               iterations=i+1, weights=weights)
path = Path(__file__).with_name('signed_grid_k12_certificate.json')
path.write_text(json.dumps(payload, separators=(',', ':'))+'\n', encoding='utf-8')
print({k:v for k,v in payload.items() if k != 'weights'}, flush=True)
print(path, flush=True)
