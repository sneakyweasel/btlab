"""Bounded reconnaissance; floating results are diagnostics only."""
import numpy as np

def layer(previous, sign=1, unit_only=False):
    modulus = 3 * len(previous)
    a = np.arange(modulus, dtype=np.int64)
    result = np.zeros(modulus)
    residue = a.copy()
    for k in range(1, 81):
        residue = 2 * residue % modulus
        valid = (residue - sign) % 3 == 0
        children = ((residue[valid] - sign) // 3) % len(previous)
        result[valid] += (3.0 / 2**k) * previous[children]
    return result

f = np.ones(1)
for depth in range(1, 13):
    f = layer(f)
    units = f[np.arange(len(f)) % 3 != 0]
    print(depth, len(f), 'mean', f.mean(), 'min', units.min(),
          'max', units.max(), 'poor', np.mean(units < 1),
          'samples', [round(f[a % len(f)], 6) for a in (1, 5, 7, 17, 19, 27, 31, 97)],
          flush=True)
