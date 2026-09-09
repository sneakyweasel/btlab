"""Build OEIS b007320.txt for n = 1..30000.

A007320 is steps to 1 under the Juggler map. Resta already published
1..10000; this file extends that range and must match the prefix.
First-passage lengths are not a(n).
"""

from __future__ import annotations

from math import isqrt
from pathlib import Path

N_MAX = 30_000
STEP_CAP = 100_000
BIT_CAP = 10_000_000

HERE = Path(__file__).resolve().parent
RESTA = Path(
    r"C:\Users\phili\.cursor\projects\c-Users-phili-Desktop-balanced-ternary"
    r"\agent-tools\ac5c31f5-025f-49d0-9221-f0562c3ab0cb.txt"
)
OUT = HERE / "b007320.txt"


def juggler(n: int) -> int:
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def stopping_times(n_max: int) -> tuple[list[int], int, int, int, int]:
    a = [0] * (n_max + 1)
    a[1] = 0
    max_bits = 0
    max_bits_n = 1
    max_steps = 0
    max_steps_n = 1
    for n in range(2, n_max + 1):
        x = n
        steps = 0
        while x != 1:
            if x < n:
                steps += a[x]
                break
            x = juggler(x)
            steps += 1
            bits = x.bit_length()
            if bits > max_bits:
                max_bits = bits
                max_bits_n = n
            if bits > BIT_CAP:
                raise RuntimeError(f"bit cap at n={n} after {steps} steps")
            if steps > STEP_CAP:
                raise RuntimeError(f"step cap at n={n}")
        a[n] = steps
        if steps > max_steps:
            max_steps = steps
            max_steps_n = n
    return a, max_bits, max_bits_n, max_steps, max_steps_n


def load_resta(path: Path) -> dict[int, int]:
    table = {}
    for line in path.read_text(encoding="ascii").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        n_s, v_s = line.split()
        table[int(n_s)] = int(v_s)
    return table


def main() -> None:
    a, max_bits, max_bits_n, max_steps, max_steps_n = stopping_times(N_MAX)
    resta = load_resta(RESTA)
    mismatches = [
        n for n, value in resta.items() if n <= N_MAX and a[n] != value
    ]
    if mismatches:
        sample = mismatches[:10]
        raise SystemExit(f"prefix mismatch vs Resta: {sample}")
    if a[1] != 0 or a[2] != 1 or a[3] != 6 or a[37] != 17:
        raise SystemExit("spot checks failed")
    lines = [f"{n} {a[n]}" for n in range(1, N_MAX + 1)]
    OUT.write_text("\n".join(lines) + "\n\n", encoding="ascii", newline="\n")
    print(f"wrote {OUT}")
    print(f"terms 1..{N_MAX}; Resta 1..{max(resta)} matched")
    print(f"max a(n) = {max_steps} at n = {max_steps_n}")
    print(f"max intermediate bits = {max_bits} at n = {max_bits_n}")


if __name__ == "__main__":
    main()
