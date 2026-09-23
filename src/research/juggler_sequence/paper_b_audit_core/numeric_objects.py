"""Historical Paper B audit: numeric objects.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import subprocess

import mpmath as mp

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
    REPO_ROOT,
)

DATA_DIR = DATA_ROOT / "paper_b_audit"


mp.mp.dps = 60


def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True).strip()
    except Exception:  # pragma: no cover
        return "unknown"


# ----------------------------------------------------------------------------------------------
# Basic objects (all mpmath at 60 digits; floors taken exactly on the mp values)
# ----------------------------------------------------------------------------------------------


def X_of(n: int) -> mp.mpf:
    return mp.power(mp.mpf(n), mp.mpf(3) / 2)


def m_of(n: int) -> int:
    return math.isqrt(n * n * n)


def Y_of(n: int) -> mp.mpf:
    m = m_of(n)
    return mp.power(mp.mpf(m), mp.mpf(3) / 2)


def v_of(n: int) -> int:
    m = m_of(n)
    return math.isqrt(m * m * m)


def frac(x: mp.mpf) -> mp.mpf:
    return x - mp.floor(x)


def theta_of(n: int) -> mp.mpf:
    return X_of(n) - m_of(n)


def theta2_of(n: int) -> mp.mpf:
    return Y_of(n) - v_of(n)


def c_of(n: int, k: int) -> mp.mpf:
    return mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(9) / 8)
