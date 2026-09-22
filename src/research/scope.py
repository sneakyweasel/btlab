"""The active research programmes; historical descriptors require explicit opt-in."""
from __future__ import annotations

import os

ACTIVE_RESEARCH = ('juggler_sequence', 'collatz', 'collatz_finite_descent', 'syracuse')


def include_archive() -> bool:
    return os.environ.get('BTLAB_INCLUDE_ARCHIVE') == '1'
