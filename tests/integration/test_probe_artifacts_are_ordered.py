"""Committed probe artifacts must not encode set iteration order.

Two payload fields serialised a frozenset and a set difference straight to
JSON. Both orders are PYTHONHASHSEED-dependent, so every probe run reshuffled
them and the churn rode into unrelated commits -- one of which contains
nothing but the reshuffle. These fields are sorted at the source; this pins
the committed artifacts to the sorted order so a reintroduction is a test
failure rather than a diff nobody reads.
"""

from __future__ import annotations

import json

from research.research_control.symbolic_composition_phase3 import (
    JSON_PATH as PHASE3_JSON,
)
from research.research_control.reverse_add_weighted_pair_phase7 import (
    JSON_PATH as PHASE7_JSON,
)


def test_not_in_default_order_is_sorted():
    payload = json.loads(PHASE3_JSON.read_text(encoding="utf-8"))
    values = payload["not_in_default_order"]
    assert values == sorted(values), values


def test_experimental_attacks_is_sorted():
    payload = json.loads(PHASE3_JSON.read_text(encoding="utf-8"))
    values = payload["experimental_attacks"]
    assert values == sorted(values), values


def test_stored_statistics_is_sorted():
    payload = json.loads(PHASE7_JSON.read_text(encoding="utf-8"))
    values = payload["tautology_checks"]["stored_statistics"]
    assert values == sorted(values), values
