"""The forbidden-engine guard must match a declaration, not a prefix of one.

`FORBIDDEN_ENGINES` lists `Energy`. On 14 September 2026 `def EnergyBound`
landed in `FateEnergyAtoms.lean` and the three residual probes, which tested
the guard with `f"def {name}" in combined`, all flipped to `*_INCOMPLETE`:
six failures from one substring collision, with nothing forbidden added.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence.future_quotient import lean_api_present as fq_lean
from research.juggler_sequence.lean_paths import declares_name, juggler_text
from research.juggler_sequence.residual_minimize import lean_api_present as rm_lean
from research.juggler_sequence.residual_state import lean_api_present as rs_lean


def test_declares_name_rejects_a_longer_name():
    assert declares_name("def Energy (n : Nat) : Nat := n", "Energy") is True
    assert declares_name("def EnergyBound (N : Nat) : Prop := True", "Energy") is False


def test_declares_name_honours_the_kind():
    assert declares_name("structure Energy where", "Energy") is True
    assert declares_name("theorem Energy_pos : True", "Energy") is False


def test_energy_bound_is_declared_and_is_not_forbidden():
    """The live collision, pinned: the declaration exists and must not fire."""
    corpus = juggler_text()
    assert declares_name(corpus, "EnergyBound") is True
    assert declares_name(corpus, "Energy") is False


@pytest.mark.parametrize("lean_api_present", [rs_lean, fq_lean, rm_lean])
def test_residual_probes_report_no_forbidden_engine(lean_api_present):
    lean = lean_api_present()
    assert lean["forbidden_hits"] == []
    assert lean["no_forbidden_engines"] is True
