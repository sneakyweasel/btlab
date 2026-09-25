"""Paper E's finite checker: a changed proof input or printed table cannot pass."""
from __future__ import annotations

from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests/unit"))
from check_paper_e import check as check_mathematics  # noqa: E402
from test_build_paper import copy_release  # noqa: E402


@pytest.fixture
def release(tmp_path):
    copy_release("e", tmp_path)
    return tmp_path


def test_the_copied_release_passes(release):
    check_mathematics(release)


@pytest.mark.parametrize("module", [
    "formal/Problems/Collatz/PreimageGrid.lean",
    "formal/Problems/Juggler/PaperECompletion.lean",
    "formal/Problems/Juggler/PaperERecurrence.lean",
    "formal/BTCalculus/FejerBox.lean",
    "formal/Problems/Juggler/OOEEffectiveReturn.lean",
    "formal/Problems/Collatz/FibreSignCoupling.lean",
])
def test_changed_transitive_proof_requires_new_audit(release, module):
    proof = release / module
    proof.write_text(proof.read_text(encoding="utf-8") + "\n-- changed proof input\n", encoding="utf-8")
    with pytest.raises(ValueError, match="Lean proof inputs changed"):
        check_mathematics(release)


def test_printed_grid_cannot_drift_from_formal_table(release):
    source = release / "docs/theory/juggler_signed_collatz_note.md"
    source.write_text(source.read_text(encoding="utf-8").replace("10000 10140 10281", "10000 10141 10281"),
                      encoding="utf-8")
    with pytest.raises(ValueError, match="printed cap table"):
        check_mathematics(release)
