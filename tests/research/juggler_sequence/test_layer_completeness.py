"""Gates that apply to every Juggler module, not only the registered ones.

`test_layer_architecture` checks the modules listed in `LAYERS`. Modules on disk but outside
that list inherit no gate, so a `sorry` in one of them would not be caught by anything except
the Paper B sorry test, which covers six of them by name. These two tests close that: the
first over every file, the second over the namespace convention, so a deviation cannot spread
silently.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

from research.juggler_sequence.lean_paths import LAYERS

ROOT = Path(__file__).resolve().parents[3]
JUGGLER = ROOT / "formal" / "Problems" / "Juggler"
INCOMPLETE = ("sorry", "admit", "axiom")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z0-9_.']+)", re.MULTILINE)

# Two modules declare into `Juggler.*` rather than the project root `Problems.Juggler.*`.
# Pinned rather than fixed: both are inside Paper A's review object, so a rename touches the
# manuscript's cited names. A third deviation should fail here and be a deliberate choice.
NON_STANDARD_ROOT = {"FanLaw", "DepthFourFive"}


def modules() -> list[Path]:
    return sorted(JUGGLER.glob("*.lean"))


def test_every_module_on_disk_is_complete() -> None:
    """Not only the ones in LAYERS: the gate should not depend on registration."""
    assert modules(), "no Juggler modules found"
    for path in modules():
        src = io.open(path, encoding="utf-8", errors="replace").read()
        for token in INCOMPLETE:
            hit = re.search(rf"(?<![A-Za-z0-9_]){token}(?![A-Za-z0-9_])", src)
            assert hit is None, f"{path.name} contains {token}"


def test_unregistered_modules_are_visible() -> None:
    """A module outside LAYERS is not an error, but it should not be a surprise either:
    this records how many there are so a drift shows up in the diff."""
    on_disk = {p.stem for p in modules()}
    outside = sorted(on_disk - set(LAYERS))
    # Six are Paper B modules with their own sorry test; the rest are support modules.
    assert len(outside) <= 20, outside


def test_namespace_convention_holds_except_where_pinned() -> None:
    """Every module declares into `Problems.Juggler` except the two pinned above."""
    offenders = set()
    for path in modules():
        src = io.open(path, encoding="utf-8", errors="replace").read()
        roots = {n.split(".")[0] for n in NAMESPACE.findall(src)}
        if roots and roots != {"Problems"}:
            offenders.add(path.stem)
    assert offenders == NON_STANDARD_ROOT, sorted(offenders)
