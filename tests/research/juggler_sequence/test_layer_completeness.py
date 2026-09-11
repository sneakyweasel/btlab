"""Gates that apply to every Juggler module, not only the registered ones.

`test_layer_architecture` checks the modules listed in `LAYERS`. Modules on disk but outside
that list inherit no gate, so a `sorry` in one of them would not be caught by anything except
the Paper B sorry test, which covers six of them by name. These two tests close that: the
first over every file, the second over the namespace convention, so a deviation cannot spread
silently.
"""

from __future__ import annotations

import importlib.util
import io
import re
from pathlib import Path

from research.juggler_sequence.lean_paths import LAYERS

ROOT = Path(__file__).resolve().parents[3]
JUGGLER = ROOT / "formal" / "Problems" / "Juggler"
INCOMPLETE = ("sorry", "admit", "axiom")

_spec = importlib.util.spec_from_file_location("layer_trust_boundary", ROOT / "tools/trust_boundary.py")
TB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TB)

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


def foreign_public_declarations(source: str, prefix: str) -> list[tuple[str, int]]:
    """Check resolved public identities, not each relative namespace command."""
    return [(name, line) for name, line in TB.source_declarations(source)
            if not name.startswith(prefix + ".")]


def test_namespace_convention_holds_except_where_pinned() -> None:
    """Public declarations stay in the project namespace, allowing nested scopes."""
    violations = {}
    nonstandard = set()
    for path in modules():
        src = path.read_text(encoding="utf-8")
        expected = "Juggler" if path.stem in NON_STANDARD_ROOT else "Problems.Juggler"
        foreign = foreign_public_declarations(src, expected)
        if foreign:
            violations[path.name] = foreign
        if foreign_public_declarations(src, "Problems.Juggler"):
            nonstandard.add(path.stem)
    assert not violations, violations
    assert nonstandard == NON_STANDARD_ROOT, sorted(nonstandard)


def test_namespace_audit_resolves_nesting_and_rejects_root_escapes() -> None:
    source = """namespace Problems
namespace Juggler
section parameters
namespace CubicGrid
theorem local_result : True := by trivial
end CubicGrid
end parameters
theorem RootCells.fact : True := by trivial
theorem _root_.Other.escaped : True := by trivial
end Juggler
end Problems
"""
    assert foreign_public_declarations(source, "Problems.Juggler") == [("Other.escaped", 9)]
    # A pinned module is permitted in Juggler, not in arbitrary foreign namespaces.
    pinned = "namespace Juggler\ntheorem fact : True := by trivial\nend Juggler\n"
    assert foreign_public_declarations(pinned, "Juggler") == []
    assert foreign_public_declarations(pinned.replace("Juggler", "Unrelated"), "Juggler") == [
        ("Unrelated.fact", 2)
    ]
