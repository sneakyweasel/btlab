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

from research.juggler_sequence.lean_registry import AUXILIARY_MODULES, LAYERS

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


def incomplete_tokens(source: str) -> set[str]:
    """Inspect executable source, not explanatory comments or string literals."""
    masked = '\n'.join(TB.source_commands(source))
    return {token for token in INCOMPLETE
            if re.search(rf"(?<![A-Za-z0-9_]){token}(?![A-Za-z0-9_])", masked)}


def test_every_module_on_disk_is_complete() -> None:
    """Not only the ones in LAYERS: the gate should not depend on registration."""
    assert modules(), "no Juggler modules found"
    for path in modules():
        src = io.open(path, encoding="utf-8", errors="replace").read()
        assert not incomplete_tokens(src), f"{path.name} contains {incomplete_tokens(src)}"


def test_completeness_masks_comments_but_rejects_actual_proof_holes():
    prose = '/- No axiom. /- No sorry. -/ -/\n-- admit is forbidden\ndef note := "sorry"\n'
    assert incomplete_tokens(prose) == set()
    assert incomplete_tokens(prose + 'theorem bad : False := by sorry\n') == {'sorry'}
    assert incomplete_tokens('theorem bad : False := by /- checked? -/ admit\n') == {'admit'}
    assert incomplete_tokens('/- proof obligation -/ axiom bad : False\n') == {'axiom'}


def test_unregistered_modules_are_visible() -> None:
    """A module outside LAYERS is not an error, but it should not be a surprise either:
    this records how many there are so a drift shows up in the diff."""
    on_disk = {p.stem for p in modules()}
    outside = sorted(on_disk - set(LAYERS))
    # Six are Paper B modules with their own sorry test; the rest are support modules.
    # Raised 20 -> 23 on 16 September 2026: the eight PaperB* research modules written
    # over the psi/barrier sessions were on disk but in no inventory, so this gate and
    # test_every_juggler_source_has_an_explicit_inventory_role were both red. They are
    # now in AUXILIARY_MODULES with roles; this budget records the new resting count.
    # 23 -> 25 the same day: PaperBAmplitudeCocycle and PaperBTailSpectrum, both
    # registered with the rest.
    # 28 -> 29 on 17 September 2026: PaperBCertificates (Lemma 5.1), kept outside
    # the Paper B barrel because it imports the itinerary stack shared with Paper A.
    # 29 -> 30 on 17 September 2026: PaperBSurvivorDecay (the Theorem 6.1 count decay),
    # outside the barrel for the same reason (it imports RateFreeDensity).
    # 30 -> 32 on 18 September 2026, both outside the barrel for that same reason:
    # PaperBSurvivorAsymptotic (the exact-rate skeleton, imports PaperBSurvivorDecay)
    # and PaperBFiveStepDensity (the Theorem 5.2-5.4 count assembly, imports
    # RateFreeDensity and PaperBCertificates). Both are in AUXILIARY_MODULES.
    # 32 -> 33 on 18 September 2026: PaperBCertificateLengths, which generalises
    # Lemma 5.1 to every length and imports PaperBCertificates for its five words.
    # 33 -> 34 on 18 September 2026: PaperBCertificateRecursion, the one-step
    # decomposition tying neverNegCount to minimalCertCount; imports both neighbours.
    # 34 -> 38 on 20 September 2026, four at once, which is itself the drift this gate
    # exists to surface: two days of multi-session output outran a budget nobody re-set.
    # All four carry roles in AUXILIARY_MODULES and all four are outside the Paper B
    # barrel for the usual reason, that they import the itinerary stack or RateFreeDensity.
    #   PaperBJumpTransposition  (18 Sep) the barrier-transposition cost, on an abstract
    #     graded Profile rather than a word set;
    #   CollatzBridgeLab         (19 Sep) the bridge lab extensions, kept out of Paper A's
    #     barrel so that barrel stays kernel-only;
    #   FateProductionWords      (19 Sep) Paper C's six production words and their
    #     prefix-freeness;
    #   PaperBLevelWindow        (19 Sep) the empty-window theorem at every level, which
    #     imports PaperBCertificateLengths, RateFreeDensity and LogCells.
    # 38 -> 37 on merging claude/elated-hopper-e20999, and the two sides of that merge
    # each knew half of it. Main had counted FateProductionWords among the four above,
    # in AUXILIARY_MODULES. The branch moved it the other way, into LAYERS, because
    # wiring it into Paper C's barrel made it a publication-layer module like every
    # other Fate* module -- so on the branch the count went 37 -> 36, and the branch's
    # note says that -1 is the only part of the delta its pass was responsible for.
    # The branch did not know about PaperBLevelWindow, which main added on 19 September
    # and which is still outside. Neither side's number survives the merge: 38 counts
    # FateProductionWords as outside when it no longer is, and 36 omits PaperBLevelWindow
    # entirely. Measured on the merged tree: 207 modules on disk, 170 in LAYERS, 37
    # outside. The budget is the measurement, not either side's arithmetic.
    # Exact role registration supersedes the historical count budget: adding an
    # anonymous module fails even when another module is removed at the same time.
    assert set(outside) == set(AUXILIARY_MODULES), outside
    assert all(AUXILIARY_MODULES.values()), "every auxiliary module needs an explicit role"


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
