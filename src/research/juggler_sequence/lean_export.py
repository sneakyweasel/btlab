"""Lean export names. Finite identities; not a halt theorem."""

from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    REPO_ROOT,
)

LEAN_MODULE = "Problems.Juggler"

THEOREMS = (
    "floorPower_one",
    "floorPower_thirteen_step",
    "floorPower_thirteen_reaches_one",
)

LEAN_PATH = JUGGLER_DIR.relative_to(REPO_ROOT).as_posix() + "/"
