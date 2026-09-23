"""Default research output locations in the checkout providing the code."""

from pathlib import Path


def collatz_data_dir() -> Path:
    """Locate Collatz results independently of the caller's working directory."""
    return Path(__file__).resolve().parents[3] / "data" / "research" / "collatz"
