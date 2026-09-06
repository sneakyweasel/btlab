"""Suite options: skip exhaustive census / UI / million-range tests by default."""

from __future__ import annotations

import pytest


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption(
        "--runslow",
        action="store_true",
        default=False,
        help="run exhaustive census, million-range, and Streamlit AppTests",
    )


def pytest_collection_modifyitems(
    config: pytest.Config, items: list[pytest.Item]
) -> None:
    if config.getoption("--runslow"):
        return
    skip_slow = pytest.mark.skip(reason="slow; pass --runslow to include")
    for item in items:
        if "slow" in item.keywords:
            item.add_marker(skip_slow)


@pytest.fixture(autouse=True)
def _mpmath_precision_is_not_shared_state() -> "object":
    """Restore mpmath's global precision after every test.

    Several modules set ``mp.dps`` inside a test body and leave it there -- 30 in the Paper B
    audit tests, 40 and 100 in the prefix-count tests -- while others assert to 1e-42 and 1e-45
    against the 60 digits their import set up.  Whether that collides depends on which xdist
    worker draws which test, so the suite was green by distribution rather than by construction.
    """

    import mpmath as mp

    before = mp.mp.dps
    yield
    mp.mp.dps = before
