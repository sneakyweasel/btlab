"""Suite options: skip exhaustive census / UI / million-range tests by default."""

from __future__ import annotations

import pytest
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCOPE = json.loads((ROOT / 'data/lab_scope.json').read_text(encoding='utf-8'))


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption('--include-archive', action='store_true', default=False,
                     help='also collect frozen projects outside the Juggler/Collatz lab')
    parser.addoption(
        "--runslow",
        action="store_true",
        default=False,
        help="run exhaustive census, million-range, and Streamlit AppTests",
    )


def pytest_ignore_collect(collection_path: Path, config: pytest.Config) -> bool | None:
    if config.getoption('--include-archive'):
        return None
    relative = collection_path.relative_to(ROOT).as_posix()
    if relative in SCOPE['archived_test_files']:
        return True
    parts = relative.split('/')
    if len(parts) >= 3 and parts[:2] == ['tests', 'research']:
        if parts[2] in SCOPE['archived_research']:
            return True
    return None


def pytest_report_header(config: pytest.Config) -> str:
    return ('scope: full historical library' if config.getoption('--include-archive') else
            'scope: Juggler/Collatz and shared dependencies; --include-archive restores historical tests')


def pytest_configure(config: pytest.Config) -> None:
    config._lab_archive_previous = os.environ.get('BTLAB_INCLUDE_ARCHIVE')
    if config.getoption('--include-archive'):
        os.environ['BTLAB_INCLUDE_ARCHIVE'] = '1'


def pytest_unconfigure(config: pytest.Config) -> None:
    previous = getattr(config, '_lab_archive_previous', None)
    if previous is None:
        os.environ.pop('BTLAB_INCLUDE_ARCHIVE', None)
    else:
        os.environ['BTLAB_INCLUDE_ARCHIVE'] = previous


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
