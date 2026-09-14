"""Digest a published artifact by its content, not by its line endings.

A SHA-256 printed beside an artifact is a claim a reader can check. Hashing raw
bytes makes that claim platform-specific: this repository is checked out with
``core.autocrlf``, so a data file is CRLF in a Windows working tree and LF in
the stored blob, and a digest recorded on Windows fails everywhere else. Paper C
printed such digests. CI, the first non-Windows machine ever to reach the
check, reported three mismatches on 14 September 2026 -- and a reviewer cloning
the repository on Linux would have seen exactly the same, which is the part
that mattered.

Normalising first is the convention ``tools/build_paper_a.py`` already uses for
its text inputs. It makes a published digest mean the content rather than the
checkout.

    python tools/artifact_digest.py <path> [<path> ...]

prints the digest of the concatenation, in the order given.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


def content_sha256(*payloads: bytes | Path) -> str:
    """SHA-256 over the payloads, line endings normalised, concatenated in order."""

    digest = hashlib.sha256()
    for payload in payloads:
        raw = payload.read_bytes() if isinstance(payload, Path) else payload
        digest.update(raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n"))
    return digest.hexdigest()


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    print(content_sha256(*(Path(a) for a in sys.argv[1:])))


if __name__ == "__main__":
    main()
