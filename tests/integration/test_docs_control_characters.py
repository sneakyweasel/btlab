r"""Guard the prose against ASCII control characters.

Patching documentation through a Python string is routine here, and it has a
silent failure mode: in a non-raw string ``"\theta"`` is not six characters,
it is TAB followed by ``heta``. The same happens to ``\v`` (``\varepsilon``),
``\f`` (``\frac``), ``\b`` (``\beta``), ``\a`` and ``\r``. Python warns only
for escapes that *fail* -- ``\(``, ``\l`` -- never for the ones that quietly
succeed, so nothing downstream complains and the LaTeX simply stops rendering.

Thirteen such characters accumulated across several sessions before anyone
measured them. The other documentation gates here check links, mirrors and
numbering; none of them looks at whether the bytes are text. This one does,
and it is the cheapest possible check: no tracked Markdown file may contain a
control character other than the line ending.

The fix when this fails is never to delete the character. Work out from
context which command was meant -- TAB before ``heta`` is ``\theta``, VT
before ``arepsilon`` is ``\varepsilon``, FF before ``ate_contagion`` is the
filename ``fate_contagion`` and wants a literal ``f``, not a backslash --
and restore it at the byte level. Then write the patch with raw strings
(``r"..."``) or from a scratch ``.py`` file rather than an inline heredoc.
"""

from __future__ import annotations

import pathlib
import subprocess

REPO = pathlib.Path(__file__).resolve().parents[2]

# Line endings only. Everything else below 0x20 is damage.
ALLOWED = frozenset({0x0A, 0x0D})

NAMES = {
    0x07: r"BEL  -- probably \a, from \alpha or \asymp",
    0x08: r"BS   -- probably \b, from \beta or a regex word boundary",
    0x09: r"TAB  -- probably \t, from \theta, \times, \tfrac or \text",
    0x0B: r"VT   -- probably \v, from \varepsilon, \varrho or \vdots",
    0x0C: r"FF   -- probably \f, from \frac (or a filename starting with f)",
}


def _tracked_markdown() -> list[pathlib.Path]:
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.md"],
        cwd=REPO,
        capture_output=True,
        check=True,
    ).stdout
    return [REPO / name.decode() for name in out.split(b"\x00") if name]


def _report(path: pathlib.Path, blob: bytes, index: int, note: str) -> str:
    line = blob.count(b"\n", 0, index) + 1
    context = blob[max(0, index - 60):index + 60].decode("utf-8", "replace")
    return (
        f"{path.relative_to(REPO).as_posix()}:{line} (byte {index}) {note}\n"
        f"    ...{context!r}..."
    )


def test_no_control_characters_in_tracked_markdown():
    """No tracked Markdown carries a control character beyond the newline."""
    files = _tracked_markdown()
    assert files, "expected tracked Markdown files"

    damage: list[str] = []
    for path in files:
        if not path.is_file():
            continue
        blob = path.read_bytes()
        for index, char in enumerate(blob):
            if char < 0x20 and char not in ALLOWED:
                note = NAMES.get(char, f"0x{char:02x} -- unexpected control character")
                damage.append(_report(path, blob, index, note))

    assert damage == [], (
        "Control characters in Markdown, almost certainly LaTeX written into a "
        "non-raw Python string. Restore the intended command; do not delete the "
        "byte. See this module's docstring.\n\n" + "\n".join(damage)
    )


def test_no_stray_carriage_return_in_tracked_markdown():
    r"""A lone CR is the same bug wearing the line ending as a disguise.

    ``\r`` in a non-raw string becomes a carriage return, which reads back as
    a real line break under universal newlines and beheads the word after it
    (``\research`` -> a line starting ``esearch``). The scan above cannot see
    it, because CR is a legitimate line ending here. A CR *not* followed by LF
    is not. Note that a later CRLF normalisation pass can mask this, so it is
    a cheap backstop rather than a complete one.
    """
    damage: list[str] = []
    for path in _tracked_markdown():
        if not path.is_file():
            continue
        blob = path.read_bytes()
        for index, char in enumerate(blob):
            if char == 0x0D and blob[index + 1:index + 2] != b"\n":
                damage.append(_report(path, blob, index, r"lone CR -- probably \r"))

    assert damage == [], (
        "Carriage return not part of a line ending:\n" + "\n".join(damage)
    )
