"""Kernel-gated verification of one candidate proof.

A candidate passes only if the file compiles with no errors, uses no ``sorry``,
and ``#print axioms`` reports nothing beyond Mathlib's three: ``propext``,
``Classical.choice``, ``Quot.sound``. ``native_decide`` fails the gate because
it adds ``Lean.ofReduceBool``. This is the probe the ``AxiomCheckPaper*.lean``
files run, applied to a single declaration.

Two ways to build the file:

* ``verify_in_place`` splices the candidate into a copy of the declaration's
  own source file, at the span the extractor recorded, with the probe right
  after it. Everything the original proof could see, the candidate sees:
  file-local definitions, private lemmas, simp attributes, options. This is
  the reference check. It costs a compile of the whole file.
* ``assemble`` + ``verify`` builds a stand-alone file from the record's
  imports, header context and statement. Cheaper, but a proof that uses
  anything defined earlier in the same file fails with "Function expected".
  Use it for declarations in fresh modules, such as ``sorry`` stubs.

v0 runs one ``lake env lean`` per candidate from ``formal/``. A REPL-backed
version that snapshots the environment before the declaration replaces these
functions without changing their signatures.
"""
from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal"
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS_LINE = re.compile(r"'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")
NO_AXIOMS_LINE = re.compile(r"'(?P<name>[^']+)' does not depend on any axioms")
ERROR_LINE = re.compile(r"^.*:\d+:\d+: error:", re.MULTILINE)
SHORT_NAME = re.compile(r"(?:theorem|lemma)\s+([^\s:({\[⦃⟨]+)")


def short_name(statement: str) -> str:
    """The identifier as declared, which resolves inside its own namespace."""
    m = SHORT_NAME.search(statement)
    if not m:
        raise ValueError("no theorem or lemma name in statement")
    return m.group(1)


def assemble(record: dict, proof: str) -> str:
    """A stand-alone Lean source for ``record`` with ``proof`` as its proof.

    The statement already carries the docstring and attributes, so nothing is
    inserted between context and declaration. The probe uses the full name.
    """
    parts = [record["imports"], record["context"], record["statement"] + proof]
    return "\n\n".join(p for p in parts if p) + f"\n\n#print axioms {record['name']}\n"


def splice(lines: list[str], span: list[int], statement: str, proof: str) -> str:
    """The source file with lines ``span`` (1-based, inclusive) replaced.

    The replacement is ``statement + proof`` followed by an axiom probe on the
    declaration's short name, so the probe runs in the same scope as the
    declaration and resolves private names too.
    """
    first, last = span
    body = statement + proof
    probe = f"\n\n#print axioms {short_name(statement)}\n"
    return "\n".join(lines[: first - 1] + [body + probe] + lines[last:]) + "\n"


def run_lean(source: str, formal_dir: Path, timeout: int) -> tuple[int | None, str]:
    tmp = tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8")
    try:
        tmp.write(source)
        tmp.close()
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", tmp.name],
                cwd=formal_dir,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return None, ""
    finally:
        Path(tmp.name).unlink(missing_ok=True)
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


def gate(returncode: int | None, out: str, timeout: int) -> tuple[bool, str, str]:
    """Apply the kernel and axiom gate to a compiler run."""
    if returncode is None:
        return False, f"timeout after {timeout}s", ""
    if returncode != 0 or ERROR_LINE.search(out):
        return False, "compile error", out
    if "declaration uses 'sorry'" in out:
        return False, "sorry", out
    if NO_AXIOMS_LINE.search(out):
        return True, "ok (no axioms)", out
    m = AXIOMS_LINE.search(out)
    if not m:
        return False, "no axiom report", out
    axioms = {a.strip() for a in m.group("axioms").split(",") if a.strip()}
    extra = axioms - OK_AXIOMS
    if extra:
        return False, "forbidden axioms: " + ", ".join(sorted(extra)), out
    return True, "ok", out


def verify(
    source: str, name: str, formal_dir: Path = FORMAL, timeout: int = 300
) -> tuple[bool, str, str]:
    """Compile a stand-alone ``source`` and gate it. Returns (passed, reason, output)."""
    rc, out = run_lean(source, formal_dir, timeout)
    return gate(rc, out, timeout)


def verify_in_place(
    record: dict, proof: str, root: Path = ROOT, timeout: int = 900
) -> tuple[bool, str, str]:
    """Splice ``proof`` into the record's own file and gate it.

    Returns (passed, reason, output). ``record`` needs ``file``, ``span`` and
    ``statement`` as written by the extractor.
    """
    lines = (root / record["file"]).read_text(encoding="utf-8").splitlines()
    source = splice(lines, record["span"], record["statement"], proof)
    rc, out = run_lean(source, root / "formal", timeout)
    return gate(rc, out, timeout)
