"""Compile consumer proofs for the cubic orbit interfaces and check their trust scope."""
from __future__ import annotations

from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
CONSUMERS = {
    "Problems.Juggler.InterfaceChecks.legacy_terminal_entry",
    "Problems.Juggler.InterfaceChecks.legacy_charge_entry",
    "Problems.Juggler.InterfaceChecks.certificate_nonlinear_charge",
    "Problems.Juggler.InterfaceChecks.certificate_terminal_totals",
    "Problems.Juggler.InterfaceChecks.shared_terminal_totals",
    "Problems.Juggler.InterfaceChecks.terminal_word_cutoff",
    "Problems.Juggler.InterfaceChecks.leftover_gap_height",
    "Problems.Juggler.InterfaceChecks.leftover_deviation_from_certificate",
}
STANDARD_DEPENDENCIES = {"propext", "Classical.choice", "Quot.sound"}
RECORD = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.MULTILINE,
)


def check_dependency_records(output: str, names: set[str]) -> None:
    """Every requested consumer is present exactly once with an allowed dependency set."""
    records = {}
    for match in RECORD.finditer(output):
        name = match.group(1)
        assert name not in records, f"Repeated dependency record: {name}"
        dependencies = {item.strip() for item in (match.group(2) or "").split(",")
                        if item.strip()}
        assert dependencies <= STANDARD_DEPENDENCIES, (name, dependencies)
        records[name] = dependencies
    assert set(records) == names, (set(records), names)
    assert not RECORD.sub("", output).strip(), output


def test_cubic_interface_consumers_compile() -> None:
    """The proof inputs contain ordinary period evidence, not the desired new conclusions."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run([lake, "env", "lean", "InterfaceCheckJuggler.lean"],
                            cwd=ROOT / "formal", capture_output=True, text=True,
                            encoding="utf-8", errors="replace", timeout=600)
    assert result.returncode == 0, (result.stdout + result.stderr)[-8000:]
    assert not result.stderr.strip(), result.stderr
    check_dependency_records(result.stdout, CONSUMERS)


@pytest.mark.parametrize("dependencies", ["", "propext", "propext, Classical.choice, Quot.sound"])
def test_consumer_dependency_subsets_are_accepted(dependencies: str) -> None:
    check_dependency_records(f"'Control.result' depends on axioms: [{dependencies}]\n",
                             {"Control.result"})


def test_consumer_dependency_output_can_wrap() -> None:
    check_dependency_records("'Control.result' depends on axioms: [propext,\n"
                             "  Classical.choice, Quot.sound]\n", {"Control.result"})


@pytest.mark.parametrize("dependencies", ["Unexpected.foundation", "Lean.ofReduceBool"])
def test_consumer_extra_dependencies_are_rejected(dependencies: str) -> None:
    with pytest.raises(AssertionError):
        check_dependency_records(f"'Control.result' depends on axioms: [propext, {dependencies}]\n",
                                 {"Control.result"})


def test_consumer_missing_or_repeated_records_are_rejected() -> None:
    record = "'Control.result' depends on axioms: [propext]\n"
    with pytest.raises(AssertionError):
        check_dependency_records("", {"Control.result"})
    with pytest.raises(AssertionError):
        check_dependency_records(record * 2, {"Control.result"})


def test_consumer_empty_dependency_record_is_accepted() -> None:
    check_dependency_records("'Control.result' does not depend on any axioms\n",
                             {"Control.result"})
