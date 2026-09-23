"""Output provenance records unknowns and detects corruption without asserting proofs."""
import importlib
import json
from pathlib import Path
import subprocess

import pytest

from research.experiments.provenance import (
    check_manifest, descriptor, recording_run, schema_errors, text_identity, write_manifest,
)
from research.experiments.table_io import write_rows


def make_run(tmp_path):
    source = tmp_path / "src/probe.py"
    source.parent.mkdir()
    source.write_text("print(42)\n", encoding="utf-8")
    directory = tmp_path / "data/research/juggler/example"
    directory.mkdir(parents=True)
    output = directory / "result.json"
    output.write_text('{"answer": 42}\n', encoding="utf-8")
    manifest = directory / "run.research.json"
    with recording_run(["python", "src/probe.py"]):
        write_manifest(manifest, root=tmp_path, programme="juggler", research_id="juggler/example",
                       scope="One finite example, n=42.", sources=[source], outputs=[output],
                       parameters={"n": 42})
    return manifest, source, output


def test_round_trip_unknown_git_state_and_changed_outputs(tmp_path):
    manifest, source, output = make_run(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    assert not schema_errors(payload)
    assert payload["source"]["revision"] is None and payload["source"]["dirty"] is None
    assert payload["generator"]["command"] == ["python", "src/probe.py"]
    assert not check_manifest(manifest, tmp_path, hashes=True)["errors"]
    source.write_text("print(43)\n", encoding="utf-8")
    stale = check_manifest(manifest, tmp_path, hashes=True)
    assert not stale["errors"] and any("Changed source" in w for w in stale["warnings"])
    output.write_text('{"answer": 43}\n', encoding="utf-8")
    assert any("Changed outputs" in e for e in check_manifest(manifest, tmp_path, hashes=True)["errors"])
    assert not check_manifest(manifest, tmp_path)["hashes_checked"]


def test_git_revision_and_dirty_state_are_real(tmp_path):
    subprocess.run(["git", "init", str(tmp_path)], check=True, capture_output=True)
    def git(*args):
        return subprocess.run(["git", "-c", f"safe.directory={tmp_path.as_posix()}",
                               "-c", "user.name=Test", "-c", "user.email=test@example.invalid", *args],
                              cwd=tmp_path, capture_output=True, text=True, check=True).stdout.strip()
    git("commit", "--allow-empty", "-m", "initial")
    manifest, _, _ = make_run(tmp_path)
    source = json.loads(manifest.read_text(encoding="utf-8"))["source"]
    assert source["revision"] == git("rev-parse", "HEAD")
    assert source["dirty"] is True


@pytest.mark.parametrize("bad_path", ["../escape.json", "/outside.json", "C:/private.json", "x\\file.json"])
def test_path_traversal_in_manifest_is_rejected(tmp_path, bad_path):
    manifest, _, _ = make_run(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["outputs"][0]["path"] = bad_path
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    assert check_manifest(manifest, tmp_path)["errors"]


def test_unsafe_artifact_root_missing_files_and_duplicate_paths(tmp_path):
    manifest, _, output = make_run(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["outputs"].append(payload["outputs"][0])
    assert any("Duplicate outputs" in error for error in schema_errors(payload))
    payload["outputs"].pop()
    payload["artifact_root"] = "../../../../../.."
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    assert any("escapes" in e for e in check_manifest(manifest, tmp_path)["errors"])
    payload["artifact_root"] = "."
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    output.unlink()
    assert any("Missing outputs" in e for e in check_manifest(manifest, tmp_path)["errors"])


def test_repeated_table_runs_preserve_data_and_record_provenance(tmp_path):
    first = write_rows([{"n": 1}], tmp_path, "example", parameters={"n": 1})
    second = write_rows([{"n": 2}], tmp_path, "example", parameters={"n": 2})
    assert first["jsonl"] != second["jsonl"]
    assert json.loads(Path(first["jsonl"]).read_text()) == {"n": 1}
    payload = json.loads(Path(second["provenance"]).read_text(encoding="utf-8"))
    assert payload["generator"]["parameters"] == {"n": 2}
    assert payload["generator"]["command"] is None
    assert payload["source"]["files"]


def test_schema_document_matches_writer_and_rejects_unsafe_paths(tmp_path):
    jsonschema = pytest.importorskip("jsonschema")
    schema = json.loads((Path(__file__).resolve().parents[2] /
                         "data/schemas/research-output-v2.schema.json").read_text())
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema, format_checker=jsonschema.FormatChecker())
    manifest, _, _ = make_run(tmp_path)
    payload = json.loads(manifest.read_text())
    validator.validate(payload)
    for field, value in (("programme", []), ("created_utc", "not-a-time"),
                         ("research_id", "collatz/wrong_programme")):
        bad = dict(payload, **{field: value})
        assert list(validator.iter_errors(bad)) and schema_errors(bad)
    for bad_path in ("../escape", "dir/../escape", "/absolute", "C:/private", "dir\\file"):
        payload["outputs"][0]["path"] = bad_path
        assert list(validator.iter_errors(payload)) and schema_errors(payload)


def test_input_integrity_and_invalid_stems(tmp_path):
    manifest, _, output = make_run(tmp_path)
    payload = json.loads(manifest.read_text())
    payload["inputs"] = [dict(payload["outputs"][0], path=output.relative_to(tmp_path).as_posix())]
    manifest.write_text(json.dumps(payload))
    output.write_text('{"answer": 43}\n')
    assert any("Changed inputs" in e for e in check_manifest(manifest, tmp_path, hashes=True)["errors"])
    with pytest.raises(ValueError, match="filename component"):
        write_rows([{"n": 1}], tmp_path, "../escape")


def test_text_inputs_accept_only_explicit_newline_equivalence(tmp_path):
    manifest, source, _ = make_run(tmp_path)
    source.write_bytes(b'print(42)\r\n')
    payload = json.loads(manifest.read_text())
    payload['inputs'] = [descriptor(source, tmp_path, text=True)]
    manifest.write_text(json.dumps(payload))
    source.write_bytes(b'print(42)\n')
    result = check_manifest(manifest, tmp_path, hashes=True)
    assert not result['errors']
    assert any('Text representation changed for inputs' in w for w in result['warnings'])
    source.write_bytes(b'print(43)\n')
    assert any('Changed inputs' in e for e in check_manifest(manifest, tmp_path, hashes=True)['errors'])


def test_legacy_manifests_and_outputs_remain_byte_exact(tmp_path):
    manifest, source, output = make_run(tmp_path)
    payload = json.loads(manifest.read_text())
    payload['schema'] = 'btlab-output/v1'
    for entry in payload['source']['files']:
        entry.pop('text', None)
    source.write_bytes(b'print(42)\r\n')
    payload['inputs'] = [descriptor(source, tmp_path)]
    manifest.write_text(json.dumps(payload))
    source.write_bytes(b'print(42)\n')
    assert any('Changed inputs' in e for e in check_manifest(manifest, tmp_path, hashes=True)['errors'])
    payload['schema'] = 'btlab-output/v2'
    payload['outputs'][0]['text'] = text_identity(output)
    assert any('only allowed' in e for e in schema_errors(payload))
    payload['outputs'][0].pop('text')
    output.write_bytes(output.read_bytes().replace(b'\r\n', b'\n') + b'\r\n')
    manifest.write_text(json.dumps(payload))
    assert any('Changed outputs' in e for e in check_manifest(manifest, tmp_path, hashes=True)['errors'])


def test_text_metadata_cannot_mask_corruption(tmp_path):
    manifest, source, _ = make_run(tmp_path)
    payload = json.loads(manifest.read_text())
    payload['source']['files'][0]['text']['sha256'] = '0' * 64
    manifest.write_text(json.dumps(payload))
    assert any('Inconsistent text fingerprint' in e for e in check_manifest(manifest, tmp_path, hashes=True)['errors'])
    source.write_bytes(b'\xff\0')
    assert 'text' not in descriptor(source, tmp_path, text=True)


@pytest.mark.parametrize('changed', [b'\xef\xbb\xbfx\n', b'x \n', b'x\r'])
def test_text_identity_preserves_bom_whitespace_and_lone_cr(tmp_path, changed):
    source = tmp_path / 'text.md'
    source.write_bytes(b'x\n')
    original = text_identity(source)
    source.write_bytes(changed)
    assert text_identity(source) != original


@pytest.mark.parametrize("via_lab", [False, True])
def test_cli_records_the_checkout_bound_runner_when_present(tmp_path, monkeypatch, via_lab):
    cli = importlib.import_module("cli.main")
    argv = ["collatz", "dual-dataset", "--length", "1", "--max-k", "2", "--write"]
    expected = ["python", "tools/lab.py", "run", "cli.main", *argv] if via_lab else [
        "python", "-m", "cli.main", *argv]
    if via_lab:
        monkeypatch.setenv("BTLAB_RUN_COMMAND", json.dumps(expected))
    else:
        monkeypatch.delenv("BTLAB_RUN_COMMAND", raising=False)
    output = tmp_path / "result.json"
    output.write_text('{"n": 1}')
    manifest = tmp_path / "run.research.json"

    def generate(_args):
        write_manifest(manifest, root=tmp_path, programme="collatz",
                       scope="One integer", outputs=[output])
        return 0

    monkeypatch.setattr(cli, "run_collatz", generate)
    assert cli.main(argv) == 0
    assert json.loads(manifest.read_text())["generator"]["command"] == expected
