"""Research retrieval must preserve authority, boundaries, and live source changes."""
import json
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from research_catalog import ResearchCatalogue


def write(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


@pytest.fixture
def repo(tmp_path):
    write(tmp_path, "docs/problems/juggler_example.md", """# Exact example
## Problem
Can mixed-pair descent hold?
## Experiments
`src/research/juggler_sequence/probe.py`
`tests/research/juggler_sequence/test_probe.py`
## Decision
**CLOSE**. This obstruction does not PROMOTE a new branch.
## Open questions
An arithmetic input remains open.
""")
    write(tmp_path, "src/research/juggler_sequence/probe.py", "# probe\n")
    write(tmp_path, "tests/research/juggler_sequence/test_probe.py", "# test\n")
    write(tmp_path, "src/research/juggler_sequence/branch_index.py", """
DOSSIER_ALIASES: dict[str, str] = {"probe": "example"}
SLOGAN_ALIASES: dict[str, str] = {"old slogan": "probe"}
""")
    write(tmp_path, "docs/problems/collatz_example.md", """# Another example
## Problem
Is this implication justified?
See [Juggler](juggler_example.md).
## Decision
**PARK** pending the missing input.
""")
    write(tmp_path, "docs/negative_knowledge.md", """# Negative knowledge
## Exact obstruction
[Example](problems/juggler_example.md): a counterexample rules this out.
""")
    write(tmp_path, "formal/Problems/Juggler/Example.lean", "theorem example : True := trivial\n")
    write(tmp_path, "docs/theory/theorem_ledger.json", json.dumps([{
        "id": "J-example", "tag": "EXACT — HUMAN PROOF", "statement": "Conditional result",
        "source": "docs/problems/juggler_example.md", "tests": [],
        "lean": "formal/Problems/Juggler/Example.lean", "decl": ["Example.example"],
    }]))
    return tmp_path


def test_aliases_decisions_and_negative_knowledge_come_from_canonical_sources(repo):
    catalogue = ResearchCatalogue(repo)
    overview = catalogue.context("old slogan")
    assert overview["id"] == "juggler/example"
    assert overview["items"][0]["decision"] == "CLOSE"
    assert overview["items"][0]["decision_source"]["line"] == 7
    obstructions = catalogue.context("juggler/example", "obstructions")
    assert any(i["file"] == "docs/negative_knowledge.md" for i in obstructions["items"])
    claims = catalogue.context("juggler/example", "claims")
    assert claims["items"][0]["tag"] == "EXACT — HUMAN PROOF"
    assert claims["items"][0]["lookup"]["ledger_id"] == "J-example"
    assert catalogue.context("collatz/example", "claims")["total"] == 0
    assert "No tests" in claims["limitations"]


def test_ambiguous_ids_and_pagination_never_pick_an_arbitrary_branch(repo):
    catalogue = ResearchCatalogue(repo)
    ambiguous = catalogue.context("example", limit=1)
    assert ambiguous["status"] == "ambiguous"
    assert ambiguous["total"] == 2 and ambiguous["next_offset"] == 1
    result = catalogue.search("example", limit=1)
    second = catalogue.search("example", limit=1, offset=1, snapshot=result["snapshot"])
    assert second["items"][0]["id"] != result["items"][0]["id"]
    write(repo, "docs/problems/collatz_new.md", "# New example\n## Decision\nCLOSE\n")
    with pytest.raises(ValueError, match="snapshot changed"):
        catalogue.search("example", offset=1, snapshot=result["snapshot"])
    assert catalogue.context("collatz/new")["status"] == "found"


def test_unknown_decisions_and_missing_refs_are_explicit(repo):
    write(repo, "docs/problems/collatz_new.md", "# Unknown\n## Problem\nPROMOTE might happen.\n")
    catalogue = ResearchCatalogue(repo)
    assert catalogue.context("collatz/new")["items"][0]["decision"] is None
    first = catalogue.check()
    assert first["errors"] == 0 and first["warnings"] == 1
    (repo / "formal/Problems/Juggler/Example.lean").unlink()
    report = catalogue.check()
    assert report["snapshot"] != first["snapshot"]
    assert report["errors"] == 1
    assert any("Missing claim reference" in i["error"] for i in report["items"])


def test_duplicate_claim_ids_invalid_tags_and_metadata_fail_validation(repo):
    path = repo / "docs/theory/theorem_ledger.json"
    rows = json.loads(path.read_text(encoding="utf-8"))
    rows.append(dict(rows[0], tag="PROVED"))
    path.write_text(json.dumps(rows), encoding="utf-8")
    write(repo, "literature/incomplete.json", '{"id":"incomplete"}')
    result = ResearchCatalogue(repo).check()
    assert result["status"] == "failed"
    assert result["errors"] == 3


def test_output_is_bounded_and_untrusted_links_are_not_followed(repo):
    write(repo, "docs/problems/collatz_long.md", "# Long\n## Decision\nCLOSE\n" + "x" * 5000
          + "\n[private](../../../outside.txt)\n[web](https://example.com/)\n")
    catalogue = ResearchCatalogue(repo)
    detail = catalogue.context("collatz/long")
    assert detail["items"][0]["decision_source"]["truncated"]
    assert not catalogue.context("collatz/long", "sources")["items"]
    with pytest.raises(ValueError):
        catalogue.search("", limit=0)
    with pytest.raises(ValueError):
        catalogue.context("collatz/long", offset=-1)


def test_title_matches_rank_ahead_of_incidental_body_mentions(repo):
    write(repo, "docs/problems/collatz_aaa.md", "# Unrelated\n## Problem\nMixed-pair descent.\n## Decision\nPARK\n")
    write(repo, "docs/problems/collatz_zzz.md", "# Mixed-pair descent\n## Decision\nPROMOTE\n")
    assert ResearchCatalogue(repo).search("mixed descent")["items"][0]["id"] == "collatz/zzz"


def test_manifest_links_reproduction_and_detects_data_corruption(repo):
    from research.experiments.provenance import write_manifest
    output = write(repo, "data/research/juggler/example/result.json", '{"n": 3}')
    manifest = output.with_suffix(".research.json")
    write_manifest(manifest, root=repo, programme="juggler", research_id="juggler/example",
                   scope="One integer", parameters={"n": 3}, outputs=[output],
                   command=["python", "tools/lab.py", "run", "research.juggler_sequence.probe"])
    catalogue = ResearchCatalogue(repo)
    assert any(d.get("kind") == "manifest" for d in catalogue.context("juggler/example", "data")["items"])
    assert any(c["basis"] == "recorded generator invocation"
               for c in catalogue.context("juggler/example", "commands")["items"])
    assert catalogue.check(hashes=True)["errors"] == 0
    output.write_text('{"n": 4}')
    assert catalogue.check(hashes=True)["errors"] == 1
    payload = json.loads(manifest.read_text())
    payload["research_id"] = "juggler/missing"
    manifest.write_text(json.dumps(payload))
    assert any(i["error"] == "Unknown research_id" for i in catalogue.check()["items"])
    payload["research_id"] = ["juggler/example"]
    manifest.write_text(json.dumps(payload))
    assert catalogue.check()["status"] == "failed"


def test_private_bibliography_and_escape_links_are_not_indexed(repo):
    write(repo, "literature/notes.private.json", 'not valid JSON; deliberately private')
    assert ResearchCatalogue(repo).check()["errors"] == 0


def test_claim_statements_are_not_parsed_as_repository_links(repo):
    path = repo / "docs/theory/theorem_ledger.json"
    rows = json.loads(path.read_text(encoding="utf-8"))
    rows[0]["statement"] = "For all n, T^[3](n) > n; [notation](missing.md) is not a source."
    rows[0]["source"] += "\n[Proof note](../../docs/theory/proof.md)"
    write(repo, "docs/theory/proof.md", "# Proof note\n")
    path.write_text(json.dumps(rows), encoding="utf-8")
    catalogue = ResearchCatalogue(repo)
    sources = {s["path"] for s in catalogue.context("juggler/example", "sources")["items"]}
    assert "docs/theory/proof.md" in sources
    assert "docs/theory/n" not in sources and "docs/theory/missing.md" not in sources
    assert catalogue.search("notation")["total"] == 1
    assert catalogue.check()["errors"] == 0 and catalogue.check()["warnings"] == 0
    (repo / "docs/theory/proof.md").unlink()
    assert catalogue.check()["errors"] == 1
