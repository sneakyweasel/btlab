"""Local read-only MCP server. Install tools/requirements-formalpedia.txt with pip."""
from __future__ import annotations

import json
import hashlib
from pathlib import Path
from typing import Any, Literal

from mcp.server.fastmcp import FastMCP
from mcp.types import ToolAnnotations

import formalpedia as fp
from formalpedia_catalog import Catalogue
import lean_style
from research_catalog import ResearchCatalogue
from formalpedia_semantic import SemanticCatalogue

catalogue = Catalogue()
research = ResearchCatalogue()
semantic = SemanticCatalogue()
mcp = FastMCP('formalpedia', instructions=(
    'Search the local Lean library before proving a result. Resolve a fully qualified name, '
    'read its complete statement and hypotheses, and inspect exact claim links. '
    'Ambiguous names return candidates, never an arbitrary theorem. Source trust markers '
    'are not compilation or axiom-audit evidence. Use lean-lsp for goals, elaboration and '
    'proof checking. Use formalpedia_research_search and formalpedia_research_context to '
    'inspect Juggler/Collatz dossiers, decisions, known obstructions and data provenance. '
    'Use formalpedia_change_impact and formalpedia_verification_plan before maintenance; '
    'formalpedia_lab_doctor discovers local prerequisites. Execute checks through tools/lab.py. '
    'Use formalpedia_type_search and formalpedia_semantic_show for compiler-derived local '
    'types, formalpedia_dependencies for proof/type edges, and formalpedia_semantic_diff '
    'for historical changes. These require an explicit CLI semantic build and reject '
    'stale exports. Structural matches are not proof applicability. '
    'All tools here are local and read-only.'))
READ_ONLY = ToolAnnotations(readOnlyHint=True, destructiveHint=False,
                            idempotentHint=True, openWorldHint=False)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_search(query: str, namespace: str | None = None, module: str | None = None,
                      kind: str | None = None, ledger_id: str | None = None,
                      include_private: bool = False, include_deprecated: bool = False,
                      limit: int = 20, offset: int = 0,
                      scope: Literal['active', 'archive', 'all'] = 'active') -> dict[str, Any]:
    """Find reusable results by name, mathematical words, type symbols or exact ledger claim.

    Results carry qualified identities and compact statements. Use formalpedia_show for
    full hypotheses. Namespace is a prefix; module is an exact import name. Pagination
    is deterministic within a snapshot; restart at offset 0 if the snapshot changes.
    Searches the current Juggler/Collatz checkout and its shared mathematics. The scope
    filter does not read Git history; removed projects have no archive entries here.
    """
    return catalogue.search(query, namespace=namespace, module=module, kind=kind,
        ledger_id=ledger_id, include_private=include_private,
        include_deprecated=include_deprecated, limit=limit, offset=offset, scope=scope)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_show(name: str, module: str | None = None,
                    include_private: bool = False) -> dict[str, Any]:
    """Inspect a theorem's complete source statement, documentation, and exact claim links.

    Prefer the fully qualified id from search. Short names are accepted only when unique.
    File-level ledger associations are separately labelled and are not theorem coverage.
    """
    return catalogue.show(name, module=module, include_private=include_private)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_claim(ledger_id: str) -> dict[str, Any]:
    """Read a mathematical ledger claim beside every declaration it explicitly names.

    Missing or ambiguous references are exposed. A recorded claim tag is provenance,
    not a new statement-coverage judgment by this tool.
    """
    return catalogue.claim(ledger_id)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_impact(target: str, limit: int = 50, offset: int = 0) -> dict[str, Any]:
    """Find imports, dependent modules and affected paper roots before editing a declaration.

    Accepts a qualified declaration, import module or source path. Dependencies are
    module-level; this tool does not assert that every theorem uses every import.
    """
    return catalogue.impact(target, limit=limit, offset=offset)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_status() -> dict[str, Any]:
    """Check live index freshness, documentation coverage and naming ambiguities."""
    return catalogue.status()


@mcp.tool(annotations=READ_ONLY)
def formalpedia_capabilities() -> dict[str, Any]:
    """Identify this server version and tool groups; diagnose stale client discovery.

    The code fingerprint identifies this running process's loaded entry point, not a
    security attestation. A fresh connection is required to load edited server code.
    """
    return {'protocol_version': 2, 'server_fingerprint': SERVER_FINGERPRINT,
            'root': str(fp.ROOT), 'tool_groups': {
                'source': ['search', 'show', 'claim', 'impact', 'status', 'lint'],
                'research': ['research_search', 'research_context', 'research_check'],
                'maintenance': ['lab_doctor', 'change_impact', 'verification_plan'],
                'semantic': ['semantic_status', 'semantic_show', 'type_search', 'dependencies', 'semantic_diff']},
            'semantic': semantic.status(), 'read_only': True}


# Captured at import: editing the file does not pretend to update a running server.
SERVER_FINGERPRINT = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


@mcp.tool(annotations=READ_ONLY)
def formalpedia_semantic_status() -> dict[str, Any]:
    """Check compiler snapshot coverage, source/object freshness and rebuild instructions."""
    return semantic.status()


@mcp.tool(annotations=READ_ONLY)
def formalpedia_semantic_show(name: str, include_ast: bool = False) -> dict[str, Any]:
    """Inspect a compiled declaration's full type, binders, direct dependencies and axioms.

    Use module::fully.qualified.name when ambiguous. Private and generated names are
    real compiler identities. AST is alpha-normalized syntax, with de Bruijn indices.
    Does not infer English claim coverage or prove the type in a new environment.
    """
    return semantic.show(name, include_ast)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_type_search(constants: list[str] | None = None, like: str | None = None,
                           pattern: list[Any] | dict[str, Any] | None = None,
                           part: Literal['type', 'conclusion'] = 'type', kind: str | None = None,
                           module: str | None = None, include_private: bool = False,
                           limit: int = 20, offset: int = 0,
                           snapshot: str | None = None) -> dict[str, Any]:
    """Search elaborated local types by constants, an existing type, or a structural pattern.

    Constants are exact Lean names and all must occur in the type. `like` compares
    alpha-normalized syntax; it does not unfold definitions or unify universes.
    Patterns use the AST from semantic_show(include_ast=True); {"hole":"x"} matches
    a subtree, and repeating a hole requires the identical subtree. Conclusion-only
    matching omits hypotheses: ALWAYS inspect binders and use Lean LSP to check reuse.
    Stale exports and changed pagination snapshots are rejected, never rebuilt here.
    """
    return semantic.search(constants, like, pattern, part, kind, module, include_private,
                           limit, offset, snapshot)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_dependencies(name: str, direction: Literal['uses', 'used_by'] = 'uses',
                            edge: Literal['type', 'value', 'all'] = 'all', depth: int = 1,
                            limit: int = 30, offset: int = 0,
                            snapshot: str | None = None) -> dict[str, Any]:
    """Traverse direct compiler type/proof edges or reverse users (depth 1..5).

    Includes private/generated local declarations. External constants are leaves;
    an unindexed external constant can still depend on other local declarations.
    Axiom questions use semantic_show's transitive Lean-collected axioms.
    """
    return semantic.dependencies(name, direction, edge, depth, limit, offset, snapshot)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_semantic_diff(before: str, after: str | None = None,
                             limit: int = 20, offset: int = 0) -> dict[str, Any]:
    """Compare saved compiler snapshots and flag users of changed local definitions.

    Reports type, proof-hash, dependency and axiom changes, plus coverage differences.
    Proof hashes are noncryptographic change hints. Does not classify a statement as
    stronger/weaker, or certify that unchanged entries remain valid after source edits.
    `after` defaults to the current saved export, whose freshness is reported separately.
    """
    return semantic.diff(before, after, limit, offset)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_lint(limit: int = 30, offset: int = 0) -> dict[str, Any]:
    """List new naming/documentation violations against the reviewed legacy baseline.

    This never changes exemptions or source files. Missing docs and generic theorem
    names are actionable; mathematical correctness requires Lean and claim review.
    """
    from formalpedia_catalog import page_bounds
    page_bounds(limit, offset)
    index, _, snapshot = catalogue.snapshot()
    baseline = json.loads(lean_style.BASELINE.read_text(encoding='utf-8'))
    result = lean_style.report(index, baseline)
    result['new_violations'] = result['new_violations'][offset:offset + limit]
    result.update(snapshot=snapshot, offset=offset,
                  next_offset=offset + limit if offset + limit < result['new_count'] else None)
    return result


@mcp.resource('formalpedia://guide')
def discovery_guide() -> str:
    """The repository's Lean naming and theorem-discovery policy."""
    return (fp.ROOT / 'docs/architecture/lean_discovery.md').read_text(encoding='utf-8')


@mcp.tool(annotations=READ_ONLY)
def formalpedia_research_search(query: str, programme: Literal['juggler', 'collatz'] | None = None,
                               decision: Literal['PROMOTE', 'PARK', 'CLOSE'] | None = None,
                               limit: int = 10, offset: int = 0, snapshot: str | None = None) -> dict[str, Any]:
    """Search canonical research dossiers and associated claims across both programmes.

    Results use programme-qualified dossier IDs. Existing Juggler aliases are reused.
    Pass the returned snapshot on later pages to reject source changes. A search miss
    does not establish novelty. No catalogue files or research outputs are written.
    """
    return research.search(query, programme, decision, limit, offset, snapshot)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_research_context(identifier: str,
                                section: Literal['overview', 'claims', 'sources', 'data', 'obstructions',
                                                 'questions', 'commands', 'papers'] = 'overview',
                                limit: int = 10, offset: int = 0,
                                snapshot: str | None = None) -> dict[str, Any]:
    """Read a bounded research context section with source paths and excerpt truncation.

    Start with overview, then inspect obstructions, questions and claims. Commands are
    suggestions, never executed. Lean references are recorded associations, not fresh
    compilation or coverage evidence. Use formalpedia_claim/show for exact statements.
    Ambiguous aliases return candidates. Unknown decisions remain null.
    """
    return research.context(identifier, section, limit, offset, snapshot)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_research_check(limit: int = 20, offset: int = 0,
                              snapshot: str | None = None) -> dict[str, Any]:
    """Inspect structural errors, missing metadata and manifest coverage without mutations.

    Validates references and manifest schemas/sizes. Does not hash large datasets or run
    tests. Use the explicit CLI `python tools/lab.py check --hashes` for hash verification.
    Legacy results remain unverified rather than receiving invented provenance.
    """
    return research.check(limit=limit, offset=offset, snapshot=snapshot)


@mcp.resource('formalpedia://research-guide')
def research_guide() -> str:
    """Research catalogue, output manifest and validation workflow."""
    return (fp.ROOT / 'docs/architecture/research_catalogue.md').read_text(encoding='utf-8')


@mcp.tool(annotations=READ_ONLY)
def formalpedia_lab_doctor() -> dict[str, Any]:
    """Discover this checkout's local Python, Lean, publication and OEIS prerequisites.

    Read-only discovery only: does not run executables, install packages, or read secrets.
    Directory presence is not compilation. Use CLI doctor --probe for version probes.
    """
    from lab_environment import doctor
    return doctor(fp.ROOT)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_change_impact(since: str = 'HEAD', paths: list[str] | None = None,
                             limit: int = 20, offset: int = 0,
                             snapshot: str | None = None) -> dict[str, Any]:
    """Trace Git changes or explicit checkout paths through imports and recorded evidence.

    Includes staged, unstaged, deleted and untracked files. Reports candidate tests,
    claims, papers and registered datasets. Not a proof dependency graph or hash audit.
    Dynamic dependencies may be absent. Pass snapshot on subsequent pages.
    """
    from lab_impact import impact
    return impact(fp.ROOT, since=since, paths=paths, limit=limit, offset=offset, snapshot=snapshot)


@mcp.tool(annotations=READ_ONLY)
def formalpedia_verification_plan(since: str = 'HEAD', paths: list[str] | None = None,
                                  limit: int = 20, offset: int = 0,
                                  snapshot: str | None = None) -> dict[str, Any]:
    """Plan trusted local verification without running tests, Lean or publication tools.

    Every check starts not_checked. Executable changes use the full fast suite because
    imports alone cannot cover dynamic/file dependencies. Long argv previews are labelled
    truncated: obtain the complete plan with `python tools/lab.py verify --changed --plan`.
    Execute through the CLI, never commands copied from a dossier or MCP result.
    """
    from lab_verify import plan_page
    return plan_page(fp.ROOT, since=since, paths=paths, limit=limit, offset=offset, snapshot=snapshot)


@mcp.resource('formalpedia://workflow-guide')
def workflow_guide() -> str:
    """Change impact, environment diagnostics, verification scope and result semantics."""
    return (fp.ROOT / 'docs/architecture/agent_workflow.md').read_text(encoding='utf-8')


@mcp.resource('formalpedia://status')
def catalogue_status() -> str:
    """Live catalogue status as JSON."""
    return json.dumps(catalogue.status(), ensure_ascii=False)


@mcp.prompt()
def find_existing_result(goal: str) -> str:
    """Guide theorem reuse and exact statement checking before writing a new proof."""
    return (f'Find a reusable local Lean result for this goal:\n{goal}\n\n'
            'Use formalpedia_search with mathematical objects and conclusion words. '
            'Inspect candidates with formalpedia_show, compare all hypotheses and the '
            'conclusion, and use formalpedia_impact before changing an interface. '
            'Use lean-lsp to check applicability in the actual proof context. '
            'A search miss is not evidence that the theorem is absent.')


if __name__ == '__main__':
    mcp.run(transport='stdio')
