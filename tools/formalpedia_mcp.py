"""Local read-only MCP server. Install tools/requirements-formalpedia.txt with pip."""
from __future__ import annotations

import json
from typing import Any, Literal

from mcp.server.fastmcp import FastMCP
from mcp.types import ToolAnnotations

import formalpedia as fp
from formalpedia_catalog import Catalogue
import lean_style

catalogue = Catalogue()
mcp = FastMCP('formalpedia', instructions=(
    'Search the local Lean library before proving a result. Resolve a fully qualified name, '
    'read its complete statement and hypotheses, and inspect exact claim links. '
    'Ambiguous names return candidates, never an arbitrary theorem. Source trust markers '
    'are not compilation or axiom-audit evidence. Use lean-lsp for goals, elaboration and '
    'proof checking. All tools here are local and read-only.'))
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
    Default scope is Juggler, Collatz and their imported shared mathematics. Use archive
    for historical projects or all for an exhaustive library search. Exact show remains global.
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
