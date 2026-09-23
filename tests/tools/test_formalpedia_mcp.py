"""Exercise the MCP contract and real stdio transport, not only Python wrappers."""
import asyncio
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import pytest

pytest.importorskip('mcp', reason='install the [mcp] extra to test the MCP transport')
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))
import formalpedia_mcp as server


def test_mcp_discovery_is_structured_and_read_only():
    async def check():
        tools = await server.mcp.list_tools()
        assert {t.name for t in tools} == {
            'formalpedia_search', 'formalpedia_show', 'formalpedia_claim',
            'formalpedia_impact', 'formalpedia_status', 'formalpedia_lint',
            'formalpedia_research_search', 'formalpedia_research_context', 'formalpedia_research_check',
            'formalpedia_lab_doctor', 'formalpedia_change_impact', 'formalpedia_verification_plan',
            'formalpedia_capabilities', 'formalpedia_semantic_status', 'formalpedia_semantic_show',
            'formalpedia_type_search', 'formalpedia_dependencies', 'formalpedia_semantic_diff',
            'formalpedia_claim_dependencies'}
        for tool in tools:
            assert tool.annotations.readOnlyHint
            assert tool.annotations.destructiveHint is False
            assert tool.annotations.openWorldHint is False
            assert tool.outputSchema
        resources = await server.mcp.list_resources()
        assert {str(r.uri) for r in resources} == {
            'formalpedia://guide', 'formalpedia://status', 'formalpedia://research-guide',
            'formalpedia://workflow-guide'}
        prompts = await server.mcp.list_prompts()
        assert [p.name for p in prompts] == ['find_existing_result']
    asyncio.run(check())


@pytest.fixture
def checkout(tmp_path):
    """An independent checkout with known source, research and compiled metadata."""
    def write(name, content):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding='utf-8')

    write('formal/Problems/Juggler/Example.lean',
          'namespace Example\n/-- Finance fixture. -/\ntheorem cycleMin_finance : True := trivial\n'
          'def step : Nat := 1\nend Example\n')
    write('formal/Problems/Collatz/Example.lean', 'namespace Other\ndef step : Nat := 2\nend Other\n')
    write('formal/Operators/Fixture.lean',
          'namespace Custom\n/-- Only the selected ledger cites this. -/\n'
          'theorem root_only : True := trivial\nend Custom\n')
    write('docs/claims/collatz/example.json', json.dumps([{
        'id': 'C-fixture', 'statement': 'Fixture identity', 'tag': 'EXACT — HUMAN PROOF',
        'lean': 'formal/Operators/Fixture.lean', 'decl': 'Custom.root_only',
        'source': 'docs/problems/collatz_fibre_sign_coupling.md', 'tests': []}]))
    write('docs/problems/collatz_fibre_sign_coupling.md',
          '# Fibre sign coupling\n## Decision\nPARK\n## Obstructions\nA fixture obstruction.\n')
    write('docs/negative_knowledge/fixture.md',
          '# A zircon barrier\n\nA finite counterexample does not refute termination.\n'
          '[Dossier](../problems/collatz_fibre_sign_coupling.md)\n')
    from research.knowledge import render_negative_index
    write('docs/negative_knowledge.md', render_negative_index(tmp_path))
    write('docs/architecture/lean_discovery.md', 'Use fully qualified names.\n')
    write('src/research/juggler_sequence/lean_registry.py', 'VALUE = 1\n')
    write('src/research/juggler_sequence/consumer.py',
          'from research.juggler_sequence.lean_registry import VALUE\n')
    write('tools/lab.py', '# fixture CLI\n')
    write('.gitignore', '.cache/\n')
    subprocess.run(['git', 'init', '-b', 'main'], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(['git', 'add', '.'], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(['git', '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                    '-c', 'commit.gpgsign=false', 'commit', '-m', 'Fixture'],
                   cwd=tmp_path, check=True, capture_output=True)
    from formalpedia_core.semantic_common import inputs, digest
    from formalpedia_core.semantic_query import SemanticCatalogue
    from formalpedia_core.semantic_store import publish
    module = 'Problems.Juggler.Example'
    ast = ['const', 'True', []]
    row = {'id': module + '::Example.cycleMin_finance', 'name': 'Example.cycleMin_finance',
           'module': module, 'kind': 'theorem', 'type': 'True', 'type_ast': ast,
           'type_sha256': digest(ast), 'binders': [], 'axioms': [], 'value_hash64': '1',
           'type_dependencies': ['True'], 'value_dependencies': ['True.intro']}
    publish(SemanticCatalogue(tmp_path), [module], [row],
            {'inputs': inputs(tmp_path), 'objects': {}, 'source_modules': None,
             'imports': {module: []}, 'object_modules': {}})
    return tmp_path


def test_real_stdio_client_searches_resolves_and_rejects_invalid_pagination(checkout):
    def inventory():
        return {p.relative_to(checkout).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in checkout.rglob('*') if p.is_file()}

    before = inventory()
    async def check():
        params = StdioServerParameters(command=sys.executable,
            args=[str(TOOLS / 'formalpedia_mcp.py'), '--root', str(checkout)], cwd=str(checkout))
        async with stdio_client(params) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                advertised = await session.list_tools()
                assert 'formalpedia_type_search' in {t.name for t in advertised.tools}
                capabilities = await session.call_tool('formalpedia_capabilities', {})
                assert not capabilities.isError
                assert capabilities.structuredContent['protocol_version'] == 4
                assert Path(capabilities.structuredContent['root']) == checkout
                assert 'semantic' in capabilities.structuredContent['tool_groups']
                claims = await session.call_tool('formalpedia_claim_dependencies',
                    {'ledger_id': 'C-fixture', 'include_compiled': True})
                assert not claims.isError
                assert not claims.structuredContent['dependency_coverage_complete']
                assert claims.structuredContent['summary']['incomplete_dependencies'] == ['C-fixture']
                origin = await session.call_tool('formalpedia_claim', {'ledger_id': 'C-fixture'})
                assert origin.structuredContent['claim_location'] == {
                    'path': 'docs/claims/collatz/example.json', 'pointer': '/0'}
                semantic = await session.call_tool('formalpedia_semantic_status', {})
                assert not semantic.isError
                assert semantic.structuredContent['status'] == 'current'
                assert semantic.structuredContent['storage_schema'] == 3
                result = await session.call_tool('formalpedia_search',
                    {'query': 'cycleMin_finance', 'limit': 3})
                assert not result.isError
                data = result.structuredContent
                assert data['results'] and data['results'][0]['qualified_name']
                detail = await session.call_tool('formalpedia_show',
                    {'name': data['results'][0]['qualified_name']})
                assert detail.structuredContent['status'] == 'found'
                assert detail.structuredContent['declaration']['signature']
                assert detail.structuredContent['compiled']['status'] == 'found'
                scoped = await session.call_tool('formalpedia_search', {'query': 'root_only'})
                assert not scoped.isError and scoped.structuredContent['total'] == 1
                assert scoped.structuredContent['results'][0]['ledger_exact'] == ['C-fixture']
                types = await session.call_tool('formalpedia_type_search', {'constants': ['True']})
                assert not types.isError and types.structuredContent['total'] == 1
                dependencies = await session.call_tool('formalpedia_dependencies',
                    {'name': 'Example.cycleMin_finance'})
                assert not dependencies.isError and dependencies.structuredContent['total'] == 2
                ambiguous = await session.call_tool('formalpedia_show', {'name': 'step'})
                assert ambiguous.structuredContent['status'] == 'ambiguous'
                bad = await session.call_tool('formalpedia_search', {'query': '', 'limit': 0})
                assert bad.isError
                guide = await session.read_resource('formalpedia://guide')
                assert 'fully qualified' in guide.contents[0].text
                branches = await session.call_tool('formalpedia_research_search',
                    {'query': 'fibre sign coupling', 'programme': 'collatz', 'limit': 2})
                assert not branches.isError
                branch = branches.structuredContent['items'][0]
                assert branch['id'] == 'collatz/fibre_sign_coupling'
                context = await session.call_tool('formalpedia_research_context',
                    {'identifier': branch['id'], 'section': 'obstructions', 'limit': 2,
                     'snapshot': branches.structuredContent['snapshot']})
                assert not context.isError and context.structuredContent['items']
                assert 'not' in context.structuredContent['limitations'].lower() or 'no tests' in context.structuredContent['limitations'].lower()
                obstacles = await session.call_tool('formalpedia_research_search',
                    {'query': 'zircon', 'kind': 'obstruction', 'programme': 'collatz'})
                assert not obstacles.isError
                assert obstacles.structuredContent['items'][0]['id'] == 'obstruction/fixture'
                obstacle = await session.call_tool('formalpedia_research_context',
                    {'identifier': 'obstruction/fixture', 'section': 'obstructions'})
                assert not obstacle.isError
                record = obstacle.structuredContent['items'][0]
                assert record['file'] == 'docs/negative_knowledge/fixture.md'
                assert 'does not refute termination' in record['text']
                stale = await session.call_tool('formalpedia_research_search',
                    {'query': 'coupling', 'snapshot': 'outdated'})
                assert stale.isError
                doctor = await session.call_tool('formalpedia_lab_doctor', {})
                assert not doctor.isError and doctor.structuredContent['checks']
                changes = await session.call_tool('formalpedia_change_impact',
                    {'paths': ['src/research/juggler_sequence/lean_registry.py'], 'limit': 2})
                assert not changes.isError and len(changes.structuredContent['items']) == 2
                plan = await session.call_tool('formalpedia_verification_plan',
                    {'paths': ['tools/lab.py'], 'limit': 2})
                assert not plan.isError
                assert all(c['status'] == 'not_checked' for c in plan.structuredContent['items'])
                invalid = await session.call_tool('formalpedia_change_impact', {'paths': ['../outside']})
                assert invalid.isError
    asyncio.run(asyncio.wait_for(check(), timeout=120))
    assert inventory() == before, 'Read-only MCP requests changed the selected checkout'


def test_read_only_server_does_not_import_compilers_or_external_review_clients():
    probe = ('import json, sys; import formalpedia_mcp; '
             'print(json.dumps(sorted(sys.modules)))')
    result = subprocess.run([sys.executable, '-c', probe], cwd=TOOLS,
                            capture_output=True, text=True, check=True, timeout=30)
    loaded = set(json.loads(result.stdout))
    assert not loaded.intersection({'formalpedia_core.advisory', 'formalpedia_core.cli',
                                    'formalpedia_core.semantic_build', 'typesafe_sdk'})
