"""Exercise the MCP contract and real stdio transport, not only Python wrappers."""
import asyncio
from pathlib import Path
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
            'formalpedia_type_search', 'formalpedia_dependencies', 'formalpedia_semantic_diff'}
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


def test_real_stdio_client_searches_resolves_and_rejects_invalid_pagination():
    async def check():
        params = StdioServerParameters(command=sys.executable,
            args=[str(TOOLS / 'formalpedia_mcp.py')], cwd=str(ROOT))
        async with stdio_client(params) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                advertised = await session.list_tools()
                assert 'formalpedia_type_search' in {t.name for t in advertised.tools}
                capabilities = await session.call_tool('formalpedia_capabilities', {})
                assert not capabilities.isError
                assert capabilities.structuredContent['protocol_version'] == 3
                assert 'semantic' in capabilities.structuredContent['tool_groups']
                semantic = await session.call_tool('formalpedia_semantic_status', {})
                assert not semantic.isError
                assert semantic.structuredContent['status'] in {'missing', 'current', 'partial', 'stale', 'unreadable'}
                result = await session.call_tool('formalpedia_search',
                    {'query': 'cycleMin_finance', 'limit': 3})
                assert not result.isError
                data = result.structuredContent
                assert data['results'] and data['results'][0]['qualified_name']
                detail = await session.call_tool('formalpedia_show',
                    {'name': data['results'][0]['qualified_name']})
                assert detail.structuredContent['status'] == 'found'
                assert detail.structuredContent['declaration']['signature']
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
