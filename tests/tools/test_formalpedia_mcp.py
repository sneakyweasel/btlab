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
            'formalpedia_impact', 'formalpedia_status', 'formalpedia_lint'}
        for tool in tools:
            assert tool.annotations.readOnlyHint
            assert tool.annotations.destructiveHint is False
            assert tool.annotations.openWorldHint is False
            assert tool.outputSchema
        resources = await server.mcp.list_resources()
        assert {str(r.uri) for r in resources} == {'formalpedia://guide', 'formalpedia://status'}
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
    asyncio.run(asyncio.wait_for(check(), timeout=120))
