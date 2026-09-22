"""Exercise the OEIS server through the actual MCP stdio protocol."""
import asyncio
import os
from pathlib import Path
import sys

import pytest

pytest.importorskip('mcp', reason='Install tools/requirements-formalpedia.txt for MCP transport tests')
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from oeis_index import create_database
import oeis_mcp as server


def test_tools_have_structured_schemas_and_read_only_annotations():
    async def check():
        tools = await server.mcp.list_tools()
        assert {t.name for t in tools} == {'oeis_get', 'oeis_search', 'oeis_terms', 'oeis_match_terms',
            'oeis_neighbors', 'oeis_lab_links', 'oeis_bfile', 'oeis_status'}
        for tool in tools:
            assert tool.outputSchema
            assert tool.annotations.readOnlyHint
            assert tool.annotations.destructiveHint is False
            assert tool.annotations.openWorldHint is False
        assert {str(r.uri) for r in await server.mcp.list_resources()} == {'oeis://guide', 'oeis://status'}
        assert [p.name for p in await server.mcp.list_prompts()] == ['investigate_sequence']
    asyncio.run(check())


def test_stdio_reads_searches_matches_and_reports_errors_without_writing(tmp_path):
    database = tmp_path / 'fixture.sqlite3'
    create_database(database, [('A000001', '%I A000001 #1 Jan 01 2026\n'
        '%N A000001 Signed example\n%S A000001 -2,0,9007199254740993\n'
        '%O A000001 -1,1\n%C A000001 Exact phoenix example.\n')],
        {'revision': 'a' * 40, 'exported_at': '2026-01-01'})
    before = database.read_bytes()

    async def check():
        params = StdioServerParameters(command=sys.executable, args=[str(TOOLS / 'oeis_mcp.py')],
            cwd=str(tmp_path), env=dict(os.environ, OEIS_DATABASE=str(database),
                                      OEIS_MIRROR=str(tmp_path / 'mirror'), PYTHONUTF8='1'))
        async with stdio_client(params) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                status = await session.call_tool('oeis_status', {})
                assert status.structuredContent['records'] == 1
                search = await session.call_tool('oeis_search', {'query': 'phoenix', 'fields': ['comments']})
                assert search.structuredContent['results'][0]['aid'] == 'A000001'
                entry = await session.call_tool('oeis_get', {'identifier': 'A000001', 'fields': ['comments']})
                assert entry.structuredContent['fields'][0]['text'] == 'Exact phoenix example.'
                matched = await session.call_tool('oeis_match_terms', {'terms': ['-2', '0', '9007199254740993']})
                assert matched.structuredContent['results'][0]['oeis_indices'] == [-1, 0, 1]
                terms = await session.call_tool('oeis_terms', {'identifier': 'A000001'})
                assert terms.structuredContent['terms'][-1]['value'] == '9007199254740993'
                pointer = await session.call_tool('oeis_bfile', {'identifier': 'A000001'})
                assert pointer.structuredContent['status'] == 'not_local'
                bad = await session.call_tool('oeis_match_terms', {'terms': ['1.5', '2', '3']})
                assert bad.isError
                bad_page = await session.call_tool('oeis_search', {'query': 'phoenix', 'limit': 999})
                assert bad_page.isError
                guide = await session.read_resource('oeis://guide')
                assert 'subsequence' in guide.contents[0].text
                prompt = await session.get_prompt('investigate_sequence', {'terms': '1,2,3'})
                assert 'novelty' in prompt.messages[0].content.text
    asyncio.run(asyncio.wait_for(check(), timeout=60))
    assert database.read_bytes() == before
