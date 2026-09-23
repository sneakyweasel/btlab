"""Real stdio transport, paper regressions, isolation and worker cleanup."""
import asyncio
from fractions import Fraction as F
import os
from pathlib import Path
import sys

import pytest

pytest.importorskip("mcp", reason="Install tools/requirements-formalpedia.txt for MCP tests")
import anyio
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import arb_mcp as server
from arb_worker import run


def test_schemas_and_read_only_annotations():
    async def check():
        tools = await server.mcp.list_tools()
        assert {tool.name for tool in tools} == {"arb_capabilities", "arb_evaluate", "arb_compare",
                "arb_production_root", "arb_paper_c_models", "arb_paper_c_rate"}
        for tool in tools:
            assert tool.outputSchema
            assert tool.annotations.readOnlyHint and not tool.annotations.destructiveHint
            assert not tool.annotations.openWorldHint
        assert {str(r.uri) for r in await server.mcp.list_resources()} == {
            "arb://guide", "arb://capabilities"}
    asyncio.run(check())


def test_stdio_certifies_paper_examples_and_survives_bad_requests(tmp_path):
    async def check():
        params = StdioServerParameters(command=sys.executable,
            args=["-B", str(ROOT / "tools/arb_mcp.py")], cwd=str(tmp_path),
            env=dict(os.environ, PYTHONUTF8="1", PYTHONDONTWRITEBYTECODE="1"))
        async with stdio_client(params) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                caps = (await session.call_tool("arb_capabilities", {})).structuredContent
                assert caps["root"] == str(ROOT) and caps["limits"]["workers"] == 2
                models = (await session.call_tool("arb_paper_c_models", {})).structuredContent
                assert len(models["models"]) == 12
                root = await session.call_tool("arb_production_root",
                    {"terms": models["models"]["OOEE_fixed"]})
                result = root.structuredContent
                assert not root.isError and result["status"] == "certified"
                lo, hi = F(result["root"]["lower"]), F(result["root"]["upper"])
                assert F("0.6265517564005") < lo <= hi < F("0.6265517564007")
                assert hi - lo <= F(1, 10**24)
                assert F(result["root"]["lower_residual"]["lower"]) > 0
                assert F(result["root"]["upper_residual"]["upper"]) < 0
                slack = await session.call_tool("arb_compare", {
                    "left": "(1/2)**(5/8)+(33/100)*(3/4)**(5/8)+(11/100)*(9/16)**(5/8)",
                    "right": "1"})
                assert slack.structuredContent["holds"] is True
                for C, expected in ((15, False), (16, True)):
                    rate = await session.call_tool("arb_paper_c_rate", {"C": C, "q": "1/2"})
                    assert rate.structuredContent["holds"] is expected
                unknown = await session.call_tool("arb_compare", {"left": "x", "right": "0",
                    "variables": {"x": ["-1", "1"]}, "max_bits": 128})
                assert unknown.structuredContent["holds"] is None
                for arguments in ({"expression": "__import__('os')"},
                                  {"expression": "x", "variables": {"x": 0.1}},
                                  {"expression": "1", "bits": True},
                                  {"expression": "1", "bits": 100000}):
                    assert (await session.call_tool("arb_evaluate", arguments)).isError
                responses = await asyncio.gather(*[
                    session.call_tool("arb_evaluate", {"expression": "sqrt(2)", "bits": bits})
                    for bits in (64, 512, 128, 256)])
                widths = []
                for response, bits in zip(responses, (64, 512, 128, 256)):
                    item = response.structuredContent
                    assert not response.isError and item["precision_bits"] == bits
                    assert item["request"]["arguments"]["bits"] == bits
                    assert "src/research_engine/arb_expressions.py" in item["source_sha256"]
                    lo, hi = F(item["enclosure"]["lower"]), F(item["enclosure"]["upper"])
                    assert lo**2 < 2 < hi**2
                    widths.append(hi-lo)
                assert widths[1] < widths[3] < widths[2] < widths[0]
                guide = await session.read_resource("arb://guide")
                assert "unresolved" in guide.contents[0].text
    asyncio.run(asyncio.wait_for(check(), timeout=90))
    assert list(tmp_path.iterdir()) == []


@pytest.mark.parametrize("arguments", [
    {"terms": [["0", "1/2"]]}, {"terms": [["1", "2"]]},
    {"terms": [[1, "1/2"]]}, {"terms": [["2", "1/2"]] * 33},
    {"terms": [["2", "1/2"]], "lower": "-1"},
    {"terms": [["2", "1/2"]], "digits": 101},
    {"terms": [["4", "1/2"]]},
])
def test_invalid_production_requests(arguments):
    with pytest.raises(ValueError):
        run({"operation": "production_root", "arguments": arguments})


def test_exact_root_and_unresolved_root_are_distinct():
    exact_root = run({"operation": "production_root", "arguments": {"terms": [["2", "1/2"]]}})
    assert exact_root["root"]["lower"] == exact_root["root"]["upper"] == "1"
    unknown = run({"operation": "production_root", "arguments": {
        "terms": [["2", "1/3"]], "digits": 100, "bits": 32, "max_bits": 32}})
    assert unknown["status"] == "unresolved" and "root" not in unknown


@pytest.mark.parametrize("change", [{"C": True}, {"C": 10001}, {"q": "0"},
                                    {"exponent": "1"}, {"kind": "guess"}])
def test_paper_rate_validates_domain(change):
    with pytest.raises(ValueError):
        run({"operation": "paper_c_rate", "arguments": {"C": 16, "q": "1/2", **change}})


def test_timeout_kills_worker_and_releases_capacity(monkeypatch):
    # Real sleeping child, using the actual launch/kill path; no test hook in production.
    original = asyncio.create_subprocess_exec
    children = []

    async def sleeper(*args, **kwargs):
        process = await original(sys.executable, "-I", "-c", "import time; time.sleep(30)", **kwargs)
        children.append(process)
        return process

    async def check():
        monkeypatch.setattr(server, "_slots", asyncio.Semaphore(2))
        monkeypatch.setattr(server, "TIMEOUT_SECONDS", 0.2)
        monkeypatch.setattr(asyncio, "create_subprocess_exec", sleeper)
        with pytest.raises(ValueError, match="exceeded"):
            await server.calculate("evaluate", {"source": "1"})
        assert children[0].returncode is not None
        monkeypatch.setattr(asyncio, "create_subprocess_exec", original)
        monkeypatch.setattr(server, "TIMEOUT_SECONDS", 20)
        assert (await server.calculate("evaluate", {"source": "1"}))["status"] == "enclosed"
    asyncio.run(check())


def test_cancelled_request_reaps_child_and_server_can_continue(monkeypatch):
    original = asyncio.create_subprocess_exec
    children = []

    async def check():
        started = asyncio.Event()

        async def sleeper(*args, **kwargs):
            process = await original(sys.executable, "-I", "-c", "import time; time.sleep(30)", **kwargs)
            children.append(process)
            started.set()
            return process

        monkeypatch.setattr(server, "_slots", asyncio.Semaphore(2))
        monkeypatch.setattr(asyncio, "create_subprocess_exec", sleeper)
        task = asyncio.create_task(server.calculate("evaluate", {"source": "1"}))
        await asyncio.wait_for(started.wait(), 10)
        task.cancel()
        with pytest.raises(asyncio.CancelledError):
            await task
        assert children[0].returncode is not None
        monkeypatch.setattr(asyncio, "create_subprocess_exec", original)
        assert (await server.calculate("evaluate", {"source": "1"}))["status"] == "enclosed"
    asyncio.run(check())


def test_mcp_level_cancellation_during_launch_recovers_slots(monkeypatch):
    original = asyncio.create_subprocess_exec
    children = []

    async def delayed_launch(*args, **kwargs):
        process = await original(sys.executable, "-I", "-c", "import time; time.sleep(30)", **kwargs)
        children.append(process)
        await asyncio.sleep(0.2)  # cancellation arrives before the caller obtains its handle
        return process

    async def check():
        monkeypatch.setattr(server, "_slots", asyncio.Semaphore(2))
        monkeypatch.setattr(asyncio, "create_subprocess_exec", delayed_launch)
        for _ in range(3):
            with anyio.move_on_after(0.1) as scope:
                await server.calculate("evaluate", {"source": "1"})
            assert scope.cancel_called
        assert len(children) == 3 and all(child.returncode is not None for child in children)
        monkeypatch.setattr(asyncio, "create_subprocess_exec", original)
        assert (await server.calculate("evaluate", {"source": "1"}))["status"] == "enclosed"
    asyncio.run(check())
