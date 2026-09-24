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
                "arb_production_root", "arb_continued_fraction", "arb_best_approximation",
                "arb_paper_c_models", "arb_paper_c_rate"}
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
                fraction = await session.call_tool("arb_continued_fraction",
                    {"expression": "log(3)/log(2)", "terms": 10})
                assert fraction.structuredContent["quotients"] == [
                    "1", "1", "1", "2", "2", "3", "1", "5", "2", "23"]
                assert fraction.structuredContent["last_convergent"] == {"p": "24727", "q": "15601"}
                assert "src/research_engine/diophantine.py" in fraction.structuredContent["source_sha256"]
                approximation = await session.call_tool("arb_best_approximation",
                    {"expression": "log(3)/log(2)", "max_denominator": "20000"})
                assert approximation.structuredContent["attained_at"] == ["15601"]
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


#: OEIS A028507, continued fraction for log_2(3), terms n = 0..44.
LOG2_3 = ["1", "1", "1", "2", "2", "3", "1", "5", "2", "23", "2", "2", "1", "1", "55", "1",
          "4", "3", "1", "1", "15", "1", "9", "2", "5", "7", "1", "1", "4", "8", "1", "11",
          "1", "20", "2", "1", "10", "1", "4", "1", "1", "1", "1", "1", "37"]


def test_continued_fraction_matches_oeis_and_stops_on_a_true_prefix():
    full = run({"operation": "continued_fraction",
                "arguments": {"expression": "log(3)/log(2)", "terms": 45}})
    assert full["status"] == "certified" and full["quotients"] == LOG2_3
    short = run({"operation": "continued_fraction", "arguments": {
        "expression": "log(3)/log(2)", "terms": 45, "bits": 32, "max_bits": 32}})
    assert short["status"] == "unresolved" and short["reason"]
    assert 0 < short["certified_terms"] < 45
    assert short["quotients"] == LOG2_3[:short["certified_terms"]]


def test_continued_fraction_of_rationals_and_boxes():
    exact = run({"operation": "continued_fraction", "arguments": {"expression": "355/113"}})
    assert exact["quotients"] == ["3", "7", "16"] and exact["terminated"]
    assert exact["last_convergent"] == {"p": "355", "q": "113"}
    truncated = run({"operation": "continued_fraction",
                     "arguments": {"expression": "355/113", "terms": 2}})
    assert truncated["quotients"] == ["3", "7"] and not truncated["terminated"]
    box = run({"operation": "continued_fraction",
               "arguments": {"expression": "x", "variables": {"x": ["1.58", "1.59"]}}})
    assert box["status"] == "unresolved" and box["quotients"] == ["1", "1", "1", "2"]


@pytest.mark.parametrize("arguments", [
    {"expression": "log(3)/log(2)", "terms": 0}, {"expression": "log(3)/log(2)", "terms": 1001},
    {"expression": "log(3)/log(2)", "terms": True}, {"expression": "log(3)", "bits": 16},
])
def test_invalid_continued_fraction_requests(arguments):
    with pytest.raises(ValueError):
        run({"operation": "continued_fraction", "arguments": arguments})


def test_best_approximation_reports_the_minimum_with_exact_endpoints():
    result = run({"operation": "best_approximation", "arguments": {
        "expression": "log(3)/log(2)", "max_denominator": "1000000", "tau": "1"}})
    assert result["status"] == "certified"
    lo, hi = F(result["minimum"]["lower"]), F(result["minimum"]["upper"])
    assert 0 < lo <= hi
    assert result["convergents"][-1]["q"] == "190537"
    assert all(isinstance(row["distance"], str) for row in result["convergents"])
    assert "src/research_engine/diophantine.py" in result["source_sha256"]


def test_largest_best_approximation_fits_the_response_budget():
    import json
    import time

    start = time.perf_counter()
    result = run({"operation": "best_approximation", "arguments": {
        "expression": "(1+sqrt(5))/2", "max_denominator": str(10**60), "tau": "16"}})
    # All partial quotients of the golden ratio are 1: the most convergents below any bound.
    assert result["status"] == "certified" and len(result["convergents"]) > 280
    assert time.perf_counter() - start < 10
    assert len(json.dumps(result)) < 131072


@pytest.mark.parametrize("change", [{"max_denominator": "0"}, {"max_denominator": "1/2"},
                                    {"max_denominator": str(10**60 + 1)}, {"tau": "-1"},
                                    {"tau": "17"}, {"max_denominator": 10}])
def test_invalid_best_approximation_requests(change):
    with pytest.raises((TypeError, ValueError)):
        run({"operation": "best_approximation", "arguments": {
            "expression": "log(3)/log(2)", "max_denominator": "100", **change}})


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
