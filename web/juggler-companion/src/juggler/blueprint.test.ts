import { describe, expect, it } from "vitest";
import snapshotData from "../../public/data/blueprint.json";
import {
  LIST_KEYS, STATUSES, formatStatuses, isBlueprint, matches, neighbours, parseStatuses, shown,
  tableOrder, toggleStatus, type Blueprint, type Claim, type Status,
} from "./blueprint";

const snapshot = snapshotData as unknown as Blueprint;

const claim = (id: string, status: Status, downstream = 0, statement = ""): Claim => ({
  id, status, downstream, statement, tag: "EXACT — HUMAN PROOF", claim_kind: "result", source: "x.md",
  lean: null, decl: [], warnings: [], next_action: "", agent_prompt: null,
});

describe("status filter", () => {
  it("shows everything when nothing is chosen, else only the chosen", () => {
    expect(shown(new Set(), "blocked")).toBe(true);
    expect(shown(new Set<Status>(["ready"]), "blocked")).toBe(false);
    expect(shown(new Set<Status>(["ready", "blocked"]), "blocked")).toBe(true);
  });

  it("selects one status on click, clears it on a second click, and combines with a modifier", () => {
    let active = toggleStatus(new Set(), "ready", false);
    expect([...active]).toEqual(["ready"]);
    active = toggleStatus(active, "blocked", false);
    expect([...active]).toEqual(["blocked"]);
    active = toggleStatus(active, "ready", true);
    expect(formatStatuses(active)).toBe("ready,blocked");
    active = toggleStatus(active, "blocked", true);
    expect([...active]).toEqual(["ready"]);
    expect(toggleStatus(active, "ready", false).size).toBe(0);
  });

  it("round-trips through the URL and ignores unknown statuses", () => {
    expect(formatStatuses(parseStatuses("blocked,nonsense,ready"))).toBe("ready,blocked");
    expect(parseStatuses(null).size).toBe(0);
  });
});

describe("search and ordering", () => {
  it("matches ID, label and statement case-insensitively", () => {
    const c = claim("J-demo", "needs_annotation", 0, "Poor fibres are thin");
    expect(matches(c, "")).toBe(true);
    expect(matches(c, "j-DEMO")).toBe(true);
    expect(matches(c, "route incomplete")).toBe(true);
    expect(matches(c, "THIN")).toBe(true);
    expect(matches(c, "cycle")).toBe(false);
  });

  it("orders by downstream reach, then ID", () => {
    const order = tableOrder({ b: claim("b", "ready", 2), a: claim("a", "ready", 2), c: claim("c", "ready", 5) });
    expect(order.map(c => c.id)).toEqual(["c", "a", "b"]);
  });
});

describe("committed snapshot", () => {
  it("has the expected shape", () => {
    expect(isBlueprint(snapshot)).toBe(true);
    expect(isBlueprint({ ...snapshot, schema: 2 })).toBe(false);
  });

  it("gives every claim a known status and counts them consistently", () => {
    const claims = Object.values(snapshot.claims);
    for (const c of claims) expect(STATUSES).toContain(c.status);
    for (const s of STATUSES) expect(claims.filter(c => c.status === s).length).toBe(snapshot.counts[s]);
  });

  it("lists, graph nodes and edges refer only to claims in the snapshot", () => {
    for (const k of LIST_KEYS) for (const id of snapshot.lists[k]) expect(snapshot.claims[id]).toBeDefined();
    for (const id of Object.keys(snapshot.graph.nodes)) expect(snapshot.claims[id]).toBeDefined();
    for (const e of snapshot.graph.edges) {
      expect(snapshot.graph.nodes[e.from]).toBeDefined();
      expect(snapshot.graph.nodes[e.to]).toBeDefined();
      // Each claim sits above its inputs in the exported layout.
      expect(snapshot.graph.nodes[e.from].y).toBeLessThan(snapshot.graph.nodes[e.to].y);
    }
  });

  it("offers an agent task exactly for claims with work to do", () => {
    const withTask = new Set<Status>(["ready", "ready_conditional", "blocked", "stale", "needs_annotation", "unannotated"]);
    for (const c of Object.values(snapshot.claims)) expect(c.agent_prompt !== null).toBe(withTask.has(c.status));
  });

  it("finds a claim's inputs and users in the graph", () => {
    const edge = snapshot.graph.edges[0];
    expect(neighbours(snapshot.graph, edge.from).uses).toContain(edge.to);
    expect(neighbours(snapshot.graph, edge.to).usedBy).toContain(edge.from);
  });
});
