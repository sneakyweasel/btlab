// Formalization Blueprint: types and pure logic for the snapshot written by
// `python tools/formalpedia.py blueprint --json web/juggler-companion/public/data/blueprint.json`.
// The snapshot is a view of the laboratory claim ledger at export time, never a source.

export const STATUSES = [
  "formalized", "ready", "ready_conditional", "blocked", "stale", "needs_annotation",
  "unannotated", "open", "finite", "not_a_target",
] as const;
export type Status = (typeof STATUSES)[number];

export const STATUS_LABEL: Record<Status, string> = {
  formalized: "Formalized",
  ready: "Ready",
  ready_conditional: "Ready, conditional",
  blocked: "Blocked",
  stale: "Stale pin",
  needs_annotation: "Route incomplete",
  unannotated: "Unannotated",
  open: "Open hypothesis",
  finite: "Finite computation",
  not_a_target: "Not a target",
};

export type Coverage = { verdict: string; band: string; reading: string | null };
export type Blocker = { claim: string; kind: string; tag: string; status: Status };
export type Input = { claim: string; kind: string; decl: string[]; lean: string | null; coverage: Coverage };

export type Claim = {
  id: string;
  tag: string;
  status: Status;
  claim_kind: string;
  statement: string;
  source: string;
  lean: string | null;
  decl: string[];
  downstream: number;
  warnings: string[];
  next_action: string;
  agent_prompt: string | null;
  route?: string;
  blockers?: Blocker[];
  conditional_on?: string[];
  inputs?: Input[];
  proof_source?: { path: string; start: string; line: number | null; freshness: string };
  coverage?: Coverage;
};

export type GraphEdge = { from: string; to: string; kind: string; route: string };
export type Graph = {
  nodes: Record<string, { x: number; y: number }>;
  edges: GraphEdge[];
  width: number;
  height: number;
  node_w: number;
  node_h: number;
};

export const LIST_KEYS = [
  "ready", "almost_ready", "unlocks", "needs_annotation", "unannotated_boundary", "blocked", "stale",
] as const;
export type ListKey = (typeof LIST_KEYS)[number];

export type Blueprint = {
  schema: number;
  generated: string;
  snapshot: string;
  scope: string | null;
  counts: Record<Status, number>;
  limitations: string;
  lists: Record<ListKey, string[]>;
  unlocks: Record<string, string[]>;
  claims: Record<string, Claim>;
  graph: Graph;
};

export const LIST_INFO: Record<ListKey, { title: string; why: string }> = {
  ready: { title: "Ready to formalize", why: "Complete route; every proof and statement input is Lean verified." },
  almost_ready: { title: "One blocker away", why: "Complete route with exactly one input not yet in Lean." },
  unlocks: { title: "Highest-value blockers", why: "Formalizing one of these makes the listed claims ready." },
  needs_annotation: { title: "Routes to complete", why: "Partial routes: enumerate the immediate dependencies." },
  unannotated_boundary: { title: "Inputs without routes", why: "Used by an annotated proof but never annotated themselves." },
  blocked: { title: "Blocked", why: "Several inputs missing from Lean." },
  stale: { title: "Stale source pins", why: "The cited passage changed; review before repinning." },
};

/** A claim is shown when no status is chosen, or when its status is one of the chosen. */
export function shown(active: ReadonlySet<Status>, status: Status): boolean {
  return active.size === 0 || active.has(status);
}

/** Case-insensitive match on the ID, label, status and statement. */
export function matches(claim: Claim, query: string): boolean {
  const q = query.trim().toLowerCase();
  if (!q) return true;
  return [claim.id, claim.tag, claim.status, STATUS_LABEL[claim.status], claim.statement]
    .some(text => text.toLowerCase().includes(q));
}

/** Plain click selects one status, or clears it when it is the only one; a modifier toggles. */
export function toggleStatus(active: ReadonlySet<Status>, status: Status, combine: boolean): Set<Status> {
  const next = new Set(active);
  if (combine) {
    if (next.has(status)) next.delete(status); else next.add(status);
    return next;
  }
  if (next.size === 1 && next.has(status)) return new Set();
  return new Set([status]);
}

export function parseStatuses(value: string | null): Set<Status> {
  const known = new Set<string>(STATUSES);
  return new Set((value ?? "").split(",").filter((s): s is Status => known.has(s)));
}

export function formatStatuses(active: ReadonlySet<Status>): string {
  return STATUSES.filter(s => active.has(s)).join(",");
}

/** Claims ordered for the table: widest downstream reach first, then by ID. */
export function tableOrder(claims: Record<string, Claim>): Claim[] {
  return Object.values(claims).sort((a, b) => b.downstream - a.downstream || a.id.localeCompare(b.id));
}

/** Direct inputs and users of one claim in the written graph. */
export function neighbours(graph: Graph, id: string): { uses: string[]; usedBy: string[] } {
  const uses = new Set<string>(), usedBy = new Set<string>();
  for (const e of graph.edges) {
    if (e.from === id) uses.add(e.to);
    if (e.to === id) usedBy.add(e.from);
  }
  return { uses: [...uses], usedBy: [...usedBy] };
}

export function isBlueprint(value: unknown): value is Blueprint {
  const v = value as Blueprint | null;
  return !!v && v.schema === 1 && typeof v.claims === "object" && typeof v.graph === "object"
    && LIST_KEYS.every(k => Array.isArray(v.lists?.[k]));
}
