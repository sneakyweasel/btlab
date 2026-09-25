// Cross-checks the committed blueprint snapshot against the laboratory claim ledger.
// A snapshot may lag the ledger: new rows and new Lean proofs only make it older, and the
// page shows its export date. It must never show more than the ledger supports, so the
// checks below fail on a claim that vanished or on "formalized" without LEAN VERIFIED.
// Refresh: python tools/formalpedia.py blueprint --json web/juggler-companion/public/data/blueprint.json
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Blueprint } from "./blueprint";

const here = fileURLToPath(new URL(".", import.meta.url));
const claimsRoot = join(here, "../../../../docs/claims");
const snapshot = JSON.parse(readFileSync(join(here, "../../public/data/blueprint.json"), "utf8")) as Blueprint;

function ledger(dir: string): Map<string, { tag: string }> {
  const rows = new Map<string, { tag: string }>();
  for (const name of readdirSync(dir)) {
    const path = join(dir, name);
    if (statSync(path).isDirectory()) {
      for (const [id, row] of ledger(path)) rows.set(id, row);
    } else if (name.endsWith(".json")) {
      for (const row of JSON.parse(readFileSync(path, "utf8")) as { id: string; tag: string }[]) rows.set(row.id, row);
    }
  }
  return rows;
}

const rows = ledger(claimsRoot);
const refresh = "refresh with python tools/formalpedia.py blueprint --json web/juggler-companion/public/data/blueprint.json";

describe("blueprint snapshot against the claim ledger", () => {
  it("names only claims that still exist", () => {
    const missing = Object.keys(snapshot.claims).filter(id => !rows.has(id));
    expect(missing, refresh).toEqual([]);
  });

  it("calls a claim formalized only while the ledger says LEAN VERIFIED", () => {
    const overstated = Object.values(snapshot.claims)
      .filter(c => c.status === "formalized" && rows.get(c.id)?.tag !== "EXACT — LEAN VERIFIED")
      .map(c => c.id);
    expect(overstated, refresh).toEqual([]);
  });

  it("copies every evidence label it shows from the ledger of its export", () => {
    // A retag after export is allowed only in the direction of more evidence: a demotion
    // (for example LEAN VERIFIED to HUMAN PROOF, or anything to REFUTED) must be re-exported.
    const demoted = Object.values(snapshot.claims)
      .filter(c => c.tag === "EXACT — LEAN VERIFIED" && rows.get(c.id)?.tag !== c.tag)
      .map(c => c.id);
    expect(demoted, refresh).toEqual([]);
  });
});
