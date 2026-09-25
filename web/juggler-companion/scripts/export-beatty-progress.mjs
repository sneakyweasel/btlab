// Package the public Beatty claim ledger for the companion; never retag or edit claims.
//
// Each claim is dated by the first commit whose diff added its ID to a tracked
// file. Claims not yet committed carry no date. Run from a full Git clone.
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../../", import.meta.url));
const ledgerPath = "docs/claims/juggler/beatty_first_passage.json";
const destination = new URL("../src/data/beatty_progress.json", import.meta.url);
const TAGS = [
  "EXACT — LEAN VERIFIED",
  "EXACT — HUMAN PROOF",
  "COMPUTATIONALLY VERIFIED",
  "CONJECTURE",
  "OBSERVATION",
  "REFUTED",
  "REPARAMETERIZATION",
];

const text = readFileSync(new URL(ledgerPath, `file:///${root.replace(/\\/g, "/")}`), "utf8").replace(/\r\n?/g, "\n");
const claims = JSON.parse(text);
assert(Array.isArray(claims) && claims.length > 0, "Empty Beatty ledger");
assert.equal(new Set(claims.map(c => c.id)).size, claims.length, "Duplicate claim IDs");
for (const claim of claims) assert(TAGS.includes(claim.tag), `Unknown evidence label on ${claim.id}: ${claim.tag}`);

const log = execFileSync("git", ["log", "--reverse", "--format=COMMIT %aI", "-p", "-G", "J-beatty-[a-z0-9-]+",
  "--", "docs", "*.json", "*.md"], { cwd: root, encoding: "utf8", maxBuffer: 1 << 30 });
const first = new Map();
let date = null;
for (const line of log.split("\n")) {
  if (line.startsWith("COMMIT ")) { date = line.slice(7).trim(); continue; }
  if (!line.startsWith("+") || line.startsWith("+++")) continue;
  for (const match of line.matchAll(/"id": "(J-beatty-[a-z0-9-]+)"/g)) if (!first.has(match[1])) first.set(match[1], date);
}

const data = {
  source: ledgerPath,
  sourceSha256: createHash("sha256").update(text).digest("hex"),
  dating: "First commit whose diff added the claim ID to a tracked file.",
  claims: claims.map(c => ({
    id: c.id,
    tag: c.tag,
    statement: c.statement,
    lean: c.lean || null,
    source: c.source,
    firstRecorded: first.get(c.id) ?? null,
  })),
};
const output = JSON.stringify(data) + "\n";
if (process.argv.includes("--check")) {
  assert.equal(readFileSync(destination, "utf8").replace(/\r\n/g, "\n"), output, "Run npm run sync:beatty-progress");
} else {
  writeFileSync(destination, output);
}
const dated = data.claims.filter(c => c.firstRecorded).length;
console.log(`Beatty progress: ${data.claims.length} claims, ${dated} dated; ${fileURLToPath(destination)}`);
