// Package an existing certified figure snapshot; never recompute research evidence.
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const source = new URL("../../../docs/theory/figures/beatty_profile.json", import.meta.url);
const manifestPath = new URL("../../../docs/theory/figures/beatty_profile.research.json", import.meta.url);
const destination = new URL("../src/data/beatty_profile.json", import.meta.url);
const bytes = readFileSync(source);
const report = JSON.parse(bytes);
const manifest = JSON.parse(readFileSync(manifestPath, "utf8"));
const sha256 = createHash("sha256").update(bytes).digest("hex");
assert.equal(manifest.outputs.find(row => row.path.endsWith("beatty_profile.json"))?.sha256, sha256,
  "Figure snapshot does not match its provenance record");
assert.equal(report.orders, report.drawing.length);
assert.deepEqual(report.drawing.map(row => row.order).sort((a, b) => a - b),
  Array.from({ length: report.orders }, (_, i) => i + 1));

// Positive rational endpoints are moved inward by at least 10^-12 before
// conversion to display coordinates. Original rational certificates are retained.
function inward(text, lower) {
  const [n, d] = text.split("/").map(BigInt);
  assert(n > 0n && d > 0n);
  const scale = 1_000_000_000_000n;
  const integer = lower ? (n * scale + d - 1n) / d + 1n : n * scale / d - 1n;
  assert(integer < BigInt(Number.MAX_SAFE_INTEGER));
  return Number(integer) / Number(scale);
}
function midpoint(interval) {
  const rational = text => { const [n, d] = text.split("/").map(Number); return n / d; };
  return (rational(interval.lower) + rational(interval.upper)) / 2;
}
const data = {
  source: "docs/theory/figures/beatty_profile.json",
  sourceSha256: sha256,
  generatedUtc: manifest.created_utc,
  scope: report.scope,
  depth: report.depth,
  orders: report.orders,
  precisionBits: report.precision_bits,
  tailUpper: Number(report.tail_strict_decimal_upper),
  tailCertificate: report.tail,
  envelope: midpoint(report.envelope),
  envelopeCertificate: report.envelope,
  coordinateWidth: report.maximum_coordinate_enclosure_width,
  cores: report.certified_deleted_cores.map(c => {
    const lower = inward(c.lower, true), upper = inward(c.upper, false);
    assert(lower < upper);
    return { order: c.order, lower, upper, certificate: { lower: c.lower, upper: c.upper } };
  }),
  // Compact tuples: order, phase, jump weight, left profile value, exact-count ratio.
  rows: report.drawing.map(r => [r.order, r.phase, r.weight, r.left, r.ratio]),
};
const output = JSON.stringify(data) + "\n";
if (process.argv.includes("--check")) {
  assert.equal(readFileSync(destination, "utf8").replace(/\r\n/g, "\n"), output, "Run npm run sync:beatty");
} else {
  writeFileSync(destination, output);
}
console.log(`Beatty profile: ${data.orders} orders, ${data.cores.length} certified gap interiors; ${fileURLToPath(destination)}`);
