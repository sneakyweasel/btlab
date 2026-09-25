// Validate the canonical Paper A release before Vite builds.
//
// This script used to also copy the built PDF into public/papers/ so the site
// could serve its own copy. Every paper is deposited on Zenodo now and the site
// links the records, so the canonical PDF lives in preprints/,
// and there is nothing left to copy. What remains is the part worth keeping: the
// release manifest is checked against the files it names, so a stale or
// hand-edited release cannot reach a deploy unnoticed.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { dirname, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../../..');
const source = 'docs/theory/juggler_finite_dynamics_note.md';
const canonical = 'preprints/juggler_finite_dynamics_note.pdf';
const manifest = resolve(root, 'docs/theory/paper_a_release.json');
const hash = (data) => createHash('sha256').update(data).digest('hex');

// Vercel uploads a website-only tree: .vercelignore drops /docs, /formal, /src
// and /preprints, so neither the manifest nor the files it names are there
// to check. Provenance is enforced on local builds and in CI instead.
if (process.env.VERCEL) {
  console.log('Paper A: Vercel deploy; laboratory tree excluded, release check runs locally and in CI.');
} else try {
  const release = JSON.parse(readFileSync(manifest, 'utf8'));
  if (release.schema !== 2 || release.canonical_source !== source ||
      !release.inputs.some((r) => r.path === source) ||
      !release.outputs.some((r) => r.path === canonical)) {
    throw new Error('Incomplete release manifest');
  }
  for (const row of [...release.inputs, ...release.outputs]) {
    const file = resolve(root, row.path);
    const rel = relative(root, file);
    if (rel.startsWith('..') || isAbsolute(rel)) throw new Error('Invalid release path');
    let data = readFileSync(file);
    if (row.mode === 'text') data = Buffer.from(data.toString('utf8').replace(/\r\n?/g, '\n'));
    if (hash(data) !== row.sha256) throw new Error(`Stale release input/output: ${row.path}`);
  }
  console.log('Paper A: canonical release verified.');
} catch (error) {
  console.error(`Paper A: ${error.message}. Run python tools/build_paper.py A from the repository root.`);
  process.exitCode = 1;
}
