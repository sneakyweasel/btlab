// Validate the canonical release before Vite copies public/ into dist/.
import { readFileSync, existsSync, mkdirSync, copyFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { dirname, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../../..');
const source = 'docs/theory/juggler_finite_dynamics_note.md';
const canonical = 'docs/theory/juggler_finite_dynamics_note.pdf';
const manifest = resolve(root, 'docs/theory/paper_a_release.json');
const target = resolve(root, 'web/juggler-companion/public/papers/juggler_finite_dynamics_note.pdf');
const hash = (data) => createHash('sha256').update(data).digest('hex');

// Vercel uploads a website-only tree (.vercelignore drops /docs, /formal, /src).
// The committed public PDF is the deploy artifact; full provenance stays on local/CI.
if (process.env.VERCEL) {
  if (!existsSync(target)) {
    console.error('Paper A: website PDF missing from public/papers/. Run python tools/build_paper_a.py from the repository root.');
    process.exitCode = 1;
  } else {
    console.log('Paper A: Vercel deploy using shipped website PDF (laboratory tree excluded).');
  }
} else try {
  const release = JSON.parse(readFileSync(manifest, 'utf8'));
  if (release.schema !== 1 || release.canonical_source !== source ||
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
  if (!process.argv.includes('--check')) {
    mkdirSync(dirname(target), { recursive: true });
    copyFileSync(resolve(root, canonical), target);
  } else if (!existsSync(target) || hash(readFileSync(target)) !== hash(readFileSync(resolve(root, canonical)))) {
    throw new Error('Stale public Paper A PDF');
  }
  console.log('Paper A: canonical release verified; website PDF synchronized.');
} catch (error) {
  console.error(`Paper A: ${error.message}. Run python tools/build_paper_a.py from the repository root.`);
  process.exitCode = 1;
}
