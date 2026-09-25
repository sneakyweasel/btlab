# Juggler companion

A static reviewer site for Papers A–C:
[Lower Bounds for Cycle Lengths in the Juggler Map](https://doi.org/10.5281/zenodo.22676453),
[Five-Step Descent Certificates for the Juggler Map](https://doi.org/10.5281/zenodo.22864934)
and [Fate Contagion and Termination Criteria for the Juggler Map](https://doi.org/10.5281/zenodo.22678165).
It teaches the basic vocabulary with pictures and a small playground. It is
not the laboratory Streamlit app and not a halt-theorem demo.

The printed results are period lower bounds at a verified descent floor.
Hitting 1 on one walk is not a proof that every start does. A
finance-survivor length is not a candidate cycle.

## Run locally

```powershell
cd web/juggler-companion
npm install
npm test
npm run dev
```

The dev server uses base `/`. Open the URL Vite prints (usually
http://localhost:5173/).

## Beatty profile

The React playground at `/play/beatty-profile` links the left-continuous phase
profile, exact-count samples, and certified deleted-gap interiors. Select an
order, inspect a phase, zoom around the selection, change the sample window,
or toggle the chart layers. It loads as a separate route chunk.

The selected-index readout gives δ_r, w_r, an enclosure of F(δ_r), and the
outward-rounded residual enclosure R_r^+ − F(δ_r). It never substitutes the
finite truncated profile for the infinite value. The collapsed distribution
view compares the selected sample range's empirical CDF with the limiting-law
enclosure H_M(y − T) ≤ P(F(U) ≤ y) ≤ H_M(y). Plateau masses are phase-interval
lengths, not equal weights per jump. Coordinates are rounded for display, and
the band is not a finite-sample confidence interval or convergence-rate bound.

The bundled `src/data/beatty_profile.json` is a display snapshot of
`data/research/juggler/winkler_phase_collapse/beatty_profile.json`: 5,047 orders at depth 8,000, with
256-bit Arb enclosures and omitted tail below 0.020220. It retains the source
hash and the exact rational gap certificates. Gray strip regions remain
unresolved; the tail band bounds the infinite profile, not finite-sample error.

## Beatty dimension atlas

`/beatty-atlas` is an unlisted working view: no navigation links to it, and it sets
`noindex`. It places a slope on the map of Hausdorff dimension against the
Diophantine class, shows the two-scale closed form, and runs the dimension game
live (a port of `research.juggler_sequence.beatty_dimension_game`). Tests check
the port against the committed `dimension_game.json` and every cited claim
against the ledger's current evidence label. The game is an exponent model, not
a proof; the tube-volume curve is a display computation from the bundled weights.

React owns visualization. From the repository root, generate certified data
without matplotlib using `python tools/export_beatty_profile.py --output
data/research/juggler/winkler_phase_collapse/beatty_profile.json`. Prefer
[artifact staging](../../docs/architecture/artifact_staging.md) before replacing
committed data. Then, from this web directory, refresh the display snapshot:

```powershell
npm run sync:beatty
node scripts/export-beatty-profile.mjs --check
```

The exporter verifies the canonical output hash before copying drawing data.
It does not regenerate counts, change evidence labels, or read private
correspondence. Site-only builds use the bundled snapshot.

## Build

```powershell
npm run build
npm run preview
```

The default public base is `/` (Vercel and local preview). GitHub project
pages set `VITE_BASE=/balanced_ternary/` in the workflow.

## Vercel

Import the GitHub repository on [Vercel](https://vercel.com/new). The root
`vercel.json` points the project at this package, so you do not need to set
a Root Directory. Framework is Vite; Node 22. The repository `.vercelignore`
drops the laboratory trees, so `prebuild` cannot hash
`docs/theory/paper_a_release.json` there and skips the check; it runs on local
builds and in CI. The papers are linked from their Zenodo records rather than
served from this package.

SPA routes (`/tour`, `/play/trajectory`, …) are rewritten to `index.html`.
If you instead set the Vercel Root Directory to `web/juggler-companion`,
the package-local `vercel.json` does the same rewrite.

## What is in the TypeScript kernel

`src/juggler/` is a display fork of

- `src/research/juggler_sequence/power_itineraries.py`
- `src/research/juggler_sequence/floor_preimages.py`
- `src/research/juggler_sequence/fate_contagion.py`
- `src/research/juggler_sequence/cycle_itinerary.py`
- `src/research/juggler_sequence/run_suffix_law.py`
- `src/research/juggler_sequence/paper_a_audit.py` (gap-transfer / Rhin fork)
- `src/research/juggler_sequence/cycle_walk_charge.py` (walk-charge transport fork)
- `src/data/fan.json` via the companion export (Proposition 5.12 fan law)

The preimage playground shows Paper C’s two productions — the even block
and the OE fiber with its parity sweep — the even-block average of
Proposition 4.4, the three §5.1 sources, and the Theorem 5.3 V-ladder
with the ρ_w test, not a halt-theorem demo.

`n_max` is looked up from the shipped Theorem 4.6 snapshot. It is never
recomputed with floating logarithms.

The lollipop figure is a second kind of fork. `src/juggler/lollipop.ts` and
`src/content/idealDecisions.ts` mirror a display contract that is defined and
proved in Lean, in `formal/Problems/Juggler/IdealCycleMin.lean` and
`IdealLollipop.lean`: which marks are forced, which depend on the fill, which
rotations are forbidden at each join site, and that the only compiled cycle in
the figure is the sink. Renaming a projection on either side silently breaks
the figure, so read
[the ideal-cycle model](../../docs/architecture/juggler_ideal_cycle_model.md)
before changing what a mark claims.

## Publish

GitHub Actions workflow `.github/workflows/juggler-companion.yml` builds this
package and deploys `dist/` to GitHub Pages. Enable Pages in the repository
settings (source: GitHub Actions) once.
