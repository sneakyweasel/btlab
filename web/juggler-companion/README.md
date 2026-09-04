# Juggler companion

A static reviewer site for Papers A–C, led by
[Cycle Financing and Near-Convergent Diophantine Obstructions in the Juggler Map](../../juggler_review/juggler_finite_dynamics_note.pdf).
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
a Root Directory. Framework is Vite; Node 22.

SPA routes (`/tour`, `/play/trajectory`, …) are rewritten to `index.html`.
If you instead set the Vercel Root Directory to `web/juggler-companion`,
the package-local `vercel.json` does the same rewrite.

## What is in the TypeScript kernel

`src/juggler/` is a display fork of

- `src/research/juggler_sequence/power_itineraries.py`
- `src/research/juggler_sequence/floor_preimages.py`
- `src/research/juggler_sequence/fate_contagion.py`
- `src/research/juggler_sequence/cycle_itinerary.py`

The preimage playground shows Paper C’s two productions — the even block
and the OE fiber with its parity sweep — not a halt-theorem demo.

`n_max` is looked up from the shipped Theorem 4.6 snapshot. It is never
recomputed with floating logarithms.

## Publish

GitHub Actions workflow `.github/workflows/juggler-companion.yml` builds this
package and deploys `dist/` to GitHub Pages. Enable Pages in the repository
settings (source: GitHub Actions) once.
