# Juggler companion (Paper A)

A static reviewer site for
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

Production builds use the GitHub project-pages base `/balanced_ternary/`.

## What is in the TypeScript kernel

`src/juggler/` is a display fork of

- `src/research/juggler_sequence/power_words.py`
- `src/research/juggler_sequence/floor_cells.py`
- `src/research/juggler_sequence/cycle_word.py`

`n_max` is looked up from the shipped Theorem 4.6 snapshot. It is never
recomputed with floating logarithms.

## Publish

GitHub Actions workflow `.github/workflows/juggler-companion.yml` builds this
package and deploys `dist/` to GitHub Pages. Enable Pages in the repository
settings (source: GitHub Actions) once.
