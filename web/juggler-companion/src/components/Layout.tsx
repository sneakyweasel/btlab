import { NavLink, Outlet } from "react-router-dom";
import { PAPERS, paperDoiHref } from "../content/papers";

const LINKS = [
  { to: "/", label: "Home", end: true },
  { to: "/tour", label: "Tour" },
  { to: "/play", label: "Playground" },
  { to: "/claims", label: "What the paper claims" },
];

const REPO_HREF = "https://github.com/sneakyweasel/btlab";
const ABOUT_HREF = "https://www.cochin.fr/about/";

export function Layout() {
  return (
    <div className="min-h-svh">
      <header className="border-b border-line bg-card/80 backdrop-blur">
        <div className="mx-auto flex max-w-6xl flex-wrap items-center justify-between gap-3 px-4 py-3">
          <NavLink to="/" className="font-serif text-xl text-ink no-underline">
            Juggler companion
          </NavLink>
          <nav className="flex flex-wrap gap-1 text-sm">
            {LINKS.map((link) => (
              <NavLink
                key={link.to}
                to={link.to}
                end={link.end}
                className={({ isActive }) =>
                  `rounded-full px-3 py-1 no-underline ${
                    isActive ? "bg-deep text-card" : "text-muted hover:bg-paper"
                  }`
                }
              >
                {link.label}
              </NavLink>
            ))}
            <a
              href={REPO_HREF}
              target="_blank"
              rel="noreferrer"
              className="rounded-full px-3 py-1 text-muted no-underline hover:bg-paper"
            >
              GitHub
            </a>
            <a
              href={ABOUT_HREF}
              target="_blank"
              rel="noreferrer"
              className="rounded-full px-3 py-1 text-muted no-underline hover:bg-paper"
            >
              About
            </a>
          </nav>
        </div>
      </header>
      <main className="mx-auto max-w-6xl px-4 py-8">
        <Outlet />
      </main>
      <footer className="border-t border-line">
        <div className="mx-auto flex max-w-6xl flex-wrap gap-x-4 gap-y-1 px-4 py-3 text-sm text-muted">
          {PAPERS.filter((paper) => paper.doi).map((paper) => (
            <a
              key={paper.letter}
              href={paperDoiHref(paper.doi!)}
              target="_blank"
              rel="noreferrer"
              className="text-muted no-underline hover:text-ink"
            >
              Paper {paper.letter} doi:{paper.doi}
            </a>
          ))}
        </div>
      </footer>
    </div>
  );
}
