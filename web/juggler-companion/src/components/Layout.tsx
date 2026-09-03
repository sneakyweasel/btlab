import { NavLink, Outlet } from "react-router-dom";

const LINKS = [
  { to: "/", label: "Home", end: true },
  { to: "/tour", label: "Tour" },
  { to: "/play", label: "Playground" },
  { to: "/claims", label: "What the paper claims" },
];

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
          </nav>
        </div>
      </header>
      <main className="mx-auto max-w-6xl px-4 py-8">
        <Outlet />
      </main>
    </div>
  );
}
